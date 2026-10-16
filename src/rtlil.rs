//! In-memory model of a Yosys RTLIL design and its text (`.il`) writer.
//!
//! Only the subset the translator needs is modelled: wires, cells with
//! parameters, processes (switch/case trees with sync rules) and
//! connections.  Signals are LSB-first chunk lists, printed MSB-first as
//! RTLIL expects.

use std::collections::HashMap;
use std::fmt::Write;

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum Bit {
    Zero,
    One,
    X,
    Z,
}

impl Bit {
    fn ch(self) -> char {
        match self {
            Bit::Zero => '0',
            Bit::One => '1',
            Bit::X => 'x',
            Bit::Z => 'z',
        }
    }
}

/// One piece of a signal.  Bits are LSB-first.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Chunk {
    Wire {
        name: String,
        wire_width: usize,
        offset: usize,
        width: usize,
    },
    Const(Vec<Bit>),
}

impl Chunk {
    fn width(&self) -> usize {
        match self {
            Chunk::Wire { width, .. } => *width,
            Chunk::Const(b) => b.len(),
        }
    }
}

/// A signal: LSB-first list of chunks.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Default)]
pub struct SigSpec {
    chunks: Vec<Chunk>,
}

impl SigSpec {
    pub fn empty() -> Self {
        SigSpec { chunks: vec![] }
    }

    pub fn wire(name: &str, width: usize) -> Self {
        if width == 0 {
            return Self::empty();
        }
        SigSpec {
            chunks: vec![Chunk::Wire {
                name: name.to_string(),
                wire_width: width,
                offset: 0,
                width,
            }],
        }
    }

    pub fn consts(bits: Vec<Bit>) -> Self {
        if bits.is_empty() {
            return Self::empty();
        }
        SigSpec {
            chunks: vec![Chunk::Const(bits)],
        }
    }

    pub fn const_u64(value: u64, width: usize) -> Self {
        let bits = (0..width)
            .map(|i| {
                if i < 64 && (value >> i) & 1 == 1 {
                    Bit::One
                } else {
                    Bit::Zero
                }
            })
            .collect();
        Self::consts(bits)
    }

    pub fn const_bit(b: Bit) -> Self {
        Self::consts(vec![b])
    }

    pub fn fill(b: Bit, width: usize) -> Self {
        Self::consts(vec![b; width])
    }

    pub fn width(&self) -> usize {
        self.chunks.iter().map(|c| c.width()).sum()
    }

    pub fn is_empty(&self) -> bool {
        self.width() == 0
    }

    pub fn is_fully_const(&self) -> bool {
        self.chunks.iter().all(|c| matches!(c, Chunk::Const(_)))
    }

    pub fn as_const(&self) -> Option<Vec<Bit>> {
        let mut ret = Vec::with_capacity(self.width());
        for c in &self.chunks {
            match c {
                Chunk::Const(b) => ret.extend_from_slice(b),
                _ => return None,
            }
        }
        Some(ret)
    }

    pub fn as_const_u64(&self) -> Option<u64> {
        let bits = self.as_const()?;
        if bits.len() > 64 {
            return None;
        }
        let mut v = 0u64;
        for (i, b) in bits.iter().enumerate() {
            match b {
                Bit::One => v |= 1 << i,
                Bit::Zero => {}
                _ => return None,
            }
        }
        Some(v)
    }

    /// Bits `[offset, offset+width)`.
    pub fn extract(&self, offset: usize, width: usize) -> SigSpec {
        let mut ret = SigSpec::empty();
        let mut pos = 0;
        for c in &self.chunks {
            let cw = c.width();
            let lo = pos;
            let hi = pos + cw;
            pos = hi;
            let s = offset.max(lo);
            let e = (offset + width).min(hi);
            if s >= e {
                continue;
            }
            match c {
                Chunk::Wire {
                    name,
                    wire_width,
                    offset: coff,
                    ..
                } => ret.push(Chunk::Wire {
                    name: name.clone(),
                    wire_width: *wire_width,
                    offset: coff + (s - lo),
                    width: e - s,
                }),
                Chunk::Const(b) => ret.push(Chunk::Const(b[s - lo..e - lo].to_vec())),
            }
        }
        ret
    }

    pub fn bit(&self, i: usize) -> SigSpec {
        self.extract(i, 1)
    }

    pub fn msb(&self) -> SigSpec {
        self.extract(self.width() - 1, 1)
    }

    fn push(&mut self, c: Chunk) {
        if c.width() == 0 {
            return;
        }
        if let Some(last) = self.chunks.last_mut() {
            match (last, &c) {
                (
                    Chunk::Wire {
                        name: n1,
                        offset: o1,
                        width: w1,
                        ..
                    },
                    Chunk::Wire {
                        name: n2,
                        offset: o2,
                        width: w2,
                        ..
                    },
                ) if n1 == n2 && *o1 + *w1 == *o2 => {
                    *w1 += *w2;
                    return;
                }
                (Chunk::Const(b1), Chunk::Const(b2)) => {
                    b1.extend_from_slice(b2);
                    return;
                }
                _ => {}
            }
        }
        self.chunks.push(c);
    }

    /// Append `other` above the current MSB.
    pub fn append(&mut self, other: &SigSpec) {
        for c in &other.chunks {
            self.push(c.clone());
        }
    }

    /// Concatenate LSB-first parts.
    pub fn concat_lsb_first(parts: &[SigSpec]) -> SigSpec {
        let mut ret = SigSpec::empty();
        for p in parts {
            ret.append(p);
        }
        ret
    }

    /// Splice `val` into bits `[lo, lo+val.width())` of `self`.
    pub fn splice(&self, lo: usize, val: &SigSpec) -> SigSpec {
        let total = self.width();
        let w = val.width();
        let mut ret = self.extract(0, lo);
        if lo + w <= total {
            ret.append(val);
            ret.append(&self.extract(lo + w, total - lo - w));
        } else {
            // Out-of-range static write: drop the overflowing bits.
            ret.append(&val.extract(0, total.saturating_sub(lo)));
        }
        ret
    }

    /// Zero- or sign-extend (or truncate) to `width`.
    pub fn resize(&self, width: usize, signed: bool) -> SigSpec {
        let cur = self.width();
        if cur == width {
            return self.clone();
        }
        if cur > width {
            return self.extract(0, width);
        }
        let mut ret = self.clone();
        if cur == 0 {
            ret.append(&SigSpec::fill(Bit::Zero, width));
            return ret;
        }
        let pad = if signed {
            let m = self.msb();
            let mut p = SigSpec::empty();
            for _ in 0..(width - cur) {
                p.append(&m);
            }
            p
        } else {
            SigSpec::fill(Bit::Zero, width - cur)
        };
        ret.append(&pad);
        ret
    }

    pub fn repeat(&self, n: usize) -> SigSpec {
        let mut ret = SigSpec::empty();
        for _ in 0..n {
            ret.append(self);
        }
        ret
    }

    /// Wires referenced by this signal.
    pub fn wire_names(&self) -> Vec<&str> {
        self.chunks
            .iter()
            .filter_map(|c| match c {
                Chunk::Wire { name, .. } => Some(name.as_str()),
                _ => None,
            })
            .collect()
    }
}

fn write_const(out: &mut String, bits: &[Bit]) {
    let _ = write!(out, "{}'", bits.len());
    for b in bits.iter().rev() {
        out.push(b.ch());
    }
}

fn write_chunk(out: &mut String, c: &Chunk) {
    match c {
        Chunk::Wire {
            name,
            wire_width,
            offset,
            width,
        } => {
            out.push_str(name);
            if *offset == 0 && *width == *wire_width {
                // whole wire
            } else if *width == 1 {
                let _ = write!(out, " [{}]", offset);
            } else {
                let _ = write!(out, " [{}:{}]", offset + width - 1, offset);
            }
        }
        Chunk::Const(b) => write_const(out, b),
    }
}

impl std::fmt::Display for SigSpec {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut s = String::new();
        if self.chunks.is_empty() {
            s.push_str("{ }");
        } else if self.chunks.len() == 1 {
            write_chunk(&mut s, &self.chunks[0]);
        } else {
            s.push_str("{ ");
            for c in self.chunks.iter().rev() {
                write_chunk(&mut s, c);
                s.push(' ');
            }
            s.push('}');
        }
        f.write_str(&s)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum PortDir {
    Input,
    Output,
    Inout,
}

#[derive(Clone, Debug)]
pub struct Wire {
    pub name: String,
    pub width: usize,
    pub port: Option<(PortDir, usize)>,
    pub attrs: Vec<(String, AttrVal)>,
}

#[derive(Clone, Debug)]
pub enum AttrVal {
    Int(i64),
    Str(String),
}

#[derive(Clone, Debug)]
pub enum ParamVal {
    Int(i64),
    Const(Vec<Bit>),
}

#[derive(Clone, Debug)]
pub struct Cell {
    pub name: String,
    pub kind: String,
    pub params: Vec<(String, ParamVal)>,
    pub conns: Vec<(String, SigSpec)>,
    pub attrs: Vec<(String, AttrVal)>,
}

#[derive(Clone, Debug, Default)]
pub struct CaseBody {
    pub actions: Vec<(SigSpec, SigSpec)>,
    pub switches: Vec<Switch>,
}

impl CaseBody {
    pub fn is_empty(&self) -> bool {
        self.actions.is_empty() && self.switches.is_empty()
    }
}

#[derive(Clone, Debug)]
pub struct Switch {
    pub signal: SigSpec,
    pub cases: Vec<Case>,
}

#[derive(Clone, Debug, Default)]
pub struct Case {
    /// Empty means `default`.
    pub patterns: Vec<SigSpec>,
    pub body: CaseBody,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SyncKind {
    Always,
    Posedge,
    Negedge,
    High,
    Low,
    Init,
}

#[derive(Clone, Debug)]
pub struct Sync {
    pub kind: SyncKind,
    pub signal: Option<SigSpec>,
    pub updates: Vec<(SigSpec, SigSpec)>,
}

#[derive(Clone, Debug)]
pub struct Process {
    pub name: String,
    pub root: CaseBody,
    pub syncs: Vec<Sync>,
    pub attrs: Vec<(String, AttrVal)>,
}

#[derive(Clone, Debug, Default)]
pub struct Module {
    pub name: String,
    pub attrs: Vec<(String, AttrVal)>,
    pub wires: Vec<Wire>,
    wire_index: HashMap<String, usize>,
    pub cells: Vec<Cell>,
    pub processes: Vec<Process>,
    pub connects: Vec<(SigSpec, SigSpec)>,
    counter: usize,
    port_counter: usize,
}

impl Module {
    pub fn new(name: &str) -> Self {
        Module {
            name: name.to_string(),
            ..Default::default()
        }
    }

    pub fn has_wire(&self, name: &str) -> bool {
        self.wire_index.contains_key(name)
    }

    pub fn rebuild_wire_index(&mut self) {
        self.wire_index = self
            .wires
            .iter()
            .enumerate()
            .map(|(i, w)| (w.name.clone(), i))
            .collect();
    }

    pub fn wire_width(&self, name: &str) -> Option<usize> {
        self.wire_index.get(name).map(|i| self.wires[*i].width)
    }

    /// Add a wire with an explicit name; returns its full signal.
    pub fn add_wire(&mut self, name: &str, width: usize) -> SigSpec {
        if let Some(i) = self.wire_index.get(name) {
            debug_assert_eq!(self.wires[*i].width, width);
            return SigSpec::wire(name, width);
        }
        self.wire_index.insert(name.to_string(), self.wires.len());
        self.wires.push(Wire {
            name: name.to_string(),
            width,
            port: None,
            attrs: vec![],
        });
        SigSpec::wire(name, width)
    }

    pub fn add_port(&mut self, name: &str, width: usize, dir: PortDir) -> SigSpec {
        let sig = self.add_wire(name, width);
        let i = self.wire_index[name];
        if self.wires[i].port.is_none() {
            self.port_counter += 1;
            self.wires[i].port = Some((dir, self.port_counter));
        }
        sig
    }

    pub fn set_wire_attr(&mut self, name: &str, attr: &str, val: AttrVal) {
        if let Some(i) = self.wire_index.get(name) {
            self.wires[*i].attrs.push((attr.to_string(), val));
        }
    }

    pub fn fresh_name(&mut self, hint: &str) -> String {
        self.counter += 1;
        format!("${}${}", self.counter, hint)
    }

    /// A fresh private wire.
    pub fn fresh_wire(&mut self, hint: &str, width: usize) -> SigSpec {
        let name = self.fresh_name(hint);
        self.add_wire(&name, width)
    }

    pub fn add_cell(
        &mut self,
        kind: &str,
        params: Vec<(&str, ParamVal)>,
        conns: Vec<(&str, SigSpec)>,
    ) -> String {
        let name = self.fresh_name(kind.trim_start_matches('$'));
        self.cells.push(Cell {
            name: name.clone(),
            kind: kind.to_string(),
            params: params
                .into_iter()
                .map(|(k, v)| (k.to_string(), v))
                .collect(),
            conns: conns
                .into_iter()
                .map(|(k, v)| (k.to_string(), v))
                .collect(),
            attrs: vec![],
        });
        name
    }

    pub fn add_cell_named(
        &mut self,
        name: &str,
        kind: &str,
        params: Vec<(String, ParamVal)>,
        conns: Vec<(String, SigSpec)>,
    ) {
        self.cells.push(Cell {
            name: name.to_string(),
            kind: kind.to_string(),
            params,
            conns,
            attrs: vec![],
        });
    }

    pub fn connect(&mut self, lhs: SigSpec, rhs: SigSpec) {
        debug_assert_eq!(lhs.width(), rhs.width());
        if lhs.is_empty() {
            return;
        }
        self.connects.push((lhs, rhs));
    }

    // ----- cell helpers -------------------------------------------------

    pub fn unop(&mut self, kind: &str, a: &SigSpec, a_signed: bool, y_width: usize) -> SigSpec {
        let y = self.fresh_wire("y", y_width);
        self.add_cell(
            kind,
            vec![
                ("\\A_SIGNED", ParamVal::Int(a_signed as i64)),
                ("\\A_WIDTH", ParamVal::Int(a.width() as i64)),
                ("\\Y_WIDTH", ParamVal::Int(y_width as i64)),
            ],
            vec![("\\A", a.clone()), ("\\Y", y.clone())],
        );
        y
    }

    pub fn binop(
        &mut self,
        kind: &str,
        a: &SigSpec,
        b: &SigSpec,
        a_signed: bool,
        b_signed: bool,
        y_width: usize,
    ) -> SigSpec {
        let y = self.fresh_wire("y", y_width);
        self.add_cell(
            kind,
            vec![
                ("\\A_SIGNED", ParamVal::Int(a_signed as i64)),
                ("\\B_SIGNED", ParamVal::Int(b_signed as i64)),
                ("\\A_WIDTH", ParamVal::Int(a.width() as i64)),
                ("\\B_WIDTH", ParamVal::Int(b.width() as i64)),
                ("\\Y_WIDTH", ParamVal::Int(y_width as i64)),
            ],
            vec![("\\A", a.clone()), ("\\B", b.clone()), ("\\Y", y.clone())],
        );
        y
    }

    /// `s ? b : a`
    pub fn mux(&mut self, a: &SigSpec, b: &SigSpec, s: &SigSpec) -> SigSpec {
        debug_assert_eq!(a.width(), b.width());
        debug_assert_eq!(s.width(), 1);
        if a == b {
            return a.clone();
        }
        let w = a.width();
        let y = self.fresh_wire("mux", w);
        self.add_cell(
            "$mux",
            vec![("\\WIDTH", ParamVal::Int(w as i64))],
            vec![
                ("\\A", a.clone()),
                ("\\B", b.clone()),
                ("\\S", s.clone()),
                ("\\Y", y.clone()),
            ],
        );
        y
    }

    /// Bitwise `s[i] ? b[i] : a[i]`
    pub fn bwmux(&mut self, a: &SigSpec, b: &SigSpec, s: &SigSpec) -> SigSpec {
        let w = a.width();
        debug_assert_eq!(b.width(), w);
        debug_assert_eq!(s.width(), w);
        let y = self.fresh_wire("bwmux", w);
        self.add_cell(
            "$bwmux",
            vec![("\\WIDTH", ParamVal::Int(w as i64))],
            vec![
                ("\\A", a.clone()),
                ("\\B", b.clone()),
                ("\\S", s.clone()),
                ("\\Y", y.clone()),
            ],
        );
        y
    }

    /// Reduce a multi-bit signal to one bit (`|a`), or pass a 1-bit signal.
    pub fn to_bool(&mut self, a: &SigSpec) -> SigSpec {
        if a.width() == 1 {
            return a.clone();
        }
        if a.width() == 0 {
            return SigSpec::const_bit(Bit::Zero);
        }
        if let Some(bits) = a.as_const() {
            if bits.iter().any(|b| *b == Bit::One) {
                return SigSpec::const_bit(Bit::One);
            }
            if bits.iter().all(|b| *b == Bit::Zero) {
                return SigSpec::const_bit(Bit::Zero);
            }
        }
        self.unop("$reduce_bool", a, false, 1)
    }

    pub fn not1(&mut self, a: &SigSpec) -> SigSpec {
        if let Some(bits) = a.as_const()
            && bits.len() == 1
        {
            return match bits[0] {
                Bit::Zero => SigSpec::const_bit(Bit::One),
                Bit::One => SigSpec::const_bit(Bit::Zero),
                _ => SigSpec::const_bit(Bit::X),
            };
        }
        self.unop("$logic_not", a, false, 1)
    }
}

#[derive(Clone, Debug, Default)]
pub struct Design {
    pub modules: Vec<Module>,
}

// --------------------------------------------------------------------------
// Writer
// --------------------------------------------------------------------------

fn write_attrs(out: &mut String, indent: &str, attrs: &[(String, AttrVal)]) {
    for (k, v) in attrs {
        match v {
            AttrVal::Int(i) => {
                let _ = writeln!(out, "{indent}attribute {k} {i}");
            }
            AttrVal::Str(s) => {
                let _ = writeln!(out, "{indent}attribute {k} \"{}\"", escape_str(s));
            }
        }
    }
}

fn escape_str(s: &str) -> String {
    let mut r = String::new();
    for c in s.chars() {
        match c {
            '"' => r.push_str("\\\""),
            '\\' => r.push_str("\\\\"),
            '\n' => r.push_str("\\n"),
            _ => r.push(c),
        }
    }
    r
}

fn write_case_body(out: &mut String, body: &CaseBody, depth: usize) {
    let indent = "  ".repeat(depth);
    for (lhs, rhs) in &body.actions {
        let _ = writeln!(out, "{indent}assign {lhs} {rhs}");
    }
    for sw in &body.switches {
        let _ = writeln!(out, "{indent}switch {}", sw.signal);
        for case in &sw.cases {
            if case.patterns.is_empty() {
                let _ = writeln!(out, "{indent}  case");
            } else {
                let pats: Vec<String> = case.patterns.iter().map(|p| p.to_string()).collect();
                let _ = writeln!(out, "{indent}  case {}", pats.join(" , "));
            }
            write_case_body(out, &case.body, depth + 2);
        }
        let _ = writeln!(out, "{indent}end");
    }
}

impl Module {
    pub fn write(&self, out: &mut String) {
        write_attrs(out, "", &self.attrs);
        let _ = writeln!(out, "module {}", self.name);
        for w in &self.wires {
            write_attrs(out, "  ", &w.attrs);
            let mut line = String::from("  wire");
            if w.width != 1 {
                let _ = write!(line, " width {}", w.width);
            }
            if let Some((dir, idx)) = w.port {
                let d = match dir {
                    PortDir::Input => "input",
                    PortDir::Output => "output",
                    PortDir::Inout => "inout",
                };
                let _ = write!(line, " {d} {idx}");
            }
            let _ = writeln!(out, "{line} {}", w.name);
        }
        for c in &self.cells {
            write_attrs(out, "  ", &c.attrs);
            let _ = writeln!(out, "  cell {} {}", c.kind, c.name);
            for (k, v) in &c.params {
                match v {
                    ParamVal::Int(i) => {
                        let _ = writeln!(out, "    parameter {k} {i}");
                    }
                    ParamVal::Const(b) => {
                        let mut s = String::new();
                        write_const(&mut s, b);
                        let _ = writeln!(out, "    parameter {k} {s}");
                    }
                }
            }
            for (k, v) in &c.conns {
                let _ = writeln!(out, "    connect {k} {v}");
            }
            let _ = writeln!(out, "  end");
        }
        for p in &self.processes {
            write_attrs(out, "  ", &p.attrs);
            let _ = writeln!(out, "  process {}", p.name);
            write_case_body(out, &p.root, 2);
            for s in &p.syncs {
                let kind = match s.kind {
                    SyncKind::Always => "always",
                    SyncKind::Posedge => "posedge",
                    SyncKind::Negedge => "negedge",
                    SyncKind::High => "high",
                    SyncKind::Low => "low",
                    SyncKind::Init => "init",
                };
                match &s.signal {
                    Some(sig) => {
                        let _ = writeln!(out, "    sync {kind} {sig}");
                    }
                    None => {
                        let _ = writeln!(out, "    sync {kind}");
                    }
                }
                for (lhs, rhs) in &s.updates {
                    let _ = writeln!(out, "      update {lhs} {rhs}");
                }
            }
            let _ = writeln!(out, "  end");
        }
        for (lhs, rhs) in &self.connects {
            let _ = writeln!(out, "  connect {lhs} {rhs}");
        }
        let _ = writeln!(out, "end");
    }
}

impl Design {
    pub fn to_il(&self) -> String {
        let mut out = String::new();
        out.push_str("# Generated by veryl-rtlil\n");
        out.push_str("autoidx 1\n");
        for m in &self.modules {
            m.write(&mut out);
            out.push('\n');
        }
        out
    }
}

/// Escape an arbitrary identifier as an RTLIL public id (`\name`).
pub fn public_id(name: &str) -> String {
    let mut s = String::from("\\");
    for c in name.chars() {
        if c.is_whitespace() {
            s.push('_');
        } else {
            s.push(c);
        }
    }
    s
}
