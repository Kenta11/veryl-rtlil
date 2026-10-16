//! Veryl IR -> RTLIL translation.
//!
//! Each Veryl module body (already monomorphized by the analyzer) becomes one
//! RTLIL module.  Combinational and clocked blocks become RTLIL processes
//! whose switch/case trees Yosys' `proc` pass lowers to cells; expressions
//! become word-level cells outside the processes.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use veryl_analyzer::ir::{
    ArrayLiteralItem, AssignDestination, CaseStatement, Component, Comptime, Declaration,
    Expression, Factor, FfDeclaration, ForBound, ForRange, ForStatement, Function, FunctionCall,
    IfResetStatement, IfStatement, InstDeclaration, Ir, Module as IrModule, Op, Signature,
    Statement, SystemFunctionCall, SystemFunctionKind, Type, TypeKind, ValueVariant, VarId,
    VarIndex, VarKind, VarSelect, VarSelectOp, Variable,
};
use veryl_analyzer::symbol::Affiliation;
use veryl_analyzer::value::Value;
use veryl_metadata::{Build, ResetType};
use veryl_parser::resource_table;
use veryl_parser::token_range::TokenRange;

use crate::error::{TResult, TranslateError, internal, unsupported};
use crate::naming;
use crate::rtlil::{
    AttrVal, Bit, Case, CaseBody, Design, Module, ParamVal, PortDir, SigSpec, Switch, Sync,
    SyncKind, Process, public_id,
};

#[derive(Clone, Debug)]
pub struct Options {
    pub omit_project_prefix: bool,
    pub build: Build,
    /// Largest array (in bits) that may be written through a dynamic index.
    pub max_dynamic_bits: usize,
}

#[derive(Clone, Debug)]
pub struct ModuleReport {
    /// Veryl module name.
    pub name: String,
    /// Module name in the SystemVerilog emitted by Veryl.
    pub sv_name: String,
    /// RTLIL module name (without the leading backslash) when translated.
    pub rtlil_name: Option<String>,
    pub project: Option<String>,
    pub error: Option<String>,
}

#[derive(Clone, Debug, Default)]
pub struct Report {
    pub modules: Vec<ModuleReport>,
}

/// Translate every top-level module of `ir`.  Modules that cannot be
/// translated are reported, not fatal.
pub fn translate_ir(ir: &Ir, opts: &Options) -> (Design, Report) {
    let mut tr = Translator {
        opts: opts.clone(),
        design: Design::default(),
        by_sig: HashMap::new(),
        by_ptr: HashMap::new(),
        used_names: HashSet::new(),
        in_progress: HashSet::new(),
        done_sig: HashMap::new(),
    };
    let mut report = Report::default();
    // Register top-level bodies first so instantiated copies with the same
    // signature share their SV name.
    for c in &ir.components {
        if let Component::Module(m) = c {
            let name = str_of(m.name);
            let sv = naming::sv_module_name(&m.signature, &name, opts.omit_project_prefix);
            tr.by_sig
                .entry(m.signature.clone())
                .or_insert_with(|| sv.clone());
        }
    }
    for c in &ir.components {
        if let Component::Module(m) = c {
            let name = str_of(m.name);
            let sv = naming::sv_module_name(&m.signature, &name, opts.omit_project_prefix);
            let project = naming::project_of(&m.signature);
            match tr.translate_module(m) {
                Ok(rtlil_name) => report.modules.push(ModuleReport {
                    name,
                    sv_name: sv,
                    rtlil_name: Some(rtlil_name),
                    project,
                    error: None,
                }),
                Err(e) => report.modules.push(ModuleReport {
                    name,
                    sv_name: sv,
                    rtlil_name: None,
                    project,
                    error: Some(e.to_string()),
                }),
            }
        }
    }
    (tr.design, report)
}

pub fn str_of(id: veryl_parser::resource_table::StrId) -> String {
    resource_table::get_str_value(id).unwrap_or_else(|| format!("{id}"))
}

struct Translator {
    opts: Options,
    design: Design,
    /// SV module name reserved for a signature (top-level bodies).
    by_sig: HashMap<Signature, String>,
    /// Translated module bodies by address.
    by_ptr: HashMap<usize, String>,
    used_names: HashSet<String>,
    in_progress: HashSet<usize>,
    /// Translated bodies by signature.
    done_sig: HashMap<Signature, String>,
}

impl Translator {
    fn module_key(m: &IrModule) -> usize {
        m as *const IrModule as usize
    }

    /// RTLIL name (without backslash) for a module body.
    fn rtlil_name_for(&mut self, m: &IrModule) -> String {
        let name = str_of(m.name);
        let base = naming::sv_module_name(&m.signature, &name, self.opts.omit_project_prefix);
        let mut cand = if let Some(sv) = self.by_sig.get(&m.signature) {
            sv.clone()
        } else {
            let mut params = String::new();
            for (k, v) in &m.signature.parameters {
                let vs = match v {
                    ValueVariant::Numeric(x) => format!("{}h{:x}", x.width(), x.payload().as_ref()),
                    other => format!("{other:?}"),
                };
                params.push_str(&format!("\\{}={}", str_of(*k), vs));
            }
            for (k, v) in &m.signature.generic_parameters {
                params.push_str(&format!("\\{}={}", str_of(*k), v));
            }
            for (k, v) in &m.signature.modport_signatures {
                params.push_str(&format!("\\{}={}", str_of(*k), v));
            }
            if params.is_empty() {
                base.clone()
            } else {
                format!("$paramod\\{base}{params}")
            }
        };
        let cand_s: String = cand
            .chars()
            .map(|c| if c.is_whitespace() { '_' } else { c })
            .collect();
        let mut cand = cand_s;
        let mut n = 1;
        let orig = cand.clone();
        while self.used_names.contains(&cand) {
            n += 1;
            cand = format!("{orig}${n}");
        }
        self.used_names.insert(cand.clone());
        cand
    }

    fn translate_module(&mut self, m: &IrModule) -> TResult<String> {
        let key = Self::module_key(m);
        if let Some(n) = self.by_ptr.get(&key) {
            return Ok(n.clone());
        }
        // Two bodies with the same signature are the same monomorphization.
        if let Some(n) = self.done_sig.get(&m.signature) {
            self.by_ptr.insert(key, n.clone());
            return Ok(n.clone());
        }
        if self.in_progress.contains(&key) {
            return internal("recursive module instantiation");
        }
        self.in_progress.insert(key);
        // Translate children first (depth-first) so their names are known.
        let mut children: HashMap<usize, String> = HashMap::new();
        let r = self.translate_children(m, &mut children);
        let r = r.and_then(|_| {
            let name = self.rtlil_name_for(m);
            let mut ctx = ModCtx::new(m, &self.opts, children, &name)?;
            ctx.build()?;
            self.design.modules.push(ctx.m);
            Ok(name)
        });
        self.in_progress.remove(&key);
        match r {
            Ok(name) => {
                self.by_ptr.insert(key, name.clone());
                self.done_sig.insert(m.signature.clone(), name.clone());
                Ok(name)
            }
            Err(e) => Err(e),
        }
    }

    fn translate_children(
        &mut self,
        m: &IrModule,
        children: &mut HashMap<usize, String>,
    ) -> TResult<()> {
        for d in &m.declarations {
            if let Declaration::Inst(inst) = d {
                match inst.component.as_ref() {
                    Component::Module(cm) => {
                        let name = self.translate_module(cm).map_err(|e| match e {
                            TranslateError::Unsupported(m) => TranslateError::Unsupported(
                                format!("in {}: {}", str_of(cm.name), m),
                            ),
                            TranslateError::Internal(m) => {
                                TranslateError::Internal(format!("in {}: {}", str_of(cm.name), m))
                            }
                        })?;
                        children.insert(Self::module_key(cm), name);
                    }
                    Component::Interface(_) => {
                        return unsupported("interface instance", &inst.token);
                    }
                    Component::SystemVerilog(_) => {
                        return unsupported("SystemVerilog module instance", &inst.token);
                    }
                }
            }
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Per-module context
// ---------------------------------------------------------------------------

#[derive(Clone)]
struct VarInfo {
    /// RTLIL wire id (with backslash); empty for constants.
    wire: String,
    total: usize,
    /// Bits per array element (packed width).
    ew: usize,
    shape: Vec<usize>,
    nelem: usize,
    ty: Type,
    kind: VarKind,
    konst: Option<SigSpec>,
    func_local: bool,
    token: TokenRange,
}

impl VarInfo {
    fn sig(&self) -> SigSpec {
        match &self.konst {
            Some(c) => c.clone(),
            None => SigSpec::wire(&self.wire, self.total),
        }
    }
}

#[derive(Clone, Debug)]
enum Written {
    Ranges(Vec<(usize, usize)>),
    All,
}

#[derive(Clone, Debug, Default)]
struct Proc {
    cur: HashMap<VarId, SigSpec>,
    written: HashMap<VarId, Written>,
}

impl Proc {
    fn note_write(&mut self, id: VarId, range: Option<(usize, usize)>) {
        let e = self
            .written
            .entry(id)
            .or_insert_with(|| Written::Ranges(vec![]));
        match (e, range) {
            (Written::Ranges(v), Some(r)) => v.push(r),
            (e, None) => *e = Written::All,
            (Written::All, _) => {}
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ResetPol {
    ActiveHigh,
    ActiveLow,
}

struct ModCtx<'a> {
    ir: &'a IrModule,
    opts: &'a Options,
    m: Module,
    vars: HashMap<VarId, VarInfo>,
    funcs: &'a fxhash::FxHashMap<VarId, Function>,
    eval: veryl_analyzer::Context,
    children: HashMap<usize, String>,
    proc_counter: usize,
    /// Validity flag of the most recent dynamic array index (see `region`).
    last_valid: Option<SigSpec>,
    cell_names: HashSet<String>,
}

/// Row-major strides for a shape.
fn strides(shape: &[usize]) -> Vec<usize> {
    let mut s = vec![1; shape.len()];
    for i in (0..shape.len().saturating_sub(1)).rev() {
        s[i] = s[i + 1] * shape[i + 1];
    }
    s
}

fn bits_for(n: usize) -> usize {
    let mut b = 1;
    while (1usize << b) < n {
        b += 1;
    }
    b
}

fn value_to_bits(v: &Value, width: usize) -> Vec<Bit> {
    let payload = v.payload();
    let xz = v.mask_xz();
    let vw = v.width();
    let signed = v.signed();
    let mut bits = Vec::with_capacity(width);
    for i in 0..width {
        let src = if i < vw { i } else if signed && vw > 0 { vw - 1 } else { usize::MAX };
        if src == usize::MAX {
            bits.push(Bit::Zero);
            continue;
        }
        if xz.bit(src as u64) {
            // z and x both carry no information; the analyzer keeps a
            // single mask for them.
            bits.push(if payload.bit(src as u64) { Bit::Z } else { Bit::X });
        } else {
            bits.push(if payload.bit(src as u64) { Bit::One } else { Bit::Zero });
        }
    }
    bits
}

/// The bit an unsized fill literal replicates.
fn fill_bit(v: &Value) -> Bit {
    let p = v.payload().bit(0);
    let x = v.mask_xz().bit(0);
    match (x, p) {
        (false, false) => Bit::Zero,
        (false, true) => Bit::One,
        (true, false) => Bit::X,
        (true, true) => Bit::Z,
    }
}

fn value_to_sig(v: &Value, width: usize) -> SigSpec {
    SigSpec::consts(value_to_bits(v, width))
}

fn merge_ranges(mut v: Vec<(usize, usize)>) -> Vec<(usize, usize)> {
    v.sort();
    let mut out: Vec<(usize, usize)> = vec![];
    for (lo, hi) in v {
        if let Some(last) = out.last_mut()
            && lo <= last.1 + 1
        {
            last.1 = last.1.max(hi);
        } else {
            out.push((lo, hi));
        }
    }
    out
}

impl<'a> ModCtx<'a> {
    fn new(
        ir: &'a IrModule,
        opts: &'a Options,
        children: HashMap<usize, String>,
        name: &str,
    ) -> TResult<Self> {
        let m = Module::new(&public_id_or_private(name));
        Ok(ModCtx {
            ir,
            opts,
            m,
            vars: HashMap::new(),
            funcs: &ir.functions,
            eval: veryl_analyzer::Context::default(),
            children,
            proc_counter: 0,
            last_valid: None,
            cell_names: HashSet::new(),
        })
    }

    fn build(&mut self) -> TResult<()> {
        if std::env::var_os("VERYL_RTLIL_DEBUG").is_some() {
            eprintln!("== module {}", str_of(self.ir.name));
            let mut ports: Vec<_> = self.ir.ports.iter().collect();
            ports.sort_by_key(|p| *p.1);
            for (path, vid) in ports {
                let k = self.ir.variables.get(vid).map(|v| v.kind.to_string()).unwrap_or_default();
                eprintln!("  port {path} = {vid} ({k})");
            }
            let mut im: Vec<_> = self.ir.interface_members.iter().collect();
            im.sort_by_key(|p| *p.0);
            for (vid, v) in im {
                eprintln!("  interface_member {vid} {} : {} kind={}", v.path, v.r#type, v.kind);
            }
        }
        self.allocate_variables()?;
        self.declare_ports()?;
        for (idx, d) in self.ir.declarations.iter().enumerate() {
            self.declaration(idx, d)?;
        }
        Ok(())
    }

    // ----- variables ---------------------------------------------------

    fn allocate_variables(&mut self) -> TResult<()> {
        let mut vars: Vec<&Variable> = self.ir.variables.values().collect();
        vars.sort_by_key(|v| v.id);
        // Seed constants so selects indexed by parameters fold.
        for v in &vars {
            if matches!(v.kind, VarKind::Param | VarKind::Const) && v.r#type.total_array() == Some(1)
            {
                self.eval.variables.insert(v.id, (*v).clone());
            }
        }
        for v in vars {
            let skip_kind = matches!(
                v.r#type.kind,
                TypeKind::Module(_)
                    | TypeKind::Interface(_)
                    | TypeKind::Modport(_, _)
                    | TypeKind::Package(_)
                    | TypeKind::Instance(_, _)
                    | TypeKind::AbstractInterface(_)
                    | TypeKind::Type
                    | TypeKind::String
                    | TypeKind::Void
            );
            if skip_kind {
                continue;
            }
            if matches!(v.r#type.kind, TypeKind::SystemVerilog) {
                return unsupported(
                    format!("variable {} of SystemVerilog type", v.path),
                    &v.token,
                );
            }
            if matches!(v.r#type.kind, TypeKind::F32 | TypeKind::F64) {
                return unsupported(format!("floating point variable {}", v.path), &v.token);
            }
            let Some(ew) = v.r#type.total_width() else {
                return unsupported(format!("unresolved width of {}", v.path), &v.token);
            };
            let shape: Vec<usize> = match v
                .r#type
                .array
                .iter()
                .map(|d| *d)
                .collect::<Option<Vec<usize>>>()
            {
                Some(s) => s,
                None => {
                    return unsupported(
                        format!("unresolved array size of {}", v.path),
                        &v.token,
                    );
                }
            };
            let nelem: usize = shape.iter().product();
            let total = ew * nelem;
            let func_local = matches!(v.affiliation, Affiliation::Function);
            let konst = if matches!(v.kind, VarKind::Param | VarKind::Const) {
                const_bits(v, ew, nelem)
            } else {
                None
            };
            let wire = if konst.is_some() || total == 0 {
                String::new()
            } else {
                // Block-scoped `let`s may repeat a path with another type;
                // keep each VarId's storage separate.
                let mut name = public_id(&v.path.to_string());
                if self.m.has_wire(&name) {
                    name = format!("{name}${}", v.id);
                }
                self.m.add_wire(&name, total);
                // Per-element alias wires `\name[i]`: Yosys' memory mapping
                // names memory words this way, so the equivalence checker can
                // pair the state elements of both sides.
                if !shape.is_empty() && nelem >= 1 {
                    for f in 0..nelem {
                        let alias = public_id(&format!("{}[{}]", v.path, f));
                        if self.m.has_wire(&alias) {
                            continue;
                        }
                        let a = self.m.add_wire(&alias, ew);
                        let off = (nelem - 1 - f) * ew;
                        let src = SigSpec::wire(&name, total).extract(off, ew);
                        self.m.connect(a, src);
                    }
                }
                name
            };
            self.vars.insert(
                v.id,
                VarInfo {
                    wire,
                    total,
                    ew,
                    shape,
                    nelem,
                    ty: v.r#type.clone(),
                    kind: v.kind,
                    konst,
                    func_local,
                    token: v.token,
                },
            );
        }
        Ok(())
    }

    fn declare_ports(&mut self) -> TResult<()> {
        let mut ports: Vec<(&veryl_analyzer::ir::VarPath, &VarId)> = self.ir.ports.iter().collect();
        ports.sort_by_key(|p| *p.1);
        for (path, vid) in ports {
            let Some(info) = self.vars.get(vid).cloned() else {
                continue;
            };
            if info.func_local {
                continue;
            }
            let dir = match info.kind {
                VarKind::Input => PortDir::Input,
                VarKind::Output => PortDir::Output,
                VarKind::Inout => PortDir::Inout,
                _ => continue,
            };
            if info.total == 0 {
                continue;
            }
            let segs: Vec<String> = path.0.iter().map(|s| str_of(*s)).collect();
            if segs.len() == 1 {
                let pname = naming::apply_affix(&segs[0], &info.ty.kind, &self.opts.build);
                let pid = public_id(&pname);
                if pid == info.wire {
                    self.m.add_port(&pid, info.total, dir);
                } else {
                    // Rename the variable's wire to the port name.
                    self.rename_wire(*vid, &pid);
                    self.m.add_port(&pid, info.total, dir);
                }
                continue;
            }
            // Expanded modport member: `__<port>_<idx...>_<member>`.
            let base = &segs[0];
            let member = &segs[segs.len() - 1];
            if info.nelem == 1 {
                let pid = public_id(&format!("__{base}_{member}"));
                self.rename_wire(*vid, &pid);
                self.m.add_port(&pid, info.total, dir);
                continue;
            }
            if dir == PortDir::Inout {
                return unsupported("inout expanded modport array port", &info.token);
            }
            let st = strides(&info.shape);
            for f in 0..info.nelem {
                let mut idxs = Vec::new();
                let mut rem = f;
                for (d, s) in info.shape.iter().zip(st.iter()) {
                    let _ = d;
                    idxs.push((rem / s).to_string());
                    rem %= s;
                }
                let pid = public_id(&format!("__{base}_{}_{member}", idxs.join("_")));
                let psig = self.m.add_port(&pid, info.ew, dir);
                let off = (info.nelem - 1 - f) * info.ew;
                let vsig = SigSpec::wire(&info.wire, info.total).extract(off, info.ew);
                match dir {
                    PortDir::Input => self.m.connect(vsig, psig),
                    _ => self.m.connect(psig, vsig),
                }
            }
        }
        Ok(())
    }

    fn rename_wire(&mut self, vid: VarId, new_name: &str) {
        let info = self.vars.get_mut(&vid).unwrap();
        let old = info.wire.clone();
        if old == new_name {
            return;
        }
        // Wires are only referenced after this point (ports are declared
        // before any declaration is processed), so renaming in place is safe.
        for w in self.m.wires.iter_mut() {
            if w.name == old {
                w.name = new_name.to_string();
            }
        }
        self.m.rebuild_wire_index();
        info.wire = new_name.to_string();
    }

    // ----- declarations ------------------------------------------------

    fn next_proc_name(&mut self, hint: &str) -> String {
        self.proc_counter += 1;
        format!("$proc{}${}", self.proc_counter, hint)
    }

    fn declaration(&mut self, idx: usize, d: &Declaration) -> TResult<()> {
        match d {
            Declaration::Comb(c) => {
                let mut p = Proc::default();
                let mut root = CaseBody::default();
                self.statements(&mut p, &mut root, &c.statements)?;
                let updates = self.finish_updates(&p)?;
                if !root.is_empty() {
                    let name = self.next_proc_name(&format!("comb{idx}"));
                    self.m.processes.push(Process {
                        name,
                        root,
                        syncs: vec![],
                        attrs: vec![],
                    });
                }
                // A bit that is not assigned on every path keeps its own
                // value: a combinational loop, which is what sv-elab builds.
                for (lhs, rhs) in updates {
                    self.m.connect(lhs, rhs);
                }
                Ok(())
            }
            Declaration::Ff(ff) => self.ff_declaration(idx, ff),
            Declaration::Inst(inst) => self.inst_declaration(inst),
            Declaration::Initial(x) => {
                if stmts_have_effect(&x.statements) {
                    return unsupported("initial block with assignments", &self.ir.token);
                }
                Ok(())
            }
            Declaration::Final(_) => Ok(()),
            Declaration::External(x) => unsupported("external component", &x.token),
            Declaration::Unsupported(t) => unsupported("unsupported declaration", t),
            Declaration::Null => Ok(()),
        }
    }

    fn finish_updates(&mut self, p: &Proc) -> TResult<Vec<(SigSpec, SigSpec)>> {
        let mut updates = vec![];
        let mut ids: Vec<&VarId> = p.written.keys().collect();
        ids.sort();
        for vid in ids {
            let Some(info) = self.vars.get(vid) else {
                continue;
            };
            if info.func_local || info.konst.is_some() || info.total == 0 {
                continue;
            }
            let Some(fin) = p.cur.get(vid) else { continue };
            let ranges = match &p.written[vid] {
                Written::All => vec![(0, info.total - 1)],
                Written::Ranges(v) => merge_ranges(v.clone()),
            };
            let wire = SigSpec::wire(&info.wire, info.total);
            for (lo, hi) in ranges {
                if lo >= info.total {
                    continue;
                }
                let hi = hi.min(info.total - 1);
                let w = hi - lo + 1;
                updates.push((wire.extract(lo, w), fin.extract(lo, w)));
            }
        }
        Ok(updates)
    }

    fn reset_polarity(&self, kind: &TypeKind) -> (ResetPol, bool) {
        match kind {
            TypeKind::ResetAsyncHigh => (ResetPol::ActiveHigh, false),
            TypeKind::ResetAsyncLow => (ResetPol::ActiveLow, false),
            TypeKind::ResetSyncHigh => (ResetPol::ActiveHigh, true),
            TypeKind::ResetSyncLow => (ResetPol::ActiveLow, true),
            _ => match self.opts.build.reset_type {
                ResetType::AsyncHigh => (ResetPol::ActiveHigh, false),
                ResetType::AsyncLow => (ResetPol::ActiveLow, false),
                ResetType::SyncHigh => (ResetPol::ActiveHigh, true),
                ResetType::SyncLow => (ResetPol::ActiveLow, true),
            },
        }
    }

    fn clock_edge(&self, kind: &TypeKind) -> SyncKind {
        match kind {
            TypeKind::ClockPosedge => SyncKind::Posedge,
            TypeKind::ClockNegedge => SyncKind::Negedge,
            _ => match self.opts.build.clock_type {
                veryl_metadata::ClockType::PosEdge => SyncKind::Posedge,
                veryl_metadata::ClockType::NegEdge => SyncKind::Negedge,
            },
        }
    }

    fn ff_declaration(&mut self, idx: usize, ff: &FfDeclaration) -> TResult<()> {
        let mut p = Proc::default();
        let mut root = CaseBody::default();
        let clk = {
            let (sig, _) = self.read_var(
                &mut p,
                &mut root,
                ff.clock.id,
                &ff.clock.index,
                &ff.clock.select,
                &ff.clock.comptime,
            )?;
            if sig.width() != 1 {
                return internal("clock is not a single bit");
            }
            sig
        };
        let clk_edge = self.clock_edge(&ff.clock.comptime.r#type.kind);
        let reset = match &ff.reset {
            Some(r) => {
                let (sig, _) = self.read_var(
                    &mut p,
                    &mut root,
                    r.id,
                    &r.index,
                    &r.select,
                    &r.comptime,
                )?;
                if sig.width() != 1 {
                    return internal("reset is not a single bit");
                }
                let (pol, sync) = self.reset_polarity(&r.comptime.r#type.kind);
                Some((sig, pol, sync))
            }
            None => None,
        };
        self.statements_ff(&mut p, &mut root, &ff.statements, reset.as_ref())?;
        let updates = self.finish_updates(&p)?;
        if updates.is_empty() {
            return Ok(());
        }
        let mut syncs = vec![Sync {
            kind: clk_edge,
            signal: Some(clk),
            updates: updates.clone(),
        }];
        if let Some((rsig, pol, sync)) = reset
            && !sync
            && root_has_reset_switch(&root)
        {
            syncs.push(Sync {
                kind: match pol {
                    ResetPol::ActiveHigh => SyncKind::Posedge,
                    ResetPol::ActiveLow => SyncKind::Negedge,
                },
                signal: Some(rsig),
                updates,
            });
        }
        let name = self.next_proc_name(&format!("ff{idx}"));
        self.m.processes.push(Process {
            name,
            root,
            syncs,
            attrs: vec![],
        });
        Ok(())
    }

    fn statements_ff(
        &mut self,
        p: &mut Proc,
        case: &mut CaseBody,
        stmts: &[Statement],
        reset: Option<&(SigSpec, ResetPol, bool)>,
    ) -> TResult<()> {
        for s in stmts {
            match s {
                Statement::IfReset(ir) => {
                    let Some((rsig, pol, _)) = reset else {
                        return unsupported("if_reset without a reset signal", &ir.token);
                    };
                    let active = match pol {
                        ResetPol::ActiveHigh => Bit::One,
                        ResetPol::ActiveLow => Bit::Zero,
                    };
                    self.branch(
                        p,
                        case,
                        rsig.clone(),
                        SigSpec::const_bit(active),
                        &ir.true_side,
                        &ir.false_side,
                        Some(reset.unwrap()),
                    )?;
                }
                other => self.statement(p, case, other)?,
            }
        }
        Ok(())
    }

    // ----- statements --------------------------------------------------

    fn statements(&mut self, p: &mut Proc, case: &mut CaseBody, stmts: &[Statement]) -> TResult<()> {
        for s in stmts {
            self.statement(p, case, s)?;
        }
        Ok(())
    }

    fn statement(&mut self, p: &mut Proc, case: &mut CaseBody, s: &Statement) -> TResult<()> {
        match s {
            Statement::Assign(a) => {
                if a.hier_dst.is_some() {
                    return unsupported("hierarchical assignment", &a.token);
                }
                if a.dst.is_empty() {
                    return Ok(());
                }
                let mut widths = Vec::with_capacity(a.dst.len());
                let mut total = 0;
                for d in &a.dst {
                    let w = self.dst_width(d)?;
                    widths.push(w);
                    total += w;
                }
                if total == 0 {
                    return Ok(());
                }
                let val = self.lower_assign(p, case, &a.expr, total)?;
                // Concatenation LHS: dst[0] takes the high bits.
                let mut lo = 0;
                for (d, w) in a.dst.iter().zip(widths.iter()).rev() {
                    let slice = val.extract(lo, *w);
                    self.write_dst(p, case, d, &slice)?;
                    lo += w;
                }
                Ok(())
            }
            Statement::If(i) => self.if_statement(p, case, i),
            Statement::IfReset(i) => unsupported("if_reset outside an always_ff reset context", &i.token),
            Statement::Case(c) => self.case_statement(p, case, c),
            Statement::For(f) => self.for_statement(p, case, f),
            Statement::SystemFunctionCall(c) => {
                match &c.kind {
                    SystemFunctionKind::Display(_)
                    | SystemFunctionKind::Write(_)
                    | SystemFunctionKind::Assert { .. }
                    | SystemFunctionKind::Finish => Ok(()),
                    _ => unsupported("system function call statement", &c.comptime.token),
                }
            }
            Statement::FunctionCall(c) => {
                self.function_call(p, case, c)?;
                Ok(())
            }
            Statement::TbMethodCall(_) => unsupported("testbench method call", &self.ir.token),
            Statement::Break => unsupported("break outside a lowered loop", &self.ir.token),
            Statement::Unsupported(t) => unsupported("unsupported statement", t),
            Statement::Null => Ok(()),
        }
    }

    fn if_statement(&mut self, p: &mut Proc, case: &mut CaseBody, i: &IfStatement) -> TResult<()> {
        let (cw, cs) = self.self_size(&i.cond)?;
        let cond = self.lower(p, case, &i.cond, cw, cs)?;
        let cond = self.m.to_bool(&cond);
        self.branch(
            p,
            case,
            cond,
            SigSpec::const_bit(Bit::One),
            &i.true_side,
            &i.false_side,
            None,
        )
    }

    /// `switch sig { case pat: t; default: f }` with SSA merging of the
    /// variables both sides may write.
    #[allow(clippy::too_many_arguments)]
    fn branch(
        &mut self,
        p: &mut Proc,
        case: &mut CaseBody,
        sig: SigSpec,
        pat: SigSpec,
        t: &[Statement],
        f: &[Statement],
        reset: Option<&(SigSpec, ResetPol, bool)>,
    ) -> TResult<()> {
        if let Some(c) = pat.as_const()
            && let Some(s) = sig.as_const()
        {
            // Constant condition: lower only the taken side.
            let taken = c == s;
            let side = if taken { t } else { f };
            return match reset {
                Some(r) => self.statements_ff(p, case, side, Some(r)),
                None => self.statements(p, case, side),
            };
        }
        let saved = p.cur.clone();
        let mut tb = CaseBody::default();
        match reset {
            Some(r) => self.statements_ff(p, &mut tb, t, Some(r))?,
            None => self.statements(p, &mut tb, t)?,
        }
        let cur_t = std::mem::replace(&mut p.cur, saved.clone());
        let mut fb = CaseBody::default();
        match reset {
            Some(r) => self.statements_ff(p, &mut fb, f, Some(r))?,
            None => self.statements(p, &mut fb, f)?,
        }
        let cur_f = std::mem::replace(&mut p.cur, saved.clone());
        let mut keys: Vec<VarId> = cur_t.keys().chain(cur_f.keys()).copied().collect();
        keys.sort();
        keys.dedup();
        for vid in keys {
            let base = saved
                .get(&vid)
                .cloned()
                .or_else(|| self.vars.get(&vid).map(|i| i.sig()));
            let Some(base) = base else { continue };
            let vt = cur_t.get(&vid).cloned().unwrap_or_else(|| base.clone());
            let vf = cur_f.get(&vid).cloned().unwrap_or_else(|| base.clone());
            if vt == vf {
                p.cur.insert(vid, vt);
                continue;
            }
            let w = vt.width();
            let hint = self
                .vars
                .get(&vid)
                .map(|i| i.wire.trim_start_matches('\\').to_string())
                .unwrap_or_default();
            let tmp = self.m.fresh_wire(&hint, w);
            tb.actions.push((tmp.clone(), vt));
            fb.actions.push((tmp.clone(), vf));
            p.cur.insert(vid, tmp);
        }
        case.switches.push(Switch {
            signal: sig,
            cases: vec![
                Case {
                    patterns: vec![pat],
                    body: tb,
                },
                Case {
                    patterns: vec![],
                    body: fb,
                },
            ],
        });
        Ok(())
    }

    fn case_statement(&mut self, p: &mut Proc, case: &mut CaseBody, c: &CaseStatement) -> TResult<()> {
        let lowered = c.lower_to_nested_if();
        self.statements(p, case, &lowered)
    }

    fn for_statement(&mut self, p: &mut Proc, case: &mut CaseBody, f: &ForStatement) -> TResult<()> {
        let bound = |ctx: &mut Self, p: &mut Proc, case: &mut CaseBody, b: &ForBound| -> TResult<usize> {
            match b {
                ForBound::Const(v, _) => Ok(*v),
                ForBound::Expression(e) => match e.eval_value(&mut ctx.eval) {
                    Some(v) => v.to_usize().ok_or_else(|| {
                        TranslateError::Unsupported("for bound does not fit".into())
                    }),
                    None => {
                        // A bound computed by earlier statements: lower it and
                        // require the result to fold to a constant.
                        let v = ctx.lower_self(p, case, e)?;
                        match v.as_const_u64() {
                            Some(n) => Ok(n as usize),
                            None => unsupported("non-constant for bound", &f.token),
                        }
                    }
                },
            }
        };
        let values: Vec<usize> = match &f.range {
            ForRange::Forward {
                start,
                end,
                inclusive,
                step,
            } => {
                let s = bound(self, p, case, start)?;
                let e = bound(self, p, case, end)?;
                let step = (*step).max(1);
                let mut v = vec![];
                let mut i = s;
                while if *inclusive { i <= e } else { i < e } {
                    v.push(i);
                    i += step;
                }
                v
            }
            ForRange::Reverse {
                start,
                end,
                inclusive,
                step,
            } => {
                let s = bound(self, p, case, start)?;
                let e = bound(self, p, case, end)?;
                let step = (*step).max(1);
                let mut v = vec![];
                let mut i = s;
                while if *inclusive { i <= e } else { i < e } {
                    v.push(i);
                    i += step;
                }
                v.reverse();
                v
            }
            ForRange::Stepped {
                start,
                end,
                inclusive,
                step,
                op,
            } => {
                let s = bound(self, p, case, start)?;
                let e = bound(self, p, case, end)?;
                let mut v = vec![];
                let mut i = s;
                while if *inclusive { i <= e } else { i < e } {
                    v.push(i);
                    let Some(n) = op.eval(i, *step) else { break };
                    if n <= i {
                        break;
                    }
                    i = n;
                    if v.len() > 4096 {
                        break;
                    }
                }
                v
            }
        };
        if values.len() > 4096 {
            return unsupported("for loop with more than 4096 iterations", &f.token);
        }
        let (vw, vsigned) = {
            let w = f.var_type.total_width().unwrap_or(32).max(1);
            (w, f.var_type.signed)
        };
        let has_break = stmts_have_break(&f.body);
        // A loop with `break` carries a flag that disables the rest of the
        // iterations once it fires.
        let brk_id = if has_break {
            Some(self.m.fresh_name("brk"))
        } else {
            None
        };
        let mut brk: SigSpec = SigSpec::const_bit(Bit::Zero);
        for v in values {
            let cst = SigSpec::const_u64(v as u64, vw);
            let _ = vsigned;
            p.cur.insert(f.var_id, cst);
            if let Some(_id) = &brk_id {
                // if (!brk) { body }
                let not_brk = self.m.not1(&brk);
                let saved = p.cur.clone();
                let mut tb = CaseBody::default();
                let mut brk_in = brk.clone();
                self.statements_break(p, &mut tb, &f.body, &mut brk_in)?;
                let cur_t = std::mem::replace(&mut p.cur, saved.clone());
                let mut fb = CaseBody::default();
                let mut keys: Vec<VarId> = cur_t.keys().copied().collect();
                keys.sort();
                for vid in keys {
                    let base = saved
                        .get(&vid)
                        .cloned()
                        .or_else(|| self.vars.get(&vid).map(|i| i.sig()));
                    let Some(base) = base else { continue };
                    let vt = cur_t[&vid].clone();
                    if vt == base {
                        continue;
                    }
                    let tmp = self.m.fresh_wire("loop", vt.width());
                    tb.actions.push((tmp.clone(), vt));
                    fb.actions.push((tmp.clone(), base));
                    p.cur.insert(vid, tmp);
                }
                if brk_in != brk {
                    let tmp = self.m.fresh_wire("brk", 1);
                    tb.actions.push((tmp.clone(), brk_in));
                    fb.actions.push((tmp.clone(), brk.clone()));
                    brk = tmp;
                }
                case.switches.push(Switch {
                    signal: not_brk,
                    cases: vec![
                        Case {
                            patterns: vec![SigSpec::const_bit(Bit::One)],
                            body: tb,
                        },
                        Case {
                            patterns: vec![],
                            body: fb,
                        },
                    ],
                });
            } else {
                self.statements(p, case, &f.body)?;
            }
        }
        p.cur.remove(&f.var_id);
        Ok(())
    }

    /// Statements inside a breakable loop body: once `brk` is set the rest
    /// of the block is skipped.
    fn statements_break(
        &mut self,
        p: &mut Proc,
        case: &mut CaseBody,
        stmts: &[Statement],
        brk: &mut SigSpec,
    ) -> TResult<()> {
        for (i, s) in stmts.iter().enumerate() {
            match s {
                Statement::Break => {
                    *brk = SigSpec::const_bit(Bit::One);
                    return Ok(());
                }
                Statement::If(ifs) if stmts_have_break(&ifs.true_side) || stmts_have_break(&ifs.false_side) => {
                    let (cw, cs) = self.self_size(&ifs.cond)?;
                    let cond = self.lower(p, case, &ifs.cond, cw, cs)?;
                    let cond = self.m.to_bool(&cond);
                    let saved = p.cur.clone();
                    let mut tb = CaseBody::default();
                    let mut brk_t = brk.clone();
                    self.statements_break(p, &mut tb, &ifs.true_side, &mut brk_t)?;
                    let cur_t = std::mem::replace(&mut p.cur, saved.clone());
                    let mut fb = CaseBody::default();
                    let mut brk_f = brk.clone();
                    self.statements_break(p, &mut fb, &ifs.false_side, &mut brk_f)?;
                    let cur_f = std::mem::replace(&mut p.cur, saved.clone());
                    let mut keys: Vec<VarId> = cur_t.keys().chain(cur_f.keys()).copied().collect();
                    keys.sort();
                    keys.dedup();
                    for vid in keys {
                        let base = saved
                            .get(&vid)
                            .cloned()
                            .or_else(|| self.vars.get(&vid).map(|i| i.sig()));
                        let Some(base) = base else { continue };
                        let vt = cur_t.get(&vid).cloned().unwrap_or_else(|| base.clone());
                        let vf = cur_f.get(&vid).cloned().unwrap_or_else(|| base.clone());
                        if vt == vf {
                            p.cur.insert(vid, vt);
                            continue;
                        }
                        let tmp = self.m.fresh_wire("if", vt.width());
                        tb.actions.push((tmp.clone(), vt));
                        fb.actions.push((tmp.clone(), vf));
                        p.cur.insert(vid, tmp);
                    }
                    if brk_t != brk_f {
                        let tmp = self.m.fresh_wire("brk", 1);
                        tb.actions.push((tmp.clone(), brk_t));
                        fb.actions.push((tmp.clone(), brk_f));
                        *brk = tmp;
                    } else {
                        *brk = brk_t;
                    }
                    case.switches.push(Switch {
                        signal: cond,
                        cases: vec![
                            Case {
                                patterns: vec![SigSpec::const_bit(Bit::One)],
                                body: tb,
                            },
                            Case {
                                patterns: vec![],
                                body: fb,
                            },
                        ],
                    });
                    // The remainder runs only when no break fired.
                    let rest = &stmts[i + 1..];
                    if !rest.is_empty() {
                        let not_brk = self.m.not1(brk);
                        let saved = p.cur.clone();
                        let mut tb = CaseBody::default();
                        let mut brk_in = brk.clone();
                        self.statements_break(p, &mut tb, rest, &mut brk_in)?;
                        let cur_t = std::mem::replace(&mut p.cur, saved.clone());
                        let mut fb = CaseBody::default();
                        let mut keys: Vec<VarId> = cur_t.keys().copied().collect();
                        keys.sort();
                        for vid in keys {
                            let base = saved
                                .get(&vid)
                                .cloned()
                                .or_else(|| self.vars.get(&vid).map(|i| i.sig()));
                            let Some(base) = base else { continue };
                            let vt = cur_t[&vid].clone();
                            if vt == base {
                                continue;
                            }
                            let tmp = self.m.fresh_wire("rest", vt.width());
                            tb.actions.push((tmp.clone(), vt));
                            fb.actions.push((tmp.clone(), base));
                            p.cur.insert(vid, tmp);
                        }
                        if brk_in != *brk {
                            let tmp = self.m.fresh_wire("brk", 1);
                            tb.actions.push((tmp.clone(), brk_in));
                            fb.actions.push((tmp.clone(), brk.clone()));
                            *brk = tmp;
                        }
                        case.switches.push(Switch {
                            signal: not_brk,
                            cases: vec![
                                Case {
                                    patterns: vec![SigSpec::const_bit(Bit::One)],
                                    body: tb,
                                },
                                Case {
                                    patterns: vec![],
                                    body: fb,
                                },
                            ],
                        });
                    }
                    return Ok(());
                }
                Statement::Case(c) if stmts_have_break(&c.default)
                    || c.arms.iter().any(|a| stmts_have_break(&a.body)) =>
                {
                    let lowered = c.lower_to_nested_if();
                    let mut rest: Vec<Statement> = lowered;
                    rest.extend_from_slice(&stmts[i + 1..]);
                    return self.statements_break(p, case, &rest, brk);
                }
                Statement::For(f) if stmts_have_break(&f.body) => {
                    // Nested breakable loop: its break only exits itself.
                    self.for_statement(p, case, f)?;
                }
                other => self.statement(p, case, other)?,
            }
        }
        Ok(())
    }

    // ----- assignment destinations ------------------------------------

    /// Width of the slice an assignment destination receives.
    fn dst_width(&mut self, d: &AssignDestination) -> TResult<usize> {
        let r = self.dst_region(d, None)?;
        Ok(r.1)
    }

    /// (offset, width) of a destination.  Dynamic offsets need a process
    /// context to lower their index expressions; when `pw` is `None` only the
    /// width is computed (offset is a placeholder).
    fn dst_region(
        &mut self,
        d: &AssignDestination,
        pw: Option<(&mut Proc, &mut CaseBody)>,
    ) -> TResult<(Offset, usize)> {
        let Some(info) = self.vars.get(&d.id).cloned() else {
            return unsupported(format!("assignment to non-signal {}", d.path), &d.token);
        };
        self.region(&info, &d.index, &d.select, &d.comptime, &d.token, pw)
    }

    fn write_dst(
        &mut self,
        p: &mut Proc,
        case: &mut CaseBody,
        d: &AssignDestination,
        val: &SigSpec,
    ) -> TResult<()> {
        let Some(info) = self.vars.get(&d.id).cloned() else {
            return unsupported(format!("assignment to non-signal {}", d.path), &d.token);
        };
        if info.konst.is_some() {
            return unsupported(format!("assignment to constant {}", d.path), &d.token);
        }
        if info.total == 0 {
            return Ok(());
        }
        if !d.index.0.is_empty() && !d.index.is_const() {
            if info.total > self.opts.max_dynamic_bits {
                return unsupported(
                    format!(
                        "dynamic write into {} ({} bits exceeds the limit of {})",
                        d.path, info.total, self.opts.max_dynamic_bits
                    ),
                    &d.token,
                );
            }
            let base = p.cur.get(&d.id).cloned().unwrap_or_else(|| info.sig());
            let new = self.write_dynamic_array(p, case, &info, &base, &d.index, &d.select, &d.comptime, &d.token, val)?;
            p.cur.insert(d.id, new);
            p.note_write(d.id, None);
            return Ok(());
        }
        let (off, w) = self.region(&info, &d.index, &d.select, &d.comptime, &d.token, Some((p, case)))?;
        let val = val.resize(w, false);
        let base = p
            .cur
            .get(&d.id)
            .cloned()
            .unwrap_or_else(|| info.sig());
        match off {
            Offset::Static(lo) => {
                if lo >= info.total {
                    // Out-of-range constant write: no effect.
                    return Ok(());
                }
                let new = base.splice(lo, &val);
                p.cur.insert(d.id, new);
                p.note_write(d.id, Some((lo, (lo + w - 1).min(info.total - 1))));
            }
            Offset::Dynamic(off_sig) => {
                if info.total > self.opts.max_dynamic_bits {
                    return unsupported(
                        format!(
                            "dynamic write into {} ({} bits exceeds the limit of {})",
                            d.path, info.total, self.opts.max_dynamic_bits
                        ),
                        &d.token,
                    );
                }
                let total = info.total;
                let ones = SigSpec::fill(Bit::One, w).resize(total, false);
                // `$shift` shifts right by B; a negative (signed) B shifts left,
                // so A << off is $shift(A, -off) and bits below 0 fall away.
                let fw = off_sig.width() + 1;
                let o = off_sig.resize(fw, true);
                let noff = self.m.unop("$neg", &o, true, fw);
                let mut mask = self.m.binop("$shift", &ones, &noff, false, true, total);
                if let Some(valid) = self.last_valid.take() {
                    let zero = SigSpec::fill(Bit::Zero, total);
                    mask = self.m.mux(&zero, &mask, &valid);
                }
                let valx = val.resize(total, false);
                let sval = self.m.binop("$shift", &valx, &noff, false, true, total);
                let new = self.m.bwmux(&base, &sval, &mask);
                p.cur.insert(d.id, new);
                p.note_write(d.id, None);
            }
        }
        Ok(())
    }

    /// Resolve index/select/part-select of a variable reference into a bit
    /// offset and width within the variable's flattened storage.
    fn region(
        &mut self,
        info: &VarInfo,
        index: &VarIndex,
        select: &VarSelect,
        ct: &Comptime,
        token: &TokenRange,
        mut pw: Option<(&mut Proc, &mut CaseBody)>,
    ) -> TResult<(Offset, usize)> {
        let (off, w, valid) = self.region_full(info, index, select, ct, token, pw)?;
        self.last_valid = valid;
        Ok((off, w))
    }

    /// Like `region`, also returning the validity flag of a dynamic
    /// unpacked-array index (`None` when always valid).
    fn region_full(
        &mut self,
        info: &VarInfo,
        index: &VarIndex,
        select: &VarSelect,
        ct: &Comptime,
        token: &TokenRange,
        mut pw: Option<(&mut Proc, &mut CaseBody)>,
    ) -> TResult<(Offset, usize, Option<SigSpec>)> {
        // --- unpacked array index ---
        let nidx = index.0.len();
        if nidx > info.shape.len() {
            return unsupported("too many array indices", token);
        }
        let rem_elems: usize = info.shape[nidx..].iter().product::<usize>().max(1);
        let sub_w = rem_elems * info.ew;
        let st = strides(&info.shape);
        let mut off = Offset::Static(0);
        let mut valid_sig: Option<SigSpec> = None;
        if nidx > 0 {
            if index.is_const() {
                let Some(idxs) = index.eval_value(&mut self.eval) else {
                    return unsupported("array index could not be evaluated", token);
                };
                let mut f0 = 0usize;
                for (i, v) in idxs.iter().enumerate() {
                    f0 += v * st[i];
                }
                if f0 + rem_elems > info.nelem {
                    // Out of range: SV reads x / writes nothing.
                    return Ok((Offset::Static(info.total + 1), sub_w, None));
                }
                off = Offset::Static(info.total - (f0 + rem_elems) * info.ew);
            } else {
                let Some((p, case)) = pw.as_mut() else {
                    // Width-only query: keep a placeholder offset and fall
                    // through to the select handling below.
                    return self.region_select_width_only(info, select, ct, token, sub_w);
                };
                // f = sum idx_i * stride_i ; off = (nelem - rem - f) * ew.
                // Everything unsigned; an out-of-range element (f >= count)
                // yields an invalid flag so the access reads x / writes
                // nothing.
                let count = info.nelem / rem_elems;
                let mut fw = bits_for(count.max(2)) + 1;
                let mut idx_sigs = vec![];
                for e in index.0.iter() {
                    let (w, s) = self.self_size(e)?;
                    let v = self.lower(p, case, e, w, s)?;
                    if s {
                        // A negative index is out of range: detect via sign.
                        fw = fw.max(w + 1);
                    } else {
                        fw = fw.max(w + 1);
                    }
                    idx_sigs.push((v, s));
                }
                let mut f: SigSpec = SigSpec::const_u64(0, fw);
                let mut neg: SigSpec = SigSpec::const_bit(Bit::Zero);
                for (i, (v, s)) in idx_sigs.into_iter().enumerate() {
                    if s {
                        let n = v.msb();
                        neg = self.m.binop("$or", &neg, &n, false, false, 1);
                    }
                    let v = v.resize(fw, false);
                    let term = if st[i] == 1 {
                        v
                    } else {
                        let c = SigSpec::const_u64(st[i] as u64, fw);
                        self.m.binop("$mul", &v, &c, false, false, fw)
                    };
                    f = self.m.binop("$add", &f, &term, false, false, fw);
                }
                let cnt = SigSpec::const_u64(count as u64, fw);
                let in_range = self.m.binop("$lt", &f, &cnt, false, false, 1);
                let not_neg = self.m.unop("$logic_not", &neg, false, 1);
                let valid = self.m.binop("$and", &in_range, &not_neg, false, false, 1);
                let base = SigSpec::const_u64((count - 1) as u64, fw);
                let e = self.m.binop("$sub", &base, &f, false, false, fw);
                let ow = bits_for(info.total.max(2)) + 1;
                let ewc = SigSpec::const_u64(sub_w as u64, ow);
                let e = e.resize(ow, false);
                let o = self.m.binop("$mul", &e, &ewc, false, false, ow);
                off = Offset::Dynamic(o);
                valid_sig = Some(valid);
            }
        }
        // --- packed select / member ---
        if select.is_empty() {
            if let Some(ps) = &ct.part_select {
                let moff: usize = ps.part_select.iter().map(|x| x.pos).sum();
                let Some(mw) = ps.part_select.last().and_then(|x| x.r#type.total_width()) else {
                    return unsupported("unresolved member width", token);
                };
                let off = self.off_add(off, moff);
                return Ok((off, mw, valid_sig));
            }
            return Ok((off, sub_w, valid_sig));
        }
        if select.is_const_with_range() {
            let Some((hi, lo)) = select.eval_value(&mut self.eval, &info.ty, false) else {
                return unsupported("select could not be evaluated", token);
            };
            if hi < lo {
                return unsupported("reversed select", token);
            }
            let off = self.off_add(off, lo);
            return Ok((off, hi - lo + 1, valid_sig));
        }
        // Dynamic packed select.
        let Some((p, case)) = pw.as_mut() else {
            // Width only.
            let w = self.dynamic_select_width(info, select, token)?;
            return Ok((Offset::Static(0), w, None));
        };
        let (dyn_off, w) = self.dynamic_select(p, case, info, select, ct, token)?;
        let off = match off {
            Offset::Static(s) => {
                if s == 0 {
                    Offset::Dynamic(dyn_off)
                } else {
                    let fw = dyn_off.width() + 1;
                    let c = SigSpec::const_u64(s as u64, fw);
                    let d = dyn_off.resize(fw, true);
                    Offset::Dynamic(self.m.binop("$add", &d, &c, true, true, fw))
                }
            }
            Offset::Dynamic(d) => {
                // The array part is unsigned, the packed part signed.
                let fw = d.width().max(dyn_off.width()) + 2;
                let a = d.resize(fw, false);
                let b = dyn_off.resize(fw, true);
                Offset::Dynamic(self.m.binop("$add", &a, &b, true, true, fw))
            }
        };
        Ok((off, w, valid_sig))
    }

    /// Width of a reference whose unpacked index is dynamic, computed without
    /// a process context (offset is a placeholder).
    fn region_select_width_only(
        &mut self,
        info: &VarInfo,
        select: &VarSelect,
        ct: &Comptime,
        token: &TokenRange,
        sub_w: usize,
    ) -> TResult<(Offset, usize, Option<SigSpec>)> {
        if select.is_empty() {
            if let Some(ps) = &ct.part_select {
                let Some(mw) = ps.part_select.last().and_then(|x| x.r#type.total_width()) else {
                    return unsupported("unresolved member width", token);
                };
                return Ok((Offset::Static(0), mw, None));
            }
            return Ok((Offset::Static(0), sub_w, None));
        }
        if select.is_const_with_range() {
            let Some((hi, lo)) = select.eval_value(&mut self.eval, &info.ty, false) else {
                return unsupported("select could not be evaluated", token);
            };
            if hi < lo {
                return unsupported("reversed select", token);
            }
            return Ok((Offset::Static(0), hi - lo + 1, None));
        }
        let w = self.dynamic_select_width(info, select, token)?;
        Ok((Offset::Static(0), w, None))
    }

    /// Packed dimension strides (outermost first) and the kind width.
    fn packed_strides(&self, info: &VarInfo) -> (Vec<usize>, usize) {
        let kw = info.ty.kind.width().unwrap_or(1);
        let dims: Vec<usize> = info
            .ty
            .width()
            .iter()
            .map(|d| d.unwrap_or(1))
            .collect();
        let mut st = strides(&dims);
        for s in st.iter_mut() {
            *s *= kw;
        }
        (st, kw)
    }

    fn dynamic_select_width(
        &mut self,
        info: &VarInfo,
        select: &VarSelect,
        token: &TokenRange,
    ) -> TResult<usize> {
        let (st, kw) = self.packed_strides(info);
        let k = select.0.len();
        let elem_w = if st.is_empty() {
            1
        } else if k <= st.len() {
            if k == 0 { info.ew } else { st[k - 1] }
        } else {
            return unsupported("too many packed indices", token);
        };
        let _ = kw;
        match &select.1 {
            None => Ok(elem_w),
            Some((op, e)) => match op {
                VarSelectOp::Colon => unsupported("non-constant range select", token),
                VarSelectOp::PlusColon | VarSelectOp::MinusColon | VarSelectOp::Step => {
                    match e.eval_value(&mut self.eval).and_then(|v| v.to_usize()) {
                        Some(w) => Ok(w),
                        None => unsupported("non-constant select width", token),
                    }
                }
            },
        }
    }

    /// Bit offset (dynamic) and width of a dynamic packed select.
    fn dynamic_select(
        &mut self,
        p: &mut Proc,
        case: &mut CaseBody,
        info: &VarInfo,
        select: &VarSelect,
        ct: &Comptime,
        token: &TokenRange,
    ) -> TResult<(SigSpec, usize)> {
        if ct.part_select.is_some() && ct.member_select_domain.is_some() {
            // The analyzer rebased the index into base coordinates only for
            // single-level selects; be conservative otherwise.
        }
        let (st, _kw) = self.packed_strides(info);
        let k = select.0.len();
        let strides_used: Vec<usize> = if st.is_empty() {
            if k != 1 {
                return unsupported("multi-dimensional select on a scalar", token);
            }
            vec![1]
        } else {
            if k > st.len() {
                return unsupported("too many packed indices", token);
            }
            st[..k].to_vec()
        };
        let elem_w = if st.is_empty() { 1 } else { st[k - 1] };
        // Offsets are signed: a `-:` select whose base is small reaches below
        // bit 0 and SystemVerilog then reads x / writes nothing for those bits.
        let mut idx_sigs = vec![];
        let mut fw = bits_for(info.total.max(2)) + 2;
        for e in select.0.iter() {
            let (w, s) = self.self_size(e)?;
            let v = self.lower(p, case, e, w, s)?;
            fw = fw.max(w + bits_for(info.total.max(2)) + 3);
            idx_sigs.push((v, s));
        }
        let mut off = SigSpec::const_u64(0, fw);
        for (i, (v, sg)) in idx_sigs.into_iter().enumerate() {
            let v = v.resize(fw, sg);
            let term = if strides_used[i] == 1 {
                v
            } else {
                let c = SigSpec::const_u64(strides_used[i] as u64, fw);
                self.m.binop("$mul", &v, &c, true, true, fw)
            };
            off = self.m.binop("$add", &off, &term, true, true, fw);
        }
        let (off, w) = match &select.1 {
            None => (off, elem_w),
            Some((op, e)) => {
                let Some(w) = e.eval_value(&mut self.eval).and_then(|v| v.to_usize()) else {
                    return unsupported("non-constant select width", token);
                };
                match op {
                    VarSelectOp::Colon => return unsupported("non-constant range select", token),
                    VarSelectOp::PlusColon => (off, w),
                    VarSelectOp::MinusColon => {
                        let c = SigSpec::const_u64((w as u64).saturating_sub(1), fw);
                        (self.m.binop("$sub", &off, &c, true, true, fw), w)
                    }
                    VarSelectOp::Step => {
                        let c = SigSpec::const_u64(w as u64, fw);
                        (self.m.binop("$mul", &off, &c, true, true, fw), w)
                    }
                }
            }
        };
        Ok((off, w))
    }

    // ----- variable reads ----------------------------------------------

    fn read_var(
        &mut self,
        p: &mut Proc,
        case: &mut CaseBody,
        id: VarId,
        index: &VarIndex,
        select: &VarSelect,
        ct: &Comptime,
    ) -> TResult<(SigSpec, bool)> {
        let Some(info) = self.vars.get(&id).cloned() else {
            return unsupported(format!("reference to non-signal variable {id}"), &ct.token);
        };
        let base = p.cur.get(&id).cloned().unwrap_or_else(|| info.sig());
        let signed = if !select.is_empty() {
            false
        } else if ct.part_select.is_some() {
            ct.member_signed.unwrap_or(false)
        } else {
            info.ty.signed
        };
        if !index.0.is_empty() && !index.is_const() {
            let sig = self.read_dynamic_array(p, case, &info, &base, index, select, ct)?;
            return Ok((sig, signed));
        }
        let (off, w) = self.region(&info, index, select, ct, &ct.token, Some((p, case)))?;
        let sig = match off {
            Offset::Static(lo) => {
                if lo + w <= info.total {
                    base.extract(lo, w)
                } else if lo >= info.total {
                    SigSpec::fill(Bit::X, w)
                } else {
                    let mut s = base.extract(lo, info.total - lo);
                    s.append(&SigSpec::fill(Bit::X, w - (info.total - lo)));
                    s
                }
            }
            Offset::Dynamic(o) => {
                let valid = self.last_valid.take();
                if info.nelem == 1 && !index.0.is_empty() && select.is_empty() {
                    // A one-element array read through a dynamic index: Yosys'
                    // memory mapping returns the single word regardless of the
                    // address, and SystemVerilog allows any value here.
                    base.extract(0, w.min(info.total)).resize(w, false)
                } else {
                    let v = self.m.binop("$shiftx", &base, &o, false, true, w);
                    match valid {
                        Some(valid) => {
                            let x = SigSpec::fill(Bit::X, w);
                            self.m.mux(&x, &v, &valid)
                        }
                        None => v,
                    }
                }
            }
        };
        Ok((sig, signed))
    }

    // ----- element-wise dynamic array access ----------------------------

    /// Chunk index `g` (unsigned, `k` bits with `2^k > count`) selected by a
    /// dynamic unpacked-array index, the number of chunks and the chunk width.
    /// An out-of-range or negative index yields `g >= count`.
    fn dyn_chunk_index(
        &mut self,
        p: &mut Proc,
        case: &mut CaseBody,
        info: &VarInfo,
        index: &VarIndex,
        token: &TokenRange,
    ) -> TResult<(SigSpec, usize, usize, usize)> {
        let nidx = index.0.len();
        if nidx > info.shape.len() {
            return unsupported("too many array indices", token);
        }
        let rem_elems: usize = info.shape[nidx..].iter().product::<usize>().max(1);
        let sub_w = rem_elems * info.ew;
        let count = info.nelem / rem_elems;
        let st = strides(&info.shape);
        let k = bits_for(count + 1);
        let mut idx_sigs = vec![];
        let mut fw = k;
        for e in index.0.iter() {
            let (w, sg) = self.self_size(e)?;
            let v = self.lower(p, case, e, w, sg)?;
            fw = fw.max(w + 1);
            idx_sigs.push((v, sg));
        }
        let fw = fw + bits_for(count + 1);
        let mut g = SigSpec::const_u64(0, fw);
        let mut neg = SigSpec::const_bit(Bit::Zero);
        for (i, (v, sg)) in idx_sigs.into_iter().enumerate() {
            if sg {
                let n = v.msb();
                neg = self.m.binop("$or", &neg, &n, false, false, 1);
            }
            let v = v.resize(fw, false);
            let term = if st[i] == 1 {
                v
            } else {
                let c = SigSpec::const_u64(st[i] as u64, fw);
                self.m.binop("$mul", &v, &c, false, false, fw)
            };
            g = self.m.binop("$add", &g, &term, false, false, fw);
        }
        // Fold anything out of range into the single value `count`.
        let cnt = SigSpec::const_u64(count as u64, fw);
        let in_range = self.m.binop("$lt", &g, &cnt, false, false, 1);
        let not_neg = self.m.unop("$logic_not", &neg, false, 1);
        let ok = self.m.binop("$and", &in_range, &not_neg, false, false, 1);
        let g = self.m.mux(&cnt, &g, &ok);
        Ok((g.extract(0, k), count, sub_w, k))
    }

    #[allow(clippy::too_many_arguments)]
    fn read_dynamic_array(
        &mut self,
        p: &mut Proc,
        case: &mut CaseBody,
        info: &VarInfo,
        base: &SigSpec,
        index: &VarIndex,
        select: &VarSelect,
        ct: &Comptime,
    ) -> TResult<SigSpec> {
        let (g, count, sub_w, k) = self.dyn_chunk_index(p, case, info, index, &ct.token)?;
        let chunk = if count == 1 {
            // Yosys' memory mapping returns the single word regardless of the
            // address; SystemVerilog allows any value here.
            base.extract(0, sub_w)
        } else {
            // `$bmux` over the chunks; padding slots read as x.
            let slots = 1usize << k;
            let mut a = base.extract(0, count * sub_w);
            a.append(&SigSpec::fill(Bit::X, (slots - count) * sub_w));
            let cm1 = SigSpec::const_u64((count - 1) as u64, k);
            let sel = self.m.binop("$sub", &cm1, &g, false, false, k);
            let y = self.m.fresh_wire("bmux", sub_w);
            self.m.add_cell(
                "$bmux",
                vec![
                    ("\\WIDTH", ParamVal::Int(sub_w as i64)),
                    ("\\S_WIDTH", ParamVal::Int(k as i64)),
                ],
                vec![("\\A", a), ("\\S", sel), ("\\Y", y.clone())],
            );
            y
        };
        // Within the chunk.
        if select.is_empty() {
            if let Some(ps) = &ct.part_select {
                let moff: usize = ps.part_select.iter().map(|x| x.pos).sum();
                let Some(mw) = ps.part_select.last().and_then(|x| x.r#type.total_width()) else {
                    return unsupported("unresolved member width", &ct.token);
                };
                return Ok(chunk.extract(moff, mw));
            }
            return Ok(chunk);
        }
        if select.is_const_with_range() {
            let Some((hi, lo)) = select.eval_value(&mut self.eval, &info.ty, false) else {
                return unsupported("select could not be evaluated", &ct.token);
            };
            if hi < lo {
                return unsupported("reversed select", &ct.token);
            }
            let w = hi - lo + 1;
            if lo + w <= chunk.width() {
                return Ok(chunk.extract(lo, w));
            }
            let mut sg = chunk.extract(lo.min(chunk.width()), chunk.width().saturating_sub(lo));
            sg.append(&SigSpec::fill(Bit::X, w - sg.width()));
            return Ok(sg);
        }
        let (off, w) = self.dynamic_select(p, case, info, select, ct, &ct.token)?;
        Ok(self.m.binop("$shiftx", &chunk, &off, false, true, w))
    }

    #[allow(clippy::too_many_arguments)]
    fn write_dynamic_array(
        &mut self,
        p: &mut Proc,
        case: &mut CaseBody,
        info: &VarInfo,
        base: &SigSpec,
        index: &VarIndex,
        select: &VarSelect,
        ct: &Comptime,
        token: &TokenRange,
        val: &SigSpec,
    ) -> TResult<SigSpec> {
        let (g, count, sub_w, k) = self.dyn_chunk_index(p, case, info, index, token)?;
        // How the value lands inside a chunk.
        enum Inner {
            Static(usize, usize),
            Dynamic(SigSpec, usize),
        }
        let inner = if select.is_empty() {
            match &ct.part_select {
                Some(ps) => {
                    let moff: usize = ps.part_select.iter().map(|x| x.pos).sum();
                    let Some(mw) = ps.part_select.last().and_then(|x| x.r#type.total_width()) else {
                        return unsupported("unresolved member width", token);
                    };
                    Inner::Static(moff, mw)
                }
                None => Inner::Static(0, sub_w),
            }
        } else if select.is_const_with_range() {
            let Some((hi, lo)) = select.eval_value(&mut self.eval, &info.ty, false) else {
                return unsupported("select could not be evaluated", token);
            };
            if hi < lo {
                return unsupported("reversed select", token);
            }
            Inner::Static(lo, hi - lo + 1)
        } else {
            let (off, w) = self.dynamic_select(p, case, info, select, ct, token)?;
            Inner::Dynamic(off, w)
        };
        let mut chunks_lsb_first: Vec<SigSpec> = Vec::with_capacity(count);
        for c in (0..count).rev() {
            // Chunk `c` sits at offset (count-1-c)*sub_w.
            let off = (count - 1 - c) * sub_w;
            let old = base.extract(off, sub_w);
            let new = match &inner {
                Inner::Static(lo, w) => {
                    let v = val.resize(*w, false);
                    if *lo >= sub_w { old.clone() } else { old.splice(*lo, &v) }
                }
                Inner::Dynamic(o, w) => {
                    let v = val.resize(*w, false);
                    let ones = SigSpec::fill(Bit::One, *w).resize(sub_w, false);
                    let fw = o.width() + 1;
                    let o2 = o.resize(fw, true);
                    let noff = self.m.unop("$neg", &o2, true, fw);
                    let mask = self.m.binop("$shift", &ones, &noff, false, true, sub_w);
                    let sval = self.m.binop("$shift", &v.resize(sub_w, false), &noff, false, true, sub_w);
                    self.m.bwmux(&old, &sval, &mask)
                }
            };
            let cc = SigSpec::const_u64(c as u64, k);
            let sel = self.m.binop("$eq", &g, &cc, false, false, 1);
            let merged = self.m.mux(&old, &new, &sel);
            chunks_lsb_first.push(merged);
        }
        let mut sig = SigSpec::concat_lsb_first(&chunks_lsb_first);
        if sig.width() < base.width() {
            sig.append(&base.extract(sig.width(), base.width() - sig.width()));
        }
        Ok(sig)
    }

    // ----- expression sizing -------------------------------------------

    /// Self-determined (width, signed) of an expression under IEEE 1800
    /// rules.
    fn self_size(&mut self, e: &Expression) -> TResult<(usize, bool)> {
        Ok(match e {
            Expression::Term(f) => self.factor_size(f)?,
            Expression::Unary(op, x, ct) => match op {
                Op::LogicNot
                | Op::BitAnd
                | Op::BitOr
                | Op::BitXor
                | Op::BitXnor
                | Op::BitNand
                | Op::BitNor => (1, false),
                Op::BitNot | Op::Add | Op::Sub => self.self_size(x)?,
                _ => return unsupported(format!("unary operator {op:?}"), &ct.token),
            },
            Expression::Binary(x, op, y, ct) => match op {
                Op::Add
                | Op::Sub
                | Op::Mul
                | Op::Div
                | Op::Rem
                | Op::BitAnd
                | Op::BitOr
                | Op::BitXor
                | Op::BitXnor => {
                    let (wx, sx) = self.self_size(x)?;
                    let (wy, sy) = self.self_size(y)?;
                    (wx.max(wy), sx && sy)
                }
                Op::Pow => {
                    let (wx, sx) = self.self_size(x)?;
                    let (_, sy) = self.self_size(y)?;
                    (wx, sx && sy)
                }
                Op::ArithShiftL | Op::ArithShiftR | Op::LogicShiftL | Op::LogicShiftR => {
                    self.self_size(x)?
                }
                Op::LessEq
                | Op::GreaterEq
                | Op::Less
                | Op::Greater
                | Op::Eq
                | Op::EqWildcard
                | Op::Ne
                | Op::NeWildcard
                | Op::LogicAnd
                | Op::LogicOr => (1, false),
                Op::As => self.cast_size(x, y, ct)?,
                _ => return unsupported(format!("binary operator {op:?}"), &ct.token),
            },
            Expression::Ternary(_, a, b, _) => {
                let (wa, sa) = self.self_size(a)?;
                let (wb, sb) = self.self_size(b)?;
                (wa.max(wb), sa && sb)
            }
            Expression::Concatenation(items, ct) => {
                let mut w = 0;
                for (e, rep) in items {
                    let (we, _) = self.self_size(e)?;
                    let n = match rep {
                        Some(r) => match r.eval_value(&mut self.eval).and_then(|v| v.to_usize()) {
                            Some(n) => n,
                            None => return unsupported("non-constant repeat", &ct.token),
                        },
                        None => 1,
                    };
                    w += we * n;
                }
                (w, false)
            }
            Expression::ArrayLiteral(_, ct) => {
                let w = ct
                    .r#type
                    .total_width()
                    .zip(ct.r#type.total_array())
                    .map(|(a, b)| a * b)
                    .unwrap_or(0);
                (w, false)
            }
            Expression::StructConstructor(ty, _, ct) => {
                let Some(w) = ty.total_width() else {
                    return unsupported("unresolved struct width", &ct.token);
                };
                (w, ty.signed)
            }
        })
    }

    fn factor_size(&mut self, f: &Factor) -> TResult<(usize, bool)> {
        match f {
            Factor::Value(ct) => match ct.get_value() {
                Ok(v) if v.width() == 0 => Ok((1, false)),
                Ok(v) => Ok((v.width(), v.signed())),
                Err(_) => unsupported("non-numeric value", &ct.token),
            },
            Factor::Variable(id, index, select, ct) => {
                let Some(info) = self.vars.get(id).cloned() else {
                    return unsupported(format!("reference to non-signal variable {id}"), &ct.token);
                };
                let (_, w) = self.region(&info, index, select, ct, &ct.token, None)?;
                let signed = if !select.is_empty() {
                    false
                } else if ct.part_select.is_some() {
                    ct.member_signed.unwrap_or(false)
                } else {
                    info.ty.signed
                };
                Ok((w, signed))
            }
            Factor::HierVariable(x) => unsupported("hierarchical reference", &x.comptime.token),
            Factor::FunctionCall(c) => {
                let w = c
                    .comptime
                    .r#type
                    .total_width()
                    .zip(c.comptime.r#type.total_array())
                    .map(|(a, b)| a * b)
                    .unwrap_or(0);
                Ok((w, c.comptime.r#type.signed))
            }
            Factor::SystemFunctionCall(c) => match &c.kind {
                SystemFunctionKind::Signed(x) => Ok((self.self_size(&x.0)?.0, true)),
                SystemFunctionKind::Unsigned(x) => Ok((self.self_size(&x.0)?.0, false)),
                SystemFunctionKind::Bits(_)
                | SystemFunctionKind::Size(..)
                | SystemFunctionKind::Clog2(_) => Ok((32, true)),
                SystemFunctionKind::Onehot(_) => Ok((1, false)),
                _ => unsupported("system function in expression", &c.comptime.token),
            },
            Factor::Anonymous(ct) => Ok((ct.r#type.total_width().unwrap_or(0), false)),
            Factor::Unknown(ct) => unsupported("unknown factor", &ct.token),
        }
    }

    fn cast_size(&mut self, x: &Expression, y: &Expression, ct: &Comptime) -> TResult<(usize, bool)> {
        // Width cast: `x as N`
        if let Expression::Term(f) = y
            && let Factor::Value(vct) = f.as_ref()
            && let Ok(v) = vct.get_value()
        {
            let (_, sx) = self.self_size(x)?;
            let Some(n) = v.to_usize() else {
                return unsupported("cast width does not fit", &ct.token);
            };
            return Ok((n, sx));
        }
        if self.is_bool_cast(y) {
            return Ok((1, false));
        }
        let tw = ct.r#type.total_width().zip(ct.r#type.total_array()).map(|(a, b)| a * b);
        match tw {
            Some(w) if w > 0 => Ok((w, ct.r#type.signed)),
            _ => {
                // Clock / reset casts keep the operand.
                self.self_size(x)
            }
        }
    }

    fn is_bool_cast(&self, y: &Expression) -> bool {
        let tok = match y {
            Expression::Term(f) => f.comptime().token,
            _ => return false,
        };
        let text = str_of(tok.beg.text);
        text == "bbool" || text == "lbool"
    }

    // ----- expression lowering ----------------------------------------

    /// Lower `e` for assignment to a `target` bit destination: the
    /// context width is the larger of the target and the expression.
    fn lower_assign(
        &mut self,
        p: &mut Proc,
        case: &mut CaseBody,
        e: &Expression,
        target: usize,
    ) -> TResult<SigSpec> {
        let (w, s) = self.self_size(e)?;
        let cw = w.max(target);
        let v = self.lower(p, case, e, cw, s)?;
        Ok(v.extract(0, target))
    }

    /// Lower `e` evaluated at context width `cw` with context signedness
    /// `cs`; returns exactly `cw` bits.
    fn lower(
        &mut self,
        p: &mut Proc,
        case: &mut CaseBody,
        e: &Expression,
        cw: usize,
        cs: bool,
    ) -> TResult<SigSpec> {
        match e {
            Expression::Term(f) => self.lower_factor(p, case, f, cw, cs),
            Expression::Unary(op, x, ct) => match op {
                Op::BitNot => {
                    let a = self.lower(p, case, x, cw, cs)?;
                    Ok(self.m.unop("$not", &a, cs, cw))
                }
                Op::Add => self.lower(p, case, x, cw, cs),
                Op::Sub => {
                    let a = self.lower(p, case, x, cw, cs)?;
                    Ok(self.m.unop("$neg", &a, cs, cw))
                }
                Op::LogicNot => {
                    let a = self.lower_self(p, case, x)?;
                    let y = self.m.unop("$logic_not", &a, false, 1);
                    Ok(y.resize(cw, false))
                }
                Op::BitAnd | Op::BitOr | Op::BitXor | Op::BitXnor | Op::BitNand | Op::BitNor => {
                    let a = self.lower_self(p, case, x)?;
                    let (kind, neg) = match op {
                        Op::BitAnd => ("$reduce_and", false),
                        Op::BitOr => ("$reduce_or", false),
                        Op::BitXor => ("$reduce_xor", false),
                        Op::BitXnor => ("$reduce_xnor", false),
                        Op::BitNand => ("$reduce_and", true),
                        _ => ("$reduce_or", true),
                    };
                    let mut y = self.m.unop(kind, &a, false, 1);
                    if neg {
                        y = self.m.unop("$logic_not", &y, false, 1);
                    }
                    Ok(y.resize(cw, false))
                }
                _ => unsupported(format!("unary operator {op:?}"), &ct.token),
            },
            Expression::Binary(x, op, y, ct) => self.lower_binary(p, case, x, *op, y, ct, cw, cs),
            Expression::Ternary(c, a, b, _) => {
                let cond = self.lower_self(p, case, c)?;
                let cond = self.m.to_bool(&cond);
                let va = self.lower(p, case, a, cw, cs)?;
                let vb = self.lower(p, case, b, cw, cs)?;
                if let Some(bits) = cond.as_const() {
                    return Ok(match bits[0] {
                        Bit::One => va,
                        Bit::Zero => vb,
                        _ => self.m.mux(&vb, &va, &cond),
                    });
                }
                Ok(self.m.mux(&vb, &va, &cond))
            }
            Expression::Concatenation(items, ct) => {
                let mut parts_msb_first = Vec::with_capacity(items.len());
                for (e, rep) in items {
                    let v = self.lower_self(p, case, e)?;
                    let n = match rep {
                        Some(r) => match r.eval_value(&mut self.eval).and_then(|v| v.to_usize()) {
                            Some(n) => n,
                            None => return unsupported("non-constant repeat", &ct.token),
                        },
                        None => 1,
                    };
                    parts_msb_first.push(v.repeat(n));
                }
                let mut sig = SigSpec::empty();
                for part in parts_msb_first.iter().rev() {
                    sig.append(part);
                }
                Ok(sig.resize(cw, false))
            }
            Expression::ArrayLiteral(items, ct) => {
                let Some(ew) = ct.r#type.total_width() else {
                    return unsupported("unresolved array literal element width", &ct.token);
                };
                let mut elems_msb_first: Vec<SigSpec> = vec![];
                let nelem = ct.r#type.total_array().unwrap_or(1).max(1);
                for item in items {
                    match item {
                        ArrayLiteralItem::Value(e, rep) => {
                            let v = self.lower_assign(p, case, e, ew)?;
                            let n = match rep {
                                Some(r) => match r.eval_value(&mut self.eval).and_then(|v| v.to_usize()) {
                                    Some(n) => n,
                                    None => return unsupported("non-constant repeat", &ct.token),
                                },
                                None => 1,
                            };
                            for _ in 0..n {
                                elems_msb_first.push(v.clone());
                            }
                        }
                        ArrayLiteralItem::Defaul(e) => {
                            // `'{default: v}`: every element not given
                            // explicitly takes `v`.
                            let v = self.lower_assign(p, case, e, ew)?;
                            while elems_msb_first.len() < nelem {
                                elems_msb_first.push(v.clone());
                            }
                        }
                    }
                }
                let mut sig = SigSpec::empty();
                for e in elems_msb_first.iter().rev() {
                    sig.append(e);
                }
                Ok(sig.resize(cw, false))
            }
            Expression::StructConstructor(ty, fields, ct) => {
                let TypeKind::Struct(s) = &ty.kind else {
                    return unsupported("union constructor", &ct.token);
                };
                let mut sig = SigSpec::empty();
                // Last member is at the LSB.
                for member in s.members.iter().rev() {
                    let Some(mw) = member.width() else {
                        return unsupported("unresolved member width", &ct.token);
                    };
                    let Some((_, e)) = fields.iter().find(|(n, _)| *n == member.name) else {
                        return unsupported("missing struct constructor field", &ct.token);
                    };
                    let v = self.lower_assign(p, case, e, mw)?;
                    sig.append(&v);
                }
                Ok(sig.resize(cw, cs && ty.signed))
            }
        }
    }

    /// Lower at the expression's own (self-determined) size.
    fn lower_self(&mut self, p: &mut Proc, case: &mut CaseBody, e: &Expression) -> TResult<SigSpec> {
        let (w, s) = self.self_size(e)?;
        self.lower(p, case, e, w, s)
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_binary(
        &mut self,
        p: &mut Proc,
        case: &mut CaseBody,
        x: &Expression,
        op: Op,
        y: &Expression,
        ct: &Comptime,
        cw: usize,
        cs: bool,
    ) -> TResult<SigSpec> {
        match op {
            Op::Add | Op::Sub | Op::Mul | Op::Div | Op::Rem | Op::BitAnd | Op::BitOr | Op::BitXor
            | Op::BitXnor => {
                let a = self.lower(p, case, x, cw, cs)?;
                let b = self.lower(p, case, y, cw, cs)?;
                let kind = match op {
                    Op::Add => "$add",
                    Op::Sub => "$sub",
                    Op::Mul => "$mul",
                    Op::Div => "$div",
                    Op::Rem => "$mod",
                    Op::BitAnd => "$and",
                    Op::BitOr => "$or",
                    Op::BitXor => "$xor",
                    _ => "$xnor",
                };
                Ok(self.m.binop(kind, &a, &b, cs, cs, cw))
            }
            Op::Pow => {
                let a = self.lower(p, case, x, cw, cs)?;
                let (wb, sb) = self.self_size(y)?;
                let b = self.lower(p, case, y, wb, sb)?;
                Ok(self.m.binop("$pow", &a, &b, cs, sb, cw))
            }
            Op::LogicShiftL | Op::ArithShiftL | Op::LogicShiftR | Op::ArithShiftR => {
                let a = self.lower(p, case, x, cw, cs)?;
                let (wb, sb) = self.self_size(y)?;
                let b = self.lower(p, case, y, wb, sb)?;
                let kind = match op {
                    Op::LogicShiftL | Op::ArithShiftL => "$shl",
                    Op::LogicShiftR => "$shr",
                    _ => "$sshr",
                };
                let a_signed = matches!(op, Op::ArithShiftR) && cs;
                Ok(self.m.binop(kind, &a, &b, a_signed, false, cw))
            }
            Op::Less | Op::LessEq | Op::Greater | Op::GreaterEq | Op::Eq | Op::Ne => {
                let (wx, sx) = self.self_size(x)?;
                let (wy, sy) = self.self_size(y)?;
                let w = wx.max(wy).max(1);
                let s = sx && sy;
                let a = self.lower(p, case, x, w, s)?;
                let b = self.lower(p, case, y, w, s)?;
                let kind = match op {
                    Op::Less => "$lt",
                    Op::LessEq => "$le",
                    Op::Greater => "$gt",
                    Op::GreaterEq => "$ge",
                    Op::Eq => "$eq",
                    _ => "$ne",
                };
                let r = self.m.binop(kind, &a, &b, s, s, 1);
                Ok(r.resize(cw, false))
            }
            Op::EqWildcard | Op::NeWildcard => {
                let (wx, sx) = self.self_size(x)?;
                let (wy, sy) = self.self_size(y)?;
                let w = wx.max(wy).max(1);
                let s = sx && sy;
                let a = self.lower(p, case, x, w, s)?;
                let b = self.lower(p, case, y, w, s)?;
                let r = if let Some(bits) = b.as_const()
                    && bits.iter().any(|b| matches!(b, Bit::X | Bit::Z))
                {
                    let mask: Vec<Bit> = bits
                        .iter()
                        .map(|b| if matches!(b, Bit::X | Bit::Z) { Bit::Zero } else { Bit::One })
                        .collect();
                    let pat: Vec<Bit> = bits
                        .iter()
                        .map(|b| if matches!(b, Bit::X | Bit::Z) { Bit::Zero } else { *b })
                        .collect();
                    let masked = self.m.binop("$and", &a, &SigSpec::consts(mask), false, false, w);
                    self.m.binop("$eq", &masked, &SigSpec::consts(pat), false, false, 1)
                } else {
                    self.m.binop("$eq", &a, &b, s, s, 1)
                };
                let r = if matches!(op, Op::NeWildcard) {
                    self.m.unop("$logic_not", &r, false, 1)
                } else {
                    r
                };
                Ok(r.resize(cw, false))
            }
            Op::LogicAnd | Op::LogicOr => {
                let a = self.lower_self(p, case, x)?;
                let b = self.lower_self(p, case, y)?;
                let kind = if matches!(op, Op::LogicAnd) {
                    "$logic_and"
                } else {
                    "$logic_or"
                };
                let r = self.m.binop(kind, &a, &b, false, false, 1);
                Ok(r.resize(cw, false))
            }
            Op::As => {
                if self.is_bool_cast(y) {
                    let a = self.lower_self(p, case, x)?;
                    let r = self.m.to_bool(&a);
                    return Ok(r.resize(cw, false));
                }
                let (tw, ts) = self.cast_size(x, y, ct)?;
                let (wx, sx) = self.self_size(x)?;
                let inner_w = wx.max(tw);
                let v = self.lower(p, case, x, inner_w, sx)?;
                let v = v.extract(0, tw);
                Ok(v.resize(cw, cs && ts))
            }
            _ => unsupported(format!("binary operator {op:?}"), &ct.token),
        }
    }

    fn lower_factor(
        &mut self,
        p: &mut Proc,
        case: &mut CaseBody,
        f: &Factor,
        cw: usize,
        cs: bool,
    ) -> TResult<SigSpec> {
        match f {
            Factor::Value(ct) => {
                let v = ct
                    .get_value()
                    .map_err(|_| TranslateError::Unsupported("non-numeric value".into()))?;
                if v.width() == 0 {
                    // Unsized fill literal `'0` / `'1` / `'x` / `'z`.
                    let b = fill_bit(v);
                    return Ok(SigSpec::fill(b, cw));
                }
                let sig = value_to_sig(v, v.width());
                Ok(sig.resize(cw, cs && v.signed()))
            }
            Factor::Variable(id, index, select, ct) => {
                let (sig, signed) = self.read_var(p, case, *id, index, select, ct)?;
                Ok(sig.resize(cw, cs && signed))
            }
            Factor::HierVariable(x) => unsupported("hierarchical reference", &x.comptime.token),
            Factor::FunctionCall(c) => {
                let (sig, signed) = self.function_call(p, case, c)?;
                Ok(sig.resize(cw, cs && signed))
            }
            Factor::SystemFunctionCall(c) => self.system_function(p, case, c, cw, cs),
            Factor::Anonymous(ct) => {
                let w = ct.r#type.total_width().unwrap_or(0);
                Ok(SigSpec::fill(Bit::Zero, w).resize(cw, false))
            }
            Factor::Unknown(ct) => unsupported("unknown factor", &ct.token),
        }
    }

    fn system_function(
        &mut self,
        p: &mut Proc,
        case: &mut CaseBody,
        c: &SystemFunctionCall,
        cw: usize,
        cs: bool,
    ) -> TResult<SigSpec> {
        match &c.kind {
            SystemFunctionKind::Signed(x) => {
                let v = self.lower_self(p, case, &x.0)?;
                Ok(v.resize(cw, cs))
            }
            SystemFunctionKind::Unsigned(x) => {
                let v = self.lower_self(p, case, &x.0)?;
                Ok(v.resize(cw, false))
            }
            SystemFunctionKind::Bits(_) | SystemFunctionKind::Size(..) | SystemFunctionKind::Clog2(_) => {
                let Ok(v) = c.comptime.get_value() else {
                    return unsupported("non-constant system function", &c.comptime.token);
                };
                let sig = value_to_sig(v, 32);
                Ok(sig.resize(cw, cs))
            }
            SystemFunctionKind::Onehot(x) => {
                let v = self.lower_self(p, case, &x.0)?;
                let w = v.width().max(1);
                let one = SigSpec::const_u64(1, w);
                let dec = self.m.binop("$sub", &v, &one, false, false, w);
                let and = self.m.binop("$and", &v, &dec, false, false, w);
                let no_more = self.m.unop("$logic_not", &and, false, 1);
                let any = self.m.unop("$reduce_bool", &v, false, 1);
                let r = self.m.binop("$and", &any, &no_more, false, false, 1);
                Ok(r.resize(cw, false))
            }
            _ => unsupported("system function in expression", &c.comptime.token),
        }
    }

    /// Inline a user function call; returns the return value (if any) and
    /// its signedness.
    fn function_call(
        &mut self,
        p: &mut Proc,
        case: &mut CaseBody,
        c: &FunctionCall,
    ) -> TResult<(SigSpec, bool)> {
        let Some(func) = self.funcs.get(&c.id).cloned() else {
            return internal(format!("function {} not found", c.id));
        };
        let body = match &c.index {
            Some(idx) => func.get_function(idx),
            None => func.get_function(&[]),
        };
        let Some(body) = body else {
            return internal("function body not found");
        };
        for (path, expr) in &c.inputs {
            let Some(arg) = body.arg_map.get(path) else {
                return internal(format!("function argument {path} not found"));
            };
            let Some(info) = self.vars.get(arg).cloned() else {
                return internal(format!("function argument {path} has no storage"));
            };
            let v = self.lower_assign(p, case, expr, info.total)?;
            p.cur.insert(*arg, v);
        }
        self.statements(p, case, &body.statements)?;
        for (path, dsts) in &c.outputs {
            let Some(arg) = body.arg_map.get(path) else {
                return internal(format!("function output {path} not found"));
            };
            let Some(info) = self.vars.get(arg).cloned() else {
                return internal(format!("function output {path} has no storage"));
            };
            let out = p.cur.get(arg).cloned().unwrap_or_else(|| info.sig());
            for d in dsts {
                let w = self.dst_width(d)?;
                let v = out.resize(w, false);
                self.write_dst(p, case, d, &v)?;
            }
        }
        let ret_w = c
            .comptime
            .r#type
            .total_width()
            .zip(c.comptime.r#type.total_array())
            .map(|(a, b)| a * b)
            .unwrap_or(0);
        let signed = c.comptime.r#type.signed;
        match body.ret {
            Some(r) => {
                let v = p
                    .cur
                    .get(&r)
                    .cloned()
                    .or_else(|| self.vars.get(&r).map(|i| i.sig()))
                    .unwrap_or_else(|| SigSpec::fill(Bit::X, ret_w));
                Ok((v.resize(ret_w, signed), signed))
            }
            None => Ok((SigSpec::fill(Bit::Zero, ret_w), false)),
        }
    }

    // ----- instances ---------------------------------------------------

    fn inst_declaration(&mut self, inst: &InstDeclaration) -> TResult<()> {
        let child = match inst.component.as_ref() {
            Component::Module(m) => m,
            _ => return unsupported("non-module instance", &inst.token),
        };
        // Modport handles bound for imported functions carry no bits; only a
        // binding of a real signal is unsupported.
        let signal_bindings: Vec<_> = inst
            .interface_bindings
            .iter()
            .filter(|b| {
                child
                    .interface_members
                    .get(&b.child)
                    .or_else(|| child.variables.get(&b.child))
                    .is_some_and(|v| {
                        !matches!(
                            v.r#type.kind,
                            TypeKind::Modport(_, _)
                                | TypeKind::Interface(_)
                                | TypeKind::Instance(_, _)
                                | TypeKind::Module(_)
                                | TypeKind::Package(_)
                                | TypeKind::AbstractInterface(_)
                        )
                    })
            })
            .collect();
        if !signal_bindings.is_empty() {
            let desc: Vec<String> = signal_bindings
                .iter()
                .map(|b| {
                    let c = child
                        .variables
                        .get(&b.child)
                        .map(|v| v.path.to_string())
                        .unwrap_or_else(|| format!("{}", b.child));
                    let pp = self
                        .ir
                        .variables
                        .get(&b.parent)
                        .map(|v| v.path.to_string())
                        .unwrap_or_else(|| format!("{}", b.parent));
                    format!("{c} <- {pp}")
                })
                .collect();
            return unsupported(
                format!("modport function binding ({})", desc.join(", ")),
                &inst.token,
            );
        }
        let key = Translator::module_key(child);
        let Some(child_name) = self.children.get(&key).cloned() else {
            return internal("child module was not translated");
        };
        let mut hier: Vec<String> = inst.hierarchy.iter().map(|s| str_of(*s)).collect();
        hier.push(str_of(inst.name));
        let mut cell_name = public_id(&hier.join("."));
        if !self.cell_names.insert(cell_name.clone()) {
            let mut k = 1;
            while !self.cell_names.insert(format!("{cell_name}${k}")) {
                k += 1;
            }
            cell_name = format!("{cell_name}${k}");
        }

        // Child port map: VarId -> (port name, width, offset-in-var, dir)
        let child_ports = child_port_layout(child, self.opts)?;

        let mut conns: Vec<(String, SigSpec)> = vec![];
        let mut p = Proc::default();
        let mut root = CaseBody::default();
        for input in &inst.inputs {
            let Some(ports) = child_ports.get(&input.id) else {
                return internal(format!("child input port {} not found", input.id));
            };
            let total: usize = ports.iter().map(|x| x.width).sum();
            let sig = if let Some(e) = input.single() {
                self.lower_assign(&mut p, &mut root, e, total)?
            } else {
                if input.exprs.is_empty() || total % input.exprs.len() != 0 {
                    return internal("instance input element count mismatch");
                }
                let per = total / input.exprs.len();
                let mut parts = vec![];
                for e in &input.exprs {
                    parts.push(self.lower_assign(&mut p, &mut root, e, per)?);
                }
                // Element 0 at the MSB.
                let mut sig = SigSpec::empty();
                for part in parts.iter().rev() {
                    sig.append(part);
                }
                sig
            };
            for pp in ports {
                conns.push((pp.name.clone(), sig.extract(pp.offset, pp.width)));
            }
        }
        if !root.is_empty() {
            // Inputs needed statements (a function with branches): the
            // temporaries are driven by the switch tree itself.
            let name = self.next_proc_name("instin");
            self.m.processes.push(Process {
                name,
                root,
                syncs: vec![],
                attrs: vec![],
            });
        }
        for output in &inst.outputs {
            if output.dst.is_empty() {
                continue;
            }
            let Some(ports) = child_ports.get(&output.id) else {
                return internal(format!("child output port {} not found", output.id));
            };
            let total: usize = ports.iter().map(|x| x.width).sum();
            let owire = self.m.fresh_wire(&format!("{}.out", hier.join(".")), total);
            for pp in ports {
                conns.push((pp.name.clone(), owire.extract(pp.offset, pp.width)));
            }
            // Multi-dst: concat-LHS style (dst[0] high) unless element-wise.
            let port_elems = child
                .variables
                .get(&output.id)
                .and_then(|v| v.r#type.total_array())
                .unwrap_or(1);
            let element_wise = output.dst.len() > 1 && port_elems == output.dst.len();
            let mut widths = vec![];
            for d in &output.dst {
                widths.push(self.dst_width(d)?);
            }
            let order: Vec<usize> = if element_wise {
                (0..output.dst.len()).collect()
            } else {
                (0..output.dst.len()).rev().collect()
            };
            let mut lo = 0;
            for i in order {
                let w = widths[i];
                let slice = if element_wise {
                    // dst[i] is element i: element 0 at the MSB.
                    let off = total - (i + 1) * w;
                    owire.extract(off, w)
                } else {
                    let s = owire.extract(lo, w);
                    lo += w;
                    s
                };
                self.connect_dst(&output.dst[i], &slice)?;
            }
        }
        self.m.add_cell_named(
            &cell_name,
            &public_id_or_private(&child_name),
            vec![],
            conns,
        );
        Ok(())
    }

    /// Continuous drive of a destination from an instance output.
    fn connect_dst(&mut self, d: &AssignDestination, val: &SigSpec) -> TResult<()> {
        let Some(info) = self.vars.get(&d.id).cloned() else {
            return unsupported(format!("instance output to non-signal {}", d.path), &d.token);
        };
        let (off, w) = self.region(&info, &d.index, &d.select, &d.comptime, &d.token, None)?;
        let Offset::Static(lo) = off else {
            return unsupported("dynamic instance output destination", &d.token);
        };
        if !d.index.is_const() || !d.select.is_const_with_range() {
            return unsupported("dynamic instance output destination", &d.token);
        }
        if lo >= info.total {
            return Ok(());
        }
        let w = w.min(info.total - lo);
        let lhs = SigSpec::wire(&info.wire, info.total).extract(lo, w);
        self.m.connect(lhs, val.resize(w, false));
        Ok(())
    }
}

#[derive(Clone, Debug)]
enum Offset {
    Static(usize),
    Dynamic(SigSpec),
}

impl ModCtx<'_> {
    fn off_add(&mut self, off: Offset, c: usize) -> Offset {
        match off {
            Offset::Static(s) => Offset::Static(s + c),
            Offset::Dynamic(d) => {
                if c == 0 {
                    Offset::Dynamic(d)
                } else {
                    let fw = d.width() + 1;
                    let k = SigSpec::const_u64(c as u64, fw);
                    let d = d.resize(fw, false);
                    Offset::Dynamic(self.m.binop("$add", &d, &k, true, true, fw))
                }
            }
        }
    }
}

#[derive(Clone, Debug)]
struct ChildPort {
    name: String,
    width: usize,
    offset: usize,
}

/// Port wires of a child module keyed by its port variable id, in the same
/// naming/layout as `ModCtx::declare_ports`.
fn child_port_layout(child: &IrModule, opts: &Options) -> TResult<HashMap<VarId, Vec<ChildPort>>> {
    let mut ret = HashMap::new();
    for (path, vid) in &child.ports {
        let Some(v) = child.variables.get(vid) else { continue };
        if !matches!(v.kind, VarKind::Input | VarKind::Output | VarKind::Inout) {
            continue;
        }
        if matches!(v.affiliation, Affiliation::Function) {
            continue;
        }
        let Some(ew) = v.r#type.total_width() else { continue };
        let shape: Vec<usize> = v.r#type.array.iter().map(|d| d.unwrap_or(1)).collect();
        let nelem: usize = shape.iter().product();
        let total = ew * nelem;
        if total == 0 {
            continue;
        }
        let segs: Vec<String> = path.0.iter().map(|s| str_of(*s)).collect();
        let mut ports = vec![];
        if segs.len() == 1 {
            let pname = naming::apply_affix(&segs[0], &v.r#type.kind, &opts.build);
            ports.push(ChildPort {
                name: public_id(&pname),
                width: total,
                offset: 0,
            });
        } else if nelem == 1 {
            let base = &segs[0];
            let member = &segs[segs.len() - 1];
            ports.push(ChildPort {
                name: public_id(&format!("__{base}_{member}")),
                width: total,
                offset: 0,
            });
        } else {
            let base = &segs[0];
            let member = &segs[segs.len() - 1];
            let st = strides(&shape);
            for f in 0..nelem {
                let mut idxs = Vec::new();
                let mut rem = f;
                for s in st.iter() {
                    idxs.push((rem / s).to_string());
                    rem %= s;
                }
                ports.push(ChildPort {
                    name: public_id(&format!("__{base}_{}_{member}", idxs.join("_"))),
                    width: ew,
                    offset: (nelem - 1 - f) * ew,
                });
            }
        }
        ret.insert(*vid, ports);
    }
    Ok(ret)
}

fn const_bits(v: &Variable, ew: usize, nelem: usize) -> Option<SigSpec> {
    if v.value.is_empty() || ew * nelem == 0 {
        return None;
    }
    let single = v.value.len() == 1;
    let mut sig = SigSpec::empty();
    // Element nelem-1 is at the LSB.
    for f in (0..nelem).rev() {
        let val = if single { &v.value[0] } else { v.value.get(f)? };
        sig.append(&value_to_sig(val, ew));
    }
    Some(sig)
}

fn stmts_have_break(stmts: &[Statement]) -> bool {
    stmts.iter().any(|s| match s {
        Statement::Break => true,
        Statement::If(i) => stmts_have_break(&i.true_side) || stmts_have_break(&i.false_side),
        Statement::IfReset(i) => stmts_have_break(&i.true_side) || stmts_have_break(&i.false_side),
        Statement::Case(c) => {
            stmts_have_break(&c.default) || c.arms.iter().any(|a| stmts_have_break(&a.body))
        }
        // A nested loop's break belongs to that loop.
        Statement::For(_) => false,
        _ => false,
    })
}

fn stmts_have_effect(stmts: &[Statement]) -> bool {
    stmts.iter().any(|s| match s {
        Statement::Assign(_) | Statement::FunctionCall(_) | Statement::TbMethodCall(_) => true,
        Statement::If(i) => stmts_have_effect(&i.true_side) || stmts_have_effect(&i.false_side),
        Statement::IfReset(i) => stmts_have_effect(&i.true_side) || stmts_have_effect(&i.false_side),
        Statement::Case(c) => {
            stmts_have_effect(&c.default) || c.arms.iter().any(|a| stmts_have_effect(&a.body))
        }
        Statement::For(f) => stmts_have_effect(&f.body),
        Statement::SystemFunctionCall(c) => matches!(c.kind, SystemFunctionKind::Readmemh(..)),
        _ => false,
    })
}

fn root_has_reset_switch(root: &CaseBody) -> bool {
    !root.switches.is_empty()
}

fn public_id_or_private(name: &str) -> String {
    if name.starts_with('$') {
        name.to_string()
    } else {
        public_id(name)
    }
}

// Unused-import silencers for items referenced only in some cfgs.
#[allow(dead_code)]
fn _unused(_: &IfResetStatement, _: &Arc<Component>, _: &AttrVal, _: &ParamVal) {}
