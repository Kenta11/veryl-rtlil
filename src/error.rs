use veryl_parser::token_range::TokenRange;

#[derive(Debug, thiserror::Error)]
pub enum TranslateError {
    #[error("unsupported: {0}")]
    Unsupported(String),
    #[error("internal: {0}")]
    Internal(String),
}

pub type TResult<T> = Result<T, TranslateError>;

pub fn loc(token: &TokenRange) -> String {
    format!("{}:{}", token.beg.line, token.beg.column)
}

pub fn unsupported<T>(what: impl Into<String>, token: &TokenRange) -> TResult<T> {
    Err(TranslateError::Unsupported(format!(
        "{} (at {})",
        what.into(),
        loc(token)
    )))
}

pub fn internal<T>(what: impl Into<String>) -> TResult<T> {
    Err(TranslateError::Internal(what.into()))
}
