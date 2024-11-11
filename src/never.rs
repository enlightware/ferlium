use std::fmt::Display;

#[derive(Debug, Clone)]
pub enum Never {}

impl Display for Never {
    fn fmt(&self, _f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {}
    }
}
