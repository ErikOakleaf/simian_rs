use std::fmt;

enum Object {
    Integer(i64),
    Boolean(bool),
    Null,
}

impl fmt::Display for Object {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Object::Integer(value) => {
                write!(f, "{}", value)
            }
            Object::Boolean(value) => {
                write!(f, "{}", value)
            }
            Object::Null => {
                write!(f, "null")
            }
        }
    }
}
