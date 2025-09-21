use crate::backend::CompilationError;
use std::{cell::RefCell, collections::HashMap, rc::Rc};

#[derive(Clone, Debug, PartialEq)]
pub enum SymbolScope {
    Global,
    Local,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Symbol {
    pub name: String,
    pub scope: SymbolScope,
    pub index: u16,
}

#[derive(Clone, Debug, PartialEq)]
pub struct SymbolTable<'a> {
    pub outer: Option<&'a SymbolTable<'a>>,
    store: HashMap<String, Symbol>,
    amount_definitons: usize,
}

impl<'a> SymbolTable<'a> {
    pub fn new() -> Self {
        SymbolTable {
            outer: None,
            store: HashMap::<String, Symbol>::new(),
            amount_definitons: 0,
        }
    }

    pub fn new_enclosed(outer: &'a SymbolTable<'a>) -> Self {
        SymbolTable {
            outer: Some(outer),
            store: HashMap::<String, Symbol>::new(),
            amount_definitons: 0,
        }
    }

    pub fn define(&mut self, name: &str) -> Symbol {
        let scope = if self.outer.is_none() {
            SymbolScope::Global
        } else {
            SymbolScope::Local
        };

        let symbol = Symbol {
            name: name.to_string(),
            scope: scope,
            index: self.amount_definitons as u16,
        };

        self.store.insert(name.to_string(), symbol.clone());
        self.amount_definitons += 1;
        symbol
    }

    pub fn resolve(&self, name: &str) -> Result<&Symbol, CompilationError> {
        match self.store.get(name) {
            None => {
                if let Some(outer) = &self.outer {
                    outer.resolve(name)
                } else {
                    Err(CompilationError::UnknownSymbol(name.to_string()))
                }
            }
            Some(symbol) => Ok(symbol),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_define() {
        let tests = vec![
            Symbol {
                name: "a".to_string(),
                scope: SymbolScope::Global,
                index: 0,
            },
            Symbol {
                name: "b".to_string(),
                scope: SymbolScope::Global,
                index: 1,
            },
            Symbol {
                name: "c".to_string(),
                scope: SymbolScope::Local,
                index: 0,
            },
            Symbol {
                name: "d".to_string(),
                scope: SymbolScope::Local,
                index: 1,
            },
            Symbol {
                name: "e".to_string(),
                scope: SymbolScope::Local,
                index: 0,
            },
            Symbol {
                name: "f".to_string(),
                scope: SymbolScope::Local,
                index: 1,
            },
        ];

        let mut global = SymbolTable::new();

        let a = global.define("a");
        let b = global.define("b");

        assert_eq!(tests[0], a);
        assert_eq!(tests[1], b);

        let mut first_local = SymbolTable::new_enclosed(&global);

        let c = first_local.define("c");
        let d = first_local.define("d");

        assert_eq!(tests[2], c);
        assert_eq!(tests[3], d);

        let mut second_local = SymbolTable::new_enclosed(&global);

        let e = second_local.define("e");
        let f = second_local.define("f");

        assert_eq!(tests[4], e);
        assert_eq!(tests[5], f);
    }

    #[test]
    fn test_resolve_global() -> Result<(), CompilationError> {
        let mut global = SymbolTable::new();

        global.define("a");
        global.define("b");

        let tests = vec![
            (
                "a",
                Symbol {
                    name: "a".to_string(),
                    scope: SymbolScope::Global,
                    index: 0,
                },
            ),
            (
                "b",
                Symbol {
                    name: "b".to_string(),
                    scope: SymbolScope::Global,
                    index: 1,
                },
            ),
        ];

        for test in tests {
            let symbol = global.resolve(test.0)?;
            assert_eq!(test.1, *symbol);
        }

        Ok(())
    }

    #[test]
    fn test_resolve_local() -> Result<(), CompilationError> {
        let mut global = SymbolTable::new();
        global.define("a");
        global.define("b");

        let mut local = SymbolTable::new_enclosed(&global);
        local.define("c");
        local.define("d");

        let tests = vec![
            (
                "a",
                Symbol {
                    name: "a".to_string(),
                    scope: SymbolScope::Global,
                    index: 0,
                },
            ),
            (
                "b",
                Symbol {
                    name: "b".to_string(),
                    scope: SymbolScope::Global,
                    index: 1,
                },
            ),
            (
                "c",
                Symbol {
                    name: "c".to_string(),
                    scope: SymbolScope::Local,
                    index: 0,
                },
            ),
            (
                "d",
                Symbol {
                    name: "d".to_string(),
                    scope: SymbolScope::Local,
                    index: 1,
                },
            ),
        ];

        for test in tests {
            let symbol = local.resolve(test.0)?;
            assert_eq!(test.1, *symbol);
        }

        Ok(())
    }

    #[test]
    fn test_resolve_nested_local() -> Result<(), CompilationError> {
        let mut global = SymbolTable::new();
        global.define("a");
        global.define("b");

        let mut first_local = SymbolTable::new_enclosed(&global);
        first_local.define("c");
        first_local.define("d");

        let mut second_local = SymbolTable::new_enclosed(&global);
        second_local.define("e");
        second_local.define("f");

        struct Test<'a> {
            table: SymbolTable<'a>,
            expected_symbols: Vec<(&'static str, Symbol)>,
        }

        let tests = vec![
            Test {
                table: first_local,
                expected_symbols: vec![
                    (
                        "a",
                        Symbol {
                            name: "a".to_string(),
                            scope: SymbolScope::Global,
                            index: 0,
                        },
                    ),
                    (
                        "b",
                        Symbol {
                            name: "b".to_string(),
                            scope: SymbolScope::Global,
                            index: 1,
                        },
                    ),
                    (
                        "c",
                        Symbol {
                            name: "c".to_string(),
                            scope: SymbolScope::Local,
                            index: 0,
                        },
                    ),
                    (
                        "d",
                        Symbol {
                            name: "d".to_string(),
                            scope: SymbolScope::Local,
                            index: 1,
                        },
                    ),
                ],
            },
            Test {
                table: second_local,
                expected_symbols: vec![
                    (
                        "a",
                        Symbol {
                            name: "a".to_string(),
                            scope: SymbolScope::Global,
                            index: 0,
                        },
                    ),
                    (
                        "b",
                        Symbol {
                            name: "b".to_string(),
                            scope: SymbolScope::Global,
                            index: 1,
                        },
                    ),
                    (
                        "e",
                        Symbol {
                            name: "e".to_string(),
                            scope: SymbolScope::Local,
                            index: 0,
                        },
                    ),
                    (
                        "f",
                        Symbol {
                            name: "f".to_string(),
                            scope: SymbolScope::Local,
                            index: 1,
                        },
                    ),
                ],
            },
        ];

        for test in tests {
            for expected_symbol in test.expected_symbols {
                let symbol = test.table.resolve(expected_symbol.0)?;
                assert_eq!(expected_symbol.1, *symbol);
            }
        }

        Ok(())
    }
}
