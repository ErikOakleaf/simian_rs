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
pub struct SymbolTable {
    pub outer: Option<Rc<RefCell<SymbolTable>>>,
    store: HashMap<String, Symbol>,
    pub amount_definitions: usize,
}

impl SymbolTable {
    pub fn new() -> Rc<RefCell<Self>> {
        Rc::new(RefCell::new(SymbolTable {
            outer: None,
            store: HashMap::<String, Symbol>::new(),
            amount_definitions: 0,
        }))
    }

    pub fn new_enclosed(outer: Rc<RefCell<SymbolTable>>) -> Rc<RefCell<Self>> {
        Rc::new(RefCell::new(SymbolTable {
            outer: Some(outer),
            store: HashMap::<String, Symbol>::new(),
            amount_definitions: 0,
        }))
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
            index: self.amount_definitions as u16,
        };

        self.store.insert(name.to_string(), symbol.clone());
        self.amount_definitions += 1;
        symbol
    }

    pub fn resolve(&self, name: &str) -> Result<Symbol, CompilationError> {
        match self.store.get(name) {
            None => {
                if let Some(outer) = &self.outer {
                    outer.as_ref().borrow().resolve(name)
                } else {
                    Err(CompilationError::UnknownSymbol(name.to_string()))
                }
            }
            Some(symbol) => Ok(symbol.clone()),
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

        let global = SymbolTable::new();

        let a = global.borrow_mut().define("a");
        let b = global.borrow_mut().define("b");

        assert_eq!(tests[0], a);
        assert_eq!(tests[1], b);

        let first_local = SymbolTable::new_enclosed(Rc::clone(&global));

        let c = first_local.borrow_mut().define("c");
        let d = first_local.borrow_mut().define("d");

        assert_eq!(tests[2], c);
        assert_eq!(tests[3], d);

        let second_local = SymbolTable::new_enclosed(Rc::clone(&global));

        let e = second_local.borrow_mut().define("e");
        let f = second_local.borrow_mut().define("f");

        assert_eq!(tests[4], e);
        assert_eq!(tests[5], f);
    }

    #[test]
    fn test_resolve_global() -> Result<(), CompilationError> {
        let mut global = SymbolTable::new();

        global.borrow_mut().define("a");
        global.borrow_mut().define("b");

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
            let symbol = global.borrow().resolve(test.0)?;
            assert_eq!(test.1, symbol);
        }

        Ok(())
    }

    #[test]
    fn test_resolve_local() -> Result<(), CompilationError> {
        let global = SymbolTable::new();
        global.borrow_mut().define("a");
        global.borrow_mut().define("b");

        let local = SymbolTable::new_enclosed(Rc::clone(&global));
        local.borrow_mut().define("c");
        local.borrow_mut().define("d");

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
            let symbol = local.borrow().resolve(test.0)?;
            assert_eq!(test.1, symbol);
        }

        Ok(())
    }

    #[test]
    fn test_resolve_nested_local() -> Result<(), CompilationError> {
        let global = SymbolTable::new();
        global.borrow_mut().define("a");
        global.borrow_mut().define("b");

        let first_local = SymbolTable::new_enclosed(Rc::clone(&global));
        first_local.borrow_mut().define("c");
        first_local.borrow_mut().define("d");

        let second_local = SymbolTable::new_enclosed(Rc::clone(&global));
        second_local.borrow_mut().define("e");
        second_local.borrow_mut().define("f");

        struct Test {
            table: SymbolTable,
            expected_symbols: Vec<(&'static str, Symbol)>,
        }

        let tests = vec![
            Test {
                table: first_local.borrow().clone(),
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
                table: second_local.borrow().clone(),
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
                assert_eq!(expected_symbol.1, symbol);
            }
        }

        Ok(())
    }
}
