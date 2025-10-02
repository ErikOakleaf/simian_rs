use crate::backend::CompilationError;
use std::{cell::RefCell, collections::HashMap, rc::Rc};

#[derive(Clone, Debug, PartialEq)]
pub enum SymbolScope {
    Global,
    Local,
    Builtin,
    Free,
    Function,
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
    pub store: HashMap<String, Symbol>,
    pub amount_definitions: usize,

    pub free_symbols: Vec<Symbol>,
}

impl SymbolTable {
    pub fn new() -> Rc<RefCell<Self>> {
        Rc::new(RefCell::new(SymbolTable {
            outer: None,
            store: HashMap::<String, Symbol>::new(),
            amount_definitions: 0,
            free_symbols: Vec::<Symbol>::new(),
        }))
    }

    pub fn new_enclosed(outer: Rc<RefCell<SymbolTable>>) -> Rc<RefCell<Self>> {
        Rc::new(RefCell::new(SymbolTable {
            outer: Some(outer),
            store: HashMap::<String, Symbol>::new(),
            amount_definitions: 0,
            free_symbols: Vec::<Symbol>::new(),
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

    pub fn define_function_name(&mut self, name: &str) -> Symbol {
        let symbol = Symbol {
            name: name.to_string(),
            scope: SymbolScope::Function,
            index: 0,
        };
        self.store.insert(name.to_string(), symbol.clone());
        symbol
    }

    pub fn define_builtin(&mut self, index: u16, name: &str) -> Symbol {
        let symbol = Symbol {
            name: name.to_string(),
            scope: SymbolScope::Builtin,
            index: index,
        };

        self.store.insert(name.to_string(), symbol.clone());
        symbol
    }

    pub fn define_free(&mut self, original: Symbol) -> Symbol {
        self.free_symbols.push(original.clone());

        let symbol = Symbol {
            name: original.name.clone(),
            index: self.free_symbols.len() as u16 - 1,
            scope: SymbolScope::Free,
        };
        self.store.insert(original.name, symbol.clone());

        symbol
    }

    pub fn resolve(&mut self, name: &str) -> Result<Symbol, CompilationError> {
        if let Some(symbol) = self.store.get(name) {
            return Ok(symbol.clone());
        }

        if let Some(outer) = &self.outer {
            let resolved = outer.borrow_mut().resolve(name)?;
            match resolved.scope {
                SymbolScope::Global | SymbolScope::Builtin => Ok(resolved),
                _ => {
                    let free = self.define_free(resolved);
                    Ok(free)
                }
            }
        } else {
            Err(CompilationError::UnknownSymbol(name.to_string()))
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
        let global = SymbolTable::new();

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
            let symbol = global.borrow_mut().resolve(test.0)?;
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
            let symbol = local.borrow_mut().resolve(test.0)?;
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

        for mut test in tests {
            for expected_symbol in test.expected_symbols {
                let symbol = test.table.resolve(expected_symbol.0)?;
                assert_eq!(expected_symbol.1, symbol);
            }
        }

        Ok(())
    }

    #[test]
    fn test_resolve_builtin() -> Result<(), CompilationError> {
        let global = SymbolTable::new();

        let tests = vec![
            (
                "a",
                Symbol {
                    name: "a".to_string(),
                    scope: SymbolScope::Builtin,
                    index: 0,
                },
            ),
            (
                "c",
                Symbol {
                    name: "c".to_string(),
                    scope: SymbolScope::Builtin,
                    index: 1,
                },
            ),
            (
                "e",
                Symbol {
                    name: "e".to_string(),
                    scope: SymbolScope::Builtin,
                    index: 2,
                },
            ),
            (
                "f",
                Symbol {
                    name: "f".to_string(),
                    scope: SymbolScope::Builtin,
                    index: 3,
                },
            ),
        ];

        for (i, test) in tests.iter().enumerate() {
            global.borrow_mut().define_builtin(i as u16, test.0);
        }

        for test in tests {
            let symbol = global.borrow_mut().resolve(test.0)?;
            assert_eq!(test.1, symbol);
        }

        Ok(())
    }

    #[test]
    fn test_resolve_free() -> Result<(), CompilationError> {
        struct Test {
            table: Rc<RefCell<SymbolTable>>,
            expected_symbols: Vec<Symbol>,
            expected_free_symbols: Vec<Symbol>,
        }

        let global = SymbolTable::new();
        global.borrow_mut().define("a");
        global.borrow_mut().define("b");

        let first_local = SymbolTable::new_enclosed(Rc::clone(&global));
        first_local.borrow_mut().define("c");
        first_local.borrow_mut().define("d");

        let second_local = SymbolTable::new_enclosed(Rc::clone(&first_local));
        second_local.borrow_mut().define("e");
        second_local.borrow_mut().define("f");

        let tests = vec![
            Test {
                table: first_local.clone(),
                expected_symbols: vec![
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
                ],
                expected_free_symbols: vec![],
            },
            Test {
                table: second_local,
                expected_symbols: vec![
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
                        scope: SymbolScope::Free,
                        index: 0,
                    },
                    Symbol {
                        name: "d".to_string(),
                        scope: SymbolScope::Free,
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
                ],
                expected_free_symbols: vec![
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
                ],
            },
        ];

        for test in tests {
            for expected in test.expected_symbols {
                let result = test.table.borrow_mut().resolve(&expected.name)?;
                assert_eq!(
                    expected, result,
                    "for resolving {} expected symbol {:?} got symbol {:?}",
                    expected.name, expected, result
                );
            }

            let free_symbols = &test.table.borrow().free_symbols;
            assert_eq!(
                free_symbols.len(),
                test.expected_free_symbols.len(),
                "wrong number of free symbols. got={}, want={}",
                free_symbols.len(),
                test.expected_free_symbols.len()
            );

            for (i, expected_free) in test.expected_free_symbols.iter().enumerate() {
                assert_eq!(
                    free_symbols[i], *expected_free,
                    "wrong free symbol at {}. got={:?}, want={:?}",
                    i, free_symbols[i], expected_free
                );
            }
        }

        Ok(())
    }

    #[test]
    fn test_resolve_unresolvable_free() -> Result<(), CompilationError> {
        let global = SymbolTable::new();
        global.borrow_mut().define("a");

        let first_local = SymbolTable::new_enclosed(Rc::clone(&global));
        first_local.borrow_mut().define("c");

        let second_local = SymbolTable::new_enclosed(Rc::clone(&first_local));
        second_local.borrow_mut().define("e");
        second_local.borrow_mut().define("f");

        let expected = vec![
            Symbol {
                name: "a".to_string(),
                scope: SymbolScope::Global,
                index: 0,
            },
            Symbol {
                name: "c".to_string(),
                scope: SymbolScope::Free,
                index: 0,
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

        for symbol in expected {
            let result = second_local.borrow_mut().resolve(&symbol.name)?;
            assert_eq!(symbol, result, "name {} not resolvable", symbol.name);
        }

        let expected_unresolvable = vec!["b", "d"];

        for name in expected_unresolvable {
            let result = second_local.borrow_mut().resolve(name);
            match result {
                Ok(_) => {
                    panic!("name {} resolved but was not expected to", name)
                }
                Err(_) => {}
            }
        }

        Ok(())
    }

    #[test]
    fn test_define_and_resolve_function_name() -> Result<(), CompilationError> {
        let global = SymbolTable::new();
        global.borrow_mut().define_function_name("a");

        let expected = Symbol {
            name: "a".to_string(),
            scope: SymbolScope::Function,
            index: 0,
        };

        let result = global.borrow_mut().resolve(&expected.name)?;

        assert_eq!(
            expected, result,
            "expected {} to resolve to {:?} got {:?}",
            expected.name, expected, result
        );

        Ok(())
    }

    #[test]
    fn test_shadowing_function_name() -> Result<(), CompilationError> {
        let global = SymbolTable::new();
        global.borrow_mut().define_function_name("a");
        global.borrow_mut().define("a");

        let expected = Symbol {
            name: "a".to_string(),
            scope: SymbolScope::Global,
            index: 0,
        };

        let result = global.borrow_mut().resolve(&expected.name)?;

        assert_eq!(
            expected, result,
            "expected {} to resolve to {:?} got {:?}",
            expected.name, expected, result
        );

        Ok(())
    }
}
