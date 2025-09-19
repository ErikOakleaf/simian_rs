use std::collections::HashMap;
use crate::backend::CompilationError;

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
    store: HashMap<String, Symbol>,
    amount_definitons: usize,
}

impl SymbolTable {
    pub fn new() -> Self {
        SymbolTable {
            store: HashMap::<String, Symbol>::new(),
            amount_definitons: 0,
        }
    }

    pub fn define(&mut self, name: &str) -> Symbol {
        let symbol = Symbol {
            name: name.to_string(),
            scope: SymbolScope::Global,
            index: self.amount_definitons as u16,
        };
        self.store.insert(name.to_string(), symbol.clone());
        self.amount_definitons += 1;
        symbol
    }

    pub fn resolve(&mut self, name: &str) -> Result<&Symbol, CompilationError> {
        self.store
            .get(name)
            .ok_or_else(|| CompilationError::UnknownSymbol(name.to_string()))
    }
}
