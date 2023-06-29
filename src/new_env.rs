use std::{
    cell::RefCell,
    rc::Rc,
    sync::{Arc, Mutex},
};

use im::HashMap;
use string_interner::{
    symbol::SymbolUsize, DefaultBackend, DefaultHashBuilder, StringInterner, Symbol,
};

use crate::types::{DataType, DataValue, DataValueResult, ErrorType};

use super::{new_eval_error, ReplError};

// Adapted from https://github.com/kanaka/mal/blob/master/impls/rust/env.rs

type EnvStringInterner = StringInterner<DefaultBackend<SymbolUsize>, DefaultHashBuilder>;

#[derive(Debug, Clone)]
pub struct EnvStruct {
    outer: Option<Env>,
    data: HashMap<SymbolUsize, DataValue>,
}

#[derive(Debug, Clone)]
pub struct Env(Arc<Mutex<EnvStruct>>);

impl Env {
    pub fn new(outer: Option<Env>) -> Self {
        Env(Arc::new(Mutex::new(EnvStruct {
            outer,
            data: HashMap::default(),
        })))
    }

    pub fn with_bindings(
        outer: Option<Env>,
        binds: &[SymbolUsize],
        more: Option<&SymbolUsize>,
        exprs: &[DataValue],
    ) -> Result<Env, ErrorType> {
        let mut env = Env::new(outer);

        let e = exprs.iter();

        for (idx, sym) in binds.iter().enumerate() {
            match exprs.get(idx) {
                Some(e) => env.set(sym, e.clone())?,
                None => {
                    // return new_eval_error(String::from("Not enough arguments to bind to"));
                    unimplemented!()
                }
            };
        }
        if let Some(sym) = more {
            let value = exprs
                .get(binds.len()..)
                .map_or(DataType::default(), |args| DataType::List(args.into()));
            env.set(
                sym,
                crate::types::DataValue {
                    value,
                    meta: HashMap::new(),
                },
            )?;
        }
        Ok(env)
    }

    pub fn outer(&self) -> Option<Env> {
        self.0.try_lock().map(|x| x.outer.clone()).ok().flatten()
    }

    pub fn find(&self, key: &SymbolUsize) -> Option<Env> {
        let (data, outer) = self
            .0
            .try_lock()
            .map(|e| (e.data.clone(), e.outer.clone()))
            .unwrap();
        match (data.contains_key(&key), outer) {
            (true, _) => Some(self.clone()),
            (false, Some(outer)) => outer.find(key),
            _ => None,
        }
    }
    pub fn get(&self, key: &SymbolUsize) -> DataValueResult {
        let Some(env) = self.find(key) else {
            // FIXME: Key should possibly resolve to string
            // new_eval_error(format!("'{:?}' not found", key));
            unimplemented!()
        };
        let res = match env
            .0
            .try_lock()
            .map_err(|_e| ErrorType::Unknown)
            .map(|e| e.data.get(key).cloned())
        {
            Ok(Some(v)) => Ok(v),
            Ok(None) => Err(ErrorType::Unknown),
            Err(e) => Err(e),
        };
        // .ok_or(ReplError::Eval(format!("'{}' not found", key)))?;
        res
    }

    /// Set a key in the environment to a value.
    pub fn set(&self, key: &SymbolUsize, val: DataValue) -> DataValueResult {
        self.0
            .try_lock()
            // FIXME: Handle case when lock cannot be acquired
            .map(|mut e| {
                e.data.insert(*key, val.clone());
                val
            })
            .map_err(|_e| ErrorType::Unknown)
        // ;
        // .map(|mut map| map.insert(key, val.clone()))
        // .map_err(|_| ReplError::Eval("Could not access environment".to_string()))?;
        // Ok(val)
    }
}
