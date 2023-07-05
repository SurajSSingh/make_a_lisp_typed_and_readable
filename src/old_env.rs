use std::{cell::RefCell, collections::HashMap, rc::Rc};

use super::{old_reader::MalType, old_repl::new_eval_error, old_repl::ReplError};

// Adapted from https://github.com/kanaka/mal/blob/master/impls/rust/env.rs

#[derive(Debug, Clone, PartialEq, Default)]
pub struct EnvStruct {
    outer: Option<Env>,
    data: RefCell<HashMap<String, MalType>>,
}

#[derive(Debug, Clone, PartialEq, Default)]
pub struct Env(Rc<EnvStruct>);

impl Env {
    pub fn new(outer: Option<Env>) -> Self {
        Env(Rc::new(EnvStruct {
            data: RefCell::new(HashMap::default()),
            outer,
        }))
    }
    pub fn with_bindings(
        outer: Option<Env>,
        binds: &[String],
        exprs: &[MalType],
    ) -> Result<Env, ReplError> {
        let mut env = Env::new(outer);

        let mut variadic_start = None;
        for (i, b) in binds.iter().enumerate() {
            if b == "&" {
                variadic_start = Some(i + 1);
                break;
            }
            match exprs.get(i) {
                Some(e) => env.set(&MalType::Symbol(b.to_string()), e.clone())?,
                None => {
                    return new_eval_error(String::from("Not enough arguments to bind to"));
                }
            };
        }
        if let Some(start) = variadic_start {
            let Some(key) = binds.get(start).map(|s|MalType::Symbol(s.to_string())) else {
                return new_eval_error(String::from(
                    "No name found for variadic arguments; there must be a name after the '&' symbol",
                ));
            };
            let val = exprs.get((start - 1)..).map_or(MalType::Nil(()), |args| {
                MalType::List(args.to_vec(), Box::new(MalType::Nil(())))
            });
            env.set(&key, val)?;
        }
        Ok(env)
    }

    pub fn outer(&self) -> Option<Env> {
        self.0.outer.clone()
    }

    pub fn find(&self, key: &str) -> Option<Env> {
        match (self.0.data.borrow().contains_key(key), self.0.outer.clone()) {
            (true, _) => Some(self.clone()),
            (false, Some(outer)) => outer.find(key),
            _ => None,
        }
    }
    pub fn get(&self, key: &MalType) -> Result<MalType, ReplError> {
        let MalType::Symbol(sym) = key else {
            return new_eval_error(format!("The key is not a symbol: got {}", key));
        };
        let Some(env) = self.find(sym) else {
            return new_eval_error(format!("'{}' not found", sym));
        };
        let val = env
            .0
            .data
            .borrow()
            .get(sym)
            .cloned()
            .ok_or(ReplError::Eval(format!("'{}' not found", sym)))?;
        Ok(val)
    }

    /// Set a key in the environment to a value.
    pub fn set(&mut self, key: &MalType, val: MalType) -> Result<MalType, ReplError> {
        let MalType::Symbol(sym) = key else {
            return new_eval_error(format!("The key is not a symbol: got {}", key));
        };
        self.0
            .data
            .try_borrow_mut()
            .map(|mut map| map.insert(sym.clone(), val.clone()))
            .map_err(|_| ReplError::Eval("Could not access environment".to_string()))?;
        Ok(val)
    }
}
