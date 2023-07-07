use std::{
    collections::HashMap,
    sync::{Arc, RwLock},
};

use string_interner::symbol::SymbolUsize;

use crate::types::{error::Error, MaltarResult};

#[derive(Debug, Clone)]
pub enum EnvData<Val>
where
    Val: Clone + Eq,
{
    Value(Val),
    Module(Env<Val>),
}

#[derive(Debug, Clone)]
pub struct EnvContext<Val>
where
    Val: Clone + Eq,
{
    /// The parent context (outer environment) - at most one
    outer: Option<Env<Val>>,
    /// A symbol table mapping symbols to either values or namespaces
    data: HashMap<SymbolUsize, EnvData<Val>>,
}
#[derive(Debug, Clone)]
pub struct Env<Val>(Arc<RwLock<EnvContext<Val>>>)
where
    Val: Clone + Eq;

impl<Val> Env<Val>
where
    Val: Clone + Eq,
{
    /// Find a symbol within the environment or its parent.
    /// If given a path, it will start at the root environment and evaluate by namespace
    pub fn find(&self, path: &[&SymbolUsize]) -> Option<Env<Val>> {
        todo!();
        //     match self.0.read() {
        //         Ok(ctx) => match path {
        //             [path @ .., key] => {
        //                 // If not namespace qualified...
        //                 if path.len() == 0 {
        //                     // ...try to find from current environment or one of its direct ancestors
        //                     if ctx.data.contains_key(key) {
        //                         Some(self.clone())
        //                     } else if let Some(outer) = &ctx.outer {
        //                         outer.find(path)
        //                     } else {
        //                         None
        //                     }
        //                 } else {
        //                     // ... otherwise, go to the root environment and traverse down the namespace and look there
        //                     let mut root_env = ctx.outer;
        //                     while let Some(outer) = root_env {
        //                         match outer.0.read(){
        //                             Ok(outer_ctx) => root_env = outer_ctx.outer,
        //                             Err(_) => todo!("Poisoned outer"),
        //                         }
        //                     }

        //                     let mut self = ctx;
        //                     for name in path {
        //                         if let Some(sub_ctx) = ns_ctx.namespaces.get(name) {
        //                             ns_ctx = sub_ctx.clone();
        //                         } else {
        //                             return None;
        //                         }
        //                     }
        //                     if ns_ctx.data.contains_key(&key) {
        //                         return Some(ns_ctx);
        //                     } else {
        //                         None
        //                     }
        //                 }
        //             }
        //             [] => todo!("Return error for empty path"),
        //         },
        //         Err(_err) => todo!("Poison error for find"),
        //     }
    }

    pub fn get(&self, path: &[&SymbolUsize]) -> MaltarResult<Val> {
        todo!();
        // if let Some(&key) = path.last() {
        //     self.find(path)
        //         .ok_or(Error::Custom("key not found".to_string()))
        //         .and_then(|env| match env.0.read() {
        //             Ok(ctx) => match ctx.data.get(key) {
        //                 Some(val) => Ok(val.clone()),
        //                 None => Err(Error::Custom("Key not found".to_string())),
        //             },
        //             Err(_err) => todo!("Poison error for get"),
        //         })
        // } else {
        //     todo!("Throw empty path error")
        // }
    }

    pub fn set(&self, key: &SymbolUsize, val: Val) -> MaltarResult<Val> {
        todo!();
        // match self.0.write() {
        //     Ok(mut ctx) => {
        //         ctx.data.insert(*key, val.clone());
        //         Ok(val)
        //     }
        //     Err(_err) => todo!("Poison error for get"),
        // }
    }

    // pub fn resolve<B, H>(
    //     &self,
    //     path: &[&SymbolUsize],
    //     intern: StringInterner<B, H>,
    // ) -> MaltarResult<String>
    // where
    //     B: string_interner::backend::Backend<Symbol = SymbolUsize>,
    //     H: std::hash::BuildHasher,
    // {
    //     self.find(path)
    //         .and_then(|ctx| {
    //             path.last()
    //                 .map(|key| intern.resolve(**key).map(|name| name.to_owned()))
    //         })
    //         .flatten()
    //         .ok_or(Error::Custom("key not found".to_string()))
    // }
}
