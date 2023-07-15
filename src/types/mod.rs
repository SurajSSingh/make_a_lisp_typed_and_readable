//! This module contains all the types used within the program.
//! There are two main sub modules: value and error.

use self::{error::Error, value::MaltarSpannedValue};

pub mod error;
pub mod value;

pub type MaltarResult<OkVal = MaltarSpannedValue, ErrVal = Error> = Result<OkVal, ErrVal>;
