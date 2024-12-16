use ff::Field;
use std::fmt::Debug;

pub(crate) mod prover;
pub(crate) mod verifier;

use crate::plonk::circuit::LookupArgumentBack as Argument;

/// Degree of lookup without inputs
pub fn base_degree(table_degree: usize) -> usize {
    // let lhs_degree = table_degree + inputs_expressions_degree + 1
    // let degree = lhs_degree + 1
    std::cmp::max(3, table_degree + 2)
}

pub fn degree_with_input(base_degree: usize, input_expression_degree: usize) -> usize {
    base_degree + input_expression_degree
}
