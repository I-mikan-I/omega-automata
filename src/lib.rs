//! # Omega Automata
//! 
//!This crate implements decision procedures and algorithms on
//!__omega-automata__. __Omega-automata__ are similar to the better-known finite
//!automata (NFA/DFA/...) except they operate on *infinite* words. They are
//!commonly used to model systems that can run for an infinite time, such as most
//!algorithms, protocols, and more.

//!For example, model checking temporal logic properties (commonly used in formal
//!hardware verification) can be implemented with an optimal worst-case time
//!complexity via omega automata.

//!## Features

//!Currently, this crate supports the following:

//!- LTL to VWABW (*very weak alternating Büchi automaton*) translation.
//!- VWABW to GBW (*generalized Büchi automaton*) translation.
//!- GBW to NBW (*non-deterministic Büchi automaton*) translation.
//!- NBW emptiness check.

//!### Checking LTL formula satsifiability

//!1. Construct an LTL formula
//!2. Convert it to a VWABW $\mathit{AM}$
//!3. Convert *AM* to a GBW *GM*
//!4. Convert *GM* to an NWB *NM*
//!5. Check the emptyness of *NM*: It is non-empty iff. the LTL formula is satisfiable.

//!## Examples

//! Let's start with the LTL formula `φ = (□◇x₁ ∧ ◇x₁) ∧ (◇(x₃ ∧ □x₂))`.
//! Intuitively, `φ` states that any sequence `w = s₁, s₂, s₃, … ∈ X^ω`
//! of variable assignments (the structure LTL is interpreted over) must
//! first have infinite `x₁ ∈ sᵢ` (also pronounced `w` *must have infinitely
//! often* `x₁`), and second it must eventually reach a position `sₖ` such that
//! `x₃, x₂ ∈ sₖ` and `x₂ ∈ sⱼ` for all `sⱼ` following `sₖ` (also
//! pronounced `x₂` must hold from `sₖ`).
//! 
//!```
//!use omega_automata::{ltl::*, automata::{*,abw::*,gbw::*,nbw::*}};
//!let mut formulas = Formulas::default();
//!let p = formulas.atom(1);
//!let r = formulas.atom(2);
//!let q = formulas.atom(3);
//!let Gr = formulas.globally(r);
//!let q_and_Gr = formulas.and(q, Gr);
//!let Fq_and_Gr = formulas.finally(q_and_Gr);
//!let Fp = formulas.finally(p);
//!let GFp = formulas.globally(Fp);
//!let intermediate = formulas.and(GFp, Fp);
//!let notp = formulas.neg(p);
//!let Fnotp = formulas.finally(notp);
//!let GFnotp = formulas.globally(Fnotp);
//!let res = formulas.and(intermediate, Fq_and_Gr);
//!let res = formulas.and(res, GFnotp);
//!let normalized = formulas.normalize(res);
//!let automata = ltl_to_abw(formulas.access(normalized));
//!let gbw = vwabw_to_gbw(&automata);
//!let nbw = gbw_to_nbw(&gbw);
//!let sat = is_nonempty(&nbw);
//!assert!(sat)
//! ```
#![allow(dead_code)]
#![cfg_attr(test, allow(non_snake_case))]
pub mod automata;
pub mod ltl;

#[cfg(test)]
mod tests {
    use crate::automata::{
        abw::ltl_to_abw,
        gbw::vwabw_to_gbw,
        nbw::{gbw_to_nbw, is_nonempty},
    };

    use super::*;
    #[test]
    fn example_test() {
        println!("It Works!")
    }

    #[test]
    fn test_sat2() {
        let mut formulas = ltl::Formulas::default();
        let p = formulas.atom(1);
        let r = formulas.atom(2);
        let q = formulas.atom(3);
        let Gr = formulas.globally(r);
        let q_and_Gr = formulas.and(q, Gr);
        let Fq_and_Gr = formulas.finally(q_and_Gr);
        let Fp = formulas.finally(p);
        let GFp = formulas.globally(Fp);
        let intermediate = formulas.and(GFp, Fp);
        let notp = formulas.neg(p);
        let Fnotp = formulas.finally(notp);
        let GFnotp = formulas.globally(Fnotp);
        let res = formulas.and(intermediate, Fq_and_Gr);
        let res = formulas.and(res, GFnotp);
        let normalized = formulas.normalize(res);
        let automata = ltl_to_abw(formulas.access(normalized));
        let gbw = vwabw_to_gbw(&automata);
        let nbw = gbw_to_nbw(&gbw);
        let sat = is_nonempty(&nbw);
        assert!(sat)
    }
}
