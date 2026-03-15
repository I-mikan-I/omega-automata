#![allow(clippy::upper_case_acronyms)]
mod abw;
mod gbw;
mod nbw;
mod util;

use std::collections::*;
pub use util::Q;
use util::*;

#[derive(Debug, Default, Clone)]
struct NBW {
    phi: HashMap<Q, Vec<(HashSet<E>, Q)>>,
    accepting: HashSet<Q>,
}

trait AsDot {
    type T: std::fmt::Display;
    fn as_dot(&self) -> Self::T;
}

#[cfg(test)]
mod tests {

    use super::AsDot;
    use super::abw::ltl_to_abw;
    use crate::automata::gbw::vwabw_to_gbw;
    use crate::automata::nbw::{gbw_to_nbw, is_nonempty};
    use crate::ltl;
    #[test]
    fn example_test() {
        println!("It Works!")
    }

    #[test]
    fn test_simple1() {
        let mut formulas = ltl::Formulas::default();
        let p = formulas.atom(1);
        let t = formulas.constant(true);
        let f = formulas.constant(false);
        let Fp = formulas.until(t, p);
        let GFp = formulas.release(f, Fp);
        let automata = ltl_to_abw(formulas.access(GFp));
        let dot = (&automata).as_dot().to_string();
        std::println!("{dot}");
    }
    #[test]
    // (GF1 /\ F1) /\ (F(3 /\ G2))
    fn test_simple2() {
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
        let res = formulas.and(intermediate, Fq_and_Gr);
        let normalized = formulas.normalize(res);
        let automata = ltl_to_abw(formulas.access(normalized));
        let dot = (&automata).as_dot().to_string();
        std::println!("{dot}");
    }

    // TODO: node merging not working correctly
    #[test]
    fn test_simple3() {
        let mut formulas = ltl::Formulas::default();
        let t = formulas.constant(true);
        let f = formulas.constant(false);
        let p = formulas.atom(1);
        let q = formulas.atom(2);
        let u1 = formulas.until(t, p);
        let u2 = formulas.until(t, u1);
        let u1u2 = formulas.and(u1, u2);
        let r = formulas.release(f, u2);
        let normalized = formulas.normalize(u2);
        let automata = ltl_to_abw(formulas.access(normalized));
        std::println!("{}", (&automata).as_dot())
    }

    #[test]
    fn test_gbw1() {
        let mut formulas = ltl::Formulas::default();
        let p = formulas.atom(1);
        let t = formulas.constant(true);
        let f = formulas.constant(false);
        let Fp = formulas.until(t, p);
        let GFp = formulas.release(f, Fp);
        let automata = ltl_to_abw(formulas.access(GFp));
        let gbw = vwabw_to_gbw(&automata);
        let dot = (&gbw).as_dot().to_string();
        std::println!("{dot}");
    }

    #[test]
    fn test_gbw2() {
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
        let res = formulas.and(intermediate, Fq_and_Gr);
        let normalized = formulas.normalize(res);
        let automata = ltl_to_abw(formulas.access(normalized));
        let gbw = vwabw_to_gbw(&automata);
        std::println!("{}", (&gbw).as_dot())
    }

    #[test]
    fn test_gbw3() {
        let mut formulas = ltl::Formulas::default();
        let t = formulas.constant(true);
        let f = formulas.constant(false);
        let p = formulas.atom(1);
        let u1 = formulas.until(t, p);
        let u2 = formulas.until(t, u1);
        let r = formulas.release(f, u2);
        let normalized = formulas.normalize(r);
        let automata = ltl_to_abw(formulas.access(normalized));
        let gbw = vwabw_to_gbw(&automata);
        std::println!("{}", (&gbw).as_dot())
    }

    #[test]
    fn test_nbw2() {
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
        let res = formulas.and(intermediate, Fq_and_Gr);
        let normalized = formulas.normalize(res);
        let automata = ltl_to_abw(formulas.access(normalized));
        let gbw = vwabw_to_gbw(&automata);
        let nbw = gbw_to_nbw(&gbw);
        std::println!("{}", (&nbw).as_dot())
    }

    #[test]
    fn test_sat1() {
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
        let res = formulas.and(intermediate, Fq_and_Gr);
        let normalized = formulas.normalize(res);
        let automata = ltl_to_abw(formulas.access(normalized));
        let gbw = vwabw_to_gbw(&automata);
        let nbw = gbw_to_nbw(&gbw);
        let sat = is_nonempty(&nbw);
        assert!(sat)
    }

    #[test]
    fn test_unsat1() {
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
        let notr = formulas.neg(r);
        let Fnotr = formulas.finally(notr);
        let GFnotr = formulas.globally(Fnotr);
        let res = formulas.and(intermediate, Fq_and_Gr);
        let res = formulas.and(res, GFnotr);
        let normalized = formulas.normalize(res);
        let automata = ltl_to_abw(formulas.access(normalized));
        let gbw = vwabw_to_gbw(&automata);
        let nbw = gbw_to_nbw(&gbw);
        let sat = is_nonempty(&nbw);
        assert!(!sat)
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
    #[test]
    fn test_unsat2() {
        let mut formulas = ltl::Formulas::default();
        let res = formulas.constant(false);
        let normalized = formulas.normalize(res);
        let automata = ltl_to_abw(formulas.access(normalized));
        let gbw = vwabw_to_gbw(&automata);
        let nbw = gbw_to_nbw(&gbw);
        let sat = is_nonempty(&nbw);
        assert!(!sat)
    }
}
