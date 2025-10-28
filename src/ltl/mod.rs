use super::automata::Q;

#[derive(Debug, Clone, Copy)]
pub enum Operator {
    Atom(Q),
    Neg(u32),
    X(u32),
    U(u32, u32),
    R(u32, u32),
    And(u32, u32),
    Or(u32, u32),
}

use Operator::*;
#[derive(Default)]
pub struct Formulas(Vec<Operator>);
pub struct Formula<'a>(pub &'a Formulas, pub u32);

impl<'a> From<Formula<'a>> for u32 {
    fn from(value: Formula<'a>) -> Self {
        value.1
    }
}

impl Formulas {
    pub fn constant(&mut self, val: bool) -> u32 {
        let idx = self.atom(1);
        let idx2 = self.neg(idx);
        if val {
            self.or(idx, idx2)
        } else {
            self.and(idx, idx2)
        }
    }
    pub fn atom(&mut self, id: Q) -> u32 {
        assert!(id > 0);
        self.0.push(Atom(id));
        self.0.len() as u32 - 1
    }
    pub fn neg(&mut self, index: u32) -> u32 {
        assert!((index as usize) < self.0.len());
        self.0.push(Neg(index));
        self.0.len() as u32 - 1
    }
    pub fn next(&mut self, index: u32) -> u32 {
        assert!((index as usize) < self.0.len());
        self.0.push(X(index));
        self.0.len() as u32 - 1
    }
    pub fn until(&mut self, index_hold: u32, index_until: u32) -> u32 {
        assert!((index_hold as usize) < self.0.len());
        assert!((index_until as usize) < self.0.len());
        self.0.push(U(index_hold, index_until));
        self.0.len() as u32 - 1
    }
    pub fn globally(&mut self, index_holds: u32) -> u32 {
        let f = self.constant(false);
        self.release(f, index_holds)
    }
    pub fn finally(&mut self, index_until: u32) -> u32 {
        let t = self.constant(true);
        self.until(t, index_until)
    }
    pub fn release(&mut self, index_release: u32, index_holds: u32) -> u32 {
        assert!((index_release as usize) < self.0.len());
        assert!((index_holds as usize) < self.0.len());
        self.0.push(R(index_release, index_holds));
        self.0.len() as u32 - 1
    }
    pub fn and(&mut self, x: u32, y: u32) -> u32 {
        assert!((x as usize) < self.0.len());
        assert!((y as usize) < self.0.len());
        self.0.push(And(x, y));
        self.0.len() as u32 - 1
    }
    pub fn or(&mut self, x: u32, y: u32) -> u32 {
        assert!((x as usize) < self.0.len());
        assert!((y as usize) < self.0.len());
        self.0.push(Or(x, y));
        self.0.len() as u32 - 1
    }
    pub fn access<'a>(&'a self, index: u32) -> Formula<'a> {
        assert!((index as usize) < self.0.len());
        Formula(self, index)
    }
    fn normalize_negated(&mut self, index: u32) -> u32 {
        assert!((index as usize) < self.0.len());
        match self.0[index as usize] {
            Atom(_) => {
                self.0.push(Neg(index));
                self.0.len() as u32 - 1
            }
            Neg(j) => j,
            X(j) => {
                let idx = self.normalize_negated(j);
                self.0.push(X(idx));
                self.0.len() as u32 - 1
            }
            U(i, j) => {
                let idx = self.normalize_negated(i);
                let idx2 = self.normalize_negated(j);
                self.0.push(R(idx, idx2));
                self.0.len() as u32 - 1
            }
            R(i, j) => {
                let idx = self.normalize_negated(i);
                let idx2 = self.normalize_negated(j);
                self.0.push(U(idx, idx2));
                self.0.len() as u32 - 1
            }
            And(i, j) => {
                let idx = self.normalize_negated(i);
                let idx2 = self.normalize_negated(j);
                self.0.push(Or(idx, idx2));
                self.0.len() as u32 - 1
            }
            Or(i, j) => {
                let idx = self.normalize_negated(i);
                let idx2 = self.normalize_negated(j);
                self.0.push(And(idx, idx2));
                self.0.len() as u32 - 1
            }
        }
    }
    pub fn normalize(&mut self, index: u32) -> u32 {
        assert!((index as usize) < self.0.len());
        match self.0[index as usize] {
            Atom(_) => index,
            Neg(j) => self.normalize_negated(j),
            X(i) => {
                let idx2 = self.normalize(i);
                self.0.push(X(idx2));
                self.0.len() as u32 - 1
            }
            U(i, j) => {
                let idx2 = self.normalize(i);
                let idx3 = self.normalize(j);
                self.0.push(U(idx2, idx3));
                self.0.len() as u32 - 1
            }
            R(i, j) => {
                let idx2 = self.normalize(i);
                let idx3 = self.normalize(j);
                self.0.push(R(idx2, idx3));
                self.0.len() as u32 - 1
            }
            And(i, j) => {
                let idx2 = self.normalize(i);
                let idx3 = self.normalize(j);
                self.0.push(And(idx2, idx3));
                self.0.len() as u32 - 1
            }
            Or(i, j) => {
                let idx2 = self.normalize(i);
                let idx3 = self.normalize(j);
                self.0.push(Or(idx2, idx3));
                self.0.len() as u32 - 1
            }
        }
    }
}

impl std::ops::Index<u32> for Formulas {
    type Output = Operator;

    fn index(&self, index: u32) -> &Self::Output {
        &self.0[index as usize]
    }
}

impl<'a> std::fmt::Display for Formula<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let v = &self.0.0;

        let op = v[self.1 as usize];

        match op {
            Atom(x) => write!(f, "{x}"),
            Neg(i) => {
                write!(f, "\u{00ac}")?;
                std::fmt::Display::fmt(&Formula(self.0, i), f)
            }
            X(i) => {
                write!(f, "X[")?;
                std::fmt::Display::fmt(&Formula(self.0, i), f)?;
                write!(f, "]")
            }
            U(i, j) => {
                write!(f, "(")?;
                std::fmt::Display::fmt(&Formula(self.0, i), f)?;
                write!(f, ")U(")?;
                std::fmt::Display::fmt(&Formula(self.0, j), f)?;
                write!(f, ")")
            }
            R(i, j) => {
                write!(f, "(")?;
                std::fmt::Display::fmt(&Formula(self.0, i), f)?;
                write!(f, ")R(")?;
                std::fmt::Display::fmt(&Formula(self.0, j), f)?;
                write!(f, ")")
            }
            And(x, y) => {
                write!(f, "(")?;
                std::fmt::Display::fmt(&Formula(self.0, x), f)?;
                write!(f, ")\u{22C0}(")?;
                std::fmt::Display::fmt(&Formula(self.0, y), f)?;
                write!(f, ")")
            }
            Or(x, y) => {
                write!(f, "(")?;
                std::fmt::Display::fmt(&Formula(self.0, x), f)?;
                write!(f, ")\u{22C1}(")?;
                std::fmt::Display::fmt(&Formula(self.0, y), f)?;
                write!(f, ")")
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::string::ToString;

    #[test]
    fn print_ltl() -> Result<(), impl std::error::Error> {
        let mut formulas = Formulas::default();
        let p1 = formulas.atom(1);
        let p2 = formulas.atom(2);
        let d = formulas.or(p1, p2);
        let c = formulas.and(p1, p2);
        let x = formulas.next(c);
        let result = formulas.until(d, x);
        let s = formulas.access(result).to_string();
        assert_eq!(s, "((1)⋁(2))U(X[(1)⋀(2)])");
        Ok::<_, std::fmt::Error>(())
    }

    #[test]
    fn normalize_ltl() {
        let mut formulas = Formulas::default();
        let p1 = formulas.atom(1);
        let p2 = formulas.atom(2);
        let d = formulas.or(p1, p2);
        let c = formulas.and(p1, p2);
        let x = formulas.next(c);
        let u = formulas.until(d, x);
        let result = formulas.neg(u);
        let len1 = formulas.0.len();
        let result2 = formulas.normalize(result);
        let len2 = formulas.0.len();
        let s = formulas.access(result).to_string();
        let s2 = formulas.access(result2).to_string();
        assert_eq!(s, "¬((1)⋁(2))U(X[(1)⋀(2)])");
        assert_eq!(s2, "((¬1)⋀(¬2))R(X[(¬1)⋁(¬2)])");
        assert!(len1 * 2 <= len2)
    }
}
