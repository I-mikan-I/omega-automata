#![allow(clippy::upper_case_acronyms)]
use super::ltl;
use rand::random_range;
use std::collections::*;

pub type Q = u32;
pub type E = u32;

#[derive(Debug, Default, Clone)]
struct NBW {
    phi: HashMap<Q, Vec<(HashSet<E>, Q)>>,
    accepting: HashSet<Q>,
}

#[derive(Debug, Default, Clone)]
struct ABW {
    nodes: u32,
    // sets of symbols E encoded as S: E = { 2e | \forall e \in 2e : !e \not \in S }.
    // E.g. S = {1, -2} encodes E = { 2e | 1 \in 2e \wedge -2 \in 2e }
    phi: HashMap<Q, Vec<(HashSet<i64>, HashSet<Q>)>>,
    labels: Vec<String>,
    accepting: HashSet<Q>,
}
struct DotABW<'a>(&'a ABW);

impl DotABW<'_> {
    fn random_color() -> [u8; 3] {
        let hue: f32 = random_range(0.0..360.0);
        let lightness: f32 = random_range(0.2..=0.9);
        let [r, g, b, _] = color::OpaqueColor::<color::Oklch>::new([lightness, 0.2, hue])
            .to_rgba8()
            .to_u8_array();
        [r, g, b]
    }
}

impl<'a> std::fmt::Display for DotABW<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "digraph {{\n  rankdir=\"LR\";\n")?;
        let abw = self.0;
        for i in 0..abw.nodes {
            writeln!(
                f,
                r#"  {}[label="{}",shape="{}"];"#,
                i,
                abw.labels[i as usize],
                if abw.accepting.contains(&i) {
                    "doubleoctagon"
                } else {
                    "ellipse"
                }
            )?;
        }
        for (node, transitions) in &abw.phi {
            for (cond, succs) in transitions {
                if !succs.is_empty() {
                    let mut iter = succs.iter();
                    write!(f, "  {} -> {}", node, iter.next().unwrap())?;
                    for succ in iter {
                        write!(f, ",{}", succ)?;
                    }
                } else {
                    write!(f, "  {} -> true", node)?;
                }
                let mut condstring = String::new();
                for (idx, &atom) in cond.iter().enumerate() {
                    condstring.push_str(&format!(
                        "{}{}",
                        if idx > 0 { "\u{2227}" } else { "" },
                        if atom > 0 {
                            format!("{atom}")
                        } else {
                            format!("\u{00ac}{}", -atom)
                        }
                    ));
                }
                let colstr: String = Self::random_color()
                    .into_iter()
                    .map(|i| format!("{i:02x}"))
                    .collect();
                writeln!(f, " [label=\"{condstring}\",color=\"#{colstr}\"];",)?;
            }
        }
        writeln!(f, "}}")
    }
}

trait AsDot {
    type T: std::fmt::Display;
    fn as_dot(&self) -> Self::T;
}

impl<'a> AsDot for &'a ABW {
    type T = DotABW<'a>;

    fn as_dot(&self) -> Self::T {
        DotABW(self)
    }
}

fn ltl_to_abw_rec(f: ltl::Formula<'_>, node_map: &mut HashMap<u32, u32>, abw: &mut ABW) -> u32 {
    if let Some(&v) = node_map.get(&f.1) {
        return v;
    }
    let formulas = f.0;
    macro_rules! phi_and {
        ($phi1:expr, $phi2_iter:expr) => {
            $phi1
                .iter()
                .flat_map(|(es, qs)| {
                    $phi2_iter.filter_map(|(es2, qs2)| {
                        let mut es = es.clone();
                        let mut qs = qs.clone();
                        for v in es2 {
                            if es.contains(&-v) {
                                return None;
                            }
                            es.insert(*v);
                        }
                        qs.extend(qs2);
                        Some((es, qs))
                    })
                })
                .collect::<Vec<_>>()
        };
    }
    macro_rules! phi_or {
        ($phi1:expr, $phi2:expr) => {
            $phi1
                .into_iter()
                .chain($phi2.into_iter())
                .collect::<Vec<_>>()
        };
    }
    match formulas[f.1] {
        ltl::Operator::Atom(p) => {
            // duplicating atoms atm
            abw.phi
                .insert(abw.nodes, vec![(HashSet::from([p as i64]), HashSet::new())]);
        }
        ltl::Operator::Neg(p) => {
            // duplicating atoms atm
            if let ltl::Operator::Atom(atom) = formulas[p] {
                abw.phi.insert(
                    abw.nodes,
                    vec![(HashSet::from([-(atom as i64)]), HashSet::new())],
                );
            } else {
                panic!()
            }
        }
        ltl::Operator::X(i) => {
            let node = ltl_to_abw_rec(formulas.access(i), node_map, abw);
            abw.phi
                .insert(abw.nodes, vec![(HashSet::new(), HashSet::from([node]))]);
        }
        ltl::Operator::U(i, j) => {
            let node1 = ltl_to_abw_rec(formulas.access(i), node_map, abw);
            let node2 = ltl_to_abw_rec(formulas.access(j), node_map, abw);

            let cont = abw.phi[&node1]
                .iter()
                .cloned()
                .map(|(es, mut qs)| {
                    qs.insert(abw.nodes);
                    (es, qs)
                })
                .collect::<Vec<_>>();
            abw.phi
                .insert(abw.nodes, phi_or!(abw.phi[&node2].clone(), cont));
        }
        ltl::Operator::R(i, j) => {
            let node1 = ltl_to_abw_rec(formulas.access(i), node_map, abw);
            let node2 = ltl_to_abw_rec(formulas.access(j), node_map, abw);
            let new_edge = [(HashSet::new(), HashSet::from([abw.nodes]))];
            let cont = abw.phi[&node1].iter().chain(new_edge.iter());
            abw.phi
                .insert(abw.nodes, phi_and!(abw.phi[&node2].clone(), cont.clone()));
            abw.accepting.insert(abw.nodes);
        }
        ltl::Operator::And(i, j) => {
            let node1 = ltl_to_abw_rec(formulas.access(i), node_map, abw);
            let node2 = ltl_to_abw_rec(formulas.access(j), node_map, abw);

            let phi_new = phi_and!(abw.phi[&node1], abw.phi[&node2].iter());
            abw.phi.insert(abw.nodes, phi_new);
        }
        ltl::Operator::Or(i, j) => {
            let node1 = ltl_to_abw_rec(formulas.access(i), node_map, abw);
            let node2 = ltl_to_abw_rec(formulas.access(j), node_map, abw);
            let phi_new = phi_or!(abw.phi[&node1].clone(), abw.phi[&node2].clone());
            abw.phi.insert(abw.nodes, phi_new);
        }
    }
    assert!(abw.labels.len() == abw.nodes as usize);
    abw.labels.push(f.to_string());
    abw.nodes += 1;
    abw.nodes - 1
}

/**
 * Must be normaliled.
 */
fn ltl_to_abw(f: ltl::Formula<'_>) -> ABW {
    let mut node_map = HashMap::new();
    let mut abw = ABW::default();
    let _ = ltl_to_abw_rec(f, &mut node_map, &mut abw);
    abw
}

struct GBW {
    phi: HashMap<Q, Vec<(HashSet<E>, HashSet<Q>)>>,
    accepting: Vec<(Q, HashSet<E>, Q)>,
}

#[cfg(test)]
mod tests {
    use super::AsDot;
    use super::*;
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
}
