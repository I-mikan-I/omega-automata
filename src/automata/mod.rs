#![allow(clippy::upper_case_acronyms)]
use super::ltl;
use std::{collections::*};

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
    phi: HashMap<Q, Vec<(HashSet<i64>, HashSet<Q>)>>,
    labels: Vec<String>,
    accepting: HashSet<Q>,
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
            abw.phi.insert(
                abw.nodes,
                vec![(HashSet::from([-(p as i64)]), HashSet::new())],
            );
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
    #[test]
    fn example_test() {
        println!("It Works!")
    }
}
