/*
Two states can be merged if: both are rejecting (or not) and their outgoing transitions are the same.


*/

use super::AsDot;
use super::util::*;
use crate::ltl;
use std::hash::BuildHasher;
use std::{
    cmp,
    collections::{BTreeSet, HashMap, HashSet},
};

pub type ABWPhi = (BTreeSet<i64>, BTreeSet<Q>);
#[derive(Debug, Default, Clone)]
pub struct ABW {
    nodes: u32,
    initial: Q,
    // sets of symbols E encoded as S: E = { 2e | \forall e \in 2e : !e \not \in S }.
    // E.g. S = {1, -2} encodes E = { 2e | 1 \in 2e \wedge -2 \in 2e }
    phi: HashMap<Q, Vec<ABWPhi>>,
    labels: Vec<String>,
    // co-buechi
    rejecting: HashSet<Q>,

    // maps phi hashes -> nodes
    nodes_unique_cache: HashMap<u64, Q>,
}

impl ABW {
    pub fn get_label(&self, key: Q) -> &str {
        &self.labels[key as usize]
    }
    pub fn get_transition(&self, node: &Q) -> &[ABWPhi] {
        &self.phi[node]
    }
    pub fn get_rejecting(&self) -> impl std::iter::Iterator<Item = &Q> {
        self.rejecting.iter()
    }
    pub fn get_initial(&self) -> Q {
        self.initial
    }

    /*
    Potential improvements: Insertion sort sorting for modified sets.
    phi has to use SELF instead of new_node_id. Will be updated to new_node_id if result is None.
     */
    fn cache_new_node(
        &mut self,
        phi: &mut Vec<ABWPhi>,
        label: &str,
        rejecting: bool,
        new_node_id: Q,
    ) -> Option<Q> {
        let hash = self.nodes_unique_cache.hasher().hash_one(&(*phi));
        // marker used for self loops
        if let Some(q) = self.nodes_unique_cache.get(&hash) {
            // update phi
            for (_, nodes) in phi.iter_mut() {
                assert!(!nodes.contains(q));
                if nodes.contains(&SELF) {
                    nodes.remove(&SELF);
                    nodes.insert(*q);
                }
            }
            // new transition implications impossible: if another transition to q existed, then the hash could not have been equal (hashes only use SELF for loops)
            phi.sort();
            if &self.phi[q] == phi && (rejecting == self.rejecting.contains(q)) {
                self.labels[*q as usize].push_str(&format!("\\n{}", label));
                return Some(*q);
            } else {
                // undo modifications
                phi.iter_mut().for_each(|(_, nodes)| {
                    assert!(!nodes.contains(&new_node_id));
                    assert!(!nodes.contains(&SELF));
                    if nodes.contains(q) {
                        nodes.remove(q);
                        nodes.insert(new_node_id);
                    }
                });
            }
        } else {
            self.nodes_unique_cache.insert(hash, new_node_id);
            phi.iter_mut().for_each(|(_, nodes)| {
                assert!(!nodes.contains(&new_node_id));
                if nodes.contains(&SELF) {
                    nodes.remove(&SELF);
                    nodes.insert(new_node_id);
                }
            });
        }
        phi.sort();
        None
    }
}
pub struct DotABW<'a>(&'a ABW);

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
                if abw.rejecting.contains(&i) {
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
                let colstr: String = random_color();
                writeln!(f, " [label=\"{condstring}\",color=\"{colstr}\"];",)?;
            }
        }
        writeln!(f, "}}")
    }
}

impl<'a> AsDot for &'a ABW {
    type T = DotABW<'a>;

    fn as_dot(&self) -> Self::T {
        DotABW(self)
    }
}

/**
 * trans1 < trans2 <=> trans1.0 \subseteq trans2.0 and trans1.1 \supseteq trans2.1 (trans1 implies trans2)
 */
pub fn transition_cmp(trans1: &ABWPhi, trans2: &ABWPhi) -> Option<cmp::Ordering> {
    let syms1 = &trans1.0;
    let syms2 = &trans2.0;

    let states1 = &trans1.1;
    let states2 = &trans2.1;

    fn syms_subset(syms1: &BTreeSet<i64>, syms2: &BTreeSet<i64>) -> bool {
        syms1.iter().all(|&i| !syms2.contains(&-i))
    }

    if states1.is_subset(states2) && syms_subset(syms2, syms1) {
        Some(cmp::Ordering::Greater)
    } else if states2.is_subset(states1) && syms_subset(syms1, syms2) {
        Some(cmp::Ordering::Less)
    } else {
        None
    }
}

use std::borrow::Borrow;

pub struct IdentityAccessor {}

impl<'this> AccessorLifetime<'this, &'this Self, ABWPhi> for IdentityAccessor {
    type Item = &'this ABWPhi;
}

impl Accessor<ABWPhi, ABWPhi> for IdentityAccessor {
    fn access<'a>(&self, k: &'a ABWPhi) -> <Self as AccessorLifetime<'a, &'a Self, ABWPhi>>::Item {
        k
    }
}

fn id(t: &ABWPhi) -> &ABWPhi {
    t
}
/**
 * Simplifies VWABW transitions and sorts them lexicographically.
 */
pub fn transitions_simpl_keyed<K, A: Accessor<K, ABWPhi>, F: Fn(&K) -> bool>(
    transitions: &mut Vec<K>,
    access: A,
    removable: F,
) {
    'outer: for i in 0..transitions.len() {
        let mut k = i + 1;
        while k < transitions.len() {
            let left = access.access(&transitions[i]);
            let right = access.access(&transitions[k]);
            let result = transition_cmp(left.borrow(), right.borrow());
            drop(left);
            drop(right);
            match result {
                Some(cmp::Ordering::Less) => {
                    if removable(&transitions[i]) {
                        transitions.remove(i);
                    }
                    continue 'outer;
                }
                Some(cmp::Ordering::Greater) => {
                    if removable(&transitions[k]) {
                        transitions.remove(k);
                    }
                    continue;
                }
                None => {}
                _ => panic!(),
            }
            k += 1;
        }
    }
    transitions.sort_by(|l, r| {
        let lv = access.access(l);
        let rv = access.access(r);
        lv.borrow().cmp(rv.borrow())
    });
}

fn transitions_simpl(transitions: &mut Vec<ABWPhi>) {
    let acc = IdentityAccessor {};
    transitions_simpl_keyed(transitions, acc, |_| true);
}

pub fn abwphi_and<
    Q: std::borrow::Borrow<ABWPhi>,
    I: std::iter::Iterator<Item = Q>,
    I2: std::iter::Iterator<Item = Q> + Clone,
>(
    phi1_iter: I,
    phi2_iter: I2,
) -> Vec<ABWPhi> {
    phi1_iter
        .flat_map(|q| {
            phi2_iter.clone().filter_map(move |q2| {
                let (es2, qs2) = q2.borrow();
                let (mut es, mut qs) = q.borrow().clone();
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
}

fn ltl_to_abw_rec(f: ltl::Formula<'_>, abw: &mut ABW) -> u32 {
    let formulas = f.0;

    macro_rules! phi_or {
        ($phi1:expr, $phi2:expr) => {
            $phi1
                .into_iter()
                .chain($phi2.into_iter())
                .collect::<Vec<_>>()
        };
    }
    let (mut new_phi, rejecting): (Vec<ABWPhi>, bool) = match formulas[f.1] {
        ltl::Operator::Atom(p) => {
            // duplicating atoms atm
            (vec![(BTreeSet::from([p as i64]), BTreeSet::new())], false)
        }
        ltl::Operator::Neg(p) => {
            // duplicating atoms atm
            if let ltl::Operator::Atom(atom) = formulas[p] {
                (
                    vec![(BTreeSet::from([-(atom as i64)]), BTreeSet::new())],
                    false,
                )
            } else {
                panic!()
            }
        }
        ltl::Operator::X(i) => {
            let node = ltl_to_abw_rec(formulas.access(i), abw);
            (vec![(BTreeSet::new(), BTreeSet::from([node]))], false)
        }
        ltl::Operator::U(i, j) => {
            let node1 = ltl_to_abw_rec(formulas.access(i), abw);
            let node2 = ltl_to_abw_rec(formulas.access(j), abw);

            let cont = abw.phi[&node1]
                .iter()
                .cloned()
                .map(|(es, mut qs)| {
                    qs.insert(SELF);
                    (es, qs)
                })
                .collect::<Vec<_>>();
            let mut phi_new = phi_or!(abw.phi[&node2].clone(), cont);
            transitions_simpl(&mut phi_new);
            (phi_new, true)
        }
        ltl::Operator::R(i, j) => {
            let node1 = ltl_to_abw_rec(formulas.access(i), abw);
            let node2 = ltl_to_abw_rec(formulas.access(j), abw);
            let new_edge = [(BTreeSet::new(), BTreeSet::from([SELF]))];
            let cont = abw.phi[&node1].iter().chain(new_edge.iter());
            let mut phi_new = abwphi_and(abw.phi[&node2].iter(), cont);
            transitions_simpl(&mut phi_new);
            (phi_new, false)
        }
        ltl::Operator::And(i, j) => {
            let node1 = ltl_to_abw_rec(formulas.access(i), abw);
            let node2 = ltl_to_abw_rec(formulas.access(j), abw);

            let mut phi_new = abwphi_and(abw.phi[&node1].iter(), abw.phi[&node2].iter());
            transitions_simpl(&mut phi_new);
            (phi_new, false)
        }
        ltl::Operator::Or(i, j) => {
            let node1 = ltl_to_abw_rec(formulas.access(i), abw);
            let node2 = ltl_to_abw_rec(formulas.access(j), abw);
            let mut phi_new = phi_or!(abw.phi[&node1].clone(), abw.phi[&node2].clone());
            transitions_simpl(&mut phi_new);
            (phi_new, false)
        }
    };
    if let Some(q) = abw.cache_new_node(&mut new_phi, f.to_string().as_str(), rejecting, abw.nodes)
    {
        return q;
    }
    abw.phi.insert(abw.nodes, new_phi);
    if rejecting {
        abw.rejecting.insert(abw.nodes);
    }
    assert!(abw.labels.len() == abw.nodes as usize);
    abw.labels.push(f.to_string());
    abw.nodes += 1;
    abw.nodes - 1
}

/**
 * Must be normalized.
 */
pub fn ltl_to_abw(f: ltl::Formula<'_>) -> ABW {
    let mut abw = ABW::default();
    let root = ltl_to_abw_rec(f, &mut abw);
    abw.initial = root;
    let mut on_stack: Vec<bool> = vec![false; abw.nodes as usize];
    let mut stack: Vec<Q> = vec![root];
    on_stack[root as usize] = true;
    let add_nodes = |q, stack: &mut Vec<Q>, on_stack: &mut Vec<bool>| {
        abw.phi[&q]
            .iter()
            .flat_map(|(_, succs)| succs.iter())
            .cloned()
            .filter(|&q| {
                if on_stack[q as usize] {
                    false
                } else {
                    on_stack[q as usize] = true;
                    true
                }
            })
            .for_each(|q| stack.push(q));
    };
    add_nodes(root, &mut stack, &mut on_stack);
    while let Some(q) = stack.pop() {
        add_nodes(q, &mut stack, &mut on_stack);
    }
    for q in 0..abw.nodes {
        if !on_stack[q as usize] {
            abw.phi.remove(&q);
            abw.labels[q as usize] = "".into();
            abw.rejecting.remove(&q);
        }
    }
    abw.nodes_unique_cache.clear();
    abw
}
