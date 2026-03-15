use std::{
    cmp,
    collections::{BTreeSet, HashMap, HashSet},
    fmt::Display,
    hash::BuildHasher,
};

use crate::automata::{
    AsDot, Q,
    gbw::GBW,
    util::{Implication, SELF, Transition, syms_subset, transitions_simpl},
};

type NBWPhi = (BTreeSet<i64>, Q);

impl Transition for NBWPhi {
    fn implies(&self, other: &Self) -> super::util::Implication {
        if self.1 != other.1 {
            Implication::None
        } else {
            if syms_subset(&self.0, &other.0) {
                Implication::Implied
            } else if syms_subset(&other.0, &self.0) {
                Implication::Implies
            } else {
                Implication::None
            }
        }
    }
}

pub struct NBW {
    nodes: Q,
    initial: Q,
    phi: HashMap<Q, Vec<NBWPhi>>,
    labels: Vec<String>,
    accepting: HashSet<Q>,
    nodes_unique_cache: HashMap<u64, Q>,
}

impl NBW {
    fn new() -> Self {
        Self {
            nodes: 0,
            initial: 0,
            phi: Default::default(),
            labels: Default::default(),
            accepting: Default::default(),
            nodes_unique_cache: Default::default(),
        }
    }
    fn cache_new_node(&mut self, phi: &mut Vec<NBWPhi>, label: &str, new_node_id: Q) -> Option<Q> {
        let hash = self.nodes_unique_cache.hasher().hash_one(&(*phi));
        if let Some(q) = self.nodes_unique_cache.get(&hash) {
            // update phi
            for (_, node) in phi.iter_mut() {
                assert!(node != q);
                if node == &SELF {
                    *node = *q;
                }
            }
            // new transition implications impossible: if another transition to q existed, then the hash could not have been equal (hashes only use SELF for loops)
            phi.sort();
            if &self.phi[q] == phi {
                self.labels[*q as usize].push_str(&format!("\\n{}", label));
                return Some(*q);
            } else {
                // undo modifications
                phi.iter_mut().for_each(|(_, node)| {
                    assert!(node != &new_node_id);
                    assert!(node != &SELF);
                    if node == q {
                        *node = new_node_id;
                    }
                });
            }
        } else {
            self.nodes_unique_cache.insert(hash, new_node_id);
            phi.iter_mut().for_each(|(_, node)| {
                assert!(node != &new_node_id);
                if node == &SELF {
                    *node = new_node_id;
                }
            });
        }
        phi.sort();
        None
    }
}

pub struct DotNBW<'a>(&'a NBW);

impl<'a> Display for DotNBW<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "digraph {{\n  rankdir=\"LR\";\n")?;
        let nbw = self.0;
        for i in 0..nbw.nodes {
            writeln!(
                f,
                r#"  {}[label="{}",shape="{}"];"#,
                i,
                nbw.labels[i as usize],
                if nbw.accepting.contains(&i) {
                    "doubleoctagon"
                } else {
                    "ellipse"
                }
            )?;
        }
        for (node, transitions) in &nbw.phi {
            for (cond, succ) in transitions {
                write!(f, "  {} -> {}", node, succ)?;
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
                writeln!(f, " [label=\"{condstring}\"];",)?;
            }
        }
        writeln!(f, "}}")
    }
}

impl<'a> AsDot for &'a NBW {
    type T = DotNBW<'a>;

    fn as_dot(&self) -> Self::T {
        DotNBW(self)
    }
}

fn transition_cmp(trans1: &NBWPhi, trans2: &NBWPhi) -> Option<cmp::Ordering> {
    let syms1 = &trans1.0;
    let syms2 = &trans2.0;
    fn syms_subset(syms1: &BTreeSet<i64>, syms2: &BTreeSet<i64>) -> bool {
        syms1.iter().all(|&i| !syms2.contains(&-i))
    }

    if syms_subset(syms2, syms1) {
        Some(cmp::Ordering::Greater)
    } else if syms_subset(syms1, syms2) {
        Some(cmp::Ordering::Less)
    } else {
        None
    }
}

fn gbw_to_nbw_rec(
    gbw: &GBW,
    out: &mut NBW,
    state: Q,
    a_set: u32,
    unique_cache: &mut HashMap<(Q, u32), Q>,
) -> Q {
    if let Some(q) = unique_cache.get(&(state, a_set)) {
        return *q;
    }
    let new_state = out.nodes;
    out.nodes += 1;
    unique_cache.insert((state, a_set), new_state);

    let accepting_count = gbw.num_accepting() as u32;
    let new_label = format!("{}\n{}", gbw.label(state), a_set);
    assert!(out.labels.len() == new_state as usize);
    out.labels.push(new_label);
    let mut new_transitions = gbw
        .transitions(state)
        .iter()
        .enumerate()
        .map(|(t_idx, (syms, node))| {
            let start_set = if a_set == accepting_count { 0 } else { a_set };
            let next_set = (start_set..accepting_count)
                .find(|set_idx| {
                    gbw.get_accepting_set(*set_idx as usize)
                        .unwrap()
                        .iter()
                        // first set to not include the transition
                        .all(|&(q, edge_index)| q != state || edge_index != t_idx)
                })
                .unwrap_or(accepting_count);
            (
                syms.clone(),
                gbw_to_nbw_rec(gbw, out, *node, next_set, unique_cache),
            )
        })
        .collect::<Vec<_>>();
    transitions_simpl(&mut new_transitions);
    for (_, target) in new_transitions.iter_mut() {
        assert!(*target != SELF);
        if *target == new_state {
            *target = SELF;
        }
    }
    new_transitions.sort();
    if let Some(q) = out.cache_new_node(
        &mut new_transitions,
        &out.labels[new_state as usize].clone(),
        new_state,
    ) {
        return q;
    }
    out.phi.insert(new_state, new_transitions);
    if a_set == accepting_count {
        out.accepting.insert(new_state);
    }
    assert!(out.nodes as usize == out.labels.len());

    new_state
}

pub fn gbw_to_nbw(gbw: &GBW) -> NBW {
    let mut nbw = NBW::new();
    gbw_to_nbw_rec(gbw, &mut nbw, gbw.initial, 0, &mut HashMap::new());
    nbw
}

fn nbw_reachability(nbw: &NBW) -> Vec<Vec<Q>> {
    let mut reachable = vec![HashSet::new(); nbw.nodes as usize];

    for _ in 0..nbw.nodes {
        for node in 0..nbw.nodes {
            if !nbw.phi.contains_key(&node) {
                continue;
            }
            let successors = nbw.phi[&node].iter().map(|(_, node)| node);

            for succ in successors {
                reachable[node as usize].insert(*succ);
                let mut old_set = HashSet::new();
                std::mem::swap(&mut old_set, &mut reachable[node as usize]);
                old_set.extend(reachable[*succ as usize].iter());
                reachable[node as usize] = old_set;
            }
        }
    }

    reachable
        .into_iter()
        .map(|set| set.into_iter().collect())
        .collect()
}

pub fn is_nonempty(nbw: &NBW) -> bool {
    let reachability = nbw_reachability(nbw);
    let init = nbw.initial;
    for accepting in &nbw.accepting {
        if reachability[init as usize].contains(accepting)
            && reachability[*accepting as usize].contains(accepting)
        {
            return true;
        }
    }
    false
}
