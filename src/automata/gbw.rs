pub struct DotGBW<'a>(&'a GBW);

use std::{
    cmp,
    collections::{BTreeSet, HashMap, HashSet},
    iter,
};

use crate::automata::{
    AsDot,
    abw::{ABW, ABWPhi, abwphi_and, transition_cmp, transitions_simpl_keyed},
};

use super::util::*;

pub type GWBPhi = (BTreeSet<i64>, Q);
pub type GBWAccepting = Vec<(Q, usize)>;
#[derive(Debug, Clone)]
pub struct GBW {
    nodes: u32,
    initial: Q,
    labels: Vec<String>,
    phi: HashMap<Q, Vec<GWBPhi>>,
    // accepting transitions
    accepting: Vec<GBWAccepting>,
    unique_cache: HashMap<BTreeSet<Q>, Q>,
}

impl GBW {
    // create with true state
    const TRUE: Q = 0;
    fn new() -> Self {
        let labels = vec!["true".into()];
        let phi = HashMap::from_iter(iter::once((0u32, vec![(BTreeSet::new(), 0u32)])));
        let unique_cache = HashMap::from_iter(std::iter::once((BTreeSet::new(), 0)));
        Self {
            nodes: 1,
            initial: 0,
            labels,
            phi,
            accepting: Default::default(),
            unique_cache,
        }
    }
    // add TRUE to each accepting set
    fn finalize(&mut self) {
        for t_i in &mut self.accepting {
            t_i.push((Self::TRUE, 0));
        }
    }
}

impl<'a> std::fmt::Display for DotGBW<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let accepting_colors: Vec<_> = (0..self.0.accepting.len())
            .map(|_| random_color())
            .collect();
        write!(f, "digraph {{\n  rankdir=\"LR\";\n")?;
        let gbw = self.0;
        for i in 0..gbw.nodes {
            writeln!(
                f,
                r#"  {}[label="{}",shape="ellipse"];"#,
                i, gbw.labels[i as usize],
            )?;
        }
        for (node, transitions) in &gbw.phi {
            for (idx, (cond, succ)) in transitions.iter().enumerate() {
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
                let colorstr = self
                    .0
                    .accepting
                    .iter()
                    .enumerate()
                    .filter(|(_, edges)| edges.contains(&(*node, idx)))
                    .map(|(colidx, _)| accepting_colors[colidx].clone())
                    .reduce(|lstr, rstr| lstr + ":" + rstr.as_str())
                    .unwrap_or("black".into());
                writeln!(f, " [label=\"{condstring}\", color=\"{colorstr}\"];",)?;
            }
        }
        writeln!(f, "}}")
    }
}

impl<'a> AsDot for &'a GBW {
    type T = DotGBW<'a>;

    fn as_dot(&self) -> Self::T {
        DotGBW(self)
    }
}

fn abwphi_to_gbwphi(
    m: &ABW,
    abwphi: Vec<super::abw::ABWPhi>,
    out: &mut GBW,
    rejecting_accepting_map: &mut HashMap<Q, usize>,
) -> Vec<GWBPhi> {
    abwphi
        .into_iter()
        .map(|(syms, states)| {
            let node = vwabw_to_gbw_rec(m, states, out, rejecting_accepting_map);
            (syms, node)
        })
        .collect()
}

fn vwabw_to_gbw_rec(
    m: &ABW,
    state: BTreeSet<Q>,
    out: &mut GBW,
    rejecting_accepting_map: &mut HashMap<Q, usize>,
) -> u32 {
    if let Some(id) = out.unique_cache.get(&state) {
        return *id;
    }
    let node = out.nodes;
    out.nodes += 1;
    out.unique_cache.insert(state.clone(), node);
    let label = state
        .iter()
        .map(|&q| m.get_label(q))
        .fold(String::new(), |a, n| a + n + "\\n");
    out.labels.push(label);
    // true
    let mut transitions: Vec<ABWPhi> = vec![(Default::default(), Default::default())];
    for q in state {
        let trans2 = m.get_transition(&q);
        transitions = abwphi_and(transitions.iter(), trans2.iter());
    }
    // let trans = abwphi_to_gbwphi(m, trans, out);
    // update final
    let mut not_removable = HashSet::new();
    let mut new_accepting: HashMap<usize, Vec<(Q, usize)>> = HashMap::new();
    for &rejecting in m.get_rejecting() {
        let index = *rejecting_accepting_map.entry(rejecting).or_insert_with(|| {
            out.accepting.push(Default::default());
            out.accepting.len() - 1
        });
        let mut new_transitions = Vec::new();
        for (i, trans @ (_, states)) in transitions.iter().enumerate() {
            if !states.contains(&rejecting) {
                new_transitions.push(i);
            } else {
                let out_rejecting = m.get_transition(&rejecting);
                if out_rejecting.iter().any(|t| {
                    !t.1.contains(&rejecting)
                        && transition_cmp(trans, t) == Some(cmp::Ordering::Less)
                }) {
                    new_transitions.push(i);
                }
            }
        }
        let closure = |idx: &usize| -> &ABWPhi { &transitions[*idx] };
        let accessor: ClosureAccessor<ABWPhi, _, _> = closure.into();
        transitions_simpl_keyed(&mut new_transitions, accessor, |_| true);
        not_removable.extend(new_transitions.iter().cloned());
        new_accepting.insert(
            index,
            new_transitions.into_iter().map(|idx| (node, idx)).collect(),
        );
    }
    let mut indices_transitions: Vec<_> = (0..transitions.len()).collect();
    let closure = |idx: &usize| -> &ABWPhi { &transitions[*idx] };
    let accessor: ClosureAccessor<ABWPhi, _, _> = closure.into();
    // filter new transitions
    transitions_simpl_keyed(&mut indices_transitions, accessor, |idx| {
        !not_removable.contains(idx)
    });
    // patch old indices
    for (accepting_idx, v) in new_accepting.into_iter() {
        for (node, idx) in v.into_iter() {
            // has to be found
            let (new_idx, _) = indices_transitions
                .iter()
                .enumerate()
                .find(|(_, old_idx)| **old_idx == idx)
                .unwrap();
            out.accepting[accepting_idx].push((node, new_idx));
        }
    }
    let transitions_final = abwphi_to_gbwphi(
        m,
        indices_transitions
            .into_iter()
            .map(|idx| transitions[idx].clone())
            .collect(),
        out,
        rejecting_accepting_map,
    );
    out.phi.insert(node, transitions_final);
    node
}

pub fn vwabw_to_gbw(m: &ABW) -> GBW {
    let mut gbw = GBW::new();
    let root = vwabw_to_gbw_rec(
        m,
        BTreeSet::from_iter(std::iter::once(m.get_initial())),
        &mut gbw,
        &mut HashMap::new(),
    );
    gbw.initial = root;
    gbw.finalize();
    gbw
}
