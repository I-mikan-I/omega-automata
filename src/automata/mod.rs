#![allow(clippy::upper_case_acronyms)]
use super::ltl;
use rand::random_range;
use std::borrow::Borrow;
use std::cmp;
use std::collections::*;
use std::hash::BuildHasher;
use std::marker::PhantomData;
use std::ops::Index;

pub type Q = u32;
const SELF: u32 = u32::MAX;
pub type E = u32;

#[derive(Debug, Default, Clone)]
struct NBW {
    phi: HashMap<Q, Vec<(HashSet<E>, Q)>>,
    accepting: HashSet<Q>,
}

type ABWPhi = (BTreeSet<i64>, BTreeSet<Q>);
#[derive(Debug, Default, Clone)]
struct ABW {
    nodes: u32,
    // sets of symbols E encoded as S: E = { 2e | \forall e \in 2e : !e \not \in S }.
    // E.g. S = {1, -2} encodes E = { 2e | 1 \in 2e \wedge -2 \in 2e }
    phi: HashMap<Q, Vec<ABWPhi>>,
    labels: Vec<String>,
    // co-buechi
    rejecting: HashSet<Q>,

    // maps phi hashes -> nodes
    nodes_unique_cache: HashMap<u64, Q>,
}
struct DotABW<'a>(&'a ABW);

type GBAPhi = (BTreeSet<i64>, Q);
type GBAAccepting = Vec<(Q, usize)>;
#[derive(Debug, Default, Clone)]
struct GBA {
    nodes: u32,
    labels: Vec<String>,
    phi: HashMap<Q, Vec<GBAPhi>>,
    // accepting transitions
    accepting: Vec<GBAAccepting>,
}

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
/**
 * trans1 < trans2 <=> trans1.0 \subseteq trans2.0 and trans1.1 \supseteq trans2.1 (trans1 implies trans2)
 */
fn transition_cmp(trans1: &ABWPhi, trans2: &ABWPhi) -> Option<cmp::Ordering> {
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

fn id(t: &ABWPhi) -> &ABWPhi {
    t
}

struct IdentityAccessor {}

impl<'this> AccessorLifetime<'this, &'this Self> for IdentityAccessor {
    type Item = &'this ABWPhi;
}

impl Accessor<ABWPhi> for IdentityAccessor {
    fn access<'this, 'a>(
        &'this self,
        k: &'a ABWPhi,
    ) -> <Self as AccessorLifetime<'a, &'a Self>>::Item {
        k
    }
}

fn transitions_simpl(transitions: &mut Vec<ABWPhi>) {
    let acc = IdentityAccessor {};
    transitions_simpl_keyed(transitions, acc);
}

trait AccessorLifetime<'this, ExtraParam> {
    type Item: Borrow<ABWPhi>;
}

trait Accessor<K>
where
    for<'this> Self: AccessorLifetime<'this, &'this Self>,
{
    fn access<'this, 'a>(&'this self, k: &'a K) -> <Self as AccessorLifetime<'a, &'a Self>>::Item;
}

struct ClosureAccessor<'a, F, K>
where
    F: Fn(&'a K) -> &'a ABWPhi,
{
    closure: F,
    _a: PhantomData<&'a K>,
}

impl<'this, 'a, K, F: Fn(&K) -> &'a ABWPhi> AccessorLifetime<'this, &'this Self>
    for ClosureAccessor<'a, F, K>
{
    type Item = &'this ABWPhi;
}

impl<'this, K, F: Fn(&K) -> &'this ABWPhi> Accessor<K> for ClosureAccessor<'this, F, K> {
    fn access<'a, 'b>(&'a self, k: &'b K) -> <Self as AccessorLifetime<'b, &'b Self>>::Item {
        let c = &self.closure;
        c(k)
    }
}

fn transitions_simpl_keyed<'a, K, A: Accessor<K>>(transitions: &'a mut Vec<K>, access: A) {
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
                    transitions.remove(i);
                    continue 'outer;
                }
                Some(cmp::Ordering::Greater) => {
                    transitions.remove(k);
                    continue;
                }
                None => {}
                _ => panic!(),
            }
            k += 1;
        }
    }
    transitions.sort_by(|l, r| {
        let lv = access.access(&l);
        let rv = access.access(&r);
        lv.borrow().cmp(rv.borrow())
    });
}
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
    let (mut new_phi, rejecting) = match formulas[f.1] {
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
            let mut phi_new = phi_and!(abw.phi[&node2].clone(), cont.clone());
            transitions_simpl(&mut phi_new);
            (phi_new, false)
        }
        ltl::Operator::And(i, j) => {
            let node1 = ltl_to_abw_rec(formulas.access(i), abw);
            let node2 = ltl_to_abw_rec(formulas.access(j), abw);

            let mut phi_new = phi_and!(abw.phi[&node1], abw.phi[&node2].iter());
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
    {
        let hash = abw.nodes_unique_cache.hasher().hash_one(&new_phi);
        if let Some(q) = abw.nodes_unique_cache.get(&hash) {
            let mut phi_expected: Vec<_> = new_phi
                .iter()
                .cloned()
                .map(|(syms, mut nodes)| {
                    if nodes.contains(&SELF) {
                        nodes.remove(&SELF);
                        nodes.insert(*q);
                    }
                    (syms, nodes)
                })
                .collect();
            transitions_simpl(&mut phi_expected);
            if abw.phi[q] == phi_expected && (rejecting == abw.rejecting.contains(q)) {
                abw.labels[*q as usize].push_str(&format!("\\n{}", f));
                return *q;
            }
        } else {
            abw.nodes_unique_cache.insert(hash, abw.nodes);
            new_phi.iter_mut().for_each(|(_, nodes)| {
                assert!(!nodes.contains(&abw.nodes));
                if nodes.contains(&SELF) {
                    nodes.remove(&SELF);
                    nodes.insert(abw.nodes);
                }
            });
            transitions_simpl(&mut new_phi);
        }
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
fn ltl_to_abw(f: ltl::Formula<'_>) -> ABW {
    let mut abw = ABW::default();
    let root = ltl_to_abw_rec(f, &mut abw);
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
            let hash = abw.nodes_unique_cache.hasher().hash_one(&abw.phi[&q]);
            if abw.nodes_unique_cache.get(&hash) == Some(&q) {
                abw.nodes_unique_cache.remove(&hash);
            }
            abw.phi.remove(&q);
            abw.labels[q as usize] = "".into();
            abw.rejecting.remove(&q);
        }
    }
    abw
}

fn abwphi_to_gbwphi(
    m: &ABW,
    abwphi: Vec<ABWPhi>,
    out: &mut GBA,
    rejecting_accepting_map: &mut HashMap<Q, usize>,
) -> Vec<GBAPhi> {
    abwphi
        .into_iter()
        .map(|(syms, states)| {
            let node = vwabw_to_gbw_rec(m, states, out, rejecting_accepting_map);
            return (syms, node);
        })
        .collect()
}

fn vwabw_to_gbw_rec(
    m: &ABW,
    state: BTreeSet<Q>,
    out: &mut GBA,
    rejecting_accepting_map: &mut HashMap<Q, usize>,
) -> u32 {
    let node = out.nodes;
    // true
    let mut transitions: Vec<ABWPhi> = vec![(Default::default(), Default::default())];
    for q in state {
        let trans2 = &m.phi[&q];
        transitions = phi_and!(transitions, trans2.iter());
    }
    // let trans = abwphi_to_gbwphi(m, trans, out);
    // update final
    for &rejecting in &m.rejecting {
        let index = rejecting_accepting_map[&rejecting];
        let mut new_transitions = Vec::new();
        for (i, trans @ (_, states)) in transitions.iter().enumerate() {
            if !states.contains(&rejecting) {
                new_transitions.push(i);
            } else {
                let out_rejecting = &m.phi[&rejecting];
                if out_rejecting.iter().any(|t| {
                    !t.1.contains(&rejecting)
                        && transition_cmp(trans, t) == Some(cmp::Ordering::Less)
                }) {
                    new_transitions.push(i);
                }
            }
        }
        let closure = |idx: &usize| -> &ABWPhi { &transitions[*idx] };
        let accessor: ClosureAccessor<_, _> = ClosureAccessor {
            closure,
            _a: PhantomData::default(),
        };
        let t: &mut _ = &mut new_transitions;
        transitions_simpl_keyed(t, accessor);
        out.accepting[index] = new_transitions.into_iter().map(|idx| (node, idx)).collect();
    }
    todo!()
}

fn vwabw_to_gbw(m: &ABW) -> GBA {
    todo!()
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
