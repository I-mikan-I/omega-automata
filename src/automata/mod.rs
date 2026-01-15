#![allow(clippy::upper_case_acronyms)]
use super::ltl;
use rand::random_range;
use std::borrow::Borrow;
use std::cmp;
use std::collections::*;
use std::hash::BuildHasher;
use std::iter;
use std::marker::PhantomData;

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
struct DotABW<'a>(&'a ABW);
struct DotGBW<'a>(&'a GBW);

type GWBPhi = (BTreeSet<i64>, Q);
type GBWAccepting = Vec<(Q, usize)>;
#[derive(Debug, Clone)]
struct GBW {
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

fn random_color() -> String {
    let hue: f32 = random_range(0.0..360.0);
    let lightness: f32 = random_range(0.2..=0.9);
    let [r, g, b, _] = color::OpaqueColor::<color::Oklch>::new([lightness, 0.2, hue])
        .to_rgba8()
        .to_u8_array();
    format!(
        "#{}",
        [r, g, b]
            .into_iter()
            .map(|i| format!("{i:02x}"))
            .collect::<String>()
    )
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

impl<'a> AsDot for &'a GBW {
    type T = DotGBW<'a>;

    fn as_dot(&self) -> Self::T {
        DotGBW(self)
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
    fn access<'a>(&self, k: &'a ABWPhi) -> <Self as AccessorLifetime<'a, &'a Self>>::Item {
        k
    }
}

fn transitions_simpl(transitions: &mut Vec<ABWPhi>) {
    let acc = IdentityAccessor {};
    transitions_simpl_keyed(transitions, acc, |_| true);
}

trait AccessorLifetime<'this, ExtraParam> {
    type Item: Borrow<ABWPhi>;
}

trait Accessor<K>
where
    for<'this> Self: AccessorLifetime<'this, &'this Self>,
{
    fn access<'a>(&self, k: &'a K) -> <Self as AccessorLifetime<'a, &'a Self>>::Item;
}

struct ClosureAccessor<'a, F, K>
where
    F: Fn(&'a K) -> &'a ABWPhi,
{
    closure: F,
    _a: PhantomData<&'a K>,
}

impl<'a, F, K> ClosureAccessor<'a, F, K> where F: Fn(&'a K) -> &'a ABWPhi {}

impl<'a, F, K> From<F> for ClosureAccessor<'a, F, K>
where
    F: Fn(&'a K) -> &'a ABWPhi,
{
    fn from(closure: F) -> Self {
        Self {
            closure,
            _a: Default::default(),
        }
    }
}

impl<'this, 'a, K, F: Fn(&K) -> &'a ABWPhi> AccessorLifetime<'this, &'this Self>
    for ClosureAccessor<'a, F, K>
{
    type Item = &'this ABWPhi;
}

impl<'this, K, F: Fn(&K) -> &'this ABWPhi> Accessor<K> for ClosureAccessor<'this, F, K> {
    fn access<'b>(&self, k: &'b K) -> <Self as AccessorLifetime<'b, &'b Self>>::Item {
        let c = &self.closure;
        c(k)
    }
}

fn transitions_simpl_keyed<K, A: Accessor<K>, F: Fn(&K) -> bool>(
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
        .map(|&q| m.labels[q as usize].as_str())
        .fold(String::new(), |a, n| a + n + "\\n");
    out.labels.push(label);
    // true
    let mut transitions: Vec<ABWPhi> = vec![(Default::default(), Default::default())];
    for q in state {
        let trans2 = &m.phi[&q];
        transitions = phi_and!(transitions, trans2.iter());
    }
    // let trans = abwphi_to_gbwphi(m, trans, out);
    // update final
    let mut not_removable = HashSet::new();
    let mut new_accepting: HashMap<usize, Vec<(Q, usize)>> = HashMap::new();
    for &rejecting in &m.rejecting {
        let index = *rejecting_accepting_map.entry(rejecting).or_insert_with(|| {
            out.accepting.push(Default::default());
            out.accepting.len() - 1
        });
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
        let accessor: ClosureAccessor<_, _> = closure.into();
        transitions_simpl_keyed(&mut new_transitions, accessor, |_| true);
        not_removable.extend(new_transitions.iter().cloned());
        new_accepting.insert(
            index,
            new_transitions.into_iter().map(|idx| (node, idx)).collect(),
        );
    }
    let mut indices_transitions: Vec<_> = (0..transitions.len()).collect();
    let closure = |idx: &usize| -> &ABWPhi { &transitions[*idx] };
    let accessor: ClosureAccessor<_, _> = closure.into();
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

fn vwabw_to_gbw(m: &ABW) -> GBW {
    let mut gbw = GBW::new();
    let root = vwabw_to_gbw_rec(
        m,
        BTreeSet::from_iter(std::iter::once(m.initial)),
        &mut gbw,
        &mut HashMap::new(),
    );
    gbw.initial = root;
    gbw.finalize();
    gbw
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
}
