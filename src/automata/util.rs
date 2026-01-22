pub type Q = u32;
pub const SELF: u32 = u32::MAX;
pub type E = u32;

use std::{borrow::Borrow, collections::BTreeSet, marker::PhantomData};

use rand::random_range;

pub enum Implication {
    Implies,
    Implied,
    None,
}
pub trait Transition {
    fn implies(&self, other: &Self) -> Implication;
}
pub fn syms_subset(syms1: &BTreeSet<i64>, syms2: &BTreeSet<i64>) -> bool {
    syms1.iter().all(|&i| !syms2.contains(&-i))
}
/**
 * Simplifies VWABW transitions and sorts them lexicographically.
 */
pub fn transitions_simpl_keyed<
    K,
    V: std::cmp::Ord + Transition,
    A: Accessor<K, V>,
    F: Fn(&K) -> bool,
>(
    transitions: &mut Vec<K>,
    access: A,
    removable: F,
) {
    'outer: for i in 0..transitions.len() {
        let mut k = i + 1;
        while k < transitions.len() {
            let left = access.access(&transitions[i]);
            let right = access.access(&transitions[k]);
            let result = left.borrow().implies(right.borrow());
            drop(left);
            drop(right);
            match result {
                Implication::Implied => {
                    if removable(&transitions[i]) {
                        transitions.remove(i);
                    }
                    continue 'outer;
                }
                Implication::Implies => {
                    if removable(&transitions[k]) {
                        transitions.remove(k);
                    }
                    continue;
                }
                Implication::None => {}
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

pub fn transitions_simpl<V: Transition + std::cmp::Ord>(transitions: &mut Vec<V>) {
    let acc = IdentityAccessor::default();
    transitions_simpl_keyed(transitions, acc, |_| true);
}

pub struct IdentityAccessor<V> {
    _a: PhantomData<V>,
}

impl<V> Default for IdentityAccessor<V> {
    fn default() -> Self {
        Self {
            _a: Default::default(),
        }
    }
}

impl<'this, V> AccessorLifetime<'this, &'this Self, V> for IdentityAccessor<V> {
    type Item = &'this V;
}

impl<V> Accessor<V, V> for IdentityAccessor<V> {
    fn access<'a>(&self, k: &'a V) -> <Self as AccessorLifetime<'a, &'a Self, V>>::Item {
        k
    }
}

pub trait AccessorLifetime<'this, ExtraParam, V> {
    type Item: Borrow<V>;
}

pub trait Accessor<K, V>
where
    for<'this> Self: AccessorLifetime<'this, &'this Self, V>,
{
    fn access<'a>(&self, k: &'a K) -> <Self as AccessorLifetime<'a, &'a Self, V>>::Item;
}

pub struct ClosureAccessor<'a, V: 'a, F, K>
where
    F: Fn(&'a K) -> &'a V,
{
    closure: F,
    _a: PhantomData<&'a K>,
}

impl<'a, V, F, K> ClosureAccessor<'a, V, F, K> where F: Fn(&'a K) -> &'a V {}

impl<'a, V, F, K> From<F> for ClosureAccessor<'a, V, F, K>
where
    F: Fn(&'a K) -> &'a V,
{
    fn from(closure: F) -> Self {
        Self {
            closure,
            _a: Default::default(),
        }
    }
}

impl<'this, 'a, K, V, F: Fn(&K) -> &'a V> AccessorLifetime<'this, &'this Self, V>
    for ClosureAccessor<'a, V, F, K>
{
    type Item = &'this V;
}

impl<'this, V, K, F: Fn(&K) -> &'this V> Accessor<K, V> for ClosureAccessor<'this, V, F, K> {
    fn access<'b>(&self, k: &'b K) -> <Self as AccessorLifetime<'b, &'b Self, V>>::Item {
        let c = &self.closure;
        c(k)
    }
}

pub fn random_color() -> String {
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
