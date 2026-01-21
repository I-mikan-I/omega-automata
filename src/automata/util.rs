pub type Q = u32;
pub const SELF: u32 = u32::MAX;
pub type E = u32;

use std::{borrow::Borrow, marker::PhantomData};

use rand::random_range;


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
