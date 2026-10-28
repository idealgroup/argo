#[cfg(test)]
use std::collections::{BTreeMap, BTreeSet};
use std::{
    cell::{Cell, RefCell},
    marker::PhantomData,
    rc::Rc,
};

use aes::{
    Aes128, Block,
    cipher::{BlockEncrypt, KeyInit},
};
use ark_ec::AdditiveGroup;
use ark_ff::{Field, PrimeField};
use arrayvec::ArrayVec;
use rustc_hash::FxHashMap;

use crate::{
    garble::Nonce,
    utils::{
        aes_hash::{AES_BLOCK_SIZE, Hash, LEN_PER_BASE_ELEM},
        group::FromLeBytesModOrder,
    },
};

thread_local! {
    static AES_INSTANCES: RefCell<FxHashMap<[u8; 16], Rc<Aes128>>> =
        RefCell::new(FxHashMap::default());
    static AES_SCOPES: Cell<usize> = const { Cell::new(0) };
}

/// Caches AES key schedules on this thread until the outermost scope ends.
/// The keys are labels of one garbling, so a later garbling can't reuse them.
pub(crate) struct AesCacheScope(PhantomData<Rc<()>>);

impl AesCacheScope {
    pub(crate) fn new() -> Self {
        AES_SCOPES.with(|scopes| scopes.set(scopes.get() + 1));
        Self(PhantomData)
    }
}

impl Drop for AesCacheScope {
    fn drop(&mut self) {
        let scopes = AES_SCOPES.with(|scopes| {
            scopes.set(scopes.get() - 1);
            scopes.get()
        });
        if scopes == 0 {
            AES_INSTANCES.with(|instances| instances.take());
        }
    }
}

#[derive(Debug)]
pub(crate) struct AesCtr;

impl AesCtr {
    pub(crate) fn get_instance(key: &[u8; 16]) -> Rc<Aes128> {
        let new = || Rc::new(Aes128::new(&(*key).into()));
        if AES_SCOPES.with(Cell::get) == 0 {
            return new();
        }
        AES_INSTANCES
            .with(|instances| Rc::clone(instances.borrow_mut().entry(*key).or_insert_with(new)))
    }
}

impl Hash for AesCtr {
    #[inline]
    fn hash(key: &[u8; 16], msg: &[u8; 16]) -> [u8; 16] {
        let mut block = Block::from(*msg);
        Self::get_instance(key).encrypt_block(&mut block);

        #[cfg(test)]
        // Check that each msg is used only once per key.
        assert!(
            COUNTERS_MAP.with(|map| { map.borrow_mut().entry(*key).or_default().insert(*msg) })
        );

        block.into()
    }
}

impl AesCtr {
    /// Uses AesCtr as an XOF to produce random bytes for hash_to_field.
    /// Returns a random field element.
    ///
    /// # Panics
    ///
    /// Panics if F::extension_degree() > 2
    pub(crate) fn hash_to_field<F>(value: [u8; AES_BLOCK_SIZE], parent_nonce: &Nonce) -> F
    where
        F: Field,
        F::BasePrimeField: FromLeBytesModOrder,
    {
        let parent_nonce = &mut parent_nonce.clone();

        const MAX_EXTENSION_DEGREE: usize = 2;

        let mut base_prime_field_elems: ArrayVec<F::BasePrimeField, MAX_EXTENSION_DEGREE> =
            ArrayVec::new();
        let num_blocks_per_base_elem = LEN_PER_BASE_ELEM / AES_BLOCK_SIZE;

        let aes = AesCtr::get_instance(&value);

        let mut bytes = [0u8; LEN_PER_BASE_ELEM];

        for _ in 0..F::extension_degree() {
            // Will panic if m > MAX_EXTENSION_DEGREE (which is what you want)
            base_prime_field_elems.push(F::BasePrimeField::ZERO);
        }

        for elem in base_prime_field_elems.iter_mut() {
            for i in 0..num_blocks_per_base_elem {
                let nonce = parent_nonce.fork();
                let mut block = Block::from(nonce.bytes());
                aes.encrypt_block(&mut block);

                let start = i * AES_BLOCK_SIZE;
                bytes[start..start + AES_BLOCK_SIZE].copy_from_slice(&block);
            }

            *elem = <F::BasePrimeField as FromLeBytesModOrder>::from_le_bytes_mod_order(&bytes);
        }

        // This unwrap cannot fail because `base_prime_field_elems` is length
        // `m = F::extension_degree()`.
        F::from_base_prime_field_elems(base_prime_field_elems).unwrap()
    }

    /// The number of bytes of this field element as a multiple of AES blocks.
    ///
    /// # Panics
    ///
    /// Panics if the number of bytes is not a multiple of AES_BLOCK_SIZE.
    pub(crate) fn num_blocks<F: Field>() -> usize {
        let base_prime_field_num_bytes = F::BasePrimeField::MODULUS_BIT_SIZE.div_ceil(8) as usize;
        assert_eq!(base_prime_field_num_bytes & AES_BLOCK_SIZE, 0);
        let num_blocks = base_prime_field_num_bytes / AES_BLOCK_SIZE;

        F::extension_degree() as usize * num_blocks
    }
}

#[cfg(test)]
thread_local! {
    /// Mapping from seed to set of used counters; a counter should be used
    /// only once per seed
    pub(crate) static COUNTERS_MAP: RefCell<BTreeMap<[u8; AES_BLOCK_SIZE], BTreeSet<[u8; AES_BLOCK_SIZE]>>> = const { RefCell::new(BTreeMap::new()) }
}

#[cfg(test)]
/// Clear the set
pub(crate) fn clear_set() {
    COUNTERS_MAP.with(|map| {
        map.borrow_mut().clear();
    });
}

#[cfg(test)]
pub(crate) fn cached_instances() -> usize {
    AES_INSTANCES.with(|instances| instances.borrow().len())
}

#[test]
fn test_aes_cache_scope() {
    let hash = |byte| {
        AesCtr::hash(&[byte; 16], &[0; 16]);
    };

    hash(0);
    assert_eq!(cached_instances(), 0);

    let outer = AesCacheScope::new();
    hash(1);
    {
        let _inner = AesCacheScope::new();
        hash(2);
    }
    assert_eq!(cached_instances(), 2);
    drop(outer);
    assert_eq!(cached_instances(), 0);
    clear_set();
}
