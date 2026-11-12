pub(crate) mod aes_ctr;
pub(crate) mod aes_mitccr;

/// The number of bytes in an AES128 block
pub(crate) const AES_BLOCK_SIZE: usize = 16;

/// Number of random bytes needed for Fq hash_to_field at 128 bits of security
pub(crate) const LEN_PER_BASE_ELEM: usize = 48;

pub trait Hash {
    fn hash(key: &[u8; 16], msg: &[u8; 16]) -> [u8; 16];
}
