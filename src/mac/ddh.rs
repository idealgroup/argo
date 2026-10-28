use ark_ec::{
    CurveGroup,
    scalar_mul::glv::GLVConfig,
    short_weierstrass::{Affine, Projective, SWCurveConfig},
};
use ark_ff::Zero;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};

use crate::mac::{
    MacKey,
    endo::{Endo, EndoMacKey, EndoScalar, PSqModR},
};

pub(crate) struct DDHMacKey<G: SWCurveConfig, const KAPPA: usize> {
    pub(crate) T: [Affine<G>; KAPPA],
    pub(crate) phis: [EndoScalar<G>; KAPPA],
    pub(crate) a: G::ScalarField,
}

impl<G: GLVConfig + Clone, const KAPPA: usize> From<DDHMacKey<G, KAPPA>>
    for [EndoMacKey<G, Affine<G>>; KAPPA]
{
    fn from(val: DDHMacKey<G, KAPPA>) -> Self {
        let ks: Vec<_> = val.T.iter().map(|T| *T * val.a).collect();
        let ks = Projective::<G>::normalize_batch(&ks);

        let mut endo_mac_keys = Vec::with_capacity(KAPPA);

        val.phis.iter().zip(ks.iter()).for_each(|(phi, &k)| {
            let endo_mac_key = EndoMacKey {
                phi: phi.clone(),
                k_scalar: None,
                k,
            };
            endo_mac_keys.push(endo_mac_key);
        });
        endo_mac_keys
            .try_into()
            // This unwrap cannot fail because both `phis` and `ks` are of
            // length `KAPPA`.
            .unwrap_or_else(|_| panic!())
    }
}

#[derive(Debug, CanonicalSerialize, CanonicalDeserialize, Clone)]
pub(crate) struct DDHMac<G: SWCurveConfig, const KAPPA: usize>(pub(crate) [Affine<G>; KAPPA]);

impl<G, const KAPPA: usize> MacKey<Affine<G>, DDHMac<G, KAPPA>> for DDHMacKey<G, KAPPA>
where
    G: GLVConfig + PSqModR,
{
    // phi[i].endo(P) + aT[i]
    fn encode(&self, value: &Affine<G>) -> DDHMac<G, KAPPA> {
        let mut macs = [Projective::<G>::zero(); KAPPA];
        macs.iter_mut()
            .zip(self.phis.iter())
            .zip(self.T.iter())
            .for_each(|((mac, phi), T)| *mac = phi.endo(*value) + *T * self.a);

        let macs = Projective::<G>::normalize_batch(&macs);

        DDHMac(
            // This unwrap cannot fail since the affine `mac` was a fixed
            // array of length `KAPPA`
            macs.try_into().unwrap(),
        )
    }

    #[cfg(test)]
    fn decode(&self, _mac: &DDHMac<G, KAPPA>) -> Affine<G> {
        unimplemented!()
    }

    fn random_key(_rng: &mut impl rand_core::CryptoRngCore) -> Self {
        unimplemented!()
    }
}
