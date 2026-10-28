use thiserror::Error;

#[derive(Error, Debug)]
pub enum GarbleError {
    #[error("There was no aux {0} provided to {1}.")]
    AuxError(&'static str, &'static str),
    #[error("There was no dst provided to {0}::derive_output_mac_key.")]
    DeriveOutputMacKeyError(&'static str),
    #[error("Could not reconstruct DigitMacKey.")]
    DigitMacKeyReconstructionError,
    #[error("{0} is not a valid curve point.")]
    InvalidEndoMacKeyK(String),
    #[error("Missing DST in Encrypt<AesMiTCCR, Mac1>::encrypt")]
    MissingDST,
    #[error("Missing k_scalar in {0} EndoMacKey.")]
    MissingKScalar(&'static str),
    #[error("The verifier key's pairing constant is zero.")]
    DegenerateVerifierKey,
}

#[derive(Error, Debug, Clone, Copy, PartialEq, Eq)]
pub enum VerifierKeyError {
    #[error("The verifying key has no gamma_abc_g1 constant term.")]
    MissingConstantTerm,
    #[error("Expected {expected} public inputs, got {actual}.")]
    PublicInputLength { expected: usize, actual: usize },
    #[error("Expected {expected} garbled public inputs, got {actual}.")]
    GarbledInputCount { expected: usize, actual: usize },
    #[error("The verifying key's pairing constant is zero.")]
    DegenerateKey,
}

#[derive(Error, Debug, Clone, Copy, PartialEq, Eq)]
pub enum InputError {
    #[error("Expected {expected} input bits, got {actual}.")]
    BitCount { expected: usize, actual: usize },
    #[error("Expected {expected} input labels, got {actual}.")]
    LabelCount { expected: usize, actual: usize },
}

#[derive(Error, Debug)]
pub enum EvalError {
    #[error("There was more than one collision in decoding.")]
    DecodingError,
    #[error("Invalid plaintext for {0}::decrypt")]
    DecryptionError(&'static str),
    #[error("Could not reconstruct GroupMac from DigitMac.")]
    DigitMacReconstructionError,
    #[error("Missing y tables for field_mac_to_ec_mac.")]
    MissingYTablesError,
    #[error("Input is the doubling point of a field_mac_to_ec_mac replica.")]
    DoublingInput,
    #[error("Missing global identifier in {0}")]
    MissingGID(&'static str),
    #[error("Missing DST in Encrypt<AesMiTCCR, Mac1>::decrypt")]
    MissingDST,
    #[error("The table does not have the shape that garbling produces.")]
    MalformedTable,
    #[error("A converted MAC has no point on the curve.")]
    InvalidMacPoint,
    #[error("A pairing's Miller loop output is zero.")]
    DegeneratePairing,
}
