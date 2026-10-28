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
}
