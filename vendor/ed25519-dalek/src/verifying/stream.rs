use curve25519_dalek::edwards::CompressedEdwardsY;
use sha2::Sha512;

use crate::verifying::RCompute;
use crate::{signature::InternalSignature, InternalError, SignatureError, VerifyingKey};

/// An IUF verifier for ed25519.
///
/// Created with [`VerifyingKey::verify_stream()`] or [`SigningKey::verify_stream()`].
///
/// [`SigningKey::verify_stream()`]: super::SigningKey::verify_stream()
#[allow(non_snake_case)]
pub struct StreamVerifier {
    cr: RCompute<Sha512>,
    sig_R: CompressedEdwardsY,
}

impl StreamVerifier {
    /// Constructs new stream verifier.
    ///
    /// Seeds hash state with public key and signature components.
    pub(crate) fn new(public_key: VerifyingKey, signature: InternalSignature) -> Self {
        Self {
            cr: RCompute::new(&public_key, signature, None),
            sig_R: signature.R,
        }
    }

    /// Digest message chunk.
    pub fn update(&mut self, chunk: impl AsRef<[u8]>) {
        self.cr.update(chunk.as_ref());
    }

    /// Finalize verifier and check against candidate signature.
    #[allow(non_snake_case)]
    pub fn finalize_and_verify(self) -> Result<(), SignatureError> {
        let expected_R = self.cr.finish();

        if expected_R == self.sig_R {
            Ok(())
        } else {
            Err(InternalError::Verify.into())
        }
    }
}
