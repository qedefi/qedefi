import EvmLean.Prelude.Bytes

/-! # SHA-256 (FIPS 180-4), for precompile `0x02`. -/

namespace EvmLean.Sha256

/-- SHA-256 digest (32 bytes). -/
def hash (data : ByteArray) : ByteArray := sorry

end EvmLean.Sha256
