module
prelude
public import Papers.RawWitnesses.Type52Data

/-! Small ordinary kernel checks for Appendix B type 52. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
@[expose] public section
namespace Papers.RationalWitnesses.RawWitnesses.Type52
open Papers.RationalWitnesses.Raw

theorem spanning_check : MinorValid coordinates certificate.spanningRows id
    certificate.spanningDenominator certificate.spanningInverse := by decide +kernel

end Papers.RationalWitnesses.RawWitnesses.Type52
