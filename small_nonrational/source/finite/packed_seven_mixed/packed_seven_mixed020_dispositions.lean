module
prelude
public import PackedSevenMixed020Classification
public import RawLeafCertificate

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.PackedReplay.PackedSevenMixed020
open Papers.RationalityTen
/-- These exact closed leaves violate the required facet count of kind 0.
For an empty dummy leaf the distinguished root quota is one. -/
def disposition (_j : Fin 1) : RawLeafCertificate.Certificate := .quota 0
theorem disposition_checked : ∀ j : Fin 1,
    RawLeafCertificate.check quota ((rawLeaves j.val).map rawCells)
      (disposition j) = true := by decide +kernel
#print axioms disposition_checked
end Papers.RationalityTen.PackedReplay.PackedSevenMixed020
