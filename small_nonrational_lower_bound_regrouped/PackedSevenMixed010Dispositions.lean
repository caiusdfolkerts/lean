module
prelude
public meta import LowerSchemas.FinitePackedSevenMixed
public import PackedSevenMixed010Classification
public import RawLeafCertificate

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.PackedReplay.PackedSevenMixed010
open Papers.RationalityTen
/-- These exact closed leaves violate the required facet count of kind 0.
For an empty dummy leaf the distinguished root quota is one. -/
cert_disposition 1 0
cert_disposition_checked 1
#print axioms disposition_checked
end Papers.RationalityTen.PackedReplay.PackedSevenMixed010
