module
prelude
public import GraphInputsRow29Part00044CheckedRecord005Segment012
public import GraphInputsRow29Part00044Data
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00044
open Papers.RationalityTen PackedGraphCertificate FiniteChecks
theorem record005_leaf_0 : Interval record005.leafTest 0 8 :=
  interval_of_check _ 0 8 (by decide +kernel)
theorem record005_leaf_8 : Interval record005.leafTest 8 16 :=
  interval_of_check _ 8 8 (by decide +kernel)
theorem record005_leaf_16 : Interval record005.leafTest 16 24 :=
  interval_of_check _ 16 8 (by decide +kernel)
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00044
