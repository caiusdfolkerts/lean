module
prelude
public import GraphInputsRow29Part00044CheckedRecord005Segment013
public import GraphInputsRow29Part00044Data
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00044
open Papers.RationalityTen PackedGraphCertificate FiniteChecks
theorem record005_leaf_24 : Interval record005.leafTest 24 32 :=
  interval_of_check _ 24 8 (by decide +kernel)
theorem record005_leaf_32 : Interval record005.leafTest 32 40 :=
  interval_of_check _ 32 8 (by decide +kernel)
theorem record005_leaf_40 : Interval record005.leafTest 40 48 :=
  interval_of_check _ 40 8 (by decide +kernel)
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00044
