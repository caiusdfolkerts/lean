module
prelude
public import GraphInputsRow29Part00044CheckedRecord005Segment011
public import GraphInputsRow29Part00044Data
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00044
open Papers.RationalityTen PackedGraphCertificate FiniteChecks
theorem record005_nodes_1152 (record005_valid : GraphGrowthInputs.Valid record005.inputs) : Interval (record005.nodeTestValid record005_valid) 1152 1184 :=
  interval_of_check _ 1152 32 (by decide_kernel_context)
theorem record005_nodes_1184 (record005_valid : GraphGrowthInputs.Valid record005.inputs) : Interval (record005.nodeTestValid record005_valid) 1184 1193 :=
  interval_of_check _ 1184 9 (by decide_kernel_context)
theorem record005_supports : record005.Supports := by unfold RawData.Supports; decide +kernel
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00044
