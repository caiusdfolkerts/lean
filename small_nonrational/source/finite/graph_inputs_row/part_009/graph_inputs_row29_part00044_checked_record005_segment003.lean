module
prelude
public import GraphInputsRow29Part00044CheckedRecord005Segment002
public import GraphInputsRow29Part00044Data
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00044
open Papers.RationalityTen PackedGraphCertificate FiniteChecks
theorem record005_nodes_288 (record005_valid : GraphGrowthInputs.Valid record005.inputs) : Interval (record005.nodeTestValid record005_valid) 288 320 :=
  interval_of_check _ 288 32 (by decide_kernel_context)
theorem record005_nodes_320 (record005_valid : GraphGrowthInputs.Valid record005.inputs) : Interval (record005.nodeTestValid record005_valid) 320 352 :=
  interval_of_check _ 320 32 (by decide_kernel_context)
theorem record005_nodes_352 (record005_valid : GraphGrowthInputs.Valid record005.inputs) : Interval (record005.nodeTestValid record005_valid) 352 384 :=
  interval_of_check _ 352 32 (by decide_kernel_context)
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00044
