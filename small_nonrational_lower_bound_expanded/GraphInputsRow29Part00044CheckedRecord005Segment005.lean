module
prelude
public import GraphInputsRow29Part00044CheckedRecord005Segment004
public import GraphInputsRow29Part00044Data
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00044
open Papers.RationalityTen PackedGraphCertificate FiniteChecks
theorem record005_nodes_480 (record005_valid : GraphGrowthInputs.Valid record005.inputs) : Interval (record005.nodeTestValid record005_valid) 480 512 :=
  interval_of_check _ 480 32 (by decide_kernel_context)
theorem record005_nodes_512 (record005_valid : GraphGrowthInputs.Valid record005.inputs) : Interval (record005.nodeTestValid record005_valid) 512 544 :=
  interval_of_check _ 512 32 (by decide_kernel_context)
theorem record005_nodes_544 (record005_valid : GraphGrowthInputs.Valid record005.inputs) : Interval (record005.nodeTestValid record005_valid) 544 576 :=
  interval_of_check _ 544 32 (by decide_kernel_context)
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00044
