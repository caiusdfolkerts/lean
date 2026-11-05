module
prelude
public import GraphInputsRow29Part00044CheckedRecord005Segment003
public import GraphInputsRow29Part00044Data
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00044
open Papers.RationalityTen PackedGraphCertificate FiniteChecks
theorem record005_nodes_384 (record005_valid : GraphGrowthInputs.Valid record005.inputs) : Interval (record005.nodeTestValid record005_valid) 384 416 :=
  interval_of_check _ 384 32 (by decide_kernel_context)
theorem record005_nodes_416 (record005_valid : GraphGrowthInputs.Valid record005.inputs) : Interval (record005.nodeTestValid record005_valid) 416 448 :=
  interval_of_check _ 416 32 (by decide_kernel_context)
theorem record005_nodes_448 (record005_valid : GraphGrowthInputs.Valid record005.inputs) : Interval (record005.nodeTestValid record005_valid) 448 480 :=
  interval_of_check _ 448 32 (by decide_kernel_context)
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00044
