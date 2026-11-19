module
prelude
public import GraphInputsRow29Part00044CheckedRecord005Segment010
public import GraphInputsRow29Part00044Data
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00044
open Papers.RationalityTen PackedGraphCertificate FiniteChecks
theorem record005_nodes_1056 (record005_valid : GraphGrowthInputs.Valid record005.inputs) : Interval (record005.nodeTestValid record005_valid) 1056 1088 :=
  interval_of_check _ 1056 32 (by decide_kernel_context)
theorem record005_nodes_1088 (record005_valid : GraphGrowthInputs.Valid record005.inputs) : Interval (record005.nodeTestValid record005_valid) 1088 1120 :=
  interval_of_check _ 1088 32 (by decide_kernel_context)
theorem record005_nodes_1120 (record005_valid : GraphGrowthInputs.Valid record005.inputs) : Interval (record005.nodeTestValid record005_valid) 1120 1152 :=
  interval_of_check _ 1120 32 (by decide_kernel_context)
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00044
