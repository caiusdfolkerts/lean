module
prelude
public import GraphInputsRow29Part00044CheckedRecord005Segment009
public import GraphInputsRow29Part00044Data
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00044
open Papers.RationalityTen PackedGraphCertificate FiniteChecks
theorem record005_nodes_960 (record005_valid : GraphGrowthInputs.Valid record005.inputs) : Interval (record005.nodeTestValid record005_valid) 960 992 :=
  interval_of_check _ 960 32 (by decide_kernel_context)
theorem record005_nodes_992 (record005_valid : GraphGrowthInputs.Valid record005.inputs) : Interval (record005.nodeTestValid record005_valid) 992 1024 :=
  interval_of_check _ 992 32 (by decide_kernel_context)
theorem record005_nodes_1024 (record005_valid : GraphGrowthInputs.Valid record005.inputs) : Interval (record005.nodeTestValid record005_valid) 1024 1056 :=
  interval_of_check _ 1024 32 (by decide_kernel_context)
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00044
