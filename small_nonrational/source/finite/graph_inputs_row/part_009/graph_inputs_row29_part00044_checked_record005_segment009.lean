module
prelude
public import GraphInputsRow29Part00044CheckedRecord005Segment008
public import GraphInputsRow29Part00044Data
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00044
open Papers.RationalityTen PackedGraphCertificate FiniteChecks
theorem record005_nodes_864 (record005_valid : GraphGrowthInputs.Valid record005.inputs) : Interval (record005.nodeTestValid record005_valid) 864 896 :=
  interval_of_check _ 864 32 (by decide_kernel_context)
theorem record005_nodes_896 (record005_valid : GraphGrowthInputs.Valid record005.inputs) : Interval (record005.nodeTestValid record005_valid) 896 928 :=
  interval_of_check _ 896 32 (by decide_kernel_context)
theorem record005_nodes_928 (record005_valid : GraphGrowthInputs.Valid record005.inputs) : Interval (record005.nodeTestValid record005_valid) 928 960 :=
  interval_of_check _ 928 32 (by decide_kernel_context)
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00044
