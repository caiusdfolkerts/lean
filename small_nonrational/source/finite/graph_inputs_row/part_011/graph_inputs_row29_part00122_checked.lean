module
prelude
public import GraphInputsRow29Part00122Data
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00122
open Papers.RationalityTen PackedGraphCertificate FiniteChecks
theorem record000_nodes_0 (record000_valid : GraphGrowthInputs.Valid record000.inputs) : Interval (record000.nodeTestValid record000_valid) 0 7 :=
  interval_of_check _ 0 7 (by decide_kernel_context)
theorem record000_supports : record000.Supports := by unfold RawData.Supports; decide +kernel
theorem record000_leaf_0 : Interval record000.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record000_leaves_nodup (j : Fin record000.l) : (record000.leaf j).Nodup :=
  record000.leaves_nodup_of_interval record000_leaf_0 j
theorem record000_checked (record000_valid : GraphGrowthInputs.Valid record000.inputs) : Interval (record000.nodeTestValid record000_valid) 0 7 :=
  (record000_nodes_0 record000_valid)
theorem record000_raw_node_checks (record000_valid : GraphGrowthInputs.Valid record000.inputs) (i : Fin record000.t) :
    RawGraphConditionedGrowth.nodeCheck (record000.inputs.problem record000_valid)
      record000.maps record000.leaf record000.nodes i = true :=
  record000.node_checks_valid record000_valid record000_supports (record000_checked record000_valid) i
#print axioms record000_raw_node_checks
theorem record001_nodes_0 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 0 32 :=
  interval_of_check _ 0 32 (by decide_kernel_context)
theorem record001_nodes_32 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 32 48 :=
  interval_of_check _ 32 16 (by decide_kernel_context)
theorem record001_supports : record001.Supports := by unfold RawData.Supports; decide +kernel
theorem record001_leaf_0 : Interval record001.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record001_leaves_nodup (j : Fin record001.l) : (record001.leaf j).Nodup :=
  record001.leaves_nodup_of_interval record001_leaf_0 j
theorem record001_checked (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 0 48 :=
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 0 32 48
  (record001_nodes_0 record001_valid)
  (record001_nodes_32 record001_valid))
theorem record001_raw_node_checks (record001_valid : GraphGrowthInputs.Valid record001.inputs) (i : Fin record001.t) :
    RawGraphConditionedGrowth.nodeCheck (record001.inputs.problem record001_valid)
      record001.maps record001.leaf record001.nodes i = true :=
  record001.node_checks_valid record001_valid record001_supports (record001_checked record001_valid) i
#print axioms record001_raw_node_checks
theorem record005_nodes_0 (record005_valid : GraphGrowthInputs.Valid record005.inputs) : Interval (record005.nodeTestValid record005_valid) 0 32 :=
  interval_of_check _ 0 32 (by decide_kernel_context)
theorem record005_nodes_32 (record005_valid : GraphGrowthInputs.Valid record005.inputs) : Interval (record005.nodeTestValid record005_valid) 32 46 :=
  interval_of_check _ 32 14 (by decide_kernel_context)
theorem record005_supports : record005.Supports := by unfold RawData.Supports; decide +kernel
theorem record005_leaf_0 : Interval record005.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record005_leaves_nodup (j : Fin record005.l) : (record005.leaf j).Nodup :=
  record005.leaves_nodup_of_interval record005_leaf_0 j
theorem record005_checked (record005_valid : GraphGrowthInputs.Valid record005.inputs) : Interval (record005.nodeTestValid record005_valid) 0 46 :=
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 0 32 46
  (record005_nodes_0 record005_valid)
  (record005_nodes_32 record005_valid))
theorem record005_raw_node_checks (record005_valid : GraphGrowthInputs.Valid record005.inputs) (i : Fin record005.t) :
    RawGraphConditionedGrowth.nodeCheck (record005.inputs.problem record005_valid)
      record005.maps record005.leaf record005.nodes i = true :=
  record005.node_checks_valid record005_valid record005_supports (record005_checked record005_valid) i
#print axioms record005_raw_node_checks
theorem record007_nodes_0 (record007_valid : GraphGrowthInputs.Valid record007.inputs) : Interval (record007.nodeTestValid record007_valid) 0 32 :=
  interval_of_check _ 0 32 (by decide_kernel_context)
theorem record007_nodes_32 (record007_valid : GraphGrowthInputs.Valid record007.inputs) : Interval (record007.nodeTestValid record007_valid) 32 64 :=
  interval_of_check _ 32 32 (by decide_kernel_context)
theorem record007_nodes_64 (record007_valid : GraphGrowthInputs.Valid record007.inputs) : Interval (record007.nodeTestValid record007_valid) 64 96 :=
  interval_of_check _ 64 32 (by decide_kernel_context)
theorem record007_nodes_96 (record007_valid : GraphGrowthInputs.Valid record007.inputs) : Interval (record007.nodeTestValid record007_valid) 96 128 :=
  interval_of_check _ 96 32 (by decide_kernel_context)
theorem record007_nodes_128 (record007_valid : GraphGrowthInputs.Valid record007.inputs) : Interval (record007.nodeTestValid record007_valid) 128 160 :=
  interval_of_check _ 128 32 (by decide_kernel_context)
theorem record007_nodes_160 (record007_valid : GraphGrowthInputs.Valid record007.inputs) : Interval (record007.nodeTestValid record007_valid) 160 192 :=
  interval_of_check _ 160 32 (by decide_kernel_context)
theorem record007_nodes_192 (record007_valid : GraphGrowthInputs.Valid record007.inputs) : Interval (record007.nodeTestValid record007_valid) 192 224 :=
  interval_of_check _ 192 32 (by decide_kernel_context)
theorem record007_nodes_224 (record007_valid : GraphGrowthInputs.Valid record007.inputs) : Interval (record007.nodeTestValid record007_valid) 224 256 :=
  interval_of_check _ 224 32 (by decide_kernel_context)
theorem record007_nodes_256 (record007_valid : GraphGrowthInputs.Valid record007.inputs) : Interval (record007.nodeTestValid record007_valid) 256 288 :=
  interval_of_check _ 256 32 (by decide_kernel_context)
theorem record007_nodes_288 (record007_valid : GraphGrowthInputs.Valid record007.inputs) : Interval (record007.nodeTestValid record007_valid) 288 320 :=
  interval_of_check _ 288 32 (by decide_kernel_context)
theorem record007_nodes_320 (record007_valid : GraphGrowthInputs.Valid record007.inputs) : Interval (record007.nodeTestValid record007_valid) 320 352 :=
  interval_of_check _ 320 32 (by decide_kernel_context)
theorem record007_nodes_352 (record007_valid : GraphGrowthInputs.Valid record007.inputs) : Interval (record007.nodeTestValid record007_valid) 352 367 :=
  interval_of_check _ 352 15 (by decide_kernel_context)
theorem record007_supports : record007.Supports := by unfold RawData.Supports; decide +kernel
theorem record007_leaf_0 : Interval record007.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record007_leaves_nodup (j : Fin record007.l) : (record007.leaf j).Nodup :=
  record007.leaves_nodup_of_interval record007_leaf_0 j
theorem record007_checked (record007_valid : GraphGrowthInputs.Valid record007.inputs) : Interval (record007.nodeTestValid record007_valid) 0 367 :=
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 0 192 367
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 0 96 192
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 0 32 96
  (record007_nodes_0 record007_valid)
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 32 64 96
  (record007_nodes_32 record007_valid)
  (record007_nodes_64 record007_valid)))
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 96 128 192
  (record007_nodes_96 record007_valid)
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 128 160 192
  (record007_nodes_128 record007_valid)
  (record007_nodes_160 record007_valid))))
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 192 288 367
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 192 224 288
  (record007_nodes_192 record007_valid)
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 224 256 288
  (record007_nodes_224 record007_valid)
  (record007_nodes_256 record007_valid)))
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 288 320 367
  (record007_nodes_288 record007_valid)
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 320 352 367
  (record007_nodes_320 record007_valid)
  (record007_nodes_352 record007_valid)))))
theorem record007_raw_node_checks (record007_valid : GraphGrowthInputs.Valid record007.inputs) (i : Fin record007.t) :
    RawGraphConditionedGrowth.nodeCheck (record007.inputs.problem record007_valid)
      record007.maps record007.leaf record007.nodes i = true :=
  record007.node_checks_valid record007_valid record007_supports (record007_checked record007_valid) i
#print axioms record007_raw_node_checks

end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00122
