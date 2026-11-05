module
prelude
public import GraphInputsRow31Part00104Data
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00104
open Papers.RationalityTen PackedGraphCertificate FiniteChecks
theorem record000_nodes_0 (record000_valid : GraphGrowthInputs.Valid record000.inputs) : Interval (record000.nodeTestValid record000_valid) 0 6 :=
  interval_of_check _ 0 6 (by decide_kernel_context)
theorem record000_supports : record000.Supports := by unfold RawData.Supports; decide +kernel
theorem record000_leaf_0 : Interval record000.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record000_leaves_nodup (j : Fin record000.l) : (record000.leaf j).Nodup :=
  record000.leaves_nodup_of_interval record000_leaf_0 j
theorem record000_checked (record000_valid : GraphGrowthInputs.Valid record000.inputs) : Interval (record000.nodeTestValid record000_valid) 0 6 :=
  (record000_nodes_0 record000_valid)
theorem record000_raw_node_checks (record000_valid : GraphGrowthInputs.Valid record000.inputs) (i : Fin record000.t) :
    RawGraphConditionedGrowth.nodeCheck (record000.inputs.problem record000_valid)
      record000.maps record000.leaf record000.nodes i = true :=
  record000.node_checks_valid record000_valid record000_supports (record000_checked record000_valid) i
#print axioms record000_raw_node_checks
theorem record001_nodes_0 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 0 32 :=
  interval_of_check _ 0 32 (by decide_kernel_context)
theorem record001_nodes_32 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 32 64 :=
  interval_of_check _ 32 32 (by decide_kernel_context)
theorem record001_nodes_64 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 64 96 :=
  interval_of_check _ 64 32 (by decide_kernel_context)
theorem record001_nodes_96 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 96 128 :=
  interval_of_check _ 96 32 (by decide_kernel_context)
theorem record001_nodes_128 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 128 160 :=
  interval_of_check _ 128 32 (by decide_kernel_context)
theorem record001_nodes_160 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 160 192 :=
  interval_of_check _ 160 32 (by decide_kernel_context)
theorem record001_nodes_192 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 192 224 :=
  interval_of_check _ 192 32 (by decide_kernel_context)
theorem record001_nodes_224 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 224 256 :=
  interval_of_check _ 224 32 (by decide_kernel_context)
theorem record001_nodes_256 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 256 288 :=
  interval_of_check _ 256 32 (by decide_kernel_context)
theorem record001_supports : record001.Supports := by unfold RawData.Supports; decide +kernel
theorem record001_leaf_0 : Interval record001.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record001_leaves_nodup (j : Fin record001.l) : (record001.leaf j).Nodup :=
  record001.leaves_nodup_of_interval record001_leaf_0 j
theorem record001_checked (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 0 288 :=
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 0 128 288
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 0 64 128
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 0 32 64
  (record001_nodes_0 record001_valid)
  (record001_nodes_32 record001_valid))
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 64 96 128
  (record001_nodes_64 record001_valid)
  (record001_nodes_96 record001_valid)))
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 128 192 288
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 128 160 192
  (record001_nodes_128 record001_valid)
  (record001_nodes_160 record001_valid))
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 192 224 288
  (record001_nodes_192 record001_valid)
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 224 256 288
  (record001_nodes_224 record001_valid)
  (record001_nodes_256 record001_valid)))))
theorem record001_raw_node_checks (record001_valid : GraphGrowthInputs.Valid record001.inputs) (i : Fin record001.t) :
    RawGraphConditionedGrowth.nodeCheck (record001.inputs.problem record001_valid)
      record001.maps record001.leaf record001.nodes i = true :=
  record001.node_checks_valid record001_valid record001_supports (record001_checked record001_valid) i
#print axioms record001_raw_node_checks
theorem record002_nodes_0 (record002_valid : GraphGrowthInputs.Valid record002.inputs) : Interval (record002.nodeTestValid record002_valid) 0 32 :=
  interval_of_check _ 0 32 (by decide_kernel_context)
theorem record002_nodes_32 (record002_valid : GraphGrowthInputs.Valid record002.inputs) : Interval (record002.nodeTestValid record002_valid) 32 64 :=
  interval_of_check _ 32 32 (by decide_kernel_context)
theorem record002_nodes_64 (record002_valid : GraphGrowthInputs.Valid record002.inputs) : Interval (record002.nodeTestValid record002_valid) 64 96 :=
  interval_of_check _ 64 32 (by decide_kernel_context)
theorem record002_nodes_96 (record002_valid : GraphGrowthInputs.Valid record002.inputs) : Interval (record002.nodeTestValid record002_valid) 96 128 :=
  interval_of_check _ 96 32 (by decide_kernel_context)
theorem record002_nodes_128 (record002_valid : GraphGrowthInputs.Valid record002.inputs) : Interval (record002.nodeTestValid record002_valid) 128 160 :=
  interval_of_check _ 128 32 (by decide_kernel_context)
theorem record002_nodes_160 (record002_valid : GraphGrowthInputs.Valid record002.inputs) : Interval (record002.nodeTestValid record002_valid) 160 192 :=
  interval_of_check _ 160 32 (by decide_kernel_context)
theorem record002_nodes_192 (record002_valid : GraphGrowthInputs.Valid record002.inputs) : Interval (record002.nodeTestValid record002_valid) 192 224 :=
  interval_of_check _ 192 32 (by decide_kernel_context)
theorem record002_nodes_224 (record002_valid : GraphGrowthInputs.Valid record002.inputs) : Interval (record002.nodeTestValid record002_valid) 224 242 :=
  interval_of_check _ 224 18 (by decide_kernel_context)
theorem record002_supports : record002.Supports := by unfold RawData.Supports; decide +kernel
theorem record002_leaf_0 : Interval record002.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record002_leaves_nodup (j : Fin record002.l) : (record002.leaf j).Nodup :=
  record002.leaves_nodup_of_interval record002_leaf_0 j
theorem record002_checked (record002_valid : GraphGrowthInputs.Valid record002.inputs) : Interval (record002.nodeTestValid record002_valid) 0 242 :=
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 0 128 242
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 0 64 128
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 0 32 64
  (record002_nodes_0 record002_valid)
  (record002_nodes_32 record002_valid))
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 64 96 128
  (record002_nodes_64 record002_valid)
  (record002_nodes_96 record002_valid)))
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 128 192 242
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 128 160 192
  (record002_nodes_128 record002_valid)
  (record002_nodes_160 record002_valid))
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 192 224 242
  (record002_nodes_192 record002_valid)
  (record002_nodes_224 record002_valid))))
theorem record002_raw_node_checks (record002_valid : GraphGrowthInputs.Valid record002.inputs) (i : Fin record002.t) :
    RawGraphConditionedGrowth.nodeCheck (record002.inputs.problem record002_valid)
      record002.maps record002.leaf record002.nodes i = true :=
  record002.node_checks_valid record002_valid record002_supports (record002_checked record002_valid) i
#print axioms record002_raw_node_checks
theorem record003_nodes_0 (record003_valid : GraphGrowthInputs.Valid record003.inputs) : Interval (record003.nodeTestValid record003_valid) 0 32 :=
  interval_of_check _ 0 32 (by decide_kernel_context)
theorem record003_nodes_32 (record003_valid : GraphGrowthInputs.Valid record003.inputs) : Interval (record003.nodeTestValid record003_valid) 32 64 :=
  interval_of_check _ 32 32 (by decide_kernel_context)
theorem record003_nodes_64 (record003_valid : GraphGrowthInputs.Valid record003.inputs) : Interval (record003.nodeTestValid record003_valid) 64 96 :=
  interval_of_check _ 64 32 (by decide_kernel_context)
theorem record003_nodes_96 (record003_valid : GraphGrowthInputs.Valid record003.inputs) : Interval (record003.nodeTestValid record003_valid) 96 128 :=
  interval_of_check _ 96 32 (by decide_kernel_context)
theorem record003_nodes_128 (record003_valid : GraphGrowthInputs.Valid record003.inputs) : Interval (record003.nodeTestValid record003_valid) 128 160 :=
  interval_of_check _ 128 32 (by decide_kernel_context)
theorem record003_nodes_160 (record003_valid : GraphGrowthInputs.Valid record003.inputs) : Interval (record003.nodeTestValid record003_valid) 160 192 :=
  interval_of_check _ 160 32 (by decide_kernel_context)
theorem record003_nodes_192 (record003_valid : GraphGrowthInputs.Valid record003.inputs) : Interval (record003.nodeTestValid record003_valid) 192 224 :=
  interval_of_check _ 192 32 (by decide_kernel_context)
theorem record003_nodes_224 (record003_valid : GraphGrowthInputs.Valid record003.inputs) : Interval (record003.nodeTestValid record003_valid) 224 256 :=
  interval_of_check _ 224 32 (by decide_kernel_context)
theorem record003_nodes_256 (record003_valid : GraphGrowthInputs.Valid record003.inputs) : Interval (record003.nodeTestValid record003_valid) 256 288 :=
  interval_of_check _ 256 32 (by decide_kernel_context)
theorem record003_nodes_288 (record003_valid : GraphGrowthInputs.Valid record003.inputs) : Interval (record003.nodeTestValid record003_valid) 288 320 :=
  interval_of_check _ 288 32 (by decide_kernel_context)
theorem record003_nodes_320 (record003_valid : GraphGrowthInputs.Valid record003.inputs) : Interval (record003.nodeTestValid record003_valid) 320 352 :=
  interval_of_check _ 320 32 (by decide_kernel_context)
theorem record003_nodes_352 (record003_valid : GraphGrowthInputs.Valid record003.inputs) : Interval (record003.nodeTestValid record003_valid) 352 384 :=
  interval_of_check _ 352 32 (by decide_kernel_context)
theorem record003_nodes_384 (record003_valid : GraphGrowthInputs.Valid record003.inputs) : Interval (record003.nodeTestValid record003_valid) 384 386 :=
  interval_of_check _ 384 2 (by decide_kernel_context)
theorem record003_supports : record003.Supports := by unfold RawData.Supports; decide +kernel
theorem record003_leaf_0 : Interval record003.leafTest 0 8 :=
  interval_of_check _ 0 8 (by decide +kernel)
theorem record003_leaf_8 : Interval record003.leafTest 8 16 :=
  interval_of_check _ 8 8 (by decide +kernel)
theorem record003_leaf_16 : Interval record003.leafTest 16 17 :=
  interval_of_check _ 16 1 (by decide +kernel)
theorem record003_leaves_nodup (j : Fin record003.l) : (record003.leaf j).Nodup :=
  record003.leaves_nodup_of_interval (FiniteChecks.interval_append record003.leafTest 0 8 17
  record003_leaf_0
  (FiniteChecks.interval_append record003.leafTest 8 16 17
  record003_leaf_8
  record003_leaf_16)) j
theorem record003_checked (record003_valid : GraphGrowthInputs.Valid record003.inputs) : Interval (record003.nodeTestValid record003_valid) 0 386 :=
  (FiniteChecks.interval_append (record003.nodeTestValid record003_valid) 0 192 386
  (FiniteChecks.interval_append (record003.nodeTestValid record003_valid) 0 96 192
  (FiniteChecks.interval_append (record003.nodeTestValid record003_valid) 0 32 96
  (record003_nodes_0 record003_valid)
  (FiniteChecks.interval_append (record003.nodeTestValid record003_valid) 32 64 96
  (record003_nodes_32 record003_valid)
  (record003_nodes_64 record003_valid)))
  (FiniteChecks.interval_append (record003.nodeTestValid record003_valid) 96 128 192
  (record003_nodes_96 record003_valid)
  (FiniteChecks.interval_append (record003.nodeTestValid record003_valid) 128 160 192
  (record003_nodes_128 record003_valid)
  (record003_nodes_160 record003_valid))))
  (FiniteChecks.interval_append (record003.nodeTestValid record003_valid) 192 288 386
  (FiniteChecks.interval_append (record003.nodeTestValid record003_valid) 192 224 288
  (record003_nodes_192 record003_valid)
  (FiniteChecks.interval_append (record003.nodeTestValid record003_valid) 224 256 288
  (record003_nodes_224 record003_valid)
  (record003_nodes_256 record003_valid)))
  (FiniteChecks.interval_append (record003.nodeTestValid record003_valid) 288 352 386
  (FiniteChecks.interval_append (record003.nodeTestValid record003_valid) 288 320 352
  (record003_nodes_288 record003_valid)
  (record003_nodes_320 record003_valid))
  (FiniteChecks.interval_append (record003.nodeTestValid record003_valid) 352 384 386
  (record003_nodes_352 record003_valid)
  (record003_nodes_384 record003_valid)))))
theorem record003_raw_node_checks (record003_valid : GraphGrowthInputs.Valid record003.inputs) (i : Fin record003.t) :
    RawGraphConditionedGrowth.nodeCheck (record003.inputs.problem record003_valid)
      record003.maps record003.leaf record003.nodes i = true :=
  record003.node_checks_valid record003_valid record003_supports (record003_checked record003_valid) i
#print axioms record003_raw_node_checks
theorem record004_nodes_0 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 0 32 :=
  interval_of_check _ 0 32 (by decide_kernel_context)
theorem record004_nodes_32 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 32 64 :=
  interval_of_check _ 32 32 (by decide_kernel_context)
theorem record004_nodes_64 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 64 96 :=
  interval_of_check _ 64 32 (by decide_kernel_context)
theorem record004_nodes_96 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 96 128 :=
  interval_of_check _ 96 32 (by decide_kernel_context)
theorem record004_nodes_128 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 128 160 :=
  interval_of_check _ 128 32 (by decide_kernel_context)
theorem record004_nodes_160 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 160 192 :=
  interval_of_check _ 160 32 (by decide_kernel_context)
theorem record004_nodes_192 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 192 224 :=
  interval_of_check _ 192 32 (by decide_kernel_context)
theorem record004_nodes_224 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 224 245 :=
  interval_of_check _ 224 21 (by decide_kernel_context)
theorem record004_supports : record004.Supports := by unfold RawData.Supports; decide +kernel
theorem record004_leaf_0 : Interval record004.leafTest 0 6 :=
  interval_of_check _ 0 6 (by decide +kernel)
theorem record004_leaves_nodup (j : Fin record004.l) : (record004.leaf j).Nodup :=
  record004.leaves_nodup_of_interval record004_leaf_0 j
theorem record004_checked (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 0 245 :=
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 0 128 245
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 0 64 128
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 0 32 64
  (record004_nodes_0 record004_valid)
  (record004_nodes_32 record004_valid))
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 64 96 128
  (record004_nodes_64 record004_valid)
  (record004_nodes_96 record004_valid)))
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 128 192 245
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 128 160 192
  (record004_nodes_128 record004_valid)
  (record004_nodes_160 record004_valid))
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 192 224 245
  (record004_nodes_192 record004_valid)
  (record004_nodes_224 record004_valid))))
theorem record004_raw_node_checks (record004_valid : GraphGrowthInputs.Valid record004.inputs) (i : Fin record004.t) :
    RawGraphConditionedGrowth.nodeCheck (record004.inputs.problem record004_valid)
      record004.maps record004.leaf record004.nodes i = true :=
  record004.node_checks_valid record004_valid record004_supports (record004_checked record004_valid) i
#print axioms record004_raw_node_checks
theorem record005_nodes_0 (record005_valid : GraphGrowthInputs.Valid record005.inputs) : Interval (record005.nodeTestValid record005_valid) 0 32 :=
  interval_of_check _ 0 32 (by decide_kernel_context)
theorem record005_nodes_32 (record005_valid : GraphGrowthInputs.Valid record005.inputs) : Interval (record005.nodeTestValid record005_valid) 32 64 :=
  interval_of_check _ 32 32 (by decide_kernel_context)
theorem record005_nodes_64 (record005_valid : GraphGrowthInputs.Valid record005.inputs) : Interval (record005.nodeTestValid record005_valid) 64 96 :=
  interval_of_check _ 64 32 (by decide_kernel_context)
theorem record005_nodes_96 (record005_valid : GraphGrowthInputs.Valid record005.inputs) : Interval (record005.nodeTestValid record005_valid) 96 128 :=
  interval_of_check _ 96 32 (by decide_kernel_context)
theorem record005_nodes_128 (record005_valid : GraphGrowthInputs.Valid record005.inputs) : Interval (record005.nodeTestValid record005_valid) 128 160 :=
  interval_of_check _ 128 32 (by decide_kernel_context)
theorem record005_nodes_160 (record005_valid : GraphGrowthInputs.Valid record005.inputs) : Interval (record005.nodeTestValid record005_valid) 160 192 :=
  interval_of_check _ 160 32 (by decide_kernel_context)
theorem record005_nodes_192 (record005_valid : GraphGrowthInputs.Valid record005.inputs) : Interval (record005.nodeTestValid record005_valid) 192 224 :=
  interval_of_check _ 192 32 (by decide_kernel_context)
theorem record005_nodes_224 (record005_valid : GraphGrowthInputs.Valid record005.inputs) : Interval (record005.nodeTestValid record005_valid) 224 256 :=
  interval_of_check _ 224 32 (by decide_kernel_context)
theorem record005_nodes_256 (record005_valid : GraphGrowthInputs.Valid record005.inputs) : Interval (record005.nodeTestValid record005_valid) 256 288 :=
  interval_of_check _ 256 32 (by decide_kernel_context)
theorem record005_nodes_288 (record005_valid : GraphGrowthInputs.Valid record005.inputs) : Interval (record005.nodeTestValid record005_valid) 288 320 :=
  interval_of_check _ 288 32 (by decide_kernel_context)
theorem record005_nodes_320 (record005_valid : GraphGrowthInputs.Valid record005.inputs) : Interval (record005.nodeTestValid record005_valid) 320 352 :=
  interval_of_check _ 320 32 (by decide_kernel_context)
theorem record005_nodes_352 (record005_valid : GraphGrowthInputs.Valid record005.inputs) : Interval (record005.nodeTestValid record005_valid) 352 361 :=
  interval_of_check _ 352 9 (by decide_kernel_context)
theorem record005_supports : record005.Supports := by unfold RawData.Supports; decide +kernel
theorem record005_leaf_0 : Interval record005.leafTest 0 4 :=
  interval_of_check _ 0 4 (by decide +kernel)
theorem record005_leaves_nodup (j : Fin record005.l) : (record005.leaf j).Nodup :=
  record005.leaves_nodup_of_interval record005_leaf_0 j
theorem record005_checked (record005_valid : GraphGrowthInputs.Valid record005.inputs) : Interval (record005.nodeTestValid record005_valid) 0 361 :=
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 0 192 361
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 0 96 192
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 0 32 96
  (record005_nodes_0 record005_valid)
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 32 64 96
  (record005_nodes_32 record005_valid)
  (record005_nodes_64 record005_valid)))
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 96 128 192
  (record005_nodes_96 record005_valid)
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 128 160 192
  (record005_nodes_128 record005_valid)
  (record005_nodes_160 record005_valid))))
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 192 288 361
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 192 224 288
  (record005_nodes_192 record005_valid)
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 224 256 288
  (record005_nodes_224 record005_valid)
  (record005_nodes_256 record005_valid)))
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 288 320 361
  (record005_nodes_288 record005_valid)
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 320 352 361
  (record005_nodes_320 record005_valid)
  (record005_nodes_352 record005_valid)))))
theorem record005_raw_node_checks (record005_valid : GraphGrowthInputs.Valid record005.inputs) (i : Fin record005.t) :
    RawGraphConditionedGrowth.nodeCheck (record005.inputs.problem record005_valid)
      record005.maps record005.leaf record005.nodes i = true :=
  record005.node_checks_valid record005_valid record005_supports (record005_checked record005_valid) i
#print axioms record005_raw_node_checks

end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00104
