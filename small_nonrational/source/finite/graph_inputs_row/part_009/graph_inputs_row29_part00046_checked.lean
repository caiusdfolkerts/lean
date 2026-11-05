module
prelude
public import GraphInputsRow29Part00046Data
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046
open Papers.RationalityTen PackedGraphCertificate FiniteChecks
theorem record000_nodes_0 (record000_valid : GraphGrowthInputs.Valid record000.inputs) : Interval (record000.nodeTestValid record000_valid) 0 32 :=
  interval_of_check _ 0 32 (by decide_kernel_context)
theorem record000_nodes_32 (record000_valid : GraphGrowthInputs.Valid record000.inputs) : Interval (record000.nodeTestValid record000_valid) 32 64 :=
  interval_of_check _ 32 32 (by decide_kernel_context)
theorem record000_nodes_64 (record000_valid : GraphGrowthInputs.Valid record000.inputs) : Interval (record000.nodeTestValid record000_valid) 64 96 :=
  interval_of_check _ 64 32 (by decide_kernel_context)
theorem record000_nodes_96 (record000_valid : GraphGrowthInputs.Valid record000.inputs) : Interval (record000.nodeTestValid record000_valid) 96 128 :=
  interval_of_check _ 96 32 (by decide_kernel_context)
theorem record000_nodes_128 (record000_valid : GraphGrowthInputs.Valid record000.inputs) : Interval (record000.nodeTestValid record000_valid) 128 160 :=
  interval_of_check _ 128 32 (by decide_kernel_context)
theorem record000_nodes_160 (record000_valid : GraphGrowthInputs.Valid record000.inputs) : Interval (record000.nodeTestValid record000_valid) 160 192 :=
  interval_of_check _ 160 32 (by decide_kernel_context)
theorem record000_nodes_192 (record000_valid : GraphGrowthInputs.Valid record000.inputs) : Interval (record000.nodeTestValid record000_valid) 192 201 :=
  interval_of_check _ 192 9 (by decide_kernel_context)
theorem record000_supports : record000.Supports := by unfold RawData.Supports; decide +kernel
theorem record000_leaf_0 : Interval record000.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record000_leaves_nodup (j : Fin record000.l) : (record000.leaf j).Nodup :=
  record000.leaves_nodup_of_interval record000_leaf_0 j
theorem record000_checked (record000_valid : GraphGrowthInputs.Valid record000.inputs) : Interval (record000.nodeTestValid record000_valid) 0 201 :=
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 0 96 201
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 0 32 96
  (record000_nodes_0 record000_valid)
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 32 64 96
  (record000_nodes_32 record000_valid)
  (record000_nodes_64 record000_valid)))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 96 160 201
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 96 128 160
  (record000_nodes_96 record000_valid)
  (record000_nodes_128 record000_valid))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 160 192 201
  (record000_nodes_160 record000_valid)
  (record000_nodes_192 record000_valid))))
theorem record000_raw_node_checks (record000_valid : GraphGrowthInputs.Valid record000.inputs) (i : Fin record000.t) :
    RawGraphConditionedGrowth.nodeCheck (record000.inputs.problem record000_valid)
      record000.maps record000.leaf record000.nodes i = true :=
  record000.node_checks_valid record000_valid record000_supports (record000_checked record000_valid) i
#print axioms record000_raw_node_checks
theorem record001_nodes_0 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 0 17 :=
  interval_of_check _ 0 17 (by decide_kernel_context)
theorem record001_supports : record001.Supports := by unfold RawData.Supports; decide +kernel
theorem record001_leaf_0 : Interval record001.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record001_leaves_nodup (j : Fin record001.l) : (record001.leaf j).Nodup :=
  record001.leaves_nodup_of_interval record001_leaf_0 j
theorem record001_checked (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 0 17 :=
  (record001_nodes_0 record001_valid)
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
theorem record002_nodes_224 (record002_valid : GraphGrowthInputs.Valid record002.inputs) : Interval (record002.nodeTestValid record002_valid) 224 256 :=
  interval_of_check _ 224 32 (by decide_kernel_context)
theorem record002_nodes_256 (record002_valid : GraphGrowthInputs.Valid record002.inputs) : Interval (record002.nodeTestValid record002_valid) 256 288 :=
  interval_of_check _ 256 32 (by decide_kernel_context)
theorem record002_nodes_288 (record002_valid : GraphGrowthInputs.Valid record002.inputs) : Interval (record002.nodeTestValid record002_valid) 288 320 :=
  interval_of_check _ 288 32 (by decide_kernel_context)
theorem record002_nodes_320 (record002_valid : GraphGrowthInputs.Valid record002.inputs) : Interval (record002.nodeTestValid record002_valid) 320 352 :=
  interval_of_check _ 320 32 (by decide_kernel_context)
theorem record002_nodes_352 (record002_valid : GraphGrowthInputs.Valid record002.inputs) : Interval (record002.nodeTestValid record002_valid) 352 384 :=
  interval_of_check _ 352 32 (by decide_kernel_context)
theorem record002_nodes_384 (record002_valid : GraphGrowthInputs.Valid record002.inputs) : Interval (record002.nodeTestValid record002_valid) 384 416 :=
  interval_of_check _ 384 32 (by decide_kernel_context)
theorem record002_nodes_416 (record002_valid : GraphGrowthInputs.Valid record002.inputs) : Interval (record002.nodeTestValid record002_valid) 416 446 :=
  interval_of_check _ 416 30 (by decide_kernel_context)
theorem record002_supports : record002.Supports := by unfold RawData.Supports; decide +kernel
theorem record002_leaf_0 : Interval record002.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record002_leaves_nodup (j : Fin record002.l) : (record002.leaf j).Nodup :=
  record002.leaves_nodup_of_interval record002_leaf_0 j
theorem record002_checked (record002_valid : GraphGrowthInputs.Valid record002.inputs) : Interval (record002.nodeTestValid record002_valid) 0 446 :=
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 0 224 446
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 0 96 224
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 0 32 96
  (record002_nodes_0 record002_valid)
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 32 64 96
  (record002_nodes_32 record002_valid)
  (record002_nodes_64 record002_valid)))
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 96 160 224
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 96 128 160
  (record002_nodes_96 record002_valid)
  (record002_nodes_128 record002_valid))
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 160 192 224
  (record002_nodes_160 record002_valid)
  (record002_nodes_192 record002_valid))))
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 224 320 446
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 224 256 320
  (record002_nodes_224 record002_valid)
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 256 288 320
  (record002_nodes_256 record002_valid)
  (record002_nodes_288 record002_valid)))
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 320 384 446
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 320 352 384
  (record002_nodes_320 record002_valid)
  (record002_nodes_352 record002_valid))
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 384 416 446
  (record002_nodes_384 record002_valid)
  (record002_nodes_416 record002_valid)))))
theorem record002_raw_node_checks (record002_valid : GraphGrowthInputs.Valid record002.inputs) (i : Fin record002.t) :
    RawGraphConditionedGrowth.nodeCheck (record002.inputs.problem record002_valid)
      record002.maps record002.leaf record002.nodes i = true :=
  record002.node_checks_valid record002_valid record002_supports (record002_checked record002_valid) i
#print axioms record002_raw_node_checks
theorem record003_nodes_0 (record003_valid : GraphGrowthInputs.Valid record003.inputs) : Interval (record003.nodeTestValid record003_valid) 0 32 :=
  interval_of_check _ 0 32 (by decide_kernel_context)
theorem record003_nodes_32 (record003_valid : GraphGrowthInputs.Valid record003.inputs) : Interval (record003.nodeTestValid record003_valid) 32 64 :=
  interval_of_check _ 32 32 (by decide_kernel_context)
theorem record003_nodes_64 (record003_valid : GraphGrowthInputs.Valid record003.inputs) : Interval (record003.nodeTestValid record003_valid) 64 82 :=
  interval_of_check _ 64 18 (by decide_kernel_context)
theorem record003_supports : record003.Supports := by unfold RawData.Supports; decide +kernel
theorem record003_leaf_0 : Interval record003.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record003_leaves_nodup (j : Fin record003.l) : (record003.leaf j).Nodup :=
  record003.leaves_nodup_of_interval record003_leaf_0 j
theorem record003_checked (record003_valid : GraphGrowthInputs.Valid record003.inputs) : Interval (record003.nodeTestValid record003_valid) 0 82 :=
  (FiniteChecks.interval_append (record003.nodeTestValid record003_valid) 0 32 82
  (record003_nodes_0 record003_valid)
  (FiniteChecks.interval_append (record003.nodeTestValid record003_valid) 32 64 82
  (record003_nodes_32 record003_valid)
  (record003_nodes_64 record003_valid)))
theorem record003_raw_node_checks (record003_valid : GraphGrowthInputs.Valid record003.inputs) (i : Fin record003.t) :
    RawGraphConditionedGrowth.nodeCheck (record003.inputs.problem record003_valid)
      record003.maps record003.leaf record003.nodes i = true :=
  record003.node_checks_valid record003_valid record003_supports (record003_checked record003_valid) i
#print axioms record003_raw_node_checks
theorem record004_nodes_0 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 0 32 :=
  interval_of_check _ 0 32 (by decide_kernel_context)
theorem record004_nodes_32 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 32 64 :=
  interval_of_check _ 32 32 (by decide_kernel_context)
theorem record004_nodes_64 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 64 73 :=
  interval_of_check _ 64 9 (by decide_kernel_context)
theorem record004_supports : record004.Supports := by unfold RawData.Supports; decide +kernel
theorem record004_leaf_0 : Interval record004.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record004_leaves_nodup (j : Fin record004.l) : (record004.leaf j).Nodup :=
  record004.leaves_nodup_of_interval record004_leaf_0 j
theorem record004_checked (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 0 73 :=
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 0 32 73
  (record004_nodes_0 record004_valid)
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 32 64 73
  (record004_nodes_32 record004_valid)
  (record004_nodes_64 record004_valid)))
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
theorem record005_nodes_224 (record005_valid : GraphGrowthInputs.Valid record005.inputs) : Interval (record005.nodeTestValid record005_valid) 224 237 :=
  interval_of_check _ 224 13 (by decide_kernel_context)
theorem record005_supports : record005.Supports := by unfold RawData.Supports; decide +kernel
theorem record005_leaf_0 : Interval record005.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record005_leaves_nodup (j : Fin record005.l) : (record005.leaf j).Nodup :=
  record005.leaves_nodup_of_interval record005_leaf_0 j
theorem record005_checked (record005_valid : GraphGrowthInputs.Valid record005.inputs) : Interval (record005.nodeTestValid record005_valid) 0 237 :=
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 0 128 237
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 0 64 128
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 0 32 64
  (record005_nodes_0 record005_valid)
  (record005_nodes_32 record005_valid))
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 64 96 128
  (record005_nodes_64 record005_valid)
  (record005_nodes_96 record005_valid)))
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 128 192 237
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 128 160 192
  (record005_nodes_128 record005_valid)
  (record005_nodes_160 record005_valid))
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 192 224 237
  (record005_nodes_192 record005_valid)
  (record005_nodes_224 record005_valid))))
theorem record005_raw_node_checks (record005_valid : GraphGrowthInputs.Valid record005.inputs) (i : Fin record005.t) :
    RawGraphConditionedGrowth.nodeCheck (record005.inputs.problem record005_valid)
      record005.maps record005.leaf record005.nodes i = true :=
  record005.node_checks_valid record005_valid record005_supports (record005_checked record005_valid) i
#print axioms record005_raw_node_checks
theorem record006_nodes_0 (record006_valid : GraphGrowthInputs.Valid record006.inputs) : Interval (record006.nodeTestValid record006_valid) 0 32 :=
  interval_of_check _ 0 32 (by decide_kernel_context)
theorem record006_nodes_32 (record006_valid : GraphGrowthInputs.Valid record006.inputs) : Interval (record006.nodeTestValid record006_valid) 32 53 :=
  interval_of_check _ 32 21 (by decide_kernel_context)
theorem record006_supports : record006.Supports := by unfold RawData.Supports; decide +kernel
theorem record006_leaf_0 : Interval record006.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record006_leaves_nodup (j : Fin record006.l) : (record006.leaf j).Nodup :=
  record006.leaves_nodup_of_interval record006_leaf_0 j
theorem record006_checked (record006_valid : GraphGrowthInputs.Valid record006.inputs) : Interval (record006.nodeTestValid record006_valid) 0 53 :=
  (FiniteChecks.interval_append (record006.nodeTestValid record006_valid) 0 32 53
  (record006_nodes_0 record006_valid)
  (record006_nodes_32 record006_valid))
theorem record006_raw_node_checks (record006_valid : GraphGrowthInputs.Valid record006.inputs) (i : Fin record006.t) :
    RawGraphConditionedGrowth.nodeCheck (record006.inputs.problem record006_valid)
      record006.maps record006.leaf record006.nodes i = true :=
  record006.node_checks_valid record006_valid record006_supports (record006_checked record006_valid) i
#print axioms record006_raw_node_checks
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
theorem record007_nodes_352 (record007_valid : GraphGrowthInputs.Valid record007.inputs) : Interval (record007.nodeTestValid record007_valid) 352 384 :=
  interval_of_check _ 352 32 (by decide_kernel_context)
theorem record007_nodes_384 (record007_valid : GraphGrowthInputs.Valid record007.inputs) : Interval (record007.nodeTestValid record007_valid) 384 416 :=
  interval_of_check _ 384 32 (by decide_kernel_context)
theorem record007_nodes_416 (record007_valid : GraphGrowthInputs.Valid record007.inputs) : Interval (record007.nodeTestValid record007_valid) 416 448 :=
  interval_of_check _ 416 32 (by decide_kernel_context)
theorem record007_nodes_448 (record007_valid : GraphGrowthInputs.Valid record007.inputs) : Interval (record007.nodeTestValid record007_valid) 448 480 :=
  interval_of_check _ 448 32 (by decide_kernel_context)
theorem record007_nodes_480 (record007_valid : GraphGrowthInputs.Valid record007.inputs) : Interval (record007.nodeTestValid record007_valid) 480 512 :=
  interval_of_check _ 480 32 (by decide_kernel_context)
theorem record007_nodes_512 (record007_valid : GraphGrowthInputs.Valid record007.inputs) : Interval (record007.nodeTestValid record007_valid) 512 544 :=
  interval_of_check _ 512 32 (by decide_kernel_context)
theorem record007_nodes_544 (record007_valid : GraphGrowthInputs.Valid record007.inputs) : Interval (record007.nodeTestValid record007_valid) 544 576 :=
  interval_of_check _ 544 32 (by decide_kernel_context)
theorem record007_nodes_576 (record007_valid : GraphGrowthInputs.Valid record007.inputs) : Interval (record007.nodeTestValid record007_valid) 576 608 :=
  interval_of_check _ 576 32 (by decide_kernel_context)
theorem record007_nodes_608 (record007_valid : GraphGrowthInputs.Valid record007.inputs) : Interval (record007.nodeTestValid record007_valid) 608 622 :=
  interval_of_check _ 608 14 (by decide_kernel_context)
theorem record007_supports : record007.Supports := by unfold RawData.Supports; decide +kernel
theorem record007_leaf_0 : Interval record007.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record007_leaves_nodup (j : Fin record007.l) : (record007.leaf j).Nodup :=
  record007.leaves_nodup_of_interval record007_leaf_0 j
theorem record007_checked (record007_valid : GraphGrowthInputs.Valid record007.inputs) : Interval (record007.nodeTestValid record007_valid) 0 622 :=
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 0 320 622
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 0 160 320
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 0 64 160
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 0 32 64
  (record007_nodes_0 record007_valid)
  (record007_nodes_32 record007_valid))
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 64 96 160
  (record007_nodes_64 record007_valid)
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 96 128 160
  (record007_nodes_96 record007_valid)
  (record007_nodes_128 record007_valid))))
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 160 224 320
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 160 192 224
  (record007_nodes_160 record007_valid)
  (record007_nodes_192 record007_valid))
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 224 256 320
  (record007_nodes_224 record007_valid)
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 256 288 320
  (record007_nodes_256 record007_valid)
  (record007_nodes_288 record007_valid)))))
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 320 480 622
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 320 384 480
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 320 352 384
  (record007_nodes_320 record007_valid)
  (record007_nodes_352 record007_valid))
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 384 416 480
  (record007_nodes_384 record007_valid)
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 416 448 480
  (record007_nodes_416 record007_valid)
  (record007_nodes_448 record007_valid))))
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 480 544 622
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 480 512 544
  (record007_nodes_480 record007_valid)
  (record007_nodes_512 record007_valid))
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 544 576 622
  (record007_nodes_544 record007_valid)
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 576 608 622
  (record007_nodes_576 record007_valid)
  (record007_nodes_608 record007_valid))))))
theorem record007_raw_node_checks (record007_valid : GraphGrowthInputs.Valid record007.inputs) (i : Fin record007.t) :
    RawGraphConditionedGrowth.nodeCheck (record007.inputs.problem record007_valid)
      record007.maps record007.leaf record007.nodes i = true :=
  record007.node_checks_valid record007_valid record007_supports (record007_checked record007_valid) i
#print axioms record007_raw_node_checks

end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046
