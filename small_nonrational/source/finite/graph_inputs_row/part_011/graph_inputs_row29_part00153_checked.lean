module
prelude
public import GraphInputsRow29Part00153Data
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00153
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
theorem record000_nodes_192 (record000_valid : GraphGrowthInputs.Valid record000.inputs) : Interval (record000.nodeTestValid record000_valid) 192 224 :=
  interval_of_check _ 192 32 (by decide_kernel_context)
theorem record000_nodes_224 (record000_valid : GraphGrowthInputs.Valid record000.inputs) : Interval (record000.nodeTestValid record000_valid) 224 256 :=
  interval_of_check _ 224 32 (by decide_kernel_context)
theorem record000_nodes_256 (record000_valid : GraphGrowthInputs.Valid record000.inputs) : Interval (record000.nodeTestValid record000_valid) 256 288 :=
  interval_of_check _ 256 32 (by decide_kernel_context)
theorem record000_nodes_288 (record000_valid : GraphGrowthInputs.Valid record000.inputs) : Interval (record000.nodeTestValid record000_valid) 288 320 :=
  interval_of_check _ 288 32 (by decide_kernel_context)
theorem record000_nodes_320 (record000_valid : GraphGrowthInputs.Valid record000.inputs) : Interval (record000.nodeTestValid record000_valid) 320 352 :=
  interval_of_check _ 320 32 (by decide_kernel_context)
theorem record000_nodes_352 (record000_valid : GraphGrowthInputs.Valid record000.inputs) : Interval (record000.nodeTestValid record000_valid) 352 357 :=
  interval_of_check _ 352 5 (by decide_kernel_context)
theorem record000_supports : record000.Supports := by unfold RawData.Supports; decide +kernel
theorem record000_leaf_0 : Interval record000.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record000_leaves_nodup (j : Fin record000.l) : (record000.leaf j).Nodup :=
  record000.leaves_nodup_of_interval record000_leaf_0 j
theorem record000_checked (record000_valid : GraphGrowthInputs.Valid record000.inputs) : Interval (record000.nodeTestValid record000_valid) 0 357 :=
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 0 192 357
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 0 96 192
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 0 32 96
  (record000_nodes_0 record000_valid)
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 32 64 96
  (record000_nodes_32 record000_valid)
  (record000_nodes_64 record000_valid)))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 96 128 192
  (record000_nodes_96 record000_valid)
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 128 160 192
  (record000_nodes_128 record000_valid)
  (record000_nodes_160 record000_valid))))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 192 288 357
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 192 224 288
  (record000_nodes_192 record000_valid)
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 224 256 288
  (record000_nodes_224 record000_valid)
  (record000_nodes_256 record000_valid)))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 288 320 357
  (record000_nodes_288 record000_valid)
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 320 352 357
  (record000_nodes_320 record000_valid)
  (record000_nodes_352 record000_valid)))))
theorem record000_raw_node_checks (record000_valid : GraphGrowthInputs.Valid record000.inputs) (i : Fin record000.t) :
    RawGraphConditionedGrowth.nodeCheck (record000.inputs.problem record000_valid)
      record000.maps record000.leaf record000.nodes i = true :=
  record000.node_checks_valid record000_valid record000_supports (record000_checked record000_valid) i
#print axioms record000_raw_node_checks
theorem record001_nodes_0 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 0 16 :=
  interval_of_check _ 0 16 (by decide_kernel_context)
theorem record001_supports : record001.Supports := by unfold RawData.Supports; decide +kernel
theorem record001_leaf_0 : Interval record001.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record001_leaves_nodup (j : Fin record001.l) : (record001.leaf j).Nodup :=
  record001.leaves_nodup_of_interval record001_leaf_0 j
theorem record001_checked (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 0 16 :=
  (record001_nodes_0 record001_valid)
theorem record001_raw_node_checks (record001_valid : GraphGrowthInputs.Valid record001.inputs) (i : Fin record001.t) :
    RawGraphConditionedGrowth.nodeCheck (record001.inputs.problem record001_valid)
      record001.maps record001.leaf record001.nodes i = true :=
  record001.node_checks_valid record001_valid record001_supports (record001_checked record001_valid) i
#print axioms record001_raw_node_checks
theorem record002_nodes_0 (record002_valid : GraphGrowthInputs.Valid record002.inputs) : Interval (record002.nodeTestValid record002_valid) 0 19 :=
  interval_of_check _ 0 19 (by decide_kernel_context)
theorem record002_supports : record002.Supports := by unfold RawData.Supports; decide +kernel
theorem record002_leaf_0 : Interval record002.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record002_leaves_nodup (j : Fin record002.l) : (record002.leaf j).Nodup :=
  record002.leaves_nodup_of_interval record002_leaf_0 j
theorem record002_checked (record002_valid : GraphGrowthInputs.Valid record002.inputs) : Interval (record002.nodeTestValid record002_valid) 0 19 :=
  (record002_nodes_0 record002_valid)
theorem record002_raw_node_checks (record002_valid : GraphGrowthInputs.Valid record002.inputs) (i : Fin record002.t) :
    RawGraphConditionedGrowth.nodeCheck (record002.inputs.problem record002_valid)
      record002.maps record002.leaf record002.nodes i = true :=
  record002.node_checks_valid record002_valid record002_supports (record002_checked record002_valid) i
#print axioms record002_raw_node_checks
theorem record003_nodes_0 (record003_valid : GraphGrowthInputs.Valid record003.inputs) : Interval (record003.nodeTestValid record003_valid) 0 10 :=
  interval_of_check _ 0 10 (by decide_kernel_context)
theorem record003_supports : record003.Supports := by unfold RawData.Supports; decide +kernel
theorem record003_leaf_0 : Interval record003.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record003_leaves_nodup (j : Fin record003.l) : (record003.leaf j).Nodup :=
  record003.leaves_nodup_of_interval record003_leaf_0 j
theorem record003_checked (record003_valid : GraphGrowthInputs.Valid record003.inputs) : Interval (record003.nodeTestValid record003_valid) 0 10 :=
  (record003_nodes_0 record003_valid)
theorem record003_raw_node_checks (record003_valid : GraphGrowthInputs.Valid record003.inputs) (i : Fin record003.t) :
    RawGraphConditionedGrowth.nodeCheck (record003.inputs.problem record003_valid)
      record003.maps record003.leaf record003.nodes i = true :=
  record003.node_checks_valid record003_valid record003_supports (record003_checked record003_valid) i
#print axioms record003_raw_node_checks
theorem record004_nodes_0 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 0 32 :=
  interval_of_check _ 0 32 (by decide_kernel_context)
theorem record004_nodes_32 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 32 64 :=
  interval_of_check _ 32 32 (by decide_kernel_context)
theorem record004_nodes_64 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 64 93 :=
  interval_of_check _ 64 29 (by decide_kernel_context)
theorem record004_supports : record004.Supports := by unfold RawData.Supports; decide +kernel
theorem record004_leaf_0 : Interval record004.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record004_leaves_nodup (j : Fin record004.l) : (record004.leaf j).Nodup :=
  record004.leaves_nodup_of_interval record004_leaf_0 j
theorem record004_checked (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 0 93 :=
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 0 32 93
  (record004_nodes_0 record004_valid)
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 32 64 93
  (record004_nodes_32 record004_valid)
  (record004_nodes_64 record004_valid)))
theorem record004_raw_node_checks (record004_valid : GraphGrowthInputs.Valid record004.inputs) (i : Fin record004.t) :
    RawGraphConditionedGrowth.nodeCheck (record004.inputs.problem record004_valid)
      record004.maps record004.leaf record004.nodes i = true :=
  record004.node_checks_valid record004_valid record004_supports (record004_checked record004_valid) i
#print axioms record004_raw_node_checks
theorem record005_nodes_0 (record005_valid : GraphGrowthInputs.Valid record005.inputs) : Interval (record005.nodeTestValid record005_valid) 0 2 :=
  interval_of_check _ 0 2 (by decide_kernel_context)
theorem record005_supports : record005.Supports := by unfold RawData.Supports; decide +kernel
theorem record005_leaf_0 : Interval record005.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record005_leaves_nodup (j : Fin record005.l) : (record005.leaf j).Nodup :=
  record005.leaves_nodup_of_interval record005_leaf_0 j
theorem record005_checked (record005_valid : GraphGrowthInputs.Valid record005.inputs) : Interval (record005.nodeTestValid record005_valid) 0 2 :=
  (record005_nodes_0 record005_valid)
theorem record005_raw_node_checks (record005_valid : GraphGrowthInputs.Valid record005.inputs) (i : Fin record005.t) :
    RawGraphConditionedGrowth.nodeCheck (record005.inputs.problem record005_valid)
      record005.maps record005.leaf record005.nodes i = true :=
  record005.node_checks_valid record005_valid record005_supports (record005_checked record005_valid) i
#print axioms record005_raw_node_checks
theorem record006_nodes_0 (record006_valid : GraphGrowthInputs.Valid record006.inputs) : Interval (record006.nodeTestValid record006_valid) 0 32 :=
  interval_of_check _ 0 32 (by decide_kernel_context)
theorem record006_nodes_32 (record006_valid : GraphGrowthInputs.Valid record006.inputs) : Interval (record006.nodeTestValid record006_valid) 32 64 :=
  interval_of_check _ 32 32 (by decide_kernel_context)
theorem record006_nodes_64 (record006_valid : GraphGrowthInputs.Valid record006.inputs) : Interval (record006.nodeTestValid record006_valid) 64 96 :=
  interval_of_check _ 64 32 (by decide_kernel_context)
theorem record006_nodes_96 (record006_valid : GraphGrowthInputs.Valid record006.inputs) : Interval (record006.nodeTestValid record006_valid) 96 128 :=
  interval_of_check _ 96 32 (by decide_kernel_context)
theorem record006_nodes_128 (record006_valid : GraphGrowthInputs.Valid record006.inputs) : Interval (record006.nodeTestValid record006_valid) 128 160 :=
  interval_of_check _ 128 32 (by decide_kernel_context)
theorem record006_nodes_160 (record006_valid : GraphGrowthInputs.Valid record006.inputs) : Interval (record006.nodeTestValid record006_valid) 160 192 :=
  interval_of_check _ 160 32 (by decide_kernel_context)
theorem record006_nodes_192 (record006_valid : GraphGrowthInputs.Valid record006.inputs) : Interval (record006.nodeTestValid record006_valid) 192 224 :=
  interval_of_check _ 192 32 (by decide_kernel_context)
theorem record006_nodes_224 (record006_valid : GraphGrowthInputs.Valid record006.inputs) : Interval (record006.nodeTestValid record006_valid) 224 256 :=
  interval_of_check _ 224 32 (by decide_kernel_context)
theorem record006_nodes_256 (record006_valid : GraphGrowthInputs.Valid record006.inputs) : Interval (record006.nodeTestValid record006_valid) 256 288 :=
  interval_of_check _ 256 32 (by decide_kernel_context)
theorem record006_nodes_288 (record006_valid : GraphGrowthInputs.Valid record006.inputs) : Interval (record006.nodeTestValid record006_valid) 288 320 :=
  interval_of_check _ 288 32 (by decide_kernel_context)
theorem record006_nodes_320 (record006_valid : GraphGrowthInputs.Valid record006.inputs) : Interval (record006.nodeTestValid record006_valid) 320 352 :=
  interval_of_check _ 320 32 (by decide_kernel_context)
theorem record006_nodes_352 (record006_valid : GraphGrowthInputs.Valid record006.inputs) : Interval (record006.nodeTestValid record006_valid) 352 384 :=
  interval_of_check _ 352 32 (by decide_kernel_context)
theorem record006_nodes_384 (record006_valid : GraphGrowthInputs.Valid record006.inputs) : Interval (record006.nodeTestValid record006_valid) 384 412 :=
  interval_of_check _ 384 28 (by decide_kernel_context)
theorem record006_supports : record006.Supports := by unfold RawData.Supports; decide +kernel
theorem record006_leaf_0 : Interval record006.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record006_leaves_nodup (j : Fin record006.l) : (record006.leaf j).Nodup :=
  record006.leaves_nodup_of_interval record006_leaf_0 j
theorem record006_checked (record006_valid : GraphGrowthInputs.Valid record006.inputs) : Interval (record006.nodeTestValid record006_valid) 0 412 :=
  (FiniteChecks.interval_append (record006.nodeTestValid record006_valid) 0 192 412
  (FiniteChecks.interval_append (record006.nodeTestValid record006_valid) 0 96 192
  (FiniteChecks.interval_append (record006.nodeTestValid record006_valid) 0 32 96
  (record006_nodes_0 record006_valid)
  (FiniteChecks.interval_append (record006.nodeTestValid record006_valid) 32 64 96
  (record006_nodes_32 record006_valid)
  (record006_nodes_64 record006_valid)))
  (FiniteChecks.interval_append (record006.nodeTestValid record006_valid) 96 128 192
  (record006_nodes_96 record006_valid)
  (FiniteChecks.interval_append (record006.nodeTestValid record006_valid) 128 160 192
  (record006_nodes_128 record006_valid)
  (record006_nodes_160 record006_valid))))
  (FiniteChecks.interval_append (record006.nodeTestValid record006_valid) 192 288 412
  (FiniteChecks.interval_append (record006.nodeTestValid record006_valid) 192 224 288
  (record006_nodes_192 record006_valid)
  (FiniteChecks.interval_append (record006.nodeTestValid record006_valid) 224 256 288
  (record006_nodes_224 record006_valid)
  (record006_nodes_256 record006_valid)))
  (FiniteChecks.interval_append (record006.nodeTestValid record006_valid) 288 352 412
  (FiniteChecks.interval_append (record006.nodeTestValid record006_valid) 288 320 352
  (record006_nodes_288 record006_valid)
  (record006_nodes_320 record006_valid))
  (FiniteChecks.interval_append (record006.nodeTestValid record006_valid) 352 384 412
  (record006_nodes_352 record006_valid)
  (record006_nodes_384 record006_valid)))))
theorem record006_raw_node_checks (record006_valid : GraphGrowthInputs.Valid record006.inputs) (i : Fin record006.t) :
    RawGraphConditionedGrowth.nodeCheck (record006.inputs.problem record006_valid)
      record006.maps record006.leaf record006.nodes i = true :=
  record006.node_checks_valid record006_valid record006_supports (record006_checked record006_valid) i
#print axioms record006_raw_node_checks
theorem record007_nodes_0 (record007_valid : GraphGrowthInputs.Valid record007.inputs) : Interval (record007.nodeTestValid record007_valid) 0 32 :=
  interval_of_check _ 0 32 (by decide_kernel_context)
theorem record007_nodes_32 (record007_valid : GraphGrowthInputs.Valid record007.inputs) : Interval (record007.nodeTestValid record007_valid) 32 46 :=
  interval_of_check _ 32 14 (by decide_kernel_context)
theorem record007_supports : record007.Supports := by unfold RawData.Supports; decide +kernel
theorem record007_leaf_0 : Interval record007.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record007_leaves_nodup (j : Fin record007.l) : (record007.leaf j).Nodup :=
  record007.leaves_nodup_of_interval record007_leaf_0 j
theorem record007_checked (record007_valid : GraphGrowthInputs.Valid record007.inputs) : Interval (record007.nodeTestValid record007_valid) 0 46 :=
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 0 32 46
  (record007_nodes_0 record007_valid)
  (record007_nodes_32 record007_valid))
theorem record007_raw_node_checks (record007_valid : GraphGrowthInputs.Valid record007.inputs) (i : Fin record007.t) :
    RawGraphConditionedGrowth.nodeCheck (record007.inputs.problem record007_valid)
      record007.maps record007.leaf record007.nodes i = true :=
  record007.node_checks_valid record007_valid record007_supports (record007_checked record007_valid) i
#print axioms record007_raw_node_checks
theorem record008_nodes_0 (record008_valid : GraphGrowthInputs.Valid record008.inputs) : Interval (record008.nodeTestValid record008_valid) 0 32 :=
  interval_of_check _ 0 32 (by decide_kernel_context)
theorem record008_nodes_32 (record008_valid : GraphGrowthInputs.Valid record008.inputs) : Interval (record008.nodeTestValid record008_valid) 32 64 :=
  interval_of_check _ 32 32 (by decide_kernel_context)
theorem record008_nodes_64 (record008_valid : GraphGrowthInputs.Valid record008.inputs) : Interval (record008.nodeTestValid record008_valid) 64 96 :=
  interval_of_check _ 64 32 (by decide_kernel_context)
theorem record008_nodes_96 (record008_valid : GraphGrowthInputs.Valid record008.inputs) : Interval (record008.nodeTestValid record008_valid) 96 128 :=
  interval_of_check _ 96 32 (by decide_kernel_context)
theorem record008_nodes_128 (record008_valid : GraphGrowthInputs.Valid record008.inputs) : Interval (record008.nodeTestValid record008_valid) 128 160 :=
  interval_of_check _ 128 32 (by decide_kernel_context)
theorem record008_nodes_160 (record008_valid : GraphGrowthInputs.Valid record008.inputs) : Interval (record008.nodeTestValid record008_valid) 160 192 :=
  interval_of_check _ 160 32 (by decide_kernel_context)
theorem record008_nodes_192 (record008_valid : GraphGrowthInputs.Valid record008.inputs) : Interval (record008.nodeTestValid record008_valid) 192 224 :=
  interval_of_check _ 192 32 (by decide_kernel_context)
theorem record008_nodes_224 (record008_valid : GraphGrowthInputs.Valid record008.inputs) : Interval (record008.nodeTestValid record008_valid) 224 256 :=
  interval_of_check _ 224 32 (by decide_kernel_context)
theorem record008_nodes_256 (record008_valid : GraphGrowthInputs.Valid record008.inputs) : Interval (record008.nodeTestValid record008_valid) 256 288 :=
  interval_of_check _ 256 32 (by decide_kernel_context)
theorem record008_nodes_288 (record008_valid : GraphGrowthInputs.Valid record008.inputs) : Interval (record008.nodeTestValid record008_valid) 288 320 :=
  interval_of_check _ 288 32 (by decide_kernel_context)
theorem record008_nodes_320 (record008_valid : GraphGrowthInputs.Valid record008.inputs) : Interval (record008.nodeTestValid record008_valid) 320 352 :=
  interval_of_check _ 320 32 (by decide_kernel_context)
theorem record008_nodes_352 (record008_valid : GraphGrowthInputs.Valid record008.inputs) : Interval (record008.nodeTestValid record008_valid) 352 384 :=
  interval_of_check _ 352 32 (by decide_kernel_context)
theorem record008_nodes_384 (record008_valid : GraphGrowthInputs.Valid record008.inputs) : Interval (record008.nodeTestValid record008_valid) 384 416 :=
  interval_of_check _ 384 32 (by decide_kernel_context)
theorem record008_nodes_416 (record008_valid : GraphGrowthInputs.Valid record008.inputs) : Interval (record008.nodeTestValid record008_valid) 416 448 :=
  interval_of_check _ 416 32 (by decide_kernel_context)
theorem record008_nodes_448 (record008_valid : GraphGrowthInputs.Valid record008.inputs) : Interval (record008.nodeTestValid record008_valid) 448 480 :=
  interval_of_check _ 448 32 (by decide_kernel_context)
theorem record008_nodes_480 (record008_valid : GraphGrowthInputs.Valid record008.inputs) : Interval (record008.nodeTestValid record008_valid) 480 512 :=
  interval_of_check _ 480 32 (by decide_kernel_context)
theorem record008_nodes_512 (record008_valid : GraphGrowthInputs.Valid record008.inputs) : Interval (record008.nodeTestValid record008_valid) 512 544 :=
  interval_of_check _ 512 32 (by decide_kernel_context)
theorem record008_nodes_544 (record008_valid : GraphGrowthInputs.Valid record008.inputs) : Interval (record008.nodeTestValid record008_valid) 544 576 :=
  interval_of_check _ 544 32 (by decide_kernel_context)
theorem record008_nodes_576 (record008_valid : GraphGrowthInputs.Valid record008.inputs) : Interval (record008.nodeTestValid record008_valid) 576 608 :=
  interval_of_check _ 576 32 (by decide_kernel_context)
theorem record008_nodes_608 (record008_valid : GraphGrowthInputs.Valid record008.inputs) : Interval (record008.nodeTestValid record008_valid) 608 640 :=
  interval_of_check _ 608 32 (by decide_kernel_context)
theorem record008_nodes_640 (record008_valid : GraphGrowthInputs.Valid record008.inputs) : Interval (record008.nodeTestValid record008_valid) 640 642 :=
  interval_of_check _ 640 2 (by decide_kernel_context)
theorem record008_supports : record008.Supports := by unfold RawData.Supports; decide +kernel
theorem record008_leaf_0 : Interval record008.leafTest 0 8 :=
  interval_of_check _ 0 8 (by decide +kernel)
theorem record008_leaf_8 : Interval record008.leafTest 8 14 :=
  interval_of_check _ 8 6 (by decide +kernel)
theorem record008_leaves_nodup (j : Fin record008.l) : (record008.leaf j).Nodup :=
  record008.leaves_nodup_of_interval (FiniteChecks.interval_append record008.leafTest 0 8 14
  record008_leaf_0
  record008_leaf_8) j
theorem record008_checked (record008_valid : GraphGrowthInputs.Valid record008.inputs) : Interval (record008.nodeTestValid record008_valid) 0 642 :=
  (FiniteChecks.interval_append (record008.nodeTestValid record008_valid) 0 320 642
  (FiniteChecks.interval_append (record008.nodeTestValid record008_valid) 0 160 320
  (FiniteChecks.interval_append (record008.nodeTestValid record008_valid) 0 64 160
  (FiniteChecks.interval_append (record008.nodeTestValid record008_valid) 0 32 64
  (record008_nodes_0 record008_valid)
  (record008_nodes_32 record008_valid))
  (FiniteChecks.interval_append (record008.nodeTestValid record008_valid) 64 96 160
  (record008_nodes_64 record008_valid)
  (FiniteChecks.interval_append (record008.nodeTestValid record008_valid) 96 128 160
  (record008_nodes_96 record008_valid)
  (record008_nodes_128 record008_valid))))
  (FiniteChecks.interval_append (record008.nodeTestValid record008_valid) 160 224 320
  (FiniteChecks.interval_append (record008.nodeTestValid record008_valid) 160 192 224
  (record008_nodes_160 record008_valid)
  (record008_nodes_192 record008_valid))
  (FiniteChecks.interval_append (record008.nodeTestValid record008_valid) 224 256 320
  (record008_nodes_224 record008_valid)
  (FiniteChecks.interval_append (record008.nodeTestValid record008_valid) 256 288 320
  (record008_nodes_256 record008_valid)
  (record008_nodes_288 record008_valid)))))
  (FiniteChecks.interval_append (record008.nodeTestValid record008_valid) 320 480 642
  (FiniteChecks.interval_append (record008.nodeTestValid record008_valid) 320 384 480
  (FiniteChecks.interval_append (record008.nodeTestValid record008_valid) 320 352 384
  (record008_nodes_320 record008_valid)
  (record008_nodes_352 record008_valid))
  (FiniteChecks.interval_append (record008.nodeTestValid record008_valid) 384 416 480
  (record008_nodes_384 record008_valid)
  (FiniteChecks.interval_append (record008.nodeTestValid record008_valid) 416 448 480
  (record008_nodes_416 record008_valid)
  (record008_nodes_448 record008_valid))))
  (FiniteChecks.interval_append (record008.nodeTestValid record008_valid) 480 576 642
  (FiniteChecks.interval_append (record008.nodeTestValid record008_valid) 480 512 576
  (record008_nodes_480 record008_valid)
  (FiniteChecks.interval_append (record008.nodeTestValid record008_valid) 512 544 576
  (record008_nodes_512 record008_valid)
  (record008_nodes_544 record008_valid)))
  (FiniteChecks.interval_append (record008.nodeTestValid record008_valid) 576 608 642
  (record008_nodes_576 record008_valid)
  (FiniteChecks.interval_append (record008.nodeTestValid record008_valid) 608 640 642
  (record008_nodes_608 record008_valid)
  (record008_nodes_640 record008_valid))))))
theorem record008_raw_node_checks (record008_valid : GraphGrowthInputs.Valid record008.inputs) (i : Fin record008.t) :
    RawGraphConditionedGrowth.nodeCheck (record008.inputs.problem record008_valid)
      record008.maps record008.leaf record008.nodes i = true :=
  record008.node_checks_valid record008_valid record008_supports (record008_checked record008_valid) i
#print axioms record008_raw_node_checks

end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00153
