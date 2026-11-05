module
prelude
public import GraphInputsRow24Part00084Data
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00084
open Papers.RationalityTen PackedGraphCertificate FiniteChecks
theorem record000_nodes_0 (record000_valid : GraphGrowthInputs.Valid record000.inputs) : Interval (record000.nodeTestValid record000_valid) 0 32 :=
  interval_of_check _ 0 32 (by decide_kernel_context)
theorem record000_nodes_32 (record000_valid : GraphGrowthInputs.Valid record000.inputs) : Interval (record000.nodeTestValid record000_valid) 32 56 :=
  interval_of_check _ 32 24 (by decide_kernel_context)
theorem record000_supports : record000.Supports := by unfold RawData.Supports; decide +kernel
theorem record000_leaf_0 : Interval record000.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record000_leaves_nodup (j : Fin record000.l) : (record000.leaf j).Nodup :=
  record000.leaves_nodup_of_interval record000_leaf_0 j
theorem record000_checked (record000_valid : GraphGrowthInputs.Valid record000.inputs) : Interval (record000.nodeTestValid record000_valid) 0 56 :=
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 0 32 56
  (record000_nodes_0 record000_valid)
  (record000_nodes_32 record000_valid))
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
theorem record001_nodes_192 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 192 220 :=
  interval_of_check _ 192 28 (by decide_kernel_context)
theorem record001_supports : record001.Supports := by unfold RawData.Supports; decide +kernel
theorem record001_leaf_0 : Interval record001.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record001_leaves_nodup (j : Fin record001.l) : (record001.leaf j).Nodup :=
  record001.leaves_nodup_of_interval record001_leaf_0 j
theorem record001_checked (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 0 220 :=
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 0 96 220
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 0 32 96
  (record001_nodes_0 record001_valid)
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 32 64 96
  (record001_nodes_32 record001_valid)
  (record001_nodes_64 record001_valid)))
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 96 160 220
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 96 128 160
  (record001_nodes_96 record001_valid)
  (record001_nodes_128 record001_valid))
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 160 192 220
  (record001_nodes_160 record001_valid)
  (record001_nodes_192 record001_valid))))
theorem record001_raw_node_checks (record001_valid : GraphGrowthInputs.Valid record001.inputs) (i : Fin record001.t) :
    RawGraphConditionedGrowth.nodeCheck (record001.inputs.problem record001_valid)
      record001.maps record001.leaf record001.nodes i = true :=
  record001.node_checks_valid record001_valid record001_supports (record001_checked record001_valid) i
#print axioms record001_raw_node_checks
theorem record002_nodes_0 (record002_valid : GraphGrowthInputs.Valid record002.inputs) : Interval (record002.nodeTestValid record002_valid) 0 32 :=
  interval_of_check _ 0 32 (by decide_kernel_context)
theorem record002_nodes_32 (record002_valid : GraphGrowthInputs.Valid record002.inputs) : Interval (record002.nodeTestValid record002_valid) 32 62 :=
  interval_of_check _ 32 30 (by decide_kernel_context)
theorem record002_supports : record002.Supports := by unfold RawData.Supports; decide +kernel
theorem record002_leaf_0 : Interval record002.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record002_leaves_nodup (j : Fin record002.l) : (record002.leaf j).Nodup :=
  record002.leaves_nodup_of_interval record002_leaf_0 j
theorem record002_checked (record002_valid : GraphGrowthInputs.Valid record002.inputs) : Interval (record002.nodeTestValid record002_valid) 0 62 :=
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 0 32 62
  (record002_nodes_0 record002_valid)
  (record002_nodes_32 record002_valid))
theorem record002_raw_node_checks (record002_valid : GraphGrowthInputs.Valid record002.inputs) (i : Fin record002.t) :
    RawGraphConditionedGrowth.nodeCheck (record002.inputs.problem record002_valid)
      record002.maps record002.leaf record002.nodes i = true :=
  record002.node_checks_valid record002_valid record002_supports (record002_checked record002_valid) i
#print axioms record002_raw_node_checks
theorem record003_nodes_0 (record003_valid : GraphGrowthInputs.Valid record003.inputs) : Interval (record003.nodeTestValid record003_valid) 0 11 :=
  interval_of_check _ 0 11 (by decide_kernel_context)
theorem record003_supports : record003.Supports := by unfold RawData.Supports; decide +kernel
theorem record003_leaf_0 : Interval record003.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record003_leaves_nodup (j : Fin record003.l) : (record003.leaf j).Nodup :=
  record003.leaves_nodup_of_interval record003_leaf_0 j
theorem record003_checked (record003_valid : GraphGrowthInputs.Valid record003.inputs) : Interval (record003.nodeTestValid record003_valid) 0 11 :=
  (record003_nodes_0 record003_valid)
theorem record003_raw_node_checks (record003_valid : GraphGrowthInputs.Valid record003.inputs) (i : Fin record003.t) :
    RawGraphConditionedGrowth.nodeCheck (record003.inputs.problem record003_valid)
      record003.maps record003.leaf record003.nodes i = true :=
  record003.node_checks_valid record003_valid record003_supports (record003_checked record003_valid) i
#print axioms record003_raw_node_checks
theorem record004_nodes_0 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 0 2 :=
  interval_of_check _ 0 2 (by decide_kernel_context)
theorem record004_supports : record004.Supports := by unfold RawData.Supports; decide +kernel
theorem record004_leaf_0 : Interval record004.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record004_leaves_nodup (j : Fin record004.l) : (record004.leaf j).Nodup :=
  record004.leaves_nodup_of_interval record004_leaf_0 j
theorem record004_checked (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 0 2 :=
  (record004_nodes_0 record004_valid)
theorem record004_raw_node_checks (record004_valid : GraphGrowthInputs.Valid record004.inputs) (i : Fin record004.t) :
    RawGraphConditionedGrowth.nodeCheck (record004.inputs.problem record004_valid)
      record004.maps record004.leaf record004.nodes i = true :=
  record004.node_checks_valid record004_valid record004_supports (record004_checked record004_valid) i
#print axioms record004_raw_node_checks
theorem record005_nodes_0 (record005_valid : GraphGrowthInputs.Valid record005.inputs) : Interval (record005.nodeTestValid record005_valid) 0 32 :=
  interval_of_check _ 0 32 (by decide_kernel_context)
theorem record005_nodes_32 (record005_valid : GraphGrowthInputs.Valid record005.inputs) : Interval (record005.nodeTestValid record005_valid) 32 47 :=
  interval_of_check _ 32 15 (by decide_kernel_context)
theorem record005_supports : record005.Supports := by unfold RawData.Supports; decide +kernel
theorem record005_leaf_0 : Interval record005.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record005_leaves_nodup (j : Fin record005.l) : (record005.leaf j).Nodup :=
  record005.leaves_nodup_of_interval record005_leaf_0 j
theorem record005_checked (record005_valid : GraphGrowthInputs.Valid record005.inputs) : Interval (record005.nodeTestValid record005_valid) 0 47 :=
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 0 32 47
  (record005_nodes_0 record005_valid)
  (record005_nodes_32 record005_valid))
theorem record005_raw_node_checks (record005_valid : GraphGrowthInputs.Valid record005.inputs) (i : Fin record005.t) :
    RawGraphConditionedGrowth.nodeCheck (record005.inputs.problem record005_valid)
      record005.maps record005.leaf record005.nodes i = true :=
  record005.node_checks_valid record005_valid record005_supports (record005_checked record005_valid) i
#print axioms record005_raw_node_checks
theorem record006_nodes_0 (record006_valid : GraphGrowthInputs.Valid record006.inputs) : Interval (record006.nodeTestValid record006_valid) 0 32 :=
  interval_of_check _ 0 32 (by decide_kernel_context)
theorem record006_nodes_32 (record006_valid : GraphGrowthInputs.Valid record006.inputs) : Interval (record006.nodeTestValid record006_valid) 32 59 :=
  interval_of_check _ 32 27 (by decide_kernel_context)
theorem record006_supports : record006.Supports := by unfold RawData.Supports; decide +kernel
theorem record006_leaf_0 : Interval record006.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record006_leaves_nodup (j : Fin record006.l) : (record006.leaf j).Nodup :=
  record006.leaves_nodup_of_interval record006_leaf_0 j
theorem record006_checked (record006_valid : GraphGrowthInputs.Valid record006.inputs) : Interval (record006.nodeTestValid record006_valid) 0 59 :=
  (FiniteChecks.interval_append (record006.nodeTestValid record006_valid) 0 32 59
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
theorem record007_nodes_320 (record007_valid : GraphGrowthInputs.Valid record007.inputs) : Interval (record007.nodeTestValid record007_valid) 320 328 :=
  interval_of_check _ 320 8 (by decide_kernel_context)
theorem record007_supports : record007.Supports := by unfold RawData.Supports; decide +kernel
theorem record007_leaf_0 : Interval record007.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record007_leaves_nodup (j : Fin record007.l) : (record007.leaf j).Nodup :=
  record007.leaves_nodup_of_interval record007_leaf_0 j
theorem record007_checked (record007_valid : GraphGrowthInputs.Valid record007.inputs) : Interval (record007.nodeTestValid record007_valid) 0 328 :=
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 0 160 328
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 0 64 160
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 0 32 64
  (record007_nodes_0 record007_valid)
  (record007_nodes_32 record007_valid))
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 64 96 160
  (record007_nodes_64 record007_valid)
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 96 128 160
  (record007_nodes_96 record007_valid)
  (record007_nodes_128 record007_valid))))
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 160 256 328
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 160 192 256
  (record007_nodes_160 record007_valid)
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 192 224 256
  (record007_nodes_192 record007_valid)
  (record007_nodes_224 record007_valid)))
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 256 288 328
  (record007_nodes_256 record007_valid)
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 288 320 328
  (record007_nodes_288 record007_valid)
  (record007_nodes_320 record007_valid)))))
theorem record007_raw_node_checks (record007_valid : GraphGrowthInputs.Valid record007.inputs) (i : Fin record007.t) :
    RawGraphConditionedGrowth.nodeCheck (record007.inputs.problem record007_valid)
      record007.maps record007.leaf record007.nodes i = true :=
  record007.node_checks_valid record007_valid record007_supports (record007_checked record007_valid) i
#print axioms record007_raw_node_checks
theorem record008_nodes_0 (record008_valid : GraphGrowthInputs.Valid record008.inputs) : Interval (record008.nodeTestValid record008_valid) 0 14 :=
  interval_of_check _ 0 14 (by decide_kernel_context)
theorem record008_supports : record008.Supports := by unfold RawData.Supports; decide +kernel
theorem record008_leaf_0 : Interval record008.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record008_leaves_nodup (j : Fin record008.l) : (record008.leaf j).Nodup :=
  record008.leaves_nodup_of_interval record008_leaf_0 j
theorem record008_checked (record008_valid : GraphGrowthInputs.Valid record008.inputs) : Interval (record008.nodeTestValid record008_valid) 0 14 :=
  (record008_nodes_0 record008_valid)
theorem record008_raw_node_checks (record008_valid : GraphGrowthInputs.Valid record008.inputs) (i : Fin record008.t) :
    RawGraphConditionedGrowth.nodeCheck (record008.inputs.problem record008_valid)
      record008.maps record008.leaf record008.nodes i = true :=
  record008.node_checks_valid record008_valid record008_supports (record008_checked record008_valid) i
#print axioms record008_raw_node_checks
theorem record009_nodes_0 (record009_valid : GraphGrowthInputs.Valid record009.inputs) : Interval (record009.nodeTestValid record009_valid) 0 32 :=
  interval_of_check _ 0 32 (by decide_kernel_context)
theorem record009_nodes_32 (record009_valid : GraphGrowthInputs.Valid record009.inputs) : Interval (record009.nodeTestValid record009_valid) 32 58 :=
  interval_of_check _ 32 26 (by decide_kernel_context)
theorem record009_supports : record009.Supports := by unfold RawData.Supports; decide +kernel
theorem record009_leaf_0 : Interval record009.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record009_leaves_nodup (j : Fin record009.l) : (record009.leaf j).Nodup :=
  record009.leaves_nodup_of_interval record009_leaf_0 j
theorem record009_checked (record009_valid : GraphGrowthInputs.Valid record009.inputs) : Interval (record009.nodeTestValid record009_valid) 0 58 :=
  (FiniteChecks.interval_append (record009.nodeTestValid record009_valid) 0 32 58
  (record009_nodes_0 record009_valid)
  (record009_nodes_32 record009_valid))
theorem record009_raw_node_checks (record009_valid : GraphGrowthInputs.Valid record009.inputs) (i : Fin record009.t) :
    RawGraphConditionedGrowth.nodeCheck (record009.inputs.problem record009_valid)
      record009.maps record009.leaf record009.nodes i = true :=
  record009.node_checks_valid record009_valid record009_supports (record009_checked record009_valid) i
#print axioms record009_raw_node_checks
theorem record010_nodes_0 (record010_valid : GraphGrowthInputs.Valid record010.inputs) : Interval (record010.nodeTestValid record010_valid) 0 32 :=
  interval_of_check _ 0 32 (by decide_kernel_context)
theorem record010_nodes_32 (record010_valid : GraphGrowthInputs.Valid record010.inputs) : Interval (record010.nodeTestValid record010_valid) 32 64 :=
  interval_of_check _ 32 32 (by decide_kernel_context)
theorem record010_nodes_64 (record010_valid : GraphGrowthInputs.Valid record010.inputs) : Interval (record010.nodeTestValid record010_valid) 64 74 :=
  interval_of_check _ 64 10 (by decide_kernel_context)
theorem record010_supports : record010.Supports := by unfold RawData.Supports; decide +kernel
theorem record010_leaf_0 : Interval record010.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record010_leaves_nodup (j : Fin record010.l) : (record010.leaf j).Nodup :=
  record010.leaves_nodup_of_interval record010_leaf_0 j
theorem record010_checked (record010_valid : GraphGrowthInputs.Valid record010.inputs) : Interval (record010.nodeTestValid record010_valid) 0 74 :=
  (FiniteChecks.interval_append (record010.nodeTestValid record010_valid) 0 32 74
  (record010_nodes_0 record010_valid)
  (FiniteChecks.interval_append (record010.nodeTestValid record010_valid) 32 64 74
  (record010_nodes_32 record010_valid)
  (record010_nodes_64 record010_valid)))
theorem record010_raw_node_checks (record010_valid : GraphGrowthInputs.Valid record010.inputs) (i : Fin record010.t) :
    RawGraphConditionedGrowth.nodeCheck (record010.inputs.problem record010_valid)
      record010.maps record010.leaf record010.nodes i = true :=
  record010.node_checks_valid record010_valid record010_supports (record010_checked record010_valid) i
#print axioms record010_raw_node_checks
theorem record011_nodes_0 (record011_valid : GraphGrowthInputs.Valid record011.inputs) : Interval (record011.nodeTestValid record011_valid) 0 32 :=
  interval_of_check _ 0 32 (by decide_kernel_context)
theorem record011_nodes_32 (record011_valid : GraphGrowthInputs.Valid record011.inputs) : Interval (record011.nodeTestValid record011_valid) 32 64 :=
  interval_of_check _ 32 32 (by decide_kernel_context)
theorem record011_nodes_64 (record011_valid : GraphGrowthInputs.Valid record011.inputs) : Interval (record011.nodeTestValid record011_valid) 64 96 :=
  interval_of_check _ 64 32 (by decide_kernel_context)
theorem record011_nodes_96 (record011_valid : GraphGrowthInputs.Valid record011.inputs) : Interval (record011.nodeTestValid record011_valid) 96 128 :=
  interval_of_check _ 96 32 (by decide_kernel_context)
theorem record011_nodes_128 (record011_valid : GraphGrowthInputs.Valid record011.inputs) : Interval (record011.nodeTestValid record011_valid) 128 160 :=
  interval_of_check _ 128 32 (by decide_kernel_context)
theorem record011_nodes_160 (record011_valid : GraphGrowthInputs.Valid record011.inputs) : Interval (record011.nodeTestValid record011_valid) 160 192 :=
  interval_of_check _ 160 32 (by decide_kernel_context)
theorem record011_nodes_192 (record011_valid : GraphGrowthInputs.Valid record011.inputs) : Interval (record011.nodeTestValid record011_valid) 192 224 :=
  interval_of_check _ 192 32 (by decide_kernel_context)
theorem record011_nodes_224 (record011_valid : GraphGrowthInputs.Valid record011.inputs) : Interval (record011.nodeTestValid record011_valid) 224 256 :=
  interval_of_check _ 224 32 (by decide_kernel_context)
theorem record011_nodes_256 (record011_valid : GraphGrowthInputs.Valid record011.inputs) : Interval (record011.nodeTestValid record011_valid) 256 288 :=
  interval_of_check _ 256 32 (by decide_kernel_context)
theorem record011_nodes_288 (record011_valid : GraphGrowthInputs.Valid record011.inputs) : Interval (record011.nodeTestValid record011_valid) 288 320 :=
  interval_of_check _ 288 32 (by decide_kernel_context)
theorem record011_nodes_320 (record011_valid : GraphGrowthInputs.Valid record011.inputs) : Interval (record011.nodeTestValid record011_valid) 320 352 :=
  interval_of_check _ 320 32 (by decide_kernel_context)
theorem record011_nodes_352 (record011_valid : GraphGrowthInputs.Valid record011.inputs) : Interval (record011.nodeTestValid record011_valid) 352 384 :=
  interval_of_check _ 352 32 (by decide_kernel_context)
theorem record011_nodes_384 (record011_valid : GraphGrowthInputs.Valid record011.inputs) : Interval (record011.nodeTestValid record011_valid) 384 416 :=
  interval_of_check _ 384 32 (by decide_kernel_context)
theorem record011_nodes_416 (record011_valid : GraphGrowthInputs.Valid record011.inputs) : Interval (record011.nodeTestValid record011_valid) 416 448 :=
  interval_of_check _ 416 32 (by decide_kernel_context)
theorem record011_nodes_448 (record011_valid : GraphGrowthInputs.Valid record011.inputs) : Interval (record011.nodeTestValid record011_valid) 448 480 :=
  interval_of_check _ 448 32 (by decide_kernel_context)
theorem record011_nodes_480 (record011_valid : GraphGrowthInputs.Valid record011.inputs) : Interval (record011.nodeTestValid record011_valid) 480 512 :=
  interval_of_check _ 480 32 (by decide_kernel_context)
theorem record011_nodes_512 (record011_valid : GraphGrowthInputs.Valid record011.inputs) : Interval (record011.nodeTestValid record011_valid) 512 538 :=
  interval_of_check _ 512 26 (by decide_kernel_context)
theorem record011_supports : record011.Supports := by unfold RawData.Supports; decide +kernel
theorem record011_leaf_0 : Interval record011.leafTest 0 6 :=
  interval_of_check _ 0 6 (by decide +kernel)
theorem record011_leaves_nodup (j : Fin record011.l) : (record011.leaf j).Nodup :=
  record011.leaves_nodup_of_interval record011_leaf_0 j
theorem record011_checked (record011_valid : GraphGrowthInputs.Valid record011.inputs) : Interval (record011.nodeTestValid record011_valid) 0 538 :=
  (FiniteChecks.interval_append (record011.nodeTestValid record011_valid) 0 256 538
  (FiniteChecks.interval_append (record011.nodeTestValid record011_valid) 0 128 256
  (FiniteChecks.interval_append (record011.nodeTestValid record011_valid) 0 64 128
  (FiniteChecks.interval_append (record011.nodeTestValid record011_valid) 0 32 64
  (record011_nodes_0 record011_valid)
  (record011_nodes_32 record011_valid))
  (FiniteChecks.interval_append (record011.nodeTestValid record011_valid) 64 96 128
  (record011_nodes_64 record011_valid)
  (record011_nodes_96 record011_valid)))
  (FiniteChecks.interval_append (record011.nodeTestValid record011_valid) 128 192 256
  (FiniteChecks.interval_append (record011.nodeTestValid record011_valid) 128 160 192
  (record011_nodes_128 record011_valid)
  (record011_nodes_160 record011_valid))
  (FiniteChecks.interval_append (record011.nodeTestValid record011_valid) 192 224 256
  (record011_nodes_192 record011_valid)
  (record011_nodes_224 record011_valid))))
  (FiniteChecks.interval_append (record011.nodeTestValid record011_valid) 256 384 538
  (FiniteChecks.interval_append (record011.nodeTestValid record011_valid) 256 320 384
  (FiniteChecks.interval_append (record011.nodeTestValid record011_valid) 256 288 320
  (record011_nodes_256 record011_valid)
  (record011_nodes_288 record011_valid))
  (FiniteChecks.interval_append (record011.nodeTestValid record011_valid) 320 352 384
  (record011_nodes_320 record011_valid)
  (record011_nodes_352 record011_valid)))
  (FiniteChecks.interval_append (record011.nodeTestValid record011_valid) 384 448 538
  (FiniteChecks.interval_append (record011.nodeTestValid record011_valid) 384 416 448
  (record011_nodes_384 record011_valid)
  (record011_nodes_416 record011_valid))
  (FiniteChecks.interval_append (record011.nodeTestValid record011_valid) 448 480 538
  (record011_nodes_448 record011_valid)
  (FiniteChecks.interval_append (record011.nodeTestValid record011_valid) 480 512 538
  (record011_nodes_480 record011_valid)
  (record011_nodes_512 record011_valid))))))
theorem record011_raw_node_checks (record011_valid : GraphGrowthInputs.Valid record011.inputs) (i : Fin record011.t) :
    RawGraphConditionedGrowth.nodeCheck (record011.inputs.problem record011_valid)
      record011.maps record011.leaf record011.nodes i = true :=
  record011.node_checks_valid record011_valid record011_supports (record011_checked record011_valid) i
#print axioms record011_raw_node_checks

end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00084
