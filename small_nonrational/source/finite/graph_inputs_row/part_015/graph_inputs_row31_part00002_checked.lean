module
prelude
public import GraphInputsRow31Part00002Data
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00002
open Papers.RationalityTen PackedGraphCertificate FiniteChecks
theorem record000_nodes_0 (record000_valid : GraphGrowthInputs.Valid record000.inputs) : Interval (record000.nodeTestValid record000_valid) 0 32 :=
  interval_of_check _ 0 32 (by decide_kernel_context)
theorem record000_nodes_32 (record000_valid : GraphGrowthInputs.Valid record000.inputs) : Interval (record000.nodeTestValid record000_valid) 32 64 :=
  interval_of_check _ 32 32 (by decide_kernel_context)
theorem record000_nodes_64 (record000_valid : GraphGrowthInputs.Valid record000.inputs) : Interval (record000.nodeTestValid record000_valid) 64 96 :=
  interval_of_check _ 64 32 (by decide_kernel_context)
theorem record000_nodes_96 (record000_valid : GraphGrowthInputs.Valid record000.inputs) : Interval (record000.nodeTestValid record000_valid) 96 128 :=
  interval_of_check _ 96 32 (by decide_kernel_context)
theorem record000_nodes_128 (record000_valid : GraphGrowthInputs.Valid record000.inputs) : Interval (record000.nodeTestValid record000_valid) 128 147 :=
  interval_of_check _ 128 19 (by decide_kernel_context)
theorem record000_supports : record000.Supports := by unfold RawData.Supports; decide +kernel
theorem record000_leaf_0 : Interval record000.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record000_leaves_nodup (j : Fin record000.l) : (record000.leaf j).Nodup :=
  record000.leaves_nodup_of_interval record000_leaf_0 j
theorem record000_checked (record000_valid : GraphGrowthInputs.Valid record000.inputs) : Interval (record000.nodeTestValid record000_valid) 0 147 :=
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 0 64 147
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 0 32 64
  (record000_nodes_0 record000_valid)
  (record000_nodes_32 record000_valid))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 64 96 147
  (record000_nodes_64 record000_valid)
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 96 128 147
  (record000_nodes_96 record000_valid)
  (record000_nodes_128 record000_valid))))
theorem record000_raw_node_checks (record000_valid : GraphGrowthInputs.Valid record000.inputs) (i : Fin record000.t) :
    RawGraphConditionedGrowth.nodeCheck (record000.inputs.problem record000_valid)
      record000.maps record000.leaf record000.nodes i = true :=
  record000.node_checks_valid record000_valid record000_supports (record000_checked record000_valid) i
#print axioms record000_raw_node_checks
theorem record001_nodes_0 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 0 8 :=
  interval_of_check _ 0 8 (by decide_kernel_context)
theorem record001_supports : record001.Supports := by unfold RawData.Supports; decide +kernel
theorem record001_leaf_0 : Interval record001.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record001_leaves_nodup (j : Fin record001.l) : (record001.leaf j).Nodup :=
  record001.leaves_nodup_of_interval record001_leaf_0 j
theorem record001_checked (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 0 8 :=
  (record001_nodes_0 record001_valid)
theorem record001_raw_node_checks (record001_valid : GraphGrowthInputs.Valid record001.inputs) (i : Fin record001.t) :
    RawGraphConditionedGrowth.nodeCheck (record001.inputs.problem record001_valid)
      record001.maps record001.leaf record001.nodes i = true :=
  record001.node_checks_valid record001_valid record001_supports (record001_checked record001_valid) i
#print axioms record001_raw_node_checks
theorem record002_nodes_0 (record002_valid : GraphGrowthInputs.Valid record002.inputs) : Interval (record002.nodeTestValid record002_valid) 0 10 :=
  interval_of_check _ 0 10 (by decide_kernel_context)
theorem record002_supports : record002.Supports := by unfold RawData.Supports; decide +kernel
theorem record002_leaf_0 : Interval record002.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record002_leaves_nodup (j : Fin record002.l) : (record002.leaf j).Nodup :=
  record002.leaves_nodup_of_interval record002_leaf_0 j
theorem record002_checked (record002_valid : GraphGrowthInputs.Valid record002.inputs) : Interval (record002.nodeTestValid record002_valid) 0 10 :=
  (record002_nodes_0 record002_valid)
theorem record002_raw_node_checks (record002_valid : GraphGrowthInputs.Valid record002.inputs) (i : Fin record002.t) :
    RawGraphConditionedGrowth.nodeCheck (record002.inputs.problem record002_valid)
      record002.maps record002.leaf record002.nodes i = true :=
  record002.node_checks_valid record002_valid record002_supports (record002_checked record002_valid) i
#print axioms record002_raw_node_checks
theorem record003_nodes_0 (record003_valid : GraphGrowthInputs.Valid record003.inputs) : Interval (record003.nodeTestValid record003_valid) 0 32 :=
  interval_of_check _ 0 32 (by decide_kernel_context)
theorem record003_nodes_32 (record003_valid : GraphGrowthInputs.Valid record003.inputs) : Interval (record003.nodeTestValid record003_valid) 32 64 :=
  interval_of_check _ 32 32 (by decide_kernel_context)
theorem record003_nodes_64 (record003_valid : GraphGrowthInputs.Valid record003.inputs) : Interval (record003.nodeTestValid record003_valid) 64 89 :=
  interval_of_check _ 64 25 (by decide_kernel_context)
theorem record003_supports : record003.Supports := by unfold RawData.Supports; decide +kernel
theorem record003_leaf_0 : Interval record003.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record003_leaves_nodup (j : Fin record003.l) : (record003.leaf j).Nodup :=
  record003.leaves_nodup_of_interval record003_leaf_0 j
theorem record003_checked (record003_valid : GraphGrowthInputs.Valid record003.inputs) : Interval (record003.nodeTestValid record003_valid) 0 89 :=
  (FiniteChecks.interval_append (record003.nodeTestValid record003_valid) 0 32 89
  (record003_nodes_0 record003_valid)
  (FiniteChecks.interval_append (record003.nodeTestValid record003_valid) 32 64 89
  (record003_nodes_32 record003_valid)
  (record003_nodes_64 record003_valid)))
theorem record003_raw_node_checks (record003_valid : GraphGrowthInputs.Valid record003.inputs) (i : Fin record003.t) :
    RawGraphConditionedGrowth.nodeCheck (record003.inputs.problem record003_valid)
      record003.maps record003.leaf record003.nodes i = true :=
  record003.node_checks_valid record003_valid record003_supports (record003_checked record003_valid) i
#print axioms record003_raw_node_checks
theorem record004_nodes_0 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 0 25 :=
  interval_of_check _ 0 25 (by decide_kernel_context)
theorem record004_supports : record004.Supports := by unfold RawData.Supports; decide +kernel
theorem record004_leaf_0 : Interval record004.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record004_leaves_nodup (j : Fin record004.l) : (record004.leaf j).Nodup :=
  record004.leaves_nodup_of_interval record004_leaf_0 j
theorem record004_checked (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 0 25 :=
  (record004_nodes_0 record004_valid)
theorem record004_raw_node_checks (record004_valid : GraphGrowthInputs.Valid record004.inputs) (i : Fin record004.t) :
    RawGraphConditionedGrowth.nodeCheck (record004.inputs.problem record004_valid)
      record004.maps record004.leaf record004.nodes i = true :=
  record004.node_checks_valid record004_valid record004_supports (record004_checked record004_valid) i
#print axioms record004_raw_node_checks
theorem record005_nodes_0 (record005_valid : GraphGrowthInputs.Valid record005.inputs) : Interval (record005.nodeTestValid record005_valid) 0 29 :=
  interval_of_check _ 0 29 (by decide_kernel_context)
theorem record005_supports : record005.Supports := by unfold RawData.Supports; decide +kernel
theorem record005_leaf_0 : Interval record005.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record005_leaves_nodup (j : Fin record005.l) : (record005.leaf j).Nodup :=
  record005.leaves_nodup_of_interval record005_leaf_0 j
theorem record005_checked (record005_valid : GraphGrowthInputs.Valid record005.inputs) : Interval (record005.nodeTestValid record005_valid) 0 29 :=
  (record005_nodes_0 record005_valid)
theorem record005_raw_node_checks (record005_valid : GraphGrowthInputs.Valid record005.inputs) (i : Fin record005.t) :
    RawGraphConditionedGrowth.nodeCheck (record005.inputs.problem record005_valid)
      record005.maps record005.leaf record005.nodes i = true :=
  record005.node_checks_valid record005_valid record005_supports (record005_checked record005_valid) i
#print axioms record005_raw_node_checks
theorem record006_nodes_0 (record006_valid : GraphGrowthInputs.Valid record006.inputs) : Interval (record006.nodeTestValid record006_valid) 0 22 :=
  interval_of_check _ 0 22 (by decide_kernel_context)
theorem record006_supports : record006.Supports := by unfold RawData.Supports; decide +kernel
theorem record006_leaf_0 : Interval record006.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record006_leaves_nodup (j : Fin record006.l) : (record006.leaf j).Nodup :=
  record006.leaves_nodup_of_interval record006_leaf_0 j
theorem record006_checked (record006_valid : GraphGrowthInputs.Valid record006.inputs) : Interval (record006.nodeTestValid record006_valid) 0 22 :=
  (record006_nodes_0 record006_valid)
theorem record006_raw_node_checks (record006_valid : GraphGrowthInputs.Valid record006.inputs) (i : Fin record006.t) :
    RawGraphConditionedGrowth.nodeCheck (record006.inputs.problem record006_valid)
      record006.maps record006.leaf record006.nodes i = true :=
  record006.node_checks_valid record006_valid record006_supports (record006_checked record006_valid) i
#print axioms record006_raw_node_checks
theorem record007_nodes_0 (record007_valid : GraphGrowthInputs.Valid record007.inputs) : Interval (record007.nodeTestValid record007_valid) 0 15 :=
  interval_of_check _ 0 15 (by decide_kernel_context)
theorem record007_supports : record007.Supports := by unfold RawData.Supports; decide +kernel
theorem record007_leaf_0 : Interval record007.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record007_leaves_nodup (j : Fin record007.l) : (record007.leaf j).Nodup :=
  record007.leaves_nodup_of_interval record007_leaf_0 j
theorem record007_checked (record007_valid : GraphGrowthInputs.Valid record007.inputs) : Interval (record007.nodeTestValid record007_valid) 0 15 :=
  (record007_nodes_0 record007_valid)
theorem record007_raw_node_checks (record007_valid : GraphGrowthInputs.Valid record007.inputs) (i : Fin record007.t) :
    RawGraphConditionedGrowth.nodeCheck (record007.inputs.problem record007_valid)
      record007.maps record007.leaf record007.nodes i = true :=
  record007.node_checks_valid record007_valid record007_supports (record007_checked record007_valid) i
#print axioms record007_raw_node_checks
theorem record008_nodes_0 (record008_valid : GraphGrowthInputs.Valid record008.inputs) : Interval (record008.nodeTestValid record008_valid) 0 4 :=
  interval_of_check _ 0 4 (by decide_kernel_context)
theorem record008_supports : record008.Supports := by unfold RawData.Supports; decide +kernel
theorem record008_leaf_0 : Interval record008.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record008_leaves_nodup (j : Fin record008.l) : (record008.leaf j).Nodup :=
  record008.leaves_nodup_of_interval record008_leaf_0 j
theorem record008_checked (record008_valid : GraphGrowthInputs.Valid record008.inputs) : Interval (record008.nodeTestValid record008_valid) 0 4 :=
  (record008_nodes_0 record008_valid)
theorem record008_raw_node_checks (record008_valid : GraphGrowthInputs.Valid record008.inputs) (i : Fin record008.t) :
    RawGraphConditionedGrowth.nodeCheck (record008.inputs.problem record008_valid)
      record008.maps record008.leaf record008.nodes i = true :=
  record008.node_checks_valid record008_valid record008_supports (record008_checked record008_valid) i
#print axioms record008_raw_node_checks
theorem record009_nodes_0 (record009_valid : GraphGrowthInputs.Valid record009.inputs) : Interval (record009.nodeTestValid record009_valid) 0 2 :=
  interval_of_check _ 0 2 (by decide_kernel_context)
theorem record009_supports : record009.Supports := by unfold RawData.Supports; decide +kernel
theorem record009_leaf_0 : Interval record009.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record009_leaves_nodup (j : Fin record009.l) : (record009.leaf j).Nodup :=
  record009.leaves_nodup_of_interval record009_leaf_0 j
theorem record009_checked (record009_valid : GraphGrowthInputs.Valid record009.inputs) : Interval (record009.nodeTestValid record009_valid) 0 2 :=
  (record009_nodes_0 record009_valid)
theorem record009_raw_node_checks (record009_valid : GraphGrowthInputs.Valid record009.inputs) (i : Fin record009.t) :
    RawGraphConditionedGrowth.nodeCheck (record009.inputs.problem record009_valid)
      record009.maps record009.leaf record009.nodes i = true :=
  record009.node_checks_valid record009_valid record009_supports (record009_checked record009_valid) i
#print axioms record009_raw_node_checks
theorem record010_nodes_0 (record010_valid : GraphGrowthInputs.Valid record010.inputs) : Interval (record010.nodeTestValid record010_valid) 0 7 :=
  interval_of_check _ 0 7 (by decide_kernel_context)
theorem record010_supports : record010.Supports := by unfold RawData.Supports; decide +kernel
theorem record010_leaf_0 : Interval record010.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record010_leaves_nodup (j : Fin record010.l) : (record010.leaf j).Nodup :=
  record010.leaves_nodup_of_interval record010_leaf_0 j
theorem record010_checked (record010_valid : GraphGrowthInputs.Valid record010.inputs) : Interval (record010.nodeTestValid record010_valid) 0 7 :=
  (record010_nodes_0 record010_valid)
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
theorem record011_nodes_192 (record011_valid : GraphGrowthInputs.Valid record011.inputs) : Interval (record011.nodeTestValid record011_valid) 192 198 :=
  interval_of_check _ 192 6 (by decide_kernel_context)
theorem record011_supports : record011.Supports := by unfold RawData.Supports; decide +kernel
theorem record011_leaf_0 : Interval record011.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record011_leaves_nodup (j : Fin record011.l) : (record011.leaf j).Nodup :=
  record011.leaves_nodup_of_interval record011_leaf_0 j
theorem record011_checked (record011_valid : GraphGrowthInputs.Valid record011.inputs) : Interval (record011.nodeTestValid record011_valid) 0 198 :=
  (FiniteChecks.interval_append (record011.nodeTestValid record011_valid) 0 96 198
  (FiniteChecks.interval_append (record011.nodeTestValid record011_valid) 0 32 96
  (record011_nodes_0 record011_valid)
  (FiniteChecks.interval_append (record011.nodeTestValid record011_valid) 32 64 96
  (record011_nodes_32 record011_valid)
  (record011_nodes_64 record011_valid)))
  (FiniteChecks.interval_append (record011.nodeTestValid record011_valid) 96 160 198
  (FiniteChecks.interval_append (record011.nodeTestValid record011_valid) 96 128 160
  (record011_nodes_96 record011_valid)
  (record011_nodes_128 record011_valid))
  (FiniteChecks.interval_append (record011.nodeTestValid record011_valid) 160 192 198
  (record011_nodes_160 record011_valid)
  (record011_nodes_192 record011_valid))))
theorem record011_raw_node_checks (record011_valid : GraphGrowthInputs.Valid record011.inputs) (i : Fin record011.t) :
    RawGraphConditionedGrowth.nodeCheck (record011.inputs.problem record011_valid)
      record011.maps record011.leaf record011.nodes i = true :=
  record011.node_checks_valid record011_valid record011_supports (record011_checked record011_valid) i
#print axioms record011_raw_node_checks
theorem record012_nodes_0 (record012_valid : GraphGrowthInputs.Valid record012.inputs) : Interval (record012.nodeTestValid record012_valid) 0 4 :=
  interval_of_check _ 0 4 (by decide_kernel_context)
theorem record012_supports : record012.Supports := by unfold RawData.Supports; decide +kernel
theorem record012_leaf_0 : Interval record012.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record012_leaves_nodup (j : Fin record012.l) : (record012.leaf j).Nodup :=
  record012.leaves_nodup_of_interval record012_leaf_0 j
theorem record012_checked (record012_valid : GraphGrowthInputs.Valid record012.inputs) : Interval (record012.nodeTestValid record012_valid) 0 4 :=
  (record012_nodes_0 record012_valid)
theorem record012_raw_node_checks (record012_valid : GraphGrowthInputs.Valid record012.inputs) (i : Fin record012.t) :
    RawGraphConditionedGrowth.nodeCheck (record012.inputs.problem record012_valid)
      record012.maps record012.leaf record012.nodes i = true :=
  record012.node_checks_valid record012_valid record012_supports (record012_checked record012_valid) i
#print axioms record012_raw_node_checks
theorem record013_nodes_0 (record013_valid : GraphGrowthInputs.Valid record013.inputs) : Interval (record013.nodeTestValid record013_valid) 0 2 :=
  interval_of_check _ 0 2 (by decide_kernel_context)
theorem record013_supports : record013.Supports := by unfold RawData.Supports; decide +kernel
theorem record013_leaf_0 : Interval record013.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record013_leaves_nodup (j : Fin record013.l) : (record013.leaf j).Nodup :=
  record013.leaves_nodup_of_interval record013_leaf_0 j
theorem record013_checked (record013_valid : GraphGrowthInputs.Valid record013.inputs) : Interval (record013.nodeTestValid record013_valid) 0 2 :=
  (record013_nodes_0 record013_valid)
theorem record013_raw_node_checks (record013_valid : GraphGrowthInputs.Valid record013.inputs) (i : Fin record013.t) :
    RawGraphConditionedGrowth.nodeCheck (record013.inputs.problem record013_valid)
      record013.maps record013.leaf record013.nodes i = true :=
  record013.node_checks_valid record013_valid record013_supports (record013_checked record013_valid) i
#print axioms record013_raw_node_checks
theorem record014_nodes_0 (record014_valid : GraphGrowthInputs.Valid record014.inputs) : Interval (record014.nodeTestValid record014_valid) 0 10 :=
  interval_of_check _ 0 10 (by decide_kernel_context)
theorem record014_supports : record014.Supports := by unfold RawData.Supports; decide +kernel
theorem record014_leaf_0 : Interval record014.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record014_leaves_nodup (j : Fin record014.l) : (record014.leaf j).Nodup :=
  record014.leaves_nodup_of_interval record014_leaf_0 j
theorem record014_checked (record014_valid : GraphGrowthInputs.Valid record014.inputs) : Interval (record014.nodeTestValid record014_valid) 0 10 :=
  (record014_nodes_0 record014_valid)
theorem record014_raw_node_checks (record014_valid : GraphGrowthInputs.Valid record014.inputs) (i : Fin record014.t) :
    RawGraphConditionedGrowth.nodeCheck (record014.inputs.problem record014_valid)
      record014.maps record014.leaf record014.nodes i = true :=
  record014.node_checks_valid record014_valid record014_supports (record014_checked record014_valid) i
#print axioms record014_raw_node_checks
theorem record015_nodes_0 (record015_valid : GraphGrowthInputs.Valid record015.inputs) : Interval (record015.nodeTestValid record015_valid) 0 32 :=
  interval_of_check _ 0 32 (by decide_kernel_context)
theorem record015_nodes_32 (record015_valid : GraphGrowthInputs.Valid record015.inputs) : Interval (record015.nodeTestValid record015_valid) 32 64 :=
  interval_of_check _ 32 32 (by decide_kernel_context)
theorem record015_nodes_64 (record015_valid : GraphGrowthInputs.Valid record015.inputs) : Interval (record015.nodeTestValid record015_valid) 64 96 :=
  interval_of_check _ 64 32 (by decide_kernel_context)
theorem record015_nodes_96 (record015_valid : GraphGrowthInputs.Valid record015.inputs) : Interval (record015.nodeTestValid record015_valid) 96 128 :=
  interval_of_check _ 96 32 (by decide_kernel_context)
theorem record015_nodes_128 (record015_valid : GraphGrowthInputs.Valid record015.inputs) : Interval (record015.nodeTestValid record015_valid) 128 160 :=
  interval_of_check _ 128 32 (by decide_kernel_context)
theorem record015_nodes_160 (record015_valid : GraphGrowthInputs.Valid record015.inputs) : Interval (record015.nodeTestValid record015_valid) 160 192 :=
  interval_of_check _ 160 32 (by decide_kernel_context)
theorem record015_nodes_192 (record015_valid : GraphGrowthInputs.Valid record015.inputs) : Interval (record015.nodeTestValid record015_valid) 192 224 :=
  interval_of_check _ 192 32 (by decide_kernel_context)
theorem record015_nodes_224 (record015_valid : GraphGrowthInputs.Valid record015.inputs) : Interval (record015.nodeTestValid record015_valid) 224 256 :=
  interval_of_check _ 224 32 (by decide_kernel_context)
theorem record015_nodes_256 (record015_valid : GraphGrowthInputs.Valid record015.inputs) : Interval (record015.nodeTestValid record015_valid) 256 288 :=
  interval_of_check _ 256 32 (by decide_kernel_context)
theorem record015_nodes_288 (record015_valid : GraphGrowthInputs.Valid record015.inputs) : Interval (record015.nodeTestValid record015_valid) 288 320 :=
  interval_of_check _ 288 32 (by decide_kernel_context)
theorem record015_nodes_320 (record015_valid : GraphGrowthInputs.Valid record015.inputs) : Interval (record015.nodeTestValid record015_valid) 320 352 :=
  interval_of_check _ 320 32 (by decide_kernel_context)
theorem record015_nodes_352 (record015_valid : GraphGrowthInputs.Valid record015.inputs) : Interval (record015.nodeTestValid record015_valid) 352 384 :=
  interval_of_check _ 352 32 (by decide_kernel_context)
theorem record015_nodes_384 (record015_valid : GraphGrowthInputs.Valid record015.inputs) : Interval (record015.nodeTestValid record015_valid) 384 391 :=
  interval_of_check _ 384 7 (by decide_kernel_context)
theorem record015_supports : record015.Supports := by unfold RawData.Supports; decide +kernel
theorem record015_leaf_0 : Interval record015.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record015_leaves_nodup (j : Fin record015.l) : (record015.leaf j).Nodup :=
  record015.leaves_nodup_of_interval record015_leaf_0 j
theorem record015_checked (record015_valid : GraphGrowthInputs.Valid record015.inputs) : Interval (record015.nodeTestValid record015_valid) 0 391 :=
  (FiniteChecks.interval_append (record015.nodeTestValid record015_valid) 0 192 391
  (FiniteChecks.interval_append (record015.nodeTestValid record015_valid) 0 96 192
  (FiniteChecks.interval_append (record015.nodeTestValid record015_valid) 0 32 96
  (record015_nodes_0 record015_valid)
  (FiniteChecks.interval_append (record015.nodeTestValid record015_valid) 32 64 96
  (record015_nodes_32 record015_valid)
  (record015_nodes_64 record015_valid)))
  (FiniteChecks.interval_append (record015.nodeTestValid record015_valid) 96 128 192
  (record015_nodes_96 record015_valid)
  (FiniteChecks.interval_append (record015.nodeTestValid record015_valid) 128 160 192
  (record015_nodes_128 record015_valid)
  (record015_nodes_160 record015_valid))))
  (FiniteChecks.interval_append (record015.nodeTestValid record015_valid) 192 288 391
  (FiniteChecks.interval_append (record015.nodeTestValid record015_valid) 192 224 288
  (record015_nodes_192 record015_valid)
  (FiniteChecks.interval_append (record015.nodeTestValid record015_valid) 224 256 288
  (record015_nodes_224 record015_valid)
  (record015_nodes_256 record015_valid)))
  (FiniteChecks.interval_append (record015.nodeTestValid record015_valid) 288 352 391
  (FiniteChecks.interval_append (record015.nodeTestValid record015_valid) 288 320 352
  (record015_nodes_288 record015_valid)
  (record015_nodes_320 record015_valid))
  (FiniteChecks.interval_append (record015.nodeTestValid record015_valid) 352 384 391
  (record015_nodes_352 record015_valid)
  (record015_nodes_384 record015_valid)))))
theorem record015_raw_node_checks (record015_valid : GraphGrowthInputs.Valid record015.inputs) (i : Fin record015.t) :
    RawGraphConditionedGrowth.nodeCheck (record015.inputs.problem record015_valid)
      record015.maps record015.leaf record015.nodes i = true :=
  record015.node_checks_valid record015_valid record015_supports (record015_checked record015_valid) i
#print axioms record015_raw_node_checks
theorem record016_nodes_0 (record016_valid : GraphGrowthInputs.Valid record016.inputs) : Interval (record016.nodeTestValid record016_valid) 0 32 :=
  interval_of_check _ 0 32 (by decide_kernel_context)
theorem record016_nodes_32 (record016_valid : GraphGrowthInputs.Valid record016.inputs) : Interval (record016.nodeTestValid record016_valid) 32 64 :=
  interval_of_check _ 32 32 (by decide_kernel_context)
theorem record016_nodes_64 (record016_valid : GraphGrowthInputs.Valid record016.inputs) : Interval (record016.nodeTestValid record016_valid) 64 85 :=
  interval_of_check _ 64 21 (by decide_kernel_context)
theorem record016_supports : record016.Supports := by unfold RawData.Supports; decide +kernel
theorem record016_leaf_0 : Interval record016.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record016_leaves_nodup (j : Fin record016.l) : (record016.leaf j).Nodup :=
  record016.leaves_nodup_of_interval record016_leaf_0 j
theorem record016_checked (record016_valid : GraphGrowthInputs.Valid record016.inputs) : Interval (record016.nodeTestValid record016_valid) 0 85 :=
  (FiniteChecks.interval_append (record016.nodeTestValid record016_valid) 0 32 85
  (record016_nodes_0 record016_valid)
  (FiniteChecks.interval_append (record016.nodeTestValid record016_valid) 32 64 85
  (record016_nodes_32 record016_valid)
  (record016_nodes_64 record016_valid)))
theorem record016_raw_node_checks (record016_valid : GraphGrowthInputs.Valid record016.inputs) (i : Fin record016.t) :
    RawGraphConditionedGrowth.nodeCheck (record016.inputs.problem record016_valid)
      record016.maps record016.leaf record016.nodes i = true :=
  record016.node_checks_valid record016_valid record016_supports (record016_checked record016_valid) i
#print axioms record016_raw_node_checks
theorem record017_nodes_0 (record017_valid : GraphGrowthInputs.Valid record017.inputs) : Interval (record017.nodeTestValid record017_valid) 0 32 :=
  interval_of_check _ 0 32 (by decide_kernel_context)
theorem record017_nodes_32 (record017_valid : GraphGrowthInputs.Valid record017.inputs) : Interval (record017.nodeTestValid record017_valid) 32 64 :=
  interval_of_check _ 32 32 (by decide_kernel_context)
theorem record017_nodes_64 (record017_valid : GraphGrowthInputs.Valid record017.inputs) : Interval (record017.nodeTestValid record017_valid) 64 96 :=
  interval_of_check _ 64 32 (by decide_kernel_context)
theorem record017_nodes_96 (record017_valid : GraphGrowthInputs.Valid record017.inputs) : Interval (record017.nodeTestValid record017_valid) 96 128 :=
  interval_of_check _ 96 32 (by decide_kernel_context)
theorem record017_nodes_128 (record017_valid : GraphGrowthInputs.Valid record017.inputs) : Interval (record017.nodeTestValid record017_valid) 128 145 :=
  interval_of_check _ 128 17 (by decide_kernel_context)
theorem record017_supports : record017.Supports := by unfold RawData.Supports; decide +kernel
theorem record017_leaf_0 : Interval record017.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record017_leaves_nodup (j : Fin record017.l) : (record017.leaf j).Nodup :=
  record017.leaves_nodup_of_interval record017_leaf_0 j
theorem record017_checked (record017_valid : GraphGrowthInputs.Valid record017.inputs) : Interval (record017.nodeTestValid record017_valid) 0 145 :=
  (FiniteChecks.interval_append (record017.nodeTestValid record017_valid) 0 64 145
  (FiniteChecks.interval_append (record017.nodeTestValid record017_valid) 0 32 64
  (record017_nodes_0 record017_valid)
  (record017_nodes_32 record017_valid))
  (FiniteChecks.interval_append (record017.nodeTestValid record017_valid) 64 96 145
  (record017_nodes_64 record017_valid)
  (FiniteChecks.interval_append (record017.nodeTestValid record017_valid) 96 128 145
  (record017_nodes_96 record017_valid)
  (record017_nodes_128 record017_valid))))
theorem record017_raw_node_checks (record017_valid : GraphGrowthInputs.Valid record017.inputs) (i : Fin record017.t) :
    RawGraphConditionedGrowth.nodeCheck (record017.inputs.problem record017_valid)
      record017.maps record017.leaf record017.nodes i = true :=
  record017.node_checks_valid record017_valid record017_supports (record017_checked record017_valid) i
#print axioms record017_raw_node_checks
theorem record018_nodes_0 (record018_valid : GraphGrowthInputs.Valid record018.inputs) : Interval (record018.nodeTestValid record018_valid) 0 32 :=
  interval_of_check _ 0 32 (by decide_kernel_context)
theorem record018_nodes_32 (record018_valid : GraphGrowthInputs.Valid record018.inputs) : Interval (record018.nodeTestValid record018_valid) 32 64 :=
  interval_of_check _ 32 32 (by decide_kernel_context)
theorem record018_nodes_64 (record018_valid : GraphGrowthInputs.Valid record018.inputs) : Interval (record018.nodeTestValid record018_valid) 64 96 :=
  interval_of_check _ 64 32 (by decide_kernel_context)
theorem record018_nodes_96 (record018_valid : GraphGrowthInputs.Valid record018.inputs) : Interval (record018.nodeTestValid record018_valid) 96 128 :=
  interval_of_check _ 96 32 (by decide_kernel_context)
theorem record018_nodes_128 (record018_valid : GraphGrowthInputs.Valid record018.inputs) : Interval (record018.nodeTestValid record018_valid) 128 160 :=
  interval_of_check _ 128 32 (by decide_kernel_context)
theorem record018_nodes_160 (record018_valid : GraphGrowthInputs.Valid record018.inputs) : Interval (record018.nodeTestValid record018_valid) 160 182 :=
  interval_of_check _ 160 22 (by decide_kernel_context)
theorem record018_supports : record018.Supports := by unfold RawData.Supports; decide +kernel
theorem record018_leaf_0 : Interval record018.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record018_leaves_nodup (j : Fin record018.l) : (record018.leaf j).Nodup :=
  record018.leaves_nodup_of_interval record018_leaf_0 j
theorem record018_checked (record018_valid : GraphGrowthInputs.Valid record018.inputs) : Interval (record018.nodeTestValid record018_valid) 0 182 :=
  (FiniteChecks.interval_append (record018.nodeTestValid record018_valid) 0 96 182
  (FiniteChecks.interval_append (record018.nodeTestValid record018_valid) 0 32 96
  (record018_nodes_0 record018_valid)
  (FiniteChecks.interval_append (record018.nodeTestValid record018_valid) 32 64 96
  (record018_nodes_32 record018_valid)
  (record018_nodes_64 record018_valid)))
  (FiniteChecks.interval_append (record018.nodeTestValid record018_valid) 96 128 182
  (record018_nodes_96 record018_valid)
  (FiniteChecks.interval_append (record018.nodeTestValid record018_valid) 128 160 182
  (record018_nodes_128 record018_valid)
  (record018_nodes_160 record018_valid))))
theorem record018_raw_node_checks (record018_valid : GraphGrowthInputs.Valid record018.inputs) (i : Fin record018.t) :
    RawGraphConditionedGrowth.nodeCheck (record018.inputs.problem record018_valid)
      record018.maps record018.leaf record018.nodes i = true :=
  record018.node_checks_valid record018_valid record018_supports (record018_checked record018_valid) i
#print axioms record018_raw_node_checks

end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00002
