module
prelude
public import GraphInputsSix0Part00018Data
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018
open Papers.RationalityTen PackedGraphCertificate FiniteChecks
theorem record000_nodes_0 (record000_valid : GraphGrowthInputs.Valid record000.inputs) : Interval (record000.nodeTestValid record000_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record000_supports : record000.Supports := by unfold RawData.Supports; decide +kernel
theorem record000_leaf_0 : Interval record000.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record000_leaves_nodup (j : Fin record000.l) : (record000.leaf j).Nodup :=
  record000.leaves_nodup_of_interval record000_leaf_0 j
theorem record000_checked (record000_valid : GraphGrowthInputs.Valid record000.inputs) : Interval (record000.nodeTestValid record000_valid) 0 1 :=
  (record000_nodes_0 record000_valid)
theorem record000_raw_node_checks (record000_valid : GraphGrowthInputs.Valid record000.inputs) (i : Fin record000.t) :
    RawGraphConditionedGrowth.nodeCheck (record000.inputs.problem record000_valid)
      record000.maps record000.leaf record000.nodes i = true :=
  record000.node_checks_valid record000_valid record000_supports (record000_checked record000_valid) i
#print axioms record000_raw_node_checks
theorem record001_nodes_0 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record001_supports : record001.Supports := by unfold RawData.Supports; decide +kernel
theorem record001_leaf_0 : Interval record001.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record001_leaves_nodup (j : Fin record001.l) : (record001.leaf j).Nodup :=
  record001.leaves_nodup_of_interval record001_leaf_0 j
theorem record001_checked (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 0 1 :=
  (record001_nodes_0 record001_valid)
theorem record001_raw_node_checks (record001_valid : GraphGrowthInputs.Valid record001.inputs) (i : Fin record001.t) :
    RawGraphConditionedGrowth.nodeCheck (record001.inputs.problem record001_valid)
      record001.maps record001.leaf record001.nodes i = true :=
  record001.node_checks_valid record001_valid record001_supports (record001_checked record001_valid) i
#print axioms record001_raw_node_checks
theorem record002_nodes_0 (record002_valid : GraphGrowthInputs.Valid record002.inputs) : Interval (record002.nodeTestValid record002_valid) 0 3 :=
  interval_of_check _ 0 3 (by decide_kernel_context)
theorem record002_supports : record002.Supports := by unfold RawData.Supports; decide +kernel
theorem record002_leaf_0 : Interval record002.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record002_leaves_nodup (j : Fin record002.l) : (record002.leaf j).Nodup :=
  record002.leaves_nodup_of_interval record002_leaf_0 j
theorem record002_checked (record002_valid : GraphGrowthInputs.Valid record002.inputs) : Interval (record002.nodeTestValid record002_valid) 0 3 :=
  (record002_nodes_0 record002_valid)
theorem record002_raw_node_checks (record002_valid : GraphGrowthInputs.Valid record002.inputs) (i : Fin record002.t) :
    RawGraphConditionedGrowth.nodeCheck (record002.inputs.problem record002_valid)
      record002.maps record002.leaf record002.nodes i = true :=
  record002.node_checks_valid record002_valid record002_supports (record002_checked record002_valid) i
#print axioms record002_raw_node_checks
theorem record003_nodes_0 (record003_valid : GraphGrowthInputs.Valid record003.inputs) : Interval (record003.nodeTestValid record003_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record003_supports : record003.Supports := by unfold RawData.Supports; decide +kernel
theorem record003_leaf_0 : Interval record003.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record003_leaves_nodup (j : Fin record003.l) : (record003.leaf j).Nodup :=
  record003.leaves_nodup_of_interval record003_leaf_0 j
theorem record003_checked (record003_valid : GraphGrowthInputs.Valid record003.inputs) : Interval (record003.nodeTestValid record003_valid) 0 1 :=
  (record003_nodes_0 record003_valid)
theorem record003_raw_node_checks (record003_valid : GraphGrowthInputs.Valid record003.inputs) (i : Fin record003.t) :
    RawGraphConditionedGrowth.nodeCheck (record003.inputs.problem record003_valid)
      record003.maps record003.leaf record003.nodes i = true :=
  record003.node_checks_valid record003_valid record003_supports (record003_checked record003_valid) i
#print axioms record003_raw_node_checks
theorem record004_nodes_0 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record004_supports : record004.Supports := by unfold RawData.Supports; decide +kernel
theorem record004_leaf_0 : Interval record004.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record004_leaves_nodup (j : Fin record004.l) : (record004.leaf j).Nodup :=
  record004.leaves_nodup_of_interval record004_leaf_0 j
theorem record004_checked (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 0 1 :=
  (record004_nodes_0 record004_valid)
theorem record004_raw_node_checks (record004_valid : GraphGrowthInputs.Valid record004.inputs) (i : Fin record004.t) :
    RawGraphConditionedGrowth.nodeCheck (record004.inputs.problem record004_valid)
      record004.maps record004.leaf record004.nodes i = true :=
  record004.node_checks_valid record004_valid record004_supports (record004_checked record004_valid) i
#print axioms record004_raw_node_checks
theorem record005_nodes_0 (record005_valid : GraphGrowthInputs.Valid record005.inputs) : Interval (record005.nodeTestValid record005_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record005_supports : record005.Supports := by unfold RawData.Supports; decide +kernel
theorem record005_leaf_0 : Interval record005.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record005_leaves_nodup (j : Fin record005.l) : (record005.leaf j).Nodup :=
  record005.leaves_nodup_of_interval record005_leaf_0 j
theorem record005_checked (record005_valid : GraphGrowthInputs.Valid record005.inputs) : Interval (record005.nodeTestValid record005_valid) 0 1 :=
  (record005_nodes_0 record005_valid)
theorem record005_raw_node_checks (record005_valid : GraphGrowthInputs.Valid record005.inputs) (i : Fin record005.t) :
    RawGraphConditionedGrowth.nodeCheck (record005.inputs.problem record005_valid)
      record005.maps record005.leaf record005.nodes i = true :=
  record005.node_checks_valid record005_valid record005_supports (record005_checked record005_valid) i
#print axioms record005_raw_node_checks
theorem record006_nodes_0 (record006_valid : GraphGrowthInputs.Valid record006.inputs) : Interval (record006.nodeTestValid record006_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record006_supports : record006.Supports := by unfold RawData.Supports; decide +kernel
theorem record006_leaf_0 : Interval record006.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record006_leaves_nodup (j : Fin record006.l) : (record006.leaf j).Nodup :=
  record006.leaves_nodup_of_interval record006_leaf_0 j
theorem record006_checked (record006_valid : GraphGrowthInputs.Valid record006.inputs) : Interval (record006.nodeTestValid record006_valid) 0 1 :=
  (record006_nodes_0 record006_valid)
theorem record006_raw_node_checks (record006_valid : GraphGrowthInputs.Valid record006.inputs) (i : Fin record006.t) :
    RawGraphConditionedGrowth.nodeCheck (record006.inputs.problem record006_valid)
      record006.maps record006.leaf record006.nodes i = true :=
  record006.node_checks_valid record006_valid record006_supports (record006_checked record006_valid) i
#print axioms record006_raw_node_checks
theorem record007_nodes_0 (record007_valid : GraphGrowthInputs.Valid record007.inputs) : Interval (record007.nodeTestValid record007_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record007_supports : record007.Supports := by unfold RawData.Supports; decide +kernel
theorem record007_leaf_0 : Interval record007.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record007_leaves_nodup (j : Fin record007.l) : (record007.leaf j).Nodup :=
  record007.leaves_nodup_of_interval record007_leaf_0 j
theorem record007_checked (record007_valid : GraphGrowthInputs.Valid record007.inputs) : Interval (record007.nodeTestValid record007_valid) 0 1 :=
  (record007_nodes_0 record007_valid)
theorem record007_raw_node_checks (record007_valid : GraphGrowthInputs.Valid record007.inputs) (i : Fin record007.t) :
    RawGraphConditionedGrowth.nodeCheck (record007.inputs.problem record007_valid)
      record007.maps record007.leaf record007.nodes i = true :=
  record007.node_checks_valid record007_valid record007_supports (record007_checked record007_valid) i
#print axioms record007_raw_node_checks
theorem record008_nodes_0 (record008_valid : GraphGrowthInputs.Valid record008.inputs) : Interval (record008.nodeTestValid record008_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record008_supports : record008.Supports := by unfold RawData.Supports; decide +kernel
theorem record008_leaf_0 : Interval record008.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record008_leaves_nodup (j : Fin record008.l) : (record008.leaf j).Nodup :=
  record008.leaves_nodup_of_interval record008_leaf_0 j
theorem record008_checked (record008_valid : GraphGrowthInputs.Valid record008.inputs) : Interval (record008.nodeTestValid record008_valid) 0 1 :=
  (record008_nodes_0 record008_valid)
theorem record008_raw_node_checks (record008_valid : GraphGrowthInputs.Valid record008.inputs) (i : Fin record008.t) :
    RawGraphConditionedGrowth.nodeCheck (record008.inputs.problem record008_valid)
      record008.maps record008.leaf record008.nodes i = true :=
  record008.node_checks_valid record008_valid record008_supports (record008_checked record008_valid) i
#print axioms record008_raw_node_checks
theorem record009_nodes_0 (record009_valid : GraphGrowthInputs.Valid record009.inputs) : Interval (record009.nodeTestValid record009_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record009_supports : record009.Supports := by unfold RawData.Supports; decide +kernel
theorem record009_leaf_0 : Interval record009.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record009_leaves_nodup (j : Fin record009.l) : (record009.leaf j).Nodup :=
  record009.leaves_nodup_of_interval record009_leaf_0 j
theorem record009_checked (record009_valid : GraphGrowthInputs.Valid record009.inputs) : Interval (record009.nodeTestValid record009_valid) 0 1 :=
  (record009_nodes_0 record009_valid)
theorem record009_raw_node_checks (record009_valid : GraphGrowthInputs.Valid record009.inputs) (i : Fin record009.t) :
    RawGraphConditionedGrowth.nodeCheck (record009.inputs.problem record009_valid)
      record009.maps record009.leaf record009.nodes i = true :=
  record009.node_checks_valid record009_valid record009_supports (record009_checked record009_valid) i
#print axioms record009_raw_node_checks
theorem record010_nodes_0 (record010_valid : GraphGrowthInputs.Valid record010.inputs) : Interval (record010.nodeTestValid record010_valid) 0 5 :=
  interval_of_check _ 0 5 (by decide_kernel_context)
theorem record010_supports : record010.Supports := by unfold RawData.Supports; decide +kernel
theorem record010_leaf_0 : Interval record010.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record010_leaves_nodup (j : Fin record010.l) : (record010.leaf j).Nodup :=
  record010.leaves_nodup_of_interval record010_leaf_0 j
theorem record010_checked (record010_valid : GraphGrowthInputs.Valid record010.inputs) : Interval (record010.nodeTestValid record010_valid) 0 5 :=
  (record010_nodes_0 record010_valid)
theorem record010_raw_node_checks (record010_valid : GraphGrowthInputs.Valid record010.inputs) (i : Fin record010.t) :
    RawGraphConditionedGrowth.nodeCheck (record010.inputs.problem record010_valid)
      record010.maps record010.leaf record010.nodes i = true :=
  record010.node_checks_valid record010_valid record010_supports (record010_checked record010_valid) i
#print axioms record010_raw_node_checks
theorem record011_nodes_0 (record011_valid : GraphGrowthInputs.Valid record011.inputs) : Interval (record011.nodeTestValid record011_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record011_supports : record011.Supports := by unfold RawData.Supports; decide +kernel
theorem record011_leaf_0 : Interval record011.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record011_leaves_nodup (j : Fin record011.l) : (record011.leaf j).Nodup :=
  record011.leaves_nodup_of_interval record011_leaf_0 j
theorem record011_checked (record011_valid : GraphGrowthInputs.Valid record011.inputs) : Interval (record011.nodeTestValid record011_valid) 0 1 :=
  (record011_nodes_0 record011_valid)
theorem record011_raw_node_checks (record011_valid : GraphGrowthInputs.Valid record011.inputs) (i : Fin record011.t) :
    RawGraphConditionedGrowth.nodeCheck (record011.inputs.problem record011_valid)
      record011.maps record011.leaf record011.nodes i = true :=
  record011.node_checks_valid record011_valid record011_supports (record011_checked record011_valid) i
#print axioms record011_raw_node_checks
theorem record012_nodes_0 (record012_valid : GraphGrowthInputs.Valid record012.inputs) : Interval (record012.nodeTestValid record012_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record012_supports : record012.Supports := by unfold RawData.Supports; decide +kernel
theorem record012_leaf_0 : Interval record012.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record012_leaves_nodup (j : Fin record012.l) : (record012.leaf j).Nodup :=
  record012.leaves_nodup_of_interval record012_leaf_0 j
theorem record012_checked (record012_valid : GraphGrowthInputs.Valid record012.inputs) : Interval (record012.nodeTestValid record012_valid) 0 1 :=
  (record012_nodes_0 record012_valid)
theorem record012_raw_node_checks (record012_valid : GraphGrowthInputs.Valid record012.inputs) (i : Fin record012.t) :
    RawGraphConditionedGrowth.nodeCheck (record012.inputs.problem record012_valid)
      record012.maps record012.leaf record012.nodes i = true :=
  record012.node_checks_valid record012_valid record012_supports (record012_checked record012_valid) i
#print axioms record012_raw_node_checks
theorem record013_nodes_0 (record013_valid : GraphGrowthInputs.Valid record013.inputs) : Interval (record013.nodeTestValid record013_valid) 0 4 :=
  interval_of_check _ 0 4 (by decide_kernel_context)
theorem record013_supports : record013.Supports := by unfold RawData.Supports; decide +kernel
theorem record013_leaf_0 : Interval record013.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record013_leaves_nodup (j : Fin record013.l) : (record013.leaf j).Nodup :=
  record013.leaves_nodup_of_interval record013_leaf_0 j
theorem record013_checked (record013_valid : GraphGrowthInputs.Valid record013.inputs) : Interval (record013.nodeTestValid record013_valid) 0 4 :=
  (record013_nodes_0 record013_valid)
theorem record013_raw_node_checks (record013_valid : GraphGrowthInputs.Valid record013.inputs) (i : Fin record013.t) :
    RawGraphConditionedGrowth.nodeCheck (record013.inputs.problem record013_valid)
      record013.maps record013.leaf record013.nodes i = true :=
  record013.node_checks_valid record013_valid record013_supports (record013_checked record013_valid) i
#print axioms record013_raw_node_checks
theorem record014_nodes_0 (record014_valid : GraphGrowthInputs.Valid record014.inputs) : Interval (record014.nodeTestValid record014_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record014_supports : record014.Supports := by unfold RawData.Supports; decide +kernel
theorem record014_leaf_0 : Interval record014.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record014_leaves_nodup (j : Fin record014.l) : (record014.leaf j).Nodup :=
  record014.leaves_nodup_of_interval record014_leaf_0 j
theorem record014_checked (record014_valid : GraphGrowthInputs.Valid record014.inputs) : Interval (record014.nodeTestValid record014_valid) 0 1 :=
  (record014_nodes_0 record014_valid)
theorem record014_raw_node_checks (record014_valid : GraphGrowthInputs.Valid record014.inputs) (i : Fin record014.t) :
    RawGraphConditionedGrowth.nodeCheck (record014.inputs.problem record014_valid)
      record014.maps record014.leaf record014.nodes i = true :=
  record014.node_checks_valid record014_valid record014_supports (record014_checked record014_valid) i
#print axioms record014_raw_node_checks
theorem record015_nodes_0 (record015_valid : GraphGrowthInputs.Valid record015.inputs) : Interval (record015.nodeTestValid record015_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record015_supports : record015.Supports := by unfold RawData.Supports; decide +kernel
theorem record015_leaf_0 : Interval record015.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record015_leaves_nodup (j : Fin record015.l) : (record015.leaf j).Nodup :=
  record015.leaves_nodup_of_interval record015_leaf_0 j
theorem record015_checked (record015_valid : GraphGrowthInputs.Valid record015.inputs) : Interval (record015.nodeTestValid record015_valid) 0 1 :=
  (record015_nodes_0 record015_valid)
theorem record015_raw_node_checks (record015_valid : GraphGrowthInputs.Valid record015.inputs) (i : Fin record015.t) :
    RawGraphConditionedGrowth.nodeCheck (record015.inputs.problem record015_valid)
      record015.maps record015.leaf record015.nodes i = true :=
  record015.node_checks_valid record015_valid record015_supports (record015_checked record015_valid) i
#print axioms record015_raw_node_checks
theorem record016_nodes_0 (record016_valid : GraphGrowthInputs.Valid record016.inputs) : Interval (record016.nodeTestValid record016_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record016_supports : record016.Supports := by unfold RawData.Supports; decide +kernel
theorem record016_leaf_0 : Interval record016.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record016_leaves_nodup (j : Fin record016.l) : (record016.leaf j).Nodup :=
  record016.leaves_nodup_of_interval record016_leaf_0 j
theorem record016_checked (record016_valid : GraphGrowthInputs.Valid record016.inputs) : Interval (record016.nodeTestValid record016_valid) 0 1 :=
  (record016_nodes_0 record016_valid)
theorem record016_raw_node_checks (record016_valid : GraphGrowthInputs.Valid record016.inputs) (i : Fin record016.t) :
    RawGraphConditionedGrowth.nodeCheck (record016.inputs.problem record016_valid)
      record016.maps record016.leaf record016.nodes i = true :=
  record016.node_checks_valid record016_valid record016_supports (record016_checked record016_valid) i
#print axioms record016_raw_node_checks
theorem record017_nodes_0 (record017_valid : GraphGrowthInputs.Valid record017.inputs) : Interval (record017.nodeTestValid record017_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record017_supports : record017.Supports := by unfold RawData.Supports; decide +kernel
theorem record017_leaf_0 : Interval record017.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record017_leaves_nodup (j : Fin record017.l) : (record017.leaf j).Nodup :=
  record017.leaves_nodup_of_interval record017_leaf_0 j
theorem record017_checked (record017_valid : GraphGrowthInputs.Valid record017.inputs) : Interval (record017.nodeTestValid record017_valid) 0 1 :=
  (record017_nodes_0 record017_valid)
theorem record017_raw_node_checks (record017_valid : GraphGrowthInputs.Valid record017.inputs) (i : Fin record017.t) :
    RawGraphConditionedGrowth.nodeCheck (record017.inputs.problem record017_valid)
      record017.maps record017.leaf record017.nodes i = true :=
  record017.node_checks_valid record017_valid record017_supports (record017_checked record017_valid) i
#print axioms record017_raw_node_checks
theorem record018_nodes_0 (record018_valid : GraphGrowthInputs.Valid record018.inputs) : Interval (record018.nodeTestValid record018_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record018_supports : record018.Supports := by unfold RawData.Supports; decide +kernel
theorem record018_leaf_0 : Interval record018.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record018_leaves_nodup (j : Fin record018.l) : (record018.leaf j).Nodup :=
  record018.leaves_nodup_of_interval record018_leaf_0 j
theorem record018_checked (record018_valid : GraphGrowthInputs.Valid record018.inputs) : Interval (record018.nodeTestValid record018_valid) 0 1 :=
  (record018_nodes_0 record018_valid)
theorem record018_raw_node_checks (record018_valid : GraphGrowthInputs.Valid record018.inputs) (i : Fin record018.t) :
    RawGraphConditionedGrowth.nodeCheck (record018.inputs.problem record018_valid)
      record018.maps record018.leaf record018.nodes i = true :=
  record018.node_checks_valid record018_valid record018_supports (record018_checked record018_valid) i
#print axioms record018_raw_node_checks
theorem record019_nodes_0 (record019_valid : GraphGrowthInputs.Valid record019.inputs) : Interval (record019.nodeTestValid record019_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record019_supports : record019.Supports := by unfold RawData.Supports; decide +kernel
theorem record019_leaf_0 : Interval record019.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record019_leaves_nodup (j : Fin record019.l) : (record019.leaf j).Nodup :=
  record019.leaves_nodup_of_interval record019_leaf_0 j
theorem record019_checked (record019_valid : GraphGrowthInputs.Valid record019.inputs) : Interval (record019.nodeTestValid record019_valid) 0 1 :=
  (record019_nodes_0 record019_valid)
theorem record019_raw_node_checks (record019_valid : GraphGrowthInputs.Valid record019.inputs) (i : Fin record019.t) :
    RawGraphConditionedGrowth.nodeCheck (record019.inputs.problem record019_valid)
      record019.maps record019.leaf record019.nodes i = true :=
  record019.node_checks_valid record019_valid record019_supports (record019_checked record019_valid) i
#print axioms record019_raw_node_checks
theorem record020_nodes_0 (record020_valid : GraphGrowthInputs.Valid record020.inputs) : Interval (record020.nodeTestValid record020_valid) 0 26 :=
  interval_of_check _ 0 26 (by decide_kernel_context)
theorem record020_supports : record020.Supports := by unfold RawData.Supports; decide +kernel
theorem record020_leaf_0 : Interval record020.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record020_leaves_nodup (j : Fin record020.l) : (record020.leaf j).Nodup :=
  record020.leaves_nodup_of_interval record020_leaf_0 j
theorem record020_checked (record020_valid : GraphGrowthInputs.Valid record020.inputs) : Interval (record020.nodeTestValid record020_valid) 0 26 :=
  (record020_nodes_0 record020_valid)
theorem record020_raw_node_checks (record020_valid : GraphGrowthInputs.Valid record020.inputs) (i : Fin record020.t) :
    RawGraphConditionedGrowth.nodeCheck (record020.inputs.problem record020_valid)
      record020.maps record020.leaf record020.nodes i = true :=
  record020.node_checks_valid record020_valid record020_supports (record020_checked record020_valid) i
#print axioms record020_raw_node_checks
theorem record021_nodes_0 (record021_valid : GraphGrowthInputs.Valid record021.inputs) : Interval (record021.nodeTestValid record021_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record021_supports : record021.Supports := by unfold RawData.Supports; decide +kernel
theorem record021_leaf_0 : Interval record021.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record021_leaves_nodup (j : Fin record021.l) : (record021.leaf j).Nodup :=
  record021.leaves_nodup_of_interval record021_leaf_0 j
theorem record021_checked (record021_valid : GraphGrowthInputs.Valid record021.inputs) : Interval (record021.nodeTestValid record021_valid) 0 1 :=
  (record021_nodes_0 record021_valid)
theorem record021_raw_node_checks (record021_valid : GraphGrowthInputs.Valid record021.inputs) (i : Fin record021.t) :
    RawGraphConditionedGrowth.nodeCheck (record021.inputs.problem record021_valid)
      record021.maps record021.leaf record021.nodes i = true :=
  record021.node_checks_valid record021_valid record021_supports (record021_checked record021_valid) i
#print axioms record021_raw_node_checks
theorem record022_nodes_0 (record022_valid : GraphGrowthInputs.Valid record022.inputs) : Interval (record022.nodeTestValid record022_valid) 0 12 :=
  interval_of_check _ 0 12 (by decide_kernel_context)
theorem record022_supports : record022.Supports := by unfold RawData.Supports; decide +kernel
theorem record022_leaf_0 : Interval record022.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record022_leaves_nodup (j : Fin record022.l) : (record022.leaf j).Nodup :=
  record022.leaves_nodup_of_interval record022_leaf_0 j
theorem record022_checked (record022_valid : GraphGrowthInputs.Valid record022.inputs) : Interval (record022.nodeTestValid record022_valid) 0 12 :=
  (record022_nodes_0 record022_valid)
theorem record022_raw_node_checks (record022_valid : GraphGrowthInputs.Valid record022.inputs) (i : Fin record022.t) :
    RawGraphConditionedGrowth.nodeCheck (record022.inputs.problem record022_valid)
      record022.maps record022.leaf record022.nodes i = true :=
  record022.node_checks_valid record022_valid record022_supports (record022_checked record022_valid) i
#print axioms record022_raw_node_checks
theorem record023_nodes_0 (record023_valid : GraphGrowthInputs.Valid record023.inputs) : Interval (record023.nodeTestValid record023_valid) 0 5 :=
  interval_of_check _ 0 5 (by decide_kernel_context)
theorem record023_supports : record023.Supports := by unfold RawData.Supports; decide +kernel
theorem record023_leaf_0 : Interval record023.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record023_leaves_nodup (j : Fin record023.l) : (record023.leaf j).Nodup :=
  record023.leaves_nodup_of_interval record023_leaf_0 j
theorem record023_checked (record023_valid : GraphGrowthInputs.Valid record023.inputs) : Interval (record023.nodeTestValid record023_valid) 0 5 :=
  (record023_nodes_0 record023_valid)
theorem record023_raw_node_checks (record023_valid : GraphGrowthInputs.Valid record023.inputs) (i : Fin record023.t) :
    RawGraphConditionedGrowth.nodeCheck (record023.inputs.problem record023_valid)
      record023.maps record023.leaf record023.nodes i = true :=
  record023.node_checks_valid record023_valid record023_supports (record023_checked record023_valid) i
#print axioms record023_raw_node_checks
theorem record024_nodes_0 (record024_valid : GraphGrowthInputs.Valid record024.inputs) : Interval (record024.nodeTestValid record024_valid) 0 14 :=
  interval_of_check _ 0 14 (by decide_kernel_context)
theorem record024_supports : record024.Supports := by unfold RawData.Supports; decide +kernel
theorem record024_leaf_0 : Interval record024.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record024_leaves_nodup (j : Fin record024.l) : (record024.leaf j).Nodup :=
  record024.leaves_nodup_of_interval record024_leaf_0 j
theorem record024_checked (record024_valid : GraphGrowthInputs.Valid record024.inputs) : Interval (record024.nodeTestValid record024_valid) 0 14 :=
  (record024_nodes_0 record024_valid)
theorem record024_raw_node_checks (record024_valid : GraphGrowthInputs.Valid record024.inputs) (i : Fin record024.t) :
    RawGraphConditionedGrowth.nodeCheck (record024.inputs.problem record024_valid)
      record024.maps record024.leaf record024.nodes i = true :=
  record024.node_checks_valid record024_valid record024_supports (record024_checked record024_valid) i
#print axioms record024_raw_node_checks
theorem record025_nodes_0 (record025_valid : GraphGrowthInputs.Valid record025.inputs) : Interval (record025.nodeTestValid record025_valid) 0 24 :=
  interval_of_check _ 0 24 (by decide_kernel_context)
theorem record025_supports : record025.Supports := by unfold RawData.Supports; decide +kernel
theorem record025_leaf_0 : Interval record025.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record025_leaves_nodup (j : Fin record025.l) : (record025.leaf j).Nodup :=
  record025.leaves_nodup_of_interval record025_leaf_0 j
theorem record025_checked (record025_valid : GraphGrowthInputs.Valid record025.inputs) : Interval (record025.nodeTestValid record025_valid) 0 24 :=
  (record025_nodes_0 record025_valid)
theorem record025_raw_node_checks (record025_valid : GraphGrowthInputs.Valid record025.inputs) (i : Fin record025.t) :
    RawGraphConditionedGrowth.nodeCheck (record025.inputs.problem record025_valid)
      record025.maps record025.leaf record025.nodes i = true :=
  record025.node_checks_valid record025_valid record025_supports (record025_checked record025_valid) i
#print axioms record025_raw_node_checks
theorem record026_nodes_0 (record026_valid : GraphGrowthInputs.Valid record026.inputs) : Interval (record026.nodeTestValid record026_valid) 0 13 :=
  interval_of_check _ 0 13 (by decide_kernel_context)
theorem record026_supports : record026.Supports := by unfold RawData.Supports; decide +kernel
theorem record026_leaf_0 : Interval record026.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record026_leaves_nodup (j : Fin record026.l) : (record026.leaf j).Nodup :=
  record026.leaves_nodup_of_interval record026_leaf_0 j
theorem record026_checked (record026_valid : GraphGrowthInputs.Valid record026.inputs) : Interval (record026.nodeTestValid record026_valid) 0 13 :=
  (record026_nodes_0 record026_valid)
theorem record026_raw_node_checks (record026_valid : GraphGrowthInputs.Valid record026.inputs) (i : Fin record026.t) :
    RawGraphConditionedGrowth.nodeCheck (record026.inputs.problem record026_valid)
      record026.maps record026.leaf record026.nodes i = true :=
  record026.node_checks_valid record026_valid record026_supports (record026_checked record026_valid) i
#print axioms record026_raw_node_checks
theorem record027_nodes_0 (record027_valid : GraphGrowthInputs.Valid record027.inputs) : Interval (record027.nodeTestValid record027_valid) 0 16 :=
  interval_of_check _ 0 16 (by decide_kernel_context)
theorem record027_supports : record027.Supports := by unfold RawData.Supports; decide +kernel
theorem record027_leaf_0 : Interval record027.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record027_leaves_nodup (j : Fin record027.l) : (record027.leaf j).Nodup :=
  record027.leaves_nodup_of_interval record027_leaf_0 j
theorem record027_checked (record027_valid : GraphGrowthInputs.Valid record027.inputs) : Interval (record027.nodeTestValid record027_valid) 0 16 :=
  (record027_nodes_0 record027_valid)
theorem record027_raw_node_checks (record027_valid : GraphGrowthInputs.Valid record027.inputs) (i : Fin record027.t) :
    RawGraphConditionedGrowth.nodeCheck (record027.inputs.problem record027_valid)
      record027.maps record027.leaf record027.nodes i = true :=
  record027.node_checks_valid record027_valid record027_supports (record027_checked record027_valid) i
#print axioms record027_raw_node_checks
theorem record028_nodes_0 (record028_valid : GraphGrowthInputs.Valid record028.inputs) : Interval (record028.nodeTestValid record028_valid) 0 10 :=
  interval_of_check _ 0 10 (by decide_kernel_context)
theorem record028_supports : record028.Supports := by unfold RawData.Supports; decide +kernel
theorem record028_leaf_0 : Interval record028.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record028_leaves_nodup (j : Fin record028.l) : (record028.leaf j).Nodup :=
  record028.leaves_nodup_of_interval record028_leaf_0 j
theorem record028_checked (record028_valid : GraphGrowthInputs.Valid record028.inputs) : Interval (record028.nodeTestValid record028_valid) 0 10 :=
  (record028_nodes_0 record028_valid)
theorem record028_raw_node_checks (record028_valid : GraphGrowthInputs.Valid record028.inputs) (i : Fin record028.t) :
    RawGraphConditionedGrowth.nodeCheck (record028.inputs.problem record028_valid)
      record028.maps record028.leaf record028.nodes i = true :=
  record028.node_checks_valid record028_valid record028_supports (record028_checked record028_valid) i
#print axioms record028_raw_node_checks
theorem record029_nodes_0 (record029_valid : GraphGrowthInputs.Valid record029.inputs) : Interval (record029.nodeTestValid record029_valid) 0 2 :=
  interval_of_check _ 0 2 (by decide_kernel_context)
theorem record029_supports : record029.Supports := by unfold RawData.Supports; decide +kernel
theorem record029_leaf_0 : Interval record029.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record029_leaves_nodup (j : Fin record029.l) : (record029.leaf j).Nodup :=
  record029.leaves_nodup_of_interval record029_leaf_0 j
theorem record029_checked (record029_valid : GraphGrowthInputs.Valid record029.inputs) : Interval (record029.nodeTestValid record029_valid) 0 2 :=
  (record029_nodes_0 record029_valid)
theorem record029_raw_node_checks (record029_valid : GraphGrowthInputs.Valid record029.inputs) (i : Fin record029.t) :
    RawGraphConditionedGrowth.nodeCheck (record029.inputs.problem record029_valid)
      record029.maps record029.leaf record029.nodes i = true :=
  record029.node_checks_valid record029_valid record029_supports (record029_checked record029_valid) i
#print axioms record029_raw_node_checks
theorem record030_nodes_0 (record030_valid : GraphGrowthInputs.Valid record030.inputs) : Interval (record030.nodeTestValid record030_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record030_supports : record030.Supports := by unfold RawData.Supports; decide +kernel
theorem record030_leaf_0 : Interval record030.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record030_leaves_nodup (j : Fin record030.l) : (record030.leaf j).Nodup :=
  record030.leaves_nodup_of_interval record030_leaf_0 j
theorem record030_checked (record030_valid : GraphGrowthInputs.Valid record030.inputs) : Interval (record030.nodeTestValid record030_valid) 0 1 :=
  (record030_nodes_0 record030_valid)
theorem record030_raw_node_checks (record030_valid : GraphGrowthInputs.Valid record030.inputs) (i : Fin record030.t) :
    RawGraphConditionedGrowth.nodeCheck (record030.inputs.problem record030_valid)
      record030.maps record030.leaf record030.nodes i = true :=
  record030.node_checks_valid record030_valid record030_supports (record030_checked record030_valid) i
#print axioms record030_raw_node_checks
theorem record031_nodes_0 (record031_valid : GraphGrowthInputs.Valid record031.inputs) : Interval (record031.nodeTestValid record031_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record031_supports : record031.Supports := by unfold RawData.Supports; decide +kernel
theorem record031_leaf_0 : Interval record031.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record031_leaves_nodup (j : Fin record031.l) : (record031.leaf j).Nodup :=
  record031.leaves_nodup_of_interval record031_leaf_0 j
theorem record031_checked (record031_valid : GraphGrowthInputs.Valid record031.inputs) : Interval (record031.nodeTestValid record031_valid) 0 1 :=
  (record031_nodes_0 record031_valid)
theorem record031_raw_node_checks (record031_valid : GraphGrowthInputs.Valid record031.inputs) (i : Fin record031.t) :
    RawGraphConditionedGrowth.nodeCheck (record031.inputs.problem record031_valid)
      record031.maps record031.leaf record031.nodes i = true :=
  record031.node_checks_valid record031_valid record031_supports (record031_checked record031_valid) i
#print axioms record031_raw_node_checks
theorem record032_nodes_0 (record032_valid : GraphGrowthInputs.Valid record032.inputs) : Interval (record032.nodeTestValid record032_valid) 0 5 :=
  interval_of_check _ 0 5 (by decide_kernel_context)
theorem record032_supports : record032.Supports := by unfold RawData.Supports; decide +kernel
theorem record032_leaf_0 : Interval record032.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record032_leaves_nodup (j : Fin record032.l) : (record032.leaf j).Nodup :=
  record032.leaves_nodup_of_interval record032_leaf_0 j
theorem record032_checked (record032_valid : GraphGrowthInputs.Valid record032.inputs) : Interval (record032.nodeTestValid record032_valid) 0 5 :=
  (record032_nodes_0 record032_valid)
theorem record032_raw_node_checks (record032_valid : GraphGrowthInputs.Valid record032.inputs) (i : Fin record032.t) :
    RawGraphConditionedGrowth.nodeCheck (record032.inputs.problem record032_valid)
      record032.maps record032.leaf record032.nodes i = true :=
  record032.node_checks_valid record032_valid record032_supports (record032_checked record032_valid) i
#print axioms record032_raw_node_checks
theorem record033_nodes_0 (record033_valid : GraphGrowthInputs.Valid record033.inputs) : Interval (record033.nodeTestValid record033_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record033_supports : record033.Supports := by unfold RawData.Supports; decide +kernel
theorem record033_leaf_0 : Interval record033.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record033_leaves_nodup (j : Fin record033.l) : (record033.leaf j).Nodup :=
  record033.leaves_nodup_of_interval record033_leaf_0 j
theorem record033_checked (record033_valid : GraphGrowthInputs.Valid record033.inputs) : Interval (record033.nodeTestValid record033_valid) 0 1 :=
  (record033_nodes_0 record033_valid)
theorem record033_raw_node_checks (record033_valid : GraphGrowthInputs.Valid record033.inputs) (i : Fin record033.t) :
    RawGraphConditionedGrowth.nodeCheck (record033.inputs.problem record033_valid)
      record033.maps record033.leaf record033.nodes i = true :=
  record033.node_checks_valid record033_valid record033_supports (record033_checked record033_valid) i
#print axioms record033_raw_node_checks
theorem record034_nodes_0 (record034_valid : GraphGrowthInputs.Valid record034.inputs) : Interval (record034.nodeTestValid record034_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record034_supports : record034.Supports := by unfold RawData.Supports; decide +kernel
theorem record034_leaf_0 : Interval record034.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record034_leaves_nodup (j : Fin record034.l) : (record034.leaf j).Nodup :=
  record034.leaves_nodup_of_interval record034_leaf_0 j
theorem record034_checked (record034_valid : GraphGrowthInputs.Valid record034.inputs) : Interval (record034.nodeTestValid record034_valid) 0 1 :=
  (record034_nodes_0 record034_valid)
theorem record034_raw_node_checks (record034_valid : GraphGrowthInputs.Valid record034.inputs) (i : Fin record034.t) :
    RawGraphConditionedGrowth.nodeCheck (record034.inputs.problem record034_valid)
      record034.maps record034.leaf record034.nodes i = true :=
  record034.node_checks_valid record034_valid record034_supports (record034_checked record034_valid) i
#print axioms record034_raw_node_checks
theorem record035_nodes_0 (record035_valid : GraphGrowthInputs.Valid record035.inputs) : Interval (record035.nodeTestValid record035_valid) 0 4 :=
  interval_of_check _ 0 4 (by decide_kernel_context)
theorem record035_supports : record035.Supports := by unfold RawData.Supports; decide +kernel
theorem record035_leaf_0 : Interval record035.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record035_leaves_nodup (j : Fin record035.l) : (record035.leaf j).Nodup :=
  record035.leaves_nodup_of_interval record035_leaf_0 j
theorem record035_checked (record035_valid : GraphGrowthInputs.Valid record035.inputs) : Interval (record035.nodeTestValid record035_valid) 0 4 :=
  (record035_nodes_0 record035_valid)
theorem record035_raw_node_checks (record035_valid : GraphGrowthInputs.Valid record035.inputs) (i : Fin record035.t) :
    RawGraphConditionedGrowth.nodeCheck (record035.inputs.problem record035_valid)
      record035.maps record035.leaf record035.nodes i = true :=
  record035.node_checks_valid record035_valid record035_supports (record035_checked record035_valid) i
#print axioms record035_raw_node_checks
theorem record036_nodes_0 (record036_valid : GraphGrowthInputs.Valid record036.inputs) : Interval (record036.nodeTestValid record036_valid) 0 3 :=
  interval_of_check _ 0 3 (by decide_kernel_context)
theorem record036_supports : record036.Supports := by unfold RawData.Supports; decide +kernel
theorem record036_leaf_0 : Interval record036.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record036_leaves_nodup (j : Fin record036.l) : (record036.leaf j).Nodup :=
  record036.leaves_nodup_of_interval record036_leaf_0 j
theorem record036_checked (record036_valid : GraphGrowthInputs.Valid record036.inputs) : Interval (record036.nodeTestValid record036_valid) 0 3 :=
  (record036_nodes_0 record036_valid)
theorem record036_raw_node_checks (record036_valid : GraphGrowthInputs.Valid record036.inputs) (i : Fin record036.t) :
    RawGraphConditionedGrowth.nodeCheck (record036.inputs.problem record036_valid)
      record036.maps record036.leaf record036.nodes i = true :=
  record036.node_checks_valid record036_valid record036_supports (record036_checked record036_valid) i
#print axioms record036_raw_node_checks
theorem record037_nodes_0 (record037_valid : GraphGrowthInputs.Valid record037.inputs) : Interval (record037.nodeTestValid record037_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record037_supports : record037.Supports := by unfold RawData.Supports; decide +kernel
theorem record037_leaf_0 : Interval record037.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record037_leaves_nodup (j : Fin record037.l) : (record037.leaf j).Nodup :=
  record037.leaves_nodup_of_interval record037_leaf_0 j
theorem record037_checked (record037_valid : GraphGrowthInputs.Valid record037.inputs) : Interval (record037.nodeTestValid record037_valid) 0 1 :=
  (record037_nodes_0 record037_valid)
theorem record037_raw_node_checks (record037_valid : GraphGrowthInputs.Valid record037.inputs) (i : Fin record037.t) :
    RawGraphConditionedGrowth.nodeCheck (record037.inputs.problem record037_valid)
      record037.maps record037.leaf record037.nodes i = true :=
  record037.node_checks_valid record037_valid record037_supports (record037_checked record037_valid) i
#print axioms record037_raw_node_checks
theorem record038_nodes_0 (record038_valid : GraphGrowthInputs.Valid record038.inputs) : Interval (record038.nodeTestValid record038_valid) 0 4 :=
  interval_of_check _ 0 4 (by decide_kernel_context)
theorem record038_supports : record038.Supports := by unfold RawData.Supports; decide +kernel
theorem record038_leaf_0 : Interval record038.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record038_leaves_nodup (j : Fin record038.l) : (record038.leaf j).Nodup :=
  record038.leaves_nodup_of_interval record038_leaf_0 j
theorem record038_checked (record038_valid : GraphGrowthInputs.Valid record038.inputs) : Interval (record038.nodeTestValid record038_valid) 0 4 :=
  (record038_nodes_0 record038_valid)
theorem record038_raw_node_checks (record038_valid : GraphGrowthInputs.Valid record038.inputs) (i : Fin record038.t) :
    RawGraphConditionedGrowth.nodeCheck (record038.inputs.problem record038_valid)
      record038.maps record038.leaf record038.nodes i = true :=
  record038.node_checks_valid record038_valid record038_supports (record038_checked record038_valid) i
#print axioms record038_raw_node_checks
theorem record039_nodes_0 (record039_valid : GraphGrowthInputs.Valid record039.inputs) : Interval (record039.nodeTestValid record039_valid) 0 2 :=
  interval_of_check _ 0 2 (by decide_kernel_context)
theorem record039_supports : record039.Supports := by unfold RawData.Supports; decide +kernel
theorem record039_leaf_0 : Interval record039.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record039_leaves_nodup (j : Fin record039.l) : (record039.leaf j).Nodup :=
  record039.leaves_nodup_of_interval record039_leaf_0 j
theorem record039_checked (record039_valid : GraphGrowthInputs.Valid record039.inputs) : Interval (record039.nodeTestValid record039_valid) 0 2 :=
  (record039_nodes_0 record039_valid)
theorem record039_raw_node_checks (record039_valid : GraphGrowthInputs.Valid record039.inputs) (i : Fin record039.t) :
    RawGraphConditionedGrowth.nodeCheck (record039.inputs.problem record039_valid)
      record039.maps record039.leaf record039.nodes i = true :=
  record039.node_checks_valid record039_valid record039_supports (record039_checked record039_valid) i
#print axioms record039_raw_node_checks
theorem record040_nodes_0 (record040_valid : GraphGrowthInputs.Valid record040.inputs) : Interval (record040.nodeTestValid record040_valid) 0 31 :=
  interval_of_check _ 0 31 (by decide_kernel_context)
theorem record040_supports : record040.Supports := by unfold RawData.Supports; decide +kernel
theorem record040_leaf_0 : Interval record040.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record040_leaves_nodup (j : Fin record040.l) : (record040.leaf j).Nodup :=
  record040.leaves_nodup_of_interval record040_leaf_0 j
theorem record040_checked (record040_valid : GraphGrowthInputs.Valid record040.inputs) : Interval (record040.nodeTestValid record040_valid) 0 31 :=
  (record040_nodes_0 record040_valid)
theorem record040_raw_node_checks (record040_valid : GraphGrowthInputs.Valid record040.inputs) (i : Fin record040.t) :
    RawGraphConditionedGrowth.nodeCheck (record040.inputs.problem record040_valid)
      record040.maps record040.leaf record040.nodes i = true :=
  record040.node_checks_valid record040_valid record040_supports (record040_checked record040_valid) i
#print axioms record040_raw_node_checks
theorem record041_nodes_0 (record041_valid : GraphGrowthInputs.Valid record041.inputs) : Interval (record041.nodeTestValid record041_valid) 0 32 :=
  interval_of_check _ 0 32 (by decide_kernel_context)
theorem record041_nodes_32 (record041_valid : GraphGrowthInputs.Valid record041.inputs) : Interval (record041.nodeTestValid record041_valid) 32 64 :=
  interval_of_check _ 32 32 (by decide_kernel_context)
theorem record041_nodes_64 (record041_valid : GraphGrowthInputs.Valid record041.inputs) : Interval (record041.nodeTestValid record041_valid) 64 96 :=
  interval_of_check _ 64 32 (by decide_kernel_context)
theorem record041_nodes_96 (record041_valid : GraphGrowthInputs.Valid record041.inputs) : Interval (record041.nodeTestValid record041_valid) 96 112 :=
  interval_of_check _ 96 16 (by decide_kernel_context)
theorem record041_supports : record041.Supports := by unfold RawData.Supports; decide +kernel
theorem record041_leaf_0 : Interval record041.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record041_leaves_nodup (j : Fin record041.l) : (record041.leaf j).Nodup :=
  record041.leaves_nodup_of_interval record041_leaf_0 j
theorem record041_checked (record041_valid : GraphGrowthInputs.Valid record041.inputs) : Interval (record041.nodeTestValid record041_valid) 0 112 :=
  (FiniteChecks.interval_append (record041.nodeTestValid record041_valid) 0 64 112
  (FiniteChecks.interval_append (record041.nodeTestValid record041_valid) 0 32 64
  (record041_nodes_0 record041_valid)
  (record041_nodes_32 record041_valid))
  (FiniteChecks.interval_append (record041.nodeTestValid record041_valid) 64 96 112
  (record041_nodes_64 record041_valid)
  (record041_nodes_96 record041_valid)))
theorem record041_raw_node_checks (record041_valid : GraphGrowthInputs.Valid record041.inputs) (i : Fin record041.t) :
    RawGraphConditionedGrowth.nodeCheck (record041.inputs.problem record041_valid)
      record041.maps record041.leaf record041.nodes i = true :=
  record041.node_checks_valid record041_valid record041_supports (record041_checked record041_valid) i
#print axioms record041_raw_node_checks
theorem record042_nodes_0 (record042_valid : GraphGrowthInputs.Valid record042.inputs) : Interval (record042.nodeTestValid record042_valid) 0 4 :=
  interval_of_check _ 0 4 (by decide_kernel_context)
theorem record042_supports : record042.Supports := by unfold RawData.Supports; decide +kernel
theorem record042_leaf_0 : Interval record042.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record042_leaves_nodup (j : Fin record042.l) : (record042.leaf j).Nodup :=
  record042.leaves_nodup_of_interval record042_leaf_0 j
theorem record042_checked (record042_valid : GraphGrowthInputs.Valid record042.inputs) : Interval (record042.nodeTestValid record042_valid) 0 4 :=
  (record042_nodes_0 record042_valid)
theorem record042_raw_node_checks (record042_valid : GraphGrowthInputs.Valid record042.inputs) (i : Fin record042.t) :
    RawGraphConditionedGrowth.nodeCheck (record042.inputs.problem record042_valid)
      record042.maps record042.leaf record042.nodes i = true :=
  record042.node_checks_valid record042_valid record042_supports (record042_checked record042_valid) i
#print axioms record042_raw_node_checks
theorem record043_nodes_0 (record043_valid : GraphGrowthInputs.Valid record043.inputs) : Interval (record043.nodeTestValid record043_valid) 0 3 :=
  interval_of_check _ 0 3 (by decide_kernel_context)
theorem record043_supports : record043.Supports := by unfold RawData.Supports; decide +kernel
theorem record043_leaf_0 : Interval record043.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record043_leaves_nodup (j : Fin record043.l) : (record043.leaf j).Nodup :=
  record043.leaves_nodup_of_interval record043_leaf_0 j
theorem record043_checked (record043_valid : GraphGrowthInputs.Valid record043.inputs) : Interval (record043.nodeTestValid record043_valid) 0 3 :=
  (record043_nodes_0 record043_valid)
theorem record043_raw_node_checks (record043_valid : GraphGrowthInputs.Valid record043.inputs) (i : Fin record043.t) :
    RawGraphConditionedGrowth.nodeCheck (record043.inputs.problem record043_valid)
      record043.maps record043.leaf record043.nodes i = true :=
  record043.node_checks_valid record043_valid record043_supports (record043_checked record043_valid) i
#print axioms record043_raw_node_checks
theorem record044_nodes_0 (record044_valid : GraphGrowthInputs.Valid record044.inputs) : Interval (record044.nodeTestValid record044_valid) 0 2 :=
  interval_of_check _ 0 2 (by decide_kernel_context)
theorem record044_supports : record044.Supports := by unfold RawData.Supports; decide +kernel
theorem record044_leaf_0 : Interval record044.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record044_leaves_nodup (j : Fin record044.l) : (record044.leaf j).Nodup :=
  record044.leaves_nodup_of_interval record044_leaf_0 j
theorem record044_checked (record044_valid : GraphGrowthInputs.Valid record044.inputs) : Interval (record044.nodeTestValid record044_valid) 0 2 :=
  (record044_nodes_0 record044_valid)
theorem record044_raw_node_checks (record044_valid : GraphGrowthInputs.Valid record044.inputs) (i : Fin record044.t) :
    RawGraphConditionedGrowth.nodeCheck (record044.inputs.problem record044_valid)
      record044.maps record044.leaf record044.nodes i = true :=
  record044.node_checks_valid record044_valid record044_supports (record044_checked record044_valid) i
#print axioms record044_raw_node_checks
theorem record045_nodes_0 (record045_valid : GraphGrowthInputs.Valid record045.inputs) : Interval (record045.nodeTestValid record045_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record045_supports : record045.Supports := by unfold RawData.Supports; decide +kernel
theorem record045_leaf_0 : Interval record045.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record045_leaves_nodup (j : Fin record045.l) : (record045.leaf j).Nodup :=
  record045.leaves_nodup_of_interval record045_leaf_0 j
theorem record045_checked (record045_valid : GraphGrowthInputs.Valid record045.inputs) : Interval (record045.nodeTestValid record045_valid) 0 1 :=
  (record045_nodes_0 record045_valid)
theorem record045_raw_node_checks (record045_valid : GraphGrowthInputs.Valid record045.inputs) (i : Fin record045.t) :
    RawGraphConditionedGrowth.nodeCheck (record045.inputs.problem record045_valid)
      record045.maps record045.leaf record045.nodes i = true :=
  record045.node_checks_valid record045_valid record045_supports (record045_checked record045_valid) i
#print axioms record045_raw_node_checks
theorem record046_nodes_0 (record046_valid : GraphGrowthInputs.Valid record046.inputs) : Interval (record046.nodeTestValid record046_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record046_supports : record046.Supports := by unfold RawData.Supports; decide +kernel
theorem record046_leaf_0 : Interval record046.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record046_leaves_nodup (j : Fin record046.l) : (record046.leaf j).Nodup :=
  record046.leaves_nodup_of_interval record046_leaf_0 j
theorem record046_checked (record046_valid : GraphGrowthInputs.Valid record046.inputs) : Interval (record046.nodeTestValid record046_valid) 0 1 :=
  (record046_nodes_0 record046_valid)
theorem record046_raw_node_checks (record046_valid : GraphGrowthInputs.Valid record046.inputs) (i : Fin record046.t) :
    RawGraphConditionedGrowth.nodeCheck (record046.inputs.problem record046_valid)
      record046.maps record046.leaf record046.nodes i = true :=
  record046.node_checks_valid record046_valid record046_supports (record046_checked record046_valid) i
#print axioms record046_raw_node_checks
theorem record047_nodes_0 (record047_valid : GraphGrowthInputs.Valid record047.inputs) : Interval (record047.nodeTestValid record047_valid) 0 2 :=
  interval_of_check _ 0 2 (by decide_kernel_context)
theorem record047_supports : record047.Supports := by unfold RawData.Supports; decide +kernel
theorem record047_leaf_0 : Interval record047.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record047_leaves_nodup (j : Fin record047.l) : (record047.leaf j).Nodup :=
  record047.leaves_nodup_of_interval record047_leaf_0 j
theorem record047_checked (record047_valid : GraphGrowthInputs.Valid record047.inputs) : Interval (record047.nodeTestValid record047_valid) 0 2 :=
  (record047_nodes_0 record047_valid)
theorem record047_raw_node_checks (record047_valid : GraphGrowthInputs.Valid record047.inputs) (i : Fin record047.t) :
    RawGraphConditionedGrowth.nodeCheck (record047.inputs.problem record047_valid)
      record047.maps record047.leaf record047.nodes i = true :=
  record047.node_checks_valid record047_valid record047_supports (record047_checked record047_valid) i
#print axioms record047_raw_node_checks
theorem record048_nodes_0 (record048_valid : GraphGrowthInputs.Valid record048.inputs) : Interval (record048.nodeTestValid record048_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record048_supports : record048.Supports := by unfold RawData.Supports; decide +kernel
theorem record048_leaf_0 : Interval record048.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record048_leaves_nodup (j : Fin record048.l) : (record048.leaf j).Nodup :=
  record048.leaves_nodup_of_interval record048_leaf_0 j
theorem record048_checked (record048_valid : GraphGrowthInputs.Valid record048.inputs) : Interval (record048.nodeTestValid record048_valid) 0 1 :=
  (record048_nodes_0 record048_valid)
theorem record048_raw_node_checks (record048_valid : GraphGrowthInputs.Valid record048.inputs) (i : Fin record048.t) :
    RawGraphConditionedGrowth.nodeCheck (record048.inputs.problem record048_valid)
      record048.maps record048.leaf record048.nodes i = true :=
  record048.node_checks_valid record048_valid record048_supports (record048_checked record048_valid) i
#print axioms record048_raw_node_checks
theorem record049_nodes_0 (record049_valid : GraphGrowthInputs.Valid record049.inputs) : Interval (record049.nodeTestValid record049_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record049_supports : record049.Supports := by unfold RawData.Supports; decide +kernel
theorem record049_leaf_0 : Interval record049.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record049_leaves_nodup (j : Fin record049.l) : (record049.leaf j).Nodup :=
  record049.leaves_nodup_of_interval record049_leaf_0 j
theorem record049_checked (record049_valid : GraphGrowthInputs.Valid record049.inputs) : Interval (record049.nodeTestValid record049_valid) 0 1 :=
  (record049_nodes_0 record049_valid)
theorem record049_raw_node_checks (record049_valid : GraphGrowthInputs.Valid record049.inputs) (i : Fin record049.t) :
    RawGraphConditionedGrowth.nodeCheck (record049.inputs.problem record049_valid)
      record049.maps record049.leaf record049.nodes i = true :=
  record049.node_checks_valid record049_valid record049_supports (record049_checked record049_valid) i
#print axioms record049_raw_node_checks
theorem record050_nodes_0 (record050_valid : GraphGrowthInputs.Valid record050.inputs) : Interval (record050.nodeTestValid record050_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record050_supports : record050.Supports := by unfold RawData.Supports; decide +kernel
theorem record050_leaf_0 : Interval record050.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record050_leaves_nodup (j : Fin record050.l) : (record050.leaf j).Nodup :=
  record050.leaves_nodup_of_interval record050_leaf_0 j
theorem record050_checked (record050_valid : GraphGrowthInputs.Valid record050.inputs) : Interval (record050.nodeTestValid record050_valid) 0 1 :=
  (record050_nodes_0 record050_valid)
theorem record050_raw_node_checks (record050_valid : GraphGrowthInputs.Valid record050.inputs) (i : Fin record050.t) :
    RawGraphConditionedGrowth.nodeCheck (record050.inputs.problem record050_valid)
      record050.maps record050.leaf record050.nodes i = true :=
  record050.node_checks_valid record050_valid record050_supports (record050_checked record050_valid) i
#print axioms record050_raw_node_checks
theorem record051_nodes_0 (record051_valid : GraphGrowthInputs.Valid record051.inputs) : Interval (record051.nodeTestValid record051_valid) 0 3 :=
  interval_of_check _ 0 3 (by decide_kernel_context)
theorem record051_supports : record051.Supports := by unfold RawData.Supports; decide +kernel
theorem record051_leaf_0 : Interval record051.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record051_leaves_nodup (j : Fin record051.l) : (record051.leaf j).Nodup :=
  record051.leaves_nodup_of_interval record051_leaf_0 j
theorem record051_checked (record051_valid : GraphGrowthInputs.Valid record051.inputs) : Interval (record051.nodeTestValid record051_valid) 0 3 :=
  (record051_nodes_0 record051_valid)
theorem record051_raw_node_checks (record051_valid : GraphGrowthInputs.Valid record051.inputs) (i : Fin record051.t) :
    RawGraphConditionedGrowth.nodeCheck (record051.inputs.problem record051_valid)
      record051.maps record051.leaf record051.nodes i = true :=
  record051.node_checks_valid record051_valid record051_supports (record051_checked record051_valid) i
#print axioms record051_raw_node_checks
theorem record052_nodes_0 (record052_valid : GraphGrowthInputs.Valid record052.inputs) : Interval (record052.nodeTestValid record052_valid) 0 3 :=
  interval_of_check _ 0 3 (by decide_kernel_context)
theorem record052_supports : record052.Supports := by unfold RawData.Supports; decide +kernel
theorem record052_leaf_0 : Interval record052.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record052_leaves_nodup (j : Fin record052.l) : (record052.leaf j).Nodup :=
  record052.leaves_nodup_of_interval record052_leaf_0 j
theorem record052_checked (record052_valid : GraphGrowthInputs.Valid record052.inputs) : Interval (record052.nodeTestValid record052_valid) 0 3 :=
  (record052_nodes_0 record052_valid)
theorem record052_raw_node_checks (record052_valid : GraphGrowthInputs.Valid record052.inputs) (i : Fin record052.t) :
    RawGraphConditionedGrowth.nodeCheck (record052.inputs.problem record052_valid)
      record052.maps record052.leaf record052.nodes i = true :=
  record052.node_checks_valid record052_valid record052_supports (record052_checked record052_valid) i
#print axioms record052_raw_node_checks
theorem record053_nodes_0 (record053_valid : GraphGrowthInputs.Valid record053.inputs) : Interval (record053.nodeTestValid record053_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record053_supports : record053.Supports := by unfold RawData.Supports; decide +kernel
theorem record053_leaf_0 : Interval record053.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record053_leaves_nodup (j : Fin record053.l) : (record053.leaf j).Nodup :=
  record053.leaves_nodup_of_interval record053_leaf_0 j
theorem record053_checked (record053_valid : GraphGrowthInputs.Valid record053.inputs) : Interval (record053.nodeTestValid record053_valid) 0 1 :=
  (record053_nodes_0 record053_valid)
theorem record053_raw_node_checks (record053_valid : GraphGrowthInputs.Valid record053.inputs) (i : Fin record053.t) :
    RawGraphConditionedGrowth.nodeCheck (record053.inputs.problem record053_valid)
      record053.maps record053.leaf record053.nodes i = true :=
  record053.node_checks_valid record053_valid record053_supports (record053_checked record053_valid) i
#print axioms record053_raw_node_checks
theorem record054_nodes_0 (record054_valid : GraphGrowthInputs.Valid record054.inputs) : Interval (record054.nodeTestValid record054_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record054_supports : record054.Supports := by unfold RawData.Supports; decide +kernel
theorem record054_leaf_0 : Interval record054.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record054_leaves_nodup (j : Fin record054.l) : (record054.leaf j).Nodup :=
  record054.leaves_nodup_of_interval record054_leaf_0 j
theorem record054_checked (record054_valid : GraphGrowthInputs.Valid record054.inputs) : Interval (record054.nodeTestValid record054_valid) 0 1 :=
  (record054_nodes_0 record054_valid)
theorem record054_raw_node_checks (record054_valid : GraphGrowthInputs.Valid record054.inputs) (i : Fin record054.t) :
    RawGraphConditionedGrowth.nodeCheck (record054.inputs.problem record054_valid)
      record054.maps record054.leaf record054.nodes i = true :=
  record054.node_checks_valid record054_valid record054_supports (record054_checked record054_valid) i
#print axioms record054_raw_node_checks
theorem record055_nodes_0 (record055_valid : GraphGrowthInputs.Valid record055.inputs) : Interval (record055.nodeTestValid record055_valid) 0 32 :=
  interval_of_check _ 0 32 (by decide_kernel_context)
theorem record055_nodes_32 (record055_valid : GraphGrowthInputs.Valid record055.inputs) : Interval (record055.nodeTestValid record055_valid) 32 64 :=
  interval_of_check _ 32 32 (by decide_kernel_context)
theorem record055_nodes_64 (record055_valid : GraphGrowthInputs.Valid record055.inputs) : Interval (record055.nodeTestValid record055_valid) 64 96 :=
  interval_of_check _ 64 32 (by decide_kernel_context)
theorem record055_nodes_96 (record055_valid : GraphGrowthInputs.Valid record055.inputs) : Interval (record055.nodeTestValid record055_valid) 96 128 :=
  interval_of_check _ 96 32 (by decide_kernel_context)
theorem record055_nodes_128 (record055_valid : GraphGrowthInputs.Valid record055.inputs) : Interval (record055.nodeTestValid record055_valid) 128 160 :=
  interval_of_check _ 128 32 (by decide_kernel_context)
theorem record055_nodes_160 (record055_valid : GraphGrowthInputs.Valid record055.inputs) : Interval (record055.nodeTestValid record055_valid) 160 192 :=
  interval_of_check _ 160 32 (by decide_kernel_context)
theorem record055_nodes_192 (record055_valid : GraphGrowthInputs.Valid record055.inputs) : Interval (record055.nodeTestValid record055_valid) 192 224 :=
  interval_of_check _ 192 32 (by decide_kernel_context)
theorem record055_nodes_224 (record055_valid : GraphGrowthInputs.Valid record055.inputs) : Interval (record055.nodeTestValid record055_valid) 224 256 :=
  interval_of_check _ 224 32 (by decide_kernel_context)
theorem record055_nodes_256 (record055_valid : GraphGrowthInputs.Valid record055.inputs) : Interval (record055.nodeTestValid record055_valid) 256 288 :=
  interval_of_check _ 256 32 (by decide_kernel_context)
theorem record055_nodes_288 (record055_valid : GraphGrowthInputs.Valid record055.inputs) : Interval (record055.nodeTestValid record055_valid) 288 320 :=
  interval_of_check _ 288 32 (by decide_kernel_context)
theorem record055_nodes_320 (record055_valid : GraphGrowthInputs.Valid record055.inputs) : Interval (record055.nodeTestValid record055_valid) 320 352 :=
  interval_of_check _ 320 32 (by decide_kernel_context)
theorem record055_nodes_352 (record055_valid : GraphGrowthInputs.Valid record055.inputs) : Interval (record055.nodeTestValid record055_valid) 352 355 :=
  interval_of_check _ 352 3 (by decide_kernel_context)
theorem record055_supports : record055.Supports := by unfold RawData.Supports; decide +kernel
theorem record055_leaf_0 : Interval record055.leafTest 0 8 :=
  interval_of_check _ 0 8 (by decide +kernel)
theorem record055_leaf_8 : Interval record055.leafTest 8 16 :=
  interval_of_check _ 8 8 (by decide +kernel)
theorem record055_leaf_16 : Interval record055.leafTest 16 22 :=
  interval_of_check _ 16 6 (by decide +kernel)
theorem record055_leaves_nodup (j : Fin record055.l) : (record055.leaf j).Nodup :=
  record055.leaves_nodup_of_interval (FiniteChecks.interval_append record055.leafTest 0 8 22
  record055_leaf_0
  (FiniteChecks.interval_append record055.leafTest 8 16 22
  record055_leaf_8
  record055_leaf_16)) j
theorem record055_checked (record055_valid : GraphGrowthInputs.Valid record055.inputs) : Interval (record055.nodeTestValid record055_valid) 0 355 :=
  (FiniteChecks.interval_append (record055.nodeTestValid record055_valid) 0 192 355
  (FiniteChecks.interval_append (record055.nodeTestValid record055_valid) 0 96 192
  (FiniteChecks.interval_append (record055.nodeTestValid record055_valid) 0 32 96
  (record055_nodes_0 record055_valid)
  (FiniteChecks.interval_append (record055.nodeTestValid record055_valid) 32 64 96
  (record055_nodes_32 record055_valid)
  (record055_nodes_64 record055_valid)))
  (FiniteChecks.interval_append (record055.nodeTestValid record055_valid) 96 128 192
  (record055_nodes_96 record055_valid)
  (FiniteChecks.interval_append (record055.nodeTestValid record055_valid) 128 160 192
  (record055_nodes_128 record055_valid)
  (record055_nodes_160 record055_valid))))
  (FiniteChecks.interval_append (record055.nodeTestValid record055_valid) 192 288 355
  (FiniteChecks.interval_append (record055.nodeTestValid record055_valid) 192 224 288
  (record055_nodes_192 record055_valid)
  (FiniteChecks.interval_append (record055.nodeTestValid record055_valid) 224 256 288
  (record055_nodes_224 record055_valid)
  (record055_nodes_256 record055_valid)))
  (FiniteChecks.interval_append (record055.nodeTestValid record055_valid) 288 320 355
  (record055_nodes_288 record055_valid)
  (FiniteChecks.interval_append (record055.nodeTestValid record055_valid) 320 352 355
  (record055_nodes_320 record055_valid)
  (record055_nodes_352 record055_valid)))))
theorem record055_raw_node_checks (record055_valid : GraphGrowthInputs.Valid record055.inputs) (i : Fin record055.t) :
    RawGraphConditionedGrowth.nodeCheck (record055.inputs.problem record055_valid)
      record055.maps record055.leaf record055.nodes i = true :=
  record055.node_checks_valid record055_valid record055_supports (record055_checked record055_valid) i
#print axioms record055_raw_node_checks
theorem record056_nodes_0 (record056_valid : GraphGrowthInputs.Valid record056.inputs) : Interval (record056.nodeTestValid record056_valid) 0 13 :=
  interval_of_check _ 0 13 (by decide_kernel_context)
theorem record056_supports : record056.Supports := by unfold RawData.Supports; decide +kernel
theorem record056_leaf_0 : Interval record056.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record056_leaves_nodup (j : Fin record056.l) : (record056.leaf j).Nodup :=
  record056.leaves_nodup_of_interval record056_leaf_0 j
theorem record056_checked (record056_valid : GraphGrowthInputs.Valid record056.inputs) : Interval (record056.nodeTestValid record056_valid) 0 13 :=
  (record056_nodes_0 record056_valid)
theorem record056_raw_node_checks (record056_valid : GraphGrowthInputs.Valid record056.inputs) (i : Fin record056.t) :
    RawGraphConditionedGrowth.nodeCheck (record056.inputs.problem record056_valid)
      record056.maps record056.leaf record056.nodes i = true :=
  record056.node_checks_valid record056_valid record056_supports (record056_checked record056_valid) i
#print axioms record056_raw_node_checks
theorem record057_nodes_0 (record057_valid : GraphGrowthInputs.Valid record057.inputs) : Interval (record057.nodeTestValid record057_valid) 0 4 :=
  interval_of_check _ 0 4 (by decide_kernel_context)
theorem record057_supports : record057.Supports := by unfold RawData.Supports; decide +kernel
theorem record057_leaf_0 : Interval record057.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record057_leaves_nodup (j : Fin record057.l) : (record057.leaf j).Nodup :=
  record057.leaves_nodup_of_interval record057_leaf_0 j
theorem record057_checked (record057_valid : GraphGrowthInputs.Valid record057.inputs) : Interval (record057.nodeTestValid record057_valid) 0 4 :=
  (record057_nodes_0 record057_valid)
theorem record057_raw_node_checks (record057_valid : GraphGrowthInputs.Valid record057.inputs) (i : Fin record057.t) :
    RawGraphConditionedGrowth.nodeCheck (record057.inputs.problem record057_valid)
      record057.maps record057.leaf record057.nodes i = true :=
  record057.node_checks_valid record057_valid record057_supports (record057_checked record057_valid) i
#print axioms record057_raw_node_checks
theorem record058_nodes_0 (record058_valid : GraphGrowthInputs.Valid record058.inputs) : Interval (record058.nodeTestValid record058_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record058_supports : record058.Supports := by unfold RawData.Supports; decide +kernel
theorem record058_leaf_0 : Interval record058.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record058_leaves_nodup (j : Fin record058.l) : (record058.leaf j).Nodup :=
  record058.leaves_nodup_of_interval record058_leaf_0 j
theorem record058_checked (record058_valid : GraphGrowthInputs.Valid record058.inputs) : Interval (record058.nodeTestValid record058_valid) 0 1 :=
  (record058_nodes_0 record058_valid)
theorem record058_raw_node_checks (record058_valid : GraphGrowthInputs.Valid record058.inputs) (i : Fin record058.t) :
    RawGraphConditionedGrowth.nodeCheck (record058.inputs.problem record058_valid)
      record058.maps record058.leaf record058.nodes i = true :=
  record058.node_checks_valid record058_valid record058_supports (record058_checked record058_valid) i
#print axioms record058_raw_node_checks
theorem record059_nodes_0 (record059_valid : GraphGrowthInputs.Valid record059.inputs) : Interval (record059.nodeTestValid record059_valid) 0 2 :=
  interval_of_check _ 0 2 (by decide_kernel_context)
theorem record059_supports : record059.Supports := by unfold RawData.Supports; decide +kernel
theorem record059_leaf_0 : Interval record059.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record059_leaves_nodup (j : Fin record059.l) : (record059.leaf j).Nodup :=
  record059.leaves_nodup_of_interval record059_leaf_0 j
theorem record059_checked (record059_valid : GraphGrowthInputs.Valid record059.inputs) : Interval (record059.nodeTestValid record059_valid) 0 2 :=
  (record059_nodes_0 record059_valid)
theorem record059_raw_node_checks (record059_valid : GraphGrowthInputs.Valid record059.inputs) (i : Fin record059.t) :
    RawGraphConditionedGrowth.nodeCheck (record059.inputs.problem record059_valid)
      record059.maps record059.leaf record059.nodes i = true :=
  record059.node_checks_valid record059_valid record059_supports (record059_checked record059_valid) i
#print axioms record059_raw_node_checks
theorem record060_nodes_0 (record060_valid : GraphGrowthInputs.Valid record060.inputs) : Interval (record060.nodeTestValid record060_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record060_supports : record060.Supports := by unfold RawData.Supports; decide +kernel
theorem record060_leaf_0 : Interval record060.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record060_leaves_nodup (j : Fin record060.l) : (record060.leaf j).Nodup :=
  record060.leaves_nodup_of_interval record060_leaf_0 j
theorem record060_checked (record060_valid : GraphGrowthInputs.Valid record060.inputs) : Interval (record060.nodeTestValid record060_valid) 0 1 :=
  (record060_nodes_0 record060_valid)
theorem record060_raw_node_checks (record060_valid : GraphGrowthInputs.Valid record060.inputs) (i : Fin record060.t) :
    RawGraphConditionedGrowth.nodeCheck (record060.inputs.problem record060_valid)
      record060.maps record060.leaf record060.nodes i = true :=
  record060.node_checks_valid record060_valid record060_supports (record060_checked record060_valid) i
#print axioms record060_raw_node_checks
theorem record061_nodes_0 (record061_valid : GraphGrowthInputs.Valid record061.inputs) : Interval (record061.nodeTestValid record061_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record061_supports : record061.Supports := by unfold RawData.Supports; decide +kernel
theorem record061_leaf_0 : Interval record061.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record061_leaves_nodup (j : Fin record061.l) : (record061.leaf j).Nodup :=
  record061.leaves_nodup_of_interval record061_leaf_0 j
theorem record061_checked (record061_valid : GraphGrowthInputs.Valid record061.inputs) : Interval (record061.nodeTestValid record061_valid) 0 1 :=
  (record061_nodes_0 record061_valid)
theorem record061_raw_node_checks (record061_valid : GraphGrowthInputs.Valid record061.inputs) (i : Fin record061.t) :
    RawGraphConditionedGrowth.nodeCheck (record061.inputs.problem record061_valid)
      record061.maps record061.leaf record061.nodes i = true :=
  record061.node_checks_valid record061_valid record061_supports (record061_checked record061_valid) i
#print axioms record061_raw_node_checks
theorem record062_nodes_0 (record062_valid : GraphGrowthInputs.Valid record062.inputs) : Interval (record062.nodeTestValid record062_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record062_supports : record062.Supports := by unfold RawData.Supports; decide +kernel
theorem record062_leaf_0 : Interval record062.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record062_leaves_nodup (j : Fin record062.l) : (record062.leaf j).Nodup :=
  record062.leaves_nodup_of_interval record062_leaf_0 j
theorem record062_checked (record062_valid : GraphGrowthInputs.Valid record062.inputs) : Interval (record062.nodeTestValid record062_valid) 0 1 :=
  (record062_nodes_0 record062_valid)
theorem record062_raw_node_checks (record062_valid : GraphGrowthInputs.Valid record062.inputs) (i : Fin record062.t) :
    RawGraphConditionedGrowth.nodeCheck (record062.inputs.problem record062_valid)
      record062.maps record062.leaf record062.nodes i = true :=
  record062.node_checks_valid record062_valid record062_supports (record062_checked record062_valid) i
#print axioms record062_raw_node_checks
theorem record063_nodes_0 (record063_valid : GraphGrowthInputs.Valid record063.inputs) : Interval (record063.nodeTestValid record063_valid) 0 2 :=
  interval_of_check _ 0 2 (by decide_kernel_context)
theorem record063_supports : record063.Supports := by unfold RawData.Supports; decide +kernel
theorem record063_leaf_0 : Interval record063.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record063_leaves_nodup (j : Fin record063.l) : (record063.leaf j).Nodup :=
  record063.leaves_nodup_of_interval record063_leaf_0 j
theorem record063_checked (record063_valid : GraphGrowthInputs.Valid record063.inputs) : Interval (record063.nodeTestValid record063_valid) 0 2 :=
  (record063_nodes_0 record063_valid)
theorem record063_raw_node_checks (record063_valid : GraphGrowthInputs.Valid record063.inputs) (i : Fin record063.t) :
    RawGraphConditionedGrowth.nodeCheck (record063.inputs.problem record063_valid)
      record063.maps record063.leaf record063.nodes i = true :=
  record063.node_checks_valid record063_valid record063_supports (record063_checked record063_valid) i
#print axioms record063_raw_node_checks
theorem record064_nodes_0 (record064_valid : GraphGrowthInputs.Valid record064.inputs) : Interval (record064.nodeTestValid record064_valid) 0 2 :=
  interval_of_check _ 0 2 (by decide_kernel_context)
theorem record064_supports : record064.Supports := by unfold RawData.Supports; decide +kernel
theorem record064_leaf_0 : Interval record064.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record064_leaves_nodup (j : Fin record064.l) : (record064.leaf j).Nodup :=
  record064.leaves_nodup_of_interval record064_leaf_0 j
theorem record064_checked (record064_valid : GraphGrowthInputs.Valid record064.inputs) : Interval (record064.nodeTestValid record064_valid) 0 2 :=
  (record064_nodes_0 record064_valid)
theorem record064_raw_node_checks (record064_valid : GraphGrowthInputs.Valid record064.inputs) (i : Fin record064.t) :
    RawGraphConditionedGrowth.nodeCheck (record064.inputs.problem record064_valid)
      record064.maps record064.leaf record064.nodes i = true :=
  record064.node_checks_valid record064_valid record064_supports (record064_checked record064_valid) i
#print axioms record064_raw_node_checks
theorem record065_nodes_0 (record065_valid : GraphGrowthInputs.Valid record065.inputs) : Interval (record065.nodeTestValid record065_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record065_supports : record065.Supports := by unfold RawData.Supports; decide +kernel
theorem record065_leaf_0 : Interval record065.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record065_leaves_nodup (j : Fin record065.l) : (record065.leaf j).Nodup :=
  record065.leaves_nodup_of_interval record065_leaf_0 j
theorem record065_checked (record065_valid : GraphGrowthInputs.Valid record065.inputs) : Interval (record065.nodeTestValid record065_valid) 0 1 :=
  (record065_nodes_0 record065_valid)
theorem record065_raw_node_checks (record065_valid : GraphGrowthInputs.Valid record065.inputs) (i : Fin record065.t) :
    RawGraphConditionedGrowth.nodeCheck (record065.inputs.problem record065_valid)
      record065.maps record065.leaf record065.nodes i = true :=
  record065.node_checks_valid record065_valid record065_supports (record065_checked record065_valid) i
#print axioms record065_raw_node_checks
theorem record066_nodes_0 (record066_valid : GraphGrowthInputs.Valid record066.inputs) : Interval (record066.nodeTestValid record066_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record066_supports : record066.Supports := by unfold RawData.Supports; decide +kernel
theorem record066_leaf_0 : Interval record066.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record066_leaves_nodup (j : Fin record066.l) : (record066.leaf j).Nodup :=
  record066.leaves_nodup_of_interval record066_leaf_0 j
theorem record066_checked (record066_valid : GraphGrowthInputs.Valid record066.inputs) : Interval (record066.nodeTestValid record066_valid) 0 1 :=
  (record066_nodes_0 record066_valid)
theorem record066_raw_node_checks (record066_valid : GraphGrowthInputs.Valid record066.inputs) (i : Fin record066.t) :
    RawGraphConditionedGrowth.nodeCheck (record066.inputs.problem record066_valid)
      record066.maps record066.leaf record066.nodes i = true :=
  record066.node_checks_valid record066_valid record066_supports (record066_checked record066_valid) i
#print axioms record066_raw_node_checks
theorem record067_nodes_0 (record067_valid : GraphGrowthInputs.Valid record067.inputs) : Interval (record067.nodeTestValid record067_valid) 0 3 :=
  interval_of_check _ 0 3 (by decide_kernel_context)
theorem record067_supports : record067.Supports := by unfold RawData.Supports; decide +kernel
theorem record067_leaf_0 : Interval record067.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record067_leaves_nodup (j : Fin record067.l) : (record067.leaf j).Nodup :=
  record067.leaves_nodup_of_interval record067_leaf_0 j
theorem record067_checked (record067_valid : GraphGrowthInputs.Valid record067.inputs) : Interval (record067.nodeTestValid record067_valid) 0 3 :=
  (record067_nodes_0 record067_valid)
theorem record067_raw_node_checks (record067_valid : GraphGrowthInputs.Valid record067.inputs) (i : Fin record067.t) :
    RawGraphConditionedGrowth.nodeCheck (record067.inputs.problem record067_valid)
      record067.maps record067.leaf record067.nodes i = true :=
  record067.node_checks_valid record067_valid record067_supports (record067_checked record067_valid) i
#print axioms record067_raw_node_checks
theorem record068_nodes_0 (record068_valid : GraphGrowthInputs.Valid record068.inputs) : Interval (record068.nodeTestValid record068_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record068_supports : record068.Supports := by unfold RawData.Supports; decide +kernel
theorem record068_leaf_0 : Interval record068.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record068_leaves_nodup (j : Fin record068.l) : (record068.leaf j).Nodup :=
  record068.leaves_nodup_of_interval record068_leaf_0 j
theorem record068_checked (record068_valid : GraphGrowthInputs.Valid record068.inputs) : Interval (record068.nodeTestValid record068_valid) 0 1 :=
  (record068_nodes_0 record068_valid)
theorem record068_raw_node_checks (record068_valid : GraphGrowthInputs.Valid record068.inputs) (i : Fin record068.t) :
    RawGraphConditionedGrowth.nodeCheck (record068.inputs.problem record068_valid)
      record068.maps record068.leaf record068.nodes i = true :=
  record068.node_checks_valid record068_valid record068_supports (record068_checked record068_valid) i
#print axioms record068_raw_node_checks
theorem record069_nodes_0 (record069_valid : GraphGrowthInputs.Valid record069.inputs) : Interval (record069.nodeTestValid record069_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record069_supports : record069.Supports := by unfold RawData.Supports; decide +kernel
theorem record069_leaf_0 : Interval record069.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record069_leaves_nodup (j : Fin record069.l) : (record069.leaf j).Nodup :=
  record069.leaves_nodup_of_interval record069_leaf_0 j
theorem record069_checked (record069_valid : GraphGrowthInputs.Valid record069.inputs) : Interval (record069.nodeTestValid record069_valid) 0 1 :=
  (record069_nodes_0 record069_valid)
theorem record069_raw_node_checks (record069_valid : GraphGrowthInputs.Valid record069.inputs) (i : Fin record069.t) :
    RawGraphConditionedGrowth.nodeCheck (record069.inputs.problem record069_valid)
      record069.maps record069.leaf record069.nodes i = true :=
  record069.node_checks_valid record069_valid record069_supports (record069_checked record069_valid) i
#print axioms record069_raw_node_checks
theorem record070_nodes_0 (record070_valid : GraphGrowthInputs.Valid record070.inputs) : Interval (record070.nodeTestValid record070_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record070_supports : record070.Supports := by unfold RawData.Supports; decide +kernel
theorem record070_leaf_0 : Interval record070.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record070_leaves_nodup (j : Fin record070.l) : (record070.leaf j).Nodup :=
  record070.leaves_nodup_of_interval record070_leaf_0 j
theorem record070_checked (record070_valid : GraphGrowthInputs.Valid record070.inputs) : Interval (record070.nodeTestValid record070_valid) 0 1 :=
  (record070_nodes_0 record070_valid)
theorem record070_raw_node_checks (record070_valid : GraphGrowthInputs.Valid record070.inputs) (i : Fin record070.t) :
    RawGraphConditionedGrowth.nodeCheck (record070.inputs.problem record070_valid)
      record070.maps record070.leaf record070.nodes i = true :=
  record070.node_checks_valid record070_valid record070_supports (record070_checked record070_valid) i
#print axioms record070_raw_node_checks
theorem record071_nodes_0 (record071_valid : GraphGrowthInputs.Valid record071.inputs) : Interval (record071.nodeTestValid record071_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record071_supports : record071.Supports := by unfold RawData.Supports; decide +kernel
theorem record071_leaf_0 : Interval record071.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record071_leaves_nodup (j : Fin record071.l) : (record071.leaf j).Nodup :=
  record071.leaves_nodup_of_interval record071_leaf_0 j
theorem record071_checked (record071_valid : GraphGrowthInputs.Valid record071.inputs) : Interval (record071.nodeTestValid record071_valid) 0 1 :=
  (record071_nodes_0 record071_valid)
theorem record071_raw_node_checks (record071_valid : GraphGrowthInputs.Valid record071.inputs) (i : Fin record071.t) :
    RawGraphConditionedGrowth.nodeCheck (record071.inputs.problem record071_valid)
      record071.maps record071.leaf record071.nodes i = true :=
  record071.node_checks_valid record071_valid record071_supports (record071_checked record071_valid) i
#print axioms record071_raw_node_checks
theorem record072_nodes_0 (record072_valid : GraphGrowthInputs.Valid record072.inputs) : Interval (record072.nodeTestValid record072_valid) 0 3 :=
  interval_of_check _ 0 3 (by decide_kernel_context)
theorem record072_supports : record072.Supports := by unfold RawData.Supports; decide +kernel
theorem record072_leaf_0 : Interval record072.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record072_leaves_nodup (j : Fin record072.l) : (record072.leaf j).Nodup :=
  record072.leaves_nodup_of_interval record072_leaf_0 j
theorem record072_checked (record072_valid : GraphGrowthInputs.Valid record072.inputs) : Interval (record072.nodeTestValid record072_valid) 0 3 :=
  (record072_nodes_0 record072_valid)
theorem record072_raw_node_checks (record072_valid : GraphGrowthInputs.Valid record072.inputs) (i : Fin record072.t) :
    RawGraphConditionedGrowth.nodeCheck (record072.inputs.problem record072_valid)
      record072.maps record072.leaf record072.nodes i = true :=
  record072.node_checks_valid record072_valid record072_supports (record072_checked record072_valid) i
#print axioms record072_raw_node_checks
theorem record073_nodes_0 (record073_valid : GraphGrowthInputs.Valid record073.inputs) : Interval (record073.nodeTestValid record073_valid) 0 2 :=
  interval_of_check _ 0 2 (by decide_kernel_context)
theorem record073_supports : record073.Supports := by unfold RawData.Supports; decide +kernel
theorem record073_leaf_0 : Interval record073.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record073_leaves_nodup (j : Fin record073.l) : (record073.leaf j).Nodup :=
  record073.leaves_nodup_of_interval record073_leaf_0 j
theorem record073_checked (record073_valid : GraphGrowthInputs.Valid record073.inputs) : Interval (record073.nodeTestValid record073_valid) 0 2 :=
  (record073_nodes_0 record073_valid)
theorem record073_raw_node_checks (record073_valid : GraphGrowthInputs.Valid record073.inputs) (i : Fin record073.t) :
    RawGraphConditionedGrowth.nodeCheck (record073.inputs.problem record073_valid)
      record073.maps record073.leaf record073.nodes i = true :=
  record073.node_checks_valid record073_valid record073_supports (record073_checked record073_valid) i
#print axioms record073_raw_node_checks
theorem record074_nodes_0 (record074_valid : GraphGrowthInputs.Valid record074.inputs) : Interval (record074.nodeTestValid record074_valid) 0 2 :=
  interval_of_check _ 0 2 (by decide_kernel_context)
theorem record074_supports : record074.Supports := by unfold RawData.Supports; decide +kernel
theorem record074_leaf_0 : Interval record074.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record074_leaves_nodup (j : Fin record074.l) : (record074.leaf j).Nodup :=
  record074.leaves_nodup_of_interval record074_leaf_0 j
theorem record074_checked (record074_valid : GraphGrowthInputs.Valid record074.inputs) : Interval (record074.nodeTestValid record074_valid) 0 2 :=
  (record074_nodes_0 record074_valid)
theorem record074_raw_node_checks (record074_valid : GraphGrowthInputs.Valid record074.inputs) (i : Fin record074.t) :
    RawGraphConditionedGrowth.nodeCheck (record074.inputs.problem record074_valid)
      record074.maps record074.leaf record074.nodes i = true :=
  record074.node_checks_valid record074_valid record074_supports (record074_checked record074_valid) i
#print axioms record074_raw_node_checks
theorem record075_nodes_0 (record075_valid : GraphGrowthInputs.Valid record075.inputs) : Interval (record075.nodeTestValid record075_valid) 0 32 :=
  interval_of_check _ 0 32 (by decide_kernel_context)
theorem record075_nodes_32 (record075_valid : GraphGrowthInputs.Valid record075.inputs) : Interval (record075.nodeTestValid record075_valid) 32 41 :=
  interval_of_check _ 32 9 (by decide_kernel_context)
theorem record075_supports : record075.Supports := by unfold RawData.Supports; decide +kernel
theorem record075_leaf_0 : Interval record075.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record075_leaves_nodup (j : Fin record075.l) : (record075.leaf j).Nodup :=
  record075.leaves_nodup_of_interval record075_leaf_0 j
theorem record075_checked (record075_valid : GraphGrowthInputs.Valid record075.inputs) : Interval (record075.nodeTestValid record075_valid) 0 41 :=
  (FiniteChecks.interval_append (record075.nodeTestValid record075_valid) 0 32 41
  (record075_nodes_0 record075_valid)
  (record075_nodes_32 record075_valid))
theorem record075_raw_node_checks (record075_valid : GraphGrowthInputs.Valid record075.inputs) (i : Fin record075.t) :
    RawGraphConditionedGrowth.nodeCheck (record075.inputs.problem record075_valid)
      record075.maps record075.leaf record075.nodes i = true :=
  record075.node_checks_valid record075_valid record075_supports (record075_checked record075_valid) i
#print axioms record075_raw_node_checks
theorem record076_nodes_0 (record076_valid : GraphGrowthInputs.Valid record076.inputs) : Interval (record076.nodeTestValid record076_valid) 0 5 :=
  interval_of_check _ 0 5 (by decide_kernel_context)
theorem record076_supports : record076.Supports := by unfold RawData.Supports; decide +kernel
theorem record076_leaf_0 : Interval record076.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record076_leaves_nodup (j : Fin record076.l) : (record076.leaf j).Nodup :=
  record076.leaves_nodup_of_interval record076_leaf_0 j
theorem record076_checked (record076_valid : GraphGrowthInputs.Valid record076.inputs) : Interval (record076.nodeTestValid record076_valid) 0 5 :=
  (record076_nodes_0 record076_valid)
theorem record076_raw_node_checks (record076_valid : GraphGrowthInputs.Valid record076.inputs) (i : Fin record076.t) :
    RawGraphConditionedGrowth.nodeCheck (record076.inputs.problem record076_valid)
      record076.maps record076.leaf record076.nodes i = true :=
  record076.node_checks_valid record076_valid record076_supports (record076_checked record076_valid) i
#print axioms record076_raw_node_checks
theorem record077_nodes_0 (record077_valid : GraphGrowthInputs.Valid record077.inputs) : Interval (record077.nodeTestValid record077_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record077_supports : record077.Supports := by unfold RawData.Supports; decide +kernel
theorem record077_leaf_0 : Interval record077.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record077_leaves_nodup (j : Fin record077.l) : (record077.leaf j).Nodup :=
  record077.leaves_nodup_of_interval record077_leaf_0 j
theorem record077_checked (record077_valid : GraphGrowthInputs.Valid record077.inputs) : Interval (record077.nodeTestValid record077_valid) 0 1 :=
  (record077_nodes_0 record077_valid)
theorem record077_raw_node_checks (record077_valid : GraphGrowthInputs.Valid record077.inputs) (i : Fin record077.t) :
    RawGraphConditionedGrowth.nodeCheck (record077.inputs.problem record077_valid)
      record077.maps record077.leaf record077.nodes i = true :=
  record077.node_checks_valid record077_valid record077_supports (record077_checked record077_valid) i
#print axioms record077_raw_node_checks
theorem record078_nodes_0 (record078_valid : GraphGrowthInputs.Valid record078.inputs) : Interval (record078.nodeTestValid record078_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record078_supports : record078.Supports := by unfold RawData.Supports; decide +kernel
theorem record078_leaf_0 : Interval record078.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record078_leaves_nodup (j : Fin record078.l) : (record078.leaf j).Nodup :=
  record078.leaves_nodup_of_interval record078_leaf_0 j
theorem record078_checked (record078_valid : GraphGrowthInputs.Valid record078.inputs) : Interval (record078.nodeTestValid record078_valid) 0 1 :=
  (record078_nodes_0 record078_valid)
theorem record078_raw_node_checks (record078_valid : GraphGrowthInputs.Valid record078.inputs) (i : Fin record078.t) :
    RawGraphConditionedGrowth.nodeCheck (record078.inputs.problem record078_valid)
      record078.maps record078.leaf record078.nodes i = true :=
  record078.node_checks_valid record078_valid record078_supports (record078_checked record078_valid) i
#print axioms record078_raw_node_checks
theorem record079_nodes_0 (record079_valid : GraphGrowthInputs.Valid record079.inputs) : Interval (record079.nodeTestValid record079_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record079_supports : record079.Supports := by unfold RawData.Supports; decide +kernel
theorem record079_leaf_0 : Interval record079.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record079_leaves_nodup (j : Fin record079.l) : (record079.leaf j).Nodup :=
  record079.leaves_nodup_of_interval record079_leaf_0 j
theorem record079_checked (record079_valid : GraphGrowthInputs.Valid record079.inputs) : Interval (record079.nodeTestValid record079_valid) 0 1 :=
  (record079_nodes_0 record079_valid)
theorem record079_raw_node_checks (record079_valid : GraphGrowthInputs.Valid record079.inputs) (i : Fin record079.t) :
    RawGraphConditionedGrowth.nodeCheck (record079.inputs.problem record079_valid)
      record079.maps record079.leaf record079.nodes i = true :=
  record079.node_checks_valid record079_valid record079_supports (record079_checked record079_valid) i
#print axioms record079_raw_node_checks
theorem record080_nodes_0 (record080_valid : GraphGrowthInputs.Valid record080.inputs) : Interval (record080.nodeTestValid record080_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record080_supports : record080.Supports := by unfold RawData.Supports; decide +kernel
theorem record080_leaf_0 : Interval record080.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record080_leaves_nodup (j : Fin record080.l) : (record080.leaf j).Nodup :=
  record080.leaves_nodup_of_interval record080_leaf_0 j
theorem record080_checked (record080_valid : GraphGrowthInputs.Valid record080.inputs) : Interval (record080.nodeTestValid record080_valid) 0 1 :=
  (record080_nodes_0 record080_valid)
theorem record080_raw_node_checks (record080_valid : GraphGrowthInputs.Valid record080.inputs) (i : Fin record080.t) :
    RawGraphConditionedGrowth.nodeCheck (record080.inputs.problem record080_valid)
      record080.maps record080.leaf record080.nodes i = true :=
  record080.node_checks_valid record080_valid record080_supports (record080_checked record080_valid) i
#print axioms record080_raw_node_checks
theorem record081_nodes_0 (record081_valid : GraphGrowthInputs.Valid record081.inputs) : Interval (record081.nodeTestValid record081_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record081_supports : record081.Supports := by unfold RawData.Supports; decide +kernel
theorem record081_leaf_0 : Interval record081.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record081_leaves_nodup (j : Fin record081.l) : (record081.leaf j).Nodup :=
  record081.leaves_nodup_of_interval record081_leaf_0 j
theorem record081_checked (record081_valid : GraphGrowthInputs.Valid record081.inputs) : Interval (record081.nodeTestValid record081_valid) 0 1 :=
  (record081_nodes_0 record081_valid)
theorem record081_raw_node_checks (record081_valid : GraphGrowthInputs.Valid record081.inputs) (i : Fin record081.t) :
    RawGraphConditionedGrowth.nodeCheck (record081.inputs.problem record081_valid)
      record081.maps record081.leaf record081.nodes i = true :=
  record081.node_checks_valid record081_valid record081_supports (record081_checked record081_valid) i
#print axioms record081_raw_node_checks
theorem record082_nodes_0 (record082_valid : GraphGrowthInputs.Valid record082.inputs) : Interval (record082.nodeTestValid record082_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record082_supports : record082.Supports := by unfold RawData.Supports; decide +kernel
theorem record082_leaf_0 : Interval record082.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record082_leaves_nodup (j : Fin record082.l) : (record082.leaf j).Nodup :=
  record082.leaves_nodup_of_interval record082_leaf_0 j
theorem record082_checked (record082_valid : GraphGrowthInputs.Valid record082.inputs) : Interval (record082.nodeTestValid record082_valid) 0 1 :=
  (record082_nodes_0 record082_valid)
theorem record082_raw_node_checks (record082_valid : GraphGrowthInputs.Valid record082.inputs) (i : Fin record082.t) :
    RawGraphConditionedGrowth.nodeCheck (record082.inputs.problem record082_valid)
      record082.maps record082.leaf record082.nodes i = true :=
  record082.node_checks_valid record082_valid record082_supports (record082_checked record082_valid) i
#print axioms record082_raw_node_checks
theorem record083_nodes_0 (record083_valid : GraphGrowthInputs.Valid record083.inputs) : Interval (record083.nodeTestValid record083_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record083_supports : record083.Supports := by unfold RawData.Supports; decide +kernel
theorem record083_leaf_0 : Interval record083.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record083_leaves_nodup (j : Fin record083.l) : (record083.leaf j).Nodup :=
  record083.leaves_nodup_of_interval record083_leaf_0 j
theorem record083_checked (record083_valid : GraphGrowthInputs.Valid record083.inputs) : Interval (record083.nodeTestValid record083_valid) 0 1 :=
  (record083_nodes_0 record083_valid)
theorem record083_raw_node_checks (record083_valid : GraphGrowthInputs.Valid record083.inputs) (i : Fin record083.t) :
    RawGraphConditionedGrowth.nodeCheck (record083.inputs.problem record083_valid)
      record083.maps record083.leaf record083.nodes i = true :=
  record083.node_checks_valid record083_valid record083_supports (record083_checked record083_valid) i
#print axioms record083_raw_node_checks
theorem record084_nodes_0 (record084_valid : GraphGrowthInputs.Valid record084.inputs) : Interval (record084.nodeTestValid record084_valid) 0 32 :=
  interval_of_check _ 0 32 (by decide_kernel_context)
theorem record084_nodes_32 (record084_valid : GraphGrowthInputs.Valid record084.inputs) : Interval (record084.nodeTestValid record084_valid) 32 61 :=
  interval_of_check _ 32 29 (by decide_kernel_context)
theorem record084_supports : record084.Supports := by unfold RawData.Supports; decide +kernel
theorem record084_leaf_0 : Interval record084.leafTest 0 3 :=
  interval_of_check _ 0 3 (by decide +kernel)
theorem record084_leaves_nodup (j : Fin record084.l) : (record084.leaf j).Nodup :=
  record084.leaves_nodup_of_interval record084_leaf_0 j
theorem record084_checked (record084_valid : GraphGrowthInputs.Valid record084.inputs) : Interval (record084.nodeTestValid record084_valid) 0 61 :=
  (FiniteChecks.interval_append (record084.nodeTestValid record084_valid) 0 32 61
  (record084_nodes_0 record084_valid)
  (record084_nodes_32 record084_valid))
theorem record084_raw_node_checks (record084_valid : GraphGrowthInputs.Valid record084.inputs) (i : Fin record084.t) :
    RawGraphConditionedGrowth.nodeCheck (record084.inputs.problem record084_valid)
      record084.maps record084.leaf record084.nodes i = true :=
  record084.node_checks_valid record084_valid record084_supports (record084_checked record084_valid) i
#print axioms record084_raw_node_checks
theorem record085_nodes_0 (record085_valid : GraphGrowthInputs.Valid record085.inputs) : Interval (record085.nodeTestValid record085_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record085_supports : record085.Supports := by unfold RawData.Supports; decide +kernel
theorem record085_leaf_0 : Interval record085.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record085_leaves_nodup (j : Fin record085.l) : (record085.leaf j).Nodup :=
  record085.leaves_nodup_of_interval record085_leaf_0 j
theorem record085_checked (record085_valid : GraphGrowthInputs.Valid record085.inputs) : Interval (record085.nodeTestValid record085_valid) 0 1 :=
  (record085_nodes_0 record085_valid)
theorem record085_raw_node_checks (record085_valid : GraphGrowthInputs.Valid record085.inputs) (i : Fin record085.t) :
    RawGraphConditionedGrowth.nodeCheck (record085.inputs.problem record085_valid)
      record085.maps record085.leaf record085.nodes i = true :=
  record085.node_checks_valid record085_valid record085_supports (record085_checked record085_valid) i
#print axioms record085_raw_node_checks
theorem record086_nodes_0 (record086_valid : GraphGrowthInputs.Valid record086.inputs) : Interval (record086.nodeTestValid record086_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record086_supports : record086.Supports := by unfold RawData.Supports; decide +kernel
theorem record086_leaf_0 : Interval record086.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record086_leaves_nodup (j : Fin record086.l) : (record086.leaf j).Nodup :=
  record086.leaves_nodup_of_interval record086_leaf_0 j
theorem record086_checked (record086_valid : GraphGrowthInputs.Valid record086.inputs) : Interval (record086.nodeTestValid record086_valid) 0 1 :=
  (record086_nodes_0 record086_valid)
theorem record086_raw_node_checks (record086_valid : GraphGrowthInputs.Valid record086.inputs) (i : Fin record086.t) :
    RawGraphConditionedGrowth.nodeCheck (record086.inputs.problem record086_valid)
      record086.maps record086.leaf record086.nodes i = true :=
  record086.node_checks_valid record086_valid record086_supports (record086_checked record086_valid) i
#print axioms record086_raw_node_checks
theorem record087_nodes_0 (record087_valid : GraphGrowthInputs.Valid record087.inputs) : Interval (record087.nodeTestValid record087_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record087_supports : record087.Supports := by unfold RawData.Supports; decide +kernel
theorem record087_leaf_0 : Interval record087.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record087_leaves_nodup (j : Fin record087.l) : (record087.leaf j).Nodup :=
  record087.leaves_nodup_of_interval record087_leaf_0 j
theorem record087_checked (record087_valid : GraphGrowthInputs.Valid record087.inputs) : Interval (record087.nodeTestValid record087_valid) 0 1 :=
  (record087_nodes_0 record087_valid)
theorem record087_raw_node_checks (record087_valid : GraphGrowthInputs.Valid record087.inputs) (i : Fin record087.t) :
    RawGraphConditionedGrowth.nodeCheck (record087.inputs.problem record087_valid)
      record087.maps record087.leaf record087.nodes i = true :=
  record087.node_checks_valid record087_valid record087_supports (record087_checked record087_valid) i
#print axioms record087_raw_node_checks
theorem record088_nodes_0 (record088_valid : GraphGrowthInputs.Valid record088.inputs) : Interval (record088.nodeTestValid record088_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record088_supports : record088.Supports := by unfold RawData.Supports; decide +kernel
theorem record088_leaf_0 : Interval record088.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record088_leaves_nodup (j : Fin record088.l) : (record088.leaf j).Nodup :=
  record088.leaves_nodup_of_interval record088_leaf_0 j
theorem record088_checked (record088_valid : GraphGrowthInputs.Valid record088.inputs) : Interval (record088.nodeTestValid record088_valid) 0 1 :=
  (record088_nodes_0 record088_valid)
theorem record088_raw_node_checks (record088_valid : GraphGrowthInputs.Valid record088.inputs) (i : Fin record088.t) :
    RawGraphConditionedGrowth.nodeCheck (record088.inputs.problem record088_valid)
      record088.maps record088.leaf record088.nodes i = true :=
  record088.node_checks_valid record088_valid record088_supports (record088_checked record088_valid) i
#print axioms record088_raw_node_checks
theorem record089_nodes_0 (record089_valid : GraphGrowthInputs.Valid record089.inputs) : Interval (record089.nodeTestValid record089_valid) 0 4 :=
  interval_of_check _ 0 4 (by decide_kernel_context)
theorem record089_supports : record089.Supports := by unfold RawData.Supports; decide +kernel
theorem record089_leaf_0 : Interval record089.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record089_leaves_nodup (j : Fin record089.l) : (record089.leaf j).Nodup :=
  record089.leaves_nodup_of_interval record089_leaf_0 j
theorem record089_checked (record089_valid : GraphGrowthInputs.Valid record089.inputs) : Interval (record089.nodeTestValid record089_valid) 0 4 :=
  (record089_nodes_0 record089_valid)
theorem record089_raw_node_checks (record089_valid : GraphGrowthInputs.Valid record089.inputs) (i : Fin record089.t) :
    RawGraphConditionedGrowth.nodeCheck (record089.inputs.problem record089_valid)
      record089.maps record089.leaf record089.nodes i = true :=
  record089.node_checks_valid record089_valid record089_supports (record089_checked record089_valid) i
#print axioms record089_raw_node_checks
theorem record090_nodes_0 (record090_valid : GraphGrowthInputs.Valid record090.inputs) : Interval (record090.nodeTestValid record090_valid) 0 2 :=
  interval_of_check _ 0 2 (by decide_kernel_context)
theorem record090_supports : record090.Supports := by unfold RawData.Supports; decide +kernel
theorem record090_leaf_0 : Interval record090.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record090_leaves_nodup (j : Fin record090.l) : (record090.leaf j).Nodup :=
  record090.leaves_nodup_of_interval record090_leaf_0 j
theorem record090_checked (record090_valid : GraphGrowthInputs.Valid record090.inputs) : Interval (record090.nodeTestValid record090_valid) 0 2 :=
  (record090_nodes_0 record090_valid)
theorem record090_raw_node_checks (record090_valid : GraphGrowthInputs.Valid record090.inputs) (i : Fin record090.t) :
    RawGraphConditionedGrowth.nodeCheck (record090.inputs.problem record090_valid)
      record090.maps record090.leaf record090.nodes i = true :=
  record090.node_checks_valid record090_valid record090_supports (record090_checked record090_valid) i
#print axioms record090_raw_node_checks
theorem record091_nodes_0 (record091_valid : GraphGrowthInputs.Valid record091.inputs) : Interval (record091.nodeTestValid record091_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record091_supports : record091.Supports := by unfold RawData.Supports; decide +kernel
theorem record091_leaf_0 : Interval record091.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record091_leaves_nodup (j : Fin record091.l) : (record091.leaf j).Nodup :=
  record091.leaves_nodup_of_interval record091_leaf_0 j
theorem record091_checked (record091_valid : GraphGrowthInputs.Valid record091.inputs) : Interval (record091.nodeTestValid record091_valid) 0 1 :=
  (record091_nodes_0 record091_valid)
theorem record091_raw_node_checks (record091_valid : GraphGrowthInputs.Valid record091.inputs) (i : Fin record091.t) :
    RawGraphConditionedGrowth.nodeCheck (record091.inputs.problem record091_valid)
      record091.maps record091.leaf record091.nodes i = true :=
  record091.node_checks_valid record091_valid record091_supports (record091_checked record091_valid) i
#print axioms record091_raw_node_checks
theorem record092_nodes_0 (record092_valid : GraphGrowthInputs.Valid record092.inputs) : Interval (record092.nodeTestValid record092_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record092_supports : record092.Supports := by unfold RawData.Supports; decide +kernel
theorem record092_leaf_0 : Interval record092.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record092_leaves_nodup (j : Fin record092.l) : (record092.leaf j).Nodup :=
  record092.leaves_nodup_of_interval record092_leaf_0 j
theorem record092_checked (record092_valid : GraphGrowthInputs.Valid record092.inputs) : Interval (record092.nodeTestValid record092_valid) 0 1 :=
  (record092_nodes_0 record092_valid)
theorem record092_raw_node_checks (record092_valid : GraphGrowthInputs.Valid record092.inputs) (i : Fin record092.t) :
    RawGraphConditionedGrowth.nodeCheck (record092.inputs.problem record092_valid)
      record092.maps record092.leaf record092.nodes i = true :=
  record092.node_checks_valid record092_valid record092_supports (record092_checked record092_valid) i
#print axioms record092_raw_node_checks
theorem record093_nodes_0 (record093_valid : GraphGrowthInputs.Valid record093.inputs) : Interval (record093.nodeTestValid record093_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record093_supports : record093.Supports := by unfold RawData.Supports; decide +kernel
theorem record093_leaf_0 : Interval record093.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record093_leaves_nodup (j : Fin record093.l) : (record093.leaf j).Nodup :=
  record093.leaves_nodup_of_interval record093_leaf_0 j
theorem record093_checked (record093_valid : GraphGrowthInputs.Valid record093.inputs) : Interval (record093.nodeTestValid record093_valid) 0 1 :=
  (record093_nodes_0 record093_valid)
theorem record093_raw_node_checks (record093_valid : GraphGrowthInputs.Valid record093.inputs) (i : Fin record093.t) :
    RawGraphConditionedGrowth.nodeCheck (record093.inputs.problem record093_valid)
      record093.maps record093.leaf record093.nodes i = true :=
  record093.node_checks_valid record093_valid record093_supports (record093_checked record093_valid) i
#print axioms record093_raw_node_checks
theorem record094_nodes_0 (record094_valid : GraphGrowthInputs.Valid record094.inputs) : Interval (record094.nodeTestValid record094_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record094_supports : record094.Supports := by unfold RawData.Supports; decide +kernel
theorem record094_leaf_0 : Interval record094.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record094_leaves_nodup (j : Fin record094.l) : (record094.leaf j).Nodup :=
  record094.leaves_nodup_of_interval record094_leaf_0 j
theorem record094_checked (record094_valid : GraphGrowthInputs.Valid record094.inputs) : Interval (record094.nodeTestValid record094_valid) 0 1 :=
  (record094_nodes_0 record094_valid)
theorem record094_raw_node_checks (record094_valid : GraphGrowthInputs.Valid record094.inputs) (i : Fin record094.t) :
    RawGraphConditionedGrowth.nodeCheck (record094.inputs.problem record094_valid)
      record094.maps record094.leaf record094.nodes i = true :=
  record094.node_checks_valid record094_valid record094_supports (record094_checked record094_valid) i
#print axioms record094_raw_node_checks
theorem record095_nodes_0 (record095_valid : GraphGrowthInputs.Valid record095.inputs) : Interval (record095.nodeTestValid record095_valid) 0 2 :=
  interval_of_check _ 0 2 (by decide_kernel_context)
theorem record095_supports : record095.Supports := by unfold RawData.Supports; decide +kernel
theorem record095_leaf_0 : Interval record095.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record095_leaves_nodup (j : Fin record095.l) : (record095.leaf j).Nodup :=
  record095.leaves_nodup_of_interval record095_leaf_0 j
theorem record095_checked (record095_valid : GraphGrowthInputs.Valid record095.inputs) : Interval (record095.nodeTestValid record095_valid) 0 2 :=
  (record095_nodes_0 record095_valid)
theorem record095_raw_node_checks (record095_valid : GraphGrowthInputs.Valid record095.inputs) (i : Fin record095.t) :
    RawGraphConditionedGrowth.nodeCheck (record095.inputs.problem record095_valid)
      record095.maps record095.leaf record095.nodes i = true :=
  record095.node_checks_valid record095_valid record095_supports (record095_checked record095_valid) i
#print axioms record095_raw_node_checks
theorem record096_nodes_0 (record096_valid : GraphGrowthInputs.Valid record096.inputs) : Interval (record096.nodeTestValid record096_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record096_supports : record096.Supports := by unfold RawData.Supports; decide +kernel
theorem record096_leaf_0 : Interval record096.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record096_leaves_nodup (j : Fin record096.l) : (record096.leaf j).Nodup :=
  record096.leaves_nodup_of_interval record096_leaf_0 j
theorem record096_checked (record096_valid : GraphGrowthInputs.Valid record096.inputs) : Interval (record096.nodeTestValid record096_valid) 0 1 :=
  (record096_nodes_0 record096_valid)
theorem record096_raw_node_checks (record096_valid : GraphGrowthInputs.Valid record096.inputs) (i : Fin record096.t) :
    RawGraphConditionedGrowth.nodeCheck (record096.inputs.problem record096_valid)
      record096.maps record096.leaf record096.nodes i = true :=
  record096.node_checks_valid record096_valid record096_supports (record096_checked record096_valid) i
#print axioms record096_raw_node_checks
theorem record097_nodes_0 (record097_valid : GraphGrowthInputs.Valid record097.inputs) : Interval (record097.nodeTestValid record097_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record097_supports : record097.Supports := by unfold RawData.Supports; decide +kernel
theorem record097_leaf_0 : Interval record097.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record097_leaves_nodup (j : Fin record097.l) : (record097.leaf j).Nodup :=
  record097.leaves_nodup_of_interval record097_leaf_0 j
theorem record097_checked (record097_valid : GraphGrowthInputs.Valid record097.inputs) : Interval (record097.nodeTestValid record097_valid) 0 1 :=
  (record097_nodes_0 record097_valid)
theorem record097_raw_node_checks (record097_valid : GraphGrowthInputs.Valid record097.inputs) (i : Fin record097.t) :
    RawGraphConditionedGrowth.nodeCheck (record097.inputs.problem record097_valid)
      record097.maps record097.leaf record097.nodes i = true :=
  record097.node_checks_valid record097_valid record097_supports (record097_checked record097_valid) i
#print axioms record097_raw_node_checks
theorem record098_nodes_0 (record098_valid : GraphGrowthInputs.Valid record098.inputs) : Interval (record098.nodeTestValid record098_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record098_supports : record098.Supports := by unfold RawData.Supports; decide +kernel
theorem record098_leaf_0 : Interval record098.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record098_leaves_nodup (j : Fin record098.l) : (record098.leaf j).Nodup :=
  record098.leaves_nodup_of_interval record098_leaf_0 j
theorem record098_checked (record098_valid : GraphGrowthInputs.Valid record098.inputs) : Interval (record098.nodeTestValid record098_valid) 0 1 :=
  (record098_nodes_0 record098_valid)
theorem record098_raw_node_checks (record098_valid : GraphGrowthInputs.Valid record098.inputs) (i : Fin record098.t) :
    RawGraphConditionedGrowth.nodeCheck (record098.inputs.problem record098_valid)
      record098.maps record098.leaf record098.nodes i = true :=
  record098.node_checks_valid record098_valid record098_supports (record098_checked record098_valid) i
#print axioms record098_raw_node_checks
theorem record099_nodes_0 (record099_valid : GraphGrowthInputs.Valid record099.inputs) : Interval (record099.nodeTestValid record099_valid) 0 1 :=
  interval_of_check _ 0 1 (by decide_kernel_context)
theorem record099_supports : record099.Supports := by unfold RawData.Supports; decide +kernel
theorem record099_leaf_0 : Interval record099.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record099_leaves_nodup (j : Fin record099.l) : (record099.leaf j).Nodup :=
  record099.leaves_nodup_of_interval record099_leaf_0 j
theorem record099_checked (record099_valid : GraphGrowthInputs.Valid record099.inputs) : Interval (record099.nodeTestValid record099_valid) 0 1 :=
  (record099_nodes_0 record099_valid)
theorem record099_raw_node_checks (record099_valid : GraphGrowthInputs.Valid record099.inputs) (i : Fin record099.t) :
    RawGraphConditionedGrowth.nodeCheck (record099.inputs.problem record099_valid)
      record099.maps record099.leaf record099.nodes i = true :=
  record099.node_checks_valid record099_valid record099_supports (record099_checked record099_valid) i
#print axioms record099_raw_node_checks

end Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00018
