module
prelude
public import GraphInputsRow31Part00050Data
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00050
open Papers.RationalityTen PackedGraphCertificate FiniteChecks
theorem record000_nodes_0 (record000_valid : GraphGrowthInputs.Valid record000.inputs) : Interval (record000.nodeTestValid record000_valid) 0 32 :=
  interval_of_check _ 0 32 (by decide_kernel_context)
theorem record000_nodes_32 (record000_valid : GraphGrowthInputs.Valid record000.inputs) : Interval (record000.nodeTestValid record000_valid) 32 64 :=
  interval_of_check _ 32 32 (by decide_kernel_context)
theorem record000_nodes_64 (record000_valid : GraphGrowthInputs.Valid record000.inputs) : Interval (record000.nodeTestValid record000_valid) 64 88 :=
  interval_of_check _ 64 24 (by decide_kernel_context)
theorem record000_supports : record000.Supports := by unfold RawData.Supports; decide +kernel
theorem record000_leaf_0 : Interval record000.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record000_leaves_nodup (j : Fin record000.l) : (record000.leaf j).Nodup :=
  record000.leaves_nodup_of_interval record000_leaf_0 j
theorem record000_checked (record000_valid : GraphGrowthInputs.Valid record000.inputs) : Interval (record000.nodeTestValid record000_valid) 0 88 :=
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 0 32 88
  (record000_nodes_0 record000_valid)
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 32 64 88
  (record000_nodes_32 record000_valid)
  (record000_nodes_64 record000_valid)))
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
theorem record001_nodes_288 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 288 320 :=
  interval_of_check _ 288 32 (by decide_kernel_context)
theorem record001_nodes_320 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 320 352 :=
  interval_of_check _ 320 32 (by decide_kernel_context)
theorem record001_nodes_352 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 352 384 :=
  interval_of_check _ 352 32 (by decide_kernel_context)
theorem record001_nodes_384 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 384 416 :=
  interval_of_check _ 384 32 (by decide_kernel_context)
theorem record001_nodes_416 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 416 448 :=
  interval_of_check _ 416 32 (by decide_kernel_context)
theorem record001_nodes_448 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 448 480 :=
  interval_of_check _ 448 32 (by decide_kernel_context)
theorem record001_nodes_480 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 480 512 :=
  interval_of_check _ 480 32 (by decide_kernel_context)
theorem record001_nodes_512 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 512 544 :=
  interval_of_check _ 512 32 (by decide_kernel_context)
theorem record001_nodes_544 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 544 576 :=
  interval_of_check _ 544 32 (by decide_kernel_context)
theorem record001_nodes_576 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 576 608 :=
  interval_of_check _ 576 32 (by decide_kernel_context)
theorem record001_nodes_608 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 608 640 :=
  interval_of_check _ 608 32 (by decide_kernel_context)
theorem record001_nodes_640 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 640 672 :=
  interval_of_check _ 640 32 (by decide_kernel_context)
theorem record001_nodes_672 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 672 704 :=
  interval_of_check _ 672 32 (by decide_kernel_context)
theorem record001_nodes_704 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 704 736 :=
  interval_of_check _ 704 32 (by decide_kernel_context)
theorem record001_nodes_736 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 736 768 :=
  interval_of_check _ 736 32 (by decide_kernel_context)
theorem record001_nodes_768 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 768 800 :=
  interval_of_check _ 768 32 (by decide_kernel_context)
theorem record001_nodes_800 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 800 801 :=
  interval_of_check _ 800 1 (by decide_kernel_context)
theorem record001_supports : record001.Supports := by unfold RawData.Supports; decide +kernel
theorem record001_leaf_0 : Interval record001.leafTest 0 6 :=
  interval_of_check _ 0 6 (by decide +kernel)
theorem record001_leaves_nodup (j : Fin record001.l) : (record001.leaf j).Nodup :=
  record001.leaves_nodup_of_interval record001_leaf_0 j
theorem record001_checked (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 0 801 :=
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 0 416 801
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 0 192 416
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 0 96 192
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 0 32 96
  (record001_nodes_0 record001_valid)
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 32 64 96
  (record001_nodes_32 record001_valid)
  (record001_nodes_64 record001_valid)))
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 96 128 192
  (record001_nodes_96 record001_valid)
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 128 160 192
  (record001_nodes_128 record001_valid)
  (record001_nodes_160 record001_valid))))
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 192 288 416
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 192 224 288
  (record001_nodes_192 record001_valid)
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 224 256 288
  (record001_nodes_224 record001_valid)
  (record001_nodes_256 record001_valid)))
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 288 352 416
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 288 320 352
  (record001_nodes_288 record001_valid)
  (record001_nodes_320 record001_valid))
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 352 384 416
  (record001_nodes_352 record001_valid)
  (record001_nodes_384 record001_valid)))))
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 416 608 801
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 416 512 608
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 416 448 512
  (record001_nodes_416 record001_valid)
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 448 480 512
  (record001_nodes_448 record001_valid)
  (record001_nodes_480 record001_valid)))
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 512 544 608
  (record001_nodes_512 record001_valid)
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 544 576 608
  (record001_nodes_544 record001_valid)
  (record001_nodes_576 record001_valid))))
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 608 704 801
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 608 640 704
  (record001_nodes_608 record001_valid)
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 640 672 704
  (record001_nodes_640 record001_valid)
  (record001_nodes_672 record001_valid)))
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 704 768 801
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 704 736 768
  (record001_nodes_704 record001_valid)
  (record001_nodes_736 record001_valid))
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 768 800 801
  (record001_nodes_768 record001_valid)
  (record001_nodes_800 record001_valid))))))
theorem record001_raw_node_checks (record001_valid : GraphGrowthInputs.Valid record001.inputs) (i : Fin record001.t) :
    RawGraphConditionedGrowth.nodeCheck (record001.inputs.problem record001_valid)
      record001.maps record001.leaf record001.nodes i = true :=
  record001.node_checks_valid record001_valid record001_supports (record001_checked record001_valid) i
#print axioms record001_raw_node_checks
theorem record002_nodes_0 (record002_valid : GraphGrowthInputs.Valid record002.inputs) : Interval (record002.nodeTestValid record002_valid) 0 29 :=
  interval_of_check _ 0 29 (by decide_kernel_context)
theorem record002_supports : record002.Supports := by unfold RawData.Supports; decide +kernel
theorem record002_leaf_0 : Interval record002.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record002_leaves_nodup (j : Fin record002.l) : (record002.leaf j).Nodup :=
  record002.leaves_nodup_of_interval record002_leaf_0 j
theorem record002_checked (record002_valid : GraphGrowthInputs.Valid record002.inputs) : Interval (record002.nodeTestValid record002_valid) 0 29 :=
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
theorem record003_nodes_320 (record003_valid : GraphGrowthInputs.Valid record003.inputs) : Interval (record003.nodeTestValid record003_valid) 320 330 :=
  interval_of_check _ 320 10 (by decide_kernel_context)
theorem record003_supports : record003.Supports := by unfold RawData.Supports; decide +kernel
theorem record003_leaf_0 : Interval record003.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record003_leaves_nodup (j : Fin record003.l) : (record003.leaf j).Nodup :=
  record003.leaves_nodup_of_interval record003_leaf_0 j
theorem record003_checked (record003_valid : GraphGrowthInputs.Valid record003.inputs) : Interval (record003.nodeTestValid record003_valid) 0 330 :=
  (FiniteChecks.interval_append (record003.nodeTestValid record003_valid) 0 160 330
  (FiniteChecks.interval_append (record003.nodeTestValid record003_valid) 0 64 160
  (FiniteChecks.interval_append (record003.nodeTestValid record003_valid) 0 32 64
  (record003_nodes_0 record003_valid)
  (record003_nodes_32 record003_valid))
  (FiniteChecks.interval_append (record003.nodeTestValid record003_valid) 64 96 160
  (record003_nodes_64 record003_valid)
  (FiniteChecks.interval_append (record003.nodeTestValid record003_valid) 96 128 160
  (record003_nodes_96 record003_valid)
  (record003_nodes_128 record003_valid))))
  (FiniteChecks.interval_append (record003.nodeTestValid record003_valid) 160 256 330
  (FiniteChecks.interval_append (record003.nodeTestValid record003_valid) 160 192 256
  (record003_nodes_160 record003_valid)
  (FiniteChecks.interval_append (record003.nodeTestValid record003_valid) 192 224 256
  (record003_nodes_192 record003_valid)
  (record003_nodes_224 record003_valid)))
  (FiniteChecks.interval_append (record003.nodeTestValid record003_valid) 256 288 330
  (record003_nodes_256 record003_valid)
  (FiniteChecks.interval_append (record003.nodeTestValid record003_valid) 288 320 330
  (record003_nodes_288 record003_valid)
  (record003_nodes_320 record003_valid)))))
theorem record003_raw_node_checks (record003_valid : GraphGrowthInputs.Valid record003.inputs) (i : Fin record003.t) :
    RawGraphConditionedGrowth.nodeCheck (record003.inputs.problem record003_valid)
      record003.maps record003.leaf record003.nodes i = true :=
  record003.node_checks_valid record003_valid record003_supports (record003_checked record003_valid) i
#print axioms record003_raw_node_checks

end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00050
