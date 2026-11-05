module
prelude
public import GraphInputsRow29Part00031Data
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00031
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
theorem record001_supports : record001.Supports := by unfold RawData.Supports; decide +kernel
theorem record001_leaf_0 : Interval record001.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record001_leaves_nodup (j : Fin record001.l) : (record001.leaf j).Nodup :=
  record001.leaves_nodup_of_interval record001_leaf_0 j
theorem record001_checked (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 0 480 :=
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 0 224 480
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 0 96 224
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 0 32 96
  (record001_nodes_0 record001_valid)
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 32 64 96
  (record001_nodes_32 record001_valid)
  (record001_nodes_64 record001_valid)))
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 96 160 224
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 96 128 160
  (record001_nodes_96 record001_valid)
  (record001_nodes_128 record001_valid))
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 160 192 224
  (record001_nodes_160 record001_valid)
  (record001_nodes_192 record001_valid))))
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 224 352 480
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 224 288 352
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 224 256 288
  (record001_nodes_224 record001_valid)
  (record001_nodes_256 record001_valid))
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 288 320 352
  (record001_nodes_288 record001_valid)
  (record001_nodes_320 record001_valid)))
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 352 416 480
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 352 384 416
  (record001_nodes_352 record001_valid)
  (record001_nodes_384 record001_valid))
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 416 448 480
  (record001_nodes_416 record001_valid)
  (record001_nodes_448 record001_valid)))))
theorem record001_raw_node_checks (record001_valid : GraphGrowthInputs.Valid record001.inputs) (i : Fin record001.t) :
    RawGraphConditionedGrowth.nodeCheck (record001.inputs.problem record001_valid)
      record001.maps record001.leaf record001.nodes i = true :=
  record001.node_checks_valid record001_valid record001_supports (record001_checked record001_valid) i
#print axioms record001_raw_node_checks
theorem record002_nodes_0 (record002_valid : GraphGrowthInputs.Valid record002.inputs) : Interval (record002.nodeTestValid record002_valid) 0 32 :=
  interval_of_check _ 0 32 (by decide_kernel_context)
theorem record002_nodes_32 (record002_valid : GraphGrowthInputs.Valid record002.inputs) : Interval (record002.nodeTestValid record002_valid) 32 46 :=
  interval_of_check _ 32 14 (by decide_kernel_context)
theorem record002_supports : record002.Supports := by unfold RawData.Supports; decide +kernel
theorem record002_leaf_0 : Interval record002.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record002_leaves_nodup (j : Fin record002.l) : (record002.leaf j).Nodup :=
  record002.leaves_nodup_of_interval record002_leaf_0 j
theorem record002_checked (record002_valid : GraphGrowthInputs.Valid record002.inputs) : Interval (record002.nodeTestValid record002_valid) 0 46 :=
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 0 32 46
  (record002_nodes_0 record002_valid)
  (record002_nodes_32 record002_valid))
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
theorem record003_nodes_384 (record003_valid : GraphGrowthInputs.Valid record003.inputs) : Interval (record003.nodeTestValid record003_valid) 384 416 :=
  interval_of_check _ 384 32 (by decide_kernel_context)
theorem record003_nodes_416 (record003_valid : GraphGrowthInputs.Valid record003.inputs) : Interval (record003.nodeTestValid record003_valid) 416 448 :=
  interval_of_check _ 416 32 (by decide_kernel_context)
theorem record003_nodes_448 (record003_valid : GraphGrowthInputs.Valid record003.inputs) : Interval (record003.nodeTestValid record003_valid) 448 480 :=
  interval_of_check _ 448 32 (by decide_kernel_context)
theorem record003_nodes_480 (record003_valid : GraphGrowthInputs.Valid record003.inputs) : Interval (record003.nodeTestValid record003_valid) 480 512 :=
  interval_of_check _ 480 32 (by decide_kernel_context)
theorem record003_nodes_512 (record003_valid : GraphGrowthInputs.Valid record003.inputs) : Interval (record003.nodeTestValid record003_valid) 512 544 :=
  interval_of_check _ 512 32 (by decide_kernel_context)
theorem record003_nodes_544 (record003_valid : GraphGrowthInputs.Valid record003.inputs) : Interval (record003.nodeTestValid record003_valid) 544 562 :=
  interval_of_check _ 544 18 (by decide_kernel_context)
theorem record003_supports : record003.Supports := by unfold RawData.Supports; decide +kernel
theorem record003_leaf_0 : Interval record003.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record003_leaves_nodup (j : Fin record003.l) : (record003.leaf j).Nodup :=
  record003.leaves_nodup_of_interval record003_leaf_0 j
theorem record003_checked (record003_valid : GraphGrowthInputs.Valid record003.inputs) : Interval (record003.nodeTestValid record003_valid) 0 562 :=
  (FiniteChecks.interval_append (record003.nodeTestValid record003_valid) 0 288 562
  (FiniteChecks.interval_append (record003.nodeTestValid record003_valid) 0 128 288
  (FiniteChecks.interval_append (record003.nodeTestValid record003_valid) 0 64 128
  (FiniteChecks.interval_append (record003.nodeTestValid record003_valid) 0 32 64
  (record003_nodes_0 record003_valid)
  (record003_nodes_32 record003_valid))
  (FiniteChecks.interval_append (record003.nodeTestValid record003_valid) 64 96 128
  (record003_nodes_64 record003_valid)
  (record003_nodes_96 record003_valid)))
  (FiniteChecks.interval_append (record003.nodeTestValid record003_valid) 128 192 288
  (FiniteChecks.interval_append (record003.nodeTestValid record003_valid) 128 160 192
  (record003_nodes_128 record003_valid)
  (record003_nodes_160 record003_valid))
  (FiniteChecks.interval_append (record003.nodeTestValid record003_valid) 192 224 288
  (record003_nodes_192 record003_valid)
  (FiniteChecks.interval_append (record003.nodeTestValid record003_valid) 224 256 288
  (record003_nodes_224 record003_valid)
  (record003_nodes_256 record003_valid)))))
  (FiniteChecks.interval_append (record003.nodeTestValid record003_valid) 288 416 562
  (FiniteChecks.interval_append (record003.nodeTestValid record003_valid) 288 352 416
  (FiniteChecks.interval_append (record003.nodeTestValid record003_valid) 288 320 352
  (record003_nodes_288 record003_valid)
  (record003_nodes_320 record003_valid))
  (FiniteChecks.interval_append (record003.nodeTestValid record003_valid) 352 384 416
  (record003_nodes_352 record003_valid)
  (record003_nodes_384 record003_valid)))
  (FiniteChecks.interval_append (record003.nodeTestValid record003_valid) 416 480 562
  (FiniteChecks.interval_append (record003.nodeTestValid record003_valid) 416 448 480
  (record003_nodes_416 record003_valid)
  (record003_nodes_448 record003_valid))
  (FiniteChecks.interval_append (record003.nodeTestValid record003_valid) 480 512 562
  (record003_nodes_480 record003_valid)
  (FiniteChecks.interval_append (record003.nodeTestValid record003_valid) 512 544 562
  (record003_nodes_512 record003_valid)
  (record003_nodes_544 record003_valid))))))
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
theorem record004_nodes_224 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 224 256 :=
  interval_of_check _ 224 32 (by decide_kernel_context)
theorem record004_nodes_256 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 256 288 :=
  interval_of_check _ 256 32 (by decide_kernel_context)
theorem record004_nodes_288 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 288 320 :=
  interval_of_check _ 288 32 (by decide_kernel_context)
theorem record004_nodes_320 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 320 352 :=
  interval_of_check _ 320 32 (by decide_kernel_context)
theorem record004_nodes_352 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 352 384 :=
  interval_of_check _ 352 32 (by decide_kernel_context)
theorem record004_nodes_384 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 384 416 :=
  interval_of_check _ 384 32 (by decide_kernel_context)
theorem record004_nodes_416 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 416 448 :=
  interval_of_check _ 416 32 (by decide_kernel_context)
theorem record004_nodes_448 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 448 480 :=
  interval_of_check _ 448 32 (by decide_kernel_context)
theorem record004_nodes_480 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 480 512 :=
  interval_of_check _ 480 32 (by decide_kernel_context)
theorem record004_nodes_512 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 512 544 :=
  interval_of_check _ 512 32 (by decide_kernel_context)
theorem record004_nodes_544 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 544 576 :=
  interval_of_check _ 544 32 (by decide_kernel_context)
theorem record004_nodes_576 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 576 608 :=
  interval_of_check _ 576 32 (by decide_kernel_context)
theorem record004_nodes_608 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 608 640 :=
  interval_of_check _ 608 32 (by decide_kernel_context)
theorem record004_nodes_640 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 640 672 :=
  interval_of_check _ 640 32 (by decide_kernel_context)
theorem record004_nodes_672 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 672 704 :=
  interval_of_check _ 672 32 (by decide_kernel_context)
theorem record004_nodes_704 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 704 736 :=
  interval_of_check _ 704 32 (by decide_kernel_context)
theorem record004_nodes_736 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 736 768 :=
  interval_of_check _ 736 32 (by decide_kernel_context)
theorem record004_nodes_768 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 768 800 :=
  interval_of_check _ 768 32 (by decide_kernel_context)
theorem record004_nodes_800 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 800 832 :=
  interval_of_check _ 800 32 (by decide_kernel_context)
theorem record004_nodes_832 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 832 864 :=
  interval_of_check _ 832 32 (by decide_kernel_context)
theorem record004_nodes_864 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 864 896 :=
  interval_of_check _ 864 32 (by decide_kernel_context)
theorem record004_nodes_896 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 896 928 :=
  interval_of_check _ 896 32 (by decide_kernel_context)
theorem record004_nodes_928 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 928 960 :=
  interval_of_check _ 928 32 (by decide_kernel_context)
theorem record004_nodes_960 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 960 992 :=
  interval_of_check _ 960 32 (by decide_kernel_context)
theorem record004_nodes_992 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 992 1024 :=
  interval_of_check _ 992 32 (by decide_kernel_context)
theorem record004_nodes_1024 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 1024 1056 :=
  interval_of_check _ 1024 32 (by decide_kernel_context)
theorem record004_nodes_1056 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 1056 1088 :=
  interval_of_check _ 1056 32 (by decide_kernel_context)
theorem record004_nodes_1088 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 1088 1120 :=
  interval_of_check _ 1088 32 (by decide_kernel_context)
theorem record004_nodes_1120 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 1120 1152 :=
  interval_of_check _ 1120 32 (by decide_kernel_context)
theorem record004_nodes_1152 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 1152 1184 :=
  interval_of_check _ 1152 32 (by decide_kernel_context)
theorem record004_nodes_1184 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 1184 1216 :=
  interval_of_check _ 1184 32 (by decide_kernel_context)
theorem record004_nodes_1216 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 1216 1248 :=
  interval_of_check _ 1216 32 (by decide_kernel_context)
theorem record004_nodes_1248 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 1248 1280 :=
  interval_of_check _ 1248 32 (by decide_kernel_context)
theorem record004_nodes_1280 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 1280 1312 :=
  interval_of_check _ 1280 32 (by decide_kernel_context)
theorem record004_nodes_1312 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 1312 1344 :=
  interval_of_check _ 1312 32 (by decide_kernel_context)
theorem record004_nodes_1344 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 1344 1376 :=
  interval_of_check _ 1344 32 (by decide_kernel_context)
theorem record004_nodes_1376 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 1376 1408 :=
  interval_of_check _ 1376 32 (by decide_kernel_context)
theorem record004_nodes_1408 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 1408 1440 :=
  interval_of_check _ 1408 32 (by decide_kernel_context)
theorem record004_nodes_1440 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 1440 1472 :=
  interval_of_check _ 1440 32 (by decide_kernel_context)
theorem record004_nodes_1472 (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 1472 1478 :=
  interval_of_check _ 1472 6 (by decide_kernel_context)
theorem record004_supports : record004.Supports := by unfold RawData.Supports; decide +kernel
theorem record004_leaf_0 : Interval record004.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record004_leaves_nodup (j : Fin record004.l) : (record004.leaf j).Nodup :=
  record004.leaves_nodup_of_interval record004_leaf_0 j
theorem record004_checked (record004_valid : GraphGrowthInputs.Valid record004.inputs) : Interval (record004.nodeTestValid record004_valid) 0 1478 :=
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 0 736 1478
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 0 352 736
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 0 160 352
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 0 64 160
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 0 32 64
  (record004_nodes_0 record004_valid)
  (record004_nodes_32 record004_valid))
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 64 96 160
  (record004_nodes_64 record004_valid)
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 96 128 160
  (record004_nodes_96 record004_valid)
  (record004_nodes_128 record004_valid))))
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 160 256 352
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 160 192 256
  (record004_nodes_160 record004_valid)
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 192 224 256
  (record004_nodes_192 record004_valid)
  (record004_nodes_224 record004_valid)))
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 256 288 352
  (record004_nodes_256 record004_valid)
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 288 320 352
  (record004_nodes_288 record004_valid)
  (record004_nodes_320 record004_valid)))))
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 352 544 736
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 352 448 544
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 352 384 448
  (record004_nodes_352 record004_valid)
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 384 416 448
  (record004_nodes_384 record004_valid)
  (record004_nodes_416 record004_valid)))
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 448 480 544
  (record004_nodes_448 record004_valid)
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 480 512 544
  (record004_nodes_480 record004_valid)
  (record004_nodes_512 record004_valid))))
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 544 640 736
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 544 576 640
  (record004_nodes_544 record004_valid)
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 576 608 640
  (record004_nodes_576 record004_valid)
  (record004_nodes_608 record004_valid)))
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 640 672 736
  (record004_nodes_640 record004_valid)
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 672 704 736
  (record004_nodes_672 record004_valid)
  (record004_nodes_704 record004_valid))))))
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 736 1120 1478
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 736 928 1120
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 736 832 928
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 736 768 832
  (record004_nodes_736 record004_valid)
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 768 800 832
  (record004_nodes_768 record004_valid)
  (record004_nodes_800 record004_valid)))
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 832 864 928
  (record004_nodes_832 record004_valid)
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 864 896 928
  (record004_nodes_864 record004_valid)
  (record004_nodes_896 record004_valid))))
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 928 1024 1120
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 928 960 1024
  (record004_nodes_928 record004_valid)
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 960 992 1024
  (record004_nodes_960 record004_valid)
  (record004_nodes_992 record004_valid)))
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 1024 1056 1120
  (record004_nodes_1024 record004_valid)
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 1056 1088 1120
  (record004_nodes_1056 record004_valid)
  (record004_nodes_1088 record004_valid)))))
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 1120 1312 1478
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 1120 1216 1312
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 1120 1152 1216
  (record004_nodes_1120 record004_valid)
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 1152 1184 1216
  (record004_nodes_1152 record004_valid)
  (record004_nodes_1184 record004_valid)))
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 1216 1248 1312
  (record004_nodes_1216 record004_valid)
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 1248 1280 1312
  (record004_nodes_1248 record004_valid)
  (record004_nodes_1280 record004_valid))))
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 1312 1408 1478
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 1312 1344 1408
  (record004_nodes_1312 record004_valid)
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 1344 1376 1408
  (record004_nodes_1344 record004_valid)
  (record004_nodes_1376 record004_valid)))
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 1408 1440 1478
  (record004_nodes_1408 record004_valid)
  (FiniteChecks.interval_append (record004.nodeTestValid record004_valid) 1440 1472 1478
  (record004_nodes_1440 record004_valid)
  (record004_nodes_1472 record004_valid)))))))
theorem record004_raw_node_checks (record004_valid : GraphGrowthInputs.Valid record004.inputs) (i : Fin record004.t) :
    RawGraphConditionedGrowth.nodeCheck (record004.inputs.problem record004_valid)
      record004.maps record004.leaf record004.nodes i = true :=
  record004.node_checks_valid record004_valid record004_supports (record004_checked record004_valid) i
#print axioms record004_raw_node_checks

end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00031
