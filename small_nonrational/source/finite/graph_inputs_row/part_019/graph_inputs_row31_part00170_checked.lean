module
prelude
public import GraphInputsRow31Part00170Data
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00170
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
theorem record000_nodes_352 (record000_valid : GraphGrowthInputs.Valid record000.inputs) : Interval (record000.nodeTestValid record000_valid) 352 384 :=
  interval_of_check _ 352 32 (by decide_kernel_context)
theorem record000_nodes_384 (record000_valid : GraphGrowthInputs.Valid record000.inputs) : Interval (record000.nodeTestValid record000_valid) 384 416 :=
  interval_of_check _ 384 32 (by decide_kernel_context)
theorem record000_nodes_416 (record000_valid : GraphGrowthInputs.Valid record000.inputs) : Interval (record000.nodeTestValid record000_valid) 416 448 :=
  interval_of_check _ 416 32 (by decide_kernel_context)
theorem record000_nodes_448 (record000_valid : GraphGrowthInputs.Valid record000.inputs) : Interval (record000.nodeTestValid record000_valid) 448 480 :=
  interval_of_check _ 448 32 (by decide_kernel_context)
theorem record000_nodes_480 (record000_valid : GraphGrowthInputs.Valid record000.inputs) : Interval (record000.nodeTestValid record000_valid) 480 512 :=
  interval_of_check _ 480 32 (by decide_kernel_context)
theorem record000_nodes_512 (record000_valid : GraphGrowthInputs.Valid record000.inputs) : Interval (record000.nodeTestValid record000_valid) 512 544 :=
  interval_of_check _ 512 32 (by decide_kernel_context)
theorem record000_nodes_544 (record000_valid : GraphGrowthInputs.Valid record000.inputs) : Interval (record000.nodeTestValid record000_valid) 544 576 :=
  interval_of_check _ 544 32 (by decide_kernel_context)
theorem record000_nodes_576 (record000_valid : GraphGrowthInputs.Valid record000.inputs) : Interval (record000.nodeTestValid record000_valid) 576 608 :=
  interval_of_check _ 576 32 (by decide_kernel_context)
theorem record000_nodes_608 (record000_valid : GraphGrowthInputs.Valid record000.inputs) : Interval (record000.nodeTestValid record000_valid) 608 615 :=
  interval_of_check _ 608 7 (by decide_kernel_context)
theorem record000_supports : record000.Supports := by unfold RawData.Supports; decide +kernel
theorem record000_leaf_0 : Interval record000.leafTest 0 2 :=
  interval_of_check _ 0 2 (by decide +kernel)
theorem record000_leaves_nodup (j : Fin record000.l) : (record000.leaf j).Nodup :=
  record000.leaves_nodup_of_interval record000_leaf_0 j
theorem record000_checked (record000_valid : GraphGrowthInputs.Valid record000.inputs) : Interval (record000.nodeTestValid record000_valid) 0 615 :=
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 0 320 615
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 0 160 320
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 0 64 160
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 0 32 64
  (record000_nodes_0 record000_valid)
  (record000_nodes_32 record000_valid))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 64 96 160
  (record000_nodes_64 record000_valid)
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 96 128 160
  (record000_nodes_96 record000_valid)
  (record000_nodes_128 record000_valid))))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 160 224 320
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 160 192 224
  (record000_nodes_160 record000_valid)
  (record000_nodes_192 record000_valid))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 224 256 320
  (record000_nodes_224 record000_valid)
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 256 288 320
  (record000_nodes_256 record000_valid)
  (record000_nodes_288 record000_valid)))))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 320 480 615
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 320 384 480
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 320 352 384
  (record000_nodes_320 record000_valid)
  (record000_nodes_352 record000_valid))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 384 416 480
  (record000_nodes_384 record000_valid)
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 416 448 480
  (record000_nodes_416 record000_valid)
  (record000_nodes_448 record000_valid))))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 480 544 615
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 480 512 544
  (record000_nodes_480 record000_valid)
  (record000_nodes_512 record000_valid))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 544 576 615
  (record000_nodes_544 record000_valid)
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 576 608 615
  (record000_nodes_576 record000_valid)
  (record000_nodes_608 record000_valid))))))
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
theorem record001_nodes_96 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 96 121 :=
  interval_of_check _ 96 25 (by decide_kernel_context)
theorem record001_supports : record001.Supports := by unfold RawData.Supports; decide +kernel
theorem record001_leaf_0 : Interval record001.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record001_leaves_nodup (j : Fin record001.l) : (record001.leaf j).Nodup :=
  record001.leaves_nodup_of_interval record001_leaf_0 j
theorem record001_checked (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 0 121 :=
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 0 64 121
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 0 32 64
  (record001_nodes_0 record001_valid)
  (record001_nodes_32 record001_valid))
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 64 96 121
  (record001_nodes_64 record001_valid)
  (record001_nodes_96 record001_valid)))
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
theorem record002_nodes_416 (record002_valid : GraphGrowthInputs.Valid record002.inputs) : Interval (record002.nodeTestValid record002_valid) 416 448 :=
  interval_of_check _ 416 32 (by decide_kernel_context)
theorem record002_nodes_448 (record002_valid : GraphGrowthInputs.Valid record002.inputs) : Interval (record002.nodeTestValid record002_valid) 448 480 :=
  interval_of_check _ 448 32 (by decide_kernel_context)
theorem record002_nodes_480 (record002_valid : GraphGrowthInputs.Valid record002.inputs) : Interval (record002.nodeTestValid record002_valid) 480 512 :=
  interval_of_check _ 480 32 (by decide_kernel_context)
theorem record002_nodes_512 (record002_valid : GraphGrowthInputs.Valid record002.inputs) : Interval (record002.nodeTestValid record002_valid) 512 544 :=
  interval_of_check _ 512 32 (by decide_kernel_context)
theorem record002_nodes_544 (record002_valid : GraphGrowthInputs.Valid record002.inputs) : Interval (record002.nodeTestValid record002_valid) 544 576 :=
  interval_of_check _ 544 32 (by decide_kernel_context)
theorem record002_nodes_576 (record002_valid : GraphGrowthInputs.Valid record002.inputs) : Interval (record002.nodeTestValid record002_valid) 576 595 :=
  interval_of_check _ 576 19 (by decide_kernel_context)
theorem record002_supports : record002.Supports := by unfold RawData.Supports; decide +kernel
theorem record002_leaf_0 : Interval record002.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record002_leaves_nodup (j : Fin record002.l) : (record002.leaf j).Nodup :=
  record002.leaves_nodup_of_interval record002_leaf_0 j
theorem record002_checked (record002_valid : GraphGrowthInputs.Valid record002.inputs) : Interval (record002.nodeTestValid record002_valid) 0 595 :=
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 0 288 595
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 0 128 288
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 0 64 128
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 0 32 64
  (record002_nodes_0 record002_valid)
  (record002_nodes_32 record002_valid))
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 64 96 128
  (record002_nodes_64 record002_valid)
  (record002_nodes_96 record002_valid)))
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 128 192 288
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 128 160 192
  (record002_nodes_128 record002_valid)
  (record002_nodes_160 record002_valid))
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 192 224 288
  (record002_nodes_192 record002_valid)
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 224 256 288
  (record002_nodes_224 record002_valid)
  (record002_nodes_256 record002_valid)))))
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 288 448 595
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 288 352 448
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 288 320 352
  (record002_nodes_288 record002_valid)
  (record002_nodes_320 record002_valid))
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 352 384 448
  (record002_nodes_352 record002_valid)
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 384 416 448
  (record002_nodes_384 record002_valid)
  (record002_nodes_416 record002_valid))))
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 448 512 595
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 448 480 512
  (record002_nodes_448 record002_valid)
  (record002_nodes_480 record002_valid))
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 512 544 595
  (record002_nodes_512 record002_valid)
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 544 576 595
  (record002_nodes_544 record002_valid)
  (record002_nodes_576 record002_valid))))))
theorem record002_raw_node_checks (record002_valid : GraphGrowthInputs.Valid record002.inputs) (i : Fin record002.t) :
    RawGraphConditionedGrowth.nodeCheck (record002.inputs.problem record002_valid)
      record002.maps record002.leaf record002.nodes i = true :=
  record002.node_checks_valid record002_valid record002_supports (record002_checked record002_valid) i
#print axioms record002_raw_node_checks

end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00170
