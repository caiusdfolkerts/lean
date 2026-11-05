module
prelude
public import GraphInputsRow31Part00032Data
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00032
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
theorem record000_nodes_448 (record000_valid : GraphGrowthInputs.Valid record000.inputs) : Interval (record000.nodeTestValid record000_valid) 448 472 :=
  interval_of_check _ 448 24 (by decide_kernel_context)
theorem record000_supports : record000.Supports := by unfold RawData.Supports; decide +kernel
theorem record000_leaf_0 : Interval record000.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record000_leaves_nodup (j : Fin record000.l) : (record000.leaf j).Nodup :=
  record000.leaves_nodup_of_interval record000_leaf_0 j
theorem record000_checked (record000_valid : GraphGrowthInputs.Valid record000.inputs) : Interval (record000.nodeTestValid record000_valid) 0 472 :=
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 0 224 472
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 0 96 224
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 0 32 96
  (record000_nodes_0 record000_valid)
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 32 64 96
  (record000_nodes_32 record000_valid)
  (record000_nodes_64 record000_valid)))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 96 160 224
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 96 128 160
  (record000_nodes_96 record000_valid)
  (record000_nodes_128 record000_valid))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 160 192 224
  (record000_nodes_160 record000_valid)
  (record000_nodes_192 record000_valid))))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 224 352 472
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 224 288 352
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 224 256 288
  (record000_nodes_224 record000_valid)
  (record000_nodes_256 record000_valid))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 288 320 352
  (record000_nodes_288 record000_valid)
  (record000_nodes_320 record000_valid)))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 352 416 472
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 352 384 416
  (record000_nodes_352 record000_valid)
  (record000_nodes_384 record000_valid))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 416 448 472
  (record000_nodes_416 record000_valid)
  (record000_nodes_448 record000_valid)))))
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
theorem record001_nodes_704 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 704 731 :=
  interval_of_check _ 704 27 (by decide_kernel_context)
theorem record001_supports : record001.Supports := by unfold RawData.Supports; decide +kernel
theorem record001_leaf_0 : Interval record001.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record001_leaves_nodup (j : Fin record001.l) : (record001.leaf j).Nodup :=
  record001.leaves_nodup_of_interval record001_leaf_0 j
theorem record001_checked (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 0 731 :=
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 0 352 731
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 0 160 352
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 0 64 160
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 0 32 64
  (record001_nodes_0 record001_valid)
  (record001_nodes_32 record001_valid))
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 64 96 160
  (record001_nodes_64 record001_valid)
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 96 128 160
  (record001_nodes_96 record001_valid)
  (record001_nodes_128 record001_valid))))
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 160 256 352
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 160 192 256
  (record001_nodes_160 record001_valid)
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 192 224 256
  (record001_nodes_192 record001_valid)
  (record001_nodes_224 record001_valid)))
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 256 288 352
  (record001_nodes_256 record001_valid)
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 288 320 352
  (record001_nodes_288 record001_valid)
  (record001_nodes_320 record001_valid)))))
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 352 544 731
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 352 448 544
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 352 384 448
  (record001_nodes_352 record001_valid)
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 384 416 448
  (record001_nodes_384 record001_valid)
  (record001_nodes_416 record001_valid)))
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 448 480 544
  (record001_nodes_448 record001_valid)
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 480 512 544
  (record001_nodes_480 record001_valid)
  (record001_nodes_512 record001_valid))))
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 544 640 731
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 544 576 640
  (record001_nodes_544 record001_valid)
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 576 608 640
  (record001_nodes_576 record001_valid)
  (record001_nodes_608 record001_valid)))
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 640 672 731
  (record001_nodes_640 record001_valid)
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 672 704 731
  (record001_nodes_672 record001_valid)
  (record001_nodes_704 record001_valid))))))
theorem record001_raw_node_checks (record001_valid : GraphGrowthInputs.Valid record001.inputs) (i : Fin record001.t) :
    RawGraphConditionedGrowth.nodeCheck (record001.inputs.problem record001_valid)
      record001.maps record001.leaf record001.nodes i = true :=
  record001.node_checks_valid record001_valid record001_supports (record001_checked record001_valid) i
#print axioms record001_raw_node_checks

end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00032
