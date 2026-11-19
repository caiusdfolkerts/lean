module
prelude
public import GraphInputsRow31Part00031Data
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00031
open Papers.RationalityTen PackedGraphCertificate FiniteChecks
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
theorem record002_nodes_576 (record002_valid : GraphGrowthInputs.Valid record002.inputs) : Interval (record002.nodeTestValid record002_valid) 576 608 :=
  interval_of_check _ 576 32 (by decide_kernel_context)
theorem record002_nodes_608 (record002_valid : GraphGrowthInputs.Valid record002.inputs) : Interval (record002.nodeTestValid record002_valid) 608 640 :=
  interval_of_check _ 608 32 (by decide_kernel_context)
theorem record002_nodes_640 (record002_valid : GraphGrowthInputs.Valid record002.inputs) : Interval (record002.nodeTestValid record002_valid) 640 672 :=
  interval_of_check _ 640 32 (by decide_kernel_context)
theorem record002_nodes_672 (record002_valid : GraphGrowthInputs.Valid record002.inputs) : Interval (record002.nodeTestValid record002_valid) 672 704 :=
  interval_of_check _ 672 32 (by decide_kernel_context)
theorem record002_nodes_704 (record002_valid : GraphGrowthInputs.Valid record002.inputs) : Interval (record002.nodeTestValid record002_valid) 704 728 :=
  interval_of_check _ 704 24 (by decide_kernel_context)
theorem record002_supports : record002.Supports := by unfold RawData.Supports; decide +kernel
theorem record002_leaf_0 : Interval record002.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record002_leaves_nodup (j : Fin record002.l) : (record002.leaf j).Nodup :=
  record002.leaves_nodup_of_interval record002_leaf_0 j
theorem record002_checked (record002_valid : GraphGrowthInputs.Valid record002.inputs) : Interval (record002.nodeTestValid record002_valid) 0 728 :=
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 0 352 728
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 0 160 352
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 0 64 160
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 0 32 64
  (record002_nodes_0 record002_valid)
  (record002_nodes_32 record002_valid))
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 64 96 160
  (record002_nodes_64 record002_valid)
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 96 128 160
  (record002_nodes_96 record002_valid)
  (record002_nodes_128 record002_valid))))
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 160 256 352
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 160 192 256
  (record002_nodes_160 record002_valid)
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 192 224 256
  (record002_nodes_192 record002_valid)
  (record002_nodes_224 record002_valid)))
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 256 288 352
  (record002_nodes_256 record002_valid)
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 288 320 352
  (record002_nodes_288 record002_valid)
  (record002_nodes_320 record002_valid)))))
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 352 544 728
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 352 448 544
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 352 384 448
  (record002_nodes_352 record002_valid)
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 384 416 448
  (record002_nodes_384 record002_valid)
  (record002_nodes_416 record002_valid)))
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 448 480 544
  (record002_nodes_448 record002_valid)
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 480 512 544
  (record002_nodes_480 record002_valid)
  (record002_nodes_512 record002_valid))))
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 544 640 728
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 544 576 640
  (record002_nodes_544 record002_valid)
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 576 608 640
  (record002_nodes_576 record002_valid)
  (record002_nodes_608 record002_valid)))
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 640 672 728
  (record002_nodes_640 record002_valid)
  (FiniteChecks.interval_append (record002.nodeTestValid record002_valid) 672 704 728
  (record002_nodes_672 record002_valid)
  (record002_nodes_704 record002_valid))))))
theorem record002_raw_node_checks (record002_valid : GraphGrowthInputs.Valid record002.inputs) (i : Fin record002.t) :
    RawGraphConditionedGrowth.nodeCheck (record002.inputs.problem record002_valid)
      record002.maps record002.leaf record002.nodes i = true :=
  record002.node_checks_valid record002_valid record002_supports (record002_checked record002_valid) i
#print axioms record002_raw_node_checks

end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00031
