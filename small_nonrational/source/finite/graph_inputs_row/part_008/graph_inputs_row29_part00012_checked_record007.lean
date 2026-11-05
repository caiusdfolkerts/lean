module
prelude
public import GraphInputsRow29Part00012Data
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00012
open Papers.RationalityTen PackedGraphCertificate FiniteChecks
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
theorem record007_nodes_608 (record007_valid : GraphGrowthInputs.Valid record007.inputs) : Interval (record007.nodeTestValid record007_valid) 608 640 :=
  interval_of_check _ 608 32 (by decide_kernel_context)
theorem record007_nodes_640 (record007_valid : GraphGrowthInputs.Valid record007.inputs) : Interval (record007.nodeTestValid record007_valid) 640 672 :=
  interval_of_check _ 640 32 (by decide_kernel_context)
theorem record007_nodes_672 (record007_valid : GraphGrowthInputs.Valid record007.inputs) : Interval (record007.nodeTestValid record007_valid) 672 704 :=
  interval_of_check _ 672 32 (by decide_kernel_context)
theorem record007_nodes_704 (record007_valid : GraphGrowthInputs.Valid record007.inputs) : Interval (record007.nodeTestValid record007_valid) 704 736 :=
  interval_of_check _ 704 32 (by decide_kernel_context)
theorem record007_nodes_736 (record007_valid : GraphGrowthInputs.Valid record007.inputs) : Interval (record007.nodeTestValid record007_valid) 736 768 :=
  interval_of_check _ 736 32 (by decide_kernel_context)
theorem record007_nodes_768 (record007_valid : GraphGrowthInputs.Valid record007.inputs) : Interval (record007.nodeTestValid record007_valid) 768 800 :=
  interval_of_check _ 768 32 (by decide_kernel_context)
theorem record007_nodes_800 (record007_valid : GraphGrowthInputs.Valid record007.inputs) : Interval (record007.nodeTestValid record007_valid) 800 832 :=
  interval_of_check _ 800 32 (by decide_kernel_context)
theorem record007_nodes_832 (record007_valid : GraphGrowthInputs.Valid record007.inputs) : Interval (record007.nodeTestValid record007_valid) 832 863 :=
  interval_of_check _ 832 31 (by decide_kernel_context)
theorem record007_supports : record007.Supports := by unfold RawData.Supports; decide +kernel
theorem record007_leaf_0 : Interval record007.leafTest 0 8 :=
  interval_of_check _ 0 8 (by decide +kernel)
theorem record007_leaf_8 : Interval record007.leafTest 8 16 :=
  interval_of_check _ 8 8 (by decide +kernel)
theorem record007_leaf_16 : Interval record007.leafTest 16 24 :=
  interval_of_check _ 16 8 (by decide +kernel)
theorem record007_leaf_24 : Interval record007.leafTest 24 29 :=
  interval_of_check _ 24 5 (by decide +kernel)
theorem record007_leaves_nodup (j : Fin record007.l) : (record007.leaf j).Nodup :=
  record007.leaves_nodup_of_interval (FiniteChecks.interval_append record007.leafTest 0 16 29
  (FiniteChecks.interval_append record007.leafTest 0 8 16
  record007_leaf_0
  record007_leaf_8)
  (FiniteChecks.interval_append record007.leafTest 16 24 29
  record007_leaf_16
  record007_leaf_24)) j
theorem record007_checked (record007_valid : GraphGrowthInputs.Valid record007.inputs) : Interval (record007.nodeTestValid record007_valid) 0 863 :=
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 0 416 863
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 0 192 416
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 0 96 192
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 0 32 96
  (record007_nodes_0 record007_valid)
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 32 64 96
  (record007_nodes_32 record007_valid)
  (record007_nodes_64 record007_valid)))
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 96 128 192
  (record007_nodes_96 record007_valid)
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 128 160 192
  (record007_nodes_128 record007_valid)
  (record007_nodes_160 record007_valid))))
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 192 288 416
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 192 224 288
  (record007_nodes_192 record007_valid)
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 224 256 288
  (record007_nodes_224 record007_valid)
  (record007_nodes_256 record007_valid)))
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 288 352 416
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 288 320 352
  (record007_nodes_288 record007_valid)
  (record007_nodes_320 record007_valid))
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 352 384 416
  (record007_nodes_352 record007_valid)
  (record007_nodes_384 record007_valid)))))
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 416 640 863
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 416 512 640
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 416 448 512
  (record007_nodes_416 record007_valid)
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 448 480 512
  (record007_nodes_448 record007_valid)
  (record007_nodes_480 record007_valid)))
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 512 576 640
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 512 544 576
  (record007_nodes_512 record007_valid)
  (record007_nodes_544 record007_valid))
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 576 608 640
  (record007_nodes_576 record007_valid)
  (record007_nodes_608 record007_valid))))
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 640 736 863
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 640 672 736
  (record007_nodes_640 record007_valid)
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 672 704 736
  (record007_nodes_672 record007_valid)
  (record007_nodes_704 record007_valid)))
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 736 800 863
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 736 768 800
  (record007_nodes_736 record007_valid)
  (record007_nodes_768 record007_valid))
  (FiniteChecks.interval_append (record007.nodeTestValid record007_valid) 800 832 863
  (record007_nodes_800 record007_valid)
  (record007_nodes_832 record007_valid))))))
theorem record007_raw_node_checks (record007_valid : GraphGrowthInputs.Valid record007.inputs) (i : Fin record007.t) :
    RawGraphConditionedGrowth.nodeCheck (record007.inputs.problem record007_valid)
      record007.maps record007.leaf record007.nodes i = true :=
  record007.node_checks_valid record007_valid record007_supports (record007_checked record007_valid) i
#print axioms record007_raw_node_checks

end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00012
