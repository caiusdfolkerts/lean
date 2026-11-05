module
prelude
public import GraphInputsRow29Part00282Data
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00282
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
theorem record000_nodes_608 (record000_valid : GraphGrowthInputs.Valid record000.inputs) : Interval (record000.nodeTestValid record000_valid) 608 640 :=
  interval_of_check _ 608 32 (by decide_kernel_context)
theorem record000_nodes_640 (record000_valid : GraphGrowthInputs.Valid record000.inputs) : Interval (record000.nodeTestValid record000_valid) 640 651 :=
  interval_of_check _ 640 11 (by decide_kernel_context)
theorem record000_supports : record000.Supports := by unfold RawData.Supports; decide +kernel
theorem record000_leaf_0 : Interval record000.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record000_leaves_nodup (j : Fin record000.l) : (record000.leaf j).Nodup :=
  record000.leaves_nodup_of_interval record000_leaf_0 j
theorem record000_checked (record000_valid : GraphGrowthInputs.Valid record000.inputs) : Interval (record000.nodeTestValid record000_valid) 0 651 :=
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 0 320 651
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
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 320 480 651
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 320 384 480
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 320 352 384
  (record000_nodes_320 record000_valid)
  (record000_nodes_352 record000_valid))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 384 416 480
  (record000_nodes_384 record000_valid)
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 416 448 480
  (record000_nodes_416 record000_valid)
  (record000_nodes_448 record000_valid))))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 480 576 651
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 480 512 576
  (record000_nodes_480 record000_valid)
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 512 544 576
  (record000_nodes_512 record000_valid)
  (record000_nodes_544 record000_valid)))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 576 608 651
  (record000_nodes_576 record000_valid)
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 608 640 651
  (record000_nodes_608 record000_valid)
  (record000_nodes_640 record000_valid))))))
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
theorem record001_nodes_800 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 800 832 :=
  interval_of_check _ 800 32 (by decide_kernel_context)
theorem record001_nodes_832 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 832 864 :=
  interval_of_check _ 832 32 (by decide_kernel_context)
theorem record001_nodes_864 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 864 896 :=
  interval_of_check _ 864 32 (by decide_kernel_context)
theorem record001_nodes_896 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 896 928 :=
  interval_of_check _ 896 32 (by decide_kernel_context)
theorem record001_nodes_928 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 928 960 :=
  interval_of_check _ 928 32 (by decide_kernel_context)
theorem record001_nodes_960 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 960 992 :=
  interval_of_check _ 960 32 (by decide_kernel_context)
theorem record001_nodes_992 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 992 1024 :=
  interval_of_check _ 992 32 (by decide_kernel_context)
theorem record001_nodes_1024 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 1024 1056 :=
  interval_of_check _ 1024 32 (by decide_kernel_context)
theorem record001_nodes_1056 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 1056 1088 :=
  interval_of_check _ 1056 32 (by decide_kernel_context)
theorem record001_nodes_1088 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 1088 1120 :=
  interval_of_check _ 1088 32 (by decide_kernel_context)
theorem record001_nodes_1120 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 1120 1152 :=
  interval_of_check _ 1120 32 (by decide_kernel_context)
theorem record001_nodes_1152 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 1152 1184 :=
  interval_of_check _ 1152 32 (by decide_kernel_context)
theorem record001_nodes_1184 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 1184 1216 :=
  interval_of_check _ 1184 32 (by decide_kernel_context)
theorem record001_nodes_1216 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 1216 1248 :=
  interval_of_check _ 1216 32 (by decide_kernel_context)
theorem record001_nodes_1248 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 1248 1280 :=
  interval_of_check _ 1248 32 (by decide_kernel_context)
theorem record001_nodes_1280 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 1280 1312 :=
  interval_of_check _ 1280 32 (by decide_kernel_context)
theorem record001_nodes_1312 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 1312 1344 :=
  interval_of_check _ 1312 32 (by decide_kernel_context)
theorem record001_nodes_1344 (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 1344 1353 :=
  interval_of_check _ 1344 9 (by decide_kernel_context)
theorem record001_supports : record001.Supports := by unfold RawData.Supports; decide +kernel
theorem record001_leaf_0 : Interval record001.leafTest 0 1 :=
  interval_of_check _ 0 1 (by decide +kernel)
theorem record001_leaves_nodup (j : Fin record001.l) : (record001.leaf j).Nodup :=
  record001.leaves_nodup_of_interval record001_leaf_0 j
theorem record001_checked (record001_valid : GraphGrowthInputs.Valid record001.inputs) : Interval (record001.nodeTestValid record001_valid) 0 1353 :=
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 0 672 1353
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 0 320 672
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 0 160 320
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 0 64 160
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 0 32 64
  (record001_nodes_0 record001_valid)
  (record001_nodes_32 record001_valid))
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 64 96 160
  (record001_nodes_64 record001_valid)
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 96 128 160
  (record001_nodes_96 record001_valid)
  (record001_nodes_128 record001_valid))))
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 160 224 320
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 160 192 224
  (record001_nodes_160 record001_valid)
  (record001_nodes_192 record001_valid))
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 224 256 320
  (record001_nodes_224 record001_valid)
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 256 288 320
  (record001_nodes_256 record001_valid)
  (record001_nodes_288 record001_valid)))))
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 320 480 672
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 320 384 480
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 320 352 384
  (record001_nodes_320 record001_valid)
  (record001_nodes_352 record001_valid))
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 384 416 480
  (record001_nodes_384 record001_valid)
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 416 448 480
  (record001_nodes_416 record001_valid)
  (record001_nodes_448 record001_valid))))
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 480 576 672
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 480 512 576
  (record001_nodes_480 record001_valid)
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 512 544 576
  (record001_nodes_512 record001_valid)
  (record001_nodes_544 record001_valid)))
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 576 608 672
  (record001_nodes_576 record001_valid)
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 608 640 672
  (record001_nodes_608 record001_valid)
  (record001_nodes_640 record001_valid))))))
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 672 1024 1353
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 672 832 1024
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 672 736 832
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 672 704 736
  (record001_nodes_672 record001_valid)
  (record001_nodes_704 record001_valid))
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 736 768 832
  (record001_nodes_736 record001_valid)
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 768 800 832
  (record001_nodes_768 record001_valid)
  (record001_nodes_800 record001_valid))))
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 832 928 1024
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 832 864 928
  (record001_nodes_832 record001_valid)
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 864 896 928
  (record001_nodes_864 record001_valid)
  (record001_nodes_896 record001_valid)))
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 928 960 1024
  (record001_nodes_928 record001_valid)
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 960 992 1024
  (record001_nodes_960 record001_valid)
  (record001_nodes_992 record001_valid)))))
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 1024 1184 1353
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 1024 1088 1184
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 1024 1056 1088
  (record001_nodes_1024 record001_valid)
  (record001_nodes_1056 record001_valid))
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 1088 1120 1184
  (record001_nodes_1088 record001_valid)
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 1120 1152 1184
  (record001_nodes_1120 record001_valid)
  (record001_nodes_1152 record001_valid))))
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 1184 1280 1353
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 1184 1216 1280
  (record001_nodes_1184 record001_valid)
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 1216 1248 1280
  (record001_nodes_1216 record001_valid)
  (record001_nodes_1248 record001_valid)))
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 1280 1312 1353
  (record001_nodes_1280 record001_valid)
  (FiniteChecks.interval_append (record001.nodeTestValid record001_valid) 1312 1344 1353
  (record001_nodes_1312 record001_valid)
  (record001_nodes_1344 record001_valid)))))))
theorem record001_raw_node_checks (record001_valid : GraphGrowthInputs.Valid record001.inputs) (i : Fin record001.t) :
    RawGraphConditionedGrowth.nodeCheck (record001.inputs.problem record001_valid)
      record001.maps record001.leaf record001.nodes i = true :=
  record001.node_checks_valid record001_valid record001_supports (record001_checked record001_valid) i
#print axioms record001_raw_node_checks

end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00282
