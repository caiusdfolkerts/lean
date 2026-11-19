module
prelude
public import GraphInputsRow29Part00044CheckedRecord005Segment014
public import GraphInputsRow29Part00044Data
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00044
open Papers.RationalityTen PackedGraphCertificate FiniteChecks
theorem record005_leaf_48 : Interval record005.leafTest 48 51 :=
  interval_of_check _ 48 3 (by decide +kernel)
theorem record005_leaves_nodup (j : Fin record005.l) : (record005.leaf j).Nodup :=
  record005.leaves_nodup_of_interval (FiniteChecks.interval_append record005.leafTest 0 24 51
  (FiniteChecks.interval_append record005.leafTest 0 8 24
  record005_leaf_0
  (FiniteChecks.interval_append record005.leafTest 8 16 24
  record005_leaf_8
  record005_leaf_16))
  (FiniteChecks.interval_append record005.leafTest 24 40 51
  (FiniteChecks.interval_append record005.leafTest 24 32 40
  record005_leaf_24
  record005_leaf_32)
  (FiniteChecks.interval_append record005.leafTest 40 48 51
  record005_leaf_40
  record005_leaf_48))) j
theorem record005_checked (record005_valid : GraphGrowthInputs.Valid record005.inputs) : Interval (record005.nodeTestValid record005_valid) 0 1193 :=
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 0 608 1193
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 0 288 608
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 0 128 288
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 0 64 128
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 0 32 64
  (record005_nodes_0 record005_valid)
  (record005_nodes_32 record005_valid))
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 64 96 128
  (record005_nodes_64 record005_valid)
  (record005_nodes_96 record005_valid)))
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 128 192 288
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 128 160 192
  (record005_nodes_128 record005_valid)
  (record005_nodes_160 record005_valid))
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 192 224 288
  (record005_nodes_192 record005_valid)
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 224 256 288
  (record005_nodes_224 record005_valid)
  (record005_nodes_256 record005_valid)))))
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 288 448 608
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 288 352 448
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 288 320 352
  (record005_nodes_288 record005_valid)
  (record005_nodes_320 record005_valid))
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 352 384 448
  (record005_nodes_352 record005_valid)
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 384 416 448
  (record005_nodes_384 record005_valid)
  (record005_nodes_416 record005_valid))))
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 448 512 608
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 448 480 512
  (record005_nodes_448 record005_valid)
  (record005_nodes_480 record005_valid))
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 512 544 608
  (record005_nodes_512 record005_valid)
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 544 576 608
  (record005_nodes_544 record005_valid)
  (record005_nodes_576 record005_valid))))))
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 608 896 1193
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 608 736 896
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 608 672 736
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 608 640 672
  (record005_nodes_608 record005_valid)
  (record005_nodes_640 record005_valid))
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 672 704 736
  (record005_nodes_672 record005_valid)
  (record005_nodes_704 record005_valid)))
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 736 800 896
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 736 768 800
  (record005_nodes_736 record005_valid)
  (record005_nodes_768 record005_valid))
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 800 832 896
  (record005_nodes_800 record005_valid)
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 832 864 896
  (record005_nodes_832 record005_valid)
  (record005_nodes_864 record005_valid)))))
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 896 1056 1193
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 896 960 1056
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 896 928 960
  (record005_nodes_896 record005_valid)
  (record005_nodes_928 record005_valid))
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 960 992 1056
  (record005_nodes_960 record005_valid)
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 992 1024 1056
  (record005_nodes_992 record005_valid)
  (record005_nodes_1024 record005_valid))))
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 1056 1120 1193
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 1056 1088 1120
  (record005_nodes_1056 record005_valid)
  (record005_nodes_1088 record005_valid))
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 1120 1152 1193
  (record005_nodes_1120 record005_valid)
  (FiniteChecks.interval_append (record005.nodeTestValid record005_valid) 1152 1184 1193
  (record005_nodes_1152 record005_valid)
  (record005_nodes_1184 record005_valid)))))))
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00044
