module
prelude
public meta import LowerSchemas.FiniteGraphLargeRow
public import GraphLargeRow29Case03359Data
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphLargeRow29Case03359
open Papers.RationalityTen PackedGraphCertificate FiniteChecks
cert_graph_nodes 0 32 32
cert_graph_nodes 32 64 32
cert_graph_nodes 64 96 32
cert_graph_nodes 96 128 32
cert_graph_nodes 128 160 32
cert_graph_nodes 160 192 32
cert_graph_nodes 192 224 32
cert_graph_nodes 224 256 32
cert_graph_nodes 256 288 32
cert_graph_nodes 288 320 32
cert_graph_nodes 320 352 32
cert_graph_nodes 352 384 32
cert_graph_nodes 384 416 32
cert_graph_nodes 416 448 32
cert_graph_nodes 448 480 32
cert_graph_nodes 480 512 32
cert_graph_nodes 512 544 32
cert_graph_nodes 544 576 32
cert_graph_nodes 576 608 32
cert_graph_nodes 608 640 32
cert_graph_nodes 640 672 32
cert_graph_nodes 672 704 32
cert_graph_nodes 704 736 32
cert_graph_nodes 736 768 32
cert_graph_nodes 768 800 32
cert_graph_nodes 800 832 32
cert_graph_nodes 832 864 32
cert_graph_nodes 864 896 32
cert_graph_nodes 896 928 32
cert_graph_nodes 928 960 32
cert_graph_nodes 960 992 32
cert_graph_nodes 992 1024 32
cert_graph_nodes 1024 1056 32
cert_graph_nodes 1056 1088 32
cert_graph_nodes 1088 1120 32
cert_graph_nodes 1120 1152 32
cert_graph_nodes 1152 1184 32
cert_graph_nodes 1184 1216 32
cert_graph_nodes 1216 1248 32
cert_graph_nodes 1248 1280 32
cert_graph_nodes 1280 1312 32
cert_graph_nodes 1312 1344 32
cert_graph_nodes 1344 1376 32
cert_graph_nodes 1376 1408 32
cert_graph_nodes 1408 1440 32
cert_graph_nodes 1440 1472 32
cert_graph_nodes 1472 1504 32
cert_graph_nodes 1504 1536 32
cert_graph_nodes 1536 1568 32
cert_graph_nodes 1568 1600 32
cert_graph_nodes 1600 1632 32
cert_graph_nodes 1632 1664 32
cert_graph_nodes 1664 1696 32
cert_graph_nodes 1696 1728 32
cert_graph_nodes 1728 1760 32
cert_graph_nodes 1760 1792 32
cert_graph_nodes 1792 1824 32
cert_graph_nodes 1824 1842 18
theorem record000_supports : record000.Supports := by unfold RawData.Supports; decide +kernel
cert_graph_leaf 0 1 1
theorem record000_leaves_nodup (j : Fin record000.l) : (record000.leaf j).Nodup :=
  record000.leaves_nodup_of_interval record000_leaf_0 j
theorem record000_checked (record000_valid : GraphGrowthInputs.Valid record000.inputs) : Interval (record000.nodeTestValid record000_valid) 0 1842 :=
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 0 928 1842
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 0 448 928
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 0 224 448
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
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 224 320 448
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 224 256 320
  (record000_nodes_224 record000_valid)
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 256 288 320
  (record000_nodes_256 record000_valid)
  (record000_nodes_288 record000_valid)))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 320 384 448
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 320 352 384
  (record000_nodes_320 record000_valid)
  (record000_nodes_352 record000_valid))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 384 416 448
  (record000_nodes_384 record000_valid)
  (record000_nodes_416 record000_valid)))))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 448 672 928
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 448 544 672
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 448 480 544
  (record000_nodes_448 record000_valid)
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 480 512 544
  (record000_nodes_480 record000_valid)
  (record000_nodes_512 record000_valid)))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 544 608 672
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 544 576 608
  (record000_nodes_544 record000_valid)
  (record000_nodes_576 record000_valid))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 608 640 672
  (record000_nodes_608 record000_valid)
  (record000_nodes_640 record000_valid))))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 672 800 928
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 672 736 800
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 672 704 736
  (record000_nodes_672 record000_valid)
  (record000_nodes_704 record000_valid))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 736 768 800
  (record000_nodes_736 record000_valid)
  (record000_nodes_768 record000_valid)))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 800 864 928
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 800 832 864
  (record000_nodes_800 record000_valid)
  (record000_nodes_832 record000_valid))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 864 896 928
  (record000_nodes_864 record000_valid)
  (record000_nodes_896 record000_valid))))))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 928 1376 1842
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 928 1152 1376
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 928 1024 1152
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 928 960 1024
  (record000_nodes_928 record000_valid)
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 960 992 1024
  (record000_nodes_960 record000_valid)
  (record000_nodes_992 record000_valid)))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 1024 1088 1152
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 1024 1056 1088
  (record000_nodes_1024 record000_valid)
  (record000_nodes_1056 record000_valid))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 1088 1120 1152
  (record000_nodes_1088 record000_valid)
  (record000_nodes_1120 record000_valid))))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 1152 1248 1376
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 1152 1184 1248
  (record000_nodes_1152 record000_valid)
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 1184 1216 1248
  (record000_nodes_1184 record000_valid)
  (record000_nodes_1216 record000_valid)))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 1248 1312 1376
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 1248 1280 1312
  (record000_nodes_1248 record000_valid)
  (record000_nodes_1280 record000_valid))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 1312 1344 1376
  (record000_nodes_1312 record000_valid)
  (record000_nodes_1344 record000_valid)))))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 1376 1600 1842
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 1376 1472 1600
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 1376 1408 1472
  (record000_nodes_1376 record000_valid)
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 1408 1440 1472
  (record000_nodes_1408 record000_valid)
  (record000_nodes_1440 record000_valid)))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 1472 1536 1600
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 1472 1504 1536
  (record000_nodes_1472 record000_valid)
  (record000_nodes_1504 record000_valid))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 1536 1568 1600
  (record000_nodes_1536 record000_valid)
  (record000_nodes_1568 record000_valid))))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 1600 1728 1842
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 1600 1664 1728
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 1600 1632 1664
  (record000_nodes_1600 record000_valid)
  (record000_nodes_1632 record000_valid))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 1664 1696 1728
  (record000_nodes_1664 record000_valid)
  (record000_nodes_1696 record000_valid)))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 1728 1792 1842
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 1728 1760 1792
  (record000_nodes_1728 record000_valid)
  (record000_nodes_1760 record000_valid))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 1792 1824 1842
  (record000_nodes_1792 record000_valid)
  (record000_nodes_1824 record000_valid)))))))
theorem record000_raw_node_checks (record000_valid : GraphGrowthInputs.Valid record000.inputs) (i : Fin record000.t) :
    RawGraphConditionedGrowth.nodeCheck (record000.inputs.problem record000_valid)
      record000.maps record000.leaf record000.nodes i = true :=
  record000.node_checks_valid record000_valid record000_supports (record000_checked record000_valid) i
#print axioms record000_raw_node_checks

end Papers.RationalityTen.CompactReplay.GraphLargeRow29Case03359
