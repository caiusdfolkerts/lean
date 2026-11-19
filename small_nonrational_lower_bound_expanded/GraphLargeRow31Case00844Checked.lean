module
prelude
public meta import LowerSchemas.FiniteGraphLargeRow
public import GraphLargeRow31Case00844Data
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphLargeRow31Case00844
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
cert_graph_nodes 1824 1856 32
cert_graph_nodes 1856 1888 32
cert_graph_nodes 1888 1920 32
cert_graph_nodes 1920 1952 32
cert_graph_nodes 1952 1984 32
cert_graph_nodes 1984 2016 32
cert_graph_nodes 2016 2048 32
cert_graph_nodes 2048 2080 32
cert_graph_nodes 2080 2112 32
cert_graph_nodes 2112 2144 32
cert_graph_nodes 2144 2176 32
cert_graph_nodes 2176 2208 32
cert_graph_nodes 2208 2240 32
cert_graph_nodes 2240 2272 32
cert_graph_nodes 2272 2277 5
theorem record000_supports : record000.Supports := by unfold RawData.Supports; decide +kernel
cert_graph_leaf 0 8 8
cert_graph_leaf 8 16 8
cert_graph_leaf 16 24 8
cert_graph_leaf 24 30 6
theorem record000_leaves_nodup (j : Fin record000.l) : (record000.leaf j).Nodup :=
  record000.leaves_nodup_of_interval (FiniteChecks.interval_append record000.leafTest 0 16 30
  (FiniteChecks.interval_append record000.leafTest 0 8 16
  record000_leaf_0
  record000_leaf_8)
  (FiniteChecks.interval_append record000.leafTest 16 24 30
  record000_leaf_16
  record000_leaf_24)) j
theorem record000_checked (record000_valid : GraphGrowthInputs.Valid record000.inputs) : Interval (record000.nodeTestValid record000_valid) 0 2277 :=
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 0 1152 2277
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 0 576 1152
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 0 288 576
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 0 128 288
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 0 64 128
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 0 32 64
  (record000_nodes_0 record000_valid)
  (record000_nodes_32 record000_valid))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 64 96 128
  (record000_nodes_64 record000_valid)
  (record000_nodes_96 record000_valid)))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 128 192 288
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 128 160 192
  (record000_nodes_128 record000_valid)
  (record000_nodes_160 record000_valid))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 192 224 288
  (record000_nodes_192 record000_valid)
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 224 256 288
  (record000_nodes_224 record000_valid)
  (record000_nodes_256 record000_valid)))))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 288 416 576
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 288 352 416
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 288 320 352
  (record000_nodes_288 record000_valid)
  (record000_nodes_320 record000_valid))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 352 384 416
  (record000_nodes_352 record000_valid)
  (record000_nodes_384 record000_valid)))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 416 480 576
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 416 448 480
  (record000_nodes_416 record000_valid)
  (record000_nodes_448 record000_valid))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 480 512 576
  (record000_nodes_480 record000_valid)
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 512 544 576
  (record000_nodes_512 record000_valid)
  (record000_nodes_544 record000_valid))))))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 576 864 1152
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 576 704 864
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 576 640 704
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 576 608 640
  (record000_nodes_576 record000_valid)
  (record000_nodes_608 record000_valid))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 640 672 704
  (record000_nodes_640 record000_valid)
  (record000_nodes_672 record000_valid)))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 704 768 864
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 704 736 768
  (record000_nodes_704 record000_valid)
  (record000_nodes_736 record000_valid))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 768 800 864
  (record000_nodes_768 record000_valid)
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 800 832 864
  (record000_nodes_800 record000_valid)
  (record000_nodes_832 record000_valid)))))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 864 992 1152
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 864 928 992
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 864 896 928
  (record000_nodes_864 record000_valid)
  (record000_nodes_896 record000_valid))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 928 960 992
  (record000_nodes_928 record000_valid)
  (record000_nodes_960 record000_valid)))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 992 1056 1152
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 992 1024 1056
  (record000_nodes_992 record000_valid)
  (record000_nodes_1024 record000_valid))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 1056 1088 1152
  (record000_nodes_1056 record000_valid)
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 1088 1120 1152
  (record000_nodes_1088 record000_valid)
  (record000_nodes_1120 record000_valid)))))))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 1152 1728 2277
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 1152 1440 1728
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 1152 1280 1440
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 1152 1216 1280
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 1152 1184 1216
  (record000_nodes_1152 record000_valid)
  (record000_nodes_1184 record000_valid))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 1216 1248 1280
  (record000_nodes_1216 record000_valid)
  (record000_nodes_1248 record000_valid)))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 1280 1344 1440
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 1280 1312 1344
  (record000_nodes_1280 record000_valid)
  (record000_nodes_1312 record000_valid))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 1344 1376 1440
  (record000_nodes_1344 record000_valid)
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 1376 1408 1440
  (record000_nodes_1376 record000_valid)
  (record000_nodes_1408 record000_valid)))))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 1440 1568 1728
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 1440 1504 1568
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 1440 1472 1504
  (record000_nodes_1440 record000_valid)
  (record000_nodes_1472 record000_valid))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 1504 1536 1568
  (record000_nodes_1504 record000_valid)
  (record000_nodes_1536 record000_valid)))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 1568 1632 1728
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 1568 1600 1632
  (record000_nodes_1568 record000_valid)
  (record000_nodes_1600 record000_valid))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 1632 1664 1728
  (record000_nodes_1632 record000_valid)
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 1664 1696 1728
  (record000_nodes_1664 record000_valid)
  (record000_nodes_1696 record000_valid))))))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 1728 2016 2277
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 1728 1856 2016
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 1728 1792 1856
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 1728 1760 1792
  (record000_nodes_1728 record000_valid)
  (record000_nodes_1760 record000_valid))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 1792 1824 1856
  (record000_nodes_1792 record000_valid)
  (record000_nodes_1824 record000_valid)))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 1856 1920 2016
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 1856 1888 1920
  (record000_nodes_1856 record000_valid)
  (record000_nodes_1888 record000_valid))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 1920 1952 2016
  (record000_nodes_1920 record000_valid)
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 1952 1984 2016
  (record000_nodes_1952 record000_valid)
  (record000_nodes_1984 record000_valid)))))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 2016 2144 2277
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 2016 2080 2144
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 2016 2048 2080
  (record000_nodes_2016 record000_valid)
  (record000_nodes_2048 record000_valid))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 2080 2112 2144
  (record000_nodes_2080 record000_valid)
  (record000_nodes_2112 record000_valid)))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 2144 2208 2277
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 2144 2176 2208
  (record000_nodes_2144 record000_valid)
  (record000_nodes_2176 record000_valid))
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 2208 2240 2277
  (record000_nodes_2208 record000_valid)
  (FiniteChecks.interval_append (record000.nodeTestValid record000_valid) 2240 2272 2277
  (record000_nodes_2240 record000_valid)
  (record000_nodes_2272 record000_valid))))))))
theorem record000_raw_node_checks (record000_valid : GraphGrowthInputs.Valid record000.inputs) (i : Fin record000.t) :
    RawGraphConditionedGrowth.nodeCheck (record000.inputs.problem record000_valid)
      record000.maps record000.leaf record000.nodes i = true :=
  record000.node_checks_valid record000_valid record000_supports (record000_checked record000_valid) i

end Papers.RationalityTen.CompactReplay.GraphLargeRow31Case00844
