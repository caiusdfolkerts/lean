module

public meta import LowerSchemas.FinitePolygonN
public import PolygonN7ClassificationPart013

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.ConcretePolygonClassification.N7
open Papers.RationalityTen PolygonBoundaryCatalogue BoundarySearch PolygonDAGSemantics
open GrowthDAG SparseGrowthDAG GrowthPruning

cert_terminal_data_join 02216 02248 2216 2248 2232 02232
cert_terminal_data_join 02184 02248 2184 2248 2216 02216
cert_terminal_data_join 02128 02248 2128 2248 2184 02184
cert_terminal_data_join_2 02256 02272 2256 2272 2264 02264
cert_terminal_data_join_3 02248 02272 2248 2272 2256 02256
cert_terminal_data_join_2 02272 02288 2272 2288 2280 02280
cert_terminal_data_join_2 02288 02304 2288 2304 2296 02296
cert_terminal_data_join 02272 02304 2272 2304 2288 02288
cert_terminal_data_join 02248 02304 2248 2304 2272 02272
cert_terminal_data_join_2 02304 02320 2304 2320 2312 02312
cert_terminal_data_join_2 02320 02336 2320 2336 2328 02328
cert_terminal_data_join 02304 02336 2304 2336 2320 02320
cert_terminal_data_join_2 02336 02352 2336 2352 2344 02344
cert_terminal_data_join_2 02352 02368 2352 2368 2360 02360
cert_terminal_data_join 02336 02368 2336 2368 2352 02352
cert_terminal_data_join 02304 02368 2304 2368 2336 02336
cert_terminal_data_join 02248 02368 2248 2368 2304 02304
cert_terminal_data_join 02128 02368 2128 2368 2248 02248
cert_terminal_data_join 01896 02368 1896 2368 2128 02128
cert_terminal_data_join_2 02376 02392 2376 2392 2384 02384
cert_terminal_data_join_3 02368 02392 2368 2392 2376 02376
cert_terminal_data_join_2 02392 02408 2392 2408 2400 02400
cert_terminal_data_join_2 02408 02424 2408 2424 2416 02416
cert_terminal_data_join 02392 02424 2392 2424 2408 02408
cert_terminal_data_join 02368 02424 2368 2424 2392 02392
cert_terminal_data_join_2 02424 02440 2424 2440 2432 02432
cert_terminal_data_join_2 02440 02456 2440 2456 2448 02448
cert_terminal_data_join 02424 02456 2424 2456 2440 02440
cert_terminal_data_join_2 02456 02472 2456 2472 2464 02464
cert_terminal_data_join_2 02472 02488 2472 2488 2480 02480
cert_terminal_data_join 02456 02488 2456 2488 2472 02472
cert_terminal_data_join 02424 02488 2424 2488 2456 02456
cert_terminal_data_join 02368 02488 2368 2488 2424 02424
cert_terminal_data_join_2 02496 02512 2496 2512 2504 02504
cert_terminal_data_join_3 02488 02512 2488 2512 2496 02496
cert_terminal_data_join_2 02512 02528 2512 2528 2520 02520
cert_terminal_data_join_2 02528 02544 2528 2544 2536 02536
cert_terminal_data_join 02512 02544 2512 2544 2528 02528
cert_terminal_data_join 02488 02544 2488 2544 2512 02512
cert_terminal_data_join_2 02544 02560 2544 2560 2552 02552
cert_terminal_data_join_2 02560 02576 2560 2576 2568 02568
cert_terminal_data_join 02544 02576 2544 2576 2560 02560
cert_terminal_data_join_2 02576 02592 2576 2592 2584 02584
cert_terminal_data_join_2 02592 02608 2592 2608 2600 02600
cert_terminal_data_join 02576 02608 2576 2608 2592 02592
cert_terminal_data_join 02544 02608 2544 2608 2576 02576
cert_terminal_data_join 02488 02608 2488 2608 2544 02544
cert_terminal_data_join 02368 02608 2368 2608 2488 02488
cert_terminal_data_join_2 02616 02632 2616 2632 2624 02624
cert_terminal_data_join_3 02608 02632 2608 2632 2616 02616
cert_terminal_data_join_2 02632 02648 2632 2648 2640 02640
cert_terminal_data_join_2 02648 02664 2648 2664 2656 02656
cert_terminal_data_join 02632 02664 2632 2664 2648 02648
cert_terminal_data_join 02608 02664 2608 2664 2632 02632
cert_terminal_data_join_2 02664 02680 2664 2680 2672 02672
cert_terminal_data_join_2 02680 02696 2680 2696 2688 02688
cert_terminal_data_join 02664 02696 2664 2696 2680 02680
cert_terminal_data_join_2 02696 02712 2696 2712 2704 02704
cert_terminal_data_join_2 02712 02728 2712 2728 2720 02720
cert_terminal_data_join 02696 02728 2696 2728 2712 02712
cert_terminal_data_join 02664 02728 2664 2728 2696 02696
cert_terminal_data_join 02608 02728 2608 2728 2664 02664
cert_terminal_data_join_2 02736 02752 2736 2752 2744 02744
theorem terminal_data_join_02728_02752 : FiniteChecks.Interval terminalTest 2728 2752 :=
  FiniteChecks.interval_append terminalTest 2728 2736 2752 terminal_data_02728 terminal_data_join_02736_02752


end Papers.RationalityTen.ConcretePolygonClassification.N7
