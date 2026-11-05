module

public import PolygonN7ClassificationPart013

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.ConcretePolygonClassification.N7
open Papers.RationalityTen PolygonBoundaryCatalogue BoundarySearch PolygonDAGSemantics
open GrowthDAG SparseGrowthDAG GrowthPruning

theorem terminal_data_join_02216_02248 : FiniteChecks.Interval terminalTest 2216 2248 :=
  FiniteChecks.interval_append terminalTest 2216 2232 2248 terminal_data_join_02216_02232 terminal_data_join_02232_02248

theorem terminal_data_join_02184_02248 : FiniteChecks.Interval terminalTest 2184 2248 :=
  FiniteChecks.interval_append terminalTest 2184 2216 2248 terminal_data_join_02184_02216 terminal_data_join_02216_02248

theorem terminal_data_join_02128_02248 : FiniteChecks.Interval terminalTest 2128 2248 :=
  FiniteChecks.interval_append terminalTest 2128 2184 2248 terminal_data_join_02128_02184 terminal_data_join_02184_02248

theorem terminal_data_join_02256_02272 : FiniteChecks.Interval terminalTest 2256 2272 :=
  FiniteChecks.interval_append terminalTest 2256 2264 2272 terminal_data_02256 terminal_data_02264

theorem terminal_data_join_02248_02272 : FiniteChecks.Interval terminalTest 2248 2272 :=
  FiniteChecks.interval_append terminalTest 2248 2256 2272 terminal_data_02248 terminal_data_join_02256_02272

theorem terminal_data_join_02272_02288 : FiniteChecks.Interval terminalTest 2272 2288 :=
  FiniteChecks.interval_append terminalTest 2272 2280 2288 terminal_data_02272 terminal_data_02280

theorem terminal_data_join_02288_02304 : FiniteChecks.Interval terminalTest 2288 2304 :=
  FiniteChecks.interval_append terminalTest 2288 2296 2304 terminal_data_02288 terminal_data_02296

theorem terminal_data_join_02272_02304 : FiniteChecks.Interval terminalTest 2272 2304 :=
  FiniteChecks.interval_append terminalTest 2272 2288 2304 terminal_data_join_02272_02288 terminal_data_join_02288_02304

theorem terminal_data_join_02248_02304 : FiniteChecks.Interval terminalTest 2248 2304 :=
  FiniteChecks.interval_append terminalTest 2248 2272 2304 terminal_data_join_02248_02272 terminal_data_join_02272_02304

theorem terminal_data_join_02304_02320 : FiniteChecks.Interval terminalTest 2304 2320 :=
  FiniteChecks.interval_append terminalTest 2304 2312 2320 terminal_data_02304 terminal_data_02312

theorem terminal_data_join_02320_02336 : FiniteChecks.Interval terminalTest 2320 2336 :=
  FiniteChecks.interval_append terminalTest 2320 2328 2336 terminal_data_02320 terminal_data_02328

theorem terminal_data_join_02304_02336 : FiniteChecks.Interval terminalTest 2304 2336 :=
  FiniteChecks.interval_append terminalTest 2304 2320 2336 terminal_data_join_02304_02320 terminal_data_join_02320_02336

theorem terminal_data_join_02336_02352 : FiniteChecks.Interval terminalTest 2336 2352 :=
  FiniteChecks.interval_append terminalTest 2336 2344 2352 terminal_data_02336 terminal_data_02344

theorem terminal_data_join_02352_02368 : FiniteChecks.Interval terminalTest 2352 2368 :=
  FiniteChecks.interval_append terminalTest 2352 2360 2368 terminal_data_02352 terminal_data_02360

theorem terminal_data_join_02336_02368 : FiniteChecks.Interval terminalTest 2336 2368 :=
  FiniteChecks.interval_append terminalTest 2336 2352 2368 terminal_data_join_02336_02352 terminal_data_join_02352_02368

theorem terminal_data_join_02304_02368 : FiniteChecks.Interval terminalTest 2304 2368 :=
  FiniteChecks.interval_append terminalTest 2304 2336 2368 terminal_data_join_02304_02336 terminal_data_join_02336_02368

theorem terminal_data_join_02248_02368 : FiniteChecks.Interval terminalTest 2248 2368 :=
  FiniteChecks.interval_append terminalTest 2248 2304 2368 terminal_data_join_02248_02304 terminal_data_join_02304_02368

theorem terminal_data_join_02128_02368 : FiniteChecks.Interval terminalTest 2128 2368 :=
  FiniteChecks.interval_append terminalTest 2128 2248 2368 terminal_data_join_02128_02248 terminal_data_join_02248_02368

theorem terminal_data_join_01896_02368 : FiniteChecks.Interval terminalTest 1896 2368 :=
  FiniteChecks.interval_append terminalTest 1896 2128 2368 terminal_data_join_01896_02128 terminal_data_join_02128_02368

theorem terminal_data_join_02376_02392 : FiniteChecks.Interval terminalTest 2376 2392 :=
  FiniteChecks.interval_append terminalTest 2376 2384 2392 terminal_data_02376 terminal_data_02384

theorem terminal_data_join_02368_02392 : FiniteChecks.Interval terminalTest 2368 2392 :=
  FiniteChecks.interval_append terminalTest 2368 2376 2392 terminal_data_02368 terminal_data_join_02376_02392

theorem terminal_data_join_02392_02408 : FiniteChecks.Interval terminalTest 2392 2408 :=
  FiniteChecks.interval_append terminalTest 2392 2400 2408 terminal_data_02392 terminal_data_02400

theorem terminal_data_join_02408_02424 : FiniteChecks.Interval terminalTest 2408 2424 :=
  FiniteChecks.interval_append terminalTest 2408 2416 2424 terminal_data_02408 terminal_data_02416

theorem terminal_data_join_02392_02424 : FiniteChecks.Interval terminalTest 2392 2424 :=
  FiniteChecks.interval_append terminalTest 2392 2408 2424 terminal_data_join_02392_02408 terminal_data_join_02408_02424

theorem terminal_data_join_02368_02424 : FiniteChecks.Interval terminalTest 2368 2424 :=
  FiniteChecks.interval_append terminalTest 2368 2392 2424 terminal_data_join_02368_02392 terminal_data_join_02392_02424

theorem terminal_data_join_02424_02440 : FiniteChecks.Interval terminalTest 2424 2440 :=
  FiniteChecks.interval_append terminalTest 2424 2432 2440 terminal_data_02424 terminal_data_02432

theorem terminal_data_join_02440_02456 : FiniteChecks.Interval terminalTest 2440 2456 :=
  FiniteChecks.interval_append terminalTest 2440 2448 2456 terminal_data_02440 terminal_data_02448

theorem terminal_data_join_02424_02456 : FiniteChecks.Interval terminalTest 2424 2456 :=
  FiniteChecks.interval_append terminalTest 2424 2440 2456 terminal_data_join_02424_02440 terminal_data_join_02440_02456

theorem terminal_data_join_02456_02472 : FiniteChecks.Interval terminalTest 2456 2472 :=
  FiniteChecks.interval_append terminalTest 2456 2464 2472 terminal_data_02456 terminal_data_02464

theorem terminal_data_join_02472_02488 : FiniteChecks.Interval terminalTest 2472 2488 :=
  FiniteChecks.interval_append terminalTest 2472 2480 2488 terminal_data_02472 terminal_data_02480

theorem terminal_data_join_02456_02488 : FiniteChecks.Interval terminalTest 2456 2488 :=
  FiniteChecks.interval_append terminalTest 2456 2472 2488 terminal_data_join_02456_02472 terminal_data_join_02472_02488

theorem terminal_data_join_02424_02488 : FiniteChecks.Interval terminalTest 2424 2488 :=
  FiniteChecks.interval_append terminalTest 2424 2456 2488 terminal_data_join_02424_02456 terminal_data_join_02456_02488

theorem terminal_data_join_02368_02488 : FiniteChecks.Interval terminalTest 2368 2488 :=
  FiniteChecks.interval_append terminalTest 2368 2424 2488 terminal_data_join_02368_02424 terminal_data_join_02424_02488

theorem terminal_data_join_02496_02512 : FiniteChecks.Interval terminalTest 2496 2512 :=
  FiniteChecks.interval_append terminalTest 2496 2504 2512 terminal_data_02496 terminal_data_02504

theorem terminal_data_join_02488_02512 : FiniteChecks.Interval terminalTest 2488 2512 :=
  FiniteChecks.interval_append terminalTest 2488 2496 2512 terminal_data_02488 terminal_data_join_02496_02512

theorem terminal_data_join_02512_02528 : FiniteChecks.Interval terminalTest 2512 2528 :=
  FiniteChecks.interval_append terminalTest 2512 2520 2528 terminal_data_02512 terminal_data_02520

theorem terminal_data_join_02528_02544 : FiniteChecks.Interval terminalTest 2528 2544 :=
  FiniteChecks.interval_append terminalTest 2528 2536 2544 terminal_data_02528 terminal_data_02536

theorem terminal_data_join_02512_02544 : FiniteChecks.Interval terminalTest 2512 2544 :=
  FiniteChecks.interval_append terminalTest 2512 2528 2544 terminal_data_join_02512_02528 terminal_data_join_02528_02544

theorem terminal_data_join_02488_02544 : FiniteChecks.Interval terminalTest 2488 2544 :=
  FiniteChecks.interval_append terminalTest 2488 2512 2544 terminal_data_join_02488_02512 terminal_data_join_02512_02544

theorem terminal_data_join_02544_02560 : FiniteChecks.Interval terminalTest 2544 2560 :=
  FiniteChecks.interval_append terminalTest 2544 2552 2560 terminal_data_02544 terminal_data_02552

theorem terminal_data_join_02560_02576 : FiniteChecks.Interval terminalTest 2560 2576 :=
  FiniteChecks.interval_append terminalTest 2560 2568 2576 terminal_data_02560 terminal_data_02568

theorem terminal_data_join_02544_02576 : FiniteChecks.Interval terminalTest 2544 2576 :=
  FiniteChecks.interval_append terminalTest 2544 2560 2576 terminal_data_join_02544_02560 terminal_data_join_02560_02576

theorem terminal_data_join_02576_02592 : FiniteChecks.Interval terminalTest 2576 2592 :=
  FiniteChecks.interval_append terminalTest 2576 2584 2592 terminal_data_02576 terminal_data_02584

theorem terminal_data_join_02592_02608 : FiniteChecks.Interval terminalTest 2592 2608 :=
  FiniteChecks.interval_append terminalTest 2592 2600 2608 terminal_data_02592 terminal_data_02600

theorem terminal_data_join_02576_02608 : FiniteChecks.Interval terminalTest 2576 2608 :=
  FiniteChecks.interval_append terminalTest 2576 2592 2608 terminal_data_join_02576_02592 terminal_data_join_02592_02608

theorem terminal_data_join_02544_02608 : FiniteChecks.Interval terminalTest 2544 2608 :=
  FiniteChecks.interval_append terminalTest 2544 2576 2608 terminal_data_join_02544_02576 terminal_data_join_02576_02608

theorem terminal_data_join_02488_02608 : FiniteChecks.Interval terminalTest 2488 2608 :=
  FiniteChecks.interval_append terminalTest 2488 2544 2608 terminal_data_join_02488_02544 terminal_data_join_02544_02608

theorem terminal_data_join_02368_02608 : FiniteChecks.Interval terminalTest 2368 2608 :=
  FiniteChecks.interval_append terminalTest 2368 2488 2608 terminal_data_join_02368_02488 terminal_data_join_02488_02608

theorem terminal_data_join_02616_02632 : FiniteChecks.Interval terminalTest 2616 2632 :=
  FiniteChecks.interval_append terminalTest 2616 2624 2632 terminal_data_02616 terminal_data_02624

theorem terminal_data_join_02608_02632 : FiniteChecks.Interval terminalTest 2608 2632 :=
  FiniteChecks.interval_append terminalTest 2608 2616 2632 terminal_data_02608 terminal_data_join_02616_02632

theorem terminal_data_join_02632_02648 : FiniteChecks.Interval terminalTest 2632 2648 :=
  FiniteChecks.interval_append terminalTest 2632 2640 2648 terminal_data_02632 terminal_data_02640

theorem terminal_data_join_02648_02664 : FiniteChecks.Interval terminalTest 2648 2664 :=
  FiniteChecks.interval_append terminalTest 2648 2656 2664 terminal_data_02648 terminal_data_02656

theorem terminal_data_join_02632_02664 : FiniteChecks.Interval terminalTest 2632 2664 :=
  FiniteChecks.interval_append terminalTest 2632 2648 2664 terminal_data_join_02632_02648 terminal_data_join_02648_02664

theorem terminal_data_join_02608_02664 : FiniteChecks.Interval terminalTest 2608 2664 :=
  FiniteChecks.interval_append terminalTest 2608 2632 2664 terminal_data_join_02608_02632 terminal_data_join_02632_02664

theorem terminal_data_join_02664_02680 : FiniteChecks.Interval terminalTest 2664 2680 :=
  FiniteChecks.interval_append terminalTest 2664 2672 2680 terminal_data_02664 terminal_data_02672

theorem terminal_data_join_02680_02696 : FiniteChecks.Interval terminalTest 2680 2696 :=
  FiniteChecks.interval_append terminalTest 2680 2688 2696 terminal_data_02680 terminal_data_02688

theorem terminal_data_join_02664_02696 : FiniteChecks.Interval terminalTest 2664 2696 :=
  FiniteChecks.interval_append terminalTest 2664 2680 2696 terminal_data_join_02664_02680 terminal_data_join_02680_02696

theorem terminal_data_join_02696_02712 : FiniteChecks.Interval terminalTest 2696 2712 :=
  FiniteChecks.interval_append terminalTest 2696 2704 2712 terminal_data_02696 terminal_data_02704

theorem terminal_data_join_02712_02728 : FiniteChecks.Interval terminalTest 2712 2728 :=
  FiniteChecks.interval_append terminalTest 2712 2720 2728 terminal_data_02712 terminal_data_02720

theorem terminal_data_join_02696_02728 : FiniteChecks.Interval terminalTest 2696 2728 :=
  FiniteChecks.interval_append terminalTest 2696 2712 2728 terminal_data_join_02696_02712 terminal_data_join_02712_02728

theorem terminal_data_join_02664_02728 : FiniteChecks.Interval terminalTest 2664 2728 :=
  FiniteChecks.interval_append terminalTest 2664 2696 2728 terminal_data_join_02664_02696 terminal_data_join_02696_02728

theorem terminal_data_join_02608_02728 : FiniteChecks.Interval terminalTest 2608 2728 :=
  FiniteChecks.interval_append terminalTest 2608 2664 2728 terminal_data_join_02608_02664 terminal_data_join_02664_02728

theorem terminal_data_join_02736_02752 : FiniteChecks.Interval terminalTest 2736 2752 :=
  FiniteChecks.interval_append terminalTest 2736 2744 2752 terminal_data_02736 terminal_data_02744

theorem terminal_data_join_02728_02752 : FiniteChecks.Interval terminalTest 2728 2752 :=
  FiniteChecks.interval_append terminalTest 2728 2736 2752 terminal_data_02728 terminal_data_join_02736_02752


end Papers.RationalityTen.ConcretePolygonClassification.N7
