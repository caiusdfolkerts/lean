module
prelude
public import SharedTriangleCountsData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
open Papers.RationalityTen FiniteChecks

namespace Papers.RationalityTen.SharedTriangleCounts
theorem Check016.part2048 : Interval test 2048 2056 :=
  interval_of_check _ 2048 8 (by decide +kernel)
theorem Check016.part2056 : Interval test 2056 2064 :=
  interval_of_check _ 2056 8 (by decide +kernel)
theorem Check016.part2064 : Interval test 2064 2072 :=
  interval_of_check _ 2064 8 (by decide +kernel)
theorem Check016.part2072 : Interval test 2072 2080 :=
  interval_of_check _ 2072 8 (by decide +kernel)
theorem Check016.part2080 : Interval test 2080 2088 :=
  interval_of_check _ 2080 8 (by decide +kernel)
theorem Check016.part2088 : Interval test 2088 2096 :=
  interval_of_check _ 2088 8 (by decide +kernel)
theorem Check016.part2096 : Interval test 2096 2104 :=
  interval_of_check _ 2096 8 (by decide +kernel)
theorem Check016.part2104 : Interval test 2104 2112 :=
  interval_of_check _ 2104 8 (by decide +kernel)
theorem Check016.part2112 : Interval test 2112 2120 :=
  interval_of_check _ 2112 8 (by decide +kernel)
theorem Check016.part2120 : Interval test 2120 2128 :=
  interval_of_check _ 2120 8 (by decide +kernel)
theorem Check016.part2128 : Interval test 2128 2136 :=
  interval_of_check _ 2128 8 (by decide +kernel)
theorem Check016.part2136 : Interval test 2136 2144 :=
  interval_of_check _ 2136 8 (by decide +kernel)
theorem Check016.part2144 : Interval test 2144 2152 :=
  interval_of_check _ 2144 8 (by decide +kernel)
theorem Check016.part2152 : Interval test 2152 2160 :=
  interval_of_check _ 2152 8 (by decide +kernel)
theorem Check016.part2160 : Interval test 2160 2168 :=
  interval_of_check _ 2160 8 (by decide +kernel)
theorem Check016.part2168 : Interval test 2168 2176 :=
  interval_of_check _ 2168 8 (by decide +kernel)
theorem Check016.checked : Interval test 2048 2176 :=
  (FiniteChecks.interval_append test 2048 2112 2176
  (FiniteChecks.interval_append test 2048 2080 2112
  (FiniteChecks.interval_append test 2048 2064 2080
  (FiniteChecks.interval_append test 2048 2056 2064
  Check016.part2048
  Check016.part2056)
  (FiniteChecks.interval_append test 2064 2072 2080
  Check016.part2064
  Check016.part2072))
  (FiniteChecks.interval_append test 2080 2096 2112
  (FiniteChecks.interval_append test 2080 2088 2096
  Check016.part2080
  Check016.part2088)
  (FiniteChecks.interval_append test 2096 2104 2112
  Check016.part2096
  Check016.part2104)))
  (FiniteChecks.interval_append test 2112 2144 2176
  (FiniteChecks.interval_append test 2112 2128 2144
  (FiniteChecks.interval_append test 2112 2120 2128
  Check016.part2112
  Check016.part2120)
  (FiniteChecks.interval_append test 2128 2136 2144
  Check016.part2128
  Check016.part2136))
  (FiniteChecks.interval_append test 2144 2160 2176
  (FiniteChecks.interval_append test 2144 2152 2160
  Check016.part2144
  Check016.part2152)
  (FiniteChecks.interval_append test 2160 2168 2176
  Check016.part2160
  Check016.part2168))))
theorem Check017.part2176 : Interval test 2176 2184 :=
  interval_of_check _ 2176 8 (by decide +kernel)
theorem Check017.part2184 : Interval test 2184 2192 :=
  interval_of_check _ 2184 8 (by decide +kernel)
theorem Check017.part2192 : Interval test 2192 2200 :=
  interval_of_check _ 2192 8 (by decide +kernel)
theorem Check017.part2200 : Interval test 2200 2208 :=
  interval_of_check _ 2200 8 (by decide +kernel)
theorem Check017.part2208 : Interval test 2208 2216 :=
  interval_of_check _ 2208 8 (by decide +kernel)
theorem Check017.part2216 : Interval test 2216 2224 :=
  interval_of_check _ 2216 8 (by decide +kernel)
theorem Check017.part2224 : Interval test 2224 2232 :=
  interval_of_check _ 2224 8 (by decide +kernel)
theorem Check017.part2232 : Interval test 2232 2240 :=
  interval_of_check _ 2232 8 (by decide +kernel)
theorem Check017.part2240 : Interval test 2240 2248 :=
  interval_of_check _ 2240 8 (by decide +kernel)
theorem Check017.part2248 : Interval test 2248 2256 :=
  interval_of_check _ 2248 8 (by decide +kernel)
theorem Check017.part2256 : Interval test 2256 2264 :=
  interval_of_check _ 2256 8 (by decide +kernel)
theorem Check017.part2264 : Interval test 2264 2272 :=
  interval_of_check _ 2264 8 (by decide +kernel)
theorem Check017.part2272 : Interval test 2272 2280 :=
  interval_of_check _ 2272 8 (by decide +kernel)
theorem Check017.part2280 : Interval test 2280 2288 :=
  interval_of_check _ 2280 8 (by decide +kernel)
theorem Check017.part2288 : Interval test 2288 2296 :=
  interval_of_check _ 2288 8 (by decide +kernel)
theorem Check017.part2296 : Interval test 2296 2304 :=
  interval_of_check _ 2296 8 (by decide +kernel)
theorem Check017.checked : Interval test 2176 2304 :=
  (FiniteChecks.interval_append test 2176 2240 2304
  (FiniteChecks.interval_append test 2176 2208 2240
  (FiniteChecks.interval_append test 2176 2192 2208
  (FiniteChecks.interval_append test 2176 2184 2192
  Check017.part2176
  Check017.part2184)
  (FiniteChecks.interval_append test 2192 2200 2208
  Check017.part2192
  Check017.part2200))
  (FiniteChecks.interval_append test 2208 2224 2240
  (FiniteChecks.interval_append test 2208 2216 2224
  Check017.part2208
  Check017.part2216)
  (FiniteChecks.interval_append test 2224 2232 2240
  Check017.part2224
  Check017.part2232)))
  (FiniteChecks.interval_append test 2240 2272 2304
  (FiniteChecks.interval_append test 2240 2256 2272
  (FiniteChecks.interval_append test 2240 2248 2256
  Check017.part2240
  Check017.part2248)
  (FiniteChecks.interval_append test 2256 2264 2272
  Check017.part2256
  Check017.part2264))
  (FiniteChecks.interval_append test 2272 2288 2304
  (FiniteChecks.interval_append test 2272 2280 2288
  Check017.part2272
  Check017.part2280)
  (FiniteChecks.interval_append test 2288 2296 2304
  Check017.part2288
  Check017.part2296))))
theorem Check018.part2304 : Interval test 2304 2312 :=
  interval_of_check _ 2304 8 (by decide +kernel)
theorem Check018.part2312 : Interval test 2312 2320 :=
  interval_of_check _ 2312 8 (by decide +kernel)
theorem Check018.part2320 : Interval test 2320 2328 :=
  interval_of_check _ 2320 8 (by decide +kernel)
theorem Check018.part2328 : Interval test 2328 2336 :=
  interval_of_check _ 2328 8 (by decide +kernel)
theorem Check018.part2336 : Interval test 2336 2344 :=
  interval_of_check _ 2336 8 (by decide +kernel)
theorem Check018.part2344 : Interval test 2344 2352 :=
  interval_of_check _ 2344 8 (by decide +kernel)
theorem Check018.part2352 : Interval test 2352 2360 :=
  interval_of_check _ 2352 8 (by decide +kernel)
theorem Check018.part2360 : Interval test 2360 2368 :=
  interval_of_check _ 2360 8 (by decide +kernel)
theorem Check018.part2368 : Interval test 2368 2376 :=
  interval_of_check _ 2368 8 (by decide +kernel)
theorem Check018.part2376 : Interval test 2376 2384 :=
  interval_of_check _ 2376 8 (by decide +kernel)
theorem Check018.part2384 : Interval test 2384 2392 :=
  interval_of_check _ 2384 8 (by decide +kernel)
theorem Check018.part2392 : Interval test 2392 2400 :=
  interval_of_check _ 2392 8 (by decide +kernel)
theorem Check018.part2400 : Interval test 2400 2408 :=
  interval_of_check _ 2400 8 (by decide +kernel)
theorem Check018.part2408 : Interval test 2408 2416 :=
  interval_of_check _ 2408 8 (by decide +kernel)
theorem Check018.part2416 : Interval test 2416 2424 :=
  interval_of_check _ 2416 8 (by decide +kernel)
theorem Check018.part2424 : Interval test 2424 2432 :=
  interval_of_check _ 2424 8 (by decide +kernel)
theorem Check018.checked : Interval test 2304 2432 :=
  (FiniteChecks.interval_append test 2304 2368 2432
  (FiniteChecks.interval_append test 2304 2336 2368
  (FiniteChecks.interval_append test 2304 2320 2336
  (FiniteChecks.interval_append test 2304 2312 2320
  Check018.part2304
  Check018.part2312)
  (FiniteChecks.interval_append test 2320 2328 2336
  Check018.part2320
  Check018.part2328))
  (FiniteChecks.interval_append test 2336 2352 2368
  (FiniteChecks.interval_append test 2336 2344 2352
  Check018.part2336
  Check018.part2344)
  (FiniteChecks.interval_append test 2352 2360 2368
  Check018.part2352
  Check018.part2360)))
  (FiniteChecks.interval_append test 2368 2400 2432
  (FiniteChecks.interval_append test 2368 2384 2400
  (FiniteChecks.interval_append test 2368 2376 2384
  Check018.part2368
  Check018.part2376)
  (FiniteChecks.interval_append test 2384 2392 2400
  Check018.part2384
  Check018.part2392))
  (FiniteChecks.interval_append test 2400 2416 2432
  (FiniteChecks.interval_append test 2400 2408 2416
  Check018.part2400
  Check018.part2408)
  (FiniteChecks.interval_append test 2416 2424 2432
  Check018.part2416
  Check018.part2424))))
theorem Check019.part2432 : Interval test 2432 2440 :=
  interval_of_check _ 2432 8 (by decide +kernel)
theorem Check019.part2440 : Interval test 2440 2448 :=
  interval_of_check _ 2440 8 (by decide +kernel)
theorem Check019.part2448 : Interval test 2448 2456 :=
  interval_of_check _ 2448 8 (by decide +kernel)
theorem Check019.part2456 : Interval test 2456 2464 :=
  interval_of_check _ 2456 8 (by decide +kernel)
theorem Check019.part2464 : Interval test 2464 2472 :=
  interval_of_check _ 2464 8 (by decide +kernel)
theorem Check019.part2472 : Interval test 2472 2480 :=
  interval_of_check _ 2472 8 (by decide +kernel)
theorem Check019.part2480 : Interval test 2480 2488 :=
  interval_of_check _ 2480 8 (by decide +kernel)
theorem Check019.part2488 : Interval test 2488 2496 :=
  interval_of_check _ 2488 8 (by decide +kernel)
theorem Check019.part2496 : Interval test 2496 2504 :=
  interval_of_check _ 2496 8 (by decide +kernel)
theorem Check019.part2504 : Interval test 2504 2512 :=
  interval_of_check _ 2504 8 (by decide +kernel)
theorem Check019.part2512 : Interval test 2512 2520 :=
  interval_of_check _ 2512 8 (by decide +kernel)
theorem Check019.part2520 : Interval test 2520 2528 :=
  interval_of_check _ 2520 8 (by decide +kernel)
theorem Check019.part2528 : Interval test 2528 2536 :=
  interval_of_check _ 2528 8 (by decide +kernel)
theorem Check019.part2536 : Interval test 2536 2544 :=
  interval_of_check _ 2536 8 (by decide +kernel)
theorem Check019.part2544 : Interval test 2544 2552 :=
  interval_of_check _ 2544 8 (by decide +kernel)
theorem Check019.part2552 : Interval test 2552 2560 :=
  interval_of_check _ 2552 8 (by decide +kernel)
theorem Check019.checked : Interval test 2432 2560 :=
  (FiniteChecks.interval_append test 2432 2496 2560
  (FiniteChecks.interval_append test 2432 2464 2496
  (FiniteChecks.interval_append test 2432 2448 2464
  (FiniteChecks.interval_append test 2432 2440 2448
  Check019.part2432
  Check019.part2440)
  (FiniteChecks.interval_append test 2448 2456 2464
  Check019.part2448
  Check019.part2456))
  (FiniteChecks.interval_append test 2464 2480 2496
  (FiniteChecks.interval_append test 2464 2472 2480
  Check019.part2464
  Check019.part2472)
  (FiniteChecks.interval_append test 2480 2488 2496
  Check019.part2480
  Check019.part2488)))
  (FiniteChecks.interval_append test 2496 2528 2560
  (FiniteChecks.interval_append test 2496 2512 2528
  (FiniteChecks.interval_append test 2496 2504 2512
  Check019.part2496
  Check019.part2504)
  (FiniteChecks.interval_append test 2512 2520 2528
  Check019.part2512
  Check019.part2520))
  (FiniteChecks.interval_append test 2528 2544 2560
  (FiniteChecks.interval_append test 2528 2536 2544
  Check019.part2528
  Check019.part2536)
  (FiniteChecks.interval_append test 2544 2552 2560
  Check019.part2544
  Check019.part2552))))
theorem Check020.part2560 : Interval test 2560 2568 :=
  interval_of_check _ 2560 8 (by decide +kernel)
theorem Check020.part2568 : Interval test 2568 2576 :=
  interval_of_check _ 2568 8 (by decide +kernel)
theorem Check020.part2576 : Interval test 2576 2584 :=
  interval_of_check _ 2576 8 (by decide +kernel)
theorem Check020.part2584 : Interval test 2584 2592 :=
  interval_of_check _ 2584 8 (by decide +kernel)
theorem Check020.part2592 : Interval test 2592 2600 :=
  interval_of_check _ 2592 8 (by decide +kernel)
theorem Check020.part2600 : Interval test 2600 2608 :=
  interval_of_check _ 2600 8 (by decide +kernel)
theorem Check020.part2608 : Interval test 2608 2616 :=
  interval_of_check _ 2608 8 (by decide +kernel)
theorem Check020.part2616 : Interval test 2616 2624 :=
  interval_of_check _ 2616 8 (by decide +kernel)
theorem Check020.part2624 : Interval test 2624 2632 :=
  interval_of_check _ 2624 8 (by decide +kernel)
theorem Check020.part2632 : Interval test 2632 2640 :=
  interval_of_check _ 2632 8 (by decide +kernel)
theorem Check020.part2640 : Interval test 2640 2648 :=
  interval_of_check _ 2640 8 (by decide +kernel)
theorem Check020.part2648 : Interval test 2648 2656 :=
  interval_of_check _ 2648 8 (by decide +kernel)
theorem Check020.part2656 : Interval test 2656 2664 :=
  interval_of_check _ 2656 8 (by decide +kernel)
theorem Check020.part2664 : Interval test 2664 2672 :=
  interval_of_check _ 2664 8 (by decide +kernel)
theorem Check020.part2672 : Interval test 2672 2680 :=
  interval_of_check _ 2672 8 (by decide +kernel)
theorem Check020.part2680 : Interval test 2680 2688 :=
  interval_of_check _ 2680 8 (by decide +kernel)
theorem Check020.checked : Interval test 2560 2688 :=
  (FiniteChecks.interval_append test 2560 2624 2688
  (FiniteChecks.interval_append test 2560 2592 2624
  (FiniteChecks.interval_append test 2560 2576 2592
  (FiniteChecks.interval_append test 2560 2568 2576
  Check020.part2560
  Check020.part2568)
  (FiniteChecks.interval_append test 2576 2584 2592
  Check020.part2576
  Check020.part2584))
  (FiniteChecks.interval_append test 2592 2608 2624
  (FiniteChecks.interval_append test 2592 2600 2608
  Check020.part2592
  Check020.part2600)
  (FiniteChecks.interval_append test 2608 2616 2624
  Check020.part2608
  Check020.part2616)))
  (FiniteChecks.interval_append test 2624 2656 2688
  (FiniteChecks.interval_append test 2624 2640 2656
  (FiniteChecks.interval_append test 2624 2632 2640
  Check020.part2624
  Check020.part2632)
  (FiniteChecks.interval_append test 2640 2648 2656
  Check020.part2640
  Check020.part2648))
  (FiniteChecks.interval_append test 2656 2672 2688
  (FiniteChecks.interval_append test 2656 2664 2672
  Check020.part2656
  Check020.part2664)
  (FiniteChecks.interval_append test 2672 2680 2688
  Check020.part2672
  Check020.part2680))))
theorem Check021.part2688 : Interval test 2688 2696 :=
  interval_of_check _ 2688 8 (by decide +kernel)
theorem Check021.part2696 : Interval test 2696 2704 :=
  interval_of_check _ 2696 8 (by decide +kernel)
theorem Check021.part2704 : Interval test 2704 2712 :=
  interval_of_check _ 2704 8 (by decide +kernel)
theorem Check021.part2712 : Interval test 2712 2720 :=
  interval_of_check _ 2712 8 (by decide +kernel)
theorem Check021.part2720 : Interval test 2720 2728 :=
  interval_of_check _ 2720 8 (by decide +kernel)
theorem Check021.part2728 : Interval test 2728 2736 :=
  interval_of_check _ 2728 8 (by decide +kernel)
theorem Check021.part2736 : Interval test 2736 2744 :=
  interval_of_check _ 2736 8 (by decide +kernel)
theorem Check021.part2744 : Interval test 2744 2752 :=
  interval_of_check _ 2744 8 (by decide +kernel)
theorem Check021.part2752 : Interval test 2752 2760 :=
  interval_of_check _ 2752 8 (by decide +kernel)
theorem Check021.part2760 : Interval test 2760 2768 :=
  interval_of_check _ 2760 8 (by decide +kernel)
theorem Check021.part2768 : Interval test 2768 2776 :=
  interval_of_check _ 2768 8 (by decide +kernel)
theorem Check021.part2776 : Interval test 2776 2784 :=
  interval_of_check _ 2776 8 (by decide +kernel)
theorem Check021.part2784 : Interval test 2784 2792 :=
  interval_of_check _ 2784 8 (by decide +kernel)
theorem Check021.part2792 : Interval test 2792 2800 :=
  interval_of_check _ 2792 8 (by decide +kernel)
theorem Check021.part2800 : Interval test 2800 2808 :=
  interval_of_check _ 2800 8 (by decide +kernel)
theorem Check021.part2808 : Interval test 2808 2816 :=
  interval_of_check _ 2808 8 (by decide +kernel)
theorem Check021.checked : Interval test 2688 2816 :=
  (FiniteChecks.interval_append test 2688 2752 2816
  (FiniteChecks.interval_append test 2688 2720 2752
  (FiniteChecks.interval_append test 2688 2704 2720
  (FiniteChecks.interval_append test 2688 2696 2704
  Check021.part2688
  Check021.part2696)
  (FiniteChecks.interval_append test 2704 2712 2720
  Check021.part2704
  Check021.part2712))
  (FiniteChecks.interval_append test 2720 2736 2752
  (FiniteChecks.interval_append test 2720 2728 2736
  Check021.part2720
  Check021.part2728)
  (FiniteChecks.interval_append test 2736 2744 2752
  Check021.part2736
  Check021.part2744)))
  (FiniteChecks.interval_append test 2752 2784 2816
  (FiniteChecks.interval_append test 2752 2768 2784
  (FiniteChecks.interval_append test 2752 2760 2768
  Check021.part2752
  Check021.part2760)
  (FiniteChecks.interval_append test 2768 2776 2784
  Check021.part2768
  Check021.part2776))
  (FiniteChecks.interval_append test 2784 2800 2816
  (FiniteChecks.interval_append test 2784 2792 2800
  Check021.part2784
  Check021.part2792)
  (FiniteChecks.interval_append test 2800 2808 2816
  Check021.part2800
  Check021.part2808))))
theorem Check022.part2816 : Interval test 2816 2824 :=
  interval_of_check _ 2816 8 (by decide +kernel)
theorem Check022.part2824 : Interval test 2824 2832 :=
  interval_of_check _ 2824 8 (by decide +kernel)
theorem Check022.part2832 : Interval test 2832 2840 :=
  interval_of_check _ 2832 8 (by decide +kernel)
theorem Check022.part2840 : Interval test 2840 2848 :=
  interval_of_check _ 2840 8 (by decide +kernel)
theorem Check022.part2848 : Interval test 2848 2856 :=
  interval_of_check _ 2848 8 (by decide +kernel)
theorem Check022.part2856 : Interval test 2856 2864 :=
  interval_of_check _ 2856 8 (by decide +kernel)
theorem Check022.part2864 : Interval test 2864 2872 :=
  interval_of_check _ 2864 8 (by decide +kernel)
theorem Check022.part2872 : Interval test 2872 2880 :=
  interval_of_check _ 2872 8 (by decide +kernel)
theorem Check022.part2880 : Interval test 2880 2888 :=
  interval_of_check _ 2880 8 (by decide +kernel)
theorem Check022.part2888 : Interval test 2888 2896 :=
  interval_of_check _ 2888 8 (by decide +kernel)
theorem Check022.part2896 : Interval test 2896 2904 :=
  interval_of_check _ 2896 8 (by decide +kernel)
theorem Check022.part2904 : Interval test 2904 2912 :=
  interval_of_check _ 2904 8 (by decide +kernel)
theorem Check022.part2912 : Interval test 2912 2920 :=
  interval_of_check _ 2912 8 (by decide +kernel)
theorem Check022.part2920 : Interval test 2920 2928 :=
  interval_of_check _ 2920 8 (by decide +kernel)
theorem Check022.part2928 : Interval test 2928 2936 :=
  interval_of_check _ 2928 8 (by decide +kernel)
theorem Check022.part2936 : Interval test 2936 2944 :=
  interval_of_check _ 2936 8 (by decide +kernel)
theorem Check022.checked : Interval test 2816 2944 :=
  (FiniteChecks.interval_append test 2816 2880 2944
  (FiniteChecks.interval_append test 2816 2848 2880
  (FiniteChecks.interval_append test 2816 2832 2848
  (FiniteChecks.interval_append test 2816 2824 2832
  Check022.part2816
  Check022.part2824)
  (FiniteChecks.interval_append test 2832 2840 2848
  Check022.part2832
  Check022.part2840))
  (FiniteChecks.interval_append test 2848 2864 2880
  (FiniteChecks.interval_append test 2848 2856 2864
  Check022.part2848
  Check022.part2856)
  (FiniteChecks.interval_append test 2864 2872 2880
  Check022.part2864
  Check022.part2872)))
  (FiniteChecks.interval_append test 2880 2912 2944
  (FiniteChecks.interval_append test 2880 2896 2912
  (FiniteChecks.interval_append test 2880 2888 2896
  Check022.part2880
  Check022.part2888)
  (FiniteChecks.interval_append test 2896 2904 2912
  Check022.part2896
  Check022.part2904))
  (FiniteChecks.interval_append test 2912 2928 2944
  (FiniteChecks.interval_append test 2912 2920 2928
  Check022.part2912
  Check022.part2920)
  (FiniteChecks.interval_append test 2928 2936 2944
  Check022.part2928
  Check022.part2936))))
theorem Check023.part2944 : Interval test 2944 2952 :=
  interval_of_check _ 2944 8 (by decide +kernel)
theorem Check023.part2952 : Interval test 2952 2960 :=
  interval_of_check _ 2952 8 (by decide +kernel)
theorem Check023.part2960 : Interval test 2960 2968 :=
  interval_of_check _ 2960 8 (by decide +kernel)
theorem Check023.part2968 : Interval test 2968 2976 :=
  interval_of_check _ 2968 8 (by decide +kernel)
theorem Check023.part2976 : Interval test 2976 2984 :=
  interval_of_check _ 2976 8 (by decide +kernel)
theorem Check023.part2984 : Interval test 2984 2992 :=
  interval_of_check _ 2984 8 (by decide +kernel)
theorem Check023.part2992 : Interval test 2992 3000 :=
  interval_of_check _ 2992 8 (by decide +kernel)
theorem Check023.part3000 : Interval test 3000 3008 :=
  interval_of_check _ 3000 8 (by decide +kernel)
theorem Check023.part3008 : Interval test 3008 3016 :=
  interval_of_check _ 3008 8 (by decide +kernel)
theorem Check023.part3016 : Interval test 3016 3024 :=
  interval_of_check _ 3016 8 (by decide +kernel)
theorem Check023.part3024 : Interval test 3024 3032 :=
  interval_of_check _ 3024 8 (by decide +kernel)
theorem Check023.part3032 : Interval test 3032 3040 :=
  interval_of_check _ 3032 8 (by decide +kernel)
theorem Check023.part3040 : Interval test 3040 3048 :=
  interval_of_check _ 3040 8 (by decide +kernel)
theorem Check023.part3048 : Interval test 3048 3056 :=
  interval_of_check _ 3048 8 (by decide +kernel)
theorem Check023.part3056 : Interval test 3056 3064 :=
  interval_of_check _ 3056 8 (by decide +kernel)
theorem Check023.part3064 : Interval test 3064 3072 :=
  interval_of_check _ 3064 8 (by decide +kernel)
theorem Check023.checked : Interval test 2944 3072 :=
  (FiniteChecks.interval_append test 2944 3008 3072
  (FiniteChecks.interval_append test 2944 2976 3008
  (FiniteChecks.interval_append test 2944 2960 2976
  (FiniteChecks.interval_append test 2944 2952 2960
  Check023.part2944
  Check023.part2952)
  (FiniteChecks.interval_append test 2960 2968 2976
  Check023.part2960
  Check023.part2968))
  (FiniteChecks.interval_append test 2976 2992 3008
  (FiniteChecks.interval_append test 2976 2984 2992
  Check023.part2976
  Check023.part2984)
  (FiniteChecks.interval_append test 2992 3000 3008
  Check023.part2992
  Check023.part3000)))
  (FiniteChecks.interval_append test 3008 3040 3072
  (FiniteChecks.interval_append test 3008 3024 3040
  (FiniteChecks.interval_append test 3008 3016 3024
  Check023.part3008
  Check023.part3016)
  (FiniteChecks.interval_append test 3024 3032 3040
  Check023.part3024
  Check023.part3032))
  (FiniteChecks.interval_append test 3040 3056 3072
  (FiniteChecks.interval_append test 3040 3048 3056
  Check023.part3040
  Check023.part3048)
  (FiniteChecks.interval_append test 3056 3064 3072
  Check023.part3056
  Check023.part3064))))
end Papers.RationalityTen.SharedTriangleCounts
