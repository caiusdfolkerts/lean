module
prelude
public import RootedSixExtra00GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport7_000 : List Nat := [0,1,2,3,4,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156]
def ridgeSupport7_001 : List Nat := [157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188]
def ridgeSupport7_002 : List Nat := [189,190,191,192,193,194,195,196,197,198,199,200,201,2584,2585,2586,2587,2588,2589,2590,2591,2592,2593,2594,2595,2596,2597,2598,2599,2600,2601,2602]
def ridgeSupport7_003 : List Nat := [2603,2604,2605,2606,2607,2608,2609,2610,2611,2612,2613,2614,2615,2616,2617,2618,2619,2620,2621,2622,2623,2624,2625,2626,2627,2628,2629,2630,2631,2632,2633,2634]
def ridgeSupport7_004 : List Nat := [2635,2636,2637,2638,2639,2640,2641,2642,2643,2644,2645,2646,2647,2648,2649,2650,2651,2652,2653,2654,2655,2656,2657,2658,2659,2660,2661,2662,2663,2664,2665,2666]
def ridgeSupport7_005 : List Nat := [2667,2668,2669,2670,2671,2672,2673,2674,2675,2676,2677,2678,2679,2680,2681,2682,2683,2684,2685,2686,2687,2688,2689,2690,2691,2692,2693,2694,2695,2696,2697,2698]
def ridgeSupport7_006 : List Nat := [2699,2700,2701,2702,2703,2704,2705,2706,2707,2708,2709,2710,2711,2712,2713,2714,2715,2716,2717,2718,2719,2720,2721,2722,2723,2724,2725,2726,2727,2728,2729,2730]
def ridgeSupport7_007 : List Nat := [2731,2732,2733,2734,2735,2736,2737,2738,2739,2740,2741,2742,2743,2744,2745,2746,2747,2748,2749,2750,2751,2752,2753,2754,2755,2756,2757,2758,2759,2760,2761,2762]
def ridgeSupport7_008 : List Nat := [2763,2764,2765,2766,2767,2768,2769,2770,2771,2772,2773,2774,2775,2776,2777,2778,2779,2780,2781,2782,2783,2784,2785,2786,2787,2788,2789,2790,2791,2792,2793,2794]
def ridgeSupport7_009 : List Nat := [2795,2796,2797,2798,2799,2800,2801,2802,2803,2804,2805,2806,2807,2808,2809,2810,2811,2812,2813,2814,2815,2816,2817,2818,2819,2820,2821,2822,2823,2824,2825,2826]
def ridgeSupport7_010 : List Nat := [2827,2828,2829,2830,2831,2832,2833,2834,2835,2836,2837,2838,2839,2840,2841,2842,2843,2844,2845,2846,2847,2848,2849,2850,2851,2852,2853,2854,2855,2856,2857,2858]
def ridgeSupport7_011 : List Nat := [2859,2860,2861,2862,2863,2864,2865,2866,2867,2868,2869,2870,2871,7156,7157,7158,7159,7160,7161,7162,7163,7164,7165,7166,7167,7168,7169,7170,7171,7172,7173,7174]
def ridgeSupport7_012 : List Nat := [7175,7176,7177,7178,7179,7816,7817,7818,7819,7820,7821,7822,7823,7824,7825,7826,7827,7828,7829,7830,7831,7832,7833,7834,7835,7836,7837,7838,7839,7840,7841,7842]
def ridgeSupport7_013 : List Nat := [7843,7844,7845,7846,7847,7848,7849,7850,7851,7852,7853,7854,7855,7856,7857,7858,7859,7860,7861,7862,7863,7864,7865,7866,7867,7868,7869,7870,7871,7872,7873,7874]
def ridgeSupport7_014 : List Nat := [7875,7876,7877,7878,7879,7880,7881,7882,7883,7884,7885,7886,7887]
def ridgeSupport7_code : Nat := 0x1ecf7b39ecd7b31ecb7b29ec97b21ec77b19ec57b11ec37b09ec17b01ebf7af9ebd7af1ebb7ae9eb97ae1eb77ad9eb57ad1eb37ac9eb17ac1eaf7ab9ead7ab1eab7aa9ea97aa1ea77a99ea57a91ea37a89ea17a81e9f7a79e9d7a71e9b7a69e997a61e977a59e957a51e937a49e917a41e8f7a39e8d7a31e8b7a29e897a21c0b7029c097021c077019c057011c037009c017001bff6ff9bfd6ff1bfb6fe9bf96fe1bf76fd9bf56fd0b372cd8b352cd0b332cc8b312cc0b2f2cb8b2d2cb0b2b2ca8b292ca0b272c98b252c90b232c88b212c80b1f2c78b1d2c70b1b2c68b192c60b172c58b152c50b132c48b112c40b0f2c38b0d2c30b0b2c28b092c20b072c18b052c10b032c08b012c00aff2bf8afd2bf0afb2be8af92be0af72bd8af52bd0af32bc8af12bc0aef2bb8aed2bb0aeb2ba8ae92ba0ae72b98ae52b90ae32b88ae12b80adf2b78add2b70adb2b68ad92b60ad72b58ad52b50ad32b48ad12b40acf2b38acd2b30acb2b28ac92b20ac72b18ac52b10ac32b08ac12b00abf2af8abd2af0abb2ae8ab92ae0ab72ad8ab52ad0ab32ac8ab12ac0aaf2ab8aad2ab0aab2aa8aa92aa0aa72a98aa52a90aa32a88aa12a80a9f2a78a9d2a70a9b2a68a992a60a972a58a952a50a932a48a912a40a8f2a38a8d2a30a8b2a28a892a20a872a18a852a10a832a08a812a00a7f29f8a7d29f0a7b29e8a7929e0a7729d8a7529d0a7329c8a7129c0a6f29b8a6d29b0a6b29a8a6929a0a672998a652990a632988a612980a5f2978a5d2970a5b2968a592960a572958a552950a532948a512940a4f2938a4d2930a4b2928a492920a472918a452910a432908a412900a3f28f8a3d28f0a3b28e8a3928e0a3728d8a3528d0a3328c8a3128c0a2f28b8a2d28b0a2b28a8a2928a0a272898a252890a232888a212880a1f2878a1d2870a1b2868a1928600c903200c703180c503100c303080c103000bf02f80bd02f00bb02e80b902e00b702d80b502d00b302c80b102c00af02b80ad02b00ab02a80a902a00a702980a502900a302880a1028009f027809d027009b02680990260097025809502500930248091024008f023808d023008b02280890220087021808502100830208004000c0020004000
def ridgeSupport7_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport7_code
def ridgeSupport7_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport7_code
def ridgeSupport7_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport7_code
def ridgeSupport7_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport7_code
def ridgeSupport7_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport7_code
def ridgeSupport7_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport7_code
def ridgeSupport7_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport7_code
def ridgeSupport7_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport7_code
def ridgeSupport7_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport7_code
def ridgeSupport7_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport7_code
def ridgeSupport7_rest_010 : Nat := PackedRawNatGrowth.drop 4480 ridgeSupport7_code
def ridgeSupport7_rest_011 : Nat := PackedRawNatGrowth.drop 4928 ridgeSupport7_code
def ridgeSupport7_rest_012 : Nat := PackedRawNatGrowth.drop 5376 ridgeSupport7_code
def ridgeSupport7_rest_013 : Nat := PackedRawNatGrowth.drop 5824 ridgeSupport7_code
def ridgeSupport7_rest_014 : Nat := PackedRawNatGrowth.drop 6272 ridgeSupport7_code
def ridgeSupport7_rest_015 : Nat := PackedRawNatGrowth.drop 6454 ridgeSupport7_code
def ridgeSupport7_suffix_015 : List Nat := []
def ridgeSupport7_suffix_014 : List Nat := ridgeSupport7_014 ++ ridgeSupport7_suffix_015
def ridgeSupport7_suffix_013 : List Nat := ridgeSupport7_013 ++ ridgeSupport7_suffix_014
def ridgeSupport7_suffix_012 : List Nat := ridgeSupport7_012 ++ ridgeSupport7_suffix_013
def ridgeSupport7_suffix_011 : List Nat := ridgeSupport7_011 ++ ridgeSupport7_suffix_012
def ridgeSupport7_suffix_010 : List Nat := ridgeSupport7_010 ++ ridgeSupport7_suffix_011
def ridgeSupport7_suffix_009 : List Nat := ridgeSupport7_009 ++ ridgeSupport7_suffix_010
def ridgeSupport7_suffix_008 : List Nat := ridgeSupport7_008 ++ ridgeSupport7_suffix_009
def ridgeSupport7_suffix_007 : List Nat := ridgeSupport7_007 ++ ridgeSupport7_suffix_008
def ridgeSupport7_suffix_006 : List Nat := ridgeSupport7_006 ++ ridgeSupport7_suffix_007
def ridgeSupport7_suffix_005 : List Nat := ridgeSupport7_005 ++ ridgeSupport7_suffix_006
def ridgeSupport7_suffix_004 : List Nat := ridgeSupport7_004 ++ ridgeSupport7_suffix_005
def ridgeSupport7_suffix_003 : List Nat := ridgeSupport7_003 ++ ridgeSupport7_suffix_004
def ridgeSupport7_suffix_002 : List Nat := ridgeSupport7_002 ++ ridgeSupport7_suffix_003
def ridgeSupport7_suffix_001 : List Nat := ridgeSupport7_001 ++ ridgeSupport7_suffix_002
def ridgeSupport7_suffix_000 : List Nat := ridgeSupport7_000 ++ ridgeSupport7_suffix_001
theorem ridgeSupport7_source : candidateSupports 7 =
    (PackedRawNatGrowth.readList 14 461 ridgeSupport7_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
