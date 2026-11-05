module
prelude
public import RootedSixExtra01GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def kindSupport10_000 : List Nat := [2190,2191,2192,2193,2194,2195,2196,2197,2198,2199,2200,2201,2202,2203,2204,2205,2206,2207,2208,2209,2210,2211,2212,2213,2214,2215,2216,2217,2218,2219,2220,2221]
def kindSupport10_001 : List Nat := [2222,2223,2224,2225,2226,2227,2228,2229,2230,2231,2232,2233,2234,2235,2236,2237,2238,2239,2240,2241,2242,2243,2244,2245,2246,2247,2248,2249,2250,2251,2252,2253]
def kindSupport10_002 : List Nat := [2254,2255,2256,2257,2258,2259,2260,2261,2262,2263,2264,2265,2266,2267,2268,2269,2270,2271,2272,2273,2274,2275,2276,2277,2278,2279,2280,2281,2282,2283,2284,2285]
def kindSupport10_003 : List Nat := [2286,2287,2288,2289,2290,2291,2292,2293,2294,2295,2296,2297,2298,2299,2300,2301,2302,2303,2304,2305,2306,2307,2308,2309,2310,2311,2312,2313,2314,2315,2316,2317]
def kindSupport10_004 : List Nat := [2318,2319,2320,2321,2322,2323,2324,2325,2326,2327,2328,2329,2330,2331,2332,2333,2334,2335,2336,2337,2338,2339,2340,2341,2342,2343,2344,2345,2346,2347,2348,2349]
def kindSupport10_005 : List Nat := [2350,2351,2352,2353,2354,2355,2356,2357,2358,2359,2360,2361,2362,2363,2364,2365,2366,2367,2368,2369,2370,2371,2372,2373,2374,2375,2376,2377,2378,2379,2380,2381]
def kindSupport10_006 : List Nat := [2382,2383,2384,2385,2386,2387,2388,2389,2390,2391,2392,2393,2394,2395,2396,2397,2398,2399,2400,2401,2402,2403,2404,2405,2406,2407,2408,2409,2410,2411,2412,2413]
def kindSupport10_007 : List Nat := [2414,2415,2416,2417,2418,2419,2420,2421,2422,2423,2424,2425,2426,2427,2428,2429,2430,2431,2432,2433,2434,2435,2436,2437,2438,2439,2440,2441,2442,2443,2444,2445]
def kindSupport10_008 : List Nat := [2446,2447,2448,2449,2450,2451,2452,2453,2454,2455,2456,2457,2458,2459,2460,2461,2462,2463,2464,2465,2466,2467,2468,2469,2470,2471,2472,2473,2474,2475,2476,2477]
def kindSupport10_009 : List Nat := [2478,2479,2480,2481,2482,2483,2484,2485,2486,2487,2488,2489,2490,2491,2492,2493,2494,2495,2496,2497,2498,2499,2500,2501,2502,2503,2504,2505,2506,2507,2508,2509]
def kindSupport10_010 : List Nat := [2510,2511,2512,2513,2514,2515,2516,2517,2518,2519,2520,2521,2522,2523,2524,2525,2526,2527,2528,2529,2530,2531,2532,2533,2534,2535,2536,2537,2538,2539,2540,2541]
def kindSupport10_011 : List Nat := [2542,2543,2544,2545,2546,2547,2548,2549,2550,2551,2552,2553,2554,2555,2556,2557,2558,2559,2560,2561,2562,2563,2564,2565,2566,2567,2568,2569,2570,2571,2572,2573]
def kindSupport10_012 : List Nat := [2574,2575,2576,2577,2578,2579,2580,2581,2582,2583,2584,2585,2586,2587,2588,2589,2590,2591,2592,2593,2594,2595,2596,2597,2598,2599,2600,2601,2602,2603,2604,2605]
def kindSupport10_013 : List Nat := [2606,2607,2608,2609,2610,2611,2612,2613,2614,2615,2616,2617,2618,2619,2620,2621,2622,2623,2624,2625,2626,2627,2628,2629,2630,2631,2632,2633,2634,2635,2636,2637]
def kindSupport10_014 : List Nat := [2638,2639,2640,2641,2642,2643,2644,2645,2646,2647,2648,2649,2650,2651,2652,2653,2654,2655,2656,2657,2658,2659,2660,2661,2662,2663,2664,2665,2666,2667,2668,2669]
def kindSupport10_015 : List Nat := [2670,2671,2672,2673,2674,2675,2676,2677,2678,2679,2680,2681,2682,2683,2684,2685,2686,2687,2688,2689,2690,2691,2692,2693,2694,2695,2696,2697,2698,2699,2700,2701]
def kindSupport10_016 : List Nat := [2702,2703,2704,2705,2706,2707,2708,2709,2710,2711,2712,2713,2714,2715,2716,2717,2718,2719,2720,2721,2722,2723,2724,2725,2726,2727,2728,2729,2730,2731,2732,2733]
def kindSupport10_017 : List Nat := [2734,2735,2736,2737,2738,2739,2740,2741,2742,2743,2744,2745,2746,2747,2748,2749,2750,2751,2752,2753,2754,2755,2756,2757,2758,2759,2760,2761,2762,2763,2764,2765]
def kindSupport10_018 : List Nat := [2766,2767,2768,2769,2770,2771,2772,2773,2774,2775,2776,2777,2778,2779,2780,2781,2782,2783,2784,2785,2786,2787,2788,2789,2790,2791,2792,2793,2794,2795,2796,2797]
def kindSupport10_019 : List Nat := [2798,2799,2800,2801,2802,2803,2804,2805,2806,2807,2808,2809,2810,2811,2812,2813,2814,2815,2816,2817,2818,2819,2820,2821,2822,2823,2824,2825,2826,2827,2828,2829]
def kindSupport10_020 : List Nat := [2830,2831,2832,2833,2834,2835,2836,2837,2838,2839,2840,2841,2842,2843,2844,2845,2846,2847,2848,2849,2850,2851,2852,2853,2854,2855,2856,2857,2858,2859,2860,2861]
def kindSupport10_021 : List Nat := [2862,2863,2864,2865,2866,2867,2868,2869,2870,2871,2872,2873,2874,2875,2876,2877,2878,2879,2880,2881,2882,2883,2884,2885,2886,2887,2888,2889,2890,2891,2892,2893]
def kindSupport10_022 : List Nat := [2894,2895,2896,2897,2898,2899,2900,2901,2902,2903,2904,2905,2906,2907,2908,2909,2910,2911,2912,2913,2914,2915,2916,2917,2918,2919,2920,2921,2922,2923,2924,2925]
def kindSupport10_023 : List Nat := [2926,2927,2928,2929,2930,2931,2932,2933,2934,2935,2936,2937,2938,2939,2940,2941,2942,2943,2944,2945,2946,2947,2948,2949,2950,2951,2952,2953,2954,2955,2956,2957]
def kindSupport10_024 : List Nat := [2958,2959,2960,2961,2962,2963,2964,2965,2966,2967,2968,2969,2970,2971,2972,2973,2974,2975,2976,2977,2978,2979,2980,2981,2982,2983,2984,2985,2986,2987,2988,2989]
def kindSupport10_025 : List Nat := [2990,2991,2992,2993,2994,2995,2996,2997,2998,2999,3000,3001,3002,3003,3004,3005,3006,3007,3008,3009,3010,3011,3012,3013,3014,3015,3016,3017,3018,3019,3020,3021]
def kindSupport10_026 : List Nat := [3022,3023,3024,3025,3026,3027,3028,3029,3030,3031,3032,3033,3034,3035,3036,3037,3038,3039,3040,3041,3042,3043,3044,3045,3046,3047,3048,3049,3050,3051,3052,3053]
def kindSupport10_027 : List Nat := [3054,3055,3056,3057,3058,3059,3060,3061,3062,3063,3064,3065,3066,3067,3068,3069,3070,3071,3072,3073,3074,3075,3076,3077,3078,3079,3080,3081,3082,3083,3084,3085]
def kindSupport10_028 : List Nat := [3086,3087,3088,3089,3090,3091,3092,3093,3094,3095,3096,3097,3098,3099,3100,3101,3102,3103,3104,3105,3106,3107,3108,3109,3110,3111,3112,3113,3114,3115,3116,3117]
def kindSupport10_029 : List Nat := [3118,3119,3120,3121,3122,3123,3124,3125,3126,3127,3128,3129,3130,3131,3132,3133,3134,3135,3136,3137,3138,3139,3140,3141,3142,3143,3144,3145,3146,3147,3148,3149]
def kindSupport10_code : Nat := 0xc4dc4cc4bc4ac49c48c47c46c45c44c43c42c41c40c3fc3ec3dc3cc3bc3ac39c38c37c36c35c34c33c32c31c30c2fc2ec2dc2cc2bc2ac29c28c27c26c25c24c23c22c21c20c1fc1ec1dc1cc1bc1ac19c18c17c16c15c14c13c12c11c10c0fc0ec0dc0cc0bc0ac09c08c07c06c05c04c03c02c01c00bffbfebfdbfcbfbbfabf9bf8bf7bf6bf5bf4bf3bf2bf1bf0befbeebedbecbebbeabe9be8be7be6be5be4be3be2be1be0bdfbdebddbdcbdbbdabd9bd8bd7bd6bd5bd4bd3bd2bd1bd0bcfbcebcdbccbcbbcabc9bc8bc7bc6bc5bc4bc3bc2bc1bc0bbfbbebbdbbcbbbbbabb9bb8bb7bb6bb5bb4bb3bb2bb1bb0bafbaebadbacbabbaaba9ba8ba7ba6ba5ba4ba3ba2ba1ba0b9fb9eb9db9cb9bb9ab99b98b97b96b95b94b93b92b91b90b8fb8eb8db8cb8bb8ab89b88b87b86b85b84b83b82b81b80b7fb7eb7db7cb7bb7ab79b78b77b76b75b74b73b72b71b70b6fb6eb6db6cb6bb6ab69b68b67b66b65b64b63b62b61b60b5fb5eb5db5cb5bb5ab59b58b57b56b55b54b53b52b51b50b4fb4eb4db4cb4bb4ab49b48b47b46b45b44b43b42b41b40b3fb3eb3db3cb3bb3ab39b38b37b36b35b34b33b32b31b30b2fb2eb2db2cb2bb2ab29b28b27b26b25b24b23b22b21b20b1fb1eb1db1cb1bb1ab19b18b17b16b15b14b13b12b11b10b0fb0eb0db0cb0bb0ab09b08b07b06b05b04b03b02b01b00affafeafdafcafbafaaf9af8af7af6af5af4af3af2af1af0aefaeeaedaecaebaeaae9ae8ae7ae6ae5ae4ae3ae2ae1ae0adfadeaddadcadbadaad9ad8ad7ad6ad5ad4ad3ad2ad1ad0acfaceacdaccacbacaac9ac8ac7ac6ac5ac4ac3ac2ac1ac0abfabeabdabcabbabaab9ab8ab7ab6ab5ab4ab3ab2ab1ab0aafaaeaadaacaabaaaaa9aa8aa7aa6aa5aa4aa3aa2aa1aa0a9fa9ea9da9ca9ba9aa99a98a97a96a95a94a93a92a91a90a8fa8ea8da8ca8ba8aa89a88a87a86a85a84a83a82a81a80a7fa7ea7da7ca7ba7aa79a78a77a76a75a74a73a72a71a70a6fa6ea6da6ca6ba6aa69a68a67a66a65a64a63a62a61a60a5fa5ea5da5ca5ba5aa59a58a57a56a55a54a53a52a51a50a4fa4ea4da4ca4ba4aa49a48a47a46a45a44a43a42a41a40a3fa3ea3da3ca3ba3aa39a38a37a36a35a34a33a32a31a30a2fa2ea2da2ca2ba2aa29a28a27a26a25a24a23a22a21a20a1fa1ea1da1ca1ba1aa19a18a17a16a15a14a13a12a11a10a0fa0ea0da0ca0ba0aa09a08a07a06a05a04a03a02a01a009ff9fe9fd9fc9fb9fa9f99f89f79f69f59f49f39f29f19f09ef9ee9ed9ec9eb9ea9e99e89e79e69e59e49e39e29e19e09df9de9dd9dc9db9da9d99d89d79d69d59d49d39d29d19d09cf9ce9cd9cc9cb9ca9c99c89c79c69c59c49c39c29c19c09bf9be9bd9bc9bb9ba9b99b89b79b69b59b49b39b29b19b09af9ae9ad9ac9ab9aa9a99a89a79a69a59a49a39a29a19a099f99e99d99c99b99a99999899799699599499399299199098f98e98d98c98b98a98998898798698598498398298198097f97e97d97c97b97a97997897797697597497397297197096f96e96d96c96b96a96996896796696596496396296196095f95e95d95c95b95a95995895795695595495395295195094f94e94d94c94b94a94994894794694594494394294194093f93e93d93c93b93a93993893793693593493393293193092f92e92d92c92b92a92992892792692592492392292192091f91e91d91c91b91a91991891791691591491391291191090f90e90d90c90b90a9099089079069059049039029019008ff8fe8fd8fc8fb8fa8f98f88f78f68f58f48f38f28f18f08ef8ee8ed8ec8eb8ea8e98e88e78e68e58e48e38e28e18e08df8de8dd8dc8db8da8d98d88d78d68d58d48d38d28d18d08cf8ce8cd8cc8cb8ca8c98c88c78c68c58c48c38c28c18c08bf8be8bd8bc8bb8ba8b98b88b78b68b58b48b38b28b18b08af8ae8ad8ac8ab8aa8a98a88a78a68a58a48a38a28a18a089f89e89d89c89b89a89989889789689589489389289189088f88e
def kindSupport10_rest_000 : Nat := PackedRawNatGrowth.drop 0 kindSupport10_code
def kindSupport10_rest_001 : Nat := PackedRawNatGrowth.drop 384 kindSupport10_code
def kindSupport10_rest_002 : Nat := PackedRawNatGrowth.drop 768 kindSupport10_code
def kindSupport10_rest_003 : Nat := PackedRawNatGrowth.drop 1152 kindSupport10_code
def kindSupport10_rest_004 : Nat := PackedRawNatGrowth.drop 1536 kindSupport10_code
def kindSupport10_rest_005 : Nat := PackedRawNatGrowth.drop 1920 kindSupport10_code
def kindSupport10_rest_006 : Nat := PackedRawNatGrowth.drop 2304 kindSupport10_code
def kindSupport10_rest_007 : Nat := PackedRawNatGrowth.drop 2688 kindSupport10_code
def kindSupport10_rest_008 : Nat := PackedRawNatGrowth.drop 3072 kindSupport10_code
def kindSupport10_rest_009 : Nat := PackedRawNatGrowth.drop 3456 kindSupport10_code
def kindSupport10_rest_010 : Nat := PackedRawNatGrowth.drop 3840 kindSupport10_code
def kindSupport10_rest_011 : Nat := PackedRawNatGrowth.drop 4224 kindSupport10_code
def kindSupport10_rest_012 : Nat := PackedRawNatGrowth.drop 4608 kindSupport10_code
def kindSupport10_rest_013 : Nat := PackedRawNatGrowth.drop 4992 kindSupport10_code
def kindSupport10_rest_014 : Nat := PackedRawNatGrowth.drop 5376 kindSupport10_code
def kindSupport10_rest_015 : Nat := PackedRawNatGrowth.drop 5760 kindSupport10_code
def kindSupport10_rest_016 : Nat := PackedRawNatGrowth.drop 6144 kindSupport10_code
def kindSupport10_rest_017 : Nat := PackedRawNatGrowth.drop 6528 kindSupport10_code
def kindSupport10_rest_018 : Nat := PackedRawNatGrowth.drop 6912 kindSupport10_code
def kindSupport10_rest_019 : Nat := PackedRawNatGrowth.drop 7296 kindSupport10_code
def kindSupport10_rest_020 : Nat := PackedRawNatGrowth.drop 7680 kindSupport10_code
def kindSupport10_rest_021 : Nat := PackedRawNatGrowth.drop 8064 kindSupport10_code
def kindSupport10_rest_022 : Nat := PackedRawNatGrowth.drop 8448 kindSupport10_code
def kindSupport10_rest_023 : Nat := PackedRawNatGrowth.drop 8832 kindSupport10_code
def kindSupport10_rest_024 : Nat := PackedRawNatGrowth.drop 9216 kindSupport10_code
def kindSupport10_rest_025 : Nat := PackedRawNatGrowth.drop 9600 kindSupport10_code
def kindSupport10_rest_026 : Nat := PackedRawNatGrowth.drop 9984 kindSupport10_code
def kindSupport10_rest_027 : Nat := PackedRawNatGrowth.drop 10368 kindSupport10_code
def kindSupport10_rest_028 : Nat := PackedRawNatGrowth.drop 10752 kindSupport10_code
def kindSupport10_rest_029 : Nat := PackedRawNatGrowth.drop 11136 kindSupport10_code
def kindSupport10_rest_030 : Nat := PackedRawNatGrowth.drop 11520 kindSupport10_code
def kindSupport10_suffix_030 : List Nat := []
def kindSupport10_suffix_029 : List Nat := kindSupport10_029 ++ kindSupport10_suffix_030
def kindSupport10_suffix_028 : List Nat := kindSupport10_028 ++ kindSupport10_suffix_029
def kindSupport10_suffix_027 : List Nat := kindSupport10_027 ++ kindSupport10_suffix_028
def kindSupport10_suffix_026 : List Nat := kindSupport10_026 ++ kindSupport10_suffix_027
def kindSupport10_suffix_025 : List Nat := kindSupport10_025 ++ kindSupport10_suffix_026
def kindSupport10_suffix_024 : List Nat := kindSupport10_024 ++ kindSupport10_suffix_025
def kindSupport10_suffix_023 : List Nat := kindSupport10_023 ++ kindSupport10_suffix_024
def kindSupport10_suffix_022 : List Nat := kindSupport10_022 ++ kindSupport10_suffix_023
def kindSupport10_suffix_021 : List Nat := kindSupport10_021 ++ kindSupport10_suffix_022
def kindSupport10_suffix_020 : List Nat := kindSupport10_020 ++ kindSupport10_suffix_021
def kindSupport10_suffix_019 : List Nat := kindSupport10_019 ++ kindSupport10_suffix_020
def kindSupport10_suffix_018 : List Nat := kindSupport10_018 ++ kindSupport10_suffix_019
def kindSupport10_suffix_017 : List Nat := kindSupport10_017 ++ kindSupport10_suffix_018
def kindSupport10_suffix_016 : List Nat := kindSupport10_016 ++ kindSupport10_suffix_017
def kindSupport10_suffix_015 : List Nat := kindSupport10_015 ++ kindSupport10_suffix_016
def kindSupport10_suffix_014 : List Nat := kindSupport10_014 ++ kindSupport10_suffix_015
def kindSupport10_suffix_013 : List Nat := kindSupport10_013 ++ kindSupport10_suffix_014
def kindSupport10_suffix_012 : List Nat := kindSupport10_012 ++ kindSupport10_suffix_013
def kindSupport10_suffix_011 : List Nat := kindSupport10_011 ++ kindSupport10_suffix_012
def kindSupport10_suffix_010 : List Nat := kindSupport10_010 ++ kindSupport10_suffix_011
def kindSupport10_suffix_009 : List Nat := kindSupport10_009 ++ kindSupport10_suffix_010
def kindSupport10_suffix_008 : List Nat := kindSupport10_008 ++ kindSupport10_suffix_009
def kindSupport10_suffix_007 : List Nat := kindSupport10_007 ++ kindSupport10_suffix_008
def kindSupport10_suffix_006 : List Nat := kindSupport10_006 ++ kindSupport10_suffix_007
def kindSupport10_suffix_005 : List Nat := kindSupport10_005 ++ kindSupport10_suffix_006
def kindSupport10_suffix_004 : List Nat := kindSupport10_004 ++ kindSupport10_suffix_005
def kindSupport10_suffix_003 : List Nat := kindSupport10_003 ++ kindSupport10_suffix_004
def kindSupport10_suffix_002 : List Nat := kindSupport10_002 ++ kindSupport10_suffix_003
def kindSupport10_suffix_001 : List Nat := kindSupport10_001 ++ kindSupport10_suffix_002
def kindSupport10_suffix_000 : List Nat := kindSupport10_000 ++ kindSupport10_suffix_001
theorem kindSupport10_source : kindSupports 10 =
    (PackedRawNatGrowth.readList 12 960 kindSupport10_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra01
