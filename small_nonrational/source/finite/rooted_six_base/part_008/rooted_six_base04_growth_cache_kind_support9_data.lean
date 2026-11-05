module
prelude
public import RootedSixBase04GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase04
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def kindSupport9_000 : List Nat := [2200,2201,2202,2203,2204,2205,2206,2207,2208,2209,2210,2211,2212,2213,2214,2215,2216,2217,2218,2219,2220,2221,2222,2223,2224,2225,2226,2227,2228,2229,2230,2231]
def kindSupport9_001 : List Nat := [2232,2233,2234,2235,2236,2237,2238,2239,2240,2241,2242,2243,2244,2245,2246,2247,2248,2249,2250,2251,2252,2253,2254,2255,2256,2257,2258,2259,2260,2261,2262,2263]
def kindSupport9_002 : List Nat := [2264,2265,2266,2267,2268,2269,2270,2271,2272,2273,2274,2275,2276,2277,2278,2279,2280,2281,2282,2283,2284,2285,2286,2287,2288,2289,2290,2291,2292,2293,2294,2295]
def kindSupport9_003 : List Nat := [2296,2297,2298,2299,2300,2301,2302,2303,2304,2305,2306,2307,2308,2309,2310,2311,2312,2313,2314,2315,2316,2317,2318,2319,2320,2321,2322,2323,2324,2325,2326,2327]
def kindSupport9_004 : List Nat := [2328,2329,2330,2331,2332,2333,2334,2335,2336,2337,2338,2339,2340,2341,2342,2343,2344,2345,2346,2347,2348,2349,2350,2351,2352,2353,2354,2355,2356,2357,2358,2359]
def kindSupport9_005 : List Nat := [2360,2361,2362,2363,2364,2365,2366,2367,2368,2369,2370,2371,2372,2373,2374,2375,2376,2377,2378,2379,2380,2381,2382,2383,2384,2385,2386,2387,2388,2389,2390,2391]
def kindSupport9_006 : List Nat := [2392,2393,2394,2395,2396,2397,2398,2399,2400,2401,2402,2403,2404,2405,2406,2407,2408,2409,2410,2411,2412,2413,2414,2415,2416,2417,2418,2419,2420,2421,2422,2423]
def kindSupport9_007 : List Nat := [2424,2425,2426,2427,2428,2429,2430,2431,2432,2433,2434,2435,2436,2437,2438,2439,2440,2441,2442,2443,2444,2445,2446,2447,2448,2449,2450,2451,2452,2453,2454,2455]
def kindSupport9_008 : List Nat := [2456,2457,2458,2459,2460,2461,2462,2463,2464,2465,2466,2467,2468,2469,2470,2471,2472,2473,2474,2475,2476,2477,2478,2479,2480,2481,2482,2483,2484,2485,2486,2487]
def kindSupport9_009 : List Nat := [2488,2489,2490,2491,2492,2493,2494,2495,2496,2497,2498,2499,2500,2501,2502,2503,2504,2505,2506,2507,2508,2509,2510,2511,2512,2513,2514,2515,2516,2517,2518,2519]
def kindSupport9_010 : List Nat := [2520,2521,2522,2523,2524,2525,2526,2527,2528,2529,2530,2531,2532,2533,2534,2535,2536,2537,2538,2539,2540,2541,2542,2543,2544,2545,2546,2547,2548,2549,2550,2551]
def kindSupport9_011 : List Nat := [2552,2553,2554,2555,2556,2557,2558,2559,2560,2561,2562,2563,2564,2565,2566,2567,2568,2569,2570,2571,2572,2573,2574,2575,2576,2577,2578,2579,2580,2581,2582,2583]
def kindSupport9_012 : List Nat := [2584,2585,2586,2587,2588,2589,2590,2591,2592,2593,2594,2595,2596,2597,2598,2599,2600,2601,2602,2603,2604,2605,2606,2607,2608,2609,2610,2611,2612,2613,2614,2615]
def kindSupport9_013 : List Nat := [2616,2617,2618,2619,2620,2621,2622,2623,2624,2625,2626,2627,2628,2629,2630,2631,2632,2633,2634,2635,2636,2637,2638,2639,2640,2641,2642,2643,2644,2645,2646,2647]
def kindSupport9_014 : List Nat := [2648,2649,2650,2651,2652,2653,2654,2655,2656,2657,2658,2659,2660,2661,2662,2663,2664,2665,2666,2667,2668,2669,2670,2671,2672,2673,2674,2675,2676,2677,2678,2679]
def kindSupport9_015 : List Nat := [2680,2681,2682,2683,2684,2685,2686,2687,2688,2689,2690,2691,2692,2693,2694,2695,2696,2697,2698,2699,2700,2701,2702,2703,2704,2705,2706,2707,2708,2709,2710,2711]
def kindSupport9_016 : List Nat := [2712,2713,2714,2715,2716,2717,2718,2719,2720,2721,2722,2723,2724,2725,2726,2727,2728,2729,2730,2731,2732,2733,2734,2735,2736,2737,2738,2739,2740,2741,2742,2743]
def kindSupport9_017 : List Nat := [2744,2745,2746,2747,2748,2749,2750,2751,2752,2753,2754,2755,2756,2757,2758,2759,2760,2761,2762,2763,2764,2765,2766,2767,2768,2769,2770,2771,2772,2773,2774,2775]
def kindSupport9_018 : List Nat := [2776,2777,2778,2779,2780,2781,2782,2783,2784,2785,2786,2787,2788,2789,2790,2791,2792,2793,2794,2795,2796,2797,2798,2799,2800,2801,2802,2803,2804,2805,2806,2807]
def kindSupport9_019 : List Nat := [2808,2809,2810,2811,2812,2813,2814,2815,2816,2817,2818,2819,2820,2821,2822,2823]
def kindSupport9_code : Nat := 0xb07b06b05b04b03b02b01b00affafeafdafcafbafaaf9af8af7af6af5af4af3af2af1af0aefaeeaedaecaebaeaae9ae8ae7ae6ae5ae4ae3ae2ae1ae0adfadeaddadcadbadaad9ad8ad7ad6ad5ad4ad3ad2ad1ad0acfaceacdaccacbacaac9ac8ac7ac6ac5ac4ac3ac2ac1ac0abfabeabdabcabbabaab9ab8ab7ab6ab5ab4ab3ab2ab1ab0aafaaeaadaacaabaaaaa9aa8aa7aa6aa5aa4aa3aa2aa1aa0a9fa9ea9da9ca9ba9aa99a98a97a96a95a94a93a92a91a90a8fa8ea8da8ca8ba8aa89a88a87a86a85a84a83a82a81a80a7fa7ea7da7ca7ba7aa79a78a77a76a75a74a73a72a71a70a6fa6ea6da6ca6ba6aa69a68a67a66a65a64a63a62a61a60a5fa5ea5da5ca5ba5aa59a58a57a56a55a54a53a52a51a50a4fa4ea4da4ca4ba4aa49a48a47a46a45a44a43a42a41a40a3fa3ea3da3ca3ba3aa39a38a37a36a35a34a33a32a31a30a2fa2ea2da2ca2ba2aa29a28a27a26a25a24a23a22a21a20a1fa1ea1da1ca1ba1aa19a18a17a16a15a14a13a12a11a10a0fa0ea0da0ca0ba0aa09a08a07a06a05a04a03a02a01a009ff9fe9fd9fc9fb9fa9f99f89f79f69f59f49f39f29f19f09ef9ee9ed9ec9eb9ea9e99e89e79e69e59e49e39e29e19e09df9de9dd9dc9db9da9d99d89d79d69d59d49d39d29d19d09cf9ce9cd9cc9cb9ca9c99c89c79c69c59c49c39c29c19c09bf9be9bd9bc9bb9ba9b99b89b79b69b59b49b39b29b19b09af9ae9ad9ac9ab9aa9a99a89a79a69a59a49a39a29a19a099f99e99d99c99b99a99999899799699599499399299199098f98e98d98c98b98a98998898798698598498398298198097f97e97d97c97b97a97997897797697597497397297197096f96e96d96c96b96a96996896796696596496396296196095f95e95d95c95b95a95995895795695595495395295195094f94e94d94c94b94a94994894794694594494394294194093f93e93d93c93b93a93993893793693593493393293193092f92e92d92c92b92a92992892792692592492392292192091f91e91d91c91b91a91991891791691591491391291191090f90e90d90c90b90a9099089079069059049039029019008ff8fe8fd8fc8fb8fa8f98f88f78f68f58f48f38f28f18f08ef8ee8ed8ec8eb8ea8e98e88e78e68e58e48e38e28e18e08df8de8dd8dc8db8da8d98d88d78d68d58d48d38d28d18d08cf8ce8cd8cc8cb8ca8c98c88c78c68c58c48c38c28c18c08bf8be8bd8bc8bb8ba8b98b88b78b68b58b48b38b28b18b08af8ae8ad8ac8ab8aa8a98a88a78a68a58a48a38a28a18a089f89e89d89c89b89a899898
def kindSupport9_rest_000 : Nat := PackedRawNatGrowth.drop 0 kindSupport9_code
def kindSupport9_rest_001 : Nat := PackedRawNatGrowth.drop 384 kindSupport9_code
def kindSupport9_rest_002 : Nat := PackedRawNatGrowth.drop 768 kindSupport9_code
def kindSupport9_rest_003 : Nat := PackedRawNatGrowth.drop 1152 kindSupport9_code
def kindSupport9_rest_004 : Nat := PackedRawNatGrowth.drop 1536 kindSupport9_code
def kindSupport9_rest_005 : Nat := PackedRawNatGrowth.drop 1920 kindSupport9_code
def kindSupport9_rest_006 : Nat := PackedRawNatGrowth.drop 2304 kindSupport9_code
def kindSupport9_rest_007 : Nat := PackedRawNatGrowth.drop 2688 kindSupport9_code
def kindSupport9_rest_008 : Nat := PackedRawNatGrowth.drop 3072 kindSupport9_code
def kindSupport9_rest_009 : Nat := PackedRawNatGrowth.drop 3456 kindSupport9_code
def kindSupport9_rest_010 : Nat := PackedRawNatGrowth.drop 3840 kindSupport9_code
def kindSupport9_rest_011 : Nat := PackedRawNatGrowth.drop 4224 kindSupport9_code
def kindSupport9_rest_012 : Nat := PackedRawNatGrowth.drop 4608 kindSupport9_code
def kindSupport9_rest_013 : Nat := PackedRawNatGrowth.drop 4992 kindSupport9_code
def kindSupport9_rest_014 : Nat := PackedRawNatGrowth.drop 5376 kindSupport9_code
def kindSupport9_rest_015 : Nat := PackedRawNatGrowth.drop 5760 kindSupport9_code
def kindSupport9_rest_016 : Nat := PackedRawNatGrowth.drop 6144 kindSupport9_code
def kindSupport9_rest_017 : Nat := PackedRawNatGrowth.drop 6528 kindSupport9_code
def kindSupport9_rest_018 : Nat := PackedRawNatGrowth.drop 6912 kindSupport9_code
def kindSupport9_rest_019 : Nat := PackedRawNatGrowth.drop 7296 kindSupport9_code
def kindSupport9_rest_020 : Nat := PackedRawNatGrowth.drop 7488 kindSupport9_code
def kindSupport9_suffix_020 : List Nat := []
def kindSupport9_suffix_019 : List Nat := kindSupport9_019 ++ kindSupport9_suffix_020
def kindSupport9_suffix_018 : List Nat := kindSupport9_018 ++ kindSupport9_suffix_019
def kindSupport9_suffix_017 : List Nat := kindSupport9_017 ++ kindSupport9_suffix_018
def kindSupport9_suffix_016 : List Nat := kindSupport9_016 ++ kindSupport9_suffix_017
def kindSupport9_suffix_015 : List Nat := kindSupport9_015 ++ kindSupport9_suffix_016
def kindSupport9_suffix_014 : List Nat := kindSupport9_014 ++ kindSupport9_suffix_015
def kindSupport9_suffix_013 : List Nat := kindSupport9_013 ++ kindSupport9_suffix_014
def kindSupport9_suffix_012 : List Nat := kindSupport9_012 ++ kindSupport9_suffix_013
def kindSupport9_suffix_011 : List Nat := kindSupport9_011 ++ kindSupport9_suffix_012
def kindSupport9_suffix_010 : List Nat := kindSupport9_010 ++ kindSupport9_suffix_011
def kindSupport9_suffix_009 : List Nat := kindSupport9_009 ++ kindSupport9_suffix_010
def kindSupport9_suffix_008 : List Nat := kindSupport9_008 ++ kindSupport9_suffix_009
def kindSupport9_suffix_007 : List Nat := kindSupport9_007 ++ kindSupport9_suffix_008
def kindSupport9_suffix_006 : List Nat := kindSupport9_006 ++ kindSupport9_suffix_007
def kindSupport9_suffix_005 : List Nat := kindSupport9_005 ++ kindSupport9_suffix_006
def kindSupport9_suffix_004 : List Nat := kindSupport9_004 ++ kindSupport9_suffix_005
def kindSupport9_suffix_003 : List Nat := kindSupport9_003 ++ kindSupport9_suffix_004
def kindSupport9_suffix_002 : List Nat := kindSupport9_002 ++ kindSupport9_suffix_003
def kindSupport9_suffix_001 : List Nat := kindSupport9_001 ++ kindSupport9_suffix_002
def kindSupport9_suffix_000 : List Nat := kindSupport9_000 ++ kindSupport9_suffix_001
theorem kindSupport9_source : kindSupports 9 =
    (PackedRawNatGrowth.readList 12 624 kindSupport9_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase04
