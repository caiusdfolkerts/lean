module
prelude
public import RootedSixBase03GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport11_000 : List Nat := [0,5,6,7,8,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214]
def ridgeSupport11_001 : List Nat := [215,216,217,218,219,220,221,222,223,224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246]
def ridgeSupport11_002 : List Nat := [247,248,249,250,251,252,253,254,255,256,257,258,259,2502,2503,2504,2505,2506,2507,2508,2509,2510,2511,2512,2513,2514,2515,2516,2517,2518,2519,2520]
def ridgeSupport11_003 : List Nat := [2521,2522,2523,2524,2525,2526,2527,2528,2529,2530,2531,2532,2533,2534,2535,2536,2537,2538,2539,2540,2541,2542,2543,2544,2545,2546,2547,2548,2549,2550,2551,2552]
def ridgeSupport11_004 : List Nat := [2553,2554,2555,2556,2557,2558,2559,2560,2561,2562,2563,2564,2565,2566,2567,2568,2569,2570,2571,2572,2573,2574,2575,2576,2577,2578,2579,2580,2581,2582,2583,2584]
def ridgeSupport11_005 : List Nat := [2585,2586,2587,2588,2589,2590,2591,2592,2593,2594,2595,2596,2597,2598,2599,2600,2601,2602,2603,2604,2605,2606,2607,2608,2609,2610,2611,2612,2613,2614,2615,2616]
def ridgeSupport11_006 : List Nat := [2617,2618,2619,2620,2621,2622,2623,2624,2625,2626,2627,2628,2629,2630,2631,2632,2633,2634,2635,2636,2637,2638,2639,2640,2641,2642,2643,2644,2645,2646,2647,2648]
def ridgeSupport11_007 : List Nat := [2649,2650,2651,2652,2653,2654,2655,2656,2657,2658,2659,2660,2661,2662,2663,2664,2665,2666,2667,2668,2669,2670,2671,2672,2673,2674,2675,2676,2677,2678,2679,2680]
def ridgeSupport11_008 : List Nat := [2681,2682,2683,2684,2685,2686,2687,2688,2689,2690,2691,2692,2693,2694,2695,2696,2697,2698,2699,2700,2701,2702,2703,2704,2705,2706,2707,2708,2709,2710,2711,2712]
def ridgeSupport11_009 : List Nat := [2713,2714,2715,2716,2717,4482,4483,4484,4485,4486,4487,4488,4489,4490,4491,4492,4493,4494,4495,4496,4497,4498,4499,4500,4501,4502,4503,4504,4505,4878,4879,4880]
def ridgeSupport11_010 : List Nat := [4881,4882,4883,4884,4885,4886,4887,4888,4889,4890,4891,4892,4893,4894,4895,4896,4897,4898,4899,4900,4901]
def ridgeSupport11_code : Nat := 0x13259924c8e6453219904c7e63d31d98e4c6e63531998c4c5e62d31598a4c4e6253119884c3e61d1998cc465e32d1958ca464e3251918c8463e31d18d8c6462e3151898c4461e30d1858c2460e304a9d54e2a6d534a9954c2a5d52ca9554a2a4d524a915482a3d51ca8d5462a2d514a895442a1d50ca855422a0d504a8154029fd4fca7d53e29ed4f4a7953c29dd4eca7553a29cd4e4a7153829bd4dca6d53629ad4d4a69534299d4cca65532298d4c4a61530297d4bca5d52e296d4b4a5952c295d4aca5552a294d4a4a51528293d49ca4d526292d494a49524291d48ca45522290d484a4152028fd47ca3d51e28ed474a3951c28dd46ca3551a28cd464a3151828bd45ca2d51628ad454a29514289d44ca25512288d444a21510287d43ca1d50e286d434a1950c285d42ca1550a284d424a11508283d41ca0d506282d414a09504281d40ca05502280d404a0150027fd3fc9fd4fe27ed3f49f94fc27dd3ec9f54fa27cd3e49f14f827bd3dc9ed4f627ad3d49e94f4279d3cc9e54f2278d3c49e14f0277d3bc9dd4ee276d3b49d94ec275d3ac9d54ea274d3a49d14e8273d39c9cd4e6272d3949c94e4271d38c10308104042000ff07f03f41f80fb07d03e41f00f707b03d41e80f307903c41e00ef07703b41d80eb07503a41d00e707303941c80e307103841c00df06f03741b80db06d03641b00d706b03541a80d306903441a00cf06703341980cb06503241900c706303141880c306103041800bf05f02f4178008003801800a000
def ridgeSupport11_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport11_code
def ridgeSupport11_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport11_code
def ridgeSupport11_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport11_code
def ridgeSupport11_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport11_code
def ridgeSupport11_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport11_code
def ridgeSupport11_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport11_code
def ridgeSupport11_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport11_code
def ridgeSupport11_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport11_code
def ridgeSupport11_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport11_code
def ridgeSupport11_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport11_code
def ridgeSupport11_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport11_code
def ridgeSupport11_rest_011 : Nat := PackedRawNatGrowth.drop 4433 ridgeSupport11_code
def ridgeSupport11_suffix_011 : List Nat := []
def ridgeSupport11_suffix_010 : List Nat := ridgeSupport11_010 ++ ridgeSupport11_suffix_011
def ridgeSupport11_suffix_009 : List Nat := ridgeSupport11_009 ++ ridgeSupport11_suffix_010
def ridgeSupport11_suffix_008 : List Nat := ridgeSupport11_008 ++ ridgeSupport11_suffix_009
def ridgeSupport11_suffix_007 : List Nat := ridgeSupport11_007 ++ ridgeSupport11_suffix_008
def ridgeSupport11_suffix_006 : List Nat := ridgeSupport11_006 ++ ridgeSupport11_suffix_007
def ridgeSupport11_suffix_005 : List Nat := ridgeSupport11_005 ++ ridgeSupport11_suffix_006
def ridgeSupport11_suffix_004 : List Nat := ridgeSupport11_004 ++ ridgeSupport11_suffix_005
def ridgeSupport11_suffix_003 : List Nat := ridgeSupport11_003 ++ ridgeSupport11_suffix_004
def ridgeSupport11_suffix_002 : List Nat := ridgeSupport11_002 ++ ridgeSupport11_suffix_003
def ridgeSupport11_suffix_001 : List Nat := ridgeSupport11_001 ++ ridgeSupport11_suffix_002
def ridgeSupport11_suffix_000 : List Nat := ridgeSupport11_000 ++ ridgeSupport11_suffix_001
theorem ridgeSupport11_source : candidateSupports 11 =
    (PackedRawNatGrowth.readList 13 341 ridgeSupport11_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase03
