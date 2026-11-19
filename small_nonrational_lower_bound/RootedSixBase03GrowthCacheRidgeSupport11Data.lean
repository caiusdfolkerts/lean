module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public meta import CertificateNumbers
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
cert_ridgeSupport_code_2 11
cert_ridgeSupport_rest 11 000 0
cert_ridgeSupport_rest 11 001 416
cert_ridgeSupport_rest 11 002 832
cert_ridgeSupport_rest 11 003 1248
cert_ridgeSupport_rest 11 004 1664
cert_ridgeSupport_rest 11 005 2080
cert_ridgeSupport_rest 11 006 2496
cert_ridgeSupport_rest 11 007 2912
cert_ridgeSupport_rest 11 008 3328
cert_ridgeSupport_rest 11 009 3744
cert_ridgeSupport_rest 11 010 4160
cert_ridgeSupport_rest 11 011 4433
cert_ridgeSupport_suffix_2 11 011
cert_ridgeSupport_suffix 11 010 011
cert_ridgeSupport_suffix 11 009 010
cert_ridgeSupport_suffix 11 008 009
cert_ridgeSupport_suffix 11 007 008
cert_ridgeSupport_suffix 11 006 007
cert_ridgeSupport_suffix 11 005 006
cert_ridgeSupport_suffix 11 004 005
cert_ridgeSupport_suffix 11 003 004
cert_ridgeSupport_suffix 11 002 003
cert_ridgeSupport_suffix 11 001 002
cert_ridgeSupport_suffix 11 000 001
cert_ridgeSupport_source 11 13 341
end Papers.RationalityTen.RootedCaches.RootedSixBase03
