module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public meta import CertificateNumbers
public import RootedSixExtra00GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport262_000 : List Nat := [3,37,40,42,44,143,144,146,151,153,167,168,170,175,177,190,193,195,198,200,635,637,640,641,643,659,661,664,665,667,684,686]
def ridgeSupport262_001 : List Nat := [687,690,692,695,696,698,699,702,703,704,706,707,709,714,715,737,739,740,742,743,745,747,748,750,751,754,755,758,760,761,763,764]
def ridgeSupport262_002 : List Nat := [766,768,769,771,772,775,776,2346,2347,2352,2353,2356,2357,2358,2359,2360,2361,2366,2367,2370,2371,2376,2377,2380,2381,2382,2383,2384,2385,2390,2391,2404]
def ridgeSupport262_003 : List Nat := [2405,2406,2407,2408,2409,2428,2429,2430,2431,2432,2433,2452,2453,2454,2455,2456,2457,2476,2477,2478,2479,2480,2481,2500,2501,2502,2503,2504,2505,2524,2525,2526]
def ridgeSupport262_004 : List Nat := [2527,2528,2529,2537,2540,2543,2546,2548,2549,2550,2551,2552,2553,2554,2556,2606,2607,2618,2619,2620,2622,2626,2628,2642,2643,2654,2655,2748,2749,2760,2761,2765]
def ridgeSupport262_005 : List Nat := [2768,2771,2774,2784,2785,2796,2797,2820,2821,2832,2833,2837,2840,2843,2846,2856,2857,2868,2869,4652,4653,4664,4665,4688,4689,4700,4701,4708,4710,4714,4716,4794]
def ridgeSupport262_006 : List Nat := [4795,4806,4807,4830,4831,4842,4843,4853,4856,4859,4862,4866,4867,4878,4879,4902,4903,4914,4915,4925,4928,4931,4934,7132,7133,7134,7135,7136,7137,7780,7781,7782]
def ridgeSupport262_007 : List Nat := [7783,7784,7785,7793,7796,7799,7801,7802,7803,7805,7808,7811,7813,7814,7815,7820,7821,7826,7827,7854,7855,7860,7861,7872,7873,7878,7879,8278,8280,8284,8286,8315]
cert_ridgeSupport_7 262 008 8318 8321 8324 8333 8336 8339 8342
cert_ridgeSupport_code_3 262
cert_ridgeSupport_rest_2 262 000 0
cert_ridgeSupport_rest_2 262 001 448
cert_ridgeSupport_rest_2 262 002 896
cert_ridgeSupport_rest_2 262 003 1344
cert_ridgeSupport_rest_2 262 004 1792
cert_ridgeSupport_rest_2 262 005 2240
cert_ridgeSupport_rest_2 262 006 2688
cert_ridgeSupport_rest_2 262 007 3136
cert_ridgeSupport_rest_2 262 008 3584
cert_ridgeSupport_rest_2 262 009 3682
cert_ridgeSupport_suffix_4 262 009
cert_ridgeSupport_suffix_3 262 008 009
cert_ridgeSupport_suffix_3 262 007 008
cert_ridgeSupport_suffix_3 262 006 007
cert_ridgeSupport_suffix_3 262 005 006
cert_ridgeSupport_suffix_3 262 004 005
cert_ridgeSupport_suffix_3 262 003 004
cert_ridgeSupport_suffix_3 262 002 003
cert_ridgeSupport_suffix_3 262 001 002
cert_ridgeSupport_suffix_3 262 000 001
cert_ridgeSupport_source_3 262 14 263
end Papers.RationalityTen.RootedCaches.RootedSixExtra00
