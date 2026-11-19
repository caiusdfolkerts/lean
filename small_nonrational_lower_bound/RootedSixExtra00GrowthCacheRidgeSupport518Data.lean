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
def ridgeSupport518_000 : List Nat := [4,38,41,43,44,155,156,158,163,165,179,180,182,187,189,191,192,194,199,201,647,649,652,653,655,671,673,676,677,679,683,685]
def ridgeSupport518_001 : List Nat := [688,689,691,716,717,719,720,723,724,725,727,728,730,735,736,737,738,740,741,744,745,746,748,749,751,756,757,758,759,761,762,765]
def ridgeSupport518_002 : List Nat := [766,767,769,770,772,777,778,2348,2349,2354,2355,2360,2361,2362,2363,2364,2365,2366,2367,2372,2373,2378,2379,2384,2385,2386,2387,2388,2389,2390,2391,2410]
def ridgeSupport518_003 : List Nat := [2411,2412,2413,2414,2415,2434,2435,2436,2437,2438,2439,2458,2459,2460,2461,2462,2463,2482,2483,2484,2485,2486,2487,2506,2507,2508,2509,2510,2511,2530,2531,2532]
def ridgeSupport518_004 : List Nat := [2533,2534,2535,2536,2538,2542,2544,2548,2550,2554,2555,2556,2557,2558,2559,2678,2679,2690,2691,2692,2694,2698,2700,2714,2715,2726,2727,2750,2751,2762,2763,2764]
def ridgeSupport518_005 : List Nat := [2766,2770,2772,2786,2787,2798,2799,2822,2823,2834,2835,2836,2838,2842,2844,2858,2859,2870,2871,4724,4725,4736,4737,4760,4761,4772,4773,4780,4782,4786,4788,4796]
def ridgeSupport518_006 : List Nat := [4797,4808,4809,4832,4833,4844,4845,4852,4854,4858,4860,4868,4869,4880,4881,4904,4905,4916,4917,4924,4926,4930,4932,7138,7139,7140,7141,7142,7143,7786,7787,7788]
def ridgeSupport518_007 : List Nat := [7789,7790,7791,7792,7794,7798,7800,7802,7803,7804,7806,7810,7812,7814,7815,7838,7839,7844,7845,7856,7857,7862,7863,7874,7875,7880,7881,8296,8298,8302,8304,8314]
cert_ridgeSupport_7 518 008 8316 8320 8322 8332 8334 8338 8340
cert_ridgeSupport_code_3 518
cert_ridgeSupport_rest_2 518 000 0
cert_ridgeSupport_rest_2 518 001 448
cert_ridgeSupport_rest_2 518 002 896
cert_ridgeSupport_rest_2 518 003 1344
cert_ridgeSupport_rest_2 518 004 1792
cert_ridgeSupport_rest_2 518 005 2240
cert_ridgeSupport_rest_2 518 006 2688
cert_ridgeSupport_rest_2 518 007 3136
cert_ridgeSupport_rest_2 518 008 3584
cert_ridgeSupport_rest_2 518 009 3682
cert_ridgeSupport_suffix_4 518 009
cert_ridgeSupport_suffix_3 518 008 009
cert_ridgeSupport_suffix_3 518 007 008
cert_ridgeSupport_suffix_3 518 006 007
cert_ridgeSupport_suffix_3 518 005 006
cert_ridgeSupport_suffix_3 518 004 005
cert_ridgeSupport_suffix_3 518 003 004
cert_ridgeSupport_suffix_3 518 002 003
cert_ridgeSupport_suffix_3 518 001 002
cert_ridgeSupport_suffix_3 518 000 001
cert_ridgeSupport_source_3 518 14 263
end Papers.RationalityTen.RootedCaches.RootedSixExtra00
