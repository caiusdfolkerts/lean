module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public meta import CertificateNumbers
public import RootedSixBase02GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport73_000 : List Nat := [5,21,22,23,175,176,179,180,185,187,188,191,192,197,199,200,203,204,209,330,419,420,422,423,424,425,427,428,430,431,433,434]
def ridgeSupport73_001 : List Nat := [440,441,443,444,445,446,448,449,451,452,454,455,461,462,464,465,466,467,469,470,472,473,475,476,2396,2397,2398,2399,2400,2401,2402,2403]
def ridgeSupport73_002 : List Nat := [2408,2409,2414,2415,2420,2421,2422,2423,2424,2425,2426,2427,2432,2433,2438,2439,2444,2445,2446,2447,2448,2449,2468,2469,2470,2471,2472,2473,2492,2493,2494,2495]
def ridgeSupport73_003 : List Nat := [2496,2497,2516,2517,2518,2519,2520,2521,2540,2541,2542,2543,2544,2545,2564,2565,2566,2567,2568,2569,2588,2589,2590,2591,2592,2593,2597,2599,2603,2605,2609,2611]
def ridgeSupport73_004 : List Nat := [2882,2883,2900,2901,2918,2919,2927,2929,2933,2935,2936,2937,2954,2955,2972,2973,2990,2991,2999,3001,3005,3007,3008,3009,3026,3027,3044,3045,3062,3063,3071,3073]
def ridgeSupport73_005 : List Nat := [3077,3079,3080,3081,3644,3646,3651,3652,3654,3657,3660,3662,3667,3668,3670,3673,3676,3678,3683,3684,3686,3689,5744,5745,5746,5747,5748,5749,5756,5757,5758,5759]
def ridgeSupport73_006 : List Nat := [5760,5761,5768,5769,5770,5771,5772,5773,5792,5793,5794,5795,5796,5797,5816,5817,5818,5819,5820,5821,5825,5827,5831,5833,5837,5839,5840,5841,5842,5843,5844,5845]
def ridgeSupport73_007 : List Nat := [5849,5851,5855,5857,5861,5863,5867,5868,5870,5871,5873,5874,6014,6015,6023,6025,6029,6031,6032,6033,6046,6048,6050,6051,6059,6061,6068,6069,6077,6079,6083,6085]
def ridgeSupport73_008 : List Nat := [6086,6087,6100,6102,6104,6105,6113,6115,6122,6123,6131,6133,6137,6139,6140,6141,6154,6156,6158,6159,6167,6169,6488,6491,6492,6495,6496,6499,7424,7425,7426,7427]
cert_ridgeSupport_2 73 7428 7429 7450 7452 7456 7458 7462 7464 7712 7713 7714 7715 7716 7717 7882 7886 7890
cert_ridgeSupport_code_2 73
cert_ridgeSupport_rest 73 000 0
cert_ridgeSupport_rest 73 001 416
cert_ridgeSupport_rest 73 002 832
cert_ridgeSupport_rest 73 003 1248
cert_ridgeSupport_rest 73 004 1664
cert_ridgeSupport_rest 73 005 2080
cert_ridgeSupport_rest 73 006 2496
cert_ridgeSupport_rest 73 007 2912
cert_ridgeSupport_rest 73 008 3328
cert_ridgeSupport_rest 73 009 3744
cert_ridgeSupport_rest 73 010 3965
cert_ridgeSupport_suffix_2 73 010
cert_ridgeSupport_suffix 73 009 010
cert_ridgeSupport_suffix 73 008 009
cert_ridgeSupport_suffix 73 007 008
cert_ridgeSupport_suffix 73 006 007
cert_ridgeSupport_suffix 73 005 006
cert_ridgeSupport_suffix 73 004 005
cert_ridgeSupport_suffix 73 003 004
cert_ridgeSupport_suffix 73 002 003
cert_ridgeSupport_suffix 73 001 002
cert_ridgeSupport_suffix 73 000 001
cert_ridgeSupport_source 73 13 305
end Papers.RationalityTen.RootedCaches.RootedSixBase02
