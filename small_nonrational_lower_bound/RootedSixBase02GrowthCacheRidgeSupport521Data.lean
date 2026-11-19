module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
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
def ridgeSupport521_000 : List Nat := [8,23,25,26,198,201,202,205,208,222,225,226,229,232,234,237,238,241,244,333,439,440,442,443,446,447,448,450,451,453,458,459]
def ridgeSupport521_001 : List Nat := [460,461,463,464,467,468,469,471,472,474,479,480,481,482,484,485,488,489,490,492,493,495,500,501,2400,2401,2406,2407,2412,2413,2414,2415]
def ridgeSupport521_002 : List Nat := [2416,2417,2418,2419,2424,2425,2430,2431,2436,2437,2438,2439,2440,2441,2442,2443,2462,2463,2464,2465,2466,2467,2486,2487,2488,2489,2490,2491,2510,2511,2512,2513]
def ridgeSupport521_003 : List Nat := [2514,2515,2534,2535,2536,2537,2538,2539,2558,2559,2560,2561,2562,2563,2582,2583,2584,2585,2586,2587,2588,2590,2594,2596,2600,2602,2606,2607,2608,2609,2610,2611]
def ridgeSupport521_004 : List Nat := [2958,2959,2976,2977,2994,2995,2996,2998,3002,3004,3012,3013,3030,3031,3048,3049,3066,3067,3068,3070,3074,3076,3084,3085,3102,3103,3120,3121,3138,3139,3140,3142]
def ridgeSupport521_005 : List Nat := [3146,3148,3156,3157,3677,3679,3682,3685,3687,3688,3709,3711,3714,3717,3719,3720,3725,3727,3730,3733,3735,3736,5748,5749,5752,5753,5754,5755,5760,5761,5764,5765]
def ridgeSupport521_006 : List Nat := [5766,5767,5786,5787,5788,5789,5790,5791,5810,5811,5812,5813,5814,5815,5816,5818,5822,5824,5828,5830,5834,5835,5836,5837,5838,5839,5840,5842,5846,5848,5852,5854]
def ridgeSupport521_007 : List Nat := [5858,5859,5860,5861,5862,5863,5865,5866,5868,5869,5871,5872,6072,6073,6074,6076,6080,6082,6090,6091,6099,6101,6108,6109,6110,6112,6126,6127,6128,6130,6134,6136]
def ridgeSupport521_008 : List Nat := [6144,6145,6153,6155,6162,6163,6164,6166,6180,6181,6182,6184,6188,6190,6198,6199,6207,6209,6216,6217,6218,6220,6497,6498,6505,6506,6509,6510,7428,7429,7432,7433]
cert_ridgeSupport_2 521 7434 7435 7455 7457 7461 7463 7467 7469 7730 7731 7732 7733 7734 7735 7891 7899 7903
cert_ridgeSupport_code_2 521
cert_ridgeSupport_rest 521 000 0
cert_ridgeSupport_rest 521 001 416
cert_ridgeSupport_rest 521 002 832
cert_ridgeSupport_rest 521 003 1248
cert_ridgeSupport_rest 521 004 1664
cert_ridgeSupport_rest 521 005 2080
cert_ridgeSupport_rest 521 006 2496
cert_ridgeSupport_rest 521 007 2912
cert_ridgeSupport_rest 521 008 3328
cert_ridgeSupport_rest 521 009 3744
cert_ridgeSupport_rest 521 010 3965
cert_ridgeSupport_suffix_2 521 010
cert_ridgeSupport_suffix 521 009 010
cert_ridgeSupport_suffix 521 008 009
cert_ridgeSupport_suffix 521 007 008
cert_ridgeSupport_suffix 521 006 007
cert_ridgeSupport_suffix 521 005 006
cert_ridgeSupport_suffix 521 004 005
cert_ridgeSupport_suffix 521 003 004
cert_ridgeSupport_suffix 521 002 003
cert_ridgeSupport_suffix 521 001 002
cert_ridgeSupport_suffix 521 000 001
cert_ridgeSupport_source 521 13 305
end Papers.RationalityTen.RootedCaches.RootedSixBase02
