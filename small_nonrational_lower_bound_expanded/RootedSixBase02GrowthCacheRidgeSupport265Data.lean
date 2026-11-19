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
def ridgeSupport265_000 : List Nat := [7,22,24,26,186,189,190,193,196,210,213,214,217,220,235,236,239,240,245,332,418,419,421,422,425,426,427,429,430,432,437,438]
def ridgeSupport265_001 : List Nat := [460,462,463,465,466,468,470,471,473,474,477,478,481,483,484,486,487,489,491,492,494,495,498,499,2398,2399,2404,2405,2408,2409,2410,2411]
def ridgeSupport265_002 : List Nat := [2412,2413,2418,2419,2422,2423,2428,2429,2432,2433,2434,2435,2436,2437,2442,2443,2456,2457,2458,2459,2460,2461,2480,2481,2482,2483,2484,2485,2504,2505,2506,2507]
def ridgeSupport265_003 : List Nat := [2508,2509,2528,2529,2530,2531,2532,2533,2552,2553,2554,2555,2556,2557,2576,2577,2578,2579,2580,2581,2589,2592,2595,2598,2600,2601,2602,2603,2604,2605,2606,2608]
def ridgeSupport265_004 : List Nat := [2886,2887,2904,2905,2922,2923,2924,2926,2930,2932,2940,2941,3028,3029,3046,3047,3064,3065,3069,3072,3075,3078,3082,3083,3100,3101,3118,3119,3136,3137,3141,3144]
def ridgeSupport265_005 : List Nat := [3147,3150,3154,3155,3661,3663,3666,3669,3671,3672,3693,3695,3698,3701,3703,3704,3724,3726,3731,3732,3734,3737,5746,5747,5750,5751,5754,5755,5758,5759,5762,5763]
def ridgeSupport265_006 : List Nat := [5766,5767,5780,5781,5782,5783,5784,5785,5804,5805,5806,5807,5808,5809,5817,5820,5823,5826,5828,5829,5830,5831,5832,5833,5834,5836,5841,5844,5847,5850,5852,5853]
def ridgeSupport265_007 : List Nat := [5854,5855,5856,5857,5858,5860,5864,5866,5867,5869,5874,5875,6018,6019,6020,6022,6026,6028,6036,6037,6045,6047,6054,6055,6056,6058,6124,6125,6129,6132,6135,6138]
def ridgeSupport265_008 : List Nat := [6142,6143,6152,6157,6160,6161,6165,6168,6178,6179,6183,6186,6189,6192,6196,6197,6206,6211,6214,6215,6219,6222,6493,6494,6501,6502,6508,6511,7426,7427,7430,7431]
cert_ridgeSupport_2 265 7434 7435 7449 7451 7460 7465 7466 7471 7724 7725 7726 7727 7728 7729 7887 7895 7902
cert_ridgeSupport_code_2 265
cert_ridgeSupport_rest 265 000 0
cert_ridgeSupport_rest 265 001 416
cert_ridgeSupport_rest 265 002 832
cert_ridgeSupport_rest 265 003 1248
cert_ridgeSupport_rest 265 004 1664
cert_ridgeSupport_rest 265 005 2080
cert_ridgeSupport_rest 265 006 2496
cert_ridgeSupport_rest 265 007 2912
cert_ridgeSupport_rest 265 008 3328
cert_ridgeSupport_rest 265 009 3744
cert_ridgeSupport_rest 265 010 3965
cert_ridgeSupport_suffix_2 265 010
cert_ridgeSupport_suffix 265 009 010
cert_ridgeSupport_suffix 265 008 009
cert_ridgeSupport_suffix 265 007 008
cert_ridgeSupport_suffix 265 006 007
cert_ridgeSupport_suffix 265 005 006
cert_ridgeSupport_suffix 265 004 005
cert_ridgeSupport_suffix 265 003 004
cert_ridgeSupport_suffix 265 002 003
cert_ridgeSupport_suffix 265 001 002
cert_ridgeSupport_suffix 265 000 001
cert_ridgeSupport_source 265 13 305
end Papers.RationalityTen.RootedCaches.RootedSixBase02
