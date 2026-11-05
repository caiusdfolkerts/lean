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
def ridgeSupport584_000 : List Nat := [23,47,87,93,98,99,212,213,214,215,222,223,453,455,457,459,461,466,467,469,472,474,476,478,480,482,487,488,490,493,721,722]
def ridgeSupport584_001 : List Nat := [725,726,729,730,790,792,794,796,798,803,804,806,809,811,813,815,817,819,824,825,827,830,1253,1254,1255,1256,1257,1258,1321,1323,1325,1326]
def ridgeSupport584_002 : List Nat := [1328,1330,1331,1335,1340,1342,1344,1346,1347,1349,1351,1352,1356,1361,1405,1407,1409,1410,1412,1414,1415,1419,1424,1426,1428,1430,1431,1433,1435,1436,1440,1445]
def ridgeSupport584_003 : List Nat := [1468,1469,1471,1472,1475,1476,1477,1479,1480,1482,1489,1490,2238,2240,2247,2249,2262,2264,2270,2271,2276,2277,2283,2285,2290,2291,2304,2305,2318,2319,2324,2325]
def ridgeSupport584_004 : List Nat := [2338,2339,2340,2345,2346,2351,2352,2353,2361,2363,2364,2366,2370,2372,2379,2381,2394,2396,2402,2403,2408,2409,2415,2417,2422,2423,2436,2437,2450,2451,2456,2457]
def ridgeSupport584_005 : List Nat := [2470,2471,2472,2477,2478,2483,2484,2485,2493,2495,2496,2498,2558,2559,2562,2567,2570,2571,2574,2579,2594,2595,2606,2607,2612,2613,2616,2621,2624,2625,2628,2633]
def ridgeSupport584_006 : List Nat := [2648,2649,2660,2661,2862,2864,2871,2873,2878,2879,2892,2893,2898,2900,2906,2907,2912,2913,2919,2921,2926,2927,2928,2933,2934,2939,2940,2941,2954,2955,2960,2961]
def ridgeSupport584_007 : List Nat := [2971,2972,2979,2980,2990,2991,3498,3500,3507,3509,3514,3515,3528,3529,3534,3536,3542,3543,3548,3549,3555,3557,3562,3563,3564,3569,3570,3575,3576,3577,3590,3591]
def ridgeSupport584_008 : List Nat := [3596,3597,3607,3608,3615,3616,3672,3677,3680,3681,3698,3699,3702,3707,3716,3717,3721,3724,3726,3731,3734,3735,3752,3753,3756,3761,3770,3771,3775,3778,4248,4253]
def ridgeSupport584_009 : List Nat := [4256,4257,4260,4265,4268,4269,4273,4276,4279,4282,4302,4307,4310,4311,4314,4319,4322,4323,4327,4330,4333,4336,4458,4460,4467,4469,4470,4472,4479,4481,4490,4491]
def ridgeSupport584_010 : List Nat := [4496,4497,4519,4521,4526,4528,4579,4581,4586,4588,4596,4601,4602,4607,4657,4660,4663,4666,4836,4837,4872,4873,4966,4967,5122,5123]
def ridgeSupport584_code : Nat := 0x28074029b3cd9a613308972cb9247523791a48c63ff1fa8fcc7d23d91ea8f2c78e3611ae8d4c69e3231908c5c62a30317f8bc45da2eb1738b645aa1e10ed875439e1c70e286fc36a1af0d6869c33a1750b785a42c615b0ac854c2921430a084ec261d84ebf75dbae9d62eac754baa1d2ee96749ba39d18e89742ba11cf6e76739b9c9cc2e6072eb961c40e1f70c385dc1ae0c703b819bf2df86fbb7c9be2dec6f5b7a9bcade36eeb771baedd66e83739b92dc86ddb6e9b6adb36d636a975ebae5d22e8d738b9b5c8ae41716b8a5beadf16f6b765baadc16deb6e5b4ad9d6c2b605adad696a8b525a6ad3167eb3e59cacdd660b2e532a9914b2a58524a911482a4051ea8e146aa34517a8b9446a22509a839416a0a503a8093fe9fe4e1270137e9bd4daa6d13669ae4d6a6a134e9a64cca6613269924c2a6112ee9764b8a5bd2d29684b1a5892b895a4a6a52d28894249f24f1276939498a4c125e92a494a49124692248aa45121e90e480a4011e68f2476a3ad1ca8e446fa3791b08d6464a31d1808be2e91744b945c82e39714b885c32e016fcb7a5bc2d29680b3859b2cc965cb2c5942c91640b165872c31610b045812bf95f4aa254c2a4151ca8a5432a11500a7c53c29b94cca6453029714b4a5652927513a49d04e7273139467c33b19c8ce06663311978cb46563291930c9064631e18e0c6863031616d0b645ac2d51690b443da1ea0f4079c3c41e00ef07703b41d80ea874c3a41cd0e5872438e1c506f83781ae0d606a83500c606202e815c05e017
def ridgeSupport584_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport584_code
def ridgeSupport584_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport584_code
def ridgeSupport584_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport584_code
def ridgeSupport584_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport584_code
def ridgeSupport584_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport584_code
def ridgeSupport584_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport584_code
def ridgeSupport584_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport584_code
def ridgeSupport584_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport584_code
def ridgeSupport584_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport584_code
def ridgeSupport584_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport584_code
def ridgeSupport584_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport584_code
def ridgeSupport584_rest_011 : Nat := PackedRawNatGrowth.drop 4498 ridgeSupport584_code
def ridgeSupport584_suffix_011 : List Nat := []
def ridgeSupport584_suffix_010 : List Nat := ridgeSupport584_010 ++ ridgeSupport584_suffix_011
def ridgeSupport584_suffix_009 : List Nat := ridgeSupport584_009 ++ ridgeSupport584_suffix_010
def ridgeSupport584_suffix_008 : List Nat := ridgeSupport584_008 ++ ridgeSupport584_suffix_009
def ridgeSupport584_suffix_007 : List Nat := ridgeSupport584_007 ++ ridgeSupport584_suffix_008
def ridgeSupport584_suffix_006 : List Nat := ridgeSupport584_006 ++ ridgeSupport584_suffix_007
def ridgeSupport584_suffix_005 : List Nat := ridgeSupport584_005 ++ ridgeSupport584_suffix_006
def ridgeSupport584_suffix_004 : List Nat := ridgeSupport584_004 ++ ridgeSupport584_suffix_005
def ridgeSupport584_suffix_003 : List Nat := ridgeSupport584_003 ++ ridgeSupport584_suffix_004
def ridgeSupport584_suffix_002 : List Nat := ridgeSupport584_002 ++ ridgeSupport584_suffix_003
def ridgeSupport584_suffix_001 : List Nat := ridgeSupport584_001 ++ ridgeSupport584_suffix_002
def ridgeSupport584_suffix_000 : List Nat := ridgeSupport584_000 ++ ridgeSupport584_suffix_001
theorem ridgeSupport584_source : candidateSupports 584 =
    (PackedRawNatGrowth.readList 13 346 ridgeSupport584_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase03
