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
def ridgeSupport200_000 : List Nat := [21,45,85,91,97,98,188,189,190,191,198,199,432,433,437,439,440,444,446,447,449,453,454,458,460,461,465,467,468,470,697,698]
def ridgeSupport200_001 : List Nat := [701,702,705,706,769,770,774,776,777,781,783,784,786,790,791,795,797,798,802,804,805,807,1229,1230,1231,1232,1233,1234,1301,1302,1303,1306]
def ridgeSupport200_002 : List Nat := [1307,1308,1310,1315,1317,1322,1323,1324,1327,1328,1329,1331,1336,1338,1385,1386,1387,1390,1391,1392,1394,1399,1401,1406,1407,1408,1411,1412,1413,1415,1420,1422]
def ridgeSupport200_003 : List Nat := [1469,1470,1472,1473,1474,1475,1477,1478,1480,1481,1483,1484,2241,2243,2245,2247,2265,2267,2271,2273,2278,2279,2284,2285,2286,2287,2292,2293,2326,2327,2332,2333]
def ridgeSupport200_004 : List Nat := [2334,2335,2340,2341,2347,2349,2353,2355,2365,2366,2368,2369,2373,2375,2377,2379,2397,2399,2403,2405,2410,2411,2416,2417,2418,2419,2424,2425,2458,2459,2464,2465]
def ridgeSupport200_005 : List Nat := [2466,2467,2472,2473,2479,2481,2485,2487,2497,2498,2500,2501,2506,2507,2509,2511,2518,2519,2521,2523,2542,2543,2554,2555,2560,2561,2563,2565,2572,2573,2575,2577]
def ridgeSupport200_006 : List Nat := [2596,2597,2608,2609,2865,2867,2869,2871,2874,2875,2880,2881,2901,2903,2907,2909,2914,2915,2920,2921,2922,2923,2928,2929,2935,2937,2941,2943,2962,2963,2968,2969]
def ridgeSupport200_007 : List Nat := [2970,2971,2973,2974,2982,2983,3501,3503,3505,3507,3510,3511,3516,3517,3537,3539,3543,3545,3550,3551,3556,3557,3558,3559,3564,3565,3571,3573,3577,3579,3598,3599]
def ridgeSupport200_008 : List Nat := [3604,3605,3606,3607,3609,3610,3619,3621,3628,3629,3646,3647,3649,3651,3664,3665,3666,3668,3673,3675,3682,3683,3700,3701,3703,3705,3718,3719,3720,3722,4195,4197]
def ridgeSupport200_009 : List Nat := [4204,4205,4207,4209,4216,4217,4218,4220,4224,4226,4249,4251,4258,4259,4261,4263,4270,4271,4272,4274,4278,4280,4461,4463,4465,4467,4473,4475,4477,4479,4486,4487]
def ridgeSupport200_010 : List Nat := [4492,4493,4520,4522,4524,4526,4580,4582,4584,4586,4591,4593,4597,4599,4650,4652,4656,4658,4840,4841,4876,4877,4962,4963,5118,5119]
def ridgeSupport200_code : Nat := 0x27ff3fe9b1cd8a61b30c974cba246523091648aa3ef1f58f8c7be3d51e88f3479235d1ac8d546a231b18c8c3c61a2ff17d8bdc5e62e71718b7c5b61710b685942c215f0ae853c2961470a284dc26610508083e41ea0f3078838c1be0db06c832c18dd14e88743ba19cf2e7773ab9d1cc6e6272db965ca8e52728b941c86e4171fb8f9c5ae2c712b88dc34e1970bb859c2ae14707b839bf6df96fab7cdbdadec6f3b799bcade46efb779bb2dd76e9b745b7adbc6dbb6d9b66db16d7b6b574eba65cf2e75736b9a5ccae61726b925bfadf56f2b775b8adc16d6b6a5b4ada16c6b625aead6d6aeb555a0ad01676b3a59bacd5666b31518a8c144aa24508a83d41aa0c502a80d402a004fda7e93de9ee4eda7653ae9d64e7a7353969ca4e2a7113849c14dba6d53629af4d4a6a13469a24d0a68133699a4bca5e12e69724b8a5c12d696a4b2a58d2be95d4a5a52528e9454a0a50127c93d499a4c525a92b492a49123e91e48ea47122e91647aa3d11de8ee476a3b11ce8e6470a37d1b68d9463a3151868c12e6172cb925c82e31714b865c22e09700b7c5bd2c71630b0e5852c2160cb0057f2bf15e4aee5722b815bcadc56b2b515a4a7453829994c4a6052f29614aca545252919478a3851b28d145ca2c51526913449a04cf267133464e3251920c8863c31d18d8c5c62c3121880c3c61a3091840c186043011610b0457c2bd15d0ae43ac1d40e9874439a1cc0e5071838a1c10df86f83781b80db86d43621b0063831817e0be05e82f00c406102d815405a015
def ridgeSupport200_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport200_code
def ridgeSupport200_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport200_code
def ridgeSupport200_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport200_code
def ridgeSupport200_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport200_code
def ridgeSupport200_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport200_code
def ridgeSupport200_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport200_code
def ridgeSupport200_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport200_code
def ridgeSupport200_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport200_code
def ridgeSupport200_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport200_code
def ridgeSupport200_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport200_code
def ridgeSupport200_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport200_code
def ridgeSupport200_rest_011 : Nat := PackedRawNatGrowth.drop 4498 ridgeSupport200_code
def ridgeSupport200_suffix_011 : List Nat := []
def ridgeSupport200_suffix_010 : List Nat := ridgeSupport200_010 ++ ridgeSupport200_suffix_011
def ridgeSupport200_suffix_009 : List Nat := ridgeSupport200_009 ++ ridgeSupport200_suffix_010
def ridgeSupport200_suffix_008 : List Nat := ridgeSupport200_008 ++ ridgeSupport200_suffix_009
def ridgeSupport200_suffix_007 : List Nat := ridgeSupport200_007 ++ ridgeSupport200_suffix_008
def ridgeSupport200_suffix_006 : List Nat := ridgeSupport200_006 ++ ridgeSupport200_suffix_007
def ridgeSupport200_suffix_005 : List Nat := ridgeSupport200_005 ++ ridgeSupport200_suffix_006
def ridgeSupport200_suffix_004 : List Nat := ridgeSupport200_004 ++ ridgeSupport200_suffix_005
def ridgeSupport200_suffix_003 : List Nat := ridgeSupport200_003 ++ ridgeSupport200_suffix_004
def ridgeSupport200_suffix_002 : List Nat := ridgeSupport200_002 ++ ridgeSupport200_suffix_003
def ridgeSupport200_suffix_001 : List Nat := ridgeSupport200_001 ++ ridgeSupport200_suffix_002
def ridgeSupport200_suffix_000 : List Nat := ridgeSupport200_000 ++ ridgeSupport200_suffix_001
theorem ridgeSupport200_source : candidateSupports 200 =
    (PackedRawNatGrowth.readList 13 346 ridgeSupport200_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase03
