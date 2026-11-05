module
prelude
public import RootedSixExtra02GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport328_000 : List Nat := [22,42,72,78,83,85,186,187,188,189,196,197,418,420,422,424,426,431,432,434,437,460,461,465,467,468,472,474,475,477,627,628]
def ridgeSupport328_001 : List Nat := [631,632,635,636,687,689,691,693,695,700,701,703,706,729,730,734,736,737,741,743,744,746,1003,1004,1005,1006,1007,1008,1062,1064,1066,1067]
def ridgeSupport328_002 : List Nat := [1069,1071,1072,1076,1081,1105,1106,1107,1110,1111,1112,1114,1119,1121,1146,1148,1150,1151,1153,1155,1156,1160,1165,1189,1190,1191,1194,1195,1196,1198,1203,1205]
def ridgeSupport328_003 : List Nat := [1230,1232,1233,1235,1236,1238,1240,1241,1243,1244,1248,1249,2403,2405,2414,2419,2470,2471,2480,2481,2493,2496,2502,2503,2507,2509,2512,2513,2518,2519,2528,2529]
def ridgeSupport328_004 : List Nat := [2566,2567,2571,2573,2576,2577,2582,2587,2598,2599,2608,2609,2622,2623,2632,2633,2643,2645,2654,2659,2710,2711,2720,2721,2733,2736,2742,2743,2747,2749,2752,2753]
def ridgeSupport328_005 : List Nat := [2758,2759,2768,2769,2806,2807,2811,2813,2816,2817,2822,2827,2838,2839,2848,2849,2862,2863,2872,2873,2882,2887,2894,2899,2914,2915,2926,2927,3027,3029,3039,3041]
def ridgeSupport328_006 : List Nat := [3060,3061,3072,3073,3435,3437,3446,3451,3454,3455,3464,3465,3502,3503,3512,3513,3525,3528,3534,3535,3539,3541,3544,3545,3550,3551,3555,3557,3560,3561,3566,3571]
def ridgeSupport328_007 : List Nat := [3598,3599,3608,3609,3622,3623,3632,3633,3660,3661,3672,3673,4011,4013,4022,4027,4030,4031,4040,4041,4078,4079,4088,4089,4101,4104,4110,4111,4115,4117,4120,4121]
def ridgeSupport328_008 : List Nat := [4126,4127,4131,4133,4136,4137,4142,4147,4174,4175,4184,4185,4198,4199,4208,4209,4220,4225,4250,4255,4264,4265,4282,4283,4365,4367,4395,4397,4410,4411,4428,4429]
def ridgeSupport328_009 : List Nat := [4856,4861,4868,4873,4900,4901,4912,4913,5001,5003,5013,5015,5046,5047,5058,5059,5193,5196,5199,5203,5205,5208,5211,5215,5218,5219,5232,5233,5252,5257,5258,5262]
def ridgeSupport328_010 : List Nat := [5276,5281,5282,5286,5288,5293,5301,5303,5325,5328,5336,5338,5512,5513,5548,5549,5638,5639,5734,5735,6070,6071,6080,6081,6094,6095,6098,6100,6101,6102,6118,6119]
def ridgeSupport328_011 : List Nat := [6128,6129,6142,6143,6146,6148,6149,6150,6165,6166,6167,6168,6200,6202,6204,6205,6285,6288,6299,6301,6322,6323,6326,6328,6329,6330,6381,6384,6395,6397,6418,6419]
def ridgeSupport328_012 : List Nat := [6422,6424,6425,6426,6435,6436,6437,6438,6470,6472,6474,6475,6561,6562,6563,6564,6596,6598,6600,6601]
def ridgeSupport328_code : Nat := 0xce4e72338d9c4cd2668f3459a1ca5e52b291946c936497249923c8d6467231916c89e44b1fb8fbc7863b71758b9c5c62db1678b2c4ee26f12188dc1ee0f3075838c0c605f02d815c036017009802bffdffafe37f0bf3df9afad7d5bea5f4af9f7cebe0df02f6f7b6b33d99ac0f606ad6d6b2b13588a6d53629a14cda5bd2d695b4a8a53528a94349ca47522a913484a38d1c28c7462a2fd16e8b1455a29d13e8994499e1cf0a76f3b69cbce56717389998ccc264b324984cc125fb2f88a6c53227713a896c4ae21f10d85dc2ea1530a884fc26a10307c838c1c20cf06682cc16209f04e819c0ba053028812c08e03f01e80cc06202b013807c03a0110057fcbfe1fdefee7e4bf21f7efbe7ddbed9f5afab72cb961c9ae4c718b8c1c4ee2670cb861c1ee0e6f9b7b9bd2de86f2b78dbbedde6ecb761baadd36e7b739b90dc56dcb6e1b5edae6c4b621afed7e6bdb5d9adad6b600b0017eabf45f0af7d7aabd35b7adb96c6b625a9ad3968eb4259cace165eb2e590ac8162eb16585ac19602b0057eabed5eeaf6568ab4158eac6560ab0157aabb55baad9560aad550aa8152ea96531a9794aaa53524a92147ea3e518a8c144ea2650da859422a10506a82d40ea064f0a7813ae9d64e8a74139a9cb4e3a7193809bd4d8a6c134e9a64b9a5b92ca96327093809b84db26c93609ac4d426993449a04ce25a92cc95c4ac25592a894e4a6252923491048424192048fe47e23e11e88c245f22d11608ae45622991488a243921a10c085e42d21590a88504261f80fbc7dc3ed1f60fac5d42e81738b945c22e016f0b685b22c215f8af45782b715a8acc5622af13e09ec4f027713a09cc3ba1db0ed07603a81d30e887343981b50d906c035e1aa0d406983481a2062831017a0bc05d82e80aa0530270120054016
def ridgeSupport328_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport328_code
def ridgeSupport328_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport328_code
def ridgeSupport328_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport328_code
def ridgeSupport328_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport328_code
def ridgeSupport328_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport328_code
def ridgeSupport328_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport328_code
def ridgeSupport328_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport328_code
def ridgeSupport328_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport328_code
def ridgeSupport328_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport328_code
def ridgeSupport328_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport328_code
def ridgeSupport328_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport328_code
def ridgeSupport328_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport328_code
def ridgeSupport328_rest_012 : Nat := PackedRawNatGrowth.drop 4992 ridgeSupport328_code
def ridgeSupport328_rest_013 : Nat := PackedRawNatGrowth.drop 5252 ridgeSupport328_code
def ridgeSupport328_suffix_013 : List Nat := []
def ridgeSupport328_suffix_012 : List Nat := ridgeSupport328_012 ++ ridgeSupport328_suffix_013
def ridgeSupport328_suffix_011 : List Nat := ridgeSupport328_011 ++ ridgeSupport328_suffix_012
def ridgeSupport328_suffix_010 : List Nat := ridgeSupport328_010 ++ ridgeSupport328_suffix_011
def ridgeSupport328_suffix_009 : List Nat := ridgeSupport328_009 ++ ridgeSupport328_suffix_010
def ridgeSupport328_suffix_008 : List Nat := ridgeSupport328_008 ++ ridgeSupport328_suffix_009
def ridgeSupport328_suffix_007 : List Nat := ridgeSupport328_007 ++ ridgeSupport328_suffix_008
def ridgeSupport328_suffix_006 : List Nat := ridgeSupport328_006 ++ ridgeSupport328_suffix_007
def ridgeSupport328_suffix_005 : List Nat := ridgeSupport328_005 ++ ridgeSupport328_suffix_006
def ridgeSupport328_suffix_004 : List Nat := ridgeSupport328_004 ++ ridgeSupport328_suffix_005
def ridgeSupport328_suffix_003 : List Nat := ridgeSupport328_003 ++ ridgeSupport328_suffix_004
def ridgeSupport328_suffix_002 : List Nat := ridgeSupport328_002 ++ ridgeSupport328_suffix_003
def ridgeSupport328_suffix_001 : List Nat := ridgeSupport328_001 ++ ridgeSupport328_suffix_002
def ridgeSupport328_suffix_000 : List Nat := ridgeSupport328_000 ++ ridgeSupport328_suffix_001
theorem ridgeSupport328_source : candidateSupports 328 =
    (PackedRawNatGrowth.readList 13 404 ridgeSupport328_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
