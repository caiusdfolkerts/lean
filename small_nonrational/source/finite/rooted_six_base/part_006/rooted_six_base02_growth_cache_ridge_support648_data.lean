module
prelude
public import RootedSixBase02GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport648_000 : List Nat := [25,45,75,81,84,86,222,223,224,225,232,233,440,441,442,445,446,451,452,457,459,481,483,485,487,489,494,495,497,500,663,664]
def ridgeSupport648_001 : List Nat := [667,668,671,672,709,710,711,714,715,720,721,726,728,750,752,754,756,758,763,764,766,769,1039,1040,1041,1042,1043,1044,1082,1086,1087,1088]
def ridgeSupport648_002 : List Nat := [1089,1091,1092,1099,1101,1125,1127,1129,1130,1132,1134,1135,1139,1144,1166,1170,1171,1172,1173,1175,1176,1183,1185,1209,1211,1213,1214,1216,1218,1219,1223,1228]
def ridgeSupport648_003 : List Nat := [1229,1231,1233,1235,1236,1238,1240,1241,1245,1247,1252,1253,2396,2401,2410,2412,2478,2479,2488,2489,2494,2495,2498,2500,2504,2505,2511,2514,2526,2527,2536,2537]
def ridgeSupport648_004 : List Nat := [2564,2569,2574,2575,2578,2580,2584,2585,2590,2591,2600,2601,2614,2615,2624,2625,2636,2641,2650,2652,2718,2719,2728,2729,2734,2735,2738,2740,2744,2745,2751,2754]
def ridgeSupport648_005 : List Nat := [2766,2767,2776,2777,2804,2809,2814,2815,2818,2820,2824,2825,2830,2831,2840,2841,2854,2855,2864,2865,2956,2958,2968,2970,2984,2985,2996,2997,3098,3103,3110,3115]
def ridgeSupport648_006 : List Nat := [3130,3131,3142,3143,3428,3433,3442,3444,3462,3463,3472,3473,3510,3511,3520,3521,3526,3527,3530,3532,3536,3537,3543,3546,3548,3553,3558,3559,3562,3564,3568,3569]
def ridgeSupport648_007 : List Nat := [3606,3607,3616,3617,3630,3631,3640,3641,3708,3709,3720,3721,4004,4009,4018,4020,4038,4039,4048,4049,4086,4087,4096,4097,4102,4103,4106,4108,4112,4113,4119,4122]
def ridgeSupport648_008 : List Nat := [4124,4129,4134,4135,4138,4140,4144,4145,4182,4183,4192,4193,4206,4207,4216,4217,4294,4296,4324,4326,4334,4335,4352,4353,4436,4441,4466,4471,4480,4481,4498,4499]
def ridgeSupport648_009 : List Nat := [4930,4932,4942,4944,4970,4971,4982,4983,5072,5077,5084,5089,5116,5117,5128,5129,5744,5749,5750,5754,5770,5771,5774,5776,5780,5781,5787,5790,5802,5803,5812,5813]
def ridgeSupport648_010 : List Nat := [5818,5819,5828,5829,5840,5845,5850,5851,5854,5856,5860,5861,5864,5866,5870,5871,5876,5881,5882,5886,5902,5903,5906,5908,5912,5913,5919,5922,5934,5935,5944,5945]
def ridgeSupport648_011 : List Nat := [5950,5951,5960,5961,5972,5977,5982,5983,5986,5988,5992,5993,5996,5998,6002,6003,6062,6063,6070,6072,6074,6075,6082,6084,6098,6099,6110,6111,6172,6173,6176,6181]
def ridgeSupport648_012 : List Nat := [6184,6185,6188,6193,6208,6209,6220,6221,6368,6373,6374,6378,6390,6391,6400,6401,6406,6407,6410,6412,6416,6417,6423,6426,6428,6433,6438,6439,6442,6444,6448,6449]
def ridgeSupport648_013 : List Nat := [6454,6455,6464,6465,6480,6481,6485,6487,6504,6505,6656,6661,6662,6666,6678,6679,6688,6689,6694,6695,6698,6700,6704,6705,6711,6714,6716,6721,6726,6727,6730,6732]
def ridgeSupport648_014 : List Nat := [6736,6737,6742,6743,6752,6753,6768,6769,6773,6775,6832,6834,6836,6837,6854,6855,6862,6864,6872,6873,6881,6883,6938,6943,6946,6947,6964,6965,6968,6973,6982,6983]
def ridgeSupport648_015 : List Nat := [6987,6990,7216,7218,7220,7221,7228,7230,7232,7233,7241,7243,7247,7249,7322,7327,7330,7331,7334,7339,7342,7343,7347,7350,7353,7356,7424,7429,7430,7434,7436,7441]
def ridgeSupport648_016 : List Nat := [7442,7446,7454,7455,7468,7469,7485,7488,7491,7495,7509,7512,7515,7519,7528,7530,7538,7543,7565,7567,7575,7578,7738,7739,7774,7775,7876,7877,7972,7973]
def ridgeSupport648_code : Nat := 0x3e4bf24f62fb13cbfe5ef1df8ebb35d97ec7f637aefd72eb575a3abfd5beac7557a8fd43ea074f7a5bd2ce8ff47ba2dd12e88f433a15d06e82f403979cb9e5b72cf95fcaee55f29b947ca2e4ff26b8a3c4fe25f127883c40e1f70f386bc34e1970c369db4bda3ed1b67bb38d9aecd3647b22d8fec6b5c7ae1d6ceb635a1aced63eb1b56bab4d596ac34efa75d38e9c34c3a60d2be95b4a3a50d26692b48fa46d20e8f3475a37d18e8c3459a2ad13e89b443a20d0be85b415a06d02e8032d3968cabe5572a3950ca0e50326f936c98e4c325992ac93e49b24391cc8d645f223910c86642b20f906c80e4031ef8f6c75639b1cb8e0c26e133083840c18e0b3053828c12e08303b81cbefdf7afa77d2be25f0af777babdc5edaf5f7aebb9ddcaedd76cbb4dda2ec9762bafdd7aeb3754ba4dd22e7f73eb9cdce2e5f72eb915c7ee33718b8a5c4ae1f70eb7f5beadf36f4b77dbbadd56e8b72db92dc16deb6ddb6adab6d0b62db12d776bab5adad2d576aab4f5a6ed2b694b485a3ad1768ab3d59daceb670a04d0227fb3fc9f0cf727ab3d09bbcdda6d736a9a84d3a6893428c9c64a3031808bbc5ca2b3154880c4021df0ee87343921910c683cc1e20df06e830c1820af056818c0c205902a813c09a04301c80d405e023010806402a00f006800c001feeff67e8bf41f8efc67da3ec9f52fa4744ba21cfae7c71cb8e1c5ee2e710b881c2ee166f8b7c1bd8dea6f3b799bc2ddc6ed375dba2dd06e63729b8edc66e0b701b6edb66c8b641b0ed866ba35c9ad2d64623b119876c3a615b09983ec1a5daaed1752ba85cd2e6171cb8c598acc164eb2658cac6161eb0e584ac21608b0257fabf95f2af456cab6159eace5612afd572ab855a2ac955eaae554aaa153ea9e52e29694a2a4c520a90146ea36514a8a143ea1e50ca861428a12507a839412a044f4a7a13be9de4e9273d3929c84e2270937e9be4dca6e135e9ae4b625a92c295c27293909be4dd26c93609ac4d4269934499e4cd266131c9864c226012f897a4bb25c928493e49824b925492849324912388f047323791b88d846a234919c8ca44d225911088644122010fc87c43a20a104c824411208103c6022fe17e0bec5ec2f41790bc05dc2d816b0b445a02cb1650b1c58c2c51500a7c53829b14c0a5c3e81f10f787b83d21e70f2878c3c21cb0e487103861be0de86e83721b807483a01c20e006f83780ac054028812c05a019
def ridgeSupport648_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport648_code
def ridgeSupport648_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport648_code
def ridgeSupport648_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport648_code
def ridgeSupport648_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport648_code
def ridgeSupport648_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport648_code
def ridgeSupport648_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport648_code
def ridgeSupport648_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport648_code
def ridgeSupport648_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport648_code
def ridgeSupport648_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport648_code
def ridgeSupport648_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport648_code
def ridgeSupport648_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport648_code
def ridgeSupport648_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport648_code
def ridgeSupport648_rest_012 : Nat := PackedRawNatGrowth.drop 4992 ridgeSupport648_code
def ridgeSupport648_rest_013 : Nat := PackedRawNatGrowth.drop 5408 ridgeSupport648_code
def ridgeSupport648_rest_014 : Nat := PackedRawNatGrowth.drop 5824 ridgeSupport648_code
def ridgeSupport648_rest_015 : Nat := PackedRawNatGrowth.drop 6240 ridgeSupport648_code
def ridgeSupport648_rest_016 : Nat := PackedRawNatGrowth.drop 6656 ridgeSupport648_code
def ridgeSupport648_rest_017 : Nat := PackedRawNatGrowth.drop 7046 ridgeSupport648_code
def ridgeSupport648_suffix_017 : List Nat := []
def ridgeSupport648_suffix_016 : List Nat := ridgeSupport648_016 ++ ridgeSupport648_suffix_017
def ridgeSupport648_suffix_015 : List Nat := ridgeSupport648_015 ++ ridgeSupport648_suffix_016
def ridgeSupport648_suffix_014 : List Nat := ridgeSupport648_014 ++ ridgeSupport648_suffix_015
def ridgeSupport648_suffix_013 : List Nat := ridgeSupport648_013 ++ ridgeSupport648_suffix_014
def ridgeSupport648_suffix_012 : List Nat := ridgeSupport648_012 ++ ridgeSupport648_suffix_013
def ridgeSupport648_suffix_011 : List Nat := ridgeSupport648_011 ++ ridgeSupport648_suffix_012
def ridgeSupport648_suffix_010 : List Nat := ridgeSupport648_010 ++ ridgeSupport648_suffix_011
def ridgeSupport648_suffix_009 : List Nat := ridgeSupport648_009 ++ ridgeSupport648_suffix_010
def ridgeSupport648_suffix_008 : List Nat := ridgeSupport648_008 ++ ridgeSupport648_suffix_009
def ridgeSupport648_suffix_007 : List Nat := ridgeSupport648_007 ++ ridgeSupport648_suffix_008
def ridgeSupport648_suffix_006 : List Nat := ridgeSupport648_006 ++ ridgeSupport648_suffix_007
def ridgeSupport648_suffix_005 : List Nat := ridgeSupport648_005 ++ ridgeSupport648_suffix_006
def ridgeSupport648_suffix_004 : List Nat := ridgeSupport648_004 ++ ridgeSupport648_suffix_005
def ridgeSupport648_suffix_003 : List Nat := ridgeSupport648_003 ++ ridgeSupport648_suffix_004
def ridgeSupport648_suffix_002 : List Nat := ridgeSupport648_002 ++ ridgeSupport648_suffix_003
def ridgeSupport648_suffix_001 : List Nat := ridgeSupport648_001 ++ ridgeSupport648_suffix_002
def ridgeSupport648_suffix_000 : List Nat := ridgeSupport648_000 ++ ridgeSupport648_suffix_001
theorem ridgeSupport648_source : candidateSupports 648 =
    (PackedRawNatGrowth.readList 13 542 ridgeSupport648_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
