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
def ridgeSupport648_000 : List Nat := [25,45,75,81,84,86,222,223,224,225,232,233,440,441,442,445,446,451,452,457,459,481,483,485,487,489,494,495,497,500,663,664]
def ridgeSupport648_001 : List Nat := [667,668,671,672,709,710,711,714,715,720,721,726,728,750,752,754,756,758,763,764,766,769,1039,1040,1041,1042,1043,1044,1082,1086,1087,1088]
def ridgeSupport648_002 : List Nat := [1089,1091,1092,1099,1101,1125,1127,1129,1130,1132,1134,1135,1139,1144,1166,1170,1171,1172,1173,1175,1176,1183,1185,1209,1211,1213,1214,1216,1218,1219,1223,1228]
def ridgeSupport648_003 : List Nat := [1229,1231,1233,1235,1236,1238,1240,1241,1245,1247,1252,1253,2396,2401,2410,2412,2478,2479,2488,2489,2494,2495,2498,2500,2504,2505,2511,2514,2526,2527,2536,2537]
def ridgeSupport648_004 : List Nat := [2564,2569,2574,2575,2578,2580,2584,2585,2590,2591,2600,2601,2614,2615,2624,2625,2636,2641,2650,2652,2718,2719,2728,2729,2734,2735,2738,2740,2744,2745,2751,2754]
def ridgeSupport648_005 : List Nat := [2766,2767,2776,2777,2804,2809,2814,2815,2818,2820,2824,2825,2830,2831,2840,2841,2854,2855,2864,2865,2956,2958,2968,2970,2984,2985,2996,2997,3098,3103,3110,3115]
def ridgeSupport648_006 : List Nat := [3130,3131,3142,3143,3428,3433,3442,3444,3462,3463,3472,3473,3510,3511,3520,3521,3526,3527,3530,3532,3536,3537,3543,3546,3548,3553,3558,3559,3562,3564,3568,3569]
def ridgeSupport648_007 : List Nat := [3606,3607,3616,3617,3630,3631,3640,3641,3708,3709,3720,3721,4004,4009,4018,4020,4038,4039,4048,4049,4086,4087,4096,4097,4102,4103,4106,4108,4112,4113,4119,4122]
def ridgeSupport648_008 : List Nat := [4124,4129,4134,4135,4138,4140,4144,4145,4182,4183,4192,4193,4206,4207,4216,4217,4294,4296,4324,4326,4334,4335,4352,4353,4436,4441,4466,4471,4480,4481,4498,4499]
def ridgeSupport648_009 : List Nat := [4930,4932,4942,4944,4970,4971,4982,4983,5072,5077,5084,5089,5116,5117,5128,5129,5192,5197,5198,5202,5204,5209,5210,5214,5222,5223,5236,5237,5253,5256,5259,5263]
def ridgeSupport648_010 : List Nat := [5277,5280,5283,5287,5296,5298,5306,5311,5333,5335,5343,5346,5506,5507,5542,5543,5644,5645,5740,5741,6078,6079,6088,6089,6093,6094,6095,6096,6101,6102,6126,6127]
def ridgeSupport648_011 : List Nat := [6136,6137,6141,6142,6143,6144,6149,6150,6182,6183,6185,6187,6219,6220,6221,6222,6290,6292,6303,6306,6321,6322,6323,6324,6329,6330,6386,6388,6399,6402,6417,6418]
def ridgeSupport648_012 : List Nat := [6419,6420,6425,6426,6452,6453,6455,6457,6489,6490,6491,6492,6578,6579,6581,6583,6615,6616,6617,6618]
def ridgeSupport648_code : Nat := 0xced67673b19d7cdbe6d73679b2cae656f2b5959c9ce4df26b934c8d6467229913c8964472058ffc7a63cb1758b9c5a62cf1658b1c51627f129892c27613709984bc15e0a704f826c0360170017ffbff5ff6ff37f8bf7dfbafad7d5be85f3ef9d7cdbe4df22f7f7beb36d9b2c1b60cad3d69ab07582a71537e9af4d5a5fd2ea9654b0a53d28e94149da47d22e911485a3ad1d28cf466a2f516a8b3454a29513a89b448a04d0227fb3fc9f0cf727ab3d09bbcdda6d736a9a84d3a6893428c9c64a3031808bbc5ca2b3154880c4021df0ee87343921910c683cc1e20df06e830c1820af056818c0c205902a813c09a04301c80d405e023010806402a00f006800c001feeff67e8bf41f8efc67da3ec9f52fa4744ba21cfae7c71cb8e1c5ee2e710b881c2ee166f8b7c1bd8dea6f3b799bc2ddc6ed375dba2dd06e63729b8edc66e0b701b6edb66c8b641b0ed866ba35c9ad2d64623b119876c3a615b09983ec1a5daaed1752ba85cd2e6171cb8c598acc164eb2658cac6161eb0e584ac21608b0257fabf95f2af456cab6159eace5612afd572ab855a2ac955eaae554aaa153ea9e52e29694a2a4c520a90146ea36514a8a143ea1e50ca861428a12507a839412a044f4a7a13be9de4e9273d3929c84e2270937e9be4dca6e135e9ae4b625a92c295c27293909be4dd26c93609ac4d4269934499e4cd266131c9864c226012f897a4bb25c928493e49824b925492849324912388f047323791b88d846a234919c8ca44d225911088644122010fc87c43a20a104c824411208103c6022fe17e0bec5ec2f41790bc05dc2d816b0b445a02cb1650b1c58c2c51500a7c53829b14c0a5c3e81f10f787b83d21e70f2878c3c21cb0e487103861be0de86e83721b807483a01c20e006f83780ac054028812c05a019
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
def ridgeSupport648_rest_013 : Nat := PackedRawNatGrowth.drop 5252 ridgeSupport648_code
def ridgeSupport648_suffix_013 : List Nat := []
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
    (PackedRawNatGrowth.readList 13 404 ridgeSupport648_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
