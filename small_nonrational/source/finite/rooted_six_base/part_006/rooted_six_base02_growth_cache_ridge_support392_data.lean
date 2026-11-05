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
def ridgeSupport392_000 : List Nat := [24,44,74,80,83,86,210,211,212,213,220,221,419,420,421,424,425,430,431,436,438,481,482,486,488,489,493,495,496,498,651,652]
def ridgeSupport392_001 : List Nat := [655,656,659,660,688,689,690,693,694,699,700,705,707,750,751,755,757,758,762,764,765,767,1027,1028,1029,1030,1031,1032,1061,1065,1066,1067]
def ridgeSupport392_002 : List Nat := [1068,1070,1071,1078,1080,1126,1127,1128,1131,1132,1133,1135,1140,1142,1145,1149,1150,1151,1152,1154,1155,1162,1164,1210,1211,1212,1215,1216,1217,1219,1224,1226]
def ridgeSupport392_003 : List Nat := [1229,1232,1233,1234,1237,1238,1239,1241,1246,1247,1249,1250,2397,2399,2416,2418,2476,2477,2482,2483,2496,2497,2499,2502,2505,2508,2510,2511,2524,2525,2530,2531]
def ridgeSupport392_004 : List Nat := [2565,2567,2572,2573,2578,2579,2584,2586,2592,2593,2606,2607,2616,2617,2630,2631,2637,2639,2656,2658,2716,2717,2722,2723,2736,2737,2739,2742,2745,2748,2750,2751]
def ridgeSupport392_005 : List Nat := [2764,2765,2770,2771,2805,2807,2812,2813,2818,2819,2824,2826,2832,2833,2846,2847,2856,2857,2870,2871,2884,2886,2896,2898,2912,2913,2924,2925,3099,3101,3111,3113]
def ridgeSupport392_006 : List Nat := [3132,3133,3144,3145,3429,3431,3448,3450,3460,3461,3466,3467,3508,3509,3514,3515,3528,3529,3531,3534,3537,3540,3542,3543,3549,3551,3556,3557,3562,3563,3568,3570]
def ridgeSupport392_007 : List Nat := [3604,3605,3610,3611,3628,3629,3634,3635,3692,3693,3704,3705,4005,4007,4024,4026,4036,4037,4042,4043,4084,4085,4090,4091,4104,4105,4107,4110,4113,4116,4118,4119]
def ridgeSupport392_008 : List Nat := [4125,4127,4132,4133,4138,4139,4144,4146,4180,4181,4186,4187,4204,4205,4210,4211,4222,4224,4252,4254,4262,4263,4280,4281,4437,4439,4467,4469,4482,4483,4500,4501]
def ridgeSupport392_009 : List Nat := [4858,4860,4870,4872,4898,4899,4910,4911,5073,5075,5085,5087,5118,5119,5130,5131,5745,5747,5752,5754,5772,5773,5775,5778,5781,5784,5786,5787,5800,5801,5806,5807]
def ridgeSupport392_010 : List Nat := [5820,5821,5834,5835,5841,5843,5848,5849,5854,5855,5860,5862,5865,5866,5873,5874,5877,5879,5884,5886,5904,5905,5907,5910,5913,5916,5918,5919,5932,5933,5938,5939]
def ridgeSupport392_011 : List Nat := [5952,5953,5966,5967,5973,5975,5980,5981,5986,5987,5992,5994,5997,5998,6005,6006,6008,6009,6016,6018,6020,6021,6028,6030,6044,6045,6056,6057,6174,6175,6177,6179]
def ridgeSupport392_012 : List Nat := [6186,6187,6189,6191,6210,6211,6222,6223,6369,6371,6376,6378,6388,6389,6394,6395,6408,6409,6411,6414,6417,6420,6422,6423,6429,6431,6436,6437,6442,6443,6448,6450]
def ridgeSupport392_013 : List Nat := [6456,6457,6470,6471,6479,6481,6482,6484,6500,6501,6657,6659,6664,6666,6676,6677,6682,6683,6696,6697,6699,6702,6705,6708,6710,6711,6717,6719,6724,6725,6730,6731]
def ridgeSupport392_014 : List Nat := [6736,6738,6744,6745,6758,6759,6767,6769,6770,6772,6778,6780,6782,6783,6800,6801,6808,6810,6818,6819,6827,6829,6939,6941,6948,6949,6966,6967,6969,6971,6984,6985]
def ridgeSupport392_015 : List Nat := [6986,6988,7162,7164,7166,7167,7174,7176,7178,7179,7187,7189,7193,7195,7323,7325,7332,7333,7335,7337,7344,7345,7346,7348,7352,7354,7425,7427,7432,7434,7437,7439]
def ridgeSupport392_016 : List Nat := [7444,7446,7448,7449,7470,7471,7484,7486,7493,7495,7508,7510,7517,7519,7522,7524,7539,7541,7559,7561,7574,7576,7740,7741,7776,7777,7874,7875,7970,7971]
def ridgeSupport392_code : Nat := 0x3e47f22f61fb0bcc3e60f1ef8f3b31d96ec4f61faebd73eb2758babfd5deab7553a8fd45e9f74f3a5fd2ee8cf463a2dd14e87f437a15d08e81f407975cb8e5a72cb963cb0e54f29f94bca4e4ef26f837c19e0af04f817c0ae04701b7ffbfedfe6feb699b4ada4ed23677b39d9becdb64bb24d8eec6f55baabd51ea8b535a98d48ea434ffa7ed3e69eb4e9a72d38e9bf4cfa66d2ce9634a5a50d25e92b48ba44d1fe8f746fa36d1a68c745da2bd14e8a3437a1ad0ae853415a08d01e8072cb964caa654b2a394fca3e51b273938c9964c325792ac92e49323f91dc8be45b229911c87642f213908c7de3eb1eb8f4c7563a31c78e1c27e13b087842c17e0b705782ac11e08703f81ebd4dea2f3b79cbc75e32f0b784bc15e02ef3778bbb5dd6edd76dbb55da2ec7762baedd72eaf755ba7dd3ae83740b99dccae5b72cb8fdc7ae39719b8b5c4ee23710b7f5bf2def6f5b795bc6dd56e9b735b92dbf6deb6cdb62da76d1b65db2ad7b6bcb57dabad536a8b4dda6ad31695b495a3ed1b68cb3d59e2ce7671a05d02a7ff3fe9efcf767a73d1997ccba6473229844c1a5f92fa8cac6523071828bac5ce2af15585cc2e214f0a684f427210107e839c1ca0db06c82dc16a0ab05481940c205702a812c09203f01d80bc05a029011807402e0130087fdbfe9feaff47e5bf29f8afc47dd3ee1f4efa573cb9e1cdae6c719b8c9c5ae2c70db869c2ae146f937c1bd6dea6f2b791bbeddd6ebb759ba8dd16e7372db92dc86ddb6e9b6adb46c5b629b0ad846bd35e1aced65624b12187ac3c614b09d83ac1b5b6adb16c2b605a92d4168cb4459bacd9652b2858fac79622b105852c21606b0257eabf15eeaf5569ab4959aacc55faaf9578ab955b2acd562ab0551aa8953aa9c531298149ea4d523a919472a38517a8b9442a2050d2861426a12506a83140ea054f1a7893ba9dc4e7a7393989c94e3270d3829c04d9a6c935a9ac4b925c12be95d27113849be4de26c935c9ac4d526913449a04cd26513209864c126012fc9784bb25d123091448324112008fe47e23e91e48ec47423791b48d846b234119c8cc43821b10bc85c42c21590a8852425204101c80c405202100c5fe2fd17e0be85ec2f51798bbc5dc2c31608af05762b615a8ac85622b014a0a4c52028f1460a2c3e41f00f787b43d21e80f307883c21b60da06bc35c1a90d406943481a306e83701aa0d406983480ac0530280128058018
def ridgeSupport392_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport392_code
def ridgeSupport392_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport392_code
def ridgeSupport392_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport392_code
def ridgeSupport392_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport392_code
def ridgeSupport392_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport392_code
def ridgeSupport392_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport392_code
def ridgeSupport392_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport392_code
def ridgeSupport392_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport392_code
def ridgeSupport392_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport392_code
def ridgeSupport392_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport392_code
def ridgeSupport392_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport392_code
def ridgeSupport392_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport392_code
def ridgeSupport392_rest_012 : Nat := PackedRawNatGrowth.drop 4992 ridgeSupport392_code
def ridgeSupport392_rest_013 : Nat := PackedRawNatGrowth.drop 5408 ridgeSupport392_code
def ridgeSupport392_rest_014 : Nat := PackedRawNatGrowth.drop 5824 ridgeSupport392_code
def ridgeSupport392_rest_015 : Nat := PackedRawNatGrowth.drop 6240 ridgeSupport392_code
def ridgeSupport392_rest_016 : Nat := PackedRawNatGrowth.drop 6656 ridgeSupport392_code
def ridgeSupport392_rest_017 : Nat := PackedRawNatGrowth.drop 7046 ridgeSupport392_code
def ridgeSupport392_suffix_017 : List Nat := []
def ridgeSupport392_suffix_016 : List Nat := ridgeSupport392_016 ++ ridgeSupport392_suffix_017
def ridgeSupport392_suffix_015 : List Nat := ridgeSupport392_015 ++ ridgeSupport392_suffix_016
def ridgeSupport392_suffix_014 : List Nat := ridgeSupport392_014 ++ ridgeSupport392_suffix_015
def ridgeSupport392_suffix_013 : List Nat := ridgeSupport392_013 ++ ridgeSupport392_suffix_014
def ridgeSupport392_suffix_012 : List Nat := ridgeSupport392_012 ++ ridgeSupport392_suffix_013
def ridgeSupport392_suffix_011 : List Nat := ridgeSupport392_011 ++ ridgeSupport392_suffix_012
def ridgeSupport392_suffix_010 : List Nat := ridgeSupport392_010 ++ ridgeSupport392_suffix_011
def ridgeSupport392_suffix_009 : List Nat := ridgeSupport392_009 ++ ridgeSupport392_suffix_010
def ridgeSupport392_suffix_008 : List Nat := ridgeSupport392_008 ++ ridgeSupport392_suffix_009
def ridgeSupport392_suffix_007 : List Nat := ridgeSupport392_007 ++ ridgeSupport392_suffix_008
def ridgeSupport392_suffix_006 : List Nat := ridgeSupport392_006 ++ ridgeSupport392_suffix_007
def ridgeSupport392_suffix_005 : List Nat := ridgeSupport392_005 ++ ridgeSupport392_suffix_006
def ridgeSupport392_suffix_004 : List Nat := ridgeSupport392_004 ++ ridgeSupport392_suffix_005
def ridgeSupport392_suffix_003 : List Nat := ridgeSupport392_003 ++ ridgeSupport392_suffix_004
def ridgeSupport392_suffix_002 : List Nat := ridgeSupport392_002 ++ ridgeSupport392_suffix_003
def ridgeSupport392_suffix_001 : List Nat := ridgeSupport392_001 ++ ridgeSupport392_suffix_002
def ridgeSupport392_suffix_000 : List Nat := ridgeSupport392_000 ++ ridgeSupport392_suffix_001
theorem ridgeSupport392_source : candidateSupports 392 =
    (PackedRawNatGrowth.readList 13 542 ridgeSupport392_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
