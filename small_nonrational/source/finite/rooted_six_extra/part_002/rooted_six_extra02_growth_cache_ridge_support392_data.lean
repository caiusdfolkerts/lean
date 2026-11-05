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
def ridgeSupport392_000 : List Nat := [24,44,74,80,83,86,210,211,212,213,220,221,419,420,421,424,425,430,431,436,438,481,482,486,488,489,493,495,496,498,651,652]
def ridgeSupport392_001 : List Nat := [655,656,659,660,688,689,690,693,694,699,700,705,707,750,751,755,757,758,762,764,765,767,1027,1028,1029,1030,1031,1032,1061,1065,1066,1067]
def ridgeSupport392_002 : List Nat := [1068,1070,1071,1078,1080,1126,1127,1128,1131,1132,1133,1135,1140,1142,1145,1149,1150,1151,1152,1154,1155,1162,1164,1210,1211,1212,1215,1216,1217,1219,1224,1226]
def ridgeSupport392_003 : List Nat := [1229,1232,1233,1234,1237,1238,1239,1241,1246,1247,1249,1250,2397,2399,2416,2418,2476,2477,2482,2483,2496,2497,2499,2502,2505,2508,2510,2511,2524,2525,2530,2531]
def ridgeSupport392_004 : List Nat := [2565,2567,2572,2573,2578,2579,2584,2586,2592,2593,2606,2607,2616,2617,2630,2631,2637,2639,2656,2658,2716,2717,2722,2723,2736,2737,2739,2742,2745,2748,2750,2751]
def ridgeSupport392_005 : List Nat := [2764,2765,2770,2771,2805,2807,2812,2813,2818,2819,2824,2826,2832,2833,2846,2847,2856,2857,2870,2871,2884,2886,2896,2898,2912,2913,2924,2925,3099,3101,3111,3113]
def ridgeSupport392_006 : List Nat := [3132,3133,3144,3145,3429,3431,3448,3450,3460,3461,3466,3467,3508,3509,3514,3515,3528,3529,3531,3534,3537,3540,3542,3543,3549,3551,3556,3557,3562,3563,3568,3570]
def ridgeSupport392_007 : List Nat := [3604,3605,3610,3611,3628,3629,3634,3635,3692,3693,3704,3705,4005,4007,4024,4026,4036,4037,4042,4043,4084,4085,4090,4091,4104,4105,4107,4110,4113,4116,4118,4119]
def ridgeSupport392_008 : List Nat := [4125,4127,4132,4133,4138,4139,4144,4146,4180,4181,4186,4187,4204,4205,4210,4211,4222,4224,4252,4254,4262,4263,4280,4281,4437,4439,4467,4469,4482,4483,4500,4501]
def ridgeSupport392_009 : List Nat := [4858,4860,4870,4872,4898,4899,4910,4911,5073,5075,5085,5087,5118,5119,5130,5131,5193,5195,5200,5202,5205,5207,5212,5214,5216,5217,5238,5239,5252,5254,5261,5263]
def ridgeSupport392_010 : List Nat := [5276,5278,5285,5287,5290,5292,5307,5309,5327,5329,5342,5344,5508,5509,5544,5545,5642,5643,5738,5739,6076,6077,6082,6083,6092,6094,6096,6097,6100,6103,6124,6125]
def ridgeSupport392_011 : List Nat := [6130,6131,6140,6142,6144,6145,6148,6151,6164,6165,6167,6169,6218,6220,6222,6223,6291,6294,6297,6300,6320,6322,6324,6325,6328,6331,6387,6390,6393,6396,6416,6418]
def ridgeSupport392_012 : List Nat := [6420,6421,6424,6427,6434,6435,6437,6439,6488,6490,6492,6493,6560,6561,6563,6565,6614,6616,6618,6619]
def ridgeSupport392_code : Nat := 0xcede76b3b19d6cd2e68f3439a0caee5732b5958c93e497247922c8de46322b914c8964431f98f9c7b63cf1778b8c5ae2d31658b0c4e626712d893c27e13b09984ac0ce05f02b814c03e013003800bff5ff2fe77f2bf6dfb2faf7d4be8df42f9d7ccbe1df0af7b7bcb35d9aac1760aad4d6a2b0b584a70537a9a34cfa5ed2ee9594aaa53d29693d49ca47d23690d484a3bd1da8c3460a2f51728af455a295142897449a05d02a7ff3fe9efcf767a73d1997ccba6473229844c1a5f92fa8cac6523071828bac5ce2af15585cc2e214f0a684f427210107e839c1ca0db06c82dc16a0ab05481940c205702a812c09203f01d80bc05a029011807402e0130087fdbfe9feaff47e5bf29f8afc47dd3ee1f4efa573cb9e1cdae6c719b8c9c5ae2c70db869c2ae146f937c1bd6dea6f2b791bbeddd6ebb759ba8dd16e7372db92dc86ddb6e9b6adb46c5b629b0ad846bd35e1aced65624b12187ac3c614b09d83ac1b5b6adb16c2b605a92d4168cb4459bacd9652b2858fac79622b105852c21606b0257eabf15eeaf5569ab4959aacc55faaf9578ab955b2acd562ab0551aa8953aa9c531298149ea4d523a919472a38517a8b9442a2050d2861426a12506a83140ea054f1a7893ba9dc4e7a7393989c94e3270d3829c04d9a6c935a9ac4b925c12be95d27113849be4de26c935c9ac4d526913449a04cd26513209864c126012fc9784bb25d123091448324112008fe47e23e91e48ec47423791b48d846b234119c8cc43821b10bc85c42c21590a8852425204101c80c405202100c5fe2fd17e0be85ec2f51798bbc5dc2c31608af05762b615a8ac85622b014a0a4c52028f1460a2c3e41f00f787b43d21e80f307883c21b60da06bc35c1a90d406943481a306e83701aa0d406983480ac0530280128058018
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
def ridgeSupport392_rest_013 : Nat := PackedRawNatGrowth.drop 5252 ridgeSupport392_code
def ridgeSupport392_suffix_013 : List Nat := []
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
    (PackedRawNatGrowth.readList 13 404 ridgeSupport392_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
