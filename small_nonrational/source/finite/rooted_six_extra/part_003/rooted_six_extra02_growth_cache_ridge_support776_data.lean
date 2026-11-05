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
def ridgeSupport776_000 : List Nat := [26,46,76,82,85,86,234,235,236,237,244,245,461,462,463,466,467,472,473,478,480,482,483,484,487,488,493,494,499,501,675,676]
def ridgeSupport776_001 : List Nat := [679,680,683,684,730,731,732,735,736,741,742,747,749,751,752,753,756,757,762,763,768,770,1051,1052,1053,1054,1055,1056,1103,1107,1108,1109]
def ridgeSupport776_002 : List Nat := [1110,1112,1113,1120,1122,1124,1128,1129,1130,1131,1133,1134,1141,1143,1187,1191,1192,1193,1194,1196,1197,1204,1206,1208,1212,1213,1214,1215,1217,1218,1225,1227]
def ridgeSupport776_003 : List Nat := [1229,1230,1234,1235,1236,1237,1239,1240,1248,1250,1251,1253,2398,2400,2404,2406,2484,2485,2490,2491,2492,2493,2498,2499,2504,2506,2510,2512,2532,2533,2538,2539]
def ridgeSupport776_004 : List Nat := [2566,2568,2572,2574,2580,2581,2586,2587,2588,2589,2594,2595,2612,2613,2618,2619,2638,2640,2644,2646,2724,2725,2730,2731,2732,2733,2738,2739,2744,2746,2750,2752]
def ridgeSupport776_005 : List Nat := [2772,2773,2778,2779,2806,2808,2812,2814,2820,2821,2826,2827,2828,2829,2834,2835,2852,2853,2858,2859,3028,3030,3040,3042,3056,3057,3068,3069,3100,3102,3112,3114]
def ridgeSupport776_006 : List Nat := [3128,3129,3140,3141,3430,3432,3436,3438,3468,3469,3474,3475,3516,3517,3522,3523,3524,3525,3530,3531,3536,3538,3542,3544,3550,3552,3556,3558,3564,3565,3570,3571]
def ridgeSupport776_007 : List Nat := [3612,3613,3618,3619,3636,3637,3642,3643,3724,3725,3736,3737,4006,4008,4012,4014,4044,4045,4050,4051,4092,4093,4098,4099,4100,4101,4106,4107,4112,4114,4118,4120]
def ridgeSupport776_008 : List Nat := [4126,4128,4132,4134,4140,4141,4146,4147,4188,4189,4194,4195,4212,4213,4218,4219,4366,4368,4396,4398,4406,4407,4424,4425,4438,4440,4468,4470,4478,4479,4496,4497]
def ridgeSupport776_009 : List Nat := [5002,5004,5014,5016,5042,5043,5054,5055,5074,5076,5086,5088,5114,5115,5126,5127,5194,5196,5198,5200,5206,5208,5210,5212,5228,5229,5234,5235,5255,5257,5259,5261]
def ridgeSupport776_010 : List Nat := [5279,5281,5283,5285,5302,5304,5308,5310,5339,5341,5345,5347,5504,5505,5540,5541,5646,5647,5742,5743,6084,6085,6090,6091,6092,6093,6095,6097,6098,6099,6132,6133]
def ridgeSupport776_011 : List Nat := [6138,6139,6140,6141,6143,6145,6146,6147,6200,6201,6203,6205,6218,6219,6221,6223,6296,6298,6302,6304,6320,6321,6323,6325,6326,6327,6392,6394,6398,6400,6416,6417]
def ridgeSupport776_012 : List Nat := [6419,6421,6422,6423,6470,6471,6473,6475,6488,6489,6491,6493,6596,6597,6599,6601,6614,6615,6617,6619]
def ridgeSupport776_code : Nat := 0xcede7673af9d6ce4e71f38b9c4caee56f2b3958ca5e52728f946c8be45b22b913c88e4432018fec7d63e316f8b6c5ae2cf1638b0c50627b135898c27e13709784ac1ee0ef073838c01e00b0037ffbfedff2ff77fabfadfd2fa77d2be8df3ef9b7ccbe5df2af8b7c4b37d9bac1f60ead2d692b03580a71d3869bb4dba5f52f29714b6a52d28e94349fa46d22e913487a39d1ca8db46ca2e516a8b1456a28513a89944aa03d01a7f73fa9f04f7a7a93d29dfcefa7673b29cc4e5a71938a8c8c6422ff17e8bb45d22b11568a4c52226f13689744b222110e83dc1ea0eb074831c18a0bb05c819c0ca05b02c813409204101e80c405a025010805c02a00b004801c009ffaffc7e9bf49f9afcc7d73eb1f50fa674cba61d1ae8c71db8e9c6ae34711b889c3ae1c6f9b7c9bdadec6f33791bc0dde6ec3759ba4dd06e5b729b8adc46e1b709b7adbc6c9b649b1ad8c6b735b1ad0d66622b111872c3861530a183cc1c5feaff17e2bf05f12f817acbd4595aca964ab24589ac4961ab0c585ac2960ab0457f2bf15f0af656dab695aaad45602af9574ab8559aac955aaac555aaa954aaa452b29514a0a4e51da8e946aa34511a88943aa1c50da86942aa145072831410a064f5a7a93ca9e44e827393949c84e1a70937a9bc4dda6e936a9b44b325912c095e272938c9c44e026c135c9aa4d4269934899c4cd26593249844c125f92f897a4bc25c12d89684ad25612a89524a8253928c8ee47523711b48d646a23491a08c846223011648b045622a91508a644f210107c83c41d20e106c60430017d8be85ea2f41788bc05de2ed1758b985ca2e016f8b705b62da1560aac5502a71520a8c3ea1f30f707b43d01e70f2078c3c41e00ef07643b01d30e9073c39c1cd07a83d01da0ec07583a80ac055029013005c01a
def ridgeSupport776_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport776_code
def ridgeSupport776_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport776_code
def ridgeSupport776_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport776_code
def ridgeSupport776_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport776_code
def ridgeSupport776_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport776_code
def ridgeSupport776_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport776_code
def ridgeSupport776_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport776_code
def ridgeSupport776_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport776_code
def ridgeSupport776_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport776_code
def ridgeSupport776_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport776_code
def ridgeSupport776_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport776_code
def ridgeSupport776_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport776_code
def ridgeSupport776_rest_012 : Nat := PackedRawNatGrowth.drop 4992 ridgeSupport776_code
def ridgeSupport776_rest_013 : Nat := PackedRawNatGrowth.drop 5252 ridgeSupport776_code
def ridgeSupport776_suffix_013 : List Nat := []
def ridgeSupport776_suffix_012 : List Nat := ridgeSupport776_012 ++ ridgeSupport776_suffix_013
def ridgeSupport776_suffix_011 : List Nat := ridgeSupport776_011 ++ ridgeSupport776_suffix_012
def ridgeSupport776_suffix_010 : List Nat := ridgeSupport776_010 ++ ridgeSupport776_suffix_011
def ridgeSupport776_suffix_009 : List Nat := ridgeSupport776_009 ++ ridgeSupport776_suffix_010
def ridgeSupport776_suffix_008 : List Nat := ridgeSupport776_008 ++ ridgeSupport776_suffix_009
def ridgeSupport776_suffix_007 : List Nat := ridgeSupport776_007 ++ ridgeSupport776_suffix_008
def ridgeSupport776_suffix_006 : List Nat := ridgeSupport776_006 ++ ridgeSupport776_suffix_007
def ridgeSupport776_suffix_005 : List Nat := ridgeSupport776_005 ++ ridgeSupport776_suffix_006
def ridgeSupport776_suffix_004 : List Nat := ridgeSupport776_004 ++ ridgeSupport776_suffix_005
def ridgeSupport776_suffix_003 : List Nat := ridgeSupport776_003 ++ ridgeSupport776_suffix_004
def ridgeSupport776_suffix_002 : List Nat := ridgeSupport776_002 ++ ridgeSupport776_suffix_003
def ridgeSupport776_suffix_001 : List Nat := ridgeSupport776_001 ++ ridgeSupport776_suffix_002
def ridgeSupport776_suffix_000 : List Nat := ridgeSupport776_000 ++ ridgeSupport776_suffix_001
theorem ridgeSupport776_source : candidateSupports 776 =
    (PackedRawNatGrowth.readList 13 404 ridgeSupport776_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
