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
def ridgeSupport776_000 : List Nat := [26,46,76,82,85,86,234,235,236,237,244,245,461,462,463,466,467,472,473,478,480,482,483,484,487,488,493,494,499,501,675,676]
def ridgeSupport776_001 : List Nat := [679,680,683,684,730,731,732,735,736,741,742,747,749,751,752,753,756,757,762,763,768,770,1051,1052,1053,1054,1055,1056,1103,1107,1108,1109]
def ridgeSupport776_002 : List Nat := [1110,1112,1113,1120,1122,1124,1128,1129,1130,1131,1133,1134,1141,1143,1187,1191,1192,1193,1194,1196,1197,1204,1206,1208,1212,1213,1214,1215,1217,1218,1225,1227]
def ridgeSupport776_003 : List Nat := [1229,1230,1234,1235,1236,1237,1239,1240,1248,1250,1251,1253,2398,2400,2404,2406,2484,2485,2490,2491,2492,2493,2498,2499,2504,2506,2510,2512,2532,2533,2538,2539]
def ridgeSupport776_004 : List Nat := [2566,2568,2572,2574,2580,2581,2586,2587,2588,2589,2594,2595,2612,2613,2618,2619,2638,2640,2644,2646,2724,2725,2730,2731,2732,2733,2738,2739,2744,2746,2750,2752]
def ridgeSupport776_005 : List Nat := [2772,2773,2778,2779,2806,2808,2812,2814,2820,2821,2826,2827,2828,2829,2834,2835,2852,2853,2858,2859,3028,3030,3040,3042,3056,3057,3068,3069,3100,3102,3112,3114]
def ridgeSupport776_006 : List Nat := [3128,3129,3140,3141,3430,3432,3436,3438,3468,3469,3474,3475,3516,3517,3522,3523,3524,3525,3530,3531,3536,3538,3542,3544,3550,3552,3556,3558,3564,3565,3570,3571]
def ridgeSupport776_007 : List Nat := [3612,3613,3618,3619,3636,3637,3642,3643,3724,3725,3736,3737,4006,4008,4012,4014,4044,4045,4050,4051,4092,4093,4098,4099,4100,4101,4106,4107,4112,4114,4118,4120]
def ridgeSupport776_008 : List Nat := [4126,4128,4132,4134,4140,4141,4146,4147,4188,4189,4194,4195,4212,4213,4218,4219,4366,4368,4396,4398,4406,4407,4424,4425,4438,4440,4468,4470,4478,4479,4496,4497]
def ridgeSupport776_009 : List Nat := [5002,5004,5014,5016,5042,5043,5054,5055,5074,5076,5086,5088,5114,5115,5126,5127,5746,5748,5750,5752,5768,5769,5774,5775,5780,5782,5786,5788,5808,5809,5814,5815]
def ridgeSupport776_010 : List Nat := [5816,5817,5822,5823,5842,5844,5848,5850,5856,5857,5862,5863,5864,5865,5867,5868,5878,5880,5882,5884,5900,5901,5906,5907,5912,5914,5918,5920,5940,5941,5946,5947]
def ridgeSupport776_011 : List Nat := [5948,5949,5954,5955,5974,5976,5980,5982,5988,5989,5994,5995,5996,5997,5999,6000,6116,6117,6124,6126,6128,6129,6136,6138,6152,6153,6164,6165,6170,6171,6178,6180]
def ridgeSupport776_012 : List Nat := [6182,6183,6190,6192,6206,6207,6218,6219,6370,6372,6374,6376,6396,6397,6402,6403,6404,6405,6410,6411,6416,6418,6422,6424,6430,6432,6436,6438,6444,6445,6450,6451]
def ridgeSupport776_013 : List Nat := [6452,6453,6458,6459,6483,6484,6486,6487,6508,6509,6658,6660,6662,6664,6684,6685,6690,6691,6692,6693,6698,6699,6704,6706,6710,6712,6718,6720,6724,6726,6732,6733]
def ridgeSupport776_014 : List Nat := [6738,6739,6740,6741,6746,6747,6771,6772,6774,6775,6886,6888,6890,6891,6908,6909,6916,6918,6926,6927,6935,6937,6940,6942,6944,6945,6962,6963,6970,6972,6980,6981]
def ridgeSupport776_015 : List Nat := [6989,6991,7270,7272,7274,7275,7282,7284,7286,7287,7295,7297,7301,7303,7324,7326,7328,7329,7336,7338,7340,7341,7349,7351,7355,7357,7426,7428,7430,7432,7438,7440]
def ridgeSupport776_016 : List Nat := [7442,7444,7460,7461,7466,7467,7487,7489,7491,7493,7511,7513,7515,7517,7534,7536,7540,7542,7571,7573,7577,7579,7736,7737,7772,7773,7878,7879,7974,7975]
def ridgeSupport776_code : Nat := 0x3e4ff26f63fb1bcbbe5cf1cf8e3b37d99ecaf64faedd74eb875bbabbd5beacf55fa8bd43ea0f4ffa57d2ae92f493a29d12e88743ba11d06e82740b97bcbbe5bf2d795bcace5572a3943ca0e4f727390fc85e40f1ff8efc76e3a71cb8d7c6ae34719b69fb4dda2ed13679b3ad99eccb643b20d8f6c73633b17d87ec3b60db04d7eebf35d7aead746b9b4efa76d3a69cf4b7a5ad2ae9534a7a52d26e93348da44d2068fb471a36d1968c3457a2ad12e893447a22d0ee873411a06d02680b2db96ccabe55b2a9953c9de4eb26b934c99e4cb25b92cc93649324191ec8c645b225910c85e42b20b904c81e40b1fb8fcc74639b1c98e2c25e12b07f83ec1860bb04f826c12608b03781ac0ae053013808bfd5fe2fe37f0bf75fb2fcb7e4bb85dbeedb76cbb5ddaaecb764baf5d72eb1756ba1dd0ae7b73cb9ddceae6b734b905c7ae35718b89dc4ae1b70cb7e5beadf16f6b765baedd36e8b73db9adc36e0b6d5b62da96d2b5fdafad736b8b5bdadad636b0b4e5a6ad2d694b47da3ad13688b3c59dace9672a03d01a7f73fa9f04f7a7a93d29dfcefa7673b29cc4e5a71938a8c8c6422ff17e8bb45d22b11568a4c52226f13689744b222110e83dc1ea0eb074831c18a0bb05c819c0ca05b02c813409204101e80c405a025010805c02a00b004801c009ffaffc7e9bf49f9afcc7d73eb1f50fa674cba61d1ae8c71db8e9c6ae34711b889c3ae1c6f9b7c9bdadec6f33791bc0dde6ec3759ba4dd06e5b729b8adc46e1b709b7adbc6c9b649b1ad8c6b735b1ad0d66622b111872c3861530a183cc1c5feaff17e2bf05f12f817acbd4595aca964ab24589ac4961ab0c585ac2960ab0457f2bf15f0af656dab695aaad45602af9574ab8559aac955aaac555aaa954aaa452b29514a0a4e51da8e946aa34511a88943aa1c50da86942aa145072831410a064f5a7a93ca9e44e827393949c84e1a70937a9bc4dda6e936a9b44b325912c095e272938c9c44e026c135c9aa4d4269934899c4cd26593249844c125f92f897a4bc25c12d89684ad25612a89524a8253928c8ee47523711b48d646a23491a08c846223011648b045622a91508a644f210107c83c41d20e106c60430017d8be85ea2f41788bc05de2ed1758b985ca2e016f8b705b62da1560aac5502a71520a8c3ea1f30f707b43d01e70f2078c3c41e00ef07643b01d30e9073c39c1cd07a83d01da0ec07583a80ac055029013005c01a
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
def ridgeSupport776_rest_013 : Nat := PackedRawNatGrowth.drop 5408 ridgeSupport776_code
def ridgeSupport776_rest_014 : Nat := PackedRawNatGrowth.drop 5824 ridgeSupport776_code
def ridgeSupport776_rest_015 : Nat := PackedRawNatGrowth.drop 6240 ridgeSupport776_code
def ridgeSupport776_rest_016 : Nat := PackedRawNatGrowth.drop 6656 ridgeSupport776_code
def ridgeSupport776_rest_017 : Nat := PackedRawNatGrowth.drop 7046 ridgeSupport776_code
def ridgeSupport776_suffix_017 : List Nat := []
def ridgeSupport776_suffix_016 : List Nat := ridgeSupport776_016 ++ ridgeSupport776_suffix_017
def ridgeSupport776_suffix_015 : List Nat := ridgeSupport776_015 ++ ridgeSupport776_suffix_016
def ridgeSupport776_suffix_014 : List Nat := ridgeSupport776_014 ++ ridgeSupport776_suffix_015
def ridgeSupport776_suffix_013 : List Nat := ridgeSupport776_013 ++ ridgeSupport776_suffix_014
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
    (PackedRawNatGrowth.readList 13 542 ridgeSupport776_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
