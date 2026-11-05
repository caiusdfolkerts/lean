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
def ridgeSupport584_000 : List Nat := [23,43,73,79,84,85,198,199,200,201,208,209,439,441,443,445,447,452,453,455,458,460,462,464,466,468,473,474,476,479,639,640]
def ridgeSupport584_001 : List Nat := [643,644,647,648,708,710,712,714,716,721,722,724,727,729,731,733,735,737,742,743,745,748,1015,1016,1017,1018,1019,1020,1083,1085,1087,1088]
def ridgeSupport584_002 : List Nat := [1090,1092,1093,1097,1102,1104,1106,1108,1109,1111,1113,1114,1118,1123,1167,1169,1171,1172,1174,1176,1177,1181,1186,1188,1190,1192,1193,1195,1197,1198,1202,1207]
def ridgeSupport584_003 : List Nat := [1230,1231,1233,1234,1237,1238,1239,1241,1242,1244,1251,1252,2402,2407,2408,2413,2472,2473,2486,2487,2492,2494,2500,2501,2506,2507,2513,2515,2520,2521,2534,2535]
def ridgeSupport584_004 : List Nat := [2568,2569,2570,2575,2576,2581,2582,2583,2596,2597,2602,2603,2620,2621,2626,2627,2642,2647,2648,2653,2712,2713,2726,2727,2732,2734,2740,2741,2746,2747,2753,2755]
def ridgeSupport584_005 : List Nat := [2760,2761,2774,2775,2808,2809,2810,2815,2816,2821,2822,2823,2836,2837,2842,2843,2860,2861,2866,2867,2954,2959,2966,2971,2986,2987,2998,2999,3026,3031,3038,3043]
def ridgeSupport584_006 : List Nat := [3058,3059,3070,3071,3434,3439,3440,3445,3456,3457,3470,3471,3504,3505,3518,3519,3524,3526,3532,3533,3538,3539,3545,3547,3552,3553,3554,3559,3560,3565,3566,3567]
def ridgeSupport584_007 : List Nat := [3600,3601,3614,3615,3624,3625,3638,3639,3676,3677,3688,3689,4010,4015,4016,4021,4032,4033,4046,4047,4080,4081,4094,4095,4100,4102,4108,4109,4114,4115,4121,4123]
def ridgeSupport584_008 : List Nat := [4128,4129,4130,4135,4136,4141,4142,4143,4176,4177,4190,4191,4200,4201,4214,4215,4292,4297,4322,4327,4336,4337,4354,4355,4364,4369,4394,4399,4408,4409,4426,4427]
def ridgeSupport584_009 : List Nat := [4928,4933,4940,4945,4972,4973,4984,4985,5000,5005,5012,5017,5044,5045,5056,5057,5744,5746,5753,5755,5768,5770,5776,5777,5782,5783,5789,5791,5796,5797,5810,5811]
def ridgeSupport584_010 : List Nat := [5824,5825,5830,5831,5844,5845,5846,5851,5852,5857,5858,5859,5867,5869,5870,5872,5876,5878,5885,5887,5900,5902,5908,5909,5914,5915,5921,5923,5928,5929,5942,5943]
def ridgeSupport584_011 : List Nat := [5956,5957,5962,5963,5976,5977,5978,5983,5984,5989,5990,5991,5999,6001,6002,6004,6064,6065,6068,6073,6076,6077,6080,6085,6100,6101,6112,6113,6118,6119,6122,6127]
def ridgeSupport584_012 : List Nat := [6130,6131,6134,6139,6154,6155,6166,6167,6368,6370,6377,6379,6384,6385,6398,6399,6404,6406,6412,6413,6418,6419,6425,6427,6432,6433,6434,6439,6440,6445,6446,6447]
def ridgeSupport584_013 : List Nat := [6460,6461,6466,6467,6477,6478,6485,6486,6496,6497,6656,6658,6665,6667,6672,6673,6686,6687,6692,6694,6700,6701,6706,6707,6713,6715,6720,6721,6722,6727,6728,6733]
def ridgeSupport584_014 : List Nat := [6734,6735,6748,6749,6754,6755,6765,6766,6773,6774,6830,6835,6838,6839,6856,6857,6860,6865,6874,6875,6879,6882,6884,6889,6892,6893,6910,6911,6914,6919,6928,6929]
def ridgeSupport584_015 : List Nat := [6933,6936,7214,7219,7222,7223,7226,7231,7234,7235,7239,7242,7245,7248,7268,7273,7276,7277,7280,7285,7288,7289,7293,7296,7299,7302,7424,7426,7433,7435,7436,7438]
def ridgeSupport584_016 : List Nat := [7445,7447,7456,7457,7462,7463,7485,7487,7492,7494,7509,7511,7516,7518,7526,7531,7532,7537,7563,7566,7569,7572,7742,7743,7778,7779,7872,7873,7968,7969]
def ridgeSupport584_code : Nat := 0x3e43f20f60fb03cc7e62f1ff8fbb29d91ec7762fae3d6ceb5f59babdd5ceabf557a8dd44e9ff4f7a4fd26e90f483a2fd15e877433a17d09e81740390dc83e4071f78f3c78e3af1c38dbc6ce34f1938a1c4de25711f887c42e1ff0eb86fc36e19f0bb631b15d88ec4360fb02d7febfb5dbaecd74eb935c5adfd6deb6b5a3accd64eb2356fab6d59eabb4eda75d3769b74c7a62d2ee97349fa4ed26e92348fa42d20e903477a39d19e8cb45ba2cd13689343fa1ed08e843417a09d0168032c3960cab655729d94dca1e50b27b93cc97e4bb25b928c93e48b243920c8de467227912c86e43320d904c7fe3fb1e38f0c75e3a71c58e0c0be05b01780abfddfdafe77f2bf7dfaafcf7e6bf0df82fab7d4be2df02f7b7bcbdcded2f637b0bba5dcaee376fbb3dd9aecb760bafdd6aeb3758ba5dd2ae8b744b9bdcdae53728b91dc86e3771ab8adc52e1d70cb7fdbf6ded6f4b785bbaddb6ebb71db8adc36dcb6ddb5adab6d4b63db1ad836c0b59dacad4b6a4b4fda76d2f696b48da42d15688b3dd9e6ce56709e0cf0276b3b49ccce5271b3889bccde26db36c9a8cd3268b3408a5c52a273138897c4aa22310c881c40a1e30f0873c38a1930c483bc1da0d306882fc17a0a3050817c0ba05b028813c08a04302080dc066027012806c03200d0047ffbff9fe2ff07e7bf39f82fc07dabec1f5efaa734b9a1cbae5c71bb8d9c52e2870fb879c22e106f7b7b9bdade86f3b789bc2de06edb765ba6dd26e6b731b8cdc46dfb6f9b62db06c7b639b02d806bab5c1aded6a5ffaff97e6bf25f1af797aebd25dbaed9756baa5cdae5971eb8a599acc965ab2c58dac6962ab14583ac1960ab0057fabe95f2af856bab59592ac8561ab05576aba55aaad155caac553aa99532a9852ea9614aea52521a90947aa3c515a8a944aa2450ba85942aa10507a829412a084f3a7993b29d84e9a7453969ca4e2a71137c9bc4dba6d93529a84b6a5a12ce962272138c9b84da26c935c9ac4d5269134499e4ce25b92c895c4ad25592a49504a6252128893a49924c1258928493248923c8c645e22d11648ae45522a11488a044e224911488844222010fc87a43b1fe0fec7f43f91fc0fdc5d82e91738b985c22df16e8b6c5b22d716a0b485a22cc1650b2058c2c41440a1c50828314009fc3be1dc0ed07643a81d20e807383981ca0e387143881bf0de86ec3721b706883401920c806383180aa0540278124056017
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
def ridgeSupport584_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport584_code
def ridgeSupport584_rest_012 : Nat := PackedRawNatGrowth.drop 4992 ridgeSupport584_code
def ridgeSupport584_rest_013 : Nat := PackedRawNatGrowth.drop 5408 ridgeSupport584_code
def ridgeSupport584_rest_014 : Nat := PackedRawNatGrowth.drop 5824 ridgeSupport584_code
def ridgeSupport584_rest_015 : Nat := PackedRawNatGrowth.drop 6240 ridgeSupport584_code
def ridgeSupport584_rest_016 : Nat := PackedRawNatGrowth.drop 6656 ridgeSupport584_code
def ridgeSupport584_rest_017 : Nat := PackedRawNatGrowth.drop 7046 ridgeSupport584_code
def ridgeSupport584_suffix_017 : List Nat := []
def ridgeSupport584_suffix_016 : List Nat := ridgeSupport584_016 ++ ridgeSupport584_suffix_017
def ridgeSupport584_suffix_015 : List Nat := ridgeSupport584_015 ++ ridgeSupport584_suffix_016
def ridgeSupport584_suffix_014 : List Nat := ridgeSupport584_014 ++ ridgeSupport584_suffix_015
def ridgeSupport584_suffix_013 : List Nat := ridgeSupport584_013 ++ ridgeSupport584_suffix_014
def ridgeSupport584_suffix_012 : List Nat := ridgeSupport584_012 ++ ridgeSupport584_suffix_013
def ridgeSupport584_suffix_011 : List Nat := ridgeSupport584_011 ++ ridgeSupport584_suffix_012
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
    (PackedRawNatGrowth.readList 13 542 ridgeSupport584_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
