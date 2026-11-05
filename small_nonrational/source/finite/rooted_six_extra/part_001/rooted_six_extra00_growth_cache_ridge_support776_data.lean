module
prelude
public import RootedSixExtra00GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport776_000 : List Nat := [30,54,74,104,110,113,114,262,263,264,265,272,273,418,419,420,421,428,429,557,558,559,562,563,568,569,574,576,578,579,580,583]
def ridgeSupport776_001 : List Nat := [584,589,590,595,597,839,840,843,844,847,848,894,895,896,899,900,905,906,911,913,915,916,917,920,921,926,927,932,934,1104,1105,1108]
def ridgeSupport776_002 : List Nat := [1109,1112,1113,1159,1160,1161,1164,1165,1170,1171,1176,1178,1180,1181,1182,1185,1186,1191,1192,1197,1199,1527,1528,1529,1530,1531,1532,1579,1583,1584,1585,1586]
def ridgeSupport776_003 : List Nat := [1588,1589,1596,1598,1600,1604,1605,1606,1607,1609,1610,1617,1619,1663,1667,1668,1669,1670,1672,1673,1680,1682,1684,1688,1689,1690,1691,1693,1694,1701,1703,1705]
def ridgeSupport776_004 : List Nat := [1706,1710,1711,1712,1713,1715,1716,1724,1726,1727,1729,2874,2876,2880,2882,2960,2961,2966,2967,2968,2969,2974,2975,2980,2982,2986,2988,3008,3009,3014,3015,3042]
def ridgeSupport776_005 : List Nat := [3044,3048,3050,3056,3057,3062,3063,3064,3065,3070,3071,3088,3089,3094,3095,3114,3116,3120,3122,3200,3201,3206,3207,3208,3209,3214,3215,3220,3222,3226,3228,3248]
def ridgeSupport776_006 : List Nat := [3249,3254,3255,3282,3284,3288,3290,3296,3297,3302,3303,3304,3305,3310,3311,3328,3329,3334,3335,3504,3506,3516,3518,3532,3533,3544,3545,3576,3578,3588,3590,3604]
def ridgeSupport776_007 : List Nat := [3605,3616,3617,3642,3644,3648,3650,3728,3729,3734,3735,3736,3737,3742,3743,3748,3750,3754,3756,3776,3777,3782,3783,3810,3812,3816,3818,3824,3825,3830,3831,3832]
def ridgeSupport776_008 : List Nat := [3833,3838,3839,3856,3857,3862,3863,4032,4034,4044,4046,4060,4061,4072,4073,4104,4106,4116,4118,4132,4133,4144,4145,4962,4964,4968,4970,5000,5001,5006,5007,5048]
def ridgeSupport776_009 : List Nat := [5049,5054,5055,5056,5057,5062,5063,5068,5070,5074,5076,5082,5084,5088,5090,5096,5097,5102,5103,5144,5145,5150,5151,5168,5169,5174,5175,5322,5324,5352,5354,5362]
def ridgeSupport776_010 : List Nat := [5363,5380,5381,5394,5396,5424,5426,5434,5435,5452,5453,5730,5732,5736,5738,5768,5769,5774,5775,5816,5817,5822,5823,5824,5825,5830,5831,5836,5838,5842,5844,5850]
def ridgeSupport776_011 : List Nat := [5852,5856,5858,5864,5865,5870,5871,5912,5913,5918,5919,5936,5937,5942,5943,6090,6092,6120,6122,6130,6131,6148,6149,6162,6164,6192,6194,6202,6203,6220,6221,6918]
def ridgeSupport776_012 : List Nat := [6920,6930,6932,6958,6959,6970,6971,6990,6992,7002,7004,7030,7031,7042,7043,7204,7205,7240,7241,7300,7301,7466,7467,7562,7563,7904,7905,7910,7911,7912,7913,7915]
def ridgeSupport776_013 : List Nat := [7917,7918,7919,7952,7953,7958,7959,7960,7961,7963,7965,7966,7967,8020,8021,8023,8025,8038,8039,8041,8043,8072,8073,8078,8079,8080,8081,8083,8085,8086,8087,8140]
def ridgeSupport776_014 : List Nat := [8141,8143,8145,8158,8159,8161,8163,8356,8358,8362,8364,8380,8381,8383,8385,8386,8387,8434,8435,8437,8439,8452,8453,8455,8457,8524,8526,8530,8532,8548,8549,8551]
def ridgeSupport776_015 : List Nat := [8553,8554,8555,8602,8603,8605,8607,8620,8621,8623,8625,8800,8801,8803,8805,8818,8819,8821,8823]
def ridgeSupport776_code : Nat := 0x227789d627389ca265898e26189821b186be1ad86b219f867619b866a16b85aa169859e1658592154854a14e8532109841e10584120f783d60f383ca0c3830a0c182fe0bd82f20ac82aa0a68291fe37f85fdf7f79fd17f3dfcd7f31f977e59f957e4df917e41f8f7e39f897e21f6b7da5f677d99f597d5df557d51f1f7c79f1d7c6df197c61f177c59f117c41eef7bb9eed7badee97ba1ee77b99ee17b81d8b7629d2b74a9c857211c497121c257091b836e09b776dd9b5c6d69b506d39b3b6ce9b2f6cb9b146c49b086c1984d613183b60e983260c1814604980560117f35fc97ea5fa17cc5f297375cd97315cc171f5c797195c616ef5bb96e95ba16e25b816dc5b696d45b496ce5b316c75b196c15b016bf5af96b95ae168f5a396895a2166a59a1664598954d553153b54e953254c1514544950554114f353c94ea53a14cc532943750d943150c141f507941950613ef4fb93e94fa13e24f813dc4f693d44f493ce4f313c74f193c14f013bf4ef93b94ee138f4e393894e2136a4da13644d8903140c10254091016405100a4020fe93fa0fdd3f70fce3f30fc23f00f173c58f113c40eff3bf8ef93be0ef73bd8ef13bc0eea3ba0ee43b88ec73b18ec13b00eac3aa8ea63a90e9f3a78e993a60e973a58e913a40e423900e3c38e8e213880e153850e063810dfa37e0dd93760dcd3730dbe36f0db236c0d073418d013400cef33b8ce933a0ce73398ce13380cda3360cd43348cb732d8cb132c0c9c3268c963250c8f3238c893220c873218c813200c3230c0c2c30a8c173058c113040bff2ff8bf92fe0bf72fd8bf12fc0bea2fa0be42f88bc72f18bc12f00bac2ea8ba62e90b9f2e78b992e60b972e58b912e40b422d00b3c2ce86c11afc6be1af06b41acc6b11ac06af1ab86aa1aa46a71a9469e1a7469b1a686991a606941a486901a246881a186851a1068319fc653194464a19246471918645191064018f863c18d463418c863118c062f18ac5fc17ec5fa17e45f817dc4af12b44a8129c4a2128449e127449c1268498124c492123448c1224488121c4591160455115045111403a60e9039f0e783990e603950e503930e4438f0e283890e103830e0037f0df83500d3c34c0d2c3480d1c255094c24e0934248091c244090c242090023e08e423808cc23208bc22e08b41ad06b01a506901a3068811104401090420107041807201c406e01a004a00d801e
def ridgeSupport776_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport776_code
def ridgeSupport776_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport776_code
def ridgeSupport776_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport776_code
def ridgeSupport776_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport776_code
def ridgeSupport776_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport776_code
def ridgeSupport776_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport776_code
def ridgeSupport776_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport776_code
def ridgeSupport776_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport776_code
def ridgeSupport776_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport776_code
def ridgeSupport776_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport776_code
def ridgeSupport776_rest_010 : Nat := PackedRawNatGrowth.drop 4480 ridgeSupport776_code
def ridgeSupport776_rest_011 : Nat := PackedRawNatGrowth.drop 4928 ridgeSupport776_code
def ridgeSupport776_rest_012 : Nat := PackedRawNatGrowth.drop 5376 ridgeSupport776_code
def ridgeSupport776_rest_013 : Nat := PackedRawNatGrowth.drop 5824 ridgeSupport776_code
def ridgeSupport776_rest_014 : Nat := PackedRawNatGrowth.drop 6272 ridgeSupport776_code
def ridgeSupport776_rest_015 : Nat := PackedRawNatGrowth.drop 6720 ridgeSupport776_code
def ridgeSupport776_rest_016 : Nat := PackedRawNatGrowth.drop 6986 ridgeSupport776_code
def ridgeSupport776_suffix_016 : List Nat := []
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
    (PackedRawNatGrowth.readList 14 499 ridgeSupport776_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
