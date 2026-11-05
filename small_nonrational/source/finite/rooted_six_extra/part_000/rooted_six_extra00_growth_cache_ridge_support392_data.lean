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
def ridgeSupport392_000 : List Nat := [28,52,72,102,108,111,114,238,239,240,241,248,249,394,395,396,397,404,405,515,516,517,520,521,526,527,532,534,577,578,582,584]
def ridgeSupport392_001 : List Nat := [585,589,591,592,594,815,816,819,820,823,824,852,853,854,857,858,863,864,869,871,914,915,919,921,922,926,928,929,931,1080,1081,1084]
def ridgeSupport392_002 : List Nat := [1085,1088,1089,1117,1118,1119,1122,1123,1128,1129,1134,1136,1179,1180,1184,1186,1187,1191,1193,1194,1196,1503,1504,1505,1506,1507,1508,1537,1541,1542,1543,1544]
def ridgeSupport392_003 : List Nat := [1546,1547,1554,1556,1602,1603,1604,1607,1608,1609,1611,1616,1618,1621,1625,1626,1627,1628,1630,1631,1638,1640,1686,1687,1688,1691,1692,1693,1695,1700,1702,1705]
def ridgeSupport392_004 : List Nat := [1708,1709,1710,1713,1714,1715,1717,1722,1723,1725,1726,2873,2875,2892,2894,2952,2953,2958,2959,2972,2973,2975,2978,2981,2984,2986,2987,3000,3001,3006,3007,3041]
def ridgeSupport392_005 : List Nat := [3043,3048,3049,3054,3055,3060,3062,3068,3069,3082,3083,3092,3093,3106,3107,3113,3115,3132,3134,3192,3193,3198,3199,3212,3213,3215,3218,3221,3224,3226,3227,3240]
def ridgeSupport392_006 : List Nat := [3241,3246,3247,3281,3283,3288,3289,3294,3295,3300,3302,3308,3309,3322,3323,3332,3333,3346,3347,3360,3362,3372,3374,3388,3389,3400,3401,3575,3577,3587,3589,3608]
def ridgeSupport392_007 : List Nat := [3609,3620,3621,3641,3643,3660,3662,3720,3721,3726,3727,3740,3741,3743,3746,3749,3752,3754,3755,3768,3769,3774,3775,3809,3811,3816,3817,3822,3823,3828,3830,3836]
def ridgeSupport392_008 : List Nat := [3837,3850,3851,3860,3861,3874,3875,3888,3890,3900,3902,3916,3917,3928,3929,4103,4105,4115,4117,4136,4137,4148,4149,4961,4963,4980,4982,4992,4993,4998,4999,5040]
def ridgeSupport392_009 : List Nat := [5041,5046,5047,5060,5061,5063,5066,5069,5072,5074,5075,5081,5083,5088,5089,5094,5095,5100,5102,5136,5137,5142,5143,5160,5161,5166,5167,5178,5180,5208,5210,5218]
def ridgeSupport392_010 : List Nat := [5219,5236,5237,5393,5395,5423,5425,5438,5439,5456,5457,5729,5731,5748,5750,5760,5761,5766,5767,5808,5809,5814,5815,5828,5829,5831,5834,5837,5840,5842,5843,5849]
def ridgeSupport392_011 : List Nat := [5851,5856,5857,5862,5863,5868,5870,5904,5905,5910,5911,5928,5929,5934,5935,5946,5948,5976,5978,5986,5987,6004,6005,6161,6163,6191,6193,6206,6207,6224,6225,6774]
def ridgeSupport392_012 : List Nat := [6776,6786,6788,6814,6815,6826,6827,6989,6991,7001,7003,7034,7035,7046,7047,7208,7209,7244,7245,7304,7305,7462,7463,7558,7559,7896,7897,7902,7903,7912,7914,7916]
def ridgeSupport392_013 : List Nat := [7917,7920,7923,7944,7945,7950,7951,7960,7962,7964,7965,7968,7971,7984,7985,7987,7989,8038,8040,8042,8043,8064,8065,8070,8071,8080,8082,8084,8085,8088,8091,8104]
def ridgeSupport392_014 : List Nat := [8105,8107,8109,8158,8160,8162,8163,8351,8354,8357,8360,8380,8382,8384,8385,8388,8391,8398,8399,8401,8403,8452,8454,8456,8457,8519,8522,8525,8528,8548,8550,8552]
def ridgeSupport392_015 : List Nat := [8553,8556,8559,8566,8567,8569,8571,8620,8622,8624,8625,8764,8765,8767,8769,8818,8820,8822,8823]
def ridgeSupport392_code : Nat := 0x227789da27489ca24188fe23d88f21b186c21ae86b217b85e617785da16f85b216985a21668592150853614a851e109842210684120d383460cf833a0c783120c183020be82f20a882960a2827dfe37f89fe07f79fad7eadfa97ea1f9b7e61f957e51f927e41f877e19f817e01f6b7da9f687d99f357ccdf317cc1f237c81f1d7c71f1a7c61f0f7c39f097c21ef37bc1eed7bb1eea7ba1edf7b79ed97b61d877619d277499c897221c4d7131c2970a1b876e19b7b6de9b5b6d65b4f6d35aab6aa9a9f6a79a846a09a7869d9851614183f60f983160bd81360457755dd17635d8975a5d6173c5ce972f5cb97295ca17175c597115c416ee5bb16e75b996e15b816db5b656d35b496d05b356ca5b1d6c55b116b75ad96b15ac16875a196815a0167659d16635985551554153f54f953154bd513544547551d1463518945a516143c50e942f50b942950a1417505941150413ee4fb13e74f993e14f813db4f653d34f493d04f353ca4f1d3c54f113b74ed93b14ec13874e193814e013764dd13634d8503540d102940a1015404d009401cf593d60f4d3d30f3e3cf0f323cc0f233c88f153c50f0b3c28efd3bf0ef63bd0eef3bb8ee93ba0ee33b84ebf3af8eb93ae0eab3aa8ea83a94ea23a7ce9d3a70e8f3a38e893a20e4e3930e3b38e4e253890e193860e05380cdf937dcd493520d3d34f0d2e34b0d223480d133448d053410cfb33e8ced33b0ce63390cdf3378cd93360cd33344caf32b8ca932a0c9b3268c983254c92323cc8d3230c7f31f8c7931e0c3e30f0c2b30a4c233088c153050c0b3028bfd2ff0bf62fd0bef2fb8be92fa0be32f84bbf2ef8bb92ee0bab2ea8ba82e94ba22e7cb9d2e70b8f2e38b892e20b4e2d30b3b2ce46be1af46bb1ae86b51acc6b21ac46ae1ab46ac1aa46a61a9069f1a7469c1a6c6981a5c69619a0666197c65e197065b19686591954652194064b1924648191c644190c6421850612182c60a1820607181860518045e4178c5e217845e0177c4ac12a84a9129c4a312884a0127049b11c046e11a4468118c462117c45e1174441110043d10f043910e03a30e843a00e7839a0e643970e4c3920d9c3650d8035f0d683590d583550d503380cdc3340ccc3300cbc252094024f0934249092024609082410858214083c20e08242080814204080c195065018d063018b06280f903e00f103c00ef03b807201bc06c019804800d001c
def ridgeSupport392_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport392_code
def ridgeSupport392_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport392_code
def ridgeSupport392_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport392_code
def ridgeSupport392_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport392_code
def ridgeSupport392_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport392_code
def ridgeSupport392_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport392_code
def ridgeSupport392_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport392_code
def ridgeSupport392_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport392_code
def ridgeSupport392_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport392_code
def ridgeSupport392_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport392_code
def ridgeSupport392_rest_010 : Nat := PackedRawNatGrowth.drop 4480 ridgeSupport392_code
def ridgeSupport392_rest_011 : Nat := PackedRawNatGrowth.drop 4928 ridgeSupport392_code
def ridgeSupport392_rest_012 : Nat := PackedRawNatGrowth.drop 5376 ridgeSupport392_code
def ridgeSupport392_rest_013 : Nat := PackedRawNatGrowth.drop 5824 ridgeSupport392_code
def ridgeSupport392_rest_014 : Nat := PackedRawNatGrowth.drop 6272 ridgeSupport392_code
def ridgeSupport392_rest_015 : Nat := PackedRawNatGrowth.drop 6720 ridgeSupport392_code
def ridgeSupport392_rest_016 : Nat := PackedRawNatGrowth.drop 6986 ridgeSupport392_code
def ridgeSupport392_suffix_016 : List Nat := []
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
    (PackedRawNatGrowth.readList 14 499 ridgeSupport392_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
