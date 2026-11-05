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
def ridgeSupport648_000 : List Nat := [29,53,73,103,109,112,114,250,251,252,253,260,261,406,407,408,409,416,417,536,537,538,541,542,547,548,553,555,577,579,581,583]
def ridgeSupport648_001 : List Nat := [585,590,591,593,596,827,828,831,832,835,836,873,874,875,878,879,884,885,890,892,914,916,918,920,922,927,928,930,933,1092,1093,1096]
def ridgeSupport648_002 : List Nat := [1097,1100,1101,1138,1139,1140,1143,1144,1149,1150,1155,1157,1179,1181,1183,1185,1187,1192,1193,1195,1198,1515,1516,1517,1518,1519,1520,1558,1562,1563,1564,1565]
def ridgeSupport648_003 : List Nat := [1567,1568,1575,1577,1601,1603,1605,1606,1608,1610,1611,1615,1620,1642,1646,1647,1648,1649,1651,1652,1659,1661,1685,1687,1689,1690,1692,1694,1695,1699,1704,1705]
def ridgeSupport648_004 : List Nat := [1707,1709,1711,1712,1714,1716,1717,1721,1723,1728,1729,2872,2877,2886,2888,2954,2955,2964,2965,2970,2971,2974,2976,2980,2981,2987,2990,3002,3003,3012,3013,3040]
def ridgeSupport648_005 : List Nat := [3045,3050,3051,3054,3056,3060,3061,3066,3067,3076,3077,3090,3091,3100,3101,3112,3117,3126,3128,3194,3195,3204,3205,3210,3211,3214,3216,3220,3221,3227,3230,3242]
def ridgeSupport648_006 : List Nat := [3243,3252,3253,3280,3285,3290,3291,3294,3296,3300,3301,3306,3307,3316,3317,3330,3331,3340,3341,3432,3434,3444,3446,3460,3461,3472,3473,3574,3579,3586,3591,3606]
def ridgeSupport648_007 : List Nat := [3607,3618,3619,3640,3645,3654,3656,3722,3723,3732,3733,3738,3739,3742,3744,3748,3749,3755,3758,3770,3771,3780,3781,3808,3813,3818,3819,3822,3824,3828,3829,3834]
def ridgeSupport648_008 : List Nat := [3835,3844,3845,3858,3859,3868,3869,3960,3962,3972,3974,3988,3989,4000,4001,4102,4107,4114,4119,4134,4135,4146,4147,4960,4965,4974,4976,4994,4995,5004,5005,5042]
def ridgeSupport648_009 : List Nat := [5043,5052,5053,5058,5059,5062,5064,5068,5069,5075,5078,5080,5085,5090,5091,5094,5096,5100,5101,5138,5139,5148,5149,5162,5163,5172,5173,5250,5252,5280,5282,5290]
def ridgeSupport648_010 : List Nat := [5291,5308,5309,5392,5397,5422,5427,5436,5437,5454,5455,5728,5733,5742,5744,5762,5763,5772,5773,5810,5811,5820,5821,5826,5827,5830,5832,5836,5837,5843,5846,5848]
def ridgeSupport648_011 : List Nat := [5853,5858,5859,5862,5864,5868,5869,5906,5907,5916,5917,5930,5931,5940,5941,6018,6020,6048,6050,6058,6059,6076,6077,6160,6165,6190,6195,6204,6205,6222,6223,6846]
def ridgeSupport648_012 : List Nat := [6848,6858,6860,6886,6887,6898,6899,6988,6993,7000,7005,7032,7033,7044,7045,7206,7207,7242,7243,7302,7303,7464,7465,7560,7561,7898,7899,7908,7909,7913,7914,7915]
def ridgeSupport648_013 : List Nat := [7916,7921,7922,7946,7947,7956,7957,7961,7962,7963,7964,7969,7970,8002,8003,8005,8007,8039,8040,8041,8042,8066,8067,8076,8077,8081,8082,8083,8084,8089,8090,8122]
def ridgeSupport648_014 : List Nat := [8123,8125,8127,8159,8160,8161,8162,8350,8352,8363,8366,8381,8382,8383,8384,8389,8390,8416,8417,8419,8421,8453,8454,8455,8456,8518,8520,8531,8534,8549,8550,8551]
def ridgeSupport648_015 : List Nat := [8552,8557,8558,8584,8585,8587,8589,8621,8622,8623,8624,8782,8783,8785,8787,8819,8820,8821,8822]
def ridgeSupport648_code : Nat := 0x227689d627489ce253894624f893a1b086be1ae86b618d862e189862216e85b6168859e1668596156854e148851a108841e10684160e5838e0e183820c683160c082fe0be82f60ae82ae0a08279fe27f85fe07f7dfbf7ef5fbb7ee9f9a7e65f947e4df927e45f8d7e31f837e09f6a7da5f687d9df477d15f437d09f227c85f1c7c6df1a7c65f157c51f0b7c29ef27bc5eec7badeea7ba5ee57b91edb7b69d897621d2974a1c877219c4b7129c277099b856e11b796de1b5d6d61b516d31af36bc9ae76b99acc6b29ac06af984f613983d60f183360b981560417bd5ef17ab5ea97a25e817845e097355cd172b5ca971d5c717135c496ed5bb16e85b996e35b896dd5b616d65b4d6cd5b316c85b196c35b096bd5af16b35ac968d5a316835a0967059b9665598154f553953d54f153354b951554414bd52f14ab52a94a25281484520943550d142b50a941d507141350493ed4fb13e84f993e34f893dd4f613d64f4d3cd4f313c84f193c34f093bd4ef13b34ec938d4e313834e093704db93654d8103340c90274099017404900b4018fa13e80f953e50f863e10f7a3de0f1d3c70f133c48f053c10efb3be8ef53bd0ef03bb8eeb3ba8ee53b80ec53b10ebb3ae8eae3aacea53a90ea03a78e9b3a68e953a50e8b3a28e483918e3d38e0e233888e173858e073808dfb37d8d913640d853610d7635d0d6a35a0d0d3430d033408cf533d0ceb33a8ce53390ce03378cdb3368cd53340cb532d0cab32a8c9e326cc953250c903238c8b3228c853210c7b31e8c3830d8c2d30a0c1d3070c133048c053010bfb2fe8bf52fd0bf02fb8beb2fa8be52f80bc52f10bbb2ee8bae2eacba52e90ba02e78b9b2e68b952e50b8b2e28b482d18b3d2ce06c11b006bb1ae46b51ad06b21ac06af1ab46ab1aa46a81a8c69f1a7869c1a686991a5c69519f467b19d067319c467019bc66e19a8654193c64b19286481918645190c64118a4627188061f187461c186c61a18585f017bc5ee17b45ec17ac4ae12ac4a912a04a3128449f127449b121448311f847d11e047711d047311c844d1130449112044511103a50e883a00e7c39a0e603960e503920df037a0dd43740dbc36e0dac36a0da43440d0c3400cfc33c0cec254094424f0938249091c245090c24108ac2290890223087821d086821908601a106801990660197065810504100fd03f00fb03e807201c006d019c04900d401d
def ridgeSupport648_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport648_code
def ridgeSupport648_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport648_code
def ridgeSupport648_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport648_code
def ridgeSupport648_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport648_code
def ridgeSupport648_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport648_code
def ridgeSupport648_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport648_code
def ridgeSupport648_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport648_code
def ridgeSupport648_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport648_code
def ridgeSupport648_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport648_code
def ridgeSupport648_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport648_code
def ridgeSupport648_rest_010 : Nat := PackedRawNatGrowth.drop 4480 ridgeSupport648_code
def ridgeSupport648_rest_011 : Nat := PackedRawNatGrowth.drop 4928 ridgeSupport648_code
def ridgeSupport648_rest_012 : Nat := PackedRawNatGrowth.drop 5376 ridgeSupport648_code
def ridgeSupport648_rest_013 : Nat := PackedRawNatGrowth.drop 5824 ridgeSupport648_code
def ridgeSupport648_rest_014 : Nat := PackedRawNatGrowth.drop 6272 ridgeSupport648_code
def ridgeSupport648_rest_015 : Nat := PackedRawNatGrowth.drop 6720 ridgeSupport648_code
def ridgeSupport648_rest_016 : Nat := PackedRawNatGrowth.drop 6986 ridgeSupport648_code
def ridgeSupport648_suffix_016 : List Nat := []
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
    (PackedRawNatGrowth.readList 14 499 ridgeSupport648_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
