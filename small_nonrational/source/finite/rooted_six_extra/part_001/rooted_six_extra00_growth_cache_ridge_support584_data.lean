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
def ridgeSupport584_000 : List Nat := [27,51,71,101,107,112,113,226,227,228,229,236,237,382,383,384,385,392,393,535,537,539,541,543,548,549,551,554,556,558,560,562]
def ridgeSupport584_001 : List Nat := [564,569,570,572,575,803,804,807,808,811,812,872,874,876,878,880,885,886,888,891,893,895,897,899,901,906,907,909,912,1068,1069,1072]
def ridgeSupport584_002 : List Nat := [1073,1076,1077,1137,1139,1141,1143,1145,1150,1151,1153,1156,1158,1160,1162,1164,1166,1171,1172,1174,1177,1491,1492,1493,1494,1495,1496,1559,1561,1563,1564,1566]
def ridgeSupport584_003 : List Nat := [1568,1569,1573,1578,1580,1582,1584,1585,1587,1589,1590,1594,1599,1643,1645,1647,1648,1650,1652,1653,1657,1662,1664,1666,1668,1669,1671,1673,1674,1678,1683,1706]
def ridgeSupport584_004 : List Nat := [1707,1709,1710,1713,1714,1715,1717,1718,1720,1727,1728,2878,2883,2884,2889,2948,2949,2962,2963,2968,2970,2976,2977,2982,2983,2989,2991,2996,2997,3010,3011,3044]
def ridgeSupport584_005 : List Nat := [3045,3046,3051,3052,3057,3058,3059,3072,3073,3078,3079,3096,3097,3102,3103,3118,3123,3124,3129,3188,3189,3202,3203,3208,3210,3216,3217,3222,3223,3229,3231,3236]
def ridgeSupport584_006 : List Nat := [3237,3250,3251,3284,3285,3286,3291,3292,3297,3298,3299,3312,3313,3318,3319,3336,3337,3342,3343,3430,3435,3442,3447,3462,3463,3474,3475,3502,3507,3514,3519,3534]
def ridgeSupport584_007 : List Nat := [3535,3546,3547,3646,3651,3652,3657,3716,3717,3730,3731,3736,3738,3744,3745,3750,3751,3757,3759,3764,3765,3778,3779,3812,3813,3814,3819,3820,3825,3826,3827,3840]
def ridgeSupport584_008 : List Nat := [3841,3846,3847,3864,3865,3870,3871,3958,3963,3970,3975,3990,3991,4002,4003,4030,4035,4042,4047,4062,4063,4074,4075,4966,4971,4972,4977,4988,4989,5002,5003,5036]
def ridgeSupport584_009 : List Nat := [5037,5050,5051,5056,5058,5064,5065,5070,5071,5077,5079,5084,5085,5086,5091,5092,5097,5098,5099,5132,5133,5146,5147,5156,5157,5170,5171,5248,5253,5278,5283,5292]
def ridgeSupport584_010 : List Nat := [5293,5310,5311,5320,5325,5350,5355,5364,5365,5382,5383,5734,5739,5740,5745,5756,5757,5770,5771,5804,5805,5818,5819,5824,5826,5832,5833,5838,5839,5845,5847,5852]
def ridgeSupport584_011 : List Nat := [5853,5854,5859,5860,5865,5866,5867,5900,5901,5914,5915,5924,5925,5938,5939,6016,6021,6046,6051,6060,6061,6078,6079,6088,6093,6118,6123,6132,6133,6150,6151,6844]
def ridgeSupport584_012 : List Nat := [6849,6856,6861,6888,6889,6900,6901,6916,6921,6928,6933,6960,6961,6972,6973,7210,7211,7246,7247,7306,7307,7460,7461,7556,7557,7892,7893,7906,7907,7916,7917,7919]
def ridgeSupport584_013 : List Nat := [7920,7921,7923,7940,7941,7954,7955,7964,7965,7967,7968,7969,7971,8003,8004,8005,8006,8021,8022,8023,8024,8060,8061,8074,8075,8084,8085,8087,8088,8089,8091,8123]
def ridgeSupport584_014 : List Nat := [8124,8125,8126,8141,8142,8143,8144,8344,8346,8365,8367,8384,8385,8387,8388,8389,8391,8417,8418,8419,8420,8435,8436,8437,8438,8512,8514,8533,8535,8552,8553,8555]
def ridgeSupport584_015 : List Nat := [8556,8557,8559,8585,8586,8587,8588,8603,8604,8605,8606,8783,8784,8785,8786,8801,8802,8803,8804]
def ridgeSupport584_code : Nat := 0x2264898e26289862528946250893e19e867619c866e18c862e18a862616f85b616c85ae16985a2157855614285020f683d60f483ce0e4838e0e283860c783160c4830e0c183020af82b609a8261fd07f3dfce7f35fbe7ef5fbc7eedf9b7e65f987e5df957e51f8b7e29f7d7df1f587d5df567d55f467d15f447d0df237c85f207c7df1d7c71f137c49f057c11ef37bc5ef07bbdeed7bb1ee37b89ed57b51d857611d257491c8b7229c4f7139c2b70a9b3d6cf1b316cc1b156c41b096c11af56bd1ae96ba1acd6b21ac16af180760197f55fd17eb5f997cd5f217bf5ef97ad5eb17a35e797855e017335cc97255c9171b5c6970d5c316eb5ba96e95b916e35b796dd5b716d75b556cf5b396c95b216c25b016bb5ae96ad5ab168b5a2967d59f167159b166b599950754194f553d14eb53994cd53214bf52f94ad52b14a35279485520143350c9425509141b506940d50313eb4fa93e94f913e34f793dd4f713d74f553cf4f393c94f213c24f013bb4ee93ad4eb138b4e2937d4df13714db136b4d98feb3fa8fdf3f78fcf3f28fc33ef8fa33e88f973e58f873e08f7b3dd8f1f3c78f193c60f073c18f013c00ef33bc8ef13bb0eeb3b98ee53b90ec33b08eb53ad0eaf3ab4ea73a98ea13a80e9a3a60e933a48e853a10e493910e4338f8ddb3768dcf3738dbf36e8db336b8d933648d873618d7735c8d6b3598d0f3438d093420cf733d8cf133c0ce33388ce13370cdb3358cd53350cb332c8ca53290c9f3274c973258c913240c8a3220c833208c7531d0c3930d0c3330b8c1f3078c193060c073018c013000bf32fc8bf12fb0beb2f98be52f90bc32f08bb52ed0baf2eb4ba72e98ba12e80b9a2e60b932e48b852e10b492d10b432cf86c01afc6b81ad86b51acc6b21ac46ae1ab46ab1aa86931a3868a1a246871a146841a0868019f867919d467419c867019bc66d19ac63f18e863618d463318c463018b862c18a86251884620187861c186c619185c5d8175c5d617545d4174c4991258494124c48e123048a1220486121048111fc47e11e447711d447311c443510d043110c042d10b03900e3438b0e283850e0c3810dfc37d0dec3780dd83750dc036e0db036a0da032c0cac3280c9c3240c8c23f08f023a08e423408c823008b822c08a82270894224087c21d086c219085c1890620181060017f05f80ed03b00e503900e3038807101c006b019404700cc01b
def ridgeSupport584_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport584_code
def ridgeSupport584_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport584_code
def ridgeSupport584_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport584_code
def ridgeSupport584_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport584_code
def ridgeSupport584_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport584_code
def ridgeSupport584_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport584_code
def ridgeSupport584_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport584_code
def ridgeSupport584_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport584_code
def ridgeSupport584_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport584_code
def ridgeSupport584_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport584_code
def ridgeSupport584_rest_010 : Nat := PackedRawNatGrowth.drop 4480 ridgeSupport584_code
def ridgeSupport584_rest_011 : Nat := PackedRawNatGrowth.drop 4928 ridgeSupport584_code
def ridgeSupport584_rest_012 : Nat := PackedRawNatGrowth.drop 5376 ridgeSupport584_code
def ridgeSupport584_rest_013 : Nat := PackedRawNatGrowth.drop 5824 ridgeSupport584_code
def ridgeSupport584_rest_014 : Nat := PackedRawNatGrowth.drop 6272 ridgeSupport584_code
def ridgeSupport584_rest_015 : Nat := PackedRawNatGrowth.drop 6720 ridgeSupport584_code
def ridgeSupport584_rest_016 : Nat := PackedRawNatGrowth.drop 6986 ridgeSupport584_code
def ridgeSupport584_suffix_016 : List Nat := []
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
    (PackedRawNatGrowth.readList 14 499 ridgeSupport584_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
