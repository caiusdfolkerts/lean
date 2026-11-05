module
prelude
public import RootedSixBase01GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport706_000 : List Nat := [290,291,292,714,715,716,802,803,804,886,887,888,956,957,958,1638,1639,1640,1641,1642,1643,1734,1735,1736,1737,1738,1739,1830,1831,1832,1833,1834]
def ridgeSupport706_001 : List Nat := [1835,2190,2191,2192,2193,2194,2195,2238,2239,2240,2241,2242,2243,2382,2383,2384,2385,2386,2387,2526,2527,2528,2529,2530,2531,2556,2557,2558,2559,2560,2561,3150]
def ridgeSupport706_002 : List Nat := [3151,3152,3153,3154,3155,3198,3199,3200,3201,3202,3203,3342,3343,3344,3345,3346,3347,3486,3487,3488,3489,3490,3491,3516,3517,3518,3519,3520,3521,4542,4543,4544]
def ridgeSupport706_003 : List Nat := [4545,4546,4547,4590,4591,4592,4593,4594,4595,4734,4735,4736,4737,4738,4739,5154,5155,5156,5157,5158,5159,5166,5167,5168,5169,5170,5171,7172,7173,7178,7179,7192]
def ridgeSupport706_004 : List Nat := [7193,7195,7198,7201,7204,7212,7214,7220,7221,7226,7227,7240,7241,7315,7318,7321,7324,7332,7334,7363,7366,7369,7372,7380,7382,7651,7654,7657,7660,7668,7670,7676]
def ridgeSupport706_005 : List Nat := [7677,7682,7683,7696,7697,7724,7725,7730,7731,7744,7745,7819,7822,7825,7828,7836,7838,7854,7855,7856,7857,7858,7859,7998,7999,8000,8001,8002,8003,8028,8029,8030]
def ridgeSupport706_006 : List Nat := [8031,8032,8033,8419,8422,8425,8428,8436,8438,8444,8445,8450,8451,8464,8465,8492,8493,8498,8499,8512,8513,8587,8590,8593,8596,8604,8606,8622,8623,8624,8625,8626]
def ridgeSupport706_007 : List Nat := [8627,8766,8767,8768,8769,8770,8771,8796,8797,8798,8799,8800,8801,9475,9478,9481,9484,9492,9494,9500,9501,9506,9507,9520,9521,9548,9549,9554,9555,9568,9569,9643]
def ridgeSupport706_008 : List Nat := [9646,9649,9652,9660,9662,9678,9679,9680,9681,9682,9683,10074,10075,10076,10077,10078,10079,10086,10087,10088,10089,10090,10091,11647,11650,11654,11707,11710,11713,11716,11724,11726]
def ridgeSupport706_009 : List Nat := [11899,11902,11906,11995,11998,12001,12004,12012,12014,12120,12121,12122,12123,12124,12125,12379,12382,12386,12475,12478,12481,12484,12492,12494,12600,12601,12602,12603,12604,12605,13075,13078]
def ridgeSupport706_010 : List Nat := [13082,13171,13174,13177,13180,13188,13190,13440,13441,13442,13443,13444,13445,14684,14685,14690,14691,14704,14705,14754,14759,14760,14765,14773,14775,14850,14855,14856,14861,14869,14871,14970]
def ridgeSupport706_011 : List Nat := [14975,14976,14981,14989,14991]
def ridgeSupport706_code : Nat := 0x3a8fea37a85ea03a7fe9eba17e857a0de823a07e80b9b7e6d79ade6a39a7e68b971e5c3963e58b95de573485d213483d20b481d203386ce1337ccde7376cdcf31acc5b313c4f713cc4ef13ac4e7138c33b0ccc3130c1c2fb0bbc18b05ec16ef5dbd72f5bbd6af59bd62eeebbb2ee4bb86edebb6ee82b9fae7bb73adccb712dc1b6fadbbb61ad82b5fe76b9daa7699da27679d9a75f9d7a75d9d7275b9d6a5d3974a5d197425cf973a5be96f25b496c65ae96ae5619582553954a54d953253194c2523948a51d9472516945250c9426506940e261898225f897a25d8972243890a241890223f88fa1b386ca1b186c21af86ba19e8672194864618e862e141850213384ca12d84b21118442103840a0fd83f20f683d20ec83a60e6838df617d81f5f7d79f5d7d71f437d09f417d01f3f7cf9eb37ac9eb17ac1eaf7ab9e9e7a71e947a45e8e7a2de417901e3378c9e2d78b1e117841e037809dfd77f1df677d1dec77a5de6778dcd67351ccc7325cc6730dca67291c9c7265c96724dc497121c3b70e9c3570d1c2e70b1c247085c1e706dc197061c0b7029c05701143350c943150c142f50b94275099425509142350892834a092814a0127f49f91f347c91f147c11ef47b91c347091c147011bf46f8dc13700dbf36f8dbd36f0da33688da13680d9f3678d133448d113440d0f3438c833208c813200c7f31f8c533148c513140c4f3138a0128009ff27f89fd27f09e327889e127809df27789532548951254094f25388c323088c123008bf22f88932248891224088f223872b1ca87291ca07271c986cb1b286c91b206c71b1866b19a866919a066719983be0ef43bc0de03770dd83240c8c3220b302cb0b28124048c122
def ridgeSupport706_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport706_code
def ridgeSupport706_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport706_code
def ridgeSupport706_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport706_code
def ridgeSupport706_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport706_code
def ridgeSupport706_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport706_code
def ridgeSupport706_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport706_code
def ridgeSupport706_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport706_code
def ridgeSupport706_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport706_code
def ridgeSupport706_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport706_code
def ridgeSupport706_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport706_code
def ridgeSupport706_rest_010 : Nat := PackedRawNatGrowth.drop 4480 ridgeSupport706_code
def ridgeSupport706_rest_011 : Nat := PackedRawNatGrowth.drop 4928 ridgeSupport706_code
def ridgeSupport706_rest_012 : Nat := PackedRawNatGrowth.drop 4998 ridgeSupport706_code
def ridgeSupport706_suffix_012 : List Nat := []
def ridgeSupport706_suffix_011 : List Nat := ridgeSupport706_011 ++ ridgeSupport706_suffix_012
def ridgeSupport706_suffix_010 : List Nat := ridgeSupport706_010 ++ ridgeSupport706_suffix_011
def ridgeSupport706_suffix_009 : List Nat := ridgeSupport706_009 ++ ridgeSupport706_suffix_010
def ridgeSupport706_suffix_008 : List Nat := ridgeSupport706_008 ++ ridgeSupport706_suffix_009
def ridgeSupport706_suffix_007 : List Nat := ridgeSupport706_007 ++ ridgeSupport706_suffix_008
def ridgeSupport706_suffix_006 : List Nat := ridgeSupport706_006 ++ ridgeSupport706_suffix_007
def ridgeSupport706_suffix_005 : List Nat := ridgeSupport706_005 ++ ridgeSupport706_suffix_006
def ridgeSupport706_suffix_004 : List Nat := ridgeSupport706_004 ++ ridgeSupport706_suffix_005
def ridgeSupport706_suffix_003 : List Nat := ridgeSupport706_003 ++ ridgeSupport706_suffix_004
def ridgeSupport706_suffix_002 : List Nat := ridgeSupport706_002 ++ ridgeSupport706_suffix_003
def ridgeSupport706_suffix_001 : List Nat := ridgeSupport706_001 ++ ridgeSupport706_suffix_002
def ridgeSupport706_suffix_000 : List Nat := ridgeSupport706_000 ++ ridgeSupport706_suffix_001
theorem ridgeSupport706_source : candidateRows 706 =
    (PackedRawNatGrowth.readList 14 357 ridgeSupport706_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase01
