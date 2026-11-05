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
def ridgeSupport515_000 : List Nat := [4,8,11,13,14,140,142,145,146,148,164,166,169,170,172,176,178,181,182,184,212,214,217,218,220,236,238,241,242,244,248,250]
def ridgeSupport515_001 : List Nat := [253,254,256,281,282,284,285,288,289,290,292,293,295,300,301,302,303,305,306,309,310,311,313,314,316,321,322,323,324,326,327,330]
def ridgeSupport515_002 : List Nat := [331,332,334,335,337,342,343,1630,1631,1636,1637,1642,1643,1644,1645,1646,1647,1648,1649,1654,1655,1660,1661,1666,1667,1668,1669,1670,1671,1672,1673,1678]
def ridgeSupport515_003 : List Nat := [1679,1682,1683,1684,1685,1690,1691,1694,1695,1696,1697,1699,1701,1705,1707,1711,1713,1716,1717,1718,1719,1720,1721,1723,1725,1729,1731,1735,1737,1740,1741,1742]
def ridgeSupport515_004 : List Nat := [1743,1744,1745,1764,1765,1766,1767,1768,1769,1774,1775,1780,1781,1786,1787,1798,1799,1804,1805,1810,1811,1818,1820,1822,1823,1824,1826,1828,1829,1830,1832,1834]
def ridgeSupport515_005 : List Nat := [1835,1842,1844,1846,1847,1848,1850,1852,1853,1854,1856,1858,1859,1867,1869,1873,1875,1879,1881,2530,2531,2536,2537,2542,2543,2548,2549,2551,2553,2557,2559,2566]
def ridgeSupport515_006 : List Nat := [2567,2572,2573,2584,2585,2596,2597,2604,2606,2610,2612,2617,2619,2623,2625,2638,2639,2644,2645,2650,2651,2656,2657,2659,2661,2665,2667,2674,2675,2680,2681,2692]
def ridgeSupport515_007 : List Nat := [2693,2704,2705,2712,2714,2718,2720,2725,2727,2731,2733,2746,2747,2752,2753,2758,2759,2764,2765,2767,2769,2773,2775,2782,2783,2788,2789,2800,2801,2812,2813,2820]
def ridgeSupport515_008 : List Nat := [2822,2826,2828,2833,2835,2839,2841,3490,3491,3496,3497,3502,3503,3508,3509,3511,3513,3517,3519,3526,3527,3532,3533,3544,3545,3556,3557,3564,3566,3570,3572,3577]
def ridgeSupport515_009 : List Nat := [3579,3583,3585,3598,3599,3604,3605,3610,3611,3616,3617,3619,3621,3625,3627,3634,3635,3640,3641,3652,3653,3664,3665,3672,3674,3678,3680,3685,3687,3691,3693,3706]
def ridgeSupport515_010 : List Nat := [3707,3712,3713,3718,3719,3724,3725,3727,3729,3733,3735,3742,3743,3748,3749,3760,3761,3772,3773,3780,3782,3786,3788,3793,3795,3799,3801,7174,7175,7180,7181,7186]
def ridgeSupport515_011 : List Nat := [7187,7188,7189,7190,7191,7192,7193,7198,7199,7204,7205,7210,7211,7212,7213,7214,7215,7216,7217,7236,7237,7238,7239,7240,7241,7260,7261,7262,7263,7264,7265,7284]
def ridgeSupport515_012 : List Nat := [7285,7286,7287,7288,7289,7308,7309,7310,7311,7312,7313,7332,7333,7334,7335,7336,7337,7356,7357,7358,7359,7360,7361,7362,7364,7368,7370,7374,7376,7380,7381,7382]
def ridgeSupport515_013 : List Nat := [7383,7384,7385,7966,7967,7978,7979,8002,8003,8014,8015,8022,8024,8028,8030,8038,8039,8050,8051,8074,8075,8086,8087,8094,8096,8100,8102,8110,8111,8122,8123,8146]
def ridgeSupport515_014 : List Nat := [8147,8158,8159,8166,8168,8172,8174,8734,8735,8746,8747,8770,8771,8782,8783,8790,8792,8796,8798,8806,8807,8818,8819,8842,8843,8854,8855,8862,8864,8868,8870,8878]
def ridgeSupport515_015 : List Nat := [8879,8890,8891,8914,8915,8926,8927,8934,8936,8940,8942,11638,11639,11642,11643,11644,11645,11650,11651,11654,11655,11656,11657,11676,11677,11678,11679,11680,11681,11700,11701,11702]
def ridgeSupport515_016 : List Nat := [11703,11704,11705,11706,11708,11712,11714,11718,11720,11724,11725,11726,11727,11728,11729,11730,11732,11736,11738,11742,11744,11748,11749,11750,11751,11752,11753,11755,11756,11758,11759,11761]
def ridgeSupport515_017 : List Nat := [11762,12088,12089,12100,12101,12108,12110,12114,12116,12124,12125,12127,12129,12136,12137,12142,12143,12154,12155,12162,12164,12168,12170,12178,12179,12181,12183,12190,12191,12196,12197,12208]
def ridgeSupport515_018 : List Nat := [12209,12216,12218,12222,12224,12232,12233,12235,12237,12244,12245,12568,12569,12580,12581,12588,12590,12594,12596,12604,12605,12607,12609,12616,12617,12622,12623,12634,12635,12642,12644,12648]
def ridgeSupport515_019 : List Nat := [12650,12658,12659,12661,12663,12670,12671,12676,12677,12688,12689,12696,12698,12702,12704,12712,12713,12715,12717,12724,12725,14410,14411,14414,14415,14416,14417,14452,14453,14458,14459,14464]
def ridgeSupport515_020 : List Nat := [14465,14500,14501,14506,14507,14512,14513,14700,14701,14702,14703,14704,14705]
def ridgeSupport515_code : Nat := 0x3971e5c396fe5bb96de5b38b1e2c38abe2ab8a5e293881e20387be1eb875e1d3851e14384fe13b84be12b1b5c6d31adc6af1a9c6a31a0c67b19ac663191c643185c61317fc5fb177c5d7173c5cb16ac5a3164c58b15bc56b14fc53b149c523141c4ff13dc4f3134c4cb12ec4b3125c493119c462fd5bf52fcdbf2efc9bf22fc0befafbabee2fb1bec2fa5be92f9fbe7af97be56f93be4af8abe22f84be0af7bbdeaf6fbdbaf69bda2f61bd7ef5dbd72f54bd4af4ebd32f45bd12f39bce2df2b7c6defb7badecb7aede9b7a2de7b79ade5b792de0b77addab762dd4b74add1b742dcfb73adcdb732dc8b71adc2b702dbcb6eadb9b6e2db7b6dadb5b6d2da1b682d9fb67ad9db672d89b622d87b61ad83b60ad7db5f2d7bb5ead77b5da2ee8bb22e88b9a2df8b7a2d38b4a2bb8aea2af8aba2a68a922a08a7a2978a5a28b8a2a27389ca267899a25e8972258895a24f893a243890a22b88aa21f8879fee7fb1fe87f99fdf7f79fd37f49fbb7ee9faf7eb9fa67e91fa07e79f977e59f8b7e29f737dc9f677d99f5e7d71f587d59f4f7d39f437d09f2b7ca9f1f7c79cd97361cd77359cd57351cd07339cca7321cc47309cc17301cbf72f9cbd72f1ca972a1ca77299ca57291c917241c8f7239c8d7231c7971e1c7771d9c7571d1c617181c5f7179c5d7171c497121c477119c457111c3170c1c2f70b9c2d70b1c2b70a9c257091c1f7079c197061c177059c157051c137049c0d7031c077018ed93b5ced33b44ecc3b28ec63b10ebd3af0eb13ac0ea53a90e9f3a78e973a54e913a3ce8d3a30e873a18e813a00e7b39e8e6d39ace673994e603978e5a3960e513940e453910e3938e0e3338c8e2b38a4e25388ce213880e1b3868e153850e0f3838e0137fcdfb37e4df437c8dee37b0de53790dd93760dcd3730dc73718dbf36f4db936dcdb536d0daf36b8da936a0da33688b192c5cb132c44b0c2c28b062c10afd2bf0af12bc0ae52b90adf2b78ad72b54ad12b3cacd2b30ac72b18ac12b00abb2ae8aad2aacaa72a94aa02a78a9a2a60a912a40a852a10a7929e0a7329c8a6b29a4a65298ca612980a5b2968a552950a4f2938a4128fca3b28e4a3428c8a2e28b0a252890a192860a0d2830a0728189ff27f49f927dc9f527d09ef27b89e927a09e327887591d5c7531d4474d1d2c7431d087401cf873d1cf073a1ce07371cd87341cc872b1ca87281c987251c907221c8071f1c7871c1c687131c4870d1c307071c186fb1be86f51bd06ef1bb86e91ba06e71b986e51b906d11b406cf1b386cd1b306c91b1c6c31b046bd1aec6b91ae06b71ad86b51ad06b11abc6ab1aa46a51a8c6a11a8069f1a7869b1a686951a506931a4868f1a386891a206871a186851a106831a0867d19f067719d867119c066f19b866d19b066b19a8665199065f19781570558151053c14e053014b05281470518144050c142050413c04e813904dc13604d413204c412f04b812d04b012704941240488121048011d047011a046410003f80fd03e80f803d00f203c40ee03b00dc03680d903580d402e00b602d40b202c00ac02a80a902980a40250092024408e023000e003400b0020004
def ridgeSupport515_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport515_code
def ridgeSupport515_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport515_code
def ridgeSupport515_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport515_code
def ridgeSupport515_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport515_code
def ridgeSupport515_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport515_code
def ridgeSupport515_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport515_code
def ridgeSupport515_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport515_code
def ridgeSupport515_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport515_code
def ridgeSupport515_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport515_code
def ridgeSupport515_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport515_code
def ridgeSupport515_rest_010 : Nat := PackedRawNatGrowth.drop 4480 ridgeSupport515_code
def ridgeSupport515_rest_011 : Nat := PackedRawNatGrowth.drop 4928 ridgeSupport515_code
def ridgeSupport515_rest_012 : Nat := PackedRawNatGrowth.drop 5376 ridgeSupport515_code
def ridgeSupport515_rest_013 : Nat := PackedRawNatGrowth.drop 5824 ridgeSupport515_code
def ridgeSupport515_rest_014 : Nat := PackedRawNatGrowth.drop 6272 ridgeSupport515_code
def ridgeSupport515_rest_015 : Nat := PackedRawNatGrowth.drop 6720 ridgeSupport515_code
def ridgeSupport515_rest_016 : Nat := PackedRawNatGrowth.drop 7168 ridgeSupport515_code
def ridgeSupport515_rest_017 : Nat := PackedRawNatGrowth.drop 7616 ridgeSupport515_code
def ridgeSupport515_rest_018 : Nat := PackedRawNatGrowth.drop 8064 ridgeSupport515_code
def ridgeSupport515_rest_019 : Nat := PackedRawNatGrowth.drop 8512 ridgeSupport515_code
def ridgeSupport515_rest_020 : Nat := PackedRawNatGrowth.drop 8960 ridgeSupport515_code
def ridgeSupport515_rest_021 : Nat := PackedRawNatGrowth.drop 9142 ridgeSupport515_code
def ridgeSupport515_suffix_021 : List Nat := []
def ridgeSupport515_suffix_020 : List Nat := ridgeSupport515_020 ++ ridgeSupport515_suffix_021
def ridgeSupport515_suffix_019 : List Nat := ridgeSupport515_019 ++ ridgeSupport515_suffix_020
def ridgeSupport515_suffix_018 : List Nat := ridgeSupport515_018 ++ ridgeSupport515_suffix_019
def ridgeSupport515_suffix_017 : List Nat := ridgeSupport515_017 ++ ridgeSupport515_suffix_018
def ridgeSupport515_suffix_016 : List Nat := ridgeSupport515_016 ++ ridgeSupport515_suffix_017
def ridgeSupport515_suffix_015 : List Nat := ridgeSupport515_015 ++ ridgeSupport515_suffix_016
def ridgeSupport515_suffix_014 : List Nat := ridgeSupport515_014 ++ ridgeSupport515_suffix_015
def ridgeSupport515_suffix_013 : List Nat := ridgeSupport515_013 ++ ridgeSupport515_suffix_014
def ridgeSupport515_suffix_012 : List Nat := ridgeSupport515_012 ++ ridgeSupport515_suffix_013
def ridgeSupport515_suffix_011 : List Nat := ridgeSupport515_011 ++ ridgeSupport515_suffix_012
def ridgeSupport515_suffix_010 : List Nat := ridgeSupport515_010 ++ ridgeSupport515_suffix_011
def ridgeSupport515_suffix_009 : List Nat := ridgeSupport515_009 ++ ridgeSupport515_suffix_010
def ridgeSupport515_suffix_008 : List Nat := ridgeSupport515_008 ++ ridgeSupport515_suffix_009
def ridgeSupport515_suffix_007 : List Nat := ridgeSupport515_007 ++ ridgeSupport515_suffix_008
def ridgeSupport515_suffix_006 : List Nat := ridgeSupport515_006 ++ ridgeSupport515_suffix_007
def ridgeSupport515_suffix_005 : List Nat := ridgeSupport515_005 ++ ridgeSupport515_suffix_006
def ridgeSupport515_suffix_004 : List Nat := ridgeSupport515_004 ++ ridgeSupport515_suffix_005
def ridgeSupport515_suffix_003 : List Nat := ridgeSupport515_003 ++ ridgeSupport515_suffix_004
def ridgeSupport515_suffix_002 : List Nat := ridgeSupport515_002 ++ ridgeSupport515_suffix_003
def ridgeSupport515_suffix_001 : List Nat := ridgeSupport515_001 ++ ridgeSupport515_suffix_002
def ridgeSupport515_suffix_000 : List Nat := ridgeSupport515_000 ++ ridgeSupport515_suffix_001
theorem ridgeSupport515_source : candidateRows 515 =
    (PackedRawNatGrowth.readList 14 653 ridgeSupport515_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase01
