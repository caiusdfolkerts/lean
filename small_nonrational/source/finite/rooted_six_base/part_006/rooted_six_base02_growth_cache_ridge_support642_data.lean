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
def ridgeSupport642_000 : List Nat := [13,35,45,51,54,56,150,151,154,155,158,159,222,223,226,227,230,231,268,269,270,273,274,279,280,285,287,309,311,313,315,317]
def ridgeSupport642_001 : List Nat := [322,323,325,328,552,556,557,558,559,561,562,569,571,595,597,599,600,602,604,605,609,614,665,666,667,668,669,670,708,712,713,714]
def ridgeSupport642_002 : List Nat := [715,717,718,725,727,751,753,755,756,758,760,761,765,770,792,796,797,798,799,801,802,809,811,835,837,839,840,842,844,845,849,854]
def ridgeSupport642_003 : List Nat := [855,857,859,861,862,864,866,867,871,873,878,879,1388,1393,1402,1404,1470,1471,1480,1481,1486,1487,1490,1492,1496,1497,1503,1506,1518,1519,1528,1529]
def ridgeSupport642_004 : List Nat := [1556,1561,1566,1567,1570,1572,1576,1577,1582,1583,1592,1593,1606,1607,1616,1617,1892,1897,1906,1908,1926,1927,1936,1937,1974,1975,1984,1985,1990,1991,1994,1996]
def ridgeSupport642_005 : List Nat := [2000,2001,2007,2010,2012,2017,2022,2023,2026,2028,2032,2033,2070,2071,2080,2081,2094,2095,2104,2105,2182,2184,2212,2214,2222,2223,2240,2241,2324,2329,2354,2359]
def ridgeSupport642_006 : List Nat := [2368,2369,2386,2387,2660,2665,2674,2676,2694,2695,2704,2705,2742,2743,2752,2753,2758,2759,2762,2764,2768,2769,2775,2778,2780,2785,2790,2791,2794,2796,2800,2801]
def ridgeSupport642_007 : List Nat := [2838,2839,2848,2849,2862,2863,2872,2873,2950,2952,2980,2982,2990,2991,3008,3009,3092,3097,3122,3127,3136,3137,3154,3155,3764,3769,3778,3780,3798,3799,3808,3809]
def ridgeSupport642_008 : List Nat := [3846,3847,3856,3857,3862,3863,3866,3868,3872,3873,3879,3882,3884,3889,3894,3895,3898,3900,3904,3905,3942,3943,3952,3953,3966,3967,3976,3977,4306,4308,4318,4320]
def ridgeSupport642_009 : List Nat := [4346,4347,4358,4359,4448,4453,4460,4465,4492,4493,4504,4505,4818,4819,4826,4827,5132,5137,5138,5142,5158,5159,5162,5164,5168,5169,5175,5178,5190,5191,5200,5201]
def ridgeSupport642_010 : List Nat := [5206,5207,5216,5217,5228,5233,5238,5239,5242,5244,5248,5249,5252,5254,5258,5259,5408,5413,5414,5418,5430,5431,5440,5441,5446,5447,5450,5452,5456,5457,5463,5466]
def ridgeSupport642_011 : List Nat := [5468,5473,5478,5479,5482,5484,5488,5489,5494,5495,5504,5505,5520,5521,5525,5527,5584,5586,5588,5589,5606,5607,5614,5616,5624,5625,5633,5635,5690,5695,5698,5699]
def ridgeSupport642_012 : List Nat := [5716,5717,5720,5725,5734,5735,5739,5742,5888,5893,5894,5898,5910,5911,5920,5921,5926,5927,5930,5932,5936,5937,5943,5946,5948,5953,5958,5959,5962,5964,5968,5969]
def ridgeSupport642_013 : List Nat := [5974,5975,5984,5985,6000,6001,6005,6007,6064,6066,6068,6069,6086,6087,6094,6096,6104,6105,6113,6115,6170,6175,6178,6179,6196,6197,6200,6205,6214,6215,6219,6222]
def ridgeSupport642_014 : List Nat := [6524,6529,6530,6534,6546,6547,6556,6557,6562,6563,6566,6568,6572,6573,6579,6582,6584,6589,6594,6595,6598,6600,6604,6605,6610,6611,6620,6621,6636,6637,6641,6643]
def ridgeSupport642_015 : List Nat := [6844,6846,6848,6849,6856,6858,6860,6861,6869,6871,6875,6877,6950,6955,6958,6959,6962,6967,6970,6971,6975,6978,6981,6984,7142,7143,7364,7369,7370,7374,7389,7392]
def ridgeSupport642_016 : List Nat := [7395,7399,7408,7410,7418,7423,7437,7440,7443,7447,7456,7458,7466,7471,7497,7500,7503,7507,7529,7531,7539,7542,7606,7607,7684,7685,7780,7781,7936,7937]
def ridgeSupport642_code : Nat := 0x3e03f00f32f993c0be04edbf6dbaedd73eb5f5a7aa7d4fea67527a5fd2ae917483a2fd13e8874379ffcfae7973c39cfce3e70737799dccae64f3137cfbe6da46d17685b3fd9deceb66fb32d97ecbb657b26d6eeb6f5afad5d66eb33595ac8d60eb0357dabccf9e7c73db9ecceee7733a79d2ce6e7333919c6ce1e70b37b9b8cdb66cf35b9accd4669b3479a2ccee673327992cc3660b30397cc27612f08f846c1ee0e306b834c11e08b03f81abf1df86fb37d8be85f3af8f7c6bdaded2f657b0bbbddd6ee3770bb0dd82eaf756ba8dd42e9974aba3dd1ae8373cb9d5cdee63730b965caae4f726b90dc82e2f716b855c1ae0b700b3759aeccf666b2ed962cab654b21d90ac7f63ab01d806bf35f8af857babcf5e6aead752ba55d0acbd656b23590ac0d602aef576ab8d5c2ad956aab3d59aac355caad555eaa3550aa6552aa8f546aa0d502a6f536a95549aa4b520a45d22a90d484a40d2028f947aa3bd1da8e346ca30d1828af456a28d14288f446a1d50de863430a1650aa84f426a0b504a82340c96dcb6a5a72d28ccc66231b18c8b8c5b22cb160883c41a1f70fa870437a1a90d27c4be21efef7e7b8bdc1ecef667a0bd01e78f3a79bbcd9e62f2c7953c9de42f2078e3c69e2ef16788bc41e0ef06770bb81daeed67623b09d72eb4629b149882c4061bb0c9832c145e0af0175ebae5d32e91710b8659cace165eb2e590ac8162eb16578abc15d8aea573ab995c2adc56d2b5d5a2ad05662b2958eac6560ab0156eab6548aa4150ea8653a29c94d2a644a9a54928294049ba4c9232914460a30115e8ae453229111088641ca0e105e82e410a08102e8163f89fc0fd87ea3f39f98fc27dc3ed1f5cfa27d03e61f28f8e7c63e09f00f6e7b63c89e40f0e7863ba1dc8ed27643289940c8e64631c98e0c5e62e31498a0c4862230f9878c326142fc97e0bde5ee2f1177cbb25d82ea1748b9e5ce2e49720b7e5be2be15e8ae256c1b78db86d23671b18d886c035e1ae8d6c6b23571ab0d4469a34c1a50d2068e3451a18cac6523221908c7c63c31d18e0c606042fd17c8be05ec2f41798bc45de2d716a8b3859a2cb1650b245902c414f0a7453829b14d0a644cc26112e89704b425812b89544a623b11c88c846222f11708b44582280a4051428614209e84ec27213709a847c23a11808b844822210e08684301ce0e607183881be0de04f827813609a04b825807003601980b404600d
def ridgeSupport642_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport642_code
def ridgeSupport642_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport642_code
def ridgeSupport642_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport642_code
def ridgeSupport642_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport642_code
def ridgeSupport642_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport642_code
def ridgeSupport642_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport642_code
def ridgeSupport642_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport642_code
def ridgeSupport642_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport642_code
def ridgeSupport642_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport642_code
def ridgeSupport642_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport642_code
def ridgeSupport642_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport642_code
def ridgeSupport642_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport642_code
def ridgeSupport642_rest_012 : Nat := PackedRawNatGrowth.drop 4992 ridgeSupport642_code
def ridgeSupport642_rest_013 : Nat := PackedRawNatGrowth.drop 5408 ridgeSupport642_code
def ridgeSupport642_rest_014 : Nat := PackedRawNatGrowth.drop 5824 ridgeSupport642_code
def ridgeSupport642_rest_015 : Nat := PackedRawNatGrowth.drop 6240 ridgeSupport642_code
def ridgeSupport642_rest_016 : Nat := PackedRawNatGrowth.drop 6656 ridgeSupport642_code
def ridgeSupport642_rest_017 : Nat := PackedRawNatGrowth.drop 7046 ridgeSupport642_code
def ridgeSupport642_suffix_017 : List Nat := []
def ridgeSupport642_suffix_016 : List Nat := ridgeSupport642_016 ++ ridgeSupport642_suffix_017
def ridgeSupport642_suffix_015 : List Nat := ridgeSupport642_015 ++ ridgeSupport642_suffix_016
def ridgeSupport642_suffix_014 : List Nat := ridgeSupport642_014 ++ ridgeSupport642_suffix_015
def ridgeSupport642_suffix_013 : List Nat := ridgeSupport642_013 ++ ridgeSupport642_suffix_014
def ridgeSupport642_suffix_012 : List Nat := ridgeSupport642_012 ++ ridgeSupport642_suffix_013
def ridgeSupport642_suffix_011 : List Nat := ridgeSupport642_011 ++ ridgeSupport642_suffix_012
def ridgeSupport642_suffix_010 : List Nat := ridgeSupport642_010 ++ ridgeSupport642_suffix_011
def ridgeSupport642_suffix_009 : List Nat := ridgeSupport642_009 ++ ridgeSupport642_suffix_010
def ridgeSupport642_suffix_008 : List Nat := ridgeSupport642_008 ++ ridgeSupport642_suffix_009
def ridgeSupport642_suffix_007 : List Nat := ridgeSupport642_007 ++ ridgeSupport642_suffix_008
def ridgeSupport642_suffix_006 : List Nat := ridgeSupport642_006 ++ ridgeSupport642_suffix_007
def ridgeSupport642_suffix_005 : List Nat := ridgeSupport642_005 ++ ridgeSupport642_suffix_006
def ridgeSupport642_suffix_004 : List Nat := ridgeSupport642_004 ++ ridgeSupport642_suffix_005
def ridgeSupport642_suffix_003 : List Nat := ridgeSupport642_003 ++ ridgeSupport642_suffix_004
def ridgeSupport642_suffix_002 : List Nat := ridgeSupport642_002 ++ ridgeSupport642_suffix_003
def ridgeSupport642_suffix_001 : List Nat := ridgeSupport642_001 ++ ridgeSupport642_suffix_002
def ridgeSupport642_suffix_000 : List Nat := ridgeSupport642_000 ++ ridgeSupport642_suffix_001
theorem ridgeSupport642_source : candidateSupports 642 =
    (PackedRawNatGrowth.readList 13 542 ridgeSupport642_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
