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
def ridgeSupport642_000 : List Nat := [13,35,45,51,54,56,150,151,154,155,158,159,222,223,226,227,230,231,268,269,270,273,274,279,280,285,287,309,311,313,315,317]
def ridgeSupport642_001 : List Nat := [322,323,325,328,552,556,557,558,559,561,562,569,571,595,597,599,600,602,604,605,609,614,665,666,667,668,669,670,708,712,713,714]
def ridgeSupport642_002 : List Nat := [715,717,718,725,727,751,753,755,756,758,760,761,765,770,792,796,797,798,799,801,802,809,811,835,837,839,840,842,844,845,849,854]
def ridgeSupport642_003 : List Nat := [855,857,859,861,862,864,866,867,871,873,878,879,1388,1393,1402,1404,1470,1471,1480,1481,1486,1487,1490,1492,1496,1497,1503,1506,1518,1519,1528,1529]
def ridgeSupport642_004 : List Nat := [1556,1561,1566,1567,1570,1572,1576,1577,1582,1583,1592,1593,1606,1607,1616,1617,1892,1897,1906,1908,1926,1927,1936,1937,1974,1975,1984,1985,1990,1991,1994,1996]
def ridgeSupport642_005 : List Nat := [2000,2001,2007,2010,2012,2017,2022,2023,2026,2028,2032,2033,2070,2071,2080,2081,2094,2095,2104,2105,2182,2184,2212,2214,2222,2223,2240,2241,2324,2329,2354,2359]
def ridgeSupport642_006 : List Nat := [2368,2369,2386,2387,2660,2665,2674,2676,2694,2695,2704,2705,2742,2743,2752,2753,2758,2759,2762,2764,2768,2769,2775,2778,2780,2785,2790,2791,2794,2796,2800,2801]
def ridgeSupport642_007 : List Nat := [2838,2839,2848,2849,2862,2863,2872,2873,2950,2952,2980,2982,2990,2991,3008,3009,3092,3097,3122,3127,3136,3137,3154,3155,3764,3769,3778,3780,3798,3799,3808,3809]
def ridgeSupport642_008 : List Nat := [3846,3847,3856,3857,3862,3863,3866,3868,3872,3873,3879,3882,3884,3889,3894,3895,3898,3900,3904,3905,3942,3943,3952,3953,3966,3967,3976,3977,4306,4308,4318,4320]
def ridgeSupport642_009 : List Nat := [4346,4347,4358,4359,4448,4453,4460,4465,4492,4493,4504,4505,4818,4819,4826,4827,5132,5137,5138,5142,5157,5160,5163,5167,5176,5178,5186,5191,5205,5208,5211,5215]
def ridgeSupport642_010 : List Nat := [5224,5226,5234,5239,5265,5268,5271,5275,5297,5299,5307,5310,5374,5375,5452,5453,5548,5549,5704,5705,5862,5863,5872,5873,5877,5878,5879,5880,5885,5886,5954,5956]
def ridgeSupport642_011 : List Nat := [5967,5970,5985,5986,5987,5988,5993,5994,6020,6021,6023,6025,6057,6058,6059,6060,6122,6124,6135,6138,6153,6154,6155,6156,6161,6162,6188,6189,6191,6193,6225,6226]
def ridgeSupport642_012 : List Nat := [6227,6228,6338,6340,6351,6354,6369,6370,6371,6372,6377,6378,6458,6459,6461,6463,6495,6496,6497,6498]
def ridgeSupport642_code : Nat := 0xcb165872c195fc9fe4f727793ac7563a71c98e3c7163871a58cfc62630b0a9853c29614706382fc16e0b3025811c06602f015809bfd5fdefd97eabd65eaef557a9bc4de1ef0b784bb55da6ec9763bb15d86ea574fba25d0adfd6fdb7c5bdeded6f5b78dbc2dcf6e6b24d922b5b5acaa6d5329ff4fea5f52ee9674b1a4dd25e929491a3bd1ca8d5468a2fd16e8b1455a23d10a875438a17d0ae851425a0b504a82340c96dcb6a5a72d28ccc66231b18c8b8c5b22cb160883c41a1f70fa870437a1a90d27c4be21efef7e7b8bdc1ecef667a0bd01e78f3a79bbcd9e62f2c7953c9de42f2078e3c69e2ef16788bc41e0ef06770bb81daeed67623b09d72eb4629b149882c4061bb0c9832c145e0af0175ebae5d32e91710b8659cace165eb2e590ac8162eb16578abc15d8aea573ab995c2adc56d2b5d5a2ad05662b2958eac6560ab0156eab6548aa4150ea8653a29c94d2a644a9a54928294049ba4c9232914460a30115e8ae453229111088641ca0e105e82e410a08102e8163f89fc0fd87ea3f39f98fc27dc3ed1f5cfa27d03e61f28f8e7c63e09f00f6e7b63c89e40f0e7863ba1dc8ed27643289940c8e64631c98e0c5e62e31498a0c4862230f9878c326142fc97e0bde5ee2f1177cbb25d82ea1748b9e5ce2e49720b7e5be2be15e8ae256c1b78db86d23671b18d886c035e1ae8d6c6b23571ab0d4469a34c1a50d2068e3451a18cac6523221908c7c63c31d18e0c606042fd17c8be05ec2f41798bc45de2d716a8b3859a2cb1650b245902c414f0a7453829b14d0a644cc26112e89704b425812b89544a623b11c88c846222f11708b44582280a4051428614209e84ec27213709a847c23a11808b844822210e08684301ce0e607183881be0de04f827813609a04b825807003601980b404600d
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
def ridgeSupport642_rest_013 : Nat := PackedRawNatGrowth.drop 5252 ridgeSupport642_code
def ridgeSupport642_suffix_013 : List Nat := []
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
    (PackedRawNatGrowth.readList 13 404 ridgeSupport642_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
