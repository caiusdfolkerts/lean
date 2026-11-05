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
def ridgeSupport194_000 : List Nat := [9,31,41,47,53,54,102,103,106,107,110,111,174,175,178,179,182,183,246,247,251,253,254,258,260,261,263,267,268,272,274,275]
def ridgeSupport194_001 : List Nat := [279,281,282,284,533,534,535,538,539,540,542,547,549,554,555,556,559,560,561,563,568,570,617,618,619,620,621,622,689,690,691,694]
def ridgeSupport194_002 : List Nat := [695,696,698,703,705,710,711,712,715,716,717,719,724,726,773,774,775,778,779,780,782,787,789,794,795,796,799,800,801,803,808,810]
def ridgeSupport194_003 : List Nat := [857,858,860,861,862,863,865,866,868,869,871,872,1401,1403,1407,1409,1460,1461,1466,1467,1487,1489,1493,1495,1500,1501,1506,1507,1508,1509,1514,1515]
def ridgeSupport194_004 : List Nat := [1556,1557,1562,1563,1569,1571,1575,1577,1596,1597,1602,1603,1620,1621,1626,1627,1905,1907,1911,1913,1916,1917,1922,1923,1964,1965,1970,1971,1991,1993,1997,1999]
def ridgeSupport194_005 : List Nat := [2004,2005,2010,2011,2012,2013,2018,2019,2025,2027,2031,2033,2060,2061,2066,2067,2084,2085,2090,2091,2109,2111,2139,2141,2154,2155,2172,2173,2181,2183,2211,2213]
def ridgeSupport194_006 : List Nat := [2226,2227,2244,2245,2673,2675,2679,2681,2684,2685,2690,2691,2732,2733,2738,2739,2759,2761,2765,2767,2772,2773,2778,2779,2780,2781,2786,2787,2793,2795,2799,2801]
def ridgeSupport194_007 : List Nat := [2828,2829,2834,2835,2852,2853,2858,2859,2877,2879,2907,2909,2922,2923,2940,2941,2949,2951,2979,2981,2994,2995,3012,3013,3777,3779,3783,3785,3788,3789,3794,3795]
def ridgeSupport194_008 : List Nat := [3836,3837,3842,3843,3863,3865,3869,3871,3876,3877,3882,3883,3884,3885,3890,3891,3897,3899,3903,3905,3932,3933,3938,3939,3956,3957,3962,3963,4233,4235,4245,4247]
def ridgeSupport194_009 : List Nat := [4278,4279,4290,4291,4305,4307,4317,4319,4350,4351,4362,4363,4754,4755,4762,4763,5135,5137,5139,5141,5158,5160,5162,5164,5169,5171,5175,5177,5206,5208,5210,5212]
def ridgeSupport194_010 : List Nat := [5217,5219,5223,5225,5266,5268,5270,5272,5288,5290,5294,5296,5382,5383,5444,5445,5540,5541,5696,5697,5852,5853,5858,5859,5876,5877,5882,5883,5886,5887,5951,5953]
def ridgeSupport194_011 : List Nat := [5957,5959,5984,5985,5990,5991,5994,5995,6002,6004,6006,6007,6020,6022,6024,6025,6119,6121,6125,6127,6152,6153,6158,6159,6162,6163,6170,6172,6174,6175,6188,6190]
def ridgeSupport194_012 : List Nat := [6192,6193,6335,6337,6341,6343,6368,6369,6374,6375,6378,6379,6440,6442,6444,6445,6458,6460,6462,6463]
def ridgeSupport194_code : Nat := 0xc9fe4fb27993ac96e4b3255928c75e3ab1cf8e6c70e38318f8c5c60e2ff063830c1760b303f81ec0e606b027812c07e03b013808bf7dfb6fd37e7bc4de22f0d784bbbdddaee9772bb5ddaaecf766bb0dd82e8f745ba0dcfedff6feb7ddbeadeb6f4b71db8adbb6dcb20d902b4b5a4aa2d512a0f506a5852ba9554a8a4c525a929492a34d19e8c7461a2e516a8b1456a1cd0de867431a1650aa851426a0ad04e82340f94dca6a527292885c42a1ff0fe86fc3761a70d1861c30a16f0b684bc2561170897bdbde9eeaf747b1bd89ebaf5c7a0bcfde76f39799bcc9e5af2c795bca9e4af2478fbc75e32f17781bc09dfaefc769bb49d9aecc764bb1dd86ec15e2af11766bb25d2ae8d70eb855beadf16d6b6a5aead6d67eb3d595aca964ab24589ac4961ab0c578abbd5d6ae9571ab895baadc56dab695aaad4567ab35592ac7559aac955aaac541aa094faa7c53ca9dd4e6a71462a3111668b2452a28d10e88543ea1f10d686a42ea16d07e83d415a0a904a824409a04901a80c3f89fbcfd67e93f19f88fba7dc3ed9f68faa7d43e79f34f927c73d99ec8f5a7ac3c19e08efa77c3bc9ddcee677132d9968caa6543219908c7a63c314989cc4662130d9868c2a6142f597a8bca5e42f19788bba5dc2eb9754ba25cf2dd96e8b6a5b42c095fcaf65791b40d9c6ca3641b10d846be35e1ae8d706b43591950ca06463211900c7c63831b18d0c5462630e1860c2c6143071830c145ac2d41678b345982cb1640b1c58c2c115f8ae85702b715b0acc5642b113709b44d826b13509a447423811988c446022f11608ac454225111887843821b10d085c42c21508e0468232117089844822010c085841c20a10408103f81fa0fb07b83d816e0b605982c815e0ae03781b80d606a033819806c03501780a403e009
def ridgeSupport194_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport194_code
def ridgeSupport194_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport194_code
def ridgeSupport194_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport194_code
def ridgeSupport194_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport194_code
def ridgeSupport194_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport194_code
def ridgeSupport194_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport194_code
def ridgeSupport194_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport194_code
def ridgeSupport194_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport194_code
def ridgeSupport194_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport194_code
def ridgeSupport194_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport194_code
def ridgeSupport194_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport194_code
def ridgeSupport194_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport194_code
def ridgeSupport194_rest_012 : Nat := PackedRawNatGrowth.drop 4992 ridgeSupport194_code
def ridgeSupport194_rest_013 : Nat := PackedRawNatGrowth.drop 5252 ridgeSupport194_code
def ridgeSupport194_suffix_013 : List Nat := []
def ridgeSupport194_suffix_012 : List Nat := ridgeSupport194_012 ++ ridgeSupport194_suffix_013
def ridgeSupport194_suffix_011 : List Nat := ridgeSupport194_011 ++ ridgeSupport194_suffix_012
def ridgeSupport194_suffix_010 : List Nat := ridgeSupport194_010 ++ ridgeSupport194_suffix_011
def ridgeSupport194_suffix_009 : List Nat := ridgeSupport194_009 ++ ridgeSupport194_suffix_010
def ridgeSupport194_suffix_008 : List Nat := ridgeSupport194_008 ++ ridgeSupport194_suffix_009
def ridgeSupport194_suffix_007 : List Nat := ridgeSupport194_007 ++ ridgeSupport194_suffix_008
def ridgeSupport194_suffix_006 : List Nat := ridgeSupport194_006 ++ ridgeSupport194_suffix_007
def ridgeSupport194_suffix_005 : List Nat := ridgeSupport194_005 ++ ridgeSupport194_suffix_006
def ridgeSupport194_suffix_004 : List Nat := ridgeSupport194_004 ++ ridgeSupport194_suffix_005
def ridgeSupport194_suffix_003 : List Nat := ridgeSupport194_003 ++ ridgeSupport194_suffix_004
def ridgeSupport194_suffix_002 : List Nat := ridgeSupport194_002 ++ ridgeSupport194_suffix_003
def ridgeSupport194_suffix_001 : List Nat := ridgeSupport194_001 ++ ridgeSupport194_suffix_002
def ridgeSupport194_suffix_000 : List Nat := ridgeSupport194_000 ++ ridgeSupport194_suffix_001
theorem ridgeSupport194_source : candidateSupports 194 =
    (PackedRawNatGrowth.readList 13 404 ridgeSupport194_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
