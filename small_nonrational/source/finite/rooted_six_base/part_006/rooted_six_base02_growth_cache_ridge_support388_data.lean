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
def ridgeSupport388_000 : List Nat := [18,34,60,63,66,138,139,140,141,148,149,335,336,337,340,341,346,347,352,354,397,398,402,404,405,409,411,412,414,532,533,534]
def ridgeSupport388_001 : List Nat := [537,538,543,544,549,551,594,595,599,601,602,606,608,609,611,880,884,885,886,887,889,890,897,899,945,946,947,950,951,952,954,959]
def ridgeSupport388_002 : List Nat := [961,964,967,968,969,972,973,974,976,981,982,984,985,1629,1631,1648,1650,1708,1709,1714,1715,1728,1729,1731,1734,1737,1740,1742,1743,1756,1757,1762]
def ridgeSupport388_003 : List Nat := [1763,1797,1799,1804,1805,1810,1811,1816,1818,1824,1825,1838,1839,1848,1849,1862,1863,1869,1871,1888,1890,1948,1949,1954,1955,1968,1969,1971,1974,1977,1980,1982]
def ridgeSupport388_004 : List Nat := [1983,1996,1997,2002,2003,2037,2039,2044,2045,2050,2051,2056,2058,2064,2065,2078,2079,2088,2089,2102,2103,2116,2118,2128,2130,2144,2145,2156,2157,2331,2333,2343]
def ridgeSupport388_005 : List Nat := [2345,2364,2365,2376,2377,3189,3191,3208,3210,3220,3221,3226,3227,3268,3269,3274,3275,3288,3289,3291,3294,3297,3300,3302,3303,3309,3311,3316,3317,3322,3323,3328]
def ridgeSupport388_006 : List Nat := [3330,3364,3365,3370,3371,3388,3389,3394,3395,3694,3695,3706,3707,4798,4799,4806,4807,5265,5267,5272,5274,5292,5293,5295,5298,5301,5304,5306,5307,5320,5321,5326]
def ridgeSupport388_007 : List Nat := [5327,5340,5341,5354,5355,5361,5363,5368,5369,5374,5375,5380,5382,5385,5386,5393,5394,5397,5399,5404,5406,5424,5425,5427,5430,5433,5436,5438,5439,5452,5453,5458]
def ridgeSupport388_008 : List Nat := [5459,5472,5473,5486,5487,5493,5495,5500,5501,5506,5507,5512,5514,5517,5518,5525,5526,5528,5529,5536,5538,5540,5541,5548,5550,5564,5565,5576,5577,5694,5695,5697]
def ridgeSupport388_009 : List Nat := [5699,5706,5707,5709,5711,5730,5731,5742,5743,6237,6239,6244,6246,6256,6257,6262,6263,6276,6277,6279,6282,6285,6288,6290,6291,6297,6299,6304,6305,6310,6311,6316]
def ridgeSupport388_010 : List Nat := [6318,6324,6325,6338,6339,6347,6349,6350,6352,6500,6501,7136,7137,7377,7379,7384,7386,7389,7391,7396,7398,7400,7401,7422,7423,7472,7474,7481,7483,7644,7645,7680]
def ridgeSupport388_011 : List Nat := [7681,7838,7839]
def ridgeSupport388_code : Nat := 0x7a7fd3de01f007777bb9d3be9cf4cba61cffe7f73a79d1ce6e72737f9bbcdae6c734f9a3be1df065972c98d0c6763371978c3c6162d71698aec56629f14d8a1c50626f133893c49624311b88ac43e217109877c3b61c70e1866c32617f0bb66fb37598ecc564fb26d92ec95643b20d8fec7d5c9ae456f6b795aead65696b495a2ad05666b31596acad63ab1b58aac4560eb0557dabe55deaeb56fab75586ac1553aa95536a9953fa9f54f2a73536a99d4c6a6151ea8e545ea2b512a88d42aa13506a8253fe9fd4f9a7c53ce9e34eba7553769b94cfa6753269914bba5d52e296b4b2a57d2b695949aa4c524e9232c79634afe57ce7b73d39bdcdcd436a134f5a78d2b6953495a48d0268033ed9f4cf567a33bd9dace767333919c2cde66db3659b0ccb6653315988c9b64d3255928c8a64431dd8ea9494a424f5278929493a47523686d43621850c0852428211908883741b20a505081f40f204502080a404200d0047fd3fe1fdcfea7d33e91f34f987bf3df1ef0f727b63d99ec4f607a33d11e74f387623b01d3ce9a7473a31ce4e7072f3971c84e4071a38c1c4ce2470d3861c1ce0a6e33711b74db86cf3671b30d926c63619b04d806b33591ab4d58672338197ccba3d91ec0f587aa3d01e70f347983c91e40f1c7883c11df8ee87703b71db0ecc7643b11c18e046f43791bb8dd86ea3741b8098c4c226012f09684b2257129894844e225110087c43421910b085442819e0ce066c3321950ca064831c18d0b105802b615a0aa85502a21500a7825412808d046022c11404201f80f0044012
def ridgeSupport388_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport388_code
def ridgeSupport388_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport388_code
def ridgeSupport388_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport388_code
def ridgeSupport388_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport388_code
def ridgeSupport388_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport388_code
def ridgeSupport388_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport388_code
def ridgeSupport388_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport388_code
def ridgeSupport388_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport388_code
def ridgeSupport388_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport388_code
def ridgeSupport388_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport388_code
def ridgeSupport388_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport388_code
def ridgeSupport388_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport388_code
def ridgeSupport388_rest_012 : Nat := PackedRawNatGrowth.drop 4615 ridgeSupport388_code
def ridgeSupport388_suffix_012 : List Nat := []
def ridgeSupport388_suffix_011 : List Nat := ridgeSupport388_011 ++ ridgeSupport388_suffix_012
def ridgeSupport388_suffix_010 : List Nat := ridgeSupport388_010 ++ ridgeSupport388_suffix_011
def ridgeSupport388_suffix_009 : List Nat := ridgeSupport388_009 ++ ridgeSupport388_suffix_010
def ridgeSupport388_suffix_008 : List Nat := ridgeSupport388_008 ++ ridgeSupport388_suffix_009
def ridgeSupport388_suffix_007 : List Nat := ridgeSupport388_007 ++ ridgeSupport388_suffix_008
def ridgeSupport388_suffix_006 : List Nat := ridgeSupport388_006 ++ ridgeSupport388_suffix_007
def ridgeSupport388_suffix_005 : List Nat := ridgeSupport388_005 ++ ridgeSupport388_suffix_006
def ridgeSupport388_suffix_004 : List Nat := ridgeSupport388_004 ++ ridgeSupport388_suffix_005
def ridgeSupport388_suffix_003 : List Nat := ridgeSupport388_003 ++ ridgeSupport388_suffix_004
def ridgeSupport388_suffix_002 : List Nat := ridgeSupport388_002 ++ ridgeSupport388_suffix_003
def ridgeSupport388_suffix_001 : List Nat := ridgeSupport388_001 ++ ridgeSupport388_suffix_002
def ridgeSupport388_suffix_000 : List Nat := ridgeSupport388_000 ++ ridgeSupport388_suffix_001
theorem ridgeSupport388_source : candidateSupports 388 =
    (PackedRawNatGrowth.readList 13 355 ridgeSupport388_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
