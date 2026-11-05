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
def ridgeSupport134_000 : List Nat := [2,31,34,35,103,104,106,111,113,138,141,143,146,148,150,153,155,158,160,528,531,533,534,536,537,539,541,542,544,545,548,549]
def ridgeSupport134_001 : List Nat := [552,554,555,557,558,560,562,563,565,566,569,570,595,596,598,599,600,601,603,604,606,607,609,610,1868,1869,1874,1875,1876,1877,1878,1879]
def ridgeSupport134_002 : List Nat := [1882,1883,1888,1889,1892,1893,1898,1899,1900,1901,1902,1903,1906,1907,1912,1913,1922,1923,1924,1925,1926,1927,1946,1947,1948,1949,1950,1951,1970,1971,1972,1973]
def ridgeSupport134_003 : List Nat := [1974,1975,1994,1995,1996,1997,1998,1999,2018,2019,2020,2021,2022,2023,2042,2043,2044,2045,2046,2047,2063,2065,2066,2067,2068,2069,2070,2071,2073,2076,2079,2082]
def ridgeSupport134_004 : List Nat := [2128,2129,2140,2141,2145,2148,2151,2154,2164,2165,2176,2177,2200,2201,2212,2213,2217,2220,2223,2226,2236,2237,2248,2249,2342,2343,2354,2355,2363,2365,2369,2371]
def ridgeSupport134_005 : List Nat := [2378,2379,2390,2391,4749,4751,4753,4755,4758,4762,4796,4798,4800,4802,4807,4811,4812,4814,4816,4818,4823,4827,5396,5397,5402,5403,5404,5405,5408,5409,5414,5415]
def ridgeSupport134_006 : List Nat := [5416,5417,5426,5427,5428,5429,5430,5431,5450,5451,5452,5453,5454,5455,5471,5473,5474,5475,5476,5477,5478,5479,5481,5484,5487,5490,5495,5497,5498,5499,5500,5501]
def ridgeSupport134_007 : List Nat := [5502,5503,5505,5508,5511,5514,5516,5517,5522,5524,5525,5527,5529,5532,5535,5538,5548,5549,5560,5561,5565,5568,5571,5574,5576,5581,5583,5586,5589,5592,5602,5603]
def ridgeSupport134_008 : List Nat := [5614,5615,5619,5622,5625,5628,5630,5635,5693,5695,5699,5701,5708,5709,5720,5721,5729,5731,5735,5737,5740,5742,7125,7127,7136,7138,7140,7142,7388,7389,7394,7395]
def ridgeSupport134_009 : List Nat := [7396,7397,7401,7404,7407,7410,7421,7423,7658,7659,7660,7661,7662,7663,8037,8048,8052]
def ridgeSupport134_code : Nat := 0x1f74fb87d97bdfdeeef6f7b3bd7deae7ff3f79e5cefe7673a79cbce4e71f38b9bbcdcdf36f937c5be0debef56cdd66cb34d99ecc7661b2cd962c9b64cb22d90ec7f63db01d7fabf95f9afb57cebdf5eeaf1d78abb15d5ae9573eb9b5c8ae3570eb815bdadcd6e2b5b5acad1567eb39599acbd656b29592ac6d632b15587ac25606aff57eabed5f2af757aabcd5deae556fab655a6acf566ab2d592ac7562ab0d57ea9f54eaa6d532a9754aa9bd4daa6b534a99d4caa53528a93d49aa43520a8ed472a3751aa8ad4525b72d79694b4259d2cc965cb1e5852c095f4af2535296949ca4651f28d4aba55929694a4a1a50527a93b499a4c924e926464a32117a8bc45922bd1588a9452a291132898440a2010ea874435219d0c886142ea1710a2850411207d03881940ba05902a814409a04902280f3ff9ff8ffa7fc3fd9fe8fce7e63f29f90fc67e23e79f38f9a7cc3e59f28f6e7b63da9ed0f667b23cf9e78f3a79c3cd9e68f0e7863c29e10f067823bc9de0ee67723b79db8eda76c3b59da8eca7643b09d80eb675a3ab9d58eaa7543a99d48e9a74c13109844be25e12e096c4b225812b89584a825311d08e446c23511988c846022e11688ac454228112889044222010f087443621910c085842a213108028013c09b04c8258128092047823411407103781a80d0067011808803e002
def ridgeSupport134_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport134_code
def ridgeSupport134_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport134_code
def ridgeSupport134_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport134_code
def ridgeSupport134_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport134_code
def ridgeSupport134_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport134_code
def ridgeSupport134_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport134_code
def ridgeSupport134_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport134_code
def ridgeSupport134_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport134_code
def ridgeSupport134_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport134_code
def ridgeSupport134_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport134_code
def ridgeSupport134_rest_010 : Nat := PackedRawNatGrowth.drop 3965 ridgeSupport134_code
def ridgeSupport134_suffix_010 : List Nat := []
def ridgeSupport134_suffix_009 : List Nat := ridgeSupport134_009 ++ ridgeSupport134_suffix_010
def ridgeSupport134_suffix_008 : List Nat := ridgeSupport134_008 ++ ridgeSupport134_suffix_009
def ridgeSupport134_suffix_007 : List Nat := ridgeSupport134_007 ++ ridgeSupport134_suffix_008
def ridgeSupport134_suffix_006 : List Nat := ridgeSupport134_006 ++ ridgeSupport134_suffix_007
def ridgeSupport134_suffix_005 : List Nat := ridgeSupport134_005 ++ ridgeSupport134_suffix_006
def ridgeSupport134_suffix_004 : List Nat := ridgeSupport134_004 ++ ridgeSupport134_suffix_005
def ridgeSupport134_suffix_003 : List Nat := ridgeSupport134_003 ++ ridgeSupport134_suffix_004
def ridgeSupport134_suffix_002 : List Nat := ridgeSupport134_002 ++ ridgeSupport134_suffix_003
def ridgeSupport134_suffix_001 : List Nat := ridgeSupport134_001 ++ ridgeSupport134_suffix_002
def ridgeSupport134_suffix_000 : List Nat := ridgeSupport134_000 ++ ridgeSupport134_suffix_001
theorem ridgeSupport134_source : candidateSupports 134 =
    (PackedRawNatGrowth.readList 13 305 ridgeSupport134_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
