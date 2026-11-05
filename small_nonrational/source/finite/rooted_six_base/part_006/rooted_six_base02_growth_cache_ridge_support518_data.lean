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
def ridgeSupport518_000 : List Nat := [4,33,35,36,127,128,130,135,137,151,152,154,159,161,163,164,166,171,173,530,552,553,555,556,559,560,561,563,564,566,571,572]
def ridgeSupport518_001 : List Nat := [573,574,576,577,580,581,582,584,585,587,592,593,594,595,597,598,601,602,603,605,606,608,613,614,1872,1873,1878,1879,1884,1885,1886,1887]
def ridgeSupport518_002 : List Nat := [1888,1889,1890,1891,1896,1897,1902,1903,1908,1909,1910,1911,1912,1913,1914,1915,1934,1935,1936,1937,1938,1939,1958,1959,1960,1961,1962,1963,1982,1983,1984,1985]
def ridgeSupport518_003 : List Nat := [1986,1987,2006,2007,2008,2009,2010,2011,2030,2031,2032,2033,2034,2035,2054,2055,2056,2057,2058,2059,2060,2062,2066,2068,2072,2074,2078,2079,2080,2081,2082,2083]
def ridgeSupport518_004 : List Nat := [2202,2203,2214,2215,2216,2218,2222,2224,2238,2239,2250,2251,2274,2275,2286,2287,2288,2290,2294,2296,2310,2311,2322,2323,2346,2347,2358,2359,2360,2362,2366,2368]
def ridgeSupport518_005 : List Nat := [2382,2383,2394,2395,4781,4783,4785,4787,4790,4794,4813,4815,4817,4819,4822,4826,4829,4831,4833,4835,4838,4842,5400,5401,5404,5405,5406,5407,5412,5413,5416,5417]
def ridgeSupport518_006 : List Nat := [5418,5419,5438,5439,5440,5441,5442,5443,5462,5463,5464,5465,5466,5467,5468,5470,5474,5476,5480,5482,5486,5487,5488,5489,5490,5491,5492,5494,5498,5500,5504,5506]
def ridgeSupport518_007 : List Nat := [5510,5511,5512,5513,5514,5515,5517,5518,5520,5521,5523,5524,5582,5584,5588,5590,5604,5605,5616,5617,5618,5620,5624,5626,5631,5633,5636,5638,5642,5644,5658,5659]
def ridgeSupport518_008 : List Nat := [5670,5671,5672,5674,5678,5680,5685,5687,5690,5692,5696,5698,5712,5713,5724,5725,5726,5728,5732,5734,5739,5741,7133,7135,7141,7143,7145,7147,7392,7393,7396,7397]
def ridgeSupport518_009 : List Nat := [7398,7399,7406,7408,7412,7414,7418,7420,7670,7671,7672,7673,7674,7675,8045,8053,8057]
def ridgeSupport518_code : Nat := 0x1f79fbafdb7bf7dfaefcf7e3befdf6e7e73eb9edcf4e7873bb9cfce6e72f3939c3ce0df5efa77cfbe5defef76cdb66bb335992cc165eb2ed972ca3650b215902c7963ab1bd8d6c6162eb1558a2c4f626b0dd86ac1960ab035812c035ffafd57e2be95f2af8d7c2bcb5e4aeb5752ba15ceaca564eb23590ac75636b1758aac4d622b0f586ac15602af957aabb55d2ae7572ab8d5c2adf56eab555a2ac9562aaf5572ab755aaacd562aaf556aa1d50aa83540a9fd4faa5752aa94d4a2a4b524a8fd47aa3b51ca8cd4625d52e6971cb865bf2dd96d4b5a5a72d1967cb365752b6959cac655f2ad4ada56929e94e4a024f927493849ba4d925692a489a44920e90647c23d91e48f0477a3b91c68e2465a32917e8be45822b91548a8453a29913689a411a08904282040fa07903481840a204901c80c405a029012808403a018fe67f23f89fc0fde7ee3ed9f68fb27d83eb9f58f867c23e09f00f7e7be3d59ea8f527a83d39e98f267923c89e40f1e78e3bd9de8ef27783bb9dd8eea7743b79db8ed27683b19d88ec27603af9d78eba75c3ab9d58ea275013309944c025e12e896c4b425912b09544a62521288940496249124091848a244120890047c23d11e08ec46c23411988c446022f11608ac45222810902b41560a6052028c14209f04d026012e089043820810007f012008c042004
def ridgeSupport518_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport518_code
def ridgeSupport518_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport518_code
def ridgeSupport518_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport518_code
def ridgeSupport518_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport518_code
def ridgeSupport518_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport518_code
def ridgeSupport518_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport518_code
def ridgeSupport518_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport518_code
def ridgeSupport518_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport518_code
def ridgeSupport518_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport518_code
def ridgeSupport518_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport518_code
def ridgeSupport518_rest_010 : Nat := PackedRawNatGrowth.drop 3965 ridgeSupport518_code
def ridgeSupport518_suffix_010 : List Nat := []
def ridgeSupport518_suffix_009 : List Nat := ridgeSupport518_009 ++ ridgeSupport518_suffix_010
def ridgeSupport518_suffix_008 : List Nat := ridgeSupport518_008 ++ ridgeSupport518_suffix_009
def ridgeSupport518_suffix_007 : List Nat := ridgeSupport518_007 ++ ridgeSupport518_suffix_008
def ridgeSupport518_suffix_006 : List Nat := ridgeSupport518_006 ++ ridgeSupport518_suffix_007
def ridgeSupport518_suffix_005 : List Nat := ridgeSupport518_005 ++ ridgeSupport518_suffix_006
def ridgeSupport518_suffix_004 : List Nat := ridgeSupport518_004 ++ ridgeSupport518_suffix_005
def ridgeSupport518_suffix_003 : List Nat := ridgeSupport518_003 ++ ridgeSupport518_suffix_004
def ridgeSupport518_suffix_002 : List Nat := ridgeSupport518_002 ++ ridgeSupport518_suffix_003
def ridgeSupport518_suffix_001 : List Nat := ridgeSupport518_001 ++ ridgeSupport518_suffix_002
def ridgeSupport518_suffix_000 : List Nat := ridgeSupport518_000 ++ ridgeSupport518_suffix_001
theorem ridgeSupport518_source : candidateSupports 518 =
    (PackedRawNatGrowth.readList 13 305 ridgeSupport518_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
