module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public meta import CertificateNumbers
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
cert_ridgeSupport_2 518 7398 7399 7406 7408 7412 7414 7418 7420 7670 7671 7672 7673 7674 7675 8045 8053 8057
cert_ridgeSupport_code_2 518
cert_ridgeSupport_rest 518 000 0
cert_ridgeSupport_rest 518 001 416
cert_ridgeSupport_rest 518 002 832
cert_ridgeSupport_rest 518 003 1248
cert_ridgeSupport_rest 518 004 1664
cert_ridgeSupport_rest 518 005 2080
cert_ridgeSupport_rest 518 006 2496
cert_ridgeSupport_rest 518 007 2912
cert_ridgeSupport_rest 518 008 3328
cert_ridgeSupport_rest 518 009 3744
cert_ridgeSupport_rest 518 010 3965
cert_ridgeSupport_suffix_2 518 010
cert_ridgeSupport_suffix 518 009 010
cert_ridgeSupport_suffix 518 008 009
cert_ridgeSupport_suffix 518 007 008
cert_ridgeSupport_suffix 518 006 007
cert_ridgeSupport_suffix 518 005 006
cert_ridgeSupport_suffix 518 004 005
cert_ridgeSupport_suffix 518 003 004
cert_ridgeSupport_suffix 518 002 003
cert_ridgeSupport_suffix 518 001 002
cert_ridgeSupport_suffix 518 000 001
cert_ridgeSupport_source 518 13 305
end Papers.RationalityTen.RootedCaches.RootedSixBase02
