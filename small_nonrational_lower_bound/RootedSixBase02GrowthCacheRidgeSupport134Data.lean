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
def ridgeSupport134_000 : List Nat := [2,31,34,35,103,104,106,111,113,138,141,143,146,148,150,153,155,158,160,528,531,533,534,536,537,539,541,542,544,545,548,549]
def ridgeSupport134_001 : List Nat := [552,554,555,557,558,560,562,563,565,566,569,570,595,596,598,599,600,601,603,604,606,607,609,610,1868,1869,1874,1875,1876,1877,1878,1879]
def ridgeSupport134_002 : List Nat := [1882,1883,1888,1889,1892,1893,1898,1899,1900,1901,1902,1903,1906,1907,1912,1913,1922,1923,1924,1925,1926,1927,1946,1947,1948,1949,1950,1951,1970,1971,1972,1973]
def ridgeSupport134_003 : List Nat := [1974,1975,1994,1995,1996,1997,1998,1999,2018,2019,2020,2021,2022,2023,2042,2043,2044,2045,2046,2047,2063,2065,2066,2067,2068,2069,2070,2071,2073,2076,2079,2082]
def ridgeSupport134_004 : List Nat := [2128,2129,2140,2141,2145,2148,2151,2154,2164,2165,2176,2177,2200,2201,2212,2213,2217,2220,2223,2226,2236,2237,2248,2249,2342,2343,2354,2355,2363,2365,2369,2371]
def ridgeSupport134_005 : List Nat := [2378,2379,2390,2391,4749,4751,4753,4755,4758,4762,4796,4798,4800,4802,4807,4811,4812,4814,4816,4818,4823,4827,5396,5397,5402,5403,5404,5405,5408,5409,5414,5415]
def ridgeSupport134_006 : List Nat := [5416,5417,5426,5427,5428,5429,5430,5431,5450,5451,5452,5453,5454,5455,5471,5473,5474,5475,5476,5477,5478,5479,5481,5484,5487,5490,5495,5497,5498,5499,5500,5501]
def ridgeSupport134_007 : List Nat := [5502,5503,5505,5508,5511,5514,5516,5517,5522,5524,5525,5527,5529,5532,5535,5538,5548,5549,5560,5561,5565,5568,5571,5574,5576,5581,5583,5586,5589,5592,5602,5603]
def ridgeSupport134_008 : List Nat := [5614,5615,5619,5622,5625,5628,5630,5635,5693,5695,5699,5701,5708,5709,5720,5721,5729,5731,5735,5737,5740,5742,7125,7127,7136,7138,7140,7142,7388,7389,7394,7395]
cert_ridgeSupport_2 134 7396 7397 7401 7404 7407 7410 7421 7423 7658 7659 7660 7661 7662 7663 8037 8048 8052
cert_ridgeSupport_code_2 134
cert_ridgeSupport_rest 134 000 0
cert_ridgeSupport_rest 134 001 416
cert_ridgeSupport_rest 134 002 832
cert_ridgeSupport_rest 134 003 1248
cert_ridgeSupport_rest 134 004 1664
cert_ridgeSupport_rest 134 005 2080
cert_ridgeSupport_rest 134 006 2496
cert_ridgeSupport_rest 134 007 2912
cert_ridgeSupport_rest 134 008 3328
cert_ridgeSupport_rest 134 009 3744
cert_ridgeSupport_rest 134 010 3965
cert_ridgeSupport_suffix_2 134 010
cert_ridgeSupport_suffix 134 009 010
cert_ridgeSupport_suffix 134 008 009
cert_ridgeSupport_suffix 134 007 008
cert_ridgeSupport_suffix 134 006 007
cert_ridgeSupport_suffix 134 005 006
cert_ridgeSupport_suffix 134 004 005
cert_ridgeSupport_suffix 134 003 004
cert_ridgeSupport_suffix 134 002 003
cert_ridgeSupport_suffix 134 001 002
cert_ridgeSupport_suffix 134 000 001
cert_ridgeSupport_source 134 13 305
end Papers.RationalityTen.RootedCaches.RootedSixBase02
