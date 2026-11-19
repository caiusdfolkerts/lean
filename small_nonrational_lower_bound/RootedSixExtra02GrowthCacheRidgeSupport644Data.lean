module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public meta import CertificateNumbers
public import RootedSixExtra02GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport644_000 : List Nat := [19,35,61,64,66,150,151,152,153,160,161,356,357,358,361,362,367,368,373,375,397,399,401,403,405,410,411,413,416,553,554,555]
def ridgeSupport644_001 : List Nat := [558,559,564,565,570,572,594,596,598,600,602,607,608,610,613,901,905,906,907,908,910,911,918,920,944,946,948,949,951,953,954,958]
def ridgeSupport644_002 : List Nat := [963,964,966,968,970,971,973,975,976,980,982,987,988,1628,1633,1642,1644,1710,1711,1720,1721,1726,1727,1730,1732,1736,1737,1743,1746,1758,1759,1768]
def ridgeSupport644_003 : List Nat := [1769,1796,1801,1806,1807,1810,1812,1816,1817,1822,1823,1832,1833,1846,1847,1856,1857,1868,1873,1882,1884,1950,1951,1960,1961,1966,1967,1970,1972,1976,1977,1983]
def ridgeSupport644_004 : List Nat := [1986,1998,1999,2008,2009,2036,2041,2046,2047,2050,2052,2056,2057,2062,2063,2072,2073,2086,2087,2096,2097,2188,2190,2200,2202,2216,2217,2228,2229,2330,2335,2342]
def ridgeSupport644_005 : List Nat := [2347,2362,2363,2374,2375,3188,3193,3202,3204,3222,3223,3232,3233,3270,3271,3280,3281,3286,3287,3290,3292,3296,3297,3303,3306,3308,3313,3318,3319,3322,3324,3328]
def ridgeSupport644_006 : List Nat := [3329,3366,3367,3376,3377,3390,3391,3400,3401,3710,3711,3722,3723,4814,4815,4822,4823,5144,5149,5150,5154,5156,5161,5162,5166,5174,5175,5188,5189,5241,5244,5247]
def ridgeSupport644_007 : List Nat := [5251,5410,5411,5446,5447,5608,5609,5910,5911,5920,5921,5925,5926,5927,5928,5933,5934,5958,5959,5968,5969,5973,5974,5975,5976,5981,5982,6014,6015,6017,6019,6051]
def ridgeSupport644_008 : List Nat := [6052,6053,6054,6242,6244,6255,6258,6273,6274,6275,6276,6281,6282]
cert_ridgeSupport_code_3 644
cert_ridgeSupport_rest_2 644 000 0
cert_ridgeSupport_rest_2 644 001 416
cert_ridgeSupport_rest_2 644 002 832
cert_ridgeSupport_rest_2 644 003 1248
cert_ridgeSupport_rest_2 644 004 1664
cert_ridgeSupport_rest_2 644 005 2080
cert_ridgeSupport_rest_2 644 006 2496
cert_ridgeSupport_rest_2 644 007 2912
cert_ridgeSupport_rest_2 644 008 3328
cert_ridgeSupport_rest_2 644 009 3497
cert_ridgeSupport_suffix_4 644 009
cert_ridgeSupport_suffix_3 644 008 009
cert_ridgeSupport_suffix_3 644 007 008
cert_ridgeSupport_suffix_3 644 006 007
cert_ridgeSupport_suffix_3 644 005 006
cert_ridgeSupport_suffix_3 644 004 005
cert_ridgeSupport_suffix_3 644 003 004
cert_ridgeSupport_suffix_3 644 002 003
cert_ridgeSupport_suffix_3 644 001 002
cert_ridgeSupport_suffix_3 644 000 001
cert_ridgeSupport_source_3 644 13 269
end Papers.RationalityTen.RootedCaches.RootedSixExtra02
