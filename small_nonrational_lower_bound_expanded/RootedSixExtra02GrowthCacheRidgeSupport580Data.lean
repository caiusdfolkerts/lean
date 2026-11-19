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
def ridgeSupport580_000 : List Nat := [17,33,59,64,65,126,127,128,129,136,137,355,357,359,361,363,368,369,371,374,376,378,380,382,384,389,390,392,395,552,554,556]
def ridgeSupport580_001 : List Nat := [558,560,565,566,568,571,573,575,577,579,581,586,587,589,592,902,904,906,907,909,911,912,916,921,923,925,927,928,930,932,933,937]
def ridgeSupport580_002 : List Nat := [942,965,966,968,969,972,973,974,976,977,979,986,987,1634,1639,1640,1645,1704,1705,1718,1719,1724,1726,1732,1733,1738,1739,1745,1747,1752,1753,1766]
def ridgeSupport580_003 : List Nat := [1767,1800,1801,1802,1807,1808,1813,1814,1815,1828,1829,1834,1835,1852,1853,1858,1859,1874,1879,1880,1885,1944,1945,1958,1959,1964,1966,1972,1973,1978,1979,1985]
def ridgeSupport580_004 : List Nat := [1987,1992,1993,2006,2007,2040,2041,2042,2047,2048,2053,2054,2055,2068,2069,2074,2075,2092,2093,2098,2099,2186,2191,2198,2203,2218,2219,2230,2231,2258,2263,2270]
def ridgeSupport580_005 : List Nat := [2275,2290,2291,2302,2303,3194,3199,3200,3205,3216,3217,3230,3231,3264,3265,3278,3279,3284,3286,3292,3293,3298,3299,3305,3307,3312,3313,3314,3319,3320,3325,3326]
def ridgeSupport580_006 : List Nat := [3327,3360,3361,3374,3375,3384,3385,3398,3399,3678,3679,3690,3691,4782,4783,4790,4791,5144,5146,5153,5155,5156,5158,5165,5167,5176,5177,5182,5183,5241,5243,5248]
def ridgeSupport580_007 : List Nat := [5250,5414,5415,5450,5451,5604,5605,5904,5905,5918,5919,5928,5929,5931,5932,5933,5935,5952,5953,5966,5967,5976,5977,5979,5980,5981,5983,6015,6016,6017,6018,6033]
def ridgeSupport580_008 : List Nat := [6034,6035,6036,6236,6238,6257,6259,6276,6277,6279,6280,6281,6283]
cert_ridgeSupport_code_3 580
cert_ridgeSupport_rest_2 580 000 0
cert_ridgeSupport_rest_2 580 001 416
cert_ridgeSupport_rest_2 580 002 832
cert_ridgeSupport_rest_2 580 003 1248
cert_ridgeSupport_rest_2 580 004 1664
cert_ridgeSupport_rest_2 580 005 2080
cert_ridgeSupport_rest_2 580 006 2496
cert_ridgeSupport_rest_2 580 007 2912
cert_ridgeSupport_rest_2 580 008 3328
cert_ridgeSupport_rest_2 580 009 3497
cert_ridgeSupport_suffix_4 580 009
cert_ridgeSupport_suffix_3 580 008 009
cert_ridgeSupport_suffix_3 580 007 008
cert_ridgeSupport_suffix_3 580 006 007
cert_ridgeSupport_suffix_3 580 005 006
cert_ridgeSupport_suffix_3 580 004 005
cert_ridgeSupport_suffix_3 580 003 004
cert_ridgeSupport_suffix_3 580 002 003
cert_ridgeSupport_suffix_3 580 001 002
cert_ridgeSupport_suffix_3 580 000 001
cert_ridgeSupport_source_3 580 13 269
end Papers.RationalityTen.RootedCaches.RootedSixExtra02
