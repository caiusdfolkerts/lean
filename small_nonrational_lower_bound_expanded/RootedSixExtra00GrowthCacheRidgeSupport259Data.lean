module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public meta import CertificateNumbers
public import RootedSixExtra00GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport259_000 : List Nat := [3,7,10,12,14,142,144,147,148,150,166,168,171,172,174,191,193,194,197,199,214,216,219,220,222,238,240,243,244,246,263,265]
def ridgeSupport259_001 : List Nat := [266,269,271,274,275,277,278,281,282,283,285,286,288,293,294,316,318,319,321,322,324,326,327,329,330,333,334,337,339,340,342,343]
def ridgeSupport259_002 : List Nat := [345,347,348,350,351,354,355,1866,1867,1872,1873,1876,1877,1878,1879,1880,1881,1886,1887,1890,1891,1896,1897,1900,1901,1902,1903,1904,1905,1910,1911,1924]
def ridgeSupport259_003 : List Nat := [1925,1926,1927,1928,1929,1948,1949,1950,1951,1952,1953,1972,1973,1974,1975,1976,1977,1996,1997,1998,1999,2000,2001,2020,2021,2022,2023,2024,2025,2044,2045,2046]
def ridgeSupport259_004 : List Nat := [2047,2048,2049,2057,2060,2063,2066,2068,2069,2070,2071,2072,2073,2074,2076,2588,2589,2600,2601,2624,2625,2636,2637,2644,2646,2650,2652,2730,2731,2742,2743,2766]
def ridgeSupport259_005 : List Nat := [2767,2778,2779,2789,2792,2795,2798,2802,2803,2814,2815,2838,2839,2850,2851,2861,2864,2867,2870,3356,3357,3368,3369,3392,3393,3404,3405,3412,3414,3418,3420,3498]
def ridgeSupport259_006 : List Nat := [3499,3510,3511,3534,3535,3546,3547,3557,3560,3563,3566,3570,3571,3582,3583,3606,3607,3618,3619,3629,3632,3635,3638,7060,7061,7062,7063,7064,7065,7684,7685,7686]
def ridgeSupport259_007 : List Nat := [7687,7688,7689,7697,7700,7703,7705,7706,7707,7709,7712,7715,7717,7718,7719,7822,7824,7828,7830,7859,7862,7865,7868,7877,7880,7883,7886,7990,7992,7996,7998,8027]
cert_ridgeSupport_7 259 008 8030 8033 8036 8045 8048 8051 8054
cert_ridgeSupport_code_3 259
cert_ridgeSupport_rest_2 259 000 0
cert_ridgeSupport_rest_2 259 001 448
cert_ridgeSupport_rest_2 259 002 896
cert_ridgeSupport_rest_2 259 003 1344
cert_ridgeSupport_rest_2 259 004 1792
cert_ridgeSupport_rest_2 259 005 2240
cert_ridgeSupport_rest_2 259 006 2688
cert_ridgeSupport_rest_2 259 007 3136
cert_ridgeSupport_rest_2 259 008 3584
cert_ridgeSupport_rest_2 259 009 3682
cert_ridgeSupport_suffix_4 259 009
cert_ridgeSupport_suffix_3 259 008 009
cert_ridgeSupport_suffix_3 259 007 008
cert_ridgeSupport_suffix_3 259 006 007
cert_ridgeSupport_suffix_3 259 005 006
cert_ridgeSupport_suffix_3 259 004 005
cert_ridgeSupport_suffix_3 259 003 004
cert_ridgeSupport_suffix_3 259 002 003
cert_ridgeSupport_suffix_3 259 001 002
cert_ridgeSupport_suffix_3 259 000 001
cert_ridgeSupport_source_3 259 14 263
end Papers.RationalityTen.RootedCaches.RootedSixExtra00
