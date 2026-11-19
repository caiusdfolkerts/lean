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
def ridgeSupport321_000 : List Nat := [10,20,26,31,33,144,145,146,147,148,149,216,217,218,219,220,221,275,277,279,280,282,284,285,289,294,318,319,320,323,324,325]
def ridgeSupport321_001 : List Nat := [327,332,334,372,373,374,375,376,377,431,433,435,436,438,440,441,445,450,474,475,476,479,480,481,483,488,490,515,517,519,520,522]
def ridgeSupport321_002 : List Nat := [524,525,529,534,558,559,560,563,564,565,567,572,574,599,601,602,604,605,607,609,610,612,613,617,618,1895,1897,1906,1911,1914,1915,1924]
def ridgeSupport321_003 : List Nat := [1925,1962,1963,1972,1973,1985,1988,1994,1995,1999,2001,2004,2005,2010,2011,2015,2017,2020,2021,2026,2031,2058,2059,2068,2069,2082,2083,2092,2093,2135,2137,2146]
def ridgeSupport321_004 : List Nat := [2151,2154,2155,2164,2165,2202,2203,2212,2213,2225,2228,2234,2235,2239,2241,2244,2245,2250,2251,2255,2257,2260,2261,2266,2271,2298,2299,2308,2309,2322,2323,2332]
def ridgeSupport321_005 : List Nat := [2333,2596,2601,2608,2613,2640,2641,2652,2653,2741,2743,2753,2755,2786,2787,2798,2799,2903,2905,2914,2919,2922,2923,2932,2933,2970,2971,2980,2981,2993,2996,3002]
def ridgeSupport321_006 : List Nat := [3003,3007,3009,3012,3013,3018,3019,3023,3025,3028,3029,3034,3039,3066,3067,3076,3077,3090,3091,3100,3101,3364,3369,3376,3381,3408,3409,3420,3421,3509,3511,3521]
def ridgeSupport321_007 : List Nat := [3523,3554,3555,3566,3567,3892,3897,3904,3909,3936,3937,3948,3949,4037,4039,4049,4051,4082,4083,4094,4095,7074,7075,7110,7111,7206,7207,7673,7676,7687,7689,7710]
def ridgeSupport321_008 : List Nat := [7711,7714,7716,7717,7718,7721,7724,7735,7737,7758,7759,7762,7764,7765,7766,7829,7830,7831,7832,7864,7866,7868,7869,7889,7892,7903,7905,7926,7927,7930,7932,7933]
def ridgeSupport321_009 : List Nat := [7934,7997,7998,7999,8000,8032,8034,8036,8037,8117,8118,8119,8120,8152,8154,8156,8157]
cert_ridgeSupport_code_3 321
cert_ridgeSupport_rest_2 321 000 0
cert_ridgeSupport_rest_2 321 001 448
cert_ridgeSupport_rest_2 321 002 896
cert_ridgeSupport_rest_2 321 003 1344
cert_ridgeSupport_rest_2 321 004 1792
cert_ridgeSupport_rest_2 321 005 2240
cert_ridgeSupport_rest_2 321 006 2688
cert_ridgeSupport_rest_2 321 007 3136
cert_ridgeSupport_rest_2 321 008 3584
cert_ridgeSupport_rest_2 321 009 4032
cert_ridgeSupport_rest_2 321 010 4270
cert_ridgeSupport_suffix_4 321 010
cert_ridgeSupport_suffix_3 321 009 010
cert_ridgeSupport_suffix_3 321 008 009
cert_ridgeSupport_suffix_3 321 007 008
cert_ridgeSupport_suffix_3 321 006 007
cert_ridgeSupport_suffix_3 321 005 006
cert_ridgeSupport_suffix_3 321 004 005
cert_ridgeSupport_suffix_3 321 003 004
cert_ridgeSupport_suffix_3 321 002 003
cert_ridgeSupport_suffix_3 321 001 002
cert_ridgeSupport_suffix_3 321 000 001
cert_ridgeSupport_source_3 321 14 305
end Papers.RationalityTen.RootedCaches.RootedSixExtra00
