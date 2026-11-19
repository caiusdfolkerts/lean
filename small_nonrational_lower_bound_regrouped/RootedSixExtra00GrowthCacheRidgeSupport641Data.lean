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
def ridgeSupport641_000 : List Nat := [13,23,29,32,34,180,181,182,183,184,185,252,253,254,255,256,257,295,299,300,301,302,304,305,312,314,338,340,342,343,345,347]
def ridgeSupport641_001 : List Nat := [348,352,357,408,409,410,411,412,413,451,455,456,457,458,460,461,468,470,494,496,498,499,501,503,504,508,513,535,539,540,541,542]
def ridgeSupport641_002 : List Nat := [544,545,552,554,578,580,582,583,585,587,588,592,597,598,600,602,604,605,607,609,610,614,616,621,622,1888,1893,1902,1904,1922,1923,1932]
def ridgeSupport641_003 : List Nat := [1933,1970,1971,1980,1981,1986,1987,1990,1992,1996,1997,2003,2006,2008,2013,2018,2019,2022,2024,2028,2029,2066,2067,2076,2077,2090,2091,2100,2101,2128,2133,2142]
def ridgeSupport641_004 : List Nat := [2144,2162,2163,2172,2173,2210,2211,2220,2221,2226,2227,2230,2232,2236,2237,2243,2246,2248,2253,2258,2259,2262,2264,2268,2269,2306,2307,2316,2317,2330,2331,2340]
def ridgeSupport641_005 : List Nat := [2341,2670,2672,2682,2684,2710,2711,2722,2723,2812,2817,2824,2829,2856,2857,2868,2869,2896,2901,2910,2912,2930,2931,2940,2941,2978,2979,2988,2989,2994,2995,2998]
def ridgeSupport641_006 : List Nat := [3000,3004,3005,3011,3014,3016,3021,3026,3027,3030,3032,3036,3037,3074,3075,3084,3085,3098,3099,3108,3109,3438,3440,3450,3452,3478,3479,3490,3491,3580,3585,3592]
def ridgeSupport641_007 : List Nat := [3597,3624,3625,3636,3637,3966,3968,3978,3980,4006,4007,4018,4019,4108,4113,4120,4125,4152,4153,4164,4165,7080,7081,7116,7117,7212,7213,7678,7680,7691,7694,7709]
def ridgeSupport641_008 : List Nat := [7710,7711,7712,7717,7718,7726,7728,7739,7742,7757,7758,7759,7760,7765,7766,7846,7847,7849,7851,7883,7884,7885,7886,7894,7896,7907,7910,7925,7926,7927,7928,7933]
def ridgeSupport641_009 : List Nat := [7934,8014,8015,8017,8019,8051,8052,8053,8054,8134,8135,8137,8139,8171,8172,8173,8174]
cert_ridgeSupport_code_3 641
cert_ridgeSupport_rest_2 641 000 0
cert_ridgeSupport_rest_2 641 001 448
cert_ridgeSupport_rest_2 641 002 896
cert_ridgeSupport_rest_2 641 003 1344
cert_ridgeSupport_rest_2 641 004 1792
cert_ridgeSupport_rest_2 641 005 2240
cert_ridgeSupport_rest_2 641 006 2688
cert_ridgeSupport_rest_2 641 007 3136
cert_ridgeSupport_rest_2 641 008 3584
cert_ridgeSupport_rest_2 641 009 4032
cert_ridgeSupport_rest_2 641 010 4270
cert_ridgeSupport_suffix_4 641 010
cert_ridgeSupport_suffix_3 641 009 010
cert_ridgeSupport_suffix_3 641 008 009
cert_ridgeSupport_suffix_3 641 007 008
cert_ridgeSupport_suffix_3 641 006 007
cert_ridgeSupport_suffix_3 641 005 006
cert_ridgeSupport_suffix_3 641 004 005
cert_ridgeSupport_suffix_3 641 003 004
cert_ridgeSupport_suffix_3 641 002 003
cert_ridgeSupport_suffix_3 641 001 002
cert_ridgeSupport_suffix_3 641 000 001
cert_ridgeSupport_source_3 641 14 305
end Papers.RationalityTen.RootedCaches.RootedSixExtra00
