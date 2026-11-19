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
def ridgeSupport261_000 : List Nat := [3,17,20,22,24,142,145,146,149,152,166,169,170,173,176,191,192,195,196,201,370,372,375,376,378,394,396,399,400,402,419,421]
def ridgeSupport261_001 : List Nat := [422,425,427,430,431,433,434,437,438,439,441,442,444,449,450,472,474,475,477,478,480,482,483,485,486,489,490,493,495,496,498,499]
def ridgeSupport261_002 : List Nat := [501,503,504,506,507,510,511,2106,2107,2112,2113,2116,2117,2118,2119,2120,2121,2126,2127,2130,2131,2136,2137,2140,2141,2142,2143,2144,2145,2150,2151,2164]
def ridgeSupport261_003 : List Nat := [2165,2166,2167,2168,2169,2188,2189,2190,2191,2192,2193,2212,2213,2214,2215,2216,2217,2236,2237,2238,2239,2240,2241,2260,2261,2262,2263,2264,2265,2284,2285,2286]
def ridgeSupport261_004 : List Nat := [2287,2288,2289,2297,2300,2303,2306,2308,2309,2310,2311,2312,2313,2314,2316,2594,2595,2612,2613,2630,2631,2632,2634,2638,2640,2648,2649,2736,2737,2754,2755,2772]
def ridgeSupport261_005 : List Nat := [2773,2777,2780,2783,2786,2790,2791,2808,2809,2826,2827,2844,2845,2849,2852,2855,2858,2862,2863,3884,3885,3896,3897,3920,3921,3932,3933,3940,3942,3946,3948,4026]
def ridgeSupport261_006 : List Nat := [4027,4038,4039,4062,4063,4074,4075,4085,4088,4091,4094,4098,4099,4110,4111,4134,4135,4146,4147,4157,4160,4163,4166,7096,7097,7098,7099,7100,7101,7732,7733,7734]
def ridgeSupport261_007 : List Nat := [7735,7736,7737,7745,7748,7751,7753,7754,7755,7757,7760,7763,7765,7766,7767,7816,7818,7832,7833,7853,7856,7866,7867,7871,7874,7884,7885,8110,8112,8116,8118,8147]
cert_ridgeSupport_7 261 008 8150 8153 8156 8165 8168 8171 8174
cert_ridgeSupport_code_3 261
cert_ridgeSupport_rest_2 261 000 0
cert_ridgeSupport_rest_2 261 001 448
cert_ridgeSupport_rest_2 261 002 896
cert_ridgeSupport_rest_2 261 003 1344
cert_ridgeSupport_rest_2 261 004 1792
cert_ridgeSupport_rest_2 261 005 2240
cert_ridgeSupport_rest_2 261 006 2688
cert_ridgeSupport_rest_2 261 007 3136
cert_ridgeSupport_rest_2 261 008 3584
cert_ridgeSupport_rest_2 261 009 3682
cert_ridgeSupport_suffix_4 261 009
cert_ridgeSupport_suffix_3 261 008 009
cert_ridgeSupport_suffix_3 261 007 008
cert_ridgeSupport_suffix_3 261 006 007
cert_ridgeSupport_suffix_3 261 005 006
cert_ridgeSupport_suffix_3 261 004 005
cert_ridgeSupport_suffix_3 261 003 004
cert_ridgeSupport_suffix_3 261 002 003
cert_ridgeSupport_suffix_3 261 001 002
cert_ridgeSupport_suffix_3 261 000 001
cert_ridgeSupport_source_3 261 14 263
end Papers.RationalityTen.RootedCaches.RootedSixExtra00
