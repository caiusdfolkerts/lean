module
prelude
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
def ridgeSupport261_008 : List Nat := [8150,8153,8156,8165,8168,8171,8174]
def ridgeSupport261_code : Nat := 0x1fee7fadfe87f95fdc7f65fd67f4dfb67ed1fb07eb9ecd7b31ec27afdebb7ae9eb07ab5e997a61e8a7a21e577959e55794de507935e4b7929e49791de447905e3978e1e3778d9e3578d1bbd6ef1bbb6ee9bb96ee1046410d04040f503340c9027409900f40390034008ffe3fecff83fd4feb3fa8fdf3f78fc73f18fbb3ee8f6c3da8f663d90f5d3d70f513d40f393ce0f2d3cb0b2f2cb8b2a2c9cb242c84b1d2c70b0b2c28af92be0ae72b98ae22b7cadc2b64ad52b50ac32b08ab12ac0a592960a502938a4a2920a472918a3528d0a23288890c242890924209072418905241090223fc8fc23e48f123c08ef23b88ed23b08d923608d723588d523508c123008bf22f88bd22f08a922a08a722988a52290891224088f223888d223087921e087721d887521d08672198861218085f217885d21708592160853214884f2138849212084721188452110841210083b20e81ff07f81fb07e81f807dc1f507cc1f207c01ef07b41ea07a41e607941e307881e007781dd076c1da07601c207041bc06e81b906dc1b606d41b206c41af06b81ab06a41a606941a30648190063c18c062817a05e017705d017203240c4030c0c002fc0b002b40aa02a40a602600950248091023801800580140044003
def ridgeSupport261_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport261_code
def ridgeSupport261_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport261_code
def ridgeSupport261_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport261_code
def ridgeSupport261_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport261_code
def ridgeSupport261_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport261_code
def ridgeSupport261_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport261_code
def ridgeSupport261_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport261_code
def ridgeSupport261_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport261_code
def ridgeSupport261_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport261_code
def ridgeSupport261_rest_009 : Nat := PackedRawNatGrowth.drop 3682 ridgeSupport261_code
def ridgeSupport261_suffix_009 : List Nat := []
def ridgeSupport261_suffix_008 : List Nat := ridgeSupport261_008 ++ ridgeSupport261_suffix_009
def ridgeSupport261_suffix_007 : List Nat := ridgeSupport261_007 ++ ridgeSupport261_suffix_008
def ridgeSupport261_suffix_006 : List Nat := ridgeSupport261_006 ++ ridgeSupport261_suffix_007
def ridgeSupport261_suffix_005 : List Nat := ridgeSupport261_005 ++ ridgeSupport261_suffix_006
def ridgeSupport261_suffix_004 : List Nat := ridgeSupport261_004 ++ ridgeSupport261_suffix_005
def ridgeSupport261_suffix_003 : List Nat := ridgeSupport261_003 ++ ridgeSupport261_suffix_004
def ridgeSupport261_suffix_002 : List Nat := ridgeSupport261_002 ++ ridgeSupport261_suffix_003
def ridgeSupport261_suffix_001 : List Nat := ridgeSupport261_001 ++ ridgeSupport261_suffix_002
def ridgeSupport261_suffix_000 : List Nat := ridgeSupport261_000 ++ ridgeSupport261_suffix_001
theorem ridgeSupport261_source : candidateSupports 261 =
    (PackedRawNatGrowth.readList 14 263 ridgeSupport261_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
