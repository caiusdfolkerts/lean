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
def ridgeSupport69_000 : List Nat := [1,15,19,20,21,131,132,135,136,141,143,144,147,148,153,155,156,159,160,165,359,361,362,365,367,371,373,374,377,379,383,385]
def ridgeSupport69_001 : List Nat := [386,389,391,431,432,434,435,436,437,439,440,442,443,445,446,452,453,455,456,457,458,460,461,463,464,466,467,473,474,476,477,478]
def ridgeSupport69_002 : List Nat := [479,481,482,484,485,487,488,2104,2105,2106,2107,2108,2109,2110,2111,2116,2117,2122,2123,2128,2129,2130,2131,2132,2133,2134,2135,2140,2141,2146,2147,2152]
def ridgeSupport69_003 : List Nat := [2153,2154,2155,2156,2157,2176,2177,2178,2179,2180,2181,2200,2201,2202,2203,2204,2205,2224,2225,2226,2227,2228,2229,2248,2249,2250,2251,2252,2253,2272,2273,2274]
def ridgeSupport69_004 : List Nat := [2275,2276,2277,2296,2297,2298,2299,2300,2301,2305,2307,2311,2313,2317,2319,2590,2591,2608,2609,2626,2627,2635,2637,2641,2643,2644,2645,2662,2663,2680,2681,2698]
def ridgeSupport69_005 : List Nat := [2699,2707,2709,2713,2715,2716,2717,2734,2735,2752,2753,2770,2771,2779,2781,2785,2787,2788,2789,3880,3881,3892,3893,3916,3917,3928,3929,3943,3945,3949,3951,3952]
def ridgeSupport69_006 : List Nat := [3953,3964,3965,3988,3989,4000,4001,4015,4017,4021,4023,4024,4025,4036,4037,4060,4061,4072,4073,4087,4089,4093,4095,7084,7085,7086,7087,7088,7089,7720,7721,7722]
def ridgeSupport69_007 : List Nat := [7723,7724,7725,7744,7745,7746,7747,7748,7749,7756,7757,7758,7759,7760,7761,7819,7821,7828,7829,7837,7839,7846,7847,7855,7857,7864,7865,8113,8115,8119,8121,8131]
def ridgeSupport69_008 : List Nat := [8133,8137,8139,8149,8151,8155,8157]
def ridgeSupport69_code : Nat := 0x1fdd7f6dfd77f55fcb7f25fc57f0dfb97eddfb37ec5eb97ae1eb17abdea77a99e9f7a75e957a51e8d7a2de517941e4f7939e4d7931e457911e437909e417901e2d78b1e2b78a9e2978a1bb16ec1baf6eb9bad6eb0fff3ff4ff93fdcfe93fa0fdd3f70fc53f10fb93ee0fb73ed4fb13ebcfa13e80f953e50f7d3df0f713dc0f6f3db4f693d9cf593d60f4d3d30f353cd0f293ca0ae52b90ae32b84add2b6cad32b48ac12b00aaf2ab8a9d2a70a9b2a64a952a4ca8b2a28a7929e0a672998a552950a532944a4d292ca432908a3128c0a1f287890f2434909241c90324048fd23f08fb23e88f923e08e523908e323888e123808cd23308cb23288c923208b522d08b322c88b122c089d227089b2268899226088522108832208881220086d21b086b21a886921a0863218885d2170857215885521508532148851214084b2128845211083f20f883d20f083b20e883920e01e8079c1e507901e207841df07781dd07701da07641d307481d0073c1cd07301ca07241c8071c1c507101be06f41bb06e81b806dc1b506d01b306c81b006bc1870614182060417f05ec17905d817505cc16f05b416a05a416702940a0027c09c026c0990250093024008f0234088021c084020c0150050013003c001
def ridgeSupport69_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport69_code
def ridgeSupport69_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport69_code
def ridgeSupport69_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport69_code
def ridgeSupport69_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport69_code
def ridgeSupport69_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport69_code
def ridgeSupport69_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport69_code
def ridgeSupport69_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport69_code
def ridgeSupport69_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport69_code
def ridgeSupport69_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport69_code
def ridgeSupport69_rest_009 : Nat := PackedRawNatGrowth.drop 3682 ridgeSupport69_code
def ridgeSupport69_suffix_009 : List Nat := []
def ridgeSupport69_suffix_008 : List Nat := ridgeSupport69_008 ++ ridgeSupport69_suffix_009
def ridgeSupport69_suffix_007 : List Nat := ridgeSupport69_007 ++ ridgeSupport69_suffix_008
def ridgeSupport69_suffix_006 : List Nat := ridgeSupport69_006 ++ ridgeSupport69_suffix_007
def ridgeSupport69_suffix_005 : List Nat := ridgeSupport69_005 ++ ridgeSupport69_suffix_006
def ridgeSupport69_suffix_004 : List Nat := ridgeSupport69_004 ++ ridgeSupport69_suffix_005
def ridgeSupport69_suffix_003 : List Nat := ridgeSupport69_003 ++ ridgeSupport69_suffix_004
def ridgeSupport69_suffix_002 : List Nat := ridgeSupport69_002 ++ ridgeSupport69_suffix_003
def ridgeSupport69_suffix_001 : List Nat := ridgeSupport69_001 ++ ridgeSupport69_suffix_002
def ridgeSupport69_suffix_000 : List Nat := ridgeSupport69_000 ++ ridgeSupport69_suffix_001
theorem ridgeSupport69_source : candidateSupports 69 =
    (PackedRawNatGrowth.readList 14 263 ridgeSupport69_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
