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
def ridgeSupport193_000 : List Nat := [9,19,25,31,32,132,133,134,135,136,137,204,205,206,207,208,209,276,277,278,281,282,283,285,290,292,297,298,299,302,303,304]
def ridgeSupport193_001 : List Nat := [306,311,313,360,361,362,363,364,365,432,433,434,437,438,439,441,446,448,453,454,455,458,459,460,462,467,469,516,517,518,521,522]
def ridgeSupport193_002 : List Nat := [523,525,530,532,537,538,539,542,543,544,546,551,553,600,601,603,604,605,606,608,609,611,612,614,615,1901,1903,1907,1909,1912,1913,1918]
def ridgeSupport193_003 : List Nat := [1919,1960,1961,1966,1967,1987,1989,1993,1995,2000,2001,2006,2007,2008,2009,2014,2015,2021,2023,2027,2029,2056,2057,2062,2063,2080,2081,2086,2087,2141,2143,2147]
def ridgeSupport193_004 : List Nat := [2149,2152,2153,2158,2159,2200,2201,2206,2207,2227,2229,2233,2235,2240,2241,2246,2247,2248,2249,2254,2255,2261,2263,2267,2269,2296,2297,2302,2303,2320,2321,2326]
def ridgeSupport193_005 : List Nat := [2327,2597,2599,2609,2611,2642,2643,2654,2655,2669,2671,2681,2683,2714,2715,2726,2727,2909,2911,2915,2917,2920,2921,2926,2927,2968,2969,2974,2975,2995,2997,3001]
def ridgeSupport193_006 : List Nat := [3003,3008,3009,3014,3015,3016,3017,3022,3023,3029,3031,3035,3037,3064,3065,3070,3071,3088,3089,3094,3095,3365,3367,3377,3379,3410,3411,3422,3423,3437,3439,3449]
def ridgeSupport193_007 : List Nat := [3451,3482,3483,3494,3495,3893,3895,3905,3907,3938,3939,3950,3951,3965,3967,3977,3979,4010,4011,4022,4023,7072,7073,7108,7109,7204,7205,7675,7677,7681,7683,7708]
def ridgeSupport193_008 : List Nat := [7709,7714,7715,7718,7719,7723,7725,7729,7731,7756,7757,7762,7763,7766,7767,7828,7830,7832,7833,7846,7848,7850,7851,7891,7893,7897,7899,7924,7925,7930,7931,7934]
def ridgeSupport193_009 : List Nat := [7935,7996,7998,8000,8001,8014,8016,8018,8019,8116,8118,8120,8121,8134,8136,8138,8139]
def ridgeSupport193_code : Nat := 0x1fcb7f29fc87f19fb97ee1fb67ed1f537d49f507d39f417d01f3e7cf1eff7bf9efb7be9ef57bd1edb7b65ed57b4deab7aa9ea87a99e997a61e967a51e577959e537949e4d7931e3378c5e2d78ade277899e237889e1d7871e037805dfd77edc257091bc56f11ba16e80fb73ed8fab3ea8f8b3e24f7f3df4f6f3db8f633d88f433d04f373cd4da73698d9b3668d7b35e4d6f35b4d5f3578d533548d3334c4d273494c173058c113040bff2ff8bf92fe0bdd2f6cbd72f54bcf2f38bc92f20bc72f18bc12f00bbb2ee4bb52eccb9f2e78b992e60b6f2db8b692da0b652d8cb5f2d74aa72a98a9b2a68a7b29e4a6f29b4a5f2978a532948a3328c4a272894917245891124408ff23f88f923e08dd236c8d723548cf23388c923208c723188c123008bb22e48b522cc89f2278899226086f21b886921a0865218c85f21748272098821208080f203880920207ed1fac7e71f947df1f787d91f607d71f587d11f407cb1f247c51f0c7af1eb87a91ea077f1df87791de07751dcc76f1db42670998264098c261098025e097425c096c2590960229089c222088021f087821b08682190850212083420b0828209081820508101d5074c1ce07301cb07281c707181c507001be06e41b706d81b506c81b106c016d05b016b05a816905a013904dc13204c012f04b812b04a81290490122047411b0468119045811504500d103400cf03380cd0330089022008702180850210020007c019004c009
def ridgeSupport193_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport193_code
def ridgeSupport193_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport193_code
def ridgeSupport193_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport193_code
def ridgeSupport193_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport193_code
def ridgeSupport193_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport193_code
def ridgeSupport193_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport193_code
def ridgeSupport193_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport193_code
def ridgeSupport193_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport193_code
def ridgeSupport193_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport193_code
def ridgeSupport193_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport193_code
def ridgeSupport193_rest_010 : Nat := PackedRawNatGrowth.drop 4270 ridgeSupport193_code
def ridgeSupport193_suffix_010 : List Nat := []
def ridgeSupport193_suffix_009 : List Nat := ridgeSupport193_009 ++ ridgeSupport193_suffix_010
def ridgeSupport193_suffix_008 : List Nat := ridgeSupport193_008 ++ ridgeSupport193_suffix_009
def ridgeSupport193_suffix_007 : List Nat := ridgeSupport193_007 ++ ridgeSupport193_suffix_008
def ridgeSupport193_suffix_006 : List Nat := ridgeSupport193_006 ++ ridgeSupport193_suffix_007
def ridgeSupport193_suffix_005 : List Nat := ridgeSupport193_005 ++ ridgeSupport193_suffix_006
def ridgeSupport193_suffix_004 : List Nat := ridgeSupport193_004 ++ ridgeSupport193_suffix_005
def ridgeSupport193_suffix_003 : List Nat := ridgeSupport193_003 ++ ridgeSupport193_suffix_004
def ridgeSupport193_suffix_002 : List Nat := ridgeSupport193_002 ++ ridgeSupport193_suffix_003
def ridgeSupport193_suffix_001 : List Nat := ridgeSupport193_001 ++ ridgeSupport193_suffix_002
def ridgeSupport193_suffix_000 : List Nat := ridgeSupport193_000 ++ ridgeSupport193_suffix_001
theorem ridgeSupport193_source : candidateSupports 193 =
    (PackedRawNatGrowth.readList 14 305 ridgeSupport193_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
