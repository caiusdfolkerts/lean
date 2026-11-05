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
def ridgeSupport133_000 : List Nat := [2,16,19,22,23,130,133,134,137,140,167,168,171,172,177,179,180,183,184,189,358,360,363,364,366,395,397,398,401,403,407,409]
def ridgeSupport133_001 : List Nat := [410,413,415,430,432,433,435,436,438,440,441,443,444,447,448,451,453,454,456,457,459,461,462,464,465,468,469,494,495,497,498,499]
def ridgeSupport133_002 : List Nat := [500,502,503,505,506,508,509,2104,2105,2110,2111,2112,2113,2114,2115,2118,2119,2124,2125,2128,2129,2134,2135,2136,2137,2138,2139,2142,2143,2148,2149,2158]
def ridgeSupport133_003 : List Nat := [2159,2160,2161,2162,2163,2182,2183,2184,2185,2186,2187,2206,2207,2208,2209,2210,2211,2230,2231,2232,2233,2234,2235,2254,2255,2256,2257,2258,2259,2278,2279,2280]
def ridgeSupport133_004 : List Nat := [2281,2282,2283,2299,2301,2302,2303,2304,2305,2306,2307,2309,2312,2315,2318,2592,2593,2610,2611,2628,2629,2633,2636,2639,2642,2646,2647,2664,2665,2682,2683,2700]
def ridgeSupport133_005 : List Nat := [2701,2705,2708,2711,2714,2718,2719,2806,2807,2824,2825,2842,2843,2851,2853,2857,2859,2860,2861,3882,3883,3894,3895,3918,3919,3930,3931,3941,3944,3947,3950,3954]
def ridgeSupport133_006 : List Nat := [3955,3966,3967,3990,3991,4002,4003,4013,4016,4019,4022,4096,4097,4108,4109,4132,4133,4144,4145,4159,4161,4165,4167,7090,7091,7092,7093,7094,7095,7726,7727,7728]
def ridgeSupport133_007 : List Nat := [7729,7730,7731,7747,7749,7750,7751,7752,7753,7759,7761,7762,7763,7764,7765,7817,7820,7830,7831,7835,7838,7848,7849,7873,7875,7882,7883,8111,8114,8117,8120,8129]
def ridgeSupport133_008 : List Nat := [8132,8135,8138,8167,8169,8173,8175]
def ridgeSupport133_code : Nat := 0x1fef7fb5fe97f9dfca7f1dfc47f05fb87ed5fb27ebdecb7b29ec37b05ea97aa1e9e7a6de977a59e8c7a25e557951e537949e51793de497921e477919e45790de3378c9e3178c1e2f78b9bb76ed9bb56ed1bb36ec9047411504140fd03140c1025409100d40310014000fb63eccfb03eb4fa33e88f973e58f7f3df8f733dc8f6e3dacf683d94f5b3d68f4f3d38f373cd8f2b3ca8b2d2cb0b2b2ca4b252c8cb1b2c68b092c20af72bd8a9f2a78a9a2a5ca942a44a8d2a30a7b29e8a6929a0a572958a52293ca4c2924a452910a3328c8a21288090e242c9082414903240890124008ff23f88fd23ec8eb23a88e923a08e723988d323488d123408cf23388bb22e88b922e08b722d88a322888a1228089f227888b22288892220887221887321c887121c086f21b8865219085f217885b216885921608572158851214084d213084721188432108841210083f20f883920e01fd07f01fa07e41f707d81f407cc1f207c41ef07b81d507501d107401ce07341cb07241c807181c5070c1c006fc1bc06ec1b906e01b606d01b306c41b006b819f067419a0664197064c191063818d062c16e05b016b05a016602f40b802dc0b402cc0b102b00ab02a00a702300890218085020801700580130040002
def ridgeSupport133_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport133_code
def ridgeSupport133_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport133_code
def ridgeSupport133_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport133_code
def ridgeSupport133_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport133_code
def ridgeSupport133_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport133_code
def ridgeSupport133_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport133_code
def ridgeSupport133_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport133_code
def ridgeSupport133_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport133_code
def ridgeSupport133_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport133_code
def ridgeSupport133_rest_009 : Nat := PackedRawNatGrowth.drop 3682 ridgeSupport133_code
def ridgeSupport133_suffix_009 : List Nat := []
def ridgeSupport133_suffix_008 : List Nat := ridgeSupport133_008 ++ ridgeSupport133_suffix_009
def ridgeSupport133_suffix_007 : List Nat := ridgeSupport133_007 ++ ridgeSupport133_suffix_008
def ridgeSupport133_suffix_006 : List Nat := ridgeSupport133_006 ++ ridgeSupport133_suffix_007
def ridgeSupport133_suffix_005 : List Nat := ridgeSupport133_005 ++ ridgeSupport133_suffix_006
def ridgeSupport133_suffix_004 : List Nat := ridgeSupport133_004 ++ ridgeSupport133_suffix_005
def ridgeSupport133_suffix_003 : List Nat := ridgeSupport133_003 ++ ridgeSupport133_suffix_004
def ridgeSupport133_suffix_002 : List Nat := ridgeSupport133_002 ++ ridgeSupport133_suffix_003
def ridgeSupport133_suffix_001 : List Nat := ridgeSupport133_001 ++ ridgeSupport133_suffix_002
def ridgeSupport133_suffix_000 : List Nat := ridgeSupport133_000 ++ ridgeSupport133_suffix_001
theorem ridgeSupport133_source : candidateSupports 133 =
    (PackedRawNatGrowth.readList 14 263 ridgeSupport133_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
