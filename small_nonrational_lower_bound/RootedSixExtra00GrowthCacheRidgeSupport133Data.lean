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
def ridgeSupport133_000 : List Nat := [2,16,19,22,23,130,133,134,137,140,167,168,171,172,177,179,180,183,184,189,358,360,363,364,366,395,397,398,401,403,407,409]
def ridgeSupport133_001 : List Nat := [410,413,415,430,432,433,435,436,438,440,441,443,444,447,448,451,453,454,456,457,459,461,462,464,465,468,469,494,495,497,498,499]
def ridgeSupport133_002 : List Nat := [500,502,503,505,506,508,509,2104,2105,2110,2111,2112,2113,2114,2115,2118,2119,2124,2125,2128,2129,2134,2135,2136,2137,2138,2139,2142,2143,2148,2149,2158]
def ridgeSupport133_003 : List Nat := [2159,2160,2161,2162,2163,2182,2183,2184,2185,2186,2187,2206,2207,2208,2209,2210,2211,2230,2231,2232,2233,2234,2235,2254,2255,2256,2257,2258,2259,2278,2279,2280]
def ridgeSupport133_004 : List Nat := [2281,2282,2283,2299,2301,2302,2303,2304,2305,2306,2307,2309,2312,2315,2318,2592,2593,2610,2611,2628,2629,2633,2636,2639,2642,2646,2647,2664,2665,2682,2683,2700]
def ridgeSupport133_005 : List Nat := [2701,2705,2708,2711,2714,2718,2719,2806,2807,2824,2825,2842,2843,2851,2853,2857,2859,2860,2861,3882,3883,3894,3895,3918,3919,3930,3931,3941,3944,3947,3950,3954]
def ridgeSupport133_006 : List Nat := [3955,3966,3967,3990,3991,4002,4003,4013,4016,4019,4022,4096,4097,4108,4109,4132,4133,4144,4145,4159,4161,4165,4167,7090,7091,7092,7093,7094,7095,7726,7727,7728]
def ridgeSupport133_007 : List Nat := [7729,7730,7731,7747,7749,7750,7751,7752,7753,7759,7761,7762,7763,7764,7765,7817,7820,7830,7831,7835,7838,7848,7849,7873,7875,7882,7883,8111,8114,8117,8120,8129]
cert_ridgeSupport_7 133 008 8132 8135 8138 8167 8169 8173 8175
cert_ridgeSupport_code_3 133
cert_ridgeSupport_rest_2 133 000 0
cert_ridgeSupport_rest_2 133 001 448
cert_ridgeSupport_rest_2 133 002 896
cert_ridgeSupport_rest_2 133 003 1344
cert_ridgeSupport_rest_2 133 004 1792
cert_ridgeSupport_rest_2 133 005 2240
cert_ridgeSupport_rest_2 133 006 2688
cert_ridgeSupport_rest_2 133 007 3136
cert_ridgeSupport_rest_2 133 008 3584
cert_ridgeSupport_rest_2 133 009 3682
cert_ridgeSupport_suffix_4 133 009
cert_ridgeSupport_suffix_3 133 008 009
cert_ridgeSupport_suffix_3 133 007 008
cert_ridgeSupport_suffix_3 133 006 007
cert_ridgeSupport_suffix_3 133 005 006
cert_ridgeSupport_suffix_3 133 004 005
cert_ridgeSupport_suffix_3 133 003 004
cert_ridgeSupport_suffix_3 133 002 003
cert_ridgeSupport_suffix_3 133 001 002
cert_ridgeSupport_suffix_3 133 000 001
cert_ridgeSupport_source_3 133 14 263
end Papers.RationalityTen.RootedCaches.RootedSixExtra00
