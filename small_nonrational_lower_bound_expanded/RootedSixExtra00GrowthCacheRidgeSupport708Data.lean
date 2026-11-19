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
def ridgeSupport708_000 : List Nat := [460,461,462,725,726,727,1149,1150,1151,1305,1306,1307,1389,1390,1391,1459,1460,1461,2106,2107,2112,2113,2126,2127,2129,2132,2135,2138,2146,2148,2154,2155]
def ridgeSupport708_001 : List Nat := [2160,2161,2174,2175,2249,2252,2255,2258,2266,2268,2297,2300,2303,2306,2314,2316,2346,2347,2352,2353,2366,2367,2369,2372,2375,2378,2386,2388,2394,2395,2400,2401]
def ridgeSupport708_002 : List Nat := [2414,2415,2489,2492,2495,2498,2506,2508,2537,2540,2543,2546,2554,2556,2698,2699,2700,2701,2702,2703,2710,2711,2712,2713,2714,2715,3641,3644,3647,3650,3658,3660]
def ridgeSupport708_003 : List Nat := [3666,3667,3672,3673,3686,3687,3714,3715,3720,3721,3734,3735,3809,3812,3815,3818,3826,3828,3844,3845,3846,3847,3848,3849,3988,3989,3990,3991,3992,3993,4018,4019]
def ridgeSupport708_004 : List Nat := [4020,4021,4022,4023,4409,4412,4415,4418,4426,4428,4434,4435,4440,4441,4454,4455,4482,4483,4488,4489,4502,4503,4577,4580,4583,4586,4594,4596,4612,4613,4614,4615]
def ridgeSupport708_005 : List Nat := [4616,4617,4756,4757,4758,4759,4760,4761,4786,4787,4788,4789,4790,4791,5465,5468,5471,5474,5482,5484,5490,5491,5496,5497,5510,5511,5538,5539,5544,5545,5558,5559]
def ridgeSupport708_006 : List Nat := [5633,5636,5639,5642,5650,5652,5668,5669,5670,5671,5672,5673,6064,6065,6066,6067,6068,6069,6076,6077,6078,6079,6080,6081,6592,6593,6594,6595,6596,6597,6604,6605]
def ridgeSupport708_007 : List Nat := [6606,6607,6608,6609,7086,7087,7092,7093,7106,7107,7122,7123,7128,7129,7142,7143,7276,7281,7282,7287,7295,7297,7372,7377,7378,7383,7391,7393,7492,7497,7498,7503]
def ridgeSupport708_008 : List Nat := [7511,7513]
cert_ridgeSupport_code_3 708
cert_ridgeSupport_rest_2 708 000 0
cert_ridgeSupport_rest_2 708 001 448
cert_ridgeSupport_rest_2 708 002 896
cert_ridgeSupport_rest_2 708 003 1344
cert_ridgeSupport_rest_2 708 004 1792
cert_ridgeSupport_rest_2 708 005 2240
cert_ridgeSupport_rest_2 708 006 2688
cert_ridgeSupport_rest_2 708 007 3136
cert_ridgeSupport_rest_2 708 008 3584
cert_ridgeSupport_rest_2 708 009 3612
cert_ridgeSupport_suffix_4 708 009
cert_ridgeSupport_suffix_3 708 008 009
cert_ridgeSupport_suffix_3 708 007 008
cert_ridgeSupport_suffix_3 708 006 007
cert_ridgeSupport_suffix_3 708 005 006
cert_ridgeSupport_suffix_3 708 004 005
cert_ridgeSupport_suffix_3 708 003 004
cert_ridgeSupport_suffix_3 708 002 003
cert_ridgeSupport_suffix_3 708 001 002
cert_ridgeSupport_suffix_3 708 000 001
cert_ridgeSupport_source_3 708 14 258
end Papers.RationalityTen.RootedCaches.RootedSixExtra00
