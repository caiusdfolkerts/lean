module
prelude
public import RootedSixBase03GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport960_000 : List Nat := [526,527,528,947,948,949,1212,1213,1214,1477,1478,1479,1586,1587,1588,1611,1612,1613,1746,1747,1748,1749,1750,1751,1752,1753,1754,1755,1756,1757,1878,1879]
def ridgeSupport960_001 : List Nat := [1880,1881,1882,1883,1884,1885,1886,1887,1888,1889,2010,2011,2012,2013,2014,2015,2016,2017,2018,2019,2020,2021,2358,2359,2360,2361,2362,2363,2364,2365,2366,2367]
def ridgeSupport960_002 : List Nat := [2368,2369,2490,2491,2492,2493,2494,2495,2496,2497,2498,2499,2500,2501,2838,2839,2840,2841,2842,2843,2844,2845,2846,2847,2848,2849,2970,2971,2972,2973,2974,2975]
def ridgeSupport960_003 : List Nat := [2976,2977,2978,2979,2980,2981,3126,3127,3128,3129,3130,3131,3132,3133,3134,3135,3136,3137,3258,3259,3260,3261,3262,3263,3264,3265,3266,3267,3268,3269,3606,3607]
def ridgeSupport960_004 : List Nat := [3608,3609,3610,3611,3612,3613,3614,3615,3616,3617,3954,3955,3956,3957,3958,3959,3960,3961,3962,3963,3964,3965,4698,4699,4700,4701,4702,4703,4704,4705,4706,4707]
def ridgeSupport960_005 : List Nat := [4708,4709,4734,4735,4736,4737,4738,4739,4740,4741,4742,4743,4744,4745,4770,4771,4772,4773,4774,4775,4776,4777,4778,4779,4780,4781,4830,4831,4832,4833,4834,4835]
def ridgeSupport960_006 : List Nat := [4836,4837,4838,4839,4840,4841,4866,4867,4868,4869,4870,4871,4872,4873,4874,4875,4876,4877,4926,4927,4928,4929,4930,4931,4932,4933,4934,4935,4936,4937,4962,4963]
def ridgeSupport960_007 : List Nat := [4964,4965,4966,4967,4968,4969,4970,4971,4972,4973,5022,5023,5024,5025,5026,5027,5028,5029,5030,5031,5032,5033,5058,5059,5060,5061,5062,5063,5064,5065,5066,5067]
def ridgeSupport960_008 : List Nat := [5068,5069,5118,5119,5120,5121,5122,5123,5124,5125,5126,5127,5128,5129,5178,5179,5180,5181,5182,5183,5184,5185,5186,5187,5188,5189]
def ridgeSupport960_code : Nat := 0x288b444a21d10a883440a1fd0fa87b43ca1dd0ea813408a03d01a80b404a01d00a8034009ffcffa79b3cc9e5cf2a7933c89e3cf1a78b3c49e1cf0a7533a89d3ce9a74b3a49d1ce8a7433a09cfce7a6db36c9b5cdaa6d33689b3cd9a6cb3649b1cd8a6933489a3cd1a68b3449a1cd0a68334099fccfa61b30c985cc2a613308983cc1a60b304981cc0a5d32e8973cb9a5cb2e4971cb8a5c32e096fcb7a55b2ac955caaa5532a8953ca9a54b2a4951ca8a513288943ca1a50b284941ca0a50328093fc9fa4cb264931c98a4c326092fc97a4bb25c92dc969efaf7c7bdbde9ef2f787bbbdd9eeaf747b9bdc9c42e2070fb879c3ae1c70db869c32e1870bb85998acc4661b309982cc065fb2f997acbc65db2e9882c4061fb0f987ac3c61db0e9872c3861bb0d974aba45d1ae89742ba05cfae7973ab9c5cdae69642b2058fac7963ab1c58dac69632b1858bac5938a9c44e1a7093829c04dfa6f937a9bc4dda6e928294049fa4f927a93c49da4e927293849ba4d8fca7e43f19f88fc27e03ef9f78fba7dc3ed9f68ec27603af9d78eba75c3ad9d68eb27583ab9d58dba6dc36d9b68db26d836b9b58daa6d43699b48c9a64c32598d0c666322e39718b8a4be25e92f076a3b41d9884041e20e
def ridgeSupport960_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport960_code
def ridgeSupport960_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport960_code
def ridgeSupport960_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport960_code
def ridgeSupport960_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport960_code
def ridgeSupport960_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport960_code
def ridgeSupport960_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport960_code
def ridgeSupport960_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport960_code
def ridgeSupport960_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport960_code
def ridgeSupport960_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport960_code
def ridgeSupport960_rest_009 : Nat := PackedRawNatGrowth.drop 3666 ridgeSupport960_code
def ridgeSupport960_suffix_009 : List Nat := []
def ridgeSupport960_suffix_008 : List Nat := ridgeSupport960_008 ++ ridgeSupport960_suffix_009
def ridgeSupport960_suffix_007 : List Nat := ridgeSupport960_007 ++ ridgeSupport960_suffix_008
def ridgeSupport960_suffix_006 : List Nat := ridgeSupport960_006 ++ ridgeSupport960_suffix_007
def ridgeSupport960_suffix_005 : List Nat := ridgeSupport960_005 ++ ridgeSupport960_suffix_006
def ridgeSupport960_suffix_004 : List Nat := ridgeSupport960_004 ++ ridgeSupport960_suffix_005
def ridgeSupport960_suffix_003 : List Nat := ridgeSupport960_003 ++ ridgeSupport960_suffix_004
def ridgeSupport960_suffix_002 : List Nat := ridgeSupport960_002 ++ ridgeSupport960_suffix_003
def ridgeSupport960_suffix_001 : List Nat := ridgeSupport960_001 ++ ridgeSupport960_suffix_002
def ridgeSupport960_suffix_000 : List Nat := ridgeSupport960_000 ++ ridgeSupport960_suffix_001
theorem ridgeSupport960_source : candidateSupports 960 =
    (PackedRawNatGrowth.readList 13 282 ridgeSupport960_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase03
