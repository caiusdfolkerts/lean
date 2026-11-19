module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public meta import CertificateNumbers
public import RootedSixExtra02GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport266_000 : List Nat := [7,39,42,44,46,187,188,190,195,197,211,212,214,219,221,234,237,239,242,244,627,629,632,633,635,651,653,656,657,659,676,678]
def ridgeSupport266_001 : List Nat := [679,682,684,687,688,690,691,694,695,696,698,699,701,706,707,729,731,732,734,735,737,739,740,742,743,746,747,750,752,753,755,756]
def ridgeSupport266_002 : List Nat := [758,760,761,763,764,767,768,2638,2639,2644,2645,2648,2649,2650,2651,2652,2653,2658,2659,2662,2663,2668,2669,2672,2673,2674,2675,2676,2677,2682,2683,2696]
def ridgeSupport266_003 : List Nat := [2697,2698,2699,2700,2701,2720,2721,2722,2723,2724,2725,2744,2745,2746,2747,2748,2749,2768,2769,2770,2771,2772,2773,2792,2793,2794,2795,2796,2797,2816,2817,2818]
def ridgeSupport266_004 : List Nat := [2819,2820,2821,2829,2832,2835,2838,2840,2841,2842,2843,2844,2845,2846,2848,2898,2899,2910,2911,2912,2914,2918,2920,2934,2935,2946,2947,3040,3041,3052,3053,3057]
def ridgeSupport266_005 : List Nat := [3060,3063,3066,3076,3077,3088,3089,3112,3113,3124,3125,3129,3132,3135,3138,3148,3149,3160,3161,4224,4225,4236,4237,4260,4261,4272,4273,4280,4282,4286,4288,4366]
def ridgeSupport266_006 : List Nat := [4367,4378,4379,4402,4403,4414,4415,4425,4428,4431,4434,4438,4439,4450,4451,4474,4475,4486,4487,4497,4500,4503,4506,5206,5207,5210,5211,5214,5215,5216,5218,5229]
def ridgeSupport266_007 : List Nat := [5232,5235,5238,5292,5293,5302,5303,5308,5309,5528,5529,5530,5531,5532,5533,6128,6129,6130,6131,6132,6133,6141,6144,6147,6149,6150,6151,6153,6156,6159,6161,6162]
def ridgeSupport266_008 : List Nat := [6163,6168,6169,6174,6175,6202,6203,6208,6209,6220,6221,6226,6227,6434,6436,6440,6442,6471,6474,6477,6480,6489,6492,6495,6498]
cert_ridgeSupport_code_3 266
cert_ridgeSupport_rest_2 266 000 0
cert_ridgeSupport_rest_2 266 001 416
cert_ridgeSupport_rest_2 266 002 832
cert_ridgeSupport_rest_2 266 003 1248
cert_ridgeSupport_rest_2 266 004 1664
cert_ridgeSupport_rest_2 266 005 2080
cert_ridgeSupport_rest_2 266 006 2496
cert_ridgeSupport_rest_2 266 007 2912
cert_ridgeSupport_rest_2 266 008 3328
cert_ridgeSupport_rest_2 266 009 3653
cert_ridgeSupport_suffix_4 266 009
cert_ridgeSupport_suffix_3 266 008 009
cert_ridgeSupport_suffix_3 266 007 008
cert_ridgeSupport_suffix_3 266 006 007
cert_ridgeSupport_suffix_3 266 005 006
cert_ridgeSupport_suffix_3 266 004 005
cert_ridgeSupport_suffix_3 266 003 004
cert_ridgeSupport_suffix_3 266 002 003
cert_ridgeSupport_suffix_3 266 001 002
cert_ridgeSupport_suffix_3 266 000 001
cert_ridgeSupport_source_3 266 13 281
end Papers.RationalityTen.RootedCaches.RootedSixExtra02
