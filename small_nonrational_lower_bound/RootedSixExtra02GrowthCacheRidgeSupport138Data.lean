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
def ridgeSupport138_000 : List Nat := [6,38,41,44,45,175,176,178,183,185,210,213,215,218,220,222,225,227,230,232,615,617,620,621,623,652,654,655,658,660,664,666]
def ridgeSupport138_001 : List Nat := [667,670,672,687,689,690,692,693,695,697,698,700,701,704,705,708,710,711,713,714,716,718,719,721,722,725,726,751,752,754,755,756]
def ridgeSupport138_002 : List Nat := [757,759,760,762,763,765,766,2636,2637,2642,2643,2644,2645,2646,2647,2650,2651,2656,2657,2660,2661,2666,2667,2668,2669,2670,2671,2674,2675,2680,2681,2690]
def ridgeSupport138_003 : List Nat := [2691,2692,2693,2694,2695,2714,2715,2716,2717,2718,2719,2738,2739,2740,2741,2742,2743,2762,2763,2764,2765,2766,2767,2786,2787,2788,2789,2790,2791,2810,2811,2812]
def ridgeSupport138_004 : List Nat := [2813,2814,2815,2831,2833,2834,2835,2836,2837,2838,2839,2841,2844,2847,2850,2896,2897,2908,2909,2913,2916,2919,2922,2932,2933,2944,2945,2968,2969,2980,2981,2985]
def ridgeSupport138_005 : List Nat := [2988,2991,2994,3004,3005,3016,3017,3110,3111,3122,3123,3131,3133,3137,3139,3146,3147,3158,3159,4222,4223,4234,4235,4258,4259,4270,4271,4281,4284,4287,4290,4294]
def ridgeSupport138_006 : List Nat := [4295,4306,4307,4330,4331,4342,4343,4353,4356,4359,4362,4436,4437,4448,4449,4472,4473,4484,4485,4499,4501,4505,4507,5204,5205,5210,5211,5212,5213,5217,5220,5223]
def ridgeSupport138_007 : List Nat := [5226,5237,5239,5290,5291,5296,5297,5306,5307,5522,5523,5524,5525,5526,5527,6122,6123,6124,6125,6126,6127,6143,6145,6146,6147,6148,6149,6155,6157,6158,6159,6160]
def ridgeSupport138_008 : List Nat := [6161,6166,6167,6172,6173,6184,6185,6190,6191,6218,6219,6224,6225,6435,6438,6441,6444,6453,6456,6459,6462,6491,6493,6497,6499]
cert_ridgeSupport_code_3 138
cert_ridgeSupport_rest_2 138 000 0
cert_ridgeSupport_rest_2 138 001 416
cert_ridgeSupport_rest_2 138 002 832
cert_ridgeSupport_rest_2 138 003 1248
cert_ridgeSupport_rest_2 138 004 1664
cert_ridgeSupport_rest_2 138 005 2080
cert_ridgeSupport_rest_2 138 006 2496
cert_ridgeSupport_rest_2 138 007 2912
cert_ridgeSupport_rest_2 138 008 3328
cert_ridgeSupport_rest_2 138 009 3653
cert_ridgeSupport_suffix_4 138 009
cert_ridgeSupport_suffix_3 138 008 009
cert_ridgeSupport_suffix_3 138 007 008
cert_ridgeSupport_suffix_3 138 006 007
cert_ridgeSupport_suffix_3 138 005 006
cert_ridgeSupport_suffix_3 138 004 005
cert_ridgeSupport_suffix_3 138 003 004
cert_ridgeSupport_suffix_3 138 002 003
cert_ridgeSupport_suffix_3 138 001 002
cert_ridgeSupport_suffix_3 138 000 001
cert_ridgeSupport_source_3 138 13 281
end Papers.RationalityTen.RootedCaches.RootedSixExtra02
