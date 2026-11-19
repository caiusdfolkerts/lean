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
def ridgeSupport74_000 : List Nat := [5,37,41,42,43,174,177,179,182,184,186,189,191,194,196,198,201,203,206,208,616,618,619,622,624,628,630,631,634,636,640,642]
def ridgeSupport74_001 : List Nat := [643,646,648,688,689,691,692,693,694,696,697,699,700,702,703,709,710,712,713,714,715,717,718,720,721,723,724,730,731,733,734,735]
def ridgeSupport74_002 : List Nat := [736,738,739,741,742,744,745,2636,2637,2638,2639,2640,2641,2642,2643,2648,2649,2654,2655,2660,2661,2662,2663,2664,2665,2666,2667,2672,2673,2678,2679,2684]
def ridgeSupport74_003 : List Nat := [2685,2686,2687,2688,2689,2708,2709,2710,2711,2712,2713,2732,2733,2734,2735,2736,2737,2756,2757,2758,2759,2760,2761,2780,2781,2782,2783,2784,2785,2804,2805,2806]
def ridgeSupport74_004 : List Nat := [2807,2808,2809,2828,2829,2830,2831,2832,2833,2837,2839,2843,2845,2849,2851,2894,2895,2906,2907,2915,2917,2921,2923,2930,2931,2942,2943,2966,2967,2978,2979,2987]
def ridgeSupport74_005 : List Nat := [2989,2993,2995,3002,3003,3014,3015,3038,3039,3050,3051,3059,3061,3065,3067,3074,3075,3086,3087,4220,4221,4232,4233,4256,4257,4268,4269,4283,4285,4289,4291,4292]
def ridgeSupport74_006 : List Nat := [4293,4304,4305,4328,4329,4340,4341,4355,4357,4361,4363,4364,4365,4376,4377,4400,4401,4412,4413,4427,4429,4433,4435,5204,5205,5206,5207,5208,5209,5219,5221,5225]
def ridgeSupport74_007 : List Nat := [5227,5231,5233,5288,5289,5294,5295,5300,5301,5516,5517,5518,5519,5520,5521,6116,6117,6118,6119,6120,6121,6140,6141,6142,6143,6144,6145,6152,6153,6154,6155,6156]
def ridgeSupport74_008 : List Nat := [6157,6164,6165,6170,6171,6182,6183,6188,6189,6200,6201,6206,6207,6437,6439,6443,6445,6455,6457,6461,6463,6473,6475,6479,6481]
cert_ridgeSupport_code_3 74
cert_ridgeSupport_rest_2 74 000 0
cert_ridgeSupport_rest_2 74 001 416
cert_ridgeSupport_rest_2 74 002 832
cert_ridgeSupport_rest_2 74 003 1248
cert_ridgeSupport_rest_2 74 004 1664
cert_ridgeSupport_rest_2 74 005 2080
cert_ridgeSupport_rest_2 74 006 2496
cert_ridgeSupport_rest_2 74 007 2912
cert_ridgeSupport_rest_2 74 008 3328
cert_ridgeSupport_rest_2 74 009 3653
cert_ridgeSupport_suffix_4 74 009
cert_ridgeSupport_suffix_3 74 008 009
cert_ridgeSupport_suffix_3 74 007 008
cert_ridgeSupport_suffix_3 74 006 007
cert_ridgeSupport_suffix_3 74 005 006
cert_ridgeSupport_suffix_3 74 004 005
cert_ridgeSupport_suffix_3 74 003 004
cert_ridgeSupport_suffix_3 74 002 003
cert_ridgeSupport_suffix_3 74 001 002
cert_ridgeSupport_suffix_3 74 000 001
cert_ridgeSupport_source_3 74 13 281
end Papers.RationalityTen.RootedCaches.RootedSixExtra02
