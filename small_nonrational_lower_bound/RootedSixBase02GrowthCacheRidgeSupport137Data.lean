module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public meta import CertificateNumbers
public import RootedSixBase02GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport137_000 : List Nat := [6,21,24,25,174,177,178,181,184,211,212,215,216,221,223,224,227,228,233,331,418,420,421,423,424,426,428,429,431,432,435,436]
def ridgeSupport137_001 : List Nat := [439,441,442,444,445,447,449,450,452,453,456,457,482,483,485,486,487,488,490,491,493,494,496,497,2396,2397,2402,2403,2404,2405,2406,2407]
def ridgeSupport137_002 : List Nat := [2410,2411,2416,2417,2420,2421,2426,2427,2428,2429,2430,2431,2434,2435,2440,2441,2450,2451,2452,2453,2454,2455,2474,2475,2476,2477,2478,2479,2498,2499,2500,2501]
def ridgeSupport137_003 : List Nat := [2502,2503,2522,2523,2524,2525,2526,2527,2546,2547,2548,2549,2550,2551,2570,2571,2572,2573,2574,2575,2591,2593,2594,2595,2596,2597,2598,2599,2601,2604,2607,2610]
def ridgeSupport137_004 : List Nat := [2884,2885,2902,2903,2920,2921,2925,2928,2931,2934,2938,2939,2956,2957,2974,2975,2992,2993,2997,3000,3003,3006,3010,3011,3098,3099,3116,3117,3134,3135,3143,3145]
def ridgeSupport137_005 : List Nat := [3149,3151,3152,3153,3645,3647,3650,3653,3655,3656,3692,3694,3699,3700,3702,3705,3708,3710,3715,3716,3718,3721,5744,5745,5750,5751,5752,5753,5756,5757,5762,5763]
def ridgeSupport137_006 : List Nat := [5764,5765,5774,5775,5776,5777,5778,5779,5798,5799,5800,5801,5802,5803,5819,5821,5822,5823,5824,5825,5826,5827,5829,5832,5835,5838,5843,5845,5846,5847,5848,5849]
def ridgeSupport137_007 : List Nat := [5850,5851,5853,5856,5859,5862,5864,5865,5870,5872,5873,5875,6016,6017,6021,6024,6027,6030,6034,6035,6044,6049,6052,6053,6057,6060,6070,6071,6075,6078,6081,6084]
def ridgeSupport137_008 : List Nat := [6088,6089,6098,6103,6106,6107,6111,6114,6176,6177,6185,6187,6191,6193,6194,6195,6208,6210,6212,6213,6221,6223,6489,6490,6500,6503,6504,6507,7424,7425,7430,7431]
cert_ridgeSupport_2 137 7432 7433 7448 7453 7454 7459 7468 7470 7718 7719 7720 7721 7722 7723 7883 7894 7898
cert_ridgeSupport_code_2 137
cert_ridgeSupport_rest 137 000 0
cert_ridgeSupport_rest 137 001 416
cert_ridgeSupport_rest 137 002 832
cert_ridgeSupport_rest 137 003 1248
cert_ridgeSupport_rest 137 004 1664
cert_ridgeSupport_rest 137 005 2080
cert_ridgeSupport_rest 137 006 2496
cert_ridgeSupport_rest 137 007 2912
cert_ridgeSupport_rest 137 008 3328
cert_ridgeSupport_rest 137 009 3744
cert_ridgeSupport_rest 137 010 3965
cert_ridgeSupport_suffix_2 137 010
cert_ridgeSupport_suffix 137 009 010
cert_ridgeSupport_suffix 137 008 009
cert_ridgeSupport_suffix 137 007 008
cert_ridgeSupport_suffix 137 006 007
cert_ridgeSupport_suffix 137 005 006
cert_ridgeSupport_suffix 137 004 005
cert_ridgeSupport_suffix 137 003 004
cert_ridgeSupport_suffix 137 002 003
cert_ridgeSupport_suffix 137 001 002
cert_ridgeSupport_suffix 137 000 001
cert_ridgeSupport_source 137 13 305
end Papers.RationalityTen.RootedCaches.RootedSixBase02
