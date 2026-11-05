module
prelude
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
def ridgeSupport137_009 : List Nat := [7432,7433,7448,7453,7454,7459,7468,7470,7718,7719,7720,7721,7722,7723,7883,7894,7898]
def ridgeSupport137_code : Nat := 0x1edaf6b7b2fc57e2af14f8a3c4fe26e9774b3a47d1ee8ef463a13d08e83f41ba03d00cb5e5a32cf964cad656709f84dc22e113085840c19e0cb06382fc15e0a7043820bf15f7efb77dabebdf4af937c8be25f06f7d7bbbdbdedaf597a9bd2de92f4379cbc9de4af1d78bbc45e16f03780b79dbc6de16eeb74dba2dcd6e3b705b76db76dab6cdb62daf6d6b6adb4ed9d6cbb645b16d876c2b60db02d7f6beb5edaeed576aab54daa2d4f6a6b49da4ad23690b47da3ad0b684b41da0acfb67cb3cd9e2cef676b38d9c1d12e867423a0dcfce7c73cb9d9ce8e7373739b1c90e47722b909c7ee3d628b14189ec4d624b11d87ec3e616b0b1836c1a5e1af0977cbbb5dc2ed5762bb05cfae7971ab8c5bdade96ecb735b82db56d2b685abad5968ab4451928bd458a29513a89944aa24511a889442a1f507a83941aa0c505a8293ee9f64faa7d13e69f24efa7793ba9dc4eda76938e9c64e2a7113869c24d7a6b935a9ac4d5a6a932e9964caa6513269924c4a6213069824bfa5f92fa97c4bda5e92ea9744b8a5c12d696a4b3a5992ca9644b1a5892ba95c0f887c03dc1ed0f587a83d01e70f307943c61e20e4872038a1c40e1070437e1bd0de06e83721b70da06cc3601af0d686b03541a80d386943481a20a583a41c80e3070037c1ba0d806b83501a60b805a82c81620ae00c806002a006
def ridgeSupport137_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport137_code
def ridgeSupport137_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport137_code
def ridgeSupport137_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport137_code
def ridgeSupport137_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport137_code
def ridgeSupport137_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport137_code
def ridgeSupport137_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport137_code
def ridgeSupport137_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport137_code
def ridgeSupport137_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport137_code
def ridgeSupport137_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport137_code
def ridgeSupport137_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport137_code
def ridgeSupport137_rest_010 : Nat := PackedRawNatGrowth.drop 3965 ridgeSupport137_code
def ridgeSupport137_suffix_010 : List Nat := []
def ridgeSupport137_suffix_009 : List Nat := ridgeSupport137_009 ++ ridgeSupport137_suffix_010
def ridgeSupport137_suffix_008 : List Nat := ridgeSupport137_008 ++ ridgeSupport137_suffix_009
def ridgeSupport137_suffix_007 : List Nat := ridgeSupport137_007 ++ ridgeSupport137_suffix_008
def ridgeSupport137_suffix_006 : List Nat := ridgeSupport137_006 ++ ridgeSupport137_suffix_007
def ridgeSupport137_suffix_005 : List Nat := ridgeSupport137_005 ++ ridgeSupport137_suffix_006
def ridgeSupport137_suffix_004 : List Nat := ridgeSupport137_004 ++ ridgeSupport137_suffix_005
def ridgeSupport137_suffix_003 : List Nat := ridgeSupport137_003 ++ ridgeSupport137_suffix_004
def ridgeSupport137_suffix_002 : List Nat := ridgeSupport137_002 ++ ridgeSupport137_suffix_003
def ridgeSupport137_suffix_001 : List Nat := ridgeSupport137_001 ++ ridgeSupport137_suffix_002
def ridgeSupport137_suffix_000 : List Nat := ridgeSupport137_000 ++ ridgeSupport137_suffix_001
theorem ridgeSupport137_source : candidateSupports 137 =
    (PackedRawNatGrowth.readList 13 305 ridgeSupport137_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
