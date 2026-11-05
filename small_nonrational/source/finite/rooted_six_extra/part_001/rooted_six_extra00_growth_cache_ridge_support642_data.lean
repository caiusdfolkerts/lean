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
def ridgeSupport642_000 : List Nat := [13,43,53,59,62,64,178,179,182,183,186,187,250,251,254,255,258,259,296,297,298,301,302,307,308,313,315,337,339,341,343,345]
def ridgeSupport642_001 : List Nat := [350,351,353,356,673,674,675,676,677,678,716,720,721,722,723,725,726,733,735,759,761,763,764,766,768,769,773,778,829,830,831,832]
def ridgeSupport642_002 : List Nat := [833,834,872,876,877,878,879,881,882,889,891,915,917,919,920,922,924,925,929,934,956,960,961,962,963,965,966,973,975,999,1001,1003]
def ridgeSupport642_003 : List Nat := [1004,1006,1008,1009,1013,1018,1019,1021,1023,1025,1026,1028,1030,1031,1035,1037,1042,1043,1864,1869,1878,1880,1946,1947,1956,1957,1962,1963,1966,1968,1972,1973]
def ridgeSupport642_004 : List Nat := [1979,1982,1994,1995,2004,2005,2032,2037,2042,2043,2046,2048,2052,2053,2058,2059,2068,2069,2082,2083,2092,2093,2368,2373,2382,2384,2402,2403,2412,2413,2450,2451]
def ridgeSupport642_005 : List Nat := [2460,2461,2466,2467,2470,2472,2476,2477,2483,2486,2488,2493,2498,2499,2502,2504,2508,2509,2546,2547,2556,2557,2570,2571,2580,2581,2658,2660,2688,2690,2698,2699]
def ridgeSupport642_006 : List Nat := [2716,2717,2800,2805,2830,2835,2844,2845,2862,2863,3136,3141,3150,3152,3170,3171,3180,3181,3218,3219,3228,3229,3234,3235,3238,3240,3244,3245,3251,3254,3256,3261]
def ridgeSupport642_007 : List Nat := [3266,3267,3270,3272,3276,3277,3314,3315,3324,3325,3338,3339,3348,3349,3426,3428,3456,3458,3466,3467,3484,3485,3568,3573,3598,3603,3612,3613,3630,3631,4192,4197]
def ridgeSupport642_008 : List Nat := [4206,4208,4226,4227,4236,4237,4274,4275,4284,4285,4290,4291,4294,4296,4300,4301,4307,4310,4312,4317,4322,4323,4326,4328,4332,4333,4370,4371,4380,4381,4394,4395]
def ridgeSupport642_009 : List Nat := [4404,4405,4734,4736,4746,4748,4774,4775,4786,4787,4876,4881,4888,4893,4920,4921,4932,4933,5262,5264,5274,5276,5302,5303,5314,5315,5404,5409,5416,5421,5448,5449]
def ridgeSupport642_010 : List Nat := [5460,5461,7074,7075,7152,7153,7248,7249,7368,7369,7682,7683,7692,7693,7697,7698,7699,7700,7705,7706,7774,7776,7787,7790,7805,7806,7807,7808,7813,7814,7840,7841]
def ridgeSupport642_011 : List Nat := [7843,7845,7877,7878,7879,7880,7942,7944,7955,7958,7973,7974,7975,7976,7981,7982,8008,8009,8011,8013,8045,8046,8047,8048,8182,8184,8195,8198,8213,8214,8215,8216]
def ridgeSupport642_012 : List Nat := [8221,8222,8302,8303,8305,8307,8339,8340,8341,8342,8422,8423,8425,8427,8459,8460,8461,8462]
def ridgeSupport642_code : Nat := 0x843a10d843210b83ae0e9839e0e6825a095825209381ce07181be06e807a01d8062017805a015801a0037fe1ff67dc1f6f7db9f6d7d35f4b7d25f487cb9f2d7ca1f277c99f257c59f137c21f067b21ec77b19ec57a95ea37a85ea07a19e857a01e7f79f9e7d79b9e6b7981e5e7869e197851e137849e117835e0c780de027325cc87145c506fc5bf06e8dba25555554552554854b5528548551c530d4c252dd4b6527149a524148e4d153444ce53384c753184c4530c4acd2b24a9d2a64a3128a4a0127e44d513444ad12a447511c444d11243b50ec43a10e6438d0e243750d843590d343350cc43210c6430d0c242f50bc42cd0b2423508c420d08241c106e419506038bce2e3874e1c384ce0e37d4df03674d9c362cd8a3608d803590d623454d14342cd0a33f4cfc33cccf23334ccc3320cc6330ccc232f4cb832d8cb332b4cac32a0ca6328cca23274c9c324cc9231b4c6c318cc623140c4e3114c402cbcb2e2c74b1c2c4cb0e2bd4af02a74a9c2a2ca8a2a08a802990a622854a14282ca0a27f49fc27cc9f227349cc27209c6270c9c226f49b826d89b326b49ac26a09a6268c9a2267499c264c99225b496c258c962254094e251494020b482c208c8222054814202c80a201480420007fe1fec7fa1fd47f01f547d41f2c7ca1ef87bb1ed47b41ec07ae1eac7aa1e947a41e6c79a1d607561d34748104c412103440b101c406101040210043ff0ff43fb0fe83f50fc43f00fb83ec0fac3e90f9c3cf0f343c60f143c30f083c10f003bc0e983a10e7439c0e683980e5c3950e4c37b0de43720dc436f0db836d0db03680d083410d0033f0cf833d0c283050c043000bf82fc0bec2f90bdc2df0b742d60b542d30b482d10b402cc0a982a50a902a30a882a10590161057c15e05641570554153054413b04e413404cc12e04b412a04a4128040c10203fc0fe03ec0fa02ec0ba02dc0b602cc0b2010003e00ec03500ac00d
def ridgeSupport642_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport642_code
def ridgeSupport642_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport642_code
def ridgeSupport642_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport642_code
def ridgeSupport642_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport642_code
def ridgeSupport642_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport642_code
def ridgeSupport642_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport642_code
def ridgeSupport642_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport642_code
def ridgeSupport642_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport642_code
def ridgeSupport642_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport642_code
def ridgeSupport642_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport642_code
def ridgeSupport642_rest_010 : Nat := PackedRawNatGrowth.drop 4480 ridgeSupport642_code
def ridgeSupport642_rest_011 : Nat := PackedRawNatGrowth.drop 4928 ridgeSupport642_code
def ridgeSupport642_rest_012 : Nat := PackedRawNatGrowth.drop 5376 ridgeSupport642_code
def ridgeSupport642_rest_013 : Nat := PackedRawNatGrowth.drop 5628 ridgeSupport642_code
def ridgeSupport642_suffix_013 : List Nat := []
def ridgeSupport642_suffix_012 : List Nat := ridgeSupport642_012 ++ ridgeSupport642_suffix_013
def ridgeSupport642_suffix_011 : List Nat := ridgeSupport642_011 ++ ridgeSupport642_suffix_012
def ridgeSupport642_suffix_010 : List Nat := ridgeSupport642_010 ++ ridgeSupport642_suffix_011
def ridgeSupport642_suffix_009 : List Nat := ridgeSupport642_009 ++ ridgeSupport642_suffix_010
def ridgeSupport642_suffix_008 : List Nat := ridgeSupport642_008 ++ ridgeSupport642_suffix_009
def ridgeSupport642_suffix_007 : List Nat := ridgeSupport642_007 ++ ridgeSupport642_suffix_008
def ridgeSupport642_suffix_006 : List Nat := ridgeSupport642_006 ++ ridgeSupport642_suffix_007
def ridgeSupport642_suffix_005 : List Nat := ridgeSupport642_005 ++ ridgeSupport642_suffix_006
def ridgeSupport642_suffix_004 : List Nat := ridgeSupport642_004 ++ ridgeSupport642_suffix_005
def ridgeSupport642_suffix_003 : List Nat := ridgeSupport642_003 ++ ridgeSupport642_suffix_004
def ridgeSupport642_suffix_002 : List Nat := ridgeSupport642_002 ++ ridgeSupport642_suffix_003
def ridgeSupport642_suffix_001 : List Nat := ridgeSupport642_001 ++ ridgeSupport642_suffix_002
def ridgeSupport642_suffix_000 : List Nat := ridgeSupport642_000 ++ ridgeSupport642_suffix_001
theorem ridgeSupport642_source : candidateSupports 642 =
    (PackedRawNatGrowth.readList 14 402 ridgeSupport642_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
