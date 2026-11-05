module
prelude
public import RootedSixBase01GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport836_000 : List Nat := [467,468,469,732,733,734,1088,1089,1090,1244,1245,1246,1328,1329,1330,1374,1375,1376,1896,1897,1898,1899,1900,1901,1992,1993,1994,1995,1996,1997,2088,2089]
def ridgeSupport836_001 : List Nat := [2090,2091,2092,2093,2160,2161,2162,2163,2164,2165,2256,2257,2258,2259,2260,2261,2352,2353,2354,2355,2356,2357,2640,2641,2642,2643,2644,2645,2652,2653,2654,2655]
def ridgeSupport836_002 : List Nat := [2656,2657,3840,3841,3842,3843,3844,3845,3888,3889,3890,3891,3892,3893,4032,4033,4034,4035,4036,4037,4290,4291,4292,4293,4294,4295,4320,4321,4322,4323,4324,4325]
def ridgeSupport836_003 : List Nat := [4800,4801,4802,4803,4804,4805,4848,4849,4850,4851,4852,4853,4992,4993,4994,4995,4996,4997,5250,5251,5252,5253,5254,5255,5280,5281,5282,5283,5284,5285,5496,5497]
def ridgeSupport836_004 : List Nat := [5498,5499,5500,5501,5544,5545,5546,5547,5548,5549,5688,5689,5690,5691,5692,5693,6222,6223,6224,6225,6226,6227,6234,6235,6236,6237,6238,6239,6918,6919,6920,6921]
def ridgeSupport836_005 : List Nat := [6922,6923,6930,6931,6932,6933,6934,6935,7410,7411,7424,7425,7430,7431,7437,7439,7447,7450,7453,7456,7458,7459,7472,7473,7478,7479,7557,7559,7567,7570,7573,7576]
def ridgeSupport836_006 : List Nat := [7605,7607,7615,7618,7621,7624,7650,7651,7664,7665,7670,7671,7677,7679,7687,7690,7693,7696,7698,7699,7712,7713,7718,7719,7797,7799,7807,7810,7813,7816,7845,7847]
def ridgeSupport836_007 : List Nat := [7855,7858,7861,7864,8076,8077,8078,8079,8080,8081,8088,8089,8090,8091,8092,8093,8949,8951,8959,8962,8965,8968,8970,8971,8984,8985,8990,8991,9018,9019,9032,9033]
def ridgeSupport836_008 : List Nat := [9038,9039,9117,9119,9127,9130,9133,9136,9144,9145,9146,9147,9148,9149,9366,9367,9368,9369,9370,9371,9396,9397,9398,9399,9400,9401,9717,9719,9727,9730,9733,9736]
def ridgeSupport836_009 : List Nat := [9738,9739,9752,9753,9758,9759,9786,9787,9800,9801,9806,9807,9885,9887,9895,9898,9901,9904,9912,9913,9914,9915,9916,9917,10134,10135,10136,10137,10138,10139,10164,10165]
def ridgeSupport836_010 : List Nat := [10166,10167,10168,10169,10245,10247,10255,10258,10261,10264,10266,10267,10280,10281,10286,10287,10314,10315,10328,10329,10334,10335,10413,10415,10423,10426,10429,10432,10440,10441,10442,10443]
def ridgeSupport836_011 : List Nat := [10444,10445,10914,10915,10916,10917,10918,10919,10926,10927,10928,10929,10930,10931,11442,11443,11444,11445,11446,11447,11454,11455,11456,11457,11458,11459,11781,11783,11788,11841,11843,11851]
def ridgeSupport836_012 : List Nat := [11854,11857,11860,11913,11915,11920,11973,11975,11983,11986,11989,11992,12180,12181,12182,12183,12184,12185,12729,12731,12736,12825,12827,12835,12838,12841,12844,13002,13003,13004,13005,13006]
def ridgeSupport836_013 : List Nat := [13007,13209,13211,13216,13305,13307,13315,13318,13321,13324,13482,13483,13484,13485,13486,13487,13557,13559,13564,13653,13655,13663,13666,13669,13672,13974,13975,13976,13977,13978,13979,14322]
def ridgeSupport836_014 : List Nat := [14323,14324,14325,14326,14327,14718,14719,14732,14733,14738,14739,14754,14755,14768,14769,14774,14775,14912,14914,14922,14927,14928,14933,15008,15010,15018,15023,15024,15029,15068,15070,15078]
def ridgeSupport836_015 : List Nat := [15083,15084,15089]
def ridgeSupport836_code : Nat := 0x3af1ebb3aebeb9badeeb73ab5eac3aafeaabaa2ea83a55e943a4fe92ba42e9039b7e6db9b1e6c39a3e68b993e64b98de63397fe5fb7f7dfdb7f5dfd37f3dfcb69bda6b699da63697da5b568d597562d57f557d5574fcd3df4f5d2bf4aed2b74acd2af4aad033409d01b403cfef3f9ce8339bce672cfcb3b2cdcb332cbcb2b22cc8a7226c88f21bc8671c0c6ef1b9be66f98be5ef96be56f94bb62ed5bb4aecfbb1eec5ba42e8bba26e54b946e4eb92ee43b906e0cb81ee05b30ecc2b306cc0b2fecbeb2decb6b2d6cb4b2cecb2aaceab2aac6ab0aabeaaeaa9eaa6aa96aa4aa8eaa2a3368cca32e8caa3268c8a3028bda2ea8b7a2be8ada17e85ea166858a12e84aa0be82ea0a6828a06e81aa062815a04a80fa01e8059ee67b89ede7b69ed67b49e6e79a9e667989e5e7969af66bc9aee6ba9ae66b89ac26ad9aaa6a79a7e69d993e64e992664898ee63a987e61e9866618982e60a9822605980a5ff97de5f592e64b892de4b692d64b4926e49a9266498925e4968ef63bc8eee3ba8ee63b88ec23ad8eaa3a78e7e39d8d3e34e8d263488cee33a8c7e31e8c663188c2e30a8c223058c0a2ff8bde2f57e75f9c7e6df9a7e65f987e45f907e3df8e7e35f8c7ae1eb57ac9eaf7a9dea57a21e857a09e7f79dde75789de267885e20784de127841e0d7829e0777fddfd77dddf677c5df0778dde27721dc57709dbf76dddb57661d957649d8f761dd8574ddd3674c5d30748dd227481d1d7469d17743dd0d741dd067405d0073cdcf26c5db166c55b146c4db126c2db0a6c25b086c1db06617d85e617585c616d85a614d8526145850613d84e58f563c58ed63a58e563856b55ac56ad5aa56a55a855f557c55ed57a55e557852954a4528d4a252854a0521d4865215484520d4824e153844e0d3824e053804bd52f44bcd2f24bc52f04b152c44b0d2c24b052c043950e4438d0e243850e0431d0c643150c4430d0c23f14fc43f0cfc23f04fc03cd4f343cccf323cc4f303c14f043c0cf023c04f002984a60297ca5e2974a5c2954a54294ca522944a5024d493424cc93224c493023548d4234c8d223448d021d487421cc87221c487020b482c20ac82a20a48281f347cc1f2c7ca1f247c81db476c1dac76a1da4768158055f157853214c453013784dd137044211044400b782dd0b701d507501d3
def ridgeSupport836_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport836_code
def ridgeSupport836_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport836_code
def ridgeSupport836_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport836_code
def ridgeSupport836_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport836_code
def ridgeSupport836_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport836_code
def ridgeSupport836_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport836_code
def ridgeSupport836_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport836_code
def ridgeSupport836_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport836_code
def ridgeSupport836_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport836_code
def ridgeSupport836_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport836_code
def ridgeSupport836_rest_010 : Nat := PackedRawNatGrowth.drop 4480 ridgeSupport836_code
def ridgeSupport836_rest_011 : Nat := PackedRawNatGrowth.drop 4928 ridgeSupport836_code
def ridgeSupport836_rest_012 : Nat := PackedRawNatGrowth.drop 5376 ridgeSupport836_code
def ridgeSupport836_rest_013 : Nat := PackedRawNatGrowth.drop 5824 ridgeSupport836_code
def ridgeSupport836_rest_014 : Nat := PackedRawNatGrowth.drop 6272 ridgeSupport836_code
def ridgeSupport836_rest_015 : Nat := PackedRawNatGrowth.drop 6720 ridgeSupport836_code
def ridgeSupport836_rest_016 : Nat := PackedRawNatGrowth.drop 6762 ridgeSupport836_code
def ridgeSupport836_suffix_016 : List Nat := []
def ridgeSupport836_suffix_015 : List Nat := ridgeSupport836_015 ++ ridgeSupport836_suffix_016
def ridgeSupport836_suffix_014 : List Nat := ridgeSupport836_014 ++ ridgeSupport836_suffix_015
def ridgeSupport836_suffix_013 : List Nat := ridgeSupport836_013 ++ ridgeSupport836_suffix_014
def ridgeSupport836_suffix_012 : List Nat := ridgeSupport836_012 ++ ridgeSupport836_suffix_013
def ridgeSupport836_suffix_011 : List Nat := ridgeSupport836_011 ++ ridgeSupport836_suffix_012
def ridgeSupport836_suffix_010 : List Nat := ridgeSupport836_010 ++ ridgeSupport836_suffix_011
def ridgeSupport836_suffix_009 : List Nat := ridgeSupport836_009 ++ ridgeSupport836_suffix_010
def ridgeSupport836_suffix_008 : List Nat := ridgeSupport836_008 ++ ridgeSupport836_suffix_009
def ridgeSupport836_suffix_007 : List Nat := ridgeSupport836_007 ++ ridgeSupport836_suffix_008
def ridgeSupport836_suffix_006 : List Nat := ridgeSupport836_006 ++ ridgeSupport836_suffix_007
def ridgeSupport836_suffix_005 : List Nat := ridgeSupport836_005 ++ ridgeSupport836_suffix_006
def ridgeSupport836_suffix_004 : List Nat := ridgeSupport836_004 ++ ridgeSupport836_suffix_005
def ridgeSupport836_suffix_003 : List Nat := ridgeSupport836_003 ++ ridgeSupport836_suffix_004
def ridgeSupport836_suffix_002 : List Nat := ridgeSupport836_002 ++ ridgeSupport836_suffix_003
def ridgeSupport836_suffix_001 : List Nat := ridgeSupport836_001 ++ ridgeSupport836_suffix_002
def ridgeSupport836_suffix_000 : List Nat := ridgeSupport836_000 ++ ridgeSupport836_suffix_001
theorem ridgeSupport836_source : candidateRows 836 =
    (PackedRawNatGrowth.readList 14 483 ridgeSupport836_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase01
