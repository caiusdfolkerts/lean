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
def ridgeSupport328_000 : List Nat := [22,42,72,78,83,85,186,187,188,189,196,197,418,420,422,424,426,431,432,434,437,460,461,465,467,468,472,474,475,477,627,628]
def ridgeSupport328_001 : List Nat := [631,632,635,636,687,689,691,693,695,700,701,703,706,729,730,734,736,737,741,743,744,746,1003,1004,1005,1006,1007,1008,1062,1064,1066,1067]
def ridgeSupport328_002 : List Nat := [1069,1071,1072,1076,1081,1105,1106,1107,1110,1111,1112,1114,1119,1121,1146,1148,1150,1151,1153,1155,1156,1160,1165,1189,1190,1191,1194,1195,1196,1198,1203,1205]
def ridgeSupport328_003 : List Nat := [1230,1232,1233,1235,1236,1238,1240,1241,1243,1244,1248,1249,2403,2405,2414,2419,2470,2471,2480,2481,2493,2496,2502,2503,2507,2509,2512,2513,2518,2519,2528,2529]
def ridgeSupport328_004 : List Nat := [2566,2567,2571,2573,2576,2577,2582,2587,2598,2599,2608,2609,2622,2623,2632,2633,2643,2645,2654,2659,2710,2711,2720,2721,2733,2736,2742,2743,2747,2749,2752,2753]
def ridgeSupport328_005 : List Nat := [2758,2759,2768,2769,2806,2807,2811,2813,2816,2817,2822,2827,2838,2839,2848,2849,2862,2863,2872,2873,2882,2887,2894,2899,2914,2915,2926,2927,3027,3029,3039,3041]
def ridgeSupport328_006 : List Nat := [3060,3061,3072,3073,3435,3437,3446,3451,3454,3455,3464,3465,3502,3503,3512,3513,3525,3528,3534,3535,3539,3541,3544,3545,3550,3551,3555,3557,3560,3561,3566,3571]
def ridgeSupport328_007 : List Nat := [3598,3599,3608,3609,3622,3623,3632,3633,3660,3661,3672,3673,4011,4013,4022,4027,4030,4031,4040,4041,4078,4079,4088,4089,4101,4104,4110,4111,4115,4117,4120,4121]
def ridgeSupport328_008 : List Nat := [4126,4127,4131,4133,4136,4137,4142,4147,4174,4175,4184,4185,4198,4199,4208,4209,4220,4225,4250,4255,4264,4265,4282,4283,4365,4367,4395,4397,4410,4411,4428,4429]
def ridgeSupport328_009 : List Nat := [4856,4861,4868,4873,4900,4901,4912,4913,5001,5003,5013,5015,5046,5047,5058,5059,5745,5748,5751,5755,5769,5772,5778,5779,5783,5785,5788,5789,5794,5795,5804,5805]
def ridgeSupport328_010 : List Nat := [5826,5827,5836,5837,5842,5843,5847,5849,5852,5853,5858,5863,5868,5869,5873,5875,5877,5880,5883,5887,5901,5904,5910,5911,5915,5917,5920,5921,5926,5927,5936,5937]
def ridgeSupport328_011 : List Nat := [5958,5959,5968,5969,5974,5975,5979,5981,5984,5985,5990,5995,6000,6001,6005,6007,6010,6011,6014,6019,6022,6023,6026,6031,6046,6047,6058,6059,6120,6121,6123,6125]
def ridgeSupport328_012 : List Nat := [6132,6133,6135,6137,6156,6157,6168,6169,6369,6372,6375,6379,6382,6383,6392,6393,6405,6408,6414,6415,6419,6421,6424,6425,6430,6431,6435,6437,6440,6441,6446,6451]
def ridgeSupport328_013 : List Nat := [6462,6463,6472,6473,6476,6478,6482,6483,6492,6493,6657,6660,6663,6667,6670,6671,6680,6681,6693,6696,6702,6703,6707,6709,6712,6713,6718,6719,6723,6725,6728,6729]
def ridgeSupport328_014 : List Nat := [6734,6739,6750,6751,6760,6761,6764,6766,6770,6771,6776,6781,6784,6785,6802,6803,6806,6811,6820,6821,6825,6828,6885,6887,6894,6895,6912,6913,6915,6917,6930,6931]
def ridgeSupport328_015 : List Nat := [6932,6934,7160,7165,7168,7169,7172,7177,7180,7181,7185,7188,7191,7194,7269,7271,7278,7279,7281,7283,7290,7291,7292,7294,7298,7300,7425,7428,7431,7435,7437,7440]
def ridgeSupport328_016 : List Nat := [7443,7447,7450,7451,7464,7465,7484,7489,7490,7494,7508,7513,7514,7518,7520,7525,7533,7535,7557,7560,7568,7570,7744,7745,7780,7781,7870,7871,7966,7967]
def ridgeSupport328_code : Nat := 0x3e3ff1ef5ffafbccbe64f20f903b25d90ec47617adfd6deb2f583abdd5aeacf553a8dd42ea0f4f3a53d28e8df46ba2fd13e887437a17d07e827407909c82e3f71f38f7c7ae39f1c78dfc6ee33f197835c17e0a704781bc0ce04f013803c00dfeefe362db14d89ec4b60bb03d80ec035dfaeed73eb97559aa9d52ea93537a96d49ea4b503a80d3ee9e34e7a72d3769b34d3a68d2fe97b4a7a4ed24e92348ba43d1fe8fb473a38d1ae8cf45fa2ed146897433a18d07e83b417a07d0268072bb95cca9e54b29d94cca4e52327f93ec99e4bb253928c92e48f23f91ec8ce46322b913c87e43b211905c7ce3e31df8eec75e39f1c98e1c0ce06301b80cbfcdfdefeb7f4bf6dfaefd37e8bd5deaaf3f79ebc7de2af0f786bc1ddfaef777abbbddd6ee3770bb5dd9aec3760baedd6eeaf756ba8dd42e8f746b98dcc2e4f726b90dc82e3b71bb8bdc5ae2170db7fdbeedf16f5b79dbc6ddb6ecb73db8adbb6dcb6cdb5eda76d2b66db32d876c2b56dab2d476a2b4eda72d33697b49da4ad19689b3dd9dece96719e1cf0a76f3b69cbce56717389998ccc264b324984cc125fb2f88a6c53227713a896c4ae21f10d85dc2ea1530a884fc26a10307c838c1c20cf06682cc16209f04e819c0ba053028812c08e03f01e80cc06202b013807c03a0110057fcbfe1fdefee7e4bf21f7efbe7ddbed9f5afab72cb961c9ae4c718b8c1c4ee2670cb861c1ee0e6f9b7b9bd2de86f2b78dbbedde6ecb761baadd36e7b739b90dc56dcb6e1b5edae6c4b621afed7e6bdb5d9adad6b600b0017eabf45f0af7d7aabd35b7adb96c6b625a9ad3968eb4259cace165eb2e590ac8162eb16585ac19602b0057eabed5eeaf6568ab4158eac6560ab0157aabb55baad9560aad550aa8152ea96531a9794aaa53524a92147ea3e518a8c144ea2650da859422a10506a82d40ea064f0a7813ae9d64e8a74139a9cb4e3a7193809bd4d8a6c134e9a64b9a5b92ca96327093809b84db26c93609ac4d426993449a04ce25a92cc95c4ac25592a894e4a6252923491048424192048fe47e23e11e88c245f22d11608ae45622991488a243921a10c085e42d21590a88504261f80fbc7dc3ed1f60fac5d42e81738b945c22e016f0b685b22c215f8af45782b715a8acc5622af13e09ec4f027713a09cc3ba1db0ed07603a81d30e887343981b50d906c035e1aa0d406983481a2062831017a0bc05d82e80aa0530270120054016
def ridgeSupport328_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport328_code
def ridgeSupport328_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport328_code
def ridgeSupport328_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport328_code
def ridgeSupport328_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport328_code
def ridgeSupport328_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport328_code
def ridgeSupport328_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport328_code
def ridgeSupport328_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport328_code
def ridgeSupport328_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport328_code
def ridgeSupport328_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport328_code
def ridgeSupport328_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport328_code
def ridgeSupport328_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport328_code
def ridgeSupport328_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport328_code
def ridgeSupport328_rest_012 : Nat := PackedRawNatGrowth.drop 4992 ridgeSupport328_code
def ridgeSupport328_rest_013 : Nat := PackedRawNatGrowth.drop 5408 ridgeSupport328_code
def ridgeSupport328_rest_014 : Nat := PackedRawNatGrowth.drop 5824 ridgeSupport328_code
def ridgeSupport328_rest_015 : Nat := PackedRawNatGrowth.drop 6240 ridgeSupport328_code
def ridgeSupport328_rest_016 : Nat := PackedRawNatGrowth.drop 6656 ridgeSupport328_code
def ridgeSupport328_rest_017 : Nat := PackedRawNatGrowth.drop 7046 ridgeSupport328_code
def ridgeSupport328_suffix_017 : List Nat := []
def ridgeSupport328_suffix_016 : List Nat := ridgeSupport328_016 ++ ridgeSupport328_suffix_017
def ridgeSupport328_suffix_015 : List Nat := ridgeSupport328_015 ++ ridgeSupport328_suffix_016
def ridgeSupport328_suffix_014 : List Nat := ridgeSupport328_014 ++ ridgeSupport328_suffix_015
def ridgeSupport328_suffix_013 : List Nat := ridgeSupport328_013 ++ ridgeSupport328_suffix_014
def ridgeSupport328_suffix_012 : List Nat := ridgeSupport328_012 ++ ridgeSupport328_suffix_013
def ridgeSupport328_suffix_011 : List Nat := ridgeSupport328_011 ++ ridgeSupport328_suffix_012
def ridgeSupport328_suffix_010 : List Nat := ridgeSupport328_010 ++ ridgeSupport328_suffix_011
def ridgeSupport328_suffix_009 : List Nat := ridgeSupport328_009 ++ ridgeSupport328_suffix_010
def ridgeSupport328_suffix_008 : List Nat := ridgeSupport328_008 ++ ridgeSupport328_suffix_009
def ridgeSupport328_suffix_007 : List Nat := ridgeSupport328_007 ++ ridgeSupport328_suffix_008
def ridgeSupport328_suffix_006 : List Nat := ridgeSupport328_006 ++ ridgeSupport328_suffix_007
def ridgeSupport328_suffix_005 : List Nat := ridgeSupport328_005 ++ ridgeSupport328_suffix_006
def ridgeSupport328_suffix_004 : List Nat := ridgeSupport328_004 ++ ridgeSupport328_suffix_005
def ridgeSupport328_suffix_003 : List Nat := ridgeSupport328_003 ++ ridgeSupport328_suffix_004
def ridgeSupport328_suffix_002 : List Nat := ridgeSupport328_002 ++ ridgeSupport328_suffix_003
def ridgeSupport328_suffix_001 : List Nat := ridgeSupport328_001 ++ ridgeSupport328_suffix_002
def ridgeSupport328_suffix_000 : List Nat := ridgeSupport328_000 ++ ridgeSupport328_suffix_001
theorem ridgeSupport328_source : candidateSupports 328 =
    (PackedRawNatGrowth.readList 13 542 ridgeSupport328_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
