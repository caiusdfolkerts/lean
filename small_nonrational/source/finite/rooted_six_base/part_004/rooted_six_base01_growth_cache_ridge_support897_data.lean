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
def ridgeSupport897_000 : List Nat := [335,336,337,491,492,493,575,576,577,597,598,599,1650,1651,1652,1653,1654,1655,1698,1699,1700,1701,1702,1703,1842,1843,1844,1845,1846,1847,1914,1915]
def ridgeSupport897_001 : List Nat := [1916,1917,1918,1919,1962,1963,1964,1965,1966,1967,2106,2107,2108,2109,2110,2111,2754,2755,2756,2757,2758,2759,2766,2767,2768,2769,2770,2771,2874,2875,2876,2877]
def ridgeSupport897_002 : List Nat := [2878,2879,2922,2923,2924,2925,2926,2927,3066,3067,3068,3069,3070,3071,3714,3715,3716,3717,3718,3719,3726,3727,3728,3729,3730,3731,4410,4411,4412,4413,4414,4415]
def ridgeSupport897_003 : List Nat := [4422,4423,4424,4425,4426,4427,7179,7181,7185,7187,7191,7193,7200,7201,7206,7207,7212,7213,7248,7249,7254,7255,7260,7261,7347,7349,7353,7355,7359,7361,7362,7363]
def ridgeSupport897_004 : List Nat := [7364,7365,7366,7367,7419,7421,7425,7427,7431,7433,7440,7441,7446,7447,7452,7453,7488,7489,7494,7495,7500,7501,7587,7589,7593,7595,7599,7601,7602,7603,7604,7605]
def ridgeSupport897_005 : List Nat := [7606,7607,8154,8155,8156,8157,8158,8159,8166,8167,8168,8169,8170,8171,8187,8189,8193,8195,8199,8201,8208,8209,8214,8215,8220,8221,8256,8257,8262,8263,8268,8269]
def ridgeSupport897_006 : List Nat := [8355,8357,8361,8363,8367,8369,8370,8371,8372,8373,8374,8375,8922,8923,8924,8925,8926,8927,8934,8935,8936,8937,8938,8939,9450,9451,9452,9453,9454,9455,9462,9463]
def ridgeSupport897_007 : List Nat := [9464,9465,9466,9467,11641,11643,11645,11739,11741,11745,11747,11751,11753,11773,11775,11777,11871,11873,11877,11879,11883,11885,12240,12241,12242,12243,12244,12245,12253,12255,12257,12351]
def ridgeSupport897_008 : List Nat := [12353,12357,12359,12363,12365,12720,12721,12722,12723,12724,12725,13068,13069,13070,13071,13072,13073,14690,14692,14696,14698,14702,14704,14726,14728,14732,14734,14738,14740,14822,14824,14828]
def ridgeSupport897_009 : List Nat := [14830,14834,14836]
def ridgeSupport897_code : Nat := 0x39f4e7cb9eee7b39e8e79b994e64b98ee633988e61b970e5bb96ae5a3964e58b311cc4330fcc3b30dcc331b5c6d31b3c6cb1b1c6c304dc12f047c117041c0fefe1bf7efddbf56fd4bf4efd2bf46fd0b9b6e6bb99ee65b986e5fb806dffb7f6de9b79ede3b786dddb76ed7db5eed7993ee4fa93e64f893de4f693be4ee93b64ec93ae4ea8bae2ea8ba62e88b9e2e68b7e2de8b762dc8b6e2da82de0b682d60b482ce0b282c60af82ae0a982960a3813604c811e0468106040807601c805e01680460108026007800e0017ff5ffb7fadfea7fa5fe87f9dfe67f7dfde7f75fdc7f6dfda76dddb676d5db476cddb276c5daf76adda97695da37535d4c751dd467505d407475d1c745dd167445d107425d07740dd0173f5cfb731dcc67315cc4730dcc27305cbf72edcb972d5cb37175c5c715dc567145c5070b5c2c709dc267085c207065c17704dc117035c0b452d14a4525148451d14644fd13e44f513c44ed13a3a4ce923a44e903a3ce8e3a1ce863a14e843a0ce822ffcbfe2ff4bfc2fecbfa2dbcb6e2db4b6c2dacb6a2cfcb3e2cf4b3c2cecb3a2b4cad22b44ad02b3cace2b1cac62b14ac42b0cac220fc83e20f483c20ec83a1ebc7ae1eb47ac1eac7aa1dfc77e1df477c1dec77a1cdc7361cd47341ccc7321a9c6a61a946a41a8c6a219dc67619d467419cc672095c2560954241090023f07b41ec07ac151054014f
def ridgeSupport897_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport897_code
def ridgeSupport897_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport897_code
def ridgeSupport897_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport897_code
def ridgeSupport897_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport897_code
def ridgeSupport897_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport897_code
def ridgeSupport897_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport897_code
def ridgeSupport897_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport897_code
def ridgeSupport897_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport897_code
def ridgeSupport897_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport897_code
def ridgeSupport897_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport897_code
def ridgeSupport897_rest_010 : Nat := PackedRawNatGrowth.drop 4074 ridgeSupport897_code
def ridgeSupport897_suffix_010 : List Nat := []
def ridgeSupport897_suffix_009 : List Nat := ridgeSupport897_009 ++ ridgeSupport897_suffix_010
def ridgeSupport897_suffix_008 : List Nat := ridgeSupport897_008 ++ ridgeSupport897_suffix_009
def ridgeSupport897_suffix_007 : List Nat := ridgeSupport897_007 ++ ridgeSupport897_suffix_008
def ridgeSupport897_suffix_006 : List Nat := ridgeSupport897_006 ++ ridgeSupport897_suffix_007
def ridgeSupport897_suffix_005 : List Nat := ridgeSupport897_005 ++ ridgeSupport897_suffix_006
def ridgeSupport897_suffix_004 : List Nat := ridgeSupport897_004 ++ ridgeSupport897_suffix_005
def ridgeSupport897_suffix_003 : List Nat := ridgeSupport897_003 ++ ridgeSupport897_suffix_004
def ridgeSupport897_suffix_002 : List Nat := ridgeSupport897_002 ++ ridgeSupport897_suffix_003
def ridgeSupport897_suffix_001 : List Nat := ridgeSupport897_001 ++ ridgeSupport897_suffix_002
def ridgeSupport897_suffix_000 : List Nat := ridgeSupport897_000 ++ ridgeSupport897_suffix_001
theorem ridgeSupport897_source : candidateRows 897 =
    (PackedRawNatGrowth.readList 14 291 ridgeSupport897_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase01
