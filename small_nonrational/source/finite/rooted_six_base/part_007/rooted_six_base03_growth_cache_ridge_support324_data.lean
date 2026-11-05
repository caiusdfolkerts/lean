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
def ridgeSupport324_000 : List Nat := [16,36,66,72,77,79,128,129,130,131,138,139,348,350,352,354,356,361,362,364,367,390,391,395,397,398,402,404,405,407,553,554]
def ridgeSupport324_001 : List Nat := [557,558,561,562,613,615,617,619,621,626,627,629,632,655,656,660,662,663,667,669,670,672,976,977,978,979,980,981,1035,1037,1039,1040]
def ridgeSupport324_002 : List Nat := [1042,1044,1045,1049,1054,1078,1079,1080,1083,1084,1085,1087,1092,1094,1119,1121,1123,1124,1126,1128,1129,1133,1138,1162,1163,1164,1167,1168,1169,1171,1176,1178]
def ridgeSupport324_003 : List Nat := [1203,1205,1206,1208,1209,1211,1213,1214,1216,1217,1221,1222,1759,1762,1765,1769,1783,1786,1792,1793,1797,1799,1802,1803,1808,1809,1818,1819,1840,1841,1850,1851]
def ridgeSupport324_004 : List Nat := [1856,1857,1861,1863,1866,1867,1872,1877,1882,1883,1887,1889,1891,1894,1897,1901,1915,1918,1924,1925,1929,1931,1934,1935,1940,1941,1950,1951,1972,1973,1982,1983]
def ridgeSupport324_005 : List Nat := [1988,1989,1993,1995,1998,1999,2004,2009,2014,2015,2019,2021,2024,2025,2028,2033,2036,2037,2040,2045,2060,2061,2072,2073,2134,2135,2137,2139,2146,2147,2149,2151]
def ridgeSupport324_006 : List Nat := [2170,2171,2182,2183,2731,2734,2737,2741,2744,2745,2754,2755,2767,2770,2776,2777,2781,2783,2786,2787,2792,2793,2797,2799,2802,2803,2808,2813,2824,2825,2834,2835]
def ridgeSupport324_007 : List Nat := [2838,2840,2844,2845,2986,2987,3151,3154,3157,3161,3164,3165,3174,3175,3187,3190,3196,3197,3201,3203,3206,3207,3212,3213,3217,3219,3222,3223,3228,3233,3244,3245]
def ridgeSupport324_008 : List Nat := [3254,3255,3258,3260,3264,3265,3270,3275,3278,3279,3296,3297,3300,3305,3314,3315,3319,3322,3379,3381,3388,3389,3406,3407,3409,3411,3424,3425,3426,3428,3978,3983]
def ridgeSupport324_009 : List Nat := [3986,3987,3990,3995,3998,3999,4003,4006,4009,4012,4087,4089,4096,4097,4099,4101,4108,4109,4110,4112,4116,4118,4411,4414,4417,4421,4423,4426,4429,4433,4436,4437]
def ridgeSupport324_010 : List Nat := [4450,4451,4506,4511,4512,4516,4542,4547,4548,4552,4554,4559,4567,4569,4627,4630,4638,4640,4742,4743,4778,4779,4928,4929,5060,5061]
def ridgeSupport324_code : Nat := 0x278b3c49a0cd025572aa943ca1a44121e90b484e3b31d78e7c72a3911c48e1c6fa3491a08cfc66a2c71628aac5522a314d8a5451e28b14189f44ee02d014808403a01b00c802c00e0030007fcbfddf58fa97d33e8df3ef9e7cdbe59f26f927c7be29ac8d626b0b581aa6d516a7b539a7ad3c69ab4cd9f4cf7679b3c99d2ce4670b38199ecce665b319982cc065e32e996ecb6656b2b1942c9c64bb259926c91646b23190ec86641b2058fac7c63b31cd8cec6662eb1718b2c55629313d756baa58eac71630b16589ac49612b0857eabe15e6af2577abb55d2ae8571ab895beadd56cab615a4acf561ab09572ab855aaac555caab443a2190f687a433a1950c686242da1650ae85640ca06101a80c3fe9fe0fea7f43f89fb0fd27e83f29f8cfbe7de3ec9f50f9e7ce3e59f24f8a7c43df9ef8f6a7b43cf9e78f2a7943c79e38f167893c29e10efc77b3b69da4ecc7633b09d7ceb675a3aa9d40e9674a3a39d14e8274039d9ce8e6273038d9c68e227103859c28e0e7053809c00df46f73749b94dc46df26313149824c025f12f49764b925c12d896a4b324d1260926491248123c91848b24511c88da46923411988c8463230917c88c44421f90f487843b21c10dc86c41e20c9054828412208103c81a40b1ea8f507a63d21e88f4054029e14e8a6c52e29614a0a4051e27813a89cc4e426d13589a44ce26511908c445c22d11508a432e1950ca064831c18d0c5861c30c16f0b605a82d21640b105802bc15c0458228106082040820009e04d0240108048010
def ridgeSupport324_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport324_code
def ridgeSupport324_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport324_code
def ridgeSupport324_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport324_code
def ridgeSupport324_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport324_code
def ridgeSupport324_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport324_code
def ridgeSupport324_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport324_code
def ridgeSupport324_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport324_code
def ridgeSupport324_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport324_code
def ridgeSupport324_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport324_code
def ridgeSupport324_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport324_code
def ridgeSupport324_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport324_code
def ridgeSupport324_rest_011 : Nat := PackedRawNatGrowth.drop 4498 ridgeSupport324_code
def ridgeSupport324_suffix_011 : List Nat := []
def ridgeSupport324_suffix_010 : List Nat := ridgeSupport324_010 ++ ridgeSupport324_suffix_011
def ridgeSupport324_suffix_009 : List Nat := ridgeSupport324_009 ++ ridgeSupport324_suffix_010
def ridgeSupport324_suffix_008 : List Nat := ridgeSupport324_008 ++ ridgeSupport324_suffix_009
def ridgeSupport324_suffix_007 : List Nat := ridgeSupport324_007 ++ ridgeSupport324_suffix_008
def ridgeSupport324_suffix_006 : List Nat := ridgeSupport324_006 ++ ridgeSupport324_suffix_007
def ridgeSupport324_suffix_005 : List Nat := ridgeSupport324_005 ++ ridgeSupport324_suffix_006
def ridgeSupport324_suffix_004 : List Nat := ridgeSupport324_004 ++ ridgeSupport324_suffix_005
def ridgeSupport324_suffix_003 : List Nat := ridgeSupport324_003 ++ ridgeSupport324_suffix_004
def ridgeSupport324_suffix_002 : List Nat := ridgeSupport324_002 ++ ridgeSupport324_suffix_003
def ridgeSupport324_suffix_001 : List Nat := ridgeSupport324_001 ++ ridgeSupport324_suffix_002
def ridgeSupport324_suffix_000 : List Nat := ridgeSupport324_000 ++ ridgeSupport324_suffix_001
theorem ridgeSupport324_source : candidateSupports 324 =
    (PackedRawNatGrowth.readList 13 346 ridgeSupport324_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase03
