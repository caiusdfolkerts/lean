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
def ridgeSupport580_000 : List Nat := [17,37,67,73,78,79,140,141,142,143,150,151,369,371,373,375,377,382,383,385,388,390,392,394,396,398,403,404,406,409,565,566]
def ridgeSupport580_001 : List Nat := [569,570,573,574,634,636,638,640,642,647,648,650,653,655,657,659,661,663,668,669,671,674,988,989,990,991,992,993,1056,1058,1060,1061]
def ridgeSupport580_002 : List Nat := [1063,1065,1066,1070,1075,1077,1079,1081,1082,1084,1086,1087,1091,1096,1140,1142,1144,1145,1147,1149,1150,1154,1159,1161,1163,1165,1166,1168,1170,1171,1175,1180]
def ridgeSupport580_003 : List Nat := [1203,1204,1206,1207,1210,1211,1212,1214,1215,1217,1224,1225,1758,1760,1767,1769,1782,1784,1790,1791,1796,1797,1803,1805,1810,1811,1824,1825,1838,1839,1844,1845]
def ridgeSupport580_004 : List Nat := [1858,1859,1860,1865,1866,1871,1872,1873,1881,1883,1884,1886,1890,1892,1899,1901,1914,1916,1922,1923,1928,1929,1935,1937,1942,1943,1956,1957,1970,1971,1976,1977]
def ridgeSupport580_005 : List Nat := [1990,1991,1992,1997,1998,2003,2004,2005,2013,2015,2016,2018,2078,2079,2082,2087,2090,2091,2094,2099,2114,2115,2126,2127,2132,2133,2136,2141,2144,2145,2148,2153]
def ridgeSupport580_006 : List Nat := [2168,2169,2180,2181,2730,2732,2739,2741,2746,2747,2760,2761,2766,2768,2774,2775,2780,2781,2787,2789,2794,2795,2796,2801,2802,2807,2808,2809,2822,2823,2828,2829]
def ridgeSupport580_007 : List Nat := [2839,2840,2847,2848,2990,2991,3150,3152,3159,3161,3166,3167,3180,3181,3186,3188,3194,3195,3200,3201,3207,3209,3214,3215,3216,3221,3222,3227,3228,3229,3242,3243]
def ridgeSupport580_008 : List Nat := [3248,3249,3259,3260,3267,3268,3324,3329,3332,3333,3350,3351,3354,3359,3368,3369,3373,3376,3378,3383,3386,3387,3404,3405,3408,3413,3422,3423,3427,3430,4032,4037]
def ridgeSupport580_009 : List Nat := [4040,4041,4044,4049,4052,4053,4057,4060,4063,4066,4086,4091,4094,4095,4098,4103,4106,4107,4111,4114,4117,4120,4410,4412,4419,4421,4422,4424,4431,4433,4442,4443]
def ridgeSupport580_010 : List Nat := [4448,4449,4507,4509,4514,4516,4543,4545,4550,4552,4560,4565,4566,4571,4633,4636,4639,4642,4740,4741,4776,4777,4930,4931,5062,5063]
def ridgeSupport580_code : Nat := 0x278f3c69a1cd0a5532a8942ca1244521f90e48663b71d68eac7423911c68e0c6fe3491a28cec66e2c31608adc56a2a314f8a4451a28b14389e44ea031015809403e01700a803c009ffeffe7fdbfd9fc4fdf7ee3f65faafd47e8bf31f92fc87e2bf01accd636afb579aaad506a6b531a76d3a69bb4c9a60d2d694b4a1a3ed1a68bb459a0ad04680b3f1988cc365e32ed962cb0655b2a993ac9c64db25992ac90647b239912c87640b2018f6c7a63a31c98dac6c62fb1798b2c57628313975ebae5902c7d630b17586ac3160eb0657cabe15eeaf2578abb15d6aea572ab8d5baadc56bab595a0ace564ab21576aba55aaacd558aaa442a2110f2878434a1910c286042ea1610aa854427a139086842419a0b905682a413a08903e81e3f11f80fbe7dd3ea9f50fa67ce3e69f20f8e7c63dc9ee0f667b23d29e90f2e7963c89e3cf127883c19e08ef877a3b69dacec87623af1d70eb67593a89d40e9e74a3a49d10e8674239a9cd0e5e72e3909c80e267123869c2ce0a70437f9bf8df06f63749b9cdc06de26493209824bf25f12f09764ba25b92d89684b324e125c926492248123891a48b244921c90447e23e91ec8f247823b11d089044321f90f887843a21c90dc86a43321710a885242721290908444201f08f807be3de1ee8f7054429f14e8a7052e2951498a4451e28d1450a2050e28214009f84f827a11f08f447423911b08d43321960ca064c31c18c0c5062030c1840c085fc2fc1790bb85d42e617104b825811e08e046823009e04e024810c04a011
def ridgeSupport580_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport580_code
def ridgeSupport580_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport580_code
def ridgeSupport580_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport580_code
def ridgeSupport580_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport580_code
def ridgeSupport580_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport580_code
def ridgeSupport580_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport580_code
def ridgeSupport580_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport580_code
def ridgeSupport580_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport580_code
def ridgeSupport580_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport580_code
def ridgeSupport580_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport580_code
def ridgeSupport580_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport580_code
def ridgeSupport580_rest_011 : Nat := PackedRawNatGrowth.drop 4498 ridgeSupport580_code
def ridgeSupport580_suffix_011 : List Nat := []
def ridgeSupport580_suffix_010 : List Nat := ridgeSupport580_010 ++ ridgeSupport580_suffix_011
def ridgeSupport580_suffix_009 : List Nat := ridgeSupport580_009 ++ ridgeSupport580_suffix_010
def ridgeSupport580_suffix_008 : List Nat := ridgeSupport580_008 ++ ridgeSupport580_suffix_009
def ridgeSupport580_suffix_007 : List Nat := ridgeSupport580_007 ++ ridgeSupport580_suffix_008
def ridgeSupport580_suffix_006 : List Nat := ridgeSupport580_006 ++ ridgeSupport580_suffix_007
def ridgeSupport580_suffix_005 : List Nat := ridgeSupport580_005 ++ ridgeSupport580_suffix_006
def ridgeSupport580_suffix_004 : List Nat := ridgeSupport580_004 ++ ridgeSupport580_suffix_005
def ridgeSupport580_suffix_003 : List Nat := ridgeSupport580_003 ++ ridgeSupport580_suffix_004
def ridgeSupport580_suffix_002 : List Nat := ridgeSupport580_002 ++ ridgeSupport580_suffix_003
def ridgeSupport580_suffix_001 : List Nat := ridgeSupport580_001 ++ ridgeSupport580_suffix_002
def ridgeSupport580_suffix_000 : List Nat := ridgeSupport580_000 ++ ridgeSupport580_suffix_001
theorem ridgeSupport580_source : candidateSupports 580 =
    (PackedRawNatGrowth.readList 13 346 ridgeSupport580_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase03
