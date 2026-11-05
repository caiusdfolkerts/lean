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
def ridgeSupport772_000 : List Nat := [20,40,70,76,79,80,176,177,178,179,186,187,391,392,393,396,397,402,403,408,410,412,413,414,417,418,423,424,429,431,601,602]
def ridgeSupport772_001 : List Nat := [605,606,609,610,656,657,658,661,662,667,668,673,675,677,678,679,682,683,688,689,694,696,1024,1025,1026,1027,1028,1029,1076,1080,1081,1082]
def ridgeSupport772_002 : List Nat := [1083,1085,1086,1093,1095,1097,1101,1102,1103,1104,1106,1107,1114,1116,1160,1164,1165,1166,1167,1169,1170,1177,1179,1181,1185,1186,1187,1188,1190,1191,1198,1200]
def ridgeSupport772_003 : List Nat := [1202,1203,1207,1208,1209,1210,1212,1213,1221,1223,1224,1226,1760,1762,1764,1766,1782,1783,1788,1789,1794,1796,1800,1802,1822,1823,1828,1829,1830,1831,1836,1837]
def ridgeSupport772_004 : List Nat := [1856,1858,1862,1864,1870,1871,1876,1877,1878,1879,1881,1882,1892,1894,1896,1898,1914,1915,1920,1921,1926,1928,1932,1934,1954,1955,1960,1961,1962,1963,1968,1969]
def ridgeSupport772_005 : List Nat := [1988,1990,1994,1996,2002,2003,2008,2009,2010,2011,2013,2014,2130,2131,2138,2140,2142,2143,2150,2152,2166,2167,2178,2179,2184,2185,2192,2194,2196,2197,2204,2206]
def ridgeSupport772_006 : List Nat := [2220,2221,2232,2233,2732,2734,2736,2738,2758,2759,2764,2765,2766,2767,2772,2773,2778,2780,2784,2786,2792,2794,2798,2800,2806,2807,2812,2813,2814,2815,2820,2821]
def ridgeSupport772_007 : List Nat := [2845,2846,2848,2849,3002,3003,3152,3154,3156,3158,3178,3179,3184,3185,3186,3187,3192,3193,3198,3200,3204,3206,3212,3214,3218,3220,3226,3227,3232,3233,3234,3235]
def ridgeSupport772_008 : List Nat := [3240,3241,3265,3266,3268,3269,3380,3382,3384,3385,3402,3403,3410,3412,3420,3421,3429,3431,3434,3436,3438,3439,3456,3457,3464,3466,3474,3475,3483,3485,4088,4090]
def ridgeSupport772_009 : List Nat := [4092,4093,4100,4102,4104,4105,4113,4115,4119,4121,4142,4144,4146,4147,4154,4156,4158,4159,4167,4169,4173,4175,4412,4414,4416,4418,4424,4426,4428,4430,4446,4447]
def ridgeSupport772_010 : List Nat := [4452,4453,4509,4511,4513,4515,4545,4547,4549,4551,4568,4570,4574,4576,4641,4643,4647,4649,4734,4735,4770,4771,4936,4937,5068,5069]
def ridgeSupport772_code : Nat := 0x279b3cc9a4cd225472a293fc9fa453227911c8863c11de8ed476238f1c58e1c7063471a18cfc6762cb1648afc57a29d14c8a5452228514089f44f209f04d824c11e07f03e81e40ea06703281840ba033017809c0460130088034011ffaffc7fd3fe1b3ad9b6c9b649b14d886c0b601aded6e6b635a9aced656aeb571aa8d526a5b529a72d3869b34d198acc46613305952ca8651b289942ca064db269928c92647323190cc8464031f98f2c78639b1c98e2c70635b1a98acc546293141776bba590ac8163cb1d582ac115feafe57eabf15eeaf65782bb95d4ae85712b815b8ada56aab5159eace566ab3158eac65592ac155caac45ca2e115a8ac44f227112a8944492241112888441a2090ee87643421990be85e42e21690a68523ef1f74fb67da3ec9f60fa67d23e61f28f8c7c43d89ec0f567aa3d49ea0f467a23c71e30f107863c09e00ef677a3b51da0ecc7643ad1d64eae7563aa9d50e9e74e3a41d18e847403969cb0e4e7263929c90e3e71e3851c20e0870237e9bf0dee6f63731b90dc46e0265132098e4c525e92f09744b925c12dc9664b225812b894e4a6252128c9444a124e926c932492248923c91c48d24612208b845a22991488a044f227113489244722290f887a43b21d10e4870434202901080640220090005702b61588ac05562aa1538a9854a2a31508a7053629614a8a4852229013109844bc25d12d096435e1ad0d4069c3441a10cf067433819a0cc064c32418d0c6062431018705d82e81660b205882c00a004f0260118050014
def ridgeSupport772_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport772_code
def ridgeSupport772_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport772_code
def ridgeSupport772_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport772_code
def ridgeSupport772_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport772_code
def ridgeSupport772_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport772_code
def ridgeSupport772_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport772_code
def ridgeSupport772_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport772_code
def ridgeSupport772_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport772_code
def ridgeSupport772_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport772_code
def ridgeSupport772_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport772_code
def ridgeSupport772_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport772_code
def ridgeSupport772_rest_011 : Nat := PackedRawNatGrowth.drop 4498 ridgeSupport772_code
def ridgeSupport772_suffix_011 : List Nat := []
def ridgeSupport772_suffix_010 : List Nat := ridgeSupport772_010 ++ ridgeSupport772_suffix_011
def ridgeSupport772_suffix_009 : List Nat := ridgeSupport772_009 ++ ridgeSupport772_suffix_010
def ridgeSupport772_suffix_008 : List Nat := ridgeSupport772_008 ++ ridgeSupport772_suffix_009
def ridgeSupport772_suffix_007 : List Nat := ridgeSupport772_007 ++ ridgeSupport772_suffix_008
def ridgeSupport772_suffix_006 : List Nat := ridgeSupport772_006 ++ ridgeSupport772_suffix_007
def ridgeSupport772_suffix_005 : List Nat := ridgeSupport772_005 ++ ridgeSupport772_suffix_006
def ridgeSupport772_suffix_004 : List Nat := ridgeSupport772_004 ++ ridgeSupport772_suffix_005
def ridgeSupport772_suffix_003 : List Nat := ridgeSupport772_003 ++ ridgeSupport772_suffix_004
def ridgeSupport772_suffix_002 : List Nat := ridgeSupport772_002 ++ ridgeSupport772_suffix_003
def ridgeSupport772_suffix_001 : List Nat := ridgeSupport772_001 ++ ridgeSupport772_suffix_002
def ridgeSupport772_suffix_000 : List Nat := ridgeSupport772_000 ++ ridgeSupport772_suffix_001
theorem ridgeSupport772_source : candidateSupports 772 =
    (PackedRawNatGrowth.readList 13 346 ridgeSupport772_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase03
