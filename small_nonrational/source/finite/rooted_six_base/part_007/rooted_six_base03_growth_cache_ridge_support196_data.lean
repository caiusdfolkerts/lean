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
def ridgeSupport196_000 : List Nat := [15,35,65,71,77,78,116,117,118,119,126,127,348,349,353,355,356,360,362,363,365,369,370,374,376,377,381,383,384,386,541,542]
def ridgeSupport196_001 : List Nat := [545,546,549,550,613,614,618,620,621,625,627,628,630,634,635,639,641,642,646,648,649,651,964,965,966,967,968,969,1036,1037,1038,1041]
def ridgeSupport196_002 : List Nat := [1042,1043,1045,1050,1052,1057,1058,1059,1062,1063,1064,1066,1071,1073,1120,1121,1122,1125,1126,1127,1129,1134,1136,1141,1142,1143,1146,1147,1148,1150,1155,1157]
def ridgeSupport196_003 : List Nat := [1204,1205,1207,1208,1209,1210,1212,1213,1215,1216,1218,1219,1761,1763,1765,1767,1785,1787,1791,1793,1798,1799,1804,1805,1806,1807,1812,1813,1846,1847,1852,1853]
def ridgeSupport196_004 : List Nat := [1854,1855,1860,1861,1867,1869,1873,1875,1885,1886,1888,1889,1893,1895,1897,1899,1917,1919,1923,1925,1930,1931,1936,1937,1938,1939,1944,1945,1978,1979,1984,1985]
def ridgeSupport196_005 : List Nat := [1986,1987,1992,1993,1999,2001,2005,2007,2017,2018,2020,2021,2026,2027,2029,2031,2038,2039,2041,2043,2062,2063,2074,2075,2080,2081,2083,2085,2092,2093,2095,2097]
def ridgeSupport196_006 : List Nat := [2116,2117,2128,2129,2733,2735,2737,2739,2742,2743,2748,2749,2769,2771,2775,2777,2782,2783,2788,2789,2790,2791,2796,2797,2803,2805,2809,2811,2830,2831,2836,2837]
def ridgeSupport196_007 : List Nat := [2838,2839,2841,2842,2982,2983,3153,3155,3157,3159,3162,3163,3168,3169,3189,3191,3195,3197,3202,3203,3208,3209,3210,3211,3216,3217,3223,3225,3229,3231,3250,3251]
def ridgeSupport196_008 : List Nat := [3256,3257,3258,3259,3261,3262,3271,3273,3280,3281,3298,3299,3301,3303,3316,3317,3318,3320,3325,3327,3334,3335,3352,3353,3355,3357,3370,3371,3372,3374,3979,3981]
def ridgeSupport196_009 : List Nat := [3988,3989,3991,3993,4000,4001,4002,4004,4008,4010,4033,4035,4042,4043,4045,4047,4054,4055,4056,4058,4062,4064,4413,4415,4417,4419,4425,4427,4429,4431,4438,4439]
def ridgeSupport196_010 : List Nat := [4444,4445,4508,4510,4512,4514,4544,4546,4548,4550,4555,4557,4561,4563,4626,4628,4632,4634,4744,4745,4780,4781,4926,4927,5058,5059]
def ridgeSupport196_code : Nat := 0x27873c299fccfa55b2ac944ca2243521890a484a3a71d18e6c72e38d1c48e147023451a08cf46722bb15c8abc55a29f14d8a5c52628714189fc4f5fc0fde7ed3f61faefd67e7bf35f96fca7e1bf05f54fa87d23e89f42fa07ccbe5df2af947c6be2da5cd2c695b4a9a3ad1b68cb461a0ed0667fb3f59f0cf667ab3d19cece5671b3899a2cd0664b31d97ccbd65db2e9972cb8659b2c993ec9d64cb25d922c90645b229912c88641b2098fac7b63bb1d58c2c6062db1698aec55629b14574eba658d2c6562eb1658aac5161eb0e57dabe55eaaf3576abb15ceae6572ab915beade56cab5d5a6ad155eaaf156eab6559aac555eaad428a14108a844418a0bd05a82c412a08d04282040da06901e80e3fd9fe4fee7f63f79fb4fd67ea3f29f90fc47e13eb9f54fa27cf3e49f20f867c23e09f00f767ba3cc9e60f267923c89e40f1678a3c29e0cefe77d3b59da4ece7653b09d80ebc75d3a99d44e9a74b3a29d10e7e73e39e9cf0e6e73638a9c50e1e70e3869c30e0e7063809bfcdf66f93739b94dc66e126193089804bf25e92f09744b925c12dc96a4b4242920c8fc47c23d91e88ee47623a91c08dc46923391988ca462230918086242f21510a084e426211908884241c20d1054826412208903881a40c1e48f2078e3c61e28f105162891440a1850428113f89ec4f427613a09cc4e226d13609a84cc265113089444422110f08743041800bf85f42f21780bb05c82e216d0b585a82d01640b185842ba15c03f81f80ee07603a81d009c04d023810404600f
def ridgeSupport196_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport196_code
def ridgeSupport196_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport196_code
def ridgeSupport196_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport196_code
def ridgeSupport196_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport196_code
def ridgeSupport196_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport196_code
def ridgeSupport196_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport196_code
def ridgeSupport196_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport196_code
def ridgeSupport196_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport196_code
def ridgeSupport196_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport196_code
def ridgeSupport196_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport196_code
def ridgeSupport196_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport196_code
def ridgeSupport196_rest_011 : Nat := PackedRawNatGrowth.drop 4498 ridgeSupport196_code
def ridgeSupport196_suffix_011 : List Nat := []
def ridgeSupport196_suffix_010 : List Nat := ridgeSupport196_010 ++ ridgeSupport196_suffix_011
def ridgeSupport196_suffix_009 : List Nat := ridgeSupport196_009 ++ ridgeSupport196_suffix_010
def ridgeSupport196_suffix_008 : List Nat := ridgeSupport196_008 ++ ridgeSupport196_suffix_009
def ridgeSupport196_suffix_007 : List Nat := ridgeSupport196_007 ++ ridgeSupport196_suffix_008
def ridgeSupport196_suffix_006 : List Nat := ridgeSupport196_006 ++ ridgeSupport196_suffix_007
def ridgeSupport196_suffix_005 : List Nat := ridgeSupport196_005 ++ ridgeSupport196_suffix_006
def ridgeSupport196_suffix_004 : List Nat := ridgeSupport196_004 ++ ridgeSupport196_suffix_005
def ridgeSupport196_suffix_003 : List Nat := ridgeSupport196_003 ++ ridgeSupport196_suffix_004
def ridgeSupport196_suffix_002 : List Nat := ridgeSupport196_002 ++ ridgeSupport196_suffix_003
def ridgeSupport196_suffix_001 : List Nat := ridgeSupport196_001 ++ ridgeSupport196_suffix_002
def ridgeSupport196_suffix_000 : List Nat := ridgeSupport196_000 ++ ridgeSupport196_suffix_001
theorem ridgeSupport196_source : candidateSupports 196 =
    (PackedRawNatGrowth.readList 13 346 ridgeSupport196_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase03
