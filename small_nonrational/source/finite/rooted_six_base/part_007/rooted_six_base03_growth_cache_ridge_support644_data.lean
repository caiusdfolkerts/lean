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
def ridgeSupport644_000 : List Nat := [19,39,69,75,78,80,164,165,166,167,174,175,370,371,372,375,376,381,382,387,389,411,413,415,417,419,424,425,427,430,589,590]
def ridgeSupport644_001 : List Nat := [593,594,597,598,635,636,637,640,641,646,647,652,654,676,678,680,682,684,689,690,692,695,1012,1013,1014,1015,1016,1017,1055,1059,1060,1061]
def ridgeSupport644_002 : List Nat := [1062,1064,1065,1072,1074,1098,1100,1102,1103,1105,1107,1108,1112,1117,1139,1143,1144,1145,1146,1148,1149,1156,1158,1182,1184,1186,1187,1189,1191,1192,1196,1201]
def ridgeSupport644_003 : List Nat := [1202,1204,1206,1208,1209,1211,1213,1214,1218,1220,1225,1226,1758,1763,1764,1768,1784,1785,1788,1790,1794,1795,1801,1804,1816,1817,1826,1827,1832,1833,1842,1843]
def ridgeSupport644_004 : List Nat := [1854,1859,1864,1865,1868,1870,1874,1875,1878,1880,1884,1885,1890,1895,1896,1900,1916,1917,1920,1922,1926,1927,1933,1936,1948,1949,1958,1959,1964,1965,1974,1975]
def ridgeSupport644_005 : List Nat := [1986,1991,1996,1997,2000,2002,2006,2007,2010,2012,2016,2017,2076,2077,2084,2086,2088,2089,2096,2098,2112,2113,2124,2125,2186,2187,2190,2195,2198,2199,2202,2207]
def ridgeSupport644_006 : List Nat := [2222,2223,2234,2235,2730,2735,2736,2740,2752,2753,2762,2763,2768,2769,2772,2774,2778,2779,2785,2788,2790,2795,2800,2801,2804,2806,2810,2811,2816,2817,2826,2827]
def ridgeSupport644_007 : List Nat := [2842,2843,2847,2849,2998,2999,3150,3155,3156,3160,3172,3173,3182,3183,3188,3189,3192,3194,3198,3199,3205,3208,3210,3215,3220,3221,3224,3226,3230,3231,3236,3237]
def ridgeSupport644_008 : List Nat := [3246,3247,3262,3263,3267,3269,3326,3328,3330,3331,3348,3349,3356,3358,3366,3367,3375,3377,3432,3437,3440,3441,3458,3459,3462,3467,3476,3477,3481,3484,4034,4036]
def ridgeSupport644_009 : List Nat := [4038,4039,4046,4048,4050,4051,4059,4061,4065,4067,4140,4145,4148,4149,4152,4157,4160,4161,4165,4168,4171,4174,4410,4415,4416,4420,4422,4427,4428,4432,4440,4441]
def ridgeSupport644_010 : List Nat := [4454,4455,4507,4510,4513,4517,4543,4546,4549,4553,4562,4564,4572,4577,4635,4637,4645,4648,4736,4737,4772,4773,4934,4935,5066,5067]
def ridgeSupport644_code : Nat := 0x27973ca9a3cd1a54b2a4940ca0245122590ec86e3c31dc8ea474a3931c58e146fe34b1a18cf466e2cf1668acc5622a114c8a5c51a28914089fc4ea09d04b824411608304081ec0e206b034818c0b1fc6fe17eebf6dfa6fd27e83f39f8efc67e23f09b38d996cab651b16d866c1b609ae2d706b6b5a1a62d2f693b499a3cd1c68ab451a06d0268033f998acc365fb2f995ecae652b29193ec9e64d326192ac94647b229910c8563fb1f98f4c7863ab1d18dec6e632b1918b0c54629b13976ebb6590ac7d636b1a585ac29602b0057dabe95ecaf4578abc15d6ae65722b855b6ada56b2b515a2ad0565ab29582ac055a2ac155eaaa45da2e915e8ae44fa26912e896449a23911688a426a13108284041920c1052828413209103a81c3f09f80fb87da3eb9f58fa47d03e69f30f8e7c23db9ed8f5a7ac3d39e98f3a79c3c81e34f0e7863c11e00efa77c3b61da0ece7623ae9d70eb07563a99d48e9c74c3a49d20e8673e3999cc8e527283919c88e327183861c24e0670237f1bf0df26f83741b90dc66de26513249884c225f12f49764b925c12d89684b225892b09504a7252928c9444a024f121890847d23e11e88f247823b91cc8ba45822a114c8a244f227113089443221810a4850426212909084641f1fc8fe07ee3f61fa8fd056e2b41590ac45582aa1540a9854828e1460a1c50c28114009f44f827b12b09544a4251127093435c1ab0d486a03461a10cf86743361850c185f82fa1780bb85d02e617205782b814e0a605282900a004e025811404e013
def ridgeSupport644_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport644_code
def ridgeSupport644_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport644_code
def ridgeSupport644_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport644_code
def ridgeSupport644_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport644_code
def ridgeSupport644_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport644_code
def ridgeSupport644_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport644_code
def ridgeSupport644_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport644_code
def ridgeSupport644_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport644_code
def ridgeSupport644_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport644_code
def ridgeSupport644_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport644_code
def ridgeSupport644_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport644_code
def ridgeSupport644_rest_011 : Nat := PackedRawNatGrowth.drop 4498 ridgeSupport644_code
def ridgeSupport644_suffix_011 : List Nat := []
def ridgeSupport644_suffix_010 : List Nat := ridgeSupport644_010 ++ ridgeSupport644_suffix_011
def ridgeSupport644_suffix_009 : List Nat := ridgeSupport644_009 ++ ridgeSupport644_suffix_010
def ridgeSupport644_suffix_008 : List Nat := ridgeSupport644_008 ++ ridgeSupport644_suffix_009
def ridgeSupport644_suffix_007 : List Nat := ridgeSupport644_007 ++ ridgeSupport644_suffix_008
def ridgeSupport644_suffix_006 : List Nat := ridgeSupport644_006 ++ ridgeSupport644_suffix_007
def ridgeSupport644_suffix_005 : List Nat := ridgeSupport644_005 ++ ridgeSupport644_suffix_006
def ridgeSupport644_suffix_004 : List Nat := ridgeSupport644_004 ++ ridgeSupport644_suffix_005
def ridgeSupport644_suffix_003 : List Nat := ridgeSupport644_003 ++ ridgeSupport644_suffix_004
def ridgeSupport644_suffix_002 : List Nat := ridgeSupport644_002 ++ ridgeSupport644_suffix_003
def ridgeSupport644_suffix_001 : List Nat := ridgeSupport644_001 ++ ridgeSupport644_suffix_002
def ridgeSupport644_suffix_000 : List Nat := ridgeSupport644_000 ++ ridgeSupport644_suffix_001
theorem ridgeSupport644_source : candidateSupports 644 =
    (PackedRawNatGrowth.readList 13 346 ridgeSupport644_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase03
