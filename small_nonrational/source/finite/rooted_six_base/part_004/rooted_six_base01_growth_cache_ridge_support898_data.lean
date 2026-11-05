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
def ridgeSupport898_000 : List Nat := [332,333,334,756,757,758,844,845,846,928,929,930,950,951,952,1626,1627,1628,1629,1630,1631,1722,1723,1724,1725,1726,1727,1818,1819,1820,1821,1822]
def ridgeSupport898_001 : List Nat := [1823,2178,2179,2180,2181,2182,2183,2226,2227,2228,2229,2230,2231,2370,2371,2372,2373,2374,2375,2742,2743,2744,2745,2746,2747,2772,2773,2774,2775,2776,2777,3138]
def ridgeSupport898_002 : List Nat := [3139,3140,3141,3142,3143,3186,3187,3188,3189,3190,3191,3330,3331,3332,3333,3334,3335,3702,3703,3704,3705,3706,3707,3732,3733,3734,3735,3736,3737,4530,4531,4532]
def ridgeSupport898_003 : List Nat := [4533,4534,4535,4578,4579,4580,4581,4582,4583,4722,4723,4724,4725,4726,4727,5370,5371,5372,5373,5374,5375,5382,5383,5384,5385,5386,5387,7176,7177,7182,7183,7188]
def ridgeSupport898_004 : List Nat := [7189,7203,7205,7209,7211,7215,7217,7224,7225,7230,7231,7236,7237,7323,7325,7329,7331,7335,7337,7371,7373,7377,7379,7383,7385,7659,7661,7665,7667,7671,7673,7680]
def ridgeSupport898_005 : List Nat := [7681,7686,7687,7692,7693,7728,7729,7734,7735,7740,7741,7827,7829,7833,7835,7839,7841,7842,7843,7844,7845,7846,7847,8142,8143,8144,8145,8146,8147,8172,8173,8174]
def ridgeSupport898_006 : List Nat := [8175,8176,8177,8427,8429,8433,8435,8439,8441,8448,8449,8454,8455,8460,8461,8496,8497,8502,8503,8508,8509,8595,8597,8601,8603,8607,8609,8610,8611,8612,8613,8614]
def ridgeSupport898_007 : List Nat := [8615,8910,8911,8912,8913,8914,8915,8940,8941,8942,8943,8944,8945,9483,9485,9489,9491,9495,9497,9504,9505,9510,9511,9516,9517,9552,9553,9558,9559,9564,9565,9651]
def ridgeSupport898_008 : List Nat := [9653,9657,9659,9663,9665,9666,9667,9668,9669,9670,9671,10218,10219,10220,10221,10222,10223,10230,10231,10232,10233,10234,10235,11653,11655,11657,11715,11717,11721,11723,11727,11729]
def ridgeSupport898_009 : List Nat := [11905,11907,11909,12003,12005,12009,12011,12015,12017,12228,12229,12230,12231,12232,12233,12385,12387,12389,12483,12485,12489,12491,12495,12497,12708,12709,12710,12711,12712,12713,13081,13083]
def ridgeSupport898_010 : List Nat := [13085,13179,13181,13185,13187,13191,13193,13548,13549,13550,13551,13552,13553,14688,14689,14694,14695,14700,14701,14762,14764,14768,14770,14774,14776,14858,14860,14864,14866,14870,14872,14978]
def ridgeSupport898_011 : List Nat := [14980,14984,14986,14990,14992]
def ridgeSupport898_code : Nat := 0x3a90ea3ba8aea23a84ea0ba18e85ba12e843a0ce82b9b8e6db9b2e6c39ace6ab96de5b3967e59b961e5834f1d3c34efd3bb4edd3b3389ce1f383ce0737dcdef31dcc6f319c6a71a8c69f1a6c6971a4c3470cfc32f0c9c3170c3c197063c186fc9bf22fc7bf1afc5bf12ef1bbbeeebbba6ee5bb8ee85ba0ee81b746dcfb72edc9b716dc3b626d87b6167fb9fea7f99fe27f79fda7ef9fba7ed9fb27eb9faa5c7971a5c597125c3970a5c196fe5bb96e65b596ce55d9572557955a551954252d94b2527949a5219482519945e513944650d942e2f18bc22ef8bba2ed8bb22d38b4a2d18b422cf8b3a1a7869a1a586921a3868a1a1867e19b8666195864e13d84f213784da13184c210d8432107841a10184020f983de0f383c60ed83adff17fc1fef7fb9fed7fb1fd37f49fd17f41fcf7f39ea77a99ea57a91ea37a89ea17a7de9b7a65e957a4de3d78f1e3778d9e3178c1e0d7831e077819e017801df977dddf377c5ded77adcd9735dcd37345ccd732dca9729dca37285c9d726dc457111c3f70f9c3970e1c3170bdc2b70a5c25708dc157051c0f7039c09702150b5429509542150754194ff53f94fd53f14fb53e927749d927549d127349c91e747991e547911e347891b746d91b546d11b346c8e993a60e973a58e953a50e7b39e8e7939e0e7739d8d073418d053410d033408c7731d8c7531d0c7331c8c473118c453110c433108ad92b60ad72b58ad52b50abb2ae8ab92ae0ab72ad89472518945251094325088b722d88b522d08b322c888722188852210883220871f1c7871d1c7071b1c686bf1af86bd1af06bb1ae865f197865d197065b19683b80edc3b60e883a10e8034e0d3434c0bd82f50bd014e053414c
def ridgeSupport898_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport898_code
def ridgeSupport898_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport898_code
def ridgeSupport898_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport898_code
def ridgeSupport898_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport898_code
def ridgeSupport898_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport898_code
def ridgeSupport898_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport898_code
def ridgeSupport898_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport898_code
def ridgeSupport898_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport898_code
def ridgeSupport898_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport898_code
def ridgeSupport898_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport898_code
def ridgeSupport898_rest_010 : Nat := PackedRawNatGrowth.drop 4480 ridgeSupport898_code
def ridgeSupport898_rest_011 : Nat := PackedRawNatGrowth.drop 4928 ridgeSupport898_code
def ridgeSupport898_rest_012 : Nat := PackedRawNatGrowth.drop 4998 ridgeSupport898_code
def ridgeSupport898_suffix_012 : List Nat := []
def ridgeSupport898_suffix_011 : List Nat := ridgeSupport898_011 ++ ridgeSupport898_suffix_012
def ridgeSupport898_suffix_010 : List Nat := ridgeSupport898_010 ++ ridgeSupport898_suffix_011
def ridgeSupport898_suffix_009 : List Nat := ridgeSupport898_009 ++ ridgeSupport898_suffix_010
def ridgeSupport898_suffix_008 : List Nat := ridgeSupport898_008 ++ ridgeSupport898_suffix_009
def ridgeSupport898_suffix_007 : List Nat := ridgeSupport898_007 ++ ridgeSupport898_suffix_008
def ridgeSupport898_suffix_006 : List Nat := ridgeSupport898_006 ++ ridgeSupport898_suffix_007
def ridgeSupport898_suffix_005 : List Nat := ridgeSupport898_005 ++ ridgeSupport898_suffix_006
def ridgeSupport898_suffix_004 : List Nat := ridgeSupport898_004 ++ ridgeSupport898_suffix_005
def ridgeSupport898_suffix_003 : List Nat := ridgeSupport898_003 ++ ridgeSupport898_suffix_004
def ridgeSupport898_suffix_002 : List Nat := ridgeSupport898_002 ++ ridgeSupport898_suffix_003
def ridgeSupport898_suffix_001 : List Nat := ridgeSupport898_001 ++ ridgeSupport898_suffix_002
def ridgeSupport898_suffix_000 : List Nat := ridgeSupport898_000 ++ ridgeSupport898_suffix_001
theorem ridgeSupport898_source : candidateRows 898 =
    (PackedRawNatGrowth.readList 14 357 ridgeSupport898_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase01
