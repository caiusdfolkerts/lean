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
def ridgeSupport193_000 : List Nat := [9,15,21,27,28,104,105,106,107,108,109,176,177,178,179,180,181,248,249,250,253,254,255,257,262,264,269,270,271,274,275,276]
def ridgeSupport193_001 : List Nat := [278,283,285,336,337,338,341,342,343,345,350,352,357,358,359,362,363,364,366,371,373,420,421,422,425,426,427,429,434,436,441,442]
def ridgeSupport193_002 : List Nat := [443,446,447,448,450,455,457,504,505,507,508,509,510,512,513,515,516,518,519,1425,1427,1431,1433,1436,1437,1442,1443,1484,1485,1490,1491,1511]
def ridgeSupport193_003 : List Nat := [1513,1517,1519,1524,1525,1530,1531,1532,1533,1538,1539,1545,1547,1551,1553,1580,1581,1586,1587,1604,1605,1610,1611,1665,1667,1671,1673,1676,1677,1682,1683,1724]
def ridgeSupport193_004 : List Nat := [1725,1730,1731,1751,1753,1757,1759,1764,1765,1770,1771,1772,1773,1778,1779,1785,1787,1791,1793,1820,1821,1826,1827,1844,1845,1850,1851,2121,2123,2133,2135,2166]
def ridgeSupport193_005 : List Nat := [2167,2178,2179,2193,2195,2205,2207,2238,2239,2250,2251,2433,2435,2439,2441,2444,2445,2450,2451,2492,2493,2498,2499,2519,2521,2525,2527,2532,2533,2538,2539,2540]
def ridgeSupport193_006 : List Nat := [2541,2546,2547,2553,2555,2559,2561,2588,2589,2594,2595,2612,2613,2618,2619,2889,2891,2901,2903,2934,2935,2946,2947,2961,2963,2973,2975,3006,3007,3018,3019,3650]
def ridgeSupport193_007 : List Nat := [3651,3654,3655,5147,5149,5151,5153,5156,5157,5162,5163,5183,5185,5189,5191,5196,5197,5202,5203,5204,5205,5210,5211,5217,5219,5223,5225,5244,5245,5250,5251,5252]
def ridgeSupport193_008 : List Nat := [5253,5255,5256,5279,5281,5283,5285,5288,5289,5294,5295,5315,5317,5321,5323,5328,5329,5334,5335,5336,5337,5342,5343,5349,5351,5355,5357,5376,5377,5382,5383,5384]
def ridgeSupport193_009 : List Nat := [5385,5387,5388,5541,5543,5550,5551,5553,5555,5562,5563,5564,5566,5570,5572,5595,5597,5604,5605,5607,5609,5616,5617,5618,5620,5624,5626,5759,5761,5763,5765,5768]
def ridgeSupport193_010 : List Nat := [5769,5774,5775,5795,5797,5801,5803,5808,5809,5814,5815,5816,5817,5822,5823,5829,5831,5835,5837,5856,5857,5862,5863,5864,5865,5867,5868,6021,6023,6030,6031,6033]
def ridgeSupport193_011 : List Nat := [6035,6042,6043,6044,6046,6050,6052,6075,6077,6084,6085,6087,6089,6096,6097,6098,6100,6104,6106,6490,6491,7366,7368,7370,7372,7378,7380,7382,7384,7400,7402,7406]
def ridgeSupport193_012 : List Nat := [7408,7426,7428,7430,7432,7448,7450,7454,7456,7604,7605,7640,7641,7736,7737]
def ridgeSupport193_code : Nat := 0x78e7c71dd9eec76d7b69d20e8f746ba31d08e837413a05cf0e7773ab9d1cd8e6b73539a5ccce65732398d95bcad5f6afb17d4be95f46fa17c9be3df16f897bdbddde92f4579ebce5e6ef35793bc8de3ef1d787bc2dbb2dd76e9b745b9edcd6e1b705b36d976c7b62dafed7d6b9b5c5aded6d6b1b585aaed536a5b51da3ed1d689b445a16d07681b3fd7eabf15f4af957c6be15e9af3d796bc95ddaedd712b855beade56eeb755b3ad8d6beb5d5a7ad2d432a17509a84541ea0d501a8053b69d74e7a72d37e9bd4d9a6c535e9ad4d1a68532e9934c5a61d2be95d4a9a5452969474a1a4fd22290f485a42520e90547da3e51a68cf463a30d16e8b5455a2a514e8a544da26511e88b441a1fd0ae855425a12508683f41da0db91dc8ce437212f2d794bbf5df2e7d73ab935c8ae0d704b775bb2d5d6aab4b5a4a8ed474a3551a288d444a1d50e28053fe9fb4fca7cd3e49ed4f627ad3d49e54f2277d3ba9d94eba70d3849bd4de264d32498d4c6262530e9834c0a32d1948bf45f227d13a893448a20d10487743b215d0aa84b4249cece7473539a1c8ce4471d38e1c04dfe6fb37c9bccde46ed3761bacdd46e53721b7cdba6d936b9b0cd846bd35e1a4cd2468d3461a24d0e683340992cc9464532218ccc6462d3161844c1e60b304980cc045fd2fe17ecbf45f52fa17bcbda5e92f3974cba45cd2e6168cb4459d2ce1664b2e5932c8881c40c20410188044001fe0fe87f03f61f90fc072438e1c20e006fc37c1bb0dd06e43681b20d686ac3541a90d306943481750b985b82d816b0b5059c2cc1650b005782b21570ab05542a41510a8047423611608a044c22410f087043421010608083fc1fc0fd07d03e41f00b505a02cc1640b105801b40d806b03501a40d001c00d805401e009
def ridgeSupport193_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport193_code
def ridgeSupport193_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport193_code
def ridgeSupport193_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport193_code
def ridgeSupport193_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport193_code
def ridgeSupport193_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport193_code
def ridgeSupport193_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport193_code
def ridgeSupport193_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport193_code
def ridgeSupport193_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport193_code
def ridgeSupport193_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport193_code
def ridgeSupport193_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport193_code
def ridgeSupport193_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport193_code
def ridgeSupport193_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport193_code
def ridgeSupport193_rest_012 : Nat := PackedRawNatGrowth.drop 4992 ridgeSupport193_code
def ridgeSupport193_rest_013 : Nat := PackedRawNatGrowth.drop 5187 ridgeSupport193_code
def ridgeSupport193_suffix_013 : List Nat := []
def ridgeSupport193_suffix_012 : List Nat := ridgeSupport193_012 ++ ridgeSupport193_suffix_013
def ridgeSupport193_suffix_011 : List Nat := ridgeSupport193_011 ++ ridgeSupport193_suffix_012
def ridgeSupport193_suffix_010 : List Nat := ridgeSupport193_010 ++ ridgeSupport193_suffix_011
def ridgeSupport193_suffix_009 : List Nat := ridgeSupport193_009 ++ ridgeSupport193_suffix_010
def ridgeSupport193_suffix_008 : List Nat := ridgeSupport193_008 ++ ridgeSupport193_suffix_009
def ridgeSupport193_suffix_007 : List Nat := ridgeSupport193_007 ++ ridgeSupport193_suffix_008
def ridgeSupport193_suffix_006 : List Nat := ridgeSupport193_006 ++ ridgeSupport193_suffix_007
def ridgeSupport193_suffix_005 : List Nat := ridgeSupport193_005 ++ ridgeSupport193_suffix_006
def ridgeSupport193_suffix_004 : List Nat := ridgeSupport193_004 ++ ridgeSupport193_suffix_005
def ridgeSupport193_suffix_003 : List Nat := ridgeSupport193_003 ++ ridgeSupport193_suffix_004
def ridgeSupport193_suffix_002 : List Nat := ridgeSupport193_002 ++ ridgeSupport193_suffix_003
def ridgeSupport193_suffix_001 : List Nat := ridgeSupport193_001 ++ ridgeSupport193_suffix_002
def ridgeSupport193_suffix_000 : List Nat := ridgeSupport193_000 ++ ridgeSupport193_suffix_001
theorem ridgeSupport193_source : candidateSupports 193 =
    (PackedRawNatGrowth.readList 13 399 ridgeSupport193_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
