module
prelude
public import RootedSixExtra00GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport224_000 : List Nat := [85,105,115,125,126,1044,1045,1046,1047,1054,1055,1200,1201,1202,1203,1210,1211,1356,1357,1361,1363,1364,1368,1370,1371,1373,1377,1378,1382,1384,1385,1389]
def ridgeSupport224_001 : List Nat := [1391,1392,1394,1465,1466,1467,1468,1475,1476,1621,1622,1626,1628,1629,1633,1635,1636,1638,1642,1643,1647,1649,1650,1654,1656,1657,1659,1730,1731,1735,1737,1738]
def ridgeSupport224_002 : List Nat := [1742,1744,1745,1747,1751,1752,1756,1758,1759,1763,1765,1766,1768,1841,1842,1844,1845,1846,1847,1849,1850,1852,1853,1855,1856,5477,5479,5483,5485,5536,5537,5542]
def ridgeSupport224_003 : List Nat := [5543,5563,5565,5569,5571,5576,5577,5582,5583,5584,5585,5590,5591,5632,5633,5638,5639,5645,5647,5651,5653,5672,5673,5678,5679,5696,5697,5702,5703,5717,5719,5723]
def ridgeSupport224_004 : List Nat := [5725,5776,5777,5782,5783,5803,5805,5809,5811,5816,5817,5822,5823,5824,5825,5830,5831,5872,5873,5878,5879,5885,5887,5891,5893,5912,5913,5918,5919,5936,5937,5942]
def ridgeSupport224_005 : List Nat := [5943,5951,5953,5963,5965,5984,5985,5996,5997,6023,6025,6035,6037,6056,6057,6068,6069,6245,6247,6251,6253,6304,6305,6310,6311,6331,6333,6337,6339,6344,6345,6350]
def ridgeSupport224_006 : List Nat := [6351,6352,6353,6358,6359,6400,6401,6406,6407,6413,6415,6419,6421,6440,6441,6446,6447,6464,6465,6470,6471,6479,6481,6491,6493,6512,6513,6524,6525,6551,6553,6563]
def ridgeSupport224_007 : List Nat := [6565,6584,6585,6596,6597,6767,6769,6779,6781,6800,6801,6812,6813,6839,6841,6851,6853,6872,6873,6884,6885,7526,7527,7562,7563,7622,7623,8464,8465,8470,8471,8488]
def ridgeSupport224_008 : List Nat := [8489,8494,8495,8498,8499,8512,8513,8518,8519,8536,8537,8542,8543,8546,8547,8560,8562,8564,8565,8578,8580,8582,8583,8632,8633,8638,8639,8656,8657,8662,8663,8666]
def ridgeSupport224_009 : List Nat := [8667,8680,8682,8684,8685,8698,8700,8702,8703,8752,8754,8756,8757,8770,8772,8774,8775]
def ridgeSupport224_code : Nat := 0x2247891a244890a23588d223288c21ff87fa1fc87ea1ed87b21ea87a21db876a1d7875a1d187421bf86fa1b986e2187861a184860a17585d217285c2163858a15f857a1598562147851a141850213384ca12f84ba12984a2117845a1118441dc77719d8b7629d677599ae56b91ad96b61ac56b0dab96adda9d6a71a916a41a7d69eda7169bd9c567119b966e19a5668d999665d97d65f197165c195d656d951653d9476519941650192f64b992964a1915644d90f6435907641990164018d763598d163418cf63398c963218c363058bd62ed8a762998a1628186d61ad86761957b55ed17a95ea17955e4d7895e1d76d5db17615d8174d5d2d7415cfd7375cd97315cc171f5c797195c617055c0d6ff5bf56f75bd96f15bc16c75b196c15b016bf5af96b95ae16b35ac56ad5aad6975a596915a4165d596d65759556475919641590162f58b962958a1615584d60f5835607581960158015d757595d157415cf57395c957215c357055bd56ed5a756995a1568156d55ad56755947401cfc73d1cf073a1ce47371cd87351cd07321cc46e81b986e51b8c6df1b786dc1b606d71b4c6d11b406ce1b286c91b1c6c31b0867b19e467819d867219c466f19ac66a1998664198c661197465c196865619545c4170c5bc16ec5ba16e457215c056f15b456915a05661588561157455b15685581550553154454d15304bb12e84b312c84b112c041f10784171058415105007e01f407301a4055
def ridgeSupport224_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport224_code
def ridgeSupport224_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport224_code
def ridgeSupport224_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport224_code
def ridgeSupport224_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport224_code
def ridgeSupport224_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport224_code
def ridgeSupport224_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport224_code
def ridgeSupport224_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport224_code
def ridgeSupport224_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport224_code
def ridgeSupport224_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport224_code
def ridgeSupport224_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport224_code
def ridgeSupport224_rest_010 : Nat := PackedRawNatGrowth.drop 4270 ridgeSupport224_code
def ridgeSupport224_suffix_010 : List Nat := []
def ridgeSupport224_suffix_009 : List Nat := ridgeSupport224_009 ++ ridgeSupport224_suffix_010
def ridgeSupport224_suffix_008 : List Nat := ridgeSupport224_008 ++ ridgeSupport224_suffix_009
def ridgeSupport224_suffix_007 : List Nat := ridgeSupport224_007 ++ ridgeSupport224_suffix_008
def ridgeSupport224_suffix_006 : List Nat := ridgeSupport224_006 ++ ridgeSupport224_suffix_007
def ridgeSupport224_suffix_005 : List Nat := ridgeSupport224_005 ++ ridgeSupport224_suffix_006
def ridgeSupport224_suffix_004 : List Nat := ridgeSupport224_004 ++ ridgeSupport224_suffix_005
def ridgeSupport224_suffix_003 : List Nat := ridgeSupport224_003 ++ ridgeSupport224_suffix_004
def ridgeSupport224_suffix_002 : List Nat := ridgeSupport224_002 ++ ridgeSupport224_suffix_003
def ridgeSupport224_suffix_001 : List Nat := ridgeSupport224_001 ++ ridgeSupport224_suffix_002
def ridgeSupport224_suffix_000 : List Nat := ridgeSupport224_000 ++ ridgeSupport224_suffix_001
theorem ridgeSupport224_source : candidateSupports 224 =
    (PackedRawNatGrowth.readList 14 305 ridgeSupport224_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
