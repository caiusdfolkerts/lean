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
def ridgeSupport800_000 : List Nat := [90,110,120,127,128,1104,1105,1106,1107,1114,1115,1260,1261,1262,1263,1270,1271,1399,1400,1401,1404,1405,1410,1411,1416,1418,1420,1421,1422,1425,1426,1431]
def ridgeSupport800_001 : List Nat := [1432,1437,1439,1525,1526,1527,1528,1535,1536,1664,1665,1666,1669,1670,1675,1676,1681,1683,1685,1686,1687,1690,1691,1696,1697,1702,1704,1773,1774,1775,1778,1779]
def ridgeSupport800_002 : List Nat := [1784,1785,1790,1792,1794,1795,1796,1799,1800,1805,1806,1811,1813,1839,1840,1844,1845,1846,1847,1849,1850,1858,1860,1861,1863,5466,5468,5472,5474,5552,5553,5558]
def ridgeSupport800_003 : List Nat := [5559,5560,5561,5566,5567,5572,5574,5578,5580,5600,5601,5606,5607,5634,5636,5640,5642,5648,5649,5654,5655,5656,5657,5662,5663,5680,5681,5686,5687,5706,5708,5712]
def ridgeSupport800_004 : List Nat := [5714,5792,5793,5798,5799,5800,5801,5806,5807,5812,5814,5818,5820,5840,5841,5846,5847,5874,5876,5880,5882,5888,5889,5894,5895,5896,5897,5902,5903,5920,5921,5926]
def ridgeSupport800_005 : List Nat := [5927,6096,6098,6108,6110,6124,6125,6136,6137,6168,6170,6180,6182,6196,6197,6208,6209,6234,6236,6240,6242,6320,6321,6326,6327,6328,6329,6334,6335,6340,6342,6346]
def ridgeSupport800_006 : List Nat := [6348,6368,6369,6374,6375,6402,6404,6408,6410,6416,6417,6422,6423,6424,6425,6430,6431,6448,6449,6454,6455,6624,6626,6636,6638,6652,6653,6664,6665,6696,6698,6708]
def ridgeSupport800_007 : List Nat := [6710,6724,6725,6736,6737,6912,6914,6924,6926,6940,6941,6952,6953,6984,6986,6996,6998,7012,7013,7024,7025,7516,7517,7552,7553,7612,7613,8480,8481,8486,8487,8488]
def ridgeSupport800_008 : List Nat := [8489,8491,8493,8494,8495,8528,8529,8534,8535,8536,8537,8539,8541,8542,8543,8596,8597,8599,8601,8614,8615,8617,8619,8648,8649,8654,8655,8656,8657,8659,8661,8662]
def ridgeSupport800_009 : List Nat := [8663,8716,8717,8719,8721,8734,8735,8737,8739,8788,8789,8791,8793,8806,8807,8809,8811]
def ridgeSupport800_code : Nat := 0x226b89a6267899a259895e2558952223888621f887a211883e20d88321d7875a1d5874e1d187421cf873a1c987221ab86a61a7869a199865e195865215f857a15d856e1598562157855a151854212f84ba12d84ae12984a2127849a1218481dbd76f1d817601d5d7571b716dc1b656d91b566d51b4a6d21b296ca1b1d6c71b0e6c31b026c01a516941a456911a3668d1a2a68a1a0968219fd67f19ee67b19e2678193764d993164c191f647991964619176459911644190a642190464098e763998e163818cc63298c663118bf62f98b962e18b762d98b162c1862618185c6169841610183560d1826609181a60617f95fe17ed5fb17de5f717d25f417275c997215c8170f5c397095c217075c197015c016fa5be16f45bc96d75b596d15b416bc5ae96b65ad16af5ab96a95aa16a75a996a15a81652594164c592963758d963158c161f587961958616175859611584160a582160458095e757995e157815cc57295c657115bf56f95b956e15b756d95b156c1562558155c55687471d147441d0873a1ce47371cd87351cd07301cbc7151c4c70e1c347081c1c7041c0c7021c006fe1be46f81bcc6f21bbc6ee1bb46a81a986a11a8069b1a686971a586951a4c6911a3068b1a186851a086811a0060017fc5f817dc5f617d459f1674598165c592164458e163458c1628588160c58215f457c15e457815dc4f713d84ef13b84ed13b045b11684531148451114008001fc07801b805a
def ridgeSupport800_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport800_code
def ridgeSupport800_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport800_code
def ridgeSupport800_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport800_code
def ridgeSupport800_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport800_code
def ridgeSupport800_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport800_code
def ridgeSupport800_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport800_code
def ridgeSupport800_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport800_code
def ridgeSupport800_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport800_code
def ridgeSupport800_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport800_code
def ridgeSupport800_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport800_code
def ridgeSupport800_rest_010 : Nat := PackedRawNatGrowth.drop 4270 ridgeSupport800_code
def ridgeSupport800_suffix_010 : List Nat := []
def ridgeSupport800_suffix_009 : List Nat := ridgeSupport800_009 ++ ridgeSupport800_suffix_010
def ridgeSupport800_suffix_008 : List Nat := ridgeSupport800_008 ++ ridgeSupport800_suffix_009
def ridgeSupport800_suffix_007 : List Nat := ridgeSupport800_007 ++ ridgeSupport800_suffix_008
def ridgeSupport800_suffix_006 : List Nat := ridgeSupport800_006 ++ ridgeSupport800_suffix_007
def ridgeSupport800_suffix_005 : List Nat := ridgeSupport800_005 ++ ridgeSupport800_suffix_006
def ridgeSupport800_suffix_004 : List Nat := ridgeSupport800_004 ++ ridgeSupport800_suffix_005
def ridgeSupport800_suffix_003 : List Nat := ridgeSupport800_003 ++ ridgeSupport800_suffix_004
def ridgeSupport800_suffix_002 : List Nat := ridgeSupport800_002 ++ ridgeSupport800_suffix_003
def ridgeSupport800_suffix_001 : List Nat := ridgeSupport800_001 ++ ridgeSupport800_suffix_002
def ridgeSupport800_suffix_000 : List Nat := ridgeSupport800_000 ++ ridgeSupport800_suffix_001
theorem ridgeSupport800_source : candidateSupports 800 =
    (PackedRawNatGrowth.readList 14 305 ridgeSupport800_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
