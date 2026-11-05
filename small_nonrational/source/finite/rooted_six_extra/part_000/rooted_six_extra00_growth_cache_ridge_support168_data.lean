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
def ridgeSupport168_000 : List Nat := [66,96,105,108,109,1045,1046,1048,1053,1055,1080,1083,1085,1088,1090,1092,1095,1097,1100,1102,1465,1468,1469,1472,1475,1502,1503,1506,1507,1512,1514,1515]
def ridgeSupport168_001 : List Nat := [1518,1519,1524,1621,1623,1624,1626,1627,1629,1631,1632,1634,1635,1638,1639,1642,1644,1645,1647,1648,1650,1652,1653,1655,1656,1659,1660,1685,1686,1688,1689,1690]
def ridgeSupport168_002 : List Nat := [1691,1693,1694,1696,1697,1699,1700,5704,5705,5710,5711,5712,5713,5714,5715,5718,5719,5724,5725,5728,5729,5734,5735,5736,5737,5738,5739,5742,5743,5748,5749,5758]
def ridgeSupport168_003 : List Nat := [5759,5760,5761,5762,5763,5782,5783,5784,5785,5786,5787,5806,5807,5808,5809,5810,5811,5830,5831,5832,5833,5834,5835,5854,5855,5856,5857,5858,5859,5878,5879,5880]
def ridgeSupport168_004 : List Nat := [5881,5882,5883,5899,5901,5902,5903,5904,5905,5906,5907,5909,5912,5915,5918,5964,5965,5976,5977,5981,5984,5987,5990,6000,6001,6012,6013,6036,6037,6048,6049,6053]
def ridgeSupport168_005 : List Nat := [6056,6059,6062,6072,6073,6084,6085,6178,6179,6190,6191,6199,6201,6205,6207,6214,6215,6226,6227,6768,6769,6786,6787,6804,6805,6809,6812,6815,6818,6822,6823,6840]
def ridgeSupport168_006 : List Nat := [6841,6858,6859,6876,6877,6881,6884,6887,6890,6894,6895,6982,6983,7000,7001,7018,7019,7027,7029,7033,7035,7036,7037,7534,7535,7536,7537,7538,7539,8518,8519,8520]
def ridgeSupport168_007 : List Nat := [8521,8522,8523,8539,8541,8542,8543,8544,8545,8551,8553,8554,8555,8556,8557,8562,8563,8568,8569,8580,8581,8586,8587,8614,8615,8620,8621,8753,8756,8766,8767,8771]
def ridgeSupport168_008 : List Nat := [8774,8784,8785,8809,8811,8818,8819]
def ridgeSupport168_code : Nat := 0x227389ca26b89a62518942246890e23f88fa23488c61ad86b21a7869a18b862a185861217985e217385ca16d85b216b85aa169859e161858215f857a15d856e14b852a14985221478519d7375c9d7175c1d6f75b9b7d6df1b7b6de5b756dcdb6b6da9b596d61b476d19aef6bb9aea6b9dae46b85add6b71acb6b29ab96ae1aa76a99aa26a7da9c6a65a956a51a836a09a7169c18536149847611983f60f583960dd82f60b982360897c55f117b95ee17ae5ead7a85e957a15e817955e5177d5df17715dc17665d8d7605d757595d6174d5d3171e5c6d7185c557135c497115c4170f5c3970d5c2d6fb5be96f95be16f75bd96e35b896e15b816df5b796cb5b296c95b216c75b196b35ac96b15ac16af5ab969b5a696995a616975a596835a096815a0167f59f967559d166f59b966b59a966959a16675999661598165d597165759596535949651594164f593964959206a41a8c6a11a8069e1a7469b1a686991a606961a5467c19ec67819dc67519d067219c066f19b466c19a866719986631988660197c65d196c65a196065719545f417bc5ee17ac5ea17a05e317885df17785c317005bd16f05b9113844c11244471110442110043d10ec438107c41d1060416105406d01b00690180042
def ridgeSupport168_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport168_code
def ridgeSupport168_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport168_code
def ridgeSupport168_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport168_code
def ridgeSupport168_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport168_code
def ridgeSupport168_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport168_code
def ridgeSupport168_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport168_code
def ridgeSupport168_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport168_code
def ridgeSupport168_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport168_code
def ridgeSupport168_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport168_code
def ridgeSupport168_rest_009 : Nat := PackedRawNatGrowth.drop 3682 ridgeSupport168_code
def ridgeSupport168_suffix_009 : List Nat := []
def ridgeSupport168_suffix_008 : List Nat := ridgeSupport168_008 ++ ridgeSupport168_suffix_009
def ridgeSupport168_suffix_007 : List Nat := ridgeSupport168_007 ++ ridgeSupport168_suffix_008
def ridgeSupport168_suffix_006 : List Nat := ridgeSupport168_006 ++ ridgeSupport168_suffix_007
def ridgeSupport168_suffix_005 : List Nat := ridgeSupport168_005 ++ ridgeSupport168_suffix_006
def ridgeSupport168_suffix_004 : List Nat := ridgeSupport168_004 ++ ridgeSupport168_suffix_005
def ridgeSupport168_suffix_003 : List Nat := ridgeSupport168_003 ++ ridgeSupport168_suffix_004
def ridgeSupport168_suffix_002 : List Nat := ridgeSupport168_002 ++ ridgeSupport168_suffix_003
def ridgeSupport168_suffix_001 : List Nat := ridgeSupport168_001 ++ ridgeSupport168_suffix_002
def ridgeSupport168_suffix_000 : List Nat := ridgeSupport168_000 ++ ridgeSupport168_suffix_001
theorem ridgeSupport168_source : candidateSupports 168 =
    (PackedRawNatGrowth.readList 14 263 ridgeSupport168_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
