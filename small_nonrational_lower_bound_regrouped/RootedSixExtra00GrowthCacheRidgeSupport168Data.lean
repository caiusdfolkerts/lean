module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public meta import CertificateNumbers
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
cert_ridgeSupport_7 168 008 8774 8784 8785 8809 8811 8818 8819
cert_ridgeSupport_code_3 168
cert_ridgeSupport_rest_2 168 000 0
cert_ridgeSupport_rest_2 168 001 448
cert_ridgeSupport_rest_2 168 002 896
cert_ridgeSupport_rest_2 168 003 1344
cert_ridgeSupport_rest_2 168 004 1792
cert_ridgeSupport_rest_2 168 005 2240
cert_ridgeSupport_rest_2 168 006 2688
cert_ridgeSupport_rest_2 168 007 3136
cert_ridgeSupport_rest_2 168 008 3584
cert_ridgeSupport_rest_2 168 009 3682
cert_ridgeSupport_suffix_4 168 009
cert_ridgeSupport_suffix_3 168 008 009
cert_ridgeSupport_suffix_3 168 007 008
cert_ridgeSupport_suffix_3 168 006 007
cert_ridgeSupport_suffix_3 168 005 006
cert_ridgeSupport_suffix_3 168 004 005
cert_ridgeSupport_suffix_3 168 003 004
cert_ridgeSupport_suffix_3 168 002 003
cert_ridgeSupport_suffix_3 168 001 002
cert_ridgeSupport_suffix_3 168 000 001
cert_ridgeSupport_source_3 168 14 263
end Papers.RationalityTen.RootedCaches.RootedSixExtra00
