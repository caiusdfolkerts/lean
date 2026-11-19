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
def ridgeSupport104_000 : List Nat := [65,95,105,106,107,1044,1047,1049,1052,1054,1056,1059,1061,1064,1066,1068,1071,1073,1076,1078,1466,1467,1470,1471,1476,1478,1479,1482,1483,1488,1490,1491]
def ridgeSupport104_001 : List Nat := [1494,1495,1500,1622,1623,1625,1626,1627,1628,1630,1631,1633,1634,1636,1637,1643,1644,1646,1647,1648,1649,1651,1652,1654,1655,1657,1658,1664,1665,1667,1668,1669]
def ridgeSupport104_002 : List Nat := [1670,1672,1673,1675,1676,1678,1679,5704,5705,5706,5707,5708,5709,5710,5711,5716,5717,5722,5723,5728,5729,5730,5731,5732,5733,5734,5735,5740,5741,5746,5747,5752]
def ridgeSupport104_003 : List Nat := [5753,5754,5755,5756,5757,5776,5777,5778,5779,5780,5781,5800,5801,5802,5803,5804,5805,5824,5825,5826,5827,5828,5829,5848,5849,5850,5851,5852,5853,5872,5873,5874]
def ridgeSupport104_004 : List Nat := [5875,5876,5877,5896,5897,5898,5899,5900,5901,5905,5907,5911,5913,5917,5919,5962,5963,5974,5975,5983,5985,5989,5991,5998,5999,6010,6011,6034,6035,6046,6047,6055]
def ridgeSupport104_005 : List Nat := [6057,6061,6063,6070,6071,6082,6083,6106,6107,6118,6119,6127,6129,6133,6135,6142,6143,6154,6155,6766,6767,6784,6785,6802,6803,6811,6813,6817,6819,6820,6821,6838]
def ridgeSupport104_006 : List Nat := [6839,6856,6857,6874,6875,6883,6885,6889,6891,6892,6893,6910,6911,6928,6929,6946,6947,6955,6957,6961,6963,6964,6965,7528,7529,7530,7531,7532,7533,8512,8513,8514]
def ridgeSupport104_007 : List Nat := [8515,8516,8517,8536,8537,8538,8539,8540,8541,8548,8549,8550,8551,8552,8553,8560,8561,8566,8567,8578,8579,8584,8585,8596,8597,8602,8603,8755,8757,8764,8765,8773]
cert_ridgeSupport_7 104 008 8775 8782 8783 8791 8793 8800 8801
cert_ridgeSupport_code_3 104
cert_ridgeSupport_rest_2 104 000 0
cert_ridgeSupport_rest_2 104 001 448
cert_ridgeSupport_rest_2 104 002 896
cert_ridgeSupport_rest_2 104 003 1344
cert_ridgeSupport_rest_2 104 004 1792
cert_ridgeSupport_rest_2 104 005 2240
cert_ridgeSupport_rest_2 104 006 2688
cert_ridgeSupport_rest_2 104 007 3136
cert_ridgeSupport_rest_2 104 008 3584
cert_ridgeSupport_rest_2 104 009 3682
cert_ridgeSupport_suffix_4 104 009
cert_ridgeSupport_suffix_3 104 008 009
cert_ridgeSupport_suffix_3 104 007 008
cert_ridgeSupport_suffix_3 104 006 007
cert_ridgeSupport_suffix_3 104 005 006
cert_ridgeSupport_suffix_3 104 004 005
cert_ridgeSupport_suffix_3 104 003 004
cert_ridgeSupport_suffix_3 104 002 003
cert_ridgeSupport_suffix_3 104 001 002
cert_ridgeSupport_suffix_3 104 000 001
cert_ridgeSupport_source_3 104 14 263
end Papers.RationalityTen.RootedCaches.RootedSixExtra00
