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
def ridgeSupport112_000 : List Nat := [75,95,115,116,117,1200,1203,1205,1208,1210,1212,1215,1217,1220,1222,1224,1227,1229,1232,1234,1465,1468,1470,1473,1475,1477,1480,1482,1485,1487,1489,1492]
def ridgeSupport112_001 : List Nat := [1494,1497,1499,1731,1732,1734,1735,1736,1737,1739,1740,1742,1743,1745,1746,1752,1753,1755,1756,1757,1758,1760,1761,1763,1764,1766,1767,1773,1774,1776,1777,1778]
def ridgeSupport112_002 : List Nat := [1779,1781,1782,1784,1785,1787,1788,6232,6233,6234,6235,6236,6237,6238,6239,6244,6245,6250,6251,6256,6257,6258,6259,6260,6261,6262,6263,6268,6269,6274,6275,6280]
def ridgeSupport112_003 : List Nat := [6281,6282,6283,6284,6285,6304,6305,6306,6307,6308,6309,6328,6329,6330,6331,6332,6333,6352,6353,6354,6355,6356,6357,6376,6377,6378,6379,6380,6381,6400,6401,6402]
def ridgeSupport112_004 : List Nat := [6403,6404,6405,6424,6425,6426,6427,6428,6429,6433,6435,6439,6441,6445,6447,6490,6491,6502,6503,6511,6513,6517,6519,6526,6527,6538,6539,6562,6563,6574,6575,6583]
def ridgeSupport112_005 : List Nat := [6585,6589,6591,6598,6599,6610,6611,6634,6635,6646,6647,6655,6657,6661,6663,6670,6671,6682,6683,6778,6779,6790,6791,6799,6801,6805,6807,6814,6815,6826,6827,6850]
def ridgeSupport112_006 : List Nat := [6851,6862,6863,6871,6873,6877,6879,6886,6887,6898,6899,6922,6923,6934,6935,6943,6945,6949,6951,6958,6959,6970,6971,7588,7589,7590,7591,7592,7593,8632,8633,8634]
def ridgeSupport112_007 : List Nat := [8635,8636,8637,8656,8657,8658,8659,8660,8661,8668,8669,8670,8671,8672,8673,8680,8681,8686,8687,8698,8699,8704,8705,8716,8717,8722,8723,8752,8753,8758,8759,8770]
cert_ridgeSupport_7 112 008 8771 8776 8777 8788 8789 8794 8795
cert_ridgeSupport_code_3 112
cert_ridgeSupport_rest_2 112 000 0
cert_ridgeSupport_rest_2 112 001 448
cert_ridgeSupport_rest_2 112 002 896
cert_ridgeSupport_rest_2 112 003 1344
cert_ridgeSupport_rest_2 112 004 1792
cert_ridgeSupport_rest_2 112 005 2240
cert_ridgeSupport_rest_2 112 006 2688
cert_ridgeSupport_rest_2 112 007 3136
cert_ridgeSupport_rest_2 112 008 3584
cert_ridgeSupport_rest_2 112 009 3682
cert_ridgeSupport_suffix_4 112 009
cert_ridgeSupport_suffix_3 112 008 009
cert_ridgeSupport_suffix_3 112 007 008
cert_ridgeSupport_suffix_3 112 006 007
cert_ridgeSupport_suffix_3 112 005 006
cert_ridgeSupport_suffix_3 112 004 005
cert_ridgeSupport_suffix_3 112 003 004
cert_ridgeSupport_suffix_3 112 002 003
cert_ridgeSupport_suffix_3 112 001 002
cert_ridgeSupport_suffix_3 112 000 001
cert_ridgeSupport_source_3 112 14 263
end Papers.RationalityTen.RootedCaches.RootedSixExtra00
