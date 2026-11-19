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
def ridgeSupport560_000 : List Nat := [78,98,117,119,120,1225,1226,1228,1233,1235,1249,1250,1252,1257,1259,1261,1262,1264,1269,1271,1490,1491,1493,1498,1500,1514,1515,1517,1522,1524,1526,1527]
def ridgeSupport560_001 : List Nat := [1529,1534,1536,1751,1752,1754,1755,1758,1759,1760,1762,1763,1765,1770,1771,1772,1773,1775,1776,1779,1780,1781,1783,1784,1786,1791,1792,1793,1794,1796,1797,1800]
def ridgeSupport560_002 : List Nat := [1801,1802,1804,1805,1807,1812,1813,6236,6237,6242,6243,6248,6249,6250,6251,6252,6253,6254,6255,6260,6261,6266,6267,6272,6273,6274,6275,6276,6277,6278,6279,6298]
def ridgeSupport560_003 : List Nat := [6299,6300,6301,6302,6303,6322,6323,6324,6325,6326,6327,6346,6347,6348,6349,6350,6351,6370,6371,6372,6373,6374,6375,6394,6395,6396,6397,6398,6399,6418,6419,6420]
def ridgeSupport560_004 : List Nat := [6421,6422,6423,6424,6426,6430,6432,6436,6438,6442,6443,6444,6445,6446,6447,6566,6567,6578,6579,6580,6582,6586,6588,6602,6603,6614,6615,6638,6639,6650,6651,6652]
def ridgeSupport560_005 : List Nat := [6654,6658,6660,6674,6675,6686,6687,6710,6711,6722,6723,6724,6726,6730,6732,6746,6747,6758,6759,6854,6855,6866,6867,6868,6870,6874,6876,6890,6891,6902,6903,6926]
def ridgeSupport560_006 : List Nat := [6927,6938,6939,6940,6942,6946,6948,6962,6963,6974,6975,6998,6999,7010,7011,7012,7014,7018,7020,7034,7035,7046,7047,7606,7607,7608,7609,7610,7611,8650,8651,8652]
def ridgeSupport560_007 : List Nat := [8653,8654,8655,8656,8658,8662,8664,8666,8667,8668,8670,8674,8676,8678,8679,8702,8703,8708,8709,8720,8721,8726,8727,8738,8739,8744,8745,8774,8775,8780,8781,8792]
cert_ridgeSupport_7 560 008 8793 8798 8799 8810 8811 8816 8817
cert_ridgeSupport_code_3 560
cert_ridgeSupport_rest_2 560 000 0
cert_ridgeSupport_rest_2 560 001 448
cert_ridgeSupport_rest_2 560 002 896
cert_ridgeSupport_rest_2 560 003 1344
cert_ridgeSupport_rest_2 560 004 1792
cert_ridgeSupport_rest_2 560 005 2240
cert_ridgeSupport_rest_2 560 006 2688
cert_ridgeSupport_rest_2 560 007 3136
cert_ridgeSupport_rest_2 560 008 3584
cert_ridgeSupport_rest_2 560 009 3682
cert_ridgeSupport_suffix_4 560 009
cert_ridgeSupport_suffix_3 560 008 009
cert_ridgeSupport_suffix_3 560 007 008
cert_ridgeSupport_suffix_3 560 006 007
cert_ridgeSupport_suffix_3 560 005 006
cert_ridgeSupport_suffix_3 560 004 005
cert_ridgeSupport_suffix_3 560 003 004
cert_ridgeSupport_suffix_3 560 002 003
cert_ridgeSupport_suffix_3 560 001 002
cert_ridgeSupport_suffix_3 560 000 001
cert_ridgeSupport_source_3 560 14 263
end Papers.RationalityTen.RootedCaches.RootedSixExtra00
