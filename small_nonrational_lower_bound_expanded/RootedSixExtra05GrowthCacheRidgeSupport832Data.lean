module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public meta import CertificateNumbers
public import RootedSixExtra05GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport832_000 : List Nat := [25,41,51,71,81,85,87,206,207,208,209,210,211,221,222,223,224,225,226,294,295,296,297,298,299,309,310,311,312,313,314,378]
def ridgeSupport832_001 : List Nat := [379,380,381,382,383,393,394,395,396,397,398,420,422,423,424,427,428,433,434,440,441,443,444,491,492,493,494,495,496,506,507,508]
def ridgeSupport832_002 : List Nat := [509,510,511,575,576,577,578,579,580,590,591,592,593,594,595,617,619,620,621,624,625,630,631,637,638,640,641,684,685,686,687,688]
def ridgeSupport832_003 : List Nat := [689,699,700,701,702,703,704,726,728,729,730,733,734,739,740,746,747,749,750,865,866,867,868,869,870,880,881,882,883,884,885,949]
def ridgeSupport832_004 : List Nat := [950,951,952,953,954,964,965,966,967,968,969,991,993,994,995,998,999,1004,1005,1011,1012,1014,1015,1058,1059,1060,1061,1062,1063,1073,1074,1075]
def ridgeSupport832_005 : List Nat := [1076,1077,1078,1100,1102,1103,1104,1107,1108,1113,1114,1120,1121,1123,1124,1125,1127,1128,1129,1132,1133,1138,1139,1145,1146,1148,1149,1156,1157,1158,1159,1160]
def ridgeSupport832_006 : List Nat := [1161,1192,1193,1194,1195,1196,1197,1228,1229,1230,1231,1232,1233,1270,1271,1272,1273,1274,1275,1288,1289,1290,1291,1292,1293,1324,1325,1326,1327,1328,1329,1360]
def ridgeSupport832_007 : List Nat := [1361,1362,1363,1364,1365,1420,1421,1422,1423,1424,1425,1456,1457,1458,1459,1460,1461,1516,1517,1518,1519,1520,1521,1582,1583,1584,1585,1586,1587,1594,1595,1597]
def ridgeSupport832_008 : List Nat := [1599,1607,1608,1609,1610,1613,1614,1615,1616,1642,1643,1645,1647,1655,1656,1657,1658,1661,1662,1663,1664,1690,1691,1693,1695,1703,1704,1705,1706,1709,1710,1711]
def ridgeSupport832_009 : List Nat := [1712,1810,1811,1813,1815,1823,1824,1825,1826,1829,1830,1831,1832,1858,1859,1861,1863,1871,1872,1873,1874,1877,1878,1879,1880,1906,1907,1909,1911,1919,1920,1921]
def ridgeSupport832_010 : List Nat := [1922,1925,1926,1927,1928,1954,1955,1957,1959,1967,1968,1969,1970,1973,1974,1975,1976,2002,2003,2005,2007,2015,2016,2017,2018,2021,2022,2023,2024,2050,2051,2053]
def ridgeSupport832_011 : List Nat := [2055,2063,2064,2065,2066,2069,2070,2071,2072]
cert_ridgeSupport_code_3 832
cert_ridgeSupport_rest_2 832 000 0
cert_ridgeSupport_rest_2 832 001 384
cert_ridgeSupport_rest_2 832 002 768
cert_ridgeSupport_rest_2 832 003 1152
cert_ridgeSupport_rest_2 832 004 1536
cert_ridgeSupport_rest_2 832 005 1920
cert_ridgeSupport_rest_2 832 006 2304
cert_ridgeSupport_rest_2 832 007 2688
cert_ridgeSupport_rest_2 832 008 3072
cert_ridgeSupport_rest_2 832 009 3456
cert_ridgeSupport_rest_2 832 010 3840
cert_ridgeSupport_rest_2 832 011 4224
cert_ridgeSupport_rest_2 832 012 4332
cert_ridgeSupport_suffix_4 832 012
cert_ridgeSupport_suffix_3 832 011 012
cert_ridgeSupport_suffix_3 832 010 011
cert_ridgeSupport_suffix_3 832 009 010
cert_ridgeSupport_suffix_3 832 008 009
cert_ridgeSupport_suffix_3 832 007 008
cert_ridgeSupport_suffix_3 832 006 007
cert_ridgeSupport_suffix_3 832 005 006
cert_ridgeSupport_suffix_3 832 004 005
cert_ridgeSupport_suffix_3 832 003 004
cert_ridgeSupport_suffix_3 832 002 003
cert_ridgeSupport_suffix_3 832 001 002
cert_ridgeSupport_suffix_3 832 000 001
cert_ridgeSupport_source_3 832 12 361
end Papers.RationalityTen.RootedCaches.RootedSixExtra05
