module
prelude
public import RootedSixExtra05GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport704_000 : List Nat := [24,40,50,70,80,84,87,185,186,187,188,189,190,200,201,202,203,204,205,273,274,275,276,277,278,288,289,290,291,292,293,357]
def ridgeSupport704_001 : List Nat := [358,359,360,361,362,372,373,374,375,376,377,420,421,423,425,427,429,434,435,437,438,442,444,470,471,472,473,474,475,485,486,487]
def ridgeSupport704_002 : List Nat := [488,489,490,554,555,556,557,558,559,569,570,571,572,573,574,617,618,620,622,624,626,631,632,634,635,639,641,663,664,665,666,667]
def ridgeSupport704_003 : List Nat := [668,678,679,680,681,682,683,726,727,729,731,733,735,740,741,743,744,748,750,844,845,846,847,848,849,859,860,861,862,863,864,928]
def ridgeSupport704_004 : List Nat := [929,930,931,932,933,943,944,945,946,947,948,991,992,994,996,998,1000,1005,1006,1008,1009,1013,1015,1037,1038,1039,1040,1041,1042,1052,1053,1054]
def ridgeSupport704_005 : List Nat := [1055,1056,1057,1100,1101,1103,1105,1107,1109,1114,1115,1117,1118,1122,1124,1125,1126,1128,1130,1132,1134,1139,1140,1142,1143,1147,1149,1162,1163,1164,1165,1166]
def ridgeSupport704_006 : List Nat := [1167,1198,1199,1200,1201,1202,1203,1234,1235,1236,1237,1238,1239,1264,1265,1266,1267,1268,1269,1294,1295,1296,1297,1298,1299,1330,1331,1332,1333,1334,1335,1366]
def ridgeSupport704_007 : List Nat := [1367,1368,1369,1370,1371,1426,1427,1428,1429,1430,1431,1462,1463,1464,1465,1466,1467,1522,1523,1524,1525,1526,1527,1576,1577,1578,1579,1580,1581,1595,1596,1597]
def ridgeSupport704_008 : List Nat := [1598,1601,1602,1603,1604,1612,1614,1616,1617,1643,1644,1645,1646,1649,1650,1651,1652,1660,1662,1664,1665,1691,1692,1693,1694,1697,1698,1699,1700,1708,1710,1712]
def ridgeSupport704_009 : List Nat := [1713,1811,1812,1813,1814,1817,1818,1819,1820,1828,1830,1832,1833,1859,1860,1861,1862,1865,1866,1867,1868,1876,1878,1880,1881,1907,1908,1909,1910,1913,1914,1915]
def ridgeSupport704_010 : List Nat := [1916,1924,1926,1928,1929,1955,1956,1957,1958,1961,1962,1963,1964,1972,1974,1976,1977,2003,2004,2005,2006,2009,2010,2011,2012,2020,2022,2024,2025,2051,2052,2053]
def ridgeSupport704_011 : List Nat := [2054,2057,2058,2059,2060,2068,2070,2072,2073]
def ridgeSupport704_code : Nat := 0x81981881681480c80b80a8098068058048037e97e87e67e47dc7db7da7d97d67d57d47d37b97b87b67b47ac7ab7aa7a97a67a57a47a378978878678477c77b77a77977677577477375975875675474c74b74a74974674574474372972872672471c71b71a7197167157147136b16b06ae6ac6a46a36a26a169e69d69c69b68168067e67c67467367267166e66d66c66b65165064e64c64464364264163e63d63c63b62d62c62b62a6296285f75f65f55f45f35f25bb5ba5b95b85b75b659759659559459359255b55a55955855755653753653553453353251351251151050f50e4f54f44f34f24f14f04d74d64d54d44d34d24b34b24b14b04af4ae48f48e48d48c48b48a47d47b47747647447346e46c46a46846646546446245e45d45b45a45545345144f44d44c42142041f41e41d41c41241141040f40e40d3f73f53f13f03ee3ed3e83e63e43e23e03df3b43b33b23b13b03af3a53a43a33a23a13a036035f35e35d35c35b35135034f34e34d34c2ee2ec2e82e72e52e42df2dd2db2d92d72d62ab2aa2a92a82a72a629c29b29a29929829728127f27b27a27827727227026e26c26a26923e23d23c23b23a23922f22e22d22c22b22a1ea1e91e81e71e61e51db1da1d91d81d71d61bc1ba1b61b51b31b21ad1ab1a91a71a51a417917817717617517416a1691681671661651251241231221211201161151141131121110cd0cc0cb0ca0c90c80be0bd0bc0bb0ba0b9057054050046032028018
def ridgeSupport704_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport704_code
def ridgeSupport704_rest_001 : Nat := PackedRawNatGrowth.drop 384 ridgeSupport704_code
def ridgeSupport704_rest_002 : Nat := PackedRawNatGrowth.drop 768 ridgeSupport704_code
def ridgeSupport704_rest_003 : Nat := PackedRawNatGrowth.drop 1152 ridgeSupport704_code
def ridgeSupport704_rest_004 : Nat := PackedRawNatGrowth.drop 1536 ridgeSupport704_code
def ridgeSupport704_rest_005 : Nat := PackedRawNatGrowth.drop 1920 ridgeSupport704_code
def ridgeSupport704_rest_006 : Nat := PackedRawNatGrowth.drop 2304 ridgeSupport704_code
def ridgeSupport704_rest_007 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport704_code
def ridgeSupport704_rest_008 : Nat := PackedRawNatGrowth.drop 3072 ridgeSupport704_code
def ridgeSupport704_rest_009 : Nat := PackedRawNatGrowth.drop 3456 ridgeSupport704_code
def ridgeSupport704_rest_010 : Nat := PackedRawNatGrowth.drop 3840 ridgeSupport704_code
def ridgeSupport704_rest_011 : Nat := PackedRawNatGrowth.drop 4224 ridgeSupport704_code
def ridgeSupport704_rest_012 : Nat := PackedRawNatGrowth.drop 4332 ridgeSupport704_code
def ridgeSupport704_suffix_012 : List Nat := []
def ridgeSupport704_suffix_011 : List Nat := ridgeSupport704_011 ++ ridgeSupport704_suffix_012
def ridgeSupport704_suffix_010 : List Nat := ridgeSupport704_010 ++ ridgeSupport704_suffix_011
def ridgeSupport704_suffix_009 : List Nat := ridgeSupport704_009 ++ ridgeSupport704_suffix_010
def ridgeSupport704_suffix_008 : List Nat := ridgeSupport704_008 ++ ridgeSupport704_suffix_009
def ridgeSupport704_suffix_007 : List Nat := ridgeSupport704_007 ++ ridgeSupport704_suffix_008
def ridgeSupport704_suffix_006 : List Nat := ridgeSupport704_006 ++ ridgeSupport704_suffix_007
def ridgeSupport704_suffix_005 : List Nat := ridgeSupport704_005 ++ ridgeSupport704_suffix_006
def ridgeSupport704_suffix_004 : List Nat := ridgeSupport704_004 ++ ridgeSupport704_suffix_005
def ridgeSupport704_suffix_003 : List Nat := ridgeSupport704_003 ++ ridgeSupport704_suffix_004
def ridgeSupport704_suffix_002 : List Nat := ridgeSupport704_002 ++ ridgeSupport704_suffix_003
def ridgeSupport704_suffix_001 : List Nat := ridgeSupport704_001 ++ ridgeSupport704_suffix_002
def ridgeSupport704_suffix_000 : List Nat := ridgeSupport704_000 ++ ridgeSupport704_suffix_001
theorem ridgeSupport704_source : candidateSupports 704 =
    (PackedRawNatGrowth.readList 12 361 ridgeSupport704_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra05
