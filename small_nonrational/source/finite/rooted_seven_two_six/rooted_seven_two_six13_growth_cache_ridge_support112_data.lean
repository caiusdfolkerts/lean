module
prelude
public import RootedSevenTwoSix13GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport112_000 : List Nat := [0,307,308,309,310,311,312,313,314,315,316,317,318,319,320,321,322,323,324,325,326,327,328,329,330,331,332,333,334,335,336,337]
def ridgeSupport112_001 : List Nat := [338,339,340,341,342,622,623,624,625,626,627,628,629,630,631,632,633,634,635,636,637,638,639,640,641,642,643,644,645,646,647,648]
def ridgeSupport112_002 : List Nat := [649,650,651,652,653,654,655,656,657,658,659,660,661,662,663,664,665,666,667,668,669,670,671,672,673,674,675,676,677,678,679,680]
def ridgeSupport112_003 : List Nat := [681,682,683,684,685,686,687,688,689,690,691,692,693,1090,1091,1092,1093,1094,1095,1096,1097,1098,1099,1100,1101,1102,1103,1104,1105,1106,1107,1108]
def ridgeSupport112_004 : List Nat := [1109,1110,1111,1112,1113,1114,1115,1116,1117,1118,1119,1120,1121,1122,1123,1124,1125,1126,1127,1128,1129,1130,1131,1132,1133,1134,1135,1136,1137,1138,1139,1140]
def ridgeSupport112_005 : List Nat := [1141,1142,1143,1144,1145,1146,1147,1148,1149,1150,1151,1152,1153,1154,1155,1156,1157,1158,1159,1160,1161,1162,1163,1164,1165,1166,1167,1168,1169,1170,1171,1172]
def ridgeSupport112_006 : List Nat := [1173,1174,1175,1176,1177,1178,1179,1180,1181,1182,1183,1184,1185,1186,1187,1188,1189,1190,1191,1192,1193,1194,1195,1196,1197,1216,1217,1218,1219,1220,1221,1420]
def ridgeSupport112_007 : List Nat := [1421,1422,1423,1424,1425,1426,1427,1428,1429,1430,1431,1432,1433,1434,1435,1436,1437,1438,1439,1440,1441,1442,1443,1444,1445,1446,1447,1448,1449,1450,1451,1452]
def ridgeSupport112_008 : List Nat := [1453,1454,1455,1456,1457,1458,1459,1460,1461,1462,1463,1464,1465,1466,1467,1468,1469,1470,1471,1472,1473,1528,1529,1530,1531,1532,1533,1534,1535,1536,1537,1538]
def ridgeSupport112_009 : List Nat := [1539,1540,1541,1542,1543,1544,1545,1906,1907,1908,1909,1910,1911,1912,1913,1914,1915,1916,1917,1918,1919,1920,1921,1922,1923,1924,1925,1926,1927,1928,1929,1930]
def ridgeSupport112_010 : List Nat := [1931,1932,1933,1934,1935,1936,1937,1938,1939,1940,1941,1942,1943,1944,1945,1946,1947,1948,1949,1950,1951,1952,1953,1954,1955,1956,1957,1958,1959,1960,1961,1962]
def ridgeSupport112_011 : List Nat := [1963,1964,1965,1966,1967,1968,1969,1970,1971,1972,1973,1974,1975,1976,1977,2032,2033,2034,2035,2036,2037]
def ridgeSupport112_code : Nat := 0x7f5fe9fcff97f1fe1ee7dc7b7f6ded7da7b3f65ec7d87aff5deb7d67abf55ea7d47a7f4de97d27a3f45e87d079ff3de77ce79bf35e67cc797f2de57ca793f25e47c878ff1de37c678bf15e27c4787f0de17c2783f05e07c077fefddf7be77bef5de7bc777eeddd7ba773ee582704607c0d81702603c05807005ffbfd7f6fe5fbbf57e6fc5c1b816fedf5bdb796eedd5b9b716dedb5b5b696ced95b1b616bed75adb596aed55a9b5169ed35a5b4968ed15a1b4167ecf59db3966ecd599b3165ecb595b2964ec9591b2163ec758db19316624c3985306604ad9592ae554a995129e534a594928e514a194127e4f49d93926e4d49993125e4b49592924e4949192123e4748d91922e4548991121e4348590920e414819011fe3f47d8f91ee3d4798f11de3b4758e91ce394718e11be3746d8d91ae354698d119e334658c918e314618c117e2f45d8b916e2d4598b115e2b4558a914e294518a113e2744d89912e2544989111e2344588910e212b5568acd592b1560abd572ad558aad552a9550a9d532a5548a8d512a1540a7d4f29d538a6d4d299530a5d4b295528a4d49291520a3d4728d518a2d45289510a1d43285508a0d412815009fd3f27d4f89ed3d2794f09dd3b2754e89cd392714e09bd371562aa550a99522a2540a794e29a530a594a292520a394628a510a19422825009f93e27a4f09d93a2724e09b93626a4d099800
def ridgeSupport112_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport112_code
def ridgeSupport112_rest_001 : Nat := PackedRawNatGrowth.drop 352 ridgeSupport112_code
def ridgeSupport112_rest_002 : Nat := PackedRawNatGrowth.drop 704 ridgeSupport112_code
def ridgeSupport112_rest_003 : Nat := PackedRawNatGrowth.drop 1056 ridgeSupport112_code
def ridgeSupport112_rest_004 : Nat := PackedRawNatGrowth.drop 1408 ridgeSupport112_code
def ridgeSupport112_rest_005 : Nat := PackedRawNatGrowth.drop 1760 ridgeSupport112_code
def ridgeSupport112_rest_006 : Nat := PackedRawNatGrowth.drop 2112 ridgeSupport112_code
def ridgeSupport112_rest_007 : Nat := PackedRawNatGrowth.drop 2464 ridgeSupport112_code
def ridgeSupport112_rest_008 : Nat := PackedRawNatGrowth.drop 2816 ridgeSupport112_code
def ridgeSupport112_rest_009 : Nat := PackedRawNatGrowth.drop 3168 ridgeSupport112_code
def ridgeSupport112_rest_010 : Nat := PackedRawNatGrowth.drop 3520 ridgeSupport112_code
def ridgeSupport112_rest_011 : Nat := PackedRawNatGrowth.drop 3872 ridgeSupport112_code
def ridgeSupport112_rest_012 : Nat := PackedRawNatGrowth.drop 4103 ridgeSupport112_code
def ridgeSupport112_suffix_012 : List Nat := []
def ridgeSupport112_suffix_011 : List Nat := ridgeSupport112_011 ++ ridgeSupport112_suffix_012
def ridgeSupport112_suffix_010 : List Nat := ridgeSupport112_010 ++ ridgeSupport112_suffix_011
def ridgeSupport112_suffix_009 : List Nat := ridgeSupport112_009 ++ ridgeSupport112_suffix_010
def ridgeSupport112_suffix_008 : List Nat := ridgeSupport112_008 ++ ridgeSupport112_suffix_009
def ridgeSupport112_suffix_007 : List Nat := ridgeSupport112_007 ++ ridgeSupport112_suffix_008
def ridgeSupport112_suffix_006 : List Nat := ridgeSupport112_006 ++ ridgeSupport112_suffix_007
def ridgeSupport112_suffix_005 : List Nat := ridgeSupport112_005 ++ ridgeSupport112_suffix_006
def ridgeSupport112_suffix_004 : List Nat := ridgeSupport112_004 ++ ridgeSupport112_suffix_005
def ridgeSupport112_suffix_003 : List Nat := ridgeSupport112_003 ++ ridgeSupport112_suffix_004
def ridgeSupport112_suffix_002 : List Nat := ridgeSupport112_002 ++ ridgeSupport112_suffix_003
def ridgeSupport112_suffix_001 : List Nat := ridgeSupport112_001 ++ ridgeSupport112_suffix_002
def ridgeSupport112_suffix_000 : List Nat := ridgeSupport112_000 ++ ridgeSupport112_suffix_001
theorem ridgeSupport112_source : candidateRows 112 =
    (PackedRawNatGrowth.readList 11 373 ridgeSupport112_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
