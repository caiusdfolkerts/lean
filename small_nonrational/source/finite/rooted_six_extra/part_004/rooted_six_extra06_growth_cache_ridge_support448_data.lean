module
prelude
public import RootedSixExtra06GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra06
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport448_000 : List Nat := [27,47,77,87,97,101,105,178,179,180,181,182,183,193,194,195,196,197,198,334,335,336,337,338,339,349,350,351,352,353,354,418]
def ridgeSupport448_001 : List Nat := [419,420,421,422,423,433,434,435,436,437,438,502,503,504,508,510,511,515,517,518,520,521,523,599,600,601,602,603,604,614,615,616]
def ridgeSupport448_002 : List Nat := [617,618,619,683,684,685,686,687,688,698,699,700,701,702,703,767,768,769,773,775,776,780,782,783,785,786,788,864,865,866,867,868]
def ridgeSupport448_003 : List Nat := [869,879,880,881,882,883,884,1020,1021,1022,1023,1024,1025,1035,1036,1037,1038,1039,1040,1104,1105,1106,1107,1108,1109,1119,1120,1121,1122,1123,1124,1188]
def ridgeSupport448_004 : List Nat := [1189,1190,1194,1196,1197,1201,1203,1204,1206,1207,1209,1213,1214,1215,1216,1217,1218,1228,1229,1230,1231,1232,1233,1297,1298,1299,1303,1305,1306,1310,1312,1313]
def ridgeSupport448_005 : List Nat := [1315,1316,1318,1322,1323,1324,1325,1326,1327,1337,1338,1339,1340,1341,1342,1406,1407,1408,1412,1414,1415,1419,1421,1422,1424,1425,1427,1431,1432,1433,1437,1439]
def ridgeSupport448_006 : List Nat := [1440,1444,1446,1447,1449,1450,1452,1456,1458,1460,1461,1462,1464,1466,1467,1468,1470,1472,1473,1504,1506,1508,1509,1510,1512,1514,1515,1516,1518,1520,1521,1552]
def ridgeSupport448_007 : List Nat := [1554,1556,1557,1558,1560,1562,1563,1564,1566,1568,1569,1672,1674,1676,1677,1678,1680,1682,1683,1684,1686,1688,1689,1720,1722,1724,1725,1726,1728,1730,1731,1732]
def ridgeSupport448_008 : List Nat := [1734,1736,1737,1840,1842,1844,1845,1846,1848,1850,1851,1852,1854,1856,1857,1888,1890,1892,1893,1894,1896,1898,1899,1900,1902,1904,1905,2008,2010,2012,2013,2014]
def ridgeSupport448_009 : List Nat := [2016,2018,2019,2020,2022,2024,2025,2056,2058,2060,2061,2062,2064,2066,2067,2068,2070,2072,2073,2176,2178,2180,2181,2182,2184,2186,2187,2188,2190,2192,2193]
def ridgeSupport448_code : Nat := 0x89189088e88c88b88a88888688588488288081981881681481381281080e80d80c80a8087e97e87e67e47e37e27e07de7dd7dc7da7d877177076e76c76b76a76876676576476276074174073e73c73b73a7387367357347327306c96c86c66c46c36c26c06be6bd6bc6ba6b869969869669469369269068e68d68c68a68862162061e61c61b61a6186166156146126105f15f05ee5ec5eb5ea5e85e65e55e45e25e05c15c05be5bc5bb5ba5b85b65b55b45b25b05ac5aa5a95a75a65a45a059f59d59959859759359159058e58d58b58758658458057f57e53e53d53c53b53a53952f52e52d52c52b52a52652452352152051e51a5195175135125114d14d04cf4ce4cd4cc4c24c14c04bf4be4bd4b94b74b64b44b34b14ad4ac4aa4a64a54a446446346246146045f45545445345245145041040f40e40d40c40b4014003ff3fe3fd3fc37437337237137036f36536436336236136031431231130f30e30c3083073053013002ff2bf2be2bd2bc2bb2ba2b02af2ae2ad2ac2ab26b26a26926826726625c25b25a25925825720b2092082062052031ff1fe1fc1f81f71f61b61b51b41b31b21b11a71a61a51a41a31a216216116015f15e15d15315215115014f14e0c60c50c40c30c20c10b70b60b50b40b30b206906506105704d02f01b
def ridgeSupport448_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport448_code
def ridgeSupport448_rest_001 : Nat := PackedRawNatGrowth.drop 384 ridgeSupport448_code
def ridgeSupport448_rest_002 : Nat := PackedRawNatGrowth.drop 768 ridgeSupport448_code
def ridgeSupport448_rest_003 : Nat := PackedRawNatGrowth.drop 1152 ridgeSupport448_code
def ridgeSupport448_rest_004 : Nat := PackedRawNatGrowth.drop 1536 ridgeSupport448_code
def ridgeSupport448_rest_005 : Nat := PackedRawNatGrowth.drop 1920 ridgeSupport448_code
def ridgeSupport448_rest_006 : Nat := PackedRawNatGrowth.drop 2304 ridgeSupport448_code
def ridgeSupport448_rest_007 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport448_code
def ridgeSupport448_rest_008 : Nat := PackedRawNatGrowth.drop 3072 ridgeSupport448_code
def ridgeSupport448_rest_009 : Nat := PackedRawNatGrowth.drop 3456 ridgeSupport448_code
def ridgeSupport448_rest_010 : Nat := PackedRawNatGrowth.drop 3828 ridgeSupport448_code
def ridgeSupport448_suffix_010 : List Nat := []
def ridgeSupport448_suffix_009 : List Nat := ridgeSupport448_009 ++ ridgeSupport448_suffix_010
def ridgeSupport448_suffix_008 : List Nat := ridgeSupport448_008 ++ ridgeSupport448_suffix_009
def ridgeSupport448_suffix_007 : List Nat := ridgeSupport448_007 ++ ridgeSupport448_suffix_008
def ridgeSupport448_suffix_006 : List Nat := ridgeSupport448_006 ++ ridgeSupport448_suffix_007
def ridgeSupport448_suffix_005 : List Nat := ridgeSupport448_005 ++ ridgeSupport448_suffix_006
def ridgeSupport448_suffix_004 : List Nat := ridgeSupport448_004 ++ ridgeSupport448_suffix_005
def ridgeSupport448_suffix_003 : List Nat := ridgeSupport448_003 ++ ridgeSupport448_suffix_004
def ridgeSupport448_suffix_002 : List Nat := ridgeSupport448_002 ++ ridgeSupport448_suffix_003
def ridgeSupport448_suffix_001 : List Nat := ridgeSupport448_001 ++ ridgeSupport448_suffix_002
def ridgeSupport448_suffix_000 : List Nat := ridgeSupport448_000 ++ ridgeSupport448_suffix_001
theorem ridgeSupport448_source : candidateSupports 448 =
    (PackedRawNatGrowth.readList 12 319 ridgeSupport448_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra06
