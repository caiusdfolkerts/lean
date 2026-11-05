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
def ridgeSupport896_000 : List Nat := [30,50,80,90,100,104,105,241,242,243,244,245,246,256,257,258,259,260,261,397,398,399,400,401,402,412,413,414,415,416,417,481]
def ridgeSupport896_001 : List Nat := [482,483,484,485,486,496,497,498,499,500,501,503,504,505,506,507,508,518,519,521,522,524,525,662,663,664,665,666,667,677,678,679]
def ridgeSupport896_002 : List Nat := [680,681,682,746,747,748,749,750,751,761,762,763,764,765,766,768,769,770,771,772,773,783,784,786,787,789,790,927,928,929,930,931]
def ridgeSupport896_003 : List Nat := [932,942,943,944,945,946,947,1083,1084,1085,1086,1087,1088,1098,1099,1100,1101,1102,1103,1167,1168,1169,1170,1171,1172,1182,1183,1184,1185,1186,1187,1189]
def ridgeSupport896_004 : List Nat := [1190,1191,1192,1193,1194,1204,1205,1207,1208,1210,1211,1276,1277,1278,1279,1280,1281,1291,1292,1293,1294,1295,1296,1298,1299,1300,1301,1302,1303,1313,1314,1316]
def ridgeSupport896_005 : List Nat := [1317,1319,1320,1385,1386,1387,1388,1389,1390,1400,1401,1402,1403,1404,1405,1407,1408,1409,1410,1411,1412,1422,1423,1425,1426,1428,1429,1432,1433,1434,1435,1436]
def ridgeSupport896_006 : List Nat := [1437,1447,1448,1450,1451,1453,1454,1462,1463,1465,1467,1468,1469,1471,1473,1474,1475,1477,1479,1510,1511,1513,1515,1516,1517,1519,1521,1522,1523,1525,1527,1558]
def ridgeSupport896_007 : List Nat := [1559,1561,1563,1564,1565,1567,1569,1570,1571,1573,1575,1678,1679,1681,1683,1684,1685,1687,1689,1690,1691,1693,1695,1726,1727,1729,1731,1732,1733,1735,1737,1738]
def ridgeSupport896_008 : List Nat := [1739,1741,1743,1846,1847,1849,1851,1852,1853,1855,1857,1858,1859,1861,1863,1894,1895,1897,1899,1900,1901,1903,1905,1906,1907,1909,1911,2014,2015,2017,2019,2020]
def ridgeSupport896_009 : List Nat := [2021,2023,2025,2026,2027,2029,2031,2062,2063,2065,2067,2068,2069,2071,2073,2074,2075,2077,2079,2182,2183,2185,2187,2188,2189,2191,2193,2194,2195,2197,2199]
def ridgeSupport896_code : Nat := 0x89789589389289188f88d88c88b88988788681f81d81b81a81981781581481381180f80e7ef7ed7eb7ea7e97e77e57e47e37e17df7de77777577377277176f76d76c76b76976776674774574374274173f73d73c73b7397377366cf6cd6cb6ca6c96c76c56c46c36c16bf6be69f69d69b69a69969769569469369168f68e62762562362262161f61d61c61b6196176165f75f55f35f25f15ef5ed5ec5eb5e95e75e65c75c55c35c25c15bf5bd5bc5bb5b95b75b65ae5ad5ab5aa5a85a759d59c59b59a59959859559459259158f58e58458358258158057f57d57c57b57a57957856e56d56c56b56a56952852752552452252151751651551451351251050f50e50d50c50b5015004ff4fe4fd4fc4bb4ba4b84b74b54b44aa4a94a84a74a64a54a34a24a14a049f49e49449349249149048f44f44e44d44c44b44a44043f43e43d43c43b3b33b23b13b03af3ae3a43a33a23a13a039f31631531331231030f3053043033023013002fe2fd2fc2fb2fa2f92ef2ee2ed2ec2eb2ea2aa2a92a82a72a62a529b29a29929829729620d20c20a2092072061fc1fb1fa1f91f81f71f51f41f31f21f11f01e61e51e41e31e21e11a11a019f19e19d19c19219119018f18e18d1051041031021011000f60f50f40f30f20f106906806405a05003201e
def ridgeSupport896_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport896_code
def ridgeSupport896_rest_001 : Nat := PackedRawNatGrowth.drop 384 ridgeSupport896_code
def ridgeSupport896_rest_002 : Nat := PackedRawNatGrowth.drop 768 ridgeSupport896_code
def ridgeSupport896_rest_003 : Nat := PackedRawNatGrowth.drop 1152 ridgeSupport896_code
def ridgeSupport896_rest_004 : Nat := PackedRawNatGrowth.drop 1536 ridgeSupport896_code
def ridgeSupport896_rest_005 : Nat := PackedRawNatGrowth.drop 1920 ridgeSupport896_code
def ridgeSupport896_rest_006 : Nat := PackedRawNatGrowth.drop 2304 ridgeSupport896_code
def ridgeSupport896_rest_007 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport896_code
def ridgeSupport896_rest_008 : Nat := PackedRawNatGrowth.drop 3072 ridgeSupport896_code
def ridgeSupport896_rest_009 : Nat := PackedRawNatGrowth.drop 3456 ridgeSupport896_code
def ridgeSupport896_rest_010 : Nat := PackedRawNatGrowth.drop 3828 ridgeSupport896_code
def ridgeSupport896_suffix_010 : List Nat := []
def ridgeSupport896_suffix_009 : List Nat := ridgeSupport896_009 ++ ridgeSupport896_suffix_010
def ridgeSupport896_suffix_008 : List Nat := ridgeSupport896_008 ++ ridgeSupport896_suffix_009
def ridgeSupport896_suffix_007 : List Nat := ridgeSupport896_007 ++ ridgeSupport896_suffix_008
def ridgeSupport896_suffix_006 : List Nat := ridgeSupport896_006 ++ ridgeSupport896_suffix_007
def ridgeSupport896_suffix_005 : List Nat := ridgeSupport896_005 ++ ridgeSupport896_suffix_006
def ridgeSupport896_suffix_004 : List Nat := ridgeSupport896_004 ++ ridgeSupport896_suffix_005
def ridgeSupport896_suffix_003 : List Nat := ridgeSupport896_003 ++ ridgeSupport896_suffix_004
def ridgeSupport896_suffix_002 : List Nat := ridgeSupport896_002 ++ ridgeSupport896_suffix_003
def ridgeSupport896_suffix_001 : List Nat := ridgeSupport896_001 ++ ridgeSupport896_suffix_002
def ridgeSupport896_suffix_000 : List Nat := ridgeSupport896_000 ++ ridgeSupport896_suffix_001
theorem ridgeSupport896_source : candidateSupports 896 =
    (PackedRawNatGrowth.readList 12 319 ridgeSupport896_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra06
