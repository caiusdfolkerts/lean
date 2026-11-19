module
prelude
public meta import CertificateNumbers
public import RootedSevenTwoSix13GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport896_000 : List Nat := [40,41,42,43,44,45,55,56,57,58,59,60,64,65,66,67,68,69,79,80,81,82,83,84,85,86,87,88,89,90,100,101]
def ridgeSupport896_001 : List Nat := [102,103,104,105,109,110,111,112,113,114,124,125,126,127,128,129,130,131,132,133,134,135,145,146,147,148,149,150,151,152,153,154]
def ridgeSupport896_002 : List Nat := [155,156,166,167,168,169,170,171,208,209,210,211,212,213,223,224,225,226,227,228,265,266,267,268,269,270,280,281,282,283,284,285]
def ridgeSupport896_003 : List Nat := [286,287,288,289,290,291,301,302,303,304,305,306,343,344,345,346,347,348,358,359,360,361,362,363,364,365,366,367,368,369,379,380]
def ridgeSupport896_004 : List Nat := [381,382,383,384,385,386,387,388,389,390,400,401,402,403,404,405,406,407,408,409,410,411,412,413,414,415,416,417,418,419,420,421]
def ridgeSupport896_005 : List Nat := [422,423,424,425,426,427,428,429,430,431,432,433,434,435,436,437,438,439,440,441,478,479,480,481,482,483,484,485,486,487,488,489]
def ridgeSupport896_006 : List Nat := [490,491,492,493,494,495,496,497,498,499,500,501,502,503,504,505,506,507,508,509,510,511,512,513,550,551,552,553,554,555,556,557]
def ridgeSupport896_007 : List Nat := [558,559,560,561,562,563,564,565,566,567,568,569,570,571,572,573,574,575,576,577,578,579,580,581,582,583,584,585,622,623,624,625]
def ridgeSupport896_008 : List Nat := [626,627,628,629,630,631,632,633,634,635,636,637,638,639,640,641,642,643,644,645,646,647,648,649,650,651,652,653,654,655,656,657]
def ridgeSupport896_009 : List Nat := [694,695,696,697,698,699,700,701,702,703,704,705,706,707,708,709,710,711,784,785,786,787,788,789,790,791,792,793,794,795,796,797]
def ridgeSupport896_010 : List Nat := [798,799,800,801,874,875,876,877,878,879,880,881,882,883,884,885,886,887,888,889,890,891,964,965,966,967,968,969,970,971,972,973]
def ridgeSupport896_011 : List Nat := [974,975,976,977,978,979,980,981,982,983,984,985,986,987,988,989,990,991,992,993,994,995,996,997,998,999,1072,1073,1074,1075,1076,1077]
def ridgeSupport896_012 : List Nat := [1078,1079,1080,1081,1082,1083,1084,1085,1086,1087,1088,1089,1090,1091,1092,1093,1094,1095,1096,1097,1098,1099,1100,1101,1102,1103,1104,1105,1106,1107,1180,1181]
def ridgeSupport896_013 : List Nat := [1182,1183,1184,1185,1186,1187,1188,1189,1190,1191,1192,1193,1194,1195,1196,1197,1198,1199,1200,1201,1202,1203,1204,1205,1206,1207,1208,1209,1210,1211,1212,1213]
def ridgeSupport896_014 : List Nat := [1214,1215,1216,1217,1218,1219,1220,1221,1222,1223,1224,1225,1226,1227,1228,1229,1230,1231,1232,1233,1234,1235,1236,1237,1238,1239,1240,1241,1242,1243,1244,1245]
def ridgeSupport896_015 : List Nat := [1246,1247,1248,1249,1250,1251,1252,1253,1254,1255,1256,1257,1312,1313,1314,1315,1316,1317,1318,1319,1320,1321,1322,1323,1324,1325,1326,1327,1328,1329,1330,1331]
def ridgeSupport896_016 : List Nat := [1332,1333,1334,1335,1336,1337,1338,1339,1340,1341,1342,1343,1344,1345,1346,1347,1366,1367,1368,1369,1370,1371,1372,1373,1374,1375,1376,1377,1378,1379,1380,1381]
def ridgeSupport896_017 : List Nat := [1382,1383,1384,1385,1386,1387,1388,1389,1390,1391,1392,1393,1394,1395,1396,1397,1398,1399,1400,1401,1420,1421,1422,1423,1424,1425,1426,1427,1428,1429,1430,1431]
def ridgeSupport896_018 : List Nat := [1432,1433,1434,1435,1436,1437,1438,1439,1440,1441,1442,1443,1444,1445,1446,1447,1448,1449,1450,1451,1452,1453,1454,1455,1546,1547,1548,1549,1550,1551,1552,1553]
def ridgeSupport896_019 : List Nat := [1554,1555,1556,1557,1558,1559,1560,1561,1562,1563,1564,1565,1566,1567,1568,1569,1570,1571,1572,1573,1574,1575,1576,1577,1578,1579,1580,1581,1762,1763,1764,1765]
def ridgeSupport896_020 : List Nat := [1766,1767,1768,1769,1770,1771,1772,1773,1774,1775,1776,1777,1778,1779,1780,1781,1782,1783,1784,1785,1786,1787,1788,1789,1790,1791,1792,1793,1794,1795,1796,1797]
def ridgeSupport896_021 : List Nat := [1834,1835,1836,1837,1838,1839,1840,1841,1842,1843,1844,1845,1846,1847,1848,1849,1850,1851,1852,1853,1854,1855,1856,1857,1858,1859,1860,1861,1862,1863,1864,1865]
def ridgeSupport896_022 : List Nat := [1866,1867,1868,1869,1906,1907,1908,1909,1910,1911,1912,1913,1914,1915,1916,1917,1918,1919,1920,1921,1922,1923,1924,1925,1926,1927,1928,1929,1930,1931,1932,1933]
def ridgeSupport896_023 : List Nat := [1934,1935,1936,1937,1938,1939,1940,1941,1978,1979,1980,1981,1982,1983,2020,2021,2022,2023,2024,2025,2026,2027,2028,2029,2030,2031,2032,2033,2034,2035,2036,2037]
def ridgeSupport896_code : Nat := (certNat% 0)
def ridgeSupport896_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport896_code
def ridgeSupport896_rest_001 : Nat := PackedRawNatGrowth.drop 352 ridgeSupport896_code
def ridgeSupport896_rest_002 : Nat := PackedRawNatGrowth.drop 704 ridgeSupport896_code
def ridgeSupport896_rest_003 : Nat := PackedRawNatGrowth.drop 1056 ridgeSupport896_code
def ridgeSupport896_rest_004 : Nat := PackedRawNatGrowth.drop 1408 ridgeSupport896_code
def ridgeSupport896_rest_005 : Nat := PackedRawNatGrowth.drop 1760 ridgeSupport896_code
def ridgeSupport896_rest_006 : Nat := PackedRawNatGrowth.drop 2112 ridgeSupport896_code
def ridgeSupport896_rest_007 : Nat := PackedRawNatGrowth.drop 2464 ridgeSupport896_code
def ridgeSupport896_rest_008 : Nat := PackedRawNatGrowth.drop 2816 ridgeSupport896_code
def ridgeSupport896_rest_009 : Nat := PackedRawNatGrowth.drop 3168 ridgeSupport896_code
def ridgeSupport896_rest_010 : Nat := PackedRawNatGrowth.drop 3520 ridgeSupport896_code
def ridgeSupport896_rest_011 : Nat := PackedRawNatGrowth.drop 3872 ridgeSupport896_code
def ridgeSupport896_rest_012 : Nat := PackedRawNatGrowth.drop 4224 ridgeSupport896_code
def ridgeSupport896_rest_013 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport896_code
def ridgeSupport896_rest_014 : Nat := PackedRawNatGrowth.drop 4928 ridgeSupport896_code
def ridgeSupport896_rest_015 : Nat := PackedRawNatGrowth.drop 5280 ridgeSupport896_code
def ridgeSupport896_rest_016 : Nat := PackedRawNatGrowth.drop 5632 ridgeSupport896_code
def ridgeSupport896_rest_017 : Nat := PackedRawNatGrowth.drop 5984 ridgeSupport896_code
def ridgeSupport896_rest_018 : Nat := PackedRawNatGrowth.drop 6336 ridgeSupport896_code
def ridgeSupport896_rest_019 : Nat := PackedRawNatGrowth.drop 6688 ridgeSupport896_code
def ridgeSupport896_rest_020 : Nat := PackedRawNatGrowth.drop 7040 ridgeSupport896_code
def ridgeSupport896_rest_021 : Nat := PackedRawNatGrowth.drop 7392 ridgeSupport896_code
def ridgeSupport896_rest_022 : Nat := PackedRawNatGrowth.drop 7744 ridgeSupport896_code
def ridgeSupport896_rest_023 : Nat := PackedRawNatGrowth.drop 8096 ridgeSupport896_code
def ridgeSupport896_rest_024 : Nat := PackedRawNatGrowth.drop 8448 ridgeSupport896_code
def ridgeSupport896_suffix_024 : List Nat := []
def ridgeSupport896_suffix_023 : List Nat := ridgeSupport896_023 ++ ridgeSupport896_suffix_024
def ridgeSupport896_suffix_022 : List Nat := ridgeSupport896_022 ++ ridgeSupport896_suffix_023
def ridgeSupport896_suffix_021 : List Nat := ridgeSupport896_021 ++ ridgeSupport896_suffix_022
def ridgeSupport896_suffix_020 : List Nat := ridgeSupport896_020 ++ ridgeSupport896_suffix_021
def ridgeSupport896_suffix_019 : List Nat := ridgeSupport896_019 ++ ridgeSupport896_suffix_020
def ridgeSupport896_suffix_018 : List Nat := ridgeSupport896_018 ++ ridgeSupport896_suffix_019
def ridgeSupport896_suffix_017 : List Nat := ridgeSupport896_017 ++ ridgeSupport896_suffix_018
def ridgeSupport896_suffix_016 : List Nat := ridgeSupport896_016 ++ ridgeSupport896_suffix_017
def ridgeSupport896_suffix_015 : List Nat := ridgeSupport896_015 ++ ridgeSupport896_suffix_016
def ridgeSupport896_suffix_014 : List Nat := ridgeSupport896_014 ++ ridgeSupport896_suffix_015
def ridgeSupport896_suffix_013 : List Nat := ridgeSupport896_013 ++ ridgeSupport896_suffix_014
def ridgeSupport896_suffix_012 : List Nat := ridgeSupport896_012 ++ ridgeSupport896_suffix_013
def ridgeSupport896_suffix_011 : List Nat := ridgeSupport896_011 ++ ridgeSupport896_suffix_012
def ridgeSupport896_suffix_010 : List Nat := ridgeSupport896_010 ++ ridgeSupport896_suffix_011
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
theorem ridgeSupport896_source : candidateRows 896 =
    (PackedRawNatGrowth.readList 11 768 ridgeSupport896_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
