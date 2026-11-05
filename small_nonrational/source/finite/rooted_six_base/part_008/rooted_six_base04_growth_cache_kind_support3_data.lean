module
prelude
public import RootedSixBase04GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase04
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def kindSupport3_000 : List Nat := [136,137,138,139,140,141,148,149,150,151,152,153,160,161,162,163,164,165,172,173,174,175,176,177,184,185,186,187,188,189,196,197]
def kindSupport3_001 : List Nat := [198,199,200,201,208,209,210,211,212,213,220,221,222,223,224,225,232,233,234,235,236,237,244,245,246,247,248,249,256,257,258,259]
def kindSupport3_002 : List Nat := [260,261,268,269,270,271,272,273,283,284,285,286,287,288,289,290,291,292,293,294,304,305,306,307,308,309,310,311,312,313,314,315]
def kindSupport3_003 : List Nat := [325,326,327,328,329,330,331,332,333,334,335,336,346,347,348,349,350,351,352,353,354,355,356,357,364,365,366,367,368,369,376,377]
def kindSupport3_004 : List Nat := [378,379,380,381,388,389,390,391,392,393,400,401,402,403,404,405,412,413,414,415,416,417,424,425,426,427,428,429,439,440,441,442]
def kindSupport3_005 : List Nat := [443,444,445,446,447,448,449,450,460,461,462,463,464,465,466,467,468,469,470,471,481,482,483,484,485,486,487,488,489,490,491,492]
def kindSupport3_006 : List Nat := [502,503,504,505,506,507,508,509,510,511,512,513,520,521,522,523,524,525,532,533,534,535,536,537,544,545,546,547,548,549,556,557]
def kindSupport3_007 : List Nat := [558,559,560,561,568,569,570,571,572,573,580,581,582,583,584,585,595,596,597,598,599,600,601,602,603,604,605,606,616,617,618,619]
def kindSupport3_008 : List Nat := [620,621,622,623,624,625,626,627,637,638,639,640,641,642,643,644,645,646,647,648,658,659,660,661,662,663,664,665,666,667,668,669]
def kindSupport3_009 : List Nat := [679,680,681,682,683,684,685,686,687,688,689,690,700,701,702,703,704,705,706,707,708,709,710,711,721,722,723,724,725,726,727,728]
def kindSupport3_010 : List Nat := [729,730,731,732,742,743,744,745,746,747,748,749,750,751,752,753,764,765,766,767,768,769,770,771,772,773,774,775,776,777,778,785]
def kindSupport3_011 : List Nat := [786,787,788,789,790,797,798,799,800,801,802,809,810,811,812,813,814,821,822,823,824,825,826,833,834,835,836,837,838,845,846,847]
def kindSupport3_012 : List Nat := [848,849,850,860,861,862,863,864,865,866,867,868,869,870,871,881,882,883,884,885,886,887,888,889,890,891,892,902,903,904,905,906]
def kindSupport3_013 : List Nat := [907,908,909,910,911,912,913,923,924,925,926,927,928,929,930,931,932,933,934,941,942,943,944,945,946,953,954,955,956,957,958,965]
def kindSupport3_014 : List Nat := [966,967,968,969,970,977,978,979,980,981,982,989,990,991,992,993,994,1001,1002,1003,1004,1005,1006,1016,1017,1018,1019,1020,1021,1022,1023,1024]
def kindSupport3_015 : List Nat := [1025,1026,1027,1037,1038,1039,1040,1041,1042,1043,1044,1045,1046,1047,1048,1058,1059,1060,1061,1062,1063,1064,1065,1066,1067,1068,1069,1079,1080,1081,1082,1083]
def kindSupport3_016 : List Nat := [1084,1085,1086,1087,1088,1089,1090,1100,1101,1102,1103,1104,1105,1106,1107,1108,1109,1110,1111,1121,1122,1123,1124,1125,1126,1127,1128,1129,1130,1131,1132,1142]
def kindSupport3_017 : List Nat := [1143,1144,1145,1146,1147,1148,1149,1150,1151,1152,1153,1163,1164,1165,1166,1167,1168,1169,1170,1171,1172,1173,1174,1185,1186,1187,1188,1189,1190,1191,1192,1193]
def kindSupport3_018 : List Nat := [1194,1195,1196,1197,1198,1199,1206,1207,1208,1209,1210,1211,1218,1219,1220,1221,1222,1223,1230,1231,1232,1233,1234,1235,1242,1243,1244,1245,1246,1247,1254,1255]
def kindSupport3_019 : List Nat := [1256,1257,1258,1259,1266,1267,1268,1269,1270,1271,1281,1282,1283,1284,1285,1286,1287,1288,1289,1290,1291,1292,1302,1303,1304,1305,1306,1307,1308,1309,1310,1311]
def kindSupport3_020 : List Nat := [1312,1313,1323,1324,1325,1326,1327,1328,1329,1330,1331,1332,1333,1334,1344,1345,1346,1347,1348,1349,1350,1351,1352,1353,1354,1355,1365,1366,1367,1368,1369,1370]
def kindSupport3_021 : List Nat := [1371,1372,1373,1374,1375,1376,1386,1387,1388,1389,1390,1391,1392,1393,1394,1395,1396,1397,1407,1408,1409,1410,1411,1412,1413,1414,1415,1416,1417,1418,1428,1429]
def kindSupport3_022 : List Nat := [1430,1431,1432,1433,1434,1435,1436,1437,1438,1439,1450,1451,1452,1453,1454,1455,1456,1457,1458,1459,1460,1461,1462,1463,1464,1471,1472,1473,1474,1475,1476,1483]
def kindSupport3_023 : List Nat := [1484,1485,1486,1487,1488,1495,1496,1497,1498,1499,1500,1507,1508,1509,1510,1511,1512,1519,1520,1521,1522,1523,1524,1531,1532,1533,1534,1535,1536,1546,1547,1548]
def kindSupport3_024 : List Nat := [1549,1550,1551,1552,1553,1554,1555,1556,1557,1567,1568,1569,1570,1571,1572,1573,1574,1575,1576,1577,1578,1588,1589,1590,1591,1592,1593,1594,1595,1596,1597,1598]
def kindSupport3_025 : List Nat := [1599,1609,1610,1611,1612,1613,1614,1615,1616,1617,1618,1619,1620,1630,1631,1632,1633,1634,1635,1636,1637,1638,1639,1640,1641,1651,1652,1653,1654,1655,1656,1657]
def kindSupport3_026 : List Nat := [1658,1659,1660,1661,1662,1672,1673,1674,1675,1676,1677,1678,1679,1680,1681,1682,1683,1693,1694,1695,1696,1697,1698,1699,1700,1701,1702,1703,1704,1715,1716,1717]
def kindSupport3_027 : List Nat := [1718,1719,1720,1721,1722,1723,1724,1725,1726,1727,1728,1729,1739,1740,1741,1742,1743,1744,1745,1746,1747,1748,1749,1750,1760,1761,1762,1763,1764,1765,1766,1767]
def kindSupport3_028 : List Nat := [1768,1769,1770,1771,1781,1782,1783,1784,1785,1786,1787,1788,1789,1790,1791,1792,1802,1803,1804,1805,1806,1807,1808,1809,1810,1811,1812,1813,1824,1825,1826,1827]
def kindSupport3_029 : List Nat := [1828,1829,1830,1831,1832,1833,1834,1835,1836,1837,1838,1849,1850,1851,1852,1853,1854,1855,1856,1857,1858,1859,1860,1861,1862,1863]
def kindSupport3_code : Nat := 0x74774674574474374274174073f73e73d73c73b73a73972e72d72c72b72a72972872772672572472372272172071571471371271171070f70e70d70c70b70a7006ff6fe6fd6fc6fb6fa6f96f86f76f66f56eb6ea6e96e86e76e66e56e46e36e26e16e06d66d56d46d36d26d16d06cf6ce6cd6cc6cb6c16c06bf6be6bd6bc6bb6ba6b96b86b76b66b56b46b36a86a76a66a56a46a36a26a16a069f69e69d69369269169068f68e68d68c68b68a68968867e67d67c67b67a67967867767667567467366966866766666566466366266166065f65e65465365265165064f64e64d64c64b64a64963f63e63d63c63b63a63963863763663563462a62962862762662562462362262162061f61561461361261161060f60e60d60c60b60a6005ff5fe5fd5fc5fb5f45f35f25f15f05ef5e85e75e65e55e45e35dc5db5da5d95d85d75d05cf5ce5cd5cc5cb5c45c35c25c15c05bf5b85b75b65b55b45b35b25b15b05af5ae5ad5ac5ab5aa59f59e59d59c59b59a59959859759659559458a58958858758658558458358258158057f57557457357257157056f56e56d56c56b56a56055f55e55d55c55b55a55955855755655554b54a54954854754654554454354254154053653553453353253153052f52e52d52c52b52152051f51e51d51c51b51a51951851751650c50b50a5095085075065055045035025014f74f64f54f44f34f24eb4ea4e94e84e74e64df4de4dd4dc4db4da4d34d24d14d04cf4ce4c74c64c54c44c34c24bb4ba4b94b84b74b64af4ae4ad4ac4ab4aa4a94a84a74a64a54a44a34a24a149649549449349249149048f48e48d48c48b48148047f47e47d47c47b47a47947847747646c46b46a46946846746646546446346246145745645545445345245145044f44e44d44c44244144043f43e43d43c43b43a43943843742d42c42b42a42942842742642542442342241841741641541441341241141040f40e40d4034024014003ff3fe3fd3fc3fb3fa3f93f83ee3ed3ec3eb3ea3e93e23e13e03df3de3dd3d63d53d43d33d23d13ca3c93c83c73c63c53be3bd3bc3bb3ba3b93b23b13b03af3ae3ad3a63a53a43a33a23a13a039f39e39d39c39b39139038f38e38d38c38b38a38938838738637c37b37a37937837737637537437337237136736636536436336236136035f35e35d35c35235135034f34e34d34634534434334234133a33933833733633532e32d32c32b32a32932232132031f31e31d31631531431331231130a3093083073063053043033023013002ff2fe2fd2fc2f12f02ef2ee2ed2ec2eb2ea2e92e82e72e62dc2db2da2d92d82d72d62d52d42d32d22d12c72c62c52c42c32c22c12c02bf2be2bd2bc2b22b12b02af2ae2ad2ac2ab2aa2a92a82a729d29c29b29a29929829729629529429329228828728628528428328228128027f27e27d27327227127026f26e26d26c26b26a26926825e25d25c25b25a25925825725625525425324924824724624524423d23c23b23a23923823123022f22e22d22c22522422322222122021921821721621521420d20c20b20a2092082012001ff1fe1fd1fc1fb1fa1f91f81f71f61ec1eb1ea1e91e81e71e61e51e41e31e21e11d71d61d51d41d31d21d11d01cf1ce1cd1cc1c21c11c01bf1be1bd1bc1bb1ba1b91b81b71ad1ac1ab1aa1a91a81a11a019f19e19d19c19519419319219119018918818718618518417d17c17b17a17917817117016f16e16d16c16516416316216116015f15e15d15c15b15a15014f14e14d14c14b14a14914814714614513b13a13913813713613513413313213113012612512412312212112011f11e11d11c11b11111010f10e10d10c1051041031021011000f90f80f70f60f50f40ed0ec0eb0ea0e90e80e10e00df0de0dd0dc0d50d40d30d20d10d00c90c80c70c60c50c40bd0bc0bb0ba0b90b80b10b00af0ae0ad0ac0a50a40a30a20a10a009909809709609509408d08c08b08a089088
def kindSupport3_rest_000 : Nat := PackedRawNatGrowth.drop 0 kindSupport3_code
def kindSupport3_rest_001 : Nat := PackedRawNatGrowth.drop 384 kindSupport3_code
def kindSupport3_rest_002 : Nat := PackedRawNatGrowth.drop 768 kindSupport3_code
def kindSupport3_rest_003 : Nat := PackedRawNatGrowth.drop 1152 kindSupport3_code
def kindSupport3_rest_004 : Nat := PackedRawNatGrowth.drop 1536 kindSupport3_code
def kindSupport3_rest_005 : Nat := PackedRawNatGrowth.drop 1920 kindSupport3_code
def kindSupport3_rest_006 : Nat := PackedRawNatGrowth.drop 2304 kindSupport3_code
def kindSupport3_rest_007 : Nat := PackedRawNatGrowth.drop 2688 kindSupport3_code
def kindSupport3_rest_008 : Nat := PackedRawNatGrowth.drop 3072 kindSupport3_code
def kindSupport3_rest_009 : Nat := PackedRawNatGrowth.drop 3456 kindSupport3_code
def kindSupport3_rest_010 : Nat := PackedRawNatGrowth.drop 3840 kindSupport3_code
def kindSupport3_rest_011 : Nat := PackedRawNatGrowth.drop 4224 kindSupport3_code
def kindSupport3_rest_012 : Nat := PackedRawNatGrowth.drop 4608 kindSupport3_code
def kindSupport3_rest_013 : Nat := PackedRawNatGrowth.drop 4992 kindSupport3_code
def kindSupport3_rest_014 : Nat := PackedRawNatGrowth.drop 5376 kindSupport3_code
def kindSupport3_rest_015 : Nat := PackedRawNatGrowth.drop 5760 kindSupport3_code
def kindSupport3_rest_016 : Nat := PackedRawNatGrowth.drop 6144 kindSupport3_code
def kindSupport3_rest_017 : Nat := PackedRawNatGrowth.drop 6528 kindSupport3_code
def kindSupport3_rest_018 : Nat := PackedRawNatGrowth.drop 6912 kindSupport3_code
def kindSupport3_rest_019 : Nat := PackedRawNatGrowth.drop 7296 kindSupport3_code
def kindSupport3_rest_020 : Nat := PackedRawNatGrowth.drop 7680 kindSupport3_code
def kindSupport3_rest_021 : Nat := PackedRawNatGrowth.drop 8064 kindSupport3_code
def kindSupport3_rest_022 : Nat := PackedRawNatGrowth.drop 8448 kindSupport3_code
def kindSupport3_rest_023 : Nat := PackedRawNatGrowth.drop 8832 kindSupport3_code
def kindSupport3_rest_024 : Nat := PackedRawNatGrowth.drop 9216 kindSupport3_code
def kindSupport3_rest_025 : Nat := PackedRawNatGrowth.drop 9600 kindSupport3_code
def kindSupport3_rest_026 : Nat := PackedRawNatGrowth.drop 9984 kindSupport3_code
def kindSupport3_rest_027 : Nat := PackedRawNatGrowth.drop 10368 kindSupport3_code
def kindSupport3_rest_028 : Nat := PackedRawNatGrowth.drop 10752 kindSupport3_code
def kindSupport3_rest_029 : Nat := PackedRawNatGrowth.drop 11136 kindSupport3_code
def kindSupport3_rest_030 : Nat := PackedRawNatGrowth.drop 11448 kindSupport3_code
def kindSupport3_suffix_030 : List Nat := []
def kindSupport3_suffix_029 : List Nat := kindSupport3_029 ++ kindSupport3_suffix_030
def kindSupport3_suffix_028 : List Nat := kindSupport3_028 ++ kindSupport3_suffix_029
def kindSupport3_suffix_027 : List Nat := kindSupport3_027 ++ kindSupport3_suffix_028
def kindSupport3_suffix_026 : List Nat := kindSupport3_026 ++ kindSupport3_suffix_027
def kindSupport3_suffix_025 : List Nat := kindSupport3_025 ++ kindSupport3_suffix_026
def kindSupport3_suffix_024 : List Nat := kindSupport3_024 ++ kindSupport3_suffix_025
def kindSupport3_suffix_023 : List Nat := kindSupport3_023 ++ kindSupport3_suffix_024
def kindSupport3_suffix_022 : List Nat := kindSupport3_022 ++ kindSupport3_suffix_023
def kindSupport3_suffix_021 : List Nat := kindSupport3_021 ++ kindSupport3_suffix_022
def kindSupport3_suffix_020 : List Nat := kindSupport3_020 ++ kindSupport3_suffix_021
def kindSupport3_suffix_019 : List Nat := kindSupport3_019 ++ kindSupport3_suffix_020
def kindSupport3_suffix_018 : List Nat := kindSupport3_018 ++ kindSupport3_suffix_019
def kindSupport3_suffix_017 : List Nat := kindSupport3_017 ++ kindSupport3_suffix_018
def kindSupport3_suffix_016 : List Nat := kindSupport3_016 ++ kindSupport3_suffix_017
def kindSupport3_suffix_015 : List Nat := kindSupport3_015 ++ kindSupport3_suffix_016
def kindSupport3_suffix_014 : List Nat := kindSupport3_014 ++ kindSupport3_suffix_015
def kindSupport3_suffix_013 : List Nat := kindSupport3_013 ++ kindSupport3_suffix_014
def kindSupport3_suffix_012 : List Nat := kindSupport3_012 ++ kindSupport3_suffix_013
def kindSupport3_suffix_011 : List Nat := kindSupport3_011 ++ kindSupport3_suffix_012
def kindSupport3_suffix_010 : List Nat := kindSupport3_010 ++ kindSupport3_suffix_011
def kindSupport3_suffix_009 : List Nat := kindSupport3_009 ++ kindSupport3_suffix_010
def kindSupport3_suffix_008 : List Nat := kindSupport3_008 ++ kindSupport3_suffix_009
def kindSupport3_suffix_007 : List Nat := kindSupport3_007 ++ kindSupport3_suffix_008
def kindSupport3_suffix_006 : List Nat := kindSupport3_006 ++ kindSupport3_suffix_007
def kindSupport3_suffix_005 : List Nat := kindSupport3_005 ++ kindSupport3_suffix_006
def kindSupport3_suffix_004 : List Nat := kindSupport3_004 ++ kindSupport3_suffix_005
def kindSupport3_suffix_003 : List Nat := kindSupport3_003 ++ kindSupport3_suffix_004
def kindSupport3_suffix_002 : List Nat := kindSupport3_002 ++ kindSupport3_suffix_003
def kindSupport3_suffix_001 : List Nat := kindSupport3_001 ++ kindSupport3_suffix_002
def kindSupport3_suffix_000 : List Nat := kindSupport3_000 ++ kindSupport3_suffix_001
theorem kindSupport3_source : kindSupports 3 =
    (PackedRawNatGrowth.readList 12 954 kindSupport3_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase04
