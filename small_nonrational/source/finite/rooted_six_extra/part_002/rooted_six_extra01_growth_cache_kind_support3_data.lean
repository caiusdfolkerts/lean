module
prelude
public import RootedSixExtra01GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def kindSupport3_000 : List Nat := [122,123,124,125,126,127,134,135,136,137,138,139,146,147,148,149,150,151,158,159,160,161,162,163,170,171,172,173,174,175,182,183]
def kindSupport3_001 : List Nat := [184,185,186,187,194,195,196,197,198,199,206,207,208,209,210,211,218,219,220,221,222,223,230,231,232,233,234,235,242,243,244,245]
def kindSupport3_002 : List Nat := [246,247,254,255,256,257,258,259,269,270,271,272,273,274,275,276,277,278,279,280,290,291,292,293,294,295,296,297,298,299,300,301]
def kindSupport3_003 : List Nat := [311,312,313,314,315,316,317,318,319,320,321,322,332,333,334,335,336,337,338,339,340,341,342,343,350,351,352,353,354,355,362,363]
def kindSupport3_004 : List Nat := [364,365,366,367,374,375,376,377,378,379,386,387,388,389,390,391,398,399,400,401,402,403,410,411,412,413,414,415,425,426,427,428]
def kindSupport3_005 : List Nat := [429,430,431,432,433,434,435,436,446,447,448,449,450,451,452,453,454,455,456,457,467,468,469,470,471,472,473,474,475,476,477,478]
def kindSupport3_006 : List Nat := [488,489,490,491,492,493,494,495,496,497,498,499,509,510,511,512,513,514,515,516,517,518,519,520,530,531,532,533,534,535,536,537]
def kindSupport3_007 : List Nat := [538,539,540,541,551,552,553,554,555,556,557,558,559,560,561,562,572,573,574,575,576,577,578,579,580,581,582,583,594,595,596,597]
def kindSupport3_008 : List Nat := [598,599,600,601,602,603,604,605,606,607,608,615,616,617,618,619,620,627,628,629,630,631,632,639,640,641,642,643,644,651,652,653]
def kindSupport3_009 : List Nat := [654,655,656,663,664,665,666,667,668,675,676,677,678,679,680,690,691,692,693,694,695,696,697,698,699,700,701,711,712,713,714,715]
def kindSupport3_010 : List Nat := [716,717,718,719,720,721,722,732,733,734,735,736,737,738,739,740,741,742,743,753,754,755,756,757,758,759,760,761,762,763,764,765]
def kindSupport3_011 : List Nat := [766,767,768,778,779,780,781,782,783,784,785,786,787,788,789,799,800,801,802,803,804,805,806,807,808,809,810,820,821,822,823,824]
def kindSupport3_012 : List Nat := [825,826,827,828,829,830,831,841,842,843,844,845,846,847,848,849,850,851,852,862,863,864,865,866,867,868,869,870,871,872,873,883]
def kindSupport3_013 : List Nat := [884,885,886,887,888,889,890,891,892,893,894,904,905,906,907,908,909,910,911,912,913,914,915,925,926,927,928,929,930,931,932,933]
def kindSupport3_014 : List Nat := [934,935,936,947,948,949,950,951,952,953,954,955,956,957,958,959,960,961,968,969,970,971,972,973,980,981,982,983,984,985,992,993]
def kindSupport3_015 : List Nat := [994,995,996,997,1004,1005,1006,1007,1008,1009,1016,1017,1018,1019,1020,1021,1028,1029,1030,1031,1032,1033,1043,1044,1045,1046,1047,1048,1049,1050,1051,1052]
def kindSupport3_016 : List Nat := [1053,1054,1064,1065,1066,1067,1068,1069,1070,1071,1072,1073,1074,1075,1085,1086,1087,1088,1089,1090,1091,1092,1093,1094,1095,1096,1106,1107,1108,1109,1110,1111]
def kindSupport3_017 : List Nat := [1112,1113,1114,1115,1116,1117,1124,1125,1126,1127,1128,1129,1136,1137,1138,1139,1140,1141,1148,1149,1150,1151,1152,1153,1160,1161,1162,1163,1164,1165,1172,1173]
def kindSupport3_018 : List Nat := [1174,1175,1176,1177,1184,1185,1186,1187,1188,1189,1199,1200,1201,1202,1203,1204,1205,1206,1207,1208,1209,1210,1220,1221,1222,1223,1224,1225,1226,1227,1228,1229]
def kindSupport3_019 : List Nat := [1230,1231,1241,1242,1243,1244,1245,1246,1247,1248,1249,1250,1251,1252,1262,1263,1264,1265,1266,1267,1268,1269,1270,1271,1272,1273,1283,1284,1285,1286,1287,1288]
def kindSupport3_020 : List Nat := [1289,1290,1291,1292,1293,1294,1304,1305,1306,1307,1308,1309,1310,1311,1312,1313,1314,1315,1325,1326,1327,1328,1329,1330,1331,1332,1333,1334,1335,1336,1346,1347]
def kindSupport3_021 : List Nat := [1348,1349,1350,1351,1352,1353,1354,1355,1356,1357,1368,1369,1370,1371,1372,1373,1374,1375,1376,1377,1378,1379,1380,1381,1382,1392,1393,1394,1395,1396,1397,1398]
def kindSupport3_022 : List Nat := [1399,1400,1401,1402,1403,1413,1414,1415,1416,1417,1418,1419,1420,1421,1422,1423,1424,1434,1435,1436,1437,1438,1439,1440,1441,1442,1443,1444,1445,1455,1456,1457]
def kindSupport3_023 : List Nat := [1458,1459,1460,1461,1462,1463,1464,1465,1466,1477,1478,1479,1480,1481,1482,1483,1484,1485,1486,1487,1488,1489,1490,1491,1501,1502,1503,1504,1505,1506,1507,1508]
def kindSupport3_024 : List Nat := [1509,1510,1511,1512,1522,1523,1524,1525,1526,1527,1528,1529,1530,1531,1532,1533,1543,1544,1545,1546,1547,1548,1549,1550,1551,1552,1553,1554,1564,1565,1566,1567]
def kindSupport3_025 : List Nat := [1568,1569,1570,1571,1572,1573,1574,1575,1586,1587,1588,1589,1590,1591,1592,1593,1594,1595,1596,1597,1598,1599,1600,1611,1612,1613,1614,1615,1616,1617,1618,1619]
def kindSupport3_026 : List Nat := [1620,1621,1622,1623,1624,1625]
def kindSupport3_code : Nat := 0x65965865765665565465365265165064f64e64d64c64b64063f63e63d63c63b63a63963863763663563463363262762662562462362262162061f61e61d61c61261161060f60e60d60c60b60a6096086075fd5fc5fb5fa5f95f85f75f65f55f45f35f25e85e75e65e55e45e35e25e15e05df5de5dd5d35d25d15d05cf5ce5cd5cc5cb5ca5c95c85c75c65c55ba5b95b85b75b65b55b45b35b25b15b05af5a55a45a35a25a15a059f59e59d59c59b59a59058f58e58d58c58b58a58958858758658557b57a57957857757657557457357257157056656556456356256156055f55e55d55c55b55a55955854d54c54b54a54954854754654554454354253853753653553453353253153052f52e52d52352252152051f51e51d51c51b51a51951850e50d50c50b50a5095085075065055045034f94f84f74f64f54f44f34f24f14f04ef4ee4e44e34e24e14e04df4de4dd4dc4db4da4d94cf4ce4cd4cc4cb4ca4c94c84c74c64c54c44ba4b94b84b74b64b54b44b34b24b14b04af4a54a44a34a24a14a049949849749649549448d48c48b48a48948848148047f47e47d47c47547447347247147046946846746646546445d45c45b45a45945845745645545445345244844744644544444344244144043f43e43d43343243143042f42e42d42c42b42a42942841e41d41c41b41a4194184174164154144134094084074064054043fd3fc3fb3fa3f93f83f13f03ef3ee3ed3ec3e53e43e33e23e13e03d93d83d73d63d53d43cd3cc3cb3ca3c93c83c13c03bf3be3bd3bc3bb3ba3b93b83b73b63b53b43b33a83a73a63a53a43a33a23a13a039f39e39d39339239139038f38e38d38c38b38a38938837e37d37c37b37a37937837737637537437336936836736636536436336236136035f35e35435335235135034f34e34d34c34b34a34933f33e33d33c33b33a33933833733633533432a32932832732632532432332232132031f31531431331231131030f30e30d30c30b30a3002ff2fe2fd2fc2fb2fa2f92f82f72f62f52f42f32f22f12e72e62e52e42e32e22e12e02df2de2dd2dc2d22d12d02cf2ce2cd2cc2cb2ca2c92c82c72bd2bc2bb2ba2b92b82b72b62b52b42b32b22a82a72a62a52a42a329c29b29a29929829729028f28e28d28c28b28428328228128027f27827727627527427326c26b26a26926826726025f25e25d25c25b25a25925825725625525425325224724624524424324224124023f23e23d23c23223123022f22e22d22c22b22a22922822721d21c21b21a2192182172162152142132122082072062052042032022012001ff1fe1fd1f31f21f11f01ef1ee1ed1ec1eb1ea1e91e81de1dd1dc1db1da1d91d81d71d61d51d41d31c91c81c71c61c51c41c31c21c11c01bf1be1b41b31b21b11b01af1ae1ad1ac1ab1aa1a919f19e19d19c19b19a19319219119018f18e18718618518418318217b17a17917817717616f16e16d16c16b16a16316216116015f15e15715615515415315215115014f14e14d14c14214114013f13e13d13c13b13a13913813712d12c12b12a12912812712612512412312211811711611511411311211111010f10e10d1031021011000ff0fe0f70f60f50f40f30f20eb0ea0e90e80e70e60df0de0dd0dc0db0da0d30d20d10d00cf0ce0c70c60c50c40c30c20bb0ba0b90b80b70b60af0ae0ad0ac0ab0aa0a30a20a10a009f09e09709609509409309208b08a08908808708607f07e07d07c07b07a
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
def kindSupport3_rest_027 : Nat := PackedRawNatGrowth.drop 10056 kindSupport3_code
def kindSupport3_suffix_027 : List Nat := []
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
    (PackedRawNatGrowth.readList 12 838 kindSupport3_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra01
