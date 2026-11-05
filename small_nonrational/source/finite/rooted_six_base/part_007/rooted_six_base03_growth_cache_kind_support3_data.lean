module
prelude
public import RootedSixBase03GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def kindSupport3_000 : List Nat := [122,123,124,125,126,127,134,135,136,137,138,139,146,147,148,149,150,151,158,159,160,161,162,163,170,171,172,173,174,175,182,183]
def kindSupport3_001 : List Nat := [184,185,186,187,194,195,196,197,198,199,206,207,208,209,210,211,218,219,220,221,222,223,230,231,232,233,234,235,242,243,244,245]
def kindSupport3_002 : List Nat := [246,247,254,255,256,257,258,259,269,270,271,272,273,274,275,276,277,278,279,280,290,291,292,293,294,295,296,297,298,299,300,301]
def kindSupport3_003 : List Nat := [311,312,313,314,315,316,317,318,319,320,321,322,332,333,334,335,336,337,338,339,340,341,342,343,344,345,346,347,357,358,359,360]
def kindSupport3_004 : List Nat := [361,362,363,364,365,366,367,368,378,379,380,381,382,383,384,385,386,387,388,389,399,400,401,402,403,404,405,406,407,408,409,410]
def kindSupport3_005 : List Nat := [420,421,422,423,424,425,426,427,428,429,430,431,441,442,443,444,445,446,447,448,449,450,451,452,462,463,464,465,466,467,468,469]
def kindSupport3_006 : List Nat := [470,471,472,473,483,484,485,486,487,488,489,490,491,492,493,494,504,505,506,507,508,509,510,511,512,513,514,515,526,527,528,529]
def kindSupport3_007 : List Nat := [530,531,532,533,534,535,536,537,538,539,540,547,548,549,550,551,552,559,560,561,562,563,564,571,572,573,574,575,576,583,584,585]
def kindSupport3_008 : List Nat := [586,587,588,595,596,597,598,599,600,607,608,609,610,611,612,622,623,624,625,626,627,628,629,630,631,632,633,643,644,645,646,647]
def kindSupport3_009 : List Nat := [648,649,650,651,652,653,654,664,665,666,667,668,669,670,671,672,673,674,675,685,686,687,688,689,690,691,692,693,694,695,696,703]
def kindSupport3_010 : List Nat := [704,705,706,707,708,715,716,717,718,719,720,727,728,729,730,731,732,739,740,741,742,743,744,751,752,753,754,755,756,763,764,765]
def kindSupport3_011 : List Nat := [766,767,768,778,779,780,781,782,783,784,785,786,787,788,789,799,800,801,802,803,804,805,806,807,808,809,810,820,821,822,823,824]
def kindSupport3_012 : List Nat := [825,826,827,828,829,830,831,841,842,843,844,845,846,847,848,849,850,851,852,862,863,864,865,866,867,868,869,870,871,872,873,883]
def kindSupport3_013 : List Nat := [884,885,886,887,888,889,890,891,892,893,894,904,905,906,907,908,909,910,911,912,913,914,915,925,926,927,928,929,930,931,932,933]
def kindSupport3_014 : List Nat := [934,935,936,947,948,949,950,951,952,953,954,955,956,957,958,959,960,961,968,969,970,971,972,973,980,981,982,983,984,985,992,993]
def kindSupport3_015 : List Nat := [994,995,996,997,1004,1005,1006,1007,1008,1009,1016,1017,1018,1019,1020,1021,1028,1029,1030,1031,1032,1033,1043,1044,1045,1046,1047,1048,1049,1050,1051,1052]
def kindSupport3_016 : List Nat := [1053,1054,1064,1065,1066,1067,1068,1069,1070,1071,1072,1073,1074,1075,1085,1086,1087,1088,1089,1090,1091,1092,1093,1094,1095,1096,1106,1107,1108,1109,1110,1111]
def kindSupport3_017 : List Nat := [1112,1113,1114,1115,1116,1117,1127,1128,1129,1130,1131,1132,1133,1134,1135,1136,1137,1138,1148,1149,1150,1151,1152,1153,1154,1155,1156,1157,1158,1159,1169,1170]
def kindSupport3_018 : List Nat := [1171,1172,1173,1174,1175,1176,1177,1178,1179,1180,1190,1191,1192,1193,1194,1195,1196,1197,1198,1199,1200,1201,1212,1213,1214,1215,1216,1217,1218,1219,1220,1221]
def kindSupport3_019 : List Nat := [1222,1223,1224,1225,1226,1233,1234,1235,1236,1237,1238,1245,1246,1247,1248,1249,1250,1257,1258,1259,1260,1261,1262,1269,1270,1271,1272,1273,1274,1281,1282,1283]
def kindSupport3_020 : List Nat := [1284,1285,1286,1293,1294,1295,1296,1297,1298,1308,1309,1310,1311,1312,1313,1314,1315,1316,1317,1318,1319,1329,1330,1331,1332,1333,1334,1335,1336,1337,1338,1339]
def kindSupport3_021 : List Nat := [1340,1350,1351,1352,1353,1354,1355,1356,1357,1358,1359,1360,1361,1371,1372,1373,1374,1375,1376,1377,1378,1379,1380,1381,1382,1392,1393,1394,1395,1396,1397,1398]
def kindSupport3_022 : List Nat := [1399,1400,1401,1402,1403,1413,1414,1415,1416,1417,1418,1419,1420,1421,1422,1423,1424,1434,1435,1436,1437,1438,1439,1440,1441,1442,1443,1444,1445,1455,1456,1457]
def kindSupport3_023 : List Nat := [1458,1459,1460,1461,1462,1463,1464,1465,1466,1477,1478,1479,1480,1481,1482,1483,1484,1485,1486,1487,1488,1489,1490,1491,1501,1502,1503,1504,1505,1506,1507,1508]
def kindSupport3_024 : List Nat := [1509,1510,1511,1512,1522,1523,1524,1525,1526,1527,1528,1529,1530,1531,1532,1533,1543,1544,1545,1546,1547,1548,1549,1550,1551,1552,1553,1554,1564,1565,1566,1567]
def kindSupport3_025 : List Nat := [1568,1569,1570,1571,1572,1573,1574,1575,1586,1587,1588,1589,1590,1591,1592,1593,1594,1595,1596,1597,1598,1599,1600,1611,1612,1613,1614,1615,1616,1617,1618,1619]
def kindSupport3_026 : List Nat := [1620,1621,1622,1623,1624,1625]
def kindSupport3_code : Nat := 0xcb265832b9958caa6543299948ca26503279938c9a64c3259900c7e63e31e98f0c7663a31c98e0c6e63631a98d0c666323139898c4a6243119888c4262030f9878c3a61c3091844c2060f3071834c1860b3051824c106072fe97f0bf65fa2fc97e0bee5f62fa97d0be65f22f4179cbcc5e52f2178cbc45e12f0177cbbc5dd2e99748ba25d02e79738b9a5cc2e59728b925c82e39718b8a5ba2dc96e0b6e5b62da96d0b665b22d896c0b5e5a52d2168cb445a12d0167cb3c59d2ce166cb345902c79638b1a58c2c59628b125882c39618b0a57b2bd15e4af05772bb15d4ae85732b915c4ae05662b29590ac65622b09580abe55e2ae9570ab65512a8153ca9c54d2a6152ca945492a4151ca8c53c29d94e8a7253829b94d8a6a53429994c8a625272931494a485232911484a4051f28f1474a385122889440a1e50e2869418a0a5042819408a024fa27c93e09ee4f627a93b89da4ec27593a89d24e227093809be4de26e93589aa4d426993489a24ca264932098e4c626293109864c2260930097e4be25e92f09624b025792b895a4ac25592a89524a8253929893849b24d126493049724b1254928493249124490e486242921090648224092008fe47e23e91f08e447123811bc8dc46d23611ac8d4469234119c8ba45c22d91688b245822b91588aa45422991488904472231114888443221110488043f21f10f486643221890c085e42e21690b085642a21490a083c41d20e106c83441920c105c82c41520a104c812408203901880a4041fe8ff07f63fa1fc8fe07e23f01f78fb87da3ec1f28f907c63e21f08f807b23d81eb8f587aa3d41e68f307963ca1e48f207823c01df8ef877a3bc1dd8ee87723b81db8ed876a3b41d98ea074e3a61d28e907463a21d08e8073e39e1ce8e4c7243911c80e3c71c38d1c60e2c7143891c40df86fa37c1bd8de86f23781bb8dd86ea3741b98da46d03671b30d946c83631b10d846c035f1af0d506a63521a88d4069e34e1a68d3069634a1a48cfc67c33d19e0cec67433919c0cdc66c33519a0ca86523281938c9864a3241918c8864232018f8c546283131890c4462030f1870c3461830b1850c005fe2fe17e8bf05f62f41798bc85e22f01778ba05ce2e61728b905c62dc16d8b685b22d816b8b4059e2ce1668b305962c41618b085822c015f8ae056e2b615a8ad05662b21588ac055e2ae1568a8c5442a11500a7c53c29d14e0a6c53429914c0a3851a28c1458a285122881438a1850a28414189e44f027713b09d44e827313909c44e026f13709904c626213089804be25812b89584aa254129893049624a124892048e24011f88f847a23c11d88d046623211888c045e228113889844a224111887043621a10c886042e21610a8850426212108884041e20e10188084022000ff87f83fa1fc0fd87e83f21f80f707b43d81eb0f507a43d01e70f307943c81e30ec87603ae1d60ea87503a61d20e8874039e1ce0e2070c3841c10e006fc37c1bd0de06ec3741b90d786b835a1ac0d586a83521a80d3869834a1a40cd06643301970cb06543281930c9064432018f0c286103061820c086002fe17e0be85f02f617a0b805bc2dc16d0b605ac2d41690b4059c2cc1650ad85682b21580ab85582aa1540a985482a21500a7853829a14c0a1050428013f09f04f427813b09d04e427013709684b025612a09484a024e126092849024612208c045c22c11508a044c224111088043c21c10d081840820210007f83f81ee0f607a83d01e60f207583a81d20e807383981be0de06e83701b60da06983481a20d0067833818e0c606283101860c205d82e81720b805b82d815e0ae05682b01560aa05182881420a004f827812e09604a8250126092045822811208804382180fe07e03e81f00f607a
def kindSupport3_rest_000 : Nat := PackedRawNatGrowth.drop 0 kindSupport3_code
def kindSupport3_rest_001 : Nat := PackedRawNatGrowth.drop 416 kindSupport3_code
def kindSupport3_rest_002 : Nat := PackedRawNatGrowth.drop 832 kindSupport3_code
def kindSupport3_rest_003 : Nat := PackedRawNatGrowth.drop 1248 kindSupport3_code
def kindSupport3_rest_004 : Nat := PackedRawNatGrowth.drop 1664 kindSupport3_code
def kindSupport3_rest_005 : Nat := PackedRawNatGrowth.drop 2080 kindSupport3_code
def kindSupport3_rest_006 : Nat := PackedRawNatGrowth.drop 2496 kindSupport3_code
def kindSupport3_rest_007 : Nat := PackedRawNatGrowth.drop 2912 kindSupport3_code
def kindSupport3_rest_008 : Nat := PackedRawNatGrowth.drop 3328 kindSupport3_code
def kindSupport3_rest_009 : Nat := PackedRawNatGrowth.drop 3744 kindSupport3_code
def kindSupport3_rest_010 : Nat := PackedRawNatGrowth.drop 4160 kindSupport3_code
def kindSupport3_rest_011 : Nat := PackedRawNatGrowth.drop 4576 kindSupport3_code
def kindSupport3_rest_012 : Nat := PackedRawNatGrowth.drop 4992 kindSupport3_code
def kindSupport3_rest_013 : Nat := PackedRawNatGrowth.drop 5408 kindSupport3_code
def kindSupport3_rest_014 : Nat := PackedRawNatGrowth.drop 5824 kindSupport3_code
def kindSupport3_rest_015 : Nat := PackedRawNatGrowth.drop 6240 kindSupport3_code
def kindSupport3_rest_016 : Nat := PackedRawNatGrowth.drop 6656 kindSupport3_code
def kindSupport3_rest_017 : Nat := PackedRawNatGrowth.drop 7072 kindSupport3_code
def kindSupport3_rest_018 : Nat := PackedRawNatGrowth.drop 7488 kindSupport3_code
def kindSupport3_rest_019 : Nat := PackedRawNatGrowth.drop 7904 kindSupport3_code
def kindSupport3_rest_020 : Nat := PackedRawNatGrowth.drop 8320 kindSupport3_code
def kindSupport3_rest_021 : Nat := PackedRawNatGrowth.drop 8736 kindSupport3_code
def kindSupport3_rest_022 : Nat := PackedRawNatGrowth.drop 9152 kindSupport3_code
def kindSupport3_rest_023 : Nat := PackedRawNatGrowth.drop 9568 kindSupport3_code
def kindSupport3_rest_024 : Nat := PackedRawNatGrowth.drop 9984 kindSupport3_code
def kindSupport3_rest_025 : Nat := PackedRawNatGrowth.drop 10400 kindSupport3_code
def kindSupport3_rest_026 : Nat := PackedRawNatGrowth.drop 10816 kindSupport3_code
def kindSupport3_rest_027 : Nat := PackedRawNatGrowth.drop 10894 kindSupport3_code
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
    (PackedRawNatGrowth.readList 13 838 kindSupport3_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase03
