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
def kindSupport9_000 : List Nat := [1150,1151,1152,1153,1154,1155,1156,1157,1158,1159,1160,1161,1162,1163,1164,1165,1166,1167,1168,1169,1170,1171,1172,1173,1174,1175,1176,1177,1178,1179,1180,1181]
def kindSupport9_001 : List Nat := [1182,1183,1184,1185,1186,1187,1188,1189,1190,1191,1192,1193,1194,1195,1196,1197,1198,1199,1200,1201,1202,1203,1204,1205,1206,1207,1208,1209,1210,1211,1212,1213]
def kindSupport9_002 : List Nat := [1214,1215,1216,1217,1218,1219,1220,1221,1222,1223,1224,1225,1226,1227,1228,1229,1230,1231,1232,1233,1234,1235,1236,1237,1238,1239,1240,1241,1242,1243,1244,1245]
def kindSupport9_003 : List Nat := [1246,1247,1248,1249,1250,1251,1252,1253,1254,1255,1256,1257,1258,1259,1260,1261,1262,1263,1264,1265,1266,1267,1268,1269,1270,1271,1272,1273,1274,1275,1276,1277]
def kindSupport9_004 : List Nat := [1278,1279,1280,1281,1282,1283,1284,1285,1286,1287,1288,1289,1290,1291,1292,1293,1294,1295,1296,1297,1298,1299,1300,1301,1302,1303,1304,1305,1306,1307,1308,1309]
def kindSupport9_005 : List Nat := [1310,1311,1312,1313,1314,1315,1316,1317,1318,1319,1320,1321,1322,1323,1324,1325,1326,1327,1328,1329,1330,1331,1332,1333,1334,1335,1336,1337,1338,1339,1340,1341]
def kindSupport9_006 : List Nat := [1342,1343,1344,1345,1346,1347,1348,1349,1350,1351,1352,1353,1354,1355,1356,1357,1358,1359,1360,1361,1362,1363,1364,1365,1366,1367,1368,1369,1370,1371,1372,1373]
def kindSupport9_007 : List Nat := [1374,1375,1376,1377,1378,1379,1380,1381,1382,1383,1384,1385,1386,1387,1388,1389,1390,1391,1392,1393,1394,1395,1396,1397,1398,1399,1400,1401,1402,1403,1404,1405]
def kindSupport9_008 : List Nat := [1406,1407,1408,1409,1410,1411,1412,1413,1414,1415,1416,1417,1418,1419,1420,1421,1422,1423,1424,1425,1426,1427,1428,1429,1430,1431,1432,1433,1434,1435,1436,1437]
def kindSupport9_009 : List Nat := [1438,1439,1440,1441,1442,1443,1444,1445,1446,1447,1448,1449,1450,1451,1452,1453,1454,1455,1456,1457,1458,1459,1460,1461,1462,1463,1464,1465,1466,1467,1468,1469]
def kindSupport9_010 : List Nat := [1470,1471,1472,1473,1474,1475,1476,1477,1478,1479,1480,1481,1482,1483,1484,1485,1486,1487,1488,1489,1490,1491,1492,1493,1494,1495,1496,1497,1498,1499,1500,1501]
def kindSupport9_011 : List Nat := [1502,1503,1504,1505,1506,1507,1508,1509,1510,1511,1512,1513,1514,1515,1516,1517,1518,1519,1520,1521,1522,1523,1524,1525,1526,1527,1528,1529,1530,1531,1532,1533]
def kindSupport9_012 : List Nat := [1534,1535,1536,1537,1538,1539,1540,1541,1542,1543,1544,1545,1546,1547,1548,1549,1550,1551,1552,1553,1554,1555,1556,1557,1558,1559,1560,1561,1562,1563,1564,1565]
def kindSupport9_013 : List Nat := [1566,1567,1568,1569,1570,1571,1572,1573,1574,1575,1576,1577,1578,1579,1580,1581,1582,1583,1584,1585,1586,1587,1588,1589,1590,1591,1592,1593]
def kindSupport9_code : Nat := 0x63963863763663563463363263163062f62e62d62c62b62a62962862762662562462362262162061f61e61d61c61b61a61961861761661561461361261161060f60e60d60c60b60a6096086076066056046036026016005ff5fe5fd5fc5fb5fa5f95f85f75f65f55f45f35f25f15f05ef5ee5ed5ec5eb5ea5e95e85e75e65e55e45e35e25e15e05df5de5dd5dc5db5da5d95d85d75d65d55d45d35d25d15d05cf5ce5cd5cc5cb5ca5c95c85c75c65c55c45c35c25c15c05bf5be5bd5bc5bb5ba5b95b85b75b65b55b45b35b25b15b05af5ae5ad5ac5ab5aa5a95a85a75a65a55a45a35a25a15a059f59e59d59c59b59a59959859759659559459359259159058f58e58d58c58b58a58958858758658558458358258158057f57e57d57c57b57a57957857757657557457357257157056f56e56d56c56b56a56956856756656556456356256156055f55e55d55c55b55a55955855755655555455355255155054f54e54d54c54b54a54954854754654554454354254154053f53e53d53c53b53a53953853753653553453353253153052f52e52d52c52b52a52952852752652552452352252152051f51e51d51c51b51a51951851751651551451351251151050f50e50d50c50b50a5095085075065055045035025015004ff4fe4fd4fc4fb4fa4f94f84f74f64f54f44f34f24f14f04ef4ee4ed4ec4eb4ea4e94e84e74e64e54e44e34e24e14e04df4de4dd4dc4db4da4d94d84d74d64d54d44d34d24d14d04cf4ce4cd4cc4cb4ca4c94c84c74c64c54c44c34c24c14c04bf4be4bd4bc4bb4ba4b94b84b74b64b54b44b34b24b14b04af4ae4ad4ac4ab4aa4a94a84a74a64a54a44a34a24a14a049f49e49d49c49b49a49949849749649549449349249149048f48e48d48c48b48a48948848748648548448348248148047f47e
def kindSupport9_rest_000 : Nat := PackedRawNatGrowth.drop 0 kindSupport9_code
def kindSupport9_rest_001 : Nat := PackedRawNatGrowth.drop 384 kindSupport9_code
def kindSupport9_rest_002 : Nat := PackedRawNatGrowth.drop 768 kindSupport9_code
def kindSupport9_rest_003 : Nat := PackedRawNatGrowth.drop 1152 kindSupport9_code
def kindSupport9_rest_004 : Nat := PackedRawNatGrowth.drop 1536 kindSupport9_code
def kindSupport9_rest_005 : Nat := PackedRawNatGrowth.drop 1920 kindSupport9_code
def kindSupport9_rest_006 : Nat := PackedRawNatGrowth.drop 2304 kindSupport9_code
def kindSupport9_rest_007 : Nat := PackedRawNatGrowth.drop 2688 kindSupport9_code
def kindSupport9_rest_008 : Nat := PackedRawNatGrowth.drop 3072 kindSupport9_code
def kindSupport9_rest_009 : Nat := PackedRawNatGrowth.drop 3456 kindSupport9_code
def kindSupport9_rest_010 : Nat := PackedRawNatGrowth.drop 3840 kindSupport9_code
def kindSupport9_rest_011 : Nat := PackedRawNatGrowth.drop 4224 kindSupport9_code
def kindSupport9_rest_012 : Nat := PackedRawNatGrowth.drop 4608 kindSupport9_code
def kindSupport9_rest_013 : Nat := PackedRawNatGrowth.drop 4992 kindSupport9_code
def kindSupport9_rest_014 : Nat := PackedRawNatGrowth.drop 5328 kindSupport9_code
def kindSupport9_suffix_014 : List Nat := []
def kindSupport9_suffix_013 : List Nat := kindSupport9_013 ++ kindSupport9_suffix_014
def kindSupport9_suffix_012 : List Nat := kindSupport9_012 ++ kindSupport9_suffix_013
def kindSupport9_suffix_011 : List Nat := kindSupport9_011 ++ kindSupport9_suffix_012
def kindSupport9_suffix_010 : List Nat := kindSupport9_010 ++ kindSupport9_suffix_011
def kindSupport9_suffix_009 : List Nat := kindSupport9_009 ++ kindSupport9_suffix_010
def kindSupport9_suffix_008 : List Nat := kindSupport9_008 ++ kindSupport9_suffix_009
def kindSupport9_suffix_007 : List Nat := kindSupport9_007 ++ kindSupport9_suffix_008
def kindSupport9_suffix_006 : List Nat := kindSupport9_006 ++ kindSupport9_suffix_007
def kindSupport9_suffix_005 : List Nat := kindSupport9_005 ++ kindSupport9_suffix_006
def kindSupport9_suffix_004 : List Nat := kindSupport9_004 ++ kindSupport9_suffix_005
def kindSupport9_suffix_003 : List Nat := kindSupport9_003 ++ kindSupport9_suffix_004
def kindSupport9_suffix_002 : List Nat := kindSupport9_002 ++ kindSupport9_suffix_003
def kindSupport9_suffix_001 : List Nat := kindSupport9_001 ++ kindSupport9_suffix_002
def kindSupport9_suffix_000 : List Nat := kindSupport9_000 ++ kindSupport9_suffix_001
theorem kindSupport9_source : kindSupports 9 =
    (PackedRawNatGrowth.readList 12 444 kindSupport9_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra05
