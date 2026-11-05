module
prelude
public import RootedSixExtra03GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra03
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
def kindSupport3_code : Nat := 0x65965865765665565465365265165064f64e64d64c64b64063f63e63d63c63b63a63963863763663563463363262762662562462362262162061f61e61d61c61261161060f60e60d60c60b60a6096086075fd5fc5fb5fa5f95f85f75f65f55f45f35f25e85e75e65e55e45e35e25e15e05df5de5dd5d35d25d15d05cf5ce5cd5cc5cb5ca5c95c85c75c65c55ba5b95b85b75b65b55b45b35b25b15b05af5a55a45a35a25a15a059f59e59d59c59b59a59058f58e58d58c58b58a58958858758658557b57a57957857757657557457357257157056656556456356256156055f55e55d55c55b55155054f54e54d54c54b54a54954854754653c53b53a53953853753653553453353253152752652552452352252152051f51e51d51c51251151050f50e50d5065055045035025014fa4f94f84f74f64f54ee4ed4ec4eb4ea4e94e24e14e04df4de4dd4d64d54d44d34d24d14ca4c94c84c74c64c54c44c34c24c14c04bf4be4bd4bc4b14b04af4ae4ad4ac4ab4aa4a94a84a74a649c49b49a49949849749649549449349249148748648548448348248148047f47e47d47c47247147046f46e46d46c46b46a46946846745d45c45b45a45945845745645545445345244844744644544444344244144043f43e43d43343243143042f42e42d42c42b42a42942841e41d41c41b41a4194184174164154144134094084074064054043fd3fc3fb3fa3f93f83f13f03ef3ee3ed3ec3e53e43e33e23e13e03d93d83d73d63d53d43cd3cc3cb3ca3c93c83c13c03bf3be3bd3bc3bb3ba3b93b83b73b63b53b43b33a83a73a63a53a43a33a23a13a039f39e39d39339239139038f38e38d38c38b38a38938837e37d37c37b37a37937837737637537437336936836736636536436336236136035f35e35435335235135034f34e34d34c34b34a34933f33e33d33c33b33a33933833733633533432a32932832732632532432332232132031f31531431331231131030f30e30d30c30b30a3002ff2fe2fd2fc2fb2f42f32f22f12f02ef2e82e72e62e52e42e32dc2db2da2d92d82d72d02cf2ce2cd2cc2cb2c42c32c22c12c02bf2b82b72b62b52b42b32b22b12b02af2ae2ad2a32a22a12a029f29e29d29c29b29a29929828e28d28c28b28a28928828728628528428327927827727627527427327227127026f26e26426326226126025f25825725625525425324c24b24a24924824724023f23e23d23c23b23423323223123022f22822722622522422321c21b21a21921821721621521421321221121020f20e2032022012001ff1fe1fd1fc1fb1fa1f91f81ee1ed1ec1eb1ea1e91e81e71e61e51e41e31d91d81d71d61d51d41d31d21d11d01cf1ce1c41c31c21c11c01bf1be1bd1bc1bb1ba1b91af1ae1ad1ac1ab1aa1a91a81a71a61a51a419a19919819719619519419319219119018f18518418318218118017f17e17d17c17b17a17016f16e16d16c16b16a16916816716616515b15a15915815715615515415315215115014f14e14d14c14214114013f13e13d13c13b13a13913813712d12c12b12a12912812712612512412312211811711611511411311211111010f10e10d1031021011000ff0fe0f70f60f50f40f30f20eb0ea0e90e80e70e60df0de0dd0dc0db0da0d30d20d10d00cf0ce0c70c60c50c40c30c20bb0ba0b90b80b70b60af0ae0ad0ac0ab0aa0a30a20a10a009f09e09709609509409309208b08a08908808708607f07e07d07c07b07a
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra03
