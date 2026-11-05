module
prelude
public import RootedSixBase01GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
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
def kindSupport3_code : Nat := 0x1964658195c6561954654194c6521944650193c64e193464c192c64018fc63e18f463c18ec63a18e463818dc63618d463418cc632189c6261894624188c6221884620187c61e187461c1848611184060f183860d183060b1828609182060717f45fc17ec5fa17e45f817dc5f617d45f417cc5f217a05e717985e517905e317885e117805df17785dd174c5d217445d0173c5ce17345cc172c5ca17245c8171c5c617145ba16e45b816dc5b616d45b416cc5b216c45b016bc5a516905a316885a1168059f167859d167059b1668590163c58e163458c162c58a1624588161c586161457b15e857915e057715d857515d057315c857115c05661594564158c5621584560157c55e157455c156c55a1564558153454c152c54a1524548151c5461514544150c54214e053714d853514d053314c853114c052f14b852d148c5221484520147c51e147451c146c51a1464518143850d143050b142850914205071418505141050313e44f813dc4f613d44f413cc4f213c44f013bc4ee13904e313884e113804df13784dd13704db13684d9133c4ce13344cc132c4ca13244c8131c4c613144c412e84b912e04b712d84b512d04b312c84b112c04af12944a4128c4a212844a01264498125c4961254494123448c122c48a1224488120448011fc47e11f447c11d447411cc47211c447011a4468119c4661194464117445c116c45a1164458115c4561154454114c4521120447111844511104431108441110043f10f843d10cc43210c443010bc42e10b442c10ac42a10a4428107841d107041b10684191060417105841510504131024408101c40610144040ff43fc0fec3fa0fe43f80fc43f00fbc3ee0fb43ec0f943e40f8c3e20f843e00f643d80f5c3d60f543d40f343cc0f2c3ca0f243c80f043c00efc3be0ef43bc0eec3ba0ee43b80edc3b60ed43b40ecc3a80e9c3a60e943a40e8c3a20e843a00e7c39e0e743930e483910e4038f0e3838d0e3038b0e283890e2037e0df437c0dec37a0de43780ddc3760dd43740dcc3690da03670d983650d903630d883610d8035f0d783540d4c3520d443500d3c34e0d3434c0d2c34a0d2433f0cf833d0cf033b0ce83390ce03370cd83350cd032a0ca43280c9c3260c943240c8c3220c843200c7c3150c503130c483110c4030f0c3830d0c3030b0c283000bfc2fe0bf42fc0bec2fa0be42f80bdc2f60bd42f40bcc2f20bc42e70b982e50b902e30b882e10b802df0b782dd0b702d20b442d00b3c2ce0b342cc0b2c2ca0b242c80b1c2bd0af02bb0ae82b90ae02b70ad82b50ad02b30ac82a80a9c2a60a942a40a8c29c0a6c29a0a642980a5c2900a3c28e0a3428c0a2c2840a0c2820a0428009fc27809dc27609d427409cc26c09ac26a09a4268099c260097c25e097425c096c25a0964258095c2560954254094c252091c2460914244090c242090424008fc23e08f423c08c823108c022f08b822d08b022b08a822908a0227087421c086c21a0864218085c2160854214084c212082020708182050810203080820108001ff07f81fd07cc1f207c41f007bc1ee07b41ec07ac1ea07a41e807781dd07701db07681d907601d707581d507501d307241c8071c1c607141c4070c1c207041c006fc1be06d01b306c81b106c01af06b81ad06b01ab06a81a9067c19e067419c066c19a064c1920644190063c18e061c1860614184060c18205ec17a05e417805dc17605bc16e05b416c05ac16a058c1620584160057c15e055c1560554154054c1520544150053c14e053414c0508141050013f04f813d04f013b04e813904e013704b412c04ac12a04a4128049c1260494124048c1220460117045811504501130448111044010f043810d040c102040410003fc0fe03dc0f603d40f403cc0f203ac0ea03a40e8039c0e6037c0de03740dc036c0da034c0d203440d0033c0ce031c0c603140c4030c0c202ec0ba02e40b802dc0b602bc0ae02b40ac02ac0aa028c0a202840a0027c09e025c0960254094024c092022c08a0224088021c08601fc07e01f407c01ec07a
def kindSupport3_rest_000 : Nat := PackedRawNatGrowth.drop 0 kindSupport3_code
def kindSupport3_rest_001 : Nat := PackedRawNatGrowth.drop 448 kindSupport3_code
def kindSupport3_rest_002 : Nat := PackedRawNatGrowth.drop 896 kindSupport3_code
def kindSupport3_rest_003 : Nat := PackedRawNatGrowth.drop 1344 kindSupport3_code
def kindSupport3_rest_004 : Nat := PackedRawNatGrowth.drop 1792 kindSupport3_code
def kindSupport3_rest_005 : Nat := PackedRawNatGrowth.drop 2240 kindSupport3_code
def kindSupport3_rest_006 : Nat := PackedRawNatGrowth.drop 2688 kindSupport3_code
def kindSupport3_rest_007 : Nat := PackedRawNatGrowth.drop 3136 kindSupport3_code
def kindSupport3_rest_008 : Nat := PackedRawNatGrowth.drop 3584 kindSupport3_code
def kindSupport3_rest_009 : Nat := PackedRawNatGrowth.drop 4032 kindSupport3_code
def kindSupport3_rest_010 : Nat := PackedRawNatGrowth.drop 4480 kindSupport3_code
def kindSupport3_rest_011 : Nat := PackedRawNatGrowth.drop 4928 kindSupport3_code
def kindSupport3_rest_012 : Nat := PackedRawNatGrowth.drop 5376 kindSupport3_code
def kindSupport3_rest_013 : Nat := PackedRawNatGrowth.drop 5824 kindSupport3_code
def kindSupport3_rest_014 : Nat := PackedRawNatGrowth.drop 6272 kindSupport3_code
def kindSupport3_rest_015 : Nat := PackedRawNatGrowth.drop 6720 kindSupport3_code
def kindSupport3_rest_016 : Nat := PackedRawNatGrowth.drop 7168 kindSupport3_code
def kindSupport3_rest_017 : Nat := PackedRawNatGrowth.drop 7616 kindSupport3_code
def kindSupport3_rest_018 : Nat := PackedRawNatGrowth.drop 8064 kindSupport3_code
def kindSupport3_rest_019 : Nat := PackedRawNatGrowth.drop 8512 kindSupport3_code
def kindSupport3_rest_020 : Nat := PackedRawNatGrowth.drop 8960 kindSupport3_code
def kindSupport3_rest_021 : Nat := PackedRawNatGrowth.drop 9408 kindSupport3_code
def kindSupport3_rest_022 : Nat := PackedRawNatGrowth.drop 9856 kindSupport3_code
def kindSupport3_rest_023 : Nat := PackedRawNatGrowth.drop 10304 kindSupport3_code
def kindSupport3_rest_024 : Nat := PackedRawNatGrowth.drop 10752 kindSupport3_code
def kindSupport3_rest_025 : Nat := PackedRawNatGrowth.drop 11200 kindSupport3_code
def kindSupport3_rest_026 : Nat := PackedRawNatGrowth.drop 11648 kindSupport3_code
def kindSupport3_rest_027 : Nat := PackedRawNatGrowth.drop 11732 kindSupport3_code
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
theorem kindSupport3_source : kindRows 3 =
    (PackedRawNatGrowth.readList 14 838 kindSupport3_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase01
