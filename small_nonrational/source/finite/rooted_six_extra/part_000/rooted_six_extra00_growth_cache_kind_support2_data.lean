module
prelude
public import RootedSixExtra00GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def kindSupport2_000 : List Nat := [130,131,132,133,134,135,142,143,144,145,146,147,154,155,156,157,158,159,166,167,168,169,170,171,178,179,180,181,182,183,190,191]
def kindSupport2_001 : List Nat := [192,193,194,195,202,203,204,205,206,207,214,215,216,217,218,219,226,227,228,229,230,231,238,239,240,241,242,243,250,251,252,253]
def kindSupport2_002 : List Nat := [254,255,262,263,264,265,266,267,274,275,276,277,278,279,280,281,282,295,296,297,298,299,300,301,302,303,316,317,318,319,320,321]
def kindSupport2_003 : List Nat := [322,323,324,337,338,339,340,341,342,343,344,345,358,359,360,361,362,363,370,371,372,373,374,375,382,383,384,385,386,387,394,395]
def kindSupport2_004 : List Nat := [396,397,398,399,406,407,408,409,410,411,418,419,420,421,422,423,430,431,432,433,434,435,436,437,438,451,452,453,454,455,456,457]
def kindSupport2_005 : List Nat := [458,459,472,473,474,475,476,477,478,479,480,493,494,495,496,497,498,499,500,501,514,515,516,517,518,519,520,521,522,535,536,537]
def kindSupport2_006 : List Nat := [538,539,540,541,542,543,556,557,558,559,560,561,562,563,564,577,578,579,580,581,582,583,584,585,598,599,600,601,602,603,604,605]
def kindSupport2_007 : List Nat := [606,607,623,624,625,626,627,628,635,636,637,638,639,640,647,648,649,650,651,652,659,660,661,662,663,664,671,672,673,674,675,676]
def kindSupport2_008 : List Nat := [683,684,685,686,687,688,695,696,697,698,699,700,701,702,703,716,717,718,719,720,721,722,723,724,737,738,739,740,741,742,743,744]
def kindSupport2_009 : List Nat := [745,758,759,760,761,762,763,764,765,766,779,780,781,782,783,784,791,792,793,794,795,796,803,804,805,806,807,808,815,816,817,818]
def kindSupport2_010 : List Nat := [819,820,827,828,829,830,831,832,839,840,841,842,843,844,851,852,853,854,855,856,857,858,859,872,873,874,875,876,877,878,879,880]
def kindSupport2_011 : List Nat := [893,894,895,896,897,898,899,900,901,914,915,916,917,918,919,920,921,922,935,936,937,938,939,940,941,942,943,956,957,958,959,960]
def kindSupport2_012 : List Nat := [961,962,963,964,977,978,979,980,981,982,983,984,985,998,999,1000,1001,1002,1003,1004,1005,1006,1019,1020,1021,1022,1023,1024,1025,1026,1027,1028]
def kindSupport2_013 : List Nat := [1044,1045,1046,1047,1048,1049,1056,1057,1058,1059,1060,1061,1068,1069,1070,1071,1072,1073,1080,1081,1082,1083,1084,1085,1092,1093,1094,1095,1096,1097,1104,1105]
def kindSupport2_014 : List Nat := [1106,1107,1108,1109,1116,1117,1118,1119,1120,1121,1122,1123,1124,1137,1138,1139,1140,1141,1142,1143,1144,1145,1158,1159,1160,1161,1162,1163,1164,1165,1166,1179]
def kindSupport2_015 : List Nat := [1180,1181,1182,1183,1184,1185,1186,1187,1200,1201,1202,1203,1204,1205,1212,1213,1214,1215,1216,1217,1224,1225,1226,1227,1228,1229,1236,1237,1238,1239,1240,1241]
def kindSupport2_016 : List Nat := [1248,1249,1250,1251,1252,1253,1260,1261,1262,1263,1264,1265,1272,1273,1274,1275,1276,1277,1278,1279,1280,1293,1294,1295,1296,1297,1298,1299,1300,1301,1314,1315]
def kindSupport2_017 : List Nat := [1316,1317,1318,1319,1320,1321,1322,1335,1336,1337,1338,1339,1340,1341,1342,1343,1356,1357,1358,1359,1360,1361,1362,1363,1364,1377,1378,1379,1380,1381,1382,1383]
def kindSupport2_018 : List Nat := [1384,1385,1398,1399,1400,1401,1402,1403,1404,1405,1406,1419,1420,1421,1422,1423,1424,1425,1426,1427,1440,1441,1442,1443,1444,1445,1446,1447,1448,1449,1465,1466]
def kindSupport2_019 : List Nat := [1467,1468,1469,1470,1477,1478,1479,1480,1481,1482,1489,1490,1491,1492,1493,1494,1501,1502,1503,1504,1505,1506,1513,1514,1515,1516,1517,1518,1525,1526,1527,1528]
def kindSupport2_020 : List Nat := [1529,1530,1537,1538,1539,1540,1541,1542,1543,1544,1545,1558,1559,1560,1561,1562,1563,1564,1565,1566,1579,1580,1581,1582,1583,1584,1585,1586,1587,1600,1601,1602]
def kindSupport2_021 : List Nat := [1603,1604,1605,1606,1607,1608,1621,1622,1623,1624,1625,1626,1627,1628,1629,1642,1643,1644,1645,1646,1647,1648,1649,1650,1663,1664,1665,1666,1667,1668,1669,1670]
def kindSupport2_022 : List Nat := [1671,1684,1685,1686,1687,1688,1689,1690,1691,1692,1705,1706,1707,1708,1709,1710,1711,1712,1713,1714,1730,1731,1732,1733,1734,1735,1736,1737,1738,1751,1752,1753]
def kindSupport2_023 : List Nat := [1754,1755,1756,1757,1758,1759,1772,1773,1774,1775,1776,1777,1778,1779,1780,1793,1794,1795,1796,1797,1798,1799,1800,1801,1814,1815,1816,1817,1818,1819,1820,1821]
def kindSupport2_024 : List Nat := [1822,1823,1839,1840,1841,1842,1843,1844,1845,1846,1847,1848]
def kindSupport2_code : Nat := 0x1ce07371cd87351cd07331cc87311cc072f1c7c71e1c7471c1c6c71a1c647181c5c7161c247081c1c7061c147041c0c7021c046f41bcc6f21bc46f01bbc6ee1bb46ec1b7c6de1b746dc1b6c6da1b646d81b5c6ca1b246c81b1c6c61b146c41b0c6c21ac86b11ac06af1ab86ad1ab06ab1aa86a91a7069b1a686991a606971a586951a506871a186851a106831a086811a0067f19c867119c066f19b866d19b066b19a865d197065b1968659196065719586551920647191864519106431908641190063318c863118c062f18b862d18b062b187861d187061b186861918606171858609182060718186051810603180860117e85f917e05f717d85f517b85ed17b05eb17a85e917885e117805df17785dd17585d517505d317485d117285c917205c717185c516f85bd16f05bb16e85b916a45a8169c5a616945a4168c5a216845a0164c5921644590163c58e163458c162c57e15f457c15ec57a15e457815dc57615a4568159c5661594564158c5621584554154c5521544550153c54e153454c14fc53e14f453c14ec53a14e453814dc52a14a4528149c5261494524148c5221454514144c5121444510143c50e143450013fc4fe13f44fc13ec4fa13e44f813c44f013bc4ee13b44ec13944e4138c4e213844e013644d8135c4d613544d413344cc132c4ca13244c813044c012fc4be12f44bc12d44b412cc4b212c44b0128c4a212844a0127c49e127449c126c48e123448c122c48a1224488121c48611e447811dc47611d447411cc47211c4464118c4621184460117c45e117445c1154454114c45211444501124448111c446111444410f443c10ec43a10e443810c443010bc42e10b442c1094424108c42210844201064418105c41610544141010403100840110003ff0ff83fd0ff03fb0fb83ed0fb03eb0fa83e90fa03e70f983d90f603d70f583d50f503d30f483d10f103c30f083c10f003bf0ef83bd0ef03af0eb83ad0eb03ab0ea83a90ea03a70e683990e603970e583950e503930e483850e103830e083810e0037f0df837d0dc036f0db836d0db036b0da83690da035b0d683590d603570d583550d503530d3034b0d283490d203470d0033f0cf833d0cf033b0cd03330cc83310cc032f0ca03270c983250c903230c7031b0c683190c603170c4030f0c3830d0c3030b0bf82fd0bf02fb0be82f90be02f70bd82e90ba02e70b982e50b902e30b882e10b502d30b482d10b402cf0b382cd0b302bf0af82bd0af02bb0ae82b90ae02b70ac02af0ab82ad0ab02ab0a902a30a882a10a8029f0a602970a582950a502930a3028b0a282890a202870a0027f09f827d09f027b09d027309c827109c026f097c25e097425c096c25a0964258095c2560924248091c2460914244090c242090423408cc23208c423008bc22e08b422c087c21e087421c086c21a0864218085c20a0824208081c2060814204080c20207d41f407cc1f207c41f007bc1ee07b41e0077c1de07741dc076c1da07641d8072c1ca07241c8071c1c607141c4070c1b606d41b406cc1b206c41b006bc1ae069c1a606941a4068c1a2066c19a0664198065c196063c18e063418c062c18a060c182060418005fc17e05dc17605d417405cc17205ac16a05a4168059c1660564158055c1560554154054c1520544144050c142050414004fc13e04f413c04bc12e04b412c04ac12a04a4128049c11a0464118045c1160454114044c112042c10a0424108041c10603fc0fe03f40fc03ec0fa03cc0f203c40f003bc0ee039c0e603940e4038c0e2036c0da03640d8035c0d6033c0ce03340cc032c0ca030c0c203040c002fc0be02dc0b602d40b402cc0b202ac0aa02a40a8029c0a6027c09e027409c026c09a024c0920244090023c08e021c0860214084020c082
def kindSupport2_rest_000 : Nat := PackedRawNatGrowth.drop 0 kindSupport2_code
def kindSupport2_rest_001 : Nat := PackedRawNatGrowth.drop 448 kindSupport2_code
def kindSupport2_rest_002 : Nat := PackedRawNatGrowth.drop 896 kindSupport2_code
def kindSupport2_rest_003 : Nat := PackedRawNatGrowth.drop 1344 kindSupport2_code
def kindSupport2_rest_004 : Nat := PackedRawNatGrowth.drop 1792 kindSupport2_code
def kindSupport2_rest_005 : Nat := PackedRawNatGrowth.drop 2240 kindSupport2_code
def kindSupport2_rest_006 : Nat := PackedRawNatGrowth.drop 2688 kindSupport2_code
def kindSupport2_rest_007 : Nat := PackedRawNatGrowth.drop 3136 kindSupport2_code
def kindSupport2_rest_008 : Nat := PackedRawNatGrowth.drop 3584 kindSupport2_code
def kindSupport2_rest_009 : Nat := PackedRawNatGrowth.drop 4032 kindSupport2_code
def kindSupport2_rest_010 : Nat := PackedRawNatGrowth.drop 4480 kindSupport2_code
def kindSupport2_rest_011 : Nat := PackedRawNatGrowth.drop 4928 kindSupport2_code
def kindSupport2_rest_012 : Nat := PackedRawNatGrowth.drop 5376 kindSupport2_code
def kindSupport2_rest_013 : Nat := PackedRawNatGrowth.drop 5824 kindSupport2_code
def kindSupport2_rest_014 : Nat := PackedRawNatGrowth.drop 6272 kindSupport2_code
def kindSupport2_rest_015 : Nat := PackedRawNatGrowth.drop 6720 kindSupport2_code
def kindSupport2_rest_016 : Nat := PackedRawNatGrowth.drop 7168 kindSupport2_code
def kindSupport2_rest_017 : Nat := PackedRawNatGrowth.drop 7616 kindSupport2_code
def kindSupport2_rest_018 : Nat := PackedRawNatGrowth.drop 8064 kindSupport2_code
def kindSupport2_rest_019 : Nat := PackedRawNatGrowth.drop 8512 kindSupport2_code
def kindSupport2_rest_020 : Nat := PackedRawNatGrowth.drop 8960 kindSupport2_code
def kindSupport2_rest_021 : Nat := PackedRawNatGrowth.drop 9408 kindSupport2_code
def kindSupport2_rest_022 : Nat := PackedRawNatGrowth.drop 9856 kindSupport2_code
def kindSupport2_rest_023 : Nat := PackedRawNatGrowth.drop 10304 kindSupport2_code
def kindSupport2_rest_024 : Nat := PackedRawNatGrowth.drop 10752 kindSupport2_code
def kindSupport2_rest_025 : Nat := PackedRawNatGrowth.drop 10920 kindSupport2_code
def kindSupport2_suffix_025 : List Nat := []
def kindSupport2_suffix_024 : List Nat := kindSupport2_024 ++ kindSupport2_suffix_025
def kindSupport2_suffix_023 : List Nat := kindSupport2_023 ++ kindSupport2_suffix_024
def kindSupport2_suffix_022 : List Nat := kindSupport2_022 ++ kindSupport2_suffix_023
def kindSupport2_suffix_021 : List Nat := kindSupport2_021 ++ kindSupport2_suffix_022
def kindSupport2_suffix_020 : List Nat := kindSupport2_020 ++ kindSupport2_suffix_021
def kindSupport2_suffix_019 : List Nat := kindSupport2_019 ++ kindSupport2_suffix_020
def kindSupport2_suffix_018 : List Nat := kindSupport2_018 ++ kindSupport2_suffix_019
def kindSupport2_suffix_017 : List Nat := kindSupport2_017 ++ kindSupport2_suffix_018
def kindSupport2_suffix_016 : List Nat := kindSupport2_016 ++ kindSupport2_suffix_017
def kindSupport2_suffix_015 : List Nat := kindSupport2_015 ++ kindSupport2_suffix_016
def kindSupport2_suffix_014 : List Nat := kindSupport2_014 ++ kindSupport2_suffix_015
def kindSupport2_suffix_013 : List Nat := kindSupport2_013 ++ kindSupport2_suffix_014
def kindSupport2_suffix_012 : List Nat := kindSupport2_012 ++ kindSupport2_suffix_013
def kindSupport2_suffix_011 : List Nat := kindSupport2_011 ++ kindSupport2_suffix_012
def kindSupport2_suffix_010 : List Nat := kindSupport2_010 ++ kindSupport2_suffix_011
def kindSupport2_suffix_009 : List Nat := kindSupport2_009 ++ kindSupport2_suffix_010
def kindSupport2_suffix_008 : List Nat := kindSupport2_008 ++ kindSupport2_suffix_009
def kindSupport2_suffix_007 : List Nat := kindSupport2_007 ++ kindSupport2_suffix_008
def kindSupport2_suffix_006 : List Nat := kindSupport2_006 ++ kindSupport2_suffix_007
def kindSupport2_suffix_005 : List Nat := kindSupport2_005 ++ kindSupport2_suffix_006
def kindSupport2_suffix_004 : List Nat := kindSupport2_004 ++ kindSupport2_suffix_005
def kindSupport2_suffix_003 : List Nat := kindSupport2_003 ++ kindSupport2_suffix_004
def kindSupport2_suffix_002 : List Nat := kindSupport2_002 ++ kindSupport2_suffix_003
def kindSupport2_suffix_001 : List Nat := kindSupport2_001 ++ kindSupport2_suffix_002
def kindSupport2_suffix_000 : List Nat := kindSupport2_000 ++ kindSupport2_suffix_001
theorem kindSupport2_source : kindSupports 2 =
    (PackedRawNatGrowth.readList 14 780 kindSupport2_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
