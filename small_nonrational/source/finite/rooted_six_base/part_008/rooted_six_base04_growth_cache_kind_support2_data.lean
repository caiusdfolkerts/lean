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
def kindSupport2_000 : List Nat := [130,131,132,133,134,135,142,143,144,145,146,147,154,155,156,157,158,159,166,167,168,169,170,171,178,179,180,181,182,183,190,191]
def kindSupport2_001 : List Nat := [192,193,194,195,202,203,204,205,206,207,214,215,216,217,218,219,226,227,228,229,230,231,238,239,240,241,242,243,250,251,252,253]
def kindSupport2_002 : List Nat := [254,255,262,263,264,265,266,267,274,275,276,277,278,279,280,281,282,295,296,297,298,299,300,301,302,303,316,317,318,319,320,321]
def kindSupport2_003 : List Nat := [322,323,324,337,338,339,340,341,342,343,344,345,358,359,360,361,362,363,370,371,372,373,374,375,382,383,384,385,386,387,394,395]
def kindSupport2_004 : List Nat := [396,397,398,399,406,407,408,409,410,411,418,419,420,421,422,423,430,431,432,433,434,435,436,437,438,451,452,453,454,455,456,457]
def kindSupport2_005 : List Nat := [458,459,472,473,474,475,476,477,478,479,480,493,494,495,496,497,498,499,500,501,514,515,516,517,518,519,526,527,528,529,530,531]
def kindSupport2_006 : List Nat := [538,539,540,541,542,543,550,551,552,553,554,555,562,563,564,565,566,567,574,575,576,577,578,579,586,587,588,589,590,591,592,593]
def kindSupport2_007 : List Nat := [594,607,608,609,610,611,612,613,614,615,628,629,630,631,632,633,634,635,636,649,650,651,652,653,654,655,656,657,670,671,672,673]
def kindSupport2_008 : List Nat := [674,675,676,677,678,691,692,693,694,695,696,697,698,699,712,713,714,715,716,717,718,719,720,733,734,735,736,737,738,739,740,741]
def kindSupport2_009 : List Nat := [754,755,756,757,758,759,760,761,762,763,779,780,781,782,783,784,791,792,793,794,795,796,803,804,805,806,807,808,815,816,817,818]
def kindSupport2_010 : List Nat := [819,820,827,828,829,830,831,832,839,840,841,842,843,844,851,852,853,854,855,856,857,858,859,872,873,874,875,876,877,878,879,880]
def kindSupport2_011 : List Nat := [893,894,895,896,897,898,899,900,901,914,915,916,917,918,919,920,921,922,935,936,937,938,939,940,947,948,949,950,951,952,959,960]
def kindSupport2_012 : List Nat := [961,962,963,964,971,972,973,974,975,976,983,984,985,986,987,988,995,996,997,998,999,1000,1007,1008,1009,1010,1011,1012,1013,1014,1015,1028]
def kindSupport2_013 : List Nat := [1029,1030,1031,1032,1033,1034,1035,1036,1049,1050,1051,1052,1053,1054,1055,1056,1057,1070,1071,1072,1073,1074,1075,1076,1077,1078,1091,1092,1093,1094,1095,1096]
def kindSupport2_014 : List Nat := [1097,1098,1099,1112,1113,1114,1115,1116,1117,1118,1119,1120,1133,1134,1135,1136,1137,1138,1139,1140,1141,1154,1155,1156,1157,1158,1159,1160,1161,1162,1175,1176]
def kindSupport2_015 : List Nat := [1177,1178,1179,1180,1181,1182,1183,1184,1200,1201,1202,1203,1204,1205,1212,1213,1214,1215,1216,1217,1224,1225,1226,1227,1228,1229,1236,1237,1238,1239,1240,1241]
def kindSupport2_016 : List Nat := [1248,1249,1250,1251,1252,1253,1260,1261,1262,1263,1264,1265,1272,1273,1274,1275,1276,1277,1278,1279,1280,1293,1294,1295,1296,1297,1298,1299,1300,1301,1314,1315]
def kindSupport2_017 : List Nat := [1316,1317,1318,1319,1320,1321,1322,1335,1336,1337,1338,1339,1340,1341,1342,1343,1356,1357,1358,1359,1360,1361,1362,1363,1364,1377,1378,1379,1380,1381,1382,1383]
def kindSupport2_018 : List Nat := [1384,1385,1398,1399,1400,1401,1402,1403,1404,1405,1406,1419,1420,1421,1422,1423,1424,1425,1426,1427,1440,1441,1442,1443,1444,1445,1446,1447,1448,1449,1465,1466]
def kindSupport2_019 : List Nat := [1467,1468,1469,1470,1477,1478,1479,1480,1481,1482,1489,1490,1491,1492,1493,1494,1501,1502,1503,1504,1505,1506,1513,1514,1515,1516,1517,1518,1525,1526,1527,1528]
def kindSupport2_020 : List Nat := [1529,1530,1537,1538,1539,1540,1541,1542,1543,1544,1545,1558,1559,1560,1561,1562,1563,1564,1565,1566,1579,1580,1581,1582,1583,1584,1585,1586,1587,1600,1601,1602]
def kindSupport2_021 : List Nat := [1603,1604,1605,1606,1607,1608,1621,1622,1623,1624,1625,1626,1627,1628,1629,1642,1643,1644,1645,1646,1647,1648,1649,1650,1663,1664,1665,1666,1667,1668,1669,1670]
def kindSupport2_022 : List Nat := [1671,1684,1685,1686,1687,1688,1689,1690,1691,1692,1705,1706,1707,1708,1709,1710,1711,1712,1713,1714,1730,1731,1732,1733,1734,1735,1736,1737,1738,1751,1752,1753]
def kindSupport2_023 : List Nat := [1754,1755,1756,1757,1758,1759,1772,1773,1774,1775,1776,1777,1778,1779,1780,1793,1794,1795,1796,1797,1798,1799,1800,1801,1814,1815,1816,1817,1818,1819,1820,1821]
def kindSupport2_024 : List Nat := [1822,1823,1839,1840,1841,1842,1843,1844,1845,1846,1847,1848]
def kindSupport2_code : Nat := 0x73873773673573473373273173072f71f71e71d71c71b71a7197187177167097087077067057047037027016f46f36f26f16f06ef6ee6ed6ec6df6de6dd6dc6db6da6d96d86d76ca6c96c86c76c66c56c46c36c26b26b16b06af6ae6ad6ac6ab6aa6a969c69b69a69969869769669569468768668568468368268168067f67267167066f66e66d66c66b66a65d65c65b65a65965865765665564864764664564464364264164063363263163062f62e62d62c62b61e61d61c61b61a6196186176166096086076066056046036026015fa5f95f85f75f65f55ee5ed5ec5eb5ea5e95e25e15e05df5de5dd5d65d55d45d35d25d15ca5c95c85c75c65c55be5bd5bc5bb5ba5b95a95a85a75a65a55a45a35a25a15a059359259159058f58e58d58c58b57e57d57c57b57a57957857757656956856756656556456356256155455355255155054f54e54d54c53f53e53d53c53b53a53953853752a52952852752652552452352251551451351251151050f50e50d5004ff4fe4fd4fc4fb4fa4f94f84f14f04ef4ee4ed4ec4e54e44e34e24e14e04d94d84d74d64d54d44cd4cc4cb4ca4c94c84c14c04bf4be4bd4bc4b54b44b34b24b14b04a049f49e49d49c49b49a49949849748a48948848748648548448348247547447347247147046f46e46d46045f45e45d45c45b45a45945844b44a44944844744644544444343643543443343243143042f42e42142041f41e41d41c41b41a41940c40b40a4094084074064054043f73f63f53f43f33f23f13f03ef3e83e73e63e53e43e33dc3db3da3d93d83d73d03cf3ce3cd3cc3cb3c43c33c23c13c03bf3b83b73b63b53b43b33ac3ab3aa3a93a83a739a39939839739639539439339238538438338238138037f37e37d37036f36e36d36c36b36a36936835b35a35935835735635535435334c34b34a34934834734033f33e33d33c33b33433333233133032f32832732632532432331c31b31a31931831731030f30e30d30c30b2fb2fa2f92f82f72f62f52f42f32f22e52e42e32e22e12e02df2de2dd2d02cf2ce2cd2cc2cb2ca2c92c82bb2ba2b92b82b72b62b52b42b32a62a52a42a32a22a12a029f29e29129028f28e28d28c28b28a28927c27b27a27927827727627527426726626526426326226126025f25225125024f24e24d24c24b24a24324224124023f23e23723623523423323222b22a22922822722621f21e21d21c21b21a21321221121020f20e2072062052042032021f51f41f31f21f11f01ef1ee1ed1e01df1de1dd1dc1db1da1d91d81cb1ca1c91c81c71c61c51c41c31b61b51b41b31b21b11b01af1ae1a71a61a51a41a31a219b19a19919819719618f18e18d18c18b18a18318218118017f17e17717617517417317216b16a16916816716615915815715615515415315215114414314214114013f13e13d13c12f12e12d12c12b12a12912812711a11911811711611511411311210b10a1091081071060ff0fe0fd0fc0fb0fa0f30f20f10f00ef0ee0e70e60e50e40e30e20db0da0d90d80d70d60cf0ce0cd0cc0cb0ca0c30c20c10c00bf0be0b70b60b50b40b30b20ab0aa0a90a80a70a609f09e09d09c09b09a09309209109008f08e087086085084083082
def kindSupport2_rest_000 : Nat := PackedRawNatGrowth.drop 0 kindSupport2_code
def kindSupport2_rest_001 : Nat := PackedRawNatGrowth.drop 384 kindSupport2_code
def kindSupport2_rest_002 : Nat := PackedRawNatGrowth.drop 768 kindSupport2_code
def kindSupport2_rest_003 : Nat := PackedRawNatGrowth.drop 1152 kindSupport2_code
def kindSupport2_rest_004 : Nat := PackedRawNatGrowth.drop 1536 kindSupport2_code
def kindSupport2_rest_005 : Nat := PackedRawNatGrowth.drop 1920 kindSupport2_code
def kindSupport2_rest_006 : Nat := PackedRawNatGrowth.drop 2304 kindSupport2_code
def kindSupport2_rest_007 : Nat := PackedRawNatGrowth.drop 2688 kindSupport2_code
def kindSupport2_rest_008 : Nat := PackedRawNatGrowth.drop 3072 kindSupport2_code
def kindSupport2_rest_009 : Nat := PackedRawNatGrowth.drop 3456 kindSupport2_code
def kindSupport2_rest_010 : Nat := PackedRawNatGrowth.drop 3840 kindSupport2_code
def kindSupport2_rest_011 : Nat := PackedRawNatGrowth.drop 4224 kindSupport2_code
def kindSupport2_rest_012 : Nat := PackedRawNatGrowth.drop 4608 kindSupport2_code
def kindSupport2_rest_013 : Nat := PackedRawNatGrowth.drop 4992 kindSupport2_code
def kindSupport2_rest_014 : Nat := PackedRawNatGrowth.drop 5376 kindSupport2_code
def kindSupport2_rest_015 : Nat := PackedRawNatGrowth.drop 5760 kindSupport2_code
def kindSupport2_rest_016 : Nat := PackedRawNatGrowth.drop 6144 kindSupport2_code
def kindSupport2_rest_017 : Nat := PackedRawNatGrowth.drop 6528 kindSupport2_code
def kindSupport2_rest_018 : Nat := PackedRawNatGrowth.drop 6912 kindSupport2_code
def kindSupport2_rest_019 : Nat := PackedRawNatGrowth.drop 7296 kindSupport2_code
def kindSupport2_rest_020 : Nat := PackedRawNatGrowth.drop 7680 kindSupport2_code
def kindSupport2_rest_021 : Nat := PackedRawNatGrowth.drop 8064 kindSupport2_code
def kindSupport2_rest_022 : Nat := PackedRawNatGrowth.drop 8448 kindSupport2_code
def kindSupport2_rest_023 : Nat := PackedRawNatGrowth.drop 8832 kindSupport2_code
def kindSupport2_rest_024 : Nat := PackedRawNatGrowth.drop 9216 kindSupport2_code
def kindSupport2_rest_025 : Nat := PackedRawNatGrowth.drop 9360 kindSupport2_code
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
    (PackedRawNatGrowth.readList 12 780 kindSupport2_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase04
