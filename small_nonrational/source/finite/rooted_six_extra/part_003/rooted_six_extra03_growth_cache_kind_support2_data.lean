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
def kindSupport2_000 : List Nat := [116,117,118,119,120,121,128,129,130,131,132,133,140,141,142,143,144,145,152,153,154,155,156,157,164,165,166,167,168,169,176,177]
def kindSupport2_001 : List Nat := [178,179,180,181,188,189,190,191,192,193,200,201,202,203,204,205,212,213,214,215,216,217,224,225,226,227,228,229,236,237,238,239]
def kindSupport2_002 : List Nat := [240,241,248,249,250,251,252,253,260,261,262,263,264,265,266,267,268,281,282,283,284,285,286,287,288,289,302,303,304,305,306,307]
def kindSupport2_003 : List Nat := [308,309,310,323,324,325,326,327,328,329,330,331,348,349,350,351,352,353,354,355,356,369,370,371,372,373,374,375,376,377,390,391]
def kindSupport2_004 : List Nat := [392,393,394,395,396,397,398,411,412,413,414,415,416,417,418,419,432,433,434,435,436,437,438,439,440,453,454,455,456,457,458,459]
def kindSupport2_005 : List Nat := [460,461,474,475,476,477,478,479,480,481,482,495,496,497,498,499,500,501,502,503,516,517,518,519,520,521,522,523,524,525,541,542]
def kindSupport2_006 : List Nat := [543,544,545,546,553,554,555,556,557,558,565,566,567,568,569,570,577,578,579,580,581,582,589,590,591,592,593,594,601,602,603,604]
def kindSupport2_007 : List Nat := [605,606,613,614,615,616,617,618,619,620,621,634,635,636,637,638,639,640,641,642,655,656,657,658,659,660,661,662,663,676,677,678]
def kindSupport2_008 : List Nat := [679,680,681,682,683,684,697,698,699,700,701,702,709,710,711,712,713,714,721,722,723,724,725,726,733,734,735,736,737,738,745,746]
def kindSupport2_009 : List Nat := [747,748,749,750,757,758,759,760,761,762,769,770,771,772,773,774,775,776,777,790,791,792,793,794,795,796,797,798,811,812,813,814]
def kindSupport2_010 : List Nat := [815,816,817,818,819,832,833,834,835,836,837,838,839,840,853,854,855,856,857,858,859,860,861,874,875,876,877,878,879,880,881,882]
def kindSupport2_011 : List Nat := [895,896,897,898,899,900,901,902,903,916,917,918,919,920,921,922,923,924,937,938,939,940,941,942,943,944,945,946,962,963,964,965]
def kindSupport2_012 : List Nat := [966,967,974,975,976,977,978,979,986,987,988,989,990,991,998,999,1000,1001,1002,1003,1010,1011,1012,1013,1014,1015,1022,1023,1024,1025,1026,1027]
def kindSupport2_013 : List Nat := [1034,1035,1036,1037,1038,1039,1040,1041,1042,1055,1056,1057,1058,1059,1060,1061,1062,1063,1076,1077,1078,1079,1080,1081,1082,1083,1084,1097,1098,1099,1100,1101]
def kindSupport2_014 : List Nat := [1102,1103,1104,1105,1118,1119,1120,1121,1122,1123,1124,1125,1126,1139,1140,1141,1142,1143,1144,1145,1146,1147,1160,1161,1162,1163,1164,1165,1166,1167,1168,1181]
def kindSupport2_015 : List Nat := [1182,1183,1184,1185,1186,1187,1188,1189,1202,1203,1204,1205,1206,1207,1208,1209,1210,1211,1227,1228,1229,1230,1231,1232,1239,1240,1241,1242,1243,1244,1251,1252]
def kindSupport2_016 : List Nat := [1253,1254,1255,1256,1263,1264,1265,1266,1267,1268,1275,1276,1277,1278,1279,1280,1287,1288,1289,1290,1291,1292,1299,1300,1301,1302,1303,1304,1305,1306,1307,1320]
def kindSupport2_017 : List Nat := [1321,1322,1323,1324,1325,1326,1327,1328,1341,1342,1343,1344,1345,1346,1347,1348,1349,1362,1363,1364,1365,1366,1367,1368,1369,1370,1383,1384,1385,1386,1387,1388]
def kindSupport2_018 : List Nat := [1389,1390,1391,1404,1405,1406,1407,1408,1409,1410,1411,1412,1425,1426,1427,1428,1429,1430,1431,1432,1433,1446,1447,1448,1449,1450,1451,1452,1453,1454,1467,1468]
def kindSupport2_019 : List Nat := [1469,1470,1471,1472,1473,1474,1475,1476,1492,1493,1494,1495,1496,1497,1498,1499,1500,1513,1514,1515,1516,1517,1518,1519,1520,1521,1534,1535,1536,1537,1538,1539]
def kindSupport2_020 : List Nat := [1540,1541,1542,1555,1556,1557,1558,1559,1560,1561,1562,1563,1576,1577,1578,1579,1580,1581,1582,1583,1584,1585,1601,1602,1603,1604,1605,1606,1607,1608,1609,1610]
def kindSupport2_code : Nat := 0x64a64964864764664564464364264163163062f62e62d62c62b62a62962861b61a6196186176166156146136066056046036026016005ff5fe5f15f05ef5ee5ed5ec5eb5ea5e95dc5db5da5d95d85d75d65d55d45c45c35c25c15c05bf5be5bd5bc5bb5ae5ad5ac5ab5aa5a95a85a75a659959859759659559459359259158458358258158057f57e57d57c56f56e56d56c56b56a56956856755a55955855755655555455355254554454354254154053f53e53d53052f52e52d52c52b52a52952851b51a51951851751651551451350c50b50a5095085075004ff4fe4fd4fc4fb4f44f34f24f14f04ef4e84e74e64e54e44e34dc4db4da4d94d84d74d04cf4ce4cd4cc4cb4bb4ba4b94b84b74b64b54b44b34b24a54a44a34a24a14a049f49e49d49048f48e48d48c48b48a48948847b47a47947847747647547447346646546446346246146045f45e45145044f44e44d44c44b44a44943c43b43a43943843743643543442742642542442342242142041f41241141040f40e40d40c40b40a4034024014003ff3fe3f73f63f53f43f33f23eb3ea3e93e83e73e63df3de3dd3dc3db3da3d33d23d13d03cf3ce3c73c63c53c43c33c23b23b13b03af3ae3ad3ac3ab3aa3a939c39b39a39939839739639539438738638538438338238138037f37237137036f36e36d36c36b36a35d35c35b35a35935835735635534834734634534434334234134033333233133032f32e32d32c32b31e31d31c31b31a3193183173163093083073063053043033023012fa2f92f82f72f62f52ee2ed2ec2eb2ea2e92e22e12e02df2de2dd2d62d52d42d32d22d12ca2c92c82c72c62c52be2bd2bc2bb2ba2b92ac2ab2aa2a92a82a72a62a52a429729629529429329229129028f28228128027f27e27d27c27b27a26d26c26b26a26926826726626525e25d25c25b25a25925225125024f24e24d24624524424324224123a23923823723623522e22d22c22b22a22922222122021f21e21d20d20c20b20a2092082072062052041f71f61f51f41f31f21f11f01ef1e21e11e01df1de1dd1dc1db1da1cd1cc1cb1ca1c91c81c71c61c51b81b71b61b51b41b31b21b11b01a31a21a11a019f19e19d19c19b18e18d18c18b18a18918818718617917817717617517417317217116416316216116015f15e15d15c14b14a14914814714614514414313613513413313213113012f12e12112011f11e11d11c11b11a11910c10b10a1091081071061051040fd0fc0fb0fa0f90f80f10f00ef0ee0ed0ec0e50e40e30e20e10e00d90d80d70d60d50d40cd0cc0cb0ca0c90c80c10c00bf0be0bd0bc0b50b40b30b20b10b00a90a80a70a60a50a409d09c09b09a09909809109008f08e08d08c085084083082081080079078077076075074
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
def kindSupport2_suffix_021 : List Nat := []
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
    (PackedRawNatGrowth.readList 12 672 kindSupport2_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra03
