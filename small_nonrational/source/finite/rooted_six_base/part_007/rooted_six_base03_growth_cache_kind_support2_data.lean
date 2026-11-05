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
def kindSupport2_code : Nat := 0x3251924c906473231914c886433211904c6263031798b8c5a62c31598a8c5262830d9868c3261830b9858c2a6143099818c0a6043019808c026002ff97f8be25f02f797b8bda5ec2f597a8bd25dc2ed9768bb25d82eb9758baa5d42e2170cb845c12e016fcb7c5bd2de16ecb5c5ad2d616acb545a92d4169cb4c5992cc165cb2c5952ca164cb245912c2160cb045812c015fcafc57d2be15bcadc56d2b615acad45692b4159cab45592ac155caac5552aa154caa45452a2150ca845412a014fca7c53d29814bca5c52d29614aca54529294146ca3451928c145ca2c51528a144ca1850b2851424a1050728013fc9fc4fd27e13ec9e84f327913c49e04ef274139c9cc4e5272138c9b84db26d13649b04d7268133c99c4cd266132c9764ba25c92e096e4b625a92d09664b225292909464a2250928093e49e24e924091e48e246923091648a24492208f647a23c91e08ee47623a91d08e646623291908c646223091808be45e228914089e44e226913089644a22490f087643a21c90e086e43621a90d084e4262129090846422210908083e412208904081e40e206903081640a20190088024001ff8ff87ee3f61fa8fd07e63f21f58fa87d23e81f38f987be3de1ee8f707b63da1e98f487a23d01e78f3878e3c61e28f107863c21d90ec47603af1d70eb47583ab1d50ea473839b1cd0e647303971cb0e547283871c30e147083831c10e0470037f1b90dc46e036f1b70db46d836b1b50d746b835b1ad0d646b03571ab0d546903471a30d146883431a10d046803331990cc466032f1970cb465832b18f0c7463831b18d0c6463031718b0c246103071830c146083031810c045f42f917c0bdc5ec2f51770bb45d82eb1750ba45c42e11700b7c5bc2dd16b0b545a82d31690b445942c91640b1c58c2c515f0af45782bb15d0ae45582ab1550aa45502a71530a9454829714b0a545282931490a4452028f1410a0450027f13f09f44f827b13d09b44d826b13509a44d026713309944bc25d12e096c4b425912909444a024f127093448c245122090c48424111d08e447023711b08d445c22d11608ac454229111088444021f10f087441a20c1058828412208103881840a2040fb87d83ea1f40f987c83e21f00f787883c21e00ef87783ba1dc0ed876839a1cc0e587283921c80e3871838a1b80db86d836a1b40d986c83621b00d186883421a00cf867833a19c0cd863831a18c0c586283121880c386182f21780bb85d82ea1740b985c82e21640b185882c21600af85782ba15c0a585282921480a3851828a1440a184d826a13409984c826213009784b824212008f847823a11c08d846823210c0858428212108083841820a10407e83f01f60fa07c83e01e20f007783b81da0ec07283901c60e207083801b20d806b83581aa0d406683301960ca06483201820c005f82f817a0bc05a82d01660b205882c01520a8053829814a0a404e827013609a04c8260122090047823811a08c042821010608204082000f207803b81d80ea074
def kindSupport2_rest_000 : Nat := PackedRawNatGrowth.drop 0 kindSupport2_code
def kindSupport2_rest_001 : Nat := PackedRawNatGrowth.drop 416 kindSupport2_code
def kindSupport2_rest_002 : Nat := PackedRawNatGrowth.drop 832 kindSupport2_code
def kindSupport2_rest_003 : Nat := PackedRawNatGrowth.drop 1248 kindSupport2_code
def kindSupport2_rest_004 : Nat := PackedRawNatGrowth.drop 1664 kindSupport2_code
def kindSupport2_rest_005 : Nat := PackedRawNatGrowth.drop 2080 kindSupport2_code
def kindSupport2_rest_006 : Nat := PackedRawNatGrowth.drop 2496 kindSupport2_code
def kindSupport2_rest_007 : Nat := PackedRawNatGrowth.drop 2912 kindSupport2_code
def kindSupport2_rest_008 : Nat := PackedRawNatGrowth.drop 3328 kindSupport2_code
def kindSupport2_rest_009 : Nat := PackedRawNatGrowth.drop 3744 kindSupport2_code
def kindSupport2_rest_010 : Nat := PackedRawNatGrowth.drop 4160 kindSupport2_code
def kindSupport2_rest_011 : Nat := PackedRawNatGrowth.drop 4576 kindSupport2_code
def kindSupport2_rest_012 : Nat := PackedRawNatGrowth.drop 4992 kindSupport2_code
def kindSupport2_rest_013 : Nat := PackedRawNatGrowth.drop 5408 kindSupport2_code
def kindSupport2_rest_014 : Nat := PackedRawNatGrowth.drop 5824 kindSupport2_code
def kindSupport2_rest_015 : Nat := PackedRawNatGrowth.drop 6240 kindSupport2_code
def kindSupport2_rest_016 : Nat := PackedRawNatGrowth.drop 6656 kindSupport2_code
def kindSupport2_rest_017 : Nat := PackedRawNatGrowth.drop 7072 kindSupport2_code
def kindSupport2_rest_018 : Nat := PackedRawNatGrowth.drop 7488 kindSupport2_code
def kindSupport2_rest_019 : Nat := PackedRawNatGrowth.drop 7904 kindSupport2_code
def kindSupport2_rest_020 : Nat := PackedRawNatGrowth.drop 8320 kindSupport2_code
def kindSupport2_rest_021 : Nat := PackedRawNatGrowth.drop 8736 kindSupport2_code
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
    (PackedRawNatGrowth.readList 13 672 kindSupport2_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase03
