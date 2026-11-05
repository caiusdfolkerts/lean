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
def kindSupport2_000 : List Nat := [116,117,118,119,120,121,128,129,130,131,132,133,140,141,142,143,144,145,152,153,154,155,156,157,164,165,166,167,168,169,176,177]
def kindSupport2_001 : List Nat := [178,179,180,181,188,189,190,191,192,193,200,201,202,203,204,205,212,213,214,215,216,217,224,225,226,227,228,229,236,237,238,239]
def kindSupport2_002 : List Nat := [240,241,248,249,250,251,252,253,260,261,262,263,264,265,266,267,268,281,282,283,284,285,286,287,288,289,302,303,304,305,306,307]
def kindSupport2_003 : List Nat := [308,309,310,323,324,325,326,327,328,329,330,331,344,345,346,347,348,349,356,357,358,359,360,361,368,369,370,371,372,373,380,381]
def kindSupport2_004 : List Nat := [382,383,384,385,392,393,394,395,396,397,404,405,406,407,408,409,416,417,418,419,420,421,422,423,424,437,438,439,440,441,442,443]
def kindSupport2_005 : List Nat := [444,445,458,459,460,461,462,463,464,465,466,479,480,481,482,483,484,485,486,487,500,501,502,503,504,505,506,507,508,521,522,523]
def kindSupport2_006 : List Nat := [524,525,526,527,528,529,542,543,544,545,546,547,548,549,550,563,564,565,566,567,568,569,570,571,584,585,586,587,588,589,590,591]
def kindSupport2_007 : List Nat := [592,593,609,610,611,612,613,614,621,622,623,624,625,626,633,634,635,636,637,638,645,646,647,648,649,650,657,658,659,660,661,662]
def kindSupport2_008 : List Nat := [669,670,671,672,673,674,681,682,683,684,685,686,687,688,689,702,703,704,705,706,707,708,709,710,723,724,725,726,727,728,729,730]
def kindSupport2_009 : List Nat := [731,744,745,746,747,748,749,750,751,752,769,770,771,772,773,774,775,776,777,790,791,792,793,794,795,796,797,798,811,812,813,814]
def kindSupport2_010 : List Nat := [815,816,817,818,819,832,833,834,835,836,837,838,839,840,853,854,855,856,857,858,859,860,861,874,875,876,877,878,879,880,881,882]
def kindSupport2_011 : List Nat := [895,896,897,898,899,900,901,902,903,916,917,918,919,920,921,922,923,924,937,938,939,940,941,942,943,944,945,946,962,963,964,965]
def kindSupport2_012 : List Nat := [966,967,974,975,976,977,978,979,986,987,988,989,990,991,998,999,1000,1001,1002,1003,1010,1011,1012,1013,1014,1015,1022,1023,1024,1025,1026,1027]
def kindSupport2_013 : List Nat := [1034,1035,1036,1037,1038,1039,1040,1041,1042,1055,1056,1057,1058,1059,1060,1061,1062,1063,1076,1077,1078,1079,1080,1081,1082,1083,1084,1097,1098,1099,1100,1101]
def kindSupport2_014 : List Nat := [1102,1103,1104,1105,1118,1119,1120,1121,1122,1123,1130,1131,1132,1133,1134,1135,1142,1143,1144,1145,1146,1147,1154,1155,1156,1157,1158,1159,1166,1167,1168,1169]
def kindSupport2_015 : List Nat := [1170,1171,1178,1179,1180,1181,1182,1183,1190,1191,1192,1193,1194,1195,1196,1197,1198,1211,1212,1213,1214,1215,1216,1217,1218,1219,1232,1233,1234,1235,1236,1237]
def kindSupport2_016 : List Nat := [1238,1239,1240,1253,1254,1255,1256,1257,1258,1259,1260,1261,1274,1275,1276,1277,1278,1279,1280,1281,1282,1295,1296,1297,1298,1299,1300,1301,1302,1303,1316,1317]
def kindSupport2_017 : List Nat := [1318,1319,1320,1321,1322,1323,1324,1337,1338,1339,1340,1341,1342,1343,1344,1345,1358,1359,1360,1361,1362,1363,1364,1365,1366,1367,1383,1384,1385,1386,1387,1388]
def kindSupport2_018 : List Nat := [1389,1390,1391,1404,1405,1406,1407,1408,1409,1410,1411,1412,1425,1426,1427,1428,1429,1430,1431,1432,1433,1446,1447,1448,1449,1450,1451,1452,1453,1454,1467,1468]
def kindSupport2_019 : List Nat := [1469,1470,1471,1472,1473,1474,1475,1476,1492,1493,1494,1495,1496,1497,1498,1499,1500,1513,1514,1515,1516,1517,1518,1519,1520,1521,1534,1535,1536,1537,1538,1539]
def kindSupport2_020 : List Nat := [1540,1541,1542,1555,1556,1557,1558,1559,1560,1561,1562,1563,1576,1577,1578,1579,1580,1581,1582,1583,1584,1585,1601,1602,1603,1604,1605,1606,1607,1608,1609,1610]
def kindSupport2_code : Nat := 0x64a64964864764664564464364264163163062f62e62d62c62b62a62962861b61a6196186176166156146136066056046036026016005ff5fe5f15f05ef5ee5ed5ec5eb5ea5e95dc5db5da5d95d85d75d65d55d45c45c35c25c15c05bf5be5bd5bc5bb5ae5ad5ac5ab5aa5a95a85a75a659959859759659559459359259158458358258158057f57e57d57c56f56e56d56c56b56a56956856755755655555455355255155054f54e54154053f53e53d53c53b53a53952c52b52a52952852752652552451751651551451351251151050f5025015004ff4fe4fd4fc4fb4fa4ed4ec4eb4ea4e94e84e74e64e54d84d74d64d54d44d34d24d14d04c34c24c14c04bf4be4bd4bc4bb4ae4ad4ac4ab4aa4a94a84a74a649f49e49d49c49b49a49349249149048f48e48748648548448348247b47a47947847747646f46e46d46c46b46a46346246146045f45e45145044f44e44d44c44b44a44943c43b43a43943843743643543442742642542442342242142041f41241141040f40e40d40c40b40a4034024014003ff3fe3f73f63f53f43f33f23eb3ea3e93e83e73e63df3de3dd3dc3db3da3d33d23d13d03cf3ce3c73c63c53c43c33c23b23b13b03af3ae3ad3ac3ab3aa3a939c39b39a39939839739639539438738638538438338238138037f37237137036f36e36d36c36b36a35d35c35b35a35935835735635534834734634534434334234134033333233133032f32e32d32c32b31e31d31c31b31a3193183173163093083073063053043033023012f02ef2ee2ed2ec2eb2ea2e92e82db2da2d92d82d72d62d52d42d32c62c52c42c32c22c12c02bf2be2b12b02af2ae2ad2ac2ab2aa2a92a22a12a029f29e29d29629529429329229128a28928828728628527e27d27c27b27a27927227127026f26e26d26626526426326226125125024f24e24d24c24b24a24924823b23a23923823723623523423322622522422322222122021f21e21121020f20e20d20c20b20a2091fc1fb1fa1f91f81f71f61f51f41e71e61e51e41e31e21e11e01df1d21d11d01cf1ce1cd1cc1cb1ca1bd1bc1bb1ba1b91b81b71b61b51a81a71a61a51a41a31a21a11a019919819719619519418d18c18b18a18918818118017f17e17d17c17517417317217117016916816716616516415d15c15b15a15915814b14a14914814714614514414313613513413313213113012f12e12112011f11e11d11c11b11a11910c10b10a1091081071061051040fd0fc0fb0fa0f90f80f10f00ef0ee0ed0ec0e50e40e30e20e10e00d90d80d70d60d50d40cd0cc0cb0ca0c90c80c10c00bf0be0bd0bc0b50b40b30b20b10b00a90a80a70a60a50a409d09c09b09a09909809109008f08e08d08c085084083082081080079078077076075074
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra01
