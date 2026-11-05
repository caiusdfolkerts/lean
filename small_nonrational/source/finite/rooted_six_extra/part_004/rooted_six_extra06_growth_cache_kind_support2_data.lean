module
prelude
public import RootedSixExtra06GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra06
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def kindSupport2_000 : List Nat := [106,107,108,109,110,111,118,119,120,121,122,123,130,131,132,133,134,135,142,143,144,145,146,147,154,155,156,157,158,159,166,167]
def kindSupport2_001 : List Nat := [168,169,170,171,178,179,180,181,182,183,184,185,186,199,200,201,202,203,204,205,206,207,220,221,222,223,224,225,226,227,228,241]
def kindSupport2_002 : List Nat := [242,243,244,245,246,247,248,249,262,263,264,265,266,267,274,275,276,277,278,279,286,287,288,289,290,291,298,299,300,301,302,303]
def kindSupport2_003 : List Nat := [310,311,312,313,314,315,322,323,324,325,326,327,334,335,336,337,338,339,340,341,342,355,356,357,358,359,360,361,362,363,376,377]
def kindSupport2_004 : List Nat := [378,379,380,381,382,383,384,397,398,399,400,401,402,403,404,405,418,419,420,421,422,423,424,425,426,439,440,441,442,443,444,445]
def kindSupport2_005 : List Nat := [446,447,460,461,462,463,464,465,466,467,468,481,482,483,484,485,486,487,488,489,502,503,504,505,506,507,508,509,510,511,527,528]
def kindSupport2_006 : List Nat := [529,530,531,532,539,540,541,542,543,544,551,552,553,554,555,556,563,564,565,566,567,568,575,576,577,578,579,580,587,588,589,590]
def kindSupport2_007 : List Nat := [591,592,599,600,601,602,603,604,605,606,607,620,621,622,623,624,625,626,627,628,641,642,643,644,645,646,647,648,649,662,663,664]
def kindSupport2_008 : List Nat := [665,666,667,668,669,670,683,684,685,686,687,688,689,690,691,704,705,706,707,708,709,710,711,712,725,726,727,728,729,730,731,732]
def kindSupport2_009 : List Nat := [733,746,747,748,749,750,751,752,753,754,767,768,769,770,771,772,773,774,775,776,792,793,794,795,796,797,804,805,806,807,808,809]
def kindSupport2_010 : List Nat := [816,817,818,819,820,821,828,829,830,831,832,833,840,841,842,843,844,845,852,853,854,855,856,857,864,865,866,867,868,869,870,871]
def kindSupport2_011 : List Nat := [872,885,886,887,888,889,890,891,892,893,906,907,908,909,910,911,912,913,914,927,928,929,930,931,932,933,934,935,948,949,950,951]
def kindSupport2_012 : List Nat := [952,953,960,961,962,963,964,965,972,973,974,975,976,977,984,985,986,987,988,989,996,997,998,999,1000,1001,1008,1009,1010,1011,1012,1013]
def kindSupport2_013 : List Nat := [1020,1021,1022,1023,1024,1025,1026,1027,1028,1041,1042,1043,1044,1045,1046,1047,1048,1049,1062,1063,1064,1065,1066,1067,1068,1069,1070,1083,1084,1085,1086,1087]
def kindSupport2_014 : List Nat := [1088,1089,1090,1091,1104,1105,1106,1107,1108,1109,1110,1111,1112,1125,1126,1127,1128,1129,1130,1131,1132,1133,1146,1147,1148,1149,1150,1151,1152,1153,1154,1167]
def kindSupport2_015 : List Nat := [1168,1169,1170,1171,1172,1173,1174,1175,1188,1189,1190,1191,1192,1193,1194,1195,1196,1197,1213,1214,1215,1216,1217,1218,1219,1220,1221,1234,1235,1236,1237,1238]
def kindSupport2_016 : List Nat := [1239,1240,1241,1242,1255,1256,1257,1258,1259,1260,1261,1262,1263,1276,1277,1278,1279,1280,1281,1282,1283,1284,1297,1298,1299,1300,1301,1302,1303,1304,1305,1306]
def kindSupport2_017 : List Nat := [1322,1323,1324,1325,1326,1327,1328,1329,1330,1343,1344,1345,1346,1347,1348,1349,1350,1351,1364,1365,1366,1367,1368,1369,1370,1371,1372,1385,1386,1387,1388,1389]
def kindSupport2_018 : List Nat := [1390,1391,1392,1393,1406,1407,1408,1409,1410,1411,1412,1413,1414,1415,1431,1432,1433,1434,1435,1436,1437,1438,1439,1440]
def kindSupport2_code : Nat := 0x5a059f59e59d59c59b59a59959859758758658558458358258158057f57e57157056f56e56d56c56b56a56955c55b55a55955855755655555454754654554454354254154053f53253153052f52e52d52c52b52a51a5195185175165155145135125115045035025015004ff4fe4fd4fc4ef4ee4ed4ec4eb4ea4e94e84e74da4d94d84d74d64d54d44d34d24c54c44c34c24c14c04bf4be4bd4ad4ac4ab4aa4a94a84a74a64a54a449749649549449349249149048f48248148047f47e47d47c47b47a46d46c46b46a46946846746646545845745645545445345245145044344244144043f43e43d43c43b42e42d42c42b42a4294284274264194184174164154144134124114044034024014003ff3fe3fd3fc3f53f43f33f23f13f03e93e83e73e63e53e43dd3dc3db3da3d93d83d13d03cf3ce3cd3cc3c53c43c33c23c13c03b93b83b73b63b53b43a73a63a53a43a33a23a13a039f39239139038f38e38d38c38b38a37d37c37b37a37937837737637536836736636536436336236136035935835735635535434d34c34b34a34934834134033f33e33d33c33533433333233133032932832732632532431d31c31b31a3193183083073063053043033023013002ff2f22f12f02ef2ee2ed2ec2eb2ea2dd2dc2db2da2d92d82d72d62d52c82c72c62c52c42c32c22c12c02b32b22b12b02af2ae2ad2ac2ab29e29d29c29b29a29929829729628928828728628528428328228127427327227127026f26e26d26c25f25e25d25c25b25a25925825725024f24e24d24c24b24424324224124023f23823723623523423322c22b22a22922822722021f21e21d21c21b21421321221121020f1ff1fe1fd1fc1fb1fa1f91f81f71f61e91e81e71e61e51e41e31e21e11d41d31d21d11d01cf1ce1cd1cc1bf1be1bd1bc1bb1ba1b91b81b71aa1a91a81a71a61a51a41a31a219519419319219119018f18e18d18017f17e17d17c17b17a17917816b16a16916816716616516416315615515415315215115014f14e14714614514414314213b13a13913813713612f12e12d12c12b12a12312212112011f11e11711611511411311210b10a1091081071060f90f80f70f60f50f40f30f20f10e40e30e20e10e00df0de0dd0dc0cf0ce0cd0cc0cb0ca0c90c80c70ba0b90b80b70b60b50b40b30b20ab0aa0a90a80a70a609f09e09d09c09b09a09309209109008f08e08708608508408308207b07a07907807707606f06e06d06c06b06a
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
def kindSupport2_rest_019 : Nat := PackedRawNatGrowth.drop 7200 kindSupport2_code
def kindSupport2_suffix_019 : List Nat := []
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
    (PackedRawNatGrowth.readList 12 600 kindSupport2_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra06
