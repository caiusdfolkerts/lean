module
prelude
public import RootedSixExtra02GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def kindSupport2_000 : List Nat := [102,103,104,105,106,107,114,115,116,117,118,119,126,127,128,129,130,131,138,139,140,141,142,143,150,151,152,153,154,155,162,163]
def kindSupport2_001 : List Nat := [164,165,166,167,174,175,176,177,178,179,186,187,188,189,190,191,198,199,200,201,202,203,210,211,212,213,214,215,222,223,224,225]
def kindSupport2_002 : List Nat := [226,227,234,235,236,237,238,239,246,247,248,249,250,251,252,253,254,267,268,269,270,271,272,273,274,275,288,289,290,291,292,293]
def kindSupport2_003 : List Nat := [294,295,296,309,310,311,312,313,314,315,316,317,334,335,336,337,338,339,340,341,342,355,356,357,358,359,360,361,362,363,376,377]
def kindSupport2_004 : List Nat := [378,379,380,381,382,383,384,397,398,399,400,401,402,403,404,405,418,419,420,421,422,423,424,425,426,439,440,441,442,443,444,445]
def kindSupport2_005 : List Nat := [446,447,460,461,462,463,464,465,466,467,468,481,482,483,484,485,486,487,488,489,502,503,504,505,506,507,508,509,510,511,531,532]
def kindSupport2_006 : List Nat := [533,534,535,536,537,538,539,552,553,554,555,556,557,558,559,560,573,574,575,576,577,578,579,580,581,594,595,596,597,598,599,600]
def kindSupport2_007 : List Nat := [601,602,615,616,617,618,619,620,627,628,629,630,631,632,639,640,641,642,643,644,651,652,653,654,655,656,663,664,665,666,667,668]
def kindSupport2_008 : List Nat := [675,676,677,678,679,680,687,688,689,690,691,692,693,694,695,708,709,710,711,712,713,714,715,716,729,730,731,732,733,734,735,736]
def kindSupport2_009 : List Nat := [737,750,751,752,753,754,755,756,757,758,771,772,773,774,775,776,777,778,779,792,793,794,795,796,797,798,799,800,813,814,815,816]
def kindSupport2_010 : List Nat := [817,818,819,820,821,834,835,836,837,838,839,840,841,842,855,856,857,858,859,860,861,862,863,864,880,881,882,883,884,885,886,887]
def kindSupport2_011 : List Nat := [888,901,902,903,904,905,906,907,908,909,922,923,924,925,926,927,928,929,930,943,944,945,946,947,948,949,950,951,964,965,966,967]
def kindSupport2_012 : List Nat := [968,969,970,971,972,973,989,990,991,992,993,994,1001,1002,1003,1004,1005,1006,1013,1014,1015,1016,1017,1018,1025,1026,1027,1028,1029,1030,1037,1038]
def kindSupport2_013 : List Nat := [1039,1040,1041,1042,1049,1050,1051,1052,1053,1054,1061,1062,1063,1064,1065,1066,1067,1068,1069,1082,1083,1084,1085,1086,1087,1088,1089,1090,1103,1104,1105,1106]
def kindSupport2_014 : List Nat := [1107,1108,1109,1110,1111,1124,1125,1126,1127,1128,1129,1130,1131,1132,1145,1146,1147,1148,1149,1150,1151,1152,1153,1166,1167,1168,1169,1170,1171,1172,1173,1174]
def kindSupport2_015 : List Nat := [1187,1188,1189,1190,1191,1192,1193,1194,1195,1208,1209,1210,1211,1212,1213,1214,1215,1216,1229,1230,1231,1232,1233,1234,1235,1236,1237,1238,1254,1255,1256,1257]
def kindSupport2_016 : List Nat := [1258,1259,1260,1261,1262,1275,1276,1277,1278,1279,1280,1281,1282,1283,1296,1297,1298,1299,1300,1301,1302,1303,1304,1317,1318,1319,1320,1321,1322,1323,1324,1325]
def kindSupport2_017 : List Nat := [1338,1339,1340,1341,1342,1343,1344,1345,1346,1347,1363,1364,1365,1366,1367,1368,1369,1370,1371,1372]
def kindSupport2_code : Nat := 0x2ae156cab45592ac155caac5552aa154ca865422a09500a7e53e29e94f0a7653a29694b0a5652a29494a0a4e5262929460a2e51628a9450a265122889440a0650228094009fe4fe27e93f09f64ee27693b09d64ea27493a09ce4e626b13549a84d326913449a04cf26713349804bf25f12f49784bb25d12e49704ab25512a49504a725312949484a324b1254928493249124492048f247120490047f23f11f48f847b23d11e48d846b23511a48d046723311948c845722b11548a845322911448a044f221110488043f21f10f487843b21d10b485842b21510a4850427213109483c41d20e106c834419209104482040f207103480c405202100c8044011fd0fe47f03f71fb0fd47dc3ed1f60fac7d43e91f10f847c03df1ef0f7479a3cc1e58f287923c81e38f1878a3c41db8ed876a3b41d98ec87623b01d78e887423a01cf8e7873a39c1cd8e6871a38c1c58e287123881c38e1870a3781bb8dd86ea3741b98dc86e23701b00d7c6bc35d1ae0d6c6b43591ac0d5c6943491a40d1c68c3451a20d0c68433519a0ccc6643311980cbc65c32d1900c7c63c31d18e0c6c63431918c0c2c6143091840c1c60c3051820c0c5ec2f517a0bcc5e42f11780bbc5dc2e11700b7c5bc2dd16e0b6c5b42d91660b2c5942c91640b1c58c2c51620adc56c2b515a0acc5642b11580abc5502a71530a945482a314e0a6c53429914c0a5c52028f1470a3451828b1420a0c50428114009fc4f027713b09d44e827313609ac4d4269134099c4b425912c095c4ac25512a094c4a4245122090c48424112008fc47c23d11808bc45c22d11608ac454229114086c43421910c085c42c21510a084c3fe1fe0fe87f03f61fa0fc87e03ee1f60f487a03ce1e60f287903c61e20f087503a61d20e8874039e1ce0e6873037e1be0de86f03761ba0dc86e036e1aa0d486a034e1a60d286903461a20ca86503261920c8864031e18e0c686002fe17e0be85f02f617a0bc85e02d616a0b485a02ce1660b285902c61560aa85502a61520a8854029e14e09e84f027613a09c84e026e13609a84a024e12609284902461220908480226112088844021e10e08684302160fe07e83f01f60fa07c83e01ee0f607783b81da0ec07583a81c60e207083801be0de06b83581aa0d406983481960ca064832018e0c605f82f817a0bc05d82e81660b205882c015e0ae053829814a0a4051828813609a04c826012e096047823811a08c045822810608204082000fe07e03b81d80ea07403981c80d606a03481a00ce066
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
def kindSupport2_rest_018 : Nat := PackedRawNatGrowth.drop 7332 kindSupport2_code
def kindSupport2_suffix_018 : List Nat := []
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
    (PackedRawNatGrowth.readList 13 564 kindSupport2_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
