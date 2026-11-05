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
def kindSupport3_000 : List Nat := [112,113,114,115,116,117,124,125,126,127,128,129,136,137,138,139,140,141,148,149,150,151,152,153,160,161,162,163,164,165,172,173]
def kindSupport3_001 : List Nat := [174,175,176,177,187,188,189,190,191,192,193,194,195,196,197,198,208,209,210,211,212,213,214,215,216,217,218,219,229,230,231,232]
def kindSupport3_002 : List Nat := [233,234,235,236,237,238,239,240,250,251,252,253,254,255,256,257,258,259,260,261,268,269,270,271,272,273,280,281,282,283,284,285]
def kindSupport3_003 : List Nat := [292,293,294,295,296,297,304,305,306,307,308,309,316,317,318,319,320,321,328,329,330,331,332,333,343,344,345,346,347,348,349,350]
def kindSupport3_004 : List Nat := [351,352,353,354,364,365,366,367,368,369,370,371,372,373,374,375,385,386,387,388,389,390,391,392,393,394,395,396,406,407,408,409]
def kindSupport3_005 : List Nat := [410,411,412,413,414,415,416,417,427,428,429,430,431,432,433,434,435,436,437,438,448,449,450,451,452,453,454,455,456,457,458,459]
def kindSupport3_006 : List Nat := [469,470,471,472,473,474,475,476,477,478,479,480,490,491,492,493,494,495,496,497,498,499,500,501,512,513,514,515,516,517,518,519]
def kindSupport3_007 : List Nat := [520,521,522,523,524,525,526,533,534,535,536,537,538,545,546,547,548,549,550,557,558,559,560,561,562,569,570,571,572,573,574,581]
def kindSupport3_008 : List Nat := [582,583,584,585,586,593,594,595,596,597,598,608,609,610,611,612,613,614,615,616,617,618,619,629,630,631,632,633,634,635,636,637]
def kindSupport3_009 : List Nat := [638,639,640,650,651,652,653,654,655,656,657,658,659,660,661,671,672,673,674,675,676,677,678,679,680,681,682,692,693,694,695,696]
def kindSupport3_010 : List Nat := [697,698,699,700,701,702,703,713,714,715,716,717,718,719,720,721,722,723,724,734,735,736,737,738,739,740,741,742,743,744,745,755]
def kindSupport3_011 : List Nat := [756,757,758,759,760,761,762,763,764,765,766,777,778,779,780,781,782,783,784,785,786,787,788,789,790,791,798,799,800,801,802,803]
def kindSupport3_012 : List Nat := [810,811,812,813,814,815,822,823,824,825,826,827,834,835,836,837,838,839,846,847,848,849,850,851,858,859,860,861,862,863,873,874]
def kindSupport3_013 : List Nat := [875,876,877,878,879,880,881,882,883,884,894,895,896,897,898,899,900,901,902,903,904,905,915,916,917,918,919,920,921,922,923,924]
def kindSupport3_014 : List Nat := [925,926,936,937,938,939,940,941,942,943,944,945,946,947,954,955,956,957,958,959,966,967,968,969,970,971,978,979,980,981,982,983]
def kindSupport3_015 : List Nat := [990,991,992,993,994,995,1002,1003,1004,1005,1006,1007,1014,1015,1016,1017,1018,1019,1029,1030,1031,1032,1033,1034,1035,1036,1037,1038,1039,1040,1050,1051]
def kindSupport3_016 : List Nat := [1052,1053,1054,1055,1056,1057,1058,1059,1060,1061,1071,1072,1073,1074,1075,1076,1077,1078,1079,1080,1081,1082,1092,1093,1094,1095,1096,1097,1098,1099,1100,1101]
def kindSupport3_017 : List Nat := [1102,1103,1113,1114,1115,1116,1117,1118,1119,1120,1121,1122,1123,1124,1134,1135,1136,1137,1138,1139,1140,1141,1142,1143,1144,1145,1155,1156,1157,1158,1159,1160]
def kindSupport3_018 : List Nat := [1161,1162,1163,1164,1165,1166,1176,1177,1178,1179,1180,1181,1182,1183,1184,1185,1186,1187,1198,1199,1200,1201,1202,1203,1204,1205,1206,1207,1208,1209,1210,1211]
def kindSupport3_019 : List Nat := [1212,1222,1223,1224,1225,1226,1227,1228,1229,1230,1231,1232,1233,1243,1244,1245,1246,1247,1248,1249,1250,1251,1252,1253,1254,1264,1265,1266,1267,1268,1269,1270]
def kindSupport3_020 : List Nat := [1271,1272,1273,1274,1275,1285,1286,1287,1288,1289,1290,1291,1292,1293,1294,1295,1296,1307,1308,1309,1310,1311,1312,1313,1314,1315,1316,1317,1318,1319,1320,1321]
def kindSupport3_021 : List Nat := [1331,1332,1333,1334,1335,1336,1337,1338,1339,1340,1341,1342,1352,1353,1354,1355,1356,1357,1358,1359,1360,1361,1362,1363,1373,1374,1375,1376,1377,1378,1379,1380]
def kindSupport3_022 : List Nat := [1381,1382,1383,1384,1394,1395,1396,1397,1398,1399,1400,1401,1402,1403,1404,1405,1416,1417,1418,1419,1420,1421,1422,1423,1424,1425,1426,1427,1428,1429,1430,1441]
def kindSupport3_023 : List Nat := [1442,1443,1444,1445,1446,1447,1448,1449,1450,1451,1452,1453,1454,1455]
def kindSupport3_code : Nat := 0x5af5ae5ad5ac5ab5aa5a95a85a75a65a55a45a35a25a159659559459359259159058f58e58d58c58b58a58958857d57c57b57a57957857757657557457357256856756656556456356256156055f55e55d55355255155054f54e54d54c54b54a54954853e53d53c53b53a53953853753653553453352952852752652552452352252152051f51e51d51c51b51050f50e50d50c50b50a5095085075065054fb4fa4f94f84f74f64f54f44f34f24f14f04e64e54e44e34e24e14e04df4de4dd4dc4db4d14d04cf4ce4cd4cc4cb4ca4c94c84c74c64bc4bb4ba4b94b84b74b64b54b44b34b24b14b04af4ae4a34a24a14a049f49e49d49c49b49a49949848e48d48c48b48a48948848748648548448347947847747647547447347247147046f46e46446346246146045f45e45d45c45b45a45944f44e44d44c44b44a44944844744644544443a43943843743643543443343243143042f42542442342242142041f41e41d41c41b41a41040f40e40d40c40b40a4094084074064053fb3fa3f93f83f73f63ef3ee3ed3ec3eb3ea3e33e23e13e03df3de3d73d63d53d43d33d23cb3ca3c93c83c73c63bf3be3bd3bc3bb3ba3b33b23b13b03af3ae3ad3ac3ab3aa3a93a839e39d39c39b39a39939839739639539439338938838738638538438338238138037f37e37437337237137036f36e36d36c36b36a36935f35e35d35c35b35a35335235135034f34e34734634534434334233b33a33933833733632f32e32d32c32b32a32332232132031f31e31731631531431331231131030f30e30d30c30b30a3092fe2fd2fc2fb2fa2f92f82f72f62f52f42f32e92e82e72e62e52e42e32e22e12e02df2de2d42d32d22d12d02cf2ce2cd2cc2cb2ca2c92bf2be2bd2bc2bb2ba2b92b82b72b62b52b42aa2a92a82a72a62a52a42a32a22a12a029f29529429329229129028f28e28d28c28b28a28027f27e27d27c27b27a27927827727627526b26a26926826726626526426326226126025625525425325225124a24924824724624523e23d23c23b23a23923223123022f22e22d22622522422322222121a21921821721621520e20d20c20b20a2092082072062052042032022012001f51f41f31f21f11f01ef1ee1ed1ec1eb1ea1e01df1de1dd1dc1db1da1d91d81d71d61d51cb1ca1c91c81c71c61c51c41c31c21c11c01b61b51b41b31b21b11b01af1ae1ad1ac1ab1a11a019f19e19d19c19b19a19919819719618c18b18a18918818718618518418318218117717617517417317217117016f16e16d16c16216116015f15e15d15c15b15a15915815714d14c14b14a14914814114013f13e13d13c13513413313213113012912812712612512411d11c11b11a11911811111010f10e10d10c1051041031021011000ff0fe0fd0fc0fb0fa0f00ef0ee0ed0ec0eb0ea0e90e80e70e60e50db0da0d90d80d70d60d50d40d30d20d10d00c60c50c40c30c20c10c00bf0be0bd0bc0bb0b10b00af0ae0ad0ac0a50a40a30a20a10a009909809709609509408d08c08b08a08908808108007f07e07d07c075074073072071070
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
def kindSupport3_rest_024 : Nat := PackedRawNatGrowth.drop 9000 kindSupport3_code
def kindSupport3_suffix_024 : List Nat := []
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
    (PackedRawNatGrowth.readList 12 750 kindSupport3_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra06
