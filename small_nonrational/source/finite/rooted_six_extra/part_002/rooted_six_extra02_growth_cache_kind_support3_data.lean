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
def kindSupport3_000 : List Nat := [108,109,110,111,112,113,120,121,122,123,124,125,132,133,134,135,136,137,144,145,146,147,148,149,156,157,158,159,160,161,168,169]
def kindSupport3_001 : List Nat := [170,171,172,173,180,181,182,183,184,185,192,193,194,195,196,197,204,205,206,207,208,209,216,217,218,219,220,221,228,229,230,231]
def kindSupport3_002 : List Nat := [232,233,240,241,242,243,244,245,255,256,257,258,259,260,261,262,263,264,265,266,276,277,278,279,280,281,282,283,284,285,286,287]
def kindSupport3_003 : List Nat := [297,298,299,300,301,302,303,304,305,306,307,308,318,319,320,321,322,323,324,325,326,327,328,329,330,331,332,333,343,344,345,346]
def kindSupport3_004 : List Nat := [347,348,349,350,351,352,353,354,364,365,366,367,368,369,370,371,372,373,374,375,385,386,387,388,389,390,391,392,393,394,395,396]
def kindSupport3_005 : List Nat := [406,407,408,409,410,411,412,413,414,415,416,417,427,428,429,430,431,432,433,434,435,436,437,438,448,449,450,451,452,453,454,455]
def kindSupport3_006 : List Nat := [456,457,458,459,469,470,471,472,473,474,475,476,477,478,479,480,490,491,492,493,494,495,496,497,498,499,500,501,512,513,514,515]
def kindSupport3_007 : List Nat := [516,517,518,519,520,521,522,523,524,525,526,527,528,529,530,540,541,542,543,544,545,546,547,548,549,550,551,561,562,563,564,565]
def kindSupport3_008 : List Nat := [566,567,568,569,570,571,572,582,583,584,585,586,587,588,589,590,591,592,593,603,604,605,606,607,608,609,610,611,612,613,614,621]
def kindSupport3_009 : List Nat := [622,623,624,625,626,633,634,635,636,637,638,645,646,647,648,649,650,657,658,659,660,661,662,669,670,671,672,673,674,681,682,683]
def kindSupport3_010 : List Nat := [684,685,686,696,697,698,699,700,701,702,703,704,705,706,707,717,718,719,720,721,722,723,724,725,726,727,728,738,739,740,741,742]
def kindSupport3_011 : List Nat := [743,744,745,746,747,748,749,759,760,761,762,763,764,765,766,767,768,769,770,780,781,782,783,784,785,786,787,788,789,790,791,801]
def kindSupport3_012 : List Nat := [802,803,804,805,806,807,808,809,810,811,812,822,823,824,825,826,827,828,829,830,831,832,833,843,844,845,846,847,848,849,850,851]
def kindSupport3_013 : List Nat := [852,853,854,865,866,867,868,869,870,871,872,873,874,875,876,877,878,879,889,890,891,892,893,894,895,896,897,898,899,900,910,911]
def kindSupport3_014 : List Nat := [912,913,914,915,916,917,918,919,920,921,931,932,933,934,935,936,937,938,939,940,941,942,952,953,954,955,956,957,958,959,960,961]
def kindSupport3_015 : List Nat := [962,963,974,975,976,977,978,979,980,981,982,983,984,985,986,987,988,995,996,997,998,999,1000,1007,1008,1009,1010,1011,1012,1019,1020,1021]
def kindSupport3_016 : List Nat := [1022,1023,1024,1031,1032,1033,1034,1035,1036,1043,1044,1045,1046,1047,1048,1055,1056,1057,1058,1059,1060,1070,1071,1072,1073,1074,1075,1076,1077,1078,1079,1080]
def kindSupport3_017 : List Nat := [1081,1091,1092,1093,1094,1095,1096,1097,1098,1099,1100,1101,1102,1112,1113,1114,1115,1116,1117,1118,1119,1120,1121,1122,1123,1133,1134,1135,1136,1137,1138,1139]
def kindSupport3_018 : List Nat := [1140,1141,1142,1143,1144,1154,1155,1156,1157,1158,1159,1160,1161,1162,1163,1164,1165,1175,1176,1177,1178,1179,1180,1181,1182,1183,1184,1185,1186,1196,1197,1198]
def kindSupport3_019 : List Nat := [1199,1200,1201,1202,1203,1204,1205,1206,1207,1217,1218,1219,1220,1221,1222,1223,1224,1225,1226,1227,1228,1239,1240,1241,1242,1243,1244,1245,1246,1247,1248,1249]
def kindSupport3_020 : List Nat := [1250,1251,1252,1253,1263,1264,1265,1266,1267,1268,1269,1270,1271,1272,1273,1274,1284,1285,1286,1287,1288,1289,1290,1291,1292,1293,1294,1295,1305,1306,1307,1308]
def kindSupport3_021 : List Nat := [1309,1310,1311,1312,1313,1314,1315,1316,1326,1327,1328,1329,1330,1331,1332,1333,1334,1335,1336,1337,1348,1349,1350,1351,1352,1353,1354,1355,1356,1357,1358,1359]
def kindSupport3_022 : List Nat := [1360,1361,1362,1373,1374,1375,1376,1377,1378,1379,1380,1381,1382,1383,1384,1385,1386,1387]
def kindSupport3_code : Nat := 0xad656a2b495a0ace5662b29590ac65622b09580abe55e2ae9548aa25502a79538a9a54c2a59528a925482a39518a8a54429c94e0a6e53629a94d0a6653229894c0a5e52e292148ca44521290147ca3c51d28e146ca345192879438a1a50c2859428a125082839418a0a50427d13e49f04f727b13d49e84f327913c49e04ef27293909c64e227093809be4de26e93709b64da26c93609ae4cc26593289924c8263931898a4c426193089824b725b12d49684b325912c49604af25712b49584a2250928093e49e24e927093649a24c926092e48d246122c914489244121c90c485242120c90447823b91d88ea47423991c88e247023791b88da46323111848c045f22f11748b845b22d11648b044e226913089644a224912088e446222911088643921c10dc86c43521a10cc86443121810bc85c424211908884242020f906082e41620a905082640c205902881240820390007fe3fe1fe8ff07f63f41f98fc87e23f01f78fa07ce3e61f28f907c63dc1ed8f687b23d81eb8f587aa3d41e98f487a23d01e78f387863c21e08f0077e3be1de8ef07763ba1dc8ee075c3ad1d60eac7543a91d40e9c74c3a51d20e8c7323981cb8e5872a3941c98e487223901c78e387083831c10e0470037f1bf0df46f837b1bd0de46de36e1b68db06d636a1b48da06ce3661b28d906c63621b08d586aa3541a98d486a23501a78d3869a34c1a58d0468033f19f0cf467833b19d0ce467033719b0cb065632a1948ca064e3261928c906463221908c5c62c31518a0c4c6243111880c3c61c30d1860c0860230017f8bf85fa2fc17d8be85f22f817b8bb45d82eb1750ba45d02e71730b945c82e31710b605ae2d616a8b505a62d21688b4059e2ce1668b0c5842c11600afc57c2bd15e0aec5742b915c0ab855a2ac1558aa85522a21508a8053e29e14e8a5852a2941498a4852228a1448a2050e28614289f84fa27c13d89e84f227213889c04de26e13689984ca26413189884c226012f89784ba25c12d89444a024f127093449824b125092449024712308f047623a11c88e046e23611a88d0466232118889c44c225112088c444221110087c43c21d10e0848422210107883841a20c1058828412208103881840a20410188084022000fa87d03e61f20f887c03de1ee0f687b03d61ea0f0077c3bc1dd0ee076c3b41d90ec075c3ac1d50e587283921c80e3871838a1c40e187083821c00db06d43681b30d906c43601af0d706b43581ab0d0868033e19e0ce867033619a0cc866032e1960c6062c3141890c4061c30c1850c2060c3041810bb85d82ea1740b985c82e21700b785b82da16c0b105842c015f0af05742b815b0ad05642b01570a6853029614a0a4852028e1460a285102861420a0850027e13e09a04cc26413109804bc25c12d09604ac25412908f847823a11c08d846823211808b845822a1140850424210107083041420810308104042000ff07a83d01e60f207883c01d20e807383981ca0e406e83701b60da06c83601a20d0067833819a0cc06283101860c206083001720b805b82d816a0b405682b01560aa05482a01420a004f827813a09c04a82501260920488240112088043821810a08403e81f00f607a03c81e00e207003781b80da06c
def kindSupport3_rest_000 : Nat := PackedRawNatGrowth.drop 0 kindSupport3_code
def kindSupport3_rest_001 : Nat := PackedRawNatGrowth.drop 416 kindSupport3_code
def kindSupport3_rest_002 : Nat := PackedRawNatGrowth.drop 832 kindSupport3_code
def kindSupport3_rest_003 : Nat := PackedRawNatGrowth.drop 1248 kindSupport3_code
def kindSupport3_rest_004 : Nat := PackedRawNatGrowth.drop 1664 kindSupport3_code
def kindSupport3_rest_005 : Nat := PackedRawNatGrowth.drop 2080 kindSupport3_code
def kindSupport3_rest_006 : Nat := PackedRawNatGrowth.drop 2496 kindSupport3_code
def kindSupport3_rest_007 : Nat := PackedRawNatGrowth.drop 2912 kindSupport3_code
def kindSupport3_rest_008 : Nat := PackedRawNatGrowth.drop 3328 kindSupport3_code
def kindSupport3_rest_009 : Nat := PackedRawNatGrowth.drop 3744 kindSupport3_code
def kindSupport3_rest_010 : Nat := PackedRawNatGrowth.drop 4160 kindSupport3_code
def kindSupport3_rest_011 : Nat := PackedRawNatGrowth.drop 4576 kindSupport3_code
def kindSupport3_rest_012 : Nat := PackedRawNatGrowth.drop 4992 kindSupport3_code
def kindSupport3_rest_013 : Nat := PackedRawNatGrowth.drop 5408 kindSupport3_code
def kindSupport3_rest_014 : Nat := PackedRawNatGrowth.drop 5824 kindSupport3_code
def kindSupport3_rest_015 : Nat := PackedRawNatGrowth.drop 6240 kindSupport3_code
def kindSupport3_rest_016 : Nat := PackedRawNatGrowth.drop 6656 kindSupport3_code
def kindSupport3_rest_017 : Nat := PackedRawNatGrowth.drop 7072 kindSupport3_code
def kindSupport3_rest_018 : Nat := PackedRawNatGrowth.drop 7488 kindSupport3_code
def kindSupport3_rest_019 : Nat := PackedRawNatGrowth.drop 7904 kindSupport3_code
def kindSupport3_rest_020 : Nat := PackedRawNatGrowth.drop 8320 kindSupport3_code
def kindSupport3_rest_021 : Nat := PackedRawNatGrowth.drop 8736 kindSupport3_code
def kindSupport3_rest_022 : Nat := PackedRawNatGrowth.drop 9152 kindSupport3_code
def kindSupport3_rest_023 : Nat := PackedRawNatGrowth.drop 9386 kindSupport3_code
def kindSupport3_suffix_023 : List Nat := []
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
    (PackedRawNatGrowth.readList 13 722 kindSupport3_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
