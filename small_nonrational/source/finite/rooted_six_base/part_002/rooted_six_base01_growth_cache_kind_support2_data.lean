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
def kindSupport2_code : Nat := 0x1928649192064719186451910643190864118c463018bc62e18b462c18ac62a18a4628186c61a1864618185c6161854614184c6061814604180c602180460017fc5fe17c45f017bc5ee17b45ec17ac5ea17a45dc176c5da17645d8175c5d617545d417105c317085c117005bf16f85bd16f05bb16b85ad16b05ab16a85a916a05a71698599166059716585951650593164859116105831608581160057f15f857d15f056f15b856d15b056b15a856915a0567155c5561554554154c5521544550153c54e150454014fc53e14f453c14ec53a14e452c14ac52a14a4528149c5261494524145c5161454514144c5121444510143c502140450013fc4fe13f44fc13ec4fa13b44ec13ac4ea13a44e8139c4e613944d8135c4d613544d4134c4d213444d0130c4c213044c012fc4be12f44bc12ec4ae12b44ac12ac4aa12a44a8129c4a6127c49e127449c126c49a124c4921244490123c48e121c4861214484120c48211ec47a11e447811dc47611bc46e11b446c11ac46a118c4621184460117c45e1144450113c44e113444c112c44a112443c10ec43a10e443810dc43610d4434109c4261094424108c4221084420107c4121044410103c40e103440c102c40a100c40210044000ffc3fe0fdc3f60fd43f40fcc3f20fac3ea0fa43e80f9c3e60f7c3de0f743dc0f6c3da0f4c3d20f443d00f3c3ce0f1c3c60f143c40f0c3c20ec83b10ec03af0eb83ad0eb03ab0ea83a90e7039b0e683990e603970e583950e503870e183850e103830e083810e0037f0dc83710dc036f0db836d0db036b0da835d0d7035b0d683590d603570d583550d203470d183450d103430d083410d003330cc83310cc032f0cb832d0cb032b0c7831d0c7031b0c683190c603170c583090c203070c183050c103030c083010bc02ef0bb82ed0bb02eb0ba82e90ba02db0b682d90b602d70b582d50b502d30b182c50b102c30b082c10b002bf0af82b10ac02af0ab82ad0ab02ab0aa82a90a882a10a8029f0a7829d0a582950a502930a482910a282890a202870a1828509f827d09f027b09e827909c827109c026f09b826d0998265099026309882610944250093c24e093424c092c24a092424808ec23a08e423808dc23608d423408cc2260894224088c2220884220087c21e0844210083c20e083420c082c20a08241fc07ec1fa07e41f807dc1f607d41f4079c1e607941e4078c1e207841e0077c1d207441d0073c1ce07341cc072c1ca06f41bc06ec1ba06e41b806dc1b606d41a8069c1a606941a4068c1a206841a00664198065c1960654194063418c062c18a0624188060418005fc17e05f417c05d417405cc17205c417005a4168059c1660594164057415c056c15a0564158052c14a0524148051c1460514144050c13604d413404cc13204c413004bc12e0484120047c11e047411c046c11a046410c042c10a0424108041c106041410403f40fc03ec0fa03e40f803c40f003bc0ee03b40ec03940e4038c0e203840e003640d8035c0d603540d403340cc032c0ca03240c803040c002fc0be02f40bc02d40b402cc0b202c40b002a40a8029c0a602940a4027409c026c09a02640980244090023c08e023408c0214084020c082020408001e407801dc07601d4074
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
theorem kindSupport2_source : kindRows 2 =
    (PackedRawNatGrowth.readList 14 672 kindSupport2_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase01
