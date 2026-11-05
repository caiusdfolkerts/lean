module
prelude
public import RootedSixExtra05GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport896_000 : List Nat := [26,42,52,72,82,86,87,227,228,229,230,231,232,242,243,244,245,246,247,315,316,317,318,319,320,330,331,332,333,334,335,399]
def ridgeSupport896_001 : List Nat := [400,401,402,403,404,414,415,416,417,418,419,421,422,423,424,425,426,436,437,439,440,442,443,512,513,514,515,516,517,527,528,529]
def ridgeSupport896_002 : List Nat := [530,531,532,596,597,598,599,600,601,611,612,613,614,615,616,618,619,620,621,622,623,633,634,636,637,639,640,705,706,707,708,709]
def ridgeSupport896_003 : List Nat := [710,720,721,722,723,724,725,727,728,729,730,731,732,742,743,745,746,748,749,886,887,888,889,890,891,901,902,903,904,905,906,970]
def ridgeSupport896_004 : List Nat := [971,972,973,974,975,985,986,987,988,989,990,992,993,994,995,996,997,1007,1008,1010,1011,1013,1014,1079,1080,1081,1082,1083,1084,1094,1095,1096]
def ridgeSupport896_005 : List Nat := [1097,1098,1099,1101,1102,1103,1104,1105,1106,1116,1117,1119,1120,1122,1123,1126,1127,1128,1129,1130,1131,1141,1142,1144,1145,1147,1148,1150,1151,1152,1153,1154]
def ridgeSupport896_006 : List Nat := [1155,1186,1187,1188,1189,1190,1191,1222,1223,1224,1225,1226,1227,1276,1277,1278,1279,1280,1281,1282,1283,1284,1285,1286,1287,1318,1319,1320,1321,1322,1323,1354]
def ridgeSupport896_007 : List Nat := [1355,1356,1357,1358,1359,1414,1415,1416,1417,1418,1419,1450,1451,1452,1453,1454,1455,1510,1511,1512,1513,1514,1515,1588,1589,1590,1591,1592,1593,1600,1601,1603]
def ridgeSupport896_008 : List Nat := [1605,1606,1607,1609,1611,1612,1613,1615,1617,1648,1649,1651,1653,1654,1655,1657,1659,1660,1661,1663,1665,1696,1697,1699,1701,1702,1703,1705,1707,1708,1709,1711]
def ridgeSupport896_009 : List Nat := [1713,1816,1817,1819,1821,1822,1823,1825,1827,1828,1829,1831,1833,1864,1865,1867,1869,1870,1871,1873,1875,1876,1877,1879,1881,1912,1913,1915,1917,1918,1919,1921]
def ridgeSupport896_010 : List Nat := [1923,1924,1925,1927,1929,1960,1961,1963,1965,1966,1967,1969,1971,1972,1973,1975,1977,2008,2009,2011,2013,2014,2015,2017,2019,2020,2021,2023,2025,2056,2057,2059]
def ridgeSupport896_011 : List Nat := [2061,2062,2063,2065,2067,2068,2069,2071,2073]
def ridgeSupport896_code : Nat := 0x81981781581481381180f80e80d80b8098087e97e77e57e47e37e17df7de7dd7db7d97d87b97b77b57b47b37b17af7ae7ad7ab7a97a878978778578478378177f77e77d77b77977875975775575475375174f74e74d74b74974872972772572472372171f71e71d71b7197186b16af6ad6ac6ab6a96a76a66a56a36a16a068167f67d67c67b67967767667567367167065164f64d64c64b6496476466456436416406396386376366356345eb5ea5e95e85e75e65af5ae5ad5ac5ab5aa58b58a58958858758654f54e54d54c54b54a52b52a5295285275265075065055045035025015004ff4fe4fd4fc4cb4ca4c94c84c74c64a74a64a54a44a34a248348248148047f47e47c47b47947847647546b46a46946846746646346246045f45d45c45245145044f44e44d44b44a44944844744643c43b43a4394384373f63f53f33f23f03ef3e53e43e33e23e13e03de3dd3dc3db3da3d93cf3ce3cd3cc3cb3ca38a38938838738638537b37a3793783773762ed2ec2ea2e92e72e62dc2db2da2d92d82d72d52d42d32d22d12d02c62c52c42c32c22c128027f27d27c27a27926f26e26d26c26b26a26826726626526426325925825725625525421421321221121020f2052042032022012001bb1ba1b81b71b51b41aa1a91a81a71a61a51a31a21a11a019f19e19419319219119018f14f14e14d14c14b14a14013f13e13d13c13b0f70f60f50f40f30f20e80e70e60e50e40e305705605204803402a01a
def ridgeSupport896_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport896_code
def ridgeSupport896_rest_001 : Nat := PackedRawNatGrowth.drop 384 ridgeSupport896_code
def ridgeSupport896_rest_002 : Nat := PackedRawNatGrowth.drop 768 ridgeSupport896_code
def ridgeSupport896_rest_003 : Nat := PackedRawNatGrowth.drop 1152 ridgeSupport896_code
def ridgeSupport896_rest_004 : Nat := PackedRawNatGrowth.drop 1536 ridgeSupport896_code
def ridgeSupport896_rest_005 : Nat := PackedRawNatGrowth.drop 1920 ridgeSupport896_code
def ridgeSupport896_rest_006 : Nat := PackedRawNatGrowth.drop 2304 ridgeSupport896_code
def ridgeSupport896_rest_007 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport896_code
def ridgeSupport896_rest_008 : Nat := PackedRawNatGrowth.drop 3072 ridgeSupport896_code
def ridgeSupport896_rest_009 : Nat := PackedRawNatGrowth.drop 3456 ridgeSupport896_code
def ridgeSupport896_rest_010 : Nat := PackedRawNatGrowth.drop 3840 ridgeSupport896_code
def ridgeSupport896_rest_011 : Nat := PackedRawNatGrowth.drop 4224 ridgeSupport896_code
def ridgeSupport896_rest_012 : Nat := PackedRawNatGrowth.drop 4332 ridgeSupport896_code
def ridgeSupport896_suffix_012 : List Nat := []
def ridgeSupport896_suffix_011 : List Nat := ridgeSupport896_011 ++ ridgeSupport896_suffix_012
def ridgeSupport896_suffix_010 : List Nat := ridgeSupport896_010 ++ ridgeSupport896_suffix_011
def ridgeSupport896_suffix_009 : List Nat := ridgeSupport896_009 ++ ridgeSupport896_suffix_010
def ridgeSupport896_suffix_008 : List Nat := ridgeSupport896_008 ++ ridgeSupport896_suffix_009
def ridgeSupport896_suffix_007 : List Nat := ridgeSupport896_007 ++ ridgeSupport896_suffix_008
def ridgeSupport896_suffix_006 : List Nat := ridgeSupport896_006 ++ ridgeSupport896_suffix_007
def ridgeSupport896_suffix_005 : List Nat := ridgeSupport896_005 ++ ridgeSupport896_suffix_006
def ridgeSupport896_suffix_004 : List Nat := ridgeSupport896_004 ++ ridgeSupport896_suffix_005
def ridgeSupport896_suffix_003 : List Nat := ridgeSupport896_003 ++ ridgeSupport896_suffix_004
def ridgeSupport896_suffix_002 : List Nat := ridgeSupport896_002 ++ ridgeSupport896_suffix_003
def ridgeSupport896_suffix_001 : List Nat := ridgeSupport896_001 ++ ridgeSupport896_suffix_002
def ridgeSupport896_suffix_000 : List Nat := ridgeSupport896_000 ++ ridgeSupport896_suffix_001
theorem ridgeSupport896_source : candidateSupports 896 =
    (PackedRawNatGrowth.readList 12 361 ridgeSupport896_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra05
