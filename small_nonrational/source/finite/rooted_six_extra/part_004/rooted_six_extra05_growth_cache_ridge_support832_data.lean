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
def ridgeSupport832_000 : List Nat := [25,41,51,71,81,85,87,206,207,208,209,210,211,221,222,223,224,225,226,294,295,296,297,298,299,309,310,311,312,313,314,378]
def ridgeSupport832_001 : List Nat := [379,380,381,382,383,393,394,395,396,397,398,420,422,423,424,427,428,433,434,440,441,443,444,491,492,493,494,495,496,506,507,508]
def ridgeSupport832_002 : List Nat := [509,510,511,575,576,577,578,579,580,590,591,592,593,594,595,617,619,620,621,624,625,630,631,637,638,640,641,684,685,686,687,688]
def ridgeSupport832_003 : List Nat := [689,699,700,701,702,703,704,726,728,729,730,733,734,739,740,746,747,749,750,865,866,867,868,869,870,880,881,882,883,884,885,949]
def ridgeSupport832_004 : List Nat := [950,951,952,953,954,964,965,966,967,968,969,991,993,994,995,998,999,1004,1005,1011,1012,1014,1015,1058,1059,1060,1061,1062,1063,1073,1074,1075]
def ridgeSupport832_005 : List Nat := [1076,1077,1078,1100,1102,1103,1104,1107,1108,1113,1114,1120,1121,1123,1124,1125,1127,1128,1129,1132,1133,1138,1139,1145,1146,1148,1149,1156,1157,1158,1159,1160]
def ridgeSupport832_006 : List Nat := [1161,1192,1193,1194,1195,1196,1197,1228,1229,1230,1231,1232,1233,1270,1271,1272,1273,1274,1275,1288,1289,1290,1291,1292,1293,1324,1325,1326,1327,1328,1329,1360]
def ridgeSupport832_007 : List Nat := [1361,1362,1363,1364,1365,1420,1421,1422,1423,1424,1425,1456,1457,1458,1459,1460,1461,1516,1517,1518,1519,1520,1521,1582,1583,1584,1585,1586,1587,1594,1595,1597]
def ridgeSupport832_008 : List Nat := [1599,1607,1608,1609,1610,1613,1614,1615,1616,1642,1643,1645,1647,1655,1656,1657,1658,1661,1662,1663,1664,1690,1691,1693,1695,1703,1704,1705,1706,1709,1710,1711]
def ridgeSupport832_009 : List Nat := [1712,1810,1811,1813,1815,1823,1824,1825,1826,1829,1830,1831,1832,1858,1859,1861,1863,1871,1872,1873,1874,1877,1878,1879,1880,1906,1907,1909,1911,1919,1920,1921]
def ridgeSupport832_010 : List Nat := [1922,1925,1926,1927,1928,1954,1955,1957,1959,1967,1968,1969,1970,1973,1974,1975,1976,2002,2003,2005,2007,2015,2016,2017,2018,2021,2022,2023,2024,2050,2051,2053]
def ridgeSupport832_011 : List Nat := [2055,2063,2064,2065,2066,2069,2070,2071,2072]
def ridgeSupport832_code : Nat := 0x81881781681581281181080f8078058038027e87e77e67e57e27e17e07df7d77d57d37d27b87b77b67b57b27b17b07af7a77a57a37a278878778678578278178077f77777577377275875775675575275175074f74774574374272872772672572272172071f7177157137126b06af6ae6ad6aa6a96a86a769f69d69b69a68067f67e67d67a67967867766f66d66b66a65064f64e64d64a64964864763f63d63b63a63363263163062f62e5f15f05ef5ee5ed5ec5b55b45b35b25b15b059159058f58e58d58c55555455355255155053153052f52e52d52c50d50c50b50a5095084fb4fa4f94f84f74f64d14d04cf4ce4cd4cc4ad4ac4ab4aa4a94a848948848748648548447d47c47a47947347246d46c46946846746546446346146045a45945445345044f44e44c4364354344334324314274264254244234223f73f63f43f33ed3ec3e73e63e33e23e13df3c93c83c73c63c53c43ba3b93b83b73b63b53753743733723713703663653643633623612ee2ed2eb2ea2e42e32de2dd2da2d92d82d62c02bf2be2bd2bc2bb2b12b02af2ae2ad2ac28128027e27d27727627127026d26c26b26925325225125024f24e24424324224124023f1ff1fe1fd1fc1fb1fa1f01ef1ee1ed1ec1eb1bc1bb1b91b81b21b11ac1ab1a81a71a61a418e18d18c18b18a18917f17e17d17c17b17a13a13913813713613512b12a1291281271260e20e10e00df0de0dd0d30d20d10d00cf0ce057055051047033029019
def ridgeSupport832_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport832_code
def ridgeSupport832_rest_001 : Nat := PackedRawNatGrowth.drop 384 ridgeSupport832_code
def ridgeSupport832_rest_002 : Nat := PackedRawNatGrowth.drop 768 ridgeSupport832_code
def ridgeSupport832_rest_003 : Nat := PackedRawNatGrowth.drop 1152 ridgeSupport832_code
def ridgeSupport832_rest_004 : Nat := PackedRawNatGrowth.drop 1536 ridgeSupport832_code
def ridgeSupport832_rest_005 : Nat := PackedRawNatGrowth.drop 1920 ridgeSupport832_code
def ridgeSupport832_rest_006 : Nat := PackedRawNatGrowth.drop 2304 ridgeSupport832_code
def ridgeSupport832_rest_007 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport832_code
def ridgeSupport832_rest_008 : Nat := PackedRawNatGrowth.drop 3072 ridgeSupport832_code
def ridgeSupport832_rest_009 : Nat := PackedRawNatGrowth.drop 3456 ridgeSupport832_code
def ridgeSupport832_rest_010 : Nat := PackedRawNatGrowth.drop 3840 ridgeSupport832_code
def ridgeSupport832_rest_011 : Nat := PackedRawNatGrowth.drop 4224 ridgeSupport832_code
def ridgeSupport832_rest_012 : Nat := PackedRawNatGrowth.drop 4332 ridgeSupport832_code
def ridgeSupport832_suffix_012 : List Nat := []
def ridgeSupport832_suffix_011 : List Nat := ridgeSupport832_011 ++ ridgeSupport832_suffix_012
def ridgeSupport832_suffix_010 : List Nat := ridgeSupport832_010 ++ ridgeSupport832_suffix_011
def ridgeSupport832_suffix_009 : List Nat := ridgeSupport832_009 ++ ridgeSupport832_suffix_010
def ridgeSupport832_suffix_008 : List Nat := ridgeSupport832_008 ++ ridgeSupport832_suffix_009
def ridgeSupport832_suffix_007 : List Nat := ridgeSupport832_007 ++ ridgeSupport832_suffix_008
def ridgeSupport832_suffix_006 : List Nat := ridgeSupport832_006 ++ ridgeSupport832_suffix_007
def ridgeSupport832_suffix_005 : List Nat := ridgeSupport832_005 ++ ridgeSupport832_suffix_006
def ridgeSupport832_suffix_004 : List Nat := ridgeSupport832_004 ++ ridgeSupport832_suffix_005
def ridgeSupport832_suffix_003 : List Nat := ridgeSupport832_003 ++ ridgeSupport832_suffix_004
def ridgeSupport832_suffix_002 : List Nat := ridgeSupport832_002 ++ ridgeSupport832_suffix_003
def ridgeSupport832_suffix_001 : List Nat := ridgeSupport832_001 ++ ridgeSupport832_suffix_002
def ridgeSupport832_suffix_000 : List Nat := ridgeSupport832_000 ++ ridgeSupport832_suffix_001
theorem ridgeSupport832_source : candidateSupports 832 =
    (PackedRawNatGrowth.readList 12 361 ridgeSupport832_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra05
