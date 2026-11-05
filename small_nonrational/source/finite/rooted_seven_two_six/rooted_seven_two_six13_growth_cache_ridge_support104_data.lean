module
prelude
public import RootedSevenTwoSix13GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport104_000 : List Nat := [0,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250,251,252,253,254,255,256,257,258,259]
def ridgeSupport104_001 : List Nat := [260,261,262,263,264,550,551,552,553,554,555,556,557,558,559,560,561,562,563,564,565,566,567,568,569,570,571,572,573,574,575,576]
def ridgeSupport104_002 : List Nat := [577,578,579,580,581,582,583,584,585,586,587,588,589,590,591,592,593,594,595,596,597,598,599,600,601,602,603,604,605,606,607,608]
def ridgeSupport104_003 : List Nat := [609,610,611,612,613,614,615,616,617,618,619,620,621,982,983,984,985,986,987,988,989,990,991,992,993,994,995,996,997,998,999,1000]
def ridgeSupport104_004 : List Nat := [1001,1002,1003,1004,1005,1006,1007,1008,1009,1010,1011,1012,1013,1014,1015,1016,1017,1018,1019,1020,1021,1022,1023,1024,1025,1026,1027,1028,1029,1030,1031,1032]
def ridgeSupport104_005 : List Nat := [1033,1034,1035,1036,1037,1038,1039,1040,1041,1042,1043,1044,1045,1046,1047,1048,1049,1050,1051,1052,1053,1054,1055,1056,1057,1058,1059,1060,1061,1062,1063,1064]
def ridgeSupport104_006 : List Nat := [1065,1066,1067,1068,1069,1070,1071,1072,1073,1074,1075,1076,1077,1078,1079,1080,1081,1082,1083,1084,1085,1086,1087,1088,1089,1210,1211,1212,1213,1214,1215,1366]
def ridgeSupport104_007 : List Nat := [1367,1368,1369,1370,1371,1372,1373,1374,1375,1376,1377,1378,1379,1380,1381,1382,1383,1384,1385,1386,1387,1388,1389,1390,1391,1392,1393,1394,1395,1396,1397,1398]
def ridgeSupport104_008 : List Nat := [1399,1400,1401,1402,1403,1404,1405,1406,1407,1408,1409,1410,1411,1412,1413,1414,1415,1416,1417,1418,1419,1510,1511,1512,1513,1514,1515,1516,1517,1518,1519,1520]
def ridgeSupport104_009 : List Nat := [1521,1522,1523,1524,1525,1526,1527,1834,1835,1836,1837,1838,1839,1840,1841,1842,1843,1844,1845,1846,1847,1848,1849,1850,1851,1852,1853,1854,1855,1856,1857,1858]
def ridgeSupport104_010 : List Nat := [1859,1860,1861,1862,1863,1864,1865,1866,1867,1868,1869,1870,1871,1872,1873,1874,1875,1876,1877,1878,1879,1880,1881,1882,1883,1884,1885,1886,1887,1888,1889,1890]
def ridgeSupport104_011 : List Nat := [1891,1892,1893,1894,1895,1896,1897,1898,1899,1900,1901,1902,1903,1904,1905,2026,2027,2028,2029,2030,2031]
def ridgeSupport104_code : Nat := 0x7effddfb7f67ebfd5dc7b876fedddb7b676bed5da7b4767ecdd97b2763ec5d87b075febdd77ae75beb5d67ac757eadd57aa753ea5d47a874fe9dd37a674be95d27a4747e8dd17a2743e85d07a073fe7dcf79e73be75ce79c737e6dcd79a733e65cc79872fe5dcb79672be557defb5f5be97cef95f1be17bef75edbd97aef55e9bd179ef358bb15626c4587b0d616c2583b05606c057fafd5f6be57baf55e6bc577aed5d6ba573ae55c6b856fadd5b6b656bad55a6b4567acd596b2563ac5586b055fabd576ae55bab5566ac557aad2fe5f4bd9792ee5d4418810fe1f43d8790ee1d4398710de1b4358690ce194318610be1742d8590ae1542985109e1342584908e1142184107e0f41d83906e0d41983105e0b41582904e0941182103e0740d81902e0540981101e0340580900e01401800ffdff3fd7f8fedfd3f97f0fddfb3f57e8fcdf93f17e0fbdf73ed7d8fadf53e97d0f9df33e57c8f8df13e17c0f7def3dd7b8f6ded3d97b0f5deb26d4d89ad352694d099d332654c898d312614c097d2f25d4b896d2d2594b095d2b2554a894d292514a093d2724d49892d2524949091d2324548890d212414808fd1f23d4788ed1d2394708dd1b2354688cd192314608bd1722d4588ad1522945089d1310820e41882904206408809001fe3f87e8fc1f63e87c8f81ee3d87a8f41e63c8788f01de3b8768ec1d63a8748e81ce39872800
def ridgeSupport104_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport104_code
def ridgeSupport104_rest_001 : Nat := PackedRawNatGrowth.drop 352 ridgeSupport104_code
def ridgeSupport104_rest_002 : Nat := PackedRawNatGrowth.drop 704 ridgeSupport104_code
def ridgeSupport104_rest_003 : Nat := PackedRawNatGrowth.drop 1056 ridgeSupport104_code
def ridgeSupport104_rest_004 : Nat := PackedRawNatGrowth.drop 1408 ridgeSupport104_code
def ridgeSupport104_rest_005 : Nat := PackedRawNatGrowth.drop 1760 ridgeSupport104_code
def ridgeSupport104_rest_006 : Nat := PackedRawNatGrowth.drop 2112 ridgeSupport104_code
def ridgeSupport104_rest_007 : Nat := PackedRawNatGrowth.drop 2464 ridgeSupport104_code
def ridgeSupport104_rest_008 : Nat := PackedRawNatGrowth.drop 2816 ridgeSupport104_code
def ridgeSupport104_rest_009 : Nat := PackedRawNatGrowth.drop 3168 ridgeSupport104_code
def ridgeSupport104_rest_010 : Nat := PackedRawNatGrowth.drop 3520 ridgeSupport104_code
def ridgeSupport104_rest_011 : Nat := PackedRawNatGrowth.drop 3872 ridgeSupport104_code
def ridgeSupport104_rest_012 : Nat := PackedRawNatGrowth.drop 4103 ridgeSupport104_code
def ridgeSupport104_suffix_012 : List Nat := []
def ridgeSupport104_suffix_011 : List Nat := ridgeSupport104_011 ++ ridgeSupport104_suffix_012
def ridgeSupport104_suffix_010 : List Nat := ridgeSupport104_010 ++ ridgeSupport104_suffix_011
def ridgeSupport104_suffix_009 : List Nat := ridgeSupport104_009 ++ ridgeSupport104_suffix_010
def ridgeSupport104_suffix_008 : List Nat := ridgeSupport104_008 ++ ridgeSupport104_suffix_009
def ridgeSupport104_suffix_007 : List Nat := ridgeSupport104_007 ++ ridgeSupport104_suffix_008
def ridgeSupport104_suffix_006 : List Nat := ridgeSupport104_006 ++ ridgeSupport104_suffix_007
def ridgeSupport104_suffix_005 : List Nat := ridgeSupport104_005 ++ ridgeSupport104_suffix_006
def ridgeSupport104_suffix_004 : List Nat := ridgeSupport104_004 ++ ridgeSupport104_suffix_005
def ridgeSupport104_suffix_003 : List Nat := ridgeSupport104_003 ++ ridgeSupport104_suffix_004
def ridgeSupport104_suffix_002 : List Nat := ridgeSupport104_002 ++ ridgeSupport104_suffix_003
def ridgeSupport104_suffix_001 : List Nat := ridgeSupport104_001 ++ ridgeSupport104_suffix_002
def ridgeSupport104_suffix_000 : List Nat := ridgeSupport104_000 ++ ridgeSupport104_suffix_001
theorem ridgeSupport104_source : candidateRows 104 =
    (PackedRawNatGrowth.readList 11 373 ridgeSupport104_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
