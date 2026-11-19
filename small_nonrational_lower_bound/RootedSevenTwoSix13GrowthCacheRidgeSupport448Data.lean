module
prelude
public meta import CertificateNumbers
public import RootedSevenTwoSix13GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport448_000 : List Nat := [172,173,174,175,182,183,229,230,231,232,239,240,286,287,291,293,294,298,300,301,303,307,308,309,310,317,318,364,365,369,371,372]
def ridgeSupport448_001 : List Nat := [376,378,379,381,385,386,390,392,393,397,399,400,402,479,481,482,483,484,486,491,493,494,495,496,498,514,516,518,519,520,522,524]
def ridgeSupport448_002 : List Nat := [525,536,537,538,540,542,543,548,549,551,553,554,555,556,558,563,565,566,567,568,570,586,588,590,591,592,594,596,597,608,609,610]
def ridgeSupport448_003 : List Nat := [612,614,615,620,621,623,625,626,627,628,630,635,637,638,639,640,642,658,660,662,663,664,666,668,669,680,681,682,684,686,687,692]
def ridgeSupport448_004 : List Nat := [693,875,877,878,879,896,897,898,900,902,903,908,909,910,912,914,915,952,953,954,955,958,959,960,961,971,973,977,979,983,985,986]
def ridgeSupport448_005 : List Nat := [987,1004,1005,1006,1008,1010,1011,1016,1017,1018,1020,1022,1023,1060,1061,1062,1063,1066,1067,1068,1069,1079,1081,1085,1087,1091,1093,1094,1095,1112,1113,1114]
def ridgeSupport448_006 : List Nat := [1116,1118,1119,1124,1125,1126,1128,1130,1131,1168,1169,1170,1171,1174,1175,1176,1177,1187,1189,1193,1195,1208,1209,1214,1215,1220,1221,1316,1317,1319,1321,1328]
def ridgeSupport448_007 : List Nat := [1329,1331,1333,1352,1353,1358,1359,1370,1371,1373,1375,1382,1383,1385,1387,1406,1407,1412,1413,1424,1425,1427,1429,1436,1437,1439,1441,1460,1461,1466,1467,1492]
def ridgeSupport448_008 : List Nat := [1494,1496,1497,1510,1512,1514,1515,1528,1530,1532,1533,1766,1767,1778,1779,1802,1803,1814,1815,1838,1839,1850,1851,1874,1875,1886,1887,1910,1911,1922,1923,1946]
def ridgeSupport448_009 : List Nat := [1947,1958,1959]
def ridgeSupport448_code : Nat := (certNat% 0)
def ridgeSupport448_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport448_code
def ridgeSupport448_rest_001 : Nat := PackedRawNatGrowth.drop 352 ridgeSupport448_code
def ridgeSupport448_rest_002 : Nat := PackedRawNatGrowth.drop 704 ridgeSupport448_code
def ridgeSupport448_rest_003 : Nat := PackedRawNatGrowth.drop 1056 ridgeSupport448_code
def ridgeSupport448_rest_004 : Nat := PackedRawNatGrowth.drop 1408 ridgeSupport448_code
def ridgeSupport448_rest_005 : Nat := PackedRawNatGrowth.drop 1760 ridgeSupport448_code
def ridgeSupport448_rest_006 : Nat := PackedRawNatGrowth.drop 2112 ridgeSupport448_code
def ridgeSupport448_rest_007 : Nat := PackedRawNatGrowth.drop 2464 ridgeSupport448_code
def ridgeSupport448_rest_008 : Nat := PackedRawNatGrowth.drop 2816 ridgeSupport448_code
def ridgeSupport448_rest_009 : Nat := PackedRawNatGrowth.drop 3168 ridgeSupport448_code
def ridgeSupport448_rest_010 : Nat := PackedRawNatGrowth.drop 3201 ridgeSupport448_code
def ridgeSupport448_suffix_010 : List Nat := []
def ridgeSupport448_suffix_009 : List Nat := ridgeSupport448_009 ++ ridgeSupport448_suffix_010
def ridgeSupport448_suffix_008 : List Nat := ridgeSupport448_008 ++ ridgeSupport448_suffix_009
def ridgeSupport448_suffix_007 : List Nat := ridgeSupport448_007 ++ ridgeSupport448_suffix_008
def ridgeSupport448_suffix_006 : List Nat := ridgeSupport448_006 ++ ridgeSupport448_suffix_007
def ridgeSupport448_suffix_005 : List Nat := ridgeSupport448_005 ++ ridgeSupport448_suffix_006
def ridgeSupport448_suffix_004 : List Nat := ridgeSupport448_004 ++ ridgeSupport448_suffix_005
def ridgeSupport448_suffix_003 : List Nat := ridgeSupport448_003 ++ ridgeSupport448_suffix_004
def ridgeSupport448_suffix_002 : List Nat := ridgeSupport448_002 ++ ridgeSupport448_suffix_003
def ridgeSupport448_suffix_001 : List Nat := ridgeSupport448_001 ++ ridgeSupport448_suffix_002
def ridgeSupport448_suffix_000 : List Nat := ridgeSupport448_000 ++ ridgeSupport448_suffix_001
theorem ridgeSupport448_source : candidateRows 448 =
    (PackedRawNatGrowth.readList 11 291 ridgeSupport448_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
