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
def ridgeSupport7_000 : List Nat := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
def ridgeSupport7_001 : List Nat := [32,33,34,35,36,406,407,408,409,410,411,412,413,414,415,416,417,418,419,420,421,422,423,424,425,426,427,428,429,430,431,432]
def ridgeSupport7_002 : List Nat := [433,434,435,436,437,438,439,440,441,442,443,444,445,446,447,448,449,450,451,452,453,454,455,456,457,458,459,460,461,462,463,464]
def ridgeSupport7_003 : List Nat := [465,466,467,468,469,470,471,472,473,474,475,476,477,694,695,696,697,698,699,700,701,702,703,704,705,706,707,708,709,710,711,712]
def ridgeSupport7_004 : List Nat := [713,714,715,716,717,718,719,720,721,722,723,724,725,726,727,728,729,730,731,732,733,734,735,736,737,738,739,740,741,742,743,744]
def ridgeSupport7_005 : List Nat := [745,746,747,748,749,750,751,752,753,754,755,756,757,758,759,760,761,762,763,764,765,766,767,768,769,770,771,772,773,774,775,776]
def ridgeSupport7_006 : List Nat := [777,778,779,780,781,782,783,784,785,786,787,788,789,790,791,792,793,794,795,796,797,798,799,800,801,1198,1199,1200,1201,1202,1203,1222]
def ridgeSupport7_007 : List Nat := [1223,1224,1225,1226,1227,1228,1229,1230,1231,1232,1233,1234,1235,1236,1237,1238,1239,1240,1241,1242,1243,1244,1245,1246,1247,1248,1249,1250,1251,1252,1253,1254]
def ridgeSupport7_008 : List Nat := [1255,1256,1257,1258,1259,1260,1261,1262,1263,1264,1265,1266,1267,1268,1269,1270,1271,1272,1273,1274,1275,1474,1475,1476,1477,1478,1479,1480,1481,1482,1483,1484]
def ridgeSupport7_009 : List Nat := [1485,1486,1487,1488,1489,1490,1491,1546,1547,1548,1549,1550,1551,1552,1553,1554,1555,1556,1557,1558,1559,1560,1561,1562,1563,1564,1565,1566,1567,1568,1569,1570]
def ridgeSupport7_010 : List Nat := [1571,1572,1573,1574,1575,1576,1577,1578,1579,1580,1581,1582,1583,1584,1585,1586,1587,1588,1589,1590,1591,1592,1593,1594,1595,1596,1597,1598,1599,1600,1601,1602]
def ridgeSupport7_011 : List Nat := [1603,1604,1605,1606,1607,1608,1609,1610,1611,1612,1613,1614,1615,1616,1617,1978,1979,1980,1981,1982,1983]
def ridgeSupport7_code : Nat := 0x7bff7def7de7bbf759472864fc9d9372664bc9592724647c8d91722643c859072063fc7d8f71e63bc758e71c637c6d8d71a633c658c71862fc5d8b71662bc558a714627c4d89712623c458871061fc3d8770e61bc358670c617c2d8570a613c258470860fc1d8370660bc1574ee95d1ba173ee75cdb9972ee55c9b9171ee35c5b8970ee14fb9f53e67c4f79ed3d67a4f39e53c6784ef9dd3b6764eb9d53a6744e79cd396724e39c5386704df9bd3766e4db9b53666c4d79ad3566a4d39a5346684cf99d336664cb995326644c798d2ce594b19612be57321640c7d8f31d638c6d8d319630c5d8b315628c4d89311620c3d8730d618c2d85309610c1d83305608c0d81301600bfd7f2fd5f8bed7d2f95f0bdd7b2f55e8bcd792f15e0bbd772ed5d8bad752e95d0b9d732e55c8b8d712e15c0b7d6f2dd5b8b6d6d2d95b0b5d6b2d55a8b4d692d15a0b3d672cd598b2d652c9590b1d632c5588b0d612c1580afd5f2bd578aed5d2b9570add5b1dd3b876ced1d93b075ceb1d53a874ce91d13a073ce71cd39872ce51c939071ce31c538870ce11c13806fcdf1bd3786ecdd1b93706dcdb1b53686ccd91b13606bcd71ad3586acd51a935069cd31a534868cd11a134067ccf19d33866ccd19933065ccb0240460881082003e0780e81c0360680c81802e0580a8140260480881001e0380680c0160280480800e0180280400600800800
def ridgeSupport7_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport7_code
def ridgeSupport7_rest_001 : Nat := PackedRawNatGrowth.drop 352 ridgeSupport7_code
def ridgeSupport7_rest_002 : Nat := PackedRawNatGrowth.drop 704 ridgeSupport7_code
def ridgeSupport7_rest_003 : Nat := PackedRawNatGrowth.drop 1056 ridgeSupport7_code
def ridgeSupport7_rest_004 : Nat := PackedRawNatGrowth.drop 1408 ridgeSupport7_code
def ridgeSupport7_rest_005 : Nat := PackedRawNatGrowth.drop 1760 ridgeSupport7_code
def ridgeSupport7_rest_006 : Nat := PackedRawNatGrowth.drop 2112 ridgeSupport7_code
def ridgeSupport7_rest_007 : Nat := PackedRawNatGrowth.drop 2464 ridgeSupport7_code
def ridgeSupport7_rest_008 : Nat := PackedRawNatGrowth.drop 2816 ridgeSupport7_code
def ridgeSupport7_rest_009 : Nat := PackedRawNatGrowth.drop 3168 ridgeSupport7_code
def ridgeSupport7_rest_010 : Nat := PackedRawNatGrowth.drop 3520 ridgeSupport7_code
def ridgeSupport7_rest_011 : Nat := PackedRawNatGrowth.drop 3872 ridgeSupport7_code
def ridgeSupport7_rest_012 : Nat := PackedRawNatGrowth.drop 4103 ridgeSupport7_code
def ridgeSupport7_suffix_012 : List Nat := []
def ridgeSupport7_suffix_011 : List Nat := ridgeSupport7_011 ++ ridgeSupport7_suffix_012
def ridgeSupport7_suffix_010 : List Nat := ridgeSupport7_010 ++ ridgeSupport7_suffix_011
def ridgeSupport7_suffix_009 : List Nat := ridgeSupport7_009 ++ ridgeSupport7_suffix_010
def ridgeSupport7_suffix_008 : List Nat := ridgeSupport7_008 ++ ridgeSupport7_suffix_009
def ridgeSupport7_suffix_007 : List Nat := ridgeSupport7_007 ++ ridgeSupport7_suffix_008
def ridgeSupport7_suffix_006 : List Nat := ridgeSupport7_006 ++ ridgeSupport7_suffix_007
def ridgeSupport7_suffix_005 : List Nat := ridgeSupport7_005 ++ ridgeSupport7_suffix_006
def ridgeSupport7_suffix_004 : List Nat := ridgeSupport7_004 ++ ridgeSupport7_suffix_005
def ridgeSupport7_suffix_003 : List Nat := ridgeSupport7_003 ++ ridgeSupport7_suffix_004
def ridgeSupport7_suffix_002 : List Nat := ridgeSupport7_002 ++ ridgeSupport7_suffix_003
def ridgeSupport7_suffix_001 : List Nat := ridgeSupport7_001 ++ ridgeSupport7_suffix_002
def ridgeSupport7_suffix_000 : List Nat := ridgeSupport7_000 ++ ridgeSupport7_suffix_001
theorem ridgeSupport7_source : candidateRows 7 =
    (PackedRawNatGrowth.readList 11 373 ridgeSupport7_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
