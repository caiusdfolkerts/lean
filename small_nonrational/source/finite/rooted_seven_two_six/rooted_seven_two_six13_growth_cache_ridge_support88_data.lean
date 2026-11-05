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
def ridgeSupport88_000 : List Nat := [0,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202]
def ridgeSupport88_001 : List Nat := [203,204,205,206,207,478,479,480,481,482,483,484,485,486,487,488,489,490,491,492,493,494,495,496,497,498,499,500,501,502,503,504]
def ridgeSupport88_002 : List Nat := [505,506,507,508,509,510,511,512,513,514,515,516,517,518,519,520,521,522,523,524,525,526,527,528,529,530,531,532,533,534,535,536]
def ridgeSupport88_003 : List Nat := [537,538,539,540,541,542,543,544,545,546,547,548,549,874,875,876,877,878,879,880,881,882,883,884,885,886,887,888,889,890,891,892]
def ridgeSupport88_004 : List Nat := [893,894,895,896,897,898,899,900,901,902,903,904,905,906,907,908,909,910,911,912,913,914,915,916,917,918,919,920,921,922,923,924]
def ridgeSupport88_005 : List Nat := [925,926,927,928,929,930,931,932,933,934,935,936,937,938,939,940,941,942,943,944,945,946,947,948,949,950,951,952,953,954,955,956]
def ridgeSupport88_006 : List Nat := [957,958,959,960,961,962,963,964,965,966,967,968,969,970,971,972,973,974,975,976,977,978,979,980,981,1204,1205,1206,1207,1208,1209,1312]
def ridgeSupport88_007 : List Nat := [1313,1314,1315,1316,1317,1318,1319,1320,1321,1322,1323,1324,1325,1326,1327,1328,1329,1330,1331,1332,1333,1334,1335,1336,1337,1338,1339,1340,1341,1342,1343,1344]
def ridgeSupport88_008 : List Nat := [1345,1346,1347,1348,1349,1350,1351,1352,1353,1354,1355,1356,1357,1358,1359,1360,1361,1362,1363,1364,1365,1492,1493,1494,1495,1496,1497,1498,1499,1500,1501,1502]
def ridgeSupport88_009 : List Nat := [1503,1504,1505,1506,1507,1508,1509,1762,1763,1764,1765,1766,1767,1768,1769,1770,1771,1772,1773,1774,1775,1776,1777,1778,1779,1780,1781,1782,1783,1784,1785,1786]
def ridgeSupport88_010 : List Nat := [1787,1788,1789,1790,1791,1792,1793,1794,1795,1796,1797,1798,1799,1800,1801,1802,1803,1804,1805,1806,1807,1808,1809,1810,1811,1812,1813,1814,1815,1816,1817,1818]
def ridgeSupport88_011 : List Nat := [1819,1820,1821,1822,1823,1824,1825,1826,1827,1828,1829,1830,1831,1832,1833,2020,2021,2022,2023,2024,2025]
def ridgeSupport88_code : Nat := 0x7e9fd1f9ff37e5fc9ca794727e4dc9792723e45c879071fe3dc778e71be35c678c717e2dc578a713e25c478870fe1dc378670be15c2784707e0dc1782703e05c07806ffdfdbf77e6fbdf5be77c6f7dedbd77a6f3de5bc7786efdddbb7766ebdd5ba7746e7dcdb97726e3dc5796f25e3bc5786f05dfbbd776ee5dbbb5766ec5d7bad756ea555aa954ea9551aa153ea754da9952ea5549a9151ea3545a8950ea1541a814fe9f53da794ee9d539a714de9b535a694ce99531a614be9752da594ae95529a5149e93525a4948e91521a412e65c4b796d2d65a3d57a8f4de93d17a0f3de73cd798f2de53c9790f1de33c5788f0de13c1780efddf3bd778eeddd3b9770edddb3b5768ecdd93b1760ebdd73ad758eadd53a9750e9dd33a5748e8dd13a1740e7dcf39d738e6dcd399730e5dcb395728e4dc9391720e3dc738d718e2dc5389710e1dc3385708e0dc1381700dfdbf37d6f8dedbd3796f0dddbb3756e8dcdb93716e0dbdb736d6d8dadb522544888d1122144087d0f21d43886d0d21943085d0b21542884d0921142083d0720d41882d0520941081d0320540880d012014007fcff1fd3f87ecfd1f93f07dcfb1f53e87ccf91f13e07bcf71ed3d87acf51e93d079cf31e53c878cf11e13c077cef0cf19c334660cb194324640c718c314620c3184304600bf17c2f45e0bb1742e45c0b716c2d45a0b31642c4580af15c2b456000
def ridgeSupport88_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport88_code
def ridgeSupport88_rest_001 : Nat := PackedRawNatGrowth.drop 352 ridgeSupport88_code
def ridgeSupport88_rest_002 : Nat := PackedRawNatGrowth.drop 704 ridgeSupport88_code
def ridgeSupport88_rest_003 : Nat := PackedRawNatGrowth.drop 1056 ridgeSupport88_code
def ridgeSupport88_rest_004 : Nat := PackedRawNatGrowth.drop 1408 ridgeSupport88_code
def ridgeSupport88_rest_005 : Nat := PackedRawNatGrowth.drop 1760 ridgeSupport88_code
def ridgeSupport88_rest_006 : Nat := PackedRawNatGrowth.drop 2112 ridgeSupport88_code
def ridgeSupport88_rest_007 : Nat := PackedRawNatGrowth.drop 2464 ridgeSupport88_code
def ridgeSupport88_rest_008 : Nat := PackedRawNatGrowth.drop 2816 ridgeSupport88_code
def ridgeSupport88_rest_009 : Nat := PackedRawNatGrowth.drop 3168 ridgeSupport88_code
def ridgeSupport88_rest_010 : Nat := PackedRawNatGrowth.drop 3520 ridgeSupport88_code
def ridgeSupport88_rest_011 : Nat := PackedRawNatGrowth.drop 3872 ridgeSupport88_code
def ridgeSupport88_rest_012 : Nat := PackedRawNatGrowth.drop 4103 ridgeSupport88_code
def ridgeSupport88_suffix_012 : List Nat := []
def ridgeSupport88_suffix_011 : List Nat := ridgeSupport88_011 ++ ridgeSupport88_suffix_012
def ridgeSupport88_suffix_010 : List Nat := ridgeSupport88_010 ++ ridgeSupport88_suffix_011
def ridgeSupport88_suffix_009 : List Nat := ridgeSupport88_009 ++ ridgeSupport88_suffix_010
def ridgeSupport88_suffix_008 : List Nat := ridgeSupport88_008 ++ ridgeSupport88_suffix_009
def ridgeSupport88_suffix_007 : List Nat := ridgeSupport88_007 ++ ridgeSupport88_suffix_008
def ridgeSupport88_suffix_006 : List Nat := ridgeSupport88_006 ++ ridgeSupport88_suffix_007
def ridgeSupport88_suffix_005 : List Nat := ridgeSupport88_005 ++ ridgeSupport88_suffix_006
def ridgeSupport88_suffix_004 : List Nat := ridgeSupport88_004 ++ ridgeSupport88_suffix_005
def ridgeSupport88_suffix_003 : List Nat := ridgeSupport88_003 ++ ridgeSupport88_suffix_004
def ridgeSupport88_suffix_002 : List Nat := ridgeSupport88_002 ++ ridgeSupport88_suffix_003
def ridgeSupport88_suffix_001 : List Nat := ridgeSupport88_001 ++ ridgeSupport88_suffix_002
def ridgeSupport88_suffix_000 : List Nat := ridgeSupport88_000 ++ ridgeSupport88_suffix_001
theorem ridgeSupport88_source : candidateRows 88 =
    (PackedRawNatGrowth.readList 11 373 ridgeSupport88_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
