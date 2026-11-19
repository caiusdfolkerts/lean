module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public meta import CertificateNumbers
public import RootedSixExtra02GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport131_000 : List Nat := [2,6,9,12,13,102,104,107,108,110,139,141,142,145,147,151,153,154,157,159,174,176,179,180,182,211,213,214,217,219,223,225]
def ridgeSupport131_001 : List Nat := [226,229,231,246,248,249,251,252,254,256,257,259,260,263,264,267,269,270,272,273,275,277,278,280,281,284,285,310,311,313,314,315]
def ridgeSupport131_002 : List Nat := [316,318,319,321,322,324,325,1388,1389,1394,1395,1396,1397,1398,1399,1402,1403,1408,1409,1412,1413,1418,1419,1420,1421,1422,1423,1426,1427,1432,1433,1442]
def ridgeSupport131_003 : List Nat := [1443,1444,1445,1446,1447,1466,1467,1468,1469,1470,1471,1490,1491,1492,1493,1494,1495,1514,1515,1516,1517,1518,1519,1538,1539,1540,1541,1542,1543,1562,1563,1564]
def ridgeSupport131_004 : List Nat := [1565,1566,1567,1583,1585,1586,1587,1588,1589,1590,1591,1593,1596,1599,1602,2110,2111,2122,2123,2146,2147,2158,2159,2169,2172,2175,2178,2182,2183,2194,2195,2218]
def ridgeSupport131_005 : List Nat := [2219,2230,2231,2241,2244,2247,2250,2324,2325,2336,2337,2360,2361,2372,2373,2387,2389,2393,2395,2878,2879,2890,2891,2914,2915,2926,2927,2937,2940,2943,2946,2950]
def ridgeSupport131_006 : List Nat := [2951,2962,2963,2986,2987,2998,2999,3009,3012,3015,3018,3092,3093,3104,3105,3128,3129,3140,3141,3155,3157,3161,3163,5132,5133,5138,5139,5140,5141,5170,5171,5176]
def ridgeSupport131_007 : List Nat := [5177,5186,5187,5218,5219,5224,5225,5234,5235,5354,5355,5356,5357,5358,5359,5858,5859,5860,5861,5862,5863,5879,5881,5882,5883,5884,5885,5891,5893,5894,5895,5896]
def ridgeSupport131_008 : List Nat := [5897,6003,6006,6009,6012,6021,6024,6027,6030,6059,6061,6065,6067,6171,6174,6177,6180,6189,6192,6195,6198,6227,6229,6233,6235]
cert_ridgeSupport_code_3 131
cert_ridgeSupport_rest_2 131 000 0
cert_ridgeSupport_rest_2 131 001 416
cert_ridgeSupport_rest_2 131 002 832
cert_ridgeSupport_rest_2 131 003 1248
cert_ridgeSupport_rest_2 131 004 1664
cert_ridgeSupport_rest_2 131 005 2080
cert_ridgeSupport_rest_2 131 006 2496
cert_ridgeSupport_rest_2 131 007 2912
cert_ridgeSupport_rest_2 131 008 3328
cert_ridgeSupport_rest_2 131 009 3653
cert_ridgeSupport_suffix_4 131 009
cert_ridgeSupport_suffix_3 131 008 009
cert_ridgeSupport_suffix_3 131 007 008
cert_ridgeSupport_suffix_3 131 006 007
cert_ridgeSupport_suffix_3 131 005 006
cert_ridgeSupport_suffix_3 131 004 005
cert_ridgeSupport_suffix_3 131 003 004
cert_ridgeSupport_suffix_3 131 002 003
cert_ridgeSupport_suffix_3 131 001 002
cert_ridgeSupport_suffix_3 131 000 001
cert_ridgeSupport_source_3 131 13 281
end Papers.RationalityTen.RootedCaches.RootedSixExtra02
