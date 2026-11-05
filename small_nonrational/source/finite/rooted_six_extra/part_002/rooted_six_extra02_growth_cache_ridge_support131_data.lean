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
def ridgeSupport131_000 : List Nat := [2,6,9,12,13,102,104,107,108,110,139,141,142,145,147,151,153,154,157,159,174,176,179,180,182,211,213,214,217,219,223,225]
def ridgeSupport131_001 : List Nat := [226,229,231,246,248,249,251,252,254,256,257,259,260,263,264,267,269,270,272,273,275,277,278,280,281,284,285,310,311,313,314,315]
def ridgeSupport131_002 : List Nat := [316,318,319,321,322,324,325,1388,1389,1394,1395,1396,1397,1398,1399,1402,1403,1408,1409,1412,1413,1418,1419,1420,1421,1422,1423,1426,1427,1432,1433,1442]
def ridgeSupport131_003 : List Nat := [1443,1444,1445,1446,1447,1466,1467,1468,1469,1470,1471,1490,1491,1492,1493,1494,1495,1514,1515,1516,1517,1518,1519,1538,1539,1540,1541,1542,1543,1562,1563,1564]
def ridgeSupport131_004 : List Nat := [1565,1566,1567,1583,1585,1586,1587,1588,1589,1590,1591,1593,1596,1599,1602,2110,2111,2122,2123,2146,2147,2158,2159,2169,2172,2175,2178,2182,2183,2194,2195,2218]
def ridgeSupport131_005 : List Nat := [2219,2230,2231,2241,2244,2247,2250,2324,2325,2336,2337,2360,2361,2372,2373,2387,2389,2393,2395,2878,2879,2890,2891,2914,2915,2926,2927,2937,2940,2943,2946,2950]
def ridgeSupport131_006 : List Nat := [2951,2962,2963,2986,2987,2998,2999,3009,3012,3015,3018,3092,3093,3104,3105,3128,3129,3140,3141,3155,3157,3161,3163,5132,5133,5138,5139,5140,5141,5170,5171,5176]
def ridgeSupport131_007 : List Nat := [5177,5186,5187,5218,5219,5224,5225,5234,5235,5354,5355,5356,5357,5358,5359,5858,5859,5860,5861,5862,5863,5879,5881,5882,5883,5884,5885,5891,5893,5894,5895,5896]
def ridgeSupport131_008 : List Nat := [5897,6003,6006,6009,6012,6021,6024,6027,6030,6059,6061,6065,6067,6171,6174,6177,6180,6189,6192,6195,6198,6227,6229,6233,6235]
def ridgeSupport131_code : Nat := 0x185bc2ce1570a7836c19e0c305b824c10e07b0377b3bd8deb6f5778ebc5de22f0b77cbbcdddaee7709b845c1ee0d705b81dbf6df96fbb7d5be6def6e7b735b96dc96e3b7153be9dd4eda7653ae9d5473a3951a68d1463a31510e885439a1c50ce865415a0a504e82540da06316d8b2c55629b115888c3961c3085840c1560a2f2978ebc45e0aedd76cbab5d52e4d724b875c32e096feb7c5bcadbd6dcb635b12d2d694b3f59f256d2b29554a9a51528893949c248524091548a232918e8c4460a2dd16c8ab455224d12488744322090fe87c43ca1bd0dc863431212d09483f41f1908c7e63c31c98dcc6c63531a18ccc64631317987cc3c61d30e186cc346073031814c0860330117bcbdc5ed2f617acbd45d72eb1754ba85d32e916fcb7c5bd2de16ecb745a72d31694b485a32d11664b305932c9163cb1c58d2c6162cb145852c21604b0057b2bd15dcaec5752ba15ccae456d2b605142881420a084fc27c13c09d84e827213709b047423811908c045822a113088844021c10d085842020e10408184042000fe07e03ec1f20f807b039c1ca0e2070837c1b60d906b03541a60b605a02cc1600ae04f827413409904b824c12208e046822c0dc06c03581a00cc00d006002400c002
def ridgeSupport131_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport131_code
def ridgeSupport131_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport131_code
def ridgeSupport131_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport131_code
def ridgeSupport131_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport131_code
def ridgeSupport131_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport131_code
def ridgeSupport131_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport131_code
def ridgeSupport131_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport131_code
def ridgeSupport131_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport131_code
def ridgeSupport131_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport131_code
def ridgeSupport131_rest_009 : Nat := PackedRawNatGrowth.drop 3653 ridgeSupport131_code
def ridgeSupport131_suffix_009 : List Nat := []
def ridgeSupport131_suffix_008 : List Nat := ridgeSupport131_008 ++ ridgeSupport131_suffix_009
def ridgeSupport131_suffix_007 : List Nat := ridgeSupport131_007 ++ ridgeSupport131_suffix_008
def ridgeSupport131_suffix_006 : List Nat := ridgeSupport131_006 ++ ridgeSupport131_suffix_007
def ridgeSupport131_suffix_005 : List Nat := ridgeSupport131_005 ++ ridgeSupport131_suffix_006
def ridgeSupport131_suffix_004 : List Nat := ridgeSupport131_004 ++ ridgeSupport131_suffix_005
def ridgeSupport131_suffix_003 : List Nat := ridgeSupport131_003 ++ ridgeSupport131_suffix_004
def ridgeSupport131_suffix_002 : List Nat := ridgeSupport131_002 ++ ridgeSupport131_suffix_003
def ridgeSupport131_suffix_001 : List Nat := ridgeSupport131_001 ++ ridgeSupport131_suffix_002
def ridgeSupport131_suffix_000 : List Nat := ridgeSupport131_000 ++ ridgeSupport131_suffix_001
theorem ridgeSupport131_source : candidateSupports 131 =
    (PackedRawNatGrowth.readList 13 281 ridgeSupport131_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
