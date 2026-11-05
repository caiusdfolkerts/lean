module
prelude
public import RootedSixBase02GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport131_000 : List Nat := [2,6,9,12,13,102,104,107,108,110,139,141,142,145,147,151,153,154,157,159,174,176,179,180,182,211,213,214,217,219,223,225]
def ridgeSupport131_001 : List Nat := [226,229,231,246,248,249,251,252,254,256,257,259,260,263,264,267,269,270,272,273,275,277,278,280,281,284,285,310,311,313,314,315]
def ridgeSupport131_002 : List Nat := [316,318,319,321,322,324,325,1388,1389,1394,1395,1396,1397,1398,1399,1402,1403,1408,1409,1412,1413,1418,1419,1420,1421,1422,1423,1426,1427,1432,1433,1442]
def ridgeSupport131_003 : List Nat := [1443,1444,1445,1446,1447,1466,1467,1468,1469,1470,1471,1490,1491,1492,1493,1494,1495,1514,1515,1516,1517,1518,1519,1538,1539,1540,1541,1542,1543,1562,1563,1564]
def ridgeSupport131_004 : List Nat := [1565,1566,1567,1583,1585,1586,1587,1588,1589,1590,1591,1593,1596,1599,1602,2110,2111,2122,2123,2146,2147,2158,2159,2169,2172,2175,2178,2182,2183,2194,2195,2218]
def ridgeSupport131_005 : List Nat := [2219,2230,2231,2241,2244,2247,2250,2324,2325,2336,2337,2360,2361,2372,2373,2387,2389,2393,2395,2878,2879,2890,2891,2914,2915,2926,2927,2937,2940,2943,2946,2950]
def ridgeSupport131_006 : List Nat := [2951,2962,2963,2986,2987,2998,2999,3009,3012,3015,3018,3092,3093,3104,3105,3128,3129,3140,3141,3155,3157,3161,3163,5132,5133,5138,5139,5140,5141,5144,5145,5150]
def ridgeSupport131_007 : List Nat := [5151,5152,5153,5162,5163,5164,5165,5166,5167,5186,5187,5188,5189,5190,5191,5207,5209,5210,5211,5212,5213,5214,5215,5217,5220,5223,5226,5231,5233,5234,5235,5236]
def ridgeSupport131_008 : List Nat := [5237,5238,5239,5241,5244,5247,5250,5252,5253,5258,5260,5261,5263,5530,5531,5542,5543,5553,5556,5559,5562,5566,5567,5570,5575,5578,5579,5584,5585,5596,5597,5607]
def ridgeSupport131_009 : List Nat := [5610,5613,5616,5620,5621,5624,5629,5632,5633,5690,5691,5702,5703,5717,5719,5723,5725,5726,5727,5734,5736,5738,5739,6010,6011,6022,6023,6033,6036,6039,6042,6046]
def ridgeSupport131_010 : List Nat := [6047,6050,6055,6058,6059,6064,6065,6076,6077,6087,6090,6093,6096,6100,6101,6104,6109,6112,6113,6170,6171,6182,6183,6197,6199,6203,6205,6206,6207,6214,6216,6218]
def ridgeSupport131_011 : List Nat := [6219,7364,7365,7370,7371,7372,7373,7402,7403,7408,7409,7418,7419,7450,7451,7456,7457,7466,7467,7586,7587,7588,7589,7590,7591]
def ridgeSupport131_code : Nat := 0x1da7ed37697b49da3ed174afa55d21e90746fa35cfbe7d73c79e1cebe757337999ccbe65731798984bc25612308d83fc1f60f7077837c1ae09f04d81bc0d5f86fc17ddbec5f56fa97d0be6df2af8f7bdbde5ec6f617abbd55e9ef4579fbcf5e6af2f794bc8de1ef0d77bbbd59aecd5668b33597ecbd65db2dd95ecab647b2358eec75601b0057f6bf15f5afa57c2bdb5eaaf3d776bb95d1ae8572eb955c7ae156feb7d5baadbd6d2b635a7ad3566eb3548fa46d232915485a42520a8ff47ca3cd1de8ed475a3a51ce8e5471a37d1aa8cf464a30d17e8bd45da2e516e8b5459a2bd11e88d445a22510e88542fa1750b685942ba15508684141fa0f5066831415a0a504e82540da06316d8b2c55629b115888c3961c3085840c1560a2f2978ebc45e0aedd76cbab5d52e4d724b875c32e096feb7c5bcadbd6dcb635b12d2d694b3f59f256d2b29554a9a51528893949c248524091548a232918e8c4460a2dd16c8ab455224d12488744322090fe87c43ca1bd0dc863431212d09483f41f1908c7e63c31c98dcc6c63531a18ccc64631317987cc3c61d30e186cc346073031814c0860330117bcbdc5ed2f617acbd45d72eb1754ba85d32e916fcb7c5bd2de16ecb745a72d31694b485a32d11664b305932c9163cb1c58d2c6162cb145852c21604b0057b2bd15dcaec5752ba15ccae456d2b605142881420a084fc27c13c09d84e827213709b047423811908c045822a113088844021c10d085842020e10408184042000fe07e03ec1f20f807b039c1ca0e2070837c1b60d906b03541a60b605a02cc1600ae04f827413409904b824c12208e046822c0dc06c03581a00cc00d006002400c002
def ridgeSupport131_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport131_code
def ridgeSupport131_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport131_code
def ridgeSupport131_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport131_code
def ridgeSupport131_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport131_code
def ridgeSupport131_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport131_code
def ridgeSupport131_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport131_code
def ridgeSupport131_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport131_code
def ridgeSupport131_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport131_code
def ridgeSupport131_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport131_code
def ridgeSupport131_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport131_code
def ridgeSupport131_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport131_code
def ridgeSupport131_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport131_code
def ridgeSupport131_rest_012 : Nat := PackedRawNatGrowth.drop 4901 ridgeSupport131_code
def ridgeSupport131_suffix_012 : List Nat := []
def ridgeSupport131_suffix_011 : List Nat := ridgeSupport131_011 ++ ridgeSupport131_suffix_012
def ridgeSupport131_suffix_010 : List Nat := ridgeSupport131_010 ++ ridgeSupport131_suffix_011
def ridgeSupport131_suffix_009 : List Nat := ridgeSupport131_009 ++ ridgeSupport131_suffix_010
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
    (PackedRawNatGrowth.readList 13 377 ridgeSupport131_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
