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
def ridgeSupport641_000 : List Nat := [13,19,25,28,30,152,153,154,155,156,157,224,225,226,227,228,229,267,271,272,273,274,276,277,284,286,310,312,314,315,317,319]
def ridgeSupport641_001 : List Nat := [320,324,329,355,359,360,361,362,364,365,372,374,398,400,402,403,405,407,408,412,417,439,443,444,445,446,448,449,456,458,482,484]
def ridgeSupport641_002 : List Nat := [486,487,489,491,492,496,501,502,504,506,508,509,511,513,514,518,520,525,526,1412,1417,1426,1428,1446,1447,1456,1457,1494,1495,1504,1505,1510]
def ridgeSupport641_003 : List Nat := [1511,1514,1516,1520,1521,1527,1530,1532,1537,1542,1543,1546,1548,1552,1553,1590,1591,1600,1601,1614,1615,1624,1625,1652,1657,1666,1668,1686,1687,1696,1697,1734]
def ridgeSupport641_004 : List Nat := [1735,1744,1745,1750,1751,1754,1756,1760,1761,1767,1770,1772,1777,1782,1783,1786,1788,1792,1793,1830,1831,1840,1841,1854,1855,1864,1865,2194,2196,2206,2208,2234]
def ridgeSupport641_005 : List Nat := [2235,2246,2247,2336,2341,2348,2353,2380,2381,2392,2393,2420,2425,2434,2436,2454,2455,2464,2465,2502,2503,2512,2513,2518,2519,2522,2524,2528,2529,2535,2538,2540]
def ridgeSupport641_006 : List Nat := [2545,2550,2551,2554,2556,2560,2561,2598,2599,2608,2609,2622,2623,2632,2633,2962,2964,2974,2976,3002,3003,3014,3015,3104,3109,3116,3121,3148,3149,3160,3161,3714]
def ridgeSupport641_007 : List Nat := [3715,3718,3719,5144,5149,5150,5154,5166,5167,5176,5177,5182,5183,5186,5188,5192,5193,5199,5202,5204,5209,5214,5215,5218,5220,5224,5225,5230,5231,5240,5241,5256]
def ridgeSupport641_008 : List Nat := [5257,5261,5263,5276,5281,5282,5286,5298,5299,5308,5309,5314,5315,5318,5320,5324,5325,5331,5334,5336,5341,5346,5347,5350,5352,5356,5357,5362,5363,5372,5373,5388]
def ridgeSupport641_009 : List Nat := [5389,5393,5395,5596,5598,5600,5601,5608,5610,5612,5613,5621,5623,5627,5629,5702,5707,5710,5711,5714,5719,5722,5723,5727,5730,5733,5736,5756,5761,5762,5766,5778]
def ridgeSupport641_010 : List Nat := [5779,5788,5789,5794,5795,5798,5800,5804,5805,5811,5814,5816,5821,5826,5827,5830,5832,5836,5837,5842,5843,5852,5853,5868,5869,5873,5875,6076,6078,6080,6081,6088]
def ridgeSupport641_011 : List Nat := [6090,6092,6093,6101,6103,6107,6109,6182,6187,6190,6191,6194,6199,6202,6203,6207,6210,6213,6216,6506,6507,7365,7368,7371,7375,7377,7380,7383,7387,7409,7411,7419]
def ridgeSupport641_012 : List Nat := [7422,7425,7428,7431,7435,7457,7459,7467,7470,7612,7613,7648,7649,7744,7745]
def ridgeSupport641_code : Nat := 0x7907c81de1ef076f7b79d2ee95f48fa43d0be83f413a03cfee7df3cf9e3cdbe6bf3539a3ccfe65f32398b96bcb5612308b842c1fe0ef075837c1960bf05d82bc135f76fb77d7beadf36f997cabe45f06f817bebde5bcede36edb765b76db96d3b695b36d996c8b635b0ed856bdb5c5adad676adb565aa2d4d6a3b515a76d39693b495a1ad05681b3e59a2ccb662b2fd96ecb5657b29593ec9d64bb2357f6bf75f7afad7b6bd95eaaf45786bc15deaee544ea2350da8653f69f94f3a7953b69d94e8a73538e9c54dda6c535a9a74cda66532298d4c3a6152f69794b3a59529a9454a1a4e523e91b489a4451e68f146fa3751a68d1464a31517e8bd459a2a514a89f449a24511288543fa1f50e687142fa17508a83d41da0c3a1dd0ce8374131658b0c4d62630c5858c256102f1d78cbbb5dd2e8173cb945c92925490a3f51f28c5460a2751328054009fc4fd27dd3ec9f14f627a93ce9e14f027713b49d74eb27453a09c74e326853409974cb26113049794ba25652b094d4a624c5258925490231d18c8bb45d228113c8944491d24e9073f39f1cc4e607273931c04e006fc37d1bdcdec6f13761ba8dce6e13701b70db46d736b1b44da06c73631a84d4069734b1a10d0467933a1964cb064f3271904c8063731b1844c2060c305181cc0c6012fe17e8bee5f12f817b0bd45e72f31784bc05d72eb16c4b605a72d31650b245892c2083841a20810308084021ff0fe87f03f41f80fb07d43e01ec0f587a43ce1e60f207883941c80e0870037c1bd0de06ec36e1a10ce066032e1950c9864832018e0bb05d02da16c0b505a42d01670b1852428814009f84f427613a09c04d823c11c08a8450224111088043c2160e5072038c1c40e1070027413809b04d026413001e00e006402600d
def ridgeSupport641_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport641_code
def ridgeSupport641_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport641_code
def ridgeSupport641_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport641_code
def ridgeSupport641_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport641_code
def ridgeSupport641_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport641_code
def ridgeSupport641_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport641_code
def ridgeSupport641_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport641_code
def ridgeSupport641_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport641_code
def ridgeSupport641_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport641_code
def ridgeSupport641_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport641_code
def ridgeSupport641_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport641_code
def ridgeSupport641_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport641_code
def ridgeSupport641_rest_012 : Nat := PackedRawNatGrowth.drop 4992 ridgeSupport641_code
def ridgeSupport641_rest_013 : Nat := PackedRawNatGrowth.drop 5187 ridgeSupport641_code
def ridgeSupport641_suffix_013 : List Nat := []
def ridgeSupport641_suffix_012 : List Nat := ridgeSupport641_012 ++ ridgeSupport641_suffix_013
def ridgeSupport641_suffix_011 : List Nat := ridgeSupport641_011 ++ ridgeSupport641_suffix_012
def ridgeSupport641_suffix_010 : List Nat := ridgeSupport641_010 ++ ridgeSupport641_suffix_011
def ridgeSupport641_suffix_009 : List Nat := ridgeSupport641_009 ++ ridgeSupport641_suffix_010
def ridgeSupport641_suffix_008 : List Nat := ridgeSupport641_008 ++ ridgeSupport641_suffix_009
def ridgeSupport641_suffix_007 : List Nat := ridgeSupport641_007 ++ ridgeSupport641_suffix_008
def ridgeSupport641_suffix_006 : List Nat := ridgeSupport641_006 ++ ridgeSupport641_suffix_007
def ridgeSupport641_suffix_005 : List Nat := ridgeSupport641_005 ++ ridgeSupport641_suffix_006
def ridgeSupport641_suffix_004 : List Nat := ridgeSupport641_004 ++ ridgeSupport641_suffix_005
def ridgeSupport641_suffix_003 : List Nat := ridgeSupport641_003 ++ ridgeSupport641_suffix_004
def ridgeSupport641_suffix_002 : List Nat := ridgeSupport641_002 ++ ridgeSupport641_suffix_003
def ridgeSupport641_suffix_001 : List Nat := ridgeSupport641_001 ++ ridgeSupport641_suffix_002
def ridgeSupport641_suffix_000 : List Nat := ridgeSupport641_000 ++ ridgeSupport641_suffix_001
theorem ridgeSupport641_source : candidateSupports 641 =
    (PackedRawNatGrowth.readList 13 399 ridgeSupport641_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
