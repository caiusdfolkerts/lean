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
def ridgeSupport641_000 : List Nat := [13,19,25,28,30,152,153,154,155,156,157,224,225,226,227,228,229,267,271,272,273,274,276,277,284,286,310,312,314,315,317,319]
def ridgeSupport641_001 : List Nat := [320,324,329,355,359,360,361,362,364,365,372,374,398,400,402,403,405,407,408,412,417,439,443,444,445,446,448,449,456,458,482,484]
def ridgeSupport641_002 : List Nat := [486,487,489,491,492,496,501,502,504,506,508,509,511,513,514,518,520,525,526,1412,1417,1426,1428,1446,1447,1456,1457,1494,1495,1504,1505,1510]
def ridgeSupport641_003 : List Nat := [1511,1514,1516,1520,1521,1527,1530,1532,1537,1542,1543,1546,1548,1552,1553,1590,1591,1600,1601,1614,1615,1624,1625,1652,1657,1666,1668,1686,1687,1696,1697,1734]
def ridgeSupport641_004 : List Nat := [1735,1744,1745,1750,1751,1754,1756,1760,1761,1767,1770,1772,1777,1782,1783,1786,1788,1792,1793,1830,1831,1840,1841,1854,1855,1864,1865,2194,2196,2206,2208,2234]
def ridgeSupport641_005 : List Nat := [2235,2246,2247,2336,2341,2348,2353,2380,2381,2392,2393,2420,2425,2434,2436,2454,2455,2464,2465,2502,2503,2512,2513,2518,2519,2522,2524,2528,2529,2535,2538,2540]
def ridgeSupport641_006 : List Nat := [2545,2550,2551,2554,2556,2560,2561,2598,2599,2608,2609,2622,2623,2632,2633,2962,2964,2974,2976,3002,3003,3014,3015,3104,3109,3116,3121,3148,3149,3160,3161,3714]
def ridgeSupport641_007 : List Nat := [3715,3718,3719,5133,5136,5139,5143,5145,5148,5151,5155,5177,5179,5187,5190,5193,5196,5199,5203,5225,5227,5235,5238,5380,5381,5416,5417,5512,5513,5858,5860,5871]
def ridgeSupport641_008 : List Nat := [5874,5889,5890,5891,5892,5897,5898,5906,5908,5919,5922,5937,5938,5939,5940,5945,5946,6026,6027,6029,6031,6063,6064,6065,6066,6074,6076,6087,6090,6105,6106,6107]
def ridgeSupport641_009 : List Nat := [6108,6113,6114,6194,6195,6197,6199,6231,6232,6233,6234]
def ridgeSupport641_code : Nat := 0x616b0b3858c2be0df06b833c195f8afc37dcbeddf6afb37cabe3def2f757b2bd8dec2f5f78fbc6de2ef1573ab9cdcd2e67732b98dc8ae3f714b895c2ae13704b81dc0ae036f2b77db92dc5589ac454a6a51505a8251da8e746ba34d14e89f44ca24d11a88743ba1cd08e83f41ca0cd05e827410a06ba1dd0ce8374131658b0c4d62630c5858c256102f1d78cbbb5dd2e8173cb945c92925490a3f51f28c5460a2751328054009fc4fd27dd3ec9f14f627a93ce9e14f027713b49d74eb27453a09c74e326853409974cb26113049794ba25652b094d4a624c5258925490231d18c8bb45d228113c8944491d24e9073f39f1cc4e607273931c04e006fc37d1bdcdec6f13761ba8dce6e13701b70db46d736b1b44da06c73631a84d4069734b1a10d0467933a1964cb064f3271904c8063731b1844c2060c305181cc0c6012fe17e8bee5f12f817b0bd45e72f31784bc05d72eb16c4b605a72d31650b245892c2083841a20810308084021ff0fe87f03f41f80fb07d43e01ec0f587a43ce1e60f207883941c80e0870037c1bd0de06ec36e1a10ce066032e1950c9864832018e0bb05d02da16c0b505a42d01670b1852428814009f84f427613a09c04d823c11c08a8450224111088043c2160e5072038c1c40e1070027413809b04d026413001e00e006402600d
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
def ridgeSupport641_rest_010 : Nat := PackedRawNatGrowth.drop 3887 ridgeSupport641_code
def ridgeSupport641_suffix_010 : List Nat := []
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
    (PackedRawNatGrowth.readList 13 299 ridgeSupport641_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
