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
def ridgeSupport515_000 : List Nat := [4,8,11,13,14,126,128,131,132,134,150,152,155,156,158,162,164,167,168,170,198,200,203,204,206,222,224,227,228,230,234,236]
def ridgeSupport515_001 : List Nat := [239,240,242,267,268,270,271,274,275,276,278,279,281,286,287,288,289,291,292,295,296,297,299,300,302,307,308,309,310,312,313,316]
def ridgeSupport515_002 : List Nat := [317,318,320,321,323,328,329,1392,1393,1398,1399,1404,1405,1406,1407,1408,1409,1410,1411,1416,1417,1422,1423,1428,1429,1430,1431,1432,1433,1434,1435,1454]
def ridgeSupport515_003 : List Nat := [1455,1456,1457,1458,1459,1478,1479,1480,1481,1482,1483,1502,1503,1504,1505,1506,1507,1526,1527,1528,1529,1530,1531,1550,1551,1552,1553,1554,1555,1574,1575,1576]
def ridgeSupport515_004 : List Nat := [1577,1578,1579,1580,1582,1586,1588,1592,1594,1598,1599,1600,1601,1602,1603,2184,2185,2196,2197,2220,2221,2232,2233,2240,2242,2246,2248,2256,2257,2268,2269,2292]
def ridgeSupport515_005 : List Nat := [2293,2304,2305,2312,2314,2318,2320,2328,2329,2340,2341,2364,2365,2376,2377,2384,2386,2390,2392,2952,2953,2964,2965,2988,2989,3000,3001,3008,3010,3014,3016,3024]
def ridgeSupport515_006 : List Nat := [3025,3036,3037,3060,3061,3072,3073,3080,3082,3086,3088,3096,3097,3108,3109,3132,3133,3144,3145,3152,3154,3158,3160,5136,5137,5140,5141,5142,5143,5148,5149,5152]
def ridgeSupport515_007 : List Nat := [5153,5154,5155,5174,5175,5176,5177,5178,5179,5198,5199,5200,5201,5202,5203,5204,5206,5210,5212,5216,5218,5222,5223,5224,5225,5226,5227,5228,5230,5234,5236,5240]
def ridgeSupport515_008 : List Nat := [5242,5246,5247,5248,5249,5250,5251,5253,5254,5256,5257,5259,5260,5586,5587,5598,5599,5606,5608,5612,5614,5622,5623,5625,5627,5634,5635,5640,5641,5652,5653,5660]
def ridgeSupport515_009 : List Nat := [5662,5666,5668,5676,5677,5679,5681,5688,5689,5694,5695,5706,5707,5714,5716,5720,5722,5730,5731,5733,5735,5742,5743,6066,6067,6078,6079,6086,6088,6092,6094,6102]
def ridgeSupport515_010 : List Nat := [6103,6105,6107,6114,6115,6120,6121,6132,6133,6140,6142,6146,6148,6156,6157,6159,6161,6168,6169,6174,6175,6186,6187,6194,6196,6200,6202,6210,6211,6213,6215,6222]
def ridgeSupport515_011 : List Nat := [6223,7368,7369,7372,7373,7374,7375,7410,7411,7416,7417,7422,7423,7458,7459,7464,7465,7470,7471,7598,7599,7600,7601,7602,7603]
def ridgeSupport515_code : Nat := 0x1db3ed976c7b61dafed774bfa5dd29e94748fa45cffe7f73e79f1cf3e79733f99dccde66732799184fc27611f08b843c2160eb071834c1960af05581fc0f6067031811c07e037019804c015ffaff97f5bfa5fa6fd17e3bf15f6efb37d7beb5f3af997c8be35efef7d7b3bd959becdd667b32d98ecc565ab2c5952ca564bb2558fec7d639b1c58c6c5f62db165892c4561eb0e5856c29609b04580ec055fbafcd7debed5eeaf657a2bcd5dfaef574eba548ca45d226911486a42d20e905481a4051fe8fd47aa3c51d28e546ea3651ae8d5469a34519e8cd462a3051728b5456a2a514e8a5451a28513e89d43ba1d50e6871437a1b508e845421a105076839417a0b5056829411a0831618acc526283125890c3d61e3095848c1960c304181cc0a6043005800bf55fa2f757b8bd15e82f2178cbc25e02ee5770bad5d62e55728b895c425612ac9524a8252529093d49e249524891948c244121c90a48424052008f547a23751b88d1468232118c8c246022e51708ad4562255128889444190cc8464132018fcc7c63a31c18d0c6462e31618acc54629314189cc4c6133091844c2060f30717ecbf45f92fc17dcbec5e32f11784bc05df2ef172cb945c92e4171cb8c5b32d916c4b605af2d7166cb345992cc165cb2c5952ca163cb1c5892c4160cb045812c015fcafc57d2be15dcaec5712b805242901430a0850027c13d09e04e427013609a84d026612e09604ac2521280938490246121090047c23c11908b8458228113089043c21c10c08583c81e00ef07603a81cc0e407183801bc0ce066032c1900c605502a014e0a4051027813809b04c025810c08404182000fc00e006802c010004
def ridgeSupport515_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport515_code
def ridgeSupport515_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport515_code
def ridgeSupport515_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport515_code
def ridgeSupport515_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport515_code
def ridgeSupport515_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport515_code
def ridgeSupport515_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport515_code
def ridgeSupport515_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport515_code
def ridgeSupport515_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport515_code
def ridgeSupport515_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport515_code
def ridgeSupport515_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport515_code
def ridgeSupport515_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport515_code
def ridgeSupport515_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport515_code
def ridgeSupport515_rest_012 : Nat := PackedRawNatGrowth.drop 4901 ridgeSupport515_code
def ridgeSupport515_suffix_012 : List Nat := []
def ridgeSupport515_suffix_011 : List Nat := ridgeSupport515_011 ++ ridgeSupport515_suffix_012
def ridgeSupport515_suffix_010 : List Nat := ridgeSupport515_010 ++ ridgeSupport515_suffix_011
def ridgeSupport515_suffix_009 : List Nat := ridgeSupport515_009 ++ ridgeSupport515_suffix_010
def ridgeSupport515_suffix_008 : List Nat := ridgeSupport515_008 ++ ridgeSupport515_suffix_009
def ridgeSupport515_suffix_007 : List Nat := ridgeSupport515_007 ++ ridgeSupport515_suffix_008
def ridgeSupport515_suffix_006 : List Nat := ridgeSupport515_006 ++ ridgeSupport515_suffix_007
def ridgeSupport515_suffix_005 : List Nat := ridgeSupport515_005 ++ ridgeSupport515_suffix_006
def ridgeSupport515_suffix_004 : List Nat := ridgeSupport515_004 ++ ridgeSupport515_suffix_005
def ridgeSupport515_suffix_003 : List Nat := ridgeSupport515_003 ++ ridgeSupport515_suffix_004
def ridgeSupport515_suffix_002 : List Nat := ridgeSupport515_002 ++ ridgeSupport515_suffix_003
def ridgeSupport515_suffix_001 : List Nat := ridgeSupport515_001 ++ ridgeSupport515_suffix_002
def ridgeSupport515_suffix_000 : List Nat := ridgeSupport515_000 ++ ridgeSupport515_suffix_001
theorem ridgeSupport515_source : candidateSupports 515 =
    (PackedRawNatGrowth.readList 13 377 ridgeSupport515_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
