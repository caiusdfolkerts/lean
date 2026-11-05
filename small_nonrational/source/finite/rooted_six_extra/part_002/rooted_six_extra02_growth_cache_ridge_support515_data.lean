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
def ridgeSupport515_000 : List Nat := [4,8,11,13,14,126,128,131,132,134,150,152,155,156,158,162,164,167,168,170,198,200,203,204,206,222,224,227,228,230,234,236]
def ridgeSupport515_001 : List Nat := [239,240,242,267,268,270,271,274,275,276,278,279,281,286,287,288,289,291,292,295,296,297,299,300,302,307,308,309,310,312,313,316]
def ridgeSupport515_002 : List Nat := [317,318,320,321,323,328,329,1392,1393,1398,1399,1404,1405,1406,1407,1408,1409,1410,1411,1416,1417,1422,1423,1428,1429,1430,1431,1432,1433,1434,1435,1454]
def ridgeSupport515_003 : List Nat := [1455,1456,1457,1458,1459,1478,1479,1480,1481,1482,1483,1502,1503,1504,1505,1506,1507,1526,1527,1528,1529,1530,1531,1550,1551,1552,1553,1554,1555,1574,1575,1576]
def ridgeSupport515_004 : List Nat := [1577,1578,1579,1580,1582,1586,1588,1592,1594,1598,1599,1600,1601,1602,1603,2184,2185,2196,2197,2220,2221,2232,2233,2240,2242,2246,2248,2256,2257,2268,2269,2292]
def ridgeSupport515_005 : List Nat := [2293,2304,2305,2312,2314,2318,2320,2328,2329,2340,2341,2364,2365,2376,2377,2384,2386,2390,2392,2952,2953,2964,2965,2988,2989,3000,3001,3008,3010,3014,3016,3024]
def ridgeSupport515_006 : List Nat := [3025,3036,3037,3060,3061,3072,3073,3080,3082,3086,3088,3096,3097,3108,3109,3132,3133,3144,3145,3152,3154,3158,3160,5136,5137,5140,5141,5142,5143,5178,5179,5184]
def ridgeSupport515_007 : List Nat := [5185,5190,5191,5226,5227,5232,5233,5238,5239,5366,5367,5368,5369,5370,5371,5870,5871,5872,5873,5874,5875,5876,5878,5882,5884,5886,5887,5888,5890,5894,5896,5898]
def ridgeSupport515_008 : List Nat := [5899,6020,6022,6026,6028,6038,6040,6044,6046,6056,6058,6062,6064,6188,6190,6194,6196,6206,6208,6212,6214,6224,6226,6230,6232]
def ridgeSupport515_code : Nat := 0x1858c2b614b0a1846c22610307d834c1960bb0597b0bd75eaaf5179ebce5e62f2d78cbc55e1af0970bb855c22e0d702b805bfedfd6fcb7d5bdade96f3b795bc6de16efb7753ee9f54f9a7c53de9ed477a3b51c68e146ba35511e88d441a2050ee875417a0b5056829411a0831618acc526283125890c3d61e3095848c1960c304181cc0a6043005800bf55fa2f757b8bd15e82f2178cbc25e02ee5770bad5d62e55728b895c425612ac9524a8252529093d49e249524891948c244121c90a48424052008f547a23751b88d1468232118c8c246022e51708ad4562255128889444190cc8464132018fcc7c63a31c18d0c6462e31618acc54629314189cc4c6133091844c2060f30717ecbf45f92fc17dcbec5e32f11784bc05df2ef172cb945c92e4171cb8c5b32d916c4b605af2d7166cb345992cc165cb2c5952ca163cb1c5892c4160cb045812c015fcafc57d2be15dcaec5712b805242901430a0850027c13d09e04e427013609a84d026612e09604ac2521280938490246121090047c23c11908b8458228113089043c21c10c08583c81e00ef07603a81cc0e407183801bc0ce066032c1900c605502a014e0a4051027813809b04c025810c08404182000fc00e006802c010004
def ridgeSupport515_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport515_code
def ridgeSupport515_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport515_code
def ridgeSupport515_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport515_code
def ridgeSupport515_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport515_code
def ridgeSupport515_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport515_code
def ridgeSupport515_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport515_code
def ridgeSupport515_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport515_code
def ridgeSupport515_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport515_code
def ridgeSupport515_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport515_code
def ridgeSupport515_rest_009 : Nat := PackedRawNatGrowth.drop 3653 ridgeSupport515_code
def ridgeSupport515_suffix_009 : List Nat := []
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
    (PackedRawNatGrowth.readList 13 281 ridgeSupport515_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
