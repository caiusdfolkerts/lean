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
def ridgeSupport259_000 : List Nat := [3,7,10,12,14,114,116,119,120,122,138,140,143,144,146,163,165,166,169,171,186,188,191,192,194,210,212,215,216,218,235,237]
def ridgeSupport259_001 : List Nat := [238,241,243,246,247,249,250,253,254,255,257,258,260,265,266,288,290,291,293,294,296,298,299,301,302,305,306,309,311,312,314,315]
def ridgeSupport259_002 : List Nat := [317,319,320,322,323,326,327,1390,1391,1396,1397,1400,1401,1402,1403,1404,1405,1410,1411,1414,1415,1420,1421,1424,1425,1426,1427,1428,1429,1434,1435,1448]
def ridgeSupport259_003 : List Nat := [1449,1450,1451,1452,1453,1472,1473,1474,1475,1476,1477,1496,1497,1498,1499,1500,1501,1520,1521,1522,1523,1524,1525,1544,1545,1546,1547,1548,1549,1568,1569,1570]
def ridgeSupport259_004 : List Nat := [1571,1572,1573,1581,1584,1587,1590,1592,1593,1594,1595,1596,1597,1598,1600,2112,2113,2124,2125,2148,2149,2160,2161,2168,2170,2174,2176,2254,2255,2266,2267,2290]
def ridgeSupport259_005 : List Nat := [2291,2302,2303,2313,2316,2319,2322,2326,2327,2338,2339,2362,2363,2374,2375,2385,2388,2391,2394,2880,2881,2892,2893,2916,2917,2928,2929,2936,2938,2942,2944,3022]
def ridgeSupport259_006 : List Nat := [3023,3034,3035,3058,3059,3070,3071,3081,3084,3087,3090,3094,3095,3106,3107,3130,3131,3142,3143,3153,3156,3159,3162,5134,5135,5138,5139,5142,5143,5172,5173,5182]
def ridgeSupport259_007 : List Nat := [5183,5188,5189,5220,5221,5230,5231,5236,5237,5360,5361,5362,5363,5364,5365,5864,5865,5866,5867,5868,5869,5877,5880,5883,5885,5886,5887,5889,5892,5895,5897,5898]
def ridgeSupport259_008 : List Nat := [5899,6002,6004,6008,6010,6039,6042,6045,6048,6057,6060,6063,6066,6170,6172,6176,6178,6207,6210,6213,6216,6225,6228,6231,6234]
def ridgeSupport259_code : Nat := 0x185ac2be1530a3848c22e10b07f822c1060730357b2bd7deb2f537a0bcede6af2f77abbc5dd2ee570bb855c26e0f704b80dbfedfd6fdb7ddbe2deb6edb765baedd56e9b7453d69e94f3a7953c69e1475a3a51be8dd465a32511688943fa1f50d6869417a0b504e82540fa0731698aec54628b11d88cc3b61d308d844c1760b304981ec0c604affd7fcbf35f92f6d7b4bcf5e72e016fcb7a5bc2dc56e0b655b22d35698b415a025692ae9544a8a51d28c93b49d248d24491748b244921e90c484a3fd1fc8f3479236d1b48cf46722010fc87a43c21c50e086543221350988414201900c7c63d31e18ecc7463931c18d8c666303169894c486233111884c4060d306182cc1460930417d4be85f32f917c4be05dd2ee176cbb45d92ec1714b885c32e11704b805ad2d616acb545a92d4166cb345952ca164cb245912c81634b185872c3160cb0457d2be15ecaf45792bc15d4ae856f2b7051c28c1430a1050027e13d09d84e827013709a84c826212e09684ac2541280930494246122090042821210408104041fe0fe07e83e81f20f707b03cc1e20ee07683ac1b40d806b83501a40c206002fc1780ba05582a414c0a5051824812008f04602280f407803b81d00e400e006002800e003
def ridgeSupport259_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport259_code
def ridgeSupport259_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport259_code
def ridgeSupport259_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport259_code
def ridgeSupport259_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport259_code
def ridgeSupport259_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport259_code
def ridgeSupport259_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport259_code
def ridgeSupport259_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport259_code
def ridgeSupport259_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport259_code
def ridgeSupport259_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport259_code
def ridgeSupport259_rest_009 : Nat := PackedRawNatGrowth.drop 3653 ridgeSupport259_code
def ridgeSupport259_suffix_009 : List Nat := []
def ridgeSupport259_suffix_008 : List Nat := ridgeSupport259_008 ++ ridgeSupport259_suffix_009
def ridgeSupport259_suffix_007 : List Nat := ridgeSupport259_007 ++ ridgeSupport259_suffix_008
def ridgeSupport259_suffix_006 : List Nat := ridgeSupport259_006 ++ ridgeSupport259_suffix_007
def ridgeSupport259_suffix_005 : List Nat := ridgeSupport259_005 ++ ridgeSupport259_suffix_006
def ridgeSupport259_suffix_004 : List Nat := ridgeSupport259_004 ++ ridgeSupport259_suffix_005
def ridgeSupport259_suffix_003 : List Nat := ridgeSupport259_003 ++ ridgeSupport259_suffix_004
def ridgeSupport259_suffix_002 : List Nat := ridgeSupport259_002 ++ ridgeSupport259_suffix_003
def ridgeSupport259_suffix_001 : List Nat := ridgeSupport259_001 ++ ridgeSupport259_suffix_002
def ridgeSupport259_suffix_000 : List Nat := ridgeSupport259_000 ++ ridgeSupport259_suffix_001
theorem ridgeSupport259_source : candidateSupports 259 =
    (PackedRawNatGrowth.readList 13 281 ridgeSupport259_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
