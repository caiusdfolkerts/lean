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
def ridgeSupport259_000 : List Nat := [3,7,10,12,14,114,116,119,120,122,138,140,143,144,146,163,165,166,169,171,186,188,191,192,194,210,212,215,216,218,235,237]
def ridgeSupport259_001 : List Nat := [238,241,243,246,247,249,250,253,254,255,257,258,260,265,266,288,290,291,293,294,296,298,299,301,302,305,306,309,311,312,314,315]
def ridgeSupport259_002 : List Nat := [317,319,320,322,323,326,327,1390,1391,1396,1397,1400,1401,1402,1403,1404,1405,1410,1411,1414,1415,1420,1421,1424,1425,1426,1427,1428,1429,1434,1435,1448]
def ridgeSupport259_003 : List Nat := [1449,1450,1451,1452,1453,1472,1473,1474,1475,1476,1477,1496,1497,1498,1499,1500,1501,1520,1521,1522,1523,1524,1525,1544,1545,1546,1547,1548,1549,1568,1569,1570]
def ridgeSupport259_004 : List Nat := [1571,1572,1573,1581,1584,1587,1590,1592,1593,1594,1595,1596,1597,1598,1600,2112,2113,2124,2125,2148,2149,2160,2161,2168,2170,2174,2176,2254,2255,2266,2267,2290]
def ridgeSupport259_005 : List Nat := [2291,2302,2303,2313,2316,2319,2322,2326,2327,2338,2339,2362,2363,2374,2375,2385,2388,2391,2394,2880,2881,2892,2893,2916,2917,2928,2929,2936,2938,2942,2944,3022]
def ridgeSupport259_006 : List Nat := [3023,3034,3035,3058,3059,3070,3071,3081,3084,3087,3090,3094,3095,3106,3107,3130,3131,3142,3143,3153,3156,3159,3162,5134,5135,5138,5139,5142,5143,5146,5147,5150]
def ridgeSupport259_007 : List Nat := [5151,5154,5155,5168,5169,5170,5171,5172,5173,5192,5193,5194,5195,5196,5197,5205,5208,5211,5214,5216,5217,5218,5219,5220,5221,5222,5224,5229,5232,5235,5238,5240]
def ridgeSupport259_008 : List Nat := [5241,5242,5243,5244,5245,5246,5248,5252,5254,5255,5257,5262,5263,5532,5533,5544,5545,5552,5554,5558,5560,5568,5569,5571,5573,5580,5581,5638,5639,5650,5651,5661]
def ridgeSupport259_009 : List Nat := [5664,5667,5670,5674,5675,5678,5683,5686,5687,5692,5693,5704,5705,5715,5718,5721,5724,5728,5729,5732,5737,5740,5741,6012,6013,6024,6025,6032,6034,6038,6040,6048]
def ridgeSupport259_010 : List Nat := [6049,6051,6053,6060,6061,6118,6119,6130,6131,6141,6144,6147,6150,6154,6155,6158,6163,6166,6167,6172,6173,6184,6185,6195,6198,6201,6204,6208,6209,6212,6217,6220]
def ridgeSupport259_011 : List Nat := [6221,7366,7367,7370,7371,7374,7375,7404,7405,7414,7415,7420,7421,7452,7453,7462,7463,7468,7469,7592,7593,7594,7595,7596,7597]
def ridgeSupport259_code : Nat := 0x1daded676afb55da9ed474b7a59d27e937477a39cfde7e73df9edcede76733f99dccbe65731f98d84dc266127089841c2060f3073836c19e0a705181dc0e605f02d813c07602f015806c01e002ffb7f3bf95f9efcd7adbd65e96f477a1bd05e62f2d792bc85e26f1177dbbe59b6cd9669b325986cc165cb2cd95aca7649b2458f6c79637b1b58cec5d62bb15589ac47620b0ed84ec25607b035736b995c5ae1d706b815b8adb56cab615a9ad45676b3948fa47522690f486a4252028fd47da3e51ee8f5479a3c51da8e7470a36d1a28cd465a32518e8c5461a30517a8b7458a2ad13689944ba255126891435a1a50ce865431a18508e84541fa0f506e835417a0b504e82540fa0731698aec54628b11d88cc3b61d308d844c1760b304981ec0c604affd7fcbf35f92f6d7b4bcf5e72e016fcb7a5bc2dc56e0b655b22d35698b415a025692ae9544a8a51d28c93b49d248d24491748b244921e90c484a3fd1fc8f3479236d1b48cf46722010fc87a43c21c50e086543221350988414201900c7c63d31e18ecc7463931c18d8c666303169894c486233111884c4060d306182cc1460930417d4be85f32f917c4be05dd2ee176cbb45d92ec1714b885c32e11704b805ad2d616acb545a92d4166cb345952ca164cb245912c81634b185872c3160cb0457d2be15ecaf45792bc15d4ae856f2b7051c28c1430a1050027e13d09d84e827013709a84c826212e09684ac2541280930494246122090042821210408104041fe0fe07e83e81f20f707b03cc1e20ee07683ac1b40d806b83501a40c206002fc1780ba05582a414c0a5051824812008f04602280f407803b81d00e400e006002800e003
def ridgeSupport259_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport259_code
def ridgeSupport259_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport259_code
def ridgeSupport259_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport259_code
def ridgeSupport259_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport259_code
def ridgeSupport259_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport259_code
def ridgeSupport259_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport259_code
def ridgeSupport259_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport259_code
def ridgeSupport259_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport259_code
def ridgeSupport259_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport259_code
def ridgeSupport259_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport259_code
def ridgeSupport259_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport259_code
def ridgeSupport259_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport259_code
def ridgeSupport259_rest_012 : Nat := PackedRawNatGrowth.drop 4901 ridgeSupport259_code
def ridgeSupport259_suffix_012 : List Nat := []
def ridgeSupport259_suffix_011 : List Nat := ridgeSupport259_011 ++ ridgeSupport259_suffix_012
def ridgeSupport259_suffix_010 : List Nat := ridgeSupport259_010 ++ ridgeSupport259_suffix_011
def ridgeSupport259_suffix_009 : List Nat := ridgeSupport259_009 ++ ridgeSupport259_suffix_010
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
    (PackedRawNatGrowth.readList 13 377 ridgeSupport259_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
