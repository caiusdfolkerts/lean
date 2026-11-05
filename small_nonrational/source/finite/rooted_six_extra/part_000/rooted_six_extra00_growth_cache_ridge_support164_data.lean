module
prelude
public import RootedSixExtra00GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport164_000 : List Nat := [66,76,85,88,89,1044,1047,1048,1051,1054,1081,1082,1085,1086,1091,1093,1094,1097,1098,1103,1200,1203,1204,1207,1210,1237,1238,1241,1242,1247,1249,1250]
def ridgeSupport164_001 : List Nat := [1253,1254,1259,1356,1358,1359,1361,1362,1364,1366,1367,1369,1370,1373,1374,1377,1379,1380,1382,1383,1385,1387,1388,1390,1391,1394,1395,1420,1421,1423,1424,1425]
def ridgeSupport164_002 : List Nat := [1426,1428,1429,1431,1432,1434,1435,5464,5465,5470,5471,5472,5473,5474,5475,5478,5479,5484,5485,5488,5489,5494,5495,5496,5497,5498,5499,5502,5503,5508,5509,5518]
def ridgeSupport164_003 : List Nat := [5519,5520,5521,5522,5523,5542,5543,5544,5545,5546,5547,5566,5567,5568,5569,5570,5571,5590,5591,5592,5593,5594,5595,5614,5615,5616,5617,5618,5619,5638,5639,5640]
def ridgeSupport164_004 : List Nat := [5641,5642,5643,5659,5661,5662,5663,5664,5665,5666,5667,5669,5672,5675,5678,5952,5953,5970,5971,5988,5989,5993,5996,5999,6002,6006,6007,6024,6025,6042,6043,6060]
def ridgeSupport164_005 : List Nat := [6061,6065,6068,6071,6074,6078,6079,6166,6167,6184,6185,6202,6203,6211,6213,6217,6219,6220,6221,6480,6481,6498,6499,6516,6517,6521,6524,6527,6530,6534,6535,6552]
def ridgeSupport164_006 : List Nat := [6553,6570,6571,6588,6589,6593,6596,6599,6602,6606,6607,6694,6695,6712,6713,6730,6731,6739,6741,6745,6747,6748,6749,7498,7499,7500,7501,7502,7503,8470,8471,8472]
def ridgeSupport164_007 : List Nat := [8473,8474,8475,8491,8493,8494,8495,8496,8497,8503,8505,8506,8507,8508,8509,8561,8564,8574,8575,8579,8582,8592,8593,8617,8619,8626,8627,8681,8684,8694,8695,8699]
def ridgeSupport164_008 : List Nat := [8702,8712,8713,8737,8739,8746,8747]
def ridgeSupport164_code : Nat := 0x222b88aa223888620988221fe87ee1f787da1ec87a61b386ca1ab86a61918642186860e17f85fa17485c613d84f213b84ea13984de13184c212f84ba12d84ae11b846a11984621178459d4f7539d4d7531d4b7529a5d6971a5b6965a55694da4b6929a3968e1a2768999cf67399ca671d9c467059bd66f19ab66a99996661987661998265fd97c65e597565d19636589951654184d613184b6125845610d83b60e982960a181760597bf5ef97ba5edd7b45ec57ad5eb179b5e697895e217775dd97725dbd76c5da57655d917535d497415d0162e58ad62858956235889621588161f587961d586d60b5829609582160758195f357c95f157c15ef57b95db57695d957615d757595c357095c157015bf56f95ab56a95a956a15a756995935649591564158f5639585561157f55f957b55e957955e157755d957155c156d55b156755995635589561558155f5579559556059b1668598165c59516505921644590163c58d163057315c856f15b856c15ac569159c5661590563158455e157455a156455715585541548551153c54e15304eb13984e513884e1137c4da13644d613544ba12dc4b412cc4b0113c44a1124446111444310f843d10e8439107841b1060417105005901600550130042
def ridgeSupport164_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport164_code
def ridgeSupport164_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport164_code
def ridgeSupport164_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport164_code
def ridgeSupport164_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport164_code
def ridgeSupport164_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport164_code
def ridgeSupport164_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport164_code
def ridgeSupport164_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport164_code
def ridgeSupport164_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport164_code
def ridgeSupport164_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport164_code
def ridgeSupport164_rest_009 : Nat := PackedRawNatGrowth.drop 3682 ridgeSupport164_code
def ridgeSupport164_suffix_009 : List Nat := []
def ridgeSupport164_suffix_008 : List Nat := ridgeSupport164_008 ++ ridgeSupport164_suffix_009
def ridgeSupport164_suffix_007 : List Nat := ridgeSupport164_007 ++ ridgeSupport164_suffix_008
def ridgeSupport164_suffix_006 : List Nat := ridgeSupport164_006 ++ ridgeSupport164_suffix_007
def ridgeSupport164_suffix_005 : List Nat := ridgeSupport164_005 ++ ridgeSupport164_suffix_006
def ridgeSupport164_suffix_004 : List Nat := ridgeSupport164_004 ++ ridgeSupport164_suffix_005
def ridgeSupport164_suffix_003 : List Nat := ridgeSupport164_003 ++ ridgeSupport164_suffix_004
def ridgeSupport164_suffix_002 : List Nat := ridgeSupport164_002 ++ ridgeSupport164_suffix_003
def ridgeSupport164_suffix_001 : List Nat := ridgeSupport164_001 ++ ridgeSupport164_suffix_002
def ridgeSupport164_suffix_000 : List Nat := ridgeSupport164_000 ++ ridgeSupport164_suffix_001
theorem ridgeSupport164_source : candidateSupports 164 =
    (PackedRawNatGrowth.readList 14 263 ridgeSupport164_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
