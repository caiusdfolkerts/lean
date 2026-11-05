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
def ridgeSupport548_000 : List Nat := [68,78,87,89,90,1068,1071,1072,1075,1078,1092,1095,1096,1099,1102,1104,1107,1108,1111,1114,1224,1227,1228,1231,1234,1248,1251,1252,1255,1258,1260,1263]
def ridgeSupport548_001 : List Nat := [1264,1267,1270,1377,1378,1380,1381,1384,1385,1386,1388,1389,1391,1396,1397,1398,1399,1401,1402,1405,1406,1407,1409,1410,1412,1417,1418,1419,1420,1422,1423,1426]
def ridgeSupport548_002 : List Nat := [1427,1428,1430,1431,1433,1438,1439,5468,5469,5474,5475,5480,5481,5482,5483,5484,5485,5486,5487,5492,5493,5498,5499,5504,5505,5506,5507,5508,5509,5510,5511,5530]
def ridgeSupport548_003 : List Nat := [5531,5532,5533,5534,5535,5554,5555,5556,5557,5558,5559,5578,5579,5580,5581,5582,5583,5602,5603,5604,5605,5606,5607,5626,5627,5628,5629,5630,5631,5650,5651,5652]
def ridgeSupport548_004 : List Nat := [5653,5654,5655,5656,5658,5662,5664,5668,5670,5674,5675,5676,5677,5678,5679,6026,6027,6044,6045,6062,6063,6064,6066,6070,6072,6080,6081,6098,6099,6116,6117,6134]
def ridgeSupport548_005 : List Nat := [6135,6136,6138,6142,6144,6152,6153,6170,6171,6188,6189,6206,6207,6208,6210,6214,6216,6224,6225,6554,6555,6572,6573,6590,6591,6592,6594,6598,6600,6608,6609,6626]
def ridgeSupport548_006 : List Nat := [6627,6644,6645,6662,6663,6664,6666,6670,6672,6680,6681,6698,6699,6716,6717,6734,6735,6736,6738,6742,6744,6752,6753,7510,7511,7512,7513,7514,7515,8482,8483,8484]
def ridgeSupport548_007 : List Nat := [8485,8486,8487,8488,8490,8494,8496,8498,8499,8500,8502,8506,8508,8510,8511,8578,8580,8594,8595,8596,8598,8612,8613,8614,8616,8630,8631,8698,8700,8714,8715,8716]
def ridgeSupport548_008 : List Nat := [8718,8732,8733,8734,8736,8750,8751]
def ridgeSupport548_code : Nat := 0x222f88ba220887a21d887220e883220b882a1fc87ea1b786da1a8869a1a586921968652193864a184860a13f84fa13c84ea13684d213384ca13084ba12a84a2127849a12584921238489d5b7569d597561d577559a616981a586959a526941a4f6939a3d68f1a2b68a9a196861a106839a0a6821a0768199f567d19e367899d167419c867199c267019bf66f99ad66b199b666985161418486119842610183f60f982d60b181b606980960218005ff97fa5fe17f75fd97e55f917d35f497c15f017b85ed97b25ec17af5eb979d5e7178b5e2962f58b962d58b162b58a96265891620587961a58616175859615585161358495ff57f95fd57f15fb57e95e757995e557915e357895cf57395cd57315cb57295b756d95b556d15b356c959f567959d567159b5669587561958556115835609581560157b55e957555d156f55b956d55b156b55a956955a1563558955d557059f1678599165c5961650593164858f163858c162c58a1624584160858115fc57e15f457a15e457715d857515d056f15b456c15a856915a0565159056215844f613cc4f013bc4ec13a84e713904e313804d2133c4cc132c4c811684571150453114044e112c448111c44410d843310c042f10b005a01640570138044
def ridgeSupport548_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport548_code
def ridgeSupport548_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport548_code
def ridgeSupport548_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport548_code
def ridgeSupport548_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport548_code
def ridgeSupport548_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport548_code
def ridgeSupport548_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport548_code
def ridgeSupport548_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport548_code
def ridgeSupport548_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport548_code
def ridgeSupport548_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport548_code
def ridgeSupport548_rest_009 : Nat := PackedRawNatGrowth.drop 3682 ridgeSupport548_code
def ridgeSupport548_suffix_009 : List Nat := []
def ridgeSupport548_suffix_008 : List Nat := ridgeSupport548_008 ++ ridgeSupport548_suffix_009
def ridgeSupport548_suffix_007 : List Nat := ridgeSupport548_007 ++ ridgeSupport548_suffix_008
def ridgeSupport548_suffix_006 : List Nat := ridgeSupport548_006 ++ ridgeSupport548_suffix_007
def ridgeSupport548_suffix_005 : List Nat := ridgeSupport548_005 ++ ridgeSupport548_suffix_006
def ridgeSupport548_suffix_004 : List Nat := ridgeSupport548_004 ++ ridgeSupport548_suffix_005
def ridgeSupport548_suffix_003 : List Nat := ridgeSupport548_003 ++ ridgeSupport548_suffix_004
def ridgeSupport548_suffix_002 : List Nat := ridgeSupport548_002 ++ ridgeSupport548_suffix_003
def ridgeSupport548_suffix_001 : List Nat := ridgeSupport548_001 ++ ridgeSupport548_suffix_002
def ridgeSupport548_suffix_000 : List Nat := ridgeSupport548_000 ++ ridgeSupport548_suffix_001
theorem ridgeSupport548_source : candidateSupports 548 =
    (PackedRawNatGrowth.readList 14 263 ridgeSupport548_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
