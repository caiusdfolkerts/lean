module
prelude
public import RootedSixBase01GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport480_000 : List Nat := [1283,1284,1285,1392,1393,1394,1501,1502,1503,1623,1624,1625,5484,5485,5486,5487,5488,5489,5580,5581,5582,5583,5584,5585,5676,5677,5678,5679,5680,5681,5748,5749]
def ridgeSupport480_001 : List Nat := [5750,5751,5752,5753,5844,5845,5846,5847,5848,5849,5940,5941,5942,5943,5944,5945,6000,6001,6002,6003,6004,6005,6012,6013,6014,6015,6016,6017,6444,6445,6446,6447]
def ridgeSupport480_002 : List Nat := [6448,6449,6540,6541,6542,6543,6544,6545,6636,6637,6638,6639,6640,6641,6696,6697,6698,6699,6700,6701,6708,6709,6710,6711,6712,6713,10246,10247,10252,10253,10258,10259]
def ridgeSupport480_003 : List Nat := [10266,10268,10272,10274,10278,10280,10294,10295,10300,10301,10306,10307,10386,10388,10392,10394,10398,10400,10434,10436,10440,10442,10446,10448,10486,10487,10492,10493,10498,10499,10506,10508]
def ridgeSupport480_004 : List Nat := [10512,10514,10518,10520,10534,10535,10540,10541,10546,10547,10626,10628,10632,10634,10638,10640,10674,10676,10680,10682,10686,10688,10764,10765,10766,10767,10768,10769,10776,10777,10778,10779]
def ridgeSupport480_005 : List Nat := [10780,10781,11014,11015,11020,11021,11026,11027,11034,11036,11040,11042,11046,11048,11062,11063,11068,11069,11074,11075,11154,11156,11160,11162,11166,11168,11202,11204,11208,11210,11214,11216]
def ridgeSupport480_006 : List Nat := [11292,11293,11294,11295,11296,11297,11304,11305,11306,11307,11308,11309,13566,13568,13572,13626,13628,13632,13634,13638,13640,13698,13700,13704,13758,13760,13764,13766,13770,13772,13860,13861]
def ridgeSupport480_007 : List Nat := [13862,13863,13864,13865,14046,14048,14052,14106,14108,14112,14114,14118,14120,14208,14209,14210,14211,14212,14213,15070,15071,15076,15077,15082,15083,15106,15107,15112,15113,15118,15119,15166]
def ridgeSupport480_008 : List Nat := [15167,15172,15173,15178,15179]
def ridgeSupport480_code : Nat := 0x3b4bed2bb45ed13b3fecfbb0fec3bb09ec23b03ec0baebebabae5eb93adfeb7b785de13783de0b781de03728dc9b722dc8371cdc6b6e4db836ded8a7628d89f626d897624d7335cad71b5c4d7035bed623584d60b548d51b542d50353cd4eb504d4034feb0b6c2cb0aec2ab0a6c28b086c20b07ec1eb076c1caf42bceaf2abc8af12bc2ae82b9eae6ab98ae52b92ad0eb42acf6b3cacdeb36aca2b26ac8ab20ac72b1aac4eb12ac36b0cac1eb06a876a1ca86ea1aa866a18a846a10a83ea0ea836a0ca7029bea6ea9b8a6d29b2a64298ea62a988a612982a4ce932a4b692ca49e926a462916a44a910a43290aa40e902a3f68fca3de8f6a3428cea32a8c8a3128c2a28289ea26a898a252892a10e842a0f683ca0de836a0a2826a08a820a07281aa04e812a03680ca01e80668e5a3868dda3668d5a3468b5a2c68ada2a68a5a2867c59f067bd9ee67b59ec6645990663d98e663598c64c593064bd92e64b592c5e057805dfd77e5df577c5dd57745dcd7725dc57705ce57385cdd7365cd57345b656d85b5d6d65b556d459e567859dd67659d567458c563058bd62e58b562c57455d0573d5ce57355cc55c557055bd56e55b556c1964658195c5df17785dd15c857115c05051410503
def ridgeSupport480_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport480_code
def ridgeSupport480_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport480_code
def ridgeSupport480_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport480_code
def ridgeSupport480_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport480_code
def ridgeSupport480_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport480_code
def ridgeSupport480_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport480_code
def ridgeSupport480_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport480_code
def ridgeSupport480_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport480_code
def ridgeSupport480_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport480_code
def ridgeSupport480_rest_009 : Nat := PackedRawNatGrowth.drop 3654 ridgeSupport480_code
def ridgeSupport480_suffix_009 : List Nat := []
def ridgeSupport480_suffix_008 : List Nat := ridgeSupport480_008 ++ ridgeSupport480_suffix_009
def ridgeSupport480_suffix_007 : List Nat := ridgeSupport480_007 ++ ridgeSupport480_suffix_008
def ridgeSupport480_suffix_006 : List Nat := ridgeSupport480_006 ++ ridgeSupport480_suffix_007
def ridgeSupport480_suffix_005 : List Nat := ridgeSupport480_005 ++ ridgeSupport480_suffix_006
def ridgeSupport480_suffix_004 : List Nat := ridgeSupport480_004 ++ ridgeSupport480_suffix_005
def ridgeSupport480_suffix_003 : List Nat := ridgeSupport480_003 ++ ridgeSupport480_suffix_004
def ridgeSupport480_suffix_002 : List Nat := ridgeSupport480_002 ++ ridgeSupport480_suffix_003
def ridgeSupport480_suffix_001 : List Nat := ridgeSupport480_001 ++ ridgeSupport480_suffix_002
def ridgeSupport480_suffix_000 : List Nat := ridgeSupport480_000 ++ ridgeSupport480_suffix_001
theorem ridgeSupport480_source : candidateRows 480 =
    (PackedRawNatGrowth.readList 14 261 ridgeSupport480_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase01
