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
def ridgeSupport536_000 : List Nat := [48,98,101,103,104,804,805,807,812,814,828,829,831,836,838,840,841,843,848,850,1489,1491,1494,1495,1497,1513,1515,1518,1519,1521,1525,1527]
def ridgeSupport536_001 : List Nat := [1530,1531,1533,1558,1559,1561,1562,1565,1566,1567,1569,1570,1572,1577,1578,1579,1580,1582,1583,1586,1587,1588,1590,1591,1593,1598,1599,1600,1601,1603,1604,1607]
def ridgeSupport536_002 : List Nat := [1608,1609,1611,1612,1614,1619,1620,4940,4941,4946,4947,4952,4953,4954,4955,4956,4957,4958,4959,4964,4965,4970,4971,4976,4977,4978,4979,4980,4981,4982,4983,5002]
def ridgeSupport536_003 : List Nat := [5003,5004,5005,5006,5007,5026,5027,5028,5029,5030,5031,5050,5051,5052,5053,5054,5055,5074,5075,5076,5077,5078,5079,5098,5099,5100,5101,5102,5103,5122,5123,5124]
def ridgeSupport536_004 : List Nat := [5125,5126,5127,5128,5130,5134,5136,5140,5142,5146,5147,5148,5149,5150,5151,5270,5271,5282,5283,5284,5286,5290,5292,5306,5307,5318,5319,5342,5343,5354,5355,5356]
def ridgeSupport536_005 : List Nat := [5358,5362,5364,5378,5379,5390,5391,5414,5415,5426,5427,5428,5430,5434,5436,5450,5451,5462,5463,6836,6837,6848,6849,6872,6873,6884,6885,6892,6894,6898,6900,6908]
def ridgeSupport536_006 : List Nat := [6909,6920,6921,6944,6945,6956,6957,6964,6966,6970,6972,6980,6981,6992,6993,7016,7017,7028,7029,7036,7038,7042,7044,7450,7451,7452,7453,7454,7455,8362,8363,8364]
def ridgeSupport536_007 : List Nat := [8365,8366,8367,8368,8370,8374,8376,8378,8379,8380,8382,8386,8388,8390,8391,8414,8415,8420,8421,8432,8433,8438,8439,8450,8451,8456,8457,8776,8778,8782,8784,8794]
def ridgeSupport536_008 : List Nat := [8796,8800,8802,8812,8814,8818,8820]
def ridgeSupport536_code : Nat := 0x227489ca26e89b2262898225c896a250893a24a89221098422103840a0f783da0f183c20e583920df837a0c7831a0c4830a0be82f20bb82ea0b882da0b282c20af82ba0ad82b20ab82a9d1f7479d1d7471d1b7469b846e09b7e6df1b756dd1b696da1b516d41b456d11b3c6ce9b366cd1b2d6cb1b216c81b096c21afd6bf1af46bc9aee6bb1ae56b91ad96b61ac16b01ab56ad1557555954b552953c54e953654d153354c9527549950f543950354094f453c94ee53b14eb53a94df53794c753194bb52e94ac52a94a652914a35289497525941f507941d507141b50694165051410503940a50214075019405501140350093ef4fb93ed4fb13eb4fa93d74f593d54f513d34f493bf4ef93bd4ef13bb4ee93a74e993a54e913a34e8938f4e3938d4e3138b4e293774dd93754dd13734dc93714dc136b4da93654d9135f4d7935d4d7135b4d693594d613534d4934d4d30654194c64e193064b1924648191c644190c641190063f18f863918dc63618d063318c862f18b862c18ac62a18a46241888621187c61e187461a186461718585fd17ec5fa17dc5f517c45ef17b85eb17a45d9175c5d6174c5d10d483500d2c3490d203460d1033f0cf433c0cb832c0c9c3250c90068019c0650188030
def ridgeSupport536_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport536_code
def ridgeSupport536_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport536_code
def ridgeSupport536_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport536_code
def ridgeSupport536_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport536_code
def ridgeSupport536_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport536_code
def ridgeSupport536_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport536_code
def ridgeSupport536_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport536_code
def ridgeSupport536_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport536_code
def ridgeSupport536_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport536_code
def ridgeSupport536_rest_009 : Nat := PackedRawNatGrowth.drop 3682 ridgeSupport536_code
def ridgeSupport536_suffix_009 : List Nat := []
def ridgeSupport536_suffix_008 : List Nat := ridgeSupport536_008 ++ ridgeSupport536_suffix_009
def ridgeSupport536_suffix_007 : List Nat := ridgeSupport536_007 ++ ridgeSupport536_suffix_008
def ridgeSupport536_suffix_006 : List Nat := ridgeSupport536_006 ++ ridgeSupport536_suffix_007
def ridgeSupport536_suffix_005 : List Nat := ridgeSupport536_005 ++ ridgeSupport536_suffix_006
def ridgeSupport536_suffix_004 : List Nat := ridgeSupport536_004 ++ ridgeSupport536_suffix_005
def ridgeSupport536_suffix_003 : List Nat := ridgeSupport536_003 ++ ridgeSupport536_suffix_004
def ridgeSupport536_suffix_002 : List Nat := ridgeSupport536_002 ++ ridgeSupport536_suffix_003
def ridgeSupport536_suffix_001 : List Nat := ridgeSupport536_001 ++ ridgeSupport536_suffix_002
def ridgeSupport536_suffix_000 : List Nat := ridgeSupport536_000 ++ ridgeSupport536_suffix_001
theorem ridgeSupport536_source : candidateSupports 536 =
    (PackedRawNatGrowth.readList 14 263 ridgeSupport536_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
