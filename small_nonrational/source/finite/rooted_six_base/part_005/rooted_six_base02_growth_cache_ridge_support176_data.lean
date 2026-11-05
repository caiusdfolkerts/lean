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
def ridgeSupport176_000 : List Nat := [68,87,90,91,528,990,991,993,998,1000,1025,1028,1030,1033,1035,1037,1040,1042,1045,1047,1254,1256,1257,1259,1260,1262,1264,1265,1267,1268,1271,1272]
def ridgeSupport176_001 : List Nat := [1275,1277,1278,1280,1281,1283,1285,1286,1288,1289,1292,1293,1318,1319,1321,1322,1323,1324,1326,1327,1329,1330,1332,1333,4508,4509,4514,4515,4516,4517,4518,4519]
def ridgeSupport176_002 : List Nat := [4522,4523,4528,4529,4532,4533,4538,4539,4540,4541,4542,4543,4546,4547,4552,4553,4562,4563,4564,4565,4566,4567,4586,4587,4588,4589,4590,4591,4610,4611,4612,4613]
def ridgeSupport176_003 : List Nat := [4614,4615,4634,4635,4636,4637,4638,4639,4658,4659,4660,4661,4662,4663,4682,4683,4684,4685,4686,4687,4703,4705,4706,4707,4708,4709,4710,4711,4713,4716,4719,4722]
def ridgeSupport176_004 : List Nat := [4748,4752,4757,4759,4761,4763,4797,4801,4804,4806,4808,4810,4813,4817,4820,4822,4824,4826,4864,4865,4876,4877,4881,4884,4887,4890,4900,4901,4912,4913,4936,4937]
def ridgeSupport176_005 : List Nat := [4948,4949,4953,4956,4959,4962,4972,4973,4984,4985,5078,5079,5090,5091,5099,5101,5105,5107,5114,5115,5126,5127,6992,6993,6998,6999,7000,7001,7004,7005,7010,7011]
def ridgeSupport176_006 : List Nat := [7012,7013,7022,7023,7024,7025,7026,7027,7046,7047,7048,7049,7050,7051,7067,7069,7070,7071,7072,7073,7074,7075,7077,7080,7083,7086,7091,7093,7094,7095,7096,7097]
def ridgeSupport176_007 : List Nat := [7098,7099,7101,7104,7107,7110,7112,7113,7118,7120,7121,7123,7124,7126,7137,7139,7141,7143,7149,7152,7155,7158,7168,7169,7180,7181,7185,7188,7191,7194,7196,7201]
def ridgeSupport176_008 : List Nat := [7203,7206,7209,7212,7222,7223,7234,7235,7239,7242,7245,7248,7250,7255,7313,7315,7319,7321,7328,7329,7340,7341,7349,7351,7355,7357,7360,7362,7544,7545,7550,7551]
def ridgeSupport176_009 : List Nat := [7552,7553,7557,7560,7563,7566,7577,7579,8006,8007,8008,8009,8010,8011,8036,8049,8053]
def ridgeSupport176_code : Nat := 0x1f75fb8fd93e97f4afa4fd23e8ff46ecdf667b1dd8bec47617b03d80ebff5fbaf3d78e61730397bcbbe5bf2d795bcace50f283933c97e49f2478afc52e287137895c47e21f10b86fc36e1670a784dc23e10f073835c17e0a704781bc0ce00f0037edbf3df86fb77cfbe5df1ef877adbd4de9ef477a1bcede4ef2378dbc3de06ef7777bbaddceee376fbb6ddaeecf75dbabdd46e97747ba2dd0ee8373fb9edceee6f717b8adc4ee2370fb86db9edcb6e3b70db7edbb6cbb64db1ed8b6bbb5cdaced636afb56da8ed4280f4069fdcfea7e73f19f6cfae7c73e29ebcf5a6f33789b6cdb26c535f9ae4d666ab3549a4cd22663330992cc9263531798a4c4661b30c980cc025b52d896b4b525a32cd9654b2258d2c4960caf653729994bca5652128c93949be4d9269933c99a4cb264931c98a4c325f927c93a49b24c925c92a46f23691ac8d246723290fc87a43b21c90dc86a40f206902c8124072028f7c7ba3db1ec8f5c7aa3af1d68eac7523a71d28e4c7223871c28dfc6fa37b1bc8ddc6ea36b1b48d8c6c23571aa8d3c69a34b1a48d1c68a33b19c29a94d0a6453129794b8a5852b29514a4a4e5262869430a125082831414a0650128013f89fa4fb27c13dc9e84f327893c09dc4ec27593a49d04e620b9054824410206902c81240620210047d03e61f08f7c7bc21002d81680ae044
def ridgeSupport176_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport176_code
def ridgeSupport176_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport176_code
def ridgeSupport176_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport176_code
def ridgeSupport176_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport176_code
def ridgeSupport176_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport176_code
def ridgeSupport176_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport176_code
def ridgeSupport176_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport176_code
def ridgeSupport176_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport176_code
def ridgeSupport176_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport176_code
def ridgeSupport176_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport176_code
def ridgeSupport176_rest_010 : Nat := PackedRawNatGrowth.drop 3965 ridgeSupport176_code
def ridgeSupport176_suffix_010 : List Nat := []
def ridgeSupport176_suffix_009 : List Nat := ridgeSupport176_009 ++ ridgeSupport176_suffix_010
def ridgeSupport176_suffix_008 : List Nat := ridgeSupport176_008 ++ ridgeSupport176_suffix_009
def ridgeSupport176_suffix_007 : List Nat := ridgeSupport176_007 ++ ridgeSupport176_suffix_008
def ridgeSupport176_suffix_006 : List Nat := ridgeSupport176_006 ++ ridgeSupport176_suffix_007
def ridgeSupport176_suffix_005 : List Nat := ridgeSupport176_005 ++ ridgeSupport176_suffix_006
def ridgeSupport176_suffix_004 : List Nat := ridgeSupport176_004 ++ ridgeSupport176_suffix_005
def ridgeSupport176_suffix_003 : List Nat := ridgeSupport176_003 ++ ridgeSupport176_suffix_004
def ridgeSupport176_suffix_002 : List Nat := ridgeSupport176_002 ++ ridgeSupport176_suffix_003
def ridgeSupport176_suffix_001 : List Nat := ridgeSupport176_001 ++ ridgeSupport176_suffix_002
def ridgeSupport176_suffix_000 : List Nat := ridgeSupport176_000 ++ ridgeSupport176_suffix_001
theorem ridgeSupport176_source : candidateSupports 176 =
    (PackedRawNatGrowth.readList 13 305 ridgeSupport176_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
