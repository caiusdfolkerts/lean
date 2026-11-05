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
def ridgeSupport274_000 : List Nat := [37,47,56,58,60,635,638,639,642,645,659,662,663,666,669,684,685,688,689,694,791,794,795,798,801,815,818,819,822,825,840,841]
def ridgeSupport274_001 : List Nat := [844,845,850,935,936,938,939,942,943,944,946,947,949,954,955,977,979,980,982,983,985,987,988,990,991,994,995,998,1000,1001,1003,1004]
def ridgeSupport274_002 : List Nat := [1006,1008,1009,1011,1012,1015,1016,4170,4171,4176,4177,4180,4181,4182,4183,4184,4185,4190,4191,4194,4195,4200,4201,4204,4205,4206,4207,4208,4209,4214,4215,4228]
def ridgeSupport274_003 : List Nat := [4229,4230,4231,4232,4233,4252,4253,4254,4255,4256,4257,4276,4277,4278,4279,4280,4281,4300,4301,4302,4303,4304,4305,4324,4325,4326,4327,4328,4329,4348,4349,4350]
def ridgeSupport274_004 : List Nat := [4351,4352,4353,4361,4364,4367,4370,4372,4373,4374,4375,4376,4377,4378,4380,4658,4659,4676,4677,4694,4695,4696,4698,4702,4704,4712,4713,4800,4801,4818,4819,4836]
def ridgeSupport274_005 : List Nat := [4837,4841,4844,4847,4850,4854,4855,4872,4873,4890,4891,4908,4909,4913,4916,4919,4922,4926,4927,5186,5187,5204,5205,5222,5223,5224,5226,5230,5232,5240,5241,5328]
def ridgeSupport274_006 : List Nat := [5329,5346,5347,5364,5365,5369,5372,5375,5378,5382,5383,5400,5401,5418,5419,5436,5437,5441,5444,5447,5450,5454,5455,7348,7349,7350,7351,7352,7353,8188,8189,8190]
def ridgeSupport274_007 : List Nat := [8191,8192,8193,8201,8204,8207,8209,8210,8211,8213,8216,8219,8221,8222,8223,8272,8274,8288,8289,8309,8312,8322,8323,8327,8330,8340,8341,8392,8394,8408,8409,8429]
def ridgeSupport274_008 : List Nat := [8432,8442,8443,8447,8450,8460,8461]
def ridgeSupport274_code : Nat := 0x210d843210283fe0fb83ea0f083b60d983620ca8322095825208a821e083820a07881d60618182052814201f807a01d806e0188056013804a011803e00c80260018001fff7ff9ffd7ff1cb972e1cb772d9cb572d154f553954a551d544550553d54f152b54a95195461507541950253fd4fc53e54f553d14e353894d1534147951e147051b946a51a146751994555151443510933f4cf933a4cdd3344cc532d4cb131b4c693094c212f74bd92f24bbd2ec4ba52e54b912d34b492c14b0126949a1260497925a49612574959245491123348c911c4469119446111744591154451112443d10c442510144010ff43f90fd43f10e943a10e743990e543910d143410cf43390cd43310b942e10b742d90b542d10a1428109f427909d427108942210874219085421107741d907141c106f41b906d41b106941a1063418905f4179059416105741590554151051414104b41283f80fdc3f40fcc3f10fc03ee0fb03eb0fa43e80f983e30f883df0f783dc0f6c3d90f5c3d60f503d30f443bb0ee83b50ecc3b20ec03af0eb83ab0ea83a80e9c3520d3434c0d243480ce43360ccc3320cbc3210c7831b0c683170ad82b10ac02ad0ab029d0a682970a582930a1428209fc27e09ec03c00e803800bc025
def ridgeSupport274_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport274_code
def ridgeSupport274_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport274_code
def ridgeSupport274_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport274_code
def ridgeSupport274_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport274_code
def ridgeSupport274_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport274_code
def ridgeSupport274_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport274_code
def ridgeSupport274_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport274_code
def ridgeSupport274_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport274_code
def ridgeSupport274_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport274_code
def ridgeSupport274_rest_009 : Nat := PackedRawNatGrowth.drop 3682 ridgeSupport274_code
def ridgeSupport274_suffix_009 : List Nat := []
def ridgeSupport274_suffix_008 : List Nat := ridgeSupport274_008 ++ ridgeSupport274_suffix_009
def ridgeSupport274_suffix_007 : List Nat := ridgeSupport274_007 ++ ridgeSupport274_suffix_008
def ridgeSupport274_suffix_006 : List Nat := ridgeSupport274_006 ++ ridgeSupport274_suffix_007
def ridgeSupport274_suffix_005 : List Nat := ridgeSupport274_005 ++ ridgeSupport274_suffix_006
def ridgeSupport274_suffix_004 : List Nat := ridgeSupport274_004 ++ ridgeSupport274_suffix_005
def ridgeSupport274_suffix_003 : List Nat := ridgeSupport274_003 ++ ridgeSupport274_suffix_004
def ridgeSupport274_suffix_002 : List Nat := ridgeSupport274_002 ++ ridgeSupport274_suffix_003
def ridgeSupport274_suffix_001 : List Nat := ridgeSupport274_001 ++ ridgeSupport274_suffix_002
def ridgeSupport274_suffix_000 : List Nat := ridgeSupport274_000 ++ ridgeSupport274_suffix_001
theorem ridgeSupport274_source : candidateSupports 274 =
    (PackedRawNatGrowth.readList 14 263 ridgeSupport274_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
