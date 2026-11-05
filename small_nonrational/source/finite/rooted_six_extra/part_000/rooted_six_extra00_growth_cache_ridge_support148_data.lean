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
def ridgeSupport148_000 : List Nat := [36,76,79,82,83,624,625,627,632,634,659,662,664,667,669,671,674,676,679,681,1200,1202,1205,1206,1208,1237,1239,1240,1243,1245,1249,1251]
def ridgeSupport148_001 : List Nat := [1252,1255,1257,1272,1274,1275,1277,1278,1280,1282,1283,1285,1286,1289,1290,1293,1295,1296,1298,1299,1301,1303,1304,1306,1307,1310,1311,1336,1337,1339,1340,1341]
def ridgeSupport148_002 : List Nat := [1342,1344,1345,1347,1348,1350,1351,4408,4409,4414,4415,4416,4417,4418,4419,4422,4423,4428,4429,4432,4433,4438,4439,4440,4441,4442,4443,4446,4447,4452,4453,4462]
def ridgeSupport148_003 : List Nat := [4463,4464,4465,4466,4467,4486,4487,4488,4489,4490,4491,4510,4511,4512,4513,4514,4515,4534,4535,4536,4537,4538,4539,4558,4559,4560,4561,4562,4563,4582,4583,4584]
def ridgeSupport148_004 : List Nat := [4585,4586,4587,4603,4605,4606,4607,4608,4609,4610,4611,4613,4616,4619,4622,4668,4669,4680,4681,4685,4688,4691,4694,4704,4705,4716,4717,4740,4741,4752,4753,4757]
def ridgeSupport148_005 : List Nat := [4760,4763,4766,4776,4777,4788,4789,4882,4883,4894,4895,4903,4905,4909,4911,4918,4919,4930,4931,6474,6475,6486,6487,6510,6511,6522,6523,6533,6536,6539,6542,6546]
def ridgeSupport148_006 : List Nat := [6547,6558,6559,6582,6583,6594,6595,6605,6608,6611,6614,6688,6689,6700,6701,6724,6725,6736,6737,6751,6753,6757,6759,7378,7379,7380,7381,7382,7383,8230,8231,8232]
def ridgeSupport148_007 : List Nat := [8233,8234,8235,8251,8253,8254,8255,8256,8257,8263,8265,8266,8267,8268,8269,8274,8275,8280,8281,8292,8293,8298,8299,8326,8327,8332,8333,8687,8690,8693,8696,8705]
def ridgeSupport148_008 : List Nat := [8708,8711,8714,8743,8745,8749,8751]
def ridgeSupport148_code : Nat := 0x222f88b6229889e20a881e20488061f887d61f287be08d8232087821a06b81aa06581920598162053814a04d813204b812a049811e041810203f80fa03d80ee02b80aa02980a20278099cd77359cd57351cd37349a676995a61697da516941a456911a2d68b1a2168819d6674d9d067359c367099b766d999f6679993664998e662d988661597b65e996f65b9957655994b65293434d093374cd932f4cb53294c9d31f4c793134c492b54ad12a94aa129e4a6d2984a552914a412854a1126d49b12614981256494d2504935249492123d48f120e482d2084815203480920148011ff47f91fd47ed1eb47a91e947a11e747991d347491d147411cf47391bb46e91b946e11b746d91a346891a1468119f467918b46291894621187461917345c917145c116f45b9165459115f457915b456915945611574559151454114d453114745191434509141450113f44f913944e05471518544150c541150053e14f453c14ec53914e051f147851b1468518145c515144c512144050f143450a14245061414503140850013f84fd13ec4fa13e04e9139c4e4138c4e113744db13604d713544b812d84b512c84b00aa42a70a902a20a7c29d0a6c2980a5829309e827809cc27109c0053014804f0130024
def ridgeSupport148_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport148_code
def ridgeSupport148_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport148_code
def ridgeSupport148_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport148_code
def ridgeSupport148_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport148_code
def ridgeSupport148_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport148_code
def ridgeSupport148_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport148_code
def ridgeSupport148_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport148_code
def ridgeSupport148_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport148_code
def ridgeSupport148_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport148_code
def ridgeSupport148_rest_009 : Nat := PackedRawNatGrowth.drop 3682 ridgeSupport148_code
def ridgeSupport148_suffix_009 : List Nat := []
def ridgeSupport148_suffix_008 : List Nat := ridgeSupport148_008 ++ ridgeSupport148_suffix_009
def ridgeSupport148_suffix_007 : List Nat := ridgeSupport148_007 ++ ridgeSupport148_suffix_008
def ridgeSupport148_suffix_006 : List Nat := ridgeSupport148_006 ++ ridgeSupport148_suffix_007
def ridgeSupport148_suffix_005 : List Nat := ridgeSupport148_005 ++ ridgeSupport148_suffix_006
def ridgeSupport148_suffix_004 : List Nat := ridgeSupport148_004 ++ ridgeSupport148_suffix_005
def ridgeSupport148_suffix_003 : List Nat := ridgeSupport148_003 ++ ridgeSupport148_suffix_004
def ridgeSupport148_suffix_002 : List Nat := ridgeSupport148_002 ++ ridgeSupport148_suffix_003
def ridgeSupport148_suffix_001 : List Nat := ridgeSupport148_001 ++ ridgeSupport148_suffix_002
def ridgeSupport148_suffix_000 : List Nat := ridgeSupport148_000 ++ ridgeSupport148_suffix_001
theorem ridgeSupport148_source : candidateSupports 148 =
    (PackedRawNatGrowth.readList 14 263 ridgeSupport148_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
