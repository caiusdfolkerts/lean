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
def ridgeSupport276_000 : List Nat := [37,77,80,82,84,636,637,639,644,646,660,661,663,668,670,683,686,688,691,693,1212,1214,1217,1218,1220,1236,1238,1241,1242,1244,1261,1263]
def ridgeSupport276_001 : List Nat := [1264,1267,1269,1272,1273,1275,1276,1279,1280,1281,1283,1284,1286,1291,1292,1314,1316,1317,1319,1320,1322,1324,1325,1327,1328,1331,1332,1335,1337,1338,1340,1341]
def ridgeSupport276_002 : List Nat := [1343,1345,1346,1348,1349,1352,1353,4410,4411,4416,4417,4420,4421,4422,4423,4424,4425,4430,4431,4434,4435,4440,4441,4444,4445,4446,4447,4448,4449,4454,4455,4468]
def ridgeSupport276_003 : List Nat := [4469,4470,4471,4472,4473,4492,4493,4494,4495,4496,4497,4516,4517,4518,4519,4520,4521,4540,4541,4542,4543,4544,4545,4564,4565,4566,4567,4568,4569,4588,4589,4590]
def ridgeSupport276_004 : List Nat := [4591,4592,4593,4601,4604,4607,4610,4612,4613,4614,4615,4616,4617,4618,4620,4670,4671,4682,4683,4684,4686,4690,4692,4706,4707,4718,4719,4812,4813,4824,4825,4829]
def ridgeSupport276_005 : List Nat := [4832,4835,4838,4848,4849,4860,4861,4884,4885,4896,4897,4901,4904,4907,4910,4920,4921,4932,4933,6476,6477,6488,6489,6512,6513,6524,6525,6532,6534,6538,6540,6618]
def ridgeSupport276_006 : List Nat := [6619,6630,6631,6654,6655,6666,6667,6677,6680,6683,6686,6690,6691,6702,6703,6726,6727,6738,6739,6749,6752,6755,6758,7384,7385,7386,7387,7388,7389,8236,8237,8238]
def ridgeSupport276_007 : List Nat := [8239,8240,8241,8249,8252,8255,8257,8258,8259,8261,8264,8267,8269,8270,8271,8276,8277,8282,8283,8310,8311,8316,8317,8328,8329,8334,8335,8686,8688,8692,8694,8723]
def ridgeSupport276_008 : List Nat := [8726,8729,8732,8741,8744,8747,8750]
def ridgeSupport276_code : Nat := 0x222e88ae228889621c8866216884e1f687d21f087ba08f823a089822207d81f207781da05b816a055815204f813a04d812e0488116043810a04180fe03c80e603180c202f80ba02d80b1cdd7371cdb7369cd97361a66698da606975a536949a476919a2f68b9a236889a1e686da186855a0b68299ff67f99e767999db676998c6629986661197d65f197165c1959656194d65313454d113394ce132e4cad3284c953214c813154c512fd4bf12f14bc12e64b8d2e04b752d94b612cd4b3126f49b92634989254494924e493124b492923f48f920c482920948212074819205481120247fd1fc47e51f147c11ef47b91ed47b11d947611d747591d547511c147011bf46f91bd46f11a946a11a746991a54691191464118f463918d463117945e117745d917545d11674599161458115f457915d45711594561153454914f4539149452114745191454511141450113b44e854915205451510542150453f14f453c14e853914dc53414cc53014bc52d14b052a14a05271494524148850c142c5061410503140450013fc4fc13ec4f913e04f513cc4f013bc4ed13704da13644d613504c413084c112f84bc0ad42b30ac02ae0aac29e0a702970a542940a1828409fc27d09f005401480500134025
def ridgeSupport276_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport276_code
def ridgeSupport276_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport276_code
def ridgeSupport276_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport276_code
def ridgeSupport276_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport276_code
def ridgeSupport276_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport276_code
def ridgeSupport276_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport276_code
def ridgeSupport276_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport276_code
def ridgeSupport276_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport276_code
def ridgeSupport276_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport276_code
def ridgeSupport276_rest_009 : Nat := PackedRawNatGrowth.drop 3682 ridgeSupport276_code
def ridgeSupport276_suffix_009 : List Nat := []
def ridgeSupport276_suffix_008 : List Nat := ridgeSupport276_008 ++ ridgeSupport276_suffix_009
def ridgeSupport276_suffix_007 : List Nat := ridgeSupport276_007 ++ ridgeSupport276_suffix_008
def ridgeSupport276_suffix_006 : List Nat := ridgeSupport276_006 ++ ridgeSupport276_suffix_007
def ridgeSupport276_suffix_005 : List Nat := ridgeSupport276_005 ++ ridgeSupport276_suffix_006
def ridgeSupport276_suffix_004 : List Nat := ridgeSupport276_004 ++ ridgeSupport276_suffix_005
def ridgeSupport276_suffix_003 : List Nat := ridgeSupport276_003 ++ ridgeSupport276_suffix_004
def ridgeSupport276_suffix_002 : List Nat := ridgeSupport276_002 ++ ridgeSupport276_suffix_003
def ridgeSupport276_suffix_001 : List Nat := ridgeSupport276_001 ++ ridgeSupport276_suffix_002
def ridgeSupport276_suffix_000 : List Nat := ridgeSupport276_000 ++ ridgeSupport276_suffix_001
theorem ridgeSupport276_source : candidateSupports 276 =
    (PackedRawNatGrowth.readList 14 263 ridgeSupport276_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
