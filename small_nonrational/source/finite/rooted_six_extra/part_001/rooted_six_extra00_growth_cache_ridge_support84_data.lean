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
def ridgeSupport84_000 : List Nat := [35,75,79,80,81,623,626,628,631,633,635,638,640,643,645,647,650,652,655,657,1201,1203,1204,1207,1209,1213,1215,1216,1219,1221,1225,1227]
def ridgeSupport84_001 : List Nat := [1228,1231,1233,1273,1274,1276,1277,1278,1279,1281,1282,1284,1285,1287,1288,1294,1295,1297,1298,1299,1300,1302,1303,1305,1306,1308,1309,1315,1316,1318,1319,1320]
def ridgeSupport84_002 : List Nat := [1321,1323,1324,1326,1327,1329,1330,4408,4409,4410,4411,4412,4413,4414,4415,4420,4421,4426,4427,4432,4433,4434,4435,4436,4437,4438,4439,4444,4445,4450,4451,4456]
def ridgeSupport84_003 : List Nat := [4457,4458,4459,4460,4461,4480,4481,4482,4483,4484,4485,4504,4505,4506,4507,4508,4509,4528,4529,4530,4531,4532,4533,4552,4553,4554,4555,4556,4557,4576,4577,4578]
def ridgeSupport84_004 : List Nat := [4579,4580,4581,4600,4601,4602,4603,4604,4605,4609,4611,4615,4617,4621,4623,4666,4667,4678,4679,4687,4689,4693,4695,4702,4703,4714,4715,4738,4739,4750,4751,4759]
def ridgeSupport84_005 : List Nat := [4761,4765,4767,4774,4775,4786,4787,4810,4811,4822,4823,4831,4833,4837,4839,4846,4847,4858,4859,6472,6473,6484,6485,6508,6509,6520,6521,6535,6537,6541,6543,6544]
def ridgeSupport84_006 : List Nat := [6545,6556,6557,6580,6581,6592,6593,6607,6609,6613,6615,6616,6617,6628,6629,6652,6653,6664,6665,6679,6681,6685,6687,7372,7373,7374,7375,7376,7377,8224,8225,8226]
def ridgeSupport84_007 : List Nat := [8227,8228,8229,8248,8249,8250,8251,8252,8253,8260,8261,8262,8263,8264,8265,8272,8273,8278,8279,8290,8291,8296,8297,8308,8309,8314,8315,8689,8691,8695,8697,8707]
def ridgeSupport84_008 : List Nat := [8709,8713,8715,8725,8727,8731,8733]
def ridgeSupport84_code : Nat := 0x221d886e217885620b8826205880e1f987de1f387c607b81ea07581d206981a2063818a057815a05181420498122047811a045811203d80f203b80ea03980e20258092023808a0218081cd17341ccf7339ccd7331a1f6875a19685da0968219fd67f19e567919d967619d767559d1673d9c167019b566d199d6671991664198f6635989661d97965e196d65b1955655194965212fb4be92ef4bb92e74b952e14b7d2d74b592cb4b292b34ac92a74a9929f4a752994a5d28f4a392834a0926b49a925f49792574955251493d247491923b48e920f4835209481d20348051fd47f11fb47e91f947e11e547911e347891e147811cd47311cb47291c947211b546d11b346c91b146c119d467119b4669199466118546111834609181460116d45b116b45a916945a1163458915d4571157455915545511534549151454114b4529145451113f44f913d44f113b44e913944e053214c452f14b852c14ac52914a05271498524148c51d147051a14645171458514144c512144450f1438508141c505141050214044ff13f84fd13f04fa13e44d1133c4cc132c4c913144c313004bf12f44b912dc4b412cc4b10a4428f0a3028a0a1c2850a0c28009f827b09e427709d027209bc051014004f012c023
def ridgeSupport84_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport84_code
def ridgeSupport84_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport84_code
def ridgeSupport84_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport84_code
def ridgeSupport84_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport84_code
def ridgeSupport84_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport84_code
def ridgeSupport84_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport84_code
def ridgeSupport84_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport84_code
def ridgeSupport84_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport84_code
def ridgeSupport84_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport84_code
def ridgeSupport84_rest_009 : Nat := PackedRawNatGrowth.drop 3682 ridgeSupport84_code
def ridgeSupport84_suffix_009 : List Nat := []
def ridgeSupport84_suffix_008 : List Nat := ridgeSupport84_008 ++ ridgeSupport84_suffix_009
def ridgeSupport84_suffix_007 : List Nat := ridgeSupport84_007 ++ ridgeSupport84_suffix_008
def ridgeSupport84_suffix_006 : List Nat := ridgeSupport84_006 ++ ridgeSupport84_suffix_007
def ridgeSupport84_suffix_005 : List Nat := ridgeSupport84_005 ++ ridgeSupport84_suffix_006
def ridgeSupport84_suffix_004 : List Nat := ridgeSupport84_004 ++ ridgeSupport84_suffix_005
def ridgeSupport84_suffix_003 : List Nat := ridgeSupport84_003 ++ ridgeSupport84_suffix_004
def ridgeSupport84_suffix_002 : List Nat := ridgeSupport84_002 ++ ridgeSupport84_suffix_003
def ridgeSupport84_suffix_001 : List Nat := ridgeSupport84_001 ++ ridgeSupport84_suffix_002
def ridgeSupport84_suffix_000 : List Nat := ridgeSupport84_000 ++ ridgeSupport84_suffix_001
theorem ridgeSupport84_source : candidateSupports 84 =
    (PackedRawNatGrowth.readList 14 263 ridgeSupport84_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
