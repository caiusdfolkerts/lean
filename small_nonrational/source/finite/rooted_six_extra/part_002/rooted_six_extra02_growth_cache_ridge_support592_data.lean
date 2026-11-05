module
prelude
public import RootedSixExtra02GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport592_000 : List Nat := [59,73,89,94,95,901,903,905,907,909,914,915,917,920,922,924,926,928,930,935,936,938,941,1013,1014,1017,1018,1021,1022,1082,1084,1086]
def ridgeSupport592_001 : List Nat := [1088,1090,1095,1096,1098,1101,1103,1105,1107,1109,1111,1116,1117,1119,1122,1276,1278,1280,1281,1283,1285,1286,1290,1295,1297,1299,1301,1302,1304,1306,1307,1311]
def ridgeSupport592_002 : List Nat := [1316,1339,1340,1342,1343,1346,1347,1348,1350,1351,1353,1360,1361,3170,3175,3176,3181,3240,3241,3254,3255,3260,3262,3268,3269,3274,3275,3281,3283,3288,3289,3302]
def ridgeSupport592_003 : List Nat := [3303,3336,3337,3338,3343,3344,3349,3350,3351,3364,3365,3370,3371,3388,3389,3394,3395,3410,3415,3416,3421,3480,3481,3494,3495,3500,3502,3508,3509,3514,3515,3521]
def ridgeSupport592_004 : List Nat := [3523,3528,3529,3542,3543,3576,3577,3578,3583,3584,3589,3590,3591,3604,3605,3610,3611,3628,3629,3634,3635,3680,3681,3684,3685,4538,4543,4544,4549,4560,4561,4574]
def ridgeSupport592_005 : List Nat := [4575,4608,4609,4622,4623,4628,4630,4636,4637,4642,4643,4649,4651,4656,4657,4658,4663,4664,4669,4670,4671,4704,4705,4718,4719,4728,4729,4742,4743,4784,4785,4792]
def ridgeSupport592_006 : List Nat := [4793,4916,4921,4946,4951,4960,4961,4978,4979,4988,4993,5018,5023,5032,5033,5050,5051,5240,5242,5249,5251,5252,5254,5261,5263,5313,5315,5320,5322,5330,5335,5336]
def ridgeSupport592_007 : List Nat := [5341,5606,5607,5642,5643,5796,5797,6240,6241,6254,6255,6264,6265,6267,6268,6269,6271,6288,6289,6302,6303,6312,6313,6315,6316,6317,6319,6500,6502,6521,6523,6540]
def ridgeSupport592_008 : List Nat := [6541,6543,6544,6545,6547,6573,6574,6575,6576,6591,6592,6593,6594]
def ridgeSupport592_code : Nat := 0x19c2ce0e70337f9b0cd7e6bb35b993cc8e64331f98dcc665ef2f3966cb262bf15b8acc55e2a715189fc4f624712187fc3ee1f30f7879c3c61bf0dd861c305a96d4960bb05579ebcd4dda6c535e9a54caa64530e98348fa46d21a909483a40d1ea8f13bb9dd4ea675139f9cd4e066f93739b94d866c13579a94ce66692b995c4ac656128794349e64f126f93749864c123f91f48f647123791948c646122b914c88e44521d90e485a42920f90748064011df8ef47463a11c58e046fe374e657323985cc0e3371938b5c58e1b70d3855c28e077033815c00dff6fd37e5bf0dd76eb3725b90dc36e0b6edb74db56da36b9b58da76d33665b30d5d6ac355daa4d436a134f5a78d2b6953495a48d1768b3455a20d0f6853425a10ce767333659b0cd3668b32d994cc566232f9978cb765b32a5950c6d634319d8c45512a81524a8e5462a2150ca8453f29f14f0a7652428f946ca3451828b1454a265112879428a0c5052819404a004fe27e11888be45d22e115c8aa453228913c89a44a224111c88444021f10f08743fe1fe8fe87f23f61fa8eb47543a81d38e8874039e1ce0e687303951c98e4871a38b1c48e1c70a05f02f016409203b
def ridgeSupport592_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport592_code
def ridgeSupport592_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport592_code
def ridgeSupport592_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport592_code
def ridgeSupport592_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport592_code
def ridgeSupport592_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport592_code
def ridgeSupport592_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport592_code
def ridgeSupport592_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport592_code
def ridgeSupport592_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport592_code
def ridgeSupport592_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport592_code
def ridgeSupport592_rest_009 : Nat := PackedRawNatGrowth.drop 3497 ridgeSupport592_code
def ridgeSupport592_suffix_009 : List Nat := []
def ridgeSupport592_suffix_008 : List Nat := ridgeSupport592_008 ++ ridgeSupport592_suffix_009
def ridgeSupport592_suffix_007 : List Nat := ridgeSupport592_007 ++ ridgeSupport592_suffix_008
def ridgeSupport592_suffix_006 : List Nat := ridgeSupport592_006 ++ ridgeSupport592_suffix_007
def ridgeSupport592_suffix_005 : List Nat := ridgeSupport592_005 ++ ridgeSupport592_suffix_006
def ridgeSupport592_suffix_004 : List Nat := ridgeSupport592_004 ++ ridgeSupport592_suffix_005
def ridgeSupport592_suffix_003 : List Nat := ridgeSupport592_003 ++ ridgeSupport592_suffix_004
def ridgeSupport592_suffix_002 : List Nat := ridgeSupport592_002 ++ ridgeSupport592_suffix_003
def ridgeSupport592_suffix_001 : List Nat := ridgeSupport592_001 ++ ridgeSupport592_suffix_002
def ridgeSupport592_suffix_000 : List Nat := ridgeSupport592_000 ++ ridgeSupport592_suffix_001
theorem ridgeSupport592_source : candidateSupports 592 =
    (PackedRawNatGrowth.readList 13 269 ridgeSupport592_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
