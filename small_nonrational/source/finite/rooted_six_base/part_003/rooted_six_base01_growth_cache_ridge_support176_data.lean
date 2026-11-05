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
def ridgeSupport176_000 : List Nat := [72,101,104,105,766,1119,1120,1122,1127,1129,1154,1157,1159,1162,1164,1166,1169,1171,1174,1176,1492,1494,1495,1497,1498,1500,1502,1503,1505,1506,1509,1510]
def ridgeSupport176_001 : List Nat := [1513,1515,1516,1518,1519,1521,1523,1524,1526,1527,1530,1531,1556,1557,1559,1560,1561,1562,1564,1565,1567,1568,1570,1571,6426,6427,6432,6433,6434,6435,6436,6437]
def ridgeSupport176_002 : List Nat := [6440,6441,6446,6447,6450,6451,6456,6457,6458,6459,6460,6461,6464,6465,6470,6471,6474,6475,6480,6481,6482,6483,6486,6487,6492,6493,6494,6495,6500,6502,6504,6505]
def ridgeSupport176_003 : List Nat := [6506,6507,6508,6509,6510,6515,6516,6521,6524,6526,6528,6529,6530,6531,6532,6533,6534,6539,6540,6545,6552,6553,6554,6555,6556,6557,6570,6571,6584,6585,6590,6591]
def ridgeSupport176_004 : List Nat := [6594,6595,6608,6609,6614,6615,6618,6619,6621,6623,6631,6632,6633,6634,6637,6638,6639,6640,6642,6643,6645,6647,6655,6656,6657,6658,6661,6662,6663,6664,6668,6670]
def ridgeSupport176_005 : List Nat := [6678,6683,6684,6689,6690,6695,6696,6701,6704,6705,6710,6711,6716,6717,6722,6723,6734,6735,6740,6741,6745,6748,6751,6754,6764,6765,6776,6777,6787,6790,6793,6796]
def ridgeSupport176_006 : List Nat := [6798,6803,6804,6809,6812,6813,6818,6819,6824,6825,6830,6831,6842,6843,6848,6849,6853,6856,6859,6862,6872,6873,6884,6885,6895,6898,6901,6904,7016,7018,7022,7024]
def ridgeSupport176_007 : List Nat := [7026,7027,7032,7033,7038,7039,7044,7045,7056,7057,7062,7063,7071,7073,7077,7079,7086,7087,7098,7099,7113,7115,7119,7121,7122,7124,7126,7129,7147,7149,7151,7152]
def ridgeSupport176_008 : List Nat := [7155,7157,7159,7160,11010,11011,11016,11017,11018,11019,11020,11021,11024,11025,11030,11031,11034,11035,11040,11041,11042,11043,11044,11045,11048,11049,11054,11055,11064,11065,11066,11067]
def ridgeSupport176_009 : List Nat := [11068,11069,11088,11089,11090,11091,11092,11093,11112,11113,11114,11115,11116,11117,11136,11137,11138,11139,11140,11141,11160,11161,11162,11163,11164,11165,11184,11185,11186,11187,11188,11189]
def ridgeSupport176_010 : List Nat := [11205,11207,11208,11209,11210,11211,11212,11213,11215,11218,11221,11224,11270,11271,11282,11283,11287,11290,11293,11296,11306,11307,11318,11319,11342,11343,11354,11355,11359,11362,11365,11368]
def ridgeSupport176_011 : List Nat := [11378,11379,11390,11391,11484,11485,11496,11497,11505,11507,11511,11513,11520,11521,11532,11533,11538,11542,11547,11549,11551,11553,11587,11591,11594,11596,11598,11600,11603,11607,11610,11612]
def ridgeSupport176_012 : List Nat := [11614,11616,14034,14035,14040,14041,14042,14043,14046,14047,14052,14053,14054,14055,14064,14065,14066,14067,14068,14069,14088,14089,14090,14091,14092,14093,14109,14111,14112,14113,14114,14115]
def ridgeSupport176_013 : List Nat := [14116,14117,14119,14122,14125,14128,14133,14135,14136,14137,14138,14139,14140,14141,14143,14146,14149,14152,14154,14155,14160,14162,14163,14165,14167,14170,14173,14176,14186,14187,14198,14199]
def ridgeSupport176_014 : List Nat := [14203,14206,14209,14212,14214,14219,14221,14224,14227,14230,14240,14241,14252,14253,14257,14260,14263,14266,14268,14273,14331,14333,14337,14339,14346,14347,14358,14359,14367,14369,14373,14375]
def ridgeSupport176_015 : List Nat := [14378,14380,14382,14384,14395,14397,14399,14401,14646,14647,14652,14653,14654,14655,14659,14662,14665,14668,14679,14681,15168,15169,15170,15171,15172,15173,15222,15235,15239]
def ridgeSupport176_code : Nat := 0x3b87ee0fb76ed17b44ed0fb42ed07b40e567957e533949e51b943e4ff93ee4f793ce4df936e10783fe0f783be0c382ee0b382ae09f825e08781fe05f816e02f80ae00f801dff77fbdf077bcdeeb7b7ded37b1deb77acde877a0de5b793de4378dde2f786de13781ddfb77bdddf776ddaf76add8375ddd6b757dd57753dd4b750dd2f74add23745dd0b73fdcf773cdcef73adce7738dcdf735dcc372ddcab727dc97724dc8f722dc87720dc7f71ddc3770cdc2f70adc27708dbd76f4dbcf6f2dbc76f0db9f6e6db976e4db7f6dedb6f6dadb676d8db4f6d2b582d5eb572d5ab55ed53b542d4eb532d4ab51ed43b486d1fb476d1bb45ad12b436d0cb406d00b3e6cf7b3cecf1b3a6ce8b376cdcb1fec7eb1cec72b1a2c65b18ac5fb16ec5ab13ec4eb0dec36b0aec2ab082c1db06ac17b04ec12b01ec06af62bd5af4abcfaf36bccaf2ebcaaf26bc8af1ebc5aed6bb4aecebb2aec6bb0ae76b9cae6eb9aae66b98ae16b84ae0eb82ae06b80adb6b6cadaeb6aada6b68ad56b54ad4eb52ad46b50acf6b3caceeb3aace6b38acbeb2eaca6b28ac96b24ac8eb22ac86b20ac6eb1aac5eb16ac46b10ac36b0cac2eb0aac26b08ac0eb026fe1bf76fd5bf36fc1bef6fb5beb6f65bd66f51bd26f45bcf6f2dbc96eedbba6ebdbae6e9dba56e85b9f6e5db966e45b906e15b846dfdb7e6de5b786dcdb726dc1b6e6da9b686be1af56bc9aef6b95ae46b65ad86b39acb6b21ac56b05ac06aedaba6abdaae6aa5aa86a8daa26a75a9c6a65a946a4da8e6a31a896a19a8369e5a7869b5a6c6989a5f6971a596955a54693da4e690da4268f5a3c68dda3668c5a3068b5a28689da226885a1c686da166839a0c6821a076819a056809a0168019ff67dd9f567cd9f267c19ef67b99ed67a99e967a19e7677d9dd676d9da675d9d667459d0670d9c266fd9be66e59b866ad9aa667599c666d99a6665998664598c662d9866615984660d982660598065f997c65e597465cd96e65b596c65ad96a65a59686599964657d95e657595c655d956654d9526545950652d94a651d946650594064f593c64ed93a64e593864cd93264bd92e64a59286495924648d9226485920646d91a188c622188061f187461c18686191860617185461417ec5fa17dc5f617d05f317c45ef17b85ec17ac5e917985e517885e1177c5de17705da17645d717585d41260496124c491123848c1228487121448211a44671188460117c2fe01a40680194048
def ridgeSupport176_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport176_code
def ridgeSupport176_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport176_code
def ridgeSupport176_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport176_code
def ridgeSupport176_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport176_code
def ridgeSupport176_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport176_code
def ridgeSupport176_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport176_code
def ridgeSupport176_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport176_code
def ridgeSupport176_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport176_code
def ridgeSupport176_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport176_code
def ridgeSupport176_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport176_code
def ridgeSupport176_rest_010 : Nat := PackedRawNatGrowth.drop 4480 ridgeSupport176_code
def ridgeSupport176_rest_011 : Nat := PackedRawNatGrowth.drop 4928 ridgeSupport176_code
def ridgeSupport176_rest_012 : Nat := PackedRawNatGrowth.drop 5376 ridgeSupport176_code
def ridgeSupport176_rest_013 : Nat := PackedRawNatGrowth.drop 5824 ridgeSupport176_code
def ridgeSupport176_rest_014 : Nat := PackedRawNatGrowth.drop 6272 ridgeSupport176_code
def ridgeSupport176_rest_015 : Nat := PackedRawNatGrowth.drop 6720 ridgeSupport176_code
def ridgeSupport176_rest_016 : Nat := PackedRawNatGrowth.drop 7126 ridgeSupport176_code
def ridgeSupport176_suffix_016 : List Nat := []
def ridgeSupport176_suffix_015 : List Nat := ridgeSupport176_015 ++ ridgeSupport176_suffix_016
def ridgeSupport176_suffix_014 : List Nat := ridgeSupport176_014 ++ ridgeSupport176_suffix_015
def ridgeSupport176_suffix_013 : List Nat := ridgeSupport176_013 ++ ridgeSupport176_suffix_014
def ridgeSupport176_suffix_012 : List Nat := ridgeSupport176_012 ++ ridgeSupport176_suffix_013
def ridgeSupport176_suffix_011 : List Nat := ridgeSupport176_011 ++ ridgeSupport176_suffix_012
def ridgeSupport176_suffix_010 : List Nat := ridgeSupport176_010 ++ ridgeSupport176_suffix_011
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
theorem ridgeSupport176_source : candidateRows 176 =
    (PackedRawNatGrowth.readList 14 509 ridgeSupport176_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase01
