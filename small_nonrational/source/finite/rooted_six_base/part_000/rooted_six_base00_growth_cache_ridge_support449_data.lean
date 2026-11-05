module
prelude
public import RootedSixBase00GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport449_000 : List Nat := [286,287,288,442,443,444,526,527,528,620,621,622,5938,5939,5940,5941,5942,5943,5986,5987,5988,5989,5990,5991,6130,6131,6132,6133,6134,6135,6202,6203]
def ridgeSupport449_001 : List Nat := [6204,6205,6206,6207,6250,6251,6252,6253,6254,6255,6394,6395,6396,6397,6398,6399,6700,6701,6702,6703,6704,6705,6712,6713,6714,6715,6716,6717,7162,7163,7164,7165]
def ridgeSupport449_002 : List Nat := [7166,7167,7210,7211,7212,7213,7214,7215,7354,7355,7356,7357,7358,7359,7660,7661,7662,7663,7664,7665,7672,7673,7674,7675,7676,7677,8356,8357,8358,8359,8360,8361]
def ridgeSupport449_003 : List Nat := [8368,8369,8370,8371,8372,8373,12520,12522,12526,12528,12532,12534,12548,12549,12554,12555,12560,12561,12596,12597,12602,12603,12608,12609,12688,12690,12694,12696,12700,12702,12730,12731]
def ridgeSupport449_004 : List Nat := [12732,12733,12734,12735,12760,12762,12766,12768,12772,12774,12788,12789,12794,12795,12800,12801,12836,12837,12842,12843,12848,12849,12928,12930,12934,12936,12940,12942,12970,12971,12972,12973]
def ridgeSupport449_005 : List Nat := [12974,12975,13288,13289,13290,13291,13292,13293,13300,13301,13302,13303,13304,13305,13528,13530,13534,13536,13540,13542,13556,13557,13562,13563,13568,13569,13604,13605,13610,13611,13616,13617]
def ridgeSupport449_006 : List Nat := [13696,13698,13702,13704,13708,13710,13738,13739,13740,13741,13742,13743,14056,14057,14058,14059,14060,14061,14068,14069,14070,14071,14072,14073,14584,14585,14586,14587,14588,14589,14596,14597]
def ridgeSupport449_007 : List Nat := [14598,14599,14600,14601,17704,17706,17710,17800,17802,17806,17808,17812,17814,17836,17838,17842,17932,17934,17938,17940,17944,17946,18148,18149,18150,18151,18152,18153,18316,18318,18322,18412]
def ridgeSupport449_008 : List Nat := [18414,18418,18420,18424,18426,18628,18629,18630,18631,18632,18633,18976,18977,18978,18979,18980,18981,21353,21355,21359,21361,21365,21367,21389,21391,21395,21397,21401,21403,21485,21487,21491]
def ridgeSupport449_009 : List Nat := [21493,21497,21499]
def ridgeSupport449_code : Nat := 0x14fee9fcd3f5a7e74fbe9f6d39ba7334e569c9d38fa71b4dde9bad371a6df4dae9b4ca259449288e5114a219441232646448c7918d231646247fa8ff11fd23f947ee8fd91e4a3c7478c8dd31ba2373c6e68dcb1b9230d46188c29184a307460c8b6516ba2d645968b2916422c7458a8b1114ba29545287212e421c83b906720ae411c7eb8fc71f6e3e9c7cb8f86df2dbe1b7bb6f66deadbd1b76b6ec6dd6dba9b74b6e86b5ed6b9ad6b5ac6b56d6a9ac7358c6b10d619ac135806a62d4c1a95b52a6a4ad491a80b50069f6d3e9a7ab4f469ccd391a7034de69b4d3619fcb3f867eecfd99fab3f467dacfb19f5b3ea67d2cfa1957b2ae655acab1955b2aa651cca3194432866504ca01918b2306456c8a9912b2246402c8018fdb1fa63eac7d18f331e463c0c7798ed31d8637ec6f98deb1bc6376c6e98cf319c6330c6598c931906282c50189db13a626ac4d1888b1106216c429882b10461ecc3d187830ee61d4c3a105aa0b4416682c9058a0b0415282a1053a0a6414a8290efe9dfc3bf677e8efc9df83be277c0ef79dee3bda77b0e5f9cbe397a72f0e5d9cba385e70b8e169c2c385670a8dff9bfe37fa6ff0dfd9bfa347a68f0d1d9a3a347268e0d189a30345e68b8d169a2c31fe63f8c7e98fc31f663e8c37986e30da61b0c35986a307e60f8c1e983c307660e8bfb97f62fea5fd0bf997f22ece5d98bb297642ec65d88b9b97362e6a5cd0b99973204dc09b41360210041e08380de01bb0374048008f811e
def ridgeSupport449_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport449_code
def ridgeSupport449_rest_001 : Nat := PackedRawNatGrowth.drop 480 ridgeSupport449_code
def ridgeSupport449_rest_002 : Nat := PackedRawNatGrowth.drop 960 ridgeSupport449_code
def ridgeSupport449_rest_003 : Nat := PackedRawNatGrowth.drop 1440 ridgeSupport449_code
def ridgeSupport449_rest_004 : Nat := PackedRawNatGrowth.drop 1920 ridgeSupport449_code
def ridgeSupport449_rest_005 : Nat := PackedRawNatGrowth.drop 2400 ridgeSupport449_code
def ridgeSupport449_rest_006 : Nat := PackedRawNatGrowth.drop 2880 ridgeSupport449_code
def ridgeSupport449_rest_007 : Nat := PackedRawNatGrowth.drop 3360 ridgeSupport449_code
def ridgeSupport449_rest_008 : Nat := PackedRawNatGrowth.drop 3840 ridgeSupport449_code
def ridgeSupport449_rest_009 : Nat := PackedRawNatGrowth.drop 4320 ridgeSupport449_code
def ridgeSupport449_rest_010 : Nat := PackedRawNatGrowth.drop 4365 ridgeSupport449_code
def ridgeSupport449_suffix_010 : List Nat := []
def ridgeSupport449_suffix_009 : List Nat := ridgeSupport449_009 ++ ridgeSupport449_suffix_010
def ridgeSupport449_suffix_008 : List Nat := ridgeSupport449_008 ++ ridgeSupport449_suffix_009
def ridgeSupport449_suffix_007 : List Nat := ridgeSupport449_007 ++ ridgeSupport449_suffix_008
def ridgeSupport449_suffix_006 : List Nat := ridgeSupport449_006 ++ ridgeSupport449_suffix_007
def ridgeSupport449_suffix_005 : List Nat := ridgeSupport449_005 ++ ridgeSupport449_suffix_006
def ridgeSupport449_suffix_004 : List Nat := ridgeSupport449_004 ++ ridgeSupport449_suffix_005
def ridgeSupport449_suffix_003 : List Nat := ridgeSupport449_003 ++ ridgeSupport449_suffix_004
def ridgeSupport449_suffix_002 : List Nat := ridgeSupport449_002 ++ ridgeSupport449_suffix_003
def ridgeSupport449_suffix_001 : List Nat := ridgeSupport449_001 ++ ridgeSupport449_suffix_002
def ridgeSupport449_suffix_000 : List Nat := ridgeSupport449_000 ++ ridgeSupport449_suffix_001
theorem ridgeSupport449_source : candidateRows 449 =
    (PackedRawNatGrowth.readList 15 291 ridgeSupport449_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase00
