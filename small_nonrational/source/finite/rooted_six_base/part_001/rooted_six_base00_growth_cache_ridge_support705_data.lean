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
def ridgeSupport705_000 : List Nat := [307,308,309,463,464,465,547,548,549,617,618,619,5932,5933,5934,5935,5936,5937,5980,5981,5982,5983,5984,5985,6124,6125,6126,6127,6128,6129,6196,6197]
def ridgeSupport705_001 : List Nat := [6198,6199,6200,6201,6244,6245,6246,6247,6248,6249,6388,6389,6390,6391,6392,6393,6808,6809,6810,6811,6812,6813,6820,6821,6822,6823,6824,6825,7156,7157,7158,7159]
def ridgeSupport705_002 : List Nat := [7160,7161,7204,7205,7206,7207,7208,7209,7348,7349,7350,7351,7352,7353,7768,7769,7770,7771,7772,7773,7780,7781,7782,7783,7784,7785,8464,8465,8466,8467,8468,8469]
def ridgeSupport705_003 : List Nat := [8476,8477,8478,8479,8480,8481,12521,12524,12527,12530,12538,12540,12546,12547,12552,12553,12566,12567,12594,12595,12600,12601,12614,12615,12689,12692,12695,12698,12706,12708,12724,12725]
def ridgeSupport705_004 : List Nat := [12726,12727,12728,12729,12761,12764,12767,12770,12778,12780,12786,12787,12792,12793,12806,12807,12834,12835,12840,12841,12854,12855,12929,12932,12935,12938,12946,12948,12964,12965,12966,12967]
def ridgeSupport705_005 : List Nat := [12968,12969,13360,13361,13362,13363,13364,13365,13372,13373,13374,13375,13376,13377,13529,13532,13535,13538,13546,13548,13554,13555,13560,13561,13574,13575,13602,13603,13608,13609,13622,13623]
def ridgeSupport705_006 : List Nat := [13697,13700,13703,13706,13714,13716,13732,13733,13734,13735,13736,13737,14128,14129,14130,14131,14132,14133,14140,14141,14142,14143,14144,14145,14656,14657,14658,14659,14660,14661,14668,14669]
def ridgeSupport705_007 : List Nat := [14670,14671,14672,14673,17705,17708,17712,17801,17804,17807,17810,17818,17820,17837,17840,17844,17933,17936,17939,17942,17950,17952,18202,18203,18204,18205,18206,18207,18317,18320,18324,18413]
def ridgeSupport705_008 : List Nat := [18416,18419,18422,18430,18432,18682,18683,18684,18685,18686,18687,19030,19031,19032,19033,19034,19035,21352,21357,21358,21363,21371,21373,21388,21393,21394,21399,21407,21409,21484,21489,21490]
def ridgeSupport705_009 : List Nat := [21495,21503,21505]
def ridgeSupport705_code : Nat := 0x150069ffd3f7a7e54fc69f653a1a73f4e5e9c95391a7194df69bdd373a6dd4db69b44a5b94b5296652c4a5794ad23fe47f48fd91f923ee47d48008ffd1fda3f9c7f08fdb1e523c8478d8e3f1c7a38ec71c8e371c6a310461e8c2d184e308460d8b6916c22d6c59c8b35164a2c7c58c8b1314c2296452972a2e541ca7b94e729ae531ca2b9447286e509ca0b9406e82dd01b9fb73e6e7adcf1b9ab7346e66dcc9b98b7306b52d6a1ad3b5a66b4ad691aca35926b14d61dac235816a6ed4d9a94b5286a46d489a83b50669f2d3e1a79b4f269d8d3a9a7134df69b8d365a20b440687ed0f9a1eb43c686ad0d1a19b4326862d0c1954b2a8654eca99952b2a46528ca4994532876508ca0591bb2366452c8a1911b222640ec8198fcb1f863e6c7c98f631ea63c4c77d8ee31d96372c6e18dbb1b6636ac6d18d231a26334c65d8ca3191628ec51989cb1386266c4c988bb1166212c421881b10261f8c3e987930ef61d8c3a5090a120423e847908ea11c422a8451089a11242228440f349e683cce7998f329e643cba7970f2d9e5a3cb27960e5c9cb8396e72d8e5a9cb4385270a0e139c26384a7090dfc9bf837ee6fd8dfa9bf435526aa0d539aa6354a6a90d4e9a9c35366a68d4c9a9831f263e0c7b98f631ea63d0c34986830ce6198c329864307260e0c1b9836306a60d0bf897f02fde5fb8bf697ec2ec25d80baf975e2eba5d70b9897302e5e5cb8b96972c04d609a813482250448088c0e881d0039e04d409a0133
def ridgeSupport705_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport705_code
def ridgeSupport705_rest_001 : Nat := PackedRawNatGrowth.drop 480 ridgeSupport705_code
def ridgeSupport705_rest_002 : Nat := PackedRawNatGrowth.drop 960 ridgeSupport705_code
def ridgeSupport705_rest_003 : Nat := PackedRawNatGrowth.drop 1440 ridgeSupport705_code
def ridgeSupport705_rest_004 : Nat := PackedRawNatGrowth.drop 1920 ridgeSupport705_code
def ridgeSupport705_rest_005 : Nat := PackedRawNatGrowth.drop 2400 ridgeSupport705_code
def ridgeSupport705_rest_006 : Nat := PackedRawNatGrowth.drop 2880 ridgeSupport705_code
def ridgeSupport705_rest_007 : Nat := PackedRawNatGrowth.drop 3360 ridgeSupport705_code
def ridgeSupport705_rest_008 : Nat := PackedRawNatGrowth.drop 3840 ridgeSupport705_code
def ridgeSupport705_rest_009 : Nat := PackedRawNatGrowth.drop 4320 ridgeSupport705_code
def ridgeSupport705_rest_010 : Nat := PackedRawNatGrowth.drop 4365 ridgeSupport705_code
def ridgeSupport705_suffix_010 : List Nat := []
def ridgeSupport705_suffix_009 : List Nat := ridgeSupport705_009 ++ ridgeSupport705_suffix_010
def ridgeSupport705_suffix_008 : List Nat := ridgeSupport705_008 ++ ridgeSupport705_suffix_009
def ridgeSupport705_suffix_007 : List Nat := ridgeSupport705_007 ++ ridgeSupport705_suffix_008
def ridgeSupport705_suffix_006 : List Nat := ridgeSupport705_006 ++ ridgeSupport705_suffix_007
def ridgeSupport705_suffix_005 : List Nat := ridgeSupport705_005 ++ ridgeSupport705_suffix_006
def ridgeSupport705_suffix_004 : List Nat := ridgeSupport705_004 ++ ridgeSupport705_suffix_005
def ridgeSupport705_suffix_003 : List Nat := ridgeSupport705_003 ++ ridgeSupport705_suffix_004
def ridgeSupport705_suffix_002 : List Nat := ridgeSupport705_002 ++ ridgeSupport705_suffix_003
def ridgeSupport705_suffix_001 : List Nat := ridgeSupport705_001 ++ ridgeSupport705_suffix_002
def ridgeSupport705_suffix_000 : List Nat := ridgeSupport705_000 ++ ridgeSupport705_suffix_001
theorem ridgeSupport705_source : candidateRows 705 =
    (PackedRawNatGrowth.readList 15 291 ridgeSupport705_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase00
