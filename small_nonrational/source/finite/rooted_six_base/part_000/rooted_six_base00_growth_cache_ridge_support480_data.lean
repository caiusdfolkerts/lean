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
def ridgeSupport480_000 : List Nat := [1365,1366,1367,1630,1631,1632,1739,1740,1741,1861,1862,1863,10450,10451,10452,10453,10454,10455,10546,10547,10548,10549,10550,10551,10642,10643,10644,10645,10646,10647,10714,10715]
def ridgeSupport480_001 : List Nat := [10716,10717,10718,10719,10810,10811,10812,10813,10814,10815,10906,10907,10908,10909,10910,10911,10966,10967,10968,10969,10970,10971,10978,10979,10980,10981,10982,10983,11410,11411,11412,11413]
def ridgeSupport480_002 : List Nat := [11414,11415,11506,11507,11508,11509,11510,11511,11602,11603,11604,11605,11606,11607,11662,11663,11664,11665,11666,11667,11674,11675,11676,11677,11678,11679,12094,12095,12096,12097,12098,12099]
def ridgeSupport480_003 : List Nat := [12106,12107,12108,12109,12110,12111,16124,16125,16130,16131,16136,16137,16144,16146,16150,16152,16156,16158,16172,16173,16178,16179,16184,16185,16264,16266,16270,16272,16276,16278,16312,16314]
def ridgeSupport480_004 : List Nat := [16318,16320,16324,16326,16364,16365,16370,16371,16376,16377,16384,16386,16390,16392,16396,16398,16412,16413,16418,16419,16424,16425,16504,16506,16510,16512,16516,16518,16552,16554,16558,16560]
def ridgeSupport480_005 : List Nat := [16564,16566,16642,16643,16644,16645,16646,16647,16654,16655,16656,16657,16658,16659,16892,16893,16898,16899,16904,16905,16912,16914,16918,16920,16924,16926,16940,16941,16946,16947,16952,16953]
def ridgeSupport480_006 : List Nat := [17032,17034,17038,17040,17044,17046,17080,17082,17086,17088,17092,17094,17170,17171,17172,17173,17174,17175,17182,17183,17184,17185,17186,17187,17458,17459,17460,17461,17462,17463,17470,17471]
def ridgeSupport480_007 : List Nat := [17472,17473,17474,17475,19984,19986,19990,20044,20046,20050,20052,20056,20058,20116,20118,20122,20176,20178,20182,20184,20188,20190,20278,20279,20280,20281,20282,20283,20464,20466,20470,20524]
def ridgeSupport480_008 : List Nat := [20526,20530,20532,20536,20538,20626,20627,20628,20629,20630,20631,20842,20843,20844,20845,20846,20847,21800,21801,21806,21807,21812,21813,21836,21837,21842,21843,21848,21849,21896,21897,21902]
def ridgeSupport480_009 : List Nat := [21903,21908,21909]
def ridgeSupport480_code : Nat := 0x15656aca558fab1d5626ac45559aab1554eaa9554daa9954d6a9a552faa5d54a6a94516fa2dd45b68b6516ba2d5425e84b5095a129424e849503aa07140d2819502ea0593fda7f94ff09e773cea79ccf389e6f3cda76f4edc9db13b5a7694ed09d353a5a74a4e5a9cb139527294e4e9c99385a7094e108887110a220c440887f10fa21bc436886b10d2219c43286470c8a190c320863f0c7a18bc316862b0c52189c312858d0b1216042be85750ae214b429485210a3a1454288847308e2119c232845b08b210f421c8431085a109421084130822101c20283fb07f2089c11282230442087c10e820f041a082c1048207040a05b40b4816102ba05540a8810d0212040407e80f501e2014c0288047008a00ec01c801d0032004400680050001ffcbff87fe6ffc9ff6bfec7f8cff11fe03fbe7f74fee1fcb3f947f20fe39fc53f887e72fce1f99bf327e5afcb1f8f3f1c7e30fc59f893f107e12fc21f81bf027dfafbf17a7af4e5e9abd317a5af4a5e86bd097a0af405e7ebcf96cfad9e5b3ab6716cdad9a5b26b6496c8ad905b1eb6396abad565aaab5516a9ad5259eeb3d967aacf459e6b3c964bac96592ab251649ac9255ceab99572aae455c6ab8956daada55b2ab6156baad6553eaa7954eaa9c5536aa6951faa3e547aa8f151daa3a53bea7794eea9dc53b6a7694cba996532aa6514c9a992526ea4d949aa9345266a4c946ba8d651aaa351469a8d20e8e1d183a286cd0d981b2c330065f0cbc155c2ab0555
def ridgeSupport480_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport480_code
def ridgeSupport480_rest_001 : Nat := PackedRawNatGrowth.drop 480 ridgeSupport480_code
def ridgeSupport480_rest_002 : Nat := PackedRawNatGrowth.drop 960 ridgeSupport480_code
def ridgeSupport480_rest_003 : Nat := PackedRawNatGrowth.drop 1440 ridgeSupport480_code
def ridgeSupport480_rest_004 : Nat := PackedRawNatGrowth.drop 1920 ridgeSupport480_code
def ridgeSupport480_rest_005 : Nat := PackedRawNatGrowth.drop 2400 ridgeSupport480_code
def ridgeSupport480_rest_006 : Nat := PackedRawNatGrowth.drop 2880 ridgeSupport480_code
def ridgeSupport480_rest_007 : Nat := PackedRawNatGrowth.drop 3360 ridgeSupport480_code
def ridgeSupport480_rest_008 : Nat := PackedRawNatGrowth.drop 3840 ridgeSupport480_code
def ridgeSupport480_rest_009 : Nat := PackedRawNatGrowth.drop 4320 ridgeSupport480_code
def ridgeSupport480_rest_010 : Nat := PackedRawNatGrowth.drop 4365 ridgeSupport480_code
def ridgeSupport480_suffix_010 : List Nat := []
def ridgeSupport480_suffix_009 : List Nat := ridgeSupport480_009 ++ ridgeSupport480_suffix_010
def ridgeSupport480_suffix_008 : List Nat := ridgeSupport480_008 ++ ridgeSupport480_suffix_009
def ridgeSupport480_suffix_007 : List Nat := ridgeSupport480_007 ++ ridgeSupport480_suffix_008
def ridgeSupport480_suffix_006 : List Nat := ridgeSupport480_006 ++ ridgeSupport480_suffix_007
def ridgeSupport480_suffix_005 : List Nat := ridgeSupport480_005 ++ ridgeSupport480_suffix_006
def ridgeSupport480_suffix_004 : List Nat := ridgeSupport480_004 ++ ridgeSupport480_suffix_005
def ridgeSupport480_suffix_003 : List Nat := ridgeSupport480_003 ++ ridgeSupport480_suffix_004
def ridgeSupport480_suffix_002 : List Nat := ridgeSupport480_002 ++ ridgeSupport480_suffix_003
def ridgeSupport480_suffix_001 : List Nat := ridgeSupport480_001 ++ ridgeSupport480_suffix_002
def ridgeSupport480_suffix_000 : List Nat := ridgeSupport480_000 ++ ridgeSupport480_suffix_001
theorem ridgeSupport480_source : candidateRows 480 =
    (PackedRawNatGrowth.readList 15 291 ridgeSupport480_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase00
