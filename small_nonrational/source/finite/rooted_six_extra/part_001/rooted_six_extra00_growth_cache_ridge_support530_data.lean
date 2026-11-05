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
def ridgeSupport530_000 : List Nat := [38,48,57,59,60,647,650,651,654,657,671,674,675,678,681,683,686,687,690,693,803,806,807,810,813,827,830,831,834,837,839,842]
def ridgeSupport530_001 : List Nat := [843,846,849,956,957,959,960,963,964,965,967,968,970,975,976,977,978,980,981,984,985,986,988,989,991,996,997,998,999,1001,1002,1005]
def ridgeSupport530_002 : List Nat := [1006,1007,1009,1010,1012,1017,1018,4172,4173,4178,4179,4184,4185,4186,4187,4188,4189,4190,4191,4196,4197,4202,4203,4208,4209,4210,4211,4212,4213,4214,4215,4234]
def ridgeSupport530_003 : List Nat := [4235,4236,4237,4238,4239,4258,4259,4260,4261,4262,4263,4282,4283,4284,4285,4286,4287,4306,4307,4308,4309,4310,4311,4330,4331,4332,4333,4334,4335,4354,4355,4356]
def ridgeSupport530_004 : List Nat := [4357,4358,4359,4360,4362,4366,4368,4372,4374,4378,4379,4380,4381,4382,4383,4730,4731,4748,4749,4766,4767,4768,4770,4774,4776,4784,4785,4802,4803,4820,4821,4838]
def ridgeSupport530_005 : List Nat := [4839,4840,4842,4846,4848,4856,4857,4874,4875,4892,4893,4910,4911,4912,4914,4918,4920,4928,4929,5258,5259,5276,5277,5294,5295,5296,5298,5302,5304,5312,5313,5330]
def ridgeSupport530_006 : List Nat := [5331,5348,5349,5366,5367,5368,5370,5374,5376,5384,5385,5402,5403,5420,5421,5438,5439,5440,5442,5446,5448,5456,5457,7354,7355,7356,7357,7358,7359,8194,8195,8196]
def ridgeSupport530_007 : List Nat := [8197,8198,8199,8200,8202,8206,8208,8210,8211,8212,8214,8218,8220,8222,8223,8290,8292,8306,8307,8308,8310,8324,8325,8326,8328,8342,8343,8410,8412,8426,8427,8428]
def ridgeSupport530_008 : List Nat := [8430,8444,8445,8446,8448,8462,8463]
def ridgeSupport530_code : Nat := 0x210f843a10083fa0fd83f20ee83b20eb83aa0dc836a097825a088821a085821207681d207381ca064818a01f807a01c806a0168052013804a010803a00a8022007801a00580120038009cbf72f9cbd72f1cbb72e955155415485519542550153f54f952d54b151b5469509542150053f94fa53e14f753d94e553914d353494c153014b852d94b252c14af52b949d527148b52293414d013384cd93324cc132f4cb931d4c7130b4c292f94be12f04bb92ea4ba12e74b992d54b512c34b092b14ac12a84a992a24a8129f4a7928d4a3127b49e911f447911d447111b44691164451110443910a44211074419105441110344090ef43b90ed43b10eb43a90d743590d543510d343490bf42f90bd42f10bb42e90a742990a542910a3428908f423908d423108b422907741d907541d107341c907141c106b41a9065419105f417905d417105b41690594161053414904d41303fa0fe43f40fc83f10fbc3ee0fb43ea0fa43e70f983e50f903df0f743dc0f683d90f603d50f503d20f443d00f3c3ca0f203c70f143c40f0c3c00efc3bd0ef03510d3834b0d283470d143420cfc33e0cec32d0ca83270c983230ad42b20abc2ae0aac2a90a982a30a8829f0a4428e0a2c28a0a1c03c00ec03900c0026
def ridgeSupport530_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport530_code
def ridgeSupport530_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport530_code
def ridgeSupport530_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport530_code
def ridgeSupport530_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport530_code
def ridgeSupport530_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport530_code
def ridgeSupport530_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport530_code
def ridgeSupport530_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport530_code
def ridgeSupport530_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport530_code
def ridgeSupport530_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport530_code
def ridgeSupport530_rest_009 : Nat := PackedRawNatGrowth.drop 3682 ridgeSupport530_code
def ridgeSupport530_suffix_009 : List Nat := []
def ridgeSupport530_suffix_008 : List Nat := ridgeSupport530_008 ++ ridgeSupport530_suffix_009
def ridgeSupport530_suffix_007 : List Nat := ridgeSupport530_007 ++ ridgeSupport530_suffix_008
def ridgeSupport530_suffix_006 : List Nat := ridgeSupport530_006 ++ ridgeSupport530_suffix_007
def ridgeSupport530_suffix_005 : List Nat := ridgeSupport530_005 ++ ridgeSupport530_suffix_006
def ridgeSupport530_suffix_004 : List Nat := ridgeSupport530_004 ++ ridgeSupport530_suffix_005
def ridgeSupport530_suffix_003 : List Nat := ridgeSupport530_003 ++ ridgeSupport530_suffix_004
def ridgeSupport530_suffix_002 : List Nat := ridgeSupport530_002 ++ ridgeSupport530_suffix_003
def ridgeSupport530_suffix_001 : List Nat := ridgeSupport530_001 ++ ridgeSupport530_suffix_002
def ridgeSupport530_suffix_000 : List Nat := ridgeSupport530_000 ++ ridgeSupport530_suffix_001
theorem ridgeSupport530_source : candidateSupports 530 =
    (PackedRawNatGrowth.readList 14 263 ridgeSupport530_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
