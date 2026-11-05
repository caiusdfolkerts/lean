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
def ridgeSupport82_000 : List Nat := [35,45,55,56,57,624,625,628,629,634,636,637,640,641,646,648,649,652,653,658,780,781,784,785,790,792,793,796,797,802,804,805]
def ridgeSupport82_001 : List Nat := [808,809,814,936,937,939,940,941,942,944,945,947,948,950,951,957,958,960,961,962,963,965,966,968,969,971,972,978,979,981,982,983]
def ridgeSupport82_002 : List Nat := [984,986,987,989,990,992,993,4168,4169,4170,4171,4172,4173,4174,4175,4180,4181,4186,4187,4192,4193,4194,4195,4196,4197,4198,4199,4204,4205,4210,4211,4216]
def ridgeSupport82_003 : List Nat := [4217,4218,4219,4220,4221,4240,4241,4242,4243,4244,4245,4264,4265,4266,4267,4268,4269,4288,4289,4290,4291,4292,4293,4312,4313,4314,4315,4316,4317,4336,4337,4338]
def ridgeSupport82_004 : List Nat := [4339,4340,4341,4360,4361,4362,4363,4364,4365,4369,4371,4375,4377,4381,4383,4654,4655,4672,4673,4690,4691,4699,4701,4705,4707,4708,4709,4726,4727,4744,4745,4762]
def ridgeSupport82_005 : List Nat := [4763,4771,4773,4777,4779,4780,4781,4798,4799,4816,4817,4834,4835,4843,4845,4849,4851,4852,4853,5182,5183,5200,5201,5218,5219,5227,5229,5233,5235,5236,5237,5254]
def ridgeSupport82_006 : List Nat := [5255,5272,5273,5290,5291,5299,5301,5305,5307,5308,5309,5326,5327,5344,5345,5362,5363,5371,5373,5377,5379,5380,5381,7336,7337,7338,7339,7340,7341,8176,8177,8178]
def ridgeSupport82_007 : List Nat := [8179,8180,8181,8200,8201,8202,8203,8204,8205,8212,8213,8214,8215,8216,8217,8275,8277,8284,8285,8293,8295,8302,8303,8311,8313,8320,8321,8395,8397,8404,8405,8413]
def ridgeSupport82_008 : List Nat := [8415,8422,8423,8431,8433,8440,8441]
def ridgeSupport82_code : Nat := 0x20f983e20f183be0e7839a0df83760d583520cd832e081820207981de06f81ba067819605d8172055814e0198062017805a015805200d803200b802a0098021ff57fd1ff37fc9ff17fc1cad72b1cab72a9ca972a1505541150354054fd53ed4f353c94e153814cf53394bd52f14bb52e54b552cd4ab52a94995261487521947551d147351c546d51ad4635189451514143f50f92f54bd12f34bc52ed4bad2e34b892d14b412bf4af92ad4ab12ab4aa52a54a8d29b4a692894a2127749d92654991263498525d496d2534949241490122f48b911f4475119445d113444510d443110b442910944210f543d10f343c90f143c10dd43710db43690d943610c543110c343090c143010ad42b10ab42a90a942a109542510934249091424107d41f107b41e907941e107341c906d41b1067419906541910634189061418105b4169055415104f413904d413104b412904941203e10f803de0f743db0f683d80f5c3d60f543d30f483cc0f2c3c90f203c60f143c30f083c10f003be0ef43b70ed83b40ecc3b10ec03ae0eb43ac0eac3a90ea032e0ca43280c943240c8831d0c703190c603160c443100c3430c0a4828d0a302890a202860a0428009f427c09e827509d027109c003900e003700b4023
def ridgeSupport82_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport82_code
def ridgeSupport82_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport82_code
def ridgeSupport82_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport82_code
def ridgeSupport82_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport82_code
def ridgeSupport82_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport82_code
def ridgeSupport82_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport82_code
def ridgeSupport82_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport82_code
def ridgeSupport82_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport82_code
def ridgeSupport82_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport82_code
def ridgeSupport82_rest_009 : Nat := PackedRawNatGrowth.drop 3682 ridgeSupport82_code
def ridgeSupport82_suffix_009 : List Nat := []
def ridgeSupport82_suffix_008 : List Nat := ridgeSupport82_008 ++ ridgeSupport82_suffix_009
def ridgeSupport82_suffix_007 : List Nat := ridgeSupport82_007 ++ ridgeSupport82_suffix_008
def ridgeSupport82_suffix_006 : List Nat := ridgeSupport82_006 ++ ridgeSupport82_suffix_007
def ridgeSupport82_suffix_005 : List Nat := ridgeSupport82_005 ++ ridgeSupport82_suffix_006
def ridgeSupport82_suffix_004 : List Nat := ridgeSupport82_004 ++ ridgeSupport82_suffix_005
def ridgeSupport82_suffix_003 : List Nat := ridgeSupport82_003 ++ ridgeSupport82_suffix_004
def ridgeSupport82_suffix_002 : List Nat := ridgeSupport82_002 ++ ridgeSupport82_suffix_003
def ridgeSupport82_suffix_001 : List Nat := ridgeSupport82_001 ++ ridgeSupport82_suffix_002
def ridgeSupport82_suffix_000 : List Nat := ridgeSupport82_000 ++ ridgeSupport82_suffix_001
theorem ridgeSupport82_source : candidateSupports 82 =
    (PackedRawNatGrowth.readList 14 263 ridgeSupport82_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
