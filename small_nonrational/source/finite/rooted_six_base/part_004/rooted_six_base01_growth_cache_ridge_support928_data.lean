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
def ridgeSupport928_000 : List Nat := [1346,1347,1348,1455,1456,1457,1564,1565,1566,1614,1615,1616,5466,5467,5468,5469,5470,5471,5562,5563,5564,5565,5566,5567,5658,5659,5660,5661,5662,5663,5730,5731]
def ridgeSupport928_001 : List Nat := [5732,5733,5734,5735,5826,5827,5828,5829,5830,5831,5922,5923,5924,5925,5926,5927,6324,6325,6326,6327,6328,6329,6336,6337,6338,6339,6340,6341,6426,6427,6428,6429]
def ridgeSupport928_002 : List Nat := [6430,6431,6522,6523,6524,6525,6526,6527,6618,6619,6620,6621,6622,6623,7020,7021,7022,7023,7024,7025,7032,7033,7034,7035,7036,7037,10248,10249,10254,10255,10260,10261]
def ridgeSupport928_003 : List Nat := [10275,10277,10281,10283,10287,10289,10296,10297,10302,10303,10308,10309,10395,10397,10401,10403,10407,10409,10443,10445,10449,10451,10455,10457,10488,10489,10494,10495,10500,10501,10515,10517]
def ridgeSupport928_004 : List Nat := [10521,10523,10527,10529,10536,10537,10542,10543,10548,10549,10635,10637,10641,10643,10647,10649,10683,10685,10689,10691,10695,10697,10980,10981,10982,10983,10984,10985,10992,10993,10994,10995]
def ridgeSupport928_005 : List Nat := [10996,10997,11016,11017,11022,11023,11028,11029,11043,11045,11049,11051,11055,11057,11064,11065,11070,11071,11076,11077,11163,11165,11169,11171,11175,11177,11211,11213,11217,11219,11223,11225]
def ridgeSupport928_006 : List Nat := [11508,11509,11510,11511,11512,11513,11520,11521,11522,11523,11524,11525,13573,13575,13577,13635,13637,13641,13643,13647,13649,13705,13707,13709,13767,13769,13773,13775,13779,13781,14022,14023]
def ridgeSupport928_007 : List Nat := [14024,14025,14026,14027,14053,14055,14057,14115,14117,14121,14123,14127,14129,14370,14371,14372,14373,14374,14375,15072,15073,15078,15079,15084,15085,15108,15109,15114,15115,15120,15121,15168]
def ridgeSupport928_008 : List Nat := [15169,15174,15175,15180,15181]
def ridgeSupport928_code : Nat := 0x3b4ded33b47ed1bb41ed03b11ec43b0bec2bb05ec13aedebb3ae7eb9bae1eb83827e09b825e093823e08b731dcbf72bdca7725dc8f6e9db9f6e5db2f6cadb276c8db1f6c6d7575d3d73f5cdd7275c7d63758bd627551d53f54bd527545d50f509d41f505b416d04b40ed02b406d00b3e6cf8b3decf6b3d6cf4af66bd7af4ebd1af36bcbaea6ba7ae8eba1ae76b9bad16b44acfeb3eace6b38acc6b2facaeb29ac96b23ac56b14ac3eb0eac26b08abd6af4abceaf2abc6af0aba6ae8ab9eae6ab96ae4a7269c7a70e9c1a6f69bba666997a64e991a63698ba4d6934a4be92ea4a6928a48691fa46e919a456913a416904a3fe8fea3e68f8a3668d7a34e8d1a3368cba2a68a7a28e8a1a27689ba116844a0fe83ea0e6838a0c682fa0ae829a096823a056814a03e80ea0268086df5b7c6dedb7a6de5b786dc5b706dbdb6e6db5b6c677d9de67759dc676d9da65fd97e65f597c65ed97a647d91e647591c646d91a63158c4630d8c263058c062e58b862dd8b662d58b45c9d7265c957245c8d7225b1d6c65b156c45b0d6c2599d6665995664598d662587d61e587561c586d61a56fd5be56f55bc56ed5ba557d55e557555c556d55a194064f193861e187461c16c45b016bc544150c542
def ridgeSupport928_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport928_code
def ridgeSupport928_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport928_code
def ridgeSupport928_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport928_code
def ridgeSupport928_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport928_code
def ridgeSupport928_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport928_code
def ridgeSupport928_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport928_code
def ridgeSupport928_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport928_code
def ridgeSupport928_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport928_code
def ridgeSupport928_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport928_code
def ridgeSupport928_rest_009 : Nat := PackedRawNatGrowth.drop 3654 ridgeSupport928_code
def ridgeSupport928_suffix_009 : List Nat := []
def ridgeSupport928_suffix_008 : List Nat := ridgeSupport928_008 ++ ridgeSupport928_suffix_009
def ridgeSupport928_suffix_007 : List Nat := ridgeSupport928_007 ++ ridgeSupport928_suffix_008
def ridgeSupport928_suffix_006 : List Nat := ridgeSupport928_006 ++ ridgeSupport928_suffix_007
def ridgeSupport928_suffix_005 : List Nat := ridgeSupport928_005 ++ ridgeSupport928_suffix_006
def ridgeSupport928_suffix_004 : List Nat := ridgeSupport928_004 ++ ridgeSupport928_suffix_005
def ridgeSupport928_suffix_003 : List Nat := ridgeSupport928_003 ++ ridgeSupport928_suffix_004
def ridgeSupport928_suffix_002 : List Nat := ridgeSupport928_002 ++ ridgeSupport928_suffix_003
def ridgeSupport928_suffix_001 : List Nat := ridgeSupport928_001 ++ ridgeSupport928_suffix_002
def ridgeSupport928_suffix_000 : List Nat := ridgeSupport928_000 ++ ridgeSupport928_suffix_001
theorem ridgeSupport928_source : candidateRows 928 =
    (PackedRawNatGrowth.readList 14 261 ridgeSupport928_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase01
