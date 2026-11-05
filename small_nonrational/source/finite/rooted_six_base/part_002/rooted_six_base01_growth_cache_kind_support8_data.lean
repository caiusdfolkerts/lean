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
def kindSupport8_000 : List Nat := [14406,14407,14408,14409,14410,14411,14412,14413,14414,14415,14416,14417,14418,14419,14420,14421,14422,14423,14424,14425,14426,14427,14428,14429,14430,14431,14432,14433,14434,14435,14436,14437]
def kindSupport8_001 : List Nat := [14438,14439,14440,14441,14442,14443,14444,14445,14446,14447,14448,14449,14450,14451,14452,14453,14454,14455,14456,14457,14458,14459,14460,14461,14462,14463,14464,14465,14466,14467,14468,14469]
def kindSupport8_002 : List Nat := [14470,14471,14472,14473,14474,14475,14476,14477,14478,14479,14480,14481,14482,14483,14484,14485,14486,14487,14488,14489,14490,14491,14492,14493,14494,14495,14496,14497,14498,14499,14500,14501]
def kindSupport8_003 : List Nat := [14502,14503,14504,14505,14506,14507,14508,14509,14510,14511,14512,14513,14514,14515,14516,14517,14518,14519,14520,14521,14522,14523,14524,14525,14526,14527,14528,14529,14530,14531,14532,14533]
def kindSupport8_004 : List Nat := [14534,14535,14536,14537,14538,14539,14540,14541,14542,14543,14544,14545,14546,14547,14548,14549,14550,14551,14552,14553,14554,14555,14556,14557,14558,14559,14560,14561,14562,14563,14564,14565]
def kindSupport8_005 : List Nat := [14566,14567,14568,14569,14570,14571,14572,14573,14574,14575,14576,14577,14578,14579,14580,14581,14582,14583,14584,14585,14586,14587,14588,14589,14590,14591,14592,14593,14594,14595,14596,14597]
def kindSupport8_006 : List Nat := [14598,14599,14600,14601,14602,14603,14604,14605,14606,14607,14608,14609,14610,14611,14612,14613,14614,14615,14616,14617,14618,14619,14620,14621,14622,14623,14624,14625,14626,14627,14628,14629]
def kindSupport8_007 : List Nat := [14630,14631,14632,14633,14634,14635,14636,14637,14638,14639,14640,14641,14642,14643,14644,14645,14646,14647,14648,14649,14650,14651,14652,14653,14654,14655,14656,14657,14658,14659,14660,14661]
def kindSupport8_008 : List Nat := [14662,14663,14664,14665,14666,14667,14668,14669,14670,14671,14672,14673,14674,14675,14676,14677,14678,14679,14680,14681]
def kindSupport8_code : Nat := 0xe567958e55f956e557954e54f952e547950e53f94ee53794ce52f94ae527948e51f946e517944e50f942e507940e4ff93ee4f793ce4ef93ae4e7938e4df936e4d7934e4cf932e4c7930e4bf92ee4b792ce4af92ae4a7928e49f926e497924e48f922e487920e47f91ee47791ce46f91ae467918e45f916e457914e44f912e447910e43f90ee43790ce42f90ae427908e41f906e417904e40f902e407900e3ff8fee3f78fce3ef8fae3e78f8e3df8f6e3d78f4e3cf8f2e3c78f0e3bf8eee3b78ece3af8eae3a78e8e39f8e6e3978e4e38f8e2e3878e0e37f8dee3778dce36f8dae3678d8e35f8d6e3578d4e34f8d2e3478d0e33f8cee3378cce32f8cae3278c8e31f8c6e3178c4e30f8c2e3078c0e2ff8bee2f78bce2ef8bae2e78b8e2df8b6e2d78b4e2cf8b2e2c78b0e2bf8aee2b78ace2af8aae2a78a8e29f8a6e2978a4e28f8a2e2878a0e27f89ee27789ce26f89ae267898e25f896e257894e24f892e247890e23f88ee23788ce22f88ae227888e21f886e217884e20f882e207880e1ff87ee1f787ce1ef87ae1e7878e1df876e1d7874e1cf872e1c7870e1bf86ee1b786ce1af86ae1a7868e19f866e197864e18f862e187860e17f85ee17785ce16f85ae167858e15f856e157854e14f852e147850e13f84ee13784ce12f84ae127848e11f846
def kindSupport8_rest_000 : Nat := PackedRawNatGrowth.drop 0 kindSupport8_code
def kindSupport8_rest_001 : Nat := PackedRawNatGrowth.drop 448 kindSupport8_code
def kindSupport8_rest_002 : Nat := PackedRawNatGrowth.drop 896 kindSupport8_code
def kindSupport8_rest_003 : Nat := PackedRawNatGrowth.drop 1344 kindSupport8_code
def kindSupport8_rest_004 : Nat := PackedRawNatGrowth.drop 1792 kindSupport8_code
def kindSupport8_rest_005 : Nat := PackedRawNatGrowth.drop 2240 kindSupport8_code
def kindSupport8_rest_006 : Nat := PackedRawNatGrowth.drop 2688 kindSupport8_code
def kindSupport8_rest_007 : Nat := PackedRawNatGrowth.drop 3136 kindSupport8_code
def kindSupport8_rest_008 : Nat := PackedRawNatGrowth.drop 3584 kindSupport8_code
def kindSupport8_rest_009 : Nat := PackedRawNatGrowth.drop 3864 kindSupport8_code
def kindSupport8_suffix_009 : List Nat := []
def kindSupport8_suffix_008 : List Nat := kindSupport8_008 ++ kindSupport8_suffix_009
def kindSupport8_suffix_007 : List Nat := kindSupport8_007 ++ kindSupport8_suffix_008
def kindSupport8_suffix_006 : List Nat := kindSupport8_006 ++ kindSupport8_suffix_007
def kindSupport8_suffix_005 : List Nat := kindSupport8_005 ++ kindSupport8_suffix_006
def kindSupport8_suffix_004 : List Nat := kindSupport8_004 ++ kindSupport8_suffix_005
def kindSupport8_suffix_003 : List Nat := kindSupport8_003 ++ kindSupport8_suffix_004
def kindSupport8_suffix_002 : List Nat := kindSupport8_002 ++ kindSupport8_suffix_003
def kindSupport8_suffix_001 : List Nat := kindSupport8_001 ++ kindSupport8_suffix_002
def kindSupport8_suffix_000 : List Nat := kindSupport8_000 ++ kindSupport8_suffix_001
theorem kindSupport8_source : kindRows 8 =
    (PackedRawNatGrowth.readList 14 276 kindSupport8_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase01
