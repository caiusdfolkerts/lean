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
def ridgeSupport848_000 : List Nat := [904,905,906,1241,1242,1243,1546,1547,1548,1592,1593,1594,4512,4513,4514,4515,4516,4517,4608,4609,4610,4611,4612,4613,4704,4705,4706,4707,4708,4709,4776,4777]
def ridgeSupport848_001 : List Nat := [4778,4779,4780,4781,4872,4873,4874,4875,4876,4877,4968,4969,4970,4971,4972,4973,5256,5257,5258,5259,5260,5261,5268,5269,5270,5271,5272,5273,6456,6457,6458,6459]
def ridgeSupport848_002 : List Nat := [6460,6461,6504,6505,6506,6507,6508,6509,6648,6649,6650,6651,6652,6653,6906,6907,6908,6909,6910,6911,6936,6937,6938,6939,6940,6941,9474,9475,9488,9489,9494,9495]
def ridgeSupport848_003 : List Nat := [9501,9503,9511,9514,9517,9520,9522,9523,9536,9537,9542,9543,9621,9623,9631,9634,9637,9640,9669,9671,9679,9682,9685,9688,9714,9715,9728,9729,9734,9735,9741,9743]
def ridgeSupport848_004 : List Nat := [9751,9754,9757,9760,9762,9763,9776,9777,9782,9783,9861,9863,9871,9874,9877,9880,9909,9911,9919,9922,9925,9928,10140,10141,10142,10143,10144,10145,10152,10153,10154,10155]
def ridgeSupport848_005 : List Nat := [10156,10157,11013,11015,11023,11026,11029,11032,11034,11035,11048,11049,11054,11055,11082,11083,11096,11097,11102,11103,11181,11183,11191,11194,11197,11200,11208,11209,11210,11211,11212,11213]
def ridgeSupport848_006 : List Nat := [11430,11431,11432,11433,11434,11435,11460,11461,11462,11463,11464,11465,13089,13091,13096,13149,13151,13159,13162,13165,13168,13221,13223,13228,13281,13283,13291,13294,13297,13300,13488,13489]
def ridgeSupport848_007 : List Nat := [13490,13491,13492,13493,14037,14039,14044,14133,14135,14143,14146,14149,14152,14310,14311,14312,14313,14314,14315,14970,14971,14984,14985,14990,14991,15006,15007,15020,15021,15026,15027,15164]
def ridgeSupport848_008 : List Nat := [15166,15174,15179,15180,15185]
def ridgeSupport848_code : Nat := 0x3b51ed33b4bed1bb3eecf3ab3eacbaadeab3a9fea7ba8fea3ba89ea23a7be9eb7ebdfab7e9dfa37e7df9b748dd17742dcff737dcd76dcdb5f6d5d2d74b4d2cf4b2d2c74b0cfd33f1cfbb3ebcf8f3e1ceb33a7ce97370cdb736acd9f35fcd77328cc8f321b326cc8b31ecc6b316cc4b2aecaab2a6ca8b29eca6af36bccaf2ebcaaf26bc8af02bbdaeeabb7aebebadad7eb5ead66b58ad2eb4aacbeb2eaca6b28ac6eb1aac62b15ac4ab0fac1eb059eb67ac9eae7aa9ea67a89e867a09e7e79e9e7679c9b226c59b0a6bf9ade6b59a626959a4a68f9a1e68598de63698c6630988e622988261d986a617983e60d981e606980660097ce5f297625d5974a5cf971e5c596a25a5968a59f965e595951e546950654094ce53294c252d94aa527947e51d945e5169446510940e5026c75b1c6c6db1a6c65b186bfdafe6bf5afc6bedafa67f59fc67ed9fa67e59f865b596c65ad96a65a596864f593c64ed93a64e59385265498525d4965255494523548c522d48a52254884db536c4dad36a4da53684c3530c4c2d30a4c253084ab52ac4aad2aa4aa52a84995264498d26249852604815204480d202480520046951a4468d1a246851a018e863918e060c182c60a136c4da136438a0e24388
def ridgeSupport848_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport848_code
def ridgeSupport848_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport848_code
def ridgeSupport848_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport848_code
def ridgeSupport848_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport848_code
def ridgeSupport848_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport848_code
def ridgeSupport848_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport848_code
def ridgeSupport848_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport848_code
def ridgeSupport848_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport848_code
def ridgeSupport848_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport848_code
def ridgeSupport848_rest_009 : Nat := PackedRawNatGrowth.drop 3654 ridgeSupport848_code
def ridgeSupport848_suffix_009 : List Nat := []
def ridgeSupport848_suffix_008 : List Nat := ridgeSupport848_008 ++ ridgeSupport848_suffix_009
def ridgeSupport848_suffix_007 : List Nat := ridgeSupport848_007 ++ ridgeSupport848_suffix_008
def ridgeSupport848_suffix_006 : List Nat := ridgeSupport848_006 ++ ridgeSupport848_suffix_007
def ridgeSupport848_suffix_005 : List Nat := ridgeSupport848_005 ++ ridgeSupport848_suffix_006
def ridgeSupport848_suffix_004 : List Nat := ridgeSupport848_004 ++ ridgeSupport848_suffix_005
def ridgeSupport848_suffix_003 : List Nat := ridgeSupport848_003 ++ ridgeSupport848_suffix_004
def ridgeSupport848_suffix_002 : List Nat := ridgeSupport848_002 ++ ridgeSupport848_suffix_003
def ridgeSupport848_suffix_001 : List Nat := ridgeSupport848_001 ++ ridgeSupport848_suffix_002
def ridgeSupport848_suffix_000 : List Nat := ridgeSupport848_000 ++ ridgeSupport848_suffix_001
theorem ridgeSupport848_source : candidateRows 848 =
    (PackedRawNatGrowth.readList 14 261 ridgeSupport848_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase01
