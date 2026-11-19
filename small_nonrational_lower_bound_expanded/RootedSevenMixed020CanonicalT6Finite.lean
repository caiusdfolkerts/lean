module
prelude
public meta import LowerSchemas.FiniteRootedSevenMixed
public import RootedSevenMixed020
public import RawKindedFacePlacement
public import RootedSevenMixed020OutsideData
public import RawOutsidePlacement

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed020.T6
open ConcreteGrowth
abbrev blockCount : Nat := 18
cert_template
cert_root_3 020
noncomputable def records : Table (RawFacePlacement.Block × Nat) :=
(.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (⟨3, 3, 5517840, 5517840, 434925761040, 361742426640⟩, 600845337414784591743549936))
 (.leaf (⟨3, 3, 5517840, 5517840, 434623771680, 361742102880⟩, 608099003014625684679557622)))
 (.branch 3
 (.leaf (⟨3, 3, 5517840, 5517840, 430312027425, 361736204550⟩, 629859999814148963487580680))
 (.leaf (⟨3, 3, 5517840, 5517840, 430043591985, 361736181510⟩, 637113665413990056423588366))))
 (.branch 6
 (.branch 5
 (.leaf (⟨3, 3, 5517840, 5517840, 356760712770, 361625649270⟩, 644367331013831149359596052))
 (.leaf (⟨3, 3, 5517840, 5517840, 288041236050, 361617784950⟩, 651620996613672242295603738)))
 (.branch 7
 (.leaf (⟨4, 3, 5391120, 5448720, 434488427280, 435025028880⟩, 306024492705762654280299199352057542710322286712392783556302547001259394063757528491946695691774420476137945694716))
 (.branch 8
 (.leaf (⟨4, 3, 5391120, 5448720, 141893788995, 434917935495⟩, 4999903554131729098993037984379738945348844602846974112688341376008632391252539565766821456578969409865908224))
 (.leaf (⟨4, 3, 4215585, 3481860, 434488427280, 435025028880⟩, 4669563182155785597893763516640450886695209683728842721136880176561954162904053542981349234434574876053078016))))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf (⟨4, 3, 4215585, 3481860, 141893788995, 434917935495⟩, 327668661148605211972968471728927724286476680609002334910648700435991981424069505391229990053391700473991690977824))
 (.leaf (⟨4, 3, 3232800, 3297600, 434488427280, 435025028880⟩, 4669563182155785597893763516640450886695209683728842721136880176561954162904053542981349234434574876053078016)))
 (.branch 12
 (.leaf (⟨4, 3, 3232800, 3297600, 141893788995, 434917935495⟩, 327668661148605211972968471728927724286476680609002334910648700435991981424069505391229990053391700473991690977824))
 (.leaf (⟨3, 3, 2164035, 2164035, 434925761040, 361742426640⟩, 600845337414784591743549936))))
 (.branch 15
 (.branch 14
 (.leaf (⟨3, 3, 2164035, 2164035, 434623771680, 361742102880⟩, 608099003014625684679557622))
 (.leaf (⟨3, 3, 2164035, 2164035, 430312027425, 361736204550⟩, 629859999814148963487580680)))
 (.branch 16
 (.leaf (⟨3, 3, 2164035, 2164035, 430043591985, 361736181510⟩, 637113665413990056423588366))
 (.branch 17
 (.leaf (⟨3, 3, 2164035, 2164035, 356760712770, 361625649270⟩, 644367331013831149359596052))
 (.leaf (⟨3, 3, 2164035, 2164035, 288041236050, 361617784950⟩, 651620996613672242295603738)))))))
cert_raw
cert_witness 556
noncomputable def faceTable : Table Nat :=
(.branch 47224
 (.branch 7252
 (.branch 7206
 (.branch 7189
 (.leaf 0)
 (.leaf 1))
 (.branch 7210
 (.leaf 2)
 (.leaf 3)))
 (.branch 27675
 (.branch 7268
 (.leaf 4)
 (.leaf 5))
 (.branch 27768
 (.leaf 6)
 (.branch 47131
 (.leaf 7)
 (.leaf 8)))))
 (.branch 57365
 (.branch 54392
 (.branch 54299
 (.leaf 9)
 (.leaf 10))
 (.branch 57351
 (.leaf 11)
 (.leaf 12)))
 (.branch 57386
 (.branch 57382
 (.leaf 13)
 (.leaf 14))
 (.branch 57428
 (.leaf 15)
 (.branch 57444
 (.leaf 16)
 (.leaf 17))))))
cert_faceWitness
cert_validity 6
cert_placement 6 020
cert_test_7
cert_symmetry 020
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed020.T6

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed020.T6
cert_check 0000 0000 0 0 6 6
cert_block_2 0000 0 6
cert_check 0001 0000 1 0 6 6
cert_block_2 0001 1 6
cert_check 0002 0000 2 0 6 6
cert_block_2 0002 2 6
cert_check 0003 0000 3 0 6 6
cert_block_2 0003 3 6
cert_check 0004 0000 4 0 6 6
cert_block_2 0004 4 6
cert_check 0005 0000 5 0 6 6
cert_block_2 0005 5 6
cert_check 0006 0000 6 0 8 8
cert_check 0006 0008 6 8 16 8
cert_check 0006 0016 6 16 24 8
cert_block 0006 6
cert_check 0007 0000 7 0 8 8
cert_check 0007 0008 7 8 16 8
cert_check 0007 0016 7 16 24 8
cert_block 0007 7
cert_check 0008 0000 8 0 8 8
cert_check 0008 0008 8 8 16 8
cert_check 0008 0016 8 16 24 8
cert_block 0008 8
cert_check 0009 0000 9 0 8 8
cert_check 0009 0008 9 8 16 8
cert_check 0009 0016 9 16 24 8
cert_block 0009 9
cert_check 0010 0000 10 0 8 8
cert_check 0010 0008 10 8 16 8
cert_check 0010 0016 10 16 24 8
cert_block 0010 10
cert_check 0011 0000 11 0 8 8
cert_check 0011 0008 11 8 16 8
cert_check 0011 0016 11 16 24 8
cert_block 0011 11
cert_check 0012 0000 12 0 6 6
cert_block_2 0012 12 6
cert_check 0013 0000 13 0 6 6
cert_block_2 0013 13 6
cert_check 0014 0000 14 0 6 6
cert_block_2 0014 14 6
cert_check 0015 0000 15 0 6 6
cert_block_2 0015 15 6
cert_check 0016 0000 16 0 6 6
cert_block_2 0016 16 6
cert_check 0017 0000 17 0 6 6
cert_block_2 0017 17 6
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed020.T6

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed020.T6
cert_metadata_validity_3 0000 0 16 16
cert_metadata_validity_3 0016 16 18 2
cert_metadata_validity_2 18
cert_metadata_symmetry_4 0000 0 16 16
cert_metadata_symmetry_4 0016 16 18 2
cert_metadata_symmetry_5 18
cert_metadata_normalizers 6
cert_metadata_root
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed020.T6
