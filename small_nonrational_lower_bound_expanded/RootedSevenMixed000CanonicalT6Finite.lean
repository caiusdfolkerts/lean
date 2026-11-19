module
prelude
public meta import LowerSchemas.FiniteRootedSevenMixed
public import RootedSevenMixed000
public import RawKindedFacePlacement
public import RootedSevenMixed000OutsideData
public import RawOutsidePlacement

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed000.T6
open ConcreteGrowth
abbrev blockCount : Nat := 19
cert_template
cert_root_3 000
noncomputable def records : Table (RawFacePlacement.Block × Nat) :=
(.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (⟨3, 3, 5517840, 5517840, 434925761040, 361742426640⟩, 709650321412400985783665226))
 (.leaf (⟨3, 3, 5517840, 5517840, 434875429665, 361742409990⟩, 716903987012242078719672912)))
 (.branch 3
 (.leaf (⟨3, 3, 5517840, 5517840, 434623771680, 361742102880⟩, 724157652612083171655680598))
 (.leaf (⟨3, 3, 5517840, 5517840, 429775156530, 361736179830⟩, 745918649411606450463703656))))
 (.branch 6
 (.branch 5
 (.leaf (⟨3, 3, 5517840, 5517840, 421185221955, 361735719030⟩, 753172315011447543399711342))
 (.leaf (⟨3, 3, 5517840, 5517840, 356760712770, 361625649270⟩, 760425980611288636335719028)))
 (.branch 7
 (.leaf (⟨3, 3, 5517840, 5517840, 288041236050, 361617784950⟩, 767679646211129729271726714))
 (.branch 8
 (.leaf (⟨3, 3, 5517840, 5517840, 215026792020, 361617201270⟩, 774933311810970822207734400))
 (.leaf (⟨4, 3, 5391120, 5448720, 434488427280, 435025028880⟩, 363742275220012584743666522906848700251775501713000944882873604831607656989761105419352900074131166667430952960604))))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf (⟨4, 3, 4215585, 3481860, 434488427280, 435025028880⟩, 5550266650695973058400061771131791959225325554117055724259888519231949500676704860207749940696682798773960704))
 (.leaf (⟨4, 3, 3232800, 3297600, 434488427280, 435025028880⟩, 5550266650695973058400061771131791959225325554117055724259888519231949500676704860207749940696682798773960704)))
 (.branch 12
 (.leaf (⟨3, 3, 2164035, 2164035, 434925761040, 361742426640⟩, 709650321412400985783665226))
 (.branch 13
 (.leaf (⟨3, 3, 2164035, 2164035, 434875429665, 361742409990⟩, 716903987012242078719672912))
 (.leaf (⟨3, 3, 2164035, 2164035, 434623771680, 361742102880⟩, 724157652612083171655680598)))))
 (.branch 16
 (.branch 15
 (.leaf (⟨3, 3, 2164035, 2164035, 429775156530, 361736179830⟩, 745918649411606450463703656))
 (.leaf (⟨3, 3, 2164035, 2164035, 421185221955, 361735719030⟩, 753172315011447543399711342)))
 (.branch 17
 (.leaf (⟨3, 3, 2164035, 2164035, 356760712770, 361625649270⟩, 760425980611288636335719028))
 (.branch 18
 (.leaf (⟨3, 3, 2164035, 2164035, 288041236050, 361617784950⟩, 767679646211129729271726714))
 (.leaf (⟨3, 3, 2164035, 2164035, 215026792020, 361617201270⟩, 774933311810970822207734400)))))))
cert_raw
cert_witness 646
noncomputable def faceTable : Table Nat :=
(.branch 47131
 (.branch 7224
 (.branch 7189
 (.branch 7182
 (.leaf 0)
 (.leaf 1))
 (.branch 7212
 (.leaf 2)
 (.leaf 3)))
 (.branch 7268
 (.branch 7252
 (.leaf 4)
 (.leaf 5))
 (.branch 7280
 (.leaf 6)
 (.branch 27675
 (.leaf 7)
 (.leaf 8)))))
 (.branch 57388
 (.branch 57351
 (.branch 54299
 (.leaf 9)
 (.leaf 10))
 (.branch 57358
 (.leaf 11)
 (.branch 57365
 (.leaf 12)
 (.leaf 13))))
 (.branch 57428
 (.branch 57400
 (.leaf 14)
 (.leaf 15))
 (.branch 57444
 (.leaf 16)
 (.branch 57456
 (.leaf 17)
 (.leaf 18))))))
cert_faceWitness
cert_validity 6
cert_placement 6 000
cert_test_7
cert_symmetry 000
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed000.T6

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed000.T6
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
cert_check 0006 0000 6 0 6 6
cert_block_2 0006 6 6
cert_check 0007 0000 7 0 6 6
cert_block_2 0007 7 6
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
cert_check 0011 0000 11 0 6 6
cert_block_2 0011 11 6
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
cert_check 0018 0000 18 0 6 6
cert_block_2 0018 18 6
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed000.T6

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed000.T6
cert_metadata_validity_3 0000 0 16 16
cert_metadata_validity_3 0016 16 19 3
cert_metadata_validity_2 19
cert_metadata_symmetry_4 0000 0 16 16
cert_metadata_symmetry_4 0016 16 19 3
cert_metadata_symmetry_5 19
cert_metadata_normalizers 6
cert_metadata_root
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed000.T6
