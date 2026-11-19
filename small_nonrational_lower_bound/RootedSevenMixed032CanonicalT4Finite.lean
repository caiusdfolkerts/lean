module
prelude
public meta import LowerSchemas.FiniteRootedSevenMixed
public meta import IntegerTables
public import RootedSevenMixed032
public import RawKindedFacePlacement
public import RootedSevenMixed032OutsideData
public import RawOutsidePlacement

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed032.T4
open ConcreteGrowth
abbrev blockCount : Nat := 26
noncomputable def template : Cell := ⟨4, 63, [3, 5, 6, 10, 12, 20, 24, 33, 36, 48], [7, 14, 28, 37, 52, 59]⟩
cert_root_3 032
noncomputable def records : Table (RawFacePlacement.Block × Nat) :=
(.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf (⟨3, 3, 5517840, 5517840, 434925761040, 361742426640⟩, 547651660551185897606414772))
 (.branch 2
 (.leaf (⟨3, 3, 5517840, 5517840, 434875429665, 361742409990⟩, 569412657350709176414437830))
 (.leaf (⟨3, 3, 5517840, 5517840, 430328804640, 361736204640⟩, 591173654150232455222460888))))
 (.branch 4
 (.leaf (⟨3, 3, 5517840, 5517840, 288041236050, 361617784950⟩, 616561483749676280498487789))
 (.branch 5
 (.leaf (⟨3, 3, 5517840, 5517840, 215026792020, 361617201270⟩, 638322480549199559306510847))
 (.leaf (⟨3, 3, 5505825, 5513475, 434925761040, 361742426640⟩, 535562199440010378714743229)))))
 (.branch 9
 (.branch 7
 (.leaf (⟨3, 3, 5505825, 5513475, 434875429665, 361742409990⟩, 557323196239533657522766287))
 (.branch 8
 (.leaf (⟨3, 3, 5505825, 5513475, 430328804640, 361736204640⟩, 579084193039056936330789345))
 (.leaf (⟨3, 3, 5505825, 5513475, 288041236050, 361617784950⟩, 604472022638500761606816246))))
 (.branch 11
 (.branch 10
 (.leaf (⟨3, 3, 5505825, 5513475, 215026792020, 361617201270⟩, 626233019438024040414839304))
 (.leaf (⟨3, 3, 5309490, 5378115, 434925761040, 361742426640⟩, 529517699472241934896857540)))
 (.branch 12
 (.leaf (⟨3, 3, 5309490, 5378115, 434875429665, 361742409990⟩, 551278696271765213704880598))
 (.leaf (⟨3, 3, 5309490, 5378115, 430328804640, 361736204640⟩, 573039693071288492512903656))))))
 (.branch 19
 (.branch 16
 (.branch 14
 (.leaf (⟨3, 3, 5309490, 5378115, 288041236050, 361617784950⟩, 598427522670732317788930557))
 (.branch 15
 (.leaf (⟨3, 3, 5309490, 5378115, 215026792020, 361617201270⟩, 620188519470255596596953615))
 (.leaf (⟨3, 3, 4396320, 2441520, 434925761040, 361742426640⟩, 534353255174214621489070527))))
 (.branch 17
 (.leaf (⟨3, 3, 4396320, 2441520, 434875429665, 361742409990⟩, 556114251973737900297093585))
 (.branch 18
 (.leaf (⟨3, 3, 4396320, 2441520, 430328804640, 361736204640⟩, 577875248773261179105116643))
 (.leaf (⟨3, 3, 4396320, 2441520, 288041236050, 361617784950⟩, 603263078372705004381143544)))))
 (.branch 22
 (.branch 20
 (.leaf (⟨3, 3, 4396320, 2441520, 215026792020, 361617201270⟩, 625024075172228283189166602))
 (.branch 21
 (.leaf (⟨3, 3, 3212610, 2183235, 434925761040, 361742426640⟩, 533144532272162451299631552))
 (.leaf (⟨3, 3, 3212610, 2183235, 434875429665, 361742409990⟩, 554905529071685730107654610))))
 (.branch 24
 (.branch 23
 (.leaf (⟨3, 3, 3212610, 2183235, 430328804640, 361736204640⟩, 576666525871209008915677668))
 (.leaf (⟨3, 3, 3212610, 2183235, 288041236050, 361617784950⟩, 602054355470652834191704569)))
 (.branch 25
 (.leaf (⟨3, 3, 3212610, 2183235, 215026792020, 361617201270⟩, 623815352270176112999727627))
 (.leaf (⟨5, 3, 2442000, 4400400, 423464616720, 508303714320⟩, 710080888955485218676802784702005114385207885646893692352511920017566628350708887319876862261393257178445509838523190139210256986035986810008753118916921945745096974861109313745909858480138450996701345307440294447807093198960054951523338387494222953158472807682918270030490884221839376444409904827334062601264884647594032970001353556484135001091540375597541925881104515985807904193358474104609329746791322958309636941403956861045390159444672275164060365413737420099027042178741937856924938067974815557957202282471362199330202967695541004198568128128794893632069957629153116650)))))))
cert_raw
cert_witness 529
cert_faceTable 51
cert_faceWitness
cert_validity 6
cert_placement 6 032
cert_test_7
cert_symmetry 032
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed032.T4

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed032.T4
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
cert_check 0008 0000 8 0 6 6
cert_block_2 0008 8 6
cert_check 0009 0000 9 0 6 6
cert_block_2 0009 9 6
cert_check 0010 0000 10 0 6 6
cert_block_2 0010 10 6
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
cert_check 0019 0000 19 0 6 6
cert_block_2 0019 19 6
cert_check 0020 0000 20 0 6 6
cert_block_2 0020 20 6
cert_check 0021 0000 21 0 6 6
cert_block_2 0021 21 6
cert_check 0022 0000 22 0 6 6
cert_block_2 0022 22 6
cert_check 0023 0000 23 0 6 6
cert_block_2 0023 23 6
cert_check 0024 0000 24 0 6 6
cert_block_2 0024 24 6
cert_check 0025 0000 25 0 8 8
cert_check 0025 0008 25 8 16 8
cert_check 0025 0016 25 16 24 8
cert_check 0025 0024 25 24 32 8
cert_check 0025 0032 25 32 40 8
cert_check 0025 0040 25 40 48 8
cert_check 0025 0048 25 48 56 8
cert_check 0025 0056 25 56 64 8
cert_check 0025 0064 25 64 72 8
cert_check 0025 0072 25 72 80 8
cert_check 0025 0080 25 80 88 8
cert_check 0025 0088 25 88 96 8
cert_check 0025 0096 25 96 104 8
cert_check 0025 0104 25 104 112 8
cert_check 0025 0112 25 112 120 8
theorem block_0025 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 25)) 0 120 :=
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 25)) 0 56 120
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 25)) 0 24 56
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 25)) 0 8 24
  check_0025_0000
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 25)) 8 16 24
  check_0025_0008
  check_0025_0016))
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 25)) 24 40 56
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 25)) 24 32 40
  check_0025_0024
  check_0025_0032)
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 25)) 40 48 56
  check_0025_0040
  check_0025_0048)))
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 25)) 56 88 120
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 25)) 56 72 88
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 25)) 56 64 72
  check_0025_0056
  check_0025_0064)
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 25)) 72 80 88
  check_0025_0072
  check_0025_0080))
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 25)) 88 104 120
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 25)) 88 96 104
  check_0025_0088
  check_0025_0096)
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 25)) 104 112 120
  check_0025_0104
  check_0025_0112))))
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed032.T4

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed032.T4
cert_metadata_validity_3 0000 0 16 16
cert_metadata_validity_3 0016 16 26 10
cert_metadata_validity_2 26
cert_metadata_symmetry_4 0000 0 16 16
cert_metadata_symmetry_4 0016 16 26 10
cert_metadata_symmetry_5 26
cert_metadata_normalizers 6
cert_metadata_root
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed032.T4
