module
prelude
public meta import LowerSchemas.FiniteRootedSevenMixed
public meta import IntegerTables
public import RootedSevenMixed030
public import RawKindedFacePlacement
public import RootedSevenMixed030OutsideData
public import RawOutsidePlacement

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed030.T4
open ConcreteGrowth
abbrev blockCount : Nat := 36
noncomputable def template : Cell := ⟨4, 63, [3, 5, 6, 10, 12, 20, 24, 33, 36, 48], [7, 14, 28, 37, 52, 59]⟩
cert_root_3 030
noncomputable def records : Table (RawFacePlacement.Block × Nat) :=
(.branch 18
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (⟨3, 3, 5517840, 5517840, 434925761040, 361742426640⟩, 656456644548802291646530062))
 (.leaf (⟨3, 3, 5517840, 5517840, 434875429665, 361742409990⟩, 678217641348325570454553120)))
 (.branch 3
 (.leaf (⟨3, 3, 5517840, 5517840, 434070123570, 361742078070⟩, 699978638147848849262576178))
 (.leaf (⟨3, 3, 5517840, 5517840, 430328804640, 361736204640⟩, 721739634947372128070599236))))
 (.branch 6
 (.branch 5
 (.leaf (⟨3, 3, 5517840, 5517840, 356760712770, 361625649270⟩, 747127464546815953346626137))
 (.leaf (⟨3, 3, 5517840, 5517840, 288041236050, 361617784950⟩, 768888461346339232154649195)))
 (.branch 7
 (.leaf (⟨3, 3, 5517840, 5517840, 215026792020, 361617201270⟩, 790649458145862510962672253))
 (.branch 8
 (.leaf (⟨3, 3, 5505825, 5513475, 434925761040, 361742426640⟩, 644367183437626772754858519))
 (.leaf (⟨3, 3, 5505825, 5513475, 434875429665, 361742409990⟩, 666128180237150051562881577))))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf (⟨3, 3, 5505825, 5513475, 434070123570, 361742078070⟩, 687889177036673330370904635))
 (.leaf (⟨3, 3, 5505825, 5513475, 430328804640, 361736204640⟩, 709650173836196609178927693)))
 (.branch 12
 (.leaf (⟨3, 3, 5505825, 5513475, 356760712770, 361625649270⟩, 735038003435640434454954594))
 (.leaf (⟨3, 3, 5505825, 5513475, 288041236050, 361617784950⟩, 756799000235163713262977652))))
 (.branch 15
 (.branch 14
 (.leaf (⟨3, 3, 5505825, 5513475, 215026792020, 361617201270⟩, 778559997034686992071000710))
 (.leaf (⟨3, 3, 5309490, 5378115, 434925761040, 361742426640⟩, 638322683469858328936972830)))
 (.branch 16
 (.leaf (⟨3, 3, 5309490, 5378115, 434875429665, 361742409990⟩, 660083680269381607744995888))
 (.branch 17
 (.leaf (⟨3, 3, 5309490, 5378115, 434070123570, 361742078070⟩, 681844677068904886553018946))
 (.leaf (⟨3, 3, 5309490, 5378115, 430328804640, 361736204640⟩, 703605673868428165361042004)))))))
 (.branch 27
 (.branch 22
 (.branch 20
 (.branch 19
 (.leaf (⟨3, 3, 5309490, 5378115, 356760712770, 361625649270⟩, 728993503467871990637068905))
 (.leaf (⟨3, 3, 5309490, 5378115, 288041236050, 361617784950⟩, 750754500267395269445091963)))
 (.branch 21
 (.leaf (⟨3, 3, 5309490, 5378115, 215026792020, 361617201270⟩, 772515497066918548253115021))
 (.leaf (⟨3, 3, 4396320, 2441520, 434925761040, 361742426640⟩, 643158239171831015529185817))))
 (.branch 24
 (.branch 23
 (.leaf (⟨3, 3, 4396320, 2441520, 434875429665, 361742409990⟩, 664919235971354294337208875))
 (.leaf (⟨3, 3, 4396320, 2441520, 434070123570, 361742078070⟩, 686680232770877573145231933)))
 (.branch 25
 (.leaf (⟨3, 3, 4396320, 2441520, 430328804640, 361736204640⟩, 708441229570400851953254991))
 (.branch 26
 (.leaf (⟨3, 3, 4396320, 2441520, 356760712770, 361625649270⟩, 733829059169844677229281892))
 (.leaf (⟨3, 3, 4396320, 2441520, 288041236050, 361617784950⟩, 755590055969367956037304950))))))
 (.branch 31
 (.branch 29
 (.branch 28
 (.leaf (⟨3, 3, 4396320, 2441520, 215026792020, 361617201270⟩, 777351052768891234845328008))
 (.leaf (⟨3, 3, 3212610, 2183235, 434925761040, 361742426640⟩, 641949516269778845339746842)))
 (.branch 30
 (.leaf (⟨3, 3, 3212610, 2183235, 434875429665, 361742409990⟩, 663710513069302124147769900))
 (.leaf (⟨3, 3, 3212610, 2183235, 434070123570, 361742078070⟩, 685471509868825402955792958))))
 (.branch 33
 (.branch 32
 (.leaf (⟨3, 3, 3212610, 2183235, 430328804640, 361736204640⟩, 707232506668348681763816016))
 (.leaf (⟨3, 3, 3212610, 2183235, 356760712770, 361625649270⟩, 732620336267792507039842917)))
 (.branch 34
 (.leaf (⟨3, 3, 3212610, 2183235, 288041236050, 361617784950⟩, 754381333067315785847865975))
 (.branch 35
 (.leaf (⟨3, 3, 3212610, 2183235, 215026792020, 361617201270⟩, 776142329866839064655889033))
 (.leaf (⟨5, 3, 2442000, 4400400, 423464616720, 508303714320⟩, 866588513459959511772914418881222568168070031871106995973065567694907844395354927790380333943496260801449826292728301435199456484999020637520886459412896578684832634626415040040926725247189374889851845905814889958752330067302271144920319093309276175487279059172214541792313364825836626762769638952542386603176328610737207583797570258729617817658655397157816472810001021550026789199241566356237508548124920671569720185631767761030904725199824531730832854117173422896363614740587099670287985642140693272772259112077295092243798723840680654103558654328610911004036397269864415830))))))))
cert_raw
cert_witness 655
cert_faceTable 71
cert_faceWitness
cert_validity 6
cert_placement 6 030
cert_test_7
cert_symmetry 030
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed030.T4

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed030.T4
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
cert_check 0025 0000 25 0 6 6
cert_block_2 0025 25 6
cert_check 0026 0000 26 0 6 6
cert_block_2 0026 26 6
cert_check 0027 0000 27 0 6 6
cert_block_2 0027 27 6
cert_check 0028 0000 28 0 6 6
cert_block_2 0028 28 6
cert_check 0029 0000 29 0 6 6
cert_block_2 0029 29 6
cert_check 0030 0000 30 0 6 6
cert_block_2 0030 30 6
cert_check 0031 0000 31 0 6 6
cert_block_2 0031 31 6
cert_check 0032 0000 32 0 6 6
cert_block_2 0032 32 6
cert_check 0033 0000 33 0 6 6
cert_block_2 0033 33 6
cert_check 0034 0000 34 0 6 6
cert_block_2 0034 34 6
cert_check 0035 0000 35 0 8 8
cert_check 0035 0008 35 8 16 8
cert_check 0035 0016 35 16 24 8
cert_check 0035 0024 35 24 32 8
cert_check 0035 0032 35 32 40 8
cert_check 0035 0040 35 40 48 8
cert_check 0035 0048 35 48 56 8
cert_check 0035 0056 35 56 64 8
cert_check 0035 0064 35 64 72 8
cert_check 0035 0072 35 72 80 8
cert_check 0035 0080 35 80 88 8
cert_check 0035 0088 35 88 96 8
cert_check 0035 0096 35 96 104 8
cert_check 0035 0104 35 104 112 8
cert_check 0035 0112 35 112 120 8
theorem block_0035 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 35)) 0 120 :=
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 35)) 0 56 120
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 35)) 0 24 56
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 35)) 0 8 24
  check_0035_0000
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 35)) 8 16 24
  check_0035_0008
  check_0035_0016))
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 35)) 24 40 56
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 35)) 24 32 40
  check_0035_0024
  check_0035_0032)
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 35)) 40 48 56
  check_0035_0040
  check_0035_0048)))
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 35)) 56 88 120
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 35)) 56 72 88
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 35)) 56 64 72
  check_0035_0056
  check_0035_0064)
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 35)) 72 80 88
  check_0035_0072
  check_0035_0080))
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 35)) 88 104 120
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 35)) 88 96 104
  check_0035_0088
  check_0035_0096)
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 35)) 104 112 120
  check_0035_0104
  check_0035_0112))))
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed030.T4

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed030.T4
cert_metadata_validity_3 0000 0 16 16
cert_metadata_validity_3 0016 16 32 16
cert_metadata_validity_3 0032 32 36 4
theorem metadata_validity : FiniteChecks.Interval validity 0 blockCount :=
  (FiniteChecks.interval_append (validity) 0 16 36
  metadata_validity_0000
  (FiniteChecks.interval_append (validity) 16 32 36
  metadata_validity_0016
  metadata_validity_0032))
cert_metadata_symmetry_4 0000 0 16 16
cert_metadata_symmetry_4 0016 16 32 16
cert_metadata_symmetry_4 0032 32 36 4
theorem metadata_symmetry : FiniteChecks.Interval symmetry 0 blockCount :=
  (FiniteChecks.interval_append (symmetry) 0 16 36
  metadata_symmetry_0000
  (FiniteChecks.interval_append (symmetry) 16 32 36
  metadata_symmetry_0016
  metadata_symmetry_0032))
cert_metadata_normalizers 6
cert_metadata_root
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed030.T4
