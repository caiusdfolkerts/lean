module
prelude
public import RootedSevenMixed005
public import RawKindedFacePlacement
public import RootedSevenMixed005OutsideData
public import RawOutsidePlacement

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed005.T6
open ConcreteGrowth
abbrev blockCount : Nat := 19
noncomputable def template : Cell := ⟨4, 63, [3, 5, 6, 10, 17, 24, 36, 40, 48], [7, 27, 46, 53, 56]⟩
noncomputable def root : Cell := FacetUniverses.RootedSevenMixed005.cells 0
noncomputable def records : Table (RawFacePlacement.Block × Nat) :=
(.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (⟨3, 3, 5517840, 5517840, 434925761040, 361742426640⟩, 709650321412400985783665226))
 (.leaf (⟨3, 3, 5517840, 5517840, 434623771680, 361742102880⟩, 716903987012242078719672912)))
 (.branch 3
 (.leaf (⟨3, 3, 5517840, 5517840, 430312027425, 361736204550⟩, 738664983811765357527695970))
 (.leaf (⟨3, 3, 5517840, 5517840, 430043591985, 361736181510⟩, 745918649411606450463703656))))
 (.branch 6
 (.branch 5
 (.leaf (⟨3, 3, 5517840, 5517840, 429775156530, 361736179830⟩, 753172315011447543399711342))
 (.leaf (⟨3, 3, 5517840, 5517840, 361055680050, 361626079350⟩, 760425980611288636335719028)))
 (.branch 7
 (.leaf (⟨3, 3, 5517840, 5517840, 356760712770, 361625649270⟩, 767679646211129729271726714))
 (.branch 8
 (.leaf (⟨3, 3, 5517840, 5517840, 352465745475, 361625618550⟩, 774933311810970822207734400))
 (.leaf (⟨4, 3, 5391120, 5448720, 434488427280, 435025028880⟩, 360134913812871964089706065184674252905434675775462934799962913717210890556885881861390012300233870030475140006486))))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf (⟨4, 3, 4215585, 3481860, 434488427280, 435025028880⟩, 5495222683912211342118418130226083142192193312217792411564700497815074792065914152881099896555301053603905536))
 (.leaf (⟨4, 3, 3232800, 3297600, 434488427280, 435025028880⟩, 5495222683912211342118418130226083142192193312217792411564700497815074792065914152881099896555301053603905536)))
 (.branch 12
 (.leaf (⟨3, 3, 2164035, 2164035, 434925761040, 361742426640⟩, 709650321412400985783665226))
 (.branch 13
 (.leaf (⟨3, 3, 2164035, 2164035, 434623771680, 361742102880⟩, 716903987012242078719672912))
 (.leaf (⟨3, 3, 2164035, 2164035, 430312027425, 361736204550⟩, 738664983811765357527695970)))))
 (.branch 16
 (.branch 15
 (.leaf (⟨3, 3, 2164035, 2164035, 430043591985, 361736181510⟩, 745918649411606450463703656))
 (.leaf (⟨3, 3, 2164035, 2164035, 429775156530, 361736179830⟩, 753172315011447543399711342)))
 (.branch 17
 (.leaf (⟨3, 3, 2164035, 2164035, 361055680050, 361626079350⟩, 760425980611288636335719028))
 (.branch 18
 (.leaf (⟨3, 3, 2164035, 2164035, 356760712770, 361625649270⟩, 767679646211129729271726714))
 (.leaf (⟨3, 3, 2164035, 2164035, 352465745475, 361625618550⟩, 774933311810970822207734400)))))))
noncomputable def raw (i : Fin blockCount) : RawFacePlacement.Block := (records.get i.val).1
noncomputable def witness (i : Fin blockCount) (code : Nat) : Fin 646 :=
  Fin.ofNat 646 (Nat.land (Nat.shiftRight (records.get i.val).2 (16 * code)) 65535)
noncomputable def faceTable : Table Nat :=
(.branch 47131
 (.branch 7212
 (.branch 7206
 (.branch 7189
 (.leaf 0)
 (.leaf 1))
 (.branch 7210
 (.leaf 2)
 (.leaf 3)))
 (.branch 7252
 (.branch 7244
 (.leaf 4)
 (.leaf 5))
 (.branch 7256
 (.leaf 6)
 (.branch 27675
 (.leaf 7)
 (.leaf 8)))))
 (.branch 57386
 (.branch 57351
 (.branch 54299
 (.leaf 9)
 (.leaf 10))
 (.branch 57365
 (.leaf 11)
 (.branch 57382
 (.leaf 12)
 (.leaf 13))))
 (.branch 57420
 (.branch 57388
 (.leaf 14)
 (.leaf 15))
 (.branch 57428
 (.leaf 16)
 (.branch 57432
 (.leaf 17)
 (.leaf 18))))))
noncomputable def faceWitness (s r : Nat) : Fin blockCount :=
  Fin.ofNat blockCount (faceTable.get (s * 1024 + r))
noncomputable def validity (i : Nat) : Bool :=
  RawFaceNormalizers.blockValidCheck 6 (raw (Fin.ofNat blockCount i))
noncomputable def placement (b : Fin blockCount) (code : Nat) : Bool :=
  RawKindedFacePlacement.check 6 (raw b) template root FacetUniverses.RootedSevenMixed005.cells
    code 0 (witness b code)
noncomputable def test (i : Nat) : Bool :=
  let b := Fin.ofNat blockCount i
  FiniteChecks.checkRange (placement b)
    0 (RawFacePlacement.count (raw b).shared (raw b).shared)
noncomputable def symmetry (i : Nat) : Bool :=
  RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed005.Outside.vertexCode root.vertices
    (raw (Fin.ofNat blockCount i))
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed005.T6

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed005.T6
theorem check_0000_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 0)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 0)) 0 6 (by decide +kernel)
theorem block_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 0)) 0 6 :=
  check_0000_0000
theorem check_0001_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 1)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 1)) 0 6 (by decide +kernel)
theorem block_0001 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 1)) 0 6 :=
  check_0001_0000
theorem check_0002_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 2)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 2)) 0 6 (by decide +kernel)
theorem block_0002 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 2)) 0 6 :=
  check_0002_0000
theorem check_0003_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 3)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 3)) 0 6 (by decide +kernel)
theorem block_0003 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 3)) 0 6 :=
  check_0003_0000
theorem check_0004_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 4)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 4)) 0 6 (by decide +kernel)
theorem block_0004 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 4)) 0 6 :=
  check_0004_0000
theorem check_0005_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 5)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 5)) 0 6 (by decide +kernel)
theorem block_0005 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 5)) 0 6 :=
  check_0005_0000
theorem check_0006_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 6)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 6)) 0 6 (by decide +kernel)
theorem block_0006 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 6)) 0 6 :=
  check_0006_0000
theorem check_0007_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 7)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 7)) 0 6 (by decide +kernel)
theorem block_0007 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 7)) 0 6 :=
  check_0007_0000
theorem check_0008_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 8)) 0 8 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 8)) 0 8 (by decide +kernel)
theorem check_0008_0008 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 8)) 8 16 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 8)) 8 8 (by decide +kernel)
theorem check_0008_0016 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 8)) 16 24 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 8)) 16 8 (by decide +kernel)
theorem block_0008 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 8)) 0 24 :=
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 8)) 0 8 24
  check_0008_0000
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 8)) 8 16 24
  check_0008_0008
  check_0008_0016))
theorem check_0009_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 9)) 0 8 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 9)) 0 8 (by decide +kernel)
theorem check_0009_0008 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 9)) 8 16 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 9)) 8 8 (by decide +kernel)
theorem check_0009_0016 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 9)) 16 24 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 9)) 16 8 (by decide +kernel)
theorem block_0009 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 9)) 0 24 :=
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 9)) 0 8 24
  check_0009_0000
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 9)) 8 16 24
  check_0009_0008
  check_0009_0016))
theorem check_0010_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 10)) 0 8 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 10)) 0 8 (by decide +kernel)
theorem check_0010_0008 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 10)) 8 16 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 10)) 8 8 (by decide +kernel)
theorem check_0010_0016 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 10)) 16 24 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 10)) 16 8 (by decide +kernel)
theorem block_0010 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 10)) 0 24 :=
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 10)) 0 8 24
  check_0010_0000
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 10)) 8 16 24
  check_0010_0008
  check_0010_0016))
theorem check_0011_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 11)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 11)) 0 6 (by decide +kernel)
theorem block_0011 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 11)) 0 6 :=
  check_0011_0000
theorem check_0012_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 12)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 12)) 0 6 (by decide +kernel)
theorem block_0012 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 12)) 0 6 :=
  check_0012_0000
theorem check_0013_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 13)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 13)) 0 6 (by decide +kernel)
theorem block_0013 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 13)) 0 6 :=
  check_0013_0000
theorem check_0014_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 14)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 14)) 0 6 (by decide +kernel)
theorem block_0014 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 14)) 0 6 :=
  check_0014_0000
theorem check_0015_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 15)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 15)) 0 6 (by decide +kernel)
theorem block_0015 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 15)) 0 6 :=
  check_0015_0000
theorem check_0016_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 16)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 16)) 0 6 (by decide +kernel)
theorem block_0016 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 16)) 0 6 :=
  check_0016_0000
theorem check_0017_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 17)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 17)) 0 6 (by decide +kernel)
theorem block_0017 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 17)) 0 6 :=
  check_0017_0000
theorem check_0018_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 18)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 18)) 0 6 (by decide +kernel)
theorem block_0018 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 18)) 0 6 :=
  check_0018_0000
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed005.T6

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed005.T6
theorem metadata_validity_0000 : FiniteChecks.Interval validity 0 16 :=
  FiniteChecks.interval_of_check validity 0 16 (by decide +kernel)
theorem metadata_validity_0016 : FiniteChecks.Interval validity 16 19 :=
  FiniteChecks.interval_of_check validity 16 3 (by decide +kernel)
theorem metadata_validity : FiniteChecks.Interval validity 0 blockCount :=
  (FiniteChecks.interval_append (validity) 0 16 19
  metadata_validity_0000
  metadata_validity_0016)
theorem metadata_symmetry_0000 : FiniteChecks.Interval symmetry 0 16 :=
  FiniteChecks.interval_of_check symmetry 0 16 (by decide +kernel)
theorem metadata_symmetry_0016 : FiniteChecks.Interval symmetry 16 19 :=
  FiniteChecks.interval_of_check symmetry 16 3 (by decide +kernel)
theorem metadata_symmetry : FiniteChecks.Interval symmetry 0 blockCount :=
  (FiniteChecks.interval_append (symmetry) 0 16 19
  metadata_symmetry_0000
  metadata_symmetry_0016)
theorem metadata_normalizers :
    RawFaceNormalizers.completeCheck 6 template root raw faceWitness = true := by decide +kernel
theorem metadata_root : RawFacetEmbedding.wellFormedCheck root = true := by decide +kernel
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed005.T6
