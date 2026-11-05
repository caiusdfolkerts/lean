module
prelude
public import RootedSevenMixed028
public import RawKindedFacePlacement
public import RootedSevenMixed028OutsideData
public import RawOutsidePlacement

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed028.T6
open ConcreteGrowth
abbrev blockCount : Nat := 17
noncomputable def template : Cell := ⟨4, 63, [3, 5, 6, 10, 17, 24, 36, 40, 48], [7, 27, 46, 53, 56]⟩
noncomputable def root : Cell := FacetUniverses.RootedSevenMixed028.cells 0
noncomputable def records : Table (RawFacePlacement.Block × Nat) :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (⟨3, 3, 5517840, 5517840, 434925761040, 361742426640⟩, 492040353417168197703434646))
 (.leaf (⟨3, 3, 5517840, 5517840, 434623771680, 361742102880⟩, 499294019017009290639442332)))
 (.branch 3
 (.leaf (⟨3, 3, 5517840, 5517840, 352465745475, 361625618550⟩, 535562347016214755319480762))
 (.leaf (⟨3, 3, 5517840, 5517840, 283746268755, 361617754230⟩, 542816012616055848255488448))))
 (.branch 6
 (.branch 5
 (.leaf (⟨4, 3, 5391120, 5448720, 434488427280, 435025028880⟩, 251914071598653344470892333519440832515209897649322632312642180285307897570629175122503379083314970921800751382946))
 (.leaf (⟨4, 3, 5391120, 5448720, 429656593185, 435020112135⟩, 3954052227058968472843503434332537952007075304783067430578209471054043018097835226049300041575048223159877632)))
 (.branch 7
 (.leaf (⟨4, 3, 5391120, 5448720, 210613265730, 434917970055⟩, 4174231453811128604664458076447738161131658314901784626811921451044482886130404560726672971049557946676936704))
 (.leaf (⟨4, 3, 4215585, 3481860, 434488427280, 435025028880⟩, 3843903680399359853669108903054818631198226055239893030709059855308833533742192933081598572313848698502250496)))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf (⟨4, 3, 4215585, 3481860, 429656593185, 435020112135⟩, 259128794412933663046526316371393609858191113092522405103112651241894460031348105947278328848324189642321299505582))
 (.leaf (⟨4, 3, 4215585, 3481860, 210613265730, 434917970055⟩, 273558240041496094399461506972979739211514390464412916641541293177493938219289453198636573312548928764778224026054)))
 (.branch 11
 (.leaf (⟨4, 3, 3232800, 3297600, 434488427280, 435025028880⟩, 3843903680399359853669108903054818631198226055239893030709059855308833533742192933081598572313848698502250496))
 (.leaf (⟨4, 3, 3232800, 3297600, 429656593185, 435020112135⟩, 259128794412933663046526316371393609858191113092522405103112651241894460031348105947278328848324189642321299505582))))
 (.branch 14
 (.branch 13
 (.leaf (⟨4, 3, 3232800, 3297600, 210613265730, 434917970055⟩, 273558240041496094399461506972979739211514390464412916641541293177493938219289453198636573312548928764778224026054))
 (.leaf (⟨3, 3, 2164035, 2164035, 434925761040, 361742426640⟩, 492040353417168197703434646)))
 (.branch 15
 (.leaf (⟨3, 3, 2164035, 2164035, 434623771680, 361742102880⟩, 499294019017009290639442332))
 (.branch 16
 (.leaf (⟨3, 3, 2164035, 2164035, 352465745475, 361625618550⟩, 535562347016214755319480762))
 (.leaf (⟨3, 3, 2164035, 2164035, 283746268755, 361617754230⟩, 542816012616055848255488448)))))))
noncomputable def raw (i : Fin blockCount) : RawFacePlacement.Block := (records.get i.val).1
noncomputable def witness (i : Fin blockCount) (code : Nat) : Fin 466 :=
  Fin.ofNat 466 (Nat.land (Nat.shiftRight (records.get i.val).2 (16 * code)) 65535)
noncomputable def faceTable : Table Nat :=
(.branch 47150
 (.branch 27675
 (.branch 7256
 (.branch 7189
 (.leaf 0)
 (.leaf 1))
 (.branch 7272
 (.leaf 2)
 (.leaf 3)))
 (.branch 27764
 (.branch 27694
 (.leaf 4)
 (.leaf 5))
 (.branch 47131
 (.leaf 6)
 (.leaf 7))))
 (.branch 54388
 (.branch 54299
 (.branch 47220
 (.leaf 8)
 (.leaf 9))
 (.branch 54318
 (.leaf 10)
 (.leaf 11)))
 (.branch 57365
 (.branch 57351
 (.leaf 12)
 (.leaf 13))
 (.branch 57432
 (.leaf 14)
 (.branch 57448
 (.leaf 15)
 (.leaf 16))))))
noncomputable def faceWitness (s r : Nat) : Fin blockCount :=
  Fin.ofNat blockCount (faceTable.get (s * 1024 + r))
noncomputable def validity (i : Nat) : Bool :=
  RawFaceNormalizers.blockValidCheck 6 (raw (Fin.ofNat blockCount i))
noncomputable def placement (b : Fin blockCount) (code : Nat) : Bool :=
  RawKindedFacePlacement.check 6 (raw b) template root FacetUniverses.RootedSevenMixed028.cells
    code 0 (witness b code)
noncomputable def test (i : Nat) : Bool :=
  let b := Fin.ofNat blockCount i
  FiniteChecks.checkRange (placement b)
    0 (RawFacePlacement.count (raw b).shared (raw b).shared)
noncomputable def symmetry (i : Nat) : Bool :=
  RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed028.Outside.vertexCode root.vertices
    (raw (Fin.ofNat blockCount i))
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed028.T6

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed028.T6
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
theorem check_0004_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 4)) 0 8 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 4)) 0 8 (by decide +kernel)
theorem check_0004_0008 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 4)) 8 16 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 4)) 8 8 (by decide +kernel)
theorem check_0004_0016 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 4)) 16 24 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 4)) 16 8 (by decide +kernel)
theorem block_0004 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 4)) 0 24 :=
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 4)) 0 8 24
  check_0004_0000
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 4)) 8 16 24
  check_0004_0008
  check_0004_0016))
theorem check_0005_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 5)) 0 8 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 5)) 0 8 (by decide +kernel)
theorem check_0005_0008 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 5)) 8 16 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 5)) 8 8 (by decide +kernel)
theorem check_0005_0016 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 5)) 16 24 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 5)) 16 8 (by decide +kernel)
theorem block_0005 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 5)) 0 24 :=
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 5)) 0 8 24
  check_0005_0000
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 5)) 8 16 24
  check_0005_0008
  check_0005_0016))
theorem check_0006_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 6)) 0 8 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 6)) 0 8 (by decide +kernel)
theorem check_0006_0008 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 6)) 8 16 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 6)) 8 8 (by decide +kernel)
theorem check_0006_0016 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 6)) 16 24 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 6)) 16 8 (by decide +kernel)
theorem block_0006 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 6)) 0 24 :=
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 6)) 0 8 24
  check_0006_0000
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 6)) 8 16 24
  check_0006_0008
  check_0006_0016))
theorem check_0007_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 7)) 0 8 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 7)) 0 8 (by decide +kernel)
theorem check_0007_0008 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 7)) 8 16 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 7)) 8 8 (by decide +kernel)
theorem check_0007_0016 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 7)) 16 24 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 7)) 16 8 (by decide +kernel)
theorem block_0007 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 7)) 0 24 :=
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 7)) 0 8 24
  check_0007_0000
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 7)) 8 16 24
  check_0007_0008
  check_0007_0016))
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
theorem check_0011_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 11)) 0 8 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 11)) 0 8 (by decide +kernel)
theorem check_0011_0008 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 11)) 8 16 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 11)) 8 8 (by decide +kernel)
theorem check_0011_0016 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 11)) 16 24 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 11)) 16 8 (by decide +kernel)
theorem block_0011 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 11)) 0 24 :=
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 11)) 0 8 24
  check_0011_0000
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 11)) 8 16 24
  check_0011_0008
  check_0011_0016))
theorem check_0012_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 12)) 0 8 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 12)) 0 8 (by decide +kernel)
theorem check_0012_0008 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 12)) 8 16 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 12)) 8 8 (by decide +kernel)
theorem check_0012_0016 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 12)) 16 24 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 12)) 16 8 (by decide +kernel)
theorem block_0012 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 12)) 0 24 :=
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 12)) 0 8 24
  check_0012_0000
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 12)) 8 16 24
  check_0012_0008
  check_0012_0016))
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
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed028.T6

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed028.T6
theorem metadata_validity_0000 : FiniteChecks.Interval validity 0 16 :=
  FiniteChecks.interval_of_check validity 0 16 (by decide +kernel)
theorem metadata_validity_0016 : FiniteChecks.Interval validity 16 17 :=
  FiniteChecks.interval_of_check validity 16 1 (by decide +kernel)
theorem metadata_validity : FiniteChecks.Interval validity 0 blockCount :=
  (FiniteChecks.interval_append (validity) 0 16 17
  metadata_validity_0000
  metadata_validity_0016)
theorem metadata_symmetry_0000 : FiniteChecks.Interval symmetry 0 16 :=
  FiniteChecks.interval_of_check symmetry 0 16 (by decide +kernel)
theorem metadata_symmetry_0016 : FiniteChecks.Interval symmetry 16 17 :=
  FiniteChecks.interval_of_check symmetry 16 1 (by decide +kernel)
theorem metadata_symmetry : FiniteChecks.Interval symmetry 0 blockCount :=
  (FiniteChecks.interval_append (symmetry) 0 16 17
  metadata_symmetry_0000
  metadata_symmetry_0016)
theorem metadata_normalizers :
    RawFaceNormalizers.completeCheck 6 template root raw faceWitness = true := by decide +kernel
theorem metadata_root : RawFacetEmbedding.wellFormedCheck root = true := by decide +kernel
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed028.T6
