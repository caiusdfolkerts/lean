module
prelude
public import RootedSevenMixed010
public import RawKindedFacePlacement
public import RootedSevenMixed010OutsideData
public import RawOutsidePlacement

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed010.T2
open ConcreteGrowth
abbrev blockCount : Nat := 32
noncomputable def template : Cell := ⟨4, 63, [3, 5, 6, 9, 10, 17, 20, 24, 34, 36, 40, 48], [7, 11, 21, 25, 38, 42, 52, 56]⟩
noncomputable def root : Cell := FacetUniverses.RootedSevenMixed010.cells 0
noncomputable def records : Table (RawFacePlacement.Block × Nat) :=
(.branch 16
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (⟨3, 3, 5517840, 5517840, 434925761040, 361742426640⟩, 496876056694782289472061846))
 (.leaf (⟨3, 3, 5517840, 5517840, 352465745475, 361625618550⟩, 504129722294623382408069532)))
 (.branch 3
 (.leaf (⟨3, 3, 5517840, 5517840, 283746268755, 361617754230⟩, 511383387894464475344077218))
 (.leaf (⟨3, 3, 5517840, 5517840, 215026792020, 361617201270⟩, 518637053494305568280084904))))
 (.branch 6
 (.branch 5
 (.leaf (⟨3, 3, 5514000, 5514000, 434925761040, 361742426640⟩, 496876056694782289472061846))
 (.leaf (⟨3, 3, 5514000, 5514000, 352465745475, 361625618550⟩, 504129722294623382408069532)))
 (.branch 7
 (.leaf (⟨3, 3, 5514000, 5514000, 283746268755, 361617754230⟩, 511383387894464475344077218))
 (.leaf (⟨3, 3, 5514000, 5514000, 215026792020, 361617201270⟩, 518637053494305568280084904)))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf (⟨3, 3, 5444640, 5390640, 434925761040, 361742426640⟩, 496876056694782289472061846))
 (.leaf (⟨3, 3, 5444640, 5390640, 352465745475, 361625618550⟩, 504129722294623382408069532)))
 (.branch 11
 (.leaf (⟨3, 3, 5444640, 5390640, 283746268755, 361617754230⟩, 511383387894464475344077218))
 (.leaf (⟨3, 3, 5444640, 5390640, 215026792020, 361617201270⟩, 518637053494305568280084904))))
 (.branch 14
 (.branch 13
 (.leaf (⟨3, 3, 5379120, 5379120, 434925761040, 361742426640⟩, 496876056694782289472061846))
 (.leaf (⟨3, 3, 5379120, 5379120, 352465745475, 361625618550⟩, 504129722294623382408069532)))
 (.branch 15
 (.leaf (⟨3, 3, 5379120, 5379120, 283746268755, 361617754230⟩, 511383387894464475344077218))
 (.leaf (⟨3, 3, 5379120, 5379120, 215026792020, 361617201270⟩, 518637053494305568280084904))))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf (⟨3, 3, 4392225, 2441475, 434925761040, 361742426640⟩, 496876056694782289472061846))
 (.leaf (⟨3, 3, 4392225, 2441475, 352465745475, 361625618550⟩, 504129722294623382408069532)))
 (.branch 19
 (.leaf (⟨3, 3, 4392225, 2441475, 283746268755, 361617754230⟩, 511383387894464475344077218))
 (.leaf (⟨3, 3, 4392225, 2441475, 215026792020, 361617201270⟩, 518637053494305568280084904))))
 (.branch 22
 (.branch 21
 (.leaf (⟨3, 3, 4326705, 2429955, 434925761040, 361742426640⟩, 496876056694782289472061846))
 (.leaf (⟨3, 3, 4326705, 2429955, 352465745475, 361625618550⟩, 504129722294623382408069532)))
 (.branch 23
 (.leaf (⟨3, 3, 4326705, 2429955, 283746268755, 361617754230⟩, 511383387894464475344077218))
 (.leaf (⟨3, 3, 4326705, 2429955, 215026792020, 361617201270⟩, 518637053494305568280084904)))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf (⟨3, 3, 3212610, 2183235, 434925761040, 361742426640⟩, 496876056694782289472061846))
 (.leaf (⟨3, 3, 3212610, 2183235, 352465745475, 361625618550⟩, 504129722294623382408069532)))
 (.branch 27
 (.leaf (⟨3, 3, 3212610, 2183235, 283746268755, 361617754230⟩, 511383387894464475344077218))
 (.leaf (⟨3, 3, 3212610, 2183235, 215026792020, 361617201270⟩, 518637053494305568280084904))))
 (.branch 30
 (.branch 29
 (.leaf (⟨3, 3, 2164035, 2164035, 434925761040, 361742426640⟩, 496876056694782289472061846))
 (.leaf (⟨3, 3, 2164035, 2164035, 352465745475, 361625618550⟩, 504129722294623382408069532)))
 (.branch 31
 (.leaf (⟨3, 3, 2164035, 2164035, 283746268755, 361617754230⟩, 511383387894464475344077218))
 (.leaf (⟨3, 3, 2164035, 2164035, 215026792020, 361617201270⟩, 518637053494305568280084904)))))))
noncomputable def raw (i : Fin blockCount) : RawFacePlacement.Block := (records.get i.val).1
noncomputable def witness (i : Fin blockCount) (code : Nat) : Fin 430 :=
  Fin.ofNat 430 (Nat.land (Nat.shiftRight (records.get i.val).2 (16 * code)) 65535)
noncomputable def faceTable : Table Nat :=
(.branch 38919
 (.branch 21511
 (.branch 11271
 (.branch 7272
 (.branch 7256
 (.leaf 0)
 (.leaf 1))
 (.branch 7280
 (.leaf 2)
 (.leaf 3)))
 (.branch 11368
 (.branch 11352
 (.leaf 4)
 (.leaf 5))
 (.branch 11376
 (.leaf 6)
 (.leaf 7))))
 (.branch 25607
 (.branch 21608
 (.branch 21592
 (.leaf 8)
 (.leaf 9))
 (.branch 21616
 (.leaf 10)
 (.leaf 11)))
 (.branch 25704
 (.branch 25688
 (.leaf 12)
 (.leaf 13))
 (.branch 25712
 (.leaf 14)
 (.leaf 15)))))
 (.branch 53255
 (.branch 43015
 (.branch 39016
 (.branch 39000
 (.leaf 16)
 (.leaf 17))
 (.branch 39024
 (.leaf 18)
 (.leaf 19)))
 (.branch 43112
 (.branch 43096
 (.leaf 20)
 (.leaf 21))
 (.branch 43120
 (.leaf 22)
 (.leaf 23))))
 (.branch 57351
 (.branch 53352
 (.branch 53336
 (.leaf 24)
 (.leaf 25))
 (.branch 53360
 (.leaf 26)
 (.leaf 27)))
 (.branch 57448
 (.branch 57432
 (.leaf 28)
 (.leaf 29))
 (.branch 57456
 (.leaf 30)
 (.leaf 31))))))
noncomputable def faceWitness (s r : Nat) : Fin blockCount :=
  Fin.ofNat blockCount (faceTable.get (s * 1024 + r))
noncomputable def validity (i : Nat) : Bool :=
  RawFaceNormalizers.blockValidCheck 6 (raw (Fin.ofNat blockCount i))
noncomputable def placement (b : Fin blockCount) (code : Nat) : Bool :=
  RawKindedFacePlacement.check 6 (raw b) template root FacetUniverses.RootedSevenMixed010.cells
    code 0 (witness b code)
noncomputable def test (i : Nat) : Bool :=
  let b := Fin.ofNat blockCount i
  FiniteChecks.checkRange (placement b)
    0 (RawFacePlacement.count (raw b).shared (raw b).shared)
noncomputable def symmetry (i : Nat) : Bool :=
  RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed010.Outside.vertexCode root.vertices
    (raw (Fin.ofNat blockCount i))
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed010.T2

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed010.T2
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
theorem check_0008_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 8)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 8)) 0 6 (by decide +kernel)
theorem block_0008 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 8)) 0 6 :=
  check_0008_0000
theorem check_0009_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 9)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 9)) 0 6 (by decide +kernel)
theorem block_0009 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 9)) 0 6 :=
  check_0009_0000
theorem check_0010_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 10)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 10)) 0 6 (by decide +kernel)
theorem block_0010 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 10)) 0 6 :=
  check_0010_0000
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
theorem check_0019_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 19)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 19)) 0 6 (by decide +kernel)
theorem block_0019 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 19)) 0 6 :=
  check_0019_0000
theorem check_0020_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 20)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 20)) 0 6 (by decide +kernel)
theorem block_0020 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 20)) 0 6 :=
  check_0020_0000
theorem check_0021_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 21)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 21)) 0 6 (by decide +kernel)
theorem block_0021 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 21)) 0 6 :=
  check_0021_0000
theorem check_0022_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 22)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 22)) 0 6 (by decide +kernel)
theorem block_0022 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 22)) 0 6 :=
  check_0022_0000
theorem check_0023_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 23)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 23)) 0 6 (by decide +kernel)
theorem block_0023 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 23)) 0 6 :=
  check_0023_0000
theorem check_0024_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 24)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 24)) 0 6 (by decide +kernel)
theorem block_0024 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 24)) 0 6 :=
  check_0024_0000
theorem check_0025_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 25)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 25)) 0 6 (by decide +kernel)
theorem block_0025 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 25)) 0 6 :=
  check_0025_0000
theorem check_0026_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 26)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 26)) 0 6 (by decide +kernel)
theorem block_0026 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 26)) 0 6 :=
  check_0026_0000
theorem check_0027_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 27)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 27)) 0 6 (by decide +kernel)
theorem block_0027 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 27)) 0 6 :=
  check_0027_0000
theorem check_0028_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 28)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 28)) 0 6 (by decide +kernel)
theorem block_0028 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 28)) 0 6 :=
  check_0028_0000
theorem check_0029_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 29)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 29)) 0 6 (by decide +kernel)
theorem block_0029 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 29)) 0 6 :=
  check_0029_0000
theorem check_0030_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 30)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 30)) 0 6 (by decide +kernel)
theorem block_0030 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 30)) 0 6 :=
  check_0030_0000
theorem check_0031_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 31)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 31)) 0 6 (by decide +kernel)
theorem block_0031 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 31)) 0 6 :=
  check_0031_0000
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed010.T2

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed010.T2
theorem metadata_validity_0000 : FiniteChecks.Interval validity 0 16 :=
  FiniteChecks.interval_of_check validity 0 16 (by decide +kernel)
theorem metadata_validity_0016 : FiniteChecks.Interval validity 16 32 :=
  FiniteChecks.interval_of_check validity 16 16 (by decide +kernel)
theorem metadata_validity : FiniteChecks.Interval validity 0 blockCount :=
  (FiniteChecks.interval_append (validity) 0 16 32
  metadata_validity_0000
  metadata_validity_0016)
theorem metadata_symmetry_0000 : FiniteChecks.Interval symmetry 0 16 :=
  FiniteChecks.interval_of_check symmetry 0 16 (by decide +kernel)
theorem metadata_symmetry_0016 : FiniteChecks.Interval symmetry 16 32 :=
  FiniteChecks.interval_of_check symmetry 16 16 (by decide +kernel)
theorem metadata_symmetry : FiniteChecks.Interval symmetry 0 blockCount :=
  (FiniteChecks.interval_append (symmetry) 0 16 32
  metadata_symmetry_0000
  metadata_symmetry_0016)
theorem metadata_normalizers :
    RawFaceNormalizers.completeCheck 6 template root raw faceWitness = true := by decide +kernel
theorem metadata_root : RawFacetEmbedding.wellFormedCheck root = true := by decide +kernel
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed010.T2
