module
prelude
public import RootedSevenMixed009
public import RawKindedFacePlacement
public import RootedSevenMixed009OutsideData
public import RawOutsidePlacement

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed009.T1
open ConcreteGrowth
abbrev blockCount : Nat := 27
noncomputable def template : Cell := ⟨4, 63, [3, 5, 6, 10, 12, 17, 20, 24, 36, 40, 48], [7, 14, 21, 27, 44, 52, 56]⟩
noncomputable def root : Cell := FacetUniverses.RootedSevenMixed009.cells 0
noncomputable def records : Table (RawFacePlacement.Block × Nat) :=
(.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf (⟨3, 3, 5517840, 5517840, 434925761040, 361742426640⟩, 507756555093136532517159318))
 (.branch 2
 (.leaf (⟨3, 3, 5517840, 5517840, 352465745475, 361625618550⟩, 725366523088369320597389898))
 (.leaf (⟨3, 3, 5517840, 5517840, 283746268755, 361617754230⟩, 855932503885508993445528246))))
 (.branch 4
 (.leaf (⟨3, 3, 5517840, 5517840, 215026792020, 361617201270⟩, 986498484682648666293666594))
 (.branch 5
 (.leaf (⟨3, 3, 5505825, 5513475, 434925761040, 361742426640⟩, 548860475686958389097922984))
 (.leaf (⟨3, 3, 5505825, 5513475, 352465745475, 361625618550⟩, 766470443682191177178153564)))))
 (.branch 9
 (.branch 7
 (.leaf (⟨3, 3, 5505825, 5513475, 283746268755, 361617754230⟩, 897036424479330850026291912))
 (.branch 8
 (.leaf (⟨3, 3, 5505825, 5513475, 215026792020, 361617201270⟩, 1027602405276470522874430260))
 (.leaf (⟨3, 3, 5444640, 5390640, 434925761040, 361742426640⟩, 548860475686958389097922984))))
 (.branch 11
 (.branch 10
 (.leaf (⟨3, 3, 5444640, 5390640, 352465745475, 361625618550⟩, 766470443682191177178153564))
 (.leaf (⟨3, 3, 5444640, 5390640, 283746268755, 361617754230⟩, 897036424479330850026291912)))
 (.branch 12
 (.leaf (⟨3, 3, 5444640, 5390640, 215026792020, 361617201270⟩, 1027602405276470522874430260))
 (.leaf (⟨4, 3, 5391120, 5448720, 434488427280, 435025028880⟩, 312637988618853781465958192238129930002064243066716722221792099937253968137149012868645660401925443083711924929026))))))
 (.branch 20
 (.branch 16
 (.branch 14
 (.leaf (⟨4, 3, 5391120, 5448720, 429656593185, 435020112135⟩, 4990728859747536882382778901597123167411397532703504013749165945568669960245334619861944129086774294204776448))
 (.branch 15
 (.leaf (⟨4, 3, 5391120, 5448720, 425630061600, 435019743600⟩, 5210908086499697014203733543712323376535980542822221209982877925559109828277903954539317058561284017721835520))
 (.leaf (⟨3, 3, 4261170, 2428995, 434925761040, 361742426640⟩, 592382469286004946713969100))))
 (.branch 18
 (.branch 17
 (.leaf (⟨3, 3, 4261170, 2428995, 352465745475, 361625618550⟩, 809992437281237734794199680))
 (.leaf (⟨3, 3, 4261170, 2428995, 283746268755, 361617754230⟩, 940558418078377407642338028)))
 (.branch 19
 (.leaf (⟨3, 3, 4261170, 2428995, 215026792020, 361617201270⟩, 1071124398875517080490476376))
 (.leaf (⟨3, 3, 3212610, 2183235, 434925761040, 361742426640⟩, 594800357819285311025971662)))))
 (.branch 23
 (.branch 21
 (.leaf (⟨3, 3, 3212610, 2183235, 352465745475, 361625618550⟩, 812410325814518099106202242))
 (.branch 22
 (.leaf (⟨3, 3, 3212610, 2183235, 283746268755, 361617754230⟩, 942976306611657771954340590))
 (.leaf (⟨3, 3, 3212610, 2183235, 215026792020, 361617201270⟩, 1073542287408797444802478938))))
 (.branch 25
 (.branch 24
 (.leaf (⟨3, 3, 2164035, 2164035, 434925761040, 361742426640⟩, 616561539090752926557274608))
 (.leaf (⟨3, 3, 2164035, 2164035, 352465745475, 361625618550⟩, 834171507085985714637505188)))
 (.branch 26
 (.leaf (⟨3, 3, 2164035, 2164035, 283746268755, 361617754230⟩, 964737487883125387485643536))
 (.leaf (⟨3, 3, 2164035, 2164035, 215026792020, 361617201270⟩, 1095303468680265060333781884)))))))
noncomputable def raw (i : Fin blockCount) : RawFacePlacement.Block := (records.get i.val).1
noncomputable def witness (i : Fin blockCount) (code : Nat) : Fin 910 :=
  Fin.ofNat 910 (Nat.land (Nat.shiftRight (records.get i.val).2 (16 * code)) 65535)
noncomputable def faceTable : Table Nat :=
(.branch 27694
 (.branch 14440
 (.branch 7280
 (.branch 7256
 (.leaf 0)
 (.branch 7272
 (.leaf 1)
 (.leaf 2)))
 (.branch 14343
 (.leaf 3)
 (.branch 14424
 (.leaf 4)
 (.leaf 5))))
 (.branch 21592
 (.branch 14448
 (.leaf 6)
 (.branch 21511
 (.leaf 7)
 (.leaf 8)))
 (.branch 21616
 (.branch 21608
 (.leaf 9)
 (.leaf 10))
 (.branch 27675
 (.leaf 11)
 (.leaf 12)))))
 (.branch 53336
 (.branch 45144
 (.branch 27701
 (.leaf 13)
 (.branch 45063
 (.leaf 14)
 (.leaf 15)))
 (.branch 45168
 (.branch 45160
 (.leaf 16)
 (.leaf 17))
 (.branch 53255
 (.leaf 18)
 (.leaf 19))))
 (.branch 57351
 (.branch 53352
 (.leaf 20)
 (.branch 53360
 (.leaf 21)
 (.leaf 22)))
 (.branch 57448
 (.branch 57432
 (.leaf 23)
 (.leaf 24))
 (.branch 57456
 (.leaf 25)
 (.leaf 26))))))
noncomputable def faceWitness (s r : Nat) : Fin blockCount :=
  Fin.ofNat blockCount (faceTable.get (s * 1024 + r))
noncomputable def validity (i : Nat) : Bool :=
  RawFaceNormalizers.blockValidCheck 6 (raw (Fin.ofNat blockCount i))
noncomputable def placement (b : Fin blockCount) (code : Nat) : Bool :=
  RawKindedFacePlacement.check 6 (raw b) template root FacetUniverses.RootedSevenMixed009.cells
    code 0 (witness b code)
noncomputable def test (i : Nat) : Bool :=
  let b := Fin.ofNat blockCount i
  FiniteChecks.checkRange (placement b)
    0 (RawFacePlacement.count (raw b).shared (raw b).shared)
noncomputable def symmetry (i : Nat) : Bool :=
  RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed009.Outside.vertexCode root.vertices
    (raw (Fin.ofNat blockCount i))
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed009.T1

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed009.T1
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
theorem check_0013_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 13)) 0 8 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 13)) 0 8 (by decide +kernel)
theorem check_0013_0008 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 13)) 8 16 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 13)) 8 8 (by decide +kernel)
theorem check_0013_0016 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 13)) 16 24 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 13)) 16 8 (by decide +kernel)
theorem block_0013 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 13)) 0 24 :=
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 13)) 0 8 24
  check_0013_0000
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 13)) 8 16 24
  check_0013_0008
  check_0013_0016))
theorem check_0014_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 14)) 0 8 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 14)) 0 8 (by decide +kernel)
theorem check_0014_0008 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 14)) 8 16 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 14)) 8 8 (by decide +kernel)
theorem check_0014_0016 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 14)) 16 24 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 14)) 16 8 (by decide +kernel)
theorem block_0014 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 14)) 0 24 :=
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 14)) 0 8 24
  check_0014_0000
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount 14)) 8 16 24
  check_0014_0008
  check_0014_0016))
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
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed009.T1

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed009.T1
theorem metadata_validity_0000 : FiniteChecks.Interval validity 0 16 :=
  FiniteChecks.interval_of_check validity 0 16 (by decide +kernel)
theorem metadata_validity_0016 : FiniteChecks.Interval validity 16 27 :=
  FiniteChecks.interval_of_check validity 16 11 (by decide +kernel)
theorem metadata_validity : FiniteChecks.Interval validity 0 blockCount :=
  (FiniteChecks.interval_append (validity) 0 16 27
  metadata_validity_0000
  metadata_validity_0016)
theorem metadata_symmetry_0000 : FiniteChecks.Interval symmetry 0 16 :=
  FiniteChecks.interval_of_check symmetry 0 16 (by decide +kernel)
theorem metadata_symmetry_0016 : FiniteChecks.Interval symmetry 16 27 :=
  FiniteChecks.interval_of_check symmetry 16 11 (by decide +kernel)
theorem metadata_symmetry : FiniteChecks.Interval symmetry 0 blockCount :=
  (FiniteChecks.interval_append (symmetry) 0 16 27
  metadata_symmetry_0000
  metadata_symmetry_0016)
theorem metadata_normalizers :
    RawFaceNormalizers.completeCheck 6 template root raw faceWitness = true := by decide +kernel
theorem metadata_root : RawFacetEmbedding.wellFormedCheck root = true := by decide +kernel
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed009.T1
