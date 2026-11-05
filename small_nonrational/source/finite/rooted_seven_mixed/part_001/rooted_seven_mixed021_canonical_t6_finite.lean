module
prelude
public import RootedSevenMixed021
public import RawKindedFacePlacement
public import RootedSevenMixed021OutsideData
public import RawOutsidePlacement

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed021.T6
open ConcreteGrowth
abbrev blockCount : Nat := 18
noncomputable def template : Cell := ⟨4, 63, [3, 5, 6, 10, 17, 24, 36, 40, 48], [7, 27, 46, 53, 56]⟩
noncomputable def root : Cell := FacetUniverses.RootedSevenMixed021.cells 0
noncomputable def records : Table (RawFacePlacement.Block × Nat) :=
(.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (⟨3, 3, 5517840, 5517840, 434925761040, 361742426640⟩, 600845337414784591743549936))
 (.leaf (⟨3, 3, 5517840, 5517840, 434875429665, 361742409990⟩, 608099003014625684679557622)))
 (.branch 3
 (.leaf (⟨3, 3, 5517840, 5517840, 434623771680, 361742102880⟩, 615352668614466777615565308))
 (.leaf (⟨3, 3, 5517840, 5517840, 429775156530, 361736179830⟩, 637113665413990056423588366))))
 (.branch 6
 (.branch 5
 (.leaf (⟨3, 3, 5517840, 5517840, 356760712770, 361625649270⟩, 644367331013831149359596052))
 (.leaf (⟨3, 3, 5517840, 5517840, 288041236050, 361617784950⟩, 651620996613672242295603738)))
 (.branch 7
 (.leaf (⟨4, 3, 5391120, 5448720, 434488427280, 435025028880⟩, 309631854112903274934259657074231990056663112649930793639213238115656160496632752049909583465671717113093758648834))
 (.branch 8
 (.leaf (⟨4, 3, 5391120, 5448720, 141893788995, 434917935495⟩, 4999903554131729098993037984379738945348844602846974112688341376008632391252539565766821456578969409865908224))
 (.leaf (⟨4, 3, 4215585, 3481860, 434488427280, 435025028880⟩, 4724607148939547314175407157546159703728341925628106033832068197978828871514844250307999278575956621223133184))))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf (⟨4, 3, 4215585, 3481860, 141893788995, 434917935495⟩, 327668661148605211972968471728927724286476680609002334910648700435991981424069505391229990053391700473991690977824))
 (.leaf (⟨4, 3, 3232800, 3297600, 434488427280, 435025028880⟩, 4724607148939547314175407157546159703728341925628106033832068197978828871514844250307999278575956621223133184)))
 (.branch 12
 (.leaf (⟨4, 3, 3232800, 3297600, 141893788995, 434917935495⟩, 327668661148605211972968471728927724286476680609002334910648700435991981424069505391229990053391700473991690977824))
 (.leaf (⟨3, 3, 2164035, 2164035, 434925761040, 361742426640⟩, 600845337414784591743549936))))
 (.branch 15
 (.branch 14
 (.leaf (⟨3, 3, 2164035, 2164035, 434875429665, 361742409990⟩, 608099003014625684679557622))
 (.leaf (⟨3, 3, 2164035, 2164035, 434623771680, 361742102880⟩, 615352668614466777615565308)))
 (.branch 16
 (.leaf (⟨3, 3, 2164035, 2164035, 429775156530, 361736179830⟩, 637113665413990056423588366))
 (.branch 17
 (.leaf (⟨3, 3, 2164035, 2164035, 356760712770, 361625649270⟩, 644367331013831149359596052))
 (.leaf (⟨3, 3, 2164035, 2164035, 288041236050, 361617784950⟩, 651620996613672242295603738)))))))
noncomputable def raw (i : Fin blockCount) : RawFacePlacement.Block := (records.get i.val).1
noncomputable def witness (i : Fin blockCount) (code : Nat) : Fin 556 :=
  Fin.ofNat 556 (Nat.land (Nat.shiftRight (records.get i.val).2 (16 * code)) 65535)
noncomputable def faceTable : Table Nat :=
(.branch 47224
 (.branch 7252
 (.branch 7189
 (.branch 7182
 (.leaf 0)
 (.leaf 1))
 (.branch 7212
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
 (.branch 57358
 (.branch 54392
 (.branch 54299
 (.leaf 9)
 (.leaf 10))
 (.branch 57351
 (.leaf 11)
 (.leaf 12)))
 (.branch 57388
 (.branch 57365
 (.leaf 13)
 (.leaf 14))
 (.branch 57428
 (.leaf 15)
 (.branch 57444
 (.leaf 16)
 (.leaf 17))))))
noncomputable def faceWitness (s r : Nat) : Fin blockCount :=
  Fin.ofNat blockCount (faceTable.get (s * 1024 + r))
noncomputable def validity (i : Nat) : Bool :=
  RawFaceNormalizers.blockValidCheck 6 (raw (Fin.ofNat blockCount i))
noncomputable def placement (b : Fin blockCount) (code : Nat) : Bool :=
  RawKindedFacePlacement.check 6 (raw b) template root FacetUniverses.RootedSevenMixed021.cells
    code 0 (witness b code)
noncomputable def test (i : Nat) : Bool :=
  let b := Fin.ofNat blockCount i
  FiniteChecks.checkRange (placement b)
    0 (RawFacePlacement.count (raw b).shared (raw b).shared)
noncomputable def symmetry (i : Nat) : Bool :=
  RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed021.Outside.vertexCode root.vertices
    (raw (Fin.ofNat blockCount i))
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed021.T6

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed021.T6
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
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed021.T6

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed021.T6
theorem metadata_validity_0000 : FiniteChecks.Interval validity 0 16 :=
  FiniteChecks.interval_of_check validity 0 16 (by decide +kernel)
theorem metadata_validity_0016 : FiniteChecks.Interval validity 16 18 :=
  FiniteChecks.interval_of_check validity 16 2 (by decide +kernel)
theorem metadata_validity : FiniteChecks.Interval validity 0 blockCount :=
  (FiniteChecks.interval_append (validity) 0 16 18
  metadata_validity_0000
  metadata_validity_0016)
theorem metadata_symmetry_0000 : FiniteChecks.Interval symmetry 0 16 :=
  FiniteChecks.interval_of_check symmetry 0 16 (by decide +kernel)
theorem metadata_symmetry_0016 : FiniteChecks.Interval symmetry 16 18 :=
  FiniteChecks.interval_of_check symmetry 16 2 (by decide +kernel)
theorem metadata_symmetry : FiniteChecks.Interval symmetry 0 blockCount :=
  (FiniteChecks.interval_append (symmetry) 0 16 18
  metadata_symmetry_0000
  metadata_symmetry_0016)
theorem metadata_normalizers :
    RawFaceNormalizers.completeCheck 6 template root raw faceWitness = true := by decide +kernel
theorem metadata_root : RawFacetEmbedding.wellFormedCheck root = true := by decide +kernel
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed021.T6
