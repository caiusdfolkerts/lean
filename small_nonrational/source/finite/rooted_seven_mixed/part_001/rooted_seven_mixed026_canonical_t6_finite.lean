module
prelude
public import RootedSevenMixed026
public import RawKindedFacePlacement
public import RootedSevenMixed026OutsideData
public import RawOutsidePlacement

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed026.T6
open ConcreteGrowth
abbrev blockCount : Nat := 18
noncomputable def template : Cell := ⟨4, 63, [3, 5, 6, 10, 17, 24, 36, 40, 48], [7, 27, 46, 53, 56]⟩
noncomputable def root : Cell := FacetUniverses.RootedSevenMixed026.cells 0
noncomputable def records : Table (RawFacePlacement.Block × Nat) :=
(.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (⟨3, 3, 5517840, 5517840, 434925761040, 361742426640⟩, 600845337414784591743549936))
 (.leaf (⟨3, 3, 5517840, 5517840, 434623771680, 361742102880⟩, 608099003014625684679557622)))
 (.branch 3
 (.leaf (⟨3, 3, 5517840, 5517840, 425480189250, 361735749750⟩, 629859999814148963487580680))
 (.leaf (⟨3, 3, 5517840, 5517840, 421185221955, 361735719030⟩, 637113665413990056423588366))))
 (.branch 6
 (.branch 5
 (.leaf (⟨3, 3, 5517840, 5517840, 361324115505, 361626081030⟩, 644367331013831149359596052))
 (.leaf (⟨3, 3, 5517840, 5517840, 283746268755, 361617754230⟩, 666128327813354428167619110)))
 (.branch 7
 (.leaf (⟨4, 3, 5391120, 5448720, 434488427280, 435025028880⟩, 306024492705762654280299199352057542710322286712392783556302547001259394063757528491946695691774420476137945694716))
 (.branch 8
 (.leaf (⟨4, 3, 5391120, 5448720, 287922677025, 434918490375⟩, 324061299741465757550101487962929779442026416400082833970856002573243226228133646281761134561260903660917010465306))
 (.leaf (⟨4, 3, 4215585, 3481860, 434488427280, 435025028880⟩, 4669563182155785597893763516640450886695209683728842721136880176561954162904053542981349234434574876053078016))))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf (⟨4, 3, 4215585, 3481860, 287922677025, 434918490375⟩, 4944783016074594179301981721168994971860870893225159284612820283646327705958007079614599455141483601903353856))
 (.leaf (⟨4, 3, 3232800, 3297600, 434488427280, 435025028880⟩, 4669563182155785597893763516640450886695209683728842721136880176561954162904053542981349234434574876053078016)))
 (.branch 12
 (.leaf (⟨4, 3, 3232800, 3297600, 287922677025, 434918490375⟩, 4944783016074594179301981721168994971860870893225159284612820283646327705958007079614599455141483601903353856))
 (.leaf (⟨3, 3, 2164035, 2164035, 434925761040, 361742426640⟩, 600845337414784591743549936))))
 (.branch 15
 (.branch 14
 (.leaf (⟨3, 3, 2164035, 2164035, 434623771680, 361742102880⟩, 608099003014625684679557622))
 (.leaf (⟨3, 3, 2164035, 2164035, 425480189250, 361735749750⟩, 629859999814148963487580680)))
 (.branch 16
 (.leaf (⟨3, 3, 2164035, 2164035, 421185221955, 361735719030⟩, 637113665413990056423588366))
 (.branch 17
 (.leaf (⟨3, 3, 2164035, 2164035, 361324115505, 361626081030⟩, 644367331013831149359596052))
 (.leaf (⟨3, 3, 2164035, 2164035, 283746268755, 361617754230⟩, 666128327813354428167619110)))))))
noncomputable def raw (i : Fin blockCount) : RawFacePlacement.Block := (records.get i.val).1
noncomputable def witness (i : Fin blockCount) (code : Nat) : Fin 556 :=
  Fin.ofNat 556 (Nat.land (Nat.shiftRight (records.get i.val).2 (16 * code)) 65535)
noncomputable def faceTable : Table Nat :=
(.branch 47206
 (.branch 7242
 (.branch 7220
 (.branch 7189
 (.leaf 0)
 (.leaf 1))
 (.branch 7224
 (.leaf 2)
 (.leaf 3)))
 (.branch 27675
 (.branch 7272
 (.leaf 4)
 (.leaf 5))
 (.branch 27750
 (.leaf 6)
 (.branch 47131
 (.leaf 7)
 (.leaf 8)))))
 (.branch 57365
 (.branch 54374
 (.branch 54299
 (.leaf 9)
 (.leaf 10))
 (.branch 57351
 (.leaf 11)
 (.leaf 12)))
 (.branch 57400
 (.branch 57396
 (.leaf 13)
 (.leaf 14))
 (.branch 57418
 (.leaf 15)
 (.branch 57448
 (.leaf 16)
 (.leaf 17))))))
noncomputable def faceWitness (s r : Nat) : Fin blockCount :=
  Fin.ofNat blockCount (faceTable.get (s * 1024 + r))
noncomputable def validity (i : Nat) : Bool :=
  RawFaceNormalizers.blockValidCheck 6 (raw (Fin.ofNat blockCount i))
noncomputable def placement (b : Fin blockCount) (code : Nat) : Bool :=
  RawKindedFacePlacement.check 6 (raw b) template root FacetUniverses.RootedSevenMixed026.cells
    code 0 (witness b code)
noncomputable def test (i : Nat) : Bool :=
  let b := Fin.ofNat blockCount i
  FiniteChecks.checkRange (placement b)
    0 (RawFacePlacement.count (raw b).shared (raw b).shared)
noncomputable def symmetry (i : Nat) : Bool :=
  RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed026.Outside.vertexCode root.vertices
    (raw (Fin.ofNat blockCount i))
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed026.T6

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed026.T6
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
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed026.T6

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed026.T6
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
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed026.T6
