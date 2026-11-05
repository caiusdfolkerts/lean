module
prelude
public import RootedSevenMixed033
public import RawKindedFacePlacement
public import RootedSevenMixed033OutsideData
public import RawOutsidePlacement

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed033.T4
open ConcreteGrowth
abbrev blockCount : Nat := 26
noncomputable def template : Cell := ⟨4, 63, [3, 5, 6, 10, 12, 20, 24, 33, 36, 48], [7, 14, 28, 37, 52, 59]⟩
noncomputable def root : Cell := FacetUniverses.RootedSevenMixed033.cells 0
noncomputable def records : Table (RawFacePlacement.Block × Nat) :=
(.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf (⟨3, 3, 5517840, 5517840, 434925761040, 361742426640⟩, 547651660551185897606414772))
 (.branch 2
 (.leaf (⟨3, 3, 5517840, 5517840, 430328804640, 361736204640⟩, 569412657350709176414437830))
 (.leaf (⟨3, 3, 5517840, 5517840, 352465745475, 361625618550⟩, 594800486950153001690464731))))
 (.branch 4
 (.leaf (⟨3, 3, 5517840, 5517840, 288041236050, 361617784950⟩, 616561483749676280498487789))
 (.branch 5
 (.leaf (⟨3, 3, 5517840, 5517840, 215026792020, 361617201270⟩, 638322480549199559306510847))
 (.leaf (⟨3, 3, 5505825, 5513475, 434925761040, 361742426640⟩, 535562199440010378714743229)))))
 (.branch 9
 (.branch 7
 (.leaf (⟨3, 3, 5505825, 5513475, 430328804640, 361736204640⟩, 557323196239533657522766287))
 (.branch 8
 (.leaf (⟨3, 3, 5505825, 5513475, 352465745475, 361625618550⟩, 582711025838977482798793188))
 (.leaf (⟨3, 3, 5505825, 5513475, 288041236050, 361617784950⟩, 604472022638500761606816246))))
 (.branch 11
 (.branch 10
 (.leaf (⟨3, 3, 5505825, 5513475, 215026792020, 361617201270⟩, 626233019438024040414839304))
 (.leaf (⟨3, 3, 5309490, 5378115, 434925761040, 361742426640⟩, 529517699472241934896857540)))
 (.branch 12
 (.leaf (⟨3, 3, 5309490, 5378115, 430328804640, 361736204640⟩, 551278696271765213704880598))
 (.leaf (⟨3, 3, 5309490, 5378115, 352465745475, 361625618550⟩, 576666525871209038980907499))))))
 (.branch 19
 (.branch 16
 (.branch 14
 (.leaf (⟨3, 3, 5309490, 5378115, 288041236050, 361617784950⟩, 598427522670732317788930557))
 (.branch 15
 (.leaf (⟨3, 3, 5309490, 5378115, 215026792020, 361617201270⟩, 620188519470255596596953615))
 (.leaf (⟨3, 3, 4396320, 2441520, 434925761040, 361742426640⟩, 534353255174214621489070527))))
 (.branch 17
 (.leaf (⟨3, 3, 4396320, 2441520, 430328804640, 361736204640⟩, 556114251973737900297093585))
 (.branch 18
 (.leaf (⟨3, 3, 4396320, 2441520, 352465745475, 361625618550⟩, 581502081573181725573120486))
 (.leaf (⟨3, 3, 4396320, 2441520, 288041236050, 361617784950⟩, 603263078372705004381143544)))))
 (.branch 22
 (.branch 20
 (.leaf (⟨3, 3, 4396320, 2441520, 215026792020, 361617201270⟩, 625024075172228283189166602))
 (.branch 21
 (.leaf (⟨3, 3, 3212610, 2183235, 434925761040, 361742426640⟩, 533144532272162451299631552))
 (.leaf (⟨3, 3, 3212610, 2183235, 430328804640, 361736204640⟩, 554905529071685730107654610))))
 (.branch 24
 (.branch 23
 (.leaf (⟨3, 3, 3212610, 2183235, 352465745475, 361625618550⟩, 580293358671129555383681511))
 (.leaf (⟨3, 3, 3212610, 2183235, 288041236050, 361617784950⟩, 602054355470652834191704569)))
 (.branch 25
 (.leaf (⟨3, 3, 3212610, 2183235, 215026792020, 361617201270⟩, 623815352270176112999727627))
 (.leaf (⟨5, 3, 2442000, 4400400, 423464616720, 508303714320⟩, 683996284871406169827450845672135538754730861276191475082419645404676425676601213908126283647709423241278123762822338256545390402875481172090064228834259506921807698233558359363407047352296630347842928541044528529316220387569685585957174936525047416103671765768035558070187137454506501391349949139799341934279643987070170534368650772776554531663687872004162834726288431725104756692377958729337966613235723339432956400699321711047804398485480232402931617296498086299470946751767744221364430138947169272154692810870373383844603675004684395881069707095492224070075551022367900120)))))))
noncomputable def raw (i : Fin blockCount) : RawFacePlacement.Block := (records.get i.val).1
noncomputable def witness (i : Fin blockCount) (code : Nat) : Fin 529 :=
  Fin.ofNat 529 (Nat.land (Nat.shiftRight (records.get i.val).2 (16 * code)) 65535)
noncomputable def faceTable : Table Nat :=
(.branch 28772
 (.branch 14373
 (.branch 7268
 (.branch 7205
 (.leaf 0)
 (.branch 7256
 (.leaf 1)
 (.leaf 2)))
 (.branch 7280
 (.leaf 3)
 (.branch 14343
 (.leaf 4)
 (.leaf 5))))
 (.branch 14448
 (.branch 14424
 (.leaf 6)
 (.branch 14436
 (.leaf 7)
 (.leaf 8)))
 (.branch 28709
 (.branch 28679
 (.leaf 9)
 (.leaf 10))
 (.branch 28760
 (.leaf 11)
 (.leaf 12)))))
 (.branch 38000
 (.branch 37925
 (.branch 28784
 (.leaf 13)
 (.branch 37895
 (.leaf 14)
 (.leaf 15)))
 (.branch 37976
 (.leaf 16)
 (.branch 37988
 (.leaf 17)
 (.leaf 18))))
 (.branch 53336
 (.branch 53255
 (.leaf 19)
 (.branch 53285
 (.leaf 20)
 (.leaf 21)))
 (.branch 53360
 (.branch 53348
 (.leaf 22)
 (.leaf 23))
 (.branch 60475
 (.leaf 24)
 (.leaf 25))))))
noncomputable def faceWitness (s r : Nat) : Fin blockCount :=
  Fin.ofNat blockCount (faceTable.get (s * 1024 + r))
noncomputable def validity (i : Nat) : Bool :=
  RawFaceNormalizers.blockValidCheck 6 (raw (Fin.ofNat blockCount i))
noncomputable def placement (b : Fin blockCount) (code : Nat) : Bool :=
  RawKindedFacePlacement.check 6 (raw b) template root FacetUniverses.RootedSevenMixed033.cells
    code 0 (witness b code)
noncomputable def test (i : Nat) : Bool :=
  let b := Fin.ofNat blockCount i
  FiniteChecks.checkRange (placement b)
    0 (RawFacePlacement.count (raw b).shared (raw b).shared)
noncomputable def symmetry (i : Nat) : Bool :=
  RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed033.Outside.vertexCode root.vertices
    (raw (Fin.ofNat blockCount i))
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed033.T4

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed033.T4
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
theorem check_0025_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 25)) 0 8 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 25)) 0 8 (by decide +kernel)
theorem check_0025_0008 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 25)) 8 16 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 25)) 8 8 (by decide +kernel)
theorem check_0025_0016 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 25)) 16 24 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 25)) 16 8 (by decide +kernel)
theorem check_0025_0024 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 25)) 24 32 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 25)) 24 8 (by decide +kernel)
theorem check_0025_0032 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 25)) 32 40 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 25)) 32 8 (by decide +kernel)
theorem check_0025_0040 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 25)) 40 48 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 25)) 40 8 (by decide +kernel)
theorem check_0025_0048 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 25)) 48 56 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 25)) 48 8 (by decide +kernel)
theorem check_0025_0056 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 25)) 56 64 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 25)) 56 8 (by decide +kernel)
theorem check_0025_0064 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 25)) 64 72 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 25)) 64 8 (by decide +kernel)
theorem check_0025_0072 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 25)) 72 80 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 25)) 72 8 (by decide +kernel)
theorem check_0025_0080 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 25)) 80 88 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 25)) 80 8 (by decide +kernel)
theorem check_0025_0088 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 25)) 88 96 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 25)) 88 8 (by decide +kernel)
theorem check_0025_0096 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 25)) 96 104 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 25)) 96 8 (by decide +kernel)
theorem check_0025_0104 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 25)) 104 112 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 25)) 104 8 (by decide +kernel)
theorem check_0025_0112 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 25)) 112 120 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 25)) 112 8 (by decide +kernel)
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
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed033.T4

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed033.T4
theorem metadata_validity_0000 : FiniteChecks.Interval validity 0 16 :=
  FiniteChecks.interval_of_check validity 0 16 (by decide +kernel)
theorem metadata_validity_0016 : FiniteChecks.Interval validity 16 26 :=
  FiniteChecks.interval_of_check validity 16 10 (by decide +kernel)
theorem metadata_validity : FiniteChecks.Interval validity 0 blockCount :=
  (FiniteChecks.interval_append (validity) 0 16 26
  metadata_validity_0000
  metadata_validity_0016)
theorem metadata_symmetry_0000 : FiniteChecks.Interval symmetry 0 16 :=
  FiniteChecks.interval_of_check symmetry 0 16 (by decide +kernel)
theorem metadata_symmetry_0016 : FiniteChecks.Interval symmetry 16 26 :=
  FiniteChecks.interval_of_check symmetry 16 10 (by decide +kernel)
theorem metadata_symmetry : FiniteChecks.Interval symmetry 0 blockCount :=
  (FiniteChecks.interval_append (symmetry) 0 16 26
  metadata_symmetry_0000
  metadata_symmetry_0016)
theorem metadata_normalizers :
    RawFaceNormalizers.completeCheck 6 template root raw faceWitness = true := by decide +kernel
theorem metadata_root : RawFacetEmbedding.wellFormedCheck root = true := by decide +kernel
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed033.T4
