module
prelude
public import RootedSevenMixed012
public import RawKindedFacePlacement
public import RootedSevenMixed012OutsideData
public import RawOutsidePlacement

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed012.T5
open ConcreteGrowth
abbrev blockCount : Nat := 22
noncomputable def template : Cell := ⟨4, 63, [3, 5, 6, 10, 17, 20, 24, 36, 40, 48], [7, 21, 27, 46, 52, 56]⟩
noncomputable def root : Cell := FacetUniverses.RootedSevenMixed012.cells 0
noncomputable def records : Table (RawFacePlacement.Block × Nat) :=
(.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf (⟨3, 3, 5517840, 5517840, 434925761040, 361742426640⟩, 527099478887435110289899926))
 (.leaf (⟨3, 3, 5517840, 5517840, 352465745475, 361625618550⟩, 788231440481714455986176622)))
 (.branch 3
 (.leaf (⟨3, 3, 5517840, 5517840, 283746268755, 361617754230⟩, 875275427679807571218268854))
 (.branch 4
 (.leaf (⟨3, 3, 5517840, 5517840, 215026792020, 361617201270⟩, 962319414877900686450361086))
 (.leaf (⟨3, 3, 5444640, 5390640, 434925761040, 361742426640⟩, 570621472486481667905946042)))))
 (.branch 8
 (.branch 6
 (.leaf (⟨3, 3, 5444640, 5390640, 352465745475, 361625618550⟩, 831753434080761013602222738))
 (.branch 7
 (.leaf (⟨3, 3, 5444640, 5390640, 283746268755, 361617754230⟩, 918797421278854128834314970))
 (.leaf (⟨3, 3, 5444640, 5390640, 215026792020, 361617201270⟩, 1005841408476947244066407202))))
 (.branch 9
 (.leaf (⟨4, 3, 5391120, 5448720, 434488427280, 435025028880⟩, 295803635385530867992913102167322985256805198810021104620240865113917638945268653476728403808472580579125637415390))
 (.branch 10
 (.leaf (⟨4, 3, 5391120, 5448720, 429656593185, 435020112135⟩, 4917335504195390732883601034544641524957385832676525068709551009935222841941161495415929346646581659877638144))
 (.leaf (⟨4, 3, 5391120, 5448720, 425630061600, 435019743600⟩, 5357693957699710996525510318775041943206551852913959461176974969916102578006300164770675205595601106911756288))))))
 (.branch 16
 (.branch 13
 (.branch 12
 (.leaf (⟨4, 3, 4215585, 3481860, 434488427280, 435025028880⟩, 4394343348236977016485545312111906810363783798124516854079640711897049989237329978425681727968669355716968448))
 (.leaf (⟨4, 3, 4215585, 3481860, 429656593185, 435020112135⟩, 316846576927183388458267078777738127271484222714888709730113051280089514737258483891339319886934183035894828630557)))
 (.branch 14
 (.leaf (⟨4, 3, 4215585, 3481860, 425630061600, 435019743600⟩, 345705468184308251164137459980910385978130777458669732806970335151288471113141178394055808815383661280808677671501))
 (.branch 15
 (.leaf (⟨3, 3, 3212610, 2183235, 434925761040, 361742426640⟩, 540398197873692467111854557))
 (.leaf (⟨3, 3, 3212610, 2183235, 352465745475, 361625618550⟩, 801530159467971812808131253)))))
 (.branch 19
 (.branch 17
 (.leaf (⟨3, 3, 3212610, 2183235, 283746268755, 361617754230⟩, 888574146666064928040223485))
 (.branch 18
 (.leaf (⟨3, 3, 3212610, 2183235, 215026792020, 361617201270⟩, 975618133864158043272315717))
 (.leaf (⟨3, 3, 2164035, 2164035, 434925761040, 361742426640⟩, 501711759976900053884666289))))
 (.branch 20
 (.leaf (⟨3, 3, 2164035, 2164035, 352465745475, 361625618550⟩, 762843721571179399580942985))
 (.branch 21
 (.leaf (⟨3, 3, 2164035, 2164035, 283746268755, 361617754230⟩, 849887708769272514813035217))
 (.leaf (⟨3, 3, 2164035, 2164035, 215026792020, 361617201270⟩, 936931695967365630045127449)))))))
noncomputable def raw (i : Fin blockCount) : RawFacePlacement.Block := (records.get i.val).1
noncomputable def witness (i : Fin blockCount) (code : Nat) : Fin 838 :=
  Fin.ofNat 838 (Nat.land (Nat.shiftRight (records.get i.val).2 (16 * code)) 65535)
noncomputable def faceTable : Table Nat :=
(.branch 47131
 (.branch 21592
 (.branch 7272
 (.branch 7256
 (.leaf 0)
 (.leaf 1))
 (.branch 7280
 (.leaf 2)
 (.branch 21511
 (.leaf 3)
 (.leaf 4))))
 (.branch 27675
 (.branch 21608
 (.leaf 5)
 (.branch 21616
 (.leaf 6)
 (.leaf 7)))
 (.branch 27694
 (.leaf 8)
 (.branch 27701
 (.leaf 9)
 (.leaf 10)))))
 (.branch 53352
 (.branch 47157
 (.branch 47150
 (.leaf 11)
 (.leaf 12))
 (.branch 53255
 (.leaf 13)
 (.branch 53336
 (.leaf 14)
 (.leaf 15))))
 (.branch 57432
 (.branch 53360
 (.leaf 16)
 (.branch 57351
 (.leaf 17)
 (.leaf 18)))
 (.branch 57448
 (.leaf 19)
 (.branch 57456
 (.leaf 20)
 (.leaf 21))))))
noncomputable def faceWitness (s r : Nat) : Fin blockCount :=
  Fin.ofNat blockCount (faceTable.get (s * 1024 + r))
noncomputable def validity (i : Nat) : Bool :=
  RawFaceNormalizers.blockValidCheck 6 (raw (Fin.ofNat blockCount i))
noncomputable def placement (b : Fin blockCount) (code : Nat) : Bool :=
  RawKindedFacePlacement.check 6 (raw b) template root FacetUniverses.RootedSevenMixed012.cells
    code 0 (witness b code)
noncomputable def test (i : Nat) : Bool :=
  let b := Fin.ofNat blockCount i
  FiniteChecks.checkRange (placement b)
    0 (RawFacePlacement.count (raw b).shared (raw b).shared)
noncomputable def symmetry (i : Nat) : Bool :=
  RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed012.Outside.vertexCode root.vertices
    (raw (Fin.ofNat blockCount i))
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed012.T5

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed012.T5
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
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed012.T5

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed012.T5
theorem metadata_validity_0000 : FiniteChecks.Interval validity 0 16 :=
  FiniteChecks.interval_of_check validity 0 16 (by decide +kernel)
theorem metadata_validity_0016 : FiniteChecks.Interval validity 16 22 :=
  FiniteChecks.interval_of_check validity 16 6 (by decide +kernel)
theorem metadata_validity : FiniteChecks.Interval validity 0 blockCount :=
  (FiniteChecks.interval_append (validity) 0 16 22
  metadata_validity_0000
  metadata_validity_0016)
theorem metadata_symmetry_0000 : FiniteChecks.Interval symmetry 0 16 :=
  FiniteChecks.interval_of_check symmetry 0 16 (by decide +kernel)
theorem metadata_symmetry_0016 : FiniteChecks.Interval symmetry 16 22 :=
  FiniteChecks.interval_of_check symmetry 16 6 (by decide +kernel)
theorem metadata_symmetry : FiniteChecks.Interval symmetry 0 blockCount :=
  (FiniteChecks.interval_append (symmetry) 0 16 22
  metadata_symmetry_0000
  metadata_symmetry_0016)
theorem metadata_normalizers :
    RawFaceNormalizers.completeCheck 6 template root raw faceWitness = true := by decide +kernel
theorem metadata_root : RawFacetEmbedding.wellFormedCheck root = true := by decide +kernel
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed012.T5
