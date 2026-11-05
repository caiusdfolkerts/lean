module
prelude
public import RootedSevenMixed031
public import RawKindedFacePlacement
public import RootedSevenMixed031OutsideData
public import RawOutsidePlacement

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed031.T4
open ConcreteGrowth
abbrev blockCount : Nat := 36
noncomputable def template : Cell := ⟨4, 63, [3, 5, 6, 10, 12, 20, 24, 33, 36, 48], [7, 14, 28, 37, 52, 59]⟩
noncomputable def root : Cell := FacetUniverses.RootedSevenMixed031.cells 0
noncomputable def records : Table (RawFacePlacement.Block × Nat) :=
(.branch 18
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (⟨3, 3, 5517840, 5517840, 434925761040, 361742426640⟩, 656456644548802291646530062))
 (.leaf (⟨3, 3, 5517840, 5517840, 434875429665, 361742409990⟩, 678217641348325570454553120)))
 (.branch 3
 (.leaf (⟨3, 3, 5517840, 5517840, 430328804640, 361736204640⟩, 699978638147848849262576178))
 (.leaf (⟨3, 3, 5517840, 5517840, 361055680050, 361626079350⟩, 725366467747292674538603079))))
 (.branch 6
 (.branch 5
 (.leaf (⟨3, 3, 5517840, 5517840, 352465745475, 361625618550⟩, 747127464546815953346626137))
 (.leaf (⟨3, 3, 5517840, 5517840, 288041236050, 361617784950⟩, 768888461346339232154649195)))
 (.branch 7
 (.leaf (⟨3, 3, 5517840, 5517840, 215026792020, 361617201270⟩, 790649458145862510962672253))
 (.branch 8
 (.leaf (⟨3, 3, 5505825, 5513475, 434925761040, 361742426640⟩, 644367183437626772754858519))
 (.leaf (⟨3, 3, 5505825, 5513475, 434875429665, 361742409990⟩, 666128180237150051562881577))))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf (⟨3, 3, 5505825, 5513475, 430328804640, 361736204640⟩, 687889177036673330370904635))
 (.leaf (⟨3, 3, 5505825, 5513475, 361055680050, 361626079350⟩, 713277006636117155646931536)))
 (.branch 12
 (.leaf (⟨3, 3, 5505825, 5513475, 352465745475, 361625618550⟩, 735038003435640434454954594))
 (.leaf (⟨3, 3, 5505825, 5513475, 288041236050, 361617784950⟩, 756799000235163713262977652))))
 (.branch 15
 (.branch 14
 (.leaf (⟨3, 3, 5505825, 5513475, 215026792020, 361617201270⟩, 778559997034686992071000710))
 (.leaf (⟨3, 3, 5309490, 5378115, 434925761040, 361742426640⟩, 638322683469858328936972830)))
 (.branch 16
 (.leaf (⟨3, 3, 5309490, 5378115, 434875429665, 361742409990⟩, 660083680269381607744995888))
 (.branch 17
 (.leaf (⟨3, 3, 5309490, 5378115, 430328804640, 361736204640⟩, 681844677068904886553018946))
 (.leaf (⟨3, 3, 5309490, 5378115, 361055680050, 361626079350⟩, 707232506668348711829045847)))))))
 (.branch 27
 (.branch 22
 (.branch 20
 (.branch 19
 (.leaf (⟨3, 3, 5309490, 5378115, 352465745475, 361625618550⟩, 728993503467871990637068905))
 (.leaf (⟨3, 3, 5309490, 5378115, 288041236050, 361617784950⟩, 750754500267395269445091963)))
 (.branch 21
 (.leaf (⟨3, 3, 5309490, 5378115, 215026792020, 361617201270⟩, 772515497066918548253115021))
 (.leaf (⟨3, 3, 4396320, 2441520, 434925761040, 361742426640⟩, 643158239171831015529185817))))
 (.branch 24
 (.branch 23
 (.leaf (⟨3, 3, 4396320, 2441520, 434875429665, 361742409990⟩, 664919235971354294337208875))
 (.leaf (⟨3, 3, 4396320, 2441520, 430328804640, 361736204640⟩, 686680232770877573145231933)))
 (.branch 25
 (.leaf (⟨3, 3, 4396320, 2441520, 361055680050, 361626079350⟩, 712068062370321398421258834))
 (.branch 26
 (.leaf (⟨3, 3, 4396320, 2441520, 352465745475, 361625618550⟩, 733829059169844677229281892))
 (.leaf (⟨3, 3, 4396320, 2441520, 288041236050, 361617784950⟩, 755590055969367956037304950))))))
 (.branch 31
 (.branch 29
 (.branch 28
 (.leaf (⟨3, 3, 4396320, 2441520, 215026792020, 361617201270⟩, 777351052768891234845328008))
 (.leaf (⟨3, 3, 3212610, 2183235, 434925761040, 361742426640⟩, 641949516269778845339746842)))
 (.branch 30
 (.leaf (⟨3, 3, 3212610, 2183235, 434875429665, 361742409990⟩, 663710513069302124147769900))
 (.leaf (⟨3, 3, 3212610, 2183235, 430328804640, 361736204640⟩, 685471509868825402955792958))))
 (.branch 33
 (.branch 32
 (.leaf (⟨3, 3, 3212610, 2183235, 361055680050, 361626079350⟩, 710859339468269228231819859))
 (.leaf (⟨3, 3, 3212610, 2183235, 352465745475, 361625618550⟩, 732620336267792507039842917)))
 (.branch 34
 (.leaf (⟨3, 3, 3212610, 2183235, 288041236050, 361617784950⟩, 754381333067315785847865975))
 (.branch 35
 (.leaf (⟨3, 3, 3212610, 2183235, 215026792020, 361617201270⟩, 776142329866839064655889033))
 (.leaf (⟨5, 3, 2442000, 4400400, 423464616720, 508303714320⟩, 840503909375880462923562479851352992537593007500404778702973293082017641721247254378629755329812426864282440217027449552534589901838514999602197569330234139861543357998864085658423914119347554240993429139419124040261457255911901779354155642340100638432478017257331829832009618058503751709709683265007665936191087950213345148164867475022037348230802893564437381655184937289323641698261050980966145414569321052693039644927132611033318964240632488969704105999934089096807519313612906034727477713113046986969749640476306276758199431149824045786060233295308241442041990663079199300))))))))
noncomputable def raw (i : Fin blockCount) : RawFacePlacement.Block := (records.get i.val).1
noncomputable def witness (i : Fin blockCount) (code : Nat) : Fin 655 :=
  Fin.ofNat 655 (Nat.land (Nat.shiftRight (records.get i.val).2 (16 * code)) 65535)
noncomputable def faceTable : Table Nat :=
(.branch 28760
 (.branch 14373
 (.branch 7256
 (.branch 7205
 (.branch 7182
 (.leaf 0)
 (.leaf 1))
 (.branch 7244
 (.leaf 2)
 (.leaf 3)))
 (.branch 7280
 (.branch 7268
 (.leaf 4)
 (.leaf 5))
 (.branch 14343
 (.leaf 6)
 (.branch 14350
 (.leaf 7)
 (.leaf 8)))))
 (.branch 14448
 (.branch 14424
 (.branch 14412
 (.leaf 9)
 (.leaf 10))
 (.branch 14436
 (.leaf 11)
 (.leaf 12)))
 (.branch 28686
 (.branch 28679
 (.leaf 13)
 (.leaf 14))
 (.branch 28709
 (.leaf 15)
 (.branch 28748
 (.leaf 16)
 (.leaf 17))))))
 (.branch 38000
 (.branch 37902
 (.branch 28784
 (.branch 28772
 (.leaf 18)
 (.leaf 19))
 (.branch 37895
 (.leaf 20)
 (.leaf 21)))
 (.branch 37964
 (.branch 37925
 (.leaf 22)
 (.leaf 23))
 (.branch 37976
 (.leaf 24)
 (.branch 37988
 (.leaf 25)
 (.leaf 26)))))
 (.branch 53324
 (.branch 53262
 (.branch 53255
 (.leaf 27)
 (.leaf 28))
 (.branch 53285
 (.leaf 29)
 (.leaf 30)))
 (.branch 53348
 (.branch 53336
 (.leaf 31)
 (.leaf 32))
 (.branch 53360
 (.leaf 33)
 (.branch 60475
 (.leaf 34)
 (.leaf 35)))))))
noncomputable def faceWitness (s r : Nat) : Fin blockCount :=
  Fin.ofNat blockCount (faceTable.get (s * 1024 + r))
noncomputable def validity (i : Nat) : Bool :=
  RawFaceNormalizers.blockValidCheck 6 (raw (Fin.ofNat blockCount i))
noncomputable def placement (b : Fin blockCount) (code : Nat) : Bool :=
  RawKindedFacePlacement.check 6 (raw b) template root FacetUniverses.RootedSevenMixed031.cells
    code 0 (witness b code)
noncomputable def test (i : Nat) : Bool :=
  let b := Fin.ofNat blockCount i
  FiniteChecks.checkRange (placement b)
    0 (RawFacePlacement.count (raw b).shared (raw b).shared)
noncomputable def symmetry (i : Nat) : Bool :=
  RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenMixed031.Outside.vertexCode root.vertices
    (raw (Fin.ofNat blockCount i))
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed031.T4

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed031.T4
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
theorem check_0032_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 32)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 32)) 0 6 (by decide +kernel)
theorem block_0032 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 32)) 0 6 :=
  check_0032_0000
theorem check_0033_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 33)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 33)) 0 6 (by decide +kernel)
theorem block_0033 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 33)) 0 6 :=
  check_0033_0000
theorem check_0034_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 34)) 0 6 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 34)) 0 6 (by decide +kernel)
theorem block_0034 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 34)) 0 6 :=
  check_0034_0000
theorem check_0035_0000 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 35)) 0 8 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 35)) 0 8 (by decide +kernel)
theorem check_0035_0008 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 35)) 8 16 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 35)) 8 8 (by decide +kernel)
theorem check_0035_0016 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 35)) 16 24 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 35)) 16 8 (by decide +kernel)
theorem check_0035_0024 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 35)) 24 32 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 35)) 24 8 (by decide +kernel)
theorem check_0035_0032 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 35)) 32 40 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 35)) 32 8 (by decide +kernel)
theorem check_0035_0040 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 35)) 40 48 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 35)) 40 8 (by decide +kernel)
theorem check_0035_0048 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 35)) 48 56 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 35)) 48 8 (by decide +kernel)
theorem check_0035_0056 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 35)) 56 64 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 35)) 56 8 (by decide +kernel)
theorem check_0035_0064 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 35)) 64 72 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 35)) 64 8 (by decide +kernel)
theorem check_0035_0072 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 35)) 72 80 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 35)) 72 8 (by decide +kernel)
theorem check_0035_0080 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 35)) 80 88 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 35)) 80 8 (by decide +kernel)
theorem check_0035_0088 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 35)) 88 96 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 35)) 88 8 (by decide +kernel)
theorem check_0035_0096 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 35)) 96 104 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 35)) 96 8 (by decide +kernel)
theorem check_0035_0104 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 35)) 104 112 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 35)) 104 8 (by decide +kernel)
theorem check_0035_0112 : FiniteChecks.Interval (placement (Fin.ofNat blockCount 35)) 112 120 :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount 35)) 112 8 (by decide +kernel)
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
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed031.T4

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.RootedCanonical.RootedSevenMixed031.T4
theorem metadata_validity_0000 : FiniteChecks.Interval validity 0 16 :=
  FiniteChecks.interval_of_check validity 0 16 (by decide +kernel)
theorem metadata_validity_0016 : FiniteChecks.Interval validity 16 32 :=
  FiniteChecks.interval_of_check validity 16 16 (by decide +kernel)
theorem metadata_validity_0032 : FiniteChecks.Interval validity 32 36 :=
  FiniteChecks.interval_of_check validity 32 4 (by decide +kernel)
theorem metadata_validity : FiniteChecks.Interval validity 0 blockCount :=
  (FiniteChecks.interval_append (validity) 0 16 36
  metadata_validity_0000
  (FiniteChecks.interval_append (validity) 16 32 36
  metadata_validity_0016
  metadata_validity_0032))
theorem metadata_symmetry_0000 : FiniteChecks.Interval symmetry 0 16 :=
  FiniteChecks.interval_of_check symmetry 0 16 (by decide +kernel)
theorem metadata_symmetry_0016 : FiniteChecks.Interval symmetry 16 32 :=
  FiniteChecks.interval_of_check symmetry 16 16 (by decide +kernel)
theorem metadata_symmetry_0032 : FiniteChecks.Interval symmetry 32 36 :=
  FiniteChecks.interval_of_check symmetry 32 4 (by decide +kernel)
theorem metadata_symmetry : FiniteChecks.Interval symmetry 0 blockCount :=
  (FiniteChecks.interval_append (symmetry) 0 16 36
  metadata_symmetry_0000
  (FiniteChecks.interval_append (symmetry) 16 32 36
  metadata_symmetry_0016
  metadata_symmetry_0032))
theorem metadata_normalizers :
    RawFaceNormalizers.completeCheck 6 template root raw faceWitness = true := by decide +kernel
theorem metadata_root : RawFacetEmbedding.wellFormedCheck root = true := by decide +kernel
end Papers.RationalityTen.RootedCanonical.RootedSevenMixed031.T4
