module
public import Consolidated.SemanticData
public import Mathlib.Data.Fin.Tuple.Basic
public import MatroidCatalogue.Definitions
public import MatroidChecked.Cases00
public import MatroidChecked.FastSemanticChecks
public import MatroidChecked.PublicRefutations.N7R3C18
public import MatroidChecked.PublicRefutations.N7R3C19
public import MatroidChecked.PublicRefutations.N7R3C20
public import MatroidChecked.PublicRefutations.N7R3C21
public import MatroidChecked.PublicRefutations.N7R3C22
public import MatroidChecked.PublicRefutations.N7R3C23
public import MatroidChecked.PublicRefutations.N7R3C24
public import MatroidChecked.PublicRefutations.N7R4C0
public import MatroidChecked.PublicRefutations.N7R4C1
public import MatroidChecked.PublicRefutations.N7R4C10
public import MatroidChecked.PublicRefutations.N7R4C11
public import MatroidChecked.PublicRefutations.N7R4C12
public import MatroidChecked.PublicRefutations.N7R4C13
public import MatroidChecked.PublicRefutations.N7R4C14
public import MatroidChecked.PublicRefutations.N7R4C15
public import MatroidChecked.PublicRefutations.N7R4C16
public import MatroidChecked.PublicRefutations.N7R4C17
public import MatroidChecked.PublicRefutations.N7R4C2
public import MatroidChecked.PublicRefutations.N7R4C3
public import MatroidChecked.PublicRefutations.N7R4C4
public import MatroidChecked.PublicRefutations.N7R4C5
public import MatroidChecked.PublicRefutations.N7R4C6
public import MatroidChecked.PublicRefutations.N7R4C7
public import MatroidChecked.PublicRefutations.N7R4C8
public import MatroidChecked.PublicRefutations.N7R4C9
public import MatroidChecked.PublicRefutations.N8R4C0
public import MatroidChecked.PublicRefutations.N8R4C1
public import MatroidChecked.PublicRefutations.N8R4C10
public import MatroidChecked.PublicRefutations.N8R4C11
public import MatroidChecked.PublicRefutations.N8R4C12
public import MatroidChecked.PublicRefutations.N8R4C13
public import MatroidChecked.PublicRefutations.N8R4C14
public import MatroidChecked.PublicRefutations.N8R4C15
public import MatroidChecked.PublicRefutations.N8R4C16
public import MatroidChecked.PublicRefutations.N8R4C17
public import MatroidChecked.PublicRefutations.N8R4C18
public import MatroidChecked.PublicRefutations.N8R4C19
public import MatroidChecked.PublicRefutations.N8R4C2
public import MatroidChecked.PublicRefutations.N8R4C20
public import MatroidChecked.PublicRefutations.N8R4C21
public import MatroidChecked.PublicRefutations.N8R4C22
public import MatroidChecked.PublicRefutations.N8R4C23
public import MatroidChecked.PublicRefutations.N8R4C24
public import MatroidChecked.PublicRefutations.N8R4C25
public import MatroidChecked.PublicRefutations.N8R4C26
public import MatroidChecked.PublicRefutations.N8R4C27
public import MatroidChecked.PublicRefutations.N8R4C28
public import MatroidChecked.PublicRefutations.N8R4C29
public import MatroidChecked.PublicRefutations.N8R4C3
public import MatroidChecked.PublicRefutations.N8R4C30
public import MatroidChecked.PublicRefutations.N8R4C31
public import MatroidChecked.PublicRefutations.N8R4C32
public import MatroidChecked.PublicRefutations.N8R4C33
public import MatroidChecked.PublicRefutations.N8R4C34
public import MatroidChecked.PublicRefutations.N8R4C35
public import MatroidChecked.PublicRefutations.N8R4C36
public import MatroidChecked.PublicRefutations.N8R4C37
public import MatroidChecked.PublicRefutations.N8R4C38
public import MatroidChecked.PublicRefutations.N8R4C39
public import MatroidChecked.PublicRefutations.N8R4C4
public import MatroidChecked.PublicRefutations.N8R4C40
public import MatroidChecked.PublicRefutations.N8R4C41
public import MatroidChecked.PublicRefutations.N8R4C42
public import MatroidChecked.PublicRefutations.N8R4C43
public import MatroidChecked.PublicRefutations.N8R4C44
public import MatroidChecked.PublicRefutations.N8R4C45
public import MatroidChecked.PublicRefutations.N8R4C46
public import MatroidChecked.PublicRefutations.N8R4C47
public import MatroidChecked.PublicRefutations.N8R4C48
public import MatroidChecked.PublicRefutations.N8R4C49
public import MatroidChecked.PublicRefutations.N8R4C5
public import MatroidChecked.PublicRefutations.N8R4C50
public import MatroidChecked.PublicRefutations.N8R4C51
public import MatroidChecked.PublicRefutations.N8R4C52
public import MatroidChecked.PublicRefutations.N8R4C53
public import MatroidChecked.PublicRefutations.N8R4C54
public import MatroidChecked.PublicRefutations.N8R4C55
public import MatroidChecked.PublicRefutations.N8R4C56
public import MatroidChecked.PublicRefutations.N8R4C58
public import MatroidChecked.PublicRefutations.N8R4C59
public import MatroidChecked.PublicRefutations.N8R4C6
public import MatroidChecked.PublicRefutations.N8R4C60
public import MatroidChecked.PublicRefutations.N8R4C63
public import MatroidChecked.PublicRefutations.N8R4C64
public import MatroidChecked.PublicRefutations.N8R4C65
public import MatroidChecked.PublicRefutations.N8R4C66
public import MatroidChecked.PublicRefutations.N8R4C67
public import MatroidChecked.PublicRefutations.N8R4C7
public import MatroidChecked.PublicRefutations.N8R4C71
public import MatroidChecked.PublicRefutations.N8R4C72
public import MatroidChecked.PublicRefutations.N8R4C73
public import MatroidChecked.PublicRefutations.N8R4C74
public import MatroidChecked.PublicRefutations.N8R4C8
public import MatroidChecked.PublicRefutations.N8R4C9


section BundlePart0
/- Source: MatroidChecked/SemanticChunks/Cases05Part01.lean -/




@[expose] public section
noncomputable section

/- Source: MatroidCatalogue/Cases/N8R4C36Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C36

abbrev U := N8R4.grid
noncomputable def old : Finset (Finset (Fin 8)) := N7R4.family 36
noncomputable def newIndexTree : Table ℕ := (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf 35) (.leaf 36)) (.node 3 (.leaf 37) (.leaf 38))) (.node 6 (.node 5 (.leaf 39) (.leaf 40)) (.node 7 (.leaf 41) (.leaf 42)))) (.node 12 (.node 10 (.node 9 (.leaf 43) (.leaf 44)) (.node 11 (.leaf 45) (.leaf 46))) (.node 14 (.node 13 (.leaf 47) (.leaf 48)) (.node 15 (.leaf 49) (.node 16 (.leaf 50) (.leaf 51)))))) (.node 26 (.node 21 (.node 19 (.node 18 (.leaf 52) (.leaf 53)) (.node 20 (.leaf 54) (.leaf 55))) (.node 23 (.node 22 (.leaf 56) (.leaf 57)) (.node 24 (.leaf 58) (.node 25 (.leaf 59) (.leaf 60))))) (.node 30 (.node 28 (.node 27 (.leaf 61) (.leaf 62)) (.node 29 (.leaf 63) (.leaf 64))) (.node 32 (.node 31 (.leaf 65) (.leaf 66)) (.node 33 (.leaf 67) (.node 34 (.leaf 68) (.leaf 69)))))))
noncomputable def newIndex (i : Fin 35) : Fin 70 := Fin.ofNat 70 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 77 (.node 38 (.node 19 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (17113743360,89,2054353)) (.leaf (33152696320,87,4151504))) (.node 3 (.leaf (32011780096,87,4151490)) (.leaf (29729947648,87,4151322)))) (.node 6 (.node 5 (.leaf (25166282752,87,4149530)) (.leaf (34293612544,90,10442376))) (.node 7 (.leaf (16172252160,146,4131610)) (.node 8 (.leaf (1073740800,157,10442376)) (.leaf (17179868160,158,12535432)))))) (.node 14 (.node 11 (.node 10 (.leaf (32145079296,153,10442376)) (.leaf (29997595648,153,10442320))) (.node 12 (.leaf (25702628352,153,10441424)) (.node 13 (.leaf (34292562944,154,12535432)) (.leaf (33151646720,153,10442369))))) (.node 16 (.node 15 (.leaf (29930421248,153,10442306)) (.leaf (25635453952,153,10441410))) (.node 17 (.leaf (34225388544,154,12535425)) (.node 18 (.leaf (33017297920,153,10442257)) (.leaf (31943556096,153,10442250))))))) (.node 28 (.node 23 (.node 21 (.node 20 (.leaf (25501105152,153,10441242)) (.leaf (34091039744,154,12535313))) (.node 22 (.leaf (32748600320,153,10440913)) (.leaf (31674858496,153,10440906)))) (.node 25 (.node 24 (.leaf (29527374848,153,10440794)) (.leaf (33822342144,154,12533969))) (.node 26 (.leaf (33285995520,160,10442376)) (.node 27 (.leaf (32212253696,160,10442369)) (.leaf (30064770048,160,10442257)))))) (.node 33 (.node 30 (.node 29 (.leaf (25769802752,160,10440913)) (.leaf (34359737344,161,12535432))) (.node 31 (.leaf (1072694256,146,3959578)) (.node 32 (.leaf (1048560,146,2353946)) (.leaf (1073741808,258,14055048))))) (.node 35 (.node 34 (.leaf (16173171696,157,10413704)) (.leaf (17179804656,158,12478088))) (.node 36 (.leaf (16173236208,258,14141064)) (.node 37 (.leaf (17112825840,157,9954952)) (.leaf (17113808880,158,11789960)))))))) (.node 57 (.node 47 (.node 42 (.node 40 (.node 39 (.leaf (17178886128,258,14599816)) (.leaf (17179869168,264,16434824))) (.node 41 (.leaf (33151648752,153,10413704)) (.leaf (33017431024,153,10413648)))) (.node 44 (.node 43 (.leaf (32748995568,153,10412752)) (.leaf (33285866480,154,12478088))) (.node 45 (.leaf (32144950256,153,10413697)) (.node 46 (.leaf (31943623664,153,10413634)) (.leaf (31675188208,153,10412738)))))) (.node 52 (.node 49 (.node 48 (.leaf (32212059120,154,12478081)) (.leaf (29997335536,153,10413585))) (.node 50 (.leaf (29930226672,153,10413578)) (.node 51 (.leaf (29527573488,153,10412570)) (.leaf (30064444400,154,12477969))))) (.node 54 (.node 53 (.leaf (25702106096,153,10412241)) (.leaf (25634997232,153,10412234))) (.node 55 (.leaf (25500779504,153,10412122)) (.node 56 (.leaf (25769214960,154,12476625)) (.leaf (34292564976,160,10413704))))))) (.node 67 (.node 62 (.node 59 (.node 58 (.leaf (34225456112,160,10413697)) (.leaf (34091238384,160,10413585))) (.node 60 (.leaf (33822802928,160,10412241)) (.node 61 (.leaf (34359673840,161,12478088)) (.leaf (33152696304,153,9954952))))) (.node 64 (.node 63 (.leaf (33152565232,153,9954896)) (.leaf (33152303088,153,9954000))) (.node 65 (.leaf (33152827376,154,11789960)) (.node 66 (.leaf (32011911152,153,9954945)) (.leaf (32011714544,153,9954882)))))) (.node 72 (.node 69 (.node 68 (.leaf (32011452400,153,9953986)) (.leaf (32011976688,154,11789953))) (.node 70 (.leaf (29730209776,153,9954833)) (.node 71 (.leaf (29730144240,153,9954826)) (.leaf (29729751024,153,9953818))))) (.node 74 (.node 73 (.leaf (29730275312,154,11789841)) (.leaf (25166807024,153,9953489))) (.node 75 (.leaf (25166741488,153,9953482)) (.node 76 (.leaf (25166610416,153,9953370)) (.leaf (25166872560,154,11788497))))))))) (.node 116 (.node 96 (.node 86 (.node 81 (.node 79 (.node 78 (.leaf (34293612528,160,9954952)) (.leaf (34293546992,160,9954945))) (.node 80 (.leaf (34293415920,160,9954833)) (.leaf (34293153776,160,9953489)))) (.node 83 (.node 82 (.leaf (34293678064,161,11789960)) (.leaf (29930487792,261,9926280))) (.node 84 (.leaf (25635520496,261,9925832)) (.node 85 (.leaf (34225455088,262,12306056)) (.leaf (29527834608,261,9954392)))))) (.node 91 (.node 88 (.node 87 (.leaf (30064705520,262,12219984)) (.leaf (31675318256,261,9954504))) (.node 89 (.leaf (33822801904,262,12305104)) (.node 90 (.leaf (31943753712,261,9954952)) (.leaf (32212189168,262,12220040))))) (.node 93 (.node 92 (.leaf (25501302768,261,9925720)) (.leaf (34091237360,262,12306000))) (.node 94 (.leaf (25769738224,262,12219088)) (.node 95 (.leaf (34359672816,263,14599816)) (.leaf (29930029040,261,10413123))))))) (.node 106 (.node 101 (.node 98 (.node 97 (.leaf (29930553328,262,11761218)) (.leaf (33151254512,261,10441928))) (.node 99 (.leaf (34224996336,262,12534466)) (.node 100 (.leaf (33151516656,261,10442376)) (.leaf (33151778800,262,11789960))))) (.node 103 (.node 102 (.leaf (25635323888,261,10155075)) (.leaf (34225258480,262,12535362))) (.node 104 (.leaf (25635586032,262,11760322)) (.node 105 (.leaf (34225520624,263,14141057)) (.leaf (29997137904,261,10413144)))))) (.node 111 (.node 108 (.node 107 (.leaf (30064246768,262,12476954)) (.leaf (29997531120,261,10155656))) (.node 109 (.leaf (29997662192,262,11761232)) (.node 110 (.leaf (29527769072,261,9954371)) (.leaf (30064639984,262,12219970))))) (.node 113 (.node 112 (.leaf (29527900144,262,11788826)) (.leaf (30064771056,263,14054929))) (.node 114 (.leaf (32144621552,261,10413256)) (.node 115 (.leaf (34292105200,262,12534480)) (.leaf (33017036784,261,10441816)))))))) (.node 135 (.node 125 (.node 120 (.node 118 (.node 117 (.leaf (33285472240,262,12477136)) (.leaf (31943294960,261,10441795))) (.node 119 (.leaf (34090778608,262,12534298)) (.leaf (32211730416,262,12477122)))) (.node 122 (.node 121 (.leaf (34359214064,263,14598353)) (.leaf (25702563824,261,10155208))) (.node 123 (.leaf (34292498416,262,12535432)) (.node 124 (.leaf (32144883696,261,10413704)) (.leaf (32145145840,262,11761288)))))) (.node 130 (.node 127 (.node 126 (.leaf (25702432752,261,10155096)) (.leaf (34292367344,262,12535376))) (.node 128 (.leaf (25702694896,262,11760336)) (.node 129 (.leaf (34292629488,263,14141064)) (.leaf (31943819248,262,11789890))))) (.node 132 (.node 131 (.leaf (31675121648,261,10212419)) (.leaf (32211992560,262,12478018))) (.node 133 (.leaf (31675383792,262,11788994)) (.node 134 (.leaf (32212254704,263,14055041)) (.leaf (25769541616,262,12218906))))))) (.node 145 (.node 140 (.node 137 (.node 136 (.leaf (32748863472,261,10212440)) (.leaf (33822605296,262,12304922))) (.node 138 (.leaf (33285734384,262,12478032)) (.node 139 (.leaf (34359476208,263,14599697)) (.leaf (32748994544,261,10212552))))) (.node 142 (.node 141 (.leaf (33822736368,262,12305090)) (.leaf (32749125616,262,11789008))) (.node 143 (.leaf (33822867440,263,14139601)) (.node 144 (.leaf (33017430000,261,10213000)) (.leaf (33285865456,262,12478088)))))) (.node 150 (.node 147 (.node 146 (.leaf (33017561072,262,11789904)) (.leaf (33285996528,263,14055048))) (.node 148 (.leaf (25501237232,261,9925699)) (.node 149 (.leaf (34091171824,262,12305986)) (.leaf (25769672688,262,12219074))))) (.node 152 (.node 151 (.leaf (34359607280,263,14599809)) (.leaf (25501368304,262,11760154))) (.node 153 (.leaf (34091302896,263,14140945)) (.node 154 (.leaf (25769803760,263,14053585)) (.leaf (34359738352,265,16434824))))))))))

noncomputable def models (i : Fin 155) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 155) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 155) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 70, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (7 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 70, (7 : Fin 8) ∈ U i → ∃ j : Fin 35, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C36

/- Source: MatroidCatalogue/Cases/N8R4C36Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C36


noncomputable def certificates_0 : List (Origin 70 155 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.neg 2)]),
   ((.fixed 3),[(.neg 3)]),
   ((.fixed 4),[(.neg 4)]),
   ((.fixed 5),[(.neg 5)]),
   ((.fixed 6),[(.neg 6)]),
   ((.fixed 7),[(.neg 7)]),
   ((.fixed 8),[(.neg 8)]),
   ((.fixed 9),[(.pos 9)]),
   ((.fixed 10),[(.pos 10)]),
   ((.fixed 11),[(.pos 11)]),
   ((.fixed 12),[(.pos 12)]),
   ((.fixed 13),[(.pos 13)]),
   ((.fixed 14),[(.pos 14)]),
   ((.fixed 15),[(.neg 15)]),
   ((.fixed 16),[(.neg 16)]),
   ((.fixed 17),[(.neg 17)]),
   ((.fixed 18),[(.neg 18)]),
   ((.fixed 19),[(.pos 19)]),
   ((.fixed 20),[(.pos 20)]),
   ((.fixed 21),[(.pos 21)]),
   ((.fixed 22),[(.pos 22)]),
   ((.fixed 23),[(.pos 23)]),
   ((.fixed 24),[(.pos 24)]),
   ((.fixed 25),[(.pos 25)]),
   ((.fixed 26),[(.pos 26)]),
   ((.fixed 27),[(.pos 27)]),
   ((.fixed 28),[(.pos 28)]),
   ((.fixed 29),[(.pos 29)]),
   ((.fixed 30),[(.pos 30)]),
   ((.fixed 31),[(.pos 31)]),
   ((.fixed 32),[(.pos 32)]),
   ((.fixed 33),[(.pos 33)]),
   ((.fixed 34),[(.pos 34)]),
   ((.exchange 9 41 5),[(.neg 41),(.neg 9),(.pos 1),(.pos 39)]),
   ((.exchange 9 46 4),[(.neg 46),(.neg 9),(.pos 5),(.pos 45)]),
   ((.exchange 10 41 5),[(.neg 41),(.neg 10),(.pos 1),(.pos 40)]),
   ((.exchange 10 45 4),[(.neg 45),(.neg 10),(.pos 5),(.pos 46)]),
   ((.exchange 10 47 4),[(.neg 47),(.neg 10),(.pos 5),(.pos 46)]),
   ((.exchange 10 48 4),[(.neg 48),(.neg 10),(.pos 7),(.pos 46)]),
   ((.exchange 10 49 4),[(.neg 49),(.neg 10),(.pos 5),(.pos 7),(.pos 46)]),
   ((.exchange 10 50 4),[(.neg 50),(.neg 10),(.pos 7),(.pos 46)]),
   ((.exchange 11 39 5),[(.neg 39),(.neg 11),(.pos 1),(.pos 41)]),
   ((.exchange 11 40 5),[(.neg 40),(.neg 11),(.pos 1),(.pos 41)]),
   ((.exchange 11 42 5),[(.neg 42),(.neg 11),(.pos 1),(.pos 4),(.pos 41)]),
   ((.exchange 11 43 5),[(.neg 43),(.neg 11),(.pos 4),(.pos 41)]),
   ((.exchange 11 44 5),[(.neg 44),(.neg 11),(.pos 4),(.pos 41)]),
   ((.exchange 11 46 4),[(.neg 46),(.neg 11),(.pos 5),(.pos 47)]),
   ((.exchange 12 41 5),[(.neg 41),(.neg 12),(.pos 2),(.pos 3),(.pos 42)]),
   ((.exchange 12 46 4),[(.neg 46),(.neg 12),(.pos 7),(.pos 48)]),
   ((.exchange 13 41 5),[(.neg 41),(.neg 13),(.pos 4),(.pos 43)]),
   ((.exchange 13 46 4),[(.neg 46),(.neg 13),(.pos 6),(.pos 8),(.pos 49)]),
   ((.exchange 14 41 5),[(.neg 41),(.neg 14),(.pos 4),(.pos 44)]),
   ((.exchange 14 46 4),[(.neg 46),(.neg 14),(.pos 7),(.pos 50)]),
   ((.exchange 19 56 4),[(.neg 56),(.neg 19),(.pos 15),(.pos 55)]),
   ((.exchange 19 57 4),[(.neg 57),(.neg 19),(.pos 15),(.pos 55)]),
   ((.exchange 19 58 4),[(.neg 58),(.neg 19),(.pos 16),(.pos 55)]),
   ((.exchange 19 59 4),[(.neg 59),(.neg 19),(.pos 16),(.pos 55)]),
   ((.exchange 19 60 4),[(.neg 60),(.neg 19),(.pos 15),(.pos 16),(.pos 55)]),
   ((.exchange 20 55 4),[(.neg 55),(.neg 20),(.pos 15),(.pos 56)]),
   ((.exchange 21 55 4),[(.neg 55),(.neg 21),(.pos 15),(.pos 57)]),
   ((.exchange 22 55 4),[(.neg 55),(.neg 22),(.pos 16),(.pos 58)]),
   ((.exchange 23 55 4),[(.neg 55),(.neg 23),(.pos 16),(.pos 59)]),
   ((.exchange 24 55 4),[(.neg 55),(.neg 24),(.pos 17),(.pos 18),(.pos 60)]),
   ((.exchange 35 9 7),[(.neg 35),(.neg 9),(.pos 1),(.pos 5)]),
   ((.exchange 36 9 7),[(.neg 36),(.neg 9),(.pos 2),(.pos 6)]),
   ((.exchange 37 9 7),[(.neg 37),(.neg 9),(.pos 0),(.pos 3),(.pos 7)]),
   ((.exchange 38 9 7),[(.neg 38),(.neg 9),(.pos 0),(.pos 4),(.pos 8)]),
   ((.exchange 39 30 4),[(.neg 39),(.neg 30),(.pos 35),(.pos 36),(.pos 45),(.pos 55)]),
   ((.exchange 39 31 1),[(.neg 39),(.neg 31),(.pos 51),(.pos 61)]),
   ((.exchange 39 32 0),[(.neg 39),(.neg 32),(.pos 52),(.pos 62)]),
   ((.exchange 40 30 4),[(.neg 40),(.neg 30),(.pos 37),(.pos 46),(.pos 56)]),
   ((.exchange 40 33 0),[(.neg 40),(.neg 33),(.pos 53),(.pos 63)]),
   ((.exchange 41 30 4),[(.neg 41),(.neg 30),(.pos 38),(.pos 47),(.pos 57)]),
   ((.exchange 41 32 2),[(.neg 41),(.neg 32),(.pos 52),(.pos 62)]),
   ((.exchange 41 33 1),[(.neg 41),(.neg 33),(.pos 53),(.pos 63)]),
   ((.exchange 42 30 4),[(.neg 42),(.neg 30),(.pos 37),(.pos 48),(.pos 58)]),
   ((.exchange 42 34 0),[(.neg 42),(.neg 34),(.pos 54),(.pos 64)]),
   ((.exchange 42 65 3),[(.neg 65),(.neg 42),(.pos 51),(.pos 61)]),
   ((.exchange 42 69 3),[(.neg 69),(.neg 42),(.pos 51),(.pos 61)]),
   ((.exchange 43 30 4),[(.neg 43),(.neg 30),(.pos 38),(.pos 49),(.pos 59)]),
   ((.exchange 44 30 4),[(.neg 44),(.neg 30),(.pos 50),(.pos 60)]),
   ((.exchange 44 34 2),[(.neg 44),(.neg 34),(.pos 54),(.pos 64)]),
   ((.exchange 45 19 5),[(.neg 45),(.neg 19),(.pos 39),(.pos 55)]),
   ((.exchange 45 31 1),[(.neg 45),(.neg 31),(.pos 51),(.pos 65)]),
   ((.exchange 45 32 0),[(.neg 45),(.neg 32),(.pos 52),(.pos 66)]),
   ((.exchange 45 62 0),[(.neg 62),(.neg 45),(.pos 52),(.pos 66)]),
   ((.exchange 46 19 5),[(.neg 46),(.neg 19),(.pos 35),(.pos 40),(.pos 56)]),
   ((.exchange 46 31 2),[(.neg 46),(.neg 31),(.pos 51),(.pos 65)]),
   ((.exchange 46 33 0),[(.neg 46),(.neg 33),(.pos 53),(.pos 67)]),
   ((.exchange 46 63 0),[(.neg 63),(.neg 46),(.pos 53),(.pos 67)]),
   ((.exchange 47 19 5),[(.neg 47),(.neg 19),(.pos 35),(.pos 41),(.pos 57)]),
   ((.exchange 48 19 5),[(.neg 48),(.neg 19),(.pos 36),(.pos 42),(.pos 58)]),
   ((.exchange 48 31 3),[(.neg 48),(.neg 31),(.pos 51),(.pos 65)]),
   ((.exchange 48 34 0),[(.neg 48),(.neg 34),(.pos 54),(.pos 68)]),
   ((.exchange 48 69 3),[(.neg 69),(.neg 48),(.pos 51),(.pos 65)]),
   ((.exchange 49 19 5),[(.neg 49),(.neg 19),(.pos 36),(.pos 43),(.pos 59)]),
   ((.exchange 49 64 1),[(.neg 64),(.neg 49),(.pos 54),(.pos 68)]),
   ((.exchange 50 19 5),[(.neg 50),(.neg 19),(.pos 37),(.pos 38),(.pos 44),(.pos 60)]),
   ((.exchange 50 33 3),[(.neg 50),(.neg 33),(.pos 53),(.pos 67)]),
   ((.exchange 50 69 2),[(.neg 69),(.neg 50),(.pos 54),(.pos 68)]),
   ((.exchange 51 13 0),[(.neg 51),(.neg 13),(.pos 52),(.pos 54)]),
   ((.exchange 51 19 5),[(.neg 51),(.neg 19),(.pos 39),(.pos 61)]),
   ((.exchange 51 26 4),[(.neg 51),(.neg 26),(.pos 46),(.pos 65)]),
   ((.exchange 51 33 0),[(.neg 51),(.neg 33),(.pos 53),(.pos 69)]),
   ((.exchange 51 44 0),[(.neg 51),(.neg 44),(.pos 53),(.pos 54)]),
   ((.exchange 51 60 5),[(.neg 60),(.neg 51),(.pos 40),(.pos 42),(.pos 61)]),
   ((.exchange 51 63 0),[(.neg 63),(.neg 51),(.pos 53),(.pos 69)]),
   ((.exchange 51 64 0),[(.neg 64),(.neg 51),(.pos 54),(.pos 69)]),
   ((.exchange 51 66 4),[(.neg 66),(.neg 51),(.pos 45),(.pos 65)]),
   ((.exchange 52 10 1),[(.neg 52),(.neg 10),(.pos 51),(.pos 53)]),
   ((.exchange 52 12 1),[(.neg 52),(.neg 12),(.pos 51),(.pos 54)]),
   ((.exchange 52 14 1),[(.neg 52),(.neg 14),(.pos 53),(.pos 54)]),
   ((.exchange 52 19 5),[(.neg 52),(.neg 19),(.pos 39),(.pos 62)]),
   ((.exchange 52 25 4),[(.neg 52),(.neg 25),(.pos 45),(.pos 66)]),
   ((.exchange 52 31 1),[(.neg 52),(.neg 31),(.pos 51),(.pos 69)]),
   ((.exchange 52 33 1),[(.neg 52),(.neg 33),(.pos 53),(.pos 69)]),
   ((.exchange 52 40 1),[(.neg 52),(.neg 40),(.pos 51),(.pos 53)]),
   ((.exchange 52 46 1),[(.neg 52),(.neg 46),(.pos 51),(.pos 53)]),
   ((.exchange 52 48 1),[(.neg 52),(.neg 48),(.pos 51),(.pos 54)]),
   ((.exchange 52 58 4),[(.neg 58),(.neg 52),(.pos 45),(.pos 49),(.pos 66)]),
   ((.exchange 52 60 5),[(.neg 60),(.neg 52),(.pos 41),(.pos 43),(.pos 62)]),
   ((.exchange 52 63 1),[(.neg 63),(.neg 52),(.pos 53),(.pos 69)]),
   ((.exchange 52 64 1),[(.neg 64),(.neg 52),(.pos 54),(.pos 69)]),
   ((.exchange 52 65 1),[(.neg 65),(.neg 52),(.pos 51),(.pos 69)]),
   ((.exchange 53 9 2),[(.neg 53),(.neg 9),(.pos 51),(.pos 52)]),
   ((.exchange 53 24 5),[(.neg 53),(.neg 24),(.pos 44),(.pos 63)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_1 : List (Origin 70 155 × List Sat.Literal) :=
  [((.exchange 53 30 4),[(.neg 53),(.neg 30),(.pos 50),(.pos 67)]),
   ((.exchange 53 31 2),[(.neg 53),(.neg 31),(.pos 51),(.pos 69)]),
   ((.exchange 53 32 2),[(.neg 53),(.neg 32),(.pos 52),(.pos 69)]),
   ((.exchange 53 34 2),[(.neg 53),(.neg 34),(.pos 54),(.pos 69)]),
   ((.exchange 53 39 2),[(.neg 53),(.neg 39),(.pos 51),(.pos 52)]),
   ((.exchange 53 42 2),[(.neg 53),(.neg 42),(.pos 51),(.pos 54)]),
   ((.exchange 53 49 2),[(.neg 53),(.neg 49),(.pos 52),(.pos 54)]),
   ((.exchange 53 60 5),[(.neg 60),(.neg 53),(.pos 44),(.pos 63)]),
   ((.exchange 53 61 2),[(.neg 61),(.neg 53),(.pos 51),(.pos 69)]),
   ((.exchange 53 62 2),[(.neg 62),(.neg 53),(.pos 52),(.pos 69)]),
   ((.exchange 53 64 2),[(.neg 64),(.neg 53),(.pos 54),(.pos 69)]),
   ((.exchange 54 9 3),[(.neg 54),(.neg 9),(.pos 51),(.pos 52)]),
   ((.exchange 54 10 3),[(.neg 54),(.neg 10),(.pos 51),(.pos 53)]),
   ((.exchange 54 11 3),[(.neg 54),(.neg 11),(.pos 52),(.pos 53)]),
   ((.exchange 54 19 5),[(.neg 54),(.neg 19),(.pos 42),(.pos 43),(.pos 64)]),
   ((.exchange 54 22 5),[(.neg 54),(.neg 22),(.pos 42),(.pos 64)]),
   ((.exchange 54 25 4),[(.neg 54),(.neg 25),(.pos 48),(.pos 49),(.pos 68)]),
   ((.exchange 54 31 3),[(.neg 54),(.neg 31),(.pos 51),(.pos 69)]),
   ((.exchange 54 32 3),[(.neg 54),(.neg 32),(.pos 52),(.pos 69)]),
   ((.exchange 54 33 3),[(.neg 54),(.neg 33),(.pos 53),(.pos 69)]),
   ((.exchange 54 39 3),[(.neg 54),(.neg 39),(.pos 51),(.pos 52)]),
   ((.exchange 54 41 3),[(.neg 54),(.neg 41),(.pos 52),(.pos 53)]),
   ((.exchange 54 46 3),[(.neg 54),(.neg 46),(.pos 51),(.pos 53)]),
   ((.exchange 54 60 4),[(.neg 60),(.neg 54),(.pos 50),(.pos 68)]),
   ((.exchange 54 65 3),[(.neg 65),(.neg 54),(.pos 51),(.pos 69)]),
   ((.exchange 54 66 3),[(.neg 66),(.neg 54),(.pos 52),(.pos 69)]),
   ((.exchange 55 9 6),[(.neg 55),(.neg 9),(.pos 39),(.pos 45)]),
   ((.exchange 55 31 1),[(.neg 55),(.neg 31),(.pos 61),(.pos 65)]),
   ((.exchange 55 32 0),[(.neg 55),(.neg 32),(.pos 62),(.pos 66)]),
   ((.exchange 56 9 6),[(.neg 56),(.neg 9),(.pos 35),(.pos 40),(.pos 46)]),
   ((.exchange 56 33 0),[(.neg 56),(.neg 33),(.pos 63),(.pos 67)]),
   ((.exchange 56 69 2),[(.neg 69),(.neg 56),(.pos 61),(.pos 65)]),
   ((.exchange 57 9 6),[(.neg 57),(.neg 9),(.pos 35),(.pos 41),(.pos 47)]),
   ((.exchange 57 32 2),[(.neg 57),(.neg 32),(.pos 62),(.pos 66)]),
   ((.exchange 58 9 6),[(.neg 58),(.neg 9),(.pos 36),(.pos 42),(.pos 48)]),
   ((.exchange 58 34 0),[(.neg 58),(.neg 34),(.pos 64),(.pos 68)]),
   ((.exchange 58 69 3),[(.neg 69),(.neg 58),(.pos 61),(.pos 65)]),
   ((.exchange 59 9 6),[(.neg 59),(.neg 9),(.pos 36),(.pos 43),(.pos 49)]),
   ((.exchange 59 32 3),[(.neg 59),(.neg 32),(.pos 62),(.pos 66)]),
   ((.exchange 60 9 6),[(.neg 60),(.neg 9),(.pos 37),(.pos 38),(.pos 44),(.pos 50)]),
   ((.exchange 60 33 3),[(.neg 60),(.neg 33),(.pos 63),(.pos 67)]),
   ((.exchange 60 69 2),[(.neg 69),(.neg 60),(.pos 64),(.pos 68)]),
   ((.exchange 61 13 6),[(.neg 61),(.neg 13),(.pos 39),(.pos 42),(.pos 51)]),
   ((.exchange 61 14 0),[(.neg 61),(.neg 14),(.pos 63),(.pos 64),(.pos 69)]),
   ((.exchange 61 25 4),[(.neg 61),(.neg 25),(.pos 55),(.pos 65)]),
   ((.exchange 61 26 4),[(.neg 61),(.neg 26),(.pos 56),(.pos 65)]),
   ((.exchange 61 34 0),[(.neg 61),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 61 44 0),[(.neg 61),(.neg 44),(.pos 63),(.pos 64)]),
   ((.exchange 61 49 4),[(.neg 61),(.neg 49),(.pos 55),(.pos 58),(.pos 65)]),
   ((.exchange 61 50 4),[(.neg 61),(.neg 50),(.pos 56),(.pos 58),(.pos 65)]),
   ((.exchange 61 53 0),[(.neg 61),(.neg 53),(.pos 63),(.pos 69)]),
   ((.exchange 61 53 6),[(.neg 61),(.neg 53),(.pos 40),(.pos 51)]),
   ((.exchange 61 54 0),[(.neg 61),(.neg 54),(.pos 64),(.pos 69)]),
   ((.exchange 61 54 6),[(.neg 61),(.neg 54),(.pos 42),(.pos 51)]),
   ((.exchange 61 67 0),[(.neg 67),(.neg 61),(.pos 63),(.pos 69)]),
   ((.exchange 62 20 1),[(.neg 62),(.neg 20),(.pos 61),(.pos 63)]),
   ((.exchange 62 22 1),[(.neg 62),(.neg 22),(.pos 61),(.pos 64)]),
   ((.exchange 62 25 4),[(.neg 62),(.neg 25),(.pos 55),(.pos 66)]),
   ((.exchange 62 34 1),[(.neg 62),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 62 44 1),[(.neg 62),(.neg 44),(.pos 63),(.pos 64)]),
   ((.exchange 62 50 6),[(.neg 62),(.neg 50),(.pos 41),(.pos 43),(.pos 52)]),
   ((.exchange 62 53 1),[(.neg 62),(.neg 53),(.pos 63),(.pos 69)]),
   ((.exchange 62 53 6),[(.neg 62),(.neg 53),(.pos 41),(.pos 52)]),
   ((.exchange 62 60 1),[(.neg 62),(.neg 60),(.pos 63),(.pos 64)]),
   ((.exchange 62 67 1),[(.neg 67),(.neg 62),(.pos 63),(.pos 69)]),
   ((.exchange 63 9 6),[(.neg 63),(.neg 9),(.pos 40),(.pos 41),(.pos 53)]),
   ((.exchange 63 19 2),[(.neg 63),(.neg 19),(.pos 61),(.pos 62)]),
   ((.exchange 63 25 4),[(.neg 63),(.neg 25),(.pos 56),(.pos 57),(.pos 67)]),
   ((.exchange 63 30 4),[(.neg 63),(.neg 30),(.pos 60),(.pos 67)]),
   ((.exchange 63 31 2),[(.neg 63),(.neg 31),(.pos 61),(.pos 69)]),
   ((.exchange 63 32 2),[(.neg 63),(.neg 32),(.pos 62),(.pos 69)]),
   ((.exchange 63 34 2),[(.neg 63),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 63 39 2),[(.neg 63),(.neg 39),(.pos 61),(.pos 62)]),
   ((.exchange 63 42 2),[(.neg 63),(.neg 42),(.pos 61),(.pos 64)]),
   ((.exchange 63 43 2),[(.neg 63),(.neg 43),(.pos 62),(.pos 64)]),
   ((.exchange 63 45 6),[(.neg 63),(.neg 45),(.pos 40),(.pos 41),(.pos 53)]),
   ((.exchange 63 59 2),[(.neg 63),(.neg 59),(.pos 62),(.pos 64)]),
   ((.exchange 64 9 6),[(.neg 64),(.neg 9),(.pos 42),(.pos 43),(.pos 54)]),
   ((.exchange 64 20 3),[(.neg 64),(.neg 20),(.pos 61),(.pos 63)]),
   ((.exchange 64 21 3),[(.neg 64),(.neg 21),(.pos 62),(.pos 63)]),
   ((.exchange 64 25 4),[(.neg 64),(.neg 25),(.pos 58),(.pos 59),(.pos 68)]),
   ((.exchange 64 31 3),[(.neg 64),(.neg 31),(.pos 61),(.pos 69)]),
   ((.exchange 64 32 3),[(.neg 64),(.neg 32),(.pos 62),(.pos 69)]),
   ((.exchange 64 33 3),[(.neg 64),(.neg 33),(.pos 63),(.pos 69)]),
   ((.exchange 64 39 3),[(.neg 64),(.neg 39),(.pos 61),(.pos 62)]),
   ((.exchange 64 40 3),[(.neg 64),(.neg 40),(.pos 61),(.pos 63)]),
   ((.exchange 64 41 3),[(.neg 64),(.neg 41),(.pos 62),(.pos 63)]),
   ((.exchange 64 46 4),[(.neg 64),(.neg 46),(.pos 58),(.pos 60),(.pos 68)]),
   ((.exchange 64 52 3),[(.neg 64),(.neg 52),(.pos 62),(.pos 69)]),
   ((.exchange 64 53 6),[(.neg 64),(.neg 53),(.pos 44),(.pos 54)]),
   ((.exchange 64 66 4),[(.neg 66),(.neg 64),(.pos 59),(.pos 68)]),
   ((.exchange 64 67 3),[(.neg 67),(.neg 64),(.pos 63),(.pos 69)]),
   ((.exchange 65 9 6),[(.neg 65),(.neg 9),(.pos 45),(.pos 51)]),
   ((.exchange 65 19 5),[(.neg 65),(.neg 19),(.pos 55),(.pos 61)]),
   ((.exchange 65 22 5),[(.neg 65),(.neg 22),(.pos 58),(.pos 61)]),
   ((.exchange 65 29 0),[(.neg 65),(.neg 29),(.pos 66),(.pos 68)]),
   ((.exchange 65 32 0),[(.neg 65),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 65 33 0),[(.neg 65),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 65 44 0),[(.neg 65),(.neg 44),(.pos 67),(.pos 68),(.pos 69)]),
   ((.exchange 65 44 6),[(.neg 65),(.neg 44),(.pos 46),(.pos 48),(.pos 51)]),
   ((.exchange 65 52 6),[(.neg 65),(.neg 52),(.pos 45),(.pos 51)]),
   ((.exchange 65 53 0),[(.neg 65),(.neg 53),(.pos 67),(.pos 69)]),
   ((.exchange 65 57 0),[(.neg 65),(.neg 57),(.pos 66),(.pos 67)]),
   ((.exchange 65 60 0),[(.neg 65),(.neg 60),(.pos 67),(.pos 68)]),
   ((.exchange 65 64 0),[(.neg 65),(.neg 64),(.pos 68),(.pos 69)]),
   ((.exchange 66 9 6),[(.neg 66),(.neg 9),(.pos 45),(.pos 52)]),
   ((.exchange 66 26 1),[(.neg 66),(.neg 26),(.pos 65),(.pos 67)]),
   ((.exchange 66 31 1),[(.neg 66),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 66 33 1),[(.neg 66),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 66 34 1),[(.neg 66),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 66 41 5),[(.neg 66),(.neg 41),(.pos 57),(.pos 62)]),
   ((.exchange 66 41 6),[(.neg 66),(.neg 41),(.pos 47),(.pos 52)]),
   ((.exchange 66 44 1),[(.neg 66),(.neg 44),(.pos 67),(.pos 68),(.pos 69)]),
   ((.exchange 66 46 1),[(.neg 66),(.neg 46),(.pos 65),(.pos 67)]),
   ((.exchange 66 58 1),[(.neg 66),(.neg 58),(.pos 65),(.pos 68)]),
   ((.exchange 66 60 1),[(.neg 66),(.neg 60),(.pos 67),(.pos 68)]),
   ((.exchange 66 63 5),[(.neg 66),(.neg 63),(.pos 57),(.pos 62)]),
   ((.exchange 66 64 5),[(.neg 66),(.neg 64),(.pos 59),(.pos 62)]),
   ((.exchange 67 14 6),[(.neg 67),(.neg 14),(.pos 50),(.pos 53)]),
   ((.exchange 67 24 5),[(.neg 67),(.neg 24),(.pos 60),(.pos 63)]),
   ((.exchange 67 28 2),[(.neg 67),(.neg 28),(.pos 65),(.pos 68)]),
   ((.exchange 67 31 2),[(.neg 67),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 67 32 2),[(.neg 67),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 67 34 2),[(.neg 67),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 67 39 5),[(.neg 67),(.neg 39),(.pos 56),(.pos 57),(.pos 63)]),
   ((.exchange 67 45 2),[(.neg 67),(.neg 45),(.pos 65),(.pos 66)]),
   ((.exchange 67 48 2),[(.neg 67),(.neg 48),(.pos 65),(.pos 68)]),
   ((.exchange 67 49 2),[(.neg 67),(.neg 49),(.pos 66),(.pos 68)])]

theorem certificates_1_valid : ∀ oc ∈ certificates_1,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_2 : List (Origin 70 155 × List Sat.Literal) :=
  [((.exchange 67 51 2),[(.neg 67),(.neg 51),(.pos 65),(.pos 69)]),
   ((.exchange 67 59 2),[(.neg 67),(.neg 59),(.pos 66),(.pos 68)]),
   ((.exchange 67 61 2),[(.neg 67),(.neg 61),(.pos 65),(.pos 69)]),
   ((.exchange 68 9 6),[(.neg 68),(.neg 9),(.pos 48),(.pos 49),(.pos 54)]),
   ((.exchange 68 14 6),[(.neg 68),(.neg 14),(.pos 50),(.pos 54)]),
   ((.exchange 68 19 5),[(.neg 68),(.neg 19),(.pos 58),(.pos 59),(.pos 64)]),
   ((.exchange 68 25 3),[(.neg 68),(.neg 25),(.pos 65),(.pos 66)]),
   ((.exchange 68 26 3),[(.neg 68),(.neg 26),(.pos 65),(.pos 67)]),
   ((.exchange 68 27 3),[(.neg 68),(.neg 27),(.pos 66),(.pos 67)]),
   ((.exchange 68 31 3),[(.neg 68),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 68 32 3),[(.neg 68),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 68 33 3),[(.neg 68),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 68 44 5),[(.neg 68),(.neg 44),(.pos 60),(.pos 64)]),
   ((.exchange 68 52 3),[(.neg 68),(.neg 52),(.pos 66),(.pos 69)]),
   ((.exchange 68 53 3),[(.neg 68),(.neg 53),(.pos 67),(.pos 69)]),
   ((.exchange 68 55 3),[(.neg 68),(.neg 55),(.pos 65),(.pos 66)]),
   ((.exchange 68 56 3),[(.neg 68),(.neg 56),(.pos 65),(.pos 67)]),
   ((.exchange 68 57 3),[(.neg 68),(.neg 57),(.pos 66),(.pos 67)]),
   ((.exchange 68 63 5),[(.neg 68),(.neg 63),(.pos 60),(.pos 64)]),
   ((.exchange 69 10 6),[(.neg 69),(.neg 10),(.pos 51),(.pos 53)]),
   ((.exchange 69 11 6),[(.neg 69),(.neg 11),(.pos 52),(.pos 53)]),
   ((.exchange 69 13 6),[(.neg 69),(.neg 13),(.pos 52),(.pos 54)]),
   ((.exchange 69 14 6),[(.neg 69),(.neg 14),(.pos 53),(.pos 54)]),
   ((.exchange 69 20 5),[(.neg 69),(.neg 20),(.pos 61),(.pos 63)]),
   ((.exchange 69 21 5),[(.neg 69),(.neg 21),(.pos 62),(.pos 63)]),
   ((.exchange 69 22 5),[(.neg 69),(.neg 22),(.pos 61),(.pos 64)]),
   ((.exchange 69 23 5),[(.neg 69),(.neg 23),(.pos 62),(.pos 64)]),
   ((.exchange 69 24 5),[(.neg 69),(.neg 24),(.pos 63),(.pos 64)]),
   ((.exchange 69 25 4),[(.neg 69),(.neg 25),(.pos 65),(.pos 66)]),
   ((.exchange 69 28 4),[(.neg 69),(.neg 28),(.pos 65),(.pos 68)]),
   ((.exchange 69 29 4),[(.neg 69),(.neg 29),(.pos 66),(.pos 68)]),
   ((.exchange 69 39 5),[(.neg 69),(.neg 39),(.pos 61),(.pos 62)]),
   ((.exchange 69 39 6),[(.neg 69),(.neg 39),(.pos 51),(.pos 52)]),
   ((.exchange 69 40 5),[(.neg 69),(.neg 40),(.pos 61),(.pos 63)]),
   ((.exchange 69 41 5),[(.neg 69),(.neg 41),(.pos 62),(.pos 63)]),
   ((.exchange 69 42 5),[(.neg 69),(.neg 42),(.pos 61),(.pos 64)]),
   ((.exchange 69 42 6),[(.neg 69),(.neg 42),(.pos 51),(.pos 54)]),
   ((.exchange 69 44 5),[(.neg 69),(.neg 44),(.pos 63),(.pos 64)]),
   ((.exchange 69 44 6),[(.neg 69),(.neg 44),(.pos 53),(.pos 54)]),
   ((.exchange 69 46 6),[(.neg 69),(.neg 46),(.pos 51),(.pos 53)]),
   ((.exchange 69 50 4),[(.neg 69),(.neg 50),(.pos 67),(.pos 68)]),
   ((.exchange 69 50 6),[(.neg 69),(.neg 50),(.pos 53),(.pos 54)]),
   ((.exchange 69 55 5),[(.neg 69),(.neg 55),(.pos 61),(.pos 62)]),
   ((.exchange 69 56 4),[(.neg 69),(.neg 56),(.pos 65),(.pos 67)]),
   ((.exchange 69 57 4),[(.neg 69),(.neg 57),(.pos 66),(.pos 67)]),
   ((.exchange 69 58 4),[(.neg 69),(.neg 58),(.pos 65),(.pos 68)]),
   ((.exchange 69 58 5),[(.neg 69),(.neg 58),(.pos 61),(.pos 64)]),
   ((.exchange 69 59 4),[(.neg 69),(.neg 59),(.pos 66),(.pos 68)]),
   ((.exchange 69 60 4),[(.neg 69),(.neg 60),(.pos 67),(.pos 68)]),
   ((.exchange 69 60 5),[(.neg 69),(.neg 60),(.pos 63),(.pos 64)]),
   (.newPoint,[(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 0),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 69)]),
   ((.excluded 1),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 54),(.neg 53),(.neg 52),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 65)]),
   ((.excluded 2),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 54),(.neg 53),(.neg 51),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 62),(.pos 66)]),
   ((.excluded 3),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 54),(.neg 52),(.neg 51),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 4),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 53),(.neg 52),(.neg 51),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 68)]),
   ((.excluded 5),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60)]),
   ((.excluded 6),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 7),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 8),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 69)]),
   ((.excluded 9),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 51),(.pos 61),(.pos 66)]),
   ((.excluded 10),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 51),(.pos 61),(.pos 67)]),
   ((.excluded 11),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 51),(.pos 61),(.pos 68)]),
   ((.excluded 12),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 51),(.pos 61)]),
   ((.excluded 13),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 52),(.pos 62),(.pos 65)]),
   ((.excluded 14),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 52),(.pos 62),(.pos 67)]),
   ((.excluded 15),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 52),(.pos 62),(.pos 68)]),
   ((.excluded 16),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 52),(.pos 62)]),
   ((.excluded 17),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 53),(.pos 63),(.pos 65)]),
   ((.excluded 18),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 53),(.pos 63),(.pos 66)]),
   ((.excluded 19),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 53),(.pos 63),(.pos 68)]),
   ((.excluded 20),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 53),(.pos 63)]),
   ((.excluded 21),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 54),(.pos 64),(.pos 65)]),
   ((.excluded 22),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 54),(.pos 64),(.pos 66)]),
   ((.excluded 23),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 54),(.pos 64),(.pos 67)]),
   ((.excluded 24),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 54),(.pos 64)]),
   ((.excluded 25),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 65)]),
   ((.excluded 26),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 66)]),
   ((.excluded 27),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 67)]),
   ((.excluded 28),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 68)]),
   ((.excluded 29),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44)]),
   ((.excluded 30),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 31),[(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 32),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 33),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 34),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 69)]),
   ((.excluded 35),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 36),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 69)]),
   ((.excluded 37),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 69)]),
   ((.excluded 38),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 69)]),
   ((.excluded 39),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 69)]),
   ((.excluded 40),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 62),(.pos 65)]),
   ((.excluded 41),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 63),(.pos 65)]),
   ((.excluded 42),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 64),(.pos 65)]),
   ((.excluded 43),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 65)]),
   ((.excluded 44),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 52),(.pos 61),(.pos 66)]),
   ((.excluded 45),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 52),(.pos 63),(.pos 66)]),
   ((.excluded 46),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 52),(.pos 64),(.pos 66)]),
   ((.excluded 47),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 52),(.pos 66)]),
   ((.excluded 48),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 53),(.pos 61),(.pos 67)]),
   ((.excluded 49),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 53),(.pos 62),(.pos 67)]),
   ((.excluded 50),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 53),(.pos 64),(.pos 67)]),
   ((.excluded 51),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 53),(.pos 67)]),
   ((.excluded 52),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 54),(.pos 61),(.pos 68)]),
   ((.excluded 53),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 54),(.pos 62),(.pos 68)]),
   ((.excluded 54),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 54),(.pos 63),(.pos 68)]),
   ((.excluded 55),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 54),(.pos 68)]),
   ((.excluded 56),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 61)]),
   ((.excluded 57),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 62)]),
   ((.excluded 58),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 63)]),
   ((.excluded 59),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 64)]),
   ((.excluded 60),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50)]),
   ((.excluded 61),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 65)]),
   ((.excluded 62),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 65)]),
   ((.excluded 63),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 65)]),
   ((.excluded 64),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 65)]),
   ((.excluded 65),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 51),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 62),(.pos 66)]),
   ((.excluded 66),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 62),(.pos 66)]),
   ((.excluded 67),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 62),(.pos 66)]),
   ((.excluded 68),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 62),(.pos 66)]),
   ((.excluded 69),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 51),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 70),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 71),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 72),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 73),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 51),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 68)]),
   ((.excluded 74),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 68)]),
   ((.excluded 75),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 68)]),
   ((.excluded 76),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 68)])]

theorem certificates_2_valid : ∀ oc ∈ certificates_2,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_3 : List (Origin 70 155 × List Sat.Literal) :=
  [((.excluded 77),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 51),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60)]),
   ((.excluded 78),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60)]),
   ((.excluded 79),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60)]),
   ((.excluded 80),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60)]),
   ((.excluded 81),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60)]),
   ((.excluded 82),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 51),(.pos 62),(.pos 67)]),
   ((.excluded 83),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 51),(.pos 62),(.pos 68)]),
   ((.excluded 84),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 51),(.pos 62)]),
   ((.excluded 85),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 51),(.pos 64),(.pos 67)]),
   ((.excluded 86),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 51),(.pos 67)]),
   ((.excluded 87),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 51),(.pos 64),(.pos 66)]),
   ((.excluded 88),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 51),(.pos 64)]),
   ((.excluded 89),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 51),(.pos 63),(.pos 66)]),
   ((.excluded 90),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 51),(.pos 66)]),
   ((.excluded 91),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 51),(.pos 63),(.pos 68)]),
   ((.excluded 92),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 51),(.pos 63)]),
   ((.excluded 93),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 51),(.pos 68)]),
   ((.excluded 94),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 51)]),
   ((.excluded 95),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 54),(.pos 62),(.pos 67)]),
   ((.excluded 96),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 62),(.pos 67)]),
   ((.excluded 97),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 54),(.pos 62),(.pos 65)]),
   ((.excluded 98),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 54),(.pos 62)]),
   ((.excluded 99),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 53),(.pos 62),(.pos 65)]),
   ((.excluded 100),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 62),(.pos 65)]),
   ((.excluded 101),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 53),(.pos 62),(.pos 68)]),
   ((.excluded 102),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 53),(.pos 62)]),
   ((.excluded 103),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 62),(.pos 68)]),
   ((.excluded 104),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 62)]),
   ((.excluded 105),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 54),(.pos 61),(.pos 67)]),
   ((.excluded 106),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 54),(.pos 67)]),
   ((.excluded 107),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 52),(.pos 61),(.pos 67)]),
   ((.excluded 108),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 61),(.pos 67)]),
   ((.excluded 109),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 52),(.pos 64),(.pos 67)]),
   ((.excluded 110),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 52),(.pos 67)]),
   ((.excluded 111),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 64),(.pos 67)]),
   ((.excluded 112),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 67)]),
   ((.excluded 113),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 54),(.pos 61),(.pos 66)]),
   ((.excluded 114),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 54),(.pos 61)]),
   ((.excluded 115),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 54),(.pos 63),(.pos 65)]),
   ((.excluded 116),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 54),(.pos 65)]),
   ((.excluded 117),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 54),(.pos 63),(.pos 66)]),
   ((.excluded 118),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 54),(.pos 63)]),
   ((.excluded 119),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 54),(.pos 66)]),
   ((.excluded 120),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 54)]),
   ((.excluded 121),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 52),(.pos 61),(.pos 68)]),
   ((.excluded 122),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 52),(.pos 61)]),
   ((.excluded 123),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 53),(.pos 61),(.pos 66)]),
   ((.excluded 124),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 61),(.pos 66)]),
   ((.excluded 125),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 53),(.pos 61),(.pos 68)]),
   ((.excluded 126),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 53),(.pos 61)]),
   ((.excluded 127),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 61),(.pos 68)]),
   ((.excluded 128),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 61)]),
   ((.excluded 129),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 63),(.pos 66)]),
   ((.excluded 130),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 53),(.pos 64),(.pos 66)]),
   ((.excluded 131),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 53),(.pos 66)]),
   ((.excluded 132),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 64),(.pos 66)]),
   ((.excluded 133),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 66)]),
   ((.excluded 134),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 53),(.pos 68)]),
   ((.excluded 135),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 53),(.pos 64),(.pos 65)]),
   ((.excluded 136),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 53),(.pos 64)]),
   ((.excluded 137),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 53),(.pos 65)]),
   ((.excluded 138),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 53)]),
   ((.excluded 139),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 52),(.pos 64),(.pos 65)]),
   ((.excluded 140),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 52),(.pos 64)]),
   ((.excluded 141),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 64),(.pos 65)]),
   ((.excluded 142),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 64)]),
   ((.excluded 143),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 52),(.pos 63),(.pos 65)]),
   ((.excluded 144),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 52),(.pos 65)]),
   ((.excluded 145),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 63),(.pos 65)]),
   ((.excluded 146),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 65)]),
   ((.excluded 147),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 52),(.pos 63),(.pos 68)]),
   ((.excluded 148),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 52),(.pos 63)]),
   ((.excluded 149),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 52),(.pos 68)]),
   ((.excluded 150),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 52)]),
   ((.excluded 151),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 63),(.pos 68)]),
   ((.excluded 152),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 63)]),
   ((.excluded 153),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 68)]),
   ((.excluded 154),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38)])]

theorem certificates_3_valid : ∀ oc ∈ certificates_3,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



theorem witness_0 : ∀ j : Fin 128,
    let w : Fin 155 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 128,
      let w : Fin 155 := ⟨0 + j.val,by omega⟩
      target w < MatroidCatalogue.count 8 4 ∧
        Papers.RationalityTen.MatroidChecked.FastSemanticChecks.RawWitness 8 (N7R4.familyMasks.get 36)
        (fun i : Fin 70 => N8R4.gridMasks.get i.val) newIndex (models w)
        (N8R4.familyMasks.get (target w)) (permutation w) := by
    refine (Fin.forall_fin_add (m := 64) (n := 64) _).2 ⟨?_, ?_⟩
    · refine (Fin.forall_fin_add (m := 32) (n := 32) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 16) (n := 16) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
      · refine (Fin.forall_fin_add (m := 16) (n := 16) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
    · refine (Fin.forall_fin_add (m := 32) (n := 32) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 16) (n := 16) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
      · refine (Fin.forall_fin_add (m := 16) (n := 16) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
  intro j
  have hj := hfast j
  exact ⟨hj.1,Papers.RationalityTen.MatroidChecked.FastSemanticChecks.rawWitness_sound 8 _ _ _ _ _ _ hj.2⟩



theorem witness_1 : ∀ j : Fin 27,
    let w : Fin 155 := ⟨128 + j.val,by omega⟩
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 27,
      let w : Fin 155 := ⟨128 + j.val,by omega⟩
      target w < MatroidCatalogue.count 8 4 ∧
        Papers.RationalityTen.MatroidChecked.FastSemanticChecks.RawWitness 8 (N7R4.familyMasks.get 36)
        (fun i : Fin 70 => N8R4.gridMasks.get i.val) newIndex (models w)
        (N8R4.familyMasks.get (target w)) (permutation w) := by
    refine (Fin.forall_fin_add (m := 13) (n := 14) _).2 ⟨?_, ?_⟩
    · refine (Fin.forall_fin_add (m := 6) (n := 7) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 3) (n := 3) _).2 ⟨?_, ?_⟩
        · decide +kernel
        · decide +kernel
      · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
        · decide +kernel
        · decide +kernel
    · refine (Fin.forall_fin_add (m := 7) (n := 7) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
        · decide +kernel
        · decide +kernel
      · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
        · decide +kernel
        · decide +kernel
  intro j
  have hj := hfast j
  exact ⟨hj.1,Papers.RationalityTen.MatroidChecked.FastSemanticChecks.rawWitness_sound 8 _ _ _ _ _ _ hj.2⟩


end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C36

/- Source: MatroidCatalogue/Cases/N8R4C36Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C36

noncomputable def certificates : List (Origin 70 155 × List Sat.Literal) :=
  certificates_0 ++ certificates_1 ++ certificates_2 ++ certificates_3

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  intro oc hoc
  simp only [certificates,List.mem_append,or_assoc] at hoc
  rcases hoc with h0 | h1 | h2 | h3
  · exact certificates_0_valid oc h0
  · exact certificates_1_valid oc h1
  · exact certificates_2_valid oc h2
  · exact certificates_3_valid oc h3

theorem models_valid : ∀ w : Fin 155,
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  by_cases h0 : w.val < 128
  ·
    have hh := witness_0 ⟨w.val - 0,by omega⟩
    have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 155) = w := Fin.ext (by dsimp only; omega)
    dsimp only at hh
    rw [heq] at hh
    exact hh
  ·
    have hh := witness_1 ⟨w.val - 128,by omega⟩
    have heq : (⟨128 + (w.val - 128),by omega⟩ : Fin 155) = w := Fin.ext (by dsimp only; omega)
    dsimp only at hh
    rw [heq] at hh
    exact hh

theorem coverage (M : BasisFamily (groundPrefix 8) 4)
    (hold : M.bases.filter ((7 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 8 4, IsomorphicWithin 8 M.bases B := by
  apply extension_covered_of_certificate (n:=7) (r:=4) (by decide)
    catalogue old U newIndex models certificates
    N8R4.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C36.formula []
    exact Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C36.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 8 4 (target w),family_mem 8 4 (target w) hw.1,?_⟩
    exact validWitness_sound 8 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C36


end
end
end BundlePart0

section BundlePart1
/- Source: MatroidChecked/SemanticChunks/Cases05Part02.lean -/




@[expose] public section
noncomputable section

/- Source: MatroidCatalogue/Cases/N8R4C37Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C37

abbrev U := N8R4.grid
noncomputable def old : Finset (Finset (Fin 8)) := N7R4.family 37
noncomputable def newIndexTree : Table ℕ := (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf 35) (.leaf 36)) (.node 3 (.leaf 37) (.leaf 38))) (.node 6 (.node 5 (.leaf 39) (.leaf 40)) (.node 7 (.leaf 41) (.leaf 42)))) (.node 12 (.node 10 (.node 9 (.leaf 43) (.leaf 44)) (.node 11 (.leaf 45) (.leaf 46))) (.node 14 (.node 13 (.leaf 47) (.leaf 48)) (.node 15 (.leaf 49) (.node 16 (.leaf 50) (.leaf 51)))))) (.node 26 (.node 21 (.node 19 (.node 18 (.leaf 52) (.leaf 53)) (.node 20 (.leaf 54) (.leaf 55))) (.node 23 (.node 22 (.leaf 56) (.leaf 57)) (.node 24 (.leaf 58) (.node 25 (.leaf 59) (.leaf 60))))) (.node 30 (.node 28 (.node 27 (.leaf 61) (.leaf 62)) (.node 29 (.leaf 63) (.leaf 64))) (.node 32 (.node 31 (.leaf 65) (.leaf 66)) (.node 33 (.leaf 67) (.node 34 (.leaf 68) (.leaf 69)))))))
noncomputable def newIndex (i : Fin 35) : Fin 70 := Fin.ofNat 70 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 14 (.node 7 (.node 3 (.node 1 (.leaf (3422577024,103,3663898)) (.node 2 (.leaf (3422754912,104,3661987)) (.leaf (227808,104,2353827)))) (.node 5 (.node 4 (.leaf (3422779872,142,7070252)) (.leaf (3252707340,104,4099235))) (.node 6 (.leaf (232784268,104,3955875)) (.leaf (3454034316,142,8199212))))) (.node 10 (.node 8 (.leaf (233011308,181,8345736)) (.node 9 (.leaf (3454236780,188,12526115)) (.leaf (233011692,188,11074595)))) (.node 12 (.node 11 (.leaf (3252885996,181,8317064)) (.leaf (3454212588,188,12411427))) (.node 13 (.leaf (3252910572,188,11246627)) (.leaf (3454237164,199,16434705)))))) (.node 21 (.node 17 (.node 15 (.leaf (30870635008,91,5761224)) (.node 16 (.leaf (34293212032,123,7858312)) (.leaf (34123342348,126,10398920)))) (.node 19 (.node 18 (.leaf (31103419276,126,10312904)) (.leaf (34324669324,163,12467336))) (.node 20 (.leaf (34293389920,126,9954504)) (.leaf (30870862816,126,9169608))))) (.node 25 (.node 23 (.node 22 (.leaf (34293414880,163,11789960)) (.leaf (31103646316,266,16406152))) (.node 24 (.leaf (34324871788,267,16434824)) (.leaf (31103646700,267,15854216)))) (.node 27 (.node 26 (.leaf (34123521004,266,16434824)) (.leaf (34324847596,267,16406152))) (.node 28 (.leaf (34123545580,267,15940232)) (.leaf (34324872172,268,16434824)))))))

noncomputable def models (i : Fin 29) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 29) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 29) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 70, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (7 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 70, (7 : Fin 8) ∈ U i → ∃ j : Fin 35, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C37

/- Source: MatroidCatalogue/Cases/N8R4C37Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C37


noncomputable def certificates_0 : List (Origin 70 29 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.neg 2)]),
   ((.fixed 3),[(.pos 3)]),
   ((.fixed 4),[(.pos 4)]),
   ((.fixed 5),[(.neg 5)]),
   ((.fixed 6),[(.neg 6)]),
   ((.fixed 7),[(.pos 7)]),
   ((.fixed 8),[(.pos 8)]),
   ((.fixed 9),[(.neg 9)]),
   ((.fixed 10),[(.neg 10)]),
   ((.fixed 11),[(.neg 11)]),
   ((.fixed 12),[(.pos 12)]),
   ((.fixed 13),[(.pos 13)]),
   ((.fixed 14),[(.neg 14)]),
   ((.fixed 15),[(.neg 15)]),
   ((.fixed 16),[(.neg 16)]),
   ((.fixed 17),[(.neg 17)]),
   ((.fixed 18),[(.neg 18)]),
   ((.fixed 19),[(.neg 19)]),
   ((.fixed 20),[(.pos 20)]),
   ((.fixed 21),[(.pos 21)]),
   ((.fixed 22),[(.pos 22)]),
   ((.fixed 23),[(.pos 23)]),
   ((.fixed 24),[(.neg 24)]),
   ((.fixed 25),[(.neg 25)]),
   ((.fixed 26),[(.pos 26)]),
   ((.fixed 27),[(.pos 27)]),
   ((.fixed 28),[(.pos 28)]),
   ((.fixed 29),[(.pos 29)]),
   ((.fixed 30),[(.neg 30)]),
   ((.fixed 31),[(.pos 31)]),
   ((.fixed 33),[(.neg 33)]),
   ((.fixed 34),[(.neg 34)]),
   ((.exchange 3 41 3),[(.neg 41),(.neg 3),(.pos 1),(.pos 40)]),
   ((.exchange 3 43 2),[(.neg 43),(.neg 3),(.pos 2),(.pos 42)]),
   ((.exchange 3 46 3),[(.neg 46),(.neg 3),(.pos 10),(.pos 40)]),
   ((.exchange 3 50 0),[(.neg 50),(.neg 3),(.pos 14),(.pos 44)]),
   ((.exchange 3 56 4),[(.neg 56),(.neg 3),(.pos 17),(.pos 37)]),
   ((.exchange 3 64 0),[(.neg 64),(.neg 3),(.pos 24),(.pos 44)]),
   ((.exchange 3 67 0),[(.neg 67),(.neg 3),(.pos 14),(.pos 24),(.pos 44)]),
   ((.exchange 3 68 0),[(.neg 68),(.neg 3),(.pos 14),(.pos 24),(.pos 44)]),
   ((.exchange 3 69 0),[(.neg 69),(.neg 3),(.pos 14),(.pos 24),(.pos 44)]),
   ((.exchange 4 40 3),[(.neg 40),(.neg 4),(.pos 1),(.pos 41)]),
   ((.exchange 4 42 2),[(.neg 42),(.neg 4),(.pos 2),(.pos 43)]),
   ((.exchange 4 46 3),[(.neg 46),(.neg 4),(.pos 1),(.pos 11),(.pos 41)]),
   ((.exchange 4 47 3),[(.neg 47),(.neg 4),(.pos 11),(.pos 41)]),
   ((.exchange 4 51 3),[(.neg 51),(.neg 4),(.pos 1),(.pos 11),(.pos 41)]),
   ((.exchange 4 52 3),[(.neg 52),(.neg 4),(.pos 11),(.pos 41)]),
   ((.exchange 4 56 4),[(.neg 56),(.neg 4),(.pos 0),(.pos 18),(.pos 38)]),
   ((.exchange 7 40 3),[(.neg 40),(.neg 7),(.pos 10),(.pos 46)]),
   ((.exchange 7 41 3),[(.neg 41),(.neg 7),(.pos 5),(.pos 10),(.pos 46)]),
   ((.exchange 7 44 0),[(.neg 44),(.neg 7),(.pos 14),(.pos 50)]),
   ((.exchange 7 47 3),[(.neg 47),(.neg 7),(.pos 5),(.pos 46)]),
   ((.exchange 7 49 2),[(.neg 49),(.neg 7),(.pos 6),(.pos 48)]),
   ((.exchange 7 51 3),[(.neg 51),(.neg 7),(.pos 10),(.pos 46)]),
   ((.exchange 7 52 3),[(.neg 52),(.neg 7),(.pos 5),(.pos 10),(.pos 46)]),
   ((.exchange 7 54 0),[(.neg 54),(.neg 7),(.pos 14),(.pos 50)]),
   ((.exchange 7 63 0),[(.neg 63),(.neg 7),(.pos 14),(.pos 30),(.pos 50)]),
   ((.exchange 7 64 0),[(.neg 64),(.neg 7),(.pos 14),(.pos 30),(.pos 50)]),
   ((.exchange 7 67 0),[(.neg 67),(.neg 7),(.pos 30),(.pos 50)]),
   ((.exchange 7 68 0),[(.neg 68),(.neg 7),(.pos 30),(.pos 50)]),
   ((.exchange 7 69 0),[(.neg 69),(.neg 7),(.pos 14),(.pos 30),(.pos 50)]),
   ((.exchange 8 41 3),[(.neg 41),(.neg 8),(.pos 11),(.pos 47)]),
   ((.exchange 8 46 3),[(.neg 46),(.neg 8),(.pos 5),(.pos 47)]),
   ((.exchange 8 48 2),[(.neg 48),(.neg 8),(.pos 6),(.pos 49)]),
   ((.exchange 12 41 3),[(.neg 41),(.neg 12),(.pos 9),(.pos 10),(.pos 51)]),
   ((.exchange 12 46 3),[(.neg 46),(.neg 12),(.pos 10),(.pos 51)]),
   ((.exchange 12 50 0),[(.neg 50),(.neg 12),(.pos 14),(.pos 54)]),
   ((.exchange 12 64 0),[(.neg 64),(.neg 12),(.pos 34),(.pos 54)]),
   ((.exchange 12 67 0),[(.neg 67),(.neg 12),(.pos 14),(.pos 34),(.pos 54)]),
   ((.exchange 12 68 0),[(.neg 68),(.neg 12),(.pos 34),(.pos 54)]),
   ((.exchange 12 69 0),[(.neg 69),(.neg 12),(.pos 34),(.pos 54)]),
   ((.exchange 13 41 3),[(.neg 41),(.neg 13),(.pos 11),(.pos 52)]),
   ((.exchange 13 46 3),[(.neg 46),(.neg 13),(.pos 9),(.pos 11),(.pos 52)]),
   ((.exchange 20 37 4),[(.neg 37),(.neg 20),(.pos 17),(.pos 56)]),
   ((.exchange 20 38 4),[(.neg 38),(.neg 20),(.pos 15),(.pos 17),(.pos 56)]),
   ((.exchange 20 50 0),[(.neg 50),(.neg 20),(.pos 24),(.pos 33),(.pos 63)]),
   ((.exchange 20 57 4),[(.neg 57),(.neg 20),(.pos 15),(.pos 56)]),
   ((.exchange 20 58 4),[(.neg 58),(.neg 20),(.pos 17),(.pos 56)]),
   ((.exchange 20 59 4),[(.neg 59),(.neg 20),(.pos 15),(.pos 17),(.pos 56)]),
   ((.exchange 20 62 2),[(.neg 62),(.neg 20),(.pos 19),(.pos 61)]),
   ((.exchange 20 64 0),[(.neg 64),(.neg 20),(.pos 24),(.pos 63)]),
   ((.exchange 20 67 0),[(.neg 67),(.neg 20),(.pos 33),(.pos 63)]),
   ((.exchange 20 68 0),[(.neg 68),(.neg 20),(.pos 24),(.pos 33),(.pos 63)]),
   ((.exchange 20 69 0),[(.neg 69),(.neg 20),(.pos 33),(.pos 63)]),
   ((.exchange 21 56 4),[(.neg 56),(.neg 21),(.pos 15),(.pos 57)]),
   ((.exchange 21 61 2),[(.neg 61),(.neg 21),(.pos 19),(.pos 62)]),
   ((.exchange 22 44 0),[(.neg 44),(.neg 22),(.pos 24),(.pos 64)]),
   ((.exchange 22 50 0),[(.neg 50),(.neg 22),(.pos 24),(.pos 34),(.pos 64)]),
   ((.exchange 22 54 0),[(.neg 54),(.neg 22),(.pos 34),(.pos 64)]),
   ((.exchange 22 56 4),[(.neg 56),(.neg 22),(.pos 17),(.pos 58)]),
   ((.exchange 22 63 0),[(.neg 63),(.neg 22),(.pos 24),(.pos 64)]),
   ((.exchange 22 67 0),[(.neg 67),(.neg 22),(.pos 24),(.pos 34),(.pos 64)]),
   ((.exchange 22 68 0),[(.neg 68),(.neg 22),(.pos 34),(.pos 64)]),
   ((.exchange 22 69 0),[(.neg 69),(.neg 22),(.pos 34),(.pos 64)]),
   ((.exchange 23 56 4),[(.neg 56),(.neg 23),(.pos 16),(.pos 18),(.pos 59)]),
   ((.exchange 26 44 0),[(.neg 44),(.neg 26),(.pos 30),(.pos 33),(.pos 67)]),
   ((.exchange 26 50 0),[(.neg 50),(.neg 26),(.pos 30),(.pos 67)]),
   ((.exchange 26 54 0),[(.neg 54),(.neg 26),(.pos 30),(.pos 33),(.pos 67)]),
   ((.exchange 26 63 0),[(.neg 63),(.neg 26),(.pos 33),(.pos 67)]),
   ((.exchange 26 64 0),[(.neg 64),(.neg 26),(.pos 30),(.pos 33),(.pos 67)]),
   ((.exchange 26 66 2),[(.neg 66),(.neg 26),(.pos 25),(.pos 65)]),
   ((.exchange 26 68 0),[(.neg 68),(.neg 26),(.pos 30),(.pos 67)]),
   ((.exchange 26 69 0),[(.neg 69),(.neg 26),(.pos 33),(.pos 67)]),
   ((.exchange 27 65 2),[(.neg 65),(.neg 27),(.pos 25),(.pos 66)]),
   ((.exchange 28 44 0),[(.neg 44),(.neg 28),(.pos 30),(.pos 34),(.pos 68)]),
   ((.exchange 28 50 0),[(.neg 50),(.neg 28),(.pos 30),(.pos 68)]),
   ((.exchange 28 54 0),[(.neg 54),(.neg 28),(.pos 34),(.pos 68)]),
   ((.exchange 28 63 0),[(.neg 63),(.neg 28),(.pos 30),(.pos 34),(.pos 68)]),
   ((.exchange 28 64 0),[(.neg 64),(.neg 28),(.pos 34),(.pos 68)]),
   ((.exchange 28 67 0),[(.neg 67),(.neg 28),(.pos 30),(.pos 68)]),
   ((.exchange 28 69 0),[(.neg 69),(.neg 28),(.pos 34),(.pos 68)]),
   ((.exchange 31 44 0),[(.neg 44),(.neg 31),(.pos 33),(.pos 34),(.pos 69)]),
   ((.exchange 31 50 0),[(.neg 50),(.neg 31),(.pos 33),(.pos 34),(.pos 69)]),
   ((.exchange 31 54 0),[(.neg 54),(.neg 31),(.pos 34),(.pos 69)]),
   ((.exchange 31 63 0),[(.neg 63),(.neg 31),(.pos 33),(.pos 69)]),
   ((.exchange 31 64 0),[(.neg 64),(.neg 31),(.pos 34),(.pos 69)]),
   ((.exchange 31 67 0),[(.neg 67),(.neg 31),(.pos 33),(.pos 69)]),
   ((.exchange 31 68 0),[(.neg 68),(.neg 31),(.pos 34),(.pos 69)]),
   ((.exchange 35 3 7),[(.neg 35),(.neg 3),(.pos 0),(.pos 1)]),
   ((.exchange 36 3 7),[(.neg 36),(.neg 3),(.pos 0),(.pos 2)]),
   ((.exchange 37 12 2),[(.neg 37),(.neg 12),(.pos 42),(.pos 48)]),
   ((.exchange 38 12 2),[(.neg 38),(.neg 12),(.pos 36),(.pos 43),(.pos 49)]),
   ((.exchange 39 3 7),[(.neg 39),(.neg 3),(.pos 1),(.pos 2)]),
   ((.exchange 40 22 2),[(.neg 40),(.neg 22),(.pos 42),(.pos 61)]),
   ((.exchange 40 59 2),[(.neg 59),(.neg 40),(.pos 39),(.pos 42),(.pos 61)]),
   ((.exchange 41 22 2),[(.neg 41),(.neg 22),(.pos 39),(.pos 43),(.pos 62)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_1 : List (Origin 70 29 × List Sat.Literal) :=
  [((.exchange 41 59 2),[(.neg 59),(.neg 41),(.pos 43),(.pos 62)]),
   ((.exchange 42 7 4),[(.neg 42),(.neg 7),(.pos 37),(.pos 48)]),
   ((.exchange 42 20 3),[(.neg 42),(.neg 20),(.pos 40),(.pos 61)]),
   ((.exchange 42 57 3),[(.neg 57),(.neg 42),(.pos 39),(.pos 40),(.pos 61)]),
   ((.exchange 43 7 4),[(.neg 43),(.neg 7),(.pos 36),(.pos 38),(.pos 49)]),
   ((.exchange 43 20 3),[(.neg 43),(.neg 20),(.pos 39),(.pos 41),(.pos 62)]),
   ((.exchange 43 57 3),[(.neg 57),(.neg 43),(.pos 41),(.pos 62)]),
   ((.exchange 45 3 5),[(.neg 45),(.neg 3),(.pos 35),(.pos 36),(.pos 39)]),
   ((.exchange 48 20 3),[(.neg 48),(.neg 20),(.pos 46),(.pos 51),(.pos 65)]),
   ((.exchange 48 22 5),[(.neg 48),(.neg 22),(.pos 42),(.pos 58)]),
   ((.exchange 48 57 3),[(.neg 57),(.neg 48),(.pos 45),(.pos 46),(.pos 65)]),
   ((.exchange 49 20 3),[(.neg 49),(.neg 20),(.pos 45),(.pos 47),(.pos 52),(.pos 66)]),
   ((.exchange 49 22 5),[(.neg 49),(.neg 22),(.pos 36),(.pos 43),(.pos 59)]),
   ((.exchange 49 40 5),[(.neg 49),(.neg 40),(.pos 36),(.pos 38),(.pos 43)]),
   ((.exchange 49 57 3),[(.neg 57),(.neg 49),(.pos 47),(.pos 66)]),
   ((.exchange 49 62 3),[(.neg 62),(.neg 49),(.pos 52),(.pos 66)]),
   ((.exchange 51 28 4),[(.neg 51),(.neg 28),(.pos 48),(.pos 65)]),
   ((.exchange 52 28 4),[(.neg 52),(.neg 28),(.pos 45),(.pos 49),(.pos 66)]),
   ((.exchange 53 3 7),[(.neg 53),(.neg 3),(.pos 10),(.pos 14)]),
   ((.exchange 55 3 6),[(.neg 55),(.neg 3),(.pos 35),(.pos 36),(.pos 39)]),
   ((.exchange 56 31 2),[(.neg 56),(.neg 31),(.pos 61),(.pos 65)]),
   ((.exchange 57 31 2),[(.neg 57),(.neg 31),(.pos 55),(.pos 62),(.pos 66)]),
   ((.exchange 60 3 7),[(.neg 60),(.neg 3),(.pos 17),(.pos 24)]),
   ((.exchange 61 3 6),[(.neg 61),(.neg 3),(.pos 40),(.pos 42)]),
   ((.exchange 61 7 4),[(.neg 61),(.neg 7),(.pos 56),(.pos 58),(.pos 65)]),
   ((.exchange 61 29 4),[(.neg 61),(.neg 29),(.pos 55),(.pos 58),(.pos 65)]),
   ((.exchange 61 38 6),[(.neg 61),(.neg 38),(.pos 39),(.pos 40),(.pos 42)]),
   ((.exchange 62 3 6),[(.neg 62),(.neg 3),(.pos 39),(.pos 41),(.pos 43)]),
   ((.exchange 62 7 4),[(.neg 62),(.neg 7),(.pos 55),(.pos 57),(.pos 59),(.pos 66)]),
   ((.exchange 62 29 4),[(.neg 62),(.neg 29),(.pos 59),(.pos 66)]),
   ((.exchange 62 38 6),[(.neg 62),(.neg 38),(.pos 41),(.pos 43)]),
   ((.exchange 65 22 5),[(.neg 65),(.neg 22),(.pos 58),(.pos 61)]),
   ((.exchange 65 43 6),[(.neg 65),(.neg 43),(.pos 45),(.pos 48),(.pos 51)]),
   ((.exchange 65 62 5),[(.neg 65),(.neg 62),(.pos 55),(.pos 61)]),
   ((.exchange 66 22 5),[(.neg 66),(.neg 22),(.pos 55),(.pos 59),(.pos 62)]),
   ((.exchange 66 43 6),[(.neg 66),(.neg 43),(.pos 49),(.pos 52)]),
   ((.exchange 66 64 5),[(.neg 66),(.neg 64),(.pos 59),(.pos 62)]),
   (.newPoint,[(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 0),[(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 49),(.neg 48),(.neg 43),(.neg 42),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 63),(.pos 64),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 1),[(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 52),(.neg 51),(.neg 47),(.neg 46),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 63),(.pos 64),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 2),[(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 3),[(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 63),(.pos 64),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 4),[(.neg 66),(.neg 65),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 49),(.neg 48),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 5),[(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 43),(.neg 42),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 40),(.pos 41),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 6),[(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 49),(.neg 48),(.neg 43),(.neg 42),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 40),(.pos 41),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 63),(.pos 64),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 7),[(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 8),[(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 63),(.pos 64),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 9),[(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 10),[(.neg 66),(.neg 65),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 52),(.neg 51),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 11),[(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 52),(.neg 51),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 63),(.pos 64),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 12),[(.neg 66),(.neg 65),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 13),[(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 63),(.pos 64),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 14),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 54),(.neg 50),(.neg 44),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 51),(.pos 52),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 65),(.pos 66)]),
   ((.excluded 15),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 51),(.pos 52),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60)]),
   ((.excluded 16),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 45),(.pos 46),(.pos 47),(.pos 51),(.pos 52),(.pos 53),(.pos 55),(.pos 60),(.pos 61),(.pos 62)]),
   ((.excluded 17),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 50),(.neg 44),(.neg 43),(.neg 42),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 51),(.pos 52),(.pos 53),(.pos 55),(.pos 60),(.pos 65),(.pos 66)]),
   ((.excluded 18),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 51),(.pos 52),(.pos 53),(.pos 55),(.pos 60)]),
   ((.excluded 19),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 42),(.pos 43),(.pos 45),(.pos 48),(.pos 49),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60)]),
   ((.excluded 20),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 65),(.pos 66)]),
   ((.excluded 21),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60)]),
   ((.excluded 22),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 45),(.pos 53),(.pos 55),(.pos 60),(.pos 65),(.pos 66)]),
   ((.excluded 23),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 45),(.pos 53),(.pos 55),(.pos 60)]),
   ((.excluded 24),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 53),(.pos 55),(.pos 60),(.pos 65),(.pos 66)]),
   ((.excluded 25),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 53),(.pos 55),(.pos 60),(.pos 61),(.pos 62)]),
   ((.excluded 26),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 53),(.pos 55),(.pos 60)]),
   ((.excluded 27),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 53),(.pos 55),(.pos 60),(.pos 61),(.pos 62)]),
   ((.excluded 28),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 53),(.pos 55),(.pos 60)])]

theorem certificates_1_valid : ∀ oc ∈ certificates_1,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



theorem witness_0 : ∀ j : Fin 29,
    let w : Fin 29 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 29,
      let w : Fin 29 := ⟨0 + j.val,by omega⟩
      target w < MatroidCatalogue.count 8 4 ∧
        Papers.RationalityTen.MatroidChecked.FastSemanticChecks.RawWitness 8 (N7R4.familyMasks.get 37)
        (fun i : Fin 70 => N8R4.gridMasks.get i.val) newIndex (models w)
        (N8R4.familyMasks.get (target w)) (permutation w) := by
    refine (Fin.forall_fin_add (m := 14) (n := 15) _).2 ⟨?_, ?_⟩
    · refine (Fin.forall_fin_add (m := 7) (n := 7) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
        · decide +kernel
        · decide +kernel
      · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
        · decide +kernel
        · decide +kernel
    · refine (Fin.forall_fin_add (m := 7) (n := 8) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
        · decide +kernel
        · decide +kernel
      · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
        · decide +kernel
        · decide +kernel
  intro j
  have hj := hfast j
  exact ⟨hj.1,Papers.RationalityTen.MatroidChecked.FastSemanticChecks.rawWitness_sound 8 _ _ _ _ _ _ hj.2⟩


end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C37

/- Source: MatroidCatalogue/Cases/N8R4C37Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C37

noncomputable def certificates : List (Origin 70 29 × List Sat.Literal) :=
  certificates_0 ++ certificates_1

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  intro oc hoc
  simp only [certificates,List.mem_append,or_assoc] at hoc
  rcases hoc with h0 | h1
  · exact certificates_0_valid oc h0
  · exact certificates_1_valid oc h1

theorem models_valid : ∀ w : Fin 29,
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 29) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 8) 4)
    (hold : M.bases.filter ((7 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 8 4, IsomorphicWithin 8 M.bases B := by
  apply extension_covered_of_certificate (n:=7) (r:=4) (by decide)
    catalogue old U newIndex models certificates
    N8R4.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C37.formula []
    exact Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C37.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 8 4 (target w),family_mem 8 4 (target w) hw.1,?_⟩
    exact validWitness_sound 8 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C37


end
end
end BundlePart1

section BundlePart2
/- Source: MatroidChecked/SemanticChunks/Cases05Part03.lean -/




@[expose] public section
noncomputable section

/- Source: MatroidCatalogue/Cases/N8R4C38Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C38

abbrev U := N8R4.grid
noncomputable def old : Finset (Finset (Fin 8)) := N7R4.family 38
noncomputable def newIndexTree : Table ℕ := (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf 35) (.leaf 36)) (.node 3 (.leaf 37) (.leaf 38))) (.node 6 (.node 5 (.leaf 39) (.leaf 40)) (.node 7 (.leaf 41) (.leaf 42)))) (.node 12 (.node 10 (.node 9 (.leaf 43) (.leaf 44)) (.node 11 (.leaf 45) (.leaf 46))) (.node 14 (.node 13 (.leaf 47) (.leaf 48)) (.node 15 (.leaf 49) (.node 16 (.leaf 50) (.leaf 51)))))) (.node 26 (.node 21 (.node 19 (.node 18 (.leaf 52) (.leaf 53)) (.node 20 (.leaf 54) (.leaf 55))) (.node 23 (.node 22 (.leaf 56) (.leaf 57)) (.node 24 (.leaf 58) (.node 25 (.leaf 59) (.leaf 60))))) (.node 30 (.node 28 (.node 27 (.leaf 61) (.leaf 62)) (.node 29 (.leaf 63) (.leaf 64))) (.node 32 (.node 31 (.leaf 65) (.leaf 66)) (.node 33 (.leaf 67) (.node 34 (.leaf 68) (.leaf 69)))))))
noncomputable def newIndex (i : Fin 35) : Fin 70 := Fin.ofNat 70 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 21 (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (3447939072,105,4151322)) (.leaf (3429046272,105,4149530))) (.node 3 (.leaf (3252713472,105,4131610)) (.node 4 (.leaf (233011200,142,2045036)) (.leaf (3454236672,143,8331820))))) (.node 7 (.node 6 (.leaf (232784364,162,3959578)) (.leaf (227820,162,2353946))) (.node 8 (.leaf (233011692,213,11664520)) (.node 9 (.leaf (3429065196,188,5730851)) (.leaf (3252904428,188,5709347)))))) (.node 15 (.node 12 (.node 11 (.leaf (3454231020,199,12477969)) (.leaf (3428874732,188,5935587))) (.node 13 (.leaf (3429071340,199,11788497)) (.node 14 (.leaf (3447749100,188,5938723)) (.leaf (3454040556,199,12455121))))) (.node 18 (.node 16 (.leaf (3447921132,188,5960227)) (.node 17 (.leaf (3447945708,199,11789841)) (.leaf (3252885996,188,5706211)))) (.node 19 (.leaf (3454212588,199,12476625)) (.node 20 (.leaf (3252910572,199,11766993)) (.leaf (3454237164,221,16425507))))))) (.node 32 (.node 26 (.node 23 (.node 22 (.leaf (30904451072,92,6248648)) (.leaf (34352390144,127,8345736))) (.node 24 (.leaf (34333497344,127,8344840)) (.node 25 (.leaf (34157164544,127,8334088)) (.leaf (31137462272,164,12535432))))) (.node 29 (.node 27 (.leaf (34358687744,165,12535432)) (.node 28 (.leaf (31137235436,246,8219400)) (.leaf (30904678892,246,7072520)))) (.node 30 (.leaf (31137462764,269,16434824)) (.node 31 (.leaf (34333516268,270,16205448)) (.leaf (34157355500,270,16201864)))))) (.node 37 (.node 34 (.node 33 (.leaf (34358682092,271,16434824)) (.leaf (34333325804,270,16430344))) (.node 35 (.leaf (34333522412,271,16205000)) (.node 36 (.leaf (34352200172,270,16431240)) (.leaf (34358491628,271,16427208))))) (.node 40 (.node 38 (.leaf (34352372204,270,16434824)) (.node 39 (.leaf (34352396780,271,16205448)) (.leaf (34157337068,270,16200968)))) (.node 41 (.leaf (34358663660,271,16434376)) (.node 42 (.leaf (34157361644,271,16197832)) (.leaf (34358688236,272,16434824))))))))

noncomputable def models (i : Fin 43) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 43) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 43) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 70, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (7 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 70, (7 : Fin 8) ∈ U i → ∃ j : Fin 35, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C38

/- Source: MatroidCatalogue/Cases/N8R4C38Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C38


noncomputable def certificates_0 : List (Origin 70 43 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.neg 2)]),
   ((.fixed 3),[(.neg 3)]),
   ((.fixed 4),[(.neg 4)]),
   ((.fixed 5),[(.neg 5)]),
   ((.fixed 6),[(.neg 6)]),
   ((.fixed 7),[(.pos 7)]),
   ((.fixed 8),[(.pos 8)]),
   ((.fixed 9),[(.neg 9)]),
   ((.fixed 10),[(.pos 10)]),
   ((.fixed 11),[(.pos 11)]),
   ((.fixed 12),[(.pos 12)]),
   ((.fixed 13),[(.pos 13)]),
   ((.fixed 14),[(.neg 14)]),
   ((.fixed 15),[(.neg 15)]),
   ((.fixed 16),[(.neg 16)]),
   ((.fixed 17),[(.pos 17)]),
   ((.fixed 18),[(.pos 18)]),
   ((.fixed 19),[(.neg 19)]),
   ((.fixed 20),[(.pos 20)]),
   ((.fixed 21),[(.pos 21)]),
   ((.fixed 22),[(.pos 22)]),
   ((.fixed 23),[(.pos 23)]),
   ((.fixed 24),[(.neg 24)]),
   ((.fixed 25),[(.neg 25)]),
   ((.fixed 26),[(.pos 26)]),
   ((.fixed 27),[(.pos 27)]),
   ((.fixed 28),[(.pos 28)]),
   ((.fixed 29),[(.pos 29)]),
   ((.fixed 30),[(.neg 30)]),
   ((.fixed 31),[(.pos 31)]),
   ((.fixed 32),[(.pos 32)]),
   ((.fixed 33),[(.neg 33)]),
   ((.fixed 34),[(.neg 34)]),
   ((.exchange 7 41 5),[(.neg 41),(.neg 7),(.pos 0),(.pos 3),(.pos 37)]),
   ((.exchange 7 47 3),[(.neg 47),(.neg 7),(.pos 5),(.pos 46)]),
   ((.exchange 7 49 2),[(.neg 49),(.neg 7),(.pos 6),(.pos 48)]),
   ((.exchange 7 53 0),[(.neg 53),(.neg 7),(.pos 14),(.pos 50)]),
   ((.exchange 7 54 0),[(.neg 54),(.neg 7),(.pos 14),(.pos 50)]),
   ((.exchange 7 60 0),[(.neg 60),(.neg 7),(.pos 30),(.pos 50)]),
   ((.exchange 7 63 0),[(.neg 63),(.neg 7),(.pos 14),(.pos 30),(.pos 50)]),
   ((.exchange 7 64 0),[(.neg 64),(.neg 7),(.pos 14),(.pos 30),(.pos 50)]),
   ((.exchange 7 67 0),[(.neg 67),(.neg 7),(.pos 30),(.pos 50)]),
   ((.exchange 7 68 0),[(.neg 68),(.neg 7),(.pos 30),(.pos 50)]),
   ((.exchange 7 69 0),[(.neg 69),(.neg 7),(.pos 14),(.pos 30),(.pos 50)]),
   ((.exchange 8 41 5),[(.neg 41),(.neg 8),(.pos 4),(.pos 38)]),
   ((.exchange 8 46 3),[(.neg 46),(.neg 8),(.pos 5),(.pos 47)]),
   ((.exchange 8 48 2),[(.neg 48),(.neg 8),(.pos 6),(.pos 49)]),
   ((.exchange 10 41 5),[(.neg 41),(.neg 10),(.pos 1),(.pos 40)]),
   ((.exchange 10 50 0),[(.neg 50),(.neg 10),(.pos 14),(.pos 53)]),
   ((.exchange 10 52 2),[(.neg 52),(.neg 10),(.pos 9),(.pos 51)]),
   ((.exchange 10 64 0),[(.neg 64),(.neg 10),(.pos 14),(.pos 33),(.pos 53)]),
   ((.exchange 10 67 0),[(.neg 67),(.neg 10),(.pos 33),(.pos 53)]),
   ((.exchange 10 68 0),[(.neg 68),(.neg 10),(.pos 14),(.pos 33),(.pos 53)]),
   ((.exchange 10 69 0),[(.neg 69),(.neg 10),(.pos 33),(.pos 53)]),
   ((.exchange 11 37 5),[(.neg 37),(.neg 11),(.pos 1),(.pos 4),(.pos 41)]),
   ((.exchange 11 38 5),[(.neg 38),(.neg 11),(.pos 4),(.pos 41)]),
   ((.exchange 11 40 5),[(.neg 40),(.neg 11),(.pos 1),(.pos 41)]),
   ((.exchange 11 42 5),[(.neg 42),(.neg 11),(.pos 1),(.pos 4),(.pos 41)]),
   ((.exchange 11 43 5),[(.neg 43),(.neg 11),(.pos 4),(.pos 41)]),
   ((.exchange 11 51 2),[(.neg 51),(.neg 11),(.pos 9),(.pos 52)]),
   ((.exchange 12 41 5),[(.neg 41),(.neg 12),(.pos 2),(.pos 3),(.pos 42)]),
   ((.exchange 12 50 0),[(.neg 50),(.neg 12),(.pos 14),(.pos 54)]),
   ((.exchange 12 64 0),[(.neg 64),(.neg 12),(.pos 34),(.pos 54)]),
   ((.exchange 12 67 0),[(.neg 67),(.neg 12),(.pos 14),(.pos 34),(.pos 54)]),
   ((.exchange 12 68 0),[(.neg 68),(.neg 12),(.pos 34),(.pos 54)]),
   ((.exchange 12 69 0),[(.neg 69),(.neg 12),(.pos 34),(.pos 54)]),
   ((.exchange 13 41 5),[(.neg 41),(.neg 13),(.pos 4),(.pos 43)]),
   ((.exchange 17 50 0),[(.neg 50),(.neg 17),(.pos 30),(.pos 60)]),
   ((.exchange 17 57 3),[(.neg 57),(.neg 17),(.pos 15),(.pos 56)]),
   ((.exchange 17 59 2),[(.neg 59),(.neg 17),(.pos 16),(.pos 58)]),
   ((.exchange 17 64 0),[(.neg 64),(.neg 17),(.pos 24),(.pos 60)]),
   ((.exchange 17 67 0),[(.neg 67),(.neg 17),(.pos 30),(.pos 60)]),
   ((.exchange 17 68 0),[(.neg 68),(.neg 17),(.pos 30),(.pos 60)]),
   ((.exchange 17 69 0),[(.neg 69),(.neg 17),(.pos 24),(.pos 30),(.pos 60)]),
   ((.exchange 18 56 3),[(.neg 56),(.neg 18),(.pos 15),(.pos 57)]),
   ((.exchange 18 58 2),[(.neg 58),(.neg 18),(.pos 16),(.pos 59)]),
   ((.exchange 20 50 0),[(.neg 50),(.neg 20),(.pos 24),(.pos 33),(.pos 63)]),
   ((.exchange 20 62 2),[(.neg 62),(.neg 20),(.pos 19),(.pos 61)]),
   ((.exchange 20 64 0),[(.neg 64),(.neg 20),(.pos 24),(.pos 63)]),
   ((.exchange 20 67 0),[(.neg 67),(.neg 20),(.pos 33),(.pos 63)]),
   ((.exchange 20 68 0),[(.neg 68),(.neg 20),(.pos 24),(.pos 33),(.pos 63)]),
   ((.exchange 20 69 0),[(.neg 69),(.neg 20),(.pos 33),(.pos 63)]),
   ((.exchange 21 61 2),[(.neg 61),(.neg 21),(.pos 19),(.pos 62)]),
   ((.exchange 22 50 0),[(.neg 50),(.neg 22),(.pos 24),(.pos 34),(.pos 64)]),
   ((.exchange 22 53 0),[(.neg 53),(.neg 22),(.pos 24),(.pos 34),(.pos 64)]),
   ((.exchange 22 54 0),[(.neg 54),(.neg 22),(.pos 34),(.pos 64)]),
   ((.exchange 22 60 0),[(.neg 60),(.neg 22),(.pos 24),(.pos 64)]),
   ((.exchange 22 63 0),[(.neg 63),(.neg 22),(.pos 24),(.pos 64)]),
   ((.exchange 22 67 0),[(.neg 67),(.neg 22),(.pos 24),(.pos 34),(.pos 64)]),
   ((.exchange 22 68 0),[(.neg 68),(.neg 22),(.pos 34),(.pos 64)]),
   ((.exchange 22 69 0),[(.neg 69),(.neg 22),(.pos 34),(.pos 64)]),
   ((.exchange 26 50 0),[(.neg 50),(.neg 26),(.pos 30),(.pos 67)]),
   ((.exchange 26 53 0),[(.neg 53),(.neg 26),(.pos 33),(.pos 67)]),
   ((.exchange 26 54 0),[(.neg 54),(.neg 26),(.pos 30),(.pos 33),(.pos 67)]),
   ((.exchange 26 60 0),[(.neg 60),(.neg 26),(.pos 30),(.pos 67)]),
   ((.exchange 26 63 0),[(.neg 63),(.neg 26),(.pos 33),(.pos 67)]),
   ((.exchange 26 64 0),[(.neg 64),(.neg 26),(.pos 30),(.pos 33),(.pos 67)]),
   ((.exchange 26 66 2),[(.neg 66),(.neg 26),(.pos 25),(.pos 65)]),
   ((.exchange 26 68 0),[(.neg 68),(.neg 26),(.pos 30),(.pos 67)]),
   ((.exchange 26 69 0),[(.neg 69),(.neg 26),(.pos 33),(.pos 67)]),
   ((.exchange 27 65 2),[(.neg 65),(.neg 27),(.pos 25),(.pos 66)]),
   ((.exchange 28 50 0),[(.neg 50),(.neg 28),(.pos 30),(.pos 68)]),
   ((.exchange 28 53 0),[(.neg 53),(.neg 28),(.pos 30),(.pos 34),(.pos 68)]),
   ((.exchange 28 54 0),[(.neg 54),(.neg 28),(.pos 34),(.pos 68)]),
   ((.exchange 28 60 0),[(.neg 60),(.neg 28),(.pos 30),(.pos 68)]),
   ((.exchange 28 63 0),[(.neg 63),(.neg 28),(.pos 30),(.pos 34),(.pos 68)]),
   ((.exchange 28 64 0),[(.neg 64),(.neg 28),(.pos 34),(.pos 68)]),
   ((.exchange 28 67 0),[(.neg 67),(.neg 28),(.pos 30),(.pos 68)]),
   ((.exchange 28 69 0),[(.neg 69),(.neg 28),(.pos 34),(.pos 68)]),
   ((.exchange 31 50 0),[(.neg 50),(.neg 31),(.pos 33),(.pos 34),(.pos 69)]),
   ((.exchange 31 53 0),[(.neg 53),(.neg 31),(.pos 33),(.pos 69)]),
   ((.exchange 31 54 0),[(.neg 54),(.neg 31),(.pos 34),(.pos 69)]),
   ((.exchange 31 60 0),[(.neg 60),(.neg 31),(.pos 33),(.pos 34),(.pos 69)]),
   ((.exchange 31 63 0),[(.neg 63),(.neg 31),(.pos 33),(.pos 69)]),
   ((.exchange 31 64 0),[(.neg 64),(.neg 31),(.pos 34),(.pos 69)]),
   ((.exchange 31 67 0),[(.neg 67),(.neg 31),(.pos 33),(.pos 69)]),
   ((.exchange 31 68 0),[(.neg 68),(.neg 31),(.pos 34),(.pos 69)]),
   ((.exchange 35 7 7),[(.neg 35),(.neg 7),(.pos 0),(.pos 5)]),
   ((.exchange 36 7 7),[(.neg 36),(.neg 7),(.pos 0),(.pos 6)]),
   ((.exchange 37 28 2),[(.neg 37),(.neg 28),(.pos 48),(.pos 58)]),
   ((.exchange 38 27 3),[(.neg 38),(.neg 27),(.pos 47),(.pos 57)]),
   ((.exchange 38 28 2),[(.neg 38),(.neg 28),(.pos 36),(.pos 49),(.pos 59)]),
   ((.exchange 39 7 7),[(.neg 39),(.neg 7),(.pos 1),(.pos 2),(.pos 9)]),
   ((.exchange 40 27 4),[(.neg 40),(.neg 27),(.pos 35),(.pos 46),(.pos 56)]),
   ((.exchange 40 31 2),[(.neg 40),(.neg 31),(.pos 51),(.pos 61)]),
   ((.exchange 41 31 2),[(.neg 41),(.neg 31),(.pos 39),(.pos 52),(.pos 62)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_1 : List (Origin 70 43 × List Sat.Literal) :=
  [((.exchange 42 65 3),[(.neg 65),(.neg 42),(.pos 51),(.pos 61)]),
   ((.exchange 43 66 3),[(.neg 66),(.neg 43),(.pos 52),(.pos 62)]),
   ((.exchange 44 7 7),[(.neg 44),(.neg 7),(.pos 3),(.pos 14)]),
   ((.exchange 45 7 7),[(.neg 45),(.neg 7),(.pos 5),(.pos 6)]),
   ((.exchange 46 12 2),[(.neg 46),(.neg 12),(.pos 48),(.pos 51)]),
   ((.exchange 46 13 2),[(.neg 46),(.neg 13),(.pos 45),(.pos 48),(.pos 51)]),
   ((.exchange 46 17 5),[(.neg 46),(.neg 17),(.pos 37),(.pos 56)]),
   ((.exchange 46 28 2),[(.neg 46),(.neg 28),(.pos 48),(.pos 65)]),
   ((.exchange 46 29 2),[(.neg 46),(.neg 29),(.pos 45),(.pos 48),(.pos 65)]),
   ((.exchange 46 62 2),[(.neg 62),(.neg 46),(.pos 45),(.pos 51),(.pos 65)]),
   ((.exchange 46 68 2),[(.neg 68),(.neg 46),(.pos 48),(.pos 65)]),
   ((.exchange 46 69 2),[(.neg 69),(.neg 46),(.pos 51),(.pos 65)]),
   ((.exchange 47 12 2),[(.neg 47),(.neg 12),(.pos 45),(.pos 49),(.pos 52)]),
   ((.exchange 47 13 2),[(.neg 47),(.neg 13),(.pos 49),(.pos 52)]),
   ((.exchange 47 17 5),[(.neg 47),(.neg 17),(.pos 35),(.pos 38),(.pos 57)]),
   ((.exchange 47 28 2),[(.neg 47),(.neg 28),(.pos 45),(.pos 49),(.pos 66)]),
   ((.exchange 47 29 2),[(.neg 47),(.neg 29),(.pos 49),(.pos 66)]),
   ((.exchange 47 32 2),[(.neg 47),(.neg 32),(.pos 52),(.pos 66)]),
   ((.exchange 47 58 2),[(.neg 58),(.neg 47),(.pos 45),(.pos 49),(.pos 66)]),
   ((.exchange 47 62 2),[(.neg 62),(.neg 47),(.pos 52),(.pos 66)]),
   ((.exchange 47 68 2),[(.neg 68),(.neg 47),(.pos 49),(.pos 66)]),
   ((.exchange 47 69 2),[(.neg 69),(.neg 47),(.pos 52),(.pos 66)]),
   ((.exchange 48 10 3),[(.neg 48),(.neg 10),(.pos 46),(.pos 51)]),
   ((.exchange 48 17 5),[(.neg 48),(.neg 17),(.pos 37),(.pos 58)]),
   ((.exchange 48 26 3),[(.neg 48),(.neg 26),(.pos 46),(.pos 65)]),
   ((.exchange 48 31 3),[(.neg 48),(.neg 31),(.pos 51),(.pos 65)]),
   ((.exchange 48 56 3),[(.neg 56),(.neg 48),(.pos 46),(.pos 65)]),
   ((.exchange 48 57 5),[(.neg 57),(.neg 48),(.pos 36),(.pos 37),(.pos 58)]),
   ((.exchange 49 10 3),[(.neg 49),(.neg 10),(.pos 45),(.pos 47),(.pos 52)]),
   ((.exchange 49 17 5),[(.neg 49),(.neg 17),(.pos 36),(.pos 38),(.pos 59)]),
   ((.exchange 49 26 3),[(.neg 49),(.neg 26),(.pos 45),(.pos 47),(.pos 66)]),
   ((.exchange 49 31 3),[(.neg 49),(.neg 31),(.pos 45),(.pos 52),(.pos 66)]),
   ((.exchange 49 56 3),[(.neg 56),(.neg 49),(.pos 45),(.pos 47),(.pos 66)]),
   ((.exchange 49 57 5),[(.neg 57),(.neg 49),(.pos 38),(.pos 59)]),
   ((.exchange 51 7 4),[(.neg 51),(.neg 7),(.pos 46),(.pos 48)]),
   ((.exchange 51 17 5),[(.neg 51),(.neg 17),(.pos 40),(.pos 42),(.pos 61)]),
   ((.exchange 51 27 4),[(.neg 51),(.neg 27),(.pos 45),(.pos 46),(.pos 65)]),
   ((.exchange 51 29 4),[(.neg 51),(.neg 29),(.pos 45),(.pos 48),(.pos 65)]),
   ((.exchange 51 56 4),[(.neg 56),(.neg 51),(.pos 46),(.pos 65)]),
   ((.exchange 51 57 5),[(.neg 57),(.neg 51),(.pos 39),(.pos 40),(.pos 61)]),
   ((.exchange 51 59 4),[(.neg 59),(.neg 51),(.pos 45),(.pos 48),(.pos 65)]),
   ((.exchange 52 7 4),[(.neg 52),(.neg 7),(.pos 45),(.pos 47),(.pos 49)]),
   ((.exchange 52 17 5),[(.neg 52),(.neg 17),(.pos 39),(.pos 41),(.pos 43),(.pos 62)]),
   ((.exchange 52 27 4),[(.neg 52),(.neg 27),(.pos 47),(.pos 66)]),
   ((.exchange 52 29 4),[(.neg 52),(.neg 29),(.pos 49),(.pos 66)]),
   ((.exchange 52 56 4),[(.neg 56),(.neg 52),(.pos 45),(.pos 47),(.pos 66)]),
   ((.exchange 52 57 5),[(.neg 57),(.neg 52),(.pos 41),(.pos 62)]),
   ((.exchange 55 7 6),[(.neg 55),(.neg 7),(.pos 35),(.pos 36),(.pos 45)]),
   ((.exchange 56 10 6),[(.neg 56),(.neg 10),(.pos 40),(.pos 46)]),
   ((.exchange 56 22 2),[(.neg 56),(.neg 22),(.pos 58),(.pos 61)]),
   ((.exchange 56 23 2),[(.neg 56),(.neg 23),(.pos 55),(.pos 58),(.pos 61)]),
   ((.exchange 56 29 2),[(.neg 56),(.neg 29),(.pos 55),(.pos 58),(.pos 65)]),
   ((.exchange 56 31 2),[(.neg 56),(.neg 31),(.pos 61),(.pos 65)]),
   ((.exchange 56 32 2),[(.neg 56),(.neg 32),(.pos 55),(.pos 61),(.pos 65)]),
   ((.exchange 56 52 2),[(.neg 56),(.neg 52),(.pos 55),(.pos 61),(.pos 65)]),
   ((.exchange 57 7 6),[(.neg 57),(.neg 7),(.pos 35),(.pos 38),(.pos 47)]),
   ((.exchange 57 22 2),[(.neg 57),(.neg 22),(.pos 55),(.pos 59),(.pos 62)]),
   ((.exchange 57 23 2),[(.neg 57),(.neg 23),(.pos 59),(.pos 62)]),
   ((.exchange 57 29 2),[(.neg 57),(.neg 29),(.pos 59),(.pos 66)]),
   ((.exchange 57 31 2),[(.neg 57),(.neg 31),(.pos 55),(.pos 62),(.pos 66)]),
   ((.exchange 57 32 2),[(.neg 57),(.neg 32),(.pos 62),(.pos 66)]),
   ((.exchange 58 11 6),[(.neg 58),(.neg 11),(.pos 36),(.pos 37),(.pos 42),(.pos 48)]),
   ((.exchange 58 20 3),[(.neg 58),(.neg 20),(.pos 56),(.pos 61)]),
   ((.exchange 58 26 3),[(.neg 58),(.neg 26),(.pos 56),(.pos 65)]),
   ((.exchange 58 47 3),[(.neg 58),(.neg 47),(.pos 55),(.pos 56),(.pos 65)]),
   ((.exchange 58 51 6),[(.neg 58),(.neg 51),(.pos 42),(.pos 48)]),
   ((.exchange 58 67 3),[(.neg 67),(.neg 58),(.pos 56),(.pos 65)]),
   ((.exchange 59 11 6),[(.neg 59),(.neg 11),(.pos 38),(.pos 43),(.pos 49)]),
   ((.exchange 59 20 3),[(.neg 59),(.neg 20),(.pos 55),(.pos 57),(.pos 62)]),
   ((.exchange 59 26 3),[(.neg 59),(.neg 26),(.pos 55),(.pos 57),(.pos 66)]),
   ((.exchange 59 47 3),[(.neg 59),(.neg 47),(.pos 57),(.pos 66)]),
   ((.exchange 59 52 6),[(.neg 59),(.neg 52),(.pos 43),(.pos 49)]),
   ((.exchange 59 67 3),[(.neg 67),(.neg 59),(.pos 57),(.pos 66)]),
   ((.exchange 61 11 6),[(.neg 61),(.neg 11),(.pos 39),(.pos 40),(.pos 51)]),
   ((.exchange 61 27 4),[(.neg 61),(.neg 27),(.pos 55),(.pos 56),(.pos 65)]),
   ((.exchange 61 29 4),[(.neg 61),(.neg 29),(.pos 55),(.pos 58),(.pos 65)]),
   ((.exchange 61 47 4),[(.neg 61),(.neg 47),(.pos 55),(.pos 56),(.pos 65)]),
   ((.exchange 61 47 6),[(.neg 61),(.neg 47),(.pos 39),(.pos 40),(.pos 51)]),
   ((.exchange 61 67 4),[(.neg 67),(.neg 61),(.pos 56),(.pos 65)]),
   ((.exchange 62 11 6),[(.neg 62),(.neg 11),(.pos 41),(.pos 52)]),
   ((.exchange 62 27 4),[(.neg 62),(.neg 27),(.pos 57),(.pos 66)]),
   ((.exchange 62 29 4),[(.neg 62),(.neg 29),(.pos 59),(.pos 66)]),
   ((.exchange 62 51 6),[(.neg 62),(.neg 51),(.pos 39),(.pos 52)]),
   ((.exchange 62 67 4),[(.neg 67),(.neg 62),(.pos 57),(.pos 66)]),
   ((.exchange 62 68 4),[(.neg 68),(.neg 62),(.pos 59),(.pos 66)]),
   ((.exchange 65 7 6),[(.neg 65),(.neg 7),(.pos 46),(.pos 48)]),
   ((.exchange 65 12 6),[(.neg 65),(.neg 12),(.pos 48),(.pos 51)]),
   ((.exchange 65 17 5),[(.neg 65),(.neg 17),(.pos 56),(.pos 58)]),
   ((.exchange 65 38 6),[(.neg 65),(.neg 38),(.pos 45),(.pos 46),(.pos 48)]),
   ((.exchange 65 41 5),[(.neg 65),(.neg 41),(.pos 55),(.pos 56),(.pos 61)]),
   ((.exchange 65 41 6),[(.neg 65),(.neg 41),(.pos 45),(.pos 46),(.pos 51)]),
   ((.exchange 65 42 5),[(.neg 65),(.neg 42),(.pos 58),(.pos 61)]),
   ((.exchange 65 53 6),[(.neg 65),(.neg 53),(.pos 46),(.pos 51)]),
   ((.exchange 65 60 5),[(.neg 65),(.neg 60),(.pos 56),(.pos 58)]),
   ((.exchange 65 63 5),[(.neg 65),(.neg 63),(.pos 56),(.pos 61)]),
   ((.exchange 66 7 6),[(.neg 66),(.neg 7),(.pos 45),(.pos 47),(.pos 49)]),
   ((.exchange 66 10 6),[(.neg 66),(.neg 10),(.pos 45),(.pos 47),(.pos 52)]),
   ((.exchange 66 12 6),[(.neg 66),(.neg 12),(.pos 45),(.pos 49),(.pos 52)]),
   ((.exchange 66 37 5),[(.neg 66),(.neg 37),(.pos 55),(.pos 57),(.pos 59)]),
   ((.exchange 66 38 6),[(.neg 66),(.neg 38),(.pos 47),(.pos 49)]),
   ((.exchange 66 41 5),[(.neg 66),(.neg 41),(.pos 57),(.pos 62)]),
   ((.exchange 66 41 6),[(.neg 66),(.neg 41),(.pos 47),(.pos 52)]),
   ((.exchange 66 60 5),[(.neg 66),(.neg 60),(.pos 57),(.pos 59)]),
   ((.exchange 66 63 5),[(.neg 66),(.neg 63),(.pos 57),(.pos 62)]),
   (.newPoint,[(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 0),[(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 64),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 1),[(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 57),(.neg 56),(.neg 52),(.neg 51),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 58),(.pos 59),(.pos 60),(.pos 63),(.pos 64),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 2),[(.neg 66),(.neg 65),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 3),[(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 4),[(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 63),(.pos 64),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 5),[(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 6),[(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 7),[(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 8),[(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 57),(.neg 56),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 58),(.pos 59),(.pos 60),(.pos 63),(.pos 64),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 9),[(.neg 66),(.neg 65),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 10),[(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 63),(.pos 64),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 11),[(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 57),(.neg 56),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 58),(.pos 59),(.pos 60),(.pos 63),(.pos 64),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 12),[(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 57),(.neg 56),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 58),(.pos 59),(.pos 60),(.pos 63),(.pos 64),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 13),[(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 64),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 14),[(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 63),(.pos 64),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 15),[(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 52),(.neg 51),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 64),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 16),[(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 64),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 17),[(.neg 66),(.neg 65),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 52),(.neg 51),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 18),[(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 52),(.neg 51),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 63),(.pos 64),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 19),[(.neg 66),(.neg 65),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 20),[(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 63),(.pos 64),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 21),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 60),(.neg 54),(.neg 53),(.neg 50),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 51),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 61),(.pos 62),(.pos 65),(.pos 66)]),
   ((.excluded 22),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57)])]

theorem certificates_1_valid : ∀ oc ∈ certificates_1,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_2 : List (Origin 70 43 × List Sat.Literal) :=
  [((.excluded 23),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 58),(.pos 59)]),
   ((.excluded 24),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 25),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 55),(.pos 65),(.pos 66)]),
   ((.excluded 26),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 55)]),
   ((.excluded 27),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 51),(.pos 52),(.pos 55),(.pos 65),(.pos 66)]),
   ((.excluded 28),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 60),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 61),(.pos 62),(.pos 65),(.pos 66)]),
   ((.excluded 29),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 65),(.pos 66)]),
   ((.excluded 30),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 58),(.pos 59)]),
   ((.excluded 31),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 32),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 55)]),
   ((.excluded 33),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 58),(.pos 59)]),
   ((.excluded 34),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 58),(.pos 59)]),
   ((.excluded 35),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 36),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 51),(.pos 52),(.pos 55)]),
   ((.excluded 37),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 38),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 39),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 40),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 55)]),
   ((.excluded 41),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 42),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55)])]

theorem certificates_2_valid : ∀ oc ∈ certificates_2,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



theorem witness_0 : ∀ j : Fin 43,
    let w : Fin 43 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 43,
      let w : Fin 43 := ⟨0 + j.val,by omega⟩
      target w < MatroidCatalogue.count 8 4 ∧
        Papers.RationalityTen.MatroidChecked.FastSemanticChecks.RawWitness 8 (N7R4.familyMasks.get 38)
        (fun i : Fin 70 => N8R4.gridMasks.get i.val) newIndex (models w)
        (N8R4.familyMasks.get (target w)) (permutation w) := by
    refine (Fin.forall_fin_add (m := 21) (n := 22) _).2 ⟨?_, ?_⟩
    · refine (Fin.forall_fin_add (m := 10) (n := 11) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 5) (n := 5) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
          · decide +kernel
          · decide +kernel
        · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
          · decide +kernel
          · decide +kernel
      · refine (Fin.forall_fin_add (m := 5) (n := 6) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
          · decide +kernel
          · decide +kernel
        · refine (Fin.forall_fin_add (m := 3) (n := 3) _).2 ⟨?_, ?_⟩
          · decide +kernel
          · decide +kernel
    · refine (Fin.forall_fin_add (m := 11) (n := 11) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 5) (n := 6) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
          · decide +kernel
          · decide +kernel
        · refine (Fin.forall_fin_add (m := 3) (n := 3) _).2 ⟨?_, ?_⟩
          · decide +kernel
          · decide +kernel
      · refine (Fin.forall_fin_add (m := 5) (n := 6) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
          · decide +kernel
          · decide +kernel
        · refine (Fin.forall_fin_add (m := 3) (n := 3) _).2 ⟨?_, ?_⟩
          · decide +kernel
          · decide +kernel
  intro j
  have hj := hfast j
  exact ⟨hj.1,Papers.RationalityTen.MatroidChecked.FastSemanticChecks.rawWitness_sound 8 _ _ _ _ _ _ hj.2⟩


end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C38

/- Source: MatroidCatalogue/Cases/N8R4C38Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C38

noncomputable def certificates : List (Origin 70 43 × List Sat.Literal) :=
  certificates_0 ++ certificates_1 ++ certificates_2

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  intro oc hoc
  simp only [certificates,List.mem_append,or_assoc] at hoc
  rcases hoc with h0 | h1 | h2
  · exact certificates_0_valid oc h0
  · exact certificates_1_valid oc h1
  · exact certificates_2_valid oc h2

theorem models_valid : ∀ w : Fin 43,
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 43) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 8) 4)
    (hold : M.bases.filter ((7 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 8 4, IsomorphicWithin 8 M.bases B := by
  apply extension_covered_of_certificate (n:=7) (r:=4) (by decide)
    catalogue old U newIndex models certificates
    N8R4.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C38.formula []
    exact Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C38.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 8 4 (target w),family_mem 8 4 (target w) hw.1,?_⟩
    exact validWitness_sound 8 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C38


end
end
end BundlePart2

section BundlePart3
/- Source: MatroidChecked/SemanticChunks/Cases05Part04.lean -/




@[expose] public section
noncomputable section

/- Source: MatroidCatalogue/Cases/N8R4C39Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C39

abbrev U := N8R4.grid
noncomputable def old : Finset (Finset (Fin 8)) := N7R4.family 39
noncomputable def newIndexTree : Table ℕ := (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf 35) (.leaf 36)) (.node 3 (.leaf 37) (.leaf 38))) (.node 6 (.node 5 (.leaf 39) (.leaf 40)) (.node 7 (.leaf 41) (.leaf 42)))) (.node 12 (.node 10 (.node 9 (.leaf 43) (.leaf 44)) (.node 11 (.leaf 45) (.leaf 46))) (.node 14 (.node 13 (.leaf 47) (.leaf 48)) (.node 15 (.leaf 49) (.node 16 (.leaf 50) (.leaf 51)))))) (.node 26 (.node 21 (.node 19 (.node 18 (.leaf 52) (.leaf 53)) (.node 20 (.leaf 54) (.leaf 55))) (.node 23 (.node 22 (.leaf 56) (.leaf 57)) (.node 24 (.leaf 58) (.node 25 (.leaf 59) (.leaf 60))))) (.node 30 (.node 28 (.node 27 (.leaf 61) (.leaf 62)) (.node 29 (.leaf 63) (.leaf 64))) (.node 32 (.node 31 (.leaf 65) (.leaf 66)) (.node 33 (.leaf 67) (.node 34 (.leaf 68) (.leaf 69)))))))
noncomputable def newIndex (i : Fin 35) : Fin 70 := Fin.ofNat 70 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 25 (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (26609483776,93,6248648)) (.node 2 (.leaf (25996517376,107,4151322)) (.leaf (1066393600,124,7765128)))) (.node 4 (.leaf (26836197376,125,8345736)) (.node 5 (.leaf (24903882752,108,4149530)) (.leaf (16137615360,108,4131610))))) (.node 9 (.node 7 (.leaf (33519007744,145,12535432)) (.node 8 (.leaf (17153628160,128,8344840)) (.leaf (34333497344,129,8344840)))) (.node 10 (.leaf (25567229952,128,8334088)) (.node 11 (.leaf (34157164544,129,8334088)) (.leaf (25768753152,169,12535432)))))) (.node 18 (.node 15 (.node 13 (.leaf (17178818560,169,12531848)) (.node 14 (.leaf (34358687744,170,12535432)) (.leaf (1065353708,112,7699720)))) (.node 16 (.leaf (1040876,112,7011592)) (.node 17 (.leaf (1066394092,167,11664520)) (.leaf (26608886252,126,5438664))))) (.node 21 (.node 19 (.leaf (26835378668,163,9829512)) (.node 20 (.leaf (25997115884,126,5668040)) (.leaf (25997337068,163,9370760)))) (.node 23 (.node 22 (.leaf (26835976684,134,7699720)) (.leaf (26609705452,134,7011592))) (.node 24 (.leaf (26836197868,175,11664520)) (.leaf (25566583276,266,10413256))))))) (.node 38 (.node 31 (.node 28 (.node 26 (.leaf (25767909868,267,12477640)) (.node 27 (.leaf (17152637420,266,10398920)) (.leaf (17177803244,267,12463304)))) (.node 29 (.leaf (34332703212,270,12535432)) (.node 30 (.leaf (34156542444,270,12531848)) (.leaf (34357869036,271,14599816))))) (.node 34 (.node 32 (.leaf (24904530412,266,9954504)) (.node 33 (.leaf (24904727020,267,11789512)) (.leaf (16138607084,266,9940168)))) (.node 36 (.node 35 (.leaf (16138631660,267,11775176)) (.leaf (33519802860,270,12306056))) (.node 37 (.leaf (33519630828,270,12302472)) (.leaf (33519827436,271,14141064)))))) (.node 44 (.node 41 (.node 39 (.leaf (34157337068,273,12306056)) (.node 40 (.leaf (17178794476,274,14571144)) (.leaf (34358663660,275,14571144)))) (.node 42 (.leaf (25567427052,274,13875848)) (.node 43 (.leaf (34157361644,275,13875848)) (.leaf (25768557036,274,14563976))))) (.node 47 (.node 45 (.leaf (25768753644,276,16434824)) (.node 46 (.leaf (34333325804,273,12535432)) (.leaf (34358491628,275,14563976)))) (.node 49 (.node 48 (.leaf (17153653228,274,13883016)) (.leaf (34333522412,275,13883016))) (.node 50 (.leaf (17178819052,276,16431240)) (.leaf (34358688236,277,16434824))))))))

noncomputable def models (i : Fin 51) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 51) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 51) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 70, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (7 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 70, (7 : Fin 8) ∈ U i → ∃ j : Fin 35, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C39

/- Source: MatroidCatalogue/Cases/N8R4C39Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C39


noncomputable def certificates_0 : List (Origin 70 51 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.neg 2)]),
   ((.fixed 3),[(.neg 3)]),
   ((.fixed 4),[(.neg 4)]),
   ((.fixed 5),[(.neg 5)]),
   ((.fixed 6),[(.neg 6)]),
   ((.fixed 7),[(.pos 7)]),
   ((.fixed 8),[(.pos 8)]),
   ((.fixed 9),[(.neg 9)]),
   ((.fixed 10),[(.pos 10)]),
   ((.fixed 11),[(.pos 11)]),
   ((.fixed 12),[(.pos 12)]),
   ((.fixed 13),[(.pos 13)]),
   ((.fixed 14),[(.neg 14)]),
   ((.fixed 15),[(.neg 15)]),
   ((.fixed 16),[(.neg 16)]),
   ((.fixed 17),[(.pos 17)]),
   ((.fixed 18),[(.pos 18)]),
   ((.fixed 19),[(.neg 19)]),
   ((.fixed 20),[(.pos 20)]),
   ((.fixed 21),[(.pos 21)]),
   ((.fixed 22),[(.pos 22)]),
   ((.fixed 23),[(.pos 23)]),
   ((.fixed 24),[(.neg 24)]),
   ((.fixed 25),[(.neg 25)]),
   ((.fixed 26),[(.neg 26)]),
   ((.fixed 27),[(.neg 27)]),
   ((.fixed 28),[(.pos 28)]),
   ((.fixed 29),[(.pos 29)]),
   ((.fixed 30),[(.pos 30)]),
   ((.fixed 31),[(.pos 31)]),
   ((.fixed 32),[(.pos 32)]),
   ((.fixed 33),[(.pos 33)]),
   ((.fixed 34),[(.pos 34)]),
   ((.exchange 7 41 5),[(.neg 41),(.neg 7),(.pos 0),(.pos 3),(.pos 37)]),
   ((.exchange 7 47 3),[(.neg 47),(.neg 7),(.pos 5),(.pos 46)]),
   ((.exchange 7 49 2),[(.neg 49),(.neg 7),(.pos 6),(.pos 48)]),
   ((.exchange 7 53 0),[(.neg 53),(.neg 7),(.pos 14),(.pos 50)]),
   ((.exchange 7 54 0),[(.neg 54),(.neg 7),(.pos 14),(.pos 50)]),
   ((.exchange 7 56 3),[(.neg 56),(.neg 7),(.pos 26),(.pos 46)]),
   ((.exchange 7 57 3),[(.neg 57),(.neg 7),(.pos 5),(.pos 26),(.pos 46)]),
   ((.exchange 7 65 3),[(.neg 65),(.neg 7),(.pos 26),(.pos 46)]),
   ((.exchange 7 66 3),[(.neg 66),(.neg 7),(.pos 5),(.pos 26),(.pos 46)]),
   ((.exchange 7 67 3),[(.neg 67),(.neg 7),(.pos 26),(.pos 46)]),
   ((.exchange 8 41 5),[(.neg 41),(.neg 8),(.pos 4),(.pos 38)]),
   ((.exchange 8 46 3),[(.neg 46),(.neg 8),(.pos 5),(.pos 47)]),
   ((.exchange 8 48 2),[(.neg 48),(.neg 8),(.pos 6),(.pos 49)]),
   ((.exchange 8 56 3),[(.neg 56),(.neg 8),(.pos 5),(.pos 27),(.pos 47)]),
   ((.exchange 10 41 5),[(.neg 41),(.neg 10),(.pos 1),(.pos 40)]),
   ((.exchange 10 50 0),[(.neg 50),(.neg 10),(.pos 14),(.pos 53)]),
   ((.exchange 10 52 2),[(.neg 52),(.neg 10),(.pos 9),(.pos 51)]),
   ((.exchange 10 54 0),[(.neg 54),(.neg 10),(.pos 14),(.pos 53)]),
   ((.exchange 11 37 5),[(.neg 37),(.neg 11),(.pos 1),(.pos 4),(.pos 41)]),
   ((.exchange 11 38 5),[(.neg 38),(.neg 11),(.pos 4),(.pos 41)]),
   ((.exchange 11 40 5),[(.neg 40),(.neg 11),(.pos 1),(.pos 41)]),
   ((.exchange 11 42 5),[(.neg 42),(.neg 11),(.pos 1),(.pos 4),(.pos 41)]),
   ((.exchange 11 43 5),[(.neg 43),(.neg 11),(.pos 4),(.pos 41)]),
   ((.exchange 11 51 2),[(.neg 51),(.neg 11),(.pos 9),(.pos 52)]),
   ((.exchange 12 41 5),[(.neg 41),(.neg 12),(.pos 2),(.pos 3),(.pos 42)]),
   ((.exchange 12 50 0),[(.neg 50),(.neg 12),(.pos 14),(.pos 54)]),
   ((.exchange 12 53 0),[(.neg 53),(.neg 12),(.pos 14),(.pos 54)]),
   ((.exchange 13 41 5),[(.neg 41),(.neg 13),(.pos 4),(.pos 43)]),
   ((.exchange 17 46 3),[(.neg 46),(.neg 17),(.pos 26),(.pos 56)]),
   ((.exchange 17 47 3),[(.neg 47),(.neg 17),(.pos 15),(.pos 26),(.pos 56)]),
   ((.exchange 17 57 3),[(.neg 57),(.neg 17),(.pos 15),(.pos 56)]),
   ((.exchange 17 59 2),[(.neg 59),(.neg 17),(.pos 16),(.pos 58)]),
   ((.exchange 17 63 0),[(.neg 63),(.neg 17),(.pos 24),(.pos 60)]),
   ((.exchange 17 64 0),[(.neg 64),(.neg 17),(.pos 24),(.pos 60)]),
   ((.exchange 17 65 3),[(.neg 65),(.neg 17),(.pos 26),(.pos 56)]),
   ((.exchange 17 66 3),[(.neg 66),(.neg 17),(.pos 15),(.pos 26),(.pos 56)]),
   ((.exchange 17 67 3),[(.neg 67),(.neg 17),(.pos 26),(.pos 56)]),
   ((.exchange 18 46 3),[(.neg 46),(.neg 18),(.pos 15),(.pos 27),(.pos 57)]),
   ((.exchange 18 56 3),[(.neg 56),(.neg 18),(.pos 15),(.pos 57)]),
   ((.exchange 18 58 2),[(.neg 58),(.neg 18),(.pos 16),(.pos 59)]),
   ((.exchange 20 60 0),[(.neg 60),(.neg 20),(.pos 24),(.pos 63)]),
   ((.exchange 20 62 2),[(.neg 62),(.neg 20),(.pos 19),(.pos 61)]),
   ((.exchange 20 64 0),[(.neg 64),(.neg 20),(.pos 24),(.pos 63)]),
   ((.exchange 21 61 2),[(.neg 61),(.neg 21),(.pos 19),(.pos 62)]),
   ((.exchange 22 60 0),[(.neg 60),(.neg 22),(.pos 24),(.pos 64)]),
   ((.exchange 22 63 0),[(.neg 63),(.neg 22),(.pos 24),(.pos 64)]),
   ((.exchange 28 46 3),[(.neg 46),(.neg 28),(.pos 26),(.pos 65)]),
   ((.exchange 28 56 3),[(.neg 56),(.neg 28),(.pos 26),(.pos 65)]),
   ((.exchange 29 46 3),[(.neg 46),(.neg 29),(.pos 25),(.pos 27),(.pos 66)]),
   ((.exchange 29 56 3),[(.neg 56),(.neg 29),(.pos 25),(.pos 27),(.pos 66)]),
   ((.exchange 30 46 3),[(.neg 46),(.neg 30),(.pos 26),(.pos 67)]),
   ((.exchange 30 56 3),[(.neg 56),(.neg 30),(.pos 26),(.pos 67)]),
   ((.exchange 35 7 7),[(.neg 35),(.neg 7),(.pos 0),(.pos 5)]),
   ((.exchange 36 7 7),[(.neg 36),(.neg 7),(.pos 0),(.pos 6)]),
   ((.exchange 37 28 2),[(.neg 37),(.neg 28),(.pos 48),(.pos 58)]),
   ((.exchange 37 30 0),[(.neg 37),(.neg 30),(.pos 50),(.pos 60)]),
   ((.exchange 37 68 2),[(.neg 68),(.neg 37),(.pos 48),(.pos 58)]),
   ((.exchange 38 28 2),[(.neg 38),(.neg 28),(.pos 36),(.pos 49),(.pos 59)]),
   ((.exchange 38 34 1),[(.neg 38),(.neg 34),(.pos 44),(.pos 50),(.pos 60)]),
   ((.exchange 38 67 1),[(.neg 67),(.neg 38),(.pos 50),(.pos 60)]),
   ((.exchange 38 68 2),[(.neg 68),(.neg 38),(.pos 49),(.pos 59)]),
   ((.exchange 39 7 7),[(.neg 39),(.neg 7),(.pos 1),(.pos 2),(.pos 9)]),
   ((.exchange 40 31 2),[(.neg 40),(.neg 31),(.pos 51),(.pos 61)]),
   ((.exchange 40 33 0),[(.neg 40),(.neg 33),(.pos 53),(.pos 63)]),
   ((.exchange 40 34 0),[(.neg 40),(.neg 34),(.pos 44),(.pos 53),(.pos 63)]),
   ((.exchange 41 31 2),[(.neg 41),(.neg 31),(.pos 39),(.pos 52),(.pos 62)]),
   ((.exchange 41 67 1),[(.neg 67),(.neg 41),(.pos 53),(.pos 63)]),
   ((.exchange 42 28 4),[(.neg 42),(.neg 28),(.pos 48),(.pos 58)]),
   ((.exchange 42 34 0),[(.neg 42),(.neg 34),(.pos 54),(.pos 64)]),
   ((.exchange 43 29 4),[(.neg 43),(.neg 29),(.pos 49),(.pos 59)]),
   ((.exchange 43 34 1),[(.neg 43),(.neg 34),(.pos 54),(.pos 64)]),
   ((.exchange 43 67 1),[(.neg 67),(.neg 43),(.pos 44),(.pos 54),(.pos 64)]),
   ((.exchange 44 7 7),[(.neg 44),(.neg 7),(.pos 3),(.pos 14)]),
   ((.exchange 45 7 7),[(.neg 45),(.neg 7),(.pos 5),(.pos 6)]),
   ((.exchange 48 10 3),[(.neg 48),(.neg 10),(.pos 46),(.pos 51)]),
   ((.exchange 48 17 5),[(.neg 48),(.neg 17),(.pos 37),(.pos 58)]),
   ((.exchange 48 30 0),[(.neg 48),(.neg 30),(.pos 50),(.pos 68)]),
   ((.exchange 48 34 0),[(.neg 48),(.neg 34),(.pos 54),(.pos 68)]),
   ((.exchange 48 57 5),[(.neg 57),(.neg 48),(.pos 36),(.pos 37),(.pos 58)]),
   ((.exchange 48 64 0),[(.neg 64),(.neg 48),(.pos 54),(.pos 68)]),
   ((.exchange 49 10 3),[(.neg 49),(.neg 10),(.pos 45),(.pos 47),(.pos 52)]),
   ((.exchange 49 17 5),[(.neg 49),(.neg 17),(.pos 36),(.pos 38),(.pos 59)]),
   ((.exchange 49 34 1),[(.neg 49),(.neg 34),(.pos 54),(.pos 68)]),
   ((.exchange 49 57 5),[(.neg 57),(.neg 49),(.pos 38),(.pos 59)]),
   ((.exchange 49 58 1),[(.neg 58),(.neg 49),(.pos 48),(.pos 68)]),
   ((.exchange 49 64 1),[(.neg 64),(.neg 49),(.pos 54),(.pos 68)]),
   ((.exchange 49 67 1),[(.neg 67),(.neg 49),(.pos 50),(.pos 68)]),
   ((.exchange 49 69 1),[(.neg 69),(.neg 49),(.pos 54),(.pos 68)]),
   ((.exchange 50 22 5),[(.neg 50),(.neg 22),(.pos 37),(.pos 44),(.pos 60)]),
   ((.exchange 50 28 2),[(.neg 50),(.neg 28),(.pos 48),(.pos 68)]),
   ((.exchange 50 59 2),[(.neg 59),(.neg 50),(.pos 49),(.pos 68)]),
   ((.exchange 50 63 3),[(.neg 63),(.neg 50),(.pos 53),(.pos 67)]),
   ((.exchange 51 17 5),[(.neg 51),(.neg 17),(.pos 40),(.pos 42),(.pos 61)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_1 : List (Origin 70 51 × List Sat.Literal) :=
  [((.exchange 51 21 5),[(.neg 51),(.neg 21),(.pos 39),(.pos 40),(.pos 61)]),
   ((.exchange 51 30 4),[(.neg 51),(.neg 30),(.pos 46),(.pos 48),(.pos 65)]),
   ((.exchange 51 33 0),[(.neg 51),(.neg 33),(.pos 53),(.pos 69)]),
   ((.exchange 51 34 0),[(.neg 51),(.neg 34),(.pos 54),(.pos 69)]),
   ((.exchange 51 59 4),[(.neg 59),(.neg 51),(.pos 45),(.pos 48),(.pos 65)]),
   ((.exchange 51 63 0),[(.neg 63),(.neg 51),(.pos 53),(.pos 69)]),
   ((.exchange 52 17 5),[(.neg 52),(.neg 17),(.pos 39),(.pos 41),(.pos 43),(.pos 62)]),
   ((.exchange 52 21 5),[(.neg 52),(.neg 21),(.pos 41),(.pos 62)]),
   ((.exchange 52 28 4),[(.neg 52),(.neg 28),(.pos 45),(.pos 49),(.pos 66)]),
   ((.exchange 52 34 1),[(.neg 52),(.neg 34),(.pos 54),(.pos 69)]),
   ((.exchange 52 58 4),[(.neg 58),(.neg 52),(.pos 45),(.pos 49),(.pos 66)]),
   ((.exchange 52 59 4),[(.neg 59),(.neg 52),(.pos 49),(.pos 66)]),
   ((.exchange 52 63 5),[(.neg 63),(.neg 52),(.pos 41),(.pos 62)]),
   ((.exchange 52 68 1),[(.neg 68),(.neg 52),(.pos 54),(.pos 69)]),
   ((.exchange 53 12 2),[(.neg 53),(.neg 12),(.pos 51),(.pos 54)]),
   ((.exchange 53 23 5),[(.neg 53),(.neg 23),(.pos 41),(.pos 44),(.pos 63)]),
   ((.exchange 54 7 4),[(.neg 54),(.neg 7),(.pos 48),(.pos 50)]),
   ((.exchange 54 22 5),[(.neg 54),(.neg 22),(.pos 42),(.pos 64)]),
   ((.exchange 54 28 4),[(.neg 54),(.neg 28),(.pos 48),(.pos 68)]),
   ((.exchange 54 29 4),[(.neg 54),(.neg 29),(.pos 49),(.pos 68)]),
   ((.exchange 54 59 4),[(.neg 59),(.neg 54),(.pos 49),(.pos 68)]),
   ((.exchange 54 61 3),[(.neg 61),(.neg 54),(.pos 51),(.pos 69)]),
   ((.exchange 54 62 3),[(.neg 62),(.neg 54),(.pos 52),(.pos 69)]),
   ((.exchange 55 7 6),[(.neg 55),(.neg 7),(.pos 35),(.pos 36),(.pos 45)]),
   ((.exchange 56 22 2),[(.neg 56),(.neg 22),(.pos 58),(.pos 61)]),
   ((.exchange 56 64 2),[(.neg 64),(.neg 56),(.pos 58),(.pos 61)]),
   ((.exchange 57 22 2),[(.neg 57),(.neg 22),(.pos 55),(.pos 59),(.pos 62)]),
   ((.exchange 57 64 2),[(.neg 64),(.neg 57),(.pos 59),(.pos 62)]),
   ((.exchange 58 7 6),[(.neg 58),(.neg 7),(.pos 37),(.pos 48)]),
   ((.exchange 58 11 6),[(.neg 58),(.neg 11),(.pos 36),(.pos 37),(.pos 42),(.pos 48)]),
   ((.exchange 58 30 0),[(.neg 58),(.neg 30),(.pos 60),(.pos 68)]),
   ((.exchange 58 34 0),[(.neg 58),(.neg 34),(.pos 64),(.pos 68)]),
   ((.exchange 58 52 3),[(.neg 58),(.neg 52),(.pos 55),(.pos 61),(.pos 65)]),
   ((.exchange 58 53 3),[(.neg 58),(.neg 53),(.pos 56),(.pos 61),(.pos 65)]),
   ((.exchange 58 63 3),[(.neg 63),(.neg 58),(.pos 56),(.pos 61)]),
   ((.exchange 59 7 6),[(.neg 59),(.neg 7),(.pos 36),(.pos 38),(.pos 49)]),
   ((.exchange 59 11 6),[(.neg 59),(.neg 11),(.pos 38),(.pos 43),(.pos 49)]),
   ((.exchange 59 30 1),[(.neg 59),(.neg 30),(.pos 60),(.pos 68)]),
   ((.exchange 59 34 1),[(.neg 59),(.neg 34),(.pos 64),(.pos 68)]),
   ((.exchange 59 53 3),[(.neg 59),(.neg 53),(.pos 57),(.pos 62),(.pos 66)]),
   ((.exchange 59 53 6),[(.neg 59),(.neg 53),(.pos 38),(.pos 43),(.pos 49)]),
   ((.exchange 59 63 3),[(.neg 63),(.neg 59),(.pos 57),(.pos 62)]),
   ((.exchange 59 67 1),[(.neg 67),(.neg 59),(.pos 60),(.pos 68)]),
   ((.exchange 59 69 1),[(.neg 69),(.neg 59),(.pos 64),(.pos 68)]),
   ((.exchange 60 7 6),[(.neg 60),(.neg 7),(.pos 37),(.pos 50)]),
   ((.exchange 60 12 6),[(.neg 60),(.neg 12),(.pos 37),(.pos 44),(.pos 50)]),
   ((.exchange 60 29 2),[(.neg 60),(.neg 29),(.pos 59),(.pos 68)]),
   ((.exchange 60 47 6),[(.neg 60),(.neg 47),(.pos 38),(.pos 50)]),
   ((.exchange 60 49 2),[(.neg 60),(.neg 49),(.pos 59),(.pos 68)]),
   ((.exchange 60 66 2),[(.neg 66),(.neg 60),(.pos 59),(.pos 68)]),
   ((.exchange 61 7 6),[(.neg 61),(.neg 7),(.pos 40),(.pos 42),(.pos 51)]),
   ((.exchange 61 11 6),[(.neg 61),(.neg 11),(.pos 39),(.pos 40),(.pos 51)]),
   ((.exchange 61 28 4),[(.neg 61),(.neg 28),(.pos 58),(.pos 65)]),
   ((.exchange 61 30 0),[(.neg 61),(.neg 30),(.pos 63),(.pos 64),(.pos 69)]),
   ((.exchange 61 33 0),[(.neg 61),(.neg 33),(.pos 63),(.pos 69)]),
   ((.exchange 61 37 4),[(.neg 61),(.neg 37),(.pos 56),(.pos 58)]),
   ((.exchange 61 50 0),[(.neg 61),(.neg 50),(.pos 63),(.pos 64),(.pos 69)]),
   ((.exchange 61 52 6),[(.neg 61),(.neg 52),(.pos 39),(.pos 51)]),
   ((.exchange 61 53 6),[(.neg 61),(.neg 53),(.pos 40),(.pos 51)]),
   ((.exchange 61 68 0),[(.neg 68),(.neg 61),(.pos 64),(.pos 69)]),
   ((.exchange 62 7 6),[(.neg 62),(.neg 7),(.pos 39),(.pos 41),(.pos 43),(.pos 52)]),
   ((.exchange 62 11 6),[(.neg 62),(.neg 11),(.pos 41),(.pos 52)]),
   ((.exchange 62 28 4),[(.neg 62),(.neg 28),(.pos 55),(.pos 59),(.pos 66)]),
   ((.exchange 62 30 1),[(.neg 62),(.neg 30),(.pos 63),(.pos 64),(.pos 69)]),
   ((.exchange 62 37 4),[(.neg 62),(.neg 37),(.pos 55),(.pos 57),(.pos 59)]),
   ((.exchange 62 54 6),[(.neg 62),(.neg 54),(.pos 43),(.pos 52)]),
   ((.exchange 62 68 1),[(.neg 68),(.neg 62),(.pos 64),(.pos 69)]),
   ((.exchange 63 13 6),[(.neg 63),(.neg 13),(.pos 41),(.pos 44),(.pos 53)]),
   ((.exchange 63 31 2),[(.neg 63),(.neg 31),(.pos 61),(.pos 69)]),
   ((.exchange 63 32 2),[(.neg 63),(.neg 32),(.pos 62),(.pos 69)]),
   ((.exchange 63 47 6),[(.neg 63),(.neg 47),(.pos 41),(.pos 53)]),
   ((.exchange 63 48 6),[(.neg 63),(.neg 48),(.pos 40),(.pos 44),(.pos 53)]),
   ((.exchange 63 50 6),[(.neg 63),(.neg 50),(.pos 44),(.pos 53)]),
   ((.exchange 63 52 2),[(.neg 63),(.neg 52),(.pos 62),(.pos 69)]),
   ((.exchange 64 7 6),[(.neg 64),(.neg 7),(.pos 42),(.pos 44),(.pos 54)]),
   ((.exchange 64 12 6),[(.neg 64),(.neg 12),(.pos 42),(.pos 54)]),
   ((.exchange 64 47 6),[(.neg 64),(.neg 47),(.pos 43),(.pos 44),(.pos 54)]),
   ((.exchange 64 48 4),[(.neg 64),(.neg 48),(.pos 58),(.pos 68)]),
   ((.exchange 64 49 4),[(.neg 64),(.neg 49),(.pos 59),(.pos 68)]),
   ((.exchange 64 66 4),[(.neg 66),(.neg 64),(.pos 59),(.pos 68)]),
   ((.exchange 65 34 0),[(.neg 65),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 65 42 6),[(.neg 65),(.neg 42),(.pos 48),(.pos 51)]),
   ((.exchange 66 42 6),[(.neg 66),(.neg 42),(.pos 45),(.pos 49),(.pos 52)]),
   ((.exchange 67 34 2),[(.neg 67),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 68 10 3),[(.neg 68),(.neg 10),(.pos 65),(.pos 67),(.pos 69)]),
   ((.exchange 68 12 6),[(.neg 68),(.neg 12),(.pos 48),(.pos 54)]),
   ((.exchange 68 22 5),[(.neg 68),(.neg 22),(.pos 58),(.pos 64)]),
   ((.exchange 68 23 5),[(.neg 68),(.neg 23),(.pos 59),(.pos 64)]),
   ((.exchange 68 37 6),[(.neg 68),(.neg 37),(.pos 48),(.pos 50)]),
   ((.exchange 68 38 5),[(.neg 68),(.neg 38),(.pos 59),(.pos 60)]),
   ((.exchange 68 42 5),[(.neg 68),(.neg 42),(.pos 58),(.pos 64)]),
   ((.exchange 68 42 6),[(.neg 68),(.neg 42),(.pos 48),(.pos 54)]),
   ((.exchange 68 43 5),[(.neg 68),(.neg 43),(.pos 59),(.pos 64)]),
   ((.exchange 68 43 6),[(.neg 68),(.neg 43),(.pos 49),(.pos 54)]),
   ((.exchange 68 46 6),[(.neg 68),(.neg 46),(.pos 48),(.pos 50)]),
   ((.exchange 68 56 5),[(.neg 68),(.neg 56),(.pos 58),(.pos 60)]),
   ((.exchange 68 57 5),[(.neg 68),(.neg 57),(.pos 59),(.pos 60)]),
   ((.exchange 69 17 5),[(.neg 69),(.neg 17),(.pos 61),(.pos 63),(.pos 64)]),
   ((.exchange 69 22 5),[(.neg 69),(.neg 22),(.pos 61),(.pos 64)]),
   ((.exchange 69 23 5),[(.neg 69),(.neg 23),(.pos 62),(.pos 64)]),
   ((.exchange 69 28 4),[(.neg 69),(.neg 28),(.pos 65),(.pos 68)]),
   ((.exchange 69 30 4),[(.neg 69),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 69 42 5),[(.neg 69),(.neg 42),(.pos 61),(.pos 64)]),
   ((.exchange 69 42 6),[(.neg 69),(.neg 42),(.pos 51),(.pos 54)]),
   ((.exchange 69 43 5),[(.neg 69),(.neg 43),(.pos 62),(.pos 64)]),
   ((.exchange 69 43 6),[(.neg 69),(.neg 43),(.pos 52),(.pos 54)]),
   (.newPoint,[(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 0),[(.neg 69),(.neg 68),(.neg 64),(.neg 63),(.neg 60),(.neg 54),(.neg 53),(.neg 50),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 51),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 61),(.pos 62),(.pos 65),(.pos 66),(.pos 67)]),
   ((.excluded 1),[(.neg 69),(.neg 68),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67)]),
   ((.excluded 2),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 3),[(.neg 69),(.neg 68),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57),(.pos 65),(.pos 66),(.pos 67)]),
   ((.excluded 4),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 57),(.neg 56),(.neg 52),(.neg 51),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 58),(.pos 59),(.pos 60),(.pos 63),(.pos 64),(.pos 68)]),
   ((.excluded 5),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 6),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 63),(.pos 64)]),
   ((.excluded 7),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 58),(.pos 59),(.pos 69)]),
   ((.excluded 8),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 58),(.pos 59)]),
   ((.excluded 9),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 61),(.pos 62),(.pos 68)]),
   ((.excluded 10),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 11),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 55),(.pos 68)]),
   ((.excluded 12),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 55),(.pos 69)]),
   ((.excluded 13),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 55)]),
   ((.excluded 14),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 15),[(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 16),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 17),[(.neg 69),(.neg 68),(.neg 64),(.neg 63),(.neg 60),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 61),(.pos 62),(.pos 65),(.pos 66),(.pos 67)]),
   ((.excluded 18),[(.neg 69),(.neg 68),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 65),(.pos 66),(.pos 67)]),
   ((.excluded 19),[(.neg 69),(.neg 68),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 50),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 51),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67)]),
   ((.excluded 20),[(.neg 69),(.neg 68),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67)])]

theorem certificates_1_valid : ∀ oc ∈ certificates_1,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_2 : List (Origin 70 51 × List Sat.Literal) :=
  [((.excluded 21),[(.neg 69),(.neg 68),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 50),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 51),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 65),(.pos 66),(.pos 67)]),
   ((.excluded 22),[(.neg 69),(.neg 68),(.neg 64),(.neg 63),(.neg 60),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 61),(.pos 62),(.pos 65),(.pos 66),(.pos 67)]),
   ((.excluded 23),[(.neg 69),(.neg 68),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57),(.pos 65),(.pos 66),(.pos 67)]),
   ((.excluded 24),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 52),(.neg 51),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 61),(.pos 62),(.pos 68)]),
   ((.excluded 25),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 52),(.neg 51),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 68)]),
   ((.excluded 26),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 58),(.pos 59),(.pos 69)]),
   ((.excluded 27),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 69)]),
   ((.excluded 28),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 58),(.pos 59)]),
   ((.excluded 29),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 30),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 53),(.pos 54),(.pos 55)]),
   ((.excluded 31),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 58),(.pos 59),(.pos 60),(.pos 63),(.pos 64),(.pos 68)]),
   ((.excluded 32),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 58),(.pos 59),(.pos 60),(.pos 63),(.pos 64),(.pos 68)]),
   ((.excluded 33),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 34),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 35),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 60),(.pos 63),(.pos 64)]),
   ((.excluded 36),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 60),(.pos 63),(.pos 64)]),
   ((.excluded 37),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 60),(.pos 63),(.pos 64)]),
   ((.excluded 38),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 39),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 69)]),
   ((.excluded 40),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 55)]),
   ((.excluded 41),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 61),(.pos 62),(.pos 68)]),
   ((.excluded 42),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 43),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 68)]),
   ((.excluded 44),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 68)]),
   ((.excluded 45),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 58),(.pos 59)]),
   ((.excluded 46),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 51),(.pos 52),(.pos 55)]),
   ((.excluded 47),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 58),(.pos 59),(.pos 69)]),
   ((.excluded 48),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 58),(.pos 59)]),
   ((.excluded 49),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 69)]),
   ((.excluded 50),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55)])]

theorem certificates_2_valid : ∀ oc ∈ certificates_2,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



theorem witness_0 : ∀ j : Fin 51,
    let w : Fin 51 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 51,
      let w : Fin 51 := ⟨0 + j.val,by omega⟩
      target w < MatroidCatalogue.count 8 4 ∧
        Papers.RationalityTen.MatroidChecked.FastSemanticChecks.RawWitness 8 (N7R4.familyMasks.get 39)
        (fun i : Fin 70 => N8R4.gridMasks.get i.val) newIndex (models w)
        (N8R4.familyMasks.get (target w)) (permutation w) := by
    refine (Fin.forall_fin_add (m := 25) (n := 26) _).2 ⟨?_, ?_⟩
    · refine (Fin.forall_fin_add (m := 12) (n := 13) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 6) (n := 6) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 3) (n := 3) _).2 ⟨?_, ?_⟩
          · decide +kernel
          · decide +kernel
        · refine (Fin.forall_fin_add (m := 3) (n := 3) _).2 ⟨?_, ?_⟩
          · decide +kernel
          · decide +kernel
      · refine (Fin.forall_fin_add (m := 6) (n := 7) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 3) (n := 3) _).2 ⟨?_, ?_⟩
          · decide +kernel
          · decide +kernel
        · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
          · decide +kernel
          · decide +kernel
    · refine (Fin.forall_fin_add (m := 13) (n := 13) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 6) (n := 7) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 3) (n := 3) _).2 ⟨?_, ?_⟩
          · decide +kernel
          · decide +kernel
        · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
          · decide +kernel
          · decide +kernel
      · refine (Fin.forall_fin_add (m := 6) (n := 7) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 3) (n := 3) _).2 ⟨?_, ?_⟩
          · decide +kernel
          · decide +kernel
        · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
          · decide +kernel
          · decide +kernel
  intro j
  have hj := hfast j
  exact ⟨hj.1,Papers.RationalityTen.MatroidChecked.FastSemanticChecks.rawWitness_sound 8 _ _ _ _ _ _ hj.2⟩


end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C39

/- Source: MatroidCatalogue/Cases/N8R4C39Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C39

noncomputable def certificates : List (Origin 70 51 × List Sat.Literal) :=
  certificates_0 ++ certificates_1 ++ certificates_2

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  intro oc hoc
  simp only [certificates,List.mem_append,or_assoc] at hoc
  rcases hoc with h0 | h1 | h2
  · exact certificates_0_valid oc h0
  · exact certificates_1_valid oc h1
  · exact certificates_2_valid oc h2

theorem models_valid : ∀ w : Fin 51,
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 51) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 8) 4)
    (hold : M.bases.filter ((7 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 8 4, IsomorphicWithin 8 M.bases B := by
  apply extension_covered_of_certificate (n:=7) (r:=4) (by decide)
    catalogue old U newIndex models certificates
    N8R4.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C39.formula []
    exact Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C39.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 8 4 (target w),family_mem 8 4 (target w) hw.1,?_⟩
    exact validWitness_sound 8 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C39


end
end
end BundlePart3

section BundlePart4
/- Source: MatroidChecked/SemanticChunks/Cases05Part05.lean -/




@[expose] public section
noncomputable section

/- Source: MatroidCatalogue/Cases/N8R4C40Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C40

abbrev U := N8R4.grid
noncomputable def old : Finset (Finset (Fin 8)) := N7R4.family 40
noncomputable def newIndexTree : Table ℕ := (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf 35) (.leaf 36)) (.node 3 (.leaf 37) (.leaf 38))) (.node 6 (.node 5 (.leaf 39) (.leaf 40)) (.node 7 (.leaf 41) (.leaf 42)))) (.node 12 (.node 10 (.node 9 (.leaf 43) (.leaf 44)) (.node 11 (.leaf 45) (.leaf 46))) (.node 14 (.node 13 (.leaf 47) (.leaf 48)) (.node 15 (.leaf 49) (.node 16 (.leaf 50) (.leaf 51)))))) (.node 26 (.node 21 (.node 19 (.node 18 (.leaf 52) (.leaf 53)) (.node 20 (.leaf 54) (.leaf 55))) (.node 23 (.node 22 (.leaf 56) (.leaf 57)) (.node 24 (.leaf 58) (.node 25 (.leaf 59) (.leaf 60))))) (.node 30 (.node 28 (.node 27 (.leaf 61) (.leaf 62)) (.node 29 (.leaf 63) (.leaf 64))) (.node 32 (.node 31 (.leaf 65) (.leaf 66)) (.node 33 (.leaf 67) (.node 34 (.leaf 68) (.leaf 69)))))))
noncomputable def newIndex (i : Fin 35) : Fin 70 := Fin.ofNat 70 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 45 (.node 22 (.node 11 (.node 5 (.node 2 (.node 1 (.leaf (30904451072,94,6248648)) (.leaf (29217742848,109,4151322))) (.node 3 (.leaf (25762455552,130,8345736)) (.node 4 (.leaf (17172520960,130,8342152)) (.leaf (34352390144,131,8345736))))) (.node 8 (.node 6 (.leaf (24903882752,109,4149530)) (.node 7 (.leaf (1072691200,167,6248648)) (.leaf (25567229952,130,8333640)))) (.node 9 (.leaf (25768753152,171,12534984)) (.node 10 (.leaf (16137615360,109,4131610)) (.leaf (29862197248,130,8334088)))))) (.node 16 (.node 13 (.node 12 (.leaf (34157164544,131,8334088)) (.leaf (30038530048,130,8344840))) (.node 14 (.leaf (17153628160,130,8340808)) (.node 15 (.leaf (34333497344,131,8344840)) (.leaf (30297782272,145,6248648))))) (.node 19 (.node 17 (.leaf (33519007744,146,12535432)) (.node 18 (.leaf (31137462272,168,6248648)) (.leaf (30063720448,171,12535432)))) (.node 20 (.leaf (17178818560,171,12527816)) (.node 21 (.leaf (34358687744,172,12535432)) (.leaf (1071645164,241,8219400))))))) (.node 33 (.node 27 (.node 24 (.node 23 (.leaf (1047020,241,7072520)) (.leaf (1072691692,278,11664520))) (.node 25 (.leaf (30298374636,246,6155016)) (.node 26 (.leaf (31137235436,247,8219400)) (.leaf (30298601964,269,14141064))))) (.node 30 (.node 28 (.leaf (30903859692,246,5237512)) (.node 29 (.leaf (30904678892,247,7072520)) (.leaf (31136643564,269,14599816)))) (.node 31 (.leaf (31137462764,279,16434824)) (.node 32 (.leaf (30037729772,267,10413704)) (.leaf (29861569004,267,10402952)))))) (.node 39 (.node 36 (.node 34 (.leaf (30062895596,268,12478088)) (.node 35 (.leaf (25761618412,267,10413256)) (.leaf (25566583276,267,10401160)))) (.node 37 (.leaf (25767909868,268,12477640)) (.node 38 (.leaf (17171511788,267,10398920)) (.leaf (17152637420,267,10397576))))) (.node 42 (.node 40 (.leaf (17177803244,268,12463304)) (.node 41 (.leaf (34351577580,271,12535432)) (.leaf (34332703212,271,12534984)))) (.node 43 (.leaf (34156542444,271,12527816)) (.node 44 (.leaf (34357869036,272,14599816)) (.leaf (29218544108,267,9954952)))))))) (.node 68 (.node 56 (.node 50 (.node 47 (.node 46 (.leaf (29218372076,267,9944200)) (.leaf (29218568684,268,11789960))) (.node 48 (.leaf (24904720876,267,9954504)) (.node 49 (.leaf (24904530412,267,9942408)) (.leaf (24904727020,268,11789512))))) (.node 53 (.node 51 (.leaf (16138625516,267,9940168)) (.node 52 (.leaf (16138607084,267,9938824)) (.leaf (16138631660,268,11775176)))) (.node 54 (.leaf (33519821292,271,12306056)) (.node 55 (.leaf (33519802860,271,12305608)) (.leaf (33519630828,271,12298440)))))) (.node 62 (.node 59 (.node 57 (.leaf (33519827436,272,14141064)) (.node 58 (.leaf (17153647084,274,10213000)) (.leaf (34333516268,275,10213000)))) (.node 60 (.leaf (17178812908,276,14596232)) (.node 61 (.leaf (25567420908,274,10205832)) (.leaf (34157355500,275,10205832))))) (.node 65 (.node 63 (.leaf (25768747500,276,14599816)) (.node 64 (.leaf (34358682092,277,14599816)) (.leaf (17153653228,276,14136584)))) (.node 66 (.leaf (30038358508,274,10433864)) (.node 67 (.leaf (34333325804,275,10433864)) (.leaf (30038555116,276,14140616))))))) (.node 79 (.node 73 (.node 70 (.node 69 (.leaf (34333522412,277,14140616)) (.leaf (17172503020,274,10442376))) (.node 71 (.leaf (17178794476,276,14595336)) (.node 72 (.leaf (17172527596,276,14137480)) (.leaf (17178819052,280,16427208))))) (.node 76 (.node 74 (.leaf (30063524332,276,14592200)) (.node 75 (.leaf (25762265580,274,10435208)) (.leaf (34352200172,275,10435208)))) (.node 77 (.leaf (25768557036,276,14591752)) (.node 78 (.leaf (34358491628,277,14592200)) (.leaf (34352372204,275,10442376)))))) (.node 85 (.node 82 (.node 80 (.leaf (25762462188,276,14141064)) (.node 81 (.leaf (34352396780,277,14141064)) (.leaf (25567427052,276,14133000)))) (.node 83 (.leaf (25768753644,280,16434376)) (.node 84 (.leaf (29862369772,274,10204488)) (.leaf (34157337068,275,10204488))))) (.node 88 (.node 86 (.leaf (30063696364,276,14599368)) (.node 87 (.leaf (34358663660,277,14599368)) (.leaf (29862394348,276,14133448)))) (.node 89 (.leaf (34157361644,277,14133448)) (.node 90 (.leaf (30063720940,280,16434824)) (.leaf (34358688236,281,16434824)))))))))

noncomputable def models (i : Fin 91) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 91) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 91) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 70, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (7 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 70, (7 : Fin 8) ∈ U i → ∃ j : Fin 35, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C40

/- Source: MatroidCatalogue/Cases/N8R4C40Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C40


noncomputable def certificates_0 : List (Origin 70 91 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.neg 2)]),
   ((.fixed 3),[(.neg 3)]),
   ((.fixed 4),[(.neg 4)]),
   ((.fixed 5),[(.neg 5)]),
   ((.fixed 6),[(.neg 6)]),
   ((.fixed 7),[(.pos 7)]),
   ((.fixed 8),[(.pos 8)]),
   ((.fixed 9),[(.neg 9)]),
   ((.fixed 10),[(.pos 10)]),
   ((.fixed 11),[(.pos 11)]),
   ((.fixed 12),[(.pos 12)]),
   ((.fixed 13),[(.pos 13)]),
   ((.fixed 14),[(.neg 14)]),
   ((.fixed 15),[(.neg 15)]),
   ((.fixed 16),[(.neg 16)]),
   ((.fixed 17),[(.pos 17)]),
   ((.fixed 18),[(.pos 18)]),
   ((.fixed 19),[(.neg 19)]),
   ((.fixed 20),[(.pos 20)]),
   ((.fixed 21),[(.pos 21)]),
   ((.fixed 22),[(.pos 22)]),
   ((.fixed 23),[(.pos 23)]),
   ((.fixed 24),[(.neg 24)]),
   ((.fixed 25),[(.neg 25)]),
   ((.fixed 26),[(.pos 26)]),
   ((.fixed 27),[(.pos 27)]),
   ((.fixed 28),[(.pos 28)]),
   ((.fixed 29),[(.pos 29)]),
   ((.fixed 30),[(.pos 30)]),
   ((.fixed 31),[(.pos 31)]),
   ((.fixed 32),[(.pos 32)]),
   ((.fixed 33),[(.pos 33)]),
   ((.fixed 34),[(.pos 34)]),
   ((.exchange 7 41 5),[(.neg 41),(.neg 7),(.pos 0),(.pos 3),(.pos 37)]),
   ((.exchange 7 47 3),[(.neg 47),(.neg 7),(.pos 5),(.pos 46)]),
   ((.exchange 7 49 2),[(.neg 49),(.neg 7),(.pos 6),(.pos 48)]),
   ((.exchange 7 53 0),[(.neg 53),(.neg 7),(.pos 14),(.pos 50)]),
   ((.exchange 7 54 0),[(.neg 54),(.neg 7),(.pos 14),(.pos 50)]),
   ((.exchange 8 41 5),[(.neg 41),(.neg 8),(.pos 4),(.pos 38)]),
   ((.exchange 8 46 3),[(.neg 46),(.neg 8),(.pos 5),(.pos 47)]),
   ((.exchange 8 48 2),[(.neg 48),(.neg 8),(.pos 6),(.pos 49)]),
   ((.exchange 10 41 5),[(.neg 41),(.neg 10),(.pos 1),(.pos 40)]),
   ((.exchange 10 50 0),[(.neg 50),(.neg 10),(.pos 14),(.pos 53)]),
   ((.exchange 10 52 2),[(.neg 52),(.neg 10),(.pos 9),(.pos 51)]),
   ((.exchange 10 54 0),[(.neg 54),(.neg 10),(.pos 14),(.pos 53)]),
   ((.exchange 11 37 5),[(.neg 37),(.neg 11),(.pos 1),(.pos 4),(.pos 41)]),
   ((.exchange 11 38 5),[(.neg 38),(.neg 11),(.pos 4),(.pos 41)]),
   ((.exchange 11 40 5),[(.neg 40),(.neg 11),(.pos 1),(.pos 41)]),
   ((.exchange 11 42 5),[(.neg 42),(.neg 11),(.pos 1),(.pos 4),(.pos 41)]),
   ((.exchange 11 43 5),[(.neg 43),(.neg 11),(.pos 4),(.pos 41)]),
   ((.exchange 11 51 2),[(.neg 51),(.neg 11),(.pos 9),(.pos 52)]),
   ((.exchange 12 41 5),[(.neg 41),(.neg 12),(.pos 2),(.pos 3),(.pos 42)]),
   ((.exchange 12 50 0),[(.neg 50),(.neg 12),(.pos 14),(.pos 54)]),
   ((.exchange 12 53 0),[(.neg 53),(.neg 12),(.pos 14),(.pos 54)]),
   ((.exchange 13 41 5),[(.neg 41),(.neg 13),(.pos 4),(.pos 43)]),
   ((.exchange 17 57 3),[(.neg 57),(.neg 17),(.pos 15),(.pos 56)]),
   ((.exchange 17 59 2),[(.neg 59),(.neg 17),(.pos 16),(.pos 58)]),
   ((.exchange 17 63 0),[(.neg 63),(.neg 17),(.pos 24),(.pos 60)]),
   ((.exchange 17 64 0),[(.neg 64),(.neg 17),(.pos 24),(.pos 60)]),
   ((.exchange 18 56 3),[(.neg 56),(.neg 18),(.pos 15),(.pos 57)]),
   ((.exchange 18 58 2),[(.neg 58),(.neg 18),(.pos 16),(.pos 59)]),
   ((.exchange 20 60 0),[(.neg 60),(.neg 20),(.pos 24),(.pos 63)]),
   ((.exchange 20 62 2),[(.neg 62),(.neg 20),(.pos 19),(.pos 61)]),
   ((.exchange 20 64 0),[(.neg 64),(.neg 20),(.pos 24),(.pos 63)]),
   ((.exchange 21 61 2),[(.neg 61),(.neg 21),(.pos 19),(.pos 62)]),
   ((.exchange 22 60 0),[(.neg 60),(.neg 22),(.pos 24),(.pos 64)]),
   ((.exchange 22 63 0),[(.neg 63),(.neg 22),(.pos 24),(.pos 64)]),
   ((.exchange 26 66 2),[(.neg 66),(.neg 26),(.pos 25),(.pos 65)]),
   ((.exchange 27 65 2),[(.neg 65),(.neg 27),(.pos 25),(.pos 66)]),
   ((.exchange 35 7 7),[(.neg 35),(.neg 7),(.pos 0),(.pos 5)]),
   ((.exchange 36 7 7),[(.neg 36),(.neg 7),(.pos 0),(.pos 6)]),
   ((.exchange 37 28 2),[(.neg 37),(.neg 28),(.pos 48),(.pos 58)]),
   ((.exchange 37 30 0),[(.neg 37),(.neg 30),(.pos 50),(.pos 60)]),
   ((.exchange 38 27 3),[(.neg 38),(.neg 27),(.pos 47),(.pos 57)]),
   ((.exchange 38 28 2),[(.neg 38),(.neg 28),(.pos 36),(.pos 49),(.pos 59)]),
   ((.exchange 38 34 1),[(.neg 38),(.neg 34),(.pos 44),(.pos 50),(.pos 60)]),
   ((.exchange 39 7 7),[(.neg 39),(.neg 7),(.pos 1),(.pos 2),(.pos 9)]),
   ((.exchange 40 27 4),[(.neg 40),(.neg 27),(.pos 35),(.pos 46),(.pos 56)]),
   ((.exchange 40 31 2),[(.neg 40),(.neg 31),(.pos 51),(.pos 61)]),
   ((.exchange 40 33 0),[(.neg 40),(.neg 33),(.pos 53),(.pos 63)]),
   ((.exchange 40 34 0),[(.neg 40),(.neg 34),(.pos 44),(.pos 53),(.pos 63)]),
   ((.exchange 41 31 2),[(.neg 41),(.neg 31),(.pos 39),(.pos 52),(.pos 62)]),
   ((.exchange 41 67 4),[(.neg 67),(.neg 41),(.pos 47),(.pos 57)]),
   ((.exchange 42 29 4),[(.neg 42),(.neg 29),(.pos 36),(.pos 48),(.pos 58)]),
   ((.exchange 42 32 3),[(.neg 42),(.neg 32),(.pos 39),(.pos 51),(.pos 61)]),
   ((.exchange 42 34 0),[(.neg 42),(.neg 34),(.pos 54),(.pos 64)]),
   ((.exchange 43 29 4),[(.neg 43),(.neg 29),(.pos 49),(.pos 59)]),
   ((.exchange 43 32 3),[(.neg 43),(.neg 32),(.pos 52),(.pos 62)]),
   ((.exchange 43 34 1),[(.neg 43),(.neg 34),(.pos 54),(.pos 64)]),
   ((.exchange 44 7 7),[(.neg 44),(.neg 7),(.pos 3),(.pos 14)]),
   ((.exchange 45 7 7),[(.neg 45),(.neg 7),(.pos 5),(.pos 6)]),
   ((.exchange 46 12 2),[(.neg 46),(.neg 12),(.pos 48),(.pos 51)]),
   ((.exchange 46 17 5),[(.neg 46),(.neg 17),(.pos 37),(.pos 56)]),
   ((.exchange 46 28 2),[(.neg 46),(.neg 28),(.pos 48),(.pos 65)]),
   ((.exchange 46 29 2),[(.neg 46),(.neg 29),(.pos 45),(.pos 48),(.pos 65)]),
   ((.exchange 46 30 0),[(.neg 46),(.neg 30),(.pos 50),(.pos 67)]),
   ((.exchange 46 31 2),[(.neg 46),(.neg 31),(.pos 51),(.pos 65)]),
   ((.exchange 46 32 2),[(.neg 46),(.neg 32),(.pos 45),(.pos 51),(.pos 65)]),
   ((.exchange 46 33 0),[(.neg 46),(.neg 33),(.pos 53),(.pos 67)]),
   ((.exchange 46 43 2),[(.neg 46),(.neg 43),(.pos 45),(.pos 48),(.pos 51)]),
   ((.exchange 46 61 2),[(.neg 61),(.neg 46),(.pos 51),(.pos 65)]),
   ((.exchange 47 12 2),[(.neg 47),(.neg 12),(.pos 45),(.pos 49),(.pos 52)]),
   ((.exchange 47 13 2),[(.neg 47),(.neg 13),(.pos 49),(.pos 52)]),
   ((.exchange 47 17 5),[(.neg 47),(.neg 17),(.pos 35),(.pos 38),(.pos 57)]),
   ((.exchange 47 28 2),[(.neg 47),(.neg 28),(.pos 45),(.pos 49),(.pos 66)]),
   ((.exchange 47 29 2),[(.neg 47),(.neg 29),(.pos 49),(.pos 66)]),
   ((.exchange 47 30 1),[(.neg 47),(.neg 30),(.pos 50),(.pos 67)]),
   ((.exchange 47 31 2),[(.neg 47),(.neg 31),(.pos 45),(.pos 52),(.pos 66)]),
   ((.exchange 47 32 2),[(.neg 47),(.neg 32),(.pos 52),(.pos 66)]),
   ((.exchange 47 33 1),[(.neg 47),(.neg 33),(.pos 53),(.pos 67)]),
   ((.exchange 47 54 2),[(.neg 54),(.neg 47),(.pos 49),(.pos 52)]),
   ((.exchange 47 61 2),[(.neg 61),(.neg 47),(.pos 45),(.pos 52),(.pos 66)]),
   ((.exchange 47 68 1),[(.neg 68),(.neg 47),(.pos 50),(.pos 67)]),
   ((.exchange 48 10 3),[(.neg 48),(.neg 10),(.pos 46),(.pos 51)]),
   ((.exchange 48 17 5),[(.neg 48),(.neg 17),(.pos 37),(.pos 58)]),
   ((.exchange 48 30 0),[(.neg 48),(.neg 30),(.pos 50),(.pos 68)]),
   ((.exchange 48 31 3),[(.neg 48),(.neg 31),(.pos 51),(.pos 65)]),
   ((.exchange 48 34 0),[(.neg 48),(.neg 34),(.pos 54),(.pos 68)]),
   ((.exchange 48 40 3),[(.neg 48),(.neg 40),(.pos 46),(.pos 51)]),
   ((.exchange 48 56 3),[(.neg 56),(.neg 48),(.pos 46),(.pos 65)]),
   ((.exchange 48 57 5),[(.neg 57),(.neg 48),(.pos 36),(.pos 37),(.pos 58)]),
   ((.exchange 48 60 0),[(.neg 60),(.neg 48),(.pos 50),(.pos 68)]),
   ((.exchange 48 62 3),[(.neg 62),(.neg 48),(.pos 45),(.pos 51),(.pos 65)]),
   ((.exchange 48 64 0),[(.neg 64),(.neg 48),(.pos 54),(.pos 68)]),
   ((.exchange 48 64 5),[(.neg 64),(.neg 48),(.pos 42),(.pos 58)]),
   ((.exchange 49 10 3),[(.neg 49),(.neg 10),(.pos 45),(.pos 47),(.pos 52)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_1 : List (Origin 70 91 × List Sat.Literal) :=
  [((.exchange 49 17 5),[(.neg 49),(.neg 17),(.pos 36),(.pos 38),(.pos 59)]),
   ((.exchange 49 27 3),[(.neg 49),(.neg 27),(.pos 47),(.pos 66)]),
   ((.exchange 49 30 1),[(.neg 49),(.neg 30),(.pos 50),(.pos 68)]),
   ((.exchange 49 31 3),[(.neg 49),(.neg 31),(.pos 45),(.pos 52),(.pos 66)]),
   ((.exchange 49 34 1),[(.neg 49),(.neg 34),(.pos 54),(.pos 68)]),
   ((.exchange 49 56 3),[(.neg 56),(.neg 49),(.pos 45),(.pos 47),(.pos 66)]),
   ((.exchange 49 57 5),[(.neg 57),(.neg 49),(.pos 38),(.pos 59)]),
   ((.exchange 49 60 1),[(.neg 60),(.neg 49),(.pos 50),(.pos 68)]),
   ((.exchange 49 64 1),[(.neg 64),(.neg 49),(.pos 54),(.pos 68)]),
   ((.exchange 49 64 5),[(.neg 64),(.neg 49),(.pos 43),(.pos 59)]),
   ((.exchange 49 69 1),[(.neg 69),(.neg 49),(.pos 54),(.pos 68)]),
   ((.exchange 49 69 3),[(.neg 69),(.neg 49),(.pos 52),(.pos 66)]),
   ((.exchange 50 22 5),[(.neg 50),(.neg 22),(.pos 37),(.pos 44),(.pos 60)]),
   ((.exchange 50 27 3),[(.neg 50),(.neg 27),(.pos 47),(.pos 67)]),
   ((.exchange 50 28 2),[(.neg 50),(.neg 28),(.pos 48),(.pos 68)]),
   ((.exchange 50 29 2),[(.neg 50),(.neg 29),(.pos 49),(.pos 68)]),
   ((.exchange 50 41 3),[(.neg 50),(.neg 41),(.pos 47),(.pos 53)]),
   ((.exchange 50 56 3),[(.neg 56),(.neg 50),(.pos 46),(.pos 67)]),
   ((.exchange 50 58 5),[(.neg 58),(.neg 50),(.pos 37),(.pos 60)]),
   ((.exchange 50 65 2),[(.neg 65),(.neg 50),(.pos 48),(.pos 68)]),
   ((.exchange 50 65 3),[(.neg 65),(.neg 50),(.pos 46),(.pos 67)]),
   ((.exchange 50 66 2),[(.neg 66),(.neg 50),(.pos 49),(.pos 68)]),
   ((.exchange 50 66 3),[(.neg 66),(.neg 50),(.pos 47),(.pos 67)]),
   ((.exchange 51 8 4),[(.neg 51),(.neg 8),(.pos 45),(.pos 46),(.pos 48)]),
   ((.exchange 51 17 5),[(.neg 51),(.neg 17),(.pos 40),(.pos 42),(.pos 61)]),
   ((.exchange 51 21 5),[(.neg 51),(.neg 21),(.pos 39),(.pos 40),(.pos 61)]),
   ((.exchange 51 26 4),[(.neg 51),(.neg 26),(.pos 46),(.pos 65)]),
   ((.exchange 51 28 4),[(.neg 51),(.neg 28),(.pos 48),(.pos 65)]),
   ((.exchange 51 29 4),[(.neg 51),(.neg 29),(.pos 45),(.pos 48),(.pos 65)]),
   ((.exchange 51 34 0),[(.neg 51),(.neg 34),(.pos 54),(.pos 69)]),
   ((.exchange 51 50 4),[(.neg 51),(.neg 50),(.pos 46),(.pos 48)]),
   ((.exchange 51 56 4),[(.neg 56),(.neg 51),(.pos 46),(.pos 65)]),
   ((.exchange 51 59 4),[(.neg 59),(.neg 51),(.pos 45),(.pos 48),(.pos 65)]),
   ((.exchange 51 63 0),[(.neg 63),(.neg 51),(.pos 53),(.pos 69)]),
   ((.exchange 51 64 0),[(.neg 64),(.neg 51),(.pos 54),(.pos 69)]),
   ((.exchange 52 7 4),[(.neg 52),(.neg 7),(.pos 45),(.pos 47),(.pos 49)]),
   ((.exchange 52 17 5),[(.neg 52),(.neg 17),(.pos 39),(.pos 41),(.pos 43),(.pos 62)]),
   ((.exchange 52 21 5),[(.neg 52),(.neg 21),(.pos 41),(.pos 62)]),
   ((.exchange 52 27 4),[(.neg 52),(.neg 27),(.pos 47),(.pos 66)]),
   ((.exchange 52 28 4),[(.neg 52),(.neg 28),(.pos 45),(.pos 49),(.pos 66)]),
   ((.exchange 52 29 4),[(.neg 52),(.neg 29),(.pos 49),(.pos 66)]),
   ((.exchange 52 33 1),[(.neg 52),(.neg 33),(.pos 53),(.pos 69)]),
   ((.exchange 52 34 1),[(.neg 52),(.neg 34),(.pos 54),(.pos 69)]),
   ((.exchange 52 38 4),[(.neg 52),(.neg 38),(.pos 47),(.pos 49)]),
   ((.exchange 52 56 4),[(.neg 56),(.neg 52),(.pos 45),(.pos 47),(.pos 66)]),
   ((.exchange 52 59 4),[(.neg 59),(.neg 52),(.pos 49),(.pos 66)]),
   ((.exchange 52 64 1),[(.neg 64),(.neg 52),(.pos 54),(.pos 69)]),
   ((.exchange 53 23 5),[(.neg 53),(.neg 23),(.pos 41),(.pos 44),(.pos 63)]),
   ((.exchange 53 27 4),[(.neg 53),(.neg 27),(.pos 47),(.pos 67)]),
   ((.exchange 53 31 2),[(.neg 53),(.neg 31),(.pos 51),(.pos 69)]),
   ((.exchange 53 32 2),[(.neg 53),(.neg 32),(.pos 52),(.pos 69)]),
   ((.exchange 53 56 4),[(.neg 56),(.neg 53),(.pos 46),(.pos 67)]),
   ((.exchange 53 59 5),[(.neg 59),(.neg 53),(.pos 41),(.pos 44),(.pos 63)]),
   ((.exchange 54 18 5),[(.neg 54),(.neg 18),(.pos 43),(.pos 44),(.pos 64)]),
   ((.exchange 54 28 4),[(.neg 54),(.neg 28),(.pos 48),(.pos 68)]),
   ((.exchange 54 29 4),[(.neg 54),(.neg 29),(.pos 49),(.pos 68)]),
   ((.exchange 54 31 3),[(.neg 54),(.neg 31),(.pos 51),(.pos 69)]),
   ((.exchange 54 32 3),[(.neg 54),(.neg 32),(.pos 52),(.pos 69)]),
   ((.exchange 54 58 4),[(.neg 58),(.neg 54),(.pos 48),(.pos 68)]),
   ((.exchange 54 59 4),[(.neg 59),(.neg 54),(.pos 49),(.pos 68)]),
   ((.exchange 55 7 6),[(.neg 55),(.neg 7),(.pos 35),(.pos 36),(.pos 45)]),
   ((.exchange 56 10 6),[(.neg 56),(.neg 10),(.pos 40),(.pos 46)]),
   ((.exchange 56 22 2),[(.neg 56),(.neg 22),(.pos 58),(.pos 61)]),
   ((.exchange 56 28 2),[(.neg 56),(.neg 28),(.pos 58),(.pos 65)]),
   ((.exchange 56 29 2),[(.neg 56),(.neg 29),(.pos 55),(.pos 58),(.pos 65)]),
   ((.exchange 56 30 0),[(.neg 56),(.neg 30),(.pos 60),(.pos 67)]),
   ((.exchange 56 42 2),[(.neg 56),(.neg 42),(.pos 58),(.pos 61)]),
   ((.exchange 56 68 0),[(.neg 68),(.neg 56),(.pos 60),(.pos 67)]),
   ((.exchange 56 69 0),[(.neg 69),(.neg 56),(.pos 63),(.pos 67)]),
   ((.exchange 56 69 2),[(.neg 69),(.neg 56),(.pos 61),(.pos 65)]),
   ((.exchange 57 7 6),[(.neg 57),(.neg 7),(.pos 35),(.pos 38),(.pos 47)]),
   ((.exchange 57 22 2),[(.neg 57),(.neg 22),(.pos 55),(.pos 59),(.pos 62)]),
   ((.exchange 57 28 2),[(.neg 57),(.neg 28),(.pos 55),(.pos 59),(.pos 66)]),
   ((.exchange 57 29 2),[(.neg 57),(.neg 29),(.pos 59),(.pos 66)]),
   ((.exchange 57 30 1),[(.neg 57),(.neg 30),(.pos 60),(.pos 67)]),
   ((.exchange 57 33 1),[(.neg 57),(.neg 33),(.pos 63),(.pos 67)]),
   ((.exchange 57 42 2),[(.neg 57),(.neg 42),(.pos 55),(.pos 59),(.pos 62)]),
   ((.exchange 57 68 1),[(.neg 68),(.neg 57),(.pos 60),(.pos 67)]),
   ((.exchange 57 69 2),[(.neg 69),(.neg 57),(.pos 62),(.pos 66)]),
   ((.exchange 58 20 3),[(.neg 58),(.neg 20),(.pos 56),(.pos 61)]),
   ((.exchange 58 30 0),[(.neg 58),(.neg 30),(.pos 60),(.pos 68)]),
   ((.exchange 58 40 3),[(.neg 58),(.neg 40),(.pos 56),(.pos 61)]),
   ((.exchange 58 46 6),[(.neg 58),(.neg 46),(.pos 37),(.pos 48)]),
   ((.exchange 58 47 6),[(.neg 58),(.neg 47),(.pos 36),(.pos 37),(.pos 48)]),
   ((.exchange 58 52 6),[(.neg 58),(.neg 52),(.pos 36),(.pos 42),(.pos 48)]),
   ((.exchange 58 53 6),[(.neg 58),(.neg 53),(.pos 37),(.pos 42),(.pos 48)]),
   ((.exchange 58 54 0),[(.neg 58),(.neg 54),(.pos 64),(.pos 68)]),
   ((.exchange 58 63 3),[(.neg 63),(.neg 58),(.pos 56),(.pos 61)]),
   ((.exchange 58 67 0),[(.neg 67),(.neg 58),(.pos 60),(.pos 68)]),
   ((.exchange 58 67 3),[(.neg 67),(.neg 58),(.pos 56),(.pos 65)]),
   ((.exchange 59 7 6),[(.neg 59),(.neg 7),(.pos 36),(.pos 38),(.pos 49)]),
   ((.exchange 59 11 6),[(.neg 59),(.neg 11),(.pos 38),(.pos 43),(.pos 49)]),
   ((.exchange 59 20 3),[(.neg 59),(.neg 20),(.pos 55),(.pos 57),(.pos 62)]),
   ((.exchange 59 30 1),[(.neg 59),(.neg 30),(.pos 60),(.pos 68)]),
   ((.exchange 59 33 1),[(.neg 59),(.neg 33),(.pos 60),(.pos 64),(.pos 68)]),
   ((.exchange 59 40 3),[(.neg 59),(.neg 40),(.pos 55),(.pos 57),(.pos 62)]),
   ((.exchange 59 46 6),[(.neg 59),(.neg 46),(.pos 36),(.pos 38),(.pos 49)]),
   ((.exchange 59 47 3),[(.neg 59),(.neg 47),(.pos 57),(.pos 66)]),
   ((.exchange 59 53 6),[(.neg 59),(.neg 53),(.pos 38),(.pos 43),(.pos 49)]),
   ((.exchange 59 63 3),[(.neg 63),(.neg 59),(.pos 57),(.pos 62)]),
   ((.exchange 59 67 1),[(.neg 67),(.neg 59),(.pos 60),(.pos 68)]),
   ((.exchange 59 67 3),[(.neg 67),(.neg 59),(.pos 57),(.pos 66)]),
   ((.exchange 60 26 3),[(.neg 60),(.neg 26),(.pos 56),(.pos 67)]),
   ((.exchange 60 27 3),[(.neg 60),(.neg 27),(.pos 57),(.pos 67)]),
   ((.exchange 60 28 2),[(.neg 60),(.neg 28),(.pos 58),(.pos 68)]),
   ((.exchange 60 29 2),[(.neg 60),(.neg 29),(.pos 59),(.pos 68)]),
   ((.exchange 60 40 3),[(.neg 60),(.neg 40),(.pos 56),(.pos 63)]),
   ((.exchange 60 47 6),[(.neg 60),(.neg 47),(.pos 38),(.pos 50)]),
   ((.exchange 60 65 2),[(.neg 65),(.neg 60),(.pos 58),(.pos 68)]),
   ((.exchange 61 11 6),[(.neg 61),(.neg 11),(.pos 39),(.pos 40),(.pos 51)]),
   ((.exchange 61 17 4),[(.neg 61),(.neg 17),(.pos 56),(.pos 58)]),
   ((.exchange 61 27 4),[(.neg 61),(.neg 27),(.pos 55),(.pos 56),(.pos 65)]),
   ((.exchange 61 30 4),[(.neg 61),(.neg 30),(.pos 56),(.pos 58),(.pos 65)]),
   ((.exchange 61 34 0),[(.neg 61),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 61 46 4),[(.neg 61),(.neg 46),(.pos 56),(.pos 65)]),
   ((.exchange 61 50 0),[(.neg 61),(.neg 50),(.pos 63),(.pos 64),(.pos 69)]),
   ((.exchange 61 54 6),[(.neg 61),(.neg 54),(.pos 42),(.pos 51)]),
   ((.exchange 61 67 0),[(.neg 67),(.neg 61),(.pos 63),(.pos 69)]),
   ((.exchange 61 68 0),[(.neg 68),(.neg 61),(.pos 64),(.pos 69)]),
   ((.exchange 62 11 6),[(.neg 62),(.neg 11),(.pos 41),(.pos 52)]),
   ((.exchange 62 27 4),[(.neg 62),(.neg 27),(.pos 57),(.pos 66)]),
   ((.exchange 62 30 4),[(.neg 62),(.neg 30),(.pos 57),(.pos 59),(.pos 66)]),
   ((.exchange 62 33 1),[(.neg 62),(.neg 33),(.pos 63),(.pos 69)]),
   ((.exchange 62 34 1),[(.neg 62),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 62 46 4),[(.neg 62),(.neg 46),(.pos 55),(.pos 57),(.pos 66)]),
   ((.exchange 62 54 6),[(.neg 62),(.neg 54),(.pos 43),(.pos 52)]),
   ((.exchange 62 60 4),[(.neg 62),(.neg 60),(.pos 57),(.pos 59)]),
   ((.exchange 62 67 1),[(.neg 67),(.neg 62),(.pos 63),(.pos 69)])]

theorem certificates_1_valid : ∀ oc ∈ certificates_1,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_2 : List (Origin 70 91 × List Sat.Literal) :=
  [((.exchange 62 68 1),[(.neg 68),(.neg 62),(.pos 64),(.pos 69)]),
   ((.exchange 63 27 4),[(.neg 63),(.neg 27),(.pos 57),(.pos 67)]),
   ((.exchange 63 31 2),[(.neg 63),(.neg 31),(.pos 61),(.pos 69)]),
   ((.exchange 63 32 2),[(.neg 63),(.neg 32),(.pos 62),(.pos 69)]),
   ((.exchange 63 46 4),[(.neg 63),(.neg 46),(.pos 56),(.pos 67)]),
   ((.exchange 63 50 6),[(.neg 63),(.neg 50),(.pos 44),(.pos 53)]),
   ((.exchange 64 7 6),[(.neg 64),(.neg 7),(.pos 42),(.pos 44),(.pos 54)]),
   ((.exchange 64 28 4),[(.neg 64),(.neg 28),(.pos 58),(.pos 68)]),
   ((.exchange 64 29 4),[(.neg 64),(.neg 29),(.pos 59),(.pos 68)]),
   ((.exchange 64 31 3),[(.neg 64),(.neg 31),(.pos 61),(.pos 69)]),
   ((.exchange 64 32 3),[(.neg 64),(.neg 32),(.pos 62),(.pos 69)]),
   ((.exchange 64 51 3),[(.neg 64),(.neg 51),(.pos 61),(.pos 69)]),
   ((.exchange 64 65 4),[(.neg 65),(.neg 64),(.pos 58),(.pos 68)]),
   ((.exchange 65 10 6),[(.neg 65),(.neg 10),(.pos 46),(.pos 51)]),
   ((.exchange 65 18 5),[(.neg 65),(.neg 18),(.pos 55),(.pos 56),(.pos 58)]),
   ((.exchange 65 30 0),[(.neg 65),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 65 33 0),[(.neg 65),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 65 38 5),[(.neg 65),(.neg 38),(.pos 55),(.pos 56),(.pos 58)]),
   ((.exchange 65 38 6),[(.neg 65),(.neg 38),(.pos 45),(.pos 46),(.pos 48)]),
   ((.exchange 65 41 5),[(.neg 65),(.neg 41),(.pos 55),(.pos 56),(.pos 61)]),
   ((.exchange 65 42 6),[(.neg 65),(.neg 42),(.pos 48),(.pos 51)]),
   ((.exchange 65 43 5),[(.neg 65),(.neg 43),(.pos 55),(.pos 58),(.pos 61)]),
   ((.exchange 65 43 6),[(.neg 65),(.neg 43),(.pos 45),(.pos 48),(.pos 51)]),
   ((.exchange 65 50 6),[(.neg 65),(.neg 50),(.pos 46),(.pos 48)]),
   ((.exchange 65 53 6),[(.neg 65),(.neg 53),(.pos 46),(.pos 51)]),
   ((.exchange 65 54 0),[(.neg 65),(.neg 54),(.pos 68),(.pos 69)]),
   ((.exchange 65 63 5),[(.neg 65),(.neg 63),(.pos 56),(.pos 61)]),
   ((.exchange 65 64 5),[(.neg 65),(.neg 64),(.pos 58),(.pos 61)]),
   ((.exchange 66 8 6),[(.neg 66),(.neg 8),(.pos 47),(.pos 49)]),
   ((.exchange 66 10 6),[(.neg 66),(.neg 10),(.pos 45),(.pos 47),(.pos 52)]),
   ((.exchange 66 12 6),[(.neg 66),(.neg 12),(.pos 45),(.pos 49),(.pos 52)]),
   ((.exchange 66 18 5),[(.neg 66),(.neg 18),(.pos 57),(.pos 59)]),
   ((.exchange 66 23 5),[(.neg 66),(.neg 23),(.pos 59),(.pos 62)]),
   ((.exchange 66 30 1),[(.neg 66),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 66 33 1),[(.neg 66),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 66 38 5),[(.neg 66),(.neg 38),(.pos 57),(.pos 59)]),
   ((.exchange 66 40 5),[(.neg 66),(.neg 40),(.pos 55),(.pos 57),(.pos 62)]),
   ((.exchange 66 40 6),[(.neg 66),(.neg 40),(.pos 45),(.pos 47),(.pos 52)]),
   ((.exchange 66 42 6),[(.neg 66),(.neg 42),(.pos 45),(.pos 49),(.pos 52)]),
   ((.exchange 66 43 5),[(.neg 66),(.neg 43),(.pos 59),(.pos 62)]),
   ((.exchange 66 50 6),[(.neg 66),(.neg 50),(.pos 47),(.pos 49)]),
   ((.exchange 66 53 6),[(.neg 66),(.neg 53),(.pos 47),(.pos 52)]),
   ((.exchange 66 63 5),[(.neg 66),(.neg 63),(.pos 57),(.pos 62)]),
   ((.exchange 66 64 1),[(.neg 66),(.neg 64),(.pos 68),(.pos 69)]),
   ((.exchange 67 7 6),[(.neg 67),(.neg 7),(.pos 46),(.pos 50)]),
   ((.exchange 67 10 6),[(.neg 67),(.neg 10),(.pos 46),(.pos 53)]),
   ((.exchange 67 17 5),[(.neg 67),(.neg 17),(.pos 56),(.pos 60)]),
   ((.exchange 67 20 5),[(.neg 67),(.neg 20),(.pos 56),(.pos 63)]),
   ((.exchange 67 28 2),[(.neg 67),(.neg 28),(.pos 65),(.pos 68)]),
   ((.exchange 67 31 2),[(.neg 67),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 67 32 2),[(.neg 67),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 67 34 2),[(.neg 67),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 67 37 6),[(.neg 67),(.neg 37),(.pos 46),(.pos 50)]),
   ((.exchange 67 38 5),[(.neg 67),(.neg 38),(.pos 57),(.pos 60)]),
   ((.exchange 67 38 6),[(.neg 67),(.neg 38),(.pos 47),(.pos 50)]),
   ((.exchange 67 40 6),[(.neg 67),(.neg 40),(.pos 46),(.pos 53)]),
   ((.exchange 67 41 5),[(.neg 67),(.neg 41),(.pos 57),(.pos 63)]),
   ((.exchange 67 41 6),[(.neg 67),(.neg 41),(.pos 47),(.pos 53)]),
   ((.exchange 67 64 2),[(.neg 67),(.neg 64),(.pos 68),(.pos 69)]),
   ((.exchange 68 7 6),[(.neg 68),(.neg 7),(.pos 48),(.pos 50)]),
   ((.exchange 68 8 6),[(.neg 68),(.neg 8),(.pos 49),(.pos 50)]),
   ((.exchange 68 10 6),[(.neg 68),(.neg 10),(.pos 48),(.pos 50),(.pos 54)]),
   ((.exchange 68 11 6),[(.neg 68),(.neg 11),(.pos 49),(.pos 50),(.pos 54)]),
   ((.exchange 68 17 5),[(.neg 68),(.neg 17),(.pos 58),(.pos 60)]),
   ((.exchange 68 18 5),[(.neg 68),(.neg 18),(.pos 59),(.pos 60)]),
   ((.exchange 68 22 5),[(.neg 68),(.neg 22),(.pos 58),(.pos 64)]),
   ((.exchange 68 26 3),[(.neg 68),(.neg 26),(.pos 65),(.pos 67)]),
   ((.exchange 68 27 3),[(.neg 68),(.neg 27),(.pos 66),(.pos 67)]),
   ((.exchange 68 33 3),[(.neg 68),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 68 37 6),[(.neg 68),(.neg 37),(.pos 48),(.pos 50)]),
   ((.exchange 68 46 3),[(.neg 68),(.neg 46),(.pos 65),(.pos 67)]),
   ((.exchange 68 47 3),[(.neg 68),(.neg 47),(.pos 66),(.pos 67)]),
   ((.exchange 68 51 6),[(.neg 68),(.neg 51),(.pos 48),(.pos 54)]),
   ((.exchange 68 56 5),[(.neg 68),(.neg 56),(.pos 58),(.pos 60)]),
   ((.exchange 68 57 5),[(.neg 68),(.neg 57),(.pos 59),(.pos 60)]),
   ((.exchange 69 8 6),[(.neg 69),(.neg 8),(.pos 52),(.pos 53),(.pos 54)]),
   ((.exchange 69 10 6),[(.neg 69),(.neg 10),(.pos 51),(.pos 53)]),
   ((.exchange 69 11 6),[(.neg 69),(.neg 11),(.pos 52),(.pos 53)]),
   ((.exchange 69 12 6),[(.neg 69),(.neg 12),(.pos 51),(.pos 54)]),
   ((.exchange 69 13 6),[(.neg 69),(.neg 13),(.pos 52),(.pos 54)]),
   ((.exchange 69 20 5),[(.neg 69),(.neg 20),(.pos 61),(.pos 63)]),
   ((.exchange 69 22 5),[(.neg 69),(.neg 22),(.pos 61),(.pos 64)]),
   ((.exchange 69 23 5),[(.neg 69),(.neg 23),(.pos 62),(.pos 64)]),
   ((.exchange 69 26 4),[(.neg 69),(.neg 26),(.pos 65),(.pos 67)]),
   ((.exchange 69 27 4),[(.neg 69),(.neg 27),(.pos 66),(.pos 67)]),
   ((.exchange 69 28 4),[(.neg 69),(.neg 28),(.pos 65),(.pos 68)]),
   ((.exchange 69 29 4),[(.neg 69),(.neg 29),(.pos 66),(.pos 68)]),
   ((.exchange 69 30 4),[(.neg 69),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 69 40 5),[(.neg 69),(.neg 40),(.pos 61),(.pos 63)]),
   ((.exchange 69 40 6),[(.neg 69),(.neg 40),(.pos 51),(.pos 53)]),
   ((.exchange 69 41 5),[(.neg 69),(.neg 41),(.pos 62),(.pos 63)]),
   ((.exchange 69 41 6),[(.neg 69),(.neg 41),(.pos 52),(.pos 53)]),
   ((.exchange 69 42 6),[(.neg 69),(.neg 42),(.pos 51),(.pos 54)]),
   ((.exchange 69 49 4),[(.neg 69),(.neg 49),(.pos 66),(.pos 68)]),
   (.newPoint,[(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 0),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 60),(.neg 54),(.neg 53),(.neg 50),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 51),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 61),(.pos 62),(.pos 65),(.pos 66)]),
   ((.excluded 1),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 64),(.pos 67)]),
   ((.excluded 2),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57),(.pos 68)]),
   ((.excluded 3),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57),(.pos 69)]),
   ((.excluded 4),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 5),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 57),(.neg 56),(.neg 52),(.neg 51),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 58),(.pos 59),(.pos 60),(.pos 63),(.pos 64),(.pos 68)]),
   ((.excluded 6),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 55),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 7),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 61),(.pos 62),(.pos 68)]),
   ((.excluded 8),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 55),(.pos 68)]),
   ((.excluded 9),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 10),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 61),(.pos 62),(.pos 67)]),
   ((.excluded 11),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 12),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 58),(.pos 59),(.pos 67)]),
   ((.excluded 13),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 58),(.pos 59),(.pos 69)]),
   ((.excluded 14),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 58),(.pos 59)]),
   ((.excluded 15),[(.neg 69),(.neg 68),(.neg 67),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 63),(.pos 64),(.pos 65),(.pos 66)]),
   ((.excluded 16),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 63),(.pos 64)]),
   ((.excluded 17),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 55),(.pos 65),(.pos 66)]),
   ((.excluded 18),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 55),(.pos 67)]),
   ((.excluded 19),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 55),(.pos 69)]),
   ((.excluded 20),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 55)]),
   ((.excluded 21),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 22),[(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 23),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 24),[(.neg 69),(.neg 68),(.neg 67),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 51),(.pos 52),(.pos 55),(.pos 60),(.pos 63),(.pos 64),(.pos 65),(.pos 66)]),
   ((.excluded 25),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 51),(.pos 52),(.pos 55),(.pos 65),(.pos 66)]),
   ((.excluded 26),[(.neg 69),(.neg 68),(.neg 67),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 60),(.pos 63),(.pos 64),(.pos 65),(.pos 66)]),
   ((.excluded 27),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 60),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 61),(.pos 62),(.pos 65),(.pos 66)]),
   ((.excluded 28),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 60),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 61),(.pos 62),(.pos 65),(.pos 66)]),
   ((.excluded 29),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 65),(.pos 66)]),
   ((.excluded 30),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 65),(.pos 66)]),
   ((.excluded 31),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 58),(.pos 59),(.pos 67)]),
   ((.excluded 32),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 61),(.pos 62),(.pos 67)])]

theorem certificates_2_valid : ∀ oc ∈ certificates_2,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_3 : List (Origin 70 91 × List Sat.Literal) :=
  [((.excluded 33),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 67)]),
   ((.excluded 34),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 52),(.neg 51),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 68)]),
   ((.excluded 35),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 52),(.neg 51),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 61),(.pos 62),(.pos 68)]),
   ((.excluded 36),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 52),(.neg 51),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 68)]),
   ((.excluded 37),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 69)]),
   ((.excluded 38),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 58),(.pos 59),(.pos 69)]),
   ((.excluded 39),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 69)]),
   ((.excluded 40),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 41),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 58),(.pos 59)]),
   ((.excluded 42),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 43),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 53),(.pos 54),(.pos 55)]),
   ((.excluded 44),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 64),(.pos 67)]),
   ((.excluded 45),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 64),(.pos 67)]),
   ((.excluded 46),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 64),(.pos 67)]),
   ((.excluded 47),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 58),(.pos 59),(.pos 60),(.pos 63),(.pos 64),(.pos 68)]),
   ((.excluded 48),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 58),(.pos 59),(.pos 60),(.pos 63),(.pos 64),(.pos 68)]),
   ((.excluded 49),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 58),(.pos 59),(.pos 60),(.pos 63),(.pos 64),(.pos 68)]),
   ((.excluded 50),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 51),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 52),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 53),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 60),(.pos 63),(.pos 64)]),
   ((.excluded 54),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 60),(.pos 63),(.pos 64)]),
   ((.excluded 55),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 60),(.pos 63),(.pos 64)]),
   ((.excluded 56),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 60),(.pos 63),(.pos 64)]),
   ((.excluded 57),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 58),(.pos 59),(.pos 69)]),
   ((.excluded 58),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 58),(.pos 59)]),
   ((.excluded 59),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 69)]),
   ((.excluded 60),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 61),(.pos 62),(.pos 68)]),
   ((.excluded 61),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 62),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 68)]),
   ((.excluded 63),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 55)]),
   ((.excluded 64),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 58),(.pos 59),(.pos 69)]),
   ((.excluded 65),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 58),(.pos 59),(.pos 67)]),
   ((.excluded 66),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 58),(.pos 59)]),
   ((.excluded 67),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 58),(.pos 59),(.pos 67)]),
   ((.excluded 68),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 58),(.pos 59)]),
   ((.excluded 69),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 56),(.pos 57),(.pos 69)]),
   ((.excluded 70),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 69)]),
   ((.excluded 71),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 69)]),
   ((.excluded 72),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 69)]),
   ((.excluded 73),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 67)]),
   ((.excluded 74),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 68)]),
   ((.excluded 75),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 76),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 68)]),
   ((.excluded 77),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 51),(.pos 52),(.pos 55)]),
   ((.excluded 78),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 79),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 68)]),
   ((.excluded 80),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 81),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 61),(.pos 62),(.pos 68)]),
   ((.excluded 82),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 68)]),
   ((.excluded 83),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 61),(.pos 62),(.pos 67)]),
   ((.excluded 84),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 85),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 67)]),
   ((.excluded 86),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 55)]),
   ((.excluded 87),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 61),(.pos 62),(.pos 67)]),
   ((.excluded 88),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 89),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 67)]),
   ((.excluded 90),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55)])]

theorem certificates_3_valid : ∀ oc ∈ certificates_3,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



theorem witness_0 : ∀ j : Fin 91,
    let w : Fin 91 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 91,
      let w : Fin 91 := ⟨0 + j.val,by omega⟩
      target w < MatroidCatalogue.count 8 4 ∧
        Papers.RationalityTen.MatroidChecked.FastSemanticChecks.RawWitness 8 (N7R4.familyMasks.get 40)
        (fun i : Fin 70 => N8R4.gridMasks.get i.val) newIndex (models w)
        (N8R4.familyMasks.get (target w)) (permutation w) := by
    refine (Fin.forall_fin_add (m := 45) (n := 46) _).2 ⟨?_, ?_⟩
    · refine (Fin.forall_fin_add (m := 22) (n := 23) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 11) (n := 11) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 5) (n := 6) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 3) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 5) (n := 6) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 3) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
      · refine (Fin.forall_fin_add (m := 11) (n := 12) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 5) (n := 6) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 3) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 6) (n := 6) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 3) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 3) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
    · refine (Fin.forall_fin_add (m := 23) (n := 23) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 11) (n := 12) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 5) (n := 6) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 3) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 6) (n := 6) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 3) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 3) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
      · refine (Fin.forall_fin_add (m := 11) (n := 12) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 5) (n := 6) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 3) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 6) (n := 6) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 3) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 3) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
  intro j
  have hj := hfast j
  exact ⟨hj.1,Papers.RationalityTen.MatroidChecked.FastSemanticChecks.rawWitness_sound 8 _ _ _ _ _ _ hj.2⟩


end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C40

/- Source: MatroidCatalogue/Cases/N8R4C40Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C40

noncomputable def certificates : List (Origin 70 91 × List Sat.Literal) :=
  certificates_0 ++ certificates_1 ++ certificates_2 ++ certificates_3

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  intro oc hoc
  simp only [certificates,List.mem_append,or_assoc] at hoc
  rcases hoc with h0 | h1 | h2 | h3
  · exact certificates_0_valid oc h0
  · exact certificates_1_valid oc h1
  · exact certificates_2_valid oc h2
  · exact certificates_3_valid oc h3

theorem models_valid : ∀ w : Fin 91,
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 91) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 8) 4)
    (hold : M.bases.filter ((7 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 8 4, IsomorphicWithin 8 M.bases B := by
  apply extension_covered_of_certificate (n:=7) (r:=4) (by decide)
    catalogue old U newIndex models certificates
    N8R4.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C40.formula []
    exact Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C40.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 8 4 (target w),family_mem 8 4 (target w) hw.1,?_⟩
    exact validWitness_sound 8 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C40


end
end
end BundlePart4

section BundlePart5
/- Source: MatroidChecked/SemanticChunks/Cases05Part06.lean -/




@[expose] public section
noncomputable section

/- Source: MatroidCatalogue/Cases/N8R4C41Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C41

abbrev U := N8R4.grid
noncomputable def old : Finset (Finset (Fin 8)) := N7R4.family 41
noncomputable def newIndexTree : Table ℕ := (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf 35) (.leaf 36)) (.node 3 (.leaf 37) (.leaf 38))) (.node 6 (.node 5 (.leaf 39) (.leaf 40)) (.node 7 (.leaf 41) (.leaf 42)))) (.node 12 (.node 10 (.node 9 (.leaf 43) (.leaf 44)) (.node 11 (.leaf 45) (.leaf 46))) (.node 14 (.node 13 (.leaf 47) (.leaf 48)) (.node 15 (.leaf 49) (.node 16 (.leaf 50) (.leaf 51)))))) (.node 26 (.node 21 (.node 19 (.node 18 (.leaf 52) (.leaf 53)) (.node 20 (.leaf 54) (.leaf 55))) (.node 23 (.node 22 (.leaf 56) (.leaf 57)) (.node 24 (.leaf 58) (.node 25 (.leaf 59) (.leaf 60))))) (.node 30 (.node 28 (.node 27 (.leaf 61) (.leaf 62)) (.node 29 (.leaf 63) (.leaf 64))) (.node 32 (.node 31 (.leaf 65) (.leaf 66)) (.node 33 (.leaf 67) (.node 34 (.leaf 68) (.leaf 69)))))))
noncomputable def newIndex (i : Fin 35) : Fin 70 := Fin.ofNat 70 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 33 (.node 16 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (30870635008,95,5761224)) (.leaf (29729776000,110,7858312))) (.node 3 (.leaf (7986013056,123,5761224)) (.leaf (34293212032,132,7858312)))) (.node 6 (.node 5 (.leaf (7986419808,114,7857416)) (.leaf (523232,114,7072520))) (.node 7 (.leaf (7986478048,164,9430344)) (.leaf (29730249312,128,5760776))))) (.node 12 (.node 10 (.node 9 (.leaf (34293652064,136,7857416)) (.leaf (30871091680,128,5237512))) (.node 11 (.leaf (30871124960,136,7072520)) (.leaf (34293643744,169,9954952)))) (.node 14 (.node 13 (.leaf (29730274272,169,9431688)) (.leaf (34293677024,176,11789960))) (.node 15 (.leaf (7581261836,114,8301832)) (.leaf (534774668,114,8215816)))))) (.node 24 (.node 20 (.node 18 (.node 17 (.leaf (8051024780,164,10333512)) (.leaf (29861896716,128,6208776))) (.node 19 (.leaf (34156896780,136,8301832)) (.leaf (30868537740,128,6151432)))) (.node 22 (.node 21 (.leaf (31136973708,136,8215816)) (.leaf (34089787788,169,10402952))) (.node 23 (.leaf (30063223692,169,10345608)) (.leaf (34358223756,176,12467336))))) (.node 28 (.node 26 (.node 25 (.leaf (535296108,266,5662664)) (.leaf (8051488876,270,10139080))) (.node 27 (.leaf (535297004,270,9268168)) (.leaf (7581670380,266,5720008)))) (.node 30 (.node 29 (.leaf (8051432428,270,10081736)) (.leaf (7581727724,270,9382856))) (.node 31 (.leaf (8051489772,282,15648136)) (.node 32 (.leaf (30063721068,283,16434376)) (.leaf (30868994668,284,12220040)))))))) (.node 49 (.node 41 (.node 37 (.node 35 (.node 34 (.leaf (31137430124,285,12186888)) (.leaf (30869027436,285,11480840))) (.node 36 (.leaf (31137462892,286,13809096)) (.leaf (34090220140,287,12306056)))) (.node 39 (.node 38 (.leaf (34358655596,288,16434376)) (.leaf (34090252908,288,16197832))) (.node 40 (.leaf (34358688364,289,16430344)) (.leaf (31137462764,283,15821512))))) (.node 45 (.node 43 (.node 42 (.leaf (30868995052,287,11660936)) (.leaf (31137430508,288,15821512))) (.node 44 (.leaf (30869027820,288,15359176)) (.leaf (31137463276,289,15559432)))) (.node 47 (.node 46 (.leaf (34157329388,283,15936200)) (.leaf (34090220524,290,16434824))) (.node 48 (.leaf (34358655980,291,16406152)) (.leaf (34090228716,283,16405704)))))) (.node 57 (.node 53 (.node 51 (.node 50 (.leaf (34090253292,291,15940232)) (.leaf (29862369772,284,12306056))) (.node 52 (.leaf (34157337068,285,12301576)) (.leaf (29862370284,285,11366152)))) (.node 55 (.node 54 (.leaf (34157337580,286,13751752)) (.leaf (30063696364,287,12220040))) (.node 56 (.leaf (34358663660,288,16405704)) (.leaf (30063696876,288,16083144))))) (.node 61 (.node 59 (.node 58 (.leaf (34358664172,289,16373000)) (.leaf (29862394348,287,11746952))) (.node 60 (.leaf (34157361644,288,15936200)) (.leaf (29862394860,288,15387848)))) (.node 63 (.node 62 (.leaf (34157362156,289,15674120)) (.leaf (30063720940,290,16406152))) (.node 64 (.leaf (34358688236,291,16434824)) (.node 65 (.leaf (30063721452,291,15854216)) (.leaf (34358688748,292,16434824)))))))))

noncomputable def models (i : Fin 66) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 66) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 66) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 70, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (7 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 70, (7 : Fin 8) ∈ U i → ∃ j : Fin 35, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C41

/- Source: MatroidCatalogue/Cases/N8R4C41Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C41


noncomputable def certificates_0 : List (Origin 70 66 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.neg 2)]),
   ((.fixed 3),[(.pos 3)]),
   ((.fixed 4),[(.pos 4)]),
   ((.fixed 5),[(.neg 5)]),
   ((.fixed 6),[(.neg 6)]),
   ((.fixed 7),[(.pos 7)]),
   ((.fixed 8),[(.pos 8)]),
   ((.fixed 9),[(.neg 9)]),
   ((.fixed 10),[(.neg 10)]),
   ((.fixed 11),[(.neg 11)]),
   ((.fixed 12),[(.pos 12)]),
   ((.fixed 13),[(.pos 13)]),
   ((.fixed 14),[(.pos 14)]),
   ((.fixed 15),[(.neg 15)]),
   ((.fixed 16),[(.neg 16)]),
   ((.fixed 17),[(.neg 17)]),
   ((.fixed 18),[(.neg 18)]),
   ((.fixed 19),[(.neg 19)]),
   ((.fixed 20),[(.pos 20)]),
   ((.fixed 21),[(.pos 21)]),
   ((.fixed 22),[(.pos 22)]),
   ((.fixed 23),[(.pos 23)]),
   ((.fixed 24),[(.pos 24)]),
   ((.fixed 25),[(.neg 25)]),
   ((.fixed 26),[(.pos 26)]),
   ((.fixed 27),[(.pos 27)]),
   ((.fixed 28),[(.pos 28)]),
   ((.fixed 29),[(.pos 29)]),
   ((.fixed 30),[(.pos 30)]),
   ((.fixed 31),[(.pos 31)]),
   ((.fixed 32),[(.pos 32)]),
   ((.fixed 33),[(.pos 33)]),
   ((.fixed 34),[(.neg 34)]),
   ((.exchange 3 38 4),[(.neg 38),(.neg 3),(.pos 0),(.pos 37)]),
   ((.exchange 3 41 3),[(.neg 41),(.neg 3),(.pos 1),(.pos 40)]),
   ((.exchange 3 43 2),[(.neg 43),(.neg 3),(.pos 2),(.pos 42)]),
   ((.exchange 3 56 4),[(.neg 56),(.neg 3),(.pos 17),(.pos 37)]),
   ((.exchange 3 60 4),[(.neg 60),(.neg 3),(.pos 17),(.pos 37)]),
   ((.exchange 4 37 4),[(.neg 37),(.neg 4),(.pos 0),(.pos 38)]),
   ((.exchange 4 40 3),[(.neg 40),(.neg 4),(.pos 1),(.pos 41)]),
   ((.exchange 4 42 2),[(.neg 42),(.neg 4),(.pos 2),(.pos 43)]),
   ((.exchange 4 46 3),[(.neg 46),(.neg 4),(.pos 1),(.pos 11),(.pos 41)]),
   ((.exchange 4 47 3),[(.neg 47),(.neg 4),(.pos 11),(.pos 41)]),
   ((.exchange 4 51 3),[(.neg 51),(.neg 4),(.pos 1),(.pos 11),(.pos 41)]),
   ((.exchange 4 52 3),[(.neg 52),(.neg 4),(.pos 11),(.pos 41)]),
   ((.exchange 4 53 3),[(.neg 53),(.neg 4),(.pos 11),(.pos 41)]),
   ((.exchange 4 56 4),[(.neg 56),(.neg 4),(.pos 0),(.pos 18),(.pos 38)]),
   ((.exchange 4 57 4),[(.neg 57),(.neg 4),(.pos 18),(.pos 38)]),
   ((.exchange 4 58 4),[(.neg 58),(.neg 4),(.pos 0),(.pos 18),(.pos 38)]),
   ((.exchange 4 59 4),[(.neg 59),(.neg 4),(.pos 18),(.pos 38)]),
   ((.exchange 4 60 4),[(.neg 60),(.neg 4),(.pos 18),(.pos 38)]),
   ((.exchange 7 41 3),[(.neg 41),(.neg 7),(.pos 5),(.pos 10),(.pos 46)]),
   ((.exchange 7 49 2),[(.neg 49),(.neg 7),(.pos 6),(.pos 48)]),
   ((.exchange 8 41 3),[(.neg 41),(.neg 8),(.pos 11),(.pos 47)]),
   ((.exchange 8 48 2),[(.neg 48),(.neg 8),(.pos 6),(.pos 49)]),
   ((.exchange 12 41 3),[(.neg 41),(.neg 12),(.pos 9),(.pos 10),(.pos 51)]),
   ((.exchange 12 64 0),[(.neg 64),(.neg 12),(.pos 34),(.pos 54)]),
   ((.exchange 12 68 0),[(.neg 68),(.neg 12),(.pos 34),(.pos 54)]),
   ((.exchange 12 69 0),[(.neg 69),(.neg 12),(.pos 34),(.pos 54)]),
   ((.exchange 13 41 3),[(.neg 41),(.neg 13),(.pos 11),(.pos 52)]),
   ((.exchange 14 41 3),[(.neg 41),(.neg 14),(.pos 11),(.pos 53)]),
   ((.exchange 20 37 4),[(.neg 37),(.neg 20),(.pos 17),(.pos 56)]),
   ((.exchange 20 38 4),[(.neg 38),(.neg 20),(.pos 15),(.pos 17),(.pos 56)]),
   ((.exchange 20 57 4),[(.neg 57),(.neg 20),(.pos 15),(.pos 56)]),
   ((.exchange 20 58 4),[(.neg 58),(.neg 20),(.pos 17),(.pos 56)]),
   ((.exchange 20 59 4),[(.neg 59),(.neg 20),(.pos 15),(.pos 17),(.pos 56)]),
   ((.exchange 20 60 4),[(.neg 60),(.neg 20),(.pos 17),(.pos 56)]),
   ((.exchange 20 62 2),[(.neg 62),(.neg 20),(.pos 19),(.pos 61)]),
   ((.exchange 21 38 4),[(.neg 38),(.neg 21),(.pos 18),(.pos 57)]),
   ((.exchange 21 56 4),[(.neg 56),(.neg 21),(.pos 15),(.pos 57)]),
   ((.exchange 21 60 4),[(.neg 60),(.neg 21),(.pos 18),(.pos 57)]),
   ((.exchange 21 61 2),[(.neg 61),(.neg 21),(.pos 19),(.pos 62)]),
   ((.exchange 22 38 4),[(.neg 38),(.neg 22),(.pos 16),(.pos 17),(.pos 58)]),
   ((.exchange 22 56 4),[(.neg 56),(.neg 22),(.pos 17),(.pos 58)]),
   ((.exchange 22 60 4),[(.neg 60),(.neg 22),(.pos 17),(.pos 58)]),
   ((.exchange 22 68 0),[(.neg 68),(.neg 22),(.pos 34),(.pos 64)]),
   ((.exchange 22 69 0),[(.neg 69),(.neg 22),(.pos 34),(.pos 64)]),
   ((.exchange 23 38 4),[(.neg 38),(.neg 23),(.pos 18),(.pos 59)]),
   ((.exchange 23 56 4),[(.neg 56),(.neg 23),(.pos 16),(.pos 18),(.pos 59)]),
   ((.exchange 23 60 4),[(.neg 60),(.neg 23),(.pos 18),(.pos 59)]),
   ((.exchange 24 37 4),[(.neg 37),(.neg 24),(.pos 17),(.pos 60)]),
   ((.exchange 24 38 4),[(.neg 38),(.neg 24),(.pos 18),(.pos 60)]),
   ((.exchange 24 56 4),[(.neg 56),(.neg 24),(.pos 17),(.pos 60)]),
   ((.exchange 24 57 4),[(.neg 57),(.neg 24),(.pos 18),(.pos 60)]),
   ((.exchange 24 58 4),[(.neg 58),(.neg 24),(.pos 17),(.pos 60)]),
   ((.exchange 24 59 4),[(.neg 59),(.neg 24),(.pos 18),(.pos 60)]),
   ((.exchange 26 66 2),[(.neg 66),(.neg 26),(.pos 25),(.pos 65)]),
   ((.exchange 27 65 2),[(.neg 65),(.neg 27),(.pos 25),(.pos 66)]),
   ((.exchange 28 54 0),[(.neg 54),(.neg 28),(.pos 34),(.pos 68)]),
   ((.exchange 28 64 0),[(.neg 64),(.neg 28),(.pos 34),(.pos 68)]),
   ((.exchange 28 69 0),[(.neg 69),(.neg 28),(.pos 34),(.pos 68)]),
   ((.exchange 31 54 0),[(.neg 54),(.neg 31),(.pos 34),(.pos 69)]),
   ((.exchange 31 64 0),[(.neg 64),(.neg 31),(.pos 34),(.pos 69)]),
   ((.exchange 31 68 0),[(.neg 68),(.neg 31),(.pos 34),(.pos 69)]),
   ((.exchange 35 3 7),[(.neg 35),(.neg 3),(.pos 0),(.pos 1)]),
   ((.exchange 36 3 7),[(.neg 36),(.neg 3),(.pos 0),(.pos 2)]),
   ((.exchange 37 12 2),[(.neg 37),(.neg 12),(.pos 42),(.pos 48)]),
   ((.exchange 37 52 2),[(.neg 52),(.neg 37),(.pos 36),(.pos 42),(.pos 48)]),
   ((.exchange 38 12 2),[(.neg 38),(.neg 12),(.pos 36),(.pos 43),(.pos 49)]),
   ((.exchange 38 14 1),[(.neg 38),(.neg 14),(.pos 44),(.pos 50)]),
   ((.exchange 38 52 2),[(.neg 52),(.neg 38),(.pos 43),(.pos 49)]),
   ((.exchange 38 54 1),[(.neg 54),(.neg 38),(.pos 44),(.pos 50)]),
   ((.exchange 39 3 7),[(.neg 39),(.neg 3),(.pos 1),(.pos 2)]),
   ((.exchange 40 22 2),[(.neg 40),(.neg 22),(.pos 42),(.pos 61)]),
   ((.exchange 40 24 0),[(.neg 40),(.neg 24),(.pos 44),(.pos 63)]),
   ((.exchange 41 22 2),[(.neg 41),(.neg 22),(.pos 39),(.pos 43),(.pos 62)]),
   ((.exchange 41 24 1),[(.neg 41),(.neg 24),(.pos 44),(.pos 63)]),
   ((.exchange 42 7 4),[(.neg 42),(.neg 7),(.pos 37),(.pos 48)]),
   ((.exchange 42 20 3),[(.neg 42),(.neg 20),(.pos 40),(.pos 61)]),
   ((.exchange 42 24 0),[(.neg 42),(.neg 24),(.pos 44),(.pos 64)]),
   ((.exchange 42 28 4),[(.neg 42),(.neg 28),(.pos 48),(.pos 58)]),
   ((.exchange 43 7 4),[(.neg 43),(.neg 7),(.pos 36),(.pos 38),(.pos 49)]),
   ((.exchange 43 20 3),[(.neg 43),(.neg 20),(.pos 39),(.pos 41),(.pos 62)]),
   ((.exchange 43 28 4),[(.neg 43),(.neg 28),(.pos 36),(.pos 49),(.pos 59)]),
   ((.exchange 43 50 1),[(.neg 50),(.neg 43),(.pos 44),(.pos 54)]),
   ((.exchange 44 8 4),[(.neg 44),(.neg 8),(.pos 38),(.pos 50)]),
   ((.exchange 44 12 2),[(.neg 44),(.neg 12),(.pos 42),(.pos 54)]),
   ((.exchange 44 20 3),[(.neg 44),(.neg 20),(.pos 40),(.pos 63)]),
   ((.exchange 44 21 3),[(.neg 44),(.neg 21),(.pos 41),(.pos 63)]),
   ((.exchange 44 30 4),[(.neg 44),(.neg 30),(.pos 50),(.pos 60)]),
   ((.exchange 44 51 2),[(.neg 51),(.neg 44),(.pos 42),(.pos 54)]),
   ((.exchange 44 66 4),[(.neg 66),(.neg 44),(.pos 38),(.pos 50),(.pos 60)]),
   ((.exchange 44 67 4),[(.neg 67),(.neg 44),(.pos 50),(.pos 60)]),
   ((.exchange 45 3 5),[(.neg 45),(.neg 3),(.pos 35),(.pos 36),(.pos 39)]),
   ((.exchange 46 28 2),[(.neg 46),(.neg 28),(.pos 48),(.pos 65)]),
   ((.exchange 46 30 0),[(.neg 46),(.neg 30),(.pos 50),(.pos 67)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_1 : List (Origin 70 66 × List Sat.Literal) :=
  [((.exchange 47 28 2),[(.neg 47),(.neg 28),(.pos 45),(.pos 49),(.pos 66)]),
   ((.exchange 48 3 5),[(.neg 48),(.neg 3),(.pos 37),(.pos 42)]),
   ((.exchange 48 20 3),[(.neg 48),(.neg 20),(.pos 46),(.pos 51),(.pos 65)]),
   ((.exchange 48 60 0),[(.neg 60),(.neg 48),(.pos 50),(.pos 68)]),
   ((.exchange 48 63 0),[(.neg 63),(.neg 48),(.pos 50),(.pos 54),(.pos 68)]),
   ((.exchange 48 67 0),[(.neg 67),(.neg 48),(.pos 50),(.pos 68)]),
   ((.exchange 49 3 5),[(.neg 49),(.neg 3),(.pos 36),(.pos 38),(.pos 43)]),
   ((.exchange 49 14 1),[(.neg 49),(.neg 14),(.pos 50),(.pos 54)]),
   ((.exchange 49 30 1),[(.neg 49),(.neg 30),(.pos 50),(.pos 68)]),
   ((.exchange 49 33 1),[(.neg 49),(.neg 33),(.pos 50),(.pos 54),(.pos 68)]),
   ((.exchange 49 53 1),[(.neg 53),(.neg 49),(.pos 50),(.pos 54)]),
   ((.exchange 49 63 1),[(.neg 63),(.neg 49),(.pos 50),(.pos 54),(.pos 68)]),
   ((.exchange 49 69 3),[(.neg 69),(.neg 49),(.pos 52),(.pos 66)]),
   ((.exchange 50 12 2),[(.neg 50),(.neg 12),(.pos 48),(.pos 54)]),
   ((.exchange 50 13 2),[(.neg 50),(.neg 13),(.pos 49),(.pos 54)]),
   ((.exchange 50 20 3),[(.neg 50),(.neg 20),(.pos 46),(.pos 53),(.pos 67)]),
   ((.exchange 50 24 5),[(.neg 50),(.neg 24),(.pos 44),(.pos 60)]),
   ((.exchange 50 28 2),[(.neg 50),(.neg 28),(.pos 48),(.pos 68)]),
   ((.exchange 50 29 2),[(.neg 50),(.neg 29),(.pos 49),(.pos 68)]),
   ((.exchange 50 51 2),[(.neg 51),(.neg 50),(.pos 48),(.pos 54)]),
   ((.exchange 50 61 5),[(.neg 61),(.neg 50),(.pos 37),(.pos 44),(.pos 60)]),
   ((.exchange 50 62 3),[(.neg 62),(.neg 50),(.pos 47),(.pos 53),(.pos 67)]),
   ((.exchange 50 63 5),[(.neg 63),(.neg 50),(.pos 44),(.pos 60)]),
   ((.exchange 50 66 2),[(.neg 66),(.neg 50),(.pos 49),(.pos 68)]),
   ((.exchange 51 58 5),[(.neg 58),(.neg 51),(.pos 42),(.pos 61)]),
   ((.exchange 52 58 5),[(.neg 58),(.neg 52),(.pos 39),(.pos 43),(.pos 62)]),
   ((.exchange 53 24 5),[(.neg 53),(.neg 24),(.pos 44),(.pos 63)]),
   ((.exchange 54 3 5),[(.neg 54),(.neg 3),(.pos 42),(.pos 44)]),
   ((.exchange 54 37 4),[(.neg 54),(.neg 37),(.pos 48),(.pos 50)]),
   ((.exchange 54 38 4),[(.neg 54),(.neg 38),(.pos 49),(.pos 50)]),
   ((.exchange 54 46 4),[(.neg 54),(.neg 46),(.pos 48),(.pos 50)]),
   ((.exchange 54 47 4),[(.neg 54),(.neg 47),(.pos 49),(.pos 50)]),
   ((.exchange 55 3 6),[(.neg 55),(.neg 3),(.pos 35),(.pos 36),(.pos 39)]),
   ((.exchange 56 31 2),[(.neg 56),(.neg 31),(.pos 61),(.pos 65)]),
   ((.exchange 56 33 0),[(.neg 56),(.neg 33),(.pos 63),(.pos 67)]),
   ((.exchange 57 31 2),[(.neg 57),(.neg 31),(.pos 55),(.pos 62),(.pos 66)]),
   ((.exchange 58 12 6),[(.neg 58),(.neg 12),(.pos 42),(.pos 48)]),
   ((.exchange 58 32 3),[(.neg 58),(.neg 32),(.pos 55),(.pos 61),(.pos 65)]),
   ((.exchange 59 12 6),[(.neg 59),(.neg 12),(.pos 36),(.pos 43),(.pos 49)]),
   ((.exchange 59 32 3),[(.neg 59),(.neg 32),(.pos 62),(.pos 66)]),
   ((.exchange 60 33 3),[(.neg 60),(.neg 33),(.pos 63),(.pos 67)]),
   ((.exchange 60 69 3),[(.neg 69),(.neg 60),(.pos 63),(.pos 67)]),
   ((.exchange 61 3 6),[(.neg 61),(.neg 3),(.pos 40),(.pos 42)]),
   ((.exchange 61 26 4),[(.neg 61),(.neg 26),(.pos 56),(.pos 65)]),
   ((.exchange 61 49 4),[(.neg 61),(.neg 49),(.pos 55),(.pos 58),(.pos 65)]),
   ((.exchange 61 50 0),[(.neg 61),(.neg 50),(.pos 63),(.pos 64),(.pos 69)]),
   ((.exchange 61 60 0),[(.neg 61),(.neg 60),(.pos 63),(.pos 64)]),
   ((.exchange 62 3 6),[(.neg 62),(.neg 3),(.pos 39),(.pos 41),(.pos 43)]),
   ((.exchange 62 7 4),[(.neg 62),(.neg 7),(.pos 55),(.pos 57),(.pos 59),(.pos 66)]),
   ((.exchange 62 26 4),[(.neg 62),(.neg 26),(.pos 55),(.pos 57),(.pos 66)]),
   ((.exchange 62 49 4),[(.neg 62),(.neg 49),(.pos 59),(.pos 66)]),
   ((.exchange 62 50 1),[(.neg 62),(.neg 50),(.pos 63),(.pos 64),(.pos 69)]),
   ((.exchange 62 53 1),[(.neg 62),(.neg 53),(.pos 63),(.pos 69)]),
   ((.exchange 63 3 6),[(.neg 63),(.neg 3),(.pos 40),(.pos 44)]),
   ((.exchange 63 7 4),[(.neg 63),(.neg 7),(.pos 56),(.pos 60),(.pos 67)]),
   ((.exchange 63 14 6),[(.neg 63),(.neg 14),(.pos 44),(.pos 53)]),
   ((.exchange 63 22 2),[(.neg 63),(.neg 22),(.pos 61),(.pos 64)]),
   ((.exchange 63 30 4),[(.neg 63),(.neg 30),(.pos 60),(.pos 67)]),
   ((.exchange 63 31 2),[(.neg 63),(.neg 31),(.pos 61),(.pos 69)]),
   ((.exchange 63 32 2),[(.neg 63),(.neg 32),(.pos 62),(.pos 69)]),
   ((.exchange 63 43 2),[(.neg 63),(.neg 43),(.pos 62),(.pos 64)]),
   ((.exchange 63 49 4),[(.neg 63),(.neg 49),(.pos 57),(.pos 60),(.pos 67)]),
   ((.exchange 63 51 2),[(.neg 63),(.neg 51),(.pos 61),(.pos 69)]),
   ((.exchange 64 3 6),[(.neg 64),(.neg 3),(.pos 42),(.pos 44)]),
   ((.exchange 64 4 6),[(.neg 64),(.neg 4),(.pos 43),(.pos 44)]),
   ((.exchange 64 21 3),[(.neg 64),(.neg 21),(.pos 62),(.pos 63)]),
   ((.exchange 64 40 3),[(.neg 64),(.neg 40),(.pos 61),(.pos 63)]),
   ((.exchange 65 3 5),[(.neg 65),(.neg 3),(.pos 56),(.pos 58),(.pos 61)]),
   ((.exchange 65 3 6),[(.neg 65),(.neg 3),(.pos 46),(.pos 48),(.pos 51)]),
   ((.exchange 65 22 5),[(.neg 65),(.neg 22),(.pos 58),(.pos 61)]),
   ((.exchange 65 33 0),[(.neg 65),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 65 44 0),[(.neg 65),(.neg 44),(.pos 67),(.pos 68),(.pos 69)]),
   ((.exchange 65 60 0),[(.neg 65),(.neg 60),(.pos 67),(.pos 68)]),
   ((.exchange 65 63 0),[(.neg 65),(.neg 63),(.pos 67),(.pos 69)]),
   ((.exchange 66 3 5),[(.neg 66),(.neg 3),(.pos 55),(.pos 57),(.pos 59),(.pos 62)]),
   ((.exchange 66 3 6),[(.neg 66),(.neg 3),(.pos 45),(.pos 47),(.pos 49),(.pos 52)]),
   ((.exchange 66 22 5),[(.neg 66),(.neg 22),(.pos 55),(.pos 59),(.pos 62)]),
   ((.exchange 66 33 1),[(.neg 66),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 66 44 1),[(.neg 66),(.neg 44),(.pos 67),(.pos 68),(.pos 69)]),
   ((.exchange 66 63 1),[(.neg 66),(.neg 63),(.pos 67),(.pos 69)]),
   ((.exchange 67 3 5),[(.neg 67),(.neg 3),(.pos 56),(.pos 60),(.pos 63)]),
   ((.exchange 67 3 6),[(.neg 67),(.neg 3),(.pos 46),(.pos 50),(.pos 53)]),
   ((.exchange 67 12 2),[(.neg 67),(.neg 12),(.pos 65),(.pos 68),(.pos 69)]),
   ((.exchange 67 13 2),[(.neg 67),(.neg 13),(.pos 66),(.pos 68),(.pos 69)]),
   ((.exchange 67 24 5),[(.neg 67),(.neg 24),(.pos 60),(.pos 63)]),
   ((.exchange 67 28 2),[(.neg 67),(.neg 28),(.pos 65),(.pos 68)]),
   ((.exchange 67 31 2),[(.neg 67),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 67 32 2),[(.neg 67),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 67 41 5),[(.neg 67),(.neg 41),(.pos 57),(.pos 63)]),
   ((.exchange 67 43 6),[(.neg 67),(.neg 43),(.pos 47),(.pos 50),(.pos 53)]),
   ((.exchange 67 44 6),[(.neg 67),(.neg 44),(.pos 50),(.pos 53)]),
   ((.exchange 67 51 2),[(.neg 67),(.neg 51),(.pos 65),(.pos 69)]),
   ((.exchange 67 52 2),[(.neg 67),(.neg 52),(.pos 66),(.pos 69)]),
   ((.exchange 67 64 5),[(.neg 67),(.neg 64),(.pos 60),(.pos 63)]),
   ((.exchange 68 20 3),[(.neg 68),(.neg 20),(.pos 65),(.pos 67),(.pos 69)]),
   ((.exchange 68 41 6),[(.neg 68),(.neg 41),(.pos 49),(.pos 50),(.pos 54)]),
   ((.exchange 68 46 3),[(.neg 68),(.neg 46),(.pos 65),(.pos 67)]),
   ((.exchange 68 47 3),[(.neg 68),(.neg 47),(.pos 66),(.pos 67)]),
   ((.exchange 69 20 5),[(.neg 69),(.neg 20),(.pos 61),(.pos 63)]),
   ((.exchange 69 21 5),[(.neg 69),(.neg 21),(.pos 62),(.pos 63)]),
   ((.exchange 69 26 4),[(.neg 69),(.neg 26),(.pos 65),(.pos 67)]),
   ((.exchange 69 27 4),[(.neg 69),(.neg 27),(.pos 66),(.pos 67)]),
   ((.exchange 69 46 4),[(.neg 69),(.neg 46),(.pos 65),(.pos 67)]),
   ((.exchange 69 47 4),[(.neg 69),(.neg 47),(.pos 66),(.pos 67)]),
   ((.exchange 69 57 4),[(.neg 69),(.neg 57),(.pos 66),(.pos 67)]),
   (.newPoint,[(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 0),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 54),(.neg 50),(.neg 44),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 51),(.pos 52),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 65),(.pos 66)]),
   ((.excluded 1),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 54),(.neg 49),(.neg 48),(.neg 43),(.neg 42),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 2),[(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 68),(.pos 69)]),
   ((.excluded 3),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 51),(.pos 52),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60)]),
   ((.excluded 4),[(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 53),(.neg 52),(.neg 51),(.neg 47),(.neg 46),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 50),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 68),(.pos 69)]),
   ((.excluded 5),[(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 6),[(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 68),(.pos 69)]),
   ((.excluded 7),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 42),(.pos 43),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 8),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 42),(.pos 43),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60)]),
   ((.excluded 9),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 65),(.pos 66)]),
   ((.excluded 10),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 65),(.pos 66)]),
   ((.excluded 11),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60)]),
   ((.excluded 12),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 13),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60)]),
   ((.excluded 14),[(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 50),(.neg 49),(.neg 48),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 68),(.pos 69)]),
   ((.excluded 15),[(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 44),(.neg 43),(.neg 42),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 16),[(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 64),(.pos 68),(.pos 69)]),
   ((.excluded 17),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 49),(.neg 48),(.neg 44),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 45),(.pos 46),(.pos 47),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 55),(.pos 61),(.pos 62),(.pos 67)]),
   ((.excluded 18),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 45),(.pos 46),(.pos 47),(.pos 51),(.pos 52),(.pos 53),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 19),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 50),(.neg 43),(.neg 42),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 40),(.pos 41),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 51),(.pos 52),(.pos 53),(.pos 55),(.pos 63),(.pos 65),(.pos 66)]),
   ((.excluded 20),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 50),(.neg 44),(.neg 43),(.neg 42),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 51),(.pos 52),(.pos 53),(.pos 55),(.pos 65),(.pos 66)]),
   ((.excluded 21),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 50),(.neg 49),(.neg 48),(.neg 43),(.neg 42),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 40),(.pos 41),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 51),(.pos 52),(.pos 53),(.pos 55),(.pos 63)])]

theorem certificates_1_valid : ∀ oc ∈ certificates_1,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_2 : List (Origin 70 66 × List Sat.Literal) :=
  [((.excluded 22),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 55),(.pos 67)]),
   ((.excluded 23),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 51),(.pos 52),(.pos 53),(.pos 55)]),
   ((.excluded 24),[(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 54),(.pos 55),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 25),[(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 54),(.pos 55),(.pos 64),(.pos 68),(.pos 69)]),
   ((.excluded 26),[(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 54),(.pos 55),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 27),[(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 50),(.pos 54),(.pos 55),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 68),(.pos 69)]),
   ((.excluded 28),[(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 50),(.pos 54),(.pos 55),(.pos 64),(.pos 68),(.pos 69)]),
   ((.excluded 29),[(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 54),(.pos 55),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 68),(.pos 69)]),
   ((.excluded 30),[(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 54),(.pos 55),(.pos 64),(.pos 68),(.pos 69)]),
   ((.excluded 31),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 45),(.pos 55),(.pos 67)]),
   ((.excluded 32),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 45),(.pos 50),(.pos 55),(.pos 63),(.pos 65),(.pos 66)]),
   ((.excluded 33),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 45),(.pos 50),(.pos 55),(.pos 65),(.pos 66)]),
   ((.excluded 34),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 45),(.pos 55),(.pos 63),(.pos 65),(.pos 66)]),
   ((.excluded 35),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 45),(.pos 55),(.pos 65),(.pos 66)]),
   ((.excluded 36),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 45),(.pos 50),(.pos 55),(.pos 63)]),
   ((.excluded 37),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 45),(.pos 50),(.pos 55)]),
   ((.excluded 38),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 45),(.pos 55),(.pos 63)]),
   ((.excluded 39),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 45),(.pos 55)]),
   ((.excluded 40),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 65),(.pos 66)]),
   ((.excluded 41),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 50),(.pos 55),(.pos 63),(.pos 65),(.pos 66)]),
   ((.excluded 42),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 50),(.pos 55),(.pos 65),(.pos 66)]),
   ((.excluded 43),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 63),(.pos 65),(.pos 66)]),
   ((.excluded 44),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 65),(.pos 66)]),
   ((.excluded 45),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 50),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 46),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 50),(.pos 55),(.pos 63)]),
   ((.excluded 47),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 50),(.pos 55)]),
   ((.excluded 48),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 63)]),
   ((.excluded 49),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 63)]),
   ((.excluded 50),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 61),(.pos 62),(.pos 67)]),
   ((.excluded 51),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 52),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 61),(.pos 62),(.pos 67)]),
   ((.excluded 53),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 54),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 67)]),
   ((.excluded 55),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 55)]),
   ((.excluded 56),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 67)]),
   ((.excluded 57),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 55)]),
   ((.excluded 58),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 61),(.pos 62),(.pos 67)]),
   ((.excluded 59),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 60),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 61),(.pos 62),(.pos 67)]),
   ((.excluded 61),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 62),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 67)]),
   ((.excluded 63),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55)]),
   ((.excluded 64),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 67)]),
   ((.excluded 65),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55)])]

theorem certificates_2_valid : ∀ oc ∈ certificates_2,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



theorem witness_0 : ∀ j : Fin 66,
    let w : Fin 66 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 66,
      let w : Fin 66 := ⟨0 + j.val,by omega⟩
      target w < MatroidCatalogue.count 8 4 ∧
        Papers.RationalityTen.MatroidChecked.FastSemanticChecks.RawWitness 8 (N7R4.familyMasks.get 41)
        (fun i : Fin 70 => N8R4.gridMasks.get i.val) newIndex (models w)
        (N8R4.familyMasks.get (target w)) (permutation w) := by
    refine (Fin.forall_fin_add (m := 33) (n := 33) _).2 ⟨?_, ?_⟩
    · refine (Fin.forall_fin_add (m := 16) (n := 17) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
          · decide +kernel
          · decide +kernel
        · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
          · decide +kernel
          · decide +kernel
      · refine (Fin.forall_fin_add (m := 8) (n := 9) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
          · decide +kernel
          · decide +kernel
        · refine (Fin.forall_fin_add (m := 4) (n := 5) _).2 ⟨?_, ?_⟩
          · decide +kernel
          · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
    · refine (Fin.forall_fin_add (m := 16) (n := 17) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 8) (n := 8) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
          · decide +kernel
          · decide +kernel
        · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
          · decide +kernel
          · decide +kernel
      · refine (Fin.forall_fin_add (m := 8) (n := 9) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
          · decide +kernel
          · decide +kernel
        · refine (Fin.forall_fin_add (m := 4) (n := 5) _).2 ⟨?_, ?_⟩
          · decide +kernel
          · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
  intro j
  have hj := hfast j
  exact ⟨hj.1,Papers.RationalityTen.MatroidChecked.FastSemanticChecks.rawWitness_sound 8 _ _ _ _ _ _ hj.2⟩


end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C41

/- Source: MatroidCatalogue/Cases/N8R4C41Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C41

noncomputable def certificates : List (Origin 70 66 × List Sat.Literal) :=
  certificates_0 ++ certificates_1 ++ certificates_2

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  intro oc hoc
  simp only [certificates,List.mem_append,or_assoc] at hoc
  rcases hoc with h0 | h1 | h2
  · exact certificates_0_valid oc h0
  · exact certificates_1_valid oc h1
  · exact certificates_2_valid oc h2

theorem models_valid : ∀ w : Fin 66,
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 66) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 8) 4)
    (hold : M.bases.filter ((7 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 8 4, IsomorphicWithin 8 M.bases B := by
  apply extension_covered_of_certificate (n:=7) (r:=4) (by decide)
    catalogue old U newIndex models certificates
    N8R4.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C41.formula []
    exact Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C41.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 8 4 (target w),family_mem 8 4 (target w) hw.1,?_⟩
    exact validWitness_sound 8 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C41


end
end
end BundlePart5

section BundlePart6
/- Source: MatroidChecked/SemanticChunks/Cases05Part07.lean -/




@[expose] public section
noncomputable section

/- Source: MatroidCatalogue/Cases/N8R4C42Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C42

abbrev U := N8R4.grid
noncomputable def old : Finset (Finset (Fin 8)) := N7R4.family 42
noncomputable def newIndexTree : Table ℕ := (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf 35) (.leaf 36)) (.node 3 (.leaf 37) (.leaf 38))) (.node 6 (.node 5 (.leaf 39) (.leaf 40)) (.node 7 (.leaf 41) (.leaf 42)))) (.node 12 (.node 10 (.node 9 (.leaf 43) (.leaf 44)) (.node 11 (.leaf 45) (.leaf 46))) (.node 14 (.node 13 (.leaf 47) (.leaf 48)) (.node 15 (.leaf 49) (.node 16 (.leaf 50) (.leaf 51)))))) (.node 26 (.node 21 (.node 19 (.node 18 (.leaf 52) (.leaf 53)) (.node 20 (.leaf 54) (.leaf 55))) (.node 23 (.node 22 (.leaf 56) (.leaf 57)) (.node 24 (.leaf 58) (.node 25 (.leaf 59) (.leaf 60))))) (.node 30 (.node 28 (.node 27 (.leaf 61) (.leaf 62)) (.node 29 (.leaf 63) (.leaf 64))) (.node 32 (.node 31 (.leaf 65) (.leaf 66)) (.node 33 (.leaf 67) (.node 34 (.leaf 68) (.leaf 69)))))))
noncomputable def newIndex (i : Fin 35) : Fin 70 := Fin.ofNat 70 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 56 (.node 28 (.node 14 (.node 7 (.node 3 (.node 1 (.leaf (30870635008,96,5761224)) (.node 2 (.leaf (29729776000,111,7858312)) (.leaf (17112818560,125,6212808)))) (.node 5 (.node 4 (.leaf (25166406528,125,5761224)) (.leaf (34293212032,133,7858312))) (.node 6 (.leaf (16171196428,115,8301832)) (.leaf (1071645580,115,8215816))))) (.node 10 (.node 8 (.leaf (17177830284,168,12467336)) (.node 9 (.leaf (29861896716,129,6208776)) (.leaf (25566962188,136,6208776)))) (.node 12 (.node 11 (.leaf (34156896780,137,8301832)) (.leaf (30868537740,129,6151432))) (.node 13 (.leaf (30600102796,136,6151432)) (.leaf (31136973708,137,8215816)))))) (.node 21 (.node 17 (.node 15 (.leaf (25499853196,169,8309896)) (.node 16 (.leaf (34089787788,170,10402952)) (.leaf (29526352780,169,8281224)))) (.node 19 (.node 18 (.leaf (30063223692,170,10345608)) (.leaf (33821352844,176,10402952))) (.node 20 (.leaf (25768289164,176,10345608)) (.leaf (34358223756,177,12467336))))) (.node 24 (.node 22 (.leaf (25166288992,115,7857416)) (.node 23 (.leaf (1047520,115,7072520)) (.leaf (25166871520,168,11789960)))) (.node 26 (.node 25 (.leaf (29730249312,129,5760776)) (.leaf (17113782880,136,5760776))) (.node 27 (.leaf (34293652064,137,7857416)) (.leaf (30871091680,129,5237512))))))) (.node 42 (.node 35 (.node 31 (.node 29 (.leaf (30870600672,136,5237512)) (.node 30 (.leaf (30871124960,137,7072520)) (.leaf (17113774560,169,7858312)))) (.node 33 (.node 32 (.leaf (34293643744,170,9954952)) (.leaf (29729749984,169,7596680))) (.node 34 (.leaf (29730274272,170,9431688)) (.leaf (34293152736,176,9954952))))) (.node 38 (.node 36 (.leaf (17113807840,176,9431688)) (.node 37 (.leaf (34293677024,177,11789960)) (.leaf (30600067180,273,10139080)))) (.node 40 (.node 39 (.leaf (29526325356,274,12530952)) (.leaf (33821292652,275,12530952))) (.node 41 (.leaf (25566845932,273,10081736)) (.leaf (25499737068,274,12444936)))))) (.node 49 (.node 45 (.node 43 (.leaf (25768172524,275,12444936)) (.node 44 (.leaf (29861870572,283,11746952)) (.leaf (34156837868,293,11742920)))) (.node 47 (.node 46 (.leaf (30063197164,294,15850632)) (.leaf (30868503532,283,11660936))) (.node 48 (.leaf (31136938988,293,11628232)) (.leaf (34089729004,294,15907976))))) (.node 52 (.node 50 (.leaf (34358164460,295,16398984)) (.node 51 (.leaf (16172162028,273,9382856)) (.leaf (16172153836,274,11513096)))) (.node 54 (.node 53 (.leaf (16172186604,275,11513096)) (.leaf (29526825964,283,12220040))) (.node 55 (.leaf (33821793260,293,12219592)) (.leaf (29526850540,294,15624840)))))))) (.node 84 (.node 70 (.node 63 (.node 59 (.node 57 (.leaf (30600559596,283,11435144)) (.node 58 (.leaf (30600592364,293,11173064)) (.leaf (33821785068,294,16148104)))) (.node 61 (.node 60 (.leaf (33821817836,295,15947400)) (.leaf (1072691820,273,9268168))) (.node 62 (.leaf (1072691692,274,11369736)) (.leaf (1072692204,275,11369736))))) (.node 66 (.node 64 (.leaf (31137462764,293,15854216)) (.node 65 (.leaf (30868994668,285,8059016)) (.leaf (31137430124,286,12220040)))) (.node 68 (.node 67 (.leaf (30869027436,286,11746952)) (.leaf (31137462892,296,8345736))) (.node 69 (.leaf (30868995052,288,11660936)) (.leaf (31137430508,289,11664520)))))) (.node 77 (.node 73 (.node 71 (.leaf (30869027820,289,11431560)) (.node 72 (.leaf (31137463276,297,11664520)) (.leaf (30063721068,293,16434824)))) (.node 75 (.node 74 (.leaf (25500318316,283,12306056)) (.leaf (25768753772,293,12305608))) (.node 76 (.leaf (34090220140,288,12306056)) (.leaf (34090252908,289,12302472))))) (.node 80 (.node 78 (.leaf (17178786412,283,12531848)) (.node 79 (.leaf (34358655596,289,12535432)) (.leaf (17178819180,293,12527816)))) (.node 82 (.node 81 (.leaf (34358688364,297,12535432)) (.leaf (25500318700,294,15682184))) (.node 83 (.leaf (25567427052,283,11521160)) (.leaf (25567427564,293,11259080))))))) (.node 98 (.node 91 (.node 87 (.node 85 (.leaf (25768753644,294,16205448)) (.node 86 (.leaf (25768754156,295,15918728)) (.leaf (34090228716,293,16406152)))) (.node 89 (.node 88 (.leaf (34090220524,298,16434824)) (.leaf (34090253292,299,15940232))) (.node 90 (.leaf (34157329388,293,15940232)) (.leaf (17178786796,294,16373896))))) (.node 94 (.node 92 (.leaf (34358655980,299,16406152)) (.node 93 (.leaf (17178794476,283,12445832)) (.leaf (17178794988,293,12413128)))) (.node 96 (.node 95 (.leaf (17178819052,294,16431240)) (.leaf (17178819564,295,16137352))) (.node 97 (.leaf (29862369772,285,8116360)) (.leaf (34157337068,286,12306056)))))) (.node 105 (.node 101 (.node 99 (.leaf (29862370284,286,11660936)) (.node 100 (.leaf (34157337580,296,8317064)) (.leaf (30063696364,288,12220040)))) (.node 103 (.node 102 (.leaf (34358663660,289,12478088)) (.leaf (30063696876,289,12187784))) (.node 104 (.leaf (34358664172,297,12478088)) (.leaf (29862394348,288,11746952))))) (.node 108 (.node 106 (.leaf (34157361644,289,11779208)) (.node 107 (.leaf (29862394860,289,11488904)) (.leaf (34157362156,297,11779208)))) (.node 110 (.node 109 (.leaf (30063720940,298,16406152)) (.leaf (34358688236,299,16434824))) (.node 111 (.leaf (30063721452,299,15854216)) (.leaf (34358688748,300,16434824)))))))))

noncomputable def models (i : Fin 112) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 112) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 112) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 70, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (7 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 70, (7 : Fin 8) ∈ U i → ∃ j : Fin 35, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C42

/- Source: MatroidCatalogue/Cases/N8R4C42Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C42


noncomputable def certificates_0 : List (Origin 70 112 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.neg 2)]),
   ((.fixed 3),[(.pos 3)]),
   ((.fixed 4),[(.pos 4)]),
   ((.fixed 5),[(.neg 5)]),
   ((.fixed 6),[(.neg 6)]),
   ((.fixed 7),[(.pos 7)]),
   ((.fixed 8),[(.pos 8)]),
   ((.fixed 9),[(.neg 9)]),
   ((.fixed 10),[(.neg 10)]),
   ((.fixed 11),[(.neg 11)]),
   ((.fixed 12),[(.pos 12)]),
   ((.fixed 13),[(.pos 13)]),
   ((.fixed 14),[(.pos 14)]),
   ((.fixed 15),[(.neg 15)]),
   ((.fixed 16),[(.neg 16)]),
   ((.fixed 17),[(.neg 17)]),
   ((.fixed 18),[(.neg 18)]),
   ((.fixed 19),[(.neg 19)]),
   ((.fixed 20),[(.pos 20)]),
   ((.fixed 21),[(.pos 21)]),
   ((.fixed 22),[(.pos 22)]),
   ((.fixed 23),[(.pos 23)]),
   ((.fixed 24),[(.pos 24)]),
   ((.fixed 25),[(.neg 25)]),
   ((.fixed 26),[(.pos 26)]),
   ((.fixed 27),[(.pos 27)]),
   ((.fixed 28),[(.pos 28)]),
   ((.fixed 29),[(.pos 29)]),
   ((.fixed 30),[(.pos 30)]),
   ((.fixed 31),[(.pos 31)]),
   ((.fixed 32),[(.pos 32)]),
   ((.fixed 33),[(.pos 33)]),
   ((.fixed 34),[(.pos 34)]),
   ((.exchange 3 38 4),[(.neg 38),(.neg 3),(.pos 0),(.pos 37)]),
   ((.exchange 3 41 3),[(.neg 41),(.neg 3),(.pos 1),(.pos 40)]),
   ((.exchange 3 43 2),[(.neg 43),(.neg 3),(.pos 2),(.pos 42)]),
   ((.exchange 3 46 3),[(.neg 46),(.neg 3),(.pos 10),(.pos 40)]),
   ((.exchange 3 47 3),[(.neg 47),(.neg 3),(.pos 1),(.pos 10),(.pos 40)]),
   ((.exchange 3 51 3),[(.neg 51),(.neg 3),(.pos 10),(.pos 40)]),
   ((.exchange 3 52 3),[(.neg 52),(.neg 3),(.pos 1),(.pos 10),(.pos 40)]),
   ((.exchange 3 53 3),[(.neg 53),(.neg 3),(.pos 10),(.pos 40)]),
   ((.exchange 3 56 4),[(.neg 56),(.neg 3),(.pos 17),(.pos 37)]),
   ((.exchange 3 57 4),[(.neg 57),(.neg 3),(.pos 0),(.pos 17),(.pos 37)]),
   ((.exchange 3 58 4),[(.neg 58),(.neg 3),(.pos 17),(.pos 37)]),
   ((.exchange 3 59 4),[(.neg 59),(.neg 3),(.pos 0),(.pos 17),(.pos 37)]),
   ((.exchange 3 60 4),[(.neg 60),(.neg 3),(.pos 17),(.pos 37)]),
   ((.exchange 4 37 4),[(.neg 37),(.neg 4),(.pos 0),(.pos 38)]),
   ((.exchange 4 40 3),[(.neg 40),(.neg 4),(.pos 1),(.pos 41)]),
   ((.exchange 4 42 2),[(.neg 42),(.neg 4),(.pos 2),(.pos 43)]),
   ((.exchange 4 46 3),[(.neg 46),(.neg 4),(.pos 1),(.pos 11),(.pos 41)]),
   ((.exchange 4 47 3),[(.neg 47),(.neg 4),(.pos 11),(.pos 41)]),
   ((.exchange 4 51 3),[(.neg 51),(.neg 4),(.pos 1),(.pos 11),(.pos 41)]),
   ((.exchange 4 52 3),[(.neg 52),(.neg 4),(.pos 11),(.pos 41)]),
   ((.exchange 4 53 3),[(.neg 53),(.neg 4),(.pos 11),(.pos 41)]),
   ((.exchange 7 40 3),[(.neg 40),(.neg 7),(.pos 10),(.pos 46)]),
   ((.exchange 7 41 3),[(.neg 41),(.neg 7),(.pos 5),(.pos 10),(.pos 46)]),
   ((.exchange 7 47 3),[(.neg 47),(.neg 7),(.pos 5),(.pos 46)]),
   ((.exchange 7 49 2),[(.neg 49),(.neg 7),(.pos 6),(.pos 48)]),
   ((.exchange 7 51 3),[(.neg 51),(.neg 7),(.pos 10),(.pos 46)]),
   ((.exchange 7 52 3),[(.neg 52),(.neg 7),(.pos 5),(.pos 10),(.pos 46)]),
   ((.exchange 7 53 3),[(.neg 53),(.neg 7),(.pos 10),(.pos 46)]),
   ((.exchange 8 40 3),[(.neg 40),(.neg 8),(.pos 5),(.pos 11),(.pos 47)]),
   ((.exchange 8 41 3),[(.neg 41),(.neg 8),(.pos 11),(.pos 47)]),
   ((.exchange 8 46 3),[(.neg 46),(.neg 8),(.pos 5),(.pos 47)]),
   ((.exchange 8 48 2),[(.neg 48),(.neg 8),(.pos 6),(.pos 49)]),
   ((.exchange 8 51 3),[(.neg 51),(.neg 8),(.pos 5),(.pos 11),(.pos 47)]),
   ((.exchange 8 52 3),[(.neg 52),(.neg 8),(.pos 11),(.pos 47)]),
   ((.exchange 8 53 3),[(.neg 53),(.neg 8),(.pos 11),(.pos 47)]),
   ((.exchange 12 40 3),[(.neg 40),(.neg 12),(.pos 10),(.pos 51)]),
   ((.exchange 12 41 3),[(.neg 41),(.neg 12),(.pos 9),(.pos 10),(.pos 51)]),
   ((.exchange 12 46 3),[(.neg 46),(.neg 12),(.pos 10),(.pos 51)]),
   ((.exchange 12 47 3),[(.neg 47),(.neg 12),(.pos 9),(.pos 10),(.pos 51)]),
   ((.exchange 12 52 3),[(.neg 52),(.neg 12),(.pos 9),(.pos 51)]),
   ((.exchange 12 53 3),[(.neg 53),(.neg 12),(.pos 10),(.pos 51)]),
   ((.exchange 13 40 3),[(.neg 40),(.neg 13),(.pos 9),(.pos 11),(.pos 52)]),
   ((.exchange 13 41 3),[(.neg 41),(.neg 13),(.pos 11),(.pos 52)]),
   ((.exchange 13 46 3),[(.neg 46),(.neg 13),(.pos 9),(.pos 11),(.pos 52)]),
   ((.exchange 13 47 3),[(.neg 47),(.neg 13),(.pos 11),(.pos 52)]),
   ((.exchange 13 51 3),[(.neg 51),(.neg 13),(.pos 9),(.pos 52)]),
   ((.exchange 13 53 3),[(.neg 53),(.neg 13),(.pos 11),(.pos 52)]),
   ((.exchange 14 40 3),[(.neg 40),(.neg 14),(.pos 10),(.pos 53)]),
   ((.exchange 14 41 3),[(.neg 41),(.neg 14),(.pos 11),(.pos 53)]),
   ((.exchange 14 46 3),[(.neg 46),(.neg 14),(.pos 10),(.pos 53)]),
   ((.exchange 14 47 3),[(.neg 47),(.neg 14),(.pos 11),(.pos 53)]),
   ((.exchange 14 51 3),[(.neg 51),(.neg 14),(.pos 10),(.pos 53)]),
   ((.exchange 14 52 3),[(.neg 52),(.neg 14),(.pos 11),(.pos 53)]),
   ((.exchange 20 37 4),[(.neg 37),(.neg 20),(.pos 17),(.pos 56)]),
   ((.exchange 20 62 2),[(.neg 62),(.neg 20),(.pos 19),(.pos 61)]),
   ((.exchange 21 37 4),[(.neg 37),(.neg 21),(.pos 15),(.pos 18),(.pos 57)]),
   ((.exchange 21 61 2),[(.neg 61),(.neg 21),(.pos 19),(.pos 62)]),
   ((.exchange 22 37 4),[(.neg 37),(.neg 22),(.pos 17),(.pos 58)]),
   ((.exchange 23 37 4),[(.neg 37),(.neg 23),(.pos 16),(.pos 18),(.pos 59)]),
   ((.exchange 24 37 4),[(.neg 37),(.neg 24),(.pos 17),(.pos 60)]),
   ((.exchange 26 66 2),[(.neg 66),(.neg 26),(.pos 25),(.pos 65)]),
   ((.exchange 27 65 2),[(.neg 65),(.neg 27),(.pos 25),(.pos 66)]),
   ((.exchange 35 3 7),[(.neg 35),(.neg 3),(.pos 0),(.pos 1)]),
   ((.exchange 36 3 7),[(.neg 36),(.neg 3),(.pos 0),(.pos 2)]),
   ((.exchange 37 12 2),[(.neg 37),(.neg 12),(.pos 42),(.pos 48)]),
   ((.exchange 38 12 2),[(.neg 38),(.neg 12),(.pos 36),(.pos 43),(.pos 49)]),
   ((.exchange 38 52 2),[(.neg 52),(.neg 38),(.pos 43),(.pos 49)]),
   ((.exchange 39 3 7),[(.neg 39),(.neg 3),(.pos 1),(.pos 2)]),
   ((.exchange 40 22 2),[(.neg 40),(.neg 22),(.pos 42),(.pos 61)]),
   ((.exchange 40 23 2),[(.neg 40),(.neg 23),(.pos 39),(.pos 42),(.pos 61)]),
   ((.exchange 40 24 0),[(.neg 40),(.neg 24),(.pos 44),(.pos 63)]),
   ((.exchange 40 64 0),[(.neg 64),(.neg 40),(.pos 44),(.pos 63)]),
   ((.exchange 41 13 2),[(.neg 41),(.neg 13),(.pos 43),(.pos 52)]),
   ((.exchange 41 14 1),[(.neg 41),(.neg 14),(.pos 44),(.pos 53)]),
   ((.exchange 41 22 2),[(.neg 41),(.neg 22),(.pos 39),(.pos 43),(.pos 62)]),
   ((.exchange 41 24 1),[(.neg 41),(.neg 24),(.pos 44),(.pos 63)]),
   ((.exchange 41 64 2),[(.neg 64),(.neg 41),(.pos 43),(.pos 62)]),
   ((.exchange 42 7 4),[(.neg 42),(.neg 7),(.pos 37),(.pos 48)]),
   ((.exchange 42 20 3),[(.neg 42),(.neg 20),(.pos 40),(.pos 61)]),
   ((.exchange 42 28 4),[(.neg 42),(.neg 28),(.pos 48),(.pos 58)]),
   ((.exchange 42 31 3),[(.neg 42),(.neg 31),(.pos 51),(.pos 61)]),
   ((.exchange 42 34 0),[(.neg 42),(.neg 34),(.pos 54),(.pos 64)]),
   ((.exchange 42 57 3),[(.neg 57),(.neg 42),(.pos 39),(.pos 40),(.pos 61)]),
   ((.exchange 42 63 3),[(.neg 63),(.neg 42),(.pos 40),(.pos 61)]),
   ((.exchange 42 65 3),[(.neg 65),(.neg 42),(.pos 51),(.pos 61)]),
   ((.exchange 42 69 0),[(.neg 69),(.neg 42),(.pos 54),(.pos 64)]),
   ((.exchange 43 7 4),[(.neg 43),(.neg 7),(.pos 36),(.pos 38),(.pos 49)]),
   ((.exchange 43 20 3),[(.neg 43),(.neg 20),(.pos 39),(.pos 41),(.pos 62)]),
   ((.exchange 43 27 3),[(.neg 43),(.neg 27),(.pos 41),(.pos 52),(.pos 62)]),
   ((.exchange 43 28 4),[(.neg 43),(.neg 28),(.pos 36),(.pos 49),(.pos 59)]),
   ((.exchange 43 34 1),[(.neg 43),(.neg 34),(.pos 54),(.pos 64)]),
   ((.exchange 43 57 3),[(.neg 57),(.neg 43),(.pos 41),(.pos 62)]),
   ((.exchange 43 66 3),[(.neg 66),(.neg 43),(.pos 52),(.pos 62)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_1 : List (Origin 70 112 × List Sat.Literal) :=
  [((.exchange 43 69 1),[(.neg 69),(.neg 43),(.pos 54),(.pos 64)]),
   ((.exchange 43 69 3),[(.neg 69),(.neg 43),(.pos 52),(.pos 62)]),
   ((.exchange 44 7 4),[(.neg 44),(.neg 7),(.pos 37),(.pos 50)]),
   ((.exchange 44 20 3),[(.neg 44),(.neg 20),(.pos 40),(.pos 63)]),
   ((.exchange 44 23 2),[(.neg 44),(.neg 23),(.pos 43),(.pos 64)]),
   ((.exchange 44 30 4),[(.neg 44),(.neg 30),(.pos 50),(.pos 60)]),
   ((.exchange 44 34 2),[(.neg 44),(.neg 34),(.pos 54),(.pos 64)]),
   ((.exchange 44 51 2),[(.neg 51),(.neg 44),(.pos 42),(.pos 54)]),
   ((.exchange 44 52 2),[(.neg 52),(.neg 44),(.pos 43),(.pos 54)]),
   ((.exchange 44 61 3),[(.neg 61),(.neg 44),(.pos 40),(.pos 63)]),
   ((.exchange 44 65 3),[(.neg 65),(.neg 44),(.pos 40),(.pos 53),(.pos 63)]),
   ((.exchange 44 67 3),[(.neg 67),(.neg 44),(.pos 53),(.pos 63)]),
   ((.exchange 44 68 2),[(.neg 68),(.neg 44),(.pos 54),(.pos 64)]),
   ((.exchange 44 69 3),[(.neg 69),(.neg 44),(.pos 53),(.pos 63)]),
   ((.exchange 45 3 5),[(.neg 45),(.neg 3),(.pos 35),(.pos 36),(.pos 39)]),
   ((.exchange 46 28 2),[(.neg 46),(.neg 28),(.pos 48),(.pos 65)]),
   ((.exchange 46 30 0),[(.neg 46),(.neg 30),(.pos 50),(.pos 67)]),
   ((.exchange 46 58 2),[(.neg 58),(.neg 46),(.pos 48),(.pos 65)]),
   ((.exchange 46 60 0),[(.neg 60),(.neg 46),(.pos 50),(.pos 67)]),
   ((.exchange 46 68 0),[(.neg 68),(.neg 46),(.pos 50),(.pos 67)]),
   ((.exchange 46 68 2),[(.neg 68),(.neg 46),(.pos 48),(.pos 65)]),
   ((.exchange 47 28 2),[(.neg 47),(.neg 28),(.pos 45),(.pos 49),(.pos 66)]),
   ((.exchange 47 58 2),[(.neg 58),(.neg 47),(.pos 45),(.pos 49),(.pos 66)]),
   ((.exchange 47 68 1),[(.neg 68),(.neg 47),(.pos 50),(.pos 67)]),
   ((.exchange 47 68 2),[(.neg 68),(.neg 47),(.pos 49),(.pos 66)]),
   ((.exchange 48 3 5),[(.neg 48),(.neg 3),(.pos 37),(.pos 42)]),
   ((.exchange 48 20 3),[(.neg 48),(.neg 20),(.pos 46),(.pos 51),(.pos 65)]),
   ((.exchange 48 22 5),[(.neg 48),(.neg 22),(.pos 42),(.pos 58)]),
   ((.exchange 48 27 3),[(.neg 48),(.neg 27),(.pos 45),(.pos 46),(.pos 65)]),
   ((.exchange 48 32 3),[(.neg 48),(.neg 32),(.pos 45),(.pos 51),(.pos 65)]),
   ((.exchange 48 34 0),[(.neg 48),(.neg 34),(.pos 54),(.pos 68)]),
   ((.exchange 48 69 0),[(.neg 69),(.neg 48),(.pos 54),(.pos 68)]),
   ((.exchange 49 3 5),[(.neg 49),(.neg 3),(.pos 36),(.pos 38),(.pos 43)]),
   ((.exchange 49 20 3),[(.neg 49),(.neg 20),(.pos 45),(.pos 47),(.pos 52),(.pos 66)]),
   ((.exchange 49 22 5),[(.neg 49),(.neg 22),(.pos 36),(.pos 43),(.pos 59)]),
   ((.exchange 49 27 3),[(.neg 49),(.neg 27),(.pos 47),(.pos 66)]),
   ((.exchange 49 34 1),[(.neg 49),(.neg 34),(.pos 54),(.pos 68)]),
   ((.exchange 49 53 1),[(.neg 53),(.neg 49),(.pos 50),(.pos 54)]),
   ((.exchange 49 60 1),[(.neg 60),(.neg 49),(.pos 50),(.pos 68)]),
   ((.exchange 49 61 3),[(.neg 61),(.neg 49),(.pos 45),(.pos 52),(.pos 66)]),
   ((.exchange 49 69 1),[(.neg 69),(.neg 49),(.pos 54),(.pos 68)]),
   ((.exchange 50 3 5),[(.neg 50),(.neg 3),(.pos 37),(.pos 44)]),
   ((.exchange 50 20 3),[(.neg 50),(.neg 20),(.pos 46),(.pos 53),(.pos 67)]),
   ((.exchange 50 28 2),[(.neg 50),(.neg 28),(.pos 48),(.pos 68)]),
   ((.exchange 50 34 2),[(.neg 50),(.neg 34),(.pos 54),(.pos 68)]),
   ((.exchange 50 58 2),[(.neg 58),(.neg 50),(.pos 48),(.pos 68)]),
   ((.exchange 50 59 2),[(.neg 59),(.neg 50),(.pos 49),(.pos 68)]),
   ((.exchange 50 62 3),[(.neg 62),(.neg 50),(.pos 47),(.pos 53),(.pos 67)]),
   ((.exchange 50 63 5),[(.neg 63),(.neg 50),(.pos 44),(.pos 60)]),
   ((.exchange 50 64 2),[(.neg 64),(.neg 50),(.pos 54),(.pos 68)]),
   ((.exchange 50 65 3),[(.neg 65),(.neg 50),(.pos 46),(.pos 67)]),
   ((.exchange 50 66 2),[(.neg 66),(.neg 50),(.pos 49),(.pos 68)]),
   ((.exchange 50 69 2),[(.neg 69),(.neg 50),(.pos 54),(.pos 68)]),
   ((.exchange 50 69 3),[(.neg 69),(.neg 50),(.pos 53),(.pos 67)]),
   ((.exchange 51 28 4),[(.neg 51),(.neg 28),(.pos 48),(.pos 65)]),
   ((.exchange 51 34 0),[(.neg 51),(.neg 34),(.pos 54),(.pos 69)]),
   ((.exchange 51 59 5),[(.neg 59),(.neg 51),(.pos 39),(.pos 42),(.pos 61)]),
   ((.exchange 51 68 4),[(.neg 68),(.neg 51),(.pos 48),(.pos 65)]),
   ((.exchange 52 28 4),[(.neg 52),(.neg 28),(.pos 45),(.pos 49),(.pos 66)]),
   ((.exchange 52 29 4),[(.neg 52),(.neg 29),(.pos 49),(.pos 66)]),
   ((.exchange 52 34 1),[(.neg 52),(.neg 34),(.pos 54),(.pos 69)]),
   ((.exchange 52 59 5),[(.neg 59),(.neg 52),(.pos 43),(.pos 62)]),
   ((.exchange 52 68 1),[(.neg 68),(.neg 52),(.pos 54),(.pos 69)]),
   ((.exchange 53 24 5),[(.neg 53),(.neg 24),(.pos 44),(.pos 63)]),
   ((.exchange 53 34 2),[(.neg 53),(.neg 34),(.pos 54),(.pos 69)]),
   ((.exchange 53 60 4),[(.neg 60),(.neg 53),(.pos 50),(.pos 67)]),
   ((.exchange 53 68 2),[(.neg 68),(.neg 53),(.pos 54),(.pos 69)]),
   ((.exchange 54 3 5),[(.neg 54),(.neg 3),(.pos 42),(.pos 44)]),
   ((.exchange 54 4 5),[(.neg 54),(.neg 4),(.pos 43),(.pos 44)]),
   ((.exchange 54 8 4),[(.neg 54),(.neg 8),(.pos 49),(.pos 50)]),
   ((.exchange 54 20 3),[(.neg 54),(.neg 20),(.pos 51),(.pos 53),(.pos 69)]),
   ((.exchange 54 22 5),[(.neg 54),(.neg 22),(.pos 42),(.pos 64)]),
   ((.exchange 54 23 5),[(.neg 54),(.neg 23),(.pos 43),(.pos 64)]),
   ((.exchange 54 24 5),[(.neg 54),(.neg 24),(.pos 44),(.pos 64)]),
   ((.exchange 54 28 4),[(.neg 54),(.neg 28),(.pos 48),(.pos 68)]),
   ((.exchange 54 29 4),[(.neg 54),(.neg 29),(.pos 49),(.pos 68)]),
   ((.exchange 54 30 4),[(.neg 54),(.neg 30),(.pos 50),(.pos 68)]),
   ((.exchange 54 32 3),[(.neg 54),(.neg 32),(.pos 52),(.pos 69)]),
   ((.exchange 54 37 5),[(.neg 54),(.neg 37),(.pos 42),(.pos 44)]),
   ((.exchange 54 46 4),[(.neg 54),(.neg 46),(.pos 48),(.pos 50)]),
   ((.exchange 54 47 4),[(.neg 54),(.neg 47),(.pos 49),(.pos 50)]),
   ((.exchange 54 58 4),[(.neg 58),(.neg 54),(.pos 48),(.pos 68)]),
   ((.exchange 54 58 5),[(.neg 58),(.neg 54),(.pos 42),(.pos 64)]),
   ((.exchange 54 59 4),[(.neg 59),(.neg 54),(.pos 49),(.pos 68)]),
   ((.exchange 54 59 5),[(.neg 59),(.neg 54),(.pos 43),(.pos 64)]),
   ((.exchange 54 60 4),[(.neg 60),(.neg 54),(.pos 50),(.pos 68)]),
   ((.exchange 54 60 5),[(.neg 60),(.neg 54),(.pos 44),(.pos 64)]),
   ((.exchange 54 61 3),[(.neg 61),(.neg 54),(.pos 51),(.pos 69)]),
   ((.exchange 54 61 5),[(.neg 61),(.neg 54),(.pos 42),(.pos 64)]),
   ((.exchange 54 62 5),[(.neg 62),(.neg 54),(.pos 43),(.pos 64)]),
   ((.exchange 54 63 3),[(.neg 63),(.neg 54),(.pos 53),(.pos 69)]),
   ((.exchange 54 63 5),[(.neg 63),(.neg 54),(.pos 44),(.pos 64)]),
   ((.exchange 54 65 3),[(.neg 65),(.neg 54),(.pos 51),(.pos 69)]),
   ((.exchange 54 66 3),[(.neg 66),(.neg 54),(.pos 52),(.pos 69)]),
   ((.exchange 54 67 3),[(.neg 67),(.neg 54),(.pos 53),(.pos 69)]),
   ((.exchange 54 67 4),[(.neg 67),(.neg 54),(.pos 50),(.pos 68)]),
   ((.exchange 55 3 6),[(.neg 55),(.neg 3),(.pos 35),(.pos 36),(.pos 39)]),
   ((.exchange 56 31 2),[(.neg 56),(.neg 31),(.pos 61),(.pos 65)]),
   ((.exchange 56 33 0),[(.neg 56),(.neg 33),(.pos 63),(.pos 67)]),
   ((.exchange 57 31 2),[(.neg 57),(.neg 31),(.pos 55),(.pos 62),(.pos 66)]),
   ((.exchange 58 13 6),[(.neg 58),(.neg 13),(.pos 36),(.pos 42),(.pos 48)]),
   ((.exchange 58 31 3),[(.neg 58),(.neg 31),(.pos 61),(.pos 65)]),
   ((.exchange 58 34 0),[(.neg 58),(.neg 34),(.pos 64),(.pos 68)]),
   ((.exchange 58 52 6),[(.neg 58),(.neg 52),(.pos 36),(.pos 42),(.pos 48)]),
   ((.exchange 58 54 6),[(.neg 58),(.neg 54),(.pos 42),(.pos 48)]),
   ((.exchange 59 31 3),[(.neg 59),(.neg 31),(.pos 55),(.pos 62),(.pos 66)]),
   ((.exchange 59 34 1),[(.neg 59),(.neg 34),(.pos 64),(.pos 68)]),
   ((.exchange 59 54 6),[(.neg 59),(.neg 54),(.pos 43),(.pos 49)]),
   ((.exchange 60 33 3),[(.neg 60),(.neg 33),(.pos 63),(.pos 67)]),
   ((.exchange 60 53 6),[(.neg 60),(.neg 53),(.pos 44),(.pos 50)]),
   ((.exchange 60 54 6),[(.neg 60),(.neg 54),(.pos 44),(.pos 50)]),
   ((.exchange 60 69 2),[(.neg 69),(.neg 60),(.pos 64),(.pos 68)]),
   ((.exchange 61 3 6),[(.neg 61),(.neg 3),(.pos 40),(.pos 42)]),
   ((.exchange 61 12 6),[(.neg 61),(.neg 12),(.pos 42),(.pos 51)]),
   ((.exchange 61 14 0),[(.neg 61),(.neg 14),(.pos 63),(.pos 64),(.pos 69)]),
   ((.exchange 61 34 0),[(.neg 61),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 61 37 6),[(.neg 61),(.neg 37),(.pos 40),(.pos 42)]),
   ((.exchange 61 67 4),[(.neg 67),(.neg 61),(.pos 56),(.pos 65)]),
   ((.exchange 62 3 6),[(.neg 62),(.neg 3),(.pos 39),(.pos 41),(.pos 43)]),
   ((.exchange 62 14 1),[(.neg 62),(.neg 14),(.pos 63),(.pos 64),(.pos 69)]),
   ((.exchange 62 34 1),[(.neg 62),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 62 37 6),[(.neg 62),(.neg 37),(.pos 39),(.pos 41),(.pos 43)]),
   ((.exchange 62 48 6),[(.neg 62),(.neg 48),(.pos 39),(.pos 43),(.pos 52)]),
   ((.exchange 62 67 1),[(.neg 67),(.neg 62),(.pos 63),(.pos 69)]),
   ((.exchange 62 67 4),[(.neg 67),(.neg 62),(.pos 57),(.pos 66)]),
   ((.exchange 62 68 1),[(.neg 68),(.neg 62),(.pos 64),(.pos 69)]),
   ((.exchange 63 3 6),[(.neg 63),(.neg 3),(.pos 40),(.pos 44)]),
   ((.exchange 63 4 6),[(.neg 63),(.neg 4),(.pos 41),(.pos 44)])]

theorem certificates_1_valid : ∀ oc ∈ certificates_1,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_2 : List (Origin 70 112 × List Sat.Literal) :=
  [((.exchange 63 7 4),[(.neg 63),(.neg 7),(.pos 56),(.pos 60),(.pos 67)]),
   ((.exchange 63 8 6),[(.neg 63),(.neg 8),(.pos 41),(.pos 44),(.pos 53)]),
   ((.exchange 63 22 2),[(.neg 63),(.neg 22),(.pos 61),(.pos 64)]),
   ((.exchange 63 23 2),[(.neg 63),(.neg 23),(.pos 62),(.pos 64)]),
   ((.exchange 63 32 2),[(.neg 63),(.neg 32),(.pos 62),(.pos 69)]),
   ((.exchange 63 34 2),[(.neg 63),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 63 37 6),[(.neg 63),(.neg 37),(.pos 40),(.pos 44)]),
   ((.exchange 63 38 6),[(.neg 63),(.neg 38),(.pos 41),(.pos 44)]),
   ((.exchange 63 50 6),[(.neg 63),(.neg 50),(.pos 44),(.pos 53)]),
   ((.exchange 63 51 2),[(.neg 63),(.neg 51),(.pos 61),(.pos 69)]),
   ((.exchange 63 58 2),[(.neg 63),(.neg 58),(.pos 61),(.pos 64)]),
   ((.exchange 63 65 2),[(.neg 65),(.neg 63),(.pos 61),(.pos 69)]),
   ((.exchange 64 3 6),[(.neg 64),(.neg 3),(.pos 42),(.pos 44)]),
   ((.exchange 64 4 6),[(.neg 64),(.neg 4),(.pos 43),(.pos 44)]),
   ((.exchange 64 7 4),[(.neg 64),(.neg 7),(.pos 58),(.pos 60),(.pos 68)]),
   ((.exchange 64 12 6),[(.neg 64),(.neg 12),(.pos 42),(.pos 54)]),
   ((.exchange 64 13 6),[(.neg 64),(.neg 13),(.pos 43),(.pos 54)]),
   ((.exchange 64 14 6),[(.neg 64),(.neg 14),(.pos 44),(.pos 54)]),
   ((.exchange 64 20 3),[(.neg 64),(.neg 20),(.pos 61),(.pos 63)]),
   ((.exchange 64 21 3),[(.neg 64),(.neg 21),(.pos 62),(.pos 63)]),
   ((.exchange 64 32 3),[(.neg 64),(.neg 32),(.pos 62),(.pos 69)]),
   ((.exchange 64 33 3),[(.neg 64),(.neg 33),(.pos 63),(.pos 69)]),
   ((.exchange 64 38 6),[(.neg 64),(.neg 38),(.pos 43),(.pos 44)]),
   ((.exchange 64 48 6),[(.neg 64),(.neg 48),(.pos 42),(.pos 54)]),
   ((.exchange 64 49 6),[(.neg 64),(.neg 49),(.pos 43),(.pos 54)]),
   ((.exchange 64 50 6),[(.neg 64),(.neg 50),(.pos 44),(.pos 54)]),
   ((.exchange 64 53 6),[(.neg 64),(.neg 53),(.pos 44),(.pos 54)]),
   ((.exchange 64 56 3),[(.neg 64),(.neg 56),(.pos 61),(.pos 63)]),
   ((.exchange 64 57 3),[(.neg 64),(.neg 57),(.pos 62),(.pos 63)]),
   ((.exchange 64 66 4),[(.neg 66),(.neg 64),(.pos 59),(.pos 68)]),
   ((.exchange 64 67 3),[(.neg 67),(.neg 64),(.pos 63),(.pos 69)]),
   ((.exchange 65 3 6),[(.neg 65),(.neg 3),(.pos 46),(.pos 48),(.pos 51)]),
   ((.exchange 65 7 6),[(.neg 65),(.neg 7),(.pos 46),(.pos 48)]),
   ((.exchange 65 12 6),[(.neg 65),(.neg 12),(.pos 48),(.pos 51)]),
   ((.exchange 65 33 0),[(.neg 65),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 65 34 0),[(.neg 65),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 65 44 6),[(.neg 65),(.neg 44),(.pos 46),(.pos 48),(.pos 51)]),
   ((.exchange 65 50 6),[(.neg 65),(.neg 50),(.pos 46),(.pos 48)]),
   ((.exchange 65 60 0),[(.neg 65),(.neg 60),(.pos 67),(.pos 68)]),
   ((.exchange 65 63 0),[(.neg 65),(.neg 63),(.pos 67),(.pos 69)]),
   ((.exchange 65 63 5),[(.neg 65),(.neg 63),(.pos 56),(.pos 61)]),
   ((.exchange 66 3 6),[(.neg 66),(.neg 3),(.pos 45),(.pos 47),(.pos 49),(.pos 52)]),
   ((.exchange 66 12 6),[(.neg 66),(.neg 12),(.pos 45),(.pos 49),(.pos 52)]),
   ((.exchange 66 24 5),[(.neg 66),(.neg 24),(.pos 57),(.pos 59),(.pos 62)]),
   ((.exchange 66 33 1),[(.neg 66),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 66 34 1),[(.neg 66),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 66 38 6),[(.neg 66),(.neg 38),(.pos 47),(.pos 49)]),
   ((.exchange 66 44 6),[(.neg 66),(.neg 44),(.pos 47),(.pos 49),(.pos 52)]),
   ((.exchange 66 50 6),[(.neg 66),(.neg 50),(.pos 47),(.pos 49)]),
   ((.exchange 66 60 1),[(.neg 66),(.neg 60),(.pos 67),(.pos 68)]),
   ((.exchange 67 3 6),[(.neg 67),(.neg 3),(.pos 46),(.pos 50),(.pos 53)]),
   ((.exchange 67 4 6),[(.neg 67),(.neg 4),(.pos 47),(.pos 50),(.pos 53)]),
   ((.exchange 67 7 6),[(.neg 67),(.neg 7),(.pos 46),(.pos 50)]),
   ((.exchange 67 8 6),[(.neg 67),(.neg 8),(.pos 47),(.pos 50)]),
   ((.exchange 67 14 6),[(.neg 67),(.neg 14),(.pos 50),(.pos 53)]),
   ((.exchange 67 24 5),[(.neg 67),(.neg 24),(.pos 60),(.pos 63)]),
   ((.exchange 67 28 2),[(.neg 67),(.neg 28),(.pos 65),(.pos 68)]),
   ((.exchange 67 29 2),[(.neg 67),(.neg 29),(.pos 66),(.pos 68)]),
   ((.exchange 67 31 2),[(.neg 67),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 67 32 2),[(.neg 67),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 67 34 2),[(.neg 67),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 67 64 2),[(.neg 67),(.neg 64),(.pos 68),(.pos 69)]),
   ((.exchange 68 12 6),[(.neg 68),(.neg 12),(.pos 48),(.pos 54)]),
   ((.exchange 68 13 6),[(.neg 68),(.neg 13),(.pos 49),(.pos 54)]),
   ((.exchange 68 14 6),[(.neg 68),(.neg 14),(.pos 50),(.pos 54)]),
   ((.exchange 68 22 5),[(.neg 68),(.neg 22),(.pos 58),(.pos 64)]),
   ((.exchange 68 26 3),[(.neg 68),(.neg 26),(.pos 65),(.pos 67)]),
   ((.exchange 68 27 3),[(.neg 68),(.neg 27),(.pos 66),(.pos 67)]),
   ((.exchange 68 31 3),[(.neg 68),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 68 32 3),[(.neg 68),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 68 33 3),[(.neg 68),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 68 38 6),[(.neg 68),(.neg 38),(.pos 49),(.pos 50)]),
   ((.exchange 68 44 6),[(.neg 68),(.neg 44),(.pos 50),(.pos 54)]),
   ((.exchange 68 46 6),[(.neg 68),(.neg 46),(.pos 48),(.pos 50)]),
   ((.exchange 68 47 6),[(.neg 68),(.neg 47),(.pos 49),(.pos 50)]),
   ((.exchange 68 51 6),[(.neg 68),(.neg 51),(.pos 48),(.pos 54)]),
   ((.exchange 68 52 6),[(.neg 68),(.neg 52),(.pos 49),(.pos 54)]),
   ((.exchange 68 53 6),[(.neg 68),(.neg 53),(.pos 50),(.pos 54)]),
   ((.exchange 68 56 3),[(.neg 68),(.neg 56),(.pos 65),(.pos 67)]),
   ((.exchange 68 57 3),[(.neg 68),(.neg 57),(.pos 66),(.pos 67)]),
   ((.exchange 69 7 4),[(.neg 69),(.neg 7),(.pos 65),(.pos 67),(.pos 68)]),
   ((.exchange 69 12 6),[(.neg 69),(.neg 12),(.pos 51),(.pos 54)]),
   ((.exchange 69 13 6),[(.neg 69),(.neg 13),(.pos 52),(.pos 54)]),
   ((.exchange 69 14 6),[(.neg 69),(.neg 14),(.pos 53),(.pos 54)]),
   ((.exchange 69 21 5),[(.neg 69),(.neg 21),(.pos 62),(.pos 63)]),
   ((.exchange 69 23 5),[(.neg 69),(.neg 23),(.pos 62),(.pos 64)]),
   ((.exchange 69 24 5),[(.neg 69),(.neg 24),(.pos 63),(.pos 64)]),
   ((.exchange 69 56 4),[(.neg 69),(.neg 56),(.pos 65),(.pos 67)]),
   ((.exchange 69 56 5),[(.neg 69),(.neg 56),(.pos 61),(.pos 63)]),
   ((.exchange 69 57 4),[(.neg 69),(.neg 57),(.pos 66),(.pos 67)]),
   ((.exchange 69 59 4),[(.neg 69),(.neg 59),(.pos 66),(.pos 68)]),
   ((.exchange 69 60 4),[(.neg 69),(.neg 60),(.pos 67),(.pos 68)]),
   ((.exchange 69 60 5),[(.neg 69),(.neg 60),(.pos 63),(.pos 64)]),
   (.newPoint,[(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 0),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 54),(.neg 50),(.neg 44),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 51),(.pos 52),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 65),(.pos 66)]),
   ((.excluded 1),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 54),(.neg 49),(.neg 48),(.neg 43),(.neg 42),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 2),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 69)]),
   ((.excluded 3),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 51),(.pos 52),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 68)]),
   ((.excluded 4),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 51),(.pos 52),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60)]),
   ((.excluded 5),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 50),(.neg 49),(.neg 48),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 6),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 44),(.neg 43),(.neg 42),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 7),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 69)]),
   ((.excluded 8),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 49),(.neg 48),(.neg 44),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 45),(.pos 46),(.pos 47),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 55),(.pos 61),(.pos 62),(.pos 67)]),
   ((.excluded 9),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 45),(.pos 46),(.pos 47),(.pos 51),(.pos 52),(.pos 53),(.pos 55),(.pos 61),(.pos 62),(.pos 68)]),
   ((.excluded 10),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 45),(.pos 46),(.pos 47),(.pos 51),(.pos 52),(.pos 53),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 11),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 50),(.neg 43),(.neg 42),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 40),(.pos 41),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 51),(.pos 52),(.pos 53),(.pos 55),(.pos 63),(.pos 65),(.pos 66)]),
   ((.excluded 12),[(.neg 69),(.neg 68),(.neg 67),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 50),(.neg 44),(.neg 43),(.neg 42),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 51),(.pos 52),(.pos 53),(.pos 55),(.pos 64),(.pos 65),(.pos 66)]),
   ((.excluded 13),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 50),(.neg 44),(.neg 43),(.neg 42),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 51),(.pos 52),(.pos 53),(.pos 55),(.pos 65),(.pos 66)]),
   ((.excluded 14),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 50),(.neg 49),(.neg 48),(.neg 43),(.neg 42),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 40),(.pos 41),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 51),(.pos 52),(.pos 53),(.pos 55),(.pos 63),(.pos 68)]),
   ((.excluded 15),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 50),(.neg 49),(.neg 48),(.neg 43),(.neg 42),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 40),(.pos 41),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 51),(.pos 52),(.pos 53),(.pos 55),(.pos 63)]),
   ((.excluded 16),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 55),(.pos 64),(.pos 67)]),
   ((.excluded 17),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 55),(.pos 67)]),
   ((.excluded 18),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 51),(.pos 52),(.pos 53),(.pos 55),(.pos 64)]),
   ((.excluded 19),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 51),(.pos 52),(.pos 53),(.pos 55),(.pos 68)]),
   ((.excluded 20),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 51),(.pos 52),(.pos 53),(.pos 55)]),
   ((.excluded 21),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 53),(.neg 52),(.neg 51),(.neg 47),(.neg 46),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 50),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 68)]),
   ((.excluded 22),[(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 23),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 68)]),
   ((.excluded 24),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 42),(.pos 43),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 25),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 42),(.pos 43),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 69)]),
   ((.excluded 26),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 42),(.pos 43),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60)]),
   ((.excluded 27),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 65),(.pos 66)]),
   ((.excluded 28),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 65),(.pos 66)]),
   ((.excluded 29),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 65),(.pos 66)]),
   ((.excluded 30),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 69)]),
   ((.excluded 31),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60)]),
   ((.excluded 32),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 33),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 63),(.pos 67)])]

theorem certificates_2_valid : ∀ oc ∈ certificates_2,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_3 : List (Origin 70 112 × List Sat.Literal) :=
  [((.excluded 34),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60)]),
   ((.excluded 35),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 69)]),
   ((.excluded 36),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60)]),
   ((.excluded 37),[(.neg 69),(.neg 68),(.neg 67),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 54),(.pos 55),(.pos 64),(.pos 65),(.pos 66)]),
   ((.excluded 38),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 54),(.pos 55),(.pos 64),(.pos 67)]),
   ((.excluded 39),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 54),(.pos 55),(.pos 64)]),
   ((.excluded 40),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 50),(.pos 54),(.pos 55),(.pos 61),(.pos 62),(.pos 68)]),
   ((.excluded 41),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 50),(.pos 54),(.pos 55),(.pos 63),(.pos 68)]),
   ((.excluded 42),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 50),(.pos 54),(.pos 55),(.pos 68)]),
   ((.excluded 43),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 54),(.pos 55),(.pos 61),(.pos 62),(.pos 67)]),
   ((.excluded 44),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 54),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 45),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 54),(.pos 55),(.pos 67)]),
   ((.excluded 46),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 54),(.pos 55),(.pos 63),(.pos 65),(.pos 66)]),
   ((.excluded 47),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 54),(.pos 55),(.pos 65),(.pos 66)]),
   ((.excluded 48),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 54),(.pos 55),(.pos 63)]),
   ((.excluded 49),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 54),(.pos 55)]),
   ((.excluded 50),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 51),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 50),(.pos 55),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 52),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 53),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 64),(.pos 67)]),
   ((.excluded 54),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 64)]),
   ((.excluded 55),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 64),(.pos 67)]),
   ((.excluded 56),[(.neg 69),(.neg 68),(.neg 67),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 50),(.pos 55),(.pos 64),(.pos 65),(.pos 66)]),
   ((.excluded 57),[(.neg 69),(.neg 68),(.neg 67),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 64),(.pos 65),(.pos 66)]),
   ((.excluded 58),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 50),(.pos 55),(.pos 64)]),
   ((.excluded 59),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 64)]),
   ((.excluded 60),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 45),(.pos 55),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 61),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 62),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 63),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 65),(.pos 66)]),
   ((.excluded 64),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 45),(.pos 50),(.pos 55),(.pos 63),(.pos 65),(.pos 66)]),
   ((.excluded 65),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 45),(.pos 50),(.pos 55),(.pos 65),(.pos 66)]),
   ((.excluded 66),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 45),(.pos 55),(.pos 63),(.pos 65),(.pos 66)]),
   ((.excluded 67),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 45),(.pos 55),(.pos 65),(.pos 66)]),
   ((.excluded 68),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 50),(.pos 55),(.pos 63),(.pos 65),(.pos 66)]),
   ((.excluded 69),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 50),(.pos 55),(.pos 65),(.pos 66)]),
   ((.excluded 70),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 63),(.pos 65),(.pos 66)]),
   ((.excluded 71),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 65),(.pos 66)]),
   ((.excluded 72),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 45),(.pos 55),(.pos 67)]),
   ((.excluded 73),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 45),(.pos 55),(.pos 63),(.pos 68)]),
   ((.excluded 74),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 45),(.pos 55),(.pos 68)]),
   ((.excluded 75),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 45),(.pos 50),(.pos 55),(.pos 63)]),
   ((.excluded 76),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 45),(.pos 55),(.pos 63)]),
   ((.excluded 77),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 45),(.pos 50),(.pos 55),(.pos 69)]),
   ((.excluded 78),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 45),(.pos 50),(.pos 55)]),
   ((.excluded 79),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 45),(.pos 55),(.pos 69)]),
   ((.excluded 80),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 45),(.pos 55)]),
   ((.excluded 81),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 63),(.pos 68)]),
   ((.excluded 82),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 61),(.pos 62),(.pos 68)]),
   ((.excluded 83),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 61),(.pos 62),(.pos 68)]),
   ((.excluded 84),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 68)]),
   ((.excluded 85),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 68)]),
   ((.excluded 86),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 63)]),
   ((.excluded 87),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 50),(.pos 55),(.pos 63)]),
   ((.excluded 88),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 63)]),
   ((.excluded 89),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 50),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 90),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 50),(.pos 55),(.pos 69)]),
   ((.excluded 91),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 50),(.pos 55)]),
   ((.excluded 92),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 69)]),
   ((.excluded 93),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 69)]),
   ((.excluded 94),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 69)]),
   ((.excluded 95),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 69)]),
   ((.excluded 96),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 61),(.pos 62),(.pos 67)]),
   ((.excluded 97),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 98),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 61),(.pos 62),(.pos 67)]),
   ((.excluded 99),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 100),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 67)]),
   ((.excluded 101),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 55)]),
   ((.excluded 102),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 67)]),
   ((.excluded 103),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 55)]),
   ((.excluded 104),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 61),(.pos 62),(.pos 67)]),
   ((.excluded 105),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 106),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 61),(.pos 62),(.pos 67)]),
   ((.excluded 107),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 108),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 67)]),
   ((.excluded 109),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55)]),
   ((.excluded 110),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 67)]),
   ((.excluded 111),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55)])]

theorem certificates_3_valid : ∀ oc ∈ certificates_3,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



theorem witness_0 : ∀ j : Fin 112,
    let w : Fin 112 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 112,
      let w : Fin 112 := ⟨0 + j.val,by omega⟩
      target w < MatroidCatalogue.count 8 4 ∧
        Papers.RationalityTen.MatroidChecked.FastSemanticChecks.RawWitness 8 (N7R4.familyMasks.get 42)
        (fun i : Fin 70 => N8R4.gridMasks.get i.val) newIndex (models w)
        (N8R4.familyMasks.get (target w)) (permutation w) := by
    refine (Fin.forall_fin_add (m := 56) (n := 56) _).2 ⟨?_, ?_⟩
    · refine (Fin.forall_fin_add (m := 28) (n := 28) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 14) (n := 14) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 7) (n := 7) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 7) (n := 7) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
      · refine (Fin.forall_fin_add (m := 14) (n := 14) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 7) (n := 7) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 7) (n := 7) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
    · refine (Fin.forall_fin_add (m := 28) (n := 28) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 14) (n := 14) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 7) (n := 7) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 7) (n := 7) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
      · refine (Fin.forall_fin_add (m := 14) (n := 14) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 7) (n := 7) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 7) (n := 7) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
  intro j
  have hj := hfast j
  exact ⟨hj.1,Papers.RationalityTen.MatroidChecked.FastSemanticChecks.rawWitness_sound 8 _ _ _ _ _ _ hj.2⟩


end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C42

/- Source: MatroidCatalogue/Cases/N8R4C42Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C42

noncomputable def certificates : List (Origin 70 112 × List Sat.Literal) :=
  certificates_0 ++ certificates_1 ++ certificates_2 ++ certificates_3

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  intro oc hoc
  simp only [certificates,List.mem_append,or_assoc] at hoc
  rcases hoc with h0 | h1 | h2 | h3
  · exact certificates_0_valid oc h0
  · exact certificates_1_valid oc h1
  · exact certificates_2_valid oc h2
  · exact certificates_3_valid oc h3

theorem models_valid : ∀ w : Fin 112,
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 112) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 8) 4)
    (hold : M.bases.filter ((7 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 8 4, IsomorphicWithin 8 M.bases B := by
  apply extension_covered_of_certificate (n:=7) (r:=4) (by decide)
    catalogue old U newIndex models certificates
    N8R4.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C42.formula []
    exact Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C42.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 8 4 (target w),family_mem 8 4 (target w) hw.1,?_⟩
    exact validWitness_sound 8 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C42

end
end
end BundlePart6

section BundlePart7
/- Source: MatroidChecked/SemanticChunks/Cases06Part00.lean -/




@[expose] public section
noncomputable section

/- Source: MatroidCatalogue/Cases/N8R4C43Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C43

abbrev U := N8R4.grid
noncomputable def old : Finset (Finset (Fin 8)) := N7R4.family 43
noncomputable def newIndexTree : Table ℕ := (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf 35) (.leaf 36)) (.node 3 (.leaf 37) (.leaf 38))) (.node 6 (.node 5 (.leaf 39) (.leaf 40)) (.node 7 (.leaf 41) (.leaf 42)))) (.node 12 (.node 10 (.node 9 (.leaf 43) (.leaf 44)) (.node 11 (.leaf 45) (.leaf 46))) (.node 14 (.node 13 (.leaf 47) (.leaf 48)) (.node 15 (.leaf 49) (.node 16 (.leaf 50) (.leaf 51)))))) (.node 26 (.node 21 (.node 19 (.node 18 (.leaf 52) (.leaf 53)) (.node 20 (.leaf 54) (.leaf 55))) (.node 23 (.node 22 (.leaf 56) (.leaf 57)) (.node 24 (.leaf 58) (.node 25 (.leaf 59) (.leaf 60))))) (.node 30 (.node 28 (.node 27 (.leaf 61) (.leaf 62)) (.node 29 (.leaf 63) (.leaf 64))) (.node 32 (.node 31 (.leaf 65) (.leaf 66)) (.node 33 (.leaf 67) (.node 34 (.leaf 68) (.leaf 69)))))))
noncomputable def newIndex (i : Fin 35) : Fin 70 := Fin.ofNat 70 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 56 (.node 28 (.node 14 (.node 7 (.node 3 (.node 1 (.leaf (21165203456,115,4151322)) (.node 2 (.leaf (20877613056,115,4149530)) (.leaf (1039104000,163,6248648)))) (.node 5 (.node 4 (.leaf (21238675456,127,6241032)) (.leaf (21440198656,165,10442376))) (.node 6 (.leaf (30904451072,97,6248648)) (.leaf (16171202560,113,8334088))))) (.node 10 (.node 8 (.leaf (34157164544,135,8334088)) (.node 9 (.leaf (33814994944,130,6248648)) (.leaf (17172520960,138,8345736)))) (.node 12 (.node 11 (.leaf (34352390144,139,8345736)) (.leaf (30600067072,169,6244168))) (.node 13 (.leaf (33821292544,171,10433864)) (.leaf (34064799744,130,6248200)))))) (.node 21 (.node 17 (.node 15 (.leaf (17153628160,138,8344840)) (.node 16 (.leaf (34333497344,139,8344840)) (.leaf (30868764672,169,6245064)))) (.node 19 (.node 18 (.leaf (34089990144,171,10435208)) (.leaf (31137462272,176,6248648))) (.node 20 (.leaf (17178818560,178,12535432)) (.leaf (34358687744,179,12535432))))) (.node 24 (.node 22 (.leaf (1038091244,242,7961352)) (.node 23 (.leaf (1014764,242,7043848)) (.leaf (1039105004,269,9272648)))) (.node 26 (.node 25 (.leaf (20877894636,267,5732552)) (.leaf (21238604780,270,7765128))) (.node 27 (.leaf (21439931372,271,10091144)) (.leaf (20877966316,270,7533960))))))) (.node 42 (.node 35 (.node 31 (.node 29 (.leaf (20878162924,271,9401672)) (.node 30 (.leaf (21164923884,267,5961928)) (.leaf (21238324204,270,7763336)))) (.node 33 (.node 32 (.leaf (21439650796,271,10089800)) (.leaf (21165276140,270,7535752))) (.node 34 (.leaf (21165472748,271,9403016)) (.leaf (21440003052,282,12478088))))) (.node 38 (.node 36 (.leaf (21238873068,282,11789960)) (.node 37 (.leaf (21440199660,301,14055048)) (.leaf (30868800492,248,8215816)))) (.node 40 (.node 39 (.leaf (30600365036,248,8214920)) (.leaf (31137235948,249,8219400))) (.node 41 (.leaf (17171545068,274,8040200)) (.leaf (17152670700,274,8038856)))))) (.node 49 (.node 45 (.node 43 (.leaf (17177836524,276,10333512)) (.node 44 (.leaf (33815329772,283,9940168)) (.leaf (34352200684,293,9944200)))) (.node 47 (.node 46 (.leaf (33821621228,294,10430280)) (.leaf (34064890860,283,9938824))) (.node 48 (.leaf (34333326316,293,9942408)) (.leaf (34090056684,294,10431176))))) (.node 52 (.node 50 (.leaf (34358492140,295,14592200)) (.node 51 (.leaf (30904417260,248,7068936)) (.leaf (30904155116,248,7068040)))) (.node 54 (.node 53 (.leaf (30904679404,249,7072520)) (.leaf (16172180460,274,7810824))) (.node 55 (.leaf (16172162028,274,7809480)) (.leaf (16172186604,276,9416008)))))))) (.node 84 (.node 70 (.node 63 (.node 59 (.node 57 (.leaf (34156831724,283,10398920)) (.node 58 (.leaf (34157356012,293,10402952)) (.leaf (34156837868,294,10200904)))) (.node 61 (.node 60 (.leaf (34157075436,283,10397576)) (.leaf (34157337580,293,10401160))) (.node 62 (.leaf (34157100012,294,10201800)) (.leaf (34157362156,295,14133448))))) (.node 66 (.node 64 (.leaf (30600330220,302,14055048)) (.node 65 (.leaf (31137201132,303,14022792)) (.leaf (30600592364,303,13563144)))) (.node 68 (.node 67 (.leaf (30868503532,302,13825672)) (.leaf (31136938988,303,14021896))) (.node 69 (.leaf (30869027820,303,13564040)) (.leaf (31137463276,304,14055048)))))) (.node 77 (.node 73 (.node 71 (.leaf (33821811692,294,14571144)) (.node 72 (.leaf (17153647596,283,7829640)) (.leaf (17178813420,294,12445832)))) (.node 75 (.node 74 (.leaf (34064557036,287,9954952)) (.leaf (34332992492,288,10413256))) (.node 76 (.leaf (34065081324,288,9954952)) (.leaf (34333516780,289,9926280))))) (.node 80 (.node 78 (.leaf (34089722860,290,10413704)) (.node 79 (.leaf (34358158316,291,12478088)) (.leaf (34090247148,298,10413704)))) (.node 82 (.node 81 (.leaf (34358682604,299,12478088)) (.leaf (34333260780,294,13882568))) (.node 83 (.leaf (17153653740,294,11527432)) (.leaf (34064563180,290,9954504))))))) (.node 98 (.node 91 (.node 87 (.node 85 (.leaf (34332998636,298,9954504)) (.node 86 (.leaf (34065087468,291,11789512)) (.leaf (34333522924,299,11789512)))) (.node 89 (.node 88 (.leaf (34351873004,294,13883016)) (.leaf (34089729004,305,12535432))) (.node 90 (.leaf (34358164460,306,14599368)) (.leaf (34090228716,294,14570696))))) (.node 94 (.node 92 (.leaf (34090253292,306,14141064)) (.node 93 (.leaf (17172503532,283,8059016)) (.leaf (17178794988,294,12444936)))) (.node 96 (.node 95 (.leaf (17172528108,294,11528328)) (.leaf (17178819564,307,16434824))) (.node 97 (.leaf (33815239660,287,10413704)) (.leaf (34352110572,288,10413704)))))) (.node 105 (.node 101 (.node 99 (.leaf (33815501804,288,9954504)) (.node 100 (.leaf (34352372716,289,10155656)) (.leaf (33821531116,290,10413256)))) (.node 103 (.node 102 (.leaf (34358402028,291,12477640)) (.leaf (33821793260,298,10413256))) (.node 104 (.leaf (34358664172,299,12477640)) (.leaf (33815264236,290,9954952))))) (.node 108 (.node 106 (.leaf (34352135148,298,9954952)) (.node 107 (.leaf (33815526380,291,11789960)) (.leaf (34352397292,299,11789960)))) (.node 110 (.node 109 (.leaf (33821555692,305,12306056)) (.leaf (34358426604,306,14599816))) (.node 111 (.leaf (33821817836,306,14140616)) (.leaf (34358688748,308,16434824)))))))))

noncomputable def models (i : Fin 112) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 112) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 112) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 70, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (7 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 70, (7 : Fin 8) ∈ U i → ∃ j : Fin 35, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C43

/- Source: MatroidCatalogue/Cases/N8R4C43Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C43


noncomputable def certificates_0 : List (Origin 70 112 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.neg 2)]),
   ((.fixed 3),[(.neg 3)]),
   ((.fixed 4),[(.neg 4)]),
   ((.fixed 5),[(.neg 5)]),
   ((.fixed 6),[(.neg 6)]),
   ((.fixed 7),[(.pos 7)]),
   ((.fixed 8),[(.pos 8)]),
   ((.fixed 9),[(.neg 9)]),
   ((.fixed 10),[(.pos 10)]),
   ((.fixed 11),[(.pos 11)]),
   ((.fixed 12),[(.pos 12)]),
   ((.fixed 13),[(.pos 13)]),
   ((.fixed 14),[(.pos 14)]),
   ((.fixed 15),[(.neg 15)]),
   ((.fixed 16),[(.neg 16)]),
   ((.fixed 17),[(.pos 17)]),
   ((.fixed 18),[(.pos 18)]),
   ((.fixed 19),[(.neg 19)]),
   ((.fixed 20),[(.pos 20)]),
   ((.fixed 21),[(.pos 21)]),
   ((.fixed 22),[(.pos 22)]),
   ((.fixed 23),[(.pos 23)]),
   ((.fixed 24),[(.pos 24)]),
   ((.fixed 25),[(.neg 25)]),
   ((.fixed 26),[(.pos 26)]),
   ((.fixed 27),[(.pos 27)]),
   ((.fixed 28),[(.pos 28)]),
   ((.fixed 29),[(.pos 29)]),
   ((.fixed 30),[(.neg 30)]),
   ((.fixed 31),[(.pos 31)]),
   ((.fixed 32),[(.pos 32)]),
   ((.fixed 33),[(.pos 33)]),
   ((.fixed 34),[(.pos 34)]),
   ((.exchange 7 38 5),[(.neg 38),(.neg 7),(.pos 0),(.pos 37)]),
   ((.exchange 7 40 5),[(.neg 40),(.neg 7),(.pos 3),(.pos 37)]),
   ((.exchange 7 41 5),[(.neg 41),(.neg 7),(.pos 0),(.pos 3),(.pos 37)]),
   ((.exchange 7 42 5),[(.neg 42),(.neg 7),(.pos 3),(.pos 37)]),
   ((.exchange 7 43 5),[(.neg 43),(.neg 7),(.pos 0),(.pos 3),(.pos 37)]),
   ((.exchange 7 44 5),[(.neg 44),(.neg 7),(.pos 3),(.pos 37)]),
   ((.exchange 7 47 3),[(.neg 47),(.neg 7),(.pos 5),(.pos 46)]),
   ((.exchange 7 49 2),[(.neg 49),(.neg 7),(.pos 6),(.pos 48)]),
   ((.exchange 7 60 0),[(.neg 60),(.neg 7),(.pos 30),(.pos 50)]),
   ((.exchange 7 67 0),[(.neg 67),(.neg 7),(.pos 30),(.pos 50)]),
   ((.exchange 7 68 0),[(.neg 68),(.neg 7),(.pos 30),(.pos 50)]),
   ((.exchange 8 37 5),[(.neg 37),(.neg 8),(.pos 0),(.pos 38)]),
   ((.exchange 8 46 3),[(.neg 46),(.neg 8),(.pos 5),(.pos 47)]),
   ((.exchange 8 48 2),[(.neg 48),(.neg 8),(.pos 6),(.pos 49)]),
   ((.exchange 10 37 5),[(.neg 37),(.neg 10),(.pos 3),(.pos 40)]),
   ((.exchange 10 52 2),[(.neg 52),(.neg 10),(.pos 9),(.pos 51)]),
   ((.exchange 11 37 5),[(.neg 37),(.neg 11),(.pos 1),(.pos 4),(.pos 41)]),
   ((.exchange 11 51 2),[(.neg 51),(.neg 11),(.pos 9),(.pos 52)]),
   ((.exchange 12 37 5),[(.neg 37),(.neg 12),(.pos 3),(.pos 42)]),
   ((.exchange 13 37 5),[(.neg 37),(.neg 13),(.pos 2),(.pos 4),(.pos 43)]),
   ((.exchange 14 37 5),[(.neg 37),(.neg 14),(.pos 3),(.pos 44)]),
   ((.exchange 17 50 0),[(.neg 50),(.neg 17),(.pos 30),(.pos 60)]),
   ((.exchange 17 57 3),[(.neg 57),(.neg 17),(.pos 15),(.pos 56)]),
   ((.exchange 17 59 2),[(.neg 59),(.neg 17),(.pos 16),(.pos 58)]),
   ((.exchange 17 67 0),[(.neg 67),(.neg 17),(.pos 30),(.pos 60)]),
   ((.exchange 17 68 0),[(.neg 68),(.neg 17),(.pos 30),(.pos 60)]),
   ((.exchange 18 56 3),[(.neg 56),(.neg 18),(.pos 15),(.pos 57)]),
   ((.exchange 18 58 2),[(.neg 58),(.neg 18),(.pos 16),(.pos 59)]),
   ((.exchange 20 62 2),[(.neg 62),(.neg 20),(.pos 19),(.pos 61)]),
   ((.exchange 21 61 2),[(.neg 61),(.neg 21),(.pos 19),(.pos 62)]),
   ((.exchange 26 50 0),[(.neg 50),(.neg 26),(.pos 30),(.pos 67)]),
   ((.exchange 26 60 0),[(.neg 60),(.neg 26),(.pos 30),(.pos 67)]),
   ((.exchange 26 66 2),[(.neg 66),(.neg 26),(.pos 25),(.pos 65)]),
   ((.exchange 26 68 0),[(.neg 68),(.neg 26),(.pos 30),(.pos 67)]),
   ((.exchange 27 65 2),[(.neg 65),(.neg 27),(.pos 25),(.pos 66)]),
   ((.exchange 28 50 0),[(.neg 50),(.neg 28),(.pos 30),(.pos 68)]),
   ((.exchange 28 60 0),[(.neg 60),(.neg 28),(.pos 30),(.pos 68)]),
   ((.exchange 28 67 0),[(.neg 67),(.neg 28),(.pos 30),(.pos 68)]),
   ((.exchange 35 7 7),[(.neg 35),(.neg 7),(.pos 0),(.pos 5)]),
   ((.exchange 36 7 7),[(.neg 36),(.neg 7),(.pos 0),(.pos 6)]),
   ((.exchange 37 27 3),[(.neg 37),(.neg 27),(.pos 35),(.pos 46),(.pos 56)]),
   ((.exchange 37 28 2),[(.neg 37),(.neg 28),(.pos 48),(.pos 58)]),
   ((.exchange 37 29 2),[(.neg 37),(.neg 29),(.pos 36),(.pos 48),(.pos 58)]),
   ((.exchange 38 27 3),[(.neg 38),(.neg 27),(.pos 47),(.pos 57)]),
   ((.exchange 38 28 2),[(.neg 38),(.neg 28),(.pos 36),(.pos 49),(.pos 59)]),
   ((.exchange 38 29 2),[(.neg 38),(.neg 29),(.pos 49),(.pos 59)]),
   ((.exchange 39 7 7),[(.neg 39),(.neg 7),(.pos 1),(.pos 2),(.pos 9)]),
   ((.exchange 40 65 4),[(.neg 65),(.neg 40),(.pos 46),(.pos 56)]),
   ((.exchange 41 65 4),[(.neg 65),(.neg 41),(.pos 35),(.pos 47),(.pos 57)]),
   ((.exchange 42 32 3),[(.neg 42),(.neg 32),(.pos 39),(.pos 51),(.pos 61)]),
   ((.exchange 42 34 0),[(.neg 42),(.neg 34),(.pos 54),(.pos 64)]),
   ((.exchange 42 65 4),[(.neg 65),(.neg 42),(.pos 48),(.pos 58)]),
   ((.exchange 42 69 3),[(.neg 69),(.neg 42),(.pos 51),(.pos 61)]),
   ((.exchange 43 32 3),[(.neg 43),(.neg 32),(.pos 52),(.pos 62)]),
   ((.exchange 43 65 4),[(.neg 65),(.neg 43),(.pos 36),(.pos 49),(.pos 59)]),
   ((.exchange 43 69 3),[(.neg 69),(.neg 43),(.pos 52),(.pos 62)]),
   ((.exchange 44 33 3),[(.neg 44),(.neg 33),(.pos 53),(.pos 63)]),
   ((.exchange 44 34 2),[(.neg 44),(.neg 34),(.pos 54),(.pos 64)]),
   ((.exchange 44 68 2),[(.neg 68),(.neg 44),(.pos 54),(.pos 64)]),
   ((.exchange 44 69 3),[(.neg 69),(.neg 44),(.pos 53),(.pos 63)]),
   ((.exchange 45 7 7),[(.neg 45),(.neg 7),(.pos 5),(.pos 6)]),
   ((.exchange 46 14 0),[(.neg 46),(.neg 14),(.pos 50),(.pos 53)]),
   ((.exchange 46 17 5),[(.neg 46),(.neg 17),(.pos 37),(.pos 56)]),
   ((.exchange 46 28 2),[(.neg 46),(.neg 28),(.pos 48),(.pos 65)]),
   ((.exchange 46 29 2),[(.neg 46),(.neg 29),(.pos 45),(.pos 48),(.pos 65)]),
   ((.exchange 46 31 2),[(.neg 46),(.neg 31),(.pos 51),(.pos 65)]),
   ((.exchange 46 32 2),[(.neg 46),(.neg 32),(.pos 45),(.pos 51),(.pos 65)]),
   ((.exchange 46 43 2),[(.neg 46),(.neg 43),(.pos 45),(.pos 48),(.pos 51)]),
   ((.exchange 46 58 2),[(.neg 58),(.neg 46),(.pos 48),(.pos 65)]),
   ((.exchange 46 59 2),[(.neg 59),(.neg 46),(.pos 45),(.pos 48),(.pos 65)]),
   ((.exchange 46 60 5),[(.neg 60),(.neg 46),(.pos 37),(.pos 56)]),
   ((.exchange 46 61 2),[(.neg 61),(.neg 46),(.pos 51),(.pos 65)]),
   ((.exchange 46 62 2),[(.neg 62),(.neg 46),(.pos 45),(.pos 51),(.pos 65)]),
   ((.exchange 46 69 2),[(.neg 69),(.neg 46),(.pos 51),(.pos 65)]),
   ((.exchange 47 14 1),[(.neg 47),(.neg 14),(.pos 50),(.pos 53)]),
   ((.exchange 47 17 5),[(.neg 47),(.neg 17),(.pos 35),(.pos 38),(.pos 57)]),
   ((.exchange 47 28 2),[(.neg 47),(.neg 28),(.pos 45),(.pos 49),(.pos 66)]),
   ((.exchange 47 31 2),[(.neg 47),(.neg 31),(.pos 45),(.pos 52),(.pos 66)]),
   ((.exchange 47 54 2),[(.neg 54),(.neg 47),(.pos 49),(.pos 52)]),
   ((.exchange 47 61 2),[(.neg 61),(.neg 47),(.pos 45),(.pos 52),(.pos 66)]),
   ((.exchange 47 62 2),[(.neg 62),(.neg 47),(.pos 52),(.pos 66)]),
   ((.exchange 47 68 2),[(.neg 68),(.neg 47),(.pos 49),(.pos 66)]),
   ((.exchange 48 17 5),[(.neg 48),(.neg 17),(.pos 37),(.pos 58)]),
   ((.exchange 48 24 5),[(.neg 48),(.neg 24),(.pos 37),(.pos 42),(.pos 58)]),
   ((.exchange 48 26 3),[(.neg 48),(.neg 26),(.pos 46),(.pos 65)]),
   ((.exchange 48 32 3),[(.neg 48),(.neg 32),(.pos 45),(.pos 51),(.pos 65)]),
   ((.exchange 48 57 3),[(.neg 57),(.neg 48),(.pos 45),(.pos 46),(.pos 65)]),
   ((.exchange 48 57 5),[(.neg 57),(.neg 48),(.pos 36),(.pos 37),(.pos 58)]),
   ((.exchange 48 62 3),[(.neg 62),(.neg 48),(.pos 45),(.pos 51),(.pos 65)]),
   ((.exchange 48 63 5),[(.neg 63),(.neg 48),(.pos 37),(.pos 42),(.pos 58)]),
   ((.exchange 48 69 3),[(.neg 69),(.neg 48),(.pos 51),(.pos 65)]),
   ((.exchange 49 11 3),[(.neg 49),(.neg 11),(.pos 47),(.pos 52)]),
   ((.exchange 49 14 1),[(.neg 49),(.neg 14),(.pos 50),(.pos 54)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_1 : List (Origin 70 112 × List Sat.Literal) :=
  [((.exchange 49 17 5),[(.neg 49),(.neg 17),(.pos 36),(.pos 38),(.pos 59)]),
   ((.exchange 49 24 5),[(.neg 49),(.neg 24),(.pos 38),(.pos 43),(.pos 59)]),
   ((.exchange 49 31 3),[(.neg 49),(.neg 31),(.pos 45),(.pos 52),(.pos 66)]),
   ((.exchange 49 32 3),[(.neg 49),(.neg 32),(.pos 52),(.pos 66)]),
   ((.exchange 49 33 1),[(.neg 49),(.neg 33),(.pos 50),(.pos 54),(.pos 68)]),
   ((.exchange 49 44 1),[(.neg 49),(.neg 44),(.pos 50),(.pos 54)]),
   ((.exchange 49 57 3),[(.neg 57),(.neg 49),(.pos 47),(.pos 66)]),
   ((.exchange 49 62 3),[(.neg 62),(.neg 49),(.pos 52),(.pos 66)]),
   ((.exchange 50 10 3),[(.neg 50),(.neg 10),(.pos 46),(.pos 53)]),
   ((.exchange 50 11 3),[(.neg 50),(.neg 11),(.pos 47),(.pos 53)]),
   ((.exchange 50 12 2),[(.neg 50),(.neg 12),(.pos 48),(.pos 54)]),
   ((.exchange 50 13 2),[(.neg 50),(.neg 13),(.pos 49),(.pos 54)]),
   ((.exchange 51 7 4),[(.neg 51),(.neg 7),(.pos 46),(.pos 48)]),
   ((.exchange 51 22 5),[(.neg 51),(.neg 22),(.pos 42),(.pos 61)]),
   ((.exchange 51 26 4),[(.neg 51),(.neg 26),(.pos 46),(.pos 65)]),
   ((.exchange 51 27 4),[(.neg 51),(.neg 27),(.pos 45),(.pos 46),(.pos 65)]),
   ((.exchange 51 28 4),[(.neg 51),(.neg 28),(.pos 48),(.pos 65)]),
   ((.exchange 51 29 4),[(.neg 51),(.neg 29),(.pos 45),(.pos 48),(.pos 65)]),
   ((.exchange 51 33 0),[(.neg 51),(.neg 33),(.pos 53),(.pos 69)]),
   ((.exchange 51 38 4),[(.neg 51),(.neg 38),(.pos 45),(.pos 46),(.pos 48)]),
   ((.exchange 51 57 4),[(.neg 57),(.neg 51),(.pos 45),(.pos 46),(.pos 65)]),
   ((.exchange 51 59 4),[(.neg 59),(.neg 51),(.pos 45),(.pos 48),(.pos 65)]),
   ((.exchange 51 63 0),[(.neg 63),(.neg 51),(.pos 53),(.pos 69)]),
   ((.exchange 51 67 4),[(.neg 67),(.neg 51),(.pos 46),(.pos 65)]),
   ((.exchange 51 68 0),[(.neg 68),(.neg 51),(.pos 54),(.pos 69)]),
   ((.exchange 51 68 4),[(.neg 68),(.neg 51),(.pos 48),(.pos 65)]),
   ((.exchange 52 7 4),[(.neg 52),(.neg 7),(.pos 45),(.pos 47),(.pos 49)]),
   ((.exchange 52 22 5),[(.neg 52),(.neg 22),(.pos 39),(.pos 43),(.pos 62)]),
   ((.exchange 52 26 4),[(.neg 52),(.neg 26),(.pos 45),(.pos 47),(.pos 66)]),
   ((.exchange 52 27 4),[(.neg 52),(.neg 27),(.pos 47),(.pos 66)]),
   ((.exchange 52 28 4),[(.neg 52),(.neg 28),(.pos 45),(.pos 49),(.pos 66)]),
   ((.exchange 52 29 4),[(.neg 52),(.neg 29),(.pos 49),(.pos 66)]),
   ((.exchange 52 33 1),[(.neg 52),(.neg 33),(.pos 53),(.pos 69)]),
   ((.exchange 52 50 4),[(.neg 52),(.neg 50),(.pos 47),(.pos 49)]),
   ((.exchange 52 56 4),[(.neg 56),(.neg 52),(.pos 45),(.pos 47),(.pos 66)]),
   ((.exchange 52 57 4),[(.neg 57),(.neg 52),(.pos 47),(.pos 66)]),
   ((.exchange 52 63 1),[(.neg 63),(.neg 52),(.pos 53),(.pos 69)]),
   ((.exchange 52 64 1),[(.neg 64),(.neg 52),(.pos 54),(.pos 69)]),
   ((.exchange 52 67 4),[(.neg 67),(.neg 52),(.pos 47),(.pos 66)]),
   ((.exchange 52 68 1),[(.neg 68),(.neg 52),(.pos 54),(.pos 69)]),
   ((.exchange 52 68 4),[(.neg 68),(.neg 52),(.pos 49),(.pos 66)]),
   ((.exchange 53 13 2),[(.neg 53),(.neg 13),(.pos 52),(.pos 54)]),
   ((.exchange 53 24 5),[(.neg 53),(.neg 24),(.pos 44),(.pos 63)]),
   ((.exchange 53 28 4),[(.neg 53),(.neg 28),(.pos 46),(.pos 50),(.pos 67)]),
   ((.exchange 53 29 4),[(.neg 53),(.neg 29),(.pos 47),(.pos 50),(.pos 67)]),
   ((.exchange 53 31 2),[(.neg 53),(.neg 31),(.pos 51),(.pos 69)]),
   ((.exchange 53 32 2),[(.neg 53),(.neg 32),(.pos 52),(.pos 69)]),
   ((.exchange 53 34 2),[(.neg 53),(.neg 34),(.pos 54),(.pos 69)]),
   ((.exchange 53 68 2),[(.neg 68),(.neg 53),(.pos 54),(.pos 69)]),
   ((.exchange 54 8 4),[(.neg 54),(.neg 8),(.pos 49),(.pos 50)]),
   ((.exchange 54 10 3),[(.neg 54),(.neg 10),(.pos 51),(.pos 53)]),
   ((.exchange 54 11 3),[(.neg 54),(.neg 11),(.pos 52),(.pos 53)]),
   ((.exchange 54 22 5),[(.neg 54),(.neg 22),(.pos 42),(.pos 64)]),
   ((.exchange 54 28 4),[(.neg 54),(.neg 28),(.pos 48),(.pos 68)]),
   ((.exchange 54 29 4),[(.neg 54),(.neg 29),(.pos 49),(.pos 68)]),
   ((.exchange 54 56 4),[(.neg 56),(.neg 54),(.pos 48),(.pos 50),(.pos 68)]),
   ((.exchange 54 57 4),[(.neg 57),(.neg 54),(.pos 49),(.pos 50),(.pos 68)]),
   ((.exchange 54 61 3),[(.neg 61),(.neg 54),(.pos 51),(.pos 69)]),
   ((.exchange 54 62 3),[(.neg 62),(.neg 54),(.pos 52),(.pos 69)]),
   ((.exchange 54 63 3),[(.neg 63),(.neg 54),(.pos 53),(.pos 69)]),
   ((.exchange 54 66 4),[(.neg 66),(.neg 54),(.pos 49),(.pos 68)]),
   ((.exchange 55 7 6),[(.neg 55),(.neg 7),(.pos 35),(.pos 36),(.pos 45)]),
   ((.exchange 56 10 6),[(.neg 56),(.neg 10),(.pos 40),(.pos 46)]),
   ((.exchange 56 22 2),[(.neg 56),(.neg 22),(.pos 58),(.pos 61)]),
   ((.exchange 56 23 2),[(.neg 56),(.neg 23),(.pos 55),(.pos 58),(.pos 61)]),
   ((.exchange 56 24 0),[(.neg 56),(.neg 24),(.pos 60),(.pos 63)]),
   ((.exchange 56 29 2),[(.neg 56),(.neg 29),(.pos 55),(.pos 58),(.pos 65)]),
   ((.exchange 56 31 2),[(.neg 56),(.neg 31),(.pos 61),(.pos 65)]),
   ((.exchange 56 49 2),[(.neg 56),(.neg 49),(.pos 55),(.pos 58),(.pos 65)]),
   ((.exchange 56 53 6),[(.neg 56),(.neg 53),(.pos 40),(.pos 46)]),
   ((.exchange 56 69 2),[(.neg 69),(.neg 56),(.pos 61),(.pos 65)]),
   ((.exchange 57 7 6),[(.neg 57),(.neg 7),(.pos 35),(.pos 38),(.pos 47)]),
   ((.exchange 57 14 1),[(.neg 57),(.neg 14),(.pos 60),(.pos 63),(.pos 67)]),
   ((.exchange 57 14 6),[(.neg 57),(.neg 14),(.pos 38),(.pos 41),(.pos 47)]),
   ((.exchange 57 22 2),[(.neg 57),(.neg 22),(.pos 55),(.pos 59),(.pos 62)]),
   ((.exchange 57 28 2),[(.neg 57),(.neg 28),(.pos 55),(.pos 59),(.pos 66)]),
   ((.exchange 57 29 2),[(.neg 57),(.neg 29),(.pos 59),(.pos 66)]),
   ((.exchange 57 31 2),[(.neg 57),(.neg 31),(.pos 55),(.pos 62),(.pos 66)]),
   ((.exchange 57 43 2),[(.neg 57),(.neg 43),(.pos 59),(.pos 62)]),
   ((.exchange 57 44 1),[(.neg 57),(.neg 44),(.pos 60),(.pos 63)]),
   ((.exchange 57 53 1),[(.neg 57),(.neg 53),(.pos 63),(.pos 67)]),
   ((.exchange 57 69 2),[(.neg 69),(.neg 57),(.pos 62),(.pos 66)]),
   ((.exchange 58 7 6),[(.neg 58),(.neg 7),(.pos 37),(.pos 48)]),
   ((.exchange 58 14 0),[(.neg 58),(.neg 14),(.pos 60),(.pos 64),(.pos 68)]),
   ((.exchange 58 14 6),[(.neg 58),(.neg 14),(.pos 37),(.pos 42),(.pos 48)]),
   ((.exchange 58 26 3),[(.neg 58),(.neg 26),(.pos 56),(.pos 65)]),
   ((.exchange 58 31 3),[(.neg 58),(.neg 31),(.pos 61),(.pos 65)]),
   ((.exchange 58 32 3),[(.neg 58),(.neg 32),(.pos 55),(.pos 61),(.pos 65)]),
   ((.exchange 58 52 3),[(.neg 58),(.neg 52),(.pos 55),(.pos 61),(.pos 65)]),
   ((.exchange 59 7 6),[(.neg 59),(.neg 7),(.pos 36),(.pos 38),(.pos 49)]),
   ((.exchange 59 14 6),[(.neg 59),(.neg 14),(.pos 38),(.pos 43),(.pos 49)]),
   ((.exchange 59 26 3),[(.neg 59),(.neg 26),(.pos 55),(.pos 57),(.pos 66)]),
   ((.exchange 59 31 3),[(.neg 59),(.neg 31),(.pos 55),(.pos 62),(.pos 66)]),
   ((.exchange 59 32 3),[(.neg 59),(.neg 32),(.pos 62),(.pos 66)]),
   ((.exchange 59 34 1),[(.neg 59),(.neg 34),(.pos 64),(.pos 68)]),
   ((.exchange 59 41 3),[(.neg 59),(.neg 41),(.pos 57),(.pos 62)]),
   ((.exchange 59 44 1),[(.neg 59),(.neg 44),(.pos 60),(.pos 64)]),
   ((.exchange 59 52 3),[(.neg 59),(.neg 52),(.pos 62),(.pos 66)]),
   ((.exchange 59 63 1),[(.neg 63),(.neg 59),(.pos 60),(.pos 64)]),
   ((.exchange 59 69 1),[(.neg 69),(.neg 59),(.pos 64),(.pos 68)]),
   ((.exchange 60 21 3),[(.neg 60),(.neg 21),(.pos 57),(.pos 63)]),
   ((.exchange 60 23 2),[(.neg 60),(.neg 23),(.pos 59),(.pos 64)]),
   ((.exchange 60 43 2),[(.neg 60),(.neg 43),(.pos 59),(.pos 64)]),
   ((.exchange 60 61 2),[(.neg 61),(.neg 60),(.pos 58),(.pos 64)]),
   ((.exchange 61 18 4),[(.neg 61),(.neg 18),(.pos 55),(.pos 56),(.pos 58)]),
   ((.exchange 61 26 4),[(.neg 61),(.neg 26),(.pos 56),(.pos 65)]),
   ((.exchange 61 28 4),[(.neg 61),(.neg 28),(.pos 58),(.pos 65)]),
   ((.exchange 61 29 4),[(.neg 61),(.neg 29),(.pos 55),(.pos 58),(.pos 65)]),
   ((.exchange 61 34 0),[(.neg 61),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 61 49 4),[(.neg 61),(.neg 49),(.pos 55),(.pos 58),(.pos 65)]),
   ((.exchange 61 53 6),[(.neg 61),(.neg 53),(.pos 40),(.pos 51)]),
   ((.exchange 61 54 6),[(.neg 61),(.neg 54),(.pos 42),(.pos 51)]),
   ((.exchange 61 68 4),[(.neg 68),(.neg 61),(.pos 58),(.pos 65)]),
   ((.exchange 62 18 4),[(.neg 62),(.neg 18),(.pos 57),(.pos 59)]),
   ((.exchange 62 24 1),[(.neg 62),(.neg 24),(.pos 63),(.pos 64)]),
   ((.exchange 62 26 4),[(.neg 62),(.neg 26),(.pos 55),(.pos 57),(.pos 66)]),
   ((.exchange 62 28 4),[(.neg 62),(.neg 28),(.pos 55),(.pos 59),(.pos 66)]),
   ((.exchange 62 33 1),[(.neg 62),(.neg 33),(.pos 63),(.pos 69)]),
   ((.exchange 62 49 4),[(.neg 62),(.neg 49),(.pos 59),(.pos 66)]),
   ((.exchange 62 53 6),[(.neg 62),(.neg 53),(.pos 41),(.pos 52)]),
   ((.exchange 62 54 6),[(.neg 62),(.neg 54),(.pos 43),(.pos 52)]),
   ((.exchange 62 67 4),[(.neg 67),(.neg 62),(.pos 57),(.pos 66)]),
   ((.exchange 62 68 1),[(.neg 68),(.neg 62),(.pos 64),(.pos 69)]),
   ((.exchange 62 68 4),[(.neg 68),(.neg 62),(.pos 59),(.pos 66)]),
   ((.exchange 63 7 6),[(.neg 63),(.neg 7),(.pos 40),(.pos 44),(.pos 53)]),
   ((.exchange 63 18 4),[(.neg 63),(.neg 18),(.pos 57),(.pos 60)]),
   ((.exchange 63 22 2),[(.neg 63),(.neg 22),(.pos 61),(.pos 64)]),
   ((.exchange 63 23 2),[(.neg 63),(.neg 23),(.pos 62),(.pos 64)])]

theorem certificates_1_valid : ∀ oc ∈ certificates_1,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_2 : List (Origin 70 112 × List Sat.Literal) :=
  [((.exchange 63 28 4),[(.neg 63),(.neg 28),(.pos 56),(.pos 60),(.pos 67)]),
   ((.exchange 63 32 2),[(.neg 63),(.neg 32),(.pos 62),(.pos 69)]),
   ((.exchange 63 34 2),[(.neg 63),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 63 37 4),[(.neg 63),(.neg 37),(.pos 56),(.pos 60)]),
   ((.exchange 63 65 4),[(.neg 65),(.neg 63),(.pos 56),(.pos 67)]),
   ((.exchange 64 7 4),[(.neg 64),(.neg 7),(.pos 58),(.pos 60),(.pos 68)]),
   ((.exchange 64 7 6),[(.neg 64),(.neg 7),(.pos 42),(.pos 44),(.pos 54)]),
   ((.exchange 64 8 4),[(.neg 64),(.neg 8),(.pos 59),(.pos 60),(.pos 68)]),
   ((.exchange 64 11 3),[(.neg 64),(.neg 11),(.pos 62),(.pos 63),(.pos 69)]),
   ((.exchange 64 18 4),[(.neg 64),(.neg 18),(.pos 59),(.pos 60)]),
   ((.exchange 64 20 3),[(.neg 64),(.neg 20),(.pos 61),(.pos 63)]),
   ((.exchange 64 21 3),[(.neg 64),(.neg 21),(.pos 62),(.pos 63)]),
   ((.exchange 64 28 4),[(.neg 64),(.neg 28),(.pos 58),(.pos 68)]),
   ((.exchange 64 29 4),[(.neg 64),(.neg 29),(.pos 59),(.pos 68)]),
   ((.exchange 64 33 3),[(.neg 64),(.neg 33),(.pos 63),(.pos 69)]),
   ((.exchange 64 53 6),[(.neg 64),(.neg 53),(.pos 44),(.pos 54)]),
   ((.exchange 64 56 4),[(.neg 64),(.neg 56),(.pos 58),(.pos 60)]),
   ((.exchange 65 7 6),[(.neg 65),(.neg 7),(.pos 46),(.pos 48)]),
   ((.exchange 65 10 6),[(.neg 65),(.neg 10),(.pos 46),(.pos 51)]),
   ((.exchange 65 12 6),[(.neg 65),(.neg 12),(.pos 48),(.pos 51)]),
   ((.exchange 65 13 6),[(.neg 65),(.neg 13),(.pos 45),(.pos 48),(.pos 51)]),
   ((.exchange 65 17 5),[(.neg 65),(.neg 17),(.pos 56),(.pos 58)]),
   ((.exchange 65 18 5),[(.neg 65),(.neg 18),(.pos 55),(.pos 56),(.pos 58)]),
   ((.exchange 65 20 5),[(.neg 65),(.neg 20),(.pos 56),(.pos 61)]),
   ((.exchange 65 22 5),[(.neg 65),(.neg 22),(.pos 58),(.pos 61)]),
   ((.exchange 65 23 5),[(.neg 65),(.neg 23),(.pos 55),(.pos 58),(.pos 61)]),
   ((.exchange 65 33 0),[(.neg 65),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 65 34 0),[(.neg 65),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 65 37 5),[(.neg 65),(.neg 37),(.pos 56),(.pos 58)]),
   ((.exchange 65 38 5),[(.neg 65),(.neg 38),(.pos 55),(.pos 56),(.pos 58)]),
   ((.exchange 65 40 5),[(.neg 65),(.neg 40),(.pos 56),(.pos 61)]),
   ((.exchange 65 40 6),[(.neg 65),(.neg 40),(.pos 46),(.pos 51)]),
   ((.exchange 65 41 5),[(.neg 65),(.neg 41),(.pos 55),(.pos 56),(.pos 61)]),
   ((.exchange 65 41 6),[(.neg 65),(.neg 41),(.pos 45),(.pos 46),(.pos 51)]),
   ((.exchange 65 42 6),[(.neg 65),(.neg 42),(.pos 48),(.pos 51)]),
   ((.exchange 65 50 6),[(.neg 65),(.neg 50),(.pos 46),(.pos 48)]),
   ((.exchange 65 53 6),[(.neg 65),(.neg 53),(.pos 46),(.pos 51)]),
   ((.exchange 65 54 6),[(.neg 65),(.neg 54),(.pos 48),(.pos 51)]),
   ((.exchange 65 63 5),[(.neg 65),(.neg 63),(.pos 56),(.pos 61)]),
   ((.exchange 66 7 6),[(.neg 66),(.neg 7),(.pos 45),(.pos 47),(.pos 49)]),
   ((.exchange 66 10 6),[(.neg 66),(.neg 10),(.pos 45),(.pos 47),(.pos 52)]),
   ((.exchange 66 12 6),[(.neg 66),(.neg 12),(.pos 45),(.pos 49),(.pos 52)]),
   ((.exchange 66 17 5),[(.neg 66),(.neg 17),(.pos 55),(.pos 57),(.pos 59)]),
   ((.exchange 66 18 5),[(.neg 66),(.neg 18),(.pos 57),(.pos 59)]),
   ((.exchange 66 20 5),[(.neg 66),(.neg 20),(.pos 55),(.pos 57),(.pos 62)]),
   ((.exchange 66 22 5),[(.neg 66),(.neg 22),(.pos 55),(.pos 59),(.pos 62)]),
   ((.exchange 66 34 1),[(.neg 66),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 66 37 5),[(.neg 66),(.neg 37),(.pos 55),(.pos 57),(.pos 59)]),
   ((.exchange 66 38 5),[(.neg 66),(.neg 38),(.pos 57),(.pos 59)]),
   ((.exchange 66 40 5),[(.neg 66),(.neg 40),(.pos 55),(.pos 57),(.pos 62)]),
   ((.exchange 66 40 6),[(.neg 66),(.neg 40),(.pos 45),(.pos 47),(.pos 52)]),
   ((.exchange 66 41 6),[(.neg 66),(.neg 41),(.pos 47),(.pos 52)]),
   ((.exchange 66 42 5),[(.neg 66),(.neg 42),(.pos 55),(.pos 59),(.pos 62)]),
   ((.exchange 66 50 6),[(.neg 66),(.neg 50),(.pos 47),(.pos 49)]),
   ((.exchange 66 53 6),[(.neg 66),(.neg 53),(.pos 47),(.pos 52)]),
   ((.exchange 66 54 6),[(.neg 66),(.neg 54),(.pos 49),(.pos 52)]),
   ((.exchange 66 60 5),[(.neg 66),(.neg 60),(.pos 57),(.pos 59)]),
   ((.exchange 66 63 5),[(.neg 66),(.neg 63),(.pos 57),(.pos 62)]),
   ((.exchange 66 64 5),[(.neg 66),(.neg 64),(.pos 59),(.pos 62)]),
   ((.exchange 67 21 5),[(.neg 67),(.neg 21),(.pos 57),(.pos 63)]),
   ((.exchange 67 31 2),[(.neg 67),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 67 40 6),[(.neg 67),(.neg 40),(.pos 46),(.pos 53)]),
   ((.exchange 67 41 6),[(.neg 67),(.neg 41),(.pos 47),(.pos 53)]),
   ((.exchange 68 10 3),[(.neg 68),(.neg 10),(.pos 65),(.pos 67),(.pos 69)]),
   ((.exchange 68 23 5),[(.neg 68),(.neg 23),(.pos 59),(.pos 64)]),
   ((.exchange 68 31 3),[(.neg 68),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 68 32 3),[(.neg 68),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 68 43 6),[(.neg 68),(.neg 43),(.pos 49),(.pos 54)]),
   ((.exchange 68 51 6),[(.neg 68),(.neg 51),(.pos 48),(.pos 54)]),
   ((.exchange 68 61 5),[(.neg 68),(.neg 61),(.pos 58),(.pos 64)]),
   ((.exchange 68 62 3),[(.neg 68),(.neg 62),(.pos 66),(.pos 69)]),
   ((.exchange 69 12 6),[(.neg 69),(.neg 12),(.pos 51),(.pos 54)]),
   ((.exchange 69 13 6),[(.neg 69),(.neg 13),(.pos 52),(.pos 54)]),
   ((.exchange 69 22 5),[(.neg 69),(.neg 22),(.pos 61),(.pos 64)]),
   ((.exchange 69 23 5),[(.neg 69),(.neg 23),(.pos 62),(.pos 64)]),
   ((.exchange 69 24 5),[(.neg 69),(.neg 24),(.pos 63),(.pos 64)]),
   ((.exchange 69 26 4),[(.neg 69),(.neg 26),(.pos 65),(.pos 67)]),
   ((.exchange 69 27 4),[(.neg 69),(.neg 27),(.pos 66),(.pos 67)]),
   ((.exchange 69 28 4),[(.neg 69),(.neg 28),(.pos 65),(.pos 68)]),
   ((.exchange 69 29 4),[(.neg 69),(.neg 29),(.pos 66),(.pos 68)]),
   ((.exchange 69 40 5),[(.neg 69),(.neg 40),(.pos 61),(.pos 63)]),
   ((.exchange 69 40 6),[(.neg 69),(.neg 40),(.pos 51),(.pos 53)]),
   ((.exchange 69 41 5),[(.neg 69),(.neg 41),(.pos 62),(.pos 63)]),
   ((.exchange 69 41 6),[(.neg 69),(.neg 41),(.pos 52),(.pos 53)]),
   ((.exchange 69 44 5),[(.neg 69),(.neg 44),(.pos 63),(.pos 64)]),
   ((.exchange 69 44 6),[(.neg 69),(.neg 44),(.pos 53),(.pos 54)]),
   ((.exchange 69 47 4),[(.neg 69),(.neg 47),(.pos 66),(.pos 67)]),
   ((.exchange 69 59 4),[(.neg 69),(.neg 59),(.pos 66),(.pos 68)]),
   (.newPoint,[(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 0),[(.neg 69),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 54),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 50),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 67),(.pos 68)]),
   ((.excluded 1),[(.neg 69),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 50),(.pos 54),(.pos 55),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 67),(.pos 68)]),
   ((.excluded 2),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 50),(.pos 55),(.pos 60),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 3),[(.neg 69),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 50),(.pos 51),(.pos 52),(.pos 55),(.pos 60),(.pos 61),(.pos 62),(.pos 67),(.pos 68)]),
   ((.excluded 4),[(.neg 69),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 50),(.pos 55),(.pos 60),(.pos 67),(.pos 68)]),
   ((.excluded 5),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 60),(.neg 54),(.neg 53),(.neg 50),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 51),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 61),(.pos 62),(.pos 65),(.pos 66)]),
   ((.excluded 6),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 7),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 8),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 64)]),
   ((.excluded 9),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57),(.pos 69)]),
   ((.excluded 10),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 11),[(.neg 69),(.neg 68),(.neg 67),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 54),(.pos 55),(.pos 64),(.pos 65),(.pos 66)]),
   ((.excluded 12),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 54),(.pos 55),(.pos 64)]),
   ((.excluded 13),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 53),(.pos 55),(.pos 58),(.pos 59),(.pos 63)]),
   ((.excluded 14),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 58),(.pos 59),(.pos 69)]),
   ((.excluded 15),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 58),(.pos 59)]),
   ((.excluded 16),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 53),(.pos 55),(.pos 63),(.pos 65),(.pos 66)]),
   ((.excluded 17),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 53),(.pos 55),(.pos 63)]),
   ((.excluded 18),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 55),(.pos 65),(.pos 66)]),
   ((.excluded 19),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 55),(.pos 69)]),
   ((.excluded 20),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 55)]),
   ((.excluded 21),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 22),[(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 50),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 23),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 50),(.pos 55),(.pos 60),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 24),[(.neg 69),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 50),(.pos 53),(.pos 55),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 67),(.pos 68)]),
   ((.excluded 25),[(.neg 69),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 50),(.pos 53),(.pos 55),(.pos 60),(.pos 61),(.pos 62),(.pos 67),(.pos 68)]),
   ((.excluded 26),[(.neg 69),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 50),(.pos 53),(.pos 55),(.pos 60),(.pos 67),(.pos 68)]),
   ((.excluded 27),[(.neg 69),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 50),(.pos 51),(.pos 52),(.pos 55),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 67),(.pos 68)]),
   ((.excluded 28),[(.neg 69),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 50),(.pos 55),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 67),(.pos 68)]),
   ((.excluded 29),[(.neg 69),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 53),(.neg 52),(.neg 51),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 50),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 67),(.pos 68)]),
   ((.excluded 30),[(.neg 69),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 50),(.pos 54),(.pos 55),(.pos 60),(.pos 61),(.pos 62),(.pos 67),(.pos 68)]),
   ((.excluded 31),[(.neg 69),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 50),(.pos 54),(.pos 55),(.pos 60),(.pos 67),(.pos 68)]),
   ((.excluded 32),[(.neg 69),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 50),(.pos 51),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 67),(.pos 68)]),
   ((.excluded 33),[(.neg 69),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 50),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 67),(.pos 68)]),
   ((.excluded 34),[(.neg 69),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 50),(.pos 51),(.pos 52),(.pos 55),(.pos 60),(.pos 67),(.pos 68)]),
   ((.excluded 35),[(.neg 69),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 50),(.pos 55),(.pos 60),(.pos 61),(.pos 62),(.pos 67),(.pos 68)]),
   ((.excluded 36),[(.neg 69),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 50),(.pos 55),(.pos 60),(.pos 67),(.pos 68)]),
   ((.excluded 37),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 51),(.pos 52),(.pos 55),(.pos 63),(.pos 65),(.pos 66)]),
   ((.excluded 38),[(.neg 69),(.neg 68),(.neg 67),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 51),(.pos 52),(.pos 55),(.pos 64),(.pos 65),(.pos 66)])]

theorem certificates_2_valid : ∀ oc ∈ certificates_2,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_3 : List (Origin 70 112 × List Sat.Literal) :=
  [((.excluded 39),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 51),(.pos 52),(.pos 55),(.pos 65),(.pos 66)]),
   ((.excluded 40),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 69)]),
   ((.excluded 41),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 58),(.pos 59),(.pos 69)]),
   ((.excluded 42),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 69)]),
   ((.excluded 43),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 64)]),
   ((.excluded 44),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 45),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 64)]),
   ((.excluded 46),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 58),(.pos 59),(.pos 63)]),
   ((.excluded 47),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 58),(.pos 59)]),
   ((.excluded 48),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 63)]),
   ((.excluded 49),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 55)]),
   ((.excluded 50),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 60),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 61),(.pos 62),(.pos 65),(.pos 66)]),
   ((.excluded 51),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 60),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 61),(.pos 62),(.pos 65),(.pos 66)]),
   ((.excluded 52),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 60),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 61),(.pos 62),(.pos 65),(.pos 66)]),
   ((.excluded 53),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 54),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 55),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 56),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 54),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 57),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 58),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 54),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 59),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 53),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 60),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 61),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 53),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 62),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 63),[(.neg 69),(.neg 68),(.neg 67),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 53),(.pos 55),(.pos 64),(.pos 65),(.pos 66)]),
   ((.excluded 64),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 53),(.pos 55),(.pos 65),(.pos 66)]),
   ((.excluded 65),[(.neg 69),(.neg 68),(.neg 67),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 64),(.pos 65),(.pos 66)]),
   ((.excluded 66),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 54),(.pos 55),(.pos 63),(.pos 65),(.pos 66)]),
   ((.excluded 67),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 54),(.pos 55),(.pos 65),(.pos 66)]),
   ((.excluded 68),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 63),(.pos 65),(.pos 66)]),
   ((.excluded 69),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 65),(.pos 66)]),
   ((.excluded 70),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 64)]),
   ((.excluded 71),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 58),(.pos 59),(.pos 69)]),
   ((.excluded 72),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 69)]),
   ((.excluded 73),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 54),(.pos 55),(.pos 58),(.pos 59),(.pos 63)]),
   ((.excluded 74),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 54),(.pos 55),(.pos 58),(.pos 59)]),
   ((.excluded 75),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 58),(.pos 59),(.pos 63)]),
   ((.excluded 76),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 58),(.pos 59)]),
   ((.excluded 77),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 54),(.pos 55),(.pos 63)]),
   ((.excluded 78),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 54),(.pos 55)]),
   ((.excluded 79),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 63)]),
   ((.excluded 80),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 55)]),
   ((.excluded 81),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 53),(.pos 55),(.pos 58),(.pos 59)]),
   ((.excluded 82),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 58),(.pos 59),(.pos 69)]),
   ((.excluded 83),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 54),(.pos 55),(.pos 58),(.pos 59),(.pos 63)]),
   ((.excluded 84),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 54),(.pos 55),(.pos 58),(.pos 59)]),
   ((.excluded 85),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 58),(.pos 59),(.pos 63)]),
   ((.excluded 86),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 58),(.pos 59)]),
   ((.excluded 87),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 54),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 88),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 54),(.pos 55),(.pos 63)]),
   ((.excluded 89),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 54),(.pos 55)]),
   ((.excluded 90),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 63)]),
   ((.excluded 91),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 63)]),
   ((.excluded 92),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 56),(.pos 57),(.pos 69)]),
   ((.excluded 93),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 69)]),
   ((.excluded 94),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 69)]),
   ((.excluded 95),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 69)]),
   ((.excluded 96),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 64)]),
   ((.excluded 97),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 53),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 98),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 56),(.pos 57),(.pos 64)]),
   ((.excluded 99),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 100),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 53),(.pos 55),(.pos 64)]),
   ((.excluded 101),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 53),(.pos 55)]),
   ((.excluded 102),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 64)]),
   ((.excluded 103),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 55)]),
   ((.excluded 104),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 64)]),
   ((.excluded 105),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 53),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 106),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 64)]),
   ((.excluded 107),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 108),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 53),(.pos 55),(.pos 64)]),
   ((.excluded 109),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 53),(.pos 55)]),
   ((.excluded 110),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 64)]),
   ((.excluded 111),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55)])]

theorem certificates_3_valid : ∀ oc ∈ certificates_3,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



theorem witness_0 : ∀ j : Fin 112,
    let w : Fin 112 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 112,
      let w : Fin 112 := ⟨0 + j.val,by omega⟩
      target w < MatroidCatalogue.count 8 4 ∧
        Papers.RationalityTen.MatroidChecked.FastSemanticChecks.RawWitness 8 (N7R4.familyMasks.get 43)
        (fun i : Fin 70 => N8R4.gridMasks.get i.val) newIndex (models w)
        (N8R4.familyMasks.get (target w)) (permutation w) := by
    refine (Fin.forall_fin_add (m := 56) (n := 56) _).2 ⟨?_, ?_⟩
    · refine (Fin.forall_fin_add (m := 28) (n := 28) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 14) (n := 14) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 7) (n := 7) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 7) (n := 7) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
      · refine (Fin.forall_fin_add (m := 14) (n := 14) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 7) (n := 7) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 7) (n := 7) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
    · refine (Fin.forall_fin_add (m := 28) (n := 28) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 14) (n := 14) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 7) (n := 7) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 7) (n := 7) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
      · refine (Fin.forall_fin_add (m := 14) (n := 14) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 7) (n := 7) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 7) (n := 7) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
          · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
  intro j
  have hj := hfast j
  exact ⟨hj.1,Papers.RationalityTen.MatroidChecked.FastSemanticChecks.rawWitness_sound 8 _ _ _ _ _ _ hj.2⟩


end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C43

/- Source: MatroidCatalogue/Cases/N8R4C43Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C43

noncomputable def certificates : List (Origin 70 112 × List Sat.Literal) :=
  certificates_0 ++ certificates_1 ++ certificates_2 ++ certificates_3

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  intro oc hoc
  simp only [certificates,List.mem_append,or_assoc] at hoc
  rcases hoc with h0 | h1 | h2 | h3
  · exact certificates_0_valid oc h0
  · exact certificates_1_valid oc h1
  · exact certificates_2_valid oc h2
  · exact certificates_3_valid oc h3

theorem models_valid : ∀ w : Fin 112,
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 112) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 8) 4)
    (hold : M.bases.filter ((7 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 8 4, IsomorphicWithin 8 M.bases B := by
  apply extension_covered_of_certificate (n:=7) (r:=4) (by decide)
    catalogue old U newIndex models certificates
    N8R4.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C43.formula []
    exact Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C43.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 8 4 (target w),family_mem 8 4 (target w) hw.1,?_⟩
    exact validWitness_sound 8 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C43


end
end
end BundlePart7
