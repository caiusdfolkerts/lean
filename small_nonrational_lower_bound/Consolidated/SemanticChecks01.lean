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
/- Source: MatroidChecked/SemanticChunks/Cases02Part00.lean -/




@[expose] public section
noncomputable section

/- Source: MatroidCatalogue/Cases/N7R4C16Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R4C16

abbrev U := N7R4.grid
noncomputable def old : Finset (Finset (Fin 8)) := N6R4.family 16
noncomputable def newIndexTree : Table ℕ := (.node 10 (.node 5 (.node 2 (.node 1 (.leaf 15) (.leaf 16)) (.node 3 (.leaf 17) (.node 4 (.leaf 18) (.leaf 19)))) (.node 7 (.node 6 (.leaf 20) (.leaf 21)) (.node 8 (.leaf 22) (.node 9 (.leaf 23) (.leaf 24))))) (.node 15 (.node 12 (.node 11 (.leaf 25) (.leaf 26)) (.node 13 (.leaf 27) (.node 14 (.leaf 28) (.leaf 29)))) (.node 17 (.node 16 (.leaf 30) (.leaf 31)) (.node 18 (.leaf 32) (.node 19 (.leaf 33) (.leaf 34))))))
noncomputable def newIndex (i : Fin 20) : Fin 35 := Fin.ofNat 35 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 98 (.node 49 (.node 24 (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (971584,44,15161552)) (.node 2 (.leaf (895648,44,15161538)) (.leaf (1014240,50,14899409)))) (.node 4 (.leaf (785376,56,14899409)) (.node 5 (.leaf (523232,56,14898961)) (.leaf (1047520,57,15423688))))) (.node 9 (.node 7 (.leaf (746896,44,15161370)) (.node 8 (.leaf (466032,44,15159578)) (.leaf (949744,56,14898275)))) (.node 10 (.leaf (884208,56,14898268)) (.node 11 (.leaf (1015280,57,15421987)) (.leaf (1029840,50,14899353)))))) (.node 18 (.node 15 (.node 13 (.leaf (915408,56,14899353)) (.node 14 (.leaf (522192,56,14898849)) (.leaf (1046480,57,15423576)))) (.node 16 (.leaf (966384,56,14898443)) (.node 17 (.leaf (769776,56,14898380)) (.leaf (1031920,57,15422211))))) (.node 21 (.node 19 (.leaf (1036080,50,14898457)) (.node 20 (.leaf (978864,56,14899339)) (.leaf (520112,56,14898828)))) (.node 22 (.leaf (1044400,57,15423555)) (.node 23 (.leaf (909168,56,14898457)) (.leaf (778096,56,14898401))))))) (.node 36 (.node 30 (.node 27 (.node 25 (.leaf (1040240,57,15422232)) (.node 26 (.leaf (65520,59,14899409)) (.leaf (983024,61,15161552)))) (.node 28 (.leaf (917488,61,15161538)) (.node 29 (.leaf (786416,61,15161370)) (.leaf (524272,61,15159578))))) (.node 33 (.node 31 (.leaf (1048560,62,15947400)) (.node 32 (.leaf (64527,63,15141658)) (.leaf (1023,63,14969626)))) (.node 34 (.leaf (65535,69,15240547)) (.node 35 (.leaf (978767,67,15117592)) (.leaf (966479,67,15116696)))))) (.node 42 (.node 39 (.node 37 (.leaf (950095,67,15116528)) (.node 38 (.leaf (982863,68,15407896)) (.leaf (971711,67,15031576)))) (.node 40 (.leaf (971519,67,15030680)) (.node 41 (.leaf (971263,67,15030512)) (.leaf (971775,68,15264536))))) (.node 45 (.node 43 (.leaf (966591,77,15120518)) (.node 44 (.leaf (950207,77,15120406)) (.leaf (982975,78,15641668)))) (.node 47 (.node 46 (.leaf (966143,77,15061270)) (.leaf (966655,78,15553412))) (.node 48 (.leaf (978431,77,15063062)) (.leaf (982527,78,15639092)))))))) (.node 73 (.node 61 (.node 55 (.node 52 (.node 50 (.leaf (978687,77,15063174)) (.node 51 (.leaf (978943,78,15555652)) (.leaf (950015,77,15118614)))) (.node 53 (.leaf (982783,78,15639428)) (.node 54 (.leaf (950271,78,15553076)) (.leaf (983039,82,16137352))))) (.node 58 (.node 56 (.leaf (915119,67,15117571)) (.node 57 (.leaf (908975,67,15116675)) (.leaf (884399,67,15116486)))) (.node 59 (.leaf (917167,68,15407875)) (.node 60 (.leaf (895967,67,15031555)) (.leaf (895871,67,15030659)))))) (.node 67 (.node 64 (.node 62 (.leaf (895487,67,15030470)) (.node 63 (.leaf (895999,68,15264515)) (.leaf (909279,77,15120560)))) (.node 65 (.leaf (884703,77,15120434)) (.node 66 (.leaf (917471,78,15641696)) (.leaf (908799,77,15061298))))) (.node 70 (.node 68 (.leaf (909311,78,15553440)) (.node 69 (.leaf (914943,77,15063090)) (.leaf (916991,78,15639078)))) (.node 71 (.leaf (915327,77,15063216)) (.node 72 (.leaf (915455,78,15555680)) (.leaf (884607,77,15118642))))))) (.node 85 (.node 79 (.node 76 (.node 74 (.leaf (917375,78,15639456)) (.node 75 (.leaf (884735,78,15553062)) (.leaf (917503,82,16137345)))) (.node 77 (.leaf (784799,67,15117347)) (.node 78 (.leaf (777631,67,15116339)) (.leaf (769439,67,15116318))))) (.node 82 (.node 80 (.leaf (785823,68,15407651)) (.node 81 (.leaf (747503,67,15031331)) (.leaf (747391,67,15030323)))) (.node 83 (.leaf (747263,67,15030302)) (.node 84 (.leaf (747519,68,15264291)) (.leaf (778223,77,15120784)))))) (.node 91 (.node 88 (.node 86 (.leaf (770031,77,15120770)) (.node 87 (.leaf (786415,78,15641864)) (.leaf (777983,77,15061410)))) (.node 89 (.leaf (778239,78,15553328)) (.node 90 (.leaf (785151,77,15063426)) (.leaf (786175,78,15639302))))) (.node 94 (.node 92 (.leaf (785279,77,15063440)) (.node 93 (.leaf (785407,78,15555848)) (.leaf (769919,77,15118754)))) (.node 96 (.node 95 (.leaf (786303,78,15639344)) (.leaf (770047,78,15553286))) (.node 97 (.leaf (786431,82,16137233)) (.leaf (522367,67,15114659))))))))) (.node 147 (.node 122 (.node 110 (.node 104 (.node 101 (.node 99 (.leaf (521343,67,15114547)) (.node 100 (.leaf (519295,67,15114526)) (.leaf (523391,68,15405411)))) (.node 102 (.leaf (1044351,78,15917776)) (.node 103 (.leaf (1014591,74,14870289)) (.leaf (1047359,75,15423240))))) (.node 107 (.node 105 (.leaf (1014655,75,15393560)) (.node 106 (.leaf (1047423,80,15619464)) (.leaf (1015615,75,15421980)))) (.node 108 (.leaf (1015679,80,15646897)) (.node 109 (.leaf (1029951,74,14870177)) (.leaf (1046335,75,15423072)))))) (.node 116 (.node 113 (.node 111 (.leaf (1031999,75,15422148)) (.node 112 (.leaf (1048383,76,16204496)) (.leaf (1030015,75,15393504)))) (.node 114 (.leaf (1046399,80,15619184)) (.node 115 (.leaf (1032063,80,15647121)) (.leaf (1048447,81,16204496))))) (.node 119 (.node 117 (.leaf (466927,67,15028643)) (.node 118 (.leaf (466911,67,15028531)) (.leaf (466879,67,15028510)))) (.node 120 (.leaf (466943,68,15262051)) (.node 121 (.leaf (1032159,78,15918672)) (.leaf (1030079,75,15394372))))))) (.node 134 (.node 128 (.node 125 (.node 123 (.leaf (1032127,80,15647814)) (.node 124 (.leaf (1029615,74,14899409)) (.leaf (1031663,75,15422211)))) (.node 126 (.leaf (1030127,75,15395016)) (.node 127 (.leaf (1032175,80,15648129)) (.leaf (1029631,75,15393315))))) (.node 131 (.node 129 (.leaf (1031679,80,15618190)) (.node 130 (.leaf (1030143,76,16148048)) (.leaf (1032191,81,16147138)))) (.node 132 (.leaf (1040319,78,15946448)) (.node 133 (.leaf (522175,77,15064098)) (.leaf (1046463,80,15621137)))))) (.node 140 (.node 137 (.node 135 (.leaf (1014719,75,15394883)) (.node 136 (.leaf (1015743,80,15647758)) (.leaf (523199,77,15064322)))) (.node 138 (.leaf (1047487,80,15621249)) (.node 139 (.leaf (524223,78,15640646)) (.leaf (1048511,81,16205378))))) (.node 143 (.node 141 (.leaf (1046271,78,15947344)) (.node 142 (.leaf (1045999,75,15423576)) (.leaf (1046015,80,15619121)))) (.node 145 (.node 144 (.leaf (522223,77,15121680)) (.leaf (1046511,80,15649928))) (.node 146 (.leaf (522239,78,15554672)) (.leaf (1046527,81,16148048)))))))) (.node 172 (.node 159 (.node 153 (.node 150 (.node 148 (.leaf (1047039,78,15947400)) (.node 149 (.leaf (1035759,74,14898961)) (.leaf (1043951,75,15423555)))) (.node 151 (.leaf (1039855,75,15422232)) (.node 152 (.leaf (1048047,76,16205448)) (.leaf (1035775,75,15393308))))) (.node 156 (.node 154 (.leaf (1043967,80,15619086)) (.node 155 (.leaf (1039871,80,15618225)) (.leaf (1048063,81,16204314)))) (.node 157 (.leaf (1015791,78,15918728)) (.node 158 (.leaf (1036271,75,15394568)) (.leaf (1040367,80,15648136)))))) (.node 165 (.node 162 (.node 160 (.leaf (520175,77,15121666)) (.node 161 (.leaf (1044463,80,15649921)) (.leaf (524271,78,15640968)))) (.node 163 (.leaf (1048559,81,16205448)) (.node 164 (.leaf (1035999,74,14898849)) (.leaf (1040095,75,15422176))))) (.node 168 (.node 166 (.leaf (1036255,75,15394400)) (.node 167 (.leaf (1040351,80,15647856)) (.leaf (1036031,75,15393476)))) (.node 170 (.node 169 (.leaf (1040127,80,15618449)) (.leaf (1036287,76,16147152))) (.node 171 (.leaf (1040383,81,16147152)) (.leaf (1044191,75,15423044))))))) (.node 184 (.node 178 (.node 175 (.node 173 (.leaf (1044223,80,15619142)) (.node 174 (.leaf (520159,77,15121442)) (.leaf (1044447,80,15649809)))) (.node 176 (.leaf (520191,78,15554630)) (.node 177 (.leaf (1044479,81,16148034)) (.leaf (523231,77,15064336))))) (.node 181 (.node 179 (.leaf (524255,78,15640688)) (.node 180 (.leaf (523263,78,15554952)) (.leaf (524287,82,16134545)))) (.node 182 (.leaf (1014495,74,14870737)) (.node 183 (.leaf (1047263,75,15423688)) (.leaf (1015519,75,15421987)))))) (.node 190 (.node 187 (.node 185 (.leaf (1048287,76,16205392)) (.node 186 (.leaf (1014751,75,15394904)) (.leaf (1047519,80,15621256)))) (.node 188 (.leaf (1015775,80,15647793)) (.node 189 (.leaf (1048543,81,16205392)) (.leaf (1014527,75,15393539))))) (.node 193 (.node 191 (.leaf (1047295,80,15619457)) (.node 192 (.leaf (1015551,80,15646862)) (.leaf (1048319,81,16204482)))) (.node 195 (.node 194 (.leaf (1014783,76,16148104)) (.leaf (1047551,81,16148104))) (.node 196 (.leaf (1015807,81,16146970)) (.leaf (1048575,83,16434824))))))))))

noncomputable def models (i : Fin 197) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 197) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 197) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 35, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (6 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 35, (6 : Fin 8) ∈ U i → ∃ j : Fin 20, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R4C16

/- Source: MatroidCatalogue/Cases/N7R4C16Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R4C16


noncomputable def certificates_0 : List (Origin 35 197 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.pos 1)]),
   ((.fixed 2),[(.pos 2)]),
   ((.fixed 3),[(.pos 3)]),
   ((.fixed 4),[(.pos 4)]),
   ((.fixed 5),[(.pos 5)]),
   ((.fixed 6),[(.pos 6)]),
   ((.fixed 7),[(.pos 7)]),
   ((.fixed 8),[(.pos 8)]),
   ((.fixed 9),[(.pos 9)]),
   ((.fixed 10),[(.pos 10)]),
   ((.fixed 11),[(.pos 11)]),
   ((.fixed 12),[(.pos 12)]),
   ((.fixed 13),[(.pos 13)]),
   ((.fixed 14),[(.pos 14)]),
   ((.exchange 1 16 4),[(.neg 16),(.neg 1),(.pos 0),(.pos 15)]),
   ((.exchange 1 17 4),[(.neg 17),(.neg 1),(.pos 0),(.pos 15)]),
   ((.exchange 1 18 4),[(.neg 18),(.neg 1),(.pos 0),(.pos 15)]),
   ((.exchange 2 15 4),[(.neg 15),(.neg 2),(.pos 0),(.pos 16)]),
   ((.exchange 2 17 4),[(.neg 17),(.neg 2),(.pos 0),(.pos 16)]),
   ((.exchange 2 18 4),[(.neg 18),(.neg 2),(.pos 0),(.pos 16)]),
   ((.exchange 3 15 4),[(.neg 15),(.neg 3),(.pos 0),(.pos 17)]),
   ((.exchange 3 16 4),[(.neg 16),(.neg 3),(.pos 0),(.pos 17)]),
   ((.exchange 3 18 4),[(.neg 18),(.neg 3),(.pos 0),(.pos 17)]),
   ((.exchange 4 15 4),[(.neg 15),(.neg 4),(.pos 0),(.pos 18)]),
   ((.exchange 4 16 4),[(.neg 16),(.neg 4),(.pos 0),(.pos 18)]),
   ((.exchange 4 17 4),[(.neg 17),(.neg 4),(.pos 0),(.pos 18)]),
   ((.exchange 15 9 2),[(.neg 15),(.neg 9),(.pos 19),(.pos 25)]),
   ((.exchange 15 10 1),[(.neg 15),(.neg 10),(.pos 20),(.pos 26)]),
   ((.exchange 15 11 0),[(.neg 15),(.neg 11),(.pos 21),(.pos 27)]),
   ((.exchange 15 33 0),[(.neg 33),(.neg 15),(.pos 21),(.pos 27)]),
   ((.exchange 16 9 3),[(.neg 16),(.neg 9),(.pos 19),(.pos 25)]),
   ((.exchange 16 12 1),[(.neg 16),(.neg 12),(.pos 22),(.pos 28)]),
   ((.exchange 16 13 0),[(.neg 16),(.neg 13),(.pos 23),(.pos 29)]),
   ((.exchange 16 31 1),[(.neg 31),(.neg 16),(.pos 22),(.pos 28)]),
   ((.exchange 16 34 1),[(.neg 34),(.neg 16),(.pos 22),(.pos 28)]),
   ((.exchange 17 10 3),[(.neg 17),(.neg 10),(.pos 20),(.pos 26)]),
   ((.exchange 17 12 2),[(.neg 17),(.neg 12),(.pos 22),(.pos 28)]),
   ((.exchange 17 14 0),[(.neg 17),(.neg 14),(.pos 24),(.pos 30)]),
   ((.exchange 17 33 0),[(.neg 33),(.neg 17),(.pos 24),(.pos 30)]),
   ((.exchange 18 11 3),[(.neg 18),(.neg 11),(.pos 21),(.pos 27)]),
   ((.exchange 18 13 2),[(.neg 18),(.neg 13),(.pos 23),(.pos 29)]),
   ((.exchange 18 14 1),[(.neg 18),(.neg 14),(.pos 24),(.pos 30)]),
   ((.exchange 18 32 2),[(.neg 32),(.neg 18),(.pos 23),(.pos 29)]),
   ((.exchange 18 33 3),[(.neg 33),(.neg 18),(.pos 21),(.pos 27)]),
   ((.exchange 18 34 1),[(.neg 34),(.neg 18),(.pos 24),(.pos 30)]),
   ((.exchange 18 34 2),[(.neg 34),(.neg 18),(.pos 23),(.pos 29)]),
   ((.exchange 19 3 1),[(.neg 19),(.neg 3),(.pos 20),(.pos 22)]),
   ((.exchange 19 4 0),[(.neg 19),(.neg 4),(.pos 21),(.pos 23)]),
   ((.exchange 19 5 4),[(.neg 19),(.neg 5),(.pos 15),(.pos 25)]),
   ((.exchange 19 6 4),[(.neg 19),(.neg 6),(.pos 16),(.pos 25)]),
   ((.exchange 19 10 1),[(.neg 19),(.neg 10),(.pos 20),(.pos 31)]),
   ((.exchange 19 11 0),[(.neg 19),(.neg 11),(.pos 21),(.pos 32)]),
   ((.exchange 19 12 1),[(.neg 19),(.neg 12),(.pos 22),(.pos 31)]),
   ((.exchange 19 13 0),[(.neg 19),(.neg 13),(.pos 23),(.pos 32)]),
   ((.exchange 19 17 1),[(.neg 19),(.neg 17),(.pos 20),(.pos 22)]),
   ((.exchange 19 29 0),[(.neg 29),(.neg 19),(.pos 23),(.pos 32)]),
   ((.exchange 19 33 0),[(.neg 33),(.neg 19),(.pos 21),(.pos 32)]),
   ((.exchange 19 34 0),[(.neg 34),(.neg 19),(.pos 23),(.pos 32)]),
   ((.exchange 20 2 2),[(.neg 20),(.neg 2),(.pos 19),(.pos 22)]),
   ((.exchange 20 4 0),[(.neg 20),(.neg 4),(.pos 21),(.pos 24)]),
   ((.exchange 20 9 2),[(.neg 20),(.neg 9),(.pos 19),(.pos 31)]),
   ((.exchange 20 11 0),[(.neg 20),(.neg 11),(.pos 21),(.pos 33)]),
   ((.exchange 20 12 2),[(.neg 20),(.neg 12),(.pos 22),(.pos 31)]),
   ((.exchange 20 14 0),[(.neg 20),(.neg 14),(.pos 24),(.pos 33)]),
   ((.exchange 20 23 0),[(.neg 23),(.neg 20),(.pos 21),(.pos 24)]),
   ((.exchange 20 25 4),[(.neg 25),(.neg 20),(.pos 15),(.pos 26)]),
   ((.exchange 20 28 4),[(.neg 28),(.neg 20),(.pos 17),(.pos 26)]),
   ((.exchange 20 30 0),[(.neg 30),(.neg 20),(.pos 24),(.pos 33)]),
   ((.exchange 20 32 0),[(.neg 32),(.neg 20),(.pos 21),(.pos 33)]),
   ((.exchange 20 34 0),[(.neg 34),(.neg 20),(.pos 24),(.pos 33)]),
   ((.exchange 21 2 2),[(.neg 21),(.neg 2),(.pos 19),(.pos 23)]),
   ((.exchange 21 3 1),[(.neg 21),(.neg 3),(.pos 20),(.pos 24)]),
   ((.exchange 21 8 4),[(.neg 21),(.neg 8),(.pos 18),(.pos 27)]),
   ((.exchange 21 9 2),[(.neg 21),(.neg 9),(.pos 19),(.pos 32)]),
   ((.exchange 21 10 1),[(.neg 21),(.neg 10),(.pos 20),(.pos 33)]),
   ((.exchange 21 12 2),[(.neg 21),(.neg 12),(.pos 19),(.pos 23),(.pos 32)]),
   ((.exchange 21 14 1),[(.neg 21),(.neg 14),(.pos 24),(.pos 33)]),
   ((.exchange 21 28 4),[(.neg 28),(.neg 21),(.pos 15),(.pos 18),(.pos 27)]),
   ((.exchange 21 29 4),[(.neg 29),(.neg 21),(.pos 18),(.pos 27)]),
   ((.exchange 21 30 1),[(.neg 30),(.neg 21),(.pos 24),(.pos 33)]),
   ((.exchange 22 1 3),[(.neg 22),(.neg 1),(.pos 19),(.pos 20)]),
   ((.exchange 22 4 0),[(.neg 22),(.neg 4),(.pos 23),(.pos 24)]),
   ((.exchange 22 6 4),[(.neg 22),(.neg 6),(.pos 16),(.pos 28)]),
   ((.exchange 22 7 4),[(.neg 22),(.neg 7),(.pos 17),(.pos 28)]),
   ((.exchange 22 13 0),[(.neg 22),(.neg 13),(.pos 23),(.pos 34)]),
   ((.exchange 22 14 0),[(.neg 22),(.neg 14),(.pos 24),(.pos 34)]),
   ((.exchange 22 30 0),[(.neg 30),(.neg 22),(.pos 24),(.pos 34)]),
   ((.exchange 22 33 0),[(.neg 33),(.neg 22),(.pos 24),(.pos 34)]),
   ((.exchange 23 1 3),[(.neg 23),(.neg 1),(.pos 19),(.pos 21)]),
   ((.exchange 23 3 1),[(.neg 23),(.neg 3),(.pos 22),(.pos 24)]),
   ((.exchange 23 6 4),[(.neg 23),(.neg 6),(.pos 16),(.pos 29)]),
   ((.exchange 23 8 4),[(.neg 23),(.neg 8),(.pos 18),(.pos 29)]),
   ((.exchange 23 11 3),[(.neg 23),(.neg 11),(.pos 21),(.pos 32)]),
   ((.exchange 23 12 1),[(.neg 23),(.neg 12),(.pos 22),(.pos 34)]),
   ((.exchange 23 14 1),[(.neg 23),(.neg 14),(.pos 24),(.pos 34)]),
   ((.exchange 23 20 3),[(.neg 23),(.neg 20),(.pos 19),(.pos 21)]),
   ((.exchange 23 26 4),[(.neg 26),(.neg 23),(.pos 16),(.pos 18),(.pos 29)]),
   ((.exchange 23 27 4),[(.neg 27),(.neg 23),(.pos 18),(.pos 29)]),
   ((.exchange 23 28 4),[(.neg 28),(.neg 23),(.pos 16),(.pos 29)]),
   ((.exchange 23 30 4),[(.neg 30),(.neg 23),(.pos 18),(.pos 29)]),
   ((.exchange 23 31 1),[(.neg 31),(.neg 23),(.pos 22),(.pos 34)]),
   ((.exchange 23 31 3),[(.neg 31),(.neg 23),(.pos 19),(.pos 32)]),
   ((.exchange 24 1 3),[(.neg 24),(.neg 1),(.pos 20),(.pos 21)]),
   ((.exchange 24 6 4),[(.neg 24),(.neg 6),(.pos 17),(.pos 18),(.pos 30)]),
   ((.exchange 24 9 2),[(.neg 24),(.neg 9),(.pos 22),(.pos 23),(.pos 34)]),
   ((.exchange 24 11 3),[(.neg 24),(.neg 11),(.pos 21),(.pos 33)]),
   ((.exchange 24 12 2),[(.neg 24),(.neg 12),(.pos 22),(.pos 34)]),
   ((.exchange 24 13 2),[(.neg 24),(.neg 13),(.pos 23),(.pos 34)]),
   ((.exchange 24 19 2),[(.neg 24),(.neg 19),(.pos 22),(.pos 23)]),
   ((.exchange 24 26 3),[(.neg 26),(.neg 24),(.pos 20),(.pos 33)]),
   ((.exchange 24 27 4),[(.neg 27),(.neg 24),(.pos 18),(.pos 30)]),
   ((.exchange 24 28 4),[(.neg 28),(.neg 24),(.pos 17),(.pos 30)]),
   ((.exchange 24 29 4),[(.neg 29),(.neg 24),(.pos 18),(.pos 30)]),
   ((.exchange 24 31 2),[(.neg 31),(.neg 24),(.pos 22),(.pos 34)]),
   ((.exchange 24 31 3),[(.neg 31),(.neg 24),(.pos 20),(.pos 33)]),
   ((.exchange 24 32 2),[(.neg 32),(.neg 24),(.pos 23),(.pos 34)]),
   ((.exchange 25 1 5),[(.neg 25),(.neg 1),(.pos 15),(.pos 19)]),
   ((.exchange 25 2 5),[(.neg 25),(.neg 2),(.pos 16),(.pos 19)]),
   ((.exchange 25 7 1),[(.neg 25),(.neg 7),(.pos 26),(.pos 28)]),
   ((.exchange 25 8 0),[(.neg 25),(.neg 8),(.pos 27),(.pos 29)]),
   ((.exchange 25 10 1),[(.neg 25),(.neg 10),(.pos 26),(.pos 31)]),
   ((.exchange 25 11 0),[(.neg 25),(.neg 11),(.pos 27),(.pos 32)]),
   ((.exchange 25 12 1),[(.neg 25),(.neg 12),(.pos 28),(.pos 31)]),
   ((.exchange 25 13 0),[(.neg 25),(.neg 13),(.pos 29),(.pos 32)]),
   ((.exchange 25 17 1),[(.neg 25),(.neg 17),(.pos 26),(.pos 28)]),
   ((.exchange 25 20 1),[(.neg 25),(.neg 20),(.pos 26),(.pos 31)]),
   ((.exchange 25 20 5),[(.neg 25),(.neg 20),(.pos 15),(.pos 19)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_1 : List (Origin 35 197 × List Sat.Literal) :=
  [((.exchange 25 22 1),[(.neg 25),(.neg 22),(.pos 28),(.pos 31)]),
   ((.exchange 25 22 5),[(.neg 25),(.neg 22),(.pos 16),(.pos 19)]),
   ((.exchange 25 30 0),[(.neg 30),(.neg 25),(.pos 27),(.pos 29)]),
   ((.exchange 26 4 5),[(.neg 26),(.neg 4),(.pos 15),(.pos 17),(.pos 20)]),
   ((.exchange 26 6 2),[(.neg 26),(.neg 6),(.pos 25),(.pos 28)]),
   ((.exchange 26 8 0),[(.neg 26),(.neg 8),(.pos 27),(.pos 30)]),
   ((.exchange 26 9 2),[(.neg 26),(.neg 9),(.pos 25),(.pos 31)]),
   ((.exchange 26 11 0),[(.neg 26),(.neg 11),(.pos 27),(.pos 33)]),
   ((.exchange 26 14 0),[(.neg 26),(.neg 14),(.pos 30),(.pos 33)]),
   ((.exchange 26 18 0),[(.neg 26),(.neg 18),(.pos 27),(.pos 30)]),
   ((.exchange 26 19 2),[(.neg 26),(.neg 19),(.pos 25),(.pos 31)]),
   ((.exchange 26 21 0),[(.neg 26),(.neg 21),(.pos 27),(.pos 33)]),
   ((.exchange 26 34 0),[(.neg 34),(.neg 26),(.pos 30),(.pos 33)]),
   ((.exchange 27 4 5),[(.neg 27),(.neg 4),(.pos 18),(.pos 21)]),
   ((.exchange 27 7 1),[(.neg 27),(.neg 7),(.pos 26),(.pos 30)]),
   ((.exchange 27 9 2),[(.neg 27),(.neg 9),(.pos 25),(.pos 32)]),
   ((.exchange 27 10 1),[(.neg 27),(.neg 10),(.pos 26),(.pos 33)]),
   ((.exchange 27 13 2),[(.neg 27),(.neg 13),(.pos 29),(.pos 32)]),
   ((.exchange 27 14 1),[(.neg 27),(.neg 14),(.pos 30),(.pos 33)]),
   ((.exchange 27 16 2),[(.neg 27),(.neg 16),(.pos 25),(.pos 29)]),
   ((.exchange 27 19 2),[(.neg 27),(.neg 19),(.pos 25),(.pos 32)]),
   ((.exchange 27 19 5),[(.neg 27),(.neg 19),(.pos 15),(.pos 21)]),
   ((.exchange 27 20 1),[(.neg 27),(.neg 20),(.pos 26),(.pos 33)]),
   ((.exchange 27 20 5),[(.neg 27),(.neg 20),(.pos 15),(.pos 21)]),
   ((.exchange 27 22 5),[(.neg 27),(.neg 22),(.pos 15),(.pos 18),(.pos 21)]),
   ((.exchange 27 28 1),[(.neg 28),(.neg 27),(.pos 26),(.pos 30)]),
   ((.exchange 27 28 2),[(.neg 28),(.neg 27),(.pos 25),(.pos 29)]),
   ((.exchange 27 34 1),[(.neg 34),(.neg 27),(.pos 30),(.pos 33)]),
   ((.exchange 28 2 5),[(.neg 28),(.neg 2),(.pos 16),(.pos 22)]),
   ((.exchange 28 3 5),[(.neg 28),(.neg 3),(.pos 17),(.pos 22)]),
   ((.exchange 28 8 0),[(.neg 28),(.neg 8),(.pos 29),(.pos 30)]),
   ((.exchange 28 11 3),[(.neg 28),(.neg 11),(.pos 25),(.pos 26),(.pos 31)]),
   ((.exchange 28 13 0),[(.neg 28),(.neg 13),(.pos 29),(.pos 34)]),
   ((.exchange 28 14 0),[(.neg 28),(.neg 14),(.pos 30),(.pos 34)]),
   ((.exchange 28 15 3),[(.neg 28),(.neg 15),(.pos 25),(.pos 26)]),
   ((.exchange 28 18 0),[(.neg 28),(.neg 18),(.pos 29),(.pos 30)]),
   ((.exchange 28 19 3),[(.neg 28),(.neg 19),(.pos 25),(.pos 31)]),
   ((.exchange 28 19 5),[(.neg 28),(.neg 19),(.pos 16),(.pos 22)]),
   ((.exchange 28 20 3),[(.neg 28),(.neg 20),(.pos 26),(.pos 31)]),
   ((.exchange 28 32 0),[(.neg 32),(.neg 28),(.pos 29),(.pos 34)]),
   ((.exchange 29 1 5),[(.neg 29),(.neg 1),(.pos 16),(.pos 18),(.pos 23)]),
   ((.exchange 29 4 5),[(.neg 29),(.neg 4),(.pos 18),(.pos 23)]),
   ((.exchange 29 5 3),[(.neg 29),(.neg 5),(.pos 25),(.pos 27)]),
   ((.exchange 29 7 1),[(.neg 29),(.neg 7),(.pos 28),(.pos 30)]),
   ((.exchange 29 9 3),[(.neg 29),(.neg 9),(.pos 25),(.pos 32)]),
   ((.exchange 29 10 1),[(.neg 29),(.neg 10),(.pos 28),(.pos 30),(.pos 34)]),
   ((.exchange 29 12 1),[(.neg 29),(.neg 12),(.pos 28),(.pos 34)]),
   ((.exchange 29 14 1),[(.neg 29),(.neg 14),(.pos 30),(.pos 34)]),
   ((.exchange 29 19 3),[(.neg 29),(.neg 19),(.pos 25),(.pos 32)]),
   ((.exchange 29 19 5),[(.neg 29),(.neg 19),(.pos 16),(.pos 23)]),
   ((.exchange 29 22 1),[(.neg 29),(.neg 22),(.pos 28),(.pos 34)]),
   ((.exchange 29 22 5),[(.neg 29),(.neg 22),(.pos 16),(.pos 23)]),
   ((.exchange 29 26 1),[(.neg 29),(.neg 26),(.pos 28),(.pos 30)]),
   ((.exchange 29 26 3),[(.neg 29),(.neg 26),(.pos 25),(.pos 27)]),
   ((.exchange 29 31 1),[(.neg 31),(.neg 29),(.pos 28),(.pos 34)]),
   ((.exchange 29 31 3),[(.neg 31),(.neg 29),(.pos 25),(.pos 32)]),
   ((.exchange 30 1 5),[(.neg 30),(.neg 1),(.pos 17),(.pos 18),(.pos 24)]),
   ((.exchange 30 4 5),[(.neg 30),(.neg 4),(.pos 18),(.pos 24)]),
   ((.exchange 30 11 3),[(.neg 30),(.neg 11),(.pos 27),(.pos 33)]),
   ((.exchange 30 12 2),[(.neg 30),(.neg 12),(.pos 28),(.pos 34)]),
   ((.exchange 30 13 2),[(.neg 30),(.neg 13),(.pos 29),(.pos 34)]),
   ((.exchange 30 15 3),[(.neg 30),(.neg 15),(.pos 26),(.pos 27)]),
   ((.exchange 30 16 2),[(.neg 30),(.neg 16),(.pos 28),(.pos 29)]),
   ((.exchange 30 19 3),[(.neg 30),(.neg 19),(.pos 26),(.pos 27),(.pos 33)]),
   ((.exchange 30 20 3),[(.neg 30),(.neg 20),(.pos 26),(.pos 33)]),
   ((.exchange 30 21 5),[(.neg 30),(.neg 21),(.pos 18),(.pos 24)]),
   ((.exchange 30 22 2),[(.neg 30),(.neg 22),(.pos 28),(.pos 34)]),
   ((.exchange 30 23 5),[(.neg 30),(.neg 23),(.pos 18),(.pos 24)]),
   ((.exchange 30 25 2),[(.neg 30),(.neg 25),(.pos 28),(.pos 29)]),
   ((.exchange 30 25 3),[(.neg 30),(.neg 25),(.pos 26),(.pos 27)]),
   ((.exchange 30 31 3),[(.neg 31),(.neg 30),(.pos 26),(.pos 33)]),
   ((.exchange 30 32 2),[(.neg 32),(.neg 30),(.pos 29),(.pos 34)]),
   ((.exchange 31 1 5),[(.neg 31),(.neg 1),(.pos 19),(.pos 20)]),
   ((.exchange 31 5 4),[(.neg 31),(.neg 5),(.pos 25),(.pos 26)]),
   ((.exchange 31 6 4),[(.neg 31),(.neg 6),(.pos 25),(.pos 28)]),
   ((.exchange 31 11 0),[(.neg 31),(.neg 11),(.pos 32),(.pos 33)]),
   ((.exchange 31 13 0),[(.neg 31),(.neg 13),(.pos 32),(.pos 34)]),
   ((.exchange 31 14 0),[(.neg 31),(.neg 14),(.pos 33),(.pos 34)]),
   ((.exchange 31 15 4),[(.neg 31),(.neg 15),(.pos 25),(.pos 26)]),
   ((.exchange 31 16 4),[(.neg 31),(.neg 16),(.pos 25),(.pos 28)]),
   ((.exchange 31 21 0),[(.neg 31),(.neg 21),(.pos 32),(.pos 33)]),
   ((.exchange 31 23 0),[(.neg 31),(.neg 23),(.pos 32),(.pos 34)]),
   ((.exchange 31 29 0),[(.neg 31),(.neg 29),(.pos 32),(.pos 34)]),
   ((.exchange 32 2 5),[(.neg 32),(.neg 2),(.pos 19),(.pos 23)]),
   ((.exchange 32 3 5),[(.neg 32),(.neg 3),(.pos 19),(.pos 21),(.pos 23)]),
   ((.exchange 32 4 5),[(.neg 32),(.neg 4),(.pos 21),(.pos 23)]),
   ((.exchange 32 6 4),[(.neg 32),(.neg 6),(.pos 25),(.pos 29)]),
   ((.exchange 32 8 4),[(.neg 32),(.neg 8),(.pos 27),(.pos 29)]),
   ((.exchange 32 12 1),[(.neg 32),(.neg 12),(.pos 31),(.pos 34)]),
   ((.exchange 32 14 1),[(.neg 32),(.neg 14),(.pos 33),(.pos 34)]),
   ((.exchange 32 15 4),[(.neg 32),(.neg 15),(.pos 25),(.pos 27)]),
   ((.exchange 32 15 5),[(.neg 32),(.neg 15),(.pos 19),(.pos 21)]),
   ((.exchange 32 16 4),[(.neg 32),(.neg 16),(.pos 25),(.pos 29)]),
   ((.exchange 32 18 4),[(.neg 32),(.neg 18),(.pos 27),(.pos 29)]),
   ((.exchange 32 20 1),[(.neg 32),(.neg 20),(.pos 31),(.pos 33)]),
   ((.exchange 32 22 1),[(.neg 32),(.neg 22),(.pos 31),(.pos 34)]),
   ((.exchange 32 28 4),[(.neg 32),(.neg 28),(.pos 25),(.pos 29)]),
   ((.exchange 33 2 2),[(.neg 33),(.neg 2),(.pos 31),(.pos 32),(.pos 34)]),
   ((.exchange 33 3 5),[(.neg 33),(.neg 3),(.pos 20),(.pos 24)]),
   ((.exchange 33 4 5),[(.neg 33),(.neg 4),(.pos 21),(.pos 24)]),
   ((.exchange 33 5 4),[(.neg 33),(.neg 5),(.pos 26),(.pos 27)]),
   ((.exchange 33 7 4),[(.neg 33),(.neg 7),(.pos 26),(.pos 30)]),
   ((.exchange 33 8 4),[(.neg 33),(.neg 8),(.pos 27),(.pos 30)]),
   ((.exchange 33 9 2),[(.neg 33),(.neg 9),(.pos 31),(.pos 32)]),
   ((.exchange 33 12 2),[(.neg 33),(.neg 12),(.pos 31),(.pos 34)]),
   ((.exchange 33 13 2),[(.neg 33),(.neg 13),(.pos 32),(.pos 34)]),
   ((.exchange 33 15 4),[(.neg 33),(.neg 15),(.pos 26),(.pos 27)]),
   ((.exchange 33 15 5),[(.neg 33),(.neg 15),(.pos 20),(.pos 21)]),
   ((.exchange 33 17 4),[(.neg 33),(.neg 17),(.pos 26),(.pos 30)]),
   ((.exchange 33 18 4),[(.neg 33),(.neg 18),(.pos 27),(.pos 30)]),
   ((.exchange 33 18 5),[(.neg 33),(.neg 18),(.pos 21),(.pos 24)]),
   ((.exchange 33 19 2),[(.neg 33),(.neg 19),(.pos 31),(.pos 32)]),
   ((.exchange 33 22 5),[(.neg 33),(.neg 22),(.pos 20),(.pos 24)]),
   ((.exchange 33 25 4),[(.neg 33),(.neg 25),(.pos 26),(.pos 27)]),
   ((.exchange 33 28 2),[(.neg 33),(.neg 28),(.pos 31),(.pos 34)]),
   ((.exchange 33 29 4),[(.neg 33),(.neg 29),(.pos 27),(.pos 30)]),
   ((.exchange 34 2 5),[(.neg 34),(.neg 2),(.pos 22),(.pos 23)]),
   ((.exchange 34 3 5),[(.neg 34),(.neg 3),(.pos 22),(.pos 24)]),
   ((.exchange 34 4 5),[(.neg 34),(.neg 4),(.pos 23),(.pos 24)]),
   ((.exchange 34 6 4),[(.neg 34),(.neg 6),(.pos 28),(.pos 29)]),
   ((.exchange 34 7 4),[(.neg 34),(.neg 7),(.pos 28),(.pos 30)]),
   ((.exchange 34 8 4),[(.neg 34),(.neg 8),(.pos 29),(.pos 30)]),
   ((.exchange 34 9 3),[(.neg 34),(.neg 9),(.pos 31),(.pos 32)]),
   ((.exchange 34 10 3),[(.neg 34),(.neg 10),(.pos 31),(.pos 33)]),
   ((.exchange 34 11 3),[(.neg 34),(.neg 11),(.pos 32),(.pos 33)]),
   ((.exchange 34 16 4),[(.neg 34),(.neg 16),(.pos 28),(.pos 29)]),
   ((.exchange 34 16 5),[(.neg 34),(.neg 16),(.pos 22),(.pos 23)]),
   ((.exchange 34 17 4),[(.neg 34),(.neg 17),(.pos 28),(.pos 30)])]

theorem certificates_1_valid : ∀ oc ∈ certificates_1,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_2 : List (Origin 35 197 × List Sat.Literal) :=
  [((.exchange 34 17 5),[(.neg 34),(.neg 17),(.pos 22),(.pos 24)]),
   ((.exchange 34 18 4),[(.neg 34),(.neg 18),(.pos 29),(.pos 30)]),
   ((.exchange 34 18 5),[(.neg 34),(.neg 18),(.pos 23),(.pos 24)]),
   ((.exchange 34 19 3),[(.neg 34),(.neg 19),(.pos 31),(.pos 32)]),
   ((.exchange 34 20 3),[(.neg 34),(.neg 20),(.pos 31),(.pos 33)]),
   ((.exchange 34 20 5),[(.neg 34),(.neg 20),(.pos 22),(.pos 24)]),
   ((.exchange 34 21 5),[(.neg 34),(.neg 21),(.pos 23),(.pos 24)]),
   ((.exchange 34 25 3),[(.neg 34),(.neg 25),(.pos 31),(.pos 32)]),
   ((.exchange 34 25 4),[(.neg 34),(.neg 25),(.pos 28),(.pos 29)]),
   ((.exchange 34 26 3),[(.neg 34),(.neg 26),(.pos 31),(.pos 33)]),
   ((.exchange 34 26 4),[(.neg 34),(.neg 26),(.pos 28),(.pos 30)]),
   ((.exchange 34 27 3),[(.neg 34),(.neg 27),(.pos 32),(.pos 33)]),
   ((.exchange 34 27 4),[(.neg 34),(.neg 27),(.pos 29),(.pos 30)]),
   (.newPoint,[(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 19),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 30),(.pos 31),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 0),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 27),(.neg 24),(.neg 23),(.neg 21),(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 19),(.pos 20),(.pos 22),(.pos 25),(.pos 26),(.pos 28),(.pos 31)]),
   ((.excluded 1),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 28),(.neg 26),(.neg 24),(.neg 22),(.neg 20),(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 19),(.pos 21),(.pos 23),(.pos 25),(.pos 27),(.pos 29),(.pos 32)]),
   ((.excluded 2),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 19),(.pos 24),(.pos 25),(.pos 30)]),
   ((.excluded 3),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 19),(.pos 25),(.pos 33)]),
   ((.excluded 4),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 19),(.pos 25),(.pos 34)]),
   ((.excluded 5),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 19),(.pos 25)]),
   ((.excluded 6),[(.neg 34),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 25),(.neg 23),(.neg 22),(.neg 19),(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 20),(.pos 21),(.pos 24),(.pos 26),(.pos 27),(.pos 30),(.pos 33)]),
   ((.excluded 7),[(.neg 33),(.neg 32),(.neg 31),(.neg 27),(.neg 26),(.neg 25),(.neg 21),(.neg 20),(.neg 19),(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 22),(.pos 23),(.pos 24),(.pos 28),(.pos 29),(.pos 30),(.pos 34)]),
   ((.excluded 8),[(.neg 34),(.neg 33),(.neg 32),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 24),(.pos 30),(.pos 31)]),
   ((.excluded 9),[(.neg 34),(.neg 33),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 24),(.pos 30),(.pos 32)]),
   ((.excluded 10),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 24),(.pos 30)]),
   ((.excluded 11),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 19),(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 20),(.pos 23),(.pos 26),(.pos 29)]),
   ((.excluded 12),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 20),(.pos 26),(.pos 32)]),
   ((.excluded 13),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 20),(.pos 26),(.pos 34)]),
   ((.excluded 14),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 20),(.pos 26)]),
   ((.excluded 15),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 23),(.pos 29),(.pos 31)]),
   ((.excluded 16),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 23),(.pos 29),(.pos 33)]),
   ((.excluded 17),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 23),(.pos 29)]),
   ((.excluded 18),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 20),(.neg 19),(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 21),(.pos 22),(.pos 27),(.pos 28)]),
   ((.excluded 19),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 21),(.pos 27),(.pos 31)]),
   ((.excluded 20),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 21),(.pos 27),(.pos 34)]),
   ((.excluded 21),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 21),(.pos 27)]),
   ((.excluded 22),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 22),(.pos 28),(.pos 32)]),
   ((.excluded 23),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 22),(.pos 28),(.pos 33)]),
   ((.excluded 24),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 22),(.pos 28)]),
   ((.excluded 25),[(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 31),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 26),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 31)]),
   ((.excluded 27),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 32)]),
   ((.excluded 28),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 33)]),
   ((.excluded 29),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 34)]),
   ((.excluded 30),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.pos 15),(.pos 16),(.pos 17),(.pos 18)]),
   ((.excluded 31),[(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 31),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 32),[(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 30),(.pos 31),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 33),[(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 31),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 34),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 21),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 20),(.pos 22),(.pos 27),(.pos 31)]),
   ((.excluded 35),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 21),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 20),(.pos 22),(.pos 29),(.pos 31)]),
   ((.excluded 36),[(.neg 34),(.neg 33),(.neg 32),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 21),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 20),(.pos 22),(.pos 30),(.pos 31)]),
   ((.excluded 37),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 21),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 20),(.pos 22),(.pos 31)]),
   ((.excluded 38),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 27),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 21),(.pos 25),(.pos 26),(.pos 28),(.pos 31)]),
   ((.excluded 39),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 27),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 23),(.pos 25),(.pos 26),(.pos 28),(.pos 31)]),
   ((.excluded 40),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 27),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 24),(.pos 25),(.pos 26),(.pos 28),(.pos 31)]),
   ((.excluded 41),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 27),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 25),(.pos 26),(.pos 28),(.pos 31)]),
   ((.excluded 42),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 21),(.pos 29),(.pos 31)]),
   ((.excluded 43),[(.neg 34),(.neg 33),(.neg 32),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 21),(.pos 30),(.pos 31)]),
   ((.excluded 44),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 21),(.pos 31)]),
   ((.excluded 45),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 24),(.pos 29),(.pos 31)]),
   ((.excluded 46),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 29),(.pos 31)]),
   ((.excluded 47),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 24),(.pos 27),(.pos 31)]),
   ((.excluded 48),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 24),(.pos 31)]),
   ((.excluded 49),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 23),(.pos 27),(.pos 31)]),
   ((.excluded 50),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 27),(.pos 31)]),
   ((.excluded 51),[(.neg 34),(.neg 33),(.neg 32),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 23),(.pos 30),(.pos 31)]),
   ((.excluded 52),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 23),(.pos 31)]),
   ((.excluded 53),[(.neg 34),(.neg 33),(.neg 32),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 30),(.pos 31)]),
   ((.excluded 54),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 31)]),
   ((.excluded 55),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 22),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 21),(.pos 23),(.pos 26),(.pos 32)]),
   ((.excluded 56),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 21),(.pos 23),(.pos 28),(.pos 32)]),
   ((.excluded 57),[(.neg 34),(.neg 33),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 21),(.pos 23),(.pos 30),(.pos 32)]),
   ((.excluded 58),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 21),(.pos 23),(.pos 32)]),
   ((.excluded 59),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 28),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20),(.pos 25),(.pos 27),(.pos 29),(.pos 32)]),
   ((.excluded 60),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 28),(.neg 26),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 22),(.pos 25),(.pos 27),(.pos 29),(.pos 32)]),
   ((.excluded 61),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 28),(.neg 26),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 24),(.pos 25),(.pos 27),(.pos 29),(.pos 32)]),
   ((.excluded 62),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 28),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 25),(.pos 27),(.pos 29),(.pos 32)]),
   ((.excluded 63),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20),(.pos 28),(.pos 32)]),
   ((.excluded 64),[(.neg 34),(.neg 33),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20),(.pos 30),(.pos 32)]),
   ((.excluded 65),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20),(.pos 32)]),
   ((.excluded 66),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 24),(.pos 28),(.pos 32)]),
   ((.excluded 67),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 28),(.pos 32)]),
   ((.excluded 68),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 24),(.pos 26),(.pos 32)]),
   ((.excluded 69),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 24),(.pos 32)]),
   ((.excluded 70),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 22),(.pos 26),(.pos 32)]),
   ((.excluded 71),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 26),(.pos 32)]),
   ((.excluded 72),[(.neg 34),(.neg 33),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 22),(.pos 30),(.pos 32)]),
   ((.excluded 73),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 22),(.pos 32)]),
   ((.excluded 74),[(.neg 34),(.neg 33),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 30),(.pos 32)]),
   ((.excluded 75),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 32)]),
   ((.excluded 76),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 23),(.neg 22),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20),(.pos 21),(.pos 24),(.pos 25),(.pos 33)]),
   ((.excluded 77),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20),(.pos 21),(.pos 24),(.pos 28),(.pos 33)]),
   ((.excluded 78),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20),(.pos 21),(.pos 24),(.pos 29),(.pos 33)]),
   ((.excluded 79),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20),(.pos 21),(.pos 24),(.pos 33)]),
   ((.excluded 80),[(.neg 34),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 26),(.pos 27),(.pos 30),(.pos 33)]),
   ((.excluded 81),[(.neg 34),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 25),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 22),(.pos 26),(.pos 27),(.pos 30),(.pos 33)]),
   ((.excluded 82),[(.neg 34),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 23),(.pos 26),(.pos 27),(.pos 30),(.pos 33)]),
   ((.excluded 83),[(.neg 34),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 26),(.pos 27),(.pos 30),(.pos 33)]),
   ((.excluded 84),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 28),(.pos 33)]),
   ((.excluded 85),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 29),(.pos 33)]),
   ((.excluded 86),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 33)]),
   ((.excluded 87),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 23),(.pos 28),(.pos 33)]),
   ((.excluded 88),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 28),(.pos 33)]),
   ((.excluded 89),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 23),(.pos 25),(.pos 33)]),
   ((.excluded 90),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 23),(.pos 33)]),
   ((.excluded 91),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 22),(.pos 25),(.pos 33)]),
   ((.excluded 92),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 25),(.pos 33)]),
   ((.excluded 93),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 22),(.pos 29),(.pos 33)]),
   ((.excluded 94),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 22),(.pos 33)]),
   ((.excluded 95),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 29),(.pos 33)]),
   ((.excluded 96),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 33)]),
   ((.excluded 97),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 34)]),
   ((.excluded 98),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 22),(.pos 23),(.pos 24),(.pos 26),(.pos 34)]),
   ((.excluded 99),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 22),(.pos 23),(.pos 24),(.pos 27),(.pos 34)]),
   ((.excluded 100),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 22),(.pos 23),(.pos 24),(.pos 34)]),
   ((.excluded 101),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 22),(.pos 27)]),
   ((.excluded 102),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 21),(.pos 22),(.pos 25),(.pos 30)]),
   ((.excluded 103),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 21),(.pos 22),(.pos 25)]),
   ((.excluded 104),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 22),(.pos 25),(.pos 30)]),
   ((.excluded 105),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 22),(.pos 25)]),
   ((.excluded 106),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 21),(.pos 22),(.pos 30)]),
   ((.excluded 107),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 22),(.pos 30)]),
   ((.excluded 108),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 21),(.pos 22),(.pos 26),(.pos 29)]),
   ((.excluded 109),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 21),(.pos 22),(.pos 26)]),
   ((.excluded 110),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 21),(.pos 22),(.pos 29)]),
   ((.excluded 111),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 21),(.pos 22)]),
   ((.excluded 112),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 22),(.pos 26),(.pos 29)]),
   ((.excluded 113),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 22),(.pos 26)])]

theorem certificates_2_valid : ∀ oc ∈ certificates_2,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_3 : List (Origin 35 197 × List Sat.Literal) :=
  [((.excluded 114),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 22),(.pos 29)]),
   ((.excluded 115),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 22)]),
   ((.excluded 116),[(.neg 33),(.neg 32),(.neg 31),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 28),(.pos 29),(.pos 30),(.pos 34)]),
   ((.excluded 117),[(.neg 33),(.neg 32),(.neg 31),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20),(.pos 28),(.pos 29),(.pos 30),(.pos 34)]),
   ((.excluded 118),[(.neg 33),(.neg 32),(.neg 31),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 21),(.pos 28),(.pos 29),(.pos 30),(.pos 34)]),
   ((.excluded 119),[(.neg 33),(.neg 32),(.neg 31),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 28),(.pos 29),(.pos 30),(.pos 34)]),
   ((.excluded 120),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20),(.pos 29)]),
   ((.excluded 121),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 21),(.pos 26),(.pos 29)]),
   ((.excluded 122),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 21),(.pos 29)]),
   ((.excluded 123),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 24),(.pos 26),(.pos 29)]),
   ((.excluded 124),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 24),(.pos 29)]),
   ((.excluded 125),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 26),(.pos 29)]),
   ((.excluded 126),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 29)]),
   ((.excluded 127),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 24),(.pos 26),(.pos 29)]),
   ((.excluded 128),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 24),(.pos 29)]),
   ((.excluded 129),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 26),(.pos 29)]),
   ((.excluded 130),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 29)]),
   ((.excluded 131),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 21),(.pos 28)]),
   ((.excluded 132),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 21),(.pos 26),(.pos 34)]),
   ((.excluded 133),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 21),(.pos 26)]),
   ((.excluded 134),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 21),(.pos 25),(.pos 30)]),
   ((.excluded 135),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 21),(.pos 30)]),
   ((.excluded 136),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 21),(.pos 25),(.pos 34)]),
   ((.excluded 137),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 21),(.pos 25)]),
   ((.excluded 138),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 21),(.pos 34)]),
   ((.excluded 139),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 21)]),
   ((.excluded 140),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 23),(.pos 26)]),
   ((.excluded 141),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 24),(.pos 26)]),
   ((.excluded 142),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 24),(.pos 26)]),
   ((.excluded 143),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 26),(.pos 34)]),
   ((.excluded 144),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 26)]),
   ((.excluded 145),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 26),(.pos 34)]),
   ((.excluded 146),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 26)]),
   ((.excluded 147),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 24),(.pos 25)]),
   ((.excluded 148),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 24),(.pos 27),(.pos 28)]),
   ((.excluded 149),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 24),(.pos 27)]),
   ((.excluded 150),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 24),(.pos 28)]),
   ((.excluded 151),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 24)]),
   ((.excluded 152),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 24),(.pos 27),(.pos 28)]),
   ((.excluded 153),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 24),(.pos 27)]),
   ((.excluded 154),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 24),(.pos 28)]),
   ((.excluded 155),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 24)]),
   ((.excluded 156),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 30)]),
   ((.excluded 157),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 27),(.pos 28)]),
   ((.excluded 158),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 28)]),
   ((.excluded 159),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 27),(.pos 34)]),
   ((.excluded 160),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 27)]),
   ((.excluded 161),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 34)]),
   ((.excluded 162),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19)]),
   ((.excluded 163),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20),(.pos 23),(.pos 27),(.pos 28)]),
   ((.excluded 164),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20),(.pos 23),(.pos 28)]),
   ((.excluded 165),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20),(.pos 27),(.pos 28)]),
   ((.excluded 166),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20),(.pos 28)]),
   ((.excluded 167),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 23),(.pos 27),(.pos 28)]),
   ((.excluded 168),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 23),(.pos 28)]),
   ((.excluded 169),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 27),(.pos 28)]),
   ((.excluded 170),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 28)]),
   ((.excluded 171),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20),(.pos 23),(.pos 27)]),
   ((.excluded 172),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 23),(.pos 27)]),
   ((.excluded 173),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20),(.pos 27),(.pos 34)]),
   ((.excluded 174),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20),(.pos 27)]),
   ((.excluded 175),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 27),(.pos 34)]),
   ((.excluded 176),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 27)]),
   ((.excluded 177),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20),(.pos 25),(.pos 34)]),
   ((.excluded 178),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20),(.pos 34)]),
   ((.excluded 179),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 25),(.pos 34)]),
   ((.excluded 180),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 34)]),
   ((.excluded 181),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20),(.pos 23),(.pos 25),(.pos 30)]),
   ((.excluded 182),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20),(.pos 23),(.pos 25)]),
   ((.excluded 183),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20),(.pos 23),(.pos 30)]),
   ((.excluded 184),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20),(.pos 23)]),
   ((.excluded 185),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20),(.pos 25),(.pos 30)]),
   ((.excluded 186),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20),(.pos 25)]),
   ((.excluded 187),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20),(.pos 30)]),
   ((.excluded 188),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20)]),
   ((.excluded 189),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 23),(.pos 25),(.pos 30)]),
   ((.excluded 190),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 23),(.pos 25)]),
   ((.excluded 191),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 23),(.pos 30)]),
   ((.excluded 192),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 23)]),
   ((.excluded 193),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 25),(.pos 30)]),
   ((.excluded 194),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 25)]),
   ((.excluded 195),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 30)]),
   ((.excluded 196),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15)])]

theorem certificates_3_valid : ∀ oc ∈ certificates_3,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



theorem witness_0 : ∀ j : Fin 128,
    let w : Fin 197 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 7 4 ∧
      ValidWitness 7 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 7 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 128,
      let w : Fin 197 := ⟨0 + j.val,by omega⟩
      target w < MatroidCatalogue.count 7 4 ∧
        Papers.RationalityTen.MatroidChecked.FastSemanticChecks.RawWitness 7 (N6R4.familyMasks.get 16)
        (fun i : Fin 35 => N7R4.gridMasks.get i.val) newIndex (models w)
        (N7R4.familyMasks.get (target w)) (permutation w) := by
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
  exact ⟨hj.1,Papers.RationalityTen.MatroidChecked.FastSemanticChecks.rawWitness_sound 7 _ _ _ _ _ _ hj.2⟩



theorem witness_1 : ∀ j : Fin 69,
    let w : Fin 197 := ⟨128 + j.val,by omega⟩
    target w < MatroidCatalogue.count 7 4 ∧
      ValidWitness 7 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 7 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 69,
      let w : Fin 197 := ⟨128 + j.val,by omega⟩
      target w < MatroidCatalogue.count 7 4 ∧
        Papers.RationalityTen.MatroidChecked.FastSemanticChecks.RawWitness 7 (N6R4.familyMasks.get 16)
        (fun i : Fin 35 => N7R4.gridMasks.get i.val) newIndex (models w)
        (N7R4.familyMasks.get (target w)) (permutation w) := by
    refine (Fin.forall_fin_add (m := 34) (n := 35) _).2 ⟨?_, ?_⟩
    · refine (Fin.forall_fin_add (m := 17) (n := 17) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 8) (n := 9) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
          · decide +kernel
          · decide +kernel
        · refine (Fin.forall_fin_add (m := 4) (n := 5) _).2 ⟨?_, ?_⟩
          · decide +kernel
          · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
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
    · refine (Fin.forall_fin_add (m := 17) (n := 18) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 8) (n := 9) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
          · decide +kernel
          · decide +kernel
        · refine (Fin.forall_fin_add (m := 4) (n := 5) _).2 ⟨?_, ?_⟩
          · decide +kernel
          · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
      · refine (Fin.forall_fin_add (m := 9) (n := 9) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 4) (n := 5) _).2 ⟨?_, ?_⟩
          · decide +kernel
          · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
        · refine (Fin.forall_fin_add (m := 4) (n := 5) _).2 ⟨?_, ?_⟩
          · decide +kernel
          · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
            · decide +kernel
  intro j
  have hj := hfast j
  exact ⟨hj.1,Papers.RationalityTen.MatroidChecked.FastSemanticChecks.rawWitness_sound 7 _ _ _ _ _ _ hj.2⟩


end Papers.RationalityTen.MatroidCatalogue.Cases.N7R4C16

/- Source: MatroidCatalogue/Cases/N7R4C16Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R4C16

noncomputable def certificates : List (Origin 35 197 × List Sat.Literal) :=
  certificates_0 ++ certificates_1 ++ certificates_2 ++ certificates_3

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  intro oc hoc
  simp only [certificates,List.mem_append,or_assoc] at hoc
  rcases hoc with h0 | h1 | h2 | h3
  · exact certificates_0_valid oc h0
  · exact certificates_1_valid oc h1
  · exact certificates_2_valid oc h2
  · exact certificates_3_valid oc h3

theorem models_valid : ∀ w : Fin 197,
    target w < MatroidCatalogue.count 7 4 ∧
      ValidWitness 7 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 7 4 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  by_cases h0 : w.val < 128
  ·
    have hh := witness_0 ⟨w.val - 0,by omega⟩
    have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 197) = w := Fin.ext (by dsimp only; omega)
    dsimp only at hh
    rw [heq] at hh
    exact hh
  ·
    have hh := witness_1 ⟨w.val - 128,by omega⟩
    have heq : (⟨128 + (w.val - 128),by omega⟩ : Fin 197) = w := Fin.ext (by dsimp only; omega)
    dsimp only at hh
    rw [heq] at hh
    exact hh

theorem coverage (M : BasisFamily (groundPrefix 7) 4)
    (hold : M.bases.filter ((6 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 7 4, IsomorphicWithin 7 M.bases B := by
  apply extension_covered_of_certificate (n:=6) (r:=4) (by decide)
    catalogue old U newIndex models certificates
    N7R4.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidChecked.PublicRefutations.N7R4C16.formula []
    exact Papers.RationalityTen.MatroidChecked.PublicRefutations.N7R4C16.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 7 4 (target w),family_mem 7 4 (target w) hw.1,?_⟩
    exact validWitness_sound 7 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R4C16


end
end
end BundlePart0

section BundlePart1
/- Source: MatroidChecked/SemanticChunks/Cases02Part01.lean -/




@[expose] public section
noncomputable section

/- Source: MatroidCatalogue/Cases/N7R4C17Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R4C17

abbrev U := N7R4.grid
noncomputable def old : Finset (Finset (Fin 8)) := N6R4.family 17
noncomputable def newIndexTree : Table ℕ := (.node 10 (.node 5 (.node 2 (.node 1 (.leaf 15) (.leaf 16)) (.node 3 (.leaf 17) (.node 4 (.leaf 18) (.leaf 19)))) (.node 7 (.node 6 (.leaf 20) (.leaf 21)) (.node 8 (.leaf 22) (.node 9 (.leaf 23) (.leaf 24))))) (.node 15 (.node 12 (.node 11 (.leaf 25) (.leaf 26)) (.node 13 (.leaf 27) (.node 14 (.leaf 28) (.leaf 29)))) (.node 17 (.node 16 (.leaf 30) (.leaf 31)) (.node 18 (.leaf 32) (.node 19 (.leaf 33) (.leaf 34))))))
noncomputable def newIndex (i : Fin 20) : Fin 35 := Fin.ofNat 35 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 176 (.node 88 (.node 44 (.node 22 (.node 11 (.node 5 (.node 2 (.node 1 (.leaf (971592,64,15161552)) (.leaf (895652,64,15161538))) (.node 3 (.leaf (1047020,68,14899409)) (.node 4 (.leaf (1014764,68,14870737)) (.leaf (785388,68,14863569))))) (.node 8 (.node 6 (.leaf (523244,68,14862225)) (.node 7 (.leaf (1047532,70,15423688)) (.leaf (523390,68,14885731)))) (.node 9 (.leaf (522202,68,14862001)) (.node 10 (.leaf (520118,68,14861966)) (.leaf (466942,68,14771043)))))) (.node 16 (.node 13 (.node 12 (.leaf (65534,68,14753123)) (.leaf (524286,82,14862225))) (.node 14 (.leaf (746898,64,15161370)) (.node 15 (.leaf (1046234,68,14899353)) (.leaf (1030106,68,14870681))))) (.node 19 (.node 17 (.leaf (915418,68,14863513)) (.node 18 (.leaf (1046490,70,15423576)) (.leaf (1044278,68,14899339)))) (.node 20 (.leaf (1036214,68,14870667)) (.node 21 (.leaf (978870,68,14863499)) (.leaf (1044406,70,15423555))))))) (.node 33 (.node 27 (.node 24 (.node 23 (.leaf (769918,79,14826833)) (.leaf (1032062,80,14862225))) (.node 25 (.leaf (786302,80,14858417)) (.node 26 (.leaf (884606,79,14837585)) (.leaf (1015678,80,14862001))))) (.node 30 (.node 28 (.leaf (917374,80,14858641)) (.node 29 (.leaf (1048446,81,15161552)) (.leaf (770046,80,14801038)))) (.node 31 (.leaf (966142,79,14891345)) (.node 32 (.leaf (1031678,80,14833294)) (.leaf (966654,80,14797713)))))) (.node 38 (.node 35 (.node 34 (.leaf (1032190,81,15132866)) (.leaf (777982,79,14798161))) (.node 36 (.leaf (786174,80,14858382)) (.node 37 (.leaf (778238,80,14801073)) (.leaf (786430,81,15125530))))) (.node 41 (.node 39 (.leaf (1040126,80,14833553)) (.node 40 (.leaf (950014,79,14805329)) (.leaf (1015550,80,14861966)))) (.node 42 (.leaf (982782,80,14826385)) (.node 43 (.leaf (1048318,81,15161538)) (.leaf (908798,79,14894929)))))))) (.node 66 (.node 55 (.node 49 (.node 46 (.node 45 (.leaf (1039870,80,14833329)) (.leaf (909310,80,14801297))) (.node 47 (.leaf (1040382,81,15132880)) (.node 48 (.leaf (982526,80,14826161)) (.leaf (916990,80,14826126))))) (.node 52 (.node 50 (.leaf (1048062,81,15161370)) (.node 51 (.leaf (950270,80,14797489)) (.leaf (983038,81,15125712)))) (.node 53 (.leaf (884734,80,14797454)) (.node 54 (.leaf (1015806,81,15132698)) (.leaf (917502,81,15125698)))))) (.node 60 (.node 57 (.node 56 (.leaf (1048574,83,15685768)) (.leaf (466033,64,15159578))) (.node 58 (.leaf (64527,64,15141658)) (.node 59 (.leaf (522367,68,14853027)) (.leaf (521343,68,14852915))))) (.node 63 (.node 61 (.leaf (519295,68,14852894)) (.node 62 (.leaf (523391,70,15405411)) (.leaf (1040185,68,14898457)))) (.node 64 (.leaf (1036153,68,14869785)) (.node 65 (.leaf (909177,68,14861721)) (.leaf (778105,68,14861553))))))) (.node 77 (.node 71 (.node 68 (.node 67 (.leaf (1040249,70,15422232)) (.leaf (978767,68,14855449))) (.node 69 (.leaf (895871,68,14768523)) (.node 70 (.leaf (747391,68,14768243)) (.leaf (1044351,82,14869785))))) (.node 74 (.node 72 (.leaf (982855,68,14887705)) (.node 73 (.leaf (966479,68,14854553)) (.leaf (950095,68,14854385)))) (.node 75 (.leaf (982863,70,15407896)) (.node 76 (.leaf (769919,80,14787430)) (.leaf (1029951,79,14870177)))))) (.node 82 (.node 79 (.node 78 (.leaf (1031999,80,14890253)) (.leaf (1030015,80,14804265))) (.node 80 (.leaf (1032063,81,15118754)) (.node 81 (.leaf (785271,79,14859537)) (.leaf (786295,80,14824565))))) (.node 85 (.node 83 (.leaf (785279,80,14789985)) (.node 84 (.leaf (786303,81,15107890)) (.leaf (1047415,80,14894929)))) (.node 86 (.leaf (915319,79,14859425)) (.node 87 (.leaf (1046391,80,14894761)) (.leaf (917367,80,14824845))))))))) (.node 132 (.node 110 (.node 99 (.node 93 (.node 90 (.node 89 (.leaf (1048439,81,15151458)) (.leaf (1014591,79,14870289))) (.node 91 (.leaf (1047359,80,14891345)) (.node 92 (.leaf (1014655,80,14804321)) (.leaf (1047423,81,15063440))))) (.node 96 (.node 94 (.leaf (1046335,80,14891177)) (.node 95 (.leaf (1015615,80,14890085)) (.leaf (1048383,81,15140706)))) (.node 97 (.leaf (915327,80,14789929)) (.node 98 (.leaf (1046399,81,15063216)) (.leaf (884607,80,14787374)))))) (.node 104 (.node 101 (.node 100 (.leaf (1015679,81,15118642)) (.leaf (917375,81,15108002))) (.node 102 (.leaf (1048447,83,15672160)) (.node 103 (.leaf (1023,64,14969626)) (.leaf (466927,68,14767011))))) (.node 107 (.node 105 (.leaf (466911,68,14766899)) (.node 106 (.leaf (466879,68,14766878)) (.leaf (466943,70,15262051)))) (.node 108 (.leaf (895995,68,14773003)) (.node 109 (.leaf (895967,68,14769419)) (.leaf (895487,68,14768334))))))) (.node 121 (.node 115 (.node 112 (.node 111 (.leaf (895999,70,15264515)) (.leaf (1031893,68,14898443))) (.node 113 (.leaf (769439,68,14854238)) (.node 114 (.leaf (1032159,82,14870681)) (.leaf (1029877,68,14869771))))) (.node 118 (.node 116 (.leaf (966389,68,14861707)) (.node 117 (.leaf (769781,68,14861518)) (.leaf (1031925,70,15422211)))) (.node 119 (.leaf (770027,79,14834897)) (.node 120 (.leaf (770043,80,14795886)) (.leaf (770031,80,14788942)))))) (.node 126 (.node 123 (.node 122 (.leaf (770047,81,14964502)) (.leaf (1032171,80,14870289))) (.node 124 (.leaf (966587,79,14805665)) (.node 125 (.leaf (1032123,80,14837389)) (.leaf (966651,80,14796201))))) (.node 129 (.node 127 (.leaf (1032187,81,15130850)) (.node 128 (.leaf (1029615,79,14899409)) (.leaf (1031663,80,14890316)))) (.node 130 (.leaf (1030127,80,14805777)) (.node 131 (.leaf (1032175,81,15120770)) (.leaf (1030079,80,14805133)))))))) (.node 154 (.node 143 (.node 137 (.node 134 (.node 133 (.leaf (966591,80,14789005)) (.leaf (1032127,81,15120518))) (.node 135 (.leaf (1029631,80,14804076)) (.node 136 (.leaf (1030143,81,14969570)) (.leaf (966143,80,14787493))))) (.node 140 (.node 138 (.leaf (1031679,81,15061270)) (.node 139 (.leaf (966655,81,14957474)) (.leaf (1032191,83,15557444)))) (.node 141 (.leaf (785821,68,14887523)) (.node 142 (.leaf (784799,68,14855267)) (.leaf (777631,68,14854259)))))) (.node 148 (.node 145 (.node 144 (.leaf (785823,70,15407651)) (.leaf (747517,68,14772835))) (.node 146 (.leaf (747503,68,14769251)) (.node 147 (.leaf (747263,68,14768222)) (.leaf (747519,70,15264291))))) (.node 151 (.node 149 (.leaf (65533,68,14752675)) (.node 150 (.leaf (65531,68,14752563)) (.leaf (65527,68,14752542)))) (.node 152 (.leaf (65535,70,15240547)) (.node 153 (.leaf (786429,82,14863569)) (.leaf (786411,80,14859425))))))) (.node 165 (.node 159 (.node 156 (.node 155 (.leaf (785147,79,14863569)) (.leaf (786171,80,14824558))) (.node 157 (.leaf (785403,80,14802081)) (.node 158 (.leaf (786427,81,15124018)) (.leaf (778215,79,14802193))))) (.node 162 (.node 160 (.leaf (786407,80,14859404)) (.node 161 (.leaf (778223,80,14788977)) (.leaf (786415,81,15109402)))) (.node 163 (.leaf (785399,80,14802060)) (.node 164 (.leaf (778231,80,14795893)) (.leaf (786423,81,15123990)))))) (.node 170 (.node 167 (.node 166 (.leaf (785151,80,14789964)) (.leaf (785407,81,14966042))) (.node 168 (.leaf (777983,80,14787444)) (.node 169 (.leaf (786175,81,15107862)) (.leaf (778239,81,14964530))))) (.node 173 (.node 171 (.leaf (786431,83,15539244)) (.node 172 (.leaf (884211,68,14861406)) (.leaf (917163,68,14887691)))) (.node 174 (.leaf (917499,82,14863513)) (.node 175 (.leaf (1015267,68,14898275)) (.leaf (1014259,68,14869603)))))))))) (.node 264 (.node 220 (.node 198 (.node 187 (.node 181 (.node 178 (.node 177 (.leaf (949747,68,14861427)) (.leaf (1015283,70,15421987))) (.node 179 (.leaf (520171,79,14833553)) (.node 180 (.leaf (1044459,80,14870737)) (.leaf (524267,80,14857633))))) (.node 184 (.node 182 (.leaf (1048555,81,15153936)) (.node 183 (.leaf (982971,80,14826665)) (.leaf (523195,79,14862225)))) (.node 185 (.leaf (1047483,80,14899409)) (.node 186 (.leaf (524219,80,14857318)) (.leaf (1048507,81,15160866)))))) (.node 192 (.node 189 (.node 188 (.leaf (1047291,80,14898961)) (.leaf (523259,80,14800289))) (.node 190 (.leaf (1047547,81,15067920)) (.node 191 (.leaf (520187,80,14799974)) (.leaf (524283,81,15122674))))) (.node 195 (.node 193 (.leaf (978683,79,14891681)) (.node 194 (.leaf (1044219,80,14894733)) (.leaf (982779,80,14824873)))) (.node 196 (.leaf (1048315,81,15159522)) (.node 197 (.leaf (978939,80,14797993)) (.leaf (1044475,81,15132194))))))) (.node 209 (.node 203 (.node 200 (.node 199 (.leaf (983035,81,15124144)) (.leaf (1048571,83,15684704))) (.node 201 (.leaf (915119,68,14855435)) (.node 202 (.leaf (908975,68,14854539)) (.leaf (884399,68,14854350))))) (.node 206 (.node 204 (.leaf (917167,70,15407875)) (.node 205 (.leaf (971711,68,14769433)) (.leaf (1040319,82,14898457)))) (.node 207 (.leaf (1014719,80,14805644)) (.node 208 (.leaf (523199,80,14789516)) (.leaf (1047487,81,15064322)))))) (.node 214 (.node 211 (.node 210 (.leaf (522173,79,14797713)) (.leaf (1046461,80,14834897))) (.node 212 (.leaf (522175,80,14789236)) (.node 213 (.leaf (1046463,81,15064098)) (.leaf (524221,80,14857486))))) (.node 217 (.node 215 (.leaf (524223,81,15108310)) (.node 216 (.leaf (950205,79,14805777)) (.leaf (1015741,80,14870156)))) (.node 218 (.leaf (982973,80,14826833)) (.node 219 (.leaf (1048509,81,15161090)) (.leaf (950207,80,14788725)))))))) (.node 242 (.node 231 (.node 225 (.node 222 (.node 221 (.leaf (1015743,81,15120406)) (.leaf (982975,81,15043938))) (.node 223 (.leaf (1048511,83,15673924)) (.node 224 (.leaf (971767,68,14773017)) (.leaf (971519,68,14768537))))) (.node 228 (.node 226 (.leaf (971263,68,14768369)) (.node 227 (.leaf (971775,70,15264536)) (.leaf (1047039,82,14899409)))) (.node 229 (.leaf (523223,79,14858641)) (.node 230 (.leaf (1047511,80,14895825)) (.leaf (523255,80,14800268)))))) (.node 236 (.node 233 (.node 232 (.leaf (1047543,81,15067906)) (.leaf (523231,80,14789537))) (.node 234 (.leaf (523263,81,14965146)) (.node 235 (.leaf (1014495,79,14870737)) (.leaf (1047263,80,14891793))))) (.node 239 (.node 237 (.leaf (1014751,80,14805665)) (.node 238 (.leaf (1047519,81,15064336)) (.leaf (1014527,80,14804300)))) (.node 240 (.leaf (1047295,81,15063426)) (.node 241 (.leaf (1014783,81,14969626)) (.leaf (1047551,83,15559432))))))) (.node 253 (.node 247 (.node 244 (.node 243 (.leaf (1046271,82,14899353)) (.leaf (1035999,79,14898849))) (.node 245 (.leaf (1040095,80,14890281)) (.node 246 (.leaf (1036031,80,14804237)) (.leaf (1040127,81,15061410))))) (.node 250 (.node 248 (.leaf (1044191,80,14891149)) (.node 249 (.leaf (1015519,80,14890092)) (.leaf (1048287,81,15141602)))) (.node 251 (.leaf (978687,80,14789901)) (.node 252 (.leaf (1044223,81,15063174)) (.leaf (950015,80,14787381)))))) (.node 258 (.node 255 (.node 254 (.leaf (1015551,81,15118614)) (.leaf (982783,81,15043490))) (.node 256 (.leaf (1048319,83,15672132)) (.node 257 (.leaf (1015791,82,14870737)) (.leaf (950269,80,14796145))))) (.node 261 (.node 259 (.leaf (950271,81,14957362)) (.node 260 (.leaf (884701,79,14838481)) (.leaf (1015773,80,14870177)))) (.node 262 (.leaf (884733,80,14796110)) (.node 263 (.leaf (1015805,81,15130906)) (.leaf (884703,80,14788718))))))))) (.node 308 (.node 286 (.node 275 (.node 269 (.node 266 (.node 265 (.leaf (1015775,81,15120434)) (.leaf (884735,81,14957334))) (.node 267 (.leaf (1015807,83,15557164)) (.node 268 (.leaf (983031,82,14887705)) (.leaf (978429,79,14891793))))) (.node 272 (.node 270 (.leaf (982525,80,14824817)) (.node 271 (.leaf (978941,80,14798161)) (.leaf (983037,81,15124368)))) (.node 273 (.leaf (978431,80,14789733)) (.node 274 (.leaf (982527,81,15043378)) (.leaf (978943,81,14957922)))))) (.node 280 (.node 277 (.node 276 (.leaf (983039,83,15539552)) (.leaf (917469,80,14859537))) (.node 278 (.leaf (520157,79,14826385)) (.node 279 (.leaf (1044445,80,14863569)) (.leaf (524253,80,14857521))))) (.node 283 (.node 281 (.leaf (1048541,81,15161104)) (.node 282 (.leaf (1043965,80,14898828)) (.leaf (520189,80,14800142)))) (.node 284 (.leaf (1044477,81,15132418)) (.node 285 (.leaf (522237,80,14800177)) (.leaf (524285,81,15122842))))))) (.node 297 (.node 291 (.node 288 (.node 287 (.leaf (914941,79,14895825)) (.leaf (1046013,80,14898849))) (.node 289 (.leaf (916989,80,14824782)) (.node 290 (.leaf (1048061,81,15159578)) (.leaf (915453,80,14802193))))) (.node 294 (.node 292 (.leaf (1046525,81,15132432)) (.node 293 (.leaf (917501,81,15124354)) (.leaf (1048573,83,15684872)))) (.node 295 (.leaf (1036255,80,14805161)) (.node 296 (.leaf (520159,80,14789222)) (.leaf (1044447,81,15121442)))))) (.node 302 (.node 299 (.node 298 (.leaf (524247,80,14857332)) (.leaf (524255,81,15108338))) (.node 300 (.leaf (909271,79,14802081)) (.node 301 (.leaf (1040343,80,14837417)) (.leaf (917463,80,14826637))))) (.node 305 (.node 303 (.leaf (1048535,81,15153698)) (.node 304 (.leaf (909279,80,14789033)) (.leaf (1040351,81,15120560)))) (.node 306 (.leaf (917471,81,15109346)) (.node 307 (.leaf (1048543,83,15673952)) (.leaf (520175,80,14789390)))))))) (.node 330 (.node 319 (.node 313 (.node 310 (.node 309 (.leaf (520191,81,14964950)) (.leaf (1035759,79,14898961))) (.node 311 (.leaf (1043951,80,14891660)) (.node 312 (.leaf (1036271,80,14805329)) (.leaf (1044463,81,15121666))))) (.node 316 (.node 314 (.leaf (1035775,80,14804069)) (.node 315 (.leaf (1043967,81,15063062)) (.leaf (1036287,81,14968674)))) (.node 317 (.leaf (1044479,83,15559236)) (.node 318 (.leaf (522215,79,14801297)) (.leaf (524263,80,14857612)))))) (.node 324 (.node 321 (.node 320 (.leaf (522231,80,14799988)) (.leaf (524279,81,15122646))) (.node 322 (.leaf (522223,80,14789425)) (.node 323 (.leaf (524271,81,15108506)) (.leaf (522239,81,14964978))))) (.node 327 (.node 325 (.leaf (524287,83,15536556)) (.node 326 (.leaf (1046503,80,14838481)) (.leaf (1040359,80,14837585)))) (.node 328 (.leaf (1048551,81,15153922)) (.node 329 (.leaf (915447,80,14797965)) (.leaf (1046519,81,15067682))))))) (.node 341 (.node 335 (.node 332 (.node 331 (.leaf (909303,80,14796173)) (.leaf (1040375,81,15065442))) (.node 333 (.leaf (917495,81,15124102)) (.node 334 (.leaf (1048567,83,15684676)) (.leaf (1045999,80,14891681))))) (.node 338 (.node 336 (.leaf (1046511,81,15121680)) (.node 337 (.leaf (1039855,80,14890337)) (.leaf (1048047,81,15141658)))) (.node 339 (.leaf (1040367,81,15120784)) (.node 340 (.leaf (1048559,83,15674120)) (.leaf (914943,80,14789740)))))) (.node 346 (.node 343 (.node 342 (.leaf (1046015,81,15063090)) (.leaf (915455,81,14965986))) (.node 344 (.leaf (1046527,83,15559264)) (.node 345 (.leaf (908799,80,14787500)) (.leaf (1039871,81,15061298))))) (.node 349 (.node 347 (.leaf (916991,81,15043350)) (.node 348 (.leaf (1048063,83,15671852)) (.leaf (909311,81,14964642)))) (.node 350 (.leaf (1040383,83,15557472)) (.node 351 (.leaf (917503,83,15539524)) (.leaf (1048575,84,16434824)))))))))))

noncomputable def models (i : Fin 352) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 352) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 352) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 35, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (6 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 35, (6 : Fin 8) ∈ U i → ∃ j : Fin 20, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R4C17

/- Source: MatroidCatalogue/Cases/N7R4C17Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R4C17


noncomputable def certificates_0 : List (Origin 35 352 × List Sat.Literal) :=
  [((.fixed 0),[(.pos 0)]),
   ((.fixed 1),[(.pos 1)]),
   ((.fixed 2),[(.pos 2)]),
   ((.fixed 3),[(.pos 3)]),
   ((.fixed 4),[(.pos 4)]),
   ((.fixed 5),[(.pos 5)]),
   ((.fixed 6),[(.pos 6)]),
   ((.fixed 7),[(.pos 7)]),
   ((.fixed 8),[(.pos 8)]),
   ((.fixed 9),[(.pos 9)]),
   ((.fixed 10),[(.pos 10)]),
   ((.fixed 11),[(.pos 11)]),
   ((.fixed 12),[(.pos 12)]),
   ((.fixed 13),[(.pos 13)]),
   ((.fixed 14),[(.pos 14)]),
   ((.exchange 15 3 1),[(.neg 15),(.neg 3),(.pos 17),(.pos 20)]),
   ((.exchange 15 4 0),[(.neg 15),(.neg 4),(.pos 18),(.pos 21)]),
   ((.exchange 15 7 1),[(.neg 15),(.neg 7),(.pos 17),(.pos 26)]),
   ((.exchange 15 8 0),[(.neg 15),(.neg 8),(.pos 18),(.pos 27)]),
   ((.exchange 15 9 2),[(.neg 15),(.neg 9),(.pos 19),(.pos 25)]),
   ((.exchange 15 10 1),[(.neg 15),(.neg 10),(.pos 20),(.pos 26)]),
   ((.exchange 15 11 0),[(.neg 15),(.neg 11),(.pos 21),(.pos 27)]),
   ((.exchange 15 23 0),[(.neg 23),(.neg 15),(.pos 18),(.pos 21)]),
   ((.exchange 15 24 0),[(.neg 24),(.neg 15),(.pos 18),(.pos 21)]),
   ((.exchange 15 24 1),[(.neg 24),(.neg 15),(.pos 17),(.pos 20)]),
   ((.exchange 15 29 0),[(.neg 29),(.neg 15),(.pos 18),(.pos 27)]),
   ((.exchange 15 31 1),[(.neg 31),(.neg 15),(.pos 20),(.pos 26)]),
   ((.exchange 15 32 0),[(.neg 32),(.neg 15),(.pos 21),(.pos 27)]),
   ((.exchange 15 33 0),[(.neg 33),(.neg 15),(.pos 21),(.pos 27)]),
   ((.exchange 15 33 1),[(.neg 33),(.neg 15),(.pos 20),(.pos 26)]),
   ((.exchange 16 3 1),[(.neg 16),(.neg 3),(.pos 17),(.pos 22)]),
   ((.exchange 16 4 0),[(.neg 16),(.neg 4),(.pos 18),(.pos 23)]),
   ((.exchange 16 5 3),[(.neg 16),(.neg 5),(.pos 15),(.pos 25)]),
   ((.exchange 16 7 1),[(.neg 16),(.neg 7),(.pos 17),(.pos 28)]),
   ((.exchange 16 8 0),[(.neg 16),(.neg 8),(.pos 18),(.pos 29)]),
   ((.exchange 16 9 3),[(.neg 16),(.neg 9),(.pos 19),(.pos 25)]),
   ((.exchange 16 12 1),[(.neg 16),(.neg 12),(.pos 22),(.pos 28)]),
   ((.exchange 16 13 0),[(.neg 16),(.neg 13),(.pos 23),(.pos 29)]),
   ((.exchange 16 21 0),[(.neg 21),(.neg 16),(.pos 18),(.pos 23)]),
   ((.exchange 16 26 1),[(.neg 26),(.neg 16),(.pos 17),(.pos 28)]),
   ((.exchange 16 31 1),[(.neg 31),(.neg 16),(.pos 22),(.pos 28)]),
   ((.exchange 16 32 0),[(.neg 32),(.neg 16),(.pos 23),(.pos 29)]),
   ((.exchange 17 1 3),[(.neg 17),(.neg 1),(.pos 15),(.pos 20)]),
   ((.exchange 17 2 2),[(.neg 17),(.neg 2),(.pos 16),(.pos 22)]),
   ((.exchange 17 4 0),[(.neg 17),(.neg 4),(.pos 18),(.pos 24)]),
   ((.exchange 17 5 3),[(.neg 17),(.neg 5),(.pos 15),(.pos 26)]),
   ((.exchange 17 8 0),[(.neg 17),(.neg 8),(.pos 18),(.pos 30)]),
   ((.exchange 17 10 3),[(.neg 17),(.neg 10),(.pos 20),(.pos 26)]),
   ((.exchange 17 14 0),[(.neg 17),(.neg 14),(.pos 24),(.pos 30)]),
   ((.exchange 17 19 2),[(.neg 19),(.neg 17),(.pos 16),(.pos 22)]),
   ((.exchange 17 19 3),[(.neg 19),(.neg 17),(.pos 15),(.pos 20)]),
   ((.exchange 17 21 0),[(.neg 21),(.neg 17),(.pos 18),(.pos 24)]),
   ((.exchange 17 23 0),[(.neg 23),(.neg 17),(.pos 18),(.pos 24)]),
   ((.exchange 17 25 2),[(.neg 25),(.neg 17),(.pos 16),(.pos 28)]),
   ((.exchange 17 25 3),[(.neg 25),(.neg 17),(.pos 15),(.pos 26)]),
   ((.exchange 17 29 0),[(.neg 29),(.neg 17),(.pos 18),(.pos 30)]),
   ((.exchange 17 31 2),[(.neg 31),(.neg 17),(.pos 22),(.pos 28)]),
   ((.exchange 17 31 3),[(.neg 31),(.neg 17),(.pos 20),(.pos 26)]),
   ((.exchange 17 34 0),[(.neg 34),(.neg 17),(.pos 24),(.pos 30)]),
   ((.exchange 18 3 1),[(.neg 18),(.neg 3),(.pos 17),(.pos 24)]),
   ((.exchange 18 5 3),[(.neg 18),(.neg 5),(.pos 15),(.pos 27)]),
   ((.exchange 18 6 2),[(.neg 18),(.neg 6),(.pos 16),(.pos 29)]),
   ((.exchange 18 7 1),[(.neg 18),(.neg 7),(.pos 17),(.pos 30)]),
   ((.exchange 18 11 3),[(.neg 18),(.neg 11),(.pos 21),(.pos 27)]),
   ((.exchange 18 13 2),[(.neg 18),(.neg 13),(.pos 23),(.pos 29)]),
   ((.exchange 18 14 1),[(.neg 18),(.neg 14),(.pos 24),(.pos 30)]),
   ((.exchange 18 19 2),[(.neg 19),(.neg 18),(.pos 16),(.pos 23)]),
   ((.exchange 18 19 3),[(.neg 19),(.neg 18),(.pos 15),(.pos 21)]),
   ((.exchange 18 20 1),[(.neg 20),(.neg 18),(.pos 17),(.pos 24)]),
   ((.exchange 18 22 1),[(.neg 22),(.neg 18),(.pos 17),(.pos 24)]),
   ((.exchange 18 25 3),[(.neg 25),(.neg 18),(.pos 15),(.pos 27)]),
   ((.exchange 18 26 1),[(.neg 26),(.neg 18),(.pos 17),(.pos 30)]),
   ((.exchange 18 28 1),[(.neg 28),(.neg 18),(.pos 17),(.pos 30)]),
   ((.exchange 18 28 2),[(.neg 28),(.neg 18),(.pos 16),(.pos 29)]),
   ((.exchange 18 32 3),[(.neg 32),(.neg 18),(.pos 21),(.pos 27)]),
   ((.exchange 18 33 1),[(.neg 33),(.neg 18),(.pos 24),(.pos 30)]),
   ((.exchange 18 34 2),[(.neg 34),(.neg 18),(.pos 23),(.pos 29)]),
   ((.exchange 19 0 4),[(.neg 19),(.neg 0),(.pos 15),(.pos 16)]),
   ((.exchange 19 4 0),[(.neg 19),(.neg 4),(.pos 21),(.pos 23)]),
   ((.exchange 19 5 4),[(.neg 19),(.neg 5),(.pos 15),(.pos 25)]),
   ((.exchange 19 6 4),[(.neg 19),(.neg 6),(.pos 16),(.pos 25)]),
   ((.exchange 19 10 1),[(.neg 19),(.neg 10),(.pos 20),(.pos 31)]),
   ((.exchange 19 11 0),[(.neg 19),(.neg 11),(.pos 21),(.pos 32)]),
   ((.exchange 19 12 1),[(.neg 19),(.neg 12),(.pos 22),(.pos 31)]),
   ((.exchange 19 13 0),[(.neg 19),(.neg 13),(.pos 23),(.pos 32)]),
   ((.exchange 19 29 4),[(.neg 29),(.neg 19),(.pos 16),(.pos 25)]),
   ((.exchange 19 34 0),[(.neg 34),(.neg 19),(.pos 23),(.pos 32)]),
   ((.exchange 20 0 4),[(.neg 20),(.neg 0),(.pos 15),(.pos 17)]),
   ((.exchange 20 2 2),[(.neg 20),(.neg 2),(.pos 19),(.pos 22)]),
   ((.exchange 20 4 0),[(.neg 20),(.neg 4),(.pos 21),(.pos 24)]),
   ((.exchange 20 5 4),[(.neg 20),(.neg 5),(.pos 15),(.pos 26)]),
   ((.exchange 20 7 4),[(.neg 20),(.neg 7),(.pos 17),(.pos 26)]),
   ((.exchange 20 9 2),[(.neg 20),(.neg 9),(.pos 19),(.pos 31)]),
   ((.exchange 20 11 0),[(.neg 20),(.neg 11),(.pos 21),(.pos 33)]),
   ((.exchange 20 14 0),[(.neg 20),(.neg 14),(.pos 24),(.pos 33)]),
   ((.exchange 20 16 4),[(.neg 20),(.neg 16),(.pos 15),(.pos 17)]),
   ((.exchange 20 23 0),[(.neg 23),(.neg 20),(.pos 21),(.pos 24)]),
   ((.exchange 20 25 4),[(.neg 25),(.neg 20),(.pos 15),(.pos 26)]),
   ((.exchange 20 28 4),[(.neg 28),(.neg 20),(.pos 17),(.pos 26)]),
   ((.exchange 20 30 4),[(.neg 30),(.neg 20),(.pos 17),(.pos 26)]),
   ((.exchange 20 34 0),[(.neg 34),(.neg 20),(.pos 24),(.pos 33)]),
   ((.exchange 21 0 4),[(.neg 21),(.neg 0),(.pos 15),(.pos 18)]),
   ((.exchange 21 2 2),[(.neg 21),(.neg 2),(.pos 19),(.pos 23)]),
   ((.exchange 21 3 1),[(.neg 21),(.neg 3),(.pos 20),(.pos 24)]),
   ((.exchange 21 5 4),[(.neg 21),(.neg 5),(.pos 15),(.pos 27)]),
   ((.exchange 21 9 2),[(.neg 21),(.neg 9),(.pos 19),(.pos 32)]),
   ((.exchange 21 10 1),[(.neg 21),(.neg 10),(.pos 20),(.pos 33)]),
   ((.exchange 21 14 1),[(.neg 21),(.neg 14),(.pos 24),(.pos 33)]),
   ((.exchange 21 16 4),[(.neg 21),(.neg 16),(.pos 15),(.pos 18)]),
   ((.exchange 21 25 4),[(.neg 25),(.neg 21),(.pos 15),(.pos 27)]),
   ((.exchange 21 28 4),[(.neg 28),(.neg 21),(.pos 15),(.pos 18),(.pos 27)]),
   ((.exchange 21 29 2),[(.neg 29),(.neg 21),(.pos 23),(.pos 32)]),
   ((.exchange 21 30 1),[(.neg 30),(.neg 21),(.pos 24),(.pos 33)]),
   ((.exchange 21 34 1),[(.neg 34),(.neg 21),(.pos 24),(.pos 33)]),
   ((.exchange 22 0 4),[(.neg 22),(.neg 0),(.pos 16),(.pos 17)]),
   ((.exchange 22 1 3),[(.neg 22),(.neg 1),(.pos 19),(.pos 20)]),
   ((.exchange 22 4 0),[(.neg 22),(.neg 4),(.pos 23),(.pos 24)]),
   ((.exchange 22 6 4),[(.neg 22),(.neg 6),(.pos 16),(.pos 28)]),
   ((.exchange 22 7 4),[(.neg 22),(.neg 7),(.pos 17),(.pos 28)]),
   ((.exchange 22 8 0),[(.neg 22),(.neg 8),(.pos 23),(.pos 24),(.pos 34)]),
   ((.exchange 22 13 0),[(.neg 22),(.neg 13),(.pos 23),(.pos 34)]),
   ((.exchange 22 14 0),[(.neg 22),(.neg 14),(.pos 24),(.pos 34)]),
   ((.exchange 22 15 4),[(.neg 22),(.neg 15),(.pos 16),(.pos 17)]),
   ((.exchange 22 18 0),[(.neg 22),(.neg 18),(.pos 23),(.pos 24)]),
   ((.exchange 22 21 0),[(.neg 22),(.neg 21),(.pos 23),(.pos 24)]),
   ((.exchange 22 25 4),[(.neg 25),(.neg 22),(.pos 16),(.pos 28)]),
   ((.exchange 22 26 4),[(.neg 26),(.neg 22),(.pos 17),(.pos 28)]),
   ((.exchange 22 29 4),[(.neg 29),(.neg 22),(.pos 16),(.pos 28)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_1 : List (Origin 35 352 × List Sat.Literal) :=
  [((.exchange 22 30 4),[(.neg 30),(.neg 22),(.pos 17),(.pos 28)]),
   ((.exchange 23 0 4),[(.neg 23),(.neg 0),(.pos 16),(.pos 18)]),
   ((.exchange 23 1 3),[(.neg 23),(.neg 1),(.pos 19),(.pos 21)]),
   ((.exchange 23 3 1),[(.neg 23),(.neg 3),(.pos 22),(.pos 24)]),
   ((.exchange 23 6 4),[(.neg 23),(.neg 6),(.pos 16),(.pos 29)]),
   ((.exchange 23 8 4),[(.neg 23),(.neg 8),(.pos 18),(.pos 29)]),
   ((.exchange 23 9 3),[(.neg 23),(.neg 9),(.pos 19),(.pos 32)]),
   ((.exchange 23 11 3),[(.neg 23),(.neg 11),(.pos 21),(.pos 32)]),
   ((.exchange 23 12 1),[(.neg 23),(.neg 12),(.pos 22),(.pos 34)]),
   ((.exchange 23 14 1),[(.neg 23),(.neg 14),(.pos 24),(.pos 34)]),
   ((.exchange 23 17 1),[(.neg 23),(.neg 17),(.pos 22),(.pos 24)]),
   ((.exchange 23 20 3),[(.neg 23),(.neg 20),(.pos 19),(.pos 21)]),
   ((.exchange 23 28 1),[(.neg 28),(.neg 23),(.pos 22),(.pos 34)]),
   ((.exchange 23 28 4),[(.neg 28),(.neg 23),(.pos 16),(.pos 29)]),
   ((.exchange 23 31 1),[(.neg 31),(.neg 23),(.pos 22),(.pos 34)]),
   ((.exchange 23 33 3),[(.neg 33),(.neg 23),(.pos 21),(.pos 32)]),
   ((.exchange 24 0 4),[(.neg 24),(.neg 0),(.pos 17),(.pos 18)]),
   ((.exchange 24 1 3),[(.neg 24),(.neg 1),(.pos 20),(.pos 21)]),
   ((.exchange 24 2 2),[(.neg 24),(.neg 2),(.pos 22),(.pos 23)]),
   ((.exchange 24 7 4),[(.neg 24),(.neg 7),(.pos 17),(.pos 30)]),
   ((.exchange 24 8 4),[(.neg 24),(.neg 8),(.pos 18),(.pos 30)]),
   ((.exchange 24 10 3),[(.neg 24),(.neg 10),(.pos 20),(.pos 33)]),
   ((.exchange 24 11 3),[(.neg 24),(.neg 11),(.pos 21),(.pos 33)]),
   ((.exchange 24 12 2),[(.neg 24),(.neg 12),(.pos 22),(.pos 34)]),
   ((.exchange 24 13 2),[(.neg 24),(.neg 13),(.pos 23),(.pos 34)]),
   ((.exchange 24 15 4),[(.neg 24),(.neg 15),(.pos 17),(.pos 18)]),
   ((.exchange 24 16 2),[(.neg 24),(.neg 16),(.pos 22),(.pos 23)]),
   ((.exchange 24 19 2),[(.neg 24),(.neg 19),(.pos 22),(.pos 23)]),
   ((.exchange 24 27 4),[(.neg 27),(.neg 24),(.pos 18),(.pos 30)]),
   ((.exchange 24 28 2),[(.neg 28),(.neg 24),(.pos 22),(.pos 34)]),
   ((.exchange 24 32 2),[(.neg 32),(.neg 24),(.pos 23),(.pos 34)]),
   ((.exchange 24 32 3),[(.neg 32),(.neg 24),(.pos 21),(.pos 33)]),
   ((.exchange 25 0 5),[(.neg 25),(.neg 0),(.pos 15),(.pos 16)]),
   ((.exchange 25 1 5),[(.neg 25),(.neg 1),(.pos 15),(.pos 19)]),
   ((.exchange 25 2 5),[(.neg 25),(.neg 2),(.pos 16),(.pos 19)]),
   ((.exchange 25 7 1),[(.neg 25),(.neg 7),(.pos 26),(.pos 28)]),
   ((.exchange 25 8 0),[(.neg 25),(.neg 8),(.pos 27),(.pos 29)]),
   ((.exchange 25 10 1),[(.neg 25),(.neg 10),(.pos 26),(.pos 31)]),
   ((.exchange 25 11 0),[(.neg 25),(.neg 11),(.pos 27),(.pos 32)]),
   ((.exchange 25 12 1),[(.neg 25),(.neg 12),(.pos 28),(.pos 31)]),
   ((.exchange 25 13 0),[(.neg 25),(.neg 13),(.pos 29),(.pos 32)]),
   ((.exchange 25 17 1),[(.neg 25),(.neg 17),(.pos 26),(.pos 28)]),
   ((.exchange 25 18 0),[(.neg 25),(.neg 18),(.pos 27),(.pos 29)]),
   ((.exchange 25 20 5),[(.neg 25),(.neg 20),(.pos 15),(.pos 19)]),
   ((.exchange 25 21 0),[(.neg 25),(.neg 21),(.pos 27),(.pos 32)]),
   ((.exchange 25 22 5),[(.neg 25),(.neg 22),(.pos 16),(.pos 19)]),
   ((.exchange 25 23 0),[(.neg 25),(.neg 23),(.pos 29),(.pos 32)]),
   ((.exchange 25 30 0),[(.neg 30),(.neg 25),(.pos 27),(.pos 29)]),
   ((.exchange 25 30 1),[(.neg 30),(.neg 25),(.pos 26),(.pos 28)]),
   ((.exchange 25 33 1),[(.neg 33),(.neg 25),(.pos 26),(.pos 31)]),
   ((.exchange 25 34 0),[(.neg 34),(.neg 25),(.pos 29),(.pos 32)]),
   ((.exchange 25 34 1),[(.neg 34),(.neg 25),(.pos 28),(.pos 31)]),
   ((.exchange 26 0 5),[(.neg 26),(.neg 0),(.pos 15),(.pos 17)]),
   ((.exchange 26 9 2),[(.neg 26),(.neg 9),(.pos 25),(.pos 31)]),
   ((.exchange 26 11 0),[(.neg 26),(.neg 11),(.pos 27),(.pos 33)]),
   ((.exchange 26 12 2),[(.neg 26),(.neg 12),(.pos 28),(.pos 31)]),
   ((.exchange 26 14 0),[(.neg 26),(.neg 14),(.pos 30),(.pos 33)]),
   ((.exchange 26 18 0),[(.neg 26),(.neg 18),(.pos 27),(.pos 30)]),
   ((.exchange 26 19 5),[(.neg 26),(.neg 19),(.pos 15),(.pos 20)]),
   ((.exchange 26 21 0),[(.neg 26),(.neg 21),(.pos 27),(.pos 33)]),
   ((.exchange 26 22 5),[(.neg 26),(.neg 22),(.pos 17),(.pos 20)]),
   ((.exchange 26 24 0),[(.neg 26),(.neg 24),(.pos 30),(.pos 33)]),
   ((.exchange 26 32 0),[(.neg 32),(.neg 26),(.pos 27),(.pos 33)]),
   ((.exchange 26 34 0),[(.neg 34),(.neg 26),(.pos 30),(.pos 33)]),
   ((.exchange 26 34 2),[(.neg 34),(.neg 26),(.pos 28),(.pos 31)]),
   ((.exchange 27 1 5),[(.neg 27),(.neg 1),(.pos 15),(.pos 21)]),
   ((.exchange 27 4 5),[(.neg 27),(.neg 4),(.pos 18),(.pos 21)]),
   ((.exchange 27 7 1),[(.neg 27),(.neg 7),(.pos 26),(.pos 30)]),
   ((.exchange 27 9 2),[(.neg 27),(.neg 9),(.pos 25),(.pos 32)]),
   ((.exchange 27 10 1),[(.neg 27),(.neg 10),(.pos 26),(.pos 33)]),
   ((.exchange 27 13 2),[(.neg 27),(.neg 13),(.pos 29),(.pos 32)]),
   ((.exchange 27 14 1),[(.neg 27),(.neg 14),(.pos 30),(.pos 33)]),
   ((.exchange 27 16 5),[(.neg 27),(.neg 16),(.pos 15),(.pos 18)]),
   ((.exchange 27 17 1),[(.neg 27),(.neg 17),(.pos 26),(.pos 30)]),
   ((.exchange 27 19 5),[(.neg 27),(.neg 19),(.pos 15),(.pos 21)]),
   ((.exchange 27 20 1),[(.neg 27),(.neg 20),(.pos 26),(.pos 33)]),
   ((.exchange 27 20 5),[(.neg 27),(.neg 20),(.pos 15),(.pos 21)]),
   ((.exchange 27 23 5),[(.neg 27),(.neg 23),(.pos 18),(.pos 21)]),
   ((.exchange 27 24 1),[(.neg 27),(.neg 24),(.pos 30),(.pos 33)]),
   ((.exchange 27 28 1),[(.neg 28),(.neg 27),(.pos 26),(.pos 30)]),
   ((.exchange 27 28 2),[(.neg 28),(.neg 27),(.pos 25),(.pos 29)]),
   ((.exchange 27 31 1),[(.neg 31),(.neg 27),(.pos 26),(.pos 33)]),
   ((.exchange 27 34 1),[(.neg 34),(.neg 27),(.pos 30),(.pos 33)]),
   ((.exchange 28 1 3),[(.neg 28),(.neg 1),(.pos 25),(.pos 26),(.pos 31)]),
   ((.exchange 28 2 5),[(.neg 28),(.neg 2),(.pos 16),(.pos 22)]),
   ((.exchange 28 3 5),[(.neg 28),(.neg 3),(.pos 17),(.pos 22)]),
   ((.exchange 28 5 3),[(.neg 28),(.neg 5),(.pos 25),(.pos 26)]),
   ((.exchange 28 8 0),[(.neg 28),(.neg 8),(.pos 29),(.pos 30)]),
   ((.exchange 28 9 3),[(.neg 28),(.neg 9),(.pos 25),(.pos 31)]),
   ((.exchange 28 10 3),[(.neg 28),(.neg 10),(.pos 26),(.pos 31)]),
   ((.exchange 28 13 0),[(.neg 28),(.neg 13),(.pos 29),(.pos 34)]),
   ((.exchange 28 14 0),[(.neg 28),(.neg 14),(.pos 30),(.pos 34)]),
   ((.exchange 28 18 0),[(.neg 28),(.neg 18),(.pos 29),(.pos 30)]),
   ((.exchange 28 18 5),[(.neg 28),(.neg 18),(.pos 16),(.pos 17)]),
   ((.exchange 28 19 3),[(.neg 28),(.neg 19),(.pos 25),(.pos 31)]),
   ((.exchange 28 19 5),[(.neg 28),(.neg 19),(.pos 16),(.pos 22)]),
   ((.exchange 28 20 3),[(.neg 28),(.neg 20),(.pos 26),(.pos 31)]),
   ((.exchange 28 23 5),[(.neg 28),(.neg 23),(.pos 16),(.pos 22)]),
   ((.exchange 28 27 3),[(.neg 28),(.neg 27),(.pos 25),(.pos 26)]),
   ((.exchange 28 33 0),[(.neg 33),(.neg 28),(.pos 30),(.pos 34)]),
   ((.exchange 28 33 3),[(.neg 33),(.neg 28),(.pos 26),(.pos 31)]),
   ((.exchange 29 0 5),[(.neg 29),(.neg 0),(.pos 16),(.pos 18)]),
   ((.exchange 29 4 5),[(.neg 29),(.neg 4),(.pos 18),(.pos 23)]),
   ((.exchange 29 5 3),[(.neg 29),(.neg 5),(.pos 25),(.pos 27)]),
   ((.exchange 29 7 1),[(.neg 29),(.neg 7),(.pos 28),(.pos 30)]),
   ((.exchange 29 9 3),[(.neg 29),(.neg 9),(.pos 25),(.pos 32)]),
   ((.exchange 29 12 1),[(.neg 29),(.neg 12),(.pos 28),(.pos 34)]),
   ((.exchange 29 15 5),[(.neg 29),(.neg 15),(.pos 16),(.pos 18)]),
   ((.exchange 29 17 5),[(.neg 29),(.neg 17),(.pos 16),(.pos 18)]),
   ((.exchange 29 19 5),[(.neg 29),(.neg 19),(.pos 16),(.pos 23)]),
   ((.exchange 29 21 3),[(.neg 29),(.neg 21),(.pos 27),(.pos 32)]),
   ((.exchange 29 21 5),[(.neg 29),(.neg 21),(.pos 18),(.pos 23)]),
   ((.exchange 29 22 1),[(.neg 29),(.neg 22),(.pos 28),(.pos 34)]),
   ((.exchange 29 22 5),[(.neg 29),(.neg 22),(.pos 16),(.pos 23)]),
   ((.exchange 29 26 1),[(.neg 29),(.neg 26),(.pos 28),(.pos 30)]),
   ((.exchange 29 26 3),[(.neg 29),(.neg 26),(.pos 25),(.pos 27)]),
   ((.exchange 29 31 3),[(.neg 31),(.neg 29),(.pos 25),(.pos 32)]),
   ((.exchange 29 33 1),[(.neg 33),(.neg 29),(.pos 30),(.pos 34)]),
   ((.exchange 30 0 5),[(.neg 30),(.neg 0),(.pos 17),(.pos 18)]),
   ((.exchange 30 3 5),[(.neg 30),(.neg 3),(.pos 17),(.pos 24)]),
   ((.exchange 30 4 5),[(.neg 30),(.neg 4),(.pos 18),(.pos 24)]),
   ((.exchange 30 5 3),[(.neg 30),(.neg 5),(.pos 26),(.pos 27)]),
   ((.exchange 30 6 2),[(.neg 30),(.neg 6),(.pos 28),(.pos 29)]),
   ((.exchange 30 10 3),[(.neg 30),(.neg 10),(.pos 26),(.pos 33)]),
   ((.exchange 30 11 3),[(.neg 30),(.neg 11),(.pos 27),(.pos 33)]),
   ((.exchange 30 12 2),[(.neg 30),(.neg 12),(.pos 28),(.pos 34)]),
   ((.exchange 30 13 2),[(.neg 30),(.neg 13),(.pos 29),(.pos 34)]),
   ((.exchange 30 20 3),[(.neg 30),(.neg 20),(.pos 26),(.pos 33)])]

theorem certificates_1_valid : ∀ oc ∈ certificates_1,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_2 : List (Origin 35 352 × List Sat.Literal) :=
  [((.exchange 30 21 3),[(.neg 30),(.neg 21),(.pos 27),(.pos 33)]),
   ((.exchange 30 21 5),[(.neg 30),(.neg 21),(.pos 18),(.pos 24)]),
   ((.exchange 30 22 2),[(.neg 30),(.neg 22),(.pos 28),(.pos 34)]),
   ((.exchange 30 22 5),[(.neg 30),(.neg 22),(.pos 17),(.pos 24)]),
   ((.exchange 30 23 2),[(.neg 30),(.neg 23),(.pos 29),(.pos 34)]),
   ((.exchange 30 23 5),[(.neg 30),(.neg 23),(.pos 18),(.pos 24)]),
   ((.exchange 30 25 2),[(.neg 30),(.neg 25),(.pos 28),(.pos 29)]),
   ((.exchange 30 25 3),[(.neg 30),(.neg 25),(.pos 26),(.pos 27)]),
   ((.exchange 30 31 3),[(.neg 31),(.neg 30),(.pos 26),(.pos 33)]),
   ((.exchange 30 32 3),[(.neg 32),(.neg 30),(.pos 27),(.pos 33)]),
   ((.exchange 31 0 5),[(.neg 31),(.neg 0),(.pos 19),(.pos 20),(.pos 22)]),
   ((.exchange 31 3 5),[(.neg 31),(.neg 3),(.pos 20),(.pos 22)]),
   ((.exchange 31 5 4),[(.neg 31),(.neg 5),(.pos 25),(.pos 26)]),
   ((.exchange 31 6 4),[(.neg 31),(.neg 6),(.pos 25),(.pos 28)]),
   ((.exchange 31 11 0),[(.neg 31),(.neg 11),(.pos 32),(.pos 33)]),
   ((.exchange 31 13 0),[(.neg 31),(.neg 13),(.pos 32),(.pos 34)]),
   ((.exchange 31 14 0),[(.neg 31),(.neg 14),(.pos 33),(.pos 34)]),
   ((.exchange 31 15 4),[(.neg 31),(.neg 15),(.pos 25),(.pos 26)]),
   ((.exchange 31 16 4),[(.neg 31),(.neg 16),(.pos 25),(.pos 28)]),
   ((.exchange 31 24 0),[(.neg 31),(.neg 24),(.pos 33),(.pos 34)]),
   ((.exchange 31 27 0),[(.neg 31),(.neg 27),(.pos 32),(.pos 33)]),
   ((.exchange 31 29 4),[(.neg 31),(.neg 29),(.pos 25),(.pos 28)]),
   ((.exchange 31 30 4),[(.neg 31),(.neg 30),(.pos 26),(.pos 28)]),
   ((.exchange 32 1 5),[(.neg 32),(.neg 1),(.pos 19),(.pos 21)]),
   ((.exchange 32 2 5),[(.neg 32),(.neg 2),(.pos 19),(.pos 23)]),
   ((.exchange 32 3 5),[(.neg 32),(.neg 3),(.pos 19),(.pos 21),(.pos 23)]),
   ((.exchange 32 4 5),[(.neg 32),(.neg 4),(.pos 21),(.pos 23)]),
   ((.exchange 32 5 4),[(.neg 32),(.neg 5),(.pos 25),(.pos 27)]),
   ((.exchange 32 8 4),[(.neg 32),(.neg 8),(.pos 27),(.pos 29)]),
   ((.exchange 32 10 1),[(.neg 32),(.neg 10),(.pos 31),(.pos 33)]),
   ((.exchange 32 12 1),[(.neg 32),(.neg 12),(.pos 31),(.pos 34)]),
   ((.exchange 32 14 1),[(.neg 32),(.neg 14),(.pos 33),(.pos 34)]),
   ((.exchange 32 15 4),[(.neg 32),(.neg 15),(.pos 25),(.pos 27)]),
   ((.exchange 32 15 5),[(.neg 32),(.neg 15),(.pos 19),(.pos 21)]),
   ((.exchange 32 16 4),[(.neg 32),(.neg 16),(.pos 25),(.pos 29)]),
   ((.exchange 32 16 5),[(.neg 32),(.neg 16),(.pos 19),(.pos 23)]),
   ((.exchange 32 18 4),[(.neg 32),(.neg 18),(.pos 27),(.pos 29)]),
   ((.exchange 32 20 1),[(.neg 32),(.neg 20),(.pos 31),(.pos 33)]),
   ((.exchange 32 22 1),[(.neg 32),(.neg 22),(.pos 31),(.pos 34)]),
   ((.exchange 32 28 1),[(.neg 32),(.neg 28),(.pos 31),(.pos 34)]),
   ((.exchange 32 28 4),[(.neg 32),(.neg 28),(.pos 25),(.pos 29)]),
   ((.exchange 32 30 4),[(.neg 32),(.neg 30),(.pos 27),(.pos 29)]),
   ((.exchange 33 1 5),[(.neg 33),(.neg 1),(.pos 20),(.pos 21)]),
   ((.exchange 33 3 5),[(.neg 33),(.neg 3),(.pos 20),(.pos 24)]),
   ((.exchange 33 5 4),[(.neg 33),(.neg 5),(.pos 26),(.pos 27)]),
   ((.exchange 33 7 4),[(.neg 33),(.neg 7),(.pos 26),(.pos 30)]),
   ((.exchange 33 8 4),[(.neg 33),(.neg 8),(.pos 27),(.pos 30)]),
   ((.exchange 33 9 2),[(.neg 33),(.neg 9),(.pos 31),(.pos 32)]),
   ((.exchange 33 12 2),[(.neg 33),(.neg 12),(.pos 31),(.pos 34)]),
   ((.exchange 33 15 5),[(.neg 33),(.neg 15),(.pos 20),(.pos 21)]),
   ((.exchange 33 18 4),[(.neg 33),(.neg 18),(.pos 27),(.pos 30)]),
   ((.exchange 33 18 5),[(.neg 33),(.neg 18),(.pos 21),(.pos 24)]),
   ((.exchange 33 19 2),[(.neg 33),(.neg 19),(.pos 31),(.pos 32)]),
   ((.exchange 33 19 5),[(.neg 33),(.neg 19),(.pos 20),(.pos 21)]),
   ((.exchange 33 22 5),[(.neg 33),(.neg 22),(.pos 20),(.pos 24)]),
   ((.exchange 33 23 5),[(.neg 33),(.neg 23),(.pos 21),(.pos 24)]),
   ((.exchange 33 25 4),[(.neg 33),(.neg 25),(.pos 26),(.pos 27)]),
   ((.exchange 33 29 2),[(.neg 33),(.neg 29),(.pos 32),(.pos 34)]),
   ((.exchange 33 29 4),[(.neg 33),(.neg 29),(.pos 27),(.pos 30)]),
   ((.exchange 34 2 5),[(.neg 34),(.neg 2),(.pos 22),(.pos 23)]),
   ((.exchange 34 3 5),[(.neg 34),(.neg 3),(.pos 22),(.pos 24)]),
   ((.exchange 34 6 4),[(.neg 34),(.neg 6),(.pos 28),(.pos 29)]),
   ((.exchange 34 7 4),[(.neg 34),(.neg 7),(.pos 28),(.pos 30)]),
   ((.exchange 34 8 4),[(.neg 34),(.neg 8),(.pos 29),(.pos 30)]),
   ((.exchange 34 9 3),[(.neg 34),(.neg 9),(.pos 31),(.pos 32)]),
   ((.exchange 34 10 3),[(.neg 34),(.neg 10),(.pos 31),(.pos 33)]),
   ((.exchange 34 11 3),[(.neg 34),(.neg 11),(.pos 32),(.pos 33)]),
   ((.exchange 34 16 4),[(.neg 34),(.neg 16),(.pos 28),(.pos 29)]),
   ((.exchange 34 16 5),[(.neg 34),(.neg 16),(.pos 22),(.pos 23)]),
   ((.exchange 34 17 5),[(.neg 34),(.neg 17),(.pos 22),(.pos 24)]),
   ((.exchange 34 19 3),[(.neg 34),(.neg 19),(.pos 31),(.pos 32)]),
   ((.exchange 34 20 3),[(.neg 34),(.neg 20),(.pos 31),(.pos 33)]),
   ((.exchange 34 21 3),[(.neg 34),(.neg 21),(.pos 32),(.pos 33)]),
   ((.exchange 34 21 5),[(.neg 34),(.neg 21),(.pos 23),(.pos 24)]),
   ((.exchange 34 25 3),[(.neg 34),(.neg 25),(.pos 31),(.pos 32)]),
   ((.exchange 34 25 4),[(.neg 34),(.neg 25),(.pos 28),(.pos 29)]),
   ((.exchange 34 26 3),[(.neg 34),(.neg 26),(.pos 31),(.pos 33)]),
   ((.exchange 34 26 4),[(.neg 34),(.neg 26),(.pos 28),(.pos 30)]),
   ((.exchange 34 27 4),[(.neg 34),(.neg 27),(.pos 29),(.pos 30)]),
   (.newPoint,[(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 19),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 30),(.pos 31),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 0),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 27),(.neg 24),(.neg 23),(.neg 21),(.neg 18),(.pos 15),(.pos 16),(.pos 17),(.pos 19),(.pos 20),(.pos 22),(.pos 25),(.pos 26),(.pos 28),(.pos 31)]),
   ((.excluded 1),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 28),(.neg 26),(.neg 24),(.neg 22),(.neg 20),(.neg 17),(.pos 15),(.pos 16),(.pos 18),(.pos 19),(.pos 21),(.pos 23),(.pos 25),(.pos 27),(.pos 29),(.pos 32)]),
   ((.excluded 2),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 17),(.pos 15),(.pos 16),(.pos 19),(.pos 24),(.pos 25)]),
   ((.excluded 3),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 17),(.pos 15),(.pos 16),(.pos 19),(.pos 25),(.pos 30)]),
   ((.excluded 4),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 17),(.pos 15),(.pos 16),(.pos 19),(.pos 25),(.pos 33)]),
   ((.excluded 5),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 17),(.pos 15),(.pos 16),(.pos 19),(.pos 25),(.pos 34)]),
   ((.excluded 6),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 17),(.pos 15),(.pos 16),(.pos 19),(.pos 25)]),
   ((.excluded 7),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.pos 15),(.pos 22),(.pos 23),(.pos 24),(.pos 34)]),
   ((.excluded 8),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 16),(.pos 15),(.pos 17),(.pos 20),(.pos 26),(.pos 34)]),
   ((.excluded 9),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.neg 17),(.neg 16),(.pos 15),(.pos 18),(.pos 21),(.pos 27),(.pos 34)]),
   ((.excluded 10),[(.neg 33),(.neg 32),(.neg 31),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.pos 15),(.pos 28),(.pos 29),(.pos 30),(.pos 34)]),
   ((.excluded 11),[(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.pos 15),(.pos 31),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 12),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.pos 15),(.pos 34)]),
   ((.excluded 13),[(.neg 34),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 25),(.neg 23),(.neg 22),(.neg 19),(.neg 16),(.pos 15),(.pos 17),(.pos 18),(.pos 20),(.pos 21),(.pos 24),(.pos 26),(.pos 27),(.pos 30),(.pos 33)]),
   ((.excluded 14),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 16),(.pos 15),(.pos 17),(.pos 20),(.pos 23),(.pos 26)]),
   ((.excluded 15),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 16),(.pos 15),(.pos 17),(.pos 20),(.pos 26),(.pos 29)]),
   ((.excluded 16),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 16),(.pos 15),(.pos 17),(.pos 20),(.pos 26),(.pos 32)]),
   ((.excluded 17),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 16),(.pos 15),(.pos 17),(.pos 20),(.pos 26)]),
   ((.excluded 18),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 20),(.neg 19),(.neg 17),(.neg 16),(.pos 15),(.pos 18),(.pos 21),(.pos 22),(.pos 27)]),
   ((.excluded 19),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.neg 17),(.neg 16),(.pos 15),(.pos 18),(.pos 21),(.pos 27),(.pos 28)]),
   ((.excluded 20),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.neg 17),(.neg 16),(.pos 15),(.pos 18),(.pos 21),(.pos 27),(.pos 31)]),
   ((.excluded 21),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.neg 17),(.neg 16),(.pos 15),(.pos 18),(.pos 21),(.pos 27)]),
   ((.excluded 22),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.pos 15),(.pos 22),(.pos 29),(.pos 33)]),
   ((.excluded 23),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.pos 15),(.pos 22),(.pos 29)]),
   ((.excluded 24),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.pos 15),(.pos 22),(.pos 33)]),
   ((.excluded 25),[(.neg 34),(.neg 33),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.pos 15),(.pos 22),(.pos 30),(.pos 32)]),
   ((.excluded 26),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.pos 15),(.pos 22),(.pos 30)]),
   ((.excluded 27),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.pos 15),(.pos 22),(.pos 32)]),
   ((.excluded 28),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.pos 15),(.pos 22)]),
   ((.excluded 29),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.pos 15),(.pos 29),(.pos 33)]),
   ((.excluded 30),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.pos 15),(.pos 24),(.pos 29),(.pos 31)]),
   ((.excluded 31),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.pos 15),(.pos 24),(.pos 29)]),
   ((.excluded 32),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.pos 15),(.pos 29),(.pos 31)]),
   ((.excluded 33),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.pos 15),(.pos 29)]),
   ((.excluded 34),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.pos 15),(.pos 23),(.pos 28),(.pos 33)]),
   ((.excluded 35),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.pos 15),(.pos 23),(.pos 33)]),
   ((.excluded 36),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.pos 15),(.pos 28),(.pos 33)]),
   ((.excluded 37),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.pos 15),(.pos 33)]),
   ((.excluded 38),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.pos 15),(.pos 23),(.pos 28)]),
   ((.excluded 39),[(.neg 34),(.neg 33),(.neg 32),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.pos 15),(.pos 23),(.pos 30),(.pos 31)]),
   ((.excluded 40),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.pos 15),(.pos 23),(.pos 30)]),
   ((.excluded 41),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.pos 15),(.pos 23),(.pos 31)]),
   ((.excluded 42),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.pos 15),(.pos 23)]),
   ((.excluded 43),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.pos 15),(.pos 24),(.pos 28),(.pos 32)]),
   ((.excluded 44),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.pos 15),(.pos 24),(.pos 28)]),
   ((.excluded 45),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.pos 15),(.pos 28),(.pos 32)]),
   ((.excluded 46),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.pos 15),(.pos 28)]),
   ((.excluded 47),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.pos 15),(.pos 24),(.pos 31)])]

theorem certificates_2_valid : ∀ oc ∈ certificates_2,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_3 : List (Origin 35 352 × List Sat.Literal) :=
  [((.excluded 48),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.pos 15),(.pos 24),(.pos 32)]),
   ((.excluded 49),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.pos 15),(.pos 24)]),
   ((.excluded 50),[(.neg 34),(.neg 33),(.neg 32),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.pos 15),(.pos 30),(.pos 31)]),
   ((.excluded 51),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.pos 15),(.pos 31)]),
   ((.excluded 52),[(.neg 34),(.neg 33),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.pos 15),(.pos 30),(.pos 32)]),
   ((.excluded 53),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.pos 15),(.pos 30)]),
   ((.excluded 54),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.pos 15),(.pos 32)]),
   ((.excluded 55),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.pos 15)]),
   ((.excluded 56),[(.neg 33),(.neg 32),(.neg 31),(.neg 27),(.neg 26),(.neg 25),(.neg 21),(.neg 20),(.neg 19),(.neg 15),(.pos 16),(.pos 17),(.pos 18),(.pos 22),(.pos 23),(.pos 24),(.pos 28),(.pos 29),(.pos 30),(.pos 34)]),
   ((.excluded 57),[(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 20),(.pos 21),(.pos 22),(.pos 23),(.pos 24),(.pos 31),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 58),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 22),(.pos 23),(.pos 24),(.pos 25),(.pos 34)]),
   ((.excluded 59),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 22),(.pos 23),(.pos 24),(.pos 26),(.pos 34)]),
   ((.excluded 60),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 22),(.pos 23),(.pos 24),(.pos 27),(.pos 34)]),
   ((.excluded 61),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 22),(.pos 23),(.pos 24),(.pos 34)]),
   ((.excluded 62),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 20),(.neg 19),(.neg 18),(.neg 15),(.pos 16),(.pos 17),(.pos 21),(.pos 22),(.pos 28)]),
   ((.excluded 63),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 15),(.pos 16),(.pos 17),(.pos 22),(.pos 27),(.pos 28)]),
   ((.excluded 64),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 15),(.pos 16),(.pos 17),(.pos 22),(.pos 28),(.pos 32)]),
   ((.excluded 65),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 15),(.pos 16),(.pos 17),(.pos 22),(.pos 28),(.pos 33)]),
   ((.excluded 66),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 15),(.pos 16),(.pos 17),(.pos 22),(.pos 28)]),
   ((.excluded 67),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 21),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 20),(.pos 22),(.pos 27),(.pos 31)]),
   ((.excluded 68),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 28),(.neg 26),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 22),(.pos 25),(.pos 27),(.pos 29),(.pos 32)]),
   ((.excluded 69),[(.neg 34),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 25),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 22),(.pos 26),(.pos 27),(.pos 30),(.pos 33)]),
   ((.excluded 70),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 22),(.pos 27)]),
   ((.excluded 71),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 21),(.neg 17),(.neg 16),(.neg 15),(.pos 18),(.pos 19),(.pos 20),(.pos 22),(.pos 31)]),
   ((.excluded 72),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 21),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 20),(.pos 22),(.pos 29),(.pos 31)]),
   ((.excluded 73),[(.neg 34),(.neg 33),(.neg 32),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 21),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 20),(.pos 22),(.pos 30),(.pos 31)]),
   ((.excluded 74),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 21),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 20),(.pos 22),(.pos 31)]),
   ((.excluded 75),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 22),(.pos 29),(.pos 33)]),
   ((.excluded 76),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 21),(.pos 22),(.pos 26),(.pos 29)]),
   ((.excluded 77),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 21),(.pos 22),(.pos 29)]),
   ((.excluded 78),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 22),(.pos 26),(.pos 29)]),
   ((.excluded 79),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 22),(.pos 29)]),
   ((.excluded 80),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.neg 17),(.neg 16),(.neg 15),(.pos 18),(.pos 22),(.pos 25),(.pos 33)]),
   ((.excluded 81),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.neg 17),(.neg 16),(.neg 15),(.pos 18),(.pos 22),(.pos 33)]),
   ((.excluded 82),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 22),(.pos 25),(.pos 33)]),
   ((.excluded 83),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 22),(.pos 33)]),
   ((.excluded 84),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.neg 17),(.neg 16),(.neg 15),(.pos 18),(.pos 22),(.pos 25)]),
   ((.excluded 85),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.neg 17),(.neg 16),(.neg 15),(.pos 18),(.pos 22),(.pos 26),(.pos 32)]),
   ((.excluded 86),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.neg 17),(.neg 16),(.neg 15),(.pos 18),(.pos 22),(.pos 26)]),
   ((.excluded 87),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.neg 17),(.neg 16),(.neg 15),(.pos 18),(.pos 22),(.pos 32)]),
   ((.excluded 88),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.neg 17),(.neg 16),(.neg 15),(.pos 18),(.pos 22)]),
   ((.excluded 89),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 21),(.pos 22),(.pos 25),(.pos 30)]),
   ((.excluded 90),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 21),(.pos 22),(.pos 25)]),
   ((.excluded 91),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 22),(.pos 25),(.pos 30)]),
   ((.excluded 92),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 22),(.pos 25)]),
   ((.excluded 93),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 21),(.pos 22),(.pos 26)]),
   ((.excluded 94),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 21),(.pos 22),(.pos 30)]),
   ((.excluded 95),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 21),(.pos 22)]),
   ((.excluded 96),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 22),(.pos 26),(.pos 32)]),
   ((.excluded 97),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 22),(.pos 26)]),
   ((.excluded 98),[(.neg 34),(.neg 33),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 22),(.pos 30),(.pos 32)]),
   ((.excluded 99),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 22),(.pos 30)]),
   ((.excluded 100),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 22),(.pos 32)]),
   ((.excluded 101),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 22)]),
   ((.excluded 102),[(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 25),(.pos 26),(.pos 27),(.pos 28),(.pos 29),(.pos 30),(.pos 31),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 103),[(.neg 33),(.neg 32),(.neg 31),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 28),(.pos 29),(.pos 30),(.pos 34)]),
   ((.excluded 104),[(.neg 33),(.neg 32),(.neg 31),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20),(.pos 28),(.pos 29),(.pos 30),(.pos 34)]),
   ((.excluded 105),[(.neg 33),(.neg 32),(.neg 31),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 21),(.pos 28),(.pos 29),(.pos 30),(.pos 34)]),
   ((.excluded 106),[(.neg 33),(.neg 32),(.neg 31),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 28),(.pos 29),(.pos 30),(.pos 34)]),
   ((.excluded 107),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 28),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 16),(.neg 15),(.pos 17),(.pos 25),(.pos 27),(.pos 29),(.pos 32)]),
   ((.excluded 108),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 28),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20),(.pos 25),(.pos 27),(.pos 29),(.pos 32)]),
   ((.excluded 109),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 28),(.neg 26),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 24),(.pos 25),(.pos 27),(.pos 29),(.pos 32)]),
   ((.excluded 110),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 28),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 25),(.pos 27),(.pos 29),(.pos 32)]),
   ((.excluded 111),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 19),(.neg 17),(.neg 15),(.pos 16),(.pos 18),(.pos 20),(.pos 23),(.pos 29)]),
   ((.excluded 112),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20),(.pos 21),(.pos 24),(.pos 29),(.pos 33)]),
   ((.excluded 113),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20),(.pos 29)]),
   ((.excluded 114),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 17),(.neg 15),(.pos 16),(.pos 18),(.pos 23),(.pos 26),(.pos 29)]),
   ((.excluded 115),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 17),(.neg 15),(.pos 16),(.pos 18),(.pos 23),(.pos 29),(.pos 31)]),
   ((.excluded 116),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 17),(.neg 15),(.pos 16),(.pos 18),(.pos 23),(.pos 29),(.pos 33)]),
   ((.excluded 117),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 17),(.neg 15),(.pos 16),(.pos 18),(.pos 23),(.pos 29)]),
   ((.excluded 118),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 16),(.neg 15),(.pos 17),(.pos 19),(.pos 29),(.pos 33)]),
   ((.excluded 119),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 16),(.neg 15),(.pos 17),(.pos 29),(.pos 33)]),
   ((.excluded 120),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 29),(.pos 33)]),
   ((.excluded 121),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 29),(.pos 33)]),
   ((.excluded 122),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 16),(.neg 15),(.pos 17),(.pos 19),(.pos 29)]),
   ((.excluded 123),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.neg 18),(.neg 16),(.neg 15),(.pos 17),(.pos 21),(.pos 29),(.pos 31)]),
   ((.excluded 124),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.neg 18),(.neg 16),(.neg 15),(.pos 17),(.pos 21),(.pos 29)]),
   ((.excluded 125),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 16),(.neg 15),(.pos 17),(.pos 29),(.pos 31)]),
   ((.excluded 126),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 16),(.neg 15),(.pos 17),(.pos 29)]),
   ((.excluded 127),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 24),(.pos 26),(.pos 29)]),
   ((.excluded 128),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 24),(.pos 29)]),
   ((.excluded 129),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 26),(.pos 29)]),
   ((.excluded 130),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 29)]),
   ((.excluded 131),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 21),(.pos 26),(.pos 29)]),
   ((.excluded 132),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 21),(.pos 29),(.pos 31)]),
   ((.excluded 133),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 21),(.pos 29)]),
   ((.excluded 134),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 24),(.pos 26),(.pos 29)]),
   ((.excluded 135),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 26),(.pos 29)]),
   ((.excluded 136),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 24),(.pos 29),(.pos 31)]),
   ((.excluded 137),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 24),(.pos 29)]),
   ((.excluded 138),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 29),(.pos 31)]),
   ((.excluded 139),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 29)]),
   ((.excluded 140),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 19),(.neg 18),(.neg 17),(.neg 15),(.pos 16),(.pos 20),(.pos 21),(.pos 24),(.pos 33)]),
   ((.excluded 141),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 23),(.neg 22),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20),(.pos 21),(.pos 24),(.pos 25),(.pos 33)]),
   ((.excluded 142),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20),(.pos 21),(.pos 24),(.pos 28),(.pos 33)]),
   ((.excluded 143),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20),(.pos 21),(.pos 24),(.pos 33)]),
   ((.excluded 144),[(.neg 34),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 15),(.pos 16),(.pos 26),(.pos 27),(.pos 30),(.pos 33)]),
   ((.excluded 145),[(.neg 34),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 26),(.pos 27),(.pos 30),(.pos 33)]),
   ((.excluded 146),[(.neg 34),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 23),(.pos 26),(.pos 27),(.pos 30),(.pos 33)]),
   ((.excluded 147),[(.neg 34),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 26),(.pos 27),(.pos 30),(.pos 33)]),
   ((.excluded 148),[(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 15),(.pos 16),(.pos 31),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 149),[(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 16),(.neg 15),(.pos 17),(.pos 31),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 150),[(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 17),(.neg 16),(.neg 15),(.pos 18),(.pos 31),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 151),[(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 31),(.pos 32),(.pos 33),(.pos 34)]),
   ((.excluded 152),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 15),(.pos 16),(.pos 33)]),
   ((.excluded 153),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 16),(.neg 15),(.pos 17),(.pos 19),(.pos 33)]),
   ((.excluded 154),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 16),(.neg 15),(.pos 17),(.pos 23),(.pos 25),(.pos 33)]),
   ((.excluded 155),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 16),(.neg 15),(.pos 17),(.pos 23),(.pos 33)]),
   ((.excluded 156),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 16),(.neg 15),(.pos 17),(.pos 25),(.pos 33)]),
   ((.excluded 157),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 16),(.neg 15),(.pos 17),(.pos 33)]),
   ((.excluded 158),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 17),(.neg 16),(.neg 15),(.pos 18),(.pos 19),(.pos 28),(.pos 33)]),
   ((.excluded 159),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 17),(.neg 16),(.neg 15),(.pos 18),(.pos 19),(.pos 33)]),
   ((.excluded 160),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 28),(.pos 33)]),
   ((.excluded 161),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 33)]),
   ((.excluded 162),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 17),(.neg 16),(.neg 15),(.pos 18),(.pos 25),(.pos 33)]),
   ((.excluded 163),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 17),(.neg 16),(.neg 15),(.pos 18),(.pos 28),(.pos 33)]),
   ((.excluded 164),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 17),(.neg 16),(.neg 15),(.pos 18),(.pos 33)]),
   ((.excluded 165),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 23),(.pos 25),(.pos 33)]),
   ((.excluded 166),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 25),(.pos 33)]),
   ((.excluded 167),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 23),(.pos 28),(.pos 33)]),
   ((.excluded 168),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 23),(.pos 33)]),
   ((.excluded 169),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 28),(.pos 33)]),
   ((.excluded 170),[(.neg 34),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 33)]),
   ((.excluded 171),[(.neg 34),(.neg 33),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 16),(.neg 15),(.pos 17),(.pos 18),(.pos 24),(.pos 30),(.pos 32)]),
   ((.excluded 172),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 20),(.neg 18),(.neg 16),(.neg 15),(.pos 17),(.pos 19),(.pos 21),(.pos 23),(.pos 32)]),
   ((.excluded 173),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 16),(.neg 15),(.pos 17),(.pos 32)]),
   ((.excluded 174),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 16),(.neg 15),(.pos 17),(.pos 18),(.pos 19),(.pos 24),(.pos 30)]),
   ((.excluded 175),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 16),(.neg 15),(.pos 17),(.pos 18),(.pos 24),(.pos 25),(.pos 30)])]

theorem certificates_3_valid : ∀ oc ∈ certificates_3,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_4 : List (Origin 35 352 × List Sat.Literal) :=
  [((.excluded 176),[(.neg 34),(.neg 33),(.neg 32),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 16),(.neg 15),(.pos 17),(.pos 18),(.pos 24),(.pos 30),(.pos 31)]),
   ((.excluded 177),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 16),(.neg 15),(.pos 17),(.pos 18),(.pos 24),(.pos 30)]),
   ((.excluded 178),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 16),(.neg 15),(.pos 17),(.pos 19),(.pos 27),(.pos 34)]),
   ((.excluded 179),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 16),(.neg 15),(.pos 17),(.pos 19),(.pos 27)]),
   ((.excluded 180),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 16),(.neg 15),(.pos 17),(.pos 19),(.pos 34)]),
   ((.excluded 181),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 16),(.neg 15),(.pos 17),(.pos 19)]),
   ((.excluded 182),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.neg 18),(.neg 16),(.neg 15),(.pos 17),(.pos 21),(.pos 31)]),
   ((.excluded 183),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.neg 18),(.neg 16),(.neg 15),(.pos 17),(.pos 21),(.pos 25),(.pos 34)]),
   ((.excluded 184),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.neg 18),(.neg 16),(.neg 15),(.pos 17),(.pos 21),(.pos 25)]),
   ((.excluded 185),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.neg 18),(.neg 16),(.neg 15),(.pos 17),(.pos 21),(.pos 34)]),
   ((.excluded 186),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.neg 18),(.neg 16),(.neg 15),(.pos 17),(.pos 21)]),
   ((.excluded 187),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 16),(.neg 15),(.pos 17),(.pos 23),(.pos 25)]),
   ((.excluded 188),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 16),(.neg 15),(.pos 17),(.pos 25),(.pos 34)]),
   ((.excluded 189),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 16),(.neg 15),(.pos 17),(.pos 25)]),
   ((.excluded 190),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 16),(.neg 15),(.pos 17),(.pos 27),(.pos 34)]),
   ((.excluded 191),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 16),(.neg 15),(.pos 17),(.pos 34)]),
   ((.excluded 192),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 16),(.neg 15),(.pos 17),(.pos 23),(.pos 27),(.pos 31)]),
   ((.excluded 193),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 16),(.neg 15),(.pos 17),(.pos 23),(.pos 27)]),
   ((.excluded 194),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 16),(.neg 15),(.pos 17),(.pos 23),(.pos 31)]),
   ((.excluded 195),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 16),(.neg 15),(.pos 17),(.pos 23)]),
   ((.excluded 196),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 16),(.neg 15),(.pos 17),(.pos 27),(.pos 31)]),
   ((.excluded 197),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 16),(.neg 15),(.pos 17),(.pos 27)]),
   ((.excluded 198),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 16),(.neg 15),(.pos 17),(.pos 31)]),
   ((.excluded 199),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 16),(.neg 15),(.pos 17)]),
   ((.excluded 200),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 22),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 21),(.pos 23),(.pos 26),(.pos 32)]),
   ((.excluded 201),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 21),(.pos 23),(.pos 28),(.pos 32)]),
   ((.excluded 202),[(.neg 34),(.neg 33),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 21),(.pos 23),(.pos 30),(.pos 32)]),
   ((.excluded 203),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 21),(.pos 23),(.pos 32)]),
   ((.excluded 204),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 27),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 21),(.pos 25),(.pos 26),(.pos 28),(.pos 31)]),
   ((.excluded 205),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 21),(.pos 28)]),
   ((.excluded 206),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 21),(.pos 25),(.pos 30)]),
   ((.excluded 207),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 21),(.pos 25),(.pos 34)]),
   ((.excluded 208),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 21),(.pos 25)]),
   ((.excluded 209),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 15),(.pos 16),(.pos 21),(.pos 26),(.pos 34)]),
   ((.excluded 210),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 15),(.pos 16),(.pos 21),(.pos 26)]),
   ((.excluded 211),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 21),(.pos 26),(.pos 34)]),
   ((.excluded 212),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 21),(.pos 26)]),
   ((.excluded 213),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 15),(.pos 16),(.pos 21),(.pos 34)]),
   ((.excluded 214),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 21),(.pos 34)]),
   ((.excluded 215),[(.neg 34),(.neg 33),(.neg 32),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 15),(.pos 16),(.pos 21),(.pos 30),(.pos 31)]),
   ((.excluded 216),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 15),(.pos 16),(.pos 21),(.pos 30)]),
   ((.excluded 217),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 15),(.pos 16),(.pos 21),(.pos 31)]),
   ((.excluded 218),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 15),(.pos 16),(.pos 21)]),
   ((.excluded 219),[(.neg 34),(.neg 33),(.neg 32),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 21),(.pos 30),(.pos 31)]),
   ((.excluded 220),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 21),(.pos 30)]),
   ((.excluded 221),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 21),(.pos 31)]),
   ((.excluded 222),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 21)]),
   ((.excluded 223),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 27),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 17),(.neg 16),(.neg 15),(.pos 18),(.pos 25),(.pos 26),(.pos 28),(.pos 31)]),
   ((.excluded 224),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 27),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 23),(.pos 25),(.pos 26),(.pos 28),(.pos 31)]),
   ((.excluded 225),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 27),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 24),(.pos 25),(.pos 26),(.pos 28),(.pos 31)]),
   ((.excluded 226),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 27),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 25),(.pos 26),(.pos 28),(.pos 31)]),
   ((.excluded 227),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 24),(.pos 25)]),
   ((.excluded 228),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.neg 17),(.neg 16),(.neg 15),(.pos 18),(.pos 20),(.pos 25),(.pos 34)]),
   ((.excluded 229),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.neg 17),(.neg 16),(.neg 15),(.pos 18),(.pos 20),(.pos 25)]),
   ((.excluded 230),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 17),(.neg 16),(.neg 15),(.pos 18),(.pos 25),(.pos 34)]),
   ((.excluded 231),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 17),(.neg 16),(.neg 15),(.pos 18),(.pos 25)]),
   ((.excluded 232),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20),(.pos 25),(.pos 34)]),
   ((.excluded 233),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 25),(.pos 34)]),
   ((.excluded 234),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20),(.pos 23),(.pos 25),(.pos 30)]),
   ((.excluded 235),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20),(.pos 23),(.pos 25)]),
   ((.excluded 236),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20),(.pos 25),(.pos 30)]),
   ((.excluded 237),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20),(.pos 25)]),
   ((.excluded 238),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 23),(.pos 25),(.pos 30)]),
   ((.excluded 239),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 23),(.pos 25)]),
   ((.excluded 240),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 25),(.pos 30)]),
   ((.excluded 241),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 25)]),
   ((.excluded 242),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 23),(.pos 26)]),
   ((.excluded 243),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20),(.pos 23),(.pos 27),(.pos 28)]),
   ((.excluded 244),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20),(.pos 23),(.pos 28)]),
   ((.excluded 245),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 23),(.pos 27),(.pos 28)]),
   ((.excluded 246),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 23),(.pos 28)]),
   ((.excluded 247),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20),(.pos 23),(.pos 27)]),
   ((.excluded 248),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20),(.pos 23),(.pos 30)]),
   ((.excluded 249),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20),(.pos 23)]),
   ((.excluded 250),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 23),(.pos 27),(.pos 31)]),
   ((.excluded 251),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 23),(.pos 27)]),
   ((.excluded 252),[(.neg 34),(.neg 33),(.neg 32),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 23),(.pos 30),(.pos 31)]),
   ((.excluded 253),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 23),(.pos 30)]),
   ((.excluded 254),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 23),(.pos 31)]),
   ((.excluded 255),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 23)]),
   ((.excluded 256),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 30)]),
   ((.excluded 257),[(.neg 34),(.neg 33),(.neg 32),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 15),(.pos 16),(.pos 30),(.pos 31)]),
   ((.excluded 258),[(.neg 34),(.neg 33),(.neg 32),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 30),(.pos 31)]),
   ((.excluded 259),[(.neg 34),(.neg 33),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 15),(.pos 16),(.pos 20),(.pos 30),(.pos 32)]),
   ((.excluded 260),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 15),(.pos 16),(.pos 20),(.pos 30)]),
   ((.excluded 261),[(.neg 34),(.neg 33),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 15),(.pos 16),(.pos 30),(.pos 32)]),
   ((.excluded 262),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 15),(.pos 16),(.pos 30)]),
   ((.excluded 263),[(.neg 34),(.neg 33),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20),(.pos 30),(.pos 32)]),
   ((.excluded 264),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20),(.pos 30)]),
   ((.excluded 265),[(.neg 34),(.neg 33),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 30),(.pos 32)]),
   ((.excluded 266),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 30)]),
   ((.excluded 267),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 17),(.neg 16),(.neg 15),(.pos 18),(.pos 31)]),
   ((.excluded 268),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 15),(.pos 16),(.pos 24),(.pos 27),(.pos 31)]),
   ((.excluded 269),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 15),(.pos 16),(.pos 24),(.pos 31)]),
   ((.excluded 270),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 15),(.pos 16),(.pos 27),(.pos 31)]),
   ((.excluded 271),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 15),(.pos 16),(.pos 31)]),
   ((.excluded 272),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 24),(.pos 27),(.pos 31)]),
   ((.excluded 273),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 24),(.pos 31)]),
   ((.excluded 274),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 27),(.pos 31)]),
   ((.excluded 275),[(.neg 34),(.neg 33),(.neg 32),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 31)]),
   ((.excluded 276),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 15),(.pos 16),(.pos 20),(.pos 32)]),
   ((.excluded 277),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 15),(.pos 16),(.pos 20),(.pos 27),(.pos 34)]),
   ((.excluded 278),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 15),(.pos 16),(.pos 20),(.pos 27)]),
   ((.excluded 279),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 15),(.pos 16),(.pos 20),(.pos 34)]),
   ((.excluded 280),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 15),(.pos 16),(.pos 20)]),
   ((.excluded 281),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 15),(.pos 16),(.pos 24),(.pos 27)]),
   ((.excluded 282),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 15),(.pos 16),(.pos 27),(.pos 34)]),
   ((.excluded 283),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 15),(.pos 16),(.pos 27)]),
   ((.excluded 284),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 15),(.pos 16),(.pos 26),(.pos 34)]),
   ((.excluded 285),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 15),(.pos 16),(.pos 34)]),
   ((.excluded 286),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 15),(.pos 16),(.pos 24),(.pos 26),(.pos 32)]),
   ((.excluded 287),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 15),(.pos 16),(.pos 24),(.pos 26)]),
   ((.excluded 288),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 15),(.pos 16),(.pos 24),(.pos 32)]),
   ((.excluded 289),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 15),(.pos 16),(.pos 24)]),
   ((.excluded 290),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 15),(.pos 16),(.pos 26),(.pos 32)]),
   ((.excluded 291),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 15),(.pos 16),(.pos 26)]),
   ((.excluded 292),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 15),(.pos 16),(.pos 32)]),
   ((.excluded 293),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 15),(.pos 16)]),
   ((.excluded 294),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20),(.pos 27),(.pos 28)]),
   ((.excluded 295),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20),(.pos 27),(.pos 34)]),
   ((.excluded 296),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20),(.pos 27)]),
   ((.excluded 297),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.neg 17),(.neg 16),(.neg 15),(.pos 18),(.pos 20),(.pos 34)]),
   ((.excluded 298),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20),(.pos 34)]),
   ((.excluded 299),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.neg 17),(.neg 16),(.neg 15),(.pos 18),(.pos 20),(.pos 28),(.pos 32)]),
   ((.excluded 300),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.neg 17),(.neg 16),(.neg 15),(.pos 18),(.pos 20),(.pos 28)]),
   ((.excluded 301),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.neg 17),(.neg 16),(.neg 15),(.pos 18),(.pos 20),(.pos 32)]),
   ((.excluded 302),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.neg 17),(.neg 16),(.neg 15),(.pos 18),(.pos 20)]),
   ((.excluded 303),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20),(.pos 28),(.pos 32)])]

theorem certificates_4_valid : ∀ oc ∈ certificates_4,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_5 : List (Origin 35 352 × List Sat.Literal) :=
  [((.excluded 304),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20),(.pos 28)]),
   ((.excluded 305),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20),(.pos 32)]),
   ((.excluded 306),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20)]),
   ((.excluded 307),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 27),(.pos 34)]),
   ((.excluded 308),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 27),(.pos 34)]),
   ((.excluded 309),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 24),(.pos 27),(.pos 28)]),
   ((.excluded 310),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 24),(.pos 27)]),
   ((.excluded 311),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 27),(.pos 28)]),
   ((.excluded 312),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 27)]),
   ((.excluded 313),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 24),(.pos 27),(.pos 28)]),
   ((.excluded 314),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 24),(.pos 27)]),
   ((.excluded 315),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 27),(.pos 28)]),
   ((.excluded 316),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 27)]),
   ((.excluded 317),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 17),(.neg 16),(.neg 15),(.pos 18),(.pos 19),(.pos 26),(.pos 34)]),
   ((.excluded 318),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 17),(.neg 16),(.neg 15),(.pos 18),(.pos 19),(.pos 34)]),
   ((.excluded 319),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 17),(.neg 16),(.neg 15),(.pos 18),(.pos 26),(.pos 34)]),
   ((.excluded 320),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 17),(.neg 16),(.neg 15),(.pos 18),(.pos 34)]),
   ((.excluded 321),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 26),(.pos 34)]),
   ((.excluded 322),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 34)]),
   ((.excluded 323),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 26),(.pos 34)]),
   ((.excluded 324),[(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 34)]),
   ((.excluded 325),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 17),(.neg 16),(.neg 15),(.pos 18),(.pos 19),(.pos 26)]),
   ((.excluded 326),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 17),(.neg 16),(.neg 15),(.pos 18),(.pos 19),(.pos 28)]),
   ((.excluded 327),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 17),(.neg 16),(.neg 15),(.pos 18),(.pos 19)]),
   ((.excluded 328),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 17),(.neg 16),(.neg 15),(.pos 18),(.pos 26),(.pos 32)]),
   ((.excluded 329),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 17),(.neg 16),(.neg 15),(.pos 18),(.pos 26)]),
   ((.excluded 330),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 17),(.neg 16),(.neg 15),(.pos 18),(.pos 28),(.pos 32)]),
   ((.excluded 331),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 17),(.neg 16),(.neg 15),(.pos 18),(.pos 28)]),
   ((.excluded 332),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 17),(.neg 16),(.neg 15),(.pos 18),(.pos 32)]),
   ((.excluded 333),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 17),(.neg 16),(.neg 15),(.pos 18)]),
   ((.excluded 334),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 24),(.pos 26)]),
   ((.excluded 335),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 26)]),
   ((.excluded 336),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 24),(.pos 28)]),
   ((.excluded 337),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 24)]),
   ((.excluded 338),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 28)]),
   ((.excluded 339),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19)]),
   ((.excluded 340),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 24),(.pos 26),(.pos 32)]),
   ((.excluded 341),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 24),(.pos 26)]),
   ((.excluded 342),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 26),(.pos 32)]),
   ((.excluded 343),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 26)]),
   ((.excluded 344),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 24),(.pos 28),(.pos 32)]),
   ((.excluded 345),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 24),(.pos 28)]),
   ((.excluded 346),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 24),(.pos 32)]),
   ((.excluded 347),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 24)]),
   ((.excluded 348),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 28),(.pos 32)]),
   ((.excluded 349),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 28)]),
   ((.excluded 350),[(.neg 34),(.neg 33),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 32)]),
   ((.excluded 351),[(.neg 34),(.neg 33),(.neg 32),(.neg 31),(.neg 30),(.neg 29),(.neg 28),(.neg 27),(.neg 26),(.neg 25),(.neg 24),(.neg 23),(.neg 22),(.neg 21),(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15)])]

theorem certificates_5_valid : ∀ oc ∈ certificates_5,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



theorem witness_0 : ∀ j : Fin 128,
    let w : Fin 352 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 7 4 ∧
      ValidWitness 7 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 7 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 128,
      let w : Fin 352 := ⟨0 + j.val,by omega⟩
      target w < MatroidCatalogue.count 7 4 ∧
        Papers.RationalityTen.MatroidChecked.FastSemanticChecks.RawWitness 7 (N6R4.familyMasks.get 17)
        (fun i : Fin 35 => N7R4.gridMasks.get i.val) newIndex (models w)
        (N7R4.familyMasks.get (target w)) (permutation w) := by
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
  exact ⟨hj.1,Papers.RationalityTen.MatroidChecked.FastSemanticChecks.rawWitness_sound 7 _ _ _ _ _ _ hj.2⟩



theorem witness_1 : ∀ j : Fin 128,
    let w : Fin 352 := ⟨128 + j.val,by omega⟩
    target w < MatroidCatalogue.count 7 4 ∧
      ValidWitness 7 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 7 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 128,
      let w : Fin 352 := ⟨128 + j.val,by omega⟩
      target w < MatroidCatalogue.count 7 4 ∧
        Papers.RationalityTen.MatroidChecked.FastSemanticChecks.RawWitness 7 (N6R4.familyMasks.get 17)
        (fun i : Fin 35 => N7R4.gridMasks.get i.val) newIndex (models w)
        (N7R4.familyMasks.get (target w)) (permutation w) := by
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
  exact ⟨hj.1,Papers.RationalityTen.MatroidChecked.FastSemanticChecks.rawWitness_sound 7 _ _ _ _ _ _ hj.2⟩



theorem witness_2 : ∀ j : Fin 96,
    let w : Fin 352 := ⟨256 + j.val,by omega⟩
    target w < MatroidCatalogue.count 7 4 ∧
      ValidWitness 7 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 7 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 96,
      let w : Fin 352 := ⟨256 + j.val,by omega⟩
      target w < MatroidCatalogue.count 7 4 ∧
        Papers.RationalityTen.MatroidChecked.FastSemanticChecks.RawWitness 7 (N6R4.familyMasks.get 17)
        (fun i : Fin 35 => N7R4.gridMasks.get i.val) newIndex (models w)
        (N7R4.familyMasks.get (target w)) (permutation w) := by
    refine (Fin.forall_fin_add (m := 48) (n := 48) _).2 ⟨?_, ?_⟩
    · refine (Fin.forall_fin_add (m := 24) (n := 24) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 12) (n := 12) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 6) (n := 6) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 3) (n := 3) _).2 ⟨?_, ?_⟩
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
      · refine (Fin.forall_fin_add (m := 12) (n := 12) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 6) (n := 6) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 3) (n := 3) _).2 ⟨?_, ?_⟩
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
    · refine (Fin.forall_fin_add (m := 24) (n := 24) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 12) (n := 12) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 6) (n := 6) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 3) (n := 3) _).2 ⟨?_, ?_⟩
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
      · refine (Fin.forall_fin_add (m := 12) (n := 12) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 6) (n := 6) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 3) (n := 3) _).2 ⟨?_, ?_⟩
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
  exact ⟨hj.1,Papers.RationalityTen.MatroidChecked.FastSemanticChecks.rawWitness_sound 7 _ _ _ _ _ _ hj.2⟩


end Papers.RationalityTen.MatroidCatalogue.Cases.N7R4C17

/- Source: MatroidCatalogue/Cases/N7R4C17Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R4C17

noncomputable def certificates : List (Origin 35 352 × List Sat.Literal) :=
  certificates_0 ++ certificates_1 ++ certificates_2 ++ certificates_3 ++ certificates_4 ++ certificates_5

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  intro oc hoc
  simp only [certificates,List.mem_append,or_assoc] at hoc
  rcases hoc with h0 | h1 | h2 | h3 | h4 | h5
  · exact certificates_0_valid oc h0
  · exact certificates_1_valid oc h1
  · exact certificates_2_valid oc h2
  · exact certificates_3_valid oc h3
  · exact certificates_4_valid oc h4
  · exact certificates_5_valid oc h5

theorem models_valid : ∀ w : Fin 352,
    target w < MatroidCatalogue.count 7 4 ∧
      ValidWitness 7 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 7 4 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  by_cases h0 : w.val < 128
  ·
    have hh := witness_0 ⟨w.val - 0,by omega⟩
    have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 352) = w := Fin.ext (by dsimp only; omega)
    dsimp only at hh
    rw [heq] at hh
    exact hh
  ·
    by_cases h1 : w.val < 256
    ·
      have hh := witness_1 ⟨w.val - 128,by omega⟩
      have heq : (⟨128 + (w.val - 128),by omega⟩ : Fin 352) = w := Fin.ext (by dsimp only; omega)
      dsimp only at hh
      rw [heq] at hh
      exact hh
    ·
      have hh := witness_2 ⟨w.val - 256,by omega⟩
      have heq : (⟨256 + (w.val - 256),by omega⟩ : Fin 352) = w := Fin.ext (by dsimp only; omega)
      dsimp only at hh
      rw [heq] at hh
      exact hh

theorem coverage (M : BasisFamily (groundPrefix 7) 4)
    (hold : M.bases.filter ((6 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 7 4, IsomorphicWithin 7 M.bases B := by
  apply extension_covered_of_certificate (n:=6) (r:=4) (by decide)
    catalogue old U newIndex models certificates
    N7R4.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidChecked.PublicRefutations.N7R4C17.formula []
    exact Papers.RationalityTen.MatroidChecked.PublicRefutations.N7R4C17.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 7 4 (target w),family_mem 7 4 (target w) hw.1,?_⟩
    exact validWitness_sound 7 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R4C17


end
end
end BundlePart1

section BundlePart2
/- Source: MatroidChecked/SemanticChunks/Cases02Part02.lean -/








@[expose] public section
noncomputable section

/- Source: MatroidCatalogue/Cases/N8R4C0Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C0

abbrev U := N8R4.grid
noncomputable def old : Finset (Finset (Fin 8)) := N7R4.family 0
noncomputable def newIndexTree : Table ℕ := (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf 35) (.leaf 36)) (.node 3 (.leaf 37) (.leaf 38))) (.node 6 (.node 5 (.leaf 39) (.leaf 40)) (.node 7 (.leaf 41) (.leaf 42)))) (.node 12 (.node 10 (.node 9 (.leaf 43) (.leaf 44)) (.node 11 (.leaf 45) (.leaf 46))) (.node 14 (.node 13 (.leaf 47) (.leaf 48)) (.node 15 (.leaf 49) (.node 16 (.leaf 50) (.leaf 51)))))) (.node 26 (.node 21 (.node 19 (.node 18 (.leaf 52) (.leaf 53)) (.node 20 (.leaf 54) (.leaf 55))) (.node 23 (.node 22 (.leaf 56) (.leaf 57)) (.node 24 (.leaf 58) (.node 25 (.leaf 59) (.leaf 60))))) (.node 30 (.node 28 (.node 27 (.leaf 61) (.leaf 62)) (.node 29 (.leaf 63) (.leaf 64))) (.node 32 (.node 31 (.leaf 65) (.leaf 66)) (.node 33 (.leaf 67) (.node 34 (.leaf 68) (.leaf 69)))))))
noncomputable def newIndex (i : Fin 35) : Fin 70 := Fin.ofNat 70 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 7 (.node 3 (.node 1 (.leaf (16106127360,1,12535432)) (.node 2 (.leaf (1006632960,1,12478088)) (.leaf (17112760320,10,14599816)))) (.node 5 (.node 4 (.leaf (983040,1,11789960)) (.leaf (16107110400,10,14141064))) (.node 6 (.leaf (1007616000,10,14055048)) (.leaf (17113743360,70,16434824))))) (.node 11 (.node 9 (.node 8 (.leaf (17179869184,0,10442376)) (.leaf (33285996544,2,12535432))) (.node 10 (.leaf (18186502144,2,12478088)) (.leaf (34292629504,11,14599816)))) (.node 13 (.node 12 (.leaf (17180852224,2,11789960)) (.leaf (33286979584,11,14141064))) (.node 14 (.leaf (18187485184,11,14055048)) (.leaf (34293612544,71,16434824))))))

noncomputable def models (i : Fin 15) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 15) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 15) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 70, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (7 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 70, (7 : Fin 8) ∈ U i → ∃ j : Fin 35, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C0

/- Source: MatroidCatalogue/Cases/N8R4C0Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C0


noncomputable def certificates_0 : List (Origin 70 15 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.neg 2)]),
   ((.fixed 3),[(.neg 3)]),
   ((.fixed 4),[(.neg 4)]),
   ((.fixed 5),[(.neg 5)]),
   ((.fixed 6),[(.neg 6)]),
   ((.fixed 7),[(.neg 7)]),
   ((.fixed 8),[(.neg 8)]),
   ((.fixed 9),[(.neg 9)]),
   ((.fixed 10),[(.neg 10)]),
   ((.fixed 11),[(.neg 11)]),
   ((.fixed 12),[(.neg 12)]),
   ((.fixed 13),[(.neg 13)]),
   ((.fixed 14),[(.neg 14)]),
   ((.fixed 15),[(.neg 15)]),
   ((.fixed 16),[(.neg 16)]),
   ((.fixed 17),[(.neg 17)]),
   ((.fixed 18),[(.neg 18)]),
   ((.fixed 19),[(.neg 19)]),
   ((.fixed 20),[(.neg 20)]),
   ((.fixed 21),[(.neg 21)]),
   ((.fixed 22),[(.neg 22)]),
   ((.fixed 23),[(.neg 23)]),
   ((.fixed 24),[(.neg 24)]),
   ((.fixed 25),[(.neg 25)]),
   ((.fixed 26),[(.neg 26)]),
   ((.fixed 27),[(.neg 27)]),
   ((.fixed 28),[(.neg 28)]),
   ((.fixed 29),[(.neg 29)]),
   ((.fixed 30),[(.neg 30)]),
   ((.fixed 31),[(.pos 31)]),
   ((.fixed 32),[(.pos 32)]),
   ((.fixed 33),[(.pos 33)]),
   ((.fixed 34),[(.pos 34)]),
   ((.exchange 31 52 6),[(.neg 52),(.neg 31),(.pos 9),(.pos 51)]),
   ((.exchange 31 53 6),[(.neg 53),(.neg 31),(.pos 10),(.pos 51)]),
   ((.exchange 31 54 6),[(.neg 54),(.neg 31),(.pos 12),(.pos 51)]),
   ((.exchange 31 62 5),[(.neg 62),(.neg 31),(.pos 19),(.pos 61)]),
   ((.exchange 31 63 5),[(.neg 63),(.neg 31),(.pos 20),(.pos 61)]),
   ((.exchange 31 64 5),[(.neg 64),(.neg 31),(.pos 22),(.pos 61)]),
   ((.exchange 31 67 4),[(.neg 67),(.neg 31),(.pos 26),(.pos 65)]),
   ((.exchange 32 51 6),[(.neg 51),(.neg 32),(.pos 9),(.pos 52)]),
   ((.exchange 32 53 6),[(.neg 53),(.neg 32),(.pos 11),(.pos 52)]),
   ((.exchange 32 54 6),[(.neg 54),(.neg 32),(.pos 13),(.pos 52)]),
   ((.exchange 32 61 5),[(.neg 61),(.neg 32),(.pos 19),(.pos 62)]),
   ((.exchange 32 63 5),[(.neg 63),(.neg 32),(.pos 21),(.pos 62)]),
   ((.exchange 32 64 5),[(.neg 64),(.neg 32),(.pos 23),(.pos 62)]),
   ((.exchange 32 67 4),[(.neg 67),(.neg 32),(.pos 27),(.pos 66)]),
   ((.exchange 33 51 6),[(.neg 51),(.neg 33),(.pos 10),(.pos 53)]),
   ((.exchange 33 52 6),[(.neg 52),(.neg 33),(.pos 11),(.pos 53)]),
   ((.exchange 33 54 6),[(.neg 54),(.neg 33),(.pos 14),(.pos 53)]),
   ((.exchange 33 61 5),[(.neg 61),(.neg 33),(.pos 20),(.pos 63)]),
   ((.exchange 33 62 5),[(.neg 62),(.neg 33),(.pos 21),(.pos 63)]),
   ((.exchange 33 64 5),[(.neg 64),(.neg 33),(.pos 24),(.pos 63)]),
   ((.exchange 33 65 4),[(.neg 65),(.neg 33),(.pos 26),(.pos 67)]),
   ((.exchange 33 66 4),[(.neg 66),(.neg 33),(.pos 27),(.pos 67)]),
   ((.exchange 33 68 4),[(.neg 68),(.neg 33),(.pos 30),(.pos 67)]),
   ((.exchange 34 51 6),[(.neg 51),(.neg 34),(.pos 12),(.pos 54)]),
   ((.exchange 34 52 6),[(.neg 52),(.neg 34),(.pos 13),(.pos 54)]),
   ((.exchange 34 53 6),[(.neg 53),(.neg 34),(.pos 14),(.pos 54)]),
   ((.exchange 34 61 5),[(.neg 61),(.neg 34),(.pos 22),(.pos 64)]),
   ((.exchange 34 62 5),[(.neg 62),(.neg 34),(.pos 23),(.pos 64)]),
   ((.exchange 34 63 5),[(.neg 63),(.neg 34),(.pos 24),(.pos 64)]),
   ((.exchange 34 67 4),[(.neg 67),(.neg 34),(.pos 30),(.pos 68)]),
   ((.exchange 35 31 7),[(.neg 35),(.neg 31),(.pos 1),(.pos 5),(.pos 15)]),
   ((.exchange 36 31 7),[(.neg 36),(.neg 31),(.pos 2),(.pos 6),(.pos 16)]),
   ((.exchange 37 31 7),[(.neg 37),(.neg 31),(.pos 3),(.pos 7),(.pos 17)]),
   ((.exchange 38 31 7),[(.neg 38),(.neg 31),(.pos 0),(.pos 4),(.pos 8),(.pos 18)]),
   ((.exchange 39 31 7),[(.neg 39),(.neg 31),(.pos 9),(.pos 19)]),
   ((.exchange 40 31 7),[(.neg 40),(.neg 31),(.pos 10),(.pos 20)]),
   ((.exchange 41 31 7),[(.neg 41),(.neg 31),(.pos 1),(.pos 11),(.pos 21)]),
   ((.exchange 42 31 7),[(.neg 42),(.neg 31),(.pos 12),(.pos 22)]),
   ((.exchange 43 31 7),[(.neg 43),(.neg 31),(.pos 2),(.pos 13),(.pos 23)]),
   ((.exchange 44 31 7),[(.neg 44),(.neg 31),(.pos 3),(.pos 14),(.pos 24)]),
   ((.exchange 45 31 7),[(.neg 45),(.neg 31),(.pos 9),(.pos 25)]),
   ((.exchange 46 31 7),[(.neg 46),(.neg 31),(.pos 10),(.pos 26)]),
   ((.exchange 47 31 7),[(.neg 47),(.neg 31),(.pos 5),(.pos 11),(.pos 27)]),
   ((.exchange 48 31 7),[(.neg 48),(.neg 31),(.pos 12),(.pos 28)]),
   ((.exchange 49 31 7),[(.neg 49),(.neg 31),(.pos 6),(.pos 13),(.pos 29)]),
   ((.exchange 50 31 7),[(.neg 50),(.neg 31),(.pos 7),(.pos 14),(.pos 30)]),
   ((.exchange 55 31 7),[(.neg 55),(.neg 31),(.pos 19),(.pos 25)]),
   ((.exchange 56 31 7),[(.neg 56),(.neg 31),(.pos 20),(.pos 26)]),
   ((.exchange 57 31 7),[(.neg 57),(.neg 31),(.pos 15),(.pos 21),(.pos 27)]),
   ((.exchange 58 31 7),[(.neg 58),(.neg 31),(.pos 22),(.pos 28)]),
   ((.exchange 59 31 7),[(.neg 59),(.neg 31),(.pos 16),(.pos 23),(.pos 29)]),
   ((.exchange 60 31 7),[(.neg 60),(.neg 31),(.pos 17),(.pos 24),(.pos 30)]),
   (.newPoint,[(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 0),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 1),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 2),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 69)]),
   ((.excluded 3),[(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 4),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 5),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 6),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 69)]),
   ((.excluded 7),[(.neg 69),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68)]),
   ((.excluded 8),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64)]),
   ((.excluded 9),[(.neg 69),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 65),(.pos 66),(.pos 67),(.pos 68)]),
   ((.excluded 10),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60)]),
   ((.excluded 11),[(.neg 69),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68)]),
   ((.excluded 12),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64)]),
   ((.excluded 13),[(.neg 69),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 65),(.pos 66),(.pos 67),(.pos 68)]),
   ((.excluded 14),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



theorem witness_0 : ∀ j : Fin 15,
    let w : Fin 15 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 15,
      let w : Fin 15 := ⟨0 + j.val,by omega⟩
      target w < MatroidCatalogue.count 8 4 ∧
        Papers.RationalityTen.MatroidChecked.FastSemanticChecks.RawWitness 8 (N7R4.familyMasks.get 0)
        (fun i : Fin 70 => N8R4.gridMasks.get i.val) newIndex (models w)
        (N8R4.familyMasks.get (target w)) (permutation w) := by
    refine (Fin.forall_fin_add (m := 7) (n := 8) _).2 ⟨?_, ?_⟩
    · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
      · decide +kernel
      · decide +kernel
    · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
      · decide +kernel
      · decide +kernel
  intro j
  have hj := hfast j
  exact ⟨hj.1,Papers.RationalityTen.MatroidChecked.FastSemanticChecks.rawWitness_sound 8 _ _ _ _ _ _ hj.2⟩


end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C0

/- Source: MatroidCatalogue/Cases/N8R4C0Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C0

noncomputable def certificates : List (Origin 70 15 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 15,
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 15) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 8) 4)
    (hold : M.bases.filter ((7 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 8 4, IsomorphicWithin 8 M.bases B := by
  apply extension_covered_of_certificate (n:=7) (r:=4) (by decide)
    catalogue old U newIndex models certificates
    N8R4.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C0.formula []
    exact Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C0.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 8 4 (target w),family_mem 8 4 (target w) hw.1,?_⟩
    exact validWitness_sound 8 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C0

/- Source: MatroidCatalogue/Cases/N8R4C1Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C1

abbrev U := N8R4.grid
noncomputable def old : Finset (Finset (Fin 8)) := N7R4.family 1
noncomputable def newIndexTree : Table ℕ := (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf 35) (.leaf 36)) (.node 3 (.leaf 37) (.leaf 38))) (.node 6 (.node 5 (.leaf 39) (.leaf 40)) (.node 7 (.leaf 41) (.leaf 42)))) (.node 12 (.node 10 (.node 9 (.leaf 43) (.leaf 44)) (.node 11 (.leaf 45) (.leaf 46))) (.node 14 (.node 13 (.leaf 47) (.leaf 48)) (.node 15 (.leaf 49) (.node 16 (.leaf 50) (.leaf 51)))))) (.node 26 (.node 21 (.node 19 (.node 18 (.leaf 52) (.leaf 53)) (.node 20 (.leaf 54) (.leaf 55))) (.node 23 (.node 22 (.leaf 56) (.leaf 57)) (.node 24 (.leaf 58) (.node 25 (.leaf 59) (.leaf 60))))) (.node 30 (.node 28 (.node 27 (.leaf 61) (.leaf 62)) (.node 29 (.leaf 63) (.leaf 64))) (.node 32 (.node 31 (.leaf 65) (.leaf 66)) (.node 33 (.leaf 67) (.node 34 (.leaf 68) (.leaf 69)))))))
noncomputable def newIndex (i : Fin 35) : Fin 70 := Fin.ofNat 70 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 7 (.node 3 (.node 1 (.leaf (7516192768,3,12535432)) (.node 2 (.leaf (528482304,12,12478088)) (.leaf (8044675072,14,14599816)))) (.node 5 (.node 4 (.leaf (516096,12,11789960)) (.leaf (7516708864,14,14141064))) (.node 6 (.leaf (528998400,72,16434824)) (.leaf (8045191168,73,16434824))))) (.node 11 (.node 9 (.node 8 (.leaf (25769803776,1,8345736)) (.leaf (33285996544,4,12535432))) (.node 10 (.leaf (26298286080,13,14599816)) (.leaf (33814478848,15,14599816)))) (.node 13 (.node 12 (.leaf (25770319872,13,14141064)) (.leaf (33286512640,15,14141064))) (.node 14 (.leaf (26298802176,74,16434824)) (.leaf (33814994944,75,16434824))))))

noncomputable def models (i : Fin 15) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 15) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 15) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 70, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (7 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 70, (7 : Fin 8) ∈ U i → ∃ j : Fin 35, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C1

/- Source: MatroidCatalogue/Cases/N8R4C1Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C1


noncomputable def certificates_0 : List (Origin 70 15 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.neg 2)]),
   ((.fixed 3),[(.neg 3)]),
   ((.fixed 4),[(.neg 4)]),
   ((.fixed 5),[(.neg 5)]),
   ((.fixed 6),[(.neg 6)]),
   ((.fixed 7),[(.neg 7)]),
   ((.fixed 8),[(.neg 8)]),
   ((.fixed 9),[(.neg 9)]),
   ((.fixed 10),[(.neg 10)]),
   ((.fixed 11),[(.neg 11)]),
   ((.fixed 12),[(.neg 12)]),
   ((.fixed 13),[(.neg 13)]),
   ((.fixed 14),[(.neg 14)]),
   ((.fixed 15),[(.neg 15)]),
   ((.fixed 16),[(.neg 16)]),
   ((.fixed 17),[(.neg 17)]),
   ((.fixed 18),[(.neg 18)]),
   ((.fixed 19),[(.neg 19)]),
   ((.fixed 20),[(.neg 20)]),
   ((.fixed 21),[(.neg 21)]),
   ((.fixed 22),[(.neg 22)]),
   ((.fixed 23),[(.neg 23)]),
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
   ((.fixed 34),[(.neg 34)]),
   ((.exchange 28 50 6),[(.neg 50),(.neg 28),(.pos 7),(.pos 48)]),
   ((.exchange 28 59 5),[(.neg 59),(.neg 28),(.pos 16),(.pos 58)]),
   ((.exchange 28 60 5),[(.neg 60),(.neg 28),(.pos 17),(.pos 58)]),
   ((.exchange 28 67 3),[(.neg 67),(.neg 28),(.pos 26),(.pos 65)]),
   ((.exchange 28 69 0),[(.neg 69),(.neg 28),(.pos 34),(.pos 68)]),
   ((.exchange 29 50 6),[(.neg 50),(.neg 29),(.pos 8),(.pos 49)]),
   ((.exchange 29 58 5),[(.neg 58),(.neg 29),(.pos 16),(.pos 59)]),
   ((.exchange 29 60 5),[(.neg 60),(.neg 29),(.pos 18),(.pos 59)]),
   ((.exchange 29 61 5),[(.neg 61),(.neg 29),(.pos 16),(.pos 23),(.pos 59)]),
   ((.exchange 29 62 5),[(.neg 62),(.neg 29),(.pos 23),(.pos 59)]),
   ((.exchange 29 63 5),[(.neg 63),(.neg 29),(.pos 18),(.pos 23),(.pos 59)]),
   ((.exchange 29 67 3),[(.neg 67),(.neg 29),(.pos 27),(.pos 66)]),
   ((.exchange 30 48 6),[(.neg 48),(.neg 30),(.pos 7),(.pos 50)]),
   ((.exchange 30 49 6),[(.neg 49),(.neg 30),(.pos 8),(.pos 50)]),
   ((.exchange 30 51 6),[(.neg 51),(.neg 30),(.pos 7),(.pos 14),(.pos 50)]),
   ((.exchange 30 52 6),[(.neg 52),(.neg 30),(.pos 8),(.pos 14),(.pos 50)]),
   ((.exchange 30 53 6),[(.neg 53),(.neg 30),(.pos 14),(.pos 50)]),
   ((.exchange 30 58 5),[(.neg 58),(.neg 30),(.pos 17),(.pos 60)]),
   ((.exchange 30 59 5),[(.neg 59),(.neg 30),(.pos 18),(.pos 60)]),
   ((.exchange 30 61 5),[(.neg 61),(.neg 30),(.pos 17),(.pos 24),(.pos 60)]),
   ((.exchange 30 62 5),[(.neg 62),(.neg 30),(.pos 18),(.pos 24),(.pos 60)]),
   ((.exchange 30 63 5),[(.neg 63),(.neg 30),(.pos 24),(.pos 60)]),
   ((.exchange 30 65 3),[(.neg 65),(.neg 30),(.pos 26),(.pos 67)]),
   ((.exchange 30 66 3),[(.neg 66),(.neg 30),(.pos 27),(.pos 67)]),
   ((.exchange 31 50 6),[(.neg 50),(.neg 31),(.pos 10),(.pos 12),(.pos 51)]),
   ((.exchange 31 59 5),[(.neg 59),(.neg 31),(.pos 19),(.pos 22),(.pos 61)]),
   ((.exchange 31 60 5),[(.neg 60),(.neg 31),(.pos 20),(.pos 22),(.pos 61)]),
   ((.exchange 31 68 0),[(.neg 68),(.neg 31),(.pos 34),(.pos 69)]),
   ((.exchange 32 50 6),[(.neg 50),(.neg 32),(.pos 11),(.pos 13),(.pos 52)]),
   ((.exchange 32 59 5),[(.neg 59),(.neg 32),(.pos 23),(.pos 62)]),
   ((.exchange 32 60 5),[(.neg 60),(.neg 32),(.pos 21),(.pos 23),(.pos 62)]),
   ((.exchange 33 50 6),[(.neg 50),(.neg 33),(.pos 14),(.pos 53)]),
   ((.exchange 33 59 5),[(.neg 59),(.neg 33),(.pos 21),(.pos 24),(.pos 63)]),
   ((.exchange 33 60 5),[(.neg 60),(.neg 33),(.pos 24),(.pos 63)]),
   ((.exchange 35 28 7),[(.neg 35),(.neg 28),(.pos 0),(.pos 5),(.pos 15)]),
   ((.exchange 36 28 7),[(.neg 36),(.neg 28),(.pos 6),(.pos 16)]),
   ((.exchange 37 28 7),[(.neg 37),(.neg 28),(.pos 7),(.pos 17)]),
   ((.exchange 38 28 7),[(.neg 38),(.neg 28),(.pos 0),(.pos 8),(.pos 18)]),
   ((.exchange 39 28 7),[(.neg 39),(.neg 28),(.pos 2),(.pos 9),(.pos 19)]),
   ((.exchange 40 28 7),[(.neg 40),(.neg 28),(.pos 3),(.pos 10),(.pos 20)]),
   ((.exchange 41 28 7),[(.neg 41),(.neg 28),(.pos 1),(.pos 4),(.pos 11),(.pos 21)]),
   ((.exchange 42 28 7),[(.neg 42),(.neg 28),(.pos 12),(.pos 22)]),
   ((.exchange 43 28 7),[(.neg 43),(.neg 28),(.pos 2),(.pos 13),(.pos 23)]),
   ((.exchange 44 28 7),[(.neg 44),(.neg 28),(.pos 3),(.pos 14),(.pos 24)]),
   ((.exchange 45 28 7),[(.neg 45),(.neg 28),(.pos 6),(.pos 25)]),
   ((.exchange 46 28 7),[(.neg 46),(.neg 28),(.pos 7),(.pos 26)]),
   ((.exchange 47 28 7),[(.neg 47),(.neg 28),(.pos 5),(.pos 8),(.pos 27)]),
   ((.exchange 54 28 7),[(.neg 54),(.neg 28),(.pos 12),(.pos 34)]),
   ((.exchange 55 28 7),[(.neg 55),(.neg 28),(.pos 16),(.pos 25)]),
   ((.exchange 56 28 7),[(.neg 56),(.neg 28),(.pos 17),(.pos 26)]),
   ((.exchange 57 28 7),[(.neg 57),(.neg 28),(.pos 15),(.pos 18),(.pos 27)]),
   ((.exchange 64 28 7),[(.neg 64),(.neg 28),(.pos 22),(.pos 34)]),
   (.newPoint,[(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 0),[(.neg 67),(.neg 66),(.neg 65),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 68),(.pos 69)]),
   ((.excluded 1),[(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 2),[(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 64),(.pos 68),(.pos 69)]),
   ((.excluded 3),[(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 4),[(.neg 67),(.neg 66),(.neg 65),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 68),(.pos 69)]),
   ((.excluded 5),[(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 6),[(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 64),(.pos 68),(.pos 69)]),
   ((.excluded 7),[(.neg 69),(.neg 68),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67)]),
   ((.excluded 8),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64)]),
   ((.excluded 9),[(.neg 69),(.neg 68),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 64),(.pos 65),(.pos 66),(.pos 67)]),
   ((.excluded 10),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 64)]),
   ((.excluded 11),[(.neg 69),(.neg 68),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67)]),
   ((.excluded 12),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64)]),
   ((.excluded 13),[(.neg 69),(.neg 68),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 64),(.pos 65),(.pos 66),(.pos 67)]),
   ((.excluded 14),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 64)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



theorem witness_0 : ∀ j : Fin 15,
    let w : Fin 15 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 15,
      let w : Fin 15 := ⟨0 + j.val,by omega⟩
      target w < MatroidCatalogue.count 8 4 ∧
        Papers.RationalityTen.MatroidChecked.FastSemanticChecks.RawWitness 8 (N7R4.familyMasks.get 1)
        (fun i : Fin 70 => N8R4.gridMasks.get i.val) newIndex (models w)
        (N8R4.familyMasks.get (target w)) (permutation w) := by
    refine (Fin.forall_fin_add (m := 7) (n := 8) _).2 ⟨?_, ?_⟩
    · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
      · decide +kernel
      · decide +kernel
    · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
      · decide +kernel
      · decide +kernel
  intro j
  have hj := hfast j
  exact ⟨hj.1,Papers.RationalityTen.MatroidChecked.FastSemanticChecks.rawWitness_sound 8 _ _ _ _ _ _ hj.2⟩


end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C1

/- Source: MatroidCatalogue/Cases/N8R4C1Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C1

noncomputable def certificates : List (Origin 70 15 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 15,
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 15) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 8) 4)
    (hold : M.bases.filter ((7 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 8 4, IsomorphicWithin 8 M.bases B := by
  apply extension_covered_of_certificate (n:=7) (r:=4) (by decide)
    catalogue old U newIndex models certificates
    N8R4.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C1.formula []
    exact Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C1.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 8 4 (target w),family_mem 8 4 (target w) hw.1,?_⟩
    exact validWitness_sound 8 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C1

/- Source: MatroidCatalogue/Cases/N8R4C2Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C2

abbrev U := N8R4.grid
noncomputable def old : Finset (Finset (Fin 8)) := N7R4.family 2
noncomputable def newIndexTree : Table ℕ := (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf 35) (.leaf 36)) (.node 3 (.leaf 37) (.leaf 38))) (.node 6 (.node 5 (.leaf 39) (.leaf 40)) (.node 7 (.leaf 41) (.leaf 42)))) (.node 12 (.node 10 (.node 9 (.leaf 43) (.leaf 44)) (.node 11 (.leaf 45) (.leaf 46))) (.node 14 (.node 13 (.leaf 47) (.leaf 48)) (.node 15 (.leaf 49) (.node 16 (.leaf 50) (.leaf 51)))))) (.node 26 (.node 21 (.node 19 (.node 18 (.leaf 52) (.leaf 53)) (.node 20 (.leaf 54) (.leaf 55))) (.node 23 (.node 22 (.leaf 56) (.leaf 57)) (.node 24 (.leaf 58) (.node 25 (.leaf 59) (.leaf 60))))) (.node 30 (.node 28 (.node 27 (.leaf 61) (.leaf 62)) (.node 29 (.leaf 63) (.leaf 64))) (.node 32 (.node 31 (.leaf 65) (.leaf 66)) (.node 33 (.leaf 67) (.node 34 (.leaf 68) (.leaf 69)))))))
noncomputable def newIndex (i : Fin 35) : Fin 70 := Fin.ofNat 70 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (24696061952,4,10442376)) (.leaf (1065353216,13,10349192))) (.node 3 (.leaf (25761415168,17,14599816)) (.leaf (1040384,13,9431688)))) (.node 6 (.node 5 (.leaf (24697102336,17,14141064)) (.leaf (1066393600,76,16434824))) (.node 7 (.leaf (25762455552,77,16434824)) (.node 8 (.leaf (25769803776,2,8345736)) (.leaf (16106127360,4,10435208)))))) (.node 14 (.node 11 (.node 10 (.leaf (33285996544,5,12535432)) (.leaf (26835156992,16,12478088))) (.node 12 (.leaf (17171480576,17,14596232)) (.node 13 (.leaf (34351349760,18,14599816)) (.leaf (25770844160,16,11789960))))) (.node 16 (.node 15 (.leaf (16107167744,17,14137480)) (.leaf (33287036928,18,14141064))) (.node 17 (.leaf (26836197376,78,16434824)) (.node 18 (.leaf (17172520960,77,16431240)) (.leaf (34352390144,79,16434824)))))))

noncomputable def models (i : Fin 19) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 19) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 19) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 70, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (7 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 70, (7 : Fin 8) ∈ U i → ∃ j : Fin 35, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C2

/- Source: MatroidCatalogue/Cases/N8R4C2Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C2


noncomputable def certificates_0 : List (Origin 70 19 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.neg 2)]),
   ((.fixed 3),[(.neg 3)]),
   ((.fixed 4),[(.neg 4)]),
   ((.fixed 5),[(.neg 5)]),
   ((.fixed 6),[(.neg 6)]),
   ((.fixed 7),[(.neg 7)]),
   ((.fixed 8),[(.neg 8)]),
   ((.fixed 9),[(.neg 9)]),
   ((.fixed 10),[(.neg 10)]),
   ((.fixed 11),[(.neg 11)]),
   ((.fixed 12),[(.neg 12)]),
   ((.fixed 13),[(.neg 13)]),
   ((.fixed 14),[(.neg 14)]),
   ((.fixed 15),[(.neg 15)]),
   ((.fixed 16),[(.neg 16)]),
   ((.fixed 17),[(.neg 17)]),
   ((.fixed 18),[(.neg 18)]),
   ((.fixed 19),[(.neg 19)]),
   ((.fixed 20),[(.neg 20)]),
   ((.fixed 21),[(.neg 21)]),
   ((.fixed 22),[(.neg 22)]),
   ((.fixed 23),[(.neg 23)]),
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
   ((.exchange 28 50 6),[(.neg 50),(.neg 28),(.pos 7),(.pos 48)]),
   ((.exchange 28 59 5),[(.neg 59),(.neg 28),(.pos 16),(.pos 58)]),
   ((.exchange 28 60 5),[(.neg 60),(.neg 28),(.pos 17),(.pos 58)]),
   ((.exchange 28 61 5),[(.neg 61),(.neg 28),(.pos 22),(.pos 58)]),
   ((.exchange 28 62 5),[(.neg 62),(.neg 28),(.pos 16),(.pos 22),(.pos 58)]),
   ((.exchange 28 63 5),[(.neg 63),(.neg 28),(.pos 17),(.pos 22),(.pos 58)]),
   ((.exchange 28 64 5),[(.neg 64),(.neg 28),(.pos 22),(.pos 58)]),
   ((.exchange 28 67 3),[(.neg 67),(.neg 28),(.pos 26),(.pos 65)]),
   ((.exchange 29 50 6),[(.neg 50),(.neg 29),(.pos 8),(.pos 49)]),
   ((.exchange 29 58 5),[(.neg 58),(.neg 29),(.pos 16),(.pos 59)]),
   ((.exchange 29 60 5),[(.neg 60),(.neg 29),(.pos 18),(.pos 59)]),
   ((.exchange 29 61 5),[(.neg 61),(.neg 29),(.pos 16),(.pos 23),(.pos 59)]),
   ((.exchange 29 62 5),[(.neg 62),(.neg 29),(.pos 23),(.pos 59)]),
   ((.exchange 29 63 5),[(.neg 63),(.neg 29),(.pos 18),(.pos 23),(.pos 59)]),
   ((.exchange 29 64 5),[(.neg 64),(.neg 29),(.pos 23),(.pos 59)]),
   ((.exchange 29 67 3),[(.neg 67),(.neg 29),(.pos 27),(.pos 66)]),
   ((.exchange 30 48 6),[(.neg 48),(.neg 30),(.pos 7),(.pos 50)]),
   ((.exchange 30 49 6),[(.neg 49),(.neg 30),(.pos 8),(.pos 50)]),
   ((.exchange 30 51 6),[(.neg 51),(.neg 30),(.pos 7),(.pos 14),(.pos 50)]),
   ((.exchange 30 52 6),[(.neg 52),(.neg 30),(.pos 8),(.pos 14),(.pos 50)]),
   ((.exchange 30 53 6),[(.neg 53),(.neg 30),(.pos 14),(.pos 50)]),
   ((.exchange 30 54 6),[(.neg 54),(.neg 30),(.pos 14),(.pos 50)]),
   ((.exchange 30 58 5),[(.neg 58),(.neg 30),(.pos 17),(.pos 60)]),
   ((.exchange 30 59 5),[(.neg 59),(.neg 30),(.pos 18),(.pos 60)]),
   ((.exchange 30 61 5),[(.neg 61),(.neg 30),(.pos 17),(.pos 24),(.pos 60)]),
   ((.exchange 30 62 5),[(.neg 62),(.neg 30),(.pos 18),(.pos 24),(.pos 60)]),
   ((.exchange 30 63 5),[(.neg 63),(.neg 30),(.pos 24),(.pos 60)]),
   ((.exchange 30 64 5),[(.neg 64),(.neg 30),(.pos 24),(.pos 60)]),
   ((.exchange 30 65 3),[(.neg 65),(.neg 30),(.pos 26),(.pos 67)]),
   ((.exchange 30 66 3),[(.neg 66),(.neg 30),(.pos 27),(.pos 67)]),
   ((.exchange 31 50 6),[(.neg 50),(.neg 31),(.pos 10),(.pos 12),(.pos 51)]),
   ((.exchange 31 58 5),[(.neg 58),(.neg 31),(.pos 22),(.pos 61)]),
   ((.exchange 31 59 5),[(.neg 59),(.neg 31),(.pos 19),(.pos 22),(.pos 61)]),
   ((.exchange 31 60 5),[(.neg 60),(.neg 31),(.pos 20),(.pos 22),(.pos 61)]),
   ((.exchange 32 50 6),[(.neg 50),(.neg 32),(.pos 11),(.pos 13),(.pos 52)]),
   ((.exchange 32 58 5),[(.neg 58),(.neg 32),(.pos 19),(.pos 23),(.pos 62)]),
   ((.exchange 32 59 5),[(.neg 59),(.neg 32),(.pos 23),(.pos 62)]),
   ((.exchange 32 60 5),[(.neg 60),(.neg 32),(.pos 21),(.pos 23),(.pos 62)]),
   ((.exchange 33 50 6),[(.neg 50),(.neg 33),(.pos 14),(.pos 53)]),
   ((.exchange 33 58 5),[(.neg 58),(.neg 33),(.pos 20),(.pos 24),(.pos 63)]),
   ((.exchange 33 59 5),[(.neg 59),(.neg 33),(.pos 21),(.pos 24),(.pos 63)]),
   ((.exchange 33 60 5),[(.neg 60),(.neg 33),(.pos 24),(.pos 63)]),
   ((.exchange 34 50 6),[(.neg 50),(.neg 34),(.pos 14),(.pos 54)]),
   ((.exchange 34 58 5),[(.neg 58),(.neg 34),(.pos 22),(.pos 64)]),
   ((.exchange 34 59 5),[(.neg 59),(.neg 34),(.pos 23),(.pos 64)]),
   ((.exchange 34 60 5),[(.neg 60),(.neg 34),(.pos 24),(.pos 64)]),
   ((.exchange 35 28 7),[(.neg 35),(.neg 28),(.pos 0),(.pos 5),(.pos 15)]),
   ((.exchange 36 28 7),[(.neg 36),(.neg 28),(.pos 6),(.pos 16)]),
   ((.exchange 37 28 7),[(.neg 37),(.neg 28),(.pos 7),(.pos 17)]),
   ((.exchange 38 28 7),[(.neg 38),(.neg 28),(.pos 0),(.pos 8),(.pos 18)]),
   ((.exchange 39 28 7),[(.neg 39),(.neg 28),(.pos 2),(.pos 9),(.pos 19)]),
   ((.exchange 40 28 7),[(.neg 40),(.neg 28),(.pos 3),(.pos 10),(.pos 20)]),
   ((.exchange 41 28 7),[(.neg 41),(.neg 28),(.pos 1),(.pos 4),(.pos 11),(.pos 21)]),
   ((.exchange 42 28 7),[(.neg 42),(.neg 28),(.pos 12),(.pos 22)]),
   ((.exchange 43 28 7),[(.neg 43),(.neg 28),(.pos 2),(.pos 13),(.pos 23)]),
   ((.exchange 44 28 7),[(.neg 44),(.neg 28),(.pos 3),(.pos 14),(.pos 24)]),
   ((.exchange 45 28 7),[(.neg 45),(.neg 28),(.pos 6),(.pos 25)]),
   ((.exchange 46 28 7),[(.neg 46),(.neg 28),(.pos 7),(.pos 26)]),
   ((.exchange 47 28 7),[(.neg 47),(.neg 28),(.pos 5),(.pos 8),(.pos 27)]),
   ((.exchange 55 28 7),[(.neg 55),(.neg 28),(.pos 16),(.pos 25)]),
   ((.exchange 56 28 7),[(.neg 56),(.neg 28),(.pos 17),(.pos 26)]),
   ((.exchange 57 28 7),[(.neg 57),(.neg 28),(.pos 15),(.pos 18),(.pos 27)]),
   ((.exchange 66 34 1),[(.neg 66),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 67 54 2),[(.neg 67),(.neg 54),(.pos 68),(.pos 69)]),
   ((.exchange 68 32 3),[(.neg 68),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 68 33 3),[(.neg 68),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 68 51 3),[(.neg 68),(.neg 51),(.pos 65),(.pos 69)]),
   ((.exchange 68 53 3),[(.neg 68),(.neg 53),(.pos 67),(.pos 69)]),
   ((.exchange 69 28 4),[(.neg 69),(.neg 28),(.pos 65),(.pos 68)]),
   ((.exchange 69 30 4),[(.neg 69),(.neg 30),(.pos 67),(.pos 68)]),
   (.newPoint,[(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 0),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 68)]),
   ((.excluded 1),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 2),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 68)]),
   ((.excluded 3),[(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 4),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 68)]),
   ((.excluded 5),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 6),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57),(.pos 68)]),
   ((.excluded 7),[(.neg 69),(.neg 68),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67)]),
   ((.excluded 8),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 9),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64)]),
   ((.excluded 10),[(.neg 69),(.neg 68),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 65),(.pos 66),(.pos 67)]),
   ((.excluded 11),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 69)]),
   ((.excluded 12),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 13),[(.neg 69),(.neg 68),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67)]),
   ((.excluded 14),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 15),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64)]),
   ((.excluded 16),[(.neg 69),(.neg 68),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57),(.pos 65),(.pos 66),(.pos 67)]),
   ((.excluded 17),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57),(.pos 69)]),
   ((.excluded 18),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



theorem witness_0 : ∀ j : Fin 19,
    let w : Fin 19 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 19,
      let w : Fin 19 := ⟨0 + j.val,by omega⟩
      target w < MatroidCatalogue.count 8 4 ∧
        Papers.RationalityTen.MatroidChecked.FastSemanticChecks.RawWitness 8 (N7R4.familyMasks.get 2)
        (fun i : Fin 70 => N8R4.gridMasks.get i.val) newIndex (models w)
        (N8R4.familyMasks.get (target w)) (permutation w) := by
    refine (Fin.forall_fin_add (m := 9) (n := 10) _).2 ⟨?_, ?_⟩
    · refine (Fin.forall_fin_add (m := 4) (n := 5) _).2 ⟨?_, ?_⟩
      · decide +kernel
      · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
        · decide +kernel
        · decide +kernel
    · refine (Fin.forall_fin_add (m := 5) (n := 5) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
        · decide +kernel
        · decide +kernel
      · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
        · decide +kernel
        · decide +kernel
  intro j
  have hj := hfast j
  exact ⟨hj.1,Papers.RationalityTen.MatroidChecked.FastSemanticChecks.rawWitness_sound 8 _ _ _ _ _ _ hj.2⟩


end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C2

/- Source: MatroidCatalogue/Cases/N8R4C2Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C2

noncomputable def certificates : List (Origin 70 19 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 19,
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 19) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 8) 4)
    (hold : M.bases.filter ((7 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 8 4, IsomorphicWithin 8 M.bases B := by
  apply extension_covered_of_certificate (n:=7) (r:=4) (by decide)
    catalogue old U newIndex models certificates
    N8R4.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C2.formula []
    exact Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C2.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 8 4 (target w),family_mem 8 4 (target w) hw.1,?_⟩
    exact validWitness_sound 8 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C2


end
end
end BundlePart2

section BundlePart3
/- Source: MatroidChecked/SemanticChunks/Cases02Part03.lean -/






@[expose] public section
noncomputable section

/- Source: MatroidCatalogue/Cases/N8R4C3Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C3

abbrev U := N8R4.grid
noncomputable def old : Finset (Finset (Fin 8)) := N7R4.family 3
noncomputable def newIndexTree : Table ℕ := (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf 35) (.leaf 36)) (.node 3 (.leaf 37) (.leaf 38))) (.node 6 (.node 5 (.leaf 39) (.leaf 40)) (.node 7 (.leaf 41) (.leaf 42)))) (.node 12 (.node 10 (.node 9 (.leaf 43) (.leaf 44)) (.node 11 (.leaf 45) (.leaf 46))) (.node 14 (.node 13 (.leaf 47) (.leaf 48)) (.node 15 (.leaf 49) (.node 16 (.leaf 50) (.leaf 51)))))) (.node 26 (.node 21 (.node 19 (.node 18 (.leaf 52) (.leaf 53)) (.node 20 (.leaf 54) (.leaf 55))) (.node 23 (.node 22 (.leaf 56) (.leaf 57)) (.node 24 (.leaf 58) (.node 25 (.leaf 59) (.leaf 60))))) (.node 30 (.node 28 (.node 27 (.leaf 61) (.leaf 62)) (.node 29 (.leaf 63) (.leaf 64))) (.node 32 (.node 31 (.leaf 65) (.leaf 66)) (.node 33 (.leaf 67) (.node 34 (.leaf 68) (.leaf 69)))))))
noncomputable def newIndex (i : Fin 35) : Fin 70 := Fin.ofNat 70 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (30064771072,4,6248648)) (.leaf (20401094656,4,6246947))) (.node 3 (.leaf (16106127360,6,12535432)) (.leaf (33285996544,7,12535432)))) (.node 6 (.node 5 (.leaf (1038090240,19,12478088)) (.leaf (31102861312,20,14599816))) (.node 7 (.leaf (21439184896,20,14598682)) (.node 8 (.leaf (17144217600,21,14599816)) (.leaf (34324086784,22,14599816)))))) (.node 14 (.node 11 (.node 10 (.leaf (1013760,19,11789960)) (.leaf (30065784832,20,14141064))) (.node 12 (.leaf (20402108416,20,14139930)) (.node 13 (.leaf (16107141120,21,14141064)) (.leaf (33287010304,22,14141064))))) (.node 16 (.node 15 (.leaf (1039104000,80,16434824)) (.leaf (31103875072,81,16434824))) (.node 17 (.leaf (21440198656,81,16433690)) (.node 18 (.leaf (17145231360,82,16434824)) (.leaf (34325100544,83,16434824)))))))

noncomputable def models (i : Fin 19) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 19) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 19) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 70, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (7 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 70, (7 : Fin 8) ∈ U i → ∃ j : Fin 35, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C3

/- Source: MatroidCatalogue/Cases/N8R4C3Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C3


noncomputable def certificates_0 : List (Origin 70 19 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.neg 2)]),
   ((.fixed 3),[(.neg 3)]),
   ((.fixed 4),[(.neg 4)]),
   ((.fixed 5),[(.neg 5)]),
   ((.fixed 6),[(.neg 6)]),
   ((.fixed 7),[(.neg 7)]),
   ((.fixed 8),[(.neg 8)]),
   ((.fixed 9),[(.neg 9)]),
   ((.fixed 10),[(.neg 10)]),
   ((.fixed 11),[(.neg 11)]),
   ((.fixed 12),[(.neg 12)]),
   ((.fixed 13),[(.neg 13)]),
   ((.fixed 14),[(.neg 14)]),
   ((.fixed 15),[(.neg 15)]),
   ((.fixed 16),[(.neg 16)]),
   ((.fixed 17),[(.neg 17)]),
   ((.fixed 18),[(.neg 18)]),
   ((.fixed 19),[(.neg 19)]),
   ((.fixed 20),[(.neg 20)]),
   ((.fixed 21),[(.neg 21)]),
   ((.fixed 22),[(.neg 22)]),
   ((.fixed 23),[(.neg 23)]),
   ((.fixed 24),[(.neg 24)]),
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
   ((.exchange 26 47 6),[(.neg 47),(.neg 26),(.pos 5),(.pos 46)]),
   ((.exchange 26 48 6),[(.neg 48),(.neg 26),(.pos 7),(.pos 46)]),
   ((.exchange 26 49 6),[(.neg 49),(.neg 26),(.pos 5),(.pos 7),(.pos 46)]),
   ((.exchange 26 51 6),[(.neg 51),(.neg 26),(.pos 10),(.pos 46)]),
   ((.exchange 26 52 6),[(.neg 52),(.neg 26),(.pos 5),(.pos 10),(.pos 46)]),
   ((.exchange 26 53 6),[(.neg 53),(.neg 26),(.pos 10),(.pos 46)]),
   ((.exchange 26 54 6),[(.neg 54),(.neg 26),(.pos 7),(.pos 10),(.pos 46)]),
   ((.exchange 26 57 5),[(.neg 57),(.neg 26),(.pos 15),(.pos 56)]),
   ((.exchange 26 58 5),[(.neg 58),(.neg 26),(.pos 17),(.pos 56)]),
   ((.exchange 26 59 5),[(.neg 59),(.neg 26),(.pos 15),(.pos 17),(.pos 56)]),
   ((.exchange 26 61 5),[(.neg 61),(.neg 26),(.pos 20),(.pos 56)]),
   ((.exchange 26 62 5),[(.neg 62),(.neg 26),(.pos 15),(.pos 20),(.pos 56)]),
   ((.exchange 26 63 5),[(.neg 63),(.neg 26),(.pos 20),(.pos 56)]),
   ((.exchange 26 64 5),[(.neg 64),(.neg 26),(.pos 17),(.pos 20),(.pos 56)]),
   ((.exchange 26 66 2),[(.neg 66),(.neg 26),(.pos 25),(.pos 65)]),
   ((.exchange 26 68 0),[(.neg 68),(.neg 26),(.pos 30),(.pos 67)]),
   ((.exchange 27 46 6),[(.neg 46),(.neg 27),(.pos 5),(.pos 47)]),
   ((.exchange 27 48 6),[(.neg 48),(.neg 27),(.pos 5),(.pos 8),(.pos 47)]),
   ((.exchange 27 49 6),[(.neg 49),(.neg 27),(.pos 8),(.pos 47)]),
   ((.exchange 27 51 6),[(.neg 51),(.neg 27),(.pos 5),(.pos 11),(.pos 47)]),
   ((.exchange 27 52 6),[(.neg 52),(.neg 27),(.pos 11),(.pos 47)]),
   ((.exchange 27 53 6),[(.neg 53),(.neg 27),(.pos 11),(.pos 47)]),
   ((.exchange 27 54 6),[(.neg 54),(.neg 27),(.pos 8),(.pos 11),(.pos 47)]),
   ((.exchange 27 56 5),[(.neg 56),(.neg 27),(.pos 15),(.pos 57)]),
   ((.exchange 27 65 2),[(.neg 65),(.neg 27),(.pos 25),(.pos 66)]),
   ((.exchange 28 46 6),[(.neg 46),(.neg 28),(.pos 7),(.pos 48)]),
   ((.exchange 28 47 6),[(.neg 47),(.neg 28),(.pos 6),(.pos 7),(.pos 48)]),
   ((.exchange 28 49 6),[(.neg 49),(.neg 28),(.pos 6),(.pos 48)]),
   ((.exchange 28 51 6),[(.neg 51),(.neg 28),(.pos 12),(.pos 48)]),
   ((.exchange 28 52 6),[(.neg 52),(.neg 28),(.pos 6),(.pos 12),(.pos 48)]),
   ((.exchange 28 53 6),[(.neg 53),(.neg 28),(.pos 7),(.pos 12),(.pos 48)]),
   ((.exchange 28 54 6),[(.neg 54),(.neg 28),(.pos 12),(.pos 48)]),
   ((.exchange 28 56 5),[(.neg 56),(.neg 28),(.pos 17),(.pos 58)]),
   ((.exchange 28 67 0),[(.neg 67),(.neg 28),(.pos 30),(.pos 68)]),
   ((.exchange 29 46 6),[(.neg 46),(.neg 29),(.pos 6),(.pos 8),(.pos 49)]),
   ((.exchange 29 47 6),[(.neg 47),(.neg 29),(.pos 8),(.pos 49)]),
   ((.exchange 29 48 6),[(.neg 48),(.neg 29),(.pos 6),(.pos 49)]),
   ((.exchange 29 56 5),[(.neg 56),(.neg 29),(.pos 16),(.pos 18),(.pos 59)]),
   ((.exchange 31 46 6),[(.neg 46),(.neg 31),(.pos 10),(.pos 51)]),
   ((.exchange 31 47 6),[(.neg 47),(.neg 31),(.pos 9),(.pos 10),(.pos 51)]),
   ((.exchange 31 48 6),[(.neg 48),(.neg 31),(.pos 12),(.pos 51)]),
   ((.exchange 31 56 5),[(.neg 56),(.neg 31),(.pos 20),(.pos 61)]),
   ((.exchange 32 46 6),[(.neg 46),(.neg 32),(.pos 9),(.pos 11),(.pos 52)]),
   ((.exchange 32 47 6),[(.neg 47),(.neg 32),(.pos 11),(.pos 52)]),
   ((.exchange 32 48 6),[(.neg 48),(.neg 32),(.pos 9),(.pos 13),(.pos 52)]),
   ((.exchange 32 56 5),[(.neg 56),(.neg 32),(.pos 19),(.pos 21),(.pos 62)]),
   ((.exchange 33 46 6),[(.neg 46),(.neg 33),(.pos 10),(.pos 53)]),
   ((.exchange 33 47 6),[(.neg 47),(.neg 33),(.pos 11),(.pos 53)]),
   ((.exchange 33 48 6),[(.neg 48),(.neg 33),(.pos 10),(.pos 14),(.pos 53)]),
   ((.exchange 33 56 5),[(.neg 56),(.neg 33),(.pos 20),(.pos 63)]),
   ((.exchange 34 46 6),[(.neg 46),(.neg 34),(.pos 12),(.pos 14),(.pos 54)]),
   ((.exchange 34 47 6),[(.neg 47),(.neg 34),(.pos 13),(.pos 14),(.pos 54)]),
   ((.exchange 34 48 6),[(.neg 48),(.neg 34),(.pos 12),(.pos 54)]),
   ((.exchange 34 56 5),[(.neg 56),(.neg 34),(.pos 22),(.pos 24),(.pos 64)]),
   ((.exchange 35 26 7),[(.neg 35),(.neg 26),(.pos 5),(.pos 15)]),
   ((.exchange 36 26 7),[(.neg 36),(.neg 26),(.pos 0),(.pos 6),(.pos 16)]),
   ((.exchange 37 26 7),[(.neg 37),(.neg 26),(.pos 7),(.pos 17)]),
   ((.exchange 38 26 7),[(.neg 38),(.neg 26),(.pos 0),(.pos 8),(.pos 18)]),
   ((.exchange 39 26 7),[(.neg 39),(.neg 26),(.pos 1),(.pos 9),(.pos 19)]),
   ((.exchange 40 26 7),[(.neg 40),(.neg 26),(.pos 10),(.pos 20)]),
   ((.exchange 41 26 7),[(.neg 41),(.neg 26),(.pos 1),(.pos 11),(.pos 21)]),
   ((.exchange 42 26 7),[(.neg 42),(.neg 26),(.pos 3),(.pos 12),(.pos 22)]),
   ((.exchange 43 26 7),[(.neg 43),(.neg 26),(.pos 2),(.pos 4),(.pos 13),(.pos 23)]),
   ((.exchange 44 26 7),[(.neg 44),(.neg 26),(.pos 3),(.pos 14),(.pos 24)]),
   ((.exchange 45 26 7),[(.neg 45),(.neg 26),(.pos 5),(.pos 25)]),
   ((.exchange 50 26 7),[(.neg 50),(.neg 26),(.pos 7),(.pos 30)]),
   ((.exchange 55 26 7),[(.neg 55),(.neg 26),(.pos 15),(.pos 25)]),
   ((.exchange 60 26 7),[(.neg 60),(.neg 26),(.pos 17),(.pos 30)]),
   ((.exchange 65 33 0),[(.neg 65),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 65 34 0),[(.neg 65),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 65 54 0),[(.neg 65),(.neg 54),(.pos 68),(.pos 69)]),
   ((.exchange 66 33 1),[(.neg 66),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 66 34 1),[(.neg 66),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 66 54 1),[(.neg 66),(.neg 54),(.pos 68),(.pos 69)]),
   ((.exchange 67 61 2),[(.neg 67),(.neg 61),(.pos 65),(.pos 69)]),
   ((.exchange 67 62 2),[(.neg 67),(.neg 62),(.pos 66),(.pos 69)]),
   ((.exchange 68 31 3),[(.neg 68),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 68 32 3),[(.neg 68),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 69 26 4),[(.neg 69),(.neg 26),(.pos 65),(.pos 67)]),
   ((.exchange 69 27 4),[(.neg 69),(.neg 27),(.pos 66),(.pos 67)]),
   ((.exchange 69 46 4),[(.neg 69),(.neg 46),(.pos 65),(.pos 67)]),
   ((.exchange 69 47 4),[(.neg 69),(.neg 47),(.pos 66),(.pos 67)]),
   (.newPoint,[(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 0),[(.neg 69),(.neg 68),(.neg 67),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66)]),
   ((.excluded 1),[(.neg 69),(.neg 66),(.neg 65),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 67),(.pos 68)]),
   ((.excluded 2),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 3),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64)]),
   ((.excluded 4),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 5),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 65),(.pos 66)]),
   ((.excluded 6),[(.neg 69),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 67),(.pos 68)]),
   ((.excluded 7),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 69)]),
   ((.excluded 8),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 60)]),
   ((.excluded 9),[(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 50),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_1 : List (Origin 70 19 × List Sat.Literal) :=
  [((.excluded 10),[(.neg 69),(.neg 68),(.neg 67),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 50),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66)]),
   ((.excluded 11),[(.neg 69),(.neg 66),(.neg 65),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 50),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 67),(.pos 68)]),
   ((.excluded 12),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 50),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 13),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 50),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64)]),
   ((.excluded 14),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 50),(.pos 55),(.pos 60),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 15),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 50),(.pos 55),(.pos 60),(.pos 65),(.pos 66)]),
   ((.excluded 16),[(.neg 69),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 50),(.pos 55),(.pos 60),(.pos 67),(.pos 68)]),
   ((.excluded 17),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 50),(.pos 55),(.pos 60),(.pos 69)]),
   ((.excluded 18),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 50),(.pos 55),(.pos 60)])]

theorem certificates_1_valid : ∀ oc ∈ certificates_1,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



theorem witness_0 : ∀ j : Fin 19,
    let w : Fin 19 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 19,
      let w : Fin 19 := ⟨0 + j.val,by omega⟩
      target w < MatroidCatalogue.count 8 4 ∧
        Papers.RationalityTen.MatroidChecked.FastSemanticChecks.RawWitness 8 (N7R4.familyMasks.get 3)
        (fun i : Fin 70 => N8R4.gridMasks.get i.val) newIndex (models w)
        (N8R4.familyMasks.get (target w)) (permutation w) := by
    refine (Fin.forall_fin_add (m := 9) (n := 10) _).2 ⟨?_, ?_⟩
    · refine (Fin.forall_fin_add (m := 4) (n := 5) _).2 ⟨?_, ?_⟩
      · decide +kernel
      · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
        · decide +kernel
        · decide +kernel
    · refine (Fin.forall_fin_add (m := 5) (n := 5) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
        · decide +kernel
        · decide +kernel
      · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
        · decide +kernel
        · decide +kernel
  intro j
  have hj := hfast j
  exact ⟨hj.1,Papers.RationalityTen.MatroidChecked.FastSemanticChecks.rawWitness_sound 8 _ _ _ _ _ _ hj.2⟩


end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C3

/- Source: MatroidCatalogue/Cases/N8R4C3Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C3

noncomputable def certificates : List (Origin 70 19 × List Sat.Literal) :=
  certificates_0 ++ certificates_1

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  intro oc hoc
  simp only [certificates,List.mem_append,or_assoc] at hoc
  rcases hoc with h0 | h1
  · exact certificates_0_valid oc h0
  · exact certificates_1_valid oc h1

theorem models_valid : ∀ w : Fin 19,
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 19) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 8) 4)
    (hold : M.bases.filter ((7 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 8 4, IsomorphicWithin 8 M.bases B := by
  apply extension_covered_of_certificate (n:=7) (r:=4) (by decide)
    catalogue old U newIndex models certificates
    N8R4.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C3.formula []
    exact Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C3.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 8 4 (target w),family_mem 8 4 (target w) hw.1,?_⟩
    exact validWitness_sound 8 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C3

/- Source: MatroidCatalogue/Cases/N8R4C4Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C4

abbrev U := N8R4.grid
noncomputable def old : Finset (Finset (Fin 8)) := N7R4.family 4
noncomputable def newIndexTree : Table ℕ := (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf 35) (.leaf 36)) (.node 3 (.leaf 37) (.leaf 38))) (.node 6 (.node 5 (.leaf 39) (.leaf 40)) (.node 7 (.leaf 41) (.leaf 42)))) (.node 12 (.node 10 (.node 9 (.leaf 43) (.leaf 44)) (.node 11 (.leaf 45) (.leaf 46))) (.node 14 (.node 13 (.leaf 47) (.leaf 48)) (.node 15 (.leaf 49) (.node 16 (.leaf 50) (.leaf 51)))))) (.node 26 (.node 21 (.node 19 (.node 18 (.leaf 52) (.leaf 53)) (.node 20 (.leaf 54) (.leaf 55))) (.node 23 (.node 22 (.leaf 56) (.leaf 57)) (.node 24 (.leaf 58) (.node 25 (.leaf 59) (.leaf 60))))) (.node 30 (.node 28 (.node 27 (.leaf 61) (.leaf 62)) (.node 29 (.leaf 63) (.leaf 64))) (.node 32 (.node 31 (.leaf 65) (.leaf 66)) (.node 33 (.leaf 67) (.node 34 (.leaf 68) (.leaf 69)))))))
noncomputable def newIndex (i : Fin 35) : Fin 70 := Fin.ofNat 70 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 11 (.node 5 (.node 2 (.node 1 (.leaf (30064771072,5,6248648)) (.leaf (28991029248,7,8345736))) (.node 3 (.leaf (24696061952,7,8344840)) (.node 4 (.leaf (16106127360,7,8334088)) (.leaf (33285996544,8,12535432))))) (.node 8 (.node 6 (.leaf (1071644672,23,14599816)) (.node 7 (.leaf (31136415744,24,14599816)) (.leaf (30062673920,25,14599816)))) (.node 9 (.leaf (25767706624,25,14599368)) (.node 10 (.leaf (17177772032,25,14592200)) (.leaf (34357641216,26,14599816)))))) (.node 17 (.node 14 (.node 12 (.leaf (1046528,23,14141064)) (.node 13 (.leaf (30065817600,24,14141064)) (.leaf (28992075776,25,14141064)))) (.node 15 (.leaf (24697108480,25,14140616)) (.node 16 (.leaf (16107173888,25,14133448)) (.leaf (33287043072,26,14141064))))) (.node 20 (.node 18 (.leaf (1072691200,84,16434824)) (.node 19 (.leaf (31137462272,85,16434824)) (.leaf (30063720448,86,16434824)))) (.node 21 (.leaf (25768753152,86,16434376)) (.node 22 (.leaf (17178818560,86,16427208)) (.leaf (34358687744,87,16434824)))))))

noncomputable def models (i : Fin 23) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 23) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 23) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 70, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (7 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 70, (7 : Fin 8) ∈ U i → ∃ j : Fin 35, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C4

/- Source: MatroidCatalogue/Cases/N8R4C4Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C4


noncomputable def certificates_0 : List (Origin 70 23 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.neg 2)]),
   ((.fixed 3),[(.neg 3)]),
   ((.fixed 4),[(.neg 4)]),
   ((.fixed 5),[(.neg 5)]),
   ((.fixed 6),[(.neg 6)]),
   ((.fixed 7),[(.neg 7)]),
   ((.fixed 8),[(.neg 8)]),
   ((.fixed 9),[(.neg 9)]),
   ((.fixed 10),[(.neg 10)]),
   ((.fixed 11),[(.neg 11)]),
   ((.fixed 12),[(.neg 12)]),
   ((.fixed 13),[(.neg 13)]),
   ((.fixed 14),[(.neg 14)]),
   ((.fixed 15),[(.neg 15)]),
   ((.fixed 16),[(.neg 16)]),
   ((.fixed 17),[(.neg 17)]),
   ((.fixed 18),[(.neg 18)]),
   ((.fixed 19),[(.neg 19)]),
   ((.fixed 20),[(.neg 20)]),
   ((.fixed 21),[(.neg 21)]),
   ((.fixed 22),[(.neg 22)]),
   ((.fixed 23),[(.neg 23)]),
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
   ((.exchange 26 47 6),[(.neg 47),(.neg 26),(.pos 5),(.pos 46)]),
   ((.exchange 26 48 6),[(.neg 48),(.neg 26),(.pos 7),(.pos 46)]),
   ((.exchange 26 49 6),[(.neg 49),(.neg 26),(.pos 5),(.pos 7),(.pos 46)]),
   ((.exchange 26 50 6),[(.neg 50),(.neg 26),(.pos 7),(.pos 46)]),
   ((.exchange 26 51 6),[(.neg 51),(.neg 26),(.pos 10),(.pos 46)]),
   ((.exchange 26 52 6),[(.neg 52),(.neg 26),(.pos 5),(.pos 10),(.pos 46)]),
   ((.exchange 26 53 6),[(.neg 53),(.neg 26),(.pos 10),(.pos 46)]),
   ((.exchange 26 54 6),[(.neg 54),(.neg 26),(.pos 7),(.pos 10),(.pos 46)]),
   ((.exchange 26 57 5),[(.neg 57),(.neg 26),(.pos 15),(.pos 56)]),
   ((.exchange 26 58 5),[(.neg 58),(.neg 26),(.pos 17),(.pos 56)]),
   ((.exchange 26 59 5),[(.neg 59),(.neg 26),(.pos 15),(.pos 17),(.pos 56)]),
   ((.exchange 26 60 5),[(.neg 60),(.neg 26),(.pos 17),(.pos 56)]),
   ((.exchange 26 61 5),[(.neg 61),(.neg 26),(.pos 20),(.pos 56)]),
   ((.exchange 26 62 5),[(.neg 62),(.neg 26),(.pos 15),(.pos 20),(.pos 56)]),
   ((.exchange 26 63 5),[(.neg 63),(.neg 26),(.pos 20),(.pos 56)]),
   ((.exchange 26 64 5),[(.neg 64),(.neg 26),(.pos 17),(.pos 20),(.pos 56)]),
   ((.exchange 26 66 2),[(.neg 66),(.neg 26),(.pos 25),(.pos 65)]),
   ((.exchange 27 46 6),[(.neg 46),(.neg 27),(.pos 5),(.pos 47)]),
   ((.exchange 27 50 6),[(.neg 50),(.neg 27),(.pos 8),(.pos 47)]),
   ((.exchange 27 56 5),[(.neg 56),(.neg 27),(.pos 15),(.pos 57)]),
   ((.exchange 27 65 2),[(.neg 65),(.neg 27),(.pos 25),(.pos 66)]),
   ((.exchange 28 46 6),[(.neg 46),(.neg 28),(.pos 7),(.pos 48)]),
   ((.exchange 28 50 6),[(.neg 50),(.neg 28),(.pos 7),(.pos 48)]),
   ((.exchange 28 56 5),[(.neg 56),(.neg 28),(.pos 17),(.pos 58)]),
   ((.exchange 29 46 6),[(.neg 46),(.neg 29),(.pos 6),(.pos 8),(.pos 49)]),
   ((.exchange 29 50 6),[(.neg 50),(.neg 29),(.pos 8),(.pos 49)]),
   ((.exchange 29 56 5),[(.neg 56),(.neg 29),(.pos 16),(.pos 18),(.pos 59)]),
   ((.exchange 30 46 6),[(.neg 46),(.neg 30),(.pos 7),(.pos 50)]),
   ((.exchange 30 47 6),[(.neg 47),(.neg 30),(.pos 8),(.pos 50)]),
   ((.exchange 30 48 6),[(.neg 48),(.neg 30),(.pos 7),(.pos 50)]),
   ((.exchange 30 49 6),[(.neg 49),(.neg 30),(.pos 8),(.pos 50)]),
   ((.exchange 30 51 6),[(.neg 51),(.neg 30),(.pos 7),(.pos 14),(.pos 50)]),
   ((.exchange 30 52 6),[(.neg 52),(.neg 30),(.pos 8),(.pos 14),(.pos 50)]),
   ((.exchange 30 53 6),[(.neg 53),(.neg 30),(.pos 14),(.pos 50)]),
   ((.exchange 30 54 6),[(.neg 54),(.neg 30),(.pos 14),(.pos 50)]),
   ((.exchange 30 56 5),[(.neg 56),(.neg 30),(.pos 17),(.pos 60)]),
   ((.exchange 31 46 6),[(.neg 46),(.neg 31),(.pos 10),(.pos 51)]),
   ((.exchange 31 50 6),[(.neg 50),(.neg 31),(.pos 10),(.pos 12),(.pos 51)]),
   ((.exchange 31 56 5),[(.neg 56),(.neg 31),(.pos 20),(.pos 61)]),
   ((.exchange 32 46 6),[(.neg 46),(.neg 32),(.pos 9),(.pos 11),(.pos 52)]),
   ((.exchange 32 50 6),[(.neg 50),(.neg 32),(.pos 11),(.pos 13),(.pos 52)]),
   ((.exchange 32 56 5),[(.neg 56),(.neg 32),(.pos 19),(.pos 21),(.pos 62)]),
   ((.exchange 33 46 6),[(.neg 46),(.neg 33),(.pos 10),(.pos 53)]),
   ((.exchange 33 50 6),[(.neg 50),(.neg 33),(.pos 14),(.pos 53)]),
   ((.exchange 33 56 5),[(.neg 56),(.neg 33),(.pos 20),(.pos 63)]),
   ((.exchange 34 46 6),[(.neg 46),(.neg 34),(.pos 12),(.pos 14),(.pos 54)]),
   ((.exchange 34 50 6),[(.neg 50),(.neg 34),(.pos 14),(.pos 54)]),
   ((.exchange 34 56 5),[(.neg 56),(.neg 34),(.pos 22),(.pos 24),(.pos 64)]),
   ((.exchange 35 26 7),[(.neg 35),(.neg 26),(.pos 5),(.pos 15)]),
   ((.exchange 36 26 7),[(.neg 36),(.neg 26),(.pos 0),(.pos 6),(.pos 16)]),
   ((.exchange 37 26 7),[(.neg 37),(.neg 26),(.pos 7),(.pos 17)]),
   ((.exchange 38 26 7),[(.neg 38),(.neg 26),(.pos 0),(.pos 8),(.pos 18)]),
   ((.exchange 39 26 7),[(.neg 39),(.neg 26),(.pos 1),(.pos 9),(.pos 19)]),
   ((.exchange 40 26 7),[(.neg 40),(.neg 26),(.pos 10),(.pos 20)]),
   ((.exchange 41 26 7),[(.neg 41),(.neg 26),(.pos 1),(.pos 11),(.pos 21)]),
   ((.exchange 42 26 7),[(.neg 42),(.neg 26),(.pos 3),(.pos 12),(.pos 22)]),
   ((.exchange 43 26 7),[(.neg 43),(.neg 26),(.pos 2),(.pos 4),(.pos 13),(.pos 23)]),
   ((.exchange 44 26 7),[(.neg 44),(.neg 26),(.pos 3),(.pos 14),(.pos 24)]),
   ((.exchange 45 26 7),[(.neg 45),(.neg 26),(.pos 5),(.pos 25)]),
   ((.exchange 55 26 7),[(.neg 55),(.neg 26),(.pos 15),(.pos 25)]),
   ((.exchange 65 30 0),[(.neg 65),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 65 33 0),[(.neg 65),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 65 34 0),[(.neg 65),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 66 30 1),[(.neg 66),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 66 33 1),[(.neg 66),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 66 34 1),[(.neg 66),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 67 28 2),[(.neg 67),(.neg 28),(.pos 65),(.pos 68)]),
   ((.exchange 67 29 2),[(.neg 67),(.neg 29),(.pos 66),(.pos 68)]),
   ((.exchange 67 31 2),[(.neg 67),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 67 32 2),[(.neg 67),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 67 34 2),[(.neg 67),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 67 54 2),[(.neg 67),(.neg 54),(.pos 68),(.pos 69)]),
   ((.exchange 67 58 2),[(.neg 67),(.neg 58),(.pos 65),(.pos 68)]),
   ((.exchange 67 59 2),[(.neg 67),(.neg 59),(.pos 66),(.pos 68)]),
   ((.exchange 67 64 2),[(.neg 67),(.neg 64),(.pos 68),(.pos 69)]),
   ((.exchange 68 31 3),[(.neg 68),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 68 32 3),[(.neg 68),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 68 33 3),[(.neg 68),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 68 53 3),[(.neg 68),(.neg 53),(.pos 67),(.pos 69)]),
   ((.exchange 69 26 4),[(.neg 69),(.neg 26),(.pos 65),(.pos 67)]),
   ((.exchange 69 27 4),[(.neg 69),(.neg 27),(.pos 66),(.pos 67)]),
   ((.exchange 69 28 4),[(.neg 69),(.neg 28),(.pos 65),(.pos 68)]),
   ((.exchange 69 29 4),[(.neg 69),(.neg 29),(.pos 66),(.pos 68)]),
   ((.exchange 69 30 4),[(.neg 69),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 69 56 4),[(.neg 69),(.neg 56),(.pos 65),(.pos 67)]),
   ((.exchange 69 57 4),[(.neg 69),(.neg 57),(.pos 66),(.pos 67)]),
   (.newPoint,[(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 0),[(.neg 69),(.neg 68),(.neg 67),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66)]),
   ((.excluded 1),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 67)]),
   ((.excluded 2),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 68)]),
   ((.excluded 3),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 4),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64)]),
   ((.excluded 5),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_1 : List (Origin 70 23 × List Sat.Literal) :=
  [((.excluded 6),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 65),(.pos 66)]),
   ((.excluded 7),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 67)]),
   ((.excluded 8),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 68)]),
   ((.excluded 9),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 69)]),
   ((.excluded 10),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55)]),
   ((.excluded 11),[(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 12),[(.neg 69),(.neg 68),(.neg 67),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66)]),
   ((.excluded 13),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 67)]),
   ((.excluded 14),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 68)]),
   ((.excluded 15),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 16),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64)]),
   ((.excluded 17),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 55),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 18),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 55),(.pos 65),(.pos 66)]),
   ((.excluded 19),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 55),(.pos 67)]),
   ((.excluded 20),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 55),(.pos 68)]),
   ((.excluded 21),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 55),(.pos 69)]),
   ((.excluded 22),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 55)])]

theorem certificates_1_valid : ∀ oc ∈ certificates_1,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



theorem witness_0 : ∀ j : Fin 23,
    let w : Fin 23 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 23,
      let w : Fin 23 := ⟨0 + j.val,by omega⟩
      target w < MatroidCatalogue.count 8 4 ∧
        Papers.RationalityTen.MatroidChecked.FastSemanticChecks.RawWitness 8 (N7R4.familyMasks.get 4)
        (fun i : Fin 70 => N8R4.gridMasks.get i.val) newIndex (models w)
        (N8R4.familyMasks.get (target w)) (permutation w) := by
    refine (Fin.forall_fin_add (m := 11) (n := 12) _).2 ⟨?_, ?_⟩
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


end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C4

/- Source: MatroidCatalogue/Cases/N8R4C4Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C4

noncomputable def certificates : List (Origin 70 23 × List Sat.Literal) :=
  certificates_0 ++ certificates_1

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  intro oc hoc
  simp only [certificates,List.mem_append,or_assoc] at hoc
  rcases hoc with h0 | h1
  · exact certificates_0_valid oc h0
  · exact certificates_1_valid oc h1

theorem models_valid : ∀ w : Fin 23,
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 23) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 8) 4)
    (hold : M.bases.filter ((7 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 8 4, IsomorphicWithin 8 M.bases B := by
  apply extension_covered_of_certificate (n:=7) (r:=4) (by decide)
    catalogue old U newIndex models certificates
    N8R4.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C4.formula []
    exact Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C4.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 8 4 (target w),family_mem 8 4 (target w) hw.1,?_⟩
    exact validWitness_sound 8 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C4


end
end
end BundlePart3

section BundlePart4
/- Source: MatroidChecked/SemanticChunks/Cases02Part04.lean -/






@[expose] public section
noncomputable section

/- Source: MatroidCatalogue/Cases/N8R4C5Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C5

abbrev U := N8R4.grid
noncomputable def old : Finset (Finset (Fin 8)) := N7R4.family 5
noncomputable def newIndexTree : Table ℕ := (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf 35) (.leaf 36)) (.node 3 (.leaf 37) (.leaf 38))) (.node 6 (.node 5 (.leaf 39) (.leaf 40)) (.node 7 (.leaf 41) (.leaf 42)))) (.node 12 (.node 10 (.node 9 (.leaf 43) (.leaf 44)) (.node 11 (.leaf 45) (.leaf 46))) (.node 14 (.node 13 (.leaf 47) (.leaf 48)) (.node 15 (.leaf 49) (.node 16 (.leaf 50) (.leaf 51)))))) (.node 26 (.node 21 (.node 19 (.node 18 (.leaf 52) (.leaf 53)) (.node 20 (.leaf 54) (.leaf 55))) (.node 23 (.node 22 (.leaf 56) (.leaf 57)) (.node 24 (.leaf 58) (.node 25 (.leaf 59) (.leaf 60))))) (.node 30 (.node 28 (.node 27 (.leaf 61) (.leaf 62)) (.node 29 (.leaf 63) (.leaf 64))) (.node 32 (.node 31 (.leaf 65) (.leaf 66)) (.node 33 (.leaf 67) (.node 34 (.leaf 68) (.leaf 69)))))))
noncomputable def newIndex (i : Fin 35) : Fin 70 := Fin.ofNat 70 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 13 (.node 6 (.node 3 (.node 1 (.leaf (32212254720,8,4151504)) (.node 2 (.leaf (31138512896,8,4151490)) (.leaf (28991029248,8,4151322)))) (.node 4 (.leaf (24696061952,8,4149530)) (.node 5 (.leaf (16106127360,8,4131610)) (.leaf (33285996544,9,12535432))))) (.node 9 (.node 7 (.leaf (1072693248,27,14599816)) (.node 8 (.leaf (33284947968,28,14599816)) (.leaf (32211206144,28,14599809)))) (.node 11 (.node 10 (.leaf (30063722496,28,14599697)) (.leaf (25768755200,28,14598353))) (.node 12 (.leaf (17178820608,28,14584017)) (.leaf (34358689792,29,14599816)))))) (.node 20 (.node 16 (.node 14 (.leaf (1047552,27,14141064)) (.node 15 (.leaf (32213302272,28,14141064)) (.leaf (31139560448,28,14141057)))) (.node 18 (.node 17 (.leaf (28992076800,28,14140945)) (.leaf (24697109504,28,14139601))) (.node 19 (.leaf (16107174912,28,14125265)) (.leaf (33287044096,29,14141064))))) (.node 23 (.node 21 (.leaf (1073740800,88,16434824)) (.node 22 (.leaf (33285995520,89,16434824)) (.leaf (32212253696,89,16434817)))) (.node 25 (.node 24 (.leaf (30064770048,89,16434705)) (.leaf (25769802752,89,16433361))) (.node 26 (.leaf (17179868160,89,16419025)) (.leaf (34359737344,90,16434824)))))))

noncomputable def models (i : Fin 27) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 27) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 27) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 70, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (7 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 70, (7 : Fin 8) ∈ U i → ∃ j : Fin 35, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C5

/- Source: MatroidCatalogue/Cases/N8R4C5Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C5


noncomputable def certificates_0 : List (Origin 70 27 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.neg 2)]),
   ((.fixed 3),[(.neg 3)]),
   ((.fixed 4),[(.neg 4)]),
   ((.fixed 5),[(.neg 5)]),
   ((.fixed 6),[(.neg 6)]),
   ((.fixed 7),[(.neg 7)]),
   ((.fixed 8),[(.neg 8)]),
   ((.fixed 9),[(.neg 9)]),
   ((.fixed 10),[(.neg 10)]),
   ((.fixed 11),[(.neg 11)]),
   ((.fixed 12),[(.neg 12)]),
   ((.fixed 13),[(.neg 13)]),
   ((.fixed 14),[(.neg 14)]),
   ((.fixed 15),[(.neg 15)]),
   ((.fixed 16),[(.neg 16)]),
   ((.fixed 17),[(.neg 17)]),
   ((.fixed 18),[(.neg 18)]),
   ((.fixed 19),[(.neg 19)]),
   ((.fixed 20),[(.neg 20)]),
   ((.fixed 21),[(.neg 21)]),
   ((.fixed 22),[(.neg 22)]),
   ((.fixed 23),[(.neg 23)]),
   ((.fixed 24),[(.neg 24)]),
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
   ((.exchange 25 46 6),[(.neg 46),(.neg 25),(.pos 5),(.pos 45)]),
   ((.exchange 25 50 6),[(.neg 50),(.neg 25),(.pos 5),(.pos 6),(.pos 45)]),
   ((.exchange 25 56 5),[(.neg 56),(.neg 25),(.pos 15),(.pos 55)]),
   ((.exchange 26 45 6),[(.neg 45),(.neg 26),(.pos 5),(.pos 46)]),
   ((.exchange 26 47 6),[(.neg 47),(.neg 26),(.pos 5),(.pos 46)]),
   ((.exchange 26 48 6),[(.neg 48),(.neg 26),(.pos 7),(.pos 46)]),
   ((.exchange 26 49 6),[(.neg 49),(.neg 26),(.pos 5),(.pos 7),(.pos 46)]),
   ((.exchange 26 50 6),[(.neg 50),(.neg 26),(.pos 7),(.pos 46)]),
   ((.exchange 26 51 6),[(.neg 51),(.neg 26),(.pos 10),(.pos 46)]),
   ((.exchange 26 52 6),[(.neg 52),(.neg 26),(.pos 5),(.pos 10),(.pos 46)]),
   ((.exchange 26 53 6),[(.neg 53),(.neg 26),(.pos 10),(.pos 46)]),
   ((.exchange 26 54 6),[(.neg 54),(.neg 26),(.pos 7),(.pos 10),(.pos 46)]),
   ((.exchange 26 55 5),[(.neg 55),(.neg 26),(.pos 15),(.pos 56)]),
   ((.exchange 26 57 5),[(.neg 57),(.neg 26),(.pos 15),(.pos 56)]),
   ((.exchange 26 58 5),[(.neg 58),(.neg 26),(.pos 17),(.pos 56)]),
   ((.exchange 26 59 5),[(.neg 59),(.neg 26),(.pos 15),(.pos 17),(.pos 56)]),
   ((.exchange 26 60 5),[(.neg 60),(.neg 26),(.pos 17),(.pos 56)]),
   ((.exchange 26 61 5),[(.neg 61),(.neg 26),(.pos 20),(.pos 56)]),
   ((.exchange 26 62 5),[(.neg 62),(.neg 26),(.pos 15),(.pos 20),(.pos 56)]),
   ((.exchange 26 63 5),[(.neg 63),(.neg 26),(.pos 20),(.pos 56)]),
   ((.exchange 26 64 5),[(.neg 64),(.neg 26),(.pos 17),(.pos 20),(.pos 56)]),
   ((.exchange 27 46 6),[(.neg 46),(.neg 27),(.pos 5),(.pos 47)]),
   ((.exchange 27 50 6),[(.neg 50),(.neg 27),(.pos 8),(.pos 47)]),
   ((.exchange 27 56 5),[(.neg 56),(.neg 27),(.pos 15),(.pos 57)]),
   ((.exchange 28 46 6),[(.neg 46),(.neg 28),(.pos 7),(.pos 48)]),
   ((.exchange 28 50 6),[(.neg 50),(.neg 28),(.pos 7),(.pos 48)]),
   ((.exchange 28 56 5),[(.neg 56),(.neg 28),(.pos 17),(.pos 58)]),
   ((.exchange 29 46 6),[(.neg 46),(.neg 29),(.pos 6),(.pos 8),(.pos 49)]),
   ((.exchange 29 50 6),[(.neg 50),(.neg 29),(.pos 8),(.pos 49)]),
   ((.exchange 29 56 5),[(.neg 56),(.neg 29),(.pos 16),(.pos 18),(.pos 59)]),
   ((.exchange 30 45 6),[(.neg 45),(.neg 30),(.pos 7),(.pos 8),(.pos 50)]),
   ((.exchange 30 46 6),[(.neg 46),(.neg 30),(.pos 7),(.pos 50)]),
   ((.exchange 30 47 6),[(.neg 47),(.neg 30),(.pos 8),(.pos 50)]),
   ((.exchange 30 48 6),[(.neg 48),(.neg 30),(.pos 7),(.pos 50)]),
   ((.exchange 30 49 6),[(.neg 49),(.neg 30),(.pos 8),(.pos 50)]),
   ((.exchange 30 51 6),[(.neg 51),(.neg 30),(.pos 7),(.pos 14),(.pos 50)]),
   ((.exchange 30 52 6),[(.neg 52),(.neg 30),(.pos 8),(.pos 14),(.pos 50)]),
   ((.exchange 30 53 6),[(.neg 53),(.neg 30),(.pos 14),(.pos 50)]),
   ((.exchange 30 54 6),[(.neg 54),(.neg 30),(.pos 14),(.pos 50)]),
   ((.exchange 30 56 5),[(.neg 56),(.neg 30),(.pos 17),(.pos 60)]),
   ((.exchange 31 46 6),[(.neg 46),(.neg 31),(.pos 10),(.pos 51)]),
   ((.exchange 31 50 6),[(.neg 50),(.neg 31),(.pos 10),(.pos 12),(.pos 51)]),
   ((.exchange 31 56 5),[(.neg 56),(.neg 31),(.pos 20),(.pos 61)]),
   ((.exchange 32 46 6),[(.neg 46),(.neg 32),(.pos 9),(.pos 11),(.pos 52)]),
   ((.exchange 32 50 6),[(.neg 50),(.neg 32),(.pos 11),(.pos 13),(.pos 52)]),
   ((.exchange 32 56 5),[(.neg 56),(.neg 32),(.pos 19),(.pos 21),(.pos 62)]),
   ((.exchange 33 46 6),[(.neg 46),(.neg 33),(.pos 10),(.pos 53)]),
   ((.exchange 33 50 6),[(.neg 50),(.neg 33),(.pos 14),(.pos 53)]),
   ((.exchange 33 56 5),[(.neg 56),(.neg 33),(.pos 20),(.pos 63)]),
   ((.exchange 34 46 6),[(.neg 46),(.neg 34),(.pos 12),(.pos 14),(.pos 54)]),
   ((.exchange 34 50 6),[(.neg 50),(.neg 34),(.pos 14),(.pos 54)]),
   ((.exchange 34 56 5),[(.neg 56),(.neg 34),(.pos 22),(.pos 24),(.pos 64)]),
   ((.exchange 35 25 7),[(.neg 35),(.neg 25),(.pos 5),(.pos 15)]),
   ((.exchange 36 25 7),[(.neg 36),(.neg 25),(.pos 6),(.pos 16)]),
   ((.exchange 37 25 7),[(.neg 37),(.neg 25),(.pos 0),(.pos 7),(.pos 17)]),
   ((.exchange 38 25 7),[(.neg 38),(.neg 25),(.pos 0),(.pos 8),(.pos 18)]),
   ((.exchange 39 25 7),[(.neg 39),(.neg 25),(.pos 9),(.pos 19)]),
   ((.exchange 40 25 7),[(.neg 40),(.neg 25),(.pos 1),(.pos 10),(.pos 20)]),
   ((.exchange 41 25 7),[(.neg 41),(.neg 25),(.pos 1),(.pos 11),(.pos 21)]),
   ((.exchange 42 25 7),[(.neg 42),(.neg 25),(.pos 2),(.pos 12),(.pos 22)]),
   ((.exchange 43 25 7),[(.neg 43),(.neg 25),(.pos 2),(.pos 13),(.pos 23)]),
   ((.exchange 44 25 7),[(.neg 44),(.neg 25),(.pos 3),(.pos 4),(.pos 14),(.pos 24)]),
   ((.exchange 65 30 0),[(.neg 65),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 65 33 0),[(.neg 65),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 65 34 0),[(.neg 65),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 66 30 1),[(.neg 66),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 66 33 1),[(.neg 66),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 66 34 1),[(.neg 66),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 67 31 2),[(.neg 67),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 67 32 2),[(.neg 67),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 67 34 2),[(.neg 67),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 67 48 2),[(.neg 67),(.neg 48),(.pos 65),(.pos 68)]),
   ((.exchange 67 49 2),[(.neg 67),(.neg 49),(.pos 66),(.pos 68)]),
   ((.exchange 67 54 2),[(.neg 67),(.neg 54),(.pos 68),(.pos 69)]),
   ((.exchange 67 58 2),[(.neg 67),(.neg 58),(.pos 65),(.pos 68)]),
   ((.exchange 67 59 2),[(.neg 67),(.neg 59),(.pos 66),(.pos 68)]),
   ((.exchange 67 64 2),[(.neg 67),(.neg 64),(.pos 68),(.pos 69)]),
   ((.exchange 68 25 3),[(.neg 68),(.neg 25),(.pos 65),(.pos 66)]),
   ((.exchange 68 31 3),[(.neg 68),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 68 32 3),[(.neg 68),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 68 33 3),[(.neg 68),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 68 53 3),[(.neg 68),(.neg 53),(.pos 67),(.pos 69)]),
   ((.exchange 69 26 4),[(.neg 69),(.neg 26),(.pos 65),(.pos 67)]),
   ((.exchange 69 27 4),[(.neg 69),(.neg 27),(.pos 66),(.pos 67)]),
   ((.exchange 69 28 4),[(.neg 69),(.neg 28),(.pos 65),(.pos 68)]),
   ((.exchange 69 29 4),[(.neg 69),(.neg 29),(.pos 66),(.pos 68)]),
   ((.exchange 69 30 4),[(.neg 69),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 69 56 4),[(.neg 69),(.neg 56),(.pos 65),(.pos 67)]),
   ((.exchange 69 57 4),[(.neg 69),(.neg 57),(.pos 66),(.pos 67)]),
   (.newPoint,[(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 0),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65)]),
   ((.excluded 1),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 66)]),
   ((.excluded 2),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 67)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_1 : List (Origin 70 27 × List Sat.Literal) :=
  [((.excluded 3),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 68)]),
   ((.excluded 4),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 5),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64)]),
   ((.excluded 6),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 7),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 65)]),
   ((.excluded 8),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 66)]),
   ((.excluded 9),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 67)]),
   ((.excluded 10),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 68)]),
   ((.excluded 11),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 69)]),
   ((.excluded 12),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54)]),
   ((.excluded 13),[(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 14),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65)]),
   ((.excluded 15),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 66)]),
   ((.excluded 16),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 67)]),
   ((.excluded 17),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 68)]),
   ((.excluded 18),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 19),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64)]),
   ((.excluded 20),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 21),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 65)]),
   ((.excluded 22),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 66)]),
   ((.excluded 23),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 67)]),
   ((.excluded 24),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 68)]),
   ((.excluded 25),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 69)]),
   ((.excluded 26),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44)])]

theorem certificates_1_valid : ∀ oc ∈ certificates_1,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



theorem witness_0 : ∀ j : Fin 27,
    let w : Fin 27 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 27,
      let w : Fin 27 := ⟨0 + j.val,by omega⟩
      target w < MatroidCatalogue.count 8 4 ∧
        Papers.RationalityTen.MatroidChecked.FastSemanticChecks.RawWitness 8 (N7R4.familyMasks.get 5)
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


end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C5

/- Source: MatroidCatalogue/Cases/N8R4C5Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C5

noncomputable def certificates : List (Origin 70 27 × List Sat.Literal) :=
  certificates_0 ++ certificates_1

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  intro oc hoc
  simp only [certificates,List.mem_append,or_assoc] at hoc
  rcases hoc with h0 | h1
  · exact certificates_0_valid oc h0
  · exact certificates_1_valid oc h1

theorem models_valid : ∀ w : Fin 27,
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 27) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 8) 4)
    (hold : M.bases.filter ((7 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 8 4, IsomorphicWithin 8 M.bases B := by
  apply extension_covered_of_certificate (n:=7) (r:=4) (by decide)
    catalogue old U newIndex models certificates
    N8R4.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C5.formula []
    exact Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C5.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 8 4 (target w),family_mem 8 4 (target w) hw.1,?_⟩
    exact validWitness_sound 8 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C5

/- Source: MatroidCatalogue/Cases/N8R4C6Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C6

abbrev U := N8R4.grid
noncomputable def old : Finset (Finset (Fin 8)) := N7R4.family 6
noncomputable def newIndexTree : Table ℕ := (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf 35) (.leaf 36)) (.node 3 (.leaf 37) (.leaf 38))) (.node 6 (.node 5 (.leaf 39) (.leaf 40)) (.node 7 (.leaf 41) (.leaf 42)))) (.node 12 (.node 10 (.node 9 (.leaf 43) (.leaf 44)) (.node 11 (.leaf 45) (.leaf 46))) (.node 14 (.node 13 (.leaf 47) (.leaf 48)) (.node 15 (.leaf 49) (.node 16 (.leaf 50) (.leaf 51)))))) (.node 26 (.node 21 (.node 19 (.node 18 (.leaf 52) (.leaf 53)) (.node 20 (.leaf 54) (.leaf 55))) (.node 23 (.node 22 (.leaf 56) (.leaf 57)) (.node 24 (.leaf 58) (.node 25 (.leaf 59) (.leaf 60))))) (.node 30 (.node 28 (.node 27 (.leaf 61) (.leaf 62)) (.node 29 (.leaf 63) (.leaf 64))) (.node 32 (.node 31 (.leaf 65) (.leaf 66)) (.node 33 (.leaf 67) (.node 34 (.leaf 68) (.leaf 69)))))))
noncomputable def newIndex (i : Fin 35) : Fin 70 := Fin.ofNat 70 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (7985954816,14,10442376)) (.leaf (7574913024,14,10435208))) (.node 3 (.leaf (528482304,14,10349192)) (.leaf (8044675072,30,14599816)))) (.node 6 (.node 5 (.leaf (26306674688,10,8345736)) (.leaf (34292629504,17,10442376))) (.node 7 (.leaf (33881587712,17,10435208)) (.node 8 (.leaf (26835156992,17,10349192)) (.leaf (34351349760,31,14599816)))))) (.node 14 (.node 11 (.node 10 (.leaf (516992,72,9431688)) (.leaf (7986471808,91,16434824))) (.node 12 (.leaf (7575430016,91,16431240)) (.node 13 (.leaf (528999296,91,16373896)) (.leaf (8045192064,92,16434824))))) (.node 16 (.node 15 (.leaf (26307191680,76,9431688)) (.leaf (34293146496,93,16434824))) (.node 17 (.leaf (33882104704,93,16431240)) (.node 18 (.leaf (26835673984,93,16373896)) (.leaf (34351866752,94,16434824)))))))

noncomputable def models (i : Fin 19) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 19) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 19) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 70, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (7 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 70, (7 : Fin 8) ∈ U i → ∃ j : Fin 35, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C6

/- Source: MatroidCatalogue/Cases/N8R4C6Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C6


noncomputable def certificates_0 : List (Origin 70 19 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.neg 2)]),
   ((.fixed 3),[(.neg 3)]),
   ((.fixed 4),[(.neg 4)]),
   ((.fixed 5),[(.neg 5)]),
   ((.fixed 6),[(.neg 6)]),
   ((.fixed 7),[(.neg 7)]),
   ((.fixed 8),[(.neg 8)]),
   ((.fixed 9),[(.neg 9)]),
   ((.fixed 10),[(.neg 10)]),
   ((.fixed 11),[(.neg 11)]),
   ((.fixed 12),[(.neg 12)]),
   ((.fixed 13),[(.neg 13)]),
   ((.fixed 14),[(.neg 14)]),
   ((.fixed 15),[(.neg 15)]),
   ((.fixed 16),[(.neg 16)]),
   ((.fixed 17),[(.neg 17)]),
   ((.fixed 18),[(.neg 18)]),
   ((.fixed 19),[(.neg 19)]),
   ((.fixed 20),[(.neg 20)]),
   ((.fixed 21),[(.neg 21)]),
   ((.fixed 22),[(.pos 22)]),
   ((.fixed 23),[(.pos 23)]),
   ((.fixed 24),[(.pos 24)]),
   ((.fixed 25),[(.neg 25)]),
   ((.fixed 26),[(.neg 26)]),
   ((.fixed 27),[(.neg 27)]),
   ((.fixed 28),[(.pos 28)]),
   ((.fixed 29),[(.pos 29)]),
   ((.fixed 30),[(.pos 30)]),
   ((.fixed 31),[(.pos 31)]),
   ((.fixed 32),[(.pos 32)]),
   ((.fixed 33),[(.pos 33)]),
   ((.fixed 34),[(.neg 34)]),
   ((.exchange 22 43 6),[(.neg 43),(.neg 22),(.pos 2),(.pos 42)]),
   ((.exchange 22 44 6),[(.neg 44),(.neg 22),(.pos 3),(.pos 42)]),
   ((.exchange 22 48 6),[(.neg 48),(.neg 22),(.pos 12),(.pos 42)]),
   ((.exchange 22 49 6),[(.neg 49),(.neg 22),(.pos 2),(.pos 12),(.pos 42)]),
   ((.exchange 22 50 6),[(.neg 50),(.neg 22),(.pos 3),(.pos 12),(.pos 42)]),
   ((.exchange 22 51 6),[(.neg 51),(.neg 22),(.pos 12),(.pos 42)]),
   ((.exchange 22 52 6),[(.neg 52),(.neg 22),(.pos 2),(.pos 12),(.pos 42)]),
   ((.exchange 22 53 6),[(.neg 53),(.neg 22),(.pos 3),(.pos 12),(.pos 42)]),
   ((.exchange 22 59 4),[(.neg 59),(.neg 22),(.pos 16),(.pos 58)]),
   ((.exchange 22 60 4),[(.neg 60),(.neg 22),(.pos 17),(.pos 58)]),
   ((.exchange 22 62 3),[(.neg 62),(.neg 22),(.pos 19),(.pos 61)]),
   ((.exchange 22 63 3),[(.neg 63),(.neg 22),(.pos 20),(.pos 61)]),
   ((.exchange 22 68 0),[(.neg 68),(.neg 22),(.pos 34),(.pos 64)]),
   ((.exchange 22 69 0),[(.neg 69),(.neg 22),(.pos 34),(.pos 64)]),
   ((.exchange 23 42 6),[(.neg 42),(.neg 23),(.pos 2),(.pos 43)]),
   ((.exchange 23 58 4),[(.neg 58),(.neg 23),(.pos 16),(.pos 59)]),
   ((.exchange 23 60 4),[(.neg 60),(.neg 23),(.pos 18),(.pos 59)]),
   ((.exchange 23 61 3),[(.neg 61),(.neg 23),(.pos 19),(.pos 62)]),
   ((.exchange 23 63 3),[(.neg 63),(.neg 23),(.pos 21),(.pos 62)]),
   ((.exchange 24 42 6),[(.neg 42),(.neg 24),(.pos 3),(.pos 44)]),
   ((.exchange 24 58 4),[(.neg 58),(.neg 24),(.pos 17),(.pos 60)]),
   ((.exchange 24 59 4),[(.neg 59),(.neg 24),(.pos 18),(.pos 60)]),
   ((.exchange 24 61 3),[(.neg 61),(.neg 24),(.pos 20),(.pos 63)]),
   ((.exchange 24 62 3),[(.neg 62),(.neg 24),(.pos 21),(.pos 63)]),
   ((.exchange 28 42 6),[(.neg 42),(.neg 28),(.pos 12),(.pos 48)]),
   ((.exchange 28 64 0),[(.neg 64),(.neg 28),(.pos 34),(.pos 68)]),
   ((.exchange 28 67 3),[(.neg 67),(.neg 28),(.pos 26),(.pos 65)]),
   ((.exchange 28 69 0),[(.neg 69),(.neg 28),(.pos 34),(.pos 68)]),
   ((.exchange 29 42 6),[(.neg 42),(.neg 29),(.pos 6),(.pos 13),(.pos 49)]),
   ((.exchange 29 67 3),[(.neg 67),(.neg 29),(.pos 27),(.pos 66)]),
   ((.exchange 30 42 6),[(.neg 42),(.neg 30),(.pos 7),(.pos 14),(.pos 50)]),
   ((.exchange 30 65 3),[(.neg 65),(.neg 30),(.pos 26),(.pos 67)]),
   ((.exchange 30 66 3),[(.neg 66),(.neg 30),(.pos 27),(.pos 67)]),
   ((.exchange 31 42 6),[(.neg 42),(.neg 31),(.pos 12),(.pos 51)]),
   ((.exchange 31 64 0),[(.neg 64),(.neg 31),(.pos 34),(.pos 69)]),
   ((.exchange 31 68 0),[(.neg 68),(.neg 31),(.pos 34),(.pos 69)]),
   ((.exchange 32 42 6),[(.neg 42),(.neg 32),(.pos 9),(.pos 13),(.pos 52)]),
   ((.exchange 33 42 6),[(.neg 42),(.neg 33),(.pos 10),(.pos 14),(.pos 53)]),
   ((.exchange 35 22 7),[(.neg 35),(.neg 22),(.pos 0),(.pos 1),(.pos 15)]),
   ((.exchange 36 22 7),[(.neg 36),(.neg 22),(.pos 2),(.pos 16)]),
   ((.exchange 37 22 7),[(.neg 37),(.neg 22),(.pos 3),(.pos 17)]),
   ((.exchange 38 22 7),[(.neg 38),(.neg 22),(.pos 0),(.pos 4),(.pos 18)]),
   ((.exchange 39 22 7),[(.neg 39),(.neg 22),(.pos 2),(.pos 19)]),
   ((.exchange 40 22 7),[(.neg 40),(.neg 22),(.pos 3),(.pos 20)]),
   ((.exchange 41 22 7),[(.neg 41),(.neg 22),(.pos 1),(.pos 4),(.pos 21)]),
   ((.exchange 45 22 7),[(.neg 45),(.neg 22),(.pos 6),(.pos 9),(.pos 25)]),
   ((.exchange 46 22 7),[(.neg 46),(.neg 22),(.pos 7),(.pos 10),(.pos 26)]),
   ((.exchange 47 22 7),[(.neg 47),(.neg 22),(.pos 5),(.pos 8),(.pos 11),(.pos 27)]),
   ((.exchange 54 22 7),[(.neg 54),(.neg 22),(.pos 12),(.pos 34)]),
   ((.exchange 55 22 7),[(.neg 55),(.neg 22),(.pos 16),(.pos 19)]),
   ((.exchange 56 22 7),[(.neg 56),(.neg 22),(.pos 17),(.pos 20)]),
   ((.exchange 57 22 7),[(.neg 57),(.neg 22),(.pos 15),(.pos 18),(.pos 21)]),
   ((.exchange 58 31 3),[(.neg 58),(.neg 31),(.pos 61),(.pos 65)]),
   ((.exchange 58 53 3),[(.neg 58),(.neg 53),(.pos 56),(.pos 61),(.pos 65)]),
   ((.exchange 58 69 3),[(.neg 69),(.neg 58),(.pos 61),(.pos 65)]),
   ((.exchange 59 31 3),[(.neg 59),(.neg 31),(.pos 55),(.pos 62),(.pos 66)]),
   ((.exchange 59 53 3),[(.neg 59),(.neg 53),(.pos 57),(.pos 62),(.pos 66)]),
   ((.exchange 59 69 3),[(.neg 69),(.neg 59),(.pos 62),(.pos 66)]),
   ((.exchange 60 31 3),[(.neg 60),(.neg 31),(.pos 56),(.pos 63),(.pos 67)]),
   ((.exchange 60 53 3),[(.neg 60),(.neg 53),(.pos 63),(.pos 67)]),
   ((.exchange 60 69 3),[(.neg 69),(.neg 60),(.pos 63),(.pos 67)]),
   ((.exchange 61 28 4),[(.neg 61),(.neg 28),(.pos 58),(.pos 65)]),
   ((.exchange 61 48 4),[(.neg 61),(.neg 48),(.pos 58),(.pos 65)]),
   ((.exchange 62 28 4),[(.neg 62),(.neg 28),(.pos 55),(.pos 59),(.pos 66)]),
   ((.exchange 62 48 4),[(.neg 62),(.neg 48),(.pos 55),(.pos 59),(.pos 66)]),
   ((.exchange 63 28 4),[(.neg 63),(.neg 28),(.pos 56),(.pos 60),(.pos 67)]),
   ((.exchange 63 48 4),[(.neg 63),(.neg 48),(.pos 56),(.pos 60),(.pos 67)]),
   ((.exchange 65 22 5),[(.neg 65),(.neg 22),(.pos 58),(.pos 61)]),
   ((.exchange 65 42 5),[(.neg 65),(.neg 42),(.pos 58),(.pos 61)]),
   ((.exchange 66 22 5),[(.neg 66),(.neg 22),(.pos 55),(.pos 59),(.pos 62)]),
   ((.exchange 66 42 5),[(.neg 66),(.neg 42),(.pos 55),(.pos 59),(.pos 62)]),
   ((.exchange 67 22 5),[(.neg 67),(.neg 22),(.pos 56),(.pos 60),(.pos 63)]),
   ((.exchange 67 42 5),[(.neg 67),(.neg 42),(.pos 56),(.pos 60),(.pos 63)]),
   (.newPoint,[(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 0),[(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 68),(.pos 69)]),
   ((.excluded 1),[(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 58),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 68),(.pos 69)]),
   ((.excluded 2),[(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 3),[(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 64),(.pos 68),(.pos 69)]),
   ((.excluded 4),[(.neg 69),(.neg 68),(.neg 64),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 65),(.pos 66),(.pos 67)]),
   ((.excluded 5),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60)]),
   ((.excluded 6),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 60),(.neg 59),(.neg 58),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 61),(.pos 62),(.pos 63)]),
   ((.excluded 7),[(.neg 69),(.neg 68),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 65),(.pos 66),(.pos 67)]),
   ((.excluded 8),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 9),[(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 10),[(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 68),(.pos 69)]),
   ((.excluded 11),[(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 58),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 68),(.pos 69)]),
   ((.excluded 12),[(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 13),[(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 64),(.pos 68),(.pos 69)]),
   ((.excluded 14),[(.neg 69),(.neg 68),(.neg 64),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 65),(.pos 66),(.pos 67)]),
   ((.excluded 15),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60)]),
   ((.excluded 16),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 60),(.neg 59),(.neg 58),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 61),(.pos 62),(.pos 63)]),
   ((.excluded 17),[(.neg 69),(.neg 68),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 65),(.pos 66),(.pos 67)]),
   ((.excluded 18),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 54),(.pos 55),(.pos 56),(.pos 57)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



theorem witness_0 : ∀ j : Fin 19,
    let w : Fin 19 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 19,
      let w : Fin 19 := ⟨0 + j.val,by omega⟩
      target w < MatroidCatalogue.count 8 4 ∧
        Papers.RationalityTen.MatroidChecked.FastSemanticChecks.RawWitness 8 (N7R4.familyMasks.get 6)
        (fun i : Fin 70 => N8R4.gridMasks.get i.val) newIndex (models w)
        (N8R4.familyMasks.get (target w)) (permutation w) := by
    refine (Fin.forall_fin_add (m := 9) (n := 10) _).2 ⟨?_, ?_⟩
    · refine (Fin.forall_fin_add (m := 4) (n := 5) _).2 ⟨?_, ?_⟩
      · decide +kernel
      · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
        · decide +kernel
        · decide +kernel
    · refine (Fin.forall_fin_add (m := 5) (n := 5) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
        · decide +kernel
        · decide +kernel
      · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
        · decide +kernel
        · decide +kernel
  intro j
  have hj := hfast j
  exact ⟨hj.1,Papers.RationalityTen.MatroidChecked.FastSemanticChecks.rawWitness_sound 8 _ _ _ _ _ _ hj.2⟩


end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C6

/- Source: MatroidCatalogue/Cases/N8R4C6Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C6

noncomputable def certificates : List (Origin 70 19 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 19,
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 19) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 8) 4)
    (hold : M.bases.filter ((7 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 8 4, IsomorphicWithin 8 M.bases B := by
  apply extension_covered_of_certificate (n:=7) (r:=4) (by decide)
    catalogue old U newIndex models certificates
    N8R4.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C6.formula []
    exact Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C6.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 8 4 (target w),family_mem 8 4 (target w) hw.1,?_⟩
    exact validWitness_sound 8 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C6


end
end
end BundlePart4

section BundlePart5
/- Source: MatroidChecked/SemanticChunks/Cases02Part05.lean -/








@[expose] public section
noncomputable section

/- Source: MatroidCatalogue/Cases/N8R4C7Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C7

abbrev U := N8R4.grid
noncomputable def old : Finset (Finset (Fin 8)) := N7R4.family 7
noncomputable def newIndexTree : Table ℕ := (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf 35) (.leaf 36)) (.node 3 (.leaf 37) (.leaf 38))) (.node 6 (.node 5 (.leaf 39) (.leaf 40)) (.node 7 (.leaf 41) (.leaf 42)))) (.node 12 (.node 10 (.node 9 (.leaf 43) (.leaf 44)) (.node 11 (.leaf 45) (.leaf 46))) (.node 14 (.node 13 (.leaf 47) (.leaf 48)) (.node 15 (.leaf 49) (.node 16 (.leaf 50) (.leaf 51)))))) (.node 26 (.node 21 (.node 19 (.node 18 (.leaf 52) (.leaf 53)) (.node 20 (.leaf 54) (.leaf 55))) (.node 23 (.node 22 (.leaf 56) (.leaf 57)) (.node 24 (.leaf 58) (.node 25 (.leaf 59) (.leaf 60))))) (.node 30 (.node 28 (.node 27 (.leaf 61) (.leaf 62)) (.node 29 (.leaf 63) (.leaf 64))) (.node 32 (.node 31 (.leaf 65) (.leaf 66)) (.node 33 (.leaf 67) (.node 34 (.leaf 68) (.leaf 69)))))))
noncomputable def newIndex (i : Fin 35) : Fin 70 := Fin.ofNat 70 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 14 (.node 7 (.node 3 (.node 1 (.leaf (25165824000,15,10442376)) (.node 2 (.leaf (16164847616,15,10435208)) (.leaf (26298286080,17,8284808)))) (.node 5 (.node 4 (.leaf (33814478848,31,12535432)) (.leaf (26306674688,11,8345736))) (.node 6 (.leaf (1065353216,15,10349192)) (.leaf (26835156992,18,10349192))))) (.node 10 (.node 8 (.leaf (17112760320,17,8345736)) (.node 9 (.leaf (34292629504,18,10442376)) (.leaf (25291653120,17,8342152)))) (.node 12 (.node 11 (.leaf (33881587712,18,10435208)) (.leaf (25761415168,31,12478088))) (.node 13 (.leaf (17171480576,31,12467336)) (.leaf (34351349760,32,14599816)))))) (.node 21 (.node 17 (.node 15 (.leaf (1041280,74,9431688)) (.node 16 (.leaf (26307715968,78,9431688)) (.leaf (25166865280,93,11789960)))) (.node 19 (.node 18 (.leaf (17113801600,95,16434824)) (.leaf (34293670784,96,16434824))) (.node 20 (.leaf (16165888896,93,11779208)) (.leaf (1066394496,93,11664520))))) (.node 25 (.node 23 (.node 22 (.leaf (17172521856,97,16398984)) (.leaf (25292694400,95,16431240))) (.node 24 (.leaf (33882628992,96,16431240)) (.leaf (26299327360,95,16373896)))) (.node 27 (.node 26 (.leaf (26836198272,96,16373896)) (.leaf (33815520128,97,16434824))) (.node 28 (.leaf (25762456448,97,16406152)) (.leaf (34352391040,98,16434824)))))))

noncomputable def models (i : Fin 29) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 29) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 29) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 70, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (7 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 70, (7 : Fin 8) ∈ U i → ∃ j : Fin 35, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C7

/- Source: MatroidCatalogue/Cases/N8R4C7Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C7


noncomputable def certificates_0 : List (Origin 70 29 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.neg 2)]),
   ((.fixed 3),[(.neg 3)]),
   ((.fixed 4),[(.neg 4)]),
   ((.fixed 5),[(.neg 5)]),
   ((.fixed 6),[(.neg 6)]),
   ((.fixed 7),[(.neg 7)]),
   ((.fixed 8),[(.neg 8)]),
   ((.fixed 9),[(.neg 9)]),
   ((.fixed 10),[(.neg 10)]),
   ((.fixed 11),[(.neg 11)]),
   ((.fixed 12),[(.neg 12)]),
   ((.fixed 13),[(.neg 13)]),
   ((.fixed 14),[(.neg 14)]),
   ((.fixed 15),[(.neg 15)]),
   ((.fixed 16),[(.neg 16)]),
   ((.fixed 17),[(.neg 17)]),
   ((.fixed 18),[(.neg 18)]),
   ((.fixed 19),[(.neg 19)]),
   ((.fixed 20),[(.neg 20)]),
   ((.fixed 21),[(.neg 21)]),
   ((.fixed 22),[(.pos 22)]),
   ((.fixed 23),[(.pos 23)]),
   ((.fixed 24),[(.pos 24)]),
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
   ((.exchange 22 43 6),[(.neg 43),(.neg 22),(.pos 2),(.pos 42)]),
   ((.exchange 22 44 6),[(.neg 44),(.neg 22),(.pos 3),(.pos 42)]),
   ((.exchange 22 48 6),[(.neg 48),(.neg 22),(.pos 12),(.pos 42)]),
   ((.exchange 22 49 6),[(.neg 49),(.neg 22),(.pos 2),(.pos 12),(.pos 42)]),
   ((.exchange 22 50 6),[(.neg 50),(.neg 22),(.pos 3),(.pos 12),(.pos 42)]),
   ((.exchange 22 51 6),[(.neg 51),(.neg 22),(.pos 12),(.pos 42)]),
   ((.exchange 22 52 6),[(.neg 52),(.neg 22),(.pos 2),(.pos 12),(.pos 42)]),
   ((.exchange 22 53 6),[(.neg 53),(.neg 22),(.pos 3),(.pos 12),(.pos 42)]),
   ((.exchange 22 54 6),[(.neg 54),(.neg 22),(.pos 12),(.pos 42)]),
   ((.exchange 22 59 4),[(.neg 59),(.neg 22),(.pos 16),(.pos 58)]),
   ((.exchange 22 60 4),[(.neg 60),(.neg 22),(.pos 17),(.pos 58)]),
   ((.exchange 22 62 3),[(.neg 62),(.neg 22),(.pos 19),(.pos 61)]),
   ((.exchange 22 63 3),[(.neg 63),(.neg 22),(.pos 20),(.pos 61)]),
   ((.exchange 23 42 6),[(.neg 42),(.neg 23),(.pos 2),(.pos 43)]),
   ((.exchange 23 58 4),[(.neg 58),(.neg 23),(.pos 16),(.pos 59)]),
   ((.exchange 23 60 4),[(.neg 60),(.neg 23),(.pos 18),(.pos 59)]),
   ((.exchange 23 61 3),[(.neg 61),(.neg 23),(.pos 19),(.pos 62)]),
   ((.exchange 23 63 3),[(.neg 63),(.neg 23),(.pos 21),(.pos 62)]),
   ((.exchange 24 42 6),[(.neg 42),(.neg 24),(.pos 3),(.pos 44)]),
   ((.exchange 24 58 4),[(.neg 58),(.neg 24),(.pos 17),(.pos 60)]),
   ((.exchange 24 59 4),[(.neg 59),(.neg 24),(.pos 18),(.pos 60)]),
   ((.exchange 24 61 3),[(.neg 61),(.neg 24),(.pos 20),(.pos 63)]),
   ((.exchange 24 62 3),[(.neg 62),(.neg 24),(.pos 21),(.pos 63)]),
   ((.exchange 28 42 6),[(.neg 42),(.neg 28),(.pos 12),(.pos 48)]),
   ((.exchange 28 67 3),[(.neg 67),(.neg 28),(.pos 26),(.pos 65)]),
   ((.exchange 29 42 6),[(.neg 42),(.neg 29),(.pos 6),(.pos 13),(.pos 49)]),
   ((.exchange 29 67 3),[(.neg 67),(.neg 29),(.pos 27),(.pos 66)]),
   ((.exchange 30 42 6),[(.neg 42),(.neg 30),(.pos 7),(.pos 14),(.pos 50)]),
   ((.exchange 30 65 3),[(.neg 65),(.neg 30),(.pos 26),(.pos 67)]),
   ((.exchange 30 66 3),[(.neg 66),(.neg 30),(.pos 27),(.pos 67)]),
   ((.exchange 31 42 6),[(.neg 42),(.neg 31),(.pos 12),(.pos 51)]),
   ((.exchange 32 42 6),[(.neg 42),(.neg 32),(.pos 9),(.pos 13),(.pos 52)]),
   ((.exchange 33 42 6),[(.neg 42),(.neg 33),(.pos 10),(.pos 14),(.pos 53)]),
   ((.exchange 34 42 6),[(.neg 42),(.neg 34),(.pos 12),(.pos 54)]),
   ((.exchange 35 22 7),[(.neg 35),(.neg 22),(.pos 0),(.pos 1),(.pos 15)]),
   ((.exchange 36 22 7),[(.neg 36),(.neg 22),(.pos 2),(.pos 16)]),
   ((.exchange 37 22 7),[(.neg 37),(.neg 22),(.pos 3),(.pos 17)]),
   ((.exchange 38 22 7),[(.neg 38),(.neg 22),(.pos 0),(.pos 4),(.pos 18)]),
   ((.exchange 39 22 7),[(.neg 39),(.neg 22),(.pos 2),(.pos 19)]),
   ((.exchange 40 22 7),[(.neg 40),(.neg 22),(.pos 3),(.pos 20)]),
   ((.exchange 41 22 7),[(.neg 41),(.neg 22),(.pos 1),(.pos 4),(.pos 21)]),
   ((.exchange 45 22 7),[(.neg 45),(.neg 22),(.pos 6),(.pos 9),(.pos 25)]),
   ((.exchange 46 22 7),[(.neg 46),(.neg 22),(.pos 7),(.pos 10),(.pos 26)]),
   ((.exchange 47 22 7),[(.neg 47),(.neg 22),(.pos 5),(.pos 8),(.pos 11),(.pos 27)]),
   ((.exchange 55 22 7),[(.neg 55),(.neg 22),(.pos 16),(.pos 19)]),
   ((.exchange 56 22 7),[(.neg 56),(.neg 22),(.pos 17),(.pos 20)]),
   ((.exchange 57 22 7),[(.neg 57),(.neg 22),(.pos 15),(.pos 18),(.pos 21)]),
   ((.exchange 58 31 3),[(.neg 58),(.neg 31),(.pos 61),(.pos 65)]),
   ((.exchange 58 34 0),[(.neg 58),(.neg 34),(.pos 64),(.pos 68)]),
   ((.exchange 58 52 3),[(.neg 58),(.neg 52),(.pos 55),(.pos 61),(.pos 65)]),
   ((.exchange 58 54 0),[(.neg 58),(.neg 54),(.pos 64),(.pos 68)]),
   ((.exchange 59 31 3),[(.neg 59),(.neg 31),(.pos 55),(.pos 62),(.pos 66)]),
   ((.exchange 59 34 1),[(.neg 59),(.neg 34),(.pos 64),(.pos 68)]),
   ((.exchange 59 53 3),[(.neg 59),(.neg 53),(.pos 57),(.pos 62),(.pos 66)]),
   ((.exchange 59 54 1),[(.neg 59),(.neg 54),(.pos 64),(.pos 68)]),
   ((.exchange 60 31 3),[(.neg 60),(.neg 31),(.pos 56),(.pos 63),(.pos 67)]),
   ((.exchange 60 53 3),[(.neg 60),(.neg 53),(.pos 63),(.pos 67)]),
   ((.exchange 60 54 2),[(.neg 60),(.neg 54),(.pos 64),(.pos 68)]),
   ((.exchange 61 28 4),[(.neg 61),(.neg 28),(.pos 58),(.pos 65)]),
   ((.exchange 61 34 0),[(.neg 61),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 62 28 4),[(.neg 62),(.neg 28),(.pos 55),(.pos 59),(.pos 66)]),
   ((.exchange 62 34 1),[(.neg 62),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 63 28 4),[(.neg 63),(.neg 28),(.pos 56),(.pos 60),(.pos 67)]),
   ((.exchange 63 34 2),[(.neg 63),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 64 28 4),[(.neg 64),(.neg 28),(.pos 58),(.pos 68)]),
   ((.exchange 64 29 4),[(.neg 64),(.neg 29),(.pos 59),(.pos 68)]),
   ((.exchange 64 30 4),[(.neg 64),(.neg 30),(.pos 60),(.pos 68)]),
   ((.exchange 64 31 3),[(.neg 64),(.neg 31),(.pos 61),(.pos 69)]),
   ((.exchange 64 32 3),[(.neg 64),(.neg 32),(.pos 62),(.pos 69)]),
   ((.exchange 64 33 3),[(.neg 64),(.neg 33),(.pos 63),(.pos 69)]),
   ((.exchange 65 22 5),[(.neg 65),(.neg 22),(.pos 58),(.pos 61)]),
   ((.exchange 65 43 5),[(.neg 65),(.neg 43),(.pos 55),(.pos 58),(.pos 61)]),
   ((.exchange 66 22 5),[(.neg 66),(.neg 22),(.pos 55),(.pos 59),(.pos 62)]),
   ((.exchange 66 34 1),[(.neg 66),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 66 43 5),[(.neg 66),(.neg 43),(.pos 59),(.pos 62)]),
   ((.exchange 67 22 5),[(.neg 67),(.neg 22),(.pos 56),(.pos 60),(.pos 63)]),
   ((.exchange 67 34 2),[(.neg 67),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 67 42 5),[(.neg 67),(.neg 42),(.pos 56),(.pos 60),(.pos 63)]),
   ((.exchange 67 43 5),[(.neg 67),(.neg 43),(.pos 57),(.pos 60),(.pos 63)]),
   ((.exchange 68 22 5),[(.neg 68),(.neg 22),(.pos 58),(.pos 64)]),
   ((.exchange 68 23 5),[(.neg 68),(.neg 23),(.pos 59),(.pos 64)]),
   ((.exchange 68 24 5),[(.neg 68),(.neg 24),(.pos 60),(.pos 64)]),
   ((.exchange 68 33 3),[(.neg 68),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 68 53 3),[(.neg 68),(.neg 53),(.pos 67),(.pos 69)]),
   ((.exchange 68 62 3),[(.neg 68),(.neg 62),(.pos 66),(.pos 69)]),
   ((.exchange 69 22 5),[(.neg 69),(.neg 22),(.pos 61),(.pos 64)]),
   ((.exchange 69 23 5),[(.neg 69),(.neg 23),(.pos 62),(.pos 64)]),
   ((.exchange 69 24 5),[(.neg 69),(.neg 24),(.pos 63),(.pos 64)]),
   ((.exchange 69 28 4),[(.neg 69),(.neg 28),(.pos 65),(.pos 68)]),
   ((.exchange 69 29 4),[(.neg 69),(.neg 29),(.pos 66),(.pos 68)]),
   ((.exchange 69 30 4),[(.neg 69),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 69 42 5),[(.neg 69),(.neg 42),(.pos 61),(.pos 64)]),
   (.newPoint,[(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_1 : List (Origin 70 29 × List Sat.Literal) :=
  [((.excluded 0),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 68)]),
   ((.excluded 1),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 58),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 2),[(.neg 69),(.neg 68),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 64),(.pos 65),(.pos 66),(.pos 67)]),
   ((.excluded 3),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 64)]),
   ((.excluded 4),[(.neg 69),(.neg 68),(.neg 64),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 65),(.pos 66),(.pos 67)]),
   ((.excluded 5),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 6),[(.neg 69),(.neg 68),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 65),(.pos 66),(.pos 67)]),
   ((.excluded 7),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 69)]),
   ((.excluded 8),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60)]),
   ((.excluded 9),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 60),(.neg 59),(.neg 58),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 61),(.pos 62),(.pos 63),(.pos 68)]),
   ((.excluded 10),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 60),(.neg 59),(.neg 58),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 61),(.pos 62),(.pos 63)]),
   ((.excluded 11),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 68)]),
   ((.excluded 12),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 69)]),
   ((.excluded 13),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 14),[(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 15),[(.neg 69),(.neg 68),(.neg 64),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 65),(.pos 66),(.pos 67)]),
   ((.excluded 16),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 68)]),
   ((.excluded 17),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 69)]),
   ((.excluded 18),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60)]),
   ((.excluded 19),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 20),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 21),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57),(.pos 69)]),
   ((.excluded 22),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57),(.pos 61),(.pos 62),(.pos 63),(.pos 68)]),
   ((.excluded 23),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57),(.pos 61),(.pos 62),(.pos 63)]),
   ((.excluded 24),[(.neg 69),(.neg 68),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57),(.pos 64),(.pos 65),(.pos 66),(.pos 67)]),
   ((.excluded 25),[(.neg 69),(.neg 68),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57),(.pos 65),(.pos 66),(.pos 67)]),
   ((.excluded 26),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57),(.pos 64)]),
   ((.excluded 27),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57),(.pos 68)]),
   ((.excluded 28),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57)])]

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
        Papers.RationalityTen.MatroidChecked.FastSemanticChecks.RawWitness 8 (N7R4.familyMasks.get 7)
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


end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C7

/- Source: MatroidCatalogue/Cases/N8R4C7Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C7

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
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C7.formula []
    exact Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C7.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 8 4 (target w),family_mem 8 4 (target w) hw.1,?_⟩
    exact validWitness_sound 8 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C7

/- Source: MatroidCatalogue/Cases/N8R4C8Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C8

abbrev U := N8R4.grid
noncomputable def old : Finset (Finset (Fin 8)) := N7R4.family 8
noncomputable def newIndexTree : Table ℕ := (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf 35) (.leaf 36)) (.node 3 (.leaf 37) (.leaf 38))) (.node 6 (.node 5 (.leaf 39) (.leaf 40)) (.node 7 (.leaf 41) (.leaf 42)))) (.node 12 (.node 10 (.node 9 (.leaf 43) (.leaf 44)) (.node 11 (.leaf 45) (.leaf 46))) (.node 14 (.node 13 (.leaf 47) (.leaf 48)) (.node 15 (.leaf 49) (.node 16 (.leaf 50) (.leaf 51)))))) (.node 26 (.node 21 (.node 19 (.node 18 (.leaf 52) (.leaf 53)) (.node 20 (.leaf 54) (.leaf 55))) (.node 23 (.node 22 (.leaf 56) (.leaf 57)) (.node 24 (.leaf 58) (.node 25 (.leaf 59) (.leaf 60))))) (.node 30 (.node 28 (.node 27 (.leaf 61) (.leaf 62)) (.node 29 (.leaf 63) (.leaf 64))) (.node 32 (.node 31 (.leaf 65) (.leaf 66)) (.node 33 (.leaf 67) (.node 34 (.leaf 68) (.leaf 69)))))))
noncomputable def newIndex (i : Fin 35) : Fin 70 := Fin.ofNat 70 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 7 (.node 3 (.node 1 (.leaf (13690208256,12,6212808)) (.node 2 (.leaf (3422552064,12,6210099)) (.leaf (17112760320,19,14599816)))) (.node 5 (.node 4 (.leaf (31457280,12,6064947)) (.leaf (13721665536,19,14527240))) (.node 6 (.leaf (3454009344,19,14524972)) (.leaf (17144217600,33,14599816))))) (.node 11 (.node 9 (.node 8 (.leaf (31200,99,16434824)) (.leaf (13690239456,100,16434824))) (.node 10 (.leaf (3422583264,100,16433690)) (.leaf (17112791520,101,16434824)))) (.node 13 (.node 12 (.leaf (31488480,100,16288538)) (.leaf (13721696736,101,16362248))) (.node 14 (.leaf (3454040544,101,16359980)) (.leaf (17144248800,102,16434824))))))

noncomputable def models (i : Fin 15) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 15) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 15) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 70, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (7 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 70, (7 : Fin 8) ∈ U i → ∃ j : Fin 35, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C8

/- Source: MatroidCatalogue/Cases/N8R4C8Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C8


noncomputable def certificates_0 : List (Origin 70 15 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.neg 2)]),
   ((.fixed 3),[(.neg 3)]),
   ((.fixed 4),[(.neg 4)]),
   ((.fixed 5),[(.neg 5)]),
   ((.fixed 6),[(.neg 6)]),
   ((.fixed 7),[(.neg 7)]),
   ((.fixed 8),[(.neg 8)]),
   ((.fixed 9),[(.neg 9)]),
   ((.fixed 10),[(.neg 10)]),
   ((.fixed 11),[(.neg 11)]),
   ((.fixed 12),[(.neg 12)]),
   ((.fixed 13),[(.neg 13)]),
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
   ((.fixed 31),[(.neg 31)]),
   ((.fixed 32),[(.neg 32)]),
   ((.fixed 33),[(.neg 33)]),
   ((.fixed 34),[(.neg 34)]),
   ((.exchange 20 41 6),[(.neg 41),(.neg 20),(.pos 1),(.pos 40)]),
   ((.exchange 20 47 6),[(.neg 47),(.neg 20),(.pos 1),(.pos 10),(.pos 40)]),
   ((.exchange 20 48 6),[(.neg 48),(.neg 20),(.pos 3),(.pos 10),(.pos 40)]),
   ((.exchange 20 57 4),[(.neg 57),(.neg 20),(.pos 15),(.pos 56)]),
   ((.exchange 20 58 4),[(.neg 58),(.neg 20),(.pos 17),(.pos 56)]),
   ((.exchange 20 59 4),[(.neg 59),(.neg 20),(.pos 15),(.pos 17),(.pos 56)]),
   ((.exchange 20 62 2),[(.neg 62),(.neg 20),(.pos 19),(.pos 61)]),
   ((.exchange 20 65 2),[(.neg 65),(.neg 20),(.pos 31),(.pos 61)]),
   ((.exchange 20 66 2),[(.neg 66),(.neg 20),(.pos 19),(.pos 31),(.pos 61)]),
   ((.exchange 20 67 0),[(.neg 67),(.neg 20),(.pos 33),(.pos 63)]),
   ((.exchange 20 68 0),[(.neg 68),(.neg 20),(.pos 24),(.pos 33),(.pos 63)]),
   ((.exchange 21 40 6),[(.neg 40),(.neg 21),(.pos 1),(.pos 41)]),
   ((.exchange 21 42 6),[(.neg 42),(.neg 21),(.pos 1),(.pos 4),(.pos 41)]),
   ((.exchange 21 43 6),[(.neg 43),(.neg 21),(.pos 4),(.pos 41)]),
   ((.exchange 21 46 6),[(.neg 46),(.neg 21),(.pos 1),(.pos 11),(.pos 41)]),
   ((.exchange 21 47 6),[(.neg 47),(.neg 21),(.pos 11),(.pos 41)]),
   ((.exchange 21 48 6),[(.neg 48),(.neg 21),(.pos 1),(.pos 4),(.pos 11),(.pos 41)]),
   ((.exchange 21 49 6),[(.neg 49),(.neg 21),(.pos 4),(.pos 11),(.pos 41)]),
   ((.exchange 21 56 4),[(.neg 56),(.neg 21),(.pos 15),(.pos 57)]),
   ((.exchange 21 61 2),[(.neg 61),(.neg 21),(.pos 19),(.pos 62)]),
   ((.exchange 21 65 2),[(.neg 65),(.neg 21),(.pos 19),(.pos 32),(.pos 62)]),
   ((.exchange 21 66 2),[(.neg 66),(.neg 21),(.pos 32),(.pos 62)]),
   ((.exchange 22 41 6),[(.neg 41),(.neg 22),(.pos 2),(.pos 3),(.pos 42)]),
   ((.exchange 22 47 6),[(.neg 47),(.neg 22),(.pos 2),(.pos 3),(.pos 12),(.pos 42)]),
   ((.exchange 22 48 6),[(.neg 48),(.neg 22),(.pos 12),(.pos 42)]),
   ((.exchange 22 56 4),[(.neg 56),(.neg 22),(.pos 17),(.pos 58)]),
   ((.exchange 22 67 0),[(.neg 67),(.neg 22),(.pos 24),(.pos 34),(.pos 64)]),
   ((.exchange 22 68 0),[(.neg 68),(.neg 22),(.pos 34),(.pos 64)]),
   ((.exchange 23 41 6),[(.neg 41),(.neg 23),(.pos 4),(.pos 43)]),
   ((.exchange 23 47 6),[(.neg 47),(.neg 23),(.pos 4),(.pos 13),(.pos 43)]),
   ((.exchange 23 48 6),[(.neg 48),(.neg 23),(.pos 2),(.pos 13),(.pos 43)]),
   ((.exchange 23 56 4),[(.neg 56),(.neg 23),(.pos 16),(.pos 18),(.pos 59)]),
   ((.exchange 26 41 6),[(.neg 41),(.neg 26),(.pos 5),(.pos 10),(.pos 46)]),
   ((.exchange 26 47 6),[(.neg 47),(.neg 26),(.pos 5),(.pos 46)]),
   ((.exchange 26 48 6),[(.neg 48),(.neg 26),(.pos 7),(.pos 46)]),
   ((.exchange 26 61 2),[(.neg 61),(.neg 26),(.pos 31),(.pos 65)]),
   ((.exchange 26 62 2),[(.neg 62),(.neg 26),(.pos 25),(.pos 31),(.pos 65)]),
   ((.exchange 26 63 0),[(.neg 63),(.neg 26),(.pos 33),(.pos 67)]),
   ((.exchange 26 64 0),[(.neg 64),(.neg 26),(.pos 30),(.pos 33),(.pos 67)]),
   ((.exchange 26 66 2),[(.neg 66),(.neg 26),(.pos 25),(.pos 65)]),
   ((.exchange 26 68 0),[(.neg 68),(.neg 26),(.pos 30),(.pos 67)]),
   ((.exchange 27 40 6),[(.neg 40),(.neg 27),(.pos 5),(.pos 11),(.pos 47)]),
   ((.exchange 27 41 6),[(.neg 41),(.neg 27),(.pos 11),(.pos 47)]),
   ((.exchange 27 42 6),[(.neg 42),(.neg 27),(.pos 5),(.pos 8),(.pos 11),(.pos 47)]),
   ((.exchange 27 43 6),[(.neg 43),(.neg 27),(.pos 8),(.pos 11),(.pos 47)]),
   ((.exchange 27 46 6),[(.neg 46),(.neg 27),(.pos 5),(.pos 47)]),
   ((.exchange 27 48 6),[(.neg 48),(.neg 27),(.pos 5),(.pos 8),(.pos 47)]),
   ((.exchange 27 49 6),[(.neg 49),(.neg 27),(.pos 8),(.pos 47)]),
   ((.exchange 27 61 2),[(.neg 61),(.neg 27),(.pos 25),(.pos 32),(.pos 66)]),
   ((.exchange 27 62 2),[(.neg 62),(.neg 27),(.pos 32),(.pos 66)]),
   ((.exchange 27 65 2),[(.neg 65),(.neg 27),(.pos 25),(.pos 66)]),
   ((.exchange 28 40 6),[(.neg 40),(.neg 28),(.pos 7),(.pos 12),(.pos 48)]),
   ((.exchange 28 41 6),[(.neg 41),(.neg 28),(.pos 6),(.pos 7),(.pos 12),(.pos 48)]),
   ((.exchange 28 42 6),[(.neg 42),(.neg 28),(.pos 12),(.pos 48)]),
   ((.exchange 28 43 6),[(.neg 43),(.neg 28),(.pos 6),(.pos 12),(.pos 48)]),
   ((.exchange 28 46 6),[(.neg 46),(.neg 28),(.pos 7),(.pos 48)]),
   ((.exchange 28 47 6),[(.neg 47),(.neg 28),(.pos 6),(.pos 7),(.pos 48)]),
   ((.exchange 28 49 6),[(.neg 49),(.neg 28),(.pos 6),(.pos 48)]),
   ((.exchange 28 63 0),[(.neg 63),(.neg 28),(.pos 30),(.pos 34),(.pos 68)]),
   ((.exchange 28 64 0),[(.neg 64),(.neg 28),(.pos 34),(.pos 68)]),
   ((.exchange 28 67 0),[(.neg 67),(.neg 28),(.pos 30),(.pos 68)]),
   ((.exchange 29 41 6),[(.neg 41),(.neg 29),(.pos 8),(.pos 13),(.pos 49)]),
   ((.exchange 29 47 6),[(.neg 47),(.neg 29),(.pos 8),(.pos 49)]),
   ((.exchange 29 48 6),[(.neg 48),(.neg 29),(.pos 6),(.pos 49)]),
   ((.exchange 35 20 7),[(.neg 35),(.neg 20),(.pos 1),(.pos 15)]),
   ((.exchange 36 20 7),[(.neg 36),(.neg 20),(.pos 0),(.pos 2),(.pos 16)]),
   ((.exchange 37 20 7),[(.neg 37),(.neg 20),(.pos 3),(.pos 17)]),
   ((.exchange 38 20 7),[(.neg 38),(.neg 20),(.pos 0),(.pos 4),(.pos 18)]),
   ((.exchange 39 20 7),[(.neg 39),(.neg 20),(.pos 1),(.pos 19)]),
   ((.exchange 44 20 7),[(.neg 44),(.neg 20),(.pos 3),(.pos 24)]),
   ((.exchange 45 20 7),[(.neg 45),(.neg 20),(.pos 5),(.pos 9),(.pos 25)]),
   ((.exchange 50 20 7),[(.neg 50),(.neg 20),(.pos 7),(.pos 14),(.pos 30)]),
   ((.exchange 51 20 7),[(.neg 51),(.neg 20),(.pos 10),(.pos 31)]),
   ((.exchange 52 20 7),[(.neg 52),(.neg 20),(.pos 9),(.pos 11),(.pos 32)]),
   ((.exchange 53 20 7),[(.neg 53),(.neg 20),(.pos 10),(.pos 33)]),
   ((.exchange 54 20 7),[(.neg 54),(.neg 20),(.pos 12),(.pos 14),(.pos 34)]),
   ((.exchange 55 20 7),[(.neg 55),(.neg 20),(.pos 15),(.pos 19)]),
   ((.exchange 60 20 7),[(.neg 60),(.neg 20),(.pos 17),(.pos 24)]),
   ((.exchange 69 20 7),[(.neg 69),(.neg 20),(.pos 31),(.pos 33)]),
   (.newPoint,[(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 0),[(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 65),(.pos 66),(.pos 69)]),
   ((.excluded 1),[(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 63),(.pos 64),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 2),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 69)]),
   ((.excluded 3),[(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 4),[(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 61),(.pos 62),(.pos 65),(.pos 66),(.pos 69)]),
   ((.excluded 5),[(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 63),(.pos 64),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 6),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 69)]),
   ((.excluded 7),[(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 8),[(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 65),(.pos 66),(.pos 69)]),
   ((.excluded 9),[(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 63),(.pos 64),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 10),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 69)]),
   ((.excluded 11),[(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 12),[(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 61),(.pos 62),(.pos 65),(.pos 66),(.pos 69)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_1 : List (Origin 70 15 × List Sat.Literal) :=
  [((.excluded 13),[(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 63),(.pos 64),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 14),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 69)])]

theorem certificates_1_valid : ∀ oc ∈ certificates_1,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



theorem witness_0 : ∀ j : Fin 15,
    let w : Fin 15 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 15,
      let w : Fin 15 := ⟨0 + j.val,by omega⟩
      target w < MatroidCatalogue.count 8 4 ∧
        Papers.RationalityTen.MatroidChecked.FastSemanticChecks.RawWitness 8 (N7R4.familyMasks.get 8)
        (fun i : Fin 70 => N8R4.gridMasks.get i.val) newIndex (models w)
        (N8R4.familyMasks.get (target w)) (permutation w) := by
    refine (Fin.forall_fin_add (m := 7) (n := 8) _).2 ⟨?_, ?_⟩
    · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
      · decide +kernel
      · decide +kernel
    · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
      · decide +kernel
      · decide +kernel
  intro j
  have hj := hfast j
  exact ⟨hj.1,Papers.RationalityTen.MatroidChecked.FastSemanticChecks.rawWitness_sound 8 _ _ _ _ _ _ hj.2⟩


end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C8

/- Source: MatroidCatalogue/Cases/N8R4C8Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C8

noncomputable def certificates : List (Origin 70 15 × List Sat.Literal) :=
  certificates_0 ++ certificates_1

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  intro oc hoc
  simp only [certificates,List.mem_append,or_assoc] at hoc
  rcases hoc with h0 | h1
  · exact certificates_0_valid oc h0
  · exact certificates_1_valid oc h1

theorem models_valid : ∀ w : Fin 15,
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 15) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 8) 4)
    (hold : M.bases.filter ((7 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 8 4, IsomorphicWithin 8 M.bases B := by
  apply extension_covered_of_certificate (n:=7) (r:=4) (by decide)
    catalogue old U newIndex models certificates
    N8R4.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C8.formula []
    exact Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C8.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 8 4 (target w),family_mem 8 4 (target w) hw.1,?_⟩
    exact validWitness_sound 8 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C8

/- Source: MatroidCatalogue/Cases/N8R4C9Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C9

abbrev U := N8R4.grid
noncomputable def old : Finset (Finset (Fin 8)) := N7R4.family 9
noncomputable def newIndexTree : Table ℕ := (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf 35) (.leaf 36)) (.node 3 (.leaf 37) (.leaf 38))) (.node 6 (.node 5 (.leaf 39) (.leaf 40)) (.node 7 (.leaf 41) (.leaf 42)))) (.node 12 (.node 10 (.node 9 (.leaf 43) (.leaf 44)) (.node 11 (.leaf 45) (.leaf 46))) (.node 14 (.node 13 (.leaf 47) (.leaf 48)) (.node 15 (.leaf 49) (.node 16 (.leaf 50) (.leaf 51)))))) (.node 26 (.node 21 (.node 19 (.node 18 (.leaf 52) (.leaf 53)) (.node 20 (.leaf 54) (.leaf 55))) (.node 23 (.node 22 (.leaf 56) (.leaf 57)) (.node 24 (.leaf 58) (.node 25 (.leaf 59) (.leaf 60))))) (.node 30 (.node 28 (.node 27 (.leaf 61) (.leaf 62)) (.node 29 (.leaf 63) (.leaf 64))) (.node 32 (.node 31 (.leaf 65) (.leaf 66)) (.node 33 (.leaf 67) (.node 34 (.leaf 68) (.leaf 69)))))))
noncomputable def newIndex (i : Fin 35) : Fin 70 := Fin.ofNat 70 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (13690208256,13,6248648)) (.leaf (20602421248,14,6246947))) (.node 3 (.leaf (34292629504,20,10442376)) (.leaf (12916359168,19,8334088)))) (.node 6 (.node 5 (.leaf (836763648,19,8219400)) (.leaf (13721665536,23,10333512))) (.node 7 (.leaf (33518780416,34,12535432)) (.node 8 (.leaf (21439184896,34,12478088)) (.leaf (34324086784,35,14599816)))))) (.node 14 (.node 11 (.node 10 (.leaf (817632,100,11789960)) (.leaf (13691025888,103,16434824))) (.node 12 (.leaf (12917176800,104,16427208)) (.node 13 (.leaf (837581280,104,16341192)) (.leaf (13722483168,105,16434824))))) (.node 16 (.node 15 (.leaf (20603238880,106,11789960)) (.leaf (34293447136,107,16434824))) (.node 17 (.leaf (33519598048,108,16434824)) (.node 18 (.leaf (21440002528,108,16406152)) (.leaf (34324904416,109,16434824)))))))

noncomputable def models (i : Fin 19) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 19) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 19) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 70, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (7 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 70, (7 : Fin 8) ∈ U i → ∃ j : Fin 35, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C9

/- Source: MatroidCatalogue/Cases/N8R4C9Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C9


noncomputable def certificates_0 : List (Origin 70 19 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.neg 2)]),
   ((.fixed 3),[(.neg 3)]),
   ((.fixed 4),[(.neg 4)]),
   ((.fixed 5),[(.neg 5)]),
   ((.fixed 6),[(.neg 6)]),
   ((.fixed 7),[(.neg 7)]),
   ((.fixed 8),[(.neg 8)]),
   ((.fixed 9),[(.neg 9)]),
   ((.fixed 10),[(.neg 10)]),
   ((.fixed 11),[(.neg 11)]),
   ((.fixed 12),[(.neg 12)]),
   ((.fixed 13),[(.neg 13)]),
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
   ((.fixed 31),[(.neg 31)]),
   ((.fixed 32),[(.neg 32)]),
   ((.fixed 33),[(.pos 33)]),
   ((.fixed 34),[(.pos 34)]),
   ((.exchange 20 41 6),[(.neg 41),(.neg 20),(.pos 1),(.pos 40)]),
   ((.exchange 20 48 6),[(.neg 48),(.neg 20),(.pos 3),(.pos 10),(.pos 40)]),
   ((.exchange 20 57 4),[(.neg 57),(.neg 20),(.pos 15),(.pos 56)]),
   ((.exchange 20 58 4),[(.neg 58),(.neg 20),(.pos 17),(.pos 56)]),
   ((.exchange 20 59 4),[(.neg 59),(.neg 20),(.pos 15),(.pos 17),(.pos 56)]),
   ((.exchange 20 64 0),[(.neg 64),(.neg 20),(.pos 24),(.pos 63)]),
   ((.exchange 20 69 2),[(.neg 69),(.neg 20),(.pos 31),(.pos 61)]),
   ((.exchange 21 40 6),[(.neg 40),(.neg 21),(.pos 1),(.pos 41)]),
   ((.exchange 21 42 6),[(.neg 42),(.neg 21),(.pos 1),(.pos 4),(.pos 41)]),
   ((.exchange 21 43 6),[(.neg 43),(.neg 21),(.pos 4),(.pos 41)]),
   ((.exchange 21 46 6),[(.neg 46),(.neg 21),(.pos 1),(.pos 11),(.pos 41)]),
   ((.exchange 21 47 6),[(.neg 47),(.neg 21),(.pos 11),(.pos 41)]),
   ((.exchange 21 48 6),[(.neg 48),(.neg 21),(.pos 1),(.pos 4),(.pos 11),(.pos 41)]),
   ((.exchange 21 49 6),[(.neg 49),(.neg 21),(.pos 4),(.pos 11),(.pos 41)]),
   ((.exchange 21 53 6),[(.neg 53),(.neg 21),(.pos 11),(.pos 41)]),
   ((.exchange 21 54 6),[(.neg 54),(.neg 21),(.pos 4),(.pos 11),(.pos 41)]),
   ((.exchange 21 56 4),[(.neg 56),(.neg 21),(.pos 15),(.pos 57)]),
   ((.exchange 21 69 2),[(.neg 69),(.neg 21),(.pos 32),(.pos 62)]),
   ((.exchange 22 41 6),[(.neg 41),(.neg 22),(.pos 2),(.pos 3),(.pos 42)]),
   ((.exchange 22 48 6),[(.neg 48),(.neg 22),(.pos 12),(.pos 42)]),
   ((.exchange 22 56 4),[(.neg 56),(.neg 22),(.pos 17),(.pos 58)]),
   ((.exchange 22 63 0),[(.neg 63),(.neg 22),(.pos 24),(.pos 64)]),
   ((.exchange 23 41 6),[(.neg 41),(.neg 23),(.pos 4),(.pos 43)]),
   ((.exchange 23 48 6),[(.neg 48),(.neg 23),(.pos 2),(.pos 13),(.pos 43)]),
   ((.exchange 23 56 4),[(.neg 56),(.neg 23),(.pos 16),(.pos 18),(.pos 59)]),
   ((.exchange 26 41 6),[(.neg 41),(.neg 26),(.pos 5),(.pos 10),(.pos 46)]),
   ((.exchange 26 48 6),[(.neg 48),(.neg 26),(.pos 7),(.pos 46)]),
   ((.exchange 26 68 0),[(.neg 68),(.neg 26),(.pos 30),(.pos 67)]),
   ((.exchange 26 69 2),[(.neg 69),(.neg 26),(.pos 31),(.pos 65)]),
   ((.exchange 27 41 6),[(.neg 41),(.neg 27),(.pos 11),(.pos 47)]),
   ((.exchange 27 48 6),[(.neg 48),(.neg 27),(.pos 5),(.pos 8),(.pos 47)]),
   ((.exchange 27 69 2),[(.neg 69),(.neg 27),(.pos 32),(.pos 66)]),
   ((.exchange 28 40 6),[(.neg 40),(.neg 28),(.pos 7),(.pos 12),(.pos 48)]),
   ((.exchange 28 41 6),[(.neg 41),(.neg 28),(.pos 6),(.pos 7),(.pos 12),(.pos 48)]),
   ((.exchange 28 42 6),[(.neg 42),(.neg 28),(.pos 12),(.pos 48)]),
   ((.exchange 28 43 6),[(.neg 43),(.neg 28),(.pos 6),(.pos 12),(.pos 48)]),
   ((.exchange 28 46 6),[(.neg 46),(.neg 28),(.pos 7),(.pos 48)]),
   ((.exchange 28 47 6),[(.neg 47),(.neg 28),(.pos 6),(.pos 7),(.pos 48)]),
   ((.exchange 28 49 6),[(.neg 49),(.neg 28),(.pos 6),(.pos 48)]),
   ((.exchange 28 53 6),[(.neg 53),(.neg 28),(.pos 7),(.pos 12),(.pos 48)]),
   ((.exchange 28 54 6),[(.neg 54),(.neg 28),(.pos 12),(.pos 48)]),
   ((.exchange 28 67 0),[(.neg 67),(.neg 28),(.pos 30),(.pos 68)]),
   ((.exchange 29 41 6),[(.neg 41),(.neg 29),(.pos 8),(.pos 13),(.pos 49)]),
   ((.exchange 29 48 6),[(.neg 48),(.neg 29),(.pos 6),(.pos 49)]),
   ((.exchange 33 41 6),[(.neg 41),(.neg 33),(.pos 11),(.pos 53)]),
   ((.exchange 33 48 6),[(.neg 48),(.neg 33),(.pos 10),(.pos 14),(.pos 53)]),
   ((.exchange 33 61 2),[(.neg 61),(.neg 33),(.pos 31),(.pos 69)]),
   ((.exchange 33 62 2),[(.neg 62),(.neg 33),(.pos 32),(.pos 69)]),
   ((.exchange 33 65 2),[(.neg 65),(.neg 33),(.pos 31),(.pos 69)]),
   ((.exchange 33 66 2),[(.neg 66),(.neg 33),(.pos 32),(.pos 69)]),
   ((.exchange 34 41 6),[(.neg 41),(.neg 34),(.pos 13),(.pos 14),(.pos 54)]),
   ((.exchange 34 48 6),[(.neg 48),(.neg 34),(.pos 12),(.pos 54)]),
   ((.exchange 35 20 7),[(.neg 35),(.neg 20),(.pos 1),(.pos 15)]),
   ((.exchange 36 20 7),[(.neg 36),(.neg 20),(.pos 0),(.pos 2),(.pos 16)]),
   ((.exchange 37 20 7),[(.neg 37),(.neg 20),(.pos 3),(.pos 17)]),
   ((.exchange 38 20 7),[(.neg 38),(.neg 20),(.pos 0),(.pos 4),(.pos 18)]),
   ((.exchange 39 20 7),[(.neg 39),(.neg 20),(.pos 1),(.pos 19)]),
   ((.exchange 44 20 7),[(.neg 44),(.neg 20),(.pos 3),(.pos 24)]),
   ((.exchange 45 20 7),[(.neg 45),(.neg 20),(.pos 5),(.pos 9),(.pos 25)]),
   ((.exchange 50 20 7),[(.neg 50),(.neg 20),(.pos 7),(.pos 14),(.pos 30)]),
   ((.exchange 51 20 7),[(.neg 51),(.neg 20),(.pos 10),(.pos 31)]),
   ((.exchange 52 20 7),[(.neg 52),(.neg 20),(.pos 9),(.pos 11),(.pos 32)]),
   ((.exchange 55 20 7),[(.neg 55),(.neg 20),(.pos 15),(.pos 19)]),
   ((.exchange 56 33 0),[(.neg 56),(.neg 33),(.pos 63),(.pos 67)]),
   ((.exchange 58 33 0),[(.neg 58),(.neg 33),(.pos 60),(.pos 64),(.pos 68)]),
   ((.exchange 60 20 7),[(.neg 60),(.neg 20),(.pos 17),(.pos 24)]),
   ((.exchange 63 27 4),[(.neg 63),(.neg 27),(.pos 57),(.pos 67)]),
   ((.exchange 64 27 4),[(.neg 64),(.neg 27),(.pos 59),(.pos 60),(.pos 68)]),
   ((.exchange 67 20 5),[(.neg 67),(.neg 20),(.pos 56),(.pos 63)]),
   ((.exchange 68 20 5),[(.neg 68),(.neg 20),(.pos 58),(.pos 60),(.pos 64)]),
   (.newPoint,[(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 0),[(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 65),(.pos 66),(.pos 69)]),
   ((.excluded 1),[(.neg 69),(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 63),(.pos 64),(.pos 67),(.pos 68)]),
   ((.excluded 2),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60)]),
   ((.excluded 3),[(.neg 68),(.neg 67),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 69)]),
   ((.excluded 4),[(.neg 64),(.neg 63),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 61),(.pos 62),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 5),[(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 61),(.pos 62),(.pos 65),(.pos 66),(.pos 69)]),
   ((.excluded 6),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 63),(.pos 64)]),
   ((.excluded 7),[(.neg 69),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 67),(.pos 68)]),
   ((.excluded 8),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 60)]),
   ((.excluded 9),[(.neg 54),(.neg 53),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 51),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 10),[(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 54),(.neg 53),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 51),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 65),(.pos 66),(.pos 69)]),
   ((.excluded 11),[(.neg 68),(.neg 67),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 51),(.pos 52),(.pos 55),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 69)]),
   ((.excluded 12),[(.neg 64),(.neg 63),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 51),(.pos 52),(.pos 55),(.pos 60),(.pos 61),(.pos 62),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 13),[(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 51),(.pos 52),(.pos 55),(.pos 60),(.pos 61),(.pos 62),(.pos 65),(.pos 66),(.pos 69)]),
   ((.excluded 14),[(.neg 69),(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 51),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 63),(.pos 64),(.pos 67),(.pos 68)]),
   ((.excluded 15),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 51),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60)]),
   ((.excluded 16),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 51),(.pos 52),(.pos 55),(.pos 60),(.pos 63),(.pos 64)]),
   ((.excluded 17),[(.neg 69),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 51),(.pos 52),(.pos 55),(.pos 60),(.pos 67),(.pos 68)]),
   ((.excluded 18),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 51),(.pos 52),(.pos 55),(.pos 60)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



theorem witness_0 : ∀ j : Fin 19,
    let w : Fin 19 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 19,
      let w : Fin 19 := ⟨0 + j.val,by omega⟩
      target w < MatroidCatalogue.count 8 4 ∧
        Papers.RationalityTen.MatroidChecked.FastSemanticChecks.RawWitness 8 (N7R4.familyMasks.get 9)
        (fun i : Fin 70 => N8R4.gridMasks.get i.val) newIndex (models w)
        (N8R4.familyMasks.get (target w)) (permutation w) := by
    refine (Fin.forall_fin_add (m := 9) (n := 10) _).2 ⟨?_, ?_⟩
    · refine (Fin.forall_fin_add (m := 4) (n := 5) _).2 ⟨?_, ?_⟩
      · decide +kernel
      · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
        · decide +kernel
        · decide +kernel
    · refine (Fin.forall_fin_add (m := 5) (n := 5) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
        · decide +kernel
        · decide +kernel
      · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
        · decide +kernel
        · decide +kernel
  intro j
  have hj := hfast j
  exact ⟨hj.1,Papers.RationalityTen.MatroidChecked.FastSemanticChecks.rawWitness_sound 8 _ _ _ _ _ _ hj.2⟩


end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C9

/- Source: MatroidCatalogue/Cases/N8R4C9Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C9

noncomputable def certificates : List (Origin 70 19 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 19,
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 19) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 8) 4)
    (hold : M.bases.filter ((7 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 8 4, IsomorphicWithin 8 M.bases B := by
  apply extension_covered_of_certificate (n:=7) (r:=4) (by decide)
    catalogue old U newIndex models certificates
    N8R4.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C9.formula []
    exact Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C9.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 8 4 (target w),family_mem 8 4 (target w) hw.1,?_⟩
    exact validWitness_sound 8 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C9


end
end
end BundlePart5

section BundlePart6
/- Source: MatroidChecked/SemanticChunks/Cases02Part06.lean -/






@[expose] public section
noncomputable section

/- Source: MatroidCatalogue/Cases/N8R4C10Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C10

abbrev U := N8R4.grid
noncomputable def old : Finset (Finset (Fin 8)) := N7R4.family 10
noncomputable def newIndexTree : Table ℕ := (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf 35) (.leaf 36)) (.node 3 (.leaf 37) (.leaf 38))) (.node 6 (.node 5 (.leaf 39) (.leaf 40)) (.node 7 (.leaf 41) (.leaf 42)))) (.node 12 (.node 10 (.node 9 (.leaf 43) (.leaf 44)) (.node 11 (.leaf 45) (.leaf 46))) (.node 14 (.node 13 (.leaf 47) (.leaf 48)) (.node 15 (.leaf 49) (.node 16 (.leaf 50) (.leaf 51)))))) (.node 26 (.node 21 (.node 19 (.node 18 (.leaf 52) (.leaf 53)) (.node 20 (.leaf 54) (.leaf 55))) (.node 23 (.node 22 (.leaf 56) (.leaf 57)) (.node 24 (.leaf 58) (.node 25 (.leaf 59) (.leaf 60))))) (.node 30 (.node 28 (.node 27 (.leaf 61) (.leaf 62)) (.node 29 (.leaf 63) (.leaf 64))) (.node 32 (.node 31 (.leaf 65) (.leaf 66)) (.node 33 (.leaf 67) (.node 34 (.leaf 68) (.leaf 69)))))))
noncomputable def newIndex (i : Fin 35) : Fin 70 := Fin.ofNat 70 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 14 (.node 7 (.node 3 (.node 1 (.leaf (17112760320,21,10442376)) (.node 2 (.leaf (30870077440,15,6248648)) (.leaf (20602421248,15,6246947)))) (.node 5 (.node 4 (.leaf (34292629504,22,10442376)) (.leaf (16137584640,33,12535432))) (.node 6 (.leaf (1038090240,33,12478088)) (.leaf (17144217600,36,14599816))))) (.node 10 (.node 8 (.leaf (21237858304,34,10413704)) (.node 9 (.leaf (34122760192,35,12535432)) (.leaf (21439184896,35,12476954)))) (.node 12 (.node 11 (.leaf (30297554944,34,10442376)) (.leaf (33518780416,35,12534298))) (.node 13 (.leaf (31102861312,35,12478088)) (.leaf (34324086784,37,14599816)))))) (.node 21 (.node 17 (.node 15 (.leaf (1014240,101,11789960)) (.node 16 (.leaf (30871091680,107,11789960)) (.leaf (20603435488,107,11788826)))) (.node 19 (.node 18 (.leaf (17113774560,110,16434824)) (.leaf (34293643744,111,16434824))) (.node 20 (.leaf (16138598880,112,16434824)) (.leaf (1039104480,112,16406152))))) (.node 25 (.node 23 (.node 22 (.leaf (17145231840,113,16434824)) (.leaf (21238872544,114,16434824))) (.node 24 (.leaf (34123774432,115,16434824)) (.leaf (21440199136,115,16405018)))) (.node 27 (.node 26 (.leaf (30298569184,114,16406152)) (.leaf (33519794656,115,16433690))) (.node 28 (.leaf (31103875552,115,16406152)) (.leaf (34325101024,116,16434824)))))))

noncomputable def models (i : Fin 29) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 29) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 29) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 70, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (7 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 70, (7 : Fin 8) ∈ U i → ∃ j : Fin 35, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C10

/- Source: MatroidCatalogue/Cases/N8R4C10Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C10


noncomputable def certificates_0 : List (Origin 70 29 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.neg 2)]),
   ((.fixed 3),[(.neg 3)]),
   ((.fixed 4),[(.neg 4)]),
   ((.fixed 5),[(.neg 5)]),
   ((.fixed 6),[(.neg 6)]),
   ((.fixed 7),[(.neg 7)]),
   ((.fixed 8),[(.neg 8)]),
   ((.fixed 9),[(.neg 9)]),
   ((.fixed 10),[(.neg 10)]),
   ((.fixed 11),[(.neg 11)]),
   ((.fixed 12),[(.neg 12)]),
   ((.fixed 13),[(.neg 13)]),
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
   ((.fixed 32),[(.pos 32)]),
   ((.fixed 33),[(.pos 33)]),
   ((.fixed 34),[(.pos 34)]),
   ((.exchange 20 41 6),[(.neg 41),(.neg 20),(.pos 1),(.pos 40)]),
   ((.exchange 20 46 6),[(.neg 46),(.neg 20),(.pos 10),(.pos 40)]),
   ((.exchange 20 57 4),[(.neg 57),(.neg 20),(.pos 15),(.pos 56)]),
   ((.exchange 20 58 4),[(.neg 58),(.neg 20),(.pos 17),(.pos 56)]),
   ((.exchange 20 59 4),[(.neg 59),(.neg 20),(.pos 15),(.pos 17),(.pos 56)]),
   ((.exchange 20 62 2),[(.neg 62),(.neg 20),(.pos 19),(.pos 61)]),
   ((.exchange 20 64 0),[(.neg 64),(.neg 20),(.pos 24),(.pos 63)]),
   ((.exchange 21 40 6),[(.neg 40),(.neg 21),(.pos 1),(.pos 41)]),
   ((.exchange 21 42 6),[(.neg 42),(.neg 21),(.pos 1),(.pos 4),(.pos 41)]),
   ((.exchange 21 43 6),[(.neg 43),(.neg 21),(.pos 4),(.pos 41)]),
   ((.exchange 21 46 6),[(.neg 46),(.neg 21),(.pos 1),(.pos 11),(.pos 41)]),
   ((.exchange 21 47 6),[(.neg 47),(.neg 21),(.pos 11),(.pos 41)]),
   ((.exchange 21 48 6),[(.neg 48),(.neg 21),(.pos 1),(.pos 4),(.pos 11),(.pos 41)]),
   ((.exchange 21 49 6),[(.neg 49),(.neg 21),(.pos 4),(.pos 11),(.pos 41)]),
   ((.exchange 21 51 6),[(.neg 51),(.neg 21),(.pos 1),(.pos 11),(.pos 41)]),
   ((.exchange 21 52 6),[(.neg 52),(.neg 21),(.pos 11),(.pos 41)]),
   ((.exchange 21 53 6),[(.neg 53),(.neg 21),(.pos 11),(.pos 41)]),
   ((.exchange 21 54 6),[(.neg 54),(.neg 21),(.pos 4),(.pos 11),(.pos 41)]),
   ((.exchange 21 56 4),[(.neg 56),(.neg 21),(.pos 15),(.pos 57)]),
   ((.exchange 21 61 2),[(.neg 61),(.neg 21),(.pos 19),(.pos 62)]),
   ((.exchange 22 41 6),[(.neg 41),(.neg 22),(.pos 2),(.pos 3),(.pos 42)]),
   ((.exchange 22 46 6),[(.neg 46),(.neg 22),(.pos 3),(.pos 12),(.pos 42)]),
   ((.exchange 22 56 4),[(.neg 56),(.neg 22),(.pos 17),(.pos 58)]),
   ((.exchange 22 63 0),[(.neg 63),(.neg 22),(.pos 24),(.pos 64)]),
   ((.exchange 23 41 6),[(.neg 41),(.neg 23),(.pos 4),(.pos 43)]),
   ((.exchange 23 46 6),[(.neg 46),(.neg 23),(.pos 2),(.pos 4),(.pos 13),(.pos 43)]),
   ((.exchange 23 56 4),[(.neg 56),(.neg 23),(.pos 16),(.pos 18),(.pos 59)]),
   ((.exchange 26 40 6),[(.neg 40),(.neg 26),(.pos 10),(.pos 46)]),
   ((.exchange 26 41 6),[(.neg 41),(.neg 26),(.pos 5),(.pos 10),(.pos 46)]),
   ((.exchange 26 42 6),[(.neg 42),(.neg 26),(.pos 7),(.pos 10),(.pos 46)]),
   ((.exchange 26 43 6),[(.neg 43),(.neg 26),(.pos 5),(.pos 7),(.pos 10),(.pos 46)]),
   ((.exchange 26 47 6),[(.neg 47),(.neg 26),(.pos 5),(.pos 46)]),
   ((.exchange 26 48 6),[(.neg 48),(.neg 26),(.pos 7),(.pos 46)]),
   ((.exchange 26 49 6),[(.neg 49),(.neg 26),(.pos 5),(.pos 7),(.pos 46)]),
   ((.exchange 26 51 6),[(.neg 51),(.neg 26),(.pos 10),(.pos 46)]),
   ((.exchange 26 52 6),[(.neg 52),(.neg 26),(.pos 5),(.pos 10),(.pos 46)]),
   ((.exchange 26 53 6),[(.neg 53),(.neg 26),(.pos 10),(.pos 46)]),
   ((.exchange 26 54 6),[(.neg 54),(.neg 26),(.pos 7),(.pos 10),(.pos 46)]),
   ((.exchange 26 66 2),[(.neg 66),(.neg 26),(.pos 25),(.pos 65)]),
   ((.exchange 26 68 0),[(.neg 68),(.neg 26),(.pos 30),(.pos 67)]),
   ((.exchange 27 41 6),[(.neg 41),(.neg 27),(.pos 11),(.pos 47)]),
   ((.exchange 27 46 6),[(.neg 46),(.neg 27),(.pos 5),(.pos 47)]),
   ((.exchange 27 65 2),[(.neg 65),(.neg 27),(.pos 25),(.pos 66)]),
   ((.exchange 28 41 6),[(.neg 41),(.neg 28),(.pos 6),(.pos 7),(.pos 12),(.pos 48)]),
   ((.exchange 28 46 6),[(.neg 46),(.neg 28),(.pos 7),(.pos 48)]),
   ((.exchange 28 67 0),[(.neg 67),(.neg 28),(.pos 30),(.pos 68)]),
   ((.exchange 29 41 6),[(.neg 41),(.neg 29),(.pos 8),(.pos 13),(.pos 49)]),
   ((.exchange 29 46 6),[(.neg 46),(.neg 29),(.pos 6),(.pos 8),(.pos 49)]),
   ((.exchange 31 41 6),[(.neg 41),(.neg 31),(.pos 9),(.pos 10),(.pos 51)]),
   ((.exchange 31 46 6),[(.neg 46),(.neg 31),(.pos 10),(.pos 51)]),
   ((.exchange 32 41 6),[(.neg 41),(.neg 32),(.pos 11),(.pos 52)]),
   ((.exchange 32 46 6),[(.neg 46),(.neg 32),(.pos 9),(.pos 11),(.pos 52)]),
   ((.exchange 33 41 6),[(.neg 41),(.neg 33),(.pos 11),(.pos 53)]),
   ((.exchange 33 46 6),[(.neg 46),(.neg 33),(.pos 10),(.pos 53)]),
   ((.exchange 34 41 6),[(.neg 41),(.neg 34),(.pos 13),(.pos 14),(.pos 54)]),
   ((.exchange 34 46 6),[(.neg 46),(.neg 34),(.pos 12),(.pos 14),(.pos 54)]),
   ((.exchange 35 20 7),[(.neg 35),(.neg 20),(.pos 1),(.pos 15)]),
   ((.exchange 36 20 7),[(.neg 36),(.neg 20),(.pos 0),(.pos 2),(.pos 16)]),
   ((.exchange 37 20 7),[(.neg 37),(.neg 20),(.pos 3),(.pos 17)]),
   ((.exchange 38 20 7),[(.neg 38),(.neg 20),(.pos 0),(.pos 4),(.pos 18)]),
   ((.exchange 39 20 7),[(.neg 39),(.neg 20),(.pos 1),(.pos 19)]),
   ((.exchange 44 20 7),[(.neg 44),(.neg 20),(.pos 3),(.pos 24)]),
   ((.exchange 45 20 7),[(.neg 45),(.neg 20),(.pos 5),(.pos 9),(.pos 25)]),
   ((.exchange 50 20 7),[(.neg 50),(.neg 20),(.pos 7),(.pos 14),(.pos 30)]),
   ((.exchange 55 20 7),[(.neg 55),(.neg 20),(.pos 15),(.pos 19)]),
   ((.exchange 56 31 2),[(.neg 56),(.neg 31),(.pos 61),(.pos 65)]),
   ((.exchange 56 33 0),[(.neg 56),(.neg 33),(.pos 63),(.pos 67)]),
   ((.exchange 56 34 0),[(.neg 56),(.neg 34),(.pos 60),(.pos 63),(.pos 67)]),
   ((.exchange 57 31 2),[(.neg 57),(.neg 31),(.pos 55),(.pos 62),(.pos 66)]),
   ((.exchange 58 31 3),[(.neg 58),(.neg 31),(.pos 61),(.pos 65)]),
   ((.exchange 58 34 0),[(.neg 58),(.neg 34),(.pos 64),(.pos 68)]),
   ((.exchange 59 31 3),[(.neg 59),(.neg 31),(.pos 55),(.pos 62),(.pos 66)]),
   ((.exchange 60 20 7),[(.neg 60),(.neg 20),(.pos 17),(.pos 24)]),
   ((.exchange 61 26 4),[(.neg 61),(.neg 26),(.pos 56),(.pos 65)]),
   ((.exchange 61 33 0),[(.neg 61),(.neg 33),(.pos 63),(.pos 69)]),
   ((.exchange 61 49 4),[(.neg 61),(.neg 49),(.pos 55),(.pos 58),(.pos 65)]),
   ((.exchange 62 26 4),[(.neg 62),(.neg 26),(.pos 55),(.pos 57),(.pos 66)]),
   ((.exchange 62 33 1),[(.neg 62),(.neg 33),(.pos 63),(.pos 69)]),
   ((.exchange 62 34 1),[(.neg 62),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 62 49 4),[(.neg 62),(.neg 49),(.pos 59),(.pos 66)]),
   ((.exchange 62 53 1),[(.neg 62),(.neg 53),(.pos 63),(.pos 69)]),
   ((.exchange 62 54 1),[(.neg 62),(.neg 54),(.pos 64),(.pos 69)]),
   ((.exchange 63 27 4),[(.neg 63),(.neg 27),(.pos 57),(.pos 67)]),
   ((.exchange 63 31 2),[(.neg 63),(.neg 31),(.pos 61),(.pos 69)]),
   ((.exchange 63 32 2),[(.neg 63),(.neg 32),(.pos 62),(.pos 69)]),
   ((.exchange 64 27 4),[(.neg 64),(.neg 27),(.pos 59),(.pos 60),(.pos 68)]),
   ((.exchange 64 31 3),[(.neg 64),(.neg 31),(.pos 61),(.pos 69)]),
   ((.exchange 64 32 3),[(.neg 64),(.neg 32),(.pos 62),(.pos 69)]),
   ((.exchange 65 20 5),[(.neg 65),(.neg 20),(.pos 56),(.pos 61)]),
   ((.exchange 65 33 0),[(.neg 65),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 65 64 0),[(.neg 65),(.neg 64),(.pos 68),(.pos 69)]),
   ((.exchange 66 20 5),[(.neg 66),(.neg 20),(.pos 55),(.pos 57),(.pos 62)]),
   ((.exchange 66 33 1),[(.neg 66),(.neg 33),(.pos 67),(.pos 69)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_1 : List (Origin 70 29 × List Sat.Literal) :=
  [((.exchange 66 34 1),[(.neg 66),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 66 64 1),[(.neg 66),(.neg 64),(.pos 68),(.pos 69)]),
   ((.exchange 66 64 5),[(.neg 66),(.neg 64),(.pos 59),(.pos 62)]),
   ((.exchange 67 20 5),[(.neg 67),(.neg 20),(.pos 56),(.pos 63)]),
   ((.exchange 67 31 2),[(.neg 67),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 67 32 2),[(.neg 67),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 68 20 5),[(.neg 68),(.neg 20),(.pos 58),(.pos 60),(.pos 64)]),
   ((.exchange 68 31 3),[(.neg 68),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 68 32 3),[(.neg 68),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 68 51 3),[(.neg 68),(.neg 51),(.pos 65),(.pos 69)]),
   ((.exchange 68 52 3),[(.neg 68),(.neg 52),(.pos 66),(.pos 69)]),
   ((.exchange 69 20 5),[(.neg 69),(.neg 20),(.pos 61),(.pos 63)]),
   ((.exchange 69 21 5),[(.neg 69),(.neg 21),(.pos 62),(.pos 63)]),
   ((.exchange 69 23 5),[(.neg 69),(.neg 23),(.pos 62),(.pos 64)]),
   ((.exchange 69 26 4),[(.neg 69),(.neg 26),(.pos 65),(.pos 67)]),
   ((.exchange 69 27 4),[(.neg 69),(.neg 27),(.pos 66),(.pos 67)]),
   ((.exchange 69 28 4),[(.neg 69),(.neg 28),(.pos 65),(.pos 68)]),
   ((.exchange 69 29 4),[(.neg 69),(.neg 29),(.pos 66),(.pos 68)]),
   ((.exchange 69 40 5),[(.neg 69),(.neg 40),(.pos 61),(.pos 63)]),
   ((.exchange 69 46 4),[(.neg 69),(.neg 46),(.pos 65),(.pos 67)]),
   ((.exchange 69 48 4),[(.neg 69),(.neg 48),(.pos 65),(.pos 68)]),
   ((.exchange 69 57 4),[(.neg 69),(.neg 57),(.pos 66),(.pos 67)]),
   ((.exchange 69 57 5),[(.neg 69),(.neg 57),(.pos 62),(.pos 63)]),
   (.newPoint,[(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 0),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 69)]),
   ((.excluded 1),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 65),(.pos 66)]),
   ((.excluded 2),[(.neg 69),(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 63),(.pos 64),(.pos 67),(.pos 68)]),
   ((.excluded 3),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60)]),
   ((.excluded 4),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 5),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 6),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 69)]),
   ((.excluded 7),[(.neg 69),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 61),(.pos 62),(.pos 67),(.pos 68)]),
   ((.excluded 8),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 61),(.pos 62)]),
   ((.excluded 9),[(.neg 69),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 67),(.pos 68)]),
   ((.excluded 10),[(.neg 69),(.neg 68),(.neg 67),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 63),(.pos 64),(.pos 65),(.pos 66)]),
   ((.excluded 11),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 63),(.pos 64)]),
   ((.excluded 12),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 65),(.pos 66)]),
   ((.excluded 13),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 60)]),
   ((.excluded 14),[(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 15),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 65),(.pos 66)]),
   ((.excluded 16),[(.neg 69),(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 63),(.pos 64),(.pos 67),(.pos 68)]),
   ((.excluded 17),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 69)]),
   ((.excluded 18),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60)]),
   ((.excluded 19),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 55),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 20),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 55),(.pos 60),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 21),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 55),(.pos 60),(.pos 69)]),
   ((.excluded 22),[(.neg 69),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 55),(.pos 60),(.pos 61),(.pos 62),(.pos 67),(.pos 68)]),
   ((.excluded 23),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 55),(.pos 60),(.pos 61),(.pos 62)]),
   ((.excluded 24),[(.neg 69),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 55),(.pos 60),(.pos 67),(.pos 68)]),
   ((.excluded 25),[(.neg 69),(.neg 68),(.neg 67),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 55),(.pos 60),(.pos 63),(.pos 64),(.pos 65),(.pos 66)]),
   ((.excluded 26),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 55),(.pos 60),(.pos 63),(.pos 64)]),
   ((.excluded 27),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 55),(.pos 60),(.pos 65),(.pos 66)]),
   ((.excluded 28),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 55),(.pos 60)])]

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
        Papers.RationalityTen.MatroidChecked.FastSemanticChecks.RawWitness 8 (N7R4.familyMasks.get 10)
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


end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C10

/- Source: MatroidCatalogue/Cases/N8R4C10Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C10

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
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C10.formula []
    exact Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C10.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 8 4 (target w),family_mem 8 4 (target w) hw.1,?_⟩
    exact validWitness_sound 8 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C10

/- Source: MatroidCatalogue/Cases/N8R4C11Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C11

abbrev U := N8R4.grid
noncomputable def old : Finset (Finset (Fin 8)) := N7R4.family 11
noncomputable def newIndexTree : Table ℕ := (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf 35) (.leaf 36)) (.node 3 (.leaf 37) (.leaf 38))) (.node 6 (.node 5 (.leaf 39) (.leaf 40)) (.node 7 (.leaf 41) (.leaf 42)))) (.node 12 (.node 10 (.node 9 (.leaf 43) (.leaf 44)) (.node 11 (.leaf 45) (.leaf 46))) (.node 14 (.node 13 (.leaf 47) (.leaf 48)) (.node 15 (.leaf 49) (.node 16 (.leaf 50) (.leaf 51)))))) (.node 26 (.node 21 (.node 19 (.node 18 (.leaf 52) (.leaf 53)) (.node 20 (.leaf 54) (.leaf 55))) (.node 23 (.node 22 (.leaf 56) (.leaf 57)) (.node 24 (.leaf 58) (.node 25 (.leaf 59) (.leaf 60))))) (.node 30 (.node 28 (.node 27 (.leaf 61) (.leaf 62)) (.node 29 (.leaf 63) (.leaf 64))) (.node 32 (.node 31 (.leaf 65) (.leaf 66)) (.node 33 (.leaf 67) (.node 34 (.leaf 68) (.leaf 69)))))))
noncomputable def newIndex (i : Fin 35) : Fin 70 := Fin.ofNat 70 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 14 (.node 7 (.node 3 (.node 1 (.leaf (13690208256,16,6212808)) (.node 2 (.leaf (29729226752,20,8345736)) (.leaf (25165824000,20,8344840)))) (.node 5 (.node 4 (.leaf (34292629504,24,10442376)) (.leaf (12949913600,20,8269128))) (.node 6 (.leaf (870318080,20,8211784)) (.leaf (13755219968,24,10333512))))) (.node 10 (.node 8 (.leaf (25499271168,38,14599816)) (.node 9 (.leaf (34089205760,39,14596232)) (.leaf (25767706624,39,14537992)))) (.node 12 (.node 11 (.leaf (29525803008,38,14571144)) (.leaf (33820770304,39,14595336))) (.node 13 (.leaf (30062673920,39,14538888)) (.leaf (34357641216,40,14599816)))))) (.node 21 (.node 17 (.node 15 (.leaf (850912,103,7072520)) (.node 16 (.leaf (13691059168,117,16434824)) (.leaf (29730077664,118,16434824)))) (.node 19 (.node 18 (.leaf (25166674912,118,16434376)) (.leaf (34293480416,119,16434824))) (.node 20 (.leaf (12950764512,118,16362248)) (.leaf (871168992,118,16333576))))) (.node 25 (.node 23 (.node 22 (.leaf (13756070880,119,16362248)) (.leaf (25500122080,120,16434824))) (.node 24 (.leaf (34090056672,121,16431240)) (.leaf (25768557536,121,16373000)))) (.node 27 (.node 26 (.leaf (29526653920,120,16406152)) (.leaf (33821621216,121,16430344))) (.node 28 (.leaf (30063524832,121,16373896)) (.leaf (34358492128,122,16434824)))))))

noncomputable def models (i : Fin 29) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 29) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 29) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 70, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (7 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 70, (7 : Fin 8) ∈ U i → ∃ j : Fin 35, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C11

/- Source: MatroidCatalogue/Cases/N8R4C11Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C11


noncomputable def certificates_0 : List (Origin 70 29 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.neg 2)]),
   ((.fixed 3),[(.neg 3)]),
   ((.fixed 4),[(.neg 4)]),
   ((.fixed 5),[(.neg 5)]),
   ((.fixed 6),[(.neg 6)]),
   ((.fixed 7),[(.neg 7)]),
   ((.fixed 8),[(.neg 8)]),
   ((.fixed 9),[(.neg 9)]),
   ((.fixed 10),[(.neg 10)]),
   ((.fixed 11),[(.neg 11)]),
   ((.fixed 12),[(.neg 12)]),
   ((.fixed 13),[(.neg 13)]),
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
   ((.fixed 24),[(.pos 24)]),
   ((.fixed 25),[(.neg 25)]),
   ((.fixed 26),[(.pos 26)]),
   ((.fixed 27),[(.pos 27)]),
   ((.fixed 28),[(.pos 28)]),
   ((.fixed 29),[(.pos 29)]),
   ((.fixed 30),[(.pos 30)]),
   ((.fixed 31),[(.neg 31)]),
   ((.fixed 32),[(.neg 32)]),
   ((.fixed 33),[(.pos 33)]),
   ((.fixed 34),[(.pos 34)]),
   ((.exchange 20 41 6),[(.neg 41),(.neg 20),(.pos 1),(.pos 40)]),
   ((.exchange 20 46 6),[(.neg 46),(.neg 20),(.pos 10),(.pos 40)]),
   ((.exchange 20 57 4),[(.neg 57),(.neg 20),(.pos 15),(.pos 56)]),
   ((.exchange 20 58 4),[(.neg 58),(.neg 20),(.pos 17),(.pos 56)]),
   ((.exchange 20 59 4),[(.neg 59),(.neg 20),(.pos 15),(.pos 17),(.pos 56)]),
   ((.exchange 20 60 4),[(.neg 60),(.neg 20),(.pos 17),(.pos 56)]),
   ((.exchange 20 66 2),[(.neg 66),(.neg 20),(.pos 19),(.pos 31),(.pos 61)]),
   ((.exchange 20 69 2),[(.neg 69),(.neg 20),(.pos 31),(.pos 61)]),
   ((.exchange 21 40 6),[(.neg 40),(.neg 21),(.pos 1),(.pos 41)]),
   ((.exchange 21 42 6),[(.neg 42),(.neg 21),(.pos 1),(.pos 4),(.pos 41)]),
   ((.exchange 21 43 6),[(.neg 43),(.neg 21),(.pos 4),(.pos 41)]),
   ((.exchange 21 44 6),[(.neg 44),(.neg 21),(.pos 4),(.pos 41)]),
   ((.exchange 21 46 6),[(.neg 46),(.neg 21),(.pos 1),(.pos 11),(.pos 41)]),
   ((.exchange 21 47 6),[(.neg 47),(.neg 21),(.pos 11),(.pos 41)]),
   ((.exchange 21 48 6),[(.neg 48),(.neg 21),(.pos 1),(.pos 4),(.pos 11),(.pos 41)]),
   ((.exchange 21 49 6),[(.neg 49),(.neg 21),(.pos 4),(.pos 11),(.pos 41)]),
   ((.exchange 21 50 6),[(.neg 50),(.neg 21),(.pos 4),(.pos 11),(.pos 41)]),
   ((.exchange 21 53 6),[(.neg 53),(.neg 21),(.pos 11),(.pos 41)]),
   ((.exchange 21 54 6),[(.neg 54),(.neg 21),(.pos 4),(.pos 11),(.pos 41)]),
   ((.exchange 21 56 4),[(.neg 56),(.neg 21),(.pos 15),(.pos 57)]),
   ((.exchange 21 66 2),[(.neg 66),(.neg 21),(.pos 32),(.pos 62)]),
   ((.exchange 21 69 2),[(.neg 69),(.neg 21),(.pos 32),(.pos 62)]),
   ((.exchange 22 41 6),[(.neg 41),(.neg 22),(.pos 2),(.pos 3),(.pos 42)]),
   ((.exchange 22 46 6),[(.neg 46),(.neg 22),(.pos 3),(.pos 12),(.pos 42)]),
   ((.exchange 22 56 4),[(.neg 56),(.neg 22),(.pos 17),(.pos 58)]),
   ((.exchange 23 41 6),[(.neg 41),(.neg 23),(.pos 4),(.pos 43)]),
   ((.exchange 23 46 6),[(.neg 46),(.neg 23),(.pos 2),(.pos 4),(.pos 13),(.pos 43)]),
   ((.exchange 23 56 4),[(.neg 56),(.neg 23),(.pos 16),(.pos 18),(.pos 59)]),
   ((.exchange 24 41 6),[(.neg 41),(.neg 24),(.pos 4),(.pos 44)]),
   ((.exchange 24 46 6),[(.neg 46),(.neg 24),(.pos 3),(.pos 14),(.pos 44)]),
   ((.exchange 24 56 4),[(.neg 56),(.neg 24),(.pos 17),(.pos 60)]),
   ((.exchange 26 40 6),[(.neg 40),(.neg 26),(.pos 10),(.pos 46)]),
   ((.exchange 26 41 6),[(.neg 41),(.neg 26),(.pos 5),(.pos 10),(.pos 46)]),
   ((.exchange 26 42 6),[(.neg 42),(.neg 26),(.pos 7),(.pos 10),(.pos 46)]),
   ((.exchange 26 43 6),[(.neg 43),(.neg 26),(.pos 5),(.pos 7),(.pos 10),(.pos 46)]),
   ((.exchange 26 44 6),[(.neg 44),(.neg 26),(.pos 7),(.pos 10),(.pos 46)]),
   ((.exchange 26 47 6),[(.neg 47),(.neg 26),(.pos 5),(.pos 46)]),
   ((.exchange 26 48 6),[(.neg 48),(.neg 26),(.pos 7),(.pos 46)]),
   ((.exchange 26 49 6),[(.neg 49),(.neg 26),(.pos 5),(.pos 7),(.pos 46)]),
   ((.exchange 26 50 6),[(.neg 50),(.neg 26),(.pos 7),(.pos 46)]),
   ((.exchange 26 53 6),[(.neg 53),(.neg 26),(.pos 10),(.pos 46)]),
   ((.exchange 26 54 6),[(.neg 54),(.neg 26),(.pos 7),(.pos 10),(.pos 46)]),
   ((.exchange 26 66 2),[(.neg 66),(.neg 26),(.pos 25),(.pos 65)]),
   ((.exchange 26 69 2),[(.neg 69),(.neg 26),(.pos 31),(.pos 65)]),
   ((.exchange 27 41 6),[(.neg 41),(.neg 27),(.pos 11),(.pos 47)]),
   ((.exchange 27 46 6),[(.neg 46),(.neg 27),(.pos 5),(.pos 47)]),
   ((.exchange 27 61 2),[(.neg 61),(.neg 27),(.pos 25),(.pos 32),(.pos 66)]),
   ((.exchange 27 62 2),[(.neg 62),(.neg 27),(.pos 32),(.pos 66)]),
   ((.exchange 27 65 2),[(.neg 65),(.neg 27),(.pos 25),(.pos 66)]),
   ((.exchange 27 69 2),[(.neg 69),(.neg 27),(.pos 32),(.pos 66)]),
   ((.exchange 28 41 6),[(.neg 41),(.neg 28),(.pos 6),(.pos 7),(.pos 12),(.pos 48)]),
   ((.exchange 28 46 6),[(.neg 46),(.neg 28),(.pos 7),(.pos 48)]),
   ((.exchange 29 41 6),[(.neg 41),(.neg 29),(.pos 8),(.pos 13),(.pos 49)]),
   ((.exchange 29 46 6),[(.neg 46),(.neg 29),(.pos 6),(.pos 8),(.pos 49)]),
   ((.exchange 30 41 6),[(.neg 41),(.neg 30),(.pos 8),(.pos 14),(.pos 50)]),
   ((.exchange 30 46 6),[(.neg 46),(.neg 30),(.pos 7),(.pos 50)]),
   ((.exchange 33 41 6),[(.neg 41),(.neg 33),(.pos 11),(.pos 53)]),
   ((.exchange 33 46 6),[(.neg 46),(.neg 33),(.pos 10),(.pos 53)]),
   ((.exchange 33 61 2),[(.neg 61),(.neg 33),(.pos 31),(.pos 69)]),
   ((.exchange 33 62 2),[(.neg 62),(.neg 33),(.pos 32),(.pos 69)]),
   ((.exchange 33 65 2),[(.neg 65),(.neg 33),(.pos 31),(.pos 69)]),
   ((.exchange 33 66 2),[(.neg 66),(.neg 33),(.pos 32),(.pos 69)]),
   ((.exchange 34 41 6),[(.neg 41),(.neg 34),(.pos 13),(.pos 14),(.pos 54)]),
   ((.exchange 34 46 6),[(.neg 46),(.neg 34),(.pos 12),(.pos 14),(.pos 54)]),
   ((.exchange 35 20 7),[(.neg 35),(.neg 20),(.pos 1),(.pos 15)]),
   ((.exchange 36 20 7),[(.neg 36),(.neg 20),(.pos 0),(.pos 2),(.pos 16)]),
   ((.exchange 37 20 7),[(.neg 37),(.neg 20),(.pos 3),(.pos 17)]),
   ((.exchange 38 20 7),[(.neg 38),(.neg 20),(.pos 0),(.pos 4),(.pos 18)]),
   ((.exchange 39 20 7),[(.neg 39),(.neg 20),(.pos 1),(.pos 19)]),
   ((.exchange 45 20 7),[(.neg 45),(.neg 20),(.pos 5),(.pos 9),(.pos 25)]),
   ((.exchange 51 20 7),[(.neg 51),(.neg 20),(.pos 10),(.pos 31)]),
   ((.exchange 52 20 7),[(.neg 52),(.neg 20),(.pos 9),(.pos 11),(.pos 32)]),
   ((.exchange 55 20 7),[(.neg 55),(.neg 20),(.pos 15),(.pos 19)]),
   ((.exchange 56 33 0),[(.neg 56),(.neg 33),(.pos 63),(.pos 67)]),
   ((.exchange 58 34 0),[(.neg 58),(.neg 34),(.pos 64),(.pos 68)]),
   ((.exchange 58 54 0),[(.neg 58),(.neg 54),(.pos 64),(.pos 68)]),
   ((.exchange 60 34 2),[(.neg 60),(.neg 34),(.pos 64),(.pos 68)]),
   ((.exchange 63 28 2),[(.neg 63),(.neg 28),(.pos 61),(.pos 64),(.pos 69)]),
   ((.exchange 63 30 4),[(.neg 63),(.neg 30),(.pos 60),(.pos 67)]),
   ((.exchange 63 34 2),[(.neg 63),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 64 20 3),[(.neg 64),(.neg 20),(.pos 61),(.pos 63)]),
   ((.exchange 64 28 4),[(.neg 64),(.neg 28),(.pos 58),(.pos 68)]),
   ((.exchange 64 33 3),[(.neg 64),(.neg 33),(.pos 63),(.pos 69)]),
   ((.exchange 64 67 3),[(.neg 67),(.neg 64),(.pos 63),(.pos 69)]),
   ((.exchange 66 60 1),[(.neg 66),(.neg 60),(.pos 67),(.pos 68)]),
   ((.exchange 67 20 5),[(.neg 67),(.neg 20),(.pos 56),(.pos 63)]),
   ((.exchange 67 34 2),[(.neg 67),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 67 59 2),[(.neg 67),(.neg 59),(.pos 66),(.pos 68)]),
   ((.exchange 68 20 5),[(.neg 68),(.neg 20),(.pos 58),(.pos 60),(.pos 64)]),
   ((.exchange 68 33 3),[(.neg 68),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 68 41 3),[(.neg 68),(.neg 41),(.pos 66),(.pos 67),(.pos 69)]),
   ((.exchange 69 24 5),[(.neg 69),(.neg 24),(.pos 63),(.pos 64)]),
   ((.exchange 69 30 4),[(.neg 69),(.neg 30),(.pos 67),(.pos 68)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_1 : List (Origin 70 29 × List Sat.Literal) :=
  [((.exchange 69 44 5),[(.neg 69),(.neg 44),(.pos 63),(.pos 64)]),
   ((.exchange 69 50 4),[(.neg 69),(.neg 50),(.pos 67),(.pos 68)]),
   ((.exchange 69 60 5),[(.neg 69),(.neg 60),(.pos 63),(.pos 64)]),
   (.newPoint,[(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 0),[(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 65),(.pos 66),(.pos 69)]),
   ((.excluded 1),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 2),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 68)]),
   ((.excluded 3),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60)]),
   ((.excluded 4),[(.neg 68),(.neg 67),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 69)]),
   ((.excluded 5),[(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 61),(.pos 62),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 6),[(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 61),(.pos 62),(.pos 65),(.pos 66),(.pos 69)]),
   ((.excluded 7),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 63),(.pos 68)]),
   ((.excluded 8),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 63)]),
   ((.excluded 9),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 68)]),
   ((.excluded 10),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 64),(.pos 67)]),
   ((.excluded 11),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 64)]),
   ((.excluded 12),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 67)]),
   ((.excluded 13),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55)]),
   ((.excluded 14),[(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 15),[(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 65),(.pos 66),(.pos 69)]),
   ((.excluded 16),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 17),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 68)]),
   ((.excluded 18),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60)]),
   ((.excluded 19),[(.neg 68),(.neg 67),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 69)]),
   ((.excluded 20),[(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 61),(.pos 62),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 21),[(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 61),(.pos 62),(.pos 65),(.pos 66),(.pos 69)]),
   ((.excluded 22),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 63),(.pos 68)]),
   ((.excluded 23),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 63)]),
   ((.excluded 24),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 68)]),
   ((.excluded 25),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 64),(.pos 67)]),
   ((.excluded 26),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 64)]),
   ((.excluded 27),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 67)]),
   ((.excluded 28),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 55)])]

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
        Papers.RationalityTen.MatroidChecked.FastSemanticChecks.RawWitness 8 (N7R4.familyMasks.get 11)
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


end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C11

/- Source: MatroidCatalogue/Cases/N8R4C11Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C11

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
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C11.formula []
    exact Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C11.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 8 4 (target w),family_mem 8 4 (target w) hw.1,?_⟩
    exact validWitness_sound 8 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C11


end
end
end BundlePart6

section BundlePart7
/- Source: MatroidChecked/SemanticChunks/Cases02Part07.lean -/




@[expose] public section
noncomputable section

/- Source: MatroidCatalogue/Cases/N8R4C12Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C12

abbrev U := N8R4.grid
noncomputable def old : Finset (Finset (Fin 8)) := N7R4.family 12
noncomputable def newIndexTree : Table ℕ := (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf 35) (.leaf 36)) (.node 3 (.leaf 37) (.leaf 38))) (.node 6 (.node 5 (.leaf 39) (.leaf 40)) (.node 7 (.leaf 41) (.leaf 42)))) (.node 12 (.node 10 (.node 9 (.leaf 43) (.leaf 44)) (.node 11 (.leaf 45) (.leaf 46))) (.node 14 (.node 13 (.leaf 47) (.leaf 48)) (.node 15 (.leaf 49) (.node 16 (.leaf 50) (.leaf 51)))))) (.node 26 (.node 21 (.node 19 (.node 18 (.leaf 52) (.leaf 53)) (.node 20 (.leaf 54) (.leaf 55))) (.node 23 (.node 22 (.leaf 56) (.leaf 57)) (.node 24 (.leaf 58) (.node 25 (.leaf 59) (.leaf 60))))) (.node 30 (.node 28 (.node 27 (.leaf 61) (.leaf 62)) (.node 29 (.leaf 63) (.leaf 64))) (.node 32 (.node 31 (.leaf 65) (.leaf 66)) (.node 33 (.leaf 67) (.node 34 (.leaf 68) (.leaf 69)))))))
noncomputable def newIndex (i : Fin 35) : Fin 70 := Fin.ofNat 70 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 14 (.node 7 (.node 3 (.node 1 (.leaf (12549357568,20,4151322)) (.node 2 (.leaf (30870077440,17,6248648)) (.leaf (25165824000,21,8344840)))) (.node 5 (.node 4 (.leaf (34292629504,25,10442376)) (.leaf (11876171776,34,8301832))) (.node 6 (.leaf (803209216,34,8215816)) (.leaf (12614369280,41,12467336))))) (.node 10 (.node 8 (.leaf (25566380032,38,12535432)) (.node 9 (.leaf (34156314624,39,12531848)) (.leaf (25767706624,42,12478088)))) (.node 12 (.node 11 (.leaf (30599544832,38,12478088)) (.leaf (31136415744,39,12445832))) (.node 13 (.leaf (33820770304,42,12535432)) (.leaf (34357641216,43,14599816)))))) (.node 21 (.node 17 (.node 15 (.leaf (785376,104,9431688)) (.node 16 (.leaf (12550142944,123,16434824)) (.leaf (30870862816,118,11789960)))) (.node 19 (.node 18 (.leaf (25166609376,124,11789960)) (.leaf (34293414880,125,16434824))) (.node 20 (.leaf (11876957152,126,16431240)) (.leaf (803994592,126,16373896))))) (.node 25 (.node 23 (.node 22 (.leaf (12615154656,127,16434824)) (.leaf (25567165408,128,16434824))) (.node 24 (.leaf (34157100000,129,16434824)) (.leaf (25768492000,130,16406152)))) (.node 27 (.node 26 (.leaf (30600330208,128,16406152)) (.leaf (31137201120,129,16406152))) (.node 28 (.leaf (33821555680,130,16434824)) (.leaf (34358426592,131,16434824)))))))

noncomputable def models (i : Fin 29) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 29) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 29) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 70, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (7 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 70, (7 : Fin 8) ∈ U i → ∃ j : Fin 35, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C12

/- Source: MatroidCatalogue/Cases/N8R4C12Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C12


noncomputable def certificates_0 : List (Origin 70 29 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.neg 2)]),
   ((.fixed 3),[(.neg 3)]),
   ((.fixed 4),[(.neg 4)]),
   ((.fixed 5),[(.neg 5)]),
   ((.fixed 6),[(.neg 6)]),
   ((.fixed 7),[(.neg 7)]),
   ((.fixed 8),[(.neg 8)]),
   ((.fixed 9),[(.neg 9)]),
   ((.fixed 10),[(.neg 10)]),
   ((.fixed 11),[(.neg 11)]),
   ((.fixed 12),[(.neg 12)]),
   ((.fixed 13),[(.neg 13)]),
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
   ((.fixed 24),[(.pos 24)]),
   ((.fixed 25),[(.neg 25)]),
   ((.fixed 26),[(.pos 26)]),
   ((.fixed 27),[(.pos 27)]),
   ((.fixed 28),[(.pos 28)]),
   ((.fixed 29),[(.pos 29)]),
   ((.fixed 30),[(.pos 30)]),
   ((.fixed 31),[(.pos 31)]),
   ((.fixed 32),[(.pos 32)]),
   ((.fixed 33),[(.neg 33)]),
   ((.fixed 34),[(.pos 34)]),
   ((.exchange 20 41 6),[(.neg 41),(.neg 20),(.pos 1),(.pos 40)]),
   ((.exchange 20 46 6),[(.neg 46),(.neg 20),(.pos 10),(.pos 40)]),
   ((.exchange 20 57 4),[(.neg 57),(.neg 20),(.pos 15),(.pos 56)]),
   ((.exchange 20 58 4),[(.neg 58),(.neg 20),(.pos 17),(.pos 56)]),
   ((.exchange 20 59 4),[(.neg 59),(.neg 20),(.pos 15),(.pos 17),(.pos 56)]),
   ((.exchange 20 60 4),[(.neg 60),(.neg 20),(.pos 17),(.pos 56)]),
   ((.exchange 20 62 2),[(.neg 62),(.neg 20),(.pos 19),(.pos 61)]),
   ((.exchange 20 67 0),[(.neg 67),(.neg 20),(.pos 33),(.pos 63)]),
   ((.exchange 20 69 0),[(.neg 69),(.neg 20),(.pos 33),(.pos 63)]),
   ((.exchange 21 40 6),[(.neg 40),(.neg 21),(.pos 1),(.pos 41)]),
   ((.exchange 21 42 6),[(.neg 42),(.neg 21),(.pos 1),(.pos 4),(.pos 41)]),
   ((.exchange 21 43 6),[(.neg 43),(.neg 21),(.pos 4),(.pos 41)]),
   ((.exchange 21 44 6),[(.neg 44),(.neg 21),(.pos 4),(.pos 41)]),
   ((.exchange 21 46 6),[(.neg 46),(.neg 21),(.pos 1),(.pos 11),(.pos 41)]),
   ((.exchange 21 47 6),[(.neg 47),(.neg 21),(.pos 11),(.pos 41)]),
   ((.exchange 21 48 6),[(.neg 48),(.neg 21),(.pos 1),(.pos 4),(.pos 11),(.pos 41)]),
   ((.exchange 21 49 6),[(.neg 49),(.neg 21),(.pos 4),(.pos 11),(.pos 41)]),
   ((.exchange 21 50 6),[(.neg 50),(.neg 21),(.pos 4),(.pos 11),(.pos 41)]),
   ((.exchange 21 51 6),[(.neg 51),(.neg 21),(.pos 1),(.pos 11),(.pos 41)]),
   ((.exchange 21 52 6),[(.neg 52),(.neg 21),(.pos 11),(.pos 41)]),
   ((.exchange 21 54 6),[(.neg 54),(.neg 21),(.pos 4),(.pos 11),(.pos 41)]),
   ((.exchange 21 56 4),[(.neg 56),(.neg 21),(.pos 15),(.pos 57)]),
   ((.exchange 21 61 2),[(.neg 61),(.neg 21),(.pos 19),(.pos 62)]),
   ((.exchange 22 41 6),[(.neg 41),(.neg 22),(.pos 2),(.pos 3),(.pos 42)]),
   ((.exchange 22 46 6),[(.neg 46),(.neg 22),(.pos 3),(.pos 12),(.pos 42)]),
   ((.exchange 22 56 4),[(.neg 56),(.neg 22),(.pos 17),(.pos 58)]),
   ((.exchange 23 41 6),[(.neg 41),(.neg 23),(.pos 4),(.pos 43)]),
   ((.exchange 23 46 6),[(.neg 46),(.neg 23),(.pos 2),(.pos 4),(.pos 13),(.pos 43)]),
   ((.exchange 23 56 4),[(.neg 56),(.neg 23),(.pos 16),(.pos 18),(.pos 59)]),
   ((.exchange 24 41 6),[(.neg 41),(.neg 24),(.pos 4),(.pos 44)]),
   ((.exchange 24 46 6),[(.neg 46),(.neg 24),(.pos 3),(.pos 14),(.pos 44)]),
   ((.exchange 24 56 4),[(.neg 56),(.neg 24),(.pos 17),(.pos 60)]),
   ((.exchange 26 40 6),[(.neg 40),(.neg 26),(.pos 10),(.pos 46)]),
   ((.exchange 26 41 6),[(.neg 41),(.neg 26),(.pos 5),(.pos 10),(.pos 46)]),
   ((.exchange 26 42 6),[(.neg 42),(.neg 26),(.pos 7),(.pos 10),(.pos 46)]),
   ((.exchange 26 43 6),[(.neg 43),(.neg 26),(.pos 5),(.pos 7),(.pos 10),(.pos 46)]),
   ((.exchange 26 44 6),[(.neg 44),(.neg 26),(.pos 7),(.pos 10),(.pos 46)]),
   ((.exchange 26 47 6),[(.neg 47),(.neg 26),(.pos 5),(.pos 46)]),
   ((.exchange 26 48 6),[(.neg 48),(.neg 26),(.pos 7),(.pos 46)]),
   ((.exchange 26 49 6),[(.neg 49),(.neg 26),(.pos 5),(.pos 7),(.pos 46)]),
   ((.exchange 26 50 6),[(.neg 50),(.neg 26),(.pos 7),(.pos 46)]),
   ((.exchange 26 51 6),[(.neg 51),(.neg 26),(.pos 10),(.pos 46)]),
   ((.exchange 26 52 6),[(.neg 52),(.neg 26),(.pos 5),(.pos 10),(.pos 46)]),
   ((.exchange 26 54 6),[(.neg 54),(.neg 26),(.pos 7),(.pos 10),(.pos 46)]),
   ((.exchange 26 63 0),[(.neg 63),(.neg 26),(.pos 33),(.pos 67)]),
   ((.exchange 26 66 2),[(.neg 66),(.neg 26),(.pos 25),(.pos 65)]),
   ((.exchange 26 69 0),[(.neg 69),(.neg 26),(.pos 33),(.pos 67)]),
   ((.exchange 27 41 6),[(.neg 41),(.neg 27),(.pos 11),(.pos 47)]),
   ((.exchange 27 46 6),[(.neg 46),(.neg 27),(.pos 5),(.pos 47)]),
   ((.exchange 27 65 2),[(.neg 65),(.neg 27),(.pos 25),(.pos 66)]),
   ((.exchange 28 41 6),[(.neg 41),(.neg 28),(.pos 6),(.pos 7),(.pos 12),(.pos 48)]),
   ((.exchange 28 46 6),[(.neg 46),(.neg 28),(.pos 7),(.pos 48)]),
   ((.exchange 29 41 6),[(.neg 41),(.neg 29),(.pos 8),(.pos 13),(.pos 49)]),
   ((.exchange 29 46 6),[(.neg 46),(.neg 29),(.pos 6),(.pos 8),(.pos 49)]),
   ((.exchange 30 41 6),[(.neg 41),(.neg 30),(.pos 8),(.pos 14),(.pos 50)]),
   ((.exchange 30 46 6),[(.neg 46),(.neg 30),(.pos 7),(.pos 50)]),
   ((.exchange 31 41 6),[(.neg 41),(.neg 31),(.pos 9),(.pos 10),(.pos 51)]),
   ((.exchange 31 46 6),[(.neg 46),(.neg 31),(.pos 10),(.pos 51)]),
   ((.exchange 31 63 0),[(.neg 63),(.neg 31),(.pos 33),(.pos 69)]),
   ((.exchange 31 67 0),[(.neg 67),(.neg 31),(.pos 33),(.pos 69)]),
   ((.exchange 32 41 6),[(.neg 41),(.neg 32),(.pos 11),(.pos 52)]),
   ((.exchange 32 46 6),[(.neg 46),(.neg 32),(.pos 9),(.pos 11),(.pos 52)]),
   ((.exchange 34 41 6),[(.neg 41),(.neg 34),(.pos 13),(.pos 14),(.pos 54)]),
   ((.exchange 34 46 6),[(.neg 46),(.neg 34),(.pos 12),(.pos 14),(.pos 54)]),
   ((.exchange 35 20 7),[(.neg 35),(.neg 20),(.pos 1),(.pos 15)]),
   ((.exchange 36 20 7),[(.neg 36),(.neg 20),(.pos 0),(.pos 2),(.pos 16)]),
   ((.exchange 37 20 7),[(.neg 37),(.neg 20),(.pos 3),(.pos 17)]),
   ((.exchange 38 20 7),[(.neg 38),(.neg 20),(.pos 0),(.pos 4),(.pos 18)]),
   ((.exchange 39 20 7),[(.neg 39),(.neg 20),(.pos 1),(.pos 19)]),
   ((.exchange 45 20 7),[(.neg 45),(.neg 20),(.pos 5),(.pos 9),(.pos 25)]),
   ((.exchange 53 20 7),[(.neg 53),(.neg 20),(.pos 10),(.pos 33)]),
   ((.exchange 55 20 7),[(.neg 55),(.neg 20),(.pos 15),(.pos 19)]),
   ((.exchange 56 31 2),[(.neg 56),(.neg 31),(.pos 61),(.pos 65)]),
   ((.exchange 57 31 2),[(.neg 57),(.neg 31),(.pos 55),(.pos 62),(.pos 66)]),
   ((.exchange 58 31 3),[(.neg 58),(.neg 31),(.pos 61),(.pos 65)]),
   ((.exchange 58 34 0),[(.neg 58),(.neg 34),(.pos 64),(.pos 68)]),
   ((.exchange 59 31 3),[(.neg 59),(.neg 31),(.pos 55),(.pos 62),(.pos 66)]),
   ((.exchange 60 34 2),[(.neg 60),(.neg 34),(.pos 64),(.pos 68)]),
   ((.exchange 61 24 0),[(.neg 61),(.neg 24),(.pos 63),(.pos 64)]),
   ((.exchange 61 26 4),[(.neg 61),(.neg 26),(.pos 56),(.pos 65)]),
   ((.exchange 61 34 0),[(.neg 61),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 61 50 4),[(.neg 61),(.neg 50),(.pos 56),(.pos 58),(.pos 65)]),
   ((.exchange 61 60 0),[(.neg 61),(.neg 60),(.pos 63),(.pos 64)]),
   ((.exchange 62 24 1),[(.neg 62),(.neg 24),(.pos 63),(.pos 64)]),
   ((.exchange 62 26 4),[(.neg 62),(.neg 26),(.pos 55),(.pos 57),(.pos 66)]),
   ((.exchange 62 50 4),[(.neg 62),(.neg 50),(.pos 57),(.pos 59),(.pos 66)]),
   ((.exchange 62 54 1),[(.neg 62),(.neg 54),(.pos 64),(.pos 69)]),
   ((.exchange 63 23 2),[(.neg 63),(.neg 23),(.pos 62),(.pos 64)]),
   ((.exchange 63 59 2),[(.neg 63),(.neg 59),(.pos 62),(.pos 64)]),
   ((.exchange 64 20 3),[(.neg 64),(.neg 20),(.pos 61),(.pos 63)]),
   ((.exchange 64 21 3),[(.neg 64),(.neg 21),(.pos 62),(.pos 63)]),
   ((.exchange 64 26 4),[(.neg 64),(.neg 26),(.pos 58),(.pos 60),(.pos 68)]),
   ((.exchange 64 28 4),[(.neg 64),(.neg 28),(.pos 58),(.pos 68)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_1 : List (Origin 70 29 × List Sat.Literal) :=
  [((.exchange 64 66 3),[(.neg 66),(.neg 64),(.pos 62),(.pos 69)]),
   ((.exchange 65 20 5),[(.neg 65),(.neg 20),(.pos 56),(.pos 61)]),
   ((.exchange 65 30 0),[(.neg 65),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 65 34 0),[(.neg 65),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 65 63 5),[(.neg 65),(.neg 63),(.pos 56),(.pos 61)]),
   ((.exchange 66 20 5),[(.neg 66),(.neg 20),(.pos 55),(.pos 57),(.pos 62)]),
   ((.exchange 66 34 1),[(.neg 66),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 66 44 1),[(.neg 66),(.neg 44),(.pos 67),(.pos 68),(.pos 69)]),
   ((.exchange 66 64 5),[(.neg 66),(.neg 64),(.pos 59),(.pos 62)]),
   ((.exchange 67 28 2),[(.neg 67),(.neg 28),(.pos 65),(.pos 68)]),
   ((.exchange 67 58 2),[(.neg 67),(.neg 58),(.pos 65),(.pos 68)]),
   ((.exchange 67 59 2),[(.neg 67),(.neg 59),(.pos 66),(.pos 68)]),
   ((.exchange 68 20 3),[(.neg 68),(.neg 20),(.pos 65),(.pos 67),(.pos 69)]),
   ((.exchange 68 20 5),[(.neg 68),(.neg 20),(.pos 58),(.pos 60),(.pos 64)]),
   ((.exchange 68 21 3),[(.neg 68),(.neg 21),(.pos 66),(.pos 67),(.pos 69)]),
   ((.exchange 68 26 3),[(.neg 68),(.neg 26),(.pos 65),(.pos 67)]),
   ((.exchange 68 31 3),[(.neg 68),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 68 44 5),[(.neg 68),(.neg 44),(.pos 60),(.pos 64)]),
   ((.exchange 68 62 3),[(.neg 68),(.neg 62),(.pos 66),(.pos 69)]),
   ((.exchange 68 63 5),[(.neg 68),(.neg 63),(.pos 60),(.pos 64)]),
   ((.exchange 69 28 4),[(.neg 69),(.neg 28),(.pos 65),(.pos 68)]),
   ((.exchange 69 29 4),[(.neg 69),(.neg 29),(.pos 66),(.pos 68)]),
   ((.exchange 69 59 4),[(.neg 69),(.neg 59),(.pos 66),(.pos 68)]),
   (.newPoint,[(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 0),[(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 63),(.pos 67),(.pos 69)]),
   ((.excluded 1),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 65),(.pos 66)]),
   ((.excluded 2),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 68)]),
   ((.excluded 3),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60)]),
   ((.excluded 4),[(.neg 68),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 67),(.pos 69)]),
   ((.excluded 5),[(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 63),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 6),[(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 63),(.pos 67),(.pos 69)]),
   ((.excluded 7),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 61),(.pos 62),(.pos 68)]),
   ((.excluded 8),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 9),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 68)]),
   ((.excluded 10),[(.neg 69),(.neg 68),(.neg 67),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 64),(.pos 65),(.pos 66)]),
   ((.excluded 11),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 65),(.pos 66)]),
   ((.excluded 12),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 64)]),
   ((.excluded 13),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55)]),
   ((.excluded 14),[(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 15),[(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 63),(.pos 67),(.pos 69)]),
   ((.excluded 16),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 65),(.pos 66)]),
   ((.excluded 17),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 68)]),
   ((.excluded 18),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60)]),
   ((.excluded 19),[(.neg 68),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 53),(.pos 55),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 67),(.pos 69)]),
   ((.excluded 20),[(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 53),(.pos 55),(.pos 63),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 21),[(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 53),(.pos 55),(.pos 63),(.pos 67),(.pos 69)]),
   ((.excluded 22),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 53),(.pos 55),(.pos 61),(.pos 62),(.pos 68)]),
   ((.excluded 23),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 53),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 24),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 53),(.pos 55),(.pos 68)]),
   ((.excluded 25),[(.neg 69),(.neg 68),(.neg 67),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 53),(.pos 55),(.pos 64),(.pos 65),(.pos 66)]),
   ((.excluded 26),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 53),(.pos 55),(.pos 65),(.pos 66)]),
   ((.excluded 27),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 53),(.pos 55),(.pos 64)]),
   ((.excluded 28),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 53),(.pos 55)])]

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
        Papers.RationalityTen.MatroidChecked.FastSemanticChecks.RawWitness 8 (N7R4.familyMasks.get 12)
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


end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C12

/- Source: MatroidCatalogue/Cases/N8R4C12Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C12

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
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C12.formula []
    exact Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C12.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 8 4 (target w),family_mem 8 4 (target w) hw.1,?_⟩
    exact validWitness_sound 8 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C12

end
end
end BundlePart7
