module
public import Consolidated.SemanticData
public import Mathlib.Data.Fin.Tuple.Basic
public import MatroidCatalogue.Definitions
public import MatroidChecked.BitsetSemanticChecks
public import MatroidChecked.FastSemanticChecks
public import MatroidChecked.BitsetOrigins
public import MatroidChecked.MaskOrigins

section BundlePart2
/- Source: MatroidChecked/SemanticChunks/Cases18Part01.lean -/




@[expose] public section
noncomputable section

/- Source: MatroidCatalogue/Cases/N8R4C72Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C72

abbrev U := N8R4.grid
noncomputable def old : Finset (Finset (Fin 8)) := N7R4.family 72
noncomputable def newIndexTree : Table ℕ := (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf 35) (.leaf 36)) (.node 3 (.leaf 37) (.leaf 38))) (.node 6 (.node 5 (.leaf 39) (.leaf 40)) (.node 7 (.leaf 41) (.leaf 42)))) (.node 12 (.node 10 (.node 9 (.leaf 43) (.leaf 44)) (.node 11 (.leaf 45) (.leaf 46))) (.node 14 (.node 13 (.leaf 47) (.leaf 48)) (.node 15 (.leaf 49) (.node 16 (.leaf 50) (.leaf 51)))))) (.node 26 (.node 21 (.node 19 (.node 18 (.leaf 52) (.leaf 53)) (.node 20 (.leaf 54) (.leaf 55))) (.node 23 (.node 22 (.leaf 56) (.leaf 57)) (.node 24 (.leaf 58) (.node 25 (.leaf 59) (.leaf 60))))) (.node 30 (.node 28 (.node 27 (.leaf 61) (.leaf 62)) (.node 29 (.leaf 63) (.leaf 64))) (.node 32 (.node 31 (.leaf 65) (.leaf 66)) (.node 33 (.leaf 67) (.node 34 (.leaf 68) (.leaf 69)))))))
noncomputable def newIndex (i : Fin 35) : Fin 70 := Fin.ofNat 70 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 88 (.node 44 (.node 22 (.node 11 (.node 5 (.node 2 (.node 1 (.leaf (23197428384,284,3570882)) (.leaf (28375307072,284,3656912))) (.node 3 (.leaf (17144248800,313,1988273)) (.node 4 (.leaf (34358492128,370,6184136)) (.leaf (28547704208,284,4086810))))) (.node 8 (.node 6 (.leaf (22958775408,284,4112794)) (.node 7 (.leaf (34325364208,370,6181427)) (.leaf (1054848720,313,1472401)))) (.node 9 (.leaf (28988930000,370,5667928)) (.node 10 (.leaf (23605526256,370,5665667)) (.leaf (16160640816,313,1559761)))))) (.node 16 (.node 13 (.node 12 (.leaf (33952886704,370,5753923)) (.leaf (33747361648,370,5751704))) (.node 14 (.leaf (17179869168,467,10413704)) (.node 15 (.leaf (34359738352,488,10413704)) (.leaf (16159635471,284,4131162))))) (.node 19 (.node 17 (.leaf (1053819375,284,3959578)) (.node 18 (.leaf (17178851823,370,6064499)) (.leaf (22959401807,313,1436113)))) (.node 20 (.leaf (33747172175,370,5708248)) (.node 21 (.leaf (23605324783,370,5564867)) (.leaf (28548321967,313,1523473))))))) (.node 33 (.node 27 (.node 24 (.node 23 (.leaf (33952692911,370,5709571)) (.leaf (28988724207,370,5566232))) (.node 25 (.leaf (34325986287,467,10333064)) (.node 26 (.leaf (34359540719,488,10333064)) (.leaf (1029951,284,2324714))))) (.node 30 (.node 28 (.leaf (16160653119,370,4689251)) (.node 29 (.leaf (28548528063,370,4677155)) (.leaf (23196802463,313,1751183)))) (.node 31 (.leaf (33952071071,370,5937183)) (.node 32 (.leaf (23197630399,370,4647111)) (.leaf (33952882623,467,9415749)))))) (.node 38 (.node 35 (.node 34 (.leaf (33952890815,488,9415749)) (.leaf (23604698623,370,5820703))) (.node 36 (.leaf (22959603583,370,4645347)) (.node 37 (.leaf (1054849023,370,4488099)) (.leaf (23605526495,467,9270149))))) (.node 41 (.node 39 (.leaf (23605526527,488,9270149)) (.node 40 (.leaf (28374688895,313,1693881)) (.leaf (33746549887,370,5935419)))) (.node 42 (.leaf (28375512959,370,4675832)) (.node 43 (.leaf (33747365759,467,9413544)) (.leaf (33747369855,488,9413544)))))))) (.node 66 (.node 55 (.node 49 (.node 46 (.node 45 (.leaf (28988106239,370,5822523)) (.leaf (28988929791,467,9272424))) (.node 47 (.leaf (28988930047,488,9272424)) (.node 48 (.leaf (34357870079,467,10330670)) (.leaf (34358918655,488,10330670))))) (.node 52 (.node 50 (.leaf (17145253599,606,16434824)) (.node 51 (.leaf (34325122783,607,16434824)) (.leaf (17178808031,607,16362248)))) (.node 53 (.leaf (34358677215,608,16434824)) (.node 54 (.leaf (17146302175,607,16359980)) (.leaf (34326171359,608,16433690)))))) (.node 60 (.node 57 (.node 56 (.leaf (17179856607,608,16288538)) (.leaf (34359725791,609,16434824))) (.node 58 (.leaf (17145261791,607,13609540)) (.node 59 (.leaf (34325130975,608,14140994)) (.leaf (17178816223,608,13999874))))) (.node 63 (.node 61 (.leaf (34358685407,610,16431233)) (.node 62 (.leaf (17146310367,608,13539351)) (.leaf (34326179551,610,16200716)))) (.node 64 (.leaf (17179864799,610,15830157)) (.node 65 (.leaf (34359733983,611,16427075)) (.leaf (17145257695,607,13607776))))))) (.node 77 (.node 71 (.node 68 (.node 67 (.leaf (34325126879,608,14140112)) (.leaf (17178812127,608,13998544))) (.node 69 (.leaf (34358681311,610,16430344)) (.node 70 (.leaf (17146306271,608,13537594)) (.leaf (34326175455,610,16199841))))) (.node 74 (.node 72 (.leaf (17179860703,610,15828393)) (.node 73 (.leaf (34359729887,611,16425752)) (.leaf (17145265887,608,13076322)))) (.node 75 (.leaf (34325135071,609,14140112)) (.node 76 (.leaf (17178820319,610,15600529)) (.leaf (34358689503,611,16197384)))))) (.node 82 (.node 79 (.node 78 (.leaf (17146314463,610,15598702)) (.leaf (34326183647,611,16196124))) (.node 80 (.leaf (17179868895,612,16091537)) (.node 81 (.leaf (34359738079,613,16419025)) (.leaf (17145253855,607,13466208))))) (.node 85 (.node 83 (.leaf (34325123039,608,14054992)) (.node 84 (.leaf (17178808287,608,13942544)) (.leaf (34358677471,610,16373896)))) (.node 86 (.leaf (17146302431,608,13424698)) (.node 87 (.leaf (34326171615,610,16114721)) (.leaf (17179856863,610,15744169))))))))) (.node 132 (.node 110 (.node 99 (.node 93 (.node 90 (.node 89 (.leaf (34359726047,611,16341080)) (.leaf (17145262047,608,12967458))) (.node 91 (.leaf (34325131231,610,15656977)) (.node 92 (.leaf (17178816479,609,13942544)) (.leaf (34358685663,611,16108680))))) (.node 96 (.node 94 (.leaf (17146310623,610,15538222)) (.node 95 (.leaf (34326179807,612,16147985)) (.leaf (17179865055,611,15539237)))) (.node 97 (.leaf (34359734239,613,16398865)) (.node 98 (.leaf (17145257951,608,12966072)) (.leaf (34325127135,610,15656032)))))) (.node 104 (.node 101 (.node 100 (.leaf (17178812383,610,15539104)) (.leaf (34358681567,612,16434824))) (.node 102 (.leaf (17146306527,609,12966072)) (.node 103 (.leaf (34326175711,611,15619184)) (.leaf (17179860959,611,15538544))))) (.node 107 (.node 105 (.leaf (34359730143,613,16397416)) (.node 106 (.leaf (17145266143,610,14826161)) (.leaf (34325135327,611,15423072)))) (.node 108 (.leaf (17178820575,611,15310176)) (.node 109 (.leaf (34358689759,613,15682184)) (.leaf (17146314719,611,15308853))))))) (.node 121 (.node 115 (.node 112 (.node 111 (.leaf (34326183903,613,15938601)) (.leaf (17179869151,613,15797481))) (.node 113 (.leaf (34359738335,614,16427096)) (.node 114 (.leaf (17145253631,607,13464388)) (.leaf (34325122815,608,14054082))))) (.node 118 (.node 116 (.leaf (17178808063,608,13941186)) (.node 117 (.leaf (34358677247,610,16372993)) (.leaf (17146302207,608,13422871)))) (.node 119 (.leaf (34326171391,610,16113804)) (.node 120 (.leaf (17179856639,610,15742349)) (.leaf (34359725823,611,16339715)))))) (.node 126 (.node 123 (.node 122 (.leaf (17145261823,608,13023367)) (.leaf (34325131007,610,15684676))) (.node 124 (.leaf (17178816255,610,15539524)) (.node 125 (.leaf (34358685439,612,16406145)) (.leaf (17146310399,609,13023367))))) (.node 129 (.node 127 (.leaf (34326179583,611,15647814)) (.node 128 (.leaf (17179864831,611,15538950)) (.leaf (34359734015,613,16368709)))) (.node 130 (.leaf (17145257727,608,13021666)) (.node 131 (.leaf (34325126911,610,15683857)) (.leaf (17178812159,609,13998544)))))))) (.node 154 (.node 143 (.node 137 (.node 134 (.node 133 (.leaf (34358681343,611,16135560)) (.leaf (17146306303,610,15536437))) (.node 135 (.leaf (34326175487,612,16203985)) (.node 136 (.leaf (17179860735,611,15536556)) (.leaf (34359729919,613,16367953))))) (.node 140 (.node 138 (.leaf (17145265919,610,14824782)) (.node 139 (.leaf (34325135103,611,15422148)) (.leaf (17178820351,611,15309700)))) (.node 141 (.leaf (34358689535,613,15680833)) (.node 142 (.leaf (17146314495,611,15307054)) (.leaf (34326183679,613,15937677)))))) (.node 148 (.node 145 (.node 144 (.leaf (17179868927,613,15796109)) (.leaf (34359738111,614,16425731))) (.node 146 (.leaf (17145253887,608,12876514)) (.node 147 (.leaf (34325123071,609,14054992)) (.leaf (17178808319,610,15486289))))) (.node 151 (.node 149 (.leaf (34358677503,611,16083144)) (.node 150 (.leaf (17146302463,610,15484021)) (.leaf (34326171647,611,16081443)))) (.node 152 (.leaf (17179856895,612,16006417)) (.node 153 (.leaf (34359726079,613,16275217)) (.leaf (17145262079,610,14797454))))))) (.node 165 (.node 159 (.node 156 (.node 155 (.leaf (34325131263,611,15394372)) (.leaf (17178816511,611,15252804))) (.node 157 (.leaf (34358685695,613,15624833)) (.node 158 (.leaf (17146310655,611,15251502)) (.leaf (34326179839,613,15852557))))) (.node 162 (.node 160 (.leaf (17179865087,613,15740109)) (.node 161 (.leaf (34359734271,614,16341059)) (.leaf (17145257983,610,14796145)))) (.node 163 (.leaf (34325127167,611,15393504)) (.node 164 (.leaf (17178812415,611,15252384)) (.leaf (34358681599,613,15623496)))))) (.node 171 (.node 168 (.node 166 (.leaf (17146306559,611,15249717)) (.node 167 (.leaf (34326175743,613,15851689)) (.leaf (17179860991,613,15738793)))) (.node 169 (.leaf (34359730175,614,16339736)) (.node 170 (.leaf (17145266175,612,14801073)) (.leaf (34325135359,613,14870681))))) (.node 174 (.node 172 (.leaf (17178820607,613,14822297)) (.node 173 (.leaf (34358689791,614,15395016)) (.leaf (17146314751,613,14820974)))) (.node 175 (.leaf (34326183935,614,15393315)) (.node 176 (.leaf (17179869183,614,15240099)) (.leaf (34359738367,615,16434824))))))))))

noncomputable def models (i : Fin 177) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 177) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 177) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 70, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (7 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 70, (7 : Fin 8) ∈ U i → ∃ j : Fin 35, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C72




end
end
end BundlePart2

