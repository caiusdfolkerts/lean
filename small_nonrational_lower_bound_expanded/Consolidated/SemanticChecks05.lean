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
/- Source: MatroidChecked/SemanticChunks/Cases06Part01.lean -/




@[expose] public section
noncomputable section

/- Source: MatroidCatalogue/Cases/N8R4C44Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C44

abbrev U := N8R4.grid
noncomputable def old : Finset (Finset (Fin 8)) := N7R4.family 44
noncomputable def newIndexTree : Table ℕ := (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf 35) (.leaf 36)) (.node 3 (.leaf 37) (.leaf 38))) (.node 6 (.node 5 (.leaf 39) (.leaf 40)) (.node 7 (.leaf 41) (.leaf 42)))) (.node 12 (.node 10 (.node 9 (.leaf 43) (.leaf 44)) (.node 11 (.leaf 45) (.leaf 46))) (.node 14 (.node 13 (.leaf 47) (.leaf 48)) (.node 15 (.leaf 49) (.node 16 (.leaf 50) (.leaf 51)))))) (.node 26 (.node 21 (.node 19 (.node 18 (.leaf 52) (.leaf 53)) (.node 20 (.leaf 54) (.leaf 55))) (.node 23 (.node 22 (.leaf 56) (.leaf 57)) (.node 24 (.leaf 58) (.node 25 (.leaf 59) (.leaf 60))))) (.node 30 (.node 28 (.node 27 (.leaf 61) (.leaf 62)) (.node 29 (.leaf 63) (.leaf 64))) (.node 32 (.node 31 (.leaf 65) (.leaf 66)) (.node 33 (.leaf 67) (.node 34 (.leaf 68) (.leaf 69)))))))
noncomputable def newIndex (i : Fin 35) : Fin 70 := Fin.ofNat 70 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 98 (.node 49 (.node 24 (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (30904451072,98,6248648)) (.node 2 (.leaf (29755138048,116,8345736)) (.leaf (33814994944,131,6248648)))) (.node 4 (.leaf (25762455552,139,6248648)) (.node 5 (.leaf (17172520960,139,6245064)) (.leaf (34352390144,140,8345736))))) (.node 9 (.node 7 (.leaf (25172580352,116,8344840)) (.node 8 (.leaf (1072691200,175,6248648)) (.leaf (25567229952,139,6240584)))) (.node 10 (.leaf (25500055552,171,6245064)) (.node 11 (.leaf (25768753152,179,8344840)) (.leaf (16171202560,116,8334088)))))) (.node 18 (.node 15 (.node 13 (.leaf (34123577344,131,6241032)) (.node 14 (.leaf (29862197248,139,6241032)) (.leaf (34157164544,140,8334088)))) (.node 16 (.leaf (34064799744,131,6248200)) (.node 17 (.leaf (30038530048,139,6248200)) (.leaf (17153628160,139,6244168))))) (.node 21 (.node 19 (.leaf (34333497344,140,8344840)) (.node 20 (.leaf (30868764672,170,6245064)) (.leaf (34089990144,172,10435208)))) (.node 22 (.leaf (31103875072,170,6248648)) (.node 23 (.leaf (17145231360,171,6248648)) (.leaf (34325100544,172,10442376))))))) (.node 36 (.node 30 (.node 27 (.node 25 (.leaf (17178818560,179,8334088)) (.node 26 (.leaf (30600067072,170,6244168)) (.leaf (29526325248,171,6244168)))) (.node 28 (.leaf (33821292544,172,10433864)) (.node 29 (.leaf (31137462272,177,6248648)) (.leaf (30063720448,179,8345736))))) (.node 33 (.node 31 (.leaf (34358687744,180,12535432)) (.node 32 (.leaf (1071645676,243,8219400)) (.leaf (1047532,243,7072520)))) (.node 34 (.leaf (1072692204,279,9272648)) (.node 35 (.leaf (31103681516,249,6155016)) (.leaf (30868800492,249,6151432)))))) (.node 42 (.node 39 (.node 37 (.leaf (30600365036,249,6150536)) (.node 38 (.leaf (31137235948,250,8219400)) (.leaf (30904646636,249,5237512)))) (.node 40 (.leaf (30904417260,249,5233928)) (.node 41 (.leaf (30904155116,249,5233032)) (.leaf (30904679404,250,7072520))))) (.node 45 (.node 43 (.leaf (30868995052,303,8059016)) (.node 44 (.leaf (30600559596,303,8058120)) (.leaf (31137430508,304,12220040)))) (.node 47 (.node 46 (.leaf (30868503532,303,7810824)) (.leaf (30869027820,304,11746952))) (.node 48 (.leaf (31103384556,303,7828744)) (.leaf (31136938988,304,12203464)))))))) (.node 73 (.node 61 (.node 55 (.node 52 (.node 50 (.leaf (31103646700,303,7829640)) (.node 51 (.leaf (31103908844,304,11761288)) (.leaf (30600330220,303,8040200)))) (.node 53 (.leaf (31137201132,304,12205704)) (.node 54 (.leaf (30600592364,304,11744712)) (.leaf (31137463276,309,11664520))))) (.node 58 (.node 56 (.leaf (30038254572,275,8059016)) (.node 57 (.leaf (29862093804,275,8048264)) (.leaf (29526549484,276,8284808)))) (.node 59 (.leaf (30063420396,277,10349192)) (.node 60 (.leaf (29755415532,275,7829640)) (.leaf (29755243500,275,7818888)))))) (.node 67 (.node 64 (.node 62 (.leaf (29754915820,276,7596680)) (.node 63 (.leaf (29755440108,277,9431688)) (.leaf (29862370284,293,5720008)))) (.node 65 (.leaf (29526825964,294,8308104)) (.node 66 (.leaf (30063696876,295,10347848)) (.leaf (29861870572,294,7842184))))) (.node 70 (.node 68 (.leaf (29862394860,295,9416008)) (.node 69 (.leaf (30038031340,294,7849352)) (.leaf (30063197164,307,14595336)))) (.node 71 (.leaf (30038359020,293,5949384)) (.node 72 (.leaf (30038555628,295,9430344)) (.leaf (29526653932,294,8300936))))))) (.node 85 (.node 79 (.node 76 (.node 74 (.leaf (30063524844,295,10333512)) (.node 75 (.leaf (29526850540,307,14136584)) (.leaf (30063721452,310,16434824)))) (.node 77 (.leaf (16172162028,275,7809480)) (.node 78 (.leaf (25499737068,276,8283464)) (.leaf (34090228716,295,12534984))))) (.node 82 (.node 80 (.leaf (25761881068,275,8058120)) (.node 81 (.leaf (25566845932,275,8046024)) (.leaf (25768172524,277,10347848)))) (.node 83 (.leaf (34123521004,288,6244168)) (.node 84 (.leaf (34157075436,289,8300936)) (.leaf (34123783148,289,7849352)))))) (.node 91 (.node 88 (.node 86 (.leaf (34157337580,297,9909704)) (.node 87 (.leaf (34324847596,291,10413256)) (.leaf (17145240556,294,8316168)))) (.node 89 (.leaf (34325109740,299,10413256)) (.node 90 (.leaf (17172503532,293,5961928)) (.leaf (17178794988,295,10343816))))) (.node 94 (.node 92 (.leaf (33815239660,288,6019272)) (.node 93 (.leaf (34352110572,289,8317064)) (.leaf (33815501804,289,7857416)))) (.node 96 (.node 95 (.leaf (34352372716,297,10155656)) (.leaf (33821531116,291,10401160))) (.node 97 (.leaf (34358402028,292,12477640)) (.leaf (33821793260,299,10401160))))))))) (.node 147 (.node 122 (.node 110 (.node 104 (.node 101 (.node 99 (.leaf (34358664172,300,12477640)) (.node 100 (.leaf (16172180460,275,7810824)) (.leaf (16172153836,276,7581000)))) (.node 102 (.leaf (16172186604,277,9416008)) (.node 103 (.leaf (17171545068,275,8040200)) (.leaf (17152670700,275,8038856))))) (.node 107 (.node 105 (.leaf (17144282092,276,8269128)) (.node 106 (.leaf (17177836524,277,10333512)) (.leaf (17172495340,294,7858312)))) (.node 108 (.leaf (17172528108,295,9428104)) (.node 109 (.leaf (17153620972,294,7857416)) (.leaf (17178786796,307,14599816)))))) (.node 116 (.node 113 (.node 111 (.leaf (17153647596,293,5732552)) (.node 112 (.leaf (17153653740,295,9426312)) (.leaf (17145258988,294,8317064)))) (.node 114 (.leaf (17178813420,295,10345608)) (.node 115 (.leaf (17145265132,307,14141064)) (.leaf (17178819564,310,16427208))))) (.node 119 (.node 117 (.leaf (25173156844,275,7828744)) (.node 118 (.leaf (25172966380,275,7816648)) (.leaf (25172900844,276,7595336)))) (.node 120 (.leaf (25173162988,277,9430344)) (.node 121 (.leaf (34324937708,295,12527816)) (.leaf (34123545580,291,9940168))))))) (.node 134 (.node 128 (.node 125 (.node 123 (.leaf (34324872172,306,12535432)) (.node 124 (.leaf (34123277292,288,6245064)) (.leaf (34123801580,289,7851144)))) (.node 126 (.leaf (34324603884,291,10413704)) (.node 127 (.leaf (34325128172,299,10413704)) (.leaf (34123283436,291,9938824))))) (.node 131 (.node 129 (.leaf (34123807724,292,11775176)) (.node 130 (.leaf (34324610028,306,12534984)) (.leaf (34325134316,308,14141064)))) (.node 132 (.leaf (34157329388,295,12298440)) (.node 133 (.leaf (25567165420,294,7843080)) (.leaf (34157100012,299,9940168)))))) (.node 140 (.node 137 (.node 135 (.leaf (34156831724,289,8301832)) (.node 136 (.leaf (25567421420,293,5721800)) (.leaf (34157356012,297,9911944)))) (.node 138 (.leaf (34156837868,299,9938824)) (.node 139 (.leaf (25567427564,295,9415560)) (.leaf (34157362156,300,11775176))))) (.node 143 (.node 141 (.leaf (34333260780,295,12305608)) (.node 142 (.leaf (33815264236,291,9944200)) (.leaf (25762200556,294,7851144)))) (.node 145 (.node 144 (.leaf (34352135148,299,9944200)) (.leaf (33821555692,306,12298440))) (.node 146 (.leaf (25768492012,307,14596232)) (.leaf (34358426604,308,14596232)))))))) (.node 172 (.node 159 (.node 153 (.node 150 (.node 148 (.leaf (33821811692,295,12535432)) (.node 149 (.leaf (25500312556,294,8309896)) (.leaf (25768748012,295,10349192)))) (.node 151 (.leaf (34064557036,288,6248648)) (.node 152 (.leaf (34332992492,289,8316168)) (.leaf (34065081324,289,7858312))))) (.node 156 (.node 154 (.leaf (34333516780,297,9926280)) (.node 155 (.leaf (34089722860,291,10402952)) (.leaf (34358158316,292,12478088)))) (.node 157 (.leaf (34090247148,299,10402952)) (.node 158 (.leaf (34358682604,300,12478088)) (.leaf (34064563180,291,9942408)))))) (.node 165 (.node 162 (.node 160 (.leaf (34332998636,299,9942408)) (.node 161 (.leaf (34064858092,288,6014792)) (.leaf (34333293548,289,8308104)))) (.node 163 (.leaf (34064890860,289,7842184)) (.node 164 (.leaf (34333326316,297,10139080)) (.leaf (34065054700,291,9954504))))) (.node 168 (.node 166 (.leaf (34333490156,299,9954504)) (.node 167 (.leaf (34065087468,292,11789512)) (.leaf (34333522924,300,11789512)))) (.node 170 (.node 169 (.leaf (34351873004,295,12306056)) (.leaf (34089729004,306,12527816))) (.node 171 (.leaf (34358164460,308,14595336)) (.leaf (34090023916,291,10398920))))))) (.node 184 (.node 178 (.node 175 (.node 173 (.leaf (25500122092,294,8301832)) (.node 174 (.leaf (34090056684,299,10398920)) (.leaf (34090220524,306,12306056)))) (.node 176 (.leaf (25500318700,307,14137480)) (.node 177 (.leaf (34090253292,308,14137480)) (.leaf (25762266092,293,5951176))))) (.node 181 (.node 179 (.leaf (25768557548,295,10333064)) (.node 180 (.leaf (25762462700,295,9431688)) (.leaf (25768754156,310,16434376)))) (.node 182 (.leaf (33815297004,288,6015688)) (.node 183 (.leaf (34352167916,289,8309896)) (.leaf (33815329772,289,7843080)))))) (.node 190 (.node 187 (.node 185 (.leaf (34352200684,297,10141320)) (.node 186 (.leaf (33821588460,291,10397576)) (.leaf (34358459372,292,12463304)))) (.node 188 (.leaf (33821621228,299,10397576)) (.node 189 (.leaf (34358492140,300,12463304)) (.leaf (33815493612,291,9954952))))) (.node 193 (.node 191 (.leaf (34352364524,299,9954952)) (.node 192 (.leaf (33815526380,292,11789960)) (.leaf (34352397292,300,11789960)))) (.node 195 (.node 194 (.leaf (33821785068,306,12305608)) (.leaf (34358655980,308,14599816))) (.node 196 (.leaf (33821817836,308,14136584)) (.leaf (34358688748,311,16434824))))))))))

noncomputable def models (i : Fin 197) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 197) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 197) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 70, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (7 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 70, (7 : Fin 8) ∈ U i → ∃ j : Fin 35, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C44

/- Source: MatroidCatalogue/Cases/N8R4C44Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C44


noncomputable def certificates_0 : List (Origin 70 197 × List Sat.Literal) :=
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
   ((.fixed 30),[(.pos 30)]),
   ((.fixed 31),[(.pos 31)]),
   ((.fixed 32),[(.pos 32)]),
   ((.fixed 33),[(.pos 33)]),
   ((.fixed 34),[(.pos 34)]),
   ((.exchange 7 41 5),[(.neg 41),(.neg 7),(.pos 0),(.pos 3),(.pos 37)]),
   ((.exchange 7 47 3),[(.neg 47),(.neg 7),(.pos 5),(.pos 46)]),
   ((.exchange 7 49 2),[(.neg 49),(.neg 7),(.pos 6),(.pos 48)]),
   ((.exchange 8 41 5),[(.neg 41),(.neg 8),(.pos 4),(.pos 38)]),
   ((.exchange 8 46 3),[(.neg 46),(.neg 8),(.pos 5),(.pos 47)]),
   ((.exchange 8 48 2),[(.neg 48),(.neg 8),(.pos 6),(.pos 49)]),
   ((.exchange 10 41 5),[(.neg 41),(.neg 10),(.pos 1),(.pos 40)]),
   ((.exchange 10 52 2),[(.neg 52),(.neg 10),(.pos 9),(.pos 51)]),
   ((.exchange 11 37 5),[(.neg 37),(.neg 11),(.pos 1),(.pos 4),(.pos 41)]),
   ((.exchange 11 38 5),[(.neg 38),(.neg 11),(.pos 4),(.pos 41)]),
   ((.exchange 11 40 5),[(.neg 40),(.neg 11),(.pos 1),(.pos 41)]),
   ((.exchange 11 42 5),[(.neg 42),(.neg 11),(.pos 1),(.pos 4),(.pos 41)]),
   ((.exchange 11 43 5),[(.neg 43),(.neg 11),(.pos 4),(.pos 41)]),
   ((.exchange 11 44 5),[(.neg 44),(.neg 11),(.pos 4),(.pos 41)]),
   ((.exchange 11 51 2),[(.neg 51),(.neg 11),(.pos 9),(.pos 52)]),
   ((.exchange 12 41 5),[(.neg 41),(.neg 12),(.pos 2),(.pos 3),(.pos 42)]),
   ((.exchange 13 41 5),[(.neg 41),(.neg 13),(.pos 4),(.pos 43)]),
   ((.exchange 14 41 5),[(.neg 41),(.neg 14),(.pos 4),(.pos 44)]),
   ((.exchange 17 57 3),[(.neg 57),(.neg 17),(.pos 15),(.pos 56)]),
   ((.exchange 17 59 2),[(.neg 59),(.neg 17),(.pos 16),(.pos 58)]),
   ((.exchange 18 56 3),[(.neg 56),(.neg 18),(.pos 15),(.pos 57)]),
   ((.exchange 18 58 2),[(.neg 58),(.neg 18),(.pos 16),(.pos 59)]),
   ((.exchange 20 62 2),[(.neg 62),(.neg 20),(.pos 19),(.pos 61)]),
   ((.exchange 21 61 2),[(.neg 61),(.neg 21),(.pos 19),(.pos 62)]),
   ((.exchange 26 66 2),[(.neg 66),(.neg 26),(.pos 25),(.pos 65)]),
   ((.exchange 27 65 2),[(.neg 65),(.neg 27),(.pos 25),(.pos 66)]),
   ((.exchange 35 7 7),[(.neg 35),(.neg 7),(.pos 0),(.pos 5)]),
   ((.exchange 36 7 7),[(.neg 36),(.neg 7),(.pos 0),(.pos 6)]),
   ((.exchange 37 26 3),[(.neg 37),(.neg 26),(.pos 46),(.pos 56)]),
   ((.exchange 37 28 2),[(.neg 37),(.neg 28),(.pos 48),(.pos 58)]),
   ((.exchange 37 67 3),[(.neg 67),(.neg 37),(.pos 46),(.pos 56)]),
   ((.exchange 38 26 3),[(.neg 38),(.neg 26),(.pos 35),(.pos 47),(.pos 57)]),
   ((.exchange 38 28 2),[(.neg 38),(.neg 28),(.pos 36),(.pos 49),(.pos 59)]),
   ((.exchange 39 7 7),[(.neg 39),(.neg 7),(.pos 1),(.pos 2),(.pos 9)]),
   ((.exchange 40 27 4),[(.neg 40),(.neg 27),(.pos 35),(.pos 46),(.pos 56)]),
   ((.exchange 40 31 2),[(.neg 40),(.neg 31),(.pos 51),(.pos 61)]),
   ((.exchange 40 33 0),[(.neg 40),(.neg 33),(.pos 53),(.pos 63)]),
   ((.exchange 41 31 2),[(.neg 41),(.neg 31),(.pos 39),(.pos 52),(.pos 62)]),
   ((.exchange 41 67 4),[(.neg 67),(.neg 41),(.pos 47),(.pos 57)]),
   ((.exchange 42 29 4),[(.neg 42),(.neg 29),(.pos 36),(.pos 48),(.pos 58)]),
   ((.exchange 42 34 0),[(.neg 42),(.neg 34),(.pos 54),(.pos 64)]),
   ((.exchange 42 68 0),[(.neg 68),(.neg 42),(.pos 54),(.pos 64)]),
   ((.exchange 42 69 0),[(.neg 69),(.neg 42),(.pos 54),(.pos 64)]),
   ((.exchange 42 69 3),[(.neg 69),(.neg 42),(.pos 51),(.pos 61)]),
   ((.exchange 43 29 4),[(.neg 43),(.neg 29),(.pos 49),(.pos 59)]),
   ((.exchange 43 68 1),[(.neg 68),(.neg 43),(.pos 54),(.pos 64)]),
   ((.exchange 43 69 3),[(.neg 69),(.neg 43),(.pos 52),(.pos 62)]),
   ((.exchange 44 30 4),[(.neg 44),(.neg 30),(.pos 50),(.pos 60)]),
   ((.exchange 44 33 3),[(.neg 44),(.neg 33),(.pos 53),(.pos 63)]),
   ((.exchange 44 67 3),[(.neg 67),(.neg 44),(.pos 53),(.pos 63)]),
   ((.exchange 44 67 4),[(.neg 67),(.neg 44),(.pos 50),(.pos 60)]),
   ((.exchange 44 69 2),[(.neg 69),(.neg 44),(.pos 54),(.pos 64)]),
   ((.exchange 44 69 3),[(.neg 69),(.neg 44),(.pos 53),(.pos 63)]),
   ((.exchange 45 7 7),[(.neg 45),(.neg 7),(.pos 5),(.pos 6)]),
   ((.exchange 46 12 2),[(.neg 46),(.neg 12),(.pos 48),(.pos 51)]),
   ((.exchange 46 14 0),[(.neg 46),(.neg 14),(.pos 50),(.pos 53)]),
   ((.exchange 46 17 5),[(.neg 46),(.neg 17),(.pos 37),(.pos 56)]),
   ((.exchange 46 28 2),[(.neg 46),(.neg 28),(.pos 48),(.pos 65)]),
   ((.exchange 46 30 0),[(.neg 46),(.neg 30),(.pos 50),(.pos 67)]),
   ((.exchange 46 31 2),[(.neg 46),(.neg 31),(.pos 51),(.pos 65)]),
   ((.exchange 46 42 2),[(.neg 46),(.neg 42),(.pos 48),(.pos 51)]),
   ((.exchange 46 54 2),[(.neg 54),(.neg 46),(.pos 48),(.pos 51)]),
   ((.exchange 46 58 2),[(.neg 58),(.neg 46),(.pos 48),(.pos 65)]),
   ((.exchange 46 60 0),[(.neg 60),(.neg 46),(.pos 50),(.pos 67)]),
   ((.exchange 46 63 0),[(.neg 63),(.neg 46),(.pos 53),(.pos 67)]),
   ((.exchange 46 68 0),[(.neg 68),(.neg 46),(.pos 50),(.pos 67)]),
   ((.exchange 46 69 2),[(.neg 69),(.neg 46),(.pos 51),(.pos 65)]),
   ((.exchange 47 12 2),[(.neg 47),(.neg 12),(.pos 45),(.pos 49),(.pos 52)]),
   ((.exchange 47 14 1),[(.neg 47),(.neg 14),(.pos 50),(.pos 53)]),
   ((.exchange 47 17 5),[(.neg 47),(.neg 17),(.pos 35),(.pos 38),(.pos 57)]),
   ((.exchange 47 28 2),[(.neg 47),(.neg 28),(.pos 45),(.pos 49),(.pos 66)]),
   ((.exchange 47 30 1),[(.neg 47),(.neg 30),(.pos 50),(.pos 67)]),
   ((.exchange 47 31 2),[(.neg 47),(.neg 31),(.pos 45),(.pos 52),(.pos 66)]),
   ((.exchange 47 33 1),[(.neg 47),(.neg 33),(.pos 53),(.pos 67)]),
   ((.exchange 47 42 2),[(.neg 47),(.neg 42),(.pos 45),(.pos 49),(.pos 52)]),
   ((.exchange 47 54 2),[(.neg 54),(.neg 47),(.pos 49),(.pos 52)]),
   ((.exchange 47 58 2),[(.neg 58),(.neg 47),(.pos 45),(.pos 49),(.pos 66)]),
   ((.exchange 47 69 2),[(.neg 69),(.neg 47),(.pos 52),(.pos 66)]),
   ((.exchange 48 14 0),[(.neg 48),(.neg 14),(.pos 50),(.pos 54)]),
   ((.exchange 48 17 5),[(.neg 48),(.neg 17),(.pos 37),(.pos 58)]),
   ((.exchange 48 26 3),[(.neg 48),(.neg 26),(.pos 46),(.pos 65)]),
   ((.exchange 48 30 0),[(.neg 48),(.neg 30),(.pos 50),(.pos 68)]),
   ((.exchange 48 32 3),[(.neg 48),(.neg 32),(.pos 45),(.pos 51),(.pos 65)]),
   ((.exchange 48 34 0),[(.neg 48),(.neg 34),(.pos 54),(.pos 68)]),
   ((.exchange 48 40 3),[(.neg 48),(.neg 40),(.pos 46),(.pos 51)]),
   ((.exchange 48 44 0),[(.neg 48),(.neg 44),(.pos 50),(.pos 54)]),
   ((.exchange 48 53 0),[(.neg 53),(.neg 48),(.pos 50),(.pos 54)]),
   ((.exchange 48 57 3),[(.neg 57),(.neg 48),(.pos 45),(.pos 46),(.pos 65)]),
   ((.exchange 48 57 5),[(.neg 57),(.neg 48),(.pos 36),(.pos 37),(.pos 58)]),
   ((.exchange 48 59 5),[(.neg 59),(.neg 48),(.pos 36),(.pos 58)]),
   ((.exchange 48 64 0),[(.neg 64),(.neg 48),(.pos 54),(.pos 68)]),
   ((.exchange 48 67 0),[(.neg 67),(.neg 48),(.pos 50),(.pos 68)]),
   ((.exchange 49 11 3),[(.neg 49),(.neg 11),(.pos 47),(.pos 52)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_1 : List (Origin 70 197 × List Sat.Literal) :=
  [((.exchange 49 17 5),[(.neg 49),(.neg 17),(.pos 36),(.pos 38),(.pos 59)]),
   ((.exchange 49 26 3),[(.neg 49),(.neg 26),(.pos 45),(.pos 47),(.pos 66)]),
   ((.exchange 49 30 1),[(.neg 49),(.neg 30),(.pos 50),(.pos 68)]),
   ((.exchange 49 32 3),[(.neg 49),(.neg 32),(.pos 52),(.pos 66)]),
   ((.exchange 49 34 1),[(.neg 49),(.neg 34),(.pos 54),(.pos 68)]),
   ((.exchange 49 40 3),[(.neg 49),(.neg 40),(.pos 45),(.pos 47),(.pos 52)]),
   ((.exchange 49 57 5),[(.neg 57),(.neg 49),(.pos 38),(.pos 59)]),
   ((.exchange 49 64 1),[(.neg 64),(.neg 49),(.pos 54),(.pos 68)]),
   ((.exchange 49 67 1),[(.neg 67),(.neg 49),(.pos 50),(.pos 68)]),
   ((.exchange 49 67 3),[(.neg 67),(.neg 49),(.pos 47),(.pos 66)]),
   ((.exchange 49 69 1),[(.neg 69),(.neg 49),(.pos 54),(.pos 68)]),
   ((.exchange 50 12 2),[(.neg 50),(.neg 12),(.pos 48),(.pos 54)]),
   ((.exchange 50 13 2),[(.neg 50),(.neg 13),(.pos 49),(.pos 54)]),
   ((.exchange 50 22 5),[(.neg 50),(.neg 22),(.pos 37),(.pos 44),(.pos 60)]),
   ((.exchange 50 26 3),[(.neg 50),(.neg 26),(.pos 46),(.pos 67)]),
   ((.exchange 50 27 3),[(.neg 50),(.neg 27),(.pos 47),(.pos 67)]),
   ((.exchange 50 28 2),[(.neg 50),(.neg 28),(.pos 48),(.pos 68)]),
   ((.exchange 50 29 2),[(.neg 50),(.neg 29),(.pos 49),(.pos 68)]),
   ((.exchange 50 33 3),[(.neg 50),(.neg 33),(.pos 53),(.pos 67)]),
   ((.exchange 50 34 2),[(.neg 50),(.neg 34),(.pos 54),(.pos 68)]),
   ((.exchange 50 40 3),[(.neg 50),(.neg 40),(.pos 46),(.pos 53)]),
   ((.exchange 50 42 2),[(.neg 50),(.neg 42),(.pos 48),(.pos 54)]),
   ((.exchange 50 43 2),[(.neg 50),(.neg 43),(.pos 49),(.pos 54)]),
   ((.exchange 50 51 2),[(.neg 51),(.neg 50),(.pos 48),(.pos 54)]),
   ((.exchange 50 52 2),[(.neg 52),(.neg 50),(.pos 49),(.pos 54)]),
   ((.exchange 50 56 5),[(.neg 56),(.neg 50),(.pos 37),(.pos 60)]),
   ((.exchange 50 59 2),[(.neg 59),(.neg 50),(.pos 49),(.pos 68)]),
   ((.exchange 50 63 3),[(.neg 63),(.neg 50),(.pos 53),(.pos 67)]),
   ((.exchange 50 65 2),[(.neg 65),(.neg 50),(.pos 48),(.pos 68)]),
   ((.exchange 50 66 3),[(.neg 66),(.neg 50),(.pos 47),(.pos 67)]),
   ((.exchange 50 69 2),[(.neg 69),(.neg 50),(.pos 54),(.pos 68)]),
   ((.exchange 51 7 4),[(.neg 51),(.neg 7),(.pos 46),(.pos 48)]),
   ((.exchange 51 17 5),[(.neg 51),(.neg 17),(.pos 40),(.pos 42),(.pos 61)]),
   ((.exchange 51 26 4),[(.neg 51),(.neg 26),(.pos 46),(.pos 65)]),
   ((.exchange 51 27 4),[(.neg 51),(.neg 27),(.pos 45),(.pos 46),(.pos 65)]),
   ((.exchange 51 34 0),[(.neg 51),(.neg 34),(.pos 54),(.pos 69)]),
   ((.exchange 51 44 0),[(.neg 51),(.neg 44),(.pos 53),(.pos 54)]),
   ((.exchange 51 50 4),[(.neg 51),(.neg 50),(.pos 46),(.pos 48)]),
   ((.exchange 51 57 5),[(.neg 57),(.neg 51),(.pos 39),(.pos 40),(.pos 61)]),
   ((.exchange 51 63 0),[(.neg 63),(.neg 51),(.pos 53),(.pos 69)]),
   ((.exchange 51 64 0),[(.neg 64),(.neg 51),(.pos 54),(.pos 69)]),
   ((.exchange 51 68 0),[(.neg 68),(.neg 51),(.pos 54),(.pos 69)]),
   ((.exchange 52 17 5),[(.neg 52),(.neg 17),(.pos 39),(.pos 41),(.pos 43),(.pos 62)]),
   ((.exchange 52 24 5),[(.neg 52),(.neg 24),(.pos 41),(.pos 43),(.pos 62)]),
   ((.exchange 52 26 4),[(.neg 52),(.neg 26),(.pos 45),(.pos 47),(.pos 66)]),
   ((.exchange 52 27 4),[(.neg 52),(.neg 27),(.pos 47),(.pos 66)]),
   ((.exchange 52 29 4),[(.neg 52),(.neg 29),(.pos 49),(.pos 66)]),
   ((.exchange 52 34 1),[(.neg 52),(.neg 34),(.pos 54),(.pos 69)]),
   ((.exchange 52 38 4),[(.neg 52),(.neg 38),(.pos 47),(.pos 49)]),
   ((.exchange 52 44 1),[(.neg 52),(.neg 44),(.pos 53),(.pos 54)]),
   ((.exchange 52 50 1),[(.neg 52),(.neg 50),(.pos 53),(.pos 54)]),
   ((.exchange 52 50 4),[(.neg 52),(.neg 50),(.pos 47),(.pos 49)]),
   ((.exchange 52 60 5),[(.neg 60),(.neg 52),(.pos 41),(.pos 43),(.pos 62)]),
   ((.exchange 52 63 1),[(.neg 63),(.neg 52),(.pos 53),(.pos 69)]),
   ((.exchange 52 68 1),[(.neg 68),(.neg 52),(.pos 54),(.pos 69)]),
   ((.exchange 53 7 4),[(.neg 53),(.neg 7),(.pos 46),(.pos 50)]),
   ((.exchange 53 12 2),[(.neg 53),(.neg 12),(.pos 51),(.pos 54)]),
   ((.exchange 53 13 2),[(.neg 53),(.neg 13),(.pos 52),(.pos 54)]),
   ((.exchange 53 17 5),[(.neg 53),(.neg 17),(.pos 40),(.pos 44),(.pos 63)]),
   ((.exchange 53 24 5),[(.neg 53),(.neg 24),(.pos 44),(.pos 63)]),
   ((.exchange 53 26 4),[(.neg 53),(.neg 26),(.pos 46),(.pos 67)]),
   ((.exchange 53 27 4),[(.neg 53),(.neg 27),(.pos 47),(.pos 67)]),
   ((.exchange 53 31 2),[(.neg 53),(.neg 31),(.pos 51),(.pos 69)]),
   ((.exchange 53 32 2),[(.neg 53),(.neg 32),(.pos 52),(.pos 69)]),
   ((.exchange 53 34 2),[(.neg 53),(.neg 34),(.pos 54),(.pos 69)]),
   ((.exchange 53 38 4),[(.neg 53),(.neg 38),(.pos 47),(.pos 50)]),
   ((.exchange 53 42 2),[(.neg 53),(.neg 42),(.pos 51),(.pos 54)]),
   ((.exchange 53 43 2),[(.neg 53),(.neg 43),(.pos 52),(.pos 54)]),
   ((.exchange 53 49 2),[(.neg 53),(.neg 49),(.pos 52),(.pos 54)]),
   ((.exchange 53 49 4),[(.neg 53),(.neg 49),(.pos 47),(.pos 50)]),
   ((.exchange 53 57 4),[(.neg 57),(.neg 53),(.pos 47),(.pos 67)]),
   ((.exchange 53 59 2),[(.neg 59),(.neg 53),(.pos 52),(.pos 54),(.pos 69)]),
   ((.exchange 53 62 2),[(.neg 62),(.neg 53),(.pos 52),(.pos 69)]),
   ((.exchange 53 65 2),[(.neg 65),(.neg 53),(.pos 51),(.pos 69)]),
   ((.exchange 53 66 2),[(.neg 66),(.neg 53),(.pos 52),(.pos 69)]),
   ((.exchange 53 66 4),[(.neg 66),(.neg 53),(.pos 47),(.pos 67)]),
   ((.exchange 53 68 2),[(.neg 68),(.neg 53),(.pos 54),(.pos 69)]),
   ((.exchange 54 7 4),[(.neg 54),(.neg 7),(.pos 48),(.pos 50)]),
   ((.exchange 54 8 4),[(.neg 54),(.neg 8),(.pos 49),(.pos 50)]),
   ((.exchange 54 10 3),[(.neg 54),(.neg 10),(.pos 51),(.pos 53)]),
   ((.exchange 54 11 3),[(.neg 54),(.neg 11),(.pos 52),(.pos 53)]),
   ((.exchange 54 17 5),[(.neg 54),(.neg 17),(.pos 42),(.pos 44),(.pos 64)]),
   ((.exchange 54 22 5),[(.neg 54),(.neg 22),(.pos 42),(.pos 64)]),
   ((.exchange 54 28 4),[(.neg 54),(.neg 28),(.pos 48),(.pos 68)]),
   ((.exchange 54 29 4),[(.neg 54),(.neg 29),(.pos 49),(.pos 68)]),
   ((.exchange 54 31 3),[(.neg 54),(.neg 31),(.pos 51),(.pos 69)]),
   ((.exchange 54 32 3),[(.neg 54),(.neg 32),(.pos 52),(.pos 69)]),
   ((.exchange 54 33 3),[(.neg 54),(.neg 33),(.pos 53),(.pos 69)]),
   ((.exchange 54 38 4),[(.neg 54),(.neg 38),(.pos 49),(.pos 50)]),
   ((.exchange 54 47 3),[(.neg 54),(.neg 47),(.pos 52),(.pos 53)]),
   ((.exchange 54 61 3),[(.neg 61),(.neg 54),(.pos 51),(.pos 69)]),
   ((.exchange 54 62 3),[(.neg 62),(.neg 54),(.pos 52),(.pos 69)]),
   ((.exchange 54 63 3),[(.neg 63),(.neg 54),(.pos 53),(.pos 69)]),
   ((.exchange 54 67 3),[(.neg 67),(.neg 54),(.pos 53),(.pos 69)]),
   ((.exchange 54 67 4),[(.neg 67),(.neg 54),(.pos 50),(.pos 68)]),
   ((.exchange 55 7 6),[(.neg 55),(.neg 7),(.pos 35),(.pos 36),(.pos 45)]),
   ((.exchange 56 10 6),[(.neg 56),(.neg 10),(.pos 40),(.pos 46)]),
   ((.exchange 56 22 2),[(.neg 56),(.neg 22),(.pos 58),(.pos 61)]),
   ((.exchange 56 28 2),[(.neg 56),(.neg 28),(.pos 58),(.pos 65)]),
   ((.exchange 56 31 2),[(.neg 56),(.neg 31),(.pos 61),(.pos 65)]),
   ((.exchange 56 33 0),[(.neg 56),(.neg 33),(.pos 63),(.pos 67)]),
   ((.exchange 56 43 2),[(.neg 56),(.neg 43),(.pos 55),(.pos 58),(.pos 61)]),
   ((.exchange 56 44 0),[(.neg 56),(.neg 44),(.pos 60),(.pos 63)]),
   ((.exchange 56 64 2),[(.neg 64),(.neg 56),(.pos 58),(.pos 61)]),
   ((.exchange 56 69 0),[(.neg 69),(.neg 56),(.pos 63),(.pos 67)]),
   ((.exchange 57 7 6),[(.neg 57),(.neg 7),(.pos 35),(.pos 38),(.pos 47)]),
   ((.exchange 57 22 2),[(.neg 57),(.neg 22),(.pos 55),(.pos 59),(.pos 62)]),
   ((.exchange 57 24 1),[(.neg 57),(.neg 24),(.pos 60),(.pos 63)]),
   ((.exchange 57 28 2),[(.neg 57),(.neg 28),(.pos 55),(.pos 59),(.pos 66)]),
   ((.exchange 57 31 2),[(.neg 57),(.neg 31),(.pos 55),(.pos 62),(.pos 66)]),
   ((.exchange 57 33 1),[(.neg 57),(.neg 33),(.pos 63),(.pos 67)]),
   ((.exchange 57 50 1),[(.neg 57),(.neg 50),(.pos 60),(.pos 67)]),
   ((.exchange 57 64 2),[(.neg 64),(.neg 57),(.pos 59),(.pos 62)]),
   ((.exchange 58 26 3),[(.neg 58),(.neg 26),(.pos 56),(.pos 65)]),
   ((.exchange 58 27 3),[(.neg 58),(.neg 27),(.pos 55),(.pos 56),(.pos 65)]),
   ((.exchange 58 32 3),[(.neg 58),(.neg 32),(.pos 55),(.pos 61),(.pos 65)]),
   ((.exchange 58 33 0),[(.neg 58),(.neg 33),(.pos 60),(.pos 64),(.pos 68)]),
   ((.exchange 58 40 3),[(.neg 58),(.neg 40),(.pos 56),(.pos 61)]),
   ((.exchange 58 46 3),[(.neg 58),(.neg 46),(.pos 56),(.pos 65)]),
   ((.exchange 58 47 6),[(.neg 58),(.neg 47),(.pos 36),(.pos 37),(.pos 48)]),
   ((.exchange 58 52 6),[(.neg 58),(.neg 52),(.pos 36),(.pos 42),(.pos 48)]),
   ((.exchange 58 53 6),[(.neg 58),(.neg 53),(.pos 37),(.pos 42),(.pos 48)]),
   ((.exchange 58 67 0),[(.neg 67),(.neg 58),(.pos 60),(.pos 68)]),
   ((.exchange 59 14 6),[(.neg 59),(.neg 14),(.pos 38),(.pos 43),(.pos 49)]),
   ((.exchange 59 21 3),[(.neg 59),(.neg 21),(.pos 57),(.pos 62)]),
   ((.exchange 59 24 1),[(.neg 59),(.neg 24),(.pos 60),(.pos 64)]),
   ((.exchange 59 26 3),[(.neg 59),(.neg 26),(.pos 55),(.pos 57),(.pos 66)]),
   ((.exchange 59 27 3),[(.neg 59),(.neg 27),(.pos 57),(.pos 66)])]

theorem certificates_1_valid : ∀ oc ∈ certificates_1,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_2 : List (Origin 70 197 × List Sat.Literal) :=
  [((.exchange 59 30 1),[(.neg 59),(.neg 30),(.pos 60),(.pos 68)]),
   ((.exchange 59 32 3),[(.neg 59),(.neg 32),(.pos 62),(.pos 66)]),
   ((.exchange 59 34 1),[(.neg 59),(.neg 34),(.pos 64),(.pos 68)]),
   ((.exchange 59 41 3),[(.neg 59),(.neg 41),(.pos 57),(.pos 62)]),
   ((.exchange 59 46 3),[(.neg 59),(.neg 46),(.pos 55),(.pos 57),(.pos 66)]),
   ((.exchange 59 52 6),[(.neg 59),(.neg 52),(.pos 43),(.pos 49)]),
   ((.exchange 59 53 6),[(.neg 59),(.neg 53),(.pos 38),(.pos 43),(.pos 49)]),
   ((.exchange 59 63 1),[(.neg 63),(.neg 59),(.pos 60),(.pos 64)]),
   ((.exchange 59 67 1),[(.neg 67),(.neg 59),(.pos 60),(.pos 68)]),
   ((.exchange 60 20 3),[(.neg 60),(.neg 20),(.pos 56),(.pos 63)]),
   ((.exchange 60 21 3),[(.neg 60),(.neg 21),(.pos 57),(.pos 63)]),
   ((.exchange 60 22 2),[(.neg 60),(.neg 22),(.pos 58),(.pos 64)]),
   ((.exchange 60 23 2),[(.neg 60),(.neg 23),(.pos 59),(.pos 64)]),
   ((.exchange 60 26 3),[(.neg 60),(.neg 26),(.pos 56),(.pos 67)]),
   ((.exchange 60 27 3),[(.neg 60),(.neg 27),(.pos 57),(.pos 67)]),
   ((.exchange 60 28 2),[(.neg 60),(.neg 28),(.pos 58),(.pos 68)]),
   ((.exchange 60 29 2),[(.neg 60),(.neg 29),(.pos 59),(.pos 68)]),
   ((.exchange 60 33 3),[(.neg 60),(.neg 33),(.pos 63),(.pos 67)]),
   ((.exchange 60 34 2),[(.neg 60),(.neg 34),(.pos 64),(.pos 68)]),
   ((.exchange 60 41 3),[(.neg 60),(.neg 41),(.pos 57),(.pos 63)]),
   ((.exchange 60 47 6),[(.neg 60),(.neg 47),(.pos 38),(.pos 50)]),
   ((.exchange 60 49 2),[(.neg 60),(.neg 49),(.pos 59),(.pos 68)]),
   ((.exchange 60 54 2),[(.neg 60),(.neg 54),(.pos 64),(.pos 68)]),
   ((.exchange 60 66 2),[(.neg 66),(.neg 60),(.pos 59),(.pos 68)]),
   ((.exchange 60 69 2),[(.neg 69),(.neg 60),(.pos 64),(.pos 68)]),
   ((.exchange 61 7 6),[(.neg 61),(.neg 7),(.pos 40),(.pos 42),(.pos 51)]),
   ((.exchange 61 18 4),[(.neg 61),(.neg 18),(.pos 55),(.pos 56),(.pos 58)]),
   ((.exchange 61 24 0),[(.neg 61),(.neg 24),(.pos 63),(.pos 64)]),
   ((.exchange 61 27 4),[(.neg 61),(.neg 27),(.pos 55),(.pos 56),(.pos 65)]),
   ((.exchange 61 33 0),[(.neg 61),(.neg 33),(.pos 63),(.pos 69)]),
   ((.exchange 61 47 4),[(.neg 61),(.neg 47),(.pos 55),(.pos 56),(.pos 65)]),
   ((.exchange 61 48 6),[(.neg 61),(.neg 48),(.pos 42),(.pos 51)]),
   ((.exchange 61 49 6),[(.neg 61),(.neg 49),(.pos 39),(.pos 42),(.pos 51)]),
   ((.exchange 61 53 0),[(.neg 61),(.neg 53),(.pos 63),(.pos 69)]),
   ((.exchange 61 54 0),[(.neg 61),(.neg 54),(.pos 64),(.pos 69)]),
   ((.exchange 61 60 0),[(.neg 61),(.neg 60),(.pos 63),(.pos 64)]),
   ((.exchange 61 60 4),[(.neg 61),(.neg 60),(.pos 56),(.pos 58)]),
   ((.exchange 61 68 0),[(.neg 68),(.neg 61),(.pos 64),(.pos 69)]),
   ((.exchange 62 7 6),[(.neg 62),(.neg 7),(.pos 39),(.pos 41),(.pos 43),(.pos 52)]),
   ((.exchange 62 18 4),[(.neg 62),(.neg 18),(.pos 57),(.pos 59)]),
   ((.exchange 62 24 1),[(.neg 62),(.neg 24),(.pos 63),(.pos 64)]),
   ((.exchange 62 27 4),[(.neg 62),(.neg 27),(.pos 57),(.pos 66)]),
   ((.exchange 62 34 1),[(.neg 62),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 62 44 1),[(.neg 62),(.neg 44),(.pos 63),(.pos 64)]),
   ((.exchange 62 47 4),[(.neg 62),(.neg 47),(.pos 57),(.pos 66)]),
   ((.exchange 62 49 6),[(.neg 62),(.neg 49),(.pos 43),(.pos 52)]),
   ((.exchange 62 50 4),[(.neg 62),(.neg 50),(.pos 57),(.pos 59),(.pos 66)]),
   ((.exchange 62 53 1),[(.neg 62),(.neg 53),(.pos 63),(.pos 69)]),
   ((.exchange 62 54 1),[(.neg 62),(.neg 54),(.pos 64),(.pos 69)]),
   ((.exchange 63 7 6),[(.neg 63),(.neg 7),(.pos 40),(.pos 44),(.pos 53)]),
   ((.exchange 63 17 4),[(.neg 63),(.neg 17),(.pos 56),(.pos 60)]),
   ((.exchange 63 22 2),[(.neg 63),(.neg 22),(.pos 61),(.pos 64)]),
   ((.exchange 63 23 2),[(.neg 63),(.neg 23),(.pos 62),(.pos 64)]),
   ((.exchange 63 26 4),[(.neg 63),(.neg 26),(.pos 56),(.pos 67)]),
   ((.exchange 63 31 2),[(.neg 63),(.neg 31),(.pos 61),(.pos 69)]),
   ((.exchange 63 32 2),[(.neg 63),(.neg 32),(.pos 62),(.pos 69)]),
   ((.exchange 63 34 2),[(.neg 63),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 63 37 4),[(.neg 63),(.neg 37),(.pos 56),(.pos 60)]),
   ((.exchange 63 38 4),[(.neg 63),(.neg 38),(.pos 57),(.pos 60)]),
   ((.exchange 63 50 6),[(.neg 63),(.neg 50),(.pos 44),(.pos 53)]),
   ((.exchange 63 66 2),[(.neg 66),(.neg 63),(.pos 62),(.pos 69)]),
   ((.exchange 63 68 2),[(.neg 68),(.neg 63),(.pos 64),(.pos 69)]),
   ((.exchange 64 7 6),[(.neg 64),(.neg 7),(.pos 42),(.pos 44),(.pos 54)]),
   ((.exchange 64 17 4),[(.neg 64),(.neg 17),(.pos 58),(.pos 60)]),
   ((.exchange 64 18 4),[(.neg 64),(.neg 18),(.pos 59),(.pos 60)]),
   ((.exchange 64 20 3),[(.neg 64),(.neg 20),(.pos 61),(.pos 63)]),
   ((.exchange 64 21 3),[(.neg 64),(.neg 21),(.pos 62),(.pos 63)]),
   ((.exchange 64 28 4),[(.neg 64),(.neg 28),(.pos 58),(.pos 68)]),
   ((.exchange 64 30 4),[(.neg 64),(.neg 30),(.pos 60),(.pos 68)]),
   ((.exchange 64 33 3),[(.neg 64),(.neg 33),(.pos 63),(.pos 69)]),
   ((.exchange 64 47 4),[(.neg 64),(.neg 47),(.pos 59),(.pos 60),(.pos 68)]),
   ((.exchange 64 50 6),[(.neg 64),(.neg 50),(.pos 44),(.pos 54)]),
   ((.exchange 64 51 6),[(.neg 64),(.neg 51),(.pos 42),(.pos 54)]),
   ((.exchange 64 53 3),[(.neg 64),(.neg 53),(.pos 63),(.pos 69)]),
   ((.exchange 64 56 3),[(.neg 64),(.neg 56),(.pos 61),(.pos 63)]),
   ((.exchange 64 57 3),[(.neg 64),(.neg 57),(.pos 62),(.pos 63)]),
   ((.exchange 64 57 4),[(.neg 64),(.neg 57),(.pos 59),(.pos 60)]),
   ((.exchange 64 66 3),[(.neg 66),(.neg 64),(.pos 62),(.pos 69)]),
   ((.exchange 64 67 3),[(.neg 67),(.neg 64),(.pos 63),(.pos 69)]),
   ((.exchange 64 67 4),[(.neg 67),(.neg 64),(.pos 60),(.pos 68)]),
   ((.exchange 65 7 6),[(.neg 65),(.neg 7),(.pos 46),(.pos 48)]),
   ((.exchange 65 10 6),[(.neg 65),(.neg 10),(.pos 46),(.pos 51)]),
   ((.exchange 65 12 6),[(.neg 65),(.neg 12),(.pos 48),(.pos 51)]),
   ((.exchange 65 33 0),[(.neg 65),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 65 34 0),[(.neg 65),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 65 38 5),[(.neg 65),(.neg 38),(.pos 55),(.pos 56),(.pos 58)]),
   ((.exchange 65 40 6),[(.neg 65),(.neg 40),(.pos 46),(.pos 51)]),
   ((.exchange 65 41 6),[(.neg 65),(.neg 41),(.pos 45),(.pos 46),(.pos 51)]),
   ((.exchange 65 44 0),[(.neg 65),(.neg 44),(.pos 67),(.pos 68),(.pos 69)]),
   ((.exchange 65 50 6),[(.neg 65),(.neg 50),(.pos 46),(.pos 48)]),
   ((.exchange 65 60 0),[(.neg 65),(.neg 60),(.pos 67),(.pos 68)]),
   ((.exchange 65 60 5),[(.neg 65),(.neg 60),(.pos 56),(.pos 58)]),
   ((.exchange 65 63 0),[(.neg 65),(.neg 63),(.pos 67),(.pos 69)]),
   ((.exchange 65 63 5),[(.neg 65),(.neg 63),(.pos 56),(.pos 61)]),
   ((.exchange 66 7 6),[(.neg 66),(.neg 7),(.pos 45),(.pos 47),(.pos 49)]),
   ((.exchange 66 10 6),[(.neg 66),(.neg 10),(.pos 45),(.pos 47),(.pos 52)]),
   ((.exchange 66 12 6),[(.neg 66),(.neg 12),(.pos 45),(.pos 49),(.pos 52)]),
   ((.exchange 66 17 5),[(.neg 66),(.neg 17),(.pos 55),(.pos 57),(.pos 59)]),
   ((.exchange 66 34 1),[(.neg 66),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 66 37 5),[(.neg 66),(.neg 37),(.pos 55),(.pos 57),(.pos 59)]),
   ((.exchange 66 37 6),[(.neg 66),(.neg 37),(.pos 45),(.pos 47),(.pos 49)]),
   ((.exchange 66 38 6),[(.neg 66),(.neg 38),(.pos 47),(.pos 49)]),
   ((.exchange 66 40 6),[(.neg 66),(.neg 40),(.pos 45),(.pos 47),(.pos 52)]),
   ((.exchange 66 50 1),[(.neg 66),(.neg 50),(.pos 67),(.pos 68)]),
   ((.exchange 66 54 1),[(.neg 66),(.neg 54),(.pos 68),(.pos 69)]),
   ((.exchange 66 60 1),[(.neg 66),(.neg 60),(.pos 67),(.pos 68)]),
   ((.exchange 66 60 5),[(.neg 66),(.neg 60),(.pos 57),(.pos 59)]),
   ((.exchange 66 63 5),[(.neg 66),(.neg 63),(.pos 57),(.pos 62)]),
   ((.exchange 67 7 6),[(.neg 67),(.neg 7),(.pos 46),(.pos 50)]),
   ((.exchange 67 14 6),[(.neg 67),(.neg 14),(.pos 50),(.pos 53)]),
   ((.exchange 67 21 5),[(.neg 67),(.neg 21),(.pos 57),(.pos 63)]),
   ((.exchange 67 28 2),[(.neg 67),(.neg 28),(.pos 65),(.pos 68)]),
   ((.exchange 67 29 2),[(.neg 67),(.neg 29),(.pos 66),(.pos 68)]),
   ((.exchange 67 31 2),[(.neg 67),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 67 32 2),[(.neg 67),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 67 34 2),[(.neg 67),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 67 37 5),[(.neg 67),(.neg 37),(.pos 56),(.pos 60)]),
   ((.exchange 67 37 6),[(.neg 67),(.neg 37),(.pos 46),(.pos 50)]),
   ((.exchange 67 38 5),[(.neg 67),(.neg 38),(.pos 57),(.pos 60)]),
   ((.exchange 67 40 6),[(.neg 67),(.neg 40),(.pos 46),(.pos 53)]),
   ((.exchange 67 41 6),[(.neg 67),(.neg 41),(.pos 47),(.pos 53)]),
   ((.exchange 67 44 6),[(.neg 67),(.neg 44),(.pos 50),(.pos 53)]),
   ((.exchange 67 49 6),[(.neg 67),(.neg 49),(.pos 47),(.pos 50)]),
   ((.exchange 67 58 2),[(.neg 67),(.neg 58),(.pos 65),(.pos 68)]),
   ((.exchange 67 59 2),[(.neg 67),(.neg 59),(.pos 66),(.pos 68)]),
   ((.exchange 67 64 2),[(.neg 67),(.neg 64),(.pos 68),(.pos 69)]),
   ((.exchange 68 12 6),[(.neg 68),(.neg 12),(.pos 48),(.pos 54)]),
   ((.exchange 68 13 6),[(.neg 68),(.neg 13),(.pos 49),(.pos 54)])]

theorem certificates_2_valid : ∀ oc ∈ certificates_2,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_3 : List (Origin 70 197 × List Sat.Literal) :=
  [((.exchange 68 14 6),[(.neg 68),(.neg 14),(.pos 50),(.pos 54)]),
   ((.exchange 68 17 5),[(.neg 68),(.neg 17),(.pos 58),(.pos 60)]),
   ((.exchange 68 18 5),[(.neg 68),(.neg 18),(.pos 59),(.pos 60)]),
   ((.exchange 68 22 5),[(.neg 68),(.neg 22),(.pos 58),(.pos 64)]),
   ((.exchange 68 23 5),[(.neg 68),(.neg 23),(.pos 59),(.pos 64)]),
   ((.exchange 68 24 5),[(.neg 68),(.neg 24),(.pos 60),(.pos 64)]),
   ((.exchange 68 26 3),[(.neg 68),(.neg 26),(.pos 65),(.pos 67)]),
   ((.exchange 68 27 3),[(.neg 68),(.neg 27),(.pos 66),(.pos 67)]),
   ((.exchange 68 31 3),[(.neg 68),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 68 32 3),[(.neg 68),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 68 37 6),[(.neg 68),(.neg 37),(.pos 48),(.pos 50)]),
   ((.exchange 68 38 5),[(.neg 68),(.neg 38),(.pos 59),(.pos 60)]),
   ((.exchange 68 42 6),[(.neg 68),(.neg 42),(.pos 48),(.pos 54)]),
   ((.exchange 68 43 6),[(.neg 68),(.neg 43),(.pos 49),(.pos 54)]),
   ((.exchange 68 44 6),[(.neg 68),(.neg 44),(.pos 50),(.pos 54)]),
   ((.exchange 68 46 6),[(.neg 68),(.neg 46),(.pos 48),(.pos 50)]),
   ((.exchange 68 47 6),[(.neg 68),(.neg 47),(.pos 49),(.pos 50)]),
   ((.exchange 68 52 3),[(.neg 68),(.neg 52),(.pos 66),(.pos 69)]),
   ((.exchange 68 52 6),[(.neg 68),(.neg 52),(.pos 49),(.pos 54)]),
   ((.exchange 68 53 3),[(.neg 68),(.neg 53),(.pos 67),(.pos 69)]),
   ((.exchange 68 53 6),[(.neg 68),(.neg 53),(.pos 50),(.pos 54)]),
   ((.exchange 68 63 3),[(.neg 68),(.neg 63),(.pos 67),(.pos 69)]),
   ((.exchange 68 63 5),[(.neg 68),(.neg 63),(.pos 60),(.pos 64)]),
   ((.exchange 69 10 6),[(.neg 69),(.neg 10),(.pos 51),(.pos 53)]),
   ((.exchange 69 11 6),[(.neg 69),(.neg 11),(.pos 52),(.pos 53)]),
   ((.exchange 69 12 6),[(.neg 69),(.neg 12),(.pos 51),(.pos 54)]),
   ((.exchange 69 13 6),[(.neg 69),(.neg 13),(.pos 52),(.pos 54)]),
   ((.exchange 69 14 6),[(.neg 69),(.neg 14),(.pos 53),(.pos 54)]),
   ((.exchange 69 18 5),[(.neg 69),(.neg 18),(.pos 62),(.pos 63),(.pos 64)]),
   ((.exchange 69 24 5),[(.neg 69),(.neg 24),(.pos 63),(.pos 64)]),
   ((.exchange 69 28 4),[(.neg 69),(.neg 28),(.pos 65),(.pos 68)]),
   ((.exchange 69 29 4),[(.neg 69),(.neg 29),(.pos 66),(.pos 68)]),
   ((.exchange 69 30 4),[(.neg 69),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 69 37 4),[(.neg 69),(.neg 37),(.pos 65),(.pos 67),(.pos 68)]),
   ((.exchange 69 40 5),[(.neg 69),(.neg 40),(.pos 61),(.pos 63)]),
   ((.exchange 69 40 6),[(.neg 69),(.neg 40),(.pos 51),(.pos 53)]),
   ((.exchange 69 41 6),[(.neg 69),(.neg 41),(.pos 52),(.pos 53)]),
   ((.exchange 69 42 6),[(.neg 69),(.neg 42),(.pos 51),(.pos 54)]),
   ((.exchange 69 43 6),[(.neg 69),(.neg 43),(.pos 52),(.pos 54)]),
   ((.exchange 69 48 4),[(.neg 69),(.neg 48),(.pos 65),(.pos 68)]),
   ((.exchange 69 48 6),[(.neg 69),(.neg 48),(.pos 51),(.pos 54)]),
   ((.exchange 69 49 4),[(.neg 69),(.neg 49),(.pos 66),(.pos 68)]),
   ((.exchange 69 49 6),[(.neg 69),(.neg 49),(.pos 52),(.pos 54)]),
   ((.exchange 69 50 4),[(.neg 69),(.neg 50),(.pos 67),(.pos 68)]),
   ((.exchange 69 50 6),[(.neg 69),(.neg 50),(.pos 53),(.pos 54)]),
   ((.exchange 69 56 4),[(.neg 69),(.neg 56),(.pos 65),(.pos 67)]),
   ((.exchange 69 57 4),[(.neg 69),(.neg 57),(.pos 66),(.pos 67)]),
   ((.exchange 69 57 5),[(.neg 69),(.neg 57),(.pos 62),(.pos 63)]),
   ((.exchange 69 60 4),[(.neg 69),(.neg 60),(.pos 67),(.pos 68)]),
   (.newPoint,[(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 0),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 60),(.neg 54),(.neg 53),(.neg 50),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 51),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 61),(.pos 62),(.pos 65),(.pos 66)]),
   ((.excluded 1),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 54),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 50),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 2),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 64)]),
   ((.excluded 3),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57),(.pos 68)]),
   ((.excluded 4),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57),(.pos 69)]),
   ((.excluded 5),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 6),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 50),(.pos 54),(.pos 55),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 68)]),
   ((.excluded 7),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 55),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 8),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 61),(.pos 62),(.pos 68)]),
   ((.excluded 9),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 53),(.pos 55),(.pos 63),(.pos 68)]),
   ((.excluded 10),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 55),(.pos 68)]),
   ((.excluded 11),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 12),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 50),(.pos 51),(.pos 52),(.pos 55),(.pos 60),(.pos 61),(.pos 62)]),
   ((.excluded 13),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 61),(.pos 62),(.pos 67)]),
   ((.excluded 14),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 15),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 53),(.pos 55),(.pos 58),(.pos 59),(.pos 63)]),
   ((.excluded 16),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 58),(.pos 59),(.pos 67)]),
   ((.excluded 17),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 58),(.pos 59),(.pos 69)]),
   ((.excluded 18),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 58),(.pos 59)]),
   ((.excluded 19),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 53),(.pos 55),(.pos 63),(.pos 65),(.pos 66)]),
   ((.excluded 20),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 53),(.pos 55),(.pos 63)]),
   ((.excluded 21),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 50),(.pos 55),(.pos 60),(.pos 65),(.pos 66)]),
   ((.excluded 22),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 50),(.pos 55),(.pos 60),(.pos 69)]),
   ((.excluded 23),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 50),(.pos 55),(.pos 60)]),
   ((.excluded 24),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 55),(.pos 69)]),
   ((.excluded 25),[(.neg 69),(.neg 68),(.neg 67),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 54),(.pos 55),(.pos 64),(.pos 65),(.pos 66)]),
   ((.excluded 26),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 54),(.pos 55),(.pos 64),(.pos 67)]),
   ((.excluded 27),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 54),(.pos 55),(.pos 64)]),
   ((.excluded 28),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 55),(.pos 65),(.pos 66)]),
   ((.excluded 29),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 55),(.pos 67)]),
   ((.excluded 30),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 55)]),
   ((.excluded 31),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 32),[(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 33),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 34),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 51),(.pos 52),(.pos 55),(.pos 60),(.pos 65),(.pos 66)]),
   ((.excluded 35),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 51),(.pos 52),(.pos 55),(.pos 63),(.pos 65),(.pos 66)]),
   ((.excluded 36),[(.neg 69),(.neg 68),(.neg 67),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 51),(.pos 52),(.pos 55),(.pos 64),(.pos 65),(.pos 66)]),
   ((.excluded 37),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 51),(.pos 52),(.pos 55),(.pos 65),(.pos 66)]),
   ((.excluded 38),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 60),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 50),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 61),(.pos 62),(.pos 65),(.pos 66)]),
   ((.excluded 39),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 60),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 61),(.pos 62),(.pos 65),(.pos 66)]),
   ((.excluded 40),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 60),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 61),(.pos 62),(.pos 65),(.pos 66)]),
   ((.excluded 41),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 60),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 61),(.pos 62),(.pos 65),(.pos 66)]),
   ((.excluded 42),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 50),(.pos 55),(.pos 63),(.pos 65),(.pos 66)]),
   ((.excluded 43),[(.neg 69),(.neg 68),(.neg 67),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 50),(.pos 55),(.pos 64),(.pos 65),(.pos 66)]),
   ((.excluded 44),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 50),(.pos 55),(.pos 65),(.pos 66)]),
   ((.excluded 45),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 54),(.pos 55),(.pos 63),(.pos 65),(.pos 66)]),
   ((.excluded 46),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 63),(.pos 65),(.pos 66)]),
   ((.excluded 47),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 54),(.pos 55),(.pos 60),(.pos 65),(.pos 66)]),
   ((.excluded 48),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 54),(.pos 55),(.pos 65),(.pos 66)]),
   ((.excluded 49),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 53),(.pos 55),(.pos 60),(.pos 65),(.pos 66)]),
   ((.excluded 50),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 60),(.pos 65),(.pos 66)]),
   ((.excluded 51),[(.neg 69),(.neg 68),(.neg 67),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 53),(.pos 55),(.pos 64),(.pos 65),(.pos 66)]),
   ((.excluded 52),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 53),(.pos 55),(.pos 65),(.pos 66)]),
   ((.excluded 53),[(.neg 69),(.neg 68),(.neg 67),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 64),(.pos 65),(.pos 66)]),
   ((.excluded 54),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 65),(.pos 66)]),
   ((.excluded 55),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 50),(.pos 53),(.pos 55),(.pos 58),(.pos 59),(.pos 67)]),
   ((.excluded 56),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 50),(.pos 53),(.pos 55),(.pos 61),(.pos 62),(.pos 67)]),
   ((.excluded 57),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 50),(.pos 53),(.pos 55),(.pos 64),(.pos 67)]),
   ((.excluded 58),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 50),(.pos 53),(.pos 55),(.pos 67)]),
   ((.excluded 59),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 60),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 61),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 62),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 63),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 61),(.pos 62),(.pos 67)]),
   ((.excluded 64),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 64),(.pos 67)]),
   ((.excluded 65),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 67)]),
   ((.excluded 66),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 54),(.pos 55),(.pos 61),(.pos 62),(.pos 67)]),
   ((.excluded 67),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 61),(.pos 62),(.pos 67)]),
   ((.excluded 68),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 54),(.pos 55),(.pos 58),(.pos 59),(.pos 67)]),
   ((.excluded 69),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 54),(.pos 55),(.pos 67)]),
   ((.excluded 70),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 58),(.pos 59),(.pos 67)]),
   ((.excluded 71),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 58),(.pos 59),(.pos 67)]),
   ((.excluded 72),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 64),(.pos 67)]),
   ((.excluded 73),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 67)]),
   ((.excluded 74),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 64),(.pos 67)]),
   ((.excluded 75),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 67)]),
   ((.excluded 76),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 77),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 50),(.pos 54),(.pos 55),(.pos 63),(.pos 68)])]

theorem certificates_3_valid : ∀ oc ∈ certificates_3,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_4 : List (Origin 70 197 × List Sat.Literal) :=
  [((.excluded 78),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 63)]),
   ((.excluded 79),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 53),(.neg 52),(.neg 51),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 50),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 68)]),
   ((.excluded 80),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 50),(.pos 54),(.pos 55),(.pos 61),(.pos 62),(.pos 68)]),
   ((.excluded 81),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 50),(.pos 54),(.pos 55),(.pos 68)]),
   ((.excluded 82),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 53),(.pos 55),(.pos 60),(.pos 61),(.pos 62)]),
   ((.excluded 83),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 53),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 84),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 60),(.pos 61),(.pos 62)]),
   ((.excluded 85),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 86),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 53),(.pos 55),(.pos 60)]),
   ((.excluded 87),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 60),(.pos 69)]),
   ((.excluded 88),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 60)]),
   ((.excluded 89),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 56),(.pos 57),(.pos 69)]),
   ((.excluded 90),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 69)]),
   ((.excluded 91),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 64)]),
   ((.excluded 92),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 53),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 93),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 56),(.pos 57),(.pos 64)]),
   ((.excluded 94),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 95),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 53),(.pos 55),(.pos 64)]),
   ((.excluded 96),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 53),(.pos 55)]),
   ((.excluded 97),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 64)]),
   ((.excluded 98),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 48),(.pos 49),(.pos 55)]),
   ((.excluded 99),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 100),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 50),(.pos 55),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 101),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 102),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 69)]),
   ((.excluded 103),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 58),(.pos 59),(.pos 69)]),
   ((.excluded 104),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 69)]),
   ((.excluded 105),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 69)]),
   ((.excluded 106),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 50),(.pos 55),(.pos 56),(.pos 57),(.pos 69)]),
   ((.excluded 107),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 69)]),
   ((.excluded 108),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 50),(.pos 55),(.pos 58),(.pos 59),(.pos 69)]),
   ((.excluded 109),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 50),(.pos 55),(.pos 69)]),
   ((.excluded 110),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 58),(.pos 59),(.pos 69)]),
   ((.excluded 111),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 58),(.pos 59),(.pos 69)]),
   ((.excluded 112),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 60),(.pos 69)]),
   ((.excluded 113),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 69)]),
   ((.excluded 114),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 60),(.pos 69)]),
   ((.excluded 115),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 69)]),
   ((.excluded 116),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 68)]),
   ((.excluded 117),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 68)]),
   ((.excluded 118),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 53),(.pos 55),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 68)]),
   ((.excluded 119),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 68)]),
   ((.excluded 120),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 60)]),
   ((.excluded 121),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 53),(.pos 55),(.pos 60),(.pos 61),(.pos 62)]),
   ((.excluded 122),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 53),(.pos 55),(.pos 60)]),
   ((.excluded 123),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 54),(.pos 55),(.pos 60),(.pos 61),(.pos 62)]),
   ((.excluded 124),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 60),(.pos 61),(.pos 62)]),
   ((.excluded 125),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 54),(.pos 55),(.pos 60)]),
   ((.excluded 126),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 60)]),
   ((.excluded 127),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 54),(.pos 55),(.pos 60),(.pos 61),(.pos 62)]),
   ((.excluded 128),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 60),(.pos 61),(.pos 62)]),
   ((.excluded 129),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 54),(.pos 55),(.pos 60)]),
   ((.excluded 130),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 60)]),
   ((.excluded 131),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 50),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 132),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 53),(.pos 55),(.pos 61),(.pos 62),(.pos 68)]),
   ((.excluded 133),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 53),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 134),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 54),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 135),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 61),(.pos 62),(.pos 68)]),
   ((.excluded 136),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 137),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 54),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 138),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 61),(.pos 62),(.pos 68)]),
   ((.excluded 139),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 140),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 53),(.pos 55),(.pos 58),(.pos 59)]),
   ((.excluded 141),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 64)]),
   ((.excluded 142),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 68)]),
   ((.excluded 143),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 53),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 144),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 53),(.pos 55),(.pos 64)]),
   ((.excluded 145),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 53),(.pos 55),(.pos 68)]),
   ((.excluded 146),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 53),(.pos 55)]),
   ((.excluded 147),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 64)]),
   ((.excluded 148),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 63),(.pos 68)]),
   ((.excluded 149),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 68)]),
   ((.excluded 150),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 54),(.pos 55),(.pos 58),(.pos 59),(.pos 63)]),
   ((.excluded 151),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 54),(.pos 55),(.pos 58),(.pos 59)]),
   ((.excluded 152),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 58),(.pos 59),(.pos 63)]),
   ((.excluded 153),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 58),(.pos 59)]),
   ((.excluded 154),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 54),(.pos 55),(.pos 63)]),
   ((.excluded 155),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 54),(.pos 55)]),
   ((.excluded 156),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 63)]),
   ((.excluded 157),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 55)]),
   ((.excluded 158),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 54),(.pos 55),(.pos 58),(.pos 59),(.pos 63)]),
   ((.excluded 159),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 54),(.pos 55),(.pos 58),(.pos 59)]),
   ((.excluded 160),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 50),(.pos 51),(.pos 52),(.pos 55),(.pos 58),(.pos 59),(.pos 63)]),
   ((.excluded 161),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 50),(.pos 51),(.pos 52),(.pos 55),(.pos 58),(.pos 59)]),
   ((.excluded 162),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 58),(.pos 59),(.pos 63)]),
   ((.excluded 163),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 58),(.pos 59)]),
   ((.excluded 164),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 50),(.pos 55),(.pos 58),(.pos 59),(.pos 63)]),
   ((.excluded 165),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 50),(.pos 55),(.pos 58),(.pos 59)]),
   ((.excluded 166),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 58),(.pos 59),(.pos 63)]),
   ((.excluded 167),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 58),(.pos 59)]),
   ((.excluded 168),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 54),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 169),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 54),(.pos 55),(.pos 63)]),
   ((.excluded 170),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 54),(.pos 55)]),
   ((.excluded 171),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 50),(.pos 51),(.pos 52),(.pos 55),(.pos 63)]),
   ((.excluded 172),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 63),(.pos 68)]),
   ((.excluded 173),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 63)]),
   ((.excluded 174),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 50),(.pos 55),(.pos 63)]),
   ((.excluded 175),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 63),(.pos 68)]),
   ((.excluded 176),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 63)]),
   ((.excluded 177),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 68)]),
   ((.excluded 178),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 68)]),
   ((.excluded 179),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 68)]),
   ((.excluded 180),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 68)]),
   ((.excluded 181),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 50),(.pos 51),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 64)]),
   ((.excluded 182),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 50),(.pos 51),(.pos 52),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 183),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 64)]),
   ((.excluded 184),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 185),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 50),(.pos 51),(.pos 52),(.pos 55),(.pos 64)]),
   ((.excluded 186),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 50),(.pos 51),(.pos 52),(.pos 55)]),
   ((.excluded 187),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 64)]),
   ((.excluded 188),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 55)]),
   ((.excluded 189),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 50),(.pos 55),(.pos 56),(.pos 57),(.pos 64)]),
   ((.excluded 190),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 50),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 191),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 64)]),
   ((.excluded 192),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 193),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 50),(.pos 55),(.pos 64)]),
   ((.excluded 194),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 50),(.pos 55)]),
   ((.excluded 195),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 64)]),
   ((.excluded 196),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55)])]

theorem certificates_4_valid : ∀ oc ∈ certificates_4,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



theorem witness_0 : ∀ j : Fin 128,
    let w : Fin 197 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 128,
      let w : Fin 197 := ⟨0 + j.val,by omega⟩
      target w < MatroidCatalogue.count 8 4 ∧
        Papers.RationalityTen.MatroidChecked.FastSemanticChecks.RawWitness 8 (N7R4.familyMasks.get 44)
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



theorem witness_1 : ∀ j : Fin 69,
    let w : Fin 197 := ⟨128 + j.val,by omega⟩
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 69,
      let w : Fin 197 := ⟨128 + j.val,by omega⟩
      target w < MatroidCatalogue.count 8 4 ∧
        Papers.RationalityTen.MatroidChecked.FastSemanticChecks.RawWitness 8 (N7R4.familyMasks.get 44)
        (fun i : Fin 70 => N8R4.gridMasks.get i.val) newIndex (models w)
        (N8R4.familyMasks.get (target w)) (permutation w) := by
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
  exact ⟨hj.1,Papers.RationalityTen.MatroidChecked.FastSemanticChecks.rawWitness_sound 8 _ _ _ _ _ _ hj.2⟩


end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C44

/- Source: MatroidCatalogue/Cases/N8R4C44Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C44

noncomputable def certificates : List (Origin 70 197 × List Sat.Literal) :=
  certificates_0 ++ certificates_1 ++ certificates_2 ++ certificates_3 ++ certificates_4

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  intro oc hoc
  simp only [certificates,List.mem_append,or_assoc] at hoc
  rcases hoc with h0 | h1 | h2 | h3 | h4
  · exact certificates_0_valid oc h0
  · exact certificates_1_valid oc h1
  · exact certificates_2_valid oc h2
  · exact certificates_3_valid oc h3
  · exact certificates_4_valid oc h4

theorem models_valid : ∀ w : Fin 197,
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
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

theorem coverage (M : BasisFamily (groundPrefix 8) 4)
    (hold : M.bases.filter ((7 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 8 4, IsomorphicWithin 8 M.bases B := by
  apply extension_covered_of_certificate (n:=7) (r:=4) (by decide)
    catalogue old U newIndex models certificates
    N8R4.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C44.formula []
    exact Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C44.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 8 4 (target w),family_mem 8 4 (target w) hw.1,?_⟩
    exact validWitness_sound 8 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C44


end
end
end BundlePart0

section BundlePart1
/- Source: MatroidChecked/SemanticChunks/Cases06Part02.lean -/




@[expose] public section
noncomputable section

/- Source: MatroidCatalogue/Cases/N8R4C45Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C45

abbrev U := N8R4.grid
noncomputable def old : Finset (Finset (Fin 8)) := N7R4.family 45
noncomputable def newIndexTree : Table ℕ := (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf 35) (.leaf 36)) (.node 3 (.leaf 37) (.leaf 38))) (.node 6 (.node 5 (.leaf 39) (.leaf 40)) (.node 7 (.leaf 41) (.leaf 42)))) (.node 12 (.node 10 (.node 9 (.leaf 43) (.leaf 44)) (.node 11 (.leaf 45) (.leaf 46))) (.node 14 (.node 13 (.leaf 47) (.leaf 48)) (.node 15 (.leaf 49) (.node 16 (.leaf 50) (.leaf 51)))))) (.node 26 (.node 21 (.node 19 (.node 18 (.leaf 52) (.leaf 53)) (.node 20 (.leaf 54) (.leaf 55))) (.node 23 (.node 22 (.leaf 56) (.leaf 57)) (.node 24 (.leaf 58) (.node 25 (.leaf 59) (.leaf 60))))) (.node 30 (.node 28 (.node 27 (.leaf 61) (.leaf 62)) (.node 29 (.leaf 63) (.leaf 64))) (.node 32 (.node 31 (.leaf 65) (.leaf 66)) (.node 33 (.leaf 67) (.node 34 (.leaf 68) (.leaf 69)))))))
noncomputable def newIndex (i : Fin 35) : Fin 70 := Fin.ofNat 70 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 33 (.node 16 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (13690229056,117,3140368)) (.leaf (13691038368,123,3140354))) (.node 3 (.leaf (850912,123,2353946)) (.leaf (13691059168,147,7072520)))) (.node 6 (.node 5 (.leaf (29729375504,123,3663394)) (.leaf (25165960272,123,3662050))) (.node 7 (.leaf (34292782416,147,7857248)) (.leaf (25166802864,182,11528328))))) (.node 12 (.node 10 (.node 9 (.leaf (34293608368,189,11528328)) (.leaf (25166807024,189,11264736))) (.node 11 (.leaf (29730193136,182,11527432)) (.leaf (34293595888,189,11527432)))) (.node 14 (.node 13 (.leaf (29730209776,189,11265632)) (.leaf (34293612528,200,11266248))) (.node 15 (.leaf (12949934091,123,3510178)) (.leaf (870318411,123,3424162)))))) (.node 24 (.node 20 (.node 18 (.node 17 (.leaf (13755240779,147,7675808)) (.leaf (871168683,182,11415432))) (.node 19 (.leaf (13756070571,189,11415432)) (.leaf (871169003,189,11059104)))) (.node 22 (.node 21 (.leaf (12950744043,182,11358088)) (.leaf (13756050411,189,11358088))) (.node 23 (.leaf (12950764523,189,11116448)) (.leaf (13756070891,200,11157384))))) (.node 28 (.node 26 (.node 25 (.leaf (25499407643,182,12461680)) (.leaf (34089358619,189,12461680))) (.node 27 (.leaf (25767843163,189,12403440)) (.leaf (29525951579,182,12404336)))) (.node 30 (.node 29 (.leaf (33820922971,189,12460784)) (.leaf (30062822747,189,12404336))) (.node 31 (.leaf (34357794139,200,12465264)) (.node 32 (.leaf (25768689595,312,16405704)) (.leaf (29526769595,313,16434824)))))))) (.node 49 (.node 41 (.node 37 (.node 35 (.node 34 (.leaf (33821736891,314,16430344)) (.leaf (30063640507,314,16373896))) (.node 36 (.leaf (34358607803,315,16434824)) (.leaf (29526785979,314,15608936)))) (.node 39 (.node 38 (.leaf (33821753275,315,15670032)) (.leaf (30063656891,315,15649872))) (.node 40 (.leaf (34358624187,316,16431240)) (.leaf (34090172411,312,16434824))))) (.node 45 (.node 43 (.node 42 (.leaf (29526769659,314,15549352)) (.leaf (33821736955,315,15618960))) (.node 44 (.leaf (30063640571,315,15526224)) (.leaf (34358607867,316,16373000)))) (.node 47 (.node 46 (.leaf (33821749243,312,16434376)) (.leaf (29526786043,315,15095472))) (.node 48 (.leaf (33821753339,316,15606696)) (.leaf (30063656699,312,16406152)))))) (.node 57 (.node 53 (.node 51 (.node 50 (.leaf (30063656955,316,15551592)) (.leaf (25500249851,313,16406152))) (.node 52 (.leaf (34090184443,314,16431240)) (.leaf (25768685307,314,16373000)))) (.node 55 (.node 54 (.leaf (34358619899,315,16406152)) (.leaf (25500253947,314,15606696))) (.node 56 (.leaf (34090188539,315,15669584)) (.leaf (25768689403,315,15647632))))) (.node 61 (.node 59 (.node 58 (.leaf (34358623995,316,16430344)) (.leaf (25500250107,314,15551592))) (.node 60 (.leaf (34090184699,315,15621200)) (.leaf (25768685563,315,15526672)))) (.node 63 (.node 62 (.leaf (34358620155,316,16373896)) (.leaf (25500254203,315,15124144))) (.node 64 (.leaf (34090188795,316,15608936)) (.node 65 (.leaf (25768689659,316,15549352)) (.leaf (34358624251,317,16434824)))))))))

noncomputable def models (i : Fin 66) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 66) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 66) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 70, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (7 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 70, (7 : Fin 8) ∈ U i → ∃ j : Fin 35, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C45

/- Source: MatroidCatalogue/Cases/N8R4C45Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C45


noncomputable def certificates_0 : List (Origin 70 66 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.pos 1)]),
   ((.fixed 2),[(.pos 2)]),
   ((.fixed 3),[(.neg 3)]),
   ((.fixed 4),[(.pos 4)]),
   ((.fixed 5),[(.pos 5)]),
   ((.fixed 6),[(.pos 6)]),
   ((.fixed 7),[(.neg 7)]),
   ((.fixed 8),[(.pos 8)]),
   ((.fixed 9),[(.neg 9)]),
   ((.fixed 10),[(.neg 10)]),
   ((.fixed 11),[(.pos 11)]),
   ((.fixed 12),[(.neg 12)]),
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
   ((.exchange 1 36 4),[(.neg 36),(.neg 1),(.pos 0),(.pos 35)]),
   ((.exchange 1 38 4),[(.neg 38),(.neg 1),(.pos 0),(.pos 35)]),
   ((.exchange 1 42 1),[(.neg 42),(.neg 1),(.pos 3),(.pos 40)]),
   ((.exchange 1 45 2),[(.neg 45),(.neg 1),(.pos 9),(.pos 39)]),
   ((.exchange 1 46 1),[(.neg 46),(.neg 1),(.pos 10),(.pos 40)]),
   ((.exchange 1 48 1),[(.neg 48),(.neg 1),(.pos 3),(.pos 10),(.pos 40)]),
   ((.exchange 1 52 2),[(.neg 52),(.neg 1),(.pos 9),(.pos 39)]),
   ((.exchange 1 56 4),[(.neg 56),(.neg 1),(.pos 15),(.pos 35)]),
   ((.exchange 1 57 4),[(.neg 57),(.neg 1),(.pos 15),(.pos 35)]),
   ((.exchange 1 58 4),[(.neg 58),(.neg 1),(.pos 0),(.pos 15),(.pos 35)]),
   ((.exchange 1 59 4),[(.neg 59),(.neg 1),(.pos 0),(.pos 15),(.pos 35)]),
   ((.exchange 1 60 4),[(.neg 60),(.neg 1),(.pos 0),(.pos 15),(.pos 35)]),
   ((.exchange 1 61 2),[(.neg 61),(.neg 1),(.pos 19),(.pos 39)]),
   ((.exchange 1 62 2),[(.neg 62),(.neg 1),(.pos 19),(.pos 39)]),
   ((.exchange 1 65 2),[(.neg 65),(.neg 1),(.pos 9),(.pos 19),(.pos 39)]),
   ((.exchange 1 66 2),[(.neg 66),(.neg 1),(.pos 9),(.pos 19),(.pos 39)]),
   ((.exchange 1 69 2),[(.neg 69),(.neg 1),(.pos 9),(.pos 19),(.pos 39)]),
   ((.exchange 2 35 4),[(.neg 35),(.neg 2),(.pos 0),(.pos 36)]),
   ((.exchange 2 40 1),[(.neg 40),(.neg 2),(.pos 3),(.pos 42)]),
   ((.exchange 2 44 1),[(.neg 44),(.neg 2),(.pos 3),(.pos 42)]),
   ((.exchange 2 46 1),[(.neg 46),(.neg 2),(.pos 3),(.pos 12),(.pos 42)]),
   ((.exchange 2 48 1),[(.neg 48),(.neg 2),(.pos 12),(.pos 42)]),
   ((.exchange 2 50 1),[(.neg 50),(.neg 2),(.pos 3),(.pos 12),(.pos 42)]),
   ((.exchange 2 53 1),[(.neg 53),(.neg 2),(.pos 3),(.pos 12),(.pos 42)]),
   ((.exchange 2 54 1),[(.neg 54),(.neg 2),(.pos 12),(.pos 42)]),
   ((.exchange 2 56 4),[(.neg 56),(.neg 2),(.pos 0),(.pos 16),(.pos 36)]),
   ((.exchange 2 57 4),[(.neg 57),(.neg 2),(.pos 0),(.pos 16),(.pos 36)]),
   ((.exchange 2 60 4),[(.neg 60),(.neg 2),(.pos 0),(.pos 16),(.pos 36)]),
   ((.exchange 4 35 4),[(.neg 35),(.neg 4),(.pos 0),(.pos 38)]),
   ((.exchange 4 36 4),[(.neg 36),(.neg 4),(.pos 0),(.pos 38)]),
   ((.exchange 4 42 1),[(.neg 42),(.neg 4),(.pos 3),(.pos 44)]),
   ((.exchange 4 46 1),[(.neg 46),(.neg 4),(.pos 3),(.pos 14),(.pos 44)]),
   ((.exchange 4 48 1),[(.neg 48),(.neg 4),(.pos 3),(.pos 14),(.pos 44)]),
   ((.exchange 4 56 4),[(.neg 56),(.neg 4),(.pos 0),(.pos 18),(.pos 38)]),
   ((.exchange 4 58 4),[(.neg 58),(.neg 4),(.pos 0),(.pos 18),(.pos 38)]),
   ((.exchange 4 59 4),[(.neg 59),(.neg 4),(.pos 18),(.pos 38)]),
   ((.exchange 4 60 4),[(.neg 60),(.neg 4),(.pos 18),(.pos 38)]),
   ((.exchange 5 39 2),[(.neg 39),(.neg 5),(.pos 9),(.pos 45)]),
   ((.exchange 5 40 1),[(.neg 40),(.neg 5),(.pos 10),(.pos 46)]),
   ((.exchange 5 42 1),[(.neg 42),(.neg 5),(.pos 7),(.pos 10),(.pos 46)]),
   ((.exchange 5 44 1),[(.neg 44),(.neg 5),(.pos 7),(.pos 10),(.pos 46)]),
   ((.exchange 5 48 1),[(.neg 48),(.neg 5),(.pos 7),(.pos 46)]),
   ((.exchange 5 50 1),[(.neg 50),(.neg 5),(.pos 7),(.pos 46)]),
   ((.exchange 5 52 2),[(.neg 52),(.neg 5),(.pos 9),(.pos 45)]),
   ((.exchange 5 53 1),[(.neg 53),(.neg 5),(.pos 10),(.pos 46)]),
   ((.exchange 5 54 1),[(.neg 54),(.neg 5),(.pos 7),(.pos 10),(.pos 46)]),
   ((.exchange 5 69 2),[(.neg 69),(.neg 5),(.pos 9),(.pos 25),(.pos 45)]),
   ((.exchange 6 40 1),[(.neg 40),(.neg 6),(.pos 7),(.pos 12),(.pos 48)]),
   ((.exchange 6 42 1),[(.neg 42),(.neg 6),(.pos 12),(.pos 48)]),
   ((.exchange 6 44 1),[(.neg 44),(.neg 6),(.pos 7),(.pos 12),(.pos 48)]),
   ((.exchange 6 46 1),[(.neg 46),(.neg 6),(.pos 7),(.pos 48)]),
   ((.exchange 6 50 1),[(.neg 50),(.neg 6),(.pos 7),(.pos 48)]),
   ((.exchange 6 53 1),[(.neg 53),(.neg 6),(.pos 7),(.pos 12),(.pos 48)]),
   ((.exchange 6 54 1),[(.neg 54),(.neg 6),(.pos 12),(.pos 48)]),
   ((.exchange 8 42 1),[(.neg 42),(.neg 8),(.pos 7),(.pos 14),(.pos 50)]),
   ((.exchange 8 46 1),[(.neg 46),(.neg 8),(.pos 7),(.pos 50)]),
   ((.exchange 8 48 1),[(.neg 48),(.neg 8),(.pos 7),(.pos 50)]),
   ((.exchange 11 39 2),[(.neg 39),(.neg 11),(.pos 9),(.pos 52)]),
   ((.exchange 11 42 1),[(.neg 42),(.neg 11),(.pos 10),(.pos 14),(.pos 53)]),
   ((.exchange 11 46 1),[(.neg 46),(.neg 11),(.pos 10),(.pos 53)]),
   ((.exchange 11 48 1),[(.neg 48),(.neg 11),(.pos 10),(.pos 14),(.pos 53)]),
   ((.exchange 11 69 2),[(.neg 69),(.neg 11),(.pos 32),(.pos 52)]),
   ((.exchange 13 42 1),[(.neg 42),(.neg 13),(.pos 12),(.pos 54)]),
   ((.exchange 13 46 1),[(.neg 46),(.neg 13),(.pos 12),(.pos 14),(.pos 54)]),
   ((.exchange 13 48 1),[(.neg 48),(.neg 13),(.pos 12),(.pos 54)]),
   ((.exchange 20 35 4),[(.neg 35),(.neg 20),(.pos 15),(.pos 56)]),
   ((.exchange 20 36 4),[(.neg 36),(.neg 20),(.pos 15),(.pos 17),(.pos 56)]),
   ((.exchange 20 38 4),[(.neg 38),(.neg 20),(.pos 15),(.pos 17),(.pos 56)]),
   ((.exchange 20 39 2),[(.neg 39),(.neg 20),(.pos 19),(.pos 61)]),
   ((.exchange 20 52 2),[(.neg 52),(.neg 20),(.pos 19),(.pos 31),(.pos 61)]),
   ((.exchange 20 57 4),[(.neg 57),(.neg 20),(.pos 15),(.pos 56)]),
   ((.exchange 20 58 4),[(.neg 58),(.neg 20),(.pos 17),(.pos 56)]),
   ((.exchange 20 59 4),[(.neg 59),(.neg 20),(.pos 15),(.pos 17),(.pos 56)]),
   ((.exchange 20 60 4),[(.neg 60),(.neg 20),(.pos 17),(.pos 56)]),
   ((.exchange 20 69 2),[(.neg 69),(.neg 20),(.pos 31),(.pos 61)]),
   ((.exchange 21 35 4),[(.neg 35),(.neg 21),(.pos 15),(.pos 57)]),
   ((.exchange 21 39 2),[(.neg 39),(.neg 21),(.pos 19),(.pos 62)]),
   ((.exchange 21 56 4),[(.neg 56),(.neg 21),(.pos 15),(.pos 57)]),
   ((.exchange 21 59 4),[(.neg 59),(.neg 21),(.pos 18),(.pos 57)]),
   ((.exchange 21 60 4),[(.neg 60),(.neg 21),(.pos 18),(.pos 57)]),
   ((.exchange 21 69 2),[(.neg 69),(.neg 21),(.pos 32),(.pos 62)]),
   ((.exchange 22 35 4),[(.neg 35),(.neg 22),(.pos 16),(.pos 17),(.pos 58)]),
   ((.exchange 22 56 4),[(.neg 56),(.neg 22),(.pos 17),(.pos 58)]),
   ((.exchange 22 57 4),[(.neg 57),(.neg 22),(.pos 16),(.pos 17),(.pos 58)]),
   ((.exchange 22 59 4),[(.neg 59),(.neg 22),(.pos 16),(.pos 58)]),
   ((.exchange 22 60 4),[(.neg 60),(.neg 22),(.pos 17),(.pos 58)]),
   ((.exchange 23 35 4),[(.neg 35),(.neg 23),(.pos 16),(.pos 18),(.pos 59)]),
   ((.exchange 23 56 4),[(.neg 56),(.neg 23),(.pos 16),(.pos 18),(.pos 59)]),
   ((.exchange 23 57 4),[(.neg 57),(.neg 23),(.pos 18),(.pos 59)]),
   ((.exchange 23 60 4),[(.neg 60),(.neg 23),(.pos 18),(.pos 59)]),
   ((.exchange 24 35 4),[(.neg 35),(.neg 24),(.pos 17),(.pos 18),(.pos 60)]),
   ((.exchange 24 36 4),[(.neg 36),(.neg 24),(.pos 17),(.pos 18),(.pos 60)]),
   ((.exchange 24 38 4),[(.neg 38),(.neg 24),(.pos 18),(.pos 60)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_1 : List (Origin 70 66 × List Sat.Literal) :=
  [((.exchange 24 56 4),[(.neg 56),(.neg 24),(.pos 17),(.pos 60)]),
   ((.exchange 24 57 4),[(.neg 57),(.neg 24),(.pos 18),(.pos 60)]),
   ((.exchange 24 58 4),[(.neg 58),(.neg 24),(.pos 17),(.pos 60)]),
   ((.exchange 24 59 4),[(.neg 59),(.neg 24),(.pos 18),(.pos 60)]),
   ((.exchange 26 39 2),[(.neg 39),(.neg 26),(.pos 25),(.pos 31),(.pos 65)]),
   ((.exchange 26 52 2),[(.neg 52),(.neg 26),(.pos 25),(.pos 31),(.pos 65)]),
   ((.exchange 26 69 2),[(.neg 69),(.neg 26),(.pos 31),(.pos 65)]),
   ((.exchange 27 39 2),[(.neg 39),(.neg 27),(.pos 25),(.pos 32),(.pos 66)]),
   ((.exchange 27 45 2),[(.neg 45),(.neg 27),(.pos 25),(.pos 66)]),
   ((.exchange 27 52 2),[(.neg 52),(.neg 27),(.pos 32),(.pos 66)]),
   ((.exchange 27 61 2),[(.neg 61),(.neg 27),(.pos 25),(.pos 32),(.pos 66)]),
   ((.exchange 27 62 2),[(.neg 62),(.neg 27),(.pos 32),(.pos 66)]),
   ((.exchange 27 69 2),[(.neg 69),(.neg 27),(.pos 32),(.pos 66)]),
   ((.exchange 33 39 2),[(.neg 39),(.neg 33),(.pos 31),(.pos 32),(.pos 69)]),
   ((.exchange 33 45 2),[(.neg 45),(.neg 33),(.pos 31),(.pos 32),(.pos 69)]),
   ((.exchange 33 52 2),[(.neg 52),(.neg 33),(.pos 32),(.pos 69)]),
   ((.exchange 33 61 2),[(.neg 61),(.neg 33),(.pos 31),(.pos 69)]),
   ((.exchange 33 62 2),[(.neg 62),(.neg 33),(.pos 32),(.pos 69)]),
   ((.exchange 33 65 2),[(.neg 65),(.neg 33),(.pos 31),(.pos 69)]),
   ((.exchange 33 66 2),[(.neg 66),(.neg 33),(.pos 32),(.pos 69)]),
   ((.exchange 35 11 0),[(.neg 35),(.neg 11),(.pos 41),(.pos 47)]),
   ((.exchange 35 53 0),[(.neg 53),(.neg 35),(.pos 41),(.pos 47)]),
   ((.exchange 37 1 7),[(.neg 37),(.neg 1),(.pos 0),(.pos 3)]),
   ((.exchange 38 53 3),[(.neg 53),(.neg 38),(.pos 41),(.pos 47)]),
   ((.exchange 39 4 0),[(.neg 39),(.neg 4),(.pos 41),(.pos 43)]),
   ((.exchange 40 21 0),[(.neg 40),(.neg 21),(.pos 41),(.pos 63)]),
   ((.exchange 41 2 2),[(.neg 41),(.neg 2),(.pos 39),(.pos 43)]),
   ((.exchange 41 5 4),[(.neg 41),(.neg 5),(.pos 35),(.pos 47)]),
   ((.exchange 41 8 4),[(.neg 41),(.neg 8),(.pos 38),(.pos 47)]),
   ((.exchange 41 13 2),[(.neg 41),(.neg 13),(.pos 43),(.pos 52)]),
   ((.exchange 41 20 1),[(.neg 41),(.neg 20),(.pos 40),(.pos 63)]),
   ((.exchange 41 23 2),[(.neg 41),(.neg 23),(.pos 43),(.pos 62)]),
   ((.exchange 41 27 4),[(.neg 41),(.neg 27),(.pos 47),(.pos 57)]),
   ((.exchange 41 36 2),[(.neg 41),(.neg 36),(.pos 39),(.pos 43)]),
   ((.exchange 41 65 4),[(.neg 65),(.neg 41),(.pos 35),(.pos 47),(.pos 57)]),
   ((.exchange 42 23 0),[(.neg 42),(.neg 23),(.pos 43),(.pos 64)]),
   ((.exchange 42 62 0),[(.neg 62),(.neg 42),(.pos 43),(.pos 64)]),
   ((.exchange 43 1 3),[(.neg 43),(.neg 1),(.pos 39),(.pos 41)]),
   ((.exchange 43 20 1),[(.neg 43),(.neg 20),(.pos 42),(.pos 44),(.pos 64)]),
   ((.exchange 43 29 4),[(.neg 43),(.neg 29),(.pos 49),(.pos 59)]),
   ((.exchange 43 45 4),[(.neg 45),(.neg 43),(.pos 36),(.pos 49)]),
   ((.exchange 43 48 4),[(.neg 48),(.neg 43),(.pos 36),(.pos 49)]),
   ((.exchange 43 65 1),[(.neg 65),(.neg 43),(.pos 42),(.pos 54),(.pos 64)]),
   ((.exchange 43 67 1),[(.neg 67),(.neg 43),(.pos 44),(.pos 54),(.pos 64)]),
   ((.exchange 45 8 0),[(.neg 45),(.neg 8),(.pos 47),(.pos 49)]),
   ((.exchange 45 38 0),[(.neg 45),(.neg 38),(.pos 47),(.pos 49)]),
   ((.exchange 46 27 0),[(.neg 46),(.neg 27),(.pos 47),(.pos 67)]),
   ((.exchange 47 1 5),[(.neg 47),(.neg 1),(.pos 35),(.pos 41)]),
   ((.exchange 47 2 2),[(.neg 47),(.neg 2),(.pos 45),(.pos 49),(.pos 52)]),
   ((.exchange 47 13 2),[(.neg 47),(.neg 13),(.pos 49),(.pos 52)]),
   ((.exchange 47 26 1),[(.neg 47),(.neg 26),(.pos 46),(.pos 67)]),
   ((.exchange 47 29 2),[(.neg 47),(.neg 29),(.pos 49),(.pos 66)]),
   ((.exchange 47 30 1),[(.neg 47),(.neg 30),(.pos 50),(.pos 67)]),
   ((.exchange 47 33 1),[(.neg 47),(.neg 33),(.pos 53),(.pos 67)]),
   ((.exchange 47 44 5),[(.neg 47),(.neg 44),(.pos 38),(.pos 41)]),
   ((.exchange 47 63 5),[(.neg 63),(.neg 47),(.pos 41),(.pos 57)]),
   ((.exchange 48 8 0),[(.neg 48),(.neg 8),(.pos 49),(.pos 50)]),
   ((.exchange 48 59 0),[(.neg 59),(.neg 48),(.pos 49),(.pos 68)]),
   ((.exchange 49 1 3),[(.neg 49),(.neg 1),(.pos 45),(.pos 47),(.pos 52)]),
   ((.exchange 49 4 5),[(.neg 49),(.neg 4),(.pos 38),(.pos 43)]),
   ((.exchange 49 5 3),[(.neg 49),(.neg 5),(.pos 45),(.pos 47)]),
   ((.exchange 49 11 3),[(.neg 49),(.neg 11),(.pos 47),(.pos 52)]),
   ((.exchange 49 20 1),[(.neg 49),(.neg 20),(.pos 48),(.pos 50),(.pos 54),(.pos 68)]),
   ((.exchange 49 28 1),[(.neg 49),(.neg 28),(.pos 48),(.pos 68)]),
   ((.exchange 49 34 1),[(.neg 49),(.neg 34),(.pos 54),(.pos 68)]),
   ((.exchange 49 39 5),[(.neg 49),(.neg 39),(.pos 36),(.pos 43)]),
   ((.exchange 49 42 5),[(.neg 49),(.neg 42),(.pos 36),(.pos 43)]),
   ((.exchange 49 57 3),[(.neg 57),(.neg 49),(.pos 47),(.pos 66)]),
   ((.exchange 49 62 5),[(.neg 62),(.neg 49),(.pos 43),(.pos 59)]),
   ((.exchange 50 27 3),[(.neg 50),(.neg 27),(.pos 47),(.pos 67)]),
   ((.exchange 50 57 3),[(.neg 57),(.neg 50),(.pos 47),(.pos 67)]),
   ((.exchange 51 1 7),[(.neg 51),(.neg 1),(.pos 9),(.pos 10)]),
   ((.exchange 53 27 4),[(.neg 53),(.neg 27),(.pos 47),(.pos 67)]),
   ((.exchange 54 8 4),[(.neg 54),(.neg 8),(.pos 49),(.pos 50)]),
   ((.exchange 54 59 4),[(.neg 59),(.neg 54),(.pos 49),(.pos 68)]),
   ((.exchange 55 1 7),[(.neg 55),(.neg 1),(.pos 15),(.pos 19)]),
   ((.exchange 56 33 0),[(.neg 56),(.neg 33),(.pos 63),(.pos 67)]),
   ((.exchange 56 53 0),[(.neg 56),(.neg 53),(.pos 63),(.pos 67)]),
   ((.exchange 56 69 0),[(.neg 69),(.neg 56),(.pos 63),(.pos 67)]),
   ((.exchange 57 33 1),[(.neg 57),(.neg 33),(.pos 63),(.pos 67)]),
   ((.exchange 57 53 6),[(.neg 57),(.neg 53),(.pos 41),(.pos 47)]),
   ((.exchange 58 34 0),[(.neg 58),(.neg 34),(.pos 64),(.pos 68)]),
   ((.exchange 58 54 0),[(.neg 58),(.neg 54),(.pos 64),(.pos 68)]),
   ((.exchange 59 13 6),[(.neg 59),(.neg 13),(.pos 43),(.pos 49)]),
   ((.exchange 60 54 2),[(.neg 60),(.neg 54),(.pos 64),(.pos 68)]),
   ((.exchange 60 69 2),[(.neg 69),(.neg 60),(.pos 64),(.pos 68)]),
   ((.exchange 61 24 0),[(.neg 61),(.neg 24),(.pos 63),(.pos 64)]),
   ((.exchange 63 6 6),[(.neg 63),(.neg 6),(.pos 40),(.pos 41),(.pos 44),(.pos 53)]),
   ((.exchange 63 22 2),[(.neg 63),(.neg 22),(.pos 61),(.pos 64)]),
   ((.exchange 63 26 4),[(.neg 63),(.neg 26),(.pos 56),(.pos 67)]),
   ((.exchange 63 30 4),[(.neg 63),(.neg 30),(.pos 60),(.pos 67)]),
   ((.exchange 63 34 2),[(.neg 63),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 63 47 4),[(.neg 63),(.neg 47),(.pos 57),(.pos 67)]),
   ((.exchange 63 49 2),[(.neg 63),(.neg 49),(.pos 62),(.pos 64),(.pos 69)]),
   ((.exchange 63 65 4),[(.neg 65),(.neg 63),(.pos 56),(.pos 67)]),
   ((.exchange 63 66 4),[(.neg 66),(.neg 63),(.pos 57),(.pos 67)]),
   ((.exchange 63 68 2),[(.neg 68),(.neg 63),(.pos 64),(.pos 69)]),
   ((.exchange 64 1 6),[(.neg 64),(.neg 1),(.pos 42),(.pos 43),(.pos 44)]),
   ((.exchange 64 4 6),[(.neg 64),(.neg 4),(.pos 43),(.pos 44)]),
   ((.exchange 64 5 4),[(.neg 64),(.neg 5),(.pos 58),(.pos 59),(.pos 60),(.pos 68)]),
   ((.exchange 64 6 6),[(.neg 64),(.neg 6),(.pos 42),(.pos 43),(.pos 54)]),
   ((.exchange 64 11 3),[(.neg 64),(.neg 11),(.pos 62),(.pos 63),(.pos 69)]),
   ((.exchange 64 20 3),[(.neg 64),(.neg 20),(.pos 61),(.pos 63)]),
   ((.exchange 64 21 3),[(.neg 64),(.neg 21),(.pos 62),(.pos 63)]),
   ((.exchange 64 33 3),[(.neg 64),(.neg 33),(.pos 63),(.pos 69)]),
   ((.exchange 64 40 3),[(.neg 64),(.neg 40),(.pos 61),(.pos 63)]),
   ((.exchange 64 48 4),[(.neg 64),(.neg 48),(.pos 58),(.pos 68)]),
   ((.exchange 64 53 3),[(.neg 64),(.neg 53),(.pos 63),(.pos 69)]),
   ((.exchange 64 67 4),[(.neg 67),(.neg 64),(.pos 60),(.pos 68)]),
   ((.exchange 65 24 0),[(.neg 65),(.neg 24),(.pos 67),(.pos 68),(.pos 69)]),
   ((.exchange 65 30 0),[(.neg 65),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 65 60 0),[(.neg 65),(.neg 60),(.pos 67),(.pos 68)]),
   ((.exchange 66 30 1),[(.neg 66),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 66 34 1),[(.neg 66),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 66 60 1),[(.neg 66),(.neg 60),(.pos 67),(.pos 68)]),
   ((.exchange 67 1 6),[(.neg 67),(.neg 1),(.pos 46),(.pos 47),(.pos 53)]),
   ((.exchange 67 22 2),[(.neg 67),(.neg 22),(.pos 65),(.pos 68),(.pos 69)]),
   ((.exchange 67 22 5),[(.neg 67),(.neg 22),(.pos 56),(.pos 60),(.pos 63)]),
   ((.exchange 67 24 5),[(.neg 67),(.neg 24),(.pos 60),(.pos 63)]),
   ((.exchange 67 28 2),[(.neg 67),(.neg 28),(.pos 65),(.pos 68)]),
   ((.exchange 67 29 2),[(.neg 67),(.neg 29),(.pos 66),(.pos 68)]),
   ((.exchange 67 34 2),[(.neg 67),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 67 48 2),[(.neg 67),(.neg 48),(.pos 65),(.pos 68)]),
   ((.exchange 67 52 6),[(.neg 67),(.neg 52),(.pos 47),(.pos 53)]),
   ((.exchange 67 54 2),[(.neg 67),(.neg 54),(.pos 68),(.pos 69)]),
   ((.exchange 67 59 2),[(.neg 67),(.neg 59),(.pos 66),(.pos 68)]),
   ((.exchange 67 62 5),[(.neg 67),(.neg 62),(.pos 57),(.pos 63)]),
   ((.exchange 68 1 5),[(.neg 68),(.neg 1),(.pos 58),(.pos 59),(.pos 60),(.pos 64)])]

theorem certificates_1_valid : ∀ oc ∈ certificates_1,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_2 : List (Origin 70 66 × List Sat.Literal) :=
  [((.exchange 68 1 6),[(.neg 68),(.neg 1),(.pos 48),(.pos 49),(.pos 50),(.pos 54)]),
   ((.exchange 68 2 5),[(.neg 68),(.neg 2),(.pos 58),(.pos 59),(.pos 64)]),
   ((.exchange 68 6 6),[(.neg 68),(.neg 6),(.pos 48),(.pos 49)]),
   ((.exchange 68 20 3),[(.neg 68),(.neg 20),(.pos 65),(.pos 67),(.pos 69)]),
   ((.exchange 68 26 3),[(.neg 68),(.neg 26),(.pos 65),(.pos 67)]),
   ((.exchange 68 27 3),[(.neg 68),(.neg 27),(.pos 66),(.pos 67)]),
   ((.exchange 68 33 3),[(.neg 68),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 68 43 6),[(.neg 68),(.neg 43),(.pos 49),(.pos 54)]),
   ((.exchange 68 44 5),[(.neg 68),(.neg 44),(.pos 60),(.pos 64)]),
   ((.exchange 68 53 3),[(.neg 68),(.neg 53),(.pos 67),(.pos 69)]),
   ((.exchange 69 30 4),[(.neg 69),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 69 44 5),[(.neg 69),(.neg 44),(.pos 63),(.pos 64)]),
   ((.exchange 69 60 4),[(.neg 69),(.neg 60),(.pos 67),(.pos 68)]),
   ((.exchange 69 60 5),[(.neg 69),(.neg 60),(.pos 63),(.pos 64)]),
   (.newPoint,[(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 0),[(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 49),(.neg 47),(.neg 43),(.neg 41),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 42),(.pos 44),(.pos 45),(.pos 46),(.pos 48),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 65),(.pos 66),(.pos 69)]),
   ((.excluded 1),[(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 54),(.neg 53),(.neg 50),(.neg 48),(.neg 46),(.neg 44),(.neg 42),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 41),(.pos 43),(.pos 45),(.pos 47),(.pos 49),(.pos 51),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 65),(.pos 66),(.pos 69)]),
   ((.excluded 2),[(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 3),[(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 65),(.pos 66),(.pos 69)]),
   ((.excluded 4),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 52),(.neg 49),(.neg 45),(.neg 43),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 40),(.pos 41),(.pos 42),(.pos 44),(.pos 46),(.pos 47),(.pos 48),(.pos 50),(.pos 51),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 5),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 52),(.neg 47),(.neg 45),(.neg 41),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 40),(.pos 42),(.pos 43),(.pos 44),(.pos 46),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 68)]),
   ((.excluded 6),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 52),(.neg 49),(.neg 47),(.neg 45),(.neg 43),(.neg 41),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 40),(.pos 42),(.pos 44),(.pos 46),(.pos 48),(.pos 50),(.pos 51),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60)]),
   ((.excluded 7),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 41),(.pos 47),(.pos 51),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 68)]),
   ((.excluded 8),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 41),(.pos 47),(.pos 51),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60)]),
   ((.excluded 9),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 51),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 68)]),
   ((.excluded 10),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 43),(.pos 49),(.pos 51),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 11),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 43),(.pos 49),(.pos 51),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60)]),
   ((.excluded 12),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 51),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 13),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 51),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60)]),
   ((.excluded 14),[(.neg 68),(.neg 67),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 49),(.neg 47),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 48),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 69)]),
   ((.excluded 15),[(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 43),(.neg 41),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 39),(.pos 40),(.pos 42),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 61),(.pos 62),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 16),[(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 49),(.neg 47),(.neg 43),(.neg 41),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 39),(.pos 40),(.pos 42),(.pos 44),(.pos 45),(.pos 46),(.pos 48),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 61),(.pos 62),(.pos 65),(.pos 66),(.pos 69)]),
   ((.excluded 17),[(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 42),(.neg 40),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 39),(.pos 41),(.pos 43),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 61),(.pos 62),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 18),[(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 42),(.neg 40),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 39),(.pos 41),(.pos 43),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 61),(.pos 62),(.pos 65),(.pos 66),(.pos 69)]),
   ((.excluded 19),[(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 61),(.pos 62),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 20),[(.neg 68),(.neg 67),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 48),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 39),(.pos 45),(.pos 47),(.pos 49),(.pos 51),(.pos 52),(.pos 55),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 69)]),
   ((.excluded 21),[(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 48),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 39),(.pos 45),(.pos 47),(.pos 49),(.pos 51),(.pos 52),(.pos 55),(.pos 61),(.pos 62),(.pos 65),(.pos 66),(.pos 69)]),
   ((.excluded 22),[(.neg 68),(.neg 67),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 69)]),
   ((.excluded 23),[(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 61),(.pos 62),(.pos 65),(.pos 66),(.pos 69)]),
   ((.excluded 24),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 52),(.neg 47),(.neg 45),(.neg 43),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 40),(.pos 41),(.pos 42),(.pos 44),(.pos 46),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 53),(.pos 54),(.pos 55),(.pos 63),(.pos 68)]),
   ((.excluded 25),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 52),(.neg 49),(.neg 47),(.neg 45),(.neg 43),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 40),(.pos 41),(.pos 42),(.pos 44),(.pos 46),(.pos 48),(.pos 50),(.pos 51),(.pos 53),(.pos 54),(.pos 55),(.pos 63)]),
   ((.excluded 26),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 52),(.neg 47),(.neg 45),(.neg 43),(.neg 41),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 40),(.pos 42),(.pos 44),(.pos 46),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 53),(.pos 54),(.pos 55),(.pos 68)]),
   ((.excluded 27),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 52),(.neg 49),(.neg 45),(.neg 41),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 40),(.pos 42),(.pos 43),(.pos 44),(.pos 46),(.pos 47),(.pos 48),(.pos 50),(.pos 51),(.pos 53),(.pos 54),(.pos 55),(.pos 64),(.pos 67)]),
   ((.excluded 28),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 52),(.neg 49),(.neg 47),(.neg 45),(.neg 41),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 40),(.pos 42),(.pos 43),(.pos 44),(.pos 46),(.pos 48),(.pos 50),(.pos 51),(.pos 53),(.pos 54),(.pos 55),(.pos 64)]),
   ((.excluded 29),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 52),(.neg 49),(.neg 45),(.neg 43),(.neg 41),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 40),(.pos 42),(.pos 44),(.pos 46),(.pos 47),(.pos 48),(.pos 50),(.pos 51),(.pos 53),(.pos 54),(.pos 55),(.pos 67)]),
   ((.excluded 30),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 52),(.neg 49),(.neg 47),(.neg 45),(.neg 43),(.neg 41),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 40),(.pos 42),(.pos 44),(.pos 46),(.pos 48),(.pos 50),(.pos 51),(.pos 53),(.pos 54),(.pos 55)]),
   ((.excluded 31),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 41),(.pos 51),(.pos 55),(.pos 68)]),
   ((.excluded 32),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 41),(.pos 49),(.pos 51),(.pos 55),(.pos 64),(.pos 67)]),
   ((.excluded 33),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 41),(.pos 49),(.pos 51),(.pos 55),(.pos 64)]),
   ((.excluded 34),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 41),(.pos 49),(.pos 51),(.pos 55),(.pos 67)]),
   ((.excluded 35),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 41),(.pos 49),(.pos 51),(.pos 55)]),
   ((.excluded 36),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 41),(.pos 51),(.pos 55),(.pos 64),(.pos 67)]),
   ((.excluded 37),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 41),(.pos 51),(.pos 55),(.pos 64)]),
   ((.excluded 38),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 41),(.pos 51),(.pos 55),(.pos 67)]),
   ((.excluded 39),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 41),(.pos 51),(.pos 55)]),
   ((.excluded 40),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 49),(.pos 51),(.pos 55),(.pos 63)]),
   ((.excluded 41),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 49),(.pos 51),(.pos 55),(.pos 64),(.pos 67)]),
   ((.excluded 42),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 49),(.pos 51),(.pos 55),(.pos 64)]),
   ((.excluded 43),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 49),(.pos 51),(.pos 55),(.pos 67)]),
   ((.excluded 44),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 49),(.pos 51),(.pos 55)]),
   ((.excluded 45),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 47),(.pos 51),(.pos 55),(.pos 64)]),
   ((.excluded 46),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 51),(.pos 55),(.pos 64),(.pos 67)]),
   ((.excluded 47),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 51),(.pos 55),(.pos 64)]),
   ((.excluded 48),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 43),(.pos 51),(.pos 55),(.pos 67)]),
   ((.excluded 49),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 51),(.pos 55),(.pos 67)]),
   ((.excluded 50),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 43),(.pos 47),(.pos 51),(.pos 55),(.pos 63),(.pos 68)]),
   ((.excluded 51),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 43),(.pos 47),(.pos 51),(.pos 55),(.pos 63)]),
   ((.excluded 52),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 43),(.pos 47),(.pos 51),(.pos 55),(.pos 68)]),
   ((.excluded 53),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 43),(.pos 47),(.pos 51),(.pos 55)]),
   ((.excluded 54),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 43),(.pos 51),(.pos 55),(.pos 63),(.pos 68)]),
   ((.excluded 55),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 43),(.pos 51),(.pos 55),(.pos 63)]),
   ((.excluded 56),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 43),(.pos 51),(.pos 55),(.pos 68)]),
   ((.excluded 57),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 43),(.pos 51),(.pos 55)]),
   ((.excluded 58),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 47),(.pos 51),(.pos 55),(.pos 63),(.pos 68)]),
   ((.excluded 59),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 47),(.pos 51),(.pos 55),(.pos 63)]),
   ((.excluded 60),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 47),(.pos 51),(.pos 55),(.pos 68)]),
   ((.excluded 61),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 47),(.pos 51),(.pos 55)]),
   ((.excluded 62),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 51),(.pos 55),(.pos 63),(.pos 68)]),
   ((.excluded 63),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 51),(.pos 55),(.pos 63)]),
   ((.excluded 64),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 51),(.pos 55),(.pos 68)]),
   ((.excluded 65),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 51),(.pos 55)])]

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
        Papers.RationalityTen.MatroidChecked.FastSemanticChecks.RawWitness 8 (N7R4.familyMasks.get 45)
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


end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C45

/- Source: MatroidCatalogue/Cases/N8R4C45Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C45

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
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C45.formula []
    exact Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C45.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 8 4 (target w),family_mem 8 4 (target w) hw.1,?_⟩
    exact validWitness_sound 8 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C45


end
end
end BundlePart1

section BundlePart2
/- Source: MatroidChecked/SemanticChunks/Cases06Part03.lean -/




@[expose] public section
noncomputable section

/- Source: MatroidCatalogue/Cases/N8R4C46Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C46

abbrev U := N8R4.grid
noncomputable def old : Finset (Finset (Fin 8)) := N7R4.family 46
noncomputable def newIndexTree : Table ℕ := (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf 35) (.leaf 36)) (.node 3 (.leaf 37) (.leaf 38))) (.node 6 (.node 5 (.leaf 39) (.leaf 40)) (.node 7 (.leaf 41) (.leaf 42)))) (.node 12 (.node 10 (.node 9 (.leaf 43) (.leaf 44)) (.node 11 (.leaf 45) (.leaf 46))) (.node 14 (.node 13 (.leaf 47) (.leaf 48)) (.node 15 (.leaf 49) (.node 16 (.leaf 50) (.leaf 51)))))) (.node 26 (.node 21 (.node 19 (.node 18 (.leaf 52) (.leaf 53)) (.node 20 (.leaf 54) (.leaf 55))) (.node 23 (.node 22 (.leaf 56) (.leaf 57)) (.node 24 (.leaf 58) (.node 25 (.leaf 59) (.leaf 60))))) (.node 30 (.node 28 (.node 27 (.leaf 61) (.leaf 62)) (.node 29 (.leaf 63) (.leaf 64))) (.node 32 (.node 31 (.leaf 65) (.leaf 66)) (.node 33 (.leaf 67) (.node 34 (.leaf 68) (.leaf 69)))))))
noncomputable def newIndex (i : Fin 35) : Fin 70 := Fin.ofNat 70 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 25 (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (24025547520,118,3664080)) (.node 2 (.leaf (14831100544,118,4115650)) (.leaf (29729776000,124,4115482)))) (.node 4 (.leaf (34293212032,148,8309896)) (.node 5 (.leaf (24025308272,126,3400026)) (.leaf (909168,126,2353498))))) (.node 9 (.node 7 (.leaf (24025882480,150,7070560)) (.node 8 (.leaf (29729603312,182,9954497)) (.leaf (34293006064,189,9954497)))) (.node 10 (.leaf (14831943152,182,9169601)) (.node 11 (.leaf (14831976432,189,9169601)) (.leaf (34293513712,190,11789953)))))) (.node 18 (.node 15 (.node 13 (.leaf (29730144240,190,11528321)) (.node 14 (.leaf (34293546992,201,11789953)) (.leaf (14016356366,126,4066643)))) (.node 16 (.leaf (930087566,126,3951955)) (.node 17 (.leaf (14888772238,150,8199492)) (.leaf (29451903758,182,10398920))))) (.node 21 (.node 19 (.leaf (33746903822,189,10398920)) (.node 20 (.leaf (24418763150,182,10312904)) (.leaf (24687199118,189,10312904)))) (.node 23 (.node 22 (.leaf (34082447758,190,12467336)) (.leaf (30055883662,190,12438664))) (.node 24 (.leaf (34350883726,201,12467336)) (.leaf (29451730046,318,12203464))))))) (.node 38 (.node 31 (.node 28 (.node 26 (.leaf (33746697342,319,12203464)) (.node 27 (.leaf (24418524926,318,12174792)) (.leaf (24686960382,319,12174792)))) (.node 29 (.leaf (34082242302,320,16426753)) (.node 30 (.leaf (30055710462,320,16340737)) (.leaf (34350677758,321,16397633))))) (.node 34 (.node 32 (.leaf (14017199998,318,11156936)) (.node 33 (.leaf (14017232766,319,11156936)) (.leaf (930995710,318,11128264)))) (.node 36 (.node 35 (.leaf (930996222,319,11128264)) (.leaf (14889647614,320,15641857))) (.node 37 (.leaf (14889615358,320,15555841)) (.leaf (14889648126,321,15351105)))))) (.node 44 (.node 41 (.node 39 (.leaf (33747206014,320,16200968)) (.node 40 (.leaf (29452271486,320,15416072)) (.leaf (33747238782,321,15935304)))) (.node 42 (.leaf (24687533566,320,16114952)) (.node 43 (.leaf (24419098622,320,15330056)) (.leaf (24687534078,321,15820616))))) (.node 47 (.node 45 (.leaf (30056250878,322,16406152)) (.node 46 (.leaf (34351218174,323,16434824)) (.leaf (30056251390,323,15621256)))) (.node 49 (.node 48 (.leaf (34082750462,322,16434824)) (.leaf (34351185918,323,16406152))) (.node 50 (.leaf (34082783230,323,15649928)) (.leaf (34351218686,324,16434824))))))))

noncomputable def models (i : Fin 51) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 51) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 51) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 70, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (7 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 70, (7 : Fin 8) ∈ U i → ∃ j : Fin 35, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C46

/- Source: MatroidCatalogue/Cases/N8R4C46Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C46


noncomputable def certificates_0 : List (Origin 70 51 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.pos 2)]),
   ((.fixed 3),[(.pos 3)]),
   ((.fixed 4),[(.pos 4)]),
   ((.fixed 5),[(.neg 5)]),
   ((.fixed 6),[(.pos 6)]),
   ((.fixed 7),[(.pos 7)]),
   ((.fixed 8),[(.pos 8)]),
   ((.fixed 9),[(.neg 9)]),
   ((.fixed 10),[(.neg 10)]),
   ((.fixed 11),[(.neg 11)]),
   ((.fixed 12),[(.pos 12)]),
   ((.fixed 13),[(.neg 13)]),
   ((.fixed 14),[(.pos 14)]),
   ((.fixed 15),[(.neg 15)]),
   ((.fixed 16),[(.neg 16)]),
   ((.fixed 17),[(.neg 17)]),
   ((.fixed 18),[(.neg 18)]),
   ((.fixed 19),[(.pos 19)]),
   ((.fixed 20),[(.pos 20)]),
   ((.fixed 21),[(.pos 21)]),
   ((.fixed 22),[(.neg 22)]),
   ((.fixed 23),[(.pos 23)]),
   ((.fixed 24),[(.pos 24)]),
   ((.fixed 25),[(.pos 25)]),
   ((.fixed 26),[(.pos 26)]),
   ((.fixed 28),[(.neg 28)]),
   ((.fixed 29),[(.pos 29)]),
   ((.fixed 30),[(.pos 30)]),
   ((.fixed 31),[(.pos 31)]),
   ((.fixed 32),[(.neg 32)]),
   ((.fixed 33),[(.pos 33)]),
   ((.fixed 34),[(.pos 34)]),
   ((.exchange 2 41 3),[(.neg 41),(.neg 2),(.pos 1),(.pos 39)]),
   ((.exchange 2 49 0),[(.neg 49),(.neg 2),(.pos 13),(.pos 43)]),
   ((.exchange 2 54 0),[(.neg 54),(.neg 2),(.pos 13),(.pos 43)]),
   ((.exchange 2 55 4),[(.neg 55),(.neg 2),(.pos 16),(.pos 36)]),
   ((.exchange 2 56 4),[(.neg 56),(.neg 2),(.pos 0),(.pos 16),(.pos 36)]),
   ((.exchange 2 61 1),[(.neg 61),(.neg 2),(.pos 22),(.pos 42)]),
   ((.exchange 2 64 1),[(.neg 64),(.neg 2),(.pos 22),(.pos 42)]),
   ((.exchange 3 41 3),[(.neg 41),(.neg 3),(.pos 1),(.pos 40)]),
   ((.exchange 3 55 4),[(.neg 55),(.neg 3),(.pos 0),(.pos 17),(.pos 37)]),
   ((.exchange 3 56 4),[(.neg 56),(.neg 3),(.pos 17),(.pos 37)]),
   ((.exchange 4 39 3),[(.neg 39),(.neg 4),(.pos 1),(.pos 41)]),
   ((.exchange 4 40 3),[(.neg 40),(.neg 4),(.pos 1),(.pos 41)]),
   ((.exchange 4 45 3),[(.neg 45),(.neg 4),(.pos 1),(.pos 11),(.pos 41)]),
   ((.exchange 4 46 3),[(.neg 46),(.neg 4),(.pos 1),(.pos 11),(.pos 41)]),
   ((.exchange 4 47 3),[(.neg 47),(.neg 4),(.pos 11),(.pos 41)]),
   ((.exchange 4 51 3),[(.neg 51),(.neg 4),(.pos 1),(.pos 11),(.pos 41)]),
   ((.exchange 4 53 3),[(.neg 53),(.neg 4),(.pos 11),(.pos 41)]),
   ((.exchange 4 55 4),[(.neg 55),(.neg 4),(.pos 0),(.pos 18),(.pos 38)]),
   ((.exchange 4 56 4),[(.neg 56),(.neg 4),(.pos 0),(.pos 18),(.pos 38)]),
   ((.exchange 6 41 3),[(.neg 41),(.neg 6),(.pos 5),(.pos 9),(.pos 45)]),
   ((.exchange 6 43 0),[(.neg 43),(.neg 6),(.pos 13),(.pos 49)]),
   ((.exchange 6 65 1),[(.neg 65),(.neg 6),(.pos 28),(.pos 48)]),
   ((.exchange 6 68 1),[(.neg 68),(.neg 6),(.pos 28),(.pos 48)]),
   ((.exchange 7 41 3),[(.neg 41),(.neg 7),(.pos 5),(.pos 10),(.pos 46)]),
   ((.exchange 8 41 3),[(.neg 41),(.neg 8),(.pos 11),(.pos 47)]),
   ((.exchange 12 41 3),[(.neg 41),(.neg 12),(.pos 9),(.pos 10),(.pos 51)]),
   ((.exchange 12 43 0),[(.neg 43),(.neg 12),(.pos 13),(.pos 54)]),
   ((.exchange 14 41 3),[(.neg 41),(.neg 14),(.pos 11),(.pos 53)]),
   ((.exchange 19 36 4),[(.neg 36),(.neg 19),(.pos 16),(.pos 55)]),
   ((.exchange 19 37 4),[(.neg 37),(.neg 19),(.pos 15),(.pos 16),(.pos 55)]),
   ((.exchange 19 38 4),[(.neg 38),(.neg 19),(.pos 15),(.pos 16),(.pos 55)]),
   ((.exchange 19 42 1),[(.neg 42),(.neg 19),(.pos 22),(.pos 61)]),
   ((.exchange 19 56 4),[(.neg 56),(.neg 19),(.pos 15),(.pos 55)]),
   ((.exchange 19 57 4),[(.neg 57),(.neg 19),(.pos 15),(.pos 55)]),
   ((.exchange 19 59 4),[(.neg 59),(.neg 19),(.pos 16),(.pos 55)]),
   ((.exchange 19 60 4),[(.neg 60),(.neg 19),(.pos 15),(.pos 16),(.pos 55)]),
   ((.exchange 19 66 0),[(.neg 66),(.neg 19),(.pos 32),(.pos 62)]),
   ((.exchange 19 69 0),[(.neg 69),(.neg 19),(.pos 32),(.pos 62)]),
   ((.exchange 20 36 4),[(.neg 36),(.neg 20),(.pos 15),(.pos 17),(.pos 56)]),
   ((.exchange 20 37 4),[(.neg 37),(.neg 20),(.pos 17),(.pos 56)]),
   ((.exchange 20 38 4),[(.neg 38),(.neg 20),(.pos 15),(.pos 17),(.pos 56)]),
   ((.exchange 20 55 4),[(.neg 55),(.neg 20),(.pos 15),(.pos 56)]),
   ((.exchange 20 57 4),[(.neg 57),(.neg 20),(.pos 15),(.pos 56)]),
   ((.exchange 20 59 4),[(.neg 59),(.neg 20),(.pos 15),(.pos 17),(.pos 56)]),
   ((.exchange 20 60 4),[(.neg 60),(.neg 20),(.pos 17),(.pos 56)]),
   ((.exchange 21 55 4),[(.neg 55),(.neg 21),(.pos 15),(.pos 57)]),
   ((.exchange 21 56 4),[(.neg 56),(.neg 21),(.pos 15),(.pos 57)]),
   ((.exchange 23 42 1),[(.neg 42),(.neg 23),(.pos 22),(.pos 64)]),
   ((.exchange 23 55 4),[(.neg 55),(.neg 23),(.pos 16),(.pos 59)]),
   ((.exchange 23 56 4),[(.neg 56),(.neg 23),(.pos 16),(.pos 18),(.pos 59)]),
   ((.exchange 24 55 4),[(.neg 55),(.neg 24),(.pos 17),(.pos 18),(.pos 60)]),
   ((.exchange 24 56 4),[(.neg 56),(.neg 24),(.pos 17),(.pos 60)]),
   ((.exchange 25 48 1),[(.neg 48),(.neg 25),(.pos 28),(.pos 65)]),
   ((.exchange 25 62 0),[(.neg 62),(.neg 25),(.pos 32),(.pos 66)]),
   ((.exchange 25 68 1),[(.neg 68),(.neg 25),(.pos 28),(.pos 65)]),
   ((.exchange 25 69 0),[(.neg 69),(.neg 25),(.pos 32),(.pos 66)]),
   ((.exchange 29 48 1),[(.neg 48),(.neg 29),(.pos 28),(.pos 68)]),
   ((.exchange 29 65 1),[(.neg 65),(.neg 29),(.pos 28),(.pos 68)]),
   ((.exchange 31 62 0),[(.neg 62),(.neg 31),(.pos 32),(.pos 69)]),
   ((.exchange 31 66 0),[(.neg 66),(.neg 31),(.pos 32),(.pos 69)]),
   ((.exchange 35 2 7),[(.neg 35),(.neg 2),(.pos 0),(.pos 1)]),
   ((.exchange 36 12 1),[(.neg 36),(.neg 12),(.pos 42),(.pos 48)]),
   ((.exchange 37 12 2),[(.neg 37),(.neg 12),(.pos 42),(.pos 48)]),
   ((.exchange 38 54 1),[(.neg 54),(.neg 38),(.pos 44),(.pos 50)]),
   ((.exchange 39 23 0),[(.neg 39),(.neg 23),(.pos 43),(.pos 62)]),
   ((.exchange 40 24 0),[(.neg 40),(.neg 24),(.pos 44),(.pos 63)]),
   ((.exchange 41 59 2),[(.neg 59),(.neg 41),(.pos 43),(.pos 62)]),
   ((.exchange 42 4 0),[(.neg 42),(.neg 4),(.pos 43),(.pos 44)]),
   ((.exchange 42 6 4),[(.neg 42),(.neg 6),(.pos 36),(.pos 48)]),
   ((.exchange 42 8 4),[(.neg 42),(.neg 8),(.pos 36),(.pos 37),(.pos 48)]),
   ((.exchange 43 21 3),[(.neg 43),(.neg 21),(.pos 41),(.pos 62)]),
   ((.exchange 43 24 1),[(.neg 43),(.neg 24),(.pos 44),(.pos 64)]),
   ((.exchange 43 40 1),[(.neg 43),(.neg 40),(.pos 42),(.pos 44)]),
   ((.exchange 44 12 2),[(.neg 44),(.neg 12),(.pos 42),(.pos 54)]),
   ((.exchange 44 19 3),[(.neg 44),(.neg 19),(.pos 40),(.pos 41),(.pos 63)]),
   ((.exchange 44 23 2),[(.neg 44),(.neg 23),(.pos 43),(.pos 64)]),
   ((.exchange 44 30 4),[(.neg 44),(.neg 30),(.pos 50),(.pos 60)]),
   ((.exchange 44 62 2),[(.neg 62),(.neg 44),(.pos 43),(.pos 64)]),
   ((.exchange 44 65 3),[(.neg 65),(.neg 44),(.pos 40),(.pos 53),(.pos 63)]),
   ((.exchange 44 66 4),[(.neg 66),(.neg 44),(.pos 38),(.pos 50),(.pos 60)]),
   ((.exchange 45 23 0),[(.neg 45),(.neg 23),(.pos 49),(.pos 52),(.pos 66)]),
   ((.exchange 45 34 0),[(.neg 45),(.neg 34),(.pos 49),(.pos 52),(.pos 66)]),
   ((.exchange 46 30 0),[(.neg 46),(.neg 30),(.pos 50),(.pos 67)]),
   ((.exchange 48 2 5),[(.neg 48),(.neg 2),(.pos 36),(.pos 42)]),
   ((.exchange 48 4 0),[(.neg 48),(.neg 4),(.pos 49),(.pos 50),(.pos 54)]),
   ((.exchange 48 14 0),[(.neg 48),(.neg 14),(.pos 50),(.pos 54)]),
   ((.exchange 48 40 5),[(.neg 48),(.neg 40),(.pos 37),(.pos 42)]),
   ((.exchange 49 19 3),[(.neg 49),(.neg 19),(.pos 45),(.pos 52),(.pos 66)]),
   ((.exchange 49 46 1),[(.neg 49),(.neg 46),(.pos 48),(.pos 50)]),
   ((.exchange 49 61 3),[(.neg 61),(.neg 49),(.pos 45),(.pos 52),(.pos 66)]),
   ((.exchange 50 2 5),[(.neg 50),(.neg 2),(.pos 37),(.pos 38),(.pos 44)]),
   ((.exchange 50 6 2),[(.neg 50),(.neg 6),(.pos 48),(.pos 49)]),
   ((.exchange 50 12 2),[(.neg 50),(.neg 12),(.pos 48),(.pos 54)]),
   ((.exchange 50 19 3),[(.neg 50),(.neg 19),(.pos 46),(.pos 47),(.pos 53),(.pos 67)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_1 : List (Origin 70 51 × List Sat.Literal) :=
  [((.exchange 50 29 2),[(.neg 50),(.neg 29),(.pos 49),(.pos 68)]),
   ((.exchange 50 34 2),[(.neg 50),(.neg 34),(.pos 54),(.pos 68)]),
   ((.exchange 50 36 2),[(.neg 50),(.neg 36),(.pos 48),(.pos 49)]),
   ((.exchange 50 62 5),[(.neg 62),(.neg 50),(.pos 38),(.pos 44),(.pos 60)]),
   ((.exchange 50 64 5),[(.neg 64),(.neg 50),(.pos 44),(.pos 60)]),
   ((.exchange 50 69 2),[(.neg 69),(.neg 50),(.pos 54),(.pos 68)]),
   ((.exchange 51 34 0),[(.neg 51),(.neg 34),(.pos 54),(.pos 69)]),
   ((.exchange 52 2 7),[(.neg 52),(.neg 2),(.pos 9),(.pos 13)]),
   ((.exchange 53 60 4),[(.neg 60),(.neg 53),(.pos 50),(.pos 67)]),
   ((.exchange 53 60 5),[(.neg 60),(.neg 53),(.pos 44),(.pos 63)]),
   ((.exchange 53 64 5),[(.neg 64),(.neg 53),(.pos 44),(.pos 63)]),
   ((.exchange 53 68 4),[(.neg 68),(.neg 53),(.pos 50),(.pos 67)]),
   ((.exchange 54 31 3),[(.neg 54),(.neg 31),(.pos 51),(.pos 69)]),
   ((.exchange 54 37 4),[(.neg 54),(.neg 37),(.pos 48),(.pos 50)]),
   ((.exchange 54 46 4),[(.neg 54),(.neg 46),(.pos 48),(.pos 50)]),
   ((.exchange 54 60 5),[(.neg 60),(.neg 54),(.pos 44),(.pos 64)]),
   ((.exchange 55 12 1),[(.neg 55),(.neg 12),(.pos 58),(.pos 61),(.pos 65)]),
   ((.exchange 56 12 2),[(.neg 56),(.neg 12),(.pos 58),(.pos 61),(.pos 65)]),
   ((.exchange 56 33 0),[(.neg 56),(.neg 33),(.pos 63),(.pos 67)]),
   ((.exchange 56 69 0),[(.neg 69),(.neg 56),(.pos 63),(.pos 67)]),
   ((.exchange 58 2 7),[(.neg 58),(.neg 2),(.pos 16),(.pos 22)]),
   ((.exchange 59 12 1),[(.neg 59),(.neg 12),(.pos 58),(.pos 64),(.pos 68)]),
   ((.exchange 60 34 2),[(.neg 60),(.neg 34),(.pos 64),(.pos 68)]),
   ((.exchange 60 54 6),[(.neg 60),(.neg 54),(.pos 44),(.pos 50)]),
   ((.exchange 60 69 3),[(.neg 69),(.neg 60),(.pos 63),(.pos 67)]),
   ((.exchange 61 7 4),[(.neg 61),(.neg 7),(.pos 56),(.pos 58),(.pos 65)]),
   ((.exchange 61 30 4),[(.neg 61),(.neg 30),(.pos 56),(.pos 58),(.pos 65)]),
   ((.exchange 61 33 0),[(.neg 61),(.neg 33),(.pos 63),(.pos 69)]),
   ((.exchange 62 2 6),[(.neg 62),(.neg 2),(.pos 39),(.pos 43)]),
   ((.exchange 62 24 1),[(.neg 62),(.neg 24),(.pos 63),(.pos 64)]),
   ((.exchange 62 40 1),[(.neg 62),(.neg 40),(.pos 61),(.pos 63)]),
   ((.exchange 63 2 2),[(.neg 63),(.neg 2),(.pos 61),(.pos 62),(.pos 64)]),
   ((.exchange 63 2 6),[(.neg 63),(.neg 2),(.pos 40),(.pos 41),(.pos 44)]),
   ((.exchange 63 6 4),[(.neg 63),(.neg 6),(.pos 56),(.pos 57),(.pos 60),(.pos 67)]),
   ((.exchange 63 23 2),[(.neg 63),(.neg 23),(.pos 62),(.pos 64)]),
   ((.exchange 63 48 6),[(.neg 63),(.neg 48),(.pos 40),(.pos 44),(.pos 53)]),
   ((.exchange 63 50 6),[(.neg 63),(.neg 50),(.pos 44),(.pos 53)]),
   ((.exchange 63 51 2),[(.neg 63),(.neg 51),(.pos 61),(.pos 69)]),
   ((.exchange 63 55 2),[(.neg 63),(.neg 55),(.pos 61),(.pos 62)]),
   ((.exchange 63 68 2),[(.neg 68),(.neg 63),(.pos 64),(.pos 69)]),
   ((.exchange 63 68 4),[(.neg 68),(.neg 63),(.pos 60),(.pos 67)]),
   ((.exchange 64 6 4),[(.neg 64),(.neg 6),(.pos 58),(.pos 59),(.pos 68)]),
   ((.exchange 64 8 4),[(.neg 64),(.neg 8),(.pos 59),(.pos 60),(.pos 68)]),
   ((.exchange 64 14 6),[(.neg 64),(.neg 14),(.pos 44),(.pos 54)]),
   ((.exchange 64 33 3),[(.neg 64),(.neg 33),(.pos 63),(.pos 69)]),
   ((.exchange 64 41 3),[(.neg 64),(.neg 41),(.pos 62),(.pos 63)]),
   ((.exchange 64 57 3),[(.neg 64),(.neg 57),(.pos 62),(.pos 63)]),
   ((.exchange 65 2 5),[(.neg 65),(.neg 2),(.pos 55),(.pos 58),(.pos 61)]),
   ((.exchange 65 33 0),[(.neg 65),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 65 40 5),[(.neg 65),(.neg 40),(.pos 56),(.pos 61)]),
   ((.exchange 66 2 6),[(.neg 66),(.neg 2),(.pos 45),(.pos 49),(.pos 52)]),
   ((.exchange 66 24 1),[(.neg 66),(.neg 24),(.pos 67),(.pos 68),(.pos 69)]),
   ((.exchange 66 30 1),[(.neg 66),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 66 44 6),[(.neg 66),(.neg 44),(.pos 47),(.pos 49),(.pos 52)]),
   ((.exchange 66 48 6),[(.neg 66),(.neg 48),(.pos 45),(.pos 49)]),
   ((.exchange 67 2 5),[(.neg 67),(.neg 2),(.pos 56),(.pos 57),(.pos 60),(.pos 63)]),
   ((.exchange 67 2 6),[(.neg 67),(.neg 2),(.pos 46),(.pos 47),(.pos 50),(.pos 53)]),
   ((.exchange 67 6 2),[(.neg 67),(.neg 6),(.pos 65),(.pos 66),(.pos 68)]),
   ((.exchange 67 12 2),[(.neg 67),(.neg 12),(.pos 65),(.pos 68),(.pos 69)]),
   ((.exchange 67 23 2),[(.neg 67),(.neg 23),(.pos 66),(.pos 68),(.pos 69)]),
   ((.exchange 67 29 2),[(.neg 67),(.neg 29),(.pos 66),(.pos 68)]),
   ((.exchange 67 34 2),[(.neg 67),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 67 41 5),[(.neg 67),(.neg 41),(.pos 57),(.pos 63)]),
   ((.exchange 67 49 6),[(.neg 67),(.neg 49),(.pos 47),(.pos 50)]),
   ((.exchange 67 64 5),[(.neg 67),(.neg 64),(.pos 60),(.pos 63)]),
   ((.exchange 68 14 6),[(.neg 68),(.neg 14),(.pos 50),(.pos 54)]),
   ((.exchange 68 23 5),[(.neg 68),(.neg 23),(.pos 59),(.pos 64)]),
   ((.exchange 68 33 3),[(.neg 68),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 68 40 5),[(.neg 68),(.neg 40),(.pos 58),(.pos 60),(.pos 64)]),
   ((.exchange 68 47 3),[(.neg 68),(.neg 47),(.pos 66),(.pos 67)]),
   ((.exchange 68 53 6),[(.neg 68),(.neg 53),(.pos 50),(.pos 54)]),
   ((.exchange 69 2 6),[(.neg 69),(.neg 2),(.pos 51),(.pos 52),(.pos 54)]),
   ((.exchange 69 24 5),[(.neg 69),(.neg 24),(.pos 63),(.pos 64)]),
   ((.exchange 69 26 4),[(.neg 69),(.neg 26),(.pos 65),(.pos 67)]),
   ((.exchange 69 48 6),[(.neg 69),(.neg 48),(.pos 51),(.pos 54)]),
   ((.exchange 69 56 4),[(.neg 69),(.neg 56),(.pos 65),(.pos 67)]),
   (.newPoint,[(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 0),[(.neg 69),(.neg 67),(.neg 66),(.neg 63),(.neg 62),(.neg 54),(.neg 50),(.neg 49),(.neg 44),(.neg 43),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 51),(.pos 52),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 64),(.pos 65),(.pos 68)]),
   ((.excluded 1),[(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 50),(.neg 48),(.neg 44),(.neg 42),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 43),(.pos 45),(.pos 46),(.pos 47),(.pos 49),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 62),(.pos 66),(.pos 69)]),
   ((.excluded 2),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 54),(.neg 49),(.neg 48),(.neg 43),(.neg 42),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 3),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 51),(.pos 52),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60)]),
   ((.excluded 4),[(.neg 69),(.neg 67),(.neg 66),(.neg 63),(.neg 62),(.neg 53),(.neg 51),(.neg 47),(.neg 46),(.neg 45),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 42),(.pos 43),(.pos 44),(.pos 48),(.pos 49),(.pos 50),(.pos 52),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 64),(.pos 65),(.pos 68)]),
   ((.excluded 5),[(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 42),(.pos 48),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 6),[(.neg 69),(.neg 67),(.neg 66),(.neg 63),(.neg 62),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 42),(.pos 48),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 64),(.pos 65),(.pos 68)]),
   ((.excluded 7),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 53),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 43),(.pos 49),(.pos 52),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 8),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 53),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 43),(.pos 49),(.pos 52),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60)]),
   ((.excluded 9),[(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 54),(.neg 53),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 44),(.pos 50),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 62),(.pos 66),(.pos 69)]),
   ((.excluded 10),[(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 62),(.pos 66),(.pos 69)]),
   ((.excluded 11),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 44),(.pos 50),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60)]),
   ((.excluded 12),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 13),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60)]),
   ((.excluded 14),[(.neg 68),(.neg 67),(.neg 65),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 50),(.neg 48),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 49),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 58),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 66),(.pos 69)]),
   ((.excluded 15),[(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 44),(.neg 42),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 39),(.pos 40),(.pos 41),(.pos 43),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 58),(.pos 62),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 16),[(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 50),(.neg 48),(.neg 44),(.neg 42),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 39),(.pos 40),(.pos 41),(.pos 43),(.pos 45),(.pos 46),(.pos 47),(.pos 49),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 58),(.pos 62),(.pos 66),(.pos 69)]),
   ((.excluded 17),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 45),(.pos 46),(.pos 47),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 58),(.pos 61),(.pos 64),(.pos 67)]),
   ((.excluded 18),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 45),(.pos 46),(.pos 47),(.pos 51),(.pos 52),(.pos 53),(.pos 58),(.pos 61),(.pos 64)]),
   ((.excluded 19),[(.neg 69),(.neg 67),(.neg 66),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 50),(.neg 49),(.neg 43),(.neg 42),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 39),(.pos 40),(.pos 41),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 51),(.pos 52),(.pos 53),(.pos 58),(.pos 63),(.pos 65),(.pos 68)]),
   ((.excluded 20),[(.neg 69),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 50),(.neg 49),(.neg 44),(.neg 43),(.neg 42),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 51),(.pos 52),(.pos 53),(.pos 58),(.pos 65),(.pos 68)]),
   ((.excluded 21),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 50),(.neg 49),(.neg 48),(.neg 43),(.neg 42),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 39),(.pos 40),(.pos 41),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 51),(.pos 52),(.pos 53),(.pos 58),(.pos 63)]),
   ((.excluded 22),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 58),(.pos 67)]),
   ((.excluded 23),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 51),(.pos 52),(.pos 53),(.pos 58)]),
   ((.excluded 24),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 43),(.pos 44),(.pos 49),(.pos 52),(.pos 54),(.pos 58),(.pos 61),(.pos 64),(.pos 67)]),
   ((.excluded 25),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 43),(.pos 44),(.pos 49),(.pos 52),(.pos 54),(.pos 58),(.pos 61),(.pos 64)]),
   ((.excluded 26),[(.neg 69),(.neg 67),(.neg 66),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 51),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 43),(.pos 48),(.pos 49),(.pos 50),(.pos 52),(.pos 54),(.pos 58),(.pos 63),(.pos 65),(.pos 68)]),
   ((.excluded 27),[(.neg 69),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 51),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 43),(.pos 48),(.pos 49),(.pos 50),(.pos 52),(.pos 54),(.pos 58),(.pos 65),(.pos 68)]),
   ((.excluded 28),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 43),(.pos 49),(.pos 52),(.pos 54),(.pos 58),(.pos 63)]),
   ((.excluded 29),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 43),(.pos 49),(.pos 52),(.pos 54),(.pos 58),(.pos 67)]),
   ((.excluded 30),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 43),(.pos 49),(.pos 52),(.pos 54),(.pos 58)]),
   ((.excluded 31),[(.neg 68),(.neg 67),(.neg 65),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 50),(.pos 52),(.pos 58),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 66),(.pos 69)]),
   ((.excluded 32),[(.neg 68),(.neg 67),(.neg 65),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 52),(.pos 58),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 66),(.pos 69)]),
   ((.excluded 33),[(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 44),(.pos 48),(.pos 52),(.pos 58),(.pos 62),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 34),[(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 48),(.pos 52),(.pos 58),(.pos 62),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 35),[(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 44),(.pos 52),(.pos 58),(.pos 62),(.pos 66),(.pos 69)]),
   ((.excluded 36),[(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 52),(.pos 58),(.pos 62),(.pos 66),(.pos 69)]),
   ((.excluded 37),[(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 52),(.pos 58),(.pos 62),(.pos 66),(.pos 69)]),
   ((.excluded 38),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 50),(.pos 52),(.pos 58),(.pos 61),(.pos 64)]),
   ((.excluded 39),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 52),(.pos 58),(.pos 61),(.pos 64),(.pos 67)]),
   ((.excluded 40),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 52),(.pos 58),(.pos 61),(.pos 64)]),
   ((.excluded 41),[(.neg 69),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 44),(.pos 48),(.pos 52),(.pos 58),(.pos 65),(.pos 68)]),
   ((.excluded 42),[(.neg 69),(.neg 67),(.neg 66),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 48),(.pos 52),(.pos 58),(.pos 63),(.pos 65),(.pos 68)]),
   ((.excluded 43),[(.neg 69),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 48),(.pos 52),(.pos 58),(.pos 65),(.pos 68)]),
   ((.excluded 44),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 44),(.pos 52),(.pos 58),(.pos 67)]),
   ((.excluded 45),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 44),(.pos 52),(.pos 58)]),
   ((.excluded 46),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 52),(.pos 58),(.pos 67)]),
   ((.excluded 47),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 52),(.pos 58),(.pos 63)]),
   ((.excluded 48),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 52),(.pos 58)]),
   ((.excluded 49),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 52),(.pos 58),(.pos 63)]),
   ((.excluded 50),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 52),(.pos 58)])]

theorem certificates_1_valid : ∀ oc ∈ certificates_1,
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
        Papers.RationalityTen.MatroidChecked.FastSemanticChecks.RawWitness 8 (N7R4.familyMasks.get 46)
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


end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C46

/- Source: MatroidCatalogue/Cases/N8R4C46Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C46

noncomputable def certificates : List (Origin 70 51 × List Sat.Literal) :=
  certificates_0 ++ certificates_1

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  intro oc hoc
  simp only [certificates,List.mem_append,or_assoc] at hoc
  rcases hoc with h0 | h1
  · exact certificates_0_valid oc h0
  · exact certificates_1_valid oc h1

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
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C46.formula []
    exact Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C46.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 8 4 (target w),family_mem 8 4 (target w) hw.1,?_⟩
    exact validWitness_sound 8 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C46


end
end
end BundlePart2

section BundlePart3
/- Source: MatroidChecked/SemanticChunks/Cases06Part04.lean -/




@[expose] public section
noncomputable section

/- Source: MatroidCatalogue/Cases/N8R4C47Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C47

abbrev U := N8R4.grid
noncomputable def old : Finset (Finset (Fin 8)) := N7R4.family 47
noncomputable def newIndexTree : Table ℕ := (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf 35) (.leaf 36)) (.node 3 (.leaf 37) (.leaf 38))) (.node 6 (.node 5 (.leaf 39) (.leaf 40)) (.node 7 (.leaf 41) (.leaf 42)))) (.node 12 (.node 10 (.node 9 (.leaf 43) (.leaf 44)) (.node 11 (.leaf 45) (.leaf 46))) (.node 14 (.node 13 (.leaf 47) (.leaf 48)) (.node 15 (.leaf 49) (.node 16 (.leaf 50) (.leaf 51)))))) (.node 26 (.node 21 (.node 19 (.node 18 (.leaf 52) (.leaf 53)) (.node 20 (.leaf 54) (.leaf 55))) (.node 23 (.node 22 (.leaf 56) (.leaf 57)) (.node 24 (.leaf 58) (.node 25 (.leaf 59) (.leaf 60))))) (.node 30 (.node 28 (.node 27 (.leaf 61) (.leaf 62)) (.node 29 (.leaf 63) (.leaf 64))) (.node 32 (.node 31 (.leaf 65) (.leaf 66)) (.node 33 (.leaf 67) (.node 34 (.leaf 68) (.leaf 69)))))))
noncomputable def newIndex (i : Fin 35) : Fin 70 := Fin.ofNat 70 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 56 (.node 28 (.node 14 (.node 7 (.node 3 (.node 1 (.leaf (26223230976,119,4151504)) (.node 2 (.leaf (26685054976,125,4151490)) (.leaf (26533912576,125,4151322)))) (.node 5 (.node 4 (.leaf (1066393600,148,3570896)) (.leaf (26836197376,149,8345736))) (.node 6 (.leaf (25106455552,127,4141410)) (.leaf (16163855360,127,4130658))))) (.node 10 (.node 8 (.leaf (33746770944,151,8332128)) (.node 9 (.leaf (34074246144,183,12535432)) (.leaf (17163074560,191,12535432)))) (.node 12 (.node 11 (.leaf (34342943744,192,12535432)) (.leaf (25501105152,191,12531792))) (.node 13 (.leaf (34091039744,192,12531792)) (.leaf (34191801344,183,12531848)))))) (.node 21 (.node 17 (.node 15 (.leaf (17146280960,191,12535376)) (.node 16 (.leaf (34326150144,192,12535376)) (.leaf (25635453952,191,12531848)))) (.node 19 (.node 18 (.leaf (34225388544,192,12531848)) (.leaf (25769802752,202,12535432))) (.node 20 (.leaf (17179868160,202,12531848)) (.leaf (34359737344,203,12535432))))) (.node 24 (.node 22 (.leaf (1065354110,163,3439898)) (.node 23 (.leaf (1041278,163,2293018)) (.leaf (1066394494,215,11664520)))) (.node 26 (.node 25 (.leaf (26684605310,189,5668040)) (.leaf (26533610366,189,5667928))) (.node 27 (.leaf (26835600254,200,9829512)) (.leaf (26223682430,189,5438664))))))) (.node 42 (.node 35 (.node 31 (.node 29 (.leaf (26223534974,189,5438552)) (.node 30 (.leaf (26223829886,200,9370760)) (.leaf (26534060926,190,7765128)))) (.node 33 (.node 32 (.leaf (26836050814,201,9829512)) (.leaf (26534208382,201,9370704))) (.node 34 (.leaf (26684908414,190,7535752)) (.leaf (26835903358,201,9829456))))) (.node 38 (.node 36 (.leaf (26685203326,201,9370760)) (.node 37 (.leaf (26836198270,222,11664520)) (.leaf (25634938750,320,14533456)))) (.node 40 (.node 39 (.leaf (25500721022,320,14533288)) (.leaf (25769156478,321,14504728))) (.node 41 (.leaf (17162100606,320,14522704)) (.leaf (17145323390,320,14522536)))))) (.node 49 (.node 45 (.node 43 (.leaf (17178877822,321,14490392)) (.node 44 (.leaf (34073927550,325,14599816)) (.leaf (34342363006,326,14599368)))) (.node 47 (.node 46 (.leaf (34090704766,326,14592088)) (.leaf (34191368062,325,14596232))) (.node 48 (.leaf (34325585790,326,14599256)) (.leaf (34224922494,326,14592200))))) (.node 52 (.node 50 (.leaf (34359140222,327,14599816)) (.node 51 (.leaf (25106972542,320,13615952)) (.leaf (25106841470,320,13615784)))) (.node 54 (.node 53 (.leaf (25107103614,321,13357848)) (.leaf (16164831102,320,13605200))) (.node 55 (.leaf (16164814718,320,13605032)) (.leaf (16164847486,321,13343512)))))))) (.node 84 (.node 70 (.node 63 (.node 59 (.node 57 (.leaf (33747091326,325,14141064)) (.node 58 (.leaf (33747353470,326,14140616)) (.leaf (33747107710,326,14133336)))) (.node 61 (.node 60 (.leaf (33747206014,325,14137480)) (.leaf (33747337086,326,14140504))) (.node 62 (.leaf (33747238782,326,14133448)) (.leaf (33747369854,327,14141064))))) (.node 66 (.node 64 (.leaf (25501237118,328,16201864)) (.node 65 (.leaf (25769672574,329,16431240)) (.leaf (25501368190,329,16201808)))) (.node 68 (.node 67 (.leaf (25635323774,328,16431240)) (.leaf (25769541502,329,16431184))) (.node 69 (.leaf (25635585918,329,16201864)) (.leaf (25769803646,330,16434824)))))) (.node 77 (.node 73 (.node 71 (.leaf (17146298238,328,16205448)) (.node 72 (.leaf (17179852670,329,16434824)) (.leaf (17146314622,329,16205392)))) (.node 75 (.node 74 (.leaf (17163059070,328,16434824)) (.leaf (17179836286,329,16434768))) (.node 76 (.leaf (17163091838,329,16205448)) (.leaf (17179869054,330,16431240))))) (.node 80 (.node 78 (.leaf (34091286398,331,16205448)) (.node 79 (.leaf (34191687550,332,16434824)) (.leaf (34325905278,333,16434768)))) (.node 82 (.node 81 (.leaf (34225241982,333,16431240)) (.leaf (34359459710,334,16434824))) (.node 83 (.leaf (34191949694,333,16205448)) (.leaf (34326167422,335,16205448))))))) (.node 98 (.node 91 (.node 87 (.node 85 (.leaf (34225504126,336,16205448)) (.node 86 (.leaf (34359721854,337,16434824)) (.leaf (34342698878,331,16434824)))) (.node 89 (.node 88 (.leaf (34191703934,333,16201808)) (.leaf (34325921662,336,16434768))) (.node 90 (.leaf (34225258366,335,16431240)) (.leaf (34359476094,337,16431184))))) (.node 94 (.node 92 (.leaf (34326052734,331,16201864)) (.node 93 (.leaf (34191966078,334,16201864)) (.leaf (34326183806,337,16205392)))) (.node 96 (.node 95 (.leaf (34225487742,331,16431240)) (.leaf (34225520510,337,16201864))) (.node 97 (.leaf (34074361726,332,16205448)) (.leaf (34342797182,333,16434824)))))) (.node 105 (.node 101 (.node 99 (.leaf (34091138942,333,16431184)) (.node 100 (.leaf (34359574398,334,16431240)) (.leaf (34074492798,333,16205392)))) (.node 103 (.node 102 (.leaf (34342928254,335,16434824)) (.leaf (34091270014,336,16205392))) (.node 104 (.leaf (34359705470,337,16434768)) (.leaf (34074394494,333,16201864))))) (.node 108 (.node 106 (.leaf (34342829950,336,16434824)) (.node 107 (.leaf (34091171710,335,16201864)) (.leaf (34359607166,337,16431240)))) (.node 110 (.node 109 (.leaf (34074525566,334,16205448)) (.leaf (34342961022,337,16205448))) (.node 111 (.leaf (34091302782,337,16201808)) (.leaf (34359738238,338,16434824)))))))))

noncomputable def models (i : Fin 112) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 112) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 112) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 70, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (7 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 70, (7 : Fin 8) ∈ U i → ∃ j : Fin 35, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C47

/- Source: MatroidCatalogue/Cases/N8R4C47Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C47


noncomputable def certificates_0 : List (Origin 70 112 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.neg 2)]),
   ((.fixed 3),[(.neg 3)]),
   ((.fixed 4),[(.neg 4)]),
   ((.fixed 5),[(.neg 5)]),
   ((.fixed 6),[(.pos 6)]),
   ((.fixed 7),[(.pos 7)]),
   ((.fixed 8),[(.pos 8)]),
   ((.fixed 9),[(.pos 9)]),
   ((.fixed 10),[(.pos 10)]),
   ((.fixed 11),[(.pos 11)]),
   ((.fixed 12),[(.neg 12)]),
   ((.fixed 13),[(.pos 13)]),
   ((.fixed 14),[(.pos 14)]),
   ((.fixed 15),[(.neg 15)]),
   ((.fixed 16),[(.pos 16)]),
   ((.fixed 17),[(.pos 17)]),
   ((.fixed 18),[(.pos 18)]),
   ((.fixed 19),[(.pos 19)]),
   ((.fixed 20),[(.pos 20)]),
   ((.fixed 21),[(.pos 21)]),
   ((.fixed 22),[(.neg 22)]),
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
   ((.exchange 6 37 5),[(.neg 37),(.neg 6),(.pos 0),(.pos 36)]),
   ((.exchange 6 38 5),[(.neg 38),(.neg 6),(.pos 0),(.pos 36)]),
   ((.exchange 6 39 5),[(.neg 39),(.neg 6),(.pos 2),(.pos 36)]),
   ((.exchange 6 40 5),[(.neg 40),(.neg 6),(.pos 0),(.pos 2),(.pos 36)]),
   ((.exchange 6 41 5),[(.neg 41),(.neg 6),(.pos 0),(.pos 2),(.pos 36)]),
   ((.exchange 6 43 5),[(.neg 43),(.neg 6),(.pos 2),(.pos 36)]),
   ((.exchange 6 44 5),[(.neg 44),(.neg 6),(.pos 0),(.pos 2),(.pos 36)]),
   ((.exchange 6 46 3),[(.neg 46),(.neg 6),(.pos 5),(.pos 45)]),
   ((.exchange 6 51 1),[(.neg 51),(.neg 6),(.pos 12),(.pos 48)]),
   ((.exchange 6 54 1),[(.neg 54),(.neg 6),(.pos 12),(.pos 48)]),
   ((.exchange 6 65 3),[(.neg 65),(.neg 6),(.pos 25),(.pos 45)]),
   ((.exchange 6 66 3),[(.neg 66),(.neg 6),(.pos 25),(.pos 45)]),
   ((.exchange 6 67 3),[(.neg 67),(.neg 6),(.pos 5),(.pos 25),(.pos 45)]),
   ((.exchange 7 36 5),[(.neg 36),(.neg 7),(.pos 0),(.pos 37)]),
   ((.exchange 7 45 3),[(.neg 45),(.neg 7),(.pos 5),(.pos 46)]),
   ((.exchange 7 55 3),[(.neg 55),(.neg 7),(.pos 5),(.pos 26),(.pos 46)]),
   ((.exchange 7 56 3),[(.neg 56),(.neg 7),(.pos 26),(.pos 46)]),
   ((.exchange 7 57 3),[(.neg 57),(.neg 7),(.pos 5),(.pos 26),(.pos 46)]),
   ((.exchange 7 65 3),[(.neg 65),(.neg 7),(.pos 26),(.pos 46)]),
   ((.exchange 7 66 3),[(.neg 66),(.neg 7),(.pos 5),(.pos 26),(.pos 46)]),
   ((.exchange 7 67 3),[(.neg 67),(.neg 7),(.pos 26),(.pos 46)]),
   ((.exchange 8 36 5),[(.neg 36),(.neg 8),(.pos 0),(.pos 38)]),
   ((.exchange 8 65 3),[(.neg 65),(.neg 8),(.pos 5),(.pos 27),(.pos 47)]),
   ((.exchange 8 66 3),[(.neg 66),(.neg 8),(.pos 27),(.pos 47)]),
   ((.exchange 8 67 3),[(.neg 67),(.neg 8),(.pos 27),(.pos 47)]),
   ((.exchange 9 36 5),[(.neg 36),(.neg 9),(.pos 2),(.pos 39)]),
   ((.exchange 9 48 1),[(.neg 48),(.neg 9),(.pos 12),(.pos 51)]),
   ((.exchange 9 54 1),[(.neg 54),(.neg 9),(.pos 12),(.pos 51)]),
   ((.exchange 10 36 5),[(.neg 36),(.neg 10),(.pos 1),(.pos 3),(.pos 40)]),
   ((.exchange 11 36 5),[(.neg 36),(.neg 11),(.pos 1),(.pos 4),(.pos 41)]),
   ((.exchange 13 36 5),[(.neg 36),(.neg 13),(.pos 2),(.pos 43)]),
   ((.exchange 13 48 1),[(.neg 48),(.neg 13),(.pos 12),(.pos 54)]),
   ((.exchange 13 51 1),[(.neg 51),(.neg 13),(.pos 12),(.pos 54)]),
   ((.exchange 14 36 5),[(.neg 36),(.neg 14),(.pos 3),(.pos 4),(.pos 44)]),
   ((.exchange 16 45 3),[(.neg 45),(.neg 16),(.pos 25),(.pos 55)]),
   ((.exchange 16 46 3),[(.neg 46),(.neg 16),(.pos 15),(.pos 25),(.pos 55)]),
   ((.exchange 16 47 3),[(.neg 47),(.neg 16),(.pos 15),(.pos 25),(.pos 55)]),
   ((.exchange 16 56 3),[(.neg 56),(.neg 16),(.pos 15),(.pos 55)]),
   ((.exchange 16 61 1),[(.neg 61),(.neg 16),(.pos 22),(.pos 58)]),
   ((.exchange 16 64 1),[(.neg 64),(.neg 16),(.pos 22),(.pos 58)]),
   ((.exchange 16 65 3),[(.neg 65),(.neg 16),(.pos 25),(.pos 55)]),
   ((.exchange 16 67 3),[(.neg 67),(.neg 16),(.pos 15),(.pos 25),(.pos 55)]),
   ((.exchange 17 45 3),[(.neg 45),(.neg 17),(.pos 15),(.pos 26),(.pos 56)]),
   ((.exchange 17 46 3),[(.neg 46),(.neg 17),(.pos 26),(.pos 56)]),
   ((.exchange 17 47 3),[(.neg 47),(.neg 17),(.pos 15),(.pos 26),(.pos 56)]),
   ((.exchange 17 55 3),[(.neg 55),(.neg 17),(.pos 15),(.pos 56)]),
   ((.exchange 17 65 3),[(.neg 65),(.neg 17),(.pos 26),(.pos 56)]),
   ((.exchange 17 66 3),[(.neg 66),(.neg 17),(.pos 15),(.pos 26),(.pos 56)]),
   ((.exchange 17 67 3),[(.neg 67),(.neg 17),(.pos 26),(.pos 56)]),
   ((.exchange 18 46 3),[(.neg 46),(.neg 18),(.pos 15),(.pos 27),(.pos 57)]),
   ((.exchange 18 65 3),[(.neg 65),(.neg 18),(.pos 15),(.pos 27),(.pos 57)]),
   ((.exchange 18 67 3),[(.neg 67),(.neg 18),(.pos 27),(.pos 57)]),
   ((.exchange 19 58 1),[(.neg 58),(.neg 19),(.pos 22),(.pos 61)]),
   ((.exchange 19 64 1),[(.neg 64),(.neg 19),(.pos 22),(.pos 61)]),
   ((.exchange 23 58 1),[(.neg 58),(.neg 23),(.pos 22),(.pos 64)]),
   ((.exchange 23 61 1),[(.neg 61),(.neg 23),(.pos 22),(.pos 64)]),
   ((.exchange 28 45 3),[(.neg 45),(.neg 28),(.pos 25),(.pos 65)]),
   ((.exchange 28 46 3),[(.neg 46),(.neg 28),(.pos 26),(.pos 65)]),
   ((.exchange 28 47 3),[(.neg 47),(.neg 28),(.pos 25),(.pos 26),(.pos 65)]),
   ((.exchange 28 55 3),[(.neg 55),(.neg 28),(.pos 25),(.pos 65)]),
   ((.exchange 28 56 3),[(.neg 56),(.neg 28),(.pos 26),(.pos 65)]),
   ((.exchange 28 57 3),[(.neg 57),(.neg 28),(.pos 25),(.pos 26),(.pos 65)]),
   ((.exchange 28 66 3),[(.neg 66),(.neg 28),(.pos 25),(.pos 65)]),
   ((.exchange 28 67 3),[(.neg 67),(.neg 28),(.pos 26),(.pos 65)]),
   ((.exchange 29 45 3),[(.neg 45),(.neg 29),(.pos 25),(.pos 66)]),
   ((.exchange 29 46 3),[(.neg 46),(.neg 29),(.pos 25),(.pos 27),(.pos 66)]),
   ((.exchange 29 47 3),[(.neg 47),(.neg 29),(.pos 27),(.pos 66)]),
   ((.exchange 29 65 3),[(.neg 65),(.neg 29),(.pos 25),(.pos 66)]),
   ((.exchange 29 67 3),[(.neg 67),(.neg 29),(.pos 27),(.pos 66)]),
   ((.exchange 30 45 3),[(.neg 45),(.neg 30),(.pos 26),(.pos 27),(.pos 67)]),
   ((.exchange 30 46 3),[(.neg 46),(.neg 30),(.pos 26),(.pos 67)]),
   ((.exchange 30 47 3),[(.neg 47),(.neg 30),(.pos 27),(.pos 67)]),
   ((.exchange 30 55 3),[(.neg 55),(.neg 30),(.pos 26),(.pos 27),(.pos 67)]),
   ((.exchange 30 56 3),[(.neg 56),(.neg 30),(.pos 26),(.pos 67)]),
   ((.exchange 30 57 3),[(.neg 57),(.neg 30),(.pos 27),(.pos 67)]),
   ((.exchange 30 65 3),[(.neg 65),(.neg 30),(.pos 26),(.pos 67)]),
   ((.exchange 30 66 3),[(.neg 66),(.neg 30),(.pos 27),(.pos 67)]),
   ((.exchange 35 6 7),[(.neg 35),(.neg 6),(.pos 0),(.pos 5)]),
   ((.exchange 36 28 1),[(.neg 36),(.neg 28),(.pos 48),(.pos 58)]),
   ((.exchange 36 29 0),[(.neg 36),(.neg 29),(.pos 49),(.pos 59)]),
   ((.exchange 37 30 0),[(.neg 37),(.neg 30),(.pos 50),(.pos 60)]),
   ((.exchange 37 31 2),[(.neg 37),(.neg 31),(.pos 42),(.pos 48),(.pos 58)]),
   ((.exchange 37 68 2),[(.neg 68),(.neg 37),(.pos 48),(.pos 58)]),
   ((.exchange 37 69 2),[(.neg 69),(.neg 37),(.pos 42),(.pos 48),(.pos 58)]),
   ((.exchange 38 68 2),[(.neg 68),(.neg 38),(.pos 49),(.pos 59)]),
   ((.exchange 39 31 1),[(.neg 39),(.neg 31),(.pos 51),(.pos 61)]),
   ((.exchange 40 33 0),[(.neg 40),(.neg 33),(.pos 53),(.pos 63)]),
   ((.exchange 40 34 2),[(.neg 40),(.neg 34),(.pos 42),(.pos 51),(.pos 61)]),
   ((.exchange 40 68 2),[(.neg 68),(.neg 40),(.pos 42),(.pos 51),(.pos 61)]),
   ((.exchange 40 69 2),[(.neg 69),(.neg 40),(.pos 51),(.pos 61)]),
   ((.exchange 42 6 7),[(.neg 42),(.neg 6),(.pos 2),(.pos 12)]),
   ((.exchange 43 28 1),[(.neg 43),(.neg 28),(.pos 42),(.pos 54),(.pos 64)]),
   ((.exchange 43 29 4),[(.neg 43),(.neg 29),(.pos 49),(.pos 59)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_1 : List (Origin 70 112 × List Sat.Literal) :=
  [((.exchange 43 32 3),[(.neg 43),(.neg 32),(.pos 52),(.pos 62)]),
   ((.exchange 43 68 4),[(.neg 68),(.neg 43),(.pos 49),(.pos 59)]),
   ((.exchange 44 30 4),[(.neg 44),(.neg 30),(.pos 50),(.pos 60)]),
   ((.exchange 44 33 3),[(.neg 44),(.neg 33),(.pos 53),(.pos 63)]),
   ((.exchange 44 34 2),[(.neg 44),(.neg 34),(.pos 54),(.pos 64)]),
   ((.exchange 44 68 4),[(.neg 68),(.neg 44),(.pos 50),(.pos 60)]),
   ((.exchange 45 13 0),[(.neg 45),(.neg 13),(.pos 49),(.pos 52)]),
   ((.exchange 46 14 0),[(.neg 46),(.neg 14),(.pos 50),(.pos 53)]),
   ((.exchange 47 13 2),[(.neg 47),(.neg 13),(.pos 49),(.pos 52)]),
   ((.exchange 47 14 1),[(.neg 47),(.neg 14),(.pos 50),(.pos 53)]),
   ((.exchange 48 8 0),[(.neg 48),(.neg 8),(.pos 49),(.pos 50)]),
   ((.exchange 48 17 5),[(.neg 48),(.neg 17),(.pos 37),(.pos 58)]),
   ((.exchange 48 29 0),[(.neg 48),(.neg 29),(.pos 49),(.pos 68)]),
   ((.exchange 48 30 0),[(.neg 48),(.neg 30),(.pos 50),(.pos 68)]),
   ((.exchange 48 38 0),[(.neg 48),(.neg 38),(.pos 49),(.pos 50)]),
   ((.exchange 48 59 0),[(.neg 59),(.neg 48),(.pos 49),(.pos 68)]),
   ((.exchange 48 60 0),[(.neg 60),(.neg 48),(.pos 50),(.pos 68)]),
   ((.exchange 48 67 0),[(.neg 67),(.neg 48),(.pos 50),(.pos 68)]),
   ((.exchange 49 9 3),[(.neg 49),(.neg 9),(.pos 45),(.pos 52)]),
   ((.exchange 49 16 5),[(.neg 49),(.neg 16),(.pos 36),(.pos 59)]),
   ((.exchange 49 20 5),[(.neg 49),(.neg 20),(.pos 36),(.pos 38),(.pos 43),(.pos 59)]),
   ((.exchange 49 30 1),[(.neg 49),(.neg 30),(.pos 50),(.pos 68)]),
   ((.exchange 49 53 3),[(.neg 53),(.neg 49),(.pos 47),(.pos 52)]),
   ((.exchange 49 61 1),[(.neg 61),(.neg 49),(.pos 48),(.pos 54),(.pos 68)]),
   ((.exchange 49 63 5),[(.neg 63),(.neg 49),(.pos 38),(.pos 43),(.pos 59)]),
   ((.exchange 49 65 1),[(.neg 65),(.neg 49),(.pos 48),(.pos 68)]),
   ((.exchange 49 69 3),[(.neg 69),(.neg 49),(.pos 52),(.pos 66)]),
   ((.exchange 50 6 2),[(.neg 50),(.neg 6),(.pos 48),(.pos 49)]),
   ((.exchange 50 9 3),[(.neg 50),(.neg 9),(.pos 46),(.pos 47),(.pos 53)]),
   ((.exchange 50 10 3),[(.neg 50),(.neg 10),(.pos 46),(.pos 53)]),
   ((.exchange 50 11 3),[(.neg 50),(.neg 11),(.pos 47),(.pos 53)]),
   ((.exchange 50 13 2),[(.neg 50),(.neg 13),(.pos 49),(.pos 54)]),
   ((.exchange 50 16 5),[(.neg 50),(.neg 16),(.pos 37),(.pos 38),(.pos 60)]),
   ((.exchange 50 19 3),[(.neg 50),(.neg 19),(.pos 46),(.pos 47),(.pos 53),(.pos 67)]),
   ((.exchange 50 20 5),[(.neg 50),(.neg 20),(.pos 37),(.pos 44),(.pos 60)]),
   ((.exchange 50 33 3),[(.neg 50),(.neg 33),(.pos 53),(.pos 67)]),
   ((.exchange 50 43 2),[(.neg 50),(.neg 43),(.pos 49),(.pos 54)]),
   ((.exchange 50 61 2),[(.neg 61),(.neg 50),(.pos 48),(.pos 54),(.pos 68)]),
   ((.exchange 50 63 3),[(.neg 63),(.neg 50),(.pos 53),(.pos 67)]),
   ((.exchange 50 64 2),[(.neg 64),(.neg 50),(.pos 54),(.pos 68)]),
   ((.exchange 50 65 2),[(.neg 65),(.neg 50),(.pos 48),(.pos 68)]),
   ((.exchange 50 66 2),[(.neg 66),(.neg 50),(.pos 49),(.pos 68)]),
   ((.exchange 51 17 5),[(.neg 51),(.neg 17),(.pos 40),(.pos 42),(.pos 61)]),
   ((.exchange 51 32 0),[(.neg 51),(.neg 32),(.pos 52),(.pos 69)]),
   ((.exchange 51 33 0),[(.neg 51),(.neg 33),(.pos 53),(.pos 69)]),
   ((.exchange 51 41 0),[(.neg 51),(.neg 41),(.pos 52),(.pos 53)]),
   ((.exchange 51 63 0),[(.neg 63),(.neg 51),(.pos 53),(.pos 69)]),
   ((.exchange 52 6 4),[(.neg 52),(.neg 6),(.pos 45),(.pos 49)]),
   ((.exchange 52 23 5),[(.neg 52),(.neg 23),(.pos 43),(.pos 62)]),
   ((.exchange 52 33 1),[(.neg 52),(.neg 33),(.pos 53),(.pos 69)]),
   ((.exchange 52 36 4),[(.neg 52),(.neg 36),(.pos 45),(.pos 49)]),
   ((.exchange 52 46 1),[(.neg 52),(.neg 46),(.pos 51),(.pos 53)]),
   ((.exchange 52 59 5),[(.neg 59),(.neg 52),(.pos 43),(.pos 62)]),
   ((.exchange 52 63 1),[(.neg 63),(.neg 52),(.pos 53),(.pos 69)]),
   ((.exchange 52 64 5),[(.neg 64),(.neg 52),(.pos 43),(.pos 62)]),
   ((.exchange 52 67 1),[(.neg 67),(.neg 52),(.pos 53),(.pos 69)]),
   ((.exchange 52 68 4),[(.neg 68),(.neg 52),(.pos 49),(.pos 66)]),
   ((.exchange 53 24 5),[(.neg 53),(.neg 24),(.pos 44),(.pos 63)]),
   ((.exchange 53 30 4),[(.neg 53),(.neg 30),(.pos 50),(.pos 67)]),
   ((.exchange 53 34 2),[(.neg 53),(.neg 34),(.pos 54),(.pos 69)]),
   ((.exchange 53 37 4),[(.neg 53),(.neg 37),(.pos 46),(.pos 50)]),
   ((.exchange 53 38 4),[(.neg 53),(.neg 38),(.pos 47),(.pos 50)]),
   ((.exchange 53 45 2),[(.neg 53),(.neg 45),(.pos 51),(.pos 52)]),
   ((.exchange 53 49 4),[(.neg 53),(.neg 49),(.pos 47),(.pos 50)]),
   ((.exchange 53 61 2),[(.neg 61),(.neg 53),(.pos 51),(.pos 69)]),
   ((.exchange 53 62 2),[(.neg 62),(.neg 53),(.pos 52),(.pos 69)]),
   ((.exchange 53 64 2),[(.neg 64),(.neg 53),(.pos 54),(.pos 69)]),
   ((.exchange 53 65 2),[(.neg 65),(.neg 53),(.pos 51),(.pos 69)]),
   ((.exchange 54 8 4),[(.neg 54),(.neg 8),(.pos 49),(.pos 50)]),
   ((.exchange 54 23 5),[(.neg 54),(.neg 23),(.pos 43),(.pos 64)]),
   ((.exchange 54 30 4),[(.neg 54),(.neg 30),(.pos 50),(.pos 68)]),
   ((.exchange 54 32 3),[(.neg 54),(.neg 32),(.pos 52),(.pos 69)]),
   ((.exchange 54 33 3),[(.neg 54),(.neg 33),(.pos 53),(.pos 69)]),
   ((.exchange 54 63 5),[(.neg 63),(.neg 54),(.pos 44),(.pos 64)]),
   ((.exchange 54 67 4),[(.neg 67),(.neg 54),(.pos 50),(.pos 68)]),
   ((.exchange 55 23 0),[(.neg 55),(.neg 23),(.pos 59),(.pos 62)]),
   ((.exchange 55 51 1),[(.neg 55),(.neg 51),(.pos 61),(.pos 65)]),
   ((.exchange 56 24 0),[(.neg 56),(.neg 24),(.pos 60),(.pos 63)]),
   ((.exchange 56 51 2),[(.neg 56),(.neg 51),(.pos 61),(.pos 65)]),
   ((.exchange 57 23 2),[(.neg 57),(.neg 23),(.pos 59),(.pos 62)]),
   ((.exchange 57 24 1),[(.neg 57),(.neg 24),(.pos 60),(.pos 63)]),
   ((.exchange 58 6 6),[(.neg 58),(.neg 6),(.pos 36),(.pos 48)]),
   ((.exchange 58 18 0),[(.neg 58),(.neg 18),(.pos 59),(.pos 60)]),
   ((.exchange 58 29 0),[(.neg 58),(.neg 29),(.pos 59),(.pos 68)]),
   ((.exchange 58 30 0),[(.neg 58),(.neg 30),(.pos 60),(.pos 68)]),
   ((.exchange 58 47 6),[(.neg 58),(.neg 47),(.pos 36),(.pos 37),(.pos 48)]),
   ((.exchange 58 50 0),[(.neg 58),(.neg 50),(.pos 60),(.pos 68)]),
   ((.exchange 58 53 6),[(.neg 58),(.neg 53),(.pos 37),(.pos 42),(.pos 48)]),
   ((.exchange 58 57 0),[(.neg 58),(.neg 57),(.pos 59),(.pos 60)]),
   ((.exchange 59 6 6),[(.neg 59),(.neg 6),(.pos 36),(.pos 49)]),
   ((.exchange 59 9 3),[(.neg 59),(.neg 9),(.pos 55),(.pos 62),(.pos 66)]),
   ((.exchange 59 10 6),[(.neg 59),(.neg 10),(.pos 36),(.pos 38),(.pos 43),(.pos 49)]),
   ((.exchange 59 19 3),[(.neg 59),(.neg 19),(.pos 55),(.pos 62)]),
   ((.exchange 59 21 3),[(.neg 59),(.neg 21),(.pos 57),(.pos 62)]),
   ((.exchange 59 24 1),[(.neg 59),(.neg 24),(.pos 60),(.pos 64)]),
   ((.exchange 59 28 1),[(.neg 59),(.neg 28),(.pos 58),(.pos 68)]),
   ((.exchange 59 32 3),[(.neg 59),(.neg 32),(.pos 62),(.pos 66)]),
   ((.exchange 59 34 1),[(.neg 59),(.neg 34),(.pos 64),(.pos 68)]),
   ((.exchange 59 44 1),[(.neg 59),(.neg 44),(.pos 60),(.pos 64)]),
   ((.exchange 59 47 6),[(.neg 59),(.neg 47),(.pos 38),(.pos 49)]),
   ((.exchange 59 53 6),[(.neg 59),(.neg 53),(.pos 38),(.pos 43),(.pos 49)]),
   ((.exchange 59 56 1),[(.neg 59),(.neg 56),(.pos 58),(.pos 60)]),
   ((.exchange 59 63 1),[(.neg 63),(.neg 59),(.pos 60),(.pos 64)]),
   ((.exchange 59 67 1),[(.neg 67),(.neg 59),(.pos 60),(.pos 68)]),
   ((.exchange 59 69 1),[(.neg 69),(.neg 59),(.pos 64),(.pos 68)]),
   ((.exchange 59 69 3),[(.neg 69),(.neg 59),(.pos 62),(.pos 66)]),
   ((.exchange 60 6 6),[(.neg 60),(.neg 6),(.pos 37),(.pos 38),(.pos 50)]),
   ((.exchange 60 9 3),[(.neg 60),(.neg 9),(.pos 56),(.pos 57),(.pos 63),(.pos 67)]),
   ((.exchange 60 19 2),[(.neg 60),(.neg 19),(.pos 58),(.pos 59),(.pos 64)]),
   ((.exchange 60 23 2),[(.neg 60),(.neg 23),(.pos 59),(.pos 64)]),
   ((.exchange 60 31 2),[(.neg 60),(.neg 31),(.pos 58),(.pos 64),(.pos 68)]),
   ((.exchange 60 33 3),[(.neg 60),(.neg 33),(.pos 63),(.pos 67)]),
   ((.exchange 60 34 2),[(.neg 60),(.neg 34),(.pos 64),(.pos 68)]),
   ((.exchange 60 40 3),[(.neg 60),(.neg 40),(.pos 56),(.pos 63)]),
   ((.exchange 60 41 3),[(.neg 60),(.neg 41),(.pos 57),(.pos 63)]),
   ((.exchange 60 55 2),[(.neg 60),(.neg 55),(.pos 58),(.pos 59)]),
   ((.exchange 60 62 2),[(.neg 62),(.neg 60),(.pos 59),(.pos 64)]),
   ((.exchange 60 62 3),[(.neg 62),(.neg 60),(.pos 57),(.pos 63)]),
   ((.exchange 60 66 2),[(.neg 66),(.neg 60),(.pos 59),(.pos 68)]),
   ((.exchange 60 69 3),[(.neg 69),(.neg 60),(.pos 63),(.pos 67)]),
   ((.exchange 61 6 6),[(.neg 61),(.neg 6),(.pos 39),(.pos 42),(.pos 51)]),
   ((.exchange 61 41 0),[(.neg 61),(.neg 41),(.pos 62),(.pos 63)]),
   ((.exchange 61 52 0),[(.neg 61),(.neg 52),(.pos 62),(.pos 69)]),
   ((.exchange 61 53 6),[(.neg 61),(.neg 53),(.pos 40),(.pos 51)]),
   ((.exchange 62 13 6),[(.neg 62),(.neg 13),(.pos 43),(.pos 52)]),
   ((.exchange 62 24 1),[(.neg 62),(.neg 24),(.pos 63),(.pos 64)]),
   ((.exchange 62 29 4),[(.neg 62),(.neg 29),(.pos 59),(.pos 66)]),
   ((.exchange 62 31 1),[(.neg 62),(.neg 31),(.pos 61),(.pos 69)])]

theorem certificates_1_valid : ∀ oc ∈ certificates_1,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_2 : List (Origin 70 112 × List Sat.Literal) :=
  [((.exchange 62 33 1),[(.neg 62),(.neg 33),(.pos 63),(.pos 69)]),
   ((.exchange 62 34 1),[(.neg 62),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 62 36 4),[(.neg 62),(.neg 36),(.pos 55),(.pos 59)]),
   ((.exchange 62 40 1),[(.neg 62),(.neg 40),(.pos 61),(.pos 63)]),
   ((.exchange 62 44 1),[(.neg 62),(.neg 44),(.pos 63),(.pos 64)]),
   ((.exchange 62 48 4),[(.neg 62),(.neg 48),(.pos 55),(.pos 59),(.pos 66)]),
   ((.exchange 62 53 6),[(.neg 62),(.neg 53),(.pos 41),(.pos 52)]),
   ((.exchange 62 60 4),[(.neg 62),(.neg 60),(.pos 57),(.pos 59)]),
   ((.exchange 62 65 1),[(.neg 65),(.neg 62),(.pos 61),(.pos 69)]),
   ((.exchange 63 6 6),[(.neg 63),(.neg 6),(.pos 40),(.pos 41),(.pos 44),(.pos 53)]),
   ((.exchange 63 16 2),[(.neg 63),(.neg 16),(.pos 61),(.pos 62),(.pos 64)]),
   ((.exchange 63 19 2),[(.neg 63),(.neg 19),(.pos 61),(.pos 62)]),
   ((.exchange 63 23 2),[(.neg 63),(.neg 23),(.pos 62),(.pos 64)]),
   ((.exchange 63 30 4),[(.neg 63),(.neg 30),(.pos 60),(.pos 67)]),
   ((.exchange 63 34 2),[(.neg 63),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 63 43 2),[(.neg 63),(.neg 43),(.pos 62),(.pos 64)]),
   ((.exchange 63 68 2),[(.neg 68),(.neg 63),(.pos 64),(.pos 69)]),
   ((.exchange 64 6 6),[(.neg 64),(.neg 6),(.pos 42),(.pos 43),(.pos 54)]),
   ((.exchange 64 21 3),[(.neg 64),(.neg 21),(.pos 62),(.pos 63)]),
   ((.exchange 64 32 3),[(.neg 64),(.neg 32),(.pos 62),(.pos 69)]),
   ((.exchange 64 33 3),[(.neg 64),(.neg 33),(.pos 63),(.pos 69)]),
   ((.exchange 64 41 3),[(.neg 64),(.neg 41),(.pos 62),(.pos 63)]),
   ((.exchange 64 53 6),[(.neg 64),(.neg 53),(.pos 44),(.pos 54)]),
   ((.exchange 64 57 4),[(.neg 64),(.neg 57),(.pos 59),(.pos 60)]),
   ((.exchange 64 66 3),[(.neg 66),(.neg 64),(.pos 62),(.pos 69)]),
   ((.exchange 64 66 4),[(.neg 66),(.neg 64),(.pos 59),(.pos 68)]),
   ((.exchange 64 67 4),[(.neg 67),(.neg 64),(.pos 60),(.pos 68)]),
   ((.exchange 65 34 0),[(.neg 65),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 66 13 6),[(.neg 66),(.neg 13),(.pos 49),(.pos 52)]),
   ((.exchange 66 23 5),[(.neg 66),(.neg 23),(.pos 59),(.pos 62)]),
   ((.exchange 66 34 1),[(.neg 66),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 66 43 6),[(.neg 66),(.neg 43),(.pos 49),(.pos 52)]),
   ((.exchange 67 14 6),[(.neg 67),(.neg 14),(.pos 50),(.pos 53)]),
   ((.exchange 67 24 5),[(.neg 67),(.neg 24),(.pos 60),(.pos 63)]),
   ((.exchange 67 34 2),[(.neg 67),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 67 44 6),[(.neg 67),(.neg 44),(.pos 50),(.pos 53)]),
   ((.exchange 67 64 5),[(.neg 67),(.neg 64),(.pos 60),(.pos 63)]),
   ((.exchange 68 7 6),[(.neg 68),(.neg 7),(.pos 48),(.pos 50)]),
   ((.exchange 68 9 3),[(.neg 68),(.neg 9),(.pos 65),(.pos 66),(.pos 69)]),
   ((.exchange 68 14 6),[(.neg 68),(.neg 14),(.pos 50),(.pos 54)]),
   ((.exchange 68 16 5),[(.neg 68),(.neg 16),(.pos 58),(.pos 59)]),
   ((.exchange 68 23 5),[(.neg 68),(.neg 23),(.pos 59),(.pos 64)]),
   ((.exchange 68 24 5),[(.neg 68),(.neg 24),(.pos 60),(.pos 64)]),
   ((.exchange 68 33 3),[(.neg 68),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 68 36 6),[(.neg 68),(.neg 36),(.pos 48),(.pos 49)]),
   ((.exchange 68 37 5),[(.neg 68),(.neg 37),(.pos 58),(.pos 60)]),
   ((.exchange 68 37 6),[(.neg 68),(.neg 37),(.pos 48),(.pos 50)]),
   ((.exchange 68 38 5),[(.neg 68),(.neg 38),(.pos 59),(.pos 60)]),
   ((.exchange 68 38 6),[(.neg 68),(.neg 38),(.pos 49),(.pos 50)]),
   ((.exchange 68 40 5),[(.neg 68),(.neg 40),(.pos 58),(.pos 60),(.pos 64)]),
   ((.exchange 68 43 6),[(.neg 68),(.neg 43),(.pos 49),(.pos 54)]),
   ((.exchange 68 44 6),[(.neg 68),(.neg 44),(.pos 50),(.pos 54)]),
   ((.exchange 68 52 3),[(.neg 68),(.neg 52),(.pos 66),(.pos 69)]),
   ((.exchange 68 62 3),[(.neg 68),(.neg 62),(.pos 66),(.pos 69)]),
   ((.exchange 69 7 6),[(.neg 69),(.neg 7),(.pos 51),(.pos 53),(.pos 54)]),
   ((.exchange 69 10 6),[(.neg 69),(.neg 10),(.pos 51),(.pos 53)]),
   ((.exchange 69 11 6),[(.neg 69),(.neg 11),(.pos 52),(.pos 53)]),
   ((.exchange 69 24 5),[(.neg 69),(.neg 24),(.pos 63),(.pos 64)]),
   ((.exchange 69 28 4),[(.neg 69),(.neg 28),(.pos 65),(.pos 68)]),
   ((.exchange 69 29 4),[(.neg 69),(.neg 29),(.pos 66),(.pos 68)]),
   ((.exchange 69 30 4),[(.neg 69),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 69 37 6),[(.neg 69),(.neg 37),(.pos 51),(.pos 53),(.pos 54)]),
   ((.exchange 69 38 4),[(.neg 69),(.neg 38),(.pos 66),(.pos 67),(.pos 68)]),
   ((.exchange 69 39 5),[(.neg 69),(.neg 39),(.pos 61),(.pos 62)]),
   ((.exchange 69 40 6),[(.neg 69),(.neg 40),(.pos 51),(.pos 53)]),
   ((.exchange 69 41 6),[(.neg 69),(.neg 41),(.pos 52),(.pos 53)]),
   ((.exchange 69 43 6),[(.neg 69),(.neg 43),(.pos 52),(.pos 54)]),
   ((.exchange 69 44 6),[(.neg 69),(.neg 44),(.pos 53),(.pos 54)]),
   ((.exchange 69 48 4),[(.neg 69),(.neg 48),(.pos 65),(.pos 68)]),
   ((.exchange 69 59 4),[(.neg 69),(.neg 59),(.pos 66),(.pos 68)]),
   ((.exchange 69 59 5),[(.neg 69),(.neg 59),(.pos 62),(.pos 64)]),
   (.newPoint,[(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 0),[(.neg 69),(.neg 68),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 51),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 61),(.pos 64),(.pos 65),(.pos 66),(.pos 67)]),
   ((.excluded 1),[(.neg 69),(.neg 68),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 58),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 48),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 49),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 59),(.pos 62),(.pos 65),(.pos 66),(.pos 67)]),
   ((.excluded 2),[(.neg 69),(.neg 68),(.neg 64),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 54),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 50),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 65),(.pos 66),(.pos 67)]),
   ((.excluded 3),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 4),[(.neg 69),(.neg 68),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57),(.pos 65),(.pos 66),(.pos 67)]),
   ((.excluded 5),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 54),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 64),(.pos 68)]),
   ((.excluded 6),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 48),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 58),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 7),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 48),(.pos 51),(.pos 54),(.pos 58),(.pos 61),(.pos 64)]),
   ((.excluded 8),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 49),(.pos 53),(.pos 59),(.pos 63)]),
   ((.excluded 9),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 49),(.pos 59),(.pos 69)]),
   ((.excluded 10),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 49),(.pos 59)]),
   ((.excluded 11),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 53),(.pos 63),(.pos 68)]),
   ((.excluded 12),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 53),(.pos 63)]),
   ((.excluded 13),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 50),(.pos 52),(.pos 60),(.pos 62)]),
   ((.excluded 14),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 50),(.pos 60),(.pos 69)]),
   ((.excluded 15),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 50),(.pos 60)]),
   ((.excluded 16),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 52),(.pos 62),(.pos 68)]),
   ((.excluded 17),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 52),(.pos 62)]),
   ((.excluded 18),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 68)]),
   ((.excluded 19),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 69)]),
   ((.excluded 20),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44)]),
   ((.excluded 21),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 22),[(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 23),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 24),[(.neg 69),(.neg 68),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 58),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 51),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 59),(.pos 62),(.pos 65),(.pos 66),(.pos 67)]),
   ((.excluded 25),[(.neg 69),(.neg 68),(.neg 64),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 51),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 65),(.pos 66),(.pos 67)]),
   ((.excluded 26),[(.neg 69),(.neg 68),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 51),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 65),(.pos 66),(.pos 67)]),
   ((.excluded 27),[(.neg 69),(.neg 68),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 48),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 45),(.pos 46),(.pos 47),(.pos 49),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 61),(.pos 64),(.pos 65),(.pos 66),(.pos 67)]),
   ((.excluded 28),[(.neg 69),(.neg 68),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 54),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 45),(.pos 46),(.pos 47),(.pos 50),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 61),(.pos 64),(.pos 65),(.pos 66),(.pos 67)]),
   ((.excluded 29),[(.neg 69),(.neg 68),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 61),(.pos 64),(.pos 65),(.pos 66),(.pos 67)]),
   ((.excluded 30),[(.neg 69),(.neg 68),(.neg 64),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 48),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 45),(.pos 46),(.pos 47),(.pos 49),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 65),(.pos 66),(.pos 67)]),
   ((.excluded 31),[(.neg 69),(.neg 68),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 48),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 45),(.pos 46),(.pos 47),(.pos 49),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 65),(.pos 66),(.pos 67)]),
   ((.excluded 32),[(.neg 69),(.neg 68),(.neg 64),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 65),(.pos 66),(.pos 67)]),
   ((.excluded 33),[(.neg 69),(.neg 68),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 58),(.neg 54),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 45),(.pos 46),(.pos 47),(.pos 50),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 59),(.pos 62),(.pos 65),(.pos 66),(.pos 67)]),
   ((.excluded 34),[(.neg 69),(.neg 68),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 45),(.pos 46),(.pos 47),(.pos 50),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 65),(.pos 66),(.pos 67)]),
   ((.excluded 35),[(.neg 69),(.neg 68),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57),(.pos 59),(.pos 62),(.pos 65),(.pos 66),(.pos 67)]),
   ((.excluded 36),[(.neg 69),(.neg 68),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57),(.pos 65),(.pos 66),(.pos 67)]),
   ((.excluded 37),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 54),(.pos 62),(.pos 68)]),
   ((.excluded 38),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 54),(.pos 63),(.pos 68)]),
   ((.excluded 39),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 54),(.pos 68)]),
   ((.excluded 40),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 48),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 59),(.pos 69)]),
   ((.excluded 41),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 48),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 60),(.pos 69)]),
   ((.excluded 42),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 48),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 69)]),
   ((.excluded 43),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 48),(.pos 51),(.pos 54),(.pos 59),(.pos 63)]),
   ((.excluded 44),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 48),(.pos 51),(.pos 54),(.pos 59)]),
   ((.excluded 45),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 48),(.pos 51),(.pos 54),(.pos 63)]),
   ((.excluded 46),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 48),(.pos 51),(.pos 54),(.pos 60),(.pos 62)]),
   ((.excluded 47),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 48),(.pos 51),(.pos 54),(.pos 60)]),
   ((.excluded 48),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 48),(.pos 51),(.pos 54),(.pos 62)]),
   ((.excluded 49),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 48),(.pos 51),(.pos 54)]),
   ((.excluded 50),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 52),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 64),(.pos 68)]),
   ((.excluded 51),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 53),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 64),(.pos 68)]),
   ((.excluded 52),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 64),(.pos 68)]),
   ((.excluded 53),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 49),(.pos 58),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 54),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 50),(.pos 58),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 55),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 58),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)])]

theorem certificates_2_valid : ∀ oc ∈ certificates_2,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_3 : List (Origin 70 112 × List Sat.Literal) :=
  [((.excluded 56),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 49),(.pos 53),(.pos 58),(.pos 61),(.pos 64)]),
   ((.excluded 57),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 49),(.pos 58),(.pos 61),(.pos 64)]),
   ((.excluded 58),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 53),(.pos 58),(.pos 61),(.pos 64)]),
   ((.excluded 59),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 50),(.pos 52),(.pos 58),(.pos 61),(.pos 64)]),
   ((.excluded 60),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 50),(.pos 58),(.pos 61),(.pos 64)]),
   ((.excluded 61),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 52),(.pos 58),(.pos 61),(.pos 64)]),
   ((.excluded 62),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 58),(.pos 61),(.pos 64)]),
   ((.excluded 63),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 52),(.pos 63),(.pos 68)]),
   ((.excluded 64),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 52),(.pos 68)]),
   ((.excluded 65),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 63),(.pos 68)]),
   ((.excluded 66),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 53),(.pos 62),(.pos 68)]),
   ((.excluded 67),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 53),(.pos 68)]),
   ((.excluded 68),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 62),(.pos 68)]),
   ((.excluded 69),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 68)]),
   ((.excluded 70),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 49),(.pos 60),(.pos 69)]),
   ((.excluded 71),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 49),(.pos 69)]),
   ((.excluded 72),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 60),(.pos 69)]),
   ((.excluded 73),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 50),(.pos 59),(.pos 69)]),
   ((.excluded 74),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 50),(.pos 69)]),
   ((.excluded 75),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 59),(.pos 69)]),
   ((.excluded 76),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 69)]),
   ((.excluded 77),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 49),(.pos 63)]),
   ((.excluded 78),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 49),(.pos 53),(.pos 60),(.pos 62)]),
   ((.excluded 79),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 49),(.pos 53),(.pos 60)]),
   ((.excluded 80),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 49),(.pos 53),(.pos 62)]),
   ((.excluded 81),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 49),(.pos 53)]),
   ((.excluded 82),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 49),(.pos 60),(.pos 62)]),
   ((.excluded 83),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 49),(.pos 60)]),
   ((.excluded 84),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 49),(.pos 62)]),
   ((.excluded 85),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 49)]),
   ((.excluded 86),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 53),(.pos 59)]),
   ((.excluded 87),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 53),(.pos 60),(.pos 62)]),
   ((.excluded 88),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 53),(.pos 60)]),
   ((.excluded 89),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 53),(.pos 62)]),
   ((.excluded 90),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 53)]),
   ((.excluded 91),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 52),(.pos 60)]),
   ((.excluded 92),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 60),(.pos 62)]),
   ((.excluded 93),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 60)]),
   ((.excluded 94),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 50),(.pos 62)]),
   ((.excluded 95),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 62)]),
   ((.excluded 96),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 50),(.pos 52),(.pos 59),(.pos 63)]),
   ((.excluded 97),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 50),(.pos 52),(.pos 59)]),
   ((.excluded 98),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 50),(.pos 52),(.pos 63)]),
   ((.excluded 99),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 50),(.pos 52)]),
   ((.excluded 100),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 50),(.pos 59),(.pos 63)]),
   ((.excluded 101),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 50),(.pos 59)]),
   ((.excluded 102),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 50),(.pos 63)]),
   ((.excluded 103),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 50)]),
   ((.excluded 104),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 52),(.pos 59),(.pos 63)]),
   ((.excluded 105),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 52),(.pos 59)]),
   ((.excluded 106),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 52),(.pos 63)]),
   ((.excluded 107),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 52)]),
   ((.excluded 108),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 59),(.pos 63)]),
   ((.excluded 109),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 59)]),
   ((.excluded 110),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 63)]),
   ((.excluded 111),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42)])]

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
        Papers.RationalityTen.MatroidChecked.FastSemanticChecks.RawWitness 8 (N7R4.familyMasks.get 47)
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


end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C47

/- Source: MatroidCatalogue/Cases/N8R4C47Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C47

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
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C47.formula []
    exact Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C47.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 8 4 (target w),family_mem 8 4 (target w) hw.1,?_⟩
    exact validWitness_sound 8 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C47


end
end
end BundlePart3

section BundlePart4
/- Source: MatroidChecked/SemanticChunks/Cases06Part05.lean -/




@[expose] public section
noncomputable section

/- Source: MatroidCatalogue/Cases/N8R4C48Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C48

abbrev U := N8R4.grid
noncomputable def old : Finset (Finset (Fin 8)) := N7R4.family 48
noncomputable def newIndexTree : Table ℕ := (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf 35) (.leaf 36)) (.node 3 (.leaf 37) (.leaf 38))) (.node 6 (.node 5 (.leaf 39) (.leaf 40)) (.node 7 (.leaf 41) (.leaf 42)))) (.node 12 (.node 10 (.node 9 (.leaf 43) (.leaf 44)) (.node 11 (.leaf 45) (.leaf 46))) (.node 14 (.node 13 (.leaf 47) (.leaf 48)) (.node 15 (.leaf 49) (.node 16 (.leaf 50) (.leaf 51)))))) (.node 26 (.node 21 (.node 19 (.node 18 (.leaf 52) (.leaf 53)) (.node 20 (.leaf 54) (.leaf 55))) (.node 23 (.node 22 (.leaf 56) (.leaf 57)) (.node 24 (.leaf 58) (.node 25 (.leaf 59) (.leaf 60))))) (.node 30 (.node 28 (.node 27 (.leaf 61) (.leaf 62)) (.node 29 (.leaf 63) (.leaf 64))) (.node 32 (.node 31 (.leaf 65) (.leaf 66)) (.node 33 (.leaf 67) (.node 34 (.leaf 68) (.leaf 69)))))))
noncomputable def newIndex (i : Fin 35) : Fin 70 := Fin.ofNat 70 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 39 (.node 19 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (23463829504,128,4151490)) (.leaf (22958971904,128,4141410))) (.node 3 (.leaf (788249600,182,2049677)) (.leaf (23605525504,191,6247171)))) (.node 6 (.node 5 (.leaf (12575268864,128,4147738)) (.leaf (11868888064,128,4130602))) (.node 7 (.leaf (12616203264,191,6232611)) (.node 8 (.leaf (32665681920,120,4151504)) (.leaf (34352390144,152,8345736)))))) (.node 14 (.node 11 (.node 10 (.leaf (33746770944,152,8332128)) (.leaf (33118059520,184,12527816))) (.node 12 (.leaf (34191801344,185,10430021)) (.node 13 (.leaf (33252408320,195,12534872)) (.leaf (34326150144,196,12534298))))) (.node 16 (.node 15 (.leaf (33151646720,195,12527816)) (.leaf (34225388544,196,12523714))) (.node 17 (.leaf (33285995520,207,12535432)) (.node 18 (.leaf (34359737344,208,12535432)) (.leaf (787481470,266,3951514))))))) (.node 29 (.node 24 (.node 21 (.node 20 (.leaf (769918,266,2345882)) (.leaf (788250494,339,4484963))) (.node 22 (.leaf (22959465342,318,7759304)) (.node 23 (.leaf (23605388158,320,12412673)) (.leaf (22959603582,320,11256217))))) (.node 26 (.node 25 (.leaf (23463337854,318,7529928)) (.leaf (23604895614,320,12403097))) (.node 27 (.leaf (23463968638,320,11265793)) (.node 28 (.leaf (23605526398,340,16433858)) (.leaf (33117619070,313,12465544)))))) (.node 34 (.node 31 (.node 30 (.leaf (33251836798,314,12436592)) (.leaf (33151173502,314,12429704))) (.node 32 (.leaf (33285391230,315,14473424)) (.node 33 (.leaf (11869578110,318,7744632)) (.leaf (12616164222,320,12401697))))) (.node 36 (.node 35 (.leaf (33747362686,325,12306056)) (.leaf (34191958910,332,14599816))) (.node 37 (.leaf (34326176638,333,14599760)) (.node 38 (.leaf (34225513342,333,14596232)) (.leaf (34359731070,334,14599816)))))))) (.node 59 (.node 49 (.node 44 (.node 41 (.node 40 (.leaf (32666124158,313,11777416)) (.leaf (32666255230,314,11519088))) (.node 42 (.leaf (32666156926,314,11512200)) (.node 43 (.leaf (32666287998,315,13097168)) (.leaf (11869618046,320,11241713))))) (.node 46 (.node 45 (.leaf (33747206014,332,14131992)) (.leaf (33747337086,333,14131936))) (.node 47 (.leaf (33747238782,333,14128408)) (.node 48 (.leaf (33747369854,334,14131992)) (.leaf (12574580606,318,7515256)))))) (.node 54 (.node 51 (.node 50 (.leaf (12615475070,320,12388593)) (.leaf (12575309694,320,11254817))) (.node 52 (.leaf (12616204158,340,16422938)) (.node 53 (.leaf (34351800190,325,12535432)) (.leaf (34191368062,332,14590744))))) (.node 56 (.node 55 (.leaf (34325585790,333,14590688)) (.leaf (34224922494,333,14587160))) (.node 57 (.leaf (34359140222,334,14590744)) (.node 58 (.leaf (34352234366,332,14141064)) (.leaf (34352365438,333,14141008))))))) (.node 69 (.node 64 (.node 61 (.node 60 (.leaf (34352267134,333,14137480)) (.leaf (34352398206,334,14141064))) (.node 62 (.leaf (33285832574,341,16434824)) (.node 63 (.leaf (34359574398,342,16434824)) (.leaf (33151745918,343,16205448))))) (.node 66 (.node 65 (.leaf (34225487742,344,16205448)) (.leaf (33285963646,345,16434264))) (.node 67 (.leaf (34359705470,346,16434264)) (.node 68 (.leaf (33252310910,343,16434824)) (.leaf (34326052734,344,16434824)))))) (.node 74 (.node 71 (.node 70 (.leaf (33285865342,345,16427208)) (.leaf (34359607166,346,16427208))) (.node 72 (.leaf (33118224254,341,16205448)) (.node 73 (.leaf (34191966078,342,16205448)) (.leaf (33252441982,345,16204888))))) (.node 76 (.node 75 (.leaf (34326183806,346,16204888)) (.leaf (33151778686,345,16197832))) (.node 77 (.leaf (34225520510,346,16197832)) (.node 78 (.leaf (33285996414,347,16434824)) (.leaf (34359738238,348,16434824)))))))))

noncomputable def models (i : Fin 79) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 79) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 79) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 70, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (7 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 70, (7 : Fin 8) ∈ U i → ∃ j : Fin 35, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C48

/- Source: MatroidCatalogue/Cases/N8R4C48Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C48


noncomputable def certificates_0 : List (Origin 70 79 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.neg 2)]),
   ((.fixed 3),[(.neg 3)]),
   ((.fixed 4),[(.neg 4)]),
   ((.fixed 5),[(.neg 5)]),
   ((.fixed 6),[(.pos 6)]),
   ((.fixed 7),[(.pos 7)]),
   ((.fixed 8),[(.pos 8)]),
   ((.fixed 9),[(.pos 9)]),
   ((.fixed 10),[(.pos 10)]),
   ((.fixed 11),[(.pos 11)]),
   ((.fixed 12),[(.neg 12)]),
   ((.fixed 13),[(.pos 13)]),
   ((.fixed 14),[(.pos 14)]),
   ((.fixed 15),[(.neg 15)]),
   ((.fixed 16),[(.pos 16)]),
   ((.fixed 17),[(.pos 17)]),
   ((.fixed 18),[(.pos 18)]),
   ((.fixed 19),[(.pos 19)]),
   ((.fixed 20),[(.pos 20)]),
   ((.fixed 21),[(.pos 21)]),
   ((.fixed 22),[(.neg 22)]),
   ((.fixed 23),[(.pos 23)]),
   ((.fixed 24),[(.pos 24)]),
   ((.fixed 25),[(.pos 25)]),
   ((.fixed 26),[(.pos 26)]),
   ((.fixed 27),[(.pos 27)]),
   ((.fixed 28),[(.pos 28)]),
   ((.fixed 29),[(.neg 29)]),
   ((.fixed 30),[(.pos 30)]),
   ((.fixed 31),[(.pos 31)]),
   ((.fixed 32),[(.pos 32)]),
   ((.fixed 33),[(.neg 33)]),
   ((.fixed 34),[(.pos 34)]),
   ((.exchange 6 41 5),[(.neg 41),(.neg 6),(.pos 0),(.pos 2),(.pos 36)]),
   ((.exchange 6 46 3),[(.neg 46),(.neg 6),(.pos 5),(.pos 45)]),
   ((.exchange 6 47 3),[(.neg 47),(.neg 6),(.pos 5),(.pos 45)]),
   ((.exchange 6 51 1),[(.neg 51),(.neg 6),(.pos 12),(.pos 48)]),
   ((.exchange 6 54 1),[(.neg 54),(.neg 6),(.pos 12),(.pos 48)]),
   ((.exchange 6 59 0),[(.neg 59),(.neg 6),(.pos 29),(.pos 49)]),
   ((.exchange 6 66 0),[(.neg 66),(.neg 6),(.pos 29),(.pos 49)]),
   ((.exchange 6 68 0),[(.neg 68),(.neg 6),(.pos 29),(.pos 49)]),
   ((.exchange 7 41 5),[(.neg 41),(.neg 7),(.pos 0),(.pos 3),(.pos 37)]),
   ((.exchange 7 45 3),[(.neg 45),(.neg 7),(.pos 5),(.pos 46)]),
   ((.exchange 7 47 3),[(.neg 47),(.neg 7),(.pos 5),(.pos 46)]),
   ((.exchange 8 41 5),[(.neg 41),(.neg 8),(.pos 4),(.pos 38)]),
   ((.exchange 8 45 3),[(.neg 45),(.neg 8),(.pos 5),(.pos 47)]),
   ((.exchange 8 46 3),[(.neg 46),(.neg 8),(.pos 5),(.pos 47)]),
   ((.exchange 9 41 5),[(.neg 41),(.neg 9),(.pos 1),(.pos 39)]),
   ((.exchange 9 48 1),[(.neg 48),(.neg 9),(.pos 12),(.pos 51)]),
   ((.exchange 9 54 1),[(.neg 54),(.neg 9),(.pos 12),(.pos 51)]),
   ((.exchange 10 41 5),[(.neg 41),(.neg 10),(.pos 1),(.pos 40)]),
   ((.exchange 10 63 0),[(.neg 63),(.neg 10),(.pos 33),(.pos 53)]),
   ((.exchange 10 67 0),[(.neg 67),(.neg 10),(.pos 33),(.pos 53)]),
   ((.exchange 10 69 0),[(.neg 69),(.neg 10),(.pos 33),(.pos 53)]),
   ((.exchange 11 36 5),[(.neg 36),(.neg 11),(.pos 1),(.pos 4),(.pos 41)]),
   ((.exchange 11 37 5),[(.neg 37),(.neg 11),(.pos 1),(.pos 4),(.pos 41)]),
   ((.exchange 11 38 5),[(.neg 38),(.neg 11),(.pos 4),(.pos 41)]),
   ((.exchange 11 39 5),[(.neg 39),(.neg 11),(.pos 1),(.pos 41)]),
   ((.exchange 11 40 5),[(.neg 40),(.neg 11),(.pos 1),(.pos 41)]),
   ((.exchange 11 43 5),[(.neg 43),(.neg 11),(.pos 4),(.pos 41)]),
   ((.exchange 11 44 5),[(.neg 44),(.neg 11),(.pos 4),(.pos 41)]),
   ((.exchange 13 41 5),[(.neg 41),(.neg 13),(.pos 4),(.pos 43)]),
   ((.exchange 13 48 1),[(.neg 48),(.neg 13),(.pos 12),(.pos 54)]),
   ((.exchange 14 41 5),[(.neg 41),(.neg 14),(.pos 4),(.pos 44)]),
   ((.exchange 16 49 0),[(.neg 49),(.neg 16),(.pos 29),(.pos 59)]),
   ((.exchange 16 56 3),[(.neg 56),(.neg 16),(.pos 15),(.pos 55)]),
   ((.exchange 16 57 3),[(.neg 57),(.neg 16),(.pos 15),(.pos 55)]),
   ((.exchange 16 61 1),[(.neg 61),(.neg 16),(.pos 22),(.pos 58)]),
   ((.exchange 16 64 1),[(.neg 64),(.neg 16),(.pos 22),(.pos 58)]),
   ((.exchange 16 66 0),[(.neg 66),(.neg 16),(.pos 29),(.pos 59)]),
   ((.exchange 16 68 0),[(.neg 68),(.neg 16),(.pos 29),(.pos 59)]),
   ((.exchange 17 55 3),[(.neg 55),(.neg 17),(.pos 15),(.pos 56)]),
   ((.exchange 17 57 3),[(.neg 57),(.neg 17),(.pos 15),(.pos 56)]),
   ((.exchange 18 55 3),[(.neg 55),(.neg 18),(.pos 15),(.pos 57)]),
   ((.exchange 18 56 3),[(.neg 56),(.neg 18),(.pos 15),(.pos 57)]),
   ((.exchange 19 58 1),[(.neg 58),(.neg 19),(.pos 22),(.pos 61)]),
   ((.exchange 19 64 1),[(.neg 64),(.neg 19),(.pos 22),(.pos 61)]),
   ((.exchange 20 53 0),[(.neg 53),(.neg 20),(.pos 33),(.pos 63)]),
   ((.exchange 20 67 0),[(.neg 67),(.neg 20),(.pos 33),(.pos 63)]),
   ((.exchange 20 69 0),[(.neg 69),(.neg 20),(.pos 33),(.pos 63)]),
   ((.exchange 23 58 1),[(.neg 58),(.neg 23),(.pos 22),(.pos 64)]),
   ((.exchange 23 61 1),[(.neg 61),(.neg 23),(.pos 22),(.pos 64)]),
   ((.exchange 25 49 0),[(.neg 49),(.neg 25),(.pos 29),(.pos 66)]),
   ((.exchange 25 59 0),[(.neg 59),(.neg 25),(.pos 29),(.pos 66)]),
   ((.exchange 25 68 0),[(.neg 68),(.neg 25),(.pos 29),(.pos 66)]),
   ((.exchange 26 53 0),[(.neg 53),(.neg 26),(.pos 33),(.pos 67)]),
   ((.exchange 26 63 0),[(.neg 63),(.neg 26),(.pos 33),(.pos 67)]),
   ((.exchange 26 69 0),[(.neg 69),(.neg 26),(.pos 33),(.pos 67)]),
   ((.exchange 28 49 0),[(.neg 49),(.neg 28),(.pos 29),(.pos 68)]),
   ((.exchange 28 59 0),[(.neg 59),(.neg 28),(.pos 29),(.pos 68)]),
   ((.exchange 28 66 0),[(.neg 66),(.neg 28),(.pos 29),(.pos 68)]),
   ((.exchange 31 53 0),[(.neg 53),(.neg 31),(.pos 33),(.pos 69)]),
   ((.exchange 31 63 0),[(.neg 63),(.neg 31),(.pos 33),(.pos 69)]),
   ((.exchange 31 67 0),[(.neg 67),(.neg 31),(.pos 33),(.pos 69)]),
   ((.exchange 35 6 7),[(.neg 35),(.neg 6),(.pos 0),(.pos 5)]),
   ((.exchange 36 25 3),[(.neg 36),(.neg 25),(.pos 45),(.pos 55)]),
   ((.exchange 36 28 1),[(.neg 36),(.neg 28),(.pos 48),(.pos 58)]),
   ((.exchange 37 25 3),[(.neg 37),(.neg 25),(.pos 35),(.pos 46),(.pos 56)]),
   ((.exchange 37 30 0),[(.neg 37),(.neg 30),(.pos 50),(.pos 60)]),
   ((.exchange 38 25 3),[(.neg 38),(.neg 25),(.pos 35),(.pos 47),(.pos 57)]),
   ((.exchange 39 31 1),[(.neg 39),(.neg 31),(.pos 51),(.pos 61)]),
   ((.exchange 39 32 0),[(.neg 39),(.neg 32),(.pos 52),(.pos 62)]),
   ((.exchange 39 66 4),[(.neg 66),(.neg 39),(.pos 45),(.pos 55)]),
   ((.exchange 40 66 4),[(.neg 66),(.neg 40),(.pos 35),(.pos 46),(.pos 56)]),
   ((.exchange 41 32 2),[(.neg 41),(.neg 32),(.pos 52),(.pos 62)]),
   ((.exchange 41 66 4),[(.neg 66),(.neg 41),(.pos 47),(.pos 57)]),
   ((.exchange 42 6 7),[(.neg 42),(.neg 6),(.pos 2),(.pos 12)]),
   ((.exchange 43 28 1),[(.neg 43),(.neg 28),(.pos 42),(.pos 54),(.pos 64)]),
   ((.exchange 45 13 0),[(.neg 45),(.neg 13),(.pos 49),(.pos 52)]),
   ((.exchange 45 16 5),[(.neg 45),(.neg 16),(.pos 36),(.pos 55)]),
   ((.exchange 45 54 0),[(.neg 54),(.neg 45),(.pos 49),(.pos 52)]),
   ((.exchange 45 64 1),[(.neg 64),(.neg 45),(.pos 48),(.pos 51),(.pos 65)]),
   ((.exchange 46 14 0),[(.neg 46),(.neg 14),(.pos 50),(.pos 53)]),
   ((.exchange 46 16 5),[(.neg 46),(.neg 16),(.pos 35),(.pos 37),(.pos 56)]),
   ((.exchange 46 44 0),[(.neg 46),(.neg 44),(.pos 50),(.pos 53)]),
   ((.exchange 46 68 0),[(.neg 68),(.neg 46),(.pos 50),(.pos 67)]),
   ((.exchange 46 68 2),[(.neg 68),(.neg 46),(.pos 48),(.pos 65)]),
   ((.exchange 47 16 5),[(.neg 47),(.neg 16),(.pos 35),(.pos 38),(.pos 57)]),
   ((.exchange 47 44 1),[(.neg 47),(.neg 44),(.pos 50),(.pos 53)]),
   ((.exchange 47 65 2),[(.neg 65),(.neg 47),(.pos 45),(.pos 66)]),
   ((.exchange 48 8 0),[(.neg 48),(.neg 8),(.pos 49),(.pos 50)]),
   ((.exchange 48 23 5),[(.neg 48),(.neg 23),(.pos 36),(.pos 42),(.pos 58)]),
   ((.exchange 48 25 3),[(.neg 48),(.neg 25),(.pos 45),(.pos 65)]),
   ((.exchange 48 30 0),[(.neg 48),(.neg 30),(.pos 50),(.pos 68)]),
   ((.exchange 48 57 5),[(.neg 57),(.neg 48),(.pos 36),(.pos 37),(.pos 58)]),
   ((.exchange 48 67 0),[(.neg 67),(.neg 48),(.pos 50),(.pos 68)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_1 : List (Origin 70 79 × List Sat.Literal) :=
  [((.exchange 49 7 1),[(.neg 49),(.neg 7),(.pos 48),(.pos 50)]),
   ((.exchange 49 9 3),[(.neg 49),(.neg 9),(.pos 45),(.pos 52)]),
   ((.exchange 49 39 3),[(.neg 49),(.neg 39),(.pos 45),(.pos 52)]),
   ((.exchange 49 51 3),[(.neg 51),(.neg 49),(.pos 45),(.pos 52)]),
   ((.exchange 50 6 2),[(.neg 50),(.neg 6),(.pos 48),(.pos 49)]),
   ((.exchange 50 25 3),[(.neg 50),(.neg 25),(.pos 46),(.pos 47),(.pos 67)]),
   ((.exchange 50 28 2),[(.neg 50),(.neg 28),(.pos 48),(.pos 68)]),
   ((.exchange 50 32 2),[(.neg 50),(.neg 32),(.pos 49),(.pos 54),(.pos 68)]),
   ((.exchange 50 40 3),[(.neg 50),(.neg 40),(.pos 46),(.pos 53)]),
   ((.exchange 50 51 3),[(.neg 51),(.neg 50),(.pos 46),(.pos 53)]),
   ((.exchange 50 52 3),[(.neg 52),(.neg 50),(.pos 47),(.pos 53)]),
   ((.exchange 50 56 3),[(.neg 56),(.neg 50),(.pos 46),(.pos 67)]),
   ((.exchange 50 57 5),[(.neg 57),(.neg 50),(.pos 38),(.pos 60)]),
   ((.exchange 50 69 2),[(.neg 69),(.neg 50),(.pos 54),(.pos 68)]),
   ((.exchange 51 11 0),[(.neg 51),(.neg 11),(.pos 52),(.pos 53)]),
   ((.exchange 51 26 4),[(.neg 51),(.neg 26),(.pos 46),(.pos 65)]),
   ((.exchange 51 32 0),[(.neg 51),(.neg 32),(.pos 52),(.pos 69)]),
   ((.exchange 51 47 0),[(.neg 51),(.neg 47),(.pos 52),(.pos 53)]),
   ((.exchange 51 57 5),[(.neg 57),(.neg 51),(.pos 39),(.pos 40),(.pos 61)]),
   ((.exchange 51 62 5),[(.neg 62),(.neg 51),(.pos 39),(.pos 61)]),
   ((.exchange 51 66 0),[(.neg 66),(.neg 51),(.pos 52),(.pos 69)]),
   ((.exchange 52 16 5),[(.neg 52),(.neg 16),(.pos 39),(.pos 43),(.pos 62)]),
   ((.exchange 52 28 1),[(.neg 52),(.neg 28),(.pos 51),(.pos 54),(.pos 69)]),
   ((.exchange 52 30 4),[(.neg 52),(.neg 30),(.pos 47),(.pos 49),(.pos 66)]),
   ((.exchange 52 37 1),[(.neg 52),(.neg 37),(.pos 51),(.pos 53),(.pos 54)]),
   ((.exchange 52 48 4),[(.neg 52),(.neg 48),(.pos 45),(.pos 49)]),
   ((.exchange 52 60 4),[(.neg 60),(.neg 52),(.pos 47),(.pos 49),(.pos 66)]),
   ((.exchange 53 7 4),[(.neg 53),(.neg 7),(.pos 46),(.pos 50)]),
   ((.exchange 53 8 4),[(.neg 53),(.neg 8),(.pos 47),(.pos 50)]),
   ((.exchange 53 13 2),[(.neg 53),(.neg 13),(.pos 52),(.pos 54)]),
   ((.exchange 53 48 4),[(.neg 53),(.neg 48),(.pos 46),(.pos 50)]),
   ((.exchange 54 23 5),[(.neg 54),(.neg 23),(.pos 43),(.pos 64)]),
   ((.exchange 54 30 4),[(.neg 54),(.neg 30),(.pos 50),(.pos 68)]),
   ((.exchange 54 57 3),[(.neg 57),(.neg 54),(.pos 52),(.pos 53),(.pos 69)]),
   ((.exchange 54 57 4),[(.neg 57),(.neg 54),(.pos 49),(.pos 50),(.pos 68)]),
   ((.exchange 54 57 5),[(.neg 57),(.neg 54),(.pos 43),(.pos 44),(.pos 64)]),
   ((.exchange 54 67 4),[(.neg 67),(.neg 54),(.pos 50),(.pos 68)]),
   ((.exchange 55 9 6),[(.neg 55),(.neg 9),(.pos 39),(.pos 45)]),
   ((.exchange 55 13 0),[(.neg 55),(.neg 13),(.pos 59),(.pos 62),(.pos 66)]),
   ((.exchange 55 28 1),[(.neg 55),(.neg 28),(.pos 58),(.pos 65)]),
   ((.exchange 55 32 0),[(.neg 55),(.neg 32),(.pos 62),(.pos 66)]),
   ((.exchange 55 43 0),[(.neg 55),(.neg 43),(.pos 59),(.pos 62)]),
   ((.exchange 55 51 1),[(.neg 55),(.neg 51),(.pos 61),(.pos 65)]),
   ((.exchange 55 54 0),[(.neg 55),(.neg 54),(.pos 59),(.pos 62),(.pos 66)]),
   ((.exchange 56 9 6),[(.neg 56),(.neg 9),(.pos 35),(.pos 40),(.pos 46)]),
   ((.exchange 56 24 0),[(.neg 56),(.neg 24),(.pos 60),(.pos 63)]),
   ((.exchange 56 30 0),[(.neg 56),(.neg 30),(.pos 60),(.pos 67)]),
   ((.exchange 56 44 0),[(.neg 56),(.neg 44),(.pos 60),(.pos 63)]),
   ((.exchange 56 51 2),[(.neg 56),(.neg 51),(.pos 61),(.pos 65)]),
   ((.exchange 57 6 6),[(.neg 57),(.neg 6),(.pos 35),(.pos 38),(.pos 47)]),
   ((.exchange 57 32 2),[(.neg 57),(.neg 32),(.pos 62),(.pos 66)]),
   ((.exchange 57 44 1),[(.neg 57),(.neg 44),(.pos 60),(.pos 63)]),
   ((.exchange 57 64 1),[(.neg 64),(.neg 57),(.pos 60),(.pos 63)]),
   ((.exchange 58 6 6),[(.neg 58),(.neg 6),(.pos 36),(.pos 48)]),
   ((.exchange 58 25 3),[(.neg 58),(.neg 25),(.pos 55),(.pos 65)]),
   ((.exchange 58 30 0),[(.neg 58),(.neg 30),(.pos 60),(.pos 68)]),
   ((.exchange 58 38 0),[(.neg 58),(.neg 38),(.pos 59),(.pos 60)]),
   ((.exchange 58 46 3),[(.neg 58),(.neg 46),(.pos 56),(.pos 65)]),
   ((.exchange 58 47 0),[(.neg 58),(.neg 47),(.pos 59),(.pos 60),(.pos 68)]),
   ((.exchange 58 52 6),[(.neg 58),(.neg 52),(.pos 36),(.pos 42),(.pos 48)]),
   ((.exchange 58 66 3),[(.neg 66),(.neg 58),(.pos 55),(.pos 65)]),
   ((.exchange 58 67 0),[(.neg 67),(.neg 58),(.pos 60),(.pos 68)]),
   ((.exchange 59 19 3),[(.neg 59),(.neg 19),(.pos 55),(.pos 62)]),
   ((.exchange 59 39 3),[(.neg 59),(.neg 39),(.pos 55),(.pos 62)]),
   ((.exchange 59 40 1),[(.neg 59),(.neg 40),(.pos 58),(.pos 60),(.pos 64)]),
   ((.exchange 59 63 3),[(.neg 63),(.neg 59),(.pos 57),(.pos 62)]),
   ((.exchange 60 13 2),[(.neg 60),(.neg 13),(.pos 59),(.pos 64),(.pos 68)]),
   ((.exchange 60 27 3),[(.neg 60),(.neg 27),(.pos 57),(.pos 67)]),
   ((.exchange 60 28 2),[(.neg 60),(.neg 28),(.pos 58),(.pos 68)]),
   ((.exchange 60 31 3),[(.neg 60),(.neg 31),(.pos 56),(.pos 63),(.pos 67)]),
   ((.exchange 60 32 3),[(.neg 60),(.neg 32),(.pos 57),(.pos 63),(.pos 67)]),
   ((.exchange 60 34 2),[(.neg 60),(.neg 34),(.pos 64),(.pos 68)]),
   ((.exchange 60 40 3),[(.neg 60),(.neg 40),(.pos 56),(.pos 63)]),
   ((.exchange 60 41 3),[(.neg 60),(.neg 41),(.pos 57),(.pos 63)]),
   ((.exchange 60 45 2),[(.neg 60),(.neg 45),(.pos 58),(.pos 59),(.pos 68)]),
   ((.exchange 60 46 3),[(.neg 60),(.neg 46),(.pos 56),(.pos 67)]),
   ((.exchange 60 47 6),[(.neg 60),(.neg 47),(.pos 38),(.pos 50)]),
   ((.exchange 60 55 2),[(.neg 60),(.neg 55),(.pos 58),(.pos 59)]),
   ((.exchange 60 65 2),[(.neg 65),(.neg 60),(.pos 58),(.pos 68)]),
   ((.exchange 61 6 6),[(.neg 61),(.neg 6),(.pos 39),(.pos 42),(.pos 51)]),
   ((.exchange 61 26 4),[(.neg 61),(.neg 26),(.pos 56),(.pos 65)]),
   ((.exchange 61 32 0),[(.neg 61),(.neg 32),(.pos 62),(.pos 69)]),
   ((.exchange 61 46 4),[(.neg 61),(.neg 46),(.pos 56),(.pos 65)]),
   ((.exchange 61 50 6),[(.neg 61),(.neg 50),(.pos 40),(.pos 42),(.pos 51)]),
   ((.exchange 62 6 4),[(.neg 62),(.neg 6),(.pos 55),(.pos 59),(.pos 66)]),
   ((.exchange 62 14 6),[(.neg 62),(.neg 14),(.pos 41),(.pos 43),(.pos 52)]),
   ((.exchange 62 28 4),[(.neg 62),(.neg 28),(.pos 55),(.pos 59),(.pos 66)]),
   ((.exchange 62 46 4),[(.neg 62),(.neg 46),(.pos 55),(.pos 57),(.pos 66)]),
   ((.exchange 62 47 4),[(.neg 62),(.neg 47),(.pos 57),(.pos 66)]),
   ((.exchange 62 50 1),[(.neg 62),(.neg 50),(.pos 63),(.pos 64),(.pos 69)]),
   ((.exchange 62 54 1),[(.neg 62),(.neg 54),(.pos 64),(.pos 69)]),
   ((.exchange 62 56 1),[(.neg 62),(.neg 56),(.pos 61),(.pos 63)]),
   ((.exchange 62 60 1),[(.neg 62),(.neg 60),(.pos 63),(.pos 64)]),
   ((.exchange 62 60 4),[(.neg 62),(.neg 60),(.pos 57),(.pos 59)]),
   ((.exchange 62 68 1),[(.neg 68),(.neg 62),(.pos 64),(.pos 69)]),
   ((.exchange 63 23 2),[(.neg 63),(.neg 23),(.pos 62),(.pos 64)]),
   ((.exchange 63 36 2),[(.neg 63),(.neg 36),(.pos 61),(.pos 62),(.pos 64)]),
   ((.exchange 63 59 2),[(.neg 63),(.neg 59),(.pos 62),(.pos 64)]),
   ((.exchange 63 59 4),[(.neg 63),(.neg 59),(.pos 57),(.pos 60)]),
   ((.exchange 64 21 3),[(.neg 64),(.neg 21),(.pos 62),(.pos 63)]),
   ((.exchange 64 30 4),[(.neg 64),(.neg 30),(.pos 60),(.pos 68)]),
   ((.exchange 64 47 3),[(.neg 64),(.neg 47),(.pos 62),(.pos 63),(.pos 69)]),
   ((.exchange 64 50 6),[(.neg 64),(.neg 50),(.pos 44),(.pos 54)]),
   ((.exchange 64 52 3),[(.neg 64),(.neg 52),(.pos 62),(.pos 69)]),
   ((.exchange 64 52 6),[(.neg 64),(.neg 52),(.pos 43),(.pos 54)]),
   ((.exchange 64 67 4),[(.neg 67),(.neg 64),(.pos 60),(.pos 68)]),
   ((.exchange 65 13 0),[(.neg 65),(.neg 13),(.pos 66),(.pos 68),(.pos 69)]),
   ((.exchange 65 19 5),[(.neg 65),(.neg 19),(.pos 55),(.pos 61)]),
   ((.exchange 65 20 5),[(.neg 65),(.neg 20),(.pos 56),(.pos 61)]),
   ((.exchange 65 24 5),[(.neg 65),(.neg 24),(.pos 56),(.pos 58),(.pos 61)]),
   ((.exchange 65 27 0),[(.neg 65),(.neg 27),(.pos 66),(.pos 67)]),
   ((.exchange 65 34 0),[(.neg 65),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 65 44 6),[(.neg 65),(.neg 44),(.pos 46),(.pos 48),(.pos 51)]),
   ((.exchange 65 52 0),[(.neg 65),(.neg 52),(.pos 66),(.pos 69)]),
   ((.exchange 65 59 5),[(.neg 65),(.neg 59),(.pos 55),(.pos 58)]),
   ((.exchange 65 60 0),[(.neg 65),(.neg 60),(.pos 67),(.pos 68)]),
   ((.exchange 65 64 0),[(.neg 65),(.neg 64),(.pos 68),(.pos 69)]),
   ((.exchange 66 26 1),[(.neg 66),(.neg 26),(.pos 65),(.pos 67)]),
   ((.exchange 66 31 1),[(.neg 66),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 67 6 6),[(.neg 67),(.neg 6),(.pos 46),(.pos 47),(.pos 50)]),
   ((.exchange 67 16 5),[(.neg 67),(.neg 16),(.pos 56),(.pos 57),(.pos 60)]),
   ((.exchange 67 28 2),[(.neg 67),(.neg 28),(.pos 65),(.pos 68)]),
   ((.exchange 67 59 5),[(.neg 67),(.neg 59),(.pos 57),(.pos 60)]),
   ((.exchange 68 7 6),[(.neg 68),(.neg 7),(.pos 48),(.pos 50)]),
   ((.exchange 68 10 3),[(.neg 68),(.neg 10),(.pos 65),(.pos 67),(.pos 69)]),
   ((.exchange 68 14 6),[(.neg 68),(.neg 14),(.pos 50),(.pos 54)]),
   ((.exchange 68 17 5),[(.neg 68),(.neg 17),(.pos 58),(.pos 60)]),
   ((.exchange 68 24 5),[(.neg 68),(.neg 24),(.pos 60),(.pos 64)])]

theorem certificates_1_valid : ∀ oc ∈ certificates_1,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_2 : List (Origin 70 79 × List Sat.Literal) :=
  [((.exchange 68 44 5),[(.neg 68),(.neg 44),(.pos 60),(.pos 64)]),
   ((.exchange 68 46 3),[(.neg 68),(.neg 46),(.pos 65),(.pos 67)]),
   ((.exchange 68 51 3),[(.neg 68),(.neg 51),(.pos 65),(.pos 69)]),
   ((.exchange 68 56 5),[(.neg 68),(.neg 56),(.pos 58),(.pos 60)]),
   ((.exchange 68 63 5),[(.neg 68),(.neg 63),(.pos 60),(.pos 64)]),
   ((.exchange 69 23 5),[(.neg 69),(.neg 23),(.pos 62),(.pos 64)]),
   ((.exchange 69 28 4),[(.neg 69),(.neg 28),(.pos 65),(.pos 68)]),
   ((.exchange 69 36 5),[(.neg 69),(.neg 36),(.pos 61),(.pos 62),(.pos 64)]),
   ((.exchange 69 43 6),[(.neg 69),(.neg 43),(.pos 52),(.pos 54)]),
   ((.exchange 69 45 6),[(.neg 69),(.neg 45),(.pos 51),(.pos 52)]),
   ((.exchange 69 55 4),[(.neg 69),(.neg 55),(.pos 65),(.pos 66)]),
   ((.exchange 69 55 5),[(.neg 69),(.neg 55),(.pos 61),(.pos 62)]),
   (.newPoint,[(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 0),[(.neg 69),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 58),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 48),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 49),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 59),(.pos 62),(.pos 66),(.pos 68)]),
   ((.excluded 1),[(.neg 69),(.neg 67),(.neg 65),(.neg 63),(.neg 62),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 54),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 64),(.pos 66),(.pos 68)]),
   ((.excluded 2),[(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 49),(.pos 53),(.pos 59),(.pos 63),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 3),[(.neg 69),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 49),(.pos 59),(.pos 66),(.pos 68)]),
   ((.excluded 4),[(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 54),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 50),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 67),(.pos 69)]),
   ((.excluded 5),[(.neg 68),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 48),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 58),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 67),(.pos 69)]),
   ((.excluded 6),[(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 53),(.pos 63),(.pos 67),(.pos 69)]),
   ((.excluded 7),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 51),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 61),(.pos 64),(.pos 65)]),
   ((.excluded 8),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 9),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 48),(.pos 51),(.pos 54),(.pos 58),(.pos 61),(.pos 64)]),
   ((.excluded 10),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 50),(.pos 52),(.pos 60),(.pos 62),(.pos 65)]),
   ((.excluded 11),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 50),(.pos 52),(.pos 60),(.pos 62)]),
   ((.excluded 12),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 50),(.pos 60),(.pos 65)]),
   ((.excluded 13),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 50),(.pos 60)]),
   ((.excluded 14),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 52),(.pos 62),(.pos 65)]),
   ((.excluded 15),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 52),(.pos 62)]),
   ((.excluded 16),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 65)]),
   ((.excluded 17),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44)]),
   ((.excluded 18),[(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 59),(.pos 63),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 19),[(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 49),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 20),[(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 49),(.pos 53),(.pos 59),(.pos 63),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 21),[(.neg 69),(.neg 67),(.neg 65),(.neg 63),(.neg 62),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 48),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 45),(.pos 46),(.pos 47),(.pos 49),(.pos 52),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 64),(.pos 66),(.pos 68)]),
   ((.excluded 22),[(.neg 69),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 48),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 45),(.pos 46),(.pos 47),(.pos 49),(.pos 52),(.pos 59),(.pos 66),(.pos 68)]),
   ((.excluded 23),[(.neg 69),(.neg 67),(.neg 65),(.neg 63),(.neg 62),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 49),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 64),(.pos 66),(.pos 68)]),
   ((.excluded 24),[(.neg 69),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 58),(.neg 53),(.neg 52),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 59),(.pos 62),(.pos 66),(.pos 68)]),
   ((.excluded 25),[(.neg 69),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 54),(.pos 59),(.pos 66),(.pos 68)]),
   ((.excluded 26),[(.neg 69),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 49),(.pos 55),(.pos 56),(.pos 57),(.pos 59),(.pos 62),(.pos 66),(.pos 68)]),
   ((.excluded 27),[(.neg 69),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 49),(.pos 59),(.pos 66),(.pos 68)]),
   ((.excluded 28),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 51),(.pos 54),(.pos 60),(.pos 62),(.pos 65)]),
   ((.excluded 29),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 51),(.pos 54),(.pos 60),(.pos 65)]),
   ((.excluded 30),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 51),(.pos 54),(.pos 62),(.pos 65)]),
   ((.excluded 31),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 51),(.pos 54),(.pos 65)]),
   ((.excluded 32),[(.neg 68),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 45),(.pos 46),(.pos 47),(.pos 50),(.pos 53),(.pos 58),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 67),(.pos 69)]),
   ((.excluded 33),[(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 45),(.pos 46),(.pos 47),(.pos 50),(.pos 53),(.pos 63),(.pos 67),(.pos 69)]),
   ((.excluded 34),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 45),(.pos 46),(.pos 47),(.pos 58),(.pos 61),(.pos 64)]),
   ((.excluded 35),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 45),(.pos 46),(.pos 47),(.pos 60),(.pos 62)]),
   ((.excluded 36),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 45),(.pos 46),(.pos 47),(.pos 60)]),
   ((.excluded 37),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 45),(.pos 46),(.pos 47),(.pos 62)]),
   ((.excluded 38),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 45),(.pos 46),(.pos 47)]),
   ((.excluded 39),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 54),(.neg 53),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 50),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 61),(.pos 64),(.pos 65)]),
   ((.excluded 40),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 50),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 61),(.pos 64),(.pos 65)]),
   ((.excluded 41),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 61),(.pos 64),(.pos 65)]),
   ((.excluded 42),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 61),(.pos 64),(.pos 65)]),
   ((.excluded 43),[(.neg 68),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 53),(.pos 58),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 67),(.pos 69)]),
   ((.excluded 44),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 50),(.pos 52),(.pos 58),(.pos 61),(.pos 64)]),
   ((.excluded 45),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 50),(.pos 58),(.pos 61),(.pos 64)]),
   ((.excluded 46),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 52),(.pos 58),(.pos 61),(.pos 64)]),
   ((.excluded 47),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 58),(.pos 61),(.pos 64)]),
   ((.excluded 48),[(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 48),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 67),(.pos 69)]),
   ((.excluded 49),[(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 48),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 63),(.pos 67),(.pos 69)]),
   ((.excluded 50),[(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 67),(.pos 69)]),
   ((.excluded 51),[(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 53),(.pos 63),(.pos 67),(.pos 69)]),
   ((.excluded 52),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 48),(.pos 51),(.pos 54),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 53),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 48),(.pos 51),(.pos 54),(.pos 60),(.pos 62)]),
   ((.excluded 54),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 48),(.pos 51),(.pos 54),(.pos 60)]),
   ((.excluded 55),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 48),(.pos 51),(.pos 54),(.pos 62)]),
   ((.excluded 56),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 48),(.pos 51),(.pos 54)]),
   ((.excluded 57),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 50),(.pos 52),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 58),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 50),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 59),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 52),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 60),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 61),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 50),(.pos 52),(.pos 65)]),
   ((.excluded 62),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 50),(.pos 52)]),
   ((.excluded 63),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 50),(.pos 62),(.pos 65)]),
   ((.excluded 64),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 50),(.pos 62)]),
   ((.excluded 65),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 50),(.pos 65)]),
   ((.excluded 66),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 50)]),
   ((.excluded 67),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 52),(.pos 60),(.pos 65)]),
   ((.excluded 68),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 52),(.pos 60)]),
   ((.excluded 69),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 52),(.pos 65)]),
   ((.excluded 70),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 52)]),
   ((.excluded 71),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 60),(.pos 62),(.pos 65)]),
   ((.excluded 72),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 60),(.pos 62)]),
   ((.excluded 73),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 60),(.pos 65)]),
   ((.excluded 74),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 60)]),
   ((.excluded 75),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 62),(.pos 65)]),
   ((.excluded 76),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 62)]),
   ((.excluded 77),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 65)]),
   ((.excluded 78),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42)])]

theorem certificates_2_valid : ∀ oc ∈ certificates_2,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



theorem witness_0 : ∀ j : Fin 79,
    let w : Fin 79 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 79,
      let w : Fin 79 := ⟨0 + j.val,by omega⟩
      target w < MatroidCatalogue.count 8 4 ∧
        Papers.RationalityTen.MatroidChecked.FastSemanticChecks.RawWitness 8 (N7R4.familyMasks.get 48)
        (fun i : Fin 70 => N8R4.gridMasks.get i.val) newIndex (models w)
        (N8R4.familyMasks.get (target w)) (permutation w) := by
    refine (Fin.forall_fin_add (m := 39) (n := 40) _).2 ⟨?_, ?_⟩
    · refine (Fin.forall_fin_add (m := 19) (n := 20) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 9) (n := 10) _).2 ⟨?_, ?_⟩
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
      · refine (Fin.forall_fin_add (m := 10) (n := 10) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 5) (n := 5) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
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
    · refine (Fin.forall_fin_add (m := 20) (n := 20) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 10) (n := 10) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 5) (n := 5) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
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
      · refine (Fin.forall_fin_add (m := 10) (n := 10) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 5) (n := 5) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 2) (n := 3) _).2 ⟨?_, ?_⟩
            · decide +kernel
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


end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C48

/- Source: MatroidCatalogue/Cases/N8R4C48Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C48

noncomputable def certificates : List (Origin 70 79 × List Sat.Literal) :=
  certificates_0 ++ certificates_1 ++ certificates_2

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  intro oc hoc
  simp only [certificates,List.mem_append,or_assoc] at hoc
  rcases hoc with h0 | h1 | h2
  · exact certificates_0_valid oc h0
  · exact certificates_1_valid oc h1
  · exact certificates_2_valid oc h2

theorem models_valid : ∀ w : Fin 79,
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 79) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 8) 4)
    (hold : M.bases.filter ((7 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 8 4, IsomorphicWithin 8 M.bases B := by
  apply extension_covered_of_certificate (n:=7) (r:=4) (by decide)
    catalogue old U newIndex models certificates
    N8R4.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C48.formula []
    exact Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C48.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 8 4 (target w),family_mem 8 4 (target w) hw.1,?_⟩
    exact validWitness_sound 8 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C48


end
end
end BundlePart4

section BundlePart5
/- Source: MatroidChecked/SemanticChunks/Cases06Part06.lean -/




@[expose] public section
noncomputable section

/- Source: MatroidCatalogue/Cases/N8R4C49Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C49

abbrev U := N8R4.grid
noncomputable def old : Finset (Finset (Fin 8)) := N7R4.family 49
noncomputable def newIndexTree : Table ℕ := (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf 35) (.leaf 36)) (.node 3 (.leaf 37) (.leaf 38))) (.node 6 (.node 5 (.leaf 39) (.leaf 40)) (.node 7 (.leaf 41) (.leaf 42)))) (.node 12 (.node 10 (.node 9 (.leaf 43) (.leaf 44)) (.node 11 (.leaf 45) (.leaf 46))) (.node 14 (.node 13 (.leaf 47) (.leaf 48)) (.node 15 (.leaf 49) (.node 16 (.leaf 50) (.leaf 51)))))) (.node 26 (.node 21 (.node 19 (.node 18 (.leaf 52) (.leaf 53)) (.node 20 (.leaf 54) (.leaf 55))) (.node 23 (.node 22 (.leaf 56) (.leaf 57)) (.node 24 (.leaf 58) (.node 25 (.leaf 59) (.leaf 60))))) (.node 30 (.node 28 (.node 27 (.leaf 61) (.leaf 62)) (.node 29 (.leaf 63) (.leaf 64))) (.node 32 (.node 31 (.leaf 65) (.leaf 66)) (.node 33 (.leaf 67) (.node 34 (.leaf 68) (.leaf 69)))))))
noncomputable def newIndex (i : Fin 35) : Fin 70 := Fin.ofNat 70 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 67 (.node 33 (.node 16 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (27752499200,129,4151042)) (.leaf (27541529600,129,4143650))) (.node 3 (.leaf (1069542400,190,2054283)) (.leaf (27375692800,183,6248515)))) (.node 6 (.node 5 (.leaf (27913088000,192,6248515)) (.leaf (32921784320,121,4151504))) (.node 7 (.leaf (25172580352,130,4149530)) (.leaf (17153628160,152,6248200))))) (.node 12 (.node 10 (.node 9 (.leaf (34333497344,153,8344840)) (.leaf (16170152960,130,4131554))) (.node 11 (.leaf (32748600320,193,12526360)) (.leaf (33822342144,194,12526360)))) (.node 14 (.node 13 (.leaf (25431831552,152,6240864)) (.leaf (34021766144,153,8333920))) (.node 15 (.leaf (33118059520,185,8342152)) (.leaf (34191801344,186,12531778)))))) (.node 24 (.node 20 (.node 18 (.node 17 (.leaf (33252408320,196,10441816)) (.leaf (17146280960,193,10433577))) (.node 19 (.leaf (34326150144,197,12534809)) (.leaf (33151646720,196,10431176)))) (.node 22 (.node 21 (.leaf (25635453952,193,10430273)) (.leaf (34225388544,197,12527809))) (.node 23 (.leaf (33285995520,209,12535432)) (.leaf (25769802752,205,12534984))))) (.node 28 (.node 26 (.node 25 (.leaf (17179868160,205,12527704)) (.leaf (34359737344,210,12535432))) (.node 27 (.leaf (1068499933,267,3955994)) (.leaf (1044445,267,2350362)))) (.node 30 (.node 29 (.leaf (1069543389,349,11660936)) (.leaf (27541736413,319,7761544))) (.node 31 (.leaf (27376061405,320,6219969)) (.node 32 (.leaf (27912932317,321,10349185)) (.leaf (27541368797,320,5753881)))))))) (.node 50 (.node 41 (.node 37 (.node 35 (.node 34 (.leaf (27541893085,321,9427985)) (.leaf (27752294365,319,7532168))) (.node 36 (.leaf (27375855581,320,6212633)) (.leaf (27912726493,321,10345489)))) (.node 39 (.node 38 (.leaf (27752132573,320,5761217)) (.leaf (27752656861,321,9431681))) (.node 40 (.leaf (27912564701,340,14599746)) (.leaf (27376218077,340,14140994))))) (.node 45 (.node 43 (.node 42 (.leaf (27913088989,350,16434754)) (.leaf (32748770269,312,10398920))) (.node 44 (.leaf (33117869021,314,8309896)) (.leaf (33252086749,315,12478032)))) (.node 47 (.node 46 (.leaf (33151423453,315,12467336)) (.leaf (33285641181,316,12438664))) (.node 48 (.leaf (25431579613,320,8344224)) (.node 49 (.leaf (25635003357,322,10412752)) (.leaf (25769221085,323,12477136))))))) (.node 58 (.node 54 (.node 52 (.node 51 (.leaf (16171113437,320,8100624)) (.leaf (34022071261,326,12306056))) (.node 53 (.leaf (33822841821,331,12534984)) (.leaf (34191940573,333,12534984)))) (.node 56 (.node 55 (.leaf (34225495005,336,12534984)) (.leaf (17146289117,328,12534984))) (.node 57 (.leaf (34326158301,335,12534984)) (.leaf (17179843549,329,14599368))))) (.node 62 (.node 60 (.node 59 (.leaf (34359712733,337,14599368)) (.leaf (32921616349,312,9940168))) (.node 61 (.leaf (32921976797,314,7851144)) (.leaf (32922107869,315,11789904)))) (.node 64 (.node 63 (.leaf (32922009565,315,11779208)) (.leaf (32922140637,316,11521160))) (.node 65 (.leaf (16171106269,322,9936024)) (.node 66 (.leaf (16171139037,323,11771032)) (.leaf (34021572573,331,12298328))))))))) (.node 100 (.node 83 (.node 75 (.node 71 (.node 69 (.node 68 (.leaf (34021933021,333,12298328)) (.leaf (34022064093,336,12298328))) (.node 70 (.leaf (25432031197,328,12298328)) (.leaf (34021965789,335,12298328)))) (.node 73 (.node 72 (.leaf (25432162269,329,14133336)) (.leaf (34022096861,337,14133336))) (.node 74 (.leaf (25172834269,320,8114848)) (.leaf (25173032925,322,9954000))))) (.node 79 (.node 77 (.node 76 (.leaf (25173163997,323,11789008)) (.leaf (25635256285,328,12527704))) (.node 78 (.leaf (25769474013,329,14592088)) (.leaf (25769672669,351,14596232)))) (.node 81 (.node 80 (.leaf (25635586013,351,14137480)) (.leaf (25769803741,352,16434824))) (.node 82 (.leaf (17152669661,320,8330000)) (.leaf (17145329629,322,10394776)))))) (.node 91 (.node 87 (.node 85 (.node 84 (.leaf (17178884061,323,12459160)) (.leaf (34333194205,326,12535432))) (.node 86 (.leaf (33822537693,331,12527704)) (.leaf (34191636445,333,12527704)))) (.node 89 (.node 88 (.leaf (34325854173,336,12527704)) (.leaf (34225190877,335,12527704))) (.node 90 (.leaf (34359408605,337,14592088)) (.leaf (34332999645,331,12305608))))) (.node 95 (.node 93 (.node 92 (.leaf (34333360093,333,12305608)) (.leaf (34333392861,336,12305608))) (.node 94 (.leaf (17153621981,328,12305608)) (.leaf (34333491165,335,12305608)))) (.node 97 (.node 96 (.leaf (17153654749,329,14140616)) (.leaf (34333523933,337,14140616))) (.node 98 (.leaf (17179836381,351,14599760)) (.node 99 (.leaf (17146314717,351,14141008)) (.leaf (17179869149,352,16431184)))))))) (.node 117 (.node 108 (.node 104 (.node 102 (.node 101 (.leaf (33117700061,343,14136584)) (.leaf (34191441885,344,14136584))) (.node 103 (.leaf (33251917789,353,14136416)) (.leaf (34325659613,354,14136416)))) (.node 106 (.node 105 (.leaf (33151254493,353,14133000)) (.leaf (34224996317,354,14133000))) (.node 107 (.leaf (33285472221,355,14599368)) (.leaf (34359214045,356,14599368))))) (.node 112 (.node 110 (.node 109 (.leaf (33252311005,353,16434824)) (.leaf (34326052829,354,16434824))) (.node 111 (.leaf (33118224349,345,14141064)) (.leaf (34191966173,346,14141064)))) (.node 114 (.node 113 (.leaf (33252442077,357,14141008)) (.leaf (34326183901,358,14141008))) (.node 115 (.leaf (33151746013,353,16205448)) (.node 116 (.leaf (34225487837,354,16205448)) (.leaf (33151778781,357,14137480))))))) (.node 125 (.node 121 (.node 119 (.node 118 (.leaf (34225520605,358,14137480)) (.leaf (32748961757,343,14595336))) (.node 120 (.leaf (33822703581,344,14595336)) (.leaf (33285832669,345,14599816)))) (.node 123 (.node 122 (.leaf (34359574493,346,14599816)) (.leaf (32749092829,353,14595168))) (.node 124 (.leaf (33822834653,354,14595168)) (.leaf (33285963741,357,14599760))))) (.node 129 (.node 127 (.node 126 (.leaf (34359705565,358,14599760)) (.leaf (32748994525,353,14591752))) (.node 128 (.leaf (33822736349,354,14591752)) (.leaf (33285865437,357,14596232)))) (.node 131 (.node 130 (.leaf (34359607261,358,14596232)) (.leaf (32749125597,355,14140616))) (.node 132 (.leaf (33822867421,356,14140616)) (.node 133 (.leaf (33285996509,359,16434824)) (.leaf (34359738333,360,16434824))))))))))

noncomputable def models (i : Fin 134) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 134) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 134) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 70, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (7 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 70, (7 : Fin 8) ∈ U i → ∃ j : Fin 35, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C49

/- Source: MatroidCatalogue/Cases/N8R4C49Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C49


noncomputable def certificates_0 : List (Origin 70 134 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.neg 2)]),
   ((.fixed 3),[(.neg 3)]),
   ((.fixed 4),[(.neg 4)]),
   ((.fixed 5),[(.pos 5)]),
   ((.fixed 6),[(.neg 6)]),
   ((.fixed 7),[(.pos 7)]),
   ((.fixed 8),[(.pos 8)]),
   ((.fixed 9),[(.pos 9)]),
   ((.fixed 10),[(.neg 10)]),
   ((.fixed 11),[(.pos 11)]),
   ((.fixed 12),[(.pos 12)]),
   ((.fixed 13),[(.pos 13)]),
   ((.fixed 14),[(.pos 14)]),
   ((.fixed 15),[(.pos 15)]),
   ((.fixed 16),[(.neg 16)]),
   ((.fixed 17),[(.pos 17)]),
   ((.fixed 18),[(.pos 18)]),
   ((.fixed 19),[(.pos 19)]),
   ((.fixed 20),[(.neg 20)]),
   ((.fixed 21),[(.pos 21)]),
   ((.fixed 22),[(.pos 22)]),
   ((.fixed 23),[(.pos 23)]),
   ((.fixed 24),[(.pos 24)]),
   ((.fixed 25),[(.pos 25)]),
   ((.fixed 26),[(.pos 26)]),
   ((.fixed 27),[(.neg 27)]),
   ((.fixed 28),[(.pos 28)]),
   ((.fixed 29),[(.pos 29)]),
   ((.fixed 30),[(.pos 30)]),
   ((.fixed 31),[(.pos 31)]),
   ((.fixed 32),[(.pos 32)]),
   ((.fixed 33),[(.pos 33)]),
   ((.fixed 34),[(.pos 34)]),
   ((.exchange 5 41 5),[(.neg 41),(.neg 5),(.pos 1),(.pos 35)]),
   ((.exchange 5 48 2),[(.neg 48),(.neg 5),(.pos 6),(.pos 45)]),
   ((.exchange 5 49 2),[(.neg 49),(.neg 5),(.pos 6),(.pos 45)]),
   ((.exchange 5 51 1),[(.neg 51),(.neg 5),(.pos 10),(.pos 46)]),
   ((.exchange 5 53 1),[(.neg 53),(.neg 5),(.pos 10),(.pos 46)]),
   ((.exchange 5 57 0),[(.neg 57),(.neg 5),(.pos 27),(.pos 47)]),
   ((.exchange 5 66 0),[(.neg 66),(.neg 5),(.pos 27),(.pos 47)]),
   ((.exchange 5 67 0),[(.neg 67),(.neg 5),(.pos 27),(.pos 47)]),
   ((.exchange 7 41 5),[(.neg 41),(.neg 7),(.pos 0),(.pos 3),(.pos 37)]),
   ((.exchange 7 45 2),[(.neg 45),(.neg 7),(.pos 6),(.pos 48)]),
   ((.exchange 7 49 2),[(.neg 49),(.neg 7),(.pos 6),(.pos 48)]),
   ((.exchange 8 41 5),[(.neg 41),(.neg 8),(.pos 4),(.pos 38)]),
   ((.exchange 8 45 2),[(.neg 45),(.neg 8),(.pos 6),(.pos 49)]),
   ((.exchange 8 48 2),[(.neg 48),(.neg 8),(.pos 6),(.pos 49)]),
   ((.exchange 9 41 5),[(.neg 41),(.neg 9),(.pos 1),(.pos 39)]),
   ((.exchange 9 46 1),[(.neg 46),(.neg 9),(.pos 10),(.pos 51)]),
   ((.exchange 11 35 5),[(.neg 35),(.neg 11),(.pos 1),(.pos 41)]),
   ((.exchange 11 37 5),[(.neg 37),(.neg 11),(.pos 1),(.pos 4),(.pos 41)]),
   ((.exchange 11 38 5),[(.neg 38),(.neg 11),(.pos 4),(.pos 41)]),
   ((.exchange 11 39 5),[(.neg 39),(.neg 11),(.pos 1),(.pos 41)]),
   ((.exchange 11 42 5),[(.neg 42),(.neg 11),(.pos 1),(.pos 4),(.pos 41)]),
   ((.exchange 11 43 5),[(.neg 43),(.neg 11),(.pos 4),(.pos 41)]),
   ((.exchange 11 44 5),[(.neg 44),(.neg 11),(.pos 4),(.pos 41)]),
   ((.exchange 11 46 1),[(.neg 46),(.neg 11),(.pos 10),(.pos 53)]),
   ((.exchange 12 41 5),[(.neg 41),(.neg 12),(.pos 2),(.pos 3),(.pos 42)]),
   ((.exchange 13 41 5),[(.neg 41),(.neg 13),(.pos 4),(.pos 43)]),
   ((.exchange 14 41 5),[(.neg 41),(.neg 14),(.pos 4),(.pos 44)]),
   ((.exchange 15 47 0),[(.neg 47),(.neg 15),(.pos 27),(.pos 57)]),
   ((.exchange 15 58 2),[(.neg 58),(.neg 15),(.pos 16),(.pos 55)]),
   ((.exchange 15 59 2),[(.neg 59),(.neg 15),(.pos 16),(.pos 55)]),
   ((.exchange 15 61 1),[(.neg 61),(.neg 15),(.pos 20),(.pos 56)]),
   ((.exchange 15 63 1),[(.neg 63),(.neg 15),(.pos 20),(.pos 56)]),
   ((.exchange 15 66 0),[(.neg 66),(.neg 15),(.pos 27),(.pos 57)]),
   ((.exchange 15 67 0),[(.neg 67),(.neg 15),(.pos 27),(.pos 57)]),
   ((.exchange 17 55 2),[(.neg 55),(.neg 17),(.pos 16),(.pos 58)]),
   ((.exchange 18 55 2),[(.neg 55),(.neg 18),(.pos 16),(.pos 59)]),
   ((.exchange 19 56 1),[(.neg 56),(.neg 19),(.pos 20),(.pos 61)]),
   ((.exchange 19 63 1),[(.neg 63),(.neg 19),(.pos 20),(.pos 61)]),
   ((.exchange 21 56 1),[(.neg 56),(.neg 21),(.pos 20),(.pos 63)]),
   ((.exchange 21 61 1),[(.neg 61),(.neg 21),(.pos 20),(.pos 63)]),
   ((.exchange 25 47 0),[(.neg 47),(.neg 25),(.pos 27),(.pos 66)]),
   ((.exchange 25 57 0),[(.neg 57),(.neg 25),(.pos 27),(.pos 66)]),
   ((.exchange 25 67 0),[(.neg 67),(.neg 25),(.pos 27),(.pos 66)]),
   ((.exchange 26 47 0),[(.neg 47),(.neg 26),(.pos 27),(.pos 67)]),
   ((.exchange 26 57 0),[(.neg 57),(.neg 26),(.pos 27),(.pos 67)]),
   ((.exchange 26 66 0),[(.neg 66),(.neg 26),(.pos 27),(.pos 67)]),
   ((.exchange 35 26 1),[(.neg 35),(.neg 26),(.pos 46),(.pos 56)]),
   ((.exchange 35 65 1),[(.neg 65),(.neg 35),(.pos 46),(.pos 56)]),
   ((.exchange 36 5 7),[(.neg 36),(.neg 5),(.pos 0),(.pos 6)]),
   ((.exchange 37 30 0),[(.neg 37),(.neg 30),(.pos 50),(.pos 60)]),
   ((.exchange 37 33 3),[(.neg 37),(.neg 33),(.pos 40),(.pos 46),(.pos 56)]),
   ((.exchange 39 29 4),[(.neg 39),(.neg 29),(.pos 36),(.pos 45),(.pos 55)]),
   ((.exchange 39 31 1),[(.neg 39),(.neg 31),(.pos 51),(.pos 61)]),
   ((.exchange 39 65 1),[(.neg 65),(.neg 39),(.pos 51),(.pos 61)]),
   ((.exchange 40 5 7),[(.neg 40),(.neg 5),(.pos 1),(.pos 10)]),
   ((.exchange 41 26 1),[(.neg 41),(.neg 26),(.pos 40),(.pos 53),(.pos 63)]),
   ((.exchange 42 29 4),[(.neg 42),(.neg 29),(.pos 36),(.pos 48),(.pos 58)]),
   ((.exchange 42 33 3),[(.neg 42),(.neg 33),(.pos 40),(.pos 51),(.pos 61)]),
   ((.exchange 42 34 0),[(.neg 42),(.neg 34),(.pos 54),(.pos 64)]),
   ((.exchange 43 29 4),[(.neg 43),(.neg 29),(.pos 49),(.pos 59)]),
   ((.exchange 43 32 3),[(.neg 43),(.neg 32),(.pos 52),(.pos 62)]),
   ((.exchange 43 69 3),[(.neg 69),(.neg 43),(.pos 52),(.pos 62)]),
   ((.exchange 44 33 3),[(.neg 44),(.neg 33),(.pos 53),(.pos 63)]),
   ((.exchange 44 69 2),[(.neg 69),(.neg 44),(.pos 54),(.pos 64)]),
   ((.exchange 45 11 0),[(.neg 45),(.neg 11),(.pos 47),(.pos 52)]),
   ((.exchange 45 23 5),[(.neg 45),(.neg 23),(.pos 36),(.pos 39),(.pos 55)]),
   ((.exchange 45 31 1),[(.neg 45),(.neg 31),(.pos 51),(.pos 65)]),
   ((.exchange 45 63 0),[(.neg 63),(.neg 45),(.pos 47),(.pos 52),(.pos 66)]),
   ((.exchange 45 63 5),[(.neg 63),(.neg 45),(.pos 35),(.pos 39),(.pos 55)]),
   ((.exchange 46 8 0),[(.neg 46),(.neg 8),(.pos 47),(.pos 50)]),
   ((.exchange 46 11 0),[(.neg 46),(.neg 11),(.pos 47),(.pos 53)]),
   ((.exchange 46 15 5),[(.neg 46),(.neg 15),(.pos 35),(.pos 56)]),
   ((.exchange 46 28 2),[(.neg 46),(.neg 28),(.pos 48),(.pos 65)]),
   ((.exchange 46 30 0),[(.neg 46),(.neg 30),(.pos 50),(.pos 67)]),
   ((.exchange 46 59 0),[(.neg 59),(.neg 46),(.pos 47),(.pos 50),(.pos 67)]),
   ((.exchange 47 9 2),[(.neg 47),(.neg 9),(.pos 45),(.pos 52)]),
   ((.exchange 47 14 1),[(.neg 47),(.neg 14),(.pos 50),(.pos 53)]),
   ((.exchange 47 37 1),[(.neg 47),(.neg 37),(.pos 46),(.pos 50)]),
   ((.exchange 48 23 5),[(.neg 48),(.neg 23),(.pos 36),(.pos 42),(.pos 58)]),
   ((.exchange 48 30 0),[(.neg 48),(.neg 30),(.pos 50),(.pos 68)]),
   ((.exchange 48 31 3),[(.neg 48),(.neg 31),(.pos 51),(.pos 65)]),
   ((.exchange 48 34 0),[(.neg 48),(.neg 34),(.pos 54),(.pos 68)]),
   ((.exchange 48 53 0),[(.neg 53),(.neg 48),(.pos 50),(.pos 54)]),
   ((.exchange 48 63 5),[(.neg 63),(.neg 48),(.pos 37),(.pos 42),(.pos 58)]),
   ((.exchange 48 67 0),[(.neg 67),(.neg 48),(.pos 50),(.pos 68)]),
   ((.exchange 49 11 3),[(.neg 49),(.neg 11),(.pos 47),(.pos 52)]),
   ((.exchange 49 22 5),[(.neg 49),(.neg 22),(.pos 36),(.pos 43),(.pos 59)]),
   ((.exchange 49 30 1),[(.neg 49),(.neg 30),(.pos 50),(.pos 68)]),
   ((.exchange 49 53 1),[(.neg 53),(.neg 49),(.pos 50),(.pos 54)]),
   ((.exchange 49 53 3),[(.neg 53),(.neg 49),(.pos 47),(.pos 52)]),
   ((.exchange 50 5 3),[(.neg 50),(.neg 5),(.pos 46),(.pos 47)]),
   ((.exchange 50 9 2),[(.neg 50),(.neg 9),(.pos 48),(.pos 49),(.pos 54)]),
   ((.exchange 50 22 5),[(.neg 50),(.neg 22),(.pos 37),(.pos 44),(.pos 60)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_1 : List (Origin 70 134 × List Sat.Literal) :=
  [((.exchange 50 25 2),[(.neg 50),(.neg 25),(.pos 48),(.pos 49),(.pos 68)]),
   ((.exchange 50 26 3),[(.neg 50),(.neg 26),(.pos 46),(.pos 67)]),
   ((.exchange 50 28 2),[(.neg 50),(.neg 28),(.pos 48),(.pos 68)]),
   ((.exchange 50 34 2),[(.neg 50),(.neg 34),(.pos 54),(.pos 68)]),
   ((.exchange 50 35 3),[(.neg 50),(.neg 35),(.pos 46),(.pos 47)]),
   ((.exchange 50 52 2),[(.neg 52),(.neg 50),(.pos 49),(.pos 54)]),
   ((.exchange 50 58 2),[(.neg 58),(.neg 50),(.pos 48),(.pos 68)]),
   ((.exchange 50 62 5),[(.neg 62),(.neg 50),(.pos 38),(.pos 44),(.pos 60)]),
   ((.exchange 50 66 2),[(.neg 66),(.neg 50),(.pos 49),(.pos 68)]),
   ((.exchange 51 13 0),[(.neg 51),(.neg 13),(.pos 52),(.pos 54)]),
   ((.exchange 51 15 5),[(.neg 51),(.neg 15),(.pos 39),(.pos 40),(.pos 61)]),
   ((.exchange 51 25 4),[(.neg 51),(.neg 25),(.pos 45),(.pos 65)]),
   ((.exchange 51 34 0),[(.neg 51),(.neg 34),(.pos 54),(.pos 69)]),
   ((.exchange 51 58 4),[(.neg 58),(.neg 51),(.pos 48),(.pos 65)]),
   ((.exchange 52 8 4),[(.neg 52),(.neg 8),(.pos 47),(.pos 49)]),
   ((.exchange 52 14 1),[(.neg 52),(.neg 14),(.pos 53),(.pos 54)]),
   ((.exchange 52 15 5),[(.neg 52),(.neg 15),(.pos 39),(.pos 41),(.pos 62)]),
   ((.exchange 52 24 5),[(.neg 52),(.neg 24),(.pos 41),(.pos 43),(.pos 62)]),
   ((.exchange 52 25 4),[(.neg 52),(.neg 25),(.pos 45),(.pos 66)]),
   ((.exchange 52 26 1),[(.neg 52),(.neg 26),(.pos 51),(.pos 53),(.pos 69)]),
   ((.exchange 52 35 4),[(.neg 52),(.neg 35),(.pos 45),(.pos 47)]),
   ((.exchange 52 46 4),[(.neg 52),(.neg 46),(.pos 45),(.pos 47)]),
   ((.exchange 52 67 1),[(.neg 67),(.neg 52),(.pos 53),(.pos 69)]),
   ((.exchange 53 8 4),[(.neg 53),(.neg 8),(.pos 47),(.pos 50)]),
   ((.exchange 53 15 5),[(.neg 53),(.neg 15),(.pos 40),(.pos 41),(.pos 63)]),
   ((.exchange 53 32 2),[(.neg 53),(.neg 32),(.pos 52),(.pos 69)]),
   ((.exchange 53 34 2),[(.neg 53),(.neg 34),(.pos 54),(.pos 69)]),
   ((.exchange 53 38 4),[(.neg 53),(.neg 38),(.pos 47),(.pos 50)]),
   ((.exchange 53 49 4),[(.neg 53),(.neg 49),(.pos 47),(.pos 50)]),
   ((.exchange 53 68 2),[(.neg 68),(.neg 53),(.pos 54),(.pos 69)]),
   ((.exchange 54 5 3),[(.neg 54),(.neg 5),(.pos 51),(.pos 52),(.pos 53)]),
   ((.exchange 54 15 5),[(.neg 54),(.neg 15),(.pos 42),(.pos 43),(.pos 44),(.pos 64)]),
   ((.exchange 54 22 5),[(.neg 54),(.neg 22),(.pos 42),(.pos 64)]),
   ((.exchange 54 25 4),[(.neg 54),(.neg 25),(.pos 48),(.pos 49),(.pos 68)]),
   ((.exchange 54 29 4),[(.neg 54),(.neg 29),(.pos 49),(.pos 68)]),
   ((.exchange 54 30 4),[(.neg 54),(.neg 30),(.pos 50),(.pos 68)]),
   ((.exchange 54 31 3),[(.neg 54),(.neg 31),(.pos 51),(.pos 69)]),
   ((.exchange 54 35 3),[(.neg 54),(.neg 35),(.pos 51),(.pos 52),(.pos 53)]),
   ((.exchange 54 35 4),[(.neg 54),(.neg 35),(.pos 48),(.pos 49),(.pos 50)]),
   ((.exchange 54 45 3),[(.neg 54),(.neg 45),(.pos 51),(.pos 52)]),
   ((.exchange 54 46 4),[(.neg 54),(.neg 46),(.pos 48),(.pos 50)]),
   ((.exchange 54 47 4),[(.neg 54),(.neg 47),(.pos 49),(.pos 50)]),
   ((.exchange 54 56 4),[(.neg 56),(.neg 54),(.pos 48),(.pos 50),(.pos 68)]),
   ((.exchange 54 61 3),[(.neg 61),(.neg 54),(.pos 51),(.pos 69)]),
   ((.exchange 54 67 3),[(.neg 67),(.neg 54),(.pos 53),(.pos 69)]),
   ((.exchange 55 5 6),[(.neg 55),(.neg 5),(.pos 35),(.pos 45)]),
   ((.exchange 55 11 0),[(.neg 55),(.neg 11),(.pos 57),(.pos 62),(.pos 66)]),
   ((.exchange 55 26 1),[(.neg 55),(.neg 26),(.pos 56),(.pos 65)]),
   ((.exchange 55 32 0),[(.neg 55),(.neg 32),(.pos 62),(.pos 66)]),
   ((.exchange 55 53 6),[(.neg 55),(.neg 53),(.pos 35),(.pos 39),(.pos 45)]),
   ((.exchange 56 7 6),[(.neg 56),(.neg 7),(.pos 37),(.pos 46)]),
   ((.exchange 56 8 0),[(.neg 56),(.neg 8),(.pos 57),(.pos 60),(.pos 67)]),
   ((.exchange 56 25 2),[(.neg 56),(.neg 25),(.pos 55),(.pos 65)]),
   ((.exchange 56 30 0),[(.neg 56),(.neg 30),(.pos 60),(.pos 67)]),
   ((.exchange 56 49 2),[(.neg 56),(.neg 49),(.pos 55),(.pos 58),(.pos 65)]),
   ((.exchange 56 59 0),[(.neg 59),(.neg 56),(.pos 57),(.pos 60)]),
   ((.exchange 57 19 2),[(.neg 57),(.neg 19),(.pos 55),(.pos 62)]),
   ((.exchange 57 61 2),[(.neg 61),(.neg 57),(.pos 55),(.pos 62)]),
   ((.exchange 58 5 6),[(.neg 58),(.neg 5),(.pos 36),(.pos 37),(.pos 48)]),
   ((.exchange 58 24 0),[(.neg 58),(.neg 24),(.pos 60),(.pos 64)]),
   ((.exchange 58 30 0),[(.neg 58),(.neg 30),(.pos 60),(.pos 68)]),
   ((.exchange 58 46 3),[(.neg 58),(.neg 46),(.pos 56),(.pos 65)]),
   ((.exchange 58 53 6),[(.neg 58),(.neg 53),(.pos 37),(.pos 42),(.pos 48)]),
   ((.exchange 58 67 0),[(.neg 67),(.neg 58),(.pos 60),(.pos 68)]),
   ((.exchange 59 5 6),[(.neg 59),(.neg 5),(.pos 36),(.pos 38),(.pos 49)]),
   ((.exchange 59 11 3),[(.neg 59),(.neg 11),(.pos 57),(.pos 62),(.pos 66)]),
   ((.exchange 59 21 3),[(.neg 59),(.neg 21),(.pos 57),(.pos 62)]),
   ((.exchange 59 24 1),[(.neg 59),(.neg 24),(.pos 60),(.pos 64)]),
   ((.exchange 59 34 1),[(.neg 59),(.neg 34),(.pos 64),(.pos 68)]),
   ((.exchange 59 53 6),[(.neg 59),(.neg 53),(.pos 38),(.pos 43),(.pos 49)]),
   ((.exchange 59 69 1),[(.neg 69),(.neg 59),(.pos 64),(.pos 68)]),
   ((.exchange 60 15 3),[(.neg 60),(.neg 15),(.pos 56),(.pos 57)]),
   ((.exchange 60 19 2),[(.neg 60),(.neg 19),(.pos 58),(.pos 59),(.pos 64)]),
   ((.exchange 60 21 3),[(.neg 60),(.neg 21),(.pos 57),(.pos 63)]),
   ((.exchange 60 31 3),[(.neg 60),(.neg 31),(.pos 56),(.pos 63),(.pos 67)]),
   ((.exchange 60 33 3),[(.neg 60),(.neg 33),(.pos 63),(.pos 67)]),
   ((.exchange 60 34 2),[(.neg 60),(.neg 34),(.pos 64),(.pos 68)]),
   ((.exchange 60 45 2),[(.neg 60),(.neg 45),(.pos 58),(.pos 59),(.pos 68)]),
   ((.exchange 60 52 6),[(.neg 60),(.neg 52),(.pos 38),(.pos 44),(.pos 50)]),
   ((.exchange 60 53 6),[(.neg 60),(.neg 53),(.pos 44),(.pos 50)]),
   ((.exchange 60 61 2),[(.neg 61),(.neg 60),(.pos 58),(.pos 64)]),
   ((.exchange 60 62 3),[(.neg 62),(.neg 60),(.pos 57),(.pos 63)]),
   ((.exchange 60 65 2),[(.neg 65),(.neg 60),(.pos 58),(.pos 68)]),
   ((.exchange 61 7 6),[(.neg 61),(.neg 7),(.pos 40),(.pos 42),(.pos 51)]),
   ((.exchange 61 23 0),[(.neg 61),(.neg 23),(.pos 62),(.pos 64)]),
   ((.exchange 61 32 0),[(.neg 61),(.neg 32),(.pos 62),(.pos 69)]),
   ((.exchange 61 52 0),[(.neg 61),(.neg 52),(.pos 62),(.pos 69)]),
   ((.exchange 61 54 0),[(.neg 61),(.neg 54),(.pos 64),(.pos 69)]),
   ((.exchange 62 5 6),[(.neg 62),(.neg 5),(.pos 39),(.pos 41),(.pos 52)]),
   ((.exchange 62 8 4),[(.neg 62),(.neg 8),(.pos 57),(.pos 59),(.pos 66)]),
   ((.exchange 62 14 6),[(.neg 62),(.neg 14),(.pos 41),(.pos 43),(.pos 52)]),
   ((.exchange 62 22 1),[(.neg 62),(.neg 22),(.pos 61),(.pos 64)]),
   ((.exchange 62 26 1),[(.neg 62),(.neg 26),(.pos 61),(.pos 63),(.pos 69)]),
   ((.exchange 62 33 1),[(.neg 62),(.neg 33),(.pos 63),(.pos 69)]),
   ((.exchange 62 34 1),[(.neg 62),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 62 46 1),[(.neg 62),(.neg 46),(.pos 61),(.pos 63),(.pos 69)]),
   ((.exchange 62 46 4),[(.neg 62),(.neg 46),(.pos 55),(.pos 57),(.pos 66)]),
   ((.exchange 62 54 1),[(.neg 62),(.neg 54),(.pos 64),(.pos 69)]),
   ((.exchange 62 56 4),[(.neg 62),(.neg 56),(.pos 55),(.pos 57)]),
   ((.exchange 63 7 6),[(.neg 63),(.neg 7),(.pos 40),(.pos 44),(.pos 53)]),
   ((.exchange 63 23 2),[(.neg 63),(.neg 23),(.pos 62),(.pos 64)]),
   ((.exchange 63 32 2),[(.neg 63),(.neg 32),(.pos 62),(.pos 69)]),
   ((.exchange 63 38 4),[(.neg 63),(.neg 38),(.pos 57),(.pos 60)]),
   ((.exchange 63 68 2),[(.neg 68),(.neg 63),(.pos 64),(.pos 69)]),
   ((.exchange 64 12 6),[(.neg 64),(.neg 12),(.pos 42),(.pos 54)]),
   ((.exchange 64 25 4),[(.neg 64),(.neg 25),(.pos 58),(.pos 59),(.pos 68)]),
   ((.exchange 64 30 4),[(.neg 64),(.neg 30),(.pos 60),(.pos 68)]),
   ((.exchange 64 31 3),[(.neg 64),(.neg 31),(.pos 61),(.pos 69)]),
   ((.exchange 64 33 3),[(.neg 64),(.neg 33),(.pos 63),(.pos 69)]),
   ((.exchange 64 35 3),[(.neg 64),(.neg 35),(.pos 61),(.pos 62),(.pos 63)]),
   ((.exchange 64 38 4),[(.neg 64),(.neg 38),(.pos 59),(.pos 60)]),
   ((.exchange 64 45 4),[(.neg 64),(.neg 45),(.pos 58),(.pos 59),(.pos 68)]),
   ((.exchange 64 51 6),[(.neg 64),(.neg 51),(.pos 42),(.pos 54)]),
   ((.exchange 64 53 3),[(.neg 64),(.neg 53),(.pos 63),(.pos 69)]),
   ((.exchange 64 56 4),[(.neg 64),(.neg 56),(.pos 58),(.pos 60)]),
   ((.exchange 65 9 6),[(.neg 65),(.neg 9),(.pos 45),(.pos 51)]),
   ((.exchange 65 12 6),[(.neg 65),(.neg 12),(.pos 48),(.pos 51)]),
   ((.exchange 65 23 5),[(.neg 65),(.neg 23),(.pos 55),(.pos 58),(.pos 61)]),
   ((.exchange 65 29 0),[(.neg 65),(.neg 29),(.pos 66),(.pos 68)]),
   ((.exchange 65 30 0),[(.neg 65),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 65 32 0),[(.neg 65),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 65 33 0),[(.neg 65),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 65 34 0),[(.neg 65),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 65 41 5),[(.neg 65),(.neg 41),(.pos 55),(.pos 56),(.pos 61)]),
   ((.exchange 65 49 0),[(.neg 65),(.neg 49),(.pos 66),(.pos 68)]),
   ((.exchange 65 54 0),[(.neg 65),(.neg 54),(.pos 68),(.pos 69)]),
   ((.exchange 65 60 0),[(.neg 65),(.neg 60),(.pos 67),(.pos 68)]),
   ((.exchange 65 62 0),[(.neg 65),(.neg 62),(.pos 66),(.pos 69)])]

theorem certificates_1_valid : ∀ oc ∈ certificates_1,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_2 : List (Origin 70 134 × List Sat.Literal) :=
  [((.exchange 65 63 0),[(.neg 65),(.neg 63),(.pos 67),(.pos 69)]),
   ((.exchange 66 31 1),[(.neg 66),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 66 39 6),[(.neg 66),(.neg 39),(.pos 45),(.pos 52)]),
   ((.exchange 66 43 6),[(.neg 66),(.neg 43),(.pos 49),(.pos 52)]),
   ((.exchange 66 51 6),[(.neg 66),(.neg 51),(.pos 45),(.pos 52)]),
   ((.exchange 66 54 1),[(.neg 66),(.neg 54),(.pos 68),(.pos 69)]),
   ((.exchange 67 7 6),[(.neg 67),(.neg 7),(.pos 46),(.pos 50)]),
   ((.exchange 67 17 5),[(.neg 67),(.neg 17),(.pos 56),(.pos 60)]),
   ((.exchange 67 28 2),[(.neg 67),(.neg 28),(.pos 65),(.pos 68)]),
   ((.exchange 67 31 2),[(.neg 67),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 67 34 2),[(.neg 67),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 67 44 5),[(.neg 67),(.neg 44),(.pos 60),(.pos 63)]),
   ((.exchange 67 44 6),[(.neg 67),(.neg 44),(.pos 50),(.pos 53)]),
   ((.exchange 67 54 2),[(.neg 67),(.neg 54),(.pos 68),(.pos 69)]),
   ((.exchange 67 58 2),[(.neg 67),(.neg 58),(.pos 65),(.pos 68)]),
   ((.exchange 67 58 5),[(.neg 67),(.neg 58),(.pos 56),(.pos 60)]),
   ((.exchange 67 61 2),[(.neg 67),(.neg 61),(.pos 65),(.pos 69)]),
   ((.exchange 67 64 5),[(.neg 67),(.neg 64),(.pos 60),(.pos 63)]),
   ((.exchange 68 7 6),[(.neg 68),(.neg 7),(.pos 48),(.pos 50)]),
   ((.exchange 68 8 6),[(.neg 68),(.neg 8),(.pos 49),(.pos 50)]),
   ((.exchange 68 14 6),[(.neg 68),(.neg 14),(.pos 50),(.pos 54)]),
   ((.exchange 68 17 5),[(.neg 68),(.neg 17),(.pos 58),(.pos 60)]),
   ((.exchange 68 21 3),[(.neg 68),(.neg 21),(.pos 66),(.pos 67),(.pos 69)]),
   ((.exchange 68 24 5),[(.neg 68),(.neg 24),(.pos 60),(.pos 64)]),
   ((.exchange 68 26 3),[(.neg 68),(.neg 26),(.pos 65),(.pos 67)]),
   ((.exchange 68 31 3),[(.neg 68),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 68 32 3),[(.neg 68),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 68 37 6),[(.neg 68),(.neg 37),(.pos 48),(.pos 50)]),
   ((.exchange 68 38 5),[(.neg 68),(.neg 38),(.pos 59),(.pos 60)]),
   ((.exchange 68 42 6),[(.neg 68),(.neg 42),(.pos 48),(.pos 54)]),
   ((.exchange 68 43 5),[(.neg 68),(.neg 43),(.pos 59),(.pos 64)]),
   ((.exchange 68 44 6),[(.neg 68),(.neg 44),(.pos 50),(.pos 54)]),
   ((.exchange 68 46 6),[(.neg 68),(.neg 46),(.pos 48),(.pos 50)]),
   ((.exchange 68 47 6),[(.neg 68),(.neg 47),(.pos 49),(.pos 50)]),
   ((.exchange 68 53 3),[(.neg 68),(.neg 53),(.pos 67),(.pos 69)]),
   ((.exchange 68 56 3),[(.neg 68),(.neg 56),(.pos 65),(.pos 67)]),
   ((.exchange 69 5 6),[(.neg 69),(.neg 5),(.pos 51),(.pos 52),(.pos 53)]),
   ((.exchange 69 7 6),[(.neg 69),(.neg 7),(.pos 51),(.pos 53),(.pos 54)]),
   ((.exchange 69 15 5),[(.neg 69),(.neg 15),(.pos 61),(.pos 62),(.pos 63)]),
   ((.exchange 69 17 5),[(.neg 69),(.neg 17),(.pos 61),(.pos 63),(.pos 64)]),
   ((.exchange 69 23 5),[(.neg 69),(.neg 23),(.pos 62),(.pos 64)]),
   ((.exchange 69 24 5),[(.neg 69),(.neg 24),(.pos 63),(.pos 64)]),
   ((.exchange 69 25 4),[(.neg 69),(.neg 25),(.pos 65),(.pos 66)]),
   ((.exchange 69 28 4),[(.neg 69),(.neg 28),(.pos 65),(.pos 68)]),
   ((.exchange 69 30 4),[(.neg 69),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 69 39 6),[(.neg 69),(.neg 39),(.pos 51),(.pos 52)]),
   ((.exchange 69 41 5),[(.neg 69),(.neg 41),(.pos 62),(.pos 63)]),
   ((.exchange 69 44 5),[(.neg 69),(.neg 44),(.pos 63),(.pos 64)]),
   ((.exchange 69 44 6),[(.neg 69),(.neg 44),(.pos 53),(.pos 54)]),
   ((.exchange 69 46 4),[(.neg 69),(.neg 46),(.pos 65),(.pos 67)]),
   ((.exchange 69 49 4),[(.neg 69),(.neg 49),(.pos 66),(.pos 68)]),
   ((.exchange 69 50 6),[(.neg 69),(.neg 50),(.pos 53),(.pos 54)]),
   ((.exchange 69 56 4),[(.neg 69),(.neg 56),(.pos 65),(.pos 67)]),
   ((.exchange 69 57 5),[(.neg 69),(.neg 57),(.pos 62),(.pos 63)]),
   ((.exchange 69 59 4),[(.neg 69),(.neg 59),(.pos 66),(.pos 68)]),
   ((.exchange 69 60 4),[(.neg 69),(.neg 60),(.pos 67),(.pos 68)]),
   (.newPoint,[(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 0),[(.neg 69),(.neg 68),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 56),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 47),(.pos 48),(.pos 49),(.pos 52),(.pos 55),(.pos 57),(.pos 58),(.pos 59),(.pos 62),(.pos 66),(.pos 67)]),
   ((.excluded 1),[(.neg 69),(.neg 68),(.neg 65),(.neg 64),(.neg 62),(.neg 59),(.neg 58),(.neg 55),(.neg 54),(.neg 52),(.neg 49),(.neg 48),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 46),(.pos 47),(.pos 50),(.pos 51),(.pos 53),(.pos 56),(.pos 57),(.pos 60),(.pos 61),(.pos 63),(.pos 66),(.pos 67)]),
   ((.excluded 2),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 47),(.pos 57),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 3),[(.neg 69),(.neg 68),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 47),(.pos 54),(.pos 57),(.pos 64),(.pos 66),(.pos 67)]),
   ((.excluded 4),[(.neg 69),(.neg 68),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 47),(.pos 57),(.pos 66),(.pos 67)]),
   ((.excluded 5),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 62),(.neg 60),(.neg 57),(.neg 54),(.neg 52),(.neg 50),(.neg 47),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 48),(.pos 49),(.pos 51),(.pos 53),(.pos 55),(.pos 56),(.pos 58),(.pos 59),(.pos 61),(.pos 63),(.pos 65)]),
   ((.excluded 6),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 50),(.pos 54),(.pos 55),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 68)]),
   ((.excluded 7),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 58),(.pos 59),(.pos 69)]),
   ((.excluded 8),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 48),(.pos 49),(.pos 55),(.pos 58),(.pos 59)]),
   ((.excluded 9),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 55),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 46),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 56),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 10),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 54),(.pos 64),(.pos 65)]),
   ((.excluded 11),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 54),(.pos 64)]),
   ((.excluded 12),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 55),(.neg 54),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 46),(.pos 51),(.pos 53),(.pos 56),(.pos 61),(.pos 63),(.pos 68)]),
   ((.excluded 13),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 55),(.neg 54),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 46),(.pos 51),(.pos 53),(.pos 56),(.pos 61),(.pos 63)]),
   ((.excluded 14),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 50),(.pos 52),(.pos 60),(.pos 62),(.pos 65)]),
   ((.excluded 15),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 50),(.pos 52),(.pos 60),(.pos 62)]),
   ((.excluded 16),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 50),(.pos 60),(.pos 65)]),
   ((.excluded 17),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 50),(.pos 60),(.pos 69)]),
   ((.excluded 18),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 50),(.pos 60)]),
   ((.excluded 19),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 52),(.pos 62),(.pos 65)]),
   ((.excluded 20),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 52),(.pos 62),(.pos 68)]),
   ((.excluded 21),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 52),(.pos 62)]),
   ((.excluded 22),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 65)]),
   ((.excluded 23),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 68)]),
   ((.excluded 24),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 69)]),
   ((.excluded 25),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44)]),
   ((.excluded 26),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 57),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 27),[(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 28),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 57),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 29),[(.neg 69),(.neg 68),(.neg 65),(.neg 64),(.neg 62),(.neg 59),(.neg 58),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 45),(.pos 47),(.pos 48),(.pos 49),(.pos 52),(.pos 56),(.pos 57),(.pos 60),(.pos 61),(.pos 63),(.pos 66),(.pos 67)]),
   ((.excluded 30),[(.neg 69),(.neg 68),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 45),(.pos 47),(.pos 48),(.pos 49),(.pos 52),(.pos 57),(.pos 64),(.pos 66),(.pos 67)]),
   ((.excluded 31),[(.neg 69),(.neg 68),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 45),(.pos 47),(.pos 48),(.pos 49),(.pos 52),(.pos 57),(.pos 66),(.pos 67)]),
   ((.excluded 32),[(.neg 69),(.neg 68),(.neg 65),(.neg 64),(.neg 62),(.neg 59),(.neg 58),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 54),(.pos 56),(.pos 57),(.pos 60),(.pos 61),(.pos 63),(.pos 66),(.pos 67)]),
   ((.excluded 33),[(.neg 69),(.neg 68),(.neg 65),(.neg 64),(.neg 62),(.neg 59),(.neg 58),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 56),(.pos 57),(.pos 60),(.pos 61),(.pos 63),(.pos 66),(.pos 67)]),
   ((.excluded 34),[(.neg 69),(.neg 68),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 56),(.neg 54),(.neg 52),(.neg 49),(.neg 48),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 46),(.pos 47),(.pos 50),(.pos 51),(.pos 53),(.pos 55),(.pos 57),(.pos 58),(.pos 59),(.pos 62),(.pos 66),(.pos 67)]),
   ((.excluded 35),[(.neg 69),(.neg 68),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 49),(.neg 48),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 46),(.pos 47),(.pos 50),(.pos 51),(.pos 53),(.pos 57),(.pos 64),(.pos 66),(.pos 67)]),
   ((.excluded 36),[(.neg 69),(.neg 68),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 49),(.neg 48),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 46),(.pos 47),(.pos 50),(.pos 51),(.pos 53),(.pos 57),(.pos 66),(.pos 67)]),
   ((.excluded 37),[(.neg 69),(.neg 68),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 54),(.pos 55),(.pos 57),(.pos 58),(.pos 59),(.pos 62),(.pos 66),(.pos 67)]),
   ((.excluded 38),[(.neg 69),(.neg 68),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 55),(.pos 57),(.pos 58),(.pos 59),(.pos 62),(.pos 66),(.pos 67)]),
   ((.excluded 39),[(.neg 69),(.neg 68),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 54),(.pos 57),(.pos 66),(.pos 67)]),
   ((.excluded 40),[(.neg 69),(.neg 68),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 57),(.pos 64),(.pos 66),(.pos 67)]),
   ((.excluded 41),[(.neg 69),(.neg 68),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 57),(.pos 66),(.pos 67)]),
   ((.excluded 42),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 50),(.neg 47),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 45),(.pos 46),(.pos 48),(.pos 49),(.pos 51),(.pos 53),(.pos 64),(.pos 65)]),
   ((.excluded 43),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 50),(.neg 47),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 45),(.pos 46),(.pos 48),(.pos 49),(.pos 51),(.pos 53),(.pos 60),(.pos 62),(.pos 65)]),
   ((.excluded 44),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 50),(.neg 47),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 45),(.pos 46),(.pos 48),(.pos 49),(.pos 51),(.pos 53),(.pos 60),(.pos 65)]),
   ((.excluded 45),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 50),(.neg 47),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 45),(.pos 46),(.pos 48),(.pos 49),(.pos 51),(.pos 53),(.pos 62),(.pos 65)]),
   ((.excluded 46),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 50),(.neg 47),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 45),(.pos 46),(.pos 48),(.pos 49),(.pos 51),(.pos 53),(.pos 65)]),
   ((.excluded 47),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 45),(.pos 48),(.pos 49),(.pos 50),(.pos 54),(.pos 56),(.pos 61),(.pos 63),(.pos 68)]),
   ((.excluded 48),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 45),(.pos 48),(.pos 49),(.pos 50),(.pos 54),(.pos 62),(.pos 68)]),
   ((.excluded 49),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 45),(.pos 48),(.pos 49),(.pos 50),(.pos 54),(.pos 68)]),
   ((.excluded 50),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 45),(.pos 48),(.pos 49),(.pos 56),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 51),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 45),(.pos 48),(.pos 49),(.pos 56),(.pos 61),(.pos 63)]),
   ((.excluded 52),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 45),(.pos 48),(.pos 49),(.pos 64)]),
   ((.excluded 53),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 45),(.pos 48),(.pos 49),(.pos 60),(.pos 62)]),
   ((.excluded 54),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 45),(.pos 48),(.pos 49),(.pos 62)]),
   ((.excluded 55),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 45),(.pos 48),(.pos 49),(.pos 60),(.pos 69)]),
   ((.excluded 56),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 45),(.pos 48),(.pos 49),(.pos 60)]),
   ((.excluded 57),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 45),(.pos 48),(.pos 49),(.pos 69)]),
   ((.excluded 58),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 45),(.pos 48),(.pos 49)]),
   ((.excluded 59),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 62),(.neg 60),(.neg 57),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 54),(.pos 55),(.pos 56),(.pos 58),(.pos 59),(.pos 61),(.pos 63),(.pos 65)]),
   ((.excluded 60),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 62),(.neg 60),(.neg 57),(.neg 54),(.neg 53),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 50),(.pos 52),(.pos 55),(.pos 56),(.pos 58),(.pos 59),(.pos 61),(.pos 63),(.pos 65)]),
   ((.excluded 61),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 62),(.neg 60),(.neg 57),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 50),(.pos 55),(.pos 56),(.pos 58),(.pos 59),(.pos 61),(.pos 63),(.pos 65)]),
   ((.excluded 62),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 62),(.neg 60),(.neg 57),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 52),(.pos 55),(.pos 56),(.pos 58),(.pos 59),(.pos 61),(.pos 63),(.pos 65)]),
   ((.excluded 63),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 62),(.neg 60),(.neg 57),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 55),(.pos 56),(.pos 58),(.pos 59),(.pos 61),(.pos 63),(.pos 65)]),
   ((.excluded 64),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 50),(.pos 56),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 65),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 56),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 66),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 54),(.pos 56),(.pos 61),(.pos 63)]),
   ((.excluded 67),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 50),(.pos 52),(.pos 56),(.pos 61),(.pos 63)]),
   ((.excluded 68),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 50),(.pos 56),(.pos 61),(.pos 63)]),
   ((.excluded 69),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 52),(.pos 56),(.pos 61),(.pos 63),(.pos 68)]),
   ((.excluded 70),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 52),(.pos 56),(.pos 61),(.pos 63)])]

theorem certificates_2_valid : ∀ oc ∈ certificates_2,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_3 : List (Origin 70 134 × List Sat.Literal) :=
  [((.excluded 71),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 56),(.pos 61),(.pos 63),(.pos 68)]),
   ((.excluded 72),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 56),(.pos 61),(.pos 63)]),
   ((.excluded 73),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 46),(.pos 51),(.pos 53),(.pos 55),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 68)]),
   ((.excluded 74),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 52),(.pos 55),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 68)]),
   ((.excluded 75),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 55),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 68)]),
   ((.excluded 76),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 46),(.pos 51),(.pos 53),(.pos 62),(.pos 68)]),
   ((.excluded 77),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 46),(.pos 51),(.pos 53),(.pos 68)]),
   ((.excluded 78),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 52),(.pos 68)]),
   ((.excluded 79),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 62),(.pos 68)]),
   ((.excluded 80),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 68)]),
   ((.excluded 81),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 46),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 58),(.pos 59),(.pos 69)]),
   ((.excluded 82),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 46),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 60),(.pos 69)]),
   ((.excluded 83),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 46),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 69)]),
   ((.excluded 84),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 46),(.pos 51),(.pos 53),(.pos 55),(.pos 58),(.pos 59)]),
   ((.excluded 85),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 46),(.pos 51),(.pos 53),(.pos 64)]),
   ((.excluded 86),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 46),(.pos 51),(.pos 53),(.pos 60),(.pos 62)]),
   ((.excluded 87),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 46),(.pos 51),(.pos 53),(.pos 60)]),
   ((.excluded 88),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 46),(.pos 51),(.pos 53),(.pos 62)]),
   ((.excluded 89),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 46),(.pos 51),(.pos 53)]),
   ((.excluded 90),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 54),(.pos 55),(.pos 58),(.pos 59)]),
   ((.excluded 91),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 50),(.pos 52),(.pos 55),(.pos 58),(.pos 59)]),
   ((.excluded 92),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 52),(.pos 55),(.pos 58),(.pos 59)]),
   ((.excluded 93),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 50),(.pos 55),(.pos 58),(.pos 59),(.pos 69)]),
   ((.excluded 94),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 50),(.pos 55),(.pos 58),(.pos 59)]),
   ((.excluded 95),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 55),(.pos 58),(.pos 59),(.pos 69)]),
   ((.excluded 96),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 55),(.pos 58),(.pos 59)]),
   ((.excluded 97),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 50),(.pos 69)]),
   ((.excluded 98),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 60),(.pos 69)]),
   ((.excluded 99),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 69)]),
   ((.excluded 100),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 54),(.pos 60),(.pos 62),(.pos 65)]),
   ((.excluded 101),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 54),(.pos 60),(.pos 62)]),
   ((.excluded 102),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 54),(.pos 60),(.pos 65)]),
   ((.excluded 103),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 54),(.pos 60)]),
   ((.excluded 104),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 54),(.pos 62),(.pos 65)]),
   ((.excluded 105),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 54),(.pos 62)]),
   ((.excluded 106),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 54),(.pos 65)]),
   ((.excluded 107),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 54)]),
   ((.excluded 108),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 52),(.pos 60),(.pos 65)]),
   ((.excluded 109),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 52),(.pos 60)]),
   ((.excluded 110),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 60),(.pos 62),(.pos 65)]),
   ((.excluded 111),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 60),(.pos 62)]),
   ((.excluded 112),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 60),(.pos 65)]),
   ((.excluded 113),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 60)]),
   ((.excluded 114),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 50),(.pos 62),(.pos 65)]),
   ((.excluded 115),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 50),(.pos 62)]),
   ((.excluded 116),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 62),(.pos 65)]),
   ((.excluded 117),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 62)]),
   ((.excluded 118),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 50),(.pos 52),(.pos 64),(.pos 65)]),
   ((.excluded 119),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 50),(.pos 52),(.pos 64)]),
   ((.excluded 120),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 50),(.pos 52),(.pos 65)]),
   ((.excluded 121),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 50),(.pos 52)]),
   ((.excluded 122),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 50),(.pos 64),(.pos 65)]),
   ((.excluded 123),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 50),(.pos 64)]),
   ((.excluded 124),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 50),(.pos 65)]),
   ((.excluded 125),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 50)]),
   ((.excluded 126),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 52),(.pos 64),(.pos 65)]),
   ((.excluded 127),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 52),(.pos 64)]),
   ((.excluded 128),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 52),(.pos 65)]),
   ((.excluded 129),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 52)]),
   ((.excluded 130),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 64),(.pos 65)]),
   ((.excluded 131),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 64)]),
   ((.excluded 132),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 65)]),
   ((.excluded 133),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40)])]

theorem certificates_3_valid : ∀ oc ∈ certificates_3,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



theorem witness_0 : ∀ j : Fin 128,
    let w : Fin 134 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 128,
      let w : Fin 134 := ⟨0 + j.val,by omega⟩
      target w < MatroidCatalogue.count 8 4 ∧
        Papers.RationalityTen.MatroidChecked.FastSemanticChecks.RawWitness 8 (N7R4.familyMasks.get 49)
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



theorem witness_1 : ∀ j : Fin 6,
    let w : Fin 134 := ⟨128 + j.val,by omega⟩
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 6,
      let w : Fin 134 := ⟨128 + j.val,by omega⟩
      target w < MatroidCatalogue.count 8 4 ∧
        Papers.RationalityTen.MatroidChecked.FastSemanticChecks.RawWitness 8 (N7R4.familyMasks.get 49)
        (fun i : Fin 70 => N8R4.gridMasks.get i.val) newIndex (models w)
        (N8R4.familyMasks.get (target w)) (permutation w) := by
    refine (Fin.forall_fin_add (m := 3) (n := 3) _).2 ⟨?_, ?_⟩
    · decide +kernel
    · decide +kernel
  intro j
  have hj := hfast j
  exact ⟨hj.1,Papers.RationalityTen.MatroidChecked.FastSemanticChecks.rawWitness_sound 8 _ _ _ _ _ _ hj.2⟩


end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C49

/- Source: MatroidCatalogue/Cases/N8R4C49Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C49

noncomputable def certificates : List (Origin 70 134 × List Sat.Literal) :=
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

theorem models_valid : ∀ w : Fin 134,
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  by_cases h0 : w.val < 128
  ·
    have hh := witness_0 ⟨w.val - 0,by omega⟩
    have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 134) = w := Fin.ext (by dsimp only; omega)
    dsimp only at hh
    rw [heq] at hh
    exact hh
  ·
    have hh := witness_1 ⟨w.val - 128,by omega⟩
    have heq : (⟨128 + (w.val - 128),by omega⟩ : Fin 134) = w := Fin.ext (by dsimp only; omega)
    dsimp only at hh
    rw [heq] at hh
    exact hh

theorem coverage (M : BasisFamily (groundPrefix 8) 4)
    (hold : M.bases.filter ((7 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 8 4, IsomorphicWithin 8 M.bases B := by
  apply extension_covered_of_certificate (n:=7) (r:=4) (by decide)
    catalogue old U newIndex models certificates
    N8R4.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C49.formula []
    exact Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C49.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 8 4 (target w),family_mem 8 4 (target w) hw.1,?_⟩
    exact validWitness_sound 8 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C49

end
end
end BundlePart5
