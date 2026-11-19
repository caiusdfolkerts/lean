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
/- Source: MatroidChecked/SemanticChunks/Cases03Part00.lean -/






@[expose] public section
noncomputable section

/- Source: MatroidCatalogue/Cases/N8R4C13Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C13

abbrev U := N8R4.grid
noncomputable def old : Finset (Finset (Fin 8)) := N7R4.family 13
noncomputable def newIndexTree : Table ℕ := (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf 35) (.leaf 36)) (.node 3 (.leaf 37) (.leaf 38))) (.node 6 (.node 5 (.leaf 39) (.leaf 40)) (.node 7 (.leaf 41) (.leaf 42)))) (.node 12 (.node 10 (.node 9 (.leaf 43) (.leaf 44)) (.node 11 (.leaf 45) (.leaf 46))) (.node 14 (.node 13 (.leaf 47) (.leaf 48)) (.node 15 (.leaf 49) (.node 16 (.leaf 50) (.leaf 51)))))) (.node 26 (.node 21 (.node 19 (.node 18 (.leaf 52) (.leaf 53)) (.node 20 (.leaf 54) (.leaf 55))) (.node 23 (.node 22 (.leaf 56) (.leaf 57)) (.node 24 (.leaf 58) (.node 25 (.leaf 59) (.leaf 60))))) (.node 30 (.node 28 (.node 27 (.leaf 61) (.leaf 62)) (.node 29 (.leaf 63) (.leaf 64))) (.node 32 (.node 31 (.leaf 65) (.leaf 66)) (.node 33 (.leaf 67) (.node 34 (.leaf 68) (.leaf 69)))))))
noncomputable def newIndex (i : Fin 35) : Fin 70 := Fin.ofNat 70 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 21 (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (30870077440,18,6248648)) (.leaf (29729226752,22,8345736))) (.node 3 (.leaf (25165824000,22,8344840)) (.node 4 (.leaf (17112760320,25,6248648)) (.leaf (34292629504,26,10442376))))) (.node 7 (.node 6 (.leaf (16171139072,35,8334088)) (.leaf (1071644672,35,8219400))) (.node 8 (.leaf (17177772032,44,14599816)) (.node 9 (.leaf (29861347328,39,8345736)) (.leaf (25566380032,39,8344840)))))) (.node 15 (.node 12 (.node 11 (.leaf (34156314624,40,12535432)) (.leaf (29525803008,42,10442376))) (.node 13 (.leaf (30062673920,43,12478088)) (.node 14 (.leaf (25499271168,42,10413704)) (.leaf (25767706624,43,12477640))))) (.node 18 (.node 16 (.leaf (30867980288,39,8317064)) (.node 17 (.leaf (30599544832,39,8316168)) (.leaf (31136415744,40,12478088)))) (.node 19 (.leaf (34089205760,43,12535432)) (.node 20 (.leaf (33820770304,43,12534984)) (.leaf (34357641216,45,14599816))))))) (.node 32 (.node 26 (.node 23 (.node 22 (.leaf (1047520,105,7072520)) (.leaf (30871124960,119,11789960))) (.node 24 (.leaf (29730274272,125,11789960)) (.node 25 (.leaf (25166871520,125,11789512)) (.leaf (17113807840,132,16434824))))) (.node 29 (.node 27 (.leaf (34293677024,133,16434824)) (.node 28 (.leaf (16172186592,134,16434824)) (.leaf (1072692192,134,16406152)))) (.node 30 (.leaf (17178819552,135,16434824)) (.node 31 (.leaf (29862394848,136,16434824)) (.leaf (25567427552,136,16434376)))))) (.node 37 (.node 34 (.node 33 (.leaf (34157362144,137,16434824)) (.leaf (30869027808,136,16406152))) (.node 35 (.leaf (30600592352,136,16405704)) (.node 36 (.leaf (31137463264,137,16406152)) (.leaf (25500318688,138,16434824))))) (.node 40 (.node 38 (.leaf (34090253280,139,16434824)) (.node 39 (.leaf (25768754144,139,16405704)) (.leaf (29526850528,138,16406152)))) (.node 41 (.leaf (33821817824,139,16434376)) (.node 42 (.leaf (30063721440,139,16406152)) (.leaf (34358688736,140,16434824))))))))

noncomputable def models (i : Fin 43) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 43) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 43) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 70, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (7 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 70, (7 : Fin 8) ∈ U i → ∃ j : Fin 35, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C13

/- Source: MatroidCatalogue/Cases/N8R4C13Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C13


noncomputable def certificates_0 : List (Origin 70 43 × List Sat.Literal) :=
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
   ((.fixed 33),[(.pos 33)]),
   ((.fixed 34),[(.pos 34)]),
   ((.exchange 20 41 6),[(.neg 41),(.neg 20),(.pos 1),(.pos 40)]),
   ((.exchange 20 57 4),[(.neg 57),(.neg 20),(.pos 15),(.pos 56)]),
   ((.exchange 20 58 4),[(.neg 58),(.neg 20),(.pos 17),(.pos 56)]),
   ((.exchange 20 59 4),[(.neg 59),(.neg 20),(.pos 15),(.pos 17),(.pos 56)]),
   ((.exchange 20 60 4),[(.neg 60),(.neg 20),(.pos 17),(.pos 56)]),
   ((.exchange 20 62 2),[(.neg 62),(.neg 20),(.pos 19),(.pos 61)]),
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
   ((.exchange 21 53 6),[(.neg 53),(.neg 21),(.pos 11),(.pos 41)]),
   ((.exchange 21 54 6),[(.neg 54),(.neg 21),(.pos 4),(.pos 11),(.pos 41)]),
   ((.exchange 21 56 4),[(.neg 56),(.neg 21),(.pos 15),(.pos 57)]),
   ((.exchange 21 61 2),[(.neg 61),(.neg 21),(.pos 19),(.pos 62)]),
   ((.exchange 22 41 6),[(.neg 41),(.neg 22),(.pos 2),(.pos 3),(.pos 42)]),
   ((.exchange 22 56 4),[(.neg 56),(.neg 22),(.pos 17),(.pos 58)]),
   ((.exchange 23 41 6),[(.neg 41),(.neg 23),(.pos 4),(.pos 43)]),
   ((.exchange 23 56 4),[(.neg 56),(.neg 23),(.pos 16),(.pos 18),(.pos 59)]),
   ((.exchange 24 41 6),[(.neg 41),(.neg 24),(.pos 4),(.pos 44)]),
   ((.exchange 24 56 4),[(.neg 56),(.neg 24),(.pos 17),(.pos 60)]),
   ((.exchange 26 41 6),[(.neg 41),(.neg 26),(.pos 5),(.pos 10),(.pos 46)]),
   ((.exchange 26 66 2),[(.neg 66),(.neg 26),(.pos 25),(.pos 65)]),
   ((.exchange 27 41 6),[(.neg 41),(.neg 27),(.pos 11),(.pos 47)]),
   ((.exchange 27 65 2),[(.neg 65),(.neg 27),(.pos 25),(.pos 66)]),
   ((.exchange 28 41 6),[(.neg 41),(.neg 28),(.pos 6),(.pos 7),(.pos 12),(.pos 48)]),
   ((.exchange 29 41 6),[(.neg 41),(.neg 29),(.pos 8),(.pos 13),(.pos 49)]),
   ((.exchange 30 41 6),[(.neg 41),(.neg 30),(.pos 8),(.pos 14),(.pos 50)]),
   ((.exchange 31 41 6),[(.neg 41),(.neg 31),(.pos 9),(.pos 10),(.pos 51)]),
   ((.exchange 32 41 6),[(.neg 41),(.neg 32),(.pos 11),(.pos 52)]),
   ((.exchange 33 41 6),[(.neg 41),(.neg 33),(.pos 11),(.pos 53)]),
   ((.exchange 34 41 6),[(.neg 41),(.neg 34),(.pos 13),(.pos 14),(.pos 54)]),
   ((.exchange 35 20 7),[(.neg 35),(.neg 20),(.pos 1),(.pos 15)]),
   ((.exchange 36 20 7),[(.neg 36),(.neg 20),(.pos 0),(.pos 2),(.pos 16)]),
   ((.exchange 37 20 7),[(.neg 37),(.neg 20),(.pos 3),(.pos 17)]),
   ((.exchange 38 20 7),[(.neg 38),(.neg 20),(.pos 0),(.pos 4),(.pos 18)]),
   ((.exchange 39 20 7),[(.neg 39),(.neg 20),(.pos 1),(.pos 19)]),
   ((.exchange 45 20 7),[(.neg 45),(.neg 20),(.pos 5),(.pos 9),(.pos 25)]),
   ((.exchange 55 20 7),[(.neg 55),(.neg 20),(.pos 15),(.pos 19)]),
   ((.exchange 56 31 2),[(.neg 56),(.neg 31),(.pos 61),(.pos 65)]),
   ((.exchange 56 33 0),[(.neg 56),(.neg 33),(.pos 63),(.pos 67)]),
   ((.exchange 57 31 2),[(.neg 57),(.neg 31),(.pos 55),(.pos 62),(.pos 66)]),
   ((.exchange 58 34 0),[(.neg 58),(.neg 34),(.pos 64),(.pos 68)]),
   ((.exchange 58 69 3),[(.neg 69),(.neg 58),(.pos 61),(.pos 65)]),
   ((.exchange 59 69 3),[(.neg 69),(.neg 59),(.pos 62),(.pos 66)]),
   ((.exchange 60 33 3),[(.neg 60),(.neg 33),(.pos 63),(.pos 67)]),
   ((.exchange 60 34 2),[(.neg 60),(.neg 34),(.pos 64),(.pos 68)]),
   ((.exchange 61 26 4),[(.neg 61),(.neg 26),(.pos 56),(.pos 65)]),
   ((.exchange 61 33 0),[(.neg 61),(.neg 33),(.pos 63),(.pos 69)]),
   ((.exchange 61 34 0),[(.neg 61),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 61 54 0),[(.neg 61),(.neg 54),(.pos 64),(.pos 69)]),
   ((.exchange 62 26 4),[(.neg 62),(.neg 26),(.pos 55),(.pos 57),(.pos 66)]),
   ((.exchange 62 33 1),[(.neg 62),(.neg 33),(.pos 63),(.pos 69)]),
   ((.exchange 62 34 1),[(.neg 62),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 62 44 1),[(.neg 62),(.neg 44),(.pos 63),(.pos 64)]),
   ((.exchange 62 53 1),[(.neg 62),(.neg 53),(.pos 63),(.pos 69)]),
   ((.exchange 62 54 1),[(.neg 62),(.neg 54),(.pos 64),(.pos 69)]),
   ((.exchange 63 22 2),[(.neg 63),(.neg 22),(.pos 61),(.pos 64)]),
   ((.exchange 63 23 2),[(.neg 63),(.neg 23),(.pos 62),(.pos 64)]),
   ((.exchange 63 30 4),[(.neg 63),(.neg 30),(.pos 60),(.pos 67)]),
   ((.exchange 63 31 2),[(.neg 63),(.neg 31),(.pos 61),(.pos 69)]),
   ((.exchange 63 32 2),[(.neg 63),(.neg 32),(.pos 62),(.pos 69)]),
   ((.exchange 63 34 2),[(.neg 63),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 63 51 2),[(.neg 63),(.neg 51),(.pos 61),(.pos 69)]),
   ((.exchange 63 52 2),[(.neg 63),(.neg 52),(.pos 62),(.pos 69)]),
   ((.exchange 63 68 4),[(.neg 68),(.neg 63),(.pos 60),(.pos 67)]),
   ((.exchange 64 20 3),[(.neg 64),(.neg 20),(.pos 61),(.pos 63)]),
   ((.exchange 64 21 3),[(.neg 64),(.neg 21),(.pos 62),(.pos 63)]),
   ((.exchange 64 26 4),[(.neg 64),(.neg 26),(.pos 58),(.pos 60),(.pos 68)]),
   ((.exchange 64 28 4),[(.neg 64),(.neg 28),(.pos 58),(.pos 68)]),
   ((.exchange 64 32 3),[(.neg 64),(.neg 32),(.pos 62),(.pos 69)]),
   ((.exchange 64 33 3),[(.neg 64),(.neg 33),(.pos 63),(.pos 69)]),
   ((.exchange 64 53 3),[(.neg 64),(.neg 53),(.pos 63),(.pos 69)]),
   ((.exchange 64 56 3),[(.neg 64),(.neg 56),(.pos 61),(.pos 63)]),
   ((.exchange 64 57 3),[(.neg 64),(.neg 57),(.pos 62),(.pos 63)]),
   ((.exchange 65 24 0),[(.neg 65),(.neg 24),(.pos 67),(.pos 68),(.pos 69)]),
   ((.exchange 65 34 0),[(.neg 65),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 65 42 5),[(.neg 65),(.neg 42),(.pos 58),(.pos 61)]),
   ((.exchange 65 64 0),[(.neg 65),(.neg 64),(.pos 68),(.pos 69)]),
   ((.exchange 65 64 5),[(.neg 65),(.neg 64),(.pos 58),(.pos 61)]),
   ((.exchange 66 20 5),[(.neg 66),(.neg 20),(.pos 55),(.pos 57),(.pos 62)]),
   ((.exchange 66 34 1),[(.neg 66),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 66 42 5),[(.neg 66),(.neg 42),(.pos 55),(.pos 59),(.pos 62)]),
   ((.exchange 66 54 1),[(.neg 66),(.neg 54),(.pos 68),(.pos 69)]),
   ((.exchange 66 60 1),[(.neg 66),(.neg 60),(.pos 67),(.pos 68)]),
   ((.exchange 66 64 1),[(.neg 66),(.neg 64),(.pos 68),(.pos 69)]),
   ((.exchange 66 64 5),[(.neg 66),(.neg 64),(.pos 59),(.pos 62)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_1 : List (Origin 70 43 × List Sat.Literal) :=
  [((.exchange 67 20 5),[(.neg 67),(.neg 20),(.pos 56),(.pos 63)]),
   ((.exchange 67 29 2),[(.neg 67),(.neg 29),(.pos 66),(.pos 68)]),
   ((.exchange 67 31 2),[(.neg 67),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 67 32 2),[(.neg 67),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 67 34 2),[(.neg 67),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 67 61 5),[(.neg 67),(.neg 61),(.pos 56),(.pos 63)]),
   ((.exchange 68 20 5),[(.neg 68),(.neg 20),(.pos 58),(.pos 60),(.pos 64)]),
   ((.exchange 68 26 3),[(.neg 68),(.neg 26),(.pos 65),(.pos 67)]),
   ((.exchange 68 27 3),[(.neg 68),(.neg 27),(.pos 66),(.pos 67)]),
   ((.exchange 68 33 3),[(.neg 68),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 68 44 5),[(.neg 68),(.neg 44),(.pos 60),(.pos 64)]),
   ((.exchange 68 47 3),[(.neg 68),(.neg 47),(.pos 66),(.pos 67)]),
   ((.exchange 68 56 3),[(.neg 68),(.neg 56),(.pos 65),(.pos 67)]),
   ((.exchange 68 57 3),[(.neg 68),(.neg 57),(.pos 66),(.pos 67)]),
   ((.exchange 68 63 5),[(.neg 68),(.neg 63),(.pos 60),(.pos 64)]),
   ((.exchange 69 21 5),[(.neg 69),(.neg 21),(.pos 62),(.pos 63)]),
   ((.exchange 69 22 5),[(.neg 69),(.neg 22),(.pos 61),(.pos 64)]),
   ((.exchange 69 23 5),[(.neg 69),(.neg 23),(.pos 62),(.pos 64)]),
   ((.exchange 69 24 5),[(.neg 69),(.neg 24),(.pos 63),(.pos 64)]),
   ((.exchange 69 28 4),[(.neg 69),(.neg 28),(.pos 65),(.pos 68)]),
   ((.exchange 69 29 4),[(.neg 69),(.neg 29),(.pos 66),(.pos 68)]),
   ((.exchange 69 30 4),[(.neg 69),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 69 48 4),[(.neg 69),(.neg 48),(.pos 65),(.pos 68)]),
   ((.exchange 69 49 4),[(.neg 69),(.neg 49),(.pos 66),(.pos 68)]),
   ((.exchange 69 57 4),[(.neg 69),(.neg 57),(.pos 66),(.pos 67)]),
   ((.exchange 69 60 5),[(.neg 69),(.neg 60),(.pos 63),(.pos 64)]),
   (.newPoint,[(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 0),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 65),(.pos 66)]),
   ((.excluded 1),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 2),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 68)]),
   ((.excluded 3),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 69)]),
   ((.excluded 4),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60)]),
   ((.excluded 5),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 6),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 7),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 69)]),
   ((.excluded 8),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 61),(.pos 62),(.pos 67)]),
   ((.excluded 9),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 61),(.pos 62),(.pos 68)]),
   ((.excluded 10),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 11),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 64),(.pos 67)]),
   ((.excluded 12),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 67)]),
   ((.excluded 13),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 63),(.pos 68)]),
   ((.excluded 14),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 68)]),
   ((.excluded 15),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 63),(.pos 65),(.pos 66)]),
   ((.excluded 16),[(.neg 69),(.neg 68),(.neg 67),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 64),(.pos 65),(.pos 66)]),
   ((.excluded 17),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 65),(.pos 66)]),
   ((.excluded 18),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 63)]),
   ((.excluded 19),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 64)]),
   ((.excluded 20),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55)]),
   ((.excluded 21),[(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 22),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 65),(.pos 66)]),
   ((.excluded 23),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 24),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 68)]),
   ((.excluded 25),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 69)]),
   ((.excluded 26),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60)]),
   ((.excluded 27),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 55),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 28),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 55),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 29),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 55),(.pos 69)]),
   ((.excluded 30),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 55),(.pos 61),(.pos 62),(.pos 67)]),
   ((.excluded 31),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 55),(.pos 61),(.pos 62),(.pos 68)]),
   ((.excluded 32),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 33),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 55),(.pos 63),(.pos 65),(.pos 66)]),
   ((.excluded 34),[(.neg 69),(.neg 68),(.neg 67),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 55),(.pos 64),(.pos 65),(.pos 66)]),
   ((.excluded 35),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 55),(.pos 65),(.pos 66)]),
   ((.excluded 36),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 55),(.pos 63),(.pos 68)]),
   ((.excluded 37),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 55),(.pos 63)]),
   ((.excluded 38),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 55),(.pos 68)]),
   ((.excluded 39),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 55),(.pos 64),(.pos 67)]),
   ((.excluded 40),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 55),(.pos 64)]),
   ((.excluded 41),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 55),(.pos 67)]),
   ((.excluded 42),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 55)])]

theorem certificates_1_valid : ∀ oc ∈ certificates_1,
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
        Papers.RationalityTen.MatroidChecked.FastSemanticChecks.RawWitness 8 (N7R4.familyMasks.get 13)
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


end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C13

/- Source: MatroidCatalogue/Cases/N8R4C13Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C13

noncomputable def certificates : List (Origin 70 43 × List Sat.Literal) :=
  certificates_0 ++ certificates_1

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  intro oc hoc
  simp only [certificates,List.mem_append,or_assoc] at hoc
  rcases hoc with h0 | h1
  · exact certificates_0_valid oc h0
  · exact certificates_1_valid oc h1

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
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C13.formula []
    exact Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C13.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 8 4 (target w),family_mem 8 4 (target w) hw.1,?_⟩
    exact validWitness_sound 8 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C13

/- Source: MatroidCatalogue/Cases/N8R4C14Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C14

abbrev U := N8R4.grid
noncomputable def old : Finset (Finset (Fin 8)) := N7R4.family 14
noncomputable def newIndexTree : Table ℕ := (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf 35) (.leaf 36)) (.node 3 (.leaf 37) (.leaf 38))) (.node 6 (.node 5 (.leaf 39) (.leaf 40)) (.node 7 (.leaf 41) (.leaf 42)))) (.node 12 (.node 10 (.node 9 (.leaf 43) (.leaf 44)) (.node 11 (.leaf 45) (.leaf 46))) (.node 14 (.node 13 (.leaf 47) (.leaf 48)) (.node 15 (.leaf 49) (.node 16 (.leaf 50) (.leaf 51)))))) (.node 26 (.node 21 (.node 19 (.node 18 (.leaf 52) (.leaf 53)) (.node 20 (.leaf 54) (.leaf 55))) (.node 23 (.node 22 (.leaf 56) (.leaf 57)) (.node 24 (.leaf 58) (.node 25 (.leaf 59) (.leaf 60))))) (.node 30 (.node 28 (.node 27 (.leaf 61) (.leaf 62)) (.node 29 (.leaf 63) (.leaf 64))) (.node 32 (.node 31 (.leaf 65) (.leaf 66)) (.node 33 (.leaf 67) (.node 34 (.leaf 68) (.leaf 69)))))))
noncomputable def newIndex (i : Fin 35) : Fin 70 := Fin.ofNat 70 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 11 (.node 5 (.node 2 (.node 1 (.leaf (3447717888,23,4076597)) (.leaf (3428843520,23,4075701))) (.node 3 (.leaf (3252682752,23,4064949)) (.node 4 (.leaf (232783872,23,3950261)) (.leaf (3454009344,27,10330677))))) (.node 8 (.node 6 (.leaf (30903631872,30,6248648)) (.node 7 (.leaf (34351349760,41,14599816)) (.leaf (34332475392,41,14599368)))) (.node 9 (.leaf (34156314624,41,14592200)) (.node 10 (.leaf (31136415744,41,14506184)) (.leaf (34357641216,46,14599816)))))) (.node 17 (.node 14 (.node 12 (.leaf (227820,141,7072520)) (.node 13 (.leaf (3447945708,142,16359980)) (.leaf (3429071340,142,16359532)))) (.node 15 (.leaf (3252910572,142,16352364)) (.node 16 (.leaf (233011692,142,16266348)) (.leaf (3454237164,143,16359980))))) (.node 20 (.node 18 (.leaf (30903859692,144,16434824)) (.node 19 (.leaf (34351577580,145,16434824)) (.leaf (34332703212,145,16434376)))) (.node 21 (.leaf (34156542444,145,16427208)) (.node 22 (.leaf (31136643564,145,16341192)) (.leaf (34357869036,146,16434824)))))))

noncomputable def models (i : Fin 23) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 23) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 23) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 70, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (7 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 70, (7 : Fin 8) ∈ U i → ∃ j : Fin 35, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C14

/- Source: MatroidCatalogue/Cases/N8R4C14Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C14


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
   ((.exchange 17 41 6),[(.neg 41),(.neg 17),(.pos 0),(.pos 3),(.pos 37)]),
   ((.exchange 17 47 6),[(.neg 47),(.neg 17),(.pos 0),(.pos 7),(.pos 37)]),
   ((.exchange 17 57 3),[(.neg 57),(.neg 17),(.pos 15),(.pos 56)]),
   ((.exchange 17 59 2),[(.neg 59),(.neg 17),(.pos 16),(.pos 58)]),
   ((.exchange 17 67 0),[(.neg 67),(.neg 17),(.pos 30),(.pos 60)]),
   ((.exchange 17 68 0),[(.neg 68),(.neg 17),(.pos 30),(.pos 60)]),
   ((.exchange 17 69 0),[(.neg 69),(.neg 17),(.pos 24),(.pos 30),(.pos 60)]),
   ((.exchange 18 41 6),[(.neg 41),(.neg 18),(.pos 4),(.pos 38)]),
   ((.exchange 18 47 6),[(.neg 47),(.neg 18),(.pos 8),(.pos 38)]),
   ((.exchange 18 56 3),[(.neg 56),(.neg 18),(.pos 15),(.pos 57)]),
   ((.exchange 18 58 2),[(.neg 58),(.neg 18),(.pos 16),(.pos 59)]),
   ((.exchange 20 41 6),[(.neg 41),(.neg 20),(.pos 1),(.pos 40)]),
   ((.exchange 20 47 6),[(.neg 47),(.neg 20),(.pos 1),(.pos 10),(.pos 40)]),
   ((.exchange 20 62 2),[(.neg 62),(.neg 20),(.pos 19),(.pos 61)]),
   ((.exchange 20 67 0),[(.neg 67),(.neg 20),(.pos 33),(.pos 63)]),
   ((.exchange 20 68 0),[(.neg 68),(.neg 20),(.pos 24),(.pos 33),(.pos 63)]),
   ((.exchange 20 69 0),[(.neg 69),(.neg 20),(.pos 33),(.pos 63)]),
   ((.exchange 21 37 6),[(.neg 37),(.neg 21),(.pos 1),(.pos 4),(.pos 41)]),
   ((.exchange 21 38 6),[(.neg 38),(.neg 21),(.pos 4),(.pos 41)]),
   ((.exchange 21 40 6),[(.neg 40),(.neg 21),(.pos 1),(.pos 41)]),
   ((.exchange 21 42 6),[(.neg 42),(.neg 21),(.pos 1),(.pos 4),(.pos 41)]),
   ((.exchange 21 43 6),[(.neg 43),(.neg 21),(.pos 4),(.pos 41)]),
   ((.exchange 21 46 6),[(.neg 46),(.neg 21),(.pos 1),(.pos 11),(.pos 41)]),
   ((.exchange 21 47 6),[(.neg 47),(.neg 21),(.pos 11),(.pos 41)]),
   ((.exchange 21 48 6),[(.neg 48),(.neg 21),(.pos 1),(.pos 4),(.pos 11),(.pos 41)]),
   ((.exchange 21 49 6),[(.neg 49),(.neg 21),(.pos 4),(.pos 11),(.pos 41)]),
   ((.exchange 21 51 6),[(.neg 51),(.neg 21),(.pos 1),(.pos 11),(.pos 41)]),
   ((.exchange 21 52 6),[(.neg 52),(.neg 21),(.pos 11),(.pos 41)]),
   ((.exchange 21 61 2),[(.neg 61),(.neg 21),(.pos 19),(.pos 62)]),
   ((.exchange 22 41 6),[(.neg 41),(.neg 22),(.pos 2),(.pos 3),(.pos 42)]),
   ((.exchange 22 47 6),[(.neg 47),(.neg 22),(.pos 2),(.pos 3),(.pos 12),(.pos 42)]),
   ((.exchange 22 67 0),[(.neg 67),(.neg 22),(.pos 24),(.pos 34),(.pos 64)]),
   ((.exchange 22 68 0),[(.neg 68),(.neg 22),(.pos 34),(.pos 64)]),
   ((.exchange 22 69 0),[(.neg 69),(.neg 22),(.pos 34),(.pos 64)]),
   ((.exchange 23 41 6),[(.neg 41),(.neg 23),(.pos 4),(.pos 43)]),
   ((.exchange 23 47 6),[(.neg 47),(.neg 23),(.pos 4),(.pos 13),(.pos 43)]),
   ((.exchange 26 41 6),[(.neg 41),(.neg 26),(.pos 5),(.pos 10),(.pos 46)]),
   ((.exchange 26 47 6),[(.neg 47),(.neg 26),(.pos 5),(.pos 46)]),
   ((.exchange 26 60 0),[(.neg 60),(.neg 26),(.pos 30),(.pos 67)]),
   ((.exchange 26 63 0),[(.neg 63),(.neg 26),(.pos 33),(.pos 67)]),
   ((.exchange 26 64 0),[(.neg 64),(.neg 26),(.pos 30),(.pos 33),(.pos 67)]),
   ((.exchange 26 66 2),[(.neg 66),(.neg 26),(.pos 25),(.pos 65)]),
   ((.exchange 26 68 0),[(.neg 68),(.neg 26),(.pos 30),(.pos 67)]),
   ((.exchange 26 69 0),[(.neg 69),(.neg 26),(.pos 33),(.pos 67)]),
   ((.exchange 27 37 6),[(.neg 37),(.neg 27),(.pos 5),(.pos 8),(.pos 47)]),
   ((.exchange 27 38 6),[(.neg 38),(.neg 27),(.pos 8),(.pos 47)]),
   ((.exchange 27 40 6),[(.neg 40),(.neg 27),(.pos 5),(.pos 11),(.pos 47)]),
   ((.exchange 27 41 6),[(.neg 41),(.neg 27),(.pos 11),(.pos 47)]),
   ((.exchange 27 42 6),[(.neg 42),(.neg 27),(.pos 5),(.pos 8),(.pos 11),(.pos 47)]),
   ((.exchange 27 43 6),[(.neg 43),(.neg 27),(.pos 8),(.pos 11),(.pos 47)]),
   ((.exchange 27 46 6),[(.neg 46),(.neg 27),(.pos 5),(.pos 47)]),
   ((.exchange 27 48 6),[(.neg 48),(.neg 27),(.pos 5),(.pos 8),(.pos 47)]),
   ((.exchange 27 49 6),[(.neg 49),(.neg 27),(.pos 8),(.pos 47)]),
   ((.exchange 27 51 6),[(.neg 51),(.neg 27),(.pos 5),(.pos 11),(.pos 47)]),
   ((.exchange 27 52 6),[(.neg 52),(.neg 27),(.pos 11),(.pos 47)]),
   ((.exchange 27 65 2),[(.neg 65),(.neg 27),(.pos 25),(.pos 66)]),
   ((.exchange 28 41 6),[(.neg 41),(.neg 28),(.pos 6),(.pos 7),(.pos 12),(.pos 48)]),
   ((.exchange 28 47 6),[(.neg 47),(.neg 28),(.pos 6),(.pos 7),(.pos 48)]),
   ((.exchange 28 60 0),[(.neg 60),(.neg 28),(.pos 30),(.pos 68)]),
   ((.exchange 28 63 0),[(.neg 63),(.neg 28),(.pos 30),(.pos 34),(.pos 68)]),
   ((.exchange 28 64 0),[(.neg 64),(.neg 28),(.pos 34),(.pos 68)]),
   ((.exchange 28 67 0),[(.neg 67),(.neg 28),(.pos 30),(.pos 68)]),
   ((.exchange 28 69 0),[(.neg 69),(.neg 28),(.pos 34),(.pos 68)]),
   ((.exchange 29 41 6),[(.neg 41),(.neg 29),(.pos 8),(.pos 13),(.pos 49)]),
   ((.exchange 29 47 6),[(.neg 47),(.neg 29),(.pos 8),(.pos 49)]),
   ((.exchange 31 41 6),[(.neg 41),(.neg 31),(.pos 9),(.pos 10),(.pos 51)]),
   ((.exchange 31 47 6),[(.neg 47),(.neg 31),(.pos 9),(.pos 10),(.pos 51)]),
   ((.exchange 31 60 0),[(.neg 60),(.neg 31),(.pos 33),(.pos 34),(.pos 69)]),
   ((.exchange 31 63 0),[(.neg 63),(.neg 31),(.pos 33),(.pos 69)]),
   ((.exchange 31 64 0),[(.neg 64),(.neg 31),(.pos 34),(.pos 69)]),
   ((.exchange 31 67 0),[(.neg 67),(.neg 31),(.pos 33),(.pos 69)]),
   ((.exchange 31 68 0),[(.neg 68),(.neg 31),(.pos 34),(.pos 69)]),
   ((.exchange 32 41 6),[(.neg 41),(.neg 32),(.pos 11),(.pos 52)]),
   ((.exchange 32 47 6),[(.neg 47),(.neg 32),(.pos 11),(.pos 52)]),
   ((.exchange 35 17 7),[(.neg 35),(.neg 17),(.pos 0),(.pos 15)]),
   ((.exchange 36 17 7),[(.neg 36),(.neg 17),(.pos 0),(.pos 16)]),
   ((.exchange 39 17 7),[(.neg 39),(.neg 17),(.pos 1),(.pos 2),(.pos 19)]),
   ((.exchange 44 17 7),[(.neg 44),(.neg 17),(.pos 3),(.pos 24)]),
   ((.exchange 45 17 7),[(.neg 45),(.neg 17),(.pos 5),(.pos 6),(.pos 25)]),
   ((.exchange 50 17 7),[(.neg 50),(.neg 17),(.pos 7),(.pos 30)]),
   ((.exchange 53 17 7),[(.neg 53),(.neg 17),(.pos 10),(.pos 14),(.pos 33)]),
   ((.exchange 54 17 7),[(.neg 54),(.neg 17),(.pos 12),(.pos 14),(.pos 34)]),
   ((.exchange 55 17 7),[(.neg 55),(.neg 17),(.pos 15),(.pos 16)]),
   ((.exchange 56 22 2),[(.neg 56),(.neg 22),(.pos 58),(.pos 61)]),
   ((.exchange 56 28 2),[(.neg 56),(.neg 28),(.pos 58),(.pos 65)]),
   ((.exchange 56 31 2),[(.neg 56),(.neg 31),(.pos 61),(.pos 65)]),
   ((.exchange 57 22 2),[(.neg 57),(.neg 22),(.pos 55),(.pos 59),(.pos 62)]),
   ((.exchange 57 28 2),[(.neg 57),(.neg 28),(.pos 55),(.pos 59),(.pos 66)]),
   ((.exchange 57 31 2),[(.neg 57),(.neg 31),(.pos 55),(.pos 62),(.pos 66)]),
   ((.exchange 57 69 2),[(.neg 69),(.neg 57),(.pos 62),(.pos 66)]),
   ((.exchange 58 20 3),[(.neg 58),(.neg 20),(.pos 56),(.pos 61)]),
   ((.exchange 58 26 3),[(.neg 58),(.neg 26),(.pos 56),(.pos 65)]),
   ((.exchange 58 69 3),[(.neg 69),(.neg 58),(.pos 61),(.pos 65)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_1 : List (Origin 70 23 × List Sat.Literal) :=
  [((.exchange 59 20 3),[(.neg 59),(.neg 20),(.pos 55),(.pos 57),(.pos 62)]),
   ((.exchange 59 26 3),[(.neg 59),(.neg 26),(.pos 55),(.pos 57),(.pos 66)]),
   ((.exchange 61 17 4),[(.neg 61),(.neg 17),(.pos 56),(.pos 58)]),
   ((.exchange 62 17 4),[(.neg 62),(.neg 17),(.pos 55),(.pos 57),(.pos 59)]),
   ((.exchange 65 22 5),[(.neg 65),(.neg 22),(.pos 58),(.pos 61)]),
   ((.exchange 66 22 5),[(.neg 66),(.neg 22),(.pos 55),(.pos 59),(.pos 62)]),
   (.newPoint,[(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 0),[(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 64),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 1),[(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 58),(.pos 59),(.pos 60),(.pos 63),(.pos 64),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 2),[(.neg 66),(.neg 65),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 3),[(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 4),[(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 63),(.pos 64),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 5),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 60),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 61),(.pos 62),(.pos 65),(.pos 66)]),
   ((.excluded 6),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 7),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 58),(.pos 59)]),
   ((.excluded 8),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 9),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 65),(.pos 66)]),
   ((.excluded 10),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55)]),
   ((.excluded 11),[(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 12),[(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 64),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 13),[(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 57),(.neg 56),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 58),(.pos 59),(.pos 60),(.pos 63),(.pos 64),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 14),[(.neg 66),(.neg 65),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 15),[(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 16),[(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 63),(.pos 64),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 17),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 60),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 61),(.pos 62),(.pos 65),(.pos 66)]),
   ((.excluded 18),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 19),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 58),(.pos 59)]),
   ((.excluded 20),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 21),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 65),(.pos 66)]),
   ((.excluded 22),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 53),(.pos 54),(.pos 55)])]

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
        Papers.RationalityTen.MatroidChecked.FastSemanticChecks.RawWitness 8 (N7R4.familyMasks.get 14)
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


end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C14

/- Source: MatroidCatalogue/Cases/N8R4C14Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C14

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
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C14.formula []
    exact Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C14.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 8 4 (target w),family_mem 8 4 (target w) hw.1,?_⟩
    exact validWitness_sound 8 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C14


end
end
end BundlePart0

section BundlePart1
/- Source: MatroidChecked/SemanticChunks/Cases03Part01.lean -/




@[expose] public section
noncomputable section

/- Source: MatroidCatalogue/Cases/N8R4C15Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C15

abbrev U := N8R4.grid
noncomputable def old : Finset (Finset (Fin 8)) := N7R4.family 15
noncomputable def newIndexTree : Table ℕ := (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf 35) (.leaf 36)) (.node 3 (.leaf 37) (.leaf 38))) (.node 6 (.node 5 (.leaf 39) (.leaf 40)) (.node 7 (.leaf 41) (.leaf 42)))) (.node 12 (.node 10 (.node 9 (.leaf 43) (.leaf 44)) (.node 11 (.leaf 45) (.leaf 46))) (.node 14 (.node 13 (.leaf 47) (.leaf 48)) (.node 15 (.leaf 49) (.node 16 (.leaf 50) (.leaf 51)))))) (.node 26 (.node 21 (.node 19 (.node 18 (.leaf 52) (.leaf 53)) (.node 20 (.leaf 54) (.leaf 55))) (.node 23 (.node 22 (.leaf 56) (.leaf 57)) (.node 24 (.leaf 58) (.node 25 (.leaf 59) (.leaf 60))))) (.node 30 (.node 28 (.node 27 (.leaf 61) (.leaf 62)) (.node 29 (.leaf 63) (.leaf 64))) (.node 32 (.node 31 (.leaf 65) (.leaf 66)) (.node 33 (.leaf 67) (.node 34 (.leaf 68) (.leaf 69)))))))
noncomputable def newIndex (i : Fin 35) : Fin 70 := Fin.ofNat 70 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 21 (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (15971909632,24,4151504)) (.leaf (32010928128,25,4151490))) (.node 3 (.leaf (29729226752,25,4151322)) (.node 4 (.leaf (25165824000,25,4149530)) (.leaf (34292629504,28,10442376))))) (.node 7 (.node 6 (.leaf (15098445824,41,4131610)) (.leaf (1005584384,41,3959578))) (.node 8 (.leaf (16037969920,47,12467336)) (.node 9 (.leaf (29929504768,48,12478088)) (.leaf (25634537472,48,12477640)))))) (.node 15 (.node 12 (.node 11 (.leaf (34224472064,49,12535432)) (.leaf (29526851584,48,12534872))) (.node 13 (.leaf (30063722496,49,12478032)) (.node 14 (.leaf (31674335232,48,12534984)) (.leaf (33821818880,49,12534480))))) (.node 18 (.node 16 (.leaf (31942770688,48,12535432)) (.node 17 (.leaf (32211206144,49,12478088)) (.leaf (25500319744,48,12477528)))) (.node 19 (.leaf (34090254336,49,12535376)) (.node 20 (.leaf (25768755200,49,12477136)) (.leaf (34358689792,50,14599816))))))) (.node 32 (.node 26 (.node 23 (.node 22 (.leaf (983024,142,11789960)) (.leaf (15972892656,147,16434824))) (.node 24 (.leaf (32011911152,148,11789960)) (.node 25 (.leaf (29730209776,148,11789904)) (.leaf (25166807024,148,11789008))))) (.node 29 (.node 27 (.leaf (34293612528,149,16434824)) (.node 28 (.leaf (15099428848,150,16434824)) (.leaf (1006567408,150,16406152)))) (.node 30 (.leaf (16038952944,151,16434824)) (.node 31 (.leaf (29930487792,152,16434824)) (.leaf (25635520496,152,16434376)))))) (.node 37 (.node 34 (.node 33 (.leaf (34225455088,153,16434824)) (.leaf (29527834608,152,16405592))) (.node 35 (.leaf (30064705520,153,16406096)) (.node 36 (.leaf (31675318256,152,16405704)) (.leaf (33822801904,153,16433872))))) (.node 40 (.node 38 (.leaf (31943753712,152,16406152)) (.node 39 (.leaf (32212189168,153,16406152)) (.leaf (25501302768,152,16434264)))) (.node 41 (.leaf (34091237360,153,16434768)) (.node 42 (.leaf (25769738224,153,16405200)) (.leaf (34359672816,154,16434824))))))))

noncomputable def models (i : Fin 43) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 43) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 43) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 70, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (7 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 70, (7 : Fin 8) ∈ U i → ∃ j : Fin 35, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C15

/- Source: MatroidCatalogue/Cases/N8R4C15Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C15


noncomputable def certificates_0 : List (Origin 70 43 × List Sat.Literal) :=
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
   ((.fixed 31),[(.neg 31)]),
   ((.fixed 32),[(.pos 32)]),
   ((.fixed 33),[(.pos 33)]),
   ((.fixed 34),[(.pos 34)]),
   ((.exchange 19 41 6),[(.neg 41),(.neg 19),(.pos 1),(.pos 39)]),
   ((.exchange 19 56 4),[(.neg 56),(.neg 19),(.pos 15),(.pos 55)]),
   ((.exchange 19 57 4),[(.neg 57),(.neg 19),(.pos 15),(.pos 55)]),
   ((.exchange 19 58 4),[(.neg 58),(.neg 19),(.pos 16),(.pos 55)]),
   ((.exchange 19 59 4),[(.neg 59),(.neg 19),(.pos 16),(.pos 55)]),
   ((.exchange 19 60 4),[(.neg 60),(.neg 19),(.pos 15),(.pos 16),(.pos 55)]),
   ((.exchange 19 65 1),[(.neg 65),(.neg 19),(.pos 31),(.pos 61)]),
   ((.exchange 19 69 1),[(.neg 69),(.neg 19),(.pos 31),(.pos 61)]),
   ((.exchange 20 41 6),[(.neg 41),(.neg 20),(.pos 1),(.pos 40)]),
   ((.exchange 20 55 4),[(.neg 55),(.neg 20),(.pos 15),(.pos 56)]),
   ((.exchange 20 57 4),[(.neg 57),(.neg 20),(.pos 15),(.pos 56)]),
   ((.exchange 20 58 4),[(.neg 58),(.neg 20),(.pos 17),(.pos 56)]),
   ((.exchange 20 59 4),[(.neg 59),(.neg 20),(.pos 15),(.pos 17),(.pos 56)]),
   ((.exchange 20 60 4),[(.neg 60),(.neg 20),(.pos 17),(.pos 56)]),
   ((.exchange 21 39 6),[(.neg 39),(.neg 21),(.pos 1),(.pos 41)]),
   ((.exchange 21 40 6),[(.neg 40),(.neg 21),(.pos 1),(.pos 41)]),
   ((.exchange 21 42 6),[(.neg 42),(.neg 21),(.pos 1),(.pos 4),(.pos 41)]),
   ((.exchange 21 43 6),[(.neg 43),(.neg 21),(.pos 4),(.pos 41)]),
   ((.exchange 21 44 6),[(.neg 44),(.neg 21),(.pos 4),(.pos 41)]),
   ((.exchange 21 45 6),[(.neg 45),(.neg 21),(.pos 1),(.pos 11),(.pos 41)]),
   ((.exchange 21 46 6),[(.neg 46),(.neg 21),(.pos 1),(.pos 11),(.pos 41)]),
   ((.exchange 21 47 6),[(.neg 47),(.neg 21),(.pos 11),(.pos 41)]),
   ((.exchange 21 48 6),[(.neg 48),(.neg 21),(.pos 1),(.pos 4),(.pos 11),(.pos 41)]),
   ((.exchange 21 49 6),[(.neg 49),(.neg 21),(.pos 4),(.pos 11),(.pos 41)]),
   ((.exchange 21 50 6),[(.neg 50),(.neg 21),(.pos 4),(.pos 11),(.pos 41)]),
   ((.exchange 21 52 6),[(.neg 52),(.neg 21),(.pos 11),(.pos 41)]),
   ((.exchange 21 53 6),[(.neg 53),(.neg 21),(.pos 11),(.pos 41)]),
   ((.exchange 21 54 6),[(.neg 54),(.neg 21),(.pos 4),(.pos 11),(.pos 41)]),
   ((.exchange 21 55 4),[(.neg 55),(.neg 21),(.pos 15),(.pos 57)]),
   ((.exchange 21 56 4),[(.neg 56),(.neg 21),(.pos 15),(.pos 57)]),
   ((.exchange 22 41 6),[(.neg 41),(.neg 22),(.pos 2),(.pos 3),(.pos 42)]),
   ((.exchange 22 55 4),[(.neg 55),(.neg 22),(.pos 16),(.pos 58)]),
   ((.exchange 22 56 4),[(.neg 56),(.neg 22),(.pos 17),(.pos 58)]),
   ((.exchange 23 41 6),[(.neg 41),(.neg 23),(.pos 4),(.pos 43)]),
   ((.exchange 23 55 4),[(.neg 55),(.neg 23),(.pos 16),(.pos 59)]),
   ((.exchange 23 56 4),[(.neg 56),(.neg 23),(.pos 16),(.pos 18),(.pos 59)]),
   ((.exchange 24 41 6),[(.neg 41),(.neg 24),(.pos 4),(.pos 44)]),
   ((.exchange 24 55 4),[(.neg 55),(.neg 24),(.pos 17),(.pos 18),(.pos 60)]),
   ((.exchange 24 56 4),[(.neg 56),(.neg 24),(.pos 17),(.pos 60)]),
   ((.exchange 25 41 6),[(.neg 41),(.neg 25),(.pos 5),(.pos 9),(.pos 45)]),
   ((.exchange 25 61 1),[(.neg 61),(.neg 25),(.pos 31),(.pos 65)]),
   ((.exchange 25 69 1),[(.neg 69),(.neg 25),(.pos 31),(.pos 65)]),
   ((.exchange 26 41 6),[(.neg 41),(.neg 26),(.pos 5),(.pos 10),(.pos 46)]),
   ((.exchange 27 41 6),[(.neg 41),(.neg 27),(.pos 11),(.pos 47)]),
   ((.exchange 28 41 6),[(.neg 41),(.neg 28),(.pos 6),(.pos 7),(.pos 12),(.pos 48)]),
   ((.exchange 29 41 6),[(.neg 41),(.neg 29),(.pos 8),(.pos 13),(.pos 49)]),
   ((.exchange 30 41 6),[(.neg 41),(.neg 30),(.pos 8),(.pos 14),(.pos 50)]),
   ((.exchange 32 41 6),[(.neg 41),(.neg 32),(.pos 11),(.pos 52)]),
   ((.exchange 32 61 1),[(.neg 61),(.neg 32),(.pos 31),(.pos 69)]),
   ((.exchange 32 65 1),[(.neg 65),(.neg 32),(.pos 31),(.pos 69)]),
   ((.exchange 33 41 6),[(.neg 41),(.neg 33),(.pos 11),(.pos 53)]),
   ((.exchange 34 41 6),[(.neg 41),(.neg 34),(.pos 13),(.pos 14),(.pos 54)]),
   ((.exchange 35 19 7),[(.neg 35),(.neg 19),(.pos 1),(.pos 15)]),
   ((.exchange 36 19 7),[(.neg 36),(.neg 19),(.pos 2),(.pos 16)]),
   ((.exchange 37 19 7),[(.neg 37),(.neg 19),(.pos 0),(.pos 3),(.pos 17)]),
   ((.exchange 38 19 7),[(.neg 38),(.neg 19),(.pos 0),(.pos 4),(.pos 18)]),
   ((.exchange 51 19 7),[(.neg 51),(.neg 19),(.pos 9),(.pos 31)]),
   ((.exchange 58 34 0),[(.neg 58),(.neg 34),(.pos 64),(.pos 68)]),
   ((.exchange 59 69 3),[(.neg 69),(.neg 59),(.pos 62),(.pos 66)]),
   ((.exchange 60 33 3),[(.neg 60),(.neg 33),(.pos 63),(.pos 67)]),
   ((.exchange 60 69 2),[(.neg 69),(.neg 60),(.pos 64),(.pos 68)]),
   ((.exchange 61 23 0),[(.neg 61),(.neg 23),(.pos 62),(.pos 64)]),
   ((.exchange 61 34 0),[(.neg 61),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 62 25 4),[(.neg 62),(.neg 25),(.pos 55),(.pos 66)]),
   ((.exchange 62 28 4),[(.neg 62),(.neg 28),(.pos 55),(.pos 59),(.pos 66)]),
   ((.exchange 62 33 1),[(.neg 62),(.neg 33),(.pos 63),(.pos 69)]),
   ((.exchange 62 34 1),[(.neg 62),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 62 40 1),[(.neg 62),(.neg 40),(.pos 61),(.pos 63)]),
   ((.exchange 62 53 1),[(.neg 62),(.neg 53),(.pos 63),(.pos 69)]),
   ((.exchange 62 67 1),[(.neg 67),(.neg 62),(.pos 63),(.pos 69)]),
   ((.exchange 63 19 2),[(.neg 63),(.neg 19),(.pos 61),(.pos 62)]),
   ((.exchange 63 22 2),[(.neg 63),(.neg 22),(.pos 61),(.pos 64)]),
   ((.exchange 63 25 4),[(.neg 63),(.neg 25),(.pos 56),(.pos 57),(.pos 67)]),
   ((.exchange 63 30 4),[(.neg 63),(.neg 30),(.pos 60),(.pos 67)]),
   ((.exchange 63 32 2),[(.neg 63),(.neg 32),(.pos 62),(.pos 69)]),
   ((.exchange 63 34 2),[(.neg 63),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 63 43 2),[(.neg 63),(.neg 43),(.pos 62),(.pos 64)]),
   ((.exchange 63 52 2),[(.neg 63),(.neg 52),(.pos 62),(.pos 69)]),
   ((.exchange 63 54 2),[(.neg 63),(.neg 54),(.pos 64),(.pos 69)]),
   ((.exchange 64 19 3),[(.neg 64),(.neg 19),(.pos 61),(.pos 62)]),
   ((.exchange 64 20 3),[(.neg 64),(.neg 20),(.pos 61),(.pos 63)]),
   ((.exchange 64 21 3),[(.neg 64),(.neg 21),(.pos 62),(.pos 63)]),
   ((.exchange 64 25 3),[(.neg 64),(.neg 25),(.pos 61),(.pos 62),(.pos 69)]),
   ((.exchange 64 28 4),[(.neg 64),(.neg 28),(.pos 58),(.pos 68)]),
   ((.exchange 64 48 4),[(.neg 64),(.neg 48),(.pos 58),(.pos 68)]),
   ((.exchange 64 50 4),[(.neg 64),(.neg 50),(.pos 60),(.pos 68)]),
   ((.exchange 64 67 3),[(.neg 67),(.neg 64),(.pos 63),(.pos 69)]),
   ((.exchange 65 24 0),[(.neg 65),(.neg 24),(.pos 67),(.pos 68),(.pos 69)]),
   ((.exchange 65 29 0),[(.neg 65),(.neg 29),(.pos 66),(.pos 68)]),
   ((.exchange 65 60 0),[(.neg 65),(.neg 60),(.pos 67),(.pos 68)]),
   ((.exchange 66 19 5),[(.neg 66),(.neg 19),(.pos 55),(.pos 62)]),
   ((.exchange 66 24 1),[(.neg 66),(.neg 24),(.pos 67),(.pos 68),(.pos 69)]),
   ((.exchange 66 33 1),[(.neg 66),(.neg 33),(.pos 67),(.pos 69)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_1 : List (Origin 70 43 × List Sat.Literal) :=
  [((.exchange 66 34 1),[(.neg 66),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 66 43 5),[(.neg 66),(.neg 43),(.pos 59),(.pos 62)]),
   ((.exchange 67 19 2),[(.neg 67),(.neg 19),(.pos 65),(.pos 66),(.pos 69)]),
   ((.exchange 67 19 5),[(.neg 67),(.neg 19),(.pos 56),(.pos 57),(.pos 63)]),
   ((.exchange 67 22 2),[(.neg 67),(.neg 22),(.pos 65),(.pos 68),(.pos 69)]),
   ((.exchange 67 24 5),[(.neg 67),(.neg 24),(.pos 60),(.pos 63)]),
   ((.exchange 67 29 2),[(.neg 67),(.neg 29),(.pos 66),(.pos 68)]),
   ((.exchange 67 32 2),[(.neg 67),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 67 34 2),[(.neg 67),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 67 45 2),[(.neg 67),(.neg 45),(.pos 65),(.pos 66)]),
   ((.exchange 67 48 2),[(.neg 67),(.neg 48),(.pos 65),(.pos 68)]),
   ((.exchange 67 62 5),[(.neg 67),(.neg 62),(.pos 57),(.pos 63)]),
   ((.exchange 68 19 5),[(.neg 68),(.neg 19),(.pos 58),(.pos 59),(.pos 64)]),
   ((.exchange 68 25 3),[(.neg 68),(.neg 25),(.pos 65),(.pos 66)]),
   ((.exchange 68 26 3),[(.neg 68),(.neg 26),(.pos 65),(.pos 67)]),
   ((.exchange 68 27 3),[(.neg 68),(.neg 27),(.pos 66),(.pos 67)]),
   ((.exchange 68 33 3),[(.neg 68),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 68 44 5),[(.neg 68),(.neg 44),(.pos 60),(.pos 64)]),
   ((.exchange 68 47 3),[(.neg 68),(.neg 47),(.pos 66),(.pos 67)]),
   ((.exchange 68 52 3),[(.neg 68),(.neg 52),(.pos 66),(.pos 69)]),
   ((.exchange 68 53 3),[(.neg 68),(.neg 53),(.pos 67),(.pos 69)]),
   ((.exchange 68 56 3),[(.neg 68),(.neg 56),(.pos 65),(.pos 67)]),
   ((.exchange 68 61 5),[(.neg 68),(.neg 61),(.pos 58),(.pos 64)]),
   ((.exchange 68 63 3),[(.neg 68),(.neg 63),(.pos 67),(.pos 69)]),
   ((.exchange 69 21 5),[(.neg 69),(.neg 21),(.pos 62),(.pos 63)]),
   ((.exchange 69 24 5),[(.neg 69),(.neg 24),(.pos 63),(.pos 64)]),
   ((.exchange 69 30 4),[(.neg 69),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 69 49 4),[(.neg 69),(.neg 49),(.pos 66),(.pos 68)]),
   ((.exchange 69 50 4),[(.neg 69),(.neg 50),(.pos 67),(.pos 68)]),
   ((.exchange 69 60 5),[(.neg 69),(.neg 60),(.pos 63),(.pos 64)]),
   (.newPoint,[(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 0),[(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 65),(.pos 69)]),
   ((.excluded 1),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 62),(.pos 66)]),
   ((.excluded 2),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 3),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 68)]),
   ((.excluded 4),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60)]),
   ((.excluded 5),[(.neg 68),(.neg 67),(.neg 66),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 69)]),
   ((.excluded 6),[(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 61),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 7),[(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 61),(.pos 65),(.pos 69)]),
   ((.excluded 8),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 62),(.pos 67)]),
   ((.excluded 9),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 62),(.pos 68)]),
   ((.excluded 10),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 62)]),
   ((.excluded 11),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 64),(.pos 67)]),
   ((.excluded 12),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 67)]),
   ((.excluded 13),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 64),(.pos 66)]),
   ((.excluded 14),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 64)]),
   ((.excluded 15),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 63),(.pos 66)]),
   ((.excluded 16),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 66)]),
   ((.excluded 17),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 63),(.pos 68)]),
   ((.excluded 18),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 63)]),
   ((.excluded 19),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 68)]),
   ((.excluded 20),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54)]),
   ((.excluded 21),[(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 51),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 22),[(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 51),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 65),(.pos 69)]),
   ((.excluded 23),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 51),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 62),(.pos 66)]),
   ((.excluded 24),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 51),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 25),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 51),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 68)]),
   ((.excluded 26),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 51),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60)]),
   ((.excluded 27),[(.neg 68),(.neg 67),(.neg 66),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 51),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 69)]),
   ((.excluded 28),[(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 51),(.pos 61),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 29),[(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 51),(.pos 61),(.pos 65),(.pos 69)]),
   ((.excluded 30),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 51),(.pos 62),(.pos 67)]),
   ((.excluded 31),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 51),(.pos 62),(.pos 68)]),
   ((.excluded 32),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 51),(.pos 62)]),
   ((.excluded 33),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 51),(.pos 64),(.pos 67)]),
   ((.excluded 34),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 51),(.pos 67)]),
   ((.excluded 35),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 51),(.pos 64),(.pos 66)]),
   ((.excluded 36),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 51),(.pos 64)]),
   ((.excluded 37),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 51),(.pos 63),(.pos 66)]),
   ((.excluded 38),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 51),(.pos 66)]),
   ((.excluded 39),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 51),(.pos 63),(.pos 68)]),
   ((.excluded 40),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 51),(.pos 63)]),
   ((.excluded 41),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 51),(.pos 68)]),
   ((.excluded 42),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 51)])]

theorem certificates_1_valid : ∀ oc ∈ certificates_1,
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
        Papers.RationalityTen.MatroidChecked.FastSemanticChecks.RawWitness 8 (N7R4.familyMasks.get 15)
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


end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C15

/- Source: MatroidCatalogue/Cases/N8R4C15Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C15

noncomputable def certificates : List (Origin 70 43 × List Sat.Literal) :=
  certificates_0 ++ certificates_1

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  intro oc hoc
  simp only [certificates,List.mem_append,or_assoc] at hoc
  rcases hoc with h0 | h1
  · exact certificates_0_valid oc h0
  · exact certificates_1_valid oc h1

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
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C15.formula []
    exact Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C15.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 8 4 (target w),family_mem 8 4 (target w) hw.1,?_⟩
    exact validWitness_sound 8 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C15


end
end
end BundlePart1

section BundlePart2
/- Source: MatroidChecked/SemanticChunks/Cases03Part02.lean -/




@[expose] public section
noncomputable section

/- Source: MatroidCatalogue/Cases/N8R4C16Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C16

abbrev U := N8R4.grid
noncomputable def old : Finset (Finset (Fin 8)) := N7R4.family 16
noncomputable def newIndexTree : Table ℕ := (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf 35) (.leaf 36)) (.node 3 (.leaf 37) (.leaf 38))) (.node 6 (.node 5 (.leaf 39) (.leaf 40)) (.node 7 (.leaf 41) (.leaf 42)))) (.node 12 (.node 10 (.node 9 (.leaf 43) (.leaf 44)) (.node 11 (.leaf 45) (.leaf 46))) (.node 14 (.node 13 (.leaf 47) (.leaf 48)) (.node 15 (.leaf 49) (.node 16 (.leaf 50) (.leaf 51)))))) (.node 26 (.node 21 (.node 19 (.node 18 (.leaf 52) (.leaf 53)) (.node 20 (.leaf 54) (.leaf 55))) (.node 23 (.node 22 (.leaf 56) (.leaf 57)) (.node 24 (.leaf 58) (.node 25 (.leaf 59) (.leaf 60))))) (.node 30 (.node 28 (.node 27 (.leaf 61) (.leaf 62)) (.node 29 (.leaf 63) (.leaf 64))) (.node 32 (.node 31 (.leaf 65) (.leaf 66)) (.node 33 (.leaf 67) (.node 34 (.leaf 68) (.leaf 69)))))))
noncomputable def newIndex (i : Fin 35) : Fin 70 := Fin.ofNat 70 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 30 (.node 15 (.node 7 (.node 3 (.node 1 (.leaf (33151778816,26,4151504)) (.node 2 (.leaf (32010928128,26,4151490)) (.leaf (29729226752,26,4151322)))) (.node 5 (.node 4 (.leaf (25165824000,26,4149530)) (.leaf (17112760320,28,2054353))) (.node 6 (.leaf (34292629504,29,10442376)) (.leaf (16172187648,46,4131610))))) (.node 11 (.node 9 (.node 8 (.leaf (1072693248,46,3959578)) (.leaf (17178820608,51,14599816))) (.node 10 (.leaf (32144097280,49,10413704)) (.leaf (29996613632,49,10413648)))) (.node 13 (.node 12 (.leaf (25701646336,49,10412752)) (.leaf (34291580928,50,12535432))) (.node 14 (.leaf (31942770688,49,10442306)) (.leaf (31674335232,49,10441410)))))) (.node 22 (.node 18 (.node 16 (.leaf (32211206144,50,12478081)) (.node 17 (.leaf (33016512512,49,10442320)) (.leaf (25500319744,49,10412570)))) (.node 20 (.node 19 (.leaf (34090254336,50,12535313)) (.leaf (25634537472,49,10412738))) (.node 21 (.leaf (25768755200,50,12476625)) (.leaf (33150730240,49,10442376))))) (.node 26 (.node 24 (.node 23 (.leaf (29929504768,49,10413634)) (.leaf (34224472064,50,12535425))) (.node 25 (.leaf (32748077056,49,10441424)) (.leaf (33284947968,50,12478088)))) (.node 28 (.node 27 (.leaf (29526851584,49,10441242)) (.leaf (33821818880,50,12533969))) (.node 29 (.leaf (30063722496,50,12477969)) (.leaf (34358689792,52,14599816))))))) (.node 45 (.node 37 (.node 33 (.node 31 (.leaf (1048560,143,11789960)) (.node 32 (.leaf (17113808880,155,16434824)) (.leaf (33152827376,149,11789960)))) (.node 35 (.node 34 (.leaf (32011976688,149,11789953)) (.leaf (29730275312,149,11789841))) (.node 36 (.leaf (25166872560,149,11788497)) (.leaf (34293678064,156,16434824))))) (.node 41 (.node 39 (.node 38 (.leaf (16173236208,157,16434824)) (.leaf (1073741808,157,16406152))) (.node 40 (.leaf (17179869168,158,16434824)) (.leaf (32145145840,159,16434824)))) (.node 43 (.node 42 (.leaf (29997662192,159,16434768)) (.leaf (25702694896,159,16433872))) (.node 44 (.leaf (34292629488,160,16434824)) (.leaf (31943819248,159,16406082)))))) (.node 53 (.node 49 (.node 47 (.node 46 (.leaf (31675383792,159,16405186)) (.leaf (32212254704,160,16406145))) (.node 48 (.leaf (33017561072,159,16406096)) (.leaf (25501368304,159,16433690)))) (.node 51 (.node 50 (.leaf (34091302896,160,16434705)) (.leaf (25635586032,159,16433858))) (.node 52 (.leaf (25769803760,160,16404689)) (.leaf (33151778800,159,16406152))))) (.node 57 (.node 55 (.node 54 (.leaf (29930553328,159,16434754)) (.leaf (34225520624,160,16434817))) (.node 56 (.leaf (32749125616,159,16405200)) (.leaf (33285996528,160,16406152)))) (.node 59 (.node 58 (.leaf (29527900144,159,16405018)) (.leaf (33822867440,160,16433361))) (.node 60 (.leaf (30064771056,160,16406033)) (.leaf (34359738352,161,16434824))))))))

noncomputable def models (i : Fin 61) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 61) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 61) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 70, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (7 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 70, (7 : Fin 8) ∈ U i → ∃ j : Fin 35, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C16

/- Source: MatroidCatalogue/Cases/N8R4C16Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C16


noncomputable def certificates_0 : List (Origin 70 61 × List Sat.Literal) :=
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
   ((.exchange 19 41 6),[(.neg 41),(.neg 19),(.pos 1),(.pos 39)]),
   ((.exchange 19 56 4),[(.neg 56),(.neg 19),(.pos 15),(.pos 55)]),
   ((.exchange 19 57 4),[(.neg 57),(.neg 19),(.pos 15),(.pos 55)]),
   ((.exchange 19 58 4),[(.neg 58),(.neg 19),(.pos 16),(.pos 55)]),
   ((.exchange 19 59 4),[(.neg 59),(.neg 19),(.pos 16),(.pos 55)]),
   ((.exchange 19 60 4),[(.neg 60),(.neg 19),(.pos 15),(.pos 16),(.pos 55)]),
   ((.exchange 20 41 6),[(.neg 41),(.neg 20),(.pos 1),(.pos 40)]),
   ((.exchange 20 55 4),[(.neg 55),(.neg 20),(.pos 15),(.pos 56)]),
   ((.exchange 20 57 4),[(.neg 57),(.neg 20),(.pos 15),(.pos 56)]),
   ((.exchange 20 58 4),[(.neg 58),(.neg 20),(.pos 17),(.pos 56)]),
   ((.exchange 20 59 4),[(.neg 59),(.neg 20),(.pos 15),(.pos 17),(.pos 56)]),
   ((.exchange 20 60 4),[(.neg 60),(.neg 20),(.pos 17),(.pos 56)]),
   ((.exchange 21 39 6),[(.neg 39),(.neg 21),(.pos 1),(.pos 41)]),
   ((.exchange 21 40 6),[(.neg 40),(.neg 21),(.pos 1),(.pos 41)]),
   ((.exchange 21 42 6),[(.neg 42),(.neg 21),(.pos 1),(.pos 4),(.pos 41)]),
   ((.exchange 21 43 6),[(.neg 43),(.neg 21),(.pos 4),(.pos 41)]),
   ((.exchange 21 44 6),[(.neg 44),(.neg 21),(.pos 4),(.pos 41)]),
   ((.exchange 21 45 6),[(.neg 45),(.neg 21),(.pos 1),(.pos 11),(.pos 41)]),
   ((.exchange 21 46 6),[(.neg 46),(.neg 21),(.pos 1),(.pos 11),(.pos 41)]),
   ((.exchange 21 47 6),[(.neg 47),(.neg 21),(.pos 11),(.pos 41)]),
   ((.exchange 21 48 6),[(.neg 48),(.neg 21),(.pos 1),(.pos 4),(.pos 11),(.pos 41)]),
   ((.exchange 21 49 6),[(.neg 49),(.neg 21),(.pos 4),(.pos 11),(.pos 41)]),
   ((.exchange 21 50 6),[(.neg 50),(.neg 21),(.pos 4),(.pos 11),(.pos 41)]),
   ((.exchange 21 51 6),[(.neg 51),(.neg 21),(.pos 1),(.pos 11),(.pos 41)]),
   ((.exchange 21 52 6),[(.neg 52),(.neg 21),(.pos 11),(.pos 41)]),
   ((.exchange 21 53 6),[(.neg 53),(.neg 21),(.pos 11),(.pos 41)]),
   ((.exchange 21 54 6),[(.neg 54),(.neg 21),(.pos 4),(.pos 11),(.pos 41)]),
   ((.exchange 21 55 4),[(.neg 55),(.neg 21),(.pos 15),(.pos 57)]),
   ((.exchange 21 56 4),[(.neg 56),(.neg 21),(.pos 15),(.pos 57)]),
   ((.exchange 22 41 6),[(.neg 41),(.neg 22),(.pos 2),(.pos 3),(.pos 42)]),
   ((.exchange 22 55 4),[(.neg 55),(.neg 22),(.pos 16),(.pos 58)]),
   ((.exchange 22 56 4),[(.neg 56),(.neg 22),(.pos 17),(.pos 58)]),
   ((.exchange 23 41 6),[(.neg 41),(.neg 23),(.pos 4),(.pos 43)]),
   ((.exchange 23 55 4),[(.neg 55),(.neg 23),(.pos 16),(.pos 59)]),
   ((.exchange 23 56 4),[(.neg 56),(.neg 23),(.pos 16),(.pos 18),(.pos 59)]),
   ((.exchange 24 41 6),[(.neg 41),(.neg 24),(.pos 4),(.pos 44)]),
   ((.exchange 24 55 4),[(.neg 55),(.neg 24),(.pos 17),(.pos 18),(.pos 60)]),
   ((.exchange 24 56 4),[(.neg 56),(.neg 24),(.pos 17),(.pos 60)]),
   ((.exchange 25 41 6),[(.neg 41),(.neg 25),(.pos 5),(.pos 9),(.pos 45)]),
   ((.exchange 26 41 6),[(.neg 41),(.neg 26),(.pos 5),(.pos 10),(.pos 46)]),
   ((.exchange 27 41 6),[(.neg 41),(.neg 27),(.pos 11),(.pos 47)]),
   ((.exchange 28 41 6),[(.neg 41),(.neg 28),(.pos 6),(.pos 7),(.pos 12),(.pos 48)]),
   ((.exchange 29 41 6),[(.neg 41),(.neg 29),(.pos 8),(.pos 13),(.pos 49)]),
   ((.exchange 30 41 6),[(.neg 41),(.neg 30),(.pos 8),(.pos 14),(.pos 50)]),
   ((.exchange 31 41 6),[(.neg 41),(.neg 31),(.pos 9),(.pos 10),(.pos 51)]),
   ((.exchange 32 41 6),[(.neg 41),(.neg 32),(.pos 11),(.pos 52)]),
   ((.exchange 33 41 6),[(.neg 41),(.neg 33),(.pos 11),(.pos 53)]),
   ((.exchange 34 41 6),[(.neg 41),(.neg 34),(.pos 13),(.pos 14),(.pos 54)]),
   ((.exchange 35 19 7),[(.neg 35),(.neg 19),(.pos 1),(.pos 15)]),
   ((.exchange 36 19 7),[(.neg 36),(.neg 19),(.pos 2),(.pos 16)]),
   ((.exchange 37 19 7),[(.neg 37),(.neg 19),(.pos 0),(.pos 3),(.pos 17)]),
   ((.exchange 38 19 7),[(.neg 38),(.neg 19),(.pos 0),(.pos 4),(.pos 18)]),
   ((.exchange 55 31 1),[(.neg 55),(.neg 31),(.pos 61),(.pos 65)]),
   ((.exchange 55 32 0),[(.neg 55),(.neg 32),(.pos 62),(.pos 66)]),
   ((.exchange 56 33 0),[(.neg 56),(.neg 33),(.pos 63),(.pos 67)]),
   ((.exchange 58 34 0),[(.neg 58),(.neg 34),(.pos 64),(.pos 68)]),
   ((.exchange 59 52 3),[(.neg 59),(.neg 52),(.pos 62),(.pos 66)]),
   ((.exchange 60 33 3),[(.neg 60),(.neg 33),(.pos 63),(.pos 67)]),
   ((.exchange 60 54 2),[(.neg 60),(.neg 54),(.pos 64),(.pos 68)]),
   ((.exchange 61 21 0),[(.neg 61),(.neg 21),(.pos 62),(.pos 63)]),
   ((.exchange 61 23 0),[(.neg 61),(.neg 23),(.pos 62),(.pos 64)]),
   ((.exchange 61 24 0),[(.neg 61),(.neg 24),(.pos 63),(.pos 64)]),
   ((.exchange 61 32 0),[(.neg 61),(.neg 32),(.pos 62),(.pos 69)]),
   ((.exchange 61 33 0),[(.neg 61),(.neg 33),(.pos 63),(.pos 69)]),
   ((.exchange 61 43 0),[(.neg 61),(.neg 43),(.pos 62),(.pos 64)]),
   ((.exchange 61 48 4),[(.neg 61),(.neg 48),(.pos 58),(.pos 65)]),
   ((.exchange 61 52 0),[(.neg 61),(.neg 52),(.pos 62),(.pos 69)]),
   ((.exchange 61 59 0),[(.neg 61),(.neg 59),(.pos 62),(.pos 64)]),
   ((.exchange 61 67 0),[(.neg 67),(.neg 61),(.pos 63),(.pos 69)]),
   ((.exchange 61 67 4),[(.neg 67),(.neg 61),(.pos 56),(.pos 65)]),
   ((.exchange 62 28 4),[(.neg 62),(.neg 28),(.pos 55),(.pos 59),(.pos 66)]),
   ((.exchange 62 33 1),[(.neg 62),(.neg 33),(.pos 63),(.pos 69)]),
   ((.exchange 62 40 1),[(.neg 62),(.neg 40),(.pos 61),(.pos 63)]),
   ((.exchange 62 44 1),[(.neg 62),(.neg 44),(.pos 63),(.pos 64)]),
   ((.exchange 62 46 1),[(.neg 62),(.neg 46),(.pos 61),(.pos 63),(.pos 69)]),
   ((.exchange 62 65 4),[(.neg 65),(.neg 62),(.pos 55),(.pos 66)]),
   ((.exchange 62 67 1),[(.neg 67),(.neg 62),(.pos 63),(.pos 69)]),
   ((.exchange 63 19 2),[(.neg 63),(.neg 19),(.pos 61),(.pos 62)]),
   ((.exchange 63 23 2),[(.neg 63),(.neg 23),(.pos 62),(.pos 64)]),
   ((.exchange 63 25 4),[(.neg 63),(.neg 25),(.pos 56),(.pos 57),(.pos 67)]),
   ((.exchange 63 30 4),[(.neg 63),(.neg 30),(.pos 60),(.pos 67)]),
   ((.exchange 63 31 2),[(.neg 63),(.neg 31),(.pos 61),(.pos 69)]),
   ((.exchange 63 32 2),[(.neg 63),(.neg 32),(.pos 62),(.pos 69)]),
   ((.exchange 63 34 2),[(.neg 63),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 63 39 2),[(.neg 63),(.neg 39),(.pos 61),(.pos 62)]),
   ((.exchange 63 51 2),[(.neg 63),(.neg 51),(.pos 61),(.pos 69)]),
   ((.exchange 63 55 2),[(.neg 63),(.neg 55),(.pos 61),(.pos 62)]),
   ((.exchange 63 58 2),[(.neg 63),(.neg 58),(.pos 61),(.pos 64)]),
   ((.exchange 63 65 2),[(.neg 65),(.neg 63),(.pos 61),(.pos 69)]),
   ((.exchange 63 66 4),[(.neg 66),(.neg 63),(.pos 57),(.pos 67)]),
   ((.exchange 64 20 3),[(.neg 64),(.neg 20),(.pos 61),(.pos 63)]),
   ((.exchange 64 21 3),[(.neg 64),(.neg 21),(.pos 62),(.pos 63)]),
   ((.exchange 64 28 4),[(.neg 64),(.neg 28),(.pos 58),(.pos 68)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_1 : List (Origin 70 61 × List Sat.Literal) :=
  [((.exchange 64 31 3),[(.neg 64),(.neg 31),(.pos 61),(.pos 69)]),
   ((.exchange 64 33 3),[(.neg 64),(.neg 33),(.pos 63),(.pos 69)]),
   ((.exchange 64 65 4),[(.neg 65),(.neg 64),(.pos 58),(.pos 68)]),
   ((.exchange 64 67 3),[(.neg 67),(.neg 64),(.pos 63),(.pos 69)]),
   ((.exchange 64 67 4),[(.neg 67),(.neg 64),(.pos 60),(.pos 68)]),
   ((.exchange 65 19 5),[(.neg 65),(.neg 19),(.pos 55),(.pos 61)]),
   ((.exchange 65 24 0),[(.neg 65),(.neg 24),(.pos 67),(.pos 68),(.pos 69)]),
   ((.exchange 65 29 0),[(.neg 65),(.neg 29),(.pos 66),(.pos 68)]),
   ((.exchange 65 30 0),[(.neg 65),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 65 33 0),[(.neg 65),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 65 59 0),[(.neg 65),(.neg 59),(.pos 66),(.pos 68)]),
   ((.exchange 65 60 0),[(.neg 65),(.neg 60),(.pos 67),(.pos 68)]),
   ((.exchange 65 62 0),[(.neg 65),(.neg 62),(.pos 66),(.pos 69)]),
   ((.exchange 65 63 0),[(.neg 65),(.neg 63),(.pos 67),(.pos 69)]),
   ((.exchange 65 64 5),[(.neg 65),(.neg 64),(.pos 58),(.pos 61)]),
   ((.exchange 66 19 5),[(.neg 66),(.neg 19),(.pos 55),(.pos 62)]),
   ((.exchange 66 31 1),[(.neg 66),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 66 34 1),[(.neg 66),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 66 46 1),[(.neg 66),(.neg 46),(.pos 65),(.pos 67)]),
   ((.exchange 66 61 1),[(.neg 66),(.neg 61),(.pos 65),(.pos 69)]),
   ((.exchange 66 61 5),[(.neg 66),(.neg 61),(.pos 55),(.pos 62)]),
   ((.exchange 66 63 1),[(.neg 66),(.neg 63),(.pos 67),(.pos 69)]),
   ((.exchange 67 19 5),[(.neg 67),(.neg 19),(.pos 56),(.pos 57),(.pos 63)]),
   ((.exchange 67 25 2),[(.neg 67),(.neg 25),(.pos 65),(.pos 66)]),
   ((.exchange 67 31 2),[(.neg 67),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 67 32 2),[(.neg 67),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 67 34 2),[(.neg 67),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 67 39 2),[(.neg 67),(.neg 39),(.pos 65),(.pos 66),(.pos 69)]),
   ((.exchange 67 44 5),[(.neg 67),(.neg 44),(.pos 60),(.pos 63)]),
   ((.exchange 67 45 2),[(.neg 67),(.neg 45),(.pos 65),(.pos 66)]),
   ((.exchange 67 54 2),[(.neg 67),(.neg 54),(.pos 68),(.pos 69)]),
   ((.exchange 67 58 2),[(.neg 67),(.neg 58),(.pos 65),(.pos 68)]),
   ((.exchange 67 61 2),[(.neg 67),(.neg 61),(.pos 65),(.pos 69)]),
   ((.exchange 68 19 5),[(.neg 68),(.neg 19),(.pos 58),(.pos 59),(.pos 64)]),
   ((.exchange 68 25 3),[(.neg 68),(.neg 25),(.pos 65),(.pos 66)]),
   ((.exchange 68 26 3),[(.neg 68),(.neg 26),(.pos 65),(.pos 67)]),
   ((.exchange 68 27 3),[(.neg 68),(.neg 27),(.pos 66),(.pos 67)]),
   ((.exchange 68 33 3),[(.neg 68),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 68 47 3),[(.neg 68),(.neg 47),(.pos 66),(.pos 67)]),
   ((.exchange 68 51 3),[(.neg 68),(.neg 51),(.pos 65),(.pos 69)]),
   ((.exchange 68 56 3),[(.neg 68),(.neg 56),(.pos 65),(.pos 67)]),
   ((.exchange 68 62 3),[(.neg 68),(.neg 62),(.pos 66),(.pos 69)]),
   ((.exchange 68 63 3),[(.neg 68),(.neg 63),(.pos 67),(.pos 69)]),
   ((.exchange 68 63 5),[(.neg 68),(.neg 63),(.pos 60),(.pos 64)]),
   ((.exchange 69 20 5),[(.neg 69),(.neg 20),(.pos 61),(.pos 63)]),
   ((.exchange 69 21 5),[(.neg 69),(.neg 21),(.pos 62),(.pos 63)]),
   ((.exchange 69 22 5),[(.neg 69),(.neg 22),(.pos 61),(.pos 64)]),
   ((.exchange 69 25 4),[(.neg 69),(.neg 25),(.pos 65),(.pos 66)]),
   ((.exchange 69 26 4),[(.neg 69),(.neg 26),(.pos 65),(.pos 67)]),
   ((.exchange 69 27 4),[(.neg 69),(.neg 27),(.pos 66),(.pos 67)]),
   ((.exchange 69 28 4),[(.neg 69),(.neg 28),(.pos 65),(.pos 68)]),
   ((.exchange 69 29 4),[(.neg 69),(.neg 29),(.pos 66),(.pos 68)]),
   ((.exchange 69 30 4),[(.neg 69),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 69 39 5),[(.neg 69),(.neg 39),(.pos 61),(.pos 62)]),
   ((.exchange 69 41 5),[(.neg 69),(.neg 41),(.pos 62),(.pos 63)]),
   ((.exchange 69 42 5),[(.neg 69),(.neg 42),(.pos 61),(.pos 64)]),
   ((.exchange 69 48 4),[(.neg 69),(.neg 48),(.pos 65),(.pos 68)]),
   ((.exchange 69 49 4),[(.neg 69),(.neg 49),(.pos 66),(.pos 68)]),
   ((.exchange 69 55 5),[(.neg 69),(.neg 55),(.pos 61),(.pos 62)]),
   ((.exchange 69 56 5),[(.neg 69),(.neg 56),(.pos 61),(.pos 63)]),
   ((.exchange 69 57 5),[(.neg 69),(.neg 57),(.pos 62),(.pos 63)]),
   ((.exchange 69 58 4),[(.neg 69),(.neg 58),(.pos 65),(.pos 68)]),
   ((.exchange 69 60 5),[(.neg 69),(.neg 60),(.pos 63),(.pos 64)]),
   (.newPoint,[(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 0),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 65)]),
   ((.excluded 1),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 62),(.pos 66)]),
   ((.excluded 2),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 3),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 68)]),
   ((.excluded 4),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 69)]),
   ((.excluded 5),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60)]),
   ((.excluded 6),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 7),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 8),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 69)]),
   ((.excluded 9),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 61),(.pos 66)]),
   ((.excluded 10),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 61),(.pos 67)]),
   ((.excluded 11),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 61),(.pos 68)]),
   ((.excluded 12),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 61)]),
   ((.excluded 13),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 63),(.pos 66)]),
   ((.excluded 14),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 64),(.pos 66)]),
   ((.excluded 15),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 66)]),
   ((.excluded 16),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 63),(.pos 65)]),
   ((.excluded 17),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 63),(.pos 68)]),
   ((.excluded 18),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 63)]),
   ((.excluded 19),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 62),(.pos 68)]),
   ((.excluded 20),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 68)]),
   ((.excluded 21),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 62),(.pos 65)]),
   ((.excluded 22),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 62),(.pos 67)]),
   ((.excluded 23),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 62)]),
   ((.excluded 24),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 64),(.pos 65)]),
   ((.excluded 25),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 65)]),
   ((.excluded 26),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 64),(.pos 67)]),
   ((.excluded 27),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 64)]),
   ((.excluded 28),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 67)]),
   ((.excluded 29),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54)]),
   ((.excluded 30),[(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 31),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 69)]),
   ((.excluded 32),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 65)]),
   ((.excluded 33),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 62),(.pos 66)]),
   ((.excluded 34),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 35),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 68)]),
   ((.excluded 36),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60)]),
   ((.excluded 37),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 38),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 39),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 69)]),
   ((.excluded 40),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 61),(.pos 66)]),
   ((.excluded 41),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 61),(.pos 67)]),
   ((.excluded 42),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 61),(.pos 68)]),
   ((.excluded 43),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 61)]),
   ((.excluded 44),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 63),(.pos 66)]),
   ((.excluded 45),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 64),(.pos 66)]),
   ((.excluded 46),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 66)]),
   ((.excluded 47),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 63),(.pos 65)]),
   ((.excluded 48),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 63),(.pos 68)]),
   ((.excluded 49),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 63)]),
   ((.excluded 50),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 62),(.pos 68)]),
   ((.excluded 51),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 68)]),
   ((.excluded 52),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 62),(.pos 65)]),
   ((.excluded 53),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 62),(.pos 67)]),
   ((.excluded 54),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 62)]),
   ((.excluded 55),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 64),(.pos 65)]),
   ((.excluded 56),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 65)]),
   ((.excluded 57),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 64),(.pos 67)]),
   ((.excluded 58),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 64)]),
   ((.excluded 59),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 67)]),
   ((.excluded 60),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38)])]

theorem certificates_1_valid : ∀ oc ∈ certificates_1,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



theorem witness_0 : ∀ j : Fin 61,
    let w : Fin 61 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 61,
      let w : Fin 61 := ⟨0 + j.val,by omega⟩
      target w < MatroidCatalogue.count 8 4 ∧
        Papers.RationalityTen.MatroidChecked.FastSemanticChecks.RawWitness 8 (N7R4.familyMasks.get 16)
        (fun i : Fin 70 => N8R4.gridMasks.get i.val) newIndex (models w)
        (N8R4.familyMasks.get (target w)) (permutation w) := by
    refine (Fin.forall_fin_add (m := 30) (n := 31) _).2 ⟨?_, ?_⟩
    · refine (Fin.forall_fin_add (m := 15) (n := 15) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 7) (n := 8) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
          · decide +kernel
          · decide +kernel
        · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
          · decide +kernel
          · decide +kernel
      · refine (Fin.forall_fin_add (m := 7) (n := 8) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
          · decide +kernel
          · decide +kernel
        · refine (Fin.forall_fin_add (m := 4) (n := 4) _).2 ⟨?_, ?_⟩
          · decide +kernel
          · decide +kernel
    · refine (Fin.forall_fin_add (m := 15) (n := 16) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 7) (n := 8) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
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


end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C16

/- Source: MatroidCatalogue/Cases/N8R4C16Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C16

noncomputable def certificates : List (Origin 70 61 × List Sat.Literal) :=
  certificates_0 ++ certificates_1

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  intro oc hoc
  simp only [certificates,List.mem_append,or_assoc] at hoc
  rcases hoc with h0 | h1
  · exact certificates_0_valid oc h0
  · exact certificates_1_valid oc h1

theorem models_valid : ∀ w : Fin 61,
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 61) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 8) 4)
    (hold : M.bases.filter ((7 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 8 4, IsomorphicWithin 8 M.bases B := by
  apply extension_covered_of_certificate (n:=7) (r:=4) (by decide)
    catalogue old U newIndex models certificates
    N8R4.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C16.formula []
    exact Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C16.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 8 4 (target w),family_mem 8 4 (target w) hw.1,?_⟩
    exact validWitness_sound 8 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C16


end
end
end BundlePart2

section BundlePart3
/- Source: MatroidChecked/SemanticChunks/Cases03Part03.lean -/




@[expose] public section
noncomputable section

/- Source: MatroidCatalogue/Cases/N8R4C17Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C17

abbrev U := N8R4.grid
noncomputable def old : Finset (Finset (Fin 8)) := N7R4.family 17
noncomputable def newIndexTree : Table ℕ := (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf 35) (.leaf 36)) (.node 3 (.leaf 37) (.leaf 38))) (.node 6 (.node 5 (.leaf 39) (.leaf 40)) (.node 7 (.leaf 41) (.leaf 42)))) (.node 12 (.node 10 (.node 9 (.leaf 43) (.leaf 44)) (.node 11 (.leaf 45) (.leaf 46))) (.node 14 (.node 13 (.leaf 47) (.leaf 48)) (.node 15 (.leaf 49) (.node 16 (.leaf 50) (.leaf 51)))))) (.node 26 (.node 21 (.node 19 (.node 18 (.leaf 52) (.leaf 53)) (.node 20 (.leaf 54) (.leaf 55))) (.node 23 (.node 22 (.leaf 56) (.leaf 57)) (.node 24 (.leaf 58) (.node 25 (.leaf 59) (.leaf 60))))) (.node 30 (.node 28 (.node 27 (.leaf 61) (.leaf 62)) (.node 29 (.leaf 63) (.leaf 64))) (.node 32 (.node 31 (.leaf 65) (.leaf 66)) (.node 33 (.leaf 67) (.node 34 (.leaf 68) (.leaf 69)))))))
noncomputable def newIndex (i : Fin 35) : Fin 70 := Fin.ofNat 70 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 21 (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (29217521664,35,4151322)) (.leaf (24903680000,35,4149530))) (.node 3 (.leaf (16137584640,35,4131610)) (.node 4 (.leaf (30297554944,41,6248648)) (.leaf (33518780416,46,12535432))))) (.node 7 (.node 6 (.leaf (30903631872,31,6248648)) (.leaf (1071644672,36,8219400))) (.node 8 (.leaf (31136415744,44,8219400)) (.node 9 (.leaf (25761415168,42,8317064)) (.leaf (17171480576,42,8309896)))))) (.node 15 (.node 12 (.node 11 (.leaf (34351349760,43,8345736)) (.leaf (25566380032,42,8300936))) (.node 13 (.leaf (25767706624,53,12477640)) (.node 14 (.leaf (29861347328,42,8301832)) (.leaf (34156314624,43,8334088))))) (.node 18 (.node 16 (.leaf (30037508096,42,8316168)) (.node 17 (.leaf (17152606208,42,8308104)) (.leaf (34332475392,43,8344840)))) (.node 19 (.leaf (30062673920,53,12478088)) (.node 20 (.leaf (17177772032,53,12463304)) (.leaf (34357641216,54,14599816))))))) (.node 32 (.node 26 (.node 23 (.node 22 (.leaf (1047020,162,7072520)) (.leaf (29218568684,163,16434824))) (.node 24 (.leaf (24904727020,163,16434376)) (.node 25 (.leaf (16138631660,163,16427208)) (.leaf (30298601964,164,16434824))))) (.node 29 (.node 27 (.leaf (33519827436,165,16434824)) (.node 28 (.leaf (30904678892,166,14141064)) (.leaf (1072691692,167,16341192)))) (.node 30 (.leaf (31137462764,168,16341192)) (.node 31 (.leaf (25762462188,169,16434824)) (.leaf (17172527596,169,16431240)))))) (.node 37 (.node 34 (.node 33 (.leaf (34352396780,170,16434824)) (.leaf (30038555116,169,16434376))) (.node 35 (.leaf (17153653228,169,16430344)) (.node 36 (.leaf (34333522412,170,16434376)) (.leaf (17178819052,171,16427208))))) (.node 40 (.node 38 (.leaf (29862394348,169,16427208)) (.node 39 (.leaf (25567427052,169,16426760)) (.leaf (34157361644,170,16427208)))) (.node 41 (.leaf (30063720940,171,16434824)) (.node 42 (.leaf (25768753644,171,16434376)) (.leaf (34358688236,172,16434824))))))))

noncomputable def models (i : Fin 43) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 43) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 43) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 70, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (7 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 70, (7 : Fin 8) ∈ U i → ∃ j : Fin 35, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C17

/- Source: MatroidCatalogue/Cases/N8R4C17Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C17


noncomputable def certificates_0 : List (Origin 70 43 × List Sat.Literal) :=
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
   ((.exchange 17 41 6),[(.neg 41),(.neg 17),(.pos 0),(.pos 3),(.pos 37)]),
   ((.exchange 17 57 3),[(.neg 57),(.neg 17),(.pos 15),(.pos 56)]),
   ((.exchange 17 59 2),[(.neg 59),(.neg 17),(.pos 16),(.pos 58)]),
   ((.exchange 17 63 0),[(.neg 63),(.neg 17),(.pos 24),(.pos 60)]),
   ((.exchange 17 64 0),[(.neg 64),(.neg 17),(.pos 24),(.pos 60)]),
   ((.exchange 18 41 6),[(.neg 41),(.neg 18),(.pos 4),(.pos 38)]),
   ((.exchange 18 56 3),[(.neg 56),(.neg 18),(.pos 15),(.pos 57)]),
   ((.exchange 18 58 2),[(.neg 58),(.neg 18),(.pos 16),(.pos 59)]),
   ((.exchange 20 41 6),[(.neg 41),(.neg 20),(.pos 1),(.pos 40)]),
   ((.exchange 20 60 0),[(.neg 60),(.neg 20),(.pos 24),(.pos 63)]),
   ((.exchange 20 62 2),[(.neg 62),(.neg 20),(.pos 19),(.pos 61)]),
   ((.exchange 20 64 0),[(.neg 64),(.neg 20),(.pos 24),(.pos 63)]),
   ((.exchange 21 37 6),[(.neg 37),(.neg 21),(.pos 1),(.pos 4),(.pos 41)]),
   ((.exchange 21 38 6),[(.neg 38),(.neg 21),(.pos 4),(.pos 41)]),
   ((.exchange 21 40 6),[(.neg 40),(.neg 21),(.pos 1),(.pos 41)]),
   ((.exchange 21 42 6),[(.neg 42),(.neg 21),(.pos 1),(.pos 4),(.pos 41)]),
   ((.exchange 21 43 6),[(.neg 43),(.neg 21),(.pos 4),(.pos 41)]),
   ((.exchange 21 46 6),[(.neg 46),(.neg 21),(.pos 1),(.pos 11),(.pos 41)]),
   ((.exchange 21 47 6),[(.neg 47),(.neg 21),(.pos 11),(.pos 41)]),
   ((.exchange 21 48 6),[(.neg 48),(.neg 21),(.pos 1),(.pos 4),(.pos 11),(.pos 41)]),
   ((.exchange 21 49 6),[(.neg 49),(.neg 21),(.pos 4),(.pos 11),(.pos 41)]),
   ((.exchange 21 50 6),[(.neg 50),(.neg 21),(.pos 4),(.pos 11),(.pos 41)]),
   ((.exchange 21 51 6),[(.neg 51),(.neg 21),(.pos 1),(.pos 11),(.pos 41)]),
   ((.exchange 21 52 6),[(.neg 52),(.neg 21),(.pos 11),(.pos 41)]),
   ((.exchange 21 53 6),[(.neg 53),(.neg 21),(.pos 11),(.pos 41)]),
   ((.exchange 21 54 6),[(.neg 54),(.neg 21),(.pos 4),(.pos 11),(.pos 41)]),
   ((.exchange 21 61 2),[(.neg 61),(.neg 21),(.pos 19),(.pos 62)]),
   ((.exchange 22 41 6),[(.neg 41),(.neg 22),(.pos 2),(.pos 3),(.pos 42)]),
   ((.exchange 22 60 0),[(.neg 60),(.neg 22),(.pos 24),(.pos 64)]),
   ((.exchange 22 63 0),[(.neg 63),(.neg 22),(.pos 24),(.pos 64)]),
   ((.exchange 23 41 6),[(.neg 41),(.neg 23),(.pos 4),(.pos 43)]),
   ((.exchange 26 41 6),[(.neg 41),(.neg 26),(.pos 5),(.pos 10),(.pos 46)]),
   ((.exchange 26 66 2),[(.neg 66),(.neg 26),(.pos 25),(.pos 65)]),
   ((.exchange 27 41 6),[(.neg 41),(.neg 27),(.pos 11),(.pos 47)]),
   ((.exchange 27 65 2),[(.neg 65),(.neg 27),(.pos 25),(.pos 66)]),
   ((.exchange 28 41 6),[(.neg 41),(.neg 28),(.pos 6),(.pos 7),(.pos 12),(.pos 48)]),
   ((.exchange 29 41 6),[(.neg 41),(.neg 29),(.pos 8),(.pos 13),(.pos 49)]),
   ((.exchange 30 41 6),[(.neg 41),(.neg 30),(.pos 8),(.pos 14),(.pos 50)]),
   ((.exchange 31 41 6),[(.neg 41),(.neg 31),(.pos 9),(.pos 10),(.pos 51)]),
   ((.exchange 32 41 6),[(.neg 41),(.neg 32),(.pos 11),(.pos 52)]),
   ((.exchange 33 41 6),[(.neg 41),(.neg 33),(.pos 11),(.pos 53)]),
   ((.exchange 34 41 6),[(.neg 41),(.neg 34),(.pos 13),(.pos 14),(.pos 54)]),
   ((.exchange 35 17 7),[(.neg 35),(.neg 17),(.pos 0),(.pos 15)]),
   ((.exchange 36 17 7),[(.neg 36),(.neg 17),(.pos 0),(.pos 16)]),
   ((.exchange 39 17 7),[(.neg 39),(.neg 17),(.pos 1),(.pos 2),(.pos 19)]),
   ((.exchange 44 17 7),[(.neg 44),(.neg 17),(.pos 3),(.pos 24)]),
   ((.exchange 45 17 7),[(.neg 45),(.neg 17),(.pos 5),(.pos 6),(.pos 25)]),
   ((.exchange 55 17 7),[(.neg 55),(.neg 17),(.pos 15),(.pos 16)]),
   ((.exchange 56 22 2),[(.neg 56),(.neg 22),(.pos 58),(.pos 61)]),
   ((.exchange 56 28 2),[(.neg 56),(.neg 28),(.pos 58),(.pos 65)]),
   ((.exchange 56 29 2),[(.neg 56),(.neg 29),(.pos 55),(.pos 58),(.pos 65)]),
   ((.exchange 56 30 0),[(.neg 56),(.neg 30),(.pos 60),(.pos 67)]),
   ((.exchange 57 22 2),[(.neg 57),(.neg 22),(.pos 55),(.pos 59),(.pos 62)]),
   ((.exchange 57 28 2),[(.neg 57),(.neg 28),(.pos 55),(.pos 59),(.pos 66)]),
   ((.exchange 57 29 2),[(.neg 57),(.neg 29),(.pos 59),(.pos 66)]),
   ((.exchange 57 30 1),[(.neg 57),(.neg 30),(.pos 60),(.pos 67)]),
   ((.exchange 57 33 1),[(.neg 57),(.neg 33),(.pos 63),(.pos 67)]),
   ((.exchange 57 68 1),[(.neg 68),(.neg 57),(.pos 60),(.pos 67)]),
   ((.exchange 57 69 2),[(.neg 69),(.neg 57),(.pos 62),(.pos 66)]),
   ((.exchange 58 20 3),[(.neg 58),(.neg 20),(.pos 56),(.pos 61)]),
   ((.exchange 58 27 3),[(.neg 58),(.neg 27),(.pos 55),(.pos 56),(.pos 65)]),
   ((.exchange 58 30 0),[(.neg 58),(.neg 30),(.pos 60),(.pos 68)]),
   ((.exchange 58 32 3),[(.neg 58),(.neg 32),(.pos 55),(.pos 61),(.pos 65)]),
   ((.exchange 58 34 0),[(.neg 58),(.neg 34),(.pos 64),(.pos 68)]),
   ((.exchange 58 41 3),[(.neg 58),(.neg 41),(.pos 55),(.pos 56),(.pos 61)]),
   ((.exchange 58 67 0),[(.neg 67),(.neg 58),(.pos 60),(.pos 68)]),
   ((.exchange 58 69 0),[(.neg 69),(.neg 58),(.pos 64),(.pos 68)]),
   ((.exchange 58 69 3),[(.neg 69),(.neg 58),(.pos 61),(.pos 65)]),
   ((.exchange 59 20 3),[(.neg 59),(.neg 20),(.pos 55),(.pos 57),(.pos 62)]),
   ((.exchange 59 27 3),[(.neg 59),(.neg 27),(.pos 57),(.pos 66)]),
   ((.exchange 59 31 3),[(.neg 59),(.neg 31),(.pos 55),(.pos 62),(.pos 66)]),
   ((.exchange 59 34 1),[(.neg 59),(.neg 34),(.pos 64),(.pos 68)]),
   ((.exchange 59 41 3),[(.neg 59),(.neg 41),(.pos 57),(.pos 62)]),
   ((.exchange 59 50 1),[(.neg 59),(.neg 50),(.pos 60),(.pos 68)]),
   ((.exchange 59 69 1),[(.neg 69),(.neg 59),(.pos 64),(.pos 68)]),
   ((.exchange 60 26 3),[(.neg 60),(.neg 26),(.pos 56),(.pos 67)]),
   ((.exchange 60 27 3),[(.neg 60),(.neg 27),(.pos 57),(.pos 67)]),
   ((.exchange 60 28 2),[(.neg 60),(.neg 28),(.pos 58),(.pos 68)]),
   ((.exchange 60 29 2),[(.neg 60),(.neg 29),(.pos 59),(.pos 68)]),
   ((.exchange 61 17 4),[(.neg 61),(.neg 17),(.pos 56),(.pos 58)]),
   ((.exchange 61 26 4),[(.neg 61),(.neg 26),(.pos 56),(.pos 65)]),
   ((.exchange 61 27 4),[(.neg 61),(.neg 27),(.pos 55),(.pos 56),(.pos 65)]),
   ((.exchange 61 28 4),[(.neg 61),(.neg 28),(.pos 58),(.pos 65)]),
   ((.exchange 61 30 0),[(.neg 61),(.neg 30),(.pos 63),(.pos 64),(.pos 69)]),
   ((.exchange 61 33 0),[(.neg 61),(.neg 33),(.pos 63),(.pos 69)]),
   ((.exchange 61 34 0),[(.neg 61),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 62 17 4),[(.neg 62),(.neg 17),(.pos 55),(.pos 57),(.pos 59)]),
   ((.exchange 62 26 4),[(.neg 62),(.neg 26),(.pos 55),(.pos 57),(.pos 66)]),
   ((.exchange 62 27 4),[(.neg 62),(.neg 27),(.pos 57),(.pos 66)]),
   ((.exchange 62 28 4),[(.neg 62),(.neg 28),(.pos 55),(.pos 59),(.pos 66)]),
   ((.exchange 62 30 1),[(.neg 62),(.neg 30),(.pos 63),(.pos 64),(.pos 69)]),
   ((.exchange 62 33 1),[(.neg 62),(.neg 33),(.pos 63),(.pos 69)]),
   ((.exchange 62 67 1),[(.neg 67),(.neg 62),(.pos 63),(.pos 69)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_1 : List (Origin 70 43 × List Sat.Literal) :=
  [((.exchange 63 27 4),[(.neg 63),(.neg 27),(.pos 57),(.pos 67)]),
   ((.exchange 64 28 4),[(.neg 64),(.neg 28),(.pos 58),(.pos 68)]),
   ((.exchange 64 29 4),[(.neg 64),(.neg 29),(.pos 59),(.pos 68)]),
   ((.exchange 64 31 3),[(.neg 64),(.neg 31),(.pos 61),(.pos 69)]),
   ((.exchange 64 32 3),[(.neg 64),(.neg 32),(.pos 62),(.pos 69)]),
   ((.exchange 64 52 3),[(.neg 64),(.neg 52),(.pos 62),(.pos 69)]),
   ((.exchange 64 65 4),[(.neg 65),(.neg 64),(.pos 58),(.pos 68)]),
   ((.exchange 64 66 4),[(.neg 66),(.neg 64),(.pos 59),(.pos 68)]),
   ((.exchange 65 17 5),[(.neg 65),(.neg 17),(.pos 56),(.pos 58)]),
   ((.exchange 65 20 5),[(.neg 65),(.neg 20),(.pos 56),(.pos 61)]),
   ((.exchange 65 22 5),[(.neg 65),(.neg 22),(.pos 58),(.pos 61)]),
   ((.exchange 65 30 0),[(.neg 65),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 65 34 0),[(.neg 65),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 65 41 5),[(.neg 65),(.neg 41),(.pos 55),(.pos 56),(.pos 61)]),
   ((.exchange 65 50 0),[(.neg 65),(.neg 50),(.pos 67),(.pos 68)]),
   ((.exchange 65 60 5),[(.neg 65),(.neg 60),(.pos 56),(.pos 58)]),
   ((.exchange 65 63 5),[(.neg 65),(.neg 63),(.pos 56),(.pos 61)]),
   ((.exchange 66 17 5),[(.neg 66),(.neg 17),(.pos 55),(.pos 57),(.pos 59)]),
   ((.exchange 66 30 1),[(.neg 66),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 66 34 1),[(.neg 66),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 66 41 5),[(.neg 66),(.neg 41),(.pos 57),(.pos 62)]),
   ((.exchange 66 50 1),[(.neg 66),(.neg 50),(.pos 67),(.pos 68)]),
   ((.exchange 66 60 5),[(.neg 66),(.neg 60),(.pos 57),(.pos 59)]),
   ((.exchange 66 63 5),[(.neg 66),(.neg 63),(.pos 57),(.pos 62)]),
   ((.exchange 66 64 5),[(.neg 66),(.neg 64),(.pos 59),(.pos 62)]),
   ((.exchange 67 17 5),[(.neg 67),(.neg 17),(.pos 56),(.pos 60)]),
   ((.exchange 67 18 5),[(.neg 67),(.neg 18),(.pos 57),(.pos 60)]),
   ((.exchange 67 20 5),[(.neg 67),(.neg 20),(.pos 56),(.pos 63)]),
   ((.exchange 67 31 2),[(.neg 67),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 67 32 2),[(.neg 67),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 67 34 2),[(.neg 67),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 67 37 5),[(.neg 67),(.neg 37),(.pos 56),(.pos 60)]),
   ((.exchange 67 40 5),[(.neg 67),(.neg 40),(.pos 56),(.pos 63)]),
   ((.exchange 67 48 2),[(.neg 67),(.neg 48),(.pos 65),(.pos 68)]),
   ((.exchange 67 49 2),[(.neg 67),(.neg 49),(.pos 66),(.pos 68)]),
   ((.exchange 67 54 2),[(.neg 67),(.neg 54),(.pos 68),(.pos 69)]),
   ((.exchange 67 64 2),[(.neg 67),(.neg 64),(.pos 68),(.pos 69)]),
   ((.exchange 68 17 5),[(.neg 68),(.neg 17),(.pos 58),(.pos 60)]),
   ((.exchange 68 18 5),[(.neg 68),(.neg 18),(.pos 59),(.pos 60)]),
   ((.exchange 68 22 5),[(.neg 68),(.neg 22),(.pos 58),(.pos 64)]),
   ((.exchange 68 23 5),[(.neg 68),(.neg 23),(.pos 59),(.pos 64)]),
   ((.exchange 68 26 3),[(.neg 68),(.neg 26),(.pos 65),(.pos 67)]),
   ((.exchange 68 27 3),[(.neg 68),(.neg 27),(.pos 66),(.pos 67)]),
   ((.exchange 68 31 3),[(.neg 68),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 68 32 3),[(.neg 68),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 68 33 3),[(.neg 68),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 68 37 5),[(.neg 68),(.neg 37),(.pos 58),(.pos 60)]),
   ((.exchange 68 42 5),[(.neg 68),(.neg 42),(.pos 58),(.pos 64)]),
   ((.exchange 68 43 5),[(.neg 68),(.neg 43),(.pos 59),(.pos 64)]),
   ((.exchange 68 51 3),[(.neg 68),(.neg 51),(.pos 65),(.pos 69)]),
   ((.exchange 68 56 3),[(.neg 68),(.neg 56),(.pos 65),(.pos 67)]),
   ((.exchange 68 57 3),[(.neg 68),(.neg 57),(.pos 66),(.pos 67)]),
   ((.exchange 68 63 3),[(.neg 68),(.neg 63),(.pos 67),(.pos 69)]),
   ((.exchange 69 17 5),[(.neg 69),(.neg 17),(.pos 61),(.pos 63),(.pos 64)]),
   ((.exchange 69 18 5),[(.neg 69),(.neg 18),(.pos 62),(.pos 63),(.pos 64)]),
   ((.exchange 69 20 5),[(.neg 69),(.neg 20),(.pos 61),(.pos 63)]),
   ((.exchange 69 22 5),[(.neg 69),(.neg 22),(.pos 61),(.pos 64)]),
   ((.exchange 69 28 4),[(.neg 69),(.neg 28),(.pos 65),(.pos 68)]),
   ((.exchange 69 29 4),[(.neg 69),(.neg 29),(.pos 66),(.pos 68)]),
   ((.exchange 69 30 4),[(.neg 69),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 69 46 4),[(.neg 69),(.neg 46),(.pos 65),(.pos 67)]),
   ((.exchange 69 56 5),[(.neg 69),(.neg 56),(.pos 61),(.pos 63)]),
   ((.exchange 69 57 5),[(.neg 69),(.neg 57),(.pos 62),(.pos 63)]),
   (.newPoint,[(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 0),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 64),(.pos 67)]),
   ((.excluded 1),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 58),(.pos 59),(.pos 60),(.pos 63),(.pos 64),(.pos 68)]),
   ((.excluded 2),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 3),[(.neg 69),(.neg 68),(.neg 67),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 63),(.pos 64),(.pos 65),(.pos 66)]),
   ((.excluded 4),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 63),(.pos 64)]),
   ((.excluded 5),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 60),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 61),(.pos 62),(.pos 65),(.pos 66)]),
   ((.excluded 6),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 7),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 65),(.pos 66)]),
   ((.excluded 8),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 68)]),
   ((.excluded 9),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 69)]),
   ((.excluded 10),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 11),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 61),(.pos 62),(.pos 68)]),
   ((.excluded 12),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 68)]),
   ((.excluded 13),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 61),(.pos 62),(.pos 67)]),
   ((.excluded 14),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 15),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 58),(.pos 59),(.pos 67)]),
   ((.excluded 16),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 58),(.pos 59),(.pos 69)]),
   ((.excluded 17),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 58),(.pos 59)]),
   ((.excluded 18),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 67)]),
   ((.excluded 19),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 69)]),
   ((.excluded 20),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55)]),
   ((.excluded 21),[(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 22),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 64),(.pos 67)]),
   ((.excluded 23),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 58),(.pos 59),(.pos 60),(.pos 63),(.pos 64),(.pos 68)]),
   ((.excluded 24),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 25),[(.neg 69),(.neg 68),(.neg 67),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 60),(.pos 63),(.pos 64),(.pos 65),(.pos 66)]),
   ((.excluded 26),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 60),(.pos 63),(.pos 64)]),
   ((.excluded 27),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 60),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 61),(.pos 62),(.pos 65),(.pos 66)]),
   ((.excluded 28),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 29),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 65),(.pos 66)]),
   ((.excluded 30),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 68)]),
   ((.excluded 31),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 69)]),
   ((.excluded 32),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 33),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 58),(.pos 59),(.pos 67)]),
   ((.excluded 34),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 58),(.pos 59),(.pos 69)]),
   ((.excluded 35),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 58),(.pos 59)]),
   ((.excluded 36),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 69)]),
   ((.excluded 37),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 61),(.pos 62),(.pos 67)]),
   ((.excluded 38),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 61),(.pos 62),(.pos 68)]),
   ((.excluded 39),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 40),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 67)]),
   ((.excluded 41),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 68)]),
   ((.excluded 42),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55)])]

theorem certificates_1_valid : ∀ oc ∈ certificates_1,
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
        Papers.RationalityTen.MatroidChecked.FastSemanticChecks.RawWitness 8 (N7R4.familyMasks.get 17)
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


end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C17

/- Source: MatroidCatalogue/Cases/N8R4C17Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C17

noncomputable def certificates : List (Origin 70 43 × List Sat.Literal) :=
  certificates_0 ++ certificates_1

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  intro oc hoc
  simp only [certificates,List.mem_append,or_assoc] at hoc
  rcases hoc with h0 | h1
  · exact certificates_0_valid oc h0
  · exact certificates_1_valid oc h1

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
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C17.formula []
    exact Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C17.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 8 4 (target w),family_mem 8 4 (target w) hw.1,?_⟩
    exact validWitness_sound 8 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C17


end
end
end BundlePart3

section BundlePart4
/- Source: MatroidChecked/SemanticChunks/Cases03Part04.lean -/




@[expose] public section
noncomputable section

/- Source: MatroidCatalogue/Cases/N8R4C18Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C18

abbrev U := N8R4.grid
noncomputable def old : Finset (Finset (Fin 8)) := N7R4.family 18
noncomputable def newIndexTree : Table ℕ := (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf 35) (.leaf 36)) (.node 3 (.leaf 37) (.leaf 38))) (.node 6 (.node 5 (.leaf 39) (.leaf 40)) (.node 7 (.leaf 41) (.leaf 42)))) (.node 12 (.node 10 (.node 9 (.leaf 43) (.leaf 44)) (.node 11 (.leaf 45) (.leaf 46))) (.node 14 (.node 13 (.leaf 47) (.leaf 48)) (.node 15 (.leaf 49) (.node 16 (.leaf 50) (.leaf 51)))))) (.node 26 (.node 21 (.node 19 (.node 18 (.leaf 52) (.leaf 53)) (.node 20 (.leaf 54) (.leaf 55))) (.node 23 (.node 22 (.leaf 56) (.leaf 57)) (.node 24 (.leaf 58) (.node 25 (.leaf 59) (.leaf 60))))) (.node 30 (.node 28 (.node 27 (.leaf 61) (.leaf 62)) (.node 29 (.leaf 63) (.leaf 64))) (.node 32 (.node 31 (.leaf 65) (.leaf 66)) (.node 33 (.leaf 67) (.node 34 (.leaf 68) (.leaf 69)))))))
noncomputable def newIndex (i : Fin 35) : Fin 70 := Fin.ofNat 70 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 31 (.node 15 (.node 7 (.node 3 (.node 1 (.leaf (30903631872,32,6248648)) (.node 2 (.leaf (29754392576,37,8345736)) (.leaf (33814478848,43,6248648)))) (.node 5 (.node 4 (.leaf (25761415168,43,6219976)) (.leaf (17171480576,43,6212808))) (.node 6 (.leaf (34351349760,45,8345736)) (.leaf (25172115456,37,8344840))))) (.node 11 (.node 9 (.node 8 (.leaf (16171139072,37,8334088)) (.leaf (30599544832,43,6150536))) (.node 10 (.leaf (29525803008,53,6248648)) (.leaf (33820770304,54,10433864)))) (.node 13 (.node 12 (.leaf (1071644672,37,8219400)) (.leaf (31102861312,43,6155016))) (.node 14 (.leaf (30867980288,43,6151432)) (.leaf (31136415744,45,8219400)))))) (.node 23 (.node 19 (.node 17 (.node 16 (.leaf (34122760192,43,6241032)) (.leaf (17144217600,53,6212808))) (.node 18 (.leaf (34324086784,54,10442376)) (.leaf (17152606208,43,6211464)))) (.node 21 (.node 20 (.leaf (17177772032,54,10333512)) (.leaf (34064039936,43,6248200))) (.node 22 (.leaf (30037508096,43,6219528)) (.leaf (34332475392,45,8344840))))) (.node 27 (.node 25 (.node 24 (.leaf (25499271168,53,6219976)) (.leaf (34089205760,54,10435208))) (.node 26 (.leaf (29861347328,43,6208776)) (.leaf (25566380032,43,6207880)))) (.node 29 (.node 28 (.leaf (34156314624,45,8334088)) (.leaf (30062673920,54,10349192))) (.node 30 (.leaf (25767706624,54,10347848)) (.leaf (34357641216,55,14599816))))))) (.node 47 (.node 39 (.node 35 (.node 33 (.node 32 (.leaf (1047532,173,7072520)) (.leaf (30904679404,174,16434824))) (.node 34 (.leaf (29755440108,175,16434824)) (.leaf (33815526380,176,16434824)))) (.node 37 (.node 36 (.leaf (25762462700,176,16406152)) (.leaf (17172528108,176,16398984))) (.node 38 (.leaf (34352397292,177,16434824)) (.leaf (25173162988,175,16434376))))) (.node 43 (.node 41 (.node 40 (.leaf (16172186604,175,16427208)) (.leaf (30600592364,176,16336712))) (.node 42 (.leaf (29526850540,178,16373896)) (.leaf (33821817836,179,16430344)))) (.node 45 (.node 44 (.leaf (1072692204,175,16341192)) (.leaf (31103908844,176,16341192))) (.node 46 (.leaf (30869027820,176,16337608)) (.leaf (31137463276,177,16341192)))))) (.node 55 (.node 51 (.node 49 (.node 48 (.leaf (34065087468,176,16434376)) (.leaf (30038555628,176,16405704))) (.node 50 (.leaf (17153653740,176,16397640)) (.leaf (34333522924,177,16434376)))) (.node 53 (.node 52 (.leaf (25500318700,178,16431240)) (.leaf (34090253292,179,16431240))) (.node 54 (.leaf (17145265132,178,16434824)) (.leaf (17178819564,179,16362248))))) (.node 59 (.node 57 (.node 56 (.leaf (34123807724,176,16427208)) (.leaf (34325134316,179,16434824))) (.node 58 (.leaf (29862394860,176,16394952)) (.leaf (25567427564,176,16394056)))) (.node 61 (.node 60 (.leaf (34157362156,177,16427208)) (.leaf (30063721452,179,16373896))) (.node 62 (.leaf (25768754156,179,16373000)) (.leaf (34358688748,180,16434824))))))))

noncomputable def models (i : Fin 63) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 63) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 63) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 70, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (7 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 70, (7 : Fin 8) ∈ U i → ∃ j : Fin 35, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C18

/- Source: MatroidCatalogue/Cases/N8R4C18Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C18


noncomputable def certificates_0 : List (Origin 70 63 × List Sat.Literal) :=
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
   ((.exchange 17 41 6),[(.neg 41),(.neg 17),(.pos 0),(.pos 3),(.pos 37)]),
   ((.exchange 17 57 3),[(.neg 57),(.neg 17),(.pos 15),(.pos 56)]),
   ((.exchange 17 59 2),[(.neg 59),(.neg 17),(.pos 16),(.pos 58)]),
   ((.exchange 18 41 6),[(.neg 41),(.neg 18),(.pos 4),(.pos 38)]),
   ((.exchange 18 56 3),[(.neg 56),(.neg 18),(.pos 15),(.pos 57)]),
   ((.exchange 18 58 2),[(.neg 58),(.neg 18),(.pos 16),(.pos 59)]),
   ((.exchange 20 41 6),[(.neg 41),(.neg 20),(.pos 1),(.pos 40)]),
   ((.exchange 20 62 2),[(.neg 62),(.neg 20),(.pos 19),(.pos 61)]),
   ((.exchange 21 37 6),[(.neg 37),(.neg 21),(.pos 1),(.pos 4),(.pos 41)]),
   ((.exchange 21 38 6),[(.neg 38),(.neg 21),(.pos 4),(.pos 41)]),
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
   ((.exchange 21 53 6),[(.neg 53),(.neg 21),(.pos 11),(.pos 41)]),
   ((.exchange 21 54 6),[(.neg 54),(.neg 21),(.pos 4),(.pos 11),(.pos 41)]),
   ((.exchange 21 61 2),[(.neg 61),(.neg 21),(.pos 19),(.pos 62)]),
   ((.exchange 22 41 6),[(.neg 41),(.neg 22),(.pos 2),(.pos 3),(.pos 42)]),
   ((.exchange 23 41 6),[(.neg 41),(.neg 23),(.pos 4),(.pos 43)]),
   ((.exchange 24 41 6),[(.neg 41),(.neg 24),(.pos 4),(.pos 44)]),
   ((.exchange 26 41 6),[(.neg 41),(.neg 26),(.pos 5),(.pos 10),(.pos 46)]),
   ((.exchange 26 66 2),[(.neg 66),(.neg 26),(.pos 25),(.pos 65)]),
   ((.exchange 27 41 6),[(.neg 41),(.neg 27),(.pos 11),(.pos 47)]),
   ((.exchange 27 65 2),[(.neg 65),(.neg 27),(.pos 25),(.pos 66)]),
   ((.exchange 28 41 6),[(.neg 41),(.neg 28),(.pos 6),(.pos 7),(.pos 12),(.pos 48)]),
   ((.exchange 29 41 6),[(.neg 41),(.neg 29),(.pos 8),(.pos 13),(.pos 49)]),
   ((.exchange 30 41 6),[(.neg 41),(.neg 30),(.pos 8),(.pos 14),(.pos 50)]),
   ((.exchange 31 41 6),[(.neg 41),(.neg 31),(.pos 9),(.pos 10),(.pos 51)]),
   ((.exchange 32 41 6),[(.neg 41),(.neg 32),(.pos 11),(.pos 52)]),
   ((.exchange 33 41 6),[(.neg 41),(.neg 33),(.pos 11),(.pos 53)]),
   ((.exchange 34 41 6),[(.neg 41),(.neg 34),(.pos 13),(.pos 14),(.pos 54)]),
   ((.exchange 35 17 7),[(.neg 35),(.neg 17),(.pos 0),(.pos 15)]),
   ((.exchange 36 17 7),[(.neg 36),(.neg 17),(.pos 0),(.pos 16)]),
   ((.exchange 39 17 7),[(.neg 39),(.neg 17),(.pos 1),(.pos 2),(.pos 19)]),
   ((.exchange 45 17 7),[(.neg 45),(.neg 17),(.pos 5),(.pos 6),(.pos 25)]),
   ((.exchange 55 17 7),[(.neg 55),(.neg 17),(.pos 15),(.pos 16)]),
   ((.exchange 56 22 2),[(.neg 56),(.neg 22),(.pos 58),(.pos 61)]),
   ((.exchange 56 24 0),[(.neg 56),(.neg 24),(.pos 60),(.pos 63)]),
   ((.exchange 56 28 2),[(.neg 56),(.neg 28),(.pos 58),(.pos 65)]),
   ((.exchange 56 31 2),[(.neg 56),(.neg 31),(.pos 61),(.pos 65)]),
   ((.exchange 56 48 2),[(.neg 56),(.neg 48),(.pos 58),(.pos 65)]),
   ((.exchange 56 51 2),[(.neg 56),(.neg 51),(.pos 61),(.pos 65)]),
   ((.exchange 57 22 2),[(.neg 57),(.neg 22),(.pos 55),(.pos 59),(.pos 62)]),
   ((.exchange 57 28 2),[(.neg 57),(.neg 28),(.pos 55),(.pos 59),(.pos 66)]),
   ((.exchange 57 31 2),[(.neg 57),(.neg 31),(.pos 55),(.pos 62),(.pos 66)]),
   ((.exchange 57 33 1),[(.neg 57),(.neg 33),(.pos 63),(.pos 67)]),
   ((.exchange 57 48 2),[(.neg 57),(.neg 48),(.pos 55),(.pos 59),(.pos 66)]),
   ((.exchange 57 50 1),[(.neg 57),(.neg 50),(.pos 60),(.pos 67)]),
   ((.exchange 57 51 2),[(.neg 57),(.neg 51),(.pos 55),(.pos 62),(.pos 66)]),
   ((.exchange 57 53 1),[(.neg 57),(.neg 53),(.pos 63),(.pos 67)]),
   ((.exchange 57 68 1),[(.neg 68),(.neg 57),(.pos 60),(.pos 67)]),
   ((.exchange 57 69 2),[(.neg 69),(.neg 57),(.pos 62),(.pos 66)]),
   ((.exchange 58 20 3),[(.neg 58),(.neg 20),(.pos 56),(.pos 61)]),
   ((.exchange 58 24 0),[(.neg 58),(.neg 24),(.pos 60),(.pos 64)]),
   ((.exchange 58 27 3),[(.neg 58),(.neg 27),(.pos 55),(.pos 56),(.pos 65)]),
   ((.exchange 58 30 0),[(.neg 58),(.neg 30),(.pos 60),(.pos 68)]),
   ((.exchange 58 41 3),[(.neg 58),(.neg 41),(.pos 55),(.pos 56),(.pos 61)]),
   ((.exchange 58 63 0),[(.neg 63),(.neg 58),(.pos 60),(.pos 64)]),
   ((.exchange 58 67 0),[(.neg 67),(.neg 58),(.pos 60),(.pos 68)]),
   ((.exchange 58 69 3),[(.neg 69),(.neg 58),(.pos 61),(.pos 65)]),
   ((.exchange 59 20 3),[(.neg 59),(.neg 20),(.pos 55),(.pos 57),(.pos 62)]),
   ((.exchange 59 27 3),[(.neg 59),(.neg 27),(.pos 57),(.pos 66)]),
   ((.exchange 59 30 1),[(.neg 59),(.neg 30),(.pos 60),(.pos 68)]),
   ((.exchange 59 34 1),[(.neg 59),(.neg 34),(.pos 64),(.pos 68)]),
   ((.exchange 59 54 1),[(.neg 59),(.neg 54),(.pos 64),(.pos 68)]),
   ((.exchange 59 67 1),[(.neg 67),(.neg 59),(.pos 60),(.pos 68)]),
   ((.exchange 60 20 3),[(.neg 60),(.neg 20),(.pos 56),(.pos 63)]),
   ((.exchange 60 26 3),[(.neg 60),(.neg 26),(.pos 56),(.pos 67)]),
   ((.exchange 60 27 3),[(.neg 60),(.neg 27),(.pos 57),(.pos 67)]),
   ((.exchange 60 28 2),[(.neg 60),(.neg 28),(.pos 58),(.pos 68)]),
   ((.exchange 60 29 2),[(.neg 60),(.neg 29),(.pos 59),(.pos 68)]),
   ((.exchange 60 48 2),[(.neg 60),(.neg 48),(.pos 58),(.pos 68)]),
   ((.exchange 60 53 3),[(.neg 60),(.neg 53),(.pos 63),(.pos 67)]),
   ((.exchange 60 61 2),[(.neg 61),(.neg 60),(.pos 58),(.pos 64)]),
   ((.exchange 60 69 2),[(.neg 69),(.neg 60),(.pos 64),(.pos 68)]),
   ((.exchange 61 17 4),[(.neg 61),(.neg 17),(.pos 56),(.pos 58)]),
   ((.exchange 61 26 4),[(.neg 61),(.neg 26),(.pos 56),(.pos 65)]),
   ((.exchange 61 27 4),[(.neg 61),(.neg 27),(.pos 55),(.pos 56),(.pos 65)]),
   ((.exchange 61 34 0),[(.neg 61),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 61 67 0),[(.neg 67),(.neg 61),(.pos 63),(.pos 69)]),
   ((.exchange 61 68 0),[(.neg 68),(.neg 61),(.pos 64),(.pos 69)]),
   ((.exchange 62 17 4),[(.neg 62),(.neg 17),(.pos 55),(.pos 57),(.pos 59)]),
   ((.exchange 62 24 1),[(.neg 62),(.neg 24),(.pos 63),(.pos 64)]),
   ((.exchange 62 26 4),[(.neg 62),(.neg 26),(.pos 55),(.pos 57),(.pos 66)]),
   ((.exchange 62 27 4),[(.neg 62),(.neg 27),(.pos 57),(.pos 66)]),
   ((.exchange 62 33 1),[(.neg 62),(.neg 33),(.pos 63),(.pos 69)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_1 : List (Origin 70 63 × List Sat.Literal) :=
  [((.exchange 62 34 1),[(.neg 62),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 62 44 1),[(.neg 62),(.neg 44),(.pos 63),(.pos 64)]),
   ((.exchange 62 54 1),[(.neg 62),(.neg 54),(.pos 64),(.pos 69)]),
   ((.exchange 62 67 1),[(.neg 67),(.neg 62),(.pos 63),(.pos 69)]),
   ((.exchange 62 68 1),[(.neg 68),(.neg 62),(.pos 64),(.pos 69)]),
   ((.exchange 63 18 4),[(.neg 63),(.neg 18),(.pos 57),(.pos 60)]),
   ((.exchange 63 22 2),[(.neg 63),(.neg 22),(.pos 61),(.pos 64)]),
   ((.exchange 63 23 2),[(.neg 63),(.neg 23),(.pos 62),(.pos 64)]),
   ((.exchange 63 27 4),[(.neg 63),(.neg 27),(.pos 57),(.pos 67)]),
   ((.exchange 63 31 2),[(.neg 63),(.neg 31),(.pos 61),(.pos 69)]),
   ((.exchange 63 32 2),[(.neg 63),(.neg 32),(.pos 62),(.pos 69)]),
   ((.exchange 63 34 2),[(.neg 63),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 63 38 4),[(.neg 63),(.neg 38),(.pos 57),(.pos 60)]),
   ((.exchange 63 42 2),[(.neg 63),(.neg 42),(.pos 61),(.pos 64)]),
   ((.exchange 63 43 2),[(.neg 63),(.neg 43),(.pos 62),(.pos 64)]),
   ((.exchange 63 47 4),[(.neg 63),(.neg 47),(.pos 57),(.pos 67)]),
   ((.exchange 63 51 2),[(.neg 63),(.neg 51),(.pos 61),(.pos 69)]),
   ((.exchange 63 65 2),[(.neg 65),(.neg 63),(.pos 61),(.pos 69)]),
   ((.exchange 63 66 2),[(.neg 66),(.neg 63),(.pos 62),(.pos 69)]),
   ((.exchange 63 68 2),[(.neg 68),(.neg 63),(.pos 64),(.pos 69)]),
   ((.exchange 64 18 4),[(.neg 64),(.neg 18),(.pos 59),(.pos 60)]),
   ((.exchange 64 20 3),[(.neg 64),(.neg 20),(.pos 61),(.pos 63)]),
   ((.exchange 64 21 3),[(.neg 64),(.neg 21),(.pos 62),(.pos 63)]),
   ((.exchange 64 29 4),[(.neg 64),(.neg 29),(.pos 59),(.pos 68)]),
   ((.exchange 64 30 4),[(.neg 64),(.neg 30),(.pos 60),(.pos 68)]),
   ((.exchange 64 38 4),[(.neg 64),(.neg 38),(.pos 59),(.pos 60)]),
   ((.exchange 64 41 3),[(.neg 64),(.neg 41),(.pos 62),(.pos 63)]),
   ((.exchange 64 56 3),[(.neg 64),(.neg 56),(.pos 61),(.pos 63)]),
   ((.exchange 64 65 3),[(.neg 65),(.neg 64),(.pos 61),(.pos 69)]),
   ((.exchange 64 67 3),[(.neg 67),(.neg 64),(.pos 63),(.pos 69)]),
   ((.exchange 65 23 5),[(.neg 65),(.neg 23),(.pos 55),(.pos 58),(.pos 61)]),
   ((.exchange 65 30 0),[(.neg 65),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 65 41 5),[(.neg 65),(.neg 41),(.pos 55),(.pos 56),(.pos 61)]),
   ((.exchange 65 53 0),[(.neg 65),(.neg 53),(.pos 67),(.pos 69)]),
   ((.exchange 65 54 0),[(.neg 65),(.neg 54),(.pos 68),(.pos 69)]),
   ((.exchange 65 60 0),[(.neg 65),(.neg 60),(.pos 67),(.pos 68)]),
   ((.exchange 65 60 5),[(.neg 65),(.neg 60),(.pos 56),(.pos 58)]),
   ((.exchange 65 63 5),[(.neg 65),(.neg 63),(.pos 56),(.pos 61)]),
   ((.exchange 65 64 0),[(.neg 65),(.neg 64),(.pos 68),(.pos 69)]),
   ((.exchange 66 23 5),[(.neg 66),(.neg 23),(.pos 59),(.pos 62)]),
   ((.exchange 66 30 1),[(.neg 66),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 66 34 1),[(.neg 66),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 66 41 5),[(.neg 66),(.neg 41),(.pos 57),(.pos 62)]),
   ((.exchange 66 53 1),[(.neg 66),(.neg 53),(.pos 67),(.pos 69)]),
   ((.exchange 66 60 5),[(.neg 66),(.neg 60),(.pos 57),(.pos 59)]),
   ((.exchange 66 63 5),[(.neg 66),(.neg 63),(.pos 57),(.pos 62)]),
   ((.exchange 66 64 1),[(.neg 66),(.neg 64),(.pos 68),(.pos 69)]),
   ((.exchange 67 17 5),[(.neg 67),(.neg 17),(.pos 56),(.pos 60)]),
   ((.exchange 67 20 5),[(.neg 67),(.neg 20),(.pos 56),(.pos 63)]),
   ((.exchange 67 21 5),[(.neg 67),(.neg 21),(.pos 57),(.pos 63)]),
   ((.exchange 67 29 2),[(.neg 67),(.neg 29),(.pos 66),(.pos 68)]),
   ((.exchange 67 31 2),[(.neg 67),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 67 32 2),[(.neg 67),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 67 34 2),[(.neg 67),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 67 38 5),[(.neg 67),(.neg 38),(.pos 57),(.pos 60)]),
   ((.exchange 67 44 5),[(.neg 67),(.neg 44),(.pos 60),(.pos 63)]),
   ((.exchange 67 54 2),[(.neg 67),(.neg 54),(.pos 68),(.pos 69)]),
   ((.exchange 67 64 5),[(.neg 67),(.neg 64),(.pos 60),(.pos 63)]),
   ((.exchange 68 17 5),[(.neg 68),(.neg 17),(.pos 58),(.pos 60)]),
   ((.exchange 68 18 5),[(.neg 68),(.neg 18),(.pos 59),(.pos 60)]),
   ((.exchange 68 22 5),[(.neg 68),(.neg 22),(.pos 58),(.pos 64)]),
   ((.exchange 68 23 5),[(.neg 68),(.neg 23),(.pos 59),(.pos 64)]),
   ((.exchange 68 24 5),[(.neg 68),(.neg 24),(.pos 60),(.pos 64)]),
   ((.exchange 68 26 3),[(.neg 68),(.neg 26),(.pos 65),(.pos 67)]),
   ((.exchange 68 27 3),[(.neg 68),(.neg 27),(.pos 66),(.pos 67)]),
   ((.exchange 68 33 3),[(.neg 68),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 68 38 5),[(.neg 68),(.neg 38),(.pos 59),(.pos 60)]),
   ((.exchange 68 56 3),[(.neg 68),(.neg 56),(.pos 65),(.pos 67)]),
   ((.exchange 68 57 3),[(.neg 68),(.neg 57),(.pos 66),(.pos 67)]),
   ((.exchange 68 63 3),[(.neg 68),(.neg 63),(.pos 67),(.pos 69)]),
   ((.exchange 69 22 5),[(.neg 69),(.neg 22),(.pos 61),(.pos 64)]),
   ((.exchange 69 23 5),[(.neg 69),(.neg 23),(.pos 62),(.pos 64)]),
   ((.exchange 69 26 4),[(.neg 69),(.neg 26),(.pos 65),(.pos 67)]),
   ((.exchange 69 28 4),[(.neg 69),(.neg 28),(.pos 65),(.pos 68)]),
   ((.exchange 69 29 4),[(.neg 69),(.neg 29),(.pos 66),(.pos 68)]),
   ((.exchange 69 30 4),[(.neg 69),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 69 40 5),[(.neg 69),(.neg 40),(.pos 61),(.pos 63)]),
   ((.exchange 69 41 5),[(.neg 69),(.neg 41),(.pos 62),(.pos 63)]),
   ((.exchange 69 42 5),[(.neg 69),(.neg 42),(.pos 61),(.pos 64)]),
   ((.exchange 69 43 5),[(.neg 69),(.neg 43),(.pos 62),(.pos 64)]),
   ((.exchange 69 44 5),[(.neg 69),(.neg 44),(.pos 63),(.pos 64)]),
   ((.exchange 69 47 4),[(.neg 69),(.neg 47),(.pos 66),(.pos 67)]),
   ((.exchange 69 49 4),[(.neg 69),(.neg 49),(.pos 66),(.pos 68)]),
   ((.exchange 69 59 4),[(.neg 69),(.neg 59),(.pos 66),(.pos 68)]),
   ((.exchange 69 60 5),[(.neg 69),(.neg 60),(.pos 63),(.pos 64)]),
   (.newPoint,[(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 0),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 60),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 61),(.pos 62),(.pos 65),(.pos 66)]),
   ((.excluded 1),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 2),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 64)]),
   ((.excluded 3),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 68)]),
   ((.excluded 4),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 69)]),
   ((.excluded 5),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 6),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 68)]),
   ((.excluded 7),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 8),[(.neg 69),(.neg 68),(.neg 67),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 64),(.pos 65),(.pos 66)]),
   ((.excluded 9),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 64),(.pos 67)]),
   ((.excluded 10),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 64)]),
   ((.excluded 11),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 12),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 65),(.pos 66)]),
   ((.excluded 13),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 63),(.pos 65),(.pos 66)]),
   ((.excluded 14),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 65),(.pos 66)]),
   ((.excluded 15),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 61),(.pos 62)]),
   ((.excluded 16),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 69)]),
   ((.excluded 17),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 60)]),
   ((.excluded 18),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 58),(.pos 59),(.pos 69)]),
   ((.excluded 19),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 69)]),
   ((.excluded 20),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 58),(.pos 59),(.pos 63)]),
   ((.excluded 21),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 58),(.pos 59),(.pos 67)]),
   ((.excluded 22),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 58),(.pos 59)]),
   ((.excluded 23),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 63),(.pos 68)]),
   ((.excluded 24),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 63)]),
   ((.excluded 25),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 61),(.pos 62),(.pos 67)]),
   ((.excluded 26),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 61),(.pos 62),(.pos 68)]),
   ((.excluded 27),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 28),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 67)]),
   ((.excluded 29),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 68)]),
   ((.excluded 30),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55)]),
   ((.excluded 31),[(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 32),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 60),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 61),(.pos 62),(.pos 65),(.pos 66)]),
   ((.excluded 33),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 34),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 64)]),
   ((.excluded 35),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 68)]),
   ((.excluded 36),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 69)]),
   ((.excluded 37),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 38),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 68)]),
   ((.excluded 39),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 40),[(.neg 69),(.neg 68),(.neg 67),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 64),(.pos 65),(.pos 66)]),
   ((.excluded 41),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 64),(.pos 67)])]

theorem certificates_1_valid : ∀ oc ∈ certificates_1,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_2 : List (Origin 70 63 × List Sat.Literal) :=
  [((.excluded 42),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 64)]),
   ((.excluded 43),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 44),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 60),(.pos 65),(.pos 66)]),
   ((.excluded 45),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 63),(.pos 65),(.pos 66)]),
   ((.excluded 46),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 65),(.pos 66)]),
   ((.excluded 47),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 58),(.pos 59),(.pos 63)]),
   ((.excluded 48),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 58),(.pos 59),(.pos 67)]),
   ((.excluded 49),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 58),(.pos 59),(.pos 69)]),
   ((.excluded 50),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 58),(.pos 59)]),
   ((.excluded 51),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 63),(.pos 68)]),
   ((.excluded 52),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 63)]),
   ((.excluded 53),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 60),(.pos 69)]),
   ((.excluded 54),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 69)]),
   ((.excluded 55),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 60),(.pos 61),(.pos 62)]),
   ((.excluded 56),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 60)]),
   ((.excluded 57),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 61),(.pos 62),(.pos 67)]),
   ((.excluded 58),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 61),(.pos 62),(.pos 68)]),
   ((.excluded 59),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 61),(.pos 62)]),
   ((.excluded 60),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 67)]),
   ((.excluded 61),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 68)]),
   ((.excluded 62),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55)])]

theorem certificates_2_valid : ∀ oc ∈ certificates_2,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



theorem witness_0 : ∀ j : Fin 63,
    let w : Fin 63 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 63,
      let w : Fin 63 := ⟨0 + j.val,by omega⟩
      target w < MatroidCatalogue.count 8 4 ∧
        Papers.RationalityTen.MatroidChecked.FastSemanticChecks.RawWitness 8 (N7R4.familyMasks.get 18)
        (fun i : Fin 70 => N8R4.gridMasks.get i.val) newIndex (models w)
        (N8R4.familyMasks.get (target w)) (permutation w) := by
    refine (Fin.forall_fin_add (m := 31) (n := 32) _).2 ⟨?_, ?_⟩
    · refine (Fin.forall_fin_add (m := 15) (n := 16) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 7) (n := 8) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 3) (n := 4) _).2 ⟨?_, ?_⟩
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


end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C18

/- Source: MatroidCatalogue/Cases/N8R4C18Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C18

noncomputable def certificates : List (Origin 70 63 × List Sat.Literal) :=
  certificates_0 ++ certificates_1 ++ certificates_2

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  intro oc hoc
  simp only [certificates,List.mem_append,or_assoc] at hoc
  rcases hoc with h0 | h1 | h2
  · exact certificates_0_valid oc h0
  · exact certificates_1_valid oc h1
  · exact certificates_2_valid oc h2

theorem models_valid : ∀ w : Fin 63,
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 63) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 8) 4)
    (hold : M.bases.filter ((7 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 8 4, IsomorphicWithin 8 M.bases B := by
  apply extension_covered_of_certificate (n:=7) (r:=4) (by decide)
    catalogue old U newIndex models certificates
    N8R4.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C18.formula []
    exact Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C18.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 8 4 (target w),family_mem 8 4 (target w) hw.1,?_⟩
    exact validWitness_sound 8 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C18


end
end
end BundlePart4

section BundlePart5
/- Source: MatroidChecked/SemanticChunks/Cases03Part05.lean -/




@[expose] public section
noncomputable section

/- Source: MatroidCatalogue/Cases/N8R4C19Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C19

abbrev U := N8R4.grid
noncomputable def old : Finset (Finset (Fin 8)) := N7R4.family 19
noncomputable def newIndexTree : Table ℕ := (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf 35) (.leaf 36)) (.node 3 (.leaf 37) (.leaf 38))) (.node 6 (.node 5 (.leaf 39) (.leaf 40)) (.node 7 (.leaf 41) (.leaf 42)))) (.node 12 (.node 10 (.node 9 (.leaf 43) (.leaf 44)) (.node 11 (.leaf 45) (.leaf 46))) (.node 14 (.node 13 (.leaf 47) (.leaf 48)) (.node 15 (.leaf 49) (.node 16 (.leaf 50) (.leaf 51)))))) (.node 26 (.node 21 (.node 19 (.node 18 (.leaf 52) (.leaf 53)) (.node 20 (.leaf 54) (.leaf 55))) (.node 23 (.node 22 (.leaf 56) (.leaf 57)) (.node 24 (.leaf 58) (.node 25 (.leaf 59) (.leaf 60))))) (.node 30 (.node 28 (.node 27 (.leaf 61) (.leaf 62)) (.node 29 (.leaf 63) (.leaf 64))) (.node 32 (.node 31 (.leaf 65) (.leaf 66)) (.node 33 (.leaf 67) (.node 34 (.leaf 68) (.leaf 69)))))))
noncomputable def newIndex (i : Fin 35) : Fin 70 := Fin.ofNat 70 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (32921092096,38,4151056)) (.leaf (27751612416,38,4122370))) (.node 3 (.leaf (7992246272,38,4112794)) (.leaf (34332475392,48,8308104)))) (.node 6 (.node 5 (.leaf (27540848640,38,4111394)) (.leaf (7580155904,38,4098290))) (.node 7 (.leaf (34021048320,48,8300656)) (.node 8 (.leaf (531628032,38,3954902)) (.leaf (27912044544,48,8214598)))))) (.node 13 (.node 11 (.node 10 (.leaf (8052015104,48,8196454)) (.leaf (33117175808,56,14599816))) (.node 12 (.leaf (34190917632,57,14595140)) (.leaf (33251393536,57,14537824)))) (.node 15 (.node 14 (.leaf (34325135360,58,14598682)) (.leaf (33150730240,57,14527240))) (.node 16 (.leaf (34224472064,58,14588098)) (.node 17 (.leaf (33284947968,58,14473424)) (.leaf (34358689792,59,14599816))))))) (.node 27 (.node 22 (.node 20 (.node 19 (.leaf (520157,181,2223970)) (.leaf (32921612253,182,16434824))) (.node 21 (.leaf (27752132573,182,16406145)) (.leaf (7992766429,182,16392537)))) (.node 24 (.node 23 (.leaf (34332995549,183,16434376)) (.leaf (27541368797,182,16398865))) (.node 25 (.leaf (7580676061,182,16385257)) (.node 26 (.leaf (34021568477,183,16427096)) (.leaf (532148189,182,16270541)))))) (.node 32 (.node 29 (.node 28 (.leaf (27912564701,183,16341059)) (.leaf (8052535261,183,16322915))) (.node 30 (.leaf (33117695965,184,16434824)) (.node 31 (.leaf (34191437789,185,16430148)) (.leaf (33251913693,185,16372832))))) (.node 34 (.node 33 (.leaf (34325655517,186,16433690)) (.leaf (33151250397,185,16362248))) (.node 35 (.leaf (34224992221,186,16423106)) (.node 36 (.leaf (33285468125,186,16308432)) (.leaf (34359209949,187,16434824))))))))

noncomputable def models (i : Fin 37) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 37) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 37) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 70, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (7 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 70, (7 : Fin 8) ∈ U i → ∃ j : Fin 35, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C19

/- Source: MatroidCatalogue/Cases/N8R4C19Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C19


noncomputable def certificates_0 : List (Origin 70 37 × List Sat.Literal) :=
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
   ((.fixed 34),[(.neg 34)]),
   ((.exchange 15 41 6),[(.neg 41),(.neg 15),(.pos 1),(.pos 35)]),
   ((.exchange 15 58 2),[(.neg 58),(.neg 15),(.pos 16),(.pos 55)]),
   ((.exchange 15 59 2),[(.neg 59),(.neg 15),(.pos 16),(.pos 55)]),
   ((.exchange 15 61 1),[(.neg 61),(.neg 15),(.pos 20),(.pos 56)]),
   ((.exchange 15 63 1),[(.neg 63),(.neg 15),(.pos 20),(.pos 56)]),
   ((.exchange 15 66 0),[(.neg 66),(.neg 15),(.pos 27),(.pos 57)]),
   ((.exchange 15 67 0),[(.neg 67),(.neg 15),(.pos 27),(.pos 57)]),
   ((.exchange 17 41 6),[(.neg 41),(.neg 17),(.pos 0),(.pos 3),(.pos 37)]),
   ((.exchange 17 55 2),[(.neg 55),(.neg 17),(.pos 16),(.pos 58)]),
   ((.exchange 18 41 6),[(.neg 41),(.neg 18),(.pos 4),(.pos 38)]),
   ((.exchange 18 55 2),[(.neg 55),(.neg 18),(.pos 16),(.pos 59)]),
   ((.exchange 19 41 6),[(.neg 41),(.neg 19),(.pos 1),(.pos 39)]),
   ((.exchange 19 56 1),[(.neg 56),(.neg 19),(.pos 20),(.pos 61)]),
   ((.exchange 21 35 6),[(.neg 35),(.neg 21),(.pos 1),(.pos 41)]),
   ((.exchange 21 37 6),[(.neg 37),(.neg 21),(.pos 1),(.pos 4),(.pos 41)]),
   ((.exchange 21 38 6),[(.neg 38),(.neg 21),(.pos 4),(.pos 41)]),
   ((.exchange 21 39 6),[(.neg 39),(.neg 21),(.pos 1),(.pos 41)]),
   ((.exchange 21 42 6),[(.neg 42),(.neg 21),(.pos 1),(.pos 4),(.pos 41)]),
   ((.exchange 21 43 6),[(.neg 43),(.neg 21),(.pos 4),(.pos 41)]),
   ((.exchange 21 44 6),[(.neg 44),(.neg 21),(.pos 4),(.pos 41)]),
   ((.exchange 21 45 6),[(.neg 45),(.neg 21),(.pos 1),(.pos 11),(.pos 41)]),
   ((.exchange 21 46 6),[(.neg 46),(.neg 21),(.pos 1),(.pos 11),(.pos 41)]),
   ((.exchange 21 48 6),[(.neg 48),(.neg 21),(.pos 1),(.pos 4),(.pos 11),(.pos 41)]),
   ((.exchange 21 49 6),[(.neg 49),(.neg 21),(.pos 4),(.pos 11),(.pos 41)]),
   ((.exchange 21 50 6),[(.neg 50),(.neg 21),(.pos 4),(.pos 11),(.pos 41)]),
   ((.exchange 21 51 6),[(.neg 51),(.neg 21),(.pos 1),(.pos 11),(.pos 41)]),
   ((.exchange 21 52 6),[(.neg 52),(.neg 21),(.pos 11),(.pos 41)]),
   ((.exchange 21 53 6),[(.neg 53),(.neg 21),(.pos 11),(.pos 41)]),
   ((.exchange 21 56 1),[(.neg 56),(.neg 21),(.pos 20),(.pos 63)]),
   ((.exchange 22 41 6),[(.neg 41),(.neg 22),(.pos 2),(.pos 3),(.pos 42)]),
   ((.exchange 22 68 0),[(.neg 68),(.neg 22),(.pos 34),(.pos 64)]),
   ((.exchange 22 69 0),[(.neg 69),(.neg 22),(.pos 34),(.pos 64)]),
   ((.exchange 23 41 6),[(.neg 41),(.neg 23),(.pos 4),(.pos 43)]),
   ((.exchange 24 41 6),[(.neg 41),(.neg 24),(.pos 4),(.pos 44)]),
   ((.exchange 25 41 6),[(.neg 41),(.neg 25),(.pos 5),(.pos 9),(.pos 45)]),
   ((.exchange 25 57 0),[(.neg 57),(.neg 25),(.pos 27),(.pos 66)]),
   ((.exchange 25 67 0),[(.neg 67),(.neg 25),(.pos 27),(.pos 66)]),
   ((.exchange 26 41 6),[(.neg 41),(.neg 26),(.pos 5),(.pos 10),(.pos 46)]),
   ((.exchange 26 57 0),[(.neg 57),(.neg 26),(.pos 27),(.pos 67)]),
   ((.exchange 26 66 0),[(.neg 66),(.neg 26),(.pos 27),(.pos 67)]),
   ((.exchange 28 41 6),[(.neg 41),(.neg 28),(.pos 6),(.pos 7),(.pos 12),(.pos 48)]),
   ((.exchange 28 64 0),[(.neg 64),(.neg 28),(.pos 34),(.pos 68)]),
   ((.exchange 28 69 0),[(.neg 69),(.neg 28),(.pos 34),(.pos 68)]),
   ((.exchange 29 41 6),[(.neg 41),(.neg 29),(.pos 8),(.pos 13),(.pos 49)]),
   ((.exchange 30 41 6),[(.neg 41),(.neg 30),(.pos 8),(.pos 14),(.pos 50)]),
   ((.exchange 31 41 6),[(.neg 41),(.neg 31),(.pos 9),(.pos 10),(.pos 51)]),
   ((.exchange 31 64 0),[(.neg 64),(.neg 31),(.pos 34),(.pos 69)]),
   ((.exchange 31 68 0),[(.neg 68),(.neg 31),(.pos 34),(.pos 69)]),
   ((.exchange 32 41 6),[(.neg 41),(.neg 32),(.pos 11),(.pos 52)]),
   ((.exchange 33 41 6),[(.neg 41),(.neg 33),(.pos 11),(.pos 53)]),
   ((.exchange 36 15 7),[(.neg 36),(.neg 15),(.pos 0),(.pos 16)]),
   ((.exchange 40 15 7),[(.neg 40),(.neg 15),(.pos 1),(.pos 20)]),
   ((.exchange 47 15 7),[(.neg 47),(.neg 15),(.pos 5),(.pos 27)]),
   ((.exchange 54 15 7),[(.neg 54),(.neg 15),(.pos 12),(.pos 13),(.pos 14),(.pos 34)]),
   ((.exchange 55 21 0),[(.neg 55),(.neg 21),(.pos 57),(.pos 62)]),
   ((.exchange 55 26 1),[(.neg 55),(.neg 26),(.pos 56),(.pos 65)]),
   ((.exchange 55 53 1),[(.neg 55),(.neg 53),(.pos 56),(.pos 61),(.pos 65)]),
   ((.exchange 56 18 0),[(.neg 56),(.neg 18),(.pos 57),(.pos 60)]),
   ((.exchange 56 25 2),[(.neg 56),(.neg 25),(.pos 55),(.pos 65)]),
   ((.exchange 56 59 0),[(.neg 59),(.neg 56),(.pos 57),(.pos 60)]),
   ((.exchange 56 68 0),[(.neg 68),(.neg 56),(.pos 60),(.pos 67)]),
   ((.exchange 57 19 2),[(.neg 57),(.neg 19),(.pos 55),(.pos 62)]),
   ((.exchange 57 37 1),[(.neg 57),(.neg 37),(.pos 56),(.pos 60)]),
   ((.exchange 57 43 2),[(.neg 57),(.neg 43),(.pos 59),(.pos 62)]),
   ((.exchange 57 58 1),[(.neg 58),(.neg 57),(.pos 56),(.pos 60)]),
   ((.exchange 58 24 0),[(.neg 58),(.neg 24),(.pos 60),(.pos 64)]),
   ((.exchange 58 30 0),[(.neg 58),(.neg 30),(.pos 60),(.pos 68)]),
   ((.exchange 59 21 3),[(.neg 59),(.neg 21),(.pos 57),(.pos 62)]),
   ((.exchange 59 30 1),[(.neg 59),(.neg 30),(.pos 60),(.pos 68)]),
   ((.exchange 59 32 3),[(.neg 59),(.neg 32),(.pos 62),(.pos 66)]),
   ((.exchange 59 50 1),[(.neg 59),(.neg 50),(.pos 60),(.pos 68)]),
   ((.exchange 59 52 3),[(.neg 59),(.neg 52),(.pos 62),(.pos 66)]),
   ((.exchange 59 69 3),[(.neg 69),(.neg 59),(.pos 62),(.pos 66)]),
   ((.exchange 60 19 2),[(.neg 60),(.neg 19),(.pos 58),(.pos 59),(.pos 64)]),
   ((.exchange 60 21 3),[(.neg 60),(.neg 21),(.pos 57),(.pos 63)]),
   ((.exchange 60 23 2),[(.neg 60),(.neg 23),(.pos 59),(.pos 64)]),
   ((.exchange 60 26 3),[(.neg 60),(.neg 26),(.pos 56),(.pos 67)]),
   ((.exchange 60 31 2),[(.neg 60),(.neg 31),(.pos 58),(.pos 64),(.pos 68)]),
   ((.exchange 60 55 3),[(.neg 60),(.neg 55),(.pos 56),(.pos 57)]),
   ((.exchange 60 65 3),[(.neg 65),(.neg 60),(.pos 56),(.pos 67)]),
   ((.exchange 61 23 0),[(.neg 61),(.neg 23),(.pos 62),(.pos 64)]),
   ((.exchange 61 25 4),[(.neg 61),(.neg 25),(.pos 55),(.pos 65)]),
   ((.exchange 61 59 0),[(.neg 61),(.neg 59),(.pos 62),(.pos 64)]),
   ((.exchange 62 17 1),[(.neg 62),(.neg 17),(.pos 61),(.pos 63),(.pos 64)]),
   ((.exchange 62 18 4),[(.neg 62),(.neg 18),(.pos 57),(.pos 59)]),
   ((.exchange 62 33 1),[(.neg 62),(.neg 33),(.pos 63),(.pos 69)]),
   ((.exchange 62 58 1),[(.neg 62),(.neg 58),(.pos 61),(.pos 64)]),
   ((.exchange 62 65 4),[(.neg 65),(.neg 62),(.pos 55),(.pos 66)]),
   ((.exchange 62 67 1),[(.neg 67),(.neg 62),(.pos 63),(.pos 69)]),
   ((.exchange 63 32 2),[(.neg 63),(.neg 32),(.pos 62),(.pos 69)]),
   ((.exchange 63 59 2),[(.neg 63),(.neg 59),(.pos 62),(.pos 64)]),
   ((.exchange 64 15 4),[(.neg 64),(.neg 15),(.pos 58),(.pos 59),(.pos 60)]),
   ((.exchange 64 35 4),[(.neg 64),(.neg 35),(.pos 58),(.pos 59),(.pos 60)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_1 : List (Origin 70 37 × List Sat.Literal) :=
  [((.exchange 64 55 3),[(.neg 64),(.neg 55),(.pos 61),(.pos 62)]),
   ((.exchange 65 15 5),[(.neg 65),(.neg 15),(.pos 55),(.pos 56)]),
   ((.exchange 65 21 0),[(.neg 65),(.neg 21),(.pos 66),(.pos 67),(.pos 69)]),
   ((.exchange 65 24 0),[(.neg 65),(.neg 24),(.pos 67),(.pos 68),(.pos 69)]),
   ((.exchange 65 29 0),[(.neg 65),(.neg 29),(.pos 66),(.pos 68)]),
   ((.exchange 65 32 0),[(.neg 65),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 65 33 0),[(.neg 65),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 65 43 5),[(.neg 65),(.neg 43),(.pos 55),(.pos 58),(.pos 61)]),
   ((.exchange 65 52 0),[(.neg 65),(.neg 52),(.pos 66),(.pos 69)]),
   ((.exchange 65 59 0),[(.neg 65),(.neg 59),(.pos 66),(.pos 68)]),
   ((.exchange 66 23 5),[(.neg 66),(.neg 23),(.pos 59),(.pos 62)]),
   ((.exchange 66 51 1),[(.neg 66),(.neg 51),(.pos 65),(.pos 69)]),
   ((.exchange 67 17 5),[(.neg 67),(.neg 17),(.pos 56),(.pos 60)]),
   ((.exchange 67 28 2),[(.neg 67),(.neg 28),(.pos 65),(.pos 68)]),
   ((.exchange 67 31 2),[(.neg 67),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 67 51 2),[(.neg 67),(.neg 51),(.pos 65),(.pos 69)]),
   ((.exchange 67 58 2),[(.neg 67),(.neg 58),(.pos 65),(.pos 68)]),
   ((.exchange 67 58 5),[(.neg 67),(.neg 58),(.pos 56),(.pos 60)]),
   ((.exchange 67 61 2),[(.neg 67),(.neg 61),(.pos 65),(.pos 69)]),
   ((.exchange 68 26 3),[(.neg 68),(.neg 26),(.pos 65),(.pos 67)]),
   ((.exchange 69 30 4),[(.neg 69),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 69 35 5),[(.neg 69),(.neg 35),(.pos 61),(.pos 62),(.pos 63)]),
   ((.exchange 69 45 4),[(.neg 69),(.neg 45),(.pos 65),(.pos 66)]),
   ((.exchange 69 46 4),[(.neg 69),(.neg 46),(.pos 65),(.pos 67)]),
   ((.exchange 69 55 4),[(.neg 69),(.neg 55),(.pos 65),(.pos 66)]),
   ((.exchange 69 55 5),[(.neg 69),(.neg 55),(.pos 61),(.pos 62)]),
   ((.exchange 69 56 4),[(.neg 69),(.neg 56),(.pos 65),(.pos 67)]),
   (.newPoint,[(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 0),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 62),(.neg 60),(.neg 57),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 58),(.pos 59),(.pos 61),(.pos 63),(.pos 65)]),
   ((.excluded 1),[(.neg 69),(.neg 68),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 57),(.pos 58),(.pos 59),(.pos 62),(.pos 66),(.pos 67)]),
   ((.excluded 2),[(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 68),(.pos 69)]),
   ((.excluded 3),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 58),(.pos 59)]),
   ((.excluded 4),[(.neg 69),(.neg 68),(.neg 65),(.neg 64),(.neg 62),(.neg 59),(.neg 58),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 56),(.pos 57),(.pos 60),(.pos 61),(.pos 63),(.pos 66),(.pos 67)]),
   ((.excluded 5),[(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 56),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 68),(.pos 69)]),
   ((.excluded 6),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 56),(.pos 61),(.pos 63)]),
   ((.excluded 7),[(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 57),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 8),[(.neg 69),(.neg 68),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 57),(.pos 66),(.pos 67)]),
   ((.excluded 9),[(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 64),(.pos 68),(.pos 69)]),
   ((.excluded 10),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 60),(.pos 62),(.pos 65)]),
   ((.excluded 11),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 60),(.pos 62)]),
   ((.excluded 12),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 60),(.pos 65)]),
   ((.excluded 13),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 60)]),
   ((.excluded 14),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 62),(.pos 65)]),
   ((.excluded 15),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 62)]),
   ((.excluded 16),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 65)]),
   ((.excluded 17),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54)]),
   ((.excluded 18),[(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 19),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 62),(.neg 60),(.neg 57),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 54),(.pos 55),(.pos 56),(.pos 58),(.pos 59),(.pos 61),(.pos 63),(.pos 65)]),
   ((.excluded 20),[(.neg 69),(.neg 68),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 54),(.pos 55),(.pos 57),(.pos 58),(.pos 59),(.pos 62),(.pos 66),(.pos 67)]),
   ((.excluded 21),[(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 54),(.pos 55),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 68),(.pos 69)]),
   ((.excluded 22),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 54),(.pos 55),(.pos 58),(.pos 59)]),
   ((.excluded 23),[(.neg 69),(.neg 68),(.neg 65),(.neg 64),(.neg 62),(.neg 59),(.neg 58),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 54),(.pos 56),(.pos 57),(.pos 60),(.pos 61),(.pos 63),(.pos 66),(.pos 67)]),
   ((.excluded 24),[(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 54),(.pos 56),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 68),(.pos 69)]),
   ((.excluded 25),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 54),(.pos 56),(.pos 61),(.pos 63)]),
   ((.excluded 26),[(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 54),(.pos 57),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 27),[(.neg 69),(.neg 68),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 54),(.pos 57),(.pos 66),(.pos 67)]),
   ((.excluded 28),[(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 54),(.pos 64),(.pos 68),(.pos 69)]),
   ((.excluded 29),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 54),(.pos 60),(.pos 62),(.pos 65)]),
   ((.excluded 30),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 54),(.pos 60),(.pos 62)]),
   ((.excluded 31),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 54),(.pos 60),(.pos 65)]),
   ((.excluded 32),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 54),(.pos 60)]),
   ((.excluded 33),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 54),(.pos 62),(.pos 65)]),
   ((.excluded 34),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 54),(.pos 62)]),
   ((.excluded 35),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 54),(.pos 65)]),
   ((.excluded 36),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 54)])]

theorem certificates_1_valid : ∀ oc ∈ certificates_1,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



theorem witness_0 : ∀ j : Fin 37,
    let w : Fin 37 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 37,
      let w : Fin 37 := ⟨0 + j.val,by omega⟩
      target w < MatroidCatalogue.count 8 4 ∧
        Papers.RationalityTen.MatroidChecked.FastSemanticChecks.RawWitness 8 (N7R4.familyMasks.get 19)
        (fun i : Fin 70 => N8R4.gridMasks.get i.val) newIndex (models w)
        (N8R4.familyMasks.get (target w)) (permutation w) := by
    refine (Fin.forall_fin_add (m := 18) (n := 19) _).2 ⟨?_, ?_⟩
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
  intro j
  have hj := hfast j
  exact ⟨hj.1,Papers.RationalityTen.MatroidChecked.FastSemanticChecks.rawWitness_sound 8 _ _ _ _ _ _ hj.2⟩


end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C19

/- Source: MatroidCatalogue/Cases/N8R4C19Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C19

noncomputable def certificates : List (Origin 70 37 × List Sat.Literal) :=
  certificates_0 ++ certificates_1

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  intro oc hoc
  simp only [certificates,List.mem_append,or_assoc] at hoc
  rcases hoc with h0 | h1
  · exact certificates_0_valid oc h0
  · exact certificates_1_valid oc h1

theorem models_valid : ∀ w : Fin 37,
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 37) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 8) 4)
    (hold : M.bases.filter ((7 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 8 4, IsomorphicWithin 8 M.bases B := by
  apply extension_covered_of_certificate (n:=7) (r:=4) (by decide)
    catalogue old U newIndex models certificates
    N8R4.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C19.formula []
    exact Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C19.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 8 4 (target w),family_mem 8 4 (target w) hw.1,?_⟩
    exact validWitness_sound 8 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C19


end
end
end BundlePart5

section BundlePart6
/- Source: MatroidChecked/SemanticChunks/Cases03Part06.lean -/




@[expose] public section
noncomputable section

/- Source: MatroidCatalogue/Cases/N8R4C20Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C20

abbrev U := N8R4.grid
noncomputable def old : Finset (Finset (Fin 8)) := N7R4.family 20
noncomputable def newIndexTree : Table ℕ := (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf 35) (.leaf 36)) (.node 3 (.leaf 37) (.leaf 38))) (.node 6 (.node 5 (.leaf 39) (.leaf 40)) (.node 7 (.leaf 41) (.leaf 42)))) (.node 12 (.node 10 (.node 9 (.leaf 43) (.leaf 44)) (.node 11 (.leaf 45) (.leaf 46))) (.node 14 (.node 13 (.leaf 47) (.leaf 48)) (.node 15 (.leaf 49) (.node 16 (.leaf 50) (.leaf 51)))))) (.node 26 (.node 21 (.node 19 (.node 18 (.leaf 52) (.leaf 53)) (.node 20 (.leaf 54) (.leaf 55))) (.node 23 (.node 22 (.leaf 56) (.leaf 57)) (.node 24 (.leaf 58) (.node 25 (.leaf 59) (.leaf 60))))) (.node 30 (.node 28 (.node 27 (.leaf 61) (.leaf 62)) (.node 29 (.leaf 63) (.leaf 64))) (.node 32 (.node 31 (.leaf 65) (.leaf 66)) (.node 33 (.leaf 67) (.node 34 (.leaf 68) (.leaf 69)))))))
noncomputable def newIndex (i : Fin 35) : Fin 70 := Fin.ofNat 70 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 26 (.node 13 (.node 6 (.node 3 (.node 1 (.leaf (32921092096,39,4151504)) (.node 2 (.leaf (27751612416,39,4122818)) (.leaf (25172115456,42,4120858)))) (.node 4 (.leaf (17152606208,48,6211464)) (.node 5 (.leaf (34332475392,49,8316168)) (.leaf (27540848640,39,4115482))))) (.node 9 (.node 7 (.leaf (16170090496,42,4099298)) (.node 8 (.leaf (25431113728,48,6207600)) (.leaf (34021048320,49,8301664)))) (.node 11 (.node 10 (.leaf (1068498944,42,3955924)) (.leaf (27375173632,48,6150214))) (.node 12 (.leaf (27912044544,49,8215620)) (.leaf (32748077056,60,8345736)))))) (.node 19 (.node 16 (.node 14 (.leaf (33821818880,61,12535362)) (.node 15 (.leaf (25634537472,60,8317057)) (.leaf (25768755200,61,12478032)))) (.node 17 (.leaf (17145266176,60,8309777)) (.node 18 (.leaf (17178820608,61,12467336)) (.leaf (33117175808,57,8342152))))) (.node 22 (.node 20 (.leaf (34190917632,58,12531778)) (.node 21 (.leaf (33251393536,58,12445776)) (.leaf (34325135360,62,12477969)))) (.node 24 (.node 23 (.leaf (33150730240,58,12438664)) (.leaf (34224472064,62,12467329))) (.node 25 (.leaf (33284947968,62,12438664)) (.leaf (34358689792,63,14599816))))))) (.node 39 (.node 32 (.node 29 (.node 27 (.leaf (1044445,188,9367176)) (.node 28 (.leaf (32922136541,189,16434824)) (.leaf (27752656861,189,16406145)))) (.node 30 (.leaf (25173159901,190,16433361)) (.node 31 (.leaf (17153650653,191,16434376)) (.leaf (34333519837,192,16434376))))) (.node 35 (.node 33 (.leaf (27541893085,189,16398865)) (.node 34 (.leaf (16171134941,190,16418969)) (.leaf (25432158173,191,16427096)))) (.node 37 (.node 36 (.leaf (34022092765,192,16427096)) (.leaf (1069543389,190,16275595))) (.node 38 (.leaf (27376218077,191,16341059)) (.leaf (27913088989,192,16341059)))))) (.node 46 (.node 42 (.node 40 (.leaf (32749121501,193,16434824)) (.node 41 (.leaf (33822863325,194,16434824)) (.leaf (25635581917,193,16406145)))) (.node 44 (.node 43 (.leaf (25769799645,194,16406145)) (.leaf (17146310621,193,16398865))) (.node 45 (.leaf (17179865053,194,16398865)) (.leaf (33118220253,195,16434824))))) (.node 49 (.node 47 (.leaf (34191962077,196,16434754)) (.node 48 (.leaf (33252437981,196,16406096)) (.leaf (34326179805,197,16434705)))) (.node 51 (.node 50 (.leaf (33151774685,196,16398984)) (.leaf (34225516509,197,16431233))) (.node 52 (.leaf (33285992413,197,16373896)) (.leaf (34359734237,198,16434824))))))))

noncomputable def models (i : Fin 53) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 53) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 53) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 70, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (7 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 70, (7 : Fin 8) ∈ U i → ∃ j : Fin 35, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C20

/- Source: MatroidCatalogue/Cases/N8R4C20Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C20


noncomputable def certificates_0 : List (Origin 70 53 × List Sat.Literal) :=
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
   ((.exchange 15 41 6),[(.neg 41),(.neg 15),(.pos 1),(.pos 35)]),
   ((.exchange 15 58 2),[(.neg 58),(.neg 15),(.pos 16),(.pos 55)]),
   ((.exchange 15 59 2),[(.neg 59),(.neg 15),(.pos 16),(.pos 55)]),
   ((.exchange 15 61 1),[(.neg 61),(.neg 15),(.pos 20),(.pos 56)]),
   ((.exchange 15 63 1),[(.neg 63),(.neg 15),(.pos 20),(.pos 56)]),
   ((.exchange 15 66 0),[(.neg 66),(.neg 15),(.pos 27),(.pos 57)]),
   ((.exchange 15 67 0),[(.neg 67),(.neg 15),(.pos 27),(.pos 57)]),
   ((.exchange 17 41 6),[(.neg 41),(.neg 17),(.pos 0),(.pos 3),(.pos 37)]),
   ((.exchange 17 55 2),[(.neg 55),(.neg 17),(.pos 16),(.pos 58)]),
   ((.exchange 18 41 6),[(.neg 41),(.neg 18),(.pos 4),(.pos 38)]),
   ((.exchange 18 55 2),[(.neg 55),(.neg 18),(.pos 16),(.pos 59)]),
   ((.exchange 19 41 6),[(.neg 41),(.neg 19),(.pos 1),(.pos 39)]),
   ((.exchange 19 56 1),[(.neg 56),(.neg 19),(.pos 20),(.pos 61)]),
   ((.exchange 21 35 6),[(.neg 35),(.neg 21),(.pos 1),(.pos 41)]),
   ((.exchange 21 37 6),[(.neg 37),(.neg 21),(.pos 1),(.pos 4),(.pos 41)]),
   ((.exchange 21 38 6),[(.neg 38),(.neg 21),(.pos 4),(.pos 41)]),
   ((.exchange 21 39 6),[(.neg 39),(.neg 21),(.pos 1),(.pos 41)]),
   ((.exchange 21 42 6),[(.neg 42),(.neg 21),(.pos 1),(.pos 4),(.pos 41)]),
   ((.exchange 21 43 6),[(.neg 43),(.neg 21),(.pos 4),(.pos 41)]),
   ((.exchange 21 44 6),[(.neg 44),(.neg 21),(.pos 4),(.pos 41)]),
   ((.exchange 21 45 6),[(.neg 45),(.neg 21),(.pos 1),(.pos 11),(.pos 41)]),
   ((.exchange 21 46 6),[(.neg 46),(.neg 21),(.pos 1),(.pos 11),(.pos 41)]),
   ((.exchange 21 48 6),[(.neg 48),(.neg 21),(.pos 1),(.pos 4),(.pos 11),(.pos 41)]),
   ((.exchange 21 49 6),[(.neg 49),(.neg 21),(.pos 4),(.pos 11),(.pos 41)]),
   ((.exchange 21 50 6),[(.neg 50),(.neg 21),(.pos 4),(.pos 11),(.pos 41)]),
   ((.exchange 21 51 6),[(.neg 51),(.neg 21),(.pos 1),(.pos 11),(.pos 41)]),
   ((.exchange 21 52 6),[(.neg 52),(.neg 21),(.pos 11),(.pos 41)]),
   ((.exchange 21 53 6),[(.neg 53),(.neg 21),(.pos 11),(.pos 41)]),
   ((.exchange 21 54 6),[(.neg 54),(.neg 21),(.pos 4),(.pos 11),(.pos 41)]),
   ((.exchange 21 56 1),[(.neg 56),(.neg 21),(.pos 20),(.pos 63)]),
   ((.exchange 22 41 6),[(.neg 41),(.neg 22),(.pos 2),(.pos 3),(.pos 42)]),
   ((.exchange 23 41 6),[(.neg 41),(.neg 23),(.pos 4),(.pos 43)]),
   ((.exchange 24 41 6),[(.neg 41),(.neg 24),(.pos 4),(.pos 44)]),
   ((.exchange 25 41 6),[(.neg 41),(.neg 25),(.pos 5),(.pos 9),(.pos 45)]),
   ((.exchange 25 57 0),[(.neg 57),(.neg 25),(.pos 27),(.pos 66)]),
   ((.exchange 25 67 0),[(.neg 67),(.neg 25),(.pos 27),(.pos 66)]),
   ((.exchange 26 41 6),[(.neg 41),(.neg 26),(.pos 5),(.pos 10),(.pos 46)]),
   ((.exchange 26 57 0),[(.neg 57),(.neg 26),(.pos 27),(.pos 67)]),
   ((.exchange 26 66 0),[(.neg 66),(.neg 26),(.pos 27),(.pos 67)]),
   ((.exchange 28 41 6),[(.neg 41),(.neg 28),(.pos 6),(.pos 7),(.pos 12),(.pos 48)]),
   ((.exchange 29 41 6),[(.neg 41),(.neg 29),(.pos 8),(.pos 13),(.pos 49)]),
   ((.exchange 30 41 6),[(.neg 41),(.neg 30),(.pos 8),(.pos 14),(.pos 50)]),
   ((.exchange 31 41 6),[(.neg 41),(.neg 31),(.pos 9),(.pos 10),(.pos 51)]),
   ((.exchange 32 41 6),[(.neg 41),(.neg 32),(.pos 11),(.pos 52)]),
   ((.exchange 33 41 6),[(.neg 41),(.neg 33),(.pos 11),(.pos 53)]),
   ((.exchange 34 41 6),[(.neg 41),(.neg 34),(.pos 13),(.pos 14),(.pos 54)]),
   ((.exchange 36 15 7),[(.neg 36),(.neg 15),(.pos 0),(.pos 16)]),
   ((.exchange 40 15 7),[(.neg 40),(.neg 15),(.pos 1),(.pos 20)]),
   ((.exchange 47 15 7),[(.neg 47),(.neg 15),(.pos 5),(.pos 27)]),
   ((.exchange 55 21 0),[(.neg 55),(.neg 21),(.pos 57),(.pos 62)]),
   ((.exchange 55 26 1),[(.neg 55),(.neg 26),(.pos 56),(.pos 65)]),
   ((.exchange 55 32 0),[(.neg 55),(.neg 32),(.pos 62),(.pos 66)]),
   ((.exchange 55 53 1),[(.neg 55),(.neg 53),(.pos 56),(.pos 61),(.pos 65)]),
   ((.exchange 56 25 2),[(.neg 56),(.neg 25),(.pos 55),(.pos 65)]),
   ((.exchange 57 19 2),[(.neg 57),(.neg 19),(.pos 55),(.pos 62)]),
   ((.exchange 57 24 1),[(.neg 57),(.neg 24),(.pos 60),(.pos 63)]),
   ((.exchange 57 61 2),[(.neg 61),(.neg 57),(.pos 55),(.pos 62)]),
   ((.exchange 58 24 0),[(.neg 58),(.neg 24),(.pos 60),(.pos 64)]),
   ((.exchange 58 30 0),[(.neg 58),(.neg 30),(.pos 60),(.pos 68)]),
   ((.exchange 58 67 0),[(.neg 67),(.neg 58),(.pos 60),(.pos 68)]),
   ((.exchange 59 21 3),[(.neg 59),(.neg 21),(.pos 57),(.pos 62)]),
   ((.exchange 59 30 1),[(.neg 59),(.neg 30),(.pos 60),(.pos 68)]),
   ((.exchange 59 34 1),[(.neg 59),(.neg 34),(.pos 64),(.pos 68)]),
   ((.exchange 59 54 1),[(.neg 59),(.neg 54),(.pos 64),(.pos 68)]),
   ((.exchange 60 19 2),[(.neg 60),(.neg 19),(.pos 58),(.pos 59),(.pos 64)]),
   ((.exchange 60 26 3),[(.neg 60),(.neg 26),(.pos 56),(.pos 67)]),
   ((.exchange 60 28 2),[(.neg 60),(.neg 28),(.pos 58),(.pos 68)]),
   ((.exchange 60 53 3),[(.neg 60),(.neg 53),(.pos 63),(.pos 67)]),
   ((.exchange 60 55 3),[(.neg 60),(.neg 55),(.pos 56),(.pos 57)]),
   ((.exchange 60 66 2),[(.neg 66),(.neg 60),(.pos 59),(.pos 68)]),
   ((.exchange 60 69 3),[(.neg 69),(.neg 60),(.pos 63),(.pos 67)]),
   ((.exchange 61 23 0),[(.neg 61),(.neg 23),(.pos 62),(.pos 64)]),
   ((.exchange 61 25 4),[(.neg 61),(.neg 25),(.pos 55),(.pos 65)]),
   ((.exchange 61 34 0),[(.neg 61),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 62 17 1),[(.neg 62),(.neg 17),(.pos 61),(.pos 63),(.pos 64)]),
   ((.exchange 62 18 4),[(.neg 62),(.neg 18),(.pos 57),(.pos 59)]),
   ((.exchange 62 26 1),[(.neg 62),(.neg 26),(.pos 61),(.pos 63),(.pos 69)]),
   ((.exchange 62 33 1),[(.neg 62),(.neg 33),(.pos 63),(.pos 69)]),
   ((.exchange 62 34 1),[(.neg 62),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 62 56 4),[(.neg 62),(.neg 56),(.pos 55),(.pos 57)]),
   ((.exchange 62 60 1),[(.neg 62),(.neg 60),(.pos 63),(.pos 64)]),
   ((.exchange 63 32 2),[(.neg 63),(.neg 32),(.pos 62),(.pos 69)]),
   ((.exchange 63 34 2),[(.neg 63),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 63 50 4),[(.neg 63),(.neg 50),(.pos 60),(.pos 67)]),
   ((.exchange 63 68 4),[(.neg 68),(.neg 63),(.pos 60),(.pos 67)]),
   ((.exchange 64 21 3),[(.neg 64),(.neg 21),(.pos 62),(.pos 63)]),
   ((.exchange 64 28 4),[(.neg 64),(.neg 28),(.pos 58),(.pos 68)]),
   ((.exchange 64 33 3),[(.neg 64),(.neg 33),(.pos 63),(.pos 69)]),
   ((.exchange 64 35 4),[(.neg 64),(.neg 35),(.pos 58),(.pos 59),(.pos 60)]),
   ((.exchange 64 55 3),[(.neg 64),(.neg 55),(.pos 61),(.pos 62)]),
   ((.exchange 64 66 3),[(.neg 66),(.neg 64),(.pos 62),(.pos 69)]),
   ((.exchange 64 66 4),[(.neg 66),(.neg 64),(.pos 59),(.pos 68)]),
   ((.exchange 65 15 5),[(.neg 65),(.neg 15),(.pos 55),(.pos 56)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_1 : List (Origin 70 53 × List Sat.Literal) :=
  [((.exchange 65 30 0),[(.neg 65),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 65 32 0),[(.neg 65),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 65 33 0),[(.neg 65),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 65 34 0),[(.neg 65),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 65 43 5),[(.neg 65),(.neg 43),(.pos 55),(.pos 58),(.pos 61)]),
   ((.exchange 65 62 0),[(.neg 65),(.neg 62),(.pos 66),(.pos 69)]),
   ((.exchange 65 63 0),[(.neg 65),(.neg 63),(.pos 67),(.pos 69)]),
   ((.exchange 66 31 1),[(.neg 66),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 66 34 1),[(.neg 66),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 66 58 1),[(.neg 66),(.neg 58),(.pos 65),(.pos 68)]),
   ((.exchange 66 61 5),[(.neg 66),(.neg 61),(.pos 55),(.pos 62)]),
   ((.exchange 66 64 1),[(.neg 66),(.neg 64),(.pos 68),(.pos 69)]),
   ((.exchange 67 17 5),[(.neg 67),(.neg 17),(.pos 56),(.pos 60)]),
   ((.exchange 67 22 2),[(.neg 67),(.neg 22),(.pos 65),(.pos 68),(.pos 69)]),
   ((.exchange 67 24 5),[(.neg 67),(.neg 24),(.pos 60),(.pos 63)]),
   ((.exchange 67 28 2),[(.neg 67),(.neg 28),(.pos 65),(.pos 68)]),
   ((.exchange 67 31 2),[(.neg 67),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 67 58 5),[(.neg 67),(.neg 58),(.pos 56),(.pos 60)]),
   ((.exchange 68 24 5),[(.neg 68),(.neg 24),(.pos 60),(.pos 64)]),
   ((.exchange 68 26 3),[(.neg 68),(.neg 26),(.pos 65),(.pos 67)]),
   ((.exchange 68 31 3),[(.neg 68),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 68 35 5),[(.neg 68),(.neg 35),(.pos 58),(.pos 59),(.pos 60)]),
   ((.exchange 68 43 5),[(.neg 68),(.neg 43),(.pos 59),(.pos 64)]),
   ((.exchange 68 52 3),[(.neg 68),(.neg 52),(.pos 66),(.pos 69)]),
   ((.exchange 68 56 5),[(.neg 68),(.neg 56),(.pos 58),(.pos 60)]),
   ((.exchange 68 61 3),[(.neg 68),(.neg 61),(.pos 65),(.pos 69)]),
   ((.exchange 68 61 5),[(.neg 68),(.neg 61),(.pos 58),(.pos 64)]),
   ((.exchange 68 63 3),[(.neg 68),(.neg 63),(.pos 67),(.pos 69)]),
   ((.exchange 68 63 5),[(.neg 68),(.neg 63),(.pos 60),(.pos 64)]),
   ((.exchange 69 23 5),[(.neg 69),(.neg 23),(.pos 62),(.pos 64)]),
   ((.exchange 69 25 4),[(.neg 69),(.neg 25),(.pos 65),(.pos 66)]),
   ((.exchange 69 26 4),[(.neg 69),(.neg 26),(.pos 65),(.pos 67)]),
   ((.exchange 69 28 4),[(.neg 69),(.neg 28),(.pos 65),(.pos 68)]),
   ((.exchange 69 29 4),[(.neg 69),(.neg 29),(.pos 66),(.pos 68)]),
   ((.exchange 69 30 4),[(.neg 69),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 69 38 4),[(.neg 69),(.neg 38),(.pos 66),(.pos 67),(.pos 68)]),
   ((.exchange 69 41 5),[(.neg 69),(.neg 41),(.pos 62),(.pos 63)]),
   ((.exchange 69 44 5),[(.neg 69),(.neg 44),(.pos 63),(.pos 64)]),
   ((.exchange 69 48 4),[(.neg 69),(.neg 48),(.pos 65),(.pos 68)]),
   ((.exchange 69 55 5),[(.neg 69),(.neg 55),(.pos 61),(.pos 62)]),
   ((.exchange 69 56 4),[(.neg 69),(.neg 56),(.pos 65),(.pos 67)]),
   ((.exchange 69 59 4),[(.neg 69),(.neg 59),(.pos 66),(.pos 68)]),
   ((.exchange 69 59 5),[(.neg 69),(.neg 59),(.pos 62),(.pos 64)]),
   ((.exchange 69 60 4),[(.neg 69),(.neg 60),(.pos 67),(.pos 68)]),
   (.newPoint,[(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 0),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 62),(.neg 60),(.neg 57),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 58),(.pos 59),(.pos 61),(.pos 63),(.pos 65)]),
   ((.excluded 1),[(.neg 69),(.neg 68),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 57),(.pos 58),(.pos 59),(.pos 62),(.pos 66),(.pos 67)]),
   ((.excluded 2),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 68)]),
   ((.excluded 3),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 58),(.pos 59),(.pos 69)]),
   ((.excluded 4),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 58),(.pos 59)]),
   ((.excluded 5),[(.neg 69),(.neg 68),(.neg 65),(.neg 64),(.neg 62),(.neg 59),(.neg 58),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 56),(.pos 57),(.pos 60),(.pos 61),(.pos 63),(.pos 66),(.pos 67)]),
   ((.excluded 6),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 56),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 7),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 56),(.pos 61),(.pos 63),(.pos 68)]),
   ((.excluded 8),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 56),(.pos 61),(.pos 63)]),
   ((.excluded 9),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 57),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 10),[(.neg 69),(.neg 68),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 57),(.pos 64),(.pos 66),(.pos 67)]),
   ((.excluded 11),[(.neg 69),(.neg 68),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 57),(.pos 66),(.pos 67)]),
   ((.excluded 12),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 64),(.pos 65)]),
   ((.excluded 13),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 64)]),
   ((.excluded 14),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 62),(.pos 68)]),
   ((.excluded 15),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 68)]),
   ((.excluded 16),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 60),(.pos 69)]),
   ((.excluded 17),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 69)]),
   ((.excluded 18),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 60),(.pos 62),(.pos 65)]),
   ((.excluded 19),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 60),(.pos 62)]),
   ((.excluded 20),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 60),(.pos 65)]),
   ((.excluded 21),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 60)]),
   ((.excluded 22),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 62),(.pos 65)]),
   ((.excluded 23),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 62)]),
   ((.excluded 24),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 65)]),
   ((.excluded 25),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54)]),
   ((.excluded 26),[(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 27),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 62),(.neg 60),(.neg 57),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 55),(.pos 56),(.pos 58),(.pos 59),(.pos 61),(.pos 63),(.pos 65)]),
   ((.excluded 28),[(.neg 69),(.neg 68),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 55),(.pos 57),(.pos 58),(.pos 59),(.pos 62),(.pos 66),(.pos 67)]),
   ((.excluded 29),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 55),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 68)]),
   ((.excluded 30),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 55),(.pos 58),(.pos 59),(.pos 69)]),
   ((.excluded 31),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 55),(.pos 58),(.pos 59)]),
   ((.excluded 32),[(.neg 69),(.neg 68),(.neg 65),(.neg 64),(.neg 62),(.neg 59),(.neg 58),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 56),(.pos 57),(.pos 60),(.pos 61),(.pos 63),(.pos 66),(.pos 67)]),
   ((.excluded 33),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 56),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 34),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 56),(.pos 61),(.pos 63),(.pos 68)]),
   ((.excluded 35),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 56),(.pos 61),(.pos 63)]),
   ((.excluded 36),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 57),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 37),[(.neg 69),(.neg 68),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 57),(.pos 64),(.pos 66),(.pos 67)]),
   ((.excluded 38),[(.neg 69),(.neg 68),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 57),(.pos 66),(.pos 67)]),
   ((.excluded 39),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 64),(.pos 65)]),
   ((.excluded 40),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 64)]),
   ((.excluded 41),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 62),(.pos 68)]),
   ((.excluded 42),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 68)]),
   ((.excluded 43),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 60),(.pos 69)]),
   ((.excluded 44),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 69)]),
   ((.excluded 45),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 60),(.pos 62),(.pos 65)]),
   ((.excluded 46),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 60),(.pos 62)]),
   ((.excluded 47),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 60),(.pos 65)]),
   ((.excluded 48),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 60)]),
   ((.excluded 49),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 62),(.pos 65)]),
   ((.excluded 50),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 62)]),
   ((.excluded 51),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47),(.pos 65)]),
   ((.excluded 52),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 40),(.pos 47)])]

theorem certificates_1_valid : ∀ oc ∈ certificates_1,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



theorem witness_0 : ∀ j : Fin 53,
    let w : Fin 53 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 53,
      let w : Fin 53 := ⟨0 + j.val,by omega⟩
      target w < MatroidCatalogue.count 8 4 ∧
        Papers.RationalityTen.MatroidChecked.FastSemanticChecks.RawWitness 8 (N7R4.familyMasks.get 20)
        (fun i : Fin 70 => N8R4.gridMasks.get i.val) newIndex (models w)
        (N8R4.familyMasks.get (target w)) (permutation w) := by
    refine (Fin.forall_fin_add (m := 26) (n := 27) _).2 ⟨?_, ?_⟩
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
    · refine (Fin.forall_fin_add (m := 13) (n := 14) _).2 ⟨?_, ?_⟩
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


end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C20

/- Source: MatroidCatalogue/Cases/N8R4C20Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C20

noncomputable def certificates : List (Origin 70 53 × List Sat.Literal) :=
  certificates_0 ++ certificates_1

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  intro oc hoc
  simp only [certificates,List.mem_append,or_assoc] at hoc
  rcases hoc with h0 | h1
  · exact certificates_0_valid oc h0
  · exact certificates_1_valid oc h1

theorem models_valid : ∀ w : Fin 53,
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 53) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 8) 4)
    (hold : M.bases.filter ((7 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 8 4, IsomorphicWithin 8 M.bases B := by
  apply extension_covered_of_certificate (n:=7) (r:=4) (by decide)
    catalogue old U newIndex models certificates
    N8R4.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C20.formula []
    exact Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C20.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 8 4 (target w),family_mem 8 4 (target w) hw.1,?_⟩
    exact validWitness_sound 8 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C20


end
end
end BundlePart6

section BundlePart7
/- Source: MatroidChecked/SemanticChunks/Cases03Part07.lean -/




@[expose] public section
noncomputable section

/- Source: MatroidCatalogue/Cases/N8R4C21Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C21

abbrev U := N8R4.grid
noncomputable def old : Finset (Finset (Fin 8)) := N7R4.family 21
noncomputable def newIndexTree : Table ℕ := (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf 35) (.leaf 36)) (.node 3 (.leaf 37) (.leaf 38))) (.node 6 (.node 5 (.leaf 39) (.leaf 40)) (.node 7 (.leaf 41) (.leaf 42)))) (.node 12 (.node 10 (.node 9 (.leaf 43) (.leaf 44)) (.node 11 (.leaf 45) (.leaf 46))) (.node 14 (.node 13 (.leaf 47) (.leaf 48)) (.node 15 (.leaf 49) (.node 16 (.leaf 50) (.leaf 51)))))) (.node 26 (.node 21 (.node 19 (.node 18 (.leaf 52) (.leaf 53)) (.node 20 (.leaf 54) (.leaf 55))) (.node 23 (.node 22 (.leaf 56) (.leaf 57)) (.node 24 (.leaf 58) (.node 25 (.leaf 59) (.leaf 60))))) (.node 30 (.node 28 (.node 27 (.leaf 61) (.leaf 62)) (.node 29 (.leaf 63) (.leaf 64))) (.node 32 (.node 31 (.leaf 65) (.leaf 66)) (.node 33 (.leaf 67) (.node 34 (.leaf 68) (.leaf 69)))))))
noncomputable def newIndex (i : Fin 35) : Fin 70 := Fin.ofNat 70 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 38 (.node 19 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (32665239552,40,4151504)) (.leaf (32052871168,43,4151490))) (.node 3 (.leaf (29754392576,43,4151322)) (.leaf (25761415168,49,4122832)))) (.node 6 (.node 5 (.leaf (17171480576,49,4115664)) (.leaf (34351349760,50,8345736))) (.node 7 (.leaf (25106055168,43,4141410)) (.node 8 (.leaf (16163799040,43,4130658)) (.leaf (31598837760,49,4109728)))))) (.node 14 (.node 11 (.node 10 (.leaf (29451354112,49,4109616)) (.leaf (33746321408,50,8332128))) (.node 12 (.leaf (1072693248,53,3955098)) (.node 13 (.leaf (32177651712,61,10412696)) (.leaf (31942770688,61,10394776))))) (.node 16 (.node 15 (.leaf (32211206144,64,12465544)) (.leaf (25634537472,61,10397576))) (.node 17 (.leaf (25500319744,61,10397296)) (.node 18 (.leaf (25768755200,64,12477136)) (.leaf (32999735296,58,4151056))))))) (.node 28 (.node 23 (.node 21 (.node 20 (.leaf (34073477120,59,12534984)) (.leaf (33016512512,62,8300656))) (.node 22 (.leaf (34090254336,63,12527704)) (.leaf (30046945280,61,10412752)))) (.node 25 (.node 24 (.leaf (29929504768,61,10394832)) (.leaf (30063722496,64,12465264))) (.node 26 (.leaf (33268170752,62,8308104)) (.node 27 (.leaf (17162043392,61,10401160)) (.leaf (34341912576,63,12534984)))))) (.node 33 (.node 30 (.node 29 (.leaf (17145266176,61,10400880)) (.leaf (17178820608,64,12459216))) (.node 31 (.leaf (33117175808,58,4143888)) (.node 32 (.leaf (34190917632,59,12527816)) (.leaf (33251393536,62,8307824))))) (.node 35 (.node 34 (.leaf (34325135360,63,12534872)) (.leaf (33150730240,62,8300936))) (.node 36 (.leaf (34224472064,63,12527816)) (.node 37 (.leaf (33284947968,65,12465544)) (.leaf (34358689792,66,14599816)))))))) (.node 57 (.node 47 (.node 42 (.node 40 (.node 39 (.leaf (1048446,199,4708760)) (.leaf (32666287998,200,16434824))) (.node 41 (.leaf (32053919614,201,16434817)) (.leaf (29755441022,201,16434705)))) (.node 44 (.node 43 (.leaf (25762463614,202,16434824)) (.leaf (17172529022,202,16431240))) (.node 45 (.leaf (34352398206,203,16434824)) (.node 46 (.leaf (25107103614,201,16425241)) (.leaf (16164847486,201,16418073)))))) (.node 52 (.node 49 (.node 48 (.leaf (31599886206,202,16425752)) (.leaf (29452402558,202,16425696))) (.node 50 (.leaf (33747369854,203,16425752)) (.node 51 (.leaf (1073741694,204,16308432)) (.leaf (32178700158,205,16434768))))) (.node 54 (.node 53 (.leaf (31943819134,205,16431184)) (.leaf (32212254590,206,16434824))) (.node 55 (.leaf (30047993726,205,16434824)) (.node 56 (.leaf (29930553214,205,16431240)) (.leaf (30064770942,206,16434768))))))) (.node 67 (.node 62 (.node 59 (.node 58 (.leaf (25635585918,205,16422168)) (.leaf (25501368190,205,16422112))) (.node 60 (.leaf (25769803646,206,16425752)) (.node 61 (.leaf (33118224254,207,16431240)) (.leaf (34191966078,208,16431240))))) (.node 64 (.node 63 (.leaf (33151778686,209,16427208)) (.leaf (34225520510,210,16427208))) (.node 65 (.leaf (33252441982,209,16434264)) (.node 66 (.leaf (17146314622,205,16425696)) (.leaf (34326183806,210,16434264)))))) (.node 72 (.node 69 (.node 68 (.leaf (17163091838,205,16425752)) (.leaf (17179869054,206,16422168))) (.node 70 (.leaf (33000783742,207,16434824)) (.node 71 (.leaf (34074525566,208,16434824)) (.leaf (33269219198,209,16434376))))) (.node 74 (.node 73 (.leaf (34342961022,210,16434376)) (.leaf (33017560958,209,16427096))) (.node 75 (.leaf (34091302782,210,16427096)) (.node 76 (.leaf (33285996414,211,16434824)) (.leaf (34359738238,212,16434824)))))))))

noncomputable def models (i : Fin 77) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 77) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 77) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 70, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (7 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 70, (7 : Fin 8) ∈ U i → ∃ j : Fin 35, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C21

/- Source: MatroidCatalogue/Cases/N8R4C21Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C21


noncomputable def certificates_0 : List (Origin 70 77 × List Sat.Literal) :=
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
   ((.fixed 29),[(.pos 29)]),
   ((.fixed 30),[(.pos 30)]),
   ((.fixed 31),[(.pos 31)]),
   ((.fixed 32),[(.pos 32)]),
   ((.fixed 33),[(.pos 33)]),
   ((.fixed 34),[(.pos 34)]),
   ((.exchange 16 41 6),[(.neg 41),(.neg 16),(.pos 0),(.pos 2),(.pos 36)]),
   ((.exchange 16 56 3),[(.neg 56),(.neg 16),(.pos 15),(.pos 55)]),
   ((.exchange 16 57 3),[(.neg 57),(.neg 16),(.pos 15),(.pos 55)]),
   ((.exchange 16 61 1),[(.neg 61),(.neg 16),(.pos 22),(.pos 58)]),
   ((.exchange 16 64 1),[(.neg 64),(.neg 16),(.pos 22),(.pos 58)]),
   ((.exchange 17 41 6),[(.neg 41),(.neg 17),(.pos 0),(.pos 3),(.pos 37)]),
   ((.exchange 17 55 3),[(.neg 55),(.neg 17),(.pos 15),(.pos 56)]),
   ((.exchange 17 57 3),[(.neg 57),(.neg 17),(.pos 15),(.pos 56)]),
   ((.exchange 18 41 6),[(.neg 41),(.neg 18),(.pos 4),(.pos 38)]),
   ((.exchange 18 55 3),[(.neg 55),(.neg 18),(.pos 15),(.pos 57)]),
   ((.exchange 18 56 3),[(.neg 56),(.neg 18),(.pos 15),(.pos 57)]),
   ((.exchange 19 41 6),[(.neg 41),(.neg 19),(.pos 1),(.pos 39)]),
   ((.exchange 19 58 1),[(.neg 58),(.neg 19),(.pos 22),(.pos 61)]),
   ((.exchange 19 64 1),[(.neg 64),(.neg 19),(.pos 22),(.pos 61)]),
   ((.exchange 20 41 6),[(.neg 41),(.neg 20),(.pos 1),(.pos 40)]),
   ((.exchange 21 36 6),[(.neg 36),(.neg 21),(.pos 1),(.pos 4),(.pos 41)]),
   ((.exchange 21 37 6),[(.neg 37),(.neg 21),(.pos 1),(.pos 4),(.pos 41)]),
   ((.exchange 21 38 6),[(.neg 38),(.neg 21),(.pos 4),(.pos 41)]),
   ((.exchange 21 39 6),[(.neg 39),(.neg 21),(.pos 1),(.pos 41)]),
   ((.exchange 21 40 6),[(.neg 40),(.neg 21),(.pos 1),(.pos 41)]),
   ((.exchange 21 43 6),[(.neg 43),(.neg 21),(.pos 4),(.pos 41)]),
   ((.exchange 21 44 6),[(.neg 44),(.neg 21),(.pos 4),(.pos 41)]),
   ((.exchange 21 45 6),[(.neg 45),(.neg 21),(.pos 1),(.pos 11),(.pos 41)]),
   ((.exchange 21 46 6),[(.neg 46),(.neg 21),(.pos 1),(.pos 11),(.pos 41)]),
   ((.exchange 21 47 6),[(.neg 47),(.neg 21),(.pos 11),(.pos 41)]),
   ((.exchange 21 48 6),[(.neg 48),(.neg 21),(.pos 1),(.pos 4),(.pos 11),(.pos 41)]),
   ((.exchange 21 49 6),[(.neg 49),(.neg 21),(.pos 4),(.pos 11),(.pos 41)]),
   ((.exchange 21 50 6),[(.neg 50),(.neg 21),(.pos 4),(.pos 11),(.pos 41)]),
   ((.exchange 21 51 6),[(.neg 51),(.neg 21),(.pos 1),(.pos 11),(.pos 41)]),
   ((.exchange 21 52 6),[(.neg 52),(.neg 21),(.pos 11),(.pos 41)]),
   ((.exchange 21 53 6),[(.neg 53),(.neg 21),(.pos 11),(.pos 41)]),
   ((.exchange 21 54 6),[(.neg 54),(.neg 21),(.pos 4),(.pos 11),(.pos 41)]),
   ((.exchange 23 41 6),[(.neg 41),(.neg 23),(.pos 4),(.pos 43)]),
   ((.exchange 23 58 1),[(.neg 58),(.neg 23),(.pos 22),(.pos 64)]),
   ((.exchange 23 61 1),[(.neg 61),(.neg 23),(.pos 22),(.pos 64)]),
   ((.exchange 24 41 6),[(.neg 41),(.neg 24),(.pos 4),(.pos 44)]),
   ((.exchange 25 41 6),[(.neg 41),(.neg 25),(.pos 5),(.pos 9),(.pos 45)]),
   ((.exchange 26 41 6),[(.neg 41),(.neg 26),(.pos 5),(.pos 10),(.pos 46)]),
   ((.exchange 27 41 6),[(.neg 41),(.neg 27),(.pos 11),(.pos 47)]),
   ((.exchange 28 41 6),[(.neg 41),(.neg 28),(.pos 6),(.pos 7),(.pos 12),(.pos 48)]),
   ((.exchange 29 41 6),[(.neg 41),(.neg 29),(.pos 8),(.pos 13),(.pos 49)]),
   ((.exchange 30 41 6),[(.neg 41),(.neg 30),(.pos 8),(.pos 14),(.pos 50)]),
   ((.exchange 31 41 6),[(.neg 41),(.neg 31),(.pos 9),(.pos 10),(.pos 51)]),
   ((.exchange 32 41 6),[(.neg 41),(.neg 32),(.pos 11),(.pos 52)]),
   ((.exchange 33 41 6),[(.neg 41),(.neg 33),(.pos 11),(.pos 53)]),
   ((.exchange 34 41 6),[(.neg 41),(.neg 34),(.pos 13),(.pos 14),(.pos 54)]),
   ((.exchange 35 16 7),[(.neg 35),(.neg 16),(.pos 0),(.pos 15)]),
   ((.exchange 42 16 7),[(.neg 42),(.neg 16),(.pos 2),(.pos 22)]),
   ((.exchange 55 23 0),[(.neg 55),(.neg 23),(.pos 59),(.pos 62)]),
   ((.exchange 55 28 1),[(.neg 55),(.neg 28),(.pos 58),(.pos 65)]),
   ((.exchange 55 29 0),[(.neg 55),(.neg 29),(.pos 59),(.pos 66)]),
   ((.exchange 55 32 0),[(.neg 55),(.neg 32),(.pos 62),(.pos 66)]),
   ((.exchange 56 24 0),[(.neg 56),(.neg 24),(.pos 60),(.pos 63)]),
   ((.exchange 56 28 2),[(.neg 56),(.neg 28),(.pos 58),(.pos 65)]),
   ((.exchange 56 31 2),[(.neg 56),(.neg 31),(.pos 61),(.pos 65)]),
   ((.exchange 57 29 2),[(.neg 57),(.neg 29),(.pos 59),(.pos 66)]),
   ((.exchange 57 30 1),[(.neg 57),(.neg 30),(.pos 60),(.pos 67)]),
   ((.exchange 57 33 1),[(.neg 57),(.neg 33),(.pos 63),(.pos 67)]),
   ((.exchange 57 49 2),[(.neg 57),(.neg 49),(.pos 59),(.pos 66)]),
   ((.exchange 57 52 2),[(.neg 57),(.neg 52),(.pos 62),(.pos 66)]),
   ((.exchange 57 69 2),[(.neg 69),(.neg 57),(.pos 62),(.pos 66)]),
   ((.exchange 58 29 0),[(.neg 58),(.neg 29),(.pos 59),(.pos 68)]),
   ((.exchange 58 30 0),[(.neg 58),(.neg 30),(.pos 60),(.pos 68)]),
   ((.exchange 58 57 0),[(.neg 58),(.neg 57),(.pos 59),(.pos 60)]),
   ((.exchange 58 67 3),[(.neg 67),(.neg 58),(.pos 56),(.pos 65)]),
   ((.exchange 59 19 3),[(.neg 59),(.neg 19),(.pos 55),(.pos 62)]),
   ((.exchange 59 24 1),[(.neg 59),(.neg 24),(.pos 60),(.pos 64)]),
   ((.exchange 59 26 3),[(.neg 59),(.neg 26),(.pos 55),(.pos 57),(.pos 66)]),
   ((.exchange 59 28 1),[(.neg 59),(.neg 28),(.pos 58),(.pos 68)]),
   ((.exchange 59 30 1),[(.neg 59),(.neg 30),(.pos 60),(.pos 68)]),
   ((.exchange 59 34 1),[(.neg 59),(.neg 34),(.pos 64),(.pos 68)]),
   ((.exchange 59 41 3),[(.neg 59),(.neg 41),(.pos 57),(.pos 62)]),
   ((.exchange 59 48 1),[(.neg 59),(.neg 48),(.pos 58),(.pos 68)]),
   ((.exchange 59 69 1),[(.neg 69),(.neg 59),(.pos 64),(.pos 68)]),
   ((.exchange 59 69 3),[(.neg 69),(.neg 59),(.pos 62),(.pos 66)]),
   ((.exchange 60 16 2),[(.neg 60),(.neg 16),(.pos 58),(.pos 59)]),
   ((.exchange 60 19 3),[(.neg 60),(.neg 19),(.pos 56),(.pos 57),(.pos 63)]),
   ((.exchange 60 23 2),[(.neg 60),(.neg 23),(.pos 59),(.pos 64)]),
   ((.exchange 60 27 3),[(.neg 60),(.neg 27),(.pos 57),(.pos 67)]),
   ((.exchange 60 28 2),[(.neg 60),(.neg 28),(.pos 58),(.pos 68)]),
   ((.exchange 60 29 2),[(.neg 60),(.neg 29),(.pos 59),(.pos 68)]),
   ((.exchange 60 36 2),[(.neg 60),(.neg 36),(.pos 58),(.pos 59)]),
   ((.exchange 60 43 2),[(.neg 60),(.neg 43),(.pos 59),(.pos 64)]),
   ((.exchange 60 55 2),[(.neg 60),(.neg 55),(.pos 58),(.pos 59)]),
   ((.exchange 60 66 3),[(.neg 66),(.neg 60),(.pos 57),(.pos 67)]),
   ((.exchange 60 69 2),[(.neg 69),(.neg 60),(.pos 64),(.pos 68)]),
   ((.exchange 61 21 0),[(.neg 61),(.neg 21),(.pos 62),(.pos 63)]),
   ((.exchange 61 46 4),[(.neg 61),(.neg 46),(.pos 56),(.pos 65)]),
   ((.exchange 61 53 0),[(.neg 61),(.neg 53),(.pos 63),(.pos 69)]),
   ((.exchange 61 66 0),[(.neg 66),(.neg 61),(.pos 62),(.pos 69)]),
   ((.exchange 61 67 0),[(.neg 67),(.neg 61),(.pos 63),(.pos 69)]),
   ((.exchange 61 67 4),[(.neg 67),(.neg 61),(.pos 56),(.pos 65)]),
   ((.exchange 62 16 4),[(.neg 62),(.neg 16),(.pos 55),(.pos 59)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_1 : List (Origin 70 77 × List Sat.Literal) :=
  [((.exchange 62 25 4),[(.neg 62),(.neg 25),(.pos 55),(.pos 66)]),
   ((.exchange 62 26 4),[(.neg 62),(.neg 26),(.pos 55),(.pos 57),(.pos 66)]),
   ((.exchange 62 34 1),[(.neg 62),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 62 54 1),[(.neg 62),(.neg 54),(.pos 64),(.pos 69)]),
   ((.exchange 62 60 1),[(.neg 62),(.neg 60),(.pos 63),(.pos 64)]),
   ((.exchange 62 65 1),[(.neg 65),(.neg 62),(.pos 61),(.pos 69)]),
   ((.exchange 62 68 1),[(.neg 68),(.neg 62),(.pos 64),(.pos 69)]),
   ((.exchange 63 16 2),[(.neg 63),(.neg 16),(.pos 61),(.pos 62),(.pos 64)]),
   ((.exchange 63 18 4),[(.neg 63),(.neg 18),(.pos 57),(.pos 60)]),
   ((.exchange 63 27 4),[(.neg 63),(.neg 27),(.pos 57),(.pos 67)]),
   ((.exchange 63 31 2),[(.neg 63),(.neg 31),(.pos 61),(.pos 69)]),
   ((.exchange 63 32 2),[(.neg 63),(.neg 32),(.pos 62),(.pos 69)]),
   ((.exchange 63 34 2),[(.neg 63),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 63 65 2),[(.neg 65),(.neg 63),(.pos 61),(.pos 69)]),
   ((.exchange 63 66 4),[(.neg 66),(.neg 63),(.pos 57),(.pos 67)]),
   ((.exchange 64 18 4),[(.neg 64),(.neg 18),(.pos 59),(.pos 60)]),
   ((.exchange 64 21 3),[(.neg 64),(.neg 21),(.pos 62),(.pos 63)]),
   ((.exchange 64 29 4),[(.neg 64),(.neg 29),(.pos 59),(.pos 68)]),
   ((.exchange 64 30 4),[(.neg 64),(.neg 30),(.pos 60),(.pos 68)]),
   ((.exchange 64 49 4),[(.neg 64),(.neg 49),(.pos 59),(.pos 68)]),
   ((.exchange 64 67 3),[(.neg 67),(.neg 64),(.pos 63),(.pos 69)]),
   ((.exchange 65 16 5),[(.neg 65),(.neg 16),(.pos 55),(.pos 58)]),
   ((.exchange 65 27 0),[(.neg 65),(.neg 27),(.pos 66),(.pos 67)]),
   ((.exchange 65 30 0),[(.neg 65),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 65 34 0),[(.neg 65),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 65 49 0),[(.neg 65),(.neg 49),(.pos 66),(.pos 68)]),
   ((.exchange 65 60 5),[(.neg 65),(.neg 60),(.pos 56),(.pos 58)]),
   ((.exchange 65 62 5),[(.neg 65),(.neg 62),(.pos 55),(.pos 61)]),
   ((.exchange 65 63 0),[(.neg 65),(.neg 63),(.pos 67),(.pos 69)]),
   ((.exchange 65 63 5),[(.neg 65),(.neg 63),(.pos 56),(.pos 61)]),
   ((.exchange 66 23 5),[(.neg 66),(.neg 23),(.pos 59),(.pos 62)]),
   ((.exchange 66 26 1),[(.neg 66),(.neg 26),(.pos 65),(.pos 67)]),
   ((.exchange 66 30 1),[(.neg 66),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 66 33 1),[(.neg 66),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 66 41 5),[(.neg 66),(.neg 41),(.pos 57),(.pos 62)]),
   ((.exchange 66 46 1),[(.neg 66),(.neg 46),(.pos 65),(.pos 67)]),
   ((.exchange 66 50 1),[(.neg 66),(.neg 50),(.pos 67),(.pos 68)]),
   ((.exchange 66 56 1),[(.neg 66),(.neg 56),(.pos 65),(.pos 67)]),
   ((.exchange 66 60 5),[(.neg 66),(.neg 60),(.pos 57),(.pos 59)]),
   ((.exchange 66 61 5),[(.neg 66),(.neg 61),(.pos 55),(.pos 62)]),
   ((.exchange 66 63 1),[(.neg 66),(.neg 63),(.pos 67),(.pos 69)]),
   ((.exchange 66 63 5),[(.neg 66),(.neg 63),(.pos 57),(.pos 62)]),
   ((.exchange 66 64 5),[(.neg 66),(.neg 64),(.pos 59),(.pos 62)]),
   ((.exchange 67 16 5),[(.neg 67),(.neg 16),(.pos 56),(.pos 57),(.pos 60)]),
   ((.exchange 67 19 5),[(.neg 67),(.neg 19),(.pos 56),(.pos 57),(.pos 63)]),
   ((.exchange 67 24 5),[(.neg 67),(.neg 24),(.pos 60),(.pos 63)]),
   ((.exchange 67 25 2),[(.neg 67),(.neg 25),(.pos 65),(.pos 66)]),
   ((.exchange 67 28 2),[(.neg 67),(.neg 28),(.pos 65),(.pos 68)]),
   ((.exchange 67 29 2),[(.neg 67),(.neg 29),(.pos 66),(.pos 68)]),
   ((.exchange 67 31 2),[(.neg 67),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 67 32 2),[(.neg 67),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 67 34 2),[(.neg 67),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 67 38 5),[(.neg 67),(.neg 38),(.pos 57),(.pos 60)]),
   ((.exchange 67 41 5),[(.neg 67),(.neg 41),(.pos 57),(.pos 63)]),
   ((.exchange 67 51 2),[(.neg 67),(.neg 51),(.pos 65),(.pos 69)]),
   ((.exchange 67 52 2),[(.neg 67),(.neg 52),(.pos 66),(.pos 69)]),
   ((.exchange 67 54 2),[(.neg 67),(.neg 54),(.pos 68),(.pos 69)]),
   ((.exchange 67 61 2),[(.neg 67),(.neg 61),(.pos 65),(.pos 69)]),
   ((.exchange 68 16 5),[(.neg 68),(.neg 16),(.pos 58),(.pos 59)]),
   ((.exchange 68 17 5),[(.neg 68),(.neg 17),(.pos 58),(.pos 60)]),
   ((.exchange 68 18 5),[(.neg 68),(.neg 18),(.pos 59),(.pos 60)]),
   ((.exchange 68 24 5),[(.neg 68),(.neg 24),(.pos 60),(.pos 64)]),
   ((.exchange 68 26 3),[(.neg 68),(.neg 26),(.pos 65),(.pos 67)]),
   ((.exchange 68 27 3),[(.neg 68),(.neg 27),(.pos 66),(.pos 67)]),
   ((.exchange 68 32 3),[(.neg 68),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 68 33 3),[(.neg 68),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 68 43 5),[(.neg 68),(.neg 43),(.pos 59),(.pos 64)]),
   ((.exchange 68 44 5),[(.neg 68),(.neg 44),(.pos 60),(.pos 64)]),
   ((.exchange 68 45 3),[(.neg 68),(.neg 45),(.pos 65),(.pos 66)]),
   ((.exchange 68 47 3),[(.neg 68),(.neg 47),(.pos 66),(.pos 67)]),
   ((.exchange 68 55 3),[(.neg 68),(.neg 55),(.pos 65),(.pos 66)]),
   ((.exchange 68 56 5),[(.neg 68),(.neg 56),(.pos 58),(.pos 60)]),
   ((.exchange 68 62 5),[(.neg 68),(.neg 62),(.pos 59),(.pos 64)]),
   ((.exchange 68 63 3),[(.neg 68),(.neg 63),(.pos 67),(.pos 69)]),
   ((.exchange 69 16 5),[(.neg 69),(.neg 16),(.pos 61),(.pos 62),(.pos 64)]),
   ((.exchange 69 24 5),[(.neg 69),(.neg 24),(.pos 63),(.pos 64)]),
   ((.exchange 69 26 4),[(.neg 69),(.neg 26),(.pos 65),(.pos 67)]),
   ((.exchange 69 27 4),[(.neg 69),(.neg 27),(.pos 66),(.pos 67)]),
   ((.exchange 69 28 4),[(.neg 69),(.neg 28),(.pos 65),(.pos 68)]),
   ((.exchange 69 29 4),[(.neg 69),(.neg 29),(.pos 66),(.pos 68)]),
   ((.exchange 69 30 4),[(.neg 69),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 69 47 4),[(.neg 69),(.neg 47),(.pos 66),(.pos 67)]),
   ((.exchange 69 56 5),[(.neg 69),(.neg 56),(.pos 61),(.pos 63)]),
   ((.exchange 69 57 5),[(.neg 69),(.neg 57),(.pos 62),(.pos 63)]),
   ((.exchange 69 59 5),[(.neg 69),(.neg 59),(.pos 62),(.pos 64)]),
   ((.exchange 69 60 4),[(.neg 69),(.neg 60),(.pos 67),(.pos 68)]),
   ((.exchange 69 60 5),[(.neg 69),(.neg 60),(.pos 63),(.pos 64)]),
   (.newPoint,[(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 0),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 61),(.pos 64),(.pos 65)]),
   ((.excluded 1),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 58),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 59),(.pos 62),(.pos 66)]),
   ((.excluded 2),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 3),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 68)]),
   ((.excluded 4),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 69)]),
   ((.excluded 5),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 6),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 64),(.pos 68)]),
   ((.excluded 7),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 58),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 8),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 58),(.pos 61),(.pos 64),(.pos 66)]),
   ((.excluded 9),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 58),(.pos 61),(.pos 64),(.pos 67)]),
   ((.excluded 10),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 58),(.pos 61),(.pos 64)]),
   ((.excluded 11),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 12),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 60),(.pos 66)]),
   ((.excluded 13),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 63),(.pos 66)]),
   ((.excluded 14),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 66)]),
   ((.excluded 15),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 62),(.pos 68)]),
   ((.excluded 16),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 63),(.pos 68)]),
   ((.excluded 17),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 68)]),
   ((.excluded 18),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 59),(.pos 63),(.pos 65)]),
   ((.excluded 19),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 59),(.pos 63)]),
   ((.excluded 20),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 63),(.pos 65)]),
   ((.excluded 21),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 63)]),
   ((.excluded 22),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 59),(.pos 67)]),
   ((.excluded 23),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 62),(.pos 67)]),
   ((.excluded 24),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 67)]),
   ((.excluded 25),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 59),(.pos 65)]),
   ((.excluded 26),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 59),(.pos 69)]),
   ((.excluded 27),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 59)]),
   ((.excluded 28),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 60),(.pos 69)]),
   ((.excluded 29),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 69)]),
   ((.excluded 30),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 60),(.pos 62),(.pos 65)]),
   ((.excluded 31),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 60),(.pos 62)]),
   ((.excluded 32),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 60),(.pos 65)]),
   ((.excluded 33),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 60)]),
   ((.excluded 34),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 62),(.pos 65)]),
   ((.excluded 35),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 62)]),
   ((.excluded 36),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 65)]),
   ((.excluded 37),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54)]),
   ((.excluded 38),[(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 39),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 61),(.pos 64),(.pos 65)])]

theorem certificates_1_valid : ∀ oc ∈ certificates_1,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_2 : List (Origin 70 77 × List Sat.Literal) :=
  [((.excluded 40),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 55),(.pos 56),(.pos 57),(.pos 59),(.pos 62),(.pos 66)]),
   ((.excluded 41),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 42),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 55),(.pos 56),(.pos 57),(.pos 68)]),
   ((.excluded 43),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 55),(.pos 56),(.pos 57),(.pos 69)]),
   ((.excluded 44),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 45),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 64),(.pos 68)]),
   ((.excluded 46),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 58),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 47),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 58),(.pos 61),(.pos 64),(.pos 66)]),
   ((.excluded 48),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 58),(.pos 61),(.pos 64),(.pos 67)]),
   ((.excluded 49),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 58),(.pos 61),(.pos 64)]),
   ((.excluded 50),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 51),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 60),(.pos 66)]),
   ((.excluded 52),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 63),(.pos 66)]),
   ((.excluded 53),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 66)]),
   ((.excluded 54),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 59),(.pos 67)]),
   ((.excluded 55),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 62),(.pos 67)]),
   ((.excluded 56),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 67)]),
   ((.excluded 57),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 62),(.pos 68)]),
   ((.excluded 58),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 63),(.pos 68)]),
   ((.excluded 59),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 68)]),
   ((.excluded 60),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 60),(.pos 62),(.pos 65)]),
   ((.excluded 61),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 60),(.pos 62)]),
   ((.excluded 62),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 62),(.pos 65)]),
   ((.excluded 63),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 62)]),
   ((.excluded 64),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 60),(.pos 65)]),
   ((.excluded 65),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 60),(.pos 69)]),
   ((.excluded 66),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 60)]),
   ((.excluded 67),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 59),(.pos 69)]),
   ((.excluded 68),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 69)]),
   ((.excluded 69),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 59),(.pos 63),(.pos 65)]),
   ((.excluded 70),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 59),(.pos 63)]),
   ((.excluded 71),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 59),(.pos 65)]),
   ((.excluded 72),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 59)]),
   ((.excluded 73),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 63),(.pos 65)]),
   ((.excluded 74),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 63)]),
   ((.excluded 75),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 65)]),
   ((.excluded 76),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42)])]

theorem certificates_2_valid : ∀ oc ∈ certificates_2,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



theorem witness_0 : ∀ j : Fin 77,
    let w : Fin 77 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 77,
      let w : Fin 77 := ⟨0 + j.val,by omega⟩
      target w < MatroidCatalogue.count 8 4 ∧
        Papers.RationalityTen.MatroidChecked.FastSemanticChecks.RawWitness 8 (N7R4.familyMasks.get 21)
        (fun i : Fin 70 => N8R4.gridMasks.get i.val) newIndex (models w)
        (N8R4.familyMasks.get (target w)) (permutation w) := by
    refine (Fin.forall_fin_add (m := 38) (n := 39) _).2 ⟨?_, ?_⟩
    · refine (Fin.forall_fin_add (m := 19) (n := 19) _).2 ⟨?_, ?_⟩
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
  intro j
  have hj := hfast j
  exact ⟨hj.1,Papers.RationalityTen.MatroidChecked.FastSemanticChecks.rawWitness_sound 8 _ _ _ _ _ _ hj.2⟩


end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C21

/- Source: MatroidCatalogue/Cases/N8R4C21Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C21

noncomputable def certificates : List (Origin 70 77 × List Sat.Literal) :=
  certificates_0 ++ certificates_1 ++ certificates_2

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  intro oc hoc
  simp only [certificates,List.mem_append,or_assoc] at hoc
  rcases hoc with h0 | h1 | h2
  · exact certificates_0_valid oc h0
  · exact certificates_1_valid oc h1
  · exact certificates_2_valid oc h2

theorem models_valid : ∀ w : Fin 77,
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 77) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 8) 4)
    (hold : M.bases.filter ((7 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 8 4, IsomorphicWithin 8 M.bases B := by
  apply extension_covered_of_certificate (n:=7) (r:=4) (by decide)
    catalogue old U newIndex models certificates
    N8R4.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C21.formula []
    exact Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C21.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 8 4 (target w),family_mem 8 4 (target w) hw.1,?_⟩
    exact validWitness_sound 8 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C21


end
end
end BundlePart7

section BundlePart8
/- Source: MatroidChecked/SemanticChunks/Cases03Part08.lean -/




@[expose] public section
noncomputable section

/- Source: MatroidCatalogue/Cases/N8R4C22Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C22

abbrev U := N8R4.grid
noncomputable def old : Finset (Finset (Fin 8)) := N7R4.family 22
noncomputable def newIndexTree : Table ℕ := (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf 35) (.leaf 36)) (.node 3 (.leaf 37) (.leaf 38))) (.node 6 (.node 5 (.leaf 39) (.leaf 40)) (.node 7 (.leaf 41) (.leaf 42)))) (.node 12 (.node 10 (.node 9 (.leaf 43) (.leaf 44)) (.node 11 (.leaf 45) (.leaf 46))) (.node 14 (.node 13 (.leaf 47) (.leaf 48)) (.node 15 (.leaf 49) (.node 16 (.leaf 50) (.leaf 51)))))) (.node 26 (.node 21 (.node 19 (.node 18 (.leaf 52) (.leaf 53)) (.node 20 (.leaf 54) (.leaf 55))) (.node 23 (.node 22 (.leaf 56) (.leaf 57)) (.node 24 (.leaf 58) (.node 25 (.leaf 59) (.leaf 60))))) (.node 30 (.node 28 (.node 27 (.leaf 61) (.leaf 62)) (.node 29 (.leaf 63) (.leaf 64))) (.node 32 (.node 31 (.leaf 65) (.leaf 66)) (.node 33 (.leaf 67) (.node 34 (.leaf 68) (.leaf 69)))))))
noncomputable def newIndex (i : Fin 35) : Fin 70 := Fin.ofNat 70 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 43 (.node 21 (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (33202110464,44,4151504)) (.leaf (32052871168,44,4151490))) (.node 3 (.leaf (29754392576,44,4151322)) (.node 4 (.leaf (8044675072,47,2017169)) (.leaf (34351349760,51,8345736))))) (.node 7 (.node 6 (.leaf (7993294848,44,4039084)) (.leaf (7582253056,44,4031916))) (.node 8 (.leaf (535822336,44,3945900)) (.node 9 (.leaf (8052015104,51,8196524)) (.leaf (29921116160,60,1956241)))))) (.node 15 (.node 12 (.node 11 (.leaf (34216083456,61,6211464)) (.leaf (30055333888,61,6182512))) (.node 13 (.leaf (31934382080,60,2013585)) (.node 14 (.leaf (34081865728,61,6211184)) (.leaf (32202817536,61,6182792))))) (.node 18 (.node 16 (.leaf (34350301184,64,14598864)) (.node 17 (.leaf (29929504768,61,6175302)) (.leaf (33117175808,60,1988497)))) (.node 19 (.leaf (34190917632,61,6207558)) (.node 20 (.leaf (33150730240,61,6146952)) (.leaf (34224472064,64,14588098))))))) (.node 32 (.node 26 (.node 23 (.node 22 (.leaf (29979836416,60,1952657)) (.leaf (30046945280,61,6182470))) (.node 24 (.leaf (29996613632,61,6175344)) (.node 25 (.leaf (30063722496,64,14473242)) (.leaf (34274803712,61,6207880))))) (.node 29 (.node 27 (.leaf (32999735296,60,1981329)) (.node 28 (.leaf (34073477120,61,6211142)) (.leaf (33268170752,61,6150536)))) (.node 30 (.leaf (34341912576,64,14598850)) (.node 31 (.leaf (32110542848,60,2017169)) (.leaf (34258026496,61,6207600)))))) (.node 37 (.node 34 (.node 33 (.leaf (32144097280,61,6175624)) (.leaf (34291580928,64,14588112))) (.node 35 (.leaf (33251393536,61,6150256)) (.node 36 (.leaf (32177651712,61,6150214)) (.leaf (34325135360,64,14598682))))) (.node 40 (.node 38 (.leaf (33016512512,61,6146672)) (.node 39 (.leaf (33284947968,64,14473424)) (.leaf (31942770688,61,6146630)))) (.node 41 (.leaf (34090254336,64,14587930)) (.node 42 (.leaf (32211206144,64,14473410)) (.leaf (34358689792,67,14599816)))))))) (.node 65 (.node 54 (.node 48 (.node 45 (.node 44 (.leaf (524286,213,2279410)) (.leaf (8045199358,214,16434824))) (.node 46 (.leaf (33202634750,215,16434824)) (.node 47 (.leaf (32053395454,215,16434817)) (.leaf (29754916862,215,16434705))))) (.node 51 (.node 49 (.leaf (34351874046,216,16434824)) (.node 50 (.leaf (7993819134,215,16322915)) (.leaf (7582777342,215,16319331)))) (.node 52 (.leaf (536346622,215,16261987)) (.node 53 (.leaf (8052539390,216,16322915)) (.leaf (29921640446,217,16434824)))))) (.node 59 (.node 56 (.node 55 (.leaf (34216607742,218,16430344)) (.leaf (30055858174,218,16372832))) (.node 57 (.leaf (31934906366,217,16406152)) (.node 58 (.leaf (34082390014,218,16430176)) (.leaf (32203341822,218,16373000))))) (.node 62 (.node 60 (.leaf (34350825470,219,16433872)) (.node 61 (.leaf (29930029054,218,16362052)) (.leaf (33117700094,217,16370312)))) (.node 63 (.leaf (34191441918,218,16426564)) (.node 64 (.leaf (33151254526,218,16333576)) (.leaf (34224996350,219,16423106))))))) (.node 76 (.node 70 (.node 67 (.node 66 (.leaf (29980360702,217,16431240)) (.leaf (30047469566,218,16372804))) (.node 68 (.leaf (29997137918,218,16362080)) (.node 69 (.leaf (30064246782,219,16308250)) (.leaf (34275327998,218,16426760))))) (.node 73 (.node 71 (.leaf (33000259582,217,16373896)) (.node 72 (.leaf (34074001406,218,16430148)) (.leaf (33268695038,218,16340744)))) (.node 74 (.leaf (34342436862,219,16433858)) (.node 75 (.leaf (32111067134,217,16398984)) (.leaf (34258550782,218,16426592)))))) (.node 81 (.node 78 (.node 77 (.leaf (32144621566,218,16362248)) (.leaf (34292105214,219,16423120))) (.node 79 (.leaf (33251917822,218,16340576)) (.node 80 (.leaf (32178175998,218,16340548)) (.leaf (34325659646,219,16433690))))) (.node 84 (.node 82 (.leaf (33017036798,218,16333408)) (.node 83 (.leaf (33285472254,219,16308432)) (.leaf (31943294974,218,16333380)))) (.node 85 (.leaf (34090778622,219,16422938)) (.node 86 (.leaf (32211730430,219,16308418)) (.leaf (34359214078,220,16434824)))))))))

noncomputable def models (i : Fin 87) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 87) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 87) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 70, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (7 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 70, (7 : Fin 8) ∈ U i → ∃ j : Fin 35, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C22

/- Source: MatroidCatalogue/Cases/N8R4C22Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C22


noncomputable def certificates_0 : List (Origin 70 87 × List Sat.Literal) :=
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
   ((.fixed 16),[(.pos 16)]),
   ((.fixed 17),[(.pos 17)]),
   ((.fixed 18),[(.pos 18)]),
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
   ((.fixed 34),[(.neg 34)]),
   ((.exchange 16 41 6),[(.neg 41),(.neg 16),(.pos 0),(.pos 2),(.pos 36)]),
   ((.exchange 16 56 3),[(.neg 56),(.neg 16),(.pos 15),(.pos 55)]),
   ((.exchange 16 57 3),[(.neg 57),(.neg 16),(.pos 15),(.pos 55)]),
   ((.exchange 17 41 6),[(.neg 41),(.neg 17),(.pos 0),(.pos 3),(.pos 37)]),
   ((.exchange 17 55 3),[(.neg 55),(.neg 17),(.pos 15),(.pos 56)]),
   ((.exchange 17 57 3),[(.neg 57),(.neg 17),(.pos 15),(.pos 56)]),
   ((.exchange 18 41 6),[(.neg 41),(.neg 18),(.pos 4),(.pos 38)]),
   ((.exchange 18 55 3),[(.neg 55),(.neg 18),(.pos 15),(.pos 57)]),
   ((.exchange 18 56 3),[(.neg 56),(.neg 18),(.pos 15),(.pos 57)]),
   ((.exchange 19 41 6),[(.neg 41),(.neg 19),(.pos 1),(.pos 39)]),
   ((.exchange 20 41 6),[(.neg 41),(.neg 20),(.pos 1),(.pos 40)]),
   ((.exchange 21 36 6),[(.neg 36),(.neg 21),(.pos 1),(.pos 4),(.pos 41)]),
   ((.exchange 21 37 6),[(.neg 37),(.neg 21),(.pos 1),(.pos 4),(.pos 41)]),
   ((.exchange 21 38 6),[(.neg 38),(.neg 21),(.pos 4),(.pos 41)]),
   ((.exchange 21 39 6),[(.neg 39),(.neg 21),(.pos 1),(.pos 41)]),
   ((.exchange 21 40 6),[(.neg 40),(.neg 21),(.pos 1),(.pos 41)]),
   ((.exchange 21 42 6),[(.neg 42),(.neg 21),(.pos 1),(.pos 4),(.pos 41)]),
   ((.exchange 21 43 6),[(.neg 43),(.neg 21),(.pos 4),(.pos 41)]),
   ((.exchange 21 44 6),[(.neg 44),(.neg 21),(.pos 4),(.pos 41)]),
   ((.exchange 21 45 6),[(.neg 45),(.neg 21),(.pos 1),(.pos 11),(.pos 41)]),
   ((.exchange 21 46 6),[(.neg 46),(.neg 21),(.pos 1),(.pos 11),(.pos 41)]),
   ((.exchange 21 47 6),[(.neg 47),(.neg 21),(.pos 11),(.pos 41)]),
   ((.exchange 21 48 6),[(.neg 48),(.neg 21),(.pos 1),(.pos 4),(.pos 11),(.pos 41)]),
   ((.exchange 21 49 6),[(.neg 49),(.neg 21),(.pos 4),(.pos 11),(.pos 41)]),
   ((.exchange 21 50 6),[(.neg 50),(.neg 21),(.pos 4),(.pos 11),(.pos 41)]),
   ((.exchange 21 51 6),[(.neg 51),(.neg 21),(.pos 1),(.pos 11),(.pos 41)]),
   ((.exchange 21 52 6),[(.neg 52),(.neg 21),(.pos 11),(.pos 41)]),
   ((.exchange 21 53 6),[(.neg 53),(.neg 21),(.pos 11),(.pos 41)]),
   ((.exchange 22 41 6),[(.neg 41),(.neg 22),(.pos 2),(.pos 3),(.pos 42)]),
   ((.exchange 22 68 0),[(.neg 68),(.neg 22),(.pos 34),(.pos 64)]),
   ((.exchange 22 69 0),[(.neg 69),(.neg 22),(.pos 34),(.pos 64)]),
   ((.exchange 23 41 6),[(.neg 41),(.neg 23),(.pos 4),(.pos 43)]),
   ((.exchange 24 41 6),[(.neg 41),(.neg 24),(.pos 4),(.pos 44)]),
   ((.exchange 25 41 6),[(.neg 41),(.neg 25),(.pos 5),(.pos 9),(.pos 45)]),
   ((.exchange 26 41 6),[(.neg 41),(.neg 26),(.pos 5),(.pos 10),(.pos 46)]),
   ((.exchange 27 41 6),[(.neg 41),(.neg 27),(.pos 11),(.pos 47)]),
   ((.exchange 28 41 6),[(.neg 41),(.neg 28),(.pos 6),(.pos 7),(.pos 12),(.pos 48)]),
   ((.exchange 28 64 0),[(.neg 64),(.neg 28),(.pos 34),(.pos 68)]),
   ((.exchange 28 69 0),[(.neg 69),(.neg 28),(.pos 34),(.pos 68)]),
   ((.exchange 29 41 6),[(.neg 41),(.neg 29),(.pos 8),(.pos 13),(.pos 49)]),
   ((.exchange 30 41 6),[(.neg 41),(.neg 30),(.pos 8),(.pos 14),(.pos 50)]),
   ((.exchange 31 41 6),[(.neg 41),(.neg 31),(.pos 9),(.pos 10),(.pos 51)]),
   ((.exchange 31 64 0),[(.neg 64),(.neg 31),(.pos 34),(.pos 69)]),
   ((.exchange 31 68 0),[(.neg 68),(.neg 31),(.pos 34),(.pos 69)]),
   ((.exchange 32 41 6),[(.neg 41),(.neg 32),(.pos 11),(.pos 52)]),
   ((.exchange 33 41 6),[(.neg 41),(.neg 33),(.pos 11),(.pos 53)]),
   ((.exchange 35 16 7),[(.neg 35),(.neg 16),(.pos 0),(.pos 15)]),
   ((.exchange 54 16 7),[(.neg 54),(.neg 16),(.pos 12),(.pos 13),(.pos 34)]),
   ((.exchange 55 22 1),[(.neg 55),(.neg 22),(.pos 58),(.pos 61)]),
   ((.exchange 55 23 0),[(.neg 55),(.neg 23),(.pos 59),(.pos 62)]),
   ((.exchange 55 28 1),[(.neg 55),(.neg 28),(.pos 58),(.pos 65)]),
   ((.exchange 55 29 0),[(.neg 55),(.neg 29),(.pos 59),(.pos 66)]),
   ((.exchange 55 31 1),[(.neg 55),(.neg 31),(.pos 61),(.pos 65)]),
   ((.exchange 55 32 0),[(.neg 55),(.neg 32),(.pos 62),(.pos 66)]),
   ((.exchange 55 42 1),[(.neg 55),(.neg 42),(.pos 58),(.pos 61)]),
   ((.exchange 55 48 1),[(.neg 55),(.neg 48),(.pos 58),(.pos 65)]),
   ((.exchange 55 52 0),[(.neg 55),(.neg 52),(.pos 62),(.pos 66)]),
   ((.exchange 56 24 0),[(.neg 56),(.neg 24),(.pos 60),(.pos 63)]),
   ((.exchange 56 30 0),[(.neg 56),(.neg 30),(.pos 60),(.pos 67)]),
   ((.exchange 56 44 0),[(.neg 56),(.neg 44),(.pos 60),(.pos 63)]),
   ((.exchange 56 50 0),[(.neg 56),(.neg 50),(.pos 60),(.pos 67)]),
   ((.exchange 56 51 2),[(.neg 56),(.neg 51),(.pos 61),(.pos 65)]),
   ((.exchange 56 53 0),[(.neg 56),(.neg 53),(.pos 63),(.pos 67)]),
   ((.exchange 56 69 2),[(.neg 69),(.neg 56),(.pos 61),(.pos 65)]),
   ((.exchange 57 29 2),[(.neg 57),(.neg 29),(.pos 59),(.pos 66)]),
   ((.exchange 57 32 2),[(.neg 57),(.neg 32),(.pos 62),(.pos 66)]),
   ((.exchange 57 33 1),[(.neg 57),(.neg 33),(.pos 63),(.pos 67)]),
   ((.exchange 57 44 1),[(.neg 57),(.neg 44),(.pos 60),(.pos 63)]),
   ((.exchange 57 50 1),[(.neg 57),(.neg 50),(.pos 60),(.pos 67)]),
   ((.exchange 57 52 2),[(.neg 57),(.neg 52),(.pos 62),(.pos 66)]),
   ((.exchange 58 19 3),[(.neg 58),(.neg 19),(.pos 55),(.pos 61)]),
   ((.exchange 58 25 3),[(.neg 58),(.neg 25),(.pos 55),(.pos 65)]),
   ((.exchange 58 26 3),[(.neg 58),(.neg 26),(.pos 56),(.pos 65)]),
   ((.exchange 58 29 0),[(.neg 58),(.neg 29),(.pos 59),(.pos 68)]),
   ((.exchange 58 30 0),[(.neg 58),(.neg 30),(.pos 60),(.pos 68)]),
   ((.exchange 58 39 3),[(.neg 58),(.neg 39),(.pos 55),(.pos 61)]),
   ((.exchange 58 63 0),[(.neg 63),(.neg 58),(.pos 60),(.pos 64)]),
   ((.exchange 58 66 3),[(.neg 66),(.neg 58),(.pos 55),(.pos 65)]),
   ((.exchange 59 17 1),[(.neg 59),(.neg 17),(.pos 58),(.pos 60)]),
   ((.exchange 59 19 3),[(.neg 59),(.neg 19),(.pos 55),(.pos 62)]),
   ((.exchange 59 21 3),[(.neg 59),(.neg 21),(.pos 57),(.pos 62)]),
   ((.exchange 59 22 1),[(.neg 59),(.neg 22),(.pos 58),(.pos 64)]),
   ((.exchange 59 25 3),[(.neg 59),(.neg 25),(.pos 55),(.pos 66)]),
   ((.exchange 59 28 1),[(.neg 59),(.neg 28),(.pos 58),(.pos 68)]),
   ((.exchange 59 30 1),[(.neg 59),(.neg 30),(.pos 60),(.pos 68)]),
   ((.exchange 59 32 3),[(.neg 59),(.neg 32),(.pos 62),(.pos 66)]),
   ((.exchange 59 63 1),[(.neg 63),(.neg 59),(.pos 60),(.pos 64)]),
   ((.exchange 60 19 3),[(.neg 60),(.neg 19),(.pos 56),(.pos 57),(.pos 63)]),
   ((.exchange 60 23 2),[(.neg 60),(.neg 23),(.pos 59),(.pos 64)]),
   ((.exchange 60 25 2),[(.neg 60),(.neg 25),(.pos 58),(.pos 59),(.pos 68)]),
   ((.exchange 60 25 3),[(.neg 60),(.neg 25),(.pos 56),(.pos 57),(.pos 67)]),
   ((.exchange 60 26 3),[(.neg 60),(.neg 26),(.pos 56),(.pos 67)]),
   ((.exchange 60 27 3),[(.neg 60),(.neg 27),(.pos 57),(.pos 67)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_1 : List (Origin 70 87 × List Sat.Literal) :=
  [((.exchange 60 29 2),[(.neg 60),(.neg 29),(.pos 59),(.pos 68)]),
   ((.exchange 60 31 2),[(.neg 60),(.neg 31),(.pos 58),(.pos 64),(.pos 68)]),
   ((.exchange 60 32 2),[(.neg 60),(.neg 32),(.pos 59),(.pos 64),(.pos 68)]),
   ((.exchange 60 33 3),[(.neg 60),(.neg 33),(.pos 63),(.pos 67)]),
   ((.exchange 60 53 3),[(.neg 60),(.neg 53),(.pos 63),(.pos 67)]),
   ((.exchange 60 55 2),[(.neg 60),(.neg 55),(.pos 58),(.pos 59)]),
   ((.exchange 60 61 3),[(.neg 61),(.neg 60),(.pos 56),(.pos 63)]),
   ((.exchange 60 62 3),[(.neg 62),(.neg 60),(.pos 57),(.pos 63)]),
   ((.exchange 61 21 0),[(.neg 61),(.neg 21),(.pos 62),(.pos 63)]),
   ((.exchange 61 24 0),[(.neg 61),(.neg 24),(.pos 63),(.pos 64)]),
   ((.exchange 61 38 4),[(.neg 61),(.neg 38),(.pos 55),(.pos 56),(.pos 58)]),
   ((.exchange 61 46 4),[(.neg 61),(.neg 46),(.pos 56),(.pos 65)]),
   ((.exchange 61 50 4),[(.neg 61),(.neg 50),(.pos 56),(.pos 58),(.pos 65)]),
   ((.exchange 61 57 0),[(.neg 61),(.neg 57),(.pos 62),(.pos 63)]),
   ((.exchange 61 59 4),[(.neg 61),(.neg 59),(.pos 55),(.pos 58)]),
   ((.exchange 61 67 0),[(.neg 67),(.neg 61),(.pos 63),(.pos 69)]),
   ((.exchange 62 24 1),[(.neg 62),(.neg 24),(.pos 63),(.pos 64)]),
   ((.exchange 62 25 4),[(.neg 62),(.neg 25),(.pos 55),(.pos 66)]),
   ((.exchange 62 27 4),[(.neg 62),(.neg 27),(.pos 57),(.pos 66)]),
   ((.exchange 62 50 4),[(.neg 62),(.neg 50),(.pos 57),(.pos 59),(.pos 66)]),
   ((.exchange 62 60 1),[(.neg 62),(.neg 60),(.pos 63),(.pos 64)]),
   ((.exchange 62 60 4),[(.neg 62),(.neg 60),(.pos 57),(.pos 59)]),
   ((.exchange 62 67 1),[(.neg 67),(.neg 62),(.pos 63),(.pos 69)]),
   ((.exchange 62 68 4),[(.neg 68),(.neg 62),(.pos 59),(.pos 66)]),
   ((.exchange 63 27 4),[(.neg 63),(.neg 27),(.pos 57),(.pos 67)]),
   ((.exchange 63 31 2),[(.neg 63),(.neg 31),(.pos 61),(.pos 69)]),
   ((.exchange 63 32 2),[(.neg 63),(.neg 32),(.pos 62),(.pos 69)]),
   ((.exchange 63 38 4),[(.neg 63),(.neg 38),(.pos 57),(.pos 60)]),
   ((.exchange 63 50 4),[(.neg 63),(.neg 50),(.pos 60),(.pos 67)]),
   ((.exchange 63 52 2),[(.neg 63),(.neg 52),(.pos 62),(.pos 69)]),
   ((.exchange 63 55 2),[(.neg 63),(.neg 55),(.pos 61),(.pos 62)]),
   ((.exchange 63 65 2),[(.neg 65),(.neg 63),(.pos 61),(.pos 69)]),
   ((.exchange 63 66 2),[(.neg 66),(.neg 63),(.pos 62),(.pos 69)]),
   ((.exchange 64 16 4),[(.neg 64),(.neg 16),(.pos 58),(.pos 59)]),
   ((.exchange 64 17 4),[(.neg 64),(.neg 17),(.pos 58),(.pos 60)]),
   ((.exchange 64 18 4),[(.neg 64),(.neg 18),(.pos 59),(.pos 60)]),
   ((.exchange 64 20 3),[(.neg 64),(.neg 20),(.pos 61),(.pos 63)]),
   ((.exchange 64 21 3),[(.neg 64),(.neg 21),(.pos 62),(.pos 63)]),
   ((.exchange 64 40 3),[(.neg 64),(.neg 40),(.pos 61),(.pos 63)]),
   ((.exchange 64 41 3),[(.neg 64),(.neg 41),(.pos 62),(.pos 63)]),
   ((.exchange 64 56 3),[(.neg 64),(.neg 56),(.pos 61),(.pos 63)]),
   ((.exchange 65 22 5),[(.neg 65),(.neg 22),(.pos 58),(.pos 61)]),
   ((.exchange 65 24 0),[(.neg 65),(.neg 24),(.pos 67),(.pos 68),(.pos 69)]),
   ((.exchange 65 38 5),[(.neg 65),(.neg 38),(.pos 55),(.pos 56),(.pos 58)]),
   ((.exchange 65 42 5),[(.neg 65),(.neg 42),(.pos 58),(.pos 61)]),
   ((.exchange 65 47 0),[(.neg 65),(.neg 47),(.pos 66),(.pos 67)]),
   ((.exchange 65 53 0),[(.neg 65),(.neg 53),(.pos 67),(.pos 69)]),
   ((.exchange 65 60 0),[(.neg 65),(.neg 60),(.pos 67),(.pos 68)]),
   ((.exchange 66 16 5),[(.neg 66),(.neg 16),(.pos 55),(.pos 59)]),
   ((.exchange 66 19 5),[(.neg 66),(.neg 19),(.pos 55),(.pos 62)]),
   ((.exchange 66 24 1),[(.neg 66),(.neg 24),(.pos 67),(.pos 68),(.pos 69)]),
   ((.exchange 66 30 1),[(.neg 66),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 66 38 5),[(.neg 66),(.neg 38),(.pos 57),(.pos 59)]),
   ((.exchange 66 43 5),[(.neg 66),(.neg 43),(.pos 59),(.pos 62)]),
   ((.exchange 66 53 1),[(.neg 66),(.neg 53),(.pos 67),(.pos 69)]),
   ((.exchange 66 58 1),[(.neg 66),(.neg 58),(.pos 65),(.pos 68)]),
   ((.exchange 66 58 5),[(.neg 66),(.neg 58),(.pos 55),(.pos 59)]),
   ((.exchange 66 60 1),[(.neg 66),(.neg 60),(.pos 67),(.pos 68)]),
   ((.exchange 66 60 5),[(.neg 66),(.neg 60),(.pos 57),(.pos 59)]),
   ((.exchange 67 16 5),[(.neg 67),(.neg 16),(.pos 56),(.pos 57),(.pos 60)]),
   ((.exchange 67 17 5),[(.neg 67),(.neg 17),(.pos 56),(.pos 60)]),
   ((.exchange 67 18 5),[(.neg 67),(.neg 18),(.pos 57),(.pos 60)]),
   ((.exchange 67 19 5),[(.neg 67),(.neg 19),(.pos 56),(.pos 57),(.pos 63)]),
   ((.exchange 67 20 5),[(.neg 67),(.neg 20),(.pos 56),(.pos 63)]),
   ((.exchange 67 21 5),[(.neg 67),(.neg 21),(.pos 57),(.pos 63)]),
   ((.exchange 67 24 5),[(.neg 67),(.neg 24),(.pos 60),(.pos 63)]),
   ((.exchange 67 25 2),[(.neg 67),(.neg 25),(.pos 65),(.pos 66)]),
   ((.exchange 67 29 2),[(.neg 67),(.neg 29),(.pos 66),(.pos 68)]),
   ((.exchange 67 31 2),[(.neg 67),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 67 32 2),[(.neg 67),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 67 64 5),[(.neg 67),(.neg 64),(.pos 60),(.pos 63)]),
   ((.exchange 68 17 5),[(.neg 68),(.neg 17),(.pos 58),(.pos 60)]),
   ((.exchange 68 18 5),[(.neg 68),(.neg 18),(.pos 59),(.pos 60)]),
   ((.exchange 68 19 5),[(.neg 68),(.neg 19),(.pos 58),(.pos 59),(.pos 64)]),
   ((.exchange 68 26 3),[(.neg 68),(.neg 26),(.pos 65),(.pos 67)]),
   ((.exchange 68 27 3),[(.neg 68),(.neg 27),(.pos 66),(.pos 67)]),
   ((.exchange 68 41 3),[(.neg 68),(.neg 41),(.pos 66),(.pos 67),(.pos 69)]),
   ((.exchange 68 56 3),[(.neg 68),(.neg 56),(.pos 65),(.pos 67)]),
   ((.exchange 69 19 5),[(.neg 69),(.neg 19),(.pos 61),(.pos 62)]),
   ((.exchange 69 39 5),[(.neg 69),(.neg 39),(.pos 61),(.pos 62)]),
   ((.exchange 69 40 5),[(.neg 69),(.neg 40),(.pos 61),(.pos 63)]),
   ((.exchange 69 41 5),[(.neg 69),(.neg 41),(.pos 62),(.pos 63)]),
   ((.exchange 69 47 4),[(.neg 69),(.neg 47),(.pos 66),(.pos 67)]),
   ((.exchange 69 56 4),[(.neg 69),(.neg 56),(.pos 65),(.pos 67)]),
   ((.exchange 69 57 4),[(.neg 69),(.neg 57),(.pos 66),(.pos 67)]),
   (.newPoint,[(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 0),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 61),(.pos 65)]),
   ((.excluded 1),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 58),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 59),(.pos 62),(.pos 66)]),
   ((.excluded 2),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 3),[(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 64),(.pos 68),(.pos 69)]),
   ((.excluded 4),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 5),[(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 68),(.pos 69)]),
   ((.excluded 6),[(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 68),(.pos 69)]),
   ((.excluded 7),[(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 8),[(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 64),(.pos 68),(.pos 69)]),
   ((.excluded 9),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 58),(.pos 62),(.pos 67)]),
   ((.excluded 10),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 58),(.pos 62)]),
   ((.excluded 11),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 58),(.pos 67)]),
   ((.excluded 12),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 58),(.pos 63),(.pos 66)]),
   ((.excluded 13),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 58),(.pos 63)]),
   ((.excluded 14),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 58),(.pos 66)]),
   ((.excluded 15),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 58)]),
   ((.excluded 16),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 62),(.pos 67)]),
   ((.excluded 17),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 60),(.pos 62),(.pos 65)]),
   ((.excluded 18),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 60),(.pos 62)]),
   ((.excluded 19),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 62),(.pos 65)]),
   ((.excluded 20),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 62)]),
   ((.excluded 21),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 59),(.pos 61),(.pos 67)]),
   ((.excluded 22),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 59),(.pos 67)]),
   ((.excluded 23),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 61),(.pos 67)]),
   ((.excluded 24),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 67)]),
   ((.excluded 25),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 59),(.pos 61)]),
   ((.excluded 26),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 59),(.pos 63),(.pos 65)]),
   ((.excluded 27),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 59),(.pos 63)]),
   ((.excluded 28),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 59),(.pos 65)]),
   ((.excluded 29),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 59)]),
   ((.excluded 30),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 60),(.pos 61),(.pos 66)]),
   ((.excluded 31),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 60),(.pos 61)]),
   ((.excluded 32),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 61),(.pos 66)]),
   ((.excluded 33),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 61)]),
   ((.excluded 34),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 60),(.pos 65)]),
   ((.excluded 35),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 60),(.pos 66)]),
   ((.excluded 36),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 60)]),
   ((.excluded 37),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 63),(.pos 65)]),
   ((.excluded 38),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 65)]),
   ((.excluded 39),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 63),(.pos 66)]),
   ((.excluded 40),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 63)]),
   ((.excluded 41),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 66)])]

theorem certificates_1_valid : ∀ oc ∈ certificates_1,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_2 : List (Origin 70 87 × List Sat.Literal) :=
  [((.excluded 42),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54)]),
   ((.excluded 43),[(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 44),[(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 64),(.pos 68),(.pos 69)]),
   ((.excluded 45),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 61),(.pos 65)]),
   ((.excluded 46),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 58),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 59),(.pos 62),(.pos 66)]),
   ((.excluded 47),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 48),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 54),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 49),[(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 54),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 68),(.pos 69)]),
   ((.excluded 50),[(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 54),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 68),(.pos 69)]),
   ((.excluded 51),[(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 54),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 52),[(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 54),(.pos 64),(.pos 68),(.pos 69)]),
   ((.excluded 53),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 54),(.pos 58),(.pos 62),(.pos 67)]),
   ((.excluded 54),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 54),(.pos 58),(.pos 62)]),
   ((.excluded 55),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 54),(.pos 58),(.pos 67)]),
   ((.excluded 56),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 54),(.pos 58),(.pos 63),(.pos 66)]),
   ((.excluded 57),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 54),(.pos 58),(.pos 63)]),
   ((.excluded 58),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 54),(.pos 58),(.pos 66)]),
   ((.excluded 59),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 54),(.pos 58)]),
   ((.excluded 60),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 54),(.pos 62),(.pos 67)]),
   ((.excluded 61),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 54),(.pos 60),(.pos 62),(.pos 65)]),
   ((.excluded 62),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 54),(.pos 60),(.pos 62)]),
   ((.excluded 63),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 54),(.pos 62),(.pos 65)]),
   ((.excluded 64),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 54),(.pos 62)]),
   ((.excluded 65),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 54),(.pos 59),(.pos 61),(.pos 67)]),
   ((.excluded 66),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 54),(.pos 59),(.pos 67)]),
   ((.excluded 67),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 54),(.pos 61),(.pos 67)]),
   ((.excluded 68),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 54),(.pos 67)]),
   ((.excluded 69),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 54),(.pos 59),(.pos 61)]),
   ((.excluded 70),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 54),(.pos 59),(.pos 63),(.pos 65)]),
   ((.excluded 71),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 54),(.pos 59),(.pos 63)]),
   ((.excluded 72),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 54),(.pos 59),(.pos 65)]),
   ((.excluded 73),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 54),(.pos 59)]),
   ((.excluded 74),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 54),(.pos 60),(.pos 61),(.pos 66)]),
   ((.excluded 75),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 54),(.pos 60),(.pos 61)]),
   ((.excluded 76),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 54),(.pos 61),(.pos 66)]),
   ((.excluded 77),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 54),(.pos 61)]),
   ((.excluded 78),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 54),(.pos 60),(.pos 65)]),
   ((.excluded 79),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 54),(.pos 60),(.pos 66)]),
   ((.excluded 80),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 54),(.pos 60)]),
   ((.excluded 81),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 54),(.pos 63),(.pos 65)]),
   ((.excluded 82),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 54),(.pos 65)]),
   ((.excluded 83),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 54),(.pos 63),(.pos 66)]),
   ((.excluded 84),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 54),(.pos 63)]),
   ((.excluded 85),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 54),(.pos 66)]),
   ((.excluded 86),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 54)])]

theorem certificates_2_valid : ∀ oc ∈ certificates_2,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



theorem witness_0 : ∀ j : Fin 87,
    let w : Fin 87 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 87,
      let w : Fin 87 := ⟨0 + j.val,by omega⟩
      target w < MatroidCatalogue.count 8 4 ∧
        Papers.RationalityTen.MatroidChecked.FastSemanticChecks.RawWitness 8 (N7R4.familyMasks.get 22)
        (fun i : Fin 70 => N8R4.gridMasks.get i.val) newIndex (models w)
        (N8R4.familyMasks.get (target w)) (permutation w) := by
    refine (Fin.forall_fin_add (m := 43) (n := 44) _).2 ⟨?_, ?_⟩
    · refine (Fin.forall_fin_add (m := 21) (n := 22) _).2 ⟨?_, ?_⟩
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
    · refine (Fin.forall_fin_add (m := 22) (n := 22) _).2 ⟨?_, ?_⟩
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


end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C22

/- Source: MatroidCatalogue/Cases/N8R4C22Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C22

noncomputable def certificates : List (Origin 70 87 × List Sat.Literal) :=
  certificates_0 ++ certificates_1 ++ certificates_2

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  intro oc hoc
  simp only [certificates,List.mem_append,or_assoc] at hoc
  rcases hoc with h0 | h1 | h2
  · exact certificates_0_valid oc h0
  · exact certificates_1_valid oc h1
  · exact certificates_2_valid oc h2

theorem models_valid : ∀ w : Fin 87,
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 87) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 8) 4)
    (hold : M.bases.filter ((7 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 8 4, IsomorphicWithin 8 M.bases B := by
  apply extension_covered_of_certificate (n:=7) (r:=4) (by decide)
    catalogue old U newIndex models certificates
    N8R4.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C22.formula []
    exact Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C22.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 8 4 (target w),family_mem 8 4 (target w) hw.1,?_⟩
    exact validWitness_sound 8 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C22


end
end
end BundlePart8

section BundlePart9
/- Source: MatroidChecked/SemanticChunks/Cases03Part09.lean -/




@[expose] public section
noncomputable section

/- Source: MatroidCatalogue/Cases/N8R4C23Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C23

abbrev U := N8R4.grid
noncomputable def old : Finset (Finset (Fin 8)) := N7R4.family 23
noncomputable def newIndexTree : Table ℕ := (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf 35) (.leaf 36)) (.node 3 (.leaf 37) (.leaf 38))) (.node 6 (.node 5 (.leaf 39) (.leaf 40)) (.node 7 (.leaf 41) (.leaf 42)))) (.node 12 (.node 10 (.node 9 (.leaf 43) (.leaf 44)) (.node 11 (.leaf 45) (.leaf 46))) (.node 14 (.node 13 (.leaf 47) (.leaf 48)) (.node 15 (.leaf 49) (.node 16 (.leaf 50) (.leaf 51)))))) (.node 26 (.node 21 (.node 19 (.node 18 (.leaf 52) (.leaf 53)) (.node 20 (.leaf 54) (.leaf 55))) (.node 23 (.node 22 (.leaf 56) (.leaf 57)) (.node 24 (.leaf 58) (.node 25 (.leaf 59) (.leaf 60))))) (.node 30 (.node 28 (.node 27 (.leaf 61) (.leaf 62)) (.node 29 (.leaf 63) (.leaf 64))) (.node 32 (.node 31 (.leaf 65) (.leaf 66)) (.node 33 (.leaf 67) (.node 34 (.leaf 68) (.leaf 69)))))))
noncomputable def newIndex (i : Fin 35) : Fin 70 := Fin.ofNat 70 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 56 (.node 28 (.node 14 (.node 7 (.node 3 (.node 1 (.leaf (33202110464,45,4151504)) (.node 2 (.leaf (32052871168,45,4151490)) (.leaf (29754392576,45,4151322)))) (.node 5 (.node 4 (.leaf (33814478848,50,2054353)) (.leaf (25761415168,50,2025681))) (.node 6 (.leaf (17171480576,50,2018513)) (.leaf (34351349760,52,8345736))))) (.node 10 (.node 8 (.leaf (25173164032,54,4149530)) (.node 9 (.leaf (16172187648,54,4131610)) (.leaf (32748077056,64,4151504)))) (.node 12 (.node 11 (.leaf (31674335232,64,4151490)) (.leaf (29526851584,64,4151322))) (.node 13 (.leaf (33821818880,67,12535432)) (.leaf (1072693248,54,3959578)))))) (.node 21 (.node 17 (.node 15 (.leaf (25701646336,64,4122832)) (.node 16 (.leaf (25634537472,64,4122818)) (.leaf (25500319744,64,4122650)))) (.node 19 (.node 18 (.leaf (25768755200,67,12478088)) (.leaf (17170432000,64,4115664))) (.node 20 (.leaf (17162043392,64,4115650)) (.leaf (17145266176,64,4115482))))) (.node 24 (.node 22 (.leaf (17178820608,67,12467336)) (.node 23 (.leaf (29921116160,62,2018513)) (.leaf (34216083456,63,6248648)))) (.node 26 (.node 25 (.leaf (30055333888,63,6219864)) (.leaf (31934382080,62,1989841))) (.node 27 (.leaf (34081865728,63,6248536)) (.leaf (32202817536,63,6219976))))))) (.node 42 (.node 35 (.node 31 (.node 29 (.leaf (34350301184,66,10442376)) (.node 30 (.leaf (29929504768,63,6212675)) (.leaf (33117175808,62,2050769)))) (.node 33 (.node 32 (.leaf (34190917632,63,6244931)) (.leaf (33150730240,63,6184136))) (.node 34 (.leaf (34224472064,66,10435201)) (.leaf (29979836416,62,2025681))))) (.node 38 (.node 36 (.leaf (30046945280,63,6219843)) (.node 37 (.leaf (29996613632,63,6212696)) (.leaf (30063722496,66,10349073)))) (.node 40 (.node 39 (.leaf (34274803712,63,6245064)) (.leaf (32999735296,62,2054353))) (.node 41 (.leaf (34073477120,63,6248515)) (.leaf (33268170752,63,6187720)))))) (.node 49 (.node 45 (.node 43 (.leaf (34341912576,66,10442369)) (.node 44 (.leaf (32110542848,62,1993425)) (.leaf (34258026496,63,6244952)))) (.node 47 (.node 46 (.leaf (32144097280,63,6212808)) (.leaf (34291580928,66,10435208))) (.node 48 (.leaf (33251393536,63,6187608)) (.leaf (32177651712,63,6187587))))) (.node 52 (.node 50 (.leaf (34325135360,66,10442257)) (.node 51 (.leaf (33016512512,63,6184024)) (.leaf (33284947968,66,10349192)))) (.node 54 (.node 53 (.leaf (31942770688,63,6184003)) (.leaf (34090254336,66,10435089))) (.node 55 (.leaf (32211206144,66,10349185)) (.leaf (34358689792,68,14599816)))))))) (.node 84 (.node 70 (.node 63 (.node 59 (.node 57 (.leaf (1048574,221,9431688)) (.node 58 (.leaf (33203159038,222,16434824)) (.leaf (32053919742,222,16434817)))) (.node 61 (.node 60 (.leaf (29755441150,222,16434705)) (.leaf (33815527422,223,16434824))) (.node 62 (.leaf (25762463742,223,16406152)) (.leaf (17172529150,223,16398984))))) (.node 66 (.node 64 (.leaf (34352398334,224,16434824)) (.node 65 (.leaf (25174212606,225,16433361)) (.leaf (16173236222,225,16419025)))) (.node 68 (.node 67 (.leaf (32749125630,226,16373896)) (.leaf (31675383806,226,16373889))) (.node 69 (.leaf (29527900158,226,16373777)) (.leaf (33822867454,227,16434824)))))) (.node 77 (.node 73 (.node 71 (.leaf (1073741822,225,16275665)) (.node 72 (.leaf (25702694910,226,16431240)) (.leaf (25635586046,226,16431233)))) (.node 75 (.node 74 (.leaf (25501368318,226,16431121)) (.leaf (25769803774,227,16406152))) (.node 76 (.leaf (17171480574,226,16434824)) (.leaf (17163091966,226,16434817))))) (.node 80 (.node 78 (.leaf (17146314750,226,16434705)) (.node 79 (.leaf (17179869182,227,16398984)) (.leaf (29922164734,228,16434824)))) (.node 82 (.node 81 (.leaf (34217132030,229,16434824)) (.leaf (30056382462,229,16406096))) (.node 83 (.leaf (31935430654,228,16406152)) (.leaf (34082914302,229,16434768))))))) (.node 98 (.node 91 (.node 87 (.node 85 (.leaf (32203866110,229,16406152)) (.node 86 (.leaf (34351349758,230,16434824)) (.leaf (29930553342,229,16398914)))) (.node 89 (.node 88 (.leaf (33118224382,228,16370312)) (.leaf (34191966206,229,16431170))) (.node 90 (.leaf (33151778814,229,16370312)) (.leaf (34225520638,230,16431233))))) (.node 94 (.node 92 (.leaf (29980884990,228,16431240)) (.node 93 (.leaf (30047993854,229,16406082)) (.leaf (29997662206,229,16398928)))) (.node 96 (.node 95 (.leaf (30064771070,230,16373777)) (.leaf (34275852286,229,16431240))) (.node 97 (.leaf (33000783870,228,16373896)) (.leaf (34074525694,229,16434754)))))) (.node 105 (.node 101 (.node 99 (.leaf (33269219326,229,16373896)) (.node 100 (.leaf (34342961150,230,16434817)) (.leaf (32111591422,228,16398984)))) (.node 103 (.node 102 (.leaf (34259075070,229,16431184)) (.leaf (32145145854,229,16398984))) (.node 104 (.leaf (34292629502,230,16431240)) (.leaf (33252442110,229,16373840))))) (.node 109 (.node 107 (.node 106 (.leaf (32178700286,229,16373826)) (.leaf (34326183934,230,16434705))) (.node 108 (.leaf (33017561086,229,16370256)) (.leaf (33285996542,230,16373896)))) (.node 111 (.node 110 (.leaf (31943819262,229,16370242)) (.leaf (34091302910,230,16431121))) (.node 112 (.leaf (32212254718,230,16373889)) (.leaf (34359738366,231,16434824)))))))))

noncomputable def models (i : Fin 113) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 113) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 113) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 70, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (7 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 70, (7 : Fin 8) ∈ U i → ∃ j : Fin 35, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C23

/- Source: MatroidCatalogue/Cases/N8R4C23Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C23


noncomputable def certificates_0 : List (Origin 70 113 × List Sat.Literal) :=
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
   ((.fixed 16),[(.pos 16)]),
   ((.fixed 17),[(.pos 17)]),
   ((.fixed 18),[(.pos 18)]),
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
   ((.exchange 16 41 6),[(.neg 41),(.neg 16),(.pos 0),(.pos 2),(.pos 36)]),
   ((.exchange 16 56 3),[(.neg 56),(.neg 16),(.pos 15),(.pos 55)]),
   ((.exchange 16 57 3),[(.neg 57),(.neg 16),(.pos 15),(.pos 55)]),
   ((.exchange 17 41 6),[(.neg 41),(.neg 17),(.pos 0),(.pos 3),(.pos 37)]),
   ((.exchange 17 55 3),[(.neg 55),(.neg 17),(.pos 15),(.pos 56)]),
   ((.exchange 17 57 3),[(.neg 57),(.neg 17),(.pos 15),(.pos 56)]),
   ((.exchange 18 41 6),[(.neg 41),(.neg 18),(.pos 4),(.pos 38)]),
   ((.exchange 18 55 3),[(.neg 55),(.neg 18),(.pos 15),(.pos 57)]),
   ((.exchange 18 56 3),[(.neg 56),(.neg 18),(.pos 15),(.pos 57)]),
   ((.exchange 19 41 6),[(.neg 41),(.neg 19),(.pos 1),(.pos 39)]),
   ((.exchange 20 41 6),[(.neg 41),(.neg 20),(.pos 1),(.pos 40)]),
   ((.exchange 21 36 6),[(.neg 36),(.neg 21),(.pos 1),(.pos 4),(.pos 41)]),
   ((.exchange 21 37 6),[(.neg 37),(.neg 21),(.pos 1),(.pos 4),(.pos 41)]),
   ((.exchange 21 38 6),[(.neg 38),(.neg 21),(.pos 4),(.pos 41)]),
   ((.exchange 21 39 6),[(.neg 39),(.neg 21),(.pos 1),(.pos 41)]),
   ((.exchange 21 40 6),[(.neg 40),(.neg 21),(.pos 1),(.pos 41)]),
   ((.exchange 21 42 6),[(.neg 42),(.neg 21),(.pos 1),(.pos 4),(.pos 41)]),
   ((.exchange 21 43 6),[(.neg 43),(.neg 21),(.pos 4),(.pos 41)]),
   ((.exchange 21 44 6),[(.neg 44),(.neg 21),(.pos 4),(.pos 41)]),
   ((.exchange 21 45 6),[(.neg 45),(.neg 21),(.pos 1),(.pos 11),(.pos 41)]),
   ((.exchange 21 46 6),[(.neg 46),(.neg 21),(.pos 1),(.pos 11),(.pos 41)]),
   ((.exchange 21 47 6),[(.neg 47),(.neg 21),(.pos 11),(.pos 41)]),
   ((.exchange 21 48 6),[(.neg 48),(.neg 21),(.pos 1),(.pos 4),(.pos 11),(.pos 41)]),
   ((.exchange 21 49 6),[(.neg 49),(.neg 21),(.pos 4),(.pos 11),(.pos 41)]),
   ((.exchange 21 50 6),[(.neg 50),(.neg 21),(.pos 4),(.pos 11),(.pos 41)]),
   ((.exchange 21 51 6),[(.neg 51),(.neg 21),(.pos 1),(.pos 11),(.pos 41)]),
   ((.exchange 21 52 6),[(.neg 52),(.neg 21),(.pos 11),(.pos 41)]),
   ((.exchange 21 53 6),[(.neg 53),(.neg 21),(.pos 11),(.pos 41)]),
   ((.exchange 21 54 6),[(.neg 54),(.neg 21),(.pos 4),(.pos 11),(.pos 41)]),
   ((.exchange 22 41 6),[(.neg 41),(.neg 22),(.pos 2),(.pos 3),(.pos 42)]),
   ((.exchange 23 41 6),[(.neg 41),(.neg 23),(.pos 4),(.pos 43)]),
   ((.exchange 24 41 6),[(.neg 41),(.neg 24),(.pos 4),(.pos 44)]),
   ((.exchange 25 41 6),[(.neg 41),(.neg 25),(.pos 5),(.pos 9),(.pos 45)]),
   ((.exchange 26 41 6),[(.neg 41),(.neg 26),(.pos 5),(.pos 10),(.pos 46)]),
   ((.exchange 27 41 6),[(.neg 41),(.neg 27),(.pos 11),(.pos 47)]),
   ((.exchange 28 41 6),[(.neg 41),(.neg 28),(.pos 6),(.pos 7),(.pos 12),(.pos 48)]),
   ((.exchange 29 41 6),[(.neg 41),(.neg 29),(.pos 8),(.pos 13),(.pos 49)]),
   ((.exchange 30 41 6),[(.neg 41),(.neg 30),(.pos 8),(.pos 14),(.pos 50)]),
   ((.exchange 31 41 6),[(.neg 41),(.neg 31),(.pos 9),(.pos 10),(.pos 51)]),
   ((.exchange 32 41 6),[(.neg 41),(.neg 32),(.pos 11),(.pos 52)]),
   ((.exchange 33 41 6),[(.neg 41),(.neg 33),(.pos 11),(.pos 53)]),
   ((.exchange 34 41 6),[(.neg 41),(.neg 34),(.pos 13),(.pos 14),(.pos 54)]),
   ((.exchange 35 16 7),[(.neg 35),(.neg 16),(.pos 0),(.pos 15)]),
   ((.exchange 55 22 1),[(.neg 55),(.neg 22),(.pos 58),(.pos 61)]),
   ((.exchange 55 23 0),[(.neg 55),(.neg 23),(.pos 59),(.pos 62)]),
   ((.exchange 55 28 1),[(.neg 55),(.neg 28),(.pos 58),(.pos 65)]),
   ((.exchange 55 29 0),[(.neg 55),(.neg 29),(.pos 59),(.pos 66)]),
   ((.exchange 55 31 1),[(.neg 55),(.neg 31),(.pos 61),(.pos 65)]),
   ((.exchange 55 32 0),[(.neg 55),(.neg 32),(.pos 62),(.pos 66)]),
   ((.exchange 56 28 2),[(.neg 56),(.neg 28),(.pos 58),(.pos 65)]),
   ((.exchange 56 31 2),[(.neg 56),(.neg 31),(.pos 61),(.pos 65)]),
   ((.exchange 56 33 0),[(.neg 56),(.neg 33),(.pos 63),(.pos 67)]),
   ((.exchange 57 33 1),[(.neg 57),(.neg 33),(.pos 63),(.pos 67)]),
   ((.exchange 57 69 2),[(.neg 69),(.neg 57),(.pos 62),(.pos 66)]),
   ((.exchange 58 18 0),[(.neg 58),(.neg 18),(.pos 59),(.pos 60)]),
   ((.exchange 58 23 0),[(.neg 58),(.neg 23),(.pos 59),(.pos 64)]),
   ((.exchange 58 24 0),[(.neg 58),(.neg 24),(.pos 60),(.pos 64)]),
   ((.exchange 58 25 3),[(.neg 58),(.neg 25),(.pos 55),(.pos 65)]),
   ((.exchange 58 27 3),[(.neg 58),(.neg 27),(.pos 55),(.pos 56),(.pos 65)]),
   ((.exchange 58 29 0),[(.neg 58),(.neg 29),(.pos 59),(.pos 68)]),
   ((.exchange 58 30 0),[(.neg 58),(.neg 30),(.pos 60),(.pos 68)]),
   ((.exchange 58 31 3),[(.neg 58),(.neg 31),(.pos 61),(.pos 65)]),
   ((.exchange 58 34 0),[(.neg 58),(.neg 34),(.pos 64),(.pos 68)]),
   ((.exchange 58 46 3),[(.neg 58),(.neg 46),(.pos 56),(.pos 65)]),
   ((.exchange 58 62 3),[(.neg 62),(.neg 58),(.pos 55),(.pos 61)]),
   ((.exchange 58 66 0),[(.neg 66),(.neg 58),(.pos 59),(.pos 68)]),
   ((.exchange 58 67 0),[(.neg 67),(.neg 58),(.pos 60),(.pos 68)]),
   ((.exchange 59 17 1),[(.neg 59),(.neg 17),(.pos 58),(.pos 60)]),
   ((.exchange 59 22 1),[(.neg 59),(.neg 22),(.pos 58),(.pos 64)]),
   ((.exchange 59 24 1),[(.neg 59),(.neg 24),(.pos 60),(.pos 64)]),
   ((.exchange 59 25 3),[(.neg 59),(.neg 25),(.pos 55),(.pos 66)]),
   ((.exchange 59 26 3),[(.neg 59),(.neg 26),(.pos 55),(.pos 57),(.pos 66)]),
   ((.exchange 59 28 1),[(.neg 59),(.neg 28),(.pos 58),(.pos 68)]),
   ((.exchange 59 30 1),[(.neg 59),(.neg 30),(.pos 60),(.pos 68)]),
   ((.exchange 59 34 1),[(.neg 59),(.neg 34),(.pos 64),(.pos 68)]),
   ((.exchange 59 41 3),[(.neg 59),(.neg 41),(.pos 57),(.pos 62)]),
   ((.exchange 59 56 1),[(.neg 59),(.neg 56),(.pos 58),(.pos 60)]),
   ((.exchange 59 61 1),[(.neg 61),(.neg 59),(.pos 58),(.pos 64)]),
   ((.exchange 59 67 1),[(.neg 67),(.neg 59),(.pos 60),(.pos 68)]),
   ((.exchange 59 69 3),[(.neg 69),(.neg 59),(.pos 62),(.pos 66)]),
   ((.exchange 60 16 2),[(.neg 60),(.neg 16),(.pos 58),(.pos 59)]),
   ((.exchange 60 19 3),[(.neg 60),(.neg 19),(.pos 56),(.pos 57),(.pos 63)]),
   ((.exchange 60 21 3),[(.neg 60),(.neg 21),(.pos 57),(.pos 63)]),
   ((.exchange 60 22 2),[(.neg 60),(.neg 22),(.pos 58),(.pos 64)]),
   ((.exchange 60 25 3),[(.neg 60),(.neg 25),(.pos 56),(.pos 57),(.pos 67)]),
   ((.exchange 60 27 3),[(.neg 60),(.neg 27),(.pos 57),(.pos 67)]),
   ((.exchange 60 28 2),[(.neg 60),(.neg 28),(.pos 58),(.pos 68)]),
   ((.exchange 60 29 2),[(.neg 60),(.neg 29),(.pos 59),(.pos 68)]),
   ((.exchange 60 34 2),[(.neg 60),(.neg 34),(.pos 64),(.pos 68)]),
   ((.exchange 60 36 2),[(.neg 60),(.neg 36),(.pos 58),(.pos 59)]),
   ((.exchange 60 49 2),[(.neg 60),(.neg 49),(.pos 59),(.pos 68)]),
   ((.exchange 60 69 2),[(.neg 69),(.neg 60),(.pos 64),(.pos 68)]),
   ((.exchange 61 24 0),[(.neg 61),(.neg 24),(.pos 63),(.pos 64)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_1 : List (Origin 70 113 × List Sat.Literal) :=
  [((.exchange 61 27 4),[(.neg 61),(.neg 27),(.pos 55),(.pos 56),(.pos 65)]),
   ((.exchange 61 32 0),[(.neg 61),(.neg 32),(.pos 62),(.pos 69)]),
   ((.exchange 61 33 0),[(.neg 61),(.neg 33),(.pos 63),(.pos 69)]),
   ((.exchange 61 34 0),[(.neg 61),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 61 43 0),[(.neg 61),(.neg 43),(.pos 62),(.pos 64)]),
   ((.exchange 61 44 0),[(.neg 61),(.neg 44),(.pos 63),(.pos 64)]),
   ((.exchange 61 59 4),[(.neg 61),(.neg 59),(.pos 55),(.pos 58)]),
   ((.exchange 61 68 0),[(.neg 68),(.neg 61),(.pos 64),(.pos 69)]),
   ((.exchange 62 18 4),[(.neg 62),(.neg 18),(.pos 57),(.pos 59)]),
   ((.exchange 62 20 1),[(.neg 62),(.neg 20),(.pos 61),(.pos 63)]),
   ((.exchange 62 22 1),[(.neg 62),(.neg 22),(.pos 61),(.pos 64)]),
   ((.exchange 62 24 1),[(.neg 62),(.neg 24),(.pos 63),(.pos 64)]),
   ((.exchange 62 25 4),[(.neg 62),(.neg 25),(.pos 55),(.pos 66)]),
   ((.exchange 62 26 4),[(.neg 62),(.neg 26),(.pos 55),(.pos 57),(.pos 66)]),
   ((.exchange 62 29 4),[(.neg 62),(.neg 29),(.pos 59),(.pos 66)]),
   ((.exchange 62 40 1),[(.neg 62),(.neg 40),(.pos 61),(.pos 63)]),
   ((.exchange 62 51 1),[(.neg 62),(.neg 51),(.pos 61),(.pos 69)]),
   ((.exchange 62 54 1),[(.neg 62),(.neg 54),(.pos 64),(.pos 69)]),
   ((.exchange 62 68 1),[(.neg 68),(.neg 62),(.pos 64),(.pos 69)]),
   ((.exchange 63 16 4),[(.neg 63),(.neg 16),(.pos 56),(.pos 57),(.pos 60)]),
   ((.exchange 63 19 2),[(.neg 63),(.neg 19),(.pos 61),(.pos 62)]),
   ((.exchange 63 22 2),[(.neg 63),(.neg 22),(.pos 61),(.pos 64)]),
   ((.exchange 63 23 2),[(.neg 63),(.neg 23),(.pos 62),(.pos 64)]),
   ((.exchange 63 25 4),[(.neg 63),(.neg 25),(.pos 56),(.pos 57),(.pos 67)]),
   ((.exchange 63 30 4),[(.neg 63),(.neg 30),(.pos 60),(.pos 67)]),
   ((.exchange 63 31 2),[(.neg 63),(.neg 31),(.pos 61),(.pos 69)]),
   ((.exchange 63 32 2),[(.neg 63),(.neg 32),(.pos 62),(.pos 69)]),
   ((.exchange 63 34 2),[(.neg 63),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 63 38 4),[(.neg 63),(.neg 38),(.pos 57),(.pos 60)]),
   ((.exchange 63 42 2),[(.neg 63),(.neg 42),(.pos 61),(.pos 64)]),
   ((.exchange 63 58 2),[(.neg 63),(.neg 58),(.pos 61),(.pos 64)]),
   ((.exchange 63 68 2),[(.neg 68),(.neg 63),(.pos 64),(.pos 69)]),
   ((.exchange 64 17 4),[(.neg 64),(.neg 17),(.pos 58),(.pos 60)]),
   ((.exchange 64 18 4),[(.neg 64),(.neg 18),(.pos 59),(.pos 60)]),
   ((.exchange 64 20 3),[(.neg 64),(.neg 20),(.pos 61),(.pos 63)]),
   ((.exchange 64 21 3),[(.neg 64),(.neg 21),(.pos 62),(.pos 63)]),
   ((.exchange 64 28 4),[(.neg 64),(.neg 28),(.pos 58),(.pos 68)]),
   ((.exchange 64 30 4),[(.neg 64),(.neg 30),(.pos 60),(.pos 68)]),
   ((.exchange 64 33 3),[(.neg 64),(.neg 33),(.pos 63),(.pos 69)]),
   ((.exchange 64 36 4),[(.neg 64),(.neg 36),(.pos 58),(.pos 59)]),
   ((.exchange 64 38 4),[(.neg 64),(.neg 38),(.pos 59),(.pos 60)]),
   ((.exchange 64 49 4),[(.neg 64),(.neg 49),(.pos 59),(.pos 68)]),
   ((.exchange 64 52 3),[(.neg 64),(.neg 52),(.pos 62),(.pos 69)]),
   ((.exchange 64 57 3),[(.neg 64),(.neg 57),(.pos 62),(.pos 63)]),
   ((.exchange 64 65 3),[(.neg 65),(.neg 64),(.pos 61),(.pos 69)]),
   ((.exchange 64 66 3),[(.neg 66),(.neg 64),(.pos 62),(.pos 69)]),
   ((.exchange 64 66 4),[(.neg 66),(.neg 64),(.pos 59),(.pos 68)]),
   ((.exchange 64 67 3),[(.neg 67),(.neg 64),(.pos 63),(.pos 69)]),
   ((.exchange 64 67 4),[(.neg 67),(.neg 64),(.pos 60),(.pos 68)]),
   ((.exchange 65 16 5),[(.neg 65),(.neg 16),(.pos 55),(.pos 58)]),
   ((.exchange 65 27 0),[(.neg 65),(.neg 27),(.pos 66),(.pos 67)]),
   ((.exchange 65 32 0),[(.neg 65),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 65 33 0),[(.neg 65),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 65 34 0),[(.neg 65),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 65 50 0),[(.neg 65),(.neg 50),(.pos 67),(.pos 68)]),
   ((.exchange 65 54 0),[(.neg 65),(.neg 54),(.pos 68),(.pos 69)]),
   ((.exchange 65 57 0),[(.neg 65),(.neg 57),(.pos 66),(.pos 67)]),
   ((.exchange 65 59 0),[(.neg 65),(.neg 59),(.pos 66),(.pos 68)]),
   ((.exchange 65 59 5),[(.neg 65),(.neg 59),(.pos 55),(.pos 58)]),
   ((.exchange 65 60 5),[(.neg 65),(.neg 60),(.pos 56),(.pos 58)]),
   ((.exchange 65 63 5),[(.neg 65),(.neg 63),(.pos 56),(.pos 61)]),
   ((.exchange 66 26 1),[(.neg 66),(.neg 26),(.pos 65),(.pos 67)]),
   ((.exchange 66 34 1),[(.neg 66),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 66 41 5),[(.neg 66),(.neg 41),(.pos 57),(.pos 62)]),
   ((.exchange 66 46 1),[(.neg 66),(.neg 46),(.pos 65),(.pos 67)]),
   ((.exchange 66 51 1),[(.neg 66),(.neg 51),(.pos 65),(.pos 69)]),
   ((.exchange 66 58 1),[(.neg 66),(.neg 58),(.pos 65),(.pos 68)]),
   ((.exchange 66 60 1),[(.neg 66),(.neg 60),(.pos 67),(.pos 68)]),
   ((.exchange 66 60 5),[(.neg 66),(.neg 60),(.pos 57),(.pos 59)]),
   ((.exchange 66 63 1),[(.neg 66),(.neg 63),(.pos 67),(.pos 69)]),
   ((.exchange 66 63 5),[(.neg 66),(.neg 63),(.pos 57),(.pos 62)]),
   ((.exchange 67 21 5),[(.neg 67),(.neg 21),(.pos 57),(.pos 63)]),
   ((.exchange 67 24 5),[(.neg 67),(.neg 24),(.pos 60),(.pos 63)]),
   ((.exchange 67 31 2),[(.neg 67),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 67 32 2),[(.neg 67),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 67 34 2),[(.neg 67),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 67 38 5),[(.neg 67),(.neg 38),(.pos 57),(.pos 60)]),
   ((.exchange 67 55 2),[(.neg 67),(.neg 55),(.pos 65),(.pos 66)]),
   ((.exchange 67 58 2),[(.neg 67),(.neg 58),(.pos 65),(.pos 68)]),
   ((.exchange 68 17 5),[(.neg 68),(.neg 17),(.pos 58),(.pos 60)]),
   ((.exchange 68 18 5),[(.neg 68),(.neg 18),(.pos 59),(.pos 60)]),
   ((.exchange 68 22 5),[(.neg 68),(.neg 22),(.pos 58),(.pos 64)]),
   ((.exchange 68 23 5),[(.neg 68),(.neg 23),(.pos 59),(.pos 64)]),
   ((.exchange 68 24 5),[(.neg 68),(.neg 24),(.pos 60),(.pos 64)]),
   ((.exchange 68 25 3),[(.neg 68),(.neg 25),(.pos 65),(.pos 66)]),
   ((.exchange 68 26 3),[(.neg 68),(.neg 26),(.pos 65),(.pos 67)]),
   ((.exchange 68 27 3),[(.neg 68),(.neg 27),(.pos 66),(.pos 67)]),
   ((.exchange 68 31 3),[(.neg 68),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 68 32 3),[(.neg 68),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 68 33 3),[(.neg 68),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 68 36 5),[(.neg 68),(.neg 36),(.pos 58),(.pos 59)]),
   ((.exchange 68 38 5),[(.neg 68),(.neg 38),(.pos 59),(.pos 60)]),
   ((.exchange 68 43 5),[(.neg 68),(.neg 43),(.pos 59),(.pos 64)]),
   ((.exchange 68 52 3),[(.neg 68),(.neg 52),(.pos 66),(.pos 69)]),
   ((.exchange 68 53 3),[(.neg 68),(.neg 53),(.pos 67),(.pos 69)]),
   ((.exchange 68 55 3),[(.neg 68),(.neg 55),(.pos 65),(.pos 66)]),
   ((.exchange 68 55 5),[(.neg 68),(.neg 55),(.pos 58),(.pos 59)]),
   ((.exchange 68 57 3),[(.neg 68),(.neg 57),(.pos 66),(.pos 67)]),
   ((.exchange 69 19 5),[(.neg 69),(.neg 19),(.pos 61),(.pos 62)]),
   ((.exchange 69 21 5),[(.neg 69),(.neg 21),(.pos 62),(.pos 63)]),
   ((.exchange 69 22 5),[(.neg 69),(.neg 22),(.pos 61),(.pos 64)]),
   ((.exchange 69 23 5),[(.neg 69),(.neg 23),(.pos 62),(.pos 64)]),
   ((.exchange 69 24 5),[(.neg 69),(.neg 24),(.pos 63),(.pos 64)]),
   ((.exchange 69 28 4),[(.neg 69),(.neg 28),(.pos 65),(.pos 68)]),
   ((.exchange 69 29 4),[(.neg 69),(.neg 29),(.pos 66),(.pos 68)]),
   ((.exchange 69 39 5),[(.neg 69),(.neg 39),(.pos 61),(.pos 62)]),
   ((.exchange 69 44 5),[(.neg 69),(.neg 44),(.pos 63),(.pos 64)]),
   ((.exchange 69 45 4),[(.neg 69),(.neg 45),(.pos 65),(.pos 66)]),
   ((.exchange 69 47 4),[(.neg 69),(.neg 47),(.pos 66),(.pos 67)]),
   ((.exchange 69 49 4),[(.neg 69),(.neg 49),(.pos 66),(.pos 68)]),
   ((.exchange 69 57 4),[(.neg 69),(.neg 57),(.pos 66),(.pos 67)]),
   ((.exchange 69 58 4),[(.neg 69),(.neg 58),(.pos 65),(.pos 68)]),
   ((.exchange 69 60 5),[(.neg 69),(.neg 60),(.pos 63),(.pos 64)]),
   (.newPoint,[(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 0),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 61),(.pos 65)]),
   ((.excluded 1),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 58),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 59),(.pos 62),(.pos 66)]),
   ((.excluded 2),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 3),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 64)]),
   ((.excluded 4),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 68)]),
   ((.excluded 5),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 69)]),
   ((.excluded 6),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 7),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 68)]),
   ((.excluded 8),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 9),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 64),(.pos 65)]),
   ((.excluded 10),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 64),(.pos 66)]),
   ((.excluded 11),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 64),(.pos 67)]),
   ((.excluded 12),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 64)]),
   ((.excluded 13),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)])]

theorem certificates_1_valid : ∀ oc ∈ certificates_1,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



noncomputable def certificates_2 : List (Origin 70 113 × List Sat.Literal) :=
  [((.excluded 14),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 61),(.pos 68)]),
   ((.excluded 15),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 62),(.pos 68)]),
   ((.excluded 16),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 63),(.pos 68)]),
   ((.excluded 17),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 68)]),
   ((.excluded 18),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 58),(.pos 69)]),
   ((.excluded 19),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 59),(.pos 69)]),
   ((.excluded 20),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 60),(.pos 69)]),
   ((.excluded 21),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 69)]),
   ((.excluded 22),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 58),(.pos 62),(.pos 67)]),
   ((.excluded 23),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 58),(.pos 62)]),
   ((.excluded 24),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 58),(.pos 67)]),
   ((.excluded 25),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 58),(.pos 63),(.pos 66)]),
   ((.excluded 26),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 58),(.pos 63)]),
   ((.excluded 27),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 58),(.pos 66)]),
   ((.excluded 28),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 58)]),
   ((.excluded 29),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 62),(.pos 67)]),
   ((.excluded 30),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 60),(.pos 62),(.pos 65)]),
   ((.excluded 31),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 60),(.pos 62)]),
   ((.excluded 32),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 62),(.pos 65)]),
   ((.excluded 33),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 62)]),
   ((.excluded 34),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 59),(.pos 61),(.pos 67)]),
   ((.excluded 35),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 59),(.pos 67)]),
   ((.excluded 36),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 61),(.pos 67)]),
   ((.excluded 37),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 67)]),
   ((.excluded 38),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 59),(.pos 61)]),
   ((.excluded 39),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 59),(.pos 63),(.pos 65)]),
   ((.excluded 40),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 59),(.pos 63)]),
   ((.excluded 41),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 59),(.pos 65)]),
   ((.excluded 42),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 59)]),
   ((.excluded 43),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 60),(.pos 61),(.pos 66)]),
   ((.excluded 44),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 60),(.pos 61)]),
   ((.excluded 45),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 61),(.pos 66)]),
   ((.excluded 46),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 61)]),
   ((.excluded 47),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 60),(.pos 65)]),
   ((.excluded 48),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 60),(.pos 66)]),
   ((.excluded 49),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 60)]),
   ((.excluded 50),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 63),(.pos 65)]),
   ((.excluded 51),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 65)]),
   ((.excluded 52),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 63),(.pos 66)]),
   ((.excluded 53),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 63)]),
   ((.excluded 54),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 66)]),
   ((.excluded 55),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54)]),
   ((.excluded 56),[(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 57),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 61),(.pos 65)]),
   ((.excluded 58),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 55),(.pos 56),(.pos 57),(.pos 59),(.pos 62),(.pos 66)]),
   ((.excluded 59),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 60),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 55),(.pos 56),(.pos 57),(.pos 64)]),
   ((.excluded 61),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 55),(.pos 56),(.pos 57),(.pos 68)]),
   ((.excluded 62),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 55),(.pos 56),(.pos 57),(.pos 69)]),
   ((.excluded 63),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 64),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 68)]),
   ((.excluded 65),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 66),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 64),(.pos 65)]),
   ((.excluded 67),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 64),(.pos 66)]),
   ((.excluded 68),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 64),(.pos 67)]),
   ((.excluded 69),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 64)]),
   ((.excluded 70),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 71),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 61),(.pos 68)]),
   ((.excluded 72),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 62),(.pos 68)]),
   ((.excluded 73),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 63),(.pos 68)]),
   ((.excluded 74),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 68)]),
   ((.excluded 75),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 58),(.pos 69)]),
   ((.excluded 76),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 59),(.pos 69)]),
   ((.excluded 77),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 60),(.pos 69)]),
   ((.excluded 78),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 69)]),
   ((.excluded 79),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 58),(.pos 62),(.pos 67)]),
   ((.excluded 80),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 58),(.pos 62)]),
   ((.excluded 81),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 58),(.pos 67)]),
   ((.excluded 82),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 58),(.pos 63),(.pos 66)]),
   ((.excluded 83),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 58),(.pos 63)]),
   ((.excluded 84),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 58),(.pos 66)]),
   ((.excluded 85),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 58)]),
   ((.excluded 86),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 62),(.pos 67)]),
   ((.excluded 87),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 60),(.pos 62),(.pos 65)]),
   ((.excluded 88),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 60),(.pos 62)]),
   ((.excluded 89),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 62),(.pos 65)]),
   ((.excluded 90),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 62)]),
   ((.excluded 91),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 59),(.pos 61),(.pos 67)]),
   ((.excluded 92),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 59),(.pos 67)]),
   ((.excluded 93),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 61),(.pos 67)]),
   ((.excluded 94),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 67)]),
   ((.excluded 95),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 59),(.pos 61)]),
   ((.excluded 96),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 59),(.pos 63),(.pos 65)]),
   ((.excluded 97),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 59),(.pos 63)]),
   ((.excluded 98),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 59),(.pos 65)]),
   ((.excluded 99),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 59)]),
   ((.excluded 100),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 60),(.pos 61),(.pos 66)]),
   ((.excluded 101),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 60),(.pos 61)]),
   ((.excluded 102),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 61),(.pos 66)]),
   ((.excluded 103),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 61)]),
   ((.excluded 104),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 60),(.pos 65)]),
   ((.excluded 105),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 60),(.pos 66)]),
   ((.excluded 106),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 60)]),
   ((.excluded 107),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 63),(.pos 65)]),
   ((.excluded 108),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 65)]),
   ((.excluded 109),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 63),(.pos 66)]),
   ((.excluded 110),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 63)]),
   ((.excluded 111),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 66)]),
   ((.excluded 112),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35)])]

theorem certificates_2_valid : ∀ oc ∈ certificates_2,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.FastSemanticChecks.fastOrigins_sound
  decide +kernel



theorem witness_0 : ∀ j : Fin 113,
    let w : Fin 113 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  have hfast : ∀ j : Fin 113,
      let w : Fin 113 := ⟨0 + j.val,by omega⟩
      target w < MatroidCatalogue.count 8 4 ∧
        Papers.RationalityTen.MatroidChecked.FastSemanticChecks.RawWitness 8 (N7R4.familyMasks.get 23)
        (fun i : Fin 70 => N8R4.gridMasks.get i.val) newIndex (models w)
        (N8R4.familyMasks.get (target w)) (permutation w) := by
    refine (Fin.forall_fin_add (m := 56) (n := 57) _).2 ⟨?_, ?_⟩
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
    · refine (Fin.forall_fin_add (m := 28) (n := 29) _).2 ⟨?_, ?_⟩
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
      · refine (Fin.forall_fin_add (m := 14) (n := 15) _).2 ⟨?_, ?_⟩
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


end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C23

/- Source: MatroidCatalogue/Cases/N8R4C23Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C23

noncomputable def certificates : List (Origin 70 113 × List Sat.Literal) :=
  certificates_0 ++ certificates_1 ++ certificates_2

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  intro oc hoc
  simp only [certificates,List.mem_append,or_assoc] at hoc
  rcases hoc with h0 | h1 | h2
  · exact certificates_0_valid oc h0
  · exact certificates_1_valid oc h1
  · exact certificates_2_valid oc h2

theorem models_valid : ∀ w : Fin 113,
    target w < MatroidCatalogue.count 8 4 ∧
      ValidWitness 8 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 8 4 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 113) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 8) 4)
    (hold : M.bases.filter ((7 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 8 4, IsomorphicWithin 8 M.bases B := by
  apply extension_covered_of_certificate (n:=7) (r:=4) (by decide)
    catalogue old U newIndex models certificates
    N8R4.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C23.formula []
    exact Papers.RationalityTen.MatroidChecked.PublicRefutations.N8R4C23.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 8 4 (target w),family_mem 8 4 (target w) hw.1,?_⟩
    exact validWitness_sound 8 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C23

end
end
end BundlePart9
