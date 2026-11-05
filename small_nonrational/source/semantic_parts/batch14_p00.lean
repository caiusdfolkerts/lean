module
public import Consolidated.SemanticData
public import Mathlib.Data.Fin.Tuple.Basic
public import MatroidCatalogue.Definitions
public import MatroidChecked.Cases00
public import MatroidChecked.FastSemanticChecks
public import MatroidChecked.BitsetSemanticChecks
public import MatroidChecked.BitsetOrigins
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
/- Source: MatroidChecked/SemanticParts/Cases15Part00/Checks00.lean -/



@[expose] public section
noncomputable section


set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C68


noncomputable def certificates_0 : List (Origin 70 629 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.pos 2)]),
   ((.fixed 3),[(.pos 3)]),
   ((.fixed 4),[(.pos 4)]),
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
   ((.exchange 2 37 4),[(.neg 37),(.neg 2),(.pos 0),(.pos 36)]),
   ((.exchange 2 38 4),[(.neg 38),(.neg 2),(.pos 0),(.pos 36)]),
   ((.exchange 2 41 3),[(.neg 41),(.neg 2),(.pos 1),(.pos 39)]),
   ((.exchange 2 48 1),[(.neg 48),(.neg 2),(.pos 12),(.pos 42)]),
   ((.exchange 2 51 1),[(.neg 51),(.neg 2),(.pos 12),(.pos 42)]),
   ((.exchange 2 54 1),[(.neg 54),(.neg 2),(.pos 12),(.pos 42)]),
   ((.exchange 3 36 4),[(.neg 36),(.neg 3),(.pos 0),(.pos 37)]),
   ((.exchange 3 38 4),[(.neg 38),(.neg 3),(.pos 0),(.pos 37)]),
   ((.exchange 3 41 3),[(.neg 41),(.neg 3),(.pos 1),(.pos 40)]),
   ((.exchange 4 36 4),[(.neg 36),(.neg 4),(.pos 0),(.pos 38)]),
   ((.exchange 4 37 4),[(.neg 37),(.neg 4),(.pos 0),(.pos 38)]),
   ((.exchange 4 39 3),[(.neg 39),(.neg 4),(.pos 1),(.pos 41)]),
   ((.exchange 4 40 3),[(.neg 40),(.neg 4),(.pos 1),(.pos 41)]),
   ((.exchange 6 42 1),[(.neg 42),(.neg 6),(.pos 12),(.pos 48)]),
   ((.exchange 6 46 3),[(.neg 46),(.neg 6),(.pos 5),(.pos 45)]),
   ((.exchange 6 47 3),[(.neg 47),(.neg 6),(.pos 5),(.pos 45)]),
   ((.exchange 6 51 1),[(.neg 51),(.neg 6),(.pos 12),(.pos 48)]),
   ((.exchange 7 45 3),[(.neg 45),(.neg 7),(.pos 5),(.pos 46)]),
   ((.exchange 7 47 3),[(.neg 47),(.neg 7),(.pos 5),(.pos 46)]),
   ((.exchange 8 45 3),[(.neg 45),(.neg 8),(.pos 5),(.pos 47)]),
   ((.exchange 8 46 3),[(.neg 46),(.neg 8),(.pos 5),(.pos 47)]),
   ((.exchange 9 42 1),[(.neg 42),(.neg 9),(.pos 12),(.pos 51)]),
   ((.exchange 13 42 1),[(.neg 42),(.neg 13),(.pos 12),(.pos 54)]),
   ((.exchange 13 51 1),[(.neg 51),(.neg 13),(.pos 12),(.pos 54)]),
   ((.exchange 16 56 3),[(.neg 56),(.neg 16),(.pos 15),(.pos 55)]),
   ((.exchange 16 57 3),[(.neg 57),(.neg 16),(.pos 15),(.pos 55)]),
   ((.exchange 17 55 3),[(.neg 55),(.neg 17),(.pos 15),(.pos 56)]),
   ((.exchange 17 57 3),[(.neg 57),(.neg 17),(.pos 15),(.pos 56)]),
   ((.exchange 18 55 3),[(.neg 55),(.neg 18),(.pos 15),(.pos 57)]),
   ((.exchange 18 56 3),[(.neg 56),(.neg 18),(.pos 15),(.pos 57)]),
   ((.exchange 35 2 7),[(.neg 35),(.neg 2),(.pos 0),(.pos 1)]),
   ((.exchange 36 11 3),[(.neg 36),(.neg 11),(.pos 35),(.pos 39),(.pos 45)]),
   ((.exchange 36 13 0),[(.neg 36),(.neg 13),(.pos 43),(.pos 49)]),
   ((.exchange 36 23 0),[(.neg 36),(.neg 23),(.pos 43),(.pos 59)]),
   ((.exchange 36 28 1),[(.neg 36),(.neg 28),(.pos 48),(.pos 58)]),
   ((.exchange 36 29 0),[(.neg 36),(.neg 29),(.pos 49),(.pos 59)]),
   ((.exchange 36 52 0),[(.neg 52),(.neg 36),(.pos 43),(.pos 49)]),
   ((.exchange 36 54 0),[(.neg 54),(.neg 36),(.pos 43),(.pos 49)]),
   ((.exchange 36 61 3),[(.neg 61),(.neg 36),(.pos 39),(.pos 55)]),
   ((.exchange 36 68 0),[(.neg 68),(.neg 36),(.pos 49),(.pos 59)]),
   ((.exchange 37 11 3),[(.neg 37),(.neg 11),(.pos 35),(.pos 40),(.pos 46)]),
   ((.exchange 37 14 0),[(.neg 37),(.neg 14),(.pos 44),(.pos 50)]),
   ((.exchange 37 22 2),[(.neg 37),(.neg 22),(.pos 42),(.pos 58)]),
   ((.exchange 37 24 0),[(.neg 37),(.neg 24),(.pos 44),(.pos 60)]),
   ((.exchange 37 28 2),[(.neg 37),(.neg 28),(.pos 48),(.pos 58)]),
   ((.exchange 37 30 0),[(.neg 37),(.neg 30),(.pos 50),(.pos 60)]),
   ((.exchange 37 31 3),[(.neg 37),(.neg 31),(.pos 40),(.pos 46),(.pos 56)]),
   ((.exchange 37 53 0),[(.neg 53),(.neg 37),(.pos 44),(.pos 50)]),
   ((.exchange 37 63 0),[(.neg 63),(.neg 37),(.pos 44),(.pos 60)]),
   ((.exchange 37 68 0),[(.neg 68),(.neg 37),(.pos 50),(.pos 60)]),
   ((.exchange 38 11 3),[(.neg 38),(.neg 11),(.pos 41),(.pos 47)]),
   ((.exchange 38 13 2),[(.neg 38),(.neg 13),(.pos 43),(.pos 49)]),
   ((.exchange 38 24 1),[(.neg 38),(.neg 24),(.pos 44),(.pos 60)]),
   ((.exchange 38 29 2),[(.neg 38),(.neg 29),(.pos 49),(.pos 59)]),
   ((.exchange 38 32 3),[(.neg 38),(.neg 32),(.pos 41),(.pos 47),(.pos 57)]),
   ((.exchange 38 52 2),[(.neg 52),(.neg 38),(.pos 43),(.pos 49)]),
   ((.exchange 38 53 1),[(.neg 53),(.neg 38),(.pos 44),(.pos 50)]),
   ((.exchange 38 54 1),[(.neg 54),(.neg 38),(.pos 44),(.pos 50)]),
   ((.exchange 38 54 2),[(.neg 54),(.neg 38),(.pos 43),(.pos 49)]),
   ((.exchange 38 63 1),[(.neg 63),(.neg 38),(.pos 44),(.pos 60)]),
   ((.exchange 38 64 2),[(.neg 64),(.neg 38),(.pos 43),(.pos 59)]),
   ((.exchange 38 66 2),[(.neg 66),(.neg 38),(.pos 49),(.pos 59)]),
   ((.exchange 38 68 1),[(.neg 68),(.neg 38),(.pos 50),(.pos 60)]),
   ((.exchange 39 6 4),[(.neg 39),(.neg 6),(.pos 36),(.pos 45)]),
   ((.exchange 39 13 0),[(.neg 39),(.neg 13),(.pos 43),(.pos 52)]),
   ((.exchange 39 18 4),[(.neg 39),(.neg 18),(.pos 35),(.pos 36),(.pos 55)]),
   ((.exchange 39 22 1),[(.neg 39),(.neg 22),(.pos 42),(.pos 61)]),
   ((.exchange 39 23 0),[(.neg 39),(.neg 23),(.pos 43),(.pos 62)]),
   ((.exchange 39 26 4),[(.neg 39),(.neg 26),(.pos 35),(.pos 45),(.pos 55)]),
   ((.exchange 39 32 0),[(.neg 39),(.neg 32),(.pos 52),(.pos 62)]),
   ((.exchange 40 6 4),[(.neg 40),(.neg 6),(.pos 35),(.pos 37),(.pos 46)]),
   ((.exchange 40 14 0),[(.neg 40),(.neg 14),(.pos 44),(.pos 53)]),
   ((.exchange 40 18 4),[(.neg 40),(.neg 18),(.pos 35),(.pos 37),(.pos 56)]),
   ((.exchange 40 24 0),[(.neg 40),(.neg 24),(.pos 44),(.pos 63)]),
   ((.exchange 40 26 4),[(.neg 40),(.neg 26),(.pos 46),(.pos 56)]),
   ((.exchange 40 31 2),[(.neg 40),(.neg 31),(.pos 51),(.pos 61)]),
   ((.exchange 40 33 0),[(.neg 40),(.neg 33),(.pos 53),(.pos 63)]),
   ((.exchange 40 50 0),[(.neg 50),(.neg 40),(.pos 44),(.pos 53)]),
   ((.exchange 40 54 0),[(.neg 54),(.neg 40),(.pos 44),(.pos 53)]),
   ((.exchange 41 6 4),[(.neg 41),(.neg 6),(.pos 35),(.pos 38),(.pos 47)]),
   ((.exchange 41 13 2),[(.neg 41),(.neg 13),(.pos 43),(.pos 52)]),
   ((.exchange 41 18 4),[(.neg 41),(.neg 18),(.pos 38),(.pos 57)]),
   ((.exchange 41 24 1),[(.neg 41),(.neg 24),(.pos 44),(.pos 63)]),
   ((.exchange 41 25 4),[(.neg 41),(.neg 25),(.pos 35),(.pos 47),(.pos 57)]),
   ((.exchange 41 33 1),[(.neg 41),(.neg 33),(.pos 53),(.pos 63)]),
   ((.exchange 41 49 2),[(.neg 49),(.neg 41),(.pos 43),(.pos 52)]),
   ((.exchange 41 50 1),[(.neg 50),(.neg 41),(.pos 44),(.pos 53)]),
   ((.exchange 41 60 1),[(.neg 60),(.neg 41),(.pos 44),(.pos 63)]),
   ((.exchange 41 64 1),[(.neg 64),(.neg 41),(.pos 44),(.pos 63)]),
   ((.exchange 41 64 2),[(.neg 64),(.neg 41),(.pos 43),(.pos 62)]),
   ((.exchange 41 69 2),[(.neg 69),(.neg 41),(.pos 52),(.pos 62)]),
   ((.exchange 42 4 0),[(.neg 42),(.neg 4),(.pos 43),(.pos 44)]),
   ((.exchange 42 16 4),[(.neg 42),(.neg 16),(.pos 36),(.pos 58)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.BitsetOrigins.bitsetOrigins_sound
  have hchecks : ∀ i : Fin 128,
    Papers.RationalityTen.MatroidChecked.BitsetOrigins.BitsetOrigin U (7 : Fin 8) old newIndex models
      (certificates_0.get i).1 (certificates_0.get i).2 := by
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
  intro oc hoc
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hoc
  exact hchecks i



noncomputable def certificates_1 : List (Origin 70 629 × List Sat.Literal) :=
  [((.exchange 42 17 4),[(.neg 42),(.neg 17),(.pos 37),(.pos 58)]),
   ((.exchange 42 19 3),[(.neg 42),(.neg 19),(.pos 39),(.pos 61)]),
   ((.exchange 42 23 0),[(.neg 42),(.neg 23),(.pos 43),(.pos 64)]),
   ((.exchange 42 24 0),[(.neg 42),(.neg 24),(.pos 44),(.pos 64)]),
   ((.exchange 43 6 4),[(.neg 43),(.neg 6),(.pos 36),(.pos 49)]),
   ((.exchange 43 8 4),[(.neg 43),(.neg 8),(.pos 38),(.pos 49)]),
   ((.exchange 43 14 1),[(.neg 43),(.neg 14),(.pos 44),(.pos 54)]),
   ((.exchange 43 16 4),[(.neg 43),(.neg 16),(.pos 36),(.pos 59)]),
   ((.exchange 43 18 4),[(.neg 43),(.neg 18),(.pos 38),(.pos 59)]),
   ((.exchange 43 21 3),[(.neg 43),(.neg 21),(.pos 41),(.pos 62)]),
   ((.exchange 43 29 4),[(.neg 43),(.neg 29),(.pos 49),(.pos 59)]),
   ((.exchange 43 32 3),[(.neg 43),(.neg 32),(.pos 52),(.pos 62)]),
   ((.exchange 43 33 3),[(.neg 43),(.neg 33),(.pos 41),(.pos 52),(.pos 62)]),
   ((.exchange 43 40 1),[(.neg 43),(.neg 40),(.pos 42),(.pos 44)]),
   ((.exchange 43 45 4),[(.neg 45),(.neg 43),(.pos 36),(.pos 49)]),
   ((.exchange 43 46 4),[(.neg 46),(.neg 43),(.pos 36),(.pos 38),(.pos 49)]),
   ((.exchange 43 47 4),[(.neg 47),(.neg 43),(.pos 38),(.pos 49)]),
   ((.exchange 43 48 4),[(.neg 48),(.neg 43),(.pos 36),(.pos 49)]),
   ((.exchange 43 56 4),[(.neg 56),(.neg 43),(.pos 36),(.pos 38),(.pos 59)]),
   ((.exchange 43 57 4),[(.neg 57),(.neg 43),(.pos 38),(.pos 59)]),
   ((.exchange 43 58 4),[(.neg 58),(.neg 43),(.pos 36),(.pos 59)]),
   ((.exchange 43 60 4),[(.neg 60),(.neg 43),(.pos 38),(.pos 59)]),
   ((.exchange 43 61 3),[(.neg 61),(.neg 43),(.pos 39),(.pos 62)]),
   ((.exchange 43 63 1),[(.neg 63),(.neg 43),(.pos 44),(.pos 64)]),
   ((.exchange 43 65 1),[(.neg 65),(.neg 43),(.pos 42),(.pos 54),(.pos 64)]),
   ((.exchange 43 66 4),[(.neg 66),(.neg 43),(.pos 49),(.pos 59)]),
   ((.exchange 44 2 2),[(.neg 44),(.neg 2),(.pos 42),(.pos 43)]),
   ((.exchange 44 6 4),[(.neg 44),(.neg 6),(.pos 37),(.pos 38),(.pos 50)]),
   ((.exchange 44 7 4),[(.neg 44),(.neg 7),(.pos 37),(.pos 50)]),
   ((.exchange 44 8 4),[(.neg 44),(.neg 8),(.pos 38),(.pos 50)]),
   ((.exchange 44 21 3),[(.neg 44),(.neg 21),(.pos 41),(.pos 63)]),
   ((.exchange 44 23 2),[(.neg 44),(.neg 23),(.pos 43),(.pos 64)]),
   ((.exchange 44 30 4),[(.neg 44),(.neg 30),(.pos 50),(.pos 60)]),
   ((.exchange 44 32 3),[(.neg 44),(.neg 32),(.pos 41),(.pos 53),(.pos 63)]),
   ((.exchange 44 33 3),[(.neg 44),(.neg 33),(.pos 53),(.pos 63)]),
   ((.exchange 44 39 2),[(.neg 44),(.neg 39),(.pos 42),(.pos 43)]),
   ((.exchange 44 46 4),[(.neg 46),(.neg 44),(.pos 37),(.pos 50)]),
   ((.exchange 44 48 4),[(.neg 48),(.neg 44),(.pos 37),(.pos 50)]),
   ((.exchange 44 55 4),[(.neg 55),(.neg 44),(.pos 37),(.pos 38),(.pos 60)]),
   ((.exchange 44 56 4),[(.neg 56),(.neg 44),(.pos 37),(.pos 60)]),
   ((.exchange 44 58 2),[(.neg 58),(.neg 44),(.pos 42),(.pos 64)]),
   ((.exchange 44 58 4),[(.neg 58),(.neg 44),(.pos 37),(.pos 60)]),
   ((.exchange 44 59 2),[(.neg 59),(.neg 44),(.pos 43),(.pos 64)]),
   ((.exchange 44 65 2),[(.neg 65),(.neg 44),(.pos 42),(.pos 54),(.pos 64)]),
   ((.exchange 44 68 2),[(.neg 68),(.neg 44),(.pos 54),(.pos 64)]),
   ((.exchange 44 69 2),[(.neg 69),(.neg 44),(.pos 54),(.pos 64)]),
   ((.exchange 45 2 5),[(.neg 45),(.neg 2),(.pos 36),(.pos 39)]),
   ((.exchange 45 13 0),[(.neg 45),(.neg 13),(.pos 49),(.pos 52)]),
   ((.exchange 45 19 5),[(.neg 45),(.neg 19),(.pos 39),(.pos 55)]),
   ((.exchange 45 29 0),[(.neg 45),(.neg 29),(.pos 49),(.pos 66)]),
   ((.exchange 45 31 1),[(.neg 45),(.neg 31),(.pos 51),(.pos 65)]),
   ((.exchange 45 32 0),[(.neg 45),(.neg 32),(.pos 52),(.pos 66)]),
   ((.exchange 45 34 0),[(.neg 45),(.neg 34),(.pos 49),(.pos 52),(.pos 66)]),
   ((.exchange 45 43 0),[(.neg 45),(.neg 43),(.pos 49),(.pos 52)]),
   ((.exchange 45 59 0),[(.neg 59),(.neg 45),(.pos 49),(.pos 66)]),
   ((.exchange 45 61 5),[(.neg 61),(.neg 45),(.pos 39),(.pos 55)]),
   ((.exchange 45 62 0),[(.neg 62),(.neg 45),(.pos 52),(.pos 66)]),
   ((.exchange 45 68 0),[(.neg 68),(.neg 45),(.pos 49),(.pos 66)]),
   ((.exchange 45 69 0),[(.neg 69),(.neg 45),(.pos 52),(.pos 66)]),
   ((.exchange 46 2 5),[(.neg 46),(.neg 2),(.pos 35),(.pos 37),(.pos 40)]),
   ((.exchange 46 14 0),[(.neg 46),(.neg 14),(.pos 50),(.pos 53)]),
   ((.exchange 46 19 5),[(.neg 46),(.neg 19),(.pos 35),(.pos 40),(.pos 56)]),
   ((.exchange 46 22 2),[(.neg 46),(.neg 22),(.pos 48),(.pos 51),(.pos 65)]),
   ((.exchange 46 30 0),[(.neg 46),(.neg 30),(.pos 50),(.pos 67)]),
   ((.exchange 46 31 2),[(.neg 46),(.neg 31),(.pos 51),(.pos 65)]),
   ((.exchange 46 33 0),[(.neg 46),(.neg 33),(.pos 53),(.pos 67)]),
   ((.exchange 46 44 0),[(.neg 46),(.neg 44),(.pos 50),(.pos 53)]),
   ((.exchange 46 60 0),[(.neg 60),(.neg 46),(.pos 50),(.pos 67)]),
   ((.exchange 46 61 5),[(.neg 61),(.neg 46),(.pos 40),(.pos 56)]),
   ((.exchange 46 68 0),[(.neg 68),(.neg 46),(.pos 50),(.pos 67)]),
   ((.exchange 46 69 0),[(.neg 69),(.neg 46),(.pos 53),(.pos 67)]),
   ((.exchange 47 2 5),[(.neg 47),(.neg 2),(.pos 35),(.pos 38),(.pos 41)]),
   ((.exchange 47 13 2),[(.neg 47),(.neg 13),(.pos 49),(.pos 52)]),
   ((.exchange 47 14 1),[(.neg 47),(.neg 14),(.pos 50),(.pos 53)]),
   ((.exchange 47 19 5),[(.neg 47),(.neg 19),(.pos 35),(.pos 41),(.pos 57)]),
   ((.exchange 47 29 2),[(.neg 47),(.neg 29),(.pos 49),(.pos 66)]),
   ((.exchange 47 30 1),[(.neg 47),(.neg 30),(.pos 50),(.pos 67)]),
   ((.exchange 47 33 1),[(.neg 47),(.neg 33),(.pos 53),(.pos 67)]),
   ((.exchange 47 43 2),[(.neg 47),(.neg 43),(.pos 49),(.pos 52)]),
   ((.exchange 47 60 1),[(.neg 60),(.neg 47),(.pos 50),(.pos 67)]),
   ((.exchange 47 61 5),[(.neg 61),(.neg 47),(.pos 35),(.pos 41),(.pos 57)]),
   ((.exchange 47 62 2),[(.neg 62),(.neg 47),(.pos 52),(.pos 66)]),
   ((.exchange 47 63 1),[(.neg 63),(.neg 47),(.pos 53),(.pos 67)]),
   ((.exchange 47 68 1),[(.neg 68),(.neg 47),(.pos 50),(.pos 67)]),
   ((.exchange 47 68 2),[(.neg 68),(.neg 47),(.pos 49),(.pos 66)]),
   ((.exchange 47 69 1),[(.neg 69),(.neg 47),(.pos 53),(.pos 67)]),
   ((.exchange 47 69 2),[(.neg 69),(.neg 47),(.pos 52),(.pos 66)]),
   ((.exchange 48 8 0),[(.neg 48),(.neg 8),(.pos 49),(.pos 50)]),
   ((.exchange 48 17 5),[(.neg 48),(.neg 17),(.pos 37),(.pos 58)]),
   ((.exchange 48 25 3),[(.neg 48),(.neg 25),(.pos 45),(.pos 65)]),
   ((.exchange 48 26 3),[(.neg 48),(.neg 26),(.pos 46),(.pos 65)]),
   ((.exchange 48 29 0),[(.neg 48),(.neg 29),(.pos 49),(.pos 68)]),
   ((.exchange 48 30 0),[(.neg 48),(.neg 30),(.pos 50),(.pos 68)]),
   ((.exchange 48 38 0),[(.neg 48),(.neg 38),(.pos 49),(.pos 50)]),
   ((.exchange 48 60 5),[(.neg 60),(.neg 48),(.pos 37),(.pos 58)]),
   ((.exchange 48 67 0),[(.neg 67),(.neg 48),(.pos 50),(.pos 68)]),
   ((.exchange 49 2 5),[(.neg 49),(.neg 2),(.pos 36),(.pos 43)]),
   ((.exchange 49 3 5),[(.neg 49),(.neg 3),(.pos 36),(.pos 38),(.pos 43)]),
   ((.exchange 49 4 5),[(.neg 49),(.neg 4),(.pos 38),(.pos 43)]),
   ((.exchange 49 9 3),[(.neg 49),(.neg 9),(.pos 45),(.pos 52)]),
   ((.exchange 49 18 5),[(.neg 49),(.neg 18),(.pos 38),(.pos 59)]),
   ((.exchange 49 25 3),[(.neg 49),(.neg 25),(.pos 45),(.pos 66)]),
   ((.exchange 49 27 3),[(.neg 49),(.neg 27),(.pos 47),(.pos 66)]),
   ((.exchange 49 31 1),[(.neg 49),(.neg 31),(.pos 48),(.pos 54),(.pos 68)]),
   ((.exchange 49 32 3),[(.neg 49),(.neg 32),(.pos 52),(.pos 66)]),
   ((.exchange 49 34 1),[(.neg 49),(.neg 34),(.pos 54),(.pos 68)]),
   ((.exchange 49 39 3),[(.neg 49),(.neg 39),(.pos 45),(.pos 52)]),
   ((.exchange 49 39 5),[(.neg 49),(.neg 39),(.pos 36),(.pos 43)]),
   ((.exchange 49 40 3),[(.neg 49),(.neg 40),(.pos 45),(.pos 47),(.pos 52)]),
   ((.exchange 49 41 3),[(.neg 49),(.neg 41),(.pos 47),(.pos 52)]),
   ((.exchange 49 41 5),[(.neg 49),(.neg 41),(.pos 38),(.pos 43)]),
   ((.exchange 49 42 5),[(.neg 49),(.neg 42),(.pos 36),(.pos 43)]),
   ((.exchange 49 51 3),[(.neg 51),(.neg 49),(.pos 45),(.pos 52)]),
   ((.exchange 49 53 3),[(.neg 53),(.neg 49),(.pos 47),(.pos 52)]),
   ((.exchange 49 55 5),[(.neg 55),(.neg 49),(.pos 36),(.pos 59)]),
   ((.exchange 49 57 5),[(.neg 57),(.neg 49),(.pos 38),(.pos 59)]),
   ((.exchange 49 58 5),[(.neg 58),(.neg 49),(.pos 36),(.pos 59)]),
   ((.exchange 49 60 5),[(.neg 60),(.neg 49),(.pos 38),(.pos 59)]),
   ((.exchange 49 62 3),[(.neg 62),(.neg 49),(.pos 52),(.pos 66)]),
   ((.exchange 49 62 5),[(.neg 62),(.neg 49),(.pos 43),(.pos 59)]),
   ((.exchange 49 64 5),[(.neg 64),(.neg 49),(.pos 43),(.pos 59)]),
   ((.exchange 49 65 3),[(.neg 65),(.neg 49),(.pos 45),(.pos 66)]),
   ((.exchange 49 67 3),[(.neg 67),(.neg 49),(.pos 47),(.pos 66)]),
   ((.exchange 49 69 3),[(.neg 69),(.neg 49),(.pos 52),(.pos 66)]),
   ((.exchange 50 2 2),[(.neg 50),(.neg 2),(.pos 48),(.pos 49),(.pos 54)]),
   ((.exchange 50 3 5),[(.neg 50),(.neg 3),(.pos 37),(.pos 44)]),
   ((.exchange 50 4 5),[(.neg 50),(.neg 4),(.pos 38),(.pos 44)]),
   ((.exchange 50 9 3),[(.neg 50),(.neg 9),(.pos 46),(.pos 47),(.pos 53)])]

theorem certificates_1_valid : ∀ oc ∈ certificates_1,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.BitsetOrigins.bitsetOrigins_sound
  have hchecks : ∀ i : Fin 128,
    Papers.RationalityTen.MatroidChecked.BitsetOrigins.BitsetOrigin U (7 : Fin 8) old newIndex models
      (certificates_1.get i).1 (certificates_1.get i).2 := by
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
  intro oc hoc
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hoc
  exact hchecks i



noncomputable def certificates_2 : List (Origin 70 629 × List Sat.Literal) :=
  [((.exchange 50 11 3),[(.neg 50),(.neg 11),(.pos 47),(.pos 53)]),
   ((.exchange 50 18 5),[(.neg 50),(.neg 18),(.pos 38),(.pos 60)]),
   ((.exchange 50 24 5),[(.neg 50),(.neg 24),(.pos 44),(.pos 60)]),
   ((.exchange 50 25 3),[(.neg 50),(.neg 25),(.pos 46),(.pos 47),(.pos 67)]),
   ((.exchange 50 26 3),[(.neg 50),(.neg 26),(.pos 46),(.pos 67)]),
   ((.exchange 50 27 3),[(.neg 50),(.neg 27),(.pos 47),(.pos 67)]),
   ((.exchange 50 31 2),[(.neg 50),(.neg 31),(.pos 48),(.pos 54),(.pos 68)]),
   ((.exchange 50 33 3),[(.neg 50),(.neg 33),(.pos 53),(.pos 67)]),
   ((.exchange 50 34 2),[(.neg 50),(.neg 34),(.pos 54),(.pos 68)]),
   ((.exchange 50 39 5),[(.neg 50),(.neg 39),(.pos 37),(.pos 38),(.pos 44)]),
   ((.exchange 50 40 5),[(.neg 50),(.neg 40),(.pos 37),(.pos 44)]),
   ((.exchange 50 41 5),[(.neg 50),(.neg 41),(.pos 38),(.pos 44)]),
   ((.exchange 50 42 5),[(.neg 50),(.neg 42),(.pos 37),(.pos 44)]),
   ((.exchange 50 43 5),[(.neg 50),(.neg 43),(.pos 38),(.pos 44)]),
   ((.exchange 50 52 3),[(.neg 52),(.neg 50),(.pos 47),(.pos 53)]),
   ((.exchange 50 56 3),[(.neg 56),(.neg 50),(.pos 46),(.pos 67)]),
   ((.exchange 50 56 5),[(.neg 56),(.neg 50),(.pos 37),(.pos 60)]),
   ((.exchange 50 57 5),[(.neg 57),(.neg 50),(.pos 38),(.pos 60)]),
   ((.exchange 50 63 3),[(.neg 63),(.neg 50),(.pos 53),(.pos 67)]),
   ((.exchange 50 63 5),[(.neg 63),(.neg 50),(.pos 44),(.pos 60)]),
   ((.exchange 50 64 5),[(.neg 64),(.neg 50),(.pos 44),(.pos 60)]),
   ((.exchange 50 65 3),[(.neg 65),(.neg 50),(.pos 46),(.pos 67)]),
   ((.exchange 50 66 3),[(.neg 66),(.neg 50),(.pos 47),(.pos 67)]),
   ((.exchange 50 69 3),[(.neg 69),(.neg 50),(.pos 53),(.pos 67)]),
   ((.exchange 51 11 0),[(.neg 51),(.neg 11),(.pos 52),(.pos 53)]),
   ((.exchange 51 25 4),[(.neg 51),(.neg 25),(.pos 45),(.pos 65)]),
   ((.exchange 51 26 4),[(.neg 51),(.neg 26),(.pos 46),(.pos 65)]),
   ((.exchange 51 32 0),[(.neg 51),(.neg 32),(.pos 52),(.pos 69)]),
   ((.exchange 51 33 0),[(.neg 51),(.neg 33),(.pos 53),(.pos 69)]),
   ((.exchange 52 2 5),[(.neg 52),(.neg 2),(.pos 39),(.pos 43)]),
   ((.exchange 52 14 1),[(.neg 52),(.neg 14),(.pos 53),(.pos 54)]),
   ((.exchange 52 19 5),[(.neg 52),(.neg 19),(.pos 39),(.pos 62)]),
   ((.exchange 52 21 5),[(.neg 52),(.neg 21),(.pos 41),(.pos 62)]),
   ((.exchange 52 22 1),[(.neg 52),(.neg 22),(.pos 51),(.pos 54),(.pos 69)]),
   ((.exchange 52 29 4),[(.neg 52),(.neg 29),(.pos 49),(.pos 66)]),
   ((.exchange 52 33 1),[(.neg 52),(.neg 33),(.pos 53),(.pos 69)]),
   ((.exchange 52 36 4),[(.neg 52),(.neg 36),(.pos 45),(.pos 49)]),
   ((.exchange 52 38 4),[(.neg 52),(.neg 38),(.pos 47),(.pos 49)]),
   ((.exchange 52 48 4),[(.neg 52),(.neg 48),(.pos 45),(.pos 49)]),
   ((.exchange 52 50 4),[(.neg 52),(.neg 50),(.pos 47),(.pos 49)]),
   ((.exchange 52 55 4),[(.neg 55),(.neg 52),(.pos 45),(.pos 66)]),
   ((.exchange 52 57 4),[(.neg 57),(.neg 52),(.pos 47),(.pos 66)]),
   ((.exchange 52 58 1),[(.neg 58),(.neg 52),(.pos 51),(.pos 54),(.pos 69)]),
   ((.exchange 52 59 4),[(.neg 59),(.neg 52),(.pos 49),(.pos 66)]),
   ((.exchange 52 61 5),[(.neg 61),(.neg 52),(.pos 39),(.pos 62)]),
   ((.exchange 52 65 1),[(.neg 65),(.neg 52),(.pos 51),(.pos 69)]),
   ((.exchange 52 65 4),[(.neg 65),(.neg 52),(.pos 45),(.pos 66)]),
   ((.exchange 52 67 4),[(.neg 67),(.neg 52),(.pos 47),(.pos 66)]),
   ((.exchange 52 68 4),[(.neg 68),(.neg 52),(.pos 49),(.pos 66)]),
   ((.exchange 53 2 2),[(.neg 53),(.neg 2),(.pos 51),(.pos 52),(.pos 54)]),
   ((.exchange 53 2 5),[(.neg 53),(.neg 2),(.pos 40),(.pos 41),(.pos 44)]),
   ((.exchange 53 21 5),[(.neg 53),(.neg 21),(.pos 41),(.pos 63)]),
   ((.exchange 53 22 2),[(.neg 53),(.neg 22),(.pos 51),(.pos 54),(.pos 69)]),
   ((.exchange 53 26 4),[(.neg 53),(.neg 26),(.pos 46),(.pos 67)]),
   ((.exchange 53 27 4),[(.neg 53),(.neg 27),(.pos 47),(.pos 67)]),
   ((.exchange 53 30 4),[(.neg 53),(.neg 30),(.pos 50),(.pos 67)]),
   ((.exchange 53 34 2),[(.neg 53),(.neg 34),(.pos 54),(.pos 69)]),
   ((.exchange 53 37 4),[(.neg 53),(.neg 37),(.pos 46),(.pos 50)]),
   ((.exchange 53 38 4),[(.neg 53),(.neg 38),(.pos 47),(.pos 50)]),
   ((.exchange 53 39 2),[(.neg 53),(.neg 39),(.pos 51),(.pos 52)]),
   ((.exchange 53 43 5),[(.neg 53),(.neg 43),(.pos 41),(.pos 44)]),
   ((.exchange 53 48 4),[(.neg 53),(.neg 48),(.pos 46),(.pos 50)]),
   ((.exchange 53 56 4),[(.neg 56),(.neg 53),(.pos 46),(.pos 67)]),
   ((.exchange 53 57 4),[(.neg 57),(.neg 53),(.pos 47),(.pos 67)]),
   ((.exchange 53 58 2),[(.neg 58),(.neg 53),(.pos 51),(.pos 54),(.pos 69)]),
   ((.exchange 53 58 4),[(.neg 58),(.neg 53),(.pos 46),(.pos 50),(.pos 67)]),
   ((.exchange 53 60 4),[(.neg 60),(.neg 53),(.pos 50),(.pos 67)]),
   ((.exchange 53 61 5),[(.neg 61),(.neg 53),(.pos 40),(.pos 63)]),
   ((.exchange 53 62 5),[(.neg 62),(.neg 53),(.pos 41),(.pos 63)]),
   ((.exchange 53 65 2),[(.neg 65),(.neg 53),(.pos 51),(.pos 69)]),
   ((.exchange 53 65 4),[(.neg 65),(.neg 53),(.pos 46),(.pos 67)]),
   ((.exchange 53 66 4),[(.neg 66),(.neg 53),(.pos 47),(.pos 67)]),
   ((.exchange 53 68 4),[(.neg 68),(.neg 53),(.pos 50),(.pos 67)]),
   ((.exchange 54 24 5),[(.neg 54),(.neg 24),(.pos 44),(.pos 64)]),
   ((.exchange 54 29 4),[(.neg 54),(.neg 29),(.pos 49),(.pos 68)]),
   ((.exchange 54 30 4),[(.neg 54),(.neg 30),(.pos 50),(.pos 68)]),
   ((.exchange 54 41 5),[(.neg 54),(.neg 41),(.pos 43),(.pos 44)]),
   ((.exchange 54 62 5),[(.neg 62),(.neg 54),(.pos 43),(.pos 64)]),
   ((.exchange 54 66 3),[(.neg 66),(.neg 54),(.pos 52),(.pos 69)]),
   ((.exchange 54 66 4),[(.neg 66),(.neg 54),(.pos 49),(.pos 68)]),
   ((.exchange 54 67 3),[(.neg 67),(.neg 54),(.pos 53),(.pos 69)]),
   ((.exchange 54 67 4),[(.neg 67),(.neg 54),(.pos 50),(.pos 68)]),
   ((.exchange 55 9 6),[(.neg 55),(.neg 9),(.pos 39),(.pos 45)]),
   ((.exchange 55 22 1),[(.neg 55),(.neg 22),(.pos 58),(.pos 61)]),
   ((.exchange 55 23 0),[(.neg 55),(.neg 23),(.pos 59),(.pos 62)]),
   ((.exchange 55 31 1),[(.neg 55),(.neg 31),(.pos 61),(.pos 65)]),
   ((.exchange 55 32 0),[(.neg 55),(.neg 32),(.pos 62),(.pos 66)]),
   ((.exchange 55 42 6),[(.neg 55),(.neg 42),(.pos 36),(.pos 39)]),
   ((.exchange 55 43 0),[(.neg 55),(.neg 43),(.pos 59),(.pos 62)]),
   ((.exchange 55 51 6),[(.neg 55),(.neg 51),(.pos 39),(.pos 45)]),
   ((.exchange 55 69 0),[(.neg 69),(.neg 55),(.pos 62),(.pos 66)]),
   ((.exchange 56 9 6),[(.neg 56),(.neg 9),(.pos 35),(.pos 40),(.pos 46)]),
   ((.exchange 56 24 0),[(.neg 56),(.neg 24),(.pos 60),(.pos 63)]),
   ((.exchange 56 28 2),[(.neg 56),(.neg 28),(.pos 58),(.pos 65)]),
   ((.exchange 56 30 0),[(.neg 56),(.neg 30),(.pos 60),(.pos 67)]),
   ((.exchange 56 31 2),[(.neg 56),(.neg 31),(.pos 61),(.pos 65)]),
   ((.exchange 56 33 0),[(.neg 56),(.neg 33),(.pos 63),(.pos 67)]),
   ((.exchange 56 42 6),[(.neg 56),(.neg 42),(.pos 37),(.pos 40)]),
   ((.exchange 56 51 6),[(.neg 56),(.neg 51),(.pos 40),(.pos 46)]),
   ((.exchange 56 53 0),[(.neg 56),(.neg 53),(.pos 63),(.pos 67)]),
   ((.exchange 56 54 2),[(.neg 56),(.neg 54),(.pos 58),(.pos 61),(.pos 65)]),
   ((.exchange 56 64 0),[(.neg 64),(.neg 56),(.pos 60),(.pos 63)]),
   ((.exchange 57 9 6),[(.neg 57),(.neg 9),(.pos 35),(.pos 41),(.pos 47)]),
   ((.exchange 57 24 1),[(.neg 57),(.neg 24),(.pos 60),(.pos 63)]),
   ((.exchange 57 29 2),[(.neg 57),(.neg 29),(.pos 59),(.pos 66)]),
   ((.exchange 57 30 1),[(.neg 57),(.neg 30),(.pos 60),(.pos 67)]),
   ((.exchange 57 32 2),[(.neg 57),(.neg 32),(.pos 62),(.pos 66)]),
   ((.exchange 57 33 1),[(.neg 57),(.neg 33),(.pos 63),(.pos 67)]),
   ((.exchange 57 37 6),[(.neg 57),(.neg 37),(.pos 35),(.pos 38)]),
   ((.exchange 57 43 2),[(.neg 57),(.neg 43),(.pos 59),(.pos 62)]),
   ((.exchange 57 49 2),[(.neg 57),(.neg 49),(.pos 59),(.pos 66)]),
   ((.exchange 57 51 6),[(.neg 57),(.neg 51),(.pos 35),(.pos 41),(.pos 47)]),
   ((.exchange 57 52 2),[(.neg 57),(.neg 52),(.pos 62),(.pos 66)]),
   ((.exchange 57 68 2),[(.neg 68),(.neg 57),(.pos 59),(.pos 66)]),
   ((.exchange 58 2 6),[(.neg 58),(.neg 2),(.pos 36),(.pos 42)]),
   ((.exchange 58 3 6),[(.neg 58),(.neg 3),(.pos 37),(.pos 42)]),
   ((.exchange 58 7 6),[(.neg 58),(.neg 7),(.pos 37),(.pos 48)]),
   ((.exchange 58 14 6),[(.neg 58),(.neg 14),(.pos 37),(.pos 42),(.pos 48)]),
   ((.exchange 58 18 0),[(.neg 58),(.neg 18),(.pos 59),(.pos 60)]),
   ((.exchange 58 23 0),[(.neg 58),(.neg 23),(.pos 59),(.pos 64)]),
   ((.exchange 58 29 0),[(.neg 58),(.neg 29),(.pos 59),(.pos 68)]),
   ((.exchange 58 30 0),[(.neg 58),(.neg 30),(.pos 60),(.pos 68)]),
   ((.exchange 58 34 0),[(.neg 58),(.neg 34),(.pos 64),(.pos 68)]),
   ((.exchange 58 39 3),[(.neg 58),(.neg 39),(.pos 55),(.pos 61)]),
   ((.exchange 58 41 3),[(.neg 58),(.neg 41),(.pos 55),(.pos 56),(.pos 61)]),
   ((.exchange 58 49 0),[(.neg 58),(.neg 49),(.pos 59),(.pos 68)]),
   ((.exchange 58 54 0),[(.neg 58),(.neg 54),(.pos 64),(.pos 68)]),
   ((.exchange 58 57 0),[(.neg 58),(.neg 57),(.pos 59),(.pos 60)])]

theorem certificates_2_valid : ∀ oc ∈ certificates_2,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.BitsetOrigins.bitsetOrigins_sound
  have hchecks : ∀ i : Fin 128,
    Papers.RationalityTen.MatroidChecked.BitsetOrigins.BitsetOrigin U (7 : Fin 8) old newIndex models
      (certificates_2.get i).1 (certificates_2.get i).2 := by
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
  intro oc hoc
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hoc
  exact hchecks i



noncomputable def certificates_3 : List (Origin 70 629 × List Sat.Literal) :=
  [((.exchange 58 66 0),[(.neg 66),(.neg 58),(.pos 59),(.pos 68)]),
   ((.exchange 58 67 0),[(.neg 67),(.neg 58),(.pos 60),(.pos 68)]),
   ((.exchange 58 69 0),[(.neg 69),(.neg 58),(.pos 64),(.pos 68)]),
   ((.exchange 59 2 6),[(.neg 59),(.neg 2),(.pos 36),(.pos 43)]),
   ((.exchange 59 4 6),[(.neg 59),(.neg 4),(.pos 38),(.pos 43)]),
   ((.exchange 59 7 6),[(.neg 59),(.neg 7),(.pos 36),(.pos 38),(.pos 49)]),
   ((.exchange 59 8 6),[(.neg 59),(.neg 8),(.pos 38),(.pos 49)]),
   ((.exchange 59 13 6),[(.neg 59),(.neg 13),(.pos 43),(.pos 49)]),
   ((.exchange 59 14 1),[(.neg 59),(.neg 14),(.pos 60),(.pos 64),(.pos 68)]),
   ((.exchange 59 21 3),[(.neg 59),(.neg 21),(.pos 57),(.pos 62)]),
   ((.exchange 59 24 1),[(.neg 59),(.neg 24),(.pos 60),(.pos 64)]),
   ((.exchange 59 26 3),[(.neg 59),(.neg 26),(.pos 55),(.pos 57),(.pos 66)]),
   ((.exchange 59 32 3),[(.neg 59),(.neg 32),(.pos 62),(.pos 66)]),
   ((.exchange 59 37 1),[(.neg 59),(.neg 37),(.pos 58),(.pos 60)]),
   ((.exchange 59 41 3),[(.neg 59),(.neg 41),(.pos 57),(.pos 62)]),
   ((.exchange 59 42 6),[(.neg 59),(.neg 42),(.pos 36),(.pos 43)]),
   ((.exchange 59 44 6),[(.neg 59),(.neg 44),(.pos 38),(.pos 43)]),
   ((.exchange 59 46 6),[(.neg 59),(.neg 46),(.pos 36),(.pos 38),(.pos 49)]),
   ((.exchange 59 47 6),[(.neg 59),(.neg 47),(.pos 38),(.pos 49)]),
   ((.exchange 59 48 1),[(.neg 59),(.neg 48),(.pos 58),(.pos 68)]),
   ((.exchange 59 48 6),[(.neg 59),(.neg 48),(.pos 36),(.pos 49)]),
   ((.exchange 59 50 6),[(.neg 59),(.neg 50),(.pos 38),(.pos 49)]),
   ((.exchange 59 52 3),[(.neg 59),(.neg 52),(.pos 62),(.pos 66)]),
   ((.exchange 59 52 6),[(.neg 59),(.neg 52),(.pos 43),(.pos 49)]),
   ((.exchange 59 54 1),[(.neg 59),(.neg 54),(.pos 64),(.pos 68)]),
   ((.exchange 59 54 6),[(.neg 59),(.neg 54),(.pos 43),(.pos 49)]),
   ((.exchange 59 63 3),[(.neg 63),(.neg 59),(.pos 57),(.pos 62)]),
   ((.exchange 59 65 1),[(.neg 65),(.neg 59),(.pos 58),(.pos 68)]),
   ((.exchange 59 65 3),[(.neg 65),(.neg 59),(.pos 55),(.pos 66)]),
   ((.exchange 59 67 3),[(.neg 67),(.neg 59),(.pos 57),(.pos 66)]),
   ((.exchange 60 3 6),[(.neg 60),(.neg 3),(.pos 37),(.pos 44)]),
   ((.exchange 60 4 6),[(.neg 60),(.neg 4),(.pos 38),(.pos 44)]),
   ((.exchange 60 7 6),[(.neg 60),(.neg 7),(.pos 37),(.pos 50)]),
   ((.exchange 60 8 6),[(.neg 60),(.neg 8),(.pos 38),(.pos 50)]),
   ((.exchange 60 14 6),[(.neg 60),(.neg 14),(.pos 44),(.pos 50)]),
   ((.exchange 60 16 2),[(.neg 60),(.neg 16),(.pos 58),(.pos 59)]),
   ((.exchange 60 21 3),[(.neg 60),(.neg 21),(.pos 57),(.pos 63)]),
   ((.exchange 60 23 2),[(.neg 60),(.neg 23),(.pos 59),(.pos 64)]),
   ((.exchange 60 26 3),[(.neg 60),(.neg 26),(.pos 56),(.pos 67)]),
   ((.exchange 60 28 2),[(.neg 60),(.neg 28),(.pos 58),(.pos 68)]),
   ((.exchange 60 29 2),[(.neg 60),(.neg 29),(.pos 59),(.pos 68)]),
   ((.exchange 60 32 3),[(.neg 60),(.neg 32),(.pos 57),(.pos 63),(.pos 67)]),
   ((.exchange 60 34 2),[(.neg 60),(.neg 34),(.pos 64),(.pos 68)]),
   ((.exchange 60 36 2),[(.neg 60),(.neg 36),(.pos 58),(.pos 59)]),
   ((.exchange 60 40 3),[(.neg 60),(.neg 40),(.pos 56),(.pos 63)]),
   ((.exchange 60 40 6),[(.neg 60),(.neg 40),(.pos 37),(.pos 44)]),
   ((.exchange 60 41 3),[(.neg 60),(.neg 41),(.pos 57),(.pos 63)]),
   ((.exchange 60 41 6),[(.neg 60),(.neg 41),(.pos 38),(.pos 44)]),
   ((.exchange 60 43 6),[(.neg 60),(.neg 43),(.pos 38),(.pos 44)]),
   ((.exchange 60 45 6),[(.neg 60),(.neg 45),(.pos 37),(.pos 38),(.pos 50)]),
   ((.exchange 60 46 6),[(.neg 60),(.neg 46),(.pos 37),(.pos 50)]),
   ((.exchange 60 48 2),[(.neg 60),(.neg 48),(.pos 58),(.pos 68)]),
   ((.exchange 60 48 6),[(.neg 60),(.neg 48),(.pos 37),(.pos 50)]),
   ((.exchange 60 49 2),[(.neg 60),(.neg 49),(.pos 59),(.pos 68)]),
   ((.exchange 60 54 6),[(.neg 60),(.neg 54),(.pos 44),(.pos 50)]),
   ((.exchange 60 55 2),[(.neg 60),(.neg 55),(.pos 58),(.pos 59)]),
   ((.exchange 60 61 2),[(.neg 61),(.neg 60),(.pos 58),(.pos 64)]),
   ((.exchange 60 61 3),[(.neg 61),(.neg 60),(.pos 56),(.pos 63)]),
   ((.exchange 60 65 2),[(.neg 65),(.neg 60),(.pos 58),(.pos 68)]),
   ((.exchange 60 65 3),[(.neg 65),(.neg 60),(.pos 56),(.pos 67)]),
   ((.exchange 60 69 2),[(.neg 69),(.neg 60),(.pos 64),(.pos 68)]),
   ((.exchange 61 3 6),[(.neg 61),(.neg 3),(.pos 40),(.pos 42)]),
   ((.exchange 61 16 4),[(.neg 61),(.neg 16),(.pos 55),(.pos 58)]),
   ((.exchange 61 21 0),[(.neg 61),(.neg 21),(.pos 62),(.pos 63)]),
   ((.exchange 61 24 0),[(.neg 61),(.neg 24),(.pos 63),(.pos 64)]),
   ((.exchange 61 25 4),[(.neg 61),(.neg 25),(.pos 55),(.pos 65)]),
   ((.exchange 61 27 4),[(.neg 61),(.neg 27),(.pos 55),(.pos 56),(.pos 65)]),
   ((.exchange 61 33 0),[(.neg 61),(.neg 33),(.pos 63),(.pos 69)]),
   ((.exchange 61 34 0),[(.neg 61),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 61 52 0),[(.neg 61),(.neg 52),(.pos 62),(.pos 69)]),
   ((.exchange 61 66 0),[(.neg 66),(.neg 61),(.pos 62),(.pos 69)]),
   ((.exchange 61 67 0),[(.neg 67),(.neg 61),(.pos 63),(.pos 69)]),
   ((.exchange 62 2 6),[(.neg 62),(.neg 2),(.pos 39),(.pos 43)]),
   ((.exchange 62 3 1),[(.neg 62),(.neg 3),(.pos 61),(.pos 63),(.pos 64)]),
   ((.exchange 62 11 6),[(.neg 62),(.neg 11),(.pos 41),(.pos 52)]),
   ((.exchange 62 18 4),[(.neg 62),(.neg 18),(.pos 57),(.pos 59)]),
   ((.exchange 62 25 4),[(.neg 62),(.neg 25),(.pos 55),(.pos 66)]),
   ((.exchange 62 26 1),[(.neg 62),(.neg 26),(.pos 61),(.pos 63),(.pos 69)]),
   ((.exchange 62 31 1),[(.neg 62),(.neg 31),(.pos 61),(.pos 69)]),
   ((.exchange 62 42 6),[(.neg 62),(.neg 42),(.pos 39),(.pos 43)]),
   ((.exchange 62 45 6),[(.neg 62),(.neg 45),(.pos 39),(.pos 52)]),
   ((.exchange 62 46 6),[(.neg 62),(.neg 46),(.pos 39),(.pos 41),(.pos 52)]),
   ((.exchange 62 47 4),[(.neg 62),(.neg 47),(.pos 57),(.pos 66)]),
   ((.exchange 62 58 4),[(.neg 62),(.neg 58),(.pos 55),(.pos 59)]),
   ((.exchange 62 65 4),[(.neg 65),(.neg 62),(.pos 55),(.pos 66)]),
   ((.exchange 62 67 4),[(.neg 67),(.neg 62),(.pos 57),(.pos 66)]),
   ((.exchange 63 2 6),[(.neg 63),(.neg 2),(.pos 40),(.pos 41),(.pos 44)]),
   ((.exchange 63 9 6),[(.neg 63),(.neg 9),(.pos 40),(.pos 41),(.pos 53)]),
   ((.exchange 63 11 6),[(.neg 63),(.neg 11),(.pos 41),(.pos 53)]),
   ((.exchange 63 16 4),[(.neg 63),(.neg 16),(.pos 56),(.pos 57),(.pos 60)]),
   ((.exchange 63 18 4),[(.neg 63),(.neg 18),(.pos 57),(.pos 60)]),
   ((.exchange 63 19 2),[(.neg 63),(.neg 19),(.pos 61),(.pos 62)]),
   ((.exchange 63 22 2),[(.neg 63),(.neg 22),(.pos 61),(.pos 64)]),
   ((.exchange 63 23 2),[(.neg 63),(.neg 23),(.pos 62),(.pos 64)]),
   ((.exchange 63 25 4),[(.neg 63),(.neg 25),(.pos 56),(.pos 57),(.pos 67)]),
   ((.exchange 63 26 4),[(.neg 63),(.neg 26),(.pos 56),(.pos 67)]),
   ((.exchange 63 27 4),[(.neg 63),(.neg 27),(.pos 57),(.pos 67)]),
   ((.exchange 63 30 4),[(.neg 63),(.neg 30),(.pos 60),(.pos 67)]),
   ((.exchange 63 31 2),[(.neg 63),(.neg 31),(.pos 61),(.pos 69)]),
   ((.exchange 63 36 4),[(.neg 63),(.neg 36),(.pos 56),(.pos 57),(.pos 60)]),
   ((.exchange 63 36 6),[(.neg 63),(.neg 36),(.pos 40),(.pos 41),(.pos 44)]),
   ((.exchange 63 43 6),[(.neg 63),(.neg 43),(.pos 41),(.pos 44)]),
   ((.exchange 63 47 4),[(.neg 63),(.neg 47),(.pos 57),(.pos 67)]),
   ((.exchange 63 51 2),[(.neg 63),(.neg 51),(.pos 61),(.pos 69)]),
   ((.exchange 63 51 6),[(.neg 63),(.neg 51),(.pos 40),(.pos 53)]),
   ((.exchange 63 52 6),[(.neg 63),(.neg 52),(.pos 41),(.pos 53)]),
   ((.exchange 63 58 4),[(.neg 63),(.neg 58),(.pos 56),(.pos 60)]),
   ((.exchange 63 66 2),[(.neg 66),(.neg 63),(.pos 62),(.pos 69)]),
   ((.exchange 64 2 6),[(.neg 64),(.neg 2),(.pos 42),(.pos 43)]),
   ((.exchange 64 16 4),[(.neg 64),(.neg 16),(.pos 58),(.pos 59)]),
   ((.exchange 64 17 4),[(.neg 64),(.neg 17),(.pos 58),(.pos 60)]),
   ((.exchange 64 26 3),[(.neg 64),(.neg 26),(.pos 61),(.pos 63),(.pos 69)]),
   ((.exchange 64 28 4),[(.neg 64),(.neg 28),(.pos 58),(.pos 68)]),
   ((.exchange 64 29 4),[(.neg 64),(.neg 29),(.pos 59),(.pos 68)]),
   ((.exchange 64 30 4),[(.neg 64),(.neg 30),(.pos 60),(.pos 68)]),
   ((.exchange 64 31 3),[(.neg 64),(.neg 31),(.pos 61),(.pos 69)]),
   ((.exchange 64 37 4),[(.neg 64),(.neg 37),(.pos 58),(.pos 60)]),
   ((.exchange 64 39 6),[(.neg 64),(.neg 39),(.pos 42),(.pos 43)]),
   ((.exchange 64 40 3),[(.neg 64),(.neg 40),(.pos 61),(.pos 63)]),
   ((.exchange 64 40 6),[(.neg 64),(.neg 40),(.pos 42),(.pos 44)]),
   ((.exchange 64 41 3),[(.neg 64),(.neg 41),(.pos 62),(.pos 63)]),
   ((.exchange 64 41 6),[(.neg 64),(.neg 41),(.pos 43),(.pos 44)]),
   ((.exchange 64 48 4),[(.neg 64),(.neg 48),(.pos 58),(.pos 68)]),
   ((.exchange 64 49 4),[(.neg 64),(.neg 49),(.pos 59),(.pos 68)]),
   ((.exchange 64 53 6),[(.neg 64),(.neg 53),(.pos 44),(.pos 54)]),
   ((.exchange 64 56 4),[(.neg 64),(.neg 56),(.pos 58),(.pos 60)]),
   ((.exchange 64 57 4),[(.neg 64),(.neg 57),(.pos 59),(.pos 60)]),
   ((.exchange 64 65 4),[(.neg 65),(.neg 64),(.pos 58),(.pos 68)])]

theorem certificates_3_valid : ∀ oc ∈ certificates_3,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.BitsetOrigins.bitsetOrigins_sound
  have hchecks : ∀ i : Fin 128,
    Papers.RationalityTen.MatroidChecked.BitsetOrigins.BitsetOrigin U (7 : Fin 8) old newIndex models
      (certificates_3.get i).1 (certificates_3.get i).2 := by
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
  intro oc hoc
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hoc
  exact hchecks i



noncomputable def certificates_4 : List (Origin 70 629 × List Sat.Literal) :=
  [((.exchange 64 66 3),[(.neg 66),(.neg 64),(.pos 62),(.pos 69)]),
   ((.exchange 64 66 4),[(.neg 66),(.neg 64),(.pos 59),(.pos 68)]),
   ((.exchange 64 67 4),[(.neg 67),(.neg 64),(.pos 60),(.pos 68)]),
   ((.exchange 65 10 6),[(.neg 65),(.neg 10),(.pos 46),(.pos 51)]),
   ((.exchange 65 13 6),[(.neg 65),(.neg 13),(.pos 45),(.pos 48),(.pos 51)]),
   ((.exchange 65 14 6),[(.neg 65),(.neg 14),(.pos 46),(.pos 48),(.pos 51)]),
   ((.exchange 65 27 0),[(.neg 65),(.neg 27),(.pos 66),(.pos 67)]),
   ((.exchange 65 29 0),[(.neg 65),(.neg 29),(.pos 66),(.pos 68)]),
   ((.exchange 65 30 0),[(.neg 65),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 65 32 0),[(.neg 65),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 65 33 0),[(.neg 65),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 65 34 0),[(.neg 65),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 65 39 5),[(.neg 65),(.neg 39),(.pos 55),(.pos 61)]),
   ((.exchange 65 40 5),[(.neg 65),(.neg 40),(.pos 56),(.pos 61)]),
   ((.exchange 65 41 5),[(.neg 65),(.neg 41),(.pos 55),(.pos 56),(.pos 61)]),
   ((.exchange 65 49 0),[(.neg 65),(.neg 49),(.pos 66),(.pos 68)]),
   ((.exchange 65 50 0),[(.neg 65),(.neg 50),(.pos 67),(.pos 68)]),
   ((.exchange 65 50 6),[(.neg 65),(.neg 50),(.pos 46),(.pos 48)]),
   ((.exchange 65 53 0),[(.neg 65),(.neg 53),(.pos 67),(.pos 69)]),
   ((.exchange 65 54 0),[(.neg 65),(.neg 54),(.pos 68),(.pos 69)]),
   ((.exchange 65 57 0),[(.neg 65),(.neg 57),(.pos 66),(.pos 67)]),
   ((.exchange 65 59 5),[(.neg 65),(.neg 59),(.pos 55),(.pos 58)]),
   ((.exchange 66 6 6),[(.neg 66),(.neg 6),(.pos 45),(.pos 49)]),
   ((.exchange 66 8 6),[(.neg 66),(.neg 8),(.pos 47),(.pos 49)]),
   ((.exchange 66 9 6),[(.neg 66),(.neg 9),(.pos 45),(.pos 52)]),
   ((.exchange 66 11 6),[(.neg 66),(.neg 11),(.pos 47),(.pos 52)]),
   ((.exchange 66 13 6),[(.neg 66),(.neg 13),(.pos 49),(.pos 52)]),
   ((.exchange 66 20 5),[(.neg 66),(.neg 20),(.pos 55),(.pos 57),(.pos 62)]),
   ((.exchange 66 21 5),[(.neg 66),(.neg 21),(.pos 57),(.pos 62)]),
   ((.exchange 66 23 5),[(.neg 66),(.neg 23),(.pos 59),(.pos 62)]),
   ((.exchange 66 30 1),[(.neg 66),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 66 33 1),[(.neg 66),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 66 34 1),[(.neg 66),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 66 36 6),[(.neg 66),(.neg 36),(.pos 45),(.pos 49)]),
   ((.exchange 66 38 6),[(.neg 66),(.neg 38),(.pos 47),(.pos 49)]),
   ((.exchange 66 39 6),[(.neg 66),(.neg 39),(.pos 45),(.pos 52)]),
   ((.exchange 66 40 5),[(.neg 66),(.neg 40),(.pos 55),(.pos 57),(.pos 62)]),
   ((.exchange 66 41 5),[(.neg 66),(.neg 41),(.pos 57),(.pos 62)]),
   ((.exchange 66 41 6),[(.neg 66),(.neg 41),(.pos 47),(.pos 52)]),
   ((.exchange 66 43 6),[(.neg 66),(.neg 43),(.pos 49),(.pos 52)]),
   ((.exchange 66 46 1),[(.neg 66),(.neg 46),(.pos 65),(.pos 67)]),
   ((.exchange 66 48 6),[(.neg 66),(.neg 48),(.pos 45),(.pos 49)]),
   ((.exchange 66 50 6),[(.neg 66),(.neg 50),(.pos 47),(.pos 49)]),
   ((.exchange 66 51 6),[(.neg 66),(.neg 51),(.pos 45),(.pos 52)]),
   ((.exchange 66 54 6),[(.neg 66),(.neg 54),(.pos 49),(.pos 52)]),
   ((.exchange 66 56 1),[(.neg 66),(.neg 56),(.pos 65),(.pos 67)]),
   ((.exchange 66 58 1),[(.neg 66),(.neg 58),(.pos 65),(.pos 68)]),
   ((.exchange 66 58 5),[(.neg 66),(.neg 58),(.pos 55),(.pos 59)]),
   ((.exchange 66 60 5),[(.neg 66),(.neg 60),(.pos 57),(.pos 59)]),
   ((.exchange 66 61 1),[(.neg 66),(.neg 61),(.pos 65),(.pos 69)]),
   ((.exchange 66 64 5),[(.neg 66),(.neg 64),(.pos 59),(.pos 62)]),
   ((.exchange 67 7 6),[(.neg 67),(.neg 7),(.pos 46),(.pos 50)]),
   ((.exchange 67 8 6),[(.neg 67),(.neg 8),(.pos 47),(.pos 50)]),
   ((.exchange 67 14 6),[(.neg 67),(.neg 14),(.pos 50),(.pos 53)]),
   ((.exchange 67 21 5),[(.neg 67),(.neg 21),(.pos 57),(.pos 63)]),
   ((.exchange 67 24 5),[(.neg 67),(.neg 24),(.pos 60),(.pos 63)]),
   ((.exchange 67 25 2),[(.neg 67),(.neg 25),(.pos 65),(.pos 66)]),
   ((.exchange 67 28 2),[(.neg 67),(.neg 28),(.pos 65),(.pos 68)]),
   ((.exchange 67 29 2),[(.neg 67),(.neg 29),(.pos 66),(.pos 68)]),
   ((.exchange 67 34 2),[(.neg 67),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 67 36 6),[(.neg 67),(.neg 36),(.pos 46),(.pos 47),(.pos 50)]),
   ((.exchange 67 37 6),[(.neg 67),(.neg 37),(.pos 46),(.pos 50)]),
   ((.exchange 67 38 6),[(.neg 67),(.neg 38),(.pos 47),(.pos 50)]),
   ((.exchange 67 39 6),[(.neg 67),(.neg 39),(.pos 46),(.pos 47),(.pos 53)]),
   ((.exchange 67 40 6),[(.neg 67),(.neg 40),(.pos 46),(.pos 53)]),
   ((.exchange 67 41 6),[(.neg 67),(.neg 41),(.pos 47),(.pos 53)]),
   ((.exchange 67 45 2),[(.neg 67),(.neg 45),(.pos 65),(.pos 66)]),
   ((.exchange 67 48 2),[(.neg 67),(.neg 48),(.pos 65),(.pos 68)]),
   ((.exchange 67 48 6),[(.neg 67),(.neg 48),(.pos 46),(.pos 50)]),
   ((.exchange 67 49 6),[(.neg 67),(.neg 49),(.pos 47),(.pos 50)]),
   ((.exchange 67 51 2),[(.neg 67),(.neg 51),(.pos 65),(.pos 69)]),
   ((.exchange 67 51 6),[(.neg 67),(.neg 51),(.pos 46),(.pos 53)]),
   ((.exchange 67 52 6),[(.neg 67),(.neg 52),(.pos 47),(.pos 53)]),
   ((.exchange 67 54 6),[(.neg 67),(.neg 54),(.pos 50),(.pos 53)]),
   ((.exchange 67 55 2),[(.neg 67),(.neg 55),(.pos 65),(.pos 66)]),
   ((.exchange 67 58 2),[(.neg 67),(.neg 58),(.pos 65),(.pos 68)]),
   ((.exchange 67 58 5),[(.neg 67),(.neg 58),(.pos 56),(.pos 60)]),
   ((.exchange 67 61 2),[(.neg 67),(.neg 61),(.pos 65),(.pos 69)]),
   ((.exchange 67 62 5),[(.neg 67),(.neg 62),(.pos 57),(.pos 63)]),
   ((.exchange 68 2 6),[(.neg 68),(.neg 2),(.pos 48),(.pos 49),(.pos 54)]),
   ((.exchange 68 3 6),[(.neg 68),(.neg 3),(.pos 48),(.pos 50),(.pos 54)]),
   ((.exchange 68 8 6),[(.neg 68),(.neg 8),(.pos 49),(.pos 50)]),
   ((.exchange 68 13 6),[(.neg 68),(.neg 13),(.pos 49),(.pos 54)]),
   ((.exchange 68 14 6),[(.neg 68),(.neg 14),(.pos 50),(.pos 54)]),
   ((.exchange 68 16 5),[(.neg 68),(.neg 16),(.pos 58),(.pos 59)]),
   ((.exchange 68 17 5),[(.neg 68),(.neg 17),(.pos 58),(.pos 60)]),
   ((.exchange 68 18 5),[(.neg 68),(.neg 18),(.pos 59),(.pos 60)]),
   ((.exchange 68 22 5),[(.neg 68),(.neg 22),(.pos 58),(.pos 64)]),
   ((.exchange 68 23 5),[(.neg 68),(.neg 23),(.pos 59),(.pos 64)]),
   ((.exchange 68 24 5),[(.neg 68),(.neg 24),(.pos 60),(.pos 64)]),
   ((.exchange 68 26 3),[(.neg 68),(.neg 26),(.pos 65),(.pos 67)]),
   ((.exchange 68 31 3),[(.neg 68),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 68 33 3),[(.neg 68),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 68 36 5),[(.neg 68),(.neg 36),(.pos 58),(.pos 59)]),
   ((.exchange 68 37 5),[(.neg 68),(.neg 37),(.pos 58),(.pos 60)]),
   ((.exchange 68 42 5),[(.neg 68),(.neg 42),(.pos 58),(.pos 64)]),
   ((.exchange 68 43 5),[(.neg 68),(.neg 43),(.pos 59),(.pos 64)]),
   ((.exchange 68 45 3),[(.neg 68),(.neg 45),(.pos 65),(.pos 66)]),
   ((.exchange 68 46 3),[(.neg 68),(.neg 46),(.pos 65),(.pos 67)]),
   ((.exchange 68 47 6),[(.neg 68),(.neg 47),(.pos 49),(.pos 50)]),
   ((.exchange 68 51 3),[(.neg 68),(.neg 51),(.pos 65),(.pos 69)]),
   ((.exchange 68 55 5),[(.neg 68),(.neg 55),(.pos 58),(.pos 59)]),
   ((.exchange 68 56 3),[(.neg 68),(.neg 56),(.pos 65),(.pos 67)]),
   ((.exchange 68 57 3),[(.neg 68),(.neg 57),(.pos 66),(.pos 67)]),
   ((.exchange 68 57 5),[(.neg 68),(.neg 57),(.pos 59),(.pos 60)]),
   ((.exchange 68 62 5),[(.neg 68),(.neg 62),(.pos 59),(.pos 64)]),
   ((.exchange 68 63 5),[(.neg 68),(.neg 63),(.pos 60),(.pos 64)]),
   ((.exchange 69 11 6),[(.neg 69),(.neg 11),(.pos 52),(.pos 53)]),
   ((.exchange 69 13 6),[(.neg 69),(.neg 13),(.pos 52),(.pos 54)]),
   ((.exchange 69 14 6),[(.neg 69),(.neg 14),(.pos 53),(.pos 54)]),
   ((.exchange 69 19 5),[(.neg 69),(.neg 19),(.pos 61),(.pos 62)]),
   ((.exchange 69 20 5),[(.neg 69),(.neg 20),(.pos 61),(.pos 63)]),
   ((.exchange 69 22 5),[(.neg 69),(.neg 22),(.pos 61),(.pos 64)]),
   ((.exchange 69 23 5),[(.neg 69),(.neg 23),(.pos 62),(.pos 64)]),
   ((.exchange 69 27 4),[(.neg 69),(.neg 27),(.pos 66),(.pos 67)]),
   ((.exchange 69 28 4),[(.neg 69),(.neg 28),(.pos 65),(.pos 68)]),
   ((.exchange 69 29 4),[(.neg 69),(.neg 29),(.pos 66),(.pos 68)]),
   ((.exchange 69 30 4),[(.neg 69),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 69 36 6),[(.neg 69),(.neg 36),(.pos 51),(.pos 52),(.pos 54)]),
   ((.exchange 69 40 5),[(.neg 69),(.neg 40),(.pos 61),(.pos 63)]),
   ((.exchange 69 42 5),[(.neg 69),(.neg 42),(.pos 61),(.pos 64)]),
   ((.exchange 69 43 6),[(.neg 69),(.neg 43),(.pos 52),(.pos 54)]),
   ((.exchange 69 45 6),[(.neg 69),(.neg 45),(.pos 51),(.pos 52)]),
   ((.exchange 69 46 4),[(.neg 69),(.neg 46),(.pos 65),(.pos 67)]),
   ((.exchange 69 46 6),[(.neg 69),(.neg 46),(.pos 51),(.pos 53)]),
   ((.exchange 69 47 4),[(.neg 69),(.neg 47),(.pos 66),(.pos 67)]),
   ((.exchange 69 47 6),[(.neg 69),(.neg 47),(.pos 52),(.pos 53)]),
   ((.exchange 69 49 4),[(.neg 69),(.neg 49),(.pos 66),(.pos 68)])]

theorem certificates_4_valid : ∀ oc ∈ certificates_4,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.BitsetOrigins.bitsetOrigins_sound
  have hchecks : ∀ i : Fin 128,
    Papers.RationalityTen.MatroidChecked.BitsetOrigins.BitsetOrigin U (7 : Fin 8) old newIndex models
      (certificates_4.get i).1 (certificates_4.get i).2 := by
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
  intro oc hoc
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hoc
  exact hchecks i



noncomputable def certificates_5 : List (Origin 70 629 × List Sat.Literal) :=
  [((.exchange 69 50 4),[(.neg 69),(.neg 50),(.pos 67),(.pos 68)]),
   ((.exchange 69 55 4),[(.neg 69),(.neg 55),(.pos 65),(.pos 66)]),
   ((.exchange 69 55 5),[(.neg 69),(.neg 55),(.pos 61),(.pos 62)]),
   ((.exchange 69 56 4),[(.neg 69),(.neg 56),(.pos 65),(.pos 67)]),
   ((.exchange 69 56 5),[(.neg 69),(.neg 56),(.pos 61),(.pos 63)]),
   ((.exchange 69 57 4),[(.neg 69),(.neg 57),(.pos 66),(.pos 67)]),
   ((.exchange 69 58 5),[(.neg 69),(.neg 58),(.pos 61),(.pos 64)]),
   (.newPoint,[(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 0),[(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 1),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 58),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 48),(.neg 44),(.neg 42),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 43),(.pos 45),(.pos 46),(.pos 47),(.pos 49),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 59),(.pos 62),(.pos 66)]),
   ((.excluded 2),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 58),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 48),(.pos 51),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 59),(.pos 62),(.pos 66)]),
   ((.excluded 3),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 44),(.pos 55),(.pos 56),(.pos 57),(.pos 59),(.pos 62),(.pos 66)]),
   ((.excluded 4),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 55),(.pos 56),(.pos 57),(.pos 59),(.pos 62),(.pos 66)]),
   ((.excluded 5),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 58),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 59),(.pos 62),(.pos 66)]),
   ((.excluded 6),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 55),(.pos 56),(.pos 57),(.pos 59),(.pos 62),(.pos 66)]),
   ((.excluded 7),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 44),(.neg 43),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 51),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 61),(.pos 65)]),
   ((.excluded 8),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 54),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 43),(.neg 42),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 50),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 9),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57),(.pos 64)]),
   ((.excluded 10),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57),(.pos 68)]),
   ((.excluded 11),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57),(.pos 69)]),
   ((.excluded 12),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 13),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 48),(.pos 51),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 14),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 43),(.pos 44),(.pos 48),(.pos 51),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 64)]),
   ((.excluded 15),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 53),(.neg 52),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 68)]),
   ((.excluded 16),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 48),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 69)]),
   ((.excluded 17),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 48),(.pos 51),(.pos 54),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 18),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 43),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 19),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 49),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 20),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 21),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 22),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 43),(.pos 50),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 61),(.pos 65)]),
   ((.excluded 23),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 43),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 61),(.pos 65)]),
   ((.excluded 24),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 43),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 61),(.pos 65)]),
   ((.excluded 25),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 54),(.neg 53),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 61),(.pos 65)]),
   ((.excluded 26),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 61),(.pos 65)]),
   ((.excluded 27),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 44),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 61),(.pos 65)]),
   ((.excluded 28),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 61),(.pos 65)]),
   ((.excluded 29),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 44),(.pos 49),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 61),(.pos 65)]),
   ((.excluded 30),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 44),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 61),(.pos 65)]),
   ((.excluded 31),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 49),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 61),(.pos 65)]),
   ((.excluded 32),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 49),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 61),(.pos 65)]),
   ((.excluded 33),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 61),(.pos 65)]),
   ((.excluded 34),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 61),(.pos 65)]),
   ((.excluded 35),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 43),(.pos 50),(.pos 55),(.pos 56),(.pos 57),(.pos 69)]),
   ((.excluded 36),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 43),(.pos 50),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 37),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 43),(.pos 55),(.pos 56),(.pos 57),(.pos 69)]),
   ((.excluded 38),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 43),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 68)]),
   ((.excluded 39),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 43),(.pos 53),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 40),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 43),(.pos 55),(.pos 56),(.pos 57),(.pos 68)]),
   ((.excluded 41),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 43),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 42),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 55),(.pos 56),(.pos 57),(.pos 69)]),
   ((.excluded 43),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 64)]),
   ((.excluded 44),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 52),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 45),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 55),(.pos 56),(.pos 57),(.pos 64)]),
   ((.excluded 46),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 47),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 44),(.pos 49),(.pos 55),(.pos 56),(.pos 57),(.pos 69)]),
   ((.excluded 48),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 44),(.pos 55),(.pos 56),(.pos 57),(.pos 69)]),
   ((.excluded 49),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 49),(.pos 55),(.pos 56),(.pos 57),(.pos 69)]),
   ((.excluded 50),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 55),(.pos 56),(.pos 57),(.pos 69)]),
   ((.excluded 51),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 44),(.pos 49),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 52),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 44),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 68)]),
   ((.excluded 53),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 44),(.pos 52),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 54),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 44),(.pos 55),(.pos 56),(.pos 57),(.pos 68)]),
   ((.excluded 55),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 44),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 56),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 49),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 64)]),
   ((.excluded 57),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 49),(.pos 53),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 58),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 49),(.pos 55),(.pos 56),(.pos 57),(.pos 64)]),
   ((.excluded 59),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 49),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 60),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 64)]),
   ((.excluded 61),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 68)]),
   ((.excluded 62),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 52),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 63),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 64)]),
   ((.excluded 64),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 55),(.pos 56),(.pos 57),(.pos 64)]),
   ((.excluded 65),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 68)]),
   ((.excluded 66),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 53),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 67),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 55),(.pos 56),(.pos 57),(.pos 68)]),
   ((.excluded 68),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 69),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 47),(.neg 46),(.neg 45),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 42),(.pos 43),(.pos 44),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 54),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 68)]),
   ((.excluded 70),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 48),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 71),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 51),(.pos 54),(.pos 64),(.pos 65)]),
   ((.excluded 72),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 43),(.pos 44),(.pos 48),(.pos 51),(.pos 54),(.pos 64),(.pos 66)]),
   ((.excluded 73),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 43),(.pos 44),(.pos 48),(.pos 51),(.pos 54),(.pos 64),(.pos 67)]),
   ((.excluded 74),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 43),(.pos 44),(.pos 48),(.pos 51),(.pos 54),(.pos 64)]),
   ((.excluded 75),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 76),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 51),(.pos 54),(.pos 59),(.pos 63),(.pos 65)]),
   ((.excluded 77),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 51),(.pos 54),(.pos 59),(.pos 65)]),
   ((.excluded 78),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 51),(.pos 54),(.pos 63),(.pos 65)]),
   ((.excluded 79),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 51),(.pos 54),(.pos 60),(.pos 62),(.pos 65)]),
   ((.excluded 80),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 51),(.pos 54),(.pos 60),(.pos 65)]),
   ((.excluded 81),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 51),(.pos 54),(.pos 62),(.pos 65)]),
   ((.excluded 82),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 51),(.pos 54),(.pos 65)]),
   ((.excluded 83),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 54),(.pos 61),(.pos 68)]),
   ((.excluded 84),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 54),(.pos 62),(.pos 68)]),
   ((.excluded 85),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 54),(.pos 63),(.pos 68)]),
   ((.excluded 86),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 54),(.pos 68)]),
   ((.excluded 87),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 48),(.pos 51),(.pos 54),(.pos 59),(.pos 61),(.pos 67)]),
   ((.excluded 88),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 48),(.pos 51),(.pos 54),(.pos 59),(.pos 61)]),
   ((.excluded 89),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 48),(.pos 51),(.pos 54),(.pos 61),(.pos 67)]),
   ((.excluded 90),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 48),(.pos 51),(.pos 54),(.pos 60),(.pos 61),(.pos 66)]),
   ((.excluded 91),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 48),(.pos 51),(.pos 54),(.pos 60),(.pos 61)]),
   ((.excluded 92),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 48),(.pos 51),(.pos 54),(.pos 61),(.pos 66)]),
   ((.excluded 93),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 48),(.pos 51),(.pos 54),(.pos 61)]),
   ((.excluded 94),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 42),(.pos 48),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 58),(.pos 69)]),
   ((.excluded 95),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 48),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 59),(.pos 69)]),
   ((.excluded 96),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 48),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 60),(.pos 69)]),
   ((.excluded 97),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 48),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 69)]),
   ((.excluded 98),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 42),(.pos 48),(.pos 51),(.pos 54),(.pos 58),(.pos 62),(.pos 67)]),
   ((.excluded 99),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 42),(.pos 48),(.pos 51),(.pos 54),(.pos 58),(.pos 62)]),
   ((.excluded 100),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 42),(.pos 48),(.pos 51),(.pos 54),(.pos 58),(.pos 67)]),
   ((.excluded 101),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 42),(.pos 48),(.pos 51),(.pos 54),(.pos 58),(.pos 63),(.pos 66)]),
   ((.excluded 102),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 42),(.pos 48),(.pos 51),(.pos 54),(.pos 58),(.pos 63)]),
   ((.excluded 103),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 42),(.pos 48),(.pos 51),(.pos 54),(.pos 58),(.pos 66)]),
   ((.excluded 104),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 42),(.pos 48),(.pos 51),(.pos 54),(.pos 58)]),
   ((.excluded 105),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 48),(.pos 51),(.pos 54),(.pos 59),(.pos 63)]),
   ((.excluded 106),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 48),(.pos 51),(.pos 54),(.pos 59),(.pos 67)]),
   ((.excluded 107),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 48),(.pos 51),(.pos 54),(.pos 59)]),
   ((.excluded 108),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 48),(.pos 51),(.pos 54),(.pos 63),(.pos 66)]),
   ((.excluded 109),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 48),(.pos 51),(.pos 54),(.pos 63)]),
   ((.excluded 110),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 48),(.pos 51),(.pos 54),(.pos 60),(.pos 66)]),
   ((.excluded 111),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 48),(.pos 51),(.pos 54),(.pos 66)]),
   ((.excluded 112),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 48),(.pos 51),(.pos 54),(.pos 60),(.pos 62)]),
   ((.excluded 113),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 48),(.pos 51),(.pos 54),(.pos 60)]),
   ((.excluded 114),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 48),(.pos 51),(.pos 54),(.pos 62),(.pos 67)]),
   ((.excluded 115),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 48),(.pos 51),(.pos 54),(.pos 62)]),
   ((.excluded 116),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 48),(.pos 51),(.pos 54),(.pos 67)]),
   ((.excluded 117),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 48),(.pos 51),(.pos 54)]),
   ((.excluded 118),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 43),(.pos 49),(.pos 59),(.pos 69)]),
   ((.excluded 119),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 43),(.pos 49),(.pos 59),(.pos 63),(.pos 65)])]

theorem certificates_5_valid : ∀ oc ∈ certificates_5,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.BitsetOrigins.bitsetOrigins_sound
  have hchecks : ∀ i : Fin 128,
    Papers.RationalityTen.MatroidChecked.BitsetOrigins.BitsetOrigin U (7 : Fin 8) old newIndex models
      (certificates_5.get i).1 (certificates_5.get i).2 := by
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
  intro oc hoc
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hoc
  exact hchecks i



end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C68

end
end
end BundlePart0

