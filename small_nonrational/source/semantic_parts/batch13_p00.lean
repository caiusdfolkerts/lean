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
/- Source: MatroidChecked/SemanticParts/Cases12Part00/Checks00.lean -/



@[expose] public section
noncomputable section


set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C62


noncomputable def certificates_0 : List (Origin 70 1111 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.neg 2)]),
   ((.fixed 3),[(.neg 3)]),
   ((.fixed 4),[(.neg 4)]),
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
   ((.fixed 15),[(.pos 15)]),
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
   ((.exchange 5 41 5),[(.neg 41),(.neg 5),(.pos 1),(.pos 35)]),
   ((.exchange 6 41 5),[(.neg 41),(.neg 6),(.pos 0),(.pos 2),(.pos 36)]),
   ((.exchange 7 41 5),[(.neg 41),(.neg 7),(.pos 0),(.pos 3),(.pos 37)]),
   ((.exchange 8 41 5),[(.neg 41),(.neg 8),(.pos 4),(.pos 38)]),
   ((.exchange 9 41 5),[(.neg 41),(.neg 9),(.pos 1),(.pos 39)]),
   ((.exchange 10 41 5),[(.neg 41),(.neg 10),(.pos 1),(.pos 40)]),
   ((.exchange 11 35 5),[(.neg 35),(.neg 11),(.pos 1),(.pos 41)]),
   ((.exchange 11 36 5),[(.neg 36),(.neg 11),(.pos 1),(.pos 4),(.pos 41)]),
   ((.exchange 11 37 5),[(.neg 37),(.neg 11),(.pos 1),(.pos 4),(.pos 41)]),
   ((.exchange 11 38 5),[(.neg 38),(.neg 11),(.pos 4),(.pos 41)]),
   ((.exchange 11 39 5),[(.neg 39),(.neg 11),(.pos 1),(.pos 41)]),
   ((.exchange 11 40 5),[(.neg 40),(.neg 11),(.pos 1),(.pos 41)]),
   ((.exchange 11 42 5),[(.neg 42),(.neg 11),(.pos 1),(.pos 4),(.pos 41)]),
   ((.exchange 11 43 5),[(.neg 43),(.neg 11),(.pos 4),(.pos 41)]),
   ((.exchange 11 44 5),[(.neg 44),(.neg 11),(.pos 4),(.pos 41)]),
   ((.exchange 12 41 5),[(.neg 41),(.neg 12),(.pos 2),(.pos 3),(.pos 42)]),
   ((.exchange 13 41 5),[(.neg 41),(.neg 13),(.pos 4),(.pos 43)]),
   ((.exchange 14 41 5),[(.neg 41),(.neg 14),(.pos 4),(.pos 44)]),
   ((.exchange 35 25 2),[(.neg 35),(.neg 25),(.pos 45),(.pos 55)]),
   ((.exchange 35 26 1),[(.neg 35),(.neg 26),(.pos 46),(.pos 56)]),
   ((.exchange 35 27 0),[(.neg 35),(.neg 27),(.pos 47),(.pos 57)]),
   ((.exchange 35 65 1),[(.neg 65),(.neg 35),(.pos 46),(.pos 56)]),
   ((.exchange 36 28 1),[(.neg 36),(.neg 28),(.pos 48),(.pos 58)]),
   ((.exchange 36 29 0),[(.neg 36),(.neg 29),(.pos 49),(.pos 59)]),
   ((.exchange 37 30 0),[(.neg 37),(.neg 30),(.pos 50),(.pos 60)]),
   ((.exchange 37 67 0),[(.neg 67),(.neg 37),(.pos 50),(.pos 60)]),
   ((.exchange 38 67 1),[(.neg 67),(.neg 38),(.pos 50),(.pos 60)]),
   ((.exchange 39 31 1),[(.neg 39),(.neg 31),(.pos 51),(.pos 61)]),
   ((.exchange 39 32 0),[(.neg 39),(.neg 32),(.pos 52),(.pos 62)]),
   ((.exchange 39 65 1),[(.neg 65),(.neg 39),(.pos 51),(.pos 61)]),
   ((.exchange 40 26 4),[(.neg 40),(.neg 26),(.pos 46),(.pos 56)]),
   ((.exchange 40 33 0),[(.neg 40),(.neg 33),(.pos 53),(.pos 63)]),
   ((.exchange 40 67 0),[(.neg 67),(.neg 40),(.pos 53),(.pos 63)]),
   ((.exchange 40 67 4),[(.neg 67),(.neg 40),(.pos 46),(.pos 56)]),
   ((.exchange 41 32 2),[(.neg 41),(.neg 32),(.pos 52),(.pos 62)]),
   ((.exchange 41 66 4),[(.neg 66),(.neg 41),(.pos 47),(.pos 57)]),
   ((.exchange 42 34 0),[(.neg 42),(.neg 34),(.pos 54),(.pos 64)]),
   ((.exchange 42 65 3),[(.neg 65),(.neg 42),(.pos 51),(.pos 61)]),
   ((.exchange 42 65 4),[(.neg 65),(.neg 42),(.pos 48),(.pos 58)]),
   ((.exchange 42 69 3),[(.neg 69),(.neg 42),(.pos 51),(.pos 61)]),
   ((.exchange 43 66 4),[(.neg 66),(.neg 43),(.pos 49),(.pos 59)]),
   ((.exchange 43 69 3),[(.neg 69),(.neg 43),(.pos 52),(.pos 62)]),
   ((.exchange 44 30 4),[(.neg 44),(.neg 30),(.pos 50),(.pos 60)]),
   ((.exchange 44 68 2),[(.neg 68),(.neg 44),(.pos 54),(.pos 64)]),
   ((.exchange 44 69 2),[(.neg 69),(.neg 44),(.pos 54),(.pos 64)]),
   ((.exchange 45 7 1),[(.neg 45),(.neg 7),(.pos 46),(.pos 48)]),
   ((.exchange 45 8 0),[(.neg 45),(.neg 8),(.pos 47),(.pos 49)]),
   ((.exchange 45 10 1),[(.neg 45),(.neg 10),(.pos 46),(.pos 51)]),
   ((.exchange 45 12 1),[(.neg 45),(.neg 12),(.pos 48),(.pos 51)]),
   ((.exchange 45 19 5),[(.neg 45),(.neg 19),(.pos 39),(.pos 55)]),
   ((.exchange 45 26 1),[(.neg 45),(.neg 26),(.pos 46),(.pos 65)]),
   ((.exchange 45 27 0),[(.neg 45),(.neg 27),(.pos 47),(.pos 66)]),
   ((.exchange 45 28 1),[(.neg 45),(.neg 28),(.pos 48),(.pos 65)]),
   ((.exchange 45 29 0),[(.neg 45),(.neg 29),(.pos 49),(.pos 66)]),
   ((.exchange 45 31 1),[(.neg 45),(.neg 31),(.pos 51),(.pos 65)]),
   ((.exchange 45 32 0),[(.neg 45),(.neg 32),(.pos 52),(.pos 66)]),
   ((.exchange 45 53 0),[(.neg 53),(.neg 45),(.pos 47),(.pos 52)]),
   ((.exchange 45 54 0),[(.neg 54),(.neg 45),(.pos 49),(.pos 52)]),
   ((.exchange 45 54 1),[(.neg 54),(.neg 45),(.pos 48),(.pos 51)]),
   ((.exchange 45 56 1),[(.neg 56),(.neg 45),(.pos 46),(.pos 65)]),
   ((.exchange 45 56 5),[(.neg 56),(.neg 45),(.pos 35),(.pos 55)]),
   ((.exchange 45 57 0),[(.neg 57),(.neg 45),(.pos 47),(.pos 66)]),
   ((.exchange 45 59 0),[(.neg 59),(.neg 45),(.pos 49),(.pos 66)]),
   ((.exchange 45 61 1),[(.neg 61),(.neg 45),(.pos 51),(.pos 65)]),
   ((.exchange 45 67 1),[(.neg 67),(.neg 45),(.pos 46),(.pos 65)]),
   ((.exchange 45 68 1),[(.neg 68),(.neg 45),(.pos 48),(.pos 65)]),
   ((.exchange 45 69 1),[(.neg 69),(.neg 45),(.pos 51),(.pos 65)]),
   ((.exchange 46 6 2),[(.neg 46),(.neg 6),(.pos 45),(.pos 48)]),
   ((.exchange 46 8 0),[(.neg 46),(.neg 8),(.pos 47),(.pos 50)]),
   ((.exchange 46 9 2),[(.neg 46),(.neg 9),(.pos 45),(.pos 51)]),
   ((.exchange 46 11 0),[(.neg 46),(.neg 11),(.pos 47),(.pos 53)]),
   ((.exchange 46 12 2),[(.neg 46),(.neg 12),(.pos 48),(.pos 51)]),
   ((.exchange 46 14 0),[(.neg 46),(.neg 14),(.pos 50),(.pos 53)]),
   ((.exchange 46 15 5),[(.neg 46),(.neg 15),(.pos 35),(.pos 56)]),
   ((.exchange 46 25 2),[(.neg 46),(.neg 25),(.pos 45),(.pos 65)]),
   ((.exchange 46 27 0),[(.neg 46),(.neg 27),(.pos 47),(.pos 67)]),
   ((.exchange 46 28 2),[(.neg 46),(.neg 28),(.pos 48),(.pos 65)]),
   ((.exchange 46 30 0),[(.neg 46),(.neg 30),(.pos 50),(.pos 67)]),
   ((.exchange 46 31 2),[(.neg 46),(.neg 31),(.pos 51),(.pos 65)]),
   ((.exchange 46 33 0),[(.neg 46),(.neg 33),(.pos 53),(.pos 67)]),
   ((.exchange 46 36 2),[(.neg 46),(.neg 36),(.pos 45),(.pos 48)]),
   ((.exchange 46 39 2),[(.neg 46),(.neg 39),(.pos 45),(.pos 51)]),
   ((.exchange 46 41 0),[(.neg 46),(.neg 41),(.pos 47),(.pos 53)]),
   ((.exchange 46 42 2),[(.neg 46),(.neg 42),(.pos 48),(.pos 51)]),
   ((.exchange 46 54 0),[(.neg 54),(.neg 46),(.pos 50),(.pos 53)]),
   ((.exchange 46 54 2),[(.neg 54),(.neg 46),(.pos 48),(.pos 51)]),
   ((.exchange 46 55 2),[(.neg 55),(.neg 46),(.pos 45),(.pos 65)]),
   ((.exchange 46 57 0),[(.neg 57),(.neg 46),(.pos 47),(.pos 67)]),
   ((.exchange 46 60 0),[(.neg 60),(.neg 46),(.pos 50),(.pos 67)]),
   ((.exchange 46 64 0),[(.neg 64),(.neg 46),(.pos 50),(.pos 53),(.pos 67)]),
   ((.exchange 46 69 0),[(.neg 69),(.neg 46),(.pos 53),(.pos 67)]),
   ((.exchange 46 69 2),[(.neg 69),(.neg 46),(.pos 51),(.pos 65)]),
   ((.exchange 47 6 2),[(.neg 47),(.neg 6),(.pos 45),(.pos 49)])]

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



noncomputable def certificates_1 : List (Origin 70 1111 × List Sat.Literal) :=
  [((.exchange 47 7 1),[(.neg 47),(.neg 7),(.pos 46),(.pos 50)]),
   ((.exchange 47 9 2),[(.neg 47),(.neg 9),(.pos 45),(.pos 52)]),
   ((.exchange 47 10 1),[(.neg 47),(.neg 10),(.pos 46),(.pos 53)]),
   ((.exchange 47 14 1),[(.neg 47),(.neg 14),(.pos 50),(.pos 53)]),
   ((.exchange 47 15 5),[(.neg 47),(.neg 15),(.pos 35),(.pos 57)]),
   ((.exchange 47 25 2),[(.neg 47),(.neg 25),(.pos 45),(.pos 66)]),
   ((.exchange 47 26 1),[(.neg 47),(.neg 26),(.pos 46),(.pos 67)]),
   ((.exchange 47 29 2),[(.neg 47),(.neg 29),(.pos 49),(.pos 66)]),
   ((.exchange 47 32 2),[(.neg 47),(.neg 32),(.pos 52),(.pos 66)]),
   ((.exchange 47 33 1),[(.neg 47),(.neg 33),(.pos 53),(.pos 67)]),
   ((.exchange 47 36 2),[(.neg 47),(.neg 36),(.pos 45),(.pos 49)]),
   ((.exchange 47 37 1),[(.neg 47),(.neg 37),(.pos 46),(.pos 50)]),
   ((.exchange 47 39 2),[(.neg 47),(.neg 39),(.pos 45),(.pos 52)]),
   ((.exchange 47 40 1),[(.neg 47),(.neg 40),(.pos 46),(.pos 53)]),
   ((.exchange 47 43 2),[(.neg 47),(.neg 43),(.pos 49),(.pos 52)]),
   ((.exchange 47 44 1),[(.neg 47),(.neg 44),(.pos 50),(.pos 53)]),
   ((.exchange 47 48 1),[(.neg 48),(.neg 47),(.pos 46),(.pos 50)]),
   ((.exchange 47 51 1),[(.neg 51),(.neg 47),(.pos 46),(.pos 53)]),
   ((.exchange 47 54 1),[(.neg 54),(.neg 47),(.pos 50),(.pos 53)]),
   ((.exchange 47 56 1),[(.neg 56),(.neg 47),(.pos 46),(.pos 67)]),
   ((.exchange 47 61 5),[(.neg 61),(.neg 47),(.pos 35),(.pos 41),(.pos 57)]),
   ((.exchange 47 62 2),[(.neg 62),(.neg 47),(.pos 52),(.pos 66)]),
   ((.exchange 47 63 1),[(.neg 63),(.neg 47),(.pos 53),(.pos 67)]),
   ((.exchange 47 65 1),[(.neg 65),(.neg 47),(.pos 46),(.pos 67)]),
   ((.exchange 47 65 2),[(.neg 65),(.neg 47),(.pos 45),(.pos 66)]),
   ((.exchange 47 68 1),[(.neg 68),(.neg 47),(.pos 50),(.pos 67)]),
   ((.exchange 47 69 2),[(.neg 69),(.neg 47),(.pos 52),(.pos 66)]),
   ((.exchange 48 5 3),[(.neg 48),(.neg 5),(.pos 45),(.pos 46)]),
   ((.exchange 48 9 3),[(.neg 48),(.neg 9),(.pos 45),(.pos 51)]),
   ((.exchange 48 10 3),[(.neg 48),(.neg 10),(.pos 46),(.pos 51)]),
   ((.exchange 48 14 0),[(.neg 48),(.neg 14),(.pos 50),(.pos 54)]),
   ((.exchange 48 15 5),[(.neg 48),(.neg 15),(.pos 36),(.pos 37),(.pos 58)]),
   ((.exchange 48 22 5),[(.neg 48),(.neg 22),(.pos 42),(.pos 58)]),
   ((.exchange 48 25 3),[(.neg 48),(.neg 25),(.pos 45),(.pos 65)]),
   ((.exchange 48 26 3),[(.neg 48),(.neg 26),(.pos 46),(.pos 65)]),
   ((.exchange 48 29 0),[(.neg 48),(.neg 29),(.pos 49),(.pos 68)]),
   ((.exchange 48 30 0),[(.neg 48),(.neg 30),(.pos 50),(.pos 68)]),
   ((.exchange 48 31 3),[(.neg 48),(.neg 31),(.pos 51),(.pos 65)]),
   ((.exchange 48 35 3),[(.neg 48),(.neg 35),(.pos 45),(.pos 46)]),
   ((.exchange 48 39 3),[(.neg 48),(.neg 39),(.pos 45),(.pos 51)]),
   ((.exchange 48 40 3),[(.neg 48),(.neg 40),(.pos 46),(.pos 51)]),
   ((.exchange 48 47 0),[(.neg 48),(.neg 47),(.pos 49),(.pos 50)]),
   ((.exchange 48 47 3),[(.neg 48),(.neg 47),(.pos 45),(.pos 46)]),
   ((.exchange 48 52 3),[(.neg 52),(.neg 48),(.pos 45),(.pos 51)]),
   ((.exchange 48 53 3),[(.neg 53),(.neg 48),(.pos 46),(.pos 51)]),
   ((.exchange 48 55 3),[(.neg 55),(.neg 48),(.pos 45),(.pos 65)]),
   ((.exchange 48 56 3),[(.neg 56),(.neg 48),(.pos 46),(.pos 65)]),
   ((.exchange 48 57 5),[(.neg 57),(.neg 48),(.pos 36),(.pos 37),(.pos 58)]),
   ((.exchange 48 61 3),[(.neg 61),(.neg 48),(.pos 51),(.pos 65)]),
   ((.exchange 48 66 3),[(.neg 66),(.neg 48),(.pos 45),(.pos 65)]),
   ((.exchange 48 69 0),[(.neg 69),(.neg 48),(.pos 54),(.pos 68)]),
   ((.exchange 48 69 3),[(.neg 69),(.neg 48),(.pos 51),(.pos 65)]),
   ((.exchange 49 5 3),[(.neg 49),(.neg 5),(.pos 45),(.pos 47)]),
   ((.exchange 49 7 1),[(.neg 49),(.neg 7),(.pos 48),(.pos 50)]),
   ((.exchange 49 9 3),[(.neg 49),(.neg 9),(.pos 45),(.pos 52)]),
   ((.exchange 49 14 1),[(.neg 49),(.neg 14),(.pos 50),(.pos 54)]),
   ((.exchange 49 15 5),[(.neg 49),(.neg 15),(.pos 36),(.pos 38),(.pos 59)]),
   ((.exchange 49 22 5),[(.neg 49),(.neg 22),(.pos 36),(.pos 43),(.pos 59)]),
   ((.exchange 49 25 3),[(.neg 49),(.neg 25),(.pos 45),(.pos 66)]),
   ((.exchange 49 27 3),[(.neg 49),(.neg 27),(.pos 47),(.pos 66)]),
   ((.exchange 49 28 1),[(.neg 49),(.neg 28),(.pos 48),(.pos 68)]),
   ((.exchange 49 32 3),[(.neg 49),(.neg 32),(.pos 52),(.pos 66)]),
   ((.exchange 49 35 3),[(.neg 49),(.neg 35),(.pos 45),(.pos 47)]),
   ((.exchange 49 37 1),[(.neg 49),(.neg 37),(.pos 48),(.pos 50)]),
   ((.exchange 49 41 3),[(.neg 49),(.neg 41),(.pos 47),(.pos 52)]),
   ((.exchange 49 42 1),[(.neg 49),(.neg 42),(.pos 48),(.pos 54)]),
   ((.exchange 49 44 1),[(.neg 49),(.neg 44),(.pos 50),(.pos 54)]),
   ((.exchange 49 51 3),[(.neg 51),(.neg 49),(.pos 45),(.pos 52)]),
   ((.exchange 49 53 1),[(.neg 53),(.neg 49),(.pos 50),(.pos 54)]),
   ((.exchange 49 55 3),[(.neg 55),(.neg 49),(.pos 45),(.pos 66)]),
   ((.exchange 49 57 3),[(.neg 57),(.neg 49),(.pos 47),(.pos 66)]),
   ((.exchange 49 60 1),[(.neg 60),(.neg 49),(.pos 50),(.pos 68)]),
   ((.exchange 49 61 5),[(.neg 61),(.neg 49),(.pos 36),(.pos 43),(.pos 59)]),
   ((.exchange 49 62 3),[(.neg 62),(.neg 49),(.pos 52),(.pos 66)]),
   ((.exchange 49 64 1),[(.neg 64),(.neg 49),(.pos 54),(.pos 68)]),
   ((.exchange 49 67 3),[(.neg 67),(.neg 49),(.pos 47),(.pos 66)]),
   ((.exchange 50 6 2),[(.neg 50),(.neg 6),(.pos 48),(.pos 49)]),
   ((.exchange 50 11 3),[(.neg 50),(.neg 11),(.pos 47),(.pos 53)]),
   ((.exchange 50 12 2),[(.neg 50),(.neg 12),(.pos 48),(.pos 54)]),
   ((.exchange 50 13 2),[(.neg 50),(.neg 13),(.pos 49),(.pos 54)]),
   ((.exchange 50 22 5),[(.neg 50),(.neg 22),(.pos 37),(.pos 44),(.pos 60)]),
   ((.exchange 50 26 3),[(.neg 50),(.neg 26),(.pos 46),(.pos 67)]),
   ((.exchange 50 27 3),[(.neg 50),(.neg 27),(.pos 47),(.pos 67)]),
   ((.exchange 50 28 2),[(.neg 50),(.neg 28),(.pos 48),(.pos 68)]),
   ((.exchange 50 29 2),[(.neg 50),(.neg 29),(.pos 49),(.pos 68)]),
   ((.exchange 50 33 3),[(.neg 50),(.neg 33),(.pos 53),(.pos 67)]),
   ((.exchange 50 34 2),[(.neg 50),(.neg 34),(.pos 54),(.pos 68)]),
   ((.exchange 50 35 3),[(.neg 50),(.neg 35),(.pos 46),(.pos 47)]),
   ((.exchange 50 36 2),[(.neg 50),(.neg 36),(.pos 48),(.pos 49)]),
   ((.exchange 50 40 3),[(.neg 50),(.neg 40),(.pos 46),(.pos 53)]),
   ((.exchange 50 41 3),[(.neg 50),(.neg 41),(.pos 47),(.pos 53)]),
   ((.exchange 50 45 3),[(.neg 50),(.neg 45),(.pos 46),(.pos 47)]),
   ((.exchange 50 51 3),[(.neg 51),(.neg 50),(.pos 46),(.pos 53)]),
   ((.exchange 50 52 3),[(.neg 52),(.neg 50),(.pos 47),(.pos 53)]),
   ((.exchange 50 56 5),[(.neg 56),(.neg 50),(.pos 37),(.pos 60)]),
   ((.exchange 50 58 2),[(.neg 58),(.neg 50),(.pos 48),(.pos 68)]),
   ((.exchange 50 58 5),[(.neg 58),(.neg 50),(.pos 37),(.pos 60)]),
   ((.exchange 50 65 2),[(.neg 65),(.neg 50),(.pos 48),(.pos 68)]),
   ((.exchange 50 69 2),[(.neg 69),(.neg 50),(.pos 54),(.pos 68)]),
   ((.exchange 50 69 3),[(.neg 69),(.neg 50),(.pos 53),(.pos 67)]),
   ((.exchange 51 6 4),[(.neg 51),(.neg 6),(.pos 45),(.pos 48)]),
   ((.exchange 51 7 4),[(.neg 51),(.neg 7),(.pos 46),(.pos 48)]),
   ((.exchange 51 11 0),[(.neg 51),(.neg 11),(.pos 52),(.pos 53)]),
   ((.exchange 51 13 0),[(.neg 51),(.neg 13),(.pos 52),(.pos 54)]),
   ((.exchange 51 14 0),[(.neg 51),(.neg 14),(.pos 53),(.pos 54)]),
   ((.exchange 51 22 5),[(.neg 51),(.neg 22),(.pos 42),(.pos 61)]),
   ((.exchange 51 26 4),[(.neg 51),(.neg 26),(.pos 46),(.pos 65)]),
   ((.exchange 51 28 4),[(.neg 51),(.neg 28),(.pos 48),(.pos 65)]),
   ((.exchange 51 29 4),[(.neg 51),(.neg 29),(.pos 45),(.pos 48),(.pos 65)]),
   ((.exchange 51 32 0),[(.neg 51),(.neg 32),(.pos 52),(.pos 69)]),
   ((.exchange 51 33 0),[(.neg 51),(.neg 33),(.pos 53),(.pos 69)]),
   ((.exchange 51 34 0),[(.neg 51),(.neg 34),(.pos 54),(.pos 69)]),
   ((.exchange 51 35 4),[(.neg 51),(.neg 35),(.pos 45),(.pos 46)]),
   ((.exchange 51 41 0),[(.neg 51),(.neg 41),(.pos 52),(.pos 53)]),
   ((.exchange 51 44 0),[(.neg 51),(.neg 44),(.pos 53),(.pos 54)]),
   ((.exchange 51 49 0),[(.neg 51),(.neg 49),(.pos 52),(.pos 54)]),
   ((.exchange 51 50 0),[(.neg 51),(.neg 50),(.pos 53),(.pos 54)]),
   ((.exchange 51 50 4),[(.neg 51),(.neg 50),(.pos 46),(.pos 48)]),
   ((.exchange 51 55 4),[(.neg 55),(.neg 51),(.pos 45),(.pos 65)]),
   ((.exchange 51 56 4),[(.neg 56),(.neg 51),(.pos 46),(.pos 65)]),
   ((.exchange 51 58 4),[(.neg 58),(.neg 51),(.pos 48),(.pos 65)]),
   ((.exchange 51 60 5),[(.neg 60),(.neg 51),(.pos 40),(.pos 42),(.pos 61)]),
   ((.exchange 51 62 0),[(.neg 62),(.neg 51),(.pos 52),(.pos 69)]),
   ((.exchange 51 62 5),[(.neg 62),(.neg 51),(.pos 39),(.pos 61)]),
   ((.exchange 51 66 4),[(.neg 66),(.neg 51),(.pos 45),(.pos 65)]),
   ((.exchange 51 67 4),[(.neg 67),(.neg 51),(.pos 46),(.pos 65)]),
   ((.exchange 52 8 4),[(.neg 52),(.neg 8),(.pos 47),(.pos 49)]),
   ((.exchange 52 10 1),[(.neg 52),(.neg 10),(.pos 51),(.pos 53)])]

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



noncomputable def certificates_2 : List (Origin 70 1111 × List Sat.Literal) :=
  [((.exchange 52 14 1),[(.neg 52),(.neg 14),(.pos 53),(.pos 54)]),
   ((.exchange 52 24 1),[(.neg 52),(.neg 24),(.pos 53),(.pos 54),(.pos 69)]),
   ((.exchange 52 24 5),[(.neg 52),(.neg 24),(.pos 41),(.pos 43),(.pos 62)]),
   ((.exchange 52 27 4),[(.neg 52),(.neg 27),(.pos 47),(.pos 66)]),
   ((.exchange 52 29 4),[(.neg 52),(.neg 29),(.pos 49),(.pos 66)]),
   ((.exchange 52 31 1),[(.neg 52),(.neg 31),(.pos 51),(.pos 69)]),
   ((.exchange 52 33 1),[(.neg 52),(.neg 33),(.pos 53),(.pos 69)]),
   ((.exchange 52 34 1),[(.neg 52),(.neg 34),(.pos 54),(.pos 69)]),
   ((.exchange 52 46 1),[(.neg 52),(.neg 46),(.pos 51),(.pos 53)]),
   ((.exchange 52 48 1),[(.neg 52),(.neg 48),(.pos 51),(.pos 54)]),
   ((.exchange 52 48 4),[(.neg 52),(.neg 48),(.pos 45),(.pos 49)]),
   ((.exchange 52 50 4),[(.neg 52),(.neg 50),(.pos 47),(.pos 49)]),
   ((.exchange 52 56 5),[(.neg 56),(.neg 52),(.pos 39),(.pos 41),(.pos 62)]),
   ((.exchange 52 59 4),[(.neg 59),(.neg 52),(.pos 49),(.pos 66)]),
   ((.exchange 52 63 1),[(.neg 63),(.neg 52),(.pos 53),(.pos 69)]),
   ((.exchange 52 67 1),[(.neg 67),(.neg 52),(.pos 53),(.pos 69)]),
   ((.exchange 52 68 1),[(.neg 68),(.neg 52),(.pos 54),(.pos 69)]),
   ((.exchange 53 5 4),[(.neg 53),(.neg 5),(.pos 46),(.pos 47)]),
   ((.exchange 53 7 4),[(.neg 53),(.neg 7),(.pos 46),(.pos 50)]),
   ((.exchange 53 8 4),[(.neg 53),(.neg 8),(.pos 47),(.pos 50)]),
   ((.exchange 53 9 2),[(.neg 53),(.neg 9),(.pos 51),(.pos 52)]),
   ((.exchange 53 12 2),[(.neg 53),(.neg 12),(.pos 51),(.pos 54)]),
   ((.exchange 53 23 5),[(.neg 53),(.neg 23),(.pos 41),(.pos 44),(.pos 63)]),
   ((.exchange 53 26 4),[(.neg 53),(.neg 26),(.pos 46),(.pos 67)]),
   ((.exchange 53 38 4),[(.neg 53),(.neg 38),(.pos 47),(.pos 50)]),
   ((.exchange 53 39 2),[(.neg 53),(.neg 39),(.pos 51),(.pos 52)]),
   ((.exchange 53 42 2),[(.neg 53),(.neg 42),(.pos 51),(.pos 54)]),
   ((.exchange 53 48 2),[(.neg 53),(.neg 48),(.pos 51),(.pos 54)]),
   ((.exchange 53 48 4),[(.neg 53),(.neg 48),(.pos 46),(.pos 50)]),
   ((.exchange 53 55 2),[(.neg 55),(.neg 53),(.pos 51),(.pos 52),(.pos 69)]),
   ((.exchange 53 60 4),[(.neg 60),(.neg 53),(.pos 50),(.pos 67)]),
   ((.exchange 53 61 2),[(.neg 61),(.neg 53),(.pos 51),(.pos 69)]),
   ((.exchange 53 62 2),[(.neg 62),(.neg 53),(.pos 52),(.pos 69)]),
   ((.exchange 53 62 5),[(.neg 62),(.neg 53),(.pos 41),(.pos 63)]),
   ((.exchange 53 68 2),[(.neg 68),(.neg 53),(.pos 54),(.pos 69)]),
   ((.exchange 53 68 4),[(.neg 68),(.neg 53),(.pos 50),(.pos 67)]),
   ((.exchange 54 8 4),[(.neg 54),(.neg 8),(.pos 49),(.pos 50)]),
   ((.exchange 54 9 3),[(.neg 54),(.neg 9),(.pos 51),(.pos 52)]),
   ((.exchange 54 10 3),[(.neg 54),(.neg 10),(.pos 51),(.pos 53)]),
   ((.exchange 54 11 3),[(.neg 54),(.neg 11),(.pos 52),(.pos 53)]),
   ((.exchange 54 15 5),[(.neg 54),(.neg 15),(.pos 42),(.pos 43),(.pos 44),(.pos 64)]),
   ((.exchange 54 22 5),[(.neg 54),(.neg 22),(.pos 42),(.pos 64)]),
   ((.exchange 54 28 4),[(.neg 54),(.neg 28),(.pos 48),(.pos 68)]),
   ((.exchange 54 29 4),[(.neg 54),(.neg 29),(.pos 49),(.pos 68)]),
   ((.exchange 54 30 4),[(.neg 54),(.neg 30),(.pos 50),(.pos 68)]),
   ((.exchange 54 31 3),[(.neg 54),(.neg 31),(.pos 51),(.pos 69)]),
   ((.exchange 54 32 3),[(.neg 54),(.neg 32),(.pos 52),(.pos 69)]),
   ((.exchange 54 33 3),[(.neg 54),(.neg 33),(.pos 53),(.pos 69)]),
   ((.exchange 54 36 4),[(.neg 54),(.neg 36),(.pos 48),(.pos 49)]),
   ((.exchange 54 37 4),[(.neg 54),(.neg 37),(.pos 48),(.pos 50)]),
   ((.exchange 54 38 4),[(.neg 54),(.neg 38),(.pos 49),(.pos 50)]),
   ((.exchange 54 39 3),[(.neg 54),(.neg 39),(.pos 51),(.pos 52)]),
   ((.exchange 54 40 3),[(.neg 54),(.neg 40),(.pos 51),(.pos 53)]),
   ((.exchange 54 41 3),[(.neg 54),(.neg 41),(.pos 52),(.pos 53)]),
   ((.exchange 54 45 3),[(.neg 54),(.neg 45),(.pos 51),(.pos 52)]),
   ((.exchange 54 45 4),[(.neg 54),(.neg 45),(.pos 48),(.pos 49)]),
   ((.exchange 54 61 3),[(.neg 61),(.neg 54),(.pos 51),(.pos 69)]),
   ((.exchange 54 62 3),[(.neg 62),(.neg 54),(.pos 52),(.pos 69)]),
   ((.exchange 54 63 3),[(.neg 63),(.neg 54),(.pos 53),(.pos 69)]),
   ((.exchange 54 65 3),[(.neg 65),(.neg 54),(.pos 51),(.pos 69)]),
   ((.exchange 54 65 4),[(.neg 65),(.neg 54),(.pos 48),(.pos 68)]),
   ((.exchange 54 67 3),[(.neg 67),(.neg 54),(.pos 53),(.pos 69)]),
   ((.exchange 55 5 6),[(.neg 55),(.neg 5),(.pos 35),(.pos 45)]),
   ((.exchange 55 17 1),[(.neg 55),(.neg 17),(.pos 56),(.pos 58)]),
   ((.exchange 55 20 1),[(.neg 55),(.neg 20),(.pos 56),(.pos 61)]),
   ((.exchange 55 22 1),[(.neg 55),(.neg 22),(.pos 58),(.pos 61)]),
   ((.exchange 55 23 0),[(.neg 55),(.neg 23),(.pos 59),(.pos 62)]),
   ((.exchange 55 26 1),[(.neg 55),(.neg 26),(.pos 56),(.pos 65)]),
   ((.exchange 55 28 1),[(.neg 55),(.neg 28),(.pos 58),(.pos 65)]),
   ((.exchange 55 29 0),[(.neg 55),(.neg 29),(.pos 59),(.pos 66)]),
   ((.exchange 55 31 1),[(.neg 55),(.neg 31),(.pos 61),(.pos 65)]),
   ((.exchange 55 32 0),[(.neg 55),(.neg 32),(.pos 62),(.pos 66)]),
   ((.exchange 55 37 1),[(.neg 55),(.neg 37),(.pos 56),(.pos 58)]),
   ((.exchange 55 46 1),[(.neg 55),(.neg 46),(.pos 56),(.pos 65)]),
   ((.exchange 55 46 6),[(.neg 55),(.neg 46),(.pos 35),(.pos 45)]),
   ((.exchange 55 51 1),[(.neg 55),(.neg 51),(.pos 61),(.pos 65)]),
   ((.exchange 55 63 1),[(.neg 63),(.neg 55),(.pos 56),(.pos 61)]),
   ((.exchange 55 67 1),[(.neg 67),(.neg 55),(.pos 56),(.pos 65)]),
   ((.exchange 55 68 0),[(.neg 68),(.neg 55),(.pos 59),(.pos 66)]),
   ((.exchange 56 10 6),[(.neg 56),(.neg 10),(.pos 40),(.pos 46)]),
   ((.exchange 56 16 2),[(.neg 56),(.neg 16),(.pos 55),(.pos 58)]),
   ((.exchange 56 18 0),[(.neg 56),(.neg 18),(.pos 57),(.pos 60)]),
   ((.exchange 56 19 2),[(.neg 56),(.neg 19),(.pos 55),(.pos 61)]),
   ((.exchange 56 21 0),[(.neg 56),(.neg 21),(.pos 57),(.pos 63)]),
   ((.exchange 56 22 2),[(.neg 56),(.neg 22),(.pos 58),(.pos 61)]),
   ((.exchange 56 24 0),[(.neg 56),(.neg 24),(.pos 60),(.pos 63)]),
   ((.exchange 56 25 2),[(.neg 56),(.neg 25),(.pos 55),(.pos 65)]),
   ((.exchange 56 27 0),[(.neg 56),(.neg 27),(.pos 57),(.pos 67)]),
   ((.exchange 56 28 2),[(.neg 56),(.neg 28),(.pos 58),(.pos 65)]),
   ((.exchange 56 30 0),[(.neg 56),(.neg 30),(.pos 60),(.pos 67)]),
   ((.exchange 56 31 2),[(.neg 56),(.neg 31),(.pos 61),(.pos 65)]),
   ((.exchange 56 33 0),[(.neg 56),(.neg 33),(.pos 63),(.pos 67)]),
   ((.exchange 56 38 0),[(.neg 56),(.neg 38),(.pos 57),(.pos 60)]),
   ((.exchange 56 42 2),[(.neg 56),(.neg 42),(.pos 58),(.pos 61)]),
   ((.exchange 56 47 0),[(.neg 56),(.neg 47),(.pos 57),(.pos 67)]),
   ((.exchange 56 53 0),[(.neg 56),(.neg 53),(.pos 63),(.pos 67)]),
   ((.exchange 56 59 2),[(.neg 59),(.neg 56),(.pos 55),(.pos 58)]),
   ((.exchange 56 62 0),[(.neg 62),(.neg 56),(.pos 57),(.pos 63)]),
   ((.exchange 56 64 0),[(.neg 64),(.neg 56),(.pos 60),(.pos 63)]),
   ((.exchange 56 66 2),[(.neg 66),(.neg 56),(.pos 55),(.pos 65)]),
   ((.exchange 56 68 2),[(.neg 68),(.neg 56),(.pos 58),(.pos 65)]),
   ((.exchange 57 13 2),[(.neg 57),(.neg 13),(.pos 59),(.pos 62),(.pos 66)]),
   ((.exchange 57 16 2),[(.neg 57),(.neg 16),(.pos 55),(.pos 59)]),
   ((.exchange 57 19 2),[(.neg 57),(.neg 19),(.pos 55),(.pos 62)]),
   ((.exchange 57 20 1),[(.neg 57),(.neg 20),(.pos 56),(.pos 63)]),
   ((.exchange 57 23 2),[(.neg 57),(.neg 23),(.pos 59),(.pos 62)]),
   ((.exchange 57 24 1),[(.neg 57),(.neg 24),(.pos 60),(.pos 63)]),
   ((.exchange 57 25 2),[(.neg 57),(.neg 25),(.pos 55),(.pos 66)]),
   ((.exchange 57 26 1),[(.neg 57),(.neg 26),(.pos 56),(.pos 67)]),
   ((.exchange 57 29 2),[(.neg 57),(.neg 29),(.pos 59),(.pos 66)]),
   ((.exchange 57 30 1),[(.neg 57),(.neg 30),(.pos 60),(.pos 67)]),
   ((.exchange 57 31 1),[(.neg 57),(.neg 31),(.pos 56),(.pos 63),(.pos 67)]),
   ((.exchange 57 32 2),[(.neg 57),(.neg 32),(.pos 62),(.pos 66)]),
   ((.exchange 57 33 1),[(.neg 57),(.neg 33),(.pos 63),(.pos 67)]),
   ((.exchange 57 37 1),[(.neg 57),(.neg 37),(.pos 56),(.pos 60)]),
   ((.exchange 57 39 2),[(.neg 57),(.neg 39),(.pos 55),(.pos 62)]),
   ((.exchange 57 40 1),[(.neg 57),(.neg 40),(.pos 56),(.pos 63)]),
   ((.exchange 57 43 2),[(.neg 57),(.neg 43),(.pos 59),(.pos 62)]),
   ((.exchange 57 50 1),[(.neg 57),(.neg 50),(.pos 60),(.pos 67)]),
   ((.exchange 57 50 6),[(.neg 57),(.neg 50),(.pos 38),(.pos 47)]),
   ((.exchange 57 51 6),[(.neg 57),(.neg 51),(.pos 35),(.pos 41),(.pos 47)]),
   ((.exchange 57 53 1),[(.neg 57),(.neg 53),(.pos 63),(.pos 67)]),
   ((.exchange 57 58 1),[(.neg 58),(.neg 57),(.pos 56),(.pos 60)]),
   ((.exchange 57 58 2),[(.neg 58),(.neg 57),(.pos 55),(.pos 59)]),
   ((.exchange 57 61 1),[(.neg 61),(.neg 57),(.pos 56),(.pos 63)]),
   ((.exchange 57 64 1),[(.neg 64),(.neg 57),(.pos 60),(.pos 63)]),
   ((.exchange 57 64 2),[(.neg 64),(.neg 57),(.pos 59),(.pos 62)]),
   ((.exchange 57 65 2),[(.neg 65),(.neg 57),(.pos 55),(.pos 66)])]

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



noncomputable def certificates_3 : List (Origin 70 1111 × List Sat.Literal) :=
  [((.exchange 57 68 2),[(.neg 68),(.neg 57),(.pos 59),(.pos 66)]),
   ((.exchange 58 12 6),[(.neg 58),(.neg 12),(.pos 42),(.pos 48)]),
   ((.exchange 58 15 3),[(.neg 58),(.neg 15),(.pos 55),(.pos 56)]),
   ((.exchange 58 18 0),[(.neg 58),(.neg 18),(.pos 59),(.pos 60)]),
   ((.exchange 58 19 3),[(.neg 58),(.neg 19),(.pos 55),(.pos 61)]),
   ((.exchange 58 20 3),[(.neg 58),(.neg 20),(.pos 56),(.pos 61)]),
   ((.exchange 58 23 0),[(.neg 58),(.neg 23),(.pos 59),(.pos 64)]),
   ((.exchange 58 24 0),[(.neg 58),(.neg 24),(.pos 60),(.pos 64)]),
   ((.exchange 58 26 3),[(.neg 58),(.neg 26),(.pos 56),(.pos 65)]),
   ((.exchange 58 29 0),[(.neg 58),(.neg 29),(.pos 59),(.pos 68)]),
   ((.exchange 58 30 0),[(.neg 58),(.neg 30),(.pos 60),(.pos 68)]),
   ((.exchange 58 31 3),[(.neg 58),(.neg 31),(.pos 61),(.pos 65)]),
   ((.exchange 58 34 0),[(.neg 58),(.neg 34),(.pos 64),(.pos 68)]),
   ((.exchange 58 35 3),[(.neg 58),(.neg 35),(.pos 55),(.pos 56)]),
   ((.exchange 58 39 3),[(.neg 58),(.neg 39),(.pos 55),(.pos 61)]),
   ((.exchange 58 40 3),[(.neg 58),(.neg 40),(.pos 56),(.pos 61)]),
   ((.exchange 58 43 0),[(.neg 58),(.neg 43),(.pos 59),(.pos 64)]),
   ((.exchange 58 44 0),[(.neg 58),(.neg 44),(.pos 60),(.pos 64)]),
   ((.exchange 58 45 3),[(.neg 58),(.neg 45),(.pos 55),(.pos 65)]),
   ((.exchange 58 46 3),[(.neg 58),(.neg 46),(.pos 56),(.pos 65)]),
   ((.exchange 58 46 6),[(.neg 58),(.neg 46),(.pos 37),(.pos 48)]),
   ((.exchange 58 50 0),[(.neg 58),(.neg 50),(.pos 60),(.pos 68)]),
   ((.exchange 58 50 6),[(.neg 58),(.neg 50),(.pos 37),(.pos 48)]),
   ((.exchange 58 51 3),[(.neg 58),(.neg 51),(.pos 61),(.pos 65)]),
   ((.exchange 58 51 6),[(.neg 58),(.neg 51),(.pos 42),(.pos 48)]),
   ((.exchange 58 57 3),[(.neg 58),(.neg 57),(.pos 55),(.pos 56)]),
   ((.exchange 58 62 0),[(.neg 62),(.neg 58),(.pos 59),(.pos 64)]),
   ((.exchange 58 62 3),[(.neg 62),(.neg 58),(.pos 55),(.pos 61)]),
   ((.exchange 58 63 0),[(.neg 63),(.neg 58),(.pos 60),(.pos 64)]),
   ((.exchange 58 63 3),[(.neg 63),(.neg 58),(.pos 56),(.pos 61)]),
   ((.exchange 58 69 0),[(.neg 69),(.neg 58),(.pos 64),(.pos 68)]),
   ((.exchange 59 5 6),[(.neg 59),(.neg 5),(.pos 36),(.pos 38),(.pos 49)]),
   ((.exchange 59 12 1),[(.neg 59),(.neg 12),(.pos 58),(.pos 64),(.pos 68)]),
   ((.exchange 59 12 6),[(.neg 59),(.neg 12),(.pos 36),(.pos 43),(.pos 49)]),
   ((.exchange 59 15 3),[(.neg 59),(.neg 15),(.pos 55),(.pos 57)]),
   ((.exchange 59 17 1),[(.neg 59),(.neg 17),(.pos 58),(.pos 60)]),
   ((.exchange 59 19 3),[(.neg 59),(.neg 19),(.pos 55),(.pos 62)]),
   ((.exchange 59 22 1),[(.neg 59),(.neg 22),(.pos 58),(.pos 64)]),
   ((.exchange 59 24 1),[(.neg 59),(.neg 24),(.pos 60),(.pos 64)]),
   ((.exchange 59 25 3),[(.neg 59),(.neg 25),(.pos 55),(.pos 66)]),
   ((.exchange 59 27 3),[(.neg 59),(.neg 27),(.pos 57),(.pos 66)]),
   ((.exchange 59 28 1),[(.neg 59),(.neg 28),(.pos 58),(.pos 68)]),
   ((.exchange 59 30 1),[(.neg 59),(.neg 30),(.pos 60),(.pos 68)]),
   ((.exchange 59 32 3),[(.neg 59),(.neg 32),(.pos 62),(.pos 66)]),
   ((.exchange 59 34 1),[(.neg 59),(.neg 34),(.pos 64),(.pos 68)]),
   ((.exchange 59 35 3),[(.neg 59),(.neg 35),(.pos 55),(.pos 57)]),
   ((.exchange 59 37 1),[(.neg 59),(.neg 37),(.pos 58),(.pos 60)]),
   ((.exchange 59 42 1),[(.neg 59),(.neg 42),(.pos 58),(.pos 64)]),
   ((.exchange 59 46 6),[(.neg 59),(.neg 46),(.pos 36),(.pos 38),(.pos 49)]),
   ((.exchange 59 47 3),[(.neg 59),(.neg 47),(.pos 57),(.pos 66)]),
   ((.exchange 59 48 1),[(.neg 59),(.neg 48),(.pos 58),(.pos 68)]),
   ((.exchange 59 52 3),[(.neg 59),(.neg 52),(.pos 62),(.pos 66)]),
   ((.exchange 59 54 1),[(.neg 59),(.neg 54),(.pos 64),(.pos 68)]),
   ((.exchange 59 56 1),[(.neg 59),(.neg 56),(.pos 58),(.pos 60)]),
   ((.exchange 59 61 1),[(.neg 61),(.neg 59),(.pos 58),(.pos 64)]),
   ((.exchange 59 61 3),[(.neg 61),(.neg 59),(.pos 55),(.pos 62)]),
   ((.exchange 59 63 3),[(.neg 63),(.neg 59),(.pos 57),(.pos 62)]),
   ((.exchange 59 65 3),[(.neg 65),(.neg 59),(.pos 55),(.pos 66)]),
   ((.exchange 59 67 3),[(.neg 67),(.neg 59),(.pos 57),(.pos 66)]),
   ((.exchange 59 69 3),[(.neg 69),(.neg 59),(.pos 62),(.pos 66)]),
   ((.exchange 60 12 2),[(.neg 60),(.neg 12),(.pos 58),(.pos 64),(.pos 68)]),
   ((.exchange 60 12 6),[(.neg 60),(.neg 12),(.pos 37),(.pos 44),(.pos 50)]),
   ((.exchange 60 15 3),[(.neg 60),(.neg 15),(.pos 56),(.pos 57)]),
   ((.exchange 60 20 3),[(.neg 60),(.neg 20),(.pos 56),(.pos 63)]),
   ((.exchange 60 21 3),[(.neg 60),(.neg 21),(.pos 57),(.pos 63)]),
   ((.exchange 60 23 2),[(.neg 60),(.neg 23),(.pos 59),(.pos 64)]),
   ((.exchange 60 26 3),[(.neg 60),(.neg 26),(.pos 56),(.pos 67)]),
   ((.exchange 60 28 2),[(.neg 60),(.neg 28),(.pos 58),(.pos 68)]),
   ((.exchange 60 29 2),[(.neg 60),(.neg 29),(.pos 59),(.pos 68)]),
   ((.exchange 60 31 3),[(.neg 60),(.neg 31),(.pos 56),(.pos 63),(.pos 67)]),
   ((.exchange 60 33 3),[(.neg 60),(.neg 33),(.pos 63),(.pos 67)]),
   ((.exchange 60 35 3),[(.neg 60),(.neg 35),(.pos 56),(.pos 57)]),
   ((.exchange 60 36 2),[(.neg 60),(.neg 36),(.pos 58),(.pos 59)]),
   ((.exchange 60 40 3),[(.neg 60),(.neg 40),(.pos 56),(.pos 63)]),
   ((.exchange 60 41 3),[(.neg 60),(.neg 41),(.pos 57),(.pos 63)]),
   ((.exchange 60 42 2),[(.neg 60),(.neg 42),(.pos 58),(.pos 64)]),
   ((.exchange 60 43 2),[(.neg 60),(.neg 43),(.pos 59),(.pos 64)]),
   ((.exchange 60 46 3),[(.neg 60),(.neg 46),(.pos 56),(.pos 67)]),
   ((.exchange 60 46 6),[(.neg 60),(.neg 46),(.pos 37),(.pos 50)]),
   ((.exchange 60 48 2),[(.neg 60),(.neg 48),(.pos 58),(.pos 68)]),
   ((.exchange 60 52 6),[(.neg 60),(.neg 52),(.pos 38),(.pos 44),(.pos 50)]),
   ((.exchange 60 54 2),[(.neg 60),(.neg 54),(.pos 64),(.pos 68)]),
   ((.exchange 60 61 3),[(.neg 61),(.neg 60),(.pos 56),(.pos 63)]),
   ((.exchange 60 62 2),[(.neg 62),(.neg 60),(.pos 59),(.pos 64)]),
   ((.exchange 60 62 3),[(.neg 62),(.neg 60),(.pos 57),(.pos 63)]),
   ((.exchange 60 69 2),[(.neg 69),(.neg 60),(.pos 64),(.pos 68)]),
   ((.exchange 60 69 3),[(.neg 69),(.neg 60),(.pos 63),(.pos 67)]),
   ((.exchange 61 15 4),[(.neg 61),(.neg 15),(.pos 55),(.pos 56)]),
   ((.exchange 61 16 4),[(.neg 61),(.neg 16),(.pos 55),(.pos 58)]),
   ((.exchange 61 17 4),[(.neg 61),(.neg 17),(.pos 56),(.pos 58)]),
   ((.exchange 61 21 0),[(.neg 61),(.neg 21),(.pos 62),(.pos 63)]),
   ((.exchange 61 23 0),[(.neg 61),(.neg 23),(.pos 62),(.pos 64)]),
   ((.exchange 61 24 0),[(.neg 61),(.neg 24),(.pos 63),(.pos 64)]),
   ((.exchange 61 27 4),[(.neg 61),(.neg 27),(.pos 55),(.pos 56),(.pos 65)]),
   ((.exchange 61 28 4),[(.neg 61),(.neg 28),(.pos 58),(.pos 65)]),
   ((.exchange 61 32 0),[(.neg 61),(.neg 32),(.pos 62),(.pos 69)]),
   ((.exchange 61 33 0),[(.neg 61),(.neg 33),(.pos 63),(.pos 69)]),
   ((.exchange 61 34 0),[(.neg 61),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 61 37 4),[(.neg 61),(.neg 37),(.pos 56),(.pos 58)]),
   ((.exchange 61 43 0),[(.neg 61),(.neg 43),(.pos 62),(.pos 64)]),
   ((.exchange 61 44 0),[(.neg 61),(.neg 44),(.pos 63),(.pos 64)]),
   ((.exchange 61 45 4),[(.neg 61),(.neg 45),(.pos 55),(.pos 65)]),
   ((.exchange 61 48 4),[(.neg 61),(.neg 48),(.pos 58),(.pos 65)]),
   ((.exchange 61 49 6),[(.neg 61),(.neg 49),(.pos 39),(.pos 42),(.pos 51)]),
   ((.exchange 61 52 0),[(.neg 61),(.neg 52),(.pos 62),(.pos 69)]),
   ((.exchange 61 53 6),[(.neg 61),(.neg 53),(.pos 40),(.pos 51)]),
   ((.exchange 61 54 0),[(.neg 61),(.neg 54),(.pos 64),(.pos 69)]),
   ((.exchange 61 57 0),[(.neg 61),(.neg 57),(.pos 62),(.pos 63)]),
   ((.exchange 61 57 4),[(.neg 61),(.neg 57),(.pos 55),(.pos 56)]),
   ((.exchange 61 59 4),[(.neg 61),(.neg 59),(.pos 55),(.pos 58)]),
   ((.exchange 61 60 0),[(.neg 61),(.neg 60),(.pos 63),(.pos 64)]),
   ((.exchange 61 66 0),[(.neg 66),(.neg 61),(.pos 62),(.pos 69)]),
   ((.exchange 61 66 4),[(.neg 66),(.neg 61),(.pos 55),(.pos 65)]),
   ((.exchange 61 67 0),[(.neg 67),(.neg 61),(.pos 63),(.pos 69)]),
   ((.exchange 61 67 4),[(.neg 67),(.neg 61),(.pos 56),(.pos 65)]),
   ((.exchange 62 16 4),[(.neg 62),(.neg 16),(.pos 55),(.pos 59)]),
   ((.exchange 62 18 4),[(.neg 62),(.neg 18),(.pos 57),(.pos 59)]),
   ((.exchange 62 22 1),[(.neg 62),(.neg 22),(.pos 61),(.pos 64)]),
   ((.exchange 62 24 1),[(.neg 62),(.neg 24),(.pos 63),(.pos 64)]),
   ((.exchange 62 25 4),[(.neg 62),(.neg 25),(.pos 55),(.pos 66)]),
   ((.exchange 62 33 1),[(.neg 62),(.neg 33),(.pos 63),(.pos 69)]),
   ((.exchange 62 34 1),[(.neg 62),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 62 35 4),[(.neg 62),(.neg 35),(.pos 55),(.pos 57)]),
   ((.exchange 62 36 4),[(.neg 62),(.neg 36),(.pos 55),(.pos 59)]),
   ((.exchange 62 40 1),[(.neg 62),(.neg 40),(.pos 61),(.pos 63)]),
   ((.exchange 62 42 1),[(.neg 62),(.neg 42),(.pos 61),(.pos 64)]),
   ((.exchange 62 44 1),[(.neg 62),(.neg 44),(.pos 63),(.pos 64)]),
   ((.exchange 62 46 6),[(.neg 62),(.neg 46),(.pos 39),(.pos 41),(.pos 52)])]

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



noncomputable def certificates_4 : List (Origin 70 1111 × List Sat.Literal) :=
  [((.exchange 62 49 4),[(.neg 62),(.neg 49),(.pos 59),(.pos 66)]),
   ((.exchange 62 51 1),[(.neg 62),(.neg 51),(.pos 61),(.pos 69)]),
   ((.exchange 62 54 1),[(.neg 62),(.neg 54),(.pos 64),(.pos 69)]),
   ((.exchange 62 54 6),[(.neg 62),(.neg 54),(.pos 43),(.pos 52)]),
   ((.exchange 62 56 1),[(.neg 62),(.neg 56),(.pos 61),(.pos 63)]),
   ((.exchange 62 58 1),[(.neg 62),(.neg 58),(.pos 61),(.pos 64)]),
   ((.exchange 62 58 4),[(.neg 62),(.neg 58),(.pos 55),(.pos 59)]),
   ((.exchange 62 60 1),[(.neg 62),(.neg 60),(.pos 63),(.pos 64)]),
   ((.exchange 62 65 1),[(.neg 65),(.neg 62),(.pos 61),(.pos 69)]),
   ((.exchange 62 65 4),[(.neg 65),(.neg 62),(.pos 55),(.pos 66)]),
   ((.exchange 63 5 6),[(.neg 63),(.neg 5),(.pos 40),(.pos 41),(.pos 53)]),
   ((.exchange 63 8 4),[(.neg 63),(.neg 8),(.pos 57),(.pos 60),(.pos 67)]),
   ((.exchange 63 9 2),[(.neg 63),(.neg 9),(.pos 61),(.pos 62),(.pos 69)]),
   ((.exchange 63 13 2),[(.neg 63),(.neg 13),(.pos 62),(.pos 64),(.pos 69)]),
   ((.exchange 63 13 6),[(.neg 63),(.neg 13),(.pos 41),(.pos 44),(.pos 53)]),
   ((.exchange 63 15 4),[(.neg 63),(.neg 15),(.pos 56),(.pos 57)]),
   ((.exchange 63 17 4),[(.neg 63),(.neg 17),(.pos 56),(.pos 60)]),
   ((.exchange 63 18 4),[(.neg 63),(.neg 18),(.pos 57),(.pos 60)]),
   ((.exchange 63 19 2),[(.neg 63),(.neg 19),(.pos 61),(.pos 62)]),
   ((.exchange 63 22 2),[(.neg 63),(.neg 22),(.pos 61),(.pos 64)]),
   ((.exchange 63 23 2),[(.neg 63),(.neg 23),(.pos 62),(.pos 64)]),
   ((.exchange 63 26 4),[(.neg 63),(.neg 26),(.pos 56),(.pos 67)]),
   ((.exchange 63 31 2),[(.neg 63),(.neg 31),(.pos 61),(.pos 69)]),
   ((.exchange 63 32 2),[(.neg 63),(.neg 32),(.pos 62),(.pos 69)]),
   ((.exchange 63 34 2),[(.neg 63),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 63 35 4),[(.neg 63),(.neg 35),(.pos 56),(.pos 57)]),
   ((.exchange 63 37 4),[(.neg 63),(.neg 37),(.pos 56),(.pos 60)]),
   ((.exchange 63 42 2),[(.neg 63),(.neg 42),(.pos 61),(.pos 64)]),
   ((.exchange 63 43 2),[(.neg 63),(.neg 43),(.pos 62),(.pos 64)]),
   ((.exchange 63 49 6),[(.neg 63),(.neg 49),(.pos 41),(.pos 44),(.pos 53)]),
   ((.exchange 63 50 4),[(.neg 63),(.neg 50),(.pos 60),(.pos 67)]),
   ((.exchange 63 54 2),[(.neg 63),(.neg 54),(.pos 64),(.pos 69)]),
   ((.exchange 63 54 6),[(.neg 63),(.neg 54),(.pos 44),(.pos 53)]),
   ((.exchange 63 55 2),[(.neg 63),(.neg 55),(.pos 61),(.pos 62)]),
   ((.exchange 63 55 4),[(.neg 63),(.neg 55),(.pos 56),(.pos 57)]),
   ((.exchange 63 58 2),[(.neg 63),(.neg 58),(.pos 61),(.pos 64)]),
   ((.exchange 63 58 4),[(.neg 63),(.neg 58),(.pos 56),(.pos 60)]),
   ((.exchange 63 59 4),[(.neg 63),(.neg 59),(.pos 57),(.pos 60)]),
   ((.exchange 63 65 2),[(.neg 65),(.neg 63),(.pos 61),(.pos 69)]),
   ((.exchange 63 66 2),[(.neg 66),(.neg 63),(.pos 62),(.pos 69)]),
   ((.exchange 63 68 2),[(.neg 68),(.neg 63),(.pos 64),(.pos 69)]),
   ((.exchange 63 68 4),[(.neg 68),(.neg 63),(.pos 60),(.pos 67)]),
   ((.exchange 64 12 6),[(.neg 64),(.neg 12),(.pos 42),(.pos 54)]),
   ((.exchange 64 16 4),[(.neg 64),(.neg 16),(.pos 58),(.pos 59)]),
   ((.exchange 64 17 4),[(.neg 64),(.neg 17),(.pos 58),(.pos 60)]),
   ((.exchange 64 18 4),[(.neg 64),(.neg 18),(.pos 59),(.pos 60)]),
   ((.exchange 64 19 3),[(.neg 64),(.neg 19),(.pos 61),(.pos 62)]),
   ((.exchange 64 20 3),[(.neg 64),(.neg 20),(.pos 61),(.pos 63)]),
   ((.exchange 64 21 3),[(.neg 64),(.neg 21),(.pos 62),(.pos 63)]),
   ((.exchange 64 28 4),[(.neg 64),(.neg 28),(.pos 58),(.pos 68)]),
   ((.exchange 64 31 3),[(.neg 64),(.neg 31),(.pos 61),(.pos 69)]),
   ((.exchange 64 32 3),[(.neg 64),(.neg 32),(.pos 62),(.pos 69)]),
   ((.exchange 64 33 3),[(.neg 64),(.neg 33),(.pos 63),(.pos 69)]),
   ((.exchange 64 36 4),[(.neg 64),(.neg 36),(.pos 58),(.pos 59)]),
   ((.exchange 64 37 4),[(.neg 64),(.neg 37),(.pos 58),(.pos 60)]),
   ((.exchange 64 38 4),[(.neg 64),(.neg 38),(.pos 59),(.pos 60)]),
   ((.exchange 64 40 3),[(.neg 64),(.neg 40),(.pos 61),(.pos 63)]),
   ((.exchange 64 41 3),[(.neg 64),(.neg 41),(.pos 62),(.pos 63)]),
   ((.exchange 64 45 6),[(.neg 64),(.neg 45),(.pos 42),(.pos 43),(.pos 54)]),
   ((.exchange 64 47 6),[(.neg 64),(.neg 47),(.pos 43),(.pos 44),(.pos 54)]),
   ((.exchange 64 48 4),[(.neg 64),(.neg 48),(.pos 58),(.pos 68)]),
   ((.exchange 64 48 6),[(.neg 64),(.neg 48),(.pos 42),(.pos 54)]),
   ((.exchange 64 49 4),[(.neg 64),(.neg 49),(.pos 59),(.pos 68)]),
   ((.exchange 64 49 6),[(.neg 64),(.neg 49),(.pos 43),(.pos 54)]),
   ((.exchange 64 50 4),[(.neg 64),(.neg 50),(.pos 60),(.pos 68)]),
   ((.exchange 64 53 3),[(.neg 64),(.neg 53),(.pos 63),(.pos 69)]),
   ((.exchange 64 55 3),[(.neg 64),(.neg 55),(.pos 61),(.pos 62)]),
   ((.exchange 64 56 3),[(.neg 64),(.neg 56),(.pos 61),(.pos 63)]),
   ((.exchange 64 65 3),[(.neg 65),(.neg 64),(.pos 61),(.pos 69)]),
   ((.exchange 64 65 4),[(.neg 65),(.neg 64),(.pos 58),(.pos 68)]),
   ((.exchange 64 66 3),[(.neg 66),(.neg 64),(.pos 62),(.pos 69)]),
   ((.exchange 64 67 3),[(.neg 67),(.neg 64),(.pos 63),(.pos 69)]),
   ((.exchange 65 5 6),[(.neg 65),(.neg 5),(.pos 45),(.pos 46)]),
   ((.exchange 65 6 6),[(.neg 65),(.neg 6),(.pos 45),(.pos 48)]),
   ((.exchange 65 7 6),[(.neg 65),(.neg 7),(.pos 46),(.pos 48)]),
   ((.exchange 65 9 6),[(.neg 65),(.neg 9),(.pos 45),(.pos 51)]),
   ((.exchange 65 10 6),[(.neg 65),(.neg 10),(.pos 46),(.pos 51)]),
   ((.exchange 65 12 6),[(.neg 65),(.neg 12),(.pos 48),(.pos 51)]),
   ((.exchange 65 15 5),[(.neg 65),(.neg 15),(.pos 55),(.pos 56)]),
   ((.exchange 65 16 5),[(.neg 65),(.neg 16),(.pos 55),(.pos 58)]),
   ((.exchange 65 17 5),[(.neg 65),(.neg 17),(.pos 56),(.pos 58)]),
   ((.exchange 65 19 5),[(.neg 65),(.neg 19),(.pos 55),(.pos 61)]),
   ((.exchange 65 20 5),[(.neg 65),(.neg 20),(.pos 56),(.pos 61)]),
   ((.exchange 65 22 5),[(.neg 65),(.neg 22),(.pos 58),(.pos 61)]),
   ((.exchange 65 27 0),[(.neg 65),(.neg 27),(.pos 66),(.pos 67)]),
   ((.exchange 65 29 0),[(.neg 65),(.neg 29),(.pos 66),(.pos 68)]),
   ((.exchange 65 30 0),[(.neg 65),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 65 32 0),[(.neg 65),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 65 33 0),[(.neg 65),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 65 34 0),[(.neg 65),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 65 35 5),[(.neg 65),(.neg 35),(.pos 55),(.pos 56)]),
   ((.exchange 65 35 6),[(.neg 65),(.neg 35),(.pos 45),(.pos 46)]),
   ((.exchange 65 36 6),[(.neg 65),(.neg 36),(.pos 45),(.pos 48)]),
   ((.exchange 65 37 5),[(.neg 65),(.neg 37),(.pos 56),(.pos 58)]),
   ((.exchange 65 37 6),[(.neg 65),(.neg 37),(.pos 46),(.pos 48)]),
   ((.exchange 65 39 5),[(.neg 65),(.neg 39),(.pos 55),(.pos 61)]),
   ((.exchange 65 39 6),[(.neg 65),(.neg 39),(.pos 45),(.pos 51)]),
   ((.exchange 65 40 5),[(.neg 65),(.neg 40),(.pos 56),(.pos 61)]),
   ((.exchange 65 40 6),[(.neg 65),(.neg 40),(.pos 46),(.pos 51)]),
   ((.exchange 65 42 5),[(.neg 65),(.neg 42),(.pos 58),(.pos 61)]),
   ((.exchange 65 42 6),[(.neg 65),(.neg 42),(.pos 48),(.pos 51)]),
   ((.exchange 65 47 6),[(.neg 65),(.neg 47),(.pos 45),(.pos 46)]),
   ((.exchange 65 49 6),[(.neg 65),(.neg 49),(.pos 45),(.pos 48)]),
   ((.exchange 65 50 0),[(.neg 65),(.neg 50),(.pos 67),(.pos 68)]),
   ((.exchange 65 52 0),[(.neg 65),(.neg 52),(.pos 66),(.pos 69)]),
   ((.exchange 65 52 6),[(.neg 65),(.neg 52),(.pos 45),(.pos 51)]),
   ((.exchange 65 54 6),[(.neg 65),(.neg 54),(.pos 48),(.pos 51)]),
   ((.exchange 65 57 5),[(.neg 65),(.neg 57),(.pos 55),(.pos 56)]),
   ((.exchange 65 60 5),[(.neg 65),(.neg 60),(.pos 56),(.pos 58)]),
   ((.exchange 65 62 0),[(.neg 65),(.neg 62),(.pos 66),(.pos 69)]),
   ((.exchange 65 63 0),[(.neg 65),(.neg 63),(.pos 67),(.pos 69)]),
   ((.exchange 65 63 5),[(.neg 65),(.neg 63),(.pos 56),(.pos 61)]),
   ((.exchange 65 64 5),[(.neg 65),(.neg 64),(.pos 58),(.pos 61)]),
   ((.exchange 66 6 6),[(.neg 66),(.neg 6),(.pos 45),(.pos 49)]),
   ((.exchange 66 11 6),[(.neg 66),(.neg 11),(.pos 47),(.pos 52)]),
   ((.exchange 66 13 6),[(.neg 66),(.neg 13),(.pos 49),(.pos 52)]),
   ((.exchange 66 15 5),[(.neg 66),(.neg 15),(.pos 55),(.pos 57)]),
   ((.exchange 66 18 5),[(.neg 66),(.neg 18),(.pos 57),(.pos 59)]),
   ((.exchange 66 19 5),[(.neg 66),(.neg 19),(.pos 55),(.pos 62)]),
   ((.exchange 66 21 5),[(.neg 66),(.neg 21),(.pos 57),(.pos 62)]),
   ((.exchange 66 26 1),[(.neg 66),(.neg 26),(.pos 65),(.pos 67)]),
   ((.exchange 66 28 1),[(.neg 66),(.neg 28),(.pos 65),(.pos 68)]),
   ((.exchange 66 30 1),[(.neg 66),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 66 31 1),[(.neg 66),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 66 33 1),[(.neg 66),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 66 34 1),[(.neg 66),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 66 35 6),[(.neg 66),(.neg 35),(.pos 45),(.pos 47)]),
   ((.exchange 66 36 5),[(.neg 66),(.neg 36),(.pos 55),(.pos 59)])]

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



noncomputable def certificates_5 : List (Origin 70 1111 × List Sat.Literal) :=
  [((.exchange 66 38 6),[(.neg 66),(.neg 38),(.pos 47),(.pos 49)]),
   ((.exchange 66 39 5),[(.neg 66),(.neg 39),(.pos 55),(.pos 62)]),
   ((.exchange 66 39 6),[(.neg 66),(.neg 39),(.pos 45),(.pos 52)]),
   ((.exchange 66 41 5),[(.neg 66),(.neg 41),(.pos 57),(.pos 62)]),
   ((.exchange 66 43 6),[(.neg 66),(.neg 43),(.pos 49),(.pos 52)]),
   ((.exchange 66 46 1),[(.neg 66),(.neg 46),(.pos 65),(.pos 67)]),
   ((.exchange 66 48 1),[(.neg 66),(.neg 48),(.pos 65),(.pos 68)]),
   ((.exchange 66 48 6),[(.neg 66),(.neg 48),(.pos 45),(.pos 49)]),
   ((.exchange 66 53 1),[(.neg 66),(.neg 53),(.pos 67),(.pos 69)]),
   ((.exchange 66 54 1),[(.neg 66),(.neg 54),(.pos 68),(.pos 69)]),
   ((.exchange 66 56 1),[(.neg 66),(.neg 56),(.pos 65),(.pos 67)]),
   ((.exchange 66 58 5),[(.neg 66),(.neg 58),(.pos 55),(.pos 59)]),
   ((.exchange 66 60 5),[(.neg 66),(.neg 60),(.pos 57),(.pos 59)]),
   ((.exchange 66 61 1),[(.neg 66),(.neg 61),(.pos 65),(.pos 69)]),
   ((.exchange 66 61 5),[(.neg 66),(.neg 61),(.pos 55),(.pos 62)]),
   ((.exchange 66 63 1),[(.neg 66),(.neg 63),(.pos 67),(.pos 69)]),
   ((.exchange 66 64 1),[(.neg 66),(.neg 64),(.pos 68),(.pos 69)]),
   ((.exchange 66 64 5),[(.neg 66),(.neg 64),(.pos 59),(.pos 62)]),
   ((.exchange 67 5 6),[(.neg 67),(.neg 5),(.pos 46),(.pos 47)]),
   ((.exchange 67 8 6),[(.neg 67),(.neg 8),(.pos 47),(.pos 50)]),
   ((.exchange 67 10 6),[(.neg 67),(.neg 10),(.pos 46),(.pos 53)]),
   ((.exchange 67 11 6),[(.neg 67),(.neg 11),(.pos 47),(.pos 53)]),
   ((.exchange 67 14 6),[(.neg 67),(.neg 14),(.pos 50),(.pos 53)]),
   ((.exchange 67 15 5),[(.neg 67),(.neg 15),(.pos 56),(.pos 57)]),
   ((.exchange 67 17 5),[(.neg 67),(.neg 17),(.pos 56),(.pos 60)]),
   ((.exchange 67 20 5),[(.neg 67),(.neg 20),(.pos 56),(.pos 63)]),
   ((.exchange 67 24 5),[(.neg 67),(.neg 24),(.pos 60),(.pos 63)]),
   ((.exchange 67 29 2),[(.neg 67),(.neg 29),(.pos 66),(.pos 68)]),
   ((.exchange 67 32 2),[(.neg 67),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 67 35 6),[(.neg 67),(.neg 35),(.pos 46),(.pos 47)]),
   ((.exchange 67 38 5),[(.neg 67),(.neg 38),(.pos 57),(.pos 60)]),
   ((.exchange 67 40 6),[(.neg 67),(.neg 40),(.pos 46),(.pos 53)]),
   ((.exchange 67 41 5),[(.neg 67),(.neg 41),(.pos 57),(.pos 63)]),
   ((.exchange 67 41 6),[(.neg 67),(.neg 41),(.pos 47),(.pos 53)]),
   ((.exchange 67 48 6),[(.neg 67),(.neg 48),(.pos 46),(.pos 50)]),
   ((.exchange 67 49 2),[(.neg 67),(.neg 49),(.pos 66),(.pos 68)]),
   ((.exchange 67 51 6),[(.neg 67),(.neg 51),(.pos 46),(.pos 53)]),
   ((.exchange 67 52 2),[(.neg 67),(.neg 52),(.pos 66),(.pos 69)]),
   ((.exchange 67 54 2),[(.neg 67),(.neg 54),(.pos 68),(.pos 69)]),
   ((.exchange 67 54 6),[(.neg 67),(.neg 54),(.pos 50),(.pos 53)]),
   ((.exchange 67 55 2),[(.neg 67),(.neg 55),(.pos 65),(.pos 66)]),
   ((.exchange 67 55 5),[(.neg 67),(.neg 55),(.pos 56),(.pos 57)]),
   ((.exchange 67 58 5),[(.neg 67),(.neg 58),(.pos 56),(.pos 60)]),
   ((.exchange 67 59 5),[(.neg 67),(.neg 59),(.pos 57),(.pos 60)]),
   ((.exchange 67 61 2),[(.neg 67),(.neg 61),(.pos 65),(.pos 69)]),
   ((.exchange 67 61 5),[(.neg 67),(.neg 61),(.pos 56),(.pos 63)]),
   ((.exchange 67 62 2),[(.neg 67),(.neg 62),(.pos 66),(.pos 69)]),
   ((.exchange 68 6 6),[(.neg 68),(.neg 6),(.pos 48),(.pos 49)]),
   ((.exchange 68 7 6),[(.neg 68),(.neg 7),(.pos 48),(.pos 50)]),
   ((.exchange 68 13 6),[(.neg 68),(.neg 13),(.pos 49),(.pos 54)]),
   ((.exchange 68 14 6),[(.neg 68),(.neg 14),(.pos 50),(.pos 54)]),
   ((.exchange 68 16 5),[(.neg 68),(.neg 16),(.pos 58),(.pos 59)]),
   ((.exchange 68 17 5),[(.neg 68),(.neg 17),(.pos 58),(.pos 60)]),
   ((.exchange 68 18 5),[(.neg 68),(.neg 18),(.pos 59),(.pos 60)]),
   ((.exchange 68 22 5),[(.neg 68),(.neg 22),(.pos 58),(.pos 64)]),
   ((.exchange 68 24 5),[(.neg 68),(.neg 24),(.pos 60),(.pos 64)]),
   ((.exchange 68 25 3),[(.neg 68),(.neg 25),(.pos 65),(.pos 66)]),
   ((.exchange 68 27 3),[(.neg 68),(.neg 27),(.pos 66),(.pos 67)]),
   ((.exchange 68 31 3),[(.neg 68),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 68 32 3),[(.neg 68),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 68 36 5),[(.neg 68),(.neg 36),(.pos 58),(.pos 59)]),
   ((.exchange 68 36 6),[(.neg 68),(.neg 36),(.pos 48),(.pos 49)]),
   ((.exchange 68 37 6),[(.neg 68),(.neg 37),(.pos 48),(.pos 50)]),
   ((.exchange 68 38 5),[(.neg 68),(.neg 38),(.pos 59),(.pos 60)]),
   ((.exchange 68 38 6),[(.neg 68),(.neg 38),(.pos 49),(.pos 50)]),
   ((.exchange 68 42 5),[(.neg 68),(.neg 42),(.pos 58),(.pos 64)]),
   ((.exchange 68 43 5),[(.neg 68),(.neg 43),(.pos 59),(.pos 64)]),
   ((.exchange 68 44 5),[(.neg 68),(.neg 44),(.pos 60),(.pos 64)]),
   ((.exchange 68 45 6),[(.neg 68),(.neg 45),(.pos 48),(.pos 49)]),
   ((.exchange 68 51 6),[(.neg 68),(.neg 51),(.pos 48),(.pos 54)]),
   ((.exchange 68 55 5),[(.neg 68),(.neg 55),(.pos 58),(.pos 59)]),
   ((.exchange 68 61 3),[(.neg 68),(.neg 61),(.pos 65),(.pos 69)]),
   ((.exchange 68 61 5),[(.neg 68),(.neg 61),(.pos 58),(.pos 64)]),
   ((.exchange 68 62 3),[(.neg 68),(.neg 62),(.pos 66),(.pos 69)]),
   ((.exchange 68 62 5),[(.neg 68),(.neg 62),(.pos 59),(.pos 64)]),
   ((.exchange 68 63 5),[(.neg 68),(.neg 63),(.pos 60),(.pos 64)]),
   ((.exchange 69 9 6),[(.neg 69),(.neg 9),(.pos 51),(.pos 52)]),
   ((.exchange 69 10 6),[(.neg 69),(.neg 10),(.pos 51),(.pos 53)]),
   ((.exchange 69 11 6),[(.neg 69),(.neg 11),(.pos 52),(.pos 53)]),
   ((.exchange 69 12 6),[(.neg 69),(.neg 12),(.pos 51),(.pos 54)]),
   ((.exchange 69 13 6),[(.neg 69),(.neg 13),(.pos 52),(.pos 54)]),
   ((.exchange 69 17 5),[(.neg 69),(.neg 17),(.pos 61),(.pos 63),(.pos 64)]),
   ((.exchange 69 19 5),[(.neg 69),(.neg 19),(.pos 61),(.pos 62)]),
   ((.exchange 69 20 5),[(.neg 69),(.neg 20),(.pos 61),(.pos 63)]),
   ((.exchange 69 21 5),[(.neg 69),(.neg 21),(.pos 62),(.pos 63)]),
   ((.exchange 69 23 5),[(.neg 69),(.neg 23),(.pos 62),(.pos 64)]),
   ((.exchange 69 24 5),[(.neg 69),(.neg 24),(.pos 63),(.pos 64)]),
   ((.exchange 69 25 4),[(.neg 69),(.neg 25),(.pos 65),(.pos 66)]),
   ((.exchange 69 26 4),[(.neg 69),(.neg 26),(.pos 65),(.pos 67)]),
   ((.exchange 69 28 4),[(.neg 69),(.neg 28),(.pos 65),(.pos 68)]),
   ((.exchange 69 29 4),[(.neg 69),(.neg 29),(.pos 66),(.pos 68)]),
   ((.exchange 69 30 4),[(.neg 69),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 69 39 5),[(.neg 69),(.neg 39),(.pos 61),(.pos 62)]),
   ((.exchange 69 40 6),[(.neg 69),(.neg 40),(.pos 51),(.pos 53)]),
   ((.exchange 69 41 5),[(.neg 69),(.neg 41),(.pos 62),(.pos 63)]),
   ((.exchange 69 42 5),[(.neg 69),(.neg 42),(.pos 61),(.pos 64)]),
   ((.exchange 69 42 6),[(.neg 69),(.neg 42),(.pos 51),(.pos 54)]),
   ((.exchange 69 43 5),[(.neg 69),(.neg 43),(.pos 62),(.pos 64)]),
   ((.exchange 69 44 5),[(.neg 69),(.neg 44),(.pos 63),(.pos 64)]),
   ((.exchange 69 45 6),[(.neg 69),(.neg 45),(.pos 51),(.pos 52)]),
   ((.exchange 69 46 4),[(.neg 69),(.neg 46),(.pos 65),(.pos 67)]),
   ((.exchange 69 47 6),[(.neg 69),(.neg 47),(.pos 52),(.pos 53)]),
   ((.exchange 69 48 6),[(.neg 69),(.neg 48),(.pos 51),(.pos 54)]),
   ((.exchange 69 50 6),[(.neg 69),(.neg 50),(.pos 53),(.pos 54)]),
   ((.exchange 69 55 4),[(.neg 69),(.neg 55),(.pos 65),(.pos 66)]),
   ((.exchange 69 55 5),[(.neg 69),(.neg 55),(.pos 61),(.pos 62)]),
   ((.exchange 69 56 4),[(.neg 69),(.neg 56),(.pos 65),(.pos 67)]),
   ((.exchange 69 56 5),[(.neg 69),(.neg 56),(.pos 61),(.pos 63)]),
   ((.exchange 69 57 4),[(.neg 69),(.neg 57),(.pos 66),(.pos 67)]),
   ((.exchange 69 58 4),[(.neg 69),(.neg 58),(.pos 65),(.pos 68)]),
   ((.exchange 69 58 5),[(.neg 69),(.neg 58),(.pos 61),(.pos 64)]),
   ((.exchange 69 59 4),[(.neg 69),(.neg 59),(.pos 66),(.pos 68)]),
   ((.exchange 69 59 5),[(.neg 69),(.neg 59),(.pos 62),(.pos 64)]),
   ((.exchange 69 60 5),[(.neg 69),(.neg 60),(.pos 63),(.pos 64)]),
   (.newPoint,[(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 0),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 57),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 48),(.pos 51),(.pos 55),(.pos 56),(.pos 58),(.pos 61),(.pos 65)]),
   ((.excluded 1),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 58),(.neg 56),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 48),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 47),(.pos 49),(.pos 52),(.pos 55),(.pos 57),(.pos 59),(.pos 62),(.pos 66)]),
   ((.excluded 2),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 50),(.pos 55),(.pos 60),(.pos 69)]),
   ((.excluded 3),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 50),(.pos 55),(.pos 60)]),
   ((.excluded 4),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 53),(.pos 55),(.pos 63),(.pos 68)]),
   ((.excluded 5),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 53),(.pos 55),(.pos 63)]),
   ((.excluded 6),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 54),(.pos 55),(.pos 64),(.pos 67)]),
   ((.excluded 7),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 54),(.pos 55),(.pos 64)]),
   ((.excluded 8),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 55),(.pos 67)]),
   ((.excluded 9),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 55),(.pos 68)]),
   ((.excluded 10),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 55),(.pos 69)]),
   ((.excluded 11),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 55)]),
   ((.excluded 12),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 45),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 46),(.pos 47),(.pos 50),(.pos 53),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 67)])]

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



end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C62

end
end
end BundlePart0

