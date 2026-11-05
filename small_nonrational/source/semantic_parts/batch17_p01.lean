module
public import Consolidated.SemanticData
public import Mathlib.Data.Fin.Tuple.Basic
public import MatroidCatalogue.Definitions
public import MatroidChecked.FastSemanticChecks
public import MatroidChecked.BitsetSemanticChecks
public import MatroidChecked.BitsetOrigins


section BundlePart1
/- Source: MatroidChecked/SemanticParts/Cases21Part00/Checks00.lean -/



@[expose] public section
noncomputable section


set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C76


noncomputable def certificates_0 : List (Origin 70 1271 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.pos 1)]),
   ((.fixed 2),[(.pos 2)]),
   ((.fixed 3),[(.pos 3)]),
   ((.fixed 4),[(.pos 4)]),
   ((.fixed 5),[(.pos 5)]),
   ((.fixed 6),[(.pos 6)]),
   ((.fixed 7),[(.pos 7)]),
   ((.fixed 8),[(.pos 8)]),
   ((.fixed 9),[(.neg 9)]),
   ((.fixed 10),[(.pos 10)]),
   ((.fixed 11),[(.pos 11)]),
   ((.fixed 12),[(.pos 12)]),
   ((.fixed 13),[(.pos 13)]),
   ((.fixed 14),[(.neg 14)]),
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
   ((.exchange 1 36 4),[(.neg 36),(.neg 1),(.pos 0),(.pos 35)]),
   ((.exchange 1 37 4),[(.neg 37),(.neg 1),(.pos 0),(.pos 35)]),
   ((.exchange 1 38 4),[(.neg 38),(.neg 1),(.pos 0),(.pos 35)]),
   ((.exchange 1 45 2),[(.neg 45),(.neg 1),(.pos 9),(.pos 39)]),
   ((.exchange 1 51 2),[(.neg 51),(.neg 1),(.pos 9),(.pos 39)]),
   ((.exchange 1 52 2),[(.neg 52),(.neg 1),(.pos 9),(.pos 39)]),
   ((.exchange 2 35 4),[(.neg 35),(.neg 2),(.pos 0),(.pos 36)]),
   ((.exchange 2 37 4),[(.neg 37),(.neg 2),(.pos 0),(.pos 36)]),
   ((.exchange 2 38 4),[(.neg 38),(.neg 2),(.pos 0),(.pos 36)]),
   ((.exchange 3 35 4),[(.neg 35),(.neg 3),(.pos 0),(.pos 37)]),
   ((.exchange 3 36 4),[(.neg 36),(.neg 3),(.pos 0),(.pos 37)]),
   ((.exchange 3 38 4),[(.neg 38),(.neg 3),(.pos 0),(.pos 37)]),
   ((.exchange 3 50 0),[(.neg 50),(.neg 3),(.pos 14),(.pos 44)]),
   ((.exchange 3 53 0),[(.neg 53),(.neg 3),(.pos 14),(.pos 44)]),
   ((.exchange 3 54 0),[(.neg 54),(.neg 3),(.pos 14),(.pos 44)]),
   ((.exchange 4 35 4),[(.neg 35),(.neg 4),(.pos 0),(.pos 38)]),
   ((.exchange 4 36 4),[(.neg 36),(.neg 4),(.pos 0),(.pos 38)]),
   ((.exchange 4 37 4),[(.neg 37),(.neg 4),(.pos 0),(.pos 38)]),
   ((.exchange 5 39 2),[(.neg 39),(.neg 5),(.pos 9),(.pos 45)]),
   ((.exchange 5 51 2),[(.neg 51),(.neg 5),(.pos 9),(.pos 45)]),
   ((.exchange 5 52 2),[(.neg 52),(.neg 5),(.pos 9),(.pos 45)]),
   ((.exchange 7 44 0),[(.neg 44),(.neg 7),(.pos 14),(.pos 50)]),
   ((.exchange 7 53 0),[(.neg 53),(.neg 7),(.pos 14),(.pos 50)]),
   ((.exchange 7 54 0),[(.neg 54),(.neg 7),(.pos 14),(.pos 50)]),
   ((.exchange 10 39 2),[(.neg 39),(.neg 10),(.pos 9),(.pos 51)]),
   ((.exchange 10 44 0),[(.neg 44),(.neg 10),(.pos 14),(.pos 53)]),
   ((.exchange 10 45 2),[(.neg 45),(.neg 10),(.pos 9),(.pos 51)]),
   ((.exchange 10 50 0),[(.neg 50),(.neg 10),(.pos 14),(.pos 53)]),
   ((.exchange 10 52 2),[(.neg 52),(.neg 10),(.pos 9),(.pos 51)]),
   ((.exchange 10 54 0),[(.neg 54),(.neg 10),(.pos 14),(.pos 53)]),
   ((.exchange 11 39 2),[(.neg 39),(.neg 11),(.pos 9),(.pos 52)]),
   ((.exchange 11 45 2),[(.neg 45),(.neg 11),(.pos 9),(.pos 52)]),
   ((.exchange 11 51 2),[(.neg 51),(.neg 11),(.pos 9),(.pos 52)]),
   ((.exchange 12 44 0),[(.neg 44),(.neg 12),(.pos 14),(.pos 54)]),
   ((.exchange 12 50 0),[(.neg 50),(.neg 12),(.pos 14),(.pos 54)]),
   ((.exchange 12 53 0),[(.neg 53),(.neg 12),(.pos 14),(.pos 54)]),
   ((.exchange 35 11 0),[(.neg 35),(.neg 11),(.pos 41),(.pos 47)]),
   ((.exchange 35 20 1),[(.neg 35),(.neg 20),(.pos 40),(.pos 56)]),
   ((.exchange 35 21 0),[(.neg 35),(.neg 21),(.pos 41),(.pos 57)]),
   ((.exchange 35 26 1),[(.neg 35),(.neg 26),(.pos 46),(.pos 56)]),
   ((.exchange 35 27 0),[(.neg 35),(.neg 27),(.pos 47),(.pos 57)]),
   ((.exchange 35 32 2),[(.neg 35),(.neg 32),(.pos 39),(.pos 45),(.pos 55)]),
   ((.exchange 35 51 1),[(.neg 51),(.neg 35),(.pos 40),(.pos 46)]),
   ((.exchange 35 53 0),[(.neg 53),(.neg 35),(.pos 41),(.pos 47)]),
   ((.exchange 35 63 0),[(.neg 63),(.neg 35),(.pos 41),(.pos 57)]),
   ((.exchange 36 12 1),[(.neg 36),(.neg 12),(.pos 42),(.pos 48)]),
   ((.exchange 36 13 0),[(.neg 36),(.neg 13),(.pos 43),(.pos 49)]),
   ((.exchange 36 19 3),[(.neg 36),(.neg 19),(.pos 39),(.pos 55)]),
   ((.exchange 36 22 1),[(.neg 36),(.neg 22),(.pos 42),(.pos 58)]),
   ((.exchange 36 23 0),[(.neg 36),(.neg 23),(.pos 43),(.pos 59)]),
   ((.exchange 36 25 3),[(.neg 36),(.neg 25),(.pos 45),(.pos 55)]),
   ((.exchange 36 28 1),[(.neg 36),(.neg 28),(.pos 48),(.pos 58)]),
   ((.exchange 36 29 0),[(.neg 36),(.neg 29),(.pos 49),(.pos 59)]),
   ((.exchange 36 61 1),[(.neg 61),(.neg 36),(.pos 42),(.pos 58)]),
   ((.exchange 36 61 3),[(.neg 61),(.neg 36),(.pos 39),(.pos 55)]),
   ((.exchange 37 12 2),[(.neg 37),(.neg 12),(.pos 42),(.pos 48)]),
   ((.exchange 37 20 3),[(.neg 37),(.neg 20),(.pos 40),(.pos 56)]),
   ((.exchange 37 22 2),[(.neg 37),(.neg 22),(.pos 42),(.pos 58)]),
   ((.exchange 37 24 0),[(.neg 37),(.neg 24),(.pos 44),(.pos 60)]),
   ((.exchange 37 26 3),[(.neg 37),(.neg 26),(.pos 46),(.pos 56)]),
   ((.exchange 37 28 2),[(.neg 37),(.neg 28),(.pos 48),(.pos 58)]),
   ((.exchange 37 68 0),[(.neg 68),(.neg 37),(.pos 50),(.pos 60)]),
   ((.exchange 38 24 1),[(.neg 38),(.neg 24),(.pos 44),(.pos 60)]),
   ((.exchange 38 29 2),[(.neg 38),(.neg 29),(.pos 49),(.pos 59)]),
   ((.exchange 38 30 1),[(.neg 38),(.neg 30),(.pos 50),(.pos 60)]),
   ((.exchange 38 62 2),[(.neg 62),(.neg 38),(.pos 43),(.pos 59)]),
   ((.exchange 38 63 1),[(.neg 63),(.neg 38),(.pos 44),(.pos 60)]),
   ((.exchange 38 68 1),[(.neg 68),(.neg 38),(.pos 50),(.pos 60)]),
   ((.exchange 39 3 1),[(.neg 39),(.neg 3),(.pos 40),(.pos 42)]),
   ((.exchange 39 4 0),[(.neg 39),(.neg 4),(.pos 41),(.pos 43)]),
   ((.exchange 39 15 4),[(.neg 39),(.neg 15),(.pos 35),(.pos 55)]),
   ((.exchange 39 20 1),[(.neg 39),(.neg 20),(.pos 40),(.pos 61)]),
   ((.exchange 39 21 0),[(.neg 39),(.neg 21),(.pos 41),(.pos 62)]),
   ((.exchange 39 22 1),[(.neg 39),(.neg 22),(.pos 42),(.pos 61)]),
   ((.exchange 39 23 0),[(.neg 39),(.neg 23),(.pos 43),(.pos 62)]),
   ((.exchange 39 37 1),[(.neg 39),(.neg 37),(.pos 40),(.pos 42)]),
   ((.exchange 39 38 0),[(.neg 39),(.neg 38),(.pos 41),(.pos 43)]),
   ((.exchange 39 47 0),[(.neg 47),(.neg 39),(.pos 41),(.pos 52)]),
   ((.exchange 39 57 0),[(.neg 57),(.neg 39),(.pos 41),(.pos 62)]),
   ((.exchange 39 57 4),[(.neg 57),(.neg 39),(.pos 35),(.pos 55)]),
   ((.exchange 40 2 2),[(.neg 40),(.neg 2),(.pos 39),(.pos 42)]),
   ((.exchange 40 4 0),[(.neg 40),(.neg 4),(.pos 41),(.pos 44)]),
   ((.exchange 40 5 4),[(.neg 40),(.neg 5),(.pos 35),(.pos 46)]),
   ((.exchange 40 11 0),[(.neg 40),(.neg 11),(.pos 41),(.pos 53)]),
   ((.exchange 40 12 2),[(.neg 40),(.neg 12),(.pos 42),(.pos 51)]),
   ((.exchange 40 15 4),[(.neg 40),(.neg 15),(.pos 35),(.pos 56)]),
   ((.exchange 40 17 4),[(.neg 40),(.neg 17),(.pos 37),(.pos 56)]),
   ((.exchange 40 19 2),[(.neg 40),(.neg 19),(.pos 39),(.pos 61)]),
   ((.exchange 40 21 0),[(.neg 40),(.neg 21),(.pos 41),(.pos 63)]),
   ((.exchange 40 22 2),[(.neg 40),(.neg 22),(.pos 42),(.pos 61)]),
   ((.exchange 40 24 0),[(.neg 40),(.neg 24),(.pos 44),(.pos 63)]),
   ((.exchange 40 26 4),[(.neg 40),(.neg 26),(.pos 46),(.pos 56)]),
   ((.exchange 40 33 0),[(.neg 40),(.neg 33),(.pos 53),(.pos 63)])]

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



noncomputable def certificates_1 : List (Origin 70 1271 × List Sat.Literal) :=
  [((.exchange 40 43 0),[(.neg 43),(.neg 40),(.pos 41),(.pos 44)]),
   ((.exchange 40 47 4),[(.neg 47),(.neg 40),(.pos 35),(.pos 46)]),
   ((.exchange 40 48 2),[(.neg 48),(.neg 40),(.pos 42),(.pos 51)]),
   ((.exchange 40 48 4),[(.neg 48),(.neg 40),(.pos 37),(.pos 46)]),
   ((.exchange 40 55 4),[(.neg 55),(.neg 40),(.pos 35),(.pos 56)]),
   ((.exchange 40 58 2),[(.neg 58),(.neg 40),(.pos 42),(.pos 61)]),
   ((.exchange 40 60 0),[(.neg 60),(.neg 40),(.pos 44),(.pos 63)]),
   ((.exchange 40 62 0),[(.neg 62),(.neg 40),(.pos 41),(.pos 63)]),
   ((.exchange 41 3 1),[(.neg 41),(.neg 3),(.pos 40),(.pos 44)]),
   ((.exchange 41 5 4),[(.neg 41),(.neg 5),(.pos 35),(.pos 47)]),
   ((.exchange 41 8 4),[(.neg 41),(.neg 8),(.pos 38),(.pos 47)]),
   ((.exchange 41 10 1),[(.neg 41),(.neg 10),(.pos 40),(.pos 53)]),
   ((.exchange 41 13 2),[(.neg 41),(.neg 13),(.pos 43),(.pos 52)]),
   ((.exchange 41 15 4),[(.neg 41),(.neg 15),(.pos 35),(.pos 57)]),
   ((.exchange 41 18 4),[(.neg 41),(.neg 18),(.pos 38),(.pos 57)]),
   ((.exchange 41 19 2),[(.neg 41),(.neg 19),(.pos 39),(.pos 62)]),
   ((.exchange 41 20 1),[(.neg 41),(.neg 20),(.pos 40),(.pos 63)]),
   ((.exchange 41 23 2),[(.neg 41),(.neg 23),(.pos 43),(.pos 62)]),
   ((.exchange 41 24 1),[(.neg 41),(.neg 24),(.pos 44),(.pos 63)]),
   ((.exchange 41 27 4),[(.neg 41),(.neg 27),(.pos 47),(.pos 57)]),
   ((.exchange 41 32 2),[(.neg 41),(.neg 32),(.pos 52),(.pos 62)]),
   ((.exchange 41 33 1),[(.neg 41),(.neg 33),(.pos 53),(.pos 63)]),
   ((.exchange 41 37 1),[(.neg 41),(.neg 37),(.pos 40),(.pos 44)]),
   ((.exchange 41 46 1),[(.neg 46),(.neg 41),(.pos 40),(.pos 53)]),
   ((.exchange 41 48 2),[(.neg 48),(.neg 41),(.pos 39),(.pos 43),(.pos 52)]),
   ((.exchange 41 60 1),[(.neg 60),(.neg 41),(.pos 44),(.pos 63)]),
   ((.exchange 41 61 2),[(.neg 61),(.neg 41),(.pos 39),(.pos 62)]),
   ((.exchange 41 66 4),[(.neg 66),(.neg 41),(.pos 47),(.pos 57)]),
   ((.exchange 42 1 3),[(.neg 42),(.neg 1),(.pos 39),(.pos 40)]),
   ((.exchange 42 4 0),[(.neg 42),(.neg 4),(.pos 43),(.pos 44)]),
   ((.exchange 42 6 4),[(.neg 42),(.neg 6),(.pos 36),(.pos 48)]),
   ((.exchange 42 13 0),[(.neg 42),(.neg 13),(.pos 43),(.pos 54)]),
   ((.exchange 42 16 4),[(.neg 42),(.neg 16),(.pos 36),(.pos 58)]),
   ((.exchange 42 19 3),[(.neg 42),(.neg 19),(.pos 39),(.pos 61)]),
   ((.exchange 42 23 0),[(.neg 42),(.neg 23),(.pos 43),(.pos 64)]),
   ((.exchange 42 24 0),[(.neg 42),(.neg 24),(.pos 44),(.pos 64)]),
   ((.exchange 42 34 0),[(.neg 42),(.neg 34),(.pos 54),(.pos 64)]),
   ((.exchange 42 38 0),[(.neg 42),(.neg 38),(.pos 43),(.pos 44)]),
   ((.exchange 42 47 0),[(.neg 47),(.neg 42),(.pos 43),(.pos 44),(.pos 54)]),
   ((.exchange 43 1 3),[(.neg 43),(.neg 1),(.pos 39),(.pos 41)]),
   ((.exchange 43 3 1),[(.neg 43),(.neg 3),(.pos 42),(.pos 44)]),
   ((.exchange 43 7 4),[(.neg 43),(.neg 7),(.pos 36),(.pos 38),(.pos 49)]),
   ((.exchange 43 8 4),[(.neg 43),(.neg 8),(.pos 38),(.pos 49)]),
   ((.exchange 43 12 1),[(.neg 43),(.neg 12),(.pos 42),(.pos 54)]),
   ((.exchange 43 17 4),[(.neg 43),(.neg 17),(.pos 36),(.pos 38),(.pos 59)]),
   ((.exchange 43 18 4),[(.neg 43),(.neg 18),(.pos 38),(.pos 59)]),
   ((.exchange 43 22 1),[(.neg 43),(.neg 22),(.pos 42),(.pos 64)]),
   ((.exchange 43 33 3),[(.neg 43),(.neg 33),(.pos 41),(.pos 52),(.pos 62)]),
   ((.exchange 43 40 1),[(.neg 43),(.neg 40),(.pos 42),(.pos 44)]),
   ((.exchange 43 46 1),[(.neg 46),(.neg 43),(.pos 42),(.pos 44),(.pos 54)]),
   ((.exchange 43 48 1),[(.neg 48),(.neg 43),(.pos 42),(.pos 54)]),
   ((.exchange 43 50 4),[(.neg 50),(.neg 43),(.pos 38),(.pos 49)]),
   ((.exchange 43 51 1),[(.neg 51),(.neg 43),(.pos 42),(.pos 54)]),
   ((.exchange 43 57 4),[(.neg 57),(.neg 43),(.pos 38),(.pos 59)]),
   ((.exchange 43 58 1),[(.neg 58),(.neg 43),(.pos 42),(.pos 64)]),
   ((.exchange 43 58 4),[(.neg 58),(.neg 43),(.pos 36),(.pos 59)]),
   ((.exchange 43 66 4),[(.neg 66),(.neg 43),(.pos 49),(.pos 59)]),
   ((.exchange 44 1 3),[(.neg 44),(.neg 1),(.pos 40),(.pos 41)]),
   ((.exchange 44 17 4),[(.neg 44),(.neg 17),(.pos 37),(.pos 60)]),
   ((.exchange 44 18 4),[(.neg 44),(.neg 18),(.pos 38),(.pos 60)]),
   ((.exchange 44 20 3),[(.neg 44),(.neg 20),(.pos 40),(.pos 63)]),
   ((.exchange 44 22 2),[(.neg 44),(.neg 22),(.pos 42),(.pos 64)]),
   ((.exchange 44 35 3),[(.neg 44),(.neg 35),(.pos 40),(.pos 41)]),
   ((.exchange 44 39 2),[(.neg 44),(.neg 39),(.pos 42),(.pos 43)]),
   ((.exchange 44 55 2),[(.neg 55),(.neg 44),(.pos 42),(.pos 43),(.pos 64)]),
   ((.exchange 44 56 4),[(.neg 56),(.neg 44),(.pos 37),(.pos 60)]),
   ((.exchange 44 58 2),[(.neg 58),(.neg 44),(.pos 42),(.pos 64)]),
   ((.exchange 44 58 4),[(.neg 58),(.neg 44),(.pos 37),(.pos 60)]),
   ((.exchange 44 59 2),[(.neg 59),(.neg 44),(.pos 43),(.pos 64)]),
   ((.exchange 44 61 2),[(.neg 61),(.neg 44),(.pos 42),(.pos 64)]),
   ((.exchange 44 62 2),[(.neg 62),(.neg 44),(.pos 43),(.pos 64)]),
   ((.exchange 45 7 1),[(.neg 45),(.neg 7),(.pos 46),(.pos 48)]),
   ((.exchange 45 8 0),[(.neg 45),(.neg 8),(.pos 47),(.pos 49)]),
   ((.exchange 45 26 1),[(.neg 45),(.neg 26),(.pos 46),(.pos 65)]),
   ((.exchange 45 27 0),[(.neg 45),(.neg 27),(.pos 47),(.pos 66)]),
   ((.exchange 45 28 1),[(.neg 45),(.neg 28),(.pos 48),(.pos 65)]),
   ((.exchange 45 29 0),[(.neg 45),(.neg 29),(.pos 49),(.pos 66)]),
   ((.exchange 46 1 5),[(.neg 46),(.neg 1),(.pos 35),(.pos 40)]),
   ((.exchange 46 2 2),[(.neg 46),(.neg 2),(.pos 45),(.pos 48),(.pos 51)]),
   ((.exchange 46 3 5),[(.neg 46),(.neg 3),(.pos 37),(.pos 40)]),
   ((.exchange 46 4 0),[(.neg 46),(.neg 4),(.pos 47),(.pos 50),(.pos 53)]),
   ((.exchange 46 8 0),[(.neg 46),(.neg 8),(.pos 47),(.pos 50)]),
   ((.exchange 46 11 0),[(.neg 46),(.neg 11),(.pos 47),(.pos 53)]),
   ((.exchange 46 12 2),[(.neg 46),(.neg 12),(.pos 48),(.pos 51)]),
   ((.exchange 46 15 5),[(.neg 46),(.neg 15),(.pos 35),(.pos 56)]),
   ((.exchange 46 16 5),[(.neg 46),(.neg 16),(.pos 35),(.pos 37),(.pos 56)]),
   ((.exchange 46 17 5),[(.neg 46),(.neg 17),(.pos 37),(.pos 56)]),
   ((.exchange 46 19 2),[(.neg 46),(.neg 19),(.pos 45),(.pos 51),(.pos 65)]),
   ((.exchange 46 20 5),[(.neg 46),(.neg 20),(.pos 40),(.pos 56)]),
   ((.exchange 46 27 0),[(.neg 46),(.neg 27),(.pos 47),(.pos 67)]),
   ((.exchange 46 30 0),[(.neg 46),(.neg 30),(.pos 50),(.pos 67)]),
   ((.exchange 46 31 2),[(.neg 46),(.neg 31),(.pos 51),(.pos 65)]),
   ((.exchange 46 33 0),[(.neg 46),(.neg 33),(.pos 53),(.pos 67)]),
   ((.exchange 46 42 5),[(.neg 46),(.neg 42),(.pos 37),(.pos 40)]),
   ((.exchange 46 43 0),[(.neg 46),(.neg 43),(.pos 47),(.pos 50),(.pos 53)]),
   ((.exchange 46 55 2),[(.neg 55),(.neg 46),(.pos 45),(.pos 65)]),
   ((.exchange 46 66 0),[(.neg 66),(.neg 46),(.pos 47),(.pos 67)]),
   ((.exchange 47 1 5),[(.neg 47),(.neg 1),(.pos 35),(.pos 41)]),
   ((.exchange 47 2 2),[(.neg 47),(.neg 2),(.pos 45),(.pos 49),(.pos 52)]),
   ((.exchange 47 4 5),[(.neg 47),(.neg 4),(.pos 38),(.pos 41)]),
   ((.exchange 47 7 1),[(.neg 47),(.neg 7),(.pos 46),(.pos 50)]),
   ((.exchange 47 12 1),[(.neg 47),(.neg 12),(.pos 46),(.pos 50),(.pos 53)]),
   ((.exchange 47 13 2),[(.neg 47),(.neg 13),(.pos 49),(.pos 52)]),
   ((.exchange 47 25 2),[(.neg 47),(.neg 25),(.pos 45),(.pos 66)]),
   ((.exchange 47 26 1),[(.neg 47),(.neg 26),(.pos 46),(.pos 67)]),
   ((.exchange 47 29 2),[(.neg 47),(.neg 29),(.pos 49),(.pos 66)]),
   ((.exchange 47 30 1),[(.neg 47),(.neg 30),(.pos 50),(.pos 67)]),
   ((.exchange 47 32 2),[(.neg 47),(.neg 32),(.pos 52),(.pos 66)]),
   ((.exchange 47 33 1),[(.neg 47),(.neg 33),(.pos 53),(.pos 67)]),
   ((.exchange 47 34 1),[(.neg 47),(.neg 34),(.pos 50),(.pos 53),(.pos 67)]),
   ((.exchange 47 40 5),[(.neg 47),(.neg 40),(.pos 35),(.pos 41)]),
   ((.exchange 47 42 1),[(.neg 47),(.neg 42),(.pos 46),(.pos 50),(.pos 53)]),
   ((.exchange 47 48 1),[(.neg 48),(.neg 47),(.pos 46),(.pos 50)]),
   ((.exchange 47 48 2),[(.neg 48),(.neg 47),(.pos 45),(.pos 49)]),
   ((.exchange 47 51 1),[(.neg 51),(.neg 47),(.pos 46),(.pos 53)]),
   ((.exchange 47 59 2),[(.neg 59),(.neg 47),(.pos 49),(.pos 66)]),
   ((.exchange 47 61 1),[(.neg 61),(.neg 47),(.pos 46),(.pos 53),(.pos 67)]),
   ((.exchange 47 65 1),[(.neg 65),(.neg 47),(.pos 46),(.pos 67)]),
   ((.exchange 47 69 2),[(.neg 69),(.neg 47),(.pos 52),(.pos 66)]),
   ((.exchange 48 1 5),[(.neg 48),(.neg 1),(.pos 36),(.pos 37),(.pos 42)]),
   ((.exchange 48 4 0),[(.neg 48),(.neg 4),(.pos 49),(.pos 50),(.pos 54)]),
   ((.exchange 48 5 3),[(.neg 48),(.neg 5),(.pos 45),(.pos 46)]),
   ((.exchange 48 8 0),[(.neg 48),(.neg 8),(.pos 49),(.pos 50)]),
   ((.exchange 48 10 3),[(.neg 48),(.neg 10),(.pos 46),(.pos 51)]),
   ((.exchange 48 11 0),[(.neg 48),(.neg 11),(.pos 49),(.pos 50),(.pos 54)]),
   ((.exchange 48 22 5),[(.neg 48),(.neg 22),(.pos 42),(.pos 58)]),
   ((.exchange 48 24 5),[(.neg 48),(.neg 24),(.pos 37),(.pos 42),(.pos 58)]),
   ((.exchange 48 26 3),[(.neg 48),(.neg 26),(.pos 46),(.pos 65)])]

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



noncomputable def certificates_2 : List (Origin 70 1271 × List Sat.Literal) :=
  [((.exchange 48 29 0),[(.neg 48),(.neg 29),(.pos 49),(.pos 68)]),
   ((.exchange 48 31 3),[(.neg 48),(.neg 31),(.pos 51),(.pos 65)]),
   ((.exchange 48 33 0),[(.neg 48),(.neg 33),(.pos 50),(.pos 54),(.pos 68)]),
   ((.exchange 48 34 0),[(.neg 48),(.neg 34),(.pos 54),(.pos 68)]),
   ((.exchange 48 41 3),[(.neg 48),(.neg 41),(.pos 45),(.pos 46),(.pos 51)]),
   ((.exchange 48 43 0),[(.neg 48),(.neg 43),(.pos 49),(.pos 54)]),
   ((.exchange 48 47 0),[(.neg 48),(.neg 47),(.pos 49),(.pos 50)]),
   ((.exchange 48 47 3),[(.neg 48),(.neg 47),(.pos 45),(.pos 46)]),
   ((.exchange 48 52 0),[(.neg 52),(.neg 48),(.pos 49),(.pos 54)]),
   ((.exchange 48 56 3),[(.neg 56),(.neg 48),(.pos 46),(.pos 65)]),
   ((.exchange 48 63 0),[(.neg 63),(.neg 48),(.pos 50),(.pos 54),(.pos 68)]),
   ((.exchange 48 64 0),[(.neg 64),(.neg 48),(.pos 54),(.pos 68)]),
   ((.exchange 48 67 0),[(.neg 67),(.neg 48),(.pos 50),(.pos 68)]),
   ((.exchange 48 69 0),[(.neg 69),(.neg 48),(.pos 54),(.pos 68)]),
   ((.exchange 49 1 3),[(.neg 49),(.neg 1),(.pos 45),(.pos 47),(.pos 52)]),
   ((.exchange 49 3 1),[(.neg 49),(.neg 3),(.pos 48),(.pos 50),(.pos 54)]),
   ((.exchange 49 7 1),[(.neg 49),(.neg 7),(.pos 48),(.pos 50)]),
   ((.exchange 49 12 1),[(.neg 49),(.neg 12),(.pos 48),(.pos 54)]),
   ((.exchange 49 20 5),[(.neg 49),(.neg 20),(.pos 36),(.pos 38),(.pos 43),(.pos 59)]),
   ((.exchange 49 24 1),[(.neg 49),(.neg 24),(.pos 50),(.pos 54),(.pos 68)]),
   ((.exchange 49 26 3),[(.neg 49),(.neg 26),(.pos 45),(.pos 47),(.pos 66)]),
   ((.exchange 49 28 1),[(.neg 49),(.neg 28),(.pos 48),(.pos 68)]),
   ((.exchange 49 31 1),[(.neg 49),(.neg 31),(.pos 48),(.pos 54),(.pos 68)]),
   ((.exchange 49 32 3),[(.neg 49),(.neg 32),(.pos 52),(.pos 66)]),
   ((.exchange 49 34 1),[(.neg 49),(.neg 34),(.pos 54),(.pos 68)]),
   ((.exchange 49 42 1),[(.neg 49),(.neg 42),(.pos 48),(.pos 54)]),
   ((.exchange 49 44 5),[(.neg 49),(.neg 44),(.pos 38),(.pos 43)]),
   ((.exchange 49 51 1),[(.neg 51),(.neg 49),(.pos 48),(.pos 54)]),
   ((.exchange 49 60 1),[(.neg 60),(.neg 49),(.pos 50),(.pos 68)]),
   ((.exchange 49 63 1),[(.neg 63),(.neg 49),(.pos 50),(.pos 54),(.pos 68)]),
   ((.exchange 49 64 1),[(.neg 64),(.neg 49),(.pos 54),(.pos 68)]),
   ((.exchange 49 65 1),[(.neg 65),(.neg 49),(.pos 48),(.pos 68)]),
   ((.exchange 49 67 1),[(.neg 67),(.neg 49),(.pos 50),(.pos 68)]),
   ((.exchange 49 69 1),[(.neg 69),(.neg 49),(.pos 54),(.pos 68)]),
   ((.exchange 50 1 3),[(.neg 50),(.neg 1),(.pos 46),(.pos 47),(.pos 53)]),
   ((.exchange 50 4 5),[(.neg 50),(.neg 4),(.pos 38),(.pos 44)]),
   ((.exchange 50 26 3),[(.neg 50),(.neg 26),(.pos 46),(.pos 67)]),
   ((.exchange 50 27 3),[(.neg 50),(.neg 27),(.pos 47),(.pos 67)]),
   ((.exchange 50 28 2),[(.neg 50),(.neg 28),(.pos 48),(.pos 68)]),
   ((.exchange 50 29 2),[(.neg 50),(.neg 29),(.pos 49),(.pos 68)]),
   ((.exchange 50 35 3),[(.neg 50),(.neg 35),(.pos 46),(.pos 47)]),
   ((.exchange 50 36 2),[(.neg 50),(.neg 36),(.pos 48),(.pos 49)]),
   ((.exchange 50 45 2),[(.neg 50),(.neg 45),(.pos 48),(.pos 49)]),
   ((.exchange 50 45 3),[(.neg 50),(.neg 45),(.pos 46),(.pos 47)]),
   ((.exchange 50 56 3),[(.neg 56),(.neg 50),(.pos 46),(.pos 67)]),
   ((.exchange 50 56 5),[(.neg 56),(.neg 50),(.pos 37),(.pos 60)]),
   ((.exchange 50 59 2),[(.neg 59),(.neg 50),(.pos 49),(.pos 68)]),
   ((.exchange 50 65 3),[(.neg 65),(.neg 50),(.pos 46),(.pos 67)]),
   ((.exchange 50 66 2),[(.neg 66),(.neg 50),(.pos 49),(.pos 68)]),
   ((.exchange 51 22 5),[(.neg 51),(.neg 22),(.pos 42),(.pos 61)]),
   ((.exchange 51 24 0),[(.neg 51),(.neg 24),(.pos 53),(.pos 54),(.pos 69)]),
   ((.exchange 51 33 0),[(.neg 51),(.neg 33),(.pos 53),(.pos 69)]),
   ((.exchange 51 34 0),[(.neg 51),(.neg 34),(.pos 54),(.pos 69)]),
   ((.exchange 51 37 4),[(.neg 51),(.neg 37),(.pos 46),(.pos 48)]),
   ((.exchange 51 37 5),[(.neg 51),(.neg 37),(.pos 40),(.pos 42)]),
   ((.exchange 51 58 5),[(.neg 58),(.neg 51),(.pos 42),(.pos 61)]),
   ((.exchange 52 63 1),[(.neg 63),(.neg 52),(.pos 53),(.pos 69)]),
   ((.exchange 53 1 5),[(.neg 53),(.neg 1),(.pos 40),(.pos 41)]),
   ((.exchange 53 26 4),[(.neg 53),(.neg 26),(.pos 46),(.pos 67)]),
   ((.exchange 53 27 4),[(.neg 53),(.neg 27),(.pos 47),(.pos 67)]),
   ((.exchange 53 31 2),[(.neg 53),(.neg 31),(.pos 51),(.pos 69)]),
   ((.exchange 53 32 2),[(.neg 53),(.neg 32),(.pos 52),(.pos 69)]),
   ((.exchange 53 35 5),[(.neg 53),(.neg 35),(.pos 40),(.pos 41)]),
   ((.exchange 53 45 4),[(.neg 53),(.neg 45),(.pos 46),(.pos 47)]),
   ((.exchange 53 56 4),[(.neg 56),(.neg 53),(.pos 46),(.pos 67)]),
   ((.exchange 53 57 4),[(.neg 57),(.neg 53),(.pos 47),(.pos 67)]),
   ((.exchange 54 1 3),[(.neg 54),(.neg 1),(.pos 51),(.pos 52),(.pos 53)]),
   ((.exchange 54 6 4),[(.neg 54),(.neg 6),(.pos 48),(.pos 49)]),
   ((.exchange 54 19 3),[(.neg 54),(.neg 19),(.pos 51),(.pos 52),(.pos 69)]),
   ((.exchange 54 23 5),[(.neg 54),(.neg 23),(.pos 43),(.pos 64)]),
   ((.exchange 54 28 4),[(.neg 54),(.neg 28),(.pos 48),(.pos 68)]),
   ((.exchange 54 29 4),[(.neg 54),(.neg 29),(.pos 49),(.pos 68)]),
   ((.exchange 54 36 4),[(.neg 54),(.neg 36),(.pos 48),(.pos 49)]),
   ((.exchange 54 39 5),[(.neg 54),(.neg 39),(.pos 42),(.pos 43)]),
   ((.exchange 54 45 4),[(.neg 54),(.neg 45),(.pos 48),(.pos 49)]),
   ((.exchange 54 55 5),[(.neg 55),(.neg 54),(.pos 42),(.pos 43),(.pos 64)]),
   ((.exchange 54 58 4),[(.neg 58),(.neg 54),(.pos 48),(.pos 68)]),
   ((.exchange 54 59 4),[(.neg 59),(.neg 54),(.pos 49),(.pos 68)]),
   ((.exchange 54 61 5),[(.neg 61),(.neg 54),(.pos 42),(.pos 64)]),
   ((.exchange 54 65 4),[(.neg 65),(.neg 54),(.pos 48),(.pos 68)]),
   ((.exchange 54 66 4),[(.neg 66),(.neg 54),(.pos 49),(.pos 68)]),
   ((.exchange 55 1 6),[(.neg 55),(.neg 1),(.pos 35),(.pos 39)]),
   ((.exchange 55 2 6),[(.neg 55),(.neg 2),(.pos 36),(.pos 39)]),
   ((.exchange 55 4 6),[(.neg 55),(.neg 4),(.pos 35),(.pos 36),(.pos 39)]),
   ((.exchange 55 18 0),[(.neg 55),(.neg 18),(.pos 57),(.pos 59)]),
   ((.exchange 55 20 1),[(.neg 55),(.neg 20),(.pos 56),(.pos 61)]),
   ((.exchange 55 21 0),[(.neg 55),(.neg 21),(.pos 57),(.pos 62)]),
   ((.exchange 55 23 0),[(.neg 55),(.neg 23),(.pos 59),(.pos 62)]),
   ((.exchange 55 26 1),[(.neg 55),(.neg 26),(.pos 56),(.pos 65)]),
   ((.exchange 55 27 0),[(.neg 55),(.neg 27),(.pos 57),(.pos 66)]),
   ((.exchange 55 28 1),[(.neg 55),(.neg 28),(.pos 58),(.pos 65)]),
   ((.exchange 55 29 0),[(.neg 55),(.neg 29),(.pos 59),(.pos 66)]),
   ((.exchange 55 32 0),[(.neg 55),(.neg 32),(.pos 62),(.pos 66)]),
   ((.exchange 55 37 1),[(.neg 55),(.neg 37),(.pos 56),(.pos 58)]),
   ((.exchange 55 38 0),[(.neg 55),(.neg 38),(.pos 57),(.pos 59)]),
   ((.exchange 55 40 1),[(.neg 55),(.neg 40),(.pos 56),(.pos 61)]),
   ((.exchange 55 40 6),[(.neg 55),(.neg 40),(.pos 35),(.pos 39)]),
   ((.exchange 55 41 0),[(.neg 55),(.neg 41),(.pos 57),(.pos 62)]),
   ((.exchange 55 42 1),[(.neg 55),(.neg 42),(.pos 58),(.pos 61)]),
   ((.exchange 55 46 1),[(.neg 55),(.neg 46),(.pos 56),(.pos 65)]),
   ((.exchange 55 48 1),[(.neg 55),(.neg 48),(.pos 58),(.pos 65)]),
   ((.exchange 55 51 1),[(.neg 55),(.neg 51),(.pos 61),(.pos 65)]),
   ((.exchange 55 52 0),[(.neg 55),(.neg 52),(.pos 62),(.pos 66)]),
   ((.exchange 55 69 0),[(.neg 69),(.neg 55),(.pos 62),(.pos 66)]),
   ((.exchange 56 5 6),[(.neg 56),(.neg 5),(.pos 35),(.pos 46)]),
   ((.exchange 56 7 6),[(.neg 56),(.neg 7),(.pos 37),(.pos 46)]),
   ((.exchange 56 10 6),[(.neg 56),(.neg 10),(.pos 40),(.pos 46)]),
   ((.exchange 56 16 2),[(.neg 56),(.neg 16),(.pos 55),(.pos 58)]),
   ((.exchange 56 18 0),[(.neg 56),(.neg 18),(.pos 57),(.pos 60)]),
   ((.exchange 56 19 2),[(.neg 56),(.neg 19),(.pos 55),(.pos 61)]),
   ((.exchange 56 21 0),[(.neg 56),(.neg 21),(.pos 57),(.pos 63)]),
   ((.exchange 56 24 0),[(.neg 56),(.neg 24),(.pos 60),(.pos 63)]),
   ((.exchange 56 25 2),[(.neg 56),(.neg 25),(.pos 55),(.pos 65)]),
   ((.exchange 56 27 0),[(.neg 56),(.neg 27),(.pos 57),(.pos 67)]),
   ((.exchange 56 28 2),[(.neg 56),(.neg 28),(.pos 58),(.pos 65)]),
   ((.exchange 56 30 0),[(.neg 56),(.neg 30),(.pos 60),(.pos 67)]),
   ((.exchange 56 31 2),[(.neg 56),(.neg 31),(.pos 61),(.pos 65)]),
   ((.exchange 56 33 0),[(.neg 56),(.neg 33),(.pos 63),(.pos 67)]),
   ((.exchange 56 36 2),[(.neg 56),(.neg 36),(.pos 55),(.pos 58)]),
   ((.exchange 56 38 0),[(.neg 56),(.neg 38),(.pos 57),(.pos 60)]),
   ((.exchange 56 39 2),[(.neg 56),(.neg 39),(.pos 55),(.pos 61)]),
   ((.exchange 56 41 0),[(.neg 56),(.neg 41),(.pos 57),(.pos 63)]),
   ((.exchange 56 42 2),[(.neg 56),(.neg 42),(.pos 58),(.pos 61)]),
   ((.exchange 56 43 6),[(.neg 56),(.neg 43),(.pos 35),(.pos 37),(.pos 40)]),
   ((.exchange 56 45 2),[(.neg 56),(.neg 45),(.pos 55),(.pos 65)]),
   ((.exchange 56 47 6),[(.neg 56),(.neg 47),(.pos 35),(.pos 46)]),
   ((.exchange 56 51 6),[(.neg 56),(.neg 51),(.pos 40),(.pos 46)]),
   ((.exchange 56 59 0),[(.neg 59),(.neg 56),(.pos 57),(.pos 60)])]

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



noncomputable def certificates_3 : List (Origin 70 1271 × List Sat.Literal) :=
  [((.exchange 56 64 2),[(.neg 64),(.neg 56),(.pos 58),(.pos 61)]),
   ((.exchange 56 66 0),[(.neg 66),(.neg 56),(.pos 57),(.pos 67)]),
   ((.exchange 57 1 6),[(.neg 57),(.neg 1),(.pos 35),(.pos 41)]),
   ((.exchange 57 3 6),[(.neg 57),(.neg 3),(.pos 35),(.pos 38),(.pos 41)]),
   ((.exchange 57 4 6),[(.neg 57),(.neg 4),(.pos 38),(.pos 41)]),
   ((.exchange 57 16 2),[(.neg 57),(.neg 16),(.pos 55),(.pos 59)]),
   ((.exchange 57 17 1),[(.neg 57),(.neg 17),(.pos 56),(.pos 60)]),
   ((.exchange 57 19 2),[(.neg 57),(.neg 19),(.pos 55),(.pos 62)]),
   ((.exchange 57 20 1),[(.neg 57),(.neg 20),(.pos 56),(.pos 63)]),
   ((.exchange 57 25 2),[(.neg 57),(.neg 25),(.pos 55),(.pos 66)]),
   ((.exchange 57 26 1),[(.neg 57),(.neg 26),(.pos 56),(.pos 67)]),
   ((.exchange 57 29 2),[(.neg 57),(.neg 29),(.pos 59),(.pos 66)]),
   ((.exchange 57 31 2),[(.neg 57),(.neg 31),(.pos 55),(.pos 62),(.pos 66)]),
   ((.exchange 57 32 2),[(.neg 57),(.neg 32),(.pos 62),(.pos 66)]),
   ((.exchange 57 39 6),[(.neg 57),(.neg 39),(.pos 35),(.pos 41)]),
   ((.exchange 57 40 1),[(.neg 57),(.neg 40),(.pos 56),(.pos 63)]),
   ((.exchange 57 45 2),[(.neg 57),(.neg 45),(.pos 55),(.pos 66)]),
   ((.exchange 57 46 1),[(.neg 57),(.neg 46),(.pos 56),(.pos 67)]),
   ((.exchange 57 53 1),[(.neg 57),(.neg 53),(.pos 63),(.pos 67)]),
   ((.exchange 57 58 1),[(.neg 58),(.neg 57),(.pos 56),(.pos 60)]),
   ((.exchange 57 58 2),[(.neg 58),(.neg 57),(.pos 55),(.pos 59)]),
   ((.exchange 57 61 1),[(.neg 61),(.neg 57),(.pos 56),(.pos 63)]),
   ((.exchange 57 61 2),[(.neg 61),(.neg 57),(.pos 55),(.pos 62)]),
   ((.exchange 57 64 2),[(.neg 64),(.neg 57),(.pos 59),(.pos 62)]),
   ((.exchange 57 65 2),[(.neg 65),(.neg 57),(.pos 55),(.pos 66)]),
   ((.exchange 58 2 6),[(.neg 58),(.neg 2),(.pos 36),(.pos 42)]),
   ((.exchange 58 3 6),[(.neg 58),(.neg 3),(.pos 37),(.pos 42)]),
   ((.exchange 58 4 6),[(.neg 58),(.neg 4),(.pos 36),(.pos 37),(.pos 42)]),
   ((.exchange 58 15 3),[(.neg 58),(.neg 15),(.pos 55),(.pos 56)]),
   ((.exchange 58 18 0),[(.neg 58),(.neg 18),(.pos 59),(.pos 60)]),
   ((.exchange 58 20 3),[(.neg 58),(.neg 20),(.pos 56),(.pos 61)]),
   ((.exchange 58 23 0),[(.neg 58),(.neg 23),(.pos 59),(.pos 64)]),
   ((.exchange 58 24 0),[(.neg 58),(.neg 24),(.pos 60),(.pos 64)]),
   ((.exchange 58 25 3),[(.neg 58),(.neg 25),(.pos 55),(.pos 65)]),
   ((.exchange 58 29 0),[(.neg 58),(.neg 29),(.pos 59),(.pos 68)]),
   ((.exchange 58 30 0),[(.neg 58),(.neg 30),(.pos 60),(.pos 68)]),
   ((.exchange 58 34 0),[(.neg 58),(.neg 34),(.pos 64),(.pos 68)]),
   ((.exchange 58 35 3),[(.neg 58),(.neg 35),(.pos 55),(.pos 56)]),
   ((.exchange 58 38 0),[(.neg 58),(.neg 38),(.pos 59),(.pos 60)]),
   ((.exchange 58 39 6),[(.neg 58),(.neg 39),(.pos 36),(.pos 42)]),
   ((.exchange 58 40 6),[(.neg 58),(.neg 40),(.pos 37),(.pos 42)]),
   ((.exchange 58 44 0),[(.neg 58),(.neg 44),(.pos 60),(.pos 64)]),
   ((.exchange 58 46 3),[(.neg 58),(.neg 46),(.pos 56),(.pos 65)]),
   ((.exchange 58 49 0),[(.neg 58),(.neg 49),(.pos 59),(.pos 68)]),
   ((.exchange 58 50 0),[(.neg 58),(.neg 50),(.pos 60),(.pos 68)]),
   ((.exchange 58 51 3),[(.neg 58),(.neg 51),(.pos 61),(.pos 65)]),
   ((.exchange 58 51 6),[(.neg 58),(.neg 51),(.pos 42),(.pos 48)]),
   ((.exchange 58 54 0),[(.neg 58),(.neg 54),(.pos 64),(.pos 68)]),
   ((.exchange 58 57 0),[(.neg 58),(.neg 57),(.pos 59),(.pos 60)]),
   ((.exchange 58 57 3),[(.neg 58),(.neg 57),(.pos 55),(.pos 56)]),
   ((.exchange 58 62 0),[(.neg 62),(.neg 58),(.pos 59),(.pos 64)]),
   ((.exchange 58 63 0),[(.neg 63),(.neg 58),(.pos 60),(.pos 64)]),
   ((.exchange 58 66 0),[(.neg 66),(.neg 58),(.pos 59),(.pos 68)]),
   ((.exchange 58 69 3),[(.neg 69),(.neg 58),(.pos 61),(.pos 65)]),
   ((.exchange 59 1 3),[(.neg 59),(.neg 1),(.pos 55),(.pos 57),(.pos 62)]),
   ((.exchange 59 4 6),[(.neg 59),(.neg 4),(.pos 38),(.pos 43)]),
   ((.exchange 59 7 6),[(.neg 59),(.neg 7),(.pos 36),(.pos 38),(.pos 49)]),
   ((.exchange 59 17 1),[(.neg 59),(.neg 17),(.pos 58),(.pos 60)]),
   ((.exchange 59 22 1),[(.neg 59),(.neg 22),(.pos 58),(.pos 64)]),
   ((.exchange 59 24 1),[(.neg 59),(.neg 24),(.pos 60),(.pos 64)]),
   ((.exchange 59 27 3),[(.neg 59),(.neg 27),(.pos 57),(.pos 66)]),
   ((.exchange 59 28 1),[(.neg 59),(.neg 28),(.pos 58),(.pos 68)]),
   ((.exchange 59 30 1),[(.neg 59),(.neg 30),(.pos 60),(.pos 68)]),
   ((.exchange 59 31 3),[(.neg 59),(.neg 31),(.pos 55),(.pos 62),(.pos 66)]),
   ((.exchange 59 34 1),[(.neg 59),(.neg 34),(.pos 64),(.pos 68)]),
   ((.exchange 59 35 3),[(.neg 59),(.neg 35),(.pos 55),(.pos 57)]),
   ((.exchange 59 37 1),[(.neg 59),(.neg 37),(.pos 58),(.pos 60)]),
   ((.exchange 59 42 1),[(.neg 59),(.neg 42),(.pos 58),(.pos 64)]),
   ((.exchange 59 42 6),[(.neg 59),(.neg 42),(.pos 36),(.pos 43)]),
   ((.exchange 59 44 6),[(.neg 59),(.neg 44),(.pos 38),(.pos 43)]),
   ((.exchange 59 46 1),[(.neg 59),(.neg 46),(.pos 58),(.pos 60),(.pos 68)]),
   ((.exchange 59 48 1),[(.neg 59),(.neg 48),(.pos 58),(.pos 68)]),
   ((.exchange 59 50 1),[(.neg 59),(.neg 50),(.pos 60),(.pos 68)]),
   ((.exchange 59 54 1),[(.neg 59),(.neg 54),(.pos 64),(.pos 68)]),
   ((.exchange 59 56 1),[(.neg 59),(.neg 56),(.pos 58),(.pos 60)]),
   ((.exchange 59 61 1),[(.neg 61),(.neg 59),(.pos 58),(.pos 64)]),
   ((.exchange 59 63 1),[(.neg 63),(.neg 59),(.pos 60),(.pos 64)]),
   ((.exchange 59 67 1),[(.neg 67),(.neg 59),(.pos 60),(.pos 68)]),
   ((.exchange 60 4 6),[(.neg 60),(.neg 4),(.pos 38),(.pos 44)]),
   ((.exchange 60 5 3),[(.neg 60),(.neg 5),(.pos 56),(.pos 57),(.pos 67)]),
   ((.exchange 60 15 3),[(.neg 60),(.neg 15),(.pos 56),(.pos 57)]),
   ((.exchange 60 19 2),[(.neg 60),(.neg 19),(.pos 58),(.pos 59),(.pos 64)]),
   ((.exchange 60 20 3),[(.neg 60),(.neg 20),(.pos 56),(.pos 63)]),
   ((.exchange 60 23 2),[(.neg 60),(.neg 23),(.pos 59),(.pos 64)]),
   ((.exchange 60 28 2),[(.neg 60),(.neg 28),(.pos 58),(.pos 68)]),
   ((.exchange 60 29 2),[(.neg 60),(.neg 29),(.pos 59),(.pos 68)]),
   ((.exchange 60 34 2),[(.neg 60),(.neg 34),(.pos 64),(.pos 68)]),
   ((.exchange 60 36 2),[(.neg 60),(.neg 36),(.pos 58),(.pos 59)]),
   ((.exchange 60 39 6),[(.neg 60),(.neg 39),(.pos 37),(.pos 38),(.pos 44)]),
   ((.exchange 60 40 6),[(.neg 60),(.neg 40),(.pos 37),(.pos 44)]),
   ((.exchange 60 42 2),[(.neg 60),(.neg 42),(.pos 58),(.pos 64)]),
   ((.exchange 60 43 2),[(.neg 60),(.neg 43),(.pos 59),(.pos 64)]),
   ((.exchange 60 47 6),[(.neg 60),(.neg 47),(.pos 38),(.pos 50)]),
   ((.exchange 60 48 2),[(.neg 60),(.neg 48),(.pos 58),(.pos 68)]),
   ((.exchange 60 55 2),[(.neg 60),(.neg 55),(.pos 58),(.pos 59)]),
   ((.exchange 60 55 3),[(.neg 60),(.neg 55),(.pos 56),(.pos 57)]),
   ((.exchange 60 61 2),[(.neg 61),(.neg 60),(.pos 58),(.pos 64)]),
   ((.exchange 60 62 2),[(.neg 62),(.neg 60),(.pos 59),(.pos 64)]),
   ((.exchange 60 65 2),[(.neg 65),(.neg 60),(.pos 58),(.pos 68)]),
   ((.exchange 60 65 3),[(.neg 65),(.neg 60),(.pos 56),(.pos 67)]),
   ((.exchange 60 66 2),[(.neg 66),(.neg 60),(.pos 59),(.pos 68)]),
   ((.exchange 61 2 6),[(.neg 61),(.neg 2),(.pos 39),(.pos 42)]),
   ((.exchange 61 3 6),[(.neg 61),(.neg 3),(.pos 40),(.pos 42)]),
   ((.exchange 61 12 6),[(.neg 61),(.neg 12),(.pos 42),(.pos 51)]),
   ((.exchange 61 15 4),[(.neg 61),(.neg 15),(.pos 55),(.pos 56)]),
   ((.exchange 61 21 0),[(.neg 61),(.neg 21),(.pos 62),(.pos 63)]),
   ((.exchange 61 23 0),[(.neg 61),(.neg 23),(.pos 62),(.pos 64)]),
   ((.exchange 61 24 0),[(.neg 61),(.neg 24),(.pos 63),(.pos 64)]),
   ((.exchange 61 26 4),[(.neg 61),(.neg 26),(.pos 56),(.pos 65)]),
   ((.exchange 61 28 4),[(.neg 61),(.neg 28),(.pos 58),(.pos 65)]),
   ((.exchange 61 32 0),[(.neg 61),(.neg 32),(.pos 62),(.pos 69)]),
   ((.exchange 61 33 0),[(.neg 61),(.neg 33),(.pos 63),(.pos 69)]),
   ((.exchange 61 34 0),[(.neg 61),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 61 35 4),[(.neg 61),(.neg 35),(.pos 55),(.pos 56)]),
   ((.exchange 61 38 0),[(.neg 61),(.neg 38),(.pos 62),(.pos 63),(.pos 64)]),
   ((.exchange 61 41 0),[(.neg 61),(.neg 41),(.pos 62),(.pos 63)]),
   ((.exchange 61 48 6),[(.neg 61),(.neg 48),(.pos 42),(.pos 51)]),
   ((.exchange 61 52 0),[(.neg 61),(.neg 52),(.pos 62),(.pos 69)]),
   ((.exchange 61 53 0),[(.neg 61),(.neg 53),(.pos 63),(.pos 69)]),
   ((.exchange 61 57 0),[(.neg 61),(.neg 57),(.pos 62),(.pos 63)]),
   ((.exchange 61 57 4),[(.neg 61),(.neg 57),(.pos 55),(.pos 56)]),
   ((.exchange 61 66 0),[(.neg 66),(.neg 61),(.pos 62),(.pos 69)]),
   ((.exchange 61 67 0),[(.neg 67),(.neg 61),(.pos 63),(.pos 69)]),
   ((.exchange 62 1 6),[(.neg 62),(.neg 1),(.pos 39),(.pos 41)]),
   ((.exchange 62 3 1),[(.neg 62),(.neg 3),(.pos 61),(.pos 63),(.pos 64)]),
   ((.exchange 62 11 6),[(.neg 62),(.neg 11),(.pos 41),(.pos 52)]),
   ((.exchange 62 15 4),[(.neg 62),(.neg 15),(.pos 55),(.pos 57)]),
   ((.exchange 62 16 4),[(.neg 62),(.neg 16),(.pos 55),(.pos 59)])]

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



noncomputable def certificates_4 : List (Origin 70 1271 × List Sat.Literal) :=
  [((.exchange 62 22 1),[(.neg 62),(.neg 22),(.pos 61),(.pos 64)]),
   ((.exchange 62 24 1),[(.neg 62),(.neg 24),(.pos 63),(.pos 64)]),
   ((.exchange 62 25 4),[(.neg 62),(.neg 25),(.pos 55),(.pos 66)]),
   ((.exchange 62 26 1),[(.neg 62),(.neg 26),(.pos 61),(.pos 63),(.pos 69)]),
   ((.exchange 62 27 4),[(.neg 62),(.neg 27),(.pos 57),(.pos 66)]),
   ((.exchange 62 29 4),[(.neg 62),(.neg 29),(.pos 59),(.pos 66)]),
   ((.exchange 62 31 1),[(.neg 62),(.neg 31),(.pos 61),(.pos 69)]),
   ((.exchange 62 38 6),[(.neg 62),(.neg 38),(.pos 41),(.pos 43)]),
   ((.exchange 62 40 1),[(.neg 62),(.neg 40),(.pos 61),(.pos 63)]),
   ((.exchange 62 42 1),[(.neg 62),(.neg 42),(.pos 61),(.pos 64)]),
   ((.exchange 62 44 1),[(.neg 62),(.neg 44),(.pos 63),(.pos 64)]),
   ((.exchange 62 47 6),[(.neg 62),(.neg 47),(.pos 41),(.pos 52)]),
   ((.exchange 62 51 1),[(.neg 62),(.neg 51),(.pos 61),(.pos 69)]),
   ((.exchange 62 53 1),[(.neg 62),(.neg 53),(.pos 63),(.pos 69)]),
   ((.exchange 62 56 1),[(.neg 62),(.neg 56),(.pos 61),(.pos 63)]),
   ((.exchange 62 56 4),[(.neg 62),(.neg 56),(.pos 55),(.pos 57)]),
   ((.exchange 62 60 1),[(.neg 62),(.neg 60),(.pos 63),(.pos 64)]),
   ((.exchange 62 67 1),[(.neg 67),(.neg 62),(.pos 63),(.pos 69)]),
   ((.exchange 62 68 4),[(.neg 68),(.neg 62),(.pos 59),(.pos 66)]),
   ((.exchange 63 1 6),[(.neg 63),(.neg 1),(.pos 40),(.pos 41)]),
   ((.exchange 63 4 6),[(.neg 63),(.neg 4),(.pos 41),(.pos 44)]),
   ((.exchange 63 18 4),[(.neg 63),(.neg 18),(.pos 57),(.pos 60)]),
   ((.exchange 63 19 2),[(.neg 63),(.neg 19),(.pos 61),(.pos 62)]),
   ((.exchange 63 23 2),[(.neg 63),(.neg 23),(.pos 62),(.pos 64)]),
   ((.exchange 63 25 4),[(.neg 63),(.neg 25),(.pos 56),(.pos 57),(.pos 67)]),
   ((.exchange 63 26 4),[(.neg 63),(.neg 26),(.pos 56),(.pos 67)]),
   ((.exchange 63 27 4),[(.neg 63),(.neg 27),(.pos 57),(.pos 67)]),
   ((.exchange 63 31 2),[(.neg 63),(.neg 31),(.pos 61),(.pos 69)]),
   ((.exchange 63 32 2),[(.neg 63),(.neg 32),(.pos 62),(.pos 69)]),
   ((.exchange 63 34 2),[(.neg 63),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 63 35 4),[(.neg 63),(.neg 35),(.pos 56),(.pos 57)]),
   ((.exchange 63 35 6),[(.neg 63),(.neg 35),(.pos 40),(.pos 41)]),
   ((.exchange 63 36 2),[(.neg 63),(.neg 36),(.pos 61),(.pos 62),(.pos 64)]),
   ((.exchange 63 37 4),[(.neg 63),(.neg 37),(.pos 56),(.pos 60)]),
   ((.exchange 63 39 2),[(.neg 63),(.neg 39),(.pos 61),(.pos 62)]),
   ((.exchange 63 42 2),[(.neg 63),(.neg 42),(.pos 61),(.pos 64)]),
   ((.exchange 63 43 2),[(.neg 63),(.neg 43),(.pos 62),(.pos 64)]),
   ((.exchange 63 46 4),[(.neg 63),(.neg 46),(.pos 56),(.pos 67)]),
   ((.exchange 63 50 4),[(.neg 63),(.neg 50),(.pos 60),(.pos 67)]),
   ((.exchange 63 52 2),[(.neg 63),(.neg 52),(.pos 62),(.pos 69)]),
   ((.exchange 63 52 6),[(.neg 63),(.neg 52),(.pos 41),(.pos 53)]),
   ((.exchange 63 55 2),[(.neg 63),(.neg 55),(.pos 61),(.pos 62)]),
   ((.exchange 63 58 2),[(.neg 63),(.neg 58),(.pos 61),(.pos 64)]),
   ((.exchange 63 58 4),[(.neg 63),(.neg 58),(.pos 56),(.pos 60)]),
   ((.exchange 63 65 2),[(.neg 65),(.neg 63),(.pos 61),(.pos 69)]),
   ((.exchange 63 65 4),[(.neg 65),(.neg 63),(.pos 56),(.pos 67)]),
   ((.exchange 64 2 6),[(.neg 64),(.neg 2),(.pos 42),(.pos 43)]),
   ((.exchange 64 10 6),[(.neg 64),(.neg 10),(.pos 42),(.pos 44),(.pos 54)]),
   ((.exchange 64 13 6),[(.neg 64),(.neg 13),(.pos 43),(.pos 54)]),
   ((.exchange 64 16 4),[(.neg 64),(.neg 16),(.pos 58),(.pos 59)]),
   ((.exchange 64 17 4),[(.neg 64),(.neg 17),(.pos 58),(.pos 60)]),
   ((.exchange 64 18 4),[(.neg 64),(.neg 18),(.pos 59),(.pos 60)]),
   ((.exchange 64 19 3),[(.neg 64),(.neg 19),(.pos 61),(.pos 62)]),
   ((.exchange 64 20 3),[(.neg 64),(.neg 20),(.pos 61),(.pos 63)]),
   ((.exchange 64 21 3),[(.neg 64),(.neg 21),(.pos 62),(.pos 63)]),
   ((.exchange 64 26 3),[(.neg 64),(.neg 26),(.pos 61),(.pos 63),(.pos 69)]),
   ((.exchange 64 28 4),[(.neg 64),(.neg 28),(.pos 58),(.pos 68)]),
   ((.exchange 64 29 4),[(.neg 64),(.neg 29),(.pos 59),(.pos 68)]),
   ((.exchange 64 31 3),[(.neg 64),(.neg 31),(.pos 61),(.pos 69)]),
   ((.exchange 64 36 4),[(.neg 64),(.neg 36),(.pos 58),(.pos 59)]),
   ((.exchange 64 37 4),[(.neg 64),(.neg 37),(.pos 58),(.pos 60)]),
   ((.exchange 64 40 6),[(.neg 64),(.neg 40),(.pos 42),(.pos 44)]),
   ((.exchange 64 41 3),[(.neg 64),(.neg 41),(.pos 62),(.pos 63)]),
   ((.exchange 64 46 4),[(.neg 64),(.neg 46),(.pos 58),(.pos 60),(.pos 68)]),
   ((.exchange 64 46 6),[(.neg 64),(.neg 46),(.pos 42),(.pos 44),(.pos 54)]),
   ((.exchange 64 47 3),[(.neg 64),(.neg 47),(.pos 62),(.pos 63),(.pos 69)]),
   ((.exchange 64 48 4),[(.neg 64),(.neg 48),(.pos 58),(.pos 68)]),
   ((.exchange 64 49 4),[(.neg 64),(.neg 49),(.pos 59),(.pos 68)]),
   ((.exchange 64 51 3),[(.neg 64),(.neg 51),(.pos 61),(.pos 69)]),
   ((.exchange 64 51 6),[(.neg 64),(.neg 51),(.pos 42),(.pos 54)]),
   ((.exchange 64 55 4),[(.neg 64),(.neg 55),(.pos 58),(.pos 59)]),
   ((.exchange 64 56 4),[(.neg 64),(.neg 56),(.pos 58),(.pos 60)]),
   ((.exchange 64 57 3),[(.neg 64),(.neg 57),(.pos 62),(.pos 63)]),
   ((.exchange 64 57 4),[(.neg 64),(.neg 57),(.pos 59),(.pos 60)]),
   ((.exchange 64 67 3),[(.neg 67),(.neg 64),(.pos 63),(.pos 69)]),
   ((.exchange 65 1 5),[(.neg 65),(.neg 1),(.pos 55),(.pos 56),(.pos 61)]),
   ((.exchange 65 4 6),[(.neg 65),(.neg 4),(.pos 45),(.pos 46),(.pos 48),(.pos 51)]),
   ((.exchange 65 5 6),[(.neg 65),(.neg 5),(.pos 45),(.pos 46)]),
   ((.exchange 65 7 6),[(.neg 65),(.neg 7),(.pos 46),(.pos 48)]),
   ((.exchange 65 10 6),[(.neg 65),(.neg 10),(.pos 46),(.pos 51)]),
   ((.exchange 65 27 0),[(.neg 65),(.neg 27),(.pos 66),(.pos 67)]),
   ((.exchange 65 29 0),[(.neg 65),(.neg 29),(.pos 66),(.pos 68)]),
   ((.exchange 65 30 0),[(.neg 65),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 65 32 0),[(.neg 65),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 65 33 0),[(.neg 65),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 65 34 0),[(.neg 65),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 65 37 5),[(.neg 65),(.neg 37),(.pos 56),(.pos 58)]),
   ((.exchange 65 37 6),[(.neg 65),(.neg 37),(.pos 46),(.pos 48)]),
   ((.exchange 65 38 5),[(.neg 65),(.neg 38),(.pos 55),(.pos 56),(.pos 58)]),
   ((.exchange 65 40 6),[(.neg 65),(.neg 40),(.pos 46),(.pos 51)]),
   ((.exchange 65 47 0),[(.neg 65),(.neg 47),(.pos 66),(.pos 67)]),
   ((.exchange 65 49 0),[(.neg 65),(.neg 49),(.pos 66),(.pos 68)]),
   ((.exchange 65 50 0),[(.neg 65),(.neg 50),(.pos 67),(.pos 68)]),
   ((.exchange 65 53 0),[(.neg 65),(.neg 53),(.pos 67),(.pos 69)]),
   ((.exchange 65 54 0),[(.neg 65),(.neg 54),(.pos 68),(.pos 69)]),
   ((.exchange 65 57 0),[(.neg 65),(.neg 57),(.pos 66),(.pos 67)]),
   ((.exchange 65 57 5),[(.neg 65),(.neg 57),(.pos 55),(.pos 56)]),
   ((.exchange 65 60 0),[(.neg 65),(.neg 60),(.pos 67),(.pos 68)]),
   ((.exchange 65 62 0),[(.neg 65),(.neg 62),(.pos 66),(.pos 69)]),
   ((.exchange 65 63 0),[(.neg 65),(.neg 63),(.pos 67),(.pos 69)]),
   ((.exchange 66 1 6),[(.neg 66),(.neg 1),(.pos 45),(.pos 47),(.pos 52)]),
   ((.exchange 66 10 6),[(.neg 66),(.neg 10),(.pos 45),(.pos 47),(.pos 52)]),
   ((.exchange 66 13 6),[(.neg 66),(.neg 13),(.pos 49),(.pos 52)]),
   ((.exchange 66 19 5),[(.neg 66),(.neg 19),(.pos 55),(.pos 62)]),
   ((.exchange 66 23 5),[(.neg 66),(.neg 23),(.pos 59),(.pos 62)]),
   ((.exchange 66 28 1),[(.neg 66),(.neg 28),(.pos 65),(.pos 68)]),
   ((.exchange 66 30 1),[(.neg 66),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 66 31 1),[(.neg 66),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 66 33 1),[(.neg 66),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 66 34 1),[(.neg 66),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 66 35 5),[(.neg 66),(.neg 35),(.pos 55),(.pos 57)]),
   ((.exchange 66 41 6),[(.neg 66),(.neg 41),(.pos 47),(.pos 52)]),
   ((.exchange 66 43 5),[(.neg 66),(.neg 43),(.pos 59),(.pos 62)]),
   ((.exchange 66 44 5),[(.neg 66),(.neg 44),(.pos 57),(.pos 59),(.pos 62)]),
   ((.exchange 66 46 1),[(.neg 66),(.neg 46),(.pos 65),(.pos 67)]),
   ((.exchange 66 48 1),[(.neg 66),(.neg 48),(.pos 65),(.pos 68)]),
   ((.exchange 66 50 1),[(.neg 66),(.neg 50),(.pos 67),(.pos 68)]),
   ((.exchange 66 53 1),[(.neg 66),(.neg 53),(.pos 67),(.pos 69)]),
   ((.exchange 66 54 1),[(.neg 66),(.neg 54),(.pos 68),(.pos 69)]),
   ((.exchange 66 54 6),[(.neg 66),(.neg 54),(.pos 49),(.pos 52)]),
   ((.exchange 66 56 1),[(.neg 66),(.neg 56),(.pos 65),(.pos 67)]),
   ((.exchange 66 56 5),[(.neg 66),(.neg 56),(.pos 55),(.pos 57)]),
   ((.exchange 66 58 1),[(.neg 66),(.neg 58),(.pos 65),(.pos 68)]),
   ((.exchange 66 63 1),[(.neg 66),(.neg 63),(.pos 67),(.pos 69)]),
   ((.exchange 67 10 6),[(.neg 67),(.neg 10),(.pos 46),(.pos 53)]),
   ((.exchange 67 12 6),[(.neg 67),(.neg 12),(.pos 46),(.pos 50),(.pos 53)]),
   ((.exchange 67 20 5),[(.neg 67),(.neg 20),(.pos 56),(.pos 63)]),
   ((.exchange 67 24 5),[(.neg 67),(.neg 24),(.pos 60),(.pos 63)])]

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



noncomputable def certificates_5 : List (Origin 70 1271 × List Sat.Literal) :=
  [((.exchange 67 25 2),[(.neg 67),(.neg 25),(.pos 65),(.pos 66)]),
   ((.exchange 67 29 2),[(.neg 67),(.neg 29),(.pos 66),(.pos 68)]),
   ((.exchange 67 31 2),[(.neg 67),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 67 32 2),[(.neg 67),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 67 35 5),[(.neg 67),(.neg 35),(.pos 56),(.pos 57)]),
   ((.exchange 67 35 6),[(.neg 67),(.neg 35),(.pos 46),(.pos 47)]),
   ((.exchange 67 36 6),[(.neg 67),(.neg 36),(.pos 46),(.pos 47),(.pos 50)]),
   ((.exchange 67 37 6),[(.neg 67),(.neg 37),(.pos 46),(.pos 50)]),
   ((.exchange 67 38 5),[(.neg 67),(.neg 38),(.pos 57),(.pos 60)]),
   ((.exchange 67 39 6),[(.neg 67),(.neg 39),(.pos 46),(.pos 47),(.pos 53)]),
   ((.exchange 67 40 5),[(.neg 67),(.neg 40),(.pos 56),(.pos 63)]),
   ((.exchange 67 40 6),[(.neg 67),(.neg 40),(.pos 46),(.pos 53)]),
   ((.exchange 67 42 6),[(.neg 67),(.neg 42),(.pos 46),(.pos 50),(.pos 53)]),
   ((.exchange 67 43 6),[(.neg 67),(.neg 43),(.pos 47),(.pos 50),(.pos 53)]),
   ((.exchange 67 44 5),[(.neg 67),(.neg 44),(.pos 60),(.pos 63)]),
   ((.exchange 67 49 2),[(.neg 67),(.neg 49),(.pos 66),(.pos 68)]),
   ((.exchange 67 51 6),[(.neg 67),(.neg 51),(.pos 46),(.pos 53)]),
   ((.exchange 67 54 2),[(.neg 67),(.neg 54),(.pos 68),(.pos 69)]),
   ((.exchange 67 55 2),[(.neg 67),(.neg 55),(.pos 65),(.pos 66)]),
   ((.exchange 67 58 2),[(.neg 67),(.neg 58),(.pos 65),(.pos 68)]),
   ((.exchange 67 58 5),[(.neg 67),(.neg 58),(.pos 56),(.pos 60)]),
   ((.exchange 67 59 2),[(.neg 67),(.neg 59),(.pos 66),(.pos 68)]),
   ((.exchange 67 61 2),[(.neg 67),(.neg 61),(.pos 65),(.pos 69)]),
   ((.exchange 67 62 2),[(.neg 67),(.neg 62),(.pos 66),(.pos 69)]),
   ((.exchange 67 64 2),[(.neg 67),(.neg 64),(.pos 68),(.pos 69)]),
   ((.exchange 68 3 6),[(.neg 68),(.neg 3),(.pos 48),(.pos 50),(.pos 54)]),
   ((.exchange 68 4 6),[(.neg 68),(.neg 4),(.pos 49),(.pos 50),(.pos 54)]),
   ((.exchange 68 6 6),[(.neg 68),(.neg 6),(.pos 48),(.pos 49)]),
   ((.exchange 68 10 6),[(.neg 68),(.neg 10),(.pos 48),(.pos 50),(.pos 54)]),
   ((.exchange 68 12 6),[(.neg 68),(.neg 12),(.pos 48),(.pos 54)]),
   ((.exchange 68 16 5),[(.neg 68),(.neg 16),(.pos 58),(.pos 59)]),
   ((.exchange 68 23 5),[(.neg 68),(.neg 23),(.pos 59),(.pos 64)]),
   ((.exchange 68 24 5),[(.neg 68),(.neg 24),(.pos 60),(.pos 64)]),
   ((.exchange 68 25 3),[(.neg 68),(.neg 25),(.pos 65),(.pos 66)]),
   ((.exchange 68 26 3),[(.neg 68),(.neg 26),(.pos 65),(.pos 67)]),
   ((.exchange 68 27 3),[(.neg 68),(.neg 27),(.pos 66),(.pos 67)]),
   ((.exchange 68 32 3),[(.neg 68),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 68 36 5),[(.neg 68),(.neg 36),(.pos 58),(.pos 59)]),
   ((.exchange 68 37 5),[(.neg 68),(.neg 37),(.pos 58),(.pos 60)]),
   ((.exchange 68 38 5),[(.neg 68),(.neg 38),(.pos 59),(.pos 60)]),
   ((.exchange 68 39 3),[(.neg 68),(.neg 39),(.pos 65),(.pos 66),(.pos 69)]),
   ((.exchange 68 39 5),[(.neg 68),(.neg 39),(.pos 58),(.pos 59),(.pos 64)]),
   ((.exchange 68 40 5),[(.neg 68),(.neg 40),(.pos 58),(.pos 60),(.pos 64)]),
   ((.exchange 68 41 6),[(.neg 68),(.neg 41),(.pos 49),(.pos 50),(.pos 54)]),
   ((.exchange 68 42 5),[(.neg 68),(.neg 42),(.pos 58),(.pos 64)]),
   ((.exchange 68 43 5),[(.neg 68),(.neg 43),(.pos 59),(.pos 64)]),
   ((.exchange 68 43 6),[(.neg 68),(.neg 43),(.pos 49),(.pos 54)]),
   ((.exchange 68 45 3),[(.neg 68),(.neg 45),(.pos 65),(.pos 66)]),
   ((.exchange 68 45 6),[(.neg 68),(.neg 45),(.pos 48),(.pos 49)]),
   ((.exchange 68 46 6),[(.neg 68),(.neg 46),(.pos 48),(.pos 50)]),
   ((.exchange 68 47 3),[(.neg 68),(.neg 47),(.pos 66),(.pos 67)]),
   ((.exchange 68 47 6),[(.neg 68),(.neg 47),(.pos 49),(.pos 50)]),
   ((.exchange 68 51 3),[(.neg 68),(.neg 51),(.pos 65),(.pos 69)]),
   ((.exchange 68 51 6),[(.neg 68),(.neg 51),(.pos 48),(.pos 54)]),
   ((.exchange 68 52 3),[(.neg 68),(.neg 52),(.pos 66),(.pos 69)]),
   ((.exchange 68 53 3),[(.neg 68),(.neg 53),(.pos 67),(.pos 69)]),
   ((.exchange 68 55 3),[(.neg 68),(.neg 55),(.pos 65),(.pos 66)]),
   ((.exchange 68 55 5),[(.neg 68),(.neg 55),(.pos 58),(.pos 59)]),
   ((.exchange 68 56 3),[(.neg 68),(.neg 56),(.pos 65),(.pos 67)]),
   ((.exchange 68 56 5),[(.neg 68),(.neg 56),(.pos 58),(.pos 60)]),
   ((.exchange 68 57 3),[(.neg 68),(.neg 57),(.pos 66),(.pos 67)]),
   ((.exchange 68 61 3),[(.neg 68),(.neg 61),(.pos 65),(.pos 69)]),
   ((.exchange 68 61 5),[(.neg 68),(.neg 61),(.pos 58),(.pos 64)]),
   ((.exchange 68 62 3),[(.neg 68),(.neg 62),(.pos 66),(.pos 69)]),
   ((.exchange 68 63 3),[(.neg 68),(.neg 63),(.pos 67),(.pos 69)]),
   ((.exchange 68 63 5),[(.neg 68),(.neg 63),(.pos 60),(.pos 64)]),
   ((.exchange 69 1 6),[(.neg 69),(.neg 1),(.pos 51),(.pos 52),(.pos 53)]),
   ((.exchange 69 8 4),[(.neg 69),(.neg 8),(.pos 66),(.pos 67),(.pos 68)]),
   ((.exchange 69 19 5),[(.neg 69),(.neg 19),(.pos 61),(.pos 62)]),
   ((.exchange 69 20 5),[(.neg 69),(.neg 20),(.pos 61),(.pos 63)]),
   ((.exchange 69 22 5),[(.neg 69),(.neg 22),(.pos 61),(.pos 64)]),
   ((.exchange 69 23 5),[(.neg 69),(.neg 23),(.pos 62),(.pos 64)]),
   ((.exchange 69 25 4),[(.neg 69),(.neg 25),(.pos 65),(.pos 66)]),
   ((.exchange 69 26 4),[(.neg 69),(.neg 26),(.pos 65),(.pos 67)]),
   ((.exchange 69 27 4),[(.neg 69),(.neg 27),(.pos 66),(.pos 67)]),
   ((.exchange 69 28 4),[(.neg 69),(.neg 28),(.pos 65),(.pos 68)]),
   ((.exchange 69 29 4),[(.neg 69),(.neg 29),(.pos 66),(.pos 68)]),
   ((.exchange 69 30 4),[(.neg 69),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 69 39 5),[(.neg 69),(.neg 39),(.pos 61),(.pos 62)]),
   ((.exchange 69 40 5),[(.neg 69),(.neg 40),(.pos 61),(.pos 63)]),
   ((.exchange 69 41 5),[(.neg 69),(.neg 41),(.pos 62),(.pos 63)]),
   ((.exchange 69 41 6),[(.neg 69),(.neg 41),(.pos 52),(.pos 53)]),
   ((.exchange 69 42 5),[(.neg 69),(.neg 42),(.pos 61),(.pos 64)]),
   ((.exchange 69 43 6),[(.neg 69),(.neg 43),(.pos 52),(.pos 54)]),
   ((.exchange 69 45 4),[(.neg 69),(.neg 45),(.pos 65),(.pos 66)]),
   ((.exchange 69 46 4),[(.neg 69),(.neg 46),(.pos 65),(.pos 67)]),
   ((.exchange 69 49 4),[(.neg 69),(.neg 49),(.pos 66),(.pos 68)]),
   ((.exchange 69 50 4),[(.neg 69),(.neg 50),(.pos 67),(.pos 68)]),
   ((.exchange 69 55 4),[(.neg 69),(.neg 55),(.pos 65),(.pos 66)]),
   ((.exchange 69 56 4),[(.neg 69),(.neg 56),(.pos 65),(.pos 67)]),
   ((.exchange 69 57 5),[(.neg 69),(.neg 57),(.pos 62),(.pos 63)]),
   ((.exchange 69 58 4),[(.neg 69),(.neg 58),(.pos 65),(.pos 68)]),
   ((.exchange 69 60 4),[(.neg 69),(.neg 60),(.pos 67),(.pos 68)]),
   (.newPoint,[(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 0),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 57),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 47),(.neg 44),(.neg 43),(.neg 41),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 42),(.pos 45),(.pos 46),(.pos 48),(.pos 51),(.pos 52),(.pos 55),(.pos 56),(.pos 58),(.pos 61),(.pos 65)]),
   ((.excluded 1),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 58),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 48),(.neg 46),(.neg 44),(.neg 42),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 41),(.pos 43),(.pos 45),(.pos 47),(.pos 49),(.pos 51),(.pos 52),(.pos 55),(.pos 57),(.pos 59),(.pos 62),(.pos 66)]),
   ((.excluded 2),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 69)]),
   ((.excluded 3),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 63),(.pos 68)]),
   ((.excluded 4),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 63)]),
   ((.excluded 5),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 68)]),
   ((.excluded 6),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 64),(.pos 67)]),
   ((.excluded 7),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 64)]),
   ((.excluded 8),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 55),(.pos 67)]),
   ((.excluded 9),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 55)]),
   ((.excluded 10),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 55),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 45),(.neg 43),(.neg 42),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 40),(.pos 41),(.pos 44),(.pos 46),(.pos 47),(.pos 50),(.pos 53),(.pos 54),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 11),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 57),(.neg 56),(.neg 55),(.neg 52),(.neg 51),(.neg 47),(.neg 46),(.neg 45),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 42),(.pos 43),(.pos 44),(.pos 48),(.pos 49),(.pos 50),(.pos 53),(.pos 54),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 68)]),
   ((.excluded 12),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 44),(.pos 50),(.pos 53),(.pos 54),(.pos 60),(.pos 61),(.pos 66)]),
   ((.excluded 13),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 44),(.pos 50),(.pos 53),(.pos 54),(.pos 60),(.pos 61)]),
   ((.excluded 14),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 44),(.pos 50),(.pos 53),(.pos 54),(.pos 60),(.pos 66)]),
   ((.excluded 15),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 44),(.pos 50),(.pos 53),(.pos 54),(.pos 60),(.pos 62),(.pos 65)]),
   ((.excluded 16),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 44),(.pos 50),(.pos 53),(.pos 54),(.pos 60),(.pos 62)]),
   ((.excluded 17),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 44),(.pos 50),(.pos 53),(.pos 54),(.pos 60),(.pos 65)]),
   ((.excluded 18),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 44),(.pos 50),(.pos 53),(.pos 54),(.pos 60)]),
   ((.excluded 19),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 40),(.pos 43),(.pos 46),(.pos 49),(.pos 56),(.pos 59),(.pos 69)]),
   ((.excluded 20),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 40),(.pos 43),(.pos 46),(.pos 49),(.pos 56),(.pos 59)]),
   ((.excluded 21),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 40),(.pos 46),(.pos 56),(.pos 69)]),
   ((.excluded 22),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 40),(.pos 46),(.pos 56),(.pos 62),(.pos 68)]),
   ((.excluded 23),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 40),(.pos 46),(.pos 56),(.pos 62)]),
   ((.excluded 24),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 40),(.pos 46),(.pos 56),(.pos 68)]),
   ((.excluded 25),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 40),(.pos 46),(.pos 56),(.pos 64),(.pos 66)]),
   ((.excluded 26),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 40),(.pos 46),(.pos 56),(.pos 64)]),
   ((.excluded 27),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 40),(.pos 46),(.pos 56),(.pos 66)]),
   ((.excluded 28),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 40),(.pos 46),(.pos 56)]),
   ((.excluded 29),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 43),(.pos 49),(.pos 59),(.pos 69)]),
   ((.excluded 30),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 43),(.pos 49),(.pos 59),(.pos 61),(.pos 67)]),
   ((.excluded 31),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 43),(.pos 49),(.pos 59),(.pos 61)]),
   ((.excluded 32),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 43),(.pos 49),(.pos 59),(.pos 67)]),
   ((.excluded 33),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 43),(.pos 49),(.pos 59),(.pos 63),(.pos 65)])]

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



end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C76

end
end
end BundlePart1

