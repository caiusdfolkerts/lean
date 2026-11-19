module
public import SemanticParts.Batch10P01Data
public import Consolidated.SemanticData
public import Mathlib.Data.Fin.Tuple.Basic
public import MatroidCatalogue.Definitions
public import MatroidChecked.BitsetSemanticChecks
public import MatroidChecked.FastSemanticChecks
public import MatroidChecked.BitsetOrigins
public import MatroidChecked.MaskOrigins

section BundlePart1
/- Source: MatroidChecked/SemanticChunks/Cases18Part00.lean -/




@[expose] public section
noncomputable section

/- Source: MatroidCatalogue/Cases/N8R4C71Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C71


noncomputable def certificates_0 : List (Origin 70 426 × List Sat.Literal) :=
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
   ((.fixed 20),[(.neg 20)]),
   ((.fixed 21),[(.pos 21)]),
   ((.fixed 22),[(.pos 22)]),
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
   ((.fixed 33),[(.pos 33)]),
   ((.fixed 34),[(.pos 34)]),
   ((.exchange 1 36 4),[(.neg 36),(.neg 1),(.pos 0),(.pos 35)]),
   ((.exchange 1 37 4),[(.neg 37),(.neg 1),(.pos 0),(.pos 35)]),
   ((.exchange 1 38 4),[(.neg 38),(.neg 1),(.pos 0),(.pos 35)]),
   ((.exchange 1 45 2),[(.neg 45),(.neg 1),(.pos 9),(.pos 39)]),
   ((.exchange 1 51 2),[(.neg 51),(.neg 1),(.pos 9),(.pos 39)]),
   ((.exchange 1 52 2),[(.neg 52),(.neg 1),(.pos 9),(.pos 39)]),
   ((.exchange 1 56 1),[(.neg 56),(.neg 1),(.pos 20),(.pos 40)]),
   ((.exchange 1 61 1),[(.neg 61),(.neg 1),(.pos 20),(.pos 40)]),
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
   ((.exchange 6 59 0),[(.neg 59),(.neg 6),(.pos 29),(.pos 49)]),
   ((.exchange 6 66 0),[(.neg 66),(.neg 6),(.pos 29),(.pos 49)]),
   ((.exchange 6 68 0),[(.neg 68),(.neg 6),(.pos 29),(.pos 49)]),
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
   ((.exchange 15 40 1),[(.neg 40),(.neg 15),(.pos 20),(.pos 56)]),
   ((.exchange 15 61 1),[(.neg 61),(.neg 15),(.pos 20),(.pos 56)]),
   ((.exchange 15 63 1),[(.neg 63),(.neg 15),(.pos 20),(.pos 56)]),
   ((.exchange 16 49 0),[(.neg 49),(.neg 16),(.pos 29),(.pos 59)]),
   ((.exchange 16 66 0),[(.neg 66),(.neg 16),(.pos 29),(.pos 59)]),
   ((.exchange 16 68 0),[(.neg 68),(.neg 16),(.pos 29),(.pos 59)]),
   ((.exchange 19 40 1),[(.neg 40),(.neg 19),(.pos 20),(.pos 61)]),
   ((.exchange 19 56 1),[(.neg 56),(.neg 19),(.pos 20),(.pos 61)]),
   ((.exchange 19 63 1),[(.neg 63),(.neg 19),(.pos 20),(.pos 61)]),
   ((.exchange 21 56 1),[(.neg 56),(.neg 21),(.pos 20),(.pos 63)]),
   ((.exchange 21 61 1),[(.neg 61),(.neg 21),(.pos 20),(.pos 63)]),
   ((.exchange 25 49 0),[(.neg 49),(.neg 25),(.pos 29),(.pos 66)]),
   ((.exchange 25 59 0),[(.neg 59),(.neg 25),(.pos 29),(.pos 66)]),
   ((.exchange 25 68 0),[(.neg 68),(.neg 25),(.pos 29),(.pos 66)]),
   ((.exchange 28 49 0),[(.neg 49),(.neg 28),(.pos 29),(.pos 68)]),
   ((.exchange 28 59 0),[(.neg 59),(.neg 28),(.pos 29),(.pos 68)]),
   ((.exchange 28 66 0),[(.neg 66),(.neg 28),(.pos 29),(.pos 68)]),
   ((.exchange 35 11 0),[(.neg 35),(.neg 11),(.pos 41),(.pos 47)]),
   ((.exchange 35 19 2),[(.neg 35),(.neg 19),(.pos 39),(.pos 55)]),
   ((.exchange 35 21 0),[(.neg 35),(.neg 21),(.pos 41),(.pos 57)]),
   ((.exchange 35 25 2),[(.neg 35),(.neg 25),(.pos 45),(.pos 55)]),
   ((.exchange 35 26 1),[(.neg 35),(.neg 26),(.pos 46),(.pos 56)]),
   ((.exchange 35 27 0),[(.neg 35),(.neg 27),(.pos 47),(.pos 57)]),
   ((.exchange 35 65 1),[(.neg 65),(.neg 35),(.pos 46),(.pos 56)]),
   ((.exchange 35 65 2),[(.neg 65),(.neg 35),(.pos 45),(.pos 55)]),
   ((.exchange 36 13 0),[(.neg 36),(.neg 13),(.pos 43),(.pos 49)]),
   ((.exchange 36 19 3),[(.neg 36),(.neg 19),(.pos 39),(.pos 55)]),
   ((.exchange 36 22 1),[(.neg 36),(.neg 22),(.pos 42),(.pos 58)]),
   ((.exchange 36 23 0),[(.neg 36),(.neg 23),(.pos 43),(.pos 59)]),
   ((.exchange 36 25 3),[(.neg 36),(.neg 25),(.pos 45),(.pos 55)]),
   ((.exchange 36 28 1),[(.neg 36),(.neg 28),(.pos 48),(.pos 58)]),
   ((.exchange 36 52 0),[(.neg 52),(.neg 36),(.pos 43),(.pos 49)]),
   ((.exchange 36 65 1),[(.neg 65),(.neg 36),(.pos 48),(.pos 58)]),
   ((.exchange 36 69 0),[(.neg 69),(.neg 36),(.pos 43),(.pos 49),(.pos 59)]),
   ((.exchange 37 12 2),[(.neg 37),(.neg 12),(.pos 42),(.pos 48)]),
   ((.exchange 37 22 2),[(.neg 37),(.neg 22),(.pos 42),(.pos 58)]),
   ((.exchange 37 24 0),[(.neg 37),(.neg 24),(.pos 44),(.pos 60)]),
   ((.exchange 37 26 3),[(.neg 37),(.neg 26),(.pos 46),(.pos 56)]),
   ((.exchange 37 28 2),[(.neg 37),(.neg 28),(.pos 48),(.pos 58)]),
   ((.exchange 37 34 0),[(.neg 37),(.neg 34),(.pos 44),(.pos 50),(.pos 60)]),
   ((.exchange 37 64 0),[(.neg 64),(.neg 37),(.pos 44),(.pos 60)]),
   ((.exchange 37 65 3),[(.neg 65),(.neg 37),(.pos 46),(.pos 56)]),
   ((.exchange 38 23 2),[(.neg 38),(.neg 23),(.pos 43),(.pos 59)]),
   ((.exchange 38 27 3),[(.neg 38),(.neg 27),(.pos 47),(.pos 57)]),
   ((.exchange 38 34 1),[(.neg 38),(.neg 34),(.pos 44),(.pos 50),(.pos 60)]),
   ((.exchange 38 52 2),[(.neg 52),(.neg 38),(.pos 43),(.pos 49)]),
   ((.exchange 38 63 1),[(.neg 63),(.neg 38),(.pos 44),(.pos 60)]),
   ((.exchange 38 68 1),[(.neg 68),(.neg 38),(.pos 50),(.pos 60)]),
   ((.exchange 38 69 2),[(.neg 69),(.neg 38),(.pos 43),(.pos 49),(.pos 59)]),
   ((.exchange 39 3 1),[(.neg 39),(.neg 3),(.pos 40),(.pos 42)]),
   ((.exchange 39 4 0),[(.neg 39),(.neg 4),(.pos 41),(.pos 43)]),
   ((.exchange 39 15 4),[(.neg 39),(.neg 15),(.pos 35),(.pos 55)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.MaskOrigins.maskOrigins_sound (grid := (fun i : Fin 70 => N8R4.gridMasks.get i.val))
  have hchecks : ∀ i : Fin 128,
    Papers.RationalityTen.MatroidChecked.MaskOrigins.MaskOrigin (fun i : Fin 70 => N8R4.gridMasks.get i.val) (7 : Fin 8) old newIndex models
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



noncomputable def certificates_1 : List (Origin 70 426 × List Sat.Literal) :=
  [((.exchange 39 17 4),[(.neg 39),(.neg 17),(.pos 35),(.pos 36),(.pos 55)]),
   ((.exchange 39 21 0),[(.neg 39),(.neg 21),(.pos 41),(.pos 62)]),
   ((.exchange 39 23 0),[(.neg 39),(.neg 23),(.pos 43),(.pos 62)]),
   ((.exchange 39 57 0),[(.neg 57),(.neg 39),(.pos 41),(.pos 62)]),
   ((.exchange 39 58 1),[(.neg 58),(.neg 39),(.pos 42),(.pos 61)]),
   ((.exchange 39 59 0),[(.neg 59),(.neg 39),(.pos 43),(.pos 62)]),
   ((.exchange 39 63 0),[(.neg 63),(.neg 39),(.pos 41),(.pos 62)]),
   ((.exchange 40 2 2),[(.neg 40),(.neg 2),(.pos 39),(.pos 42)]),
   ((.exchange 40 4 0),[(.neg 40),(.neg 4),(.pos 41),(.pos 44)]),
   ((.exchange 40 5 4),[(.neg 40),(.neg 5),(.pos 35),(.pos 46)]),
   ((.exchange 40 7 4),[(.neg 40),(.neg 7),(.pos 37),(.pos 46)]),
   ((.exchange 40 11 0),[(.neg 40),(.neg 11),(.pos 41),(.pos 53)]),
   ((.exchange 40 12 2),[(.neg 40),(.neg 12),(.pos 42),(.pos 51)]),
   ((.exchange 40 50 4),[(.neg 50),(.neg 40),(.pos 37),(.pos 46)]),
   ((.exchange 41 2 2),[(.neg 41),(.neg 2),(.pos 39),(.pos 43)]),
   ((.exchange 41 3 1),[(.neg 41),(.neg 3),(.pos 40),(.pos 44)]),
   ((.exchange 41 5 4),[(.neg 41),(.neg 5),(.pos 35),(.pos 47)]),
   ((.exchange 41 10 1),[(.neg 41),(.neg 10),(.pos 40),(.pos 53)]),
   ((.exchange 41 13 2),[(.neg 41),(.neg 13),(.pos 43),(.pos 52)]),
   ((.exchange 41 15 4),[(.neg 41),(.neg 15),(.pos 35),(.pos 57)]),
   ((.exchange 41 19 2),[(.neg 41),(.neg 19),(.pos 39),(.pos 62)]),
   ((.exchange 41 32 2),[(.neg 41),(.neg 32),(.pos 52),(.pos 62)]),
   ((.exchange 41 58 1),[(.neg 58),(.neg 41),(.pos 40),(.pos 44),(.pos 63)]),
   ((.exchange 41 59 2),[(.neg 59),(.neg 41),(.pos 43),(.pos 62)]),
   ((.exchange 41 65 1),[(.neg 65),(.neg 41),(.pos 40),(.pos 53),(.pos 63)]),
   ((.exchange 42 4 0),[(.neg 42),(.neg 4),(.pos 43),(.pos 44)]),
   ((.exchange 42 7 4),[(.neg 42),(.neg 7),(.pos 37),(.pos 48)]),
   ((.exchange 42 10 3),[(.neg 42),(.neg 10),(.pos 40),(.pos 51)]),
   ((.exchange 42 16 4),[(.neg 42),(.neg 16),(.pos 36),(.pos 58)]),
   ((.exchange 42 17 4),[(.neg 42),(.neg 17),(.pos 37),(.pos 58)]),
   ((.exchange 42 21 3),[(.neg 42),(.neg 21),(.pos 39),(.pos 40),(.pos 61)]),
   ((.exchange 42 23 0),[(.neg 42),(.neg 23),(.pos 43),(.pos 64)]),
   ((.exchange 42 24 0),[(.neg 42),(.neg 24),(.pos 44),(.pos 64)]),
   ((.exchange 42 28 4),[(.neg 42),(.neg 28),(.pos 48),(.pos 58)]),
   ((.exchange 42 38 0),[(.neg 42),(.neg 38),(.pos 43),(.pos 44)]),
   ((.exchange 42 41 3),[(.neg 42),(.neg 41),(.pos 39),(.pos 40)]),
   ((.exchange 42 46 3),[(.neg 46),(.neg 42),(.pos 40),(.pos 51)]),
   ((.exchange 42 46 4),[(.neg 46),(.neg 42),(.pos 37),(.pos 48)]),
   ((.exchange 42 49 0),[(.neg 49),(.neg 42),(.pos 43),(.pos 54)]),
   ((.exchange 42 52 0),[(.neg 52),(.neg 42),(.pos 43),(.pos 54)]),
   ((.exchange 42 55 4),[(.neg 55),(.neg 42),(.pos 36),(.pos 58)]),
   ((.exchange 42 56 4),[(.neg 56),(.neg 42),(.pos 37),(.pos 58)]),
   ((.exchange 42 59 0),[(.neg 59),(.neg 42),(.pos 43),(.pos 64)]),
   ((.exchange 42 60 0),[(.neg 60),(.neg 42),(.pos 44),(.pos 64)]),
   ((.exchange 42 62 0),[(.neg 62),(.neg 42),(.pos 43),(.pos 64)]),
   ((.exchange 42 63 0),[(.neg 63),(.neg 42),(.pos 44),(.pos 64)]),
   ((.exchange 42 69 0),[(.neg 69),(.neg 42),(.pos 54),(.pos 64)]),
   ((.exchange 43 1 3),[(.neg 43),(.neg 1),(.pos 39),(.pos 41)]),
   ((.exchange 43 3 1),[(.neg 43),(.neg 3),(.pos 42),(.pos 44)]),
   ((.exchange 43 6 4),[(.neg 43),(.neg 6),(.pos 36),(.pos 49)]),
   ((.exchange 43 7 4),[(.neg 43),(.neg 7),(.pos 36),(.pos 38),(.pos 49)]),
   ((.exchange 43 12 1),[(.neg 43),(.neg 12),(.pos 42),(.pos 54)]),
   ((.exchange 43 15 4),[(.neg 43),(.neg 15),(.pos 36),(.pos 38),(.pos 59)]),
   ((.exchange 43 16 4),[(.neg 43),(.neg 16),(.pos 36),(.pos 59)]),
   ((.exchange 43 17 4),[(.neg 43),(.neg 17),(.pos 36),(.pos 38),(.pos 59)]),
   ((.exchange 43 22 1),[(.neg 43),(.neg 22),(.pos 42),(.pos 64)]),
   ((.exchange 43 31 1),[(.neg 43),(.neg 31),(.pos 42),(.pos 54),(.pos 64)]),
   ((.exchange 43 34 1),[(.neg 43),(.neg 34),(.pos 54),(.pos 64)]),
   ((.exchange 43 40 1),[(.neg 43),(.neg 40),(.pos 42),(.pos 44)]),
   ((.exchange 43 45 4),[(.neg 45),(.neg 43),(.pos 36),(.pos 49)]),
   ((.exchange 43 46 3),[(.neg 46),(.neg 43),(.pos 39),(.pos 41),(.pos 52)]),
   ((.exchange 43 46 4),[(.neg 46),(.neg 43),(.pos 36),(.pos 38),(.pos 49)]),
   ((.exchange 43 47 4),[(.neg 47),(.neg 43),(.pos 38),(.pos 49)]),
   ((.exchange 44 1 3),[(.neg 44),(.neg 1),(.pos 40),(.pos 41)]),
   ((.exchange 44 2 2),[(.neg 44),(.neg 2),(.pos 42),(.pos 43)]),
   ((.exchange 44 17 4),[(.neg 44),(.neg 17),(.pos 37),(.pos 60)]),
   ((.exchange 44 18 4),[(.neg 44),(.neg 18),(.pos 38),(.pos 60)]),
   ((.exchange 44 22 2),[(.neg 44),(.neg 22),(.pos 42),(.pos 64)]),
   ((.exchange 44 23 2),[(.neg 44),(.neg 23),(.pos 43),(.pos 64)]),
   ((.exchange 44 39 2),[(.neg 44),(.neg 39),(.pos 42),(.pos 43)]),
   ((.exchange 44 39 3),[(.neg 44),(.neg 39),(.pos 40),(.pos 41)]),
   ((.exchange 44 55 4),[(.neg 55),(.neg 44),(.pos 37),(.pos 38),(.pos 60)]),
   ((.exchange 44 58 2),[(.neg 58),(.neg 44),(.pos 42),(.pos 64)]),
   ((.exchange 44 61 2),[(.neg 61),(.neg 44),(.pos 42),(.pos 64)]),
   ((.exchange 45 15 5),[(.neg 45),(.neg 15),(.pos 35),(.pos 55)]),
   ((.exchange 45 16 5),[(.neg 45),(.neg 16),(.pos 36),(.pos 55)]),
   ((.exchange 45 18 0),[(.neg 45),(.neg 18),(.pos 47),(.pos 49),(.pos 66)]),
   ((.exchange 45 18 5),[(.neg 45),(.neg 18),(.pos 35),(.pos 36),(.pos 55)]),
   ((.exchange 45 26 1),[(.neg 45),(.neg 26),(.pos 46),(.pos 65)]),
   ((.exchange 45 27 0),[(.neg 45),(.neg 27),(.pos 47),(.pos 66)]),
   ((.exchange 45 28 1),[(.neg 45),(.neg 28),(.pos 48),(.pos 65)]),
   ((.exchange 45 38 0),[(.neg 45),(.neg 38),(.pos 47),(.pos 49)]),
   ((.exchange 45 50 0),[(.neg 50),(.neg 45),(.pos 47),(.pos 49)]),
   ((.exchange 45 56 1),[(.neg 56),(.neg 45),(.pos 46),(.pos 65)]),
   ((.exchange 45 57 0),[(.neg 57),(.neg 45),(.pos 47),(.pos 66)]),
   ((.exchange 45 60 0),[(.neg 60),(.neg 45),(.pos 47),(.pos 49),(.pos 66)]),
   ((.exchange 46 2 2),[(.neg 46),(.neg 2),(.pos 45),(.pos 48),(.pos 51)]),
   ((.exchange 46 8 0),[(.neg 46),(.neg 8),(.pos 47),(.pos 50)]),
   ((.exchange 46 11 0),[(.neg 46),(.neg 11),(.pos 47),(.pos 53)]),
   ((.exchange 46 13 0),[(.neg 46),(.neg 13),(.pos 47),(.pos 50),(.pos 53)]),
   ((.exchange 46 15 5),[(.neg 46),(.neg 15),(.pos 35),(.pos 56)]),
   ((.exchange 46 17 5),[(.neg 46),(.neg 17),(.pos 37),(.pos 56)]),
   ((.exchange 46 24 0),[(.neg 46),(.neg 24),(.pos 50),(.pos 53),(.pos 67)]),
   ((.exchange 46 25 2),[(.neg 46),(.neg 25),(.pos 45),(.pos 65)]),
   ((.exchange 46 27 0),[(.neg 46),(.neg 27),(.pos 47),(.pos 67)]),
   ((.exchange 46 30 0),[(.neg 46),(.neg 30),(.pos 50),(.pos 67)]),
   ((.exchange 46 31 2),[(.neg 46),(.neg 31),(.pos 51),(.pos 65)]),
   ((.exchange 46 33 0),[(.neg 46),(.neg 33),(.pos 53),(.pos 67)]),
   ((.exchange 46 41 5),[(.neg 46),(.neg 41),(.pos 35),(.pos 40)]),
   ((.exchange 46 43 0),[(.neg 46),(.neg 43),(.pos 47),(.pos 50),(.pos 53)]),
   ((.exchange 46 52 0),[(.neg 52),(.neg 46),(.pos 47),(.pos 53)]),
   ((.exchange 46 58 5),[(.neg 58),(.neg 46),(.pos 37),(.pos 56)]),
   ((.exchange 46 61 2),[(.neg 61),(.neg 46),(.pos 51),(.pos 65)]),
   ((.exchange 46 63 0),[(.neg 63),(.neg 46),(.pos 53),(.pos 67)]),
   ((.exchange 46 64 0),[(.neg 64),(.neg 46),(.pos 50),(.pos 53),(.pos 67)]),
   ((.exchange 46 66 0),[(.neg 66),(.neg 46),(.pos 47),(.pos 67)]),
   ((.exchange 47 1 5),[(.neg 47),(.neg 1),(.pos 35),(.pos 41)]),
   ((.exchange 47 2 2),[(.neg 47),(.neg 2),(.pos 45),(.pos 49),(.pos 52)]),
   ((.exchange 47 4 5),[(.neg 47),(.neg 4),(.pos 38),(.pos 41)]),
   ((.exchange 47 6 2),[(.neg 47),(.neg 6),(.pos 45),(.pos 49)]),
   ((.exchange 47 13 2),[(.neg 47),(.neg 13),(.pos 49),(.pos 52)]),
   ((.exchange 47 19 2),[(.neg 47),(.neg 19),(.pos 45),(.pos 52),(.pos 66)]),
   ((.exchange 47 28 1),[(.neg 47),(.neg 28),(.pos 46),(.pos 50),(.pos 67)]),
   ((.exchange 47 40 1),[(.neg 47),(.neg 40),(.pos 46),(.pos 53)]),
   ((.exchange 47 42 1),[(.neg 47),(.neg 42),(.pos 46),(.pos 50),(.pos 53)]),
   ((.exchange 47 42 2),[(.neg 47),(.neg 42),(.pos 45),(.pos 49),(.pos 52)]),
   ((.exchange 47 42 5),[(.neg 47),(.neg 42),(.pos 35),(.pos 38),(.pos 41)]),
   ((.exchange 47 48 2),[(.neg 48),(.neg 47),(.pos 45),(.pos 49)]),
   ((.exchange 47 51 1),[(.neg 51),(.neg 47),(.pos 46),(.pos 53)]),
   ((.exchange 47 55 2),[(.neg 55),(.neg 47),(.pos 45),(.pos 66)]),
   ((.exchange 47 62 2),[(.neg 62),(.neg 47),(.pos 52),(.pos 66)]),
   ((.exchange 47 63 5),[(.neg 63),(.neg 47),(.pos 41),(.pos 57)]),
   ((.exchange 47 64 1),[(.neg 64),(.neg 47),(.pos 50),(.pos 53),(.pos 67)]),
   ((.exchange 47 69 2),[(.neg 69),(.neg 47),(.pos 52),(.pos 66)]),
   ((.exchange 48 3 5),[(.neg 48),(.neg 3),(.pos 37),(.pos 42)]),
   ((.exchange 48 5 3),[(.neg 48),(.neg 5),(.pos 45),(.pos 46)]),
   ((.exchange 48 11 0),[(.neg 48),(.neg 11),(.pos 49),(.pos 50),(.pos 54)]),
   ((.exchange 48 13 0),[(.neg 48),(.neg 13),(.pos 49),(.pos 54)])]

theorem certificates_1_valid : ∀ oc ∈ certificates_1,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.MaskOrigins.maskOrigins_sound (grid := (fun i : Fin 70 => N8R4.gridMasks.get i.val))
  have hchecks : ∀ i : Fin 128,
    Papers.RationalityTen.MatroidChecked.MaskOrigins.MaskOrigin (fun i : Fin 70 => N8R4.gridMasks.get i.val) (7 : Fin 8) old newIndex models
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



end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C71



end
end
end BundlePart1

