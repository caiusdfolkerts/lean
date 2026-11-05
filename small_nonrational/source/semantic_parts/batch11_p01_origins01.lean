module
public import SemanticParts.Batch11P01Data
public import Consolidated.SemanticData
public import Mathlib.Data.Fin.Tuple.Basic
public import MatroidCatalogue.Definitions
public import MatroidChecked.BitsetSemanticChecks
public import MatroidChecked.FastSemanticChecks
public import MatroidChecked.BitsetOrigins
public import MatroidChecked.MaskOrigins

section BundlePart1
/- Source: MatroidChecked/SemanticChunks/Cases19Part00.lean -/




@[expose] public section
noncomputable section

/- Source: MatroidCatalogue/Cases/N8R4C74Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C74


noncomputable def certificates_2 : List (Origin 70 434 × List Sat.Literal) :=
  [((.exchange 53 15 4),[(.neg 53),(.neg 15),(.pos 46),(.pos 47),(.pos 67)]),
   ((.exchange 53 25 4),[(.neg 53),(.neg 25),(.pos 46),(.pos 47),(.pos 67)]),
   ((.exchange 53 30 4),[(.neg 53),(.neg 30),(.pos 50),(.pos 67)]),
   ((.exchange 53 31 2),[(.neg 53),(.neg 31),(.pos 51),(.pos 69)]),
   ((.exchange 53 32 2),[(.neg 53),(.neg 32),(.pos 52),(.pos 69)]),
   ((.exchange 53 38 4),[(.neg 53),(.neg 38),(.pos 47),(.pos 50)]),
   ((.exchange 53 43 2),[(.neg 53),(.neg 43),(.pos 52),(.pos 54)]),
   ((.exchange 53 56 4),[(.neg 56),(.neg 53),(.pos 46),(.pos 67)]),
   ((.exchange 53 60 4),[(.neg 60),(.neg 53),(.pos 50),(.pos 67)]),
   ((.exchange 53 60 5),[(.neg 60),(.neg 53),(.pos 44),(.pos 63)]),
   ((.exchange 53 61 2),[(.neg 61),(.neg 53),(.pos 51),(.pos 69)]),
   ((.exchange 53 66 4),[(.neg 66),(.neg 53),(.pos 47),(.pos 67)]),
   ((.exchange 54 11 3),[(.neg 54),(.neg 11),(.pos 52),(.pos 53)]),
   ((.exchange 54 29 4),[(.neg 54),(.neg 29),(.pos 49),(.pos 68)]),
   ((.exchange 54 30 4),[(.neg 54),(.neg 30),(.pos 50),(.pos 68)]),
   ((.exchange 54 32 3),[(.neg 54),(.neg 32),(.pos 52),(.pos 69)]),
   ((.exchange 54 59 4),[(.neg 59),(.neg 54),(.pos 49),(.pos 68)]),
   ((.exchange 54 63 3),[(.neg 63),(.neg 54),(.pos 53),(.pos 69)]),
   ((.exchange 54 66 3),[(.neg 66),(.neg 54),(.pos 52),(.pos 69)]),
   ((.exchange 55 1 6),[(.neg 55),(.neg 1),(.pos 35),(.pos 39)]),
   ((.exchange 55 17 1),[(.neg 55),(.neg 17),(.pos 56),(.pos 58)]),
   ((.exchange 55 21 0),[(.neg 55),(.neg 21),(.pos 57),(.pos 62)]),
   ((.exchange 55 26 1),[(.neg 55),(.neg 26),(.pos 56),(.pos 65)]),
   ((.exchange 55 27 0),[(.neg 55),(.neg 27),(.pos 57),(.pos 66)]),
   ((.exchange 55 31 1),[(.neg 55),(.neg 31),(.pos 61),(.pos 65)]),
   ((.exchange 55 32 0),[(.neg 55),(.neg 32),(.pos 62),(.pos 66)]),
   ((.exchange 55 40 6),[(.neg 55),(.neg 40),(.pos 35),(.pos 39)]),
   ((.exchange 55 41 6),[(.neg 55),(.neg 41),(.pos 35),(.pos 39)]),
   ((.exchange 55 51 6),[(.neg 55),(.neg 51),(.pos 39),(.pos 45)]),
   ((.exchange 55 53 1),[(.neg 55),(.neg 53),(.pos 56),(.pos 61),(.pos 65)]),
   ((.exchange 55 53 6),[(.neg 55),(.neg 53),(.pos 35),(.pos 39),(.pos 45)]),
   ((.exchange 55 67 1),[(.neg 67),(.neg 55),(.pos 56),(.pos 65)]),
   ((.exchange 56 6 2),[(.neg 56),(.neg 6),(.pos 55),(.pos 58),(.pos 65)]),
   ((.exchange 56 7 6),[(.neg 56),(.neg 7),(.pos 37),(.pos 46)]),
   ((.exchange 56 27 0),[(.neg 56),(.neg 27),(.pos 57),(.pos 67)]),
   ((.exchange 56 30 0),[(.neg 56),(.neg 30),(.pos 60),(.pos 67)]),
   ((.exchange 56 38 6),[(.neg 56),(.neg 38),(.pos 35),(.pos 37)]),
   ((.exchange 56 45 2),[(.neg 56),(.neg 45),(.pos 55),(.pos 65)]),
   ((.exchange 56 48 2),[(.neg 56),(.neg 48),(.pos 58),(.pos 65)]),
   ((.exchange 56 49 2),[(.neg 56),(.neg 49),(.pos 55),(.pos 58),(.pos 65)]),
   ((.exchange 57 2 2),[(.neg 57),(.neg 2),(.pos 55),(.pos 59),(.pos 62)]),
   ((.exchange 57 3 1),[(.neg 57),(.neg 3),(.pos 56),(.pos 60),(.pos 63)]),
   ((.exchange 57 6 2),[(.neg 57),(.neg 6),(.pos 55),(.pos 59),(.pos 66)]),
   ((.exchange 57 10 6),[(.neg 57),(.neg 10),(.pos 35),(.pos 41),(.pos 47)]),
   ((.exchange 57 14 1),[(.neg 57),(.neg 14),(.pos 60),(.pos 63),(.pos 67)]),
   ((.exchange 57 22 1),[(.neg 57),(.neg 22),(.pos 56),(.pos 60),(.pos 63)]),
   ((.exchange 57 23 2),[(.neg 57),(.neg 23),(.pos 59),(.pos 62)]),
   ((.exchange 57 25 2),[(.neg 57),(.neg 25),(.pos 55),(.pos 66)]),
   ((.exchange 57 26 1),[(.neg 57),(.neg 26),(.pos 56),(.pos 67)]),
   ((.exchange 57 30 1),[(.neg 57),(.neg 30),(.pos 60),(.pos 67)]),
   ((.exchange 57 33 1),[(.neg 57),(.neg 33),(.pos 63),(.pos 67)]),
   ((.exchange 57 42 2),[(.neg 57),(.neg 42),(.pos 55),(.pos 59),(.pos 62)]),
   ((.exchange 57 44 1),[(.neg 57),(.neg 44),(.pos 60),(.pos 63)]),
   ((.exchange 57 49 2),[(.neg 57),(.neg 49),(.pos 59),(.pos 66)]),
   ((.exchange 57 51 1),[(.neg 57),(.neg 51),(.pos 56),(.pos 63),(.pos 67)]),
   ((.exchange 57 58 1),[(.neg 58),(.neg 57),(.pos 56),(.pos 60)]),
   ((.exchange 57 64 2),[(.neg 64),(.neg 57),(.pos 59),(.pos 62)]),
   ((.exchange 57 65 2),[(.neg 65),(.neg 57),(.pos 55),(.pos 66)]),
   ((.exchange 58 10 6),[(.neg 58),(.neg 10),(.pos 37),(.pos 42),(.pos 48)]),
   ((.exchange 58 24 0),[(.neg 58),(.neg 24),(.pos 60),(.pos 64)]),
   ((.exchange 58 30 0),[(.neg 58),(.neg 30),(.pos 60),(.pos 68)]),
   ((.exchange 58 33 3),[(.neg 58),(.neg 33),(.pos 56),(.pos 61),(.pos 65)]),
   ((.exchange 58 34 0),[(.neg 58),(.neg 34),(.pos 64),(.pos 68)]),
   ((.exchange 58 44 6),[(.neg 58),(.neg 44),(.pos 37),(.pos 42)]),
   ((.exchange 58 50 0),[(.neg 58),(.neg 50),(.pos 60),(.pos 68)]),
   ((.exchange 58 53 3),[(.neg 58),(.neg 53),(.pos 56),(.pos 61),(.pos 65)]),
   ((.exchange 58 54 0),[(.neg 58),(.neg 54),(.pos 64),(.pos 68)]),
   ((.exchange 58 67 3),[(.neg 67),(.neg 58),(.pos 56),(.pos 65)]),
   ((.exchange 59 30 1),[(.neg 59),(.neg 30),(.pos 60),(.pos 68)]),
   ((.exchange 59 32 3),[(.neg 59),(.neg 32),(.pos 62),(.pos 66)]),
   ((.exchange 59 41 3),[(.neg 59),(.neg 41),(.pos 57),(.pos 62)]),
   ((.exchange 59 44 1),[(.neg 59),(.neg 44),(.pos 60),(.pos 64)]),
   ((.exchange 59 47 3),[(.neg 59),(.neg 47),(.pos 57),(.pos 66)]),
   ((.exchange 59 50 1),[(.neg 59),(.neg 50),(.pos 60),(.pos 68)]),
   ((.exchange 59 54 1),[(.neg 59),(.neg 54),(.pos 64),(.pos 68)]),
   ((.exchange 59 63 3),[(.neg 63),(.neg 59),(.pos 57),(.pos 62)]),
   ((.exchange 59 69 1),[(.neg 69),(.neg 59),(.pos 64),(.pos 68)]),
   ((.exchange 59 69 3),[(.neg 69),(.neg 59),(.pos 62),(.pos 66)]),
   ((.exchange 60 2 2),[(.neg 60),(.neg 2),(.pos 58),(.pos 59),(.pos 64)]),
   ((.exchange 60 7 6),[(.neg 60),(.neg 7),(.pos 37),(.pos 50)]),
   ((.exchange 60 8 6),[(.neg 60),(.neg 8),(.pos 38),(.pos 50)]),
   ((.exchange 60 21 3),[(.neg 60),(.neg 21),(.pos 57),(.pos 63)]),
   ((.exchange 60 26 3),[(.neg 60),(.neg 26),(.pos 56),(.pos 67)]),
   ((.exchange 60 28 2),[(.neg 60),(.neg 28),(.pos 58),(.pos 68)]),
   ((.exchange 60 35 3),[(.neg 60),(.neg 35),(.pos 56),(.pos 57)]),
   ((.exchange 60 40 6),[(.neg 60),(.neg 40),(.pos 37),(.pos 44)]),
   ((.exchange 60 41 3),[(.neg 60),(.neg 41),(.pos 57),(.pos 63)]),
   ((.exchange 60 43 2),[(.neg 60),(.neg 43),(.pos 59),(.pos 64)]),
   ((.exchange 60 48 2),[(.neg 60),(.neg 48),(.pos 58),(.pos 68)]),
   ((.exchange 60 49 2),[(.neg 60),(.neg 49),(.pos 59),(.pos 68)]),
   ((.exchange 60 53 3),[(.neg 60),(.neg 53),(.pos 63),(.pos 67)]),
   ((.exchange 60 54 2),[(.neg 60),(.neg 54),(.pos 64),(.pos 68)]),
   ((.exchange 60 55 3),[(.neg 60),(.neg 55),(.pos 56),(.pos 57)]),
   ((.exchange 60 69 2),[(.neg 69),(.neg 60),(.pos 64),(.pos 68)]),
   ((.exchange 60 69 3),[(.neg 69),(.neg 60),(.pos 63),(.pos 67)]),
   ((.exchange 61 0 4),[(.neg 61),(.neg 0),(.pos 55),(.pos 56),(.pos 58)]),
   ((.exchange 61 9 6),[(.neg 61),(.neg 9),(.pos 39),(.pos 51)]),
   ((.exchange 61 23 0),[(.neg 61),(.neg 23),(.pos 62),(.pos 64)]),
   ((.exchange 61 32 0),[(.neg 61),(.neg 32),(.pos 62),(.pos 69)]),
   ((.exchange 61 34 0),[(.neg 61),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 61 43 6),[(.neg 61),(.neg 43),(.pos 39),(.pos 42)]),
   ((.exchange 61 45 4),[(.neg 61),(.neg 45),(.pos 55),(.pos 65)]),
   ((.exchange 61 48 4),[(.neg 61),(.neg 48),(.pos 58),(.pos 65)]),
   ((.exchange 62 0 4),[(.neg 62),(.neg 0),(.pos 55),(.pos 57),(.pos 59)]),
   ((.exchange 62 0 6),[(.neg 62),(.neg 0),(.pos 39),(.pos 41),(.pos 43)]),
   ((.exchange 62 3 1),[(.neg 62),(.neg 3),(.pos 61),(.pos 63),(.pos 64)]),
   ((.exchange 62 9 6),[(.neg 62),(.neg 9),(.pos 39),(.pos 52)]),
   ((.exchange 62 15 4),[(.neg 62),(.neg 15),(.pos 55),(.pos 57)]),
   ((.exchange 62 18 4),[(.neg 62),(.neg 18),(.pos 57),(.pos 59)]),
   ((.exchange 62 24 1),[(.neg 62),(.neg 24),(.pos 63),(.pos 64)]),
   ((.exchange 62 27 4),[(.neg 62),(.neg 27),(.pos 57),(.pos 66)]),
   ((.exchange 62 31 1),[(.neg 62),(.neg 31),(.pos 61),(.pos 69)]),
   ((.exchange 62 33 1),[(.neg 62),(.neg 33),(.pos 63),(.pos 69)]),
   ((.exchange 62 34 1),[(.neg 62),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 62 45 6),[(.neg 62),(.neg 45),(.pos 39),(.pos 52)]),
   ((.exchange 62 47 4),[(.neg 62),(.neg 47),(.pos 57),(.pos 66)]),
   ((.exchange 62 53 1),[(.neg 62),(.neg 53),(.pos 63),(.pos 69)]),
   ((.exchange 62 56 4),[(.neg 62),(.neg 56),(.pos 55),(.pos 57)]),
   ((.exchange 62 60 4),[(.neg 62),(.neg 60),(.pos 57),(.pos 59)]),
   ((.exchange 62 65 1),[(.neg 65),(.neg 62),(.pos 61),(.pos 69)]),
   ((.exchange 62 65 4),[(.neg 65),(.neg 62),(.pos 55),(.pos 66)]),
   ((.exchange 63 18 4),[(.neg 63),(.neg 18),(.pos 57),(.pos 60)]),
   ((.exchange 63 27 4),[(.neg 63),(.neg 27),(.pos 57),(.pos 67)]),
   ((.exchange 63 30 4),[(.neg 63),(.neg 30),(.pos 60),(.pos 67)]),
   ((.exchange 63 32 2),[(.neg 63),(.neg 32),(.pos 62),(.pos 69)]),
   ((.exchange 63 34 2),[(.neg 63),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 63 38 4),[(.neg 63),(.neg 38),(.pos 57),(.pos 60)]),
   ((.exchange 63 43 2),[(.neg 63),(.neg 43),(.pos 62),(.pos 64)])]

theorem certificates_2_valid : ∀ oc ∈ certificates_2,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.MaskOrigins.maskOrigins_sound (grid := (fun i : Fin 70 => N8R4.gridMasks.get i.val))
  have hchecks : ∀ i : Fin 128,
    Papers.RationalityTen.MatroidChecked.MaskOrigins.MaskOrigin (fun i : Fin 70 => N8R4.gridMasks.get i.val) (7 : Fin 8) old newIndex models
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



noncomputable def certificates_3 : List (Origin 70 434 × List Sat.Literal) :=
  [((.exchange 63 47 4),[(.neg 63),(.neg 47),(.pos 57),(.pos 67)]),
   ((.exchange 63 54 2),[(.neg 63),(.neg 54),(.pos 64),(.pos 69)]),
   ((.exchange 63 59 4),[(.neg 63),(.neg 59),(.pos 57),(.pos 60)]),
   ((.exchange 63 68 2),[(.neg 68),(.neg 63),(.pos 64),(.pos 69)]),
   ((.exchange 64 10 6),[(.neg 64),(.neg 10),(.pos 42),(.pos 44),(.pos 54)]),
   ((.exchange 64 17 4),[(.neg 64),(.neg 17),(.pos 58),(.pos 60)]),
   ((.exchange 64 18 4),[(.neg 64),(.neg 18),(.pos 59),(.pos 60)]),
   ((.exchange 64 29 4),[(.neg 64),(.neg 29),(.pos 59),(.pos 68)]),
   ((.exchange 64 31 3),[(.neg 64),(.neg 31),(.pos 61),(.pos 69)]),
   ((.exchange 64 32 3),[(.neg 64),(.neg 32),(.pos 62),(.pos 69)]),
   ((.exchange 64 33 3),[(.neg 64),(.neg 33),(.pos 63),(.pos 69)]),
   ((.exchange 64 38 4),[(.neg 64),(.neg 38),(.pos 59),(.pos 60)]),
   ((.exchange 64 48 4),[(.neg 64),(.neg 48),(.pos 58),(.pos 68)]),
   ((.exchange 64 51 3),[(.neg 64),(.neg 51),(.pos 61),(.pos 69)]),
   ((.exchange 64 53 3),[(.neg 64),(.neg 53),(.pos 63),(.pos 69)]),
   ((.exchange 64 55 3),[(.neg 64),(.neg 55),(.pos 61),(.pos 62)]),
   ((.exchange 64 65 3),[(.neg 65),(.neg 64),(.pos 61),(.pos 69)]),
   ((.exchange 64 66 4),[(.neg 66),(.neg 64),(.pos 59),(.pos 68)]),
   ((.exchange 65 2 5),[(.neg 65),(.neg 2),(.pos 55),(.pos 58),(.pos 61)]),
   ((.exchange 65 2 6),[(.neg 65),(.neg 2),(.pos 45),(.pos 48),(.pos 51)]),
   ((.exchange 65 6 6),[(.neg 65),(.neg 6),(.pos 45),(.pos 48)]),
   ((.exchange 65 9 6),[(.neg 65),(.neg 9),(.pos 45),(.pos 51)]),
   ((.exchange 65 14 6),[(.neg 65),(.neg 14),(.pos 46),(.pos 48),(.pos 51)]),
   ((.exchange 65 18 5),[(.neg 65),(.neg 18),(.pos 55),(.pos 56),(.pos 58)]),
   ((.exchange 65 24 0),[(.neg 65),(.neg 24),(.pos 67),(.pos 68),(.pos 69)]),
   ((.exchange 65 27 0),[(.neg 65),(.neg 27),(.pos 66),(.pos 67)]),
   ((.exchange 65 30 0),[(.neg 65),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 65 32 0),[(.neg 65),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 65 33 0),[(.neg 65),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 65 34 0),[(.neg 65),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 65 35 5),[(.neg 65),(.neg 35),(.pos 55),(.pos 56)]),
   ((.exchange 65 36 6),[(.neg 65),(.neg 36),(.pos 45),(.pos 48)]),
   ((.exchange 65 37 6),[(.neg 65),(.neg 37),(.pos 46),(.pos 48)]),
   ((.exchange 65 49 0),[(.neg 65),(.neg 49),(.pos 66),(.pos 68)]),
   ((.exchange 65 49 6),[(.neg 65),(.neg 49),(.pos 45),(.pos 48)]),
   ((.exchange 65 52 6),[(.neg 65),(.neg 52),(.pos 45),(.pos 51)]),
   ((.exchange 65 53 0),[(.neg 65),(.neg 53),(.pos 67),(.pos 69)]),
   ((.exchange 65 54 0),[(.neg 65),(.neg 54),(.pos 68),(.pos 69)]),
   ((.exchange 65 57 5),[(.neg 65),(.neg 57),(.pos 55),(.pos 56)]),
   ((.exchange 65 60 5),[(.neg 65),(.neg 60),(.pos 56),(.pos 58)]),
   ((.exchange 65 63 0),[(.neg 65),(.neg 63),(.pos 67),(.pos 69)]),
   ((.exchange 65 64 5),[(.neg 65),(.neg 64),(.pos 58),(.pos 61)]),
   ((.exchange 66 0 5),[(.neg 66),(.neg 0),(.pos 55),(.pos 57),(.pos 59)]),
   ((.exchange 66 6 6),[(.neg 66),(.neg 6),(.pos 45),(.pos 49)]),
   ((.exchange 66 7 6),[(.neg 66),(.neg 7),(.pos 45),(.pos 47),(.pos 49)]),
   ((.exchange 66 8 6),[(.neg 66),(.neg 8),(.pos 47),(.pos 49)]),
   ((.exchange 66 11 6),[(.neg 66),(.neg 11),(.pos 47),(.pos 52)]),
   ((.exchange 66 30 1),[(.neg 66),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 66 33 1),[(.neg 66),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 66 34 1),[(.neg 66),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 66 35 5),[(.neg 66),(.neg 35),(.pos 55),(.pos 57)]),
   ((.exchange 66 36 6),[(.neg 66),(.neg 36),(.pos 45),(.pos 49)]),
   ((.exchange 66 39 5),[(.neg 66),(.neg 39),(.pos 55),(.pos 62)]),
   ((.exchange 66 41 5),[(.neg 66),(.neg 41),(.pos 57),(.pos 62)]),
   ((.exchange 66 42 6),[(.neg 66),(.neg 42),(.pos 45),(.pos 49),(.pos 52)]),
   ((.exchange 66 43 6),[(.neg 66),(.neg 43),(.pos 49),(.pos 52)]),
   ((.exchange 66 46 1),[(.neg 66),(.neg 46),(.pos 65),(.pos 67)]),
   ((.exchange 66 53 6),[(.neg 66),(.neg 53),(.pos 47),(.pos 52)]),
   ((.exchange 66 54 1),[(.neg 66),(.neg 54),(.pos 68),(.pos 69)]),
   ((.exchange 66 58 1),[(.neg 66),(.neg 58),(.pos 65),(.pos 68)]),
   ((.exchange 66 60 5),[(.neg 66),(.neg 60),(.pos 57),(.pos 59)]),
   ((.exchange 66 64 1),[(.neg 66),(.neg 64),(.pos 68),(.pos 69)]),
   ((.exchange 67 0 5),[(.neg 67),(.neg 0),(.pos 56),(.pos 57),(.pos 60)]),
   ((.exchange 67 7 6),[(.neg 67),(.neg 7),(.pos 46),(.pos 50)]),
   ((.exchange 67 21 5),[(.neg 67),(.neg 21),(.pos 57),(.pos 63)]),
   ((.exchange 67 28 2),[(.neg 67),(.neg 28),(.pos 65),(.pos 68)]),
   ((.exchange 67 31 2),[(.neg 67),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 67 32 2),[(.neg 67),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 67 34 2),[(.neg 67),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 67 35 5),[(.neg 67),(.neg 35),(.pos 56),(.pos 57)]),
   ((.exchange 67 37 5),[(.neg 67),(.neg 37),(.pos 56),(.pos 60)]),
   ((.exchange 67 39 6),[(.neg 67),(.neg 39),(.pos 46),(.pos 47),(.pos 53)]),
   ((.exchange 67 40 6),[(.neg 67),(.neg 40),(.pos 46),(.pos 53)]),
   ((.exchange 67 41 6),[(.neg 67),(.neg 41),(.pos 47),(.pos 53)]),
   ((.exchange 67 45 2),[(.neg 67),(.neg 45),(.pos 65),(.pos 66)]),
   ((.exchange 67 49 2),[(.neg 67),(.neg 49),(.pos 66),(.pos 68)]),
   ((.exchange 67 52 2),[(.neg 67),(.neg 52),(.pos 66),(.pos 69)]),
   ((.exchange 67 52 6),[(.neg 67),(.neg 52),(.pos 47),(.pos 53)]),
   ((.exchange 67 54 2),[(.neg 67),(.neg 54),(.pos 68),(.pos 69)]),
   ((.exchange 67 58 2),[(.neg 67),(.neg 58),(.pos 65),(.pos 68)]),
   ((.exchange 67 58 5),[(.neg 67),(.neg 58),(.pos 56),(.pos 60)]),
   ((.exchange 68 0 5),[(.neg 68),(.neg 0),(.pos 58),(.pos 59),(.pos 60)]),
   ((.exchange 68 8 6),[(.neg 68),(.neg 8),(.pos 49),(.pos 50)]),
   ((.exchange 68 17 5),[(.neg 68),(.neg 17),(.pos 58),(.pos 60)]),
   ((.exchange 68 18 5),[(.neg 68),(.neg 18),(.pos 59),(.pos 60)]),
   ((.exchange 68 22 5),[(.neg 68),(.neg 22),(.pos 58),(.pos 64)]),
   ((.exchange 68 27 3),[(.neg 68),(.neg 27),(.pos 66),(.pos 67)]),
   ((.exchange 68 31 3),[(.neg 68),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 68 32 3),[(.neg 68),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 68 33 3),[(.neg 68),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 68 36 6),[(.neg 68),(.neg 36),(.pos 48),(.pos 49)]),
   ((.exchange 68 37 6),[(.neg 68),(.neg 37),(.pos 48),(.pos 50)]),
   ((.exchange 68 38 5),[(.neg 68),(.neg 38),(.pos 59),(.pos 60)]),
   ((.exchange 68 38 6),[(.neg 68),(.neg 38),(.pos 49),(.pos 50)]),
   ((.exchange 68 43 5),[(.neg 68),(.neg 43),(.pos 59),(.pos 64)]),
   ((.exchange 68 46 3),[(.neg 68),(.neg 46),(.pos 65),(.pos 67)]),
   ((.exchange 68 53 3),[(.neg 68),(.neg 53),(.pos 67),(.pos 69)]),
   ((.exchange 68 62 3),[(.neg 68),(.neg 62),(.pos 66),(.pos 69)]),
   ((.exchange 68 62 5),[(.neg 68),(.neg 62),(.pos 59),(.pos 64)]),
   ((.exchange 69 0 5),[(.neg 69),(.neg 0),(.pos 61),(.pos 62),(.pos 63),(.pos 64)]),
   ((.exchange 69 9 6),[(.neg 69),(.neg 9),(.pos 51),(.pos 52)]),
   ((.exchange 69 10 6),[(.neg 69),(.neg 10),(.pos 51),(.pos 53)]),
   ((.exchange 69 24 5),[(.neg 69),(.neg 24),(.pos 63),(.pos 64)]),
   ((.exchange 69 25 4),[(.neg 69),(.neg 25),(.pos 65),(.pos 66)]),
   ((.exchange 69 26 4),[(.neg 69),(.neg 26),(.pos 65),(.pos 67)]),
   ((.exchange 69 27 4),[(.neg 69),(.neg 27),(.pos 66),(.pos 67)]),
   ((.exchange 69 28 4),[(.neg 69),(.neg 28),(.pos 65),(.pos 68)]),
   ((.exchange 69 29 4),[(.neg 69),(.neg 29),(.pos 66),(.pos 68)]),
   ((.exchange 69 30 4),[(.neg 69),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 69 36 6),[(.neg 69),(.neg 36),(.pos 51),(.pos 52),(.pos 54)]),
   ((.exchange 69 40 6),[(.neg 69),(.neg 40),(.pos 51),(.pos 53)]),
   ((.exchange 69 41 5),[(.neg 69),(.neg 41),(.pos 62),(.pos 63)]),
   ((.exchange 69 41 6),[(.neg 69),(.neg 41),(.pos 52),(.pos 53)]),
   ((.exchange 69 43 6),[(.neg 69),(.neg 43),(.pos 52),(.pos 54)]),
   ((.exchange 69 44 6),[(.neg 69),(.neg 44),(.pos 53),(.pos 54)]),
   ((.exchange 69 45 4),[(.neg 69),(.neg 45),(.pos 65),(.pos 66)]),
   ((.exchange 69 45 6),[(.neg 69),(.neg 45),(.pos 51),(.pos 52)]),
   ((.exchange 69 46 4),[(.neg 69),(.neg 46),(.pos 65),(.pos 67)]),
   ((.exchange 69 47 4),[(.neg 69),(.neg 47),(.pos 66),(.pos 67)]),
   ((.exchange 69 48 4),[(.neg 69),(.neg 48),(.pos 65),(.pos 68)]),
   ((.exchange 69 49 6),[(.neg 69),(.neg 49),(.pos 52),(.pos 54)]),
   ((.exchange 69 57 4),[(.neg 69),(.neg 57),(.pos 66),(.pos 67)]),
   ((.exchange 69 58 4),[(.neg 69),(.neg 58),(.pos 65),(.pos 68)]),
   ((.exchange 69 58 5),[(.neg 69),(.neg 58),(.pos 61),(.pos 64)]),
   (.newPoint,[(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 0),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 62),(.neg 60),(.neg 57),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 44),(.neg 43),(.neg 41),(.neg 38),(.pos 35),(.pos 36),(.pos 37),(.pos 39),(.pos 40),(.pos 42),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 51),(.pos 54),(.pos 55),(.pos 56),(.pos 58),(.pos 59),(.pos 61),(.pos 63),(.pos 65)]),
   ((.excluded 1),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 56),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 48),(.neg 42),(.neg 40),(.neg 37),(.pos 35),(.pos 36),(.pos 38),(.pos 39),(.pos 41),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 49),(.pos 52),(.pos 55),(.pos 57),(.pos 58),(.pos 59),(.pos 62),(.pos 66)]),
   ((.excluded 2),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 57),(.neg 56),(.neg 54),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 46),(.pos 47),(.pos 50),(.pos 53),(.pos 55),(.pos 58),(.pos 59),(.pos 67)])]

theorem certificates_3_valid : ∀ oc ∈ certificates_3,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.MaskOrigins.maskOrigins_sound (grid := (fun i : Fin 70 => N8R4.gridMasks.get i.val))
  have hchecks : ∀ i : Fin 128,
    Papers.RationalityTen.MatroidChecked.MaskOrigins.MaskOrigin (fun i : Fin 70 => N8R4.gridMasks.get i.val) (7 : Fin 8) old newIndex models
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



end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C74


end
end
end BundlePart1

