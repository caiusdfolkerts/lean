module
public import SemanticParts.Batch11P00Data
public import Consolidated.SemanticData
public import Mathlib.Data.Fin.Tuple.Basic
public import MatroidCatalogue.Definitions
public import MatroidChecked.BitsetSemanticChecks
public import MatroidChecked.FastSemanticChecks
public import MatroidChecked.BitsetOrigins
public import MatroidChecked.MaskOrigins

section BundlePart0
/- Source: MatroidChecked/SemanticChunks/Cases18Part02.lean -/




@[expose] public section
noncomputable section

/- Source: MatroidCatalogue/Cases/N8R4C73Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C73


noncomputable def certificates_2 : List (Origin 70 272 × List Sat.Literal) :=
  [((.exchange 54 60 4),[(.neg 60),(.neg 54),(.pos 50),(.pos 68)]),
   ((.exchange 54 60 5),[(.neg 60),(.neg 54),(.pos 44),(.pos 64)]),
   ((.exchange 54 63 5),[(.neg 63),(.neg 54),(.pos 44),(.pos 64)]),
   ((.exchange 54 66 4),[(.neg 66),(.neg 54),(.pos 49),(.pos 68)]),
   ((.exchange 55 0 6),[(.neg 55),(.neg 0),(.pos 35),(.pos 36)]),
   ((.exchange 55 17 1),[(.neg 55),(.neg 17),(.pos 56),(.pos 58)]),
   ((.exchange 55 21 0),[(.neg 55),(.neg 21),(.pos 57),(.pos 62)]),
   ((.exchange 55 22 1),[(.neg 55),(.neg 22),(.pos 58),(.pos 61)]),
   ((.exchange 55 23 0),[(.neg 55),(.neg 23),(.pos 59),(.pos 62)]),
   ((.exchange 55 37 1),[(.neg 55),(.neg 37),(.pos 56),(.pos 58)]),
   ((.exchange 55 37 6),[(.neg 55),(.neg 37),(.pos 35),(.pos 36)]),
   ((.exchange 55 42 1),[(.neg 55),(.neg 42),(.pos 58),(.pos 61)]),
   ((.exchange 55 64 0),[(.neg 64),(.neg 55),(.pos 59),(.pos 62)]),
   ((.exchange 56 0 6),[(.neg 56),(.neg 0),(.pos 35),(.pos 37)]),
   ((.exchange 56 5 6),[(.neg 56),(.neg 5),(.pos 35),(.pos 46)]),
   ((.exchange 56 6 2),[(.neg 56),(.neg 6),(.pos 55),(.pos 58),(.pos 65)]),
   ((.exchange 56 8 6),[(.neg 56),(.neg 8),(.pos 35),(.pos 37),(.pos 46)]),
   ((.exchange 56 28 2),[(.neg 56),(.neg 28),(.pos 58),(.pos 65)]),
   ((.exchange 56 30 0),[(.neg 56),(.neg 30),(.pos 60),(.pos 67)]),
   ((.exchange 56 45 6),[(.neg 56),(.neg 45),(.pos 35),(.pos 46)]),
   ((.exchange 56 47 0),[(.neg 56),(.neg 47),(.pos 57),(.pos 67)]),
   ((.exchange 56 47 6),[(.neg 56),(.neg 47),(.pos 35),(.pos 46)]),
   ((.exchange 56 59 2),[(.neg 59),(.neg 56),(.pos 55),(.pos 58)]),
   ((.exchange 56 66 0),[(.neg 66),(.neg 56),(.pos 57),(.pos 67)]),
   ((.exchange 56 68 0),[(.neg 68),(.neg 56),(.pos 60),(.pos 67)]),
   ((.exchange 56 68 2),[(.neg 68),(.neg 56),(.pos 58),(.pos 65)]),
   ((.exchange 57 9 2),[(.neg 57),(.neg 9),(.pos 55),(.pos 62),(.pos 66)]),
   ((.exchange 57 33 1),[(.neg 57),(.neg 33),(.pos 63),(.pos 67)]),
   ((.exchange 57 39 2),[(.neg 57),(.neg 39),(.pos 55),(.pos 62)]),
   ((.exchange 57 51 1),[(.neg 57),(.neg 51),(.pos 56),(.pos 63),(.pos 67)]),
   ((.exchange 57 52 2),[(.neg 57),(.neg 52),(.pos 62),(.pos 66)]),
   ((.exchange 57 53 1),[(.neg 57),(.neg 53),(.pos 63),(.pos 67)]),
   ((.exchange 57 61 2),[(.neg 61),(.neg 57),(.pos 55),(.pos 62)]),
   ((.exchange 58 0 6),[(.neg 58),(.neg 0),(.pos 36),(.pos 37)]),
   ((.exchange 58 5 6),[(.neg 58),(.neg 5),(.pos 36),(.pos 37),(.pos 48)]),
   ((.exchange 58 12 6),[(.neg 58),(.neg 12),(.pos 42),(.pos 48)]),
   ((.exchange 58 14 6),[(.neg 58),(.neg 14),(.pos 37),(.pos 42),(.pos 48)]),
   ((.exchange 58 21 3),[(.neg 58),(.neg 21),(.pos 55),(.pos 56),(.pos 61)]),
   ((.exchange 58 24 0),[(.neg 58),(.neg 24),(.pos 60),(.pos 64)]),
   ((.exchange 58 30 0),[(.neg 58),(.neg 30),(.pos 60),(.pos 68)]),
   ((.exchange 58 34 0),[(.neg 58),(.neg 34),(.pos 64),(.pos 68)]),
   ((.exchange 58 38 6),[(.neg 58),(.neg 38),(.pos 36),(.pos 37)]),
   ((.exchange 58 39 3),[(.neg 58),(.neg 39),(.pos 55),(.pos 61)]),
   ((.exchange 58 43 0),[(.neg 58),(.neg 43),(.pos 59),(.pos 64)]),
   ((.exchange 58 44 0),[(.neg 58),(.neg 44),(.pos 60),(.pos 64)]),
   ((.exchange 58 45 6),[(.neg 58),(.neg 45),(.pos 36),(.pos 48)]),
   ((.exchange 58 49 0),[(.neg 58),(.neg 49),(.pos 59),(.pos 68)]),
   ((.exchange 58 54 6),[(.neg 58),(.neg 54),(.pos 42),(.pos 48)]),
   ((.exchange 58 66 0),[(.neg 66),(.neg 58),(.pos 59),(.pos 68)]),
   ((.exchange 58 67 0),[(.neg 67),(.neg 58),(.pos 60),(.pos 68)]),
   ((.exchange 58 67 3),[(.neg 67),(.neg 58),(.pos 56),(.pos 65)]),
   ((.exchange 59 1 3),[(.neg 59),(.neg 1),(.pos 55),(.pos 57),(.pos 62)]),
   ((.exchange 59 34 1),[(.neg 59),(.neg 34),(.pos 64),(.pos 68)]),
   ((.exchange 59 48 1),[(.neg 59),(.neg 48),(.pos 58),(.pos 68)]),
   ((.exchange 59 51 3),[(.neg 59),(.neg 51),(.pos 55),(.pos 62),(.pos 66)]),
   ((.exchange 59 54 1),[(.neg 59),(.neg 54),(.pos 64),(.pos 68)]),
   ((.exchange 59 54 6),[(.neg 59),(.neg 54),(.pos 43),(.pos 49)]),
   ((.exchange 59 61 1),[(.neg 61),(.neg 59),(.pos 58),(.pos 64)]),
   ((.exchange 59 65 1),[(.neg 65),(.neg 59),(.pos 58),(.pos 68)]),
   ((.exchange 60 1 3),[(.neg 60),(.neg 1),(.pos 56),(.pos 57),(.pos 63)]),
   ((.exchange 60 3 6),[(.neg 60),(.neg 3),(.pos 37),(.pos 44)]),
   ((.exchange 60 22 2),[(.neg 60),(.neg 22),(.pos 58),(.pos 64)]),
   ((.exchange 60 28 2),[(.neg 60),(.neg 28),(.pos 58),(.pos 68)]),
   ((.exchange 60 33 3),[(.neg 60),(.neg 33),(.pos 63),(.pos 67)]),
   ((.exchange 60 34 2),[(.neg 60),(.neg 34),(.pos 64),(.pos 68)]),
   ((.exchange 60 51 3),[(.neg 60),(.neg 51),(.pos 56),(.pos 63),(.pos 67)]),
   ((.exchange 60 51 6),[(.neg 60),(.neg 51),(.pos 37),(.pos 44),(.pos 50)]),
   ((.exchange 60 53 6),[(.neg 60),(.neg 53),(.pos 44),(.pos 50)]),
   ((.exchange 60 61 2),[(.neg 61),(.neg 60),(.pos 58),(.pos 64)]),
   ((.exchange 60 69 2),[(.neg 69),(.neg 60),(.pos 64),(.pos 68)]),
   ((.exchange 61 0 4),[(.neg 61),(.neg 0),(.pos 55),(.pos 56),(.pos 58)]),
   ((.exchange 61 12 6),[(.neg 61),(.neg 12),(.pos 42),(.pos 51)]),
   ((.exchange 61 16 4),[(.neg 61),(.neg 16),(.pos 55),(.pos 58)]),
   ((.exchange 61 23 0),[(.neg 61),(.neg 23),(.pos 62),(.pos 64)]),
   ((.exchange 61 32 0),[(.neg 61),(.neg 32),(.pos 62),(.pos 69)]),
   ((.exchange 61 34 0),[(.neg 61),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 61 48 4),[(.neg 61),(.neg 48),(.pos 58),(.pos 65)]),
   ((.exchange 61 52 0),[(.neg 61),(.neg 52),(.pos 62),(.pos 69)]),
   ((.exchange 61 66 0),[(.neg 66),(.neg 61),(.pos 62),(.pos 69)]),
   ((.exchange 62 5 4),[(.neg 62),(.neg 5),(.pos 55),(.pos 57),(.pos 66)]),
   ((.exchange 62 12 6),[(.neg 62),(.neg 12),(.pos 39),(.pos 43),(.pos 52)]),
   ((.exchange 62 17 1),[(.neg 62),(.neg 17),(.pos 61),(.pos 63),(.pos 64)]),
   ((.exchange 62 22 1),[(.neg 62),(.neg 22),(.pos 61),(.pos 64)]),
   ((.exchange 62 26 4),[(.neg 62),(.neg 26),(.pos 55),(.pos 57),(.pos 66)]),
   ((.exchange 62 28 4),[(.neg 62),(.neg 28),(.pos 55),(.pos 59),(.pos 66)]),
   ((.exchange 62 31 1),[(.neg 62),(.neg 31),(.pos 61),(.pos 69)]),
   ((.exchange 62 35 4),[(.neg 62),(.neg 35),(.pos 55),(.pos 57)]),
   ((.exchange 62 36 4),[(.neg 62),(.neg 36),(.pos 55),(.pos 59)]),
   ((.exchange 62 47 4),[(.neg 62),(.neg 47),(.pos 57),(.pos 66)]),
   ((.exchange 62 48 4),[(.neg 62),(.neg 48),(.pos 55),(.pos 59),(.pos 66)]),
   ((.exchange 62 49 4),[(.neg 62),(.neg 49),(.pos 59),(.pos 66)]),
   ((.exchange 62 51 1),[(.neg 62),(.neg 51),(.pos 61),(.pos 69)]),
   ((.exchange 62 53 1),[(.neg 62),(.neg 53),(.pos 63),(.pos 69)]),
   ((.exchange 62 56 4),[(.neg 62),(.neg 56),(.pos 55),(.pos 57)]),
   ((.exchange 62 67 4),[(.neg 67),(.neg 62),(.pos 57),(.pos 66)]),
   ((.exchange 62 68 1),[(.neg 68),(.neg 62),(.pos 64),(.pos 69)]),
   ((.exchange 63 34 2),[(.neg 63),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 63 43 2),[(.neg 63),(.neg 43),(.pos 62),(.pos 64)]),
   ((.exchange 63 50 4),[(.neg 63),(.neg 50),(.pos 60),(.pos 67)]),
   ((.exchange 64 1 3),[(.neg 64),(.neg 1),(.pos 61),(.pos 62),(.pos 63)]),
   ((.exchange 64 3 6),[(.neg 64),(.neg 3),(.pos 42),(.pos 44)]),
   ((.exchange 64 4 6),[(.neg 64),(.neg 4),(.pos 43),(.pos 44)]),
   ((.exchange 64 8 4),[(.neg 64),(.neg 8),(.pos 59),(.pos 60),(.pos 68)]),
   ((.exchange 64 13 6),[(.neg 64),(.neg 13),(.pos 43),(.pos 54)]),
   ((.exchange 64 14 6),[(.neg 64),(.neg 14),(.pos 44),(.pos 54)]),
   ((.exchange 64 21 3),[(.neg 64),(.neg 21),(.pos 62),(.pos 63)]),
   ((.exchange 64 29 4),[(.neg 64),(.neg 29),(.pos 59),(.pos 68)]),
   ((.exchange 64 32 3),[(.neg 64),(.neg 32),(.pos 62),(.pos 69)]),
   ((.exchange 64 36 4),[(.neg 64),(.neg 36),(.pos 58),(.pos 59)]),
   ((.exchange 64 40 6),[(.neg 64),(.neg 40),(.pos 42),(.pos 44)]),
   ((.exchange 64 48 4),[(.neg 64),(.neg 48),(.pos 58),(.pos 68)]),
   ((.exchange 64 49 6),[(.neg 64),(.neg 49),(.pos 43),(.pos 54)]),
   ((.exchange 64 53 3),[(.neg 64),(.neg 53),(.pos 63),(.pos 69)]),
   ((.exchange 64 56 4),[(.neg 64),(.neg 56),(.pos 58),(.pos 60)]),
   ((.exchange 64 67 3),[(.neg 67),(.neg 64),(.pos 63),(.pos 69)]),
   ((.exchange 65 14 6),[(.neg 65),(.neg 14),(.pos 46),(.pos 48),(.pos 51)]),
   ((.exchange 65 24 5),[(.neg 65),(.neg 24),(.pos 56),(.pos 58),(.pos 61)]),
   ((.exchange 65 30 0),[(.neg 65),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 65 33 0),[(.neg 65),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 65 34 0),[(.neg 65),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 65 54 0),[(.neg 65),(.neg 54),(.pos 68),(.pos 69)]),
   ((.exchange 66 30 1),[(.neg 66),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 66 33 1),[(.neg 66),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 66 50 1),[(.neg 66),(.neg 50),(.pos 67),(.pos 68)]),
   ((.exchange 66 63 1),[(.neg 66),(.neg 63),(.pos 67),(.pos 69)]),
   ((.exchange 67 1 5),[(.neg 67),(.neg 1),(.pos 56),(.pos 57),(.pos 63)]),
   ((.exchange 67 12 6),[(.neg 67),(.neg 12),(.pos 46),(.pos 50),(.pos 53)]),
   ((.exchange 67 16 5),[(.neg 67),(.neg 16),(.pos 56),(.pos 57),(.pos 60)])]

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



noncomputable def certificates_3 : List (Origin 70 272 × List Sat.Literal) :=
  [((.exchange 67 17 5),[(.neg 67),(.neg 17),(.pos 56),(.pos 60)]),
   ((.exchange 67 19 5),[(.neg 67),(.neg 19),(.pos 56),(.pos 57),(.pos 63)]),
   ((.exchange 67 29 2),[(.neg 67),(.neg 29),(.pos 66),(.pos 68)]),
   ((.exchange 67 31 2),[(.neg 67),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 67 32 2),[(.neg 67),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 67 34 2),[(.neg 67),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 67 37 5),[(.neg 67),(.neg 37),(.pos 56),(.pos 60)]),
   ((.exchange 67 41 5),[(.neg 67),(.neg 41),(.pos 57),(.pos 63)]),
   ((.exchange 67 48 2),[(.neg 67),(.neg 48),(.pos 65),(.pos 68)]),
   ((.exchange 67 49 2),[(.neg 67),(.neg 49),(.pos 66),(.pos 68)]),
   ((.exchange 67 51 2),[(.neg 67),(.neg 51),(.pos 65),(.pos 69)]),
   ((.exchange 67 52 2),[(.neg 67),(.neg 52),(.pos 66),(.pos 69)]),
   ((.exchange 67 55 5),[(.neg 67),(.neg 55),(.pos 56),(.pos 57)]),
   ((.exchange 67 58 5),[(.neg 67),(.neg 58),(.pos 56),(.pos 60)]),
   ((.exchange 68 5 3),[(.neg 68),(.neg 5),(.pos 65),(.pos 66),(.pos 67)]),
   ((.exchange 68 6 6),[(.neg 68),(.neg 6),(.pos 48),(.pos 49)]),
   ((.exchange 68 9 3),[(.neg 68),(.neg 9),(.pos 65),(.pos 66),(.pos 69)]),
   ((.exchange 68 13 6),[(.neg 68),(.neg 13),(.pos 49),(.pos 54)]),
   ((.exchange 68 14 6),[(.neg 68),(.neg 14),(.pos 50),(.pos 54)]),
   ((.exchange 68 15 5),[(.neg 68),(.neg 15),(.pos 58),(.pos 59),(.pos 60)]),
   ((.exchange 68 17 5),[(.neg 68),(.neg 17),(.pos 58),(.pos 60)]),
   ((.exchange 68 26 3),[(.neg 68),(.neg 26),(.pos 65),(.pos 67)]),
   ((.exchange 68 32 3),[(.neg 68),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 68 33 3),[(.neg 68),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 68 36 5),[(.neg 68),(.neg 36),(.pos 58),(.pos 59)]),
   ((.exchange 68 38 6),[(.neg 68),(.neg 38),(.pos 49),(.pos 50)]),
   ((.exchange 68 51 6),[(.neg 68),(.neg 51),(.pos 48),(.pos 54)]),
   ((.exchange 68 52 3),[(.neg 68),(.neg 52),(.pos 66),(.pos 69)]),
   ((.exchange 68 52 6),[(.neg 68),(.neg 52),(.pos 49),(.pos 54)]),
   ((.exchange 68 53 6),[(.neg 68),(.neg 53),(.pos 50),(.pos 54)]),
   ((.exchange 68 56 5),[(.neg 68),(.neg 56),(.pos 58),(.pos 60)]),
   ((.exchange 68 57 3),[(.neg 68),(.neg 57),(.pos 66),(.pos 67)]),
   ((.exchange 68 61 5),[(.neg 68),(.neg 61),(.pos 58),(.pos 64)]),
   ((.exchange 68 62 5),[(.neg 68),(.neg 62),(.pos 59),(.pos 64)]),
   ((.exchange 69 0 4),[(.neg 69),(.neg 0),(.pos 65),(.pos 66),(.pos 67),(.pos 68)]),
   ((.exchange 69 0 5),[(.neg 69),(.neg 0),(.pos 61),(.pos 62),(.pos 63),(.pos 64)]),
   ((.exchange 69 1 5),[(.neg 69),(.neg 1),(.pos 61),(.pos 62),(.pos 63)]),
   ((.exchange 69 12 6),[(.neg 69),(.neg 12),(.pos 51),(.pos 54)]),
   ((.exchange 69 17 5),[(.neg 69),(.neg 17),(.pos 61),(.pos 63),(.pos 64)]),
   ((.exchange 69 24 5),[(.neg 69),(.neg 24),(.pos 63),(.pos 64)]),
   ((.exchange 69 27 4),[(.neg 69),(.neg 27),(.pos 66),(.pos 67)]),
   ((.exchange 69 28 4),[(.neg 69),(.neg 28),(.pos 65),(.pos 68)]),
   ((.exchange 69 38 4),[(.neg 69),(.neg 38),(.pos 66),(.pos 67),(.pos 68)]),
   ((.exchange 69 40 6),[(.neg 69),(.neg 40),(.pos 51),(.pos 53)]),
   ((.exchange 69 43 5),[(.neg 69),(.neg 43),(.pos 62),(.pos 64)]),
   ((.exchange 69 44 6),[(.neg 69),(.neg 44),(.pos 53),(.pos 54)]),
   ((.exchange 69 46 4),[(.neg 69),(.neg 46),(.pos 65),(.pos 67)]),
   ((.exchange 69 47 4),[(.neg 69),(.neg 47),(.pos 66),(.pos 67)]),
   ((.exchange 69 48 6),[(.neg 69),(.neg 48),(.pos 51),(.pos 54)]),
   ((.exchange 69 49 4),[(.neg 69),(.neg 49),(.pos 66),(.pos 68)]),
   ((.exchange 69 50 4),[(.neg 69),(.neg 50),(.pos 67),(.pos 68)]),
   ((.exchange 69 57 5),[(.neg 69),(.neg 57),(.pos 62),(.pos 63)]),
   ((.exchange 69 58 4),[(.neg 69),(.neg 58),(.pos 65),(.pos 68)]),
   ((.exchange 69 60 4),[(.neg 69),(.neg 60),(.pos 67),(.pos 68)]),
   ((.exchange 69 60 5),[(.neg 69),(.neg 60),(.pos 63),(.pos 64)]),
   (.newPoint,[(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 0),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 62),(.neg 60),(.neg 59),(.neg 57),(.neg 54),(.neg 53),(.neg 52),(.neg 49),(.neg 47),(.neg 44),(.neg 41),(.neg 38),(.pos 35),(.pos 36),(.pos 37),(.pos 39),(.pos 40),(.pos 42),(.pos 43),(.pos 45),(.pos 46),(.pos 48),(.pos 50),(.pos 51),(.pos 55),(.pos 56),(.pos 58),(.pos 61),(.pos 63),(.pos 65),(.pos 66)]),
   ((.excluded 1),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 61),(.neg 58),(.neg 56),(.neg 54),(.neg 51),(.neg 50),(.neg 48),(.neg 46),(.neg 44),(.neg 40),(.neg 37),(.pos 35),(.pos 36),(.pos 38),(.pos 39),(.pos 41),(.pos 42),(.pos 43),(.pos 45),(.pos 47),(.pos 49),(.pos 52),(.pos 53),(.pos 55),(.pos 57),(.pos 59),(.pos 60),(.pos 62),(.pos 65),(.pos 66)]),
   ((.excluded 2),[(.neg 69),(.neg 68),(.neg 67),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 54),(.pos 55),(.pos 64),(.pos 65),(.pos 66)]),
   ((.excluded 3),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 45),(.pos 55),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 4),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 45),(.pos 55),(.pos 65),(.pos 66)]),
   ((.excluded 5),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 47),(.neg 45),(.neg 41),(.neg 40),(.neg 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 42),(.pos 43),(.pos 44),(.pos 46),(.pos 48),(.pos 49),(.pos 50),(.pos 54),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 68)]),
   ((.excluded 6),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 55),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 47),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 56),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 7),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 44),(.pos 54),(.pos 64),(.pos 67)]),
   ((.excluded 8),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 44),(.pos 54),(.pos 64)]),
   ((.excluded 9),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 51),(.neg 49),(.neg 45),(.neg 44),(.neg 40),(.neg 38),(.neg 35),(.pos 36),(.pos 37),(.pos 39),(.pos 41),(.pos 42),(.pos 43),(.pos 46),(.pos 47),(.pos 48),(.pos 50),(.pos 52),(.pos 53),(.pos 58),(.pos 62),(.pos 67)]),
   ((.excluded 10),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 47),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 35),(.pos 36),(.pos 37),(.pos 39),(.pos 42),(.pos 43),(.pos 46),(.pos 48),(.pos 50),(.pos 58),(.pos 69)]),
   ((.excluded 11),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 47),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 35),(.pos 36),(.pos 37),(.pos 39),(.pos 42),(.pos 43),(.pos 46),(.pos 48),(.pos 50),(.pos 58)]),
   ((.excluded 12),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 40),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 41),(.pos 42),(.pos 43),(.pos 47),(.pos 52),(.pos 53),(.pos 62),(.pos 68)]),
   ((.excluded 13),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 40),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 41),(.pos 42),(.pos 43),(.pos 47),(.pos 52),(.pos 53),(.pos 62)]),
   ((.excluded 14),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 58),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 37),(.neg 35),(.pos 36),(.pos 38),(.pos 39),(.pos 40),(.pos 42),(.pos 43),(.pos 49),(.pos 51),(.pos 56),(.pos 57),(.pos 59),(.pos 60),(.pos 61),(.pos 63),(.pos 67)]),
   ((.excluded 15),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 58),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 37),(.neg 35),(.pos 36),(.pos 38),(.pos 39),(.pos 42),(.pos 43),(.pos 49),(.pos 57),(.pos 59),(.pos 60),(.pos 69)]),
   ((.excluded 16),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 58),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 37),(.neg 35),(.pos 36),(.pos 38),(.pos 39),(.pos 42),(.pos 43),(.pos 49),(.pos 57),(.pos 59),(.pos 60)]),
   ((.excluded 17),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 40),(.pos 42),(.pos 43),(.pos 51),(.pos 56),(.pos 61),(.pos 63),(.pos 68)]),
   ((.excluded 18),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 40),(.pos 42),(.pos 43),(.pos 51),(.pos 56),(.pos 61),(.pos 63)]),
   ((.excluded 19),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 67)]),
   ((.excluded 20),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 68)]),
   ((.excluded 21),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 69)]),
   ((.excluded 22),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43)]),
   ((.excluded 23),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 58),(.neg 55),(.neg 54),(.neg 51),(.neg 49),(.neg 45),(.neg 43),(.neg 42),(.neg 39),(.neg 36),(.pos 35),(.pos 37),(.pos 38),(.pos 40),(.pos 41),(.pos 44),(.pos 46),(.pos 47),(.pos 48),(.pos 50),(.pos 52),(.pos 53),(.pos 56),(.pos 57),(.pos 59),(.pos 60),(.pos 61),(.pos 63),(.pos 67)]),
   ((.excluded 24),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 44),(.neg 43),(.neg 42),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 41),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 25),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 51),(.neg 49),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 41),(.pos 46),(.pos 47),(.pos 48),(.pos 50),(.pos 52),(.pos 53),(.pos 64),(.pos 67)]),
   ((.excluded 26),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 51),(.neg 49),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 41),(.pos 46),(.pos 47),(.pos 48),(.pos 50),(.pos 52),(.pos 53),(.pos 67)]),
   ((.excluded 27),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 36),(.pos 35),(.pos 37),(.pos 40),(.pos 46),(.pos 48),(.pos 49),(.pos 50),(.pos 54),(.pos 56),(.pos 61),(.pos 63),(.pos 68)]),
   ((.excluded 28),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 36),(.pos 35),(.pos 37),(.pos 40),(.pos 46),(.pos 48),(.pos 50),(.pos 56),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 29),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 36),(.pos 35),(.pos 37),(.pos 40),(.pos 46),(.pos 48),(.pos 50),(.pos 56),(.pos 61),(.pos 63)]),
   ((.excluded 30),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 46),(.pos 48),(.pos 49),(.pos 50),(.pos 54),(.pos 62),(.pos 68)]),
   ((.excluded 31),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 46),(.pos 48),(.pos 49),(.pos 50),(.pos 54),(.pos 68)]),
   ((.excluded 32),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 61),(.neg 58),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 49),(.neg 47),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 36),(.neg 35),(.pos 37),(.pos 38),(.pos 44),(.pos 45),(.pos 46),(.pos 48),(.pos 50),(.pos 51),(.pos 55),(.pos 57),(.pos 59),(.pos 60),(.pos 62),(.pos 65),(.pos 66)]),
   ((.excluded 33),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 58),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 47),(.neg 45),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 36),(.neg 35),(.pos 37),(.pos 38),(.pos 44),(.pos 46),(.pos 48),(.pos 50),(.pos 57),(.pos 59),(.pos 60),(.pos 69)]),
   ((.excluded 34),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 58),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 47),(.neg 45),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 36),(.neg 35),(.pos 37),(.pos 38),(.pos 44),(.pos 46),(.pos 48),(.pos 50),(.pos 57),(.pos 59),(.pos 60)]),
   ((.excluded 35),[(.neg 69),(.neg 68),(.neg 67),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 49),(.neg 47),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 45),(.pos 46),(.pos 48),(.pos 50),(.pos 51),(.pos 55),(.pos 64),(.pos 65),(.pos 66)]),
   ((.excluded 36),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 49),(.neg 47),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 45),(.pos 46),(.pos 48),(.pos 50),(.pos 51),(.pos 55),(.pos 65),(.pos 66)]),
   ((.excluded 37),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 46),(.pos 48),(.pos 50),(.pos 62)]),
   ((.excluded 38),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 46),(.pos 48),(.pos 50),(.pos 64)]),
   ((.excluded 39),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 46),(.pos 48),(.pos 50),(.pos 69)]),
   ((.excluded 40),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 46),(.pos 48),(.pos 50)]),
   ((.excluded 41),[(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 40),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 42),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 58),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 40),(.pos 54),(.pos 56),(.pos 57),(.pos 59),(.pos 60),(.pos 61),(.pos 63),(.pos 67)]),
   ((.excluded 43),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 58),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 40),(.pos 56),(.pos 57),(.pos 59),(.pos 60),(.pos 61),(.pos 63),(.pos 67)]),
   ((.excluded 44),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 49),(.pos 56),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 45),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 56),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 46),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 62),(.neg 60),(.neg 59),(.neg 57),(.neg 54),(.neg 51),(.neg 50),(.neg 48),(.neg 46),(.neg 43),(.neg 42),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 41),(.pos 44),(.pos 45),(.pos 47),(.pos 49),(.pos 52),(.pos 53),(.pos 55),(.pos 56),(.pos 58),(.pos 61),(.pos 63),(.pos 65),(.pos 66)]),
   ((.excluded 47),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 55),(.neg 54),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 43),(.neg 42),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 41),(.pos 44),(.pos 47),(.pos 52),(.pos 53),(.pos 56),(.pos 61),(.pos 63),(.pos 68)]),
   ((.excluded 48),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 55),(.neg 54),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 43),(.neg 42),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 41),(.pos 44),(.pos 47),(.pos 52),(.pos 53),(.pos 56),(.pos 61),(.pos 63)]),
   ((.excluded 49),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 62),(.neg 60),(.neg 59),(.neg 57),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 45),(.pos 54),(.pos 55),(.pos 56),(.pos 58),(.pos 61),(.pos 63),(.pos 65),(.pos 66)]),
   ((.excluded 50),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 62),(.neg 60),(.neg 59),(.neg 57),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 45),(.pos 55),(.pos 56),(.pos 58),(.pos 61),(.pos 63),(.pos 65),(.pos 66)]),
   ((.excluded 51),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 49),(.pos 56),(.pos 61),(.pos 63)]),
   ((.excluded 52),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 54),(.pos 56),(.pos 61),(.pos 63)]),
   ((.excluded 53),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 56),(.pos 61),(.pos 63),(.pos 68)]),
   ((.excluded 54),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 56),(.pos 61),(.pos 63)]),
   ((.excluded 55),[(.neg 69),(.neg 68),(.neg 67),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 51),(.neg 50),(.neg 48),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 41),(.pos 45),(.pos 47),(.pos 49),(.pos 52),(.pos 53),(.pos 55),(.pos 64),(.pos 65),(.pos 66)]),
   ((.excluded 56),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 51),(.neg 50),(.neg 48),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 41),(.pos 45),(.pos 47),(.pos 49),(.pos 52),(.pos 53),(.pos 55),(.pos 65),(.pos 66)]),
   ((.excluded 57),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 61),(.neg 58),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 45),(.pos 54),(.pos 55),(.pos 57),(.pos 59),(.pos 60),(.pos 62),(.pos 65),(.pos 66)]),
   ((.excluded 58),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 61),(.neg 58),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 37),(.neg 36),(.neg 35),(.pos 38),(.pos 45),(.pos 55),(.pos 57),(.pos 59),(.pos 60),(.pos 62),(.pos 65),(.pos 66)]),
   ((.excluded 59),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 44),(.pos 45),(.pos 55),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 60),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 45),(.pos 55),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 61),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 44),(.pos 45),(.pos 55),(.pos 65),(.pos 66)]),
   ((.excluded 62),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 45),(.pos 54),(.pos 55),(.pos 65),(.pos 66)]),
   ((.excluded 63),[(.neg 69),(.neg 68),(.neg 67),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 45),(.pos 55),(.pos 64),(.pos 65),(.pos 66)]),
   ((.excluded 64),[(.neg 69),(.neg 68),(.neg 67),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 45),(.pos 55),(.pos 65),(.pos 66)]),
   ((.excluded 65),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 58),(.neg 56),(.neg 55),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 40),(.neg 39),(.neg 37),(.neg 36),(.pos 35),(.pos 38),(.pos 41),(.pos 47),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 57),(.pos 59),(.pos 60),(.pos 69)]),
   ((.excluded 66),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 56),(.neg 55),(.neg 54),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 40),(.neg 39),(.neg 37),(.neg 36),(.pos 35),(.pos 38),(.pos 41),(.pos 47),(.pos 52),(.pos 53),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 68)]),
   ((.excluded 67),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 58),(.neg 56),(.neg 55),(.neg 54),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 40),(.neg 39),(.neg 37),(.neg 36),(.pos 35),(.pos 38),(.pos 41),(.pos 47),(.pos 52),(.pos 53),(.pos 57),(.pos 59),(.pos 60)]),
   ((.excluded 68),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 41),(.pos 47),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 58),(.pos 69)]),
   ((.excluded 69),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 41),(.pos 47),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 69)]),
   ((.excluded 70),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 41),(.pos 47),(.pos 52),(.pos 53),(.pos 58)]),
   ((.excluded 71),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 41),(.pos 47),(.pos 52),(.pos 53),(.pos 64)])]

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



end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C73


end
end
end BundlePart0

