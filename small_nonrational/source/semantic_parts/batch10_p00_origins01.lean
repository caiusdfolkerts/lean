module
public import SemanticParts.Batch10P00Data
public import Consolidated.SemanticData
public import Mathlib.Data.Fin.Tuple.Basic
public import MatroidCatalogue.Definitions
public import MatroidChecked.BitsetSemanticChecks
public import MatroidChecked.FastSemanticChecks
public import MatroidChecked.BitsetOrigins
public import MatroidChecked.MaskOrigins

section BundlePart0
/- Source: MatroidChecked/SemanticChunks/Cases14Part01.lean -/




@[expose] public section
noncomputable section

/- Source: MatroidCatalogue/Cases/N8R4C67Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C67


noncomputable def certificates_2 : List (Origin 70 356 × List Sat.Literal) :=
  [((.exchange 53 30 4),[(.neg 53),(.neg 30),(.pos 50),(.pos 67)]),
   ((.exchange 53 31 2),[(.neg 53),(.neg 31),(.pos 51),(.pos 69)]),
   ((.exchange 53 32 2),[(.neg 53),(.neg 32),(.pos 52),(.pos 69)]),
   ((.exchange 53 36 4),[(.neg 53),(.neg 36),(.pos 46),(.pos 47),(.pos 50)]),
   ((.exchange 53 42 2),[(.neg 53),(.neg 42),(.pos 51),(.pos 54)]),
   ((.exchange 53 57 5),[(.neg 57),(.neg 53),(.pos 41),(.pos 63)]),
   ((.exchange 53 59 2),[(.neg 59),(.neg 53),(.pos 52),(.pos 54),(.pos 69)]),
   ((.exchange 53 62 2),[(.neg 62),(.neg 53),(.pos 52),(.pos 69)]),
   ((.exchange 53 64 5),[(.neg 64),(.neg 53),(.pos 44),(.pos 63)]),
   ((.exchange 53 65 4),[(.neg 65),(.neg 53),(.pos 46),(.pos 67)]),
   ((.exchange 53 68 4),[(.neg 68),(.neg 53),(.pos 50),(.pos 67)]),
   ((.exchange 54 3 5),[(.neg 54),(.neg 3),(.pos 42),(.pos 44)]),
   ((.exchange 54 30 4),[(.neg 54),(.neg 30),(.pos 50),(.pos 68)]),
   ((.exchange 54 31 3),[(.neg 54),(.neg 31),(.pos 51),(.pos 69)]),
   ((.exchange 54 37 4),[(.neg 54),(.neg 37),(.pos 48),(.pos 50)]),
   ((.exchange 54 58 4),[(.neg 58),(.neg 54),(.pos 48),(.pos 68)]),
   ((.exchange 54 60 5),[(.neg 60),(.neg 54),(.pos 44),(.pos 64)]),
   ((.exchange 55 9 6),[(.neg 55),(.neg 9),(.pos 39),(.pos 45)]),
   ((.exchange 55 23 0),[(.neg 55),(.neg 23),(.pos 59),(.pos 62)]),
   ((.exchange 55 29 0),[(.neg 55),(.neg 29),(.pos 59),(.pos 66)]),
   ((.exchange 55 32 0),[(.neg 55),(.neg 32),(.pos 62),(.pos 66)]),
   ((.exchange 55 42 6),[(.neg 55),(.neg 42),(.pos 36),(.pos 39)]),
   ((.exchange 55 51 1),[(.neg 55),(.neg 51),(.pos 61),(.pos 65)]),
   ((.exchange 55 51 6),[(.neg 55),(.neg 51),(.pos 39),(.pos 45)]),
   ((.exchange 55 69 0),[(.neg 69),(.neg 55),(.pos 62),(.pos 66)]),
   ((.exchange 56 9 6),[(.neg 56),(.neg 9),(.pos 35),(.pos 40),(.pos 46)]),
   ((.exchange 56 24 0),[(.neg 56),(.neg 24),(.pos 60),(.pos 63)]),
   ((.exchange 56 30 0),[(.neg 56),(.neg 30),(.pos 60),(.pos 67)]),
   ((.exchange 56 33 0),[(.neg 56),(.neg 33),(.pos 63),(.pos 67)]),
   ((.exchange 56 42 6),[(.neg 56),(.neg 42),(.pos 37),(.pos 40)]),
   ((.exchange 56 48 2),[(.neg 56),(.neg 48),(.pos 58),(.pos 65)]),
   ((.exchange 56 51 6),[(.neg 56),(.neg 51),(.pos 40),(.pos 46)]),
   ((.exchange 56 64 0),[(.neg 64),(.neg 56),(.pos 60),(.pos 63)]),
   ((.exchange 56 68 0),[(.neg 68),(.neg 56),(.pos 60),(.pos 67)]),
   ((.exchange 56 69 0),[(.neg 69),(.neg 56),(.pos 63),(.pos 67)]),
   ((.exchange 57 9 6),[(.neg 57),(.neg 9),(.pos 35),(.pos 41),(.pos 47)]),
   ((.exchange 57 23 2),[(.neg 57),(.neg 23),(.pos 59),(.pos 62)]),
   ((.exchange 57 29 2),[(.neg 57),(.neg 29),(.pos 59),(.pos 66)]),
   ((.exchange 57 32 2),[(.neg 57),(.neg 32),(.pos 62),(.pos 66)]),
   ((.exchange 57 33 1),[(.neg 57),(.neg 33),(.pos 63),(.pos 67)]),
   ((.exchange 57 42 6),[(.neg 57),(.neg 42),(.pos 35),(.pos 38),(.pos 41)]),
   ((.exchange 57 49 2),[(.neg 57),(.neg 49),(.pos 59),(.pos 66)]),
   ((.exchange 57 51 6),[(.neg 57),(.neg 51),(.pos 35),(.pos 41),(.pos 47)]),
   ((.exchange 57 64 2),[(.neg 64),(.neg 57),(.pos 59),(.pos 62)]),
   ((.exchange 57 69 1),[(.neg 69),(.neg 57),(.pos 63),(.pos 67)]),
   ((.exchange 57 69 2),[(.neg 69),(.neg 57),(.pos 62),(.pos 66)]),
   ((.exchange 58 6 6),[(.neg 58),(.neg 6),(.pos 36),(.pos 48)]),
   ((.exchange 58 7 6),[(.neg 58),(.neg 7),(.pos 37),(.pos 48)]),
   ((.exchange 58 18 0),[(.neg 58),(.neg 18),(.pos 59),(.pos 60)]),
   ((.exchange 58 25 3),[(.neg 58),(.neg 25),(.pos 55),(.pos 65)]),
   ((.exchange 58 29 0),[(.neg 58),(.neg 29),(.pos 59),(.pos 68)]),
   ((.exchange 58 30 0),[(.neg 58),(.neg 30),(.pos 60),(.pos 68)]),
   ((.exchange 58 45 6),[(.neg 58),(.neg 45),(.pos 36),(.pos 48)]),
   ((.exchange 58 46 6),[(.neg 58),(.neg 46),(.pos 37),(.pos 48)]),
   ((.exchange 58 49 0),[(.neg 58),(.neg 49),(.pos 59),(.pos 68)]),
   ((.exchange 58 50 0),[(.neg 58),(.neg 50),(.pos 60),(.pos 68)]),
   ((.exchange 58 66 0),[(.neg 66),(.neg 58),(.pos 59),(.pos 68)]),
   ((.exchange 58 67 0),[(.neg 67),(.neg 58),(.pos 60),(.pos 68)]),
   ((.exchange 59 8 6),[(.neg 59),(.neg 8),(.pos 38),(.pos 49)]),
   ((.exchange 59 14 1),[(.neg 59),(.neg 14),(.pos 60),(.pos 64),(.pos 68)]),
   ((.exchange 59 21 3),[(.neg 59),(.neg 21),(.pos 57),(.pos 62)]),
   ((.exchange 59 31 1),[(.neg 59),(.neg 31),(.pos 58),(.pos 64),(.pos 68)]),
   ((.exchange 59 40 3),[(.neg 59),(.neg 40),(.pos 55),(.pos 57),(.pos 62)]),
   ((.exchange 59 41 3),[(.neg 59),(.neg 41),(.pos 57),(.pos 62)]),
   ((.exchange 59 44 1),[(.neg 59),(.neg 44),(.pos 60),(.pos 64)]),
   ((.exchange 59 47 3),[(.neg 59),(.neg 47),(.pos 57),(.pos 66)]),
   ((.exchange 59 47 6),[(.neg 59),(.neg 47),(.pos 38),(.pos 49)]),
   ((.exchange 59 48 1),[(.neg 59),(.neg 48),(.pos 58),(.pos 68)]),
   ((.exchange 59 51 6),[(.neg 59),(.neg 51),(.pos 36),(.pos 43),(.pos 49)]),
   ((.exchange 59 54 1),[(.neg 59),(.neg 54),(.pos 64),(.pos 68)]),
   ((.exchange 59 61 3),[(.neg 61),(.neg 59),(.pos 55),(.pos 62)]),
   ((.exchange 59 63 1),[(.neg 63),(.neg 59),(.pos 60),(.pos 64)]),
   ((.exchange 60 2 2),[(.neg 60),(.neg 2),(.pos 58),(.pos 59),(.pos 64)]),
   ((.exchange 60 2 6),[(.neg 60),(.neg 2),(.pos 37),(.pos 38),(.pos 44)]),
   ((.exchange 60 4 6),[(.neg 60),(.neg 4),(.pos 38),(.pos 44)]),
   ((.exchange 60 7 6),[(.neg 60),(.neg 7),(.pos 37),(.pos 50)]),
   ((.exchange 60 26 3),[(.neg 60),(.neg 26),(.pos 56),(.pos 67)]),
   ((.exchange 60 31 2),[(.neg 60),(.neg 31),(.pos 58),(.pos 64),(.pos 68)]),
   ((.exchange 60 32 3),[(.neg 60),(.neg 32),(.pos 57),(.pos 63),(.pos 67)]),
   ((.exchange 60 34 2),[(.neg 60),(.neg 34),(.pos 64),(.pos 68)]),
   ((.exchange 60 39 2),[(.neg 60),(.neg 39),(.pos 58),(.pos 59),(.pos 64)]),
   ((.exchange 60 39 6),[(.neg 60),(.neg 39),(.pos 37),(.pos 38),(.pos 44)]),
   ((.exchange 60 49 6),[(.neg 60),(.neg 49),(.pos 38),(.pos 50)]),
   ((.exchange 60 53 6),[(.neg 60),(.neg 53),(.pos 44),(.pos 50)]),
   ((.exchange 60 54 2),[(.neg 60),(.neg 54),(.pos 64),(.pos 68)]),
   ((.exchange 60 61 3),[(.neg 61),(.neg 60),(.pos 56),(.pos 63)]),
   ((.exchange 60 62 2),[(.neg 62),(.neg 60),(.pos 59),(.pos 64)]),
   ((.exchange 60 65 3),[(.neg 65),(.neg 60),(.pos 56),(.pos 67)]),
   ((.exchange 60 66 2),[(.neg 66),(.neg 60),(.pos 59),(.pos 68)]),
   ((.exchange 60 66 3),[(.neg 66),(.neg 60),(.pos 57),(.pos 67)]),
   ((.exchange 60 69 3),[(.neg 69),(.neg 60),(.pos 63),(.pos 67)]),
   ((.exchange 61 21 0),[(.neg 61),(.neg 21),(.pos 62),(.pos 63)]),
   ((.exchange 61 25 4),[(.neg 61),(.neg 25),(.pos 55),(.pos 65)]),
   ((.exchange 61 26 4),[(.neg 61),(.neg 26),(.pos 56),(.pos 65)]),
   ((.exchange 61 32 0),[(.neg 61),(.neg 32),(.pos 62),(.pos 69)]),
   ((.exchange 61 33 0),[(.neg 61),(.neg 33),(.pos 63),(.pos 69)]),
   ((.exchange 61 67 0),[(.neg 67),(.neg 61),(.pos 63),(.pos 69)]),
   ((.exchange 62 2 6),[(.neg 62),(.neg 2),(.pos 39),(.pos 43)]),
   ((.exchange 62 9 6),[(.neg 62),(.neg 9),(.pos 39),(.pos 52)]),
   ((.exchange 62 12 1),[(.neg 62),(.neg 12),(.pos 61),(.pos 64),(.pos 69)]),
   ((.exchange 62 14 6),[(.neg 62),(.neg 14),(.pos 41),(.pos 43),(.pos 52)]),
   ((.exchange 62 16 4),[(.neg 62),(.neg 16),(.pos 55),(.pos 59)]),
   ((.exchange 62 18 4),[(.neg 62),(.neg 18),(.pos 57),(.pos 59)]),
   ((.exchange 62 24 1),[(.neg 62),(.neg 24),(.pos 63),(.pos 64)]),
   ((.exchange 62 25 4),[(.neg 62),(.neg 25),(.pos 55),(.pos 66)]),
   ((.exchange 62 27 4),[(.neg 62),(.neg 27),(.pos 57),(.pos 66)]),
   ((.exchange 62 31 1),[(.neg 62),(.neg 31),(.pos 61),(.pos 69)]),
   ((.exchange 62 37 6),[(.neg 62),(.neg 37),(.pos 39),(.pos 41),(.pos 43)]),
   ((.exchange 62 45 6),[(.neg 62),(.neg 45),(.pos 39),(.pos 52)]),
   ((.exchange 62 49 4),[(.neg 62),(.neg 49),(.pos 59),(.pos 66)]),
   ((.exchange 62 51 1),[(.neg 62),(.neg 51),(.pos 61),(.pos 69)]),
   ((.exchange 62 51 6),[(.neg 62),(.neg 51),(.pos 39),(.pos 52)]),
   ((.exchange 62 58 4),[(.neg 62),(.neg 58),(.pos 55),(.pos 59)]),
   ((.exchange 62 60 4),[(.neg 62),(.neg 60),(.pos 57),(.pos 59)]),
   ((.exchange 62 65 1),[(.neg 65),(.neg 62),(.pos 61),(.pos 69)]),
   ((.exchange 62 67 4),[(.neg 67),(.neg 62),(.pos 57),(.pos 66)]),
   ((.exchange 63 2 2),[(.neg 63),(.neg 2),(.pos 61),(.pos 62),(.pos 64)]),
   ((.exchange 63 2 6),[(.neg 63),(.neg 2),(.pos 40),(.pos 41),(.pos 44)]),
   ((.exchange 63 4 6),[(.neg 63),(.neg 4),(.pos 41),(.pos 44)]),
   ((.exchange 63 9 6),[(.neg 63),(.neg 9),(.pos 40),(.pos 41),(.pos 53)]),
   ((.exchange 63 11 6),[(.neg 63),(.neg 11),(.pos 41),(.pos 53)]),
   ((.exchange 63 12 2),[(.neg 63),(.neg 12),(.pos 61),(.pos 64),(.pos 69)]),
   ((.exchange 63 14 6),[(.neg 63),(.neg 14),(.pos 44),(.pos 53)]),
   ((.exchange 63 16 4),[(.neg 63),(.neg 16),(.pos 56),(.pos 57),(.pos 60)]),
   ((.exchange 63 17 4),[(.neg 63),(.neg 17),(.pos 56),(.pos 60)]),
   ((.exchange 63 18 4),[(.neg 63),(.neg 18),(.pos 57),(.pos 60)]),
   ((.exchange 63 25 4),[(.neg 63),(.neg 25),(.pos 56),(.pos 57),(.pos 67)]),
   ((.exchange 63 26 4),[(.neg 63),(.neg 26),(.pos 56),(.pos 67)])]

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



noncomputable def certificates_3 : List (Origin 70 356 × List Sat.Literal) :=
  [((.exchange 63 28 2),[(.neg 63),(.neg 28),(.pos 61),(.pos 64),(.pos 69)]),
   ((.exchange 63 30 4),[(.neg 63),(.neg 30),(.pos 60),(.pos 67)]),
   ((.exchange 63 31 2),[(.neg 63),(.neg 31),(.pos 61),(.pos 69)]),
   ((.exchange 63 37 4),[(.neg 63),(.neg 37),(.pos 56),(.pos 60)]),
   ((.exchange 63 38 6),[(.neg 63),(.neg 38),(.pos 41),(.pos 44)]),
   ((.exchange 63 39 2),[(.neg 63),(.neg 39),(.pos 61),(.pos 62)]),
   ((.exchange 63 43 6),[(.neg 63),(.neg 43),(.pos 41),(.pos 44)]),
   ((.exchange 63 47 4),[(.neg 63),(.neg 47),(.pos 57),(.pos 67)]),
   ((.exchange 63 47 6),[(.neg 63),(.neg 47),(.pos 41),(.pos 53)]),
   ((.exchange 63 51 6),[(.neg 63),(.neg 51),(.pos 40),(.pos 53)]),
   ((.exchange 63 52 6),[(.neg 63),(.neg 52),(.pos 41),(.pos 53)]),
   ((.exchange 63 65 2),[(.neg 65),(.neg 63),(.pos 61),(.pos 69)]),
   ((.exchange 63 65 4),[(.neg 65),(.neg 63),(.pos 56),(.pos 67)]),
   ((.exchange 63 68 4),[(.neg 68),(.neg 63),(.pos 60),(.pos 67)]),
   ((.exchange 64 14 6),[(.neg 64),(.neg 14),(.pos 44),(.pos 54)]),
   ((.exchange 64 21 3),[(.neg 64),(.neg 21),(.pos 62),(.pos 63)]),
   ((.exchange 64 30 4),[(.neg 64),(.neg 30),(.pos 60),(.pos 68)]),
   ((.exchange 64 32 3),[(.neg 64),(.neg 32),(.pos 62),(.pos 69)]),
   ((.exchange 64 33 3),[(.neg 64),(.neg 33),(.pos 63),(.pos 69)]),
   ((.exchange 64 38 4),[(.neg 64),(.neg 38),(.pos 59),(.pos 60)]),
   ((.exchange 65 14 6),[(.neg 65),(.neg 14),(.pos 46),(.pos 48),(.pos 51)]),
   ((.exchange 65 21 5),[(.neg 65),(.neg 21),(.pos 55),(.pos 56),(.pos 61)]),
   ((.exchange 65 27 0),[(.neg 65),(.neg 27),(.pos 66),(.pos 67)]),
   ((.exchange 65 29 0),[(.neg 65),(.neg 29),(.pos 66),(.pos 68)]),
   ((.exchange 65 30 0),[(.neg 65),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 65 32 0),[(.neg 65),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 65 33 0),[(.neg 65),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 65 34 0),[(.neg 65),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 65 41 6),[(.neg 65),(.neg 41),(.pos 45),(.pos 46),(.pos 51)]),
   ((.exchange 65 42 6),[(.neg 65),(.neg 42),(.pos 48),(.pos 51)]),
   ((.exchange 65 47 0),[(.neg 65),(.neg 47),(.pos 66),(.pos 67)]),
   ((.exchange 65 50 0),[(.neg 65),(.neg 50),(.pos 67),(.pos 68)]),
   ((.exchange 65 52 0),[(.neg 65),(.neg 52),(.pos 66),(.pos 69)]),
   ((.exchange 65 54 0),[(.neg 65),(.neg 54),(.pos 68),(.pos 69)]),
   ((.exchange 65 57 0),[(.neg 65),(.neg 57),(.pos 66),(.pos 67)]),
   ((.exchange 65 59 0),[(.neg 65),(.neg 59),(.pos 66),(.pos 68)]),
   ((.exchange 65 60 0),[(.neg 65),(.neg 60),(.pos 67),(.pos 68)]),
   ((.exchange 65 63 0),[(.neg 65),(.neg 63),(.pos 67),(.pos 69)]),
   ((.exchange 65 64 0),[(.neg 65),(.neg 64),(.pos 68),(.pos 69)]),
   ((.exchange 66 8 6),[(.neg 66),(.neg 8),(.pos 47),(.pos 49)]),
   ((.exchange 66 9 6),[(.neg 66),(.neg 9),(.pos 45),(.pos 52)]),
   ((.exchange 66 12 6),[(.neg 66),(.neg 12),(.pos 45),(.pos 49),(.pos 52)]),
   ((.exchange 66 21 5),[(.neg 66),(.neg 21),(.pos 57),(.pos 62)]),
   ((.exchange 66 23 5),[(.neg 66),(.neg 23),(.pos 59),(.pos 62)]),
   ((.exchange 66 28 1),[(.neg 66),(.neg 28),(.pos 65),(.pos 68)]),
   ((.exchange 66 30 1),[(.neg 66),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 66 31 1),[(.neg 66),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 66 33 1),[(.neg 66),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 66 36 5),[(.neg 66),(.neg 36),(.pos 55),(.pos 59)]),
   ((.exchange 66 40 5),[(.neg 66),(.neg 40),(.pos 55),(.pos 57),(.pos 62)]),
   ((.exchange 66 41 5),[(.neg 66),(.neg 41),(.pos 57),(.pos 62)]),
   ((.exchange 66 46 1),[(.neg 66),(.neg 46),(.pos 65),(.pos 67)]),
   ((.exchange 66 48 6),[(.neg 66),(.neg 48),(.pos 45),(.pos 49)]),
   ((.exchange 66 50 1),[(.neg 66),(.neg 50),(.pos 67),(.pos 68)]),
   ((.exchange 66 51 1),[(.neg 66),(.neg 51),(.pos 65),(.pos 69)]),
   ((.exchange 66 51 6),[(.neg 66),(.neg 51),(.pos 45),(.pos 52)]),
   ((.exchange 66 54 1),[(.neg 66),(.neg 54),(.pos 68),(.pos 69)]),
   ((.exchange 66 56 1),[(.neg 66),(.neg 56),(.pos 65),(.pos 67)]),
   ((.exchange 66 58 1),[(.neg 66),(.neg 58),(.pos 65),(.pos 68)]),
   ((.exchange 66 58 5),[(.neg 66),(.neg 58),(.pos 55),(.pos 59)]),
   ((.exchange 67 7 6),[(.neg 67),(.neg 7),(.pos 46),(.pos 50)]),
   ((.exchange 67 14 6),[(.neg 67),(.neg 14),(.pos 50),(.pos 53)]),
   ((.exchange 67 16 5),[(.neg 67),(.neg 16),(.pos 56),(.pos 57),(.pos 60)]),
   ((.exchange 67 18 5),[(.neg 67),(.neg 18),(.pos 57),(.pos 60)]),
   ((.exchange 67 20 5),[(.neg 67),(.neg 20),(.pos 56),(.pos 63)]),
   ((.exchange 67 21 5),[(.neg 67),(.neg 21),(.pos 57),(.pos 63)]),
   ((.exchange 67 24 5),[(.neg 67),(.neg 24),(.pos 60),(.pos 63)]),
   ((.exchange 67 29 2),[(.neg 67),(.neg 29),(.pos 66),(.pos 68)]),
   ((.exchange 67 31 2),[(.neg 67),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 67 34 2),[(.neg 67),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 67 37 5),[(.neg 67),(.neg 37),(.pos 56),(.pos 60)]),
   ((.exchange 67 38 5),[(.neg 67),(.neg 38),(.pos 57),(.pos 60)]),
   ((.exchange 67 41 5),[(.neg 67),(.neg 41),(.pos 57),(.pos 63)]),
   ((.exchange 67 45 2),[(.neg 67),(.neg 45),(.pos 65),(.pos 66)]),
   ((.exchange 67 49 6),[(.neg 67),(.neg 49),(.pos 47),(.pos 50)]),
   ((.exchange 67 51 2),[(.neg 67),(.neg 51),(.pos 65),(.pos 69)]),
   ((.exchange 67 51 6),[(.neg 67),(.neg 51),(.pos 46),(.pos 53)]),
   ((.exchange 67 52 6),[(.neg 67),(.neg 52),(.pos 47),(.pos 53)]),
   ((.exchange 67 54 2),[(.neg 67),(.neg 54),(.pos 68),(.pos 69)]),
   ((.exchange 67 54 6),[(.neg 67),(.neg 54),(.pos 50),(.pos 53)]),
   ((.exchange 67 55 2),[(.neg 67),(.neg 55),(.pos 65),(.pos 66)]),
   ((.exchange 67 59 2),[(.neg 67),(.neg 59),(.pos 66),(.pos 68)]),
   ((.exchange 67 62 2),[(.neg 67),(.neg 62),(.pos 66),(.pos 69)]),
   ((.exchange 67 62 5),[(.neg 67),(.neg 62),(.pos 57),(.pos 63)]),
   ((.exchange 67 64 2),[(.neg 67),(.neg 64),(.pos 68),(.pos 69)]),
   ((.exchange 67 64 5),[(.neg 67),(.neg 64),(.pos 60),(.pos 63)]),
   ((.exchange 68 2 5),[(.neg 68),(.neg 2),(.pos 58),(.pos 59),(.pos 64)]),
   ((.exchange 68 3 5),[(.neg 68),(.neg 3),(.pos 58),(.pos 60),(.pos 64)]),
   ((.exchange 68 6 6),[(.neg 68),(.neg 6),(.pos 48),(.pos 49)]),
   ((.exchange 68 12 6),[(.neg 68),(.neg 12),(.pos 48),(.pos 54)]),
   ((.exchange 68 14 6),[(.neg 68),(.neg 14),(.pos 50),(.pos 54)]),
   ((.exchange 68 24 5),[(.neg 68),(.neg 24),(.pos 60),(.pos 64)]),
   ((.exchange 68 26 3),[(.neg 68),(.neg 26),(.pos 65),(.pos 67)]),
   ((.exchange 68 31 3),[(.neg 68),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 68 32 3),[(.neg 68),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 68 33 3),[(.neg 68),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 68 39 5),[(.neg 68),(.neg 39),(.pos 58),(.pos 59),(.pos 64)]),
   ((.exchange 68 41 6),[(.neg 68),(.neg 41),(.pos 49),(.pos 50),(.pos 54)]),
   ((.exchange 68 42 6),[(.neg 68),(.neg 42),(.pos 48),(.pos 54)]),
   ((.exchange 68 45 6),[(.neg 68),(.neg 45),(.pos 48),(.pos 49)]),
   ((.exchange 68 46 6),[(.neg 68),(.neg 46),(.pos 48),(.pos 50)]),
   ((.exchange 68 51 3),[(.neg 68),(.neg 51),(.pos 65),(.pos 69)]),
   ((.exchange 68 52 3),[(.neg 68),(.neg 52),(.pos 66),(.pos 69)]),
   ((.exchange 68 55 3),[(.neg 68),(.neg 55),(.pos 65),(.pos 66)]),
   ((.exchange 68 57 5),[(.neg 68),(.neg 57),(.pos 59),(.pos 60)]),
   ((.exchange 68 62 3),[(.neg 68),(.neg 62),(.pos 66),(.pos 69)]),
   ((.exchange 69 10 6),[(.neg 69),(.neg 10),(.pos 51),(.pos 53)]),
   ((.exchange 69 14 6),[(.neg 69),(.neg 14),(.pos 53),(.pos 54)]),
   ((.exchange 69 24 5),[(.neg 69),(.neg 24),(.pos 63),(.pos 64)]),
   ((.exchange 69 25 4),[(.neg 69),(.neg 25),(.pos 65),(.pos 66)]),
   ((.exchange 69 26 4),[(.neg 69),(.neg 26),(.pos 65),(.pos 67)]),
   ((.exchange 69 27 4),[(.neg 69),(.neg 27),(.pos 66),(.pos 67)]),
   ((.exchange 69 28 4),[(.neg 69),(.neg 28),(.pos 65),(.pos 68)]),
   ((.exchange 69 39 5),[(.neg 69),(.neg 39),(.pos 61),(.pos 62)]),
   ((.exchange 69 42 6),[(.neg 69),(.neg 42),(.pos 51),(.pos 54)]),
   ((.exchange 69 45 4),[(.neg 69),(.neg 45),(.pos 65),(.pos 66)]),
   ((.exchange 69 45 6),[(.neg 69),(.neg 45),(.pos 51),(.pos 52)]),
   ((.exchange 69 46 4),[(.neg 69),(.neg 46),(.pos 65),(.pos 67)]),
   ((.exchange 69 46 6),[(.neg 69),(.neg 46),(.pos 51),(.pos 53)]),
   ((.exchange 69 48 4),[(.neg 69),(.neg 48),(.pos 65),(.pos 68)]),
   ((.exchange 69 48 6),[(.neg 69),(.neg 48),(.pos 51),(.pos 54)]),
   ((.exchange 69 49 4),[(.neg 69),(.neg 49),(.pos 66),(.pos 68)]),
   ((.exchange 69 50 4),[(.neg 69),(.neg 50),(.pos 67),(.pos 68)]),
   ((.exchange 69 50 6),[(.neg 69),(.neg 50),(.pos 53),(.pos 54)]),
   ((.exchange 69 55 4),[(.neg 69),(.neg 55),(.pos 65),(.pos 66)]),
   ((.exchange 69 55 5),[(.neg 69),(.neg 55),(.pos 61),(.pos 62)]),
   ((.exchange 69 56 4),[(.neg 69),(.neg 56),(.pos 65),(.pos 67)]),
   ((.exchange 69 56 5),[(.neg 69),(.neg 56),(.pos 61),(.pos 63)])]

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



end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C67


end
end
end BundlePart0

