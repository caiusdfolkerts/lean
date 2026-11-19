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


noncomputable def certificates_0 : List (Origin 70 434 × List Sat.Literal) :=
  [((.fixed 0),[(.pos 0)]),
   ((.fixed 1),[(.pos 1)]),
   ((.fixed 2),[(.pos 2)]),
   ((.fixed 3),[(.pos 3)]),
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
   ((.fixed 27),[(.pos 27)]),
   ((.fixed 28),[(.pos 28)]),
   ((.fixed 29),[(.pos 29)]),
   ((.fixed 30),[(.pos 30)]),
   ((.fixed 31),[(.pos 31)]),
   ((.fixed 32),[(.pos 32)]),
   ((.fixed 33),[(.pos 33)]),
   ((.fixed 34),[(.pos 34)]),
   ((.exchange 0 41 0),[(.neg 41),(.neg 0),(.pos 4),(.pos 38)]),
   ((.exchange 0 45 3),[(.neg 45),(.neg 0),(.pos 5),(.pos 35)]),
   ((.exchange 0 46 3),[(.neg 46),(.neg 0),(.pos 5),(.pos 35)]),
   ((.exchange 0 47 3),[(.neg 47),(.neg 0),(.pos 5),(.pos 35)]),
   ((.exchange 0 55 2),[(.neg 55),(.neg 0),(.pos 16),(.pos 36)]),
   ((.exchange 0 58 2),[(.neg 58),(.neg 0),(.pos 16),(.pos 36)]),
   ((.exchange 0 59 2),[(.neg 59),(.neg 0),(.pos 16),(.pos 36)]),
   ((.exchange 1 38 0),[(.neg 38),(.neg 1),(.pos 4),(.pos 41)]),
   ((.exchange 1 43 0),[(.neg 43),(.neg 1),(.pos 4),(.pos 41)]),
   ((.exchange 1 44 0),[(.neg 44),(.neg 1),(.pos 4),(.pos 41)]),
   ((.exchange 1 56 1),[(.neg 56),(.neg 1),(.pos 20),(.pos 40)]),
   ((.exchange 1 61 1),[(.neg 61),(.neg 1),(.pos 20),(.pos 40)]),
   ((.exchange 1 63 1),[(.neg 63),(.neg 1),(.pos 20),(.pos 40)]),
   ((.exchange 2 41 0),[(.neg 41),(.neg 2),(.pos 4),(.pos 43)]),
   ((.exchange 2 48 1),[(.neg 48),(.neg 2),(.pos 12),(.pos 42)]),
   ((.exchange 2 51 1),[(.neg 51),(.neg 2),(.pos 12),(.pos 42)]),
   ((.exchange 2 54 1),[(.neg 54),(.neg 2),(.pos 12),(.pos 42)]),
   ((.exchange 3 41 0),[(.neg 41),(.neg 3),(.pos 4),(.pos 44)]),
   ((.exchange 6 35 3),[(.neg 35),(.neg 6),(.pos 5),(.pos 45)]),
   ((.exchange 6 42 1),[(.neg 42),(.neg 6),(.pos 12),(.pos 48)]),
   ((.exchange 6 46 3),[(.neg 46),(.neg 6),(.pos 5),(.pos 45)]),
   ((.exchange 6 47 3),[(.neg 47),(.neg 6),(.pos 5),(.pos 45)]),
   ((.exchange 6 51 1),[(.neg 51),(.neg 6),(.pos 12),(.pos 48)]),
   ((.exchange 6 54 1),[(.neg 54),(.neg 6),(.pos 12),(.pos 48)]),
   ((.exchange 7 35 3),[(.neg 35),(.neg 7),(.pos 5),(.pos 46)]),
   ((.exchange 7 45 3),[(.neg 45),(.neg 7),(.pos 5),(.pos 46)]),
   ((.exchange 7 47 3),[(.neg 47),(.neg 7),(.pos 5),(.pos 46)]),
   ((.exchange 8 35 3),[(.neg 35),(.neg 8),(.pos 5),(.pos 47)]),
   ((.exchange 8 45 3),[(.neg 45),(.neg 8),(.pos 5),(.pos 47)]),
   ((.exchange 8 46 3),[(.neg 46),(.neg 8),(.pos 5),(.pos 47)]),
   ((.exchange 9 42 1),[(.neg 42),(.neg 9),(.pos 12),(.pos 51)]),
   ((.exchange 9 48 1),[(.neg 48),(.neg 9),(.pos 12),(.pos 51)]),
   ((.exchange 9 54 1),[(.neg 54),(.neg 9),(.pos 12),(.pos 51)]),
   ((.exchange 13 42 1),[(.neg 42),(.neg 13),(.pos 12),(.pos 54)]),
   ((.exchange 13 48 1),[(.neg 48),(.neg 13),(.pos 12),(.pos 54)]),
   ((.exchange 13 51 1),[(.neg 51),(.neg 13),(.pos 12),(.pos 54)]),
   ((.exchange 15 36 2),[(.neg 36),(.neg 15),(.pos 16),(.pos 55)]),
   ((.exchange 15 40 1),[(.neg 40),(.neg 15),(.pos 20),(.pos 56)]),
   ((.exchange 15 58 2),[(.neg 58),(.neg 15),(.pos 16),(.pos 55)]),
   ((.exchange 15 59 2),[(.neg 59),(.neg 15),(.pos 16),(.pos 55)]),
   ((.exchange 15 61 1),[(.neg 61),(.neg 15),(.pos 20),(.pos 56)]),
   ((.exchange 15 63 1),[(.neg 63),(.neg 15),(.pos 20),(.pos 56)]),
   ((.exchange 17 36 2),[(.neg 36),(.neg 17),(.pos 16),(.pos 58)]),
   ((.exchange 17 55 2),[(.neg 55),(.neg 17),(.pos 16),(.pos 58)]),
   ((.exchange 17 59 2),[(.neg 59),(.neg 17),(.pos 16),(.pos 58)]),
   ((.exchange 18 36 2),[(.neg 36),(.neg 18),(.pos 16),(.pos 59)]),
   ((.exchange 18 55 2),[(.neg 55),(.neg 18),(.pos 16),(.pos 59)]),
   ((.exchange 18 58 2),[(.neg 58),(.neg 18),(.pos 16),(.pos 59)]),
   ((.exchange 19 40 1),[(.neg 40),(.neg 19),(.pos 20),(.pos 61)]),
   ((.exchange 19 56 1),[(.neg 56),(.neg 19),(.pos 20),(.pos 61)]),
   ((.exchange 19 63 1),[(.neg 63),(.neg 19),(.pos 20),(.pos 61)]),
   ((.exchange 21 40 1),[(.neg 40),(.neg 21),(.pos 20),(.pos 63)]),
   ((.exchange 21 56 1),[(.neg 56),(.neg 21),(.pos 20),(.pos 63)]),
   ((.exchange 21 61 1),[(.neg 61),(.neg 21),(.pos 20),(.pos 63)]),
   ((.exchange 35 2 2),[(.neg 35),(.neg 2),(.pos 36),(.pos 39)]),
   ((.exchange 35 3 1),[(.neg 35),(.neg 3),(.pos 37),(.pos 40)]),
   ((.exchange 35 17 1),[(.neg 35),(.neg 17),(.pos 37),(.pos 56)]),
   ((.exchange 35 18 0),[(.neg 35),(.neg 18),(.pos 38),(.pos 57)]),
   ((.exchange 35 58 1),[(.neg 58),(.neg 35),(.pos 37),(.pos 56)]),
   ((.exchange 35 64 1),[(.neg 64),(.neg 35),(.pos 37),(.pos 40),(.pos 56)]),
   ((.exchange 35 64 2),[(.neg 64),(.neg 35),(.pos 36),(.pos 39),(.pos 55)]),
   ((.exchange 36 3 1),[(.neg 36),(.neg 3),(.pos 37),(.pos 42)]),
   ((.exchange 36 8 0),[(.neg 36),(.neg 8),(.pos 38),(.pos 49)]),
   ((.exchange 36 9 3),[(.neg 36),(.neg 9),(.pos 39),(.pos 45)]),
   ((.exchange 36 14 1),[(.neg 36),(.neg 14),(.pos 37),(.pos 42),(.pos 48)]),
   ((.exchange 36 17 1),[(.neg 36),(.neg 17),(.pos 37),(.pos 58)]),
   ((.exchange 37 1 3),[(.neg 37),(.neg 1),(.pos 35),(.pos 40)]),
   ((.exchange 37 2 2),[(.neg 37),(.neg 2),(.pos 36),(.pos 42)]),
   ((.exchange 37 8 0),[(.neg 37),(.neg 8),(.pos 38),(.pos 50)]),
   ((.exchange 37 10 3),[(.neg 37),(.neg 10),(.pos 40),(.pos 46)]),
   ((.exchange 37 18 0),[(.neg 37),(.neg 18),(.pos 38),(.pos 60)]),
   ((.exchange 37 23 0),[(.neg 37),(.neg 23),(.pos 38),(.pos 44),(.pos 60)]),
   ((.exchange 37 26 3),[(.neg 37),(.neg 26),(.pos 46),(.pos 56)]),
   ((.exchange 37 30 0),[(.neg 37),(.neg 30),(.pos 50),(.pos 60)]),
   ((.exchange 37 43 2),[(.neg 43),(.neg 37),(.pos 36),(.pos 42)]),
   ((.exchange 37 51 3),[(.neg 51),(.neg 37),(.pos 40),(.pos 46)]),
   ((.exchange 37 53 3),[(.neg 53),(.neg 37),(.pos 40),(.pos 46)]),
   ((.exchange 37 57 3),[(.neg 57),(.neg 37),(.pos 35),(.pos 56)]),
   ((.exchange 37 62 2),[(.neg 62),(.neg 37),(.pos 36),(.pos 42),(.pos 58)]),
   ((.exchange 37 67 3),[(.neg 67),(.neg 37),(.pos 46),(.pos 56)]),
   ((.exchange 37 68 0),[(.neg 68),(.neg 37),(.pos 50),(.pos 60)]),
   ((.exchange 37 68 2),[(.neg 68),(.neg 37),(.pos 48),(.pos 58)]),
   ((.exchange 38 6 2),[(.neg 38),(.neg 6),(.pos 36),(.pos 49)]),
   ((.exchange 38 7 1),[(.neg 38),(.neg 7),(.pos 37),(.pos 50)]),
   ((.exchange 38 15 3),[(.neg 38),(.neg 15),(.pos 35),(.pos 57)]),
   ((.exchange 38 17 1),[(.neg 38),(.neg 17),(.pos 37),(.pos 60)]),
   ((.exchange 38 29 2),[(.neg 38),(.neg 29),(.pos 49),(.pos 59)]),
   ((.exchange 38 56 3),[(.neg 56),(.neg 38),(.pos 35),(.pos 57)]),
   ((.exchange 39 3 1),[(.neg 39),(.neg 3),(.pos 40),(.pos 42)]),
   ((.exchange 39 7 4),[(.neg 39),(.neg 7),(.pos 35),(.pos 36),(.pos 45)]),
   ((.exchange 39 8 0),[(.neg 39),(.neg 8),(.pos 41),(.pos 43),(.pos 52)]),
   ((.exchange 39 10 1),[(.neg 39),(.neg 10),(.pos 40),(.pos 51)]),
   ((.exchange 39 14 1),[(.neg 39),(.neg 14),(.pos 40),(.pos 42),(.pos 51)])]

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



noncomputable def certificates_1 : List (Origin 70 434 × List Sat.Literal) :=
  [((.exchange 39 25 4),[(.neg 39),(.neg 25),(.pos 45),(.pos 55)]),
   ((.exchange 39 33 1),[(.neg 39),(.neg 33),(.pos 40),(.pos 51),(.pos 61)]),
   ((.exchange 39 49 0),[(.neg 49),(.neg 39),(.pos 43),(.pos 52)]),
   ((.exchange 39 50 1),[(.neg 50),(.neg 39),(.pos 40),(.pos 42),(.pos 51)]),
   ((.exchange 39 50 4),[(.neg 50),(.neg 39),(.pos 35),(.pos 36),(.pos 45)]),
   ((.exchange 39 57 4),[(.neg 57),(.neg 39),(.pos 35),(.pos 55)]),
   ((.exchange 39 58 1),[(.neg 58),(.neg 39),(.pos 42),(.pos 61)]),
   ((.exchange 39 64 0),[(.neg 64),(.neg 39),(.pos 43),(.pos 62)]),
   ((.exchange 40 2 2),[(.neg 40),(.neg 2),(.pos 39),(.pos 42)]),
   ((.exchange 40 8 0),[(.neg 40),(.neg 8),(.pos 41),(.pos 44),(.pos 53)]),
   ((.exchange 40 36 4),[(.neg 40),(.neg 36),(.pos 35),(.pos 37)]),
   ((.exchange 40 43 2),[(.neg 43),(.neg 40),(.pos 39),(.pos 42)]),
   ((.exchange 40 48 4),[(.neg 48),(.neg 40),(.pos 37),(.pos 46)]),
   ((.exchange 41 9 2),[(.neg 41),(.neg 9),(.pos 39),(.pos 52)]),
   ((.exchange 41 10 1),[(.neg 41),(.neg 10),(.pos 40),(.pos 53)]),
   ((.exchange 41 15 4),[(.neg 41),(.neg 15),(.pos 35),(.pos 57)]),
   ((.exchange 41 19 2),[(.neg 41),(.neg 19),(.pos 39),(.pos 62)]),
   ((.exchange 41 27 4),[(.neg 41),(.neg 27),(.pos 47),(.pos 57)]),
   ((.exchange 41 32 2),[(.neg 41),(.neg 32),(.pos 52),(.pos 62)]),
   ((.exchange 41 69 1),[(.neg 69),(.neg 41),(.pos 53),(.pos 63)]),
   ((.exchange 42 0 4),[(.neg 42),(.neg 0),(.pos 36),(.pos 37)]),
   ((.exchange 42 1 3),[(.neg 42),(.neg 1),(.pos 39),(.pos 40)]),
   ((.exchange 42 17 4),[(.neg 42),(.neg 17),(.pos 37),(.pos 58)]),
   ((.exchange 42 18 0),[(.neg 42),(.neg 18),(.pos 43),(.pos 44),(.pos 64)]),
   ((.exchange 42 19 3),[(.neg 42),(.neg 19),(.pos 39),(.pos 61)]),
   ((.exchange 42 35 3),[(.neg 42),(.neg 35),(.pos 39),(.pos 40)]),
   ((.exchange 42 38 4),[(.neg 42),(.neg 38),(.pos 36),(.pos 37)]),
   ((.exchange 42 55 3),[(.neg 55),(.neg 42),(.pos 39),(.pos 61)]),
   ((.exchange 42 62 3),[(.neg 62),(.neg 42),(.pos 39),(.pos 61)]),
   ((.exchange 43 6 4),[(.neg 43),(.neg 6),(.pos 36),(.pos 49)]),
   ((.exchange 43 22 1),[(.neg 43),(.neg 22),(.pos 42),(.pos 64)]),
   ((.exchange 43 29 4),[(.neg 43),(.neg 29),(.pos 49),(.pos 59)]),
   ((.exchange 43 55 3),[(.neg 55),(.neg 43),(.pos 39),(.pos 62)]),
   ((.exchange 44 34 2),[(.neg 44),(.neg 34),(.pos 54),(.pos 64)]),
   ((.exchange 44 61 2),[(.neg 61),(.neg 44),(.pos 42),(.pos 64)]),
   ((.exchange 44 68 4),[(.neg 68),(.neg 44),(.pos 50),(.pos 60)]),
   ((.exchange 45 29 0),[(.neg 45),(.neg 29),(.pos 49),(.pos 66)]),
   ((.exchange 45 31 1),[(.neg 45),(.neg 31),(.pos 51),(.pos 65)]),
   ((.exchange 45 32 0),[(.neg 45),(.neg 32),(.pos 52),(.pos 66)]),
   ((.exchange 45 54 0),[(.neg 54),(.neg 45),(.pos 49),(.pos 52)]),
   ((.exchange 45 59 0),[(.neg 59),(.neg 45),(.pos 49),(.pos 66)]),
   ((.exchange 45 64 1),[(.neg 64),(.neg 45),(.pos 48),(.pos 51),(.pos 65)]),
   ((.exchange 45 64 5),[(.neg 64),(.neg 45),(.pos 36),(.pos 39),(.pos 55)]),
   ((.exchange 45 68 0),[(.neg 68),(.neg 45),(.pos 49),(.pos 66)]),
   ((.exchange 46 14 0),[(.neg 46),(.neg 14),(.pos 50),(.pos 53)]),
   ((.exchange 46 17 5),[(.neg 46),(.neg 17),(.pos 37),(.pos 56)]),
   ((.exchange 46 22 2),[(.neg 46),(.neg 22),(.pos 48),(.pos 51),(.pos 65)]),
   ((.exchange 46 28 2),[(.neg 46),(.neg 28),(.pos 48),(.pos 65)]),
   ((.exchange 46 31 2),[(.neg 46),(.neg 31),(.pos 51),(.pos 65)]),
   ((.exchange 46 33 0),[(.neg 46),(.neg 33),(.pos 53),(.pos 67)]),
   ((.exchange 46 42 5),[(.neg 46),(.neg 42),(.pos 37),(.pos 40)]),
   ((.exchange 46 54 0),[(.neg 54),(.neg 46),(.pos 50),(.pos 53)]),
   ((.exchange 46 61 2),[(.neg 61),(.neg 46),(.pos 51),(.pos 65)]),
   ((.exchange 46 63 0),[(.neg 63),(.neg 46),(.pos 53),(.pos 67)]),
   ((.exchange 46 64 5),[(.neg 64),(.neg 46),(.pos 37),(.pos 40),(.pos 56)]),
   ((.exchange 46 68 2),[(.neg 68),(.neg 46),(.pos 48),(.pos 65)]),
   ((.exchange 47 14 1),[(.neg 47),(.neg 14),(.pos 50),(.pos 53)]),
   ((.exchange 47 30 1),[(.neg 47),(.neg 30),(.pos 50),(.pos 67)]),
   ((.exchange 47 33 1),[(.neg 47),(.neg 33),(.pos 53),(.pos 67)]),
   ((.exchange 47 43 2),[(.neg 47),(.neg 43),(.pos 49),(.pos 52)]),
   ((.exchange 47 44 1),[(.neg 47),(.neg 44),(.pos 50),(.pos 53)]),
   ((.exchange 47 59 2),[(.neg 59),(.neg 47),(.pos 49),(.pos 66)]),
   ((.exchange 48 8 0),[(.neg 48),(.neg 8),(.pos 49),(.pos 50)]),
   ((.exchange 48 26 3),[(.neg 48),(.neg 26),(.pos 46),(.pos 65)]),
   ((.exchange 48 29 0),[(.neg 48),(.neg 29),(.pos 49),(.pos 68)]),
   ((.exchange 48 30 0),[(.neg 48),(.neg 30),(.pos 50),(.pos 68)]),
   ((.exchange 48 38 5),[(.neg 48),(.neg 38),(.pos 36),(.pos 37)]),
   ((.exchange 48 55 3),[(.neg 55),(.neg 48),(.pos 45),(.pos 65)]),
   ((.exchange 48 59 0),[(.neg 59),(.neg 48),(.pos 49),(.pos 68)]),
   ((.exchange 49 0 5),[(.neg 49),(.neg 0),(.pos 36),(.pos 38)]),
   ((.exchange 49 3 1),[(.neg 49),(.neg 3),(.pos 48),(.pos 50),(.pos 54)]),
   ((.exchange 49 9 3),[(.neg 49),(.neg 9),(.pos 45),(.pos 52)]),
   ((.exchange 49 10 1),[(.neg 49),(.neg 10),(.pos 48),(.pos 50),(.pos 54)]),
   ((.exchange 49 11 3),[(.neg 49),(.neg 11),(.pos 47),(.pos 52)]),
   ((.exchange 49 14 1),[(.neg 49),(.neg 14),(.pos 50),(.pos 54)]),
   ((.exchange 49 30 1),[(.neg 49),(.neg 30),(.pos 50),(.pos 68)]),
   ((.exchange 49 32 3),[(.neg 49),(.neg 32),(.pos 52),(.pos 66)]),
   ((.exchange 49 34 1),[(.neg 49),(.neg 34),(.pos 54),(.pos 68)]),
   ((.exchange 49 37 1),[(.neg 49),(.neg 37),(.pos 48),(.pos 50)]),
   ((.exchange 49 39 3),[(.neg 49),(.neg 39),(.pos 45),(.pos 52)]),
   ((.exchange 49 41 3),[(.neg 49),(.neg 41),(.pos 47),(.pos 52)]),
   ((.exchange 49 42 5),[(.neg 49),(.neg 42),(.pos 36),(.pos 43)]),
   ((.exchange 49 44 1),[(.neg 49),(.neg 44),(.pos 50),(.pos 54)]),
   ((.exchange 49 55 3),[(.neg 55),(.neg 49),(.pos 45),(.pos 66)]),
   ((.exchange 49 57 3),[(.neg 57),(.neg 49),(.pos 47),(.pos 66)]),
   ((.exchange 49 62 3),[(.neg 62),(.neg 49),(.pos 52),(.pos 66)]),
   ((.exchange 49 64 1),[(.neg 64),(.neg 49),(.pos 54),(.pos 68)]),
   ((.exchange 49 65 3),[(.neg 65),(.neg 49),(.pos 45),(.pos 66)]),
   ((.exchange 49 67 3),[(.neg 67),(.neg 49),(.pos 47),(.pos 66)]),
   ((.exchange 49 69 3),[(.neg 69),(.neg 49),(.pos 52),(.pos 66)]),
   ((.exchange 50 0 5),[(.neg 50),(.neg 0),(.pos 37),(.pos 38)]),
   ((.exchange 50 10 3),[(.neg 50),(.neg 10),(.pos 46),(.pos 53)]),
   ((.exchange 50 18 5),[(.neg 50),(.neg 18),(.pos 38),(.pos 60)]),
   ((.exchange 50 23 5),[(.neg 50),(.neg 23),(.pos 38),(.pos 44),(.pos 60)]),
   ((.exchange 50 36 2),[(.neg 50),(.neg 36),(.pos 48),(.pos 49)]),
   ((.exchange 50 39 3),[(.neg 50),(.neg 39),(.pos 46),(.pos 47),(.pos 53)]),
   ((.exchange 50 41 3),[(.neg 50),(.neg 41),(.pos 47),(.pos 53)]),
   ((.exchange 50 51 3),[(.neg 51),(.neg 50),(.pos 46),(.pos 53)]),
   ((.exchange 50 58 5),[(.neg 58),(.neg 50),(.pos 37),(.pos 60)]),
   ((.exchange 50 62 2),[(.neg 62),(.neg 50),(.pos 49),(.pos 54),(.pos 68)]),
   ((.exchange 50 69 3),[(.neg 69),(.neg 50),(.pos 53),(.pos 67)]),
   ((.exchange 51 0 5),[(.neg 51),(.neg 0),(.pos 39),(.pos 40),(.pos 42)]),
   ((.exchange 51 11 0),[(.neg 51),(.neg 11),(.pos 52),(.pos 53)]),
   ((.exchange 51 21 5),[(.neg 51),(.neg 21),(.pos 39),(.pos 40),(.pos 61)]),
   ((.exchange 51 25 4),[(.neg 51),(.neg 25),(.pos 45),(.pos 65)]),
   ((.exchange 51 26 4),[(.neg 51),(.neg 26),(.pos 46),(.pos 65)]),
   ((.exchange 51 32 0),[(.neg 51),(.neg 32),(.pos 52),(.pos 69)]),
   ((.exchange 51 33 0),[(.neg 51),(.neg 33),(.pos 53),(.pos 69)]),
   ((.exchange 51 35 5),[(.neg 51),(.neg 35),(.pos 39),(.pos 40)]),
   ((.exchange 51 57 4),[(.neg 57),(.neg 51),(.pos 45),(.pos 46),(.pos 65)]),
   ((.exchange 51 57 5),[(.neg 57),(.neg 51),(.pos 39),(.pos 40),(.pos 61)]),
   ((.exchange 51 62 0),[(.neg 62),(.neg 51),(.pos 52),(.pos 69)]),
   ((.exchange 51 62 5),[(.neg 62),(.neg 51),(.pos 39),(.pos 61)]),
   ((.exchange 51 67 0),[(.neg 67),(.neg 51),(.pos 53),(.pos 69)]),
   ((.exchange 52 0 5),[(.neg 52),(.neg 0),(.pos 39),(.pos 41),(.pos 43)]),
   ((.exchange 52 10 1),[(.neg 52),(.neg 10),(.pos 51),(.pos 53)]),
   ((.exchange 52 22 1),[(.neg 52),(.neg 22),(.pos 51),(.pos 54),(.pos 69)]),
   ((.exchange 52 29 4),[(.neg 52),(.neg 29),(.pos 49),(.pos 66)]),
   ((.exchange 52 34 1),[(.neg 52),(.neg 34),(.pos 54),(.pos 69)]),
   ((.exchange 52 36 4),[(.neg 52),(.neg 36),(.pos 45),(.pos 49)]),
   ((.exchange 52 37 4),[(.neg 52),(.neg 37),(.pos 45),(.pos 47),(.pos 49)]),
   ((.exchange 52 44 1),[(.neg 52),(.neg 44),(.pos 53),(.pos 54)]),
   ((.exchange 52 61 1),[(.neg 61),(.neg 52),(.pos 51),(.pos 69)]),
   ((.exchange 52 63 1),[(.neg 63),(.neg 52),(.pos 53),(.pos 69)]),
   ((.exchange 53 0 4),[(.neg 53),(.neg 0),(.pos 46),(.pos 47),(.pos 50)]),
   ((.exchange 53 0 5),[(.neg 53),(.neg 0),(.pos 40),(.pos 41),(.pos 44)]),
   ((.exchange 53 6 4),[(.neg 53),(.neg 6),(.pos 46),(.pos 47),(.pos 50)]),
   ((.exchange 53 8 4),[(.neg 53),(.neg 8),(.pos 47),(.pos 50)])]

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



end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C74


end
end
end BundlePart1

