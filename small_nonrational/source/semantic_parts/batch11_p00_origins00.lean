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


noncomputable def certificates_0 : List (Origin 70 272 × List Sat.Literal) :=
  [((.fixed 0),[(.pos 0)]),
   ((.fixed 1),[(.pos 1)]),
   ((.fixed 2),[(.neg 2)]),
   ((.fixed 3),[(.pos 3)]),
   ((.fixed 4),[(.pos 4)]),
   ((.fixed 5),[(.pos 5)]),
   ((.fixed 6),[(.pos 6)]),
   ((.fixed 7),[(.neg 7)]),
   ((.fixed 8),[(.pos 8)]),
   ((.fixed 9),[(.pos 9)]),
   ((.fixed 10),[(.pos 10)]),
   ((.fixed 11),[(.neg 11)]),
   ((.fixed 12),[(.pos 12)]),
   ((.fixed 13),[(.pos 13)]),
   ((.fixed 14),[(.pos 14)]),
   ((.fixed 15),[(.pos 15)]),
   ((.fixed 16),[(.pos 16)]),
   ((.fixed 17),[(.pos 17)]),
   ((.fixed 18),[(.neg 18)]),
   ((.fixed 19),[(.pos 19)]),
   ((.fixed 20),[(.neg 20)]),
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
   ((.exchange 0 39 2),[(.neg 39),(.neg 0),(.pos 2),(.pos 36)]),
   ((.exchange 0 42 2),[(.neg 42),(.neg 0),(.pos 2),(.pos 36)]),
   ((.exchange 0 43 2),[(.neg 43),(.neg 0),(.pos 2),(.pos 36)]),
   ((.exchange 0 46 1),[(.neg 46),(.neg 0),(.pos 7),(.pos 37)]),
   ((.exchange 0 48 1),[(.neg 48),(.neg 0),(.pos 7),(.pos 37)]),
   ((.exchange 0 50 1),[(.neg 50),(.neg 0),(.pos 7),(.pos 37)]),
   ((.exchange 0 57 0),[(.neg 57),(.neg 0),(.pos 18),(.pos 38)]),
   ((.exchange 0 59 0),[(.neg 59),(.neg 0),(.pos 18),(.pos 38)]),
   ((.exchange 0 60 0),[(.neg 60),(.neg 0),(.pos 18),(.pos 38)]),
   ((.exchange 1 36 2),[(.neg 36),(.neg 1),(.pos 2),(.pos 39)]),
   ((.exchange 1 42 2),[(.neg 42),(.neg 1),(.pos 2),(.pos 39)]),
   ((.exchange 1 43 2),[(.neg 43),(.neg 1),(.pos 2),(.pos 39)]),
   ((.exchange 1 47 0),[(.neg 47),(.neg 1),(.pos 11),(.pos 41)]),
   ((.exchange 1 52 0),[(.neg 52),(.neg 1),(.pos 11),(.pos 41)]),
   ((.exchange 1 53 0),[(.neg 53),(.neg 1),(.pos 11),(.pos 41)]),
   ((.exchange 1 56 1),[(.neg 56),(.neg 1),(.pos 20),(.pos 40)]),
   ((.exchange 1 63 1),[(.neg 63),(.neg 1),(.pos 20),(.pos 40)]),
   ((.exchange 3 36 2),[(.neg 36),(.neg 3),(.pos 2),(.pos 42)]),
   ((.exchange 3 39 2),[(.neg 39),(.neg 3),(.pos 2),(.pos 42)]),
   ((.exchange 3 43 2),[(.neg 43),(.neg 3),(.pos 2),(.pos 42)]),
   ((.exchange 4 36 2),[(.neg 36),(.neg 4),(.pos 2),(.pos 43)]),
   ((.exchange 4 39 2),[(.neg 39),(.neg 4),(.pos 2),(.pos 43)]),
   ((.exchange 4 42 2),[(.neg 42),(.neg 4),(.pos 2),(.pos 43)]),
   ((.exchange 5 37 1),[(.neg 37),(.neg 5),(.pos 7),(.pos 46)]),
   ((.exchange 5 41 0),[(.neg 41),(.neg 5),(.pos 11),(.pos 47)]),
   ((.exchange 5 48 1),[(.neg 48),(.neg 5),(.pos 7),(.pos 46)]),
   ((.exchange 5 50 1),[(.neg 50),(.neg 5),(.pos 7),(.pos 46)]),
   ((.exchange 5 55 2),[(.neg 55),(.neg 5),(.pos 25),(.pos 45)]),
   ((.exchange 5 65 2),[(.neg 65),(.neg 5),(.pos 25),(.pos 45)]),
   ((.exchange 5 66 2),[(.neg 66),(.neg 5),(.pos 25),(.pos 45)]),
   ((.exchange 6 37 1),[(.neg 37),(.neg 6),(.pos 7),(.pos 48)]),
   ((.exchange 6 46 1),[(.neg 46),(.neg 6),(.pos 7),(.pos 48)]),
   ((.exchange 6 50 1),[(.neg 50),(.neg 6),(.pos 7),(.pos 48)]),
   ((.exchange 8 37 1),[(.neg 37),(.neg 8),(.pos 7),(.pos 50)]),
   ((.exchange 8 46 1),[(.neg 46),(.neg 8),(.pos 7),(.pos 50)]),
   ((.exchange 8 48 1),[(.neg 48),(.neg 8),(.pos 7),(.pos 50)]),
   ((.exchange 9 41 0),[(.neg 41),(.neg 9),(.pos 11),(.pos 52)]),
   ((.exchange 10 41 0),[(.neg 41),(.neg 10),(.pos 11),(.pos 53)]),
   ((.exchange 15 38 0),[(.neg 38),(.neg 15),(.pos 18),(.pos 57)]),
   ((.exchange 15 40 1),[(.neg 40),(.neg 15),(.pos 20),(.pos 56)]),
   ((.exchange 15 45 2),[(.neg 45),(.neg 15),(.pos 25),(.pos 55)]),
   ((.exchange 15 59 0),[(.neg 59),(.neg 15),(.pos 18),(.pos 57)]),
   ((.exchange 15 60 0),[(.neg 60),(.neg 15),(.pos 18),(.pos 57)]),
   ((.exchange 15 61 1),[(.neg 61),(.neg 15),(.pos 20),(.pos 56)]),
   ((.exchange 15 63 1),[(.neg 63),(.neg 15),(.pos 20),(.pos 56)]),
   ((.exchange 15 65 2),[(.neg 65),(.neg 15),(.pos 25),(.pos 55)]),
   ((.exchange 15 66 2),[(.neg 66),(.neg 15),(.pos 25),(.pos 55)]),
   ((.exchange 16 38 0),[(.neg 38),(.neg 16),(.pos 18),(.pos 59)]),
   ((.exchange 16 57 0),[(.neg 57),(.neg 16),(.pos 18),(.pos 59)]),
   ((.exchange 16 60 0),[(.neg 60),(.neg 16),(.pos 18),(.pos 59)]),
   ((.exchange 17 38 0),[(.neg 38),(.neg 17),(.pos 18),(.pos 60)]),
   ((.exchange 17 57 0),[(.neg 57),(.neg 17),(.pos 18),(.pos 60)]),
   ((.exchange 17 59 0),[(.neg 59),(.neg 17),(.pos 18),(.pos 60)]),
   ((.exchange 19 40 1),[(.neg 40),(.neg 19),(.pos 20),(.pos 61)]),
   ((.exchange 19 56 1),[(.neg 56),(.neg 19),(.pos 20),(.pos 61)]),
   ((.exchange 19 63 1),[(.neg 63),(.neg 19),(.pos 20),(.pos 61)]),
   ((.exchange 21 40 1),[(.neg 40),(.neg 21),(.pos 20),(.pos 63)]),
   ((.exchange 21 56 1),[(.neg 56),(.neg 21),(.pos 20),(.pos 63)]),
   ((.exchange 21 61 1),[(.neg 61),(.neg 21),(.pos 20),(.pos 63)]),
   ((.exchange 26 45 2),[(.neg 45),(.neg 26),(.pos 25),(.pos 65)]),
   ((.exchange 26 55 2),[(.neg 55),(.neg 26),(.pos 25),(.pos 65)]),
   ((.exchange 26 66 2),[(.neg 66),(.neg 26),(.pos 25),(.pos 65)]),
   ((.exchange 27 45 2),[(.neg 45),(.neg 27),(.pos 25),(.pos 66)]),
   ((.exchange 27 55 2),[(.neg 55),(.neg 27),(.pos 25),(.pos 66)]),
   ((.exchange 27 65 2),[(.neg 65),(.neg 27),(.pos 25),(.pos 66)]),
   ((.exchange 35 3 1),[(.neg 35),(.neg 3),(.pos 37),(.pos 40)]),
   ((.exchange 35 4 0),[(.neg 35),(.neg 4),(.pos 38),(.pos 41)]),
   ((.exchange 35 6 2),[(.neg 35),(.neg 6),(.pos 36),(.pos 45)]),
   ((.exchange 35 10 1),[(.neg 35),(.neg 10),(.pos 40),(.pos 46)]),
   ((.exchange 35 16 2),[(.neg 35),(.neg 16),(.pos 36),(.pos 55)]),
   ((.exchange 35 23 2),[(.neg 35),(.neg 23),(.pos 36),(.pos 39),(.pos 55)]),
   ((.exchange 35 26 1),[(.neg 35),(.neg 26),(.pos 46),(.pos 56)]),
   ((.exchange 35 44 1),[(.neg 44),(.neg 35),(.pos 37),(.pos 40)]),
   ((.exchange 35 48 2),[(.neg 48),(.neg 35),(.pos 36),(.pos 45)]),
   ((.exchange 35 52 2),[(.neg 52),(.neg 35),(.pos 39),(.pos 45)]),
   ((.exchange 35 64 1),[(.neg 64),(.neg 35),(.pos 37),(.pos 40),(.pos 56)]),
   ((.exchange 35 67 1),[(.neg 67),(.neg 35),(.pos 46),(.pos 56)]),
   ((.exchange 35 68 1),[(.neg 68),(.neg 35),(.pos 37),(.pos 46),(.pos 56)]),
   ((.exchange 35 68 2),[(.neg 68),(.neg 35),(.pos 36),(.pos 45),(.pos 55)]),
   ((.exchange 35 69 1),[(.neg 69),(.neg 35),(.pos 40),(.pos 46),(.pos 56)]),
   ((.exchange 36 8 0),[(.neg 36),(.neg 8),(.pos 38),(.pos 49)]),
   ((.exchange 36 15 3),[(.neg 36),(.neg 15),(.pos 35),(.pos 55)]),
   ((.exchange 36 17 1),[(.neg 36),(.neg 17),(.pos 37),(.pos 58)]),
   ((.exchange 36 65 1),[(.neg 65),(.neg 36),(.pos 48),(.pos 58)]),
   ((.exchange 36 67 3),[(.neg 67),(.neg 36),(.pos 35),(.pos 45),(.pos 55)]),
   ((.exchange 37 4 0),[(.neg 37),(.neg 4),(.pos 38),(.pos 44)]),
   ((.exchange 37 15 3),[(.neg 37),(.neg 15),(.pos 35),(.pos 56)]),
   ((.exchange 37 16 2),[(.neg 37),(.neg 16),(.pos 36),(.pos 58)]),
   ((.exchange 37 22 2),[(.neg 37),(.neg 22),(.pos 42),(.pos 58)]),
   ((.exchange 37 24 0),[(.neg 37),(.neg 24),(.pos 44),(.pos 60)]),
   ((.exchange 37 61 2),[(.neg 61),(.neg 37),(.pos 42),(.pos 58)]),
   ((.exchange 38 1 3),[(.neg 38),(.neg 1),(.pos 35),(.pos 41)]),
   ((.exchange 38 6 2),[(.neg 38),(.neg 6),(.pos 36),(.pos 49)])]

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



noncomputable def certificates_1 : List (Origin 70 272 × List Sat.Literal) :=
  [((.exchange 38 40 1),[(.neg 40),(.neg 38),(.pos 37),(.pos 44)]),
   ((.exchange 38 45 2),[(.neg 45),(.neg 38),(.pos 36),(.pos 49)]),
   ((.exchange 38 51 1),[(.neg 51),(.neg 38),(.pos 37),(.pos 44),(.pos 50)]),
   ((.exchange 38 53 1),[(.neg 53),(.neg 38),(.pos 44),(.pos 50)]),
   ((.exchange 39 10 1),[(.neg 39),(.neg 10),(.pos 40),(.pos 51)]),
   ((.exchange 39 15 4),[(.neg 39),(.neg 15),(.pos 35),(.pos 55)]),
   ((.exchange 39 31 1),[(.neg 39),(.neg 31),(.pos 51),(.pos 61)]),
   ((.exchange 39 33 0),[(.neg 39),(.neg 33),(.pos 41),(.pos 52),(.pos 62)]),
   ((.exchange 40 4 0),[(.neg 40),(.neg 4),(.pos 41),(.pos 44)]),
   ((.exchange 40 6 2),[(.neg 40),(.neg 6),(.pos 39),(.pos 42),(.pos 51)]),
   ((.exchange 40 12 2),[(.neg 40),(.neg 12),(.pos 42),(.pos 51)]),
   ((.exchange 40 24 0),[(.neg 40),(.neg 24),(.pos 44),(.pos 63)]),
   ((.exchange 40 38 4),[(.neg 40),(.neg 38),(.pos 35),(.pos 37)]),
   ((.exchange 40 49 4),[(.neg 49),(.neg 40),(.pos 35),(.pos 37),(.pos 46)]),
   ((.exchange 41 0 4),[(.neg 41),(.neg 0),(.pos 35),(.pos 38)]),
   ((.exchange 41 3 1),[(.neg 41),(.neg 3),(.pos 40),(.pos 44)]),
   ((.exchange 41 15 4),[(.neg 41),(.neg 15),(.pos 35),(.pos 57)]),
   ((.exchange 41 23 2),[(.neg 41),(.neg 23),(.pos 43),(.pos 62)]),
   ((.exchange 42 17 4),[(.neg 42),(.neg 17),(.pos 37),(.pos 58)]),
   ((.exchange 42 24 0),[(.neg 42),(.neg 24),(.pos 44),(.pos 64)]),
   ((.exchange 42 34 0),[(.neg 42),(.neg 34),(.pos 54),(.pos 64)]),
   ((.exchange 42 53 3),[(.neg 53),(.neg 42),(.pos 40),(.pos 51)]),
   ((.exchange 42 60 0),[(.neg 60),(.neg 42),(.pos 44),(.pos 64)]),
   ((.exchange 42 68 0),[(.neg 68),(.neg 42),(.pos 54),(.pos 64)]),
   ((.exchange 43 24 1),[(.neg 43),(.neg 24),(.pos 44),(.pos 64)]),
   ((.exchange 43 50 1),[(.neg 50),(.neg 43),(.pos 44),(.pos 54)]),
   ((.exchange 43 53 1),[(.neg 53),(.neg 43),(.pos 44),(.pos 54)]),
   ((.exchange 43 60 1),[(.neg 60),(.neg 43),(.pos 44),(.pos 64)]),
   ((.exchange 43 63 1),[(.neg 63),(.neg 43),(.pos 44),(.pos 64)]),
   ((.exchange 44 0 4),[(.neg 44),(.neg 0),(.pos 37),(.pos 38)]),
   ((.exchange 44 1 3),[(.neg 44),(.neg 1),(.pos 40),(.pos 41)]),
   ((.exchange 44 8 4),[(.neg 44),(.neg 8),(.pos 38),(.pos 50)]),
   ((.exchange 44 12 2),[(.neg 44),(.neg 12),(.pos 42),(.pos 54)]),
   ((.exchange 44 17 4),[(.neg 44),(.neg 17),(.pos 37),(.pos 60)]),
   ((.exchange 44 22 2),[(.neg 44),(.neg 22),(.pos 42),(.pos 64)]),
   ((.exchange 44 23 2),[(.neg 44),(.neg 23),(.pos 43),(.pos 64)]),
   ((.exchange 44 34 2),[(.neg 44),(.neg 34),(.pos 54),(.pos 64)]),
   ((.exchange 44 45 4),[(.neg 45),(.neg 44),(.pos 37),(.pos 38),(.pos 50)]),
   ((.exchange 44 48 2),[(.neg 48),(.neg 44),(.pos 42),(.pos 54)]),
   ((.exchange 44 56 4),[(.neg 56),(.neg 44),(.pos 37),(.pos 60)]),
   ((.exchange 44 58 2),[(.neg 58),(.neg 44),(.pos 42),(.pos 64)]),
   ((.exchange 44 58 4),[(.neg 58),(.neg 44),(.pos 37),(.pos 60)]),
   ((.exchange 44 59 2),[(.neg 59),(.neg 44),(.pos 43),(.pos 64)]),
   ((.exchange 44 61 2),[(.neg 61),(.neg 44),(.pos 42),(.pos 64)]),
   ((.exchange 44 62 2),[(.neg 62),(.neg 44),(.pos 43),(.pos 64)]),
   ((.exchange 44 65 4),[(.neg 65),(.neg 44),(.pos 37),(.pos 50),(.pos 60)]),
   ((.exchange 44 68 2),[(.neg 68),(.neg 44),(.pos 54),(.pos 64)]),
   ((.exchange 45 0 5),[(.neg 45),(.neg 0),(.pos 35),(.pos 36)]),
   ((.exchange 45 1 5),[(.neg 45),(.neg 1),(.pos 35),(.pos 39)]),
   ((.exchange 45 3 1),[(.neg 45),(.neg 3),(.pos 46),(.pos 48),(.pos 51)]),
   ((.exchange 45 4 0),[(.neg 45),(.neg 4),(.pos 47),(.pos 49),(.pos 52)]),
   ((.exchange 45 10 1),[(.neg 45),(.neg 10),(.pos 46),(.pos 51)]),
   ((.exchange 45 12 1),[(.neg 45),(.neg 12),(.pos 48),(.pos 51)]),
   ((.exchange 45 40 1),[(.neg 45),(.neg 40),(.pos 46),(.pos 51)]),
   ((.exchange 46 21 0),[(.neg 46),(.neg 21),(.pos 47),(.pos 53),(.pos 67)]),
   ((.exchange 46 31 2),[(.neg 46),(.neg 31),(.pos 51),(.pos 65)]),
   ((.exchange 46 32 2),[(.neg 46),(.neg 32),(.pos 45),(.pos 51),(.pos 65)]),
   ((.exchange 46 62 0),[(.neg 62),(.neg 46),(.pos 47),(.pos 53),(.pos 67)]),
   ((.exchange 46 62 2),[(.neg 62),(.neg 46),(.pos 45),(.pos 51),(.pos 65)]),
   ((.exchange 46 66 0),[(.neg 66),(.neg 46),(.pos 47),(.pos 67)]),
   ((.exchange 47 6 2),[(.neg 47),(.neg 6),(.pos 45),(.pos 49)]),
   ((.exchange 47 15 5),[(.neg 47),(.neg 15),(.pos 35),(.pos 57)]),
   ((.exchange 47 30 1),[(.neg 47),(.neg 30),(.pos 50),(.pos 67)]),
   ((.exchange 48 9 3),[(.neg 48),(.neg 9),(.pos 45),(.pos 51)]),
   ((.exchange 48 13 0),[(.neg 48),(.neg 13),(.pos 49),(.pos 54)]),
   ((.exchange 48 29 0),[(.neg 48),(.neg 29),(.pos 49),(.pos 68)]),
   ((.exchange 48 31 3),[(.neg 48),(.neg 31),(.pos 51),(.pos 65)]),
   ((.exchange 48 34 0),[(.neg 48),(.neg 34),(.pos 54),(.pos 68)]),
   ((.exchange 48 43 0),[(.neg 48),(.neg 43),(.pos 49),(.pos 54)]),
   ((.exchange 48 69 0),[(.neg 69),(.neg 48),(.pos 54),(.pos 68)]),
   ((.exchange 49 1 3),[(.neg 49),(.neg 1),(.pos 45),(.pos 47),(.pos 52)]),
   ((.exchange 49 4 5),[(.neg 49),(.neg 4),(.pos 38),(.pos 43)]),
   ((.exchange 49 12 1),[(.neg 49),(.neg 12),(.pos 48),(.pos 54)]),
   ((.exchange 49 30 1),[(.neg 49),(.neg 30),(.pos 50),(.pos 68)]),
   ((.exchange 49 34 1),[(.neg 49),(.neg 34),(.pos 54),(.pos 68)]),
   ((.exchange 49 35 5),[(.neg 49),(.neg 35),(.pos 36),(.pos 38)]),
   ((.exchange 49 39 3),[(.neg 49),(.neg 39),(.pos 45),(.pos 52)]),
   ((.exchange 49 40 1),[(.neg 49),(.neg 40),(.pos 48),(.pos 50),(.pos 54)]),
   ((.exchange 49 41 5),[(.neg 49),(.neg 41),(.pos 38),(.pos 43)]),
   ((.exchange 49 51 1),[(.neg 51),(.neg 49),(.pos 48),(.pos 54)]),
   ((.exchange 49 62 5),[(.neg 62),(.neg 49),(.pos 43),(.pos 59)]),
   ((.exchange 49 64 5),[(.neg 64),(.neg 49),(.pos 43),(.pos 59)]),
   ((.exchange 49 65 1),[(.neg 65),(.neg 49),(.pos 48),(.pos 68)]),
   ((.exchange 50 24 5),[(.neg 50),(.neg 24),(.pos 44),(.pos 60)]),
   ((.exchange 50 41 5),[(.neg 50),(.neg 41),(.pos 38),(.pos 44)]),
   ((.exchange 50 43 5),[(.neg 50),(.neg 43),(.pos 38),(.pos 44)]),
   ((.exchange 50 64 2),[(.neg 64),(.neg 50),(.pos 54),(.pos 68)]),
   ((.exchange 50 66 2),[(.neg 66),(.neg 50),(.pos 49),(.pos 68)]),
   ((.exchange 51 0 4),[(.neg 51),(.neg 0),(.pos 45),(.pos 46),(.pos 48)]),
   ((.exchange 51 3 5),[(.neg 51),(.neg 3),(.pos 40),(.pos 42)]),
   ((.exchange 51 4 0),[(.neg 51),(.neg 4),(.pos 52),(.pos 53),(.pos 54)]),
   ((.exchange 51 6 4),[(.neg 51),(.neg 6),(.pos 45),(.pos 48)]),
   ((.exchange 51 17 4),[(.neg 51),(.neg 17),(.pos 46),(.pos 48),(.pos 65)]),
   ((.exchange 51 26 4),[(.neg 51),(.neg 26),(.pos 46),(.pos 65)]),
   ((.exchange 51 27 4),[(.neg 51),(.neg 27),(.pos 45),(.pos 46),(.pos 65)]),
   ((.exchange 51 32 0),[(.neg 51),(.neg 32),(.pos 52),(.pos 69)]),
   ((.exchange 51 34 0),[(.neg 51),(.neg 34),(.pos 54),(.pos 69)]),
   ((.exchange 51 36 4),[(.neg 51),(.neg 36),(.pos 45),(.pos 48)]),
   ((.exchange 51 38 4),[(.neg 51),(.neg 38),(.pos 45),(.pos 46),(.pos 48)]),
   ((.exchange 51 38 5),[(.neg 51),(.neg 38),(.pos 39),(.pos 40),(.pos 42)]),
   ((.exchange 51 44 5),[(.neg 51),(.neg 44),(.pos 40),(.pos 42)]),
   ((.exchange 51 49 4),[(.neg 51),(.neg 49),(.pos 45),(.pos 48)]),
   ((.exchange 51 59 4),[(.neg 59),(.neg 51),(.pos 45),(.pos 48),(.pos 65)]),
   ((.exchange 51 59 5),[(.neg 59),(.neg 51),(.pos 39),(.pos 42),(.pos 61)]),
   ((.exchange 51 60 4),[(.neg 60),(.neg 51),(.pos 46),(.pos 48),(.pos 65)]),
   ((.exchange 51 67 0),[(.neg 67),(.neg 51),(.pos 53),(.pos 69)]),
   ((.exchange 51 67 4),[(.neg 67),(.neg 51),(.pos 46),(.pos 65)]),
   ((.exchange 52 12 1),[(.neg 52),(.neg 12),(.pos 51),(.pos 54)]),
   ((.exchange 52 19 5),[(.neg 52),(.neg 19),(.pos 39),(.pos 62)]),
   ((.exchange 52 29 4),[(.neg 52),(.neg 29),(.pos 49),(.pos 66)]),
   ((.exchange 52 31 1),[(.neg 52),(.neg 31),(.pos 51),(.pos 69)]),
   ((.exchange 53 3 5),[(.neg 53),(.neg 3),(.pos 40),(.pos 44)]),
   ((.exchange 53 26 4),[(.neg 53),(.neg 26),(.pos 46),(.pos 67)]),
   ((.exchange 53 28 4),[(.neg 53),(.neg 28),(.pos 46),(.pos 50),(.pos 67)]),
   ((.exchange 53 30 4),[(.neg 53),(.neg 30),(.pos 50),(.pos 67)]),
   ((.exchange 53 31 2),[(.neg 53),(.neg 31),(.pos 51),(.pos 69)]),
   ((.exchange 53 34 2),[(.neg 53),(.neg 34),(.pos 54),(.pos 69)]),
   ((.exchange 54 6 4),[(.neg 54),(.neg 6),(.pos 48),(.pos 49)]),
   ((.exchange 54 8 4),[(.neg 54),(.neg 8),(.pos 49),(.pos 50)]),
   ((.exchange 54 24 5),[(.neg 54),(.neg 24),(.pos 44),(.pos 64)]),
   ((.exchange 54 30 4),[(.neg 54),(.neg 30),(.pos 50),(.pos 68)]),
   ((.exchange 54 32 3),[(.neg 54),(.neg 32),(.pos 52),(.pos 69)]),
   ((.exchange 54 35 4),[(.neg 54),(.neg 35),(.pos 48),(.pos 49),(.pos 50)]),
   ((.exchange 54 38 4),[(.neg 54),(.neg 38),(.pos 49),(.pos 50)]),
   ((.exchange 54 40 5),[(.neg 54),(.neg 40),(.pos 42),(.pos 44)]),
   ((.exchange 54 45 4),[(.neg 54),(.neg 45),(.pos 48),(.pos 49)]),
   ((.exchange 54 47 4),[(.neg 54),(.neg 47),(.pos 49),(.pos 50)]),
   ((.exchange 54 56 4),[(.neg 56),(.neg 54),(.pos 48),(.pos 50),(.pos 68)])]

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



end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C73


end
end
end BundlePart0

