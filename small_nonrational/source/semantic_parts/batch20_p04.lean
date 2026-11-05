module
public import Consolidated.SemanticData
public import Mathlib.Data.Fin.Tuple.Basic
public import MatroidCatalogue.Definitions
public import MatroidChecked.FastSemanticChecks
public import MatroidChecked.BitsetSemanticChecks
public import MatroidChecked.BitsetOrigins
public import MatroidChecked.MaskOrigins


section BundlePart4
/- Source: MatroidChecked/SemanticParts/Cases25Part00/Checks00.lean -/



@[expose] public section
noncomputable section


set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C80


noncomputable def certificates_0 : List (Origin 70 1212 × List Sat.Literal) :=
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
   ((.fixed 11),[(.pos 11)]),
   ((.fixed 12),[(.pos 12)]),
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
   ((.exchange 0 42 2),[(.neg 42),(.neg 0),(.pos 2),(.pos 36)]),
   ((.exchange 0 43 2),[(.neg 43),(.neg 0),(.pos 2),(.pos 36)]),
   ((.exchange 0 46 1),[(.neg 46),(.neg 0),(.pos 7),(.pos 37)]),
   ((.exchange 0 48 1),[(.neg 48),(.neg 0),(.pos 7),(.pos 37)]),
   ((.exchange 0 50 1),[(.neg 50),(.neg 0),(.pos 7),(.pos 37)]),
   ((.exchange 0 55 3),[(.neg 55),(.neg 0),(.pos 15),(.pos 35)]),
   ((.exchange 0 56 3),[(.neg 56),(.neg 0),(.pos 15),(.pos 35)]),
   ((.exchange 0 57 3),[(.neg 57),(.neg 0),(.pos 15),(.pos 35)]),
   ((.exchange 1 42 2),[(.neg 42),(.neg 1),(.pos 2),(.pos 39)]),
   ((.exchange 1 43 2),[(.neg 43),(.neg 1),(.pos 2),(.pos 39)]),
   ((.exchange 3 36 2),[(.neg 36),(.neg 3),(.pos 2),(.pos 42)]),
   ((.exchange 3 39 2),[(.neg 39),(.neg 3),(.pos 2),(.pos 42)]),
   ((.exchange 3 43 2),[(.neg 43),(.neg 3),(.pos 2),(.pos 42)]),
   ((.exchange 4 36 2),[(.neg 36),(.neg 4),(.pos 2),(.pos 43)]),
   ((.exchange 4 39 2),[(.neg 39),(.neg 4),(.pos 2),(.pos 43)]),
   ((.exchange 4 42 2),[(.neg 42),(.neg 4),(.pos 2),(.pos 43)]),
   ((.exchange 5 37 1),[(.neg 37),(.neg 5),(.pos 7),(.pos 46)]),
   ((.exchange 5 48 1),[(.neg 48),(.neg 5),(.pos 7),(.pos 46)]),
   ((.exchange 5 50 1),[(.neg 50),(.neg 5),(.pos 7),(.pos 46)]),
   ((.exchange 6 37 1),[(.neg 37),(.neg 6),(.pos 7),(.pos 48)]),
   ((.exchange 6 46 1),[(.neg 46),(.neg 6),(.pos 7),(.pos 48)]),
   ((.exchange 6 50 1),[(.neg 50),(.neg 6),(.pos 7),(.pos 48)]),
   ((.exchange 8 37 1),[(.neg 37),(.neg 8),(.pos 7),(.pos 50)]),
   ((.exchange 8 46 1),[(.neg 46),(.neg 8),(.pos 7),(.pos 50)]),
   ((.exchange 8 48 1),[(.neg 48),(.neg 8),(.pos 7),(.pos 50)]),
   ((.exchange 16 35 3),[(.neg 35),(.neg 16),(.pos 15),(.pos 55)]),
   ((.exchange 16 56 3),[(.neg 56),(.neg 16),(.pos 15),(.pos 55)]),
   ((.exchange 16 57 3),[(.neg 57),(.neg 16),(.pos 15),(.pos 55)]),
   ((.exchange 17 35 3),[(.neg 35),(.neg 17),(.pos 15),(.pos 56)]),
   ((.exchange 17 55 3),[(.neg 55),(.neg 17),(.pos 15),(.pos 56)]),
   ((.exchange 17 57 3),[(.neg 57),(.neg 17),(.pos 15),(.pos 56)]),
   ((.exchange 18 35 3),[(.neg 35),(.neg 18),(.pos 15),(.pos 57)]),
   ((.exchange 18 55 3),[(.neg 55),(.neg 18),(.pos 15),(.pos 57)]),
   ((.exchange 18 56 3),[(.neg 56),(.neg 18),(.pos 15),(.pos 57)]),
   ((.exchange 35 3 1),[(.neg 35),(.neg 3),(.pos 37),(.pos 40)]),
   ((.exchange 35 4 0),[(.neg 35),(.neg 4),(.pos 38),(.pos 41)]),
   ((.exchange 35 6 2),[(.neg 35),(.neg 6),(.pos 36),(.pos 45)]),
   ((.exchange 35 8 0),[(.neg 35),(.neg 8),(.pos 38),(.pos 47)]),
   ((.exchange 35 10 1),[(.neg 35),(.neg 10),(.pos 40),(.pos 46)]),
   ((.exchange 35 11 0),[(.neg 35),(.neg 11),(.pos 41),(.pos 47)]),
   ((.exchange 35 13 2),[(.neg 35),(.neg 13),(.pos 36),(.pos 39),(.pos 45)]),
   ((.exchange 35 34 1),[(.neg 35),(.neg 34),(.pos 37),(.pos 40),(.pos 46),(.pos 56)]),
   ((.exchange 35 43 0),[(.neg 43),(.neg 35),(.pos 38),(.pos 41)]),
   ((.exchange 35 44 0),[(.neg 44),(.neg 35),(.pos 38),(.pos 41)]),
   ((.exchange 35 51 2),[(.neg 51),(.neg 35),(.pos 39),(.pos 45)]),
   ((.exchange 35 52 0),[(.neg 52),(.neg 35),(.pos 41),(.pos 47)]),
   ((.exchange 36 5 3),[(.neg 36),(.neg 5),(.pos 35),(.pos 45)]),
   ((.exchange 36 8 0),[(.neg 36),(.neg 8),(.pos 38),(.pos 49)]),
   ((.exchange 36 17 1),[(.neg 36),(.neg 17),(.pos 37),(.pos 58)]),
   ((.exchange 36 18 0),[(.neg 36),(.neg 18),(.pos 38),(.pos 59)]),
   ((.exchange 36 25 3),[(.neg 36),(.neg 25),(.pos 45),(.pos 55)]),
   ((.exchange 36 29 0),[(.neg 36),(.neg 29),(.pos 49),(.pos 59)]),
   ((.exchange 36 46 3),[(.neg 46),(.neg 36),(.pos 35),(.pos 45)]),
   ((.exchange 36 50 0),[(.neg 50),(.neg 36),(.pos 38),(.pos 49)]),
   ((.exchange 36 57 0),[(.neg 57),(.neg 36),(.pos 38),(.pos 59)]),
   ((.exchange 36 68 0),[(.neg 68),(.neg 36),(.pos 49),(.pos 59)]),
   ((.exchange 37 16 2),[(.neg 37),(.neg 16),(.pos 36),(.pos 58)]),
   ((.exchange 37 18 0),[(.neg 37),(.neg 18),(.pos 38),(.pos 60)]),
   ((.exchange 37 20 3),[(.neg 37),(.neg 20),(.pos 40),(.pos 56)]),
   ((.exchange 37 22 2),[(.neg 37),(.neg 22),(.pos 42),(.pos 58)]),
   ((.exchange 37 41 3),[(.neg 41),(.neg 37),(.pos 35),(.pos 40)]),
   ((.exchange 37 43 0),[(.neg 43),(.neg 37),(.pos 38),(.pos 44)]),
   ((.exchange 37 57 0),[(.neg 57),(.neg 37),(.pos 38),(.pos 60)]),
   ((.exchange 37 61 3),[(.neg 61),(.neg 37),(.pos 40),(.pos 56)]),
   ((.exchange 37 64 0),[(.neg 64),(.neg 37),(.pos 44),(.pos 60)]),
   ((.exchange 38 1 3),[(.neg 38),(.neg 1),(.pos 35),(.pos 41)]),
   ((.exchange 38 3 1),[(.neg 38),(.neg 3),(.pos 37),(.pos 44)]),
   ((.exchange 38 5 3),[(.neg 38),(.neg 5),(.pos 35),(.pos 47)]),
   ((.exchange 38 6 2),[(.neg 38),(.neg 6),(.pos 36),(.pos 49)]),
   ((.exchange 38 14 1),[(.neg 38),(.neg 14),(.pos 44),(.pos 50)]),
   ((.exchange 38 17 1),[(.neg 38),(.neg 17),(.pos 37),(.pos 60)]),
   ((.exchange 38 29 2),[(.neg 38),(.neg 29),(.pos 49),(.pos 59)]),
   ((.exchange 38 39 3),[(.neg 39),(.neg 38),(.pos 35),(.pos 41)]),
   ((.exchange 38 42 1),[(.neg 42),(.neg 38),(.pos 37),(.pos 44)]),
   ((.exchange 38 53 1),[(.neg 53),(.neg 38),(.pos 44),(.pos 50)]),
   ((.exchange 38 54 2),[(.neg 54),(.neg 38),(.pos 43),(.pos 49)]),
   ((.exchange 38 55 2),[(.neg 55),(.neg 38),(.pos 36),(.pos 59)]),
   ((.exchange 38 56 1),[(.neg 56),(.neg 38),(.pos 37),(.pos 60)]),
   ((.exchange 38 64 2),[(.neg 64),(.neg 38),(.pos 43),(.pos 59)]),
   ((.exchange 38 68 1),[(.neg 68),(.neg 38),(.pos 50),(.pos 60)]),
   ((.exchange 39 10 1),[(.neg 39),(.neg 10),(.pos 40),(.pos 51)]),
   ((.exchange 39 11 0),[(.neg 39),(.neg 11),(.pos 41),(.pos 52)]),
   ((.exchange 39 20 1),[(.neg 39),(.neg 20),(.pos 40),(.pos 61)]),
   ((.exchange 39 21 0),[(.neg 39),(.neg 21),(.pos 41),(.pos 62)]),
   ((.exchange 39 25 4),[(.neg 39),(.neg 25),(.pos 45),(.pos 55)]),
   ((.exchange 39 31 1),[(.neg 39),(.neg 31),(.pos 51),(.pos 61)]),
   ((.exchange 39 32 0),[(.neg 39),(.neg 32),(.pos 52),(.pos 62)]),
   ((.exchange 39 69 1),[(.neg 69),(.neg 39),(.pos 51),(.pos 61)]),
   ((.exchange 40 0 4),[(.neg 40),(.neg 0),(.pos 35),(.pos 37)]),
   ((.exchange 40 4 0),[(.neg 40),(.neg 4),(.pos 41),(.pos 44)]),
   ((.exchange 40 8 4),[(.neg 40),(.neg 8),(.pos 35),(.pos 37),(.pos 46)]),
   ((.exchange 40 11 0),[(.neg 40),(.neg 11),(.pos 41),(.pos 53)]),
   ((.exchange 40 12 2),[(.neg 40),(.neg 12),(.pos 42),(.pos 51)])]

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



noncomputable def certificates_1 : List (Origin 70 1212 × List Sat.Literal) :=
  [((.exchange 40 14 0),[(.neg 40),(.neg 14),(.pos 44),(.pos 53)]),
   ((.exchange 40 21 0),[(.neg 40),(.neg 21),(.pos 41),(.pos 63)]),
   ((.exchange 40 22 2),[(.neg 40),(.neg 22),(.pos 42),(.pos 61)]),
   ((.exchange 40 24 0),[(.neg 40),(.neg 24),(.pos 44),(.pos 63)]),
   ((.exchange 40 30 4),[(.neg 40),(.neg 30),(.pos 37),(.pos 46),(.pos 56)]),
   ((.exchange 40 31 2),[(.neg 40),(.neg 31),(.pos 51),(.pos 61)]),
   ((.exchange 40 32 0),[(.neg 40),(.neg 32),(.pos 41),(.pos 53),(.pos 63)]),
   ((.exchange 40 33 0),[(.neg 40),(.neg 33),(.pos 53),(.pos 63)]),
   ((.exchange 40 36 4),[(.neg 40),(.neg 36),(.pos 35),(.pos 37)]),
   ((.exchange 40 49 4),[(.neg 49),(.neg 40),(.pos 35),(.pos 37),(.pos 46)]),
   ((.exchange 40 52 2),[(.neg 52),(.neg 40),(.pos 39),(.pos 51)]),
   ((.exchange 40 58 4),[(.neg 58),(.neg 40),(.pos 37),(.pos 56)]),
   ((.exchange 40 60 4),[(.neg 60),(.neg 40),(.pos 37),(.pos 56)]),
   ((.exchange 40 64 0),[(.neg 64),(.neg 40),(.pos 44),(.pos 63)]),
   ((.exchange 40 66 4),[(.neg 66),(.neg 40),(.pos 35),(.pos 46),(.pos 56)]),
   ((.exchange 40 69 0),[(.neg 69),(.neg 40),(.pos 53),(.pos 63)]),
   ((.exchange 41 0 4),[(.neg 41),(.neg 0),(.pos 35),(.pos 38)]),
   ((.exchange 41 3 1),[(.neg 41),(.neg 3),(.pos 40),(.pos 44)]),
   ((.exchange 41 5 4),[(.neg 41),(.neg 5),(.pos 35),(.pos 47)]),
   ((.exchange 41 8 4),[(.neg 41),(.neg 8),(.pos 38),(.pos 47)]),
   ((.exchange 41 10 1),[(.neg 41),(.neg 10),(.pos 40),(.pos 53)]),
   ((.exchange 41 12 2),[(.neg 41),(.neg 12),(.pos 39),(.pos 43),(.pos 52)]),
   ((.exchange 41 16 2),[(.neg 41),(.neg 16),(.pos 39),(.pos 43),(.pos 62)]),
   ((.exchange 41 18 4),[(.neg 41),(.neg 18),(.pos 38),(.pos 57)]),
   ((.exchange 41 20 1),[(.neg 41),(.neg 20),(.pos 40),(.pos 63)]),
   ((.exchange 41 24 1),[(.neg 41),(.neg 24),(.pos 44),(.pos 63)]),
   ((.exchange 41 27 4),[(.neg 41),(.neg 27),(.pos 47),(.pos 57)]),
   ((.exchange 41 32 2),[(.neg 41),(.neg 32),(.pos 52),(.pos 62)]),
   ((.exchange 41 33 1),[(.neg 41),(.neg 33),(.pos 53),(.pos 63)]),
   ((.exchange 41 49 4),[(.neg 49),(.neg 41),(.pos 38),(.pos 47)]),
   ((.exchange 41 50 4),[(.neg 50),(.neg 41),(.pos 38),(.pos 47)]),
   ((.exchange 41 51 1),[(.neg 51),(.neg 41),(.pos 40),(.pos 53)]),
   ((.exchange 41 51 2),[(.neg 51),(.neg 41),(.pos 39),(.pos 52)]),
   ((.exchange 41 59 4),[(.neg 59),(.neg 41),(.pos 38),(.pos 57)]),
   ((.exchange 42 10 3),[(.neg 42),(.neg 10),(.pos 40),(.pos 51)]),
   ((.exchange 42 24 0),[(.neg 42),(.neg 24),(.pos 44),(.pos 64)]),
   ((.exchange 42 28 4),[(.neg 42),(.neg 28),(.pos 48),(.pos 58)]),
   ((.exchange 42 30 4),[(.neg 42),(.neg 30),(.pos 37),(.pos 48),(.pos 58)]),
   ((.exchange 42 31 3),[(.neg 42),(.neg 31),(.pos 51),(.pos 61)]),
   ((.exchange 42 34 0),[(.neg 42),(.neg 34),(.pos 54),(.pos 64)]),
   ((.exchange 42 65 4),[(.neg 65),(.neg 42),(.pos 48),(.pos 58)]),
   ((.exchange 42 67 4),[(.neg 67),(.neg 42),(.pos 37),(.pos 48),(.pos 58)]),
   ((.exchange 42 69 0),[(.neg 69),(.neg 42),(.pos 54),(.pos 64)]),
   ((.exchange 43 8 4),[(.neg 43),(.neg 8),(.pos 38),(.pos 49)]),
   ((.exchange 43 11 3),[(.neg 43),(.neg 11),(.pos 41),(.pos 52)]),
   ((.exchange 43 14 1),[(.neg 43),(.neg 14),(.pos 44),(.pos 54)]),
   ((.exchange 43 21 3),[(.neg 43),(.neg 21),(.pos 41),(.pos 62)]),
   ((.exchange 43 24 1),[(.neg 43),(.neg 24),(.pos 44),(.pos 64)]),
   ((.exchange 43 29 4),[(.neg 43),(.neg 29),(.pos 49),(.pos 59)]),
   ((.exchange 43 32 3),[(.neg 43),(.neg 32),(.pos 52),(.pos 62)]),
   ((.exchange 43 47 4),[(.neg 47),(.neg 43),(.pos 38),(.pos 49)]),
   ((.exchange 43 50 4),[(.neg 50),(.neg 43),(.pos 38),(.pos 49)]),
   ((.exchange 43 57 3),[(.neg 57),(.neg 43),(.pos 41),(.pos 62)]),
   ((.exchange 43 57 4),[(.neg 57),(.neg 43),(.pos 38),(.pos 59)]),
   ((.exchange 43 68 4),[(.neg 68),(.neg 43),(.pos 49),(.pos 59)]),
   ((.exchange 44 1 3),[(.neg 44),(.neg 1),(.pos 40),(.pos 41)]),
   ((.exchange 44 8 4),[(.neg 44),(.neg 8),(.pos 38),(.pos 50)]),
   ((.exchange 44 10 3),[(.neg 44),(.neg 10),(.pos 40),(.pos 53)]),
   ((.exchange 44 16 2),[(.neg 44),(.neg 16),(.pos 42),(.pos 43),(.pos 64)]),
   ((.exchange 44 17 4),[(.neg 44),(.neg 17),(.pos 37),(.pos 60)]),
   ((.exchange 44 21 3),[(.neg 44),(.neg 21),(.pos 41),(.pos 63)]),
   ((.exchange 44 22 2),[(.neg 44),(.neg 22),(.pos 42),(.pos 64)]),
   ((.exchange 44 26 4),[(.neg 44),(.neg 26),(.pos 37),(.pos 50),(.pos 60)]),
   ((.exchange 44 30 4),[(.neg 44),(.neg 30),(.pos 50),(.pos 60)]),
   ((.exchange 44 32 3),[(.neg 44),(.neg 32),(.pos 41),(.pos 53),(.pos 63)]),
   ((.exchange 44 33 3),[(.neg 44),(.neg 33),(.pos 53),(.pos 63)]),
   ((.exchange 44 35 4),[(.neg 44),(.neg 35),(.pos 37),(.pos 38)]),
   ((.exchange 44 36 4),[(.neg 44),(.neg 36),(.pos 37),(.pos 38)]),
   ((.exchange 44 45 4),[(.neg 45),(.neg 44),(.pos 37),(.pos 38),(.pos 50)]),
   ((.exchange 44 49 4),[(.neg 49),(.neg 44),(.pos 38),(.pos 50)]),
   ((.exchange 44 56 4),[(.neg 56),(.neg 44),(.pos 37),(.pos 60)]),
   ((.exchange 44 57 4),[(.neg 57),(.neg 44),(.pos 38),(.pos 60)]),
   ((.exchange 44 59 4),[(.neg 59),(.neg 44),(.pos 38),(.pos 60)]),
   ((.exchange 44 65 4),[(.neg 65),(.neg 44),(.pos 37),(.pos 50),(.pos 60)]),
   ((.exchange 44 68 4),[(.neg 68),(.neg 44),(.pos 50),(.pos 60)]),
   ((.exchange 45 1 5),[(.neg 45),(.neg 1),(.pos 35),(.pos 39)]),
   ((.exchange 45 3 1),[(.neg 45),(.neg 3),(.pos 46),(.pos 48),(.pos 51)]),
   ((.exchange 45 8 0),[(.neg 45),(.neg 8),(.pos 47),(.pos 49)]),
   ((.exchange 45 11 0),[(.neg 45),(.neg 11),(.pos 47),(.pos 52)]),
   ((.exchange 45 13 0),[(.neg 45),(.neg 13),(.pos 49),(.pos 52)]),
   ((.exchange 45 16 5),[(.neg 45),(.neg 16),(.pos 36),(.pos 55)]),
   ((.exchange 45 17 1),[(.neg 45),(.neg 17),(.pos 46),(.pos 48),(.pos 65)]),
   ((.exchange 45 23 5),[(.neg 45),(.neg 23),(.pos 36),(.pos 39),(.pos 55)]),
   ((.exchange 45 27 0),[(.neg 45),(.neg 27),(.pos 47),(.pos 66)]),
   ((.exchange 45 29 0),[(.neg 45),(.neg 29),(.pos 49),(.pos 66)]),
   ((.exchange 45 31 1),[(.neg 45),(.neg 31),(.pos 51),(.pos 65)]),
   ((.exchange 45 32 0),[(.neg 45),(.neg 32),(.pos 52),(.pos 66)]),
   ((.exchange 45 37 5),[(.neg 45),(.neg 37),(.pos 35),(.pos 36)]),
   ((.exchange 45 38 0),[(.neg 45),(.neg 38),(.pos 47),(.pos 49)]),
   ((.exchange 45 41 0),[(.neg 45),(.neg 41),(.pos 47),(.pos 52)]),
   ((.exchange 45 41 5),[(.neg 45),(.neg 41),(.pos 35),(.pos 39)]),
   ((.exchange 45 43 0),[(.neg 45),(.neg 43),(.pos 49),(.pos 52)]),
   ((.exchange 45 44 1),[(.neg 45),(.neg 44),(.pos 46),(.pos 48),(.pos 51)]),
   ((.exchange 45 50 0),[(.neg 50),(.neg 45),(.pos 47),(.pos 49)]),
   ((.exchange 45 54 0),[(.neg 54),(.neg 45),(.pos 49),(.pos 52)]),
   ((.exchange 45 58 5),[(.neg 58),(.neg 45),(.pos 36),(.pos 55)]),
   ((.exchange 45 59 0),[(.neg 59),(.neg 45),(.pos 49),(.pos 66)]),
   ((.exchange 45 60 1),[(.neg 60),(.neg 45),(.pos 46),(.pos 48),(.pos 65)]),
   ((.exchange 45 68 0),[(.neg 68),(.neg 45),(.pos 49),(.pos 66)]),
   ((.exchange 45 69 1),[(.neg 69),(.neg 45),(.pos 51),(.pos 65)]),
   ((.exchange 46 1 5),[(.neg 46),(.neg 1),(.pos 35),(.pos 40)]),
   ((.exchange 46 25 2),[(.neg 46),(.neg 25),(.pos 45),(.pos 65)]),
   ((.exchange 46 27 0),[(.neg 46),(.neg 27),(.pos 47),(.pos 67)]),
   ((.exchange 46 31 2),[(.neg 46),(.neg 31),(.pos 51),(.pos 65)]),
   ((.exchange 46 33 0),[(.neg 46),(.neg 33),(.pos 53),(.pos 67)]),
   ((.exchange 46 41 0),[(.neg 46),(.neg 41),(.pos 47),(.pos 53)]),
   ((.exchange 46 52 0),[(.neg 52),(.neg 46),(.pos 47),(.pos 53)]),
   ((.exchange 46 57 0),[(.neg 57),(.neg 46),(.pos 47),(.pos 67)]),
   ((.exchange 46 62 5),[(.neg 62),(.neg 46),(.pos 35),(.pos 40),(.pos 56)]),
   ((.exchange 46 63 0),[(.neg 63),(.neg 46),(.pos 53),(.pos 67)]),
   ((.exchange 46 63 5),[(.neg 63),(.neg 46),(.pos 40),(.pos 56)]),
   ((.exchange 47 0 5),[(.neg 47),(.neg 0),(.pos 35),(.pos 38)]),
   ((.exchange 47 3 1),[(.neg 47),(.neg 3),(.pos 46),(.pos 50),(.pos 53)]),
   ((.exchange 47 6 2),[(.neg 47),(.neg 6),(.pos 45),(.pos 49)]),
   ((.exchange 47 9 2),[(.neg 47),(.neg 9),(.pos 45),(.pos 52)]),
   ((.exchange 47 17 1),[(.neg 47),(.neg 17),(.pos 46),(.pos 50),(.pos 67)]),
   ((.exchange 47 18 5),[(.neg 47),(.neg 18),(.pos 38),(.pos 57)]),
   ((.exchange 47 25 2),[(.neg 47),(.neg 25),(.pos 45),(.pos 66)]),
   ((.exchange 47 29 2),[(.neg 47),(.neg 29),(.pos 49),(.pos 66)]),
   ((.exchange 47 33 1),[(.neg 47),(.neg 33),(.pos 53),(.pos 67)]),
   ((.exchange 47 36 2),[(.neg 47),(.neg 36),(.pos 45),(.pos 49)]),
   ((.exchange 47 39 2),[(.neg 47),(.neg 39),(.pos 45),(.pos 52)]),
   ((.exchange 47 39 5),[(.neg 47),(.neg 39),(.pos 35),(.pos 41)]),
   ((.exchange 47 44 1),[(.neg 47),(.neg 44),(.pos 50),(.pos 53)]),
   ((.exchange 47 48 2),[(.neg 48),(.neg 47),(.pos 45),(.pos 49)]),
   ((.exchange 47 51 1),[(.neg 51),(.neg 47),(.pos 46),(.pos 53)]),
   ((.exchange 47 51 2),[(.neg 51),(.neg 47),(.pos 45),(.pos 52)]),
   ((.exchange 47 54 1),[(.neg 54),(.neg 47),(.pos 50),(.pos 53)])]

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



noncomputable def certificates_2 : List (Origin 70 1212 × List Sat.Literal) :=
  [((.exchange 47 54 2),[(.neg 54),(.neg 47),(.pos 49),(.pos 52)]),
   ((.exchange 47 55 2),[(.neg 55),(.neg 47),(.pos 45),(.pos 66)]),
   ((.exchange 47 58 5),[(.neg 58),(.neg 47),(.pos 35),(.pos 38),(.pos 57)]),
   ((.exchange 47 59 2),[(.neg 59),(.neg 47),(.pos 49),(.pos 66)]),
   ((.exchange 47 60 1),[(.neg 60),(.neg 47),(.pos 50),(.pos 67)]),
   ((.exchange 47 65 1),[(.neg 65),(.neg 47),(.pos 46),(.pos 67)]),
   ((.exchange 48 9 3),[(.neg 48),(.neg 9),(.pos 45),(.pos 51)]),
   ((.exchange 48 23 5),[(.neg 48),(.neg 23),(.pos 36),(.pos 42),(.pos 58)]),
   ((.exchange 48 25 3),[(.neg 48),(.neg 25),(.pos 45),(.pos 65)]),
   ((.exchange 48 29 0),[(.neg 48),(.neg 29),(.pos 49),(.pos 68)]),
   ((.exchange 48 31 3),[(.neg 48),(.neg 31),(.pos 51),(.pos 65)]),
   ((.exchange 48 34 0),[(.neg 48),(.neg 34),(.pos 54),(.pos 68)]),
   ((.exchange 48 52 0),[(.neg 52),(.neg 48),(.pos 49),(.pos 54)]),
   ((.exchange 48 62 5),[(.neg 62),(.neg 48),(.pos 36),(.pos 42),(.pos 58)]),
   ((.exchange 48 64 0),[(.neg 64),(.neg 48),(.pos 54),(.pos 68)]),
   ((.exchange 48 69 0),[(.neg 69),(.neg 48),(.pos 54),(.pos 68)]),
   ((.exchange 48 69 3),[(.neg 69),(.neg 48),(.pos 51),(.pos 65)]),
   ((.exchange 49 0 5),[(.neg 49),(.neg 0),(.pos 36),(.pos 38)]),
   ((.exchange 49 1 3),[(.neg 49),(.neg 1),(.pos 45),(.pos 47),(.pos 52)]),
   ((.exchange 49 3 1),[(.neg 49),(.neg 3),(.pos 48),(.pos 50),(.pos 54)]),
   ((.exchange 49 4 5),[(.neg 49),(.neg 4),(.pos 38),(.pos 43)]),
   ((.exchange 49 11 3),[(.neg 49),(.neg 11),(.pos 47),(.pos 52)]),
   ((.exchange 49 14 1),[(.neg 49),(.neg 14),(.pos 50),(.pos 54)]),
   ((.exchange 49 17 1),[(.neg 49),(.neg 17),(.pos 48),(.pos 50),(.pos 68)]),
   ((.exchange 49 22 5),[(.neg 49),(.neg 22),(.pos 36),(.pos 43),(.pos 59)]),
   ((.exchange 49 25 3),[(.neg 49),(.neg 25),(.pos 45),(.pos 66)]),
   ((.exchange 49 32 3),[(.neg 49),(.neg 32),(.pos 52),(.pos 66)]),
   ((.exchange 49 34 1),[(.neg 49),(.neg 34),(.pos 54),(.pos 68)]),
   ((.exchange 49 35 3),[(.neg 49),(.neg 35),(.pos 45),(.pos 47)]),
   ((.exchange 49 35 5),[(.neg 49),(.neg 35),(.pos 36),(.pos 38)]),
   ((.exchange 49 40 1),[(.neg 49),(.neg 40),(.pos 48),(.pos 50),(.pos 54)]),
   ((.exchange 49 41 3),[(.neg 49),(.neg 41),(.pos 47),(.pos 52)]),
   ((.exchange 49 42 1),[(.neg 49),(.neg 42),(.pos 48),(.pos 54)]),
   ((.exchange 49 44 5),[(.neg 49),(.neg 44),(.pos 38),(.pos 43)]),
   ((.exchange 49 46 3),[(.neg 49),(.neg 46),(.pos 45),(.pos 47)]),
   ((.exchange 49 51 1),[(.neg 51),(.neg 49),(.pos 48),(.pos 54)]),
   ((.exchange 49 51 3),[(.neg 51),(.neg 49),(.pos 45),(.pos 52)]),
   ((.exchange 49 53 3),[(.neg 53),(.neg 49),(.pos 47),(.pos 52)]),
   ((.exchange 49 55 3),[(.neg 55),(.neg 49),(.pos 45),(.pos 66)]),
   ((.exchange 49 57 3),[(.neg 57),(.neg 49),(.pos 47),(.pos 66)]),
   ((.exchange 49 57 5),[(.neg 57),(.neg 49),(.pos 38),(.pos 59)]),
   ((.exchange 49 58 1),[(.neg 58),(.neg 49),(.pos 48),(.pos 68)]),
   ((.exchange 49 58 5),[(.neg 58),(.neg 49),(.pos 36),(.pos 59)]),
   ((.exchange 49 60 5),[(.neg 60),(.neg 49),(.pos 38),(.pos 59)]),
   ((.exchange 49 61 5),[(.neg 61),(.neg 49),(.pos 36),(.pos 43),(.pos 59)]),
   ((.exchange 49 62 5),[(.neg 62),(.neg 49),(.pos 43),(.pos 59)]),
   ((.exchange 49 65 1),[(.neg 65),(.neg 49),(.pos 48),(.pos 68)]),
   ((.exchange 49 65 3),[(.neg 65),(.neg 49),(.pos 45),(.pos 66)]),
   ((.exchange 49 67 3),[(.neg 67),(.neg 49),(.pos 47),(.pos 66)]),
   ((.exchange 50 13 2),[(.neg 50),(.neg 13),(.pos 49),(.pos 54)]),
   ((.exchange 50 18 5),[(.neg 50),(.neg 18),(.pos 38),(.pos 60)]),
   ((.exchange 50 24 5),[(.neg 50),(.neg 24),(.pos 44),(.pos 60)]),
   ((.exchange 50 29 2),[(.neg 50),(.neg 29),(.pos 49),(.pos 68)]),
   ((.exchange 50 43 2),[(.neg 50),(.neg 43),(.pos 49),(.pos 54)]),
   ((.exchange 50 43 5),[(.neg 50),(.neg 43),(.pos 38),(.pos 44)]),
   ((.exchange 50 52 2),[(.neg 52),(.neg 50),(.pos 49),(.pos 54)]),
   ((.exchange 50 52 3),[(.neg 52),(.neg 50),(.pos 47),(.pos 53)]),
   ((.exchange 50 57 3),[(.neg 57),(.neg 50),(.pos 47),(.pos 67)]),
   ((.exchange 50 57 5),[(.neg 57),(.neg 50),(.pos 38),(.pos 60)]),
   ((.exchange 50 63 3),[(.neg 63),(.neg 50),(.pos 53),(.pos 67)]),
   ((.exchange 50 63 5),[(.neg 63),(.neg 50),(.pos 44),(.pos 60)]),
   ((.exchange 50 64 2),[(.neg 64),(.neg 50),(.pos 54),(.pos 68)]),
   ((.exchange 50 66 3),[(.neg 66),(.neg 50),(.pos 47),(.pos 67)]),
   ((.exchange 51 0 4),[(.neg 51),(.neg 0),(.pos 45),(.pos 46),(.pos 48)]),
   ((.exchange 51 3 5),[(.neg 51),(.neg 3),(.pos 40),(.pos 42)]),
   ((.exchange 51 6 4),[(.neg 51),(.neg 6),(.pos 45),(.pos 48)]),
   ((.exchange 51 11 0),[(.neg 51),(.neg 11),(.pos 52),(.pos 53)]),
   ((.exchange 51 13 0),[(.neg 51),(.neg 13),(.pos 52),(.pos 54)]),
   ((.exchange 51 22 5),[(.neg 51),(.neg 22),(.pos 42),(.pos 61)]),
   ((.exchange 51 25 4),[(.neg 51),(.neg 25),(.pos 45),(.pos 65)]),
   ((.exchange 51 26 4),[(.neg 51),(.neg 26),(.pos 46),(.pos 65)]),
   ((.exchange 51 28 4),[(.neg 51),(.neg 28),(.pos 48),(.pos 65)]),
   ((.exchange 51 32 0),[(.neg 51),(.neg 32),(.pos 52),(.pos 69)]),
   ((.exchange 51 33 0),[(.neg 51),(.neg 33),(.pos 53),(.pos 69)]),
   ((.exchange 51 34 0),[(.neg 51),(.neg 34),(.pos 54),(.pos 69)]),
   ((.exchange 51 43 0),[(.neg 51),(.neg 43),(.pos 52),(.pos 54)]),
   ((.exchange 51 47 4),[(.neg 51),(.neg 47),(.pos 45),(.pos 46)]),
   ((.exchange 51 67 0),[(.neg 67),(.neg 51),(.pos 53),(.pos 69)]),
   ((.exchange 52 4 5),[(.neg 52),(.neg 4),(.pos 41),(.pos 43)]),
   ((.exchange 52 5 4),[(.neg 52),(.neg 5),(.pos 45),(.pos 47)]),
   ((.exchange 52 6 4),[(.neg 52),(.neg 6),(.pos 45),(.pos 49)]),
   ((.exchange 52 10 1),[(.neg 52),(.neg 10),(.pos 51),(.pos 53)]),
   ((.exchange 52 12 1),[(.neg 52),(.neg 12),(.pos 51),(.pos 54)]),
   ((.exchange 52 22 5),[(.neg 52),(.neg 22),(.pos 39),(.pos 43),(.pos 62)]),
   ((.exchange 52 25 4),[(.neg 52),(.neg 25),(.pos 45),(.pos 66)]),
   ((.exchange 52 27 4),[(.neg 52),(.neg 27),(.pos 47),(.pos 66)]),
   ((.exchange 52 29 4),[(.neg 52),(.neg 29),(.pos 49),(.pos 66)]),
   ((.exchange 52 31 1),[(.neg 52),(.neg 31),(.pos 51),(.pos 69)]),
   ((.exchange 52 33 1),[(.neg 52),(.neg 33),(.pos 53),(.pos 69)]),
   ((.exchange 52 34 1),[(.neg 52),(.neg 34),(.pos 54),(.pos 69)]),
   ((.exchange 52 35 4),[(.neg 52),(.neg 35),(.pos 45),(.pos 47)]),
   ((.exchange 52 36 4),[(.neg 52),(.neg 36),(.pos 45),(.pos 49)]),
   ((.exchange 52 38 4),[(.neg 52),(.neg 38),(.pos 47),(.pos 49)]),
   ((.exchange 52 42 1),[(.neg 52),(.neg 42),(.pos 51),(.pos 54)]),
   ((.exchange 52 44 1),[(.neg 52),(.neg 44),(.pos 53),(.pos 54)]),
   ((.exchange 52 46 1),[(.neg 52),(.neg 46),(.pos 51),(.pos 53)]),
   ((.exchange 52 48 1),[(.neg 52),(.neg 48),(.pos 51),(.pos 54)]),
   ((.exchange 52 48 4),[(.neg 52),(.neg 48),(.pos 45),(.pos 49)]),
   ((.exchange 52 50 1),[(.neg 52),(.neg 50),(.pos 53),(.pos 54)]),
   ((.exchange 52 50 4),[(.neg 52),(.neg 50),(.pos 47),(.pos 49)]),
   ((.exchange 52 57 4),[(.neg 57),(.neg 52),(.pos 47),(.pos 66)]),
   ((.exchange 52 65 1),[(.neg 65),(.neg 52),(.pos 51),(.pos 69)]),
   ((.exchange 52 65 4),[(.neg 65),(.neg 52),(.pos 45),(.pos 66)]),
   ((.exchange 52 68 1),[(.neg 68),(.neg 52),(.pos 54),(.pos 69)]),
   ((.exchange 52 68 4),[(.neg 68),(.neg 52),(.pos 49),(.pos 66)]),
   ((.exchange 53 0 5),[(.neg 53),(.neg 0),(.pos 40),(.pos 41),(.pos 44)]),
   ((.exchange 53 1 5),[(.neg 53),(.neg 1),(.pos 40),(.pos 41)]),
   ((.exchange 53 4 5),[(.neg 53),(.neg 4),(.pos 41),(.pos 44)]),
   ((.exchange 53 6 2),[(.neg 53),(.neg 6),(.pos 51),(.pos 52),(.pos 54)]),
   ((.exchange 53 8 4),[(.neg 53),(.neg 8),(.pos 47),(.pos 50)]),
   ((.exchange 53 9 2),[(.neg 53),(.neg 9),(.pos 51),(.pos 52)]),
   ((.exchange 53 12 2),[(.neg 53),(.neg 12),(.pos 51),(.pos 54)]),
   ((.exchange 53 21 5),[(.neg 53),(.neg 21),(.pos 41),(.pos 63)]),
   ((.exchange 53 24 5),[(.neg 53),(.neg 24),(.pos 44),(.pos 63)]),
   ((.exchange 53 27 4),[(.neg 53),(.neg 27),(.pos 47),(.pos 67)]),
   ((.exchange 53 30 4),[(.neg 53),(.neg 30),(.pos 50),(.pos 67)]),
   ((.exchange 53 31 2),[(.neg 53),(.neg 31),(.pos 51),(.pos 69)]),
   ((.exchange 53 34 2),[(.neg 53),(.neg 34),(.pos 54),(.pos 69)]),
   ((.exchange 53 36 4),[(.neg 53),(.neg 36),(.pos 46),(.pos 47),(.pos 50)]),
   ((.exchange 53 38 4),[(.neg 53),(.neg 38),(.pos 47),(.pos 50)]),
   ((.exchange 53 45 4),[(.neg 53),(.neg 45),(.pos 46),(.pos 47)]),
   ((.exchange 53 57 4),[(.neg 57),(.neg 53),(.pos 47),(.pos 67)]),
   ((.exchange 53 58 4),[(.neg 58),(.neg 53),(.pos 46),(.pos 50),(.pos 67)]),
   ((.exchange 53 60 4),[(.neg 60),(.neg 53),(.pos 50),(.pos 67)]),
   ((.exchange 53 61 2),[(.neg 61),(.neg 53),(.pos 51),(.pos 69)]),
   ((.exchange 53 62 5),[(.neg 62),(.neg 53),(.pos 41),(.pos 63)]),
   ((.exchange 53 65 2),[(.neg 65),(.neg 53),(.pos 51),(.pos 69)]),
   ((.exchange 53 65 4),[(.neg 65),(.neg 53),(.pos 46),(.pos 67)])]

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



noncomputable def certificates_3 : List (Origin 70 1212 × List Sat.Literal) :=
  [((.exchange 53 66 4),[(.neg 66),(.neg 53),(.pos 47),(.pos 67)]),
   ((.exchange 54 4 5),[(.neg 54),(.neg 4),(.pos 43),(.pos 44)]),
   ((.exchange 54 8 4),[(.neg 54),(.neg 8),(.pos 49),(.pos 50)]),
   ((.exchange 54 16 5),[(.neg 54),(.neg 16),(.pos 42),(.pos 43),(.pos 64)]),
   ((.exchange 54 17 4),[(.neg 54),(.neg 17),(.pos 48),(.pos 50),(.pos 68)]),
   ((.exchange 54 22 5),[(.neg 54),(.neg 22),(.pos 42),(.pos 64)]),
   ((.exchange 54 23 5),[(.neg 54),(.neg 23),(.pos 43),(.pos 64)]),
   ((.exchange 54 28 4),[(.neg 54),(.neg 28),(.pos 48),(.pos 68)]),
   ((.exchange 54 30 4),[(.neg 54),(.neg 30),(.pos 50),(.pos 68)]),
   ((.exchange 54 31 3),[(.neg 54),(.neg 31),(.pos 51),(.pos 69)]),
   ((.exchange 54 39 3),[(.neg 54),(.neg 39),(.pos 51),(.pos 52)]),
   ((.exchange 54 40 3),[(.neg 54),(.neg 40),(.pos 51),(.pos 53)]),
   ((.exchange 54 41 3),[(.neg 54),(.neg 41),(.pos 52),(.pos 53)]),
   ((.exchange 54 45 3),[(.neg 54),(.neg 45),(.pos 51),(.pos 52)]),
   ((.exchange 54 45 4),[(.neg 54),(.neg 45),(.pos 48),(.pos 49)]),
   ((.exchange 54 46 3),[(.neg 54),(.neg 46),(.pos 51),(.pos 53)]),
   ((.exchange 54 47 4),[(.neg 54),(.neg 47),(.pos 49),(.pos 50)]),
   ((.exchange 54 56 4),[(.neg 56),(.neg 54),(.pos 48),(.pos 50),(.pos 68)]),
   ((.exchange 54 59 5),[(.neg 59),(.neg 54),(.pos 43),(.pos 64)]),
   ((.exchange 54 65 4),[(.neg 65),(.neg 54),(.pos 48),(.pos 68)]),
   ((.exchange 54 67 3),[(.neg 67),(.neg 54),(.pos 53),(.pos 69)]),
   ((.exchange 55 6 6),[(.neg 55),(.neg 6),(.pos 36),(.pos 45)]),
   ((.exchange 55 22 1),[(.neg 55),(.neg 22),(.pos 58),(.pos 61)]),
   ((.exchange 55 23 0),[(.neg 55),(.neg 23),(.pos 59),(.pos 62)]),
   ((.exchange 55 28 1),[(.neg 55),(.neg 28),(.pos 58),(.pos 65)]),
   ((.exchange 55 29 0),[(.neg 55),(.neg 29),(.pos 59),(.pos 66)]),
   ((.exchange 55 31 1),[(.neg 55),(.neg 31),(.pos 61),(.pos 65)]),
   ((.exchange 55 32 0),[(.neg 55),(.neg 32),(.pos 62),(.pos 66)]),
   ((.exchange 55 43 0),[(.neg 55),(.neg 43),(.pos 59),(.pos 62)]),
   ((.exchange 55 51 6),[(.neg 55),(.neg 51),(.pos 39),(.pos 45)]),
   ((.exchange 55 52 0),[(.neg 55),(.neg 52),(.pos 62),(.pos 66)]),
   ((.exchange 55 64 0),[(.neg 64),(.neg 55),(.pos 59),(.pos 62)]),
   ((.exchange 55 68 0),[(.neg 68),(.neg 55),(.pos 59),(.pos 66)]),
   ((.exchange 55 68 1),[(.neg 68),(.neg 55),(.pos 58),(.pos 65)]),
   ((.exchange 55 69 1),[(.neg 69),(.neg 55),(.pos 61),(.pos 65)]),
   ((.exchange 56 3 6),[(.neg 56),(.neg 3),(.pos 37),(.pos 40)]),
   ((.exchange 56 10 6),[(.neg 56),(.neg 10),(.pos 40),(.pos 46)]),
   ((.exchange 56 22 2),[(.neg 56),(.neg 22),(.pos 58),(.pos 61)]),
   ((.exchange 56 24 0),[(.neg 56),(.neg 24),(.pos 60),(.pos 63)]),
   ((.exchange 56 28 2),[(.neg 56),(.neg 28),(.pos 58),(.pos 65)]),
   ((.exchange 56 30 0),[(.neg 56),(.neg 30),(.pos 60),(.pos 67)]),
   ((.exchange 56 31 2),[(.neg 56),(.neg 31),(.pos 61),(.pos 65)]),
   ((.exchange 56 33 0),[(.neg 56),(.neg 33),(.pos 63),(.pos 67)]),
   ((.exchange 56 44 0),[(.neg 56),(.neg 44),(.pos 60),(.pos 63)]),
   ((.exchange 56 54 6),[(.neg 56),(.neg 54),(.pos 37),(.pos 40),(.pos 46)]),
   ((.exchange 56 68 0),[(.neg 68),(.neg 56),(.pos 60),(.pos 67)]),
   ((.exchange 57 4 6),[(.neg 57),(.neg 4),(.pos 38),(.pos 41)]),
   ((.exchange 57 11 6),[(.neg 57),(.neg 11),(.pos 41),(.pos 47)]),
   ((.exchange 57 23 2),[(.neg 57),(.neg 23),(.pos 59),(.pos 62)]),
   ((.exchange 57 24 1),[(.neg 57),(.neg 24),(.pos 60),(.pos 63)]),
   ((.exchange 57 29 2),[(.neg 57),(.neg 29),(.pos 59),(.pos 66)]),
   ((.exchange 57 30 1),[(.neg 57),(.neg 30),(.pos 60),(.pos 67)]),
   ((.exchange 57 33 1),[(.neg 57),(.neg 33),(.pos 63),(.pos 67)]),
   ((.exchange 57 44 1),[(.neg 57),(.neg 44),(.pos 60),(.pos 63)]),
   ((.exchange 57 49 6),[(.neg 57),(.neg 49),(.pos 38),(.pos 47)]),
   ((.exchange 57 50 1),[(.neg 57),(.neg 50),(.pos 60),(.pos 67)]),
   ((.exchange 57 52 2),[(.neg 57),(.neg 52),(.pos 62),(.pos 66)]),
   ((.exchange 57 53 1),[(.neg 57),(.neg 53),(.pos 63),(.pos 67)]),
   ((.exchange 57 69 1),[(.neg 69),(.neg 57),(.pos 63),(.pos 67)]),
   ((.exchange 58 0 6),[(.neg 58),(.neg 0),(.pos 36),(.pos 37)]),
   ((.exchange 58 3 6),[(.neg 58),(.neg 3),(.pos 37),(.pos 42)]),
   ((.exchange 58 5 3),[(.neg 58),(.neg 5),(.pos 55),(.pos 56),(.pos 65)]),
   ((.exchange 58 18 0),[(.neg 58),(.neg 18),(.pos 59),(.pos 60)]),
   ((.exchange 58 20 3),[(.neg 58),(.neg 20),(.pos 56),(.pos 61)]),
   ((.exchange 58 23 0),[(.neg 58),(.neg 23),(.pos 59),(.pos 64)]),
   ((.exchange 58 24 0),[(.neg 58),(.neg 24),(.pos 60),(.pos 64)]),
   ((.exchange 58 26 3),[(.neg 58),(.neg 26),(.pos 56),(.pos 65)]),
   ((.exchange 58 29 0),[(.neg 58),(.neg 29),(.pos 59),(.pos 68)]),
   ((.exchange 58 30 0),[(.neg 58),(.neg 30),(.pos 60),(.pos 68)]),
   ((.exchange 58 31 3),[(.neg 58),(.neg 31),(.pos 61),(.pos 65)]),
   ((.exchange 58 34 0),[(.neg 58),(.neg 34),(.pos 64),(.pos 68)]),
   ((.exchange 58 40 6),[(.neg 58),(.neg 40),(.pos 37),(.pos 42)]),
   ((.exchange 58 43 0),[(.neg 58),(.neg 43),(.pos 59),(.pos 64)]),
   ((.exchange 58 44 0),[(.neg 58),(.neg 44),(.pos 60),(.pos 64)]),
   ((.exchange 58 45 3),[(.neg 58),(.neg 45),(.pos 55),(.pos 65)]),
   ((.exchange 58 46 3),[(.neg 58),(.neg 46),(.pos 56),(.pos 65)]),
   ((.exchange 58 49 0),[(.neg 58),(.neg 49),(.pos 59),(.pos 68)]),
   ((.exchange 58 50 0),[(.neg 58),(.neg 50),(.pos 60),(.pos 68)]),
   ((.exchange 58 51 3),[(.neg 58),(.neg 51),(.pos 61),(.pos 65)]),
   ((.exchange 58 54 0),[(.neg 58),(.neg 54),(.pos 64),(.pos 68)]),
   ((.exchange 58 57 0),[(.neg 58),(.neg 57),(.pos 59),(.pos 60)]),
   ((.exchange 58 62 0),[(.neg 62),(.neg 58),(.pos 59),(.pos 64)]),
   ((.exchange 58 63 0),[(.neg 63),(.neg 58),(.pos 60),(.pos 64)]),
   ((.exchange 58 63 3),[(.neg 63),(.neg 58),(.pos 56),(.pos 61)]),
   ((.exchange 58 67 0),[(.neg 67),(.neg 58),(.pos 60),(.pos 68)]),
   ((.exchange 58 69 0),[(.neg 69),(.neg 58),(.pos 64),(.pos 68)]),
   ((.exchange 59 1 3),[(.neg 59),(.neg 1),(.pos 55),(.pos 57),(.pos 62)]),
   ((.exchange 59 12 6),[(.neg 59),(.neg 12),(.pos 36),(.pos 43),(.pos 49)]),
   ((.exchange 59 17 1),[(.neg 59),(.neg 17),(.pos 58),(.pos 60)]),
   ((.exchange 59 22 1),[(.neg 59),(.neg 22),(.pos 58),(.pos 64)]),
   ((.exchange 59 24 1),[(.neg 59),(.neg 24),(.pos 60),(.pos 64)]),
   ((.exchange 59 28 1),[(.neg 59),(.neg 28),(.pos 58),(.pos 68)]),
   ((.exchange 59 30 1),[(.neg 59),(.neg 30),(.pos 60),(.pos 68)]),
   ((.exchange 59 31 1),[(.neg 59),(.neg 31),(.pos 58),(.pos 64),(.pos 68)]),
   ((.exchange 59 37 1),[(.neg 59),(.neg 37),(.pos 58),(.pos 60)]),
   ((.exchange 59 37 6),[(.neg 59),(.neg 37),(.pos 36),(.pos 38)]),
   ((.exchange 59 39 3),[(.neg 59),(.neg 39),(.pos 55),(.pos 62)]),
   ((.exchange 59 41 3),[(.neg 59),(.neg 41),(.pos 57),(.pos 62)]),
   ((.exchange 59 41 6),[(.neg 59),(.neg 41),(.pos 38),(.pos 43)]),
   ((.exchange 59 42 1),[(.neg 59),(.neg 42),(.pos 58),(.pos 64)]),
   ((.exchange 59 44 1),[(.neg 59),(.neg 44),(.pos 60),(.pos 64)]),
   ((.exchange 59 44 6),[(.neg 59),(.neg 44),(.pos 38),(.pos 43)]),
   ((.exchange 59 47 6),[(.neg 59),(.neg 47),(.pos 38),(.pos 49)]),
   ((.exchange 59 48 1),[(.neg 59),(.neg 48),(.pos 58),(.pos 68)]),
   ((.exchange 59 50 1),[(.neg 59),(.neg 50),(.pos 60),(.pos 68)]),
   ((.exchange 59 52 3),[(.neg 59),(.neg 52),(.pos 62),(.pos 66)]),
   ((.exchange 59 52 6),[(.neg 59),(.neg 52),(.pos 43),(.pos 49)]),
   ((.exchange 59 54 1),[(.neg 59),(.neg 54),(.pos 64),(.pos 68)]),
   ((.exchange 59 56 1),[(.neg 59),(.neg 56),(.pos 58),(.pos 60)]),
   ((.exchange 59 61 1),[(.neg 61),(.neg 59),(.pos 58),(.pos 64)]),
   ((.exchange 59 61 3),[(.neg 61),(.neg 59),(.pos 55),(.pos 62)]),
   ((.exchange 59 65 1),[(.neg 65),(.neg 59),(.pos 58),(.pos 68)]),
   ((.exchange 59 65 3),[(.neg 65),(.neg 59),(.pos 55),(.pos 66)]),
   ((.exchange 59 67 3),[(.neg 67),(.neg 59),(.pos 57),(.pos 66)]),
   ((.exchange 59 69 1),[(.neg 69),(.neg 59),(.pos 64),(.pos 68)]),
   ((.exchange 59 69 3),[(.neg 69),(.neg 59),(.pos 62),(.pos 66)]),
   ((.exchange 60 4 6),[(.neg 60),(.neg 4),(.pos 38),(.pos 44)]),
   ((.exchange 60 5 3),[(.neg 60),(.neg 5),(.pos 56),(.pos 57),(.pos 67)]),
   ((.exchange 60 5 6),[(.neg 60),(.neg 5),(.pos 37),(.pos 38),(.pos 50)]),
   ((.exchange 60 8 6),[(.neg 60),(.neg 8),(.pos 38),(.pos 50)]),
   ((.exchange 60 11 3),[(.neg 60),(.neg 11),(.pos 57),(.pos 63),(.pos 67)]),
   ((.exchange 60 16 2),[(.neg 60),(.neg 16),(.pos 58),(.pos 59)]),
   ((.exchange 60 19 3),[(.neg 60),(.neg 19),(.pos 56),(.pos 57),(.pos 63)]),
   ((.exchange 60 26 3),[(.neg 60),(.neg 26),(.pos 56),(.pos 67)]),
   ((.exchange 60 27 3),[(.neg 60),(.neg 27),(.pos 57),(.pos 67)]),
   ((.exchange 60 28 2),[(.neg 60),(.neg 28),(.pos 58),(.pos 68)]),
   ((.exchange 60 29 2),[(.neg 60),(.neg 29),(.pos 59),(.pos 68)]),
   ((.exchange 60 31 2),[(.neg 60),(.neg 31),(.pos 58),(.pos 64),(.pos 68)])]

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



noncomputable def certificates_4 : List (Origin 70 1212 × List Sat.Literal) :=
  [((.exchange 60 33 3),[(.neg 60),(.neg 33),(.pos 63),(.pos 67)]),
   ((.exchange 60 34 2),[(.neg 60),(.neg 34),(.pos 64),(.pos 68)]),
   ((.exchange 60 35 6),[(.neg 60),(.neg 35),(.pos 37),(.pos 38)]),
   ((.exchange 60 36 2),[(.neg 60),(.neg 36),(.pos 58),(.pos 59)]),
   ((.exchange 60 39 3),[(.neg 60),(.neg 39),(.pos 56),(.pos 57),(.pos 63)]),
   ((.exchange 60 40 6),[(.neg 60),(.neg 40),(.pos 37),(.pos 44)]),
   ((.exchange 60 41 3),[(.neg 60),(.neg 41),(.pos 57),(.pos 63)]),
   ((.exchange 60 41 6),[(.neg 60),(.neg 41),(.pos 38),(.pos 44)]),
   ((.exchange 60 42 2),[(.neg 60),(.neg 42),(.pos 58),(.pos 64)]),
   ((.exchange 60 43 2),[(.neg 60),(.neg 43),(.pos 59),(.pos 64)]),
   ((.exchange 60 43 6),[(.neg 60),(.neg 43),(.pos 38),(.pos 44)]),
   ((.exchange 60 45 6),[(.neg 60),(.neg 45),(.pos 37),(.pos 38),(.pos 50)]),
   ((.exchange 60 46 3),[(.neg 60),(.neg 46),(.pos 56),(.pos 67)]),
   ((.exchange 60 48 2),[(.neg 60),(.neg 48),(.pos 58),(.pos 68)]),
   ((.exchange 60 54 6),[(.neg 60),(.neg 54),(.pos 44),(.pos 50)]),
   ((.exchange 60 61 2),[(.neg 61),(.neg 60),(.pos 58),(.pos 64)]),
   ((.exchange 60 61 3),[(.neg 61),(.neg 60),(.pos 56),(.pos 63)]),
   ((.exchange 60 62 2),[(.neg 62),(.neg 60),(.pos 59),(.pos 64)]),
   ((.exchange 60 65 2),[(.neg 65),(.neg 60),(.pos 58),(.pos 68)]),
   ((.exchange 60 65 3),[(.neg 65),(.neg 60),(.pos 56),(.pos 67)]),
   ((.exchange 60 69 2),[(.neg 69),(.neg 60),(.pos 64),(.pos 68)]),
   ((.exchange 61 0 4),[(.neg 61),(.neg 0),(.pos 55),(.pos 56),(.pos 58)]),
   ((.exchange 61 9 6),[(.neg 61),(.neg 9),(.pos 39),(.pos 51)]),
   ((.exchange 61 12 6),[(.neg 61),(.neg 12),(.pos 42),(.pos 51)]),
   ((.exchange 61 17 4),[(.neg 61),(.neg 17),(.pos 56),(.pos 58)]),
   ((.exchange 61 21 0),[(.neg 61),(.neg 21),(.pos 62),(.pos 63)]),
   ((.exchange 61 23 0),[(.neg 61),(.neg 23),(.pos 62),(.pos 64)]),
   ((.exchange 61 24 0),[(.neg 61),(.neg 24),(.pos 63),(.pos 64)]),
   ((.exchange 61 25 4),[(.neg 61),(.neg 25),(.pos 55),(.pos 65)]),
   ((.exchange 61 26 4),[(.neg 61),(.neg 26),(.pos 56),(.pos 65)]),
   ((.exchange 61 27 4),[(.neg 61),(.neg 27),(.pos 55),(.pos 56),(.pos 65)]),
   ((.exchange 61 28 4),[(.neg 61),(.neg 28),(.pos 58),(.pos 65)]),
   ((.exchange 61 29 0),[(.neg 61),(.neg 29),(.pos 62),(.pos 64),(.pos 69)]),
   ((.exchange 61 32 0),[(.neg 61),(.neg 32),(.pos 62),(.pos 69)]),
   ((.exchange 61 33 0),[(.neg 61),(.neg 33),(.pos 63),(.pos 69)]),
   ((.exchange 61 34 0),[(.neg 61),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 61 41 0),[(.neg 61),(.neg 41),(.pos 62),(.pos 63)]),
   ((.exchange 61 43 0),[(.neg 61),(.neg 43),(.pos 62),(.pos 64)]),
   ((.exchange 61 45 4),[(.neg 61),(.neg 45),(.pos 55),(.pos 65)]),
   ((.exchange 61 46 4),[(.neg 61),(.neg 46),(.pos 56),(.pos 65)]),
   ((.exchange 61 46 6),[(.neg 61),(.neg 46),(.pos 40),(.pos 51)]),
   ((.exchange 61 48 4),[(.neg 61),(.neg 48),(.pos 58),(.pos 65)]),
   ((.exchange 61 48 6),[(.neg 61),(.neg 48),(.pos 42),(.pos 51)]),
   ((.exchange 61 52 6),[(.neg 61),(.neg 52),(.pos 39),(.pos 51)]),
   ((.exchange 61 57 0),[(.neg 61),(.neg 57),(.pos 62),(.pos 63)]),
   ((.exchange 61 59 4),[(.neg 61),(.neg 59),(.pos 55),(.pos 58)]),
   ((.exchange 61 66 4),[(.neg 66),(.neg 61),(.pos 55),(.pos 65)]),
   ((.exchange 62 3 6),[(.neg 62),(.neg 3),(.pos 39),(.pos 41),(.pos 43)]),
   ((.exchange 62 5 4),[(.neg 62),(.neg 5),(.pos 55),(.pos 57),(.pos 66)]),
   ((.exchange 62 11 6),[(.neg 62),(.neg 11),(.pos 41),(.pos 52)]),
   ((.exchange 62 13 6),[(.neg 62),(.neg 13),(.pos 43),(.pos 52)]),
   ((.exchange 62 16 4),[(.neg 62),(.neg 16),(.pos 55),(.pos 59)]),
   ((.exchange 62 18 4),[(.neg 62),(.neg 18),(.pos 57),(.pos 59)]),
   ((.exchange 62 22 1),[(.neg 62),(.neg 22),(.pos 61),(.pos 64)]),
   ((.exchange 62 24 1),[(.neg 62),(.neg 24),(.pos 63),(.pos 64)]),
   ((.exchange 62 25 4),[(.neg 62),(.neg 25),(.pos 55),(.pos 66)]),
   ((.exchange 62 29 4),[(.neg 62),(.neg 29),(.pos 59),(.pos 66)]),
   ((.exchange 62 31 1),[(.neg 62),(.neg 31),(.pos 61),(.pos 69)]),
   ((.exchange 62 33 1),[(.neg 62),(.neg 33),(.pos 63),(.pos 69)]),
   ((.exchange 62 34 1),[(.neg 62),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 62 36 4),[(.neg 62),(.neg 36),(.pos 55),(.pos 59)]),
   ((.exchange 62 45 6),[(.neg 62),(.neg 45),(.pos 39),(.pos 52)]),
   ((.exchange 62 49 4),[(.neg 62),(.neg 49),(.pos 59),(.pos 66)]),
   ((.exchange 62 51 6),[(.neg 62),(.neg 51),(.pos 39),(.pos 52)]),
   ((.exchange 62 54 1),[(.neg 62),(.neg 54),(.pos 64),(.pos 69)]),
   ((.exchange 62 58 4),[(.neg 62),(.neg 58),(.pos 55),(.pos 59)]),
   ((.exchange 62 68 4),[(.neg 68),(.neg 62),(.pos 59),(.pos 66)]),
   ((.exchange 63 0 6),[(.neg 63),(.neg 0),(.pos 40),(.pos 41),(.pos 44)]),
   ((.exchange 63 1 6),[(.neg 63),(.neg 1),(.pos 40),(.pos 41)]),
   ((.exchange 63 3 6),[(.neg 63),(.neg 3),(.pos 40),(.pos 44)]),
   ((.exchange 63 4 6),[(.neg 63),(.neg 4),(.pos 41),(.pos 44)]),
   ((.exchange 63 11 6),[(.neg 63),(.neg 11),(.pos 41),(.pos 53)]),
   ((.exchange 63 16 2),[(.neg 63),(.neg 16),(.pos 61),(.pos 62),(.pos 64)]),
   ((.exchange 63 17 4),[(.neg 63),(.neg 17),(.pos 56),(.pos 60)]),
   ((.exchange 63 18 4),[(.neg 63),(.neg 18),(.pos 57),(.pos 60)]),
   ((.exchange 63 22 2),[(.neg 63),(.neg 22),(.pos 61),(.pos 64)]),
   ((.exchange 63 23 2),[(.neg 63),(.neg 23),(.pos 62),(.pos 64)]),
   ((.exchange 63 26 4),[(.neg 63),(.neg 26),(.pos 56),(.pos 67)]),
   ((.exchange 63 27 4),[(.neg 63),(.neg 27),(.pos 57),(.pos 67)]),
   ((.exchange 63 29 2),[(.neg 63),(.neg 29),(.pos 62),(.pos 64),(.pos 69)]),
   ((.exchange 63 31 2),[(.neg 63),(.neg 31),(.pos 61),(.pos 69)]),
   ((.exchange 63 34 2),[(.neg 63),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 63 36 4),[(.neg 63),(.neg 36),(.pos 56),(.pos 57),(.pos 60)]),
   ((.exchange 63 38 4),[(.neg 63),(.neg 38),(.pos 57),(.pos 60)]),
   ((.exchange 63 38 6),[(.neg 63),(.neg 38),(.pos 41),(.pos 44)]),
   ((.exchange 63 39 6),[(.neg 63),(.neg 39),(.pos 40),(.pos 41)]),
   ((.exchange 63 46 4),[(.neg 63),(.neg 46),(.pos 56),(.pos 67)]),
   ((.exchange 63 47 4),[(.neg 63),(.neg 47),(.pos 57),(.pos 67)]),
   ((.exchange 63 47 6),[(.neg 63),(.neg 47),(.pos 41),(.pos 53)]),
   ((.exchange 63 50 4),[(.neg 63),(.neg 50),(.pos 60),(.pos 67)]),
   ((.exchange 63 52 6),[(.neg 63),(.neg 52),(.pos 41),(.pos 53)]),
   ((.exchange 63 58 4),[(.neg 63),(.neg 58),(.pos 56),(.pos 60)]),
   ((.exchange 63 59 4),[(.neg 63),(.neg 59),(.pos 57),(.pos 60)]),
   ((.exchange 63 66 4),[(.neg 66),(.neg 63),(.pos 57),(.pos 67)]),
   ((.exchange 64 0 6),[(.neg 64),(.neg 0),(.pos 42),(.pos 43),(.pos 44)]),
   ((.exchange 64 3 6),[(.neg 64),(.neg 3),(.pos 42),(.pos 44)]),
   ((.exchange 64 4 6),[(.neg 64),(.neg 4),(.pos 43),(.pos 44)]),
   ((.exchange 64 6 6),[(.neg 64),(.neg 6),(.pos 42),(.pos 43),(.pos 54)]),
   ((.exchange 64 12 6),[(.neg 64),(.neg 12),(.pos 42),(.pos 54)]),
   ((.exchange 64 13 6),[(.neg 64),(.neg 13),(.pos 43),(.pos 54)]),
   ((.exchange 64 14 6),[(.neg 64),(.neg 14),(.pos 44),(.pos 54)]),
   ((.exchange 64 16 4),[(.neg 64),(.neg 16),(.pos 58),(.pos 59)]),
   ((.exchange 64 17 4),[(.neg 64),(.neg 17),(.pos 58),(.pos 60)]),
   ((.exchange 64 18 4),[(.neg 64),(.neg 18),(.pos 59),(.pos 60)]),
   ((.exchange 64 19 3),[(.neg 64),(.neg 19),(.pos 61),(.pos 62)]),
   ((.exchange 64 20 3),[(.neg 64),(.neg 20),(.pos 61),(.pos 63)]),
   ((.exchange 64 21 3),[(.neg 64),(.neg 21),(.pos 62),(.pos 63)]),
   ((.exchange 64 26 4),[(.neg 64),(.neg 26),(.pos 58),(.pos 60),(.pos 68)]),
   ((.exchange 64 28 4),[(.neg 64),(.neg 28),(.pos 58),(.pos 68)]),
   ((.exchange 64 29 4),[(.neg 64),(.neg 29),(.pos 59),(.pos 68)]),
   ((.exchange 64 30 4),[(.neg 64),(.neg 30),(.pos 60),(.pos 68)]),
   ((.exchange 64 31 3),[(.neg 64),(.neg 31),(.pos 61),(.pos 69)]),
   ((.exchange 64 32 3),[(.neg 64),(.neg 32),(.pos 62),(.pos 69)]),
   ((.exchange 64 33 3),[(.neg 64),(.neg 33),(.pos 63),(.pos 69)]),
   ((.exchange 64 36 4),[(.neg 64),(.neg 36),(.pos 58),(.pos 59)]),
   ((.exchange 64 37 4),[(.neg 64),(.neg 37),(.pos 58),(.pos 60)]),
   ((.exchange 64 38 4),[(.neg 64),(.neg 38),(.pos 59),(.pos 60)]),
   ((.exchange 64 41 3),[(.neg 64),(.neg 41),(.pos 62),(.pos 63)]),
   ((.exchange 64 50 6),[(.neg 64),(.neg 50),(.pos 44),(.pos 54)]),
   ((.exchange 64 52 3),[(.neg 64),(.neg 52),(.pos 62),(.pos 69)]),
   ((.exchange 64 55 3),[(.neg 64),(.neg 55),(.pos 61),(.pos 62)]),
   ((.exchange 64 56 3),[(.neg 64),(.neg 56),(.pos 61),(.pos 63)]),
   ((.exchange 64 56 4),[(.neg 64),(.neg 56),(.pos 58),(.pos 60)]),
   ((.exchange 64 57 3),[(.neg 64),(.neg 57),(.pos 62),(.pos 63)]),
   ((.exchange 64 57 4),[(.neg 64),(.neg 57),(.pos 59),(.pos 60)]),
   ((.exchange 64 65 4),[(.neg 65),(.neg 64),(.pos 58),(.pos 68)]),
   ((.exchange 64 66 3),[(.neg 66),(.neg 64),(.pos 62),(.pos 69)]),
   ((.exchange 64 66 4),[(.neg 66),(.neg 64),(.pos 59),(.pos 68)])]

theorem certificates_4_valid : ∀ oc ∈ certificates_4,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.MaskOrigins.maskOrigins_sound (grid := (fun i : Fin 70 => N8R4.gridMasks.get i.val))
  have hchecks : ∀ i : Fin 128,
    Papers.RationalityTen.MatroidChecked.MaskOrigins.MaskOrigin (fun i : Fin 70 => N8R4.gridMasks.get i.val) (7 : Fin 8) old newIndex models
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



noncomputable def certificates_5 : List (Origin 70 1212 × List Sat.Literal) :=
  [((.exchange 64 67 4),[(.neg 67),(.neg 64),(.pos 60),(.pos 68)]),
   ((.exchange 65 0 5),[(.neg 65),(.neg 0),(.pos 55),(.pos 56),(.pos 58)]),
   ((.exchange 65 0 6),[(.neg 65),(.neg 0),(.pos 45),(.pos 46),(.pos 48)]),
   ((.exchange 65 8 6),[(.neg 65),(.neg 8),(.pos 45),(.pos 46),(.pos 48)]),
   ((.exchange 65 9 6),[(.neg 65),(.neg 9),(.pos 45),(.pos 51)]),
   ((.exchange 65 10 6),[(.neg 65),(.neg 10),(.pos 46),(.pos 51)]),
   ((.exchange 65 12 6),[(.neg 65),(.neg 12),(.pos 48),(.pos 51)]),
   ((.exchange 65 16 5),[(.neg 65),(.neg 16),(.pos 55),(.pos 58)]),
   ((.exchange 65 18 5),[(.neg 65),(.neg 18),(.pos 55),(.pos 56),(.pos 58)]),
   ((.exchange 65 19 5),[(.neg 65),(.neg 19),(.pos 55),(.pos 61)]),
   ((.exchange 65 20 5),[(.neg 65),(.neg 20),(.pos 56),(.pos 61)]),
   ((.exchange 65 22 5),[(.neg 65),(.neg 22),(.pos 58),(.pos 61)]),
   ((.exchange 65 27 0),[(.neg 65),(.neg 27),(.pos 66),(.pos 67)]),
   ((.exchange 65 29 0),[(.neg 65),(.neg 29),(.pos 66),(.pos 68)]),
   ((.exchange 65 30 0),[(.neg 65),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 65 32 0),[(.neg 65),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 65 34 0),[(.neg 65),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 65 38 5),[(.neg 65),(.neg 38),(.pos 55),(.pos 56),(.pos 58)]),
   ((.exchange 65 42 5),[(.neg 65),(.neg 42),(.pos 58),(.pos 61)]),
   ((.exchange 65 47 0),[(.neg 65),(.neg 47),(.pos 66),(.pos 67)]),
   ((.exchange 65 50 0),[(.neg 65),(.neg 50),(.pos 67),(.pos 68)]),
   ((.exchange 65 53 0),[(.neg 65),(.neg 53),(.pos 67),(.pos 69)]),
   ((.exchange 65 59 0),[(.neg 65),(.neg 59),(.pos 66),(.pos 68)]),
   ((.exchange 65 59 5),[(.neg 65),(.neg 59),(.pos 55),(.pos 58)]),
   ((.exchange 65 60 0),[(.neg 65),(.neg 60),(.pos 67),(.pos 68)]),
   ((.exchange 65 62 0),[(.neg 65),(.neg 62),(.pos 66),(.pos 69)]),
   ((.exchange 65 62 5),[(.neg 65),(.neg 62),(.pos 55),(.pos 61)]),
   ((.exchange 66 0 5),[(.neg 66),(.neg 0),(.pos 55),(.pos 57),(.pos 59)]),
   ((.exchange 66 1 6),[(.neg 66),(.neg 1),(.pos 45),(.pos 47),(.pos 52)]),
   ((.exchange 66 3 1),[(.neg 66),(.neg 3),(.pos 65),(.pos 67),(.pos 68),(.pos 69)]),
   ((.exchange 66 5 6),[(.neg 66),(.neg 5),(.pos 45),(.pos 47)]),
   ((.exchange 66 6 6),[(.neg 66),(.neg 6),(.pos 45),(.pos 49)]),
   ((.exchange 66 8 6),[(.neg 66),(.neg 8),(.pos 47),(.pos 49)]),
   ((.exchange 66 9 6),[(.neg 66),(.neg 9),(.pos 45),(.pos 52)]),
   ((.exchange 66 10 1),[(.neg 66),(.neg 10),(.pos 65),(.pos 67),(.pos 69)]),
   ((.exchange 66 16 5),[(.neg 66),(.neg 16),(.pos 55),(.pos 59)]),
   ((.exchange 66 17 5),[(.neg 66),(.neg 17),(.pos 55),(.pos 57),(.pos 59)]),
   ((.exchange 66 19 5),[(.neg 66),(.neg 19),(.pos 55),(.pos 62)]),
   ((.exchange 66 21 5),[(.neg 66),(.neg 21),(.pos 57),(.pos 62)]),
   ((.exchange 66 23 5),[(.neg 66),(.neg 23),(.pos 59),(.pos 62)]),
   ((.exchange 66 26 1),[(.neg 66),(.neg 26),(.pos 65),(.pos 67)]),
   ((.exchange 66 28 1),[(.neg 66),(.neg 28),(.pos 65),(.pos 68)]),
   ((.exchange 66 31 1),[(.neg 66),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 66 33 1),[(.neg 66),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 66 34 1),[(.neg 66),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 66 35 6),[(.neg 66),(.neg 35),(.pos 45),(.pos 47)]),
   ((.exchange 66 36 6),[(.neg 66),(.neg 36),(.pos 45),(.pos 49)]),
   ((.exchange 66 39 6),[(.neg 66),(.neg 39),(.pos 45),(.pos 52)]),
   ((.exchange 66 41 5),[(.neg 66),(.neg 41),(.pos 57),(.pos 62)]),
   ((.exchange 66 41 6),[(.neg 66),(.neg 41),(.pos 47),(.pos 52)]),
   ((.exchange 66 43 6),[(.neg 66),(.neg 43),(.pos 49),(.pos 52)]),
   ((.exchange 66 44 1),[(.neg 66),(.neg 44),(.pos 67),(.pos 68),(.pos 69)]),
   ((.exchange 66 46 1),[(.neg 66),(.neg 46),(.pos 65),(.pos 67)]),
   ((.exchange 66 48 6),[(.neg 66),(.neg 48),(.pos 45),(.pos 49)]),
   ((.exchange 66 50 1),[(.neg 66),(.neg 50),(.pos 67),(.pos 68)]),
   ((.exchange 66 50 6),[(.neg 66),(.neg 50),(.pos 47),(.pos 49)]),
   ((.exchange 66 51 6),[(.neg 66),(.neg 51),(.pos 45),(.pos 52)]),
   ((.exchange 66 54 6),[(.neg 66),(.neg 54),(.pos 49),(.pos 52)]),
   ((.exchange 66 58 1),[(.neg 66),(.neg 58),(.pos 65),(.pos 68)]),
   ((.exchange 66 58 5),[(.neg 66),(.neg 58),(.pos 55),(.pos 59)]),
   ((.exchange 66 60 1),[(.neg 66),(.neg 60),(.pos 67),(.pos 68)]),
   ((.exchange 66 60 5),[(.neg 66),(.neg 60),(.pos 57),(.pos 59)]),
   ((.exchange 66 61 1),[(.neg 66),(.neg 61),(.pos 65),(.pos 69)]),
   ((.exchange 66 61 5),[(.neg 66),(.neg 61),(.pos 55),(.pos 62)]),
   ((.exchange 66 63 5),[(.neg 66),(.neg 63),(.pos 57),(.pos 62)]),
   ((.exchange 66 64 1),[(.neg 66),(.neg 64),(.pos 68),(.pos 69)]),
   ((.exchange 66 64 5),[(.neg 66),(.neg 64),(.pos 59),(.pos 62)]),
   ((.exchange 67 3 6),[(.neg 67),(.neg 3),(.pos 46),(.pos 50),(.pos 53)]),
   ((.exchange 67 6 2),[(.neg 67),(.neg 6),(.pos 65),(.pos 66),(.pos 68)]),
   ((.exchange 67 6 6),[(.neg 67),(.neg 6),(.pos 46),(.pos 47),(.pos 50)]),
   ((.exchange 67 8 6),[(.neg 67),(.neg 8),(.pos 47),(.pos 50)]),
   ((.exchange 67 11 6),[(.neg 67),(.neg 11),(.pos 47),(.pos 53)]),
   ((.exchange 67 17 5),[(.neg 67),(.neg 17),(.pos 56),(.pos 60)]),
   ((.exchange 67 18 5),[(.neg 67),(.neg 18),(.pos 57),(.pos 60)]),
   ((.exchange 67 21 5),[(.neg 67),(.neg 21),(.pos 57),(.pos 63)]),
   ((.exchange 67 24 5),[(.neg 67),(.neg 24),(.pos 60),(.pos 63)]),
   ((.exchange 67 25 2),[(.neg 67),(.neg 25),(.pos 65),(.pos 66)]),
   ((.exchange 67 28 2),[(.neg 67),(.neg 28),(.pos 65),(.pos 68)]),
   ((.exchange 67 29 2),[(.neg 67),(.neg 29),(.pos 66),(.pos 68)]),
   ((.exchange 67 31 2),[(.neg 67),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 67 32 2),[(.neg 67),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 67 37 5),[(.neg 67),(.neg 37),(.pos 56),(.pos 60)]),
   ((.exchange 67 38 5),[(.neg 67),(.neg 38),(.pos 57),(.pos 60)]),
   ((.exchange 67 38 6),[(.neg 67),(.neg 38),(.pos 47),(.pos 50)]),
   ((.exchange 67 39 6),[(.neg 67),(.neg 39),(.pos 46),(.pos 47),(.pos 53)]),
   ((.exchange 67 40 5),[(.neg 67),(.neg 40),(.pos 56),(.pos 63)]),
   ((.exchange 67 41 6),[(.neg 67),(.neg 41),(.pos 47),(.pos 53)]),
   ((.exchange 67 45 2),[(.neg 67),(.neg 45),(.pos 65),(.pos 66)]),
   ((.exchange 67 45 6),[(.neg 67),(.neg 45),(.pos 46),(.pos 47)]),
   ((.exchange 67 51 2),[(.neg 67),(.neg 51),(.pos 65),(.pos 69)]),
   ((.exchange 67 52 6),[(.neg 67),(.neg 52),(.pos 47),(.pos 53)]),
   ((.exchange 67 54 2),[(.neg 67),(.neg 54),(.pos 68),(.pos 69)]),
   ((.exchange 67 54 6),[(.neg 67),(.neg 54),(.pos 50),(.pos 53)]),
   ((.exchange 67 58 2),[(.neg 67),(.neg 58),(.pos 65),(.pos 68)]),
   ((.exchange 67 58 5),[(.neg 67),(.neg 58),(.pos 56),(.pos 60)]),
   ((.exchange 67 61 2),[(.neg 67),(.neg 61),(.pos 65),(.pos 69)]),
   ((.exchange 67 62 2),[(.neg 67),(.neg 62),(.pos 66),(.pos 69)]),
   ((.exchange 67 62 5),[(.neg 67),(.neg 62),(.pos 57),(.pos 63)]),
   ((.exchange 67 64 2),[(.neg 67),(.neg 64),(.pos 68),(.pos 69)]),
   ((.exchange 68 4 5),[(.neg 68),(.neg 4),(.pos 59),(.pos 60),(.pos 64)]),
   ((.exchange 68 13 6),[(.neg 68),(.neg 13),(.pos 49),(.pos 54)]),
   ((.exchange 68 14 6),[(.neg 68),(.neg 14),(.pos 50),(.pos 54)]),
   ((.exchange 68 17 5),[(.neg 68),(.neg 17),(.pos 58),(.pos 60)]),
   ((.exchange 68 18 5),[(.neg 68),(.neg 18),(.pos 59),(.pos 60)]),
   ((.exchange 68 22 5),[(.neg 68),(.neg 22),(.pos 58),(.pos 64)]),
   ((.exchange 68 23 5),[(.neg 68),(.neg 23),(.pos 59),(.pos 64)]),
   ((.exchange 68 24 5),[(.neg 68),(.neg 24),(.pos 60),(.pos 64)]),
   ((.exchange 68 25 3),[(.neg 68),(.neg 25),(.pos 65),(.pos 66)]),
   ((.exchange 68 26 3),[(.neg 68),(.neg 26),(.pos 65),(.pos 67)]),
   ((.exchange 68 27 3),[(.neg 68),(.neg 27),(.pos 66),(.pos 67)]),
   ((.exchange 68 31 3),[(.neg 68),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 68 36 5),[(.neg 68),(.neg 36),(.pos 58),(.pos 59)]),
   ((.exchange 68 37 5),[(.neg 68),(.neg 37),(.pos 58),(.pos 60)]),
   ((.exchange 68 40 3),[(.neg 68),(.neg 40),(.pos 65),(.pos 67),(.pos 69)]),
   ((.exchange 68 42 5),[(.neg 68),(.neg 42),(.pos 58),(.pos 64)]),
   ((.exchange 68 43 5),[(.neg 68),(.neg 43),(.pos 59),(.pos 64)]),
   ((.exchange 68 45 3),[(.neg 68),(.neg 45),(.pos 65),(.pos 66)]),
   ((.exchange 68 46 3),[(.neg 68),(.neg 46),(.pos 65),(.pos 67)]),
   ((.exchange 68 47 6),[(.neg 68),(.neg 47),(.pos 49),(.pos 50)]),
   ((.exchange 68 51 3),[(.neg 68),(.neg 51),(.pos 65),(.pos 69)]),
   ((.exchange 68 53 3),[(.neg 68),(.neg 53),(.pos 67),(.pos 69)]),
   ((.exchange 68 55 3),[(.neg 68),(.neg 55),(.pos 65),(.pos 66)]),
   ((.exchange 68 56 3),[(.neg 68),(.neg 56),(.pos 65),(.pos 67)]),
   ((.exchange 68 56 5),[(.neg 68),(.neg 56),(.pos 58),(.pos 60)]),
   ((.exchange 68 57 3),[(.neg 68),(.neg 57),(.pos 66),(.pos 67)]),
   ((.exchange 68 61 3),[(.neg 68),(.neg 61),(.pos 65),(.pos 69)]),
   ((.exchange 68 61 5),[(.neg 68),(.neg 61),(.pos 58),(.pos 64)]),
   ((.exchange 68 62 3),[(.neg 68),(.neg 62),(.pos 66),(.pos 69)])]

theorem certificates_5_valid : ∀ oc ∈ certificates_5,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.MaskOrigins.maskOrigins_sound (grid := (fun i : Fin 70 => N8R4.gridMasks.get i.val))
  have hchecks : ∀ i : Fin 128,
    Papers.RationalityTen.MatroidChecked.MaskOrigins.MaskOrigin (fun i : Fin 70 => N8R4.gridMasks.get i.val) (7 : Fin 8) old newIndex models
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



noncomputable def certificates_6 : List (Origin 70 1212 × List Sat.Literal) :=
  [((.exchange 68 62 5),[(.neg 68),(.neg 62),(.pos 59),(.pos 64)]),
   ((.exchange 68 63 3),[(.neg 68),(.neg 63),(.pos 67),(.pos 69)]),
   ((.exchange 68 63 5),[(.neg 68),(.neg 63),(.pos 60),(.pos 64)]),
   ((.exchange 69 0 5),[(.neg 69),(.neg 0),(.pos 61),(.pos 62),(.pos 63),(.pos 64)]),
   ((.exchange 69 9 6),[(.neg 69),(.neg 9),(.pos 51),(.pos 52)]),
   ((.exchange 69 10 6),[(.neg 69),(.neg 10),(.pos 51),(.pos 53)]),
   ((.exchange 69 12 6),[(.neg 69),(.neg 12),(.pos 51),(.pos 54)]),
   ((.exchange 69 14 6),[(.neg 69),(.neg 14),(.pos 53),(.pos 54)]),
   ((.exchange 69 20 5),[(.neg 69),(.neg 20),(.pos 61),(.pos 63)]),
   ((.exchange 69 22 5),[(.neg 69),(.neg 22),(.pos 61),(.pos 64)]),
   ((.exchange 69 23 5),[(.neg 69),(.neg 23),(.pos 62),(.pos 64)]),
   ((.exchange 69 25 4),[(.neg 69),(.neg 25),(.pos 65),(.pos 66)]),
   ((.exchange 69 26 4),[(.neg 69),(.neg 26),(.pos 65),(.pos 67)]),
   ((.exchange 69 28 4),[(.neg 69),(.neg 28),(.pos 65),(.pos 68)]),
   ((.exchange 69 30 4),[(.neg 69),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 69 39 6),[(.neg 69),(.neg 39),(.pos 51),(.pos 52)]),
   ((.exchange 69 40 6),[(.neg 69),(.neg 40),(.pos 51),(.pos 53)]),
   ((.exchange 69 43 6),[(.neg 69),(.neg 43),(.pos 52),(.pos 54)]),
   ((.exchange 69 44 5),[(.neg 69),(.neg 44),(.pos 63),(.pos 64)]),
   ((.exchange 69 45 6),[(.neg 69),(.neg 45),(.pos 51),(.pos 52)]),
   ((.exchange 69 47 4),[(.neg 69),(.neg 47),(.pos 66),(.pos 67)]),
   ((.exchange 69 47 6),[(.neg 69),(.neg 47),(.pos 52),(.pos 53)]),
   ((.exchange 69 48 4),[(.neg 69),(.neg 48),(.pos 65),(.pos 68)]),
   ((.exchange 69 48 6),[(.neg 69),(.neg 48),(.pos 51),(.pos 54)]),
   ((.exchange 69 55 4),[(.neg 69),(.neg 55),(.pos 65),(.pos 66)]),
   ((.exchange 69 56 4),[(.neg 69),(.neg 56),(.pos 65),(.pos 67)]),
   ((.exchange 69 56 5),[(.neg 69),(.neg 56),(.pos 61),(.pos 63)]),
   ((.exchange 69 57 4),[(.neg 69),(.neg 57),(.pos 66),(.pos 67)]),
   ((.exchange 69 58 4),[(.neg 69),(.neg 58),(.pos 65),(.pos 68)]),
   ((.exchange 69 59 4),[(.neg 69),(.neg 59),(.pos 66),(.pos 68)]),
   ((.exchange 69 60 4),[(.neg 69),(.neg 60),(.pos 67),(.pos 68)]),
   (.newPoint,[(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 0),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 54),(.neg 53),(.neg 52),(.neg 49),(.neg 47),(.neg 44),(.neg 41),(.neg 38),(.pos 35),(.pos 36),(.pos 37),(.pos 39),(.pos 40),(.pos 42),(.pos 43),(.pos 45),(.pos 46),(.pos 48),(.pos 50),(.pos 51),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 61),(.pos 65)]),
   ((.excluded 1),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 47),(.neg 45),(.neg 41),(.neg 40),(.neg 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 42),(.pos 43),(.pos 44),(.pos 46),(.pos 48),(.pos 49),(.pos 50),(.pos 54),(.pos 58),(.pos 59),(.pos 60),(.pos 64),(.pos 68)]),
   ((.excluded 2),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 49),(.neg 47),(.neg 45),(.neg 44),(.neg 40),(.neg 38),(.neg 35),(.pos 36),(.pos 37),(.pos 39),(.pos 41),(.pos 42),(.pos 43),(.pos 46),(.pos 48),(.pos 50),(.pos 52),(.pos 58),(.pos 62)]),
   ((.excluded 3),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 49),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 35),(.pos 36),(.pos 37),(.pos 39),(.pos 42),(.pos 43),(.pos 46),(.pos 47),(.pos 48),(.pos 50),(.pos 53),(.pos 58),(.pos 67)]),
   ((.excluded 4),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 47),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 35),(.pos 36),(.pos 37),(.pos 39),(.pos 42),(.pos 43),(.pos 46),(.pos 48),(.pos 50),(.pos 58),(.pos 69)]),
   ((.excluded 5),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 47),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 35),(.pos 36),(.pos 37),(.pos 39),(.pos 42),(.pos 43),(.pos 46),(.pos 48),(.pos 50),(.pos 58),(.pos 63),(.pos 66)]),
   ((.excluded 6),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 47),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 35),(.pos 36),(.pos 37),(.pos 39),(.pos 42),(.pos 43),(.pos 46),(.pos 48),(.pos 50),(.pos 58),(.pos 63)]),
   ((.excluded 7),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 47),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 35),(.pos 36),(.pos 37),(.pos 39),(.pos 42),(.pos 43),(.pos 46),(.pos 48),(.pos 50),(.pos 58),(.pos 66)]),
   ((.excluded 8),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 47),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 35),(.pos 36),(.pos 37),(.pos 39),(.pos 42),(.pos 43),(.pos 46),(.pos 48),(.pos 50),(.pos 58)]),
   ((.excluded 9),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 58),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 48),(.neg 46),(.neg 44),(.neg 40),(.neg 37),(.pos 35),(.pos 36),(.pos 38),(.pos 39),(.pos 41),(.pos 42),(.pos 43),(.pos 45),(.pos 47),(.pos 49),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 59),(.pos 62),(.pos 66)]),
   ((.excluded 10),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 11),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 40),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 41),(.pos 42),(.pos 43),(.pos 52),(.pos 62),(.pos 67)]),
   ((.excluded 12),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 40),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 41),(.pos 42),(.pos 43),(.pos 52),(.pos 62),(.pos 68)]),
   ((.excluded 13),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 40),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 41),(.pos 42),(.pos 43),(.pos 52),(.pos 60),(.pos 62),(.pos 65)]),
   ((.excluded 14),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 40),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 41),(.pos 42),(.pos 43),(.pos 52),(.pos 60),(.pos 62)]),
   ((.excluded 15),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 40),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 41),(.pos 42),(.pos 43),(.pos 52),(.pos 62),(.pos 65)]),
   ((.excluded 16),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 40),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 41),(.pos 42),(.pos 43),(.pos 52),(.pos 62)]),
   ((.excluded 17),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 18),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 64)]),
   ((.excluded 19),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 69)]),
   ((.excluded 20),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 45),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 68)]),
   ((.excluded 21),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 45),(.pos 53),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 22),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 68)]),
   ((.excluded 23),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 45),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 24),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 44),(.pos 54),(.pos 64),(.pos 66)]),
   ((.excluded 25),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 44),(.pos 54),(.pos 64),(.pos 67)]),
   ((.excluded 26),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 44),(.pos 47),(.pos 54),(.pos 64),(.pos 65)]),
   ((.excluded 27),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 44),(.pos 47),(.pos 54),(.pos 64)]),
   ((.excluded 28),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 44),(.pos 54),(.pos 64),(.pos 65)]),
   ((.excluded 29),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 44),(.pos 54),(.pos 64)]),
   ((.excluded 30),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 37),(.neg 35),(.pos 36),(.pos 38),(.pos 39),(.pos 40),(.pos 42),(.pos 43),(.pos 49),(.pos 51),(.pos 59),(.pos 61),(.pos 67)]),
   ((.excluded 31),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 37),(.neg 35),(.pos 36),(.pos 38),(.pos 39),(.pos 40),(.pos 42),(.pos 43),(.pos 49),(.pos 51),(.pos 59),(.pos 61)]),
   ((.excluded 32),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 37),(.neg 35),(.pos 36),(.pos 38),(.pos 39),(.pos 42),(.pos 43),(.pos 49),(.pos 59),(.pos 67)]),
   ((.excluded 33),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 37),(.neg 35),(.pos 36),(.pos 38),(.pos 39),(.pos 42),(.pos 43),(.pos 49),(.pos 59),(.pos 69)]),
   ((.excluded 34),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 37),(.neg 35),(.pos 36),(.pos 38),(.pos 39),(.pos 42),(.pos 43),(.pos 49),(.pos 53),(.pos 59),(.pos 65)]),
   ((.excluded 35),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 37),(.neg 35),(.pos 36),(.pos 38),(.pos 39),(.pos 42),(.pos 43),(.pos 49),(.pos 53),(.pos 59)]),
   ((.excluded 36),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 37),(.neg 35),(.pos 36),(.pos 38),(.pos 39),(.pos 42),(.pos 43),(.pos 49),(.pos 59),(.pos 63),(.pos 65)]),
   ((.excluded 37),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 37),(.neg 35),(.pos 36),(.pos 38),(.pos 39),(.pos 42),(.pos 43),(.pos 49),(.pos 59),(.pos 63)]),
   ((.excluded 38),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 37),(.neg 35),(.pos 36),(.pos 38),(.pos 39),(.pos 42),(.pos 43),(.pos 49),(.pos 59),(.pos 65)]),
   ((.excluded 39),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 37),(.neg 35),(.pos 36),(.pos 38),(.pos 39),(.pos 42),(.pos 43),(.pos 49),(.pos 59)]),
   ((.excluded 40),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 40),(.pos 42),(.pos 43),(.pos 51),(.pos 61),(.pos 67)]),
   ((.excluded 41),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 40),(.pos 42),(.pos 43),(.pos 51),(.pos 60),(.pos 61),(.pos 66)]),
   ((.excluded 42),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 40),(.pos 42),(.pos 43),(.pos 51),(.pos 61),(.pos 66)]),
   ((.excluded 43),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 40),(.pos 42),(.pos 43),(.pos 47),(.pos 51),(.pos 60),(.pos 61)]),
   ((.excluded 44),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 40),(.pos 42),(.pos 43),(.pos 51),(.pos 60),(.pos 61)]),
   ((.excluded 45),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 40),(.pos 42),(.pos 43),(.pos 47),(.pos 51),(.pos 61),(.pos 68)]),
   ((.excluded 46),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 40),(.pos 42),(.pos 43),(.pos 47),(.pos 51),(.pos 61)]),
   ((.excluded 47),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 40),(.pos 42),(.pos 43),(.pos 51),(.pos 61),(.pos 68)]),
   ((.excluded 48),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 40),(.pos 42),(.pos 43),(.pos 51),(.pos 61)]),
   ((.excluded 49),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 50),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 67)]),
   ((.excluded 51),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 47),(.pos 60),(.pos 69)]),
   ((.excluded 52),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 47),(.pos 69)]),
   ((.excluded 53),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 60),(.pos 69)]),
   ((.excluded 54),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 69)]),
   ((.excluded 55),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 63),(.pos 66)]),
   ((.excluded 56),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 53),(.pos 60),(.pos 66)]),
   ((.excluded 57),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 53),(.pos 66)]),
   ((.excluded 58),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 60),(.pos 66)]),
   ((.excluded 59),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 66)]),
   ((.excluded 60),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 53),(.pos 68)]),
   ((.excluded 61),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 53),(.pos 60),(.pos 65)]),
   ((.excluded 62),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 53),(.pos 60)]),
   ((.excluded 63),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 53),(.pos 65)]),
   ((.excluded 64),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 53)]),
   ((.excluded 65),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 47),(.pos 60),(.pos 65)]),
   ((.excluded 66),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 47),(.pos 60)]),
   ((.excluded 67),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 60),(.pos 65)]),
   ((.excluded 68),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 60)]),
   ((.excluded 69),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 47),(.pos 63),(.pos 65)]),
   ((.excluded 70),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 47),(.pos 65)]),
   ((.excluded 71),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 63),(.pos 65)]),
   ((.excluded 72),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 65)]),
   ((.excluded 73),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 47),(.pos 63),(.pos 68)]),
   ((.excluded 74),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 47),(.pos 63)]),
   ((.excluded 75),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 47),(.pos 68)]),
   ((.excluded 76),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 47)]),
   ((.excluded 77),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 63),(.pos 68)]),
   ((.excluded 78),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 63)]),
   ((.excluded 79),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43),(.pos 68)]),
   ((.excluded 80),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.neg 35),(.pos 36),(.pos 39),(.pos 42),(.pos 43)]),
   ((.excluded 81),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 54),(.neg 52),(.neg 51),(.neg 49),(.neg 45),(.neg 43),(.neg 42),(.neg 39),(.neg 36),(.pos 35),(.pos 37),(.pos 38),(.pos 40),(.pos 41),(.pos 44),(.pos 46),(.pos 47),(.pos 48),(.pos 50),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 82),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 83),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 49),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 46),(.pos 47),(.pos 48),(.pos 50),(.pos 53),(.pos 62),(.pos 67)]),
   ((.excluded 84),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 49),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 46),(.pos 47),(.pos 48),(.pos 50),(.pos 53),(.pos 64),(.pos 67)]),
   ((.excluded 85),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 49),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 46),(.pos 47),(.pos 48),(.pos 50),(.pos 53),(.pos 59),(.pos 61),(.pos 67)]),
   ((.excluded 86),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 49),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 46),(.pos 47),(.pos 48),(.pos 50),(.pos 53),(.pos 59),(.pos 67)]),
   ((.excluded 87),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 49),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 46),(.pos 47),(.pos 48),(.pos 50),(.pos 53),(.pos 61),(.pos 67)]),
   ((.excluded 88),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 52),(.neg 51),(.neg 49),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 36),(.neg 35),(.pos 37),(.pos 46),(.pos 47),(.pos 48),(.pos 50),(.pos 53),(.pos 67)]),
   ((.excluded 89),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 36),(.pos 35),(.pos 37),(.pos 40),(.pos 46),(.pos 48),(.pos 50),(.pos 55),(.pos 56),(.pos 57),(.pos 59),(.pos 62),(.pos 66)]),
   ((.excluded 90),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 53),(.neg 52),(.neg 51),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 36),(.pos 35),(.pos 37),(.pos 40),(.pos 46),(.pos 48),(.pos 49),(.pos 50),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 68)]),
   ((.excluded 91),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 36),(.pos 35),(.pos 37),(.pos 40),(.pos 46),(.pos 48),(.pos 50),(.pos 55),(.pos 56),(.pos 57),(.pos 69)]),
   ((.excluded 92),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 51),(.neg 49),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 36),(.pos 35),(.pos 37),(.pos 40),(.pos 46),(.pos 48),(.pos 50),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 64)]),
   ((.excluded 93),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 51),(.neg 49),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 36),(.pos 35),(.pos 37),(.pos 40),(.pos 46),(.pos 48),(.pos 50),(.pos 52),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 94),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 36),(.pos 35),(.pos 37),(.pos 40),(.pos 46),(.pos 48),(.pos 50),(.pos 55),(.pos 56),(.pos 57),(.pos 64)]),
   ((.excluded 95),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 36),(.pos 35),(.pos 37),(.pos 40),(.pos 46),(.pos 48),(.pos 50),(.pos 55),(.pos 56),(.pos 57)])]

theorem certificates_6_valid : ∀ oc ∈ certificates_6,
    ValidOrigin U (7 : Fin 8) old newIndex models oc.1 oc.2 := by
  apply Papers.RationalityTen.MatroidChecked.MaskOrigins.maskOrigins_sound (grid := (fun i : Fin 70 => N8R4.gridMasks.get i.val))
  have hchecks : ∀ i : Fin 128,
    Papers.RationalityTen.MatroidChecked.MaskOrigins.MaskOrigin (fun i : Fin 70 => N8R4.gridMasks.get i.val) (7 : Fin 8) old newIndex models
      (certificates_6.get i).1 (certificates_6.get i).2 := by
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



end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C80

end
end
end BundlePart4

