module
public import Consolidated.SemanticData
public import Mathlib.Data.Fin.Tuple.Basic
public import MatroidCatalogue.Definitions
public import MatroidChecked.FastSemanticChecks
public import MatroidChecked.BitsetSemanticChecks
public import MatroidChecked.BitsetOrigins
public import MatroidChecked.MaskOrigins


section BundlePart4
/- Source: MatroidChecked/SemanticParts/Cases27Part00/Checks00.lean -/



@[expose] public section
noncomputable section


set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C82


noncomputable def certificates_0 : List (Origin 70 2165 × List Sat.Literal) :=
  [((.fixed 0),[(.pos 0)]),
   ((.fixed 1),[(.pos 1)]),
   ((.fixed 2),[(.pos 2)]),
   ((.fixed 3),[(.pos 3)]),
   ((.fixed 4),[(.pos 4)]),
   ((.fixed 5),[(.pos 5)]),
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
   ((.exchange 0 55 3),[(.neg 55),(.neg 0),(.pos 15),(.pos 35)]),
   ((.exchange 0 56 3),[(.neg 56),(.neg 0),(.pos 15),(.pos 35)]),
   ((.exchange 0 57 3),[(.neg 57),(.neg 0),(.pos 15),(.pos 35)]),
   ((.exchange 2 48 1),[(.neg 48),(.neg 2),(.pos 12),(.pos 42)]),
   ((.exchange 2 51 1),[(.neg 51),(.neg 2),(.pos 12),(.pos 42)]),
   ((.exchange 2 54 1),[(.neg 54),(.neg 2),(.pos 12),(.pos 42)]),
   ((.exchange 6 42 1),[(.neg 42),(.neg 6),(.pos 12),(.pos 48)]),
   ((.exchange 6 51 1),[(.neg 51),(.neg 6),(.pos 12),(.pos 48)]),
   ((.exchange 6 54 1),[(.neg 54),(.neg 6),(.pos 12),(.pos 48)]),
   ((.exchange 9 42 1),[(.neg 42),(.neg 9),(.pos 12),(.pos 51)]),
   ((.exchange 9 48 1),[(.neg 48),(.neg 9),(.pos 12),(.pos 51)]),
   ((.exchange 9 54 1),[(.neg 54),(.neg 9),(.pos 12),(.pos 51)]),
   ((.exchange 13 42 1),[(.neg 42),(.neg 13),(.pos 12),(.pos 54)]),
   ((.exchange 13 48 1),[(.neg 48),(.neg 13),(.pos 12),(.pos 54)]),
   ((.exchange 13 51 1),[(.neg 51),(.neg 13),(.pos 12),(.pos 54)]),
   ((.exchange 16 35 3),[(.neg 35),(.neg 16),(.pos 15),(.pos 55)]),
   ((.exchange 16 56 3),[(.neg 56),(.neg 16),(.pos 15),(.pos 55)]),
   ((.exchange 16 57 3),[(.neg 57),(.neg 16),(.pos 15),(.pos 55)]),
   ((.exchange 17 35 3),[(.neg 35),(.neg 17),(.pos 15),(.pos 56)]),
   ((.exchange 17 55 3),[(.neg 55),(.neg 17),(.pos 15),(.pos 56)]),
   ((.exchange 17 57 3),[(.neg 57),(.neg 17),(.pos 15),(.pos 56)]),
   ((.exchange 18 55 3),[(.neg 55),(.neg 18),(.pos 15),(.pos 57)]),
   ((.exchange 18 56 3),[(.neg 56),(.neg 18),(.pos 15),(.pos 57)]),
   ((.exchange 35 4 0),[(.neg 35),(.neg 4),(.pos 38),(.pos 41)]),
   ((.exchange 35 6 2),[(.neg 35),(.neg 6),(.pos 36),(.pos 45)]),
   ((.exchange 35 7 1),[(.neg 35),(.neg 7),(.pos 37),(.pos 46)]),
   ((.exchange 35 9 2),[(.neg 35),(.neg 9),(.pos 39),(.pos 45)]),
   ((.exchange 35 10 1),[(.neg 35),(.neg 10),(.pos 40),(.pos 46)]),
   ((.exchange 35 11 0),[(.neg 35),(.neg 11),(.pos 41),(.pos 47)]),
   ((.exchange 35 42 2),[(.neg 42),(.neg 35),(.pos 36),(.pos 39)]),
   ((.exchange 35 52 2),[(.neg 52),(.neg 35),(.pos 39),(.pos 45)]),
   ((.exchange 36 3 1),[(.neg 36),(.neg 3),(.pos 37),(.pos 42)]),
   ((.exchange 36 4 0),[(.neg 36),(.neg 4),(.pos 38),(.pos 43)]),
   ((.exchange 36 5 3),[(.neg 36),(.neg 5),(.pos 35),(.pos 45)]),
   ((.exchange 36 7 1),[(.neg 36),(.neg 7),(.pos 37),(.pos 48)]),
   ((.exchange 36 9 3),[(.neg 36),(.neg 9),(.pos 39),(.pos 45)]),
   ((.exchange 36 13 0),[(.neg 36),(.neg 13),(.pos 43),(.pos 49)]),
   ((.exchange 36 18 0),[(.neg 36),(.neg 18),(.pos 38),(.pos 59)]),
   ((.exchange 36 19 3),[(.neg 36),(.neg 19),(.pos 39),(.pos 55)]),
   ((.exchange 36 22 1),[(.neg 36),(.neg 22),(.pos 42),(.pos 58)]),
   ((.exchange 36 23 0),[(.neg 36),(.neg 23),(.pos 43),(.pos 59)]),
   ((.exchange 36 25 3),[(.neg 36),(.neg 25),(.pos 45),(.pos 55)]),
   ((.exchange 36 28 1),[(.neg 36),(.neg 28),(.pos 48),(.pos 58)]),
   ((.exchange 36 44 1),[(.neg 44),(.neg 36),(.pos 37),(.pos 42)]),
   ((.exchange 36 46 3),[(.neg 46),(.neg 36),(.pos 35),(.pos 45)]),
   ((.exchange 36 47 3),[(.neg 47),(.neg 36),(.pos 35),(.pos 45)]),
   ((.exchange 36 50 0),[(.neg 50),(.neg 36),(.pos 38),(.pos 49)]),
   ((.exchange 36 52 3),[(.neg 52),(.neg 36),(.pos 39),(.pos 45)]),
   ((.exchange 36 57 0),[(.neg 57),(.neg 36),(.pos 38),(.pos 59)]),
   ((.exchange 36 60 1),[(.neg 60),(.neg 36),(.pos 37),(.pos 58)]),
   ((.exchange 36 62 0),[(.neg 62),(.neg 36),(.pos 43),(.pos 59)]),
   ((.exchange 36 65 3),[(.neg 65),(.neg 36),(.pos 45),(.pos 55)]),
   ((.exchange 36 66 0),[(.neg 66),(.neg 36),(.pos 49),(.pos 59)]),
   ((.exchange 36 68 0),[(.neg 68),(.neg 36),(.pos 49),(.pos 59)]),
   ((.exchange 37 2 2),[(.neg 37),(.neg 2),(.pos 36),(.pos 42)]),
   ((.exchange 37 4 0),[(.neg 37),(.neg 4),(.pos 38),(.pos 44)]),
   ((.exchange 37 5 3),[(.neg 37),(.neg 5),(.pos 35),(.pos 46)]),
   ((.exchange 37 6 2),[(.neg 37),(.neg 6),(.pos 36),(.pos 48)]),
   ((.exchange 37 14 0),[(.neg 37),(.neg 14),(.pos 44),(.pos 50)]),
   ((.exchange 37 16 2),[(.neg 37),(.neg 16),(.pos 36),(.pos 58)]),
   ((.exchange 37 18 0),[(.neg 37),(.neg 18),(.pos 38),(.pos 60)]),
   ((.exchange 37 20 3),[(.neg 37),(.neg 20),(.pos 40),(.pos 56)]),
   ((.exchange 37 22 2),[(.neg 37),(.neg 22),(.pos 42),(.pos 58)]),
   ((.exchange 37 24 0),[(.neg 37),(.neg 24),(.pos 44),(.pos 60)]),
   ((.exchange 37 28 2),[(.neg 37),(.neg 28),(.pos 48),(.pos 58)]),
   ((.exchange 37 30 0),[(.neg 37),(.neg 30),(.pos 50),(.pos 60)]),
   ((.exchange 37 31 2),[(.neg 37),(.neg 31),(.pos 42),(.pos 48),(.pos 58)]),
   ((.exchange 37 34 2),[(.neg 37),(.neg 34),(.pos 42),(.pos 48),(.pos 58)]),
   ((.exchange 37 41 3),[(.neg 41),(.neg 37),(.pos 35),(.pos 40)]),
   ((.exchange 37 54 0),[(.neg 54),(.neg 37),(.pos 44),(.pos 50)]),
   ((.exchange 37 55 2),[(.neg 55),(.neg 37),(.pos 36),(.pos 58)]),
   ((.exchange 37 65 3),[(.neg 65),(.neg 37),(.pos 46),(.pos 56)]),
   ((.exchange 38 1 3),[(.neg 38),(.neg 1),(.pos 35),(.pos 41)]),
   ((.exchange 38 3 1),[(.neg 38),(.neg 3),(.pos 37),(.pos 44)]),
   ((.exchange 38 6 2),[(.neg 38),(.neg 6),(.pos 36),(.pos 49)]),
   ((.exchange 38 7 1),[(.neg 38),(.neg 7),(.pos 37),(.pos 50)]),
   ((.exchange 38 13 2),[(.neg 38),(.neg 13),(.pos 43),(.pos 49)]),
   ((.exchange 38 16 2),[(.neg 38),(.neg 16),(.pos 36),(.pos 59)]),
   ((.exchange 38 17 1),[(.neg 38),(.neg 17),(.pos 37),(.pos 60)]),
   ((.exchange 38 23 2),[(.neg 38),(.neg 23),(.pos 43),(.pos 59)]),
   ((.exchange 38 24 1),[(.neg 38),(.neg 24),(.pos 44),(.pos 60)]),
   ((.exchange 38 29 2),[(.neg 38),(.neg 29),(.pos 49),(.pos 59)]),
   ((.exchange 38 30 1),[(.neg 38),(.neg 30),(.pos 50),(.pos 60)]),
   ((.exchange 38 42 1),[(.neg 42),(.neg 38),(.pos 37),(.pos 44)]),
   ((.exchange 38 46 1),[(.neg 46),(.neg 38),(.pos 37),(.pos 50)]),
   ((.exchange 38 52 2),[(.neg 52),(.neg 38),(.pos 43),(.pos 49)]),
   ((.exchange 38 53 1),[(.neg 53),(.neg 38),(.pos 44),(.pos 50)]),
   ((.exchange 38 55 2),[(.neg 55),(.neg 38),(.pos 36),(.pos 59)]),
   ((.exchange 38 56 1),[(.neg 56),(.neg 38),(.pos 37),(.pos 60)]),
   ((.exchange 38 58 1),[(.neg 58),(.neg 38),(.pos 37),(.pos 60)]),
   ((.exchange 38 58 2),[(.neg 58),(.neg 38),(.pos 36),(.pos 59)]),
   ((.exchange 38 63 1),[(.neg 63),(.neg 38),(.pos 44),(.pos 60)]),
   ((.exchange 38 64 2),[(.neg 64),(.neg 38),(.pos 43),(.pos 59)])]

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



noncomputable def certificates_1 : List (Origin 70 2165 × List Sat.Literal) :=
  [((.exchange 38 66 2),[(.neg 66),(.neg 38),(.pos 49),(.pos 59)]),
   ((.exchange 38 67 1),[(.neg 67),(.neg 38),(.pos 50),(.pos 60)]),
   ((.exchange 38 68 2),[(.neg 68),(.neg 38),(.pos 49),(.pos 59)]),
   ((.exchange 39 3 1),[(.neg 39),(.neg 3),(.pos 40),(.pos 42)]),
   ((.exchange 39 4 0),[(.neg 39),(.neg 4),(.pos 41),(.pos 43)]),
   ((.exchange 39 11 0),[(.neg 39),(.neg 11),(.pos 41),(.pos 52)]),
   ((.exchange 39 21 0),[(.neg 39),(.neg 21),(.pos 41),(.pos 62)]),
   ((.exchange 39 25 4),[(.neg 39),(.neg 25),(.pos 45),(.pos 55)]),
   ((.exchange 39 30 0),[(.neg 39),(.neg 30),(.pos 41),(.pos 43),(.pos 52),(.pos 62)]),
   ((.exchange 39 31 1),[(.neg 39),(.neg 31),(.pos 51),(.pos 61)]),
   ((.exchange 39 32 0),[(.neg 39),(.neg 32),(.pos 52),(.pos 62)]),
   ((.exchange 39 33 0),[(.neg 39),(.neg 33),(.pos 41),(.pos 52),(.pos 62)]),
   ((.exchange 39 44 0),[(.neg 44),(.neg 39),(.pos 41),(.pos 43)]),
   ((.exchange 39 44 1),[(.neg 44),(.neg 39),(.pos 40),(.pos 42)]),
   ((.exchange 39 46 4),[(.neg 46),(.neg 39),(.pos 35),(.pos 45)]),
   ((.exchange 39 50 1),[(.neg 50),(.neg 39),(.pos 40),(.pos 42),(.pos 51)]),
   ((.exchange 39 53 1),[(.neg 53),(.neg 39),(.pos 40),(.pos 51)]),
   ((.exchange 39 56 1),[(.neg 56),(.neg 39),(.pos 40),(.pos 61)]),
   ((.exchange 39 57 0),[(.neg 57),(.neg 39),(.pos 41),(.pos 62)]),
   ((.exchange 39 59 0),[(.neg 59),(.neg 39),(.pos 43),(.pos 62)]),
   ((.exchange 39 63 0),[(.neg 63),(.neg 39),(.pos 41),(.pos 62)]),
   ((.exchange 39 64 0),[(.neg 64),(.neg 39),(.pos 43),(.pos 62)]),
   ((.exchange 39 64 1),[(.neg 64),(.neg 39),(.pos 42),(.pos 61)]),
   ((.exchange 39 67 4),[(.neg 67),(.neg 39),(.pos 35),(.pos 45),(.pos 55)]),
   ((.exchange 40 0 4),[(.neg 40),(.neg 0),(.pos 35),(.pos 37)]),
   ((.exchange 40 2 2),[(.neg 40),(.neg 2),(.pos 39),(.pos 42)]),
   ((.exchange 40 4 0),[(.neg 40),(.neg 4),(.pos 41),(.pos 44)]),
   ((.exchange 40 9 2),[(.neg 40),(.neg 9),(.pos 39),(.pos 51)]),
   ((.exchange 40 11 0),[(.neg 40),(.neg 11),(.pos 41),(.pos 53)]),
   ((.exchange 40 14 0),[(.neg 40),(.neg 14),(.pos 44),(.pos 53)]),
   ((.exchange 40 17 4),[(.neg 40),(.neg 17),(.pos 37),(.pos 56)]),
   ((.exchange 40 19 2),[(.neg 40),(.neg 19),(.pos 39),(.pos 61)]),
   ((.exchange 40 21 0),[(.neg 40),(.neg 21),(.pos 41),(.pos 63)]),
   ((.exchange 40 24 0),[(.neg 40),(.neg 24),(.pos 44),(.pos 63)]),
   ((.exchange 40 31 2),[(.neg 40),(.neg 31),(.pos 51),(.pos 61)]),
   ((.exchange 40 32 0),[(.neg 40),(.neg 32),(.pos 41),(.pos 53),(.pos 63)]),
   ((.exchange 40 33 0),[(.neg 40),(.neg 33),(.pos 53),(.pos 63)]),
   ((.exchange 40 38 4),[(.neg 40),(.neg 38),(.pos 35),(.pos 37)]),
   ((.exchange 40 47 4),[(.neg 47),(.neg 40),(.pos 35),(.pos 46)]),
   ((.exchange 40 52 0),[(.neg 52),(.neg 40),(.pos 41),(.pos 53)]),
   ((.exchange 40 52 2),[(.neg 52),(.neg 40),(.pos 39),(.pos 51)]),
   ((.exchange 40 54 0),[(.neg 54),(.neg 40),(.pos 44),(.pos 53)]),
   ((.exchange 40 55 2),[(.neg 55),(.neg 40),(.pos 39),(.pos 61)]),
   ((.exchange 40 57 0),[(.neg 57),(.neg 40),(.pos 41),(.pos 63)]),
   ((.exchange 40 58 2),[(.neg 58),(.neg 40),(.pos 42),(.pos 61)]),
   ((.exchange 40 62 0),[(.neg 62),(.neg 40),(.pos 41),(.pos 63)]),
   ((.exchange 40 64 2),[(.neg 64),(.neg 40),(.pos 42),(.pos 61)]),
   ((.exchange 40 65 4),[(.neg 65),(.neg 40),(.pos 46),(.pos 56)]),
   ((.exchange 40 69 2),[(.neg 69),(.neg 40),(.pos 51),(.pos 61)]),
   ((.exchange 41 2 2),[(.neg 41),(.neg 2),(.pos 39),(.pos 43)]),
   ((.exchange 41 3 1),[(.neg 41),(.neg 3),(.pos 40),(.pos 44)]),
   ((.exchange 41 5 4),[(.neg 41),(.neg 5),(.pos 35),(.pos 47)]),
   ((.exchange 41 8 4),[(.neg 41),(.neg 8),(.pos 38),(.pos 47)]),
   ((.exchange 41 9 2),[(.neg 41),(.neg 9),(.pos 39),(.pos 52)]),
   ((.exchange 41 10 1),[(.neg 41),(.neg 10),(.pos 40),(.pos 53)]),
   ((.exchange 41 13 2),[(.neg 41),(.neg 13),(.pos 43),(.pos 52)]),
   ((.exchange 41 14 1),[(.neg 41),(.neg 14),(.pos 44),(.pos 53)]),
   ((.exchange 41 19 2),[(.neg 41),(.neg 19),(.pos 39),(.pos 62)]),
   ((.exchange 41 20 1),[(.neg 41),(.neg 20),(.pos 40),(.pos 63)]),
   ((.exchange 41 23 2),[(.neg 41),(.neg 23),(.pos 43),(.pos 62)]),
   ((.exchange 41 24 1),[(.neg 41),(.neg 24),(.pos 44),(.pos 63)]),
   ((.exchange 41 27 4),[(.neg 41),(.neg 27),(.pos 47),(.pos 57)]),
   ((.exchange 41 32 2),[(.neg 41),(.neg 32),(.pos 52),(.pos 62)]),
   ((.exchange 41 33 1),[(.neg 41),(.neg 33),(.pos 53),(.pos 63)]),
   ((.exchange 41 50 1),[(.neg 50),(.neg 41),(.pos 44),(.pos 53)]),
   ((.exchange 41 59 2),[(.neg 59),(.neg 41),(.pos 43),(.pos 62)]),
   ((.exchange 41 64 1),[(.neg 64),(.neg 41),(.pos 44),(.pos 63)]),
   ((.exchange 41 64 2),[(.neg 64),(.neg 41),(.pos 43),(.pos 62)]),
   ((.exchange 41 67 1),[(.neg 67),(.neg 41),(.pos 53),(.pos 63)]),
   ((.exchange 42 0 4),[(.neg 42),(.neg 0),(.pos 36),(.pos 37)]),
   ((.exchange 42 1 3),[(.neg 42),(.neg 1),(.pos 39),(.pos 40)]),
   ((.exchange 42 16 4),[(.neg 42),(.neg 16),(.pos 36),(.pos 58)]),
   ((.exchange 42 17 4),[(.neg 42),(.neg 17),(.pos 37),(.pos 58)]),
   ((.exchange 42 19 3),[(.neg 42),(.neg 19),(.pos 39),(.pos 61)]),
   ((.exchange 42 20 3),[(.neg 42),(.neg 20),(.pos 40),(.pos 61)]),
   ((.exchange 42 23 0),[(.neg 42),(.neg 23),(.pos 43),(.pos 64)]),
   ((.exchange 42 24 0),[(.neg 42),(.neg 24),(.pos 44),(.pos 64)]),
   ((.exchange 42 41 0),[(.neg 42),(.neg 41),(.pos 43),(.pos 44)]),
   ((.exchange 42 41 3),[(.neg 42),(.neg 41),(.pos 39),(.pos 40)]),
   ((.exchange 42 59 4),[(.neg 59),(.neg 42),(.pos 36),(.pos 58)]),
   ((.exchange 42 63 0),[(.neg 63),(.neg 42),(.pos 44),(.pos 64)]),
   ((.exchange 43 1 3),[(.neg 43),(.neg 1),(.pos 39),(.pos 41)]),
   ((.exchange 43 3 1),[(.neg 43),(.neg 3),(.pos 42),(.pos 44)]),
   ((.exchange 43 8 4),[(.neg 43),(.neg 8),(.pos 38),(.pos 49)]),
   ((.exchange 43 11 3),[(.neg 43),(.neg 11),(.pos 41),(.pos 52)]),
   ((.exchange 43 14 1),[(.neg 43),(.neg 14),(.pos 44),(.pos 54)]),
   ((.exchange 43 16 4),[(.neg 43),(.neg 16),(.pos 36),(.pos 59)]),
   ((.exchange 43 21 3),[(.neg 43),(.neg 21),(.pos 41),(.pos 62)]),
   ((.exchange 43 22 1),[(.neg 43),(.neg 22),(.pos 42),(.pos 64)]),
   ((.exchange 43 24 1),[(.neg 43),(.neg 24),(.pos 44),(.pos 64)]),
   ((.exchange 43 33 3),[(.neg 43),(.neg 33),(.pos 41),(.pos 52),(.pos 62)]),
   ((.exchange 43 34 1),[(.neg 43),(.neg 34),(.pos 54),(.pos 64)]),
   ((.exchange 43 37 4),[(.neg 43),(.neg 37),(.pos 36),(.pos 38)]),
   ((.exchange 43 45 4),[(.neg 45),(.neg 43),(.pos 36),(.pos 49)]),
   ((.exchange 43 48 4),[(.neg 48),(.neg 43),(.pos 36),(.pos 49)]),
   ((.exchange 43 50 1),[(.neg 50),(.neg 43),(.pos 44),(.pos 54)]),
   ((.exchange 43 53 3),[(.neg 53),(.neg 43),(.pos 41),(.pos 52)]),
   ((.exchange 43 57 4),[(.neg 57),(.neg 43),(.pos 38),(.pos 59)]),
   ((.exchange 43 60 1),[(.neg 60),(.neg 43),(.pos 44),(.pos 64)]),
   ((.exchange 43 60 4),[(.neg 60),(.neg 43),(.pos 38),(.pos 59)]),
   ((.exchange 43 61 1),[(.neg 61),(.neg 43),(.pos 42),(.pos 64)]),
   ((.exchange 43 63 1),[(.neg 63),(.neg 43),(.pos 44),(.pos 64)]),
   ((.exchange 43 63 3),[(.neg 63),(.neg 43),(.pos 41),(.pos 62)]),
   ((.exchange 43 66 3),[(.neg 66),(.neg 43),(.pos 52),(.pos 62)]),
   ((.exchange 44 0 4),[(.neg 44),(.neg 0),(.pos 37),(.pos 38)]),
   ((.exchange 44 1 3),[(.neg 44),(.neg 1),(.pos 40),(.pos 41)]),
   ((.exchange 44 2 2),[(.neg 44),(.neg 2),(.pos 42),(.pos 43)]),
   ((.exchange 44 9 2),[(.neg 44),(.neg 9),(.pos 42),(.pos 43),(.pos 54)]),
   ((.exchange 44 13 2),[(.neg 44),(.neg 13),(.pos 43),(.pos 54)]),
   ((.exchange 44 17 4),[(.neg 44),(.neg 17),(.pos 37),(.pos 60)]),
   ((.exchange 44 20 3),[(.neg 44),(.neg 20),(.pos 40),(.pos 63)]),
   ((.exchange 44 21 3),[(.neg 44),(.neg 21),(.pos 41),(.pos 63)]),
   ((.exchange 44 22 2),[(.neg 44),(.neg 22),(.pos 42),(.pos 64)]),
   ((.exchange 44 23 2),[(.neg 44),(.neg 23),(.pos 43),(.pos 64)]),
   ((.exchange 44 31 2),[(.neg 44),(.neg 31),(.pos 42),(.pos 54),(.pos 64)]),
   ((.exchange 44 32 3),[(.neg 44),(.neg 32),(.pos 41),(.pos 53),(.pos 63)]),
   ((.exchange 44 33 3),[(.neg 44),(.neg 33),(.pos 53),(.pos 63)]),
   ((.exchange 44 34 2),[(.neg 44),(.neg 34),(.pos 54),(.pos 64)]),
   ((.exchange 44 45 2),[(.neg 45),(.neg 44),(.pos 42),(.pos 43),(.pos 54)]),
   ((.exchange 44 46 4),[(.neg 46),(.neg 44),(.pos 37),(.pos 50)]),
   ((.exchange 44 48 4),[(.neg 48),(.neg 44),(.pos 37),(.pos 50)]),
   ((.exchange 44 51 3),[(.neg 51),(.neg 44),(.pos 40),(.pos 53)]),
   ((.exchange 44 52 2),[(.neg 52),(.neg 44),(.pos 43),(.pos 54)]),
   ((.exchange 44 52 3),[(.neg 52),(.neg 44),(.pos 41),(.pos 53)]),
   ((.exchange 44 57 3),[(.neg 57),(.neg 44),(.pos 41),(.pos 63)]),
   ((.exchange 44 57 4),[(.neg 57),(.neg 44),(.pos 38),(.pos 60)]),
   ((.exchange 44 59 2),[(.neg 59),(.neg 44),(.pos 43),(.pos 64)]),
   ((.exchange 44 61 2),[(.neg 61),(.neg 44),(.pos 42),(.pos 64)])]

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



noncomputable def certificates_2 : List (Origin 70 2165 × List Sat.Literal) :=
  [((.exchange 44 62 2),[(.neg 62),(.neg 44),(.pos 43),(.pos 64)]),
   ((.exchange 44 67 3),[(.neg 67),(.neg 44),(.pos 53),(.pos 63)]),
   ((.exchange 44 67 4),[(.neg 67),(.neg 44),(.pos 50),(.pos 60)]),
   ((.exchange 44 68 2),[(.neg 68),(.neg 44),(.pos 54),(.pos 64)]),
   ((.exchange 44 69 2),[(.neg 69),(.neg 44),(.pos 54),(.pos 64)]),
   ((.exchange 45 0 5),[(.neg 45),(.neg 0),(.pos 35),(.pos 36)]),
   ((.exchange 45 1 5),[(.neg 45),(.neg 1),(.pos 35),(.pos 39)]),
   ((.exchange 45 3 1),[(.neg 45),(.neg 3),(.pos 46),(.pos 48),(.pos 51)]),
   ((.exchange 45 8 0),[(.neg 45),(.neg 8),(.pos 47),(.pos 49)]),
   ((.exchange 45 11 0),[(.neg 45),(.neg 11),(.pos 47),(.pos 52)]),
   ((.exchange 45 13 0),[(.neg 45),(.neg 13),(.pos 49),(.pos 52)]),
   ((.exchange 45 16 5),[(.neg 45),(.neg 16),(.pos 36),(.pos 55)]),
   ((.exchange 45 21 5),[(.neg 45),(.neg 21),(.pos 35),(.pos 39),(.pos 55)]),
   ((.exchange 45 27 0),[(.neg 45),(.neg 27),(.pos 47),(.pos 66)]),
   ((.exchange 45 32 0),[(.neg 45),(.neg 32),(.pos 52),(.pos 66)]),
   ((.exchange 45 37 1),[(.neg 45),(.neg 37),(.pos 46),(.pos 48)]),
   ((.exchange 45 38 0),[(.neg 45),(.neg 38),(.pos 47),(.pos 49)]),
   ((.exchange 45 40 5),[(.neg 45),(.neg 40),(.pos 35),(.pos 39)]),
   ((.exchange 45 41 0),[(.neg 45),(.neg 41),(.pos 47),(.pos 52)]),
   ((.exchange 45 44 1),[(.neg 45),(.neg 44),(.pos 46),(.pos 48),(.pos 51)]),
   ((.exchange 45 50 0),[(.neg 50),(.neg 45),(.pos 47),(.pos 49)]),
   ((.exchange 45 53 0),[(.neg 53),(.neg 45),(.pos 47),(.pos 52)]),
   ((.exchange 45 57 0),[(.neg 57),(.neg 45),(.pos 47),(.pos 66)]),
   ((.exchange 45 59 0),[(.neg 59),(.neg 45),(.pos 49),(.pos 66)]),
   ((.exchange 45 60 5),[(.neg 60),(.neg 45),(.pos 35),(.pos 36),(.pos 55)]),
   ((.exchange 45 63 5),[(.neg 63),(.neg 45),(.pos 35),(.pos 39),(.pos 55)]),
   ((.exchange 45 69 0),[(.neg 69),(.neg 45),(.pos 52),(.pos 66)]),
   ((.exchange 46 2 2),[(.neg 46),(.neg 2),(.pos 45),(.pos 48),(.pos 51)]),
   ((.exchange 46 6 2),[(.neg 46),(.neg 6),(.pos 45),(.pos 48)]),
   ((.exchange 46 8 0),[(.neg 46),(.neg 8),(.pos 47),(.pos 50)]),
   ((.exchange 46 9 2),[(.neg 46),(.neg 9),(.pos 45),(.pos 51)]),
   ((.exchange 46 11 0),[(.neg 46),(.neg 11),(.pos 47),(.pos 53)]),
   ((.exchange 46 13 2),[(.neg 46),(.neg 13),(.pos 45),(.pos 48),(.pos 51)]),
   ((.exchange 46 17 5),[(.neg 46),(.neg 17),(.pos 37),(.pos 56)]),
   ((.exchange 46 20 5),[(.neg 46),(.neg 20),(.pos 40),(.pos 56)]),
   ((.exchange 46 22 2),[(.neg 46),(.neg 22),(.pos 48),(.pos 51),(.pos 65)]),
   ((.exchange 46 25 2),[(.neg 46),(.neg 25),(.pos 45),(.pos 65)]),
   ((.exchange 46 27 0),[(.neg 46),(.neg 27),(.pos 47),(.pos 67)]),
   ((.exchange 46 28 2),[(.neg 46),(.neg 28),(.pos 48),(.pos 65)]),
   ((.exchange 46 30 0),[(.neg 46),(.neg 30),(.pos 50),(.pos 67)]),
   ((.exchange 46 34 2),[(.neg 46),(.neg 34),(.pos 48),(.pos 51),(.pos 65)]),
   ((.exchange 46 36 2),[(.neg 46),(.neg 36),(.pos 45),(.pos 48)]),
   ((.exchange 46 38 0),[(.neg 46),(.neg 38),(.pos 47),(.pos 50)]),
   ((.exchange 46 38 5),[(.neg 46),(.neg 38),(.pos 35),(.pos 37)]),
   ((.exchange 46 41 0),[(.neg 46),(.neg 41),(.pos 47),(.pos 53)]),
   ((.exchange 46 41 5),[(.neg 46),(.neg 41),(.pos 35),(.pos 40)]),
   ((.exchange 46 42 5),[(.neg 46),(.neg 42),(.pos 37),(.pos 40)]),
   ((.exchange 46 44 5),[(.neg 46),(.neg 44),(.pos 37),(.pos 40)]),
   ((.exchange 46 54 0),[(.neg 54),(.neg 46),(.pos 50),(.pos 53)]),
   ((.exchange 46 55 2),[(.neg 55),(.neg 46),(.pos 45),(.pos 65)]),
   ((.exchange 47 0 5),[(.neg 47),(.neg 0),(.pos 35),(.pos 38)]),
   ((.exchange 47 1 5),[(.neg 47),(.neg 1),(.pos 35),(.pos 41)]),
   ((.exchange 47 4 5),[(.neg 47),(.neg 4),(.pos 38),(.pos 41)]),
   ((.exchange 47 6 2),[(.neg 47),(.neg 6),(.pos 45),(.pos 49)]),
   ((.exchange 47 7 1),[(.neg 47),(.neg 7),(.pos 46),(.pos 50)]),
   ((.exchange 47 9 2),[(.neg 47),(.neg 9),(.pos 45),(.pos 52)]),
   ((.exchange 47 10 1),[(.neg 47),(.neg 10),(.pos 46),(.pos 53)]),
   ((.exchange 47 14 1),[(.neg 47),(.neg 14),(.pos 50),(.pos 53)]),
   ((.exchange 47 22 5),[(.neg 47),(.neg 22),(.pos 35),(.pos 38),(.pos 41),(.pos 57)]),
   ((.exchange 47 25 2),[(.neg 47),(.neg 25),(.pos 45),(.pos 66)]),
   ((.exchange 47 26 1),[(.neg 47),(.neg 26),(.pos 46),(.pos 67)]),
   ((.exchange 47 29 2),[(.neg 47),(.neg 29),(.pos 49),(.pos 66)]),
   ((.exchange 47 32 2),[(.neg 47),(.neg 32),(.pos 52),(.pos 66)]),
   ((.exchange 47 33 1),[(.neg 47),(.neg 33),(.pos 53),(.pos 67)]),
   ((.exchange 47 37 1),[(.neg 47),(.neg 37),(.pos 46),(.pos 50)]),
   ((.exchange 47 40 5),[(.neg 47),(.neg 40),(.pos 35),(.pos 41)]),
   ((.exchange 47 48 1),[(.neg 48),(.neg 47),(.pos 46),(.pos 50)]),
   ((.exchange 47 48 2),[(.neg 48),(.neg 47),(.pos 45),(.pos 49)]),
   ((.exchange 47 51 1),[(.neg 51),(.neg 47),(.pos 46),(.pos 53)]),
   ((.exchange 47 51 2),[(.neg 51),(.neg 47),(.pos 45),(.pos 52)]),
   ((.exchange 47 54 1),[(.neg 54),(.neg 47),(.pos 50),(.pos 53)]),
   ((.exchange 47 54 2),[(.neg 54),(.neg 47),(.pos 49),(.pos 52)]),
   ((.exchange 47 56 1),[(.neg 56),(.neg 47),(.pos 46),(.pos 67)]),
   ((.exchange 47 60 1),[(.neg 60),(.neg 47),(.pos 50),(.pos 67)]),
   ((.exchange 47 65 2),[(.neg 65),(.neg 47),(.pos 45),(.pos 66)]),
   ((.exchange 47 68 1),[(.neg 68),(.neg 47),(.pos 50),(.pos 67)]),
   ((.exchange 47 68 2),[(.neg 68),(.neg 47),(.pos 49),(.pos 66)]),
   ((.exchange 48 0 5),[(.neg 48),(.neg 0),(.pos 36),(.pos 37)]),
   ((.exchange 48 5 3),[(.neg 48),(.neg 5),(.pos 45),(.pos 46)]),
   ((.exchange 48 8 0),[(.neg 48),(.neg 8),(.pos 49),(.pos 50)]),
   ((.exchange 48 16 5),[(.neg 48),(.neg 16),(.pos 36),(.pos 58)]),
   ((.exchange 48 17 5),[(.neg 48),(.neg 17),(.pos 37),(.pos 58)]),
   ((.exchange 48 26 3),[(.neg 48),(.neg 26),(.pos 46),(.pos 65)]),
   ((.exchange 48 29 0),[(.neg 48),(.neg 29),(.pos 49),(.pos 68)]),
   ((.exchange 48 30 0),[(.neg 48),(.neg 30),(.pos 50),(.pos 68)]),
   ((.exchange 48 35 5),[(.neg 48),(.neg 35),(.pos 36),(.pos 37)]),
   ((.exchange 48 55 5),[(.neg 55),(.neg 48),(.pos 36),(.pos 58)]),
   ((.exchange 48 56 5),[(.neg 56),(.neg 48),(.pos 37),(.pos 58)]),
   ((.exchange 48 60 0),[(.neg 60),(.neg 48),(.pos 50),(.pos 68)]),
   ((.exchange 48 60 5),[(.neg 60),(.neg 48),(.pos 37),(.pos 58)]),
   ((.exchange 48 67 0),[(.neg 67),(.neg 48),(.pos 50),(.pos 68)]),
   ((.exchange 48 67 3),[(.neg 67),(.neg 48),(.pos 46),(.pos 65)]),
   ((.exchange 49 0 5),[(.neg 49),(.neg 0),(.pos 36),(.pos 38)]),
   ((.exchange 49 1 3),[(.neg 49),(.neg 1),(.pos 45),(.pos 47),(.pos 52)]),
   ((.exchange 49 2 5),[(.neg 49),(.neg 2),(.pos 36),(.pos 43)]),
   ((.exchange 49 3 1),[(.neg 49),(.neg 3),(.pos 48),(.pos 50),(.pos 54)]),
   ((.exchange 49 4 5),[(.neg 49),(.neg 4),(.pos 38),(.pos 43)]),
   ((.exchange 49 5 3),[(.neg 49),(.neg 5),(.pos 45),(.pos 47)]),
   ((.exchange 49 9 3),[(.neg 49),(.neg 9),(.pos 45),(.pos 52)]),
   ((.exchange 49 16 5),[(.neg 49),(.neg 16),(.pos 36),(.pos 59)]),
   ((.exchange 49 18 5),[(.neg 49),(.neg 18),(.pos 38),(.pos 59)]),
   ((.exchange 49 22 1),[(.neg 49),(.neg 22),(.pos 48),(.pos 54),(.pos 68)]),
   ((.exchange 49 23 5),[(.neg 49),(.neg 23),(.pos 43),(.pos 59)]),
   ((.exchange 49 25 3),[(.neg 49),(.neg 25),(.pos 45),(.pos 66)]),
   ((.exchange 49 31 1),[(.neg 49),(.neg 31),(.pos 48),(.pos 54),(.pos 68)]),
   ((.exchange 49 32 3),[(.neg 49),(.neg 32),(.pos 52),(.pos 66)]),
   ((.exchange 49 35 5),[(.neg 49),(.neg 35),(.pos 36),(.pos 38)]),
   ((.exchange 49 46 3),[(.neg 49),(.neg 46),(.pos 45),(.pos 47)]),
   ((.exchange 49 51 3),[(.neg 51),(.neg 49),(.pos 45),(.pos 52)]),
   ((.exchange 49 53 1),[(.neg 53),(.neg 49),(.pos 50),(.pos 54)]),
   ((.exchange 49 53 3),[(.neg 53),(.neg 49),(.pos 47),(.pos 52)]),
   ((.exchange 49 55 3),[(.neg 55),(.neg 49),(.pos 45),(.pos 66)]),
   ((.exchange 49 57 5),[(.neg 57),(.neg 49),(.pos 38),(.pos 59)]),
   ((.exchange 49 62 5),[(.neg 62),(.neg 49),(.pos 43),(.pos 59)]),
   ((.exchange 49 65 1),[(.neg 65),(.neg 49),(.pos 48),(.pos 68)]),
   ((.exchange 49 67 3),[(.neg 67),(.neg 49),(.pos 47),(.pos 66)]),
   ((.exchange 49 69 3),[(.neg 69),(.neg 49),(.pos 52),(.pos 66)]),
   ((.exchange 50 0 5),[(.neg 50),(.neg 0),(.pos 37),(.pos 38)]),
   ((.exchange 50 2 2),[(.neg 50),(.neg 2),(.pos 48),(.pos 49),(.pos 54)]),
   ((.exchange 50 3 5),[(.neg 50),(.neg 3),(.pos 37),(.pos 44)]),
   ((.exchange 50 13 2),[(.neg 50),(.neg 13),(.pos 49),(.pos 54)]),
   ((.exchange 50 17 5),[(.neg 50),(.neg 17),(.pos 37),(.pos 60)]),
   ((.exchange 50 18 5),[(.neg 50),(.neg 18),(.pos 38),(.pos 60)]),
   ((.exchange 50 22 2),[(.neg 50),(.neg 22),(.pos 48),(.pos 54),(.pos 68)]),
   ((.exchange 50 24 5),[(.neg 50),(.neg 24),(.pos 44),(.pos 60)]),
   ((.exchange 50 28 2),[(.neg 50),(.neg 28),(.pos 48),(.pos 68)]),
   ((.exchange 50 29 2),[(.neg 50),(.neg 29),(.pos 49),(.pos 68)]),
   ((.exchange 50 31 2),[(.neg 50),(.neg 31),(.pos 48),(.pos 54),(.pos 68)])]

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



noncomputable def certificates_3 : List (Origin 70 2165 × List Sat.Literal) :=
  [((.exchange 50 33 3),[(.neg 50),(.neg 33),(.pos 53),(.pos 67)]),
   ((.exchange 50 34 2),[(.neg 50),(.neg 34),(.pos 54),(.pos 68)]),
   ((.exchange 50 35 3),[(.neg 50),(.neg 35),(.pos 46),(.pos 47)]),
   ((.exchange 50 56 5),[(.neg 56),(.neg 50),(.pos 37),(.pos 60)]),
   ((.exchange 50 57 5),[(.neg 57),(.neg 50),(.pos 38),(.pos 60)]),
   ((.exchange 50 58 2),[(.neg 58),(.neg 50),(.pos 48),(.pos 68)]),
   ((.exchange 50 58 5),[(.neg 58),(.neg 50),(.pos 37),(.pos 60)]),
   ((.exchange 50 63 5),[(.neg 63),(.neg 50),(.pos 44),(.pos 60)]),
   ((.exchange 50 65 2),[(.neg 65),(.neg 50),(.pos 48),(.pos 68)]),
   ((.exchange 50 65 3),[(.neg 65),(.neg 50),(.pos 46),(.pos 67)]),
   ((.exchange 51 1 5),[(.neg 51),(.neg 1),(.pos 39),(.pos 40)]),
   ((.exchange 51 5 4),[(.neg 51),(.neg 5),(.pos 45),(.pos 46)]),
   ((.exchange 51 11 0),[(.neg 51),(.neg 11),(.pos 52),(.pos 53)]),
   ((.exchange 51 20 5),[(.neg 51),(.neg 20),(.pos 40),(.pos 61)]),
   ((.exchange 51 26 4),[(.neg 51),(.neg 26),(.pos 46),(.pos 65)]),
   ((.exchange 51 32 0),[(.neg 51),(.neg 32),(.pos 52),(.pos 69)]),
   ((.exchange 51 33 0),[(.neg 51),(.neg 33),(.pos 53),(.pos 69)]),
   ((.exchange 51 35 5),[(.neg 51),(.neg 35),(.pos 39),(.pos 40)]),
   ((.exchange 51 47 0),[(.neg 51),(.neg 47),(.pos 52),(.pos 53)]),
   ((.exchange 51 56 4),[(.neg 56),(.neg 51),(.pos 46),(.pos 65)]),
   ((.exchange 51 56 5),[(.neg 56),(.neg 51),(.pos 40),(.pos 61)]),
   ((.exchange 51 63 0),[(.neg 63),(.neg 51),(.pos 53),(.pos 69)]),
   ((.exchange 51 63 5),[(.neg 63),(.neg 51),(.pos 40),(.pos 61)]),
   ((.exchange 51 66 4),[(.neg 66),(.neg 51),(.pos 45),(.pos 65)]),
   ((.exchange 51 67 0),[(.neg 67),(.neg 51),(.pos 53),(.pos 69)]),
   ((.exchange 51 67 4),[(.neg 67),(.neg 51),(.pos 46),(.pos 65)]),
   ((.exchange 52 0 5),[(.neg 52),(.neg 0),(.pos 39),(.pos 41),(.pos 43)]),
   ((.exchange 52 1 5),[(.neg 52),(.neg 1),(.pos 39),(.pos 41)]),
   ((.exchange 52 2 5),[(.neg 52),(.neg 2),(.pos 39),(.pos 43)]),
   ((.exchange 52 4 5),[(.neg 52),(.neg 4),(.pos 41),(.pos 43)]),
   ((.exchange 52 21 5),[(.neg 52),(.neg 21),(.pos 41),(.pos 62)]),
   ((.exchange 52 22 1),[(.neg 52),(.neg 22),(.pos 51),(.pos 54),(.pos 69)]),
   ((.exchange 52 24 5),[(.neg 52),(.neg 24),(.pos 41),(.pos 43),(.pos 62)]),
   ((.exchange 52 25 4),[(.neg 52),(.neg 25),(.pos 45),(.pos 66)]),
   ((.exchange 52 26 4),[(.neg 52),(.neg 26),(.pos 45),(.pos 47),(.pos 66)]),
   ((.exchange 52 37 1),[(.neg 52),(.neg 37),(.pos 51),(.pos 53),(.pos 54)]),
   ((.exchange 52 38 4),[(.neg 52),(.neg 38),(.pos 47),(.pos 49)]),
   ((.exchange 52 38 5),[(.neg 52),(.neg 38),(.pos 41),(.pos 43)]),
   ((.exchange 52 40 1),[(.neg 52),(.neg 40),(.pos 51),(.pos 53)]),
   ((.exchange 52 40 5),[(.neg 52),(.neg 40),(.pos 39),(.pos 41)]),
   ((.exchange 52 46 1),[(.neg 52),(.neg 46),(.pos 51),(.pos 53)]),
   ((.exchange 52 46 4),[(.neg 52),(.neg 46),(.pos 45),(.pos 47)]),
   ((.exchange 52 50 1),[(.neg 52),(.neg 50),(.pos 53),(.pos 54)]),
   ((.exchange 52 55 4),[(.neg 55),(.neg 52),(.pos 45),(.pos 66)]),
   ((.exchange 52 57 5),[(.neg 57),(.neg 52),(.pos 41),(.pos 62)]),
   ((.exchange 52 59 4),[(.neg 59),(.neg 52),(.pos 49),(.pos 66)]),
   ((.exchange 52 63 5),[(.neg 63),(.neg 52),(.pos 41),(.pos 62)]),
   ((.exchange 52 67 4),[(.neg 67),(.neg 52),(.pos 47),(.pos 66)]),
   ((.exchange 52 68 1),[(.neg 68),(.neg 52),(.pos 54),(.pos 69)]),
   ((.exchange 52 68 4),[(.neg 68),(.neg 52),(.pos 49),(.pos 66)]),
   ((.exchange 53 0 5),[(.neg 53),(.neg 0),(.pos 40),(.pos 41),(.pos 44)]),
   ((.exchange 53 1 5),[(.neg 53),(.neg 1),(.pos 40),(.pos 41)]),
   ((.exchange 53 2 2),[(.neg 53),(.neg 2),(.pos 51),(.pos 52),(.pos 54)]),
   ((.exchange 53 4 5),[(.neg 53),(.neg 4),(.pos 41),(.pos 44)]),
   ((.exchange 53 9 2),[(.neg 53),(.neg 9),(.pos 51),(.pos 52)]),
   ((.exchange 53 13 2),[(.neg 53),(.neg 13),(.pos 52),(.pos 54)]),
   ((.exchange 53 20 5),[(.neg 53),(.neg 20),(.pos 40),(.pos 63)]),
   ((.exchange 53 21 5),[(.neg 53),(.neg 21),(.pos 41),(.pos 63)]),
   ((.exchange 53 22 2),[(.neg 53),(.neg 22),(.pos 51),(.pos 54),(.pos 69)]),
   ((.exchange 53 30 4),[(.neg 53),(.neg 30),(.pos 50),(.pos 67)]),
   ((.exchange 53 31 2),[(.neg 53),(.neg 31),(.pos 51),(.pos 69)]),
   ((.exchange 53 34 2),[(.neg 53),(.neg 34),(.pos 54),(.pos 69)]),
   ((.exchange 53 35 4),[(.neg 53),(.neg 35),(.pos 46),(.pos 47)]),
   ((.exchange 53 37 5),[(.neg 53),(.neg 37),(.pos 40),(.pos 44)]),
   ((.exchange 53 42 5),[(.neg 53),(.neg 42),(.pos 40),(.pos 44)]),
   ((.exchange 53 43 2),[(.neg 53),(.neg 43),(.pos 52),(.pos 54)]),
   ((.exchange 53 45 2),[(.neg 53),(.neg 45),(.pos 51),(.pos 52)]),
   ((.exchange 53 57 5),[(.neg 57),(.neg 53),(.pos 41),(.pos 63)]),
   ((.exchange 53 58 2),[(.neg 58),(.neg 53),(.pos 51),(.pos 54),(.pos 69)]),
   ((.exchange 53 60 4),[(.neg 60),(.neg 53),(.pos 50),(.pos 67)]),
   ((.exchange 53 60 5),[(.neg 60),(.neg 53),(.pos 44),(.pos 63)]),
   ((.exchange 53 64 2),[(.neg 64),(.neg 53),(.pos 54),(.pos 69)]),
   ((.exchange 53 65 4),[(.neg 65),(.neg 53),(.pos 46),(.pos 67)]),
   ((.exchange 53 68 2),[(.neg 68),(.neg 53),(.pos 54),(.pos 69)]),
   ((.exchange 54 8 4),[(.neg 54),(.neg 8),(.pos 49),(.pos 50)]),
   ((.exchange 54 11 3),[(.neg 54),(.neg 11),(.pos 52),(.pos 53)]),
   ((.exchange 54 24 5),[(.neg 54),(.neg 24),(.pos 44),(.pos 64)]),
   ((.exchange 54 29 4),[(.neg 54),(.neg 29),(.pos 49),(.pos 68)]),
   ((.exchange 54 30 4),[(.neg 54),(.neg 30),(.pos 50),(.pos 68)]),
   ((.exchange 54 32 3),[(.neg 54),(.neg 32),(.pos 52),(.pos 69)]),
   ((.exchange 54 33 3),[(.neg 54),(.neg 33),(.pos 53),(.pos 69)]),
   ((.exchange 54 38 5),[(.neg 54),(.neg 38),(.pos 43),(.pos 44)]),
   ((.exchange 54 41 5),[(.neg 54),(.neg 41),(.pos 43),(.pos 44)]),
   ((.exchange 54 47 4),[(.neg 54),(.neg 47),(.pos 49),(.pos 50)]),
   ((.exchange 54 60 4),[(.neg 60),(.neg 54),(.pos 50),(.pos 68)]),
   ((.exchange 54 60 5),[(.neg 60),(.neg 54),(.pos 44),(.pos 64)]),
   ((.exchange 54 62 3),[(.neg 62),(.neg 54),(.pos 52),(.pos 69)]),
   ((.exchange 54 66 4),[(.neg 66),(.neg 54),(.pos 49),(.pos 68)]),
   ((.exchange 55 6 6),[(.neg 55),(.neg 6),(.pos 36),(.pos 45)]),
   ((.exchange 55 9 6),[(.neg 55),(.neg 9),(.pos 39),(.pos 45)]),
   ((.exchange 55 22 1),[(.neg 55),(.neg 22),(.pos 58),(.pos 61)]),
   ((.exchange 55 23 0),[(.neg 55),(.neg 23),(.pos 59),(.pos 62)]),
   ((.exchange 55 28 1),[(.neg 55),(.neg 28),(.pos 58),(.pos 65)]),
   ((.exchange 55 29 0),[(.neg 55),(.neg 29),(.pos 59),(.pos 66)]),
   ((.exchange 55 31 1),[(.neg 55),(.neg 31),(.pos 61),(.pos 65)]),
   ((.exchange 55 32 0),[(.neg 55),(.neg 32),(.pos 62),(.pos 66)]),
   ((.exchange 55 49 6),[(.neg 55),(.neg 49),(.pos 36),(.pos 45)]),
   ((.exchange 55 52 6),[(.neg 55),(.neg 52),(.pos 39),(.pos 45)]),
   ((.exchange 55 68 0),[(.neg 68),(.neg 55),(.pos 59),(.pos 66)]),
   ((.exchange 56 10 6),[(.neg 56),(.neg 10),(.pos 40),(.pos 46)]),
   ((.exchange 56 24 0),[(.neg 56),(.neg 24),(.pos 60),(.pos 63)]),
   ((.exchange 56 30 0),[(.neg 56),(.neg 30),(.pos 60),(.pos 67)]),
   ((.exchange 56 33 0),[(.neg 56),(.neg 33),(.pos 63),(.pos 67)]),
   ((.exchange 56 42 6),[(.neg 56),(.neg 42),(.pos 37),(.pos 40)]),
   ((.exchange 56 48 6),[(.neg 56),(.neg 48),(.pos 37),(.pos 46)]),
   ((.exchange 56 51 6),[(.neg 56),(.neg 51),(.pos 40),(.pos 46)]),
   ((.exchange 57 4 6),[(.neg 57),(.neg 4),(.pos 38),(.pos 41)]),
   ((.exchange 57 8 6),[(.neg 57),(.neg 8),(.pos 38),(.pos 47)]),
   ((.exchange 57 11 6),[(.neg 57),(.neg 11),(.pos 41),(.pos 47)]),
   ((.exchange 57 53 1),[(.neg 57),(.neg 53),(.pos 63),(.pos 67)]),
   ((.exchange 58 3 6),[(.neg 58),(.neg 3),(.pos 37),(.pos 42)]),
   ((.exchange 58 5 3),[(.neg 58),(.neg 5),(.pos 55),(.pos 56),(.pos 65)]),
   ((.exchange 58 7 6),[(.neg 58),(.neg 7),(.pos 37),(.pos 48)]),
   ((.exchange 58 9 6),[(.neg 58),(.neg 9),(.pos 36),(.pos 42),(.pos 48)]),
   ((.exchange 58 10 6),[(.neg 58),(.neg 10),(.pos 37),(.pos 42),(.pos 48)]),
   ((.exchange 58 18 0),[(.neg 58),(.neg 18),(.pos 59),(.pos 60)]),
   ((.exchange 58 23 0),[(.neg 58),(.neg 23),(.pos 59),(.pos 64)]),
   ((.exchange 58 24 0),[(.neg 58),(.neg 24),(.pos 60),(.pos 64)]),
   ((.exchange 58 29 0),[(.neg 58),(.neg 29),(.pos 59),(.pos 68)]),
   ((.exchange 58 30 0),[(.neg 58),(.neg 30),(.pos 60),(.pos 68)]),
   ((.exchange 58 31 3),[(.neg 58),(.neg 31),(.pos 61),(.pos 65)]),
   ((.exchange 58 34 0),[(.neg 58),(.neg 34),(.pos 64),(.pos 68)]),
   ((.exchange 58 38 0),[(.neg 58),(.neg 38),(.pos 59),(.pos 60)]),
   ((.exchange 58 41 3),[(.neg 58),(.neg 41),(.pos 55),(.pos 56),(.pos 61)]),
   ((.exchange 58 43 0),[(.neg 58),(.neg 43),(.pos 59),(.pos 64)]),
   ((.exchange 58 44 0),[(.neg 58),(.neg 44),(.pos 60),(.pos 64)]),
   ((.exchange 58 44 6),[(.neg 58),(.neg 44),(.pos 37),(.pos 42)]),
   ((.exchange 58 49 0),[(.neg 58),(.neg 49),(.pos 59),(.pos 68)])]

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



noncomputable def certificates_4 : List (Origin 70 2165 × List Sat.Literal) :=
  [((.exchange 58 50 0),[(.neg 58),(.neg 50),(.pos 60),(.pos 68)]),
   ((.exchange 58 54 0),[(.neg 58),(.neg 54),(.pos 64),(.pos 68)]),
   ((.exchange 58 57 0),[(.neg 58),(.neg 57),(.pos 59),(.pos 60)]),
   ((.exchange 58 62 0),[(.neg 62),(.neg 58),(.pos 59),(.pos 64)]),
   ((.exchange 58 63 3),[(.neg 63),(.neg 58),(.pos 56),(.pos 61)]),
   ((.exchange 58 66 0),[(.neg 66),(.neg 58),(.pos 59),(.pos 68)]),
   ((.exchange 58 66 3),[(.neg 66),(.neg 58),(.pos 55),(.pos 65)]),
   ((.exchange 58 67 3),[(.neg 67),(.neg 58),(.pos 56),(.pos 65)]),
   ((.exchange 58 69 3),[(.neg 69),(.neg 58),(.pos 61),(.pos 65)]),
   ((.exchange 59 0 6),[(.neg 59),(.neg 0),(.pos 36),(.pos 38)]),
   ((.exchange 59 2 6),[(.neg 59),(.neg 2),(.pos 36),(.pos 43)]),
   ((.exchange 59 5 3),[(.neg 59),(.neg 5),(.pos 55),(.pos 57),(.pos 66)]),
   ((.exchange 59 8 6),[(.neg 59),(.neg 8),(.pos 38),(.pos 49)]),
   ((.exchange 59 22 1),[(.neg 59),(.neg 22),(.pos 58),(.pos 64)]),
   ((.exchange 59 26 3),[(.neg 59),(.neg 26),(.pos 55),(.pos 57),(.pos 66)]),
   ((.exchange 59 28 1),[(.neg 59),(.neg 28),(.pos 58),(.pos 68)]),
   ((.exchange 59 30 1),[(.neg 59),(.neg 30),(.pos 60),(.pos 68)]),
   ((.exchange 59 32 3),[(.neg 59),(.neg 32),(.pos 62),(.pos 66)]),
   ((.exchange 59 34 1),[(.neg 59),(.neg 34),(.pos 64),(.pos 68)]),
   ((.exchange 59 37 1),[(.neg 59),(.neg 37),(.pos 58),(.pos 60)]),
   ((.exchange 59 37 6),[(.neg 59),(.neg 37),(.pos 36),(.pos 38)]),
   ((.exchange 59 41 3),[(.neg 59),(.neg 41),(.pos 57),(.pos 62)]),
   ((.exchange 59 41 6),[(.neg 59),(.neg 41),(.pos 38),(.pos 43)]),
   ((.exchange 59 44 6),[(.neg 59),(.neg 44),(.pos 38),(.pos 43)]),
   ((.exchange 59 45 6),[(.neg 59),(.neg 45),(.pos 36),(.pos 49)]),
   ((.exchange 59 47 6),[(.neg 59),(.neg 47),(.pos 38),(.pos 49)]),
   ((.exchange 59 48 1),[(.neg 59),(.neg 48),(.pos 58),(.pos 68)]),
   ((.exchange 59 48 6),[(.neg 59),(.neg 48),(.pos 36),(.pos 49)]),
   ((.exchange 59 50 1),[(.neg 59),(.neg 50),(.pos 60),(.pos 68)]),
   ((.exchange 59 53 6),[(.neg 59),(.neg 53),(.pos 38),(.pos 43),(.pos 49)]),
   ((.exchange 59 54 6),[(.neg 59),(.neg 54),(.pos 43),(.pos 49)]),
   ((.exchange 59 56 1),[(.neg 59),(.neg 56),(.pos 58),(.pos 60)]),
   ((.exchange 59 61 1),[(.neg 61),(.neg 59),(.pos 58),(.pos 64)]),
   ((.exchange 59 65 1),[(.neg 65),(.neg 59),(.pos 58),(.pos 68)]),
   ((.exchange 59 67 1),[(.neg 67),(.neg 59),(.pos 60),(.pos 68)]),
   ((.exchange 59 69 1),[(.neg 69),(.neg 59),(.pos 64),(.pos 68)]),
   ((.exchange 60 0 6),[(.neg 60),(.neg 0),(.pos 37),(.pos 38)]),
   ((.exchange 60 16 2),[(.neg 60),(.neg 16),(.pos 58),(.pos 59)]),
   ((.exchange 60 22 2),[(.neg 60),(.neg 22),(.pos 58),(.pos 64)]),
   ((.exchange 60 23 2),[(.neg 60),(.neg 23),(.pos 59),(.pos 64)]),
   ((.exchange 60 26 3),[(.neg 60),(.neg 26),(.pos 56),(.pos 67)]),
   ((.exchange 60 28 2),[(.neg 60),(.neg 28),(.pos 58),(.pos 68)]),
   ((.exchange 60 29 2),[(.neg 60),(.neg 29),(.pos 59),(.pos 68)]),
   ((.exchange 60 34 2),[(.neg 60),(.neg 34),(.pos 64),(.pos 68)]),
   ((.exchange 60 35 6),[(.neg 60),(.neg 35),(.pos 37),(.pos 38)]),
   ((.exchange 60 39 2),[(.neg 60),(.neg 39),(.pos 58),(.pos 59),(.pos 64)]),
   ((.exchange 60 40 3),[(.neg 60),(.neg 40),(.pos 56),(.pos 63)]),
   ((.exchange 60 40 6),[(.neg 60),(.neg 40),(.pos 37),(.pos 44)]),
   ((.exchange 60 41 3),[(.neg 60),(.neg 41),(.pos 57),(.pos 63)]),
   ((.exchange 60 41 6),[(.neg 60),(.neg 41),(.pos 38),(.pos 44)]),
   ((.exchange 60 42 2),[(.neg 60),(.neg 42),(.pos 58),(.pos 64)]),
   ((.exchange 60 42 6),[(.neg 60),(.neg 42),(.pos 37),(.pos 44)]),
   ((.exchange 60 47 3),[(.neg 60),(.neg 47),(.pos 57),(.pos 67)]),
   ((.exchange 60 47 6),[(.neg 60),(.neg 47),(.pos 38),(.pos 50)]),
   ((.exchange 60 48 2),[(.neg 60),(.neg 48),(.pos 58),(.pos 68)]),
   ((.exchange 60 48 6),[(.neg 60),(.neg 48),(.pos 37),(.pos 50)]),
   ((.exchange 60 49 2),[(.neg 60),(.neg 49),(.pos 59),(.pos 68)]),
   ((.exchange 60 54 2),[(.neg 60),(.neg 54),(.pos 64),(.pos 68)]),
   ((.exchange 60 54 6),[(.neg 60),(.neg 54),(.pos 44),(.pos 50)]),
   ((.exchange 60 55 2),[(.neg 60),(.neg 55),(.pos 58),(.pos 59)]),
   ((.exchange 60 61 2),[(.neg 61),(.neg 60),(.pos 58),(.pos 64)]),
   ((.exchange 60 62 2),[(.neg 62),(.neg 60),(.pos 59),(.pos 64)]),
   ((.exchange 60 65 2),[(.neg 65),(.neg 60),(.pos 58),(.pos 68)]),
   ((.exchange 60 66 3),[(.neg 66),(.neg 60),(.pos 57),(.pos 67)]),
   ((.exchange 60 69 2),[(.neg 69),(.neg 60),(.pos 64),(.pos 68)]),
   ((.exchange 61 0 4),[(.neg 61),(.neg 0),(.pos 55),(.pos 56),(.pos 58)]),
   ((.exchange 61 2 6),[(.neg 61),(.neg 2),(.pos 39),(.pos 42)]),
   ((.exchange 61 3 6),[(.neg 61),(.neg 3),(.pos 40),(.pos 42)]),
   ((.exchange 61 4 6),[(.neg 61),(.neg 4),(.pos 39),(.pos 40),(.pos 42)]),
   ((.exchange 61 13 6),[(.neg 61),(.neg 13),(.pos 39),(.pos 42),(.pos 51)]),
   ((.exchange 61 21 0),[(.neg 61),(.neg 21),(.pos 62),(.pos 63)]),
   ((.exchange 61 28 4),[(.neg 61),(.neg 28),(.pos 58),(.pos 65)]),
   ((.exchange 61 30 0),[(.neg 61),(.neg 30),(.pos 63),(.pos 64),(.pos 69)]),
   ((.exchange 61 32 0),[(.neg 61),(.neg 32),(.pos 62),(.pos 69)]),
   ((.exchange 61 33 0),[(.neg 61),(.neg 33),(.pos 63),(.pos 69)]),
   ((.exchange 61 34 0),[(.neg 61),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 61 37 4),[(.neg 61),(.neg 37),(.pos 56),(.pos 58)]),
   ((.exchange 61 41 0),[(.neg 61),(.neg 41),(.pos 62),(.pos 63)]),
   ((.exchange 61 41 6),[(.neg 61),(.neg 41),(.pos 39),(.pos 40)]),
   ((.exchange 61 43 0),[(.neg 61),(.neg 43),(.pos 62),(.pos 64)]),
   ((.exchange 61 44 0),[(.neg 61),(.neg 44),(.pos 63),(.pos 64)]),
   ((.exchange 61 45 4),[(.neg 61),(.neg 45),(.pos 55),(.pos 65)]),
   ((.exchange 61 46 4),[(.neg 61),(.neg 46),(.pos 56),(.pos 65)]),
   ((.exchange 61 46 6),[(.neg 61),(.neg 46),(.pos 40),(.pos 51)]),
   ((.exchange 61 50 6),[(.neg 61),(.neg 50),(.pos 40),(.pos 42),(.pos 51)]),
   ((.exchange 61 53 0),[(.neg 61),(.neg 53),(.pos 63),(.pos 69)]),
   ((.exchange 61 54 0),[(.neg 61),(.neg 54),(.pos 64),(.pos 69)]),
   ((.exchange 61 57 0),[(.neg 61),(.neg 57),(.pos 62),(.pos 63)]),
   ((.exchange 61 60 0),[(.neg 61),(.neg 60),(.pos 63),(.pos 64)]),
   ((.exchange 61 66 0),[(.neg 66),(.neg 61),(.pos 62),(.pos 69)]),
   ((.exchange 61 67 4),[(.neg 67),(.neg 61),(.pos 56),(.pos 65)]),
   ((.exchange 62 0 6),[(.neg 62),(.neg 0),(.pos 39),(.pos 41),(.pos 43)]),
   ((.exchange 62 1 6),[(.neg 62),(.neg 1),(.pos 39),(.pos 41)]),
   ((.exchange 62 2 6),[(.neg 62),(.neg 2),(.pos 39),(.pos 43)]),
   ((.exchange 62 4 6),[(.neg 62),(.neg 4),(.pos 41),(.pos 43)]),
   ((.exchange 62 5 4),[(.neg 62),(.neg 5),(.pos 55),(.pos 57),(.pos 66)]),
   ((.exchange 62 9 6),[(.neg 62),(.neg 9),(.pos 39),(.pos 52)]),
   ((.exchange 62 11 6),[(.neg 62),(.neg 11),(.pos 41),(.pos 52)]),
   ((.exchange 62 20 1),[(.neg 62),(.neg 20),(.pos 61),(.pos 63)]),
   ((.exchange 62 22 1),[(.neg 62),(.neg 22),(.pos 61),(.pos 64)]),
   ((.exchange 62 31 1),[(.neg 62),(.neg 31),(.pos 61),(.pos 69)]),
   ((.exchange 62 33 1),[(.neg 62),(.neg 33),(.pos 63),(.pos 69)]),
   ((.exchange 62 34 1),[(.neg 62),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 62 36 4),[(.neg 62),(.neg 36),(.pos 55),(.pos 59)]),
   ((.exchange 62 38 4),[(.neg 62),(.neg 38),(.pos 57),(.pos 59)]),
   ((.exchange 62 40 1),[(.neg 62),(.neg 40),(.pos 61),(.pos 63)]),
   ((.exchange 62 40 6),[(.neg 62),(.neg 40),(.pos 39),(.pos 41)]),
   ((.exchange 62 44 1),[(.neg 62),(.neg 44),(.pos 63),(.pos 64)]),
   ((.exchange 62 44 6),[(.neg 62),(.neg 44),(.pos 41),(.pos 43)]),
   ((.exchange 62 47 6),[(.neg 62),(.neg 47),(.pos 41),(.pos 52)]),
   ((.exchange 62 51 6),[(.neg 62),(.neg 51),(.pos 39),(.pos 52)]),
   ((.exchange 62 53 6),[(.neg 62),(.neg 53),(.pos 41),(.pos 52)]),
   ((.exchange 62 54 1),[(.neg 62),(.neg 54),(.pos 64),(.pos 69)]),
   ((.exchange 62 54 6),[(.neg 62),(.neg 54),(.pos 43),(.pos 52)]),
   ((.exchange 62 56 1),[(.neg 62),(.neg 56),(.pos 61),(.pos 63)]),
   ((.exchange 62 60 1),[(.neg 62),(.neg 60),(.pos 63),(.pos 64)]),
   ((.exchange 62 65 1),[(.neg 65),(.neg 62),(.pos 61),(.pos 69)]),
   ((.exchange 62 65 4),[(.neg 65),(.neg 62),(.pos 55),(.pos 66)]),
   ((.exchange 62 67 1),[(.neg 67),(.neg 62),(.pos 63),(.pos 69)]),
   ((.exchange 63 0 6),[(.neg 63),(.neg 0),(.pos 40),(.pos 41),(.pos 44)]),
   ((.exchange 63 1 6),[(.neg 63),(.neg 1),(.pos 40),(.pos 41)]),
   ((.exchange 63 3 6),[(.neg 63),(.neg 3),(.pos 40),(.pos 44)]),
   ((.exchange 63 4 6),[(.neg 63),(.neg 4),(.pos 41),(.pos 44)]),
   ((.exchange 63 11 6),[(.neg 63),(.neg 11),(.pos 41),(.pos 53)]),
   ((.exchange 63 14 6),[(.neg 63),(.neg 14),(.pos 44),(.pos 53)]),
   ((.exchange 63 18 4),[(.neg 63),(.neg 18),(.pos 57),(.pos 60)]),
   ((.exchange 63 19 2),[(.neg 63),(.neg 19),(.pos 61),(.pos 62)]),
   ((.exchange 63 22 2),[(.neg 63),(.neg 22),(.pos 61),(.pos 64)])]

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



noncomputable def certificates_5 : List (Origin 70 2165 × List Sat.Literal) :=
  [((.exchange 63 23 2),[(.neg 63),(.neg 23),(.pos 62),(.pos 64)]),
   ((.exchange 63 26 4),[(.neg 63),(.neg 26),(.pos 56),(.pos 67)]),
   ((.exchange 63 27 4),[(.neg 63),(.neg 27),(.pos 57),(.pos 67)]),
   ((.exchange 63 30 4),[(.neg 63),(.neg 30),(.pos 60),(.pos 67)]),
   ((.exchange 63 31 2),[(.neg 63),(.neg 31),(.pos 61),(.pos 69)]),
   ((.exchange 63 32 2),[(.neg 63),(.neg 32),(.pos 62),(.pos 69)]),
   ((.exchange 63 34 2),[(.neg 63),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 63 35 6),[(.neg 63),(.neg 35),(.pos 40),(.pos 41)]),
   ((.exchange 63 36 4),[(.neg 63),(.neg 36),(.pos 56),(.pos 57),(.pos 60)]),
   ((.exchange 63 38 6),[(.neg 63),(.neg 38),(.pos 41),(.pos 44)]),
   ((.exchange 63 42 2),[(.neg 63),(.neg 42),(.pos 61),(.pos 64)]),
   ((.exchange 63 42 6),[(.neg 63),(.neg 42),(.pos 40),(.pos 44)]),
   ((.exchange 63 43 2),[(.neg 63),(.neg 43),(.pos 62),(.pos 64)]),
   ((.exchange 63 45 4),[(.neg 63),(.neg 45),(.pos 56),(.pos 57),(.pos 67)]),
   ((.exchange 63 47 6),[(.neg 63),(.neg 47),(.pos 41),(.pos 53)]),
   ((.exchange 63 50 6),[(.neg 63),(.neg 50),(.pos 44),(.pos 53)]),
   ((.exchange 63 51 6),[(.neg 63),(.neg 51),(.pos 40),(.pos 53)]),
   ((.exchange 63 54 6),[(.neg 63),(.neg 54),(.pos 44),(.pos 53)]),
   ((.exchange 63 55 2),[(.neg 63),(.neg 55),(.pos 61),(.pos 62)]),
   ((.exchange 63 58 2),[(.neg 63),(.neg 58),(.pos 61),(.pos 64)]),
   ((.exchange 63 59 2),[(.neg 63),(.neg 59),(.pos 62),(.pos 64)]),
   ((.exchange 63 65 2),[(.neg 65),(.neg 63),(.pos 61),(.pos 69)]),
   ((.exchange 63 68 2),[(.neg 68),(.neg 63),(.pos 64),(.pos 69)]),
   ((.exchange 64 1 3),[(.neg 64),(.neg 1),(.pos 61),(.pos 62),(.pos 63)]),
   ((.exchange 64 3 6),[(.neg 64),(.neg 3),(.pos 42),(.pos 44)]),
   ((.exchange 64 4 6),[(.neg 64),(.neg 4),(.pos 43),(.pos 44)]),
   ((.exchange 64 13 6),[(.neg 64),(.neg 13),(.pos 43),(.pos 54)]),
   ((.exchange 64 16 4),[(.neg 64),(.neg 16),(.pos 58),(.pos 59)]),
   ((.exchange 64 18 4),[(.neg 64),(.neg 18),(.pos 59),(.pos 60)]),
   ((.exchange 64 19 3),[(.neg 64),(.neg 19),(.pos 61),(.pos 62)]),
   ((.exchange 64 20 3),[(.neg 64),(.neg 20),(.pos 61),(.pos 63)]),
   ((.exchange 64 21 3),[(.neg 64),(.neg 21),(.pos 62),(.pos 63)]),
   ((.exchange 64 30 4),[(.neg 64),(.neg 30),(.pos 60),(.pos 68)]),
   ((.exchange 64 31 3),[(.neg 64),(.neg 31),(.pos 61),(.pos 69)]),
   ((.exchange 64 32 3),[(.neg 64),(.neg 32),(.pos 62),(.pos 69)]),
   ((.exchange 64 33 3),[(.neg 64),(.neg 33),(.pos 63),(.pos 69)]),
   ((.exchange 64 37 4),[(.neg 64),(.neg 37),(.pos 58),(.pos 60)]),
   ((.exchange 64 37 6),[(.neg 64),(.neg 37),(.pos 42),(.pos 44)]),
   ((.exchange 64 39 3),[(.neg 64),(.neg 39),(.pos 61),(.pos 62)]),
   ((.exchange 64 40 3),[(.neg 64),(.neg 40),(.pos 61),(.pos 63)]),
   ((.exchange 64 40 6),[(.neg 64),(.neg 40),(.pos 42),(.pos 44)]),
   ((.exchange 64 41 3),[(.neg 64),(.neg 41),(.pos 62),(.pos 63)]),
   ((.exchange 64 41 6),[(.neg 64),(.neg 41),(.pos 43),(.pos 44)]),
   ((.exchange 64 49 4),[(.neg 64),(.neg 49),(.pos 59),(.pos 68)]),
   ((.exchange 64 51 3),[(.neg 64),(.neg 51),(.pos 61),(.pos 69)]),
   ((.exchange 64 52 3),[(.neg 64),(.neg 52),(.pos 62),(.pos 69)]),
   ((.exchange 64 53 3),[(.neg 64),(.neg 53),(.pos 63),(.pos 69)]),
   ((.exchange 64 53 6),[(.neg 64),(.neg 53),(.pos 44),(.pos 54)]),
   ((.exchange 64 55 4),[(.neg 64),(.neg 55),(.pos 58),(.pos 59)]),
   ((.exchange 64 56 3),[(.neg 64),(.neg 56),(.pos 61),(.pos 63)]),
   ((.exchange 64 56 4),[(.neg 64),(.neg 56),(.pos 58),(.pos 60)]),
   ((.exchange 64 57 3),[(.neg 64),(.neg 57),(.pos 62),(.pos 63)]),
   ((.exchange 64 57 4),[(.neg 64),(.neg 57),(.pos 59),(.pos 60)]),
   ((.exchange 64 65 3),[(.neg 65),(.neg 64),(.pos 61),(.pos 69)]),
   ((.exchange 64 66 3),[(.neg 66),(.neg 64),(.pos 62),(.pos 69)]),
   ((.exchange 64 66 4),[(.neg 66),(.neg 64),(.pos 59),(.pos 68)]),
   ((.exchange 64 67 3),[(.neg 67),(.neg 64),(.pos 63),(.pos 69)]),
   ((.exchange 64 67 4),[(.neg 67),(.neg 64),(.pos 60),(.pos 68)]),
   ((.exchange 65 0 5),[(.neg 65),(.neg 0),(.pos 55),(.pos 56),(.pos 58)]),
   ((.exchange 65 1 5),[(.neg 65),(.neg 1),(.pos 55),(.pos 56),(.pos 61)]),
   ((.exchange 65 2 5),[(.neg 65),(.neg 2),(.pos 55),(.pos 58),(.pos 61)]),
   ((.exchange 65 13 6),[(.neg 65),(.neg 13),(.pos 45),(.pos 48),(.pos 51)]),
   ((.exchange 65 14 6),[(.neg 65),(.neg 14),(.pos 46),(.pos 48),(.pos 51)]),
   ((.exchange 65 16 5),[(.neg 65),(.neg 16),(.pos 55),(.pos 58)]),
   ((.exchange 65 17 5),[(.neg 65),(.neg 17),(.pos 56),(.pos 58)]),
   ((.exchange 65 20 5),[(.neg 65),(.neg 20),(.pos 56),(.pos 61)]),
   ((.exchange 65 29 0),[(.neg 65),(.neg 29),(.pos 66),(.pos 68)]),
   ((.exchange 65 30 0),[(.neg 65),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 65 32 0),[(.neg 65),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 65 33 0),[(.neg 65),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 65 34 0),[(.neg 65),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 65 37 6),[(.neg 65),(.neg 37),(.pos 46),(.pos 48)]),
   ((.exchange 65 44 6),[(.neg 65),(.neg 44),(.pos 46),(.pos 48),(.pos 51)]),
   ((.exchange 65 47 0),[(.neg 65),(.neg 47),(.pos 66),(.pos 67)]),
   ((.exchange 65 49 0),[(.neg 65),(.neg 49),(.pos 66),(.pos 68)]),
   ((.exchange 65 50 0),[(.neg 65),(.neg 50),(.pos 67),(.pos 68)]),
   ((.exchange 65 59 5),[(.neg 65),(.neg 59),(.pos 55),(.pos 58)]),
   ((.exchange 65 60 0),[(.neg 65),(.neg 60),(.pos 67),(.pos 68)]),
   ((.exchange 65 63 0),[(.neg 65),(.neg 63),(.pos 67),(.pos 69)]),
   ((.exchange 65 64 0),[(.neg 65),(.neg 64),(.pos 68),(.pos 69)]),
   ((.exchange 65 64 5),[(.neg 65),(.neg 64),(.pos 58),(.pos 61)]),
   ((.exchange 66 4 6),[(.neg 66),(.neg 4),(.pos 47),(.pos 49),(.pos 52)]),
   ((.exchange 66 5 6),[(.neg 66),(.neg 5),(.pos 45),(.pos 47)]),
   ((.exchange 66 6 6),[(.neg 66),(.neg 6),(.pos 45),(.pos 49)]),
   ((.exchange 66 9 6),[(.neg 66),(.neg 9),(.pos 45),(.pos 52)]),
   ((.exchange 66 11 6),[(.neg 66),(.neg 11),(.pos 47),(.pos 52)]),
   ((.exchange 66 13 6),[(.neg 66),(.neg 13),(.pos 49),(.pos 52)]),
   ((.exchange 66 18 5),[(.neg 66),(.neg 18),(.pos 57),(.pos 59)]),
   ((.exchange 66 21 5),[(.neg 66),(.neg 21),(.pos 57),(.pos 62)]),
   ((.exchange 66 24 5),[(.neg 66),(.neg 24),(.pos 57),(.pos 59),(.pos 62)]),
   ((.exchange 66 26 1),[(.neg 66),(.neg 26),(.pos 65),(.pos 67)]),
   ((.exchange 66 28 1),[(.neg 66),(.neg 28),(.pos 65),(.pos 68)]),
   ((.exchange 66 30 1),[(.neg 66),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 66 34 1),[(.neg 66),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 66 35 6),[(.neg 66),(.neg 35),(.pos 45),(.pos 47)]),
   ((.exchange 66 36 5),[(.neg 66),(.neg 36),(.pos 55),(.pos 59)]),
   ((.exchange 66 38 6),[(.neg 66),(.neg 38),(.pos 47),(.pos 49)]),
   ((.exchange 66 46 1),[(.neg 66),(.neg 46),(.pos 65),(.pos 67)]),
   ((.exchange 66 46 6),[(.neg 66),(.neg 46),(.pos 45),(.pos 47)]),
   ((.exchange 66 48 1),[(.neg 66),(.neg 48),(.pos 65),(.pos 68)]),
   ((.exchange 66 50 1),[(.neg 66),(.neg 50),(.pos 67),(.pos 68)]),
   ((.exchange 66 51 1),[(.neg 66),(.neg 51),(.pos 65),(.pos 69)]),
   ((.exchange 66 53 1),[(.neg 66),(.neg 53),(.pos 67),(.pos 69)]),
   ((.exchange 66 53 6),[(.neg 66),(.neg 53),(.pos 47),(.pos 52)]),
   ((.exchange 66 60 1),[(.neg 66),(.neg 60),(.pos 67),(.pos 68)]),
   ((.exchange 67 1 6),[(.neg 67),(.neg 1),(.pos 46),(.pos 47),(.pos 53)]),
   ((.exchange 67 4 6),[(.neg 67),(.neg 4),(.pos 47),(.pos 50),(.pos 53)]),
   ((.exchange 67 5 6),[(.neg 67),(.neg 5),(.pos 46),(.pos 47)]),
   ((.exchange 67 7 6),[(.neg 67),(.neg 7),(.pos 46),(.pos 50)]),
   ((.exchange 67 14 6),[(.neg 67),(.neg 14),(.pos 50),(.pos 53)]),
   ((.exchange 67 21 5),[(.neg 67),(.neg 21),(.pos 57),(.pos 63)]),
   ((.exchange 67 24 5),[(.neg 67),(.neg 24),(.pos 60),(.pos 63)]),
   ((.exchange 67 28 2),[(.neg 67),(.neg 28),(.pos 65),(.pos 68)]),
   ((.exchange 67 29 2),[(.neg 67),(.neg 29),(.pos 66),(.pos 68)]),
   ((.exchange 67 31 2),[(.neg 67),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 67 32 2),[(.neg 67),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 67 34 2),[(.neg 67),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 67 37 5),[(.neg 67),(.neg 37),(.pos 56),(.pos 60)]),
   ((.exchange 67 38 5),[(.neg 67),(.neg 38),(.pos 57),(.pos 60)]),
   ((.exchange 67 40 5),[(.neg 67),(.neg 40),(.pos 56),(.pos 63)]),
   ((.exchange 67 41 5),[(.neg 67),(.neg 41),(.pos 57),(.pos 63)]),
   ((.exchange 67 41 6),[(.neg 67),(.neg 41),(.pos 47),(.pos 53)]),
   ((.exchange 67 43 2),[(.neg 67),(.neg 43),(.pos 66),(.pos 68),(.pos 69)]),
   ((.exchange 67 45 2),[(.neg 67),(.neg 45),(.pos 65),(.pos 66)]),
   ((.exchange 67 48 6),[(.neg 67),(.neg 48),(.pos 46),(.pos 50)]),
   ((.exchange 67 51 2),[(.neg 67),(.neg 51),(.pos 65),(.pos 69)]),
   ((.exchange 67 51 6),[(.neg 67),(.neg 51),(.pos 46),(.pos 53)]),
   ((.exchange 67 52 2),[(.neg 67),(.neg 52),(.pos 66),(.pos 69)])]

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



noncomputable def certificates_6 : List (Origin 70 2165 × List Sat.Literal) :=
  [((.exchange 67 54 2),[(.neg 67),(.neg 54),(.pos 68),(.pos 69)]),
   ((.exchange 67 55 2),[(.neg 67),(.neg 55),(.pos 65),(.pos 66)]),
   ((.exchange 67 58 2),[(.neg 67),(.neg 58),(.pos 65),(.pos 68)]),
   ((.exchange 67 59 2),[(.neg 67),(.neg 59),(.pos 66),(.pos 68)]),
   ((.exchange 67 62 5),[(.neg 67),(.neg 62),(.pos 57),(.pos 63)]),
   ((.exchange 67 64 2),[(.neg 67),(.neg 64),(.pos 68),(.pos 69)]),
   ((.exchange 68 4 6),[(.neg 68),(.neg 4),(.pos 49),(.pos 50),(.pos 54)]),
   ((.exchange 68 10 6),[(.neg 68),(.neg 10),(.pos 48),(.pos 50),(.pos 54)]),
   ((.exchange 68 17 5),[(.neg 68),(.neg 17),(.pos 58),(.pos 60)]),
   ((.exchange 68 23 5),[(.neg 68),(.neg 23),(.pos 59),(.pos 64)]),
   ((.exchange 68 24 5),[(.neg 68),(.neg 24),(.pos 60),(.pos 64)]),
   ((.exchange 68 26 3),[(.neg 68),(.neg 26),(.pos 65),(.pos 67)]),
   ((.exchange 68 27 3),[(.neg 68),(.neg 27),(.pos 66),(.pos 67)]),
   ((.exchange 68 31 3),[(.neg 68),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 68 32 3),[(.neg 68),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 68 33 3),[(.neg 68),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 68 36 5),[(.neg 68),(.neg 36),(.pos 58),(.pos 59)]),
   ((.exchange 68 36 6),[(.neg 68),(.neg 36),(.pos 48),(.pos 49)]),
   ((.exchange 68 37 5),[(.neg 68),(.neg 37),(.pos 58),(.pos 60)]),
   ((.exchange 68 37 6),[(.neg 68),(.neg 37),(.pos 48),(.pos 50)]),
   ((.exchange 68 40 6),[(.neg 68),(.neg 40),(.pos 48),(.pos 50),(.pos 54)]),
   ((.exchange 68 43 5),[(.neg 68),(.neg 43),(.pos 59),(.pos 64)]),
   ((.exchange 68 45 3),[(.neg 68),(.neg 45),(.pos 65),(.pos 66)]),
   ((.exchange 68 45 6),[(.neg 68),(.neg 45),(.pos 48),(.pos 49)]),
   ((.exchange 68 46 3),[(.neg 68),(.neg 46),(.pos 65),(.pos 67)]),
   ((.exchange 68 46 6),[(.neg 68),(.neg 46),(.pos 48),(.pos 50)]),
   ((.exchange 68 47 3),[(.neg 68),(.neg 47),(.pos 66),(.pos 67)]),
   ((.exchange 68 52 3),[(.neg 68),(.neg 52),(.pos 66),(.pos 69)]),
   ((.exchange 68 53 6),[(.neg 68),(.neg 53),(.pos 50),(.pos 54)]),
   ((.exchange 68 55 3),[(.neg 68),(.neg 55),(.pos 65),(.pos 66)]),
   ((.exchange 68 55 5),[(.neg 68),(.neg 55),(.pos 58),(.pos 59)]),
   ((.exchange 68 56 5),[(.neg 68),(.neg 56),(.pos 58),(.pos 60)]),
   ((.exchange 68 57 3),[(.neg 68),(.neg 57),(.pos 66),(.pos 67)]),
   ((.exchange 68 61 5),[(.neg 68),(.neg 61),(.pos 58),(.pos 64)]),
   ((.exchange 68 63 3),[(.neg 68),(.neg 63),(.pos 67),(.pos 69)]),
   ((.exchange 69 0 5),[(.neg 69),(.neg 0),(.pos 61),(.pos 62),(.pos 63),(.pos 64)]),
   ((.exchange 69 3 5),[(.neg 69),(.neg 3),(.pos 61),(.pos 63),(.pos 64)]),
   ((.exchange 69 11 6),[(.neg 69),(.neg 11),(.pos 52),(.pos 53)]),
   ((.exchange 69 13 6),[(.neg 69),(.neg 13),(.pos 52),(.pos 54)]),
   ((.exchange 69 19 5),[(.neg 69),(.neg 19),(.pos 61),(.pos 62)]),
   ((.exchange 69 21 5),[(.neg 69),(.neg 21),(.pos 62),(.pos 63)]),
   ((.exchange 69 22 5),[(.neg 69),(.neg 22),(.pos 61),(.pos 64)]),
   ((.exchange 69 23 5),[(.neg 69),(.neg 23),(.pos 62),(.pos 64)]),
   ((.exchange 69 24 5),[(.neg 69),(.neg 24),(.pos 63),(.pos 64)]),
   ((.exchange 69 25 4),[(.neg 69),(.neg 25),(.pos 65),(.pos 66)]),
   ((.exchange 69 27 4),[(.neg 69),(.neg 27),(.pos 66),(.pos 67)]),
   ((.exchange 69 29 4),[(.neg 69),(.neg 29),(.pos 66),(.pos 68)]),
   ((.exchange 69 30 4),[(.neg 69),(.neg 30),(.pos 67),(.pos 68)]),
   ((.exchange 69 37 6),[(.neg 69),(.neg 37),(.pos 51),(.pos 53),(.pos 54)]),
   ((.exchange 69 40 6),[(.neg 69),(.neg 40),(.pos 51),(.pos 53)]),
   ((.exchange 69 44 5),[(.neg 69),(.neg 44),(.pos 63),(.pos 64)]),
   ((.exchange 69 45 6),[(.neg 69),(.neg 45),(.pos 51),(.pos 52)]),
   ((.exchange 69 46 4),[(.neg 69),(.neg 46),(.pos 65),(.pos 67)]),
   ((.exchange 69 46 6),[(.neg 69),(.neg 46),(.pos 51),(.pos 53)]),
   ((.exchange 69 47 4),[(.neg 69),(.neg 47),(.pos 66),(.pos 67)]),
   ((.exchange 69 47 6),[(.neg 69),(.neg 47),(.pos 52),(.pos 53)]),
   ((.exchange 69 48 4),[(.neg 69),(.neg 48),(.pos 65),(.pos 68)]),
   ((.exchange 69 49 4),[(.neg 69),(.neg 49),(.pos 66),(.pos 68)]),
   ((.exchange 69 49 6),[(.neg 69),(.neg 49),(.pos 52),(.pos 54)]),
   ((.exchange 69 50 4),[(.neg 69),(.neg 50),(.pos 67),(.pos 68)]),
   ((.exchange 69 50 6),[(.neg 69),(.neg 50),(.pos 53),(.pos 54)]),
   ((.exchange 69 55 4),[(.neg 69),(.neg 55),(.pos 65),(.pos 66)]),
   ((.exchange 69 55 5),[(.neg 69),(.neg 55),(.pos 61),(.pos 62)]),
   ((.exchange 69 57 4),[(.neg 69),(.neg 57),(.pos 66),(.pos 67)]),
   ((.exchange 69 57 5),[(.neg 69),(.neg 57),(.pos 62),(.pos 63)]),
   ((.exchange 69 59 4),[(.neg 69),(.neg 59),(.pos 66),(.pos 68)]),
   (.newPoint,[(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 0),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 58),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 48),(.neg 46),(.neg 44),(.neg 42),(.neg 40),(.neg 37),(.pos 35),(.pos 36),(.pos 38),(.pos 39),(.pos 41),(.pos 43),(.pos 45),(.pos 47),(.pos 49),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 59),(.pos 62),(.pos 66)]),
   ((.excluded 1),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 54),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 45),(.neg 43),(.neg 42),(.neg 39),(.neg 36),(.pos 35),(.pos 37),(.pos 38),(.pos 40),(.pos 41),(.pos 44),(.pos 46),(.pos 47),(.pos 50),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 2),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 40),(.neg 39),(.neg 37),(.neg 36),(.pos 35),(.pos 38),(.pos 41),(.pos 47),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 61),(.pos 65)]),
   ((.excluded 3),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 40),(.neg 39),(.neg 37),(.neg 36),(.pos 35),(.pos 38),(.pos 41),(.pos 42),(.pos 47),(.pos 48),(.pos 51),(.pos 54),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 4),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 40),(.neg 39),(.neg 37),(.neg 36),(.pos 35),(.pos 38),(.pos 41),(.pos 47),(.pos 55),(.pos 56),(.pos 57),(.pos 64)]),
   ((.excluded 5),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 40),(.neg 39),(.neg 37),(.neg 36),(.pos 35),(.pos 38),(.pos 41),(.pos 47),(.pos 55),(.pos 56),(.pos 57),(.pos 68)]),
   ((.excluded 6),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 40),(.neg 39),(.neg 37),(.neg 36),(.pos 35),(.pos 38),(.pos 41),(.pos 47),(.pos 55),(.pos 56),(.pos 57),(.pos 69)]),
   ((.excluded 7),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 40),(.neg 39),(.neg 37),(.neg 36),(.pos 35),(.pos 38),(.pos 41),(.pos 47),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 8),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 44),(.neg 43),(.neg 41),(.neg 38),(.pos 35),(.pos 36),(.pos 37),(.pos 39),(.pos 40),(.pos 42),(.pos 45),(.pos 46),(.pos 48),(.pos 51),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 61),(.pos 65)]),
   ((.excluded 9),[(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 10),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 43),(.pos 50),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 61),(.pos 65)]),
   ((.excluded 11),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 43),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 61),(.pos 65)]),
   ((.excluded 12),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 43),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 61),(.pos 65)]),
   ((.excluded 13),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 54),(.neg 53),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 61),(.pos 65)]),
   ((.excluded 14),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 61),(.pos 65)]),
   ((.excluded 15),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 44),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 61),(.pos 65)]),
   ((.excluded 16),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 61),(.pos 65)]),
   ((.excluded 17),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 44),(.pos 49),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 61),(.pos 65)]),
   ((.excluded 18),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 44),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 61),(.pos 65)]),
   ((.excluded 19),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 49),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 61),(.pos 65)]),
   ((.excluded 20),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 49),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 61),(.pos 65)]),
   ((.excluded 21),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 61),(.pos 65)]),
   ((.excluded 22),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 61),(.pos 65)]),
   ((.excluded 23),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 43),(.pos 44),(.pos 48),(.pos 51),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 64)]),
   ((.excluded 24),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 58),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 48),(.pos 51),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 59),(.pos 62),(.pos 66)]),
   ((.excluded 25),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 48),(.pos 51),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 26),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 53),(.neg 52),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 68)]),
   ((.excluded 27),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 48),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 69)]),
   ((.excluded 28),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 53),(.neg 52),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 42),(.pos 48),(.pos 51),(.pos 54),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 29),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 36),(.pos 35),(.pos 37),(.pos 40),(.pos 46),(.pos 55),(.pos 56),(.pos 57),(.pos 59),(.pos 62),(.pos 66)]),
   ((.excluded 30),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 44),(.pos 55),(.pos 56),(.pos 57),(.pos 59),(.pos 62),(.pos 66)]),
   ((.excluded 31),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 50),(.pos 55),(.pos 56),(.pos 57),(.pos 59),(.pos 62),(.pos 66)]),
   ((.excluded 32),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 58),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 59),(.pos 62),(.pos 66)]),
   ((.excluded 33),[(.neg 69),(.neg 68),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 61),(.neg 60),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 55),(.pos 56),(.pos 57),(.pos 59),(.pos 62),(.pos 66)]),
   ((.excluded 34),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 35),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 43),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 36),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 49),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 37),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 38),[(.neg 69),(.neg 68),(.neg 66),(.neg 65),(.neg 64),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.pos 35),(.pos 55),(.pos 56),(.pos 57),(.pos 60),(.pos 63),(.pos 67)]),
   ((.excluded 39),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 68)]),
   ((.excluded 40),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 69)]),
   ((.excluded 41),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 44),(.pos 45),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 42),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 68)]),
   ((.excluded 43),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 68)]),
   ((.excluded 44),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 53),(.pos 55),(.pos 56),(.pos 57),(.pos 64)]),
   ((.excluded 45),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 53),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 46),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 50),(.pos 55),(.pos 56),(.pos 57),(.pos 64)]),
   ((.excluded 47),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 64)]),
   ((.excluded 48),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 50),(.pos 55),(.pos 56),(.pos 57),(.pos 69)]),
   ((.excluded 49),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 50),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 50),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 56),(.pos 57),(.pos 69)]),
   ((.excluded 51),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.pos 35),(.pos 36),(.pos 39),(.pos 45),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 52),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 36),(.pos 35),(.pos 37),(.pos 40),(.pos 43),(.pos 46),(.pos 55),(.pos 56),(.pos 57),(.pos 68)]),
   ((.excluded 53),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 36),(.pos 35),(.pos 37),(.pos 40),(.pos 43),(.pos 46),(.pos 55),(.pos 56),(.pos 57),(.pos 69)]),
   ((.excluded 54),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 36),(.pos 35),(.pos 37),(.pos 40),(.pos 43),(.pos 46),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 55),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 36),(.pos 35),(.pos 37),(.pos 40),(.pos 46),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 68)]),
   ((.excluded 56),[(.neg 69),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 36),(.pos 35),(.pos 37),(.pos 40),(.pos 46),(.pos 55),(.pos 56),(.pos 57),(.pos 68)]),
   ((.excluded 57),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 36),(.pos 35),(.pos 37),(.pos 40),(.pos 46),(.pos 52),(.pos 55),(.pos 56),(.pos 57),(.pos 64)]),
   ((.excluded 58),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 36),(.pos 35),(.pos 37),(.pos 40),(.pos 46),(.pos 52),(.pos 55),(.pos 56),(.pos 57)]),
   ((.excluded 59),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 36),(.pos 35),(.pos 37),(.pos 40),(.pos 46),(.pos 49),(.pos 55),(.pos 56),(.pos 57),(.pos 64)]),
   ((.excluded 60),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 36),(.pos 35),(.pos 37),(.pos 40),(.pos 46),(.pos 55),(.pos 56),(.pos 57),(.pos 64)])]

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



end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C82

end
end
end BundlePart4

