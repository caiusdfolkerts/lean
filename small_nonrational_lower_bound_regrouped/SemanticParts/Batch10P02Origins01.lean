module
public import SemanticParts.Batch10P02Data
public import Consolidated.SemanticData
public import Mathlib.Data.Fin.Tuple.Basic
public import MatroidCatalogue.Definitions
public import MatroidChecked.BitsetSemanticChecks
public import MatroidChecked.FastSemanticChecks
public import MatroidChecked.BitsetOrigins
public import MatroidChecked.MaskOrigins

section BundlePart2
/- Source: MatroidChecked/SemanticChunks/Cases18Part01.lean -/




@[expose] public section
noncomputable section

/- Source: MatroidCatalogue/Cases/N8R4C72Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C72


noncomputable def certificates_2 : List (Origin 70 177 × List Sat.Literal) :=
  [((.exchange 51 34 0),[(.neg 51),(.neg 34),(.pos 54),(.pos 69)]),
   ((.exchange 51 50 4),[(.neg 51),(.neg 50),(.pos 46),(.pos 48)]),
   ((.exchange 51 63 0),[(.neg 63),(.neg 51),(.pos 53),(.pos 69)]),
   ((.exchange 51 67 0),[(.neg 67),(.neg 51),(.pos 53),(.pos 69)]),
   ((.exchange 52 23 5),[(.neg 52),(.neg 23),(.pos 43),(.pos 62)]),
   ((.exchange 52 34 1),[(.neg 52),(.neg 34),(.pos 54),(.pos 69)]),
   ((.exchange 52 60 4),[(.neg 60),(.neg 52),(.pos 47),(.pos 49),(.pos 66)]),
   ((.exchange 52 67 1),[(.neg 67),(.neg 52),(.pos 53),(.pos 69)]),
   ((.exchange 53 1 5),[(.neg 53),(.neg 1),(.pos 40),(.pos 41)]),
   ((.exchange 53 5 4),[(.neg 53),(.neg 5),(.pos 46),(.pos 47)]),
   ((.exchange 53 55 2),[(.neg 55),(.neg 53),(.pos 51),(.pos 52),(.pos 69)]),
   ((.exchange 53 57 4),[(.neg 57),(.neg 53),(.pos 47),(.pos 67)]),
   ((.exchange 53 61 5),[(.neg 61),(.neg 53),(.pos 40),(.pos 63)]),
   ((.exchange 53 62 2),[(.neg 62),(.neg 53),(.pos 52),(.pos 69)]),
   ((.exchange 53 65 2),[(.neg 65),(.neg 53),(.pos 51),(.pos 69)]),
   ((.exchange 54 2 5),[(.neg 54),(.neg 2),(.pos 42),(.pos 43)]),
   ((.exchange 54 25 3),[(.neg 54),(.neg 25),(.pos 51),(.pos 52),(.pos 69)]),
   ((.exchange 54 58 4),[(.neg 58),(.neg 54),(.pos 48),(.pos 68)]),
   ((.exchange 54 65 3),[(.neg 65),(.neg 54),(.pos 51),(.pos 69)]),
   ((.exchange 54 65 4),[(.neg 65),(.neg 54),(.pos 48),(.pos 68)]),
   ((.exchange 54 66 3),[(.neg 66),(.neg 54),(.pos 52),(.pos 69)]),
   ((.exchange 55 1 6),[(.neg 55),(.neg 1),(.pos 35),(.pos 39)]),
   ((.exchange 55 3 1),[(.neg 55),(.neg 3),(.pos 56),(.pos 58),(.pos 61)]),
   ((.exchange 55 4 0),[(.neg 55),(.neg 4),(.pos 57),(.pos 59),(.pos 62)]),
   ((.exchange 55 5 6),[(.neg 55),(.neg 5),(.pos 35),(.pos 45)]),
   ((.exchange 55 6 6),[(.neg 55),(.neg 6),(.pos 36),(.pos 45)]),
   ((.exchange 55 7 1),[(.neg 55),(.neg 7),(.pos 56),(.pos 58),(.pos 65)]),
   ((.exchange 55 10 1),[(.neg 55),(.neg 10),(.pos 56),(.pos 61),(.pos 65)]),
   ((.exchange 55 23 0),[(.neg 55),(.neg 23),(.pos 59),(.pos 62)]),
   ((.exchange 55 40 6),[(.neg 55),(.neg 40),(.pos 35),(.pos 39)]),
   ((.exchange 55 46 6),[(.neg 55),(.neg 46),(.pos 35),(.pos 45)]),
   ((.exchange 55 47 6),[(.neg 55),(.neg 47),(.pos 35),(.pos 45)]),
   ((.exchange 55 53 1),[(.neg 55),(.neg 53),(.pos 56),(.pos 61),(.pos 65)]),
   ((.exchange 55 69 0),[(.neg 69),(.neg 55),(.pos 62),(.pos 66)]),
   ((.exchange 55 69 1),[(.neg 69),(.neg 55),(.pos 61),(.pos 65)]),
   ((.exchange 56 2 2),[(.neg 56),(.neg 2),(.pos 55),(.pos 58),(.pos 61)]),
   ((.exchange 56 4 0),[(.neg 56),(.neg 4),(.pos 57),(.pos 60),(.pos 63)]),
   ((.exchange 56 64 0),[(.neg 64),(.neg 56),(.pos 60),(.pos 63)]),
   ((.exchange 57 7 1),[(.neg 57),(.neg 7),(.pos 56),(.pos 60),(.pos 67)]),
   ((.exchange 57 16 2),[(.neg 57),(.neg 16),(.pos 55),(.pos 59)]),
   ((.exchange 57 25 2),[(.neg 57),(.neg 25),(.pos 55),(.pos 66)]),
   ((.exchange 57 28 2),[(.neg 57),(.neg 28),(.pos 55),(.pos 59),(.pos 66)]),
   ((.exchange 58 6 6),[(.neg 58),(.neg 6),(.pos 36),(.pos 48)]),
   ((.exchange 58 7 6),[(.neg 58),(.neg 7),(.pos 37),(.pos 48)]),
   ((.exchange 58 8 0),[(.neg 58),(.neg 8),(.pos 59),(.pos 60),(.pos 68)]),
   ((.exchange 58 15 3),[(.neg 58),(.neg 15),(.pos 55),(.pos 56)]),
   ((.exchange 58 25 3),[(.neg 58),(.neg 25),(.pos 55),(.pos 65)]),
   ((.exchange 58 30 0),[(.neg 58),(.neg 30),(.pos 60),(.pos 68)]),
   ((.exchange 58 46 6),[(.neg 58),(.neg 46),(.pos 37),(.pos 48)]),
   ((.exchange 58 49 6),[(.neg 58),(.neg 49),(.pos 36),(.pos 48)]),
   ((.exchange 58 57 0),[(.neg 58),(.neg 57),(.pos 59),(.pos 60)]),
   ((.exchange 58 57 3),[(.neg 58),(.neg 57),(.pos 55),(.pos 56)]),
   ((.exchange 58 66 3),[(.neg 66),(.neg 58),(.pos 55),(.pos 65)]),
   ((.exchange 59 1 3),[(.neg 59),(.neg 1),(.pos 55),(.pos 57),(.pos 62)]),
   ((.exchange 59 24 1),[(.neg 59),(.neg 24),(.pos 60),(.pos 64)]),
   ((.exchange 59 37 1),[(.neg 59),(.neg 37),(.pos 58),(.pos 60)]),
   ((.exchange 59 61 3),[(.neg 61),(.neg 59),(.pos 55),(.pos 62)]),
   ((.exchange 60 1 3),[(.neg 60),(.neg 1),(.pos 56),(.pos 57),(.pos 63)]),
   ((.exchange 60 8 6),[(.neg 60),(.neg 8),(.pos 38),(.pos 50)]),
   ((.exchange 60 12 6),[(.neg 60),(.neg 12),(.pos 37),(.pos 44),(.pos 50)]),
   ((.exchange 60 13 6),[(.neg 60),(.neg 13),(.pos 38),(.pos 44),(.pos 50)]),
   ((.exchange 60 47 6),[(.neg 60),(.neg 47),(.pos 38),(.pos 50)]),
   ((.exchange 60 48 2),[(.neg 60),(.neg 48),(.pos 58),(.pos 68)]),
   ((.exchange 60 48 6),[(.neg 60),(.neg 48),(.pos 37),(.pos 50)]),
   ((.exchange 60 62 2),[(.neg 62),(.neg 60),(.pos 59),(.pos 64)]),
   ((.exchange 60 69 2),[(.neg 69),(.neg 60),(.pos 64),(.pos 68)]),
   ((.exchange 61 1 6),[(.neg 61),(.neg 1),(.pos 39),(.pos 40)]),
   ((.exchange 61 10 6),[(.neg 61),(.neg 10),(.pos 40),(.pos 51)]),
   ((.exchange 61 11 6),[(.neg 61),(.neg 11),(.pos 39),(.pos 40),(.pos 51)]),
   ((.exchange 61 33 0),[(.neg 61),(.neg 33),(.pos 63),(.pos 69)]),
   ((.exchange 61 41 6),[(.neg 61),(.neg 41),(.pos 39),(.pos 40)]),
   ((.exchange 61 57 4),[(.neg 61),(.neg 57),(.pos 55),(.pos 56)]),
   ((.exchange 61 66 4),[(.neg 66),(.neg 61),(.pos 55),(.pos 65)]),
   ((.exchange 62 34 1),[(.neg 62),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 63 10 6),[(.neg 63),(.neg 10),(.pos 40),(.pos 53)]),
   ((.exchange 63 34 2),[(.neg 63),(.neg 34),(.pos 64),(.pos 69)]),
   ((.exchange 63 50 4),[(.neg 63),(.neg 50),(.pos 60),(.pos 67)]),
   ((.exchange 63 65 2),[(.neg 65),(.neg 63),(.pos 61),(.pos 69)]),
   ((.exchange 64 11 6),[(.neg 64),(.neg 11),(.pos 43),(.pos 44),(.pos 54)]),
   ((.exchange 64 13 6),[(.neg 64),(.neg 13),(.pos 43),(.pos 54)]),
   ((.exchange 64 57 4),[(.neg 64),(.neg 57),(.pos 59),(.pos 60)]),
   ((.exchange 65 6 6),[(.neg 65),(.neg 6),(.pos 45),(.pos 48)]),
   ((.exchange 65 12 6),[(.neg 65),(.neg 12),(.pos 48),(.pos 51)]),
   ((.exchange 65 16 5),[(.neg 65),(.neg 16),(.pos 55),(.pos 58)]),
   ((.exchange 65 19 5),[(.neg 65),(.neg 19),(.pos 55),(.pos 61)]),
   ((.exchange 65 32 0),[(.neg 65),(.neg 32),(.pos 66),(.pos 69)]),
   ((.exchange 65 34 0),[(.neg 65),(.neg 34),(.pos 68),(.pos 69)]),
   ((.exchange 65 62 0),[(.neg 65),(.neg 62),(.pos 66),(.pos 69)]),
   ((.exchange 66 10 1),[(.neg 66),(.neg 10),(.pos 65),(.pos 67),(.pos 69)]),
   ((.exchange 66 31 1),[(.neg 66),(.neg 31),(.pos 65),(.pos 69)]),
   ((.exchange 66 33 1),[(.neg 66),(.neg 33),(.pos 67),(.pos 69)]),
   ((.exchange 66 61 5),[(.neg 66),(.neg 61),(.pos 55),(.pos 62)]),
   ((.exchange 67 8 6),[(.neg 67),(.neg 8),(.pos 47),(.pos 50)]),
   ((.exchange 67 43 6),[(.neg 67),(.neg 43),(.pos 47),(.pos 50),(.pos 53)]),
   ((.exchange 67 62 2),[(.neg 67),(.neg 62),(.pos 66),(.pos 69)]),
   ((.exchange 67 64 2),[(.neg 67),(.neg 64),(.pos 68),(.pos 69)]),
   ((.exchange 68 1 3),[(.neg 68),(.neg 1),(.pos 65),(.pos 66),(.pos 67),(.pos 69)]),
   ((.exchange 68 7 6),[(.neg 68),(.neg 7),(.pos 48),(.pos 50)]),
   ((.exchange 68 10 6),[(.neg 68),(.neg 10),(.pos 48),(.pos 50),(.pos 54)]),
   ((.exchange 68 12 6),[(.neg 68),(.neg 12),(.pos 48),(.pos 54)]),
   ((.exchange 69 1 6),[(.neg 69),(.neg 1),(.pos 51),(.pos 52),(.pos 53)]),
   ((.exchange 69 4 6),[(.neg 69),(.neg 4),(.pos 52),(.pos 53),(.pos 54)]),
   ((.exchange 69 8 4),[(.neg 69),(.neg 8),(.pos 66),(.pos 67),(.pos 68)]),
   ((.exchange 69 10 6),[(.neg 69),(.neg 10),(.pos 51),(.pos 53)]),
   ((.exchange 69 12 6),[(.neg 69),(.neg 12),(.pos 51),(.pos 54)]),
   ((.exchange 69 13 6),[(.neg 69),(.neg 13),(.pos 52),(.pos 54)]),
   ((.exchange 69 20 5),[(.neg 69),(.neg 20),(.pos 61),(.pos 63)]),
   ((.exchange 69 46 6),[(.neg 69),(.neg 46),(.pos 51),(.pos 53)]),
   ((.exchange 69 48 6),[(.neg 69),(.neg 48),(.pos 51),(.pos 54)]),
   ((.exchange 69 49 6),[(.neg 69),(.neg 49),(.pos 52),(.pos 54)]),
   ((.exchange 69 55 4),[(.neg 69),(.neg 55),(.pos 65),(.pos 66)]),
   (.newPoint,[(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 0),[(.neg 69),(.neg 67),(.neg 65),(.neg 64),(.neg 61),(.neg 60),(.neg 58),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 48),(.neg 46),(.neg 44),(.neg 42),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 41),(.pos 43),(.pos 45),(.pos 47),(.pos 49),(.pos 51),(.pos 52),(.pos 55),(.pos 57),(.pos 59),(.pos 62),(.pos 63),(.pos 66),(.pos 68)]),
   ((.excluded 1),[(.neg 69),(.neg 68),(.neg 66),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 57),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 47),(.neg 44),(.neg 43),(.neg 41),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 40),(.pos 42),(.pos 45),(.pos 46),(.pos 48),(.pos 51),(.pos 52),(.pos 55),(.pos 56),(.pos 58),(.pos 61),(.pos 64),(.pos 65),(.pos 67)]),
   ((.excluded 2),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 55),(.pos 60),(.pos 69)]),
   ((.excluded 3),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 55)]),
   ((.excluded 4),[(.neg 69),(.neg 68),(.neg 66),(.neg 64),(.neg 61),(.neg 59),(.neg 58),(.neg 55),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 45),(.neg 43),(.neg 42),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 40),(.pos 41),(.pos 44),(.pos 46),(.pos 47),(.pos 50),(.pos 53),(.pos 54),(.pos 56),(.pos 57),(.pos 60),(.pos 62),(.pos 63),(.pos 65),(.pos 67)]),
   ((.excluded 5),[(.neg 69),(.neg 67),(.neg 65),(.neg 63),(.neg 62),(.neg 57),(.neg 56),(.neg 55),(.neg 52),(.neg 51),(.neg 47),(.neg 46),(.neg 45),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 42),(.pos 43),(.pos 44),(.pos 48),(.pos 49),(.pos 50),(.pos 53),(.pos 54),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 64),(.pos 66),(.pos 68)]),
   ((.excluded 6),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 44),(.pos 50),(.pos 53),(.pos 54),(.pos 60)]),
   ((.excluded 7),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 40),(.pos 43),(.pos 46),(.pos 49),(.pos 56),(.pos 59),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 8),[(.neg 69),(.neg 68),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 40),(.pos 46),(.pos 56),(.pos 65),(.pos 67)]),
   ((.excluded 9),[(.neg 69),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 43),(.pos 49),(.pos 59),(.pos 66),(.pos 68)]),
   ((.excluded 10),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 41),(.pos 42),(.pos 47),(.pos 48),(.pos 57),(.pos 58),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 11),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 41),(.pos 47),(.pos 57),(.pos 62),(.pos 63)]),
   ((.excluded 12),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 42),(.pos 48),(.pos 58),(.pos 61),(.pos 64)]),
   ((.excluded 13),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38),(.pos 69)]),
   ((.excluded 14),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.pos 35),(.pos 36),(.pos 37),(.pos 38)]),
   ((.excluded 15),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 56),(.neg 55),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 39),(.pos 40),(.pos 41),(.pos 42),(.pos 43),(.pos 44),(.pos 45),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 57),(.pos 58),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)])]

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



noncomputable def certificates_3 : List (Origin 70 177 × List Sat.Literal) :=
  [((.excluded 16),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 55),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 39),(.pos 44),(.pos 45),(.pos 46),(.pos 47),(.pos 48),(.pos 49),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 56),(.pos 59),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 17),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 39),(.pos 44),(.pos 45),(.pos 50),(.pos 51),(.pos 52),(.pos 53),(.pos 54),(.pos 69)]),
   ((.excluded 18),[(.neg 69),(.neg 67),(.neg 65),(.neg 63),(.neg 62),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 50),(.neg 48),(.neg 46),(.neg 44),(.neg 43),(.neg 41),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 39),(.pos 40),(.pos 42),(.pos 45),(.pos 47),(.pos 49),(.pos 51),(.pos 52),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 64),(.pos 66),(.pos 68)]),
   ((.excluded 19),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 41),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 39),(.pos 40),(.pos 42),(.pos 45),(.pos 51),(.pos 52),(.pos 58),(.pos 61),(.pos 64)]),
   ((.excluded 20),[(.neg 69),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 50),(.neg 48),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 39),(.pos 45),(.pos 47),(.pos 49),(.pos 51),(.pos 52),(.pos 59),(.pos 66),(.pos 68)]),
   ((.excluded 21),[(.neg 69),(.neg 68),(.neg 66),(.neg 64),(.neg 61),(.neg 59),(.neg 58),(.neg 55),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 47),(.neg 44),(.neg 42),(.neg 40),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 39),(.pos 41),(.pos 43),(.pos 45),(.pos 46),(.pos 48),(.pos 51),(.pos 52),(.pos 56),(.pos 57),(.pos 60),(.pos 62),(.pos 63),(.pos 65),(.pos 67)]),
   ((.excluded 22),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 42),(.neg 40),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 39),(.pos 41),(.pos 43),(.pos 45),(.pos 51),(.pos 52),(.pos 57),(.pos 62),(.pos 63)]),
   ((.excluded 23),[(.neg 69),(.neg 68),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 55),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 47),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 39),(.pos 45),(.pos 46),(.pos 48),(.pos 51),(.pos 52),(.pos 56),(.pos 65),(.pos 67)]),
   ((.excluded 24),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 39),(.pos 45),(.pos 51),(.pos 52),(.pos 60)]),
   ((.excluded 25),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 39),(.pos 45),(.pos 51),(.pos 52)]),
   ((.excluded 26),[(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 41),(.pos 42),(.pos 46),(.pos 49),(.pos 55),(.pos 56),(.pos 57),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 27),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 60),(.neg 59),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 41),(.pos 42),(.pos 57),(.pos 58),(.pos 61),(.pos 62),(.pos 63),(.pos 64),(.pos 69)]),
   ((.excluded 28),[(.neg 69),(.neg 68),(.neg 66),(.neg 64),(.neg 61),(.neg 59),(.neg 58),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 41),(.pos 46),(.pos 56),(.pos 57),(.pos 60),(.pos 62),(.pos 63),(.pos 65),(.pos 67)]),
   ((.excluded 29),[(.neg 69),(.neg 67),(.neg 65),(.neg 64),(.neg 61),(.neg 60),(.neg 58),(.neg 56),(.neg 52),(.neg 51),(.neg 47),(.neg 46),(.neg 45),(.neg 43),(.neg 42),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 41),(.pos 44),(.pos 48),(.pos 49),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 57),(.pos 59),(.pos 62),(.pos 63),(.pos 66),(.pos 68)]),
   ((.excluded 30),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 43),(.neg 42),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 41),(.pos 44),(.pos 50),(.pos 53),(.pos 54),(.pos 57),(.pos 62),(.pos 63)]),
   ((.excluded 31),[(.neg 69),(.neg 67),(.neg 65),(.neg 64),(.neg 61),(.neg 60),(.neg 58),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 41),(.pos 49),(.pos 55),(.pos 57),(.pos 59),(.pos 62),(.pos 63),(.pos 66),(.pos 68)]),
   ((.excluded 32),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 41),(.pos 48),(.pos 57),(.pos 62),(.pos 63)]),
   ((.excluded 33),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 41),(.pos 57),(.pos 62),(.pos 63)]),
   ((.excluded 34),[(.neg 69),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 52),(.neg 51),(.neg 47),(.neg 46),(.neg 45),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 44),(.pos 48),(.pos 49),(.pos 50),(.pos 53),(.pos 54),(.pos 59),(.pos 66),(.pos 68)]),
   ((.excluded 35),[(.neg 69),(.neg 67),(.neg 65),(.neg 63),(.neg 62),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 42),(.pos 49),(.pos 58),(.pos 59),(.pos 60),(.pos 61),(.pos 64),(.pos 66),(.pos 68)]),
   ((.excluded 36),[(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 46),(.pos 49),(.pos 56),(.pos 59),(.pos 65),(.pos 66),(.pos 67),(.pos 68),(.pos 69)]),
   ((.excluded 37),[(.neg 69),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 49),(.pos 59),(.pos 66),(.pos 68)]),
   ((.excluded 38),[(.neg 69),(.neg 67),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 49),(.pos 59),(.pos 66),(.pos 68)]),
   ((.excluded 39),[(.neg 69),(.neg 68),(.neg 66),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 57),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 45),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 42),(.pos 43),(.pos 44),(.pos 46),(.pos 47),(.pos 50),(.pos 53),(.pos 54),(.pos 55),(.pos 56),(.pos 58),(.pos 61),(.pos 64),(.pos 65),(.pos 67)]),
   ((.excluded 40),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 42),(.pos 43),(.pos 44),(.pos 50),(.pos 53),(.pos 54),(.pos 58),(.pos 61),(.pos 64)]),
   ((.excluded 41),[(.neg 69),(.neg 68),(.neg 66),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 57),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 42),(.pos 46),(.pos 55),(.pos 56),(.pos 58),(.pos 61),(.pos 64),(.pos 65),(.pos 67)]),
   ((.excluded 42),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 42),(.pos 47),(.pos 58),(.pos 61),(.pos 64)]),
   ((.excluded 43),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 63),(.neg 62),(.neg 60),(.neg 59),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 42),(.pos 58),(.pos 61),(.pos 64)]),
   ((.excluded 44),[(.neg 69),(.neg 68),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 55),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 45),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 44),(.pos 46),(.pos 47),(.pos 50),(.pos 53),(.pos 54),(.pos 56),(.pos 65),(.pos 67)]),
   ((.excluded 45),[(.neg 69),(.neg 68),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 46),(.pos 56),(.pos 65),(.pos 67)]),
   ((.excluded 46),[(.neg 69),(.neg 68),(.neg 66),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 46),(.pos 56),(.pos 65),(.pos 67)]),
   ((.excluded 47),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 44),(.pos 50),(.pos 53),(.pos 54),(.pos 55)]),
   ((.excluded 48),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 52),(.neg 51),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 43),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 44),(.pos 50),(.pos 53),(.pos 54)]),
   ((.excluded 49),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43),(.pos 47),(.pos 48),(.pos 55),(.pos 60),(.pos 69)]),
   ((.excluded 50),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43),(.pos 47),(.pos 48),(.pos 55),(.pos 60)]),
   ((.excluded 51),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43),(.pos 47),(.pos 48),(.pos 55),(.pos 69)]),
   ((.excluded 52),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43),(.pos 47),(.pos 48),(.pos 55)]),
   ((.excluded 53),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43),(.pos 47),(.pos 48),(.pos 60),(.pos 69)]),
   ((.excluded 54),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43),(.pos 47),(.pos 48),(.pos 60)]),
   ((.excluded 55),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43),(.pos 47),(.pos 48),(.pos 69)]),
   ((.excluded 56),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43),(.pos 47),(.pos 48)]),
   ((.excluded 57),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43),(.pos 47),(.pos 55),(.pos 60),(.pos 69)]),
   ((.excluded 58),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43),(.pos 47),(.pos 55),(.pos 60)]),
   ((.excluded 59),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43),(.pos 47),(.pos 55),(.pos 69)]),
   ((.excluded 60),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43),(.pos 47),(.pos 55)]),
   ((.excluded 61),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43),(.pos 47),(.pos 60),(.pos 69)]),
   ((.excluded 62),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43),(.pos 47),(.pos 60)]),
   ((.excluded 63),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43),(.pos 47),(.pos 69)]),
   ((.excluded 64),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43),(.pos 47)]),
   ((.excluded 65),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43),(.pos 48),(.pos 55),(.pos 60),(.pos 69)]),
   ((.excluded 66),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43),(.pos 48),(.pos 55),(.pos 60)]),
   ((.excluded 67),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43),(.pos 48),(.pos 55),(.pos 69)]),
   ((.excluded 68),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43),(.pos 48),(.pos 55)]),
   ((.excluded 69),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43),(.pos 48),(.pos 60),(.pos 69)]),
   ((.excluded 70),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43),(.pos 48),(.pos 60)]),
   ((.excluded 71),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43),(.pos 48),(.pos 69)]),
   ((.excluded 72),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43),(.pos 48)]),
   ((.excluded 73),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43),(.pos 55),(.pos 60),(.pos 69)]),
   ((.excluded 74),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43),(.pos 55),(.pos 60)]),
   ((.excluded 75),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43),(.pos 55),(.pos 69)]),
   ((.excluded 76),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43),(.pos 55)]),
   ((.excluded 77),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43),(.pos 60),(.pos 69)]),
   ((.excluded 78),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43),(.pos 60)]),
   ((.excluded 79),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43),(.pos 69)]),
   ((.excluded 80),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 43)]),
   ((.excluded 81),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 47),(.pos 48),(.pos 55),(.pos 60),(.pos 69)]),
   ((.excluded 82),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 47),(.pos 48),(.pos 55),(.pos 60)]),
   ((.excluded 83),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 47),(.pos 48),(.pos 55),(.pos 69)]),
   ((.excluded 84),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 47),(.pos 48),(.pos 55)]),
   ((.excluded 85),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 47),(.pos 48),(.pos 60),(.pos 69)]),
   ((.excluded 86),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 47),(.pos 48),(.pos 60)]),
   ((.excluded 87),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 47),(.pos 48),(.pos 69)]),
   ((.excluded 88),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 47),(.pos 48)]),
   ((.excluded 89),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 47),(.pos 55),(.pos 60),(.pos 69)]),
   ((.excluded 90),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 47),(.pos 55),(.pos 60)]),
   ((.excluded 91),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 47),(.pos 55),(.pos 69)]),
   ((.excluded 92),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 47),(.pos 55)]),
   ((.excluded 93),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 47),(.pos 60),(.pos 69)]),
   ((.excluded 94),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 47),(.pos 60)]),
   ((.excluded 95),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 47),(.pos 69)]),
   ((.excluded 96),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 47)]),
   ((.excluded 97),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 48),(.pos 55),(.pos 60),(.pos 69)]),
   ((.excluded 98),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 48),(.pos 55),(.pos 60)]),
   ((.excluded 99),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 48),(.pos 55),(.pos 69)]),
   ((.excluded 100),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 48),(.pos 55)]),
   ((.excluded 101),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 48),(.pos 60),(.pos 69)]),
   ((.excluded 102),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 48),(.pos 60)]),
   ((.excluded 103),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 48),(.pos 69)]),
   ((.excluded 104),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 48)]),
   ((.excluded 105),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 55),(.pos 60),(.pos 69)]),
   ((.excluded 106),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 55),(.pos 60)]),
   ((.excluded 107),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 55),(.pos 69)]),
   ((.excluded 108),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 55)]),
   ((.excluded 109),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 60),(.pos 69)]),
   ((.excluded 110),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 60)]),
   ((.excluded 111),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40),(.pos 69)]),
   ((.excluded 112),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 43),(.neg 42),(.neg 41),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 40)]),
   ((.excluded 113),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 47),(.pos 48),(.pos 55),(.pos 60),(.pos 69)]),
   ((.excluded 114),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 47),(.pos 48),(.pos 55),(.pos 60)]),
   ((.excluded 115),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 47),(.pos 48),(.pos 55),(.pos 69)]),
   ((.excluded 116),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 47),(.pos 48),(.pos 55)]),
   ((.excluded 117),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 47),(.pos 48),(.pos 60),(.pos 69)]),
   ((.excluded 118),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 47),(.pos 48),(.pos 60)]),
   ((.excluded 119),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 47),(.pos 48),(.pos 69)]),
   ((.excluded 120),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 47),(.pos 48)]),
   ((.excluded 121),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 47),(.pos 55),(.pos 60),(.pos 69)]),
   ((.excluded 122),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 47),(.pos 55),(.pos 60)]),
   ((.excluded 123),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 47),(.pos 55),(.pos 69)]),
   ((.excluded 124),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 47),(.pos 55)]),
   ((.excluded 125),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 47),(.pos 60),(.pos 69)]),
   ((.excluded 126),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 47),(.pos 60)]),
   ((.excluded 127),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 47),(.pos 69)]),
   ((.excluded 128),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 47)]),
   ((.excluded 129),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 48),(.pos 55),(.pos 60),(.pos 69)]),
   ((.excluded 130),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 48),(.pos 55),(.pos 60)]),
   ((.excluded 131),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 48),(.pos 55),(.pos 69)]),
   ((.excluded 132),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 48),(.pos 55)]),
   ((.excluded 133),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 48),(.pos 60),(.pos 69)]),
   ((.excluded 134),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 48),(.pos 60)]),
   ((.excluded 135),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 48),(.pos 69)]),
   ((.excluded 136),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 48)]),
   ((.excluded 137),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 55),(.pos 60),(.pos 69)]),
   ((.excluded 138),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 55),(.pos 60)]),
   ((.excluded 139),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 55),(.pos 69)]),
   ((.excluded 140),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 55)]),
   ((.excluded 141),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 60),(.pos 69)]),
   ((.excluded 142),[(.neg 69),(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 60)]),
   ((.excluded 143),[(.neg 68),(.neg 67),(.neg 66),(.neg 65),(.neg 64),(.neg 63),(.neg 62),(.neg 61),(.neg 60),(.neg 59),(.neg 58),(.neg 57),(.neg 56),(.neg 55),(.neg 54),(.neg 53),(.neg 52),(.neg 51),(.neg 50),(.neg 49),(.neg 48),(.neg 47),(.neg 46),(.neg 45),(.neg 44),(.neg 42),(.neg 41),(.neg 40),(.neg 39),(.neg 38),(.neg 37),(.neg 36),(.neg 35),(.pos 43),(.pos 69)])]

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



end Papers.RationalityTen.MatroidCatalogue.Cases.N8R4C72



end
end
end BundlePart2

