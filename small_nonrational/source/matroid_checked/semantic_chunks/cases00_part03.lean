module
public import MatroidCatalogue.Definitions
public import MatroidCases.N6R3C1
import all MatroidCases.N6R3C1
public import MatroidCases.N6R3C2
import all MatroidCases.N6R3C2
public import MatroidCases.N6R3C3
import all MatroidCases.N6R3C3
public import MatroidCases.N6R3C4
import all MatroidCases.N6R3C4
public import MatroidCases.N6R3C5
import all MatroidCases.N6R3C5
public import MatroidCases.N6R3C6
import all MatroidCases.N6R3C6
public import MatroidCases.N6R3C7
import all MatroidCases.N6R3C7

@[expose] public section
noncomputable section

/- Source: MatroidCatalogue/Cases/N6R3C1Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C1

abbrev U := N6R3.grid
noncomputable def old : Finset (Finset (Fin 8)) := N5R3.family 1
noncomputable def newIndexTree : Table ℕ := (.node 5 (.node 2 (.node 1 (.leaf 10) (.leaf 11)) (.node 3 (.leaf 12) (.node 4 (.leaf 13) (.leaf 14)))) (.node 7 (.node 6 (.leaf 15) (.leaf 16)) (.node 8 (.leaf 17) (.node 9 (.leaf 18) (.leaf 19)))))
noncomputable def newIndex (i : Fin 10) : Fin 20 := Fin.ofNat 20 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 3 (.node 1 (.leaf (768,1,16341192)) (.node 2 (.leaf (192,1,16339491)) (.leaf (960,3,16406152)))) (.node 5 (.node 4 (.leaf (30,8,16434824)) (.leaf (798,9,16434824))) (.node 6 (.leaf (222,9,16433690)) (.leaf (990,10,16434824)))))

noncomputable def models (i : Fin 7) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 7) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 7) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 20, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (5 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 20, (5 : Fin 8) ∈ U i → ∃ j : Fin 10, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C1

/- Source: MatroidCatalogue/Cases/N6R3C1Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C1


noncomputable def certificates_0 : List (Origin 20 7 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.neg 2)]),
   ((.fixed 3),[(.neg 3)]),
   ((.fixed 4),[(.neg 4)]),
   ((.fixed 5),[(.pos 5)]),
   ((.fixed 6),[(.pos 6)]),
   ((.fixed 7),[(.pos 7)]),
   ((.fixed 8),[(.pos 8)]),
   ((.fixed 9),[(.neg 9)]),
   ((.exchange 5 12 4),[(.neg 12),(.neg 5),(.pos 0),(.pos 11)]),
   ((.exchange 5 13 4),[(.neg 13),(.neg 5),(.pos 2),(.pos 11)]),
   ((.exchange 5 14 4),[(.neg 14),(.neg 5),(.pos 0),(.pos 2),(.pos 11)]),
   ((.exchange 5 17 2),[(.neg 17),(.neg 5),(.pos 4),(.pos 16)]),
   ((.exchange 5 19 0),[(.neg 19),(.neg 5),(.pos 9),(.pos 18)]),
   ((.exchange 6 11 4),[(.neg 11),(.neg 6),(.pos 0),(.pos 12)]),
   ((.exchange 6 16 2),[(.neg 16),(.neg 6),(.pos 4),(.pos 17)]),
   ((.exchange 7 11 4),[(.neg 11),(.neg 7),(.pos 2),(.pos 13)]),
   ((.exchange 7 18 0),[(.neg 18),(.neg 7),(.pos 9),(.pos 19)]),
   ((.exchange 8 11 4),[(.neg 11),(.neg 8),(.pos 1),(.pos 3),(.pos 14)]),
   ((.exchange 10 5 5),[(.neg 10),(.neg 5),(.pos 0),(.pos 4)]),
   ((.exchange 15 5 5),[(.neg 15),(.neg 5),(.pos 2),(.pos 9)]),
   (.newPoint,[(.pos 10),(.pos 11),(.pos 12),(.pos 13),(.pos 14),(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 19)]),
   ((.excluded 0),[(.neg 19),(.neg 18),(.pos 10),(.pos 11),(.pos 12),(.pos 13),(.pos 14),(.pos 15),(.pos 16),(.pos 17)]),
   ((.excluded 1),[(.neg 17),(.neg 16),(.pos 10),(.pos 11),(.pos 12),(.pos 13),(.pos 14),(.pos 15),(.pos 18),(.pos 19)]),
   ((.excluded 2),[(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.pos 10),(.pos 11),(.pos 12),(.pos 13),(.pos 14),(.pos 15)]),
   ((.excluded 3),[(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.pos 10),(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 19)]),
   ((.excluded 4),[(.neg 19),(.neg 18),(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.pos 10),(.pos 15),(.pos 16),(.pos 17)]),
   ((.excluded 5),[(.neg 17),(.neg 16),(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.pos 10),(.pos 15),(.pos 18),(.pos 19)]),
   ((.excluded 6),[(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.pos 10),(.pos 15)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (5 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 7,
    let w : Fin 7 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 6 3 ∧
      ValidWitness 6 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 6 3 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C1

/- Source: MatroidCatalogue/Cases/N6R3C1Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C1

noncomputable def certificates : List (Origin 20 7 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (5 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 7,
    target w < MatroidCatalogue.count 6 3 ∧
      ValidWitness 6 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 6 3 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 7) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 6) 3)
    (hold : M.bases.filter ((5 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 6 3, IsomorphicWithin 6 M.bases B := by
  apply extension_covered_of_certificate (n:=5) (r:=3) (by decide)
    catalogue old U newIndex models certificates
    N6R3.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N6R3C1.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N6R3C1.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 6 3 (target w),family_mem 6 3 (target w) hw.1,?_⟩
    exact validWitness_sound 6 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C1

/- Source: MatroidCatalogue/Cases/N6R3C2Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C2

abbrev U := N6R3.grid
noncomputable def old : Finset (Finset (Fin 8)) := N5R3.family 2
noncomputable def newIndexTree : Table ℕ := (.node 5 (.node 2 (.node 1 (.leaf 10) (.leaf 11)) (.node 3 (.leaf 12) (.node 4 (.leaf 13) (.leaf 14)))) (.node 7 (.node 6 (.leaf 15) (.leaf 16)) (.node 8 (.leaf 17) (.node 9 (.leaf 18) (.leaf 19)))))
noncomputable def newIndex (i : Fin 10) : Fin 20 := Fin.ofNat 20 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 4 (.node 2 (.node 1 (.leaf (768,2,16341192)) (.leaf (704,3,16373896))) (.node 3 (.leaf (448,3,16373000)) (.leaf (960,4,16406152)))) (.node 6 (.node 5 (.leaf (62,9,16362248)) (.leaf (830,11,16434824))) (.node 7 (.leaf (766,12,16434824)) (.node 8 (.leaf (510,12,16434376)) (.leaf (1022,13,16434824))))))

noncomputable def models (i : Fin 9) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 9) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 9) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 20, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (5 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 20, (5 : Fin 8) ∈ U i → ∃ j : Fin 10, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C2

/- Source: MatroidCatalogue/Cases/N6R3C2Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C2


noncomputable def certificates_0 : List (Origin 20 9 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.neg 2)]),
   ((.fixed 3),[(.neg 3)]),
   ((.fixed 4),[(.neg 4)]),
   ((.fixed 5),[(.pos 5)]),
   ((.fixed 6),[(.pos 6)]),
   ((.fixed 7),[(.pos 7)]),
   ((.fixed 8),[(.pos 8)]),
   ((.fixed 9),[(.pos 9)]),
   ((.exchange 5 12 4),[(.neg 12),(.neg 5),(.pos 0),(.pos 11)]),
   ((.exchange 5 13 4),[(.neg 13),(.neg 5),(.pos 2),(.pos 11)]),
   ((.exchange 5 14 4),[(.neg 14),(.neg 5),(.pos 0),(.pos 2),(.pos 11)]),
   ((.exchange 5 15 4),[(.neg 15),(.neg 5),(.pos 2),(.pos 11)]),
   ((.exchange 5 17 2),[(.neg 17),(.neg 5),(.pos 4),(.pos 16)]),
   ((.exchange 6 11 4),[(.neg 11),(.neg 6),(.pos 0),(.pos 12)]),
   ((.exchange 6 14 4),[(.neg 14),(.neg 6),(.pos 3),(.pos 12)]),
   ((.exchange 6 16 2),[(.neg 16),(.neg 6),(.pos 4),(.pos 17)]),
   ((.exchange 7 11 4),[(.neg 11),(.neg 7),(.pos 2),(.pos 13)]),
   ((.exchange 7 14 4),[(.neg 14),(.neg 7),(.pos 1),(.pos 13)]),
   ((.exchange 8 11 4),[(.neg 11),(.neg 8),(.pos 1),(.pos 3),(.pos 14)]),
   ((.exchange 8 12 4),[(.neg 12),(.neg 8),(.pos 3),(.pos 14)]),
   ((.exchange 8 13 4),[(.neg 13),(.neg 8),(.pos 1),(.pos 14)]),
   ((.exchange 8 15 4),[(.neg 15),(.neg 8),(.pos 3),(.pos 14)]),
   ((.exchange 9 11 4),[(.neg 11),(.neg 9),(.pos 2),(.pos 15)]),
   ((.exchange 9 14 4),[(.neg 14),(.neg 9),(.pos 3),(.pos 15)]),
   ((.exchange 10 5 5),[(.neg 10),(.neg 5),(.pos 0),(.pos 4)]),
   ((.exchange 17 9 1),[(.neg 17),(.neg 9),(.pos 18),(.pos 19)]),
   ((.exchange 18 7 2),[(.neg 18),(.neg 7),(.pos 16),(.pos 19)]),
   ((.exchange 19 5 3),[(.neg 19),(.neg 5),(.pos 16),(.pos 18)]),
   (.newPoint,[(.pos 10),(.pos 11),(.pos 12),(.pos 13),(.pos 14),(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 19)]),
   ((.excluded 0),[(.neg 19),(.neg 18),(.pos 10),(.pos 11),(.pos 12),(.pos 13),(.pos 14),(.pos 15),(.pos 16),(.pos 17)]),
   ((.excluded 1),[(.neg 19),(.neg 17),(.neg 16),(.pos 10),(.pos 11),(.pos 12),(.pos 13),(.pos 14),(.pos 15),(.pos 18)]),
   ((.excluded 2),[(.neg 18),(.neg 17),(.neg 16),(.pos 10),(.pos 11),(.pos 12),(.pos 13),(.pos 14),(.pos 15),(.pos 19)]),
   ((.excluded 3),[(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.pos 10),(.pos 11),(.pos 12),(.pos 13),(.pos 14),(.pos 15)]),
   ((.excluded 4),[(.neg 15),(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.pos 10),(.pos 16),(.pos 17),(.pos 18),(.pos 19)]),
   ((.excluded 5),[(.neg 19),(.neg 18),(.neg 15),(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.pos 10),(.pos 16),(.pos 17)]),
   ((.excluded 6),[(.neg 19),(.neg 17),(.neg 16),(.neg 15),(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.pos 10),(.pos 18)]),
   ((.excluded 7),[(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.pos 10),(.pos 19)]),
   ((.excluded 8),[(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.pos 10)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (5 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 9,
    let w : Fin 9 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 6 3 ∧
      ValidWitness 6 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 6 3 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C2

/- Source: MatroidCatalogue/Cases/N6R3C2Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C2

noncomputable def certificates : List (Origin 20 9 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (5 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 9,
    target w < MatroidCatalogue.count 6 3 ∧
      ValidWitness 6 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 6 3 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 9) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 6) 3)
    (hold : M.bases.filter ((5 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 6 3, IsomorphicWithin 6 M.bases B := by
  apply extension_covered_of_certificate (n:=5) (r:=3) (by decide)
    catalogue old U newIndex models certificates
    N6R3.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N6R3C2.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N6R3C2.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 6 3 (target w),family_mem 6 3 (target w) hw.1,?_⟩
    exact validWitness_sound 6 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C2

/- Source: MatroidCatalogue/Cases/N6R3C3Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C3

abbrev U := N6R3.grid
noncomputable def old : Finset (Finset (Fin 8)) := N5R3.family 3
noncomputable def newIndexTree : Table ℕ := (.node 5 (.node 2 (.node 1 (.leaf 10) (.leaf 11)) (.node 3 (.leaf 12) (.node 4 (.leaf 13) (.leaf 14)))) (.node 7 (.node 6 (.leaf 15) (.leaf 16)) (.node 8 (.leaf 17) (.node 9 (.leaf 18) (.leaf 19)))))
noncomputable def newIndex (i : Fin 10) : Fin 20 := Fin.ofNat 20 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 5 (.node 2 (.node 1 (.leaf (896,4,16308432)) (.leaf (832,4,16308418))) (.node 3 (.leaf (704,4,16308250)) (.node 4 (.leaf (448,4,16306458)) (.leaf (960,5,16406152))))) (.node 8 (.node 6 (.leaf (63,14,16288538)) (.node 7 (.leaf (959,15,16434824)) (.leaf (895,15,16434817)))) (.node 9 (.leaf (767,15,16434705)) (.node 10 (.leaf (511,15,16433361)) (.leaf (1023,16,16434824))))))

noncomputable def models (i : Fin 11) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 11) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 11) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 20, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (5 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 20, (5 : Fin 8) ∈ U i → ∃ j : Fin 10, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C3

/- Source: MatroidCatalogue/Cases/N6R3C3Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C3


noncomputable def certificates_0 : List (Origin 20 11 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.neg 2)]),
   ((.fixed 3),[(.neg 3)]),
   ((.fixed 4),[(.pos 4)]),
   ((.fixed 5),[(.pos 5)]),
   ((.fixed 6),[(.pos 6)]),
   ((.fixed 7),[(.pos 7)]),
   ((.fixed 8),[(.pos 8)]),
   ((.fixed 9),[(.pos 9)]),
   ((.exchange 4 11 4),[(.neg 11),(.neg 4),(.pos 0),(.pos 10)]),
   ((.exchange 4 12 4),[(.neg 12),(.neg 4),(.pos 0),(.pos 10)]),
   ((.exchange 4 13 4),[(.neg 13),(.neg 4),(.pos 1),(.pos 10)]),
   ((.exchange 4 14 4),[(.neg 14),(.neg 4),(.pos 1),(.pos 10)]),
   ((.exchange 4 15 4),[(.neg 15),(.neg 4),(.pos 0),(.pos 1),(.pos 10)]),
   ((.exchange 5 10 4),[(.neg 10),(.neg 5),(.pos 0),(.pos 11)]),
   ((.exchange 6 10 4),[(.neg 10),(.neg 6),(.pos 0),(.pos 12)]),
   ((.exchange 7 10 4),[(.neg 10),(.neg 7),(.pos 1),(.pos 13)]),
   ((.exchange 8 10 4),[(.neg 10),(.neg 8),(.pos 1),(.pos 14)]),
   ((.exchange 9 10 4),[(.neg 10),(.neg 9),(.pos 2),(.pos 3),(.pos 15)]),
   ((.exchange 16 8 0),[(.neg 16),(.neg 8),(.pos 17),(.pos 19)]),
   ((.exchange 16 9 0),[(.neg 16),(.neg 9),(.pos 18),(.pos 19)]),
   ((.exchange 17 5 1),[(.neg 17),(.neg 5),(.pos 16),(.pos 18)]),
   ((.exchange 17 9 1),[(.neg 17),(.neg 9),(.pos 18),(.pos 19)]),
   ((.exchange 18 4 2),[(.neg 18),(.neg 4),(.pos 16),(.pos 17)]),
   ((.exchange 18 7 2),[(.neg 18),(.neg 7),(.pos 16),(.pos 19)]),
   ((.exchange 18 13 2),[(.neg 18),(.neg 13),(.pos 16),(.pos 19)]),
   ((.exchange 19 5 3),[(.neg 19),(.neg 5),(.pos 16),(.pos 18)]),
   ((.exchange 19 6 3),[(.neg 19),(.neg 6),(.pos 17),(.pos 18)]),
   (.newPoint,[(.pos 10),(.pos 11),(.pos 12),(.pos 13),(.pos 14),(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 19)]),
   ((.excluded 0),[(.neg 19),(.neg 18),(.neg 17),(.pos 10),(.pos 11),(.pos 12),(.pos 13),(.pos 14),(.pos 15),(.pos 16)]),
   ((.excluded 1),[(.neg 19),(.neg 18),(.neg 16),(.pos 10),(.pos 11),(.pos 12),(.pos 13),(.pos 14),(.pos 15),(.pos 17)]),
   ((.excluded 2),[(.neg 19),(.neg 17),(.neg 16),(.pos 10),(.pos 11),(.pos 12),(.pos 13),(.pos 14),(.pos 15),(.pos 18)]),
   ((.excluded 3),[(.neg 18),(.neg 17),(.neg 16),(.pos 10),(.pos 11),(.pos 12),(.pos 13),(.pos 14),(.pos 15),(.pos 19)]),
   ((.excluded 4),[(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.pos 10),(.pos 11),(.pos 12),(.pos 13),(.pos 14),(.pos 15)]),
   ((.excluded 5),[(.neg 15),(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.pos 16),(.pos 17),(.pos 18),(.pos 19)]),
   ((.excluded 6),[(.neg 19),(.neg 18),(.neg 17),(.neg 15),(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.pos 16)]),
   ((.excluded 7),[(.neg 19),(.neg 18),(.neg 16),(.neg 15),(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.pos 17)]),
   ((.excluded 8),[(.neg 19),(.neg 17),(.neg 16),(.neg 15),(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.pos 18)]),
   ((.excluded 9),[(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.pos 19)]),
   ((.excluded 10),[(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 10)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (5 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 11,
    let w : Fin 11 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 6 3 ∧
      ValidWitness 6 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 6 3 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C3

/- Source: MatroidCatalogue/Cases/N6R3C3Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C3

noncomputable def certificates : List (Origin 20 11 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (5 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 11,
    target w < MatroidCatalogue.count 6 3 ∧
      ValidWitness 6 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 6 3 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 11) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 6) 3)
    (hold : M.bases.filter ((5 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 6 3, IsomorphicWithin 6 M.bases B := by
  apply extension_covered_of_certificate (n:=5) (r:=3) (by decide)
    catalogue old U newIndex models certificates
    N6R3.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N6R3C3.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N6R3C3.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 6 3 (target w),family_mem 6 3 (target w) hw.1,?_⟩
    exact validWitness_sound 6 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C3

/- Source: MatroidCatalogue/Cases/N6R3C4Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C4

abbrev U := N6R3.grid
noncomputable def old : Finset (Finset (Fin 8)) := N5R3.family 4
noncomputable def newIndexTree : Table ℕ := (.node 5 (.node 2 (.node 1 (.leaf 10) (.leaf 11)) (.node 3 (.leaf 12) (.node 4 (.leaf 13) (.leaf 14)))) (.node 7 (.node 6 (.leaf 15) (.leaf 16)) (.node 8 (.leaf 17) (.node 9 (.leaf 18) (.leaf 19)))))
noncomputable def newIndex (i : Fin 10) : Fin 20 := Fin.ofNat 20 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 4 (.node 2 (.node 1 (.leaf (216,9,16308250)) (.leaf (198,9,16306458))) (.node 3 (.leaf (30,9,16288538)) (.leaf (222,14,16434824)))) (.node 6 (.node 5 (.leaf (800,6,16341192)) (.leaf (1016,12,16373896))) (.node 7 (.leaf (998,12,16373000)) (.node 8 (.leaf (830,12,16362248)) (.leaf (1022,17,16434824))))))

noncomputable def models (i : Fin 9) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 9) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 9) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 20, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (5 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 20, (5 : Fin 8) ∈ U i → ∃ j : Fin 10, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C4

/- Source: MatroidCatalogue/Cases/N6R3C4Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C4


noncomputable def certificates_0 : List (Origin 20 9 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.pos 2)]),
   ((.fixed 3),[(.pos 3)]),
   ((.fixed 4),[(.neg 4)]),
   ((.fixed 5),[(.pos 5)]),
   ((.fixed 6),[(.pos 6)]),
   ((.fixed 7),[(.pos 7)]),
   ((.fixed 9),[(.neg 9)]),
   ((.exchange 2 12 3),[(.neg 12),(.neg 2),(.pos 0),(.pos 11)]),
   ((.exchange 2 14 2),[(.neg 14),(.neg 2),(.pos 1),(.pos 13)]),
   ((.exchange 2 18 0),[(.neg 18),(.neg 2),(.pos 9),(.pos 15)]),
   ((.exchange 2 19 0),[(.neg 19),(.neg 2),(.pos 9),(.pos 15)]),
   ((.exchange 3 11 3),[(.neg 11),(.neg 3),(.pos 0),(.pos 12)]),
   ((.exchange 3 13 2),[(.neg 13),(.neg 3),(.pos 1),(.pos 14)]),
   ((.exchange 5 15 0),[(.neg 15),(.neg 5),(.pos 9),(.pos 18)]),
   ((.exchange 5 17 2),[(.neg 17),(.neg 5),(.pos 4),(.pos 16)]),
   ((.exchange 5 19 0),[(.neg 19),(.neg 5),(.pos 9),(.pos 18)]),
   ((.exchange 6 16 2),[(.neg 16),(.neg 6),(.pos 4),(.pos 17)]),
   ((.exchange 7 15 0),[(.neg 15),(.neg 7),(.pos 9),(.pos 19)]),
   ((.exchange 7 18 0),[(.neg 18),(.neg 7),(.pos 9),(.pos 19)]),
   ((.exchange 10 2 5),[(.neg 10),(.neg 2),(.pos 0),(.pos 1)]),
   ((.exchange 11 7 2),[(.neg 11),(.neg 7),(.pos 13),(.pos 16)]),
   ((.exchange 12 7 2),[(.neg 12),(.neg 7),(.pos 10),(.pos 14),(.pos 17)]),
   ((.exchange 13 5 3),[(.neg 13),(.neg 5),(.pos 11),(.pos 16)]),
   ((.exchange 14 5 3),[(.neg 14),(.neg 5),(.pos 10),(.pos 12),(.pos 17)]),
   ((.exchange 16 2 4),[(.neg 16),(.neg 2),(.pos 11),(.pos 13)]),
   ((.exchange 17 2 4),[(.neg 17),(.neg 2),(.pos 10),(.pos 12),(.pos 14)]),
   (.newPoint,[(.pos 10),(.pos 11),(.pos 12),(.pos 13),(.pos 14),(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 19)]),
   ((.excluded 0),[(.neg 17),(.neg 16),(.neg 14),(.neg 13),(.pos 10),(.pos 11),(.pos 12),(.pos 15),(.pos 18),(.pos 19)]),
   ((.excluded 1),[(.neg 17),(.neg 16),(.neg 12),(.neg 11),(.pos 10),(.pos 13),(.pos 14),(.pos 15),(.pos 18),(.pos 19)]),
   ((.excluded 2),[(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.pos 10),(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 19)]),
   ((.excluded 3),[(.neg 17),(.neg 16),(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.pos 10),(.pos 15),(.pos 18),(.pos 19)]),
   ((.excluded 4),[(.neg 19),(.neg 18),(.neg 15),(.pos 10),(.pos 11),(.pos 12),(.pos 13),(.pos 14),(.pos 16),(.pos 17)]),
   ((.excluded 5),[(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.neg 14),(.neg 13),(.pos 10),(.pos 11),(.pos 12)]),
   ((.excluded 6),[(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.neg 12),(.neg 11),(.pos 10),(.pos 13),(.pos 14)]),
   ((.excluded 7),[(.neg 19),(.neg 18),(.neg 15),(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.pos 10),(.pos 16),(.pos 17)]),
   ((.excluded 8),[(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.pos 10)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (5 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 9,
    let w : Fin 9 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 6 3 ∧
      ValidWitness 6 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 6 3 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C4

/- Source: MatroidCatalogue/Cases/N6R3C4Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C4

noncomputable def certificates : List (Origin 20 9 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (5 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 9,
    target w < MatroidCatalogue.count 6 3 ∧
      ValidWitness 6 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 6 3 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 9) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 6) 3)
    (hold : M.bases.filter ((5 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 6 3, IsomorphicWithin 6 M.bases B := by
  apply extension_covered_of_certificate (n:=5) (r:=3) (by decide)
    catalogue old U newIndex models certificates
    N6R3.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N6R3C4.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N6R3C4.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 6 3 (target w),family_mem 6 3 (target w) hw.1,?_⟩
    exact validWitness_sound 6 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C4

/- Source: MatroidCatalogue/Cases/N6R3C5Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C5

abbrev U := N6R3.grid
noncomputable def old : Finset (Finset (Fin 8)) := N5R3.family 5
noncomputable def newIndexTree : Table ℕ := (.node 5 (.node 2 (.node 1 (.leaf 10) (.leaf 11)) (.node 3 (.leaf 12) (.node 4 (.leaf 13) (.leaf 14)))) (.node 7 (.node 6 (.leaf 15) (.leaf 16)) (.node 8 (.leaf 17) (.node 9 (.leaf 18) (.leaf 19)))))
noncomputable def newIndex (i : Fin 10) : Fin 20 := Fin.ofNat 20 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 7 (.node 3 (.node 1 (.leaf (800,7,16341192)) (.node 2 (.leaf (728,10,16373896)) (.leaf (504,12,16341192)))) (.node 5 (.node 4 (.leaf (1016,13,16373896)) (.leaf (454,10,16373000))) (.node 6 (.leaf (62,10,16362248)) (.leaf (510,17,16397640))))) (.node 10 (.node 8 (.leaf (742,12,16340744)) (.node 9 (.leaf (998,13,16373000)) (.leaf (798,12,16333576)))) (.node 12 (.node 11 (.leaf (830,13,16362248)) (.leaf (990,17,16406152))) (.node 13 (.leaf (766,17,16398984)) (.leaf (1022,18,16434824))))))

noncomputable def models (i : Fin 14) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 14) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 14) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 20, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (5 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 20, (5 : Fin 8) ∈ U i → ∃ j : Fin 10, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C5

/- Source: MatroidCatalogue/Cases/N6R3C5Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C5


noncomputable def certificates_0 : List (Origin 20 14 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.pos 2)]),
   ((.fixed 3),[(.pos 3)]),
   ((.fixed 4),[(.neg 4)]),
   ((.fixed 5),[(.pos 5)]),
   ((.fixed 6),[(.pos 6)]),
   ((.fixed 7),[(.pos 7)]),
   ((.fixed 8),[(.pos 8)]),
   ((.fixed 9),[(.pos 9)]),
   ((.exchange 2 12 3),[(.neg 12),(.neg 2),(.pos 0),(.pos 11)]),
   ((.exchange 2 14 2),[(.neg 14),(.neg 2),(.pos 1),(.pos 13)]),
   ((.exchange 3 11 3),[(.neg 11),(.neg 3),(.pos 0),(.pos 12)]),
   ((.exchange 3 13 2),[(.neg 13),(.neg 3),(.pos 1),(.pos 14)]),
   ((.exchange 5 17 2),[(.neg 17),(.neg 5),(.pos 4),(.pos 16)]),
   ((.exchange 6 16 2),[(.neg 16),(.neg 6),(.pos 4),(.pos 17)]),
   ((.exchange 10 2 5),[(.neg 10),(.neg 2),(.pos 0),(.pos 1)]),
   ((.exchange 11 7 2),[(.neg 11),(.neg 7),(.pos 13),(.pos 16)]),
   ((.exchange 11 9 0),[(.neg 11),(.neg 9),(.pos 15),(.pos 18)]),
   ((.exchange 12 7 2),[(.neg 12),(.neg 7),(.pos 10),(.pos 14),(.pos 17)]),
   ((.exchange 12 9 1),[(.neg 12),(.neg 9),(.pos 15),(.pos 18)]),
   ((.exchange 13 5 3),[(.neg 13),(.neg 5),(.pos 11),(.pos 16)]),
   ((.exchange 14 5 3),[(.neg 14),(.neg 5),(.pos 10),(.pos 12),(.pos 17)]),
   ((.exchange 14 18 1),[(.neg 18),(.neg 14),(.pos 15),(.pos 19)]),
   ((.exchange 15 5 3),[(.neg 15),(.neg 5),(.pos 11),(.pos 18)]),
   ((.exchange 15 8 2),[(.neg 15),(.neg 8),(.pos 14),(.pos 19)]),
   ((.exchange 15 16 3),[(.neg 16),(.neg 15),(.pos 11),(.pos 18)]),
   ((.exchange 16 2 4),[(.neg 16),(.neg 2),(.pos 11),(.pos 13)]),
   ((.exchange 16 3 4),[(.neg 16),(.neg 3),(.pos 10),(.pos 11),(.pos 13)]),
   ((.exchange 17 2 4),[(.neg 17),(.neg 2),(.pos 10),(.pos 12),(.pos 14)]),
   ((.exchange 17 3 4),[(.neg 17),(.neg 3),(.pos 12),(.pos 14)]),
   ((.exchange 17 9 1),[(.neg 17),(.neg 9),(.pos 18),(.pos 19)]),
   ((.exchange 18 2 4),[(.neg 18),(.neg 2),(.pos 11),(.pos 15)]),
   ((.exchange 18 7 2),[(.neg 18),(.neg 7),(.pos 16),(.pos 19)]),
   ((.exchange 18 13 4),[(.neg 18),(.neg 13),(.pos 11),(.pos 15)]),
   ((.exchange 19 3 4),[(.neg 19),(.neg 3),(.pos 14),(.pos 15)]),
   ((.exchange 19 5 3),[(.neg 19),(.neg 5),(.pos 16),(.pos 18)]),
   (.newPoint,[(.pos 10),(.pos 11),(.pos 12),(.pos 13),(.pos 14),(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 19)]),
   ((.excluded 0),[(.neg 19),(.neg 18),(.neg 15),(.pos 10),(.pos 11),(.pos 12),(.pos 13),(.pos 14),(.pos 16),(.pos 17)]),
   ((.excluded 1),[(.neg 19),(.neg 17),(.neg 16),(.neg 14),(.neg 13),(.pos 10),(.pos 11),(.pos 12),(.pos 15),(.pos 18)]),
   ((.excluded 2),[(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.neg 14),(.neg 13),(.pos 10),(.pos 11),(.pos 12),(.pos 19)]),
   ((.excluded 3),[(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.neg 14),(.neg 13),(.pos 10),(.pos 11),(.pos 12)]),
   ((.excluded 4),[(.neg 18),(.neg 17),(.neg 16),(.neg 12),(.neg 11),(.pos 10),(.pos 13),(.pos 14),(.pos 15),(.pos 19)]),
   ((.excluded 5),[(.neg 15),(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.pos 10),(.pos 16),(.pos 17),(.pos 18),(.pos 19)]),
   ((.excluded 6),[(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.pos 10),(.pos 19)]),
   ((.excluded 7),[(.neg 19),(.neg 17),(.neg 16),(.neg 15),(.neg 12),(.neg 11),(.pos 10),(.pos 13),(.pos 14),(.pos 18)]),
   ((.excluded 8),[(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.neg 12),(.neg 11),(.pos 10),(.pos 13),(.pos 14)]),
   ((.excluded 9),[(.neg 19),(.neg 18),(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.pos 10),(.pos 15),(.pos 16),(.pos 17)]),
   ((.excluded 10),[(.neg 19),(.neg 18),(.neg 15),(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.pos 10),(.pos 16),(.pos 17)]),
   ((.excluded 11),[(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.pos 10),(.pos 15)]),
   ((.excluded 12),[(.neg 19),(.neg 17),(.neg 16),(.neg 15),(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.pos 10),(.pos 18)]),
   ((.excluded 13),[(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.pos 10)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (5 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 14,
    let w : Fin 14 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 6 3 ∧
      ValidWitness 6 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 6 3 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C5

/- Source: MatroidCatalogue/Cases/N6R3C5Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C5

noncomputable def certificates : List (Origin 20 14 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (5 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 14,
    target w < MatroidCatalogue.count 6 3 ∧
      ValidWitness 6 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 6 3 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 14) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 6) 3)
    (hold : M.bases.filter ((5 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 6 3, IsomorphicWithin 6 M.bases B := by
  apply extension_covered_of_certificate (n:=5) (r:=3) (by decide)
    catalogue old U newIndex models certificates
    N6R3.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N6R3C5.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N6R3C5.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 6 3 (target w),family_mem 6 3 (target w) hw.1,?_⟩
    exact validWitness_sound 6 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C5

/- Source: MatroidCatalogue/Cases/N6R3C6Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C6

abbrev U := N6R3.grid
noncomputable def old : Finset (Finset (Fin 8)) := N5R3.family 6
noncomputable def newIndexTree : Table ℕ := (.node 5 (.node 2 (.node 1 (.leaf 10) (.leaf 11)) (.node 3 (.leaf 12) (.node 4 (.leaf 13) (.leaf 14)))) (.node 7 (.node 6 (.leaf 15) (.leaf 16)) (.node 8 (.leaf 17) (.node 9 (.leaf 18) (.leaf 19)))))
noncomputable def newIndex (i : Fin 10) : Fin 20 := Fin.ofNat 20 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 7 (.node 3 (.node 1 (.leaf (432,11,16308432)) (.node 2 (.leaf (872,12,16308418)) (.leaf (728,12,16308250)))) (.node 5 (.node 4 (.leaf (1016,15,16373896)) (.leaf (391,12,16298338))) (.node 6 (.leaf (55,12,16287586)) (.leaf (439,15,16360288))))) (.node 10 (.node 8 (.leaf (751,19,16434376)) (.node 9 (.leaf (1007,20,16434376)) (.leaf (767,20,16427096)))) (.node 12 (.node 11 (.leaf (863,19,16427208)) (.leaf (991,20,16434264))) (.node 13 (.leaf (895,20,16427208)) (.leaf (1023,21,16434824))))))

noncomputable def models (i : Fin 14) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 14) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 14) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 20, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (5 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 20, (5 : Fin 8) ∈ U i → ∃ j : Fin 10, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C6

/- Source: MatroidCatalogue/Cases/N6R3C6Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C6


noncomputable def certificates_0 : List (Origin 20 14 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.pos 1)]),
   ((.fixed 2),[(.pos 2)]),
   ((.fixed 3),[(.pos 3)]),
   ((.fixed 4),[(.pos 4)]),
   ((.fixed 5),[(.pos 5)]),
   ((.fixed 6),[(.pos 6)]),
   ((.fixed 7),[(.neg 7)]),
   ((.fixed 8),[(.pos 8)]),
   ((.fixed 9),[(.pos 9)]),
   ((.exchange 1 11 3),[(.neg 11),(.neg 1),(.pos 0),(.pos 10)]),
   ((.exchange 1 12 3),[(.neg 12),(.neg 1),(.pos 0),(.pos 10)]),
   ((.exchange 1 16 1),[(.neg 16),(.neg 1),(.pos 7),(.pos 13)]),
   ((.exchange 1 19 1),[(.neg 19),(.neg 1),(.pos 7),(.pos 13)]),
   ((.exchange 2 10 3),[(.neg 10),(.neg 2),(.pos 0),(.pos 11)]),
   ((.exchange 3 10 3),[(.neg 10),(.neg 3),(.pos 0),(.pos 12)]),
   ((.exchange 4 13 1),[(.neg 13),(.neg 4),(.pos 7),(.pos 16)]),
   ((.exchange 4 19 1),[(.neg 19),(.neg 4),(.pos 7),(.pos 16)]),
   ((.exchange 8 13 1),[(.neg 13),(.neg 8),(.pos 7),(.pos 19)]),
   ((.exchange 8 16 1),[(.neg 16),(.neg 8),(.pos 7),(.pos 19)]),
   ((.exchange 10 8 0),[(.neg 10),(.neg 8),(.pos 14),(.pos 17)]),
   ((.exchange 11 9 0),[(.neg 11),(.neg 9),(.pos 15),(.pos 18)]),
   ((.exchange 12 19 1),[(.neg 19),(.neg 12),(.pos 15),(.pos 18)]),
   ((.exchange 13 3 0),[(.neg 13),(.neg 3),(.pos 14),(.pos 15)]),
   ((.exchange 14 4 3),[(.neg 14),(.neg 4),(.pos 10),(.pos 17)]),
   ((.exchange 14 5 3),[(.neg 14),(.neg 5),(.pos 10),(.pos 12),(.pos 17)]),
   ((.exchange 14 11 1),[(.neg 14),(.neg 11),(.pos 13),(.pos 15)]),
   ((.exchange 15 5 3),[(.neg 15),(.neg 5),(.pos 11),(.pos 18)]),
   ((.exchange 15 17 2),[(.neg 17),(.neg 15),(.pos 14),(.pos 19)]),
   ((.exchange 17 1 4),[(.neg 17),(.neg 1),(.pos 10),(.pos 14)]),
   ((.exchange 17 2 1),[(.neg 17),(.neg 2),(.pos 16),(.pos 18),(.pos 19)]),
   ((.exchange 17 2 4),[(.neg 17),(.neg 2),(.pos 10),(.pos 12),(.pos 14)]),
   ((.exchange 17 9 1),[(.neg 17),(.neg 9),(.pos 18),(.pos 19)]),
   ((.exchange 18 1 2),[(.neg 18),(.neg 1),(.pos 16),(.pos 17),(.pos 19)]),
   ((.exchange 18 1 4),[(.neg 18),(.neg 1),(.pos 11),(.pos 12),(.pos 15)]),
   ((.exchange 18 10 2),[(.neg 18),(.neg 10),(.pos 16),(.pos 17)]),
   ((.exchange 18 13 4),[(.neg 18),(.neg 13),(.pos 11),(.pos 15)]),
   ((.exchange 19 6 3),[(.neg 19),(.neg 6),(.pos 17),(.pos 18)]),
   (.newPoint,[(.pos 10),(.pos 11),(.pos 12),(.pos 13),(.pos 14),(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 19)]),
   ((.excluded 0),[(.neg 18),(.neg 17),(.neg 15),(.neg 14),(.pos 10),(.pos 11),(.pos 12),(.pos 13),(.pos 16),(.pos 19)]),
   ((.excluded 1),[(.neg 19),(.neg 18),(.neg 16),(.neg 15),(.neg 13),(.pos 10),(.pos 11),(.pos 12),(.pos 14),(.pos 17)]),
   ((.excluded 2),[(.neg 19),(.neg 17),(.neg 16),(.neg 14),(.neg 13),(.pos 10),(.pos 11),(.pos 12),(.pos 15),(.pos 18)]),
   ((.excluded 3),[(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.neg 14),(.neg 13),(.pos 10),(.pos 11),(.pos 12)]),
   ((.excluded 4),[(.neg 18),(.neg 17),(.neg 12),(.neg 11),(.neg 10),(.pos 13),(.pos 14),(.pos 15),(.pos 16),(.pos 19)]),
   ((.excluded 5),[(.neg 15),(.neg 14),(.neg 12),(.neg 11),(.neg 10),(.pos 13),(.pos 16),(.pos 17),(.pos 18),(.pos 19)]),
   ((.excluded 6),[(.neg 18),(.neg 17),(.neg 15),(.neg 14),(.neg 12),(.neg 11),(.neg 10),(.pos 13),(.pos 16),(.pos 19)]),
   ((.excluded 7),[(.neg 19),(.neg 17),(.neg 16),(.neg 15),(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.pos 14),(.pos 18)]),
   ((.excluded 8),[(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.pos 14)]),
   ((.excluded 9),[(.neg 19),(.neg 17),(.neg 16),(.neg 15),(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.pos 18)]),
   ((.excluded 10),[(.neg 19),(.neg 18),(.neg 16),(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.pos 15),(.pos 17)]),
   ((.excluded 11),[(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.pos 15)]),
   ((.excluded 12),[(.neg 19),(.neg 18),(.neg 16),(.neg 15),(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.pos 17)]),
   ((.excluded 13),[(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 10)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (5 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 14,
    let w : Fin 14 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 6 3 ∧
      ValidWitness 6 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 6 3 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C6

/- Source: MatroidCatalogue/Cases/N6R3C6Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C6

noncomputable def certificates : List (Origin 20 14 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (5 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 14,
    target w < MatroidCatalogue.count 6 3 ∧
      ValidWitness 6 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 6 3 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 14) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 6) 3)
    (hold : M.bases.filter ((5 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 6 3, IsomorphicWithin 6 M.bases B := by
  apply extension_covered_of_certificate (n:=5) (r:=3) (by decide)
    catalogue old U newIndex models certificates
    N6R3.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N6R3C6.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N6R3C6.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 6 3 (target w),family_mem 6 3 (target w) hw.1,?_⟩
    exact validWitness_sound 6 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C6

/- Source: MatroidCatalogue/Cases/N6R3C7Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C7

abbrev U := N6R3.grid
noncomputable def old : Finset (Finset (Fin 8)) := N5R3.family 7
noncomputable def newIndexTree : Table ℕ := (.node 5 (.node 2 (.node 1 (.leaf 10) (.leaf 11)) (.node 3 (.leaf 12) (.node 4 (.leaf 13) (.leaf 14)))) (.node 7 (.node 6 (.leaf 15) (.leaf 16)) (.node 8 (.leaf 17) (.node 9 (.leaf 18) (.leaf 19)))))
noncomputable def newIndex (i : Fin 10) : Fin 20 := Fin.ofNat 20 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (944,13,16308432)) (.leaf (872,13,16308418))) (.node 3 (.leaf (728,13,16308250)) (.node 4 (.leaf (504,15,16275665)) (.leaf (1016,16,16373896))))) (.node 7 (.node 6 (.leaf (455,17,16306458)) (.leaf (63,17,16288538))) (.node 8 (.leaf (511,22,16434824)) (.node 9 (.leaf (887,20,16341192)) (.leaf (759,20,16341080)))))) (.node 15 (.node 12 (.node 11 (.leaf (1015,21,16406152)) (.leaf (863,20,16337475))) (.node 13 (.leaf (895,21,16398977)) (.node 14 (.leaf (927,20,16337496)) (.leaf (991,21,16406033))))) (.node 18 (.node 16 (.leaf (943,20,16337608)) (.node 17 (.leaf (959,21,16398984)) (.leaf (751,20,16341059)))) (.node 19 (.leaf (1007,21,16406145)) (.node 20 (.leaf (767,21,16398865)) (.leaf (1023,23,16434824)))))))

noncomputable def models (i : Fin 21) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 21) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 21) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 20, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (5 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 20, (5 : Fin 8) ∈ U i → ∃ j : Fin 10, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C7

/- Source: MatroidCatalogue/Cases/N6R3C7Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C7


noncomputable def certificates_0 : List (Origin 20 21 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.pos 1)]),
   ((.fixed 2),[(.pos 2)]),
   ((.fixed 3),[(.pos 3)]),
   ((.fixed 4),[(.pos 4)]),
   ((.fixed 5),[(.pos 5)]),
   ((.fixed 6),[(.pos 6)]),
   ((.fixed 7),[(.pos 7)]),
   ((.fixed 8),[(.pos 8)]),
   ((.fixed 9),[(.pos 9)]),
   ((.exchange 1 11 3),[(.neg 11),(.neg 1),(.pos 0),(.pos 10)]),
   ((.exchange 1 12 3),[(.neg 12),(.neg 1),(.pos 0),(.pos 10)]),
   ((.exchange 2 10 3),[(.neg 10),(.neg 2),(.pos 0),(.pos 11)]),
   ((.exchange 3 10 3),[(.neg 10),(.neg 3),(.pos 0),(.pos 12)]),
   ((.exchange 10 7 1),[(.neg 10),(.neg 7),(.pos 13),(.pos 16)]),
   ((.exchange 10 8 0),[(.neg 10),(.neg 8),(.pos 14),(.pos 17)]),
   ((.exchange 11 19 2),[(.neg 19),(.neg 11),(.pos 13),(.pos 16)]),
   ((.exchange 12 9 1),[(.neg 12),(.neg 9),(.pos 15),(.pos 18)]),
   ((.exchange 13 5 3),[(.neg 13),(.neg 5),(.pos 11),(.pos 16)]),
   ((.exchange 13 8 0),[(.neg 13),(.neg 8),(.pos 14),(.pos 19)]),
   ((.exchange 13 9 0),[(.neg 13),(.neg 9),(.pos 15),(.pos 19)]),
   ((.exchange 13 12 0),[(.neg 13),(.neg 12),(.pos 14),(.pos 15)]),
   ((.exchange 14 4 3),[(.neg 14),(.neg 4),(.pos 10),(.pos 17)]),
   ((.exchange 14 7 1),[(.neg 14),(.neg 7),(.pos 13),(.pos 19)]),
   ((.exchange 14 9 1),[(.neg 14),(.neg 9),(.pos 15),(.pos 19)]),
   ((.exchange 15 1 2),[(.neg 15),(.neg 1),(.pos 13),(.pos 14)]),
   ((.exchange 15 5 3),[(.neg 15),(.neg 5),(.pos 11),(.pos 18)]),
   ((.exchange 15 7 2),[(.neg 15),(.neg 7),(.pos 13),(.pos 19)]),
   ((.exchange 15 8 2),[(.neg 15),(.neg 8),(.pos 14),(.pos 19)]),
   ((.exchange 16 1 4),[(.neg 16),(.neg 1),(.pos 10),(.pos 13)]),
   ((.exchange 16 8 0),[(.neg 16),(.neg 8),(.pos 17),(.pos 19)]),
   ((.exchange 16 9 0),[(.neg 16),(.neg 9),(.pos 18),(.pos 19)]),
   ((.exchange 16 15 0),[(.neg 16),(.neg 15),(.pos 18),(.pos 19)]),
   ((.exchange 17 2 1),[(.neg 17),(.neg 2),(.pos 16),(.pos 18),(.pos 19)]),
   ((.exchange 17 2 4),[(.neg 17),(.neg 2),(.pos 10),(.pos 12),(.pos 14)]),
   ((.exchange 17 9 1),[(.neg 17),(.neg 9),(.pos 18),(.pos 19)]),
   ((.exchange 18 1 4),[(.neg 18),(.neg 1),(.pos 11),(.pos 12),(.pos 15)]),
   ((.exchange 18 4 2),[(.neg 18),(.neg 4),(.pos 16),(.pos 17)]),
   ((.exchange 18 7 2),[(.neg 18),(.neg 7),(.pos 16),(.pos 19)]),
   ((.exchange 18 13 4),[(.neg 18),(.neg 13),(.pos 11),(.pos 15)]),
   ((.exchange 18 14 2),[(.neg 18),(.neg 14),(.pos 17),(.pos 19)]),
   ((.exchange 19 1 4),[(.neg 19),(.neg 1),(.pos 13),(.pos 14)]),
   ((.exchange 19 2 4),[(.neg 19),(.neg 2),(.pos 13),(.pos 15)]),
   ((.exchange 19 3 4),[(.neg 19),(.neg 3),(.pos 14),(.pos 15)]),
   ((.exchange 19 5 3),[(.neg 19),(.neg 5),(.pos 16),(.pos 18)]),
   ((.exchange 19 6 3),[(.neg 19),(.neg 6),(.pos 17),(.pos 18)]),
   ((.exchange 19 10 3),[(.neg 19),(.neg 10),(.pos 16),(.pos 17)]),
   (.newPoint,[(.pos 10),(.pos 11),(.pos 12),(.pos 13),(.pos 14),(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 19)]),
   ((.excluded 0),[(.neg 19),(.neg 18),(.neg 17),(.neg 15),(.neg 14),(.pos 10),(.pos 11),(.pos 12),(.pos 13),(.pos 16)]),
   ((.excluded 1),[(.neg 19),(.neg 18),(.neg 16),(.neg 15),(.neg 13),(.pos 10),(.pos 11),(.pos 12),(.pos 14),(.pos 17)]),
   ((.excluded 2),[(.neg 19),(.neg 17),(.neg 16),(.neg 14),(.neg 13),(.pos 10),(.pos 11),(.pos 12),(.pos 15),(.pos 18)]),
   ((.excluded 3),[(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.neg 14),(.neg 13),(.pos 10),(.pos 11),(.pos 12),(.pos 19)]),
   ((.excluded 4),[(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.neg 14),(.neg 13),(.pos 10),(.pos 11),(.pos 12)]),
   ((.excluded 5),[(.neg 18),(.neg 17),(.neg 16),(.neg 12),(.neg 11),(.neg 10),(.pos 13),(.pos 14),(.pos 15),(.pos 19)]),
   ((.excluded 6),[(.neg 15),(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.pos 16),(.pos 17),(.pos 18),(.pos 19)]),
   ((.excluded 7),[(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.pos 19)]),
   ((.excluded 8),[(.neg 19),(.neg 18),(.neg 16),(.neg 15),(.neg 14),(.neg 12),(.neg 11),(.neg 10),(.pos 13),(.pos 17)]),
   ((.excluded 9),[(.neg 19),(.neg 17),(.neg 16),(.neg 15),(.neg 14),(.neg 12),(.neg 11),(.neg 10),(.pos 13),(.pos 18)]),
   ((.excluded 10),[(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.neg 14),(.neg 12),(.neg 11),(.neg 10),(.pos 13)]),
   ((.excluded 11),[(.neg 19),(.neg 18),(.neg 16),(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.pos 15),(.pos 17)]),
   ((.excluded 12),[(.neg 19),(.neg 18),(.neg 16),(.neg 15),(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.pos 17)]),
   ((.excluded 13),[(.neg 19),(.neg 18),(.neg 17),(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.pos 15),(.pos 16)]),
   ((.excluded 14),[(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.pos 15)]),
   ((.excluded 15),[(.neg 19),(.neg 18),(.neg 17),(.neg 15),(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.pos 14),(.pos 16)]),
   ((.excluded 16),[(.neg 19),(.neg 18),(.neg 17),(.neg 15),(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.pos 16)]),
   ((.excluded 17),[(.neg 19),(.neg 17),(.neg 16),(.neg 15),(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.pos 14),(.pos 18)]),
   ((.excluded 18),[(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.pos 14)]),
   ((.excluded 19),[(.neg 19),(.neg 17),(.neg 16),(.neg 15),(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.pos 18)]),
   ((.excluded 20),[(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 10)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (5 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 21,
    let w : Fin 21 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 6 3 ∧
      ValidWitness 6 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 6 3 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C7

/- Source: MatroidCatalogue/Cases/N6R3C7Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C7

noncomputable def certificates : List (Origin 20 21 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (5 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 21,
    target w < MatroidCatalogue.count 6 3 ∧
      ValidWitness 6 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 6 3 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 21) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 6) 3)
    (hold : M.bases.filter ((5 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 6 3, IsomorphicWithin 6 M.bases B := by
  apply extension_covered_of_certificate (n:=5) (r:=3) (by decide)
    catalogue old U newIndex models certificates
    N6R3.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N6R3C7.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N6R3C7.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 6 3 (target w),family_mem 6 3 (target w) hw.1,?_⟩
    exact validWitness_sound 6 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C7

