module
public import MatroidCatalogue.Definitions
public import MatroidCases.N7R2C1
import all MatroidCases.N7R2C1
public import MatroidCases.N7R2C2
import all MatroidCases.N7R2C2
public import MatroidCases.N7R2C3
import all MatroidCases.N7R2C3
public import MatroidCases.N7R2C4
import all MatroidCases.N7R2C4
public import MatroidCases.N7R2C5
import all MatroidCases.N7R2C5
public import MatroidCases.N7R2C6
import all MatroidCases.N7R2C6
public import MatroidCases.N7R2C7
import all MatroidCases.N7R2C7
public import MatroidCases.N7R2C8
import all MatroidCases.N7R2C8

@[expose] public section
noncomputable section

/- Source: MatroidCatalogue/Cases/N7R2C1Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C1

abbrev U := N7R2.grid
noncomputable def old : Finset (Finset (Fin 8)) := N6R2.family 1
noncomputable def newIndexTree : Table ℕ := (.node 3 (.node 1 (.leaf 15) (.node 2 (.leaf 16) (.leaf 17))) (.node 4 (.leaf 18) (.node 5 (.leaf 19) (.leaf 20))))
noncomputable def newIndex (i : Fin 6) : Fin 21 := Fin.ofNat 21 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 1 (.leaf (48,1,15947400)) (.node 2 (.leaf (15,3,16434824)) (.leaf (63,4,16434824))))

noncomputable def models (i : Fin 3) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 3) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 3) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 21, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (6 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 21, (6 : Fin 8) ∈ U i → ∃ j : Fin 6, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C1

/- Source: MatroidCatalogue/Cases/N7R2C1Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C1


noncomputable def certificates_0 : List (Origin 21 3 × List Sat.Literal) :=
  [((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.neg 2)]),
   ((.fixed 3),[(.neg 3)]),
   ((.fixed 4),[(.neg 4)]),
   ((.fixed 5),[(.neg 5)]),
   ((.fixed 6),[(.pos 6)]),
   ((.fixed 7),[(.pos 7)]),
   ((.fixed 8),[(.pos 8)]),
   ((.fixed 9),[(.pos 9)]),
   ((.fixed 10),[(.pos 10)]),
   ((.fixed 14),[(.neg 14)]),
   ((.exchange 6 17 4),[(.neg 17),(.neg 6),(.pos 1),(.pos 15)]),
   ((.exchange 6 18 4),[(.neg 18),(.neg 6),(.pos 3),(.pos 15)]),
   ((.exchange 6 20 0),[(.neg 20),(.neg 6),(.pos 14),(.pos 19)]),
   ((.exchange 7 17 4),[(.neg 17),(.neg 7),(.pos 2),(.pos 16)]),
   ((.exchange 7 18 4),[(.neg 18),(.neg 7),(.pos 4),(.pos 16)]),
   ((.exchange 8 15 4),[(.neg 15),(.neg 8),(.pos 1),(.pos 17)]),
   ((.exchange 8 16 4),[(.neg 16),(.neg 8),(.pos 2),(.pos 17)]),
   ((.exchange 8 18 4),[(.neg 18),(.neg 8),(.pos 5),(.pos 17)]),
   ((.exchange 9 15 4),[(.neg 15),(.neg 9),(.pos 3),(.pos 18)]),
   ((.exchange 9 16 4),[(.neg 16),(.neg 9),(.pos 4),(.pos 18)]),
   ((.exchange 9 17 4),[(.neg 17),(.neg 9),(.pos 5),(.pos 18)]),
   ((.exchange 10 19 0),[(.neg 19),(.neg 10),(.pos 14),(.pos 20)]),
   (.newPoint,[(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 19),(.pos 20)]),
   ((.excluded 0),[(.neg 20),(.neg 19),(.pos 15),(.pos 16),(.pos 17),(.pos 18)]),
   ((.excluded 1),[(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 20)]),
   ((.excluded 2),[(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 3,
    let w : Fin 3 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 7 2 ∧
      ValidWitness 7 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 7 2 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C1

/- Source: MatroidCatalogue/Cases/N7R2C1Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C1

noncomputable def certificates : List (Origin 21 3 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 3,
    target w < MatroidCatalogue.count 7 2 ∧
      ValidWitness 7 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 7 2 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 3) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 7) 2)
    (hold : M.bases.filter ((6 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 7 2, IsomorphicWithin 7 M.bases B := by
  apply extension_covered_of_certificate (n:=6) (r:=2) (by decide)
    catalogue old U newIndex models certificates
    N7R2.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N7R2C1.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N7R2C1.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 7 2 (target w),family_mem 7 2 (target w) hw.1,?_⟩
    exact validWitness_sound 7 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C1

/- Source: MatroidCatalogue/Cases/N7R2C2Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C2

abbrev U := N7R2.grid
noncomputable def old : Finset (Finset (Fin 8)) := N6R2.family 2
noncomputable def newIndexTree : Table ℕ := (.node 3 (.node 1 (.leaf 15) (.node 2 (.leaf 16) (.leaf 17))) (.node 4 (.leaf 18) (.node 5 (.leaf 19) (.leaf 20))))
noncomputable def newIndex (i : Fin 6) : Fin 21 := Fin.ofNat 21 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 2 (.node 1 (.leaf (48,2,15947400)) (.leaf (47,4,16205448))) (.node 3 (.leaf (31,4,16148104)) (.leaf (63,5,16434824))))

noncomputable def models (i : Fin 4) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 4) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 4) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 21, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (6 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 21, (6 : Fin 8) ∈ U i → ∃ j : Fin 6, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C2

/- Source: MatroidCatalogue/Cases/N7R2C2Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C2


noncomputable def certificates_0 : List (Origin 21 4 × List Sat.Literal) :=
  [((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.neg 2)]),
   ((.fixed 5),[(.neg 5)]),
   ((.fixed 6),[(.pos 6)]),
   ((.fixed 7),[(.pos 7)]),
   ((.fixed 8),[(.pos 8)]),
   ((.fixed 9),[(.pos 9)]),
   ((.fixed 10),[(.pos 10)]),
   ((.fixed 11),[(.pos 11)]),
   ((.fixed 12),[(.pos 12)]),
   ((.fixed 13),[(.pos 13)]),
   ((.fixed 14),[(.pos 14)]),
   ((.exchange 6 17 4),[(.neg 17),(.neg 6),(.pos 1),(.pos 15)]),
   ((.exchange 7 17 4),[(.neg 17),(.neg 7),(.pos 2),(.pos 16)]),
   ((.exchange 8 15 4),[(.neg 15),(.neg 8),(.pos 1),(.pos 17)]),
   ((.exchange 8 16 4),[(.neg 16),(.neg 8),(.pos 2),(.pos 17)]),
   ((.exchange 8 18 4),[(.neg 18),(.neg 8),(.pos 5),(.pos 17)]),
   ((.exchange 9 17 4),[(.neg 17),(.neg 9),(.pos 5),(.pos 18)]),
   ((.exchange 17 14 2),[(.neg 17),(.neg 14),(.pos 19),(.pos 20)]),
   ((.exchange 19 10 4),[(.neg 19),(.neg 10),(.pos 15),(.pos 20)]),
   ((.exchange 19 11 4),[(.neg 19),(.neg 11),(.pos 16),(.pos 20)]),
   ((.exchange 19 12 4),[(.neg 19),(.neg 12),(.pos 17),(.pos 20)]),
   ((.exchange 19 13 4),[(.neg 19),(.neg 13),(.pos 18),(.pos 20)]),
   ((.exchange 20 8 5),[(.neg 20),(.neg 8),(.pos 17),(.pos 19)]),
   (.newPoint,[(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 19),(.pos 20)]),
   ((.excluded 0),[(.neg 20),(.neg 19),(.pos 15),(.pos 16),(.pos 17),(.pos 18)]),
   ((.excluded 1),[(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19)]),
   ((.excluded 2),[(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20)]),
   ((.excluded 3),[(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 4,
    let w : Fin 4 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 7 2 ∧
      ValidWitness 7 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 7 2 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C2

/- Source: MatroidCatalogue/Cases/N7R2C2Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C2

noncomputable def certificates : List (Origin 21 4 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 4,
    target w < MatroidCatalogue.count 7 2 ∧
      ValidWitness 7 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 7 2 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 4) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 7) 2)
    (hold : M.bases.filter ((6 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 7 2, IsomorphicWithin 7 M.bases B := by
  apply extension_covered_of_certificate (n:=6) (r:=2) (by decide)
    catalogue old U newIndex models certificates
    N7R2.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N7R2C2.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N7R2C2.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 7 2 (target w),family_mem 7 2 (target w) hw.1,?_⟩
    exact validWitness_sound 7 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C2

/- Source: MatroidCatalogue/Cases/N7R2C3Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C3

abbrev U := N7R2.grid
noncomputable def old : Finset (Finset (Fin 8)) := N6R2.family 3
noncomputable def newIndexTree : Table ℕ := (.node 3 (.node 1 (.leaf 15) (.node 2 (.leaf 16) (.leaf 17))) (.node 4 (.leaf 18) (.node 5 (.leaf 19) (.leaf 20))))
noncomputable def newIndex (i : Fin 6) : Fin 21 := Fin.ofNat 21 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 1 (.leaf (56,3,15685768)) (.node 2 (.leaf (7,3,15536556)) (.leaf (63,6,16434824))))

noncomputable def models (i : Fin 3) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 3) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 3) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 21, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (6 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 21, (6 : Fin 8) ∈ U i → ∃ j : Fin 6, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C3

/- Source: MatroidCatalogue/Cases/N7R2C3Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C3


noncomputable def certificates_0 : List (Origin 21 3 × List Sat.Literal) :=
  [((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.neg 2)]),
   ((.fixed 3),[(.pos 3)]),
   ((.fixed 4),[(.pos 4)]),
   ((.fixed 5),[(.pos 5)]),
   ((.fixed 6),[(.pos 6)]),
   ((.fixed 9),[(.neg 9)]),
   ((.fixed 10),[(.pos 10)]),
   ((.fixed 14),[(.neg 14)]),
   ((.exchange 3 17 3),[(.neg 17),(.neg 3),(.pos 1),(.pos 15)]),
   ((.exchange 3 19 0),[(.neg 19),(.neg 3),(.pos 9),(.pos 18)]),
   ((.exchange 4 17 3),[(.neg 17),(.neg 4),(.pos 2),(.pos 16)]),
   ((.exchange 5 15 3),[(.neg 15),(.neg 5),(.pos 1),(.pos 17)]),
   ((.exchange 5 16 3),[(.neg 16),(.neg 5),(.pos 2),(.pos 17)]),
   ((.exchange 6 18 0),[(.neg 18),(.neg 6),(.pos 9),(.pos 19)]),
   ((.exchange 6 20 0),[(.neg 20),(.neg 6),(.pos 14),(.pos 19)]),
   ((.exchange 10 19 0),[(.neg 19),(.neg 10),(.pos 14),(.pos 20)]),
   (.newPoint,[(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 19),(.pos 20)]),
   ((.excluded 0),[(.neg 20),(.neg 19),(.neg 18),(.pos 15),(.pos 16),(.pos 17)]),
   ((.excluded 1),[(.neg 17),(.neg 16),(.neg 15),(.pos 18),(.pos 19),(.pos 20)]),
   ((.excluded 2),[(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 3,
    let w : Fin 3 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 7 2 ∧
      ValidWitness 7 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 7 2 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C3

/- Source: MatroidCatalogue/Cases/N7R2C3Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C3

noncomputable def certificates : List (Origin 21 3 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 3,
    target w < MatroidCatalogue.count 7 2 ∧
      ValidWitness 7 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 7 2 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 3) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 7) 2)
    (hold : M.bases.filter ((6 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 7 2, IsomorphicWithin 7 M.bases B := by
  apply extension_covered_of_certificate (n:=6) (r:=2) (by decide)
    catalogue old U newIndex models certificates
    N7R2.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N7R2C3.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N7R2C3.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 7 2 (target w),family_mem 7 2 (target w) hw.1,?_⟩
    exact validWitness_sound 7 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C3

/- Source: MatroidCatalogue/Cases/N7R2C4Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C4

abbrev U := N7R2.grid
noncomputable def old : Finset (Finset (Fin 8)) := N6R2.family 4
noncomputable def newIndexTree : Table ℕ := (.node 3 (.node 1 (.leaf 15) (.node 2 (.leaf 16) (.leaf 17))) (.node 4 (.leaf 18) (.node 5 (.leaf 19) (.leaf 20))))
noncomputable def newIndex (i : Fin 6) : Fin 21 := Fin.ofNat 21 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 2 (.node 1 (.leaf (56,4,15685768)) (.leaf (31,7,16148104))) (.node 3 (.leaf (39,6,16205448)) (.leaf (63,8,16434824))))

noncomputable def models (i : Fin 4) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 4) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 4) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 21, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (6 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 21, (6 : Fin 8) ∈ U i → ∃ j : Fin 6, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C4

/- Source: MatroidCatalogue/Cases/N7R2C4Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C4


noncomputable def certificates_0 : List (Origin 21 4 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.neg 2)]),
   ((.fixed 3),[(.pos 3)]),
   ((.fixed 4),[(.pos 4)]),
   ((.fixed 5),[(.pos 5)]),
   ((.fixed 6),[(.pos 6)]),
   ((.fixed 9),[(.neg 9)]),
   ((.fixed 10),[(.pos 10)]),
   ((.fixed 11),[(.pos 11)]),
   ((.fixed 12),[(.pos 12)]),
   ((.fixed 13),[(.pos 13)]),
   ((.exchange 3 16 3),[(.neg 16),(.neg 3),(.pos 0),(.pos 15)]),
   ((.exchange 3 17 3),[(.neg 17),(.neg 3),(.pos 1),(.pos 15)]),
   ((.exchange 3 19 0),[(.neg 19),(.neg 3),(.pos 9),(.pos 18)]),
   ((.exchange 4 15 3),[(.neg 15),(.neg 4),(.pos 0),(.pos 16)]),
   ((.exchange 4 17 3),[(.neg 17),(.neg 4),(.pos 2),(.pos 16)]),
   ((.exchange 5 15 3),[(.neg 15),(.neg 5),(.pos 1),(.pos 17)]),
   ((.exchange 5 16 3),[(.neg 16),(.neg 5),(.pos 2),(.pos 17)]),
   ((.exchange 6 18 0),[(.neg 18),(.neg 6),(.pos 9),(.pos 19)]),
   ((.exchange 17 13 2),[(.neg 17),(.neg 13),(.pos 18),(.pos 20)]),
   ((.exchange 18 10 3),[(.neg 18),(.neg 10),(.pos 15),(.pos 20)]),
   ((.exchange 18 11 3),[(.neg 18),(.neg 11),(.pos 16),(.pos 20)]),
   ((.exchange 18 12 3),[(.neg 18),(.neg 12),(.pos 17),(.pos 20)]),
   ((.exchange 20 5 5),[(.neg 20),(.neg 5),(.pos 17),(.pos 18)]),
   (.newPoint,[(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 19),(.pos 20)]),
   ((.excluded 0),[(.neg 20),(.neg 19),(.neg 18),(.pos 15),(.pos 16),(.pos 17)]),
   ((.excluded 1),[(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20)]),
   ((.excluded 2),[(.neg 20),(.neg 17),(.neg 16),(.neg 15),(.pos 18),(.pos 19)]),
   ((.excluded 3),[(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 4,
    let w : Fin 4 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 7 2 ∧
      ValidWitness 7 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 7 2 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C4

/- Source: MatroidCatalogue/Cases/N7R2C4Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C4

noncomputable def certificates : List (Origin 21 4 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 4,
    target w < MatroidCatalogue.count 7 2 ∧
      ValidWitness 7 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 7 2 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 4) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 7) 2)
    (hold : M.bases.filter ((6 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 7 2, IsomorphicWithin 7 M.bases B := by
  apply extension_covered_of_certificate (n:=6) (r:=2) (by decide)
    catalogue old U newIndex models certificates
    N7R2.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N7R2C4.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N7R2C4.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 7 2 (target w),family_mem 7 2 (target w) hw.1,?_⟩
    exact validWitness_sound 7 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C4

/- Source: MatroidCatalogue/Cases/N7R2C5Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C5

abbrev U := N7R2.grid
noncomputable def old : Finset (Finset (Fin 8)) := N6R2.family 5
noncomputable def newIndexTree : Table ℕ := (.node 3 (.node 1 (.leaf 15) (.node 2 (.leaf 16) (.leaf 17))) (.node 4 (.leaf 18) (.node 5 (.leaf 19) (.leaf 20))))
noncomputable def newIndex (i : Fin 6) : Fin 21 := Fin.ofNat 21 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 2 (.node 1 (.leaf (56,5,15685768)) (.leaf (55,8,15947400))) (.node 3 (.leaf (47,8,15940232)) (.node 4 (.leaf (31,8,15854216)) (.leaf (63,9,16434824)))))

noncomputable def models (i : Fin 5) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 5) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 5) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 21, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (6 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 21, (6 : Fin 8) ∈ U i → ∃ j : Fin 6, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C5

/- Source: MatroidCatalogue/Cases/N7R2C5Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C5


noncomputable def certificates_0 : List (Origin 21 5 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 3),[(.pos 3)]),
   ((.fixed 4),[(.pos 4)]),
   ((.fixed 5),[(.pos 5)]),
   ((.fixed 6),[(.pos 6)]),
   ((.fixed 9),[(.pos 9)]),
   ((.fixed 10),[(.pos 10)]),
   ((.fixed 13),[(.pos 13)]),
   ((.fixed 14),[(.pos 14)]),
   ((.exchange 3 16 3),[(.neg 16),(.neg 3),(.pos 0),(.pos 15)]),
   ((.exchange 3 17 3),[(.neg 17),(.neg 3),(.pos 1),(.pos 15)]),
   ((.exchange 4 15 3),[(.neg 15),(.neg 4),(.pos 0),(.pos 16)]),
   ((.exchange 5 15 3),[(.neg 15),(.neg 5),(.pos 1),(.pos 17)]),
   ((.exchange 17 13 2),[(.neg 17),(.neg 13),(.pos 18),(.pos 20)]),
   ((.exchange 17 14 2),[(.neg 17),(.neg 14),(.pos 19),(.pos 20)]),
   ((.exchange 18 6 3),[(.neg 18),(.neg 6),(.pos 15),(.pos 19)]),
   ((.exchange 18 10 3),[(.neg 18),(.neg 10),(.pos 15),(.pos 20)]),
   ((.exchange 19 5 4),[(.neg 19),(.neg 5),(.pos 17),(.pos 18)]),
   ((.exchange 20 9 5),[(.neg 20),(.neg 9),(.pos 18),(.pos 19)]),
   (.newPoint,[(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 19),(.pos 20)]),
   ((.excluded 0),[(.neg 20),(.neg 19),(.neg 18),(.pos 15),(.pos 16),(.pos 17)]),
   ((.excluded 1),[(.neg 20),(.neg 19),(.neg 17),(.neg 16),(.neg 15),(.pos 18)]),
   ((.excluded 2),[(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19)]),
   ((.excluded 3),[(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20)]),
   ((.excluded 4),[(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 5,
    let w : Fin 5 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 7 2 ∧
      ValidWitness 7 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 7 2 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C5

/- Source: MatroidCatalogue/Cases/N7R2C5Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C5

noncomputable def certificates : List (Origin 21 5 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 5,
    target w < MatroidCatalogue.count 7 2 ∧
      ValidWitness 7 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 7 2 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 5) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 7) 2)
    (hold : M.bases.filter ((6 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 7 2, IsomorphicWithin 7 M.bases B := by
  apply extension_covered_of_certificate (n:=6) (r:=2) (by decide)
    catalogue old U newIndex models certificates
    N7R2.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N7R2C5.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N7R2C5.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 7 2 (target w),family_mem 7 2 (target w) hw.1,?_⟩
    exact validWitness_sound 7 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C5

/- Source: MatroidCatalogue/Cases/N7R2C6Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C6

abbrev U := N7R2.grid
noncomputable def old : Finset (Finset (Fin 8)) := N6R2.family 6
noncomputable def newIndexTree : Table ℕ := (.node 3 (.node 1 (.leaf 15) (.node 2 (.leaf 16) (.leaf 17))) (.node 4 (.leaf 18) (.node 5 (.leaf 19) (.leaf 20))))
noncomputable def newIndex (i : Fin 6) : Fin 21 := Fin.ofNat 21 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 2 (.node 1 (.leaf (60,7,15387848)) (.leaf (51,7,15385139))) (.node 3 (.leaf (15,7,15239987)) (.leaf (63,10,16434824))))

noncomputable def models (i : Fin 4) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 4) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 4) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 21, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (6 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 21, (6 : Fin 8) ∈ U i → ∃ j : Fin 6, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C6

/- Source: MatroidCatalogue/Cases/N7R2C6Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C6


noncomputable def certificates_0 : List (Origin 21 4 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.pos 1)]),
   ((.fixed 2),[(.pos 2)]),
   ((.fixed 3),[(.pos 3)]),
   ((.fixed 4),[(.pos 4)]),
   ((.fixed 5),[(.neg 5)]),
   ((.fixed 6),[(.pos 6)]),
   ((.fixed 7),[(.pos 7)]),
   ((.fixed 8),[(.pos 8)]),
   ((.fixed 10),[(.pos 10)]),
   ((.fixed 14),[(.neg 14)]),
   ((.exchange 1 16 2),[(.neg 16),(.neg 1),(.pos 0),(.pos 15)]),
   ((.exchange 1 18 0),[(.neg 18),(.neg 1),(.pos 5),(.pos 17)]),
   ((.exchange 2 15 2),[(.neg 15),(.neg 2),(.pos 0),(.pos 16)]),
   ((.exchange 3 17 0),[(.neg 17),(.neg 3),(.pos 5),(.pos 18)]),
   ((.exchange 6 20 0),[(.neg 20),(.neg 6),(.pos 14),(.pos 19)]),
   ((.exchange 10 19 0),[(.neg 19),(.neg 10),(.pos 14),(.pos 20)]),
   ((.exchange 15 8 0),[(.neg 15),(.neg 8),(.pos 17),(.pos 19)]),
   ((.exchange 16 8 1),[(.neg 16),(.neg 8),(.pos 17),(.pos 19)]),
   ((.exchange 17 6 2),[(.neg 17),(.neg 6),(.pos 15),(.pos 19)]),
   ((.exchange 17 7 2),[(.neg 17),(.neg 7),(.pos 16),(.pos 19)]),
   ((.exchange 20 3 5),[(.neg 20),(.neg 3),(.pos 15),(.pos 18)]),
   ((.exchange 20 4 5),[(.neg 20),(.neg 4),(.pos 16),(.pos 18)]),
   (.newPoint,[(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 19),(.pos 20)]),
   ((.excluded 0),[(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.pos 15),(.pos 16)]),
   ((.excluded 1),[(.neg 20),(.neg 19),(.neg 16),(.neg 15),(.pos 17),(.pos 18)]),
   ((.excluded 2),[(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19),(.pos 20)]),
   ((.excluded 3),[(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 4,
    let w : Fin 4 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 7 2 ∧
      ValidWitness 7 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 7 2 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C6

/- Source: MatroidCatalogue/Cases/N7R2C6Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C6

noncomputable def certificates : List (Origin 21 4 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 4,
    target w < MatroidCatalogue.count 7 2 ∧
      ValidWitness 7 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 7 2 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 4) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 7) 2)
    (hold : M.bases.filter ((6 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 7 2, IsomorphicWithin 7 M.bases B := by
  apply extension_covered_of_certificate (n:=6) (r:=2) (by decide)
    catalogue old U newIndex models certificates
    N7R2.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N7R2C6.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N7R2C6.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 7 2 (target w),family_mem 7 2 (target w) hw.1,?_⟩
    exact validWitness_sound 7 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C6

/- Source: MatroidCatalogue/Cases/N7R2C7Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C7

abbrev U := N7R2.grid
noncomputable def old : Finset (Finset (Fin 8)) := N6R2.family 7
noncomputable def newIndexTree : Table ℕ := (.node 3 (.node 1 (.leaf 15) (.node 2 (.leaf 16) (.leaf 17))) (.node 4 (.leaf 18) (.node 5 (.leaf 19) (.leaf 20))))
noncomputable def newIndex (i : Fin 6) : Fin 21 := Fin.ofNat 21 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 2 (.node 1 (.leaf (60,8,15423688)) (.leaf (47,10,16205448))) (.node 3 (.leaf (31,10,16148104)) (.node 4 (.leaf (51,8,15421987)) (.leaf (63,11,16434824)))))

noncomputable def models (i : Fin 5) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 5) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 5) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 21, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (6 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 21, (6 : Fin 8) ∈ U i → ∃ j : Fin 6, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C7

/- Source: MatroidCatalogue/Cases/N7R2C7Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C7


noncomputable def certificates_0 : List (Origin 21 5 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.pos 1)]),
   ((.fixed 2),[(.pos 2)]),
   ((.fixed 3),[(.pos 3)]),
   ((.fixed 5),[(.neg 5)]),
   ((.fixed 6),[(.pos 6)]),
   ((.fixed 8),[(.pos 8)]),
   ((.fixed 9),[(.pos 9)]),
   ((.fixed 10),[(.pos 10)]),
   ((.fixed 12),[(.pos 12)]),
   ((.fixed 13),[(.pos 13)]),
   ((.fixed 14),[(.pos 14)]),
   ((.exchange 1 16 2),[(.neg 16),(.neg 1),(.pos 0),(.pos 15)]),
   ((.exchange 1 18 0),[(.neg 18),(.neg 1),(.pos 5),(.pos 17)]),
   ((.exchange 2 15 2),[(.neg 15),(.neg 2),(.pos 0),(.pos 16)]),
   ((.exchange 3 17 0),[(.neg 17),(.neg 3),(.pos 5),(.pos 18)]),
   ((.exchange 16 8 1),[(.neg 16),(.neg 8),(.pos 17),(.pos 19)]),
   ((.exchange 16 12 1),[(.neg 16),(.neg 12),(.pos 17),(.pos 20)]),
   ((.exchange 16 13 1),[(.neg 16),(.neg 13),(.pos 18),(.pos 20)]),
   ((.exchange 16 14 1),[(.neg 16),(.neg 14),(.pos 19),(.pos 20)]),
   ((.exchange 17 6 2),[(.neg 17),(.neg 6),(.pos 15),(.pos 19)]),
   ((.exchange 17 10 2),[(.neg 17),(.neg 10),(.pos 15),(.pos 20)]),
   ((.exchange 19 2 4),[(.neg 19),(.neg 2),(.pos 16),(.pos 17)]),
   ((.exchange 20 2 5),[(.neg 20),(.neg 2),(.pos 16),(.pos 17)]),
   ((.exchange 20 9 5),[(.neg 20),(.neg 9),(.pos 18),(.pos 19)]),
   (.newPoint,[(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 19),(.pos 20)]),
   ((.excluded 0),[(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.pos 15),(.pos 16)]),
   ((.excluded 1),[(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19)]),
   ((.excluded 2),[(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20)]),
   ((.excluded 3),[(.neg 20),(.neg 19),(.neg 16),(.neg 15),(.pos 17),(.pos 18)]),
   ((.excluded 4),[(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 5,
    let w : Fin 5 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 7 2 ∧
      ValidWitness 7 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 7 2 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C7

/- Source: MatroidCatalogue/Cases/N7R2C7Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C7

noncomputable def certificates : List (Origin 21 5 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 5,
    target w < MatroidCatalogue.count 7 2 ∧
      ValidWitness 7 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 7 2 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 5) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 7) 2)
    (hold : M.bases.filter ((6 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 7 2, IsomorphicWithin 7 M.bases B := by
  apply extension_covered_of_certificate (n:=6) (r:=2) (by decide)
    catalogue old U newIndex models certificates
    N7R2.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N7R2C7.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N7R2C7.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 7 2 (target w),family_mem 7 2 (target w) hw.1,?_⟩
    exact validWitness_sound 7 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C7

/- Source: MatroidCatalogue/Cases/N7R2C8Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C8

abbrev U := N7R2.grid
noncomputable def old : Finset (Finset (Fin 8)) := N6R2.family 8
noncomputable def newIndexTree : Table ℕ := (.node 3 (.node 1 (.leaf 15) (.node 2 (.leaf 16) (.leaf 17))) (.node 4 (.leaf 18) (.node 5 (.leaf 19) (.leaf 20))))
noncomputable def newIndex (i : Fin 6) : Fin 21 := Fin.ofNat 21 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 3 (.node 1 (.leaf (60,9,15423688)) (.node 2 (.leaf (59,11,15685768)) (.leaf (55,11,15684872)))) (.node 4 (.leaf (47,11,15674120)) (.node 5 (.leaf (31,11,15559432)) (.leaf (63,12,16434824)))))

noncomputable def models (i : Fin 6) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 6) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 6) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 21, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (6 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 21, (6 : Fin 8) ∈ U i → ∃ j : Fin 6, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C8

/- Source: MatroidCatalogue/Cases/N7R2C8Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C8


noncomputable def certificates_0 : List (Origin 21 6 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.pos 1)]),
   ((.fixed 2),[(.pos 2)]),
   ((.fixed 3),[(.pos 3)]),
   ((.fixed 5),[(.pos 5)]),
   ((.fixed 6),[(.pos 6)]),
   ((.fixed 8),[(.pos 8)]),
   ((.fixed 9),[(.pos 9)]),
   ((.fixed 10),[(.pos 10)]),
   ((.fixed 12),[(.pos 12)]),
   ((.fixed 13),[(.pos 13)]),
   ((.fixed 14),[(.pos 14)]),
   ((.exchange 1 16 2),[(.neg 16),(.neg 1),(.pos 0),(.pos 15)]),
   ((.exchange 2 15 2),[(.neg 15),(.neg 2),(.pos 0),(.pos 16)]),
   ((.exchange 15 5 0),[(.neg 15),(.neg 5),(.pos 17),(.pos 18)]),
   ((.exchange 16 12 1),[(.neg 16),(.neg 12),(.pos 17),(.pos 20)]),
   ((.exchange 16 13 1),[(.neg 16),(.neg 13),(.pos 18),(.pos 20)]),
   ((.exchange 16 14 1),[(.neg 16),(.neg 14),(.pos 19),(.pos 20)]),
   ((.exchange 17 3 2),[(.neg 17),(.neg 3),(.pos 15),(.pos 18)]),
   ((.exchange 17 6 2),[(.neg 17),(.neg 6),(.pos 15),(.pos 19)]),
   ((.exchange 17 10 2),[(.neg 17),(.neg 10),(.pos 15),(.pos 20)]),
   ((.exchange 18 2 3),[(.neg 18),(.neg 2),(.pos 16),(.pos 17)]),
   ((.exchange 19 5 4),[(.neg 19),(.neg 5),(.pos 17),(.pos 18)]),
   ((.exchange 20 5 5),[(.neg 20),(.neg 5),(.pos 17),(.pos 18)]),
   ((.exchange 20 8 5),[(.neg 20),(.neg 8),(.pos 17),(.pos 19)]),
   ((.exchange 20 9 5),[(.neg 20),(.neg 9),(.pos 18),(.pos 19)]),
   (.newPoint,[(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 19),(.pos 20)]),
   ((.excluded 0),[(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.pos 15),(.pos 16)]),
   ((.excluded 1),[(.neg 20),(.neg 19),(.neg 18),(.neg 16),(.neg 15),(.pos 17)]),
   ((.excluded 2),[(.neg 20),(.neg 19),(.neg 17),(.neg 16),(.neg 15),(.pos 18)]),
   ((.excluded 3),[(.neg 20),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 19)]),
   ((.excluded 4),[(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.pos 20)]),
   ((.excluded 5),[(.neg 20),(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 6,
    let w : Fin 6 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 7 2 ∧
      ValidWitness 7 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 7 2 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C8

/- Source: MatroidCatalogue/Cases/N7R2C8Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C8

noncomputable def certificates : List (Origin 21 6 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (6 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 6,
    target w < MatroidCatalogue.count 7 2 ∧
      ValidWitness 7 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 7 2 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 6) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 7) 2)
    (hold : M.bases.filter ((6 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 7 2, IsomorphicWithin 7 M.bases B := by
  apply extension_covered_of_certificate (n:=6) (r:=2) (by decide)
    catalogue old U newIndex models certificates
    N7R2.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N7R2C8.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N7R2C8.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 7 2 (target w),family_mem 7 2 (target w) hw.1,?_⟩
    exact validWitness_sound 7 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N7R2C8

