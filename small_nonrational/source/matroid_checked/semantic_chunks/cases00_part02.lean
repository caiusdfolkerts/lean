module
public import MatroidCatalogue.Definitions
public import MatroidCases.N6R1C0
import all MatroidCases.N6R1C0
public import MatroidCases.N6R2C0
import all MatroidCases.N6R2C0
public import MatroidCases.N6R2C1
import all MatroidCases.N6R2C1
public import MatroidCases.N6R2C2
import all MatroidCases.N6R2C2
public import MatroidCases.N6R2C3
import all MatroidCases.N6R2C3
public import MatroidCases.N6R2C4
import all MatroidCases.N6R2C4
public import MatroidCases.N6R2C5
import all MatroidCases.N6R2C5
public import MatroidCases.N6R3C0
import all MatroidCases.N6R3C0

@[expose] public section
noncomputable section

/- Source: MatroidCatalogue/Cases/N6R1C0Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R1C0

abbrev U := N6R1.grid
noncomputable def old : Finset (Finset (Fin 8)) := N5R1.family 0
noncomputable def newIndexTree : Table ℕ := (.leaf 5)
noncomputable def newIndex (i : Fin 1) : Fin 6 := Fin.ofNat 6 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.leaf (1,0,16434824))

noncomputable def models (i : Fin 1) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 1) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 1) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 6, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (5 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 6, (5 : Fin 8) ∈ U i → ∃ j : Fin 1, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N6R1C0

/- Source: MatroidCatalogue/Cases/N6R1C0Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R1C0


noncomputable def certificates_0 : List (Origin 6 1 × List Sat.Literal) :=
  [(.newPoint,[(.pos 5)]),
   ((.excluded 0),[(.neg 5)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (5 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 1,
    let w : Fin 1 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 6 1 ∧
      ValidWitness 6 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 6 1 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N6R1C0

/- Source: MatroidCatalogue/Cases/N6R1C0Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R1C0

noncomputable def certificates : List (Origin 6 1 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (5 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 1,
    target w < MatroidCatalogue.count 6 1 ∧
      ValidWitness 6 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 6 1 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 1) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 6) 1)
    (hold : M.bases.filter ((5 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 6 1, IsomorphicWithin 6 M.bases B := by
  apply extension_covered_of_certificate (n:=5) (r:=1) (by decide)
    catalogue old U newIndex models certificates
    N6R1.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N6R1C0.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N6R1C0.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 6 1 (target w),family_mem 6 1 (target w) hw.1,?_⟩
    exact validWitness_sound 6 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N6R1C0

/- Source: MatroidCatalogue/Cases/N6R2C0Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R2C0

abbrev U := N6R2.grid
noncomputable def old : Finset (Finset (Fin 8)) := N5R2.family 0
noncomputable def newIndexTree : Table ℕ := (.node 2 (.node 1 (.leaf 10) (.leaf 11)) (.node 3 (.leaf 12) (.node 4 (.leaf 13) (.leaf 14))))
noncomputable def newIndex (i : Fin 5) : Fin 15 := Fin.ofNat 15 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 1 (.leaf (16,0,16406152)) (.node 2 (.leaf (15,1,16434824)) (.leaf (31,2,16434824))))

noncomputable def models (i : Fin 3) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 3) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 3) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 15, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (5 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 15, (5 : Fin 8) ∈ U i → ∃ j : Fin 5, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N6R2C0

/- Source: MatroidCatalogue/Cases/N6R2C0Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R2C0


noncomputable def certificates_0 : List (Origin 15 3 × List Sat.Literal) :=
  [((.fixed 3),[(.neg 3)]),
   ((.fixed 4),[(.neg 4)]),
   ((.fixed 5),[(.neg 5)]),
   ((.fixed 6),[(.pos 6)]),
   ((.fixed 7),[(.pos 7)]),
   ((.fixed 8),[(.pos 8)]),
   ((.fixed 9),[(.pos 9)]),
   ((.exchange 6 13 4),[(.neg 13),(.neg 6),(.pos 3),(.pos 10)]),
   ((.exchange 7 13 4),[(.neg 13),(.neg 7),(.pos 4),(.pos 11)]),
   ((.exchange 8 13 4),[(.neg 13),(.neg 8),(.pos 5),(.pos 12)]),
   ((.exchange 9 10 4),[(.neg 10),(.neg 9),(.pos 3),(.pos 13)]),
   ((.exchange 9 11 4),[(.neg 11),(.neg 9),(.pos 4),(.pos 13)]),
   ((.exchange 9 12 4),[(.neg 12),(.neg 9),(.pos 5),(.pos 13)]),
   (.newPoint,[(.pos 10),(.pos 11),(.pos 12),(.pos 13),(.pos 14)]),
   ((.excluded 0),[(.neg 14),(.pos 10),(.pos 11),(.pos 12),(.pos 13)]),
   ((.excluded 1),[(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.pos 14)]),
   ((.excluded 2),[(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 10)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (5 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 3,
    let w : Fin 3 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 6 2 ∧
      ValidWitness 6 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 6 2 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N6R2C0

/- Source: MatroidCatalogue/Cases/N6R2C0Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R2C0

noncomputable def certificates : List (Origin 15 3 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (5 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 3,
    target w < MatroidCatalogue.count 6 2 ∧
      ValidWitness 6 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 6 2 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 3) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 6) 2)
    (hold : M.bases.filter ((5 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 6 2, IsomorphicWithin 6 M.bases B := by
  apply extension_covered_of_certificate (n:=5) (r:=2) (by decide)
    catalogue old U newIndex models certificates
    N6R2.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N6R2C0.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N6R2C0.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 6 2 (target w),family_mem 6 2 (target w) hw.1,?_⟩
    exact validWitness_sound 6 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N6R2C0

/- Source: MatroidCatalogue/Cases/N6R2C1Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R2C1

abbrev U := N6R2.grid
noncomputable def old : Finset (Finset (Fin 8)) := N5R2.family 1
noncomputable def newIndexTree : Table ℕ := (.node 2 (.node 1 (.leaf 10) (.leaf 11)) (.node 3 (.leaf 12) (.node 4 (.leaf 13) (.leaf 14))))
noncomputable def newIndex (i : Fin 5) : Fin 15 := Fin.ofNat 15 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 1 (.leaf (24,1,16373896)) (.node 2 (.leaf (7,3,16434824)) (.leaf (31,4,16434824))))

noncomputable def models (i : Fin 3) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 3) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 3) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 15, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (5 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 15, (5 : Fin 8) ∈ U i → ∃ j : Fin 5, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N6R2C1

/- Source: MatroidCatalogue/Cases/N6R2C1Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R2C1


noncomputable def certificates_0 : List (Origin 15 3 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.neg 2)]),
   ((.fixed 3),[(.pos 3)]),
   ((.fixed 4),[(.pos 4)]),
   ((.fixed 5),[(.pos 5)]),
   ((.fixed 6),[(.pos 6)]),
   ((.fixed 9),[(.neg 9)]),
   ((.exchange 3 11 3),[(.neg 11),(.neg 3),(.pos 0),(.pos 10)]),
   ((.exchange 3 12 3),[(.neg 12),(.neg 3),(.pos 1),(.pos 10)]),
   ((.exchange 3 14 0),[(.neg 14),(.neg 3),(.pos 9),(.pos 13)]),
   ((.exchange 4 10 3),[(.neg 10),(.neg 4),(.pos 0),(.pos 11)]),
   ((.exchange 4 12 3),[(.neg 12),(.neg 4),(.pos 2),(.pos 11)]),
   ((.exchange 5 10 3),[(.neg 10),(.neg 5),(.pos 1),(.pos 12)]),
   ((.exchange 5 11 3),[(.neg 11),(.neg 5),(.pos 2),(.pos 12)]),
   ((.exchange 6 13 0),[(.neg 13),(.neg 6),(.pos 9),(.pos 14)]),
   (.newPoint,[(.pos 10),(.pos 11),(.pos 12),(.pos 13),(.pos 14)]),
   ((.excluded 0),[(.neg 14),(.neg 13),(.pos 10),(.pos 11),(.pos 12)]),
   ((.excluded 1),[(.neg 12),(.neg 11),(.neg 10),(.pos 13),(.pos 14)]),
   ((.excluded 2),[(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 10)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (5 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 3,
    let w : Fin 3 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 6 2 ∧
      ValidWitness 6 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 6 2 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N6R2C1

/- Source: MatroidCatalogue/Cases/N6R2C1Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R2C1

noncomputable def certificates : List (Origin 15 3 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (5 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 3,
    target w < MatroidCatalogue.count 6 2 ∧
      ValidWitness 6 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 6 2 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 3) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 6) 2)
    (hold : M.bases.filter ((5 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 6 2, IsomorphicWithin 6 M.bases B := by
  apply extension_covered_of_certificate (n:=5) (r:=2) (by decide)
    catalogue old U newIndex models certificates
    N6R2.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N6R2C1.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N6R2C1.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 6 2 (target w),family_mem 6 2 (target w) hw.1,?_⟩
    exact validWitness_sound 6 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N6R2C1

/- Source: MatroidCatalogue/Cases/N6R2C2Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R2C2

abbrev U := N6R2.grid
noncomputable def old : Finset (Finset (Fin 8)) := N5R2.family 2
noncomputable def newIndexTree : Table ℕ := (.node 2 (.node 1 (.leaf 10) (.leaf 11)) (.node 3 (.leaf 12) (.node 4 (.leaf 13) (.leaf 14))))
noncomputable def newIndex (i : Fin 5) : Fin 15 := Fin.ofNat 15 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 2 (.node 1 (.leaf (24,2,16373896)) (.leaf (23,4,16406152))) (.node 3 (.leaf (15,4,16398984)) (.leaf (31,5,16434824))))

noncomputable def models (i : Fin 4) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 4) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 4) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 15, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (5 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 15, (5 : Fin 8) ∈ U i → ∃ j : Fin 5, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N6R2C2

/- Source: MatroidCatalogue/Cases/N6R2C2Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R2C2


noncomputable def certificates_0 : List (Origin 15 4 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 3),[(.pos 3)]),
   ((.fixed 4),[(.pos 4)]),
   ((.fixed 5),[(.pos 5)]),
   ((.fixed 6),[(.pos 6)]),
   ((.fixed 7),[(.pos 7)]),
   ((.fixed 8),[(.pos 8)]),
   ((.fixed 9),[(.pos 9)]),
   ((.exchange 3 11 3),[(.neg 11),(.neg 3),(.pos 0),(.pos 10)]),
   ((.exchange 3 12 3),[(.neg 12),(.neg 3),(.pos 1),(.pos 10)]),
   ((.exchange 4 10 3),[(.neg 10),(.neg 4),(.pos 0),(.pos 11)]),
   ((.exchange 5 10 3),[(.neg 10),(.neg 5),(.pos 1),(.pos 12)]),
   ((.exchange 10 9 0),[(.neg 10),(.neg 9),(.pos 13),(.pos 14)]),
   ((.exchange 13 6 3),[(.neg 13),(.neg 6),(.pos 10),(.pos 14)]),
   ((.exchange 13 7 3),[(.neg 13),(.neg 7),(.pos 11),(.pos 14)]),
   ((.exchange 13 8 3),[(.neg 13),(.neg 8),(.pos 12),(.pos 14)]),
   ((.exchange 14 3 4),[(.neg 14),(.neg 3),(.pos 10),(.pos 13)]),
   (.newPoint,[(.pos 10),(.pos 11),(.pos 12),(.pos 13),(.pos 14)]),
   ((.excluded 0),[(.neg 14),(.neg 13),(.pos 10),(.pos 11),(.pos 12)]),
   ((.excluded 1),[(.neg 14),(.neg 12),(.neg 11),(.neg 10),(.pos 13)]),
   ((.excluded 2),[(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.pos 14)]),
   ((.excluded 3),[(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 10)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (5 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 4,
    let w : Fin 4 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 6 2 ∧
      ValidWitness 6 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 6 2 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N6R2C2

/- Source: MatroidCatalogue/Cases/N6R2C2Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R2C2

noncomputable def certificates : List (Origin 15 4 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (5 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 4,
    target w < MatroidCatalogue.count 6 2 ∧
      ValidWitness 6 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 6 2 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 4) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 6) 2)
    (hold : M.bases.filter ((5 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 6 2, IsomorphicWithin 6 M.bases B := by
  apply extension_covered_of_certificate (n:=5) (r:=2) (by decide)
    catalogue old U newIndex models certificates
    N6R2.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N6R2C2.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N6R2C2.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 6 2 (target w),family_mem 6 2 (target w) hw.1,?_⟩
    exact validWitness_sound 6 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N6R2C2

/- Source: MatroidCatalogue/Cases/N6R2C3Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R2C3

abbrev U := N6R2.grid
noncomputable def old : Finset (Finset (Fin 8)) := N5R2.family 3
noncomputable def newIndexTree : Table ℕ := (.node 2 (.node 1 (.leaf 10) (.leaf 11)) (.node 3 (.leaf 12) (.node 4 (.leaf 13) (.leaf 14))))
noncomputable def newIndex (i : Fin 5) : Fin 15 := Fin.ofNat 15 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 2 (.node 1 (.leaf (28,4,16341192)) (.leaf (19,4,16339491))) (.node 3 (.leaf (15,6,16434824)) (.leaf (31,7,16434824))))

noncomputable def models (i : Fin 4) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 4) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 4) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 15, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (5 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 15, (5 : Fin 8) ∈ U i → ∃ j : Fin 5, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N6R2C3

/- Source: MatroidCatalogue/Cases/N6R2C3Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R2C3


noncomputable def certificates_0 : List (Origin 15 4 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.pos 1)]),
   ((.fixed 2),[(.pos 2)]),
   ((.fixed 3),[(.pos 3)]),
   ((.fixed 5),[(.neg 5)]),
   ((.fixed 6),[(.pos 6)]),
   ((.fixed 7),[(.pos 7)]),
   ((.fixed 8),[(.pos 8)]),
   ((.exchange 1 11 2),[(.neg 11),(.neg 1),(.pos 0),(.pos 10)]),
   ((.exchange 1 13 0),[(.neg 13),(.neg 1),(.pos 5),(.pos 12)]),
   ((.exchange 2 10 2),[(.neg 10),(.neg 2),(.pos 0),(.pos 11)]),
   ((.exchange 3 12 0),[(.neg 12),(.neg 3),(.pos 5),(.pos 13)]),
   ((.exchange 10 8 0),[(.neg 10),(.neg 8),(.pos 12),(.pos 14)]),
   ((.exchange 12 6 2),[(.neg 12),(.neg 6),(.pos 10),(.pos 14)]),
   ((.exchange 12 7 2),[(.neg 12),(.neg 7),(.pos 11),(.pos 14)]),
   ((.exchange 14 1 4),[(.neg 14),(.neg 1),(.pos 10),(.pos 12)]),
   (.newPoint,[(.pos 10),(.pos 11),(.pos 12),(.pos 13),(.pos 14)]),
   ((.excluded 0),[(.neg 14),(.neg 13),(.neg 12),(.pos 10),(.pos 11)]),
   ((.excluded 1),[(.neg 14),(.neg 11),(.neg 10),(.pos 12),(.pos 13)]),
   ((.excluded 2),[(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.pos 14)]),
   ((.excluded 3),[(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 10)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (5 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 4,
    let w : Fin 4 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 6 2 ∧
      ValidWitness 6 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 6 2 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N6R2C3

/- Source: MatroidCatalogue/Cases/N6R2C3Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R2C3

noncomputable def certificates : List (Origin 15 4 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (5 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 4,
    target w < MatroidCatalogue.count 6 2 ∧
      ValidWitness 6 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 6 2 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 4) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 6) 2)
    (hold : M.bases.filter ((5 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 6 2, IsomorphicWithin 6 M.bases B := by
  apply extension_covered_of_certificate (n:=5) (r:=2) (by decide)
    catalogue old U newIndex models certificates
    N6R2.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N6R2C3.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N6R2C3.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 6 2 (target w),family_mem 6 2 (target w) hw.1,?_⟩
    exact validWitness_sound 6 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N6R2C3

/- Source: MatroidCatalogue/Cases/N6R2C4Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R2C4

abbrev U := N6R2.grid
noncomputable def old : Finset (Finset (Fin 8)) := N5R2.family 4
noncomputable def newIndexTree : Table ℕ := (.node 2 (.node 1 (.leaf 10) (.leaf 11)) (.node 3 (.leaf 12) (.node 4 (.leaf 13) (.leaf 14))))
noncomputable def newIndex (i : Fin 5) : Fin 15 := Fin.ofNat 15 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 2 (.node 1 (.leaf (28,5,16341192)) (.leaf (27,7,16373896))) (.node 3 (.leaf (23,7,16373000)) (.node 4 (.leaf (15,7,16362248)) (.leaf (31,8,16434824)))))

noncomputable def models (i : Fin 5) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 5) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 5) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 15, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (5 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 15, (5 : Fin 8) ∈ U i → ∃ j : Fin 5, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N6R2C4

/- Source: MatroidCatalogue/Cases/N6R2C4Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R2C4


noncomputable def certificates_0 : List (Origin 15 5 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.pos 1)]),
   ((.fixed 2),[(.pos 2)]),
   ((.fixed 3),[(.pos 3)]),
   ((.fixed 5),[(.pos 5)]),
   ((.fixed 6),[(.pos 6)]),
   ((.fixed 8),[(.pos 8)]),
   ((.fixed 9),[(.pos 9)]),
   ((.exchange 1 11 2),[(.neg 11),(.neg 1),(.pos 0),(.pos 10)]),
   ((.exchange 2 10 2),[(.neg 10),(.neg 2),(.pos 0),(.pos 11)]),
   ((.exchange 11 8 1),[(.neg 11),(.neg 8),(.pos 12),(.pos 14)]),
   ((.exchange 11 9 1),[(.neg 11),(.neg 9),(.pos 13),(.pos 14)]),
   ((.exchange 12 6 2),[(.neg 12),(.neg 6),(.pos 10),(.pos 14)]),
   ((.exchange 13 6 3),[(.neg 13),(.neg 6),(.pos 10),(.pos 14)]),
   ((.exchange 14 1 4),[(.neg 14),(.neg 1),(.pos 10),(.pos 12)]),
   ((.exchange 14 3 4),[(.neg 14),(.neg 3),(.pos 10),(.pos 13)]),
   ((.exchange 14 5 4),[(.neg 14),(.neg 5),(.pos 12),(.pos 13)]),
   (.newPoint,[(.pos 10),(.pos 11),(.pos 12),(.pos 13),(.pos 14)]),
   ((.excluded 0),[(.neg 14),(.neg 13),(.neg 12),(.pos 10),(.pos 11)]),
   ((.excluded 1),[(.neg 14),(.neg 13),(.neg 11),(.neg 10),(.pos 12)]),
   ((.excluded 2),[(.neg 14),(.neg 12),(.neg 11),(.neg 10),(.pos 13)]),
   ((.excluded 3),[(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.pos 14)]),
   ((.excluded 4),[(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 10)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (5 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 5,
    let w : Fin 5 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 6 2 ∧
      ValidWitness 6 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 6 2 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N6R2C4

/- Source: MatroidCatalogue/Cases/N6R2C4Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R2C4

noncomputable def certificates : List (Origin 15 5 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (5 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 5,
    target w < MatroidCatalogue.count 6 2 ∧
      ValidWitness 6 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 6 2 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 5) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 6) 2)
    (hold : M.bases.filter ((5 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 6 2, IsomorphicWithin 6 M.bases B := by
  apply extension_covered_of_certificate (n:=5) (r:=2) (by decide)
    catalogue old U newIndex models certificates
    N6R2.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N6R2C4.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N6R2C4.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 6 2 (target w),family_mem 6 2 (target w) hw.1,?_⟩
    exact validWitness_sound 6 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N6R2C4

/- Source: MatroidCatalogue/Cases/N6R2C5Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R2C5

abbrev U := N6R2.grid
noncomputable def old : Finset (Finset (Fin 8)) := N5R2.family 5
noncomputable def newIndexTree : Table ℕ := (.node 2 (.node 1 (.leaf 10) (.leaf 11)) (.node 3 (.leaf 12) (.node 4 (.leaf 13) (.leaf 14))))
noncomputable def newIndex (i : Fin 5) : Fin 15 := Fin.ofNat 15 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 3 (.node 1 (.leaf (30,8,16308432)) (.node 2 (.leaf (29,8,16308418)) (.leaf (27,8,16308250)))) (.node 4 (.leaf (23,8,16306458)) (.node 5 (.leaf (15,8,16288538)) (.leaf (31,9,16434824)))))

noncomputable def models (i : Fin 6) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 6) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 6) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 15, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (5 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 15, (5 : Fin 8) ∈ U i → ∃ j : Fin 5, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N6R2C5

/- Source: MatroidCatalogue/Cases/N6R2C5Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R2C5


noncomputable def certificates_0 : List (Origin 15 6 × List Sat.Literal) :=
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
   ((.exchange 10 2 0),[(.neg 10),(.neg 2),(.pos 11),(.pos 12)]),
   ((.exchange 10 4 0),[(.neg 10),(.neg 4),(.pos 11),(.pos 13)]),
   ((.exchange 10 7 0),[(.neg 10),(.neg 7),(.pos 11),(.pos 14)]),
   ((.exchange 10 8 0),[(.neg 10),(.neg 8),(.pos 12),(.pos 14)]),
   ((.exchange 10 9 0),[(.neg 10),(.neg 9),(.pos 13),(.pos 14)]),
   ((.exchange 11 5 1),[(.neg 11),(.neg 5),(.pos 12),(.pos 13)]),
   ((.exchange 11 6 1),[(.neg 11),(.neg 6),(.pos 10),(.pos 14)]),
   ((.exchange 12 6 2),[(.neg 12),(.neg 6),(.pos 10),(.pos 14)]),
   ((.exchange 13 6 3),[(.neg 13),(.neg 6),(.pos 10),(.pos 14)]),
   ((.exchange 14 0 4),[(.neg 14),(.neg 0),(.pos 10),(.pos 11)]),
   ((.exchange 14 1 4),[(.neg 14),(.neg 1),(.pos 10),(.pos 12)]),
   ((.exchange 14 3 4),[(.neg 14),(.neg 3),(.pos 10),(.pos 13)]),
   (.newPoint,[(.pos 10),(.pos 11),(.pos 12),(.pos 13),(.pos 14)]),
   ((.excluded 0),[(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.pos 10)]),
   ((.excluded 1),[(.neg 14),(.neg 13),(.neg 12),(.neg 10),(.pos 11)]),
   ((.excluded 2),[(.neg 14),(.neg 13),(.neg 11),(.neg 10),(.pos 12)]),
   ((.excluded 3),[(.neg 14),(.neg 12),(.neg 11),(.neg 10),(.pos 13)]),
   ((.excluded 4),[(.neg 13),(.neg 12),(.neg 11),(.neg 10),(.pos 14)]),
   ((.excluded 5),[(.neg 14),(.neg 13),(.neg 12),(.neg 11),(.neg 10)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (5 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 6,
    let w : Fin 6 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 6 2 ∧
      ValidWitness 6 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 6 2 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N6R2C5

/- Source: MatroidCatalogue/Cases/N6R2C5Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R2C5

noncomputable def certificates : List (Origin 15 6 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (5 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 6,
    target w < MatroidCatalogue.count 6 2 ∧
      ValidWitness 6 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 6 2 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 6) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 6) 2)
    (hold : M.bases.filter ((5 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 6 2, IsomorphicWithin 6 M.bases B := by
  apply extension_covered_of_certificate (n:=5) (r:=2) (by decide)
    catalogue old U newIndex models certificates
    N6R2.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N6R2C5.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N6R2C5.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 6 2 (target w),family_mem 6 2 (target w) hw.1,?_⟩
    exact validWitness_sound 6 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N6R2C5

/- Source: MatroidCatalogue/Cases/N6R3C0Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C0

abbrev U := N6R3.grid
noncomputable def old : Finset (Finset (Fin 8)) := N5R3.family 0
noncomputable def newIndexTree : Table ℕ := (.node 5 (.node 2 (.node 1 (.leaf 10) (.leaf 11)) (.node 3 (.leaf 12) (.node 4 (.leaf 13) (.leaf 14)))) (.node 7 (.node 6 (.leaf 15) (.leaf 16)) (.node 8 (.leaf 17) (.node 9 (.leaf 18) (.leaf 19)))))
noncomputable def newIndex (i : Fin 10) : Fin 20 := Fin.ofNat 20 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 3 (.node 1 (.leaf (512,0,16373896)) (.node 2 (.leaf (448,1,16406152)) (.leaf (960,2,16406152)))) (.node 5 (.node 4 (.leaf (56,1,16398984)) (.leaf (568,2,16398984))) (.node 6 (.leaf (504,6,16434824)) (.leaf (1016,7,16434824)))))

noncomputable def models (i : Fin 7) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 7) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 7) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 20, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (5 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 20, (5 : Fin 8) ∈ U i → ∃ j : Fin 10, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C0

/- Source: MatroidCatalogue/Cases/N6R3C0Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C0


noncomputable def certificates_0 : List (Origin 20 7 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.neg 2)]),
   ((.fixed 3),[(.neg 3)]),
   ((.fixed 4),[(.neg 4)]),
   ((.fixed 5),[(.neg 5)]),
   ((.fixed 6),[(.neg 6)]),
   ((.fixed 7),[(.pos 7)]),
   ((.fixed 8),[(.pos 8)]),
   ((.fixed 9),[(.pos 9)]),
   ((.exchange 7 14 4),[(.neg 14),(.neg 7),(.pos 1),(.pos 13)]),
   ((.exchange 7 15 4),[(.neg 15),(.neg 7),(.pos 2),(.pos 13)]),
   ((.exchange 7 17 3),[(.neg 17),(.neg 7),(.pos 4),(.pos 16)]),
   ((.exchange 7 18 3),[(.neg 18),(.neg 7),(.pos 5),(.pos 16)]),
   ((.exchange 8 13 4),[(.neg 13),(.neg 8),(.pos 1),(.pos 14)]),
   ((.exchange 8 15 4),[(.neg 15),(.neg 8),(.pos 3),(.pos 14)]),
   ((.exchange 8 16 3),[(.neg 16),(.neg 8),(.pos 4),(.pos 17)]),
   ((.exchange 8 18 3),[(.neg 18),(.neg 8),(.pos 6),(.pos 17)]),
   ((.exchange 9 13 4),[(.neg 13),(.neg 9),(.pos 2),(.pos 15)]),
   ((.exchange 9 14 4),[(.neg 14),(.neg 9),(.pos 3),(.pos 15)]),
   ((.exchange 9 16 3),[(.neg 16),(.neg 9),(.pos 5),(.pos 18)]),
   ((.exchange 9 17 3),[(.neg 17),(.neg 9),(.pos 6),(.pos 18)]),
   ((.exchange 10 7 5),[(.neg 10),(.neg 7),(.pos 1),(.pos 4)]),
   ((.exchange 11 7 5),[(.neg 11),(.neg 7),(.pos 2),(.pos 5)]),
   ((.exchange 12 7 5),[(.neg 12),(.neg 7),(.pos 0),(.pos 3),(.pos 6)]),
   (.newPoint,[(.pos 10),(.pos 11),(.pos 12),(.pos 13),(.pos 14),(.pos 15),(.pos 16),(.pos 17),(.pos 18),(.pos 19)]),
   ((.excluded 0),[(.neg 19),(.pos 10),(.pos 11),(.pos 12),(.pos 13),(.pos 14),(.pos 15),(.pos 16),(.pos 17),(.pos 18)]),
   ((.excluded 1),[(.neg 18),(.neg 17),(.neg 16),(.pos 10),(.pos 11),(.pos 12),(.pos 13),(.pos 14),(.pos 15),(.pos 19)]),
   ((.excluded 2),[(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.pos 10),(.pos 11),(.pos 12),(.pos 13),(.pos 14),(.pos 15)]),
   ((.excluded 3),[(.neg 15),(.neg 14),(.neg 13),(.pos 10),(.pos 11),(.pos 12),(.pos 16),(.pos 17),(.pos 18),(.pos 19)]),
   ((.excluded 4),[(.neg 19),(.neg 15),(.neg 14),(.neg 13),(.pos 10),(.pos 11),(.pos 12),(.pos 16),(.pos 17),(.pos 18)]),
   ((.excluded 5),[(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.neg 14),(.neg 13),(.pos 10),(.pos 11),(.pos 12),(.pos 19)]),
   ((.excluded 6),[(.neg 19),(.neg 18),(.neg 17),(.neg 16),(.neg 15),(.neg 14),(.neg 13),(.pos 10),(.pos 11),(.pos 12)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (5 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 7,
    let w : Fin 7 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 6 3 ∧
      ValidWitness 6 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 6 3 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C0

/- Source: MatroidCatalogue/Cases/N6R3C0Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C0

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
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N6R3C0.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N6R3C0.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 6 3 (target w),family_mem 6 3 (target w) hw.1,?_⟩
    exact validWitness_sound 6 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N6R3C0

