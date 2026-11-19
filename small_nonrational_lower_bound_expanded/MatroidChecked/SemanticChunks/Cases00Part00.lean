module
public import MatroidCatalogue.Definitions
public import MatroidCases.N2R1C0
import all MatroidCases.N2R1C0
public import MatroidCases.N3R1C0
import all MatroidCases.N3R1C0
public import MatroidCases.N3R2C0
import all MatroidCases.N3R2C0
public import MatroidCases.N4R1C0
import all MatroidCases.N4R1C0
public import MatroidCases.N4R2C0
import all MatroidCases.N4R2C0
public import MatroidCases.N4R2C1
import all MatroidCases.N4R2C1
public import MatroidCases.N4R3C0
import all MatroidCases.N4R3C0
public import MatroidCases.N5R1C0
import all MatroidCases.N5R1C0

@[expose] public section
noncomputable section

/- Source: MatroidCatalogue/Cases/N2R1C0Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N2R1C0

abbrev U := N2R1.grid
noncomputable def old : Finset (Finset (Fin 8)) := N1R1.family 0
noncomputable def newIndexTree : Table ℕ := (.leaf 1)
noncomputable def newIndex (i : Fin 1) : Fin 2 := Fin.ofNat 2 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.leaf (1,0,16434824))

noncomputable def models (i : Fin 1) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 1) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 1) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 2, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (1 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 2, (1 : Fin 8) ∈ U i → ∃ j : Fin 1, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N2R1C0

/- Source: MatroidCatalogue/Cases/N2R1C0Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N2R1C0


noncomputable def certificates_0 : List (Origin 2 1 × List Sat.Literal) :=
  [(.newPoint,[(.pos 1)]),
   ((.excluded 0),[(.neg 1)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (1 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 1,
    let w : Fin 1 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 2 1 ∧
      ValidWitness 2 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 2 1 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N2R1C0

/- Source: MatroidCatalogue/Cases/N2R1C0Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N2R1C0

noncomputable def certificates : List (Origin 2 1 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (1 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 1,
    target w < MatroidCatalogue.count 2 1 ∧
      ValidWitness 2 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 2 1 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 1) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 2) 1)
    (hold : M.bases.filter ((1 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 2 1, IsomorphicWithin 2 M.bases B := by
  apply extension_covered_of_certificate (n:=1) (r:=1) (by decide)
    catalogue old U newIndex models certificates
    N2R1.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N2R1C0.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N2R1C0.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 2 1 (target w),family_mem 2 1 (target w) hw.1,?_⟩
    exact validWitness_sound 2 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N2R1C0

/- Source: MatroidCatalogue/Cases/N3R1C0Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N3R1C0

abbrev U := N3R1.grid
noncomputable def old : Finset (Finset (Fin 8)) := N2R1.family 0
noncomputable def newIndexTree : Table ℕ := (.leaf 2)
noncomputable def newIndex (i : Fin 1) : Fin 3 := Fin.ofNat 3 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.leaf (1,0,16434824))

noncomputable def models (i : Fin 1) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 1) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 1) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 3, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (2 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 3, (2 : Fin 8) ∈ U i → ∃ j : Fin 1, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N3R1C0

/- Source: MatroidCatalogue/Cases/N3R1C0Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N3R1C0


noncomputable def certificates_0 : List (Origin 3 1 × List Sat.Literal) :=
  [(.newPoint,[(.pos 2)]),
   ((.excluded 0),[(.neg 2)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (2 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 1,
    let w : Fin 1 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 3 1 ∧
      ValidWitness 3 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 3 1 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N3R1C0

/- Source: MatroidCatalogue/Cases/N3R1C0Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N3R1C0

noncomputable def certificates : List (Origin 3 1 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (2 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 1,
    target w < MatroidCatalogue.count 3 1 ∧
      ValidWitness 3 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 3 1 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 1) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 3) 1)
    (hold : M.bases.filter ((2 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 3 1, IsomorphicWithin 3 M.bases B := by
  apply extension_covered_of_certificate (n:=2) (r:=1) (by decide)
    catalogue old U newIndex models certificates
    N3R1.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N3R1C0.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N3R1C0.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 3 1 (target w),family_mem 3 1 (target w) hw.1,?_⟩
    exact validWitness_sound 3 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N3R1C0

/- Source: MatroidCatalogue/Cases/N3R2C0Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N3R2C0

abbrev U := N3R2.grid
noncomputable def old : Finset (Finset (Fin 8)) := N2R2.family 0
noncomputable def newIndexTree : Table ℕ := (.node 1 (.leaf 1) (.leaf 2))
noncomputable def newIndex (i : Fin 2) : Fin 3 := Fin.ofNat 3 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 1 (.leaf (2,0,16434768)) (.node 2 (.leaf (1,0,16434754)) (.leaf (3,1,16434824))))

noncomputable def models (i : Fin 3) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 3) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 3) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 3, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (2 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 3, (2 : Fin 8) ∈ U i → ∃ j : Fin 2, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N3R2C0

/- Source: MatroidCatalogue/Cases/N3R2C0Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N3R2C0


noncomputable def certificates_0 : List (Origin 3 3 × List Sat.Literal) :=
  [(.newPoint,[(.pos 1),(.pos 2)]),
   ((.excluded 0),[(.neg 2),(.pos 1)]),
   ((.excluded 1),[(.neg 1),(.pos 2)]),
   ((.excluded 2),[(.neg 2),(.neg 1)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (2 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 3,
    let w : Fin 3 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 3 2 ∧
      ValidWitness 3 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 3 2 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N3R2C0

/- Source: MatroidCatalogue/Cases/N3R2C0Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N3R2C0

noncomputable def certificates : List (Origin 3 3 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (2 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 3,
    target w < MatroidCatalogue.count 3 2 ∧
      ValidWitness 3 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 3 2 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 3) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 3) 2)
    (hold : M.bases.filter ((2 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 3 2, IsomorphicWithin 3 M.bases B := by
  apply extension_covered_of_certificate (n:=2) (r:=2) (by decide)
    catalogue old U newIndex models certificates
    N3R2.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N3R2C0.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N3R2C0.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 3 2 (target w),family_mem 3 2 (target w) hw.1,?_⟩
    exact validWitness_sound 3 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N3R2C0

/- Source: MatroidCatalogue/Cases/N4R1C0Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N4R1C0

abbrev U := N4R1.grid
noncomputable def old : Finset (Finset (Fin 8)) := N3R1.family 0
noncomputable def newIndexTree : Table ℕ := (.leaf 3)
noncomputable def newIndex (i : Fin 1) : Fin 4 := Fin.ofNat 4 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.leaf (1,0,16434824))

noncomputable def models (i : Fin 1) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 1) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 1) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 4, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (3 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 4, (3 : Fin 8) ∈ U i → ∃ j : Fin 1, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N4R1C0

/- Source: MatroidCatalogue/Cases/N4R1C0Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N4R1C0


noncomputable def certificates_0 : List (Origin 4 1 × List Sat.Literal) :=
  [(.newPoint,[(.pos 3)]),
   ((.excluded 0),[(.neg 3)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (3 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 1,
    let w : Fin 1 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 4 1 ∧
      ValidWitness 4 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 4 1 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N4R1C0

/- Source: MatroidCatalogue/Cases/N4R1C0Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N4R1C0

noncomputable def certificates : List (Origin 4 1 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (3 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 1,
    target w < MatroidCatalogue.count 4 1 ∧
      ValidWitness 4 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 4 1 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 1) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 4) 1)
    (hold : M.bases.filter ((3 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 4 1, IsomorphicWithin 4 M.bases B := by
  apply extension_covered_of_certificate (n:=3) (r:=1) (by decide)
    catalogue old U newIndex models certificates
    N4R1.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N4R1C0.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N4R1C0.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 4 1 (target w),family_mem 4 1 (target w) hw.1,?_⟩
    exact validWitness_sound 4 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N4R1C0

/- Source: MatroidCatalogue/Cases/N4R2C0Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N4R2C0

abbrev U := N4R2.grid
noncomputable def old : Finset (Finset (Fin 8)) := N3R2.family 0
noncomputable def newIndexTree : Table ℕ := (.node 1 (.leaf 3) (.node 2 (.leaf 4) (.leaf 5)))
noncomputable def newIndex (i : Fin 3) : Fin 6 := Fin.ofNat 6 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 1 (.leaf (4,0,16434376)) (.node 2 (.leaf (3,1,16434824)) (.leaf (7,2,16434824))))

noncomputable def models (i : Fin 3) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 3) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 3) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 6, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (3 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 6, (3 : Fin 8) ∈ U i → ∃ j : Fin 3, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N4R2C0

/- Source: MatroidCatalogue/Cases/N4R2C0Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N4R2C0


noncomputable def certificates_0 : List (Origin 6 3 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.pos 1)]),
   ((.fixed 2),[(.pos 2)]),
   ((.exchange 1 4 2),[(.neg 4),(.neg 1),(.pos 0),(.pos 3)]),
   ((.exchange 2 3 2),[(.neg 3),(.neg 2),(.pos 0),(.pos 4)]),
   (.newPoint,[(.pos 3),(.pos 4),(.pos 5)]),
   ((.excluded 0),[(.neg 5),(.pos 3),(.pos 4)]),
   ((.excluded 1),[(.neg 4),(.neg 3),(.pos 5)]),
   ((.excluded 2),[(.neg 5),(.neg 4),(.neg 3)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (3 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 3,
    let w : Fin 3 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 4 2 ∧
      ValidWitness 4 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 4 2 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N4R2C0

/- Source: MatroidCatalogue/Cases/N4R2C0Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N4R2C0

noncomputable def certificates : List (Origin 6 3 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (3 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 3,
    target w < MatroidCatalogue.count 4 2 ∧
      ValidWitness 4 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 4 2 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 3) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 4) 2)
    (hold : M.bases.filter ((3 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 4 2, IsomorphicWithin 4 M.bases B := by
  apply extension_covered_of_certificate (n:=3) (r:=2) (by decide)
    catalogue old U newIndex models certificates
    N4R2.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N4R2C0.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N4R2C0.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 4 2 (target w),family_mem 4 2 (target w) hw.1,?_⟩
    exact validWitness_sound 4 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N4R2C0

/- Source: MatroidCatalogue/Cases/N4R2C1Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N4R2C1

abbrev U := N4R2.grid
noncomputable def old : Finset (Finset (Fin 8)) := N3R2.family 1
noncomputable def newIndexTree : Table ℕ := (.node 1 (.leaf 3) (.node 2 (.leaf 4) (.leaf 5)))
noncomputable def newIndex (i : Fin 3) : Fin 6 := Fin.ofNat 6 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 2 (.node 1 (.leaf (6,2,16433872)) (.leaf (5,2,16433858))) (.node 3 (.leaf (3,2,16433690)) (.leaf (7,3,16434824))))

noncomputable def models (i : Fin 4) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 4) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 4) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 6, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (3 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 6, (3 : Fin 8) ∈ U i → ∃ j : Fin 3, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N4R2C1

/- Source: MatroidCatalogue/Cases/N4R2C1Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N4R2C1


noncomputable def certificates_0 : List (Origin 6 4 × List Sat.Literal) :=
  [((.fixed 0),[(.pos 0)]),
   ((.fixed 1),[(.pos 1)]),
   ((.fixed 2),[(.pos 2)]),
   ((.exchange 3 2 0),[(.neg 3),(.neg 2),(.pos 4),(.pos 5)]),
   ((.exchange 4 1 1),[(.neg 4),(.neg 1),(.pos 3),(.pos 5)]),
   ((.exchange 5 0 2),[(.neg 5),(.neg 0),(.pos 3),(.pos 4)]),
   (.newPoint,[(.pos 3),(.pos 4),(.pos 5)]),
   ((.excluded 0),[(.neg 5),(.neg 4),(.pos 3)]),
   ((.excluded 1),[(.neg 5),(.neg 3),(.pos 4)]),
   ((.excluded 2),[(.neg 4),(.neg 3),(.pos 5)]),
   ((.excluded 3),[(.neg 5),(.neg 4),(.neg 3)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (3 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 4,
    let w : Fin 4 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 4 2 ∧
      ValidWitness 4 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 4 2 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N4R2C1

/- Source: MatroidCatalogue/Cases/N4R2C1Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N4R2C1

noncomputable def certificates : List (Origin 6 4 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (3 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 4,
    target w < MatroidCatalogue.count 4 2 ∧
      ValidWitness 4 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 4 2 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 4) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 4) 2)
    (hold : M.bases.filter ((3 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 4 2, IsomorphicWithin 4 M.bases B := by
  apply extension_covered_of_certificate (n:=3) (r:=2) (by decide)
    catalogue old U newIndex models certificates
    N4R2.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N4R2C1.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N4R2C1.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 4 2 (target w),family_mem 4 2 (target w) hw.1,?_⟩
    exact validWitness_sound 4 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N4R2C1

/- Source: MatroidCatalogue/Cases/N4R3C0Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N4R3C0

abbrev U := N4R3.grid
noncomputable def old : Finset (Finset (Fin 8)) := N3R3.family 0
noncomputable def newIndexTree : Table ℕ := (.node 1 (.leaf 1) (.node 2 (.leaf 2) (.leaf 3)))
noncomputable def newIndex (i : Fin 3) : Fin 4 := Fin.ofNat 4 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 3 (.node 1 (.leaf (4,0,16433872)) (.node 2 (.leaf (2,0,16433858)) (.leaf (6,1,16434376)))) (.node 5 (.node 4 (.leaf (1,0,16433690)) (.leaf (5,1,16434264))) (.node 6 (.leaf (3,1,16434243)) (.leaf (7,2,16434824)))))

noncomputable def models (i : Fin 7) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 7) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 7) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 4, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (3 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 4, (3 : Fin 8) ∈ U i → ∃ j : Fin 3, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N4R3C0

/- Source: MatroidCatalogue/Cases/N4R3C0Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N4R3C0


noncomputable def certificates_0 : List (Origin 4 7 × List Sat.Literal) :=
  [(.newPoint,[(.pos 1),(.pos 2),(.pos 3)]),
   ((.excluded 0),[(.neg 3),(.pos 1),(.pos 2)]),
   ((.excluded 1),[(.neg 2),(.pos 1),(.pos 3)]),
   ((.excluded 2),[(.neg 3),(.neg 2),(.pos 1)]),
   ((.excluded 3),[(.neg 1),(.pos 2),(.pos 3)]),
   ((.excluded 4),[(.neg 3),(.neg 1),(.pos 2)]),
   ((.excluded 5),[(.neg 2),(.neg 1),(.pos 3)]),
   ((.excluded 6),[(.neg 3),(.neg 2),(.neg 1)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (3 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 7,
    let w : Fin 7 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 4 3 ∧
      ValidWitness 4 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 4 3 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N4R3C0

/- Source: MatroidCatalogue/Cases/N4R3C0Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N4R3C0

noncomputable def certificates : List (Origin 4 7 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (3 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 7,
    target w < MatroidCatalogue.count 4 3 ∧
      ValidWitness 4 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 4 3 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 7) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 4) 3)
    (hold : M.bases.filter ((3 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 4 3, IsomorphicWithin 4 M.bases B := by
  apply extension_covered_of_certificate (n:=3) (r:=3) (by decide)
    catalogue old U newIndex models certificates
    N4R3.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N4R3C0.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N4R3C0.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 4 3 (target w),family_mem 4 3 (target w) hw.1,?_⟩
    exact validWitness_sound 4 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N4R3C0

/- Source: MatroidCatalogue/Cases/N5R1C0Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N5R1C0

abbrev U := N5R1.grid
noncomputable def old : Finset (Finset (Fin 8)) := N4R1.family 0
noncomputable def newIndexTree : Table ℕ := (.leaf 4)
noncomputable def newIndex (i : Fin 1) : Fin 5 := Fin.ofNat 5 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.leaf (1,0,16434824))

noncomputable def models (i : Fin 1) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 1) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 1) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 5, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (4 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 5, (4 : Fin 8) ∈ U i → ∃ j : Fin 1, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N5R1C0

/- Source: MatroidCatalogue/Cases/N5R1C0Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N5R1C0


noncomputable def certificates_0 : List (Origin 5 1 × List Sat.Literal) :=
  [(.newPoint,[(.pos 4)]),
   ((.excluded 0),[(.neg 4)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (4 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 1,
    let w : Fin 1 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 5 1 ∧
      ValidWitness 5 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 5 1 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N5R1C0

/- Source: MatroidCatalogue/Cases/N5R1C0Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N5R1C0

noncomputable def certificates : List (Origin 5 1 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (4 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 1,
    target w < MatroidCatalogue.count 5 1 ∧
      ValidWitness 5 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 5 1 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 1) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 5) 1)
    (hold : M.bases.filter ((4 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 5 1, IsomorphicWithin 5 M.bases B := by
  apply extension_covered_of_certificate (n:=4) (r:=1) (by decide)
    catalogue old U newIndex models certificates
    N5R1.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N5R1C0.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N5R1C0.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 5 1 (target w),family_mem 5 1 (target w) hw.1,?_⟩
    exact validWitness_sound 5 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N5R1C0

