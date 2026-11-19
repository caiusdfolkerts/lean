module
public import MatroidCatalogue.Definitions
public import MatroidCases.N5R2C0
import all MatroidCases.N5R2C0
public import MatroidCases.N5R2C1
import all MatroidCases.N5R2C1
public import MatroidCases.N5R2C2
import all MatroidCases.N5R2C2
public import MatroidCases.N5R2C3
import all MatroidCases.N5R2C3
public import MatroidCases.N5R3C0
import all MatroidCases.N5R3C0
public import MatroidCases.N5R3C1
import all MatroidCases.N5R3C1
public import MatroidCases.N5R3C2
import all MatroidCases.N5R3C2
public import MatroidCases.N5R4C0
import all MatroidCases.N5R4C0

@[expose] public section
noncomputable section

/- Source: MatroidCatalogue/Cases/N5R2C0Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N5R2C0

abbrev U := N5R2.grid
noncomputable def old : Finset (Finset (Fin 8)) := N4R2.family 0
noncomputable def newIndexTree : Table ℕ := (.node 2 (.node 1 (.leaf 6) (.leaf 7)) (.node 3 (.leaf 8) (.leaf 9)))
noncomputable def newIndex (i : Fin 4) : Fin 10 := Fin.ofNat 10 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 1 (.leaf (8,0,16431240)) (.node 2 (.leaf (7,1,16434824)) (.leaf (15,2,16434824))))

noncomputable def models (i : Fin 3) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 3) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 3) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 10, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (4 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 10, (4 : Fin 8) ∈ U i → ∃ j : Fin 4, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N5R2C0

/- Source: MatroidCatalogue/Cases/N5R2C0Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N5R2C0


noncomputable def certificates_0 : List (Origin 10 3 × List Sat.Literal) :=
  [((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.neg 2)]),
   ((.fixed 3),[(.pos 3)]),
   ((.fixed 4),[(.pos 4)]),
   ((.fixed 5),[(.pos 5)]),
   ((.exchange 3 8 3),[(.neg 8),(.neg 3),(.pos 1),(.pos 6)]),
   ((.exchange 4 8 3),[(.neg 8),(.neg 4),(.pos 2),(.pos 7)]),
   ((.exchange 5 6 3),[(.neg 6),(.neg 5),(.pos 1),(.pos 8)]),
   ((.exchange 5 7 3),[(.neg 7),(.neg 5),(.pos 2),(.pos 8)]),
   (.newPoint,[(.pos 6),(.pos 7),(.pos 8),(.pos 9)]),
   ((.excluded 0),[(.neg 9),(.pos 6),(.pos 7),(.pos 8)]),
   ((.excluded 1),[(.neg 8),(.neg 7),(.neg 6),(.pos 9)]),
   ((.excluded 2),[(.neg 9),(.neg 8),(.neg 7),(.neg 6)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (4 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 3,
    let w : Fin 3 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 5 2 ∧
      ValidWitness 5 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 5 2 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N5R2C0

/- Source: MatroidCatalogue/Cases/N5R2C0Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N5R2C0

noncomputable def certificates : List (Origin 10 3 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (4 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 3,
    target w < MatroidCatalogue.count 5 2 ∧
      ValidWitness 5 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 5 2 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 3) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 5) 2)
    (hold : M.bases.filter ((4 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 5 2, IsomorphicWithin 5 M.bases B := by
  apply extension_covered_of_certificate (n:=4) (r:=2) (by decide)
    catalogue old U newIndex models certificates
    N5R2.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N5R2C0.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N5R2C0.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 5 2 (target w),family_mem 5 2 (target w) hw.1,?_⟩
    exact validWitness_sound 5 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N5R2C0

/- Source: MatroidCatalogue/Cases/N5R2C1Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N5R2C1

abbrev U := N5R2.grid
noncomputable def old : Finset (Finset (Fin 8)) := N4R2.family 1
noncomputable def newIndexTree : Table ℕ := (.node 2 (.node 1 (.leaf 6) (.leaf 7)) (.node 3 (.leaf 8) (.leaf 9)))
noncomputable def newIndex (i : Fin 4) : Fin 10 := Fin.ofNat 10 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 1 (.leaf (12,1,16427208)) (.node 2 (.leaf (3,1,16425507)) (.leaf (15,3,16434824))))

noncomputable def models (i : Fin 3) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 3) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 3) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 10, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (4 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 10, (4 : Fin 8) ∈ U i → ∃ j : Fin 4, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N5R2C1

/- Source: MatroidCatalogue/Cases/N5R2C1Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N5R2C1


noncomputable def certificates_0 : List (Origin 10 3 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.pos 1)]),
   ((.fixed 2),[(.pos 2)]),
   ((.fixed 3),[(.pos 3)]),
   ((.fixed 5),[(.neg 5)]),
   ((.exchange 1 7 2),[(.neg 7),(.neg 1),(.pos 0),(.pos 6)]),
   ((.exchange 1 9 0),[(.neg 9),(.neg 1),(.pos 5),(.pos 8)]),
   ((.exchange 2 6 2),[(.neg 6),(.neg 2),(.pos 0),(.pos 7)]),
   ((.exchange 3 8 0),[(.neg 8),(.neg 3),(.pos 5),(.pos 9)]),
   (.newPoint,[(.pos 6),(.pos 7),(.pos 8),(.pos 9)]),
   ((.excluded 0),[(.neg 9),(.neg 8),(.pos 6),(.pos 7)]),
   ((.excluded 1),[(.neg 7),(.neg 6),(.pos 8),(.pos 9)]),
   ((.excluded 2),[(.neg 9),(.neg 8),(.neg 7),(.neg 6)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (4 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 3,
    let w : Fin 3 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 5 2 ∧
      ValidWitness 5 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 5 2 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N5R2C1

/- Source: MatroidCatalogue/Cases/N5R2C1Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N5R2C1

noncomputable def certificates : List (Origin 10 3 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (4 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 3,
    target w < MatroidCatalogue.count 5 2 ∧
      ValidWitness 5 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 5 2 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 3) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 5) 2)
    (hold : M.bases.filter ((4 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 5 2, IsomorphicWithin 5 M.bases B := by
  apply extension_covered_of_certificate (n:=4) (r:=2) (by decide)
    catalogue old U newIndex models certificates
    N5R2.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N5R2C1.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N5R2C1.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 5 2 (target w),family_mem 5 2 (target w) hw.1,?_⟩
    exact validWitness_sound 5 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N5R2C1

/- Source: MatroidCatalogue/Cases/N5R2C2Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N5R2C2

abbrev U := N5R2.grid
noncomputable def old : Finset (Finset (Fin 8)) := N4R2.family 2
noncomputable def newIndexTree : Table ℕ := (.node 2 (.node 1 (.leaf 6) (.leaf 7)) (.node 3 (.leaf 8) (.leaf 9)))
noncomputable def newIndex (i : Fin 4) : Fin 10 := Fin.ofNat 10 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 2 (.node 1 (.leaf (12,2,16427208)) (.leaf (11,3,16431240))) (.node 3 (.leaf (7,3,16430344)) (.leaf (15,4,16434824))))

noncomputable def models (i : Fin 4) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 4) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 4) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 10, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (4 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 10, (4 : Fin 8) ∈ U i → ∃ j : Fin 4, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N5R2C2

/- Source: MatroidCatalogue/Cases/N5R2C2Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N5R2C2


noncomputable def certificates_0 : List (Origin 10 4 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.pos 1)]),
   ((.fixed 2),[(.pos 2)]),
   ((.fixed 3),[(.pos 3)]),
   ((.fixed 5),[(.pos 5)]),
   ((.exchange 1 7 2),[(.neg 7),(.neg 1),(.pos 0),(.pos 6)]),
   ((.exchange 2 6 2),[(.neg 6),(.neg 2),(.pos 0),(.pos 7)]),
   ((.exchange 7 5 1),[(.neg 7),(.neg 5),(.pos 8),(.pos 9)]),
   ((.exchange 8 3 2),[(.neg 8),(.neg 3),(.pos 6),(.pos 9)]),
   ((.exchange 9 1 3),[(.neg 9),(.neg 1),(.pos 6),(.pos 8)]),
   (.newPoint,[(.pos 6),(.pos 7),(.pos 8),(.pos 9)]),
   ((.excluded 0),[(.neg 9),(.neg 8),(.pos 6),(.pos 7)]),
   ((.excluded 1),[(.neg 9),(.neg 7),(.neg 6),(.pos 8)]),
   ((.excluded 2),[(.neg 8),(.neg 7),(.neg 6),(.pos 9)]),
   ((.excluded 3),[(.neg 9),(.neg 8),(.neg 7),(.neg 6)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (4 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 4,
    let w : Fin 4 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 5 2 ∧
      ValidWitness 5 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 5 2 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N5R2C2

/- Source: MatroidCatalogue/Cases/N5R2C2Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N5R2C2

noncomputable def certificates : List (Origin 10 4 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (4 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 4,
    target w < MatroidCatalogue.count 5 2 ∧
      ValidWitness 5 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 5 2 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 4) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 5) 2)
    (hold : M.bases.filter ((4 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 5 2, IsomorphicWithin 5 M.bases B := by
  apply extension_covered_of_certificate (n:=4) (r:=2) (by decide)
    catalogue old U newIndex models certificates
    N5R2.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N5R2C2.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N5R2C2.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 5 2 (target w),family_mem 5 2 (target w) hw.1,?_⟩
    exact validWitness_sound 5 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N5R2C2

/- Source: MatroidCatalogue/Cases/N5R2C3Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N5R2C3

abbrev U := N5R2.grid
noncomputable def old : Finset (Finset (Fin 8)) := N4R2.family 3
noncomputable def newIndexTree : Table ℕ := (.node 2 (.node 1 (.leaf 6) (.leaf 7)) (.node 3 (.leaf 8) (.leaf 9)))
noncomputable def newIndex (i : Fin 4) : Fin 10 := Fin.ofNat 10 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 2 (.node 1 (.leaf (14,4,16423120)) (.leaf (13,4,16423106))) (.node 3 (.leaf (11,4,16422938)) (.node 4 (.leaf (7,4,16421146)) (.leaf (15,5,16434824)))))

noncomputable def models (i : Fin 5) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 5) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 5) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 10, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (4 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 10, (4 : Fin 8) ∈ U i → ∃ j : Fin 4, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N5R2C3

/- Source: MatroidCatalogue/Cases/N5R2C3Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N5R2C3


noncomputable def certificates_0 : List (Origin 10 5 × List Sat.Literal) :=
  [((.fixed 0),[(.pos 0)]),
   ((.fixed 1),[(.pos 1)]),
   ((.fixed 2),[(.pos 2)]),
   ((.fixed 3),[(.pos 3)]),
   ((.fixed 4),[(.pos 4)]),
   ((.fixed 5),[(.pos 5)]),
   ((.exchange 6 4 0),[(.neg 6),(.neg 4),(.pos 7),(.pos 9)]),
   ((.exchange 6 5 0),[(.neg 6),(.neg 5),(.pos 8),(.pos 9)]),
   ((.exchange 7 1 1),[(.neg 7),(.neg 1),(.pos 6),(.pos 8)]),
   ((.exchange 7 3 1),[(.neg 7),(.neg 3),(.pos 6),(.pos 9)]),
   ((.exchange 8 0 2),[(.neg 8),(.neg 0),(.pos 6),(.pos 7)]),
   ((.exchange 9 2 3),[(.neg 9),(.neg 2),(.pos 7),(.pos 8)]),
   (.newPoint,[(.pos 6),(.pos 7),(.pos 8),(.pos 9)]),
   ((.excluded 0),[(.neg 9),(.neg 8),(.neg 7),(.pos 6)]),
   ((.excluded 1),[(.neg 9),(.neg 8),(.neg 6),(.pos 7)]),
   ((.excluded 2),[(.neg 9),(.neg 7),(.neg 6),(.pos 8)]),
   ((.excluded 3),[(.neg 8),(.neg 7),(.neg 6),(.pos 9)]),
   ((.excluded 4),[(.neg 9),(.neg 8),(.neg 7),(.neg 6)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (4 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 5,
    let w : Fin 5 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 5 2 ∧
      ValidWitness 5 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 5 2 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N5R2C3

/- Source: MatroidCatalogue/Cases/N5R2C3Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N5R2C3

noncomputable def certificates : List (Origin 10 5 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (4 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 5,
    target w < MatroidCatalogue.count 5 2 ∧
      ValidWitness 5 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 5 2 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 5) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 5) 2)
    (hold : M.bases.filter ((4 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 5 2, IsomorphicWithin 5 M.bases B := by
  apply extension_covered_of_certificate (n:=4) (r:=2) (by decide)
    catalogue old U newIndex models certificates
    N5R2.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N5R2C3.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N5R2C3.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 5 2 (target w),family_mem 5 2 (target w) hw.1,?_⟩
    exact validWitness_sound 5 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N5R2C3

/- Source: MatroidCatalogue/Cases/N5R3C0Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N5R3C0

abbrev U := N5R3.grid
noncomputable def old : Finset (Finset (Fin 8)) := N4R3.family 0
noncomputable def newIndexTree : Table ℕ := (.node 3 (.node 1 (.leaf 4) (.node 2 (.leaf 5) (.leaf 6))) (.node 4 (.leaf 7) (.node 5 (.leaf 8) (.leaf 9))))
noncomputable def newIndex (i : Fin 6) : Fin 10 := Fin.ofNat 10 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 3 (.node 1 (.leaf (32,0,16427208)) (.node 2 (.leaf (24,1,16431240)) (.leaf (56,2,16431240)))) (.node 5 (.node 4 (.leaf (6,1,16430344)) (.leaf (38,2,16430344))) (.node 6 (.leaf (30,4,16434824)) (.leaf (62,5,16434824)))))

noncomputable def models (i : Fin 7) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 7) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 7) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 10, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (4 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 10, (4 : Fin 8) ∈ U i → ∃ j : Fin 6, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N5R3C0

/- Source: MatroidCatalogue/Cases/N5R3C0Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N5R3C0


noncomputable def certificates_0 : List (Origin 10 7 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.neg 1)]),
   ((.fixed 2),[(.pos 2)]),
   ((.fixed 3),[(.pos 3)]),
   ((.exchange 2 6 3),[(.neg 6),(.neg 2),(.pos 0),(.pos 5)]),
   ((.exchange 2 8 2),[(.neg 8),(.neg 2),(.pos 1),(.pos 7)]),
   ((.exchange 3 5 3),[(.neg 5),(.neg 3),(.pos 0),(.pos 6)]),
   ((.exchange 3 7 2),[(.neg 7),(.neg 3),(.pos 1),(.pos 8)]),
   ((.exchange 4 2 4),[(.neg 4),(.neg 2),(.pos 0),(.pos 1)]),
   (.newPoint,[(.pos 4),(.pos 5),(.pos 6),(.pos 7),(.pos 8),(.pos 9)]),
   ((.excluded 0),[(.neg 9),(.pos 4),(.pos 5),(.pos 6),(.pos 7),(.pos 8)]),
   ((.excluded 1),[(.neg 8),(.neg 7),(.pos 4),(.pos 5),(.pos 6),(.pos 9)]),
   ((.excluded 2),[(.neg 9),(.neg 8),(.neg 7),(.pos 4),(.pos 5),(.pos 6)]),
   ((.excluded 3),[(.neg 6),(.neg 5),(.pos 4),(.pos 7),(.pos 8),(.pos 9)]),
   ((.excluded 4),[(.neg 9),(.neg 6),(.neg 5),(.pos 4),(.pos 7),(.pos 8)]),
   ((.excluded 5),[(.neg 8),(.neg 7),(.neg 6),(.neg 5),(.pos 4),(.pos 9)]),
   ((.excluded 6),[(.neg 9),(.neg 8),(.neg 7),(.neg 6),(.neg 5),(.pos 4)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (4 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 7,
    let w : Fin 7 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 5 3 ∧
      ValidWitness 5 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 5 3 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N5R3C0

/- Source: MatroidCatalogue/Cases/N5R3C0Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N5R3C0

noncomputable def certificates : List (Origin 10 7 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (4 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 7,
    target w < MatroidCatalogue.count 5 3 ∧
      ValidWitness 5 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 5 3 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 7) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 5) 3)
    (hold : M.bases.filter ((4 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 5 3, IsomorphicWithin 5 M.bases B := by
  apply extension_covered_of_certificate (n:=4) (r:=3) (by decide)
    catalogue old U newIndex models certificates
    N5R3.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N5R3C0.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N5R3C0.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 5 3 (target w),family_mem 5 3 (target w) hw.1,?_⟩
    exact validWitness_sound 5 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N5R3C0

/- Source: MatroidCatalogue/Cases/N5R3C1Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N5R3C1

abbrev U := N5R3.grid
noncomputable def old : Finset (Finset (Fin 8)) := N4R3.family 1
noncomputable def newIndexTree : Table ℕ := (.node 3 (.node 1 (.leaf 4) (.node 2 (.leaf 5) (.leaf 6))) (.node 4 (.leaf 7) (.node 5 (.leaf 8) (.leaf 9))))
noncomputable def newIndex (i : Fin 6) : Fin 10 := Fin.ofNat 10 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 4 (.node 2 (.node 1 (.leaf (48,2,16423120)) (.leaf (40,2,16423106))) (.node 3 (.leaf (24,2,16422938)) (.leaf (56,3,16431240)))) (.node 6 (.node 5 (.leaf (7,4,16421146)) (.leaf (55,6,16434824))) (.node 7 (.leaf (47,6,16434817)) (.node 8 (.leaf (31,6,16434705)) (.leaf (63,7,16434824))))))

noncomputable def models (i : Fin 9) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 9) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 9) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 10, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (4 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 10, (4 : Fin 8) ∈ U i → ∃ j : Fin 6, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N5R3C1

/- Source: MatroidCatalogue/Cases/N5R3C1Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N5R3C1


noncomputable def certificates_0 : List (Origin 10 9 × List Sat.Literal) :=
  [((.fixed 0),[(.neg 0)]),
   ((.fixed 1),[(.pos 1)]),
   ((.fixed 2),[(.pos 2)]),
   ((.fixed 3),[(.pos 3)]),
   ((.exchange 1 5 3),[(.neg 5),(.neg 1),(.pos 0),(.pos 4)]),
   ((.exchange 1 6 3),[(.neg 6),(.neg 1),(.pos 0),(.pos 4)]),
   ((.exchange 2 4 3),[(.neg 4),(.neg 2),(.pos 0),(.pos 5)]),
   ((.exchange 3 4 3),[(.neg 4),(.neg 3),(.pos 0),(.pos 6)]),
   ((.exchange 7 3 0),[(.neg 7),(.neg 3),(.pos 8),(.pos 9)]),
   ((.exchange 8 2 1),[(.neg 8),(.neg 2),(.pos 7),(.pos 9)]),
   ((.exchange 9 1 2),[(.neg 9),(.neg 1),(.pos 7),(.pos 8)]),
   ((.exchange 9 4 2),[(.neg 9),(.neg 4),(.pos 7),(.pos 8)]),
   (.newPoint,[(.pos 4),(.pos 5),(.pos 6),(.pos 7),(.pos 8),(.pos 9)]),
   ((.excluded 0),[(.neg 9),(.neg 8),(.pos 4),(.pos 5),(.pos 6),(.pos 7)]),
   ((.excluded 1),[(.neg 9),(.neg 7),(.pos 4),(.pos 5),(.pos 6),(.pos 8)]),
   ((.excluded 2),[(.neg 8),(.neg 7),(.pos 4),(.pos 5),(.pos 6),(.pos 9)]),
   ((.excluded 3),[(.neg 9),(.neg 8),(.neg 7),(.pos 4),(.pos 5),(.pos 6)]),
   ((.excluded 4),[(.neg 6),(.neg 5),(.neg 4),(.pos 7),(.pos 8),(.pos 9)]),
   ((.excluded 5),[(.neg 9),(.neg 8),(.neg 6),(.neg 5),(.neg 4),(.pos 7)]),
   ((.excluded 6),[(.neg 9),(.neg 7),(.neg 6),(.neg 5),(.neg 4),(.pos 8)]),
   ((.excluded 7),[(.neg 8),(.neg 7),(.neg 6),(.neg 5),(.neg 4),(.pos 9)]),
   ((.excluded 8),[(.neg 9),(.neg 8),(.neg 7),(.neg 6),(.neg 5),(.neg 4)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (4 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 9,
    let w : Fin 9 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 5 3 ∧
      ValidWitness 5 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 5 3 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N5R3C1

/- Source: MatroidCatalogue/Cases/N5R3C1Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N5R3C1

noncomputable def certificates : List (Origin 10 9 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (4 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 9,
    target w < MatroidCatalogue.count 5 3 ∧
      ValidWitness 5 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 5 3 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 9) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 5) 3)
    (hold : M.bases.filter ((4 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 5 3, IsomorphicWithin 5 M.bases B := by
  apply extension_covered_of_certificate (n:=4) (r:=3) (by decide)
    catalogue old U newIndex models certificates
    N5R3.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N5R3C1.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N5R3C1.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 5 3 (target w),family_mem 5 3 (target w) hw.1,?_⟩
    exact validWitness_sound 5 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N5R3C1

/- Source: MatroidCatalogue/Cases/N5R3C2Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N5R3C2

abbrev U := N5R3.grid
noncomputable def old : Finset (Finset (Fin 8)) := N4R3.family 2
noncomputable def newIndexTree : Table ℕ := (.node 3 (.node 1 (.leaf 4) (.node 2 (.leaf 5) (.leaf 6))) (.node 4 (.leaf 7) (.node 5 (.leaf 8) (.leaf 9))))
noncomputable def newIndex (i : Fin 6) : Fin 10 := Fin.ofNat 10 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 7 (.node 3 (.node 1 (.leaf (52,5,16423120)) (.node 2 (.leaf (42,5,16423106)) (.leaf (30,6,16419025)))) (.node 5 (.node 4 (.leaf (62,7,16427208)) (.leaf (25,5,16422938))) (.node 6 (.leaf (7,5,16421146)) (.leaf (31,7,16425507))))) (.node 10 (.node 8 (.leaf (45,6,16418969)) (.node 9 (.leaf (61,7,16427096)) (.leaf (47,7,16425731)))) (.node 12 (.node 11 (.leaf (51,6,16418073)) (.leaf (59,7,16427075))) (.node 13 (.leaf (55,7,16425752)) (.leaf (63,8,16434824))))))

noncomputable def models (i : Fin 14) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 14) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 14) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 10, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (4 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 10, (4 : Fin 8) ∈ U i → ∃ j : Fin 6, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N5R3C2

/- Source: MatroidCatalogue/Cases/N5R3C2Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N5R3C2


noncomputable def certificates_0 : List (Origin 10 14 × List Sat.Literal) :=
  [((.fixed 0),[(.pos 0)]),
   ((.fixed 1),[(.pos 1)]),
   ((.fixed 2),[(.pos 2)]),
   ((.fixed 3),[(.pos 3)]),
   ((.exchange 4 2 1),[(.neg 4),(.neg 2),(.pos 5),(.pos 7)]),
   ((.exchange 4 3 0),[(.neg 4),(.neg 3),(.pos 6),(.pos 8)]),
   ((.exchange 5 1 2),[(.neg 5),(.neg 1),(.pos 4),(.pos 7)]),
   ((.exchange 5 3 0),[(.neg 5),(.neg 3),(.pos 6),(.pos 9)]),
   ((.exchange 6 1 2),[(.neg 6),(.neg 1),(.pos 4),(.pos 8)]),
   ((.exchange 6 2 1),[(.neg 6),(.neg 2),(.pos 5),(.pos 9)]),
   ((.exchange 6 7 1),[(.neg 7),(.neg 6),(.pos 5),(.pos 9)]),
   ((.exchange 7 0 3),[(.neg 7),(.neg 0),(.pos 4),(.pos 5)]),
   ((.exchange 7 3 0),[(.neg 7),(.neg 3),(.pos 8),(.pos 9)]),
   ((.exchange 7 6 0),[(.neg 7),(.neg 6),(.pos 8),(.pos 9)]),
   ((.exchange 8 0 3),[(.neg 8),(.neg 0),(.pos 4),(.pos 6)]),
   ((.exchange 8 2 1),[(.neg 8),(.neg 2),(.pos 7),(.pos 9)]),
   ((.exchange 9 0 3),[(.neg 9),(.neg 0),(.pos 5),(.pos 6)]),
   ((.exchange 9 1 2),[(.neg 9),(.neg 1),(.pos 7),(.pos 8)]),
   ((.exchange 9 4 2),[(.neg 9),(.neg 4),(.pos 7),(.pos 8)]),
   (.newPoint,[(.pos 4),(.pos 5),(.pos 6),(.pos 7),(.pos 8),(.pos 9)]),
   ((.excluded 0),[(.neg 9),(.neg 8),(.neg 6),(.pos 4),(.pos 5),(.pos 7)]),
   ((.excluded 1),[(.neg 9),(.neg 7),(.neg 5),(.pos 4),(.pos 6),(.pos 8)]),
   ((.excluded 2),[(.neg 8),(.neg 7),(.neg 6),(.neg 5),(.pos 4),(.pos 9)]),
   ((.excluded 3),[(.neg 9),(.neg 8),(.neg 7),(.neg 6),(.neg 5),(.pos 4)]),
   ((.excluded 4),[(.neg 8),(.neg 7),(.neg 4),(.pos 5),(.pos 6),(.pos 9)]),
   ((.excluded 5),[(.neg 6),(.neg 5),(.neg 4),(.pos 7),(.pos 8),(.pos 9)]),
   ((.excluded 6),[(.neg 8),(.neg 7),(.neg 6),(.neg 5),(.neg 4),(.pos 9)]),
   ((.excluded 7),[(.neg 9),(.neg 7),(.neg 6),(.neg 4),(.pos 5),(.pos 8)]),
   ((.excluded 8),[(.neg 9),(.neg 8),(.neg 7),(.neg 6),(.neg 4),(.pos 5)]),
   ((.excluded 9),[(.neg 9),(.neg 7),(.neg 6),(.neg 5),(.neg 4),(.pos 8)]),
   ((.excluded 10),[(.neg 9),(.neg 8),(.neg 5),(.neg 4),(.pos 6),(.pos 7)]),
   ((.excluded 11),[(.neg 9),(.neg 8),(.neg 7),(.neg 5),(.neg 4),(.pos 6)]),
   ((.excluded 12),[(.neg 9),(.neg 8),(.neg 6),(.neg 5),(.neg 4),(.pos 7)]),
   ((.excluded 13),[(.neg 9),(.neg 8),(.neg 7),(.neg 6),(.neg 5),(.neg 4)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (4 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 14,
    let w : Fin 14 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 5 3 ∧
      ValidWitness 5 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 5 3 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N5R3C2

/- Source: MatroidCatalogue/Cases/N5R3C2Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N5R3C2

noncomputable def certificates : List (Origin 10 14 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (4 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 14,
    target w < MatroidCatalogue.count 5 3 ∧
      ValidWitness 5 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 5 3 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 14) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 5) 3)
    (hold : M.bases.filter ((4 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 5 3, IsomorphicWithin 5 M.bases B := by
  apply extension_covered_of_certificate (n:=4) (r:=3) (by decide)
    catalogue old U newIndex models certificates
    N5R3.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N5R3C2.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N5R3C2.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 5 3 (target w),family_mem 5 3 (target w) hw.1,?_⟩
    exact validWitness_sound 5 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N5R3C2

/- Source: MatroidCatalogue/Cases/N5R4C0Data.lean -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates

open Papers.RationalityTen.BasisExtensionCNF
namespace Papers.RationalityTen.MatroidCatalogue.Cases.N5R4C0

abbrev U := N5R4.grid
noncomputable def old : Finset (Finset (Fin 8)) := N4R4.family 0
noncomputable def newIndexTree : Table ℕ := (.node 2 (.node 1 (.leaf 1) (.leaf 2)) (.node 3 (.leaf 3) (.leaf 4)))
noncomputable def newIndex (i : Fin 4) : Fin 5 := Fin.ofNat 5 (newIndexTree.get i.val)

noncomputable def witnessTree : Table (ℕ × ℕ × ℕ) :=
  (.node 7 (.node 3 (.node 1 (.leaf (8,0,16423120)) (.node 2 (.leaf (4,0,16423106)) (.leaf (12,1,16427208)))) (.node 5 (.node 4 (.leaf (2,0,16422938)) (.leaf (10,1,16427096))) (.node 6 (.leaf (6,1,16427075)) (.leaf (14,2,16431240))))) (.node 11 (.node 9 (.node 8 (.leaf (1,0,16421146)) (.leaf (9,1,16425752))) (.node 10 (.leaf (5,1,16425731)) (.leaf (13,2,16430344)))) (.node 13 (.node 12 (.leaf (3,1,16425507)) (.leaf (11,2,16430176))) (.node 14 (.leaf (7,2,16430148)) (.leaf (15,3,16434824))))))

noncomputable def models (i : Fin 15) : ℕ := (witnessTree.get i.val).1
noncomputable def target (i : Fin 15) : ℕ := (witnessTree.get i.val).2.1
noncomputable def permutation (i : Fin 15) : ℕ := (witnessTree.get i.val).2.2

theorem old_complete : ∀ A ∈ old, ∃ i : Fin 5, U i = A := by decide +kernel
theorem old_avoids : ∀ A ∈ old, (4 : Fin 8) ∉ A := by decide +kernel
theorem new_complete : ∀ i : Fin 5, (4 : Fin 8) ∈ U i → ∃ j : Fin 4, newIndex j = i := by decide +kernel

end Papers.RationalityTen.MatroidCatalogue.Cases.N5R4C0

/- Source: MatroidCatalogue/Cases/N5R4C0Checks.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N5R4C0


noncomputable def certificates_0 : List (Origin 5 15 × List Sat.Literal) :=
  [(.newPoint,[(.pos 1),(.pos 2),(.pos 3),(.pos 4)]),
   ((.excluded 0),[(.neg 4),(.pos 1),(.pos 2),(.pos 3)]),
   ((.excluded 1),[(.neg 3),(.pos 1),(.pos 2),(.pos 4)]),
   ((.excluded 2),[(.neg 4),(.neg 3),(.pos 1),(.pos 2)]),
   ((.excluded 3),[(.neg 2),(.pos 1),(.pos 3),(.pos 4)]),
   ((.excluded 4),[(.neg 4),(.neg 2),(.pos 1),(.pos 3)]),
   ((.excluded 5),[(.neg 3),(.neg 2),(.pos 1),(.pos 4)]),
   ((.excluded 6),[(.neg 4),(.neg 3),(.neg 2),(.pos 1)]),
   ((.excluded 7),[(.neg 1),(.pos 2),(.pos 3),(.pos 4)]),
   ((.excluded 8),[(.neg 4),(.neg 1),(.pos 2),(.pos 3)]),
   ((.excluded 9),[(.neg 3),(.neg 1),(.pos 2),(.pos 4)]),
   ((.excluded 10),[(.neg 4),(.neg 3),(.neg 1),(.pos 2)]),
   ((.excluded 11),[(.neg 2),(.neg 1),(.pos 3),(.pos 4)]),
   ((.excluded 12),[(.neg 4),(.neg 2),(.neg 1),(.pos 3)]),
   ((.excluded 13),[(.neg 3),(.neg 2),(.neg 1),(.pos 4)]),
   ((.excluded 14),[(.neg 4),(.neg 3),(.neg 2),(.neg 1)])]

theorem certificates_0_valid : ∀ oc ∈ certificates_0,
    ValidOrigin U (4 : Fin 8) old newIndex models oc.1 oc.2 := by
  decide +kernel



theorem witness_0 : ∀ j : Fin 15,
    let w : Fin 15 := ⟨0 + j.val,by omega⟩
    target w < MatroidCatalogue.count 5 4 ∧
      ValidWitness 5 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 5 4 (target w)) (permutation w) := by
  decide +kernel


end Papers.RationalityTen.MatroidCatalogue.Cases.N5R4C0

/- Source: MatroidCatalogue/Cases/N5R4C0Coverage.lean -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
open Papers.RationalityTen.BasisExtensionCNF

namespace Papers.RationalityTen.MatroidCatalogue.Cases.N5R4C0

noncomputable def certificates : List (Origin 5 15 × List Sat.Literal) :=
  certificates_0

theorem certificates_valid : ∀ oc ∈ certificates,
    ValidOrigin U (4 : Fin 8) old newIndex models oc.1 oc.2 := by
  exact certificates_0_valid

theorem models_valid : ∀ w : Fin 15,
    target w < MatroidCatalogue.count 5 4 ∧
      ValidWitness 5 (extensionFamily old U newIndex (models w))
        (MatroidCatalogue.family 5 4 (target w)) (permutation w) := by
  intro w
  have hbound := w.isLt
  have hh := witness_0 ⟨w.val - 0,by omega⟩
  have heq : (⟨0 + (w.val - 0),by omega⟩ : Fin 15) = w := Fin.ext (by dsimp only; omega)
  dsimp only at hh
  rw [heq] at hh
  exact hh

theorem coverage (M : BasisFamily (groundPrefix 5) 4)
    (hold : M.bases.filter ((4 : Fin 8) ∉ ·) = old) :
    ∃ B ∈ catalogue 5 4, IsomorphicWithin 5 M.bases B := by
  apply extension_covered_of_certificate (n:=4) (r:=4) (by decide)
    catalogue old U newIndex models certificates
    N5R4.grid_complete old_complete old_avoids new_complete certificates_valid
  · change Sat.Fmla.proof Papers.RationalityTen.MatroidCases.N5R4C0.extension.formula []
    exact Papers.RationalityTen.MatroidCases.N5R4C0.extension.refutation
  · intro w
    have hw := models_valid w
    refine ⟨MatroidCatalogue.family 5 4 (target w),family_mem 5 4 (target w) hw.1,?_⟩
    exact validWitness_sound 5 _ _ (permutation w) hw.2
  · exact hold

end Papers.RationalityTen.MatroidCatalogue.Cases.N5R4C0

