module
public import shared_results.part003
public import graph_results.augmented_chain_contraction

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.ProjectedResolutionBaseChange -/
section

/-!
# Degreewise split exactness of the projected resolution

The coefficient-linear homotopy on the total module need not preserve the
chosen homological grading. Projecting each of its values to the next degree
produces the actual degreewise augmented contraction. Its identities then
prove exactness after every coefficient base change, without a flatness
hypothesis.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option synthInstance.maxHeartbeats 5000
set_option maxRecDepth 4096
noncomputable section

namespace FourPapers.ProjectedFreeResolution

open CommAlg
open scoped TensorProduct

universe u
variable {R S F M : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup F] [Module S F] [Module R F] [IsScalarTower R S F]
  [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
  {I : Type*} (b : Module.Basis I S F) (degree : I → ℕ)
  (D : Module.End S F) (ε : F →ₗ[S] M)
  (C : HomologicalPerturbation.LinearDeformationRetract (R := R) (M := F) (H := M))
  (hD : C.sourceD = D.restrictScalars R)
  (hε : C.projection = ε.restrictScalars R)
  (ht : C.targetD = 0)
  (hlower : ∀ p, D.comp (projection b degree (p+1)) = (projection b degree p).comp D)
  (hzero : D.comp (projection b degree 0) = 0)
  (hεzero : ε.comp (projection b degree 0) = ε)

def projectedDifferential (p : ℕ) : piece b degree (p+1) →ₗ[R] piece b degree p :=
  ((data b degree D C hD hlower).differential p).restrictScalars R

def projectedHomotopy (p : ℕ) : piece b degree p →ₗ[R] piece b degree (p+1) where
  toFun x := ⟨projection b degree (p+1) (C.homotopy x.val),
    Grading.projection_mem _ _ _ _⟩
  map_add' x y := by apply Subtype.ext; simp
  map_smul' a x := by apply Subtype.ext; simp

def projectedSection : M →ₗ[R] piece b degree 0 where
  toFun m := ⟨projection b degree 0 (C.inclusion m), Grading.projection_mem _ _ _ _⟩
  map_add' x y := by apply Subtype.ext; simp
  map_smul' a x := by apply Subtype.ext; simp

include hε hεzero in
theorem projectedSection_retract :
    ((augmentationZero b degree ε).restrictScalars R).comp
      (projectedSection b degree C) = LinearMap.id := by
  apply LinearMap.ext
  intro m
  change ε (projection b degree 0 (C.inclusion m)) = m
  have hz := LinearMap.congr_fun hεzero (C.inclusion m)
  change ε (projection b degree 0 (C.inclusion m)) = ε (C.inclusion m) at hz
  rw [hz]
  have he := C.projection_inclusion m
  rw [hε] at he
  exact he

include hε hzero in
theorem projectedHomotopy_zero :
    (projectedDifferential b degree D C hD hlower 0).comp
      (projectedHomotopy b degree C 0) =
    LinearMap.id - (projectedSection b degree C).comp
      ((augmentationZero b degree ε).restrictScalars R) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change D (projection b degree 1 (C.homotopy x.val)) =
    x.val - projection b degree 0 (C.inclusion (ε x.val))
  have hz := LinearMap.congr_fun (hlower 0) (C.homotopy x.val)
  change D (projection b degree 1 (C.homotopy x.val)) =
    projection b degree 0 (D (C.homotopy x.val)) at hz
  rw [hz]
  have he := LinearMap.congr_fun C.deformation x.val
  rw [hD, hε] at he
  change D (C.homotopy x.val) + C.homotopy (D x.val) =
    x.val - C.inclusion (ε x.val) at he
  rw [zero_degree_cycle b degree D hzero x, map_zero, add_zero] at he
  rw [he, map_sub, Grading.projection_eq_self x.property]

include ε hε hεzero in
theorem projectedHomotopy_succ (p : ℕ) :
    (projectedDifferential b degree D C hD hlower (p+1)).comp
        (projectedHomotopy b degree C (p+1)) +
      (projectedHomotopy b degree C p).comp
        (projectedDifferential b degree D C hD hlower p) =
    LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change D (projection b degree (p+1+1) (C.homotopy x.val)) +
    projection b degree (p+1) (C.homotopy (D x.val)) = x.val
  have hz := LinearMap.congr_fun (hlower (p+1)) (C.homotopy x.val)
  change D (projection b degree (p+1+1) (C.homotopy x.val)) =
    projection b degree (p+1) (D (C.homotopy x.val)) at hz
  rw [hz, ← map_add]
  have he := LinearMap.congr_fun C.deformation x.val
  rw [hD, hε] at he
  change D (C.homotopy x.val) + C.homotopy (D x.val) =
    x.val - C.inclusion (ε x.val) at he
  rw [augmentation_positive b degree ε hεzero p x, map_zero, sub_zero] at he
  rw [he, Grading.projection_eq_self x.property]

/-- The actual homological terms, differentials, and augmentation admit a
coefficient-linear contraction. The maps are built from the given splitting;
this is stronger than a mere exactness proposition. -/
def augmentedContraction : AugmentedChainContraction R (fun p => ↥(piece b degree p)) M where
  d p := projectedDifferential b degree D C hD hlower p
  augmentation := (augmentationZero b degree ε).restrictScalars R
  homotopy := projectedHomotopy b degree C
  sectionMap := projectedSection b degree C
  square p := by
    apply LinearMap.ext
    intro x
    exact LinearMap.congr_fun ((data b degree D C hD hlower).differential_comp p) x
  augmentation_boundary := by
    apply LinearMap.ext
    intro x
    exact LinearMap.congr_fun (augmentationZero_comp b degree D ε C hD hε ht hlower) x
  retract := projectedSection_retract b degree ε C hε hεzero
  contraction_zero := projectedHomotopy_zero b degree D ε C hD hε hlower hzero
  contraction_succ := projectedHomotopy_succ b degree D ε C hD hε hlower hεzero

variable (T : Type*) [CommRing T] [Algebra R T]

/-- Tensoring the displayed augmented chain complex with an arbitrary
coefficient algebra preserves its explicit contraction and exactness. -/
def baseChangeContraction : AugmentedChainContraction T
    (fun p => T ⊗[R] piece b degree p) (T ⊗[R] M) :=
  (augmentedContraction b degree D ε C hD hε ht hlower hzero hεzero).baseChange T

include hε ht hzero hεzero in
theorem baseChange_exact_at_augmentation :
    Function.Exact
      ((projectedDifferential b degree D C hD hlower 0).baseChange T)
      (((augmentationZero b degree ε).restrictScalars R).baseChange T) :=
  (baseChangeContraction b degree D ε C hD hε ht hlower hzero hεzero T).exact_augmentation

include ε hε ht hzero hεzero in
theorem baseChange_exact_positive (p : ℕ) :
    Function.Exact
      ((projectedDifferential b degree D C hD hlower (p+1)).baseChange T)
      ((projectedDifferential b degree D C hD hlower p).baseChange T) :=
  (baseChangeContraction b degree D ε C hD hε ht hlower hzero hεzero T).exact_positive p

include D C hD hε ht hlower hzero hεzero in
theorem baseChange_augmentation_surjective :
    Function.Surjective (((augmentationZero b degree ε).restrictScalars R).baseChange T) :=
  (baseChangeContraction b degree D ε C hD hε ht hlower hzero hεzero T).augmentation_surjective

end FourPapers.ProjectedFreeResolution

end
end
end


end
