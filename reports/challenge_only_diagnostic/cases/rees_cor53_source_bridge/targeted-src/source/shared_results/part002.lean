module
public import graph_foundation.part001
public import shared_results.part001

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.ContractionTensor -/
section

/-!
# Tensoring contractions with an arbitrary coefficient module

The coefficient module need not be flat. Tensoring the explicit splitting
identities directly proves all eight identities for the new complex. This
is used for the polynomial diagonal resolution and for arbitrary parameter
base changes.
-/

section
set_option autoImplicit false
noncomputable section

namespace FourPapers.HomologicalPerturbation.LinearContraction

open scoped TensorProduct

variable {R M H H' : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H]
  [AddCommGroup H'] [Module R H']
  (C : LinearContraction (R := R) (M := M) (H := H))

/-- Reidentify the actual target by an established linear equivalence. -/
def changeTarget (e : H ≃ₗ[R] H') :
    LinearContraction (R := R) (M := M) (H := H') where
  d := C.d
  h := C.h
  inclusion := C.inclusion.comp e.symm.toLinearMap
  projection := e.toLinearMap.comp C.projection
  differential := C.differential
  retract := by
    ext x
    change e (C.projection (C.inclusion (e.symm x))) = x
    rw [C.projection_inclusion_apply, e.apply_symm_apply]
  inclusion_cycle := by
    ext x
    exact C.differential_inclusion_apply (e.symm x)
  projection_boundary := by
    ext x
    change e (C.projection (C.d x)) = 0
    rw [C.projection_differential_apply, map_zero]
  homotopy := by
    rw [C.homotopy]
    congr 1
    ext x
    change C.inclusion (C.projection x) =
      C.inclusion (e.symm (e (C.projection x)))
    rw [e.symm_apply_apply]
  squareHomotopy := C.squareHomotopy
  homotopyInclusion := by
    ext x
    exact C.homotopy_inclusion_apply (e.symm x)
  projectionHomotopy := by
    ext x
    change e (C.projection (C.h x)) = 0
    rw [C.projection_homotopy_apply, map_zero]

variable {N : Type*} [AddCommGroup N] [Module R N]

/-- Transport the source through a proved coordinate equivalence. All
differentials and homotopies are conjugated, with their identities retained. -/
def changeSource (e : M ≃ₗ[R] N) :
    LinearContraction (R := R) (M := N) (H := H) where
  d := e.toLinearMap.comp (C.d.comp e.symm.toLinearMap)
  h := e.toLinearMap.comp (C.h.comp e.symm.toLinearMap)
  inclusion := e.toLinearMap.comp C.inclusion
  projection := C.projection.comp e.symm.toLinearMap
  differential := by
    ext x
    change e (C.d (e.symm (e (C.d (e.symm x))))) = 0
    rw [e.symm_apply_apply]
    have hz : C.d (C.d (e.symm x)) = 0 := LinearMap.congr_fun C.differential (e.symm x)
    rw [hz, map_zero]
  retract := by
    ext x
    change C.projection (e.symm (e (C.inclusion x))) = x
    rw [e.symm_apply_apply, C.projection_inclusion_apply]
  inclusion_cycle := by
    ext x
    change e (C.d (e.symm (e (C.inclusion x)))) = 0
    rw [e.symm_apply_apply, C.differential_inclusion_apply, map_zero]
  projection_boundary := by
    ext x
    change C.projection (e.symm (e (C.d (e.symm x)))) = 0
    rw [e.symm_apply_apply, C.projection_differential_apply]
  homotopy := by
    ext x
    change e (C.d (e.symm (e (C.h (e.symm x))))) +
      e (C.h (e.symm (e (C.d (e.symm x))))) =
        x - e (C.inclusion (C.projection (e.symm x)))
    rw [e.symm_apply_apply, e.symm_apply_apply, ← map_add]
    have he := LinearMap.congr_fun C.homotopy (e.symm x)
    change C.d (C.h (e.symm x)) + C.h (C.d (e.symm x)) =
      e.symm x - C.inclusion (C.projection (e.symm x)) at he
    rw [he, map_sub, e.apply_symm_apply]
  squareHomotopy := by
    ext x
    change e (C.h (e.symm (e (C.h (e.symm x))))) = 0
    rw [e.symm_apply_apply, C.homotopy_square_apply, map_zero]
  homotopyInclusion := by
    ext x
    change e (C.h (e.symm (e (C.inclusion x)))) = 0
    rw [e.symm_apply_apply, C.homotopy_inclusion_apply, map_zero]
  projectionHomotopy := by
    ext x
    change C.projection (e.symm (e (C.h (e.symm x)))) = 0
    rw [e.symm_apply_apply, C.projection_homotopy_apply]

/-- The ordinary tensor product of an actual contraction with a module. -/
def tensorRight (N : Type*) [AddCommGroup N] [Module R N] : LinearContraction
    (R := R) (M := M ⊗[R] N) (H := H ⊗[R] N) where
  d := C.d.rTensor N
  h := C.h.rTensor N
  inclusion := C.inclusion.rTensor N
  projection := C.projection.rTensor N
  differential := by
    rw [← LinearMap.rTensor_mul, C.differential, LinearMap.rTensor_zero]
  retract := by
    rw [← LinearMap.rTensor_comp, C.retract, LinearMap.rTensor_id]
  inclusion_cycle := by
    rw [← LinearMap.rTensor_comp, C.inclusion_cycle, LinearMap.rTensor_zero]
  projection_boundary := by
    rw [← LinearMap.rTensor_comp, C.projection_boundary, LinearMap.rTensor_zero]
  homotopy := by
    rw [← LinearMap.rTensor_mul, ← LinearMap.rTensor_mul,
      ← LinearMap.rTensor_add, C.homotopy, LinearMap.rTensor_sub,
      LinearMap.rTensor_comp]
    simp only [Module.End.one_eq_id, LinearMap.rTensor_id]
  squareHomotopy := by
    rw [← LinearMap.rTensor_mul, C.squareHomotopy, LinearMap.rTensor_zero]
  homotopyInclusion := by
    rw [← LinearMap.rTensor_comp, C.homotopyInclusion, LinearMap.rTensor_zero]
  projectionHomotopy := by
    rw [← LinearMap.rTensor_comp, C.projectionHomotopy, LinearMap.rTensor_zero]

@[simp] theorem tensorRight_d_tmul (x : M) (n : N) :
    (C.tensorRight N).d (x ⊗ₜ[R] n) = C.d x ⊗ₜ[R] n := rfl

@[simp] theorem tensorRight_h_tmul (x : M) (n : N) :
    (C.tensorRight N).h (x ⊗ₜ[R] n) = C.h x ⊗ₜ[R] n := rfl

@[simp] theorem tensorRight_inclusion_tmul (x : H) (n : N) :
    (C.tensorRight N).inclusion (x ⊗ₜ[R] n) = C.inclusion x ⊗ₜ[R] n := rfl

@[simp] theorem tensorRight_projection_tmul (x : M) (n : N) :
    (C.tensorRight N).projection (x ⊗ₜ[R] n) = C.projection x ⊗ₜ[R] n := rfl

end FourPapers.HomologicalPerturbation.LinearContraction

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.LinearDeformationRetract -/
section

/-!
# A deformation retract with nonzero target differential

This packages the output of the perturbation construction as actual linear
chain maps and an actual chain homotopy. The identities, and hence the cycle
and boundary correspondences, survive arbitrary tensor extension.
-/

section
set_option autoImplicit false
noncomputable section

namespace FourPapers.HomologicalPerturbation

open scoped TensorProduct

variable {R M H : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H]

structure LinearDeformationRetract where
  sourceD : Module.End R M
  targetD : Module.End R H
  inclusion : H →ₗ[R] M
  projection : M →ₗ[R] H
  homotopy : Module.End R M
  source_square : sourceD * sourceD = 0
  target_square : targetD * targetD = 0
  inclusion_chain : sourceD.comp inclusion = inclusion.comp targetD
  projection_chain : projection.comp sourceD = targetD.comp projection
  retract : projection.comp inclusion = LinearMap.id
  deformation : sourceD * homotopy + homotopy * sourceD =
    1 - inclusion.comp projection

namespace LinearContraction

variable (C : LinearContraction (R := R) (M := M) (H := H))
  (δ : Module.End R M) (u v : (Module.End R M)ˣ)
  (hu : (u : Module.End R M) = 1 + δ * C.h)
  (hv : (v : Module.End R M) = 1 + C.h * δ)
  (hD : (C.d + δ) * (C.d + δ) = 0)

/-- The perturbation identities give a genuine deformation retract. -/
def perturb : LinearDeformationRetract (R := R) (M := M) (H := H) where
  sourceD := C.d + δ
  targetD := C.transferredDifferential δ u
  inclusion := C.transferredInclusion δ u
  projection := C.transferredProjection δ u
  homotopy := C.transferredHomotopy δ u
  source_square := hD
  target_square := C.transferredDifferential_square δ u v hu hv hD
  inclusion_chain := C.transferred_inclusion_chain δ u v hu hv hD
  projection_chain := C.transferred_projection_chain δ u v hu hv hD
  retract := C.transferred_retract δ u
  deformation := C.transferred_homotopy_identity δ u v hu hv hD

end LinearContraction

namespace LinearDeformationRetract

variable (C : LinearDeformationRetract (R := R) (M := M) (H := H))

@[simp] theorem projection_inclusion (x : H) :
    C.projection (C.inclusion x) = x := LinearMap.congr_fun C.retract x

theorem inclusion_injective : Function.Injective C.inclusion := by
  intro x y h
  have he := congrArg C.projection h
  simpa only [C.projection_inclusion] using he

theorem inclusion_differential (x : H) :
    C.sourceD (C.inclusion x) = C.inclusion (C.targetD x) :=
  LinearMap.congr_fun C.inclusion_chain x

theorem projection_differential (x : M) :
    C.projection (C.sourceD x) = C.targetD (C.projection x) :=
  LinearMap.congr_fun C.projection_chain x

theorem cycle_iff (x : H) : C.targetD x = 0 ↔ C.sourceD (C.inclusion x) = 0 := by
  rw [C.inclusion_differential]
  constructor
  · intro h
    rw [h, map_zero]
  · intro h
    apply C.inclusion_injective
    rw [map_zero]
    exact h

/-- Boundaries correspond in both directions, including the actual chosen
preimage. This is the exactness implication used by a transferred resolution. -/
theorem boundary_iff (x : H) :
    (∃ y, C.targetD y = x) ↔ ∃ z, C.sourceD z = C.inclusion x := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨C.inclusion y, C.inclusion_differential y⟩
  · rintro ⟨z, hz⟩
    refine ⟨C.projection z, ?_⟩
    rw [← C.projection_differential, hz, C.projection_inclusion]

/-- Every source cycle differs from its transferred representative by the
explicit boundary supplied by the homotopy. -/
theorem cycle_decomposition (x : M) (hx : C.sourceD x = 0) :
    x = C.inclusion (C.projection x) + C.sourceD (C.homotopy x) := by
  have he := LinearMap.congr_fun C.deformation x
  change C.sourceD (C.homotopy x) + C.homotopy (C.sourceD x) =
    x - C.inclusion (C.projection x) at he
  rw [hx, map_zero, add_zero] at he
  rw [he]
  abel

/-- A cycle whose projected class is a boundary is itself a boundary, with
an explicit preimage. -/
theorem boundary_of_projected_boundary (x : M) (hx : C.sourceD x = 0)
    (y : H) (hy : C.targetD y = C.projection x) :
    C.sourceD (C.inclusion y + C.homotopy x) = x := by
  rw [map_add, C.inclusion_differential, hy]
  exact (C.cycle_decomposition x hx).symm

variable (S : Type*) [CommRing S] [Algebra R S]

/-- Arbitrary base change of the actual chain maps and homotopy. No
flatness hypothesis on `S` appears or is needed. -/
def baseChange : LinearDeformationRetract
    (R := S) (M := S ⊗[R] M) (H := S ⊗[R] H) where
  sourceD := C.sourceD.baseChange S
  targetD := C.targetD.baseChange S
  inclusion := C.inclusion.baseChange S
  projection := C.projection.baseChange S
  homotopy := C.homotopy.baseChange S
  source_square := by
    rw [← LinearMap.baseChange_mul, C.source_square, LinearMap.baseChange_zero]
  target_square := by
    rw [← LinearMap.baseChange_mul, C.target_square, LinearMap.baseChange_zero]
  inclusion_chain := by
    rw [← LinearMap.baseChange_comp, C.inclusion_chain, LinearMap.baseChange_comp]
  projection_chain := by
    rw [← LinearMap.baseChange_comp, C.projection_chain, LinearMap.baseChange_comp]
  retract := by
    rw [← LinearMap.baseChange_comp, C.retract, LinearMap.baseChange_id]
  deformation := by
    rw [← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul,
      ← LinearMap.baseChange_add, C.deformation, LinearMap.baseChange_sub,
      LinearMap.baseChange_one, LinearMap.baseChange_comp]

end LinearDeformationRetract
end FourPapers.HomologicalPerturbation

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.PerturbationMinimality -/
section

/-!
# Minimal matrix entries in the transferred differential

Every summand of the transferred differential contains the perturbation.
Consequently, if that perturbation has image in an ideal times the source,
the transferred differential has image in the same ideal times its target.
This statement concerns the literal matrix coefficients in any chosen basis.
For the polynomial construction the ideal is the ideal of all variables.
-/

section
set_option autoImplicit false
noncomputable section

namespace FourPapers.HomologicalPerturbation

variable {R M H : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H]

lemma linearMap_preserves_ideal_multiple (I : Ideal R) (f : M →ₗ[R] H)
    {x : M} (hx : x ∈ I • (⊤ : Submodule R M)) :
    f x ∈ I • (⊤ : Submodule R H) :=
  Submodule.smul_top_le_comap_smul_top I f hx

lemma basis_coefficient_mem_ideal {J : Type*} (b : Module.Basis J R M)
    (I : Ideal R) {x : M} (hx : x ∈ I • (⊤ : Submodule R M)) (j : J) :
    b.repr x j ∈ I := by
  have hc := linearMap_preserves_ideal_multiple I (b.coord j) hx
  simpa only [Module.Basis.coord_apply, Ideal.smul_eq_mul, Ideal.mul_top] using hc

namespace LinearContraction

variable (C : LinearContraction (R := R) (M := M) (H := H))
  (δ : Module.End R M) (u : (Module.End R M)ˣ)

/-- The actual correction operator keeps the required ideal factor. No
formal inverse series or unproved nilpotence assertion is used. -/
theorem correction_mem_ideal_multiple (I : Ideal R)
    (hδ : ∀ x, δ x ∈ I • (⊤ : Submodule R M)) (x : M) :
    correction u δ x ∈ I • (⊤ : Submodule R M) :=
  linearMap_preserves_ideal_multiple I (↑(u⁻¹) : Module.End R M) (hδ x)

theorem transferredDifferential_mem_ideal_multiple (I : Ideal R)
    (hδ : ∀ x, δ x ∈ I • (⊤ : Submodule R M)) (x : H) :
    C.transferredDifferential δ u x ∈ I • (⊤ : Submodule R H) :=
  linearMap_preserves_ideal_multiple I C.projection
    (correction_mem_ideal_multiple δ u I hδ (C.inclusion x))

/-- Every displayed matrix coefficient belongs to the variable ideal in the
polynomial application, which is the precise minimality assertion. -/
theorem transferredDifferential_basis_coefficient_mem {J : Type*}
    (b : Module.Basis J R H) (I : Ideal R)
    (hδ : ∀ x, δ x ∈ I • (⊤ : Submodule R M)) (i j : J) :
    b.repr (C.transferredDifferential δ u (b i)) j ∈ I :=
  basis_coefficient_mem_ideal b I
    (C.transferredDifferential_mem_ideal_multiple δ u I hδ (b i)) j

/-- Reduction along a ring map that kills the ideal makes every coefficient
of the differential zero. This includes each field residue of the parameter
ring followed by setting the polynomial variables to zero. -/
theorem transferredDifferential_basis_coefficient_map_zero
    {S J : Type*} [CommRing S] (φ : R →+* S)
    (b : Module.Basis J R H) (I : Ideal R) (hI : I ≤ RingHom.ker φ)
    (hδ : ∀ x, δ x ∈ I • (⊤ : Submodule R M)) (i j : J) :
    φ (b.repr (C.transferredDifferential δ u (b i)) j) = 0 :=
  hI (C.transferredDifferential_basis_coefficient_mem δ u b I hδ i j)

end LinearContraction
end FourPapers.HomologicalPerturbation

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.GradedPerturbation -/
section

/-!
# Homological degrees of the transferred differential

Actual degree projections record a nonnegative homological grading. The
contraction raises degree by one and the perturbation lowers degree by one.
The inverse of `1 + δh` commutes with every degree projection, so the
transferred differential lowers degree by one. Degree zero is treated
explicitly; no negative-degree component is suppressed by a convention.
-/

section
set_option autoImplicit false
noncomputable section

namespace FourPapers.HomologicalPerturbation.LinearContraction

variable {R M H : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H]
  (C : LinearContraction (R := R) (M := M) (H := H))
  (P : ℕ → Module.End R M) (Q : ℕ → Module.End R H)
  (δ : Module.End R M) (u : (Module.End R M)ˣ)
  (hu : (u : Module.End R M) = 1 + δ * C.h)
  (hh : ∀ p, C.h * P p = P (p+1) * C.h)
  (hh0 : P 0 * C.h = 0)
  (hδ : ∀ p, δ * P (p+1) = P p * δ)
  (hδ0 : δ * P 0 = 0)
  (hi : ∀ p, C.inclusion.comp (Q p) = (P p).comp C.inclusion)
  (hp : ∀ p, C.projection.comp (P p) = (Q p).comp C.projection)

include hu hh hδ in
theorem perturbationUnit_commutes_projection (p : ℕ) :
    Commute (u : Module.End R M) (P p) := by
  change (u : Module.End R M) * P p = P p * (u : Module.End R M)
  rw [hu, add_mul, mul_add, one_mul, mul_one]
  congr 1
  rw [mul_assoc, hh p, ← mul_assoc, hδ p, mul_assoc]

include hu hh hδ in
theorem correction_lowers_degree (p : ℕ) :
    correction u δ * P (p+1) = P p * correction u δ := by
  have hc := (C.perturbationUnit_commutes_projection P δ u hu hh hδ p).units_inv_left
  rw [correction, mul_assoc, hδ p, ← mul_assoc, hc.eq, mul_assoc]

include hδ0 in
theorem correction_zero_degree : correction u δ * P 0 = 0 := by
  rw [correction, mul_assoc, hδ0, mul_zero]

include hu hh hh0 hδ hδ0 in
theorem homotopy_correction_preserves_degree (p : ℕ) :
    (C.h * correction u δ) * P p = P p * (C.h * correction u δ) := by
  cases p with
  | zero =>
      rw [mul_assoc, correction_zero_degree P δ u hδ0, mul_zero,
        ← mul_assoc, hh0, zero_mul]
  | succ p =>
      rw [mul_assoc, C.correction_lowers_degree P δ u hu hh hδ p,
        ← mul_assoc, hh p, mul_assoc]

include hu hh hδ in
theorem correction_homotopy_preserves_degree (p : ℕ) :
    (correction u δ * C.h) * P p = P p * (correction u δ * C.h) := by
  rw [mul_assoc, hh p, ← mul_assoc,
    C.correction_lowers_degree P δ u hu hh hδ p, mul_assoc]

include hu hh hδ hi hp in
/-- The actual transferred differential has homological degree −1. -/
theorem transferredDifferential_lowers_degree (p : ℕ) :
    (C.transferredDifferential δ u).comp (Q (p+1)) =
      (Q p).comp (C.transferredDifferential δ u) := by
  ext x
  change C.projection (correction u δ (C.inclusion (Q (p+1) x))) =
    Q p (C.projection (correction u δ (C.inclusion x)))
  have hi' := LinearMap.congr_fun (hi (p+1)) x
  have ha' := LinearMap.congr_fun
    (C.correction_lowers_degree P δ u hu hh hδ p) (C.inclusion x)
  have hp' := LinearMap.congr_fun (hp p) (correction u δ (C.inclusion x))
  change C.inclusion (Q (p+1) x) = P (p+1) (C.inclusion x) at hi'
  change correction u δ (P (p+1) (C.inclusion x)) =
    P p (correction u δ (C.inclusion x)) at ha'
  change C.projection (P p (correction u δ (C.inclusion x))) =
    Q p (C.projection (correction u δ (C.inclusion x))) at hp'
  rw [hi', ha', hp']

include hδ0 hi in
theorem transferredDifferential_zero_degree :
    (C.transferredDifferential δ u).comp (Q 0) = 0 := by
  ext x
  change C.projection (correction u δ (C.inclusion (Q 0 x))) = 0
  have hi' := LinearMap.congr_fun (hi 0) x
  change C.inclusion (Q 0 x) = P 0 (C.inclusion x) at hi'
  rw [hi']
  have ha := LinearMap.congr_fun (correction_zero_degree P δ u hδ0) (C.inclusion x)
  change correction u δ (P 0 (C.inclusion x)) = 0 at ha
  rw [ha, map_zero]

include hu hh hh0 hδ hδ0 hi in
theorem transferredInclusion_preserves_degree (p : ℕ) :
    (C.transferredInclusion δ u).comp (Q p) =
      (P p).comp (C.transferredInclusion δ u) := by
  ext x
  change C.inclusion (Q p x) - C.h (correction u δ (C.inclusion (Q p x))) =
    P p (C.inclusion x - C.h (correction u δ (C.inclusion x)))
  have hi' := LinearMap.congr_fun (hi p) x
  change C.inclusion (Q p x) = P p (C.inclusion x) at hi'
  have hc := LinearMap.congr_fun
    (C.homotopy_correction_preserves_degree P δ u hu hh hh0 hδ hδ0 p) (C.inclusion x)
  change C.h (correction u δ (P p (C.inclusion x))) =
    P p (C.h (correction u δ (C.inclusion x))) at hc
  rw [hi', hc, map_sub]

include hu hh hδ hp in
theorem transferredProjection_preserves_degree (p : ℕ) :
    (C.transferredProjection δ u).comp (P p) =
      (Q p).comp (C.transferredProjection δ u) := by
  ext x
  change C.projection (P p x - correction u δ (C.h (P p x))) =
    Q p (C.projection (x - correction u δ (C.h x)))
  have hc := LinearMap.congr_fun
    (C.correction_homotopy_preserves_degree P δ u hu hh hδ p) x
  change correction u δ (C.h (P p x)) = P p (correction u δ (C.h x)) at hc
  rw [hc, ← map_sub]
  exact LinearMap.congr_fun (hp p) _

include hu hh hδ in
theorem transferredHomotopy_raises_degree (p : ℕ) :
    C.transferredHomotopy δ u * P p = P (p+1) * C.transferredHomotopy δ u := by
  change (C.h - C.h * correction u δ * C.h) * P p =
    P (p+1) * (C.h - C.h * correction u δ * C.h)
  rw [sub_mul, mul_sub, hh p]
  congr 1
  calc
    (C.h * correction u δ * C.h) * P p =
        C.h * correction u δ * (C.h * P p) := by noncomm_ring
    _ = C.h * correction u δ * (P (p+1) * C.h) := by rw [hh p]
    _ = C.h * (correction u δ * P (p+1)) * C.h := by noncomm_ring
    _ = C.h * (P p * correction u δ) * C.h := by
      rw [C.correction_lowers_degree P δ u hu hh hδ p]
    _ = (C.h * P p) * correction u δ * C.h := by noncomm_ring
    _ = P (p+1) * (C.h * correction u δ * C.h) := by
      rw [hh p]
      noncomm_ring

end FourPapers.HomologicalPerturbation.LinearContraction

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.ContractionRestriction -/
section

/-! # Restriction of the actual scalar-linear contraction identities -/

section
set_option autoImplicit false
noncomputable section

namespace FourPapers.HomologicalPerturbation.LinearContraction

variable {R M H : Type*} [CommRing R]
  [AddCommGroup M] [Module R M]
  [AddCommGroup H] [Module R H]
  (C : LinearContraction (R := R) (M := M) (H := H))

/-- Restricting scalars preserves the same maps and all eight identities. -/
def restrictScalars (K : Type*) [CommRing K] [Algebra K R]
    [Module K M] [IsScalarTower K R M]
    [Module K H] [IsScalarTower K R H] :
    LinearContraction (R := K) (M := M) (H := H) where
  d := C.d.restrictScalars K
  h := C.h.restrictScalars K
  inclusion := C.inclusion.restrictScalars K
  projection := C.projection.restrictScalars K
  differential := by ext x; exact LinearMap.congr_fun C.differential x
  retract := by ext x; exact LinearMap.congr_fun C.retract x
  inclusion_cycle := by ext x; exact LinearMap.congr_fun C.inclusion_cycle x
  projection_boundary := by ext x; exact LinearMap.congr_fun C.projection_boundary x
  homotopy := by ext x; exact LinearMap.congr_fun C.homotopy x
  squareHomotopy := by ext x; exact LinearMap.congr_fun C.squareHomotopy x
  homotopyInclusion := by ext x; exact LinearMap.congr_fun C.homotopyInclusion x
  projectionHomotopy := by ext x; exact LinearMap.congr_fun C.projectionHomotopy x

end FourPapers.HomologicalPerturbation.LinearContraction

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.LinearContractionBaseChange -/
section

/-!
# Arbitrary scalar extension of a strong deformation retract

The identities are transported through ordinary tensor extension. No flatness
assumption on the new coefficient ring is used. In particular, once an
augmented resolution is split over its parameter ring, its exactness survives
every parameter specialization, including non-flat specializations.
-/

section
set_option autoImplicit false
noncomputable section

namespace FourPapers.HomologicalPerturbation.LinearContraction

open scoped TensorProduct

variable {R M H : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H]
  (C : LinearContraction (R := R) (M := M) (H := H))
  (S : Type*) [CommRing S] [Algebra R S]

/-- Every identity of the contraction survives an arbitrary ring base
change. The target remains the tensor extension of the actual homology. -/
def baseChange : LinearContraction
    (R := S) (M := S ⊗[R] M) (H := S ⊗[R] H) where
  d := C.d.baseChange S
  h := C.h.baseChange S
  inclusion := C.inclusion.baseChange S
  projection := C.projection.baseChange S
  differential := by
    rw [← LinearMap.baseChange_mul, C.differential, LinearMap.baseChange_zero]
  retract := by
    rw [← LinearMap.baseChange_comp, C.retract, LinearMap.baseChange_id]
  inclusion_cycle := by
    rw [← LinearMap.baseChange_comp, C.inclusion_cycle, LinearMap.baseChange_zero]
  projection_boundary := by
    rw [← LinearMap.baseChange_comp, C.projection_boundary, LinearMap.baseChange_zero]
  homotopy := by
    rw [← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul,
      ← LinearMap.baseChange_add, C.homotopy, LinearMap.baseChange_sub,
      LinearMap.baseChange_one, LinearMap.baseChange_comp]
  squareHomotopy := by
    rw [← LinearMap.baseChange_mul, C.squareHomotopy, LinearMap.baseChange_zero]
  homotopyInclusion := by
    rw [← LinearMap.baseChange_comp, C.homotopyInclusion, LinearMap.baseChange_zero]
  projectionHomotopy := by
    rw [← LinearMap.baseChange_comp, C.projectionHomotopy, LinearMap.baseChange_zero]

@[simp] theorem baseChange_d_tmul (s : S) (x : M) :
    (C.baseChange S).d (s ⊗ₜ[R] x) = s ⊗ₜ[R] C.d x := rfl

@[simp] theorem baseChange_h_tmul (s : S) (x : M) :
    (C.baseChange S).h (s ⊗ₜ[R] x) = s ⊗ₜ[R] C.h x := rfl

@[simp] theorem baseChange_inclusion_tmul (s : S) (x : H) :
    (C.baseChange S).inclusion (s ⊗ₜ[R] x) = s ⊗ₜ[R] C.inclusion x := rfl

@[simp] theorem baseChange_projection_tmul (s : S) (x : M) :
    (C.baseChange S).projection (s ⊗ₜ[R] x) = s ⊗ₜ[R] C.projection x := rfl

/-- On the acyclic summand, the identity gives an actual boundary for every
cycle. This continues to hold after any specialization of the coefficients. -/
theorem baseChange_cycle_boundary (x : S ⊗[R] M)
    (hx : (C.baseChange S).d x = 0)
    (hp : (C.baseChange S).projection x = 0) :
    (C.baseChange S).d ((C.baseChange S).h x) = x := by
  have he := LinearMap.congr_fun (C.baseChange S).homotopy x
  change (C.baseChange S).d ((C.baseChange S).h x) +
    (C.baseChange S).h ((C.baseChange S).d x) =
      x - (C.baseChange S).inclusion ((C.baseChange S).projection x) at he
  simpa only [hx, hp, map_zero, add_zero, sub_zero] using he

end FourPapers.HomologicalPerturbation.LinearContraction

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.ContractionSign -/
section

/-! # Reversing the sign of a differential and its contraction -/

section
set_option autoImplicit false
noncomputable section

namespace FourPapers.HomologicalPerturbation.LinearContraction

variable {R M H : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H]
  (C : LinearContraction (R := R) (M := M) (H := H))

def negDifferential : LinearContraction (R := R) (M := M) (H := H) where
  d := -C.d
  h := -C.h
  inclusion := C.inclusion
  projection := C.projection
  differential := by simpa only [neg_mul_neg] using C.differential
  retract := C.retract
  inclusion_cycle := by
    ext x
    change -(C.d (C.inclusion x)) = 0
    rw [C.differential_inclusion_apply, neg_zero]
  projection_boundary := by
    ext x
    change C.projection (-C.d x) = 0
    rw [map_neg, C.projection_differential_apply, neg_zero]
  homotopy := by simpa only [neg_mul_neg] using C.homotopy
  squareHomotopy := by simpa only [neg_mul_neg] using C.squareHomotopy
  homotopyInclusion := by
    ext x
    change -(C.h (C.inclusion x)) = 0
    rw [C.homotopy_inclusion_apply, neg_zero]
  projectionHomotopy := by
    ext x
    change C.projection (-C.h x) = 0
    rw [map_neg, C.projection_homotopy_apply, neg_zero]

end FourPapers.HomologicalPerturbation.LinearContraction

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.TransferredAugmentation -/
section

/-!
# Exactness of a transferred complex with its actual augmentation

A deformation retract of a split resolution inherits a split augmentation.
The new augmentation is the original augmentation composed with the actual
inclusion of the transferred complex. All identities are explicit linear
identities and therefore survive arbitrary coefficient base change.
-/

section
set_option autoImplicit false
noncomputable section

namespace FourPapers.HomologicalPerturbation.LinearDeformationRetract

variable {R M H Q : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H]
  [AddCommGroup Q] [Module R Q]

variable (P : LinearDeformationRetract (R := R) (M := M) (H := H))

def restrictScalars (K : Type*) [CommRing K] [Algebra K R]
    [Module K M] [IsScalarTower K R M]
    [Module K H] [IsScalarTower K R H] :
    LinearDeformationRetract (R := K) (M := M) (H := H) where
  sourceD := P.sourceD.restrictScalars K
  targetD := P.targetD.restrictScalars K
  inclusion := P.inclusion.restrictScalars K
  projection := P.projection.restrictScalars K
  homotopy := P.homotopy.restrictScalars K
  source_square := by ext x; exact LinearMap.congr_fun P.source_square x
  target_square := by ext x; exact LinearMap.congr_fun P.target_square x
  inclusion_chain := by ext x; exact LinearMap.congr_fun P.inclusion_chain x
  projection_chain := by ext x; exact LinearMap.congr_fun P.projection_chain x
  retract := by ext x; exact LinearMap.congr_fun P.retract x
  deformation := by ext x; exact LinearMap.congr_fun P.deformation x

variable (B : LinearContraction (R := R) (M := M) (H := Q))
  (hD : P.sourceD = B.d)

def descendedInclusion : Q →ₗ[R] H := P.projection.comp B.inclusion
def descendedProjection : H →ₗ[R] Q := B.projection.comp P.inclusion
def descendedHomotopy : Module.End R H :=
  P.projection.comp (B.h.comp P.inclusion)

include hD in
theorem descended_retract :
    (P.descendedProjection B).comp (P.descendedInclusion B) = LinearMap.id := by
  ext q
  have hcycle : P.sourceD (B.inclusion q) = 0 := by
    rw [hD, B.differential_inclusion_apply]
  have he := LinearMap.congr_fun P.deformation (B.inclusion q)
  change P.sourceD (P.homotopy (B.inclusion q)) +
    P.homotopy (P.sourceD (B.inclusion q)) =
      B.inclusion q - P.inclusion (P.projection (B.inclusion q)) at he
  rw [hcycle, map_zero, add_zero] at he
  have hi : P.inclusion (P.projection (B.inclusion q)) =
      B.inclusion q - P.sourceD (P.homotopy (B.inclusion q)) := by
    rw [he]
    abel
  change B.projection (P.inclusion (P.projection (B.inclusion q))) = q
  rw [hi, map_sub, B.projection_inclusion_apply, hD,
    B.projection_differential_apply, sub_zero]

include hD in
theorem descended_inclusion_cycle :
    P.targetD.comp (P.descendedInclusion B) = 0 := by
  ext q
  change P.targetD (P.projection (B.inclusion q)) = 0
  rw [← P.projection_differential, hD, B.differential_inclusion_apply, map_zero]

include hD in
theorem descended_projection_boundary :
    (P.descendedProjection B).comp P.targetD = 0 := by
  ext x
  change B.projection (P.inclusion (P.targetD x)) = 0
  rw [← P.inclusion_differential, hD, B.projection_differential_apply]

include hD in
theorem descended_homotopy :
    P.targetD * P.descendedHomotopy B + P.descendedHomotopy B * P.targetD =
      1 - (P.descendedInclusion B).comp (P.descendedProjection B) := by
  ext x
  change P.targetD (P.projection (B.h (P.inclusion x))) +
    P.projection (B.h (P.inclusion (P.targetD x))) =
      x - P.projection (B.inclusion (B.projection (P.inclusion x)))
  rw [← P.projection_differential, ← P.inclusion_differential, ← map_add, hD]
  have he := LinearMap.congr_fun B.homotopy (P.inclusion x)
  change B.d (B.h (P.inclusion x)) + B.h (B.d (P.inclusion x)) =
    P.inclusion x - B.inclusion (B.projection (P.inclusion x)) at he
  rw [he, map_sub, P.projection_inclusion]

/-- A transferred complex is a genuine split augmented resolution whenever
its source was one. The augmentation target is unchanged. -/
def descendZeroContraction :
    LinearDeformationRetract (R := R) (M := H) (H := Q) where
  sourceD := P.targetD
  targetD := 0
  inclusion := P.descendedInclusion B
  projection := P.descendedProjection B
  homotopy := P.descendedHomotopy B
  source_square := P.target_square
  target_square := by rw [zero_mul]
  inclusion_chain := by
    rw [LinearMap.comp_zero]
    exact P.descended_inclusion_cycle B hD
  projection_chain := by
    rw [LinearMap.zero_comp]
    exact P.descended_projection_boundary B hD
  retract := P.descended_retract B hD
  deformation := P.descended_homotopy B hD

include hD in
/-- The preimage of a cycle in the augmentation kernel is an explicit
homotopy value, including after nonflat coefficient specializations. -/
theorem descended_cycle_boundary (x : H) (hx : P.targetD x = 0)
    (hε : P.descendedProjection B x = 0) :
    P.targetD (P.descendedHomotopy B x) = x := by
  have he := LinearMap.congr_fun (P.descended_homotopy B hD) x
  change P.targetD (P.descendedHomotopy B x) + P.descendedHomotopy B (P.targetD x) =
    x - P.descendedInclusion B (P.descendedProjection B x) at he
  simpa only [hx, hε, map_zero, add_zero, sub_zero] using he

end FourPapers.HomologicalPerturbation.LinearDeformationRetract

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.FiniteGradedFree -/
section

/-! # Finite free total homology from finite free bounded graded pieces -/

section
set_option autoImplicit false
noncomputable section

namespace FourPapers

open Classical DirectSum

variable {R : Type*} [CommRing R] [Nontrivial R] [StrongRankCondition R]
  (H : ℕ → ℕ → Type*)
  [∀ q p, AddCommGroup (H q p)] [∀ q p, Module R (H q p)]
  [∀ q p, Module.Free R (H q p)] [∀ q p, Module.Finite R (H q p)]

abbrev GradedFreeIndex := Σ q : ℕ, Σ p : ℕ, Module.Free.ChooseBasisIndex R (H q p)

def gradedFreeBasis : Module.Basis (GradedFreeIndex (R := R) H) R (⨁ q, ⨁ p, H q p) :=
  DFinsupp.basis (fun q => DFinsupp.basis (fun p => Module.Free.chooseBasis R (H q p)))

theorem gradedFreeIndex_finite (Q N : ℕ)
    (hQ : ∀ q p, Q < q → Subsingleton (H q p))
    (hN : ∀ q p, N < p → Subsingleton (H q p)) :
    Finite (GradedFreeIndex (R := R) H) := by
  have hq (a : GradedFreeIndex (R := R) H) : a.1 ≤ Q := by
    by_contra h
    letI := hQ a.1 a.2.1 (Nat.lt_of_not_ge h)
    exact (Module.Free.chooseBasis R (H a.1 a.2.1)).ne_zero a.2.2
      (Subsingleton.elim _ _)
  have hp (a : GradedFreeIndex (R := R) H) : a.2.1 ≤ N := by
    by_contra h
    letI := hN a.1 a.2.1 (Nat.lt_of_not_ge h)
    exact (Module.Free.chooseBasis R (H a.1 a.2.1)).ne_zero a.2.2
      (Subsingleton.elim _ _)
  let B := Σ q : Fin (Q+1), Σ p : Fin (N+1),
    Module.Free.ChooseBasisIndex R (H q.val p.val)
  let f : GradedFreeIndex (R := R) H → B := fun a =>
    ⟨⟨a.1, Nat.lt_succ_iff.mpr (hq a)⟩,
      ⟨⟨a.2.1, Nat.lt_succ_iff.mpr (hp a)⟩, a.2.2⟩⟩
  let g : B → GradedFreeIndex (R := R) H := fun a => ⟨a.1.val,a.2.1.val,a.2.2⟩
  have hgf : Function.LeftInverse g f := fun _ => rfl
  exact Finite.of_injective f hgf.injective

theorem finite_gradedFreeTotal (Q N : ℕ)
    (hQ : ∀ q p, Q < q → Subsingleton (H q p))
    (hN : ∀ q p, N < p → Subsingleton (H q p)) :
    Module.Finite R (⨁ q, ⨁ p, H q p) := by
  letI := gradedFreeIndex_finite (R := R) H Q N hQ hN
  exact Module.Finite.of_basis (gradedFreeBasis (R := R) H)

end FourPapers

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.BoundedProjectiveResolution -/
section

/-! # The actual projective dimension of a bounded projective resolution

Every derived Ext class has a cocycle representative on the displayed
resolution. If its degree term is zero, that representative is zero.
-/

section
set_option autoImplicit false
noncomputable section
namespace FourPapers
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {X : C} (P : ProjectiveResolution X)

theorem hasProjectiveDimensionLE_of_bounded_resolution (h : ℕ)
    (hz : ∀ p : ℕ, h < p → IsZero (P.complex.X p)) :
    HasProjectiveDimensionLE X h := by
  letI := HasExt.standard C
  apply HasProjectiveDimensionLT.mk
  intro p hp Y z
  obtain ⟨f, hf, rfl⟩ := P.extMk_surjective z (p+1) rfl
  have he : f = 0 := (hz p (by omega)).eq_zero_of_src f
  subst f
  exact P.extMk_zero (p+1) rfl

theorem projectiveDimension_le_of_bounded_resolution (h : ℕ)
    (hz : ∀ p : ℕ, h < p → IsZero (P.complex.X p)) :
    projectiveDimension X ≤ (h : WithBot ℕ∞) :=
  (projectiveDimension_le_iff X h).mpr
    (hasProjectiveDimensionLE_of_bounded_resolution P h hz)

end FourPapers
end

end
end

/- BEGIN EXACT BODY: FourPapers.Common.ComplexHomologyQuotientEquiv -/
section

/-! # Transporting a nonnegative complex's homology

An equivalence of the actual cycle modules induces an equivalence of homology
when it carries the actual boundary submodule onto the target submodule.
Keeping this construction abstract avoids expanding a concrete chain basis
while instantiating the quotient equivalence.
-/

section
set_option autoImplicit false
noncomputable section

namespace FourPapers.ProjectiveComplexSplitting

universe u v w
variable {R : Type u} [CommRing R]
  (C : ℕ → Type v) [∀ n, AddCommGroup (C n)] [∀ n, Module R (C n)]
  (d : ∀ n, C (n + 1) →ₗ[R] C n)
  (dd : ∀ n, (d n).comp (d (n + 1)) = 0)
  {N : Type w} [AddCommGroup N] [Module R N]

/-- The quotient map induced by a proved equivalence of cycles and boundaries. -/
def homologyEquivOfCycles (p : ℕ) (S : Submodule R N)
    (e : cycles (R := R) C d p ≃ₗ[R] N)
    (he : (boundaries (R := R) C d dd p).map e.toLinearMap = S) :
    Homology (R := R) C d dd p ≃ₗ[R] (N ⧸ S) :=
  Submodule.Quotient.equiv (R := R) (R₂ := R)
    (σ₁₂ := RingHom.id R) (σ₂₁ := RingHom.id R)
    (boundaries C d dd p) S e he

end FourPapers.ProjectiveComplexSplitting

end
end
end

/- BEGIN EXACT BODY: CommAlg.Rees.Basic -/
section

/-! # Actual mixed ideal products and their coefficientwise multi-Rees subalgebra

The generic definitions and proofs are extracted unchanged from the recovered
`CommAlg.IntegralClosure.MultiRees` development. No polymatroid hypothesis is used.
-/

section
noncomputable section
namespace CommAlg
open Classical Finset
variable {J R : Type*} [Fintype J] [DecidableEq J] [CommRing R]

def powerProduct (I : J → Ideal R) (s : J →₀ ℕ) : Ideal R := ∏ j, (I j) ^ (s j)

@[simp] theorem powerProduct_zero (I : J → Ideal R) : powerProduct I 0 = ⊤ := by
  simp [powerProduct]

theorem powerProduct_add (I : J → Ideal R) (s t : J →₀ ℕ) :
    powerProduct I (s + t) = powerProduct I s * powerProduct I t := by
  simp only [powerProduct, Finsupp.add_apply, pow_add, Finset.prod_mul_distrib]

def multiReesAlgebra (I : J → Ideal R) : Subalgebra R (MvPolynomial J R) where
  carrier := {p | ∀ s, p.coeff s ∈ powerProduct I s}
  zero_mem' := by simp
  one_mem' := by
    intro s
    by_cases hs : s = 0
    · subst s; simp
    · simp [MvPolynomial.coeff_one, hs, Ne.symm hs]
  add_mem' hp hq := fun s => by
    simpa only [MvPolynomial.coeff_add] using Ideal.add_mem _ (hp s) (hq s)
  mul_mem' hp hq := by
    intro s
    rw [MvPolynomial.coeff_mul]
    apply Ideal.sum_mem
    intro uv huv
    have he : uv.1 + uv.2 = s := Finset.HasAntidiagonal.mem_antidiagonal.mp huv
    have h := Ideal.mul_mem_mul (hp uv.1) (hq uv.2)
    rwa [← powerProduct_add, he] at h
  algebraMap_mem' r := by
    intro s
    change (MvPolynomial.C r).coeff s ∈ powerProduct I s
    by_cases hs : s = 0
    · subst s; simp
    · simp [MvPolynomial.coeff_C, hs, Ne.symm hs]

@[simp] theorem mem_multiReesAlgebra (I : J → Ideal R) (p : MvPolynomial J R) :
    p ∈ multiReesAlgebra I ↔ ∀ s, p.coeff s ∈ powerProduct I s := Iff.rfl

@[simp] theorem monomial_mem_multiReesAlgebra (I : J → Ideal R) (s : J →₀ ℕ) (r : R) :
    MvPolynomial.monomial s r ∈ multiReesAlgebra I ↔ r ∈ powerProduct I s := by
  constructor
  · intro h
    simpa using h s
  · intro h t
    by_cases ht : t = s
    · subst t; simpa using h
    · simp [MvPolynomial.coeff_monomial, ht, Ne.symm ht]

def multiReesIdeal (I : J → Ideal R) (K : (J →₀ ℕ) → Ideal R)
    (hact : ∀ s t, powerProduct I s * K t ≤ K (s + t)) : Ideal (multiReesAlgebra I) where
  carrier := {p | ∀ s, p.val.coeff s ∈ K s}
  zero_mem' := by simp
  add_mem' hp hq := fun s => by
    simpa only [Subalgebra.coe_add, MvPolynomial.coeff_add] using (K s).add_mem (hp s) (hq s)
  smul_mem' r p hp := by
    intro s
    change (r.val * p.val).coeff s ∈ K s
    rw [MvPolynomial.coeff_mul]
    apply Ideal.sum_mem
    intro uv huv
    have he : uv.1 + uv.2 = s := Finset.HasAntidiagonal.mem_antidiagonal.mp huv
    rw [← he]
    exact hact uv.1 uv.2 (Ideal.mul_mem_mul (r.property uv.1) (hp uv.2))

@[simp] theorem mem_multiReesIdeal (I : J → Ideal R) (K : (J →₀ ℕ) → Ideal R)
    (hact : ∀ s t, powerProduct I s * K t ≤ K (s + t)) (p : multiReesAlgebra I) :
    p ∈ multiReesIdeal I K hact ↔ ∀ s, p.val.coeff s ∈ K s := Iff.rfl

end CommAlg

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.SplitRankOne -/
section

/-! # A direct summand of a rank-one module over a domain

The result uses the actual section and retraction.  Its projector is
multiplication by an idempotent scalar, which is zero or one in a domain.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 200000
noncomputable section

namespace FourPapers

variable {R M : Type*} [CommRing R] [IsDomain R]
  [AddCommGroup M] [Module R M]

theorem split_rank_one_zero_or_equiv (i : M →ₗ[R] R) (r : R →ₗ[R] M)
    (hri : r.comp i = LinearMap.id) :
    Subsingleton M ∨ Nonempty (M ≃ₗ[R] R) := by
  have hret (x : M) : r (i x) = x := LinearMap.congr_fun hri x
  have hi : Function.Injective i := by
    intro x y h
    rw [← hret x, ← hret y, h]
  let e : R := i (r 1)
  have hp (a : R) : i (r a) = a * e := by
    calc
      i (r a) = i (r (a • (1 : R))) := by rw [smul_eq_mul, mul_one]
      _ = a • i (r 1) := by rw [map_smul, map_smul]
      _ = a * e := rfl
  have he : e * e = e := (hp e).symm.trans (congrArg i (hret (r 1)))
  have hz : e * (e - 1) = 0 := by rw [mul_sub, he, mul_one, sub_self]
  rcases mul_eq_zero.mp hz with he0 | he1
  · left
    have hi0 (x : M) : i x = 0 := by
      calc
        i x = i (r (i x)) := (congrArg i (hret x)).symm
        _ = i x * e := hp (i x)
        _ = 0 := by rw [he0, mul_zero]
    exact ⟨fun x y => hi ((hi0 x).trans (hi0 y).symm)⟩
  · right
    have he1' : e = 1 := sub_eq_zero.mp he1
    refine ⟨LinearEquiv.ofBijective i ⟨hi, ?_⟩⟩
    intro a
    exact ⟨r a, by rw [hp, he1', mul_one]⟩

theorem split_rank_one_free (i : M →ₗ[R] R) (r : R →ₗ[R] M)
    (hri : r.comp i = LinearMap.id) : Module.Free R M := by
  cases split_rank_one_zero_or_equiv i r hri with
  | inl h =>
    letI := h
    infer_instance
  | inr h => exact Module.Free.of_equiv (Classical.choice h).symm

theorem split_rank_one_finite (i : M →ₗ[R] R) (r : R →ₗ[R] M)
    (hri : r.comp i = LinearMap.id) : Module.Finite R M := by
  cases split_rank_one_zero_or_equiv i r hri with
  | inl h =>
    letI := h
    exact Module.Finite.of_surjective (0 : R →ₗ[R] M)
      (fun x => ⟨0, Subsingleton.elim _ _⟩)
  | inr h => exact Module.Finite.equiv (Classical.choice h).symm

end FourPapers

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.ProjectiveHomologyBaseChange -/
section

/-!
# Base change of the actual homology of a split projective complex

Projectivity of the terms and their literal kernel/image homology supplies
the sections constructed in `ProjectiveComplexSplitting`. Their identities
are tensored with an arbitrary coefficient algebra. The resulting maps
identify the new homology with the tensor extension of the old homology;
flatness of the coefficient algebra is not assumed.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.ProjectiveComplexSplitting
open scoped TensorProduct

variable {R : Type*} [CommRing R]
  (C : ℕ → Type*) [∀ n, AddCommGroup (C n)] [∀ n, Module R (C n)]
  (d : ∀ n, C (n+1) →ₗ[R] C n)
  (dd : ∀ n, (d n).comp (d (n+1)) = 0)
  (S : Type*) [CommRing S] [Algebra R S]

abbrev scalarPiece (n : ℕ) := S ⊗[R] C n

def scalarDifferential (n : ℕ) : scalarPiece (R := R) C S (n+1) →ₗ[S] scalarPiece (R := R) C S n :=
  (d n).baseChange S

include dd in
theorem scalarDifferential_comp (n : ℕ) :
    (scalarDifferential C d S n).comp (scalarDifferential C d S (n+1)) = 0 := by
  rw [scalarDifferential, scalarDifferential, ← LinearMap.baseChange_comp,
    dd n, LinearMap.baseChange_zero]

abbrev ScalarHomology (p : ℕ) :=
  Homology (R := S) (scalarPiece (R := R) C S) (scalarDifferential C d S)
    (scalarDifferential_comp C d dd S) p

variable (hC : ∀ n, Module.Projective R (C n))
  (hH : ∀ n, Module.Projective R (Homology C d dd n))

def scalarHomologyRepresentative (p : ℕ) :
    (S ⊗[R] Homology C d dd p) →ₗ[S] scalarPiece (R := R) C S p :=
  (homologyInclusion C d dd hH p).baseChange S

def scalarHomologyCoordinate (p : ℕ) :
    scalarPiece (R := R) C S p →ₗ[S] (S ⊗[R] Homology C d dd p) :=
  (homologyProjection C d dd hC hH p).baseChange S

def scalarHomotopy (p : ℕ) : scalarPiece (R := R) C S p →ₗ[S] scalarPiece (R := R) C S (p+1) :=
  (homotopy C d dd hC hH p).baseChange S

theorem scalarHomologyCoordinate_representative (p : ℕ) :
    (scalarHomologyCoordinate C d dd S hC hH p).comp
      (scalarHomologyRepresentative C d dd S hH p) = LinearMap.id := by
  have he : (homologyProjection C d dd hC hH p).comp
      (homologyInclusion C d dd hH p) = LinearMap.id := by
    apply LinearMap.ext
    intro x
    exact homologyProjection_homologyInclusion C d dd hC hH p x
  rw [scalarHomologyCoordinate, scalarHomologyRepresentative,
    ← LinearMap.baseChange_comp, he, LinearMap.baseChange_id]

theorem scalarHomologyRepresentative_cycle (p : ℕ)
    (x : S ⊗[R] Homology C d dd p) :
    scalarHomologyRepresentative C d dd S hH p x ∈
      cycles (R := S) (scalarPiece (R := R) C S) (scalarDifferential C d S) p := by
  cases p with
  | zero => trivial
  | succ p =>
      have he : (d p).comp (homologyInclusion C d dd hH (p+1)) = 0 := by
        apply LinearMap.ext
        intro y
        exact homologyInclusion_is_cycle C d dd hH p y
      change scalarDifferential C d S p
        (scalarHomologyRepresentative C d dd S hH (p+1) x) = 0
      have hbase : (scalarDifferential C d S p).comp
          (scalarHomologyRepresentative C d dd S hH (p+1)) = 0 := by
        rw [scalarDifferential, scalarHomologyRepresentative,
          ← LinearMap.baseChange_comp, he, LinearMap.baseChange_zero]
      exact LinearMap.congr_fun hbase x

theorem scalarHomologyCoordinate_boundary (p : ℕ) (x : scalarPiece (R := R) C S (p+1)) :
    scalarHomologyCoordinate C d dd S hC hH p (scalarDifferential C d S p x) = 0 := by
  have he : (homologyProjection C d dd hC hH p).comp (d p) = 0 := by
    apply LinearMap.ext
    intro y
    exact homologyProjection_kills_boundaries C d dd hC hH p y
  have hbase : (scalarHomologyCoordinate C d dd S hC hH p).comp
      (scalarDifferential C d S p) = 0 := by
    rw [scalarHomologyCoordinate, scalarDifferential,
      ← LinearMap.baseChange_comp, he, LinearMap.baseChange_zero]
  exact LinearMap.congr_fun hbase x

theorem scalar_contraction_zero (x : scalarPiece (R := R) C S 0) :
    scalarDifferential C d S 0 (scalarHomotopy C d dd S hC hH 0 x) =
      x - scalarHomologyRepresentative C d dd S hH 0
        (scalarHomologyCoordinate C d dd S hC hH 0 x) := by
  have he : (d 0).comp (homotopy C d dd hC hH 0) =
      LinearMap.id - (homologyInclusion C d dd hH 0).comp
        (homologyProjection C d dd hC hH 0) := by
    apply LinearMap.ext
    intro y
    exact contraction_zero C d dd hC hH y
  have hbase : (scalarDifferential C d S 0).comp (scalarHomotopy C d dd S hC hH 0) =
      LinearMap.id - (scalarHomologyRepresentative C d dd S hH 0).comp
        (scalarHomologyCoordinate C d dd S hC hH 0) := by
    rw [scalarDifferential, scalarHomotopy, scalarHomologyRepresentative,
      scalarHomologyCoordinate, ← LinearMap.baseChange_comp, he,
      LinearMap.baseChange_sub, LinearMap.baseChange_id, LinearMap.baseChange_comp]
  exact LinearMap.congr_fun hbase x

theorem scalar_contraction_succ (p : ℕ) (x : scalarPiece (R := R) C S (p+1)) :
    scalarDifferential C d S (p+1) (scalarHomotopy C d dd S hC hH (p+1) x) +
      scalarHomotopy C d dd S hC hH p (scalarDifferential C d S p x) =
      x - scalarHomologyRepresentative C d dd S hH (p+1)
        (scalarHomologyCoordinate C d dd S hC hH (p+1) x) := by
  have he : (d (p+1)).comp (homotopy C d dd hC hH (p+1)) +
      (homotopy C d dd hC hH p).comp (d p) =
      LinearMap.id - (homologyInclusion C d dd hH (p+1)).comp
        (homologyProjection C d dd hC hH (p+1)) := by
    apply LinearMap.ext
    intro y
    exact contraction_succ C d dd hC hH p y
  have hbase : (scalarDifferential C d S (p+1)).comp
        (scalarHomotopy C d dd S hC hH (p+1)) +
      (scalarHomotopy C d dd S hC hH p).comp (scalarDifferential C d S p) =
      LinearMap.id - (scalarHomologyRepresentative C d dd S hH (p+1)).comp
        (scalarHomologyCoordinate C d dd S hC hH (p+1)) := by
    rw [scalarDifferential, scalarDifferential, scalarHomotopy, scalarHomotopy,
      scalarHomologyRepresentative, scalarHomologyCoordinate,
      ← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp,
      ← LinearMap.baseChange_add, he, LinearMap.baseChange_sub,
      LinearMap.baseChange_id, LinearMap.baseChange_comp]
  exact LinearMap.congr_fun hbase x

theorem scalar_cycle_homotopy (p : ℕ)
    (x : cycles (R := S) (scalarPiece (R := R) C S) (scalarDifferential C d S) p) :
    scalarDifferential C d S p (scalarHomotopy C d dd S hC hH p x.val) =
      x.val - scalarHomologyRepresentative C d dd S hH p
        (scalarHomologyCoordinate C d dd S hC hH p x.val) := by
  cases p with
  | zero => exact scalar_contraction_zero C d dd S hC hH x.val
  | succ p =>
      have he := scalar_contraction_succ C d dd S hC hH p x.val
      have hx : scalarDifferential C d S p x.val = 0 := x.property
      simpa only [hx, map_zero, add_zero] using he

set_option maxHeartbeats 100000 in
def scalarHomologyProjection (p : ℕ) :
    ScalarHomology C d dd S p →ₗ[S] (S ⊗[R] Homology C d dd p) := by
  let π := (scalarHomologyCoordinate C d dd S hC hH p).comp
    (cycles (R := S) (scalarPiece (R := R) C S) (scalarDifferential C d S) p).subtype
  have hπ : boundaries (R := S) (scalarPiece (R := R) C S) (scalarDifferential C d S)
      (scalarDifferential_comp C d dd S) p ≤ LinearMap.ker π := by
    rintro x ⟨y, rfl⟩
    change scalarHomologyCoordinate C d dd S hC hH p (scalarDifferential C d S p y) = 0
    exact scalarHomologyCoordinate_boundary C d dd S hC hH p y
  let f := Submodule.liftQ (R := S) (R₂ := S) (τ₁₂ := RingHom.id S)
    (M := ↥(cycles (R := S) (scalarPiece (R := R) C S) (scalarDifferential C d S) p))
    (M₂ := S ⊗[R] Homology C d dd p)
    (boundaries (R := S) (scalarPiece (R := R) C S) (scalarDifferential C d S)
      (scalarDifferential_comp C d dd S) p) π hπ
  exact { toFun := fun x => f x
          map_add' := fun x y => f.map_add x y
          map_smul' := fun r x => f.map_smul r x }

set_option maxHeartbeats 100000 in
def scalarHomologyInclusion (p : ℕ) :
    (S ⊗[R] Homology C d dd p) →ₗ[S] ScalarHomology C d dd S p := by
  let f := (Submodule.mkQ (R := S)
    (M := ↥(cycles (R := S) (scalarPiece (R := R) C S) (scalarDifferential C d S) p))
    (boundaries (R := S) (scalarPiece (R := R) C S) (scalarDifferential C d S)
      (scalarDifferential_comp C d dd S) p)).comp
      ((scalarHomologyRepresentative C d dd S hH p).codRestrict
        (cycles (R := S) (scalarPiece (R := R) C S) (scalarDifferential C d S) p)
        (scalarHomologyRepresentative_cycle C d dd S hH p))
  exact { toFun := fun x => f x
          map_add' := fun x y => f.map_add x y
          map_smul' := fun r x => f.map_smul r x }

@[simp] theorem scalarHomologyProjection_mk (p : ℕ)
    (x : cycles (R := S) (scalarPiece (R := R) C S) (scalarDifferential C d S) p) :
    scalarHomologyProjection C d dd S hC hH p (Submodule.Quotient.mk x) =
      scalarHomologyCoordinate C d dd S hC hH p x.val := rfl

theorem scalarHomologyProjection_inclusion (p : ℕ) :
    (scalarHomologyProjection C d dd S hC hH p).comp
      (scalarHomologyInclusion C d dd S hH p) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun (scalarHomologyCoordinate_representative C d dd S hC hH p) x

set_option maxHeartbeats 100000 in
theorem scalarHomologyInclusion_projection (p : ℕ) :
    (scalarHomologyInclusion C d dd S hH p).comp
      (scalarHomologyProjection C d dd S hC hH p) = LinearMap.id := by
  apply Submodule.quot_hom_ext (R := S)
    (M := ↥(cycles (R := S) (scalarPiece (R := R) C S) (scalarDifferential C d S) p))
    (M₂ := ScalarHomology C d dd S p)
    (p := boundaries (R := S) (scalarPiece (R := R) C S) (scalarDifferential C d S)
      (scalarDifferential_comp C d dd S) p)
  intro x
  change Submodule.Quotient.mk
      ⟨scalarHomologyRepresentative C d dd S hH p
        (scalarHomologyCoordinate C d dd S hC hH p x.val), _⟩ =
    (Submodule.Quotient.mk x : ScalarHomology C d dd S p)
  apply (Submodule.Quotient.eq _).mpr
  refine ⟨-scalarHomotopy C d dd S hC hH p x.val, ?_⟩
  apply Subtype.ext
  change scalarDifferential C d S p (-scalarHomotopy C d dd S hC hH p x.val) =
    scalarHomologyRepresentative C d dd S hH p
      (scalarHomologyCoordinate C d dd S hC hH p x.val) - x.val
  rw [map_neg, scalar_cycle_homotopy C d dd S hC hH p x]
  abel

/-- Arbitrary base change commutes with actual homology when the original
terms and homology are projective. This includes every residue characteristic. -/
def projectiveHomologyBaseChangeEquiv (p : ℕ) :
    ScalarHomology C d dd S p ≃ₗ[S] (S ⊗[R] Homology C d dd p) :=
  LinearEquiv.ofLinearMap (scalarHomologyProjection C d dd S hC hH p)
    (scalarHomologyInclusion C d dd S hH p)
    (scalarHomologyProjection_inclusion C d dd S hC hH p)
    (scalarHomologyInclusion_projection C d dd S hC hH p)

include hC hH in
theorem scalarHomology_finrank [StrongRankCondition R] [StrongRankCondition S]
    (p : ℕ) [Module.Free R (Homology C d dd p)] :
    Module.finrank S (ScalarHomology C d dd S p) = Module.finrank R (Homology C d dd p) := by
  rw [(projectiveHomologyBaseChangeEquiv C d dd S hC hH p).finrank_eq,
    Module.finrank_baseChange]

end FourPapers.ProjectiveComplexSplitting

#print axioms FourPapers.ProjectiveComplexSplitting.projectiveHomologyBaseChangeEquiv

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.ChainHomologyCongr -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.ProjectiveComplexSplitting

variable {R : Type*} [CommRing R]
  (C D : ℕ → Type*)
  [∀ n, AddCommGroup (C n)] [∀ n, Module R (C n)]
  [∀ n, AddCommGroup (D n)] [∀ n, Module R (D n)]
  (c : ∀ n, C (n+1) →ₗ[R] C n) (d : ∀ n, D (n+1) →ₗ[R] D n)
  (cc : ∀ n, (c n).comp (c (n+1)) = 0)
  (dd : ∀ n, (d n).comp (d (n+1)) = 0)
  (e : ∀ n, C n ≃ₗ[R] D n)
  (he : ∀ n x, e n (c n x) = d n (e (n+1) x))

def chainCyclesEquiv (p : ℕ) : cycles C c p ≃ₗ[R] cycles D d p where
  toFun x := ⟨e p x.val, by
    cases p with
    | zero => trivial
    | succ p =>
        change d p (e (p+1) x.val) = 0
        rw [← he, show c p x.val = 0 from x.property, map_zero]⟩
  invFun y := ⟨(e p).symm y.val, by
    cases p with
    | zero => trivial
    | succ p =>
        change c p ((e (p+1)).symm y.val) = 0
        apply (e p).injective
        rw [he, LinearEquiv.apply_symm_apply, map_zero]
        exact y.property⟩
  left_inv x := Subtype.ext ((e p).symm_apply_apply x.val)
  right_inv y := Subtype.ext ((e p).apply_symm_apply y.val)
  map_add' x y := Subtype.ext ((e p).map_add x.val y.val)
  map_smul' r x := Subtype.ext ((e p).map_smul r x.val)

lemma chainCyclesEquiv_boundaries (p : ℕ) :
    (boundaries C c cc p).map (chainCyclesEquiv C D c d e he p).toLinearMap =
      boundaries D d dd p := by
  ext z
  constructor
  · rintro ⟨x, ⟨y, rfl⟩, rfl⟩
    refine ⟨e (p+1) y, ?_⟩
    apply Subtype.ext
    exact (he p y).symm
  · rintro ⟨y, rfl⟩
    refine ⟨toCycles C c cc p ((e (p+1)).symm y),
      ⟨(e (p+1)).symm y, rfl⟩, ?_⟩
    apply Subtype.ext
    change e p (c p ((e (p+1)).symm y)) = d p y
    rw [he, LinearEquiv.apply_symm_apply]

/-- Degree-preserving chain equivalences induce equivalences of the literal
kernel/image quotients, with the full degree-zero term retained. -/
def chainHomologyEquiv (p : ℕ) : Homology C c cc p ≃ₗ[R] Homology D d dd p :=
  Submodule.Quotient.equiv _ _ (chainCyclesEquiv C D c d e he p)
    (chainCyclesEquiv_boundaries C D c d cc dd e he p)

end FourPapers.ProjectiveComplexSplitting

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.PolynomialCoefficientBaseChange -/
section

/-!
# Polynomial-linear realizations of coefficient base change

Tensoring a polynomial module over its coefficient ring initially gives an
explicit coefficient-linear map. A realization records the actual action of
each source polynomial. Polynomial induction then proves that transported
maps are linear over the entire specialized polynomial ring.

For a module with a specified polynomial basis, the realization is the literal
finitely supported polynomial-coordinate module with the same index set.
Every transported matrix entry is obtained by the coefficient ring map.
-/

section
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section

namespace FourPapers.PolynomialCoefficientBaseChange

open Classical MvPolynomial
open scoped TensorProduct

variable {R V : Type*} [CommRing R]
  (A : Type*) [CommRing A] [Algebra R A]
  {F G H : Type*}
  [AddCommGroup F] [Module (MvPolynomial V R) F] [Module R F]
  [IsScalarTower R (MvPolynomial V R) F]
  [AddCommGroup G] [Module (MvPolynomial V R) G] [Module R G]
  [IsScalarTower R (MvPolynomial V R) G]
  [AddCommGroup H] [Module (MvPolynomial V R) H] [Module R H]
  [IsScalarTower R (MvPolynomial V R) H]

def sourceMultiply (F : Type*) [AddCommGroup F]
    [Module (MvPolynomial V R) F] [Module R F]
    [IsScalarTower R (MvPolynomial V R) F]
    (p : MvPolynomial V R) : Module.End R F where
  toFun x := p • x
  map_add' x y := smul_add p x y
  map_smul' r x := smul_comm p r x

@[simp] theorem sourceMultiply_apply (p : MvPolynomial V R) (x : F) :
    sourceMultiply F p x = p • x := rfl

variable {F' G' H' : Type*}
  [AddCommGroup F'] [Module (MvPolynomial V A) F'] [Module A F']
  [IsScalarTower A (MvPolynomial V A) F']
  [AddCommGroup G'] [Module (MvPolynomial V A) G'] [Module A G']
  [IsScalarTower A (MvPolynomial V A) G']
  [AddCommGroup H'] [Module (MvPolynomial V A) H'] [Module A H']
  [IsScalarTower A (MvPolynomial V A) H']

structure Realization (F F' : Type*)
    [AddCommGroup F] [Module (MvPolynomial V R) F] [Module R F]
    [IsScalarTower R (MvPolynomial V R) F]
    [AddCommGroup F'] [Module (MvPolynomial V A) F'] [Module A F']
    [IsScalarTower A (MvPolynomial V A) F'] where
  equivalence : (A ⊗[R] F) ≃ₗ[A] F'
  multiply : ∀ (p : MvPolynomial V R) (x : A ⊗[R] F),
    equivalence ((sourceMultiply F p).baseChange A x) =
      MvPolynomial.map (algebraMap R A) p • equivalence x

namespace Realization

variable (eF : Realization (R := R) (V := V) A F F')
  (eG : Realization (R := R) (V := V) A G G')
  (eH : Realization (R := R) (V := V) A H H')
  (f : F →ₗ[MvPolynomial V R] G)

def coefficientTransfer : F' →ₗ[A] G' :=
  eG.equivalence.toLinearMap.comp
    (((f.restrictScalars R).baseChange A).comp eF.equivalence.symm.toLinearMap)

theorem coefficientTransfer_equivalence (x : A ⊗[R] F) :
    coefficientTransfer A eF eG f (eF.equivalence x) =
      eG.equivalence ((f.restrictScalars R).baseChange A x) := by
  change eG.equivalence ((f.restrictScalars R).baseChange A
    (eF.equivalence.symm (eF.equivalence x))) = _
  rw [eF.equivalence.symm_apply_apply]

theorem coefficientTransfer_source_smul (p : MvPolynomial V R) (x : F') :
    coefficientTransfer A eF eG f (MvPolynomial.map (algebraMap R A) p • x) =
      MvPolynomial.map (algebraMap R A) p • coefficientTransfer A eF eG f x := by
  obtain ⟨y,rfl⟩ := eF.equivalence.surjective x
  rw [← eF.multiply p y, coefficientTransfer_equivalence,
    coefficientTransfer_equivalence, ← eG.multiply]
  congr 1
  have he : (f.restrictScalars R).comp (sourceMultiply F p) =
      (sourceMultiply G p).comp (f.restrictScalars R) := by
    ext z
    exact f.map_smul p z
  have hb := congrArg (fun g : F →ₗ[R] G => g.baseChange A) he
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp] at hb
  exact LinearMap.congr_fun hb y

theorem coefficientTransfer_polynomial_smul (p : MvPolynomial V A) (x : F') :
    coefficientTransfer A eF eG f (p • x) =
      p • coefficientTransfer A eF eG f x := by
  induction p using MvPolynomial.induction_on generalizing x with
  | C a =>
      simpa only [← MvPolynomial.algebraMap_eq, algebraMap_smul] using
        (coefficientTransfer A eF eG f).map_smul a x
  | add p q hp hq =>
      rw [add_smul, map_add, hp, hq, add_smul]
  | mul_X p v hp =>
      rw [mul_smul, hp]
      have hx := coefficientTransfer_source_smul A eF eG f (X v) x
      rw [MvPolynomial.map_X] at hx
      rw [hx, mul_smul]

/-- Transported base-change maps are genuinely polynomial-linear. -/
def transfer : F' →ₗ[MvPolynomial V A] G' where
  toFun := coefficientTransfer A eF eG f
  map_add' := (coefficientTransfer A eF eG f).map_add
  map_smul' := coefficientTransfer_polynomial_smul A eF eG f

theorem transfer_equivalence (x : A ⊗[R] F) :
    transfer A eF eG f (eF.equivalence x) =
      eG.equivalence ((f.restrictScalars R).baseChange A x) :=
  coefficientTransfer_equivalence A eF eG f x

theorem transfer_comp (g : G →ₗ[MvPolynomial V R] H) :
    transfer A eF eH (g.comp f) = (transfer A eG eH g).comp (transfer A eF eG f) := by
  ext x
  obtain ⟨y,rfl⟩ := eF.equivalence.surjective x
  simp only [LinearMap.comp_apply, transfer_equivalence]
  have he : (g.comp f).restrictScalars R =
      (g.restrictScalars R).comp (f.restrictScalars R) := rfl
  rw [he, LinearMap.baseChange_comp]
  rfl

@[simp] theorem transfer_zero : transfer A eF eG (0 : F →ₗ[MvPolynomial V R] G) = 0 := by
  ext x
  obtain ⟨y,rfl⟩ := eF.equivalence.surjective x
  rw [transfer_equivalence]
  simp

theorem transfer_exact (g : G →ₗ[MvPolynomial V R] H)
    (hex : Function.Exact ((f.restrictScalars R).baseChange A)
      ((g.restrictScalars R).baseChange A)) :
    Function.Exact (transfer A eF eG f) (transfer A eG eH g) := by
  intro x
  obtain ⟨y,rfl⟩ := eG.equivalence.surjective x
  rw [transfer_equivalence, eH.equivalence.map_eq_zero_iff, hex y]
  constructor
  · rintro ⟨z,rfl⟩
    exact ⟨eF.equivalence z, transfer_equivalence A eF eG f z⟩
  · rintro ⟨z,hz⟩
    refine ⟨eF.equivalence.symm z, ?_⟩
    apply eG.equivalence.injective
    rw [← transfer_equivalence A eF eG f (eF.equivalence.symm z),
      eF.equivalence.apply_symm_apply]
    exact hz

theorem transfer_surjective
    (hf : Function.Surjective ((f.restrictScalars R).baseChange A)) :
    Function.Surjective (transfer A eF eG f) := by
  intro x
  obtain ⟨y,hy⟩ := hf (eG.equivalence.symm x)
  refine ⟨eF.equivalence y, ?_⟩
  rw [transfer_equivalence, hy, eG.equivalence.apply_symm_apply]

end Realization

section FreeCoordinates

variable {I J : Type*} (b : Module.Basis I (MvPolynomial V R) F)
  (c : Module.Basis J (MvPolynomial V R) G)

/-- The same polynomial basis indices after changing only coefficients. -/
def basisCoordinates : (A ⊗[R] F) ≃ₗ[A] (I →₀ MvPolynomial V A) :=
  (LinearEquiv.baseChange R A F (I →₀ MvPolynomial V R)
    (b.repr.restrictScalars R)).trans
    ((TensorProduct.finsuppRight R A A (MvPolynomial V R) I).trans
      (Finsupp.mapRange.linearEquiv (MvPolynomial.algebraTensorAlgEquiv R A).toLinearEquiv))

theorem basisCoordinates_tmul_apply (a : A) (x : F) (i : I) :
    basisCoordinates A b (a ⊗ₜ[R] x) i =
      a • MvPolynomial.map (algebraMap R A) (b.repr x i) := by
  simp [basisCoordinates, MvPolynomial.algebraTensorAlgEquiv_tmul]

@[simp] theorem basisCoordinates_one_tmul_basis (i : I) :
    basisCoordinates A b (1 ⊗ₜ[R] b i) = Finsupp.single i 1 := by
  ext j
  rw [basisCoordinates_tmul_apply]
  simp only [Module.Basis.repr_self, Finsupp.single_apply, one_smul]
  split_ifs <;> simp

@[simp] theorem basisCoordinates_symm_single (i : I) :
    (basisCoordinates A b).symm (Finsupp.single i 1) = 1 ⊗ₜ[R] b i := by
  apply (basisCoordinates A b).injective
  rw [LinearEquiv.apply_symm_apply, basisCoordinates_one_tmul_basis]

theorem basisCoordinates_source_multiply (p : MvPolynomial V R) (x : A ⊗[R] F) :
    basisCoordinates A b ((sourceMultiply F p).baseChange A x) =
      MvPolynomial.map (algebraMap R A) p • basisCoordinates A b x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  | tmul a x =>
      ext i
      simp only [LinearMap.baseChange_tmul, sourceMultiply_apply,
        basisCoordinates_tmul_apply, map_smul, Finsupp.smul_apply,
        smul_eq_mul, map_mul, mul_smul_comm]

def basisRealization : Realization (R := R) (V := V) A F (I →₀ MvPolynomial V A) where
  equivalence := basisCoordinates A b
  multiply := basisCoordinates_source_multiply A b

/-- The actual specialized matrix is obtained entry by entry by mapping
the original polynomial coefficients. -/
theorem basisRealization_transfer_entry (f : F →ₗ[MvPolynomial V R] G) (i : I) (j : J) :
    (Realization.transfer A (basisRealization A b) (basisRealization A c) f (Finsupp.single i 1)) j =
      MvPolynomial.map (algebraMap R A) (c.repr (f (b i)) j) := by
  rw [← basisCoordinates_one_tmul_basis A b i]
  change (Realization.transfer A (basisRealization A b) (basisRealization A c) f
    ((basisRealization A b).equivalence (1 ⊗ₜ[R] b i))) j = _
  rw [Realization.transfer_equivalence A (basisRealization A b) (basisRealization A c) f]
  change basisCoordinates A c ((f.restrictScalars R).baseChange A (1 ⊗ₜ[R] b i)) j = _
  rw [LinearMap.baseChange_tmul, basisCoordinates_tmul_apply, one_smul]
  rfl

end FreeCoordinates
end FourPapers.PolynomialCoefficientBaseChange

namespace FourPapers

variable {S B F G I J : Type*} [CommRing S] [CommRing B] [Algebra S B]
  [AddCommGroup F] [Module S F] [AddCommGroup G] [Module S G]

/-- A coefficientwise zero specialized matrix is the zero base-changed
linear map. This connects the matrix minimality assertion to the actual
differential after taking the polynomial residue field. -/
theorem basis_baseChange_zero_of_coefficients
    (b : Module.Basis I S F) (c : Module.Basis J S G) (f : F →ₗ[S] G)
    (hf : ∀ i j, algebraMap S B (c.repr (f (b i)) j) = 0) :
    f.baseChange B = 0 := by
  apply (b.baseChange B).ext
  intro i
  apply (c.baseChange B).repr.injective
  ext j
  simp only [Module.Basis.baseChange_apply, LinearMap.baseChange_tmul,
    Module.Basis.baseChange_repr_tmul, LinearMap.zero_apply, map_zero,
    Finsupp.zero_apply, Algebra.smul_def, hf, zero_mul]

end FourPapers

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.ColoredMultiplicityCounting -/
section

/-! # Positive multiplicities with prescribed color totals

A multiplicity assignment splits into independent assignments on its color
fibers. The cardinality is therefore a product of the ordinary positive
stars-and-bars counts. The support must meet every color when all prescribed
totals are positive; this condition is explicit.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
noncomputable section
namespace FourPapers.ColoredMultiplicityCounting
open Classical MultichainCounting
variable {A C : Type*} [Fintype A] [Fintype C]

abbrev PositiveWeights (A : Type*) [Fintype A] (m : ℕ) :=
  {f : A → ℕ // (∑ a, f a) = m ∧ ∀ a, 0 < f a}

def positiveSymWeights (m : ℕ) : PositiveSym A m ≃ PositiveWeights A m :=
  ((Sym.equivNatSumOfFintype A m).subtypeEquiv (fun s => by
    simp only [Sym.coe_equivNatSumOfFintype_apply_apply, Multiset.count_pos, Sym.mem_coe])).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter (fun f : A → ℕ => (∑ a, f a) = m)
        (fun f => ∀ a, 0 < f a))

instance positiveWeightsFintype (m : ℕ) : Fintype (PositiveWeights A m) :=
  Fintype.ofEquiv (PositiveSym A m) (positiveSymWeights m)

theorem card_positiveWeights [Nonempty A] (m : ℕ) (hm : 0 < m) :
    Nat.card (PositiveWeights A m) = (m-1).choose (Fintype.card A-1) := by
  rw [← Nat.card_congr (positiveSymWeights (A := A) m)]
  exact card_positiveSym m hm

abbrev ColoredWeights (color : A → C) (m : C → ℕ) :=
  {f : A → ℕ // (∀ a, 0 < f a) ∧ ∀ c, (∑ a : {a // color a = c}, f a.val) = m c}

/-- Restriction and gluing of multiplicities on the actual color fibers. -/
def coloredWeightsEquiv (color : A → C) (m : C → ℕ) :
    ColoredWeights color m ≃ (∀ c, PositiveWeights {a // color a = c} (m c)) where
  toFun f c := ⟨fun a => f.val a.val, f.property.2 c, fun a => f.property.1 a.val⟩
  invFun g := ⟨fun a => (g (color a)).val ⟨a,rfl⟩,
    (fun a => (g (color a)).property.2 ⟨a,rfl⟩), by
      intro c
      have he : (fun a : {a // color a = c} => (g (color a.val)).val ⟨a.val,rfl⟩) =
          (g c).val := by
        funext a
        rcases a with ⟨a,ha⟩
        cases ha
        rfl
      rw [he]
      exact (g c).property.1⟩
  left_inv f := by apply Subtype.ext; rfl
  right_inv g := by
    funext c
    apply Subtype.ext
    funext a
    rcases a with ⟨a,ha⟩
    cases ha
    rfl

instance coloredWeightsFintype (color : A → C) (m : C → ℕ) :
    Fintype (ColoredWeights color m) :=
  Fintype.ofEquiv _ (coloredWeightsEquiv color m).symm

/-- The precise product of positive binomial coefficients. -/
theorem card_coloredWeights (color : A → C) (hcolor : Function.Surjective color)
    (m : C → ℕ) (hm : ∀ c, 0 < m c) :
    Nat.card (ColoredWeights color m) =
      ∏ c, (m c-1).choose (Fintype.card {a // color a = c}-1) := by
  rw [Nat.card_congr (coloredWeightsEquiv color m), Nat.card_pi]
  apply Finset.prod_congr rfl
  intro c _
  letI : Nonempty {a // color a = c} := by
    obtain ⟨a,ha⟩ := hcolor c
    exact ⟨⟨a,ha⟩⟩
  exact card_positiveWeights (m c) (hm c)

theorem coloredWeights_total (color : A → C) (m : C → ℕ) (f : ColoredWeights color m) :
    (∑ a, f.val a) = ∑ c, m c := by
  rw [← Fintype.sum_fiberwise color f.val]
  simp only [f.property.2]

/-- The fixed total size is a consequence of the prescribed color totals. -/
def positiveColoredWeightsEquiv (color : A → C) (m : C → ℕ) :
    {f : PositiveWeights A (∑ c, m c) //
      ∀ c, (∑ a : {a // color a = c}, f.val a.val) = m c} ≃
      ColoredWeights color m where
  toFun f := ⟨f.val.val,f.val.property.2,f.property⟩
  invFun f := ⟨⟨f.val,coloredWeights_total color m f,f.property.1⟩,f.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma sum_delta_fiber (color : A → C) (c : C) (x : A) :
    (∑ a : {a // color a = c}, if a.val = x then 1 else 0 : ℕ) =
      if color x = c then 1 else 0 := by
  by_cases hx : color x = c
  · rw [if_pos hx]
    let b : {a // color a = c} := ⟨x,hx⟩
    rw [Finset.sum_eq_single b]
    · simp [b]
    · intro a _ hab
      rw [if_neg (fun ha => hab (Subtype.ext ha))]
    · intro h
      exact (h (Finset.mem_univ b)).elim
  · rw [if_neg hx]
    apply Finset.sum_eq_zero
    intro a _
    rw [if_neg]
    intro ha
    exact hx (ha ▸ a.property)

/-- Counting by a color fiber agrees with literal multiset color counting. -/
theorem sum_count_fiber (color : A → C) (s : Multiset A) (c : C) :
    (∑ a : {a // color a = c}, s.count a.val) = (s.map color).count c := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons x s ih =>
      simp only [Multiset.count_cons, Multiset.map_cons, Finset.sum_add_distrib, ih,
        sum_delta_fiber]
      congr 1
      simp only [eq_comm]

/-- Restrict the positive-multiset correspondence to prescribed color totals. -/
def positiveColoredSymWeights (color : A → C) (m : C → ℕ) :
    {s : PositiveSym A (∑ c, m c) // ∀ c, (s.val.val.map color).count c = m c} ≃
      ColoredWeights color m :=
  ((positiveSymWeights (A := A) (∑ c, m c)).subtypeEquiv (fun s => by
    change (∀ c, (s.val.val.map color).count c = m c) ↔
      ∀ c, (∑ a : {a // color a = c}, (s.val.val).count a.val) = m c
    simp only [sum_count_fiber])).trans (positiveColoredWeightsEquiv color m)

section Tuples
variable [Preorder A]

def tupleColorCount (color : A → C) {M : ℕ} (w : MonotoneTuple A M) (c : C) : ℕ :=
  ((List.ofFn w.val : Multiset A).map color).count c

lemma list_color_count (color : A → C) (l : List A) (c : C) :
    (l.map color).count c = (l.map (fun a => if color a = c then 1 else 0)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.count_cons, List.sum_cons, ih]
      by_cases h : color a = c <;> simp [h, Nat.add_comm]

theorem tupleColorCount_sum (color : A → C) {M : ℕ} (w : MonotoneTuple A M) (c : C) :
    tupleColorCount color w c = ∑ i, if color (w.val i) = c then 1 else 0 := by
  rw [tupleColorCount, Multiset.map_coe, Multiset.coe_count, list_color_count]
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_def]

end Tuples

section Supports
variable [PartialOrder A]

/-- Positive prescribed totals force the support to contain every color. -/
theorem coloredWeights_surjective (color : A → C) (m : C → ℕ)
    (hm : ∀ c, 0 < m c) (f : ColoredWeights color m) :
    Function.Surjective color := by
  intro c
  by_contra h
  letI : IsEmpty {a // color a = c} := ⟨fun a => h ⟨a.val,a.property⟩⟩
  have hz : (∑ a : {a // color a = c}, f.val a.val) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    exact isEmptyElim a
  have he := f.property.2 c
  rw [hz] at he
  exact (Nat.ne_of_gt (hm c)) he.symm

/-- Fixing the strict support leaves exactly the independent positive
multiplicities in its color fibers. -/
def coloredSupportFiberEquiv (color : A → C) (m : C → ℕ)
    (hM : 0 < ∑ c, m c) (s : StrictSupport A) :
    {w : {w : MonotoneTuple A (∑ c, m c) // tupleSupport hM w = s} //
      ∀ c, tupleColorCount color w.val c = m c} ≃
        ColoredWeights (fun a : s.val => color a.val) m := by
  letI : LinearOrder s.val := s.property.2.linearOrder
  let colorS : s.val → C := fun a => color a.val
  let e₁ :
      {w : {w : MonotoneTuple A (∑ c, m c) // tupleSupport hM w = s} //
        ∀ c, tupleColorCount color w.val c = m c} ≃
      {w : {w : MonotoneTuple s.val (∑ c, m c) // Function.Surjective w.val} //
        ∀ c, tupleColorCount colorS w.val c = m c} :=
    (supportFiberEquiv hM s).subtypeEquiv (fun w => by
      simp only [tupleColorCount_sum]
      rfl)
  let e₂ :
      {w : {w : MonotoneTuple s.val (∑ c, m c) // Function.Surjective w.val} //
        ∀ c, tupleColorCount colorS w.val c = m c} ≃
      {w : PositiveSym s.val (∑ c, m c) //
        ∀ c, (w.val.val.map colorS).count c = m c} :=
    (surjectiveMonotoneEquiv (α := s.val) (∑ c, m c)).subtypeEquiv
      (fun _ => Iff.rfl)
  exact e₁.trans (e₂.trans (positiveColoredSymWeights colorS m))

abbrev ColoredTuple (color : A → C) (m : C → ℕ) :=
  {w : MonotoneTuple A (∑ c, m c) // ∀ c, tupleColorCount color w c = m c}

/-- Interchange the two independently imposed conditions on a tuple. -/
def coloredTupleSupportFiberEquiv (color : A → C) (m : C → ℕ)
    (hM : 0 < ∑ c, m c) (s : StrictSupport A) :
    {w : ColoredTuple color m // tupleSupport hM w.val = s} ≃
      {w : {w : MonotoneTuple A (∑ c, m c) // tupleSupport hM w = s} //
        ∀ c, tupleColorCount color w.val c = m c} where
  toFun w := ⟨⟨w.val.val,w.property⟩,w.val.property⟩
  invFun w := ⟨⟨w.val.val,w.property⟩,w.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Every support containing all colors contributes the product of the
positive stars-and-bars coefficients. All other supports contribute zero. -/
theorem card_coloredTupleSupportFiber (color : A → C) (m : C → ℕ)
    (hm : ∀ c, 0 < m c) (hM : 0 < ∑ c, m c) (s : StrictSupport A) :
    Nat.card {w : ColoredTuple color m // tupleSupport hM w.val = s} =
      if Function.Surjective (fun a : s.val => color a.val) then
        ∏ c, (m c-1).choose (Fintype.card {a : s.val // color a.val = c}-1)
      else 0 := by
  rw [Nat.card_congr (coloredTupleSupportFiberEquiv color m hM s),
    Nat.card_congr (coloredSupportFiberEquiv color m hM s)]
  split_ifs with hs
  · exact card_coloredWeights _ hs m hm
  · letI : IsEmpty (ColoredWeights (fun a : s.val => color a.val) m) :=
      ⟨fun f => hs (coloredWeights_surjective _ m hm f)⟩
    rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero]

/-- The multivariate positive-binomial expansion of any support-dependent
sum over prescribed-color multichains. Its coefficients are nonnegative
integers, and depend only on the strict support. -/
theorem sum_by_colored_strict_support (color : A → C) (m : C → ℕ)
    (hm : ∀ c, 0 < m c) (hM : 0 < ∑ c, m c) (f : StrictSupport A → ℕ) :
    (∑ w : ColoredTuple color m, f (tupleSupport hM w.val)) =
      ∑ s : StrictSupport A,
        (∏ c, (m c-1).choose (Fintype.card {a : s.val // color a.val = c}-1)) *
          (if Function.Surjective (fun a : s.val => color a.val) then f s else 0) := by
  have hgroup : (∑ w : ColoredTuple color m, f (tupleSupport hM w.val)) =
      ∑ s : StrictSupport A,
        ∑ w : {w : ColoredTuple color m // tupleSupport hM w.val = s}, f s := by
    symm
    rw [← Fintype.sum_sigma (f := fun x :
      Σ s : StrictSupport A, {w : ColoredTuple color m // tupleSupport hM w.val = s} =>
        f x.1)]
    apply Fintype.sum_equiv (Equiv.sigmaFiberEquiv
      (fun w : ColoredTuple color m => tupleSupport hM w.val))
    intro w
    exact congrArg f w.2.property.symm
  rw [hgroup]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    card_coloredTupleSupportFiber color m hm hM s]
  simp only [nsmul_eq_mul, Nat.cast_id]
  split_ifs <;> simp

end Supports

end FourPapers.ColoredMultiplicityCounting

#print axioms FourPapers.ColoredMultiplicityCounting.card_coloredWeights

#print axioms FourPapers.ColoredMultiplicityCounting.sum_by_colored_strict_support

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.MultivariatePositiveBinomial -/
section

/-! # Multivariate positive-binomial polynomials

Products of the positive binomial functions in independent color parameters
are represented by actual rational multivariate polynomials. The coefficients
in this basis are natural numbers, rather than arbitrary rational coefficients.
-/

section
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FourPapers.MultivariatePositiveBinomial
open Classical PositiveBinomialPolynomial
variable {C ι : Type*} [Fintype C] [Fintype ι]

/-- The polynomial `choose(X_c - 1, r)` in the color variable `c`. -/
def coordinateBinomial (c : C) (r : ℕ) : MvPolynomial C ℚ :=
  (binomialPolynomial r).eval₂ MvPolynomial.C (MvPolynomial.X c-1)

lemma coordinatePolynomial_eval (p : Polynomial ℚ) (c : C) (x : C → ℚ) :
    MvPolynomial.eval x (p.eval₂ MvPolynomial.C (MvPolynomial.X c-1)) =
      p.eval (x c-1) := by
  rw [Polynomial.hom_eval₂]
  have he : (MvPolynomial.eval x).comp MvPolynomial.C = RingHom.id ℚ :=
    RingHom.ext (fun a => MvPolynomial.eval_C a)
  rw [he,Polynomial.eval₂_id,(MvPolynomial.eval x).map_sub,
    MvPolynomial.eval_X,(MvPolynomial.eval x).map_one]

theorem coordinateBinomial_eval (c : C) (r : ℕ) (m : C → ℕ)
    (hm : 0 < m c) :
    MvPolynomial.eval (fun a => (m a : ℚ)) (coordinateBinomial c r) =
      ((m c-1).choose r : ℚ) := by
  have hs : (m c : ℚ)-1 = ((m c-1 : ℕ) : ℚ) := by
    exact (Nat.cast_sub (by omega : 1 ≤ m c)).symm
  exact (coordinatePolynomial_eval (binomialPolynomial r) c (fun a => (m a : ℚ))).trans
    ((congrArg (fun x : ℚ => (binomialPolynomial r).eval x) hs).trans
      (binomialPolynomial_eval r (m c-1)))

def polynomial (coeff : ι → ℕ) (degree : ι → C → ℕ) : MvPolynomial C ℚ :=
  ∑ a, MvPolynomial.C (coeff a : ℚ) * ∏ c, coordinateBinomial c (degree a c)

/-- One fixed polynomial represents every positive parameter vector. -/
theorem polynomial_eval (coeff : ι → ℕ) (degree : ι → C → ℕ)
    (m : C → ℕ) (hm : ∀ c, 0 < m c) :
    MvPolynomial.eval (fun c => (m c : ℚ)) (polynomial coeff degree) =
      ((∑ a, coeff a * ∏ c, (m c-1).choose (degree a c) : ℕ) : ℚ) := by
  rw [polynomial,MvPolynomial.eval_sum,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [(MvPolynomial.eval (fun c => (m c : ℚ))).map_mul,MvPolynomial.eval_C,
    Nat.cast_mul,MvPolynomial.eval_prod,Nat.cast_prod]
  apply congrArg (fun x : ℚ => (coeff a : ℚ)*x)
  apply Finset.prod_congr rfl
  intro c _
  exact coordinateBinomial_eval c (degree a c) m (hm c)

end FourPapers.MultivariatePositiveBinomial

#print axioms FourPapers.MultivariatePositiveBinomial.polynomial_eval

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.ThreeTermHomologyMap -/
section

/-!
# The actual map on three-term homology

A commuting triple of linear maps induces a map on the literal quotient
of cycles by boundaries. Its value on every represented class is retained
explicitly. The construction is over a commutative ring and introduces no
injectivity, splitting, or dimension hypothesis.
-/

section
set_option autoImplicit false
noncomputable section

namespace FourPapers.FilteredHomology

variable {K X Y Z X' Y' Z' : Type*} [CommRing K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
  [AddCommGroup Z] [Module K Z] [AddCommGroup X'] [Module K X']
  [AddCommGroup Y'] [Module K Y'] [AddCommGroup Z'] [Module K Z']

def threeTermCycleMap (g : Y →ₗ[K] Z) (g' : Y' →ₗ[K] Z')
    (b : Y →ₗ[K] Y') (c : Z →ₗ[K] Z')
    (hg : ∀ y, c (g y) = g' (b y)) :
    LinearMap.ker g →ₗ[K] LinearMap.ker g' :=
  (b.comp (LinearMap.ker g).subtype).codRestrict _ (by
    intro y
    change g' (b y.val) = 0
    rw [← hg, y.property, c.map_zero])

@[simp] theorem threeTermCycleMap_val (g : Y →ₗ[K] Z) (g' : Y' →ₗ[K] Z')
    (b : Y →ₗ[K] Y') (c : Z →ₗ[K] Z')
    (hg : ∀ y, c (g y) = g' (b y)) (z : LinearMap.ker g) :
    (threeTermCycleMap g g' b c hg z).val = b z.val := rfl

def threeTermHomologyMap
    (f : X →ₗ[K] Y) (g : Y →ₗ[K] Z) (hfg : g.comp f = 0)
    (f' : X' →ₗ[K] Y') (g' : Y' →ₗ[K] Z') (hfg' : g'.comp f' = 0)
    (a : X →ₗ[K] X') (b : Y →ₗ[K] Y') (c : Z →ₗ[K] Z')
    (hf : ∀ x, b (f x) = f' (a x))
    (hg : ∀ y, c (g y) = g' (b y)) :
    Homology f g hfg →ₗ[K] Homology f' g' hfg' :=
  Submodule.mapQ (LinearMap.range (boundaryMap f g hfg))
    (LinearMap.range (boundaryMap f' g' hfg'))
    (threeTermCycleMap g g' b c hg) (by
      rintro _ ⟨x, rfl⟩
      exact ⟨a x, Subtype.ext (hf x).symm⟩)

@[simp] theorem threeTermHomologyMap_class
    (f : X →ₗ[K] Y) (g : Y →ₗ[K] Z) (hfg : g.comp f = 0)
    (f' : X' →ₗ[K] Y') (g' : Y' →ₗ[K] Z') (hfg' : g'.comp f' = 0)
    (a : X →ₗ[K] X') (b : Y →ₗ[K] Y') (c : Z →ₗ[K] Z')
    (hf : ∀ x, b (f x) = f' (a x))
    (hg : ∀ y, c (g y) = g' (b y)) (z : LinearMap.ker g) :
    threeTermHomologyMap f g hfg f' g' hfg' a b c hf hg (homologyClass f g hfg z) =
      homologyClass f' g' hfg' (threeTermCycleMap g g' b c hg z) := rfl

/-- Boundary reflection proves injectivity of this specific induced map.
The criterion concerns actual representatives of cycles and boundaries. -/
theorem threeTermHomologyMap_injective_of_reflects_boundaries
    (f : X →ₗ[K] Y) (g : Y →ₗ[K] Z) (hfg : g.comp f = 0)
    (f' : X' →ₗ[K] Y') (g' : Y' →ₗ[K] Z') (hfg' : g'.comp f' = 0)
    (a : X →ₗ[K] X') (b : Y →ₗ[K] Y') (c : Z →ₗ[K] Z')
    (hf : ∀ x, b (f x) = f' (a x))
    (hg : ∀ y, c (g y) = g' (b y))
    (hreflect : ∀ y, g y = 0 → (∃ x', f' x' = b y) → ∃ x, f x = y) :
    Function.Injective (threeTermHomologyMap f g hfg f' g' hfg' a b c hf hg) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨z, rfl⟩ := (LinearMap.range (boundaryMap f g hfg)).mkQ_surjective x
  change threeTermHomologyMap f g hfg f' g' hfg' a b c hf hg
    (homologyClass f g hfg z) = 0 at hx
  rw [threeTermHomologyMap_class] at hx
  obtain ⟨w, hw⟩ := (Submodule.Quotient.mk_eq_zero
    (LinearMap.range (boundaryMap f' g' hfg'))).mp hx
  have hfw : f' w = b z.val := congrArg Subtype.val hw
  obtain ⟨y, hy⟩ := hreflect z.val z.property ⟨w, hfw⟩
  apply (Submodule.mem_bot K).mpr
  apply (Submodule.Quotient.mk_eq_zero (LinearMap.range (boundaryMap f g hfg))).mpr
  exact ⟨y, Subtype.ext hy⟩

end FourPapers.FilteredHomology

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.FiniteComplexRanks -/
section

/-! # Recovering differential ranks from all actual homology dimensions -/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
noncomputable section

namespace FourPapers.FilteredHomology

open Classical

variable {K X Y Z : Type*} [Field K]
  [AddCommGroup X] [Module K X] [FiniteDimensional K X]
  [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y]
  [AddCommGroup Z] [Module K Z]
  (f : X →ₗ[K] Y) (g : Y →ₗ[K] Z) (hfg : g.comp f=0)

def boundaryRangeEquiv : LinearMap.range (boundaryMap f g hfg) ≃ₗ[K] LinearMap.range f where
  toFun z := ⟨z.val.val, by obtain ⟨x,hx⟩ := z.property; exact ⟨x,congrArg Subtype.val hx⟩⟩
  invFun z := ⟨⟨z.val,by
      obtain ⟨x, hx⟩ := z.property
      rw [← hx]
      exact LinearMap.congr_fun hfg x⟩,by
        obtain ⟨x,hx⟩ := z.property
        exact ⟨x,Subtype.ext hx⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finrank_homology_add_finrank_source :
    Module.finrank K (Homology f g hfg)+Module.finrank K X =
      Module.finrank K (LinearMap.ker g)+Module.finrank K (LinearMap.ker f) := by
  have hq := Submodule.finrank_quotient_add_finrank
    (LinearMap.range (boundaryMap f g hfg))
  have hr := (boundaryRangeEquiv f g hfg).finrank_eq
  have hn := LinearMap.finrank_range_add_finrank_ker f
  change Module.finrank K (Homology f g hfg)+
    Module.finrank K (LinearMap.range (boundaryMap f g hfg)) =
      Module.finrank K (LinearMap.ker g) at hq
  omega

end FourPapers.FilteredHomology

namespace FourPapers.FiniteComplexRanks

open FilteredHomology

variable {K : Type*} [Field K] (C : ℕ → Type*)
  [∀ p,AddCommGroup (C p)] [∀ p,Module K (C p)] [∀ p,FiniteDimensional K (C p)]
  (d e : ∀ p,C (p+1) →ₗ[K] C p)

def previous (d : ∀ p,C (p+1) →ₗ[K] C p) : ∀ p,C p →ₗ[K] C p.pred
  | 0 => 0
  | p+1 => d p

variable (hdd : ∀ p,(d p).comp (d (p+1))=0)
  (hee : ∀ p,(e p).comp (e (p+1))=0)

include hdd in
theorem previous_comp (p : ℕ) : (previous C d p).comp (d p)=0 := by
  cases p with
  | zero => exact LinearMap.zero_comp _
  | succ p => exact hdd p

/-- The first differential is determined recursively from H₀, the next
from H₁, and so on. No bound on the number of nonzero degrees is needed. -/
theorem kernel_finrank_eq_of_homology_finrank_eq
    (hH : ∀ p,
      Module.finrank K (Homology (d p) (previous C d p) (previous_comp C d hdd p)) =
      Module.finrank K (Homology (e p) (previous C e p) (previous_comp C e hee p))) :
    ∀ p, Module.finrank K (LinearMap.ker (previous C d p)) =
      Module.finrank K (LinearMap.ker (previous C e p)) := by
  intro p
  induction p with
  | zero => rfl
  | succ p ih =>
    have hd := finrank_homology_add_finrank_source (d p) (previous C d p)
      (previous_comp C d hdd p)
    have he := finrank_homology_add_finrank_source (e p) (previous C e p)
      (previous_comp C e hee p)
    have hβ := hH p
    change Module.finrank K (LinearMap.ker (d p)) = Module.finrank K (LinearMap.ker (e p))
    omega

end FourPapers.FiniteComplexRanks

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.SplittingHomologyComparison -/
section

/-! # Agreement of the two literal kernel/image homology presentations -/

section
set_option autoImplicit false
noncomputable section

namespace FourPapers.ProjectiveComplexSplitting

variable {R : Type*} [CommRing R]
  (C : ℕ → Type*) [∀ n, AddCommGroup (C n)] [∀ n, Module R (C n)]
  (d : ∀ n, C (n+1) →ₗ[R] C n)
  (dd : ∀ n, (d n).comp (d (n+1)) = 0)

def previous : (n : ℕ) → C n →ₗ[R] C n.pred
  | 0 => 0
  | n+1 => d n

include dd in
theorem previous_comp (n : ℕ) : (previous C d n).comp (d n) = 0 := by
  cases n with
  | zero => exact LinearMap.zero_comp _
  | succ n => exact dd n

def splittingCyclesEquiv (n : ℕ) :
    cycles C d n ≃ₗ[R] LinearMap.ker (previous C d n) := by
  cases n with
  | zero =>
      exact
        { toFun := fun x => ⟨x.val, rfl⟩
          invFun := fun x => ⟨x.val, trivial⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
  | succ n => exact LinearEquiv.refl R _

theorem splittingCyclesEquiv_boundaries (n : ℕ) :
    (boundaries C d dd n).map (splittingCyclesEquiv C d n).toLinearMap =
      LinearMap.range (FilteredHomology.boundaryMap (d n) (previous C d n)
        (previous_comp C d dd n)) := by
  cases n <;>
    (ext x
     constructor
     · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
       exact ⟨z, rfl⟩
     · rintro ⟨z, rfl⟩
       exact ⟨toCycles C d dd _ z, ⟨z, rfl⟩, rfl⟩)

/-- Both sides use the actual kernel and actual image, including the full
degree-zero cycle module. Only their subtype presentations differ. -/
def splittingHomologyEquiv (n : ℕ) :
    Homology C d dd n ≃ₗ[R]
      FilteredHomology.Homology (d n) (previous C d n) (previous_comp C d dd n) :=
  Submodule.Quotient.equiv _ _ (splittingCyclesEquiv C d n)
    (splittingCyclesEquiv_boundaries C d dd n)

end FourPapers.ProjectiveComplexSplitting

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.CycleQuotientHomologyMap -/
section

/-!
# Maps from a cycle quotient to three-term homology

A cycle inclusion and a compatible map on boundary preimages induce the
literal map on quotient modules. Boundary reflection proves its injectivity.
All quotient constructions are performed over abstract module parameters.
-/

section
set_option autoImplicit false
noncomputable section
namespace FourPapers.FilteredHomology

variable {K : Type*} [CommRing K]
  {U C X Y Z : Type*}
  [AddCommGroup U] [Module K U] [AddCommGroup C] [Module K C]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
  [AddCommGroup Z] [Module K Z]

/-- The map from any cycle quotient to the actual three-term homology.
Both the cycle inclusion and the boundary preimage map are actual maps. -/
def cycleQuotientHomologyMap
    (f : X →ₗ[K] Y) (g : Y →ₗ[K] Z) (hfg : g.comp f = 0)
    (b : U →ₗ[K] C) (ι : C →ₗ[K] LinearMap.ker g) (j : U →ₗ[K] X)
    (h : ∀ u, ι (b u) = boundaryMap f g hfg (j u)) :
    (C ⧸ LinearMap.range b) →ₗ[K] Homology f g hfg :=
  (LinearMap.range b).mapQ (LinearMap.range (boundaryMap f g hfg)) ι (by
    rintro c ⟨u, rfl⟩
    exact ⟨j u, (h u).symm⟩)

@[simp] theorem cycleQuotientHomologyMap_mk
    (f : X →ₗ[K] Y) (g : Y →ₗ[K] Z) (hfg : g.comp f = 0)
    (b : U →ₗ[K] C) (ι : C →ₗ[K] LinearMap.ker g) (j : U →ₗ[K] X)
    (h : ∀ u, ι (b u) = boundaryMap f g hfg (j u)) (c : C) :
    cycleQuotientHomologyMap f g hfg b ι j h (Submodule.Quotient.mk c) =
      homologyClass f g hfg (ι c) := rfl

/-- Boundary reflection is exactly the condition needed for injection. -/
theorem cycleQuotientHomologyMap_injective
    (f : X →ₗ[K] Y) (g : Y →ₗ[K] Z) (hfg : g.comp f = 0)
    (b : U →ₗ[K] C) (ι : C →ₗ[K] LinearMap.ker g) (j : U →ₗ[K] X)
    (h : ∀ u, ι (b u) = boundaryMap f g hfg (j u))
    (hreflect : ∀ c, ι c ∈ LinearMap.range (boundaryMap f g hfg) →
      c ∈ LinearMap.range b) :
    Function.Injective (cycleQuotientHomologyMap f g hfg b ι j h) := by
  apply LinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro z hz
  obtain ⟨c, rfl⟩ := (LinearMap.range b).mkQ_surjective z
  have hc : homologyClass f g hfg (ι c) = 0 := hz
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  apply hreflect c
  exact (Submodule.Quotient.mk_eq_zero _).mp hc

end FourPapers.FilteredHomology

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.SubmoduleHomologyMap -/
section

/-! # Homology maps from homogeneous submodules

The source and target cycles below are literal submodules of one ambient
module.  Expressing this structure in the interface fixes the canonical
submodule actions before specializing to a concrete exterior complex.
-/

section
set_option autoImplicit false
noncomputable section

namespace FourPapers.FilteredHomology

variable {K M : Type*} [CommRing K] [AddCommGroup M] [Module K M]

/-- Inclusion of a cycle submodule induces the literal map of quotients.
The boundary compatibility records equality in the ambient module. -/
def submoduleHomologyMap (T : Submodule K M) (D : T →ₗ[K] T)
    (hD : D.comp D = 0) (U C : Submodule K T)
    (b : U →ₗ[K] C) (hC : C ≤ LinearMap.ker D)
    (hb : ∀ u, (b u).val = D u.val) :
    (C ⧸ LinearMap.range b) →ₗ[K] Homology D D hD :=
  cycleQuotientHomologyMap (K := K) (U := U) (C := C)
    (X := T) (Y := T) (Z := T) D D hD b
    (Submodule.inclusion hC) U.subtype (fun u => Subtype.ext (hb u))

@[simp] theorem submoduleHomologyMap_mk (T : Submodule K M) (D : T →ₗ[K] T)
    (hD : D.comp D = 0) (U C : Submodule K T)
    (b : U →ₗ[K] C) (hC : C ≤ LinearMap.ker D)
    (hb : ∀ u, (b u).val = D u.val) (c : C) :
    submoduleHomologyMap T D hD U C b hC hb (Submodule.Quotient.mk c) =
      homologyClass D D hD ⟨c.val, hC c.property⟩ := rfl

/-- If every cycle that bounds in the total complex already bounds through
the indicated incoming submodule, the induced homology map is injective. -/
theorem submoduleHomologyMap_injective (T : Submodule K M) (D : T →ₗ[K] T)
    (hD : D.comp D = 0) (U C : Submodule K T)
    (b : U →ₗ[K] C) (hC : C ≤ LinearMap.ker D)
    (hb : ∀ u, (b u).val = D u.val)
    (hreflect : ∀ c : C, (∃ a : T, D a = c.val) → c ∈ LinearMap.range b) :
    Function.Injective (submoduleHomologyMap T D hD U C b hC hb) := by
  unfold submoduleHomologyMap
  apply cycleQuotientHomologyMap_injective
  intro c hc
  obtain ⟨a, ha⟩ := hc
  exact hreflect c ⟨a, congrArg Subtype.val ha⟩

end FourPapers.FilteredHomology

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.HomologyCycleQuotientMap -/
section

/-!
# Maps from homology to a quotient of cycles

A linear map on cycles descends to homology when it carries boundaries to
the prescribed boundary submodule. The construction is kept over abstract
modules so that applications can supply their concrete cycle carriers
without expanding those carriers during quotient elaboration.
-/

section
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace FourPapers.FilteredHomology

variable {K : Type*} [CommRing K]
  {U C X Y Z : Type*}
  [AddCommGroup U] [Module K U] [AddCommGroup C] [Module K C]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
  [AddCommGroup Z] [Module K Z]

/-- The literal quotient map induced by a map of cycle modules. -/
def homologyCycleQuotientMap
    (f : X →ₗ[K] Y) (g : Y →ₗ[K] Z) (hfg : g.comp f = 0)
    (b : U →ₗ[K] C) (π : LinearMap.ker g →ₗ[K] C)
    (h : ∀ x, π (boundaryMap f g hfg x) ∈ LinearMap.range b) :
    Homology f g hfg →ₗ[K] (C ⧸ LinearMap.range b) :=
  (LinearMap.range (boundaryMap f g hfg)).mapQ (LinearMap.range b) π (by
    rintro c ⟨x, rfl⟩
    exact h x)

@[simp] theorem homologyCycleQuotientMap_class
    (f : X →ₗ[K] Y) (g : Y →ₗ[K] Z) (hfg : g.comp f = 0)
    (b : U →ₗ[K] C) (π : LinearMap.ker g →ₗ[K] C)
    (h : ∀ x, π (boundaryMap f g hfg x) ∈ LinearMap.range b)
    (z : LinearMap.ker g) :
    homologyCycleQuotientMap f g hfg b π h (homologyClass f g hfg z) =
      Submodule.Quotient.mk (π z) := rfl

/-- The same map with canonical submodule structures fixed by the ambient
module. This form is convenient for degree pieces of a concrete complex. -/
def submoduleHomologyProjection {M : Type*} [AddCommGroup M] [Module K M]
    (T : Submodule K M) (D : T →ₗ[K] T) (hD : D.comp D = 0)
    (U C : Submodule K T) (b : U →ₗ[K] C)
    (π : LinearMap.ker D →ₗ[K] C)
    (h : ∀ x, π (boundaryMap D D hD x) ∈ LinearMap.range b) :
    Homology D D hD →ₗ[K] (C ⧸ LinearMap.range b) :=
  homologyCycleQuotientMap (K := K) (U := U) (C := C)
    (X := T) (Y := T) (Z := T) D D hD b π h

end FourPapers.FilteredHomology

end
end
end


end
