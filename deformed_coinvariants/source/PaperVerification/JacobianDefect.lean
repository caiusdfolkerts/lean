module

public import PaperVerification.JacobianFreeness
public import PaperVerification.EulerReduction
public import PaperVerification.EulerResonance

/-!
# The actual Euler relation space of a Jacobian perturbation

The aggregate map has the same image as the paper's sum of individual operator
images. Its Euler kernel calculation therefore applies to the literal quotient,
including at exceptional parameters.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial
open scoped BigOperators

namespace PaperVerification.JacobianDivergence

variable {K ι : Type*} [Field K] [Fintype ι]
local instance defectDecidableEq : DecidableEq ι := Classical.decEq ι
local notation "P" => MvPolynomial ι K

def coefficientMap (F : P) : (ι → P) →ₗ[K] P :=
  (KoszulSyzygies.coefficient (gradient F)).restrictScalars K

def aggregateOperator (F : P) (t : K) : (ι → P) →ₗ[K] P :=
  EulerReduction.perturbed (coefficientMap F) divergence (LinearMap.mulLeft K F) t

theorem aggregateOperator_apply (F : P) (t : K) (g : ι → P) :
    aggregateOperator F t g = ∑ i, EulerJacobian.operator (gradient F) F t i (g i) := by
  simp only [aggregateOperator, EulerReduction.perturbed_apply, coefficientMap,
    LinearMap.restrictScalars_apply, KoszulSyzygies.coefficient_apply,
    divergence_apply, LinearMap.mulLeft_apply, EulerJacobian.operator,
    Finset.sum_add_distrib, Finset.mul_sum, Finset.smul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem aggregateOperator_single (F p : P) (t : K) (i : ι) :
    aggregateOperator F t (Pi.single i p) = EulerJacobian.operator (gradient F) F t i p := by
  classical
  simp only [aggregateOperator, EulerReduction.perturbed_apply, coefficientMap,
    LinearMap.restrictScalars_apply, coefficient_single, divergence_single,
    LinearMap.mulLeft_apply, EulerJacobian.operator]
  rw [mul_comm p]

theorem aggregate_range_eq_hit (F : P) (t : K) :
    LinearMap.range (aggregateOperator F t) = EulerJacobian.hit (gradient F) F t := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    rw [aggregateOperator_apply]
    exact (EulerJacobian.hit (gradient F) F t).sum_mem fun i _ =>
      EulerJacobian.operator_mem_hit (gradient F) F t i (g i)
  · apply Submodule.span_le.mpr
    rintro p ⟨i, q, rfl⟩
    exact ⟨Pi.single i q, aggregateOperator_single F q t i⟩

theorem coefficientMap_range (F : P) :
    LinearMap.range (coefficientMap F) = jacobianSubmodule F := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    change (∑ i, g i * gradient F i) ∈ Ideal.span (Set.range (gradient F))
    exact (Ideal.span (Set.range (gradient F))).sum_mem fun i _ =>
      Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · intro p hp
    change p ∈ Submodule.span P (Set.range (gradient F)) at hp
    have aux : ∀ q : P, q * p ∈ LinearMap.range (coefficientMap F) := by
      induction hp using Submodule.span_induction with
      | mem p hp =>
        obtain ⟨i, rfl⟩ := hp
        intro q
        exact ⟨Pi.single i q, coefficient_single (gradient F) i q⟩
      | zero => intro q; simpa only [mul_zero] using (LinearMap.range (coefficientMap F)).zero_mem
      | add p r hp hr ihp ihr =>
        intro q
        simpa only [mul_add] using (LinearMap.range (coefficientMap F)).add_mem (ihp q) (ihr q)
      | smul a p hp ih =>
        intro q
        simpa only [smul_eq_mul, mul_assoc] using ih (q * a)
    simpa only [one_mul] using aux 1

def eulerFieldMap (w : ι → ℕ) : P →ₗ[K] (ι → P) where
  toFun := eulerField w
  map_add' p q := by ext i; simp [eulerField, mul_add, smul_add]
  map_smul' c p := by
    ext i
    simp only [eulerField, Pi.smul_apply, RingHom.id_apply,
      mul_smul_comm, smul_comm c]

@[simp] theorem eulerFieldMap_apply (w : ι → ℕ) (p : P) :
    eulerFieldMap w p = eulerField w p := rfl

def normalizedEulerField (w : ι → ℕ) (h : ℕ) : P →ₗ[K] (ι → P) :=
  (h : K)⁻¹ • eulerFieldMap w

theorem coefficient_normalizedEuler [CharZero K] (F : P) (w : ι → ℕ) (h : ℕ)
    (hh : 0 < h) (hF : F.IsWeightedHomogeneous w h) :
    (coefficientMap F).comp (normalizedEulerField w h) = LinearMap.mulLeft K F := by
  apply LinearMap.ext
  intro p
  change coefficientMap F ((h : K)⁻¹ • eulerField w p) = F * p
  rw [map_smul]
  have he : coefficientMap F (eulerField w p) = (h : K) • (F * p) := by
    simpa only [coefficientMap, LinearMap.restrictScalars_apply, Nat.cast_smul_eq_nsmul]
      using coefficient_eulerField F w h hF p
  rw [he, smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hh)), one_smul]

theorem normalizedEuler_scalar (w : ι → ℕ) (h : ℕ) (t : K) :
    EulerReduction.eulerScalar divergence (normalizedEulerField w h) t =
      EulerResonance.scalarEuler w (1 + (t / h) * (∑ i, w i : ℕ)) (t / h) := by
  apply LinearMap.ext
  intro p
  simp only [EulerReduction.eulerScalar_apply, normalizedEulerField,
    LinearMap.smul_apply, eulerFieldMap_apply, map_smul, divergence_eulerField,
    EulerResonance.scalarEuler_apply, weightedEuler_apply, smul_add,
    ← Nat.cast_smul_eq_nsmul K, smul_smul, add_smul, one_smul, div_eq_mul_inv,
    add_assoc, mul_assoc]

theorem scaled_divergence_kernel_image (F : P) (t : K) (ht : t ≠ 0) :
    (LinearMap.ker (coefficientMap F)).map (t • divergence) = divergenceSpace F := by
  rw [Submodule.map_smul divergence _ t ht]
  rfl

/-- Exact membership in the relation space, for the genuine operator family.
No isolated-critical-point or regular-sequence hypothesis is needed here. -/
theorem potential_hit_iff [CharZero K]
    (F : P) (w : ι → ℕ) (h : ℕ) (t : K)
    (hh : 0 < h) (hF : F.IsWeightedHomogeneous w h) (ht : t ≠ 0) (p : P) :
    F * p ∈ EulerJacobian.hit (gradient F) F t ↔
      p ∈ LinearMap.range
        (EulerResonance.scalarEuler w (1 + (t / h) * (∑ i, w i : ℕ)) (t / h)) ⊔
        divergenceSpace F := by
  have he := EulerReduction.potential_relation_iff
    (coefficientMap F) divergence (normalizedEulerField w h) (LinearMap.mulLeft K F) t
    (coefficient_normalizedEuler F w h hh hF) p
  rw [← aggregate_range_eq_hit, ← normalizedEuler_scalar,
    ← scaled_divergence_kernel_image F t ht]
  exact he

def potentialToHitQuotient (F : P) (t : K) :
    P →ₗ[K] (P ⧸ EulerJacobian.hit (gradient F) F t) :=
  (EulerJacobian.hit (gradient F) F t).mkQ.comp (LinearMap.mulLeft K F)

/-- The image of the Jacobian ideal in the literal differential quotient. -/
def defectImage (F : P) (t : K) :
    Submodule K (P ⧸ EulerJacobian.hit (gradient F) F t) :=
  (jacobianSubmodule F).map (EulerJacobian.hit (gradient F) F t).mkQ

/-- The hit space is contained in the actual Jacobian ideal at every parameter. -/
theorem hit_le_jacobian [CharZero K] (F : P) (w : ι → ℕ) (h : ℕ) (t : K)
    (hh : 0 < h) (hF : F.IsWeightedHomogeneous w h) :
    EulerJacobian.hit (gradient F) F t ≤ jacobianSubmodule F := by
  have he : EulerJacobian.EulerRelation (gradient F) F w (h : K) := by
    simpa only [EulerJacobian.EulerRelation, gradient, Nat.cast_smul_eq_nsmul]
      using hF.sum_weight_X_mul_pderiv
  exact EulerJacobian.hit_le_coefficientIdeal (gradient F) F t
    (EulerJacobian.perturbation_mem_ideal (gradient F) F w (h : K) he
      (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hh)))

/-- The literal quotient of Jacobian elements by the hit relations. The preceding
containment identifies these relations with the paper's subspace `H_t(F)`. -/
abbrev DefectQuotient (F : P) (t : K) :=
  jacobianSubmodule F ⧸
    (EulerJacobian.hit (gradient F) F t).comap (jacobianSubmodule F).subtype

def defectToHit (F : P) (t : K) :
    jacobianSubmodule F →ₗ[K] (P ⧸ EulerJacobian.hit (gradient F) F t) :=
  (EulerJacobian.hit (gradient F) F t).mkQ.comp (jacobianSubmodule F).subtype

theorem defectToHit_kernel (F : P) (t : K) :
    LinearMap.ker (defectToHit F t) =
      (EulerJacobian.hit (gradient F) F t).comap (jacobianSubmodule F).subtype := by
  ext x
  change (EulerJacobian.hit (gradient F) F t).mkQ (x : P) = 0 ↔ _
  simp only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
    Submodule.subtype_apply]

theorem defectToHit_range (F : P) (t : K) :
    LinearMap.range (defectToHit F t) = defectImage F t := by
  rw [defectToHit, LinearMap.range_comp, Submodule.range_subtype, defectImage]

def defectQuotientEquivImage (F : P) (t : K) :
    DefectQuotient F t ≃ₗ[K] defectImage F t :=
  (Submodule.quotEquivOfEq _ _ (defectToHit_kernel F t).symm).trans
    ((defectToHit F t).quotKerEquivRange.trans
      (LinearEquiv.ofEq _ _ (defectToHit_range F t)))

theorem potentialToHitQuotient_range [CharZero K]
    (F : P) (w : ι → ℕ) (h : ℕ) (t : K)
    (hh : 0 < h) (hF : F.IsWeightedHomogeneous w h) :
    LinearMap.range (potentialToHitQuotient F t) = defectImage F t := by
  have hJ := EulerReduction.coefficient_range
    (coefficientMap F) divergence (normalizedEulerField w h) (LinearMap.mulLeft K F) t
    (coefficient_normalizedEuler F w h hh hF)
  change LinearMap.range (coefficientMap F) =
    LinearMap.range (aggregateOperator F t) ⊔ LinearMap.range (LinearMap.mulLeft K F) at hJ
  rw [coefficientMap_range, aggregate_range_eq_hit] at hJ
  rw [potentialToHitQuotient, LinearMap.range_comp, defectImage, hJ,
    Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq]

theorem potentialToHitQuotient_kernel [CharZero K]
    (F : P) (w : ι → ℕ) (h : ℕ) (t : K)
    (hh : 0 < h) (hF : F.IsWeightedHomogeneous w h) (ht : t ≠ 0) :
    LinearMap.ker (potentialToHitQuotient F t) =
      LinearMap.range
        (EulerResonance.scalarEuler w (1 + (t / h) * (∑ i, w i : ℕ)) (t / h)) ⊔
        divergenceSpace F := by
  ext p
  change (EulerJacobian.hit (gradient F) F t).mkQ (F * p) = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact potential_hit_iff F w h t hh hF ht p

theorem normalized_resonance [CharZero K] (w : ι → ℕ) (h d : ℕ) (t : K)
    (hh : 0 < h) (hres : (h : K) + t * ((∑ i, w i : ℕ) + d : K) = 0) :
    t ≠ 0 ∧
    (1 + (t / h) * (∑ i, w i : ℕ)) + (t / h) * (d : K) = 0 ∧
    ∀ j : ℕ, j ≠ d →
      (1 + (t / h) * (∑ i, w i : ℕ)) + (t / h) * (j : K) ≠ 0 := by
  have hhK : (h : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hh)
  have ht : t ≠ 0 := by
    intro ht
    rw [ht, zero_mul, add_zero] at hres
    exact hhK hres
  have hscale (j : ℕ) : (h : K) *
      ((1 + (t / h) * (∑ i, w i : ℕ)) + (t / h) * (j : K)) =
      (h : K) + t * ((∑ i, w i : ℕ) + j : K) := by
    field_simp [hhK]
    <;> ring
  have hd : (1 + (t / h) * (∑ i, w i : ℕ)) + (t / h) * (d : K) = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left hhK
    rw [hscale, hres]
  refine ⟨ht, hd, ?_⟩
  intro j hj hz
  have hjres : (h : K) + t * ((∑ i, w i : ℕ) + j : K) = 0 := by
    rw [← hscale, hz, mul_zero]
  have he : t * ((j : K) - (d : K)) = 0 := by
    calc
      _ = ((h : K) + t * ((∑ i, w i : ℕ) + j : K)) -
          ((h : K) + t * ((∑ i, w i : ℕ) + d : K)) := by ring
      _ = 0 := by rw [hjres, hres, sub_self]
  exact hj (Nat.cast_injective (sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left ht)))

/-- The canonical exceptional defect, with the actual divergence quotient on
the right. No finite-dimensional cutoff or regular-gradient assumption enters
this identification. -/
def exceptionalDefectEquiv [CharZero K]
    (F : P) (w : ι → ℕ) (h d : ℕ) (t : K)
    (hh : 0 < h) (hF : F.IsWeightedHomogeneous w h)
    (hres : (h : K) + t * ((∑ i, w i : ℕ) + d : K) = 0) :
    defectImage F t ≃ₗ[K] EulerResonance.quotientComponent w d (divergenceSpace F) := by
  obtain ⟨ht, hd, hother⟩ := normalized_resonance w h d t hh hres
  exact (LinearEquiv.ofEq _ _ (potentialToHitQuotient_range F w h t hh hF).symm).trans
    ((potentialToHitQuotient F t).quotKerEquivRange.symm.trans
      ((Submodule.quotEquivOfEq _ _ (potentialToHitQuotient_kernel F w h t hh hF ht)).trans
        (EulerResonance.resonantQuotientEquiv w
          (1 + (t / h) * (∑ i, w i : ℕ)) (t / h) d hd hother
          (divergenceSpace F)
          (fun f hf => homogeneousComponent_mem_divergenceSpace F w h hF f hf d))))

/-- The same canonical isomorphism with `J(F)/H_t(F)` as its actual source. -/
def exceptionalDefectQuotientEquiv [CharZero K]
    (F : P) (w : ι → ℕ) (h d : ℕ) (t : K)
    (hh : 0 < h) (hF : F.IsWeightedHomogeneous w h)
    (hres : (h : K) + t * ((∑ i, w i : ℕ) + d : K) = 0) :
    DefectQuotient F t ≃ₗ[K] EulerResonance.quotientComponent w d (divergenceSpace F) :=
  (defectQuotientEquivImage F t).trans (exceptionalDefectEquiv F w h d t hh hF hres)

end PaperVerification.JacobianDivergence
