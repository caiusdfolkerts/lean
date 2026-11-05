module

public import PaperVerification.VectorJacobianKernel
public import PaperVerification.EulerInjective
public import PaperVerification.EulerParameters
public import PaperVerification.JacobianDefect

/-!
# The normalized vector-valued Euler family

The target is the actual finite direct sum of polynomial copies, represented
as a finite function space. The hit subspace is the image of the sum of the
displayed first-order operators. Its equality with the span of their individual
images is proved below, so the construction does not take an ideal closure.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open MvPolynomial
open scoped BigOperators

namespace PaperVerification.VectorEuler

variable {K ι κ : Type*} [Field K] [CharZero K] [Fintype ι]
local notation "P" => MvPolynomial ι K
local notation "M" => κ → P
local instance vectorEulerBasicDecidableEq : DecidableEq ι := Classical.decEq ι

/-- Multiplication by the entire vector of defining equations. -/
def potential (F : κ → P) : P →ₗ[K] M where
  toFun p a := F a * p
  map_add' p q := by funext a; exact mul_add _ _ _
  map_smul' c p := by funext a; exact mul_smul_comm _ _ _

@[simp] theorem potential_apply (F : κ → P) (p : P) (a : κ) :
    potential F p a = F a * p := rfl

/-- The literal normalized first-order operator in Section 6.3. -/
def operator (F : κ → P) (h : κ → ℕ) (t : K) (i : ι) (p : P) : M :=
  fun a => (h a : K)⁻¹ • (pderiv i (F a) * p) + t • (F a * pderiv i p)

def aggregate (F : κ → P) (h : κ → ℕ) (t : K) : (ι → P) →ₗ[K] M :=
  EulerReduction.perturbed (VectorJacobian.normalizedJacobianMap F h)
    JacobianDivergence.divergence (potential F) t

def coefficientSpace (F : κ → P) (h : κ → ℕ) : Submodule K M :=
  LinearMap.range (VectorJacobian.normalizedJacobianMap F h)

/-- The literal normalized Jacobian column `A_i`. -/
def coefficientColumn (F : κ → P) (h : κ → ℕ) (i : ι) : M :=
  fun a => (h a : K)⁻¹ • pderiv i (F a)

def coefficientMapPolynomial (F : κ → P) (h : κ → ℕ) : (ι → P) →ₗ[P] M where
  toFun g := ∑ i, g i • coefficientColumn F h i
  map_add' g u := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c g := by
    simp only [Pi.smul_apply, RingHom.id_apply, smul_smul, Finset.smul_sum, smul_eq_mul]

@[simp] theorem coefficientMapPolynomial_apply_sum (F : κ → P) (h : κ → ℕ) (g : ι → P) :
    coefficientMapPolynomial F h g = ∑ i, g i • coefficientColumn F h i := rfl

theorem coefficientMapPolynomial_apply (F : κ → P) (h : κ → ℕ) (g : ι → P) :
    coefficientMapPolynomial F h g = VectorJacobian.normalizedJacobianMap F h g := by
  funext a
  rw [coefficientMapPolynomial_apply_sum, Finset.sum_apply]
  change (∑ i, g i * ((h a : K)⁻¹ • pderiv i (F a))) =
    (h a : K)⁻¹ • ∑ i, pderiv i (F a) * g i
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_smul_comm, mul_comm]

theorem coefficientMapPolynomial_range (F : κ → P) (h : κ → ℕ) :
    LinearMap.range (coefficientMapPolynomial F h) =
      Submodule.span P (Set.range (coefficientColumn F h)) := by
  classical
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ (g i) (Submodule.subset_span ⟨i, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    refine ⟨Pi.single i 1, ?_⟩
    simp [coefficientMapPolynomial, Pi.single_apply]

/-- The range model is exactly the paper's polynomial span `Σ_i A_i P`,
regarded as a vector subspace. -/
theorem coefficientSpace_eq_polynomial_span (F : κ → P) (h : κ → ℕ) :
    coefficientSpace F h =
      (Submodule.span P (Set.range (coefficientColumn F h))).restrictScalars K := by
  rw [← coefficientMapPolynomial_range]
  ext v
  change (∃ g, VectorJacobian.normalizedJacobianMap F h g = v) ↔
    ∃ g, coefficientMapPolynomial F h g = v
  simp only [coefficientMapPolynomial_apply]

def hit (F : κ → P) (h : κ → ℕ) (t : K) : Submodule K M :=
  LinearMap.range (aggregate F h t)

abbrev Defect (F : κ → P) (h : κ → ℕ) (t : K) :=
  coefficientSpace F h ⧸ (hit F h t).comap (coefficientSpace F h).subtype

def defectImage (F : κ → P) (h : κ → ℕ) (t : K) : Submodule K (M ⧸ hit F h t) :=
  (coefficientSpace F h).map (hit F h t).mkQ

def potentialToQuotient (F : κ → P) (h : κ → ℕ) (t : K) :
    P →ₗ[K] (M ⧸ hit F h t) := (hit F h t).mkQ.comp (potential F)

theorem aggregate_apply (F : κ → P) (h : κ → ℕ) (t : K) (g : ι → P) :
    aggregate F h t g = ∑ i, operator F h t i (g i) := by
  funext a
  simp only [aggregate, EulerReduction.perturbed_apply,
    VectorJacobian.normalizedJacobianMap_apply, VectorJacobian.jacobianMap_apply,
    potential_apply, JacobianDivergence.divergence_apply, operator,
    Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Finset.sum_add_distrib,
    Finset.mul_sum, Finset.smul_sum]

theorem aggregate_single (F : κ → P) (h : κ → ℕ) (t : K) (i : ι) (p : P) :
    aggregate F h t (Pi.single i p) = operator F h t i p := by
  classical
  funext a
  simp only [aggregate, EulerReduction.perturbed_apply,
    VectorJacobian.normalizedJacobianMap_apply, VectorJacobian.jacobianMap_apply,
    potential_apply, JacobianDivergence.divergence_single, operator,
    Pi.add_apply, Pi.smul_apply]
  simp [Pi.single_apply]

theorem hit_eq_span_images (F : κ → P) (h : κ → ℕ) (t : K) :
    hit F h t = Submodule.span K {v | ∃ i p, v = operator F h t i p} := by
  classical
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    rw [aggregate_apply]
    exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨i, g i, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, p, rfl⟩
    exact ⟨Pi.single i p, aggregate_single F h t i p⟩

/-- Weighted Euler, with the normalization in each row exactly cancelled. -/
theorem coefficient_euler (F : κ → P) (h : κ → ℕ) (w : ι → ℕ)
    (hh : ∀ a, 0 < h a)
    (hF : ∀ a, (F a).IsWeightedHomogeneous w (h a)) :
    (VectorJacobian.normalizedJacobianMap F h).comp
      (JacobianDivergence.eulerFieldMap w) = potential F := by
  apply LinearMap.ext
  intro p
  funext a
  change (h a : K)⁻¹ • VectorJacobian.jacobianMap F
    (JacobianDivergence.eulerField w p) a = F a * p
  have hc : VectorJacobian.jacobianMap F (JacobianDivergence.eulerField w p) a =
      (h a : K) • (F a * p) := by
    have he := JacobianDivergence.coefficient_eulerField (F a) w (h a) (hF a) p
    simpa only [VectorJacobian.jacobianMap_apply, KoszulSyzygies.coefficient_apply,
      JacobianDivergence.gradient, Nat.cast_smul_eq_nsmul, mul_comm] using he
  rw [hc, smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (hh a).ne'), one_smul]

theorem scalar_euler (w : ι → ℕ) (t : K) :
    EulerReduction.eulerScalar JacobianDivergence.divergence
      (JacobianDivergence.eulerFieldMap w) t =
      EulerResonance.scalarEuler w (1 + t * (∑ i, w i : ℕ)) t := by
  apply LinearMap.ext
  intro p
  simp only [EulerReduction.eulerScalar_apply, JacobianDivergence.eulerFieldMap_apply,
    JacobianDivergence.divergence_eulerField, EulerResonance.scalarEuler_apply,
    JacobianDivergence.weightedEuler_apply, smul_add,
    ← Nat.cast_smul_eq_nsmul K, smul_smul, add_smul, one_smul, add_assoc]

theorem hit_le_coefficient (F : κ → P) (h : κ → ℕ) (w : ι → ℕ) (t : K)
    (hh : ∀ a, 0 < h a)
    (hF : ∀ a, (F a).IsWeightedHomogeneous w (h a)) :
    hit F h t ≤ coefficientSpace F h :=
  EulerInjective.hit_le_coefficient (VectorJacobian.normalizedJacobianMap F h)
    JacobianDivergence.divergence (JacobianDivergence.eulerFieldMap w) (potential F) t
    (coefficient_euler F h w hh hF)

theorem potentialToQuotient_range (F : κ → P) (h : κ → ℕ) (w : ι → ℕ) (t : K)
    (hh : ∀ a, 0 < h a)
    (hF : ∀ a, (F a).IsWeightedHomogeneous w (h a)) :
    LinearMap.range (potentialToQuotient F h t) = defectImage F h t :=
  EulerInjective.potentialMap_range (VectorJacobian.normalizedJacobianMap F h)
    JacobianDivergence.divergence (JacobianDivergence.eulerFieldMap w) (potential F) t
    (coefficient_euler F h w hh hF)

def defectEquivImage (F : κ → P) (h : κ → ℕ) (t : K) :
    Defect F h t ≃ₗ[K] defectImage F h t :=
  EulerInjective.defectEquivImage (VectorJacobian.normalizedJacobianMap F h)
    JacobianDivergence.divergence (potential F) t

theorem scalarEuler_surjective_of_nonresonant (w : ι → ℕ) (t : K)
    (hnr : ∀ a : ι →₀ ℕ,
      1 + t * ((∑ i, w i : ℕ) + EulerJacobian.monomialWeight w a : K) ≠ 0) :
    Function.Surjective (EulerReduction.eulerScalar JacobianDivergence.divergence
      (JacobianDivergence.eulerFieldMap w) t) := by
  rw [scalar_euler, ← LinearMap.range_eq_top]
  apply top_unique
  intro p hpTop
  clear hpTop
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => exact Submodule.add_mem _ hp hq
  | monomial a c =>
    let z : K := 1 + t * ((∑ i, w i : ℕ) + EulerJacobian.monomialWeight w a : K)
    refine ⟨z⁻¹ • monomial a c, ?_⟩
    rw [map_smul, EulerResonance.scalarEuler_homogeneous w _ t
      (Finsupp.weight w a) _ (isWeightedHomogeneous_monomial w a c rfl)]
    have hz : (1 + t * (∑ i, w i : ℕ)) + t * (Finsupp.weight w a : K) = z := by
      dsimp [z]
      rw [EulerJacobian.monomialWeight_eq_weight]
      ring
    rw [hz, smul_smul, inv_mul_cancel₀ (hnr a), one_smul]

theorem hit_eq_coefficient_of_nonresonant [Nonempty ι]
    (F : κ → P) (h : κ → ℕ) (w : ι → ℕ) (t : K)
    (hw : ∀ i, 0 < w i) (hh : ∀ a, 0 < h a)
    (hF : ∀ a, (F a).IsWeightedHomogeneous w (h a))
    (hnr : ∀ d ∈ EulerJacobian.occurringDegrees (K := K) w,
      t ≠ -(1 : K) / ((∑ i, w i : ℕ) + d : K)) :
    hit F h t = coefficientSpace F h := by
  apply EulerInjective.hit_eq_coefficient_of_surjective
    (VectorJacobian.normalizedJacobianMap F h) JacobianDivergence.divergence
    (JacobianDivergence.eulerFieldMap w) (potential F) t (coefficient_euler F h w hh hF)
  apply scalarEuler_surjective_of_nonresonant w t
  simpa only [Nat.cast_one] using
    (EulerJacobian.nonresonance_iff w hw 1 t).mp (by simpa only [Nat.cast_one] using hnr)

/-- Resonance at degree `d` is unique in characteristic zero. -/
theorem resonance_eigenvalues (w : ι → ℕ) (t : K) (d : ℕ)
    (hres : 1 + t * ((∑ i, w i : ℕ) + d : K) = 0) :
    ((1 + t * (∑ i, w i : ℕ)) + t * (d : K) = 0) ∧
      ∀ j : ℕ, j ≠ d → (1 + t * (∑ i, w i : ℕ)) + t * (j : K) ≠ 0 := by
  have hd : (1 + t * (∑ i, w i : ℕ)) + t * (d : K) = 0 := by
    simpa only [Nat.cast_add, mul_add, add_assoc] using hres
  refine ⟨hd, ?_⟩
  have ht : t ≠ 0 := by intro ht; simp [ht] at hres
  intro j hj hjzero
  have hm : t * (j : K) = t * (d : K) :=
    add_left_cancel (hjzero.trans hd.symm)
  exact hj (Nat.cast_injective (mul_left_cancel₀ ht hm))

theorem potentialToQuotient_kernel_at_resonance
    (F : κ → P) (h : κ → ℕ) (w : ι → ℕ) (t : K) (d : ℕ)
    (hh : ∀ a, 0 < h a)
    (hF : ∀ a, (F a).IsWeightedHomogeneous w (h a))
    (hC : Function.Injective (VectorJacobian.normalizedJacobianMap F h))
    (hres : 1 + t * ((∑ i, w i : ℕ) + d : K) = 0) :
    LinearMap.ker (potentialToQuotient F h t) =
      LinearMap.ker (weightedHomogeneousComponent w d : P →ₗ[K] P) := by
  rw [show LinearMap.ker (potentialToQuotient F h t) =
      LinearMap.range (EulerReduction.eulerScalar JacobianDivergence.divergence
        (JacobianDivergence.eulerFieldMap w) t) from
      EulerInjective.potentialMap_kernel (VectorJacobian.normalizedJacobianMap F h)
        JacobianDivergence.divergence (JacobianDivergence.eulerFieldMap w) (potential F) t
        (coefficient_euler F h w hh hF) hC,
    scalar_euler]
  exact EulerResonance.range_scalarEuler_eq_projection_kernel w _ t d
    (resonance_eigenvalues w t d hres).1 (resonance_eigenvalues w t d hres).2

theorem potentialToQuotient_eq_component
    (F : κ → P) (h : κ → ℕ) (w : ι → ℕ) (t : K) (d : ℕ)
    (hh : ∀ a, 0 < h a)
    (hF : ∀ a, (F a).IsWeightedHomogeneous w (h a))
    (hC : Function.Injective (VectorJacobian.normalizedJacobianMap F h))
    (hres : 1 + t * ((∑ i, w i : ℕ) + d : K) = 0) (p : P) :
    potentialToQuotient F h t p =
      potentialToQuotient F h t (weightedHomogeneousComponent w d p) := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply LinearMap.mem_ker.mp
  rw [potentialToQuotient_kernel_at_resonance F h w t d hh hF hC hres,
    LinearMap.mem_ker, map_sub, EulerResonance.homogeneous_projection_idempotent,
    sub_self]

def homogeneousPotentialMap (F : κ → P) (h : κ → ℕ) (w : ι → ℕ) (t : K) (d : ℕ)
    (hh : ∀ a, 0 < h a)
    (hF : ∀ a, (F a).IsWeightedHomogeneous w (h a)) :
    weightedHomogeneousSubmodule K w d →ₗ[K] defectImage F h t :=
  ((potentialToQuotient F h t).domRestrict (weightedHomogeneousSubmodule K w d)).codRestrict
    (defectImage F h t) (fun p => by
      rw [← potentialToQuotient_range F h w t hh hF]
      exact ⟨p, rfl⟩)

theorem homogeneousPotentialMap_bijective
    (F : κ → P) (h : κ → ℕ) (w : ι → ℕ) (t : K) (d : ℕ)
    (hh : ∀ a, 0 < h a)
    (hF : ∀ a, (F a).IsWeightedHomogeneous w (h a))
    (hC : Function.Injective (VectorJacobian.normalizedJacobianMap F h))
    (hres : 1 + t * ((∑ i, w i : ℕ) + d : K) = 0) :
    Function.Bijective (homogeneousPotentialMap F h w t d hh hF) := by
  constructor
  · apply (LinearMap.ker_eq_bot).mp
    apply eq_bot_iff.mpr
    intro p hp
    have hz : potentialToQuotient F h t (p : P) = 0 :=
      congrArg Subtype.val (LinearMap.mem_ker.mp hp)
    have hzero : weightedHomogeneousComponent w d (p : P) = 0 := by
      apply LinearMap.mem_ker.mp
      rw [← potentialToQuotient_kernel_at_resonance F h w t d hh hF hC hres]
      exact hz
    apply Subtype.ext
    exact p.property.weightedHomogeneousComponent_same.symm.trans hzero
  · intro y
    have hy := (potentialToQuotient_range F h w t hh hF).ge y.property
    obtain ⟨p, hp⟩ := hy
    refine ⟨⟨weightedHomogeneousComponent w d p,
      weightedHomogeneousComponent_isWeightedHomogeneous d p⟩, ?_⟩
    apply Subtype.ext
    exact (potentialToQuotient_eq_component F h w t d hh hF hC hres p).symm.trans hp

/-- The canonical map `p ↦ [F p]`, an isomorphism onto the actual defect image. -/
def homogeneousDefectEquiv
    (F : κ → P) (h : κ → ℕ) (w : ι → ℕ) (t : K) (d : ℕ)
    (hh : ∀ a, 0 < h a)
    (hF : ∀ a, (F a).IsWeightedHomogeneous w (h a))
    (hC : Function.Injective (VectorJacobian.normalizedJacobianMap F h))
    (hres : 1 + t * ((∑ i, w i : ℕ) + d : K) = 0) :
    weightedHomogeneousSubmodule K w d ≃ₗ[K] defectImage F h t :=
  LinearEquiv.ofBijective (homogeneousPotentialMap F h w t d hh hF)
    (homogeneousPotentialMap_bijective F h w t d hh hF hC hres)

@[simp] theorem homogeneousDefectEquiv_apply
    (F : κ → P) (h : κ → ℕ) (w : ι → ℕ) (t : K) (d : ℕ)
    (hh : ∀ a, 0 < h a)
    (hF : ∀ a, (F a).IsWeightedHomogeneous w (h a))
    (hC : Function.Injective (VectorJacobian.normalizedJacobianMap F h))
    (hres : 1 + t * ((∑ i, w i : ℕ) + d : K) = 0)
    (p : weightedHomogeneousSubmodule K w d) :
    (homogeneousDefectEquiv F h w t d hh hF hC hres p : M ⧸ hit F h t) =
      (hit F h t).mkQ (potential F p) := rfl

end PaperVerification.VectorEuler
