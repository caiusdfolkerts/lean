module

public import PaperVerification.PowerOperators
public import PaperVerification.Eigencomponents
public import PaperVerification.JacobianDivergence
public import PaperVerification.JacobianTorsion

/-!
# Grading and torsion for the actual divergence quotient

Euler invariance is proved directly from the product rule and commuting partial
derivatives. Distinct-eigenvalue projection then gives all homogeneous pieces,
without assuming that the divergence subspace is an ideal.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open MvPolynomial
open scoped BigOperators

namespace PaperVerification.JacobianDivergence

variable {K ι : Type*} [Field K] [Fintype ι]
local notation "P" => MvPolynomial ι K

/-- Weighted Euler differentiation, as a genuine linear endomorphism. -/
def weightedEuler (w : ι → ℕ) : P →ₗ[K] P :=
  ∑ i, w i • PowerOperators.euler i

@[simp] theorem weightedEuler_apply (w : ι → ℕ) (f : P) :
    weightedEuler w f = ∑ i, w i • (X i * pderiv i f) := by
  simp only [weightedEuler, LinearMap.sum_apply, LinearMap.smul_apply,
    PowerOperators.euler_apply]

theorem weightedEuler_homogeneous (w : ι → ℕ) (f : P) (d : ℕ)
    (hf : f.IsWeightedHomogeneous w d) : weightedEuler w f = (d : K) • f := by
  simpa only [weightedEuler_apply, Nat.cast_smul_eq_nsmul] using hf.sum_weight_X_mul_pderiv

theorem weightedEuler_mul (w : ι → ℕ) (f g : P) :
    weightedEuler w (f * g) = weightedEuler w f * g + f * weightedEuler w g := by
  have hterm (i : ι) : w i • (X i * pderiv i (f * g)) =
      (w i • (X i * pderiv i f)) * g + f * (w i • (X i * pderiv i g)) := by
    rw [pderiv_mul]
    simp only [nsmul_eq_mul]
    ring
  simp only [weightedEuler_apply, hterm, Finset.sum_add_distrib,
    Finset.sum_mul, Finset.mul_sum]

theorem pderiv_weightedEuler (w : ι → ℕ) (f : P) (j : ι) :
    pderiv j (weightedEuler w f) = w j • pderiv j f + weightedEuler w (pderiv j f) := by
  classical
  have hterm (i : ι) : pderiv j (w i • (X i * pderiv i f)) =
      (if i = j then w j • pderiv j f else 0) + w i • (X i * pderiv i (pderiv j f)) := by
    by_cases hij : i = j
    · subst i
      simp only [map_nsmul, pderiv_mul, pderiv_X_self, one_mul,
        ite_true, smul_add]
    · simp only [map_nsmul, pderiv_mul, pderiv_X_of_ne hij, zero_mul, zero_add,
        ite_eq_right hij]
      rw [pderiv_comm j i f]
  rw [weightedEuler_apply, map_sum]
  simp only [hterm, Finset.sum_add_distrib]
  simp [weightedEuler_apply]

/-- The Euler action on a gradient component, allowing `h < w i` and zero partials. -/
theorem weightedEuler_gradient (F : P) (w : ι → ℕ) (h : ℕ)
    (hF : F.IsWeightedHomogeneous w h) (i : ι) :
    weightedEuler w (pderiv i F) = h • pderiv i F - w i • pderiv i F := by
  have hder := congrArg (pderiv i) hF.sum_weight_X_mul_pderiv
  rw [← weightedEuler_apply] at hder
  rw [pderiv_weightedEuler, map_nsmul] at hder
  exact eq_sub_of_add_eq (by simpa only [add_comm] using hder)

/-- The degree-zero Euler action on polynomial vector fields. -/
def eulerShift (w : ι → ℕ) (g : ι → P) : ι → P :=
  fun i => weightedEuler w (g i) - w i • g i

theorem coefficient_eulerShift (F : P) (w : ι → ℕ) (h : ℕ)
    (hF : F.IsWeightedHomogeneous w h) (g : ι → P) :
    KoszulSyzygies.coefficient (gradient F) (eulerShift w g) =
      weightedEuler w (KoszulSyzygies.coefficient (gradient F) g) -
        h • KoszulSyzygies.coefficient (gradient F) g := by
  have hterm (i : ι) : (weightedEuler w (g i) - w i • g i) * pderiv i F =
      weightedEuler w (g i * pderiv i F) - h • (g i * pderiv i F) := by
    rw [weightedEuler_mul, weightedEuler_gradient F w h hF]
    simp only [nsmul_eq_mul]
    ring
  simp only [KoszulSyzygies.coefficient_apply, gradient, eulerShift, hterm,
    Finset.sum_sub_distrib, map_sum, Finset.smul_sum]

theorem divergence_eulerShift (w : ι → ℕ) (g : ι → P) :
    divergence (eulerShift w g) = weightedEuler w (divergence g) := by
  simp only [divergence_apply, eulerShift, map_sub, pderiv_weightedEuler,
    map_nsmul, add_sub_cancel_left, map_sum]

/-- Tangency and divergence are compatible with the actual weighted Euler action. -/
theorem weightedEuler_mem_divergenceSpace (F : P) (w : ι → ℕ) (h : ℕ)
    (hF : F.IsWeightedHomogeneous w h) (u : P) (hu : u ∈ divergenceSpace F) :
    weightedEuler w u ∈ divergenceSpace F := by
  obtain ⟨g, hg, rfl⟩ := hu
  refine ⟨eulerShift w g, ?_, divergence_eulerShift w g⟩
  have hz : KoszulSyzygies.coefficient (gradient F) g = 0 := hg
  change KoszulSyzygies.coefficient (gradient F) (eulerShift w g) = 0
  rw [coefficient_eulerShift F w h hF, hz, map_zero, smul_zero, sub_self]

/-- Any subspace stable under weighted Euler contains every homogeneous component.
No ideal or finite-dimensionality assumption is made. -/
theorem homogeneousComponent_mem_of_eulerStable [CharZero K]
    (w : ι → ℕ) (U : Submodule K P)
    (hU : ∀ u ∈ U, weightedEuler w u ∈ U) (f : P) (hf : f ∈ U) (d : ℕ) :
    weightedHomogeneousComponent w d f ∈ U := by
  classical
  let v : ℕ → P := fun j => weightedHomogeneousComponent w j f
  have hvfin := weightedHomogeneousComponent_finsupp (w := w) f
  let s : Finset ℕ := hvfin.toFinset
  have hsum : ∑ j ∈ s, v j = f := by
    rw [← sum_weightedHomogeneousComponent w f, finsum_eq_sum _ hvfin]
  have he (j : ℕ) : weightedEuler w (v j) = (j : K) • v j :=
    weightedEuler_homogeneous w _ j (weightedHomogeneousComponent_isWeightedHomogeneous j f)
  by_cases hd : d ∈ s
  · exact Eigencomponents.mem_of_sum_mem (weightedEuler w) U hU
      (fun j : ℕ => (j : K)) Nat.cast_injective s v (fun j _ => he j)
      (hsum.symm ▸ hf) d hd
  · have hz : v d = 0 := by
      apply Function.notMem_support.mp
      intro hmem
      apply hd
      exact hvfin.mem_toFinset.mpr hmem
    change v d ∈ U
    rw [hz]
    exact U.zero_mem

theorem homogeneousComponent_mem_divergenceSpace [CharZero K]
    (F : P) (w : ι → ℕ) (h : ℕ) (hF : F.IsWeightedHomogeneous w h)
    (u : P) (hu : u ∈ divergenceSpace F) (d : ℕ) :
    weightedHomogeneousComponent w d u ∈ divergenceSpace F :=
  homogeneousComponent_mem_of_eulerStable w (divergenceSpace F)
    (weightedEuler_mem_divergenceSpace F w h hF) u hu d

/-- Multiplication by the potential is injective on the whole divergence quotient,
not just on its homogeneous classes. -/
theorem potential_torsion_free [CharZero K] {n : ℕ} [Nonempty (Fin n)]
    (F u : MvPolynomial (Fin n) K) (w : Fin n → ℕ) (h : ℕ)
    (hw : ∀ i, 0 < w i) (hh : 0 < h) (hF : F.IsWeightedHomogeneous w h)
    (hreg : RingTheory.Sequence.IsWeaklyRegular (MvPolynomial (Fin n) K)
      (List.ofFn (gradient F)))
    (hFu : F * u ∈ divergenceSpace F) : u ∈ divergenceSpace F := by
  classical
  let v : ℕ → MvPolynomial (Fin n) K := fun d => weightedHomogeneousComponent w d u
  have hvfin := weightedHomogeneousComponent_finsupp (w := w) u
  let s : Finset ℕ := hvfin.toFinset
  have hsum : ∑ d ∈ s, v d = u := by
    rw [← sum_weightedHomogeneousComponent w u, finsum_eq_sum _ hvfin]
  have hprod : ∑ d ∈ s, F * v d ∈ divergenceSpace F := by
    rw [← Finset.mul_sum, hsum]
    exact hFu
  have hμ : Function.Injective (fun d : ℕ => ((h + d : ℕ) : K)) := by
    intro a b hab
    exact Nat.add_left_cancel (Nat.cast_injective hab)
  have he (d : ℕ) : weightedEuler w (F * v d) = ((h + d : ℕ) : K) • (F * v d) :=
    weightedEuler_homogeneous w _ _
      (hF.mul (weightedHomogeneousComponent_isWeightedHomogeneous d u))
  have hparts := Eigencomponents.mem_of_sum_mem (weightedEuler w) (divergenceSpace F)
    (weightedEuler_mem_divergenceSpace F w h hF) _ hμ s (fun d => F * v d)
    (fun d _ => he d) hprod
  rw [← hsum]
  apply (divergenceSpace F).sum_mem
  intro d hd
  exact homogeneous_potential_torsion_free F (v d) w h d hw hh hF
    (weightedHomogeneousComponent_isWeightedHomogeneous d u) hreg (hparts d hd)

end PaperVerification.JacobianDivergence
