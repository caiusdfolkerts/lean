module

public import PaperVerification.JacobianDivergence
public import PaperVerification.EulerParameters

/-!
# Homogeneous torsion reduction for the Brieskorn divergence quotient

The relation `F u ∈ div(ker dF)` is converted to `u ∈ div(ker dF)` by
an actual tangent polynomial vector field. This is the essential injectivity
step; it does not assume freeness of the Brieskorn module.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open MvPolynomial
open scoped BigOperators

namespace PaperVerification.JacobianDivergence

variable {K : Type*} [Field K] [CharZero K]

/-- A homogeneous class in the divergence quotient has no `F`-torsion.
The hypotheses are exactly positive weights/degree and a regular gradient. -/
theorem homogeneous_potential_torsion_free {n : ℕ} [Nonempty (Fin n)]
    (F u : MvPolynomial (Fin n) K) (w : Fin n → ℕ) (h d : ℕ)
    (hw : ∀ i, 0 < w i) (hh : 0 < h)
    (hF : F.IsWeightedHomogeneous w h) (hu : u.IsWeightedHomogeneous w d)
    (hreg : RingTheory.Sequence.IsWeaklyRegular (MvPolynomial (Fin n) K)
      (List.ofFn (gradient F)))
    (hFu : F * u ∈ divergenceSpace F) : u ∈ divergenceSpace F := by
  obtain ⟨g, hg, hdiv⟩ := hFu
  have hker : g ∈ LinearMap.ker (KoszulSyzygies.coefficient (gradient F)) := hg
  rw [KoszulSyzygies.kernel_eq_boundary_range (gradient F) hreg] at hker
  obtain ⟨A, rfl⟩ := hker
  rw [divergence_boundary] at hdiv
  let C : (Fin n → MvPolynomial (Fin n) K) →ₗ[K] MvPolynomial (Fin n) K :=
    (KoszulSyzygies.coefficient (gradient F)).restrictScalars K
  let Y : Fin n → MvPolynomial (Fin n) K :=
    curl A - (h : K)⁻¹ • eulerField w u
  have hhK : (h : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hh)
  have hC : C (eulerField w u) = (h : K) • (F * u) := by
    simpa only [C, LinearMap.restrictScalars_apply, Nat.cast_smul_eq_nsmul]
      using coefficient_eulerField F w h hF u
  have hCY : C Y = 0 := by
    change C (curl A - (h : K)⁻¹ • eulerField w u) = 0
    rw [map_sub, map_smul, hC, smul_smul, inv_mul_cancel₀ hhK, one_smul]
    exact sub_eq_zero.mpr hdiv
  have hDY : divergence Y =
      (-((h : K)⁻¹ * ((∑ i, w i) + d : K))) • u := by
    change divergence (curl A - (h : K)⁻¹ • eulerField w u) = _
    rw [map_sub, map_smul, divergence_curl,
      divergence_eulerField_homogeneous w u d hu]
    simp only [zero_sub, ← Nat.cast_smul_eq_nsmul K, smul_smul, neg_smul, Nat.cast_add]
  have hYmem : divergence Y ∈ divergenceSpace F :=
    ⟨Y, hCY, rfl⟩
  rw [hDY] at hYmem
  have hWd : (∑ i, w i) + d ≠ 0 := Nat.ne_of_gt
    (Nat.add_pos_left (EulerJacobian.weight_sum_pos w hw) d)
  have hScalar : -((h : K)⁻¹ * ((∑ i, w i) + d : K)) ≠ 0 :=
    neg_ne_zero.mpr (mul_ne_zero (inv_ne_zero hhK) (by simpa only [Nat.cast_add] using (Nat.cast_ne_zero.mpr hWd : (((∑ i, w i) + d : ℕ) : K) ≠ 0)))
  have hscaled := (divergenceSpace F).smul_mem
    (-((h : K)⁻¹ * ((∑ i, w i) + d : K)))⁻¹ hYmem
  simpa only [smul_smul, inv_mul_cancel₀ hScalar, one_smul] using hscaled

end PaperVerification.JacobianDivergence
