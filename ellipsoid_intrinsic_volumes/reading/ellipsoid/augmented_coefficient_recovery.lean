module

public import Ellipsoid.CompactInverse
public import Ellipsoid.PrincipalReconstruction
public import tau_ceti.topology.algebra.polynomial.basic

@[expose] public section

noncomputable section

open Set Filter Matrix Polynomial
open scoped Topology BigOperators

namespace EllipsoidVerification

/-- The last coefficient is retained as an output, so this map controls
perturbations of the volume as well as of all internal intrinsic volumes. -/
def augmentedCoefficientMap (m : ℕ) (z : (Fin m → ℝ) × ℝ) : (Fin m → ℝ) × ℝ :=
  (coefficientMap m 1 z.2 z.1, z.2)

def augmentedCoefficientDomain (m : ℕ) : Set ((Fin m → ℝ) × ℝ) :=
  {z | 0 ≤ z.1 ∧ 0 < z.2}

theorem contDiff_variableEndpoints (m : ℕ) (N : WithTop ℕ∞) :
    ContDiff ℝ N (fun z : (Fin m → ℝ) × ℝ => fixedEndpoints m 1 z.2 z.1) := by
  apply contDiff_pi.mpr
  intro j
  unfold fixedEndpoints
  split_ifs <;> fun_prop

theorem contDiffAt_augmentedCoefficientMap {m : ℕ} {z : (Fin m → ℝ) × ℝ}
    (hz : z ∈ augmentedCoefficientDomain m) :
    ContDiffAt ℝ 1 (augmentedCoefficientMap m) z := by
  have he := fixedEndpoints_admissible (by norm_num : (0 : ℝ) < 1) hz.2 hz.1
  have hU := (isOpen_positiveCoefficientDomain (m + 1)).mem_nhds
    (admissible_mem_positiveCoefficientDomain he)
  apply ContDiffAt.prodMk
  · apply contDiffAt_pi.mpr
    intro k
    have hk : ContDiffAt ℝ 1
        (fun e : Coefficients (m + 1) => coefficientTransform e (k.val + 1))
        (fixedEndpoints m 1 z.2 z.1) :=
      ((contDiffOn_coefficientTransform (n := m + 1) (k := k.val + 1)
        (by omega) (by omega)).contDiffAt hU).of_le (by simp)
    exact ContDiffAt.comp
      (f := fun w : (Fin m → ℝ) × ℝ => fixedEndpoints m 1 w.2 w.1)
      (g := fun e : Coefficients (m + 1) => coefficientTransform e (k.val + 1))
      z hk (contDiff_variableEndpoints m 1).contDiffAt
  · exact contDiff_snd.contDiffAt

theorem augmentedCoefficientMap_injOn {m : ℕ} :
    Set.InjOn (augmentedCoefficientMap m) (augmentedCoefficientDomain m) := by
  intro x hx y hy hxy
  have hlast := congrArg (fun w : (Fin m → ℝ) × ℝ => w.2) hxy
  change x.2 = y.2 at hlast
  have hfirst : coefficientMap m 1 x.2 x.1 = coefficientMap m 1 x.2 y.1 := by
    simpa only [augmentedCoefficientMap, hlast] using congrArg Prod.fst hxy
  have hcoords := coefficientMap_injOn_nonnegative (by norm_num : (0 : ℝ) < 1)
    hx.2 hx.1 hy.1 hfirst
  exact Prod.ext hcoords hlast

theorem augmentedCoefficientMap_fderiv_injective {m : ℕ} {z : (Fin m → ℝ) × ℝ}
    (hz : z ∈ augmentedCoefficientDomain m) :
    Function.Injective (fderiv ℝ (augmentedCoefficientMap m) z) := by
  let L := fderiv ℝ (augmentedCoefficientMap m) z
  have hL : HasFDerivAt (augmentedCoefficientMap m) L z :=
    (contDiffAt_augmentedCoefficientMap hz).differentiableAt one_ne_zero |>.hasFDerivAt
  have hsnd : (ContinuousLinearMap.snd ℝ (Fin m → ℝ) ℝ).comp L =
      ContinuousLinearMap.snd ℝ (Fin m → ℝ) ℝ :=
    hL.snd.unique hasFDerivAt_snd
  have hfirst : L.comp (ContinuousLinearMap.inl ℝ (Fin m → ℝ) ℝ) =
      (matrixDerivative (fixedCoefficientJacobian m 1 z.2 z.1)).prod 0 := by
    have ha : HasFDerivAt
        (fun v : Fin m → ℝ => augmentedCoefficientMap m (v, z.2))
        (L.comp (ContinuousLinearMap.inl ℝ (Fin m → ℝ) ℝ)) z.1 := by
      simpa only [Function.comp_def] using
        (HasFDerivAt.comp (𝕜 := ℝ)
          (f := fun v : Fin m → ℝ => (v, z.2))
          (g := augmentedCoefficientMap m) (g' := L)
          z.1 hL (hasFDerivAt_prodMk_left (𝕜 := ℝ) z.1 z.2))
    have hb := (hasFDerivAt_coefficientMap (by norm_num : (0 : ℝ) < 1) hz.2 hz.1).prodMk
      (hasFDerivAt_const z.2 z.1)
    exact ha.unique hb
  apply (injective_iff_map_eq_zero L).mpr
  intro w hw
  have hw2 : w.2 = 0 := by
    have h := congrArg (fun A : ((Fin m → ℝ) × ℝ) →L[ℝ] ℝ => A w) hsnd
    change (L w).2 = w.2 at h
    rw [hw] at h
    exact h.symm
  have hw1 : w.1 = 0 := by
    by_contra hne
    obtain ⟨i, hi⟩ := (fixedCoefficientJacobian_diagonallyStable
      (by norm_num : (0 : ℝ) < 1) hz.2 hz.1).exists_positive_coordinate hne
    have hh := congrArg (fun A : (Fin m → ℝ) →L[ℝ] ((Fin m → ℝ) × ℝ) => A w.1) hfirst
    have hw' : (w.1, (0 : ℝ)) = w := Prod.ext rfl hw2.symm
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, hw', hw,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.zero_apply] at hh
    have hzero := congrArg (fun y : (Fin m → ℝ) × ℝ => y.1 i) hh
    change (0 : ℝ) = (fixedCoefficientJacobian m 1 z.2 z.1 *ᵥ w.1) i at hzero
    rw [← hzero, mul_zero] at hi
    exact (lt_irrefl 0) hi
  exact Prod.ext hw1 hw2

/-- This is a uniform estimate for the literal improper-integral map,
including variations of the leading coefficient. -/
theorem augmentedCoefficientMap_inverse_lipschitz {m : ℕ}
    {K : Set ((Fin m → ℝ) × ℝ)} (hK : IsCompact K)
    (hKD : K ⊆ augmentedCoefficientDomain m) :
    ∃ L : ℝ, 0 < L ∧ ∀ x ∈ K, ∀ y ∈ K,
      ‖x - y‖ ≤ L * ‖augmentedCoefficientMap m x - augmentedCoefficientMap m y‖ :=
  compact_inverse_lipschitz_of_contDiff hK
    (fun x hx => contDiffAt_augmentedCoefficientMap (hKD hx))
    (augmentedCoefficientMap_injOn.mono hKD)
    (fun x hx => augmentedCoefficientMap_fderiv_injective (hKD hx))

@[fun_prop] theorem continuous_axisCoefficients (n : ℕ) :
    Continuous (axisCoefficients (n := n)) := by
  apply continuous_pi
  intro j
  apply continuous_iff_continuousAt.mpr
  intro a
  apply Polynomial.continuousAt_coeff_prod
  intro i hi k hk
  simp only [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_C_mul_X]
  split_ifs <;>
    first
    | exact continuousAt_const
    | exact continuousAt_const.add ((continuous_apply i).continuousAt.pow 2)

def axisCoefficientData {m : ℕ} (a : Fin (m + 1) → ℝ) : (Fin m → ℝ) × ℝ :=
  (internalCoefficients m (axisCoefficients a), axisCoefficients a (Fin.last (m + 1)))

@[fun_prop] theorem continuous_axisCoefficientData (m : ℕ) :
    Continuous (axisCoefficientData (m := m)) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro i
    exact (continuous_apply _).comp (continuous_axisCoefficients (m + 1))
  · change Continuous (fun a : Fin (m + 1) → ℝ =>
      axisCoefficients a (Fin.last (m + 1)))
    exact (continuous_apply (Fin.last (m + 1))).comp
      (continuous_axisCoefficients (m + 1))

theorem axisCoefficientData_mem {m : ℕ} {a : Fin (m + 1) → ℝ}
    (ha : ∀ i, 0 < a i) : axisCoefficientData a ∈ augmentedCoefficientDomain m := by
  have h := axisCoefficients_admissible a ha
  exact ⟨fun i => h.1 _, h.2.2⟩

theorem axisCoefficientData_inverse_lipschitz (m : ℕ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    ∃ L : ℝ, 0 < L ∧ ∀ x y : Fin (m + 1) → ℝ,
      x ∈ Icc (fun _ => a) (fun _ => b) → y ∈ Icc (fun _ => a) (fun _ => b) →
      ‖axisCoefficientData x - axisCoefficientData y‖ ≤
        L * ‖augmentedCoefficientMap m (axisCoefficientData x) -
          augmentedCoefficientMap m (axisCoefficientData y)‖ := by
  obtain ⟨L, hL, hbound⟩ := augmentedCoefficientMap_inverse_lipschitz
    (isCompact_Icc.image (continuous_axisCoefficientData m)) (by
      rintro _ ⟨x, hx, rfl⟩
      exact axisCoefficientData_mem fun i => ha.trans_le (hx.1 i))
  exact ⟨L, hL, fun x y hx hy => hbound _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩⟩

end EllipsoidVerification
