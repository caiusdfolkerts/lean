import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Tactic

/-! # Attainment for a balanced finite exponential sum

The linear forms have zero sum and separate points.  Positive coefficients
then force every sublevel set to be bounded.  This is the analytic existence
step in the determinant proof of radial isotropic positioning.
-/

noncomputable section

namespace Bier.Forster

open Classical Finset

variable {E J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype J] [Nonempty J]

def exponentialSum (L : E →ₗ[ℝ] (J → ℝ)) (c : J → ℝ) (x : E) : ℝ :=
  ∑ j, c j * Real.exp (L x j)

theorem exponentialSum_continuous (L : E →ₗ[ℝ] (J → ℝ)) (c : J → ℝ) :
    Continuous (exponentialSum L c) := by
  unfold exponentialSum
  fun_prop

theorem exponentialSum_nonneg (L : E →ₗ[ℝ] (J → ℝ)) (c : J → ℝ)
    (hc : ∀ j, 0 ≤ c j) (x : E) : 0 ≤ exponentialSum L c x :=
  Finset.sum_nonneg fun j _ => mul_nonneg (hc j) (Real.exp_nonneg _)

theorem balanced_vector_bound (y : J → ℝ) (hy : ∑ j, y j = 0)
    (B : ℝ) (hB : 0 ≤ B) (hu : ∀ j, y j ≤ B) :
    ‖y‖ ≤ (Fintype.card J : ℝ) * B := by
  have hn : (1 : ℝ) ≤ Fintype.card J := by
    exact_mod_cast Fintype.card_pos (α := J)
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by positivity) hB)).mpr
  intro j
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have hs : ∑ i ∈ univ.erase j, y i ≤ (Fintype.card J : ℝ) * B := by
      calc
        ∑ i ∈ univ.erase j, y i ≤ ∑ _i ∈ univ.erase j, B :=
          Finset.sum_le_sum fun i _ => hu i
        _ = ((univ.erase j).card : ℝ) * B := by simp
        _ ≤ (Fintype.card J : ℝ) * B := by
          apply mul_le_mul_of_nonneg_right _ hB
          exact_mod_cast Finset.card_le_card (Finset.erase_subset j univ)
    have he := Finset.sum_erase_add (s := univ) (f := y) (mem_univ j)
    rw [hy] at he
    linarith
  · exact (hu j).trans (by nlinarith)

theorem exponentialSum_sublevel_bounded (L : E →ₗ[ℝ] (J → ℝ))
    (hL : Function.Injective L) (hz : ∀ x, ∑ j, L x j = 0)
    (c : J → ℝ) (hc : ∀ j, 0 < c j) :
    Bornology.IsBounded {x : E | exponentialSum L c x ≤ exponentialSum L c 0} := by
  let C := exponentialSum L c 0
  let B := 1 + ∑ j, C / c j
  have hC : 0 ≤ C := exponentialSum_nonneg L c (fun j => (hc j).le) 0
  have hB : 0 ≤ B := by
    dsimp [B]
    exact add_nonneg zero_le_one (Finset.sum_nonneg fun j _ => div_nonneg hC (hc j).le)
  have hu {x : E} (hx : exponentialSum L c x ≤ C) (j : J) : L x j ≤ B := by
    have ht : c j * Real.exp (L x j) ≤ C := by
      exact (Finset.single_le_sum
        (fun i _ => mul_nonneg (hc i).le (Real.exp_nonneg _)) (mem_univ j)).trans hx
    have he : Real.exp (L x j) ≤ C / c j := by
      apply (le_div_iff₀ (hc j)).mpr
      nlinarith
    have hb : C / c j ≤ ∑ i, C / c i :=
      Finset.single_le_sum (fun i _ => div_nonneg hC (hc i).le) (mem_univ j)
    have hexp := Real.add_one_le_exp (L x j)
    dsimp [B]
    linarith
  obtain ⟨K, _, hK⟩ := L.injective_iff_antilipschitz.mp hL
  apply (hK.isBounded_preimage
    (Metric.isBounded_closedBall (x := (0 : J → ℝ)) (r := (Fintype.card J : ℝ) * B))).subset
  intro x hx
  change dist (L x) 0 ≤ (Fintype.card J : ℝ) * B
  rw [dist_zero_right]
  exact balanced_vector_bound (L x) (hz x) B hB (hu hx)

theorem exists_exponentialSum_minimum (L : E →ₗ[ℝ] (J → ℝ))
    (hL : Function.Injective L) (hz : ∀ x, ∑ j, L x j = 0)
    (c : J → ℝ) (hc : ∀ j, 0 < c j) :
    ∃ x : E, ∀ y : E, exponentialSum L c x ≤ exponentialSum L c y := by
  exact (exponentialSum_continuous L c).exists_forall_le_of_isBounded 0
    (exponentialSum_sublevel_bounded L hL hz c hc)

/-- At the minimum, every directional derivative vanishes. -/
theorem exponentialSum_minimum_stationary (L : E →ₗ[ℝ] (J → ℝ))
    (c : J → ℝ) (x : E)
    (hx : ∀ y : E, exponentialSum L c x ≤ exponentialSum L c y) (v : E) :
    ∑ j, c j * Real.exp (L x j) * L v j = 0 := by
  let f : ℝ → ℝ := fun t => exponentialSum L c (x + t • v)
  have hmin : IsLocalMin f 0 := by
    apply IsMinOn.isLocalMin (s := Set.univ)
    · intro t _
      simpa [f] using hx (x + t • v)
    · exact Filter.univ_mem
  have hd : HasDerivAt f (∑ j, c j * Real.exp (L x j) * L v j) 0 := by
    have hterm (j : J) :
        HasDerivAt (fun t : ℝ => c j * Real.exp (L x j + t * L v j))
          (c j * Real.exp (L x j) * L v j) 0 := by
      convert (((hasDerivAt_id (0 : ℝ)).mul_const (L v j)).const_add
        (L x j)).exp.const_mul (c j) using 1 <;> simp <;> ring
    convert HasDerivAt.sum (u := univ) (fun j _ => hterm j) using 1
    ext t
    simp [f, exponentialSum, map_add, map_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Finset.sum_apply]
  exact hmin.hasDerivAt_eq_zero hd

end Bier.Forster
