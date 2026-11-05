module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

/-!
# Removing probability normalization from first variations

The quantile argument compares conditional probability measures. The radial
first-variation argument compares unnormalised volume integrals. This lemma
connects them when the actual masses have the same first derivative.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Set

namespace RankThreeProjection.Rigidity

set_option backward.isDefEq.respectTransparency false in
/-- If two masses and two numerators agree at the base point, the masses
have equal first derivatives, and the normalized difference has zero first
derivative, then the unnormalised difference has zero first derivative.
Existence of the individual derivatives is explicit; in the application it
comes from the localized radial first-variation theorem. -/
theorem raw_difference_derivative_zero_of_normalized
    (V W F G : ℝ → ℝ) (v f g x : ℝ) (s : Set ℝ)
    (hs : UniqueDiffWithinAt ℝ s x)
    (hV : HasDerivWithinAt V v s x)
    (hW : HasDerivWithinAt W v s x)
    (hF : HasDerivWithinAt F f s x)
    (hG : HasDerivWithinAt G g s x)
    (hVW : V x = W x) (hFG : F x = G x) (hV0 : V x ≠ 0)
    (hzero : HasDerivWithinAt (fun t => F t / V t - G t / W t) 0 s x) :
    HasDerivWithinAt (fun t => F t - G t) 0 s x := by
  have hW0 : W x ≠ 0 := by rwa [← hVW]
  have hquot := (hF.fun_div hV hV0).fun_sub (hG.fun_div hW hW0)
  have he := hs.eq_deriv s hquot hzero
  rw [← hVW, ← hFG] at he
  field_simp [hV0] at he
  have hprod : (f - g) * V x = 0 := by nlinarith [he]
  have hfg : f = g := sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hV0)
  simpa only [hfg, sub_self] using hF.fun_sub hG

end RankThreeProjection.Rigidity
