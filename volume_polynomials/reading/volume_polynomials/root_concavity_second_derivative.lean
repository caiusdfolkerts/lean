module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

@[expose] public section
set_option autoImplicit false
noncomputable section

/-!
# The differential consequence of root concavity

This is the scalar calculus step needed to obtain the diagonal mixed-volume
form's reference inequality directly from Brunn--Minkowski. All derivatives
in the hypotheses are actual derivatives of the indicated real functions.
-/

open Set

namespace VolumePolynomials

/-- The logarithmic second-derivative bound implied by positive-power
concavity. The domain is an actual open neighborhood, so no one-sided or
boundary derivative is substituted for the derivative at the reference. -/
theorem root_concave_second_derivative
    {f f' : ℝ → ℝ} {ε q B : ℝ} (hε : 0 < ε) (hq : 0 < q)
    (hpos : ∀ x ∈ Ioo (-ε) ε, 0 < f x)
    (hf : ∀ x ∈ Ioo (-ε) ε, HasDerivAt f (f' x) x)
    (hf' : HasDerivAt f' B 0)
    (hc : ConcaveOn ℝ (Ioo (-ε) ε) (fun x => f x ^ q)) :
    f 0 * B ≤ (1 - q) * (f' 0) ^ 2 := by
  first
  | have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
    have hf0 : 0 < f 0 := hpos 0 h0
    let g' : ℝ → ℝ := fun x => q * f x ^ (q - 1) * f' x
    have hderiv (x : ℝ) (hx : x ∈ Ioo (-ε) ε) :
        deriv (fun y => f y ^ q) x = g' x := by
      first
      | rw [((hf x hx).rpow_const (p := q) (Or.inl (hpos x hx).ne')).deriv]
        dsimp only [g']
        ring
    have hanti : AntitoneOn g' (Ioo (-ε) ε) := by
      first
      | have ha := hc.antitoneOn_deriv
          (fun x hx => ((hf x hx).rpow_const (p := q) (Or.inl (hpos x hx).ne')).differentiableAt)
        intro x hx y hy hxy
        rw [← hderiv x hx, ← hderiv y hy]
        exact ha hx hy hxy
    have hp : HasDerivAt (fun x => f x ^ (q - 1))
        (f' 0 * (q - 1) * f 0 ^ (q - 2)) 0 := by
      first
      | simpa only [show q - 1 - 1 = q - 2 by ring] using
          (hf 0 h0).rpow_const (p := q - 1) (Or.inl hf0.ne')
    have hgp : HasDerivAt g'
        (q * (q - 1) * f 0 ^ (q - 2) * (f' 0) ^ 2 +
          q * f 0 ^ (q - 1) * B) 0 := by
      first
      | convert (hp.const_mul q).mul hf' using 1
        ring
    have hn := hanti.derivWithin_nonpos (x := 0)
    rw [hgp.hasDerivWithinAt.derivWithin (isOpen_Ioo.uniqueDiffWithinAt h0)] at hn
    have hexp : f 0 ^ (q - 1) = f 0 ^ (q - 2) * f 0 := by
      first
      | calc
          f 0 ^ (q - 1) = f 0 ^ ((q - 2) + 1) := by congr 1; ring
          _ = f 0 ^ (q - 2) * f 0 ^ (1 : ℝ) := Real.rpow_add hf0 _ _
          _ = f 0 ^ (q - 2) * f 0 := by rw [Real.rpow_one]
    rw [hexp] at hn
    have hfactor : 0 < q * f 0 ^ (q - 2) := mul_pos hq (Real.rpow_pos_of_pos hf0 _)
    have hform : q * (q - 1) * f 0 ^ (q - 2) * (f' 0) ^ 2 +
          q * (f 0 ^ (q - 2) * f 0) * B =
        (q * f 0 ^ (q - 2)) * ((q - 1) * (f' 0) ^ 2 + f 0 * B) := by ring
    rw [hform] at hn
    have hinner := nonpos_of_mul_nonpos_right hn hfactor
    linarith

/-- The normalization of first and second volume derivatives gives the
reference reverse Cauchy--Schwarz inequality in every dimension at least
two. The geometric application supplies `f` from actual volume. -/
theorem root_concavity_reference_inequality
    {d : ℕ} (hd : 2 ≤ d) {f f' : ℝ → ℝ} {ε a b c : ℝ} (hε : 0 < ε)
    (hpos : ∀ x ∈ Ioo (-ε) ε, 0 < f x)
    (hf : ∀ x ∈ Ioo (-ε) ε, HasDerivAt f (f' x) x)
    (hf' : HasDerivAt f' ((d : ℝ) * ((d : ℝ) - 1) * b) 0)
    (hc : ConcaveOn ℝ (Ioo (-ε) ε) (fun x => f x ^ ((d : ℝ)⁻¹)))
    (hvalue : f 0 = c) (hfirst : f' 0 = (d : ℝ) * a) : c * b ≤ a ^ 2 := by
  first
  | have hdpos : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
    have hd1 : 0 < (d : ℝ) - 1 := by
      first
      | have htwo : (2 : ℝ) ≤ d := by exact_mod_cast hd
        linarith
    have h := root_concave_second_derivative hε (inv_pos.mpr hdpos) hpos hf hf' hc
    rw [hvalue, hfirst] at h
    have hleft : c * ((d : ℝ) * ((d : ℝ) - 1) * b) =
        ((d : ℝ) * ((d : ℝ) - 1)) * (c * b) := by ring
    have hright : (1 - (d : ℝ)⁻¹) * ((d : ℝ) * a) ^ 2 =
        ((d : ℝ) * ((d : ℝ) - 1)) * a ^ 2 := by
      first
      | field_simp [ne_of_gt hdpos] <;> ring
    rw [hleft, hright] at h
    exact Iff.mp (mul_le_mul_iff_of_pos_left (mul_pos hdpos hd1)) h

end VolumePolynomials
