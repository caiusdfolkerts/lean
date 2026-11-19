module

public import VolumePolynomials.BivariateCoordinates
public import VolumePolynomials.LogObstruction
public import Mathlib.Order.Filter.Germ.Basic
public import Mathlib.RingTheory.Algebraic.Integral

@[expose] public section

/-!
# Algebraic closure of eventual polynomial relations

The coefficients are polynomials in an actual real-valued base function.
Germs are used only to transport Mathlib's proved closure of algebraic elements
under addition and multiplication. Every conclusion is then converted back to
an explicit nonzero real bivariate polynomial and an eventual evaluation identity.

This gives the elimination step in the logarithmic boundary argument without
assuming quantifier elimination, a Puiseux expansion, or a resultant identity.
-/

open Filter Polynomial Asymptotics
open scoped Topology Polynomial.Bivariate

namespace VolumePolynomials

/-- An actual nonzero bivariate real polynomial vanishes eventually. -/
def HasPolynomialRelation {α : Type*} (l : Filter α) (s g : α → ℝ) : Prop :=
  ∃ p : ℝ[X][Y], p ≠ 0 ∧ ∀ᶠ x in l, p.evalEval (s x) (g x) = 0

/-- Evaluation of a univariate polynomial in the base function, modulo eventual equality. -/
noncomputable def germPolynomialEvaluation {α : Type*} (l : Filter α) (s : α → ℝ) :
    ℝ[X] →+* Germ l ℝ :=
  (Germ.coeRingHom l).comp (RingHom.pi fun x => Polynomial.evalRingHom (s x))

theorem germPolynomialEvaluation_apply {α : Type*} (l : Filter α) (s : α → ℝ)
    (p : ℝ[X]) :
    germPolynomialEvaluation l s p = Germ.ofFun (fun x => p.eval (s x)) := rfl

theorem aeval_germ {α : Type*} (l : Filter α) (s g : α → ℝ) (p : ℝ[X][Y]) :
    let : Algebra ℝ[X] (Germ l ℝ) := (germPolynomialEvaluation l s).toAlgebra
    Polynomial.aeval (Germ.ofFun g : Germ l ℝ) p =
      Germ.ofFun (fun x => p.evalEval (s x) (g x)) := by
  let : Algebra ℝ[X] (Germ l ℝ) := (germPolynomialEvaluation l s).toAlgebra
  change Polynomial.aeval (Germ.ofFun g : Germ l ℝ) p =
    Germ.ofFun (fun x => p.evalEval (s x) (g x))
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add, hp, hq]
      change Germ.ofFun (fun x => p.evalEval (s x) (g x) + q.evalEval (s x) (g x)) = _
      congr 1
      funext x
      simp only [evalEval_add]
  | monomial n a =>
      rw [Polynomial.aeval_monomial]
      change Germ.ofFun (fun x => a.eval (s x) * g x ^ n) =
        Germ.ofFun (fun x => (monomial n a).evalEval (s x) (g x))
      congr 1
      funext x
      simp only [evalEval, eval_monomial, eval_mul, eval_pow, eval_C]

theorem hasPolynomialRelation_iff_isAlgebraic {α : Type*} (l : Filter α)
    (s g : α → ℝ) :
    let : Algebra ℝ[X] (Germ l ℝ) := (germPolynomialEvaluation l s).toAlgebra
    HasPolynomialRelation l s g ↔ IsAlgebraic ℝ[X] (Germ.ofFun g : Germ l ℝ) := by
  let : Algebra ℝ[X] (Germ l ℝ) := (germPolynomialEvaluation l s).toAlgebra
  constructor
  · rintro ⟨p, hp, hrel⟩
    refine ⟨p, hp, ?_⟩
    rw [aeval_germ]
    exact Germ.coe_eq.mpr hrel
  · rintro ⟨p, hp, hrel⟩
    refine ⟨p, hp, ?_⟩
    rw [aeval_germ] at hrel
    exact Germ.coe_eq.mp hrel

namespace HasPolynomialRelation

variable {α : Type*} {l : Filter α} {s f g : α → ℝ}

theorem congr (hf : HasPolynomialRelation l s f) (hfg : f =ᶠ[l] g) :
    HasPolynomialRelation l s g := by
  obtain ⟨p, hp, hrel⟩ := hf
  refine ⟨p, hp, ?_⟩
  filter_upwards [hrel, hfg] with x hx hfgx
  simpa only [← hfgx] using hx

theorem sub (hf : HasPolynomialRelation l s f) (hg : HasPolynomialRelation l s g) :
    HasPolynomialRelation l s (fun x => f x - g x) := by
  let : Algebra ℝ[X] (Germ l ℝ) := (germPolynomialEvaluation l s).toAlgebra
  apply (hasPolynomialRelation_iff_isAlgebraic l s _).mpr
  exact ((hasPolynomialRelation_iff_isAlgebraic l s f).mp hf).sub
    ((hasPolynomialRelation_iff_isAlgebraic l s g).mp hg)

theorem mul (hf : HasPolynomialRelation l s f) (hg : HasPolynomialRelation l s g) :
    HasPolynomialRelation l s (fun x => f x * g x) := by
  let : Algebra ℝ[X] (Germ l ℝ) := (germPolynomialEvaluation l s).toAlgebra
  apply (hasPolynomialRelation_iff_isAlgebraic l s _).mpr
  exact ((hasPolynomialRelation_iff_isAlgebraic l s f).mp hf).mul
    ((hasPolynomialRelation_iff_isAlgebraic l s g).mp hg)

theorem pow (hf : HasPolynomialRelation l s f) (n : ℕ) :
    HasPolynomialRelation l s (fun x => f x ^ n) := by
  let : Algebra ℝ[X] (Germ l ℝ) := (germPolynomialEvaluation l s).toAlgebra
  apply (hasPolynomialRelation_iff_isAlgebraic l s _).mpr
  exact ((hasPolynomialRelation_iff_isAlgebraic l s f).mp hf).pow n

end HasPolynomialRelation

/-- The reciprocal of the base coordinate is algebraic wherever it is eventually nonzero. -/
theorem hasPolynomialRelation_inv {α : Type*} {l : Filter α} {s : α → ℝ}
    (hs : ∀ᶠ x in l, s x ≠ 0) :
    HasPolynomialRelation l s (fun x => (s x)⁻¹) := by
  refine ⟨C X * Y - 1, ?_, ?_⟩
  · intro hzero
    have hcoeff := congrArg (fun p : ℝ[X][Y] => p.coeff 1) hzero
    simp [Polynomial.coeff_one] at hcoeff
  · filter_upwards [hs] with x hx
    simp [evalEval_C, hx]

/-- Scaling the difference of two algebraic functions by an inverse coordinate
power produces an explicit eventual polynomial relation. -/
theorem hasPolynomialRelation_scaled_gap {α : Type*} {l : Filter α}
    {s r b : α → ℝ} (hr : HasPolynomialRelation l s r)
    (hb : HasPolynomialRelation l s b) (hs : ∀ᶠ x in l, s x ≠ 0) (n : ℕ) :
    HasPolynomialRelation l s (fun x => (r x - b x) / s x ^ n) := by
  apply ((hr.sub hb).mul ((hasPolynomialRelation_inv hs).pow n)).congr
  exact Filter.Eventually.of_forall fun x => by simp only [div_eq_mul_inv, inv_pow]

/-- A divergent function with logarithmic upper growth is transcendental over
the polynomial ring in the reciprocal independent variable. -/
theorem no_polynomialRelation_of_logBound {g : ℝ → ℝ}
    (hg : Tendsto g atTop atTop) (hlog : g =O[atTop] Real.log) :
    ¬ HasPolynomialRelation atTop (fun x : ℝ => x⁻¹) g := by
  rintro ⟨p, hp, hrel⟩
  apply no_bivariate_relation_of_logBound hg hlog
    (p := Polynomial.Bivariate.swap p)
    (fun h => hp (Polynomial.Bivariate.swap.injective (by simpa using h)))
  simpa only [bivariate_eval_swap] using hrel

end VolumePolynomials
