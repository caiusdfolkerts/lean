module

public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Trunc
public import Mathlib.Topology.Algebra.TopologicallyNilpotent

/-!
# Formal series evaluated at actual nilpotent elements

All coefficient and target rings carry an explicitly chosen discrete topology
inside the construction. Thus callers need only algebraic nilpotence, not any
topological hypothesis. The truncation lemma proves that evaluation is exactly
a finite polynomial calculation in every actual Artinian local factor.

-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.Fermion

open scoped PowerSeries.WithPiTopology
attribute [local instance] DiscreteTopology.instContinuousSMul

variable {F A B : Type*} [CommRing F] [CommRing A] [CommRing B]
  [Algebra F A] [Algebra F B]

local instance : UniformSpace F := ⊥
local instance : UniformSpace A := ⊥
local instance : UniformSpace B := ⊥

/-- Evaluation at a nilpotent element, with all analytic hypotheses supplied
by explicit discrete structures rather than passed to the caller. -/
def nilpotentSeriesEval (x : A) (hx : IsNilpotent x) : PowerSeries F →ₐ[F] A :=
  PowerSeries.aeval hx.isTopologicallyNilpotent

@[simp]
theorem nilpotentSeriesEval_coe (x : A) (hx : IsNilpotent x) (p : Polynomial F) :
    nilpotentSeriesEval x hx (p : PowerSeries F)=Polynomial.aeval x p :=
  PowerSeries.aeval_coe hx.isTopologicallyNilpotent p

@[simp]
theorem nilpotentSeriesEval_X (x : A) (hx : IsNilpotent x) :
    nilpotentSeriesEval x hx (PowerSeries.X : PowerSeries F)=x := by
  have hX : ((Polynomial.X : Polynomial F) : PowerSeries F)=PowerSeries.X := Polynomial.coe_X
  rw [←hX,nilpotentSeriesEval_coe,Polynomial.aeval_X]

@[simp]
theorem nilpotentSeriesEval_C (x : A) (hx : IsNilpotent x) (c : F) :
    nilpotentSeriesEval x hx (PowerSeries.C c)=algebraMap F A c := by
  rw [←Polynomial.coe_C,nilpotentSeriesEval_coe,Polynomial.aeval_C]

/-- The series evaluation is the actual finite truncation, for every
nilpotence exponent, including exponent zero in a zero ring. -/
theorem nilpotentSeriesEval_eq_trunc (x : A) (hx : IsNilpotent x)
    (N : ℕ) (hN : x^N=0) (f : PowerSeries F) :
    nilpotentSeriesEval x hx f=Polynomial.aeval x (f.trunc N) := by
  have h := congrArg (nilpotentSeriesEval x hx)
    (PowerSeries.eq_X_pow_mul_shift_add_trunc N f)
  simpa only [map_add,map_mul,map_pow,nilpotentSeriesEval_X,hN,zero_mul,zero_add,
    nilpotentSeriesEval_coe] using h

/-- Algebra homomorphisms commute with evaluation of nilpotent series. -/
theorem nilpotentSeriesEval_map (x : A) (hx : IsNilpotent x) (f : A →ₐ[F] B) :
    f.comp (nilpotentSeriesEval x hx)=
      nilpotentSeriesEval (f x) (hx.map f.toRingHom) := by
  exact PowerSeries.comp_aeval hx.isTopologicallyNilpotent
    (continuous_of_discreteTopology : Continuous f)

/-- Zero constant coefficient keeps the evaluated coordinate nilpotent. -/
theorem nilpotentSeriesEval_isNilpotent (x : A) (hx : IsNilpotent x)
    (g : PowerSeries F) (hg : g.constantCoeff=0) :
    IsNilpotent (nilpotentSeriesEval x hx g) := by
  obtain ⟨h,hh⟩ := PowerSeries.X_dvd_iff.mpr hg
  rw [hh,map_mul,nilpotentSeriesEval_X]
  obtain ⟨N,hN⟩ := hx
  exact ⟨N,by rw [mul_pow,hN,zero_mul]⟩

/-- Substitution of formal coordinates specializes to substitution in
every actual nilpotent coefficient ring. -/
theorem nilpotentSeriesEval_subst (x : A) (hx : IsNilpotent x)
    (g : PowerSeries F) (hg : g.constantCoeff=0) (f : PowerSeries F) :
    nilpotentSeriesEval x hx (f.subst g)=
      nilpotentSeriesEval (nilpotentSeriesEval x hx g)
        (nilpotentSeriesEval_isNilpotent x hx g hg) f := by
  let hgs : PowerSeries.HasSubst g := .of_constantCoeff_zero' hg
  have hc : Continuous (nilpotentSeriesEval x hx : PowerSeries F → A) :=
    PowerSeries.continuous_aeval hx.isTopologicallyNilpotent
  have he := PowerSeries.comp_aeval (R := F) hgs.hasEval hc
  rw [←PowerSeries.substAlgHom_eq_aeval hgs] at he
  have hp := AlgHom.congr_fun he f
  simpa only [AlgHom.comp_apply,PowerSeries.coe_substAlgHom,nilpotentSeriesEval] using hp

/-- The two-sided formal inverse remains a two-sided inverse on nilpotent
elements. This is the missing surjectivity step in a local coordinate change. -/
theorem nilpotentSeriesEval_subst_inverse (x : A) (hx : IsNilpotent x)
    (g : PowerSeries F) (hg : g.constantCoeff=0) (hg₁ : IsUnit (g.coeff 1)) :
    nilpotentSeriesEval (nilpotentSeriesEval x hx g)
      (nilpotentSeriesEval_isNilpotent x hx g hg) (g.substInvOfIsUnit hg₁)=x := by
  rw [←nilpotentSeriesEval_subst x hx g hg,
    PowerSeries.subst_substInvOfIsUnit_left g hg hg₁,nilpotentSeriesEval_X]

theorem nilpotentSeriesEval_inverse_subst (x : A) (hx : IsNilpotent x)
    (g : PowerSeries F) (hg : g.constantCoeff=0) (hg₁ : IsUnit (g.coeff 1)) :
    nilpotentSeriesEval (nilpotentSeriesEval x hx (g.substInvOfIsUnit hg₁))
      (nilpotentSeriesEval_isNilpotent x hx _ (PowerSeries.constantCoeff_substInvOfIsUnit g hg₁)) g=x := by
  rw [←nilpotentSeriesEval_subst x hx _ (PowerSeries.constantCoeff_substInvOfIsUnit g hg₁),
    PowerSeries.subst_substInvOfIsUnit_right g hg hg₁,nilpotentSeriesEval_X]

end PaperVerification.Fermion
