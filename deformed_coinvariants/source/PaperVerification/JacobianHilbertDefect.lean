module

public import PaperVerification.JacobianDegree
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Hilbert-function additivity for the literal Jacobian quotients

The homogeneous source spaces are finite dimensional because the coordinate
weights are positive. Rank-nullity is applied in each actual quotient component.
The resulting power-series identity records the exact degree of the defect.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial
open scoped BigOperators

namespace PaperVerification.EulerResonance

variable {K ι : Type*} [Field K] [Fintype ι]
local notation "P" => MvPolynomial ι K

theorem quotientComponent_finrank_add (w : ι → ℕ) (d : ℕ)
    (U V : Submodule K P) (hUV : U ≤ V) (hw : ∀ i, 0 < w i) :
    Module.finrank K (quotientComponent w d U) =
      Module.finrank K (quotientComponent w d V) +
      Module.finrank K ↥(V.map U.mkQ ⊓ quotientComponent w d U : Submodule K (P ⧸ U)) := by
  let S := quotientComponent w d U
  let f := (Submodule.factor hUV).domRestrict S
  letI : Module.Finite K S := quotientComponent_finite w d U hw
  have hrange : LinearMap.range f = quotientComponent w d V := by
    dsimp only [f, LinearMap.domRestrict]
    rw [LinearMap.range_comp, Submodule.range_subtype]
    dsimp only [S]
    rw [quotientComponent_eq_map, ← Submodule.map_comp, Submodule.factor_comp_mk,
      ← quotientComponent_eq_map]
  have hfactor : LinearMap.ker (Submodule.factor hUV) = V.map U.mkQ := by
    rw [Submodule.factor, Submodule.ker_mapQ, Submodule.comap_id]
  have hkernel : (LinearMap.ker f).map S.subtype = V.map U.mkQ ⊓ S := by
    dsimp only [f, LinearMap.domRestrict]
    rw [LinearMap.ker_comp, hfactor,
      Submodule.map_comap_subtype, inf_comm]
  have hdim := f.finrank_range_add_finrank_ker
  rw [hrange, ← Submodule.finrank_map_subtype_eq S (LinearMap.ker f), hkernel] at hdim
  exact hdim.symm

/-- The Hilbert series uses the dimensions of the actual homogeneous quotient
components, rather than an abstract sequence supplied as a hypothesis. -/
def hilbertSeries (w : ι → ℕ) (U : Submodule K P) : PowerSeries ℕ :=
  PowerSeries.mk fun d => Module.finrank K (quotientComponent w d U)

@[simp] theorem coeff_hilbertSeries (w : ι → ℕ) (U : Submodule K P) (d : ℕ) :
    PowerSeries.coeff d (hilbertSeries w U) = Module.finrank K (quotientComponent w d U) :=
  PowerSeries.coeff_mk _ _

end PaperVerification.EulerResonance

namespace PaperVerification.JacobianDivergence

variable {K ι : Type*} [Field K] [CharZero K] [Fintype ι]
local notation "P" => MvPolynomial ι K

theorem exceptional_hilbert_function (F : P) (w : ι → ℕ) (h d e : ℕ) (t : K)
    (hw : ∀ i, 0 < w i) (hh : 0 < h) (hF : F.IsWeightedHomogeneous w h)
    (hres : (h : K) + t * ((∑ i, w i : ℕ) + d : K) = 0) :
    Module.finrank K
        (EulerResonance.quotientComponent w e (EulerJacobian.hit (gradient F) F t)) =
      Module.finrank K (EulerResonance.quotientComponent w e (jacobianSubmodule F)) +
      if e = h + d then Module.finrank K (DefectQuotient F t) else 0 := by
  have hdim := EulerResonance.quotientComponent_finrank_add w e
    (EulerJacobian.hit (gradient F) F t) (jacobianSubmodule F)
    (hit_le_jacobian F w h t hh hF) hw
  change _ = _ + Module.finrank K
    ↥(defectImage F t ⊓ EulerResonance.quotientComponent w e
      (EulerJacobian.hit (gradient F) F t) :
        Submodule K (P ⧸ EulerJacobian.hit (gradient F) F t)) at hdim
  by_cases he : e = h + d
  · subst e
    rw [inf_eq_left.mpr (exceptional_defect_concentrated F w h d t hh hF hres)] at hdim
    rw [if_pos rfl]
    exact hdim.trans (congrArg (_ + ·) (defectQuotientEquivImage F t).finrank_eq.symm)
  · rw [exceptional_defect_other_degree F w h d e t hh hF hres (Ne.symm he),
      finrank_bot, add_zero] at hdim
    simpa only [if_neg he, add_zero] using hdim

/-- The defect contributes one homogeneous term. The coefficient is the
dimension of the literal quotient `J(F)/H_t(F)`. The Brieskorn comparison and
homogeneous tower basis compute it separately. -/
theorem exceptional_hilbert_series (F : P) (w : ι → ℕ) (h d : ℕ) (t : K)
    (hw : ∀ i, 0 < w i) (hh : 0 < h) (hF : F.IsWeightedHomogeneous w h)
    (hres : (h : K) + t * ((∑ i, w i : ℕ) + d : K) = 0) :
    EulerResonance.hilbertSeries w (EulerJacobian.hit (gradient F) F t) =
      EulerResonance.hilbertSeries w (jacobianSubmodule F) +
        PowerSeries.monomial (h + d) (Module.finrank K (DefectQuotient F t)) := by
  ext e
  simp only [map_add, EulerResonance.coeff_hilbertSeries, PowerSeries.coeff_monomial]
  simpa only [eq_comm] using exceptional_hilbert_function F w h d e t hw hh hF hres

end PaperVerification.JacobianDivergence
