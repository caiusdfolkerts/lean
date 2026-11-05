module

public import PaperVerification.PolynomialDivergence
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# Actual weighted degrees of polynomial derivations

Degrees are integers, so a derivative never replaces a negative-degree piece
by the constant piece. A derivation has degree `d` precisely when it sends
every polynomial component of degree `e` to degree `e+d`. The coordinate
criterion, divergence degree, bracket degree, and component identities are
all proved from the actual polynomial maps.

This supporting source has not yet been compiled.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.PolynomialHomogeneousDerivations

open MvPolynomial PolynomialDivergence
open scoped BigOperators

variable {K ι : Type*} [CommRing K] [Fintype ι]
local notation "P" => MvPolynomial ι K
local notation "Der" => Derivation K P P

/-- The literal coefficient degrees of the vector field. -/
def HasDegree (w : ι → ℤ) (D : Der) (d : ℤ) : Prop :=
  ∀ i, IsWeightedHomogeneous w (D (X i)) (d+w i)

theorem apply_homogeneous {w : ι → ℤ} {D : Der} {d e : ℤ}
    (hD : HasDegree w D d) {p : P} (hp : IsWeightedHomogeneous w p e) :
    IsWeightedHomogeneous w (D p) (e+d) := by
  rw [apply_eq_sum D p]
  apply IsWeightedHomogeneous.sum
  intro i hi
  have hpartial := hp.pderiv (i := i) (n' := e-w i) (by omega)
  have hprod := (hD i).mul hpartial
  convert hprod using 1 <;> omega

/-- This identifies the coordinate definition with the ordinary graded-map
meaning; neither direction is left as an informal interpretation. -/
theorem hasDegree_iff (w : ι → ℤ) (D : Der) (d : ℤ) :
    HasDegree w D d ↔
      ∀ e p, IsWeightedHomogeneous w p e →
        IsWeightedHomogeneous w (D p) (e+d) := by
  constructor
  · intro hD e p hp
    exact apply_homogeneous hD hp
  · intro h i
    simpa only [add_comm (w i) d] using h (w i) (X i) (isWeightedHomogeneous_X w i)

theorem divergence_homogeneous {w : ι → ℤ} {D : Der} {d : ℤ}
    (hD : HasDegree w D d) : IsWeightedHomogeneous w (divergence D) d := by
  rw [divergence_apply]
  apply IsWeightedHomogeneous.sum
  intro i hi
  exact (hD i).pderiv rfl

theorem bracket_hasDegree {w : ι → ℤ} {D E : Der} {d e : ℤ}
    (hD : HasDegree w D d) (hE : HasDegree w E e) :
    HasDegree w ⁅D,E⁆ (d+e) := by
  intro i
  rw [Derivation.commutator_apply]
  apply IsWeightedHomogeneous.sub
  · have h := apply_homogeneous hD (hE i)
    convert h using 1 <;> omega
  · have h := apply_homogeneous hE (hD i)
    convert h using 1 <;> omega

theorem polynomial_smul_hasDegree {w : ι → ℤ} {D : Der} {d e : ℤ}
    (hD : HasDegree w D d) {p : P} (hp : IsWeightedHomogeneous w p e) :
    HasDegree w (p • D) (e+d) := by
  intro i
  change IsWeightedHomogeneous w (p * D (X i)) ((e+d)+w i)
  simpa only [add_assoc] using hp.mul (hD i)

/-- A homogeneous linear map commutes with the actual component projections
with precisely the stated degree shift. The proof checks every monomial. -/
theorem component_map (w : ι → ℤ) (T : P →ₗ[K] P) (d : ℤ)
    (hT : ∀ e p, IsWeightedHomogeneous w p e →
      IsWeightedHomogeneous w (T p) (e+d)) (n : ℤ) (p : P) :
    weightedHomogeneousComponent w (n+d) (T p) =
      T (weightedHomogeneousComponent w n p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
      simp only [map_add,hp,hq]
  | monomial a c =>
      have hm := isWeightedHomogeneous_monomial w a c rfl
      have ht := hT (Finsupp.weight w a) (monomial a c) hm
      rw [weightedHomogeneousComponent_of_mem ht,
        weightedHomogeneousComponent_of_mem hm]
      by_cases hn : n = Finsupp.weight w a
      · simp only [hn,if_pos rfl]
      · have hnd : n+d ≠ Finsupp.weight w a+d := fun h => hn (add_right_cancel h)
        simp only [if_neg hn,if_neg hnd,map_zero]

theorem component_derivation {w : ι → ℤ} {D : Der} {d : ℤ}
    (hD : HasDegree w D d) (n : ℤ) (p : P) :
    weightedHomogeneousComponent w (n+d) (D p) =
      D (weightedHomogeneousComponent w n p) :=
  component_map w D.toLinearMap d ((hasDegree_iff w D d).mp hD) n p

theorem component_multiply {w : ι → ℤ} {q : P} {d : ℤ}
    (hq : IsWeightedHomogeneous w q d) (n : ℤ) (p : P) :
    weightedHomogeneousComponent w (n+d) (q*p) =
      q * weightedHomogeneousComponent w n p := by
  apply component_map w (LinearMap.mulLeft K q) d
  intro e f hf
  simpa only [LinearMap.mulLeft_apply,add_comm d e] using hq.mul hf

end PaperVerification.PolynomialHomogeneousDerivations
