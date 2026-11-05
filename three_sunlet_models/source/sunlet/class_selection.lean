module

public import sunlet.identified_normalization
public import sunlet.weighted_initial
public import Mathlib.Data.Finset.Sort

/-!
# Actual initial monomials for an ordered class partition

The integer weights realize the cross-class and same-class choices in §7.1.
Algebraic independence is proved over an arbitrary field from rational
independence of the actual selected exponents.
-/

@[expose] public section
noncomputable section
open scoped BigOperators MonomialOrder
open MvPolynomial

namespace Sunlet.ClassSelection

variable {K G C : Type*} [Field K] [AddCommGroup G]
  [Fintype C] [LinearOrder C]

def selectsU (q : G → C) (σ : Set C) (b c : G) : Prop :=
  q b < q c ∨ (q b = q c ∧ q (c - b) ∈ σ)

instance (q : G → C) (σ : Set C) [DecidablePred (· ∈ σ)] (b c : G) :
    Decidable (selectsU q σ b c) := by unfold selectsU; infer_instance

def uExponent (q : G → C) (bc : G × G) : ParamVar C C →₀ ℕ :=
  (Finsupp.single (.s (q bc.1)) 1 + Finsupp.single (.t (q bc.2)) 1) +
    (Finsupp.single (.u (q (bc.2 - bc.1))) 1 + Finsupp.single (.h (q bc.2)) 1)

def vExponent (q : G → C) (bc : G × G) : ParamVar C C →₀ ℕ :=
  (Finsupp.single (.s (q bc.1)) 1 + Finsupp.single (.t (q bc.2)) 1) +
    (Finsupp.single (.v (q (bc.2 - bc.1))) 1 + Finsupp.single (.h (q bc.1)) 1)

def selectedExponent (q : G → C) (σ : Set C) [DecidablePred (· ∈ σ)]
    (bc : G × G) : ParamVar C C →₀ ℕ :=
  if selectsU q σ bc.1 bc.2 then uExponent q bc else vExponent q bc

def orderRank (i : C) : ℕ := ((Fintype.orderIsoFinOfCardEq C rfl).symm i).val

theorem orderRank_strictMono : StrictMono (orderRank (C := C)) := by
  intro a b hab
  exact (Fintype.orderIsoFinOfCardEq C rfl).symm.strictMono hab

def reverseWeight (σ : Set C) [DecidablePred (· ∈ σ)] : ParamVar C C → ℕ
  | .s _ => 0
  | .t _ => 0
  | .h i => 2 * orderRank i
  | .u i => if i ∈ σ then 1 else 0
  | .v i => if i ∈ σ then 0 else 1

def liftedVariable (σ : Set C) [DecidablePred (· ∈ σ)]
    (i : ParamVar C C) : WithBot (ParamVar C C) →₀ ℕ :=
  Finsupp.single (i : WithBot (ParamVar C C)) 1 + Finsupp.single ⊥ (reverseWeight σ i)

def liftedU (q : G → C) (σ : Set C) [DecidablePred (· ∈ σ)]
    (bc : G × G) : WithBot (ParamVar C C) →₀ ℕ :=
  (liftedVariable σ (.s (q bc.1)) + liftedVariable σ (.t (q bc.2))) +
    (liftedVariable σ (.u (q (bc.2 - bc.1))) + liftedVariable σ (.h (q bc.2)))

def liftedV (q : G → C) (σ : Set C) [DecidablePred (· ∈ σ)]
    (bc : G × G) : WithBot (ParamVar C C) →₀ ℕ :=
  (liftedVariable σ (.s (q bc.1)) + liftedVariable σ (.t (q bc.2))) +
    (liftedVariable σ (.v (q (bc.2 - bc.1))) + liftedVariable σ (.h (q bc.1)))

def selectedLifted (q : G → C) (σ : Set C) [DecidablePred (· ∈ σ)]
    (bc : G × G) : WithBot (ParamVar C C) →₀ ℕ :=
  if selectsU q σ bc.1 bc.2 then liftedU q σ bc else liftedV q σ bc

def weightHom (σ : Set C) [DecidablePred (· ∈ σ)] :
    MvPolynomial (ParamVar C C) K →ₐ[K] MvPolynomial (WithBot (ParamVar C C)) K :=
  aeval fun i => monomial (liftedVariable σ i) 1

theorem weightHom_coordinate (q : G → C) (σ : Set C) [DecidablePred (· ∈ σ)]
    (bc : G × G) :
    weightHom (K := K) σ (Identified.coordinatePolynomial q (bc.2 - bc.1, bc.1)) =
      monomial (liftedU q σ bc) 1 + monomial (liftedV q σ bc) 1 := by
  simp [weightHom, Identified.coordinatePolynomial, liftedU, liftedV, mul_add, monomial_mul]

theorem selectedLifted_coe (q : G → C) (σ : Set C) [DecidablePred (· ∈ σ)]
    (bc : G × G) (i : ParamVar C C) :
    selectedLifted q σ bc (i : WithBot (ParamVar C C)) = selectedExponent q σ bc i := by
  simp only [selectedLifted, selectedExponent]
  split_ifs <;> simp [liftedU, liftedV, liftedVariable, uExponent, vExponent, Finsupp.single_apply]

theorem strict_selected_weight (q : G → C) (σ : Set C) [DecidablePred (· ∈ σ)]
    (bc : G × G) :
    if selectsU q σ bc.1 bc.2 then liftedV q σ bc ⊥ < liftedU q σ bc ⊥
    else liftedU q σ bc ⊥ < liftedV q σ bc ⊥ := by
  rcases bc with ⟨b, c⟩
  rcases lt_trichotomy (q b) (q c) with h | h | h
  · have hr := orderRank_strictMono h
    by_cases hs : q (c - b) ∈ σ <;>
      simp [selectsU, h, liftedU, liftedV, liftedVariable, reverseWeight, hs] <;> omega
  · by_cases hs : q (c - b) ∈ σ <;>
      simp [selectsU, h, liftedU, liftedV, liftedVariable, reverseWeight, hs]
  · have hr := orderRank_strictMono h
    have hlt : ¬ q b < q c := not_lt.mpr h.le
    have hne : q b ≠ q c := Ne.symm (ne_of_lt h)
    by_cases hs : q (c - b) ∈ σ <;>
      simp [selectsU, hlt, hne, liftedU, liftedV, liftedVariable, reverseWeight, hs] <;> omega

section MonomialOrder

variable [LinearOrder (ParamVar C C)]

theorem weighted_leading (q : G → C) (σ : Set C) [DecidablePred (· ∈ σ)]
    (bc : G × G) :
    MonomialOrder.lex.degree
        (weightHom (K := K) σ (Identified.coordinatePolynomial q (bc.2 - bc.1, bc.1))) =
        selectedLifted q σ bc ∧
      MonomialOrder.lex.Monic
        (weightHom (K := K) σ (Identified.coordinatePolynomial q (bc.2 - bc.1, bc.1))) := by
  classical
  let m : MonomialOrder (WithBot (ParamVar C C)) := MonomialOrder.lex
  have hw := strict_selected_weight q σ bc
  rw [weightHom_coordinate, selectedLifted]
  by_cases hs : selectsU q σ bc.1 bc.2
  · simp only [if_pos hs] at hw ⊢
    have hlt : m.degree (monomial (liftedV q σ bc) (1 : K)) ≺[m]
        m.degree (monomial (liftedU q σ bc) (1 : K)) := by
      simpa [m.degree_monomial] using (WeightedInitial.lex_lt_of_bot hw)
    exact ⟨by simpa [m, m.degree_monomial] using m.degree_add_of_lt hlt,
      m.monic_monomial_one.add_of_lt hlt⟩
  · simp only [if_neg hs] at hw ⊢
    have hlt : m.degree (monomial (liftedU q σ bc) (1 : K)) ≺[m]
        m.degree (monomial (liftedV q σ bc) (1 : K)) := by
      simpa [m.degree_monomial] using (WeightedInitial.lex_lt_of_bot hw)
    rw [add_comm]
    exact ⟨by simpa [m, m.degree_monomial] using m.degree_add_of_lt hlt,
      m.monic_monomial_one.add_of_lt hlt⟩

end MonomialOrder

theorem coordinate_subfamily_algebraicIndependent
    {I : Type*} [Fintype I] (q : G → C) (σ : Set C) [DecidablePred (· ∈ σ)]
    (r : I → G × G)
    (hr : LinearIndependent ℚ (fun j i => (selectedExponent q σ (r j) i : ℚ))) :
    AlgebraicIndependent K (fun j =>
      Identified.coordinatePolynomial (K := K) q ((r j).2 - (r j).1, (r j).1)) := by
  classical
  letI : LinearOrder (ParamVar C C) := LinearOrder.lift'
    (Fintype.equivFin (ParamVar C C)) (Fintype.equivFin (ParamVar C C)).injective
  let m : MonomialOrder (WithBot (ParamVar C C)) := MonomialOrder.lex
  let f : I → MvPolynomial (ParamVar C C) K := fun j =>
    Identified.coordinatePolynomial q ((r j).2 - (r j).1, (r j).1)
  let φ := weightHom (K := K) σ
  have hdegree (j : I) : m.degree (φ (f j)) = selectedLifted q σ (r j) :=
    (weighted_leading q σ (r j)).1
  have hn (j : I) : φ (f j) ≠ 0 := (weighted_leading q σ (r j)).2.ne_zero
  have hlin : LinearIndependent ℚ (fun j i => (m.degree (φ (f j)) i : ℚ)) := by
    apply LinearIndependent.of_comp (WeightedInitial.forgetWeight (ι := C) (Ω := C))
    convert hr using 1
    funext j i
    simp only [Function.comp_apply, WeightedInitial.forgetWeight, LinearMap.coe_mk,
      AddHom.coe_mk, hdegree, selectedLifted_coe]
  exact AlgebraicIndependent.of_comp φ
    (InitialIndependence.algebraicIndependent_of_rational_leading_exponents m
      (fun j => φ (f j)) hn hlin)

end Sunlet.ClassSelection
