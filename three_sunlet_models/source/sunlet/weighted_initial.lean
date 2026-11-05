module

public import sunlet.selected_exponents
public import sunlet.exponent_independence
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Order.WithBot

/-! Realizing the paper's weight selection by an ordinary lexicographic order.
An extra variable records reversed weights. All original monomials have total
degree four, so reversing each weight selects exactly the stated least-weight
term. The new variable is eliminated only through a proved algebra homomorphism. -/

@[expose] public section
noncomputable section
open scoped BigOperators MonomialOrder
open MvPolynomial Sunlet.SelectedRelations Sunlet.SelectedExponents

namespace Sunlet.WeightedInitial

variable {K ι Ω : Type*} [Field K] [Fintype ι] [Fintype Ω]
  [DecidableEq ι] [DecidableEq Ω]

def reverseWeight (o : Ω) (P : Set ι) [DecidablePred (· ∈ P)] : ParamVar ι Ω → ℕ
  | .s _ => 2
  | .t _ => 2
  | .h b => if b = o then 0 else 2
  | .u a => if a ∈ P then 2 else 1
  | .v a => if a ∈ P then 1 else 2

def liftedVariable (o : Ω) (P : Set ι) [DecidablePred (· ∈ P)]
    (i : ParamVar ι Ω) : WithBot (ParamVar ι Ω) →₀ ℕ :=
  Finsupp.single (i : WithBot (ParamVar ι Ω)) 1 +
    Finsupp.single ⊥ (reverseWeight o P i)

def liftedU (π : ι → Equiv.Perm Ω) (o : Ω) (P : Set ι) [DecidablePred (· ∈ P)]
    (ab : ι × Ω) : WithBot (ParamVar ι Ω) →₀ ℕ :=
  (liftedVariable o P (.s ab.2) + liftedVariable o P (.t (π ab.1 ab.2))) +
    (liftedVariable o P (.u ab.1) + liftedVariable o P (.h (π ab.1 ab.2)))

def liftedV (π : ι → Equiv.Perm Ω) (o : Ω) (P : Set ι) [DecidablePred (· ∈ P)]
    (ab : ι × Ω) : WithBot (ParamVar ι Ω) →₀ ℕ :=
  (liftedVariable o P (.s ab.2) + liftedVariable o P (.t (π ab.1 ab.2))) +
    (liftedVariable o P (.v ab.1) + liftedVariable o P (.h ab.2))

def selectedLifted (π : ι → Equiv.Perm Ω) (e : ι) (o : Ω) (P : Set ι)
    [DecidablePred (· ∈ P)] (ab : ι × Ω) : WithBot (ParamVar ι Ω) →₀ ℕ :=
  if selectsU π e o P ab.1 ab.2 then liftedU π o P ab else liftedV π o P ab

def weightHom (o : Ω) (P : Set ι) [DecidablePred (· ∈ P)] :
    MvPolynomial (ParamVar ι Ω) K →ₐ[K] MvPolynomial (WithBot (ParamVar ι Ω)) K :=
  aeval fun i => monomial (liftedVariable o P i) 1

theorem weightHom_coordinate (π : ι → Equiv.Perm Ω) (o : Ω) (P : Set ι)
    [DecidablePred (· ∈ P)] (ab : ι × Ω) :
    weightHom (K := K) o P (coordinatePolynomial π ab) =
      monomial (liftedU π o P ab) 1 + monomial (liftedV π o P ab) 1 := by
  simp [weightHom, coordinatePolynomial, liftedU, liftedV, mul_add, monomial_mul]

theorem selectedLifted_coe (π : ι → Equiv.Perm Ω) (e : ι) (o : Ω) (P : Set ι)
    [DecidablePred (· ∈ P)] (ab : ι × Ω) (i : ParamVar ι Ω) :
    selectedLifted π e o P ab (i : WithBot (ParamVar ι Ω)) = selectedExponent π e o P ab i := by
  simp only [selectedLifted, selectedExponent]
  split_ifs <;>
    simp [liftedU, liftedV, liftedVariable, uExponent, vExponent, Finsupp.single_apply]

/-- The two monomial weights differ strictly in exactly the direction in the
paper's selection table, including the identity color and the exceptional edges. -/
theorem strict_selected_weight
    (π : ι → Equiv.Perm Ω) (e : ι) (o : Ω) (P : Set ι) [DecidablePred (· ∈ P)]
    (he : π e = Equiv.refl Ω) (heP : e ∉ P)
    (hder : ∀ a, a ≠ e → ∀ b, π a b ≠ b) (ab : ι × Ω) :
    if selectsU π e o P ab.1 ab.2 then
      liftedV π o P ab ⊥ < liftedU π o P ab ⊥
    else liftedU π o P ab ⊥ < liftedV π o P ab ⊥ := by
  rcases ab with ⟨a, b⟩
  by_cases ha : a = e
  · subst a
    simp [selectsU, heP, liftedU, liftedV, liftedVariable, reverseWeight, he]
  · have hfix : π a o ≠ o := hder a ha o
    have hpre : b = (π a).symm o ↔ π a b = o := (π a).eq_symm_apply
    by_cases haP : a ∈ P <;> by_cases hb : b = o <;> by_cases hp : π a b = o
    all_goals try { subst b; exact (hfix hp).elim }
    all_goals simp [selectsU, haP, hpre, ha, hb, hp, hfix, Equiv.eq_symm_apply,
      liftedU, liftedV, liftedVariable, reverseWeight]

section MonomialOrder

variable [LinearOrder (ParamVar ι Ω)]

lemma lex_lt_of_bot {d e : WithBot (ParamVar ι Ω) →₀ ℕ} (h : d ⊥ < e ⊥) :
    d ≺[MonomialOrder.lex] e := by
  rw [MonomialOrder.lex_lt_iff, Finsupp.Lex.lt_iff]
  exact ⟨⊥, fun i hi => (not_lt_of_ge bot_le hi).elim, h⟩

theorem weighted_leading
    (π : ι → Equiv.Perm Ω) (e : ι) (o : Ω) (P : Set ι) [DecidablePred (· ∈ P)]
    (he : π e = Equiv.refl Ω) (heP : e ∉ P)
    (hder : ∀ a, a ≠ e → ∀ b, π a b ≠ b) (ab : ι × Ω) :
    MonomialOrder.lex.degree (weightHom (K := K) o P (coordinatePolynomial π ab)) =
        selectedLifted π e o P ab ∧
      MonomialOrder.lex.Monic (weightHom (K := K) o P (coordinatePolynomial π ab)) := by
  classical
  let m : MonomialOrder (WithBot (ParamVar ι Ω)) := MonomialOrder.lex
  have hw := strict_selected_weight π e o P he heP hder ab
  rw [weightHom_coordinate, selectedLifted]
  by_cases hs : selectsU π e o P ab.1 ab.2
  · simp only [if_pos hs] at hw ⊢
    have hlt : m.degree (monomial (liftedV π o P ab) (1 : K)) ≺[m]
        m.degree (monomial (liftedU π o P ab) (1 : K)) := by
      simpa [m.degree_monomial] using (lex_lt_of_bot hw)
    exact ⟨by simpa [m, m.degree_monomial] using m.degree_add_of_lt hlt,
      m.monic_monomial_one.add_of_lt hlt⟩
  · simp only [if_neg hs] at hw ⊢
    have hlt : m.degree (monomial (liftedU π o P ab) (1 : K)) ≺[m]
        m.degree (monomial (liftedV π o P ab) (1 : K)) := by
      simpa [m.degree_monomial] using (lex_lt_of_bot hw)
    rw [add_comm]
    exact ⟨by simpa [m, m.degree_monomial] using m.degree_add_of_lt hlt,
      m.monic_monomial_one.add_of_lt hlt⟩

end MonomialOrder

def forgetWeight : (WithBot (ParamVar ι Ω) → ℚ) →ₗ[ℚ] (ParamVar ι Ω → ℚ) where
  toFun w i := w i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Every rationally independent subfamily of the selected exponents gives an
algebraically independent subfamily of the actual coordinate polynomials. -/
theorem coordinate_subfamily_algebraicIndependent
    {I : Type*} [Fintype I]
    (π : ι → Equiv.Perm Ω) (e : ι) (o : Ω) (P : Set ι) [DecidablePred (· ∈ P)]
    (he : π e = Equiv.refl Ω) (heP : e ∉ P)
    (hder : ∀ a, a ≠ e → ∀ b, π a b ≠ b)
    (r : I → ι × Ω)
    (hr : LinearIndependent ℚ (fun j i => (selectedExponent π e o P (r j) i : ℚ))) :
    AlgebraicIndependent K (fun j => coordinatePolynomial (K := K) π (r j)) := by
  classical
  letI : LinearOrder (ParamVar ι Ω) := LinearOrder.lift'
    (Fintype.equivFin (ParamVar ι Ω)) (Fintype.equivFin (ParamVar ι Ω)).injective
  let m : MonomialOrder (WithBot (ParamVar ι Ω)) := MonomialOrder.lex
  let f : I → MvPolynomial (ParamVar ι Ω) K := fun j => coordinatePolynomial π (r j)
  let φ := weightHom (K := K) o P
  have hdegree (j : I) : m.degree (φ (f j)) = selectedLifted π e o P (r j) :=
    (weighted_leading π e o P he heP hder (r j)).1
  have hn (j : I) : φ (f j) ≠ 0 :=
    (weighted_leading π e o P he heP hder (r j)).2.ne_zero
  have hlin : LinearIndependent ℚ (fun j i => (m.degree (φ (f j)) i : ℚ)) := by
    apply LinearIndependent.of_comp (forgetWeight (ι := ι) (Ω := Ω))
    convert hr using 1
    funext j i
    simp only [Function.comp_apply, forgetWeight, LinearMap.coe_mk, AddHom.coe_mk,
      hdegree, selectedLifted_coe]
  have hh := InitialIndependence.algebraicIndependent_of_rational_leading_exponents
    m (fun j => φ (f j)) hn hlin
  exact AlgebraicIndependent.of_comp φ hh

end Sunlet.WeightedInitial
