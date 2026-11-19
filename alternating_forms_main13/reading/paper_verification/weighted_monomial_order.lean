module

public import Mathlib.Data.Finsupp.MonomialOrder
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Algebra.Order.Monoid.Prod
public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Order.Basic

/-!
# A monomial order refining an actual natural weight

The synonym is the additive graph of `(weight, oldOrder)` inside the
lexicographic product. This constructs the order and its well-foundedness;
no compatibility or termination condition is assumed of the weight.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.WeightedMonomialOrder

variable {σ : Type*}

/-- A base monomial order on any finite variable set. The temporary
linear order is scoped inside this definition, so it does not replace any
existing partial order used to express the mathematical chain condition. -/
def finiteBaseOrder (σ : Type*) [Fintype σ] : MonomialOrder σ := by
  classical
  let e := Fintype.equivFin σ
  letI : LinearOrder σ := LinearOrder.lift' e e.injective
  letI : WellFoundedGT σ := InvImage.wf e (wellFounded_gt (α := Fin (Fintype.card σ)))
  exact MonomialOrder.lex

def graph (m : MonomialOrder σ) (w : σ → ℕ) :
    (σ →₀ ℕ) →+ Lex (ℕ × m.syn) where
  toFun a := toLex (Finsupp.weight w a,m.toSyn a)
  map_zero' := by simp only [map_zero]; rfl
  map_add' a b := by simp only [map_add]; rfl

theorem graph_injective (m : MonomialOrder σ) (w : σ → ℕ) :
    Function.Injective (graph m w) := by
  intro a b h
  exact m.toSyn.injective (congrArg (fun z : Lex (ℕ × m.syn) => (ofLex z).2) h)

def weightedRefinement (m : MonomialOrder σ) (w : σ → ℕ) : MonomialOrder σ where
  syn := AddMonoidHom.mrange (graph m w)
  toSyn :=
    { Equiv.ofBijective (AddMonoidHom.mrangeRestrict (graph m w))
        ⟨fun a b h => graph_injective m w (congrArg Subtype.val h),
          AddMonoidHom.mrangeRestrict_surjective (graph m w)⟩ with
      map_add' a b := by
        apply Subtype.ext
        exact (graph m w).map_add' a b }
  toSyn_monotone := by
    intro a b hab
    change toLex (Finsupp.weight w a,m.toSyn a)≤toLex (Finsupp.weight w b,m.toSyn b)
    apply Prod.Lex.le_iff.mpr
    have hw : Finsupp.weight w a≤Finsupp.weight w b := by
      obtain ⟨c,rfl⟩ := exists_add_of_le hab
      rw [map_add]
      exact Nat.le_add_right _ _
    rcases hw.lt_or_eq with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h,m.toSyn_monotone hab⟩

theorem lt_of_weight_lt (m : MonomialOrder σ) (w : σ → ℕ) (a b : σ →₀ ℕ)
    (h : Finsupp.weight w a<Finsupp.weight w b) :
    (weightedRefinement m w).toSyn a<(weightedRefinement m w).toSyn b := by
  change toLex (Finsupp.weight w a,m.toSyn a)<toLex (Finsupp.weight w b,m.toSyn b)
  exact Prod.Lex.lt_iff.mpr (Or.inl h)

theorem weight_le_of_le (m : MonomialOrder σ) (w : σ → ℕ) (a b : σ →₀ ℕ)
    (h : (weightedRefinement m w).toSyn a≤(weightedRefinement m w).toSyn b) :
    Finsupp.weight w a≤Finsupp.weight w b := by
  change toLex (Finsupp.weight w a,m.toSyn a)≤toLex (Finsupp.weight w b,m.toSyn b) at h
  rcases Prod.Lex.le_iff.mp h with h | ⟨h,_⟩
  · exact h.le
  · exact h.le

theorem lt_of_weight_eq_of_lt (m : MonomialOrder σ) (w : σ → ℕ)
    (a b : σ →₀ ℕ) (he : Finsupp.weight w a=Finsupp.weight w b)
    (hlt : m.toSyn a<m.toSyn b) :
    (weightedRefinement m w).toSyn a<(weightedRefinement m w).toSyn b := by
  change toLex (Finsupp.weight w a,m.toSyn a)<toLex (Finsupp.weight w b,m.toSyn b)
  exact Prod.Lex.lt_iff.mpr (Or.inr ⟨he,hlt⟩)

end PaperVerification.WeightedMonomialOrder
