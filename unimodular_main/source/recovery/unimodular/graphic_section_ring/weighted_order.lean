module

public import Mathlib.Data.Finsupp.MonomialOrder.DegLex
public import Mathlib.Algebra.Order.Monoid.Prod

/-!
# A genuine monomial order refining a nonnegative integral height

The construction refines any existing monomial order by an additive natural
weight.  It retains all monomial-order axioms, including well-foundedness.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Unimodular.GraphicSectionRing.WeightedOrder

variable {σ : Type*}

/-- The type synonym carries the height-first order, without changing exponents. -/
def Syn (w : (σ →₀ ℕ) →+ ℕ) (m : MonomialOrder σ) := σ →₀ ℕ

def ofSyn {w : (σ →₀ ℕ) →+ ℕ} {m : MonomialOrder σ} : Syn w m ≃ (σ →₀ ℕ) :=
  Equiv.refl _

instance {w : (σ →₀ ℕ) →+ ℕ} {m : MonomialOrder σ} : AddCommMonoid (Syn w m) :=
  ofSyn.addCommMonoid

def key (w : (σ →₀ ℕ) →+ ℕ) (m : MonomialOrder σ) (x : Syn w m) : ℕ ×ₗ m.syn :=
  toLex (w (ofSyn x), m.toSyn (ofSyn x))

theorem key_injective (w : (σ →₀ ℕ) →+ ℕ) (m : MonomialOrder σ) :
    Function.Injective (key w m) := by
  intro a b h
  have hs := congrArg (fun z : ℕ ×ₗ m.syn => (ofLex z).2) h
  exact ofSyn.injective (m.toSyn.injective hs)

instance {w : (σ →₀ ℕ) →+ ℕ} {m : MonomialOrder σ} : LinearOrder (Syn w m) :=
  LinearOrder.lift' (key w m) (key_injective w m)

theorem key_add {w : (σ →₀ ℕ) →+ ℕ} {m : MonomialOrder σ} (a b : Syn w m) :
    key w m (a + b) = key w m a + key w m b := by
  change toLex (w (ofSyn a + ofSyn b), m.toSyn (ofSyn a + ofSyn b)) = _
  simp only [map_add]
  rfl

instance {w : (σ →₀ ℕ) →+ ℕ} {m : MonomialOrder σ} : IsOrderedAddMonoid (Syn w m) where
  add_le_add_left a b h c := by
    change key w m (a + c) ≤ key w m (b + c)
    rw [key_add, key_add]
    change key w m a ≤ key w m b at h
    exact add_le_add_left h (key w m c)

instance {w : (σ →₀ ℕ) →+ ℕ} {m : MonomialOrder σ} : WellFoundedLT (Syn w m) :=
  InvImage.wf (key w m) wellFounded_lt

theorem weight_monotone (w : (σ →₀ ℕ) →+ ℕ) : Monotone w := by
  intro a b hab
  have hb : b = a + (b - a) := (add_tsub_cancel_of_le hab).symm
  rw [hb, map_add]
  exact Nat.le_add_right _ _

/-- The first key is height and the second key is the supplied monomial order. -/
def refine (w : (σ →₀ ℕ) →+ ℕ) (m : MonomialOrder σ) : MonomialOrder σ where
  syn := Syn w m
  toSyn := { toEquiv := ofSyn.symm, map_add' := fun _ _ => rfl }
  toSyn_monotone a b hab := by
    change toLex (w a, m.toSyn a) ≤ toLex (w b, m.toSyn b)
    apply Prod.Lex.toLex_le_toLex.mpr
    rcases lt_or_eq_of_le (weight_monotone w hab) with hw | hw
    · exact Or.inl hw
    · exact Or.inr ⟨hw, m.toSyn_monotone hab⟩

open scoped MonomialOrder

theorem lt_of_weight_lt (w : (σ →₀ ℕ) →+ ℕ) (m : MonomialOrder σ)
    {a b : σ →₀ ℕ} (h : w a < w b) : a ≺[refine w m] b := by
  change toLex (w a, m.toSyn a) < toLex (w b, m.toSyn b)
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)

theorem weight_le_of_le (w : (σ →₀ ℕ) →+ ℕ) (m : MonomialOrder σ)
    {a b : σ →₀ ℕ} (h : a ≼[refine w m] b) : w a ≤ w b := by
  change toLex (w a, m.toSyn a) ≤ toLex (w b, m.toSyn b) at h
  rcases Prod.Lex.toLex_le_toLex.mp h with h | h
  · exact h.le
  · exact h.1.le

#print axioms refine
#print axioms lt_of_weight_lt

end Unimodular.GraphicSectionRing.WeightedOrder
