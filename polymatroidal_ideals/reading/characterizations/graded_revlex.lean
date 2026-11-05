import Characterizations.VariableOrders
import Mathlib.Data.Finsupp.MonomialOrder
import Mathlib.Order.WellFounded

/-! # Graded reverse lexicographic order as a genuine Mathlib monomial order -/
noncomputable section
namespace Characterizations
open Classical CommAlg.Polymatroid
variable {V : Type*} [Fintype V] [DecidableEq V]

def GradedReverse (V : Type*) := Exponent V

instance : AddCommMonoid (GradedReverse V) := inferInstanceAs (AddCommMonoid (Exponent V))

def gradedReverseEquiv : Exponent V ≃+ GradedReverse V := AddEquiv.refl _

def gradedReverseUnderlying (a : GradedReverse V) : Exponent V := a

section Ordered
variable [LinearOrder V]

def gradedReverseKey (a : GradedReverse V) : Lex (ℕ × (Colex (Exponent V))ᵒᵈ) :=
  toLex ((gradedReverseUnderlying a).degree, OrderDual.toDual (toColex (gradedReverseUnderlying a)))

theorem gradedReverseKey_injective : Function.Injective (gradedReverseKey (V := V)) := by
  intro a b he
  exact congrArg (fun x : Lex (ℕ × (Colex (Exponent V))ᵒᵈ) =>
    (ofColex (OrderDual.ofDual ((ofLex x).2)) : Exponent V)) he

instance : LinearOrder (GradedReverse V) :=
  LinearOrder.lift' gradedReverseKey gradedReverseKey_injective

theorem gradedReverse_lt_iff (a b : GradedReverse V) :
    a < b ↔ (gradedReverseUnderlying a).degree < (gradedReverseUnderlying b).degree ∨
      ((gradedReverseUnderlying a).degree = (gradedReverseUnderlying b).degree ∧
        toColex (gradedReverseUnderlying b) < toColex (gradedReverseUnderlying a)) := by
  change gradedReverseKey a < gradedReverseKey b ↔ _
  simp only [gradedReverseKey, Prod.Lex.toLex_lt_toLex, OrderDual.toDual_lt_toDual]

theorem gradedReverse_le_iff (a b : GradedReverse V) :
    a ≤ b ↔ (gradedReverseUnderlying a).degree < (gradedReverseUnderlying b).degree ∨
      ((gradedReverseUnderlying a).degree = (gradedReverseUnderlying b).degree ∧
        toColex (gradedReverseUnderlying b) ≤ toColex (gradedReverseUnderlying a)) := by
  change gradedReverseKey a ≤ gradedReverseKey b ↔ _
  simp only [gradedReverseKey, Prod.Lex.toLex_le_toLex, OrderDual.toDual_le_toDual]

instance : IsOrderedAddMonoid (GradedReverse V) where
  add_le_add_left a b h c := by
    rw [gradedReverse_le_iff] at h ⊢
    change (gradedReverseUnderlying a + gradedReverseUnderlying c).degree < (gradedReverseUnderlying b + gradedReverseUnderlying c).degree ∨
      ((gradedReverseUnderlying a + gradedReverseUnderlying c).degree = (gradedReverseUnderlying b + gradedReverseUnderlying c).degree ∧
        toColex (gradedReverseUnderlying b + gradedReverseUnderlying c) ≤ toColex (gradedReverseUnderlying a + gradedReverseUnderlying c))
    simpa only [map_add, toColex_add, add_lt_add_iff_right, add_left_inj,
      add_le_add_iff_right] using h

theorem gradedReverse_degree_mono :
    Monotone (fun a : GradedReverse V => (gradedReverseUnderlying a).degree) := by
  intro a b h
  rcases (gradedReverse_le_iff a b).mp h with h | h
  · exact h.le
  · exact h.1.le

instance : WellFoundedLT (GradedReverse V) := by
  apply WellFounded.wellFoundedLT_iff_exists_minimal.mpr
  intro S hS
  obtain ⟨a, ha⟩ := hS
  let T : Set (GradedReverse V) :=
    {b | b ∈ S ∧ (gradedReverseUnderlying b).degree ≤ (gradedReverseUnderlying a).degree}
  have hfin : T.Finite := by
    change {b : Exponent V | b ∈ S ∧ b.degree ≤ (gradedReverseUnderlying a).degree}.Finite
    apply (Set.finite_Iic (constExponent (gradedReverseUnderlying a).degree)).subset
    intro b hb i
    exact (coordinate_le_degree b i).trans hb.2
  obtain ⟨b, hb, hmin⟩ := hfin.exists_minimal ⟨a, ha, le_rfl⟩
  refine ⟨b, hb.1, ?_⟩
  intro c hc hcb
  exact hmin ⟨hc, (gradedReverse_degree_mono hcb).trans hb.2⟩ hcb

def gradedRevlexMonomialOrder : MonomialOrder V where
  syn := GradedReverse V
  toSyn := gradedReverseEquiv
  toSyn_monotone a b hab := by
    apply (gradedReverse_le_iff _ _).mpr
    have hd := degree_mono hab
    rcases hd.lt_or_eq with hlt | he
    · exact Or.inl hlt
    · have hab' := eq_of_le_of_degree_eq hab he
      exact Or.inr ⟨he, by rw [hab']⟩

end Ordered

def variableGradedRevlexOrder (o : VariableOrder V) : MonomialOrder V :=
  letI := variableLinearOrder o
  gradedRevlexMonomialOrder

theorem variableGradedRevlexOrder_decreasing_iff (o : VariableOrder V)
    (a b : Exponent V) (hd : a.degree = b.degree) :
    (variableGradedRevlexOrder o).toSyn b < (variableGradedRevlexOrder o).toSyn a ↔
      variableRevlex o a b := by
  letI := variableLinearOrder o
  change gradedReverseEquiv b < gradedReverseEquiv a ↔ _
  rw [gradedReverse_lt_iff]
  change (b.degree < a.degree ∨ b.degree = a.degree ∧ toColex a < toColex b) ↔ _
  simp only [hd, lt_self_iff_false, true_and, false_or, Finsupp.Colex.lt_iff]
  exact ⟨fun ⟨i, he, hi⟩ => ⟨i, hi, he⟩, fun ⟨i, hi, he⟩ => ⟨i, he, hi⟩⟩

end Characterizations
