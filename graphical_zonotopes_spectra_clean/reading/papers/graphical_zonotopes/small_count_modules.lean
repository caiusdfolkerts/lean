module

public import Papers.GraphicalZonotopes.PureResponseClasses
public import Papers.GraphicalZonotopes.IntegralBooleanResponse
public import Papers.GraphicalZonotopes.ResponseBlockHelpers
public import Papers.GraphicalZonotopes.OneBlockCircuit

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
namespace SmallCount
open Finset
open scoped BigOperators Classical
variable {H : Type*} [Fintype H] [LinearOrder H]

def crossingPairs (blocks : Finset (Finset H)) : Finset (OrientedEdge (⊤ : SimpleGraph H)) :=
  univ.filter (fun e => Crosses blocks e.1.1 e.1.2)

@[simp] theorem mem_crossingPairs (blocks : Finset (Finset H))
    (e : OrientedEdge (⊤ : SimpleGraph H)) :
    e∈crossingPairs blocks ↔ Crosses blocks e.1.1 e.1.2 := by
  simp only [crossingPairs,mem_filter,mem_univ,true_and]

abbrev Branch (blocks : Finset (Finset H)) := Option ↥(crossingPairs blocks)

/-- The first outer vertex carries the complete-multipartite response;
every selected pair has its own negative pure-coordinate outer module. -/
def modules (blocks : Finset (Finset H)) : Branch blocks → SetFunction H
  | none => complementModule univ blocks
  | some e => negativePairModule univ e.1.1.1 e.1.1.2

theorem modules_boolean {blocks : Finset (Finset H)}
    (hb : ComplementFamily (univ : Finset H) blocks) (hs : 3≤Fintype.card H) :
    ∀ j,IsMonotoneBoolean (modules blocks j) := by
  intro j
  cases j with
  | none => exact hb.module_boolean
  | some e =>
    exact (negativePairBlocks_family univ (by simpa using hs)
      (mem_univ _) (mem_univ _) (ne_of_lt e.1.2.1)).module_boolean

theorem modules_essential {blocks : Finset (Finset H)}
    (hb : ComplementFamily (univ : Finset H) blocks) (hs : 3≤Fintype.card H) :
    ∀ j a,Essential (modules blocks j) a := by
  intro j a
  cases j with
  | none => exact hb.essential (mem_univ a)
  | some e =>
    exact negativePairModule_essential univ (by simpa using hs)
      (mem_univ _) (mem_univ _) (ne_of_lt e.1.2.1) (mem_univ a)

theorem modules_coefficients {blocks : Finset (Finset H)}
    (hb : ComplementFamily (univ : Finset H) blocks) (hs : 3≤Fintype.card H)
    (j : Branch blocks) :
    rowLowerEquiv.symm (responseVector (modules blocks j))=
      fullBlock (OneBlockCircuit.column (crossingPairs blocks) j) := by
  cases j with
  | none =>
    rw [modules,complementModule_response_coefficients hb]
    funext r
    by_cases hc : rowClique r=univ <;>
      by_cases he : Crosses blocks r.1.1.1 r.1.1.2 <;>
        simp only [fullBlock,OneBlockCircuit.column,mem_crossingPairs,hc,he,
          and_self,true_and,false_and,ite_true,ite_false]
  | some e =>
    rw [modules,negativePairModule_coefficients univ (by simpa using hs)
      (mem_univ _) (mem_univ _) e.1.2.1]
    funext r
    have he : r.1=e.1 ↔ r.1.1.1=e.1.1.1 ∧ r.1.1.2=e.1.1.2 := by
      constructor
      · intro h
        exact ⟨congrArg (fun q : OrientedEdge (⊤ : SimpleGraph H) => q.1.1) h,
          congrArg (fun q : OrientedEdge (⊤ : SimpleGraph H) => q.1.2) h⟩
      · rintro ⟨h₁,h₂⟩
        exact Subtype.ext (Prod.ext h₁ h₂)
    simp only [← he]
    by_cases hc : rowClique r=univ <;> by_cases hp : r.1=e.1 <;>
      simp only [fullBlock,OneBlockCircuit.column,hc,hp,
        true_and,false_and,ite_true,ite_false,not_true_eq_false,not_false_eq_true]

theorem weighted_coefficients {blocks : Finset (Finset H)}
    (hb : ComplementFamily (univ : Finset H) blocks) (hs : 3≤Fintype.card H)
    (t : Branch blocks → ℝ) :
    rowLowerEquiv.symm (weightedResponse (modules blocks) t)=
      fullBlock (OneBlockCircuit.response (crossingPairs blocks) t) := by
  rw [rowLower_symm_weightedResponse]
  simp_rw [modules_coefficients hb hs]
  funext r
  rw [Finset.sum_apply]
  by_cases hc : rowClique r=univ
  · simp only [Pi.smul_apply,smul_eq_mul,fullBlock,if_pos hc,
      OneBlockCircuit.response]
  · simp only [Pi.smul_apply,smul_eq_mul,fullBlock,if_neg hc,mul_zero,sum_const_zero]

/-- All real relations, with no positivity assumption, are exactly the
constant vectors. The unused pair is part of the actual full hub block. -/
theorem integrable_iff_constant {blocks : Finset (Finset H)}
    (hb : ComplementFamily (univ : Finset H) blocks) (hs : 3≤Fintype.card H)
    (hproper : ∃ e : OrientedEdge (⊤ : SimpleGraph H),e∉crossingPairs blocks)
    (t : Branch blocks → ℝ) :
    (∃ z : SetFunction H,TranslationNormalized z ∧ Compatible z (modules blocks) t) ↔
      ∃ c : ℝ,∀ j,t j=c := by
  letI : Nonempty (OrientedEdge (⊤ : SimpleGraph H)):=⟨hproper.choose⟩
  rw [integrable_iff_blockConstant,weighted_coefficients hb hs,
    fullBlock_constant_iff,OneBlockCircuit.constant_response_iff _ hproper]

theorem unit_integrable {blocks : Finset (Finset H)}
    (hb : ComplementFamily (univ : Finset H) blocks) (hs : 3≤Fintype.card H)
    (hproper : ∃ e : OrientedEdge (⊤ : SimpleGraph H),e∉crossingPairs blocks) :
    ∃ z : SetFunction H,TranslationNormalized z ∧
      Compatible z (modules blocks) (fun _ => 1) :=
  (integrable_iff_constant hb hs hproper _).mpr ⟨1,fun _ => rfl⟩

theorem unit_unique {blocks : Finset (Finset H)}
    (hb : ComplementFamily (univ : Finset H) blocks) (hs : 3≤Fintype.card H)
    (hproper : ∃ e : OrientedEdge (⊤ : SimpleGraph H),e∉crossingPairs blocks) :
    UniqueIntegrableRelation (modules blocks) (fun _ => 1) := by
  intro t ht
  obtain ⟨c,hc⟩:=(integrable_iff_constant hb hs hproper t).mp ht
  refine ⟨c,?_⟩
  funext j
  simpa only [Pi.smul_apply,smul_eq_mul,mul_one] using hc j

theorem unit_integral_lift {blocks : Finset (Finset H)}
    (hb : ComplementFamily (univ : Finset H) blocks) (hs : 3≤Fintype.card H)
    (hproper : ∃ e : OrientedEdge (⊤ : SimpleGraph H),e∉crossingPairs blocks) :
    ∃ z : SetFunction H,TranslationNormalized z ∧ IntegerValued z ∧
      Compatible z (modules blocks) (fun _ => 1) := by
  have hrel : (fun _ : Branch blocks => (1 : ℝ))∈
      LinearMap.ker (quotientRelation (modules blocks)) :=
    (mem_quotientRelation_ker_iff _ _).mpr (unit_integrable hb hs hproper)
  simpa only [Int.cast_one] using integral_compatible_lift
    (modules blocks) (modules_boolean hb hs) (fun _ => (1 : ℤ))
    (by simpa only [Int.cast_one] using hrel)

end SmallCount
end BooleanModule
end GraphicalZonotopes
