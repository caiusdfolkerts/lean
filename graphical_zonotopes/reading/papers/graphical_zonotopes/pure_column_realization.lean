module

public import Papers.GraphicalZonotopes.BlockPairCoordinates
public import Papers.GraphicalZonotopes.PureGraphModules
public import Papers.GraphicalZonotopes.FiniteSplitting

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators
variable {H : Type*} [Fintype H] [LinearOrder H]

/-- A column is realized by an actual monotone Boolean function. Its entire
essential-variable set is recorded, as is its class in the full response
quotient. -/
def PureRealizable (C : Finset H) (x : PairIn C → ℝ) : Prop :=
  ∃ F : SetFunction H, IsMonotoneBoolean F ∧
    (∀ a ∈ C, Essential F a) ∧
    (∀ a, a ∉ C → ∀ X, F (insert a X) = F X) ∧
    responseClass F = blockClass C x

def pairIndicator {C : Finset H} (A : Finset (PairIn C)) : PairIn C → ℝ :=
  fun e => if e ∈ A then 1 else 0

def starPairs (C : Finset H) (a : H) (B : Finset H) : Finset (PairIn C) :=
  univ.filter (fun e => StarPair a B e.1.1.1 e.1.1.2)

def cliquePairs (C U : Finset H) : Finset (PairIn C) :=
  univ.filter (fun e => e.1.1.1 ∈ U ∧ e.1.1.2 ∈ U)

@[simp] theorem mem_starPairs {C : Finset H} {a : H} {B : Finset H} {e : PairIn C} :
    e ∈ starPairs C a B ↔ StarPair a B e.1.1.1 e.1.1.2 := by
  simp [starPairs]

@[simp] theorem mem_cliquePairs {C U : Finset H} {e : PairIn C} :
    e ∈ cliquePairs C U ↔ e.1.1.1 ∈ U ∧ e.1.1.2 ∈ U := by
  simp [cliquePairs]

theorem pureRealizable_star (C : Finset H) {a : H} {B : Finset H}
    (ha : a ∈ C) (hB : B ⊆ C) (hne : B.Nonempty) (haB : a ∉ B) :
    PureRealizable C (pairIndicator (starPairs C a B)) := by
  obtain ⟨hf,he,hi,hr⟩ := partialStarModule_properties C ha hB hne haB
  refine ⟨partialStarModule C a B,hf,he,hi,?_⟩
  rw [responseClass_eq_coefficientClass,hr]
  apply congrArg coefficientClass
  funext r
  change (if rowClique r=C ∧ StarPair a B r.1.1.1 r.1.1.2 then 1 else 0) =
    if h : rowClique r=C then pairIndicator (starPairs C a B) (pairAtRow C r h) else 0
  by_cases h : rowClique r=C <;> simp [h,pairIndicator,pairAtRow]

theorem pureRealizable_clique (C U : Finset H) (hU : U ⊆ C) (hcard : 2 ≤ U.card) :
    PureRealizable C (pairIndicator (cliquePairs C U)) := by
  obtain ⟨hf,he,hi,hr⟩ := cliqueModule_properties C U hU hcard
  refine ⟨cliqueModule C U,hf,he,hi,?_⟩
  rw [responseClass_eq_coefficientClass,hr]
  apply congrArg coefficientClass
  funext r
  change (if rowClique r=C ∧ r.1.1.1∈U ∧ r.1.1.2∈U then 1 else 0) =
    if h : rowClique r=C then pairIndicator (cliquePairs C U) (pairAtRow C r h) else 0
  by_cases h : rowClique r=C <;> simp [h,pairIndicator,pairAtRow]

theorem blockClass_singleton (C : Finset H) (e : PairIn C) :
    blockClass C (pairIndicator {e}) = pureCoordinate C e.1.1.1 e.1.1.2 := by
  apply congrArg coefficientClass
  funext r
  change (if h : rowClique r=C then pairIndicator {e} (pairAtRow C r h) else 0) =
    if rowClique r=C ∧ r.1.1.1=e.1.1.1 ∧ r.1.1.2=e.1.1.2 then 1 else 0
  by_cases h : rowClique r=C
  · have he : pairAtRow C r h=e ↔ r.1.1.1=e.1.1.1 ∧ r.1.1.2=e.1.1.2 := by
      constructor
      · intro he
        exact ⟨congrArg (fun t : PairIn C => t.1.1.1) he,
          congrArg (fun t : PairIn C => t.1.1.2) he⟩
      · rintro ⟨hu,hv⟩
        apply Subtype.ext
        apply Subtype.ext
        exact Prod.ext hu hv
    simp only [h,dite_true,pairIndicator,mem_singleton,he,true_and]
  · simp only [h,dite_false,false_and,ite_false]

theorem pureRealizable_pair (C : Finset H) (e : PairIn C) :
    PureRealizable C (pairIndicator {e}) := by
  refine ⟨positivePairModule C e.1.1.1 e.1.1.2,
    (positivePairBlocks_family C e.2.1 e.2.2 (ne_of_lt e.1.2.1)).module_boolean,?_,?_,?_⟩
  · exact fun a ha => positivePairModule_essential C e.2.1 e.2.2 (ne_of_lt e.1.2.1) ha
  · exact fun a ha X => complementModule_ignores_outside C _ ha X
  · rw [positivePairModule_class C e.2.1 e.2.2 e.1.2.1,blockClass_singleton]

theorem pureRealizable_negative_pair (C : Finset H) (hC : 3 ≤ C.card) (e : PairIn C) :
    PureRealizable C (-pairIndicator {e}) := by
  refine ⟨negativePairModule C e.1.1.1 e.1.1.2,
    (negativePairBlocks_family C hC e.2.1 e.2.2 (ne_of_lt e.1.2.1)).module_boolean,?_,?_,?_⟩
  · exact fun a ha => negativePairModule_essential C hC e.2.1 e.2.2 (ne_of_lt e.1.2.1) ha
  · exact fun a ha X => complementModule_ignores_outside C _ ha X
  · rw [negativePairModule_class C hC e.2.1 e.2.2 e.1.2.1,map_neg,blockClass_singleton]

/-- Indicator columns of the nonempty parts of a genuine finite partition
are independent. This elementary statement is used before quotienting. -/
theorem linearIndependent_partition_indicators {E : Type*} [DecidableEq E]
    {A : Finset E} (Q : Finpartition A) :
    LinearIndependent ℝ (fun B : Q.parts => fun e : E => if e∈B.1 then (1 : ℝ) else 0) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc B
  obtain ⟨e,he⟩ := nonempty_iff_ne_empty.mpr (Q.ne_bot B.2)
  have hmem : ∀ D : Q.parts, e∈D.1 ↔ D=B := by
    intro D
    constructor
    · intro hD
      apply Subtype.ext
      by_contra hDB
      exact Finset.disjoint_left.mp (Q.disjoint D.2 B.2 hDB) hD he
    · intro hD
      exact hD.symm ▸ he
  have hv := congrFun hc e
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hv
  simp_rw [hmem] at hv
  simpa using hv

theorem sum_partition_indicators {E : Type*} [DecidableEq E]
    {A : Finset E} (Q : Finpartition A) (e : E) :
    (∑ B : Q.parts,if e∈B.1 then (1 : ℝ) else 0) = if e∈A then 1 else 0 := by
  classical
  by_cases he : e∈A
  · obtain ⟨B,hB,heB⟩ := Q.exists_mem he
    have hmem : ∀ D : Q.parts, e∈D.1 ↔ D=⟨B,hB⟩ := by
      intro D
      constructor
      · intro hD
        apply Subtype.ext
        by_contra hDB
        exact Finset.disjoint_left.mp (Q.disjoint D.2 hB hDB) hD heB
      · intro hD
        exact hD.symm ▸ heB
    simp_rw [hmem]
    simp [he]
  · have hmem : ∀ D : Q.parts, e∉D.1 := fun D hD => he ((Q.le D.2) hD)
    simp [hmem,he]

end BooleanModule
end GraphicalZonotopes
