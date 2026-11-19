/- Ordinary matroid semantics for the regular binary signed sums.
The sum criterion depends only on matched input cycles and support, and is
proved to define a unique ordinary Mathlib matroid. -/
module
public import Recovery.Unimodular.ProductVectorMatroid
public import Recovery.Unimodular.PriorExtensions.SignedSumsRegular
public import Recovery.Unimodular.PriorExtensions.SignedSumsBinary
public import Mathlib.Combinatorics.Matroid.Sum
public import Mathlib.Algebra.Field.ZMod
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
namespace Unimodular.SignedSums

/-- Ordinary matroid equality, including every subset of labels, for all fields. -/
theorem tu_matroid_field_invariant {K F I E : Type*} [Field K] [Field F]
    [Fintype I] [Fintype E] (M : Matrix I E ℤ) (hM : M.IsTotallyUnimodular) :
    VectorMatroid.ofFamily (K := K) (fun j i => (M i j : K)) =
      VectorMatroid.ofFamily (K := F) (fun j i => (M i j : F)) := by
  classical
  apply Matroid.ext_indep (by simp)
  intro S hS
  rw [VectorMatroid.ofFamily_indep, VectorMatroid.ofFamily_indep]
  letI : Fintype S := Fintype.ofFinite S
  exact tu_selected_independence_field_invariant M hM (fun j : S => j.val)

namespace Binary

/-- Independence is exactly absence of a nonzero supported binary cycle. -/
theorem indep_iff_supported_cycles {E M : Type*} [Fintype E]
    [AddCommGroup M] [Module F M] (U : E → M) (S : Set E) :
    LinearIndepOn F U S ↔
      ∀ x : E → F, (∀ e, e ∉ S → x e = 0) → Cycle U x → ∀ e, x e = 0 := by
  classical
  let s := S.toFinite.toFinset
  have hs : (s : Set E) = S := Set.Finite.coe_toFinset _
  rw [← hs, linearIndepOn_finset_iff]
  constructor
  · intro h x hx hc e
    by_cases he : e ∈ s
    · apply h x _ e he
      change ∑ i ∈ s, x i • U i = 0
      rw [← hc]
      exact Finset.sum_subset (Finset.subset_univ s) (fun i _ hi => by rw [hx i hi, zero_smul])
    · exact hx e he
  · intro h x hx e he
    let y : E → F := fun i => if i ∈ s then x i else 0
    have hy : ∀ i, i ∉ (s : Set E) → y i = 0 := by
      intro i hi
      change i ∉ s at hi
      simp [y, hi]
    have hc : Cycle U y := by
      simpa [Cycle, y, ite_smul, Finset.sum_filter] using hx
    have hz := h y hy hc e
    simpa [y, he] using hz

/-- The standard matched-cycle independent-set specification of a binary
port sum. It is expressed entirely using the two input representations. -/
def MatchedIndependent {P A B T L R : Type*} [AddCommGroup P] [Module F P]
    [AddCommGroup A] [Module F A] [AddCommGroup B] [Module F B]
    [Fintype T] [Fintype L] [Fintype R]
    (C : T → P) (U : L → P × A) (V : R → P × B) (S : Set (L ⊕ R)) : Prop :=
  ∀ (x : L → F) (y : R → F) (z : T → F),
    (∀ l, Sum.inl l ∉ S → x l = 0) → (∀ r, Sum.inr r ∉ S → y r = 0) →
    Cycle (sideFamily C U) (Sum.elim z x) → Cycle (sideFamily C V) (Sum.elim z y) →
    (∀ l, x l = 0) ∧ ∀ r, y r = 0

/-- A genuine ordinary matroid satisfies the binary sum rule if and only if
all its independent subsets have the matched-cycle specification. -/
def IsPortSum {P A B T L R : Type*} [AddCommGroup P] [Module F P]
    [AddCommGroup A] [Module F A] [AddCommGroup B] [Module F B]
    [Fintype T] [Fintype L] [Fintype R]
    (M : Matroid (L ⊕ R)) (C : T → P) (U : L → P × A) (V : R → P × B) : Prop :=
  M.E = Set.univ ∧ ∀ S, M.Indep S ↔ MatchedIndependent C U V S

/-- The actual joined family realizes this binary sum in an ordinary matroid. -/
theorem joined_matroid_isPortSum {P A B T L R : Type*}
    [AddCommGroup P] [Module F P] [AddCommGroup A] [Module F A]
    [AddCommGroup B] [Module F B] [Fintype T] [Fintype L] [Fintype R]
    (C : T → P) (hC : Submodule.span F (Set.range C) = ⊤)
    (U : L → P × A) (V : R → P × B) :
    IsPortSum (VectorMatroid.ofFamily (K := F) (joinedFamily (R := F) U V)) C U V := by
  refine ⟨by simp, ?_⟩
  intro S
  rw [VectorMatroid.ofFamily_indep, indep_iff_supported_cycles]
  constructor
  · intro h x y z hx hy hu hv
    have hc : Cycle (joinedFamily (R := F) U V) (Sum.elim x y) :=
      (joined_cycle_iff_matched C hC U V x y).mpr ⟨z, hu, hv⟩
    have hz := h (Sum.elim x y) (by
      intro i
      cases i with
      | inl l => exact hx l
      | inr r => exact hy r) hc
    exact ⟨fun l => hz (.inl l), fun r => hz (.inr r)⟩
  · intro h w hw hc
    let x : L → F := fun l => w (.inl l)
    let y : R → F := fun r => w (.inr r)
    have he : Sum.elim x y = w := by funext i; cases i <;> rfl
    obtain ⟨z, hzU, hzV⟩ := (joined_cycle_iff_matched C hC U V x y).mp (by rwa [he])
    obtain ⟨hx, hy⟩ := h x y z (fun l => hw (.inl l)) (fun r => hw (.inr r)) hzU hzV
    intro i
    cases i with
    | inl l => exact hx l
    | inr r => exact hy r

/-- The cycle specification determines the ordinary matroid uniquely. -/
theorem IsPortSum.unique {P A B T L R : Type*}
    [AddCommGroup P] [Module F P] [AddCommGroup A] [Module F A]
    [AddCommGroup B] [Module F B] [Fintype T] [Fintype L] [Fintype R]
    {C : T → P} {U : L → P × A} {V : R → P × B} {M N : Matroid (L ⊕ R)}
    (hM : IsPortSum M C U V) (hN : IsPortSum N C U V) : M = N := by
  apply Matroid.ext_indep (hM.1.trans hN.1.symm)
  intro S hS
  exact (hM.2 S).trans (hN.2 S).symm

theorem triangle_sum_ordinary_matroid {A B L R : Type*}
    [AddCommGroup A] [Module F A] [AddCommGroup B] [Module F B]
    [Fintype L] [Fintype R]
    (U : L → (Fin 2 → F) × A) (V : R → (Fin 2 → F) × B) :
    IsPortSum (VectorMatroid.ofFamily (K := F) (joinedFamily (R := F) U V))
      trianglePort U V := joined_matroid_isPortSum trianglePort triangle_ports_span U V

theorem single_sum_ordinary_matroid {A B L R : Type*}
    [AddCommGroup A] [Module F A] [AddCommGroup B] [Module F B]
    [Fintype L] [Fintype R]
    (U : L → (Fin 1 → F) × A) (V : R → (Fin 1 → F) × B) :
    IsPortSum (VectorMatroid.ofFamily (K := F) (joinedFamily (R := F) U V))
      singlePort U V := joined_matroid_isPortSum singlePort single_ports_span U V

end Binary
end Unimodular.SignedSums
#print axioms Unimodular.SignedSums.tu_matroid_field_invariant
#print axioms Unimodular.SignedSums.Binary.joined_matroid_isPortSum
#print axioms Unimodular.SignedSums.Binary.IsPortSum.unique
#print axioms Unimodular.SignedSums.Binary.triangle_sum_ordinary_matroid
#print axioms Unimodular.SignedSums.Binary.single_sum_ordinary_matroid
