module

public import Recovery.Unimodular.PriorExtensions.BinaryMatroidCycles
public import Recovery.Unimodular.PriorExtensions.SignedSumsMatroid
public import Continuation.Seymour.R12.VectorClosure

@[expose] public section

/-!
# Intrinsic ordinary binary port sums

The complete declarations below are extracted from the ordinary-matroid
prefix of `PriorExtensions/SignedSumsFaithful.lean`. Only the unrelated
integral quotient-lattice applications are omitted. The closure interface
is the already proved ordinary vector-matroid closure theorem.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Unimodular.SignedSums

/-- Every finite subset is the support of a binary coefficient function. -/
theorem binary_support_indicator {E : Type*} [Fintype E] [DecidableEq E] (S : Finset E) :
    Binary.support (fun e => if e ∈ S then (1 : Binary.F) else 0) = S := by
  ext e
  by_cases he : e ∈ S <;> simp [Binary.support, he]

/-- Binary support loses no information because the only nonzero coefficient
is one. This makes the support formulation identical to a subset formulation. -/
theorem binary_support_injective {E : Type*} [Fintype E] [DecidableEq E] :
    Function.Injective (Binary.support (E := E)) := by
  intro x y h
  funext e
  have he : (x e ≠ 0) ↔ (y e ≠ 0) := by
    simpa only [Binary.mem_support] using Eq.to_iff (congrArg (fun S : Finset E => e ∈ S) h)
  rcases Binary.value_zero_or_one (x e) with hx | hx <;>
    rcases Binary.value_zero_or_one (y e) with hy | hy <;>
    simp_all

/-- The independent-set rule of a binary port sum, using only the two
ordinary input matroids and their intrinsic finite circuit unions. Shared
port supports cancel by literal symmetric difference (SignedSumsSupport). -/
def IntrinsicPortIndependent {T L R : Type*} [Fintype T] [Fintype L] [Fintype R]
    (M₁ : Matroid (T ⊕ L)) (M₂ : Matroid (T ⊕ R)) (S : Set (L ⊕ R)) : Prop := by
  classical
  exact ∀ (x : L → Binary.F) (y : R → Binary.F) (z : T → Binary.F),
    (∀ l, Sum.inl l ∉ S → x l = 0) → (∀ r, Sum.inr r ∉ S → y r = 0) →
    BinaryMatroidCycles.DisjointCircuitUnion M₁ (Binary.support (Sum.elim z x)) →
    BinaryMatroidCycles.DisjointCircuitUnion M₂ (Binary.support (Sum.elim z y)) →
    (∀ l, x l = 0) ∧ ∀ r, y r = 0

/-- This specifies an ordinary matroid by exactly its independent subsets.
No output representation or lattice property is included in the criterion. -/
def IsOrdinaryPortSum {T L R : Type*} [Fintype T] [Fintype L] [Fintype R]
    (M : Matroid (L ⊕ R)) (M₁ : Matroid (T ⊕ L)) (M₂ : Matroid (T ⊕ R)) : Prop :=
  M.E = Set.univ ∧ ∀ S, M.Indep S ↔ IntrinsicPortIndependent M₁ M₂ S

theorem IsOrdinaryPortSum.unique {T L R : Type*} [Fintype T] [Fintype L] [Fintype R]
    {M N : Matroid (L ⊕ R)} {M₁ : Matroid (T ⊕ L)} {M₂ : Matroid (T ⊕ R)}
    (hM : IsOrdinaryPortSum M M₁ M₂) (hN : IsOrdinaryPortSum N M₁ M₂) : M = N := by
  apply Matroid.ext_indep (hM.1.trans hN.1.symm)
  intro S hS
  exact (hM.2 S).trans (hN.2 S).symm

/-- The coefficient sum rule is exactly the intrinsic ordinary matroid rule;
equality of the two input matroids is sufficient, with no chosen realization
hidden in the conclusion. -/
theorem ordinaryPortSum_of_isPortSum {P A B T L R : Type*}
    [AddCommGroup P] [Module Binary.F P] [AddCommGroup A] [Module Binary.F A]
    [AddCommGroup B] [Module Binary.F B] [Fintype T] [Fintype L] [Fintype R]
    {C : T → P} {U : L → P × A} {V : R → P × B} {M : Matroid (L ⊕ R)}
    {M₁ : Matroid (T ⊕ L)} {M₂ : Matroid (T ⊕ R)}
    (hM : Binary.IsPortSum M C U V)
    (h₁ : M₁ = VectorMatroid.ofFamily (K := Binary.F) (Binary.sideFamily C U))
    (h₂ : M₂ = VectorMatroid.ofFamily (K := Binary.F) (Binary.sideFamily C V)) :
    IsOrdinaryPortSum M M₁ M₂ := by
  classical
  refine ⟨hM.1, fun S => (hM.2 S).trans ?_⟩
  unfold Binary.MatchedIndependent IntrinsicPortIndependent
  rw [h₁, h₂]
  simp_rw [← BinaryMatroidCycles.cycle_iff_disjointCircuitUnion]

theorem ofFamily_mem_closure_iff {K E V : Type*} [Field K]
    [AddCommGroup V] [Module K V] (v : E → V) (S : Set E) (e : E) :
    e ∈ (VectorMatroid.ofFamily (K := K) v).closure S ↔
      v e ∈ Submodule.span K (v '' S) :=
  SeymourCovectors.ofFamily_mem_closure_iff v S e

/-- The paper's linear non-coloop criterion is exactly ordinary Matroid.IsColoop. -/
theorem ofFamily_isColoop_iff {K E V : Type*} [Field K]
    [AddCommGroup V] [Module K V] (v : E → V) (e : E) :
    (VectorMatroid.ofFamily (K := K) v).IsColoop e ↔
      v e ∉ Submodule.span K (v '' {f | f ≠ e}) := by
  rw [Matroid.isColoop_iff_notMem_closure_compl (by simp), ofFamily_mem_closure_iff]
  have he : (Set.univ : Set E) \ {e} = {f | f ≠ e} := by ext f; simp
  simp only [VectorMatroid.ofFamily_ground, he]


end Unimodular.SignedSums
#print axioms Unimodular.SignedSums.ordinaryPortSum_of_isPortSum
