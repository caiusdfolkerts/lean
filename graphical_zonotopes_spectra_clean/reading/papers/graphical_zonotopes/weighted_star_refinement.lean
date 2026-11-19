module

public import Papers.GraphicalZonotopes.PairColumnRefinement
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators
variable {H : Type*} [Fintype H] [LinearOrder H]

structure StarPiece (C : Finset H) where
  center : H
  leaves : Finset H
  center_mem : center∈C
  leaves_subset : leaves⊆C
  nonempty : leaves.Nonempty
  center_notMem : center∉leaves

def StarPiece.edges {C : Finset H} (P : StarPiece C) : Finset (PairIn C) :=
  starPairs C P.center P.leaves

def StarPiece.vector {C : Finset H} (P : StarPiece C) : PairIn C → ℝ :=
  pairIndicator P.edges

def StarPiece.response {C : Finset H} (P : StarPiece C) : ResponseQuotient H :=
  blockClass C P.vector

theorem StarPiece.realizable {C : Finset H} (P : StarPiece C) : PureRealizable C P.vector :=
  pureRealizable_star C P.center_mem P.leaves_subset P.nonempty P.center_notMem

private theorem pairIndicator_union {C : Finset H} {A B : Finset (PairIn C)}
    (h : Disjoint A B) : pairIndicator (A∪B)=pairIndicator A+pairIndicator B := by
  funext e
  by_cases ha : e∈A <;> by_cases hb : e∈B
  · exact False.elim (disjoint_left.mp h ha hb)
  all_goals simp [pairIndicator,ha,hb]

/-- Splitting off an actual pair preserves the class sum and every covered
pair. Both child columns are actual nonempty partial-star modules. -/
theorem StarPiece.split_at {C : Finset H} (P : StarPiece C) (e : PairIn C)
    (he : e∈P.edges) (hne : P.response≠blockClass C (pairIndicator {e})) :
    ∃ L R : StarPiece C,L.response=blockClass C (pairIndicator {e}) ∧
      R.response=P.response-blockClass C (pairIndicator {e}) ∧
      L.edges∪R.edges=P.edges := by
  have he' := mem_starPairs.mp he
  have hex : ∃ b∈P.leaves,starPairs C P.center {b}={e} := by
    rcases he' with ⟨hu,hv⟩ | ⟨hv,hu⟩
    · have hne : P.center≠e.1.1.2 := fun h => P.center_notMem (h.symm ▸ hv)
      have hem : e∈starPairs C P.center {e.1.1.2} := mem_starPairs.mpr (Or.inl ⟨hu,mem_singleton_self _⟩)
      have heq := mem_singleton.mp (starPairs_singleton C hne P.center_mem e.2.2 ▸ hem)
      exact ⟨e.1.1.2,hv,(starPairs_singleton C hne P.center_mem e.2.2).trans
        (congrArg singleton heq.symm)⟩
    · have hne : P.center≠e.1.1.1 := fun h => P.center_notMem (h.symm ▸ hu)
      have hem : e∈starPairs C P.center {e.1.1.1} := mem_starPairs.mpr (Or.inr ⟨hv,mem_singleton_self _⟩)
      have heq := mem_singleton.mp (starPairs_singleton C hne P.center_mem e.2.1 ▸ hem)
      exact ⟨e.1.1.1,hu,(starPairs_singleton C hne P.center_mem e.2.1).trans
        (congrArg singleton heq.symm)⟩
  obtain ⟨b,hb,hpair⟩ := hex
  have hcb : P.center≠b := fun h => P.center_notMem (h.symm ▸ hb)
  have herase : (P.leaves.erase b).Nonempty := by
    by_contra hn
    have he0 : P.leaves.erase b=∅ := not_nonempty_iff_eq_empty.mp hn
    rcases (erase_eq_empty_iff P.leaves b).mp he0 with h | h
    · exact P.nonempty.ne_empty h
    · apply hne
      change blockClass C (pairIndicator (starPairs C P.center P.leaves))=_
      rw [h,hpair]
  let L : StarPiece C := ⟨P.center,{b},P.center_mem,singleton_subset_iff.mpr
    (P.leaves_subset hb),singleton_nonempty _,by simpa only [mem_singleton] using hcb⟩
  let R : StarPiece C := ⟨P.center,P.leaves.erase b,P.center_mem,
    (erase_subset _ _).trans P.leaves_subset,herase,
    fun h => P.center_notMem (mem_of_mem_erase h)⟩
  have hL : L.edges={e} := hpair
  have hdis : Disjoint L.edges R.edges := starPairs_disjoint C P.center
    (B:={b}) (D:=P.leaves.erase b) (disjoint_singleton_left.mpr (notMem_erase b P.leaves))
    (by simpa only [mem_singleton] using hcb) (fun h => P.center_notMem (mem_of_mem_erase h))
  have hcover : L.edges∪R.edges=P.edges := by
    change starPairs C P.center {b}∪starPairs C P.center (P.leaves.erase b)=_
    rw [← starPairs_union,singleton_union,insert_erase hb]
    rfl
  have hsum : L.response+R.response=P.response := by
    change blockClass C (pairIndicator L.edges)+blockClass C (pairIndicator R.edges)=_
    rw [← map_add,← pairIndicator_union hdis,hcover]
    rfl
  have hclass : L.response=blockClass C (pairIndicator {e}) := by
    change blockClass C (pairIndicator L.edges)=_
    rw [hL]
  refine ⟨L,R,hclass,?_,hcover⟩
  rw [← hsum,hclass]
  abel

/-- An independent collection of positive partial stars, with integer scales
bounded by `M`, a prescribed weighted response, and coverage of every pair. -/
structure WeightedStarFamily (C : Finset H) (M : ℤ) (v : ResponseQuotient H) (r : ℕ) where
  piece : Fin r → StarPiece C
  weight : Fin r → ℤ
  positive : ∀ j,0<weight j
  bounded : ∀ j,weight j≤M
  independent : LinearIndependent ℝ (fun j => (piece j).response)
  weighted_sum : (∑ j,(weight j : ℝ) • (piece j).response)=v
  covers : ∀ e : PairIn C,∃ j,e∈(piece j).edges

theorem weightedStarFamily_of_data {C : Finset H} {M : ℤ} {v : ResponseQuotient H}
    {J : Type*} [Fintype J] (P : J → StarPiece C) (w : J → ℤ)
    (hp : ∀ j,0<w j) (hb : ∀ j,w j≤M)
    (hi : LinearIndependent ℝ (fun j => (P j).response))
    (hs : (∑ j,(w j : ℝ) • (P j).response)=v)
    (hc : ∀ e : PairIn C,∃ j,e∈(P j).edges) {r : ℕ} (hr : Fintype.card J=r) :
    Nonempty (WeightedStarFamily C M v r) := by
  classical
  let e : Fin r ≃ J := (finCongr hr.symm).trans (Fintype.equivFin J).symm
  refine ⟨⟨fun i => P (e i),fun i => w (e i),fun i => hp (e i),fun i => hb (e i),
    hi.comp e e.injective,?_,?_⟩⟩
  · exact (e.sum_comp _).trans hs
  · intro x
    obtain ⟨j,hj⟩ := hc x
    exact ⟨e.symm j,by simpa only [e.apply_symm_apply] using hj⟩

/-- One independent rank-increasing split. Positivity, the upper weight
bound, the prescribed weighted response, and complete pair coverage persist. -/
theorem WeightedStarFamily.step {C : Finset H} {M : ℤ} {v : ResponseQuotient H}
    {r : ℕ} (P : WeightedStarFamily C M v r) (e₀ : PairIn C)
    (hr : r<C.card.choose 2-1) : Nonempty (WeightedStarFamily C M v (r+1)) := by
  classical
  obtain ⟨e,he⟩ := exists_pair_outside_span C e₀ (fun j => (P.piece j).response)
    P.independent (by simpa only [Fintype.card_fin] using hr)
  obtain ⟨j₀,hj₀⟩ := P.covers e
  have hne : (P.piece j₀).response≠blockClass C (pairIndicator {e}) := by
    intro h
    exact he (h ▸ Submodule.subset_span ⟨j₀,rfl⟩)
  obtain ⟨L,R,hL,hR,hcov⟩ := (P.piece j₀).split_at e hj₀ hne
  let Q : Option (Fin r) → StarPiece C := fun j => match j with
    | none => L
    | some j => if j=j₀ then R else P.piece j
  let w : Option (Fin r) → ℤ := fun j => Option.casesOn' j (P.weight j₀) P.weight
  have hq : (fun j => (Q j).response)=
      splitColumnFamily (fun j => (P.piece j).response) j₀ (blockClass C (pairIndicator {e})) := by
    funext j
    cases j with
    | none => exact hL
    | some j =>
      by_cases h : j=j₀
      · subst j
        simp only [Q,splitColumnFamily,ite_true,hR]
      · simp only [Q,splitColumnFamily,ite_eq_right h]
  have hi : LinearIndependent ℝ (fun j => (Q j).response) := by
    rw [hq]
    exact splitColumnFamily_independent _ P.independent j₀ _ he
  have hs : (∑ j,(w j : ℝ) • (Q j).response)=v := by
    have hw : (fun j : Option (Fin r) => (w j : ℝ))=
        fun j => Option.casesOn' j (P.weight j₀ : ℝ) (fun i => (P.weight i : ℝ)) := by
      funext j
      cases j <;> rfl
    change (∑ j,(fun i : Option (Fin r) => (w i : ℝ)) j • (fun i => (Q i).response) j)=v
    rw [hw,hq]
    exact (splitColumnFamily_preserves_sum (fun j => (P.piece j).response) j₀
      (blockClass C (pairIndicator {e})) (fun j => (P.weight j : ℝ))).trans P.weighted_sum
  have hc : ∀ f : PairIn C,∃ j,f∈(Q j).edges := by
    intro f
    obtain ⟨j,hj⟩ := P.covers f
    by_cases h : j=j₀
    · subst j
      rw [← hcov,mem_union] at hj
      rcases hj with hj | hj
      · exact ⟨none,hj⟩
      · exact ⟨some j₀,by simpa only [Q,ite_true] using hj⟩
    · exact ⟨some j,by simpa only [Q,ite_eq_right h] using hj⟩
  apply weightedStarFamily_of_data Q w _ _ hi hs hc (by simp)
  · intro j
    cases j with
    | none => exact P.positive j₀
    | some j => exact P.positive j
  · intro j
    cases j with
    | none => exact P.bounded j₀
    | some j => exact P.bounded j

/-- Refinement reaches every intermediate number of columns all the way to
the full quotient dimension. All modules and integer scales are retained. -/
theorem WeightedStarFamily.refine {C : Finset H} {M : ℤ} {v : ResponseQuotient H}
    {r : ℕ} (P : WeightedStarFamily C M v r) (e₀ : PairIn C)
    {k : ℕ} (hlo : r≤k) (hhi : k≤C.card.choose 2-1) :
    Nonempty (WeightedStarFamily C M v k) := by
  induction k, hlo using Nat.le_induction with
  | base => exact ⟨P⟩
  | succ k hk ih =>
    obtain ⟨Q⟩ := ih (by omega)
    exact Q.step e₀ (by omega)

end BooleanModule
end GraphicalZonotopes
