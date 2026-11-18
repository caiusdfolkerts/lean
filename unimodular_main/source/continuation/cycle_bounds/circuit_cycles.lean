module

public import Continuation.CycleBounds.CircuitPaths
public import Continuation.CycleBounds.GraphWallBound
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-! # Exact signed cycle coordinates for every nonloop incidence circuit -/

noncomputable section
open scoped BigOperators Matroid
namespace Unimodular.CycleBounds
open SeriesParallel SeriesParallel.IncidenceGraph
attribute [local instance] Classical.propDecidable
variable {V E : Type*}

/-- An oriented traversal of a genuine simple cycle, retaining each multigraph
edge label. The signs express precisely the chosen incidence orientations. -/
structure SignedCycle (G : IncidenceGraph V E) where
  length : ℕ
  positive : 0 < length
  vertices : Fin length → V
  edges : Fin length → E
  signs : Fin length → ℤ
  word : CycleWord G (List.ofFn vertices)
  injective : Function.Injective edges
  oriented : ∀ i, edges i ∈ G.edges ∧
    ((signs i = 1 ∧ G.source (edges i) = vertices i ∧
        G.target (edges i) = vertices (finRotate length i)) ∨
     (signs i = -1 ∧ G.source (edges i) = vertices (finRotate length i) ∧
        G.target (edges i) = vertices i))

namespace SignedCycle
variable {G : IncidenceGraph V E} (c : SignedCycle G)

theorem signs_unit (i : Fin c.length) : c.signs i = 1 ∨ c.signs i = -1 :=
  ((c.oriented i).2).elim (fun h ↦ Or.inl h.1) (fun h ↦ Or.inr h.1)

theorem signed_column (i : Fin c.length) :
    (c.signs i : ℝ) • G.column (c.edges i) =
      vertex (c.vertices i) - vertex (c.vertices (finRotate c.length i)) := by
  rcases (c.oriented i).2 with ⟨hε, hs, ht⟩ | ⟨hε, hs, ht⟩
  · simp [column, hε, hs, ht]
  · simp [column, hε, hs, ht]

/-- The signed incidence relation follows by cancellation around the whole cycle. -/
theorem relation : ∑ i, (c.signs i : ℝ) • G.column (c.edges i) = 0 := by
  simp_rw [c.signed_column]
  have hr : (∑ i, vertex (c.vertices (finRotate c.length i))) =
      ∑ i, vertex (c.vertices i) :=
    Fintype.sum_equiv (finRotate c.length) _ _ (fun _ ↦ rfl)
  rw [Finset.sum_sub_distrib, hr, sub_self]

theorem range_not_indep : ¬G.cycleMatroid.Indep (Set.range c.edges) := by
  intro hi
  have hli := ((VectorMatroid.onSet_indep _ _ _).mp hi).2
  have hli' : LinearIndependent ℝ (G.column ∘ c.edges) := by
    apply linearIndepOn_univ_iff.mp
    apply LinearIndepOn.comp_of_image (f := c.edges) _ c.injective.injOn
    simpa only [Set.image_univ] using hli
  have hz := (Fintype.linearIndependent_iff.mp hli') (fun i ↦ (c.signs i : ℝ)) c.relation
  let i : Fin c.length := ⟨0, c.positive⟩
  rcases c.signs_unit i with h | h <;> simpa [h] using hz i

/-- Any genuine circuit containing the cycle has exactly its labels. -/
theorem range_eq_circuit {C : Set E} (hC : G.cycleMatroid.IsCircuit C)
    (hsub : Set.range c.edges ⊆ C) : Set.range c.edges = C :=
  hC.eq_of_not_indep_subset c.range_not_indep hsub

end SignedCycle

/-- A simple path together with a specified closing edge gives signed cycle
coordinates, with coefficient +1 at the closing edge. -/
theorem exists_signedCycle_of_path (G : IncidenceGraph V E) {C : Set E}
    (hC : C ⊆ G.edges) (e : E) (he : e ∈ G.edges)
    (hne : G.source e ≠ G.target e)
    (p : (supportGraph G (C \ {e})).Walk (G.target e) (G.source e)) (hp : p.IsPath) :
    ∃ c : SignedCycle G, Set.range c.edges ⊆ insert e C ∧
      ∃ i, c.edges i = e ∧ c.signs i = 1 := by
  let k := p.length
  let v : Fin (k + 1) → V := fun i ↦ p.getVert i.val
  have hv : Function.Injective v := by
    intro i j hij
    apply Fin.ext
    exact hp.getVert_injOn (Nat.le_of_lt_succ i.isLt) (Nat.le_of_lt_succ j.isLt) hij
  have hchoose : ∀ i : Fin k, ∃ f : E, ∃ ε : ℤ, f ∈ C \ {e} ∧
      ((ε = 1 ∧ G.source f = v i.castSucc ∧ G.target f = v i.succ) ∨
       (ε = -1 ∧ G.source f = v i.succ ∧ G.target f = v i.castSucc)) := by
    intro i
    obtain ⟨_, f, hf, hor⟩ := p.adj_getVert_succ i.isLt
    rcases hor with h | h
    · exact ⟨f, 1, hf, Or.inl ⟨rfl, h.1, h.2⟩⟩
    · exact ⟨f, -1, hf, Or.inr ⟨rfl, h.1, h.2⟩⟩
  choose f ε hf hor using hchoose
  have hfij : Function.Injective f := by
    intro i j heq
    rcases hor i with ⟨_, his, hit⟩ | ⟨_, his, hit⟩ <;>
      rcases hor j with ⟨_, hjs, hjt⟩ | ⟨_, hjs, hjt⟩
    · have hh := hv (his.symm.trans ((congrArg G.source heq).trans hjs))
      exact Fin.castSucc_injective k hh
    · have h₁ := congrArg Fin.val (hv (his.symm.trans ((congrArg G.source heq).trans hjs)))
      have h₂ := congrArg Fin.val (hv (hit.symm.trans ((congrArg G.target heq).trans hjt)))
      simp only [Fin.val_castSucc, Fin.val_succ] at h₁ h₂
      omega
    · have h₁ := congrArg Fin.val (hv (his.symm.trans ((congrArg G.source heq).trans hjs)))
      have h₂ := congrArg Fin.val (hv (hit.symm.trans ((congrArg G.target heq).trans hjt)))
      simp only [Fin.val_castSucc, Fin.val_succ] at h₁ h₂
      omega
    · have hh := hv (hit.symm.trans ((congrArg G.target heq).trans hjt))
      exact Fin.castSucc_injective k hh
  let edges : Fin (k + 1) → E := Fin.snoc f e
  let signs : Fin (k + 1) → ℤ := Fin.snoc ε 1
  have heinj : Function.Injective edges := by
    intro i j hij
    induction i using Fin.lastCases <;> induction j using Fin.lastCases
    · rfl
    · exact ((hf _).2 (by simpa [edges] using hij.symm)).elim
    · exact ((hf _).2 (by simpa [edges] using hij)).elim
    · apply congrArg Fin.castSucc
      apply hfij
      simpa [edges] using hij
  have hword : List.ofFn v = p.support := by
    apply List.ext_getElem
    · simp [v, k, p.length_support]
    · intro i hi hj
      simp only [List.getElem_ofFn]
      exact p.getVert_eq_support_getElem (by simp only [List.length_ofFn] at hi; exact Nat.le_of_lt_succ hi)
  have hrot (i : Fin k) : finRotate (k + 1) i.castSucc = i.succ := finRotate_of_lt i.isLt
  let cycle : SignedCycle G :=
    { length := k + 1
      positive := Nat.succ_pos _
      vertices := v
      edges := edges
      signs := signs
      word := by
        rw [hword]
        exact cycleWord_of_path G (Set.sdiff_subset.trans hC) e he hne p hp
      injective := heinj
      oriented := by
        intro i
        induction i using Fin.lastCases
        · exact ⟨by simpa [edges] using he, Or.inl ⟨by simp [signs], by simp [edges, v, k],
            by simp [edges, v, finRotate_last]⟩⟩
        · rename_i i
          exact ⟨by simpa [edges] using hC (hf i).1, by simpa [edges, signs, hrot] using hor i⟩ }
  refine ⟨cycle, ?_, Fin.last k, ?_, ?_⟩
  · rintro _ ⟨i, rfl⟩
    induction i using Fin.lastCases
    · simp [cycle, edges]
    · rename_i i
      simpa [cycle, edges] using Set.mem_insert_of_mem e (hf i).1
  · simp [cycle, edges]
  · simp [cycle, signs]

/-- Every nonloop circuit is exactly the edge set of an actual signed simple
cycle, with a prescribed edge oriented with coefficient +1. -/
theorem circuit_signed_cycle [Fintype V] (G : IncidenceGraph V E) {C : Set E}
    (hC : G.cycleMatroid.IsCircuit C) {e : E} (he : e ∈ C)
    (hne : G.source e ≠ G.target e) :
    ∃ c : SignedCycle G, Set.range c.edges = C ∧
      ∃ i, c.edges i = e ∧ c.signs i = 1 := by
  obtain ⟨p, hp⟩ := circuit_exists_path G hC he
  obtain ⟨c, hc, i, hie, hiε⟩ := exists_signedCycle_of_path G hC.subset_ground e
    (hC.subset_ground he) hne p hp
  have hsub : Set.range c.edges ⊆ C := hc.trans (Set.insert_subset he Set.Subset.rfl)
  exact ⟨c, c.range_eq_circuit hC hsub, i, hie, hiε⟩

#print axioms circuit_signed_cycle
end Unimodular.CycleBounds
