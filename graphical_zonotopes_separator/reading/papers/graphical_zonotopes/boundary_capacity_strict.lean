module

public import Papers.GraphicalZonotopes.BoundaryContexts

/-! # Strict maximality of complete-graph boundary capacity

This is Lemma 7.13. Missing cliques inject into missing boundary rows;
when there are at least three vertices an additional missing row proves
strictness. The proof counts the actual boundary contexts used by the
separator theorem.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.BoundaryCapacity
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [LinearOrder V]
local instance : DecidableEq V := LinearOrder.toDecidableEq

abbrev TopContext (V : Type*) [Fintype V] [LinearOrder V] :=
  BoundaryContext (⊤ : SimpleGraph V)

def Valid (G : SimpleGraph V) (r : TopContext V) : Prop :=
  G.Adj r.1.1.1 r.1.1.2 ∧ r.2.1 ⊆ commonNeighbors G r.1.1.1 r.1.1.2

abbrev MissingRow (G : SimpleGraph V) := {r : TopContext V // ¬Valid G r}
abbrev MissingClique (G : SimpleGraph V) :=
  {C : CliqueIndex (⊤ : SimpleGraph V) // ¬G.IsClique C.1}

def contextSet (r : TopContext V) : Finset V := insert r.1.1.1 (insert r.1.1.2 r.2.1)

def contextOfPair (C : Finset V) (u v : V) (huv : u<v) : TopContext V :=
  ⟨⟨(u,v),huv,by simpa only [SimpleGraph.top_adj] using ne_of_lt huv⟩,
    ⟨(C.erase u).erase v,mem_powerset.mpr (by
      intro w hw
      simp only [mem_erase] at hw
      simp only [mem_commonNeighbors,SimpleGraph.top_adj]
      exact ⟨Ne.symm hw.2.1,Ne.symm hw.1⟩)⟩⟩

theorem contextSet_pair (C : Finset V) (u v : V) (huv : u<v)
    (hu : u∈C) (hv : v∈C) : contextSet (contextOfPair C u v huv)=C := by
  ext w
  simp only [contextSet,contextOfPair,mem_insert,mem_erase]
  constructor
  · rintro (rfl|rfl|⟨hwv,hwu,hw⟩)
    · exact hu
    · exact hv
    · exact hw
  · intro hw
    by_cases hwu : w=u
    · exact Or.inl hwu
    · by_cases hwv : w=v
      · exact Or.inr (Or.inl hwv)
      · exact Or.inr (Or.inr ⟨hwv,hwu,hw⟩)

theorem missing_pair (G : SimpleGraph V) (C : MissingClique G) :
    ∃ u∈C.1.1,∃ v∈C.1.1,u<v ∧ ¬G.Adj u v := by
  by_contra hn
  apply C.2
  intro u hu v hv huv
  by_contra hnon
  apply hn
  rcases lt_or_gt_of_ne huv with hlt|hgt
  · exact ⟨u,hu,v,hv,hlt,hnon⟩
  · exact ⟨v,hv,u,hu,hgt,fun h => hnon (G.adj_symm h)⟩

noncomputable def missingLeft (G : SimpleGraph V) (C : MissingClique G) : V :=
  (missing_pair G C).choose
noncomputable def missingRight (G : SimpleGraph V) (C : MissingClique G) : V :=
  (missing_pair G C).choose_spec.2.choose

theorem missingLeft_mem (G : SimpleGraph V) (C : MissingClique G) : missingLeft G C∈C.1.1 :=
  (missing_pair G C).choose_spec.1

theorem missingRight_mem (G : SimpleGraph V) (C : MissingClique G) : missingRight G C∈C.1.1 :=
  (missing_pair G C).choose_spec.2.choose_spec.1

theorem missing_lt (G : SimpleGraph V) (C : MissingClique G) : missingLeft G C < missingRight G C :=
  (missing_pair G C).choose_spec.2.choose_spec.2.1

theorem missing_nonadj (G : SimpleGraph V) (C : MissingClique G) :
    ¬G.Adj (missingLeft G C) (missingRight G C) :=
  (missing_pair G C).choose_spec.2.choose_spec.2.2

def missingInjection (G : SimpleGraph V) (C : MissingClique G) : MissingRow G :=
  ⟨contextOfPair C.1.1 (missingLeft G C) (missingRight G C) (missing_lt G C),
    fun h => missing_nonadj G C h.1⟩

@[simp] theorem contextSet_missingInjection (G : SimpleGraph V) (C : MissingClique G) :
    contextSet (missingInjection G C).1=C.1.1 :=
  contextSet_pair _ _ _ (missing_lt G C) (missingLeft_mem G C) (missingRight_mem G C)

theorem missingInjection_injective (G : SimpleGraph V) : Function.Injective (missingInjection G) := by
  intro C D he
  apply Subtype.ext
  apply Subtype.ext
  have h := congrArg (fun r : MissingRow G => contextSet r.1) he
  simpa only [contextSet_missingInjection] using h

theorem top_not_clique (G : SimpleGraph V) (hG : G≠⊤) : ¬G.IsClique (univ : Finset V) := by
  intro h
  apply hG
  apply SimpleGraph.ext
  funext u v
  apply propext
  constructor
  · intro h
    exact (SimpleGraph.top_adj _ _).mpr h.ne
  · intro huv
    exact h (mem_univ _) (mem_univ _) ((SimpleGraph.top_adj _ _).mp huv)

def fullMissingClique (G : SimpleGraph V) (hn : 3≤Fintype.card V) (hG : G≠⊤) : MissingClique G :=
  ⟨⟨univ,by simp only [IsCliqueCoordinate,card_univ]; exact ⟨by omega,fun u hu v hv huv => huv⟩⟩,
    top_not_clique G hG⟩

theorem exists_third (hn : 3≤Fintype.card V) (u v : V) : ∃ w : V,w≠u ∧ w≠v := by
  by_contra h
  push_neg at h
  have he : (univ : Finset V)⊆{u,v} := by
    intro w hw
    by_cases hwu : w=u
    · simp [hwu]
    · simp [h w hwu]
  have hc := card_le_card he
  have hp : ({u,v} : Finset V).card≤2 := by exact card_insert_le _ _ |>.trans (by simp)
  simp only [card_univ] at hc
  omega

/-- Every proper graph has strictly more missing contexts than missing
cliques when the vertex set has cardinality at least three. -/
theorem missing_card_lt (G : SimpleGraph V) (hn : 3≤Fintype.card V) (hG : G≠⊤) :
    Fintype.card (MissingClique G)<Fintype.card (MissingRow G) := by
  apply Fintype.card_lt_of_injective_not_surjective (missingInjection G) (missingInjection_injective G)
  intro hsurj
  let C := fullMissingClique G hn hG
  let u := missingLeft G C
  let v := missingRight G C
  have huv : u<v := missing_lt G C
  have hnon : ¬G.Adj u v := missing_nonadj G C
  obtain ⟨w,hwu,hwv⟩ := exists_third hn u v
  have huC : u∈(univ : Finset V) := mem_univ _
  have hwC : w∈(univ : Finset V) := mem_univ _
  rcases lt_or_gt_of_ne (Ne.symm hwu) with huw|hwu'
  · let r := contextOfPair univ u w huw
    have hr : ¬Valid G r := by
      intro hr
      have hvS : v∈r.2.1 := by simp [r,contextOfPair,ne_of_gt huv,Ne.symm hwv]
      have hvN := hr.2 hvS
      exact hnon ((mem_commonNeighbors _ _ _ _).mp hvN).1
    obtain ⟨D,hD⟩ := hsurj ⟨r,hr⟩
    have hDC : D=C := by
      apply Subtype.ext
      apply Subtype.ext
      have h := congrArg (fun a : MissingRow G => contextSet a.1) hD
      simpa only [contextSet_missingInjection,r,C,fullMissingClique,
        contextSet_pair univ u w huw huC hwC] using h
    subst D
    have he := congrArg (fun a : MissingRow G => a.1.1.1.2) hD
    change v=w at he
    exact hwv he.symm
  · let r := contextOfPair univ w u hwu'
    have hr : ¬Valid G r := by
      intro hr
      have hvS : v∈r.2.1 := by simp [r,contextOfPair,ne_of_gt huv,Ne.symm hwv]
      have hvN := hr.2 hvS
      exact hnon ((mem_commonNeighbors _ _ _ _).mp hvN).2
    obtain ⟨D,hD⟩ := hsurj ⟨r,hr⟩
    have hDC : D=C := by
      apply Subtype.ext
      apply Subtype.ext
      have h := congrArg (fun a : MissingRow G => contextSet a.1) hD
      simpa only [contextSet_missingInjection,r,C,fullMissingClique,
        contextSet_pair univ w u hwu' hwC huC] using h
    subst D
    have he := congrArg (fun a : MissingRow G => a.1.1.1.1) hD
    change u=w at he
    exact hwu he.symm

def validContextEquiv (G : SimpleGraph V) :
    BoundaryContext G ≃ {r : TopContext V // Valid G r} where
  toFun r := ⟨⟨⟨r.1.1,r.1.2.1,by simpa only [SimpleGraph.top_adj] using r.1.2.2.ne⟩,
    ⟨r.2.1,mem_powerset.mpr (by
      intro w hw
      have h := (mem_commonNeighbors _ _ _ _).mp ((mem_powerset.mp r.2.2) hw)
      simpa only [mem_commonNeighbors,SimpleGraph.top_adj] using And.intro h.1.ne h.2.ne)⟩⟩,
    r.1.2.2,mem_powerset.mp r.2.2⟩
  invFun r := ⟨⟨r.1.1.1,r.1.1.2.1,r.2.1⟩,⟨r.1.2.1,mem_powerset.mpr r.2.2⟩⟩
  left_inv r := by cases r; rfl
  right_inv r := by cases r; rfl

def validCliqueEquiv (G : SimpleGraph V) :
    CliqueIndex G ≃ {C : CliqueIndex (⊤ : SimpleGraph V) // G.IsClique C.1} where
  toFun C := ⟨⟨C.1,C.2.1,fun u hu v hv huv => huv⟩,C.2.2⟩
  invFun C := ⟨C.1.1,C.1.2.1,C.2⟩
  left_inv C := rfl
  right_inv C := rfl

/-- The complete graph uniquely maximizes m(G)-d(G), exactly for the
actual boundary-row and clique-coordinate counts of Lemma 7.13. -/
theorem proper_capacity_lt (G : SimpleGraph V) (hn : 3≤Fintype.card V) (hG : G≠⊤) :
    Fintype.card (BoundaryContext G)-Fintype.card (CliqueIndex G)<
      Fintype.card (BoundaryContext (⊤ : SimpleGraph V))-
        Fintype.card (CliqueIndex (⊤ : SimpleGraph V)) := by
  have h := missing_card_lt G hn hG
  have hr : Fintype.card (MissingRow G)=
      Fintype.card (TopContext V)-Fintype.card (BoundaryContext G) := by
    rw [Fintype.card_subtype_compl,←Fintype.card_congr (validContextEquiv G)]
  have hc : Fintype.card (MissingClique G)=
      Fintype.card (CliqueIndex (⊤ : SimpleGraph V))-Fintype.card (CliqueIndex G) := by
    rw [Fintype.card_subtype_compl,←Fintype.card_congr (validCliqueEquiv G)]
  rw [hr,hc] at h
  have hmr : Fintype.card (BoundaryContext G)≤Fintype.card (TopContext V) := by
    rw [Fintype.card_congr (validContextEquiv G)]
    exact Fintype.card_subtype_le _
  have hmc : Fintype.card (CliqueIndex G)≤Fintype.card (CliqueIndex (⊤ : SimpleGraph V)) := by
    rw [Fintype.card_congr (validCliqueEquiv G)]
    exact Fintype.card_subtype_le _
  have hle := clique_count_le_boundary_context_count G
  have htop := clique_count_le_boundary_context_count (⊤ : SimpleGraph V)
  change Fintype.card (CliqueIndex (⊤ : SimpleGraph V))-Fintype.card (CliqueIndex G)<
      Fintype.card (BoundaryContext (⊤ : SimpleGraph V))-Fintype.card (BoundaryContext G) at h
  change Fintype.card (BoundaryContext G)≤Fintype.card (BoundaryContext (⊤ : SimpleGraph V)) at hmr
  omega

end GraphicalZonotopes.BoundaryCapacity
