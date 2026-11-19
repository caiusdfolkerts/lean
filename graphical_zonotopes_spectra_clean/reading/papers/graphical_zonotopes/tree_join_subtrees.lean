module

public import Papers.GraphicalZonotopes.TreeJoinInduced

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.TreeJoin
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A connected subgraph of a forest already contains every ambient edge
between its vertices. Thus the word "subtree" does not restrict s₃ to a
smaller class when we represent it as an induced graph. -/
theorem connected_subgraph_eq {W : Type*} {G H : SimpleGraph W}
    (hG : G.IsAcyclic) (hH : H.Connected) (hHG : H≤G) : H=G := by
  have htree : G.IsTree := ⟨hH.mono hHG,hG⟩
  have hmin := SimpleGraph.isTree_iff_minimal_connected.mp htree
  exact le_antisymm hHG (hmin.2 hH hHG)

theorem induced_subcubic_iff_subtree {T : SimpleGraph V} (hT : T.IsAcyclic)
    (U : Finset V) :
    ((subtree T U).IsTree ∧ (subtree T U).maxDegree≤3) ↔
      ∃ H : SimpleGraph U,H≤subtree T U ∧ H.IsTree ∧ H.maxDegree≤3 := by
  constructor
  · rintro ⟨ht,hd⟩
    exact ⟨_,le_rfl,ht,hd⟩
  · rintro ⟨H,hH,ht,hd⟩
    have he := connected_subgraph_eq (hT.induce _) ht.connected hH
    subst H
    exact ⟨ht,hd⟩

def subcubicSubtreeSets (T : SimpleGraph V) : Finset (Finset V) :=
  univ.filter (fun U => (subtree T U).IsTree ∧
    (subtree T U).maxDegree≤3)

/-- The largest number of vertices in a nonempty connected subtree with
maximum degree at most three. `induced_subcubic_iff_subtree` proves that on
a forest this is exactly the maximum over all connected subgraphs. -/
def s3 (T : SimpleGraph V) : ℕ := (subcubicSubtreeSets T).sup Finset.card

theorem subtree_card_le_s3 {T : SimpleGraph V} {U : Finset V}
    (ht : (subtree T U).IsTree) (hd : (subtree T U).maxDegree≤3) :
    U.card≤s3 T := by
  apply le_sup
  exact mem_filter.mpr ⟨mem_univ _,ht,hd⟩

theorem singleton_subtree (T : SimpleGraph V) (v : V) :
    ({v} : Finset V)∈subcubicSubtreeSets T := by
  letI : Nonempty ({v} : Finset V) := ⟨⟨v,by simp⟩⟩
  letI : Subsingleton ({v} : Finset V) := ⟨by
    intro x y
    apply Subtype.ext
    have hx : x.1=v := mem_singleton.mp x.2
    have hy : y.1=v := mem_singleton.mp y.2
    exact hx.trans hy.symm⟩
  exact mem_filter.mpr ⟨mem_univ _,SimpleGraph.IsTree.of_subsingleton,by simp⟩

theorem s3_pos (T : SimpleGraph V) [Nonempty V] : 1≤s3 T := by
  obtain ⟨v⟩ := (inferInstance : Nonempty V)
  have h := le_sup (s := subcubicSubtreeSets T) (f := Finset.card) (singleton_subtree T v)
  simpa only [card_singleton,s3] using h

theorem s3_le_card (T : SimpleGraph V) : s3 T≤Fintype.card V := by
  apply Finset.sup_le_iff.mpr
  intro U hU
  exact card_le_univ U

theorem s3_attained (T : SimpleGraph V) [Nonempty V] :
    ∃ U : Finset V,(subtree T U).IsTree ∧
      (subtree T U).maxDegree≤3 ∧ U.card=s3 T := by
  obtain ⟨v⟩ := (inferInstance : Nonempty V)
  obtain ⟨U,hU,hmax⟩ := (subcubicSubtreeSets T).exists_max_image Finset.card
    ⟨{v},singleton_subtree T v⟩
  obtain ⟨ht,hd⟩ := (mem_filter.mp hU).2
  exact ⟨U,ht,hd,le_antisymm (subtree_card_le_s3 ht hd) (Finset.sup_le_iff.mpr hmax)⟩

theorem s3_eq_card_iff {T : SimpleGraph V} (hT : T.IsTree) :
    s3 T=Fintype.card V ↔ T.maxDegree≤3 := by
  letI : Nonempty V := hT.connected.nonempty
  have hdeg : (subtree T univ).maxDegree=T.maxDegree := by
    exact (subtreeUnivIso T).maxDegree_eq
  constructor
  · intro he
    obtain ⟨U,ht,hd,hcard⟩ := s3_attained T
    have hU : U=univ := eq_univ_of_card U (hcard.trans he)
    subst U
    rwa [hdeg] at hd
  · intro hd
    apply le_antisymm (s3_le_card T)
    have ht : (subtree T univ).IsTree := by
      exact (subtreeUnivIso T).isTree_iff.mpr hT
    have h := subtree_card_le_s3 ht (by rwa [hdeg])
    simpa only [card_univ] using h

end GraphicalZonotopes.TreeJoin
