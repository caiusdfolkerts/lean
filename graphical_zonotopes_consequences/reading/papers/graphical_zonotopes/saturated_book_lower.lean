module

public import Papers.GraphicalZonotopes.SaturatedSeparatorBounds
public import Papers.GraphicalZonotopes.BookIntervalArithmetic

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.SaturatedDirections
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
local instance {V : Type*} [LinearOrder V] : DecidableEq V := LinearOrder.toDecidableEq

variable {s k : ℕ}
abbrev Vertex (s k : ℕ) := Fin s ⊕ Fin k
local instance vertexOrder (s k : ℕ) : LinearOrder (Vertex s k) :=
  inferInstanceAs (LinearOrder (Fin s ⊕ₗ Fin k))
local instance vertexDecidableEq (s k : ℕ) : DecidableEq (Vertex s k) :=
  (vertexOrder s k).toDecidableEq

def bookPartition {H : SimpleGraph (Vertex s k)} (hH : H ≤ cliqueBook s k) :
    Separator.Partition H (BookDimension.boundary s k) (BookDimension.privatePart s k) where
  boundary_disjoint := (BookDimension.partition s k).boundary_disjoint
  private_disjoint := (BookDimension.partition s k).private_disjoint
  cover := (BookDimension.partition s k).cover
  no_cross_edge := fun i j u v hu hv hadj =>
    (BookDimension.partition s k).no_cross_edge i j u v hu hv (hH hadj)

/-- At separator saturation no hub edge can be missing. -/
theorem hubs_clique (hs : 3 ≤ s) {H : SimpleGraph (Vertex s (cliqueCapacity s))}
    (hH : H ≤ cliqueBook s (cliqueCapacity s))
    (z : graphicalFunctionSpace H) (hz : ExtremeSupermodular z.1)
    (hd : FullDimension (basePolytope z.1)) : H.IsClique (BookDimension.boundary s (cliqueCapacity s)) := by
  by_contra hnon
  have hb := Separator.full_partition_capacity
    (by simp only [Fintype.card_sum,Fintype.card_fin]; omega)
    (bookPartition hH) (fun j => singleton_nonempty _) z hz hd
  have hstrict := Separator.proper_boundary_capacity_lt H
    (BookDimension.boundary s (cliqueCapacity s))
    (by simpa only [BookDimension.boundary_card] using hs) hnon
  rw [BookDimension.boundary_card] at hstrict
  simp only [Fintype.card_fin] at hb
  omega

def outerNeighbors (H : SimpleGraph (Vertex s k)) (i : Fin s) : Finset (Fin k) :=
  univ.filter (fun j => H.Adj (.inl i) (.inr j))

def outerNonneighbors (H : SimpleGraph (Vertex s k)) (i : Fin s) : Finset (Fin k) :=
  univ.filter (fun j => ¬H.Adj (.inl i) (.inr j))

def smallerBoundary (i : Fin s) : Finset (Vertex s k) :=
  (BookDimension.boundary s k).erase (.inl i)

def hubPrivate (H : SimpleGraph (Vertex s k)) (i : Fin s) :
    Option {j : Fin k // ¬H.Adj (.inl i) (.inr j)} → Finset (Vertex s k)
  | none => insert (.inl i) ((outerNeighbors H i).image Sum.inr)
  | some j => {Sum.inr j.1}

@[simp] theorem mem_outerNeighbors (H : SimpleGraph (Vertex s k)) (i : Fin s) (j : Fin k) :
    j ∈ outerNeighbors H i ↔ H.Adj (.inl i) (.inr j) := by
  simp only [outerNeighbors,mem_filter,mem_univ,true_and]

theorem hubPrivate_nonempty (H : SimpleGraph (Vertex s k)) (i : Fin s)
    (j : Option {j : Fin k // ¬H.Adj (.inl i) (.inr j)}) : (hubPrivate H i j).Nonempty := by
  cases j with
  | none => exact insert_nonempty _ _
  | some j => exact singleton_nonempty _

@[simp] theorem mem_smallerBoundary (i : Fin s) (v : Vertex s k) :
    v ∈ smallerBoundary (k := k) i ↔ ∃ a : Fin s,a ≠ i ∧ v = .inl a := by
  simp only [smallerBoundary,mem_erase,BookDimension.boundary,mem_image,mem_univ,true_and]
  constructor
  · rintro ⟨hne,a,rfl⟩
    exact ⟨a,fun h => hne (congrArg Sum.inl h),rfl⟩
  · rintro ⟨a,hai,rfl⟩
    exact ⟨fun h => hai (Sum.inl_injective h),a,rfl⟩

theorem no_outer_adj {H : SimpleGraph (Vertex s k)} (hH : H ≤ cliqueBook s k)
    (i j : Fin k) : ¬H.Adj (.inr i) (.inr j) := by
  intro h
  have hh := hH h
  simpa only [cliqueBook,Sum.isLeft_inr,Bool.false_eq_true,or_self,and_false] using hh

def hubPartition {H : SimpleGraph (Vertex s k)} (hH : H ≤ cliqueBook s k) (i : Fin s) :
    Separator.Partition H (smallerBoundary i) (hubPrivate H i) where
  boundary_disjoint j := by
    apply disjoint_left.mpr
    intro v hv hp
    obtain ⟨a,hai,rfl⟩ := (mem_smallerBoundary i v).mp hv
    cases j with
    | none =>
      simp only [hubPrivate,mem_insert,mem_image] at hp
      rcases hp with he | ⟨j,hj,he⟩
      · exact hai (Sum.inl_injective he)
      · exact Sum.inr_ne_inl he
    | some j => exact Sum.inl_ne_inr (mem_singleton.mp hp)
  private_disjoint := by
    intro j l hjl
    apply disjoint_left.mpr
    intro v hvj hvl
    cases j with
    | none =>
      cases l with
      | none => exact hjl rfl
      | some l =>
        have hv : v = Sum.inr l.1 := mem_singleton.mp hvl
        subst v
        simp only [hubPrivate,mem_insert,Sum.inr.injEq,Sum.inr_ne_inl,mem_image,false_or] at hvj
        obtain ⟨a,ha,he⟩ := hvj
        subst a
        exact l.2 ((mem_outerNeighbors _ _ _).mp ha)
    | some j =>
      cases l with
      | none =>
        have hv : v = Sum.inr j.1 := mem_singleton.mp hvj
        subst v
        simp only [hubPrivate,mem_insert,Sum.inr.injEq,Sum.inr_ne_inl,mem_image,false_or] at hvl
        obtain ⟨a,ha,he⟩ := hvl
        subst a
        exact j.2 ((mem_outerNeighbors _ _ _).mp ha)
      | some l =>
        have he : j.1 = l.1 := Sum.inr_injective ((mem_singleton.mp hvj).symm.trans (mem_singleton.mp hvl))
        exact hjl (congrArg Option.some (Subtype.ext he))
  cover v := by
    cases v with
    | inl a =>
      by_cases hai : a = i
      · subst a
        exact Or.inr ⟨none,mem_insert_self _ _⟩
      · exact Or.inl ((mem_smallerBoundary _ _).mpr ⟨a,hai,rfl⟩)
    | inr j =>
      by_cases hadj : H.Adj (.inl i) (.inr j)
      · exact Or.inr ⟨none,mem_insert_of_mem (mem_image.mpr ⟨j,(mem_outerNeighbors _ _ _).mpr hadj,rfl⟩)⟩
      · exact Or.inr ⟨some ⟨j,hadj⟩,mem_singleton_self _⟩
  no_cross_edge := by
    intro j l u v hu hv hadj
    cases j with
    | none =>
      cases l with
      | none => rfl
      | some l =>
        have hv' : v = Sum.inr l.1 := mem_singleton.mp hv
        subst v
        rcases mem_insert.mp hu with rfl | hu
        · exact False.elim (l.2 hadj)
        · obtain ⟨a,ha,rfl⟩ := mem_image.mp hu
          exact False.elim (no_outer_adj hH _ _ hadj)
    | some j =>
      have hu' : u = Sum.inr j.1 := mem_singleton.mp hu
      subst u
      cases l with
      | none =>
        rcases mem_insert.mp hv with rfl | hv
        · exact False.elim (j.2 (H.adj_symm hadj))
        · obtain ⟨a,ha,rfl⟩ := mem_image.mp hv
          exact False.elim (no_outer_adj hH _ _ hadj)
      | some l =>
        have hv' : v = Sum.inr l.1 := mem_singleton.mp hv
        subst v
        exact False.elim (no_outer_adj hH _ _ hadj)

/-- Deleting all other hubs counts each outer nonneighbor separately,
plus the component containing the selected hub. -/
theorem outer_neighbors_lower (hs : 3 ≤ s)
    {H : SimpleGraph (Vertex s (cliqueCapacity s))}
    (hH : H ≤ cliqueBook s (cliqueCapacity s))
    (z : graphicalFunctionSpace H) (hz : ExtremeSupermodular z.1)
    (hd : FullDimension (basePolytope z.1)) (i : Fin s) :
    saturatedHubNeighbors s ≤ (outerNeighbors H i).card := by
  have hcl := hubs_clique hs hH z hz hd
  have hsm : H.IsClique (smallerBoundary (k := cliqueCapacity s) i) :=
    fun u hu v hv huv => hcl (mem_of_mem_erase hu) (mem_of_mem_erase hv) huv
  have hb := Separator.full_partition_clique_capacity
    (by simp only [Fintype.card_sum,Fintype.card_fin]; omega)
    (hubPartition hH i) (hubPrivate_nonempty H i) hsm z hz hd
  have hcard : (smallerBoundary (k := cliqueCapacity s) i).card = s-1 := by
    rw [smallerBoundary,card_erase_of_mem,BookDimension.boundary_card]
    exact mem_image.mpr ⟨i,mem_univ _,rfl⟩
  rw [hcard,Fintype.card_option,Fintype.card_subtype] at hb
  have hp := card_filter_add_card_filter_not
    (s := (univ : Finset (Fin (cliqueCapacity s))))
    (p := fun j => H.Adj (.inl i) (.inr j))
  simp only [card_univ,Fintype.card_fin] at hp
  change (outerNeighbors H i).card + (outerNonneighbors H i).card = cliqueCapacity s at hp
  change (outerNonneighbors H i).card + 1 ≤ cliqueCapacity (s-1) at hb
  have hmono := BooleanModule.cliqueCapacity_pred_le (show 1 ≤ s by omega)
  unfold saturatedHubNeighbors
  rw [if_neg (by omega : s ≠ 2)]
  omega

/-- A full-dimensional indecomposable deformation on three coordinates has
all three directions.  A missing pair would give two nonzero private blocks
over a singleton boundary, whose separator capacity is only one. -/
theorem three_vertex_complete {V : Type*} [Fintype V] [LinearOrder V]
    (hV : Fintype.card V = 3) (H : SimpleGraph V)
    (z : graphicalFunctionSpace H) (hz : ExtremeSupermodular z.1)
    (hd : FullDimension (basePolytope z.1)) : H = ⊤ := by
  apply SimpleGraph.ext
  funext u v
  apply propext
  constructor
  · intro h
    exact (SimpleGraph.top_adj _ _).mpr h.ne
  · intro htop
    have huv : u ≠ v := (SimpleGraph.top_adj _ _).mp htop
    by_contra hnon
    let B : Finset V := (univ.erase u).erase v
    let A : Fin 2 → Finset V := fun j => if j = 0 then {u} else {v}
    have hA : ∀ j,(A j).Nonempty := by
      intro j
      fin_cases j <;> simp [A]
    have hp : Separator.Partition H B A := {
      boundary_disjoint := by
        intro j
        fin_cases j <;> simp [A,B,disjoint_singleton_left,disjoint_singleton_right]
      private_disjoint := by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all [A,disjoint_singleton,ne_comm]
      cover := by
        intro w
        by_cases hwu : w = u
        · subst w
          exact Or.inr ⟨0,by simp [A]⟩
        by_cases hwv : w = v
        · subst w
          exact Or.inr ⟨1,by simp [A]⟩
        exact Or.inl (by simp [B,hwu,hwv])
      no_cross_edge := by
        intro i j a b ha hb hab
        fin_cases i <;> fin_cases j
        · rfl
        · have ha' : a = u := by simpa [A] using ha
          have hb' : b = v := by simpa [A] using hb
          exact False.elim (hnon (ha' ▸ hb' ▸ hab))
        · have ha' : a = v := by simpa [A] using ha
          have hb' : b = u := by simpa [A] using hb
          exact False.elim (hnon (H.adj_symm (ha' ▸ hb' ▸ hab)))
        · rfl }
    have hBcard : B.card = 1 := by
      dsimp only [B]
      rw [card_erase_of_mem (by simp [Ne.symm huv]),
        card_erase_of_mem (mem_univ u),card_univ,hV]
    have hB : H.IsClique B :=
      SimpleGraph.IsClique.of_subsingleton (Finset.card_le_one.mp hBcard.le)
    have hbound := Separator.full_partition_clique_capacity
      (by omega : 2 ≤ Fintype.card V) hp hA hB z hz hd
    rw [hBcard] at hbound
    norm_num [cliqueCapacity,Nat.choose] at hbound

end GraphicalZonotopes.SaturatedDirections
