module

public import Papers.GraphicalZonotopes.TriangleClasses
public import Papers.GraphicalZonotopes.TetrahedralGrowth
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
namespace TriangleComponents
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The graph of all tetrahedra of the actual direction graph, with adjacency
exactly across a shared triangle. Non-tetrahedral finite subsets are isolated;
this harmless ambient choice avoids any nonempty-type assumption. -/
def cliqueGraph (G : SimpleGraph V) : SimpleGraph (Finset V) where
  Adj C D := C.card = 4 ∧ D.card = 4 ∧ G.IsClique C ∧ G.IsClique D ∧
    C ≠ D ∧ 3 ≤ (C ∩ D).card
  symm := ⟨fun C D h => ⟨h.2.1,h.1,h.2.2.2.1,h.2.2.1,Ne.symm h.2.2.2.2.1,
    by simpa only [inter_comm] using h.2.2.2.2.2⟩⟩
  loopless := ⟨fun _ h => h.2.2.2.2.1 rfl⟩

theorem reachable_of_shared_triangle {G : SimpleGraph V} {C D T : Finset V}
    (hC : C.card = 4) (hD : D.card = 4) (hcC : G.IsClique C) (hcD : G.IsClique D)
    (hT : T.card = 3) (hTC : T ⊆ C) (hTD : T ⊆ D) :
    (cliqueGraph G).Reachable C D := by
  by_cases he : C = D
  · subst D
    exact SimpleGraph.Reachable.rfl
  · apply SimpleGraph.Adj.reachable
    exact ⟨hC,hD,hcC,hcD,he,by
      have h := card_le_card (subset_inter hTC hTD)
      omega⟩

/-- All four-element subsets of one clique lie in one triangle-connected
component. The proof exchanges one vertex at a time, and decreases the exact
cardinality of the set difference at each step. -/
theorem tetrahedra_in_clique_reachable {G : SimpleGraph V} {C : Finset V}
    (hC : G.IsClique C) {D E : Finset V} (hD : D.card = 4) (hE : E.card = 4)
    (hDC : D ⊆ C) (hEC : E ⊆ C) : (cliqueGraph G).Reachable D E := by
  classical
  suffices h : ∀ n D, (D \ E).card = n → D.card = 4 → D ⊆ C →
      (cliqueGraph G).Reachable D E from h _ D rfl hD hDC
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro D hn hD hDC
    by_cases hDE : D = E
    · subst D
      exact SimpleGraph.Reachable.rfl
    · have hdiff : (D \ E).Nonempty := by
        by_contra he
        have hsub := sdiff_eq_empty_iff_subset.mp (not_nonempty_iff_eq_empty.mp he)
        exact hDE (eq_of_subset_of_card_le hsub (by omega))
      obtain ⟨u,hu⟩ := hdiff
      obtain ⟨huD,huE⟩ := mem_sdiff.mp hu
      have hother : (E \ D).Nonempty := by
        rw [← card_pos]
        have he := card_sdiff_comm (show D.card = E.card by omega)
        have hp : 0<(D \ E).card := card_pos.mpr ⟨u,hu⟩
        omega
      obtain ⟨v,hv⟩ := hother
      obtain ⟨hvE,hvD⟩ := mem_sdiff.mp hv
      let D' := insert v (D.erase u)
      have hvErase : v ∉ D.erase u := fun h => hvD (mem_of_mem_erase h)
      have hD' : D'.card = 4 := by
        simp only [D',card_insert_of_notMem hvErase,card_erase_of_mem huD,hD]
      have hD'C : D' ⊆ C := by
        intro w hw
        rcases mem_insert.mp hw with rfl | hw
        · exact hEC hvE
        · exact hDC (mem_of_mem_erase hw)
      have hdiff' : D' \ E = (D \ E).erase u := by
        ext w
        simp only [D',mem_sdiff,mem_insert,mem_erase]
        constructor
        · rintro ⟨hw,hwE⟩
          rcases hw with rfl | hw
          · exact False.elim (hwE hvE)
          · exact ⟨hw.1,hw.2,hwE⟩
        · rintro ⟨hwu,hwD,hwE⟩
          exact ⟨Or.inr ⟨hwu,hwD⟩,hwE⟩
      have hlt : (D' \ E).card < n := by
        rw [hdiff',card_erase_of_mem hu]
        have hp : 0<(D \ E).card := card_pos.mpr ⟨u,hu⟩
        omega
      have hstep : (cliqueGraph G).Reachable D D' := by
        apply reachable_of_shared_triangle hD hD'
          (fun x hx y hy hxy => hC (hDC hx) (hDC hy) hxy)
          (fun x hx y hy hxy => hC (hD'C hx) (hD'C hy) hxy)
          (T := D.erase u)
        · rw [card_erase_of_mem huD,hD]
        · exact erase_subset _ _
        · exact subset_insert _ _
      exact hstep.trans (ih _ hlt D' rfl hD' hD'C)

abbrev ComponentIndex (G : SimpleGraph V) := (cliqueGraph G).ConnectedComponent ⊕ Finset V

noncomputable instance componentIndexFintype (G : SimpleGraph V) :
    Fintype (ComponentIndex G) := by
  classical
  unfold ComponentIndex
  infer_instance

abbrev IncidentTetrahedron (G : SimpleGraph V) (C : Finset V) : Prop :=
  ∃ D : Finset V, D.card = 4 ∧ G.IsClique D ∧ C ⊆ D

abbrev ContainedTetrahedron (G : SimpleGraph V) (C : Finset V) : Prop :=
  ∃ D : Finset V, D.card = 4 ∧ G.IsClique D ∧ D ⊆ C

def classOf (G : SimpleGraph V) (C : Finset V) : ComponentIndex G := by
  classical
  exact if hC : C.card = 3 then
    if h : IncidentTetrahedron G C then
      Sum.inl ((cliqueGraph G).connectedComponentMk (Classical.choose h))
    else Sum.inr C
  else if h : ContainedTetrahedron G C then
    Sum.inl ((cliqueGraph G).connectedComponentMk (Classical.choose h))
  else Sum.inr C

theorem contained_of_clique {G : SimpleGraph V} {C : Finset V}
    (hC : 4 ≤ C.card) (hc : G.IsClique C) : ContainedTetrahedron G C := by
  obtain ⟨D,hDC,hD⟩ := exists_subset_card_eq hC
  exact ⟨D,hD,fun u hu v hv huv => hc (hDC hu) (hDC hv) huv,hDC⟩

theorem triangle_extends_in_clique {G : SimpleGraph V} {C T : Finset V}
    (hC : 4 ≤ C.card) (hc : G.IsClique C) (hT : T.card = 3) (hTC : T ⊆ C) :
    ∃ D : Finset V, D.card = 4 ∧ G.IsClique D ∧ T ⊆ D ∧ D ⊆ C := by
  have hdiff : (C \ T).Nonempty := by
    rw [← card_pos,card_sdiff_of_subset hTC,hT]
    omega
  obtain ⟨v,hv⟩ := hdiff
  obtain ⟨hvC,hvT⟩ := mem_sdiff.mp hv
  refine ⟨insert v T,by rw [card_insert_of_notMem hvT,hT],?_,subset_insert _ _,?_⟩
  · intro u hu w hw huw
    exact hc (insert_subset hvC hTC hu) (insert_subset hvC hTC hw) huw
  · exact insert_subset hvC hTC

theorem classOf_higher {G : SimpleGraph V} {C D : Finset V}
    (hC : 4 ≤ C.card) (hc : G.IsClique C) (hD : D.card = 4)
    (hDC : D ⊆ C) :
    classOf G C = Sum.inl ((cliqueGraph G).connectedComponentMk D) := by
  classical
  have he := contained_of_clique hC hc
  have hn : C.card ≠ 3 := by omega
  have hcomp : (cliqueGraph G).connectedComponentMk (Classical.choose he)=
      (cliqueGraph G).connectedComponentMk D := by
    apply SimpleGraph.ConnectedComponent.sound
    obtain ⟨hd,hcl,hsub⟩ := Classical.choose_spec he
    exact tetrahedra_in_clique_reachable hc hd hD hsub hDC
  unfold classOf
  rw [dite_eq_right hn, dite_eq_left he]
  exact congrArg Sum.inl hcomp

theorem classOf_triangle {G : SimpleGraph V} {T D : Finset V}
    (hT : T.card = 3) (hD : D.card = 4) (hcD : G.IsClique D) (hTD : T ⊆ D) :
    classOf G T = Sum.inl ((cliqueGraph G).connectedComponentMk D) := by
  classical
  have he : IncidentTetrahedron G T := ⟨D,hD,hcD,hTD⟩
  have hcomp : (cliqueGraph G).connectedComponentMk (Classical.choose he)=
      (cliqueGraph G).connectedComponentMk D := by
    apply SimpleGraph.ConnectedComponent.sound
    obtain ⟨hd,hc,hsub⟩ := Classical.choose_spec he
    exact reachable_of_shared_triangle hd hD hc hcD hT hsub hTD
  unfold classOf
  rw [dite_eq_left hT, dite_eq_left he]
  exact congrArg Sum.inl hcomp

theorem classOf_compatible {G : SimpleGraph V} {y : SetFunction V}
    (hy : CliqueSupported G y) : PositiveDecomposition.ClassCompatible y (classOf G) := by
  intro C hC hyC T hT hTC
  have hc : G.IsClique C := by
    intro u hu v hv huv
    by_contra hn
    exact hyC (hy.2.2 C u v hu hv huv hn)
  obtain ⟨D,hD,hcD,hTD,hDC⟩ := triangle_extends_in_clique hC hc hT hTC
  rw [classOf_triangle hT hD hcD hTD,classOf_higher hC hc hD hDC]

def componentFamily (G : SimpleGraph V) (a : (cliqueGraph G).ConnectedComponent) :
    Finset (Finset V) := by
  classical
  exact univ.filter (fun C => C.card = 4 ∧ G.IsClique C ∧
    (cliqueGraph G).connectedComponentMk C = a)

def componentVertices (G : SimpleGraph V) (a : (cliqueGraph G).ConnectedComponent) :
    Finset V := (componentFamily G a).biUnion id

theorem mem_componentFamily {G : SimpleGraph V} {a : (cliqueGraph G).ConnectedComponent}
    {C : Finset V} : C ∈ componentFamily G a ↔
      C.card = 4 ∧ G.IsClique C ∧ (cliqueGraph G).connectedComponentMk C = a := by
  classical
  simp [componentFamily]

theorem higher_subset_component {G : SimpleGraph V} {C : Finset V}
    (hC : 4 ≤ C.card) (hc : G.IsClique C)
    {a : (cliqueGraph G).ConnectedComponent} (ha : classOf G C = Sum.inl a) :
    C ⊆ componentVertices G a := by
  classical
  obtain ⟨D,hD,hcD,hDC⟩ := contained_of_clique hC hc
  have hDa : (cliqueGraph G).connectedComponentMk D = a := by
    rw [classOf_higher hC hc hD hDC] at ha
    exact Sum.inl.inj ha
  intro v hv
  by_cases hvD : v ∈ D
  · exact mem_biUnion.mpr ⟨D,mem_componentFamily.mpr ⟨hD,hcD,hDa⟩,hvD⟩
  · have hne : D.Nonempty := card_pos.mp (by omega)
    obtain ⟨u,hu⟩ := hne
    let E := insert v (D.erase u)
    have hvE : v ∉ D.erase u := fun h => hvD (mem_of_mem_erase h)
    have hE : E.card = 4 := by
      simp only [E,card_insert_of_notMem hvE,card_erase_of_mem hu,hD]
    have hEC : E ⊆ C := insert_subset hv ((erase_subset _ _).trans hDC)
    have hcE : G.IsClique E := fun x hx y hy hxy => hc (hEC hx) (hEC hy) hxy
    have hEa : (cliqueGraph G).connectedComponentMk E = a :=
      (SimpleGraph.ConnectedComponent.sound
        (tetrahedra_in_clique_reachable hc hE hD hEC hDC)).trans hDa
    exact mem_biUnion.mpr ⟨E,mem_componentFamily.mpr ⟨hE,hcE,hEa⟩,mem_insert_self _ _⟩

theorem triangle_subset_component {G : SimpleGraph V} {T : Finset V} (hT : T.card = 3)
    {a : (cliqueGraph G).ConnectedComponent} (ha : classOf G T = Sum.inl a) :
    T ⊆ componentVertices G a := by
  classical
  by_cases hi : IncidentTetrahedron G T
  · obtain ⟨D,hD,hcD,hTD⟩ := hi
    have he := classOf_triangle hT hD hcD hTD
    rw [he] at ha
    intro v hv
    exact mem_biUnion.mpr ⟨D,mem_componentFamily.mpr ⟨hD,hcD,Sum.inl.inj ha⟩,hTD hv⟩
  · simp [classOf,hT,hi] at ha

theorem right_class_is_triangle {G : SimpleGraph V} {y : SetFunction V}
    (hy : CliqueSupported G y) {C T : Finset V} (hC : 3 ≤ C.card) (hyC : y C ≠ 0)
    (ha : classOf G C = Sum.inr T) : C.card = 3 ∧ C = T := by
  classical
  have hc : G.IsClique C := by
    intro u hu v hv huv
    by_contra hn
    exact hyC (hy.2.2 C u v hu hv huv hn)
  by_cases h3 : C.card = 3
  · refine ⟨h3,?_⟩
    by_cases hi : IncidentTetrahedron G C
    · simp [classOf,h3,hi] at ha
    · have hclass : classOf G C=Sum.inr C := by
        simp only [classOf, dite_eq_left h3, dite_eq_right hi]
      exact Sum.inr.inj (hclass.symm.trans ha)
  · have h4 : 4 ≤ C.card := by omega
    obtain ⟨D,hD,hcD,hDC⟩ := contained_of_clique h4 hc
    rw [classOf_higher h4 hc hD hDC] at ha
    cases ha

theorem componentFamily_preconnected (G : SimpleGraph V)
    (a : (cliqueGraph G).ConnectedComponent) :
    (tetrahedronGraph (componentFamily G a)).Preconnected := by
  classical
  intro C D
  have hC := mem_componentFamily.mp C.2
  have hD := mem_componentFamily.mp D.2
  have hr : (cliqueGraph G).Reachable C.1 D.1 :=
    SimpleGraph.ConnectedComponent.exact (hC.2.2.trans hD.2.2.symm)
  rw [SimpleGraph.reachable_eq_reflTransGen] at hr
  have hpath : ∀ E, Relation.ReflTransGen (cliqueGraph G).Adj C.1 E →
      ∃ hE : E ∈ componentFamily G a,
        (tetrahedronGraph (componentFamily G a)).Reachable C ⟨E,hE⟩ := by
    intro E hp
    induction hp with
    | refl => exact ⟨C.2,SimpleGraph.Reachable.rfl⟩
    | @tail E F hp hEF ih =>
      obtain ⟨hE,hreach⟩ := ih
      have hcE := mem_componentFamily.mp hE
      have hF : F ∈ componentFamily G a := mem_componentFamily.mpr
        ⟨hEF.2.1,hEF.2.2.2.1,
          (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hEF).symm.trans hcE.2.2⟩
      refine ⟨hF,hreach.trans (SimpleGraph.Adj.reachable ?_)⟩
      exact ⟨fun he => hEF.2.2.2.2.1 (congrArg Subtype.val he),hEF.2.2.2.2.2⟩
  obtain ⟨hD',hreach⟩ := hpath _ hr
  exact hreach

end TriangleComponents
end GraphicalZonotopes
