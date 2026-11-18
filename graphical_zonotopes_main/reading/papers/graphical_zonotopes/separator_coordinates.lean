module

public import Papers.GraphicalZonotopes.BoundaryContexts
public import Papers.GraphicalZonotopes.Gluing
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace Separator
open Finset
open scoped BigOperators
variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

/-- A partition of the private vertices across an induced boundary. These
conditions are precisely disjoint coverage and absence of edges between
private parts; no clique or rigidity assumption is made on the boundary. -/
structure Partition (G : SimpleGraph V) (B : Finset V) (A : J → Finset V) : Prop where
  boundary_disjoint : ∀ j,Disjoint B (A j)
  private_disjoint : Pairwise (fun j k => Disjoint (A j) (A k))
  cover : ∀ v : V,v∈B ∨ ∃ j,v∈A j
  no_cross_edge : ∀ j k u v,u∈A j → v∈A k → G.Adj u v → j=k

variable {G : SimpleGraph V} {B : Finset V} {A : J → Finset V}

/-- Every clique not contained in the boundary has one and only one private
branch. This exhausts all original Möbius coordinates. -/
theorem Partition.clique_unique_branch (h : Partition G B A)
    (C : CliqueIndex G) (hC : ¬C.1⊆B) : ∃! j : J,C.1⊆B∪A j := by
  obtain ⟨u,huC,huB⟩ := Finset.not_subset.mp hC
  obtain ⟨j,huj⟩ := (h.cover u).resolve_left huB
  have hsub : C.1⊆B∪A j := by
    intro v hvC
    by_cases hvB : v∈B
    · exact mem_union_left _ hvB
    · obtain ⟨k,hvk⟩ := (h.cover v).resolve_left hvB
      by_cases hjk : j=k
      · subst k
        exact mem_union_right _ hvk
      · have huv : u≠v := by
          intro he
          have hdis := Finset.disjoint_left.mp (h.private_disjoint hjk)
          exact hdis (he ▸ huj) hvk
        have hedge := C.2.2 huC hvC huv
        exact False.elim (hjk (h.no_cross_edge j k u v huj hvk hedge))
  refine ⟨j,hsub,?_⟩
  intro k hk
  have huk : u∈A k := (mem_union.mp (hk huC)).resolve_left huB
  by_contra hkj
  exact Finset.disjoint_left.mp (h.private_disjoint hkj) huk huj

abbrev boundaryIndex (G : SimpleGraph V) (B : Finset V) :=
  {C : CliqueIndex G // C.1⊆B}

abbrev privateIndex (G : SimpleGraph V) (B : Finset V) (A : J → Finset V) (j : J) :=
  {C : CliqueIndex G // ¬C.1⊆B ∧ C.1⊆B∪A j}

noncomputable instance boundaryIndexFintype : Fintype (boundaryIndex G B) := by
  classical
  unfold boundaryIndex
  infer_instance

noncomputable instance privateIndexFintype (j : J) : Fintype (privateIndex G B A j) := by
  classical
  unfold privateIndex
  infer_instance

def branchOf (h : Partition G B A) (C : CliqueIndex G) (hC : ¬C.1⊆B) : J :=
  Classical.choose (h.clique_unique_branch C hC)

theorem branchOf_spec (h : Partition G B A) (C : CliqueIndex G) (hC : ¬C.1⊆B) :
    C.1⊆B∪A (branchOf h C hC) :=
  (Classical.choose_spec (h.clique_unique_branch C hC)).1

theorem branchOf_eq (h : Partition G B A) (C : CliqueIndex G) (hC : ¬C.1⊆B)
    {j : J} (hj : C.1⊆B∪A j) : branchOf h C hC=j := by
  exact ((Classical.choose_spec (h.clique_unique_branch C hC)).2 j hj).symm

def classify (h : Partition G B A) (C : CliqueIndex G) :
    boundaryIndex G B ⊕ (Σ j : J,privateIndex G B A j) := by
  classical
  exact if hC : C.1⊆B then Sum.inl ⟨C,hC⟩ else
    Sum.inr ⟨branchOf h C hC,⟨C,hC,branchOf_spec h C hC⟩⟩

def forget : boundaryIndex G B ⊕ (Σ j : J,privateIndex G B A j) → CliqueIndex G
  | Sum.inl C => C.1
  | Sum.inr ⟨_,C⟩ => C.1

@[simp] theorem forget_classify (h : Partition G B A) (C : CliqueIndex G) :
    forget (classify h C)=C := by
  classical
  unfold classify
  split_ifs <;> rfl

@[simp] theorem classify_boundary (h : Partition G B A) (C : boundaryIndex G B) :
    classify h C.1=Sum.inl C := by
  classical
  simp [classify,C.2]

@[simp] theorem classify_private (h : Partition G B A) (j : J)
    (C : privateIndex G B A j) : classify h C.1=Sum.inr ⟨j,C⟩ := by
  classical
  unfold classify
  rw [dif_neg C.2.1]
  have hj := branchOf_eq h C.1 C.2.1 C.2.2
  congr 1
  apply Sigma.ext hj
  change (⟨C.1, _⟩ : {D : CliqueIndex G // ¬D.1⊆B ∧ D.1⊆B∪A (branchOf h C.1 C.2.1)}) ≍ C
  exact (Subtype.heq_iff_coe_eq (by intro D; rw [hj])).mpr rfl

/-- Exact reindexing of every clique coordinate into one boundary coordinate
or one private coordinate. No zero slots or exceptional cliques are omitted. -/
def indexEquiv (h : Partition G B A) :
    CliqueIndex G ≃ boundaryIndex G B ⊕ (Σ j : J,privateIndex G B A j) where
  toFun := classify h
  invFun := forget
  left_inv := forget_classify h
  right_inv c := by
    cases c with
    | inl C => exact classify_boundary h C
    | inr C => rcases C with ⟨j,C⟩; exact classify_private h j C

def joinCoordinates (h : Partition G B A)
    (x : (boundaryIndex G B → ℝ) × (∀ j : J,privateIndex G B A j → ℝ)) :
    CliqueIndex G → ℝ := fun C =>
  match classify h C with
  | Sum.inl D => x.1 D
  | Sum.inr ⟨j,D⟩ => x.2 j D

@[simp] theorem joinCoordinates_boundary (h : Partition G B A)
    (x : (boundaryIndex G B → ℝ) × (∀ j : J,privateIndex G B A j → ℝ))
    (C : boundaryIndex G B) : joinCoordinates h x C.1=x.1 C := by
  simp only [joinCoordinates,classify_boundary]

@[simp] theorem joinCoordinates_private (h : Partition G B A)
    (x : (boundaryIndex G B → ℝ) × (∀ j : J,privateIndex G B A j → ℝ))
    (j : J) (C : privateIndex G B A j) : joinCoordinates h x C.1=x.2 j C := by
  simp only [joinCoordinates,classify_private]

/-- The complete linear coordinate dictionary, before inequalities are
translated. This is an actual equivalence, rather than a dimension assumption. -/
def coordinateEquiv (h : Partition G B A) :
    ((boundaryIndex G B → ℝ) × (∀ j : J,privateIndex G B A j → ℝ)) ≃ₗ[ℝ]
      (CliqueIndex G → ℝ) where
  toFun := joinCoordinates h
  invFun y := (fun C => y C.1,fun _ C => y C.1)
  left_inv x := by
    apply Prod.ext
    · funext C
      exact joinCoordinates_boundary h x C
    · funext j C
      exact joinCoordinates_private h x j C
  right_inv y := by
    funext C
    have hf := forget_classify h C
    unfold joinCoordinates
    cases hc : classify h C with
    | inl D =>
      have he : D.1=C := by simpa only [hc,forget] using hf
      exact congrArg y he
    | inr D =>
      rcases D with ⟨j,D⟩
      have he : D.1=C := by simpa only [hc,forget] using hf
      exact congrArg y he
  map_add' x y := by
    funext C
    cases hc : classify h C <;> simp [joinCoordinates, hc]
  map_smul' a x := by
    funext C
    cases hc : classify h C <;> simp [joinCoordinates, hc]

/-- Composition with the actual graphical Möbius equivalence gives the
original normalized set functions, not an abstract stand-in cone. -/
def functionEquiv (h : Partition G B A) :
    ((boundaryIndex G B → ℝ) × (∀ j : J,privateIndex G B A j → ℝ)) ≃ₗ[ℝ]
      graphicalFunctionSpace G :=
  (coordinateEquiv h).trans (graphicalCoordinatesEquiv G)

/-- The graph after deleting the boundary, with its usual induced adjacency. -/
def outsideGraph (G : SimpleGraph V) (B : Finset V) : SimpleGraph {v : V // v∉B} :=
  G.induce {v : V | v∉B}

def componentPart (G : SimpleGraph V) (B : Finset V)
    (c : (outsideGraph G B).ConnectedComponent) : Finset V := by
  classical
  exact univ.filter (fun v => ∃ hv : v∉B,
    (outsideGraph G B).connectedComponentMk ⟨v,hv⟩=c)

@[simp] theorem mem_componentPart (G : SimpleGraph V) (B : Finset V)
    (c : (outsideGraph G B).ConnectedComponent) (v : V) :
    v∈componentPart G B c ↔ ∃ hv : v∉B,
      (outsideGraph G B).connectedComponentMk ⟨v,hv⟩=c := by
  classical
  simp [componentPart]

noncomputable instance componentFintype (G : SimpleGraph V) (B : Finset V) :
    Fintype ((outsideGraph G B).ConnectedComponent) := Fintype.ofFinite _

/-- Every actual induced separator supplies the partition used by the
coordinate dictionary, including empty boundaries and no private vertices. -/
theorem componentPartition (G : SimpleGraph V) (B : Finset V) :
    Partition G B (componentPart G B) := by
  classical
  constructor
  · intro c
    apply Finset.disjoint_left.mpr
    intro v hvB hvc
    obtain ⟨hv,_⟩ := (mem_componentPart G B c v).mp hvc
    exact hv hvB
  · intro c d hcd
    apply Finset.disjoint_left.mpr
    intro v hvc hvd
    obtain ⟨hv,hc⟩ := (mem_componentPart G B c v).mp hvc
    obtain ⟨hv',hd⟩ := (mem_componentPart G B d v).mp hvd
    exact hcd (hc.symm.trans hd)
  · intro v
    by_cases hv : v∈B
    · exact Or.inl hv
    · refine Or.inr ⟨(outsideGraph G B).connectedComponentMk ⟨v,hv⟩,?_⟩
      exact (mem_componentPart G B _ v).mpr ⟨hv,rfl⟩
  · intro c d u v hu hv hadj
    obtain ⟨huB,huc⟩ := (mem_componentPart G B c u).mp hu
    obtain ⟨hvB,hvd⟩ := (mem_componentPart G B d v).mp hv
    have he : (outsideGraph G B).connectedComponentMk ⟨u,huB⟩=
        (outsideGraph G B).connectedComponentMk ⟨v,hvB⟩ :=
      SimpleGraph.ConnectedComponent.sound (SimpleGraph.Adj.reachable hadj)
    exact huc.symm.trans (he.trans hvd)

end Separator
end GraphicalZonotopes
