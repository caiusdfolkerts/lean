module

public import Papers.GraphicalZonotopes.GraphModels
public import Mathlib.Data.Finset.Card

@[expose] public section
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The common neighbors of a triangle, with its own vertices excluded. -/
def commonApices (G : SimpleGraph V) (T : Finset V) : Finset V :=
  univ.filter (fun v => v ∉ T ∧ ∀ t ∈ T, G.Adj v t)

@[simp] theorem mem_commonApices (G : SimpleGraph V) (T : Finset V) (v : V) :
    v ∈ commonApices G T ↔ v ∉ T ∧ ∀ t ∈ T, G.Adj v t := by
  simp [commonApices]

theorem tetrahedra_over_triangle_eq_image {G : SimpleGraph V} {T : Finset V}
    (hT : T.card = 3) (hcT : G.IsClique T) :
    (tetrahedra G).filter (fun C => T ⊆ C) =
      (commonApices G T).image (fun u => insert u T) := by
  ext C
  constructor
  · intro hC
    obtain ⟨hC,hTC⟩ := mem_filter.mp hC
    obtain ⟨hcC,hclC⟩ := (mem_filter.mp hC).2
    have hd : (C \ T).card = 1 := by
      rw [card_sdiff_of_subset hTC,hcC,hT]
    obtain ⟨u,hu⟩ := card_eq_one.mp hd
    have huCT : u ∈ C ∧ u ∉ T := mem_sdiff.mp (by rw [hu]; simp)
    refine mem_image.mpr ⟨u,(mem_commonApices G T u).mpr ⟨huCT.2,?_⟩,?_⟩
    · intro t ht
      exact hclC huCT.1 (hTC ht) (fun he => huCT.2 (he ▸ ht))
    · ext v
      constructor
      · intro hv
        rcases mem_insert.mp hv with rfl | hv
        · exact huCT.1
        · exact hTC hv
      · intro hv
        by_cases hvT : v ∈ T
        · exact mem_insert_of_mem hvT
        · have hvm : v ∈ C \ T := mem_sdiff.mpr ⟨hv,hvT⟩
          rw [hu] at hvm
          exact mem_insert.mpr (Or.inl (mem_singleton.mp hvm))
  · intro hC
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hC
    obtain ⟨huT,huAdj⟩ := (mem_commonApices G T u).mp hu
    apply mem_filter.mpr
    refine ⟨mem_filter.mpr ⟨mem_univ _,?_,?_⟩,subset_insert _ _⟩
    · rw [card_insert_of_notMem huT,hT]
    · intro a ha b hb hab
      rcases mem_insert.mp ha with hau | haT
      · subst a
        exact huAdj b ((mem_insert.mp hb).resolve_left (Ne.symm hab))
      · rcases mem_insert.mp hb with hbu | hbT
        · subst b
          exact G.adj_symm (huAdj a haT)
        · exact hcT haT hbT hab

/-- The paper's tetrahedron multiplicity is literally the number of common
neighbors of its triangle. No maximal-clique or planarity convention enters
this elementary finite-set dictionary. -/
theorem triangleMultiplicity_eq_commonApices_card {G : SimpleGraph V} {T : Finset V}
    (hT : T.card = 3) (hcT : G.IsClique T) :
    triangleMultiplicity G T = (commonApices G T).card := by
  rw [triangleMultiplicity,tetrahedra_over_triangle_eq_image hT hcT]
  apply card_image_of_injOn
  intro u hu v hv he
  change insert u T = insert v T at he
  have huT := ((mem_commonApices G T u).mp hu).1
  have hum : u ∈ insert v T := by rw [← he]; exact mem_insert_self _ _
  exact (mem_insert.mp hum).resolve_right huT

end GraphicalZonotopes
