module

public import sunlet.permutation_families
public import Mathlib.Data.Finset.Card
public import Lean.Elab.Tactic.Omega

/-! The finite orbit estimates used to split Latin colors into two transitive families. -/

@[expose] public section
noncomputable section
open Finset

namespace Sunlet

variable {ι Ω : Type*} [Fintype ι] [Fintype Ω] [DecidableEq ι] [DecidableEq Ω]

/-- The literal normalized Latin property. Every column is a bijection. -/
structure NormalizedLatinSystem (ι Ω : Type*) where
  perm : ι → Equiv.Perm Ω
  identity : ι
  normalized : perm identity = Equiv.refl Ω
  column_bijective : ∀ b, Function.Bijective (fun a => perm a b)

namespace NormalizedLatinSystem

variable (L : NormalizedLatinSystem ι Ω)

include L in
theorem card_eq (o : Ω) : Fintype.card ι = Fintype.card Ω :=
  Fintype.card_congr (Equiv.ofBijective _ (L.column_bijective o))

theorem derangement (a : ι) (ha : a ≠ L.identity) (b : Ω) : L.perm a b ≠ b := by
  intro h
  apply ha
  apply (L.column_bijective b).injective
  simpa [L.normalized] using h

theorem perm_injective (o : Ω) : Function.Injective L.perm := by
  intro a b h
  exact (L.column_bijective o).injective (congrArg (fun p : Equiv.Perm Ω => p o) h)

def neighbors (P : Finset ι) (x : Ω) : Finset Ω := insert x (P.image fun a => L.perm a x)

theorem card_neighbors (P : Finset ι) (he : L.identity ∉ P) (x : Ω) :
    (L.neighbors P x).card = P.card + 1 := by
  have hn : x ∉ P.image (fun a => L.perm a x) := by
    intro h
    obtain ⟨a, ha, hx⟩ := mem_image.mp h
    exact L.derangement a (fun heq => he (heq ▸ ha)) x hx
  simp only [neighbors, card_insert_of_notMem hn]
  rw [card_image_of_injective P (L.column_bijective x).injective]

theorem connected_of_mem_neighbors {P : Finset ι} {x y : Ω}
    (hy : y ∈ L.neighbors P x) : ColorConnected L.perm (P : Set ι) x y := by
  rcases mem_insert.mp hy with rfl | hy
  · exact colorConnected_refl _ _ _
  · obtain ⟨a, ha, rfl⟩ := mem_image.mp hy
    exact colorConnected_step _ _ ha x

theorem neighbors_subset {P : Finset ι} {S : Finset Ω}
    (hS : ∀ a ∈ P, ∀ x ∈ S, L.perm a x ∈ S) {x : Ω} (hx : x ∈ S) :
    L.neighbors P x ⊆ S := by
  intro y hy
  rcases mem_insert.mp hy with rfl | hy
  · exact hx
  · obtain ⟨a, ha, rfl⟩ := mem_image.mp hy
    exact hS a ha x hx

theorem neighbors_disjoint_of_not_connected {P : Finset ι} {x y : Ω}
    (hxy : ¬ColorConnected L.perm (P : Set ι) x y) :
    Disjoint (L.neighbors P x) (L.neighbors P y) := by
  apply Finset.disjoint_left.mpr
  intro z hz₁ hz₂
  apply hxy
  exact Relation.EqvGen.trans _ _ _ (L.connected_of_mem_neighbors hz₁)
    (Relation.EqvGen.symm _ _ (L.connected_of_mem_neighbors hz₂))

/-- Inside a preserved finite set, two different orbits would each contain
at least one more point than there are colors. -/
theorem connected_on_of_card (P : Finset ι) (S : Finset Ω)
    (he : L.identity ∉ P)
    (hS : ∀ a ∈ P, ∀ x ∈ S, L.perm a x ∈ S)
    (hcard : S.card < 2 * (P.card + 1)) :
    ∀ x ∈ S, ∀ y ∈ S, ColorConnected L.perm (P : Set ι) x y := by
  intro x hx y hy
  by_contra hxy
  have hdis := L.neighbors_disjoint_of_not_connected hxy
  have hsub : L.neighbors P x ∪ L.neighbors P y ⊆ S :=
    union_subset (L.neighbors_subset hS hx) (L.neighbors_subset hS hy)
  have hc := card_le_card hsub
  rw [card_union_of_disjoint hdis, L.card_neighbors P he x, L.card_neighbors P he y] at hc
  omega

theorem transitive_of_card (P : Finset ι) (he : L.identity ∉ P)
    (hcard : Fintype.card Ω < 2 * (P.card + 1)) :
    TransitiveFamily L.perm (P : Set ι) := by
  intro x y
  exact L.connected_on_of_card P univ he (by intros; exact mem_univ _)
    (by simpa using hcard) x (mem_univ _) y (mem_univ _)

def orbit (P : Finset ι) (x : Ω) : Finset Ω := by
  classical
  exact univ.filter fun y => ColorConnected L.perm (P : Set ι) x y

@[simp] theorem mem_orbit (P : Finset ι) (x y : Ω) :
    y ∈ L.orbit P x ↔ ColorConnected L.perm (P : Set ι) x y := by simp [orbit]

theorem self_mem_orbit (P : Finset ι) (x : Ω) : x ∈ L.orbit P x := by
  simp only [mem_orbit]
  exact Relation.EqvGen.refl _

theorem perm_mem_orbit_iff {P : Finset ι} {a : ι} (ha : a ∈ P) (x y : Ω) :
    L.perm a y ∈ L.orbit P x ↔ y ∈ L.orbit P x := by
  simp only [mem_orbit]
  constructor
  · intro h
    exact Relation.EqvGen.trans _ _ _ h
      (Relation.EqvGen.symm _ _ (colorConnected_step _ _ ha y))
  · intro h
    exact Relation.EqvGen.trans _ _ _ h (colorConnected_step _ _ ha y)

theorem neighbors_subset_orbit (P : Finset ι) (x : Ω) :
    L.neighbors P x ⊆ L.orbit P x := by
  intro y hy
  exact (L.mem_orbit P x y).mpr (L.connected_of_mem_neighbors hy)

theorem orbit_card_lower (P : Finset ι) (he : L.identity ∉ P) (x : Ω) :
    P.card + 1 ≤ (L.orbit P x).card := by
  simpa [L.card_neighbors P he x] using card_le_card (L.neighbors_subset_orbit P x)

end NormalizedLatinSystem
end Sunlet
