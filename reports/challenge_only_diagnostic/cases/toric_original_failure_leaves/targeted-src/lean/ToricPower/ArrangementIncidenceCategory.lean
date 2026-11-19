module

public import ToricPower.ArrangementEquivariant
public import Mathlib.CategoryTheory.Category.Basic

/-!
# The actual finite translated incidence category

Objects are all normalized cells of the augmented integral arrangement.
A morphism from `c` to `d` records an integer translate of the entire
closed cell `c` contained in the closed cell `d`. Composition adds the
translation vectors. Distinct incidences are retained even when their
source and target objects coincide after quotienting by the lattice.

Both the object set and each actual hom-set are proved finite. Every
nonidentity morphism strictly increases cell dimension. Thus this is a
finite direct category suitable for actual cellular module diagrams;
it is not the face poset of a possibly nonregular torus quotient.

Candidate source pending checking by the pinned Lean compiler.
-/

@[expose] public noncomputable section

open Set CategoryTheory
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)

/-- All genuine normalized cells, in all their actual dimensions. -/
abbrev IncidenceObject := Σ d, NormalizedCell A d

/-- The literal closed polyhedron attached to a normalized cell. -/
def incidenceClosedCell (c : IncidenceObject A) : Set (Fin n → ℝ) :=
  closedCell (augmentedForms A) c.2.val.val.1 c.2.val.val.2

/-- Each lattice vector remains an individual incidence. -/
abbrev IncidenceHom (c d : IncidenceObject A) :=
  {a : Fin n → ℤ // ∀ x ∈ incidenceClosedCell A c,
    x + latticeLift a ∈ incidenceClosedCell A d}

@[ext]
theorem IncidenceHom.ext {c d : IncidenceObject A} {f g : IncidenceHom A c d}
    (h : f.val = g.val) : f = g := Subtype.ext h

@[reducible]
instance incidenceCategory : Category (IncidenceObject A) where
  Hom := IncidenceHom A
  id c := ⟨0, by
    intro x hx
    have zeroLift : latticeLift (0 : Fin n → ℤ) = 0 := by
      funext j
      simp only [latticeLift, Pi.zero_apply, Int.cast_zero]
    rw [zeroLift, add_zero]
    exact hx⟩
  comp f g := ⟨f.val + g.val, by
    intro x hx
    have h := g.property _ (f.property x hx)
    simpa only [latticeLift_add, add_assoc] using h⟩
  id_comp f := by apply Subtype.ext; exact zero_add f.val
  comp_id f := by apply Subtype.ext; exact add_zero f.val
  assoc f g h := by apply Subtype.ext; exact add_assoc f.val g.val h.val

@[simp]
theorem incidence_id_val (c : IncidenceObject A) :
    (𝟙 c : c ⟶ c).val = 0 := rfl

@[simp]
theorem incidence_comp_val {c d e : IncidenceObject A} (f : c ⟶ d) (g : d ⟶ e) :
    (f ≫ g).val = f.val + g.val := rfl

/-- Every point of a normalized closed cell lies in the literal compact
cube. This is used to bound actual incidence translations. -/
theorem incidenceClosedCell_subset_cube (c : IncidenceObject A) :
    incidenceClosedCell A c ⊆ Icc (-1 : Fin n → ℝ) 0 := by
  intro x hx
  constructor
  · intro j
    have hb := (closedCell_coordinate_bounds A _ _ hx j).1
    have he : c.2.val.val.1 (.inr j) = 0 := congrFun c.2.property j
    simpa only [he, Int.cast_zero, zero_sub, Pi.neg_apply, Pi.one_apply] using hb
  · intro j
    have hb := (closedCell_coordinate_bounds A _ _ hx j).2
    have he : c.2.val.val.1 (.inr j) = 0 := congrFun c.2.property j
    simpa only [he, Int.cast_zero, Pi.zero_apply] using hb

/-- Each coordinate of an actual incidence translation is one of
`-1`, `0`, and `1`; this is a consequence of the literal closed cells. -/
theorem incidence_translation_bounds {c d : IncidenceObject A} (f : c ⟶ d)
    (j : Fin n) : -1 ≤ f.val j ∧ f.val j ≤ 1 := by
  obtain ⟨x, hx⟩ := c.2.val.property.1
  have hc : x ∈ incidenceClosedCell A c := cell_subset_closedCell _ _ _ hx
  have hbase := incidenceClosedCell_subset_cube A c hc
  have htarget := incidenceClosedCell_subset_cube A d (f.property x hc)
  have hlow : (-1 : ℝ) ≤ (f.val j : ℝ) := by
    have h₁ := hbase.2 j
    have h₂ := htarget.1 j
    change -1 ≤ x j + (f.val j : ℝ) at h₂
    change x j ≤ 0 at h₁
    linarith
  have hupp : (f.val j : ℝ) ≤ 1 := by
    have h₁ := hbase.1 j
    have h₂ := htarget.2 j
    change x j + (f.val j : ℝ) ≤ 0 at h₂
    change -1 ≤ x j at h₁
    linarith
  exact ⟨by exact_mod_cast hlow, by exact_mod_cast hupp⟩

instance incidenceHom_finite (c d : IncidenceObject A) : Finite (c ⟶ d) := by
  let target := {a : Fin n → ℤ | ∀ j, a j ∈ Icc (-1 : ℤ) 1}
  have finite_target : Set.Finite target :=
    Set.Finite.pi' (fun _ : Fin n => Set.finite_Icc (-1 : ℤ) 1)
  letI : Finite target := finite_target.to_subtype
  exact Finite.of_injective
    (fun f : c ⟶ d => (⟨f.val, incidence_translation_bounds A f⟩ : target))
    (fun f g h => Subtype.ext (congrArg (fun a : target => a.val) h))

/-- The incidence condition is exactly containment of the genuine
translated closed cell, rather than an inequality-only surrogate. -/
theorem incidence_mem_iff_closedCell_subset (c d : IncidenceObject A)
    (a : Fin n → ℤ) :
    (∀ x ∈ incidenceClosedCell A c,
      x + latticeLift a ∈ incidenceClosedCell A d) ↔
    closedCell (augmentedForms A) (translateCell A a c.2.val).val.1
        (translateCell A a c.2.val).val.2 ⊆ incidenceClosedCell A d := by
  rw [show closedCell (augmentedForms A) (translateCell A a c.2.val).val.1
      (translateCell A a c.2.val).val.2 =
      (fun x => x + latticeLift a) '' incidenceClosedCell A c by
    exact (add_image_closedCell _ _ _ _ _ (augmentedForms_latticeLift A a)).symm]
  constructor
  · intro h
    rintro y ⟨x, hx, rfl⟩
    exact h x hx
  · intro h x hx
    exact h ⟨x, hx, rfl⟩

/-- Equal-dimensional incident cells in the universal cover are the
same actual cell. A proper face has strictly smaller intrinsic dimension. -/
theorem cell_subset_closedCell_same_dimension {d : ℕ}
    (c e : Cell (augmentedForms A) d)
    (hce : closedCell (augmentedForms A) c.val.1 c.val.2 ⊆
      closedCell (augmentedForms A) e.val.1 e.val.2) : c = e := by
  obtain ⟨x, hx⟩ := c.property.1
  have hxe := hce (cell_subset_closedCell _ _ _ hx)
  have hxopen : x ∈ cell (augmentedForms A) e.val.1 e.val.2 := by
    by_contra hnot
    obtain ⟨y, hy⟩ := e.property.1
    have hdim := boundary_finrank_lt (augmentedForms A) e.val.1 e.val.2 hy hxe hnot
    rw [integralIndices_eq_of_mem_cell _ _ _ hx, c.property.2, e.property.2] at hdim
    exact (Nat.lt_irrefl d) hdim
  obtain ⟨hlabel, hactive⟩ := cell_indices_unique (augmentedForms A) hx hxopen
  exact Subtype.ext (Prod.ext hlabel hactive)

/-- Every incidence weakly increases actual cell dimension. -/
theorem incidence_dimension_le {c d : IncidenceObject A} (f : c ⟶ d) : c.1 ≤ d.1 := by
  obtain ⟨x, hx⟩ := c.2.val.property.1
  have hxt : x + latticeLift f.val ∈
      cell (augmentedForms A) (translateCell A f.val c.2.val).val.1
        (translateCell A f.val c.2.val).val.2 :=
    (add_mem_cell_iff _ _ _ _ _ (augmentedForms_latticeLift A f.val) x).mpr hx
  have hxd := f.property x (cell_subset_closedCell _ _ _ hx)
  by_cases hxo : x + latticeLift f.val ∈
      cell (augmentedForms A) d.2.val.val.1 d.2.val.val.2
  · have hi := (cell_indices_unique (augmentedForms A) hxt hxo).2
    have hd : c.1 = d.1 := by
      rw [← c.2.val.property.2, ← d.2.val.property.2]
      change Module.finrank ℝ (cellDirection (augmentedForms A)
          (translateCell A f.val c.2.val).val.2) = _
      rw [hi]
    exact hd.le
  · obtain ⟨y, hy⟩ := d.2.val.property.1
    have hd := boundary_finrank_lt (augmentedForms A) d.2.val.val.1 d.2.val.val.2
      hy hxd hxo
    rw [integralIndices_eq_of_mem_cell _ _ _ hxt,
      (translateCell A f.val c.2.val).property.2, d.2.val.property.2] at hd
    exact hd.le

/-- An incidence of equal dimension has zero translation and equal
normalized representatives. -/
theorem incidence_eq_of_dimension_eq {c d : IncidenceObject A} (f : c ⟶ d)
    (hd : c.1 = d.1) : c = d ∧ f.val = 0 := by
  rcases c with ⟨dc, c⟩
  rcases d with ⟨dd, d⟩
  dsimp at hd
  subst dd
  have hclosed := (incidence_mem_iff_closedCell_subset A ⟨dc,c⟩ ⟨dc,d⟩ f.val).mp f.property
  have he : translateCell A f.val c.val = d.val :=
    cell_subset_closedCell_same_dimension A _ _ hclosed
  have hzero : f.val = 0 := by
    have hc := congrArg (coordinateCeilings A) he
    simpa only [coordinateCeilings_translateCell, c.property, d.property, zero_add] using hc
  have hcd : c = d := by
    apply Subtype.ext
    simpa only [hzero, translateCell_zero] using he
  exact ⟨by subst d; rfl, hzero⟩

/-- Every nonidentity incidence strictly increases dimension. In
particular, there are no nontrivial automorphisms or hidden lattice loops. -/
theorem incidence_dimension_lt_of_ne {c d : IncidenceObject A} (f : c ⟶ d)
    (h : c ≠ d) : c.1 < d.1 :=
  lt_of_le_of_ne (incidence_dimension_le A f)
    (fun hd => h (incidence_eq_of_dimension_eq A f hd).1)

instance incidenceEndomorphism_subsingleton (c : IncidenceObject A) :
    Subsingleton (c ⟶ c) := by
  refine ⟨fun f g => Subtype.ext ?_⟩
  rw [(incidence_eq_of_dimension_eq A f rfl).2,
    (incidence_eq_of_dimension_eq A g rfl).2]

/-- Any actual sequence of nonidentity incidences has length bounded by
the ambient lattice rank. This gives the finite bound used by the
normalized bar construction, without truncating a larger category. -/
theorem incidence_strict_chain_length_le (m : ℕ)
    (c : Fin (m+1) → IncidenceObject A)
    (f : ∀ i : Fin m, c i.castSucc ⟶ c i.succ)
    (hne : ∀ i : Fin m, c i.castSucc ≠ c i.succ) : m ≤ n := by
  have bounds : ∀ i : Fin (m+1), i.val ≤ (c i).1 := by
    intro i
    induction i using Fin.induction with
    | zero => exact Nat.zero_le _
    | succ i hi =>
      exact Nat.succ_le_of_lt (lt_of_le_of_lt hi
        (incidence_dimension_lt_of_ne A (f i) (hne i)))
  have step : m ≤ (c (Fin.last m)).1 := bounds (Fin.last m)
  exact step.trans (cell_dimension_le A (c (Fin.last m)).2.val)

end ToricPower.IntegralArrangement

end
