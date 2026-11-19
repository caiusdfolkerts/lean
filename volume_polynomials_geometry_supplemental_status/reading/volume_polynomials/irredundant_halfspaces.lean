module

public import VolumePolynomials.PolytopeFacetGeometry
public import Mathlib.Data.Nat.Find

@[expose] public section
set_option autoImplicit false

/-!
# Removing redundant inequalities from a finite halfspace representation

The finite family of inequalities is reduced by a minimum-cardinality argument.
Its body is preserved exactly. No assumption about the original presentation
being irredundant, or about every listed supporting face being a facet, is made.
-/

noncomputable section
open Set
open scoped RealInnerProductSpace

namespace OAI.Paper092.HPolytope

variable {d : ℕ} {ι : Type*} [Fintype ι] (P : HPolytope d ι)

def IsEssential (i : ι) : Prop :=
  ¬ ∀ x : Euclidean d,
    (∀ j, j ≠ i → ⟪P.normal j, x⟫ ≤ P.offset j) → ⟪P.normal i, x⟫ ≤ P.offset i

theorem vectorSpan_face_of_essential (i : ι) (hi : P.IsEssential i) :
    vectorSpan ℝ (P.face i) = normalHyperplane (P.normal i) := by
  first
  | apply le_antisymm
    · rw [vectorSpan_def]
      apply Submodule.span_le.mpr
      rintro _ ⟨x, hx, y, hy, rfl⟩
      apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
      change ⟪P.normal i, x - y⟫ = 0
      rw [inner_sub_right, hx.2, hy.2, sub_self]
    · intro v hv
      obtain ⟨x, hx, _⟩ := P.exists_strict_face_point_of_essential i hi
      have hxspan := subset_affineSpan ℝ (P.face i) hx
      have hvinner := Submodule.mem_orthogonal_singleton_iff_inner_right.mp hv
      have hyspan : x + v ∈ affineSpan ℝ (P.face i) := by
        change x + v ∈ (affineSpan ℝ (P.face i) : Set (Euclidean d))
        rw [P.affineSpan_face_of_essential i hi]
        change ⟪P.normal i, x + v⟫ = P.offset i
        rw [inner_add_right, hx.2, hvinner, add_zero]
      have hvdir := (affineSpan ℝ (P.face i)).vsub_mem_direction hyspan hxspan
      simpa only [direction_affineSpan, vsub_eq_sub, add_sub_cancel_left] using hvdir

theorem finrank_face_of_essential (i : ι) (hi : P.IsEssential i) :
    Module.finrank ℝ (vectorSpan ℝ (P.face i)) = d - 1 := by
  first
  | rw [P.vectorSpan_face_of_essential i hi]
    apply normalHyperplane_finrank
    intro h
    simpa [h] using P.normal_unit i

theorem face_eq_exposedFace (i : ι) (hne : (P.face i).Nonempty) :
    P.face i = exposedFace P.body (P.normal i) := by
  first
  | ext x
    constructor
    · intro hx
      refine ⟨hx.1, ?_⟩
      intro y hy
      change ⟪P.normal i, y⟫ ≤ ⟪P.normal i, x⟫
      rw [hx.2]
      exact hy i
    · intro hx
      obtain ⟨y, hy⟩ := hne
      refine ⟨hx.1, le_antisymm (hx.1 i) ?_⟩
      have h := hx.2 y hy.1
      change ⟪P.normal i, y⟫ ≤ ⟪P.normal i, x⟫ at h
      rwa [hy.2] at h

theorem offset_eq_support (i : ι) (hne : (P.face i).Nonempty) :
    P.offset i = SupportGeometry.support P.body (innerSL ℝ (P.normal i)) := by
  first
  | obtain ⟨x, hx⟩ := hne
    apply le_antisymm
    · have h := SupportGeometry.le_support P.compact (innerSL ℝ (P.normal i)) hx.1
      change ⟪P.normal i, x⟫ ≤ SupportGeometry.support P.body (innerSL ℝ (P.normal i)) at h
      rwa [hx.2] at h
    · exact SupportGeometry.support_le P.body_nonempty _ (fun y hy => hy i)

/-- A subset of the original inequalities with exactly the original body. -/
def RepresentsBody (s : Finset ι) : Prop :=
  ∀ x : Euclidean d, (∀ i ∈ s, ⟪P.normal i, x⟫ ≤ P.offset i) ↔ x ∈ P.body

theorem representsBody_univ : P.RepresentsBody Finset.univ := by
  first
  | intro x
    simp [body]

def restrict (s : Finset ι) (hs : P.RepresentsBody s) : HPolytope d s where
  normal i := P.normal i.val
  offset i := P.offset i.val
  normal_unit i := P.normal_unit i.val
  compact := by
    first
    | convert P.compact using 1
      ext x
      constructor
      · intro hx
        exact (hs x).mp (fun i hi => hx ⟨i, hi⟩)
      · intro hx i
        exact (hs x).mpr hx i.val i.property
  strict_feasible := by
    first
    | obtain ⟨x, hx⟩ := P.strict_feasible
      exact ⟨x, fun i => hx i.val⟩
  distinct := by
    first
    | intro i j h
      apply Subtype.ext
      exact P.distinct h

@[simp] theorem restrict_body (s : Finset ι) (hs : P.RepresentsBody s) :
    (P.restrict s hs).body = P.body := by
  first
  | ext x
    constructor
    · intro hx
      exact (hs x).mp (fun i hi => hx ⟨i, hi⟩)
    · intro hx i
      exact (hs x).mpr hx i.val i.property

/-- A finite halfspace presentation always contains an irredundant subfamily. -/
theorem exists_irredundant_restriction :
    ∃ s : Finset ι, ∃ hs : P.RepresentsBody s,
      ∀ i : s, (P.restrict s hs).IsEssential i := by
  first
  | classical
    have hex : ∃ k : ℕ, ∃ s : Finset ι, P.RepresentsBody s ∧ s.card = k :=
      ⟨Finset.univ.card, Finset.univ, P.representsBody_univ, rfl⟩
    obtain ⟨s, hs, hcard⟩ := Nat.find_spec hex
    have hminimal : ∀ r : Finset ι, P.RepresentsBody r → s.card ≤ r.card := by
      intro r hr
      rw [hcard]
      exact Nat.find_min' hex ⟨r, hr, rfl⟩
    refine ⟨s, hs, ?_⟩
    intro i hi
    change ∀ x : Euclidean d,
      (∀ j : s, j ≠ i → ⟪P.normal j.val, x⟫ ≤ P.offset j.val) →
        ⟪P.normal i.val, x⟫ ≤ P.offset i.val at hi
    have herase : P.RepresentsBody (s.erase i.val) := by
      intro x
      constructor
      · intro hx
        apply (hs x).mp
        intro j hj
        by_cases hji : j = i.val
        · subst j
          apply hi x
          intro k hki
          exact hx k.val (Finset.mem_erase.mpr
            ⟨fun h => hki (Subtype.ext h), k.property⟩)
        · exact hx j (Finset.mem_erase.mpr ⟨hji, hj⟩)
      · intro hx j hj
        exact (hs x).mpr hx j (Finset.mem_of_mem_erase hj)
    exact (not_lt_of_ge (hminimal _ herase)) (Finset.card_erase_lt_of_mem i.property)

theorem exists_irredundant :
    ∃ k : ℕ, ∃ Q : HPolytope d (Fin k),
      Q.body = P.body ∧ ∀ i, Q.IsEssential i := by
  first
  | classical
    obtain ⟨s, hs, he⟩ := P.exists_irredundant_restriction
    let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
    refine ⟨Fintype.card s, (P.restrict s hs).reindex e, ?_, ?_⟩
    · rw [reindex_body, restrict_body]
    · intro i hred
      apply he (e i)
      intro x hx
      apply hred x
      intro j hji
      apply hx (e j)
      exact fun h => hji (e.injective h)

end OAI.Paper092.HPolytope
