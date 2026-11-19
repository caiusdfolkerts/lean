module

public import PaperVerification.IsotropicAttractingClosedCells

/-!
# Closed affine cells in the increasing open filtration

The morphism from one ambient open to the next is the actual restriction
inclusion.  Its closed complement is exactly the already constructed affine
cell, with the same original scheme structure and the same structure map.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.IsotropicAttractingCharts

open AlgebraicGeometry CategoryTheory
open PaperVerification.AlternatingForms

variable {K : Type} [Field K] [CharZero K] {n t : ℕ}

/-- The actual inclusion of successive ambient open subsets. -/
def orderedOpenInclusion (m : ℕ) (c₁ c₂ : ℕ) :
    (orderedComplement (K := K) (n := n) (t := t) m c₁ c₂).toScheme ⟶
      (orderedComplement (K := K) (n := n) (t := t) (m+1) c₁ c₂).toScheme :=
  Scheme.homOfLE _ (orderedComplement_mono c₁ c₂ (Nat.le_succ m))

instance orderedOpenInclusion_isOpenImmersion (m : ℕ) (c₁ c₂ : ℕ) :
    IsOpenImmersion (orderedOpenInclusion (K := K) (n := n) (t := t) m c₁ c₂) := by
  unfold orderedOpenInclusion
  infer_instance

theorem orderedOpenInclusion_comp_ι (m : ℕ) (c₁ c₂ : ℕ) :
    orderedOpenInclusion (K := K) (n := n) (t := t) m c₁ c₂ ≫
      (orderedComplement (K := K) (n := n) (t := t) (m+1) c₁ c₂).ι =
        (orderedComplement (K := K) (n := n) (t := t) m c₁ c₂).ι :=
  Scheme.homOfLE_ι _ _

theorem orderedOpenInclusion_range (m : ℕ) (c₁ c₂ : ℕ)
    (x : (orderedComplement (K := K) (n := n) (t := t) (m+1) c₁ c₂).toScheme) :
    x ∈ Set.range (orderedOpenInclusion (K := K) (n := n) (t := t) m c₁ c₂) ↔
      x.val ∈ orderedComplement (K := K) (n := n) (t := t) m c₁ c₂ := by
  constructor
  · rintro ⟨y,rfl⟩
    simpa only [orderedOpenInclusion, Scheme.homOfLE_apply] using y.property
  · intro hx
    refine ⟨⟨x.val,hx⟩,?_⟩
    apply Subtype.ext
    exact Scheme.homOfLE_apply _ _

/-- The actual cell is the closed complement of the preceding ambient
open inside the next one. This is the pair used by the Thom sequence. -/
theorem orderedCellClosedMap_range (i : Fin (pivotCount (t+2) n)) (c₁ c₂ : ℕ) :
    Set.range (orderedCellClosedMap (K := K) i c₁ c₂) =
      (Set.range (orderedOpenInclusion (K := K) (n := n) (t := t) i.val c₁ c₂))ᶜ := by
  ext x
  rw [Set.mem_compl_iff, orderedOpenInclusion_range]
  have hr : x ∈ Set.range (orderedCellClosedMap (K := K) i c₁ c₂) ↔
      x.val ∈ Set.range (filtrationChartToOriginal (K := K)
        (pivotPrefix (t+2) n i.val) (weightOrderedPivots (t+2) n i) c₁ c₂) := by
    rw [← orderedCellClosedMap_comp_ι]
    constructor
    · rintro ⟨y,rfl⟩
      exact ⟨y,rfl⟩
    · rintro ⟨y,hy⟩
      exact ⟨y,Subtype.ext hy⟩
  rw [hr, ordered_filtration_stratum, Set.mem_sdiff]
  change (_ ∧ _) ↔ ¬ ¬ _
  have hx := x.property
  change ¬ x.val ∈ Set.range (filtrationToOriginal (K := K)
    (pivotPrefix (t+2) n (i.val+1)) c₁ c₂) at hx
  simp only [hx, not_false_eq_true, and_true, not_not]

end PaperVerification.IsotropicAttractingCharts
