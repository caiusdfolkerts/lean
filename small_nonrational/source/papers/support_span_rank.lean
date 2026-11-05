module
public import Papers.RationalityTenSupportBasics

@[expose] public section
noncomputable section

open Matrix Module Set

namespace Papers.RationalityTen.ChirotopeDensity

/-- The span of a strictly supported face contains no labelled point outside
that face. Consequently a labelled span inclusion implies support inclusion. -/
theorem strictSupport_subset_of_span_le {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (S T : Finset (Fin n)) (a : Fin r → ℝ)
    (ha : StrictSupport p S a)
    (hspan : Submodule.span ℝ (p '' (↑T : Set (Fin n))) ≤
      Submodule.span ℝ (p '' (↑S : Set (Fin n)))) : T ⊆ S := by
  have hker : Submodule.span ℝ (p '' (↑S : Set (Fin n))) ≤ (dotLinear a).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    exact ha.1 i hi
  intro i hi
  by_contra hnot
  have hz : a ⬝ᵥ p i = 0 :=
    hker (hspan (Submodule.subset_span ⟨i, hi, rfl⟩))
  exact (ne_of_gt (ha.2 i hnot)) hz

/-- Adding a label outside a strictly supported face strictly increases its
homogeneous span rank. No affine-general-position hypothesis is required. -/
theorem strictSupport_union_rank_gt {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (S T : Finset (Fin n)) (a : Fin r → ℝ)
    (ha : StrictSupport p S a) (hnot : ¬ T ⊆ S) :
    subsetRank p S < subsetRank p (S ∪ T) := by
  classical
  have hS : Submodule.span ℝ (p '' (↑S : Set (Fin n))) ≤
      Submodule.span ℝ (p '' (↑(S ∪ T) : Set (Fin n))) := by
    apply Submodule.span_mono
    exact Set.image_mono (fun _ hi => Finset.mem_union_left T hi)
  have hT : Submodule.span ℝ (p '' (↑T : Set (Fin n))) ≤
      Submodule.span ℝ (p '' (↑(S ∪ T) : Set (Fin n))) := by
    apply Submodule.span_mono
    exact Set.image_mono (fun _ hi => Finset.mem_union_right S hi)
  change finrank ℝ (Submodule.span ℝ (p '' (↑S : Set (Fin n)))) <
    finrank ℝ (Submodule.span ℝ (p '' (↑(S ∪ T) : Set (Fin n))))
  by_contra hn
  have heq := Submodule.eq_of_le_of_finrank_le hS (Nat.le_of_not_gt hn)
  exact hnot (strictSupport_subset_of_span_le p S T a ha (hT.trans heq.ge))

#print axioms strictSupport_subset_of_span_le
#print axioms strictSupport_union_rank_gt

end Papers.RationalityTen.ChirotopeDensity
