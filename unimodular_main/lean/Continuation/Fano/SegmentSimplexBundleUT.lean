module

public import Continuation.Fano.SegmentSimplexBundleTwoDimensional
public import Continuation.Fano.SegmentSimplexBundleTriangleFace

/-! The exact absence criterion for genuine unimodular triangular faces. -/

@[expose] public noncomputable section

set_option autoImplicit false

namespace Unimodular.SegmentSimplexBundle

open SegmentSimplex

theorem Q_UT_free_iff {d : ℕ} {a : ℤ}
    (hd : 1 ≤ d) (ha : 0 ≤ a) (had : a ≤ d) :
    (∀ E : Set (Ambient (d + 1)), IsExtreme ℝ (Q d a) E →
      ¬ IsUnimodularTriangle E) ↔ d = 1 ∨ a < d := by
  constructor
  · intro h
    by_cases hd1 : d = 1
    · exact Or.inl hd1
    · by_cases hlt : a < d
      · exact Or.inr hlt
      · have haeq : a = (d : ℤ) := by omega
        have hd2 : 2 ≤ d := by omega
        subst a
        obtain ⟨E, hE, htri⟩ := exists_unimodular_triangle_at_top d hd2
        exact (h E hE htri).elim
  · rintro (rfl | hlt)
    · exact Q_UT_free_dim_two ha had
    · exact Q_UT_free_of_lt hd ha hlt

theorem presentation_UT_free_iff {d : ℕ} {a : ℤ}
    (hd : 1 ≤ d) (ha : 0 ≤ a) (had : a ≤ d) :
    (∀ E : Set (Ambient (d + 1)),
      IsExtreme ℝ (presentation d a hd ha had).carrier E →
      ¬ IsUnimodularTriangle E) ↔ d = 1 ∨ a < d := by
  rw [presentation_carrier]
  exact Q_UT_free_iff hd ha had

end Unimodular.SegmentSimplexBundle

#print axioms Unimodular.SegmentSimplexBundle.Q_UT_free_iff
#print axioms Unimodular.SegmentSimplexBundle.presentation_UT_free_iff
