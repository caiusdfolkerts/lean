module

public import PaperVerification.AlternatingFormsGenericRelativeDimension
public import PaperVerification.OnePlaneProjectiveGeometry
public import PaperVerification.SmoothSchemeKrullDimension

/-!
# The geometric clause of Theorem 1.2 in actual Krull dimension

The dimension is Mathlib's `topologicalKrullDim`, not an equation count used
as a definition. The separate presentation-to-Krull comparison supplies the
required equality for every nonempty scheme on the proved generic open.
-/

@[expose] public section
noncomputable section
open AlgebraicGeometry

namespace PaperVerification.AlternatingForms

variable {K : Type} [Field K] [CharZero K]

/-- General pairs in the full nonempty range define actual smooth nonempty
projective schemes of the expected topological Krull dimension. -/
theorem generic_pair_commonIsotropic_geometry (t n : ℕ)
    (hs : 2 * (t + 2) ≤ n + 1) :
    ∃ Q : MvPolynomial (Fin 2 × StrictPairs n) K, Q ≠ 0 ∧
      (∃ a : (Fin 2 × StrictPairs n) → K, MvPolynomial.aeval a Q ≠ 0) ∧
      ∀ a : (Fin 2 × StrictPairs n) → K, MvPolynomial.aeval a Q ≠ 0 →
        Nonempty (Proj (isotropicProjectiveGrading (t := t) (fun l i ↦ a (l, i)))) ∧
        Smooth (isotropicStructureMap (t := t) (fun l i ↦ a (l, i))) ∧
        topologicalKrullDim
          (Proj (isotropicProjectiveGrading (t := t) (fun l i ↦ a (l, i)))) =
          (((t + 2) * (n + 1 - 2 * (t + 2)) : ℕ) : WithBot ℕ∞) := by
  obtain ⟨Q, hQ, hpoint, hgood⟩ := generic_pair_commonIsotropic_smooth_nonempty (K := K) t n hs
  refine ⟨Q, hQ, hpoint, ?_⟩
  intro a ha
  obtain ⟨hX, hdim⟩ := hgood a ha
  letI := hX
  letI := hdim
  exact ⟨hX, SmoothOfRelativeDimension.smooth
      ((t + 2) * (n + 1 - 2 * (t + 2)))
      (isotropicStructureMap (t := t) (fun l i ↦ a (l, i))),
    SmoothSchemeKrullDimension.topologicalKrullDim_eq
      (d := (t + 2) * (n + 1 - 2 * (t + 2)))
      (isotropicStructureMap (t := t) (fun l i ↦ a (l, i)))⟩

/-- The one-plane boundary has its actual dimension n−1 in every ambient
dimension, including n=1. -/
theorem onePlaneOriginal_geometry (n : ℕ) (hn : 0 < n) :
    Nonempty (Proj (onePlaneOriginalGrading (K := K) n)) ∧
      Smooth (onePlaneOriginalStructureMap (K := K) n) ∧
      topologicalKrullDim (Proj (onePlaneOriginalGrading (K := K) n)) =
        ((n - 1 : ℕ) : WithBot ℕ∞) := by
  obtain ⟨hX, hdim⟩ := onePlaneOriginal_nonempty_smooth (K := K) n hn
  letI := hX
  letI := hdim
  exact ⟨hX, SmoothOfRelativeDimension.smooth (n - 1)
      (onePlaneOriginalStructureMap (K := K) n),
    SmoothSchemeKrullDimension.topologicalKrullDim_eq (d := n - 1)
      (onePlaneOriginalStructureMap (K := K) n)⟩

end PaperVerification.AlternatingForms
