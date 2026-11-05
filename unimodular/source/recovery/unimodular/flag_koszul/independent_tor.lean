module

public import Recovery.Unimodular.FlagKoszul.BarReindex

/-!
# Ordinary derived Tor from independently indexed homogeneous boundaries

Only the positive-basis index is renamed. The algebra, augmentation and
original internal degree remain unchanged. For a geometric index in Type,
ULift puts its basis in the coefficient field's universe, as required by the
ordinary ModuleCat Tor construction. Every differential identity is the
checked actual reduced-bar identity of BarReindex.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

namespace Unimodular.FlagKoszul.BarReindex

open PaperVerification.AugmentedAlgebraBasis

section BasisData
variable {K A I J : Type*} [Field K] [Ring A] [Algebra K A]

theorem unit_transport (e : I ≃ J) (B : Module.Basis (Option I) K A)
    (hunit : B none = 1) : basis e B none = 1 := by rw [basis_none, hunit]

theorem augmentation_transport (e : I ≃ J) (ε : A →ₐ[K] K)
    (B : Module.Basis (Option I) K A) (hε : ∀ i, ε (B (some i)) = 0) :
    ∀ j, ε (basis e B (some j)) = 0 := by
  intro j
  rw [basis_some]
  exact hε _

theorem productCoefficients_reindex_apply (e : I ≃ J)
    (B : Module.Basis (Option I) K A) (a b c : J) :
    productCoefficients (basis e B) a b c =
      productCoefficients B (e.symm a) (e.symm b) (e.symm c) := by
  have h := congrArg (fun z : J →₀ K => z c)
    (productCoefficients_transport e B (e.symm a) (e.symm b))
  simpa only [coefficientEquiv_apply, Equiv.apply_symm_apply] using h.symm

theorem productDegree_transport (e : I ≃ J) (B : Module.Basis (Option I) K A)
    (δ : I → ℕ)
    (hδ : ∀ a b c, productCoefficients B a b c ≠ 0 → δ c = δ a + δ b) :
    ∀ a b c, productCoefficients (basis e B) a b c ≠ 0 →
      (δ ∘ e.symm) c = (δ ∘ e.symm) a + (δ ∘ e.symm) b := by
  intro a b c hc
  rw [productCoefficients_reindex_apply] at hc
  exact hδ _ _ _ hc
end BasisData

section DerivedTor
universe u v
variable {K A J : Type u} {I : Type v} [Field K] [Ring A] [Algebra K A]

/-- An independent index universe is transported by an actual equivalence;
the conclusion is diagonal vanishing in ordinary derived augmentation Tor. -/
theorem hasDiagonalTor_reindex (e : I ≃ J) (ε : A →ₐ[K] K)
    (B : Module.Basis (Option I) K A) (hunit : B none = 1)
    (hε : ∀ i, ε (B (some i)) = 0) (δ : I → ℕ)
    (hδ : ∀ a b c, productCoefficients B a b c ≠ 0 → δ c = δ a + δ b)
    (hpos : ∀ i, 0 < δ i)
    (hbound : ∀ r N, r < N → ∀ z : List I →₀ K,
      z ∈ homogeneousPiece δ r N → PaperVerification.ReducedBarBasis.differential B z = 0 →
      ∃ y ∈ homogeneousPiece δ (r + 1) N,
        -PaperVerification.ReducedBarBasis.differential B y = z) :
    PaperVerification.WeightedBar.HasDiagonalTor ε (basis e B)
      (unit_transport e B hunit) (augmentation_transport e ε B hε)
      (δ ∘ e.symm) (productDegree_transport e B δ hδ) := by
  apply TorCriterion.hasDiagonalTor_of_boundaries ε (basis e B)
    (unit_transport e B hunit) (augmentation_transport e ε B hε)
    (δ ∘ e.symm) (productDegree_transport e B δ hδ) (fun j => hpos (e.symm j))
  intro r N hrN z hz hdz
  let w := (wordEquiv e (K := K)).symm z
  have hew : wordEquiv e w = z := (wordEquiv e).apply_symm_apply z
  have hw : w ∈ homogeneousPiece δ r N := by
    apply (homogeneousPiece_transport e δ r N w).mp
    rw [hew]
    exact hz
  have hdw : PaperVerification.ReducedBarBasis.differential B w = 0 := by
    apply (wordEquiv e).injective
    rw [map_zero, differential_transport, hew]
    exact hdz
  obtain ⟨y, hy, hdy⟩ := hbound r N hrN w hw hdw
  refine ⟨wordEquiv e y, (homogeneousPiece_transport e δ (r + 1) N y).mpr hy, ?_⟩
  rw [← differential_transport, ← map_neg, hdy, hew]

end DerivedTor

section GeometricIndex
universe u
variable {K A : Type u} {I : Type} [Field K] [Ring A] [Algebra K A]

/-- A small geometric basis index works over a coefficient field in any
universe. The genuine algebra and augmentation are not lifted or replaced. -/
theorem hasDiagonalTor_ulift (ε : A →ₐ[K] K)
    (B : Module.Basis (Option I) K A) (hunit : B none = 1)
    (hε : ∀ i, ε (B (some i)) = 0) (δ : I → ℕ)
    (hδ : ∀ a b c, productCoefficients B a b c ≠ 0 → δ c = δ a + δ b)
    (hpos : ∀ i, 0 < δ i)
    (hbound : ∀ r N, r < N → ∀ z : List I →₀ K,
      z ∈ homogeneousPiece δ r N → PaperVerification.ReducedBarBasis.differential B z = 0 →
      ∃ y ∈ homogeneousPiece δ (r + 1) N,
        -PaperVerification.ReducedBarBasis.differential B y = z) :
    PaperVerification.WeightedBar.HasDiagonalTor ε
      (basis (Equiv.ulift.symm : I ≃ ULift.{u} I) B)
      (unit_transport Equiv.ulift.symm B hunit)
      (augmentation_transport Equiv.ulift.symm ε B hε)
      (δ ∘ Equiv.ulift) (productDegree_transport Equiv.ulift.symm B δ hδ) :=
  hasDiagonalTor_reindex Equiv.ulift.symm ε B hunit hε δ hδ hpos hbound

end GeometricIndex

#print axioms hasDiagonalTor_reindex
#print axioms hasDiagonalTor_ulift

end Unimodular.FlagKoszul.BarReindex

#check Unimodular.FlagKoszul.BarReindex.hasDiagonalTor_ulift
