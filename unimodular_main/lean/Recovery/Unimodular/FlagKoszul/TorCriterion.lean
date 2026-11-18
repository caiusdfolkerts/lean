module

public import Recovery.Unimodular.KoszulSupport.PaperVerification.WeightedBarTor

/-!
# Homogeneous cycle witnesses imply diagonal ordinary derived Tor

This is the final homological bridge. The groups are the actual left-derived
augmentation tensor functor, connected to the reduced bar complex by the
checked projective resolution. The vanishing statement retains every
homological and internal degree.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Unimodular.FlagKoszul.TorCriterion

open CategoryTheory CategoryTheory.Limits
open PaperVerification.WeightedBar

universe u
variable {K A I : Type u} [Field K] [Ring A] [Algebra K A]
  (ε : A →ₐ[K] K) (B : Module.Basis (Option I) K A)
  (hunit : B none = 1) (hε : ∀ i, ε (B (some i)) = 0)
  (δ : I → ℕ)
  (hδ : ∀ a b c, PaperVerification.AugmentedAlgebraBasis.productCoefficients B a b c ≠ 0 →
    δ c = δ a + δ b)

theorem zero_length_piece_eq_bot {N : ℕ} (hN : N ≠ 0) :
    piece (K := K) δ 0 N = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro z hz
  change z = 0
  ext L
  by_contra hL
  have h := hz (Finsupp.mem_support_iff.mpr hL)
  have hnil : L = [] := List.length_eq_zero_iff.mp h.1
  have hn : 0 = N := by simpa only [hnil, totalDegree_nil] using h.2
  exact hN hn.symm

/-- Constructed homogeneous boundaries suffice for Koszulness in its ordinary
Tor meaning; no homology or exactness axiom is introduced. -/
theorem hasDiagonalTor_of_boundaries (hpos : ∀ i, 0 < δ i)
    (hbound : ∀ r N, r < N → ∀ z : List I →₀ K,
      z ∈ piece δ r N → PaperVerification.ReducedBarBasis.differential B z = 0 →
      ∃ y ∈ piece δ (r + 1) N,
        -PaperVerification.ReducedBarBasis.differential B y = z) :
    HasDiagonalTor ε B hunit hε δ hδ := by
  apply (hasDiagonalTor_iff ε B hunit hε δ hδ).mpr
  intro r N hrN
  let C := internalComplex ε B hunit hε δ hδ N
  suffices C.ExactAt r from this.isZero_homology
  by_cases hNr : N < r
  · have hbot := piece_eq_bot_of_lt (K := K) δ hpos r N hNr
    haveI : Subsingleton (piece (K := K) δ r N) := by rw [hbot]; infer_instance
    apply HomologicalComplex.ExactAt.of_isZero
    change IsZero (ModuleCat.of K (piece (K := K) δ r N))
    exact ModuleCat.isZero_of_subsingleton _
  cases r with
  | zero =>
    have hbot := zero_length_piece_eq_bot (K := K) δ (Ne.symm hrN)
    haveI : Subsingleton (piece (K := K) δ 0 N) := by rw [hbot]; infer_instance
    apply HomologicalComplex.ExactAt.of_isZero
    change IsZero (ModuleCat.of K (piece (K := K) δ 0 N))
    exact ModuleCat.isZero_of_subsingleton _
  | succ r =>
    have hlt : r + 1 < N := by omega
    rw [C.exactAt_iff' (r + 2) (r + 1) r (by simp) (by simp)]
    rw [CategoryTheory.ShortComplex.moduleCat_exact_iff_range_eq_ker]
    change LinearMap.range (C.d (r + 2) (r + 1)).hom =
      LinearMap.ker (C.d (r + 1) r).hom
    simp only [C, internalComplex_d, ModuleCat.hom_ofHom]
    apply le_antisymm
    · exact LinearMap.range_le_ker_iff.mpr
        (internalDifferential_squared ε B hunit hε δ hδ r N)
    · intro z hz
      have hdz : PaperVerification.ReducedBarBasis.differential B z.1 = 0 := by
        have h := congrArg Subtype.val (LinearMap.mem_ker.mp hz)
        exact neg_eq_zero.mp h
      obtain ⟨y, hy, hdy⟩ := hbound (r + 1) N hlt z.1 z.2 hdz
      refine ⟨⟨y, hy⟩, ?_⟩
      exact Subtype.ext hdy

#print axioms hasDiagonalTor_of_boundaries

end Unimodular.FlagKoszul.TorCriterion
