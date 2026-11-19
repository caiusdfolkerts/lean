module

public import PaperVerification.FiniteProjectionGeometry
public import PaperVerification.GaussianLaplace

@[expose] public section

/-!
# The general finite-profile projection transfer

This file proves the statement of Proposition 6.1 at the level of actual finite
disjoint product decompositions. All point sets, Gaussian series, and squared
distances are the original geometric objects. Convergence is an explicit input
for the component series. No projected minimizer or fibre depth is assumed.

The final geometric implication uses the general discrete Laplace principle:
equal fibre theta functions for every positive parameter have equal infima of
their squared-distance families. It does not require nearest-point attainment.
-/

noncomputable section

namespace PaperVerification.ColdSpots

variable {h w : ℕ} {G : Type*}

theorem setGaussian_pos_of_nonempty {n : ℕ}
    (S : Set (Fin n → ℝ)) (α : ℝ) (x : Fin n → ℝ) (hS : S.Nonempty)
    (hs : Summable (fun z : S => Real.exp (-α * sqDist z.val x))) :
    0 < setGaussian S α x := by
  obtain ⟨z, hz⟩ := hS
  exact hs.tsum_pos (fun _ => (Real.exp_pos _).le) ⟨z, hz⟩ (Real.exp_pos _)

/-- The infimum in the geometric definition is the same infimum used in the
Laplace theorem. The order of the two points is reconciled by symmetry. -/
theorem squaredDepth_eq_subtype_sInf {n : ℕ}
    (S : Set (Fin n → ℝ)) (x : Fin n → ℝ) :
    squaredDepth S x = sInf (Set.range (fun z : S => sqDist z.val x)) := by
  unfold squaredDepth
  congr 1
  ext r
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨z, hz⟩, sqDist_comm z x⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z.val, z.property, sqDist_comm x z.val⟩

/-- Equality of the complete Gaussian functions determines the actual nearest
squared distance, even for nonclosed sets for which the infimum is not attained. -/
theorem squaredDepth_eq_of_gaussian_eq {n m : ℕ}
    (S : Set (Fin n → ℝ)) (T : Set (Fin m → ℝ))
    (x : Fin n → ℝ) (y : Fin m → ℝ)
    (hS : S.Nonempty) (hT : T.Nonempty)
    {α₀ : ℝ} (hα₀ : 0 < α₀)
    (hs : Summable (fun z : S => Real.exp (-α₀ * sqDist z.val x)))
    (ht : Summable (fun z : T => Real.exp (-α₀ * sqDist z.val y)))
    (heq : ∀ α : ℝ, 0 < α → setGaussian S α x = setGaussian T α y) :
    squaredDepth S x = squaredDepth T y := by
  letI : Nonempty S := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  letI : Nonempty T := ⟨⟨hT.choose, hT.choose_spec⟩⟩
  rw [squaredDepth_eq_subtype_sInf, squaredDepth_eq_subtype_sInf]
  exact gaussian_infimum_eq_of_equal_sums
    (fun z : S => sqDist z.val x) (fun z : T => sqDist z.val y)
    (fun _ => sqDist_nonneg _ _) (fun _ => sqDist_nonneg _ _)
    hα₀ hs ht heq

/-- The common fibre depth is a conclusion of theta equality, not a hypothesis
added to the geometric part of the projection theorem. -/
theorem projection_common_fibre_depth [Nonempty G]
    (D : G → Set (Fin w → ℝ)) (hDne : ∀ g, (D g).Nonempty)
    (t₀ : Fin w → ℝ) (c : ℝ → ℝ)
    (hD : ∀ g, Summable (fun v : D g => Real.exp (-sqDist v.val t₀)))
    (hfibre : ∀ α : ℝ, 0 < α → ∀ g, setGaussian (D g) α t₀ = c α) :
    ∃ ρ : ℝ, ∀ g, squaredDepth (D g) t₀ = ρ := by
  let g₀ : G := Classical.arbitrary G
  refine ⟨squaredDepth (D g₀) t₀, fun g => ?_⟩
  apply squaredDepth_eq_of_gaussian_eq (D g) (D g₀) t₀ t₀ (hDne g) (hDne g₀)
    (α₀ := 1) (by norm_num)
  · simpa only [neg_mul, one_mul] using hD g
  · simpa only [neg_mul, one_mul] using hD g₀
  · intro α hα
    exact (hfibre α hα g).trans (hfibre α hα g₀).symm

/-- Proposition 6.1 for a finite disjoint orthogonal product decomposition,
with component convergence explicit. The result includes the exact universal
minimum set, the quotient of minimum values, and the full deep-hole assertion. -/
theorem finite_profile_projection_transfer [Fintype G] [Nonempty G]
    (C : G → Set (Fin h → ℝ)) (D : G → Set (Fin w → ℝ))
    (hdisj : Pairwise (fun g g' => Disjoint (C g) (C g')))
    (hCne : ∀ g, (C g).Nonempty) (hDne : ∀ g, (D g).Nonempty)
    (t₀ : Fin w → ℝ) (c : ℝ → ℝ)
    (hC : ∀ α : ℝ, 0 < α → ∀ x g,
      Summable (fun v : C g => Real.exp (-α * sqDist v.val x)))
    (hD : ∀ α : ℝ, 0 < α → ∀ g,
      Summable (fun v : D g => Real.exp (-α * sqDist v.val t₀)))
    (hfibre : ∀ α : ℝ, 0 < α → ∀ g, setGaussian (D g) α t₀ = c α)
    (K : Set (Fin (h + w) → ℝ))
    (hK : ∀ α : ℝ, 0 < α → ∀ z,
      IsColdSpot (orthogonalGlue C D) α z ↔ z ∈ K)
    (hmeet : ∃ x₀ : Fin h → ℝ, Fin.append x₀ t₀ ∈ K) :
    (∀ α : ℝ, 0 < α → ∀ x : Fin h → ℝ,
      IsColdSpot (⋃ g, C g) α x ↔ Fin.append x t₀ ∈ K) ∧
    (∀ α : ℝ, 0 < α →
      sInf (Set.range (setGaussian (⋃ g, C g) α)) =
        sInf (Set.range (setGaussian (orthogonalGlue C D) α)) / c α) ∧
    ((∀ z, z ∈ K ↔ IsDeepHole (orthogonalGlue C D) z) →
      ∀ x : Fin h → ℝ,
        IsDeepHole (⋃ g, C g) x ↔ Fin.append x t₀ ∈ K) := by
  let g₀ : G := Classical.arbitrary G
  have hc (α : ℝ) (hα : 0 < α) : 0 < c α := by
    rw [← hfibre α hα g₀]
    exact setGaussian_pos_of_nonempty (D g₀) α t₀ (hDne g₀) (hD α hα g₀)
  refine ⟨projection_universal_minimum_set C D hdisj c hc t₀ hC hD hfibre K hK hmeet,
    ?_, ?_⟩
  · intro α hα
    apply projection_gaussian_minimum_value C D hdisj α (c α) (hc α hα) t₀
      (hC α hα) (hD α hα) (hfibre α hα)
    obtain ⟨x₀, hx₀⟩ := hmeet
    exact ⟨x₀, (hK α hα _).mpr hx₀⟩
  · intro hKdeep x
    obtain ⟨ρ, hρ⟩ := projection_common_fibre_depth D hDne t₀ c (by
      intro g
      simpa only [neg_mul, one_mul] using hD 1 (by norm_num) g) hfibre
    have hmeetDeep : ∃ x₀ : Fin h → ℝ,
        IsDeepHole (orthogonalGlue C D) (Fin.append x₀ t₀) := by
      obtain ⟨x₀, hx₀⟩ := hmeet
      exact ⟨x₀, (hKdeep _).mp hx₀⟩
    exact (projection_deepHole_iff_slice C D hCne hDne t₀ ρ hρ hmeetDeep x).trans
      (hKdeep _).symm

/-- The all-positive-parameter cold-spot/deep-hole equivalence on the projection.
Only the original lattice's equivalence and a slice intersection are assumed. -/
theorem projection_universal_coldSpot_iff_deepHole [Fintype G] [Nonempty G]
    (C : G → Set (Fin h → ℝ)) (D : G → Set (Fin w → ℝ))
    (hdisj : Pairwise (fun g g' => Disjoint (C g) (C g')))
    (hCne : ∀ g, (C g).Nonempty) (hDne : ∀ g, (D g).Nonempty)
    (t₀ : Fin w → ℝ) (c : ℝ → ℝ)
    (hC : ∀ α : ℝ, 0 < α → ∀ x g,
      Summable (fun v : C g => Real.exp (-α * sqDist v.val x)))
    (hD : ∀ α : ℝ, 0 < α → ∀ g,
      Summable (fun v : D g => Real.exp (-α * sqDist v.val t₀)))
    (hfibre : ∀ α : ℝ, 0 < α → ∀ g, setGaussian (D g) α t₀ = c α)
    (hL : ∀ α : ℝ, 0 < α → ∀ z,
      IsColdSpot (orthogonalGlue C D) α z ↔ IsDeepHole (orthogonalGlue C D) z)
    (hmeet : ∃ x₀ : Fin h → ℝ,
      IsDeepHole (orthogonalGlue C D) (Fin.append x₀ t₀)) :
    ∀ α : ℝ, 0 < α → ∀ x : Fin h → ℝ,
      IsColdSpot (⋃ g, C g) α x ↔ IsDeepHole (⋃ g, C g) x := by
  have ht := finite_profile_projection_transfer C D hdisj hCne hDne t₀ c
    hC hD hfibre {z | IsDeepHole (orthogonalGlue C D) z} hL hmeet
  intro α hα x
  exact (ht.1 α hα x).trans (ht.2.2 (fun _ => Iff.rfl) x).symm

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.squaredDepth_eq_of_gaussian_eq
#print axioms PaperVerification.ColdSpots.projection_common_fibre_depth
#print axioms PaperVerification.ColdSpots.finite_profile_projection_transfer
#print axioms PaperVerification.ColdSpots.projection_universal_coldSpot_iff_deepHole

