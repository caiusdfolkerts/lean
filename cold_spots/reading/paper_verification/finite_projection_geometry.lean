module

public import PaperVerification.FiniteProjection
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Geometric projection transfer

The squared-distance factorization is proved directly from infima of actual
Euclidean squared distances; nearest-point attainment is not assumed. Together
with the equal-theta/equal-infimum theorem, this is the geometric argument in
Proposition 6.1.
-/

noncomputable section

namespace PaperVerification.ColdSpots

variable {h w : ℕ} {G : Type*}

theorem finite_projection_nonempty [Nonempty G]
    (C : G → Set (Fin h → ℝ)) (hC : ∀ g, (C g).Nonempty) :
    (⋃ g, C g).Nonempty := by
  let g : G := Classical.arbitrary G
  obtain ⟨x, hx⟩ := hC g
  exact ⟨x, Set.mem_iUnion.mpr ⟨g, hx⟩⟩

theorem orthogonalGlue_nonempty [Nonempty G]
    (C : G → Set (Fin h → ℝ)) (D : G → Set (Fin w → ℝ))
    (hC : ∀ g, (C g).Nonempty) (hD : ∀ g, (D g).Nonempty) :
    (orthogonalGlue C D).Nonempty := by
  let g : G := Classical.arbitrary G
  obtain ⟨x, hx⟩ := hC g
  obtain ⟨y, hy⟩ := hD g
  exact ⟨Fin.append x y, g, x, hx, y, hy, rfl⟩

/-- Common fibre depth gives the exact geometric identity on the whole slice.
This holds even when none of the relevant infima is attained. -/
theorem projection_depth_factorization [Nonempty G]
    (C : G → Set (Fin h → ℝ)) (D : G → Set (Fin w → ℝ))
    (hC : ∀ g, (C g).Nonempty) (hD : ∀ g, (D g).Nonempty)
    (t₀ : Fin w → ℝ) (ρ : ℝ)
    (hfibre : ∀ g, squaredDepth (D g) t₀ = ρ)
    (x : Fin h → ℝ) :
    squaredDepth (orthogonalGlue C D) (Fin.append x t₀) =
      squaredDepth (⋃ g, C g) x + ρ := by
  apply le_antisymm
  · have hle : squaredDepth (orthogonalGlue C D) (Fin.append x t₀) - ρ ≤
        squaredDepth (⋃ g, C g) x := by
      apply le_csInf ((finite_projection_nonempty C hC).image (fun z => sqDist x z))
      rintro r ⟨u, hu, rfl⟩
      obtain ⟨g, hg⟩ := Set.mem_iUnion.mp hu
      have hinner : squaredDepth (orthogonalGlue C D) (Fin.append x t₀) -
          sqDist x u ≤ squaredDepth (D g) t₀ := by
        apply le_csInf ((hD g).image (fun z => sqDist t₀ z))
        rintro r ⟨v, hv, rfl⟩
        have hb := squaredDepth_le (Fin.append x t₀)
          (show Fin.append u v ∈ orthogonalGlue C D from ⟨g, u, hg, v, hv, rfl⟩)
        rw [sqDist_append_blocks] at hb
        linarith
      rw [hfibre g] at hinner
      linarith
    linarith
  · apply le_csInf ((orthogonalGlue_nonempty C D hC hD).image
      (fun z => sqDist (Fin.append x t₀) z))
    rintro r ⟨z, ⟨g, u, hu, v, hv, rfl⟩, rfl⟩
    change squaredDepth (⋃ g, C g) x + ρ ≤
      sqDist (Fin.append x t₀) (Fin.append u v)
    rw [sqDist_append_blocks]
    have hbase := squaredDepth_le x (Set.mem_iUnion.mpr ⟨g, hu⟩)
    have hdist := squaredDepth_le t₀ hv
    rw [hfibre g] at hdist
    linarith

/-- Exact deepest-point transfer when a deepest point lies on the fixed slice. -/
theorem projection_deepHole_iff_slice [Nonempty G]
    (C : G → Set (Fin h → ℝ)) (D : G → Set (Fin w → ℝ))
    (hC : ∀ g, (C g).Nonempty) (hD : ∀ g, (D g).Nonempty)
    (t₀ : Fin w → ℝ) (ρ : ℝ)
    (hfibre : ∀ g, squaredDepth (D g) t₀ = ρ)
    (hmeet : ∃ x₀ : Fin h → ℝ,
      IsDeepHole (orthogonalGlue C D) (Fin.append x₀ t₀))
    (x : Fin h → ℝ) :
    IsDeepHole (⋃ g, C g) x ↔
      IsDeepHole (orthogonalGlue C D) (Fin.append x t₀) := by
  have hfactor (y : Fin h → ℝ) :=
    projection_depth_factorization C D hC hD t₀ ρ hfibre y
  obtain ⟨x₀, hx₀⟩ := hmeet
  constructor
  · intro hx z
    have hle : squaredDepth (orthogonalGlue C D) (Fin.append x₀ t₀) ≤
        squaredDepth (orthogonalGlue C D) (Fin.append x t₀) := by
      rw [hfactor x₀, hfactor x]
      simpa only [add_comm] using add_le_add_right (hx x₀) ρ
    exact (hx₀ z).trans hle
  · intro hx y
    have hle := hx (Fin.append y t₀)
    rw [hfactor x, hfactor y] at hle
    linarith

theorem sInf_gaussian_range_eq_of_coldSpot {n : ℕ}
    (L : Set (Fin n → ℝ)) (α : ℝ) {x : Fin n → ℝ}
    (hx : IsColdSpot L α x) :
    sInf (Set.range (setGaussian L α)) = setGaussian L α x := by
  have hb : BddBelow (Set.range (setGaussian L α)) :=
    ⟨setGaussian L α x, by rintro r ⟨y, rfl⟩; exact hx y⟩
  apply le_antisymm
  · exact csInf_le hb ⟨x, rfl⟩
  · exact le_csInf ⟨setGaussian L α x, x, rfl⟩ (by
      rintro r ⟨y, rfl⟩
      exact hx y)

/-- The literal quotient-of-minima formula in Proposition 6.1. -/
theorem projection_gaussian_minimum_value [Fintype G]
    (C : G → Set (Fin h → ℝ)) (D : G → Set (Fin w → ℝ))
    (hdisj : Pairwise (fun g g' => Disjoint (C g) (C g')))
    (α c : ℝ) (hc : 0 < c) (t₀ : Fin w → ℝ)
    (hC : ∀ x g, Summable (fun v : C g => Real.exp (-α * sqDist v.val x)))
    (hD : ∀ g, Summable (fun v : D g => Real.exp (-α * sqDist v.val t₀)))
    (hfibre : ∀ g, setGaussian (D g) α t₀ = c)
    (hmeet : ∃ x₀ : Fin h → ℝ,
      IsColdSpot (orthogonalGlue C D) α (Fin.append x₀ t₀)) :
    sInf (Set.range (setGaussian (⋃ g, C g) α)) =
      sInf (Set.range (setGaussian (orthogonalGlue C D) α)) / c := by
  obtain ⟨x₀, hx₀⟩ := hmeet
  have hp : IsColdSpot (⋃ g, C g) α x₀ :=
    (projection_coldSpot_iff_slice C D hdisj α c hc t₀ hC hD hfibre
      ⟨x₀, hx₀⟩ x₀).mpr hx₀
  rw [sInf_gaussian_range_eq_of_coldSpot _ _ hp,
    sInf_gaussian_range_eq_of_coldSpot _ _ hx₀,
    projection_gaussian_factorization C D hdisj α c x₀ t₀ (hC x₀) hD hfibre]
  field_simp [hc.ne'] <;> ring

/-- The analytic and geometric transfers combine without assuming that the
projection already has the desired minimum set. -/
theorem projection_coldSpot_iff_deepHole [Fintype G] [Nonempty G]
    (C : G → Set (Fin h → ℝ)) (D : G → Set (Fin w → ℝ))
    (hdisj : Pairwise (fun g g' => Disjoint (C g) (C g')))
    (hCne : ∀ g, (C g).Nonempty) (hDne : ∀ g, (D g).Nonempty)
    (α c ρ : ℝ) (hc : 0 < c) (t₀ : Fin w → ℝ)
    (hC : ∀ x g, Summable (fun v : C g => Real.exp (-α * sqDist v.val x)))
    (hD : ∀ g, Summable (fun v : D g => Real.exp (-α * sqDist v.val t₀)))
    (hGaussian : ∀ g, setGaussian (D g) α t₀ = c)
    (hDepth : ∀ g, squaredDepth (D g) t₀ = ρ)
    (hL : ∀ z, IsColdSpot (orthogonalGlue C D) α z ↔ IsDeepHole (orthogonalGlue C D) z)
    (hmeet : ∃ x₀ : Fin h → ℝ,
      IsDeepHole (orthogonalGlue C D) (Fin.append x₀ t₀))
    (x : Fin h → ℝ) :
    IsColdSpot (⋃ g, C g) α x ↔ IsDeepHole (⋃ g, C g) x := by
  have hmeetCold : ∃ x₀ : Fin h → ℝ,
      IsColdSpot (orthogonalGlue C D) α (Fin.append x₀ t₀) := by
    obtain ⟨x₀, hx₀⟩ := hmeet
    exact ⟨x₀, (hL _).mpr hx₀⟩
  rw [projection_coldSpot_iff_slice C D hdisj α c hc t₀ hC hD hGaussian hmeetCold,
    hL, projection_deepHole_iff_slice C D hCne hDne t₀ ρ hDepth hmeet]

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.projection_depth_factorization
#print axioms PaperVerification.ColdSpots.projection_deepHole_iff_slice
#print axioms PaperVerification.ColdSpots.projection_gaussian_minimum_value
#print axioms PaperVerification.ColdSpots.projection_coldSpot_iff_deepHole

