module
public import Papers.RelativeFourCoordinateDensity
public import Papers.CoordinateAxisColumnGluing

@[expose] public section
noncomputable section

open Matrix Module Set Filter Topology
open scoped BigOperators

namespace Papers.RationalityTen.FixedCoordinateFlagDensity

open ChirotopeDensity PlaneRationalization

/-- Two small coordinate groups may be approximated relative to the same
external parameter. The second application retains the first matrix as part
of that parameter, so the rational choices are simultaneous. -/
theorem relative_two_four_coordinate_density {X : Type*} [TopologicalSpace X]
    {m₁ p₁ n₁ m₂ p₂ n₂ : ℕ} (hp₁ : p₁ ≤ 4) (hp₂ : p₂ ≤ 4)
    (A₁ : X → Matrix (Fin m₁) (Fin p₁) ℝ)
    (A₂ : X → Matrix (Fin m₂) (Fin p₂) ℝ) (x : X)
    (hA₁ : ContinuousAt A₁ x) (hA₂ : ContinuousAt A₂ x)
    (S : Set X) (hx : x ∈ closure S)
    (hRat₁ : ∀ y ∈ S, RationalCoordinates (A₁ y))
    (hRat₂ : ∀ y ∈ S, RationalCoordinates (A₂ y))
    (hRanks₁ : ∀ y ∈ S, SameSubsetRanks (A₁ x).col (A₁ y).col)
    (hRanks₂ : ∀ y ∈ S, SameSubsetRanks (A₂ x).col (A₂ y).col)
    (C₁ : Matrix (Fin p₁) (Fin n₁) ℝ) (hC₁ : A₁ x * C₁ = 0)
    (C₂ : Matrix (Fin p₂) (Fin n₂) ℝ) (hC₂ : A₂ x * C₂ = 0) :
    ((x, C₁), C₂) ∈ closure
      {z : (X × Matrix (Fin p₁) (Fin n₁) ℝ) × Matrix (Fin p₂) (Fin n₂) ℝ |
        z.1.1 ∈ S ∧ RationalCoordinates z.1.2 ∧ RationalCoordinates z.2 ∧
        A₁ z.1.1 * z.1.2 = 0 ∧ A₂ z.1.1 * z.2 = 0 ∧
        z.1.2.rank = C₁.rank ∧ z.2.rank = C₂.rank ∧
        PreservesZeroEntries C₁ z.1.2 ∧ PreservesZeroEntries C₂ z.2} := by
  let T : Set (X × Matrix (Fin p₁) (Fin n₁) ℝ) :=
    {z | z.1 ∈ S ∧ RationalCoordinates z.2 ∧ A₁ z.1 * z.2 = 0 ∧
      z.2.rank = C₁.rank ∧ PreservesZeroEntries C₁ z.2}
  have hT : (x, C₁) ∈ closure T :=
    relative_four_coordinate_density hp₁ A₁ x hA₁ S hx hRat₁ hRanks₁ C₁ hC₁
  have h := relative_four_coordinate_density hp₂
    (fun z : X × Matrix (Fin p₁) (Fin n₁) ℝ => A₂ z.1)
    (x, C₁) (hA₂.comp continuous_fst.continuousAt) T hT
    (fun y hy => hRat₂ y.1 hy.1) (fun y hy => hRanks₂ y.1 hy.1) C₂ hC₂
  apply closure_mono ?_ h
  intro z hz
  exact ⟨hz.1.1, hz.1.2.1, hz.2.1, hz.1.2.2.1, hz.2.2.1,
    hz.1.2.2.2.1, hz.2.2.2.1, hz.1.2.2.2.2, hz.2.2.2.2⟩

/-- Nonzero entries of a fixed finite matrix remain nonzero nearby. This open
condition complements the exact zero equations in the density theorem. -/
theorem eventually_nonzero_entries {p n : ℕ}
    (C : Matrix (Fin p) (Fin n) ℝ) :
    ∀ᶠ D in 𝓝 C, ∀ i j, C i j ≠ 0 → D i j ≠ 0 := by
  apply eventually_all.mpr
  intro i
  apply eventually_all.mpr
  intro j
  by_cases hij : C i j = 0
  · exact Filter.Eventually.of_forall (fun _ h => False.elim (h hij))
  · have hc : Continuous (fun D : Matrix (Fin p) (Fin n) ℝ => D i j) :=
      (continuous_apply j).comp (continuous_apply i)
    have hh : ∀ᶠ D in 𝓝 C, D i j ≠ 0 :=
      (hc.continuousAt (x := C)).eventually_ne hij
    exact hh.mono (fun _ h _ => h)

#print axioms relative_two_four_coordinate_density

end Papers.RationalityTen.FixedCoordinateFlagDensity
