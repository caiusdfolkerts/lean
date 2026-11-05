module
public import VolumeVerification.ProjectionLinearRelations
@[expose] public section
set_option autoImplicit false

/-!
# From the mixed-area identities to the full-dimensional obstruction

This theorem removes the finite-cone, measurable-selection and moment-matrix
interfaces from the geometric proof.  Its remaining geometric inputs are
the actual centered mixed-area measures, their mixed-volume pairing, and
the equality-rigidity implications.  Those implications must still be proved
for convex bodies; they are not declared as axioms here.
-/
namespace VolumeVerification.ProjectionMeasureReduction
open scoped BigOperators ENNReal Matrix
open MeasureTheory Set
open ProjectionLinearRelations
open EdgeMoments

variable {Ω : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]

theorem impossible_measure_data {n : ℕ} (hn : 5 ≤ n)
    (P Z : Matrix (Fin n) (Fin n) ℝ)
    (hsym : ∀ i j, P i j = P j i)
    (hdiag : ∀ i, P i i = 0)
    (hpos : ∀ i j, i ≠ j → 0 < P i j)
    (hrank : P.rank = 3)
    (μ : Fin n → Measure Ω) [∀ i, IsFiniteMeasure (μ i)]
    (φ : Ω → Fin n → ℝ) (hφ : Continuous φ)
    (hpair : ∀ i j, P i j = ∫ x, |coordinate Z φ j x| ∂μ i)
    (hcenter : ∀ i j, ∫ x, φ x j ∂μ i = 0)
    (hrelations : ∀ w : Fin n → ℝ, P *ᵥ w = 0 →
      ∀ s, MeasurableSet s → ∑ i, w i*(μ i).real s = 0)
    (hrigidity : ∀ w : Fin n → ℝ, P *ᵥ w = 0 →
      ∃ l : Fin n → ℝ, ∀ i, ∀ᵐ x ∂μ i,
        (∑ j, w j*|coordinate Z φ j x|) = ∑ j, l j*φ x j) :
    False := by
  classical
  obtain ⟨N,rfl⟩ : ∃ N, n = N+3 := ⟨n-3,by omega⟩
  obtain ⟨W,hWrank,hWker,hWP⟩ := exists_relation_matrix P hrank
  choose L hL using fun k : Fin (N+3-3) =>
    hrigidity (W k) (rows_in_kernel P hsym W hWP k)
  obtain ⟨σ,r,_,hr,hcone⟩ :=
    MarkedPolynomialCone.exists_sorted_rays P hsym hdiag hpos hrank
  let Q := P.submatrix σ σ
  let Z' := Z.submatrix σ id
  let W' := W.submatrix id σ
  let μ' : Fin (N+3) → Measure Ω := fun i => μ (σ i)
  letI : ∀ i, IsFiniteMeasure (μ' i) := fun i => inferInstance
  let μtotal : Measure Ω := ∑ i, μ' i
  letI : IsFiniteMeasure μtotal := by
    dsimp [μtotal]
    infer_instance
  have hdom : ∀ i, μ' i ≤ μtotal := by
    intro i
    exact Finset.single_le_sum (fun j _ => Measure.zero_le _) (Finset.mem_univ i)
  have hWr : ∀ k s, MeasurableSet s →
      ∑ i, W' k i*(μ' i).real s = 0 := by
    intro k s hs
    change (∑ i, W k (σ i)*(μ (σ i)).real s) = 0
    exact (sum_permute σ (fun i => W k i * (μ i).real s)).trans
      (hrelations (W k) (rows_in_kernel P hsym W hWP k) s hs)
  have hspan : ∀ y : Fin (N+3) → ℝ,
      (∀ i, 0 ≤ y i) → W' *ᵥ y = 0 →
      ∃ c : Fin (N+3) → ℝ, (∀ e, 0 ≤ c e) ∧ ∑ e, c e • r e = y := by
    intro y hy hWy
    apply (hcone y).mpr
    refine ⟨hy,?_⟩
    exact (reindex_relation_matrix P W hWker σ y).mp hWy
  obtain ⟨ν,hν,hdecomp⟩ :=
    ConeMeasureDecomposition.decompose_positive_measure_vector
      μtotal μ' hdom W' r (ray_nonnegative r hr) hspan hWr
  letI : ∀ e, IsFiniteMeasure (ν e) := hν
  have hW'rank : W'.rank = N+3-3 := by
    dsimp [W']
    simpa using (Matrix.rank_submatrix W (Equiv.refl _) σ).trans hWrank
  have hQdiag : ∀ i, Q i i = 0 := fun i => hdiag _
  have hQpos : ∀ i j, i ≠ j → 0 < Q i j := by
    intro i j hij
    exact hpos _ _ (fun h => hij (σ.injective h))
  have hcoord : ∀ j x, coordinate Z' φ j x = coordinate Z φ (σ j) x := by
    intro j x
    rfl
  have hQpair : ∀ i j, Q i j = ∫ x, |coordinate Z' φ j x| ∂μ' i := by
    intro i j
    simpa only [Q, μ', Matrix.submatrix_apply, hcoord] using hpair (σ i) (σ j)
  have hQcenter : ∀ i j, ∫ x, φ x j ∂μ' i = 0 :=
    fun i j => hcenter (σ i) j
  have hrig : ∀ i, ∀ᵐ x ∂μ' i,
      W' *ᵥ (fun j => |coordinate Z' φ j x|) = L *ᵥ φ x := by
    intro i
    have hall : ∀ᵐ x ∂μ (σ i), ∀ k : Fin (N+3-3),
        (∑ j, W k j*|coordinate Z φ j x|) =
          ∑ j, L k j*φ x j :=
      ae_all_iff.mpr fun k => hL k (σ i)
    filter_upwards [hall] with x hx
    ext k
    change (∑ j, W k (σ j)*|coordinate Z' φ j x|) = _
    simp only [hcoord]
    simpa only [Matrix.mulVec, dotProduct] using
      (sum_permute σ (fun j => W k j * |coordinate Z φ j x|)).trans (hx k)
  exact PolygonMeasureObstruction.impossible_positive_polygon_measure_data
    hn μ' ν r hr hdecomp Q Z' φ hφ hQdiag hQpos hQpair hQcenter
    W' hW'rank L hrig

end VolumeVerification.ProjectionMeasureReduction

