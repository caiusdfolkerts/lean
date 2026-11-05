module
public import Projection.Normalization.Transforms
public import Projection.Normalization.MinorBounds
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.Sequences

/-!
# Compactification of actual marked mixed-volume arrays

For every `0 < k ≤ n`, the marked image is closed. Moreover, every point in
that image has a representation whose repeated body has affine dimension at
least `n - k + 1`. These assertions concern the actual mixed volume, compact
convex bodies, and segment vectors from `Projection.Topology`.

To obtain Theorem 3.1 in its coordinate-projection form, the remaining
identification is between this marked image and the closure of coordinate
projection arrays. That identification uses coordinate extrusion and density
of invertible marked frames; neither is encoded as a hypothesis here.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set Metric Module MeasureTheory Filter
open scoped Topology Pointwise

namespace RankThreeProjection
open VolumePolynomials

/-- Arrays obtained from actual bodies and arbitrary actual segment marks. -/
def markedArrayLocus (n k : ℕ) : Set (Deleted n k → ℝ) :=
  Set.range (fun q : Body n × (Fin n → Space n) => allMarkedArray (k := k) q.1 q.2)

/-- The same marked construction with a repeated body having nonempty ambient
interior. No condition is imposed on the marked vectors. -/
def fullMarkedLocus (n k : ℕ) : Set (Deleted n k → ℝ) :=
  {P | ∃ (K : Body n) (U : Fin n → Space n),
    (interior (K : Set (Space n))).Nonempty ∧ allMarkedArray K U = P}

/-- A positive thickening by a body with interior has nonempty interior even
when the original body is lower dimensional. -/
theorem interior_body_thickening {n : ℕ} (K Q : Body n)
    (hQ : (0 : Space n) ∈ interior (Q : Set (Space n))) {t : ℝ} (ht : 0 < t) :
    (interior ((K + t • Q : Body n) : Set (Space n))).Nonempty := by
  obtain ⟨x, hx⟩ := K.nonempty
  have htQ : (0 : Space n) ∈ interior ((t • Q : Body n) : Set (Space n)) := by
    rw [ConvexBody.coe_smul, interior_smul₀ ht.ne']
    exact ⟨0, hQ, smul_zero t⟩
  refine ⟨x, ?_⟩
  change x ∈ interior ((K : Set (Space n)) + ((t • Q : Body n) : Set (Space n)))
  exact subset_interior_add_right (Set.mem_add.mpr ⟨x, hx, 0, htQ, add_zero x⟩)

/-- Actual convex bodies with nonempty ambient interior are dense in all
nonempty compact convex bodies, in every dimension. -/
theorem dense_full_bodies (n : ℕ) :
    Dense {K : Body n | (interior (K : Set (Space n))).Nonempty} := by
  rw [Metric.dense_iff]
  intro K ε hε
  obtain ⟨Q, _hfinite, hQ⟩ := exists_finiteHull_with_zero_interior (E := Space n)
  have hc : Continuous (fun t : ℝ => K + t • Q) := by fun_prop
  obtain ⟨δ, hδ, hnear⟩ := Metric.continuousAt_iff.mp (hc.continuousAt (x := (0 : ℝ))) ε hε
  have ht : 0 < δ / 2 := half_pos hδ
  have hdist : dist (δ / 2) (0 : ℝ) < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos ht]
    exact half_lt_self hδ
  refine ⟨K + (δ / 2) • Q, ?_, interior_body_thickening K Q hQ ht⟩
  simpa only [mem_ball, body_zero_smul, add_zero] using hnear hdist

theorem marked_mem_closure_fullMarked {n k : ℕ} (K : Body n) (U : Fin n → Space n) :
    allMarkedArray (k := k) K U ∈ closure (fullMarkedLocus n k) := by
  let f : Body n → Deleted n k → ℝ := fun L => allMarkedArray L U
  have hf : Continuous f := by
    simpa only [f, Function.comp_def, id_eq] using
      (continuous_allMarkedArray (n := n) (k := k)).comp
        (continuous_id.prodMk (continuous_const : Continuous (fun _ : Body n => U)))
  exact map_mem_closure (f := f) (x := K) hf ((dense_full_bodies n) K)
    (fun L hL => ⟨L, U, hL, rfl⟩)

/-- Uniform bounds for all full-dimensional marked representations whose
coefficients have one common upper bound. -/
theorem uniform_normalized_representations (n k : ℕ) (hk : 0 < k) (hkn : k ≤ n)
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ ρ > 0, ∃ R D : ℝ, ∀ (K : Body n) (U : Fin n → Space n),
      (interior (K : Set (Space n))).Nonempty →
      (∀ I : Deleted n k, allMarkedArray K U I ≤ B) →
      ∃ (L : Body n) (V : Fin n → Space n) (s : Finset (Fin n)),
        s.card < k ∧ coordinateDisk s ρ ⊆ (L : Set (Space n)) ∧
        (L : Set (Space n)) ⊆ closedBall 0 R ∧ ‖V‖ ≤ D ∧
        allMarkedArray (k := k) L V = allMarkedArray K U := by
  obtain ⟨ρ, hρ, hAffine⟩ := exists_affine_normalized_marked_pairs n
  refine ⟨ρ, hρ, (n : ℝ), max 1 (((n - k).factorial : ℝ) * B / ρ ^ (n - k)), ?_⟩
  intro K U hfull hcoeff
  obtain ⟨L, V, hinner, houter, heq⟩ := hAffine k hk K U hfull
  have hcoeff' : ∀ I : Deleted n k, allMarkedArray L V I ≤ B := by
    intro I
    rw [heq]
    exact hcoeff I
  obtain ⟨N, W, s, hs, hdisk, hball, hmarks, harray⟩ :=
    normalize_marked_pair hk L V hinner houter
      (minorMaximum_bound hkn L V hρ hB hinner hcoeff')
  exact ⟨N, W, s, hs, hdisk, hball, hmarks, harray.trans heq⟩

/-- A convergent sequence of marked arrays with full-dimensional repeated
bodies has a marked limit retaining at least `n - k + 1` affine dimensions. -/
theorem fullMarked_limit {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    (p : ℕ → Deleted n k → ℝ) (P : Deleted n k → ℝ)
    (hp : Tendsto p atTop (𝓝 P)) (hfull : ∀ m, p m ∈ fullMarkedLocus n k) :
    ∃ (K : Body n) (U : Fin n → Space n),
      n - k + 1 ≤ bodyDimension K ∧ allMarkedArray K U = P := by
  obtain ⟨B, hBpos, hB⟩ := (Metric.isBounded_range_of_tendsto p hp).exists_pos_norm_le
  obtain ⟨ρ, hρ, R, D, hnormal⟩ := uniform_normalized_representations n k hk hkn B hBpos.le
  apply marked_limit_of_bounded_representations hkn hρ p P hp
  intro m
  obtain ⟨K, U, hK, heq⟩ := hfull m
  have hcoeff : ∀ I : Deleted n k, allMarkedArray K U I ≤ B := by
    intro I
    rw [heq]
    exact (le_abs_self _).trans ((norm_le_pi_norm (p m) I).trans (hB (p m) ⟨m, rfl⟩))
  obtain ⟨L, V, s, hs, hdisk, houter, hmarks, harray⟩ := hnormal K U hK hcoeff
  exact ⟨L, V, s, hs, hdisk, houter, hmarks, harray.trans heq⟩

/-- The marked compactification, with the full affine-dimension conclusion. -/
theorem fullMarked_closure_representation {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    {P : Deleted n k → ℝ} (hP : P ∈ closure (fullMarkedLocus n k)) :
    ∃ (K : Body n) (U : Fin n → Space n),
      n - k + 1 ≤ bodyDimension K ∧ allMarkedArray K U = P := by
  obtain ⟨p, hp, hlim⟩ := mem_closure_iff_seq_limit.mp hP
  exact fullMarked_limit hk hkn p P hlim hp

theorem closure_fullMarkedLocus_eq_markedArrayLocus {n k : ℕ}
    (hk : 0 < k) (hkn : k ≤ n) :
    closure (fullMarkedLocus n k) = markedArrayLocus n k := by
  apply Set.Subset.antisymm
  · intro P hP
    obtain ⟨K, U, _hdim, heq⟩ := fullMarked_closure_representation hk hkn hP
    exact ⟨(K, U), heq⟩
  · rintro P ⟨⟨K, U⟩, rfl⟩
    exact marked_mem_closure_fullMarked K U

theorem isClosed_markedArrayLocus {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    IsClosed (markedArrayLocus n k) := by
  rw [← closure_fullMarkedLocus_eq_markedArrayLocus hk hkn]
  exact isClosed_closure

theorem marked_representation_with_dimension {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    {P : Deleted n k → ℝ} (hP : P ∈ markedArrayLocus n k) :
    ∃ (K : Body n) (U : Fin n → Space n),
      n - k + 1 ≤ bodyDimension K ∧ allMarkedArray K U = P := by
  apply fullMarked_closure_representation hk hkn
  rwa [closure_fullMarkedLocus_eq_markedArrayLocus hk hkn]

end RankThreeProjection
