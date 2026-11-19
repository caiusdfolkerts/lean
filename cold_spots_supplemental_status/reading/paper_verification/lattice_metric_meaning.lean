module

public import PaperVerification.LatticeDefs
public import PaperVerification.DnGaussian
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Analysis.SpecialFunctions.Sqrt


@[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

variable {n : ℕ}

def euclideanRealization (L : Set (Fin n → ℝ)) : Set (EuclideanSpace ℝ (Fin n)) :=
  (fun x : Fin n → ℝ ↦ (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))) '' L

theorem sqDist_eq_euclidean_dist_sq (x y : Fin n → ℝ) :
    sqDist x y=dist (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 y)^2 := by
  rw [sqDist_eq_euclidean_norm_sq,dist_eq_norm]

def euclideanRealizationEquiv (L : Set (Fin n → ℝ)) : L ≃ euclideanRealization L :=
  Equiv.ofBijective (fun x ↦ ⟨(WithLp.toLp 2 x.val : EuclideanSpace ℝ (Fin n)),
    x.val,x.property,rfl⟩) ⟨by
      intro x y h
      apply Subtype.ext
      have he := congrArg (fun p : euclideanRealization L ↦ WithLp.ofLp p.val) h
      exact he,by
      rintro ⟨y,x,hx,rfl⟩
      exact ⟨⟨x,hx⟩,rfl⟩⟩

theorem setGaussian_eq_euclidean (L : Set (Fin n → ℝ)) (α : ℝ) (x : Fin n → ℝ) :
    setGaussian L α x = ∑' v : euclideanRealization L,
      Real.exp (-α*dist v.val (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))^2) := by
  rw [← (euclideanRealizationEquiv L).tsum_eq]
  apply tsum_congr
  intro v
  exact congrArg (fun t : ℝ ↦ Real.exp (-α*t)) (sqDist_eq_euclidean_dist_sq v.val x)

theorem isColdSpot_iff_euclidean (L : Set (Fin n → ℝ)) (α : ℝ) (x : Fin n → ℝ) :
    IsColdSpot L α x ↔ ∀ y : EuclideanSpace ℝ (Fin n),
      (∑' v : euclideanRealization L,
        Real.exp (-α*dist v.val (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))^2)) ≤
      ∑' v : euclideanRealization L, Real.exp (-α*dist v.val y^2) := by
  constructor
  · intro h y
    have hy := h (WithLp.ofLp y)
    simpa only [setGaussian_eq_euclidean,WithLp.toLp_ofLp] using hy
  · intro h y
    have hy := h (WithLp.toLp 2 y)
    simpa only [setGaussian_eq_euclidean] using hy

/-- The working infimum of squared distances is exactly the square of the
ordinary metric distance to the actual Euclidean lattice set. -/
theorem squaredDepth_eq_infDist_sq (L : Set (Fin n → ℝ)) (hL : L.Nonempty) (x : Fin n → ℝ) :
    squaredDepth L x=
      Metric.infDist (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) (euclideanRealization L)^2 := by
  let d := Metric.infDist (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) (euclideanRealization L)
  have hd : 0 ≤ d := Metric.infDist_nonneg
  have hD := squaredDepth_nonneg L hL x
  apply le_antisymm
  · have hs : Real.sqrt (squaredDepth L x) ≤ d := by
      apply (Metric.le_infDist (hL.image _)).mpr
      rintro y ⟨z,hz,rfl⟩
      apply (sq_le_sq₀ (Real.sqrt_nonneg _) dist_nonneg).mp
      rw [Real.sq_sqrt hD,← sqDist_eq_euclidean_dist_sq]
      exact squaredDepth_le x hz
    have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 2
    rw [Real.sq_sqrt hD] at hsq
    exact hsq
  · apply le_csInf (hL.image _)
    rintro r ⟨z,hz,rfl⟩
    change d^2 ≤ sqDist x z
    rw [sqDist_eq_euclidean_dist_sq]
    exact pow_le_pow_left₀ hd
      (Metric.infDist_le_dist_of_mem (show (WithLp.toLp 2 z : EuclideanSpace ℝ (Fin n))∈
        euclideanRealization L from ⟨z,hz,rfl⟩)) 2

/-- In particular the formal `IsDeepHole` predicate has exactly its ordinary
Euclidean metric meaning; all ambient points are quantified. -/
theorem isDeepHole_iff_metric (L : Set (Fin n → ℝ)) (hL : L.Nonempty) (x : Fin n → ℝ) :
    IsDeepHole L x ↔ ∀ y : EuclideanSpace ℝ (Fin n),
      Metric.infDist y (euclideanRealization L) ≤
        Metric.infDist (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) (euclideanRealization L) := by
  constructor
  · intro h y
    have hy := h (WithLp.ofLp y)
    rw [squaredDepth_eq_infDist_sq L hL,squaredDepth_eq_infDist_sq L hL] at hy
    simpa only [WithLp.toLp_ofLp] using
      (sq_le_sq₀ (Metric.infDist_nonneg) (Metric.infDist_nonneg)).mp hy
  · intro h y
    rw [squaredDepth_eq_infDist_sq L hL,squaredDepth_eq_infDist_sq L hL]
    exact pow_le_pow_left₀ (Metric.infDist_nonneg) (h (WithLp.toLp 2 y)) 2

end PaperVerification.ColdSpots
