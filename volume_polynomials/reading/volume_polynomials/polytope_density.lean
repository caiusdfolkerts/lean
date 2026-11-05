module
public import VolumePolynomials.CoefficientMap
public import VolumePolynomials.VolumeLipschitz

@[expose] public section
set_option autoImplicit false
noncomputable section

/-!
# The coefficient locus of full-dimensional polytopes

An inscribed finite convex hull followed by arbitrarily small cube addition
approximates every convex body by a full-dimensional polytope. Consequently the
closure of the coefficient locus of such tuples is the whole realization locus.
This gives the full-dimensional-polytope clause of the threshold theorem from
the corresponding nonsemialgebraicity theorem for arbitrary convex bodies.
-/

open Set Metric Topology
open scoped Pointwise

namespace VolumePolynomials
open PolytopeGeometry

theorem coordinateCube_isFiniteHull (d : ℕ) :
    IsFiniteHull (coordinateCube d : Set (Space d)) := by
  first
  | let V : Set (Space d) := Set.pi Set.univ (fun _ => ({-1, 1} : Set ℝ))
    refine ⟨V, Set.Finite.pi (fun _ => (Set.finite_singleton (1 : ℝ)).insert (-1)), ?_⟩
    change Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)) = convexHull ℝ V
    dsimp only [V]
    rw [convexHull_pi]
    simp only [convexHull_pair, segment_eq_Icc (show (-1 : ℝ) ≤ 1 by norm_num)]
    ext x
    simp only [Set.mem_Icc, Set.mem_pi, Set.mem_univ, forall_true_left]
    exact ⟨fun h i => ⟨h.1 i, h.2 i⟩,
      fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩

/-- The interior condition is literal ambient interior, so every body obtained
here is full dimensional even when the original body is a point. -/
theorem interior_add_smul_coordinateCube_nonempty {d : ℕ} (P : Body d)
    {t : ℝ} (ht : 0 < t) :
    (interior ((P + t • coordinateCube d : Body d) : Set (Space d))).Nonempty := by
  first
  | obtain ⟨x, hx⟩ := P.nonempty
    refine ⟨x, mem_interior_iff_mem_nhds.mpr (Metric.mem_nhds_iff.mpr ⟨t, ht, ?_⟩)⟩
    intro y hy
    have hnorm : ‖y - x‖ ≤ t := by
      simpa only [dist_eq_norm] using (Metric.mem_ball.mp hy).le
    let u : Space d := t⁻¹ • (y - x)
    have hu : u ∈ coordinateCube d := by
      have hi (i : Fin d) : |u i| ≤ 1 := by
        have hcoord : |(y - x) i| ≤ t := by
          calc
            |(y - x) i| = ‖(y - x) i‖ := (Real.norm_eq_abs _).symm
            _ ≤ ‖y - x‖ := norm_le_pi_norm (y - x) i
            _ ≤ t := hnorm
        change |t⁻¹ * (y - x) i| ≤ 1
        rw [abs_mul, abs_inv, abs_of_pos ht]
        calc
          t⁻¹ * |(y - x) i| ≤ t⁻¹ * t :=
            mul_le_mul_of_nonneg_left hcoord (inv_nonneg.mpr ht.le)
          _ = 1 := inv_mul_cancel₀ ht.ne'
      exact ⟨fun i => (abs_le.mp (hi i)).1, fun i => (abs_le.mp (hi i)).2⟩
    have hscale : t • u = y - x := by
      simp only [u, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
    exact Set.mem_add.mpr ⟨x, hx, y - x, ⟨u, hu, hscale⟩, by abel⟩

def FullDimensionalPolytope {d : ℕ} (K : Body d) : Prop :=
  IsFiniteHull (K : Set (Space d)) ∧ (interior (K : Set (Space d))).Nonempty

theorem exists_near_fullDimensionalPolytope {d : ℕ} (K : Body d)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P : Body d, FullDimensionalPolytope P ∧ dist P K < ε := by
  first
  | obtain ⟨P, hpoly, _, hPK⟩ := exists_inscribed_finiteHullBody K (half_pos hε)
    have hc : Continuous (fun t : ℝ => P + t • coordinateCube d) := by fun_prop
    obtain ⟨δ, hδ, hnear⟩ := Metric.continuousAt_iff.mp (hc.continuousAt (x := (0 : ℝ)))
      (ε / 2) (half_pos hε)
    let t : ℝ := δ / 2
    have ht : 0 < t := half_pos hδ
    have htδ : dist t 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos ht]
      exact half_lt_self hδ
    let Q : Body d := P + t • coordinateCube d
    have hQP : dist Q P < ε / 2 := by
      simpa only [body_zero_smul, add_zero] using hnear htδ
    refine ⟨Q, ⟨?_, interior_add_smul_coordinateCube_nonempty P ht⟩, ?_⟩
    · exact hpoly.add ((coordinateCube_isFiniteHull d).smul t)
    · calc
        dist Q K ≤ dist Q P + dist P K := dist_triangle Q P K
        _ < ε / 2 + ε / 2 := add_lt_add hQP hPK
        _ = ε := by ring

theorem dense_fullDimensionalPolytopes (d : ℕ) :
    Dense {K : Body d | FullDimensionalPolytope K} := by
  first
  | rw [Metric.dense_iff]
    intro K ε hε
    obtain ⟨P, hP, hPK⟩ := exists_near_fullDimensionalPolytope K hε
    exact ⟨P, hPK, hP⟩

theorem dense_fullDimensionalPolytopeTuples (n d : ℕ) :
    Dense {K : Fin n → Body d | ∀ i, FullDimensionalPolytope (K i)} := by
  first
  | simpa [Set.pi] using
      dense_pi Set.univ (fun (_ : Fin n) _ => dense_fullDimensionalPolytopes d)

def FullDimensionalPolytopeLocus (n d : ℕ) : Set (Coefficients n d) :=
  {c | ∃ K : Fin n → Body d, (∀ i, FullDimensionalPolytope (K i)) ∧ Realizes K c}

theorem fullDimensionalPolytopeLocus_eq_image (n d : ℕ) :
    FullDimensionalPolytopeLocus n d =
      coefficientMap '' {K : Fin n → Body d | ∀ i, FullDimensionalPolytope (K i)} := by
  first
  | ext c
    constructor
    · rintro ⟨K, hK, hc⟩
      exact ⟨K, hK, hc.eq_coefficientMap.symm⟩
    · rintro ⟨K, hK, rfl⟩
      exact ⟨K, hK, coefficientMap_realizes K⟩

theorem closure_fullDimensionalPolytopeLocus (n d : ℕ) (hd : 0 < d) :
    closure (FullDimensionalPolytopeLocus n d) = VolumeLocus n d := by
  first
  | rw [fullDimensionalPolytopeLocus_eq_image]
    exact closure_coefficientMap_image_of_dense hd (dense_fullDimensionalPolytopeTuples n d)

end VolumePolynomials
