module
public import PaperVerification.ToricNormalConeRealization
@[expose] public section
/-!
# Normal cones of finite convex combinations

All support inequalities are the actual coordinate-pairing inequalities of
the lattice polytope. Zero weights are ignored; positive weights force equality
of the support value at every participating point.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.LatticePolytope

open Set
open scoped BigOperators

variable {n : ℕ} (P : LatticePolytope n)

/-- A normal supports a finite convex average exactly when it supports every
point with positive weight. The averaging family need not consist of vertices. -/
theorem mem_normalCone_convex_average {ι : Type*} [Fintype ι]
    (v : ι → Ambient n) (p : ι → ℝ)
    (hv : ∀ i, v i ∈ P.carrier)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (u : Ambient n) :
    u ∈ P.normalCone (∑ i, p i • v i) ↔
      ∀ i, 0 < p i → u ∈ P.normalCone (v i) := by
  classical
  let x : Ambient n := ∑ i, p i • v i
  let f : Ambient n →ₗ[ℝ] ℝ := dotProductEquiv ℝ (Fin n) u
  have hmem (z : Ambient n) :
      u ∈ P.normalCone z ↔ ∀ y ∈ P.carrier, f z ≤ f y := by
    change (∀ y ∈ P.carrier, 0 ≤ f (y - z)) ↔ _
    simp only [map_sub, sub_nonneg]
  have hfx : f x = ∑ i, p i * f (v i) := by
    simp only [x, map_sum, map_smul, smul_eq_mul]
  change u ∈ P.normalCone x ↔ _
  simp only [hmem]
  constructor
  · intro hx i hi y hy
    have hnonneg (j : ι) : 0 ≤ p j * (f (v j) - f x) :=
      mul_nonneg (hp0 j) (sub_nonneg.mpr (hx (v j) (hv j)))
    have hsum : (∑ j, p j * (f (v j) - f x)) = 0 := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hp1, one_mul, ← hfx,
        sub_self]
    have hterm : p i * (f (v i) - f x) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnonneg j)).mp hsum i
        (Finset.mem_univ i)
    have heq : f (v i) = f x :=
      sub_eq_zero.mp ((mul_eq_zero.mp hterm).resolve_left (ne_of_gt hi))
    rw [heq]
    exact hx y hy
  · intro h y hy
    have hterm (i : ι) : p i * f (v i) ≤ p i * f y := by
      by_cases hi : p i = 0
      · simp only [hi, zero_mul, le_refl]
      · have hip : 0 < p i := lt_of_le_of_ne (hp0 i) (Ne.symm hi)
        exact mul_le_mul_of_nonneg_left (h i hip y hy) (hp0 i)
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hterm i)
    rw [← hfx, ← Finset.sum_mul, hp1, one_mul] at hs
    exact hs

/-- Set-valued form: the normal cone of a convex average is the intersection
of the actual normal cones at precisely its positive-weight points. -/
theorem normalCone_convex_average {ι : Type*} [Fintype ι]
    (v : ι → Ambient n) (p : ι → ℝ)
    (hv : ∀ i, v i ∈ P.carrier)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) :
    P.normalCone (∑ i, p i • v i) =
      ⋂ i ∈ Finset.univ.filter (fun i => 0 < p i), P.normalCone (v i) := by
  classical
  ext u
  simp only [Set.mem_iInter, Finset.mem_filter, Finset.mem_univ, true_and,
    P.mem_normalCone_convex_average v p hv hp0 hp1 u]

end PaperVerification.ToricGeometry.LatticePolytope

