module
public import PaperVerification.ToricFaceInheritance
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.Push
@[expose] public section
/-!
# A quantitative reserve for nonincident integral supporting facets

This is the local slack estimate used in Lemma 3.2. It follows directly from
the genuine tangent cone and long incident edges: one descending edge supplies
a negative integral coefficient, and a coefficient of greatest magnitude
controls every nonnegative coordinate displacement. No Mori statement is an
assumption of this estimate.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

/-- An affine functional evaluated on an arbitrary basis-coordinate displacement. -/
theorem affine_apply_add_basis_sum (f : E →ᵃ[ℝ] ℝ) (v : E)
    (b : Module.Basis ι ℝ E) (h : ι → ℝ) :
    f (v + ∑ i, h i • b i) = f v + ∑ i, h i * f.linear (b i) := by
  rw [add_comm]
  change f ((∑ i, h i • b i) +ᵥ v) = _
  rw [AffineMap.map_vadd]
  simp [map_sum, map_smul, vadd_eq_add, smul_eq_mul, add_comm]

/-- If an actual supporting affine functional is positive at a vertex, its
linear part is strictly negative on at least one incident basis direction. -/
theorem supporting_facet_has_descending_direction
    (P : Set E) (v : E) (b : Module.Basis ι ℝ E)
    (hcone : ∀ x ∈ P, ∀ i, 0 ≤ b.repr (x - v) i)
    (f : E →ᵃ[ℝ] ℝ) (hfv : 0 < f v)
    (htouch : ∃ y ∈ P, f y = 0) :
    ∃ i, f.linear (b i) < 0 := by
  by_contra hnone
  push_neg at hnone
  obtain ⟨y, hy, hfy⟩ := htouch
  have hsum : 0 ≤ ∑ i, b.repr (y - v) i * f.linear (b i) :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hcone y hy i) (hnone i))
  have h := affine_apply_basis_coordinates f b v y
  rw [hfy] at h
  linarith

/-- The exact reserve `L - sum h` for every real nonnegative normal displacement.
The supporting facet must actually meet the polytope and be nonincident to the
chosen vertex. Its integrality is required on the primitive basis directions. -/
theorem nonincident_facet_displacement_reserve
    (P : Set E) (v : E) (b : Module.Basis ι ℝ E)
    (hcone : ∀ x ∈ P, ∀ i, 0 ≤ b.repr (x - v) i)
    (lengths : ι → ℝ) (L : ℝ) (hlength : ∀ i, L ≤ lengths i)
    (hedges : ∀ i, v + lengths i • b i ∈ P)
    (f : E →ᵃ[ℝ] ℝ) (hfeasible : ∀ x ∈ P, 0 ≤ f x)
    (hfv : 0 < f v) (htouch : ∃ y ∈ P, f y = 0)
    (hintegral : ∀ i, ∃ z : ℤ, (z : ℝ) = f.linear (b i))
    (h : ι → ℝ) (hh : ∀ i, 0 ≤ h i) (hbudget : (∑ i, h i) ≤ L) :
    L - ∑ i, h i ≤ f (v + ∑ i, h i • b i) := by
  classical
  obtain ⟨i₀, hi₀⟩ := supporting_facet_has_descending_direction P v b hcone f hfv htouch
  obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset ι)
    (fun i => f.linear (b i)) ⟨i₀, Finset.mem_univ i₀⟩
  have hjneg : f.linear (b j) < 0 :=
    (hmin i₀ (Finset.mem_univ i₀)).trans_lt hi₀
  let c := -f.linear (b j)
  have hcpos : 0 < c := neg_pos.mpr hjneg
  have hc1 : 1 ≤ c := by
    obtain ⟨z, hz⟩ := hintegral j
    have hzneg : z < 0 := by exact_mod_cast (hz.symm ▸ hjneg)
    have hzbound : (1 : ℤ) ≤ -z := by omega
    dsimp only [c]
    rw [← hz]
    exact_mod_cast hzbound
  have hcoef (i : ι) : -c ≤ f.linear (b i) := by
    simpa only [c, neg_neg] using hmin i (Finset.mem_univ i)
  have hslack : L * c ≤ f v := by
    have hedge := hfeasible _ (hedges j)
    rw [affine_apply_add_smul] at hedge
    have hprod : L * c ≤ lengths j * c :=
      mul_le_mul_of_nonneg_right (hlength j) hcpos.le
    dsimp only [c] at hprod
    nlinarith
  have hsum : -(c * ∑ i, h i) ≤ ∑ i, h i * f.linear (b i) := by
    calc
      -(c * ∑ i, h i) = ∑ i, h i * (-c) := by
        simp [Finset.sum_mul, Finset.mul_sum, mul_comm]
      _ ≤ ∑ i, h i * f.linear (b i) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hcoef i) (hh i))
  have hscale : L - ∑ i, h i ≤ c * (L - ∑ i, h i) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hbudget) (sub_nonneg.mpr hc1)]
  rw [affine_apply_add_basis_sum]
  nlinarith

/-- Strict reserve prevents any nonincident facet from appearing before the
total displacement reaches the original edge bound. -/
theorem nonincident_facet_displacement_positive
    (P : Set E) (v : E) (b : Module.Basis ι ℝ E)
    (hcone : ∀ x ∈ P, ∀ i, 0 ≤ b.repr (x - v) i)
    (lengths : ι → ℝ) (L : ℝ) (hlength : ∀ i, L ≤ lengths i)
    (hedges : ∀ i, v + lengths i • b i ∈ P)
    (f : E →ᵃ[ℝ] ℝ) (hfeasible : ∀ x ∈ P, 0 ≤ f x)
    (hfv : 0 < f v) (htouch : ∃ y ∈ P, f y = 0)
    (hintegral : ∀ i, ∃ z : ℤ, (z : ℝ) = f.linear (b i))
    (h : ι → ℝ) (hh : ∀ i, 0 ≤ h i) (hbudget : (∑ i, h i) < L) :
    0 < f (v + ∑ i, h i • b i) := by
  exact (sub_pos.mpr hbudget).trans_le
    (nonincident_facet_displacement_reserve P v b hcone lengths L hlength hedges f
      hfeasible hfv htouch hintegral h hh hbudget.le)

end PaperVerification.ToricGeometry
