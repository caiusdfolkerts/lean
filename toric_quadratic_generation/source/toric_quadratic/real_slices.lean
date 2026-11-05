module

public import toric_quadratic.real_support

@[expose] public section

/-!
# Real displaced supports and their invariant degrees

This module supplies the all-real degree-loss assertion in Lemma 3.2.
Every wall is tested by the actual Cartier-point slack from `RealSupport`.
The supporting divisor, the facet heights, and the degree threshold may
all be real. Purity and an integral projectivity witness are derived from
the real strict support.
The zero threshold is included: a nonnegative displacement with total
height at most zero is identically zero on the selected facets.
-/

noncomputable section

namespace ToricQuadratic.RealSlices

open Set
open PaperVerification.ToricGeometry
open PaperVerification.ToricGeometry.SmoothCompleteFan
open ToricQuadratic.RealSupport
open scoped BigOperators Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

/-- Genuine nefness makes every literal ray slack nonnegative at every
Cartier point. -/
theorem wallSlack_nonneg_of_nef (a : Lattice n → ℝ) (ha : «Σ».IsNef a)
    (s : «Σ».fullCones) (u : Lattice n) (hu : u ∈ «Σ».rays) :
    0 ≤ «Σ».wallSlack a s u := by
  have hh := «Σ».cartierPoint_mem_of_nef ha s u hu
  change -a u ≤ (dotProductEquiv ℝ (Fin n) (embed n u)) («Σ».cartierPoint a s) at hh
  dsimp only [wallSlack]
  linarith

theorem wallSlack_sub (a b : Lattice n → ℝ) (s : «Σ».fullCones) (u : Lattice n) :
    «Σ».wallSlack (a - b) s u = «Σ».wallSlack a s u - «Σ».wallSlack b s u := by
  simp only [wallSlack, Pi.sub_apply, «Σ».cartierPoint_sub, map_sub]
  ring

theorem wallSlack_smul (c : ℝ) (a : Lattice n → ℝ)
    (s : «Σ».fullCones) (u : Lattice n) :
    «Σ».wallSlack (c • a) s u = c * «Σ».wallSlack a s u := by
  simp only [wallSlack, Pi.smul_apply, «Σ».cartierPoint_smul, map_smul, smul_eq_mul]
  ring

/-- The proportional remainder is nef for arbitrary real support. Its
proof uses all actual extremal primitive relations and the projective
fan's established nef criterion. -/
theorem displacedSupport_nef_difference
    (hpure : «Σ».IsPure) (A : Lattice n → ℤ)
    (hA : «Σ».IsStrictSupport (fun u => (A u : ℝ)))
    (a : Lattice n → ℝ) (ha : «Σ».IsStrictSupport a)
    (e : ℝ) (he : 0 < e) (hbound : WallDegreesAtLeast «Σ» a e)
    (T : Finset (Lattice n)) (h : Lattice n → ℝ)
    (hh : ∀ u ∈ T, 0 ≤ h u) :
    «Σ».IsNef (displacedSupport a T h - (1 - (∑ u ∈ T, h u) / e) • a) := by
  let H := ∑ u ∈ T, h u
  have hH : 0 ≤ H := Finset.sum_nonneg hh
  have hHe : 0 ≤ H / e := div_nonneg hH he.le
  apply («Σ».isNef_iff_extremal_primitive_nonneg hpure A hA _).mpr
  intro R hR
  have hd := contractible_degree_lower_bound «Σ» hpure a ha e hbound R
    (R.combinatoriallyContractible_of_extremal hR)
  have hf := R.degree_facetWeight_le T h hh
  have hmul := mul_le_mul_of_nonneg_left hd hHe
  have hcancel : (H / e) * e = H := div_mul_cancel₀ H he.ne'
  rw [hcancel] at hmul
  rw [R.degree_sub, R.degree_smul, displacedSupport, R.degree_sub]
  change 0 ≤ R.degree a - R.degree (facetWeight T h) - (1 - H / e) * R.degree a
  change R.degree (facetWeight T h) ≤ H at hf
  nlinarith

/-- **Lemma 3.2, all-real invariant-degree estimate.** Moving nonnegative
facets through total height `H ≤ e` preserves the uniform lower degree
bound `e - H`. This includes `e = 0`, boundary budgets, and
nonintegral support coefficients and heights. -/
theorem displacedSupport_wallDegreesAtLeast
    (a : Lattice n → ℝ) (ha : «Σ».IsStrictSupport a)
    (e : ℝ) (hbound : WallDegreesAtLeast «Σ» a e)
    (T : Finset (Lattice n)) (h : Lattice n → ℝ)
    (hh : ∀ u ∈ T, 0 ≤ h u) (hbudget : (∑ u ∈ T, h u) ≤ e) :
    WallDegreesAtLeast «Σ» (displacedSupport a T h) (e - ∑ u ∈ T, h u) := by
  have hpure : «Σ».IsPure := «Σ».isPure_of_complete
  obtain ⟨A, hA⟩ := «Σ».exists_integral_strictSupport_of_real a ha
  have htotal : 0 ≤ ∑ u ∈ T, h u := Finset.sum_nonneg hh
  by_cases he : e = 0
  · have hzero : (∑ u ∈ T, h u) = 0 :=
      le_antisymm (by simpa only [he] using hbudget) htotal
    have hhzero : ∀ u ∈ T, h u = 0 := (Finset.sum_eq_zero_iff_of_nonneg hh).mp hzero
    have hsupport : displacedSupport a T h = a := by
      funext u
      change a u - (if u ∈ T then h u else 0) = a u
      by_cases hu : u ∈ T
      · simp [hu, hhzero u hu]
      · simp [hu]
    simpa only [hsupport, hzero, sub_zero] using hbound
  · have hepos : 0 < e := lt_of_le_of_ne (htotal.trans hbudget) (Ne.symm he)
    let c : ℝ := 1 - (∑ u ∈ T, h u) / e
    have hc : 0 ≤ c := sub_nonneg.mpr ((div_le_one hepos).mpr hbudget)
    have hnef := displacedSupport_nef_difference «Σ» hpure A hA a ha e hepos hbound T h hh
    intro s t hst u hut hus
    have hu : u ∈ «Σ».rays := «Σ».ray_mem_of_mem_cone («Σ».fullCones_mem t) hut
    have hs := wallSlack_nonneg_of_nef «Σ»
      (displacedSupport a T h - c • a) hnef s u hu
    rw [wallSlack_sub, wallSlack_smul] at hs
    have hmul := mul_le_mul_of_nonneg_left (hbound s t hst u hut hus) hc
    have hce : c * e = e - ∑ u ∈ T, h u := by
      dsimp only [c]
      rw [sub_mul, one_mul, div_mul_cancel₀ _ hepos.ne']
    rw [hce] at hmul
    linarith

/-- The nef and strict-support conclusions of Lemma 3.2 follow from the
same ordinary wall-degree hypothesis used in the all-real degree estimate. -/
theorem displacedSupport_convexity
    (a : Lattice n → ℝ) (ha : «Σ».IsStrictSupport a)
    (e : ℝ) (hbound : WallDegreesAtLeast «Σ» a e)
    (T : Finset (Lattice n)) (h : Lattice n → ℝ)
    (hh : ∀ u ∈ T, 0 ≤ h u) (hbudget : (∑ u ∈ T, h u) ≤ e) :
    «Σ».IsNef (displacedSupport a T h) ∧
      ((∑ u ∈ T, h u) < e → «Σ».IsStrictSupport (displacedSupport a T h)) := by
  have hpure : «Σ».IsPure := «Σ».isPure_of_complete
  obtain ⟨A, hA⟩ := «Σ».exists_integral_strictSupport_of_real a ha
  have hdegree (R : «Σ».PrimitiveRelation) (hR : R.IsExtremal) : e ≤ R.degree a :=
    contractible_degree_lower_bound «Σ» hpure a ha e hbound R
      (R.combinatoriallyContractible_of_extremal hR)
  exact ⟨«Σ».displacedSupport_isNef hpure A hA a e hdegree T h hh hbudget,
    fun hlt => «Σ».displacedSupport_isStrictSupport hpure A hA a e hdegree T h hh hlt⟩

end ToricQuadratic.RealSlices

end
