module

public import PaperVerification.ToricFaceDegreeBounds
public import PaperVerification.ToricFocusQuotientRelation
public import PaperVerification.ToricSelectedDegreeEstimates

@[expose] public section

/-!
# Exact fiber degrees of arbitrary real normal-height slices

On the selected focus, each subtracted facet coefficient contributes with
its actual positive primitive-relation coefficient. The lower estimate
retains a baseline height, which is zero for ordinary boxes and one for
inner boxes. All coefficients are read from the genuine lattice relation.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan.PrimitiveRelation

open scoped BigOperators Classical

variable {n : ℕ} {«Σ» : SmoothCompleteFan n} (R : «Σ».PrimitiveRelation)

theorem degree_displaced_focus (a : Lattice n → ℝ) (h : Lattice n → ℝ) :
    R.degree (displacedSupport a R.negative h) =
      R.degree a + ∑ u ∈ R.negative, (R.coefficient u : ℝ) * h u := by
  rw [displacedSupport, R.degree_sub]
  have hp : (∑ u ∈ R.positive, facetWeight R.negative h u) = 0 := by
    apply Finset.sum_eq_zero
    intro u hu
    have hn : u ∉ R.negative := fun hh => Finset.disjoint_left.mp R.disjoint hu hh
    simp only [facetWeight, if_neg hn]
  have hn : (∑ u ∈ R.negative, (R.coefficient u : ℝ) * facetWeight R.negative h u) =
      ∑ u ∈ R.negative, (R.coefficient u : ℝ) * h u := by
    apply Finset.sum_congr rfl
    intro u hu
    simp only [facetWeight, if_pos hu]
  simp only [degree, hp, hn]
  ring

theorem weighted_focus_height_lower
    (hne : R.negative.Nonempty) (base : ℝ) (h : Lattice n → ℝ)
    (hh : ∀ u ∈ R.negative, base ≤ h u) :
    base * R.negativeCoefficientSum + (R.minimumCoefficient hne : ℝ) *
      ((∑ u ∈ R.negative, h u) - base * R.negative.card) ≤
      ∑ u ∈ R.negative, (R.coefficient u : ℝ) * h u := by
  have hterm (u : Lattice n) (hu : u ∈ R.negative) :
      base * (R.coefficient u : ℝ) + (R.minimumCoefficient hne : ℝ) * (h u - base) ≤
        (R.coefficient u : ℝ) * h u := by
    have hm : (R.minimumCoefficient hne : ℝ) ≤ R.coefficient u := by
      exact_mod_cast (R.minimumCoefficient_spec hne).2.2 u hu
    nlinarith [mul_nonneg (sub_nonneg.mpr hm) (sub_nonneg.mpr (hh u hu))]
  have hsum := Finset.sum_le_sum hterm
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul, negativeCoefficientSum] at hsum ⊢
  nlinarith

theorem degree_displaced_focus_lower
    (hne : R.negative.Nonempty) (a : Lattice n → ℝ)
    (base : ℝ) (h : Lattice n → ℝ) (hh : ∀ u ∈ R.negative, base ≤ h u) :
    R.degree a + base * R.negativeCoefficientSum + (R.minimumCoefficient hne : ℝ) *
      ((∑ u ∈ R.negative, h u) - base * R.negative.card) ≤
      R.degree (displacedSupport a R.negative h) := by
  rw [R.degree_displaced_focus]
  have hw := R.weighted_focus_height_lower hne base h hh
  linarith

end PaperVerification.ToricGeometry.SmoothCompleteFan.PrimitiveRelation
