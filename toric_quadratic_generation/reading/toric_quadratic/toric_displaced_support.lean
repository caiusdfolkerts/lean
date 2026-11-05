module

public import PaperVerification.ToricFanFaceHulls
public import PaperVerification.ToricContractibleEdgeDegrees

@[expose] public section

/-!
# Exact displaced slices and their convex support

Subtracting nonnegative primitive-facet coefficients imposes the prescribed
normal heights. The equality with the actual slice is a direct equality of
subsets. The primitive degree estimate proves nefness and strict support
through the already established extremal criterion.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped BigOperators Classical

def facetWeight {n : ℕ} (T : Finset (Lattice n)) (h : Lattice n → ℝ) :
    Lattice n → ℝ := fun u => if u ∈ T then h u else 0

def displacedSupport {n : ℕ} (a : Lattice n → ℝ)
    (T : Finset (Lattice n)) (h : Lattice n → ℝ) : Lattice n → ℝ :=
  a - facetWeight T h

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

/-- Equality of the actual displaced support face and the actual normal
height slice of the original polytope. -/
theorem displaced_supportFace_eq_slice (a : Lattice n → ℝ)
    (T : Finset (Lattice n)) (h : Lattice n → ℝ)
    (hh : ∀ u ∈ T, 0 ≤ h u) :
    «Σ».supportFace (displacedSupport a T h) T =
      {x ∈ «Σ».fanPolytope a | ∀ u ∈ T,
        (dotProductEquiv ℝ (Fin n) (embed n u)) x + a u = h u} := by
  ext x
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · intro u hu
      have hxu := hx.1 u hu
      by_cases huT : u ∈ T
      · simp only [displacedSupport, Pi.sub_apply, facetWeight, if_pos huT] at hxu
        have hhu := hh u huT
        linarith
      · simpa only [displacedSupport, Pi.sub_apply, facetWeight, if_neg huT, sub_zero] using hxu
    · intro u hu
      have hxu := hx.2 u hu
      simp only [displacedSupport, Pi.sub_apply, facetWeight, if_pos hu] at hxu
      linarith
  · intro hx
    refine ⟨?_, ?_⟩
    · intro u hu
      by_cases huT : u ∈ T
      · have he := hx.2 u huT
        simp only [displacedSupport, Pi.sub_apply, facetWeight, if_pos huT]
        linarith
      · simpa only [displacedSupport, Pi.sub_apply, facetWeight, if_neg huT, sub_zero]
          using hx.1 u hu
    · intro u hu
      have he := hx.2 u hu
      simp only [displacedSupport, Pi.sub_apply, facetWeight, if_pos hu]
      linarith

namespace PrimitiveRelation

variable {«Σ»} (R : «Σ».PrimitiveRelation)

/-- A nonnegative collection of facet shifts has degree at most its total
height on any primitive relation, since every positive coefficient is one. -/
theorem degree_facetWeight_le (T : Finset (Lattice n)) (h : Lattice n → ℝ)
    (hh : ∀ u ∈ T, 0 ≤ h u) : R.degree (facetWeight T h) ≤ ∑ u ∈ T, h u := by
  have hnonneg (u : Lattice n) : 0 ≤ facetWeight T h u := by
    by_cases hu : u ∈ T
    · simpa only [facetWeight, if_pos hu] using hh u hu
    · simp [facetWeight, hu]
  have hnegative : 0 ≤ ∑ u ∈ R.negative,
      (R.coefficient u : ℝ) * facetWeight T h u :=
    Finset.sum_nonneg (fun u hu => mul_nonneg (Nat.cast_nonneg _) (hnonneg u))
  have hpositive : (∑ u ∈ R.positive, facetWeight T h u) ≤ ∑ u ∈ T, h u := by
    let S := R.positive.filter (fun u => u ∈ T)
    have hsub : S ⊆ T := fun u hu => (Finset.mem_filter.mp hu).2
    have he : (∑ u ∈ R.positive, facetWeight T h u) = ∑ u ∈ S, h u := by
      rw [show S = R.positive.filter (fun u => u ∈ T) from rfl, Finset.sum_filter]
      rfl
    rw [he]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun u hu huS => hh u hu)
  unfold degree
  linarith

theorem degree_displacedSupport_lower (a : Lattice n → ℝ)
    (T : Finset (Lattice n)) (h : Lattice n → ℝ)
    (hh : ∀ u ∈ T, 0 ≤ h u) :
    R.degree a - (∑ u ∈ T, h u) ≤ R.degree (displacedSupport a T h) := by
  rw [displacedSupport, R.degree_sub]
  exact sub_le_sub_left (R.degree_facetWeight_le T h hh) _

end PrimitiveRelation

/-- The nef assertion of the displaced-slice lemma, derived from genuine
extremal degrees and the proved convex-support criterion. -/
theorem displacedSupport_isNef (hpure : «Σ».IsPure)
    (H : Lattice n → ℤ) (hH : «Σ».IsStrictSupport (fun u => (H u : ℝ)))
    (a : Lattice n → ℝ) (e : ℝ)
    (hdegree : ∀ R : «Σ».PrimitiveRelation, R.IsExtremal → e ≤ R.degree a)
    (T : Finset (Lattice n)) (h : Lattice n → ℝ)
    (hh : ∀ u ∈ T, 0 ≤ h u) (hbudget : (∑ u ∈ T, h u) ≤ e) :
    «Σ».IsNef (displacedSupport a T h) := by
  apply («Σ».isNef_iff_extremal_primitive_nonneg hpure H hH _).mpr
  intro R hR
  exact (sub_nonneg.mpr (hbudget.trans (hdegree R hR))).trans
    (R.degree_displacedSupport_lower a T h hh)

/-- Strictly smaller displacement gives actual strict support, rather than
only a positive inequality assumed to imply ampleness. -/
theorem displacedSupport_isStrictSupport (hpure : «Σ».IsPure)
    (H : Lattice n → ℤ) (hH : «Σ».IsStrictSupport (fun u => (H u : ℝ)))
    (a : Lattice n → ℝ) (e : ℝ)
    (hdegree : ∀ R : «Σ».PrimitiveRelation, R.IsExtremal → e ≤ R.degree a)
    (T : Finset (Lattice n)) (h : Lattice n → ℝ)
    (hh : ∀ u ∈ T, 0 ≤ h u) (hbudget : (∑ u ∈ T, h u) < e) :
    «Σ».IsStrictSupport (displacedSupport a T h) := by
  apply «Σ».isStrictSupport_of_extremal_primitive_pos hpure H hH
  intro R hR
  exact (sub_pos.mpr (hbudget.trans_le (hdegree R hR))).trans_le
    (R.degree_displacedSupport_lower a T h hh)

/-- All nef support functions are closed under actual finite sums. -/
theorem isNef_finset_sum {ι : Type*} (I : Finset ι)
    (a : ι → Lattice n → ℝ) (ha : ∀ i ∈ I, «Σ».IsNef (a i)) :
    «Σ».IsNef (∑ i ∈ I, a i) := by
  induction I using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using «Σ».isNef_zero
  | @insert i I hi ih =>
      rw [Finset.sum_insert hi]
      exact IsNef.add «Σ» (ha i (Finset.mem_insert_self _ _))
        (ih (fun j hj => ha j (Finset.mem_insert_of_mem hj)))

end SmoothCompleteFan

end PaperVerification.ToricGeometry
