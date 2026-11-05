module
public import PaperVerification.ToricStarCombinatorics
@[expose] public section

/-!
# Primitive-relation pushdown when the exceptional ray is not positive

The old positive collection is proved primitive. If the exceptional ray
occurs negatively, its actual sum is expanded with positive integral
coefficients in an actual old cone. The resulting relation is constructed
and its degree pairing with every old divisor coefficient function is
proved to agree with pullback.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

def expandedRayCoefficient {ι : Type*} (s t : Finset ι) (e : ι)
    (c : ι → ℕ) (v : ι) : ℕ :=
  (if v ∈ s.erase e then c v else 0) + (if v ∈ t then c e else 0)

theorem sum_expandedRayCoefficient_smul {ι K E : Type*}
    [CommSemiring K] [AddCommMonoid E] [Module K E]
    (s t : Finset ι) (e : ι) (c : ι → ℕ) (v : ι → E) :
    (∑ i ∈ s.erase e ∪ t, (expandedRayCoefficient s t e c i : K) • v i) =
      (∑ i ∈ s.erase e, (c i : K) • v i) + (c e : K) • ∑ i ∈ t, v i := by
  let U := s.erase e ∪ t
  have hfirst : (∑ i ∈ U, ((if i ∈ s.erase e then c i else 0 : ℕ) : K) • v i) =
      ∑ i ∈ s.erase e, (c i : K) • v i := by
    calc
      (∑ i ∈ U, ((if i ∈ s.erase e then c i else 0 : ℕ) : K) • v i) =
          ∑ i ∈ s.erase e, ((if i ∈ s.erase e then c i else 0 : ℕ) : K) • v i := by
        symm
        apply Finset.sum_subset Finset.subset_union_left
        intro i _ hi
        simp only [if_neg hi, Nat.cast_zero, zero_smul]
      _ = ∑ i ∈ s.erase e, (c i : K) • v i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [if_pos hi]
  have hsecond : (∑ i ∈ U, ((if i ∈ t then c e else 0 : ℕ) : K) • v i) =
      (c e : K) • ∑ i ∈ t, v i := by
    calc
      (∑ i ∈ U, ((if i ∈ t then c e else 0 : ℕ) : K) • v i) =
          ∑ i ∈ t, ((if i ∈ t then c e else 0 : ℕ) : K) • v i := by
        symm
        apply Finset.sum_subset Finset.subset_union_right
        intro i _ hi
        simp only [if_neg hi, Nat.cast_zero, zero_smul]
      _ = ∑ i ∈ t, (c e : K) • v i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [if_pos hi]
      _ = (c e : K) • ∑ i ∈ t, v i := Finset.smul_sum.symm
  simp only [expandedRayCoefficient, Nat.cast_add, add_smul, Finset.sum_add_distrib]
  exact congrArg₂ (· + ·) hfirst hsecond

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
variable (t : Finset (Lattice n)) (ht : t ∈ «Σ».cones) (hne : t.Nonempty)

/-- Every nonexceptional primitive relation with no positive exceptional
coefficient has a genuine old primitive relation as pushdown. Degree
compatibility is universal over real coefficient functions. -/
theorem primitiveRelation_pushdown_without_positive_sum_data
    (hcard : 2 ≤ t.card) (R : («Σ».starSubdivision t ht hne).PrimitiveRelation)
    (heP : (∑ v ∈ t, v) ∉ R.positive) (hPt : R.positive ≠ t) :
    ∃ S : «Σ».PrimitiveRelation, S.positive = R.positive ∧
      S.negative = (if (∑ v ∈ t, v) ∈ R.negative then
        R.negative.erase (∑ v ∈ t, v) ∪ t else R.negative) ∧
      ∀ a : Lattice n → ℝ, S.degree a = R.degree (starCoefficientBase a t) := by
  let e := ∑ v ∈ t, v
  have hPold := «Σ».primitiveCollection_pushdown_without_sum t ht hne hcard R.primitive heP hPt
  have hpossum (a : Lattice n → ℝ) :
      (∑ v ∈ R.positive, starCoefficientBase a t v) = ∑ v ∈ R.positive, a v := by
    apply Finset.sum_congr rfl
    intro v hv
    have hve : v ≠ (∑ w ∈ t, w) := fun h => heP (h ▸ hv)
    simp only [starCoefficientBase, if_neg hve]
  by_cases heN : e ∈ R.negative
  · obtain ⟨p, hp, hpN, hNold⟩ :=
      («Σ».mem_starSubdivision_with_sum_iff t ht hne hcard heN).mp R.negative_cone
    let N := R.negative.erase e ∪ t
    let c := expandedRayCoefficient R.negative t e R.coefficient
    let Eclassical : Finset (Lattice n) := by
      letI : DecidableEq (Lattice n) := fun x y => Classical.propDecidable (x = y)
      exact R.negative.erase e
    let Nclassical : Finset (Lattice n) := by
      letI : DecidableEq (Lattice n) := fun x y => Classical.propDecidable (x = y)
      exact R.negative.erase e ∪ t
    have hEclassical : Eclassical = R.negative.erase e := by
      ext v
      simp only [Eclassical, Finset.mem_erase]
    have hNclassical : Nclassical = N := by
      ext v
      simp only [Nclassical, N, Finset.mem_union, Finset.mem_erase]
    have hexpand (K E : Type) [CommSemiring K] [AddCommMonoid E] [Module K E]
        (v : Lattice n → E) :
        (∑ i ∈ N, (c i : K) • v i) =
          (∑ i ∈ R.negative.erase e, (R.coefficient i : K) • v i) +
            (R.coefficient e : K) • ∑ i ∈ t, v i := by
      have h := sum_expandedRayCoefficient_smul (K := K) R.negative t e R.coefficient v
      change (∑ i ∈ Nclassical, (c i : K) • v i) =
        (∑ i ∈ Eclassical, (R.coefficient i : K) • v i) +
          (R.coefficient e : K) • ∑ i ∈ t, v i at h
      rw [hNclassical, hEclassical] at h
      exact h
    have hc : ∀ v ∈ N, 0 < c v := by
      intro v hv
      rcases Finset.mem_union.mp hv with hv | hv
      · have hvN := Finset.mem_of_mem_erase hv
        have hpos := R.coefficient_pos v hvN
        simp only [c, expandedRayCoefficient, Finset.mem_erase,
          if_pos (Finset.mem_erase.mp hv)]
        omega
      · have hepos := R.coefficient_pos e heN
        simp only [c, expandedRayCoefficient, if_pos hv]
        omega
    have heq : (∑ v ∈ R.positive, v) = ∑ v ∈ N, (c v : ℤ) • v := by
      have hexpandZ := hexpand ℤ (Lattice n) id
      simp only [id_eq] at hexpandZ
      rw [hexpandZ]
      rw [R.equation]
      rw [← Finset.add_sum_erase R.negative (fun v => (R.coefficient v : ℤ) • v) heN]
      change (R.coefficient e : ℤ) • e + _ = _ + (R.coefficient e : ℤ) • e
      exact add_comm _ _
    let S : «Σ».PrimitiveRelation := ⟨R.positive, N, c, hPold, hNold, hc, heq⟩
    refine ⟨S, rfl, ?_, ?_⟩
    · change N = if e ∈ R.negative then N else R.negative
      rw [if_pos heN]
    intro a
    have hneg : (∑ v ∈ N, (c v : ℝ) * a v) =
        ∑ v ∈ R.negative, (R.coefficient v : ℝ) * starCoefficientBase a t v := by
      have hexpandReal := hexpand ℝ ℝ a
      simp only [smul_eq_mul] at hexpandReal
      rw [hexpandReal]
      rw [← Finset.add_sum_erase R.negative
        (fun v => (R.coefficient v : ℝ) * starCoefficientBase a t v) heN]
      have hrest : (∑ v ∈ R.negative.erase e,
          (R.coefficient v : ℝ) * starCoefficientBase a t v) =
          ∑ v ∈ R.negative.erase e, (R.coefficient v : ℝ) * a v := by
        apply Finset.sum_congr rfl
        intro v hv
        have hve := (Finset.mem_erase.mp hv).1
        change v ≠ (∑ w ∈ t, w) at hve
        simp only [starCoefficientBase, if_neg hve]
      have heval : starCoefficientBase a t e = ∑ w ∈ t, a w := by
        unfold starCoefficientBase
        exact if_pos rfl
      rw [hrest, heval]
      ring
    simp only [PrimitiveRelation.degree, S, hpossum, hneg]
  · have hNold := ((«Σ».mem_starSubdivision_without_sum_iff t ht hne heN).mp
      R.negative_cone).1
    let S : «Σ».PrimitiveRelation :=
      ⟨R.positive, R.negative, R.coefficient, hPold, hNold, R.coefficient_pos, R.equation⟩
    refine ⟨S, rfl, ?_, ?_⟩
    · change R.negative = if e ∈ R.negative then R.negative.erase e ∪ t else R.negative
      rw [if_neg heN]
    intro a
    have hneg : (∑ v ∈ R.negative,
        (R.coefficient v : ℝ) * starCoefficientBase a t v) =
        ∑ v ∈ R.negative, (R.coefficient v : ℝ) * a v := by
      apply Finset.sum_congr rfl
      intro v hv
      have hve : v ≠ e := fun h => heN (h ▸ hv)
      change v ≠ (∑ w ∈ t, w) at hve
      simp only [starCoefficientBase, if_neg hve]
    simp only [PrimitiveRelation.degree, S, hpossum, hneg]

theorem primitiveRelation_pushdown_without_positive_sum
    (hcard : 2 ≤ t.card) (R : («Σ».starSubdivision t ht hne).PrimitiveRelation)
    (heP : (∑ v ∈ t, v) ∉ R.positive) (hPt : R.positive ≠ t) :
    ∃ S : «Σ».PrimitiveRelation, S.positive = R.positive ∧
      ∀ a : Lattice n → ℝ, S.degree a = R.degree (starCoefficientBase a t) := by
  obtain ⟨S, hP, hN, hdegree⟩ :=
    «Σ».primitiveRelation_pushdown_without_positive_sum_data t ht hne hcard R heP hPt
  exact ⟨S, hP, hdegree⟩

end SmoothCompleteFan

end PaperVerification.ToricGeometry
