module

public import PaperVerification.ToricDisjointStars

@[expose] public section

/-!
# The explicit minimum-coefficient lift of an activated primitive relation

The lifted relation is constructed by replacing the focus sum with its new
ray and subtracting the minimum old coefficient. Positivity, the actual new
focus cone, the vector identity, and the complete degree formula are proved.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

def residualRayCoefficient {ι : Type*} (t : Finset ι) (m : ℕ)
    (c : ι → ℕ) (v : ι) : ℕ := if v ∈ t then c v - m else c v

theorem sum_residualRayCoefficient_smul {ι K E : Type*}
    [CommSemiring K] [AddCommMonoid E] [Module K E]
    (s t : Finset ι) (hts : t ⊆ s) (m : ℕ) (c : ι → ℕ)
    (hm : ∀ i ∈ t, m ≤ c i) (v : ι → E) :
    (∑ i ∈ s, (c i : K) • v i) =
      (∑ i ∈ s, (residualRayCoefficient t m c i : K) • v i) +
      (m : K) • ∑ i ∈ t, v i := by
  have hsplit (i : ι) : residualRayCoefficient t m c i +
      (if i ∈ t then m else 0) = c i := by
    by_cases hi : i ∈ t
    · simp only [residualRayCoefficient, if_pos hi]
      exact Nat.sub_add_cancel (hm i hi)
    · simp only [residualRayCoefficient, if_neg hi, add_zero]
  have hcast (i : ι) : (c i : K) = (residualRayCoefficient t m c i : K) +
      ((if i ∈ t then m else 0 : ℕ) : K) := by
    rw [← Nat.cast_add, hsplit]
  have hsecond : (∑ i ∈ s, ((if i ∈ t then m else 0 : ℕ) : K) • v i) =
      (m : K) • ∑ i ∈ t, v i := by
    calc
      (∑ i ∈ s, ((if i ∈ t then m else 0 : ℕ) : K) • v i) =
          ∑ i ∈ t, ((if i ∈ t then m else 0 : ℕ) : K) • v i := by
        symm
        apply Finset.sum_subset hts
        intro i _ hi
        simp only [if_neg hi, Nat.cast_zero, zero_smul]
      _ = ∑ i ∈ t, (m : K) • v i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [if_pos hi]
      _ = (m : K) • ∑ i ∈ t, v i := Finset.smul_sum.symm
  simp only [hcast, add_smul, Finset.sum_add_distrib, hsecond]

theorem sum_residual_filter {ι K E : Type*}
    [CommSemiring K] [AddCommMonoid E] [Module K E]
    (s : Finset ι) (c : ι → ℕ) (v : ι → E) :
    (∑ i ∈ s.filter (fun i => 0 < c i), (c i : K) • v i) =
      ∑ i ∈ s, (c i : K) • v i := by
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i hi hif
  have hc : c i = 0 := by
    have hnot : ¬ 0 < c i := fun h => hif (Finset.mem_filter.mpr ⟨hi, h⟩)
    omega
  simp only [hc, Nat.cast_zero, zero_smul]

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
variable (t : Finset (Lattice n)) (ht : t ∈ «Σ».cones) (hne : t.Nonempty)

/-- The exact relation lift and its universal degree identity. The minimum
coefficient is positive and attained on an actual focus ray. -/
theorem exists_minimum_coefficient_lift (hcard : 2 ≤ t.card)
    (R : «Σ».PrimitiveRelation) (htN : t ⊆ R.negative) :
    ∃ m : ℕ, 0 < m ∧ (∃ p ∈ t, R.coefficient p = m) ∧
      (∀ v ∈ t, m ≤ R.coefficient v) ∧
      ∃ S : («Σ».starSubdivision t ht hne).PrimitiveRelation,
        S.positive = R.positive ∧ ∀ a : Lattice n → ℝ,
          S.degree a = R.degree a + (m : ℝ) * ((∑ v ∈ t, a v) - a (∑ v ∈ t, v)) := by
  obtain ⟨p, hp, hmin⟩ := t.exists_min_image R.coefficient hne
  let m := R.coefficient p
  let e := ∑ v ∈ t, v
  let d := residualRayCoefficient t m R.coefficient
  let N := R.negative.filter (fun v => 0 < d v)
  let c : Lattice n → ℕ := fun v => if v = e then m else d v
  have hm : 0 < m := R.coefficient_pos p (htN hp)
  have heold : e ∉ «Σ».rays := «Σ».sum_rays_not_mem_rays ht hcard
  have heNold : e ∉ R.negative :=
    fun h => heold («Σ».ray_mem_of_mem_cone R.negative_cone h)
  have heP : e ∉ R.positive := fun h => heold (R.primitive.1 h)
  have heN : e ∉ N := fun h => heNold (Finset.mem_filter.mp h).1
  have hpN : p ∉ N := by
    intro h
    have hpzero : d p = 0 := by simp [d, residualRayCoefficient, hp, m]
    have hpos := (Finset.mem_filter.mp h).2
    rw [hpzero] at hpos
    omega
  have htP : ¬ t ⊆ R.positive := by
    intro h
    exact Finset.disjoint_left.mp R.disjoint (h hp) (htN hp)
  have hPnew := «Σ».primitiveCollection_survives_star t ht hne hcard R.primitive htP
  have hNnew : insert e N ∈ («Σ».starSubdivision t ht hne).cones := by
    apply («Σ».starSubdivision t ht hne).downward
      (starRaySet R.negative t p)
      («Σ».starRaySet_mem_starSubdivision t ht hne R.negative_cone htN hp)
    intro v hv
    apply (mem_starRaySet R.negative t p v).mpr
    rcases Finset.mem_insert.mp hv with hve | hvN
    · exact Or.inl hve
    · exact Or.inr ⟨fun hvp => hpN (hvp ▸ hvN), (Finset.mem_filter.mp hvN).1⟩
  have hc : ∀ v ∈ insert e N, 0 < c v := by
    intro v hv
    rcases Finset.mem_insert.mp hv with hve | hvN
    · subst v
      simpa only [c, if_pos rfl] using hm
    · have hve : v ≠ e := fun h => heN (h ▸ hvN)
      simpa only [c, if_neg hve] using (Finset.mem_filter.mp hvN).2
  have hsum (K E : Type) [CommSemiring K] [AddCommMonoid E] [Module K E]
      (v : Lattice n → E) :
      (∑ x ∈ insert e N, (c x : K) • v x) =
        (m : K) • v e + ∑ x ∈ R.negative, (d x : K) • v x := by
    rw [Finset.sum_insert heN]
    simp only [c, if_pos rfl]
    congr 1
    calc
      (∑ x ∈ N, ((if x = e then m else d x : ℕ) : K) • v x) =
          ∑ x ∈ N, (d x : K) • v x := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [if_neg (fun h : x = e => heN (h ▸ hx))]
      _ = ∑ x ∈ R.negative, (d x : K) • v x :=
        sum_residual_filter R.negative d v
  have heq : (∑ v ∈ R.positive, v) = ∑ v ∈ insert e N, (c v : ℤ) • v := by
    have hsumZ := hsum ℤ (Lattice n) id
    have hresidualZ := sum_residualRayCoefficient_smul (K := ℤ)
      R.negative t htN m R.coefficient hmin id
    simp only [id_eq] at hsumZ hresidualZ
    rw [R.equation, hsumZ, hresidualZ]
    exact add_comm _ _
  let S : («Σ».starSubdivision t ht hne).PrimitiveRelation :=
    ⟨R.positive, insert e N, c, hPnew, hNnew, hc, heq⟩
  refine ⟨m, hm, ⟨p, hp, rfl⟩, hmin, S, rfl, ?_⟩
  intro a
  have hnewsum := hsum ℝ ℝ a
  have holdsum := sum_residualRayCoefficient_smul (K := ℝ)
    R.negative t htN m R.coefficient hmin a
  simp only [smul_eq_mul] at hnewsum holdsum
  change (∑ v ∈ R.positive, a v) - (∑ v ∈ insert e N, (c v : ℝ) * a v) =
    ((∑ v ∈ R.positive, a v) - ∑ v ∈ R.negative, (R.coefficient v : ℝ) * a v) +
      (m : ℝ) * ((∑ v ∈ t, a v) - a e)
  rw [hnewsum, holdsum]
  ring

/-- Every primitive lift with this positive collection has exactly the
minimum-coefficient degree formula. Thus an actual extremal class pushing
to an activated old class is identified without assuming uniqueness of
its lift as an extra hypothesis. -/
theorem minimum_coefficient_lift_degree_unique (hcard : 2 ≤ t.card)
    (R : «Σ».PrimitiveRelation) (htN : t ⊆ R.negative) :
    ∃ m : ℕ, 0 < m ∧ (∃ p ∈ t, R.coefficient p = m) ∧
      (∀ v ∈ t, m ≤ R.coefficient v) ∧
      ∀ S : («Σ».starSubdivision t ht hne).PrimitiveRelation,
        S.positive = R.positive → ∀ a : Lattice n → ℝ,
          S.degree a = R.degree a + (m : ℝ) * ((∑ v ∈ t, a v) - a (∑ v ∈ t, v)) := by
  obtain ⟨m, hm, hminmem, hmin, S₀, hS₀, hdegree⟩ :=
    «Σ».exists_minimum_coefficient_lift t ht hne hcard R htN
  refine ⟨m, hm, hminmem, hmin, ?_⟩
  intro S hS a
  exact (S.degree_unique S₀ (hS.trans hS₀.symm) a).trans (hdegree a)

end SmoothCompleteFan

end PaperVerification.ToricGeometry
