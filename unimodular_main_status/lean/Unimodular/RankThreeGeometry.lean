module

public import Unimodular.Geometry

@[expose] public section

noncomputable section

namespace Unimodular.SmoothCompleteFan

open scoped BigOperators

variable {n : ℕ} (fan : SmoothCompleteFan n)

/-- A complete positive-coordinate fan has no nonzero linear functional that is
nonpositive on every ray. This is derived from actual conic completeness. -/
theorem no_separating_functional (h : Ambient n)
    (hh : ∀ u ∈ fan.rays, pairing h u ≤ 0)
    (hne : h ≠ 0) : False := by
  obtain ⟨b, hb, hx⟩ := fan.complete h
  have hc := (mem_basisCone_iff b h).1 hx
  have hnonpos : realPairing h h ≤ 0 := by
    rw [realPairing_eq_coordinates b]
    exact Finset.sum_nonpos fun i _ =>
      mul_nonpos_of_nonneg_of_nonpos (hc i) (hh (b i) ⟨b, hb, i, rfl⟩)
  have hex : ∃ i, h i ≠ 0 := by
    contrapose! hne
    ext i
    exact hne i
  obtain ⟨i, hi⟩ := hex
  have hpos : 0 < realPairing h h := by
    apply Finset.sum_pos'
    · intro j _
      exact mul_self_nonneg (h j)
    · exact ⟨i, Finset.mem_univ _, mul_self_pos.2 hi⟩
  exact (not_lt_of_ge hnonpos) hpos

/-- Every supporting hyperplane of the ray hull of a complete positive-coordinate
fan contains at most n rays. In particular, a quadrilateral support face rules out
such a fan in rank three. No polytope simplicity hypothesis is assumed here. -/
theorem support_rays_card_le (hfan : fan.PositiveCoordinateCriterion)
    {J : Type*} [Fintype J] (a : J → Lattice n)
    (ha : ∀ j, a j ∈ fan.rays) (hinj : Function.Injective a)
    (h : Ambient n) (hbound : ∀ u ∈ fan.rays, pairing h u ≤ 1)
    (heq : ∀ j, pairing h (a j) = 1) : Fintype.card J ≤ n := by
  classical
  let x : Ambient n := ∑ j, embed (a j)
  obtain ⟨b, hb, hx⟩ := fan.complete x
  have hc := (mem_basisCone_iff b x).1 hx
  let m : Ambient n := dualCorner b (fun _ => 1)
  have hsum (p : Ambient n) : realPairing p x = ∑ j, pairing p (a j) := by
    simp only [x, realPairing, Finset.sum_apply, Finset.mul_sum, embed, pairing]
    exact Finset.sum_comm
  have hxval : realPairing h x = Fintype.card J := by
    rw [hsum]
    simp [heq]
  have hmcoord : realPairing m x = ∑ i, realCoordinates b x i := by
    rw [realPairing_eq_coordinates b]
    simp [m, pairing_dualCorner_basis]
  have hcmp : realPairing h x ≤ realPairing m x := by
    rw [realPairing_eq_coordinates b, hmcoord]
    exact Finset.sum_le_sum fun i _ => by
      simpa using mul_le_mul_of_nonneg_left (hbound (b i) ⟨b, hb, i, rfl⟩) (hc i)
  have hupper (j : J) : pairing m (a j) ≤ 1 :=
    (fan.strict_support_at_basis hfan b hb (a j) (ha j)).1
  have hsumle : (∑ j, pairing m (a j)) ≤ Fintype.card J := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun j _ => hupper j)
  have hsumeq : (∑ j, pairing m (a j)) = Fintype.card J := by
    apply le_antisymm hsumle
    simpa [hxval, hsum] using hcmp
  have hmone (j : J) : pairing m (a j) = 1 := by
    by_contra hnot
    have hjlt : pairing m (a j) < 1 := lt_of_le_of_ne (hupper j) hnot
    have hslt : (∑ j, pairing m (a j)) < (∑ _ : J, (1 : ℝ)) := by
      apply Finset.sum_lt_sum
      · intro k _
        exact hupper k
      · exact ⟨j, Finset.mem_univ _, hjlt⟩
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hslt
    exact (ne_of_lt hslt) hsumeq
  have hex (j : J) : ∃ i, b i = a j :=
    (fan.strict_support_at_basis hfan b hb (a j) (ha j)).2.1 (hmone j)
  choose f hf using hex
  have hf_inj : Function.Injective f := by
    intro j k hjk
    apply hinj
    rw [← hf j, ← hf k, hjk]
  simpa using Fintype.card_le_of_injective f hf_inj

end Unimodular.SmoothCompleteFan
