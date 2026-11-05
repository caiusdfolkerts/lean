module
public import Papers.RationalityTenPolytopeDensity
public import Mathlib.Tactic.IntervalCases

@[expose] public section
noncomputable section

open Matrix Module Set

namespace Papers.RationalityTen.ChirotopeDensity

/-- A strict supporting form of a proper labelled face is nonzero. -/
theorem strictSupport_normal_ne_zero {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (S : Finset (Fin n)) (a : Fin r → ℝ)
    (ha : StrictSupport p S a) (hS : S ≠ Finset.univ) : a ≠ 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, i ∉ S := by
    by_contra h
    apply hS
    ext i
    simp only [Finset.mem_univ, iff_true]
    exact not_not.mp (fun hn => h ⟨i, hn⟩)
  intro hz
  have hp := ha.2 i hi
  rw [hz, zero_dotProduct] at hp
  exact lt_irrefl 0 hp

/-- Proportional nonzero strict supporting forms have exactly the same
zero labels, including when their proportionality factor is negative. -/
theorem strictSupport_labels_eq_of_smul {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (S T : Finset (Fin n))
    (a b : Fin r → ℝ) (ha : StrictSupport p S a) (hb : StrictSupport p T b)
    (hane : a ≠ 0) (t : ℝ) (ht : t • b = a) : S = T := by
  have htne : t ≠ 0 := by
    intro h
    apply hane
    rw [← ht, h, zero_smul]
  ext i
  constructor
  · intro hi
    by_contra hn
    have hz := ha.1 i hi
    rw [← ht, smul_dotProduct, smul_eq_mul] at hz
    have hbzero := (mul_eq_zero.mp hz).resolve_left htne
    exact (ne_of_gt (hb.2 i hn)) hbzero
  · intro hi
    by_contra hn
    have hz : a ⬝ᵥ p i = 0 := by
      rw [← ht, smul_dotProduct, hb.1 i hi, smul_zero]
    exact (ne_of_gt (ha.2 i hn)) hz

/-- Any family of at most two distinct proper supporting masks has
independent supporting normals. This includes the empty and singleton
families, so the later reconstruction has no exceptional small case. -/
theorem at_most_two_strictSupport_normals_independent {n r k : ℕ}
    (p : Fin n → Fin r → ℝ) (hk : k ≤ 2)
    (H : Fin k → Finset (Fin n)) (hH : Function.Injective H)
    (a : Fin k → Fin r → ℝ) (ha : ∀ j, StrictSupport p (H j) (a j))
    (hproper : ∀ j, H j ≠ Finset.univ) : LinearIndependent ℝ a := by
  interval_cases k
  · exact linearIndependent_empty_type
  · apply linearIndependent_unique_iff.mpr
    exact strictSupport_normal_ne_zero p (H default) (a default) (ha default) (hproper default)
  · apply linearIndependent_fin2.mpr
    refine ⟨strictSupport_normal_ne_zero p (H 1) (a 1) (ha 1) (hproper 1), ?_⟩
    intro t ht
    have heq := strictSupport_labels_eq_of_smul p (H 0) (H 1) (a 0) (a 1)
      (ha 0) (ha 1) (strictSupport_normal_ne_zero p (H 0) (a 0) (ha 0) (hproper 0)) t ht
    have h := hH heq
    exact Fin.zero_ne_one h

#print axioms at_most_two_strictSupport_normals_independent

end Papers.RationalityTen.ChirotopeDensity
