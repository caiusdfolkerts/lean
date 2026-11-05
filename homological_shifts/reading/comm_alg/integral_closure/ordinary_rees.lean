import CommAlg.IntegralClosure.ShiftRees
import CommAlg.Polymatroid.PowerShiftRees

/-! # The ordinary Rees algebra and the positive-power shift ideal

This module applies the full weight proof inside Mathlib's ordinary
`reesAlgebra`. The comparison with one-variable multigrading is an actual
algebra homomorphism with an exact coefficient formula.
-/

noncomputable section

namespace CommAlg

open Classical Finset Polymatroid

variable {R : Type*} [CommRing R]

def reesToMulti (I : Ideal R) : reesAlgebra I →ₐ[R] multiReesAlgebra (fun _ : Unit => I) :=
  ((MvPolynomial.uniqueAlgEquiv R Unit).symm.toAlgHom.comp (reesAlgebra I).val).codRestrict
    (multiReesAlgebra (fun _ : Unit => I)) (by
      intro p s
      change ((MvPolynomial.uniqueAlgEquiv R Unit).symm p.val).coeff s ∈
        powerProduct (fun _ : Unit => I) s
      rw [MvPolynomial.coeff_uniqueAlgEquiv_symm]
      simpa [powerProduct] using p.property (s ()))

@[simp] theorem reesToMulti_coeff (I : Ideal R) (p : reesAlgebra I) (s : Unit →₀ ℕ) :
    ((reesToMulti I p).val).coeff s = p.val.coeff (s ()) :=
  MvPolynomial.coeff_uniqueAlgEquiv_symm _ p.val s

section Ranks

variable {V k : Type*} [Fintype V] [DecidableEq V] [CommRing k] [Nontrivial k]

theorem universalAugmentedRank_zero (A : Finset V) :
    universalAugmentedRank (zeroRank : RankFunction V) A = 0 := by
  apply Nat.eq_zero_of_le_zero
  have h := universalAugmentedRank_le_cost (zeroRank : RankFunction V) (⊥ : Finpartition A)
  simpa [partitionCost, Finpartition.parts_bot, cardinalLift, RankFunction.add,
    cardinalRank] using h

theorem rankShiftIdeal_zeroRank_pos (i : ℕ) (hi : 0 < i) :
    rankShiftIdeal k (zeroRank : RankFunction V) i = ⊥ := by
  have hu : universalHomologicalRank (zeroRank : RankFunction V) i univ = 0 := by
    apply Nat.eq_zero_of_le_zero
    have h := shiftRankValue_le_u (zeroRank : RankFunction V)
      (universalAugmentedRank zeroRank) i univ
    change universalHomologicalRank (zeroRank : RankFunction V) i univ ≤
      universalAugmentedRank zeroRank univ at h
    simpa only [universalAugmentedRank_zero] using h
  simp [rankShiftIdeal, hu, Nat.ne_of_lt hi]

theorem oneColor_rank (ρ : RankFunction V) (s : Unit →₀ ℕ) :
    (zeroRank : RankFunction V).add (multiRank (fun _ : Unit => ρ) s) = ρ.scale (s ()) := by
  apply RankFunction.ext_fun
  intro A
  simp [RankFunction.add, multiRank_apply, RankFunction.scale]

theorem positivePowerPiece_eq_oneColor (ρ : RankFunction V) (i : ℕ) (hi : 0 < i)
    (s : Unit →₀ ℕ) :
    powerShiftPiece (k := k) ρ i (s ()) =
      rankShiftIdeal k (zeroRank.add (multiRank (fun _ : Unit => ρ) s)) i := by
  rw [oneColor_rank]
  by_cases hs : s () = 0
  · rw [hs, powerShiftPiece_zero]
    have he : ρ.scale 0 = (zeroRank : RankFunction V) := by
      apply RankFunction.ext_fun
      intro A
      simp [RankFunction.scale]
    rw [he, rankShiftIdeal_zeroRank_pos i hi]
  · simp [powerShiftPiece, hs]

theorem mem_shiftReesIdeal_iff_oneColor (ρ : RankFunction V) (i : ℕ) (hi : 0 < i)
    (p : reesAlgebra (rankIdeal k ρ)) :
    p ∈ shiftReesIdeal ρ i ↔
      reesToMulti (rankIdeal k ρ) p ∈ rankShiftMultiIdeal zeroRank (fun _ : Unit => ρ) i := by
  rw [mem_shiftReesIdeal, mem_rankShiftMultiIdeal]
  simp only [reesToMulti_coeff, ← positivePowerPiece_eq_oneColor ρ i hi]
  constructor
  · intro h s
    exact h (s ())
  · intro h n
    simpa using h (Finsupp.single () n)

/-- Theorem 6.1 for the formula ideals, in Mathlib's actual ordinary Rees
algebra and with exactly the positive power layers. -/
theorem shiftReesIdeal_integrallyClosed [IsDomain k] (ρ : RankFunction V)
    (i : ℕ) (hi : 0 < i) : IsIntegrallyClosedIdeal (shiftReesIdeal (k := k) ρ i) := by
  let f := (multiReesFlatten (fun _ : Unit => rankIdeal k ρ)).comp
    (reesToMulti (rankIdeal k ρ)).toRingHom
  apply Weight.integrallyClosed_of_weight_bounds f
    (shiftWeight (fun _ : Unit => ρ)) (shiftThreshold zeroRank i)
    (fun t p => shiftWeight_bound_zero (fun _ : Unit => ρ) t (reesToMulti (rankIdeal k ρ) p))
  intro p
  rw [mem_shiftReesIdeal_iff_oneColor ρ i hi, rankShiftMulti_mem_iff_weights]
  rfl

end Ranks

theorem integrallyClosed_bot [IsDomain R] : IsIntegrallyClosedIdeal (⊥ : Ideal R) := by
  intro x hx
  obtain ⟨n, hn, c, hc, he⟩ := hx
  have hcz : ∀ j ∈ range n, c j = 0 := by
    intro j hj
    have hjn := mem_range.mp hj
    have hp : n - j ≠ 0 := by omega
    simpa only [Ideal.bot_pow hp, Ideal.mem_bot] using hc j hjn
  have hz : x ^ n = 0 := by
    have hs : ∑ j ∈ range n, c j * x ^ j = 0 :=
      sum_eq_zero (fun j hj => by rw [hcz j hj, zero_mul])
    simpa only [hs, add_zero] using he
  exact Ideal.mem_bot.mpr (eq_zero_of_pow_eq_zero hz)

end CommAlg
