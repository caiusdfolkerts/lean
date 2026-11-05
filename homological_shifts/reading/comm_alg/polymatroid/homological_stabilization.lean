import CommAlg.Polymatroid.IdealBridge
import CommAlg.Polymatroid.UniversalPowerStabilization
import CommAlg.Rees.BoxGeneration

/-! # Stabilization for actual polynomial ideals

These statements use the genuine derived-Tor homological shift of the actual
ideal powers and products. The zero ideal is included explicitly, as are
arbitrary inactive variables, the unit ideal, and fixed polymatroidal twists.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]

/-- The complete twisted equality of Theorem 1.1, for actual ideals.
The degree-zero case is also valid. -/
theorem homologicalShift_twistedPowers (I J : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (hJ : IsPolymatroidalIdeal J)
    (i s : ℕ) (hs : i ≤ s) :
    homologicalShiftIdeal (J * I ^ (s + 1)) (hJ.mul (hI.pow (s + 1))) i =
      I * homologicalShiftIdeal (J * I ^ s) (hJ.mul (hI.pow s)) i := by
  rcases hI.eq_bot_or_rank with rfl | ⟨ρ, rfl⟩
  · simp
  rcases hJ.eq_bot_or_rank with rfl | ⟨η, rfl⟩
  · simp
  rw [homologicalShiftIdeal_eq_rankShiftIdeal _ _ (twistedPowerRank η ρ (s + 1))
      (rankIdeal_twistedPower k η ρ (s + 1)).symm,
    homologicalShiftIdeal_eq_rankShiftIdeal _ _ (twistedPowerRank η ρ s)
      (rankIdeal_twistedPower k η ρ s).symm]
  exact twistedPower_rankShiftIdeal_succ k η ρ i s hs

/-- Theorem 1.1: no loss of parameter range and no additional activity
hypothesis on the original ideal. -/
theorem homologicalShift_powers (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i s : ℕ) (hs : i ≤ s) :
    homologicalShiftIdeal (I ^ (s + 1)) (hI.pow (s + 1)) i =
      I * homologicalShiftIdeal (I ^ s) (hI.pow s) i := by
  simpa using homologicalShift_twistedPowers I ⊤ hI isPolymatroidalIdeal_top i s hs

section SeveralColors

variable {C : Type*} [Fintype C] [DecidableEq C]

theorem IsPolymatroidalIdeal.powerProduct (I : C → Ideal (MvPolynomial V k))
    (hI : ∀ c, IsPolymatroidalIdeal (I c)) (s : C →₀ ℕ) :
    IsPolymatroidalIdeal (CommAlg.powerProduct I s) :=
  IsPolymatroidalIdeal.prod univ (fun c => I c ^ (s c)) (fun c hc => (hI c).pow (s c))

theorem powerProduct_erase_decompose (I : C → Ideal (MvPolynomial V k))
    (s : C →₀ ℕ) (c : C) :
    CommAlg.powerProduct I s = CommAlg.powerProduct I (s.erase c) * I c ^ (s c) := by
  have he : s.erase c + Finsupp.single c (s c) = s := by
    ext x
    by_cases hx : x = c
    · subst x; simp
    · simp [Finsupp.erase_apply, hx, Ne.symm hx]
  conv_lhs => rw [← he]
  rw [CommAlg.powerProduct_add, CommAlg.powerProduct_single]

theorem twistedPowerProduct_erase_decompose (I : C → Ideal (MvPolynomial V k))
    (J : Ideal (MvPolynomial V k)) (s : C →₀ ℕ) (c : C) :
    J * CommAlg.powerProduct I s =
      (J * CommAlg.powerProduct I (s.erase c)) * I c ^ (s c) := by
  rw [powerProduct_erase_decompose I s c, mul_assoc]

theorem twistedPowerProduct_succ_decompose (I : C → Ideal (MvPolynomial V k))
    (J : Ideal (MvPolynomial V k)) (s : C →₀ ℕ) (c : C) :
    J * CommAlg.powerProduct I (s + Finsupp.single c 1) =
      (J * CommAlg.powerProduct I (s.erase c)) * I c ^ (s c + 1) := by
  rw [twistedPowerProduct_erase_decompose I J (s + Finsupp.single c 1) c]
  have he : (s + Finsupp.single c 1).erase c = s.erase c := by
    ext x
    by_cases hx : x = c
    · subst x; simp
    · simp [Finsupp.erase_apply, hx, Ne.symm hx]
  simp only [he, Finsupp.add_apply, Finsupp.single_eq_same]

/-- The full several-colors equality of Corollary 4.1 on actual ideals,
including zero factors, arbitrary fixed twists and zero exponents. -/
theorem homologicalShift_severalColors (I : C → Ideal (MvPolynomial V k))
    (J : Ideal (MvPolynomial V k)) (hI : ∀ c, IsPolymatroidalIdeal (I c))
    (hJ : IsPolymatroidalIdeal J) (s : C →₀ ℕ) (i : ℕ) (c : C) (hs : i ≤ s c) :
    homologicalShiftIdeal (J * CommAlg.powerProduct I (s + Finsupp.single c 1))
        (hJ.mul (IsPolymatroidalIdeal.powerProduct I hI _)) i =
      I c * homologicalShiftIdeal (J * CommAlg.powerProduct I s)
        (hJ.mul (IsPolymatroidalIdeal.powerProduct I hI _)) i := by
  let K := J * CommAlg.powerProduct I (s.erase c)
  have hK : IsPolymatroidalIdeal K :=
    hJ.mul (IsPolymatroidalIdeal.powerProduct I hI _)
  calc
    _ = homologicalShiftIdeal (K * I c ^ (s c + 1)) (hK.mul ((hI c).pow _)) i :=
      homologicalShiftIdeal_congr _ _ (twistedPowerProduct_succ_decompose I J s c) i
    _ = I c * homologicalShiftIdeal (K * I c ^ (s c)) (hK.mul ((hI c).pow _)) i :=
      homologicalShift_twistedPowers (I c) K (hI c) hK i (s c) hs
    _ = _ := congrArg (I c * ·)
      (homologicalShiftIdeal_congr _ _ (twistedPowerProduct_erase_decompose I J s c).symm i)

end SeveralColors

end CommAlg.Polymatroid
