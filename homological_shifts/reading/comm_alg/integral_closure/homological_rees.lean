import CommAlg.IntegralClosure.OrdinaryRees
import CommAlg.Polymatroid.HomologicalMultiplication

/-! # Integral closure of the genuine homological-shift Rees ideals

Every homogeneous coefficient below is the homological shift of an actual
polynomial ideal, defined through its genuine derived-Tor components.
The weight proof is applied only after proving exact equality of carriers.
-/

noncomputable section

namespace CommAlg

open Classical Finset Polymatroid

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]
variable {C : Type*} [Fintype C] [DecidableEq C]

theorem polymatroidal_powerProduct (I : C → Ideal (MvPolynomial V k))
    (hI : ∀ j, IsPolymatroidalIdeal (I j)) (s : C →₀ ℕ) :
    IsPolymatroidalIdeal (powerProduct I s) :=
  IsPolymatroidalIdeal.prod univ (fun j => I j ^ s j) (fun j _ => (hI j).pow (s j))

def homologicalMultiPiece (J : Ideal (MvPolynomial V k))
    (I : C → Ideal (MvPolynomial V k)) (hJ : IsPolymatroidalIdeal J)
    (hI : ∀ j, IsPolymatroidalIdeal (I j)) (i : ℕ) (s : C →₀ ℕ) :
    Ideal (MvPolynomial V k) :=
  homologicalShiftIdeal (J * powerProduct I s) (hJ.mul (polymatroidal_powerProduct I hI s)) i

theorem homologicalMultiPiece_action (J : Ideal (MvPolynomial V k))
    (I : C → Ideal (MvPolynomial V k)) (hJ : IsPolymatroidalIdeal J)
    (hI : ∀ j, IsPolymatroidalIdeal (I j)) (i : ℕ) (s t : C →₀ ℕ) :
    powerProduct I s * homologicalMultiPiece J I hJ hI i t ≤
      homologicalMultiPiece J I hJ hI i (s + t) := by
  have he : powerProduct I s * (J * powerProduct I t) = J * powerProduct I (s + t) := by
    rw [powerProduct_add]
    ac_rfl
  have h := homologicalShiftIdeal_mul_le (powerProduct I s) (J * powerProduct I t)
    (polymatroidal_powerProduct I hI s) (hJ.mul (polymatroidal_powerProduct I hI t)) i
  rw [homologicalShiftIdeal_congr _ (hJ.mul (polymatroidal_powerProduct I hI (s + t))) he i] at h
  exact h

def homologicalMultiIdeal (J : Ideal (MvPolynomial V k))
    (I : C → Ideal (MvPolynomial V k)) (hJ : IsPolymatroidalIdeal J)
    (hI : ∀ j, IsPolymatroidalIdeal (I j)) (i : ℕ) : Ideal (multiReesAlgebra I) :=
  multiReesIdeal I (homologicalMultiPiece J I hJ hI i)
    (homologicalMultiPiece_action J I hJ hI i)

@[simp] theorem mem_homologicalMultiIdeal (J : Ideal (MvPolynomial V k))
    (I : C → Ideal (MvPolynomial V k)) (hJ : IsPolymatroidalIdeal J)
    (hI : ∀ j, IsPolymatroidalIdeal (I j)) (i : ℕ) (p : multiReesAlgebra I) :
    p ∈ homologicalMultiIdeal J I hJ hI i ↔
      ∀ s, p.val.coeff s ∈ homologicalMultiPiece J I hJ hI i s := Iff.rfl

theorem homologicalMultiPiece_rank (η : RankFunction V) (ρ : C → RankFunction V)
    (hJ : IsPolymatroidalIdeal (rankIdeal k η))
    (hI : ∀ j, IsPolymatroidalIdeal (rankIdeal k (ρ j))) (i : ℕ) (s : C →₀ ℕ) :
    homologicalMultiPiece (rankIdeal k η) (fun j => rankIdeal k (ρ j)) hJ hI i s =
      rankShiftMultiFamily η ρ i s := by
  unfold homologicalMultiPiece rankShiftMultiFamily
  apply homologicalShiftIdeal_eq_rankShiftIdeal
  rw [powerProduct, ← rankIdeal_multiRank, rankIdeal_add]

theorem homologicalMultiIdeal_rank (η : RankFunction V) (ρ : C → RankFunction V)
    (hJ : IsPolymatroidalIdeal (rankIdeal k η))
    (hI : ∀ j, IsPolymatroidalIdeal (rankIdeal k (ρ j))) (i : ℕ) :
    homologicalMultiIdeal (rankIdeal k η) (fun j => rankIdeal k (ρ j)) hJ hI i =
      rankShiftMultiIdeal η ρ i := by
  ext p
  simp only [mem_homologicalMultiIdeal, homologicalMultiPiece_rank,
    mem_rankShiftMultiIdeal, rankShiftMultiFamily]

theorem homologicalMultiIdeal_zero_twist (I : C → Ideal (MvPolynomial V k))
    (hJ : IsPolymatroidalIdeal (⊥ : Ideal (MvPolynomial V k)))
    (hI : ∀ j, IsPolymatroidalIdeal (I j)) (i : ℕ) :
    homologicalMultiIdeal ⊥ I hJ hI i = ⊥ := by
  ext p
  simp only [mem_homologicalMultiIdeal, homologicalMultiPiece, Ideal.bot_mul,
    homologicalShiftIdeal_bot, Ideal.mem_bot]
  constructor
  · intro hp
    apply Subtype.ext
    apply MvPolynomial.ext
    simpa using hp
  · rintro rfl
    simp

/-- Corollary 6.2: the entire twisted multi-Rees ideal of genuine
homological shifts is integrally closed. Zero coordinates and the unit
ideal are included; a zero twist gives the zero ideal. -/
theorem homologicalMultiIdeal_integrallyClosed [IsDomain k]
    (J : Ideal (MvPolynomial V k)) (I : C → Ideal (MvPolynomial V k))
    (hJ : IsPolymatroidalIdeal J) (hI : ∀ j, IsPolymatroidalIdeal (I j))
    (hIne : ∀ j, I j ≠ ⊥) (i : ℕ) :
    IsIntegrallyClosedIdeal (homologicalMultiIdeal J I hJ hI i) := by
  rcases hJ.eq_bot_or_rank with h0 | ⟨η, hη⟩
  · subst J
    rw [homologicalMultiIdeal_zero_twist]
    exact integrallyClosed_bot
  · choose ρ hρ using fun j => (hI j).exists_rank (hIne j)
    have he : I = fun j => rankIdeal k (ρ j) := funext hρ
    subst J
    subst I
    rw [homologicalMultiIdeal_rank]
    exact rankShiftMultiIdeal_integrallyClosed η ρ i

def homologicalPowerPiece (I : Ideal (MvPolynomial V k)) (hI : IsPolymatroidalIdeal I)
    (i s : ℕ) : Ideal (MvPolynomial V k) :=
  if s = 0 then ⊥ else homologicalShiftIdeal (I ^ s) (hI.pow s) i

theorem homologicalPowerPiece_action (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i n s : ℕ) :
    I ^ n * homologicalPowerPiece I hI i s ≤ homologicalPowerPiece I hI i (n + s) := by
  by_cases hs : s = 0
  · simp [homologicalPowerPiece, hs]
  · have hns : n + s ≠ 0 := by omega
    simp only [homologicalPowerPiece, if_neg hs, if_neg hns]
    have h := homologicalShiftIdeal_mul_le (I ^ n) (I ^ s) (hI.pow n) (hI.pow s) i
    rw [homologicalShiftIdeal_congr _ (hI.pow (n + s)) (pow_add I n s).symm i] at h
    exact h

def homologicalPowerIdeal (I : Ideal (MvPolynomial V k)) (hI : IsPolymatroidalIdeal I)
    (i : ℕ) : Ideal (reesAlgebra I) where
  carrier := {p | ∀ s, p.val.coeff s ∈ homologicalPowerPiece I hI i s}
  zero_mem' := by simp
  add_mem' hp hq := fun s => by
    simpa only [Subalgebra.coe_add, Polynomial.coeff_add] using
      (homologicalPowerPiece I hI i s).add_mem (hp s) (hq s)
  smul_mem' r p hp := by
    intro s
    change (r.val * p.val).coeff s ∈ homologicalPowerPiece I hI i s
    rw [Polynomial.coeff_mul]
    apply Ideal.sum_mem
    rintro ⟨n, t⟩ hnt
    rw [← Finset.mem_antidiagonal.mp hnt]
    exact homologicalPowerPiece_action I hI i n t
      (Ideal.mul_mem_mul (r.property n) (hp t))

@[simp] theorem mem_homologicalPowerIdeal (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i : ℕ) (p : reesAlgebra I) :
    p ∈ homologicalPowerIdeal I hI i ↔
      ∀ s, p.val.coeff s ∈ homologicalPowerPiece I hI i s := Iff.rfl

theorem homologicalPowerPiece_rank (ρ : RankFunction V)
    (hI : IsPolymatroidalIdeal (rankIdeal k ρ)) (i s : ℕ) :
    homologicalPowerPiece (rankIdeal k ρ) hI i s = powerShiftPiece ρ i s := by
  by_cases hs : s = 0
  · simp [homologicalPowerPiece, powerShiftPiece, hs]
  · simp only [homologicalPowerPiece, powerShiftPiece, if_neg hs]
    exact homologicalShiftIdeal_eq_rankShiftIdeal _ _ (ρ.scale s)
      (rankIdeal_scale k ρ s).symm i

theorem homologicalPowerIdeal_rank (ρ : RankFunction V)
    (hI : IsPolymatroidalIdeal (rankIdeal k ρ)) (i : ℕ) :
    homologicalPowerIdeal (rankIdeal k ρ) hI i = shiftReesIdeal ρ i := by
  ext p
  simp only [mem_homologicalPowerIdeal, homologicalPowerPiece_rank, mem_shiftReesIdeal]

theorem homologicalPowerIdeal_bot
    (hI : IsPolymatroidalIdeal (⊥ : Ideal (MvPolynomial V k))) (i : ℕ) :
    homologicalPowerIdeal ⊥ hI i = ⊥ := by
  have hp (s : ℕ) : homologicalPowerPiece ⊥ hI i s = ⊥ := by
    by_cases hs : s = 0
    · simp [homologicalPowerPiece, hs]
    · simp [homologicalPowerPiece, hs, Ideal.bot_pow hs]
  ext p
  simp only [mem_homologicalPowerIdeal, hp, Ideal.mem_bot]
  constructor
  · intro h
    apply Subtype.ext
    apply Polynomial.ext
    simpa using h
  · rintro rfl
    simp

/-- Theorem 6.1 in its literal ideal form: the positive-power direct sum of
genuine homological shifts is an integrally closed ideal of Mathlib's
ordinary Rees algebra, for every polymatroidal ideal and every `i > 0`. -/
theorem homologicalPowerIdeal_integrallyClosed [IsDomain k]
    (I : Ideal (MvPolynomial V k)) (hI : IsPolymatroidalIdeal I)
    (i : ℕ) (hi : 0 < i) : IsIntegrallyClosedIdeal (homologicalPowerIdeal I hI i) := by
  rcases hI.eq_bot_or_rank with h0 | ⟨ρ, hρ⟩
  · subst I
    rw [homologicalPowerIdeal_bot]
    exact integrallyClosed_bot
  · subst I
    rw [homologicalPowerIdeal_rank]
    exact shiftReesIdeal_integrallyClosed ρ i hi

end CommAlg
