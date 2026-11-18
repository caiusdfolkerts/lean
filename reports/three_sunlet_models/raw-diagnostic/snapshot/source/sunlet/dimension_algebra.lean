module

public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.Tactic.NormNum

/-!
# Dimension of finite-type domains

This module derives the Krull-dimension/transcendence-degree bridge from
Mathlib's going-up theorem, incomparability, Noether normalization, and the
dimension of a polynomial ring.  The bridge is proved here rather than taken
as an extra axiom or an implicit convention for the dimension of the model.
-/

@[expose] public section
noncomputable section

namespace Sunlet.DimensionAlgebra

section Order

variable {α β : Type*} [PartialOrder α] [PartialOrder β]

/-- A finite strict chain can be lifted through a surjection with the going-up
property.  Keeping the endpoint is what makes the induction work. -/
theorem exists_lift_series (f : α → β) (hsurj : Function.Surjective f)
    (hup : ∀ a b, f a ≤ b → ∃ a', a ≤ a' ∧ f a' = b) (p : LTSeries β) :
    ∃ q : LTSeries α, q.length = p.length ∧ f q.last = p.last := by
  induction p using RelSeries.inductionOn' with
  | singleton b =>
      obtain ⟨a, ha⟩ := hsurj b
      exact ⟨RelSeries.singleton _ a, rfl, ha⟩
  | snoc p b hpb ih =>
      obtain ⟨q, hlen, hlast⟩ := ih
      obtain ⟨a, hqa, hfa⟩ := hup q.last b (by simpa [hlast] using hpb.le)
      have hlt : q.last < a := lt_of_le_of_ne hqa (by
        intro h
        have : p.last = b := by rw [← hlast, h, hfa]
        exact hpb.ne this)
      refine ⟨q.snoc a hlt, ?_, ?_⟩
      · simpa using congrArg Nat.succ hlen
      · simpa using hfa

theorem krullDim_le_of_goingUp (f : α → β) (hsurj : Function.Surjective f)
    (hup : ∀ a b, f a ≤ b → ∃ a', a ≤ a' ∧ f a' = b) :
    Order.krullDim β ≤ Order.krullDim α := by
  unfold Order.krullDim
  refine iSup_le fun p => ?_
  obtain ⟨q, hlen, _⟩ := exists_lift_series f hsurj hup p
  rw [← hlen]
  exact le_iSup_of_le q le_rfl

end Order

section IntegralExtension

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.IsIntegral R S]

theorem integral_comap_strictMono :
    StrictMono (PrimeSpectrum.comap (algebraMap R S)) := by
  intro p q hpq
  exact Ideal.IsIntegral.under_lt_under (R := R) hpq

theorem ringKrullDim_le_of_integral : ringKrullDim S ≤ ringKrullDim R :=
  Order.krullDim_le_of_strictMono _ (integral_comap_strictMono R S)

theorem ringKrullDim_eq_of_integral [FaithfulSMul R S] :
    ringKrullDim R = ringKrullDim S := by
  apply le_antisymm
  · apply krullDim_le_of_goingUp (PrimeSpectrum.comap (algebraMap R S))
      (Algebra.IsIntegral.comap_surjective R S)
    intro p q hpq
    obtain ⟨Q, hQ, hprime, hcomap⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral q.asIdeal p.asIdeal hpq
    exact ⟨⟨Q, hprime⟩, hQ, PrimeSpectrum.ext hcomap⟩
  · exact ringKrullDim_le_of_integral R S

end IntegralExtension

section FiniteTypeDomain

variable (K A : Type*) [Field K] [CommRing A] [IsDomain A] [Algebra K A]
  [Algebra.FiniteType K A]

/-- For an actual finite-type domain over a field, its Krull dimension is the
finite transcendence degree. -/
theorem ringKrullDim_eq_trdeg_toNat :
    ringKrullDim A = ((Algebra.trdeg K A).toNat : ℕ) := by
  obtain ⟨n, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg K A
  letI : Algebra (MvPolynomial (Fin n) K) A := g.toRingHom.toAlgebra
  haveI : IsScalarTower K (MvPolynomial (Fin n) K) A :=
    IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
  haveI : Algebra.IsIntegral (MvPolynomial (Fin n) K) A := ⟨hint⟩
  haveI : FaithfulSMul (MvPolynomial (Fin n) K) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have hdim : ringKrullDim A = (n : ℕ) := by
    rw [← ringKrullDim_eq_of_integral (MvPolynomial (Fin n) K) A]
    simp
  have htrdeg : n = (Algebra.trdeg K A).toNat := by
    have h := congrArg Cardinal.toNat
      (lift_trdeg_add_eq K (MvPolynomial (Fin n) K) A)
    simpa [trdeg_eq_zero, MvPolynomial.trdeg_of_isDomain] using h
  rw [hdim, ← htrdeg]

theorem ringKrullDim_le_of_trdeg_le (n : ℕ) (h : Algebra.trdeg K A ≤ n) :
    ringKrullDim A ≤ (n : ℕ) := by
  rw [ringKrullDim_eq_trdeg_toNat K A]
  have hn : (Algebra.trdeg K A).toNat ≤ n := by
    simpa using Cardinal.toNat_le_toNat h (by simp)
  exact_mod_cast hn

theorem le_ringKrullDim_of_le_trdeg (n : ℕ) (h : (n : Cardinal) ≤ Algebra.trdeg K A) :
    (n : ℕ) ≤ ringKrullDim A := by
  rw [ringKrullDim_eq_trdeg_toNat K A]
  have hn : n ≤ (Algebra.trdeg K A).toNat := by
    simpa using Cardinal.toNat_le_toNat h (trdeg_lt_aleph0_of_finiteType (R := K) (S := A))
  exact_mod_cast hn

/-- An algebraically independent family gives the required lower dimension
bound for the ordinary prime-ideal-chain definition of dimension. -/
theorem card_le_ringKrullDim_of_algebraicIndependent {ι : Type*} [Fintype ι]
    (x : ι → A) (hx : AlgebraicIndependent K x) :
    (Fintype.card ι : ℕ) ≤ ringKrullDim A := by
  rw [ringKrullDim_eq_trdeg_toNat K A]
  have h := Cardinal.toNat_le_toNat hx.lift_cardinalMk_le_trdeg
    (by simpa only [Cardinal.lift_lt_aleph0] using
      (trdeg_lt_aleph0_of_finiteType (R := K) (S := A)))
  have hn : Fintype.card ι ≤ (Algebra.trdeg K A).toNat := by simpa using h
  exact_mod_cast hn

end FiniteTypeDomain

end Sunlet.DimensionAlgebra
