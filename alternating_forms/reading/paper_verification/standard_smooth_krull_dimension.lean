/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
See https://www.apache.org/licenses/LICENSE-2.0 for the license.

Adapted from openai/math, commit 4eaee87548250b2682affda7d05d947c05554bae,
OAI/Algebra/RingTheory/SmoothKrullDimension.lean. This version generalizes the
field statement from complex numbers to every field and uses current Mathlib
imports. All proofs are included and must pass the same kernel audit.
-/
module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Standard smooth dimension is actual Krull dimension over a field

A standard smooth algebra of relative dimension d is étale over a polynomial
algebra in d variables. Quasi-finiteness bounds prime chains from above; flat
going-down preserves prime heights. A maximal ideal over the polynomial base
therefore supplies the matching lower bound whenever the algebra is nonzero.
-/

@[expose] public section
noncomputable section

open Algebra MvPolynomial RingHom

namespace PaperVerification.StandardSmoothKrullDimension

section QuasiFinite

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem quasiFinite_strictMono_comap [QuasiFinite R S] :
    StrictMono (PrimeSpectrum.comap (algebraMap R S)) := by
  intro P Q hPQ
  have hle : P.asIdeal.under R ≤ Q.asIdeal.under R := Ideal.comap_mono hPQ.le
  refine lt_of_le_of_ne hle ?_
  intro heq
  have heq' : P.asIdeal.under R = Q.asIdeal.under R := by
    simpa [Ideal.under] using congrArg PrimeSpectrum.asIdeal heq
  have hPQeq : P.asIdeal = Q.asIdeal :=
    QuasiFinite.eq_of_le_of_under_eq (R := R) P.asIdeal Q.asIdeal hPQ.le heq'
  exact hPQ.ne (PrimeSpectrum.ext hPQeq)

theorem quasiFinite_ringKrullDim_le [QuasiFinite R S] :
    ringKrullDim S ≤ ringKrullDim R := by
  rw [ringKrullDim, ringKrullDim]
  exact Order.krullDim_le_of_strictMono _ quasiFinite_strictMono_comap

theorem quasiFinite_height_eq_under [QuasiFinite R S] [Module.Flat R S]
    (P : Ideal S) [P.IsPrime] : P.height = (P.under R).height := by
  calc
    P.height = Order.height (⟨P, inferInstance⟩ : PrimeSpectrum S) :=
      PrimeSpectrum.height_eq_orderHeight (⟨P, inferInstance⟩ : PrimeSpectrum S)
    _ = Order.height
        (PrimeSpectrum.comap (algebraMap R S) (⟨P, inferInstance⟩ : PrimeSpectrum S)) := by
      apply Order.height_eq_of_strictMono (PrimeSpectrum.comap (algebraMap R S))
        quasiFinite_strictMono_comap
      intro Q p hp
      have hp' : p.asIdeal < Q.asIdeal.under R := by
        have hp'' : p.asIdeal < (PrimeSpectrum.comap (algebraMap R S) Q).asIdeal := hp
        simpa only [Ideal.under, PrimeSpectrum.comap_asIdeal] using hp''
      obtain ⟨Q', hQ'Q, hQ'prime, hQ'over⟩ :=
        Q.asIdeal.exists_ideal_lt_liesOver_of_lt
          (R := R) (p := p.asIdeal) (q := Q.asIdeal.under R) hp'
      refine ⟨⟨Q', hQ'prime⟩, hQ'Q, ?_⟩
      apply PrimeSpectrum.ext
      simpa [Ideal.under] using hQ'over.over.symm
    _ = (P.under R).height := by
      rw [show (P.under R) =
        (PrimeSpectrum.comap (algebraMap R S)
          (⟨P, inferInstance⟩ : PrimeSpectrum S)).asIdeal from rfl]
      exact (PrimeSpectrum.height_eq_orderHeight
        (PrimeSpectrum.comap (algebraMap R S)
          (⟨P, inferInstance⟩ : PrimeSpectrum S))).symm

end QuasiFinite

theorem finiteType_maximal_comap {R S : Type*} [CommRing R] [CommRing S]
    [IsJacobsonRing R] {f : R →+* S} (hf : f.FiniteType)
    (P : Ideal S) [P.IsMaximal] : (P.comap f).IsMaximal := by
  let L := S ⧸ P
  let q : S →+* L := Ideal.Quotient.mk P
  letI : Field L := Ideal.Quotient.field P
  have hft : (q.comp f).FiniteType := hf.comp_surjective Ideal.Quotient.mk_surjective
  have hfin : (q.comp f).Finite := RingHom.finite_iff_finiteType_of_isJacobsonRing.mpr hft
  have hmax : ((⊥ : Ideal L).comap (q.comp f)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (q.comp f) hfin.to_isIntegral ⊥
  change (((⊥ : Ideal L).comap q).comap f).IsMaximal at hmax
  have hq : (⊥ : Ideal L).comap q = P := by
    rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  rwa [hq] at hmax

/-- A maximal ideal of a polynomial algebra over any field has the full height. -/
theorem polynomial_maximal_height (K : Type*) [Field K] (d : ℕ)
    (P : Ideal (MvPolynomial (Fin d) K)) [P.IsMaximal] : P.height = d := by
  induction d with
  | zero =>
      have hle : (↑P.height : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin 0) K) :=
        Ideal.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top'
      simp only [MvPolynomial.ringKrullDim_of_isNoetherianRing,
        ringKrullDim_eq_zero_of_field, ENat.card_eq_coe_fintype_card, Fintype.card_fin,
        Nat.cast_zero, WithBot.coe_zero, zero_add] at hle
      exact le_antisymm (WithBot.coe_le_coe.mp hle) bot_le
  | succ n ih =>
      let e : MvPolynomial (Fin (n + 1)) K ≃+* Polynomial (MvPolynomial (Fin n) K) :=
        (MvPolynomial.finSuccEquiv K n).toRingEquiv
      let Q : Ideal (Polynomial (MvPolynomial (Fin n) K)) := P.map e
      letI : Q.IsMaximal := Ideal.map_isMaximal_of_equiv e
      letI : (Q.under (MvPolynomial (Fin n) K)).IsMaximal := by
        change (Q.comap (Polynomial.C : MvPolynomial (Fin n) K →+*
          Polynomial (MvPolynomial (Fin n) K))).IsMaximal
        exact Polynomial.isMaximal_comap_C_of_isJacobsonRing Q
      calc
        P.height = Q.height := (RingEquiv.height_map e P).symm
        _ = (Q.under (MvPolynomial (Fin n) K)).height + 1 :=
          Polynomial.height_eq_height_add_one _ Q
        _ = n + 1 := by rw [ih (Q.under (MvPolynomial (Fin n) K))]

variable {K S : Type*} [Field K] [CommRing S] {f : K →+* S} {d : ℕ}

/-- Standard smooth relative dimension is a genuine upper bound on prime chains. -/
theorem standardSmooth_ringKrullDim_le (hf : f.IsStandardSmoothOfRelativeDimension d) :
    ringKrullDim S ≤ (d : ℕ) := by
  obtain ⟨g, _, hg⟩ := hf.exists_etale_mvPolynomial
  letI : Algebra (MvPolynomial (Fin d) K) S := g.toAlgebra
  letI : Algebra.Etale (MvPolynomial (Fin d) K) S := RingHom.etale_algebraMap.mp hg
  calc
    ringKrullDim S ≤ ringKrullDim (MvPolynomial (Fin d) K) := quasiFinite_ringKrullDim_le
    _ = (d : ℕ) := by simp

/-- Every nonzero standard smooth algebra over a field has exactly the
relative dimension given by its presentation. -/
theorem standardSmooth_ringKrullDim_eq [Nontrivial S]
    (hf : f.IsStandardSmoothOfRelativeDimension d) : ringKrullDim S = (d : ℕ) := by
  obtain ⟨g, _, hg⟩ := hf.exists_etale_mvPolynomial
  letI : Algebra (MvPolynomial (Fin d) K) S := g.toAlgebra
  letI : Algebra.Etale (MvPolynomial (Fin d) K) S := RingHom.etale_algebraMap.mp hg
  obtain ⟨P, hP⟩ := Ideal.exists_maximal S
  letI : P.IsMaximal := hP
  have hfiniteType : (algebraMap (MvPolynomial (Fin d) K) S).FiniteType :=
    RingHom.finiteType_algebraMap.mpr inferInstance
  letI : (P.under (MvPolynomial (Fin d) K)).IsMaximal :=
    finiteType_maximal_comap hfiniteType P
  have hheight : P.height = d := by
    rw [quasiFinite_height_eq_under (R := MvPolynomial (Fin d) K)]
    exact polynomial_maximal_height K d (P.under (MvPolynomial (Fin d) K))
  apply le_antisymm (standardSmooth_ringKrullDim_le hf)
  change (↑(d : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim S
  have hlower : (↑P.height : WithBot ℕ∞) ≤ ringKrullDim S :=
    Ideal.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top'
  rwa [← hheight]

end PaperVerification.StandardSmoothKrullDimension
