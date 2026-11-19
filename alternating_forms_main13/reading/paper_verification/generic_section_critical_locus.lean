module

public import PaperVerification.GenericSectionDifferentials
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.Tactic

/-!
# The parameter image of a critical incidence scheme

The evaluation matrix of a generated bundle has a right inverse on the affine
charts used here. A normalized nonzero relation between the differentials at a
common zero therefore forces an algebraic relation among the parameters.
Passing through the finitely many minimal primes produces one nonzero parameter
polynomial that vanishes nilpotently on the entire critical incidence scheme.

The minimal-prime argument adapts `incidence_polynomial` in OpenAI's public
`OAI/AlgebraicGeometry/Seshadri/Bertini/LinearFamilies.lean`, commit
`4eaee87548250b2682affda7d05d947c05554bae`, under Apache-2.0.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Matrix
open KaehlerDifferential

namespace PaperVerification.GenericSectionDifferentials

variable {K L A ι κ : Type*} [Field K] [CharZero K] [Field L] [Algebra K L]
  [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- A right inverse for the evaluation matrix proves independence of its rows. -/
theorem rows_linearIndependent_of_rightInverse
    (v : Matrix κ ι L) (u : Matrix ι κ L) (hvu : v*u=1) :
    LinearIndependent L v := by
  apply Matrix.vecMul_injective_iff.mp
  intro x y h
  have h' := congrArg (fun z => z ᵥ* u) h
  simpa only [Matrix.vecMul_vecMul, hvu, Matrix.vecMul_one] using h'

/-- A normalized relation between the section differentials forces an actual
nonzero polynomial relation among the coefficient parameters. -/
theorem critical_parameters_polynomial [Algebra.EssFiniteType K L]
    (v : Matrix κ ι L) (u : Matrix ι κ L) (hvu : v*u=1)
    (a : ι → L) (c : κ → L) (j₀ : κ) (hc : c j₀=1)
    (hzero : ∀ j, ∑ i, a i*v j i=0)
    (hcritical : ∑ j, c j • (∑ i, a i • D K L (v j i))=0) :
    ∃ p : MvPolynomial ι K, p≠0 ∧ MvPolynomial.aeval a p=0 := by
  have hdep : ¬ AlgebraicIndependent K a := by
    intro ha
    have hlin := section_differentials_linearIndependent v a
      (rows_linearIndependent_of_rightInverse v u hvu) ha hzero
    have hz := Fintype.linearIndependent_iff.mp hlin c hcritical
    exact one_ne_zero (hc.symm.trans (hz j₀))
  rw [algebraicIndependent_iff] at hdep
  push Not at hdep
  obtain ⟨p, hp, hne⟩ := hdep
  exact ⟨p, hne, hp⟩

variable [CommRing A] [Algebra K A]

/-- The critical equations descend to every field-valued point, including the
fraction fields of the irreducible components. -/
theorem critical_parameters_polynomial_image [Algebra.EssFiniteType K L]
    [Algebra A L] [IsScalarTower K A L]
    (v : Matrix κ ι A) (u : Matrix ι κ A) (hvu : v*u=1)
    (a : ι → A) (c : κ → A) (j₀ : κ) (hc : c j₀=1)
    (hzero : ∀ j, ∑ i, a i*v j i=0)
    (hcritical : ∑ j, c j • (∑ i, a i • D K A (v j i))=0) :
    ∃ p : MvPolynomial ι K, p≠0 ∧
      MvPolynomial.aeval (fun i => algebraMap A L (a i)) p=0 := by
  refine critical_parameters_polynomial (v.map (algebraMap A L))
    (u.map (algebraMap A L)) ?_ (fun i => algebraMap A L (a i))
    (fun j => algebraMap A L (c j)) j₀ ?_ ?_ ?_
  · simpa only [Matrix.map_mul, Matrix.map_one, map_zero, map_one] using
      congrArg (Matrix.map · (algebraMap A L)) hvu
  · simpa only [hc, map_one]
  · intro j
    simpa only [Matrix.map_apply, map_sum, map_mul, map_zero] using
      congrArg (algebraMap A L) (hzero j)
  · have h := congrArg (KaehlerDifferential.map K K A L) hcritical
    simpa only [map_sum, map_smul, KaehlerDifferential.map_D, map_zero,
      IsScalarTower.algebraMap_smul, Matrix.map_apply] using h

/-- A single nonzero parameter polynomial vanishes nilpotently on a finite-type
critical incidence algebra. No assumption that its points are reduced is used. -/
theorem critical_incidence_polynomial [Algebra.FiniteType K A]
    (v : Matrix κ ι A) (u : Matrix ι κ A) (hvu : v*u=1)
    (a : ι → A) (c : κ → A) (j₀ : κ) (hc : c j₀=1)
    (hzero : ∀ j, ∑ i, a i*v j i=0)
    (hcritical : ∑ j, c j • (∑ i, a i • D K A (v j i))=0) :
    ∃ p : MvPolynomial ι K, p≠0 ∧ IsNilpotent (MvPolynomial.aeval a p) := by
  classical
  letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  let Q := minimalPrimes A
  letI : Fintype Q := (minimalPrimes.finite_of_isNoetherianRing A).fintype
  have hf : ∀ q : Q, ∃ p : MvPolynomial ι K,
      p≠0 ∧ MvPolynomial.aeval a p ∈ q.val := by
    intro q
    letI : q.val.IsPrime := q.property.isPrime
    let B := A ⧸ q.val
    let F := FractionRing B
    letI : Algebra.EssFiniteType B F :=
      Algebra.EssFiniteType.of_isLocalization F (nonZeroDivisors B)
    letI : Algebra.EssFiniteType K F := Algebra.EssFiniteType.comp K B F
    obtain ⟨p,hp,he⟩ := critical_parameters_polynomial_image (L:=F)
      v u hvu a c j₀ hc hzero hcritical
    refine ⟨p,hp,?_⟩
    have he' : algebraMap A F (MvPolynomial.aeval a p)=0 := by
      change (IsScalarTower.toAlgHom K A F) (MvPolynomial.aeval a p)=0
      rw [MvPolynomial.comp_aeval_apply a (IsScalarTower.toAlgHom K A F)]
      exact he
    have hinj : Function.Injective (algebraMap B F) := IsFractionRing.injective B F
    rw [IsScalarTower.algebraMap_apply A B F] at he'
    have hq : algebraMap A B (MvPolynomial.aeval a p)=0 :=
      hinj (he'.trans (map_zero _).symm)
    exact Ideal.Quotient.eq_zero_iff_mem.mp hq
  choose p hp hm using hf
  refine ⟨∏ q : Q, p q, Finset.prod_ne_zero_iff.mpr (fun q _ => hp q), ?_⟩
  rw [nilpotent_iff_mem_prime]
  intro J hJ
  letI : J.IsPrime := hJ
  obtain ⟨q,hq,hqJ⟩ :=
    Ideal.exists_minimalPrimes_le (I:=(⊥ : Ideal A)) (J:=J) bot_le
  simp only [map_prod]
  apply Ideal.IsPrime.prod_mem_iff.mpr
  exact ⟨⟨q,hq⟩, Finset.mem_univ _, hqJ (hm ⟨q,hq⟩)⟩

end PaperVerification.GenericSectionDifferentials
