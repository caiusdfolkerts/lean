module

public import PaperVerification.FermionSupport
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# From ordinary moments to radical relations and finiteness

The support calculation can be applied in the fraction field of every prime
quotient. This proves radical containment over an arbitrary commutative base,
without a Nullstellensatz or a characteristic assumption. Monic one-variable
relations in the radical then make the polynomial quotient a finite module.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion

open scoped BigOperators

theorem scalar_moment_map {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (f : R →+* S) (x v : Fin n → R) (k : ℕ) :
    f (moment x v k) = moment (fun i ↦ f (x i)) (fun i ↦ f (v i)) k := by
  simp only [moment, smul_eq_mul, map_sum, map_mul, map_pow]

section Radical

variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A] {n : ℕ}

/-- The first `n` ordinary moments with a common polynomial. -/
def ordinaryMomentIdeal (x : Fin n → A) (β : Fin n → K) (G : Polynomial K) : Ideal A :=
  Ideal.span (Set.range fun k : Fin n ↦
    moment x (fun i ↦ algebraMap K A (β i) * Polynomial.aeval (x i) G) k)

theorem ordinaryMoment_mem (x : Fin n → A) (β : Fin n → K) (G : Polynomial K) (k : ℕ) :
    moment x (fun i ↦ algebraMap K A (β i) * Polynomial.aeval (x i) G) k ∈
      ordinaryMomentIdeal x β G := by
  rw [moment_eq_sum_first]
  apply Submodule.sum_mem
  intro j _
  exact Submodule.smul_mem _ _ (Ideal.subset_span ⟨j, rfl⟩)

/-- Ordinary common-polynomial moments force each common-polynomial value into the radical.

This statement is over arbitrary coefficient rings. It does not assume the
polynomial basis theorem or any finite-dimensionality conclusion.
-/
theorem common_polynomial_mem_radical
    (I : Ideal A) (x : Fin n → A) (β : Fin n → K) (G : Polynomial K)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i))
    (hmom : ∀ k : Fin n,
      moment x (fun i ↦ algebraMap K A (β i) * Polynomial.aeval (x i) G) k ∈ I)
    (i : Fin n) : Polynomial.aeval (x i) G ∈ I.radical := by
  rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
  rintro P ⟨hIP, hP⟩
  letI : P.IsPrime := hP
  let Q := A ⧸ P
  let F := FractionRing Q
  let f : A →+* F := (algebraMap Q F).comp (Ideal.Quotient.mk P)
  let φ : K →+* F := f.comp (algebraMap K A)
  have heval (j : Fin n) :
      f (Polynomial.aeval (x j) G) = (G.map φ).eval (f (x j)) := by
    simp only [Polynomial.aeval_def, Polynomial.hom_eval₂, Polynomial.eval_map, φ]
  have hβF : ∀ U : Finset (Fin n), U.Nonempty → (∑ j ∈ U, φ (β j)) ≠ 0 := by
    intro U hU
    have hu : IsUnit (∑ j ∈ U, φ (β j)) := by
      simpa only [map_sum] using (hβ U hU).map φ
    exact hu.ne_zero
  have hmomF : ∀ k : Fin n,
      moment (fun j ↦ f (x j)) (fun j ↦ φ (β j) * (G.map φ).eval (f (x j))) k = 0 := by
    intro k
    have hmem := hIP (hmom k)
    have hz : f (moment x (fun j ↦ algebraMap K A (β j) * Polynomial.aeval (x j) G) k) = 0 := by
      change algebraMap Q F (Ideal.Quotient.mk P _) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hmem, map_zero]
    simpa only [scalar_moment_map, map_mul, heval, φ, RingHom.comp_apply] using hz
  have hz := (common_polynomial_moments_zero_iff
    (fun j ↦ f (x j)) (fun j ↦ φ (β j)) (G.map φ) hβF).mp hmomF i
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply IsFractionRing.injective Q F
  change f (Polynomial.aeval (x i) G) = algebraMap Q F 0
  rw [heval, hz, map_zero]

/-- The common-polynomial moment ideal has exactly the expected radical.

This is the scheme-theoretic support assertion before separated covers are imposed.
-/
theorem ordinaryMoment_radical
    (x : Fin n → A) (β : Fin n → K) (G : Polynomial K)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i)) :
    (ordinaryMomentIdeal x β G).radical =
      (Ideal.span (Set.range fun i ↦ Polynomial.aeval (x i) G)).radical := by
  apply le_antisymm
  · apply Ideal.radical_mono
    apply Ideal.span_le.mpr
    rintro _ ⟨k, rfl⟩
    apply Submodule.sum_mem
    intro i _
    change x i ^ (k : ℕ) * (algebraMap K A (β i) * Polynomial.aeval (x i) G) ∈ _
    apply Ideal.mul_mem_left
    apply Ideal.mul_mem_left
    exact Ideal.subset_span ⟨i, rfl⟩
  · apply Ideal.radical_le_radical_iff.mpr
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply common_polynomial_mem_radical _ x β G hβ
    exact fun k ↦ ordinaryMoment_mem x β G k

end Radical

section FinitePolynomialQuotient

variable {K : Type*} [CommRing K] {n : ℕ}

/-- A monic univariate relation in the radical makes the corresponding quotient variable integral. -/
theorem quotient_variable_integral_of_radical
    (I : Ideal (MvPolynomial (Fin n) K)) (i : Fin n) (p : Polynomial K)
    (hp : p.Monic)
    (h : Polynomial.aeval (MvPolynomial.X i) p ∈ I.radical) :
    IsIntegral K (Ideal.Quotient.mk I (MvPolynomial.X i)) := by
  obtain ⟨m, hm⟩ := Ideal.mem_radical_iff.mp h
  refine ⟨p ^ m, hp.pow m, ?_⟩
  change Polynomial.aeval ((Ideal.Quotient.mkₐ K I) (MvPolynomial.X i)) (p ^ m) = 0
  rw [Polynomial.aeval_algHom_apply]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  simpa only [map_pow] using hm

/-- Monic univariate radical relations for all variables imply module finiteness.

The relations may have different degrees, and no reducedness or field
hypothesis is needed.
-/
theorem finite_quotient_of_univariate_radical
    (I : Ideal (MvPolynomial (Fin n) K))
    (p : Fin n → Polynomial K) (hp : ∀ i, (p i).Monic)
    (h : ∀ i, Polynomial.aeval (MvPolynomial.X i) (p i) ∈ I.radical) :
    Module.Finite K (MvPolynomial (Fin n) K ⧸ I) := by
  let q := Ideal.Quotient.mkₐ K I
  let v : Fin n → MvPolynomial (Fin n) K ⧸ I := fun i ↦ q (MvPolynomial.X i)
  have hv : ∀ i, IsIntegral K (v i) := fun i ↦
    quotient_variable_integral_of_radical I i (p i) (hp i) (h i)
  have heval : MvPolynomial.aeval v = q := by
    ext i
    simp [v]
  have hadjoin : Algebra.adjoin K (Set.range v) = ⊤ := by
    rw [Algebra.adjoin_range_eq_range_aeval, heval]
    exact (AlgHom.range_eq_top _).mpr (Ideal.Quotient.mkₐ_surjective K I)
  have hfg := fg_adjoin_of_finite (Set.finite_range v) (fun z hz ↦ by
    obtain ⟨i, rfl⟩ := hz
    exact hv i)
  rw [hadjoin] at hfg
  exact Module.Finite.of_fg_top (by simpa using hfg)

/-- The ordinary ideal for separated covers and a common polynomial, with its first `n` moments. -/
def separatedOrdinaryIdeal (β : Fin n → K) (G : Polynomial K)
    (φ : Fin n → Polynomial K) : Ideal (MvPolynomial (Fin n) K) :=
  let x := fun i ↦ Polynomial.aeval (MvPolynomial.X i) (φ i)
  ordinaryMomentIdeal x β G

/-- Finiteness of the separated ordinary common-polynomial quotient.

The hypothesis on each composition is automatic for the monic positive-degree
covers in Section 7. This theorem retains it explicitly so that the zero-ring
case and constant-polynomial cases need no artificial degree convention.
-/
theorem separated_ordinary_finite
    (β : Fin n → K) (G : Polynomial K) (φ : Fin n → Polynomial K)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i))
    (hmonic : ∀ i, (G.comp (φ i)).Monic) :
    Module.Finite K (MvPolynomial (Fin n) K ⧸ separatedOrdinaryIdeal β G φ) := by
  apply finite_quotient_of_univariate_radical _ (fun i ↦ G.comp (φ i)) hmonic
  intro i
  rw [Polynomial.aeval_comp]
  apply common_polynomial_mem_radical _
    (fun i ↦ Polynomial.aeval (MvPolynomial.X i) (φ i)) β G hβ
  intro k
  exact Ideal.subset_span ⟨k, rfl⟩

end FinitePolynomialQuotient

end PaperVerification.Fermion
