module

public import PaperVerification.HomogeneousQuotientProjective
public import PaperVerification.RegularPairProjectiveSections
public import PaperVerification.SingleGeneratorProjectiveSections
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.RingTheory.Regular.IsSMulRegular
public import Mathlib.Order.ConditionallyCompletePartialOrder.Indexed

/-!
# Complete sections for the original one-plane polynomial quotient

The quotient ideal is proved to be zero at the application.  For at least
two variables, distinct original variables form a regular pair.  For a
single variable, homogeneous polynomials are literal scalar multiples of
its powers and the one-chart argument applies.  Thus every nonempty set
of polynomial coordinates, including a projective point, is covered.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.PolynomialQuotientProjectiveSections

open MvPolynomial AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type*} [Field K]

/-- QuotientRing homogeneous polynomial in one variable is its one possible monomial. -/
theorem homogeneous_eq_single_variable [Subsingleton σ] (i : σ) (p : (MvPolynomial σ K)) (d : ℕ)
    (hp : p.IsHomogeneous d) : p=C (p.coeff (Finsupp.single i d))*X i^d := by
  classical
  rw [C_mul_X_pow_eq_monomial]
  ext m
  by_cases hm : m=Finsupp.single i d
  · subst m
    simp
  · have hdegree : m.degree≠d := by
      intro hd
      have he : m=Finsupp.single i (m i) := by
        ext j
        have hji : j=i := Subsingleton.elim _ _
        subst j
        simp
      have hmi : m i=d := by
        have hmdeg := congrArg Finsupp.degree he
        rw [Finsupp.degree_single] at hmdeg
        exact hmdeg.symm.trans hd
      exact hm (he.trans (congrArg (Finsupp.single i) hmi))
    simp only [hp.coeff_eq_zero hdegree,coeff_monomial,if_neg (Ne.symm hm)]

variable (Q : Ideal (MvPolynomial σ K)) (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K))
  (hbot : Q=⊥)

local notation "QuotientRing" => (MvPolynomial σ K)⧸Q
local notation "𝒜" => HomogeneousQuotientProjective.grading (K := K) Q hQ
local notation "φ" => Ideal.Quotient.mkₐ K Q

include hbot in
/-- The quotient map for the proved zero ideal is injective. -/
theorem quotientMap_injective : Function.Injective φ := by
  apply (injective_iff_map_eq_zero φ).mpr
  intro p hp
  have h : p∈Q := Ideal.Quotient.eq_zero_iff_mem.mp hp
  simpa only [hbot,Ideal.mem_bot] using h

include hbot in
theorem coordinate_ne_zero (i : σ) : φ (X i)≠0 := by
  intro h
  exact X_ne_zero i (quotientMap_injective Q hbot (h.trans (map_zero φ).symm))

include hbot in
theorem coordinate_regular (i : σ) : IsRegular (φ (X i)) := by
  haveI : Q.IsPrime := by rw [hbot]; infer_instance
  exact isRegular_iff_ne_zero.mpr (coordinate_ne_zero Q hbot i)

include hbot in
theorem coordinate_dvd_cancel (i j : σ) (hij : i≠j) (z : QuotientRing)
    (hz : φ (X i)∣φ (X j)*z) : φ (X i)∣z := by
  obtain ⟨q,hq⟩ := hz
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mkₐ_surjective K Q z
  obtain ⟨r,rfl⟩ := Ideal.Quotient.mkₐ_surjective K Q q
  have he : X j*p=X i*r := quotientMap_injective Q hbot (by simpa only [map_mul] using hq)
  have hdiv : (X i : (MvPolynomial σ K))∣p := by
    rcases X_dvd_mul_iff.mp (show (X i : (MvPolynomial σ K))∣X j*p from ⟨r,he⟩) with h | h
    · exact (hij (X_dvd_X.mp h)).elim
    · exact h
  obtain ⟨r,hr⟩ := hdiv
  exact ⟨φ r,by rw [hr,map_mul]⟩

include hbot in
theorem coordinate_regular_mod (i j : σ) (hij : i≠j) :
    IsRegular (Ideal.Quotient.mk (Ideal.span ({φ (X i)} : Set QuotientRing)) (φ (X j))) := by
  let U : Ideal QuotientRing := Ideal.span ({φ (X i)} : Set QuotientRing)
  change IsRegular (Ideal.Quotient.mk U (φ (X j)))
  apply (Commute.isRegular_iff
    (fun a : QuotientRing⧸U ↦ Commute.all (Ideal.Quotient.mk U (φ (X j))) a)).mpr
  change IsSMulRegular (QuotientRing⧸U) (Ideal.Quotient.mk U (φ (X j)))
  apply IsSMulRegular.of_right_eq_zero_of_smul
    (R := QuotientRing⧸U) (M := QuotientRing⧸U)
    (r := Ideal.Quotient.mk U (φ (X j)))
  intro z hz
  obtain ⟨w,rfl⟩ := Ideal.Quotient.mk_surjective z
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.mem_span_singleton.mpr
  apply coordinate_dvd_cancel Q hbot i j hij w
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  simpa only [map_mul,smul_eq_mul] using hz

theorem coordinate_cover : (⨆ i : σ,Proj.basicOpen (A := QuotientRing) (σ := Submodule K QuotientRing) 𝒜 (φ (X i)))=⊤ :=
  HomogeneousQuotientProjective.presentation_basicOpen_cover
    (K := K) (σ := σ) (τ := σ) Q hQ (Ideal.Quotient.mkₐ K Q)
    (Ideal.Quotient.mkₐ_surjective K Q)
    (fun i : σ ↦ by
      change Ideal.Quotient.mk Q (X i)∈𝒜 1
      exact HomogeneousQuotientProjective.quotient_X_mem_one Q hQ i)

theorem singleton_piece [Subsingleton σ] (i : σ) (d : ℕ) (r : QuotientRing) (hr : r∈𝒜 d) :
    ∃ c : QuotientRing,c∈𝒜 0 ∧ r=c*φ (X i)^d := by
  rw [HomogeneousQuotientProjective.grading_eq_piece] at hr
  obtain ⟨p,hp,rfl⟩ := hr
  change ∃ c : QuotientRing,c∈𝒜 0 ∧ φ p=c*φ (X i)^d
  refine ⟨φ (C (p.coeff (Finsupp.single i d))),?_,?_⟩
  · rw [HomogeneousQuotientProjective.grading_eq_piece]
    exact ⟨C _,isHomogeneous_C σ _,rfl⟩
  · have he := congrArg (fun z : MvPolynomial σ K ↦ φ z)
      (homogeneous_eq_single_variable i p d hp)
    simpa only [map_mul,map_pow] using he

set_option backward.isDefEq.respectTransparency false in
theorem singleton_coordinate_cover [Subsingleton σ] (i : σ) :
    Proj.basicOpen (A := QuotientRing) (σ := Submodule K QuotientRing) 𝒜 (φ (X i))=⊤ := by
  exact (ciSup_subsingleton i (fun j : σ ↦ Proj.basicOpen (A := QuotientRing) (σ := Submodule K QuotientRing) 𝒜 (φ (X j)))).symm.trans
    (coordinate_cover Q hQ)

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
include K σ Q hQ hbot in
theorem singleton_bijective [Subsingleton σ] (i : σ) (d : ℕ) :
    Function.Bijective (Proj.toTwistingSheaf (A := QuotientRing) (σ := Submodule K QuotientRing) 𝒜 (rfl : (d : ℤ)=d) ⊤) := by
  exact SingleGeneratorProjectiveSections.bijective_toTwistingSheaf_top
    (A := QuotientRing) (σ := Submodule K QuotientRing)
    𝒜 (φ (X i))
    (HomogeneousQuotientProjective.quotient_X_mem_one (K := K) (σ := σ) Q hQ i)
    (coordinate_regular (K := K) (σ := σ) Q hbot i)
    (singleton_coordinate_cover (K := K) (σ := σ) Q hQ i)
    (singleton_piece (K := K) (σ := σ) Q hQ i) d

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
include K σ Q hQ hbot in
theorem pair_bijective (i j : σ) (hij : i≠j) (d : ℕ) :
    Function.Bijective (Proj.toTwistingSheaf (A := QuotientRing) (σ := Submodule K QuotientRing) 𝒜 (rfl : (d : ℤ)=d) ⊤) := by
  exact RegularPairProjectiveSections.bijective_toTwistingSheaf_top
    (A := QuotientRing) (σ := Submodule K QuotientRing) (I := σ)
    𝒜 (fun l : σ ↦ φ (X l))
    (HomogeneousQuotientProjective.quotient_X_mem_one (K := K) (σ := σ) Q hQ)
    (coordinate_regular (K := K) (σ := σ) Q hbot)
    (coordinate_cover (K := K) (σ := σ) Q hQ) i j
    (coordinate_regular_mod (K := K) (σ := σ) Q hbot i j hij) d

set_option backward.isDefEq.respectTransparency false in
include K σ Q hQ hbot in
/-- The genuine all-degree section comparison, including one polynomial variable. -/
theorem bijective_toTwistingSheaf_top [Nonempty σ] (d : ℕ) :
    Function.Bijective (Proj.toTwistingSheaf (A := QuotientRing) (σ := Submodule K QuotientRing) 𝒜 (rfl : (d : ℤ)=d) ⊤) := by
  classical
  obtain ⟨i⟩ := (inferInstance : Nonempty σ)
  rcases subsingleton_or_nontrivial σ with hsub | hnontrivial
  · letI := hsub
    exact singleton_bijective Q hQ hbot i d
  · letI := hnontrivial
    obtain ⟨j,hji⟩ := exists_ne i
    exact pair_bijective Q hQ hbot i j (Ne.symm hji) d

end PaperVerification.PolynomialQuotientProjectiveSections
