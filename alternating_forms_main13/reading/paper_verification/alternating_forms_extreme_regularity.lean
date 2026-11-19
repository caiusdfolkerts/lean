module

public import PaperVerification.AlternatingFormsPBWNormalForm
public import PaperVerification.AlternatingFormsOddPrime
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.Algebra.Regular.SMul
public import Mathlib.RingTheory.Regular.IsSMulRegular

/-! Exact graded and projective comparison maps. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms

open MvPolynomial Hibi

section NormalSupport

variable {s n : ℕ} (α β : Fin s → Fin n)

/-- Adjoining a universally comparable index preserves a chain support. -/
theorem normalMonomial_single_add (I : IntervalIndex α β)
    (hI : ∀ J : IntervalIndex α β,I≤J ∨ J≤I)
    (a : IntervalIndex α β →₀ ℕ) (ha : NormalMonomial α β a) :
    NormalMonomial α β (Finsupp.single I 1+a) := by
  classical
  intro J hJ L hL
  have hJ' := Finset.mem_union.mp (Finsupp.support_add hJ)
  have hL' := Finset.mem_union.mp (Finsupp.support_add hL)
  rcases hJ' with hJ' | hJ'
  · have eJ : J=I := Finset.mem_singleton.mp (Finsupp.support_single_subset hJ')
    subst J
    exact hI L
  · rcases hL' with hL' | hL'
    · have eL : L=I := Finset.mem_singleton.mp (Finsupp.support_single_subset hL')
      subst L
      exact (hI J).symm
    · exact ha J hJ' L hL'

/-- Multiplication by an extreme coordinate does not require straightening. -/
theorem normalSupport_X_mul {K : Type*} [Field K]
    (I : IntervalIndex α β) (hI : ∀ J : IntervalIndex α β,I≤J ∨ J≤I)
    (p : MvPolynomial (IntervalIndex α β) K)
    (hp : ∀ a∈p.support,NormalMonomial α β a) :
    ∀ a∈(X I*p).support,NormalMonomial α β a := by
  classical
  intro a ha
  rw [support_X_mul] at ha
  obtain ⟨b,hb,rfl⟩ := Finset.mem_map.mp ha
  exact normalMonomial_single_add α β I hI b (hp b hb)

/-- A single variable is a normal polynomial. -/
theorem normalSupport_X {K : Type*} [Field K] (I : IntervalIndex α β) :
    ∀ a∈(X I : MvPolynomial (IntervalIndex α β) K).support,
      NormalMonomial α β a := by
  classical
  intro a ha
  have ha' : a=Finsupp.single I 1 :=
    Finset.mem_singleton.mp (support_monomial_subset ha)
  subst a
  intro J hJ L hL
  have eJ : J=I := Finset.mem_singleton.mp (Finsupp.support_single_subset hJ)
  have eL : L=I := Finset.mem_singleton.mp (Finsupp.support_single_subset hL)
  exact Or.inl (by rw [eJ,eL])

end NormalSupport

variable {K : Type*} [Field K] [CharZero K]
  (k t : ℕ) (hs : t+2≤k+1)

local notation "α" => oddIntervalLower k (t+2) hs
local notation "β" => oddIntervalUpper k (t+2) hs
local notation "Q" => isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k)
local notation "A" => MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸Q
local notation "φ" => oddGoodMap (K := K) k t hs

/-- Every good coordinate survives in the literal original quotient. -/
theorem oddGoodCoordinate_ne_zero (I : IntervalIndex α β) : φ (X I)≠0 := by
  intro h
  exact X_ne_zero I (oddGood_normal_polynomial_eq_zero k t hs (X I)
    (normalSupport_X α β I) h)

/-- Divisibility by one extreme coordinate is not introduced by multiplying
by a different extreme coordinate in the actual Plucker quotient. -/
theorem oddGoodCoordinate_dvd_of_dvd_mul
    (I J : IntervalIndex α β) (hIJ : I≠J)
    (hI : ∀ L : IntervalIndex α β,I≤L ∨ L≤I)
    (hJ : ∀ L : IntervalIndex α β,J≤L ∨ L≤J)
    (z : A) (hz : φ (X I)∣φ (X J)*z) : φ (X I)∣z := by
  classical
  obtain ⟨r,hr⟩ := hz
  obtain ⟨p,rfl⟩ := oddGoodMap_surjective k t hs z
  obtain ⟨q,rfl⟩ := oddGoodMap_surjective k t hs r
  let p' := oddGoodNormalForm (K := K) k t hs p
  let q' := oddGoodNormalForm (K := K) k t hs q
  have hp : ∀ a∈p'.support,NormalMonomial α β a :=
    oddGoodNormalForm_normal k t hs p
  have hq : ∀ a∈q'.support,NormalMonomial α β a :=
    oddGoodNormalForm_normal k t hs q
  have he : X J*p'=X I*q' := by
    apply sub_eq_zero.mp
    apply oddGood_normal_polynomial_eq_zero k t hs (X J*p'-X I*q')
    · intro a ha
      rcases Finset.mem_union.mp (support_sub _ _ _ ha) with ha | ha
      · exact normalSupport_X_mul α β J hJ p' hp a ha
      · exact normalSupport_X_mul α β I hI q' hq a ha
    · simp only [map_sub,map_mul,p',q',oddGoodMap_normalForm]
      exact sub_eq_zero.mpr hr
  have hdiv : (X I : MvPolynomial (IntervalIndex α β) K)∣p' := by
    have hmul : (X I : MvPolynomial (IntervalIndex α β) K)∣X J*p' := ⟨q',he⟩
    rcases X_dvd_mul_iff.mp hmul with h | h
    · exact False.elim (hIJ (X_dvd_X.mp h))
    · exact h
  obtain ⟨w,hw⟩ := hdiv
  refine ⟨φ w,?_⟩
  calc
    φ p = φ p' := (oddGoodMap_normalForm k t hs p).symm
    _ = φ (X I)*φ w := by rw [hw,map_mul]

/-- The regularity condition is in the ordinary principal-ideal quotient. -/
theorem oddGoodCoordinate_regular_mod
    (I J : IntervalIndex α β) (hIJ : I≠J)
    (hI : ∀ L : IntervalIndex α β,I≤L ∨ L≤I)
    (hJ : ∀ L : IntervalIndex α β,J≤L ∨ L≤J) :
    IsRegular (Ideal.Quotient.mk (Ideal.span ({φ (X I)} : Set A)) (φ (X J))) := by
  let U : Ideal A := Ideal.span ({φ (X I)} : Set A)
  apply (Commute.isRegular_iff (R := A⧸U)
    (a := Ideal.Quotient.mk U (φ (X J))) (fun a ↦ Commute.all _ a)).mpr
  change IsSMulRegular (A⧸U) (Ideal.Quotient.mk U (φ (X J)))
  apply IsSMulRegular.of_right_eq_zero_of_smul (R := A⧸U) (M := A⧸U)
  intro z hz
  obtain ⟨w,rfl⟩ := Ideal.Quotient.mk_surjective z
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.mem_span_singleton.mpr
  apply oddGoodCoordinate_dvd_of_dvd_mul k t hs I J hIJ hI hJ w
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  simpa only [map_mul,smul_eq_mul] using hz

/-- The actual lower endpoint, regarded as a good coordinate. -/
def oddLeastGoodIndex : IntervalIndex α β :=
  ⟨⟨α,oddIntervalLower_strictMono k (t+2) hs⟩,
    fun i ↦ ⟨le_rfl,oddIntervalLower_le_upper k (t+2) hs i⟩⟩

/-- The actual upper endpoint, regarded as a good coordinate. -/
def oddGreatestGoodIndex : IntervalIndex α β :=
  ⟨⟨β,oddIntervalUpper_strictMono k (t+2) hs⟩,
    fun i ↦ ⟨oddIntervalLower_le_upper k (t+2) hs i,le_rfl⟩⟩

theorem oddLeastGoodIndex_le (I : IntervalIndex α β) : oddLeastGoodIndex k t hs≤I :=
  fun i ↦ (I.property i).1

theorem le_oddGreatestGoodIndex (I : IntervalIndex α β) : I≤oddGreatestGoodIndex k t hs :=
  fun i ↦ (I.property i).2

theorem oddLeastGoodIndex_ne_greatest (hstrict : t+2<k+1) :
    oddLeastGoodIndex k t hs≠oddGreatestGoodIndex k t hs := by
  intro h
  have he := congrArg (fun I : IntervalIndex α β ↦ (I.val.val (0 : Fin (t+2))).val) h
  change 2*0=2*(k+1-(t+2)+0) at he
  omega

/-- In every positive-dimensional interval, the two extremal good coordinates
form a genuine regular pair in the original common-isotropic ring. -/
theorem odd_extremeCoordinates_regularPair (hstrict : t+2<k+1) :
    IsRegular (φ (X (oddLeastGoodIndex k t hs))) ∧
    IsRegular (Ideal.Quotient.mk
      (Ideal.span ({φ (X (oddLeastGoodIndex k t hs))} : Set A))
      (φ (X (oddGreatestGoodIndex k t hs)))) := by
  letI : (Q).IsPrime := odd_isotropicPluckerIdeal_isPrime k t hs
  exact ⟨isRegular_iff_ne_zero.mpr (oddGoodCoordinate_ne_zero k t hs _),
    oddGoodCoordinate_regular_mod k t hs _ _
      (oddLeastGoodIndex_ne_greatest k t hs hstrict)
      (fun I ↦ Or.inl (oddLeastGoodIndex_le k t hs I))
      (fun I ↦ Or.inr (le_oddGreatestGoodIndex k t hs I))⟩

end PaperVerification.AlternatingForms
