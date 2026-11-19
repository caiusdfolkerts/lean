module

public import PaperVerification.SegreCoordinateLocalization
public import Mathlib.Algebra.MonoidAlgebra.Grading
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Integer degrees and homogeneous fractions in coordinate localizations

The Laurent model carries its literal total-exponent grading. Every element
of degree `t` has one homogeneous numerator over a power of the coordinate
product, with numerator degree exactly the denominator degree plus `t`.
This is the precise form required by the twisting-sheaf section comparison.
-/

set_option autoImplicit false

@[expose] public section

namespace PaperVerification.Segre.CoordinateLocalization

open scoped BigOperators

variable {I K : Type*} [Fintype I] [DecidableEq I] [CommRing K]

def totalDegree (S : Finset I) : allowedExponents S →+ ℤ where
  toFun a := ∑ i, a.val i
  map_zero' := by simp
  map_add' a b := by simp only [AddSubmonoid.coe_add,Pi.add_apply,Finset.sum_add_distrib]

abbrev localDegree (S : Finset I) (t : ℤ) : Submodule K (LocalLaurent K I S) :=
  AddMonoidAlgebra.gradeBy K (totalDegree S) t

theorem totalDegree_natural (S : Finset I) (a : I →₀ ℕ) :
    totalDegree S (naturalExponentMap S a)=(a.degree : ℤ) := by
  change (∑ i, (a i : ℤ)) = (a.degree : ℤ)
  simp only [Finsupp.degree_eq_sum, Nat.cast_sum]

theorem localizationMap_coeff (S : Finset I) (p : MvPolynomial I K) (a : I →₀ ℕ) :
    (localizationMap S p).coeff (naturalExponentMap S a)=p.coeff a :=
  Finsupp.mapDomain_apply_of_injective (naturalExponentMap_injective S) p.coeff a

/-- The integer grading of a polynomial image is precisely its ordinary monomial grading. -/
theorem localizationMap_mem_degree_iff (S : Finset I) (p : MvPolynomial I K) (t : ℤ) :
    localizationMap S p ∈ localDegree S t ↔
      ∀ a : I →₀ ℕ, p.coeff a≠0 → (a.degree : ℤ)=t := by
  classical
  constructor
  · intro hp a ha
    have hm : naturalExponentMap S a ∈ (localizationMap S p).coeff.support := by
      rw [Finsupp.mem_support_iff,localizationMap_coeff]
      exact ha
    simpa only [totalDegree_natural] using hp _ hm
  · intro hp a ha
    have hc : (Finsupp.mapDomain (naturalExponentMap S) p.coeff) a≠0 :=
      Finsupp.mem_support_iff.mp ha
    obtain ⟨b,rfl⟩ := Finsupp.mem_range_of_mapDomain_ne_zero hc
    rw [Finsupp.mapDomain_apply_of_injective (naturalExponentMap_injective S)] at hc
    exact (totalDegree_natural S b).trans (hp b hc)

theorem localizationMap_mem_degree (S : Finset I) {j : ℕ} {p : MvPolynomial I K}
    (hp : p ∈ MvPolynomial.homogeneousSubmodule I K j) :
    localizationMap S p ∈ localDegree S (j : ℤ) := by
  apply (localizationMap_mem_degree_iff S p j).mpr
  intro a ha
  have h : a.degree=j := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hp ha
  exact congrArg (fun z : ℕ => (z : ℤ)) h

theorem homogeneous_of_localizationMap_mem (S : Finset I) {j : ℕ} {p : MvPolynomial I K}
    (hp : localizationMap S p ∈ localDegree S (j : ℤ)) :
    p ∈ MvPolynomial.homogeneousSubmodule I K j := by
  intro a ha
  have h : a.degree=j := Int.natCast_inj.mp ((localizationMap_mem_degree_iff S p j).mp hp a ha)
  simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using h

/-- The polynomial whose inversion defines the chart intersection. -/
noncomputable def denominator (S : Finset I) : MvPolynomial I K := ∏ i ∈ S, MvPolynomial.X i

theorem localizationMap_denominator (S : Finset I) :
    localizationMap S (denominator (K := K) S) =
      AddMonoidAlgebra.single (naturalExponentMap S (denominatorExponent S)) 1 := by
  rw [denominator,← denominator_monomial_eq_prod]
  exact AddMonoidAlgebra.mapDomain_single

theorem denominator_homogeneous (S : Finset I) :
    denominator (K := K) S ∈ MvPolynomial.homogeneousSubmodule I K S.card := by
  apply (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
  simpa only [denominator,Finset.sum_const,smul_eq_mul,mul_one] using
    MvPolynomial.IsHomogeneous.prod S (fun i => (MvPolynomial.X i : MvPolynomial I K))
      (fun _ => 1) (fun i _ => MvPolynomial.isHomogeneous_X (R := K) i)

theorem denominator_image_isUnit (S : Finset I) :
    IsUnit (localizationMap S (denominator (K := K) S)) := by
  rw [localizationMap_denominator]
  exact denominator_isUnit S

theorem denominator_image_degree (S : Finset I) :
    localizationMap S (denominator (K := K) S) ∈ localDegree S (S.card : ℤ) :=
  localizationMap_mem_degree S (denominator_homogeneous S)

/-- The homogeneous numerator/denominator representation of every Laurent section. -/
theorem homogeneous_fraction (S : Finset I) (hS : S.Nonempty) (t : ℤ)
    (x : LocalLaurent K I S) (hx : x ∈ localDegree S t) :
    ∃ (m j : ℕ) (p : MvPolynomial I K),
      (j : ℤ)=(m*S.card : ℕ)+t ∧
      p ∈ MvPolynomial.homogeneousSubmodule I K j ∧
      x*(localizationMap S (denominator S))^m=localizationMap S p := by
  classical
  letI : IsLocalization.Away (denominator (K := K) S) (LocalLaurent K I S) := by
    change IsLocalization.Away (∏ i ∈ S, (MvPolynomial.X i : MvPolynomial I K))
      (LocalLaurent K I S)
    exact localLaurent_isLocalization S
  obtain ⟨m,p,hp⟩ := IsLocalization.Away.surj (denominator (K := K) S) x
  change x*(localizationMap S (denominator S))^m=localizationMap S p at hp
  have hdeg : localizationMap S p ∈ localDegree S (t+m • (S.card : ℤ)) := by
    rw [← hp]
    exact SetLike.mul_mem_graded hx (SetLike.pow_mem_graded m (denominator_image_degree S))
  by_cases hp0 : p=0
  · have hx0 : x=0 := by
      apply (IsUnit.mul_left_eq_zero ((denominator_image_isUnit S).pow m)).mp
      rw [hp,hp0,map_zero]
    let r : ℕ := (-t).toNat
    have hr : -t≤(r : ℤ) := by dsimp [r]; omega
    have hcard : 0<S.card := hS.card_pos
    have hmul : r≤r*S.card := Nat.le_mul_of_pos_right r hcard
    have hmul' : (r : ℤ)≤((r*S.card : ℕ) : ℤ) := by omega
    have hnonneg : 0≤((r*S.card : ℕ) : ℤ)+t := by omega
    refine ⟨r,(((r*S.card : ℕ) : ℤ)+t).toNat,0,?_,?_,?_⟩
    · exact Int.toNat_of_nonneg hnonneg
    · exact Submodule.zero_mem _
    · rw [hx0,zero_mul,map_zero]
  · obtain ⟨a,ha⟩ := MvPolynomial.exists_coeff_ne_zero hp0
    have he := (localizationMap_mem_degree_iff S p _).mp hdeg a ha
    have hnonneg : 0≤t+m • (S.card : ℤ) := he ▸ Int.natCast_nonneg a.degree
    refine ⟨m,(t+m • (S.card : ℤ)).toNat,p,?_,?_,hp⟩
    · rw [Int.toNat_of_nonneg hnonneg]
      simp only [nsmul_eq_mul,Int.natCast_mul]
      omega
    · apply homogeneous_of_localizationMap_mem S
      rw [Int.toNat_of_nonneg hnonneg]
      exact hdeg

end PaperVerification.Segre.CoordinateLocalization
