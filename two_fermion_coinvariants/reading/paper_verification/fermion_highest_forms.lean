module

public import PaperVerification.FermionFilteredBasis
public import PaperVerification.FermionDefinitions
public import PaperVerification.FermionOrdinaryParameters
public import PaperVerification.FermionCreatorTriangularity
public import Mathlib.Tactic.FieldSimp

/-!
# The paper's coupled highest forms give literal integer-weight leading forms

Multiplying the rational weights by the product of the covering degrees
preserves every strict comparison. This file derives the ordinary regular
sequence and creator leading polynomials directly from `PairedData`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Filtered

open MvPolynomial
open scoped BigOperators

variable {R ι : Type*} [CommRing R] (w : ι → ℕ)

def HasTop (d : ℕ) (p q : MvPolynomial ι R) : Prop :=
  Bound w d p ∧ weightedHomogeneousComponent w d p = q

theorem HasTop.homogeneous {d : ℕ} {p q : MvPolynomial ι R} (h : HasTop w d p q) :
    q.IsWeightedHomogeneous w d := by
  rw [← h.2]
  exact weightedHomogeneousComponent_isWeightedHomogeneous _ _

theorem HasTop.of_homogeneous {d : ℕ} {p : MvPolynomial ι R}
    (hp : p.IsWeightedHomogeneous w d) : HasTop w d p p :=
  ⟨homogeneous_bound w hp,weightedHomogeneousComponent_eq_self hp⟩

theorem HasTop.C (a : R) : HasTop w 0 (C a) (C a) :=
  HasTop.of_homogeneous w (isWeightedHomogeneous_C w a)

theorem HasTop.one : HasTop w 0 (1 : MvPolynomial ι R) 1 :=
  HasTop.of_homogeneous w (isWeightedHomogeneous_one R w)

theorem HasTop.zero (d : ℕ) : HasTop w d (0 : MvPolynomial ι R) 0 :=
  ⟨bound_zero w d,map_zero _⟩

theorem HasTop.add {d : ℕ} {p p₀ q q₀ : MvPolynomial ι R}
    (hp : HasTop w d p p₀) (hq : HasTop w d q q₀) : HasTop w d (p + q) (p₀ + q₀) :=
  ⟨bound_add w hp.1 hq.1,by rw [map_add,hp.2,hq.2]⟩

theorem HasTop.sub {d : ℕ} {p p₀ q q₀ : MvPolynomial ι R}
    (hp : HasTop w d p p₀) (hq : HasTop w d q q₀) : HasTop w d (p - q) (p₀ - q₀) :=
  ⟨bound_sub w hp.1 hq.1,by rw [map_sub,hp.2,hq.2]⟩

theorem HasTop.mul {d e : ℕ} {p p₀ q q₀ : MvPolynomial ι R}
    (hp : HasTop w d p p₀) (hq : HasTop w e q q₀) : HasTop w (d + e) (p * q) (p₀ * q₀) :=
  ⟨bound_mul w hp.1 hq.1,by rw [component_mul_top w hp.1 hq.1,hp.2,hq.2]⟩

theorem HasTop.pow {d : ℕ} {p p₀ : MvPolynomial ι R}
    (hp : HasTop w d p p₀) (k : ℕ) : HasTop w (k * d) (p ^ k) (p₀ ^ k) := by
  induction k with
  | zero => simpa only [zero_mul,pow_zero] using HasTop.one (R := R) w
  | succ k ih =>
      simpa only [Nat.succ_mul,pow_succ] using HasTop.mul w ih hp

theorem HasTop.sum {J : Type*} (S : Finset J) (p q : J → MvPolynomial ι R) (d : ℕ)
    (h : ∀ j ∈ S, HasTop w d (p j) (q j)) : HasTop w d (∑ j ∈ S, p j) (∑ j ∈ S, q j) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using HasTop.zero (R := R) w d
  | @insert j S hj ih =>
      rw [Finset.sum_insert hj,Finset.sum_insert hj]
      exact HasTop.add w (h j (Finset.mem_insert_self _ _))
        (ih (fun k hk ↦ h k (Finset.mem_insert_of_mem hk)))

theorem HasTop.prod {J : Type*} (S : Finset J) (p q : J → MvPolynomial ι R) (d : J → ℕ)
    (h : ∀ j ∈ S, HasTop w (d j) (p j) (q j)) :
    HasTop w (∑ j ∈ S, d j) (∏ j ∈ S, p j) (∏ j ∈ S, q j) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty,Finset.prod_empty] using HasTop.one (R := R) w
  | @insert j S hj ih =>
      rw [Finset.sum_insert hj,Finset.prod_insert hj,Finset.prod_insert hj]
      exact HasTop.mul w (h j (Finset.mem_insert_self _ _))
        (ih (fun k hk ↦ h k (Finset.mem_insert_of_mem hk)))

end PaperVerification.Fermion.Filtered

namespace PaperVerification.Fermion

open MvPolynomial Filtered Exterior
open scoped BigOperators

section CoefficientRing

variable {R : Type*} [CommRing R] {n : ℕ}

theorem monomialWeight_mul_coveringProduct (r : Fin n → ℕ) (hr : ∀ i, 0 < r i)
    (a : Fin n →₀ ℕ) :
    monomialWeight r a * (∏ i, r i : ℕ) = (Finsupp.weight (coveringWeight r) a : ℚ) := by
  rw [monomialWeight,Finset.sum_mul,Finsupp.weight_eq_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  have hri : (r i : ℚ) ≠ 0 := by exact_mod_cast (hr i).ne'
  have hW : (∏ j, r j : ℕ) = r i * coveringWeight r i := (coveringWeight_mul r i).symm
  have hWq : (∏ j, (r j : ℚ)) = (r i : ℚ) * (coveringWeight r i : ℚ) := by
    exact_mod_cast hW
  rw [hWq]
  simp only [nsmul_eq_mul,Nat.cast_mul,Nat.cast_id]
  field_simp

theorem HasHighestPower.hasTop (r : Fin n → ℕ) (hr : ∀ i, 0 < r i)
    (p : PolynomialRing R n) (i : Fin n) (d : ℕ) (hp : HasHighestPower r p i d) :
    HasTop (coveringWeight r) (d * coveringWeight r i) p (X i ^ d) := by
  classical
  have hW : (0 : ℚ) < (∏ j, r j : ℕ) := by
    exact_mod_cast Finset.prod_pos (fun j _ ↦ hr j)
  have hri : (r i : ℚ) ≠ 0 := by exact_mod_cast (hr i).ne'
  have hsingle : Finsupp.weight (coveringWeight r) (Finsupp.single i d) = d * coveringWeight r i := by
    simp only [Finsupp.weight_single,nsmul_eq_mul,Nat.cast_id]
  have hsmall (a : Fin n →₀ ℕ) (ha : p.coeff a ≠ 0) (hne : a ≠ Finsupp.single i d) :
      Finsupp.weight (coveringWeight r) a < d * coveringWeight r i := by
    have h := mul_lt_mul_of_pos_right (hp.2 a (mem_support_iff.mpr ha) hne) hW
    rw [monomialWeight_mul_coveringProduct r hr] at h
    have hright : (d : ℚ) / r i * (∏ j, r j : ℕ) = d * (coveringWeight r i : ℚ) := by
      rw [← coveringWeight_mul r i]
      push_cast
      field_simp
    rw [hright] at h
    exact_mod_cast h
  constructor
  · intro a ha
    by_cases he : a = Finsupp.single i d
    · rw [he,hsingle]
    · exact (hsmall a ha he).le
  · rw [X_pow_eq_monomial]
    ext a
    rw [coeff_weightedHomogeneousComponent,coeff_monomial]
    by_cases he : a = Finsupp.single i d
    · subst a
      simp only [hsingle,if_true,hp.1]
    · by_cases ha : p.coeff a = 0
      · simp only [ha,he,Ne.symm he,if_false,ite_self]
      · have hw := hsmall a ha he
        simp only [if_neg hw.ne,if_neg he,if_neg (Ne.symm he)]

def coupledOrdinaryMoment (d : PairedData (K := R) (n := n)) (k : ℕ) : PolynomialRing R n :=
  moment d.phi (fun i ↦ C (d.beta i) * d.a i * d.b i) k

def coupledOrdinaryIdeal (d : PairedData (K := R) (n := n)) : Ideal (PolynomialRing R n) :=
  Ideal.span (Set.range (fun k : Fin n ↦ coupledOrdinaryMoment d k))

theorem coupledOrdinaryMoment_mem (d : PairedData (K := R) (n := n)) (k : ℕ) :
    coupledOrdinaryMoment d k ∈ coupledOrdinaryIdeal d := by
  rw [coupledOrdinaryMoment,moment_eq_sum_first]
  exact Ideal.sum_mem _ (fun j hj ↦ Submodule.smul_mem _ _ (Ideal.subset_span ⟨j,rfl⟩))

theorem paired_phi_hasTop (d : PairedData (K := R) (n := n)) (i : Fin n) :
    HasTop (coveringWeight d.r) (∏ j, d.r j) (d.phi i) (X i ^ d.r i) := by
  simpa only [coveringWeight_mul] using
    HasHighestPower.hasTop d.r d.positive_r (d.phi i) i (d.r i) (d.highest_phi i)

theorem paired_a_hasTop (d : PairedData (K := R) (n := n)) (i : Fin n) :
    HasTop (coveringWeight d.r) (d.u i * coveringWeight d.r i) (d.a i) (X i ^ d.u i) :=
  HasHighestPower.hasTop d.r d.positive_r (d.a i) i (d.u i) (d.highest_a i)

theorem paired_b_hasTop (d : PairedData (K := R) (n := n)) (i : Fin n) :
    HasTop (coveringWeight d.r) (d.v i * coveringWeight d.r i) (d.b i) (X i ^ d.v i) :=
  HasHighestPower.hasTop d.r d.positive_r (d.b i) i (d.v i) (d.highest_b i)

end CoefficientRing

section FieldMoments

variable {R : Type*} [Field R] {n : ℕ}

theorem coupledOrdinaryMoment_hasTop (d : PairedData (K := R) (n := n)) (k : ℕ) :
    HasTop (coveringWeight d.r) ((∏ i, d.r i) * (d.s + k))
      (coupledOrdinaryMoment d k) (powerMoment d.r d.beta d.s k) := by
  have hterm (i : Fin n) : HasTop (coveringWeight d.r) ((∏ j, d.r j) * (d.s + k))
      (d.phi i ^ k * (C (d.beta i) * d.a i * d.b i))
      (C (d.beta i) * X i ^ (d.r i * (d.s + k))) := by
    have h := HasTop.mul (coveringWeight d.r) (HasTop.pow _ (paired_phi_hasTop d i) k)
      (HasTop.mul _ (HasTop.mul _ (HasTop.C _ (d.beta i)) (paired_a_hasTop d i))
        (paired_b_hasTop d i))
    have hd : k * (∏ j, d.r j) + (0 + d.u i * coveringWeight d.r i +
        d.v i * coveringWeight d.r i) = (∏ j, d.r j) * (d.s + k) := by
      rw [zero_add,← Nat.add_mul,d.degree_split i]
      have hw := coveringWeight_mul d.r i
      nlinarith
    have he : (X i ^ d.r i : PolynomialRing R n) ^ k *
        (C (d.beta i) * X i ^ d.u i * X i ^ d.v i) =
      C (d.beta i) * X i ^ (d.r i * (d.s + k)) := by
      calc
        _ = C (d.beta i) * X i ^ (d.r i * k + (d.u i + d.v i)) := by
          simp only [pow_add,pow_mul]
          ring
        _ = _ := by
          rw [d.degree_split i]
          congr 2
          ring
    simpa only [hd,he] using h
  simpa only [coupledOrdinaryMoment,moment,smul_eq_mul,powerMoment] using
    HasTop.sum (coveringWeight d.r) Finset.univ _ _ _ (fun i _ ↦ hterm i)

end FieldMoments

section CreatorCoefficients

variable {R : Type*} [CommRing R] {n : ℕ}

def creatorDiagonalDegree (d : PairedData (K := R) (n := n)) : OddIndex n → ℕ
  | .inl i => d.u i * coveringWeight d.r i + (Finset.Ioi i).card * ∏ j, d.r j
  | .inr i => d.v i * coveringWeight d.r i + (Finset.Ioi i).card * ∏ j, d.r j

def creatorWordPolynomial (d : PairedData (K := R) (n := n)) (T : Finset (OddIndex n)) :
    PolynomialRing R n :=
  ∏ j ∈ T, prefixCreatorDiagonal d.phi (fun i ↦ C (d.beta i)) d.a d.b j

def powerCreatorWordPolynomial (d : PairedData (K := R) (n := n)) (T : Finset (OddIndex n)) :
    PolynomialRing R n :=
  ∏ j ∈ T, prefixCreatorDiagonal (fun i ↦ (X i : PolynomialRing R n) ^ d.r i)
    (fun i ↦ C (d.beta i)) (fun i ↦ X i ^ d.u i) (fun i ↦ X i ^ d.v i) j

theorem creatorDiagonal_hasTop (d : PairedData (K := R) (n := n)) (a : OddIndex n) :
    HasTop (coveringWeight d.r) (creatorDiagonalDegree d a)
      (prefixCreatorDiagonal d.phi (fun i ↦ C (d.beta i)) d.a d.b a)
      (prefixCreatorDiagonal (fun i ↦ (X i : PolynomialRing R n) ^ d.r i)
        (fun i ↦ C (d.beta i)) (fun i ↦ X i ^ d.u i) (fun i ↦ X i ^ d.v i) a) := by
  have hsuffix (i : Fin n) : HasTop (coveringWeight d.r) ((Finset.Ioi i).card * ∏ j, d.r j)
      (∏ j ∈ Finset.Ioi i, (d.phi i - d.phi j))
      (∏ j ∈ Finset.Ioi i, ((X i : PolynomialRing R n) ^ d.r i - X j ^ d.r j)) := by
    simpa only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id] using
      HasTop.prod (coveringWeight d.r) (Finset.Ioi i) _ _ (fun _ ↦ ∏ j, d.r j)
        (fun j hj ↦ HasTop.sub _ (paired_phi_hasTop d i) (paired_phi_hasTop d j))
  cases a with
  | inl i =>
      simpa only [creatorDiagonalDegree,prefixCreatorDiagonal,Finset.filter_lt_eq_Ioi,zero_add] using
        HasTop.mul _ (HasTop.mul _ (HasTop.C _ (d.beta i)) (paired_a_hasTop d i)) (hsuffix i)
  | inr i =>
      simpa only [creatorDiagonalDegree,prefixCreatorDiagonal,Finset.filter_lt_eq_Ioi] using
        HasTop.mul _ (paired_b_hasTop d i) (hsuffix i)

theorem creatorWordPolynomial_hasTop (d : PairedData (K := R) (n := n)) (T : Finset (OddIndex n)) :
    HasTop (coveringWeight d.r) (∑ j ∈ T, creatorDiagonalDegree d j)
      (creatorWordPolynomial d T) (powerCreatorWordPolynomial d T) :=
  HasTop.prod _ T _ _ _ (fun j hj ↦ creatorDiagonal_hasTop d j)

end CreatorCoefficients

end PaperVerification.Fermion
