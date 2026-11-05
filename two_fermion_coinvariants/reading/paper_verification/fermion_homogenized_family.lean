module

public import PaperVerification.FermionPairedIndex
public import PaperVerification.FermionHighestPowerMonomial
public import PaperVerification.FermionPairedAlgebraBaseChange
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# The literal finite free weighted homogenized family

The parameter is the ordinary polynomial variable over the original ring.
Each coefficient is multiplied by the exact missing integer weight, after
clearing the positive covering denominators.  The arbitrary-ring theorem
applies to these actual coefficients.  The fibers at zero and one are
identified as algebras through the proved quotient scalar-extension map.

The associated-graded/Rees
identification is a separate assertion and is not assumed here.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PaperVerification.Fermion

open MvPolynomial Exterior
open scoped BigOperators TensorProduct

variable {R : Type*} [CommRing R] {n : ℕ}

local instance FermionHomogenizedFamily_localInst_1 : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' modeRank modeRank_injective

def weightedHomogenize (w : Fin n → ℕ) (D : ℕ) (p : PolynomialRing R n) :
    PolynomialRing (Polynomial R) n :=
  ∑ a ∈ p.support, monomial a (Polynomial.C (p.coeff a) *
    Polynomial.X^(D-Finsupp.weight w a))

@[simp] theorem weightedHomogenize_coeff (w : Fin n → ℕ) (D : ℕ)
    (p : PolynomialRing R n) (a : Fin n →₀ ℕ) :
    (weightedHomogenize w D p).coeff a =
      Polynomial.C (p.coeff a) * Polynomial.X^(D-Finsupp.weight w a) := by
  classical
  by_cases ha : a ∈ p.support
  · simp [weightedHomogenize,coeff_sum,coeff_monomial,ha]
  · have hz := MvPolynomial.notMem_support_iff.mp ha
    simp [weightedHomogenize,coeff_sum,coeff_monomial,ha,hz]

@[simp] theorem weightedHomogenize_at_one (w : Fin n → ℕ) (D : ℕ)
    (p : PolynomialRing R n) :
    MvPolynomial.map (Polynomial.evalRingHom (1 : R)) (weightedHomogenize w D p) = p := by
  ext a
  rw [coeff_map,weightedHomogenize_coeff]
  simp

theorem weightedHomogenize_at_zero (w : Fin n → ℕ) (D : ℕ)
    (p : PolynomialRing R n) (hp : Filtered.Bound w D p) :
    MvPolynomial.map (Polynomial.evalRingHom (0 : R)) (weightedHomogenize w D p) =
      weightedHomogeneousComponent w D p := by
  ext a
  rw [coeff_map,weightedHomogenize_coeff,coeff_weightedHomogeneousComponent]
  by_cases ha : p.coeff a=0
  · simp [ha]
  · have hle := hp a ha
    by_cases he : Finsupp.weight w a=D
    · simp [he]
    · have hpos : D-Finsupp.weight w a ≠ 0 := by omega
      simp [he,hpos]

theorem weightedHomogenize_hasHighestPower (r : Fin n → ℕ)
    (p : PolynomialRing R n) (i : Fin n) (e : ℕ) (hp : HasHighestPower r p i e) :
    HasHighestPower r (weightedHomogenize (coveringWeight r) (e*coveringWeight r i) p) i e := by
  constructor
  · rw [weightedHomogenize_coeff,hp.1,Finsupp.weight_single]
    simp only [nsmul_eq_mul,Nat.cast_id,Nat.sub_self,pow_zero,mul_one,map_one]
  · intro a ha hne
    apply hp.2 a _ hne
    apply mem_support_iff.mpr
    intro hz
    apply mem_support_iff.mp ha
    simp only [weightedHomogenize_coeff,hz,map_zero,zero_mul]

def PairedData.power (d : PairedData (K := R) (n := n)) : PairedData (K := R) (n := n) where
  positive_n := d.positive_n
  s := d.s
  positive_s := d.positive_s
  r := d.r
  u := d.u
  v := d.v
  positive_r := d.positive_r
  degree_split := d.degree_split
  beta := d.beta
  allowed_weights := d.allowed_weights
  phi := fun i ↦ X i^d.r i
  a := fun i ↦ X i^d.u i
  b := fun i ↦ X i^d.v i
  highest_phi := fun i ↦ highestPower_X_pow d.r i (d.r i)
  highest_a := fun i ↦ highestPower_X_pow d.r i (d.u i)
  highest_b := fun i ↦ highestPower_X_pow d.r i (d.v i)

def pairedHomogenizedData (d : PairedData (K := R) (n := n)) :
    PairedData (K := Polynomial R) (n := n) where
  positive_n := d.positive_n
  s := d.s
  positive_s := d.positive_s
  r := d.r
  u := d.u
  v := d.v
  positive_r := d.positive_r
  degree_split := d.degree_split
  beta := Polynomial.C ∘ d.beta
  allowed_weights := (d.map Polynomial.C).allowed_weights
  phi := fun i ↦ weightedHomogenize (coveringWeight d.r) (d.r i*coveringWeight d.r i) (d.phi i)
  a := fun i ↦ weightedHomogenize (coveringWeight d.r) (d.u i*coveringWeight d.r i) (d.a i)
  b := fun i ↦ weightedHomogenize (coveringWeight d.r) (d.v i*coveringWeight d.r i) (d.b i)
  highest_phi := fun i ↦ weightedHomogenize_hasHighestPower d.r _ i _ (d.highest_phi i)
  highest_a := fun i ↦ weightedHomogenize_hasHighestPower d.r _ i _ (d.highest_a i)
  highest_b := fun i ↦ weightedHomogenize_hasHighestPower d.r _ i _ (d.highest_b i)

theorem PairedData.eq_of_fields (d e : PairedData (K := R) (n := n))
    (hs : d.s=e.s) (hr : d.r=e.r) (hu : d.u=e.u) (hv : d.v=e.v)
    (hβ : d.beta=e.beta) (hφ : d.phi=e.phi) (ha : d.a=e.a) (hb : d.b=e.b) : d=e := by
  cases d
  cases e
  cases hs
  cases hr
  cases hu
  cases hv
  cases hβ
  cases hφ
  cases ha
  cases hb
  rfl

@[simp] theorem pairedHomogenizedData_at_one (d : PairedData (K := R) (n := n)) :
    (pairedHomogenizedData d).map (Polynomial.evalRingHom (1 : R)) = d := by
  apply PairedData.eq_of_fields ((pairedHomogenizedData d).map (Polynomial.evalRingHom (1 : R))) d rfl rfl rfl rfl
  · funext i
    simp [PairedData.map,pairedHomogenizedData]
  · funext i
    exact weightedHomogenize_at_one _ _ _
  · funext i
    exact weightedHomogenize_at_one _ _ _
  · funext i
    exact weightedHomogenize_at_one _ _ _

@[simp] theorem pairedHomogenizedData_at_zero (d : PairedData (K := R) (n := n)) :
    (pairedHomogenizedData d).map (Polynomial.evalRingHom (0 : R)) = d.power := by
  apply PairedData.eq_of_fields ((pairedHomogenizedData d).map (Polynomial.evalRingHom (0 : R))) d.power rfl rfl rfl rfl
  · funext i
    simp [PairedData.map,pairedHomogenizedData,PairedData.power]
  · funext i
    have ht := HasHighestPower.hasTop d.r d.positive_r _ i _ (d.highest_phi i)
    exact (weightedHomogenize_at_zero _ _ _ ht.1).trans ht.2
  · funext i
    have ht := HasHighestPower.hasTop d.r d.positive_r _ i _ (d.highest_a i)
    exact (weightedHomogenize_at_zero _ _ _ ht.1).trans ht.2
  · funext i
    have ht := HasHighestPower.hasTop d.r d.positive_r _ i _ (d.highest_b i)
    exact (weightedHomogenize_at_zero _ _ _ ht.1).trans ht.2

abbrev PairedHomogenizedQuotient (d : PairedData (K := R) (n := n)) :=
  PairedQuotient (pairedHomogenizedData d).beta (pairedHomogenizedData d).phi
    (pairedHomogenizedData d).a (pairedHomogenizedData d).b

/-- The literal original monomials are a basis over the parameter ring. -/
def pairedHomogenizedBasis (d : PairedData (K := R) (n := n)) :
    Module.Basis (PairedIndex d) (Polynomial R) (PairedHomogenizedQuotient d) :=
  pairedPaperBasis (pairedHomogenizedData d)

theorem pairedHomogenized_finite_free (d : PairedData (K := R) (n := n)) :
    Module.Finite (Polynomial R) (PairedHomogenizedQuotient d) ∧
      Module.Free (Polynomial R) (PairedHomogenizedQuotient d) :=
  ⟨Module.Finite.of_basis (pairedArbitraryRingBasis (pairedHomogenizedData d)),
    Module.Free.of_basis (pairedHomogenizedBasis d)⟩

theorem pairedHomogenized_flat (d : PairedData (K := R) (n := n)) :
    Module.Flat (Polynomial R) (PairedHomogenizedQuotient d) := by
  letI := (pairedHomogenized_finite_free d).2
  infer_instance

/-- The fiber at one is the original coupled algebra, with its actual product. -/
def pairedHomogenized_fiber_one (d : PairedData (K := R) (n := n)) :
    letI : Algebra (Polynomial R) R := (Polynomial.evalRingHom (1 : R)).toAlgebra
    R ⊗[Polynomial R] PairedHomogenizedQuotient d ≃ₐ[R]
      PairedQuotient d.beta d.phi d.a d.b := by
  letI : Algebra (Polynomial R) R := (Polynomial.evalRingHom (1 : R)).toAlgebra
  have h := pairedQuotientBaseChangeAlgEquiv (Polynomial R) R (pairedHomogenizedData d)
  change R ⊗[Polynomial R] PairedHomogenizedQuotient d ≃ₐ[R]
      PairedQuotient ((pairedHomogenizedData d).map (Polynomial.evalRingHom (1 : R))).beta
        ((pairedHomogenizedData d).map (Polynomial.evalRingHom (1 : R))).phi
        ((pairedHomogenizedData d).map (Polynomial.evalRingHom (1 : R))).a
        ((pairedHomogenizedData d).map (Polynomial.evalRingHom (1 : R))).b at h
  exact Eq.mp (congrArg (fun e : PairedData (K := R) (n := n) =>
    R ⊗[Polynomial R] PairedHomogenizedQuotient d ≃ₐ[R]
      PairedQuotient e.beta e.phi e.a e.b) (pairedHomogenizedData_at_one d)) h

/-- Equal actual two-sided ideals give the identity-on-representatives
algebra equivalence of their ring-congruence quotients. -/
def superQuotientCongr {I J : TwoSidedIdeal (SuperRing R n)} (h : I = J) :
    I.ringCon.Quotient ≃ₐ[R] J.ringCon.Quotient :=
  RingCon.congrₐ R (AlgEquiv.refl : SuperRing R n ≃ₐ[R] SuperRing R n) (by cases h; rfl)

@[simp] theorem superQuotientCongr_mk
    {I J : TwoSidedIdeal (SuperRing R n)} (h : I = J) (x : SuperRing R n) :
    superQuotientCongr h (x : I.ringCon.Quotient) = (x : J.ringCon.Quotient) := rfl

/-- The fiber at zero is precisely the homogeneous power algebra. -/
def pairedHomogenized_fiber_zero (d : PairedData (K := R) (n := n)) :
    letI : Algebra (Polynomial R) R := (Polynomial.evalRingHom (0 : R)).toAlgebra
    R ⊗[Polynomial R] PairedHomogenizedQuotient d ≃ₐ[R]
      PairedQuotient d.beta (fun i ↦ X i^d.r i) (fun i ↦ X i^d.u i) (fun i ↦ X i^d.v i) := by
  letI : Algebra (Polynomial R) R := (Polynomial.evalRingHom (0 : R)).toAlgebra
  have h := pairedQuotientBaseChangeAlgEquiv (Polynomial R) R (pairedHomogenizedData d)
  change R ⊗[Polynomial R] PairedHomogenizedQuotient d ≃ₐ[R]
      PairedQuotient ((pairedHomogenizedData d).map (Polynomial.evalRingHom (0 : R))).beta
        ((pairedHomogenizedData d).map (Polynomial.evalRingHom (0 : R))).phi
        ((pairedHomogenizedData d).map (Polynomial.evalRingHom (0 : R))).a
        ((pairedHomogenizedData d).map (Polynomial.evalRingHom (0 : R))).b at h
  have hI : pairedIdeal
      ((pairedHomogenizedData d).map (Polynomial.evalRingHom (0 : R))).beta
      ((pairedHomogenizedData d).map (Polynomial.evalRingHom (0 : R))).phi
      ((pairedHomogenizedData d).map (Polynomial.evalRingHom (0 : R))).a
      ((pairedHomogenizedData d).map (Polynomial.evalRingHom (0 : R))).b =
      pairedIdeal d.beta (fun i ↦ X i^d.r i) (fun i ↦ X i^d.u i) (fun i ↦ X i^d.v i) :=
      by
    have hβ : ((pairedHomogenizedData d).map (Polynomial.evalRingHom (0 : R))).beta=
        d.beta := by
      funext i
      change Polynomial.evalRingHom (0 : R) (Polynomial.C (d.beta i))=d.beta i
      simp only [Polynomial.coe_evalRingHom,Polynomial.eval_C]
    have hφ : ((pairedHomogenizedData d).map (Polynomial.evalRingHom (0 : R))).phi=
        fun i ↦ (X i^d.r i : PolynomialRing R n) := by
      funext i
      have ht := HasHighestPower.hasTop d.r d.positive_r _ i _ (d.highest_phi i)
      exact (weightedHomogenize_at_zero _ _ _ ht.1).trans ht.2
    have ha : ((pairedHomogenizedData d).map (Polynomial.evalRingHom (0 : R))).a=
        fun i ↦ (X i^d.u i : PolynomialRing R n) := by
      funext i
      have ht := HasHighestPower.hasTop d.r d.positive_r _ i _ (d.highest_a i)
      exact (weightedHomogenize_at_zero _ _ _ ht.1).trans ht.2
    have hb : ((pairedHomogenizedData d).map (Polynomial.evalRingHom (0 : R))).b=
        fun i ↦ (X i^d.v i : PolynomialRing R n) := by
      funext i
      have ht := HasHighestPower.hasTop d.r d.positive_r _ i _ (d.highest_b i)
      exact (weightedHomogenize_at_zero _ _ _ ht.1).trans ht.2
    rw [hβ,hφ,ha,hb]
  exact h.trans (superQuotientCongr hI)

end PaperVerification.Fermion
