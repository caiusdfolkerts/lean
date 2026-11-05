module

public import PaperVerification.PowerSpanning
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Data.Fintype.BigOperators

/-!
# The finite Artin space and its actual quotient map

The indices are exactly the bounded exponent vectors in the paper. Their
cardinality is proved by an equivalence with a product of finite intervals.
The finite-dimensional quotient is obtained from the established spanning
theorem, without assuming any linear independence or dimension formula.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial Module
open scoped BigOperators

namespace PaperVerification.PowerOperators

def ArtinIndex (n m : ℕ) := {a : Fin n →₀ ℕ // IsArtinExponent m a}

/-- All bounds, including the zero-variable case, are retained exactly. -/
def artinIndexEquiv (n m : ℕ) :
    ArtinIndex n m ≃ (∀ i : Fin n, Fin (m+i.val)) where
  toFun a i := ⟨a.val i, a.property i⟩
  invFun a := ⟨Finsupp.equivFunOnFinite.symm (fun i => (a i).val),
    fun i => (a i).isLt⟩
  left_inv a := by
    apply Subtype.ext
    ext i
    rfl
  right_inv a := by
    funext i
    apply Fin.ext
    rfl

instance artinIndex_fintype (n m : ℕ) : Fintype (ArtinIndex n m) :=
  Fintype.ofEquiv (∀ i : Fin n, Fin (m+i.val)) (artinIndexEquiv n m).symm

theorem card_artinIndex (n m : ℕ) :
    Fintype.card (ArtinIndex n m) = ∏ i : Fin n, (m+i.val) := by
  rw [Fintype.card_congr (artinIndexEquiv n m), Fintype.card_pi]
  simp only [Fintype.card_fin]

variable {K : Type*} [Field K] {n : ℕ}

theorem artinSpan_eq_span_range (m : ℕ) :
    artinSpan K n m = Submodule.span K
      (Set.range fun a : ArtinIndex n m => monomial a.val (1 : K)) := by
  unfold artinSpan
  congr 1
  ext p
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a.val, a.property, rfl⟩

theorem artinMonomials_linearIndependent (m : ℕ) :
    LinearIndependent K (fun a : ArtinIndex n m => monomial a.val (1 : K)) :=
  (basisMonomials (Fin n) K).linearIndependent.comp
    (fun a : ArtinIndex n m => a.val) Subtype.val_injective

def artinBasis (K : Type*) [Field K] (n m : ℕ) :
    Basis (ArtinIndex n m) K (artinSpan K n m) :=
  (Basis.span (artinMonomials_linearIndependent (K := K) (n := n) m)).map
    (LinearEquiv.ofEq _ _ (artinSpan_eq_span_range (K := K) (n := n) m).symm)

@[simp] theorem artinBasis_apply (m : ℕ) (a : ArtinIndex n m) :
    (artinBasis K n m a : MvPolynomial (Fin n) K) = monomial a.val 1 := by
  simp only [artinBasis, Basis.map_apply, LinearEquiv.coe_ofEq_apply,
    Basis.coe_span_apply]

instance artinSpan_finite (m : ℕ) : Module.Finite K (artinSpan K n m) :=
  Module.Finite.of_basis (artinBasis K n m)

theorem artinSpan_finrank (m : ℕ) :
    Module.finrank K (artinSpan K n m) = ∏ i : Fin n, (m+i.val) := by
  rw [Module.finrank_eq_card_basis (artinBasis K n m), card_artinIndex]

def artinDegreeBound (n m : ℕ) : ℕ := ∑ i : Fin n, (m+i.val-1)

theorem artinIndex_degree_le (m : ℕ) (a : ArtinIndex n m) :
    a.val.degree ≤ artinDegreeBound n m := by
  rw [Finsupp.degree_eq_sum]
  apply Finset.sum_le_sum
  intro i _
  have hi := a.property i
  omega

/-- This map sends an Artin polynomial to its class in the actual joint-image
quotient. It is not a map to an auxiliary quotient with prescribed basis. -/
def artinQuotientMap (c : Fin n → K) (lam : K) (m : ℕ) :
    artinSpan K n m →ₗ[K] (MvPolynomial (Fin n) K ⧸ tailHit c lam m) :=
  (tailHit c lam m).mkQ.comp (artinSpan K n m).subtype

theorem artinQuotientMap_surjective
    (c : Fin n → K) (lam : K) (m : ℕ) (hm : 0 < m)
    (hnr : Nonresonant c lam m) :
    Function.Surjective (artinQuotientMap c lam m) := by
  intro q
  have hq : q ∈ (artinSpan K n m).map (tailHit c lam m).mkQ := by
    rw [artinSpan_quotient_eq_top c lam m hm hnr]
    trivial
  obtain ⟨p, hp, he⟩ := hq
  exact ⟨⟨p, hp⟩, he⟩

theorem tailQuotient_finite
    (c : Fin n → K) (lam : K) (m : ℕ) (hm : 0 < m)
    (hnr : Nonresonant c lam m) :
    Module.Finite K (MvPolynomial (Fin n) K ⧸ tailHit c lam m) :=
  Module.Finite.of_surjective (artinQuotientMap c lam m)
    (artinQuotientMap_surjective c lam m hm hnr)

theorem tailQuotient_finrank_le
    (c : Fin n → K) (lam : K) (m : ℕ) (hm : 0 < m)
    (hnr : Nonresonant c lam m) :
    Module.finrank K (MvPolynomial (Fin n) K ⧸ tailHit c lam m) ≤
      ∏ i : Fin n, (m+i.val) := by
  rw [← artinSpan_finrank (K := K) (n := n) m]
  exact LinearMap.finrank_le_finrank_of_surjective
    (artinQuotientMap_surjective c lam m hm hnr)

/-- A general extraction step. The lower bound is discharged separately by
the degreewise specialization argument; it is not a principal theorem's
hypothesis. -/
def artinQuotientEquivOfLowerBound
    (c : Fin n → K) (lam : K) (m : ℕ) (hm : 0 < m)
    (hnr : Nonresonant c lam m)
    (hlower : (∏ i : Fin n, (m+i.val)) ≤
      Module.finrank K (MvPolynomial (Fin n) K ⧸ tailHit c lam m)) :
    artinSpan K n m ≃ₗ[K] (MvPolynomial (Fin n) K ⧸ tailHit c lam m) := by
  letI := tailQuotient_finite c lam m hm hnr
  exact LinearEquiv.ofBijective (artinQuotientMap c lam m)
    (OrzechProperty.bijective_of_surjective_of_finrank_le
      (artinQuotientMap c lam m) (artinQuotientMap_surjective c lam m hm hnr)
      (by rwa [artinSpan_finrank]))

def artinQuotientBasisOfLowerBound
    (c : Fin n → K) (lam : K) (m : ℕ) (hm : 0 < m)
    (hnr : Nonresonant c lam m)
    (hlower : (∏ i : Fin n, (m+i.val)) ≤
      Module.finrank K (MvPolynomial (Fin n) K ⧸ tailHit c lam m)) :
    Basis (ArtinIndex n m) K (MvPolynomial (Fin n) K ⧸ tailHit c lam m) :=
  (artinBasis K n m).map (artinQuotientEquivOfLowerBound c lam m hm hnr hlower)

@[simp] theorem artinQuotientBasisOfLowerBound_apply
    (c : Fin n → K) (lam : K) (m : ℕ) (hm : 0 < m)
    (hnr : Nonresonant c lam m)
    (hlower : (∏ i : Fin n, (m+i.val)) ≤
      Module.finrank K (MvPolynomial (Fin n) K ⧸ tailHit c lam m))
    (a : ArtinIndex n m) :
    artinQuotientBasisOfLowerBound c lam m hm hnr hlower a =
      (tailHit c lam m).mkQ (monomial a.val 1) := by
  change (tailHit c lam m).mkQ (artinBasis K n m a) = _
  rw [artinBasis_apply]

end PaperVerification.PowerOperators
