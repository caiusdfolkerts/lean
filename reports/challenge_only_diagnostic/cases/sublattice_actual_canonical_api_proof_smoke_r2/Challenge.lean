module
public import Mathlib.Data.Set.PowersetCard
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Tactic

/- Canonical proof/API smoke for the actual first Solution errors of run44371585714.
Every proposition has an actual proof. No custom project imports or admitted facts.
This is a diagnostic, not a theorem submission or a full Solution check. -/
@[expose] public noncomputable section
open Classical MvPolynomial
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.weightedGradedAlgebra
namespace PalomarSublatticeApiSmoke
universe u v
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

/-- The exact integer-weight/support-sum identity used by the ordinary bridge. -/
theorem integerWeight_degree (a : V →₀ ℕ) :
    Finsupp.weight (fun _ : V => (1 : ℤ)) a = (a.degree : ℤ) := by
  simp [Finsupp.weight_eq_sum, Finsupp.degree, Finsupp.sum]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro j _ hj
  simp only [Finsupp.notMem_support_iff.mp hj, Nat.cast_zero]

abbrev Coordinates (I : Ideal (MvPolynomial V k)) (p : ℕ) := Set.powersetCard V p →₀ I

def coefficientAt (I : Ideal (MvPolynomial V k)) (p : ℕ)
    (s : Set.powersetCard V p) : Coordinates I p →ₗ[k] MvPolynomial V k :=
  (I.subtype.restrictScalars k).comp (Finsupp.lapply s)

def piece (I : Ideal (MvPolynomial V k)) (q : ℤ) (p : ℕ) :
    Submodule k (Coordinates I p) :=
  ⨅ s : Set.powersetCard V p,
    (weightedHomogeneousSubmodule k (fun _ : V => (1 : ℤ)) (q - (p : ℤ))).comap
      (coefficientAt I p s)

theorem mem_piece_iff (I : Ideal (MvPolynomial V k)) (q : ℤ) (p : ℕ)
    (x : Coordinates I p) :
    x ∈ piece I q p ↔ ∀ s : Set.powersetCard V p, ∀ a : V →₀ ℕ,
      (x s).val.coeff a ≠ 0 → (a.degree : ℤ) + (p : ℤ) = q := by
  simp only [piece, Submodule.mem_iInf, Submodule.mem_comap,
    MvPolynomial.mem_weightedHomogeneousSubmodule]
  change (∀ s : Set.powersetCard V p,
    (x s).val.IsWeightedHomogeneous (fun _ : V => (1 : ℤ)) (q - (p : ℤ))) ↔ _
  simp only [MvPolynomial.IsWeightedHomogeneous, integerWeight_degree]
  constructor
  · intro h s a ha
    have hh := h s ha
    omega
  · intro h s a ha
    have hh := h s a ha
    omega

/-- This is the actual negative-piece proof, with extensionality stopped at
one Finsupp coordinate, one ideal subtype, then one polynomial coefficient. -/
theorem piece_negative (I : Ideal (MvPolynomial V k)) {q : ℤ}
    (hq : q < 0) (p : ℕ) : piece I q p = ⊥ := by
  apply le_antisymm
  · intro x hx
    have he : x = 0 := by
      apply Finsupp.ext
      intro s
      apply Subtype.ext
      apply MvPolynomial.ext
      intro a
      change (x s).val.coeff a = 0
      by_contra hn
      have hd := (mem_piece_iff I q p x).mp hx s a hn
      have ha : (0 : ℤ) ≤ (a.degree : ℤ) := Int.natCast_nonneg _
      have hp : (0 : ℤ) ≤ (p : ℤ) := Int.natCast_nonneg _
      omega
    simp [he]
  · exact bot_le

/-- The exact missing simplification at the restricted monomial basis. -/
theorem subtype_single_apply {A : Type*} {S : Set A} (b c : S) :
    (Finsupp.single c (1 : k)) b = if c.val = b.val then 1 else 0 := by
  simp only [Finsupp.single_apply, Subtype.ext_iff]

section CoefficientMaps
variable {A M N : Type*} [AddCommGroup M] [Module k M]
  [AddCommGroup N] [Module k N] (e : M ≃ₗ[k] N)

def chainsEquiv : (A →₀ M) ≃ₗ[k] (A →₀ N) := Finsupp.mapRange.linearEquiv e

theorem chains_single (s : A) (x : M) :
    chainsEquiv e (Finsupp.single s x) = Finsupp.single s (e x) := by
  change Finsupp.mapRange e (map_zero _) (Finsupp.single s x) = _
  exact Finsupp.mapRange_single

/-- Finsupp.lhom_ext already introduces both the exterior index and coefficient. -/
theorem chain_linear_ext (f g : (A →₀ M) →ₗ[k] N)
    (h : ∀ s x, f (Finsupp.single s x) = g (Finsupp.single s x)) : f = g := by
  apply Finsupp.lhom_ext
  intro s x
  exact h s x

/-- Actual coefficient values in the target Finsupp basis after coordinatewise
transport; this is the generic form of the fine quotient repr bridge. -/
theorem chains_repr {B : Type*} (b : Module.Basis B k N) (x : A →₀ M) (t : A × B) :
    (Finsupp.basis (fun _ : A => b)).repr (chainsEquiv e x) ⟨t.1,t.2⟩ =
      b.repr (e (x t.1)) t.2 := by
  rw [Finsupp.basis_repr]
  rfl
end CoefficientMaps

section FineQuotients
variable (I J : Ideal (MvPolynomial V k)) (h : I = J)

def quotientEquiv : (MvPolynomial V k ⧸ I) ≃ₐ[k] (MvPolynomial V k ⧸ J) :=
  Ideal.quotientEquivAlgOfEq k h

def variableDegree (j : V) : V →₀ ℤ := Finsupp.single j 1

def polynomialPiece (a : V →₀ ℤ) : Submodule k (MvPolynomial V k) :=
  weightedHomogeneousSubmodule k variableDegree a

def quotientPiece (I : Ideal (MvPolynomial V k)) (a : V →₀ ℤ) :
    Submodule k (MvPolynomial V k ⧸ I) :=
  (polynomialPiece a).map (Ideal.Quotient.mkₐ k I).toLinearMap

/-- Exact map-composition API for actual signed homogeneous coefficient images. -/
theorem quotientPiece_map (a : V →₀ ℤ) :
    (quotientPiece I a).map (quotientEquiv I J h).toLinearMap = quotientPiece J a := by
  change ((polynomialPiece a).map (Ideal.Quotient.mkₐ k I).toLinearMap).map
    (quotientEquiv I J h).toLinearMap =
      (polynomialPiece a).map (Ideal.Quotient.mkₐ k J).toLinearMap
  rw [← Submodule.map_comp]
  congr 1

/-- The same actual scalar action used in the Koszul differential is preserved. -/
theorem quotientEquiv_smul (f : MvPolynomial V k) (x : MvPolynomial V k ⧸ I) :
    quotientEquiv I J h (f • x) = f • quotientEquiv I J h x := by
  change quotientEquiv I J h (Ideal.Quotient.mk _ f * x) =
    Ideal.Quotient.mk _ f * quotientEquiv I J h x
  simp only [map_mul, quotientEquiv, Ideal.quotientEquivAlgOfEq_mk]

/-- Explicit iInf-family argument, as required by the pinned API. -/
theorem component_mem (C : ℕ → Submodule k (MvPolynomial V k))
    (x : MvPolynomial V k) (hx : x ∈ ⨅ i, C i) (i : ℕ) : x ∈ C i :=
  (Submodule.mem_iInf _).mp hx i
end FineQuotients

open CategoryTheory
/-- In exterior degree zero the chain differential to degree zero is genuinely
zero; the pinned of_d_ne lemma handles the forbidden complex-shape arrow. -/
theorem chain_zero_differential (X : ℕ → ModuleCat k)
    (d : ∀ i, X (i+1) ⟶ X i) (sq : ∀ i, d (i+1) ≫ d i = 0) :
    (ChainComplex.of X d sq).d 0 0 = 0 := by
  change ChainComplex.of.d X d 0 0 = 0
  exact ChainComplex.of_d_ne X d (by decide)
end PalomarSublatticeApiSmoke
