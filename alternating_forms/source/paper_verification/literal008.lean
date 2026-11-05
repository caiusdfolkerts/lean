module

public import Mathlib.Data.Finset.Sort
public import paper_verification.literal007
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.LinearAlgebra.Basis.Fin
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.Order.Sum.Order
public import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.PowerSeries.WellKnown
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.SetTheory.Cardinal.NatCard
import Lean.Elab.Tactic.Omega
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Isomorphisms
public import paper_verification.literal003
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Logic.Equiv.Option
public import paper_verification.literal004
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.LinearAlgebra.Finsupp.SumProd
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Module.Opposite
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs

set_option Elab.async false

section TAF_LiteralSource_0464
/- Original module: TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Basis -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The ordered Poincaré--Birkhoff--Witt basis

For any ordered basis `b` of a Lie algebra over a commutative ring, the products of its canonical
generators in increasing order form a basis of the enveloping algebra. The indices are finitely
supported natural exponents. The value at an exponent is the corresponding ordered product,
with coefficient `1`, including the empty product `1`.

The evaluation of the polynomial representation gives a linear equivalence with multivariate
polynomials carrying these basis vectors to the usual monomials. This is an equivalence of
modules; the enveloping algebra need not be commutative.

## Main results

* `Module.Basis.pbwBasis`: the ordered monomial basis of the enveloping algebra.
* `Module.Basis.pbwBasis_eq_prod_pow`: its value as the increasing product of generator powers.
* `Module.Basis.mem_pbwFiltration_iff_pbwBasis_repr`: the basis is adapted to the PBW filtration,
  which in degree `k` is spanned by the basis vectors of total degree at most `k`.
* `Module.Basis.pbwEquiv`: the linear equivalence with multivariate polynomials.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Chapter V, §17.4.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter I, §2.7.
-/

public section

namespace Module.Basis

open MvPolynomial TauCeti.UniversalEnvelopingAlgebra

universe u v w

variable {R : Type u} {L : Type v} {ι : Type w}
  [CommRing R] [LieRing L] [LieAlgebra R L] [LinearOrder ι] (b : Basis ι R L)

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

/-- The ordered monomial with exponent vector `n`: repeat each generator `n i` times and
multiply the resulting word in increasing order. -/
private noncomputable def pbwBasisMonomial (n : ι →₀ ℕ) : U :=
  pbwMonomial R L b (n.toMultiset.sort (· ≤ ·))

/-- The ordered-word formula for a PBW basis monomial. -/
private theorem pbwBasisMonomial_def (n : ι →₀ ℕ) :
    b.pbwBasisMonomial n = pbwMonomial R L b (n.toMultiset.sort (· ≤ ·)) :=
  (rfl)

@[simp]
private theorem pbwBasisMonomial_zero : b.pbwBasisMonomial 0 = 1 := by
  simp [pbwBasisMonomial, Finsupp.toMultiset_zero]

/-- Ordered words are precisely the monomials indexed by their multiplicities. -/
private theorem pbwBasisMonomial_toFinsupp {word : List ι} (hword : word.Pairwise (· ≤ ·)) :
    b.pbwBasisMonomial (Multiset.toFinsupp (word : Multiset ι)) = pbwMonomial R L b word := by
  rw [pbwBasisMonomial_def, Multiset.toFinsupp_toMultiset, Multiset.coe_sort,
    List.mergeSort_eq_self (· ≤ ·) hword]

@[simp]
private theorem pbwEval_pbwBasisMonomial (n : ι →₀ ℕ) :
    b.pbwEval (b.pbwBasisMonomial n) = monomial n 1 := by
  rw [pbwBasisMonomial_def, pbwEval_pbwMonomial b (Multiset.pairwise_sort _ _),
    Multiset.sort_eq, Finsupp.toMultiset_toFinsupp]

/-- The ordered monomials in a basis are linearly independent. -/
private theorem linearIndependent_pbwBasisMonomial : LinearIndependent R b.pbwBasisMonomial := by
  apply LinearIndependent.of_comp b.pbwEval
  simpa [Function.comp_def] using (basisMonomials ι R).linearIndependent

/-- The ordered monomials in a basis span the enveloping algebra. -/
private theorem span_range_pbwBasisMonomial :
    Submodule.span R (Set.range b.pbwBasisMonomial) = ⊤ := by
  apply top_unique
  rw [← span_iUnion_orderedPBWMonomials_eq_top R L b b.span_eq]
  apply Submodule.span_mono
  intro a ha
  obtain ⟨k, hk⟩ := Set.mem_iUnion.1 ha
  obtain ⟨word, hword, _, rfl⟩ := (mem_orderedPBWMonomials_iff R L b).1 hk
  exact ⟨Multiset.toFinsupp (word : Multiset ι), b.pbwBasisMonomial_toFinsupp hword⟩

/-- The Poincaré--Birkhoff--Witt basis: ordered monomials in a chosen basis of the Lie algebra,
over an arbitrary commutative ring. -/
noncomputable def pbwBasis : Basis (ι →₀ ℕ) R U :=
  Basis.mk b.linearIndependent_pbwBasisMonomial b.span_range_pbwBasisMonomial.ge

private theorem pbwBasis_apply_aux (n : ι →₀ ℕ) : b.pbwBasis n = b.pbwBasisMonomial n :=
  Basis.mk_apply _ _ n

/-- The basis vector at `n` is the word containing `n i` copies of each generator, sorted in
increasing order. -/
theorem pbwBasis_apply (n : ι →₀ ℕ) :
    b.pbwBasis n = pbwMonomial R L b (n.toMultiset.sort (· ≤ ·)) := by
  rw [pbwBasis_apply_aux, pbwBasisMonomial_def]

@[simp]
theorem pbwBasis_zero : b.pbwBasis 0 = 1 := by
  rw [pbwBasis_apply_aux, pbwBasisMonomial_zero]

/-- The ordered PBW monomials of word length at most `k` are exactly the PBW basis vectors whose
exponent vectors have total degree at most `k`. -/
theorem orderedPBWMonomials_eq_image_pbwBasis (k : ℕ) :
    orderedPBWMonomials R L b k = b.pbwBasis '' {n | n.degree ≤ k} := by
  ext a
  rw [mem_orderedPBWMonomials_iff]
  constructor
  · rintro ⟨word, hword, hk, rfl⟩
    refine ⟨Multiset.toFinsupp (word : Multiset ι), ?_, ?_⟩
    · rw [Set.mem_ofPred_eq, ← Finsupp.card_toMultiset_eq_degree,
        Multiset.toFinsupp_toMultiset]
      exact hk
    · rw [pbwBasis_apply_aux, b.pbwBasisMonomial_toFinsupp hword]
  · rintro ⟨n, hn, rfl⟩
    refine ⟨_, Multiset.pairwise_sort _ _, ?_, (b.pbwBasis_apply n).symm⟩
    rwa [Multiset.length_sort, Finsupp.card_toMultiset_eq_degree]

/-- **The PBW basis is adapted to the PBW filtration.** Filtration degree `k` is spanned by the PBW
basis vectors of total degree at most `k`. -/
theorem span_image_pbwBasis_eq_pbwFiltration (k : ℕ) :
    Submodule.span R (b.pbwBasis '' {n | n.degree ≤ k}) = pbwFiltration R L k := by
  rw [← orderedPBWMonomials_eq_image_pbwBasis b, span_orderedPBWMonomials_eq_pbwFiltration R L (⇑b)
    b.span_eq]

/-- An element has PBW filtration degree at most `k` exactly when its PBW coordinates are
supported on exponent vectors of total degree at most `k`. -/
theorem mem_pbwFiltration_iff_pbwBasis_repr {k : ℕ} {a : U} :
    a ∈ pbwFiltration R L k ↔ ∀ n ∈ (b.pbwBasis.repr a).support, n.degree ≤ k := by
  rw [← span_image_pbwBasis_eq_pbwFiltration b, Basis.mem_span_image]
  simp [Set.subset_def]

/-- PBW evaluation sends each ordered basis vector to the corresponding polynomial monomial. -/
@[simp]
theorem pbwEval_pbwBasis (n : ι →₀ ℕ) : b.pbwEval (b.pbwBasis n) = monomial n 1 := by
  rw [pbwBasis_apply_aux, pbwEval_pbwBasisMonomial]

/-- The PBW evaluation is bijective: it carries the ordered basis to the polynomial basis. -/
theorem pbwEval_bijective : Function.Bijective b.pbwEval := by
  have h : b.pbwEval = b.pbwBasis.equiv (basisMonomials ι R) (Equiv.refl _) := by
    apply b.pbwBasis.ext
    intro n
    calc
      b.pbwEval (b.pbwBasis n) = basisMonomials ι R n := by simp
      _ = _ := (Basis.equiv_apply b.pbwBasis n (basisMonomials ι R) (Equiv.refl _)).symm
  rw [h]
  exact (b.pbwBasis.equiv (basisMonomials ι R) (Equiv.refl _)).bijective

/-- The linear PBW equivalence with polynomials, normalized by the ordered monomial basis. -/
noncomputable def pbwEquiv : U ≃ₗ[R] MvPolynomial ι R :=
  LinearEquiv.ofBijective b.pbwEval b.pbwEval_bijective

@[simp]
theorem pbwEquiv_apply (a : U) : b.pbwEquiv a = b.pbwEval a :=
  (rfl)

@[simp]
theorem pbwEquiv_symm_monomial (n : ι →₀ ℕ) :
    b.pbwEquiv.symm (monomial n 1) = b.pbwBasis n := by
  apply b.pbwEquiv.injective
  simp

/-- The basis vector at `n` is the product of `ι(b i) ^ n i`, with the support traversed in
increasing order. No commutativity of the enveloping algebra is assumed. -/
theorem pbwBasis_eq_prod_pow (n : ι →₀ ℕ) :
    b.pbwBasis n = ((n.support.sort (· ≤ ·)).map
      (fun i ↦ _root_.UniversalEnvelopingAlgebra.ι R (b i) ^ n i)).prod := by
  let indices := n.support.sort (· ≤ ·)
  let word := indices.flatMap fun i ↦ List.replicate (n i) i
  have hword : word.Pairwise (· ≤ ·) := by
    apply List.pairwise_flatMap.2
    refine ⟨fun i _ ↦ List.pairwise_replicate.2 (Or.inr le_rfl), ?_⟩
    exact (Finset.pairwise_sort _ _).imp fun {i j} hij x hx y hy ↦ by
      simpa [List.eq_of_mem_replicate hx, List.eq_of_mem_replicate hy] using hij
  have hmult : Multiset.toFinsupp (word : Multiset ι) = n := by
    have haux (l : List ι) :
        Multiset.toFinsupp ((l.flatMap fun i ↦ List.replicate (n i) i) : Multiset ι) =
          (l.map fun i ↦ Finsupp.single i (n i)).sum := by
      induction l with
      | nil => simp [Multiset.toFinsupp_zero]
      | cons i l ih =>
          simp only [List.flatMap_cons, ← Multiset.coe_add, Multiset.toFinsupp_add,
            List.map_cons, List.sum_cons, ih]
          congr 1
          ext j
          by_cases hij : i = j
          · subst j
            simp
          · simp [Multiset.toFinsupp_apply, List.count_replicate, hij]
    rw [haux]
    rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.sort_eq]
    exact Finsupp.sum_single n
  have hprod : pbwMonomial R L b word = ((indices.map
      (fun i ↦ _root_.UniversalEnvelopingAlgebra.ι R (b i) ^ n i))).prod := by
    rw [pbwMonomial_def, List.map_map, List.map_flatMap]
    induction indices with
    | nil => simp
    | cons i indices ih =>
        rw [List.flatMap_cons, List.prod_append, ih]
        simp only [List.map_cons, List.prod_cons, List.map_replicate, List.prod_replicate,
          Function.comp_apply]
  rw [← hprod, ← b.pbwBasisMonomial_toFinsupp hword, hmult, pbwBasis_apply_aux]

@[simp]
theorem pbwBasis_single (i : ι) (k : ℕ) :
    b.pbwBasis (Finsupp.single i k) = _root_.UniversalEnvelopingAlgebra.ι R (b i) ^ k := by
  by_cases hk : k = 0
  · subst k
    simp
  · rw [pbwBasis_eq_prod_pow]
    simp [Finsupp.support_single _ hk]

end Module.Basis

namespace Module.Basis

open TauCeti.UniversalEnvelopingAlgebra

variable {R L M ι κ : Type*} [CommRing R]
  [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]
  [LinearOrder ι] [LinearOrder κ]

/-- A Lie map taking an ordered basis into another ordered basis carries each PBW monomial to
the ambient monomial with its exponents extended by zero outside the embedded indices. -/
theorem map_pbwBasis (b : Basis ι R L) (c : Basis κ R M)
    (f : L →ₗ⁅R⁆ M) (e : ι ↪o κ) (h : ∀ i, f (b i) = c (e i)) (n : ι →₀ ℕ) :
    map R f (b.pbwBasis n) = c.pbwBasis (n.embDomain e.toEmbedding) := by
  have hsort : (n.toMultiset.sort (· ≤ ·)).map e =
      (n.embDomain e.toEmbedding).toMultiset.sort (· ≤ ·) := by
    rw [Finsupp.embDomain_eq_mapDomain, ← Finsupp.toMultiset_map]
    exact Multiset.map_sort e n.toMultiset (· ≤ ·) (· ≤ ·)
      (fun _ _ _ _ ↦ e.le_iff_le.symm)
  rw [pbwBasis_apply, map_pbwMonomial, pbwBasis_apply, ← hsort]
  simp only [pbwMonomial_def, List.map_map, Function.comp_def, h]

end Module.Basis
end
end TAF_LiteralSource_0464

section TAF_LiteralSource_0465
/- Original module: PaperVerification.TwoStepPBWGrading -/


/-!
# The actual generator grading and the weighted PBW basis

For a central two-step Lie algebra whose central space is generated by
brackets, the degree `d` piece is defined as the span of length-`d`
products of the original degree-one generators.  It is proved equal to
the span of PBW monomials with generator weights one and central weights
two.  In particular, the PBW filtration is not substituted for the grading
used by the paper.

The reverse inclusion uses the genuine Lie endomorphism `(v,z) ↦ (2v,4z)`.
Its induced enveloping-algebra endomorphism acts on the two descriptions
with the same eigenvalue, and distinct natural powers of two separate all
degrees in characteristic zero.

This file is a proof candidate until checked with the full PBW closure.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.TwoStepPBWGrading

open TwoStepCentralLie QuadraticCommutatorQuotient
open TauCeti.UniversalEnvelopingAlgebra
attribute [local instance 100] LieRing.ofAssociativeRing

variable {K ν : Type*} [Field K] [CharZero K] [Fintype ν] [LinearOrder ν]
  (D : Data (K := K) (V := ν → K) (Z := K × K))

local instance : LinearOrder (ν ⊕ Fin 2) := Sum.Lex.linearOrder

local notation "U" => UniversalEnvelopingAlgebra K (LieSpace D)

/-- Images of the original degree-one generators in the actual enveloping algebra. -/
def generatorMap : (ν → K) →ₗ[K] U :=
  (UniversalEnvelopingAlgebra.ι K (L := LieSpace D)).toLinearMap.comp (generator D)

@[simp] theorem generatorMap_apply (v : ν → K) :
    generatorMap D v=UniversalEnvelopingAlgebra.ι K (generator D v) := rfl

def generatorSpace : Submodule K U := LinearMap.range (generatorMap D)

/-- The ordinary generator grading, defined by products before PBW is used. -/
def wordPiece (d : ℕ) : Submodule K U := generatorSpace D ^ d

theorem generator_mem_wordPiece (v : ν → K) :
    generatorMap D v∈wordPiece D 1 := by
  rw [wordPiece,pow_one]
  exact LinearMap.mem_range_self _ v

theorem mul_mem_wordPiece {i j : ℕ} {x y : U}
    (hx : x∈wordPiece D i) (hy : y∈wordPiece D j) :
    x*y∈wordPiece D (i+j) := by
  rw [wordPiece,pow_add]
  exact Submodule.mul_mem_mul hx hy

/-- This map preserves the actual two-step bracket, including its quadratic central weight. -/
def scaleLie (t : K) : LieSpace D →ₗ⁅K⁆ LieSpace D where
  toLinearMap :=
    { toFun x := (t • x.1,t^2 • x.2)
      map_add' x y := by
        apply (coordinates D).injective
        change (t • (x.1+y.1),t^2 • (x.2+y.2))=
          (t • x.1+t • y.1,t^2 • x.2+t^2 • y.2)
        simp only [smul_add]
      map_smul' c x := by
        apply (coordinates D).injective
        change (t • (c • x.1),t^2 • (c • x.2))=
          (c • (t • x.1),c • (t^2 • x.2))
        simp only [smul_smul,mul_comm] }
  map_lie' {x y} := by
    apply (coordinates D).injective
    change (t • (0 : ν → K),t^2 • D.bilinear x.1 y.1)=
      (0,D.bilinear (t • x.1) (t • y.1))
    simp [map_smul,LinearMap.smul_apply,smul_smul,pow_two]

@[simp] theorem scaleLie_generator (t : K) (v : ν → K) :
    scaleLie D t (generator D v)=t • generator D v := by
  apply (coordinates D).injective
  change (t • v,t^2 • (0 : K × K))=(t • v,t • (0 : K × K))
  simp only [smul_zero]

@[simp] theorem scaleLie_central (t : K) (z : K × K) :
    scaleLie D t (central D z)=t^2 • central D z := by
  apply (coordinates D).injective
  change (t • (0 : ν → K),t^2 • z)=(t^2 • (0 : ν → K),t^2 • z)
  simp only [smul_zero]

def scaleAlgebra (t : K) : U →ₐ[K] U :=
  TauCeti.UniversalEnvelopingAlgebra.map K (scaleLie D t)

@[simp] theorem scaleAlgebra_generator (t : K) (v : ν → K) :
    scaleAlgebra D t (generatorMap D v)=t • generatorMap D v := by
  change TauCeti.UniversalEnvelopingAlgebra.map K (scaleLie D t)
    (UniversalEnvelopingAlgebra.ι K (generator D v))=_
  rw [TauCeti.UniversalEnvelopingAlgebra.map_ι]
  rw [scaleLie_generator,map_smul]
  rfl

@[simp] theorem scaleAlgebra_central (t : K) (z : K × K) :
    scaleAlgebra D t (UniversalEnvelopingAlgebra.ι K (central D z))=
      t^2 • UniversalEnvelopingAlgebra.ι K (central D z) := by
  rw [scaleAlgebra,TauCeti.UniversalEnvelopingAlgebra.map_ι]
  rw [scaleLie_central,map_smul]

theorem wordPiece_eigenvector (t : K) (d : ℕ) (x : U) (hx : x∈wordPiece D d) :
    scaleAlgebra D t x=t^d • x := by
  refine Submodule.pow_induction_on_left' (M := generatorSpace D)
    (C := fun n y _ => scaleAlgebra D t y=t^n • y) ?_ ?_ ?_ hx
  · intro r
    simp
  · intro x y i hx hy ihx ihy
    rw [map_add,ihx,ihy,smul_add]
  · intro m hm i x hx ih
    obtain ⟨v,rfl⟩ := hm
    rw [map_mul,scaleAlgebra_generator,ih,smul_mul_smul,pow_succ']

def lieBasis : Module.Basis (ν ⊕ Fin 2) K (LieSpace D) :=
  ((Pi.basisFun K ν).prod (Module.Basis.finTwoProd K)).map (coordinates D).symm

@[simp] theorem lieBasis_inl (i : ν) :
    lieBasis D (.inl i)=generator D (Pi.basisFun K ν i) := by
  simp [lieBasis,Module.Basis.prod_apply,generator,coordinates] <;> rfl

@[simp] theorem lieBasis_inr (i : Fin 2) :
    lieBasis D (.inr i)=central D (Module.Basis.finTwoProd K i) := by
  simp [lieBasis,Module.Basis.prod_apply,central,coordinates] <;> rfl

def weight : ν ⊕ Fin 2 → ℕ := Sum.elim (fun _ => 1) (fun _ => 2)

def pbwDegree (a : (ν ⊕ Fin 2) →₀ ℕ) : ℕ :=
  (a.toMultiset.map (weight (ν := ν))).sum

theorem scaleAlgebra_lieBasis (t : K) (i : ν ⊕ Fin 2) :
    scaleAlgebra D t (UniversalEnvelopingAlgebra.ι K (lieBasis D i))=
      t^(weight i) • UniversalEnvelopingAlgebra.ι K (lieBasis D i) := by
  cases i with
  | inl i => simpa only [lieBasis_inl,weight,Sum.elim_inl,pow_one,generatorMap_apply] using
      scaleAlgebra_generator D t (Pi.basisFun K ν i)
  | inr i => simpa only [lieBasis_inr,weight,Sum.elim_inr] using
      scaleAlgebra_central D t (Module.Basis.finTwoProd K i)

theorem scaleAlgebra_pbwMonomial (t : K) (l : List (ν ⊕ Fin 2)) :
    scaleAlgebra D t (pbwMonomial K (LieSpace D) (lieBasis D) l)=
      t^((l.map weight).sum) • pbwMonomial K (LieSpace D) (lieBasis D) l := by
  induction l with
  | nil => simp
  | cons i l ih =>
      rw [pbwMonomial_cons,map_mul,scaleAlgebra_lieBasis,ih,
        List.map_cons,List.sum_cons,pow_add,smul_mul_smul]

theorem scaleAlgebra_pbwBasis (t : K) (a : (ν ⊕ Fin 2) →₀ ℕ) :
    scaleAlgebra D t ((lieBasis D).pbwBasis a)=
      t^(pbwDegree a) • (lieBasis D).pbwBasis a := by
  rw [Module.Basis.pbwBasis_apply,scaleAlgebra_pbwMonomial]
  congr 1
  congr 1
  rw [pbwDegree,←Multiset.sum_coe,←Multiset.map_coe,Multiset.sort_eq]

theorem powers_two_injective : Function.Injective (fun d : ℕ => (2 : K)^d) := by
  intro i j hij
  apply Nat.pow_right_injective (by decide : 2≤(2 : ℕ))
  change (2 : K)^i=(2 : K)^j at hij
  apply Nat.cast_injective (R := K)
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using hij

theorem wordPiece_le_pbwDegreePiece (d : ℕ) :
    wordPiece D d≤AlternatingForms.BasisDegree.piece
      (lieBasis D).pbwBasis pbwDegree d := by
  intro x hx
  exact (EigenBasisGrading.eigenvector_iff_degree_support
    (lieBasis D).pbwBasis pbwDegree (fun d => (2 : K)^d)
    (scaleAlgebra D 2).toLinearMap (scaleAlgebra_pbwBasis D 2)
    (powers_two_injective (K := K)) d x).mp (wordPiece_eigenvector D 2 d x hx)

variable (hD : Function.Surjective (bracketMap D))

include hD in
/-- Bracket generation puts the actual central generators in word degree two. -/
theorem central_mem_wordPiece (z : K × K) :
    UniversalEnvelopingAlgebra.ι K (central D z)∈wordPiece D 2 := by
  obtain ⟨a,rfl⟩ := hD z
  let X : ν → U := fun i => generatorMap D (Pi.basisFun K ν i)
  have he : (UniversalEnvelopingAlgebra.ι K).toLinearMap.comp
      ((central D).comp (bracketMap D))=commutatorMap X := by
    apply (Pi.basisFun K (ν × ν)).ext
    rintro ⟨i,j⟩
    simp only [LinearMap.comp_apply,bracketMap,Module.Basis.constr_basis,
      commutatorMap_basis]
    have hlie := (UniversalEnvelopingAlgebra.ι K (L := LieSpace D)).map_lie
      (generator D (Pi.basisFun K ν i)) (generator D (Pi.basisFun K ν j))
    have hbr : ⁅generator D (Pi.basisFun K ν i),generator D (Pi.basisFun K ν j)⁆=
        central D (D.bilinear (Pi.basisFun K ν i) (Pi.basisFun K ν j)) :=
      TwoStepCentralLie.generator_bracket D _ _
    erw [hbr] at hlie
    simpa only [LieHom.coe_toLinearMap,LieRing.of_associative_ring_bracket,
      QuadraticCommutatorQuotient.commutator,X,generatorMap_apply] using hlie
  change ((UniversalEnvelopingAlgebra.ι K).toLinearMap.comp
    ((central D).comp (bracketMap D))) a∈_
  rw [he,←(Pi.basisFun K (ν × ν)).sum_repr a,map_sum]
  apply Submodule.sum_mem
  intro p hp
  rw [map_smul,commutatorMap_basis,QuadraticCommutatorQuotient.commutator]
  apply Submodule.smul_mem
  exact Submodule.sub_mem _
    (mul_mem_wordPiece D (generator_mem_wordPiece D _) (generator_mem_wordPiece D _))
    (mul_mem_wordPiece D (generator_mem_wordPiece D _) (generator_mem_wordPiece D _))

include hD in
theorem lieBasis_mem_wordPiece (i : ν ⊕ Fin 2) :
    UniversalEnvelopingAlgebra.ι K (lieBasis D i)∈wordPiece D (weight i) := by
  cases i with
  | inl i => simpa only [lieBasis_inl,weight,Sum.elim_inl,generatorMap_apply] using
      generator_mem_wordPiece D (Pi.basisFun K ν i)
  | inr i => simpa only [lieBasis_inr,weight,Sum.elim_inr] using
      central_mem_wordPiece D hD (Module.Basis.finTwoProd K i)

include hD in
theorem pbwMonomial_mem_wordPiece (l : List (ν ⊕ Fin 2)) :
    pbwMonomial K (LieSpace D) (lieBasis D) l∈wordPiece D ((l.map weight).sum) := by
  induction l with
  | nil =>
      simp only [pbwMonomial_nil,List.map_nil,List.sum_nil,wordPiece,pow_zero]
      simpa only [map_one] using (Submodule.algebraMap_mem (R := K) (A := U) 1)
  | cons i l ih =>
      rw [pbwMonomial_cons,List.map_cons,List.sum_cons]
      exact mul_mem_wordPiece D (lieBasis_mem_wordPiece D hD i) ih

include hD in
theorem pbwBasis_mem_wordPiece (a : (ν ⊕ Fin 2) →₀ ℕ) :
    (lieBasis D).pbwBasis a∈wordPiece D (pbwDegree a) := by
  rw [Module.Basis.pbwBasis_apply]
  convert pbwMonomial_mem_wordPiece D hD _ using 1
  simp only [pbwDegree,←Multiset.sum_coe,←Multiset.map_coe,Multiset.sort_eq]

include hD in
/-- Exact equality with the original generator grading, in every degree. -/
theorem wordPiece_eq_pbwDegreePiece (d : ℕ) :
    wordPiece D d=AlternatingForms.BasisDegree.piece
      (lieBasis D).pbwBasis pbwDegree d := by
  apply le_antisymm (wordPiece_le_pbwDegreePiece D d)
  rw [AlternatingForms.BasisDegree.piece_eq_span]
  apply Submodule.span_le.mpr
  rintro x ⟨a,ha,rfl⟩
  rw [←ha]
  exact pbwBasis_mem_wordPiece D hD a

include hD in
/-- The dimension counts all weighted PBW exponent vectors, with no bound
on the requested degree. -/
theorem finrank_wordPiece (d : ℕ) :
    Module.finrank K (wordPiece D d)=
      Nat.card {a : (ν ⊕ Fin 2) →₀ ℕ // pbwDegree a=d} := by
  rw [wordPiece_eq_pbwDegreePiece D hD]
  exact EigenBasisGrading.finrank_piece (lieBasis D).pbwBasis pbwDegree d

/-- The word pieces form a genuine internal direct-sum decomposition. -/
def grading : TauCeti.InternalGrading K U ℕ where
  piece := wordPiece D
  isInternal := by
    have he : wordPiece D=AlternatingForms.BasisDegree.piece
        (lieBasis D).pbwBasis pbwDegree := funext (wordPiece_eq_pbwDegreePiece D hD)
    rw [he]
    exact (AlternatingForms.BasisDegree.grading (lieBasis D).pbwBasis pbwDegree).isInternal

end PaperVerification.TwoStepPBWGrading
end
end
end TAF_LiteralSource_0465

section TAF_LiteralSource_0466
/- Original module: PaperVerification.WeightedMonomialSeries -/


/-!
# The generating series of all positive-weight exponent vectors

The coefficient identity is proved by a literal equivalence between
weighted exponent vectors and divisible exponent vectors in the finite
coefficient convolution.  Thus the product of geometric series counts
all monomials of every weight; no Hilbert-series formula is postulated.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators PowerSeries

namespace PaperVerification.WeightedMonomialSeries

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  (w : ι → ℕ) (hw : ∀ i,w i≠0)

def Exponents (d : ℕ) := {a : ι →₀ ℕ // Finsupp.weight w a=d}

def scale (a : ι →₀ ℕ) : ι →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => w i*a i)

def unscale (a : ι →₀ ℕ) : ι →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => a i/w i)

@[simp] theorem scale_apply (a : ι →₀ ℕ) (i : ι) : scale w a i=w i*a i := by
  simp [scale]

@[simp] theorem unscale_apply (a : ι →₀ ℕ) (i : ι) : unscale w a i=a i/w i := by
  simp [unscale]

def divisibleAntidiagonal (d : ℕ) : Finset (ι →₀ ℕ) :=
  (Finset.finsuppAntidiag Finset.univ d).filter (fun a => ∀ i,w i∣a i)

theorem mem_divisibleAntidiagonal (d : ℕ) (a : ι →₀ ℕ) :
    a∈divisibleAntidiagonal w d ↔ (∑ i,a i)=d ∧ ∀ i,w i∣a i := by
  simp only [divisibleAntidiagonal,Finset.mem_filter,Finset.mem_finsuppAntidiag,
    Finset.subset_univ,and_true]

def exponentEquiv (d : ℕ) : Exponents w d ≃ divisibleAntidiagonal w d where
  toFun a := ⟨scale w a.val,by
    rw [mem_divisibleAntidiagonal]
    constructor
    · simpa only [scale_apply,Finsupp.weight_eq_sum,smul_eq_mul,mul_comm] using a.property
    · intro i
      exact ⟨a.val i,rfl⟩⟩
  invFun a := ⟨unscale w a.val,by
    have ha := (mem_divisibleAntidiagonal w d a.val).mp a.property
    rw [Finsupp.weight_eq_sum]
    calc
      (∑ i,unscale w a.val i • w i) = ∑ i,a.val i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact Nat.div_mul_cancel (ha.2 i)
      _ = d := ha.1⟩
  left_inv a := by
    apply Subtype.ext
    ext i
    simp only [unscale_apply,scale_apply,Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (hw i))]
  right_inv a := by
    apply Subtype.ext
    ext i
    simp only [scale_apply,unscale_apply]
    exact Nat.mul_div_cancel' (((mem_divisibleAntidiagonal w d a.val).mp a.property).2 i)

def geometric (i : ι) : ℤ⟦X⟧ :=
  PowerSeries.expand (w i) (hw i) (PowerSeries.invOneSubPow ℤ 1)

theorem coeff_geometric (i : ι) (d : ℕ) :
    PowerSeries.coeff d (geometric w hw i)=if w i∣d then 1 else 0 := by
  rw [geometric,PowerSeries.coeff_expand]
  simp [PowerSeries.invOneSubPow]

private theorem product_indicators (a : ι →₀ ℕ) :
    (∏ i,if w i∣a i then (1 : ℤ) else 0)=
      if ∀ i,w i∣a i then 1 else 0 := by
  by_cases h : ∀ i,w i∣a i
  · simp [h]
  · rw [if_neg h]
    obtain ⟨i,hi⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- Exact generating-series coefficients, including degree zero. -/
theorem coeff_product (d : ℕ) :
    PowerSeries.coeff d (∏ i,geometric w hw i)=Nat.card (Exponents w d) := by
  rw [PowerSeries.coeff_prod]
  simp_rw [coeff_geometric,product_indicators]
  rw [Finset.sum_boole]
  have hcard : Nat.card (Exponents w d)=(divisibleAntidiagonal w d).card := by
    have h := Nat.card_congr (exponentEquiv w hw d)
    simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using h
  rw [hcard]
  rfl

theorem series_eq_product :
    PowerSeries.mk (fun d => (Nat.card (Exponents w d) : ℤ))=
      ∏ i,geometric w hw i := by
  apply PowerSeries.ext
  intro d
  rw [PowerSeries.coeff_mk,coeff_product]

/-- Every factor is the inverse of its actual monomial denominator. -/
theorem geometric_mul_denominator (i : ι) :
    geometric w hw i*(1-PowerSeries.X^(w i))=1 := by
  have h := (PowerSeries.invOneSubPow ℤ 1).val_inv
  rw [PowerSeries.invOneSubPow_inv_eq_one_sub_pow,pow_one] at h
  have he := congrArg (PowerSeries.expand (w i) (hw i)) h
  simpa only [map_mul,map_sub,map_one,PowerSeries.expand_X,geometric] using he

include hw in
theorem series_mul_denominator_eq_one :
    PowerSeries.mk (fun d => (Nat.card (Exponents w d) : ℤ))*
      (∏ i,(1-PowerSeries.X^(w i)))=1 := by
  rw [series_eq_product w hw,←Finset.prod_mul_distrib]
  simp only [geometric_mul_denominator w hw,Finset.prod_const_one]

end PaperVerification.WeightedMonomialSeries
end
end
end TAF_LiteralSource_0466

section TAF_LiteralSource_0467
/- Original module: PaperVerification.TwoStepPBWHilbert -/


/-!
# The full Hilbert series of the actual two-step enveloping algebra

The degree pieces here are powers of the original generator subspace.
Their equality with weighted PBW pieces was established independently.
Counting the resulting exponent vectors gives the literal identity
`H(t) (1-t)^n (1-t^2)^2 = 1`, in all degrees at once.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators PowerSeries

namespace PaperVerification.TwoStepPBWGrading

open TwoStepCentralLie QuadraticCommutatorQuotient

variable {K ν : Type*} [Field K] [CharZero K] [Fintype ν] [LinearOrder ν]
  (D : Data (K := K) (V := ν → K) (Z := K × K))
  (hD : Function.Surjective (bracketMap D))

theorem pbwDegree_eq_weight (a : (ν ⊕ Fin 2) →₀ ℕ) :
    pbwDegree a=Finsupp.weight (weight (ν := ν)) a := by
  simpa only [pbwDegree,Finsupp.toMultiset_toFinsupp] using
    (Finsupp.weight_toFinsupp (weight (ν := ν)) a.toMultiset).symm

theorem weight_ne_zero (i : ν ⊕ Fin 2) : weight i≠0 := by
  cases i <;> simp [weight]

def hilbertSeries : ℤ⟦X⟧ :=
  PowerSeries.mk (fun d => (Module.finrank K (wordPiece D d) : ℤ))

include hD in
theorem hilbertSeries_eq_weightedSeries :
    hilbertSeries D=PowerSeries.mk (fun d =>
      (Nat.card (WeightedMonomialSeries.Exponents (weight (ν := ν)) d) : ℤ)) := by
  apply PowerSeries.ext
  intro d
  simp only [hilbertSeries,PowerSeries.coeff_mk,finrank_wordPiece D hD,
    pbwDegree_eq_weight,WeightedMonomialSeries.Exponents]

theorem weight_denominator :
    (∏ i : ν ⊕ Fin 2,(1-PowerSeries.X^(weight i) : ℤ⟦X⟧))=
      (1-PowerSeries.X)^Fintype.card ν*(1-PowerSeries.X^2)^2 := by
  rw [Fintype.prod_sum_type]
  simp only [weight,Sum.elim_inl,Sum.elim_inr,pow_one,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin]

include hD in
/-- The literal Hilbert-series formula with no degree cutoff. -/
theorem hilbertSeries_mul_denominator_eq_one :
    hilbertSeries D*((1-PowerSeries.X)^Fintype.card ν*(1-PowerSeries.X^2)^2)=1 := by
  rw [hilbertSeries_eq_weightedSeries D hD,←weight_denominator]
  exact WeightedMonomialSeries.series_mul_denominator_eq_one
    (weight (ν := ν)) weight_ne_zero

include hD in
/-- Equivalent inverse-series formulation of the printed rational expression. -/
theorem hilbertSeries_eq_inverse :
    hilbertSeries D=(PowerSeries.invOneSubPow ℤ (Fintype.card ν) : ℤ⟦X⟧)*
      PowerSeries.expand 2 (by decide) (PowerSeries.invOneSubPow ℤ 2 : ℤ⟦X⟧) := by
  let A : ℤ⟦X⟧ := (1-PowerSeries.X)^Fintype.card ν
  let B : ℤ⟦X⟧ := (1-PowerSeries.X^2)^2
  let C : ℤ⟦X⟧ := PowerSeries.invOneSubPow ℤ (Fintype.card ν)
  let E : ℤ⟦X⟧ := PowerSeries.expand 2 (by decide) (PowerSeries.invOneSubPow ℤ 2 : ℤ⟦X⟧)
  have hAC : A*C=1 := by
    simpa only [A,C,PowerSeries.invOneSubPow_inv_eq_one_sub_pow] using
      (PowerSeries.invOneSubPow ℤ (Fintype.card ν)).inv_val
  have hBE : B*E=1 := by
    have h := (PowerSeries.invOneSubPow ℤ 2).inv_val
    rw [PowerSeries.invOneSubPow_inv_eq_one_sub_pow] at h
    have he := congrArg (PowerSeries.expand 2 (by decide)) h
    simpa only [B,E,map_mul,map_pow,map_sub,map_one,PowerSeries.expand_X] using he
  have hDE : (A*B)*(C*E)=1 := by
    calc
      (A*B)*(C*E)=(A*C)*(B*E) := by ac_rfl
      _=1 := by rw [hAC,hBE,mul_one]
  have hHD : hilbertSeries D*(A*B)=1 := hilbertSeries_mul_denominator_eq_one D hD
  change hilbertSeries D=C*E
  calc
    hilbertSeries D=hilbertSeries D*1 := (mul_one _).symm
    _=hilbertSeries D*((A*B)*(C*E)) := by rw [hDE]
    _=(hilbertSeries D*(A*B))*(C*E) := (mul_assoc _ _ _).symm
    _=C*E := by rw [hHD,one_mul]

end PaperVerification.TwoStepPBWGrading
end
end
end TAF_LiteralSource_0467

section TAF_LiteralSource_0468
/- Original module: PaperVerification.AlternatingFormsQuadraticDualHilbert -/


/-!
# The genuine quadratic-dual grading and its complete Hilbert series

The degree pieces are defined inside the annihilator-presented quadratic
dual as powers of the span of its original free generators.  The actual
enveloping-algebra isomorphism is proved to preserve those generators,
and hence every degree piece.  The weighted PBW count therefore computes
this quadratic dual's Hilbert series, rather than that of an unrelated
graded presentation.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical PowerSeries

namespace PaperVerification.AlternatingForms.QuadraticDual

open TwoStepDual

variable {K ν : Type*} [Field K] [CharZero K] [Fintype ν] [LinearOrder ν] [Nonempty ν]
  (f g : ⋀[K]^2 (ν → K))

def generatorMap : (ν → K) →ₗ[K] QuadraticDual f g :=
  (Pi.basisFun K ν).constr K
    (fun i => RingQuot.mkAlgHom K (DualRelation f g) (FreeAlgebra.ι K i))

def generatorSpace : Submodule K (QuadraticDual f g) := LinearMap.range (generatorMap f g)

/-- Exact degree in the original quadratic generators. -/
def wordPiece (d : ℕ) : Submodule K (QuadraticDual f g) := generatorSpace f g ^ d

variable (hinj : Function.Injective (orbitExteriorRelationMap f g 1))

theorem generatorMap_transport :
    (quadraticDualEnvelopingEquiv f g hinj).toLinearMap.comp (generatorMap f g)=
      TwoStepPBWGrading.generatorMap (bracketData f g) := by
  apply (Pi.basisFun K ν).ext
  intro i
  simp only [LinearMap.comp_apply,generatorMap,Module.Basis.constr_basis,
    AlgEquiv.toLinearMap_apply,quadraticDualEnvelopingEquiv_generator,
    TwoStepPBWGrading.generatorMap]
  rfl

theorem generatorSpace_transport :
    (generatorSpace f g).map (quadraticDualEnvelopingEquiv f g hinj).toLinearMap=
      TwoStepPBWGrading.generatorSpace (bracketData f g) := by
  rw [generatorSpace,←LinearMap.range_comp,generatorMap_transport]
  rfl

theorem wordPiece_transport (d : ℕ) :
    (wordPiece f g d).map (quadraticDualEnvelopingEquiv f g hinj).toLinearMap=
      TwoStepPBWGrading.wordPiece (bracketData f g) d := by
  change (generatorSpace f g ^ d).map
    (quadraticDualEnvelopingEquiv f g hinj).toAlgHom.toLinearMap=_
  rw [Submodule.map_pow]
  change ((generatorSpace f g).map
    (quadraticDualEnvelopingEquiv f g hinj).toLinearMap)^d=_
  rw [generatorSpace_transport]
  rfl

def degreeEquiv (d : ℕ) :
    wordPiece f g d ≃ₗ[K] TwoStepPBWGrading.wordPiece (bracketData f g) d :=
  (Submodule.equivMapOfInjective (quadraticDualEnvelopingEquiv f g hinj).toLinearMap
    (quadraticDualEnvelopingEquiv f g hinj).injective (wordPiece f g d)).trans
      (LinearEquiv.ofEq _ _ (wordPiece_transport f g hinj d))

def hilbertSeries : ℤ⟦X⟧ :=
  PowerSeries.mk (fun d => (Module.finrank K (wordPiece f g d) : ℤ))

include hinj in
theorem hilbertSeries_transport :
    hilbertSeries f g=TwoStepPBWGrading.hilbertSeries (bracketData f g) := by
  apply PowerSeries.ext
  intro d
  simp only [hilbertSeries,TwoStepPBWGrading.hilbertSeries,PowerSeries.coeff_mk]
  exact congrArg (fun n : ℕ => (n : ℤ)) (degreeEquiv f g hinj d).finrank_eq

include hinj in
/-- The full printed rational series for the ordinary quadratic dual,
expressed as an exact identity of power series over the integers. -/
theorem hilbertSeries_mul_denominator_eq_one :
    hilbertSeries f g*((1-PowerSeries.X)^Fintype.card ν*(1-PowerSeries.X^2)^2)=1 := by
  rw [hilbertSeries_transport f g hinj]
  exact TwoStepPBWGrading.hilbertSeries_mul_denominator_eq_one (bracketData f g)
    (bracketMap_surjective f g hinj)

include hinj in
theorem hilbertSeries_eq_inverse :
    hilbertSeries f g=(PowerSeries.invOneSubPow ℤ (Fintype.card ν) : ℤ⟦X⟧)*
      PowerSeries.expand 2 (by decide) (PowerSeries.invOneSubPow ℤ 2) := by
  rw [hilbertSeries_transport f g hinj]
  exact TwoStepPBWGrading.hilbertSeries_eq_inverse (bracketData f g)
    (bracketMap_surjective f g hinj)

end PaperVerification.AlternatingForms.QuadraticDual
end
end
end TAF_LiteralSource_0468

section TAF_LiteralSource_0469
/- Original module: PaperVerification.AlternatingFormsQuadraticDualTensorHilbert -/


/-!
# The original tensor-quotient grading and Hilbert series

The generator map here is the composite of Mathlib's tensor-algebra
inclusion with the actual annihilator quotient map.  The comparison with
free-generator coordinates preserves this linear map, its range, and
every power of that range.  Thus the Hilbert formula also holds for the
literal tensor-algebra definition of the quadratic dual.

This source is a candidate until its full closure has been checked.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical PowerSeries

namespace PaperVerification.AlternatingForms.QuadraticDual

variable {K ν : Type*} [Field K] [CharZero K] [Fintype ν] [LinearOrder ν] [Nonempty ν]
  (f g : ⋀[K]^2 (ν → K))

def tensorGeneratorMap : Module.Dual K (ν → K) →ₗ[K] TensorQuadraticDual f g :=
  (RingQuot.mkAlgHom K (TensorDualRelation f g)).toLinearMap.comp (TensorAlgebra.ι K)

def tensorWordPiece (d : ℕ) : Submodule K (TensorQuadraticDual f g) :=
  (tensorGeneratorMap f g).range ^ d

theorem tensorGeneratorMap_transport :
    (tensorDualEquiv f g).toLinearMap.comp (tensorGeneratorMap f g)=
      (generatorMap f g).comp (Pi.basisFun K ν).toDualEquiv.symm.toLinearMap := by
  apply (Pi.basisFun K ν).dualBasis.ext
  intro i
  change tensorDualEquiv f g
      (RingQuot.mkAlgHom K (TensorDualRelation f g)
        (TensorAlgebra.ι K ((Pi.basisFun K ν).dualBasis i)))=
    generatorMap f g ((Pi.basisFun K ν).toDualEquiv.symm
      ((Pi.basisFun K ν).dualBasis i))
  rw [tensorDualEquiv_generator]
  simp only [Module.Basis.dualBasis,Module.Basis.map_apply,
    LinearEquiv.symm_apply_apply,generatorMap,Module.Basis.constr_basis]

theorem tensorWordPiece_transport (d : ℕ) :
    (tensorWordPiece f g d).map (tensorDualEquiv f g).toLinearMap=wordPiece f g d := by
  change ((tensorGeneratorMap f g).range ^ d).map
    (tensorDualEquiv f g).toAlgHom.toLinearMap=wordPiece f g d
  rw [Submodule.map_pow]
  change ((tensorGeneratorMap f g).range.map (tensorDualEquiv f g).toLinearMap)^d=_
  rw [←LinearMap.range_comp,tensorGeneratorMap_transport]
  rw [LinearMap.range_comp,
    LinearMap.range_eq_top.mpr (Pi.basisFun K ν).toDualEquiv.symm.surjective,
    Submodule.map_top]
  rfl

def tensorDegreeEquiv (d : ℕ) : tensorWordPiece f g d ≃ₗ[K] wordPiece f g d :=
  (Submodule.equivMapOfInjective (tensorDualEquiv f g).toLinearMap
    (tensorDualEquiv f g).injective (tensorWordPiece f g d)).trans
      (LinearEquiv.ofEq _ _ (tensorWordPiece_transport f g d))

def tensorHilbertSeries : ℤ⟦X⟧ :=
  PowerSeries.mk (fun d => (Module.finrank K (tensorWordPiece f g d) : ℤ))

theorem tensorHilbertSeries_eq : tensorHilbertSeries f g=hilbertSeries f g := by
  apply PowerSeries.ext
  intro d
  simp only [tensorHilbertSeries,hilbertSeries,PowerSeries.coeff_mk]
  exact congrArg (fun n : ℕ => (n : ℤ)) (tensorDegreeEquiv f g d).finrank_eq

theorem tensorHilbertSeries_mul_denominator_eq_one
    (hinj : Function.Injective (orbitExteriorRelationMap f g 1)) :
    tensorHilbertSeries f g*
      ((1-PowerSeries.X)^Fintype.card ν*(1-PowerSeries.X^2)^2)=1 := by
  rw [tensorHilbertSeries_eq]
  exact hilbertSeries_mul_denominator_eq_one f g hinj

end PaperVerification.AlternatingForms.QuadraticDual
end
end
end TAF_LiteralSource_0469

section TAF_LiteralSource_0470
/- Original module: PaperVerification.AlternatingFormsQuadraticDualPrincipal -/


/-!
# The complete generic quadratic-dual clause of Proposition 5.3

This endpoint retains every dimension `n ≥ 6` and a nonempty principal
open subset of the full original coefficient space.  The source is the
ordinary annihilator-defined quadratic dual.  Its isomorphism with the
actual ordinary two-step enveloping algebra, both Lie-degree dimensions,
triple-bracket vanishing, and its full original-generator Hilbert series
are conclusions of the theorem.

The separate assertion that the exterior quotient is Koszul exactly for
`n ≤ 4` is not asserted by this endpoint.  This source remains a proof
candidate until compiled with its complete dependency closure.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical PowerSeries

namespace PaperVerification.AlternatingForms

variable (K : Type) [Field K] [CharZero K]

theorem paper_proposition_5_3_dual_clause (n : ℕ) (hn : 6≤n) :
    ∃ (ι : Type) (fin : Fintype ι),
      letI := fin
      ∃ b₂ : Module.Basis ι K (⋀[K]^2 (Fin n → K)),
        ∃ Q : MvPolynomial (ι ⊕ ι) K, Q≠0 ∧
          (∃ y : (ι ⊕ ι) → K, MvPolynomial.eval y Q≠0) ∧
          ∀ y : (ι ⊕ ι) → K, MvPolynomial.eval y Q≠0 →
            let f := (orbitFormsFromCoordinates b₂ y).1
            let g := (orbitFormsFromCoordinates b₂ y).2
            let D := TwoStepDual.bracketData f g
            Nonempty (QuadraticDual.TensorQuadraticDual f g ≃ₐ[K]
              UniversalEnvelopingAlgebra K (TwoStepCentralLie.LieSpace D)) ∧
            Module.finrank K (TwoStepCentralLie.degreeOne D)=n ∧
            Module.finrank K (TwoStepCentralLie.degreeTwo D)=2 ∧
            Disjoint (TwoStepCentralLie.degreeOne D) (TwoStepCentralLie.degreeTwo D) ∧
            TwoStepCentralLie.degreeOne D ⊔ TwoStepCentralLie.degreeTwo D=⊤ ∧
            TwoStepCentralLie.degreeTwo D=Submodule.span K
              (Set.range (fun p : Fin n × Fin n =>
                ⁅TwoStepCentralLie.generator D (Pi.basisFun K (Fin n) p.1),
                  TwoStepCentralLie.generator D (Pi.basisFun K (Fin n) p.2)⁆)) ∧
            (∀ x y z : TwoStepCentralLie.LieSpace D, ⁅⁅x,y⁆,z⁆=0) ∧
            QuadraticDual.tensorHilbertSeries f g*
              ((1-PowerSeries.X)^n*(1-PowerSeries.X^2)^2)=1 := by
  letI : NeZero n := ⟨by omega⟩
  have hdim : Module.finrank K (Fin n → K)=n := by simp
  obtain ⟨ι,fin,h⟩ := generic_cubic_wedge_injective (K := K) (M := Fin n → K) n hn hdim
  letI := fin
  obtain ⟨b₂,Q,hQ,hnonempty,h⟩ := h
  refine ⟨ι,fin,b₂,Q,hQ,hnonempty,?_⟩
  intro y hy
  let f := (orbitFormsFromCoordinates b₂ y).1
  let g := (orbitFormsFromCoordinates b₂ y).2
  let D := TwoStepDual.bracketData f g
  refine ⟨⟨QuadraticDual.tensorQuadraticDualEnvelopingEquiv f g (h y hy)⟩,
    ?_,?_,?_,?_,?_,?_,?_⟩
  · exact (TwoStepCentralLie.finrank_degreeOne D).trans hdim
  · simpa using TwoStepCentralLie.finrank_degreeTwo D
  · exact TwoStepCentralLie.degree_subspaces_disjoint D
  · exact TwoStepCentralLie.degree_subspaces_span D
  · exact QuadraticCommutatorQuotient.degreeTwo_eq_span_generator_brackets D
      (TwoStepDual.bracketMap_surjective f g (h y hy))
  · exact TwoStepCentralLie.bracket_bracket_eq_zero D
  · simpa only [Fintype.card_fin] using
      QuadraticDual.tensorHilbertSeries_mul_denominator_eq_one f g (h y hy)

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0470

section TAF_LiteralSource_0471
/- Original module: PaperVerification.BasisQuotientSelection -/


/-! # Exact coordinates after quotienting by a subset of a genuine basis -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.BasisQuotientSelection

variable {K M I : Type*} [Field K] [AddCommGroup M] [Module K M]
  (B : Module.Basis I K M) (P : I → Prop)

def discarded : Submodule K M := Submodule.span K (B '' {i | ¬P i})

def projection : M →ₗ[K] ({i // P i} →₀ K) :=
  (Finsupp.lcomapDomain (R := K) (M := K) Subtype.val Subtype.val_injective).comp B.repr.toLinearMap

@[simp] theorem projection_apply (x : M) (i : {i // P i}) :
    projection B P x i=B.repr x i.val := rfl

theorem projection_surjective : Function.Surjective (projection B P) := by
  intro x
  refine ⟨B.repr.symm (Finsupp.mapDomain Subtype.val x),?_⟩
  change Finsupp.lcomapDomain (R := K) (M := K) Subtype.val Subtype.val_injective
    (B.repr (B.repr.symm (Finsupp.mapDomain Subtype.val x)))=x
  rw [LinearEquiv.apply_symm_apply]
  exact Finsupp.leftInverse_lcomapDomain_mapDomain Subtype.val Subtype.val_injective x

@[simp] theorem projection_basis (i : {i // P i}) :
    projection B P (B i.val)=Finsupp.single i 1 := by
  apply Finsupp.ext
  intro j
  rw [projection_apply,Module.Basis.repr_self]
  simp only [Finsupp.single_apply,Subtype.ext_iff]

theorem discarded_eq_ker : discarded B P=(projection B P).ker := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨i,hi,rfl⟩
    apply LinearMap.mem_ker.mpr
    apply Finsupp.ext
    intro j
    rw [projection_apply,Module.Basis.repr_self,Finsupp.zero_apply]
    exact Finsupp.single_eq_of_ne (fun h => hi (h ▸ j.property))
  · intro x hx
    have hz := LinearMap.mem_ker.mp hx
    rw [←B.linearCombination_repr x,Finsupp.linearCombination_apply,Finsupp.sum]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨i,?_,rfl⟩
    intro hP
    have he := congrArg (fun z : {i // P i} →₀ K => z ⟨i,hP⟩) hz
    rw [projection_apply,Finsupp.zero_apply] at he
    exact (Finsupp.mem_support_iff.mp hi) he

/-- This is an equivalence of the literal vector-space quotient by the
specified span, with all retained coordinates. -/
def quotientCoordinates : (M ⧸ discarded B P) ≃ₗ[K] ({i // P i} →₀ K) :=
  (Submodule.quotEquivOfEq _ _ (discarded_eq_ker B P)).trans
    ((projection B P).quotKerEquivOfSurjective (projection_surjective B P))

@[simp] theorem quotientCoordinates_mk (x : M) :
    quotientCoordinates B P (Submodule.Quotient.mk x)=projection B P x := by
  simp only [quotientCoordinates,LinearEquiv.trans_apply,Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

def quotientBasis : Module.Basis {i // P i} K (M ⧸ discarded B P) :=
  .ofRepr (quotientCoordinates B P)

@[simp] theorem quotientBasis_apply (i : {i // P i}) :
    quotientBasis B P i=Submodule.Quotient.mk (B i.val) := by
  apply (quotientCoordinates B P).injective
  rw [quotientCoordinates_mk,projection_basis]
  exact Module.Basis.repr_self (quotientBasis B P) i

end PaperVerification.BasisQuotientSelection
end
end
end TAF_LiteralSource_0471

section TAF_LiteralSource_0472
/- Original module: PaperVerification.ExteriorMonomialQuotient -/


/-!
# Literal bases of exterior monomial ideal quotients

The ideal is the ordinary ideal generated by specified exterior basis
monomials. Its underlying vector subspace is proved to be exactly the
span of monomials containing a forbidden subset. Consequently the
remaining exterior monomials give an actual basis of the ring quotient.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.ExteriorMonomialQuotient

section Signs

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

theorem intUnit_smul_mem (N : Submodule R V) (u : ℤˣ) {x : V} (hx : x∈N) :
    u • x∈N := by
  change (u : ℤ) • x∈N
  exact N.toAddSubgroup.zsmul_mem hx _

theorem mem_of_intUnit_smul_mem (N : Submodule R V) (u : ℤˣ) {x : V}
    (hx : u • x∈N) : x∈N := by
  simpa only [inv_smul_smul] using intUnit_smul_mem N u⁻¹ hx

end Signs

variable {K M I : Type*} [Field K] [AddCommGroup M] [Module K M]
  [LinearOrder I] (b : Module.Basis I K M) (F : Set (Finset I))

/-- A set is forbidden precisely when it contains a specified generator. -/
def Bad (S : Finset I) : Prop := ∃ T∈F,T⊆S

def Allowed := {S : Finset I // ¬Bad F S}

def badSpace : Submodule K (ExteriorAlgebra K M) :=
  Submodule.span K (b.ExteriorAlgebra '' {S | Bad F S})

def monomialIdeal : Ideal (ExteriorAlgebra K M) :=
  Ideal.span (b.ExteriorAlgebra '' F)

theorem bad_mono {S T : Finset I} (hS : Bad F S) (hST : S⊆T) : Bad F T := by
  obtain ⟨U,hU,hUS⟩ := hS
  exact ⟨U,hU,hUS.trans hST⟩

theorem basis_mul_disjoint (S T : Finset I) (h : Disjoint S T) :
    ∃ u : ℤˣ,b.ExteriorAlgebra S*b.ExteriorAlgebra T=u • b.ExteriorAlgebra (S∪T) := by
  let s : Set.powersetCard I S.card := ⟨S,rfl⟩
  let t : Set.powersetCard I T.card := ⟨T,rfl⟩
  refine ⟨(Set.powersetCard.permOfDisjoint (show Disjoint s.val t.val from h)).sign,?_⟩
  simpa only [Set.powersetCard.coe_disjUnion,Finset.disjUnion_eq_union,s,t] using
    ExteriorAlgebra.basis_mul_of_disjoint b s t h

theorem basis_mul_not_disjoint (S T : Finset I) (h : ¬Disjoint S T) :
    b.ExteriorAlgebra S*b.ExteriorAlgebra T=0 :=
  ExteriorAlgebra.basis_mul_of_not_disjoint b
    (⟨S,rfl⟩ : Set.powersetCard I S.card)
    (⟨T,rfl⟩ : Set.powersetCard I T.card) h

theorem basis_mul_mem_badSpace (S T : Finset I)
    (h : Bad F S ∨ Bad F T) : b.ExteriorAlgebra S*b.ExteriorAlgebra T∈badSpace b F := by
  by_cases hd : Disjoint S T
  · obtain ⟨u,hu⟩ := basis_mul_disjoint b S T hd
    rw [hu]
    apply intUnit_smul_mem
    apply Submodule.subset_span
    refine ⟨S∪T,?_,rfl⟩
    rcases h with hS | hT
    · exact bad_mono F hS Finset.subset_union_left
    · exact bad_mono F hT Finset.subset_union_right
  · rw [basis_mul_not_disjoint b S T hd]
    exact (badSpace b F).zero_mem

theorem basis_mul_mem_badSpace_right (S : Finset I) {y : ExteriorAlgebra K M}
    (hy : y∈badSpace b F) : b.ExteriorAlgebra S*y∈badSpace b F := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨T,hT,rfl⟩ := hy
      exact basis_mul_mem_badSpace b F S T (Or.inr hT)
  | zero => simpa only [mul_zero] using (badSpace b F).zero_mem
  | add y z hy hz ihy ihz =>
      simpa only [mul_add] using (badSpace b F).add_mem ihy ihz
  | smul a y hy ih =>
      simpa only [mul_smul_comm] using (badSpace b F).smul_mem a ih

theorem basis_mul_mem_badSpace_left (T : Finset I) {x : ExteriorAlgebra K M}
    (hx : x∈badSpace b F) : x*b.ExteriorAlgebra T∈badSpace b F := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨S,hS,rfl⟩ := hx
      exact basis_mul_mem_badSpace b F S T (Or.inl hS)
  | zero => simpa only [zero_mul] using (badSpace b F).zero_mem
  | add x y hx hy ihx ihy =>
      simpa only [add_mul] using (badSpace b F).add_mem ihx ihy
  | smul a x hx ih =>
      simpa only [smul_mul_assoc] using (badSpace b F).smul_mem a ih

theorem mul_mem_badSpace_right (x : ExteriorAlgebra K M) {y : ExteriorAlgebra K M}
    (hy : y∈badSpace b F) : x*y∈badSpace b F := by
  rw [←b.ExteriorAlgebra.linearCombination_repr x,Finsupp.linearCombination_apply,
    Finsupp.sum,Finset.sum_mul]
  apply Submodule.sum_mem
  intro S hS
  rw [smul_mul_assoc]
  exact (badSpace b F).smul_mem _ (basis_mul_mem_badSpace_right b F S hy)

theorem mul_mem_badSpace_left (y : ExteriorAlgebra K M) {x : ExteriorAlgebra K M}
    (hx : x∈badSpace b F) : x*y∈badSpace b F := by
  rw [←b.ExteriorAlgebra.linearCombination_repr y,Finsupp.linearCombination_apply,
    Finsupp.sum,Finset.mul_sum]
  apply Submodule.sum_mem
  intro T hT
  rw [mul_smul_comm]
  exact (badSpace b F).smul_mem _ (basis_mul_mem_badSpace_left b F T hx)

/-- The computed vector-space span is itself a two-sided ideal. -/
def closedIdeal : Ideal (ExteriorAlgebra K M) where
  carrier := badSpace b F
  zero_mem' := (badSpace b F).zero_mem
  add_mem' := (badSpace b F).add_mem
  smul_mem' a x hx := mul_mem_badSpace_right b F a hx

instance : (closedIdeal b F).IsTwoSided where
  mul_mem_of_left y hx := mul_mem_badSpace_left b F y hx

theorem basis_mem_monomialIdeal_of_bad (S : Finset I) (hS : Bad F S) :
    b.ExteriorAlgebra S∈monomialIdeal b F := by
  obtain ⟨T,hT,hTS⟩ := hS
  have hg : b.ExteriorAlgebra T∈monomialIdeal b F :=
    Ideal.subset_span ⟨T,hT,rfl⟩
  have hp := (monomialIdeal b F).mul_mem_left (b.ExteriorAlgebra (S\T)) hg
  obtain ⟨u,hu⟩ := basis_mul_disjoint b (S\T) T disjoint_sdiff_self_left
  rw [hu,Finset.sdiff_union_of_subset hTS] at hp
  exact mem_of_intUnit_smul_mem (monomialIdeal b F) u hp

/-- Equality with the ordinary generated ideal, not a replacement definition. -/
theorem monomialIdeal_eq_closedIdeal : monomialIdeal b F=closedIdeal b F := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro x ⟨S,hS,rfl⟩
    exact Submodule.subset_span ⟨S,⟨S,hS,(by intro i hi; exact hi)⟩,rfl⟩
  · intro x hx
    change x∈badSpace b F at hx
    have hincl : badSpace b F≤(monomialIdeal b F).restrictScalars K := by
      apply Submodule.span_le.mpr
      rintro x ⟨S,hS,rfl⟩
      exact basis_mem_monomialIdeal_of_bad b F S hS
    exact hincl hx

instance : (monomialIdeal b F).IsTwoSided := by
  rw [monomialIdeal_eq_closedIdeal]
  infer_instance

theorem badSpace_eq_restrict : badSpace b F=(monomialIdeal b F).restrictScalars K := by
  rw [monomialIdeal_eq_closedIdeal]
  rfl

theorem discarded_eq_badSpace :
    BasisQuotientSelection.discarded b.ExteriorAlgebra (fun S => ¬Bad F S)=badSpace b F := by
  simp only [BasisQuotientSelection.discarded,not_not,badSpace]

/-- Genuine coordinates of the ring quotient, obtained by proving its
relation space is exactly the span of discarded exterior basis vectors. -/
def quotientCoordinates :
    (ExteriorAlgebra K M⧸monomialIdeal b F) ≃ₗ[K] (Allowed F→₀K) :=
  (Submodule.Quotient.restrictScalarsEquiv K (monomialIdeal b F)).symm.trans
    ((Submodule.quotEquivOfEq _ _
      ((discarded_eq_badSpace b F).trans (badSpace_eq_restrict b F)).symm).trans
        (BasisQuotientSelection.quotientCoordinates b.ExteriorAlgebra (fun S => ¬Bad F S)))

def quotientBasis : Module.Basis (Allowed F) K
    (ExteriorAlgebra K M⧸monomialIdeal b F) := .ofRepr (quotientCoordinates b F)

@[simp] theorem quotientCoordinates_mk (x : ExteriorAlgebra K M) :
    quotientCoordinates b F (Ideal.Quotient.mk (monomialIdeal b F) x)=
      BasisQuotientSelection.projection b.ExteriorAlgebra (fun S => ¬Bad F S) x := by
  simp only [quotientCoordinates,LinearEquiv.trans_apply,Submodule.quotEquivOfEq_mk,
    BasisQuotientSelection.quotientCoordinates_mk]
  rfl

@[simp] theorem quotientBasis_apply (S : Allowed F) :
    quotientBasis b F S=Ideal.Quotient.mk (monomialIdeal b F) (b.ExteriorAlgebra S.val) := by
  apply (quotientCoordinates b F).injective
  rw [quotientCoordinates_mk,BasisQuotientSelection.projection_basis]
  exact Module.Basis.repr_self (quotientBasis b F) S

theorem quotient_monomial_eq_zero_of_bad (S : Finset I) (hS : Bad F S) :
    Ideal.Quotient.mk (monomialIdeal b F) (b.ExteriorAlgebra S)=0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (basis_mem_monomialIdeal_of_bad b F S hS)

/-- The augmentation on a nonempty exterior basis monomial is zero. -/
theorem algebraMapInv_basis (S : Finset I) (hS : S.Nonempty) :
    ExteriorAlgebra.algebraMapInv (b.ExteriorAlgebra S)=0 := by
  rw [b.exteriorAlgebra_eq_prod_map_sort,map_list_prod]
  obtain ⟨i,hi⟩ := hS
  apply List.prod_eq_zero (l := ((S.sort (fun a b : I => a ≤ b)).map b).map (ExteriorAlgebra.ι K) |>.map
    (ExteriorAlgebra.algebraMapInv : ExteriorAlgebra K M→ₐ[K]K))
  apply List.mem_map.mpr
  refine ⟨ExteriorAlgebra.ι K (b i),?_,?_⟩
  · apply List.mem_map.mpr
    refine ⟨b i,List.mem_map.mpr ⟨i,(Finset.mem_sort _).mpr hi,rfl⟩,rfl⟩
  · simp only [ExteriorAlgebra.algebraMapInv,ExteriorAlgebra.lift_ι_apply,LinearMap.zero_apply]

variable (hF : ∀ S∈F,S.Nonempty)

include hF in
theorem monomialIdeal_le_augmentation_ker :
    monomialIdeal b F≤RingHom.ker
      (ExteriorAlgebra.algebraMapInv : ExteriorAlgebra K M→ₐ[K]K).toRingHom := by
  apply Ideal.span_le.mpr
  rintro x ⟨S,hS,rfl⟩
  exact algebraMapInv_basis b S (hF S hS)

def augmentation : (ExteriorAlgebra K M⧸monomialIdeal b F)→ₐ[K]K :=
  Ideal.Quotient.liftₐ (monomialIdeal b F) ExteriorAlgebra.algebraMapInv
    (fun x hx => monomialIdeal_le_augmentation_ker b F hF hx)

@[simp] theorem augmentation_mk (x : ExteriorAlgebra K M) :
    augmentation b F hF (Ideal.Quotient.mk (monomialIdeal b F) x)=
      ExteriorAlgebra.algebraMapInv x := rfl

end PaperVerification.ExteriorMonomialQuotient
end
end
end TAF_LiteralSource_0472

section TAF_LiteralSource_0473
/- Original module: PaperVerification.QuadraticWordBarFibers -/


/-!
# Literal bar fibers for arbitrary quadratic word relations

A bar tensor is a list of actual positive basis indices. The equivalence
of each positive factor with its normal word identifies fixed-concatenation
tensor indices with the admissible factorizations used in the cut complex.
No tensor factors, internal degrees, or basis words are discarded.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PaperVerification.QuadraticWordBar

open PaperVerification.AlternatingForms.BarCompositions


/-- A nonempty word whose literal adjacent pairs are allowed. No reflexivity
or order structure is required, so square-zero generators are included. -/
def PositiveWord {J : Type*} (R : J → J → Prop) :=
  {W : List J // 0 < W.length ∧ W.IsChain R}

variable {C J : Type*} {R : J → J → Prop} (e : C ≃ PositiveWord R)

def flattenBarWord (L : List C) : List J :=
  (L.map (fun c ↦ (e c).val)).flatten

def ActualBarIndex (W : List J) (r : ℕ) :=
  {L : List C // flattenBarWord e L=W ∧ L.length=r}

def actualFactorization (W : List J) (r : ℕ) (L : ActualBarIndex e W r) :
    BarIndex R W r :=
  ⟨⟨⟨L.val.map (fun c ↦ (e c).val),L.property.1,by
    intro T hT
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hT
    exact (e c).property.1⟩,by
      intro T hT
      obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hT
      exact (e c).property.2⟩,by
        simpa only [List.length_map] using L.property.2⟩

def factorizationBarWord (W : List J) (L : AdmissibleFactorization R W) : List C :=
  L.val.val.attach.map (fun T ↦ e.symm
    ⟨T.val,L.val.property.2 T.val T.property,L.property T.val T.property⟩)

theorem factorizationBarWord_map (W : List J)
    (L : AdmissibleFactorization R W) :
    (factorizationBarWord e W L).map (fun c ↦ (e c).val)=L.val.val := by
  simp only [factorizationBarWord,List.map_map,Function.comp_def]
  calc
    _ = L.val.val.attach.map Subtype.val := by
      apply List.map_congr_left
      intro T hT
      exact congrArg (fun Z : PositiveWord R => Z.val)
        (e.apply_symm_apply ⟨T.val,L.val.property.2 T.val T.property,
          L.property T.val T.property⟩)
    _ = _ := List.attach_map_subtype_val _

theorem factorizationBarWord_flatten (W : List J)
    (L : AdmissibleFactorization R W) :
    flattenBarWord e (factorizationBarWord e W L)=W := by
  rw [flattenBarWord,factorizationBarWord_map,L.val.property.1]

theorem factorizationBarWord_length (W : List J)
    (L : AdmissibleFactorization R W) :
    (factorizationBarWord e W L).length=L.val.val.length := by
  simp only [factorizationBarWord,List.length_map,List.length_attach]

def actualBarIndexEquiv (W : List J) (r : ℕ) :
    ActualBarIndex e W r ≃ BarIndex R W r where
  toFun := actualFactorization e W r
  invFun L := ⟨factorizationBarWord e W L.val,
    factorizationBarWord_flatten e W L.val,
    (factorizationBarWord_length e W L.val).trans L.property⟩
  left_inv L := by
    apply Subtype.ext
    apply (List.map_injective_iff.mpr
      (show Function.Injective (fun c : C ↦ (e c).val) from
        fun c d h ↦ e.injective (Subtype.ext h)))
    rw [factorizationBarWord_map]
    rfl
  right_inv L := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact factorizationBarWord_map e W L.val

@[simp] theorem actualBarIndexEquiv_length (W : List J) (r : ℕ)
    (L : ActualBarIndex e W r) :
    (actualBarIndexEquiv e W r L).val.val.val.length=L.val.length :=
  List.length_map _

def InternalDegreeIndex (r N : ℕ) :=
  {L : List C // L.length=r ∧ (flattenBarWord e L).length=N}

def internalDegreeFiberEquiv (r N : ℕ) :
    InternalDegreeIndex e r N ≃
      Σ W : {W : List J // W.length=N},ActualBarIndex e W.val r where
  toFun L := ⟨⟨flattenBarWord e L.val,L.property.2⟩,⟨L.val,rfl,L.property.1⟩⟩
  invFun L := ⟨L.2.val,L.2.property.2,by
    rw [L.2.property.1]
    exact L.1.property⟩
  left_inv L := rfl
  right_inv L := by
    rcases L with ⟨⟨W,hW⟩,⟨L,hL,hlen⟩⟩
    dsimp only at hL
    subst W
    rfl

def internalDegreeCutFiberEquiv (r N : ℕ) :
    InternalDegreeIndex e r N ≃
      Σ W : {W : List J // W.length=N},BarIndex R W.val r :=
  (internalDegreeFiberEquiv e r N).trans
    (Equiv.sigmaCongrRight (fun W ↦ actualBarIndexEquiv e W.val r))

variable {K : Type*} [CommRing K]

def internalDegreePiece (r N : ℕ) : Submodule K (List C →₀ K) :=
  Finsupp.supported K K {L | L.length=r ∧ (flattenBarWord e L).length=N}

def internalDegreeCoordinates (r N : ℕ) :
    internalDegreePiece (K := K) e r N ≃ₗ[K] (InternalDegreeIndex e r N →₀ K) :=
  Finsupp.supportedEquivFinsupp (R := K) _

def internalDegreeCutCoordinates (r N : ℕ) :
    internalDegreePiece (K := K) e r N ≃ₗ[K]
      ((Σ W : {W : List J // W.length=N},BarIndex R W.val r) →₀ K) :=
  (internalDegreeCoordinates e r N).trans
    (Finsupp.domLCongr (internalDegreeCutFiberEquiv e r N))

end PaperVerification.QuadraticWordBar

end
end
end TAF_LiteralSource_0473

section TAF_LiteralSource_0474
/- Original module: PaperVerification.QuadraticWordBarExact -/


/-!
# Exactness of the quadratic monomial bar complex

There are finitely many literal generator words of a fixed length. The
normal-block tensor module splits over these words, and the cut
differential acts separately on each fiber. The actual cut contraction
therefore proves exactness of this full leading complex away from the
diagonal, with no rank or acyclicity hypothesis.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace PaperVerification.QuadraticWordBar

open PaperVerification.AlternatingForms.BarCompositions

variable {C J : Type*} [Fintype J]
  {R : J → J → Prop} (e : C ≃ PositiveWord R)

instance fixedWordFintype (N : ℕ) : Fintype {W : List J // W.length=N} := by
  apply Fintype.ofSurjective
    (fun f : Fin N → J ↦ (⟨List.ofFn f,List.length_ofFn⟩ : {W : List J // W.length=N}))
  intro W
  rcases W with ⟨W,hW⟩
  subst N
  refine ⟨W.get,?_⟩
  apply Subtype.ext
  exact List.ofFn_get W

variable {K : Type*} [CommRing K]

def internalDegreeFiberCoordinates (r N : ℕ) :
    internalDegreePiece (K := K) e r N ≃ₗ[K]
      (W : {W : List J // W.length=N}) → (BarIndex R W.val r →₀ K) :=
  (internalDegreeCutCoordinates e r N).trans (Finsupp.sigmaFinsuppLEquivPiFinsupp K)

def leadingFiberDifferential (r N : ℕ) :
    ((W : {W : List J // W.length=N}) → (BarIndex R W.val (r+1) →₀ K)) →ₗ[K]
      ((W : {W : List J // W.length=N}) → (BarIndex R W.val r →₀ K)) where
  toFun z W := cutModelDifferential R W.val r (z W)
  map_add' z w := by
    funext W
    exact map_add (cutModelDifferential (K := K) R W.val r) (z W) (w W)
  map_smul' a z := by
    funext W
    simpa only [Pi.smul_apply,RingHom.id_apply] using
      map_smul (cutModelDifferential (K := K) R W.val r) a (z W)

theorem leadingFiberDifferential_apply (r N : ℕ)
    (z : (W : {W : List J // W.length=N}) → (BarIndex R W.val (r+1) →₀ K))
    (W : {W : List J // W.length=N}) :
    leadingFiberDifferential (K := K) (J := J) (R := R) r N z W=
      cutModelDifferential (K := K) R W.val r (z W) := rfl

def leadingDegreeDifferential (r N : ℕ) :
    internalDegreePiece (K := K) e (r+1) N →ₗ[K] internalDegreePiece (K := K) e r N :=
  (internalDegreeFiberCoordinates e r N).symm.toLinearMap.comp
    ((leadingFiberDifferential r N).comp
      (internalDegreeFiberCoordinates e (r+1) N).toLinearMap)

theorem leadingDegreeDifferential_comm (r N : ℕ)
    (z : internalDegreePiece (K := K) e (r+1) N) :
    internalDegreeFiberCoordinates e r N (leadingDegreeDifferential e r N z)=
      leadingFiberDifferential r N (internalDegreeFiberCoordinates e (r+1) N z) := by
  simp only [leadingDegreeDifferential,LinearMap.comp_apply,LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]

theorem leadingFiberDifferential_squared (r N : ℕ)
    (z : (W : {W : List J // W.length=N}) → (BarIndex R W.val (r+2) →₀ K)) :
    leadingFiberDifferential r N (leadingFiberDifferential (K := K) (r+1) N z)=0 := by
  funext W
  exact cutModelDifferential_squared R W.val r (z W)

theorem leadingFiber_range_eq_ker (r N : ℕ) (hr : r+1≠N) :
    (leadingFiberDifferential (K := K) (J := J) (R := R) (r+1) N).range=
      (leadingFiberDifferential (K := K) (J := J) (R := R) r N).ker := by
  ext z
  constructor
  · rintro ⟨y,rfl⟩
    exact LinearMap.mem_ker.mpr (leadingFiberDifferential_squared r N y)
  · intro hz
    have hc : ∀ W : {W : List J // W.length=N},
        ∃ y : BarIndex R W.val (r+2) →₀ K,
          cutModelDifferential R W.val (r+1) y=z W := by
      intro W
      apply cutModel_cycle_is_boundary R W.val (r+1)
        (by simpa only [W.property] using hr) (z W)
      have he := congrFun (LinearMap.mem_ker.mp hz) W
      change cutModelDifferential R W.val r (z W)=0 at he
      have he' := congrArg (barExteriorMap (K := K) R W.val r) he
      rw [barExteriorMap_differential,map_zero] at he'
      exact he'
    refine ⟨fun W ↦ Classical.choose (hc W),?_⟩
    funext W
    exact Classical.choose_spec (hc W)

theorem leadingDegree_range_eq_ker (r N : ℕ) (hr : r+1≠N) :
    (leadingDegreeDifferential (K := K) e (r+1) N).range=
      (leadingDegreeDifferential (K := K) e r N).ker := by
  ext z
  constructor
  · rintro ⟨y,rfl⟩
    apply LinearMap.mem_ker.mpr
    apply (internalDegreeFiberCoordinates e r N).injective
    rw [leadingDegreeDifferential_comm,leadingDegreeDifferential_comm,map_zero]
    exact leadingFiberDifferential_squared r N _
  · intro hz
    have hc : internalDegreeFiberCoordinates e (r+1) N z∈
        (leadingFiberDifferential (K := K) (J := J) (R := R) r N).ker := by
      apply LinearMap.mem_ker.mpr
      rw [←leadingDegreeDifferential_comm,LinearMap.mem_ker.mp hz,map_zero]
    rw [←leadingFiber_range_eq_ker r N hr] at hc
    obtain ⟨y,hy⟩ := hc
    refine ⟨(internalDegreeFiberCoordinates e (r+2) N).symm y,?_⟩
    apply (internalDegreeFiberCoordinates e (r+1) N).injective
    rw [leadingDegreeDifferential_comm,LinearEquiv.apply_symm_apply,hy]

end PaperVerification.QuadraticWordBar

end
end
end TAF_LiteralSource_0474

section TAF_LiteralSource_0475
/- Original module: PaperVerification.QuadraticWordBarMerging -/


/-!
# Normal adjacent multiplication and admissible cut deletion

Normal merging is defined on the literal positive words. Its output,
when present, is exactly the factorization obtained by deleting the
corresponding interior cut. Thus optional cuts are precisely the nonzero
normal adjacent products.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace PaperVerification.QuadraticWordBar

open PaperVerification.AlternatingForms.BarCompositions

open PaperVerification.AlternatingForms.BarCoefficientFormula PaperVerification.ReducedBarBasis

variable {C J : Type*} {R : J → J → Prop} (e : C ≃ PositiveWord R)

def concatenateNormal (a b : C)
    (h : ((e a).val++(e b).val).IsChain R) : C :=
  e.symm ⟨(e a).val++(e b).val,
    by rw [List.length_append]; exact Nat.add_pos_left (e a).property.1 _,h⟩

@[simp] theorem concatenateNormal_word (a b : C)
    (h : ((e a).val++(e b).val).IsChain R) :
    (e (concatenateNormal e a b h)).val=(e a).val++(e b).val := by
  exact congrArg (fun W : PositiveWord R => W.val)
    (e.apply_symm_apply _)

def normalMerge : ℕ → List C → Option (List C)
  | 0,a::b::L => if h : ((e a).val++(e b).val).IsChain R
      then some (concatenateNormal e a b h::L) else none
  | 0,_ => none
  | i+1,a::L => (normalMerge i L).map (a::·)
  | _+1,[] => none

theorem normalMerge_map (i : ℕ) (L M : List C)
    (h : normalMerge e i L=some M) :
    M.map (fun a ↦ (e a).val)=mergeAdjacent (·++·) i (L.map (fun a ↦ (e a).val)) := by
  induction i generalizing L M with
  | zero =>
    cases L with
    | nil => simp only [normalMerge] at h; cases h
    | cons a L =>
      cases L with
      | nil => simp only [normalMerge] at h; cases h
      | cons b L =>
        by_cases hab : ((e a).val++(e b).val).IsChain R
        · rw [normalMerge,dif_pos hab] at h
          cases h
          simp only [List.map_cons,mergeAdjacent,concatenateNormal_word]
        · rw [normalMerge,dif_neg hab] at h
          cases h
  | succ i ih =>
    cases L with
    | nil => simp only [normalMerge] at h; cases h
    | cons a L =>
      cases he : normalMerge e i L with
      | none => simp only [normalMerge,he,Option.map_none] at h; cases h
      | some T =>
        simp only [normalMerge,he,Option.map_some,Option.some.injEq] at h
        subst M
        simp only [List.map_cons,mergeAdjacent,ih L T he]

theorem normalMerge_length (i : ℕ) (L M : List C)
    (h : normalMerge e i L=some M) (hi : i+1<L.length) :
    M.length+1=L.length := by
  have hm := normalMerge_map e i L M h
  have hlen := congrArg List.length hm
  have hj : i+1<(L.map (fun a ↦ (e a).val)).length := by
    simpa only [List.length_map] using hi
  have he := mergeAdjacent_length (·++·) i (L.map (fun a ↦ (e a).val)) hj
  simpa only [List.length_map,←hlen] using he

theorem normalMerge_exists_iff (i : ℕ) (L : List C) (hi : i+1<L.length) :
    (∃ M,normalMerge e i L=some M) ↔
      ∀ T∈mergeAdjacent (·++·) i (L.map (fun a ↦ (e a).val)),T.IsChain R := by
  constructor
  · rintro ⟨M,hM⟩ T hT
    rw [←normalMerge_map e i L M hM] at hT
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hT
    exact (e a).property.2
  · intro h
    induction i generalizing L with
    | zero =>
      cases L with
      | nil => simp only [List.length_nil] at hi; omega
      | cons a L =>
        cases L with
        | nil => simp only [List.length_cons,List.length_nil] at hi; omega
        | cons b L =>
          have hab : ((e a).val++(e b).val).IsChain R :=
            h _ (by simp only [List.map_cons,mergeAdjacent]; exact List.mem_cons_self)
          exact ⟨concatenateNormal e a b hab::L,by rw [normalMerge,dif_pos hab]⟩
    | succ i ih =>
      cases L with
      | nil => simp only [List.length_nil] at hi; omega
      | cons a L =>
        have hi' : i+1<L.length := by simp only [List.length_cons] at hi; omega
        have h' : ∀ T∈mergeAdjacent (·++·) i (L.map (fun a ↦ (e a).val)),T.IsChain R := by
          intro T hT
          apply h T
          exact List.mem_cons_of_mem _ hT
        obtain ⟨M,hM⟩ := ih L hi' h'
        exact ⟨a::M,by simp only [normalMerge,hM,Option.map_some]⟩

theorem normalMerge_optional (W : List J) (r : ℕ) (L : ActualBarIndex e W r)
    (i : ℕ) (hi : i+1<L.val.length) :
    (∃ M,normalMerge e i L.val=some M) ↔
      (factorizationComposition W (actualFactorization e W r L).val.val).boundary
        ⟨i+1,by
          simpa only [factorizationComposition,Composition.length,actualFactorization,
            List.length_map] using Nat.lt_succ_of_lt hi⟩∉mandatoryCuts R W := by
  rw [normalMerge_exists_iff e i L.val hi]
  exact merge_admissible_iff_optional R W (actualFactorization e W r L).val i
    (by simpa only [actualFactorization,List.length_map] using hi)

variable {K : Type*} [CommRing K]

def normalProduct (a b : C) : C →₀ K :=
  if h : ((e a).val++(e b).val).IsChain R
    then Finsupp.single (concatenateNormal e a b h) 1 else 0

def optionalSingle (M : Option (List C)) : List C →₀ K :=
  M.elim 0 (fun L ↦ Finsupp.single L 1)

theorem adjacent_normalProduct (i : ℕ) (L : List C) :
    adjacent (normalProduct (K := K) e) i L=optionalSingle (normalMerge e i L) := by
  induction i generalizing L with
  | zero =>
    cases L with
    | nil => rfl
    | cons a L =>
      cases L with
      | nil => rfl
      | cons b L =>
        by_cases h : ((e a).val++(e b).val).IsChain R
        · simp only [adjacent,normalProduct,normalMerge,dif_pos h,appendTail_single,
            optionalSingle,Option.elim_some]
        · simp only [adjacent,normalProduct,normalMerge,dif_neg h,map_zero,
            optionalSingle,Option.elim_none]
  | succ i ih =>
    cases L with
    | nil => rfl
    | cons a L =>
      rw [adjacent,normalMerge,ih]
      cases normalMerge e i L <;> simp only [optionalSingle,Option.map_none,
        Option.map_some,Option.elim_none,Option.elim_some,map_zero,prefix_single]

def barWordMap (W : List J) (r : ℕ) :
    (BarIndex R W r →₀ K) →ₗ[K] (List C →₀ K) :=
  Finsupp.lmapDomain K K (fun L ↦ factorizationBarWord e W L.val)

@[simp] theorem barWordMap_single (W : List J) (r : ℕ)
    (L : BarIndex R W r) (c : K) :
    barWordMap e W r (Finsupp.single L c)=
      Finsupp.single (factorizationBarWord e W L.val) c := by
  simp only [barWordMap,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]

theorem barWordMap_injective (W : List J) (r : ℕ) :
    Function.Injective (barWordMap (K := K) e W r) := by
  apply Finsupp.mapDomain_injective
  intro L M h
  apply (actualBarIndexEquiv e W r).symm.injective
  apply Subtype.ext
  change factorizationBarWord e W L.val = factorizationBarWord e W M.val
  exact h

end PaperVerification.QuadraticWordBar
end
end
end TAF_LiteralSource_0475

section TAF_LiteralSource_0476
/- Original module: PaperVerification.QuadraticWordBarTransport -/


/-!
# Exact transport from normal bar multiplication to cut contraction

Every normal adjacent merge is precisely an optional interior cut, with
the same output word and sign. The equality below is an identity for
the full differential, not a comparison of dimensions or possible terms.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.QuadraticWordBar

open PaperVerification.AlternatingForms.BarCompositions

open PaperVerification.AlternatingForms.BarCoefficientFormula

variable {K C J : Type*} [CommRing K] 
  {R : J → J → Prop} (e : C ≃ PositiveWord R)

theorem adjacent_normalProduct_cut (W : List J) (r : ℕ)
    (L : ActualBarIndex e W (r+1))
    (j : Fin ((factorizationComposition W (actualFactorization e W (r+1) L).val.val).length+1))
    (hj : (factorizationComposition W (actualFactorization e W (r+1) L).val.val).boundary j∉
      mandatoryCuts R W) :
    adjacent (normalProduct (K := K) e) (j.val-1) L.val=
      barWordMap (K := K) e W r (Finsupp.single
        (mergedBarIndex R W r (actualFactorization e W (r+1) L) j hj) 1) := by
  have hb := optional_boundary_index_bounds R W
    (actualFactorization e W (r+1) L).val j hj
  have hi : j.val-1+1<L.val.length := by
    simpa only [actualFactorization,List.length_map] using
      (show j.val-1+1<(actualFactorization e W (r+1) L).val.val.val.length by omega)
  have hj' := hj
  have he : j.val-1+1=j.val := by omega
  have ho : ∃ M,normalMerge e (j.val-1) L.val=some M := by
    apply (normalMerge_optional e W (r+1) L (j.val-1) hi).mpr
    have hindex : (⟨j.val-1+1, by
        simpa only [factorizationComposition,Composition.length,actualFactorization,
          List.length_map] using Nat.lt_succ_of_lt hi⟩ :
        Fin ((factorizationComposition W
          (actualFactorization e W (r+1) L).val.val).length+1)) = j := by
      apply Fin.ext
      exact he
    exact hindex.symm ▸ hj'
  obtain ⟨M,hM⟩ := ho
  rw [adjacent_normalProduct,hM,optionalSingle,Option.elim_some,barWordMap_single]
  congr 1
  apply (List.map_injective_iff.mpr
    (show Function.Injective (fun a : C ↦ (e a).val) from
      fun a b hab ↦ e.injective (Subtype.ext hab)))
  rw [factorizationBarWord_map]
  exact normalMerge_map e (j.val-1) L.val M hM

theorem adjacent_normalProduct_zero_of_mandatory (W : List J) (r : ℕ)
    (L : ActualBarIndex e W r) (i : ℕ) (hi : i+1<L.val.length)
    (hj : (factorizationComposition W (actualFactorization e W r L).val.val).boundary
      ⟨i+1,by
        simpa only [factorizationComposition,Composition.length,actualFactorization,
          List.length_map] using Nat.lt_succ_of_lt hi⟩∈mandatoryCuts R W) :
    adjacent (normalProduct (K := K) e) i L.val=0 := by
  have hnone : normalMerge e i L.val=none := by
    cases hm : normalMerge e i L.val with
    | none => rfl
    | some M =>
      have ho := (normalMerge_optional e W r L i hi).mp ⟨M,hm⟩
      exact False.elim (ho hj)
  rw [adjacent_normalProduct,hnone]
  rfl

theorem sum_interior_bar_signs {M : Type*} [AddCommGroup M] (r : ℕ) (f : ℕ → M) :
    (∑ j∈Finset.range (r+2),if 0<j ∧ j<r+1 then (-1 : ℤˣ)^j • f (j-1) else 0)=
      ∑ i∈Finset.range r,(-1 : ℤˣ)^(i+1) • f i := by
  rw [Finset.sum_range_succ]
  simp only [lt_self_iff_false,and_false,if_false,add_zero]
  rw [Finset.sum_range_succ']
  simp only [Nat.lt_irrefl,false_and,if_false,add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < r := Finset.mem_range.mp hi
  rw [if_pos (by constructor <;> omega),Nat.add_sub_cancel]

set_option maxHeartbeats 800000 in
/-- The actual tensor sign convention is the negative of the recursive
positive-first-merge convention. Endpoints contribute zero because they
are mandatory, and every interior optional cut is retained. -/
theorem cutDifferential_transport_basis (W : List J) (r : ℕ)
    (L : ActualBarIndex e W (r+1)) :
    barWordMap (K := K) e W r
      (cutModelDifferential (K := K) R W r
        (Finsupp.single (actualFactorization e W (r+1) L) 1))=
      -basisDifferential (normalProduct (K := K) e) L.val := by
  let A := actualFactorization e W (r+1) L
  let c := factorizationComposition W A.val.val
  have hc : c.length=L.val.length := by
    simp only [c,A,factorizationComposition,Composition.length,actualFactorization,
      List.length_map]
  rw [cutModelDifferential_single_merges,map_sum,negative_basisDifferential_expansion]
  calc
    (∑ j : Fin (c.length+1),barWordMap (K := K) e W r
      (if hj : c.boundary j∉mandatoryCuts R W
        then (-1 : ℤˣ)^j.val • Finsupp.single (mergedBarIndex R W r A j hj) (1 : K)
        else 0)) =
      ∑ j : Fin (c.length+1),if 0<j.val ∧ j.val<L.val.length
        then (-1 : ℤˣ)^j.val • adjacent (normalProduct (K := K) e) (j.val-1) L.val else 0 := by
      apply Finset.sum_congr rfl
      intro j hjmem
      by_cases hb : 0<j.val ∧ j.val<L.val.length
      · rw [if_pos hb]
        by_cases hj : c.boundary j∉mandatoryCuts R W
        · rw [dif_pos hj,map_zsmul_unit,←adjacent_normalProduct_cut e W r L j hj]
        · rw [dif_neg hj,map_zero]
          have hi : j.val-1+1<L.val.length := by omega
          have hm : c.boundary
              ⟨j.val-1+1,by omega⟩∈mandatoryCuts R W := by
            convert not_not.mp hj using 1
            congr 1
            apply Fin.ext
            change j.val-1+1=j.val
            omega
          rw [adjacent_normalProduct_zero_of_mandatory e W (r+1) L
            (j.val-1) hi hm,smul_zero]
      · have hj : ¬c.boundary j∉mandatoryCuts R W := by
          intro hj
          have hp := optional_boundary_index_bounds R W A.val j hj
          apply hb
          exact ⟨hp.1,by simpa only [A,actualFactorization,List.length_map] using hp.2⟩
        rw [dif_neg hj,if_neg hb,map_zero]
    _ = ∑ j∈Finset.range (c.length+1),if 0<j ∧ j<L.val.length
        then (-1 : ℤˣ)^j • adjacent (normalProduct (K := K) e) (j-1) L.val else 0 :=
      Fin.sum_univ_eq_sum_range
        (fun j : ℕ => if 0<j ∧ j<L.val.length then
          (-1 : ℤˣ)^j • adjacent (normalProduct (K := K) e) (j-1) L.val else 0)
        (c.length+1)
    _ = ∑ i∈Finset.range (L.val.length-1),
        (-1 : ℤˣ)^(i+1) • adjacent (normalProduct (K := K) e) i L.val := by
      rw [hc,L.property.2,Nat.add_sub_cancel]
      simpa only [Nat.add_assoc] using sum_interior_bar_signs r
        (fun i => adjacent (normalProduct (K := K) e) i L.val)

end PaperVerification.QuadraticWordBar
end
end
end TAF_LiteralSource_0476

section TAF_LiteralSource_0477
/- Original module: PaperVerification.QuadraticWordBarCoordinates -/


/-!
# The cut decomposition in literal tensor coordinates

The inclusion of a fixed-word fiber sends each factorization to its
actual positive-basis tensor word. Its coordinates are a single outer
fiber. Consequently the leading degree differential has exactly the
normal adjacent-merge formula on each original tensor basis vector.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace PaperVerification.QuadraticWordBar

open PaperVerification.AlternatingForms.BarCompositions

open PaperVerification.AlternatingForms.BarCoefficientFormula

variable {K C J : Type*} [CommRing K] [Fintype J]
  {R : J → J → Prop} (e : C ≃ PositiveWord R)

theorem internalDegreeFiberCoordinates_apply (r N : ℕ)
    (z : internalDegreePiece (K := K) e r N)
    (W : {W : List J // W.length=N}) (L : BarIndex R W.val r) :
    internalDegreeFiberCoordinates e r N z W L=
      z.val (factorizationBarWord e W.val L.val) := by
  rfl

theorem factorizationBarWord_injective (W : List J) (r : ℕ) :
    Function.Injective (fun L : BarIndex R W r ↦ factorizationBarWord e W L.val) := by
  intro L M h
  apply (actualBarIndexEquiv e W r).symm.injective
  apply Subtype.ext
  change factorizationBarWord e W L.val = factorizationBarWord e W M.val
  exact h

theorem barWordMap_mem_internalDegree (r N : ℕ)
    (W : {W : List J // W.length=N}) (z : BarIndex R W.val r →₀ K) :
    barWordMap e W.val r z∈internalDegreePiece (K := K) e r N := by
  induction z using Finsupp.induction_linear with
  | zero => simpa only [map_zero] using (internalDegreePiece (K := K) e r N).zero_mem
  | add z w hz hw => simpa only [map_add] using
      (internalDegreePiece (K := K) e r N).add_mem hz hw
  | single L c =>
    rw [barWordMap_single]
    apply Finsupp.single_mem_supported K c
    exact ⟨(factorizationBarWord_length e W.val L.val).trans L.property,
      by rw [factorizationBarWord_flatten]; exact W.property⟩

def fiberInclusion (r N : ℕ) (W : {W : List J // W.length=N}) :
    (BarIndex R W.val r →₀ K) →ₗ[K] internalDegreePiece (K := K) e r N :=
  LinearMap.codRestrict _ (barWordMap e W.val r) (barWordMap_mem_internalDegree e r N W)

@[simp] theorem fiberInclusion_val (r N : ℕ) (W : {W : List J // W.length=N})
    (z : BarIndex R W.val r →₀ K) :
    (fiberInclusion e r N W z).val=barWordMap e W.val r z := rfl

theorem internalDegreeFiberCoordinates_fiberInclusion (r N : ℕ)
    (W : {W : List J // W.length=N}) (z : BarIndex R W.val r →₀ K) :
    internalDegreeFiberCoordinates e r N (fiberInclusion e r N W z)=Pi.single W z := by
  funext V
  ext L
  rw [internalDegreeFiberCoordinates_apply]
  change (Finsupp.mapDomain (fun T : BarIndex R W.val r ↦
    factorizationBarWord e W.val T.val) z) (factorizationBarWord e V.val L.val)=_
  by_cases h : V=W
  · subst V
    rw [Finsupp.mapDomain_apply_of_injective (factorizationBarWord_injective e W.val r),
      Pi.single_eq_same]
  · have hn : factorizationBarWord e V.val L.val∉
        Set.range (fun T : BarIndex R W.val r ↦ factorizationBarWord e W.val T.val) := by
      rintro ⟨T,hT⟩
      apply h
      apply Subtype.ext
      have hh := congrArg (flattenBarWord e) hT
      rw [factorizationBarWord_flatten,factorizationBarWord_flatten] at hh
      exact hh.symm
    rw [Finsupp.mapDomain_of_notMem_range _ _ hn,Pi.single_eq_of_ne h,Finsupp.zero_apply]

set_option maxHeartbeats 800000 in
theorem leadingDegreeDifferential_fiberInclusion (r N : ℕ)
    (W : {W : List J // W.length=N}) (z : BarIndex R W.val (r+1) →₀ K) :
    leadingDegreeDifferential e r N (fiberInclusion e (r+1) N W z)=
      fiberInclusion e r N W (cutModelDifferential R W.val r z) := by
  apply (internalDegreeFiberCoordinates e r N).injective
  rw [leadingDegreeDifferential_comm,internalDegreeFiberCoordinates_fiberInclusion,
    internalDegreeFiberCoordinates_fiberInclusion]
  funext V
  rw [leadingFiberDifferential_apply (K := K) (J := J) (R := R)]
  by_cases h : V=W
  · subst V
    simp only [Pi.single_eq_same]
  · simp only [Pi.single_eq_of_ne h,map_zero]

def tensorBasis (r N : ℕ) :
    Module.Basis (InternalDegreeIndex e r N) K (internalDegreePiece (K := K) e r N) :=
  .ofRepr (internalDegreeCoordinates e r N)

@[simp] theorem tensorBasis_val (r N : ℕ) (L : InternalDegreeIndex e r N) :
    (tensorBasis (K := K) e r N L).val=Finsupp.single L.val 1 := by
  change ((Finsupp.supportedEquivFinsupp (M := K) (R := K)
    {T : List C | T.length=r ∧ (flattenBarWord e T).length=N}).symm
      (Finsupp.single L 1)).val=Finsupp.single L.val 1
  exact Finsupp.supportedEquivFinsupp_symm_single _ _ _

@[simp] theorem tensorBasis_repr_apply (r N : ℕ)
    (z : internalDegreePiece (K := K) e r N) (L : InternalDegreeIndex e r N) :
    (tensorBasis e r N).repr z L=z.val L.val := rfl

theorem tensorBasis_repr_sub (r N : ℕ)
    (x y : internalDegreePiece (K := K) e r N) (L : InternalDegreeIndex e r N) :
    (tensorBasis e r N).repr (x-y) L=x.val L.val-y.val L.val := rfl

theorem tensorBasis_eq_fiberInclusion (r N : ℕ) (L : InternalDegreeIndex e r N) :
    tensorBasis (K := K) e r N L=
      fiberInclusion e r N ⟨flattenBarWord e L.val,L.property.2⟩
        (Finsupp.single (actualFactorization e (flattenBarWord e L.val) r
          ⟨L.val,rfl,L.property.1⟩) 1) := by
  apply Subtype.ext
  rw [tensorBasis_val,fiberInclusion_val,barWordMap_single]
  congr 1
  have h := (actualBarIndexEquiv e (flattenBarWord e L.val) r).left_inv
    ⟨L.val,rfl,L.property.1⟩
  have hw := congrArg
    (fun T : ActualBarIndex e (flattenBarWord e L.val) r => T.val) h
  exact hw.symm

/-- Coordinates of the leading operator on every original tensor. -/
theorem leadingDegreeDifferential_tensorBasis_val (r N : ℕ)
    (L : InternalDegreeIndex e (r+1) N) :
    (leadingDegreeDifferential e r N (tensorBasis (K := K) e (r+1) N L)).val=
      -basisDifferential (normalProduct e) L.val := by
  rw [tensorBasis_eq_fiberInclusion,leadingDegreeDifferential_fiberInclusion,
    fiberInclusion_val]
  exact cutDifferential_transport_basis e (flattenBarWord e L.val) r
    ⟨L.val,rfl,L.property.1⟩

end PaperVerification.QuadraticWordBar
end
end
end TAF_LiteralSource_0477

section TAF_LiteralSource_0478
/- Original module: PaperVerification.NoncommutativeBarFree -/


/-!
# The normalized free bar differential over an arbitrary augmented ring

The free module is indexed by words in the positive basis. Its differential
has the actual left multiplication term and the actual adjacent-product terms.
All coefficients come from the supplied algebra and its unit-plus-augmentation
basis; no differential identity or homological exactness is assumed.
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace PaperVerification.NoncommutativeBar

open PaperVerification.AugmentedAlgebraBasis

variable {K A I : Type*} [CommRing K] [Ring A] [Algebra K A]
  (ε : A →ₐ[K] K) (B : Module.Basis (Option I) K A)
  (hunit : B none=1) (hε : ∀ i,ε (B (some i))=0)

abbrev Words (I A : Type*) [Zero A] := List I →₀ A

/-- Extension of word coefficients along the actual algebra map. -/
def lift : Words I K →ₗ[K] Words I A :=
  Finsupp.linearCombination K (fun L ↦ Finsupp.single L 1)

@[simp] theorem lift_single (L : List I) (c : K) :
    lift (A := A) (Finsupp.single L c)=c • Finsupp.single L 1 :=
  Finsupp.linearCombination_single _ _ _

def prepend (i : I) : Words I A →ₗ[A] Words I A :=
  Finsupp.lmapDomain A A (List.cons i)

@[simp] theorem prefix_single (i : I) (L : List I) (a : A) :
    prepend i (Finsupp.single L a)=Finsupp.single (i::L) a := by
  simp [prepend]

def frontBasis : List I → Words I A
  | [] => 0
  | i::L => Finsupp.single L (positiveVector B i)

/-- The term that multiplies the free coefficient by the first bar factor. -/
def front : Words I A →ₗ[A] Words I A :=
  Finsupp.linearCombination A (frontBasis B)

@[simp] theorem front_single (L : List I) (a : A) :
    front B (Finsupp.single L a)=a • frontBasis B L :=
  Finsupp.linearCombination_single _ _ _

/-- The scalar extension of the actual positive-basis adjacent-product differential. -/
def internal : Words I A →ₗ[A] Words I A :=
  Finsupp.linearCombination A (fun L ↦
    lift (PaperVerification.ReducedBarBasis.differentialBasis B L))

@[simp] theorem internal_single (L : List I) (a : A) :
    internal B (Finsupp.single L a)=
      a • lift (PaperVerification.ReducedBarBasis.differentialBasis B L) :=
  Finsupp.linearCombination_single _ _ _

theorem lift_prefix (i : I) (z : Words I K) :
    lift (PaperVerification.ReducedBarBasis.prepend i z)=
      prepend i (lift (A := A) z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add z w hz hw => simp only [map_add,hz,hw]
  | single L c =>
    simp only [PaperVerification.ReducedBarBasis.prefix_single,lift_single,
      LinearMap.map_smul_of_tower,prefix_single]

theorem internal_lift (z : Words I K) :
    internal B (lift z)=lift (PaperVerification.ReducedBarBasis.differential B z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add z w hz hw => simp only [map_add,hz,hw]
  | single L c =>
    simp only [lift_single,LinearMap.map_smul_of_tower,internal_single,one_smul,
      PaperVerification.ReducedBarBasis.differential_single,map_smul]

theorem front_lift_prefix (i : I) (z : Words I K) :
    front B (lift (PaperVerification.ReducedBarBasis.prepend i z))=
      positiveVector B i • lift z := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero,smul_zero]
  | add z w hz hw => simp only [map_add,smul_add,hz,hw]
  | single L c =>
    simp only [PaperVerification.ReducedBarBasis.prefix_single,lift_single,
      LinearMap.map_smul_of_tower,front_single,frontBasis,one_smul]
    rw [smul_comm]
    congr 1
    simp only [Finsupp.smul_single,smul_eq_mul,mul_one]

theorem front_lift_appendTail (L : List I) (c : I →₀ K) :
    front B (lift (PaperVerification.ReducedBarBasis.appendTail L c))=
      Finsupp.single L (positiveCombination B c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero,Finsupp.single_zero]
  | add c d hc hd => simp only [map_add,Finsupp.single_add,hc,hd]
  | single i c =>
    simp only [PaperVerification.ReducedBarBasis.appendTail_single,lift_single,
      LinearMap.map_smul_of_tower,front_single,frontBasis,one_smul,
      positiveCombination,Finsupp.linearCombination_single,Finsupp.smul_single,
      smul_assoc,one_smul]

include hunit hε in
theorem front_lift_merge (i : I) (z : Words I K) :
    front B (lift (PaperVerification.ReducedBarBasis.merge B i z))=
      positiveVector B i • front B (lift z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero,smul_zero]
  | add z w hz hw => simp only [map_add,smul_add,hz,hw]
  | single L c =>
    cases L with
    | nil =>
      simp only [PaperVerification.ReducedBarBasis.merge_single,
        PaperVerification.ReducedBarBasis.mergeBasis,smul_zero,map_zero,
        lift_single,LinearMap.map_smul_of_tower,front_single,frontBasis]
    | cons j L =>
      simp only [PaperVerification.ReducedBarBasis.merge_single,
        PaperVerification.ReducedBarBasis.mergeBasis,map_smul,
        LinearMap.map_smul_of_tower,front_lift_appendTail,
        product_expansion ε B hunit hε,lift_single,front_single,frontBasis,one_smul]
      rw [smul_comm]
      congr 1
      simp only [Finsupp.smul_single,smul_eq_mul]

include hunit hε in
theorem internal_squared (z : Words I A) : internal B (internal B z)=0 := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add z w hz hw => simp only [map_add,hz,hw,add_zero]
  | single L a =>
    rw [internal_single,map_smul,internal_lift,
      PaperVerification.ReducedBarBasis.differentialBasis_squared ε B hunit hε,
      map_zero,smul_zero]

include hunit hε in
/-- The first multiplication term and the internal terms satisfy the identity
that leaves exactly the square of the first multiplication term. -/
theorem front_internal (z : Words I A) :
    front B (internal B z)+internal B (front B z)=front B (front B z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero,add_zero]
  | add z w hz hw =>
    simp only [map_add]
    rw [show front B (internal B z)+front B (internal B w)+
      (internal B (front B z)+internal B (front B w))=
      (front B (internal B z)+internal B (front B z))+
      (front B (internal B w)+internal B (front B w)) by abel,hz,hw]
  | single L a =>
    have h : front B (internal B (Finsupp.single L 1))+
        internal B (front B (Finsupp.single L 1))=
        front B (front B (Finsupp.single L 1)) := by
      cases L with
      | nil =>
        simp only [internal_single,PaperVerification.ReducedBarBasis.differentialBasis,
          front_single,frontBasis,map_zero,smul_zero,add_zero]
      | cons i L =>
        simp only [internal_single,one_smul,
          PaperVerification.ReducedBarBasis.differentialBasis,map_sub,
          front_lift_merge ε B hunit hε,front_lift_prefix,
          front_single,frontBasis,map_smul,internal_single,one_smul,lift_single,
          LinearMap.map_smul_of_tower]
        abel
    have ha : Finsupp.single L a=a • (Finsupp.single L 1 : Words I A) := by
      simp only [Finsupp.smul_single,smul_eq_mul,mul_one]
    rw [ha]
    simp only [map_smul,←smul_add,h]

/-- The genuine normalized free bar differential, with the standard signs. -/
def differential : Words I A →ₗ[A] Words I A := front B-internal B

include hunit hε in
theorem differential_squared (z : Words I A) :
    differential B (differential B z)=0 := by
  change front B (front B z-internal B z)-
    internal B (front B z-internal B z)=0
  rw [map_sub,map_sub,internal_squared ε B hunit hε,sub_zero]
  have h := front_internal ε B hunit hε z
  rw [←h]
  abel

/-- The positive-part prepend used in the actual contracting homotopy. -/
def positivePrefix (L : List I) : A →ₗ[K] Words I A :=
  (Finsupp.linearCombination K (fun i ↦ Finsupp.single (i::L) 1)).comp
    (positiveCoordinates B)

/-- This map increases bar length by one and is K-linear, as a contraction
of a free A-resolution should be. It is not asserted to be A-linear. -/
def homotopy : Words I A →ₗ[K] Words I A :=
  Finsupp.lsum K (positivePrefix B)

@[simp] theorem homotopy_single (L : List I) (a : A) :
    homotopy B (Finsupp.single L a)=
      Finsupp.linearCombination K (fun i ↦ Finsupp.single (i::L) 1)
        (positiveCoordinates B a) := by
  simp only [homotopy,Finsupp.lsum_single,positivePrefix,LinearMap.comp_apply]

include hunit in
@[simp] theorem homotopy_single_one (L : List I) :
    homotopy B (Finsupp.single L (1 : A))=0 := by
  rw [homotopy_single,positiveCoordinates_one B hunit,map_zero]

@[simp] theorem homotopy_single_positive (L : List I) (i : I) :
    homotopy B (Finsupp.single L (positiveVector B i))=Finsupp.single (i::L) 1 := by
  rw [homotopy_single,positiveCoordinates_vector,
    Finsupp.linearCombination_single,one_smul]

/-- Scalar extension of multiplication of the first positive tensor factor. -/
def merge (i : I) : Words I A →ₗ[A] Words I A :=
  Finsupp.linearCombination A (fun L ↦
    lift (PaperVerification.ReducedBarBasis.mergeBasis B i L))

@[simp] theorem merge_single (i : I) (L : List I) (a : A) :
    merge B i (Finsupp.single L a)=
      a • lift (PaperVerification.ReducedBarBasis.mergeBasis B i L) :=
  Finsupp.linearCombination_single _ _ _

/-- The first face on a unit-coefficient word.  This is stated with its
actual coefficient restriction; arbitrary coefficients multiply on the
right and cannot be moved past a bar factor in a noncommutative algebra. -/
theorem front_prefix (i : I) (L : List I) :
    front B (prepend i (Finsupp.single L 1))=
      positiveVector B i • (Finsupp.single L 1 : Words I A) := by
  simp only [prefix_single,front_single,frontBasis,one_smul,
    Finsupp.smul_single,smul_eq_mul,mul_one]

theorem internal_prefix (i : I) (z : Words I A) :
    internal B (prepend i z)=merge B i z-prepend i (internal B z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero,sub_zero]
  | add z w hz hw => simp only [map_add,hz,hw]; abel
  | single L a =>
    simp only [prefix_single,internal_single,
      PaperVerification.ReducedBarBasis.differentialBasis,map_sub,
      PaperVerification.ReducedBarBasis.merge_single,one_smul,
      lift_prefix,smul_sub,merge_single,map_smul]

def positivePrefixMap (a : A) : Words I A →ₗ[K] Words I A :=
  Finsupp.linearCombination K (fun i ↦ (prepend (A := A) i).restrictScalars K)
    (positiveCoordinates B a)

def positiveMergeMap (a : A) : Words I A →ₗ[K] Words I A :=
  Finsupp.linearCombination K (fun i ↦ (merge B i).restrictScalars K)
    (positiveCoordinates B a)

theorem homotopy_single_eq_prefix (L : List I) (a : A) :
    homotopy B (Finsupp.single L a)=
      positivePrefixMap B a (Finsupp.single L 1) := by
  simp only [homotopy_single,positivePrefixMap,Finsupp.linearCombination_apply,
    Finsupp.sum,LinearMap.sum_apply,LinearMap.smul_apply,
    LinearMap.restrictScalars_apply,prefix_single]

theorem homotopy_smul_lift (a : A) (z : Words I K) :
    homotopy B (a • lift z)=positivePrefixMap B a (lift z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero,smul_zero]
  | add z w hz hw => simp only [map_add,smul_add,hz,hw]
  | single L c =>
    calc
      homotopy B (a • lift (Finsupp.single L c)) =
          homotopy B (c • (a • (Finsupp.single L 1 : Words I A))) := by
        rw [lift_single,smul_comm a c]
      _ = c • homotopy B (Finsupp.single L a) := by
        rw [map_smul]
        congr 1
        simp only [Finsupp.smul_single,smul_eq_mul,mul_one]
      _ = c • positivePrefixMap B a (Finsupp.single L 1) := by
        rw [homotopy_single_eq_prefix]
      _ = positivePrefixMap B a (lift (Finsupp.single L c)) := by
        rw [lift_single,map_smul]

theorem front_positivePrefixMap (a : A) (L : List I) :
    front B (positivePrefixMap B a (Finsupp.single L 1))=
      positiveCombination B (positiveCoordinates B a) • (Finsupp.single L 1 : Words I A) := by
  simp only [positivePrefixMap,Finsupp.linearCombination_apply,Finsupp.sum,
    LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.restrictScalars_apply,
    map_sum,LinearMap.map_smul_of_tower,front_prefix,positiveCombination_apply,
    Finset.sum_smul,smul_assoc]

theorem internal_positivePrefixMap (a : A) (z : Words I A) :
    internal B (positivePrefixMap B a z)=
      positiveMergeMap B a z-positivePrefixMap B a (internal B z) := by
  simp only [positivePrefixMap,positiveMergeMap,Finsupp.linearCombination_apply,
    Finsupp.sum,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.restrictScalars_apply,
    map_sum,LinearMap.map_smul_of_tower,internal_prefix,smul_sub,Finset.sum_sub_distrib]

include hunit hε in
theorem front_positivePrefixMap_add_scalar (a : A) (L : List I) :
    front B (positivePrefixMap B a (Finsupp.single L 1))+
      ε a • (Finsupp.single L 1 : Words I A)=a • Finsupp.single L 1 := by
  rw [front_positivePrefixMap]
  have h := congrArg (fun x : A ↦ x • (Finsupp.single L 1 : Words I A))
    (scalar_add_positive ε B hunit hε a)
  simp only [add_smul,smul_assoc,one_smul] at h
  simpa only [add_comm] using h

theorem lift_appendTail (L : List I) (c : I →₀ K) :
    lift (A := A) (PaperVerification.ReducedBarBasis.appendTail L c)=
      Finsupp.linearCombination K (fun i ↦ Finsupp.single (i::L) (1 : A)) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => simp only [map_add,hc,hd]
  | single i c =>
    simp only [PaperVerification.ReducedBarBasis.appendTail_single,lift_single,
      Finsupp.linearCombination_single]

include hunit hε in
/-- The coefficient splitting of a product gives exactly the two terms that
cancel the first adjacent multiplication in the homotopy identity. -/
theorem homotopy_front_cons (a : A) (i : I) (L : List I) :
    homotopy B (front B (Finsupp.single (i::L) a))=
      ε a • Finsupp.single (i::L) 1+
        positiveMergeMap B a (Finsupp.single (i::L) 1) := by
  rw [front_single]
  change homotopy B (a • Finsupp.single L (positiveVector B i))=_
  rw [Finsupp.smul_single]
  change homotopy B (Finsupp.single L (a*positiveVector B i))=_
  rw [homotopy_single,positiveCoordinates_mul_vector ε B hunit hε,
    map_add,map_smul,Finsupp.linearCombination_single]
  simp only [Finsupp.sum,map_sum,map_smul,positiveMergeMap,
    Finsupp.linearCombination_apply,LinearMap.sum_apply,LinearMap.smul_apply,
    LinearMap.restrictScalars_apply,merge_single,one_smul,
    PaperVerification.ReducedBarBasis.mergeBasis,lift_appendTail]

theorem positiveMergeMap_nil (a : A) :
    positiveMergeMap B a (Finsupp.single [] (1 : A))=0 := by
  simp only [positiveMergeMap,Finsupp.linearCombination_apply,Finsupp.sum,
    LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.restrictScalars_apply,
    merge_single,PaperVerification.ReducedBarBasis.mergeBasis,map_zero,smul_zero,
    Finset.sum_const_zero]

/-- Augmentation followed by the degree-zero unit inclusion. -/
def augmentationProjection : Words I A →ₗ[K] Words I A :=
  (ε.toLinearMap.smulRight (Finsupp.single [] (1 : A))).comp
    (Finsupp.lapply [])

@[simp] theorem augmentationProjection_nil (a : A) :
    augmentationProjection (I := I) ε (Finsupp.single [] a)=
      ε a • Finsupp.single [] 1 := by
  simp [augmentationProjection]

@[simp] theorem augmentationProjection_cons (i : I) (L : List I) (a : A) :
    augmentationProjection ε (Finsupp.single (i::L) a)=0 := by
  simp [augmentationProjection]

include hunit hε in
/-- The explicit K-linear contraction of the augmented normalized free bar
complex. Together with the length restriction, this proves actual exactness. -/
theorem contracting_identity (z : Words I A) :
    differential B (homotopy B z)+homotopy B (differential B z)+
      augmentationProjection ε z=z := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero,add_zero]
  | add z w hz hw =>
    simp only [map_add]
    calc
      _ = (differential B (homotopy B z)+homotopy B (differential B z)+
          augmentationProjection ε z)+
        (differential B (homotopy B w)+homotopy B (differential B w)+
          augmentationProjection ε w) := by abel
      _ = _ := by rw [hz,hw]
  | single L a =>
    cases L with
    | nil =>
      rw [homotopy_single_eq_prefix,augmentationProjection_nil]
      have hd : differential B (Finsupp.single [] a)=0 := by
        simp only [differential,LinearMap.sub_apply,front_single,frontBasis,
          internal_single,PaperVerification.ReducedBarBasis.differentialBasis,
          map_zero,smul_zero,sub_zero]
      rw [hd,map_zero,add_zero]
      change front B (positivePrefixMap B a (Finsupp.single [] 1))-
        internal B (positivePrefixMap B a (Finsupp.single [] 1))+
          ε a • Finsupp.single [] 1=Finsupp.single [] a
      rw [internal_positivePrefixMap,positiveMergeMap_nil,internal_single,
        PaperVerification.ReducedBarBasis.differentialBasis,map_zero,smul_zero,
        map_zero,sub_zero,sub_zero,front_positivePrefixMap_add_scalar ε B hunit hε]
      simp only [Finsupp.smul_single,smul_eq_mul,mul_one]
    | cons i L =>
      rw [homotopy_single_eq_prefix,augmentationProjection_cons,add_zero]
      have hd : homotopy B (differential B (Finsupp.single (i::L) a))=
          ε a • Finsupp.single (i::L) 1+
            positiveMergeMap B a (Finsupp.single (i::L) 1)-
            positivePrefixMap B a
              (lift (PaperVerification.ReducedBarBasis.differentialBasis B (i::L))) := by
        change homotopy B (front B (Finsupp.single (i::L) a)-
          internal B (Finsupp.single (i::L) a))=_
        rw [map_sub,homotopy_front_cons ε B hunit hε,internal_single,homotopy_smul_lift]
      rw [hd]
      change (front B (positivePrefixMap B a (Finsupp.single (i::L) 1))-
        internal B (positivePrefixMap B a (Finsupp.single (i::L) 1)))+_=_
      rw [internal_positivePrefixMap,internal_single,one_smul]
      have h := front_positivePrefixMap_add_scalar ε B hunit hε a (i::L)
      have ha : a • (Finsupp.single (i::L) 1 : Words I A)=Finsupp.single (i::L) a := by
        simp only [Finsupp.smul_single,smul_eq_mul,mul_one]
      rw [ha] at h
      calc
        _ = front B (positivePrefixMap B a (Finsupp.single (i::L) 1))+
            ε a • Finsupp.single (i::L) 1 := by abel
        _ = _ := h

end PaperVerification.NoncommutativeBar
end
end
end TAF_LiteralSource_0478

section TAF_LiteralSource_0479
/- Original module: PaperVerification.NoncommutativeBarLength -/


/-!
# Length grading and exactness of the normalized free bar construction

The length pieces are actual supported submodules of the word module. The
differential decreases length and the explicit contraction increases it.
This supplies cycle-to-boundary witnesses in every positive bar degree.
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace PaperVerification.NoncommutativeBar

open PaperVerification.AugmentedAlgebraBasis

variable {K A I : Type*} [CommRing K] [Ring A] [Algebra K A]
  (ε : A →ₐ[K] K) (B : Module.Basis (Option I) K A)
  (hunit : B none=1) (hε : ∀ i,ε (B (some i))=0)

def lengthPiece (I A : Type*) [Ring A] (r : ℕ) :
    Submodule A (Words I A) :=
  Finsupp.supported A A {L | L.length=r}

theorem single_mem_lengthPiece (L : List I) (a : A) {r : ℕ} (hL : L.length=r) :
    Finsupp.single L a ∈ lengthPiece I A r :=
  Finsupp.single_mem_supported A a hL

theorem mem_lengthPiece_iff (z : Words I A) (r : ℕ) :
    z ∈ lengthPiece I A r ↔ ∀ L : List I,L.length≠r → z L=0 :=
  Finsupp.mem_supported' A z

theorem lengthPiece_eq_span (r : ℕ) :
    lengthPiece I A r=Submodule.span A
      ((fun L : List I ↦ Finsupp.single L (1 : A)) '' {L | L.length=r}) :=
  Finsupp.supported_eq_span_single A {L : List I | L.length=r}

instance lengthPiece_free (r : ℕ) : Module.Free A (lengthPiece I A r) :=
  Module.Free.of_basis ((Module.Basis.ofRepr (LinearEquiv.refl A _) :
      Module.Basis {L : List I | L.length=r} A ({L : List I | L.length=r} →₀ A)).map
    (Finsupp.supportedEquivFinsupp (M := A) (R := A) {L : List I | L.length=r}).symm)

theorem lift_apply (z : Words I K) (L : List I) :
    lift (A := A) z L=algebraMap K A (z L) := by
  classical
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero,Finsupp.zero_apply]
  | add z w hz hw => simp only [map_add,Finsupp.add_apply,hz,hw]
  | single T c =>
    by_cases h : T=L <;>
      simp [lift_single,Finsupp.single_apply,h,Algebra.smul_def]

theorem lift_mem_lengthPiece {r : ℕ} (z : Words I K) (hz : z∈lengthPiece I K r) :
    lift (A := A) z ∈ lengthPiece I A r := by
  rw [mem_lengthPiece_iff] at hz ⊢
  intro L hL
  rw [lift_apply,hz L hL,map_zero]

theorem prefix_mem_lengthPiece (i : I) {r : ℕ} (z : Words I A)
    (hz : z∈lengthPiece I A r) : prepend i z∈lengthPiece I A (r+1) := by
  rw [lengthPiece_eq_span] at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨L,hL,rfl⟩ := hz
    change L.length=r at hL
    rw [prefix_single]
    exact single_mem_lengthPiece _ _ (by simpa only [List.length_cons,hL])
  | zero => simpa only [map_zero] using (lengthPiece I A (r+1)).zero_mem
  | add z w hz hw ihz ihw =>
    simpa only [map_add] using (lengthPiece I A (r+1)).add_mem ihz ihw
  | smul a z hz ih =>
    simpa only [map_smul] using (lengthPiece I A (r+1)).smul_mem a ih

theorem reduced_prefix_eq (i : I) :
    PaperVerification.ReducedBarBasis.prepend (K := K) i=prepend (A := K) i := by
  apply Finsupp.lhom_ext
  intro L c
  simp only [PaperVerification.ReducedBarBasis.prefix_single,prefix_single]

theorem appendTail_mem_lengthPiece (L : List I) (c : I →₀ K) :
    PaperVerification.ReducedBarBasis.appendTail L c∈lengthPiece I K (L.length+1) := by
  rw [PaperVerification.ReducedBarBasis.appendTail,Finsupp.linearCombination_apply,Finsupp.sum]
  apply Submodule.sum_mem
  intro i hi
  exact (lengthPiece I K (L.length+1)).smul_mem _
    (single_mem_lengthPiece _ _ rfl)

theorem reducedDifferentialBasis_mem_lengthPiece (L : List I) :
    PaperVerification.ReducedBarBasis.differentialBasis B L∈
      lengthPiece I K (L.length-1) := by
  induction L with
  | nil =>
    simp only [PaperVerification.ReducedBarBasis.differentialBasis]
    exact Submodule.zero_mem _
  | cons i L ih =>
    cases L with
    | nil =>
      simp only [PaperVerification.ReducedBarBasis.differentialBasis,
        PaperVerification.ReducedBarBasis.merge_single,
        PaperVerification.ReducedBarBasis.mergeBasis,smul_zero,map_zero,sub_zero]
      exact Submodule.zero_mem _
    | cons j L =>
      change PaperVerification.ReducedBarBasis.differentialBasis B (i::j::L)∈
        lengthPiece I K (L.length+1)
      rw [PaperVerification.ReducedBarBasis.differentialBasis]
      apply Submodule.sub_mem
      · rw [PaperVerification.ReducedBarBasis.merge_single,one_smul,
          PaperVerification.ReducedBarBasis.mergeBasis]
        exact appendTail_mem_lengthPiece L _
      · rw [reduced_prefix_eq]
        exact prefix_mem_lengthPiece i _
          (by simpa only [List.length_cons,Nat.add_sub_cancel] using ih)

theorem front_mem_lengthPiece {r : ℕ} (z : Words I A)
    (hz : z∈lengthPiece I A (r+1)) : front B z∈lengthPiece I A r := by
  rw [lengthPiece_eq_span] at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨L,hL,rfl⟩ := hz
    change L.length=r+1 at hL
    cases L with
    | nil => simp only [List.length_nil] at hL; omega
    | cons i L =>
      rw [front_single,one_smul]
      exact single_mem_lengthPiece _ _ (by simpa only [List.length_cons,Nat.add_right_cancel_iff] using hL)
  | zero => simpa only [map_zero] using (lengthPiece I A r).zero_mem
  | add z w hz hw ihz ihw =>
    simpa only [map_add] using (lengthPiece I A r).add_mem ihz ihw
  | smul a z hz ih =>
    simpa only [map_smul] using (lengthPiece I A r).smul_mem a ih

theorem internal_mem_lengthPiece {r : ℕ} (z : Words I A)
    (hz : z∈lengthPiece I A (r+1)) : internal B z∈lengthPiece I A r := by
  rw [lengthPiece_eq_span] at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨L,hL,rfl⟩ := hz
    change L.length=r+1 at hL
    rw [internal_single,one_smul]
    have h := lift_mem_lengthPiece (A := A) _ (reducedDifferentialBasis_mem_lengthPiece B L)
    simpa only [hL,Nat.add_sub_cancel] using h
  | zero => simpa only [map_zero] using (lengthPiece I A r).zero_mem
  | add z w hz hw ihz ihw =>
    simpa only [map_add] using (lengthPiece I A r).add_mem ihz ihw
  | smul a z hz ih =>
    simpa only [map_smul] using (lengthPiece I A r).smul_mem a ih

theorem differential_mem_lengthPiece {r : ℕ} (z : Words I A)
    (hz : z∈lengthPiece I A (r+1)) : differential B z∈lengthPiece I A r :=
  (lengthPiece I A r).sub_mem (front_mem_lengthPiece B z hz)
    (internal_mem_lengthPiece B z hz)

theorem homotopy_mem_lengthPiece {r : ℕ} (z : Words I A)
    (hz : z∈lengthPiece I A r) : homotopy B z∈lengthPiece I A (r+1) := by
  classical
  rw [←Finsupp.sum_single z,Finsupp.sum,map_sum]
  apply Submodule.sum_mem
  intro L hL
  have hlen : L.length=r := hz hL
  rw [homotopy_single,Finsupp.linearCombination_apply,Finsupp.sum]
  apply Submodule.sum_mem
  intro i hi
  exact (lengthPiece I A (r+1)).smul_of_tower_mem _
    (single_mem_lengthPiece _ _ (by simp only [List.length_cons,hlen]))

theorem augmentationProjection_eq_zero_of_positive {r : ℕ} (z : Words I A)
    (hz : z∈lengthPiece I A (r+1)) : augmentationProjection ε z=0 := by
  have hzero : z []=0 := (mem_lengthPiece_iff z (r+1)).mp hz [] (by simp)
  simp only [augmentationProjection,LinearMap.comp_apply,LinearMap.smulRight_apply,
    Finsupp.lapply_apply,hzero,AlgHom.toLinearMap_apply,map_zero,zero_smul]

include hunit hε in
/-- Every positive-length cycle is a boundary of the explicitly constructed
next-length element. This is exactness of the actual differential. -/
theorem positive_cycle_is_boundary {r : ℕ} (z : Words I A)
    (hz : z∈lengthPiece I A (r+1)) (hd : differential B z=0) :
    ∃ y∈lengthPiece I A (r+2),differential B y=z := by
  refine ⟨homotopy B z,homotopy_mem_lengthPiece B z hz,?_⟩
  have h := contracting_identity ε B hunit hε z
  simpa only [hd,map_zero,augmentationProjection_eq_zero_of_positive ε z hz,add_zero] using h

end PaperVerification.NoncommutativeBar
end
end
end TAF_LiteralSource_0479

section TAF_LiteralSource_0480
/- Original module: PaperVerification.AugmentationCoinvariants -/


/-!
# Actual augmentation coinvariants over a possibly noncommutative algebra

For an augmented algebra `ε : A →ₐ[K] K`, this module constructs the
literal additive functor `M ↦ M/(ker ε)M`.  The source algebra is only a
`Ring`; it is not required to be commutative.  The functor is proved left
adjoint to restriction of scalars along the augmentation.

The last definitions use Mathlib's actual left-derived-functor machinery
and its comparison with an arbitrary genuine projective resolution.  No
vanishing, diagonal grading, or Koszulness assertion is inserted into the
definition.  Identification with a normalized bar complex is a separate
proof obligation.  This supporting source is a candidate until checked.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PaperVerification.AugmentationCoinvariants

open CategoryTheory CategoryTheory.Limits

universe u
variable {K A : Type u} [CommRing K] [Ring A] [Algebra K A]
  (ε : A →ₐ[K] K)

local instance groundModule (M : ModuleCat.{u} A) : Module K M :=
  Module.compHom M (algebraMap K A)

abbrev baseObject (M : ModuleCat.{u} A) : ModuleCat.{u} K :=
  (ModuleCat.restrictScalars (algebraMap K A)).obj M

/-- The literal subspace generated by the action of the augmentation kernel. -/
def relations (M : ModuleCat.{u} A) : Submodule K (baseObject (K := K) M) :=
  Submodule.span K {x | ∃ a : A, ε a=0 ∧ ∃ m : M,a • m=x}

theorem kernel_smul_mem (M : ModuleCat.{u} A) (a : A) (ha : ε a=0) (m : M) :
    a • m∈relations ε M := Submodule.subset_span ⟨a,ha,m,rfl⟩

def object (M : ModuleCat.{u} A) : ModuleCat.{u} K :=
  ModuleCat.of K ((baseObject (K := K) M) ⧸ relations ε M)

def quotient (M : ModuleCat.{u} A) : baseObject (K := K) M →ₗ[K] object ε M :=
  (relations ε M).mkQ

@[simp] theorem quotient_apply (M : ModuleCat.{u} A) (m : M) :
    quotient ε M m=Submodule.Quotient.mk m := rfl

theorem relations_map {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    relations ε M≤(relations ε N).comap
      ((ModuleCat.restrictScalars (algebraMap K A)).map f).hom := by
  apply Submodule.span_le.mpr
  rintro x ⟨a,ha,m,rfl⟩
  change f.hom (a • m)∈relations ε N
  rw [map_smul]
  exact kernel_smul_mem ε N a ha (f.hom m)

def map {M N : ModuleCat.{u} A} (f : M ⟶ N) : object ε M ⟶ object ε N :=
  ModuleCat.ofHom ((relations ε M).mapQ (relations ε N)
    ((ModuleCat.restrictScalars (algebraMap K A)).map f).hom (relations_map ε f))

@[simp] theorem map_quotient {M N : ModuleCat.{u} A} (f : M ⟶ N) (m : M) :
    (map ε f).hom (quotient ε M m)=quotient ε N (f.hom m) := rfl

/-- Actual quotient coinvariants as a functor on left modules. -/
def functor : ModuleCat.{u} A ⥤ ModuleCat.{u} K where
  obj := object ε
  map := map ε
  map_id M := by
    ext x
    refine Quotient.inductionOn' x ?_
    intro m
    rfl
  map_comp f g := by
    ext x
    refine Quotient.inductionOn' x ?_
    intro m
    rfl

instance : (functor ε).Additive where
  map_add {M N} {f g} := by
    ext x
    refine Quotient.inductionOn' x ?_
    intro m
    rfl

/-- After passing to coinvariants, the original action is exactly the
action through the augmentation. -/
theorem quotient_smul (M : ModuleCat.{u} A) (a : A) (m : M) :
    quotient ε M (a • m)=ε a • quotient ε M m := by
  change (Submodule.Quotient.mk (a • m) : (baseObject (K := K) M) ⧸ relations ε M)=
    Submodule.Quotient.mk ((algebraMap K A (ε a)) • m)
  apply (Submodule.Quotient.eq (relations ε M)).mpr
  have h := kernel_smul_mem ε M (a-algebraMap K A (ε a)) (by simp) m
  simpa only [sub_smul] using h

def toAugmentationHom (M : ModuleCat.{u} A) (N : ModuleCat.{u} K)
    (f : object ε M ⟶ N) : M ⟶ (ModuleCat.restrictScalars ε.toRingHom).obj N := by
  letI : Module A N := Module.compHom N ε.toRingHom
  exact ModuleCat.ofHom (X := M) (Y := (ModuleCat.restrictScalars ε.toRingHom).obj N)
    { toFun m := f.hom (quotient ε M m)
      map_add' m n := by rw [map_add,map_add]
      map_smul' a m := by
        change f.hom (quotient ε M (a • m))=ε a • f.hom (quotient ε M m)
        rw [quotient_smul,map_smul] }

def augmentationHomLinear (M : ModuleCat.{u} A) (N : ModuleCat.{u} K)
    (f : M ⟶ (ModuleCat.restrictScalars ε.toRingHom).obj N) :
    baseObject (K := K) M →ₗ[K] N where
  toFun := f.hom
  map_add' := f.hom.map_add
  map_smul' c m := by
    change f.hom ((algebraMap K A c) • m)=c • f.hom m
    erw [map_smul]
    change ε (algebraMap K A c) • f.hom m=c • f.hom m
    simp

theorem relations_le_kernel (M : ModuleCat.{u} A) (N : ModuleCat.{u} K)
    (f : M ⟶ (ModuleCat.restrictScalars ε.toRingHom).obj N) :
    relations ε M≤LinearMap.ker (augmentationHomLinear ε M N f) := by
  apply Submodule.span_le.mpr
  rintro x ⟨a,ha,m,rfl⟩
  change f.hom (a • m)=0
  rw [map_smul]
  change ε a • f.hom m=0
  rw [ha,zero_smul]

def fromAugmentationHom (M : ModuleCat.{u} A) (N : ModuleCat.{u} K)
    (f : M ⟶ (ModuleCat.restrictScalars ε.toRingHom).obj N) : object ε M ⟶ N :=
  ModuleCat.ofHom ((relations ε M).liftQ (augmentationHomLinear ε M N f)
    (relations_le_kernel ε M N f))

@[simp] theorem fromAugmentationHom_quotient (M : ModuleCat.{u} A) (N : ModuleCat.{u} K)
    (f : M ⟶ (ModuleCat.restrictScalars ε.toRingHom).obj N) (m : M) :
    (fromAugmentationHom ε M N f).hom (quotient ε M m)=f.hom m := rfl

/-- The genuine universal property of augmentation coinvariants. -/
def homEquiv (M : ModuleCat.{u} A) (N : ModuleCat.{u} K) :
    (object ε M ⟶ N) ≃ (M ⟶ (ModuleCat.restrictScalars ε.toRingHom).obj N) where
  toFun := toAugmentationHom ε M N
  invFun := fromAugmentationHom ε M N
  left_inv f := by
    ext x
    refine Quotient.inductionOn' x ?_
    intro m
    rfl
  right_inv f := by
    ext m
    rfl

/-- The quotient construction is left adjoint to the actual restriction
functor along `ε`, for ordinary noncommutative `A`. -/
def adjunction : functor ε ⊣ ModuleCat.restrictScalars ε.toRingHom :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv ε
      homEquiv_naturality_left_symm := by
        intro M' M N f g
        ext x
        refine Quotient.inductionOn' x ?_
        intro m
        rfl
      homEquiv_naturality_right := by
        intro M N N' f g
        ext m
        rfl }

/-- The actual augmentation module, with its left `A` action through `ε`. -/
def augmentationModule : ModuleCat.{u} A :=
  (ModuleCat.restrictScalars ε.toRingHom).obj (ModuleCat.of K K)

/-- Ordinary left-derived augmentation coinvariants.  These are defined
using genuine projective resolutions by Mathlib's categorical machinery. -/
def derived (r : ℕ) : ModuleCat.{u} A ⥤ ModuleCat.{u} K :=
  (functor ε).leftDerived r

def augmentationTor (r : ℕ) : ModuleCat.{u} K :=
  (derived ε r).obj (augmentationModule ε)

/-- Every actual projective resolution computes this derived functor.
The supplied object is a verified `ProjectiveResolution`, not an assumed
acyclic sequence or a renamed homology vector space. -/
def computedByResolution {M : ModuleCat.{u} A} (P : ProjectiveResolution M) (r : ℕ) :
    (derived ε r).obj M ≅
      (((functor ε).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).homology r :=
  P.isoLeftDerivedObj (functor ε) r

end PaperVerification.AugmentationCoinvariants
end
end
end TAF_LiteralSource_0480

section TAF_LiteralSource_0481
/- Original module: PaperVerification.NoncommutativeBarResolution -/


/-!
# An actual projective normalized bar resolution

The terms are the free length pieces and the differential is the literal
normalized bar differential. Exactness is proved using the explicit contraction.
The augmentation module is the actual quotient by the augmentation ideal,
proved algebra-isomorphic to the coefficient ring.
-/

@[expose] public section
noncomputable section

namespace PaperVerification.NoncommutativeBar

open CategoryTheory CategoryTheory.Limits
open PaperVerification.AugmentedAlgebraBasis

universe u
variable {K A I : Type u} [CommRing K] [Ring A] [Algebra K A]
  (ε : A →ₐ[K] K) (B : Module.Basis (Option I) K A)
  (hunit : B none=1) (hε : ∀ i,ε (B (some i))=0)

def residueIdeal : Ideal A := RingHom.ker ε.toRingHom

instance residueIdeal_twoSided : (residueIdeal ε).IsTwoSided := by
  dsimp only [residueIdeal]
  infer_instance

abbrev Residue := A ⧸ residueIdeal ε

theorem augmentation_surjective : Function.Surjective ε := by
  intro c
  exact ⟨algebraMap K A c, ε.commutes c⟩

def residueEquivCoefficients : Residue ε ≃ₐ[K] K :=
  Ideal.quotientKerAlgEquivOfSurjective (augmentation_surjective ε)

def degreeDifferential (r : ℕ) :
    lengthPiece I A (r+1) →ₗ[A] lengthPiece I A r :=
  LinearMap.codRestrict _
    ((differential B).comp (lengthPiece I A (r+1)).subtype)
    (fun z ↦ differential_mem_lengthPiece B z.val z.property)

@[simp] theorem degreeDifferential_coe (r : ℕ) (z : lengthPiece I A (r+1)) :
    (degreeDifferential B r z : Words I A)=differential B z.val := rfl

include hunit hε in
theorem degreeDifferential_comp (r : ℕ) :
    (degreeDifferential B r).comp (degreeDifferential B (r+1))=0 := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  exact differential_squared ε B hunit hε z.val

def complex : ChainComplex (ModuleCat A) ℕ :=
  ChainComplex.of (fun r ↦ ModuleCat.of A (lengthPiece I A r))
    (fun r ↦ ModuleCat.ofHom (degreeDifferential B r))
    (fun r ↦ ModuleCat.hom_ext (degreeDifferential_comp ε B hunit hε r))

include hunit hε in
@[simp] theorem complex_X (r : ℕ) :
    (complex ε B hunit hε).X r=ModuleCat.of A (lengthPiece I A r) := rfl

include hunit hε in
@[simp] theorem complex_d (r : ℕ) :
    (complex ε B hunit hε).d (r+1) r=ModuleCat.ofHom (degreeDifferential B r) := by
  simp [complex]

/-- The degree-zero map is evaluation of the free coefficient modulo the
actual augmentation ideal. -/
def augmentationMap : lengthPiece I A 0 →ₗ[A] Residue ε :=
  (residueIdeal ε).mkQ.comp
    ((Finsupp.lapply []).comp (lengthPiece I A 0).subtype)

theorem length_zero_eq_single (z : Words I A) (hz : z∈lengthPiece I A 0) :
    z=Finsupp.single [] (z []) := by
  classical
  ext L
  by_cases hL : L=[]
  · subst L
    simp
  · have hlen : L.length≠0 := fun h => hL (List.length_eq_zero_iff.mp h)
    rw [(mem_lengthPiece_iff z 0).mp hz L hlen,Finsupp.single_eq_of_ne hL]

theorem differential_length_zero (z : Words I A) (hz : z∈lengthPiece I A 0) :
    differential B z=0 := by
  rw [length_zero_eq_single z hz]
  simp only [differential,LinearMap.sub_apply,front_single,frontBasis,internal_single,
    PaperVerification.ReducedBarBasis.differentialBasis,map_zero,smul_zero,sub_zero]

theorem augmentationMap_surjective : Function.Surjective (augmentationMap (I := I) ε) := by
  intro q
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective q
  exact ⟨⟨Finsupp.single [] a,single_mem_lengthPiece _ _ rfl⟩,by
    simp [augmentationMap]⟩

include hunit hε in
/-- The augmentation kills the literal differential on every length-one word. -/
theorem augmentation_differential_zero (z : Words I A)
    (hz : z∈lengthPiece I A 1) :
    (residueIdeal ε).mkQ ((differential B z) [])=0 := by
  rw [lengthPiece_eq_span] at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨L,hL,rfl⟩ := hz
    obtain ⟨i,rfl⟩ := List.length_eq_one_iff.mp hL
    simp only [differential,LinearMap.sub_apply,front_single,frontBasis,internal_single,
      PaperVerification.ReducedBarBasis.differentialBasis,
      PaperVerification.ReducedBarBasis.merge_single,
      PaperVerification.ReducedBarBasis.mergeBasis,smul_zero,map_zero,sub_zero,one_smul,
      Finsupp.single_eq_same]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact hε i
  | zero => simp only [map_zero,Finsupp.zero_apply]
  | add z w hz hw ihz ihw => simp only [map_add,Finsupp.add_apply,ihz,ihw,add_zero]
  | smul a z hz ih =>
    simp only [map_smul,Finsupp.smul_apply,ih,smul_zero]

include hunit hε in
theorem augmentationMap_differential :
    (augmentationMap (I := I) ε).comp (degreeDifferential B 0)=0 := by
  apply LinearMap.ext
  intro z
  exact augmentation_differential_zero ε B hunit hε z.val z.property

include hunit hε in
theorem degreeDifferential_exact (r : ℕ) :
    Function.Exact (degreeDifferential B (r+1)) (degreeDifferential B r) := by
  intro z
  constructor
  · intro hz
    have hd : differential B z.val=0 := congrArg Subtype.val hz
    obtain ⟨y,hy,hd⟩ := positive_cycle_is_boundary ε B hunit hε z.val z.property hd
    exact ⟨⟨y,hy⟩,Subtype.ext hd⟩
  · rintro ⟨y,rfl⟩
    apply Subtype.ext
    exact differential_squared ε B hunit hε y.val

include hunit hε in
theorem augmentationMap_exact :
    Function.Exact (degreeDifferential B 0) (augmentationMap (I := I) ε) := by
  intro z
  constructor
  · intro hz
    have he : ε (z.val [])=0 := Ideal.Quotient.eq_zero_iff_mem.mp hz
    have hp : augmentationProjection ε z.val=0 := by
      simp only [augmentationProjection,LinearMap.comp_apply,LinearMap.smulRight_apply,
        Finsupp.lapply_apply,AlgHom.toLinearMap_apply,he,zero_smul]
    refine ⟨⟨homotopy B z.val,homotopy_mem_lengthPiece B z.val z.property⟩,?_⟩
    apply Subtype.ext
    change differential B (homotopy B z.val)=z.val
    have h := contracting_identity ε B hunit hε z.val
    simpa only [differential_length_zero B z.val z.property,map_zero,hp,add_zero] using h
  · rintro ⟨y,rfl⟩
    exact LinearMap.congr_fun (augmentationMap_differential ε B hunit hε) y

include hunit hε in
theorem complex_exactAt_succ (r : ℕ) :
    (complex ε B hunit hε).ExactAt (r+1) := by
  rw [HomologicalComplex.exactAt_iff' _ ((r+1)+1) (r+1) r (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff_range_eq_ker]
  simp only [HomologicalComplex.sc',HomologicalComplex.shortComplexFunctor',
    complex,ChainComplex.of_d,ModuleCat.hom_ofHom]
  exact (LinearMap.exact_iff.mp (degreeDifferential_exact ε B hunit hε r)).symm

def augmentation :
    (complex ε B hunit hε).X 0 ⟶ ModuleCat.of A (Residue ε) :=
  ModuleCat.ofHom (augmentationMap ε)

include hunit hε in
theorem complex_d_augmentation :
    (complex ε B hunit hε).d 1 0 ≫ augmentation ε B hunit hε=0 := by
  apply ModuleCat.hom_ext
  exact augmentationMap_differential ε B hunit hε

include hunit hε in
theorem augmentation_exact :
    (ShortComplex.mk _ _ (complex_d_augmentation ε B hunit hε)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  change LinearMap.range (degreeDifferential B 0)=LinearMap.ker (augmentationMap ε)
  exact (LinearMap.exact_iff.mp (augmentationMap_exact ε B hunit hε)).symm

instance augmentation_epi : Epi (augmentation ε B hunit hε) :=
  (ModuleCat.epi_iff_surjective _).mpr (augmentationMap_surjective ε)

/-- The actual normalized free bar resolution, with no exactness premise. -/
def resolution : ProjectiveResolution (ModuleCat.of A (Residue ε)) where
  complex := complex ε B hunit hε
  projective r := by
    change Projective (ModuleCat.of A (lengthPiece I A r))
    infer_instance
  π := (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨augmentation ε B hunit hε,complex_d_augmentation ε B hunit hε⟩
  quasiIso := ⟨fun r ↦ by
    cases r with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff,ShortComplex.quasiIso_iff_of_zeros']
      · change (ShortComplex.mk _ _ (complex_d_augmentation ε B hunit hε)).Exact ∧
          Epi (augmentation ε B hunit hε)
        exact ⟨augmentation_exact ε B hunit hε,inferInstance⟩
      all_goals rfl
    | succ r =>
      rw [quasiIsoAt_iff_exactAt']
      · exact complex_exactAt_succ ε B hunit hε r
      · exact ChainComplex.exactAt_succ_single_obj _ _⟩

/-- The actual left-derived augmentation-coinvariants functor is computed
by the genuine projective bar resolution.  The algebra need not commute. -/
def derivedCoinvariantsIso (r : ℕ) :
    (AugmentationCoinvariants.derived ε r).obj (ModuleCat.of A (Residue ε)) ≅
      (((AugmentationCoinvariants.functor ε).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (resolution ε B hunit hε).complex).homology r :=
  AugmentationCoinvariants.computedByResolution ε (resolution ε B hunit hε) r

end PaperVerification.NoncommutativeBar
end
end
end TAF_LiteralSource_0481

section TAF_LiteralSource_0482
/- Original module: TauCeti.LinearAlgebra.TensorProduct.Balanced.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Tensor products over a noncommutative algebra

For a right `A`-module `M` and a left `A`-module `N`, both modules over a commutative
ring `k`, the balanced tensor product is the quotient of `M ⊗[k] N` by the relations
`(m a) ⊗ n - m ⊗ (a n)`. Right actions are represented by `Module Aᵐᵒᵖ M`.

The universal property identifies linear maps out of this quotient with balanced
`k`-bilinear maps. Pure tensors, induction, extensionality, and functoriality let
consumers work without unfolding the quotient. This is the underlying module
construction for tensoring bimodules and differential graded modules. It is not a
derived tensor product.

The quotient uses Mathlib's `TensorProduct` and `Submodule.liftQ`. The mathematical
construction is the ordinary tensor product used in Keller, *Deriving DG categories*,
Section 6.1.
-/

public section

namespace TauCeti

open MulOpposite
open scoped TensorProduct

variable (k A M N : Type*) [CommRing k] [Semiring A]
  [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M]
  [AddCommGroup N] [Module k N] [Module A N]

/-- The submodule generated by the relations moving an `A` action across a tensor. -/
def balancedTensorRelations : Submodule k (M ⊗[k] N) :=
  Submodule.span k {z | ∃ (a : A) (m : M) (n : N),
    z = (op a • m) ⊗ₜ[k] n - m ⊗ₜ[k] (a • n)}

/-- The balancing submodule is spanned by the elementary balancing relations. -/
theorem balancedTensorRelations_def : balancedTensorRelations k A M N =
    Submodule.span k {z | ∃ (a : A) (m : M) (n : N),
      z = (op a • m) ⊗ₜ[k] n - m ⊗ₜ[k] (a • n)} := (rfl)

/-- The tensor product of a right `A`-module and a left `A`-module, balanced over `A`
and linear over `k`. Compatible scalar actions give the usual algebra-relative tensor product. -/
-- Expose the quotient carrier so inherited gradings can use the canonical quotient instances.
@[expose]
def BalancedTensorProduct := (M ⊗[k] N) ⧸ balancedTensorRelations k A M N

namespace BalancedTensorProduct

instance : AddCommGroup (BalancedTensorProduct k A M N) :=
  inferInstanceAs (AddCommGroup ((M ⊗[k] N) ⧸ balancedTensorRelations k A M N))

instance : Module k (BalancedTensorProduct k A M N) :=
  inferInstanceAs (Module k ((M ⊗[k] N) ⧸ balancedTensorRelations k A M N))

/-- The balanced tensor product with a zero left factor is zero. -/
instance [Subsingleton M] : Subsingleton (BalancedTensorProduct k A M N) :=
  inferInstanceAs (Subsingleton ((M ⊗[k] N) ⧸ balancedTensorRelations k A M N))

/-- The balanced tensor product with a zero right factor is zero. -/
instance [Subsingleton N] : Subsingleton (BalancedTensorProduct k A M N) :=
  inferInstanceAs (Subsingleton ((M ⊗[k] N) ⧸ balancedTensorRelations k A M N))

variable {M N}

/-- The quotient map from the tensor product over the ground ring. -/
def mkQ : M ⊗[k] N →ₗ[k] BalancedTensorProduct k A M N :=
  (balancedTensorRelations k A M N).mkQ

/-- The balanced quotient map is the submodule quotient map. -/
theorem mkQ_def : mkQ k A (M := M) (N := N) =
    (balancedTensorRelations k A M N).mkQ := (rfl)

/-- The canonical bilinear map to the balanced tensor product. -/
def mk : M →ₗ[k] N →ₗ[k] BalancedTensorProduct k A M N :=
  (TensorProduct.mk k M N).compr₂ (mkQ k A)

/-- The canonical bilinear map is the ground-ring tensor map followed by the quotient. -/
theorem mk_def : mk k A (M := M) (N := N) =
    (TensorProduct.mk k M N).compr₂ (mkQ k A) := (rfl)

/-- A pure tensor in the balanced tensor product. -/
def tmul (m : M) (n : N) : BalancedTensorProduct k A M N := mk k A m n

@[simp]
theorem mk_apply (m : M) (n : N) : mk k A m n = tmul k A m n := (rfl)

@[simp]
theorem mkQ_tmul (m : M) (n : N) : mkQ k A (m ⊗ₜ[k] n) = tmul k A m n := (rfl)

/-- A ground-ring tensor vanishes in the quotient exactly when it lies in the span of
balancing relations. -/
@[simp]
theorem mkQ_eq_zero_iff (z : M ⊗[k] N) :
    mkQ k A z = 0 ↔ z ∈ balancedTensorRelations k A M N :=
  Submodule.Quotient.mk_eq_zero _

@[simp]
theorem zero_tmul (n : N) : tmul k A (0 : M) n = 0 := by
  simp only [tmul, map_zero, LinearMap.zero_apply]

@[simp]
theorem tmul_zero (m : M) : tmul k A m (0 : N) = 0 := by
  simp only [tmul, map_zero]

theorem add_tmul (m m' : M) (n : N) :
    tmul k A (m + m') n = tmul k A m n + tmul k A m' n := by
  simp only [tmul, map_add, LinearMap.add_apply]

theorem tmul_add (m : M) (n n' : N) :
    tmul k A m (n + n') = tmul k A m n + tmul k A m n' := by
  simp only [tmul, map_add]

@[simp]
theorem smul_tmul (r : k) (m : M) (n : N) :
    tmul k A (r • m) n = r • tmul k A m n := by
  simp only [tmul, map_smul, LinearMap.smul_apply]

@[simp]
theorem tmul_smul (r : k) (m : M) (n : N) :
    tmul k A m (r • n) = r • tmul k A m n := by
  simp only [tmul, map_smul]

/-- An `A` action can be moved from the right module to the left module. -/
theorem balance (a : A) (m : M) (n : N) :
    tmul k A (op a • m) n = tmul k A m (a • n) := by
  apply sub_eq_zero.mp
  rw [← mkQ_tmul, ← mkQ_tmul, ← map_sub]
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (Submodule.subset_span ⟨a, m, n, rfl⟩)

/-- Every balanced tensor is represented by a ground-ring tensor. -/
theorem mkQ_surjective : Function.Surjective (mkQ k A (M := M) (N := N)) :=
  (balancedTensorRelations k A M N).mkQ_surjective

/-- Induction on balanced tensors by pure tensors and addition. -/
@[elab_as_elim]
theorem induction_on {P : BalancedTensorProduct k A M N → Prop}
    (x : BalancedTensorProduct k A M N)
    (ht : ∀ m n, P (tmul k A m n))
    (ha : ∀ x y, P x → P y → P (x + y)) : P x := by
  obtain ⟨z, rfl⟩ := mkQ_surjective k A x
  induction z using TensorProduct.inductionOn with
  | tmul m n => exact ht m n
  | add x y hx hy => simpa using ha _ _ hx hy

variable {k A} {P : Type*} [AddCommGroup P] [Module k P]

/-- Linear maps out of a balanced tensor product agree if they agree on pure tensors. -/
@[ext high]
theorem hom_ext {f g : BalancedTensorProduct k A M N →ₗ[k] P}
    (h : ∀ m n, f (tmul k A m n) = g (tmul k A m n)) : f = g := by
  apply LinearMap.ext
  intro x
  induction x using induction_on with
  | ht m n => exact h m n
  | ha x y hx hy => simp [hx, hy]

/-- Lift a balanced bilinear map through the tensor product. -/
def lift (f : M →ₗ[k] N →ₗ[k] P)
    (hf : ∀ (a : A) m n, f (op a • m) n = f m (a • n)) :
    BalancedTensorProduct k A M N →ₗ[k] P :=
  (balancedTensorRelations k A M N).liftQ (TensorProduct.lift f) (by
    rw [balancedTensorRelations, Submodule.span_le]
    rintro z ⟨a, m, n, rfl⟩
    simp [LinearMap.mem_ker, hf])

@[simp]
theorem lift_tmul (f : M →ₗ[k] N →ₗ[k] P)
    (hf : ∀ (a : A) m n, f (op a • m) n = f m (a • n)) (m : M) (n : N) :
    lift f hf (tmul k A m n) = f m n := (rfl)

/-- The universal property: balanced bilinear maps are precisely linear maps out of
the balanced tensor product. -/
def liftEquiv :
    {f : M →ₗ[k] N →ₗ[k] P // ∀ (a : A) m n, f (op a • m) n = f m (a • n)} ≃
      (BalancedTensorProduct k A M N →ₗ[k] P) where
  toFun f := lift f.1 f.2
  invFun g := ⟨(mk k A).compr₂ g, fun a m n ↦ congrArg g (balance k A a m n)⟩
  left_inv f := by ext m n; rfl
  right_inv g := hom_ext fun _ _ ↦ rfl

@[simp]
theorem liftEquiv_apply (f :
    {f : M →ₗ[k] N →ₗ[k] P // ∀ (a : A) m n, f (op a • m) n = f m (a • n)}) :
    liftEquiv f = lift f.1 f.2 := (rfl)

@[simp]
theorem liftEquiv_symm_apply (g : BalancedTensorProduct k A M N →ₗ[k] P) (m : M) (n : N) :
    (liftEquiv.symm g).1 m n = g (tmul k A m n) := (rfl)

section Map

variable {M' N' M'' N'' : Type*}
  [AddCommGroup M'] [Module k M'] [Module Aᵐᵒᵖ M']
  [AddCommGroup N'] [Module k N'] [Module A N']
  [AddCommGroup M''] [Module k M''] [Module Aᵐᵒᵖ M'']
  [AddCommGroup N''] [Module k N''] [Module A N'']

/-- The map induced by equivariant ground-ring linear maps in both factors. -/
def map (f : M →ₗ[k] M') (g : N →ₗ[k] N')
    (hf : ∀ (a : A) m, f (op a • m) = op a • f m)
    (hg : ∀ (a : A) n, g (a • n) = a • g n) :
    BalancedTensorProduct k A M N →ₗ[k] BalancedTensorProduct k A M' N' :=
  lift (((mk k A).comp f).compl₂ g) (fun a m n ↦ by
    simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, mk_apply, hf, hg]
    exact balance k A a (f m) (g n))

@[simp]
theorem map_tmul (f : M →ₗ[k] M') (g : N →ₗ[k] N')
    (hf : ∀ (a : A) m, f (op a • m) = op a • f m)
    (hg : ∀ (a : A) n, g (a • n) = a • g n) (m : M) (n : N) :
    map f g hf hg (tmul k A m n) = tmul k A (f m) (g n) := (rfl)

@[simp]
theorem map_id : map (A := A) (LinearMap.id : M →ₗ[k] M) (LinearMap.id : N →ₗ[k] N)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) = LinearMap.id :=
  hom_ext fun _ _ ↦ rfl

/-- Tensoring respects composition of equivariant maps. -/
theorem map_comp (f : M →ₗ[k] M') (g : N →ₗ[k] N')
    (f' : M' →ₗ[k] M'') (g' : N' →ₗ[k] N'')
    (hf : ∀ (a : A) m, f (op a • m) = op a • f m)
    (hg : ∀ (a : A) n, g (a • n) = a • g n)
    (hf' : ∀ (a : A) m, f' (op a • m) = op a • f' m)
    (hg' : ∀ (a : A) n, g' (a • n) = a • g' n) :
    map (f'.comp f) (g'.comp g)
        (fun a m ↦ by simp [hf, hf']) (fun a n ↦ by simp [hg, hg']) =
      (map f' g' hf' hg').comp (map f g hf hg) :=
  hom_ext fun _ _ ↦ rfl

/-- Equivariant linear equivalences of the factors identify their balanced tensor products. -/
def congr (f : M ≃ₗ[k] M') (g : N ≃ₗ[k] N')
    (hf : ∀ (a : A) m, f (op a • m) = op a • f m)
    (hg : ∀ (a : A) n, g (a • n) = a • g n) :
    BalancedTensorProduct k A M N ≃ₗ[k] BalancedTensorProduct k A M' N' :=
  LinearEquiv.ofLinearMap (map f.toLinearMap g.toLinearMap hf hg)
    (map f.symm.toLinearMap g.symm.toLinearMap
      (fun a m ↦ by
        apply f.injective
        simpa only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using
          (hf a (f.symm m)).symm)
      (fun a n ↦ by
        apply g.injective
        simpa only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using
          (hg a (g.symm n)).symm))
    (by
      apply hom_ext
      intro m n
      simp)
    (by
      apply hom_ext
      intro m n
      simp)

/-- The carrier map of tensor congruence is the balanced tensor of the two factor maps. -/
theorem congr_apply (f : M ≃ₗ[k] M') (g : N ≃ₗ[k] N')
    (hf : ∀ (a : A) m, f (op a • m) = op a • f m)
    (hg : ∀ (a : A) n, g (a • n) = a • g n) (z : BalancedTensorProduct k A M N) :
    congr f g hf hg z = map f.toLinearMap g.toLinearMap hf hg z := by
  simp only [congr, LinearEquiv.coe_ofLinearMap]

@[simp]
theorem congr_tmul (f : M ≃ₗ[k] M') (g : N ≃ₗ[k] N')
    (hf : ∀ (a : A) m, f (op a • m) = op a • f m)
    (hg : ∀ (a : A) n, g (a • n) = a • g n) (m : M) (n : N) :
    congr f g hf hg (tmul k A m n) = tmul k A (f m) (g n) := (rfl)

@[simp]
theorem congr_symm_tmul (f : M ≃ₗ[k] M') (g : N ≃ₗ[k] N')
    (hf : ∀ (a : A) m, f (op a • m) = op a • f m)
    (hg : ∀ (a : A) n, g (a • n) = a • g n) (m : M') (n : N') :
    (congr f g hf hg).symm (tmul k A m n) = tmul k A (f.symm m) (g.symm n) := (rfl)

end Map

end BalancedTensorProduct

end TauCeti
end
end TAF_LiteralSource_0482

section TAF_LiteralSource_0483
/- Original module: PaperVerification.AugmentationBalancedTensor -/


/-!
# Augmentation coinvariants are the ordinary balanced tensor product

This is the explicit comparison `K ⊗_A M ≃ M/(ker ε)M` for an arbitrary
possibly noncommutative augmented algebra.  The tensor on the left is the
actual quotient of the ground-ring tensor product by the balancing
relations, with the right `A` action on `K` defined through the augmentation.
The maps are `c ⊗ m ↦ c [m]` and `[m] ↦ 1 ⊗ m`, and both inverse laws are
proved.  This identifies the functor being derived in the companion file
with ordinary augmentation tensoring, without a commutativity assumption
on `A` or an assumed bar-homology comparison.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PaperVerification.AugmentationCoinvariants

open CategoryTheory MulOpposite

universe u
variable {K A : Type u} [CommRing K] [Ring A] [Algebra K A]

/-- The coefficient ring carrying the specified right augmentation action. -/
def RightResidue (ε : A →ₐ[K] K) := K

variable (ε : A →ₐ[K] K)

def rightResidueValue (c : RightResidue ε) : K := c

local instance balancedGroundModule (M : ModuleCat.{u} A) : Module K M :=
  Module.compHom M (algebraMap K A)

instance : AddCommGroup (RightResidue ε) := inferInstanceAs (AddCommGroup K)
instance : Module K (RightResidue ε) := inferInstanceAs (Module K K)

def rightAugmentation : Aᵐᵒᵖ →+* K where
  toFun a := ε a.unop
  map_one' := ε.map_one
  map_mul' a b := by
    change ε (b.unop*a.unop)=ε a.unop*ε b.unop
    rw [map_mul,mul_comm]
  map_zero' := ε.map_zero
  map_add' a b := ε.map_add _ _

instance : Module Aᵐᵒᵖ (RightResidue ε) :=
  Module.compHom (RightResidue ε) (rightAugmentation ε)

local instance originalModule (M : ModuleCat.{u} A) :
    Module A (baseObject (K := K) M) := inferInstanceAs (Module A M)

/-- The actual ordinary tensor product with the right augmentation module. -/
abbrev Balanced (M : ModuleCat.{u} A) :=
  TauCeti.BalancedTensorProduct K A (RightResidue ε) (baseObject (K := K) M)

def balancedEvaluation (M : ModuleCat.{u} A) :
    RightResidue ε →ₗ[K] baseObject (K := K) M →ₗ[K] object ε M :=
  LinearMap.mk₂ K (fun c m => rightResidueValue ε c • quotient ε M m)
    (by
      intro c d m
      change (rightResidueValue ε c+rightResidueValue ε d) • quotient ε M m=_
      exact add_smul _ _ _)
    (by
      intro k c m
      change (k*rightResidueValue ε c) • quotient ε M m=_
      exact mul_smul _ _ _)
    (by
      intro c m n
      rw [map_add,smul_add])
    (by
      intro k c m
      rw [map_smul,smul_comm])

theorem balancedEvaluation_balanced (M : ModuleCat.{u} A)
    (a : A) (c : RightResidue ε) (m : M) :
    balancedEvaluation ε M (op a • c) m=balancedEvaluation ε M c (a • m) := by
  change (ε a*(rightResidueValue ε c)) • quotient ε M m=(rightResidueValue ε c) • quotient ε M (a • m)
  rw [quotient_smul,smul_smul,mul_comm]

def balancedToCoinvariants (M : ModuleCat.{u} A) : Balanced ε M →ₗ[K] object ε M :=
  TauCeti.BalancedTensorProduct.lift (balancedEvaluation ε M)
    (balancedEvaluation_balanced ε M)

@[simp] theorem balancedToCoinvariants_tmul (M : ModuleCat.{u} A)
    (c : RightResidue ε) (m : M) :
    balancedToCoinvariants ε M (TauCeti.BalancedTensorProduct.tmul K A c m)=
      (rightResidueValue ε c) • quotient ε M m := by
  rw [balancedToCoinvariants,TauCeti.BalancedTensorProduct.lift_tmul]
  rfl

def toBalanced (M : ModuleCat.{u} A) : baseObject (K := K) M →ₗ[K] Balanced ε M :=
  TauCeti.BalancedTensorProduct.mk K A (show RightResidue ε from (1 : K))

theorem relations_le_toBalanced_kernel (M : ModuleCat.{u} A) :
    relations ε M≤LinearMap.ker (toBalanced ε M) := by
  apply Submodule.span_le.mpr
  rintro x ⟨a,ha,m,rfl⟩
  change TauCeti.BalancedTensorProduct.tmul K A
    (show RightResidue ε from (1 : K)) (a • m)=0
  have h := TauCeti.BalancedTensorProduct.balance K A a
    (show RightResidue ε from (1 : K)) m
  have hz : op a • (show RightResidue ε from (1 : K))=0 := by
    change ε a*1=0
    rw [ha,zero_mul]
  rw [hz,TauCeti.BalancedTensorProduct.zero_tmul] at h
  exact h.symm

def coinvariantsToBalanced (M : ModuleCat.{u} A) : object ε M →ₗ[K] Balanced ε M :=
  (relations ε M).liftQ (toBalanced ε M) (relations_le_toBalanced_kernel ε M)

@[simp] theorem coinvariantsToBalanced_quotient (M : ModuleCat.{u} A) (m : M) :
    coinvariantsToBalanced ε M (quotient ε M m)=
      TauCeti.BalancedTensorProduct.tmul K A (show RightResidue ε from (1 : K)) m := by
  rw [coinvariantsToBalanced,quotient_apply]
  erw [Submodule.liftQ_apply]
  exact TauCeti.BalancedTensorProduct.mk_apply K A _ _

/-- An actual linear equivalence with the literal balanced tensor quotient. -/
def balancedEquiv (M : ModuleCat.{u} A) : Balanced ε M ≃ₗ[K] object ε M :=
  LinearEquiv.ofLinearMap (balancedToCoinvariants ε M) (coinvariantsToBalanced ε M)
    (by
      apply LinearMap.ext
      intro x
      refine Quotient.inductionOn' x ?_
      intro m
      change balancedToCoinvariants ε M (coinvariantsToBalanced ε M (quotient ε M m))=
        quotient ε M m
      rw [coinvariantsToBalanced_quotient,balancedToCoinvariants_tmul]
      change (1 : K) • quotient ε M m=quotient ε M m
      exact one_smul _ _)
    (by
      apply TauCeti.BalancedTensorProduct.hom_ext
      intro c m
      change coinvariantsToBalanced ε M
        (balancedToCoinvariants ε M (TauCeti.BalancedTensorProduct.tmul K A c m))=
          TauCeti.BalancedTensorProduct.tmul K A c m
      rw [balancedToCoinvariants_tmul,map_smul,coinvariantsToBalanced_quotient,
        ←TauCeti.BalancedTensorProduct.smul_tmul]
      congr 1
      change (rightResidueValue ε c)*1=c
      exact mul_one _)

@[simp] theorem balancedEquiv_tmul (M : ModuleCat.{u} A)
    (c : RightResidue ε) (m : M) :
    balancedEquiv ε M (TauCeti.BalancedTensorProduct.tmul K A c m)=
      (rightResidueValue ε c) • quotient ε M m := by
  exact balancedToCoinvariants_tmul ε M c m

end PaperVerification.AugmentationCoinvariants
end
end
end TAF_LiteralSource_0483

section TAF_LiteralSource_0484
/- Original module: PaperVerification.NoncommutativeBarCoinvariants -/


/-!
# Ordinary noncommutative augmentation Tor and its reduced bar complex

Tensoring the explicit free resolution with the augmentation residue kills
the first multiplication term. The surviving differential is exactly the
negative adjacent-product differential in the original positive basis.
The comparison is an isomorphism of actual chain complexes.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators TensorProduct

namespace PaperVerification.NoncommutativeBar

open CategoryTheory CategoryTheory.Limits
open PaperVerification.AugmentedAlgebraBasis

universe u
variable {K A I : Type u} [CommRing K] [Ring A] [Algebra K A]
  (ε : A →ₐ[K] K) (B : Module.Basis (Option I) K A)
  (hunit : B none=1) (hε : ∀ i,ε (B (some i))=0)

def specialize : Words I A →ₗ[K] Words I K :=
  Finsupp.mapRange.linearMap ε.toLinearMap

@[simp] theorem specialize_apply (z : Words I A) (L : List I) :
    specialize ε z L=ε (z L) := rfl

@[simp] theorem specialize_single (L : List I) (a : A) :
    specialize ε (Finsupp.single L a)=Finsupp.single L (ε a) := by
  classical
  ext T
  by_cases h : L=T <;> simp [specialize_apply,Finsupp.single_apply,h]

theorem specialize_smul (a : A) (z : Words I A) :
    specialize ε (a • z)=ε a • specialize ε z := by
  ext L
  simp only [specialize_apply,Finsupp.smul_apply,smul_eq_mul,map_mul]

theorem specialize_lift (z : Words I K) : specialize ε (lift z)=z := by
  ext L
  rw [specialize_apply,lift_apply,ε.commutes]
  rfl

include hε in
theorem specialize_front (z : Words I A) : specialize ε (front B z)=0 := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add z w hz hw => simp only [map_add,hz,hw,add_zero]
  | single L a =>
    cases L with
    | nil => simp only [front_single,frontBasis,smul_zero,map_zero]
    | cons i L =>
      rw [front_single,specialize_smul]
      change ε a • specialize ε (Finsupp.single L (B (some i)))=0
      rw [specialize_single,hε,Finsupp.single_zero,smul_zero]

theorem specialize_internal (z : Words I A) :
    specialize ε (internal B z)=
      PaperVerification.ReducedBarBasis.differential B (specialize ε z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add z w hz hw => simp only [map_add,hz,hw]
  | single L a =>
    rw [internal_single,specialize_smul,specialize_lift,specialize_single,
      PaperVerification.ReducedBarBasis.differential_single]

include hε in
theorem specialize_differential (z : Words I A) :
    specialize ε (differential B z)=
      -PaperVerification.ReducedBarBasis.differential B (specialize ε z) := by
  change specialize ε (front B z-internal B z)=_
  rw [map_sub,specialize_front ε B hε,specialize_internal,zero_sub]

theorem specialize_mem_lengthPiece {r : ℕ} (z : Words I A)
    (hz : z∈lengthPiece I A r) : specialize ε z∈lengthPiece I K r := by
  rw [mem_lengthPiece_iff] at hz ⊢
  intro L hL
  rw [specialize_apply,hz L hL,map_zero]

def specializePiece (r : ℕ) : lengthPiece I A r →ₗ[K] lengthPiece I K r :=
  LinearMap.codRestrict _
    ((specialize ε).comp ((lengthPiece I A r).subtype.restrictScalars K))
    (fun z ↦ specialize_mem_lengthPiece ε z.val z.property)

theorem reducedDifferential_mem_lengthPiece {r : ℕ} (z : Words I K)
    (hz : z∈lengthPiece I K (r+1)) :
    PaperVerification.ReducedBarBasis.differential B z∈lengthPiece I K r := by
  rw [lengthPiece_eq_span] at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨L,hL,rfl⟩ := hz
    change L.length=r+1 at hL
    rw [PaperVerification.ReducedBarBasis.differential_single,one_smul]
    simpa only [hL,Nat.add_sub_cancel] using reducedDifferentialBasis_mem_lengthPiece B L
  | zero => simpa only [map_zero] using (lengthPiece I K r).zero_mem
  | add z w hz hw ihz ihw =>
    simpa only [map_add] using (lengthPiece I K r).add_mem ihz ihw
  | smul a z hz ih =>
    simpa only [map_smul] using (lengthPiece I K r).smul_mem a ih

def reducedDegreeDifferential (r : ℕ) :
    lengthPiece I K (r+1) →ₗ[K] lengthPiece I K r :=
  LinearMap.codRestrict _
    ((PaperVerification.ReducedBarBasis.differential B).comp
      (lengthPiece I K (r+1)).subtype)
    (fun z ↦ reducedDifferential_mem_lengthPiece B z.val z.property)

/-- The literal pointwise negative of the actual adjacent-product map.
Its formula is stated explicitly, so the construction does not depend
on inferring a second additive-group dictionary for a space of maps. -/
def negativeReducedDegreeDifferential (r : ℕ) :
    lengthPiece I K (r+1) →ₗ[K] lengthPiece I K r where
  toFun z := ⟨-(PaperVerification.ReducedBarBasis.differential B z.val),
    (lengthPiece I K r).neg_mem
      (reducedDifferential_mem_lengthPiece B z.val z.property)⟩
  map_add' x y := by
    apply Subtype.ext
    change -(PaperVerification.ReducedBarBasis.differential B (x.val+y.val))=
      -(PaperVerification.ReducedBarBasis.differential B x.val)+
        -(PaperVerification.ReducedBarBasis.differential B y.val)
    rw [map_add,neg_add]
  map_smul' c z := by
    apply Subtype.ext
    change -(PaperVerification.ReducedBarBasis.differential B (c • z.val))=
      c • -(PaperVerification.ReducedBarBasis.differential B z.val)
    rw [map_smul,smul_neg]

@[simp] theorem negativeReducedDegreeDifferential_apply (r : ℕ)
    (z : lengthPiece I K (r+1)) :
    negativeReducedDegreeDifferential B r z=-(reducedDegreeDifferential B r z) := rfl

include hunit hε in
theorem negativeReducedDifferential_comp (r : ℕ) :
    (negativeReducedDegreeDifferential B r).comp (negativeReducedDegreeDifferential B (r+1))=0 := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  change -PaperVerification.ReducedBarBasis.differential B
    (-PaperVerification.ReducedBarBasis.differential B z.val)=0
  rw [map_neg,neg_neg,PaperVerification.ReducedBarBasis.differential_squared ε B hunit hε]

def reducedComplex : ChainComplex (ModuleCat K) ℕ :=
  ChainComplex.of (fun r ↦ ModuleCat.of K (lengthPiece I K r))
    (fun r ↦ ModuleCat.ofHom (negativeReducedDegreeDifferential B r))
    (fun r ↦ ModuleCat.hom_ext (negativeReducedDifferential_comp ε B hunit hε r))

include hunit hε in
@[simp] theorem reducedComplex_d (r : ℕ) :
    (reducedComplex ε B hunit hε).d (r+1) r=
      ModuleCat.ofHom (negativeReducedDegreeDifferential B r) := by
  simp [reducedComplex]

/-- The actual free module in bar degree `r`. -/
abbrev freeObject (r : ℕ) : ModuleCat.{u} A := ModuleCat.of A (lengthPiece I A r)

/-- Identity on elements, with a proof that the inherited scalar action
agrees with the categorical restriction-of-scalars action. -/
def freeGroundEquiv (r : ℕ) : lengthPiece I A r ≃ₗ[K]
    AugmentationCoinvariants.baseObject (K := K) (freeObject (I := I) (A := A) r) where
  toFun z := z
  invFun z := z
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c z := by
    change c • z=(algebraMap K A c) • z
    exact (IsScalarTower.algebraMap_smul A c z).symm

def liftPiece (r : ℕ) : lengthPiece I K r →ₗ[K] lengthPiece I A r where
  toFun z := ⟨lift z.val,lift_mem_lengthPiece (A := A) z.val z.property⟩
  map_add' z w := Subtype.ext (map_add (lift (A := A)) z.val w.val)
  map_smul' c z := Subtype.ext (map_smul (lift (A := A)) c z.val)

@[simp] theorem specializePiece_smul (r : ℕ) (a : A) (z : lengthPiece I A r) :
    specializePiece ε r (a • z)=ε a • specializePiece ε r z := by
  apply Subtype.ext
  exact specialize_smul ε a z.val

/-- Specialization kills exactly the augmentation relations needed to
factor through actual coinvariants of the actual free bar module. -/
def coinvariantToReduced (r : ℕ) :
    AugmentationCoinvariants.object ε (freeObject (I := I) (A := A) r) →ₗ[K]
      lengthPiece I K r := by
  change ((AugmentationCoinvariants.baseObject (K := K) (freeObject (I := I) (A := A) r)) ⧸
    AugmentationCoinvariants.relations ε (freeObject (I := I) (A := A) r)) →ₗ[K]
      lengthPiece I K r
  let F : AugmentationCoinvariants.baseObject (K := K)
      (freeObject (I := I) (A := A) r) →ₗ[K] lengthPiece I K r :=
    (specializePiece ε r).comp
      (freeGroundEquiv (K := K) (A := A) (I := I) r).symm.toLinearMap
  refine (AugmentationCoinvariants.relations ε (freeObject (I := I) (A := A) r)).liftQ
    (R₂ := K) (M₂ := ↥(lengthPiece I K r)) (τ₁₂ := RingHom.id K) F ?_
  apply Submodule.span_le.mpr
  rintro z ⟨a,ha,m,rfl⟩
  change specializePiece ε r (a • m)=0
  rw [specializePiece_smul,ha,zero_smul]

@[simp] theorem coinvariantToReduced_quotient (r : ℕ) (z : lengthPiece I A r) :
    coinvariantToReduced ε r
      (AugmentationCoinvariants.quotient ε (freeObject (I := I) (A := A) r) z)=
        specializePiece ε r z := rfl

def reducedToCoinvariant (r : ℕ) : lengthPiece I K r →ₗ[K]
    AugmentationCoinvariants.object ε (freeObject (I := I) (A := A) r) :=
  (AugmentationCoinvariants.quotient ε (freeObject (I := I) (A := A) r)).comp
    ((freeGroundEquiv (K := K) (A := A) (I := I) r).toLinearMap.comp
      (liftPiece (K := K) (A := A) (I := I) r))

theorem reduced_coinvariant_inverse (r : ℕ) (z : lengthPiece I K r) :
    coinvariantToReduced ε r (reducedToCoinvariant ε r z)=z := by
  apply Subtype.ext
  exact specialize_lift ε z.val

theorem coinvariant_specialize_inverse (r : ℕ) (z : Words I A)
    (hz : z∈lengthPiece I A r) :
    reducedToCoinvariant ε r (specializePiece ε r ⟨z,hz⟩)=
      AugmentationCoinvariants.quotient ε (freeObject (I := I) (A := A) r) ⟨z,hz⟩ := by
  have hs : z∈Submodule.span A
      ((fun L : List I ↦ Finsupp.single L (1 : A)) '' {L | L.length=r}) := by
    rwa [←lengthPiece_eq_span]
  revert hz
  induction hs using Submodule.span_induction with
  | mem z hz =>
      rintro hmem
      obtain ⟨L,hL,rfl⟩ := hz
      change AugmentationCoinvariants.quotient ε (freeObject (I := I) (A := A) r)
        ⟨lift (specialize ε (Finsupp.single L 1)),_⟩=
          AugmentationCoinvariants.quotient ε (freeObject (I := I) (A := A) r)
            ⟨Finsupp.single L 1,_⟩
      congr 1
      apply Subtype.ext
      change lift (specialize ε (Finsupp.single L 1))=Finsupp.single L 1
      rw [specialize_single,map_one,lift_single,one_smul]
  | zero =>
      intro hz
      change reducedToCoinvariant ε r (specializePiece ε r 0)=
        AugmentationCoinvariants.quotient ε (freeObject (I := I) (A := A) r) 0
      rw [map_zero,map_zero,map_zero]
  | add z w hz hw ihz ihw =>
      intro hsum
      have hz' : z∈lengthPiece I A r := by rwa [lengthPiece_eq_span]
      have hw' : w∈lengthPiece I A r := by rwa [lengthPiece_eq_span]
      change reducedToCoinvariant ε r (specializePiece ε r (⟨z,hz'⟩+⟨w,hw'⟩))=
        AugmentationCoinvariants.quotient ε (freeObject (I := I) (A := A) r)
          (⟨z,hz'⟩+⟨w,hw'⟩)
      rw [map_add,map_add,map_add,ihz hz',ihw hw']
  | smul a z hz ih =>
      intro hsmul
      have hz' : z∈lengthPiece I A r := by rwa [lengthPiece_eq_span]
      change reducedToCoinvariant ε r (specializePiece ε r (a • ⟨z,hz'⟩))=
        AugmentationCoinvariants.quotient ε (freeObject (I := I) (A := A) r) (a • ⟨z,hz'⟩)
      rw [specializePiece_smul,map_smul,ih hz',AugmentationCoinvariants.quotient_smul]

def coinvariantTermEquiv (r : ℕ) :
    AugmentationCoinvariants.object ε (freeObject (I := I) (A := A) r) ≃ₗ[K]
      lengthPiece I K r :=
  LinearEquiv.ofLinearMap (coinvariantToReduced ε r) (reducedToCoinvariant ε r)
    (by
      apply LinearMap.ext
      intro z
      exact reduced_coinvariant_inverse ε r z)
    (by
      apply LinearMap.ext
      intro z
      refine Quotient.inductionOn' z ?_
      intro x
      exact coinvariant_specialize_inverse ε r x.val x.property)

@[simp] theorem coinvariantTermEquiv_quotient (r : ℕ) (z : lengthPiece I A r) :
    coinvariantTermEquiv ε r
      (AugmentationCoinvariants.quotient ε (freeObject (I := I) (A := A) r) z)=
        specializePiece ε r z := rfl

def coinvariantComplex : ChainComplex (ModuleCat K) ℕ :=
  ((AugmentationCoinvariants.functor ε).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (resolution ε B hunit hε).complex

include hunit hε in
@[simp] theorem coinvariantComplex_d_quotient (r : ℕ) (z : lengthPiece I A (r+1)) :
    (coinvariantComplex ε B hunit hε).d (r+1) r
      (AugmentationCoinvariants.quotient ε (freeObject (I := I) (A := A) (r+1)) z)=
        AugmentationCoinvariants.quotient ε (freeObject (I := I) (A := A) r)
          (degreeDifferential B r z) := by
  simp only [coinvariantComplex,Functor.mapHomologicalComplex_obj_d,resolution,
    complex_d,AugmentationCoinvariants.map_quotient,ModuleCat.ofHom_apply]
  rfl

include hunit hε in
theorem coinvariantTermEquiv_comm (r : ℕ) :
    (coinvariantTermEquiv (I := I) ε (r+1)).toModuleIso.hom ≫
        (reducedComplex ε B hunit hε).d (r+1) r=
      (coinvariantComplex ε B hunit hε).d (r+1) r ≫
        (coinvariantTermEquiv (I := I) ε r).toModuleIso.hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  refine Quotient.inductionOn' z ?_
  intro x
  change (reducedComplex ε B hunit hε).d (r+1) r
      (coinvariantTermEquiv ε (r+1)
        (AugmentationCoinvariants.quotient ε (freeObject (I := I) (A := A) (r+1)) x))=
    coinvariantTermEquiv ε r ((coinvariantComplex ε B hunit hε).d (r+1) r
      (AugmentationCoinvariants.quotient ε (freeObject (I := I) (A := A) (r+1)) x))
  rw [coinvariantComplex_d_quotient,reducedComplex_d]
  change -(reducedDegreeDifferential B r
      (coinvariantTermEquiv ε (r+1)
        (AugmentationCoinvariants.quotient ε (freeObject (I := I) (A := A) (r+1)) x)))=
    coinvariantTermEquiv ε r
      (AugmentationCoinvariants.quotient ε (freeObject (I := I) (A := A) r)
        (degreeDifferential B r x))
  rw [coinvariantTermEquiv_quotient,coinvariantTermEquiv_quotient]
  apply Subtype.ext
  exact (specialize_differential ε B hε x.val).symm

def coinvariantComplexIso : coinvariantComplex ε B hunit hε ≅ reducedComplex ε B hunit hε :=
  HomologicalComplex.Hom.isoOfComponents
    (fun r ↦ (coinvariantTermEquiv (I := I) ε r).toModuleIso) (by
      intro i j hij
      change j+1=i at hij
      subst i
      exact coinvariantTermEquiv_comm ε B hunit hε j)

/-- The augmentation residue really is the coefficient module with the
left action through the original augmentation. -/
def residueAugmentationEquiv :
    Residue ε ≃ₗ[A] AugmentationCoinvariants.augmentationModule ε where
  toFun := residueEquivCoefficients ε
  invFun := (residueEquivCoefficients ε).symm
  left_inv := (residueEquivCoefficients ε).left_inv
  right_inv := (residueEquivCoefficients ε).right_inv
  map_add' := (residueEquivCoefficients ε).map_add
  map_smul' a q := by
    refine Quotient.inductionOn' q ?_
    intro x
    change ε (a*x)=ε a*ε x
    exact map_mul ε a x

/-- Actual ordinary augmentation Tor, computed by the actual adjacent-product
complex.  Ordinary augmentation tensoring is independently identified with
the balanced tensor product by `AugmentationCoinvariants.balancedEquiv`. -/
def ordinaryTorReducedBarIso (r : ℕ) :
    AugmentationCoinvariants.augmentationTor ε r ≅
      (reducedComplex ε B hunit hε).homology r :=
  ((AugmentationCoinvariants.derived ε r).mapIso
      (residueAugmentationEquiv ε).toModuleIso).symm ≪≫
    derivedCoinvariantsIso ε B hunit hε r ≪≫
      HomologicalComplex.homologyMapIso (coinvariantComplexIso ε B hunit hε) r

end PaperVerification.NoncommutativeBar
end
end
end TAF_LiteralSource_0484

