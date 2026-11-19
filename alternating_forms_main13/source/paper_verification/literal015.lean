module

public import paper_verification.literal014
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.Tactic
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.Data.Finsupp.Order
public import Mathlib.Tactic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.List.Sort
public import paper_verification.literal002
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Combinatorics.Young.YoungDiagram
import paper_verification.literal002
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
public import Mathlib.LinearAlgebra.Alternating.Basic
public import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.Tactic.FinCases
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.RingTheory.Ideal.Span
import Mathlib.LinearAlgebra.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import paper_verification.literal005
public import Mathlib.Combinatorics.Young.SemistandardTableau
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.MvPolynomial.Equiv

set_option Elab.async false

section TAF_LiteralSource_0630
/- Original module: PaperVerification.GenericVectorSectionEmptiness -/


/-!
# Generic emptiness when there are too many equations

The same parameter polynomial used for generic smoothness makes the gradients
of the original equations independent at every field-valued common zero.
Their number therefore cannot exceed the number of ambient differential
coordinates. If it does, the literal ideal of equations is the unit ideal.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
open KaehlerDifferential

namespace PaperVerification.GenericSectionDifferentials

variable {K R ι κ τ : Type*} [Field K] [CharZero K] [CommRing R]
  [Algebra K R] [Fintype ι] [Fintype κ] [Fintype τ] [DecidableEq κ]

/-- Nonvanishing of a parameter polynomial persists in every extension field. -/
lemma parameter_aeval_map_ne_zero {L : Type*} [Field L] [Algebra K L]
    (a : ι → K) (p : MvPolynomial ι K) (ha : MvPolynomial.aeval a p ≠ 0) :
    MvPolynomial.aeval (fun i => algebraMap K L (a i)) p ≠ 0 := by
  have he : algebraMap K L (MvPolynomial.aeval a p) =
      MvPolynomial.aeval (fun i => algebraMap K L (a i)) p := by
    simpa only [Algebra.ofId_apply] using
      (MvPolynomial.comp_aeval_apply a (Algebra.ofId K L) p)
  rw [← he]
  intro h
  exact ha ((algebraMap K L).injective (h.trans (map_zero _).symm))

/-- The number of equations is bounded by the ambient differential rank at
every field-valued common zero in the good parameter locus. -/
theorem linearSection_card_le_of_point [Algebra.FiniteType K R]
    (b : Module.Basis τ R Ω[R⁄K]) (v : Matrix κ ι R)
    (u : Matrix ι κ R) (hvu : v*u=1) (a : ι → K)
    (ha : MvPolynomial.aeval a (criticalAvoidancePolynomial b v u hvu) ≠ 0)
    {L : Type*} [Field L] [Algebra K L] (χ : R →ₐ[K] L)
    (hz : ∀ j, χ (linearSection v a j)=0) :
    Fintype.card κ ≤ Fintype.card τ := by
  have hz' : ∀ j, ∑ i, algebraMap K L (a i)*χ (v j i)=0 := by
    intro j
    simpa only [linearSection,map_sum,Algebra.smul_def,map_mul,AlgHom.commutes]
      using hz j
  have h := specialized_gradient_linearIndependent b v u hvu χ
    (fun i => algebraMap K L (a i)) (parameter_aeval_map_ne_zero a _ ha) hz'
  simpa only [Module.finrank_fintype_fun_eq_card] using h.fintype_card_le_finrank

/-- Above the dimension threshold, the equations generate the unit ideal on
the same nonempty principal open of the full parameter space. -/
theorem linearSection_ideal_eq_top_of_more_equations [Algebra.FiniteType K R]
    (b : Module.Basis τ R Ω[R⁄K]) (v : Matrix κ ι R)
    (u : Matrix ι κ R) (hvu : v*u=1) (a : ι → K)
    (ha : MvPolynomial.aeval a (criticalAvoidancePolynomial b v u hvu) ≠ 0)
    (hcard : Fintype.card τ < Fintype.card κ) :
    Ideal.span (Set.range (linearSection v a)) = ⊤ := by
  classical
  by_contra hI
  obtain ⟨J,hJ,hIJ⟩ := Ideal.exists_le_maximal _ hI
  letI : J.IsMaximal := hJ
  letI : Field (R ⧸ J) := Ideal.Quotient.field J
  have hz : ∀ j, (Ideal.Quotient.mkₐ K J) (linearSection v a j)=0 := by
    intro j
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (hIJ (Ideal.subset_span (Set.mem_range_self j)))
  exact (not_le_of_gt hcard)
    (linearSection_card_le_of_point b v u hvu a ha (Ideal.Quotient.mkₐ K J) hz)

end PaperVerification.GenericSectionDifferentials
end
end
end TAF_LiteralSource_0630

section TAF_LiteralSource_0631
/- Original module: PaperVerification.LocalJacobianCriterion -/


/-!
# The local Jacobian criterion in terms of defining equations

Independence of the defining differentials over the residue field splits the
cotangent map. This formulation does not assume that the conormal module is
already free, or that the given equations are already a regular sequence.
-/

@[expose] public section
noncomputable section
open scoped BigOperators TensorProduct
open KaehlerDifferential

namespace PaperVerification.GenericSectionDifferentials

/-- Over a local ring, independence modulo the maximal ideal splits a finite
family of vectors in a finite free module. -/
theorem linearCombination_split_of_residue_independent
    {R M κ : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    [Fintype κ] (v : κ → M)
    (hv : LinearIndependent (IsLocalRing.ResidueField R)
      (fun i => (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] v i)) :
    ∃ l : M →ₗ[R] (κ → R),
      l.comp (Fintype.linearCombination R v) = LinearMap.id := by
  classical
  let k := IsLocalRing.ResidueField R
  let F := Fintype.linearCombination R v
  let b := (Pi.basisFun R κ).baseChange k
  have he : F.baseChange k = b.constr k (fun i => (1 : k) ⊗ₜ[R] v i) := by
    apply b.ext
    intro i
    simp [F, b, Module.Basis.baseChange_apply]
  apply (IsLocalRing.split_injective_iff_lTensor_residueField_injective F).mpr
  change Function.Injective (F.baseChange k)
  rw [he]
  exact b.injective_constr_of_linearIndependent hv

/-- Equations whose differentials are independent in the residue field cut
out a formally smooth local quotient of a smooth ambient algebra. -/
theorem formallySmooth_of_residue_independent_equations
    {K S κ : Type*} [CommRing K] [CommRing S] [IsLocalRing S]
    [Algebra K S] [Fintype κ]
    (P : Algebra.Extension K S) [Algebra.FormallySmooth K P.Ring]
    [Module.Free P.Ring Ω[P.Ring⁄K]] [Module.Finite P.Ring Ω[P.Ring⁄K]]
    (f : κ → P.Ring) (hf : Ideal.span (Set.range f)=P.ker)
    (hind : LinearIndependent (IsLocalRing.ResidueField S)
      (fun i => (1 : IsLocalRing.ResidueField S) ⊗ₜ[S]
        ((1 : S) ⊗ₜ[P.Ring] D K P.Ring (f i)))) :
    Algebra.FormallySmooth K S := by
  let g : κ → P.Cotangent := fun i => Algebra.Extension.Cotangent.mk
    ⟨f i, hf ▸ Ideal.subset_span (Set.mem_range_self i)⟩
  let F := Fintype.linearCombination S g
  let J := Fintype.linearCombination S (fun i => P.cotangentComplex (g i))
  have hspan : Submodule.span S (Set.range g)=⊤ :=
    Algebra.Extension.Cotangent.span_eq_top_of_span_eq_ker f hf
  have hsurj : Function.Surjective F :=
    (span_range_eq_top_iff_surjective_fintypeLinearCombination S g).mp hspan
  have hJ : J=P.cotangentComplex.comp F := by
    ext x
    simp [J,F,Fintype.linearCombination_apply]
  have hind' : LinearIndependent (IsLocalRing.ResidueField S)
      (fun i => (1 : IsLocalRing.ResidueField S) ⊗ₜ[S]
        P.cotangentComplex (g i)) := by
    simpa only [g,Algebra.Extension.cotangentComplex_mk] using hind
  obtain ⟨l,hl⟩ := linearCombination_split_of_residue_independent
    (fun i => P.cotangentComplex (g i)) hind'
  apply P.formallySmooth_iff_split_injection.mpr
  refine ⟨F.comp l,?_⟩
  apply LinearMap.ext
  intro x
  obtain ⟨y,rfl⟩ := hsurj x
  have hy := LinearMap.congr_fun hl y
  change l (J y)=y at hy
  rw [hJ,LinearMap.comp_apply] at hy
  exact congrArg F hy

end PaperVerification.GenericSectionDifferentials
end
end
end TAF_LiteralSource_0631

section TAF_LiteralSource_0632
/- Original module: PaperVerification.RectangularReflection -/


/-!
# Rectangular reversal and the coefficient pairing

The reversal of a polynomial supported in an exponent box `0 ≤ a ≤ d`
sends `X^a` to `X^(d-a)`.  Unlike inversion in a rational function field,
this is an actual linear map on multivariate polynomials.  The top
coefficient of the product with its reversal is the sum of squares of
its coefficients.  This supplies an elementary positivity argument for
the Chern pairing in Section 4 of the paper.

No cohomology or Chow group is defined in this file.
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace PaperVerification.RectangularReflection

open MvPolynomial

variable {σ R : Type*} [CommSemiring R]

/-- Every monomial of `p` lies in the exponent box bounded by `d`. -/
def BoundedBy (d : σ →₀ ℕ) (p : MvPolynomial σ R) : Prop :=
  ∀ a ∈ p.support, a ≤ d

/-- Reflect exponents in the upper corner of a box.  Outside the box
the truncated subtraction still defines a linear map; its reflection
properties are used only with the explicitly stated support bound. -/
def reflect (d : σ →₀ ℕ) : MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  AddMonoidAlgebra.mapDomainLinearMap R R (fun a => d - a)

@[simp] theorem reflect_monomial (d a : σ →₀ ℕ) (r : R) :
    reflect d (monomial a r) = monomial (d-a) r := by
  exact AddMonoidAlgebra.mapDomainLinearMap_single _ _ _

theorem reflect_apply (d : σ →₀ ℕ) (p : MvPolynomial σ R) :
    reflect d p = ∑ a ∈ p.support, monomial (d-a) (p.coeff a) := by
  classical
  conv_lhs => rw [← support_sum_monomial_coeff p]
  simp only [map_sum, reflect_monomial]

theorem boundedBy_reflect (d : σ →₀ ℕ) (p : MvPolynomial σ R) :
    BoundedBy d (reflect d p) := by
  classical
  intro a ha
  rw [reflect_apply] at ha
  obtain ⟨b,hb,hab⟩ := Finset.mem_biUnion.mp (support_sum ha)
  have heq : a = d-b := by
    simpa only [Finset.mem_singleton] using support_monomial_subset hab
  rw [heq]
  exact tsub_le_self

theorem boundedBy_mul {d e : σ →₀ ℕ} {p q : MvPolynomial σ R}
    (hp : BoundedBy d p) (hq : BoundedBy e q) :
    BoundedBy (d+e) (p*q) := by
  classical
  intro a ha
  obtain ⟨b,hb,c,hc,rfl⟩ := Finset.mem_add.mp (support_mul p q ha)
  exact add_le_add (hp b hb) (hq c hc)

theorem reflect_reflect {d : σ →₀ ℕ} {p : MvPolynomial σ R}
    (hp : BoundedBy d p) : reflect d (reflect d p) = p := by
  classical
  rw [reflect_apply d p]
  simp only [map_sum, reflect_monomial]
  calc
    _ = ∑ a ∈ p.support, monomial a (p.coeff a) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [tsub_tsub_cancel_of_le (hp a ha)]
    _ = p := support_sum_monomial_coeff p

theorem reflect_mul {d e : σ →₀ ℕ} {p q : MvPolynomial σ R}
    (hp : BoundedBy d p) (hq : BoundedBy e q) :
    reflect (d+e) (p*q) = reflect d p * reflect e q := by
  classical
  calc
    _ = ∑ a ∈ p.support, ∑ b ∈ q.support,
        monomial ((d+e)-(a+b)) (p.coeff a*q.coeff b) := by
      conv_lhs => rw [← support_sum_monomial_coeff p, ← support_sum_monomial_coeff q]
      simp only [Finset.sum_mul, Finset.mul_sum, map_sum, monomial_mul_monomial,
        reflect_monomial]
      exact Finset.sum_comm
    _ = ∑ a ∈ p.support, ∑ b ∈ q.support,
        monomial ((d-a)+(e-b)) (p.coeff a*q.coeff b) := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      have h : (d+e)-(a+b) = (d-a)+(e-b) := by
        ext i
        have h₁ := hp a ha i
        have h₂ := hq b hb i
        simp only [Finsupp.add_apply, Finsupp.tsub_apply]
        omega
      rw [h]
    _ = reflect d p * reflect e q := by
      rw [reflect_apply, reflect_apply]
      simp only [Finset.sum_mul, Finset.mul_sum, monomial_mul_monomial]
      exact Finset.sum_comm

/-- Top coefficient against the reversal is the coefficient dot product. -/
theorem coeff_mul_reflect {d : σ →₀ ℕ} (p q : MvPolynomial σ R)
    (hq : BoundedBy d q) :
    (p * reflect d q).coeff d = ∑ a ∈ q.support, p.coeff a*q.coeff a := by
  classical
  rw [reflect_apply, Finset.mul_sum, coeff_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [coeff_mul_monomial', ite_eq_left (tsub_le_self),
    tsub_tsub_cancel_of_le (hq a ha)]

theorem coeff_self_mul_reflect {d : σ →₀ ℕ} (p : MvPolynomial σ R)
    (hp : BoundedBy d p) :
    (p * reflect d p).coeff d = ∑ a ∈ p.support, (p.coeff a)^2 := by
  rw [coeff_mul_reflect p p hp]
  simp only [pow_two]

section Uniform

variable [Fintype σ]

/-- The exponent assigning the same bound to every variable. -/
def uniformExponent (c : ℕ) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun _ => c

@[simp] theorem uniformExponent_apply (c : ℕ) (i : σ) :
    uniformExponent (σ := σ) c i = c := rfl

theorem uniformExponent_add (c d : ℕ) :
    uniformExponent (σ := σ) (c+d) = uniformExponent c + uniformExponent d := by
  ext i
  rfl

theorem mapDomain_uniformExponent (e : Equiv.Perm σ) (c : ℕ) :
    (uniformExponent (σ := σ) c).mapDomain e = uniformExponent c := by
  ext i
  obtain ⟨j,rfl⟩ := e.surjective i
  rw [Finsupp.mapDomain_apply_of_injective e.injective]
  rfl

theorem rename_reflect (e : Equiv.Perm σ) (c : ℕ) (p : MvPolynomial σ R) :
    rename e (reflect (uniformExponent c) p) =
      reflect (uniformExponent c) (rename e p) := by
  classical
  conv_lhs => rw [← support_sum_monomial_coeff p]
  conv_rhs => rw [← support_sum_monomial_coeff p]
  simp only [map_sum, reflect_monomial, rename_monomial]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finsupp.mapDomain_tsub e.injective, mapDomain_uniformExponent]

theorem reflect_isSymmetric {p : MvPolynomial σ R} (hp : p.IsSymmetric) (c : ℕ) :
    (reflect (uniformExponent c) p).IsSymmetric := by
  intro e
  rw [rename_reflect, hp e]

end Uniform

section Ordered

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Positivity is a proof over an ordered field, not a numerical test. -/
theorem coeff_self_mul_reflect_pos {d : σ →₀ ℕ} {p : MvPolynomial σ K}
    (hp : BoundedBy d p) (hne : p ≠ 0) :
    0 < (p * reflect d p).coeff d := by
  classical
  rw [coeff_self_mul_reflect p hp]
  have hsupport : p.support.Nonempty := by
    by_contra hn
    have hz : p.support = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    exact hne (by ext a; exact notMem_support_iff.mp (by simp [hz]))
  obtain ⟨a,ha⟩ := hsupport
  exact Finset.sum_pos' (fun b _ => sq_nonneg (p.coeff b))
    ⟨a,ha,sq_pos_of_ne_zero (mem_support_iff.mp ha)⟩

end Ordered

end PaperVerification.RectangularReflection
end
end
end TAF_LiteralSource_0632

section TAF_LiteralSource_0633
/- Original module: TauCeti.Combinatorics.Young.OfRowLens -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Young diagrams from a bounded family of row lengths

Mathlib builds a Young diagram from a weakly decreasing `List ℕ` of row lengths
(`YoungDiagram.ofRowLens`) and reads that list back off a diagram (`YoungDiagram.rowLens`); the
two are inverse only after the *positive* entries are singled out, since `rowLens` never records
a row of length `0`.

Indexing the row lengths by `Fin n` rather than by a list removes that mismatch: a weakly
decreasing `f : Fin n → ℕ` is allowed to end in zeros, and `YoungDiagram.ofRowLensFin`
turns any such family into the diagram whose `i`-th row has length `f i` for `i < n` and which has
no row beyond. Reading the first `n` row lengths back off is then an honest inverse on the
diagrams with at most `n` rows — the form consumed when partitions with a bounded number of rows
are matched against weight data for `GL n`.

## Main definitions

* `YoungDiagram.ofRowLensFin`: the Young diagram with prescribed weakly decreasing row
  lengths `f : Fin n → ℕ` and no further rows.

## Main results

* `YoungDiagram.rowLen_ofRowLensFin` and
  `YoungDiagram.rowLen_ofRowLensFin_eq_zero_of_le`: the row lengths of `ofRowLensFin f hf`
  are `f` on `Fin n` and `0` beyond it.
* `YoungDiagram.colLen_zero_ofRowLensFin_le` and
  `YoungDiagram.ofRowLensFin_rowLen`: `ofRowLensFin` lands in the diagrams with at most
  `n` rows, and is there inverse to reading off the first `n` row lengths.
* `YoungDiagram.card_ofRowLensFin`: its number of cells is `∑ i, f i`.
-/

public section

namespace YoungDiagram

variable {n : ℕ}

/-- The Young diagram whose first `n` rows have the prescribed weakly decreasing lengths
`f : Fin n → ℕ`, and which has no row beyond.  Unlike `YoungDiagram.ofRowLens`, the family `f`
may take the value `0`; such an entry simply contributes an empty row. -/
def ofRowLensFin (f : Fin n → ℕ) (hf : Antitone f) : _root_.YoungDiagram :=
  _root_.YoungDiagram.ofRowLens (List.ofFn f) hf.sortedGE_ofFn

/-- The rows of `ofRowLensFin f hf` indexed by `Fin n` have the prescribed lengths. -/
@[simp]
theorem rowLen_ofRowLensFin (f : Fin n → ℕ) (hf : Antitone f) (i : Fin n) :
    (ofRowLensFin f hf).rowLen i = f i := by
  have h : (i : ℕ) < (List.ofFn f).length := by simp
  simpa [ofRowLensFin] using
    _root_.YoungDiagram.rowLen_ofRowLens (w := List.ofFn f) (hw := hf.sortedGE_ofFn) ⟨i, h⟩

/-- The rows of `ofRowLensFin f hf` past the `n` prescribed ones are empty. -/
@[simp]
theorem rowLen_ofRowLensFin_eq_zero_of_le (f : Fin n → ℕ) (hf : Antitone f) {i : ℕ} (hi : n ≤ i) :
    (ofRowLensFin f hf).rowLen i = 0 := by
  by_contra h
  have hmem : ((i, 0) : ℕ × ℕ) ∈ ofRowLensFin f hf :=
    _root_.YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero h)
  grind [ofRowLensFin, _root_.YoungDiagram.mem_ofRowLens, List.length_ofFn]

/-- `ofRowLensFin f hf` has at most `n` rows. -/
theorem colLen_zero_ofRowLensFin_le (f : Fin n → ℕ) (hf : Antitone f) :
    (ofRowLensFin f hf).colLen 0 ≤ n := by
  by_contra h
  have hmem : ((n, 0) : ℕ × ℕ) ∈ ofRowLensFin f hf :=
    _root_.YoungDiagram.mem_iff_lt_colLen.mpr (Nat.lt_of_not_le h)
  grind [_root_.YoungDiagram.mem_iff_lt_rowLen, rowLen_ofRowLensFin_eq_zero_of_le]

/-- Reading the first `n` row lengths off a Young diagram with at most `n` rows recovers it. -/
theorem ofRowLensFin_rowLen (μ : _root_.YoungDiagram) (hμ : μ.colLen 0 ≤ n) :
    ofRowLensFin (fun i : Fin n => μ.rowLen i) (fun _ _ h => μ.rowLen_anti _ _ h) = μ := by
  refine rowLen_injective (funext fun i => ?_)
  by_cases hi : i < n
  · simpa using rowLen_ofRowLensFin _ _ ⟨i, hi⟩
  · grind [rowLen_ofRowLensFin_eq_zero_of_le, rowLen_eq_zero_of_colLen_le]

/-- `ofRowLensFin f hf` has `∑ i, f i` cells. -/
@[simp]
theorem card_ofRowLensFin (f : Fin n → ℕ) (hf : Antitone f) :
    (ofRowLensFin f hf).card = ∑ i, f i := by
  rw [card_eq_sum_range_rowLen _ (colLen_zero_ofRowLensFin_le f hf),
    ← Fin.sum_univ_eq_sum_range (fun i => (ofRowLensFin f hf).rowLen i) n]
  exact Finset.sum_congr rfl fun i _ => rowLen_ofRowLensFin f hf i

end YoungDiagram

end
end TAF_LiteralSource_0633

section TAF_LiteralSource_0634
/- Original module: TauCeti.Data.Fin.StrictAnti -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Strictly antitone sequences indexed by `Fin n`

A sequence `f : Fin n → α` is strictly antitone when it strictly decreases along the indices.  This
file records three facts about such sequences, used for beta-numbers of Young diagrams and the Pieri
rule for Schur polynomials.

Over `ℕ` a strictly antitone sequence drops by at least one at each step, so it drops by at least
the index gap: `StrictAnti.add_sub_le_nat`.  This is what makes a strictly decreasing sequence of
`n` natural numbers a sequence of beta-numbers of a Young diagram.  The increasing analogue indexed
by all of `ℕ` is `StrictMono.add_le_nat`.

Over any linear order, an *injective* sequence becomes strictly antitone after precomposition with a
suitable permutation of the indices (`Function.Injective.exists_strictAnti_comp`), and over any
partial order that permutation is unique (`StrictAnti.perm_eq`): sorting into decreasing order is
possible and unambiguous.  Mathlib's `Tuple.sort` sorts into *increasing* order; composing with the
reversal `Fin.revPerm` turns it around.

## Main results

* `StrictAnti.add_sub_le_nat`: a strictly antitone sequence of naturals drops by at least the index
  gap.
* `Function.Injective.exists_strictAnti_comp`: an injective sequence can be sorted into decreasing
  order.
* `StrictAnti.perm_eq`: the sorting permutation is unique.
-/

public section

open Equiv

variable {n : ℕ} {α : Type*}

/-- **A strictly antitone sequence of naturals drops by at least the index gap**: it loses at least
one unit at each step, hence at least `j - i` units between the indices `i ≤ j`. -/
theorem StrictAnti.add_sub_le_nat {η : Fin n → ℕ} (hη : StrictAnti η) {i j : Fin n}
    (hij : i ≤ j) : η j + ((j : ℕ) - (i : ℕ)) ≤ η i := by
  obtain ⟨j, hj⟩ := j
  simp only [Fin.le_def] at hij
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ k hik ih =>
    have := hη (Fin.mk_lt_mk.mpr k.lt_succ_self : (⟨k, by omega⟩ : Fin n) < ⟨k + 1, hj⟩)
    grind

/-- **Sorting into decreasing order.**  Precomposing an injective sequence indexed by `Fin n` with
a suitable permutation of the indices makes it strictly antitone. -/
theorem Function.Injective.exists_strictAnti_comp [LinearOrder α] {f : Fin n → α}
    (hf : Function.Injective f) : ∃ τ : Perm (Fin n), StrictAnti (f ∘ τ) := by
  have hmono : StrictMono (f ∘ Tuple.sort f) :=
    (Tuple.monotone_sort f).strictMono_of_injective (hf.comp (Tuple.sort f).injective)
  refine ⟨Fin.revPerm.trans (Tuple.sort f), fun i j hij => ?_⟩
  simpa using hmono (Fin.rev_lt_rev.mpr hij)

/-- **The sorting permutation is unique.**  Two permutations of the indices that both make a
sequence strictly antitone are equal. -/
theorem StrictAnti.perm_eq [PartialOrder α] {f : Fin n → α} {τ₁ τ₂ : Perm (Fin n)}
    (h₁ : StrictAnti (f ∘ τ₁)) (h₂ : StrictAnti (f ∘ τ₂)) : τ₁ = τ₂ :=
  Equiv.ext <| congrFun <| ((τ₁.injective_comp f).mp h₁.injective).comp_left
    (Tuple.unique_antitone h₁.antitone h₂.antitone)
end
end TAF_LiteralSource_0634

section TAF_LiteralSource_0635
/- Original module: TauCeti.Combinatorics.Young.BetaNumbers -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Beta-numbers of a Young diagram

Fix a Young diagram `μ` and a bound `r` on its number of rows. The `i`-th **beta-number**
`YoungDiagram.betaNumber μ r i = μ.rowLen i + (r - 1 - i)` is the length of row `i` plus the number
`r - 1 - i` of rows of the bounding `r`-row strip that lie below it. Adding that shift to the weakly
decreasing row lengths makes the beta-numbers strictly decrease across the indices `i < j < r`
inside the bound, so those `r` numbers are pairwise distinct; that is the whole point of the
construction.  This file also records that the natural-number product of their differences casts
to the corresponding integer product.

Beta-numbers are the bookkeeping device behind the Frobenius determinant formula and the
Frame-Robinson-Thrall route to the hook-length formula. Their relation to hook lengths --- for the
exact row count `r = μ.colLen 0` the beta-numbers of the nonempty rows `i < μ.colLen 0` are the
hook lengths of the first column, and in general they describe a row of hook lengths --- needs the
hook-length API and is developed in `TauCeti/Combinatorics/Young/HookLength/BetaNumbers.lean`.

## Main definitions

* `YoungDiagram.betaNumber`: the beta-numbers of `μ` relative to a bound `r` on its number of rows.

## Main results

* `YoungDiagram.betaNumber_lt_betaNumber`: the beta-numbers strictly decrease across the indices
  `i < j < r` inside the bound.
* `YoungDiagram.injOn_betaNumber`: the beta-numbers of the indices `i < r` are pairwise distinct.
* `YoungDiagram.strictAnti_betaNumber`: the beta-numbers relative to `r` are strictly antitone on
  `Fin r`, and `YoungDiagram.exists_eq_betaNumber_of_strictAnti`: conversely every strictly antitone
  `Fin r → ℕ` is the sequence of beta-numbers of a diagram with at most `r` rows.
* `YoungDiagram.eq_of_betaNumber_eq`: a Young diagram with at most `r` rows is determined by its
  beta-numbers of the indices `i < r`.
* `YoungDiagram.sum_betaNumber`: the beta-numbers of a diagram with at most `r` rows total its
  number of cells plus the staircase `∑_j (r - 1 - j)`.
* `YoungDiagram.cast_prod_betaNumber_sub`: casts the product of beta-number differences from
  `ℕ` to `ℤ`.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I, Section
  1, Example 1, for beta-numbers and the description of a row of hook lengths by them.
-/

public section

namespace YoungDiagram

variable {μ : YoungDiagram} {r i j : ℕ}

/-- The `i`-th **beta-number** of a Young diagram `μ`, relative to a bound `r` on its number of
rows: the length of row `i` plus the number `r - 1 - i` of rows of the bounding `r`-row strip that
lie below it. For `r = μ.colLen 0` and a nonempty row `i < μ.colLen 0` this is the hook length of
the first cell of row `i`; see `YoungDiagram.betaNumber_eq_hookLength`. -/
def betaNumber (μ : YoungDiagram) (r i : ℕ) : ℕ := μ.rowLen i + (r - 1 - i)

theorem betaNumber_def (μ : YoungDiagram) (r i : ℕ) :
    μ.betaNumber r i = μ.rowLen i + (r - 1 - i) := (rfl)

/-- The beta-numbers strictly decrease along the rows, because the row lengths are weakly
decreasing while the shifts `r - 1 - i` strictly decrease. -/
theorem betaNumber_lt_betaNumber (μ : YoungDiagram) (hij : i < j) (hj : j < r) :
    μ.betaNumber r j < μ.betaNumber r i := by
  have := μ.rowLen_anti i j hij.le
  simp only [betaNumber_def]
  omega

-- The antecedents of `betaNumber_lt_betaNumber` mention no beta-number, so the `@[grind →]`
-- pattern does not exist; the useful trigger is a pair of beta-numbers sharing a bound, which is
-- what makes `grind` derive `βᵢ ≠ βⱼ` and `βᵢ - βⱼ ≠ 0` on its own.
grind_pattern betaNumber_lt_betaNumber => μ.betaNumber r i, μ.betaNumber r j

/-- The beta-numbers of the rows inside the bound strictly decrease. -/
theorem strictAntiOn_betaNumber (μ : YoungDiagram) (r : ℕ) :
    StrictAntiOn (μ.betaNumber r) (Set.Iio r) :=
  fun _ _ _ hb hab => μ.betaNumber_lt_betaNumber hab (Set.mem_Iio.mp hb)

/-- The beta-numbers of the rows inside the bound are pairwise distinct. -/
theorem injOn_betaNumber (μ : YoungDiagram) (r : ℕ) :
    Set.InjOn (μ.betaNumber r) (Set.Iio r) :=
  (μ.strictAntiOn_betaNumber r).injOn

/-- **A Young diagram is determined by its beta-numbers**: two diagrams with at most `r` rows whose
beta-numbers relative to `r` agree at every index `i < r` are equal.  Inside the bound the row
lengths are recovered by subtracting the common shift `r - 1 - i`, and outside it both diagrams
have empty rows. -/
theorem eq_of_betaNumber_eq {ν : YoungDiagram} (hμ : μ.colLen 0 ≤ r) (hν : ν.colLen 0 ≤ r)
    (h : ∀ i < r, μ.betaNumber r i = ν.betaNumber r i) : μ = ν := by
  refine rowLen_injective (funext fun i => ?_)
  by_cases hi : i < r
  · have := h i hi
    rw [betaNumber_def, betaNumber_def] at this
    omega
  · rw [rowLen_eq_zero_of_colLen_le (hμ.trans (Nat.not_lt.mp hi)),
      rowLen_eq_zero_of_colLen_le (hν.trans (Nat.not_lt.mp hi))]

/-- The beta-numbers relative to a bound `r` strictly decrease along the indices `Fin r`. -/
theorem strictAnti_betaNumber (μ : YoungDiagram) (r : ℕ) :
    StrictAnti fun j : Fin r => μ.betaNumber r j :=
  fun _ j hij => μ.betaNumber_lt_betaNumber (Fin.lt_def.mp hij) j.isLt

/-- **A strictly decreasing sequence of naturals is a sequence of beta-numbers.**  Every strictly
antitone `η : Fin r → ℕ` is the sequence of beta-numbers relative to `r` of a Young diagram with at
most `r` rows, unique by `YoungDiagram.eq_of_betaNumber_eq`.  Strict decrease is exactly what makes
the differences `η j - (r - 1 - j)` weakly decreasing and nonnegative, hence row lengths. -/
theorem exists_eq_betaNumber_of_strictAnti {r : ℕ} {η : Fin r → ℕ} (hη : StrictAnti η) :
    ∃ μ : YoungDiagram, μ.colLen 0 ≤ r ∧ ∀ j : Fin r, μ.betaNumber r j = η j := by
  have hshift : ∀ j : Fin r, r - 1 - (j : ℕ) ≤ η j := by
    intro j
    have hr : 0 < r := Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt
    set L : Fin r := ⟨r - 1, by omega⟩ with _hLdef
    have hLval : (L : ℕ) = r - 1 := rfl
    have hle : j ≤ L := Fin.le_def.mpr (by rw [hLval]; omega)
    have hgap := hη.add_sub_le_nat hle
    rw [hLval] at hgap
    omega
  have hanti : Antitone fun j : Fin r => η j - (r - 1 - (j : ℕ)) := by
    intro i j hij
    dsimp only
    have hgap := hη.add_sub_le_nat hij
    have hi := hshift i
    have hj := hshift j
    have _ : (i : ℕ) ≤ (j : ℕ) := Fin.le_def.mp hij
    have _ : (j : ℕ) < r := j.isLt
    omega
  refine ⟨ofRowLensFin _ hanti, colLen_zero_ofRowLensFin_le _ hanti, fun j => ?_⟩
  rw [betaNumber_def, rowLen_ofRowLensFin]
  have := hshift j
  omega


open Finset

/-- **The beta-numbers of a diagram total its size plus the staircase.**  For a diagram with at most
`r` rows the row lengths add up to the number of cells, and the shifts add up separately. -/
theorem sum_betaNumber (μ : YoungDiagram) {r : ℕ} (hμ : μ.colLen 0 ≤ r) :
    ∑ j : Fin r, μ.betaNumber r j = μ.card + ∑ j : Fin r, (r - 1 - (j : ℕ)) := by
  simp only [betaNumber_def]
  rw [Finset.sum_add_distrib, card_eq_sum_range_rowLen μ hμ,
    Fin.sum_univ_eq_sum_range (fun i => μ.rowLen i) r]

/-- The Vandermonde-style product of the differences of the beta-numbers is computed by the same
formula over `ℤ`, the differences being nonnegative. -/
theorem cast_prod_betaNumber_sub (μ : YoungDiagram) (r : ℕ) :
    ((∏ k ∈ range r, ∏ l ∈ Ico (k + 1) r, (μ.betaNumber r k - μ.betaNumber r l) : ℕ) : ℤ)
      = ∏ k ∈ range r, ∏ l ∈ Ico (k + 1) r,
          ((μ.betaNumber r k : ℤ) - (μ.betaNumber r l : ℤ)) := by
  rw [Nat.cast_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Nat.cast_prod]
  refine Finset.prod_congr rfl fun l hl => ?_
  rw [mem_Ico] at hl
  exact Nat.cast_sub (μ.betaNumber_lt_betaNumber (by omega) hl.2).le

end YoungDiagram
end
end TAF_LiteralSource_0635

section TAF_LiteralSource_0636
/- Original module: TauCeti.LinearAlgebra.BilinearForm.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Basic identities for bilinear forms

Away from characteristic two a bilinear form cannot be both symmetric and alternating without
being zero: symmetry and alternation give `B x y = B y x` and `B x y = -B y x`, so `2 * B x y = 0`,
and cancelling the `2` leaves `B x y = 0`.

That cancellation is all the hypothesis on the ring there is: `2` has to be regular, and nothing
is asked of any other element, so the statement covers rings with zero divisors elsewhere.  Over a
field, or over any domain, `IsRegular.of_ne_zero` supplies the hypothesis from `(2 : R) ≠ 0`.

For a left-separating alternating bilinear map on a module with a two-element basis, its value
on that basis has trivial scalar annihilator. This holds over any commutative semiring and for
maps valued in an arbitrary module.

## Main results

* `TauCeti.BilinForm.eq_zero_of_isSymm_of_isAlt`: a symmetric alternating form over a ring in which
  `2` is regular is zero.
* `TauCeti.BilinForm.nondegenerate_smul_iff`: scalar multiplication by a regular element
  preserves nondegeneracy.
* `TauCeti.BilinForm.nondegenerate_neg_iff`: negating a bilinear form preserves nondegeneracy.
* `Module.Basis.dualBasis_smul_apply`: the dual basis of a scalar multiple of a form.
* `LinearMap.BilinForm.IsSymm.apply_add_self`: polarization of a symmetric bilinear form.
* `LinearMap.IsAlt.eq_zero_of_smul_apply_basis_eq_zero`: the value of a left-separating
  alternating bilinear map on a two-element basis has trivial scalar annihilator.
-/

public section

namespace LinearMap.IsAlt

/-- The value of a left-separating alternating bilinear map on a two-element basis has trivial
scalar annihilator, over any commutative semiring. -/
theorem eq_zero_of_smul_apply_basis_eq_zero {R M N : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (b : Module.Basis (Fin 2) R M) {ω : M →ₗ[R] M →ₗ[R] N} (halt : ω.IsAlt)
    (hω : ω.SeparatingLeft) {r : R} (hr : r • ω (b 0) (b 1) = 0) : r = 0 := by
  have hb : r • b 0 = 0 := hω _ fun y ↦ by
    conv_lhs => rw [← b.sum_repr y]
    simp only [Fin.sum_univ_two, map_add, map_smul, smul_apply, LinearMap.smul_apply, halt (b 0), hr, smul_zero,
      add_zero]
  simpa using congr(b.repr $hb 0)

end LinearMap.IsAlt

namespace LinearMap.BilinForm.IsSymm

/-- Polarization of a symmetric bilinear form over a commutative semiring. -/
theorem apply_add_self {R M : Type*} [CommSemiring R] [AddCommMonoid M]
    [Module R M] {B : LinearMap.BilinForm R M} (hB : B.IsSymm) (x y : M) :
    B (x + y) (x + y) = B x x + B y y + 2 * B x y := by
  simp only [map_add, LinearMap.add_apply, hB.eq y x]
  ring

end LinearMap.BilinForm.IsSymm

namespace TauCeti

open _root_.LinearMap (BilinForm)

namespace BilinForm

/-- **Away from characteristic two a symmetric alternating form is zero**: symmetry and alternation
force `2 * B x y = 0`, and a regular `2` cancels. -/
theorem eq_zero_of_isSymm_of_isAlt {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (h2 : IsLeftRegular (2 : R)) {B : BilinForm R M} (hsymm : B.IsSymm)
    (halt : B.IsAlt) : B = 0 := by
  refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
  have hzero : (2 : R) * B x y = 2 * 0 := by
    rw [mul_zero]
    linear_combination hsymm.eq x y - halt.neg_eq x y
  simpa using h2 hzero

/-- A scalar multiple of a bilinear form by a regular element is nondegenerate if and only if
the original form is nondegenerate. -/
@[simp]
theorem nondegenerate_smul_iff {R M : Type*} [CommSemiring R] [AddCommMonoid M]
    [Module R M] {B : BilinForm R M} {c : R} (hc : IsRegular c) :
    (c • B).Nondegenerate ↔ B.Nondegenerate := by
  constructor
  · rintro ⟨hl, hr⟩
    refine ⟨fun x hx ↦ hl x fun y ↦ ?_, fun y hy ↦ hr y fun x ↦ ?_⟩
    · specialize hx y
      simp only [LinearMap.smul_apply, smul_eq_mul, hx, mul_zero]
    · specialize hy x
      simp only [LinearMap.smul_apply, smul_eq_mul, hy, mul_zero]
  · rintro ⟨hl, hr⟩
    refine ⟨fun x hx ↦ hl x fun y ↦ ?_, fun y hy ↦ hr y fun x ↦ ?_⟩
    · specialize hx y
      simp only [LinearMap.smul_apply, smul_eq_mul, hc.left.mul_left_eq_zero_iff] at hx
      exact hx
    · specialize hy x
      simp only [LinearMap.smul_apply, smul_eq_mul, hc.left.mul_left_eq_zero_iff] at hy
      exact hy

/-- Negating a bilinear form preserves nondegeneracy. -/
@[simp]
theorem nondegenerate_neg_iff {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {B : BilinForm R M} :
    (-B).Nondegenerate ↔ B.Nondegenerate := by
  rw [← neg_one_smul R B]
  exact nondegenerate_smul_iff (isUnit_neg_one : IsUnit (-1 : R)).isRegular

end BilinForm

end TauCeti

namespace Module.Basis

/-- The basis dual to `b` for a nonzero scalar multiple `c • B` of a nondegenerate bilinear form
is `c⁻¹` times the basis dual to `b` for `B`. -/
@[simp]
theorem dualBasis_smul_apply {K V ι : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Finite ι] [DecidableEq ι] (b : Module.Basis ι K V)
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate) (c : K) (hc : c ≠ 0) (i : ι) :
    LinearMap.BilinForm.dualBasis (c • B)
        ((TauCeti.BilinForm.nondegenerate_smul_iff (IsRegular.of_ne_zero hc)).mpr hB) b i =
      c⁻¹ • LinearMap.BilinForm.dualBasis B hB b i := by
  let hBc : (c • B).Nondegenerate :=
    (TauCeti.BilinForm.nondegenerate_smul_iff (IsRegular.of_ne_zero hc)).mpr hB
  apply LinearMap.ker_eq_bot.mp hBc.ker_eq_bot
  apply b.ext
  intro j
  simp only [map_smul]
  rw [LinearMap.BilinForm.apply_dualBasis_left]
  simp only [LinearMap.smul_apply, smul_eq_mul]
  rw [LinearMap.BilinForm.apply_dualBasis_left]
  split_ifs
  · simp only [mul_one, inv_mul_cancel₀ hc]
  · simp only [mul_zero]

end Module.Basis
end
end TAF_LiteralSource_0636

section TAF_LiteralSource_0637
/- Original module: TauCeti.LinearAlgebra.Multilinear.Span -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Values of a multilinear map on spans

A multilinear map is linear in each argument separately, so its value at a family of arguments
drawn from the spans of sets `s i` is a linear combination of its values at families drawn from
the sets `s i` themselves. This is the multilinear analogue of `Submodule.map₂_span_span` for
bilinear maps. It reduces statements about all values of a determinant-like expression to its
values on generators.

For an alternating map, this shows that the value vanishes when more than `k` of the arguments
lie in the span of `k` vectors. Over a domain this is `AlternatingMap.map_linearDependent`, but
over an arbitrary ring no cancellation is available.

## Main results

* `MultilinearMap.map_mem_span_image_pi`: if `m i ∈ span R (s i)` for every `i`, then `f m` lies
  in the span of the values of `f` on `Set.univ.pi s`.
* `AlternatingMap.map_eq_zero_of_mem_span`: an alternating map vanishes when more than `k` of
  its arguments lie in the span of `k` vectors, over any semiring.
-/

public section

namespace MultilinearMap

variable {R ι N : Type*} {M : ι → Type*} [Semiring R] [Finite ι]
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [AddCommMonoid N] [Module R N]

/-- The value of a multilinear map at arguments drawn from the spans of sets `s i` lies in the
span of its values at arguments drawn from the sets `s i`. -/
theorem map_mem_span_image_pi (f : MultilinearMap R M N) (s : ∀ i, Set (M i)) {m : ∀ i, M i}
    (hm : ∀ i, m i ∈ Submodule.span R (s i)) :
    f m ∈ Submodule.span R (f '' Set.univ.pi s) := by
  classical
  cases nonempty_fintype ι
  -- Replace the arguments indexed by `t` by elements of the spans, one coordinate at a time.
  suffices key : ∀ t : Finset ι, ∀ m : ∀ i, M i, (∀ i, m i ∈ Submodule.span R (s i)) →
      (∀ i ∉ t, m i ∈ s i) → f m ∈ Submodule.span R (f '' Set.univ.pi s) from
    key Finset.univ m hm (by simp)
  intro t
  induction t using Finset.induction_on with
  | empty => exact fun m _ h ↦ Submodule.subset_span ⟨m, fun i _ ↦ h i (by simp), rfl⟩
  | insert a t ha ih =>
    intro m hm h
    have hupdate : ∀ x ∈ Submodule.span R (s a),
        f (Function.update m a x) ∈ Submodule.span R (f '' Set.univ.pi s) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        refine ih _ (fun i ↦ ?_) (fun i hi ↦ ?_)
        · rcases eq_or_ne i a with rfl | hia
          · simpa using Submodule.subset_span hx
          · simpa [hia] using hm i
        · rcases eq_or_ne i a with rfl | hia
          · simpa using hx
          · simpa [hia] using h i (by simp [hia, hi])
      | zero => simp
      | add x y _ _ hx hy => rw [f.map_update_add]; exact add_mem hx hy
      | smul c x _ hx => rw [f.map_update_smul]; exact Submodule.smul_mem _ c hx
    simpa using hupdate (m a) (hm a)

end MultilinearMap

namespace AlternatingMap

variable {ι R M N : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N]

/-- **An alternating map vanishes when too many arguments lie in a small span.** If more than `k`
of the arguments lie in the span of `k` vectors, then the value is zero. Over a domain this
follows from `AlternatingMap.map_linearDependent`; here the ring is arbitrary. -/
theorem map_eq_zero_of_mem_span [Finite ι] (f : M [⋀^ι]→ₗ[R] N) {v : ι → M} {t : Finset ι}
    {k : ℕ} (c : Fin k → M) (ht : k < t.card)
    (hv : ∀ i ∈ t, v i ∈ Submodule.span R (Set.range c)) : f v = 0 := by
  classical
  cases nonempty_fintype ι
  -- Expand the arguments indexed by `t` along `c`; the other arguments stay fixed.
  let s : ι → Set M := fun i ↦ if i ∈ t then Set.range c else {v i}
  have hs (i : ι) : v i ∈ Submodule.span R (s i) := by
    by_cases hi : i ∈ t
    · simpa [s, hi] using hv i hi
    · simp [s, hi]
  refine (Submodule.mem_bot R).1 <| Submodule.span_le.2 ?_ <|
    f.toMultilinearMap.map_mem_span_image_pi s hs
  rintro _ ⟨w, hw, rfl⟩
  -- Each expanded family takes more than `k` values in `range c` on `t`, so two coincide.
  have hwc (i : t) : w i ∈ Set.range c := by simpa [s, i.2] using hw i trivial
  choose g hg using hwc
  obtain ⟨i, j, hij, hgij⟩ := Fintype.exists_ne_map_eq_of_card_lt g (by simpa using ht)
  simpa using f.map_eq_zero_of_eq w (by rw [← hg i, ← hg j, hgij]) (Subtype.coe_ne_coe.2 hij)

end AlternatingMap
end
end TAF_LiteralSource_0637

section TAF_LiteralSource_0638
/- Original module: TauCeti.LinearAlgebra.BilinearMap.Multilinear -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Bilinear maps read off multilinear maps in two variables

A multilinear map on the constant family `fun _ : Fin 2 => V` and a bilinear map on `V` carry the
same data.  This file records the direction that is used downstream:
`MultilinearMap.toBilinMap` reads a multilinear map `m` as the bilinear map
`(x, y) ↦ m ![x, y]`, and two recognition lemmas say when that map is symmetric or alternating.

The point of the construction is that the maps out of a second symmetric or exterior power are
multilinear in exactly this sense, so a functional on `Sym²V` or on `⋀²V` becomes a bilinear form
on `V` by composing with the universal multilinear map.  That is what
`TauCeti/LinearAlgebra/BilinearForm/Squares.lean` builds on this file.  An alternating bilinear
map can likewise be read as an `AlternatingMap` on `Fin 2`, and these two readings are inverse.

## Main definitions

* `MultilinearMap.toBilinMap`: the bilinear map `(x, y) ↦ m ![x, y]` of a multilinear map `m` in
  two variables.
* `LinearMap.IsAlt.toAlternatingMap`: an alternating bilinear map read as an alternating map on
  two arguments.

## Main results

* `MultilinearMap.isSymm_toBilinMap`: the scalar-valued form is symmetric when `m` is unchanged by
  swapping its two arguments.
* `MultilinearMap.isAlt_toBilinMap`: the map is alternating when `m` vanishes on a repeated
  argument; `AlternatingMap.isAlt_toBilinMap` specializes this to alternating maps.
* `MultilinearMap.toBilinMap_injective`: the other half of "the same data" -- the bilinear map
  determines the multilinear map.
* `AlternatingMap.toAlternatingMap_isAlt_toBilinMap` and
  `LinearMap.IsAlt.toBilinMap_toAlternatingMap`: the two round trips between alternating maps on
  `Fin 2` and alternating bilinear maps.

## Implementation notes

Bilinearity is Mathlib's `MultilinearMap.cons_add` and `cons_smul` at the first argument and
`MultilinearMap.snoc_add` and `snoc_smul` at the second, since `![x, y]` is both `Fin.cons x ![y]`
and `Fin.snoc ![x] y`.  Feeding those four facts to `LinearMap.mk₂` keeps the four linearity goals
stated in the `![·, ·]` notation, so none of them has to be massaged into the nested form a bare
`LinearMap` constructor would present.
-/

public section

variable {R V N : Type*} [CommSemiring R] [AddCommMonoid V] [Module R V]
  [AddCommMonoid N] [Module R N]

namespace LinearMap

namespace IsAlt

/-- An alternating bilinear map read as an alternating map in two arguments. -/
def toAlternatingMap {ω : V →ₗ[R] V →ₗ[R] N} (hω : LinearMap.IsAlt ω) :
    V [⋀^Fin 2]→ₗ[R] N where
  toFun v := ω (v 0) (v 1)
  map_update_add' v i x y := by fin_cases i <;> simp
  map_update_smul' v i c x := by fin_cases i <;> simp
  map_eq_zero_of_eq' v i j hv hij := by
    fin_cases i <;> fin_cases j <;> simp_all [hω.self_eq_zero]

/-- Evaluating the alternating map recovers the original bilinear map on the two arguments. -/
@[simp]
theorem toAlternatingMap_apply {ω : V →ₗ[R] V →ₗ[R] N} (hω : LinearMap.IsAlt ω)
    (v : Fin 2 → V) : hω.toAlternatingMap v = ω (v 0) (v 1) :=
  (rfl)

end IsAlt

end LinearMap

namespace MultilinearMap

/-- The bilinear map `(x, y) ↦ m ![x, y]` of a multilinear map `m` in two variables. -/
def toBilinMap (m : MultilinearMap R (fun _ : Fin 2 => V) N) : LinearMap.BilinMap R V N :=
  LinearMap.mk₂ R (fun x y => m ![x, y])
    (fun x x' y => m.cons_add ![y] x x')
    (fun c x y => m.cons_smul ![y] c x)
    (fun x y y' => by simpa using m.snoc_add ![x] y y')
    (fun c x y => by simpa using m.snoc_smul ![x] c y)

@[simp]
theorem toBilinMap_apply (m : MultilinearMap R (fun _ : Fin 2 => V) N) (x y : V) :
    m.toBilinMap x y = m ![x, y] :=
  (rfl)

/-- The form of a scalar-valued multilinear map that is unchanged by swapping its two arguments
is symmetric. -/
theorem isSymm_toBilinMap {m : MultilinearMap R (fun _ : Fin 2 => V) R}
    (h : ∀ x y : V, m ![y, x] = m ![x, y]) : LinearMap.BilinForm.IsSymm m.toBilinMap :=
  ⟨fun x y => (h x y).symm⟩

/-- The bilinear map of a multilinear map that vanishes on a repeated argument is alternating. -/
theorem isAlt_toBilinMap {m : MultilinearMap R (fun _ : Fin 2 => V) N}
    (h : ∀ x : V, m ![x, x] = 0) : m.toBilinMap.IsAlt :=
  fun x => (toBilinMap_apply m x x).trans (h x)

/-- **A multilinear map in two variables is determined by its bilinear map.**  Every argument of
`m` is a `![x, y]`, and the bilinear map records the value of `m` there. -/
theorem toBilinMap_injective :
    Function.Injective (toBilinMap : MultilinearMap R (fun _ : Fin 2 => V) N → _) := by
  intro m n h
  ext f
  rw [← FinVec.etaExpand_eq f]
  exact congr($h (f 0) (f 1))

end MultilinearMap

namespace AlternatingMap

/-- The bilinear map of an alternating map in two arguments is alternating. -/
theorem isAlt_toBilinMap (A : V [⋀^Fin 2]→ₗ[R] N) : A.toMultilinearMap.toBilinMap.IsAlt :=
  MultilinearMap.isAlt_toBilinMap fun x =>
    A.map_eq_zero_of_eq ![x, x] (i := 0) (j := 1) rfl (by decide)

/-- Reading an alternating map in two arguments as a bilinear map and back recovers the map. -/
@[simp]
theorem toAlternatingMap_isAlt_toBilinMap (A : V [⋀^Fin 2]→ₗ[R] N) :
    A.isAlt_toBilinMap.toAlternatingMap = A := by
  ext v
  rw [← FinVec.etaExpand_eq v]
  rfl

end AlternatingMap

namespace LinearMap.IsAlt

/-- Reading an alternating bilinear map as an alternating map and back recovers the map. -/
@[simp]
theorem toBilinMap_toAlternatingMap {B : V →ₗ[R] V →ₗ[R] N} (hB : B.IsAlt) :
    hB.toAlternatingMap.toMultilinearMap.toBilinMap = B :=
  (rfl)

end LinearMap.IsAlt
end
end TAF_LiteralSource_0638

section TAF_LiteralSource_0639
/- Original module: TauCeti.LinearAlgebra.Determinant.Basic -/
/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Determinant transformation laws, evaluation, and determinants of updated rows

Precomposing an alternating form of top degree with an endomorphism `φ` multiplies it by
`LinearMap.det φ`, and — the direction that is actually used — a *nonzero* form merely known to be
*scaled* by some `d` thereby identifies `d` as the determinant, without computing it, as soon as
scalars cancel against nonzero vectors of the codomain (`IsCancelMulZero R` and
`Module.IsTorsionFree R N`; see the implementation notes, where `ω ≠ 0` alone is shown to be
insufficient). This file records that law in three vocabularies: for
an `AlternatingMap` indexed by a basis' index type, for an alternating bilinear form on a rank-two
module, and for the standard-basis determinant form under matrix multiplication. It also
identifies evaluation of the row determinant form on a family of linear functionals with the
determinant of their evaluation matrix. Ideal membership of these determinants extends from
a set of rows to its linear span.

Mathlib's `Module.Basis.det_comp` is the case `ω = b.det` of the first statement. The step taken
here is that every top-degree alternating form is a multiple of `b.det`
(`AlternatingMap.eq_basis_det_smulRight`), so the same law holds for all of them; that is what
makes the converse available for a form supplied by something other than a basis, such as a
pairing.

The file also records one identity for the determinant of a matrix with one row replaced,
alongside Mathlib's `Matrix.det_updateRow_add` and `Matrix.det_updateRow_smul`: Jacobi's formula
in row form, that rescaling one row entry by entry along a fixed vector of factors and summing the
results over the rows multiplies the determinant by the total of the factors.

It also records facts used to compute ideals of maximal minors: the determinant in a product
basis of a block-diagonal family, and of a family that becomes block diagonal after a permutation,
and Cramer's rule for an endomorphism of a free module of finite rank.

Finally, it records the Weinstein–Aronszajn identity `det (1 + X ∘ₗ Y) = det (1 + Y ∘ₗ X)` for
linear maps `X` and `Y` between two free modules of finite rank, possibly of different ranks.

## Main results

* `AlternatingMap.eq_basis_det_smulRight`: `ω = b.det.smulRight (ω b)` for `ω` of top degree.
* `AlternatingMap.compLinearMap_eq_det_smul`: `ω ∘ φ = det φ • ω` for `ω` of top degree.
* `LinearMap.det_eq_of_compLinearMap_eq_smul`: if `ω ≠ 0` and `ω ∘ φ = d • ω` then `det φ = d`,
  for `R` cancellative and `N` torsion-free.
* `LinearMap.IsAlt.compl₁₂_self_eq_det_smul` and `LinearMap.det_eq_of_compl₁₂_self_eq_smul`: the
  same two statements for an alternating bilinear form on a module of rank two.
* `LinearMap.det_eq_of_compl₁₂_self_eq_smul_of_separatingLeft`: the recovery statement over any
  commutative ring, for a left-separating form.
* `Matrix.detRowAlternating_mulVec`: multiplication by a square matrix scales the
  standard-basis determinant form by the matrix determinant.
* `Matrix.detRowAlternating_pi_apply`: evaluating the row determinant form on a family of
  linear functionals gives the determinant of their evaluation matrix.
* `Matrix.detRowAlternating_compLinearMap_pi_apply`: the same evaluation in multilinear-map
  vocabulary after precomposition with the family of functionals.
* `TauCeti.det_mem_of_mem_span`: ideal membership of evaluation determinants extends from
  a set of rows to its linear span.
* `Matrix.sum_det_updateRow_mul_row`: Jacobi's formula for a determinant, in row form.
* `Matrix.det_mul_column_intCast`: scaling every row `i` of an integer matrix by `d i`
  multiplies the determinant by `∏ i, d i`, over any commutative ring.
* `LinearMap.det_one_add_comp_comm`: the Weinstein–Aronszajn identity
  `det (1 + X ∘ₗ Y) = det (1 + Y ∘ₗ X)` for linear maps between free modules of finite rank.
* `LinearEquiv.det_ker_eq_bot_of_finrank_le_one`: the determinant kernel is trivial in
  dimension at most one.
* `Module.Basis.prod_det_sumElim`: the determinant in a product basis of a family split between
  the two factors is the product of the two determinants.
* `Module.Basis.exists_prod_det_eq_sign_smul_mul`: the same up to sign for a family with exactly
  as many members in the first factor as the rank of the first factor.
* `LinearMap.det_smul_mem_range`: Cramer's rule, `det φ • x ∈ range φ`.

## Implementation notes

The forms are valued in an arbitrary module `N`, not in `R`. Mathlib's
`AlternatingMap.eq_smul_basis_det` is the `N = R` case of the first result here; the codomain plays
no part in the argument, only the coordinates do, so the `N`-valued statement is what is proved.

The recovery statements need cancellation hypotheses, not just `ω ≠ 0`, and neither of the two
assumed can be dropped:

* without `IsCancelMulZero R`: over `R = ZMod 4`, with `N = R` (which is torsion-free over
  itself), the form `ω = 2 • b.det` is nonzero and satisfies `ω ∘ id = 3 • ω`, while
  `det id = 1`;
* without `Module.IsTorsionFree R N`: over `R = ℤ`, with `M = ℤ²` and `N = ZMod 2`, the
  determinant form reduced mod `2`, `(x, y) ↦ x₀ y₁ - x₁ y₀`, is nonzero and alternating, and
  `φ = 3 • id` scales it by `9`, that is by `1`, while `det φ = 9`.

`IsCancelMulZero R` and `Module.IsTorsionFree R N` are assumed for these recovery statements, and
for nothing else; together they let a nonzero form, an element of a torsion-free module of
alternating or bilinear maps, cancel from `det φ • ω = d • ω`. A left-separating form needs neither:
a scalar killing it kills a basis vector, so vanishes, and
`LinearMap.det_eq_of_compl₁₂_self_eq_smul_of_separatingLeft` holds over every commutative ring. The
examples above are not left-separating: `2 • b.det` pairs `2 • b 0` to zero, and the reduced
determinant form pairs `2 • e₀` to zero.

None of the transformation laws stated for a basis is a `simp` lemma: the basis is a hypothesis
and does not occur in the conclusion, so `simp` could not infer it.

The bilinear statements use `LinearMap.IsAlt.toAlternatingMap` to read an alternating bilinear form
as an `AlternatingMap` on `Fin 2`.

## Provenance

The four transformation and recovery laws are ported from the AINTLIB `HasseWeil` project
(Apache-2.0), revision `513e83879e2f`, file `HasseWeil/WeilPairing/PairingDet.lean`, declarations
`alternating_comp_eq_det_smul` and `det_eq_of_alternating_scaling`. The source states them over a
field, for a scalar-valued form, evaluated at a basis, and proves the first by expanding `φ (b j)`
in coordinates; none of that is reproduced here. `Matrix.detRowAlternating_mulVec` predates
that port and is not from the source, nor is the left-separating recovery statement.
-/

public section

open Module

namespace AlternatingMap

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N]

/-- **A top-degree alternating form is its basis determinant times its value on the basis.** This
is Mathlib's `AlternatingMap.eq_smul_basis_det` with the codomain an arbitrary module rather than
`R`. -/
theorem eq_basis_det_smulRight [Fintype ι] [DecidableEq ι] (b : Basis ι R M)
    (ω : M [⋀^ι]→ₗ[R] N) : ω = b.det.smulRight (ω ⇑b) := by
  -- Mathlib's proof generalises unchanged: it reads off the coordinates and never touches the
  -- values, and `Module.Basis.ext_alternating` is already stated for an arbitrary codomain.
  refine Module.Basis.ext_alternating b fun i h => ?_
  let σ : Equiv.Perm ι := Equiv.ofBijective i (Finite.injective_iff_bijective.1 h)
  -- `ext_alternating` hands back the arguments as `fun i => b (i j)`, whereas `map_perm` and
  -- `Basis.det_self` are stated for the composite `⇑b ∘ σ`. The two are the same function, so
  -- the `change` is definitional; Mathlib's own `eq_smul_basis_det` opens with the same step.
  change ω (⇑b ∘ σ) = (b.det.smulRight (ω ⇑b)) (⇑b ∘ σ)
  simp [map_perm, Basis.det_self]

/-- **An endomorphism scales a top-degree alternating form by its determinant.** Here `ω` is of
top degree in the sense that its index type indexes a basis of `M`; that basis is a hypothesis and
does not occur in the conclusion, which is an equality of alternating maps. -/
theorem compLinearMap_eq_det_smul [Finite ι] (b : Basis ι R M) (ω : M [⋀^ι]→ₗ[R] N)
    (φ : M →ₗ[R] M) : ω.compLinearMap φ = LinearMap.det φ • ω := by
  cases nonempty_fintype ι
  classical
  rw [eq_basis_det_smulRight b ω]
  ext v
  simp [← Function.comp_def, mul_smul]

end AlternatingMap

namespace Module.Basis

variable {ι ι' R M M' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']

/-- The determinant in a product basis of a family whose first arguments lie in the first factor
and whose last arguments lie in the second factor is the product of the two determinants. -/
theorem prod_det_sumElim (b : Basis ι R M) (b' : Basis ι' R M') (v : ι → M) (v' : ι' → M') :
    (b.prod b').det (Sum.elim (LinearMap.inl R M M' ∘ v) (LinearMap.inr R M M' ∘ v')) =
      b.det v * b'.det v' := by
  have h : (b.prod b').toMatrix (Sum.elim (LinearMap.inl R M M' ∘ v)
      (LinearMap.inr R M M' ∘ v')) = Matrix.fromBlocks (b.toMatrix v) 0 0 (b'.toMatrix v') := by
    ext (i | i) (j | j) <;> simp [Basis.toMatrix_apply]
  rw [det_apply, h, Matrix.det_fromBlocks_zero₂₁, det_apply, det_apply]

/-- If the members of a family satisfying `P` lie in the first factor, the others lie in the
second factor, and exactly `card ι` members satisfy `P`, then, after a permutation `σ` moving the
former to the front, the determinant of the family in a product basis is, up to the sign of `σ`,
the product of the determinants of the two blocks of components. -/
theorem exists_prod_det_eq_sign_smul_mul (b : Basis ι R M) (b' : Basis ι' R M')
    (w : ι ⊕ ι' → M × M') (P : ι ⊕ ι' → Prop) [DecidablePred P]
    (hcard : Fintype.card {i // P i} = Fintype.card ι) (h₁ : ∀ i, P i → (w i).2 = 0)
    (h₂ : ∀ i, ¬P i → (w i).1 = 0) :
    ∃ σ : Equiv.Perm (ι ⊕ ι'), (b.prod b').det w = Equiv.Perm.sign σ •
      (b.det (fun k ↦ (w (σ (.inl k))).1) * b'.det (fun l ↦ (w (σ (.inr l))).2)) := by
  let e₁ : ι ≃ {i // P i} := (Fintype.equivOfCardEq hcard).symm
  let e₂ : ι' ≃ {i // ¬P i} := (Fintype.equivOfCardEq (by
    rw [Fintype.card_subtype_compl, hcard, Fintype.card_sum, Nat.add_sub_cancel_left])).symm
  let σ : Equiv.Perm (ι ⊕ ι') := (e₁.sumCongr e₂).trans (Equiv.sumCompl P)
  have hσ : w ∘ σ = Sum.elim (LinearMap.inl R M M' ∘ fun k ↦ (w (σ (.inl k))).1)
      (LinearMap.inr R M M' ∘ fun l ↦ (w (σ (.inr l))).2) := by
    ext1 (k | l)
    · exact Prod.ext (by simp) (by simpa using h₁ _ (by simpa [σ] using (e₁ k).2))
    · exact Prod.ext (by simpa using h₂ _ (by simpa [σ] using (e₂ l).2)) (by simp)
  refine ⟨σ, ?_⟩
  have h := (b.prod b').det.map_perm w σ
  rw [hσ, prod_det_sumElim] at h
  rw [h, smul_smul, Int.units_mul_self, one_smul]

end Module.Basis

namespace LinearMap

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N]

/-- **The multiplier of a nonzero top-degree alternating form is the determinant.** An
endomorphism which scales `ω` by `d` has `det φ = d`; the scaling identifies the determinant
without computing it, and only the one endomorphism is involved.

The cancellation hypotheses on `R` and `N` are required, not incidental: dropping either one
leaves the multiplier of a nonzero `ω` ambiguous, as the two examples in the module docstring show.
-/
theorem det_eq_of_compLinearMap_eq_smul [Finite ι] [IsCancelMulZero R] [Module.IsTorsionFree R N]
    (b : Basis ι R M) {ω : M [⋀^ι]→ₗ[R] N} (hω : ω ≠ 0) {φ : M →ₗ[R] M} {d : R}
    (h : ω.compLinearMap φ = d • ω) : LinearMap.det φ = d :=
  smul_left_injective R hω <| (AlternatingMap.compLinearMap_eq_det_smul b ω φ).symm.trans h

/-- **An endomorphism of a rank-two module scales an alternating bilinear form by its
determinant.** The basis is a hypothesis witnessing that the rank is two; it does not occur in the
conclusion, which is an equality of bilinear maps. -/
theorem IsAlt.compl₁₂_self_eq_det_smul (b : Basis (Fin 2) R M) {ω : M →ₗ[R] M →ₗ[R] N}
    (halt : ω.IsAlt) (φ : M →ₗ[R] M) : ω.compl₁₂ φ φ = LinearMap.det φ • ω := by
  ext x y
  simpa only [compl₁₂_apply, smul_apply, AlternatingMap.compLinearMap_apply,
    IsAlt.toAlternatingMap_apply, LinearMap.smul_apply, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, _root_.smul_apply] using
    congr($(AlternatingMap.compLinearMap_eq_det_smul b halt.toAlternatingMap φ) ![x, y])

/-- **The multiplier of a nonzero alternating bilinear form on a rank-two module is the
determinant.** This is the form the additivised Weil pairing supplies: its scaling by an isogeny's
degree identifies that degree as a determinant.

As above, neither cancellation hypothesis can be dropped; the module docstring's `ZMod 2` example
is itself an alternating bilinear form on a rank-two module. -/
theorem det_eq_of_compl₁₂_self_eq_smul [IsCancelMulZero R] [Module.IsTorsionFree R N]
    (b : Basis (Fin 2) R M) {ω : M →ₗ[R] M →ₗ[R] N} (halt : ω.IsAlt) (hω : ω ≠ 0)
    {φ : M →ₗ[R] M} {d : R} (h : ω.compl₁₂ φ φ = d • ω) : LinearMap.det φ = d :=
  smul_left_injective R hω <| (halt.compl₁₂_self_eq_det_smul b φ).symm.trans h

/-- **The multiplier of a left-separating alternating bilinear form on a rank-two module is the
determinant**, over any commutative ring. Left separation of `ω` takes the place of the
cancellation hypotheses of `LinearMap.det_eq_of_compl₁₂_self_eq_smul`; this is the form that
applies to the Weil pairing on `N`-torsion, a module over `ZMod N`, which is not a domain for
composite `N`. -/
theorem det_eq_of_compl₁₂_self_eq_smul_of_separatingLeft (b : Basis (Fin 2) R M)
    {ω : M →ₗ[R] M →ₗ[R] N} (halt : ω.IsAlt) (hω : ω.SeparatingLeft) {φ : M →ₗ[R] M} {d : R}
    (h : ω.compl₁₂ φ φ = d • ω) : LinearMap.det φ = d := by
  have hd : LinearMap.det φ • ω = d • ω := (halt.compl₁₂_self_eq_det_smul b φ).symm.trans h
  -- the difference kills `ω (b 0) (b 1)`, so it vanishes
  refine sub_eq_zero.1 <| halt.eq_zero_of_smul_apply_basis_eq_zero b hω ?_
  rw [sub_smul, sub_eq_zero]
  simpa using congr($hd (b 0) (b 1))

/-- The **Weinstein–Aronszajn identity** for linear maps: for linear maps `X : F' →ₗ[R] F` and
`Y : F →ₗ[R] F'` between free modules of finite rank, `det (1 + X ∘ₗ Y) = det (1 + Y ∘ₗ X)`. This
is Mathlib's `Matrix.det_one_add_mul_comm`, read through the matrices of `X` and `Y` in bases. -/
theorem det_one_add_comp_comm {F F' : Type*} [AddCommGroup F] [Module R F] [Module.Free R F]
    [Module.Finite R F] [AddCommGroup F'] [Module R F'] [Module.Free R F'] [Module.Finite R F']
    (X : F' →ₗ[R] F) (Y : F →ₗ[R] F') :
    LinearMap.det (1 + X ∘ₗ Y) = LinearMap.det (1 + Y ∘ₗ X) := by
  classical
  let b := Free.chooseBasis R F
  let b' := Free.chooseBasis R F'
  rw [← det_toMatrix b, ← det_toMatrix b', map_add, map_add, toMatrix_one, toMatrix_one,
    toMatrix_comp b b' b, toMatrix_comp b' b b']
  exact Matrix.det_one_add_mul_comm _ _

/-- **Cramer's rule for an endomorphism.** The determinant of an endomorphism `φ` of a free
module of finite rank multiplies every vector into the range of `φ`: `det φ • x = φ (adj φ x)`,
for the adjugate `adj φ` of `φ`. -/
theorem det_smul_mem_range {F : Type*} [AddCommGroup F] [Module R F] [Module.Free R F]
    [Module.Finite R F] (φ : F →ₗ[R] F) (x : F) : LinearMap.det φ • x ∈ range φ := by
  classical
  let b := Free.chooseBasis R F
  refine ⟨Matrix.toLin b b (toMatrix b b φ).adjugate x, ?_⟩
  have h := congr(Matrix.toLin b b $((toMatrix b b φ).mul_adjugate) x)
  rw [Matrix.toLin_mul b b b, Matrix.toLin_toMatrix, map_smul, Matrix.toLin_one,
    det_toMatrix] at h
  simpa using h

end LinearMap

namespace LinearEquiv

/-- The determinant kernel on a finite free module of rank at most one is trivial. -/
@[simp]
theorem det_ker_eq_bot_of_finrank_le_one {R V : Type*} [CommRing R] [AddCommGroup V]
    [Module R V] [Module.Free R V] [Module.Finite R V] (hV : Module.finrank R V ≤ 1) :
    (LinearEquiv.det (R := R) (M := V)).ker = ⊥ := by
  nontriviality R
  refine (Subgroup.eq_bot_iff_forall _).mpr fun g hg => ?_
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hV with hV | hV
  · have := (Module.finrank_eq_zero_iff_of_free R V).mp hV
    exact Subsingleton.elim _ _
  · have := SpecialLinearGroup.subsingleton_of_finrank_eq_one (R := R) (V := V) hV
    exact congrArg Subtype.val (Subsingleton.elim (⟨g, hg⟩ : SpecialLinearGroup R V) 1)

end LinearEquiv

namespace Matrix

/-- Evaluating the row determinant form after a family of linear functionals gives the
matrix of those functionals evaluated on the input vectors. -/
@[simp]
theorem detRowAlternating_pi_apply {ι R F : Type*} [Fintype ι]
    [DecidableEq ι] [CommRing R] [AddCommGroup F] [Module R F]
    (f : ι → Module.Dual R F) (v : ι → F) :
    detRowAlternating (fun i => LinearMap.pi f (v i)) =
      (Matrix.of fun i j => f j (v i)).det := by
  have hmatrix : (fun i => LinearMap.pi f (v i)) = Matrix.of (fun i j => f j (v i)) := by
    ext i j
    simp only [LinearMap.pi_apply, Matrix.of_apply]
  -- Mathlib defines `det` as evaluation of `detRowAlternating` on the rows.
  simpa only [Matrix.det] using congrArg Matrix.det hmatrix

/-- The multilinear form obtained by precomposing the row determinant with a family of linear
functionals evaluates to the determinant of their evaluation matrix. -/
theorem detRowAlternating_compLinearMap_pi_apply {ι R F : Type*} [Fintype ι]
    [DecidableEq ι] [CommRing R] [AddCommGroup F] [Module R F]
    (f : ι → Module.Dual R F) (v : ι → F) :
    (detRowAlternating.compLinearMap (LinearMap.pi f)).toMultilinearMap v =
      (Matrix.of fun i j => f j (v i)).det := by
  rw [AlternatingMap.coe_multilinearMap, AlternatingMap.compLinearMap_apply,
    detRowAlternating_pi_apply]

end Matrix

namespace TauCeti

/-- If an ideal contains all evaluation determinants whose rows lie in a set, it also contains
those whose rows lie in the linear span of that set. The row and functional families may be
indexed by any finite type. -/
theorem det_mem_of_mem_span {ι R F : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    [AddCommGroup F] [Module R F] {s : Set F} {I : Ideal R} (f : ι → Dual R F) {v : ι → F}
    (hv : ∀ i, v i ∈ Submodule.span R s)
    (h : ∀ w : ι → F, (∀ i, w i ∈ s) → (Matrix.of fun i j ↦ f j (w i)).det ∈ I) :
    (Matrix.of fun i j ↦ f j (v i)).det ∈ I := by
  rw [← Matrix.detRowAlternating_compLinearMap_pi_apply]
  refine Submodule.span_le.2 ?_ <|
    MultilinearMap.map_mem_span_image_pi
      (Matrix.detRowAlternating.compLinearMap (LinearMap.pi f)).toMultilinearMap (fun _ ↦ s) hv
  rintro _ ⟨w, hw, rfl⟩
  rw [Matrix.detRowAlternating_compLinearMap_pi_apply]
  exact h w fun i ↦ hw i trivial

end TauCeti

namespace Matrix

/-- Multiplication by a square matrix scales the standard-basis determinant form by its
determinant. This is `AlternatingMap.compLinearMap_eq_det_smul` at `ω = (Pi.basisFun R ι).det`,
in matrix vocabulary. -/
@[simp]
theorem detRowAlternating_mulVec {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (M : Matrix ι ι R) (v : ι → ι → R) :
    detRowAlternating (fun i => M *ᵥ v i) = M.det * detRowAlternating v := by
  simpa only [Pi.basisFun_det, Function.comp_def, toLin'_apply, LinearMap.det_toLin'] using
    (Pi.basisFun R ι).det_comp (toLin' M) v

/-- **Jacobi's formula for a determinant, in row form.**  Rescale one row of a matrix entry by
entry along a fixed vector of factors, and sum the resulting determinants over the rows: the
answer is the determinant multiplied by the total of the factors. -/
theorem sum_det_updateRow_mul_row {ι : Type*} [DecidableEq ι] [Fintype ι] {R : Type*} [CommRing R]
    (A : Matrix ι ι R) (d : ι → R) :
    (∑ k, (A.updateRow k fun j => d j * A k j).det) = (∑ j, d j) * A.det := by
  have key (k : ι) : (A.updateRow k fun j => d j * A k j).det
      = ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : R) * (d (σ⁻¹ k) * ∏ i, A (σ i) i) := by
    rw [det_apply']
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hterm (i : ι) : (A.updateRow k fun j => d j * A k j) (σ i) i
        = (if i = σ⁻¹ k then d i else 1) * A (σ i) i := by
      rcases eq_or_ne i (σ⁻¹ k) with rfl | h
      · simp [updateRow_apply]
      · have hk : σ i ≠ k := fun hc => h (by rw [← hc]; simp)
        rw [updateRow_apply, ite_eq_right hk, ite_eq_right h, one_mul]
    rw [Finset.prod_congr rfl fun i _ => hterm i, Finset.prod_mul_distrib,
      Finset.prod_ite_eq' Finset.univ (σ⁻¹ k) d]
    simp
  rw [Finset.sum_congr rfl fun k _ => key k, Finset.sum_comm, det_apply', Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← Finset.mul_sum, ← Finset.sum_mul, Equiv.sum_comp (σ⁻¹ : Equiv.Perm ι) d]
  ring

/-- **The determinant of a scaled integer matrix.** Scaling every row `i` of an integer
matrix `M` by `d i`, with the entries cast into a commutative ring `R`, multiplies the
determinant by `∏ i, d i`. -/
theorem det_mul_column_intCast {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [CommRing R] (d : n → R) (M : Matrix n n ℤ) :
    (of fun i j ↦ d i * (M i j : R)).det = (∏ i, d i) * (M.det : R) := by
  simpa [Int.cast_det] using det_mul_column d (M.map ((↑) : ℤ → R))

end Matrix
end
end TAF_LiteralSource_0639

section TAF_LiteralSource_0640
/- Original module: TauCeti.RingTheory.MvPolynomial.Symmetric.Alternant -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Alternants

For a finite alphabet `σ` and an exponent vector `α : σ → ℕ`, the **alternant**

`a_α = det (X_i ^ α_j)_{i, j ∈ σ}`

is the determinant of the matrix whose row `i` records the powers of the variable `X_i` and whose
column `j` records a single exponent `α_j`.  It is the antisymmetric counterpart of a monomial
symmetric polynomial: expanding the determinant, `a_α` is the signed sum of the monomials
`∏ᵢ X_{τ i} ^ α_i` over the permutations `τ` of `σ`.

Alternants are the numerators of Jacobi's bialternant formula `s_λ = a_{λ+δ} / a_δ` for the Schur
polynomials, and the carriers of Frobenius's formula for the characters of the symmetric group,
`p_ν · a_δ = ∑_λ χ^λ(ν) · a_{λ+δ}`.  The identity that makes the latter compute is the
multiplication rule for power sums proved here,

`p_r · a_α = ∑_j a_{α + r e_j}`,

`TauCeti.psum_mul_alternant`: multiplying by a power sum raises one exponent at a time.  Rewriting
each `a_{α + r e_j}` in terms of a strictly decreasing exponent vector — it vanishes when an
exponent repeats (`TauCeti.alternant_eq_zero_of_not_injective`) and otherwise changes by the sign
of the sorting permutation (`TauCeti.alternant_comp_perm`) — is the move of one bead on the abacus
of beta-numbers, which is how the Murnaghan-Nakayama rule arises from it.

The companion rule for elementary symmetric polynomials,

`e_r · a_α = ∑_{|T| = r} a_{α + 1_T}`,

`TauCeti.esymm_mul_alternant`, raises `r` *distinct* exponents by one each instead.  On beta-numbers
that adds a vertical strip, and since the shifted exponents stay in their original order, no sorting
sign appears: that is the dual Pieri rule.

## Main definitions

* `TauCeti.alternant σ R α`: the alternant `det (X_i ^ α_j)` in `MvPolynomial σ R`.

## Main statements

* `TauCeti.alternant_eq_sum`: the Leibniz expansion of the alternant as a signed sum of monomials,
  and `TauCeti.coeff_alternant` with `TauCeti.coeff_alternant_of_injective` its coefficients.
* `TauCeti.alternant_ne_zero_of_injective`: an alternant of pairwise distinct exponents is
  nonzero.
* `TauCeti.isHomogeneous_alternant`: `a_α` is homogeneous of degree `∑ i, α i`.
* `TauCeti.rename_alternant`: `a_α` is antisymmetric, permuting the variables by `e` multiplying
  it by `sign e`.
* `TauCeti.alternant_comp_perm` and `TauCeti.alternant_eq_zero_of_not_injective`: permuting the
  exponents multiplies `a_α` by the sign, and a repeated exponent kills it.
* `TauCeti.alternant_add_const`: shifting every exponent by `c` multiplies `a_α` by
  `(∏ i, X i) ^ c`.
* `TauCeti.alternant_fin_val_eq_vandermonde`: for the exponents `0, 1, …, n - 1` the alternant
  is the Vandermonde product `∏_{i < j} (X_j - X_i)`.
* `TauCeti.psum_mul_alternant`: the power-sum multiplication rule `p_r · a_α = ∑_j a_{α + r e_j}`.
* `TauCeti.hsymm_mul_alternant`: the complete-homogeneous multiplication rule
  `h_r · a_α = ∑_{|γ| = r} a_{α + γ}`.
* `TauCeti.sum_monomial_mul_alternant`: the multiplication rule for a symmetric polynomial
  `f = ∑_i c_i x^{d_i}`, `f · a_α = ∑_i c_i · a_{α + d_i}`.
* `TauCeti.esymm_mul_alternant`: the elementary-symmetric multiplication rule
  `e_r · a_α = ∑_{|T| = r} a_{α + 1_T}`.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 3 (alternants and the bialternant formula) and Section 7 (the characters of the
  symmetric groups).
* R. P. Stanley, *Enumerative Combinatorics, Vol. 2*, Sections 7.15 (the classical definition of
  Schur functions and the Pieri rules) and 7.17 (the Murnaghan-Nakayama rule).
-/

public section

namespace TauCeti

open MvPolynomial Equiv Finset

variable (σ : Type*) [Fintype σ] [DecidableEq σ] (R : Type*) [CommRing R]

/-- The **alternant** `a_α = det (X_i ^ α_j)` of an exponent vector `α : σ → ℕ`: the determinant of
the matrix whose entry in row `i` and column `j` is the variable `X_i` raised to the exponent
`α_j`. -/
noncomputable def alternant (α : σ → ℕ) : MvPolynomial σ R :=
  (Matrix.of fun i j => (X i : MvPolynomial σ R) ^ α j).det

variable {σ R}

/-- The alternant `a_α` is the determinant of the matrix whose `(i, j)` entry is `X i ^ α j`. -/
theorem alternant_def (α : σ → ℕ) :
    alternant σ R α = (Matrix.of fun i j => (X i : MvPolynomial σ R) ^ α j).det :=
  (rfl)

/-- **The Leibniz expansion of an alternant**: `a_α` is the signed sum, over the permutations `τ`
of the alphabet, of the monomials `∏ᵢ X_{τ i} ^ α_i`. -/
theorem alternant_eq_sum (α : σ → ℕ) :
    alternant σ R α = ∑ τ : Perm σ, Perm.sign τ • ∏ i, (X (τ i) : MvPolynomial σ R) ^ α i := by
  simp only [alternant_def, Matrix.det_apply, Matrix.of_apply]

/-- The coefficient of the monomial `x^d` in the alternant `a_α` is the signed count of the
permutations `τ` that carry `d` to `α`, in the sense that `d (τ i) = α i` for every `i`. -/
theorem coeff_alternant (α : σ → ℕ) (d : σ →₀ ℕ) :
    (alternant σ R α).coeff d =
      ∑ τ ∈ univ.filter (fun τ : Perm σ => ⇑d ∘ ⇑τ = α), ((Perm.sign τ : ℤ) : R) := by
  rw [alternant_eq_sum, coeff_sum, sum_filter]
  refine sum_congr rfl fun τ _ => ?_
  have hprod : ∏ i, (X (τ i) : MvPolynomial σ R) ^ α i = ∏ k, (X k) ^ α (τ.symm k) := by
    rw [← Equiv.prod_comp τ fun k => (X k : MvPolynomial σ R) ^ α (τ.symm k)]
    simp
  have hiff : d = Finsupp.indicator (univ : Finset σ) (fun k _ => α (τ.symm k)) ↔
      ⇑d ∘ ⇑τ = α := by
    constructor
    · rintro rfl
      funext i
      simp
    · intro h
      ext k
      simp [← h]
  rw [Units.smul_def, zsmul_eq_mul, ← map_intCast (C : R →+* MvPolynomial σ R), coeff_C_mul,
    hprod, coeff_prod_X_pow]
  by_cases h : ⇑d ∘ ⇑τ = α <;> simp [hiff, h]

/-- For an alternant of pairwise distinct exponents, the coefficient of the monomial
`∏ᵢ X_i ^ α (τ i)` is the sign of `τ`. -/
theorem coeff_alternant_of_injective {α : σ → ℕ} (hα : Function.Injective α) (τ : Perm σ) :
    (alternant σ R α).coeff (Finsupp.equivFunOnFinite.symm (α ∘ τ)) =
      ((Perm.sign τ : ℤ) : R) := by
  rw [coeff_alternant, sum_eq_single τ⁻¹]
  · simp
  · intro ρ hρ hne
    have hρ' : (α ∘ τ) ∘ ρ = α := by simpa using (mem_filter.1 hρ).2
    refine absurd ?_ hne
    ext i
    have hi : τ (ρ i) = i := hα (congrFun hρ' i)
    exact Perm.eq_inv_iff_eq.2 hi
  · intro h
    refine absurd (mem_filter.2 ⟨mem_univ _, ?_⟩) h
    funext i
    simp

/-- **An alternant of pairwise distinct exponents is nonzero**: the monomial `∏ᵢ X_i ^ α i`
occurs in it with coefficient `1`. -/
theorem alternant_ne_zero_of_injective [Nontrivial R] {α : σ → ℕ} (hα : Function.Injective α) :
    alternant σ R α ≠ 0 := by
  intro h
  have := coeff_alternant_of_injective (R := R) hα 1
  simp [h] at this

/-- An alternant is homogeneous of degree the total of its exponents. -/
theorem isHomogeneous_alternant (α : σ → ℕ) :
    (alternant σ R α).IsHomogeneous (∑ i, α i) := by
  rw [alternant_eq_sum]
  refine IsHomogeneous.sum _ _ _ fun τ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul, ← map_intCast (C : R →+* MvPolynomial σ R)]
  exact (IsHomogeneous.prod _ _ _ fun i _ => isHomogeneous_X_pow (τ i) (α i)).C_mul _

/-- **Alternants are antisymmetric**: renaming the variables along a permutation `e` multiplies
an alternant by the sign of `e`. -/
@[simp]
theorem rename_alternant (e : Perm σ) (α : σ → ℕ) :
    rename e (alternant σ R α) = Perm.sign e • alternant σ R α := by
  rw [alternant_def, AlgHom.map_det, Units.smul_def, zsmul_eq_mul,
    ← Matrix.det_permute]
  congr 1
  ext i j
  simp

/-- Permuting the exponents of an alternant multiplies it by the sign of the permutation. -/
@[simp]
theorem alternant_comp_perm (e : Perm σ) (α : σ → ℕ) :
    alternant σ R (α ∘ e) = Perm.sign e • alternant σ R α := by
  rw [alternant_def, alternant_def, Units.smul_def, zsmul_eq_mul, ← Matrix.det_permute']
  congr 1

/-- An alternant with a repeated exponent vanishes. -/
theorem alternant_eq_zero_of_not_injective {α : σ → ℕ} (hα : ¬ Function.Injective α) :
    alternant σ R α = 0 := by
  simp only [Function.Injective, not_forall] at hα
  obtain ⟨i, j, hij, hne⟩ := hα
  exact Matrix.det_zero_of_column_eq hne fun k => by simp [hij]

/-- Raising every exponent of an alternant by `c` multiplies it by `(∏ i, X i) ^ c`. -/
theorem alternant_add_const (α : σ → ℕ) (c : ℕ) :
    alternant σ R (fun j => α j + c) = (∏ i, (X i : MvPolynomial σ R)) ^ c * alternant σ R α := by
  have hmat : (Matrix.of fun i j => (X i : MvPolynomial σ R) ^ (α j + c)) =
      Matrix.diagonal (fun i => (X i : MvPolynomial σ R) ^ c) *
        Matrix.of fun i j => (X i : MvPolynomial σ R) ^ α j := by
    ext i j
    simp [Matrix.diagonal_mul, pow_add, mul_comm]
  rw [alternant_def, alternant_def, hmat, Matrix.det_mul, Matrix.det_diagonal, prod_pow]

/-- **The Vandermonde alternant**: for the exponents `0, 1, …, n - 1` the alternant is the
Vandermonde product `∏_{i < j} (X_j - X_i)`. -/
theorem alternant_fin_val_eq_vandermonde (n : ℕ) :
    alternant (Fin n) R (fun j => (j : ℕ)) = ∏ i : Fin n, ∏ j ∈ Ioi i, (X j - X i) :=
  Matrix.det_vandermonde (X : Fin n → MvPolynomial (Fin n) R)

/-- **The power-sum multiplication rule for alternants**: multiplying `a_α` by the power sum
`p_r = ∑ᵢ X_i ^ r` gives the sum of the alternants obtained from `α` by raising a single exponent
by `r`, `p_r · a_α = ∑_j a_{α + r e_j}`. -/
theorem psum_mul_alternant (r : ℕ) (α : σ → ℕ) :
    psum σ R r * alternant σ R α =
      ∑ j, alternant σ R (Function.update α j (α j + r)) := by
  set A := Matrix.of fun i j => (X i : MvPolynomial σ R) ^ α j with hA
  have hcol : ∀ j, alternant σ R (Function.update α j (α j + r)) =
      (A.transpose.updateRow j fun i => (X i : MvPolynomial σ R) ^ r * A.transpose j i).det := by
    intro j
    rw [alternant_def, ← Matrix.det_transpose]
    congr 1
    ext k i
    rcases eq_or_ne k j with rfl | hk
    · simp [hA, pow_add, mul_comm]
    · simp [hA, Matrix.updateRow_ne hk, Function.update_of_ne hk]
  rw [sum_congr rfl fun j _ => hcol j, Matrix.sum_det_updateRow_mul_row, Matrix.det_transpose,
    psum, alternant_def]

/-- **The complete-homogeneous multiplication rule for alternants**: multiplying `a_α` by the
complete homogeneous symmetric polynomial `h_r` gives the sum of the alternants obtained from `α` by
adding an exponent vector of total degree `r`, `h_r · a_α = ∑_{|γ| = r} a_{α + γ}`.

Unlike the power-sum rule, the shifts here are not supported at a single index, so the terms with a
repeated exponent do not account for all the cancellation: the surviving terms still have to be
sorted back into decreasing order.  That extra step is what separates the Pieri rule from the
Murnaghan-Nakayama rule. -/
theorem hsymm_mul_alternant (r : ℕ) (α : σ → ℕ) :
    hsymm σ R r * alternant σ R α =
      ∑ γ ∈ Finset.piAntidiag (Finset.univ : Finset σ) r,
        alternant σ R fun i => α i + γ i := by
  have hsum : ∀ (τ : Perm σ) (γ : σ → ℕ), ∑ i, γ (τ i) = ∑ i, γ i := fun τ γ =>
    Equiv.sum_comp τ γ
  -- Twisting the alphabet by a permutation permutes the exponent vectors of total degree `r`, so
  -- the monomials of `h_r` are the same whichever variable each exponent is attached to.
  have key : ∀ τ : Perm σ,
      ∑ γ ∈ Finset.piAntidiag (Finset.univ : Finset σ) r,
          ∏ i, (X (τ i) : MvPolynomial σ R) ^ γ i = hsymm σ R r := by
    intro τ
    rw [hsymm_eq_sum_piAntidiag]
    refine Finset.sum_nbij' (fun γ => γ ∘ τ.symm) (fun γ => γ ∘ τ) (fun γ hγ => ?_)
      (fun γ hγ => ?_) (fun γ _ => funext fun i => by simp) (fun γ _ => funext fun i => by simp)
      fun γ _ => ?_
    · simp only [Finset.mem_piAntidiag, Finset.mem_univ, implies_true, and_true,
        Function.comp_apply] at hγ ⊢
      rw [hsum τ.symm γ, hγ]
    · simp only [Finset.mem_piAntidiag, Finset.mem_univ, implies_true, and_true,
        Function.comp_apply] at hγ ⊢
      rw [hsum τ γ, hγ]
    · simp only [Function.comp_apply]
      rw [← Equiv.prod_comp τ fun k => (X k : MvPolynomial σ R) ^ γ (τ.symm k)]
      exact Finset.prod_congr rfl fun i _ => by rw [Equiv.symm_apply_apply]
  simp only [alternant_eq_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [mul_smul_comm, ← Finset.smul_sum]
  congr 1
  rw [← key τ, Finset.sum_mul]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => by rw [← pow_add, Nat.add_comm]

/-- **The multiplication rule for alternants and symmetric polynomials**: if
`f = ∑_i c_i x^{d_i}` is symmetric, multiplying `a_α` by `f` gives the sum of the alternants
obtained from `α` by adding each exponent vector `d_i`, weighted by its coefficient,
`f · a_α = ∑_i c_i · a_{α + d_i}`.

The monomials need not be distinct, so the identity applies directly to a symmetric polynomial
given as a generating function, such as a Schur polynomial as a sum over tableaux. -/
theorem sum_monomial_mul_alternant {ι : Type*} (s : Finset ι) (d : ι → σ →₀ ℕ) (c : ι → R)
    (hf : (∑ i ∈ s, monomial (d i) (c i)).IsSymmetric) (α : σ → ℕ) :
    (∑ i ∈ s, monomial (d i) (c i)) * alternant σ R α =
      ∑ i ∈ s, c i • alternant σ R fun j => α j + d i j := by
  -- Renaming the symmetric factor along `τ` attaches its exponents to the variables `X (τ j)`.
  have key : ∀ τ : Perm σ,
      (∑ i ∈ s, monomial (d i) (c i)) * ∏ j, (X (τ j) : MvPolynomial σ R) ^ α j =
        ∑ i ∈ s, c i • ∏ j, (X (τ j) : MvPolynomial σ R) ^ (α j + d i j) := by
    intro τ
    rw [← hf τ, map_sum, sum_mul]
    refine sum_congr rfl fun i _ => ?_
    rw [monomial_eq, Finsupp.prod_fintype _ _ fun _ => pow_zero _, map_mul, rename_C, map_prod,
      smul_eq_C_mul, mul_assoc, ← prod_mul_distrib]
    simp only [map_pow, rename_X, pow_add, mul_comm]
  simp only [alternant_eq_sum, mul_sum, smul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun τ _ => ?_
  rw [mul_smul_comm, key, smul_sum]
  exact sum_congr rfl fun i _ => smul_comm _ _ _

/-- **The elementary-symmetric multiplication rule for alternants**: multiplying `a_α` by the
elementary symmetric polynomial `e_r = ∑_{|T| = r} ∏_{i ∈ T} X_i` gives the sum of the alternants
obtained from `α` by raising by one each of the `r` exponents indexed by an `r`-element set,
`e_r · a_α = ∑_{|T| = r} a_{α + 1_T}`.

Unlike the power-sum rule, this raises no exponent twice, so the shifted exponent vectors are the
translates of `α` by the indicator of a set. -/
theorem esymm_mul_alternant (r : ℕ) (α : σ → ℕ) :
    esymm σ R r * alternant σ R α =
      ∑ T ∈ powersetCard r (univ : Finset σ),
        alternant σ R fun j => α j + if j ∈ T then 1 else 0 := by
  -- Expand both sides by the Leibniz formula.  A permutation `τ` contributes the monomial
  -- `∏ᵢ X_{τ i} ^ α i` times, on the left, the squarefree monomial of an `r`-element set, and, on
  -- the right, the squarefree monomial of the set of raised exponents carried along `τ`.
  have key : ∀ (T : Finset σ) (τ : Perm σ),
      ∏ i, (X (τ i) : MvPolynomial σ R) ^ (α i + if i ∈ T then 1 else 0) =
        (∏ i, (X (τ i) : MvPolynomial σ R) ^ α i) *
          ∏ k ∈ T.map τ.toEmbedding, (X k : MvPolynomial σ R) := by
    intro T τ
    rw [prod_map]
    simp only [Equiv.coe_toEmbedding, pow_add, prod_mul_distrib]
    congr 1
    calc ∏ i, (X (τ i) : MvPolynomial σ R) ^ (if i ∈ T then 1 else 0)
        = ∏ i, if i ∈ T then (X (τ i) : MvPolynomial σ R) else 1 :=
          prod_congr rfl fun i _ => by split_ifs <;> simp
      _ = ∏ i ∈ T, (X (τ i) : MvPolynomial σ R) := by rw [prod_ite_mem, univ_inter]
  rw [eq_comm]
  calc ∑ T ∈ powersetCard r (univ : Finset σ),
          alternant σ R (fun j => α j + if j ∈ T then 1 else 0)
      = ∑ T ∈ powersetCard r (univ : Finset σ), ∑ τ : Perm σ, Perm.sign τ •
          ((∏ i, (X (τ i) : MvPolynomial σ R) ^ α i) *
            ∏ k ∈ T.map τ.toEmbedding, (X k : MvPolynomial σ R)) :=
        sum_congr rfl fun T _ => by
          rw [alternant_eq_sum]
          exact sum_congr rfl fun τ _ => by rw [key T τ]
    _ = ∑ τ : Perm σ, ∑ T ∈ powersetCard r (univ : Finset σ), Perm.sign τ •
          ((∏ i, (X (τ i) : MvPolynomial σ R) ^ α i) *
            ∏ k ∈ T.map τ.toEmbedding, (X k : MvPolynomial σ R)) := sum_comm
    _ = ∑ τ : Perm σ, ∑ T ∈ powersetCard r (univ : Finset σ), Perm.sign τ •
          ((∏ i, (X (τ i) : MvPolynomial σ R) ^ α i) * ∏ k ∈ T, (X k : MvPolynomial σ R)) :=
        sum_congr rfl fun τ _ => Finset.sum_equiv (Equiv.finsetCongr τ)
          (fun T => by simp) fun T _ => by simp
    _ = ∑ T ∈ powersetCard r (univ : Finset σ), ∑ τ : Perm σ, Perm.sign τ •
          ((∏ i, (X (τ i) : MvPolynomial σ R) ^ α i) * ∏ k ∈ T, (X k : MvPolynomial σ R)) :=
        sum_comm
    _ = esymm σ R r * alternant σ R α := by
        rw [esymm, sum_mul]
        refine sum_congr rfl fun T _ => ?_
        rw [alternant_eq_sum, mul_sum]
        exact sum_congr rfl fun τ _ => by rw [mul_smul_comm, mul_comm]

end TauCeti
end
end TAF_LiteralSource_0640

section TAF_LiteralSource_0641
/- Original module: TauCeti.Combinatorics.Young.SemistandardTableau -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Order properties of semistandard Young tableaux

Mathlib's `SemistandardYoungTableau` records that entries increase weakly along each row and
strictly down each column, each within a single row or column. This file derives the order facts
that combine these conditions across several rows and columns: an entry is bounded by any entry
weakly below and to the right of it, and, since the entries start at `0` and increase strictly down
each column, the entry in row `i` is at least `i`.

The material is kept in its own module, upstream of the content and Kostka-number theory, so that
these basic order facts about tableaux do not oblige a consumer to import that theory.

## Main declarations

* `SemistandardYoungTableau.entry_le_of_le`: entries increase weakly to the right and downwards.
* `SemistandardYoungTableau.le_entry`: the entry in row `i` is at least `i`.
-/

public section

namespace SemistandardYoungTableau

variable {μ : YoungDiagram}

/-- The entries of a semistandard Young tableau increase weakly to the right and downwards. -/
theorem entry_le_of_le (T : SemistandardYoungTableau μ) {i₁ i₂ j₁ j₂ : ℕ} (hi : i₁ ≤ i₂)
    (hj : j₁ ≤ j₂) (hc : ((i₂, j₂) : ℕ × ℕ) ∈ μ) : T i₁ j₁ ≤ T i₂ j₂ :=
  (T.row_weak_of_le hj (μ.up_left_mem hi le_rfl hc)).trans (T.col_weak hi hc)

/-- The entries of a semistandard Young tableau increase strictly down a column, so the entry in
row `i` is at least `i`. -/
theorem le_entry (T : SemistandardYoungTableau μ) {i j : ℕ} (h : (i, j) ∈ μ) : i ≤ T i j := by
  induction i with
  | zero => exact Nat.zero_le _
  | succ m ih =>
    exact Nat.succ_le_of_lt <|
      (ih (μ.up_left_mem m.le_succ le_rfl h)).trans_lt (T.col_strict m.lt_succ_self h)

end SemistandardYoungTableau
end
end TAF_LiteralSource_0641

section TAF_LiteralSource_0642
/- Original module: TauCeti.Combinatorics.Young.Kostka -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Kostka numbers

The *content* of a semistandard Young tableau records how often each natural number is used as an
entry, and the *Kostka number* `K_{μ w}` counts the semistandard tableaux of shape `μ` and content
`w`.  This file defines both, proves that the tableaux of a given content are finite, and
establishes the two facts that make the Kostka numbers a triangular array for the dominance order:
the tableau of shape `μ` whose `i`-th row consists of `i`s is the only one of content
`μ.rowLen` (so `K_{μ μ} = 1`), and a tableau of shape `μ` and content `w` forces every partial sum
`∑_{i < k} w i` to be at most the corresponding partial sum of the row lengths of `μ` (so, for
partitions, `K_{μ ν} = 0` unless `μ` dominates `ν`).

The mechanism behind both is a single observation, `SemistandardYoungTableau.le_entry`: the
entries of a semistandard tableau strictly increase down each column, so the entry in row `i` is at
least `i`, and therefore the cells carrying an entry smaller than `k` all lie in the first `k`
rows.

Mathlib's `SemistandardYoungTableau` fills the cells with natural numbers starting at `0`, so the
alphabet here is `0, 1, 2, …` rather than the classical `1, 2, 3, …` and the content of the
highest-weight tableau `SemistandardYoungTableau.highestWeight μ` is `μ.rowLen` on the nose.

## Main definitions

* `SemistandardYoungTableau.content`: the content (or weight) of a semistandard Young
  tableau, `content T i` being the number of cells filled with `i`.
* `TauCeti.BoundedSSYT`: the semistandard Young tableaux of a given shape whose entries lie below
  a given bound, that is, those written in a finite alphabet.
* `TauCeti.diagramKostkaNumber`: the number of semistandard Young tableaux of a given shape and
  content.
* `TauCeti.kostkaNumber`: the Kostka number of two partitions of the same natural number, the
  shape and the content being read off their Young diagrams.

## Main results

* `SemistandardYoungTableau.sum_content_le_sum_take_rowLens`: the partial sums of the
  content of a tableau of shape `μ` are bounded by those of the row lengths of `μ`.
* `SemistandardYoungTableau.eq_highestWeight_of_content_eq_rowLen`: a tableau of shape `μ`
  and content `μ.rowLen` is the highest-weight tableau.
* `SemistandardYoungTableau.finite_content_eq`: the tableaux of a fixed shape and content
  are finite, so the Kostka number counts them faithfully.
* `TauCeti.finite_boundedSSYT`: likewise the tableaux of a fixed shape written in a finite alphabet,
  `TauCeti.BoundedSSYT`, are finite.
* `TauCeti.BoundedSSYT.content_eq_zero`: a tableau in a finite alphabet uses no other letter.
* `TauCeti.BoundedSSYT.isEmpty_of_lt_colLen`: a shape taller than its alphabet admits no tableau.
* `TauCeti.kostkaNumber_self`: `K_{μ μ} = 1`.
* `TauCeti.kostkaNumber_eq_zero_of_not_dominates`: `K_{μ ν} = 0` unless `μ` dominates `ν`.

## References

* [W. Fulton, *Young Tableaux*][fulton1997], Section 2.2.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 1.
-/

public section

namespace SemistandardYoungTableau

variable {μ : YoungDiagram}

/-- The content, or weight, of a semistandard Young tableau: the multiset of its entries, read as
a finitely supported multiplicity function, so `content T i` is the number of cells of the shape
whose entry is `i`. -/
noncomputable def content (T : _root_.SemistandardYoungTableau μ) : ℕ →₀ ℕ :=
  (μ.cells.val.map fun c => T c.1 c.2).toFinsupp

/-- The content of a tableau counts the cells of its shape carrying a given entry. -/
theorem content_apply (T : _root_.SemistandardYoungTableau μ) (i : ℕ) :
    content T i = (μ.cells.filter fun c => T c.1 c.2 = i).card := by
  rw [content, Multiset.toFinsupp_apply, Multiset.count_map]
  simp [Finset.card, Finset.filter_val, eq_comm]

/-- The support of the content of a tableau is the set of entries it uses. -/
@[simp]
theorem support_content (T : _root_.SemistandardYoungTableau μ) :
    (content T).support = μ.cells.image fun c => T c.1 c.2 := by
  rw [content, Multiset.toFinsupp_support, Multiset.toFinset_map, Finset.val_toFinset]

/-- The cells carrying an entry smaller than `k` all lie in the first `k` rows. -/
theorem filter_entry_lt_subset_filter_fst_lt (T : _root_.SemistandardYoungTableau μ) (k : ℕ) :
    (μ.cells.filter fun c => T c.1 c.2 < k) ⊆ μ.cells.filter fun c => c.1 < k := by
  intro c hc
  rw [Finset.mem_filter] at hc ⊢
  exact ⟨hc.1, lt_of_le_of_lt (le_entry T (by simpa using hc.1)) hc.2⟩

/-- The first `k` values of the content of a tableau count the cells carrying an entry smaller
than `k`. -/
theorem sum_content_eq_card_filter (T : _root_.SemistandardYoungTableau μ) (k : ℕ) :
    ∑ i ∈ Finset.range k, content T i = (μ.cells.filter fun c => T c.1 c.2 < k).card := by
  symm
  calc
    (μ.cells.filter fun c => T c.1 c.2 < k).card =
        ∑ i ∈ Finset.range k,
          ((μ.cells.filter fun c => T c.1 c.2 < k).filter fun c => T c.1 c.2 = i).card := by
      refine Finset.card_eq_sum_card_fiberwise fun c hc => ?_
      simp only [Finset.mem_coe, Finset.mem_filter] at hc
      exact Finset.mem_range.mpr hc.2
    _ = ∑ i ∈ Finset.range k, content T i := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hik : i < k := Finset.mem_range.mp hi
      rw [content_apply]
      refine congrArg Finset.card (Finset.ext fun c => ?_)
      simp only [Finset.mem_filter, and_assoc]
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, h.2 ▸ hik, h.2⟩⟩

/-- The content of a tableau of shape `μ` is a composition of the number of cells of `μ`, once the
range of summation covers all the entries. -/
theorem sum_content_eq_card {T : _root_.SemistandardYoungTableau μ} {N : ℕ}
    (hN : ∀ c ∈ μ.cells, T c.1 c.2 < N) :
    ∑ i ∈ Finset.range N, content T i = μ.card := by
  rw [sum_content_eq_card_filter, Finset.filter_true_of_mem hN]

/-- **Dominance bound for the content of a tableau**: the partial sums of the content of a
semistandard tableau of shape `μ` never exceed the partial sums of the row lengths of `μ`. -/
theorem sum_content_le_sum_take_rowLens (T : _root_.SemistandardYoungTableau μ) (k : ℕ) :
    ∑ i ∈ Finset.range k, content T i ≤ (μ.rowLens.take k).sum := by
  rw [sum_content_eq_card_filter, YoungDiagram.sum_take_rowLens_eq_card_filter_fst]
  exact Finset.card_le_card (filter_entry_lt_subset_filter_fst_lt T k)

/-- The highest-weight tableau, whose `i`-th row consists of `i`s, has content the row lengths of
its shape. -/
@[simp]
theorem content_highestWeight (μ : YoungDiagram) :
    ⇑(content (_root_.SemistandardYoungTableau.highestWeight μ)) = μ.rowLen := by
  funext i
  rw [content_apply, μ.rowLen_eq_card]
  refine congrArg Finset.card (Finset.ext fun c => ?_)
  simp only [_root_.YoungDiagram.mem_row_iff,
    _root_.SemistandardYoungTableau.highestWeight_apply]
  aesop

/-- **Uniqueness of the highest-weight tableau**: a semistandard tableau of shape `μ` whose content
is the row lengths of `μ` has an `i` in every cell of row `i`, so it is
`SemistandardYoungTableau.highestWeight μ`. -/
theorem eq_highestWeight_of_content_eq_rowLen {T : _root_.SemistandardYoungTableau μ}
    (h : ⇑(content T) = μ.rowLen) : T = _root_.SemistandardYoungTableau.highestWeight μ := by
  have key : ∀ i j : ℕ, (i, j) ∈ μ → T i j = i := by
    intro i j hij
    have hcards : (μ.cells.filter fun c => T c.1 c.2 < i + 1).card =
        (μ.cells.filter fun c => c.1 < i + 1).card := by
      rw [← sum_content_eq_card_filter, ← YoungDiagram.sum_range_rowLen_eq_card_filter_fst]
      exact Finset.sum_congr rfl fun k _ => congrFun h k
    have hsets := Finset.eq_of_subset_of_card_le
      (filter_entry_lt_subset_filter_fst_lt T (i + 1)) hcards.ge
    have hmem : ((i, j) : ℕ × ℕ) ∈ μ.cells.filter fun c => T c.1 c.2 < i + 1 := by
      rw [hsets, Finset.mem_filter]
      exact ⟨hij, Nat.lt_succ_self i⟩
    exact le_antisymm (Nat.lt_succ_iff.mp (Finset.mem_filter.mp hmem).2) (le_entry T hij)
  ext i j
  by_cases hij : (i, j) ∈ μ
  · rw [key i j hij, _root_.SemistandardYoungTableau.highestWeight_apply, ite_eq_left hij]
  · rw [T.zeros hij, _root_.SemistandardYoungTableau.highestWeight_apply, ite_eq_right hij]

/-- The semistandard tableaux of a fixed shape and content are finite. -/
instance finite_content_eq (μ : YoungDiagram) (w : ℕ → ℕ) :
    Finite {T : _root_.SemistandardYoungTableau μ // ⇑(content T) = w} := by
  by_cases hne : Nonempty {T : _root_.SemistandardYoungTableau μ // ⇑(content T) = w}
  swap
  · rw [not_nonempty_iff] at hne
    infer_instance
  obtain ⟨T₀, hT₀⟩ := hne.some
  have hmem : ∀ T : _root_.SemistandardYoungTableau μ, ⇑(content T) = w →
      ∀ c ∈ μ.cells, T c.1 c.2 ∈ μ.cells.image fun d => T₀ d.1 d.2 := by
    intro T hT c hc
    rw [← support_content T₀, DFunLike.coe_injective (hT₀.trans hT.symm), support_content T]
    exact Finset.mem_image.mpr ⟨c, hc, rfl⟩
  refine Finite.of_injective
    (fun (T : {T : _root_.SemistandardYoungTableau μ // ⇑(content T) = w}) (c : ↥μ.cells) =>
      (⟨T.1 (c : ℕ × ℕ).1 (c : ℕ × ℕ).2, hmem T.1 T.2 _ c.2⟩ :
        ↥(μ.cells.image fun d => T₀ d.1 d.2))) fun T T' hTT' => ?_
  refine Subtype.ext (_root_.SemistandardYoungTableau.ext fun i j => ?_)
  by_cases hij : (i, j) ∈ μ
  · exact congrArg Subtype.val (congrFun hTT' ⟨(i, j), hij⟩)
  · rw [T.1.zeros hij, T'.1.zeros hij]

end SemistandardYoungTableau

namespace TauCeti

open YoungDiagram (ofPartition)

/-- The semistandard Young tableaux of shape `μ` written in the alphabet `{0, …, n - 1}`, that
is, those all of whose entries are smaller than `n`.  Mathlib's `SemistandardYoungTableau μ`
allows arbitrary natural-number entries and is infinite for a nonempty `μ`, so bounding the
alphabet is what makes the tableaux of a fixed shape finitely many. -/
abbrev BoundedSSYT (n : ℕ) (μ : YoungDiagram) : Type :=
  {T : _root_.SemistandardYoungTableau μ // ∀ i c : ℕ, (i, c) ∈ μ → T i c < n}

namespace BoundedSSYT

variable {n : ℕ} {μ : YoungDiagram}

/-- The entries of a tableau written in the alphabet `{0, …, n - 1}` all use letters of that
alphabet. -/
theorem entry_lt (T : BoundedSSYT n μ) {i c : ℕ} (h : (i, c) ∈ μ) : T.1 i c < n :=
  T.2 i c h

/-- A tableau written in the alphabet `{0, …, n - 1}` uses no letter outside that alphabet. -/
theorem content_eq_zero (T : BoundedSSYT n μ) {i : ℕ} (hi : n ≤ i) :
    T.1.content i = 0 := by
  rw [SemistandardYoungTableau.content_apply, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro c hc hci
  have := entry_lt T ((YoungDiagram.mem_cells _).mp hc)
  omega

/-- **A shape taller than its alphabet admits no tableau**: entries increase strictly down a
column, so a column of more than `n` cells cannot be filled from an `n`-letter alphabet. -/
theorem isEmpty_of_lt_colLen (h : n < μ.colLen 0) : IsEmpty (BoundedSSYT n μ) := by
  refine ⟨fun T => absurd (entry_lt T (YoungDiagram.mem_iff_lt_colLen.mpr h)) (not_lt.mpr ?_)⟩
  exact SemistandardYoungTableau.le_entry T.1 (YoungDiagram.mem_iff_lt_colLen.mpr h)

/-- The empty shape has a unique tableau, the empty one. -/
instance (n : ℕ) : Unique (BoundedSSYT n (⊥ : YoungDiagram)) where
  default := ⟨_root_.SemistandardYoungTableau.highestWeight ⊥, fun _ _ hic => absurd hic (by simp)⟩
  uniq T := Subtype.ext <| _root_.SemistandardYoungTableau.ext fun _ _ => by
    rw [T.1.zeros (by simp), _root_.SemistandardYoungTableau.highestWeight_apply,
      ite_eq_right (by simp)]

end BoundedSSYT

/-- **Bounded semistandard tableaux of a fixed shape are finitely many**: such a tableau is
determined by its restriction to the finitely many cells of `μ`, where it takes one of `n` values.
Mathlib's `SemistandardYoungTableau μ` allows unbounded entries and is infinite for a nonempty
`μ`, so the bound is what makes the count finite.  No relation between `n` and the number of rows
of `μ` is needed: for a shape taller than `n` the type is empty, columns being strict. -/
instance finite_boundedSSYT (n : ℕ) (μ : YoungDiagram) : Finite (BoundedSSYT n μ) := by
  refine Finite.of_injective (β := μ.cells → Fin n)
    (fun T x => ⟨T.1 x.1.1 x.1.2, T.2 _ _ ((YoungDiagram.mem_cells _).mp x.2)⟩) ?_
  rintro ⟨T, hT⟩ ⟨T', hT'⟩ h
  refine Subtype.ext (_root_.SemistandardYoungTableau.ext fun i c => ?_)
  by_cases hc : (i, c) ∈ μ
  · exact congrArg Fin.val (congrFun h ⟨(i, c), (YoungDiagram.mem_cells _).mpr hc⟩)
  · rw [T.zeros hc, T'.zeros hc]

noncomputable instance (n : ℕ) (μ : YoungDiagram) : Fintype (BoundedSSYT n μ) := .ofFinite _

/-- The **Kostka number** `K_{μ w}` of a shape and a weight function: the number of semistandard
Young tableaux of shape `μ` whose content is `w`. -/
noncomputable def diagramKostkaNumber (μ : YoungDiagram) (w : ℕ → ℕ) : ℕ :=
  Nat.card {T : _root_.SemistandardYoungTableau μ // ⇑(SemistandardYoungTableau.content T) = w}

/-- The Kostka number of a shape and a weight function counts the semistandard tableaux of that
shape whose content is that weight. -/
theorem diagramKostkaNumber_def (μ : YoungDiagram) (w : ℕ → ℕ) :
    diagramKostkaNumber μ w =
      Nat.card
        {T : _root_.SemistandardYoungTableau μ // ⇑(SemistandardYoungTableau.content T) = w} :=
  (rfl)

/-- A Kostka number is nonzero exactly when a tableau of the prescribed shape and content
exists. -/
theorem diagramKostkaNumber_ne_zero_iff {μ : YoungDiagram} {w : ℕ → ℕ} :
    diagramKostkaNumber μ w ≠ 0 ↔
      ∃ T : _root_.SemistandardYoungTableau μ, ⇑(SemistandardYoungTableau.content T) = w := by
  rw [diagramKostkaNumber_def, Nat.card_ne_zero]
  exact ⟨fun h => h.1.elim fun T => ⟨T.1, T.2⟩, fun ⟨T, hT⟩ => ⟨⟨⟨T, hT⟩⟩, inferInstance⟩⟩

/-- **The diagonal Kostka number is `1`**: the highest-weight tableau is the only semistandard
tableau of shape `μ` whose content is the row lengths of `μ`. -/
@[simp]
theorem diagramKostkaNumber_rowLen (μ : YoungDiagram) : diagramKostkaNumber μ μ.rowLen = 1 := by
  rw [diagramKostkaNumber_def, Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun T T' => Subtype.ext ?_⟩,
    ⟨⟨_root_.SemistandardYoungTableau.highestWeight μ,
      SemistandardYoungTableau.content_highestWeight μ⟩⟩⟩
  rw [SemistandardYoungTableau.eq_highestWeight_of_content_eq_rowLen T.2,
    SemistandardYoungTableau.eq_highestWeight_of_content_eq_rowLen T'.2]

/-- **Partial-sum bound for a nonzero Kostka number**: if `K_{μ w} ≠ 0` then every partial sum of
`w` is bounded by the corresponding partial sum of the row lengths of `μ`.  For partitions this
becomes the dominance statement `TauCeti.dominates_of_kostkaNumber_ne_zero`. -/
theorem sum_le_sum_take_rowLens_of_diagramKostkaNumber_ne_zero {μ : YoungDiagram} {w : ℕ → ℕ}
    (h : diagramKostkaNumber μ w ≠ 0) (k : ℕ) :
    ∑ i ∈ Finset.range k, w i ≤ (μ.rowLens.take k).sum := by
  obtain ⟨T, hT⟩ := diagramKostkaNumber_ne_zero_iff.mp h
  calc
    ∑ i ∈ Finset.range k, w i = ∑ i ∈ Finset.range k, SemistandardYoungTableau.content T i :=
      Finset.sum_congr rfl fun i _ => (congrFun hT i).symm
    _ ≤ (μ.rowLens.take k).sum := SemistandardYoungTableau.sum_content_le_sum_take_rowLens T k

/-- The **Kostka number** `K_{μ ν}` of two partitions of the same natural number: the number of
semistandard tableaux of the shape of `μ` whose content is the row lengths of the diagram of `ν`,
that is (by `YoungDiagram.rowLen_ofPartition`), the tableaux using the entry `i` exactly as often as
the `i`-th largest part of `ν` prescribes. -/
noncomputable def kostkaNumber {n : ℕ} (μ ν : n.Partition) : ℕ :=
  diagramKostkaNumber (ofPartition μ) (ofPartition ν).rowLen

/-- The Kostka number of two partitions is the Kostka number of the diagram of `μ` together with
the row lengths of the diagram of `ν`. -/
theorem kostkaNumber_def {n : ℕ} (μ ν : n.Partition) :
    kostkaNumber μ ν = diagramKostkaNumber (ofPartition μ) (ofPartition ν).rowLen := (rfl)

/-- A Kostka number of two partitions is nonzero exactly when a tableau of shape `μ` and content
`ν` exists. -/
theorem kostkaNumber_ne_zero_iff {n : ℕ} {μ ν : n.Partition} :
    kostkaNumber μ ν ≠ 0 ↔ ∃ T : _root_.SemistandardYoungTableau (ofPartition μ),
      ⇑(SemistandardYoungTableau.content T) = (ofPartition ν).rowLen := by
  rw [kostkaNumber_def, diagramKostkaNumber_ne_zero_iff]

/-- A partition contributes exactly one tableau to its own Kostka number. -/
@[simp]
theorem kostkaNumber_self {n : ℕ} (μ : n.Partition) : kostkaNumber μ μ = 1 :=
  (kostkaNumber_def μ μ).trans (diagramKostkaNumber_rowLen _)

/-- **The Kostka numbers are triangular for the dominance order**: `K_{μ ν} ≠ 0` forces `μ` to
dominate `ν`. -/
theorem dominates_of_kostkaNumber_ne_zero {n : ℕ} {μ ν : n.Partition}
    (h : kostkaNumber μ ν ≠ 0) : μ.Dominates ν := by
  refine Nat.Partition.dominates_iff.mpr fun k => ?_
  rw [kostkaNumber_def] at h
  have hk := sum_le_sum_take_rowLens_of_diagramKostkaNumber_ne_zero h k
  rwa [YoungDiagram.sum_range_rowLen_eq_card_filter_fst,
    ← YoungDiagram.sum_take_rowLens_eq_card_filter_fst,
    YoungDiagram.rowLens_ofPartition_eq_sort_parts,
    YoungDiagram.rowLens_ofPartition_eq_sort_parts] at hk

/-- **The Kostka numbers vanish off the dominance order**: there is no semistandard tableau of
shape `μ` and content `ν` unless `μ` dominates `ν`. -/
theorem kostkaNumber_eq_zero_of_not_dominates {n : ℕ} {μ ν : n.Partition}
    (h : ¬ μ.Dominates ν) : kostkaNumber μ ν = 0 :=
  not_not.mp fun h' => h (dominates_of_kostkaNumber_ne_zero h')

end TauCeti
end
end TAF_LiteralSource_0642

section TAF_LiteralSource_0643
/- Original module: TauCeti.Combinatorics.Young.Interlacing -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Interlacing shapes and the branching of bounded tableaux

A Young diagram `ν` **interlaces** `μ` when their row lengths alternate,
`μ₀ ≥ ν₀ ≥ μ₁ ≥ ν₁ ≥ ⋯`; equivalently `ν ⊆ μ` and the skew shape `μ / ν` is a *horizontal
strip*, having at most one cell in each column.  This file defines that relation,
`YoungDiagram.InterlacedBy`, packages the shapes interlacing a fixed `μ` and having at most
`n` rows as a `Finset`, `YoungDiagram.interlacingShapes`, and proves the combinatorial
heart of the `GLₙ₊₁ ↓ GLₙ` branching rule.

That heart is a bijection.  A semistandard tableau of shape `μ` written in the `n + 1` letters
`{0, …, n}` is the same thing as a choice of a shape `ν` interlacing `μ` together with a
semistandard tableau of shape `ν` written in the `n` letters `{0, …, n - 1}`: the cells carrying
the top letter `n` are exactly the cells of `μ / ν`.  Interlacing is precisely the condition making
this work.  One direction is easy — rows increase weakly, so in each row the cells with a small
entry form a prefix, and columns increase strictly, so `μᵢ₊₁ ≤ νᵢ`.  The converse is where
interlacing does its work: filling every cell of `μ / ν` with the single letter `n` keeps the
columns strict exactly because `μ / ν` has no two cells in a column, which is `μᵢ₊₁ ≤ νᵢ`.

Interlacing also has a reading on beta-numbers, `TauCeti.forall_betaNumber_le_iff_interlacedBy`:
shifting the row lengths by the staircase turns the alternating inequalities into the statement that
the comparisons `ν_j + (N - 1 - j) ≤ μ_i + (N - 1 - i)` hold exactly for `i ≤ j`.  That is the form
in which horizontal strips appear in the Pieri rule.

The bijection is stated fibrewise, as `TauCeti.BoundedSSYT.fiberEquiv`: the tableaux of shape `μ`
whose sub-shape of small entries is a *given* `ν` are the tableaux of shape `ν`.  Phrasing it this
way keeps every type non-dependent, so the resulting sum decomposition
`TauCeti.BoundedSSYT.sum_eq_sum_interlacingShapes` needs no transport along an equality of shapes.

## Main definitions

* `YoungDiagram.InterlacedBy`: `InterlacedBy μ ν` says that `ν` interlaces `μ`, that is
  `μ.rowLen (i + 1) ≤ ν.rowLen i` and `ν.rowLen i ≤ μ.rowLen i` for every `i`.  The shape being
  interlaced is written first, as in `TauCeti.Interlaces` for integer sequences.
* `YoungDiagram.interlacingShapes`: the shapes interlacing `μ` with at most `n` rows.
* `TauCeti.BoundedSSYT.restrictShape`: the cells of `μ` whose entry is smaller than `n`.
* `TauCeti.BoundedSSYT.restrict` and `TauCeti.BoundedSSYT.extend`: erasing the cells carrying the
  top letter, and putting them back.

## Main results

* `YoungDiagram.sum_interlacingShapes_eq_sum_piFinset`: the shapes with at most `n` rows
  interlacing a shape with at most `n + 1` rows are parametrized by their row lengths, the `j`-th
  drawn freely from `[μ_{j+1}, μ_j]`.
* `TauCeti.forall_betaNumber_le_iff_interlacedBy`: interlacing read on beta-numbers, the
  comparisons of the beta-numbers of the two shapes cutting out the initial segments.
* `TauCeti.BoundedSSYT.restrictShape_mem_interlacingShapes`: the sub-shape of small entries
  interlaces `μ` and has at most `n` rows.
* `TauCeti.BoundedSSYT.content_restrict`: erasing the top letter leaves unchanged how often each
  of the remaining letters occurs.
* `TauCeti.BoundedSSYT.fiberEquiv`: the tableaux of shape `μ` in `n + 1` letters with a given
  sub-shape `ν` of small entries are the tableaux of shape `ν` in `n` letters.
* `TauCeti.BoundedSSYT.sum_eq_sum_interlacingShapes`: the resulting decomposition of a sum over
  the tableaux of shape `μ`, indexed by the interlacing shapes, and
  `TauCeti.BoundedSSYT.card_eq_sum_interlacingShapes`: its counting form, the branching rule for
  the number of tableaux.

## References

* [W. Fulton, *Young Tableaux*][fulton1997], Section 2.2.
* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/RepresentationTheory/ClassicalGroups/README.md),
  Layer 6, "branching rules".
-/

public section

namespace YoungDiagram

variable {μ ν : _root_.YoungDiagram}

/-- `YoungDiagram.InterlacedBy μ ν` says that the Young diagram `ν` **interlaces** `μ`: the
two sequences of row lengths alternate, `μ₀ ≥ ν₀ ≥ μ₁ ≥ ν₁ ≥ ⋯`.  Equivalently `ν ⊆ μ` and the
skew shape `μ / ν` is a horizontal strip: no column of `μ` contains two of its cells.

As for the integer sequences of `TauCeti.Interlaces`, the shape being interlaced is written
first. -/
def InterlacedBy (μ ν : _root_.YoungDiagram) : Prop :=
  ∀ i, μ.rowLen (i + 1) ≤ ν.rowLen i ∧ ν.rowLen i ≤ μ.rowLen i

/-- Interlacing unfolded: the pair of inequalities at each row.  This is the introduction and
elimination rule for `YoungDiagram.InterlacedBy`, whose body is not exposed. -/
@[simp]
theorem interlacedBy_iff :
    InterlacedBy μ ν ↔ ∀ i, μ.rowLen (i + 1) ≤ ν.rowLen i ∧ ν.rowLen i ≤ μ.rowLen i :=
  Iff.rfl

/-- An interlacing shape reaches at least as far as the next row of the shape it interlaces. -/
theorem InterlacedBy.rowLen_succ_le (h : InterlacedBy μ ν) (i : ℕ) :
    μ.rowLen (i + 1) ≤ ν.rowLen i :=
  (h i).1

/-- An interlacing shape reaches no further than the shape it interlaces. -/
theorem InterlacedBy.rowLen_le (h : InterlacedBy μ ν) (i : ℕ) : ν.rowLen i ≤ μ.rowLen i :=
  (h i).2

/-- An interlacing shape is a sub-diagram. -/
theorem InterlacedBy.le (h : InterlacedBy μ ν) : ν ≤ μ :=
  le_of_forall_rowLen_le h.rowLen_le

/-- **A horizontal strip has at most one cell in a column**: if `ν` interlaces `μ`, then a cell of
`μ` strictly below row `i` already lies in `ν` at row `i`.  This is the form of interlacing that
keeps a column strict when the whole of `μ / ν` is filled with one letter. -/
theorem InterlacedBy.mem_of_lt (h : InterlacedBy μ ν) {i₁ i₂ j : ℕ} (hi : i₁ < i₂)
    (hc : ((i₂, j) : ℕ × ℕ) ∈ μ) : ((i₁, j) : ℕ × ℕ) ∈ ν :=
  _root_.YoungDiagram.mem_iff_lt_rowLen.mpr
    ((_root_.YoungDiagram.mem_iff_lt_rowLen.mp hc).trans_le
      ((μ.rowLen_anti (i₁ + 1) i₂ hi).trans (h.rowLen_succ_le i₁)))

/-- **The shapes interlacing `μ` with at most `n` rows.**  These index the summands of the
`GLₙ₊₁ ↓ GLₙ` branching rule; the row bound is genuine, since a shape may interlace `μ` and still
be too tall to be written in `n` letters. -/
noncomputable def interlacingShapes (n : ℕ) (μ : _root_.YoungDiagram) :
    Finset _root_.YoungDiagram :=
  Set.Finite.toFinset (s := {ν : _root_.YoungDiagram | InterlacedBy μ ν ∧ ν.colLen 0 ≤ n})
    ((finite_Iic μ).subset fun _ h => Set.mem_Iic.mpr h.1.le)

@[simp]
theorem mem_interlacingShapes {n : ℕ} :
    ν ∈ interlacingShapes n μ ↔ InterlacedBy μ ν ∧ ν.colLen 0 ≤ n :=
  Set.Finite.mem_toFinset _

/-- **The shapes interlacing `μ` are parametrized by their row lengths.**  For a shape `μ` with at
most `n + 1` rows, a shape `ν` with at most `n` rows interlaces `μ` exactly when its `j`-th row
length lies in `[μ_{j+1}, μ_j]` for each `j < n`, and it is determined by those row lengths.  So a
sum over the interlacing shapes is a sum over the families `r : Fin n → ℕ` drawn from those
intervals. -/
theorem sum_interlacingShapes_eq_sum_piFinset {M : Type*} [AddCommMonoid M] {n : ℕ}
    (hμ : μ.colLen 0 ≤ n + 1) (f : (Fin n → ℕ) → M) :
    ∑ ν ∈ interlacingShapes n μ, f (fun j => ν.rowLen j) =
      ∑ r ∈ Fintype.piFinset fun j : Fin n => Finset.Icc (μ.rowLen ((j : ℕ) + 1)) (μ.rowLen j),
        f r := by
  refine Finset.sum_bij (fun ν _ j => ν.rowLen j) (fun ν hν => ?_) (fun ν₁ hν₁ ν₂ hν₂ h => ?_)
    (fun r hr => ?_) fun _ _ => rfl
  · obtain ⟨hint, -⟩ := mem_interlacingShapes.mp hν
    exact Fintype.mem_piFinset.mpr fun j => Finset.mem_Icc.mpr (interlacedBy_iff.mp hint j)
  · refine rowLen_injective (funext fun i => ?_)
    rcases lt_or_ge i n with hi | hi
    · exact congrFun h ⟨i, hi⟩
    · rw [rowLen_eq_zero_of_colLen_le ((mem_interlacingShapes.mp hν₁).2.trans hi),
        rowLen_eq_zero_of_colLen_le ((mem_interlacingShapes.mp hν₂).2.trans hi)]
  · have hr' : ∀ j : Fin n, μ.rowLen ((j : ℕ) + 1) ≤ r j ∧ r j ≤ μ.rowLen j := fun j =>
      Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hr j)
    have hanti : Antitone r := fun j k hjk => by
      rcases hjk.eq_or_lt with rfl | hlt
      · exact le_rfl
      · exact ((hr' k).2.trans (μ.rowLen_anti _ _ (Nat.succ_le_of_lt hlt))).trans (hr' j).1
    refine ⟨ofRowLensFin r hanti, mem_interlacingShapes.mpr
      ⟨interlacedBy_iff.mpr fun i => ?_, colLen_zero_ofRowLensFin_le r hanti⟩,
      funext fun j => rowLen_ofRowLensFin r hanti j⟩
    rcases lt_or_ge i n with hi | hi
    · have h := rowLen_ofRowLensFin r hanti ⟨i, hi⟩
      rw [Fin.val_mk] at h
      rw [h]
      exact hr' ⟨i, hi⟩
    · rw [rowLen_ofRowLensFin_eq_zero_of_le r hanti hi,
        rowLen_eq_zero_of_colLen_le (hμ.trans (by omega))]
      exact ⟨le_rfl, Nat.zero_le _⟩

end YoungDiagram

namespace TauCeti

/-- **Interlacing, read on beta-numbers.**  For diagrams `μ` and `ν` with at most `N` rows, the
beta-number of `ν` at `j` is at most the beta-number of `μ` at `i` exactly for `i ≤ j` precisely
when the row lengths interlace, `μ₀ ≥ ν₀ ≥ μ₁ ≥ ⋯`, that is, when `μ / ν` is a horizontal strip. -/
theorem forall_betaNumber_le_iff_interlacedBy {N : ℕ} {μ ν : YoungDiagram}
    (hμ : μ.colLen 0 ≤ N) (hν : ν.colLen 0 ≤ N) :
    (∀ i j : Fin N, ν.betaNumber N j ≤ μ.betaNumber N i ↔ i ≤ j) ↔
      μ.InterlacedBy ν := by
  simp only [YoungDiagram.betaNumber_def, YoungDiagram.interlacedBy_iff]
  constructor
  · intro h i
    have h' : ∀ a b : ℕ, a < N → b < N →
        (ν.rowLen b + (N - 1 - b) ≤ μ.rowLen a + (N - 1 - a) ↔ a ≤ b) := by
      intro a b ha hb
      simpa [Fin.le_def] using h ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨?_, ?_⟩
    · by_cases hi : i + 1 < N
      · have hlt := ((h' (i + 1) i hi (by omega)).not).mpr (by omega)
        omega
      · rw [YoungDiagram.rowLen_eq_zero_of_colLen_le (hμ.trans (by omega))]
        exact Nat.zero_le _
    · by_cases hi : i < N
      · have := (h' i i hi hi).mpr le_rfl
        omega
      · rw [YoungDiagram.rowLen_eq_zero_of_colLen_le (hν.trans (by omega))]
        exact Nat.zero_le _
  · intro h i j
    rw [Fin.le_def]
    have hiN : (i : ℕ) < N := i.isLt
    have hjN : (j : ℕ) < N := j.isLt
    refine ⟨fun hle => ?_, fun hle => ?_⟩
    · by_contra hij
      have h1 : μ.rowLen i ≤ μ.rowLen ((j : ℕ) + 1) := μ.rowLen_anti _ _ (by omega)
      have h2 : μ.rowLen ((j : ℕ) + 1) ≤ ν.rowLen j := (h j).1
      omega
    · have h1 : ν.rowLen j ≤ μ.rowLen j := (h j).2
      have h2 : μ.rowLen j ≤ μ.rowLen i := μ.rowLen_anti _ _ hle
      omega

namespace BoundedSSYT

variable {n : ℕ} {μ ν : _root_.YoungDiagram}

/-- **The sub-shape of small entries**: the cells of `μ` whose entry is smaller than the top letter
`n`.  It is a Young diagram because the entries increase weakly to the right and downwards. -/
def restrictShape (T : BoundedSSYT (n + 1) μ) : _root_.YoungDiagram where
  cells := μ.cells.filter fun c => T.1 c.1 c.2 < n
  isLowerSet := by
    rintro c d hdc hc
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hc ⊢
    exact ⟨μ.isLowerSet hdc hc.1,
      lt_of_le_of_lt (SemistandardYoungTableau.entry_le_of_le T.1 hdc.1 hdc.2 hc.1) hc.2⟩

@[simp]
theorem mem_restrictShape {T : BoundedSSYT (n + 1) μ} {i j : ℕ} :
    ((i, j) : ℕ × ℕ) ∈ restrictShape T ↔ ((i, j) : ℕ × ℕ) ∈ μ ∧ T.1 i j < n :=
  Finset.mem_filter

/-- Reading the defining property of `TauCeti.BoundedSSYT.restrictShape` off an equation naming
it. -/
theorem mem_iff_of_restrictShape_eq {T : BoundedSSYT (n + 1) μ} (hν : restrictShape T = ν)
    {i j : ℕ} : ((i, j) : ℕ × ℕ) ∈ ν ↔ ((i, j) : ℕ × ℕ) ∈ μ ∧ T.1 i j < n := by
  subst hν; exact mem_restrictShape

/-- The sub-shape of small entries is a sub-diagram. -/
theorem restrictShape_le (T : BoundedSSYT (n + 1) μ) : restrictShape T ≤ μ := by
  rintro ⟨i, j⟩ hc
  exact (mem_restrictShape.mp hc).1

/-- **The sub-shape of small entries interlace the shape.**  Every cell of `μ` in row `i + 1`
carries an entry at most `n`, so column strictness makes the entry of the cell directly above it
smaller than `n`, and that cell is therefore small: this is the inequality `μᵢ₊₁ ≤ νᵢ`. -/
theorem interlacedBy_restrictShape (T : BoundedSSYT (n + 1) μ) :
    YoungDiagram.InterlacedBy μ (restrictShape T) :=
  fun i => ⟨YoungDiagram.le_rowLen_of_forall_mem fun j hj => by
      have hc : ((i + 1, j) : ℕ × ℕ) ∈ μ := _root_.YoungDiagram.mem_iff_lt_rowLen.mpr hj
      have hlt : T.1 i j < T.1 (i + 1) j := T.1.col_strict (Nat.lt_succ_self i) hc
      have hbound : T.1 (i + 1) j < n + 1 := entry_lt T hc
      exact mem_restrictShape.mpr ⟨μ.up_left_mem (Nat.le_succ i) le_rfl hc, by omega⟩,
    YoungDiagram.rowLen_le_of_le (restrictShape_le T) i⟩

/-- **The sub-shape of small entries is written in `n` letters**, so it has at most `n` rows: the
entry in row `i` is at least `i`. -/
theorem colLen_zero_restrictShape_le (T : BoundedSSYT (n + 1) μ) :
    (restrictShape T).colLen 0 ≤ n := by
  by_contra h
  have hmem : ((n, 0) : ℕ × ℕ) ∈ restrictShape T :=
    _root_.YoungDiagram.mem_iff_lt_colLen.mpr (Nat.lt_of_not_le h)
  obtain ⟨hμ, hlt⟩ := mem_restrictShape.mp hmem
  exact absurd (SemistandardYoungTableau.le_entry T.1 hμ) (by omega)

/-- The sub-shape of small entries is one of the shapes the branching rule sums over. -/
theorem restrictShape_mem_interlacingShapes (T : BoundedSSYT (n + 1) μ) :
    restrictShape T ∈ YoungDiagram.interlacingShapes n μ :=
  YoungDiagram.mem_interlacingShapes.mpr
    ⟨interlacedBy_restrictShape T, colLen_zero_restrictShape_le T⟩

/-- **Erasing the top letter, as a filling**: keep the entries on the sub-shape `ν` of small
entries and drop the rest.  The shape is passed as a parameter, together with the equation
identifying it, so that the result lives in a type that does not depend on `T`.  Only the bounded
form `TauCeti.BoundedSSYT.restrict` is part of the interface. -/
private def restrictTableau (T : BoundedSSYT (n + 1) μ) (ν : _root_.YoungDiagram)
    (hν : restrictShape T = ν) : _root_.SemistandardYoungTableau ν where
  entry := fun i j => if ((i, j) : ℕ × ℕ) ∈ ν then T.1 i j else 0
  row_weak' := fun {i j₁ j₂} hj hc => by
    have hc₁ : ((i, j₁) : ℕ × ℕ) ∈ ν := ν.up_left_mem le_rfl hj.le hc
    rw [ite_eq_left hc₁, ite_eq_left hc]
    exact T.1.row_weak hj ((mem_iff_of_restrictShape_eq hν).mp hc).1
  col_strict' := fun {i₁ i₂ j} hi hc => by
    have hc₁ : ((i₁, j) : ℕ × ℕ) ∈ ν := ν.up_left_mem hi.le le_rfl hc
    rw [ite_eq_left hc₁, ite_eq_left hc]
    exact T.1.col_strict hi ((mem_iff_of_restrictShape_eq hν).mp hc).1
  zeros' := fun {_ _} hc => ite_eq_right hc

/-- The entries of the filling underlying `TauCeti.BoundedSSYT.restrict`. -/
private theorem restrictTableau_apply (T : BoundedSSYT (n + 1) μ) (ν : _root_.YoungDiagram)
    (hν : restrictShape T = ν) (i j : ℕ) :
    restrictTableau T ν hν i j = if ((i, j) : ℕ × ℕ) ∈ ν then T.1 i j else 0 :=
  (rfl)

/-- **Erasing the top letter**: a tableau of shape `μ` in the letters `{0, …, n}` restricts to a
tableau of shape `ν` in the letters `{0, …, n - 1}`, where `ν` is its sub-shape of small entries.
The shape is passed as a parameter, together with the equation identifying it, so that the result
lives in a type that does not depend on `T`. -/
def restrict (T : BoundedSSYT (n + 1) μ) (ν : _root_.YoungDiagram) (hν : restrictShape T = ν) :
    BoundedSSYT n ν :=
  ⟨restrictTableau T ν hν, fun i j hc => by
    rw [restrictTableau_apply, ite_eq_left hc]
    exact ((mem_iff_of_restrictShape_eq hν).mp hc).2⟩

/-- The entries of a restricted tableau. -/
@[simp]
theorem restrict_apply (T : BoundedSSYT (n + 1) μ) (ν : _root_.YoungDiagram)
    (hν : restrictShape T = ν) (i j : ℕ) :
    (restrict T ν hν).1 i j = if ((i, j) : ℕ × ℕ) ∈ ν then T.1 i j else 0 :=
  restrictTableau_apply T ν hν i j

/-- **Erasing the top letter changes no other multiplicity**: the cells of `μ` carrying a letter
smaller than the top letter `n` are exactly the cells of the sub-shape `ν`, and there the two
tableaux agree, so each such letter occupies as many cells of `ν` as it does of `μ`. -/
@[simp]
theorem content_restrict (T : BoundedSSYT (n + 1) μ) (hν : restrictShape T = ν) {i : ℕ}
    (hi : i < n) :
    SemistandardYoungTableau.content (restrict T ν hν).1 i
      = SemistandardYoungTableau.content T.1 i := by
  rw [SemistandardYoungTableau.content_apply, SemistandardYoungTableau.content_apply]
  have hcells : (ν.cells.filter fun c => (restrict T ν hν).1 c.1 c.2 = i)
      = μ.cells.filter fun c => T.1 c.1 c.2 = i := by
    ext c
    obtain ⟨a, b⟩ := c
    simp only [Finset.mem_filter, _root_.YoungDiagram.mem_cells, restrict_apply]
    grind [mem_iff_of_restrictShape_eq]
  rw [hcells]

/-- **Restoring the top letter, as a filling**: keep the entries of `T` on `ν` and write the letter
`n` on every cell of `μ / ν`.  Columns stay strict because `ν` interlaces `μ`, so no column of
`μ / ν` holds two cells.  Only the bounded form `TauCeti.BoundedSSYT.extend` is part of the
interface. -/
private def extendTableau (h : YoungDiagram.InterlacedBy μ ν) (T : BoundedSSYT n ν) :
    _root_.SemistandardYoungTableau μ where
  entry := fun i j =>
    if ((i, j) : ℕ × ℕ) ∈ ν then T.1 i j else if ((i, j) : ℕ × ℕ) ∈ μ then n else 0
  row_weak' := fun {i j₁ j₂} hj hc => by
    by_cases hc₂ : ((i, j₂) : ℕ × ℕ) ∈ ν
    · have hc₁ : ((i, j₁) : ℕ × ℕ) ∈ ν := ν.up_left_mem le_rfl hj.le hc₂
      rw [ite_eq_left hc₁, ite_eq_left hc₂]
      exact T.1.row_weak hj hc₂
    · rw [ite_eq_right hc₂, ite_eq_left hc]
      by_cases hc₁ : ((i, j₁) : ℕ × ℕ) ∈ ν
      · rw [ite_eq_left hc₁]
        exact (entry_lt T hc₁).le
      · rw [ite_eq_right hc₁, ite_eq_left (μ.up_left_mem le_rfl hj.le hc)]
  col_strict' := fun {i₁ i₂ j} hi hc => by
    have hc₁ : ((i₁, j) : ℕ × ℕ) ∈ ν := h.mem_of_lt hi hc
    rw [ite_eq_left hc₁]
    by_cases hc₂ : ((i₂, j) : ℕ × ℕ) ∈ ν
    · rw [ite_eq_left hc₂]
      exact T.1.col_strict hi hc₂
    · rw [ite_eq_right hc₂, ite_eq_left hc]
      exact entry_lt T hc₁
  zeros' := fun {_ _} hc => by
    rw [ite_eq_right fun hν => hc (h.le hν), ite_eq_right hc]

/-- The entries of the filling underlying `TauCeti.BoundedSSYT.extend`. -/
private theorem extendTableau_apply (h : YoungDiagram.InterlacedBy μ ν) (T : BoundedSSYT n ν)
    (i j : ℕ) :
    extendTableau h T i j =
      if ((i, j) : ℕ × ℕ) ∈ ν then T.1 i j else if ((i, j) : ℕ × ℕ) ∈ μ then n else 0 :=
  (rfl)

/-- **Restoring the top letter**: filling every cell of `μ / ν` with the letter `n` turns a tableau
of shape `ν` in `n` letters into a tableau of shape `μ` in `n + 1` letters. -/
def extend (h : YoungDiagram.InterlacedBy μ ν) (T : BoundedSSYT n ν) : BoundedSSYT (n + 1) μ :=
  ⟨extendTableau h T, fun i j hc => by
    rw [extendTableau_apply]
    by_cases hc₁ : ((i, j) : ℕ × ℕ) ∈ ν
    · rw [ite_eq_left hc₁]
      exact Nat.lt_succ_of_lt (entry_lt T hc₁)
    · rw [ite_eq_right hc₁, ite_eq_left hc]
      exact Nat.lt_succ_self n⟩

/-- The entries of an extended tableau. -/
@[simp]
theorem extend_apply (h : YoungDiagram.InterlacedBy μ ν) (T : BoundedSSYT n ν) (i j : ℕ) :
    (extend h T).1 i j =
      if ((i, j) : ℕ × ℕ) ∈ ν then T.1 i j else if ((i, j) : ℕ × ℕ) ∈ μ then n else 0 :=
  extendTableau_apply h T i j

/-- Restoring the top letter on the cells of `μ / ν` gives back `ν` as the sub-shape of small
entries. -/
@[simp]
theorem restrictShape_extend (h : YoungDiagram.InterlacedBy μ ν) (T : BoundedSSYT n ν) :
    restrictShape (extend h T) = ν := by
  ext c
  obtain ⟨i, j⟩ := c
  simp only [_root_.YoungDiagram.mem_cells, mem_restrictShape, extend_apply]
  grind [IsConcreteLE.le_iff.mp h.le, entry_lt]

/-- **The branching bijection, fibrewise.**  The tableaux of shape `μ` in the letters `{0, …, n}`
whose sub-shape of small entries is a given `ν` are exactly the tableaux of shape `ν` in the
letters `{0, …, n - 1}`: erasing and restoring the top letter are mutually inverse. -/
def fiberEquiv (h : YoungDiagram.InterlacedBy μ ν) :
    {T : BoundedSSYT (n + 1) μ // restrictShape T = ν} ≃ BoundedSSYT n ν where
  toFun T := restrict T.1 ν T.2
  invFun T := ⟨extend h T, restrictShape_extend h T⟩
  left_inv := by
    rintro ⟨T, hT⟩
    refine Subtype.ext (Subtype.ext (_root_.SemistandardYoungTableau.ext fun i j => ?_))
    rw [extend_apply, restrict_apply]
    by_cases hν : ((i, j) : ℕ × ℕ) ∈ ν
    · rw [ite_eq_left hν, ite_eq_left hν]
    · rw [ite_eq_right hν]
      by_cases hμ : ((i, j) : ℕ × ℕ) ∈ μ
      · rw [ite_eq_left hμ]
        have hnot : ¬ T.1 i j < n := fun hlt => hν ((mem_iff_of_restrictShape_eq hT).mpr ⟨hμ, hlt⟩)
        have hlt := entry_lt T hμ
        have heq : T.1 i j = n := by omega
        exact heq.symm
      · rw [ite_eq_right hμ]
        exact (T.1.zeros hμ).symm
  right_inv := by
    intro T
    refine Subtype.ext (_root_.SemistandardYoungTableau.ext fun i j => ?_)
    rw [restrict_apply, extend_apply]
    by_cases hν : ((i, j) : ℕ × ℕ) ∈ ν
    · rw [ite_eq_left hν, ite_eq_left hν]
    · rw [ite_eq_right hν]
      exact (T.1.zeros hν).symm

/-- The branching bijection erases the top letter. -/
@[simp]
theorem fiberEquiv_apply (h : YoungDiagram.InterlacedBy μ ν)
    (T : {T : BoundedSSYT (n + 1) μ // restrictShape T = ν}) :
    fiberEquiv h T = restrict T.1 ν T.2 :=
  (rfl)

/-- The inverse of the branching bijection restores the top letter. -/
@[simp]
theorem fiberEquiv_symm_apply (h : YoungDiagram.InterlacedBy μ ν) (T : BoundedSSYT n ν) :
    (fiberEquiv h).symm T = ⟨extend h T, restrictShape_extend h T⟩ :=
  (rfl)

/-- **The branching decomposition of a sum over tableaux**: summing over the tableaux of shape `μ`
in the letters `{0, …, n}` is summing, over the shapes `ν` interlacing `μ` with at most `n` rows,
over the tableaux of shape `ν` in the letters `{0, …, n - 1}`. -/
theorem sum_eq_sum_interlacingShapes {M : Type*} [AddCommMonoid M] (n : ℕ)
    (μ : _root_.YoungDiagram) (f : ∀ ν : _root_.YoungDiagram, BoundedSSYT n ν → M) :
    ∑ T : BoundedSSYT (n + 1) μ, f (restrictShape T) (restrict T (restrictShape T) rfl)
      = ∑ ν ∈ YoungDiagram.interlacingShapes n μ, ∑ T : BoundedSSYT n ν, f ν T := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun T _ => restrictShape_mem_interlacingShapes T)
    (fun T => f (restrictShape T) (restrict T (restrictShape T) rfl))]
  refine Finset.sum_congr rfl fun ν hν => ?_
  rw [Finset.sum_subtype (p := fun T : BoundedSSYT (n + 1) μ => restrictShape T = ν) _
    (fun T => by simp)]
  refine Fintype.sum_equiv (fiberEquiv (YoungDiagram.mem_interlacingShapes.mp hν).1) _ _
    fun T => ?_
  obtain ⟨T, hT⟩ := T
  subst hT
  rfl

/-- **The branching rule for the number of tableaux**: the tableaux of shape `μ` in `n + 1` letters
are counted by the tableaux of the shapes interlacing `μ`, written in `n` letters.  The statement
is purely combinatorial; when `μ` has at most `n + 1` rows it is, over `ℂ`, the counting shadow of
the multiplicity-free `GLₙ₊₁ ↓ GLₙ` branching of the irreducible of highest weight `μ`, whose
dimension is the number of such tableaux. -/
theorem card_eq_sum_interlacingShapes (n : ℕ) (μ : _root_.YoungDiagram) :
    Fintype.card (BoundedSSYT (n + 1) μ)
      = ∑ ν ∈ YoungDiagram.interlacingShapes n μ, Fintype.card (BoundedSSYT n ν) := by
  simpa using sum_eq_sum_interlacingShapes n μ fun _ _ => (1 : ℕ)

end BoundedSSYT

end TauCeti
end
end TAF_LiteralSource_0643

section TAF_LiteralSource_0644
/- Original module: TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Schur polynomials

The **Schur polynomial** `s_μ` of a Young diagram `μ` in `N` variables is the generating function
of the semistandard Young tableaux of shape `μ` whose entries are drawn from the `N`-letter
alphabet: each such tableau contributes the monomial `∏ᵢ xᵢ ^ (number of cells filled with i)`.
This file defines it, `TauCeti.diagramSchurPoly`, reads off the basic structure that the
definition alone gives, and transports it to the partition-indexed Schur polynomial
`TauCeti.schurPoly` in an arbitrary finite alphabet.

The tableaux summed over are the bounded ones, `TauCeti.BoundedSSYT`: Mathlib's
`SemistandardYoungTableau μ` fills cells with arbitrary natural numbers, and it is the bound that
makes the sum finite. The alphabet is `0, 1, …, N - 1` rather than the classical `1, …, N`,
matching `SemistandardYoungTableau.content`.

The load-bearing statement is `TauCeti.coeff_diagramSchurPoly`: the coefficient of a monomial
`x^d` in `s_μ` is the image in the coefficient semiring of the Kostka number `K_{μ d}`, the number
of semistandard tableaux of shape `μ` and content `d`. Every other result here is read off it
together with the Kostka theory of `TauCeti.Combinatorics.Young.Kostka`:

* `TauCeti.diagramSchurPoly_eq_zero_iff`: `s_μ` vanishes exactly when `μ` is taller than the
  alphabet, since columns are strict and the entry in row `i` is at least `i`.
* `TauCeti.coeff_diagramSchurPoly_rowLenWeight`: the coefficient at the exponent recording the row
  lengths of `μ` is `1`, the highest-weight tableau being the unique one of that content.
* `TauCeti.coeff_diagramSchurPoly_ofPartition_eq_zero_of_not_dominates`: for partitions, the
  exponent recording the parts of `ν` occurs in `s_μ` only if `μ` dominates `ν`. Together with the
  previous item this is the triangularity of the Schur polynomials against the dominance order,
  and `TauCeti.coeff_diagramSchurPoly_eq_zero_of_sum_lt` is the partial-sum form it comes from.
* `TauCeti.isHomogeneous_diagramSchurPoly`: `s_μ` is homogeneous of degree the number of cells of
  `μ`, every tableau of shape `μ` having that many entries.

An arbitrary finite alphabet `σ` is ordered by `Fintype.equivFin σ`, and `TauCeti.schurPoly σ R μ`
is `TauCeti.diagramSchurPoly` renamed along that ordering. The result does not depend on the
ordering, but that is the symmetry of `s_μ`, which is *not* proved here: it is the Bender-Knuth
involution, and it lives downstream in
`TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Symmetric`.  None of the results below need it.

## Main definitions

* `TauCeti.BoundedSSYT.weight`: the content of a bounded tableau, packaged as an exponent vector
  on the alphabet.
* `TauCeti.diagramSchurPoly`: the Schur polynomial of a Young diagram in the alphabet `Fin N`.
* `TauCeti.rowLenWeight`: the exponent vector recording the row lengths of a shape, the exponent
  of the monomial contributed by the highest-weight tableau.
* `TauCeti.schurPoly`: the Schur polynomial of a partition in a finite alphabet.
* `TauCeti.partWeight`: the exponent vector on a finite alphabet recording the parts of a
  partition.

## Main results

* `TauCeti.coeff_diagramSchurPoly`: the coefficients of a Schur polynomial are the images of the
  Kostka numbers, `TauCeti.coeff_schurPoly` is its form in an arbitrary finite alphabet, and
  `TauCeti.coeff_schurPoly_partWeight` reads it at the exponent of a partition.
* `TauCeti.eval_diagramSchurPoly`: evaluating a Schur polynomial sums the monomials of its
  tableaux.
* `TauCeti.eval_one_diagramSchurPoly_eq_card_boundedSSYT` and
  `TauCeti.eval_one_schurPoly_eq_card_boundedSSYT`: evaluating at one counts the bounded
  tableaux.
* `TauCeti.diagramSchurPoly_eq_zero_iff` and `TauCeti.schurPoly_eq_zero_iff`: a Schur polynomial
  vanishes exactly for a shape taller than its alphabet.
* `TauCeti.isHomogeneous_diagramSchurPoly` and `TauCeti.isHomogeneous_schurPoly`: a Schur
  polynomial is homogeneous of degree the number of cells of its shape.

## References

* [W. Fulton, *Young Tableaux*][fulton1997], Section 2.2.
* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 5.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 7.
-/

public section

namespace TauCeti

open YoungDiagram (ofPartition card_ofPartition)
open Finset MvPolynomial

namespace BoundedSSYT

variable {N : ℕ} {μ : YoungDiagram}

/-- The letters a bounded tableau uses all come from the alphabet, so its content is supported on
the image of `Fin N`. -/
private theorem support_content_subset_range (T : BoundedSSYT N μ) :
    ↑(SemistandardYoungTableau.content T.1).support ⊆ Set.range (Fin.val : Fin N → ℕ) := by
  intro x hx
  simp only [Finset.mem_coe, SemistandardYoungTableau.support_content, Finset.mem_image] at hx
  obtain ⟨c, hc, rfl⟩ := hx
  exact ⟨⟨_, entry_lt T ((YoungDiagram.mem_cells _).mp hc)⟩, rfl⟩

/-- The **weight** of a bounded tableau: its content, read as an exponent vector indexed by the
alphabet `Fin N`. This is the exponent of the monomial the tableau contributes to
`TauCeti.diagramSchurPoly`. -/
noncomputable def weight (T : BoundedSSYT N μ) : Fin N →₀ ℕ :=
  Finsupp.comapDomain Fin.val (SemistandardYoungTableau.content T.1) Fin.val_injective.injOn

@[simp]
theorem weight_apply (T : BoundedSSYT N μ) (i : Fin N) :
    weight T i = SemistandardYoungTableau.content T.1 i :=
  Finsupp.comapDomain_apply _ _ _ _

/-- Extending the weight of a bounded tableau by zero recovers its content: no letter outside the
alphabet occurs. -/
theorem mapDomain_weight (T : BoundedSSYT N μ) :
    Finsupp.mapDomain Fin.val (weight T) = SemistandardYoungTableau.content T.1 :=
  Finsupp.mapDomain_comapDomain _ Fin.val_injective _ (support_content_subset_range T)

/-- The sum of the weight of a bounded tableau of shape `μ` is the number of cells of `μ`: every
cell carries exactly one letter. -/
theorem sum_weight (T : BoundedSSYT N μ) : ∑ i, weight T i = μ.card := by
  simp only [weight_apply]
  rw [Fin.sum_univ_eq_sum_range fun i => SemistandardYoungTableau.content T.1 i]
  exact SemistandardYoungTableau.sum_content_eq_card fun c hc =>
    entry_lt T ((YoungDiagram.mem_cells _).mp hc)

/-- **Boundedness is not an extra condition on a content extended by zero**: a letter outside the
alphabet would have to occur in the content, where the extension puts a zero. -/
private theorem lt_of_content_eq {T : _root_.SemistandardYoungTableau μ} {d : Fin N →₀ ℕ}
    (h : ⇑(SemistandardYoungTableau.content T) = ⇑(Finsupp.mapDomain Fin.val d))
    {i c : ℕ} (hic : (i, c) ∈ μ) : T i c < N := by
  by_contra hlt
  have hmem : SemistandardYoungTableau.content T (T i c) ≠ 0 := by
    rw [← Finsupp.mem_support_iff, SemistandardYoungTableau.support_content]
    exact Finset.mem_image.mpr ⟨(i, c), (YoungDiagram.mem_cells _).mpr hic, rfl⟩
  refine hmem ((congrFun h (T i c)).trans (Finsupp.mapDomain_of_notMem_range _ _ ?_))
  rintro ⟨y, hy⟩
  exact hlt (hy ▸ y.isLt)

/-- The weight of a bounded tableau whose content is an exponent vector extended by zero is that
exponent vector. -/
private theorem weight_eq_of_content_eq (T : BoundedSSYT N μ) {d : Fin N →₀ ℕ}
    (h : ⇑(SemistandardYoungTableau.content T.1) = ⇑(Finsupp.mapDomain Fin.val d)) :
    weight T = d := by
  ext i
  rw [weight_apply, congrFun h i, Finsupp.mapDomain_apply_of_injective Fin.val_injective]

/-- **The bounded tableaux of a given weight are the tableaux of the corresponding content.**
Boundedness is not an extra condition on the right-hand side: a letter outside the alphabet would
have to occur in the content, where the extension by zero puts a zero. -/
private noncomputable def weightFiberEquivContentFiber (N : ℕ) (μ : YoungDiagram)
    (d : Fin N →₀ ℕ) :
    {T : BoundedSSYT N μ // weight T = d} ≃
      {T : _root_.SemistandardYoungTableau μ //
        ⇑(SemistandardYoungTableau.content T) = ⇑(Finsupp.mapDomain Fin.val d)} where
  toFun T := ⟨T.1.1, by rw [← mapDomain_weight T.1, T.2]⟩
  invFun T := ⟨⟨T.1, fun _ _ hic => lt_of_content_eq T.2 hic⟩, weight_eq_of_content_eq _ T.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The number of bounded tableaux of a given weight is a Kostka number. -/
theorem card_weight_eq (d : Fin N →₀ ℕ) :
    Nat.card {T : BoundedSSYT N μ // weight T = d}
      = diagramKostkaNumber μ (Finsupp.mapDomain Fin.val d) :=
  (Nat.card_congr (weightFiberEquivContentFiber N μ d)).trans (diagramKostkaNumber_def _ _).symm

end BoundedSSYT

variable (N : ℕ) (R : Type*) [CommSemiring R] (μ : YoungDiagram)

/-- **The Schur polynomial** `s_μ` of a Young diagram `μ` in the `N` variables `x₀, …, x_{N-1}`:
the generating function of the semistandard Young tableaux of shape `μ` in the alphabet
`{0, …, N - 1}`, each contributing the monomial `∏ᵢ xᵢ ^ (number of cells filled with i)`. -/
noncomputable def diagramSchurPoly : MvPolynomial (Fin N) R :=
  ∑ T : BoundedSSYT N μ, monomial (BoundedSSYT.weight T) 1

/-- The defining sum of a Schur polynomial, one weight monomial per bounded tableau of the
shape.  `TauCeti.diagramSchurPoly` is public, but its *body* is not exposed — this file's
`public section` carries no `@[expose]` — so no equation lemma for it reaches a downstream module;
this restatement is what such a module rewrites with. -/
theorem diagramSchurPoly_eq_sum :
    diagramSchurPoly N R μ = ∑ T : BoundedSSYT N μ, monomial (BoundedSSYT.weight T) 1 :=
  (rfl)

variable {N R μ}

/-- **The coefficients of a Schur polynomial are the Kostka numbers**: the coefficient of `x^d` in
`s_μ` is the image in `R` of the number of semistandard tableaux of shape `μ` whose content
is `d`. -/
theorem coeff_diagramSchurPoly (d : Fin N →₀ ℕ) :
    (diagramSchurPoly N R μ).coeff d
      = (diagramKostkaNumber μ (Finsupp.mapDomain Fin.val d) : R) := by
  classical
  rw [diagramSchurPoly]
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_boole, ← BoundedSSYT.card_weight_eq d, Nat.card_eq_fintype_card,
    Fintype.card_subtype]

/-- **A Schur polynomial is the generating function of its tableaux**, in the literal sense: at any
family of values it is the sum, over the bounded tableaux of its shape, of the product of the
values raised to the multiplicities of the corresponding letters. -/
theorem eval_diagramSchurPoly (y : Fin N → R) :
    eval y (diagramSchurPoly N R μ)
      = ∑ T : BoundedSSYT N μ, ∏ i, y i ^ BoundedSSYT.weight T i := by
  rw [diagramSchurPoly, map_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [eval_monomial, one_mul]
  exact Finsupp.prod_fintype _ _ fun _ => pow_zero _

/-- **A Schur polynomial evaluated at one counts bounded semistandard tableaux.**  Every monomial
in the tableau generating function contributes one, so the value is the cardinality of
`TauCeti.BoundedSSYT N μ`. -/
@[simp] theorem eval_one_diagramSchurPoly_eq_card_boundedSSYT (N : ℕ) (μ : YoungDiagram) :
    eval (fun _ : Fin N => (1 : R)) (diagramSchurPoly N R μ) =
      (Nat.card (BoundedSSYT N μ) : R) := by
  rw [eval_diagramSchurPoly]
  simp only [one_pow, prod_const_one, sum_const, card_univ, Nat.card_eq_fintype_card,
    nsmul_eq_mul, mul_one]

/-- Scalars pass through a Schur polynomial: every coefficient is the cast of a natural number,
namely of a Kostka number, and casts of natural numbers are preserved by semiring homomorphisms. -/
theorem map_diagramSchurPoly {S : Type*} [CommSemiring S] (f : R →+* S) :
    MvPolynomial.map f (diagramSchurPoly N R μ) = diagramSchurPoly N S μ := by
  ext d
  rw [MvPolynomial.coeff_map, coeff_diagramSchurPoly, coeff_diagramSchurPoly, map_natCast]

/-- **A Schur polynomial of a shape taller than its alphabet vanishes**, there being no tableau to
sum over. -/
theorem diagramSchurPoly_eq_zero_of_lt_colLen (h : N < μ.colLen 0) :
    diagramSchurPoly N R μ = 0 := by
  have := BoundedSSYT.isEmpty_of_lt_colLen h
  simp [diagramSchurPoly]

/-- **The Schur polynomial of the empty shape is `1`**, the empty tableau contributing the empty
monomial. -/
@[simp]
theorem diagramSchurPoly_bot : diagramSchurPoly N R (⊥ : YoungDiagram) = 1 := by
  have hw : BoundedSSYT.weight (default : BoundedSSYT N (⊥ : YoungDiagram)) = 0 := by
    ext i
    rw [BoundedSSYT.weight_apply, Finsupp.coe_zero, Pi.zero_apply,
      SemistandardYoungTableau.content_apply]
    simp
  rw [diagramSchurPoly, Finset.univ_unique, Finset.sum_singleton, hw, monomial_zero']
  exact map_one C

variable (N μ)

/-- The exponent vector on the alphabet `Fin N` recording the row lengths of `μ`: the content of
the highest-weight tableau of shape `μ`, and the exponent of the monomial it contributes to
`TauCeti.diagramSchurPoly`. -/
noncomputable def rowLenWeight : Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i : Fin N => μ.rowLen i

@[simp]
theorem rowLenWeight_apply (i : Fin N) : rowLenWeight N μ i = μ.rowLen i :=
  (rfl)

variable {N μ}

/-- Extending the row lengths of a shape no taller than the alphabet by zero recovers them. -/
theorem mapDomain_rowLenWeight (h : μ.colLen 0 ≤ N) :
    ⇑(Finsupp.mapDomain Fin.val (rowLenWeight N μ)) = μ.rowLen := by
  funext j
  by_cases hj : j < N
  · exact Finsupp.mapDomain_apply_of_injective Fin.val_injective _ (⟨j, hj⟩ : Fin N)
  · have hzero : μ.rowLen j = 0 := by
      by_contra hne
      exact hj (lt_of_lt_of_le (YoungDiagram.mem_iff_lt_colLen.mp
        (YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero hne))) h)
    rw [hzero]
    refine Finsupp.mapDomain_of_notMem_range _ _ ?_
    rintro ⟨y, hy⟩
    exact hj (hy ▸ y.isLt)

/-- For a shape taller than the alphabet the row-length exponent records only the rows the
alphabet reaches, so its degree falls short of the number of cells. -/
private theorem degree_rowLenWeight_lt (h : N < μ.colLen 0) :
    (rowLenWeight N μ).degree < μ.card := by
  rw [Finsupp.degree_eq_sum]
  simp only [rowLenWeight_apply]
  rw [Fin.sum_univ_eq_sum_range fun i => μ.rowLen i,
    YoungDiagram.sum_range_rowLen_eq_card_filter_fst]
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).mpr
    ⟨(N, 0), (YoungDiagram.mem_cells _).mpr (YoungDiagram.mem_iff_lt_colLen.mpr h), ?_⟩)
  simp

/-- **The coefficient of a Schur polynomial at the row lengths of its shape is `1`**: the
highest-weight tableau, whose `i`-th row consists of `i`s, is the unique tableau of shape `μ`
whose content is the row lengths of `μ`. -/
theorem coeff_diagramSchurPoly_rowLenWeight (h : μ.colLen 0 ≤ N) :
    (diagramSchurPoly N R μ).coeff (rowLenWeight N μ) = 1 := by
  rw [coeff_diagramSchurPoly, mapDomain_rowLenWeight h, diagramKostkaNumber_rowLen, Nat.cast_one]

/-- **A Schur polynomial of a shape no taller than its alphabet is nonzero.** -/
theorem diagramSchurPoly_ne_zero [Nontrivial R] (h : μ.colLen 0 ≤ N) :
    diagramSchurPoly N R μ ≠ 0 := by
  intro hz
  have h1 := coeff_diagramSchurPoly_rowLenWeight (R := R) h
  rw [hz] at h1
  simp at h1

/-- **A Schur polynomial vanishes exactly for a shape taller than its alphabet.** -/
theorem diagramSchurPoly_eq_zero_iff [Nontrivial R] :
    diagramSchurPoly N R μ = 0 ↔ N < μ.colLen 0 :=
  ⟨fun h => not_le.mp fun hle => diagramSchurPoly_ne_zero hle h,
    diagramSchurPoly_eq_zero_of_lt_colLen⟩

/-- **Triangularity of the Schur polynomials**: an exponent whose partial sums overshoot those of
the row lengths of `μ` does not occur in `s_μ`. For partitions this is the vanishing of `s_μ`
outside the dominance order, `TauCeti.kostkaNumber_eq_zero_of_not_dominates`. -/
theorem coeff_diagramSchurPoly_eq_zero_of_sum_lt {d : Fin N →₀ ℕ} {k : ℕ}
    (h : (μ.rowLens.take k).sum < ∑ i ∈ Finset.range k, Finsupp.mapDomain Fin.val d i) :
    (diagramSchurPoly N R μ).coeff d = 0 := by
  have hzero : diagramKostkaNumber μ (Finsupp.mapDomain Fin.val d) = 0 := by
    by_contra hne
    exact absurd (sum_le_sum_take_rowLens_of_diagramKostkaNumber_ne_zero hne k) (not_le.mpr h)
  rw [coeff_diagramSchurPoly, hzero, Nat.cast_zero]

/-- **A Schur polynomial is homogeneous** of degree the number of cells of its shape: a tableau of
shape `μ` has one entry per cell. -/
theorem isHomogeneous_diagramSchurPoly : (diagramSchurPoly N R μ).IsHomogeneous μ.card :=
  IsHomogeneous.sum _ _ _ fun T _ =>
    isHomogeneous_monomial _ ((Finsupp.degree_eq_sum _).trans (BoundedSSYT.sum_weight T))

/-- The total degree of a nonzero Schur polynomial is the number of cells of its shape. -/
theorem totalDegree_diagramSchurPoly [Nontrivial R] (h : μ.colLen 0 ≤ N) :
    (diagramSchurPoly N R μ).totalDegree = μ.card :=
  isHomogeneous_diagramSchurPoly.totalDegree (diagramSchurPoly_ne_zero h)

section Partition

variable {n : ℕ} (μ ν : n.Partition)

/-- **The coefficients of a Schur polynomial are the Kostka numbers of partitions**: the
coefficient of `s_μ` at the exponent recording the parts of `ν` is the image in `R` of `K_{μν}`.
The row bound is what makes the exponent record all of `ν`: an alphabet shorter than the number of
parts of `ν` would truncate it. -/
theorem coeff_diagramSchurPoly_ofPartition (h : (ofPartition ν).colLen 0 ≤ N) :
    (diagramSchurPoly N R (ofPartition μ)).coeff (rowLenWeight N (ofPartition ν))
      = (kostkaNumber μ ν : R) := by
  rw [coeff_diagramSchurPoly, mapDomain_rowLenWeight h, kostkaNumber_def]

/-- **The Schur polynomials are triangular for the dominance order**: the exponent recording the
parts of `ν` occurs in `s_μ` only if `μ` dominates `ν`. No row bound is needed: an alphabet too
short to record all of `ν` truncates the exponent to one of degree less than `n`, where `s_μ`
vanishes by homogeneity. -/
theorem coeff_diagramSchurPoly_ofPartition_eq_zero_of_not_dominates (hd : ¬ μ.Dominates ν) :
    (diagramSchurPoly N R (ofPartition μ)).coeff (rowLenWeight N (ofPartition ν)) = 0 := by
  rcases le_or_gt ((ofPartition ν).colLen 0) N with h | h
  · rw [coeff_diagramSchurPoly_ofPartition μ ν h, kostkaNumber_eq_zero_of_not_dominates hd,
      Nat.cast_zero]
  · refine isHomogeneous_diagramSchurPoly.coeff_eq_zero ?_
    rw [card_ofPartition]
    exact ((degree_rowLenWeight_lt h).trans_eq (card_ofPartition ν)).ne

end Partition

section Alphabet

variable {σ : Type*} [Fintype σ] {n : ℕ}

/-- **The Schur polynomial** `s_μ` of a partition `μ` in the finite alphabet `σ`: the Schur
polynomial `TauCeti.diagramSchurPoly` of the Young diagram of `μ` in the alphabet
`Fin (Fintype.card σ)`, renamed along the ordering `Fintype.equivFin σ` of `σ`. The ordering does
not matter, `s_μ` being symmetric (`TauCeti.schurPoly_isSymmetric`, proved downstream). -/
noncomputable def schurPoly (σ : Type*) [Fintype σ] (R : Type*) [CommSemiring R] {n : ℕ}
    (μ : n.Partition) : MvPolynomial σ R :=
  rename (Fintype.equivFin σ).symm (diagramSchurPoly (Fintype.card σ) R (ofPartition μ))

/-- The Schur polynomial of a partition is the Schur polynomial of its Young diagram, renamed
along the chosen ordering of the alphabet.  As for `TauCeti.diagramSchurPoly_eq_sum`, the body of
`TauCeti.schurPoly` is not exposed outside this module, so this restatement is what a downstream
module rewrites with. -/
theorem schurPoly_eq_rename (μ : n.Partition) :
    schurPoly σ R μ
      = rename (Fintype.equivFin σ).symm (diagramSchurPoly (Fintype.card σ) R (ofPartition μ)) :=
  (rfl)

/-- **A Schur polynomial evaluated at one counts bounded semistandard tableaux**: the value of
`s_μ` at the all-ones point of the alphabet `σ` is the number of semistandard tableaux of shape
`μ` with entries below the number of letters of `σ`. -/
@[simp] theorem eval_one_schurPoly_eq_card_boundedSSYT (μ : n.Partition) :
    eval (fun _ : σ => (1 : R)) (schurPoly σ R μ) =
      (Nat.card (BoundedSSYT (Fintype.card σ) (ofPartition μ)) : R) := by
  simp [schurPoly_eq_rename, eval_rename, Function.comp_def]

/-- The exponent vector on the alphabet `σ` recording the parts of `ν`, read through the ordering
`Fintype.equivFin σ`: the image of `TauCeti.rowLenWeight` of the Young diagram of `ν`. -/
noncomputable def partWeight (σ : Type*) [Fintype σ] {n : ℕ} (ν : n.Partition) : σ →₀ ℕ :=
  Finsupp.mapDomain (Fintype.equivFin σ).symm (rowLenWeight (Fintype.card σ) (ofPartition ν))

@[simp]
theorem partWeight_apply (ν : n.Partition) (x : σ) :
    partWeight σ ν x = (ofPartition ν).rowLen (Fintype.equivFin σ x) := by
  conv_lhs => rw [partWeight, ← (Fintype.equivFin σ).symm_apply_apply x]
  rw [Finsupp.mapDomain_apply_of_injective (Fintype.equivFin σ).symm.injective, rowLenWeight_apply]

variable (μ ν : n.Partition)

/-- **The coefficients of a Schur polynomial in a finite alphabet are the Kostka numbers**: at the
exponent obtained from `d` by the ordering of the alphabet, the coefficient of `s_μ` is the image
in `R` of the Kostka number of `μ` and the content that `d` extends to by zero. -/
theorem coeff_schurPoly_mapDomain (d : Fin (Fintype.card σ) →₀ ℕ) :
    (schurPoly σ R μ).coeff (Finsupp.mapDomain (Fintype.equivFin σ).symm d)
      = (diagramKostkaNumber (ofPartition μ) (Finsupp.mapDomain Fin.val d) : R) := by
  rw [schurPoly, MvPolynomial.coeff_rename_mapDomain _ (Fintype.equivFin σ).symm.injective,
    coeff_diagramSchurPoly]

/-- **The coefficients of a Schur polynomial in a finite alphabet are the Kostka numbers**: the
coefficient of `s_μ` at an arbitrary exponent `d` is the image in `R` of the Kostka number of `μ`
and the content obtained from `d` by numbering the alphabet with `Fintype.equivFin`. -/
theorem coeff_schurPoly (d : σ →₀ ℕ) :
    (schurPoly σ R μ).coeff d
      = (diagramKostkaNumber (ofPartition μ)
          (Finsupp.mapDomain (fun x => (Fintype.equivFin σ x : ℕ)) d) : R) := by
  have hd : Finsupp.mapDomain (Fintype.equivFin σ).symm
      (Finsupp.mapDomain (Fintype.equivFin σ) d) = d := by
    rw [← Finsupp.mapDomain_comp]
    simp
  conv_lhs => rw [← hd]
  rw [coeff_schurPoly_mapDomain, ← Finsupp.mapDomain_comp]
  rfl

/-- **The coefficient of a Schur polynomial at a partition is a Kostka number**: the coefficient
of `s_μ` at the exponent recording the parts of `ν` is the image in `R` of `K_{μν}`. The row bound
is what makes the exponent record all of `ν`: an alphabet with fewer letters than `ν` has parts
would truncate the record. -/
theorem coeff_schurPoly_partWeight (h : (ofPartition ν).colLen 0 ≤ Fintype.card σ) :
    (schurPoly σ R μ).coeff (partWeight σ ν) = (kostkaNumber μ ν : R) := by
  rw [partWeight, coeff_schurPoly_mapDomain, mapDomain_rowLenWeight h, kostkaNumber_def]

/-- **Schur polynomials are triangular for dominance**: the exponent recording the parts of `ν`
occurs in `s_μ` only if `μ` dominates `ν`. No row bound needed: an alphabet too short to record all
of `ν` truncates the exponent to degree less than `n`, where `s_μ` vanishes by homogeneity. -/
theorem coeff_schurPoly_partWeight_eq_zero_of_not_dominates (hd : ¬ μ.Dominates ν) :
    (schurPoly σ R μ).coeff (partWeight σ ν) = 0 := by
  rw [partWeight, schurPoly]
  rw [MvPolynomial.coeff_rename_mapDomain _ (Fintype.equivFin σ).symm.injective]
  exact coeff_diagramSchurPoly_ofPartition_eq_zero_of_not_dominates μ ν hd

/-- Scalars pass through a Schur polynomial: every coefficient is the cast of a natural number,
namely of a Kostka number, and casts of natural numbers are preserved by semiring homomorphisms. -/
theorem map_schurPoly {S : Type*} [CommSemiring S] (f : R →+* S) :
    MvPolynomial.map f (schurPoly σ R μ) = schurPoly σ S μ := by
  rw [schurPoly, schurPoly, map_rename, map_diagramSchurPoly]

/-- **The Schur polynomial of the partition of `0` is `1`**, its Young diagram being empty and the
empty tableau contributing the empty monomial. -/
@[simp]
theorem schurPoly_partition_zero (p : Nat.Partition 0) : schurPoly σ R p = 1 := by
  have hbot : ofPartition p = ⊥ :=
    YoungDiagram.ext ((Finset.card_eq_zero.mp (card_ofPartition p)).trans
      YoungDiagram.cells_bot.symm)
  rw [schurPoly, hbot, diagramSchurPoly_bot, map_one]

/-- **A Schur polynomial vanishes for a partition with more parts than the alphabet has letters**,
over every commutative semiring; `TauCeti.schurPoly_eq_zero_iff` is the converse over a nontrivial
one. -/
theorem schurPoly_eq_zero_of_card_lt (h : Fintype.card σ < μ.parts.card) :
    schurPoly σ R μ = 0 := by
  rw [schurPoly, diagramSchurPoly_eq_zero_of_lt_colLen
    (by rwa [YoungDiagram.colLen_zero_ofPartition]), map_zero]

/-- **A Schur polynomial vanishes exactly for a partition with more parts than the alphabet has
letters.** -/
theorem schurPoly_eq_zero_iff [Nontrivial R] :
    schurPoly σ R μ = 0 ↔ Fintype.card σ < (ofPartition μ).colLen 0 := by
  rw [schurPoly, map_eq_zero_iff _ (rename_injective _ (Fintype.equivFin σ).symm.injective),
    diagramSchurPoly_eq_zero_iff]

/-- **A Schur polynomial is homogeneous** of degree the natural number its partition partitions: a
tableau of that shape has one entry per cell. -/
theorem isHomogeneous_schurPoly : (schurPoly σ R μ).IsHomogeneous n := by
  have h := isHomogeneous_diagramSchurPoly (N := Fintype.card σ) (R := R) (μ := ofPartition μ)
  rw [card_ofPartition μ] at h
  rw [schurPoly]
  exact h.rename_isHomogeneous

end Alphabet

end TauCeti
end
end TAF_LiteralSource_0644

section TAF_LiteralSource_0645
/- Original module: TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Branching -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The branching rule for Schur polynomials

A Schur polynomial in `n + 1` variables is a polynomial in its last variable whose terms are
Schur polynomials in the first `n`, one term for each shape that **interlaces** its own:

`s_μ(x₀, …, x_n) = ∑_{ν ≺ μ} x_n ^ (|μ| - |ν|) · s_ν(x₀, …, x_{n-1})`.

This is `TauCeti.diagramSchurPoly_eq_sum_interlacingShapes`, an identity of *polynomials* over an
arbitrary commutative semiring.  The exponent of the last variable is forced: the cells of `μ` not
in `ν` are exactly the cells carrying the top letter, so a shape `ν` contributes in degree
`|μ| - |ν|` and in no other — the coefficient of `x_n ^ k` is thus the sum of the `s_ν` over the
interlacing shapes `ν` of cardinality `|μ| - k`, of which there may be several.  Specializing the
last variable recovers the identities of values that this grading refines:
`TauCeti.eval_snoc_diagramSchurPoly` at an arbitrary value, and at `1` the multiplicity-free form

`s_μ(x₀, …, x_{n-1}, 1) = ∑_{ν ≺ μ} s_ν(x₀, …, x_{n-1})`,

both as an identity of polynomials (`TauCeti.aeval_snoc_one_diagramSchurPoly`) and, at a family of
values, as `TauCeti.eval_diagramSchurPoly_of_apply_last_eq_one`.  At `0` instead every term of
positive degree dies, leaving the single degree-zero term, the one for `ν = μ`, and one reads off
the **stability** of Schur polynomials (`TauCeti.aeval_snoc_zero_diagramSchurPoly`): a shape has
the same Schur polynomial in `n` and in `n + 1` variables, once the extra variable is set to zero
— both being zero when the shape has more than `n` rows, so that no term at all survives.

Over `ℂ`, and for a shape `μ` of at most `n + 1` rows — so that `μ` is the highest weight of a
polynomial irreducible of `GLₙ₊₁` and `s_μ` its character — the specialization at `1` reads as the
multiplicity-free branching rule for the restriction `GLₙ₊₁ ↓ GLₙ`: that irreducible restricts to
the direct sum, each with multiplicity one, of the irreducibles whose highest weights interlace
`μ`.  That reading is not proved here, and it does not transfer to positive characteristic: there
the identity of characters no longer forces a direct-sum decomposition, because the representations
of `GLₙ₊₁` are not semisimple in general.  The graded identity is the sharper statement the
Gelfand-Tsetlin theory iterates, since it records not only which shapes occur but the weight of
each occurrence.

Nothing analytic happens here.  `TauCeti.diagramSchurPoly` is by construction the generating
function of the bounded semistandard tableaux of its shape, so the identity is the sum-over-a-
partition form of the bijection `TauCeti.BoundedSSYT.fiberEquiv` of
`TauCeti.Combinatorics.Young.Interlacing`: a tableau in the `n + 1` letters `{0, …, n}` is a
tableau in the `n` letters `{0, …, n - 1}` on an interlacing sub-shape, together with the cells
carrying the top letter `n`.  Those cells are what the last variable counts.

## Main results

* `TauCeti.BoundedSSYT.weight_restrict`: the weight form of `TauCeti.BoundedSSYT.content_restrict`,
  that erasing the top letter of a tableau does not change how often any of the remaining letters
  occurs, and `TauCeti.BoundedSSYT.card_add_weight_last`: the erased letter accounts for exactly
  the cells the sub-shape drops.
* `TauCeti.BoundedSSYT.weight_eq_mapDomain_add_single`: the resulting splitting of the weight of a
  tableau into the weight of its restriction and the multiplicity of the top letter.
* `TauCeti.BoundedSSYT.card_weight_eq_sum_interlacingShapes`: the counting form of that splitting,
  the branching rule for the number of tableaux of a given weight.
* `TauCeti.diagramSchurPoly_eq_sum_interlacingShapes`: **the branching rule**, as an identity of
  polynomials graded by the last variable.
* `TauCeti.aeval_snoc_diagramSchurPoly`: the substitution of an arbitrary value for the last
  variable, in an arbitrary algebra, from which `TauCeti.eval_snoc_diagramSchurPoly`,
  `TauCeti.aeval_snoc_one_diagramSchurPoly`, `TauCeti.eval_snoc_one_diagramSchurPoly` and
  `TauCeti.eval_diagramSchurPoly_of_apply_last_eq_one` — the specializations at an arbitrary
  value and at `1` — are read off.
* `TauCeti.aeval_snoc_zero_diagramSchurPoly`: **stability**, the specialization at `0`.

## References

* [W. Fulton, *Young Tableaux*][fulton1997], Section 2.2.
* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 5, Example 3.
* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/RepresentationTheory/ClassicalGroups/README.md),
  Layer 6, "branching rules".
-/

public section

namespace TauCeti

open MvPolynomial

variable {R : Type*} [CommSemiring R]

namespace BoundedSSYT

variable {n : ℕ} {μ ν : _root_.YoungDiagram}

/-- **Erasing the top letter changes no other multiplicity**, read on weights: the combinatorial
statement is `TauCeti.BoundedSSYT.content_restrict`, and the weight of a bounded tableau is its
content restricted to the alphabet.

Not a `simp` lemma: `simp` already reduces the left-hand side by unfolding `weight` and applying
the `simp` lemma `TauCeti.BoundedSSYT.content_restrict` it transports, so tagging it would only
duplicate that route. -/
theorem weight_restrict (T : BoundedSSYT (n + 1) μ) (hν : restrictShape T = ν) (i : Fin n) :
    weight (restrict T ν hν) i = weight T i.castSucc := by
  rw [weight_apply, weight_apply, Fin.val_castSucc, content_restrict T hν i.isLt]

/-- **The top letter fills exactly the cells the sub-shape drops.**  Every cell of `μ` carries a
letter, and the letters below the top one occupy precisely the cells of the sub-shape `ν`, so the
multiplicity of the top letter makes up the difference `|μ| - |ν|`.  Stated as an addition, which
is the form the exponent bookkeeping of the branching rule needs. -/
theorem card_add_weight_last (T : BoundedSSYT (n + 1) μ) :
    (restrictShape T).card + weight T (Fin.last n) = μ.card := by
  have hsum : ∑ i, weight T i = μ.card := sum_weight T
  rw [Fin.sum_univ_castSucc] at hsum
  rw [← hsum, ← sum_weight (restrict T _ rfl)]
  exact congrArg (· + weight T (Fin.last n))
    (Finset.sum_congr rfl fun i _ => weight_restrict T rfl i)

/-- **The weight of a tableau splits along the top letter**: it is the weight of the restriction,
transported into the first `n` letters, together with the multiplicity of the top letter.  This is
the exponent-vector form of the branching bijection, and is what turns the sum over tableaux
defining a Schur polynomial into a sum of monomials in the last variable. -/
theorem weight_eq_mapDomain_add_single (T : BoundedSSYT (n + 1) μ) (hν : restrictShape T = ν) :
    weight T = Finsupp.mapDomain Fin.castSucc (weight (restrict T ν hν))
      + Finsupp.single (Fin.last n) (weight T (Fin.last n)) := by
  ext i
  induction i using Fin.lastCases with
  | last =>
    rw [Finsupp.add_apply, Finsupp.single_eq_same,
      Finsupp.mapDomain_of_notMem_range _ _
        (by rintro ⟨j, hj⟩; exact absurd hj (Fin.castSucc_lt_last j).ne),
      zero_add]
  | cast j =>
    have hne : Fin.castSucc j ≠ Fin.last n := (Fin.castSucc_lt_last j).ne
    rw [Finsupp.add_apply, Finsupp.mapDomain_apply_of_injective (Fin.castSucc_injective n),
      Finsupp.single_eq_of_ne hne, add_zero, weight_restrict T hν j]

/-- **The weight-refined branching rule for tableaux.**  The tableaux of shape `μ` in the letters
`{0, …, n}` with weight `c` are counted by the tableaux of weight `c` restricted to the letters
`{0, …, n - 1}`, on the shapes `ν` interlacing `μ` with at most `n` rows whose size `|ν|` falls
short of `|μ|` by the multiplicity `c n` of the top letter.  Summing over all weights recovers the
unrefined count `TauCeti.BoundedSSYT.card_eq_sum_interlacingShapes`. -/
theorem card_weight_eq_sum_interlacingShapes (μ : YoungDiagram) (c : Fin (n + 1) → ℕ) :
    Nat.card {T : BoundedSSYT (n + 1) μ // ⇑(weight T) = c} =
      ∑ ν ∈ YoungDiagram.interlacingShapes n μ with ν.card + c (Fin.last n) = μ.card,
        Nat.card {T : BoundedSSYT n ν // ⇑(weight T) = fun i => c i.castSucc} := by
  classical
  have key (T : BoundedSSYT (n + 1) μ) : ⇑(weight T) = c ↔
      (⇑(weight (restrict T (restrictShape T) rfl)) = fun i => c i.castSucc) ∧
        (restrictShape T).card + c (Fin.last n) = μ.card := by
    have hlast := card_add_weight_last T
    simp only [funext_iff, Fin.forall_fin_succ', weight_restrict]
    exact and_congr_right fun _ => by omega
  calc Nat.card {T : BoundedSSYT (n + 1) μ // ⇑(weight T) = c}
      = ∑ T : BoundedSSYT (n + 1) μ,
          if (⇑(weight (restrict T (restrictShape T) rfl)) = fun i => c i.castSucc) ∧
            (restrictShape T).card + c (Fin.last n) = μ.card then 1 else 0 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
        exact Finset.sum_congr rfl fun T _ => if_congr (key T) rfl rfl
    _ = ∑ ν ∈ YoungDiagram.interlacingShapes n μ, ∑ T : BoundedSSYT n ν,
          if (⇑(weight T) = fun i => c i.castSucc) ∧ ν.card + c (Fin.last n) = μ.card
          then 1 else 0 :=
        sum_eq_sum_interlacingShapes n μ fun ν T =>
          if (⇑(weight T) = fun i => c i.castSucc) ∧ ν.card + c (Fin.last n) = μ.card then 1 else 0
    _ = _ := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun ν _ => ?_
        by_cases h : ν.card + c (Fin.last n) = μ.card
        · simp only [h, and_true, ↓reduceIte]
          rw [← Finset.card_filter, ← Fintype.card_subtype, Nat.card_eq_fintype_card]
        · simp [h]

end BoundedSSYT

/-- **The branching rule for Schur polynomials**, as an identity of polynomials over an arbitrary
commutative semiring: `s_μ` in `n + 1` variables is the sum, over the shapes `ν` interlacing `μ`
with at most `n` rows, of `s_ν` in the first `n` variables times the last variable raised to
`|μ| - |ν|`.

Each interlacing shape occurs exactly once, in exactly one degree in the last variable.  Over `ℂ`,
and for a shape `μ` of at most `n + 1` rows, setting the last variable to `1` is the character form
of the multiplicity-free `GLₙ₊₁ ↓ GLₙ` branching rule. -/
theorem diagramSchurPoly_eq_sum_interlacingShapes (n : ℕ) (μ : _root_.YoungDiagram) :
    diagramSchurPoly (n + 1) R μ
      = ∑ ν ∈ YoungDiagram.interlacingShapes n μ,
          X (Fin.last n) ^ (μ.card - ν.card) * rename Fin.castSucc (diagramSchurPoly n R ν) := by
  have key : ∀ T : BoundedSSYT (n + 1) μ,
      (monomial (BoundedSSYT.weight T) (1 : R))
        = X (Fin.last n) ^ (μ.card - (BoundedSSYT.restrictShape T).card) *
            rename Fin.castSucc
              (monomial (BoundedSSYT.weight (BoundedSSYT.restrict T _ rfl)) (1 : R)) := by
    intro T
    have hcard := BoundedSSYT.card_add_weight_last T
    have hexp : μ.card - (BoundedSSYT.restrictShape T).card
        = BoundedSSYT.weight T (Fin.last n) := by omega
    have hw : BoundedSSYT.weight T
        = Finsupp.single (Fin.last n) (BoundedSSYT.weight T (Fin.last n))
          + Finsupp.mapDomain Fin.castSucc
              (BoundedSSYT.weight (BoundedSSYT.restrict T _ rfl)) :=
      (BoundedSSYT.weight_eq_mapDomain_add_single T rfl).trans (add_comm _ _)
    rw [rename_monomial, X_pow_eq_monomial, monomial_mul_monomial, one_mul, hexp]
    exact congrArg (monomial · (1 : R)) hw
  rw [diagramSchurPoly_eq_sum, Finset.sum_congr rfl fun T _ => key T,
    BoundedSSYT.sum_eq_sum_interlacingShapes n μ fun ν S =>
      X (Fin.last n) ^ (μ.card - ν.card) * rename Fin.castSucc (monomial (BoundedSSYT.weight S) 1)]
  exact Finset.sum_congr rfl fun ν _ => by
    rw [← Finset.mul_sum, ← map_sum, diagramSchurPoly_eq_sum]

/-- **The branching rule, with the last variable substituted.**  Substituting a family of values in
an `R`-algebra for the first `n` variables of `s_μ` and `t` for the last gives the sum of
`t ^ (|μ| - |ν|) · s_ν` over the shapes `ν` interlacing `μ`.  The specializations below are the
cases of an evaluation in `R` itself, and of the variables themselves for the first `n`. -/
theorem aeval_snoc_diagramSchurPoly {A : Type*} [CommSemiring A] [Algebra R A] (n : ℕ)
    (μ : _root_.YoungDiagram) (x : Fin n → A) (t : A) :
    aeval (Fin.snoc x t) (diagramSchurPoly (n + 1) R μ)
      = ∑ ν ∈ YoungDiagram.interlacingShapes n μ,
          t ^ (μ.card - ν.card) * aeval x (diagramSchurPoly n R ν) := by
  rw [diagramSchurPoly_eq_sum_interlacingShapes, map_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [map_mul, map_pow, aeval_X, Fin.snoc_last, aeval_rename, Fin.snoc_comp_castSucc]

/-- **The branching rule, evaluated at an arbitrary last value.**  Substituting `t` for the last
variable of `s_μ` gives the sum of `t ^ (|μ| - |ν|) · s_ν` over the shapes `ν` interlacing `μ`. -/
theorem eval_snoc_diagramSchurPoly (n : ℕ) (μ : _root_.YoungDiagram) (x : Fin n → R) (t : R) :
    eval (Fin.snoc x t) (diagramSchurPoly (n + 1) R μ)
      = ∑ ν ∈ YoungDiagram.interlacingShapes n μ,
          t ^ (μ.card - ν.card) * eval x (diagramSchurPoly n R ν) := by
  simpa only [aeval_eq_eval] using aeval_snoc_diagramSchurPoly (R := R) n μ x t

/-- **The branching rule with the last variable set to `1`, as an identity of polynomials.**  This
is stronger than the identity of values `TauCeti.eval_diagramSchurPoly_of_apply_last_eq_one` below:
over a general commutative semiring an identity holding at every family of values need not hold
between the polynomials themselves. -/
theorem aeval_snoc_one_diagramSchurPoly (n : ℕ) (μ : _root_.YoungDiagram) :
    aeval (Fin.snoc (X : Fin n → MvPolynomial (Fin n) R) 1) (diagramSchurPoly (n + 1) R μ)
      = ∑ ν ∈ YoungDiagram.interlacingShapes n μ, diagramSchurPoly n R ν := by
  rw [aeval_snoc_diagramSchurPoly]
  exact Finset.sum_congr rfl fun ν _ => by rw [one_pow, one_mul, aeval_X_left_apply]

/-- **Stability of Schur polynomials.**  A shape has the same Schur polynomial in `n` and in
`n + 1` variables, once the extra variable is set to `0`: only the shape itself survives the
specialization, every other interlacing shape being smaller and so carrying a positive power of
the vanishing variable.  A shape of more than `n` rows interlaces no shape of at most `n` rows
that is as large, so there both sides vanish.

Not a `simp` lemma: substituting polynomials for the variables, `simp` rewrites `aeval` to
`bind₁` by `MvPolynomial.aeval_eq_bind₁`, so this left-hand side is not in `simp`-normal form. -/
theorem aeval_snoc_zero_diagramSchurPoly (n : ℕ) (μ : _root_.YoungDiagram) :
    aeval (Fin.snoc (X : Fin n → MvPolynomial (Fin n) R) 0) (diagramSchurPoly (n + 1) R μ)
      = diagramSchurPoly n R μ := by
  have hvanish : ∀ ν ∈ YoungDiagram.interlacingShapes n μ, ν ≠ μ →
      (0 : MvPolynomial (Fin n) R) ^ (μ.card - ν.card) * aeval X (diagramSchurPoly n R ν) = 0 := by
    intro ν hν hne
    have hsub : ν.cells ⊆ μ.cells :=
      YoungDiagram.cells_subset_iff.mpr (YoungDiagram.mem_interlacingShapes.mp hν).1.le
    have hlt : ν.card < μ.card :=
      Finset.card_lt_card (lt_of_le_of_ne hsub fun h => hne (YoungDiagram.ext h))
    rw [zero_pow (by omega), zero_mul]
  rw [aeval_snoc_diagramSchurPoly]
  rcases le_or_gt (μ.colLen 0) n with hμ | hμ
  · have hself : μ ∈ YoungDiagram.interlacingShapes n μ :=
      YoungDiagram.mem_interlacingShapes.mpr
        ⟨YoungDiagram.interlacedBy_iff.mpr
          fun i => ⟨μ.rowLen_anti i (i + 1) (Nat.le_succ i), le_rfl⟩, hμ⟩
    rw [Finset.sum_eq_single_of_mem μ hself hvanish, Nat.sub_self, pow_zero, one_mul,
      aeval_X_left_apply]
  · rw [diagramSchurPoly_eq_zero_of_lt_colLen hμ]
    refine Finset.sum_eq_zero fun ν hν => hvanish ν hν ?_
    rintro rfl
    have := (YoungDiagram.mem_interlacingShapes.mp hν).2
    omega

/-- **The branching rule for Schur polynomials**, evaluated at a family of values with a `1`
appended. -/
theorem eval_snoc_one_diagramSchurPoly (n : ℕ) (μ : _root_.YoungDiagram) (x : Fin n → R) :
    eval (Fin.snoc x 1) (diagramSchurPoly (n + 1) R μ)
      = ∑ ν ∈ YoungDiagram.interlacingShapes n μ, eval x (diagramSchurPoly n R ν) := by
  rw [eval_snoc_diagramSchurPoly]
  exact Finset.sum_congr rfl fun ν _ => by rw [one_pow, one_mul]

/-- **The branching rule for Schur polynomials**, at any evaluation sending the last variable
to `1`: the value of `s_μ` in `n + 1` variables is the sum of the values of the `s_ν` in the first
`n`, over the shapes `ν` interlacing `μ` with at most `n` rows, each occurring once. -/
theorem eval_diagramSchurPoly_of_apply_last_eq_one (n : ℕ) (μ : _root_.YoungDiagram)
    (x : Fin (n + 1) → R) (hx : x (Fin.last n) = 1) :
    eval x (diagramSchurPoly (n + 1) R μ)
      = ∑ ν ∈ YoungDiagram.interlacingShapes n μ,
          eval (fun i : Fin n => x i.castSucc) (diagramSchurPoly n R ν) := by
  conv_lhs => rw [← Fin.snoc_init_self x, hx]
  rw [eval_snoc_one_diagramSchurPoly, Fin.init_def]

end TauCeti
end
end TAF_LiteralSource_0645

section TAF_LiteralSource_0646
/- Original module: TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Bialternant -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Jacobi's bialternant formula

For a Young diagram `μ` with at most `N` rows, write `λ_j = μ.rowLen j` for its row lengths and
`δ_j = N - 1 - j` for the staircase exponents on the alphabet `Fin N`.  **Jacobi's bialternant
formula** says that the Schur polynomial `s_μ`, defined combinatorially as the generating function
of the semistandard tableaux of shape `μ`, is the quotient of two alternants,
`s_μ = a_{λ+δ} / a_δ`.  The quotient is not itself an operation on `MvPolynomial`, so the formula
is stated here in the division-free form

`s_μ · a_δ = a_{λ+δ}`,

`TauCeti.diagramSchurPoly_mul_alternant`.  It is the symmetric-polynomial form of the Weyl character
formula for `GL_N`, with `a_δ` the Weyl denominator and `a_{λ+δ}` the Weyl numerator; identifying
`s_μ` with the character of the irreducible representation of highest weight `λ` is a separate
statement, not made here.

## Both sides branch in the same way

The tableau side has a branching rule in the last variable,
`TauCeti.diagramSchurPoly_eq_sum_interlacingShapes`:
`s_μ(x₀, …, x_n) = ∑_{ν ≺ μ} x_n ^ (|μ| - |ν|) · s_ν(x₀, …, x_{n-1})`, the sum running over the
shapes `ν` with at most `n` rows interlacing `μ`.  The alternant side satisfies the same rule up to
the Vandermonde factor `∏_{i < n} (x_i - x_n)`: this is
`TauCeti.alternant_eq_prod_mul_sum_interlacingShapes`,

`a_{λ+δ}(x₀, …, x_n) = ∏_{i < n} (x_i - x_n) · ∑_{ν ≺ μ} x_n ^ (|μ| - |ν|) · a_{ν+δ'}(x')`,

with `x' = (x₀, …, x_{n-1})` and `δ'` the staircase on those `n` letters.  For the empty shape it
is the recursion `a_δ = ∏_{i < n} (x_i - x_n) · a_{δ'}` of the Vandermonde determinant, and the
bialternant formula follows from the two branching rules by induction on the number of variables.

## Main statements

* `TauCeti.injective_staircase`: the staircase exponents are pairwise distinct, so `a_δ` is
  nonzero over a domain and may be cancelled.
* `TauCeti.alternant_eq_prod_mul_sum_interlacingShapes`: the branching rule for the alternants
  `a_{λ+δ}`.
* `TauCeti.diagramSchurPoly_mul_alternant`: **Jacobi's bialternant formula** for Young diagrams.
* `TauCeti.schurPoly_mul_alternant`: the formula for partitions in any finite alphabet.

## Implementation notes

The branching rule for alternants is a determinant computation.  Writing `y = x_n` and
`e_j = λ_j + n - j` for the exponents, subtracting `y ^ (e_j - e_{j+1})` times column `j + 1` from
column `j` for every `j < n` at once (right multiplication by a unitriangular matrix) empties the
last row except for its final entry `y ^ λ_n`.  In the remaining `n × n` block the entry in row `i`
and column `j` is `x_i - y` times the geometric sum
`∑_{λ_{j+1} ≤ m ≤ λ_j} x_i ^ (m + n - 1 - j) · y ^ (λ_j - m)`.  Pulling the factor `x_i - y` out of
each row and expanding the determinant multilinearly in its columns
(`MultilinearMap.map_sum_finset`) gives a sum over families `m_j ∈ [λ_{j+1}, λ_j]`. These are the
row lengths of shapes interlacing `μ` (`YoungDiagram.sum_interlacingShapes_eq_sum_piFinset`).

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 3 (the Schur functions as quotients of alternants) and Section 5 (their tableau
  expansion).
* [W. Fulton, *Young Tableaux*][fulton1997], Chapter 6.
-/

public section

open MvPolynomial Finset

namespace TauCeti

variable {R : Type*} [CommRing R]

/-- **Column reduction of an alternant.**  For weakly decreasing exponents `e` on `n + 1` letters,
subtracting `x_n ^ (e_j - e_{j+1})` times column `j + 1` from column `j`, for every `j < n` at
once, empties the last row of `(x_i ^ e_j)` except for its final entry `x_n ^ e_n`, so the
alternant is that entry times the determinant of the remaining `n × n` block. -/
private theorem alternant_eq_X_last_pow_mul_det {n : ℕ} (e : Fin (n + 1) → ℕ)
    (he : ∀ j : Fin n, e j.succ ≤ e j.castSucc) :
    alternant (Fin (n + 1)) R e = X (Fin.last n) ^ e (Fin.last n) *
      (Matrix.of fun i j : Fin n => (X i.castSucc : MvPolynomial (Fin (n + 1)) R) ^ e j.castSucc -
        X i.castSucc ^ e j.succ * X (Fin.last n) ^ (e j.castSucc - e j.succ)).det := by
  set y : MvPolynomial (Fin (n + 1)) R := X (Fin.last n) with hy
  -- The column operation, as right multiplication by a unitriangular matrix `U`.
  set U : Matrix (Fin (n + 1)) (Fin (n + 1)) (MvPolynomial (Fin (n + 1)) R) :=
    Matrix.of fun k j =>
      (if k = j then 1 else 0) - if (k : ℕ) = j + 1 then y ^ (e j - e k) else 0 with hU
  have hdetU : U.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular U fun k j hkj => ?_]
    · simp [hU]
    · have hkj' : k < j := OrderDual.toDual_lt_toDual.mp hkj
      have h2 : (k : ℕ) ≠ j + 1 := by omega
      simp [hU, hkj'.ne, h2]
  set A : Matrix (Fin (n + 1)) (Fin (n + 1)) (MvPolynomial (Fin (n + 1)) R) :=
    Matrix.of fun i j => X i ^ e j with hA
  have hAU_last : ∀ i, (A * U) i (Fin.last n) = X i ^ e (Fin.last n) := by
    intro i
    rw [Matrix.mul_apply]
    simp only [hU, hA, Matrix.of_apply, mul_sub, sum_sub_distrib, mul_ite, mul_one, mul_zero,
      sum_ite_eq', mem_univ, ite_true]
    rw [sum_eq_zero fun k _ => ite_eq_right (by simp only [Fin.val_last]; omega), sub_zero]
  have hAU_cs : ∀ i (j : Fin n), (A * U) i j.castSucc =
      X i ^ e j.castSucc - X i ^ e j.succ * y ^ (e j.castSucc - e j.succ) := by
    intro i j
    rw [Matrix.mul_apply]
    simp only [hU, hA, Matrix.of_apply, mul_sub, sum_sub_distrib, mul_ite, mul_one, mul_zero,
      sum_ite_eq', mem_univ, ite_true]
    congr 1
    rw [sum_eq_single j.succ (fun k _ hk => ite_eq_right fun h => hk (Fin.ext (by
      simp only [Fin.val_succ, Fin.val_castSucc] at h ⊢; omega))) (fun h => absurd (mem_univ _) h)]
    simp
  have hrow : ∀ j : Fin n, (A * U) (Fin.last n) j.castSucc = 0 := by
    intro j
    rw [hAU_cs, ← pow_add, Nat.add_sub_cancel' (he j), sub_self]
  -- Laplace expansion along the last row of `A * U`.
  rw [alternant_def, ← hA, ← mul_one (Matrix.det _), ← hdetU, ← Matrix.det_mul,
    Matrix.det_succ_row _ (Fin.last n), Fin.sum_univ_castSucc]
  simp only [hrow, mul_zero, zero_mul, sum_const_zero, zero_add, Fin.succAbove_last,
    hAU_last, Fin.val_last, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul, ← hy]
  exact congrArg (y ^ e (Fin.last n) * Matrix.det ·)
    (Matrix.ext fun i j => by rw [Matrix.submatrix_apply, hAU_cs, Matrix.of_apply])

/-- **The branching rule for alternants.**  For a shape `μ` with at most `n + 1` rows, the
alternant `a_{λ+δ}` of its row lengths `λ` shifted by the staircase `δ_j = n - j` on `n + 1`
letters is the Vandermonde factor `∏_{i < n} (x_i - x_n)` times the sum, over the shapes `ν` with
at most `n` rows interlacing `μ`, of `x_n ^ (|μ| - |ν|)` times the alternant `a_{ν+δ'}` in the
first `n` letters, `δ'_j = n - 1 - j`.

This is the alternant counterpart of the branching rule
`TauCeti.diagramSchurPoly_eq_sum_interlacingShapes` for Schur polynomials. -/
theorem alternant_eq_prod_mul_sum_interlacingShapes (n : ℕ) (μ : _root_.YoungDiagram)
    (hμ : μ.colLen 0 ≤ n + 1) :
    alternant (Fin (n + 1)) R (fun j => μ.betaNumber (n + 1) j) =
      (∏ i : Fin n, (X i.castSucc - X (Fin.last n))) *
        ∑ ν ∈ YoungDiagram.interlacingShapes n μ,
          X (Fin.last n) ^ (μ.card - ν.card) *
            rename Fin.castSucc (alternant (Fin n) R fun j => ν.betaNumber n j) := by
  set y : MvPolynomial (Fin (n + 1)) R := X (Fin.last n) with hy
  set e : Fin (n + 1) → ℕ := fun j => μ.betaNumber (n + 1) j with he
  have he_anti : ∀ j : Fin n, e j.succ ≤ e j.castSucc := by
    intro j
    have := μ.rowLen_anti j (j + 1) (Nat.le_succ _)
    simp only [he, YoungDiagram.betaNumber_def, Fin.val_succ, Fin.val_castSucc]
    omega
  -- After column reduction, each entry of the block is `x_i - y` times a geometric sum.
  set N : Matrix (Fin n) (Fin n) (MvPolynomial (Fin (n + 1)) R) := Matrix.of fun i j =>
    ∑ m ∈ Icc (μ.rowLen ((j : ℕ) + 1)) (μ.rowLen j),
      X i.castSucc ^ (m + (n - 1 - j)) * y ^ (μ.rowLen j - m) with hN
  have hblock : (Matrix.of fun i j : Fin n => (X i.castSucc : MvPolynomial (Fin (n + 1)) R) ^
      e j.castSucc - X i.castSucc ^ e j.succ * y ^ (e j.castSucc - e j.succ)) =
      Matrix.of fun i j : Fin n => (X i.castSucc - y) * N i j := by
    refine Matrix.ext fun i j => ?_
    rw [Matrix.of_apply, Matrix.of_apply, hN, Matrix.of_apply]
    set a := μ.rowLen ((j : ℕ) + 1)
    set b := μ.rowLen j
    set c := n - 1 - j
    have hab : a ≤ b := μ.rowLen_anti _ _ (Nat.le_succ _)
    have h1 : e j.castSucc = b + 1 + c := by
      simp only [he, YoungDiagram.betaNumber_def, Fin.val_castSucc]
      omega
    have h2 : e j.succ = a + c := by
      simp only [he, YoungDiagram.betaNumber_def, Fin.val_succ]
      omega
    have h3 : e j.castSucc - e j.succ = b + 1 - a := by rw [h1, h2]; omega
    -- Keep `b + 1` in the bound so the geometric sum matches the interval calculation below.
    have hab1 : a ≤ b + 1 := Nat.le_succ_of_le hab
    have hgeom := (Commute.all (X i.castSucc : MvPolynomial (Fin (n + 1)) R) y).geom_sum₂_Ico_mul
      hab1
    have hsum : ∑ m ∈ Icc a b, (X i.castSucc : MvPolynomial (Fin (n + 1)) R) ^ (m + c) *
        y ^ (b - m) = X i.castSucc ^ c *
          ∑ m ∈ Ico a (b + 1), X i.castSucc ^ m * y ^ (b + 1 - 1 - m) := by
      rw [Finset.Ico_add_one_right_eq_Icc, Finset.mul_sum]
      refine sum_congr rfl fun m _ => ?_
      rw [pow_add, Nat.add_sub_cancel]
      ring
    rw [hsum, h3, h1, h2]
    linear_combination (-(X i.castSucc ^ c : MvPolynomial (Fin (n + 1)) R)) * hgeom
  -- The right-hand side, as a sum over the families of row lengths of the interlacing shapes.
  have hsum : ∑ ν ∈ YoungDiagram.interlacingShapes n μ, y ^ (μ.card - ν.card) *
      rename Fin.castSucc (alternant (Fin n) R fun j => ν.betaNumber n j) =
      ∑ r ∈ Fintype.piFinset fun j : Fin n => Icc (μ.rowLen ((j : ℕ) + 1)) (μ.rowLen j),
        y ^ (μ.card - ∑ j, r j) *
          rename Fin.castSucc (alternant (Fin n) R fun j => r j + (n - 1 - j)) := by
    simp only [YoungDiagram.betaNumber_def]
    rw [← YoungDiagram.sum_interlacingShapes_eq_sum_piFinset hμ]
    refine sum_congr rfl fun ν hν => ?_
    rw [YoungDiagram.card_eq_sum_range_rowLen ν (YoungDiagram.mem_interlacingShapes.mp hν).2,
      ← Fin.sum_univ_eq_sum_range]
  -- Pull the factor `x_i - y` out of each row and expand the block multilinearly in its columns.
  have hdet_sum : (Matrix.of fun i j : Fin n =>
      ∑ m ∈ Icc (μ.rowLen ((j : ℕ) + 1)) (μ.rowLen j),
        X i.castSucc ^ (m + (n - 1 - j)) * y ^ (μ.rowLen j - m)).det =
      ∑ r ∈ Fintype.piFinset (fun j : Fin n =>
        Icc (μ.rowLen ((j : ℕ) + 1)) (μ.rowLen j)),
        (Matrix.of fun i j : Fin n =>
          X i.castSucc ^ (r j + (n - 1 - j)) * y ^ (μ.rowLen j - r j)).det := by
    simp_rw [← Matrix.det_transpose (Matrix.of _), Matrix.det.eq_1]
    have h := (Matrix.detRowAlternating (R := MvPolynomial (Fin (n + 1)) R)
      (n := Fin n)).toMultilinearMap.map_sum_finset
        (fun j (m : ℕ) i => X i.castSucc ^ (m + (n - 1 - j)) * y ^ (μ.rowLen j - m))
        (fun j : Fin n => Icc (μ.rowLen ((j : ℕ) + 1)) (μ.rowLen j))
    simp only [AlternatingMap.coe_multilinearMap] at h
    convert h using 3 with r
    · congr 1
      ext j i
      simp [Finset.sum_apply]
    · rfl
  have hel : e (Fin.last n) = μ.rowLen n := by simp [he, YoungDiagram.betaNumber_def]
  rw [alternant_eq_X_last_pow_mul_det e he_anti, ← hy, hel, hblock, Matrix.det_mul_column, hN,
    hdet_sum, hsum, mul_left_comm, Finset.mul_sum]
  congr 1
  refine sum_congr rfl fun r hr => ?_
  have hr' : ∀ j ∈ univ, r j ≤ μ.rowLen j := fun j _ =>
    (mem_Icc.mp (Fintype.mem_piFinset.mp hr j)).2
  have hdet : (Matrix.of fun i j : Fin n =>
      (X i.castSucc : MvPolynomial (Fin (n + 1)) R) ^ (r j + (n - 1 - j)) *
        y ^ (μ.rowLen j - r j)).det = (∏ j : Fin n, y ^ (μ.rowLen j - r j)) *
          rename Fin.castSucc (alternant (Fin n) R fun j => r j + (n - 1 - j)) := by
    rw [alternant_def, AlgHom.map_det, ← Matrix.det_mul_row]
    congr 1
    ext i j : 1
    simp [mul_comm]
  have hcard : μ.card = ∑ j : Fin n, μ.rowLen j + μ.rowLen n := by
    rw [YoungDiagram.card_eq_sum_range_rowLen μ hμ, sum_range_succ, Fin.sum_univ_eq_sum_range]
  have hle : ∑ j : Fin n, r j ≤ ∑ j : Fin n, μ.rowLen j := sum_le_sum hr'
  rw [hdet, ← mul_assoc, prod_pow_eq_pow_sum, ← pow_add, sum_tsub_distrib _ hr', hcard]
  congr 2
  omega

/-- The staircase exponents `δ_j = N - 1 - j` are pairwise distinct.  Together with
`TauCeti.alternant_ne_zero_of_injective` this is what makes the Vandermonde alternant `a_δ`
nonzero, and so cancellable, over a domain. -/
theorem injective_staircase (N : ℕ) : Function.Injective fun j : Fin N => N - 1 - (j : ℕ) :=
  fun i j hij => by
    have := i.isLt
    have := j.isLt
    exact Fin.ext (by simp only at hij; omega)

/-- **Jacobi's bialternant formula.**  For a Young diagram `μ` with at most `N` rows, the Schur
polynomial `s_μ` in the alphabet `Fin N` times the Vandermonde alternant `a_δ`, `δ_j = N - 1 - j`,
is the alternant `a_{λ+δ}` of the row lengths `λ_j = μ.rowLen j` shifted by the staircase:
`s_μ · a_δ = a_{λ+δ}`.  This is the division-free form of `s_μ = a_{λ+δ} / a_δ`.

The row bound is necessary: for a taller shape `s_μ` vanishes, while the right-hand side, which
only sees the first `N` rows, need not. -/
theorem diagramSchurPoly_mul_alternant (N : ℕ) (μ : _root_.YoungDiagram) (hμ : μ.colLen 0 ≤ N) :
    diagramSchurPoly N R μ * alternant (Fin N) R (fun j => N - 1 - j) =
      alternant (Fin N) R fun j => μ.betaNumber N j := by
  have hbot : ∀ i, (⊥ : _root_.YoungDiagram).rowLen i = 0 := fun i =>
    Nat.eq_zero_of_not_pos fun h =>
      _root_.YoungDiagram.notMem_bot _ (_root_.YoungDiagram.mem_iff_lt_rowLen.mpr h)
  have hbotc : (⊥ : _root_.YoungDiagram).colLen 0 = 0 :=
    Nat.eq_zero_of_not_pos fun h =>
      _root_.YoungDiagram.notMem_bot _ (_root_.YoungDiagram.mem_iff_lt_colLen.mpr h)
  induction N generalizing μ with
  | zero =>
    have hμ0 : μ = ⊥ := YoungDiagram.rowLen_injective (funext fun i => by
      rw [YoungDiagram.rowLen_eq_zero_of_colLen_le (hμ.trans (Nat.zero_le i)), hbot])
    subst hμ0
    simp [diagramSchurPoly_bot, alternant_def, YoungDiagram.betaNumber_def]
  | succ n ih =>
    -- The Vandermonde recursion: the branching rule for the alternant of the empty shape.
    have hvan : alternant (Fin (n + 1)) R (fun j => n - j) =
        (∏ i : Fin n, (X i.castSucc - X (Fin.last n))) *
          rename Fin.castSucc (alternant (Fin n) R fun j => n - 1 - j) := by
      have hshapes : YoungDiagram.interlacingShapes n ⊥ = {⊥} := by
        ext ν
        simp only [YoungDiagram.mem_interlacingShapes, mem_singleton]
        refine ⟨fun h => le_bot_iff.mp h.1.le, ?_⟩
        rintro rfl
        exact ⟨YoungDiagram.interlacedBy_iff.mpr fun i => by simp [hbot], by simp [hbotc]⟩
      simpa [hshapes, hbot, YoungDiagram.betaNumber_def] using
        alternant_eq_prod_mul_sum_interlacingShapes (R := R) n ⊥ (by simp [hbotc])
    simp only [Nat.add_sub_cancel]
    rw [diagramSchurPoly_eq_sum_interlacingShapes, hvan,
      alternant_eq_prod_mul_sum_interlacingShapes n μ hμ, sum_mul, mul_sum]
    refine sum_congr rfl fun ν hν => ?_
    rw [← ih ν (YoungDiagram.mem_interlacingShapes.mp hν).2, map_mul]
    ring

/-- **Jacobi's bialternant formula for partitions.** In a finite alphabet `σ`, ordered by
`Fintype.equivFin σ`, the Schur polynomial of `μ` times the renamed staircase alternant equals
the renamed alternant of the beta-numbers of its Young diagram. -/
theorem schurPoly_mul_alternant {σ : Type*} [Fintype σ] {n : ℕ} (μ : n.Partition)
    (hμ : (YoungDiagram.ofPartition μ).colLen 0 ≤ Fintype.card σ) :
    schurPoly σ R μ *
        rename (Fintype.equivFin σ).symm
          (alternant (Fin (Fintype.card σ)) R (fun j => Fintype.card σ - 1 - j)) =
      rename (Fintype.equivFin σ).symm
        (alternant (Fin (Fintype.card σ)) R
          (fun j => (YoungDiagram.ofPartition μ).betaNumber (Fintype.card σ) j)) := by
  rw [schurPoly_eq_rename, ← map_mul,
    diagramSchurPoly_mul_alternant (Fintype.card σ) (YoungDiagram.ofPartition μ) hμ]

end TauCeti
end
end TAF_LiteralSource_0646

section TAF_LiteralSource_0647
/- Original module: TauCeti.Algebra.MvPolynomial.Monomial -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Monomials in multivariate polynomial rings

Multiplying together a multiset of variables, one factor per element, gives the monomial whose
exponent vector is the multiplicity function of the multiset: `TauCeti.prod_map_X_eq_monomial`.
Mathlib's `MvPolynomial.prod_X_pow_eq_monomial` says the same thing for a product indexed by the
support of an exponent vector; this is the multiset-indexed form, which is how the monomials of
`MvPolynomial.hsymm` and `MvPolynomial.msymm` are written.

The file also computes Mathlib's embedding `Polynomial.toMvPolynomial i`, which places a
univariate polynomial in the variable `Xᵢ`, on monomials.

## Main results

* `TauCeti.prod_map_X_eq_monomial`: the product of a multiset of variables is the monomial with
  coefficient `1` at the multiplicity function of the multiset.
* `MvPolynomial.coeff_prod_univ_X_pow`: the coefficients of the monomial `∏ᵢ Xᵢ ^ Lᵢ` in finitely
  many variables.
* `MvPolynomial.coeff_prod_X_pow_mul_prod_X_pow`: the coefficients of a product `Xᵃ Yᵇ` of
  monomials in two disjoint groups of variables.
* `MvPolynomial.eval₂_monomial_sumElim_of_eq_one`: evaluating `c X^a Y^e` with every `X`
  variable set to `1` gives the value of `c Y^e`.
* `Polynomial.toMvPolynomial_monomial`: a univariate monomial placed in `Xᵢ` is the multivariate
  monomial with exponent `n eᵢ`.
-/

public section

namespace TauCeti

open MvPolynomial

/-- **A monomial is the product of the variables it uses, with multiplicity.**  This is the form
in which the monomials of `MvPolynomial.hsymm` and `MvPolynomial.msymm` are written. -/
theorem prod_map_X_eq_monomial {σ : Type*} [DecidableEq σ] {R : Type*} [CommSemiring R]
    (s : Multiset σ) :
    (s.map (X : σ → MvPolynomial σ R)).prod = monomial s.toFinsupp (1 : R) := by
  rw [Finset.prod_multiset_map_count, ← prod_X_pow_eq_monomial, Multiset.toFinsupp_support]
  exact Finset.prod_congr rfl fun a _ => by rw [Multiset.toFinsupp_apply]

end TauCeti

namespace MvPolynomial

variable {ι A : Type*} [CommSemiring A]

/-- The coefficient of `Xᴷ` in the monomial `∏ᵢ Xᵢ ^ Lᵢ` in finitely many variables is `1` when
the exponents agree and `0` otherwise. -/
theorem coeff_prod_univ_X_pow [Fintype ι] (L : ι → ℕ) (K : ι →₀ ℕ) :
    (∏ i, (X i : MvPolynomial ι A) ^ L i).coeff K = if ∀ i, L i = K i then 1 else 0 := by
  classical
  simp [coeff_prod_X_pow, Finsupp.ext_iff, eq_comm]

/-- The coefficient of `Xᵉ` in the product `Xᵃ Yᵇ` of monomials in two disjoint groups of
finitely many variables `Xᵢ = X (inl i)` and `Yⱼ = X (inr j)` is `1` when `a` and `b` are the
restrictions of `e` and `0` otherwise. -/
theorem coeff_prod_X_pow_mul_prod_X_pow {κ : Type*} [Fintype ι] [Fintype κ] (a : ι → ℕ)
    (b : κ → ℕ) (e : ι ⊕ κ →₀ ℕ) :
    ((∏ i, (X (Sum.inl i) : MvPolynomial (ι ⊕ κ) A) ^ a i) *
        ∏ j, (X (Sum.inr j) : MvPolynomial (ι ⊕ κ) A) ^ b j).coeff e =
      if (∀ i, a i = e (Sum.inl i)) ∧ ∀ j, b j = e (Sum.inr j) then 1 else 0 := by
  have h := Fintype.prod_sum_type (fun k ↦ (X k : MvPolynomial (ι ⊕ κ) A) ^ Sum.elim a b k)
  simp only [Sum.elim_inl, Sum.elim_inr] at h
  rw [← h, coeff_prod_univ_X_pow]
  simp [Sum.forall]

/-- Evaluating the monomial `c X^a Y^e` in the variables `τ ⊕ σ` at a point whose `.inl`
coordinates are all `1` gives the value of `c Y^e` at the `.inr` coordinates. -/
theorem eval₂_monomial_sumElim_of_eq_one {σ τ R T : Type*} [CommSemiring R] [CommSemiring T]
    (φ : R →+* T) (x : τ ⊕ σ → T) (hx : ∀ h, x (.inl h) = 1) (a : τ →₀ ℕ) (e : σ →₀ ℕ)
    (c : R) :
    eval₂ φ x (monomial (a.sumElim e) c) = eval₂ φ (x ∘ Sum.inr) (monomial e c) := by
  simp [eval₂_monomial, Finsupp.prod_sumElim, Function.comp_def, hx]

end MvPolynomial

namespace Polynomial

/-- A univariate monomial placed in the variable `Xᵢ` is the monomial with exponent `n eᵢ`. -/
@[simp]
theorem toMvPolynomial_monomial {R σ : Type*} [CommSemiring R] (i : σ) (n : ℕ) (a : R) :
    (monomial n a).toMvPolynomial i = MvPolynomial.monomial (Finsupp.single i n) a := by
  simp [toMvPolynomial, MvPolynomial.X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial,
    MvPolynomial.C_mul_monomial]

end Polynomial
end
end TAF_LiteralSource_0647

