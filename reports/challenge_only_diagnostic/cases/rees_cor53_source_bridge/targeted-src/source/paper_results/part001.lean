module
public import graph_foundation.part010
public import shared_results.part001
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.List.Lemmas
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.DirectSum.Algebra
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Group.Commute.Basic
public import Mathlib.Algebra.Group.Commute.Units
public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
public import Mathlib.Algebra.Group.Units.Basic
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.Algebra.MvPolynomial.Supported
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Rearrangement
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Algebra.Polynomial.Module.Basic
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.CategoryTheory.Abelian.Projective.Ext
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Data.Fin.Fin2
public import Mathlib.Data.Fin.Rev
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Sum
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.MonomialOrder.DegLex
public import Mathlib.Data.Finsupp.Order
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Sort
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.List.Chain
public import Mathlib.Data.List.Dedup
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Sym.Card
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.DirectSum.Basis
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import Mathlib.LinearAlgebra.ExteriorPower.WedgePairing
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.LinearAlgebra.TensorProduct.Lift
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Logic.Equiv.Set
public import Mathlib.Logic.Function.Basic
public import Mathlib.Order.Birkhoff
public import Mathlib.Order.Int.ConditionallyCompleteOrder
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.MinMax
public import Mathlib.Order.Preorder.Chain
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.Order.RelIso.Basic
public import Mathlib.Order.Sum.Order
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.Depth.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Ideal.HasGoingUp
public import Mathlib.RingTheory.Ideal.IsPrimary
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.RingTheory.PowerSeries.WellKnown
public import Mathlib.RingTheory.Regular.IsSMulRegular
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.Tactic.NthRewrite
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.PositiveLabelGrouping -/
section

/-! # Regrouping a finite sum by a positive integer label -/

section
set_option autoImplicit false

namespace FourPapers.FinitePositiveGrouping
open scoped BigOperators

/-- Group every summand by its positive label. No ordering or positivity
assumption on the coefficients is needed: the identity holds in any semiring. -/
theorem sum_grouped_by_positive_label {ι R : Type*} [Fintype ι] [Semiring R]
    (c : ι → R) (r : ι → ℕ) (N : ℕ) (hr : ∀ a, 1 ≤ r a ∧ r a ≤ N)
    (w : ℕ → R) :
    ∑ a, c a * w (r a) =
      ∑ j ∈ Finset.Icc 1 N,
        (∑ a ∈ Finset.univ.filter (fun a => r a = j), c a) * w j := by
  classical
  symm
  calc
    (∑ j ∈ Finset.Icc 1 N,
        (∑ a ∈ Finset.univ.filter (fun a => r a = j), c a) * w j) =
        ∑ j ∈ Finset.Icc 1 N, ∑ a, if r a = j then c a * w j else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul, Finset.sum_filter]
    _ = ∑ a, ∑ j ∈ Finset.Icc 1 N, if r a = j then c a * w j else 0 :=
      Finset.sum_comm
    _ = ∑ a, c a * w (r a) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_eq_single (r a)]
      · simp only [ite_true]
      · intro j _ hj
        exact if_neg (Ne.symm hj)
      · intro hnot
        exact (hnot (Finset.mem_Icc.mpr (hr a))).elim

end FourPapers.FinitePositiveGrouping

end
end

/- BEGIN EXACT BODY: FourPapers.Common.PositiveMultiplicitySeries -/
section

/-! # The generating series of positive multiplicities

`positiveMultiplicitySeries R r` is the literal formal series
`z^r / (1-z)^r`. Its coefficient counts assignments of positive
multiplicities to an ordered support of cardinality `r`.
-/

section
set_option autoImplicit false
noncomputable section
namespace FourPapers.PositiveMultiplicitySeries
open PowerSeries
variable (R : Type*) [CommRing R]

def series (r : ℕ) : PowerSeries R :=
  X^r * (invOneSubPow R r).val

theorem coefficient (r : ℕ) (hr : 0 < r) (m : ℕ) :
    coeff m (series R r) = if m = 0 then 0 else ((m-1).choose (r-1) : R) := by
  rw [series, coeff_X_pow_mul']
  by_cases h : r ≤ m
  · rw [if_pos h, invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos R r hr,
      coeff_mk, if_neg (by omega : m ≠ 0)]
    rw [show r-1+(m-r) = m-1 by omega]
  · rw [if_neg h]
    by_cases hm : m = 0
    · rw [if_pos hm]
    · rw [if_neg hm, Nat.choose_eq_zero_of_lt (by omega : m-1 < r-1), Nat.cast_zero]

/-- The denominator in the notation is an actual inverse unit. -/
theorem denominator_identity (r : ℕ) :
    series R r * (1-X)^r = X^r := by
  rw [series, mul_assoc, ← invOneSubPow_inv_eq_one_sub_pow R r,
    Units.val_inv, mul_one]

variable {R} {I : Type*} [Fintype I]

/-- A finite positive-binomial expansion is exactly a rational formal series. -/
theorem finite_sum (c : I → R) (r : I → ℕ) (hr : ∀ i, 0 < r i) :
    PowerSeries.mk (fun m => if m = 0 then 0 else
      ∑ i, ((m-1).choose (r i-1) : R) * c i) =
      ∑ i, series R (r i) * PowerSeries.C (c i) := by
  ext m
  simp only [PowerSeries.coeff_mk, map_sum, PowerSeries.coeff_mul_C,
    coefficient R _ (hr _)]
  by_cases hm : m = 0 <;>
    simp only [hm, if_pos, if_neg, if_false, zero_mul, Finset.sum_const_zero]

end FourPapers.PositiveMultiplicitySeries

#print axioms FourPapers.PositiveMultiplicitySeries.coefficient

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.KoszulExteriorDuality -/
section

/-! # Complementary-degree duality of the actual coefficient Koszul maps

Mathlib's perfect wedge pairing gives the degreewise equivalence. The
differential identity is proved by contracting a product of exterior
degree one above the rank, where it is genuinely zero. Thus all signs
come from the existing contraction Leibniz rule and no characteristic
restriction is imposed.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.KoszulExteriorDuality
open Classical CategoryTheory CommAlg CommAlg.Koszul Module
open scoped TensorProduct
universe u
variable {R V : Type u} [CommRing R] [Nontrivial R] [Fintype V] [LinearOrder V]

abbrev Free := V → R
abbrev Exterior := ExteriorAlgebra R (Free (R := R) (V := V))
abbrev Power (p : ℕ) := ⋀[R]^p (Free (R := R) (V := V))

/-- A genuine trivialization of the top exterior power. Its normalization
is irrelevant to the duality and can change only an invertible scalar. -/
def coordinateVolume : Power (R := R) (V := V) (Module.finrank R (V → R)) ≃ₗ[R] R := by
  let b := Pi.basisFun R V
  letI : Unique (Set.powersetCard V (Module.finrank R (V → R))) :=
    { default := ⟨Finset.univ, by simp [Module.finrank_eq_card_basis b]⟩
      uniq := fun s => Subtype.ext (Finset.eq_univ_of_card _
        (by simpa only [Module.finrank_eq_card_basis b] using
          (Set.powersetCard.mem_iff.mp s.property))) }
  exact (b.exteriorPower (Module.finrank R (V → R))).equivFun.trans
    (LinearEquiv.funUnique _ R R)

variable (vol : Power (R := R) (V := V) (Module.finrank R (V → R)) ≃ₗ[R] R)

private lemma exterior_cast_apply {a b : ℕ} (h : a = b)
    (f : Power (R := R) (V := V) b →ₗ[R] R)
    (x : Power (R := R) (V := V) a) (y : Power (R := R) (V := V) b)
    (hxy : x.val = y.val) : (h ▸ f) x = f y := by
  subst b
  exact congrArg f (Subtype.ext hxy)

lemma wedgePairing_apply {p q : ℕ} (h : q+p = Module.finrank R (V → R))
    (w : Power (R := R) (V := V) q) (v : Power (R := R) (V := V) p) :
    exteriorPower.wedgePairing vol h w v =
      vol ⟨w.val*v.val, by
        rw [← h]
        exact SetLike.mul_mem_graded w.property v.property⟩ := by
  unfold exteriorPower.wedgePairing
  rw [LinearMap.compr₂_apply]
  exact exterior_cast_apply (R := R) (V := V) h vol.toLinearMap _ _ rfl

/-- The exact scalar adjoint identity for contraction. -/
theorem wedgePairing_differential (x : V → R) (p q : ℕ)
    (h : (q+1)+p = Module.finrank R (V → R))
    (w : Power (R := R) (V := V) (q+1)) (v : Power (R := R) (V := V) (p+1)) :
    exteriorPower.wedgePairing vol (show q+(p+1) = Module.finrank R (V → R) by omega)
      (koszulComplex.d (Fintype.linearCombination R x) q w) v =
      (-1 : R)^q * exteriorPower.wedgePairing vol h w
        (koszulComplex.d (Fintype.linearCombination R x) p v) := by
  let φ := Fintype.linearCombination R x
  have hqp : q+(p+1) = Module.finrank R (V → R) := by omega
  have hzero : (w.val*v.val : Exterior (R := R) (V := V)) = 0 :=
    ZeroMemClass.coe_eq_zero.mpr
      (exteriorPower.eq_zero_of_finrank_lt (R := R) (M := V → R)
        ((q+1)+(p+1)) (by omega)
        ⟨_, SetLike.mul_mem_graded w.property v.property⟩)
  have hc := congrArg (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R (V → R))) φ) hzero
  rw [CliffordAlgebra.contractLeft_mul,
    TauCeti.ExteriorAlgebra.involute_of_mem_exteriorPower w.property,
    smul_mul_assoc, map_zero] at hc
  let a : Power (R := R) (V := V) (Module.finrank R (V → R)) :=
    ⟨(koszulComplex.d φ q w).val*v.val, by
      rw [← hqp]
      exact SetLike.mul_mem_graded (koszulComplex.d φ q w).property v.property⟩
  let b : Power (R := R) (V := V) (Module.finrank R (V → R)) :=
    ⟨w.val*(koszulComplex.d φ p v).val, by
      rw [← h]
      exact SetLike.mul_mem_graded w.property (koszulComplex.d φ p v).property⟩
  have htop : a + (-1 : R)^(q+1) • b = 0 := by
    apply Subtype.ext
    simpa only [a, b, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_zero,
      differential_eq_contraction, TauCeti.coe_koszulDifferential_apply] using hc
  have hs := congrArg vol htop
  simp only [map_add, map_smul, map_zero, smul_eq_mul, pow_succ, mul_neg_one,
    neg_mul, ← sub_eq_add_neg] at hs
  rw [wedgePairing_apply, wedgePairing_apply]
  exact sub_eq_zero.mp hs

variable (M : ModuleCat.{u} R)

/-- Tensoring the perfect pairing gives the actual coefficient-module
duality. No projectivity of M is required. -/
def coefficientDuality (p q : ℕ) (h : q+p = Module.finrank R (V → R)) :
    (Power (R := R) (V := V) q ⊗[R] M) ≃ₗ[R]
      (Power (R := R) (V := V) p →ₗ[R] M) :=
  (TensorProduct.congr (exteriorPower.wedgePairing vol h).toPerfPair
    (LinearEquiv.refl R M)).trans (dualTensorHomEquiv R _ M)

@[simp] theorem coefficientDuality_tmul (p q : ℕ)
    (h : q+p = Module.finrank R (V → R))
    (w : Power (R := R) (V := V) q) (m : M) (v : Power (R := R) (V := V) p) :
    coefficientDuality vol M p q h (w ⊗ₜ[R] m) v =
      exteriorPower.wedgePairing vol h w v • m := by
  simp only [coefficientDuality, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    LinearEquiv.refl_apply, dualTensorHomEquiv_tmul, LinearMap.toPerfPair_apply]

/-- The genuine coefficient differential is dual to precomposition with
the genuine exterior differential, up to the displayed invertible sign. -/
theorem coefficientDuality_differential (x : V → R) (p q : ℕ)
    (h : (q+1)+p = Module.finrank R (V → R))
    (z : (familyCoefficientComplex x M).X (q+1)) :
    coefficientDuality vol M (p+1) q (by omega)
        (((familyCoefficientComplex x M).d (q+1) q).hom z) =
      (-1 : R)^q • (coefficientDuality vol M p (q+1) h z).comp
        (koszulComplex.d (Fintype.linearCombination R x) p) := by
  induction z using TensorProduct.induction_on with
  | zero =>
      have hz : ((familyCoefficientComplex x M).d (q+1) q).hom
          (0 : (familyCoefficientComplex x M).X (q+1)) = 0 :=
        ((familyCoefficientComplex x M).d (q+1) q).hom.map_zero
      rw [hz]
      simp only [map_zero, LinearMap.zero_comp, smul_zero]
  | add a b ha hb => simp only [map_add, ha, hb, LinearMap.add_comp, smul_add]
  | tmul w m =>
      apply LinearMap.ext
      intro v
      rw [family_d_tmul, coefficientDuality_tmul,
        LinearMap.smul_apply, LinearMap.comp_apply, coefficientDuality_tmul,
        wedgePairing_differential]
      exact mul_smul _ _ _

end FourPapers.KoszulExteriorDuality
end

end
end

/- BEGIN EXACT BODY: FourPapers.Common.ProjectiveExtCohomology -/
section

/-! # Genuine Ext as the literal Hom-complex cycle/boundary quotient

This comparison uses Mathlib's projective-resolution constructors for Ext.
The degree-zero incoming map is zero, and its kernel statement is proved
from the extension of a projective resolution by zero in positive cochain
degrees. No Ext or exactness assertion is postulated.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.ProjectiveExtCohomology
open Classical CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open CochainComplex HomComplex FourPapers.FilteredHomology
universe u
variable {R : Type u} [CommRing R]
variable {X : ModuleCat.{u} R} (P : ProjectiveResolution X) (M : ModuleCat.{u} R)

def differential (p : ℕ) : (P.complex.X p →ₗ[R] M) →ₗ[R] (P.complex.X (p+1) →ₗ[R] M) :=
  LinearMap.lcomp R M (P.complex.d (p+1) p).hom

def incoming : (p : ℕ) → (P.complex.X p.pred →ₗ[R] M) →ₗ[R] (P.complex.X p →ₗ[R] M)
  | 0 => 0
  | p+1 => differential P M p

theorem differential_comp (p : ℕ) : (differential P M p).comp (incoming P M p) = 0 := by
  cases p with
  | zero => simp only [incoming, LinearMap.comp_zero]
  | succ p =>
      ext f x
      change f ((P.complex.d (p+1) p).hom ((P.complex.d (p+2) (p+1)).hom x)) = 0
      have he := congrArg (fun t => t.hom x) (P.complex.d_comp_d (p+2) (p+1) p)
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
        LinearMap.zero_apply, map_zero] using congrArg f he

abbrev Cohomology (p : ℕ) :=
  Homology (incoming P M p) (differential P M p) (differential_comp P M p)

/-- The missing degree-zero case of the ordinary projective-resolution
boundary criterion: there is no incoming negative chain degree. -/
theorem extMk_zero_eq_zero_iff (f : P.complex.X 0 ⟶ M)
    (hf : P.complex.d 1 0 ≫ f = 0) : P.extMk f 1 rfl hf = 0 ↔ f = 0 := by
  rw [← P.extEquivCohomologyClass.apply_eq_iff_eq,
    P.extEquivCohomologyClass_extMk, P.extEquivCohomologyClass_zero,
    CohomologyClass.mk_eq_zero_iff]
  rw [Cocycle.toSingleMk_mem_coboundaries_iff _ _ _ _ _ 1 (by norm_num)]
  constructor
  · rintro ⟨g, hg⟩
    have hz : IsZero (P.cochainComplex.X 1) :=
      CochainComplex.isZero_of_isStrictlyLE P.cochainComplex 0 1 (by norm_num)
    rw [hz.eq_zero_of_src g, comp_zero] at hg
    apply (cancel_epi (P.cochainComplexXIso (-((0 : ℕ) : ℤ)) 0 rfl).hom).mp
    simpa only [comp_zero] using hg.symm
  · intro hf0
    subst f
    exact ⟨0, by simp⟩

def cycleClass (p : ℕ) : LinearMap.ker (differential P M p) →ₗ[R] Ext X M p where
  toFun f := P.extMk (ModuleCat.ofHom f.val) (p+1) rfl
    (ModuleCat.hom_ext f.property)
  map_add' f g := by
    exact (P.add_extMk (ModuleCat.ofHom f.val) (ModuleCat.ofHom g.val) (p+1) rfl _ _).symm
  map_smul' r f := by
    exact (P.smul_extMk r (ModuleCat.ofHom f.val) (p+1) rfl _).symm

theorem cycleClass_surjective (p : ℕ) : Function.Surjective (cycleClass P M p) := by
  intro z
  obtain ⟨f, hf, he⟩ := P.extMk_surjective z (p+1) rfl
  refine ⟨⟨f.hom, ?_⟩, he⟩
  change differential P M p f.hom = 0
  simpa only [differential, LinearMap.lcomp_apply', ModuleCat.hom_comp,
    ModuleCat.hom_zero] using congrArg ModuleCat.Hom.hom hf

theorem cycleClass_kernel (p : ℕ) :
    LinearMap.ker (cycleClass P M p) =
      LinearMap.range (boundaryMap (incoming P M p) (differential P M p)
        (differential_comp P M p)) := by
  ext f
  change P.extMk (ModuleCat.ofHom f.val) (p+1) rfl
    (ModuleCat.hom_ext f.property) = 0 ↔ _
  cases p with
  | zero =>
      rw [extMk_zero_eq_zero_iff]
      constructor
      · intro hf
        refine ⟨0, ?_⟩
        apply Subtype.ext
        exact (congrArg ModuleCat.Hom.hom hf).symm
      · rintro ⟨g, hg⟩
        apply ModuleCat.hom_ext
        have he := congrArg Subtype.val hg
        change (0 : P.complex.X 0 →ₗ[R] M) = f.val at he
        exact he.symm
  | succ p =>
      rw [P.extMk_eq_zero_iff _ _ rfl _ p rfl]
      constructor
      · rintro ⟨g, hg⟩
        refine ⟨g.hom, ?_⟩
        apply Subtype.ext
        exact congrArg ModuleCat.Hom.hom hg
      · rintro ⟨g, hg⟩
        refine ⟨ModuleCat.ofHom g, ?_⟩
        apply ModuleCat.hom_ext
        exact congrArg Subtype.val hg

/-- The cohomology quotient is genuinely equivalent to the derived Ext
group, including degree zero. -/
def cohomologyExtEquiv (p : ℕ) : Cohomology P M p ≃ₗ[R] Ext X M p :=
  (Submodule.quotEquivOfEq _ _ (cycleClass_kernel P M p).symm).trans
    ((cycleClass P M p).quotKerEquivOfSurjective (cycleClass_surjective P M p))

end FourPapers.ProjectiveExtCohomology
end

end
end

/- BEGIN EXACT BODY: FourPapers.Common.FiniteDistributiveChains -/
section

/-!
# Finite distributive lattices: the exact height and a saturated chain

The height is the number of join-irreducibles.  The chain is obtained by
taking the initial lower sets of a linear extension of those irreducibles
and applying the inverse of Mathlib's Birkhoff representation.  No grading
or maximal-chain assertion is supplied as a hypothesis.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.FiniteDistributive
open Classical Finset

variable (L : Type*) [Fintype L] [DistribLattice L] [OrderBot L]

abbrev Irreducible := {a : L // SupIrred a}

def height : ℕ := Fintype.card (Irreducible L)

def ideal (a : L) : Finset (Irreducible L) :=
  OrderEmbedding.birkhoffFinset a

lemma ideal_strictMono : StrictMono (ideal L) :=
  (OrderEmbedding.birkhoffFinset (α := L)).strictMono

@[simp] lemma ideal_bot : ideal L ⊥ = ∅ := by
  apply Finset.coe_injective
  rw [Finset.coe_empty]
  simp only [ideal, OrderEmbedding.coe_birkhoffFinset,
    OrderEmbedding.birkhoffSet_apply, OrderIso.map_bot, LowerSet.coe_bot]

def rank (a : L) : ℕ := (ideal L a).card

lemma rank_strictMono : StrictMono (rank L) := by
  intro a b hab
  exact Finset.card_lt_card (ideal_strictMono L hab)

lemma rank_le_height (a : L) : rank L a ≤ height L :=
  Finset.card_le_univ _

@[simp] lemma rank_bot : rank L ⊥ = 0 := by simp [rank]

lemma rank_pos {a : L} (ha : a ≠ ⊥) : 0 < rank L a := by
  simpa only [rank_bot] using rank_strictMono L (bot_lt_iff_ne_bot.mpr ha)

/-- A chain which omits the bottom has at most one member at each of the
positive ranks `1,…,height L`. -/
theorem chain_card_le_height (s : Finset L)
    (hs : (s : Set L).Pairwise (fun a b => a ≤ b ∨ b ≤ a))
    (hbot : (⊥ : L) ∉ s) : s.card ≤ height L := by
  have hinj : Set.InjOn (rank L) (s : Set L) := by
    intro a ha b hb he
    by_contra hab
    rcases hs ha hb hab with hab' | hba'
    · exact (ne_of_lt (rank_strictMono L (lt_of_le_of_ne hab' hab))) he
    · exact (ne_of_gt (rank_strictMono L (lt_of_le_of_ne hba' (Ne.symm hab)))) he
  have hsub : s.image (rank L) ⊆ Finset.Icc 1 (height L) := by
    intro r hr
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hr
    exact Finset.mem_Icc.mpr ⟨rank_pos L (fun he => hbot (he ▸ ha)),
      rank_le_height L a⟩
  have hc := Finset.card_le_card hsub
  rwa [Finset.card_image_of_injOn hinj, Nat.card_Icc, Nat.add_sub_cancel] at hc

local instance irreducibleExtensionFintype : Fintype (LinearExtension (Irreducible L)) :=
  inferInstanceAs (Fintype (Irreducible L))

/-- The linear extension is used only to order the construction, not to
replace the original partial order on the irreducibles. -/
def enumeration : Fin (height L) ≃ Irreducible L :=
  (monoEquivOfFin (LinearExtension (Irreducible L)) rfl).toEquiv

def position : Irreducible L → Fin (height L) := (enumeration L).symm

lemma position_monotone : Monotone (position L) := by
  intro a b hab
  exact (monoEquivOfFin (LinearExtension (Irreducible L)) rfl).symm.monotone
    (toLinearExtension.monotone hab)

@[simp] lemma position_enumeration (i : Fin (height L)) :
    position L (enumeration L i) = i := (enumeration L).symm_apply_apply i

def initialIdeal (j : Fin (height L + 1)) : LowerSet (Irreducible L) where
  carrier := {a | (position L a).val < j.val}
  lower' := by
    intro a b hba ha
    change (position L b).val < j.val
    change (position L a).val < j.val at ha
    exact lt_of_le_of_lt (show (position L b).val ≤ (position L a).val from
      position_monotone L hba) ha

@[simp] lemma mem_initialIdeal (j : Fin (height L + 1)) (a : Irreducible L) :
    a ∈ initialIdeal L j ↔ (position L a).val < j.val := Iff.rfl

lemma initialIdeal_monotone : Monotone (initialIdeal L) := by
  intro i j hij a ha
  change (position L a).val < j.val
  change (position L a).val < i.val at ha
  exact lt_of_lt_of_le ha (show i.val ≤ j.val from hij)

@[simp] lemma initialIdeal_zero : initialIdeal L 0 = ⊥ := by
  apply SetLike.coe_injective
  change {a : Irreducible L | (position L a).val < 0} = ∅
  ext a
  exact iff_false_intro (Nat.not_lt_zero _)

@[simp] lemma initialIdeal_last : initialIdeal L (Fin.last (height L)) = ⊤ := by
  apply SetLike.coe_injective
  change {a : Irreducible L | (position L a).val < height L} = Set.univ
  ext a
  exact iff_true_intro (position L a).isLt

lemma initialIdeal_strictMono : StrictMono (initialIdeal L) := by
  intro i j hij
  apply lt_of_le_of_ne (initialIdeal_monotone L hij.le)
  intro he
  let p : Irreducible L := enumeration L ⟨i.val, by omega⟩
  have hp : p ∈ initialIdeal L j := by
    change (position L p).val < j.val
    simpa only [p, position_enumeration] using (show i.val < j.val from hij)
  have hp' : p ∉ initialIdeal L i := by simp [p]
  exact hp' (he.symm ▸ hp)

lemma initialIdeal_covBy (i : Fin (height L)) :
    initialIdeal L i.castSucc ⋖ initialIdeal L i.succ := by
  apply covBy_of_eq_or_eq (initialIdeal_strictMono L (by simp))
  intro J hleft hright
  by_cases hp : enumeration L i ∈ J
  · right
    apply le_antisymm hright
    intro p hp'
    have hpi : (position L p).val ≤ i.val := Nat.lt_succ_iff.mp hp'
    rcases lt_or_eq_of_le hpi with hlt | he
    · exact hleft hlt
    · have hpeq : p = enumeration L i := by
        apply (enumeration L).symm.injective
        change position L p = position L (enumeration L i)
        rw [position_enumeration]
        exact Fin.ext he
      exact hpeq.symm ▸ hp
  · left
    apply le_antisymm _ hleft
    intro p hp'
    have hpi : (position L p).val ≤ i.val := Nat.lt_succ_iff.mp (hright hp')
    apply lt_of_le_of_ne hpi
    intro he
    have hpeq : p = enumeration L i := by
      apply (enumeration L).symm.injective
      change position L p = position L (enumeration L i)
      rw [position_enumeration]
      exact Fin.ext he
    exact hp (hpeq ▸ hp')

def maximalChain (j : Fin (height L + 1)) : L :=
  OrderIso.lowerSetSupIrred.symm (initialIdeal L j)

lemma maximalChain_strictMono : StrictMono (maximalChain L) :=
  OrderIso.lowerSetSupIrred.symm.strictMono.comp (initialIdeal_strictMono L)

lemma maximalChain_monotone : Monotone (maximalChain L) :=
  (maximalChain_strictMono L).monotone

@[simp] lemma maximalChain_zero : maximalChain L 0 = ⊥ := by
  simp [maximalChain]

lemma maximalChain_covBy (i : Fin (height L)) :
    maximalChain L i.castSucc ⋖ maximalChain L i.succ := by
  apply CovBy.of_image (OrderIso.lowerSetSupIrred (α := L)).toOrderEmbedding
  change OrderIso.lowerSetSupIrred
      (OrderIso.lowerSetSupIrred.symm (initialIdeal L i.castSucc)) ⋖
    OrderIso.lowerSetSupIrred
      (OrderIso.lowerSetSupIrred.symm (initialIdeal L i.succ))
  simpa only [OrderIso.apply_symm_apply] using initialIdeal_covBy L i

end FourPapers.FiniteDistributive
end

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.FiniteLatticeBirkhoff -/
section

section
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FourPapers.Sublattice
open Classical
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

def finiteBundledSublattice (hE : finiteLatticeClosed n E) :
    Sublattice (FiniteTuple n) where
  carrier := E
  supClosed' := fun a ha b hb => hE.2 a ha b hb
  infClosed' := fun a ha b hb => hE.1 a ha b hb

/-- The underlying type is exactly the set of tuples from the paper. -/
def finiteTupleDistribLattice (hE : finiteLatticeClosed n E) : DistribLattice E :=
  inferInstanceAs (DistribLattice (finiteBundledSublattice hE))

def finiteTupleOrderBot (hE : finiteLatticeClosed n E) (hne : E.Nonempty) : OrderBot E := by
  letI : DistribLattice E := finiteTupleDistribLattice hE
  letI : Nonempty E := hne.to_subtype
  exact Fintype.toOrderBot E

/-- The integer called `h` in Theorem 8.1 is the cardinality of the actual
join-irreducible poset of the finite lattice, not an externally supplied bound. -/
def finiteLatticeHeight (hE : finiteLatticeClosed n E) (hne : E.Nonempty) : ℕ := by
  letI : DistribLattice E := finiteTupleDistribLattice hE
  letI : OrderBot E := finiteTupleOrderBot hE hne
  exact FourPapers.FiniteDistributive.height E

def finiteLatticeBottom (hE : finiteLatticeClosed n E) (hne : E.Nonempty) : E := by
  letI : OrderBot E := finiteTupleOrderBot hE hne
  exact ⊥

lemma finiteLatticeBottom_le (hE : finiteLatticeClosed n E) (hne : E.Nonempty) (a : E) :
    (finiteLatticeBottom hE hne).val ≤ a.val := by
  letI : OrderBot E := finiteTupleOrderBot hE hne
  exact (show (⊥ : E) ≤ a from bot_le)

def finiteLatticeMaximalChain (hE : finiteLatticeClosed n E) (hne : E.Nonempty) :
    Fin (finiteLatticeHeight hE hne + 1) → E := by
  letI : DistribLattice E := finiteTupleDistribLattice hE
  letI : OrderBot E := finiteTupleOrderBot hE hne
  exact FourPapers.FiniteDistributive.maximalChain E

lemma finiteLatticeMaximalChain_strictMono (hE : finiteLatticeClosed n E)
    (hne : E.Nonempty) : StrictMono (finiteLatticeMaximalChain hE hne) := by
  letI : DistribLattice E := finiteTupleDistribLattice hE
  letI : OrderBot E := finiteTupleOrderBot hE hne
  exact FourPapers.FiniteDistributive.maximalChain_strictMono E

@[simp] lemma finiteLatticeMaximalChain_zero (hE : finiteLatticeClosed n E)
    (hne : E.Nonempty) : finiteLatticeMaximalChain hE hne 0 = finiteLatticeBottom hE hne := by
  letI : DistribLattice E := finiteTupleDistribLattice hE
  letI : OrderBot E := finiteTupleOrderBot hE hne
  exact FourPapers.FiniteDistributive.maximalChain_zero E

lemma finiteLatticeMaximalChain_covBy (hE : finiteLatticeClosed n E)
    (hne : E.Nonempty) (i : Fin (finiteLatticeHeight hE hne)) :
    finiteLatticeMaximalChain hE hne i.castSucc ⋖
      finiteLatticeMaximalChain hE hne i.succ := by
  letI : DistribLattice E := finiteTupleDistribLattice hE
  letI : OrderBot E := finiteTupleOrderBot hE hne
  exact FourPapers.FiniteDistributive.maximalChain_covBy E i

lemma finiteLattice_chain_card (hE : finiteLatticeClosed n E) (hne : E.Nonempty)
    (s : Finset E) (hs : (s : Set E).Pairwise (fun a b => a ≤ b ∨ b ≤ a))
    (hbot : finiteLatticeBottom hE hne ∉ s) : s.card ≤ finiteLatticeHeight hE hne := by
  letI : DistribLattice E := finiteTupleDistribLattice hE
  letI : OrderBot E := finiteTupleOrderBot hE hne
  exact FourPapers.FiniteDistributive.chain_card_le_height E s hs hbot

end FourPapers.Sublattice
end

end
end

/- BEGIN EXACT BODY: FourPapers.Common.FiniteLatticeThresholds -/
section

/-!
# Coordinate thresholds in a finite distributive lattice

A threshold of a lattice map to a chain is either constant or the principal
filter of an actual join-irreducible. This gives the row-difference label
formula without assuming a coordinate-chain representation.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace FourPapers

inductive CoordinateSymbol (P : Type*)
  | zero
  | top
  | at (p : P)
  deriving DecidableEq

namespace FiniteDistributive

open Classical
variable (L : Type*) [Fintype L] [DistribLattice L] [OrderBot L]

def thresholdHolds (c : CoordinateSymbol (Irreducible L)) (a : L) : Prop :=
  match c with
  | .zero => False
  | .top => True
  | .at p => p.val ≤ a

theorem exists_thresholdSymbol (φ : L → ℕ) (hmono : Monotone φ)
    (hinf : ∀ a b, φ (a ⊓ b) = min (φ a) (φ b))
    (hsup : ∀ a b, φ (a ⊔ b) = max (φ a) (φ b)) (j : ℕ) :
    ∃ c : CoordinateSymbol (Irreducible L), ∀ a, j ≤ φ a ↔ thresholdHolds L c a := by
  by_cases hall : j ≤ φ ⊥
  · exact ⟨.top,fun a => ⟨fun _ => True.intro,fun _ => hall.trans (hmono bot_le)⟩⟩
  by_cases hex : ∃ a, j ≤ φ a
  · let U : Finset L := Finset.univ.filter fun a => j ≤ φ a
    have hU : U.Nonempty := by
      obtain ⟨a,ha⟩ := hex
      exact ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩⟩
    obtain ⟨p,hp,hmin⟩ := U.exists_minimal hU
    have hpj : j ≤ φ p := (Finset.mem_filter.mp hp).2
    have hleast : ∀ a, j ≤ φ a → p ≤ a := by
      intro a ha
      have hpa : p ⊓ a ∈ U := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _,by rw [hinf]; exact le_min hpj ha⟩
      exact (hmin hpa inf_le_left).trans inf_le_right
    have hprime : SupPrime p := by
      refine ⟨?_,?_⟩
      · intro hpmin
        have he : p=⊥ := isMin_iff_eq_bot.mp hpmin
        exact hall (he ▸ hpj)
      · intro a b hpab
        have hh : j ≤ max (φ a) (φ b) := by
          rw [← hsup]
          exact hpj.trans (hmono hpab)
        exact (le_max_iff.mp hh).imp (hleast a) (hleast b)
    refine ⟨.at ⟨p,hprime.supIrred⟩,?_⟩
    intro a
    exact ⟨hleast a,fun h => hpj.trans (hmono h)⟩
  · refine ⟨.zero,?_⟩
    intro a
    exact ⟨fun h => hex ⟨a,h⟩,False.elim⟩

def thresholdSymbol (φ : L → ℕ) (hmono : Monotone φ)
    (hinf : ∀ a b, φ (a ⊓ b) = min (φ a) (φ b))
    (hsup : ∀ a b, φ (a ⊔ b) = max (φ a) (φ b)) (j : ℕ) :
    CoordinateSymbol (Irreducible L) :=
  Classical.choose (exists_thresholdSymbol L φ hmono hinf hsup j)

theorem thresholdSymbol_spec (φ : L → ℕ) (hmono : Monotone φ)
    (hinf : ∀ a b, φ (a ⊓ b) = min (φ a) (φ b))
    (hsup : ∀ a b, φ (a ⊔ b) = max (φ a) (φ b)) (j : ℕ) (a : L) :
    j ≤ φ a ↔ thresholdHolds L (thresholdSymbol L φ hmono hinf hsup j) a :=
  Classical.choose_spec (exists_thresholdSymbol L φ hmono hinf hsup j) a

end FiniteDistributive
end FourPapers

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.FiniteLatticeOrderPoints -/
section

/-! # Integer order-polytope points are exactly multichains of the lattice -/

section
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace FourPapers.FiniteDistributive

open Classical
variable (L : Type*) [Fintype L] [DistribLattice L] [OrderBot L] (m : ℕ)

abbrev OrderPoint := {f : Irreducible L → Fin (m+1) // Antitone f}
abbrev Multichain := {w : Fin m → L // Monotone w}

def levelIdeal (f : OrderPoint L m) (t : Fin m) : LowerSet (Irreducible L) where
  carrier := {p | t.val < (f.val p).val}
  lower' := by
    intro p q hqp hp
    change t.val < (f.val p).val at hp
    exact hp.trans_le (show (f.val p).val ≤ (f.val q).val from f.property hqp)

def pointChain (f : OrderPoint L m) : Multichain L m :=
  ⟨fun s => OrderIso.lowerSetSupIrred.symm (levelIdeal L m f s.rev),by
    intro s t hst
    apply OrderIso.lowerSetSupIrred.symm.monotone
    intro p hp
    change s.rev.val < (f.val p).val at hp
    change t.rev.val < (f.val p).val
    exact lt_of_le_of_lt
      (show t.rev.val ≤ s.rev.val from Fin.rev_le_rev.mpr hst) hp⟩

@[simp] theorem le_pointChain (f : OrderPoint L m) (s : Fin m) (p : Irreducible L) :
    p.val ≤ (pointChain L m f).val s ↔ s.rev.val < (f.val p).val := by
  change p ∈ OrderIso.lowerSetSupIrred
      (OrderIso.lowerSetSupIrred.symm (levelIdeal L m f s.rev)) ↔ _
  rw [OrderIso.apply_symm_apply]
  rfl

def chainPoint (w : Multichain L m) : OrderPoint L m :=
  ⟨fun p => ⟨(Finset.univ.filter fun s : Fin m => p.val ≤ w.val s).card,by
      simpa only [Fintype.card_fin] using
        Nat.lt_succ_of_le (Finset.card_le_univ
          (Finset.univ.filter fun s : Fin m => p.val ≤ w.val s))⟩,by
    intro p q hpq
    change (Finset.univ.filter fun s : Fin m => q.val ≤ w.val s).card ≤
      (Finset.univ.filter fun s : Fin m => p.val ≤ w.val s).card
    apply Finset.card_le_card
    intro s hs
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (show p.val ≤ q.val from hpq).trans (Finset.mem_filter.mp hs).2⟩⟩

/-- An upper subset of `Fin m` is determined by its cardinality. -/
theorem upperPredicate_iff_count (P : Fin m → Prop) (hP : ∀ s t, s ≤ t → P s → P t)
    (s : Fin m) :
    P s ↔ s.rev.val < (Finset.univ.filter P).card := by
  have hs := s.isLt
  have hrev : s.rev.val = m - 1 - s.val := by
    rw [Fin.val_rev]
    omega
  rw [hrev]
  constructor
  · intro hp
    have hsub : Finset.Ici s ⊆ Finset.univ.filter P := by
      intro t ht
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hP s t (Finset.mem_Ici.mp ht) hp⟩
    have hc := Finset.card_le_card hsub
    rw [Fin.card_Ici] at hc
    omega
  · intro hc
    by_contra hp
    have hsub : Finset.univ.filter P ⊆ Finset.Ioi s := by
      intro t ht
      apply Finset.mem_Ioi.mpr
      by_contra hst
      exact hp (hP t s (le_of_not_gt hst) (Finset.mem_filter.mp ht).2)
    have hh := Finset.card_le_card hsub
    rw [Fin.card_Ioi] at hh
    omega

@[simp] theorem pointChain_chainPoint (w : Multichain L m) :
    pointChain L m (chainPoint L m w) = w := by
  apply Subtype.ext
  funext s
  apply OrderIso.lowerSetSupIrred.injective
  ext p
  change p.val ≤ (pointChain L m (chainPoint L m w)).val s ↔ p.val ≤ w.val s
  rw [le_pointChain]
  exact (upperPredicate_iff_count m (fun t => p.val ≤ w.val t)
    (fun t u htu hp => hp.trans (w.property htu)) s).symm

@[simp] theorem chainPoint_pointChain (f : OrderPoint L m) :
    chainPoint L m (pointChain L m f) = f := by
  apply Subtype.ext
  funext p
  apply Fin.ext
  change (Finset.univ.filter fun s : Fin m => p.val ≤ (pointChain L m f).val s).card = _
  simp only [le_pointChain]
  calc
    _ = (Finset.univ.filter fun t : Fin m => t.val < (f.val p).val).card := by
      apply Finset.card_bij (fun s _ => s.rev)
      · intro s hs
        simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hs
      · intro s hs t ht he
        exact Fin.rev_bijective.1 he
      · intro t ht
        refine ⟨t.rev,?_,Fin.rev_rev t⟩
        simpa only [Finset.mem_filter,Finset.mem_univ,true_and,Fin.rev_rev] using ht
    _ = (f.val p).val := by
      rw [Fin.card_filter_val_lt,min_eq_right (Nat.le_of_lt_succ (f.val p).isLt)]

def pointChainEquiv : OrderPoint L m ≃ Multichain L m where
  toFun := pointChain L m
  invFun := chainPoint L m
  left_inv := chainPoint_pointChain L m
  right_inv := pointChain_chainPoint L m

def symbolValue (f : Irreducible L → Fin (m+1)) : CoordinateSymbol (Irreducible L) → ℕ
  | .zero => 0
  | .top => m
  | .at p => (f p).val

theorem threshold_count (f : OrderPoint L m) (c : CoordinateSymbol (Irreducible L)) :
    (Finset.univ.filter fun s : Fin m => thresholdHolds L c ((pointChain L m f).val s)).card =
      symbolValue L m f.val c := by
  cases c with
  | zero => simp [thresholdHolds,symbolValue]
  | top => simp [thresholdHolds,symbolValue]
  | «at» p =>
      have h := congrArg (fun g : OrderPoint L m => (g.val p).val) (chainPoint_pointChain L m f)
      exact h

theorem coordinate_threshold_count (f : OrderPoint L m) (φ : L → ℕ) (hmono : Monotone φ)
    (hinf : ∀ a b, φ (a ⊓ b) = min (φ a) (φ b))
    (hsup : ∀ a b, φ (a ⊔ b) = max (φ a) (φ b)) (j : ℕ) :
    (Finset.univ.filter fun s : Fin m => j ≤ φ ((pointChain L m f).val s)).card =
      symbolValue L m f.val (thresholdSymbol L φ hmono hinf hsup j) := by
  simp_rw [thresholdSymbol_spec L φ hmono hinf hsup j]
  exact threshold_count L m f _

end FourPapers.FiniteDistributive

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.SimplicialDomination -/
section

/-!
# Integral augmented contractions from dominated vertex deletion

A link which is a cone supplies an actual linear homotopy for deleting its
vertex. Repeated deletion therefore constructs an augmented contraction over
any commutative coefficient ring, without a topological comparison theorem.
-/

section
set_option autoImplicit false
noncomputable section

namespace FourPapers.SimplicialDomination

open Classical CommAlg.Simplicial

variable {V k : Type*} [Fintype V] [LinearOrder V] [CommRing k]

/-- An actual augmented simplicial contraction in all chain degrees. The
empty face is retained in degree zero. -/
structure FaceContraction (K : Finset V → Prop) where
  homotopy : Module.End k (Ambient V k)
  raises : ∀ i z, z ∈ Chains K i → homotopy z ∈ Chains K (i+1)
  identity : ∀ i z, z ∈ Chains K i → boundary (homotopy z) + homotopy (boundary z) = z

namespace FaceContraction

variable {K : Finset V → Prop} (C : FaceContraction (k := k) K)

include C in
theorem exactIn (i : ℕ) : ExactIn (k := k) K i := by
  intro z hz hdz
  refine ⟨C.homotopy z,C.raises i z hz,?_⟩
  simpa only [hdz,map_zero,add_zero] using C.identity i z hz

/-- The cone homotopy is exterior creation by its actual cone vertex. -/
def cone (a : V) (hc : ∀ F, K F → K (insert a F)) : FaceContraction (k := k) K where
  homotopy := creation a
  raises i z hz := creation_mem_of_cone a hc hz
  identity i z hz := by rw [boundary_creation]; exact sub_add_cancel _ _

end FaceContraction

lemma contraction_zero_degree_zero (v : V) {K : Finset V → Prop}
    {z : Ambient V k} (hz : z ∈ Chains K 0) : contraction v z = 0 := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨F,⟨hF,hcard⟩,rfl⟩ := hx
      have hF0 : F=∅ := Finset.card_eq_zero.mp hcard
      rw [hF0,contraction_basis]
      simp only [Finset.notMem_empty,if_false]
  | zero => exact map_zero _
  | add x y hx hy ihx ihy => rw [map_add,ihx,ihy,add_zero]
  | smul r x hx ih => rw [map_smul,ih,smul_zero]

/-- The actual vertex replacement operator sends e_v to e_a and fixes all
other exterior generators. Its formula includes every orientation sign. -/
def replacement (v a : V) : Module.End k (Ambient V k) :=
  LinearMap.id - (creation v).comp (contraction v) + (creation a).comp (contraction v)

/-- On a face containing v this is exterior creation by a; on every other
face it vanishes. The displayed equivalent formula makes chain identities
independent of an ordering convention for the vertices. -/
def deletionHomotopy (v a : V) : Module.End k (Ambient V k) :=
  -((creation (k := k) v).comp ((creation a).comp (contraction v)))

@[simp] theorem replacement_apply (v a : V) (z : Ambient V k) :
    replacement v a z = z-creation v (contraction v z)+creation a (contraction v z) := rfl

@[simp] theorem deletionHomotopy_apply (v a : V) (z : Ambient V k) :
    deletionHomotopy v a z = -creation v (creation a (contraction v z)) := rfl

theorem deletionHomotopy_identity (v a : V) (z : Ambient V k) :
    boundary (deletionHomotopy v a z) + deletionHomotopy v a (boundary z) =
      z-replacement v a z := by
  rw [deletionHomotopy_apply,map_neg,boundary_creation,boundary_creation,
    deletionHomotopy_apply,contraction_boundary,replacement_apply]
  simp only [map_sub,map_neg]
  abel

theorem replacement_chain (v a : V) (z : Ambient V k) :
    boundary (replacement v a z) = replacement v a (boundary z) := by
  rw [replacement_apply,map_add,map_sub,boundary_creation,boundary_creation,
    replacement_apply,contraction_boundary]
  simp only [map_neg]
  abel

variable {K : Finset V → Prop} (hK : Downward K) (v a : V)
  (hcone : ∀ F, link K v F → link K v (insert a F))

include hK hcone in
theorem replacement_mem_deletion (i : ℕ) (z : Ambient V k) (hz : z ∈ Chains K i) :
    replacement v a z ∈ Chains (deletion K v) i := by
  rw [replacement_apply]
  apply Submodule.add_mem _ (delete_part_mem v hz)
  cases i with
  | zero =>
      rw [contraction_zero_degree_zero v hz,map_zero]
      exact Submodule.zero_mem _
  | succ i =>
      exact link_le_deletion hK v (i+1)
        (creation_mem_of_cone a hcone (contraction_mem v hz))

include hcone in
theorem deletionHomotopy_raises (i : ℕ) (z : Ambient V k) (hz : z ∈ Chains K i) :
    deletionHomotopy v a z ∈ Chains K (i+1) := by
  rw [deletionHomotopy_apply]
  apply Submodule.neg_mem
  cases i with
  | zero =>
      rw [contraction_zero_degree_zero v hz,map_zero,map_zero]
      exact Submodule.zero_mem _
  | succ i =>
      exact creation_mem_link v (creation_mem_of_cone a hcone (contraction_mem v hz))

include hK hcone in
/-- A dominated vertex can be deleted while retaining an explicit
augmented linear contraction in every degree. -/
def FaceContraction.ofDeletionCone (D : FaceContraction (k := k) (deletion K v)) :
    FaceContraction (k := k) K where
  homotopy := deletionHomotopy v a + D.homotopy.comp (replacement v a)
  raises i z hz := by
    change deletionHomotopy v a z + D.homotopy (replacement v a z) ∈ Chains K (i+1)
    exact Submodule.add_mem _ (deletionHomotopy_raises v a hcone i z hz)
      (chains_mono (fun F hF => hF.1) (i+1)
        (D.raises i _ (replacement_mem_deletion hK v a hcone i z hz)))
  identity i z hz := by
    change boundary (deletionHomotopy v a z + D.homotopy (replacement v a z)) +
      (deletionHomotopy v a (boundary z) + D.homotopy (replacement v a (boundary z))) = z
    rw [map_add,← replacement_chain]
    have h₁ := deletionHomotopy_identity (k := k) v a z
    have h₂ := D.identity i _ (replacement_mem_deletion hK v a hcone i z hz)
    calc
      _ = (boundary (deletionHomotopy v a z) + deletionHomotopy v a (boundary z)) +
        (boundary (D.homotopy (replacement v a z)) +
          D.homotopy (boundary (replacement v a z))) := by abel
      _ = z := by rw [h₁,h₂]; exact sub_add_cancel _ _

end FourPapers.SimplicialDomination

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.IntegerAlcoveContraction -/
section

/-!
# A combinatorial contraction of finite integer alcove complexes

A Freudenthal simplex is a coordinatewise chain of integer vertices whose
coordinate diameters are at most one. For a finite vertex set with least
vertex a, the operation v ↦ max(a,v−1) supplies a cone point in the link of
every maximal vertex. The resulting deletion recursion constructs an actual
augmented integral chain contraction of the full induced complex.
-/

section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
noncomputable section

namespace FourPapers.IntegerAlcove

open Classical CommAlg.Simplicial SimplicialDomination

variable {V I k : Type*} [Fintype V] [LinearOrder V] [CommRing k]
  (coordinate : V → I → ℤ)

/-- The literal simplices of the integer affine-braid triangulation. -/
def faces (S : Finset V) (F : Finset V) : Prop :=
  F ⊆ S ∧
    (∀ v ∈ F, ∀ w ∈ F, coordinate v ≤ coordinate w ∨ coordinate w ≤ coordinate v) ∧
    ∀ v ∈ F, ∀ w ∈ F, ∀ i, coordinate v i ≤ coordinate w i+1

theorem faces_downward (S : Finset V) : Downward (faces coordinate S) := by
  intro F G hGF hF
  exact ⟨hGF.trans hF.1,fun v hv w hw => hF.2.1 v (hGF hv) w (hGF hw),
    fun v hv w hw i => hF.2.2 v (hGF hv) w (hGF hw) i⟩

theorem faces_erase (S : Finset V) (v : V) :
    faces coordinate (S.erase v) = deletion (faces coordinate S) v := by
  funext F
  apply propext
  constructor
  · intro hF
    refine ⟨⟨hF.1.trans (Finset.erase_subset _ _),hF.2⟩,?_⟩
    intro hv
    exact Finset.notMem_erase v S (hF.1 hv)
  · rintro ⟨hF,hv⟩
    refine ⟨?_,hF.2⟩
    intro w hw
    exact Finset.mem_erase.mpr ⟨(fun h => hv (h ▸ hw)),hF.1 hw⟩

theorem faces_insert_of_le (S F : Finset V) (u : V)
    (hF : faces coordinate S F) (hu : u ∈ S)
    (hlo : ∀ w ∈ F, coordinate u ≤ coordinate w)
    (hhi : ∀ w ∈ F, ∀ i, coordinate w i ≤ coordinate u i+1) :
    faces coordinate S (insert u F) := by
  refine ⟨Finset.insert_subset_iff.mpr ⟨hu,hF.1⟩,?_,?_⟩
  · intro v hv w hw
    rcases Finset.mem_insert.mp hv with hv | hv
    · rcases Finset.mem_insert.mp hw with hw | hw
      · rw [hv,hw]
        exact Or.inl le_rfl
      · rw [hv]
        exact Or.inl (hlo w hw)
    · rcases Finset.mem_insert.mp hw with hw | hw
      · rw [hw]
        exact Or.inr (hlo v hv)
      · exact hF.2.1 v hv w hw
  · intro v hv w hw i
    rcases Finset.mem_insert.mp hv with hv | hv
    · rcases Finset.mem_insert.mp hw with hw | hw
      · rw [hv,hw]
        omega
      · rw [hv]
        exact (hlo w hw i).trans (le_add_of_nonneg_right (by decide : (0 : ℤ) ≤ 1))
    · rcases Finset.mem_insert.mp hw with hw | hw
      · rw [hw]
        exact hhi v hv i
      · exact hF.2.2 v hv w hw i

theorem singleton_cone (a : V) (F : Finset V) (hF : faces coordinate {a} F) :
    faces coordinate {a} (insert a F) := by
  apply faces_insert_of_le coordinate {a} F a hF (Finset.mem_singleton_self a)
  · intro w hw
    have he : w=a := Finset.mem_singleton.mp (hF.1 hw)
    subst w
    exact le_rfl
  · intro w hw i
    have he : w=a := Finset.mem_singleton.mp (hF.1 hw)
    subst w
    omega

/-- The geometric conditions used by the explicit deletion contraction.
They will be proved from the actual integer difference inequalities. -/
structure StepSystem (Q : Finset V) (a : V) : Prop where
  anchor_mem : a ∈ Q
  least : ∀ v ∈ Q, coordinate a ≤ coordinate v
  lower_step : ∀ v ∈ Q, v ≠ a →
    ∃ u ∈ Q, ∀ i, coordinate u i = max (coordinate a i) (coordinate v i-1)

def LowerVertexSet (Q S : Finset V) : Prop :=
  S ⊆ Q ∧ ∀ v ∈ S, ∀ u ∈ Q, coordinate u ≤ coordinate v → u ∈ S

variable {coordinate} (hinj : Function.Injective coordinate)
  {Q : Finset V} {a : V} (H : StepSystem coordinate Q a)

include H in
lemma step_le {v u : V} (hv : v ∈ Q)
    (hu : ∀ i, coordinate u i = max (coordinate a i) (coordinate v i-1)) :
    coordinate u ≤ coordinate v := by
  intro i
  rw [hu i]
  exact max_le (H.least v hv i) (sub_le_self _ (by decide : (0 : ℤ) ≤ 1))

include hinj H in
lemma step_ne {v u : V} (hv : v ∈ Q) (hva : v ≠ a)
    (hu : ∀ i, coordinate u i = max (coordinate a i) (coordinate v i-1)) : u ≠ v := by
  intro huv
  apply hva
  apply hinj
  funext i
  have ha := H.least v hv i
  by_contra hne
  have hlt : coordinate a i < coordinate v i := lt_of_le_of_ne ha (Ne.symm hne)
  have hm : max (coordinate a i) (coordinate v i-1) < coordinate v i :=
    max_lt_iff.mpr ⟨hlt,by omega⟩
  rw [← hu i,huv] at hm
  exact (lt_irrefl _ hm)

include H in
lemma maximal_link_cone {S : Finset V} (hS : LowerVertexSet coordinate Q S)
    {v u : V} (hv : v ∈ S) (hmax : ∀ w ∈ S, coordinate v ≤ coordinate w → coordinate w ≤ coordinate v)
    (huQ : u ∈ Q) (huv : u ≠ v)
    (hu : ∀ i, coordinate u i = max (coordinate a i) (coordinate v i-1)) :
    ∀ F, link (faces coordinate S) v F → link (faces coordinate S) v (insert u F) := by
  intro F hF
  have huS : u ∈ S := hS.2 v hv u huQ (step_le H (hS.1 hv) hu)
  have hwv : ∀ w ∈ insert v F, coordinate w ≤ coordinate v := by
    intro w hw
    rcases hF.1.2.1 w hw v (Finset.mem_insert_self v F) with h | h
    · exact h
    · exact hmax w (hF.1.1 hw) h
  have hlow : ∀ w ∈ insert v F, coordinate u ≤ coordinate w := by
    intro w hw i
    rw [hu i]
    apply max_le (H.least w (hS.1 (hF.1.1 hw)) i)
    have hd := hF.1.2.2 v (Finset.mem_insert_self v F) w hw i
    exact sub_le_iff_le_add.mpr hd
  have hupp : ∀ w ∈ insert v F, ∀ i, coordinate w i ≤ coordinate u i+1 := by
    intro w hw i
    have hw' := hwv w hw i
    have hu' := le_max_right (coordinate a i) (coordinate v i-1)
    rw [← hu i] at hu'
    exact hw'.trans (sub_le_iff_le_add.mp hu')
  have hnew := faces_insert_of_le coordinate S (insert v F) u hF.1 huS hlow hupp
  refine ⟨?_,?_⟩
  · simpa only [Finset.insert_comm] using hnew
  · intro hv'
    rcases Finset.mem_insert.mp hv' with h | h
    · exact huv h.symm
    · exact hF.2 h

include hinj H in
/-- An explicit finite sequence of link-cone deletions gives an actual
augmented contraction over every coefficient ring. -/
theorem nonempty_faceContraction : Nonempty (FaceContraction (k := k) (faces coordinate Q)) := by
  have hmain : ∀ n : ℕ, ∀ S : Finset V, S.card=n →
      LowerVertexSet coordinate Q S → a ∈ S →
        Nonempty (FaceContraction (k := k) (faces coordinate S)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro S hn hS haS
      by_cases hsingle : S={a}
      · subst S
        exact ⟨FaceContraction.cone a (singleton_cone coordinate a)⟩
      · obtain ⟨v,hv,hmax⟩ := Finset.exists_maximalFor coordinate S ⟨a,haS⟩
        have hva : v ≠ a := by
          intro he
          apply hsingle
          ext w
          constructor
          · intro hw
            apply Finset.mem_singleton.mpr
            apply hinj
            have hl := H.least w (hS.1 hw)
            have hvw : coordinate v ≤ coordinate w := by simpa only [he] using hl
            have hr : coordinate w ≤ coordinate a := by
              simpa only [he] using hmax hw hvw
            exact le_antisymm hr hl
          · intro hw
            rw [Finset.mem_singleton] at hw
            subst w
            exact haS
        obtain ⟨u,huQ,hu⟩ := H.lower_step v (hS.1 hv) hva
        have huv := step_ne hinj H (hS.1 hv) hva hu
        have hS' : LowerVertexSet coordinate Q (S.erase v) := by
          refine ⟨(Finset.erase_subset _ _).trans hS.1,?_⟩
          intro w hw t ht htw
          have hw' := Finset.mem_erase.mp hw
          refine Finset.mem_erase.mpr ⟨?_,hS.2 w hw'.2 t ht htw⟩
          intro htv
          subst t
          have hwt : w=v := hinj (le_antisymm (hmax hw'.2 htw) htw)
          exact hw'.1 hwt
        have ha' : a ∈ S.erase v := Finset.mem_erase.mpr ⟨Ne.symm hva,haS⟩
        have hlt : (S.erase v).card<n := by
          rw [← hn]
          exact Finset.card_erase_lt_of_mem hv
        obtain ⟨D⟩ := ih (S.erase v).card hlt (S.erase v) rfl hS' ha'
        have D' : FaceContraction (k := k) (deletion (faces coordinate S) v) := by
          rw [← faces_erase]
          exact D
        exact ⟨FaceContraction.ofDeletionCone (faces_downward coordinate S) v u
          (maximal_link_cone H hS hv hmax huQ huv hu) D'⟩
  exact hmain Q.card Q rfl ⟨Finset.Subset.refl _,fun _ _ _ hu _ => hu⟩ H.anchor_mem

include hinj H in
/-- The actual contracting operator selected from the proved finite
deletion construction. No homology-vanishing axiom is used. -/
def faceContraction : FaceContraction (k := k) (faces coordinate Q) :=
  Classical.choice (nonempty_faceContraction (k := k) hinj H)

include hinj H in
theorem faces_exact (p : ℕ) : ExactIn (k := k) (faces coordinate Q) p :=
  (faceContraction (k := k) hinj H).exactIn p

end FourPapers.IntegerAlcove

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.IntegerDifferencePolytope -/
section

/-!
# Literal bounded integer difference polytopes have contracting alcove complexes

All vertices are actual integer points in a finite cube. Absolute coordinate
bounds and arbitrary integral difference inequalities define the vertex set.
Its coordinatewise minimum and the lower-step operation are proved to stay
inside it. Thus the chain contraction requires no unproved convexity or
contractibility assertion.
-/

section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
noncomputable section

namespace FourPapers.IntegerDifferencePolytope

open Classical

variable {I : Type*} [Fintype I] (m : ℕ)

abbrev Vertex := I → Fin (m+1)

/-- This order only orients exterior faces. Coordinate comparisons below
always use the explicit coordinate map and never this arbitrary total order. -/
noncomputable instance vertexLinearOrder : LinearOrder (Vertex (I := I) m) :=
  LinearOrder.lift' (Fintype.equivFin (Vertex (I := I) m)) (Fintype.equivFin _).injective

def coordinate (f : Vertex (I := I) m) (i : I) : ℤ := (f i).val

theorem coordinate_injective : Function.Injective (coordinate (I := I) m) := by
  intro f g h
  funext i
  apply Fin.ext
  have hi := congrFun h i
  change ((f i).val : ℤ) = ((g i).val : ℤ) at hi
  exact_mod_cast hi

structure Bounds where
  lower : I → ℤ
  upper : I → ℤ
  differences : Set (I × I × ℤ)

namespace Bounds

variable (B : Bounds (I := I))

def Allowed (f : Vertex (I := I) m) : Prop :=
  (∀ i, B.lower i ≤ coordinate m f i ∧ coordinate m f i ≤ B.upper i) ∧
    ∀ i j b, (i,j,b) ∈ B.differences → coordinate m f i-coordinate m f j ≤ b

def vertices : Finset (Vertex (I := I) m) := Finset.univ.filter (B.Allowed m)

@[simp] theorem mem_vertices (f : Vertex (I := I) m) : f ∈ B.vertices m ↔ B.Allowed m f := by
  simp only [vertices,Finset.mem_filter,Finset.mem_univ,true_and]

end Bounds

def vertexMin (f g : Vertex (I := I) m) : Vertex (I := I) m := fun i => min (f i) (g i)

@[simp] theorem vertexMin_coordinate (f g : Vertex (I := I) m) (i : I) :
    coordinate m (vertexMin m f g) i = min (coordinate m f i) (coordinate m g i) := by
  change ((min (f i) (g i)).val : ℤ) = min ((f i).val : ℤ) ((g i).val : ℤ)
  rw [Fin.val_min]
  exact_mod_cast (rfl : min (f i).val (g i).val = min (f i).val (g i).val)

lemma min_difference_le (x y x' y' b : ℤ) (hx : x-x'≤b) (hy : y-y'≤b) :
    min x y-min x' y'≤b := by
  by_cases h : x'≤y'
  · rw [min_eq_left h]
    have hm := min_le_left x y
    omega
  · rw [min_eq_right (le_of_not_ge h)]
    have hm := min_le_right x y
    omega

lemma max_difference_le (x y x' y' b : ℤ) (hx : x-x'≤b) (hy : y-y'≤b) :
    max x y-max x' y'≤b := by
  by_cases h : x≤y
  · rw [max_eq_right h]
    have hm := le_max_right x' y'
    omega
  · rw [max_eq_left (le_of_not_ge h)]
    have hm := le_max_left x' y'
    omega

namespace Bounds

variable (B : Bounds (I := I))

theorem allowed_min {f g : Vertex (I := I) m} (hf : B.Allowed m f) (hg : B.Allowed m g) :
    B.Allowed m (vertexMin m f g) := by
  refine ⟨?_,?_⟩
  · intro i
    rw [vertexMin_coordinate]
    exact ⟨le_min (hf.1 i).1 (hg.1 i).1,(min_le_left _ _).trans (hf.1 i).2⟩
  · intro i j b hb
    rw [vertexMin_coordinate,vertexMin_coordinate]
    exact min_difference_le _ _ _ _ b (hf.2 i j b hb) (hg.2 i j b hb)

/-- A minimal integer vertex is automatically the coordinatewise least
vertex because the actual inequality set is closed under componentwise min. -/
theorem exists_least (hQ : (B.vertices m).Nonempty) :
    ∃ a ∈ B.vertices m, ∀ v ∈ B.vertices m, coordinate m a ≤ coordinate m v := by
  obtain ⟨a,ha,hmin⟩ := Finset.exists_minimalFor (coordinate m) (B.vertices m) hQ
  refine ⟨a,ha,?_⟩
  intro v hv
  have hu : vertexMin m a v ∈ B.vertices m :=
    (B.mem_vertices m _).mpr (B.allowed_min m ((B.mem_vertices m _).mp ha) ((B.mem_vertices m _).mp hv))
  have hua : coordinate m (vertexMin m a v) ≤ coordinate m a := by
    intro i
    rw [vertexMin_coordinate]
    exact min_le_left _ _
  have hau := hmin hu hua
  intro i
  exact (hau i).trans (by rw [vertexMin_coordinate]; exact min_le_right _ _)

end Bounds

/-- The exact simultaneous one-step descent, clipped at the least vertex.
All coordinates remain actual elements of the original finite integer cube. -/
def lowerStepVertex (a v : Vertex (I := I) m) (hav : coordinate m a ≤ coordinate m v) :
    Vertex (I := I) m := fun i =>
  ⟨(max (coordinate m a i) (coordinate m v i-1)).toNat, by
    have hle : max (coordinate m a i) (coordinate m v i-1) ≤ coordinate m v i :=
      max_le (hav i) (by omega)
    apply (Int.toNat_lt_of_ne_zero (Nat.succ_ne_zero m)).mpr
    apply hle.trans_lt
    change ((v i).val : ℤ) < ((m+1 : ℕ) : ℤ)
    exact_mod_cast (v i).isLt⟩

@[simp] theorem lowerStepVertex_coordinate (a v : Vertex (I := I) m)
    (hav : coordinate m a ≤ coordinate m v) (i : I) :
    coordinate m (lowerStepVertex m a v hav) i =
      max (coordinate m a i) (coordinate m v i-1) := by
  change ((max (coordinate m a i) (coordinate m v i-1)).toNat : ℤ) = _
  apply Int.toNat_of_nonneg
  exact (Int.natCast_nonneg _).trans (le_max_left _ _)

namespace Bounds

variable (B : Bounds (I := I))

theorem allowed_lowerStep {a v : Vertex (I := I) m}
    (ha : B.Allowed m a) (hv : B.Allowed m v) (hav : coordinate m a ≤ coordinate m v) :
    B.Allowed m (lowerStepVertex m a v hav) := by
  refine ⟨?_,?_⟩
  · intro i
    rw [lowerStepVertex_coordinate]
    refine ⟨(ha.1 i).1.trans (le_max_left _ _),?_⟩
    have hstep : coordinate m v i-1 ≤ coordinate m v i := by omega
    exact (max_le (hav i) hstep).trans (hv.1 i).2
  · intro i j b hb
    rw [lowerStepVertex_coordinate,lowerStepVertex_coordinate]
    apply max_difference_le _ _ _ _ b (ha.2 i j b hb)
    have hh := hv.2 i j b hb
    omega

/-- Every geometric hypothesis of the simplicial contraction is now derived
from the actual inequality-defined integer vertex set. -/
def stepSystem (hQ : (B.vertices m).Nonempty) :
    IntegerAlcove.StepSystem (coordinate m) (B.vertices m)
      (Classical.choose (B.exists_least m hQ)) := by
  let a := Classical.choose (B.exists_least m hQ)
  have ha := Classical.choose_spec (B.exists_least m hQ)
  refine ⟨ha.1,ha.2,?_⟩
  intro v hv hva
  refine ⟨lowerStepVertex m a v (ha.2 v hv),?_,?_⟩
  · apply (B.mem_vertices m _).mpr
    exact B.allowed_lowerStep m ((B.mem_vertices m _).mp ha.1)
      ((B.mem_vertices m _).mp hv) (ha.2 v hv)
  · exact lowerStepVertex_coordinate m a v (ha.2 v hv)

/-- The actual oriented augmented chain complex of every nonempty induced
integer divisor polytope contracts over every commutative coefficient ring. -/
def faceContraction {k : Type*} [CommRing k] (hQ : (B.vertices m).Nonempty) :
    SimplicialDomination.FaceContraction (k := k)
      (IntegerAlcove.faces (coordinate m) (B.vertices m)) :=
  IntegerAlcove.faceContraction (coordinate_injective m) (B.stepSystem m hQ)

theorem exactIn {k : Type*} [CommRing k] (hQ : (B.vertices m).Nonempty) (p : ℕ) :
    CommAlg.Simplicial.ExactIn (k := k)
      (IntegerAlcove.faces (coordinate m) (B.vertices m)) p :=
  (B.faceContraction m (k := k) hQ).exactIn p

end Bounds
end FourPapers.IntegerDifferencePolytope

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.IntegerAlcoveDimension -/
section

/-! # The exact combinatorial dimension of an integer alcove simplex -/

section
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace FourPapers.IntegerAlcove

open Classical CommAlg.Simplicial

variable {V I k : Type*} [Fintype V] [LinearOrder V] [Fintype I] [CommRing k]
  (coordinate : V → I → ℤ) (hinj : Function.Injective coordinate)

/-- Within a unit cube the set of coordinates above the bottom vertex
determines a vertex exactly. -/
def highCoordinates (a v : V) : Finset I :=
  Finset.univ.filter fun i => coordinate a i < coordinate v i

include hinj in
theorem highCoordinates_injective_on_cube (a : V) {v w : V}
    (hav : coordinate a ≤ coordinate v) (haw : coordinate a ≤ coordinate w)
    (hva : ∀ i, coordinate v i ≤ coordinate a i+1)
    (hwa : ∀ i, coordinate w i ≤ coordinate a i+1)
    (he : highCoordinates coordinate a v = highCoordinates coordinate a w) : v=w := by
  apply hinj
  funext i
  have hm : (coordinate a i < coordinate v i) ↔ (coordinate a i < coordinate w i) := by
    simpa only [highCoordinates,Finset.mem_filter,Finset.mem_univ,true_and] using
      Iff.of_eq (congrArg (fun s : Finset I => i ∈ s) he)
  by_cases hv : coordinate a i < coordinate v i
  · have hw := hm.mp hv
    have hv' : coordinate v i = coordinate a i+1 :=
      le_antisymm (hva i) (Int.add_one_le_of_lt hv)
    have hw' : coordinate w i = coordinate a i+1 :=
      le_antisymm (hwa i) (Int.add_one_le_of_lt hw)
    exact hv'.trans hw'.symm
  · have hw : ¬coordinate a i < coordinate w i := mt hm.mpr hv
    have hv' : coordinate v i = coordinate a i := le_antisymm (le_of_not_gt hv) (hav i)
    have hw' : coordinate w i = coordinate a i := le_antisymm (le_of_not_gt hw) (haw i)
    exact hv'.trans hw'.symm

theorem highCoordinates_mono (a : V) {v w : V} (hvw : coordinate v ≤ coordinate w) :
    highCoordinates coordinate a v ⊆ highCoordinates coordinate a w := by
  intro i hi
  simp only [highCoordinates,Finset.mem_filter,Finset.mem_univ,true_and] at hi ⊢
  exact hi.trans_le (hvw i)

include hinj in
/-- Every simplex has at most `card I+1` vertices. This proves the length
bound from the literal finite face set, without an unformalized geometric
dimension assertion. -/
theorem face_card_le {S F : Finset V} (hF : faces coordinate S F) :
    F.card ≤ Fintype.card I+1 := by
  by_cases hne : F.Nonempty
  · obtain ⟨a,ha,hmin⟩ := Finset.exists_minimalFor coordinate F hne
    have hleast : ∀ v ∈ F, coordinate a ≤ coordinate v := by
      intro v hv
      rcases hF.2.1 a ha v hv with hav | hva
      · exact hav
      · exact hmin hv hva
    let rank : V → ℕ := fun v => (highCoordinates coordinate a v).card
    have hrank : Set.InjOn rank (F : Set V) := by
      intro v hv w hw he
      have hcubev := hF.2.2 v hv a ha
      have hcubew := hF.2.2 w hw a ha
      apply highCoordinates_injective_on_cube coordinate hinj a (hleast v hv)
        (hleast w hw) hcubev hcubew
      rcases hF.2.1 v hv w hw with hvw | hwv
      · exact Finset.eq_of_subset_of_card_le
          (highCoordinates_mono coordinate a hvw) he.ge
      · exact (Finset.eq_of_subset_of_card_le
          (highCoordinates_mono coordinate a hwv) he.le).symm
    have hsub : F.image rank ⊆ Finset.range (Fintype.card I+1) := by
      intro r hr
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hr
      apply Finset.mem_range.mpr
      exact Nat.lt_succ_of_le (Finset.card_le_univ (highCoordinates coordinate a v))
    have hc := Finset.card_le_card hsub
    rwa [Finset.card_image_of_injOn hrank,Finset.card_range] at hc
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty]
    exact Nat.zero_le _

include hinj in
theorem chains_eq_bot_of_gt_dimension (S : Finset V) (p : ℕ)
    (hp : Fintype.card I+1 < p) :
    Chains (k := k) (faces coordinate S) p = ⊥ := by
  apply chains_eq_bot_of_no_face
  intro F hF he
  have hc := face_card_le coordinate hinj hF
  omega

end FourPapers.IntegerAlcove

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.IntegerSymbolPolytope -/
section

/-!
# Integer difference inequalities with the fixed endpoints zero and m

The endpoint symbols allow constant rows and all unused row variables in the
original polynomial ring. An inconsistent constant inequality gives an empty
vertex set. No coordinates are discarded and no nonempty-strand assumption
is introduced into the final exactness criterion.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace FourPapers.IntegerSymbolPolytope

open Classical IntegerDifferencePolytope

variable {P : Type*} [Fintype P] (m : ℕ)

def value (f : Vertex (I := P) m) : CoordinateSymbol P → ℤ
  | .zero => 0
  | .top => m
  | .at p => coordinate m f p

@[simp] theorem value_min (f g : Vertex (I := P) m) (c : CoordinateSymbol P) :
    value m (vertexMin m f g) c = min (value m f c) (value m g c) := by
  cases c <;> simp only [value,vertexMin_coordinate,min_self]

@[simp] theorem value_step (a v : Vertex (I := P) m)
    (hav : coordinate m a ≤ coordinate m v) (c : CoordinateSymbol P) :
    value m (lowerStepVertex m a v hav) c = max (value m a c) (value m v c-1) := by
  cases c with
  | zero => norm_num [value]
  | top => simp only [value,max_eq_left (by omega : (m : ℤ)-1≤m)]
  | «at» p => exact lowerStepVertex_coordinate m a v hav p

abbrev System (P : Type*) := Set (CoordinateSymbol P × CoordinateSymbol P × ℤ)

def Allowed (B : System P) (f : Vertex (I := P) m) : Prop :=
  ∀ c d b, (c,d,b) ∈ B → value m f c-value m f d ≤ b

def vertices (B : System P) : Finset (Vertex (I := P) m) :=
  Finset.univ.filter (Allowed m B)

@[simp] theorem mem_vertices (B : System P) (f : Vertex (I := P) m) :
    f ∈ vertices m B ↔ Allowed m B f := by
  simp only [vertices,Finset.mem_filter,Finset.mem_univ,true_and]

theorem allowed_min {B : System P} {f g : Vertex (I := P) m}
    (hf : Allowed m B f) (hg : Allowed m B g) : Allowed m B (vertexMin m f g) := by
  intro c d b hb
  rw [value_min,value_min]
  exact min_difference_le _ _ _ _ b (hf c d b hb) (hg c d b hb)

theorem allowed_lowerStep {B : System P} {a v : Vertex (I := P) m}
    (ha : Allowed m B a) (hv : Allowed m B v) (hav : coordinate m a ≤ coordinate m v) :
    Allowed m B (lowerStepVertex m a v hav) := by
  intro c d b hb
  rw [value_step,value_step]
  apply max_difference_le _ _ _ _ b (ha c d b hb)
  have hh := hv c d b hb
  omega

theorem exists_least (B : System P) (hQ : (vertices m B).Nonempty) :
    ∃ a ∈ vertices m B, ∀ v ∈ vertices m B, coordinate m a ≤ coordinate m v := by
  obtain ⟨a,ha,hmin⟩ := Finset.exists_minimalFor (coordinate m) (vertices m B) hQ
  refine ⟨a,ha,?_⟩
  intro v hv
  have hu : vertexMin m a v ∈ vertices m B :=
    (mem_vertices m B _).mpr (allowed_min m ((mem_vertices m B _).mp ha)
      ((mem_vertices m B _).mp hv))
  have hua : coordinate m (vertexMin m a v) ≤ coordinate m a := by
    intro p
    rw [vertexMin_coordinate]
    exact min_le_left _ _
  have hau := hmin hu hua
  intro p
  exact (hau p).trans (by rw [vertexMin_coordinate]; exact min_le_right _ _)

def stepSystem (B : System P) (hQ : (vertices m B).Nonempty) :
    IntegerAlcove.StepSystem (coordinate m) (vertices m B)
      (Classical.choose (exists_least m B hQ)) := by
  let a := Classical.choose (exists_least m B hQ)
  have ha := Classical.choose_spec (exists_least m B hQ)
  refine ⟨ha.1,ha.2,?_⟩
  intro v hv hva
  refine ⟨lowerStepVertex m a v (ha.2 v hv),?_,?_⟩
  · apply (mem_vertices m B _).mpr
    exact allowed_lowerStep m ((mem_vertices m B _).mp ha.1)
      ((mem_vertices m B _).mp hv) (ha.2 v hv)
  · exact lowerStepVertex_coordinate m a v (ha.2 v hv)

def faceContraction {k : Type*} [CommRing k] (B : System P)
    (hQ : (vertices m B).Nonempty) :
    SimplicialDomination.FaceContraction (k := k)
      (IntegerAlcove.faces (coordinate m) (vertices m B)) :=
  IntegerAlcove.faceContraction (coordinate_injective m) (stepSystem m B hQ)

theorem exactIn {k : Type*} [CommRing k] (B : System P)
    (hQ : (vertices m B).Nonempty) (p : ℕ) :
    CommAlg.Simplicial.ExactIn (k := k)
      (IntegerAlcove.faces (coordinate m) (vertices m B)) p :=
  (faceContraction m B (k := k) hQ).exactIn p

end FourPapers.IntegerSymbolPolytope

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.AlcoveRowCoordinates -/
section

/-!
# The literal row labels of the order-polytope vertices

Every row and every original variable is retained. The two threshold symbols
for a variable give its exponent as a difference of integer order coordinates.
This includes constant rows and unused columns without auxiliary assumptions.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice

open Classical CommAlg.Polymatroid FiniteDistributive

universe u
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}
  (hE : finiteLatticeClosed n E) (hne : E.Nonempty)

/-- The actual finite tuple lattice, retaining its closure proof in the type head. -/
def AlcoveLattice (_hE : finiteLatticeClosed n E) : Type := E

instance alcoveLatticeFintype : Fintype (AlcoveLattice hE) :=
  inferInstanceAs (Fintype E)

instance alcoveLatticeDistribLattice : DistribLattice (AlcoveLattice hE) :=
  finiteTupleDistribLattice hE

/-- The carrier change is the identity on the original tuples and their order. -/
def alcoveLatticeOrderIso : AlcoveLattice hE ≃o E := OrderIso.refl _

abbrev AlcoveIrreducible := FiniteDistributive.Irreducible (AlcoveLattice hE)
abbrev AlcovePoint (m : ℕ) := FiniteDistributive.OrderPoint (AlcoveLattice hE) m

def rowCoordinate (r : Fin d) (a : E) : ℕ := (a.val r).val

theorem rowCoordinate_monotone (r : Fin d) : Monotone (rowCoordinate (E := E) r) :=
  fun _ _ h => h r

theorem rowCoordinate_inf (r : Fin d) (a b : AlcoveLattice hE) :
    rowCoordinate r ((a ⊓ b) : AlcoveLattice hE) = min (rowCoordinate r a) (rowCoordinate r b) := rfl

theorem rowCoordinate_sup (r : Fin d) (a b : AlcoveLattice hE) :
    rowCoordinate r ((a ⊔ b) : AlcoveLattice hE) = max (rowCoordinate r a) (rowCoordinate r b) := rfl

def rowThreshold (r : Fin d) (j : ℕ) : CoordinateSymbol (AlcoveIrreducible hE) := by
  letI : OrderBot (AlcoveLattice hE) := finiteTupleOrderBot hE hne
  exact thresholdSymbol (AlcoveLattice hE) (rowCoordinate r) (rowCoordinate_monotone r)
    (rowCoordinate_inf hE r) (rowCoordinate_sup hE r) j

theorem rowThreshold_spec (r : Fin d) (j : ℕ) (a : E) :
    j ≤ (a.val r).val ↔ thresholdHolds (AlcoveLattice hE) (rowThreshold hE hne r j) a := by
  letI : OrderBot (AlcoveLattice hE) := finiteTupleOrderBot hE hne
  exact thresholdSymbol_spec (AlcoveLattice hE) (rowCoordinate r) (rowCoordinate_monotone r)
    (rowCoordinate_inf hE r) (rowCoordinate_sup hE r) j a

def alcovePointChain (m : ℕ) (f : AlcovePoint hE m) : FiniteMultichain n E m := by
  letI : OrderBot (AlcoveLattice hE) := finiteTupleOrderBot hE hne
  exact ⟨(pointChain (AlcoveLattice hE) m f).val, fun _ _ h =>
    (pointChain (AlcoveLattice hE) m f).property h⟩

def alcoveChainPoint (hne : E.Nonempty) (m : ℕ) (w : FiniteMultichain n E m) : AlcovePoint hE m := by
  letI : OrderBot (AlcoveLattice hE) := finiteTupleOrderBot hE hne
  exact chainPoint (AlcoveLattice hE) m ⟨w.val, fun _ _ h => w.property h⟩

@[simp] theorem alcovePointChain_chainPoint (m : ℕ) (w : FiniteMultichain n E m) :
    alcovePointChain hE hne m (alcoveChainPoint hE hne m w) = w := by
  letI : OrderBot (AlcoveLattice hE) := finiteTupleOrderBot hE hne
  apply Subtype.ext
  exact congrArg (fun z : FiniteDistributive.Multichain (AlcoveLattice hE) m => z.val)
    (pointChain_chainPoint (AlcoveLattice hE) m ⟨w.val, fun _ _ h => w.property h⟩)

@[simp] theorem alcoveChainPoint_pointChain (m : ℕ) (f : AlcovePoint hE m) :
    alcoveChainPoint hE hne m (alcovePointChain hE hne m f) = f := by
  letI : OrderBot (AlcoveLattice hE) := finiteTupleOrderBot hE hne
  exact chainPoint_pointChain (AlcoveLattice hE) m f

def alcovePointChainEquiv (m : ℕ) : AlcovePoint hE m ≃ FiniteMultichain n E m where
  toFun := alcovePointChain hE hne m
  invFun := alcoveChainPoint hE hne m
  left_inv := alcoveChainPoint_pointChain hE hne m
  right_inv := alcovePointChain_chainPoint hE hne m

def alcovePointLabel (m : ℕ) (f : AlcovePoint hE m) : Exponent (FiniteVariable.{u} n) :=
  finiteChainShift n (alcovePointChain hE hne m f)

lemma count_eq_count_ge_sub (m : ℕ) (a : Fin m → ℕ) (j : ℕ) :
    (Finset.univ.filter fun s => a s=j).card =
      (Finset.univ.filter fun s => j≤a s).card-
        (Finset.univ.filter fun s => j+1≤a s).card := by
  have he : (Finset.univ.filter fun s => j≤a s) \ (Finset.univ.filter fun s => j+1≤a s) =
      (Finset.univ.filter fun s => a s=j) := by
    ext s
    simp only [Finset.mem_sdiff,Finset.mem_filter,Finset.mem_univ,true_and]
    omega
  rw [← he,Finset.card_sdiff_of_subset]
  intro s hs
  have hh := (Finset.mem_filter.mp hs).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩

/-- Cumulative row counts use the actual multichain attached to the point. -/
theorem rowThreshold_count (m : ℕ) (f : AlcovePoint hE m) (r : Fin d) (j : ℕ) :
    (Finset.univ.filter fun s : Fin m =>
      j ≤ (((alcovePointChain hE hne m f).val s).val r).val).card =
      symbolValue (AlcoveLattice hE) m f.val (rowThreshold hE hne r j) := by
  letI : OrderBot (AlcoveLattice hE) := finiteTupleOrderBot hE hne
  exact coordinate_threshold_count (AlcoveLattice hE) m f (rowCoordinate r)
    (rowCoordinate_monotone r) (rowCoordinate_inf hE r) (rowCoordinate_sup hE r) j

/-- The row-difference formula in Theorem 8.1, in the unchanged polynomial
variables. Threshold symbols are actual proved coordinate filters. -/
theorem alcovePointLabel_apply (m : ℕ) (f : AlcovePoint hE m)
    (r : Fin d) (j : Fin (n r)) :
    alcovePointLabel hE hne m f ⟨r,ULift.up j⟩ =
      symbolValue (AlcoveLattice hE) m f.val (rowThreshold hE hne r j.val)-
        symbolValue (AlcoveLattice hE) m f.val (rowThreshold hE hne r (j.val+1)) := by
  have hcount : alcovePointLabel hE hne m f ⟨r,ULift.up j⟩ =
      (Finset.univ.filter fun s : Fin m =>
        (((alcovePointChain hE hne m f).val s).val r).val=j.val).card := by
    simp only [alcovePointLabel,finiteChainShift,Finsupp.finsetSum_apply,
      finiteRowExponent_apply,Finset.card_filter,Fin.ext_iff]
  rw [hcount,count_eq_count_ge_sub,
    rowThreshold_count hE hne m f r j.val,
    rowThreshold_count hE hne m f r (j.val+1)]

theorem rowThresholdValue_antitone (m : ℕ) (f : AlcovePoint hE m)
    (r : Fin d) {i j : ℕ} (hij : i≤j) :
    symbolValue (AlcoveLattice hE) m f.val (rowThreshold hE hne r j) ≤
      symbolValue (AlcoveLattice hE) m f.val (rowThreshold hE hne r i) := by
  rw [← rowThreshold_count hE hne m f r j, ← rowThreshold_count hE hne m f r i]
  apply Finset.card_le_card
  intro s hs
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hij.trans (Finset.mem_filter.mp hs).2⟩

theorem alcovePointLabel_degree (m : ℕ) (f : AlcovePoint hE m) :
    (alcovePointLabel hE hne m f).degree=m*d :=
  finiteChainShift_degree _

variable {m : ℕ}

lemma finiteChainCoefficient_not_contains_zero (w : FiniteMultichain n E m) :
    ¬ Contains (finiteChainCoefficientFamily n w) (0 : Exponent (FiniteVariable.{u} n)) := by
  rintro ⟨g,hg,hg0⟩
  obtain ⟨s,hs,hgs⟩ := Finset.mem_biUnion.mp hg
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hgs
  obtain ⟨r,hr,hprev⟩ := (Finset.mem_filter.mp hb).2
  have hh := hg0 ⟨r,ULift.up (b r)⟩
  simp only [Finsupp.tsub_apply,finiteRowExponent_apply,ite_true,
    if_neg (ne_of_gt hr),Nat.sub_zero,Finsupp.zero_apply] at hh
  omega

include hE in
theorem finiteChainShift_injective :
    Function.Injective (finiteChainShift.{u} n (E := E) (m := m)) := by
  intro w z he
  let iw : FiniteChainStandardIndex.{u} n E m :=
    ⟨w,0,finiteChainCoefficient_not_contains_zero w⟩
  let iz : FiniteChainStandardIndex.{u} n E m :=
    ⟨z,0,finiteChainCoefficient_not_contains_zero z⟩
  have hh : finiteChainIndexExponent iw = finiteChainIndexExponent iz := by
    simpa only [iw,iz,finiteChainIndexExponent,zero_add] using he
  exact congrArg Sigma.fst (finiteChainIndexExponent_injective hE hh)

/-- Distinct integer order-polytope vertices have distinct actual labels. -/
theorem alcovePointLabel_injective (m : ℕ) :
    Function.Injective (alcovePointLabel.{u} hE hne m) :=
  (finiteChainShift_injective hE).comp (alcovePointChainEquiv hE hne m).injective

theorem finitePowerGenerator_degree (m : ℕ) {a : Exponent (FiniteVariable.{u} n)}
    (ha : a ∈ exponentPowerFamily (finiteRowFamily n E) m) : a.degree=m*d := by
  induction m generalizing a with
  | zero =>
      have he : a=0 := by simpa only [exponentPowerFamily,Finset.mem_singleton] using ha
      simp only [he,map_zero,Nat.zero_mul]
  | succ m ih =>
      obtain ⟨⟨b,c⟩,hbc,rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨hb,hc⟩ := Finset.mem_product.mp hbc
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hc
      rw [map_add,ih hb,finiteRowExponent_degree,Nat.succ_mul]

theorem alcovePointLabel_mem_powerFamily (m : ℕ) (f : AlcovePoint hE m) :
    alcovePointLabel hE hne m f ∈ exponentPowerFamily (finiteRowFamily n E) m := by
  apply (exponentPowerFamily_image_list E (finiteRowExponent n) m _).mpr
  refine ⟨List.ofFn (alcovePointChain hE hne m f).val,List.length_ofFn,?_⟩
  exact (finiteChainShift_eq_list _).symm

/-- The vertex labels are exactly the minimal monomial generators of the
ordinary power, with no auxiliary generators or changes of polynomial ring. -/
theorem alcovePointLabel_family (m : ℕ) :
    Finset.univ.image (alcovePointLabel.{u} hE hne m) =
      exponentPowerFamily (finiteRowFamily n E) m := by
  ext a
  constructor
  · intro ha
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp ha
    exact alcovePointLabel_mem_powerFamily hE hne m f
  · intro ha
    obtain ⟨w,hw⟩ := finiteChainIndexExponent_surjective hE a ⟨a,ha,le_rfl⟩
    have hv : w.2.val=0 := by
      apply (Finsupp.degree_eq_zero_iff _).mp
      have hd := congrArg Finsupp.degree hw
      rw [finiteChainIndexExponent,map_add,finiteChainShift_degree,
        finitePowerGenerator_degree m ha] at hd
      omega
    refine Finset.mem_image.mpr ⟨alcoveChainPoint hE hne m w.1,Finset.mem_univ _,?_⟩
    change finiteChainShift n (alcovePointChain hE hne m (alcoveChainPoint hE hne m w.1))=a
    rw [alcovePointChain_chainPoint]
    simpa only [finiteChainIndexExponent,hv,zero_add] using hw

theorem alcovePointLabel_ideal {k : Type*} [CommSemiring k] (m : ℕ) :
    monomialIdeal k (Finset.univ.image (alcovePointLabel.{u} hE hne m)) =
      (finiteSublatticeIdeal n (k := k) E)^m := by
  rw [alcovePointLabel_family]
  exact finitePowerFamily_ideal (n := n) E m

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.AlcoveDivisorContraction -/
section

/-!
# The genuine divisor complexes of the sublattice cellular model

The displayed row-difference inequalities are identified with divisibility
by the actual vertex monomials. Their finite oriented augmented simplicial
complexes have explicit linear contractions over every commutative ring.
The number of coordinates is exactly the number of join-irreducibles.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice

open Classical CommAlg.Polymatroid FiniteDistributive IntegerDifferencePolytope

universe u

/-- Changing a finite enumeration does not change the literal oriented
face contraction; the finite-type structures are uniquely equal. -/
def faceContractionChangeFintype {V' R : Type*}
    [LinearOrder V'] [CommRing R] (F₀ F₁ : Fintype V') (K : Finset V' → Prop)
    (c : @SimplicialDomination.FaceContraction V' R F₀ inferInstance inferInstance K) :
    @SimplicialDomination.FaceContraction V' R F₁ inferInstance inferInstance K := by
  have h : F₀ = F₁ := Subsingleton.elim _ _
  cases h
  exact c

variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}
  (hE : finiteLatticeClosed n E) (hne : E.Nonempty)

abbrev AlcoveVertex (m : ℕ) := Vertex (I := AlcoveIrreducible hE) m

def alcoveVertices (m : ℕ) : Finset (AlcoveVertex hE m) := Finset.univ.filter Antitone

def alcoveFaces (m : ℕ) : Finset (AlcoveVertex hE m) → Prop :=
  IntegerAlcove.faces (coordinate m) (alcoveVertices hE m)

def alcoveVertexLabel (m : ℕ) (f : AlcoveVertex hE m) : Exponent (FiniteVariable.{u} n) :=
  if hf : Antitone f then alcovePointLabel hE hne m ⟨f,hf⟩ else 0

@[simp] theorem alcoveVertexLabel_point (m : ℕ) (f : AlcovePoint hE m) :
    alcoveVertexLabel hE hne m f.val = alcovePointLabel hE hne m f := by
  rw [alcoveVertexLabel,dif_pos f.property]

def alcoveDivisorVertices (m : ℕ) (b : Exponent (FiniteVariable.{u} n)) :
    Finset (AlcoveVertex hE m) :=
  (alcoveVertices hE m).filter fun f => alcoveVertexLabel hE hne m f ≤ b

def alcoveDivisorFaces (m : ℕ) (b : Exponent (FiniteVariable.{u} n))
    (F : Finset (AlcoveVertex hE m)) : Prop :=
  alcoveFaces hE m F ∧ ∀ f ∈ F, alcoveVertexLabel hE hne m f ≤ b

theorem alcoveDivisorFaces_eq (m : ℕ) (b : Exponent (FiniteVariable.{u} n)) :
    alcoveDivisorFaces hE hne m b =
      IntegerAlcove.faces (coordinate m) (alcoveDivisorVertices hE hne m b) := by
  funext F
  apply propext
  constructor
  · rintro ⟨hF,hb⟩
    exact ⟨fun f hf => Finset.mem_filter.mpr ⟨hF.1 hf,hb f hf⟩,hF.2⟩
  · intro hF
    exact ⟨⟨fun f hf => (Finset.mem_filter.mp (hF.1 hf)).1,hF.2⟩,
      fun f hf => (Finset.mem_filter.mp (hF.1 hf)).2⟩

theorem symbolValue_cast (m : ℕ) (f : AlcoveVertex hE m)
    (c : CoordinateSymbol (AlcoveIrreducible hE)) :
    (symbolValue (AlcoveLattice hE) m f c : ℤ) = IntegerSymbolPolytope.value m f c := by
  cases c <;> rfl

theorem alcovePointLabel_le_iff (m : ℕ) (f : AlcovePoint hE m)
    (b : Exponent (FiniteVariable.{u} n)) (r : Fin d) (j : Fin (n r)) :
    alcovePointLabel hE hne m f ⟨r,ULift.up j⟩ ≤ b ⟨r,ULift.up j⟩ ↔
      IntegerSymbolPolytope.value m f.val (rowThreshold hE hne r j.val)-
        IntegerSymbolPolytope.value m f.val (rowThreshold hE hne r (j.val+1)) ≤
          (b ⟨r,ULift.up j⟩ : ℤ) := by
  have hmono := rowThresholdValue_antitone hE hne m f r (Nat.le_succ j.val)
  have he : (alcovePointLabel hE hne m f ⟨r,ULift.up j⟩ : ℤ) =
      IntegerSymbolPolytope.value m f.val (rowThreshold hE hne r j.val)-
        IntegerSymbolPolytope.value m f.val (rowThreshold hE hne r (j.val+1)) := by
    rw [alcovePointLabel_apply,Int.natCast_sub hmono,symbolValue_cast,symbolValue_cast]
  rw [← he]
  exact_mod_cast (Iff.rfl : alcovePointLabel hE hne m f ⟨r,ULift.up j⟩ ≤ b ⟨r,ULift.up j⟩ ↔ _)

def alcoveOrderSystem : IntegerSymbolPolytope.System (AlcoveIrreducible hE) :=
  {z | ∃ p q : AlcoveIrreducible hE, p ≤ q ∧ z=(.at q,.at p,0)}

def alcoveLabelSystem (b : Exponent (FiniteVariable.{u} n)) :
    IntegerSymbolPolytope.System (AlcoveIrreducible hE) :=
  {z | ∃ x : FiniteVariable.{u} n,
    z=(rowThreshold hE hne x.1 x.2.down.val,
      rowThreshold hE hne x.1 (x.2.down.val+1),(b x : ℤ))}

def alcoveDivisorSystem (b : Exponent (FiniteVariable.{u} n)) :
    IntegerSymbolPolytope.System (AlcoveIrreducible hE) :=
  alcoveOrderSystem hE ∪ alcoveLabelSystem hE hne b

theorem alcoveOrderSystem_allowed (m : ℕ) (f : AlcoveVertex hE m) :
    IntegerSymbolPolytope.Allowed m (alcoveOrderSystem hE) f ↔ Antitone f := by
  constructor
  · intro h p q hpq
    have hh := h (.at q) (.at p) 0 ⟨p,q,hpq,rfl⟩
    change (f q).val ≤ (f p).val
    change ((f q).val : ℤ)-((f p).val : ℤ)≤0 at hh
    omega
  · intro h c e b hb
    obtain ⟨p,q,hpq,he⟩ := hb
    cases he
    have hh := h hpq
    change ((f q).val : ℤ)-((f p).val : ℤ)≤0
    change (f q).val≤(f p).val at hh
    omega

theorem alcoveDivisorSystem_allowed (m : ℕ) (b : Exponent (FiniteVariable.{u} n))
    (f : AlcoveVertex hE m) :
    IntegerSymbolPolytope.Allowed m (alcoveDivisorSystem hE hne b) f ↔
      Antitone f ∧ alcoveVertexLabel hE hne m f ≤ b := by
  constructor
  · intro h
    have hf : Antitone f := (alcoveOrderSystem_allowed hE m f).mp
      (fun c e a ha => h c e a (Or.inl ha))
    refine ⟨hf,?_⟩
    intro x
    obtain ⟨r,⟨j⟩⟩ := x
    rw [alcoveVertexLabel_point hE hne m ⟨f,hf⟩]
    apply (alcovePointLabel_le_iff hE hne m ⟨f,hf⟩ b r j).mpr
    exact h _ _ _ (Or.inr ⟨⟨r,ULift.up j⟩,rfl⟩)
  · rintro ⟨hf,hb⟩ c e a ha
    rcases ha with ha | ha
    · exact (alcoveOrderSystem_allowed hE m f).mpr hf c e a ha
    · obtain ⟨⟨r,⟨j⟩⟩,he⟩ := ha
      cases he
      apply (alcovePointLabel_le_iff hE hne m ⟨f,hf⟩ b r j).mp
      simpa only [alcoveVertexLabel_point hE hne m ⟨f,hf⟩] using hb ⟨r,ULift.up j⟩

theorem alcoveDivisorVertices_eq_system (m : ℕ) (b : Exponent (FiniteVariable.{u} n)) :
    alcoveDivisorVertices hE hne m b =
      IntegerSymbolPolytope.vertices m (alcoveDivisorSystem hE hne b) := by
  ext f
  simp only [alcoveDivisorVertices,alcoveVertices,Finset.mem_filter,Finset.mem_univ,
    true_and,IntegerSymbolPolytope.mem_vertices,alcoveDivisorSystem_allowed]

/-- Actual contraction of every nonempty genuine divisor subcomplex, valid
over every commutative coefficient ring, including the zero ring. -/
def alcoveDivisorContraction {k : Type*} [CommRing k] (m : ℕ)
    (b : Exponent (FiniteVariable.{u} n))
    (hb : (alcoveDivisorVertices hE hne m b).Nonempty) :
    SimplicialDomination.FaceContraction (k := k) (alcoveDivisorFaces hE hne m b) := by
  rw [alcoveDivisorVertices_eq_system] at hb
  rw [alcoveDivisorFaces_eq,alcoveDivisorVertices_eq_system]
  let c := IntegerSymbolPolytope.faceContraction (k := k) m
    (alcoveDivisorSystem hE hne b) hb
  exact faceContractionChangeFintype (R := k) _
    (inferInstance : Fintype (AlcoveVertex hE m)) _ c

theorem alcoveDivisor_exact {k : Type*} [CommRing k] (m : ℕ)
    (b : Exponent (FiniteVariable.{u} n))
    (hb : (alcoveDivisorVertices hE hne m b).Nonempty) (p : ℕ) :
    CommAlg.Simplicial.ExactIn (k := k) (alcoveDivisorFaces hE hne m b) p :=
  (alcoveDivisorContraction hE hne m b hb).exactIn p

theorem alcoveFaces_card_le (m : ℕ) {F : Finset (AlcoveVertex hE m)}
    (hF : alcoveFaces hE m F) : F.card ≤ finiteLatticeHeight hE hne+1 := by
  exact IntegerAlcove.face_card_le (coordinate m) (coordinate_injective m) hF

theorem alcoveFaces_downward (m : ℕ) : CommAlg.Simplicial.Downward (alcoveFaces hE m) :=
  IntegerAlcove.faces_downward _ _

theorem alcoveSingleton_face_iff (m : ℕ) (f : AlcoveVertex hE m) :
    alcoveFaces hE m {f} ↔ f ∈ alcoveVertices hE m := by
  constructor
  · intro h
    exact h.1 (Finset.mem_singleton_self f)
  · intro hf
    refine ⟨Finset.singleton_subset_iff.mpr hf,?_,?_⟩
    · intro v hv w hw
      have hv' := Finset.mem_singleton.mp hv
      have hw' := Finset.mem_singleton.mp hw
      subst v
      subst w
      exact Or.inl le_rfl
    · intro v hv w hw p
      have hv' := Finset.mem_singleton.mp hv
      have hw' := Finset.mem_singleton.mp hw
      subst v
      subst w
      omega

theorem alcoveVertexLabel_family (m : ℕ) :
    (alcoveVertices hE m).image (alcoveVertexLabel.{u} hE hne m) =
      exponentPowerFamily (finiteRowFamily n E) m := by
  rw [← alcovePointLabel_family hE hne m]
  ext a
  constructor
  · intro ha
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp ha
    have hanti : Antitone f := (Finset.mem_filter.mp hf).2
    exact Finset.mem_image.mpr ⟨⟨f,hanti⟩,Finset.mem_univ _,
      (alcoveVertexLabel_point hE hne m ⟨f,hanti⟩).symm⟩
  · intro ha
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_image.mpr ⟨f.val,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,f.property⟩,
      alcoveVertexLabel_point hE hne m f⟩

theorem alcoveDivisor_nonempty_iff (m : ℕ) (b : Exponent (FiniteVariable.{u} n)) :
    (alcoveDivisorVertices hE hne m b).Nonempty ↔
      Contains (exponentPowerFamily (finiteRowFamily n E) m) b := by
  rw [← alcoveVertexLabel_family hE hne m]
  constructor
  · rintro ⟨f,hf⟩
    obtain ⟨hf,hb⟩ := Finset.mem_filter.mp hf
    exact ⟨_,Finset.mem_image.mpr ⟨f,hf,rfl⟩,hb⟩
  · rintro ⟨a,ha,hab⟩
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp ha
    exact ⟨f,Finset.mem_filter.mpr ⟨hf,hab⟩⟩

theorem alcoveVertexLabel_ideal {k : Type*} [CommSemiring k] (m : ℕ) :
    monomialIdeal k ((alcoveVertices hE m).image (alcoveVertexLabel.{u} hE hne m)) =
      (finiteSublatticeIdeal n (k := k) E)^m := by
  rw [alcoveVertexLabel_family]
  exact finitePowerFamily_ideal (n := n) E m

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.LabelledSimplicialComplex -/
section

/-! # The actual polynomial complex of a monomial-labelled simplicial complex

The coefficient from F to F\{v} is the exterior incidence sign times
the quotient of their least-common-multiple labels. The differential is
polynomial-linear. Its square is proved zero by embedding it in the
literal exterior boundary, multiplying the F coordinate by its label.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.LabelledSimplicial

open Classical CommAlg MvPolynomial
open scoped BigOperators

universe u v w
variable {k : Type u} {X : Type w} {V : Type v} [CommRing k] [Fintype V] [LinearOrder V]
  [Fintype X] (K : Finset V → Prop) (hK : Simplicial.Downward K)
  (u : V → X →₀ ℕ)

abbrev PolynomialRing := MvPolynomial X k
abbrev Face := {F : Finset V // K F}
abbrev FreeModule := Face K →₀ PolynomialRing (k:=k) (X:=X)

def faceLabel (F : Finset V) : X →₀ ℕ := F.sup u

theorem faceLabel_mono {F G : Finset V} (h : F⊆G) : faceLabel u F≤faceLabel u G :=
  Finset.sup_mono h

@[simp] theorem faceLabel_empty : faceLabel u ∅=0 := by
  simp only [faceLabel, Finset.sup_empty]
  rfl
@[simp] theorem faceLabel_singleton (v : V) : faceLabel u {v}=u v := by simp [faceLabel]

def eraseFace (F : Face K) (v : V) : Face K :=
  ⟨F.val.erase v,hK (Finset.erase_subset v F.val) F.property⟩

def freeBasis : Module.Basis (Face K) (PolynomialRing (k:=k) (X:=X))
    (FreeModule (k:=k) (X:=X) K) := Finsupp.basisSingleOne

@[simp] theorem freeBasis_apply (F : Face K) :
    freeBasis (k:=k) (X:=X) K F=Finsupp.single F 1 := rfl

/-- The polynomial-linear differential with the literal signed lcm quotients. -/
def differential : Module.End (PolynomialRing (k:=k) (X:=X)) (FreeModule (k:=k) (X:=X) K) :=
  (freeBasis (k:=k) (X:=X) K).constr (PolynomialRing (k:=k) (X:=X))
    (fun F => ∑ v : {v // v∈F.val},
    TauCeti.ExteriorAlgebra.basisEraseSign v.val F.val •
      (monomial (faceLabel u F.val-faceLabel u (F.val.erase v.val)) (1:k) •
        freeBasis K (eraseFace K hK F v.val)))

@[simp] theorem differential_basis (F : Face K) :
    differential K hK u (freeBasis (k:=k) K F)=
      ∑ v : {v // v∈F.val},TauCeti.ExteriorAlgebra.basisEraseSign v.val F.val •
        (monomial (faceLabel u F.val-faceLabel u (F.val.erase v.val)) (1:k) •
          freeBasis K (eraseFace K hK F v.val)) :=
  Module.Basis.constr_basis _ _ _ _

def labelledEmbedding : FreeModule (k:=k) (X:=X) K →ₗ[PolynomialRing (k:=k) (X:=X)]
    Simplicial.Ambient V (PolynomialRing (k:=k) (X:=X)) :=
  (freeBasis (k:=k) (X:=X) K).constr (PolynomialRing (k:=k) (X:=X)) (fun F =>
    monomial (faceLabel u F.val) (1:k) • Simplicial.basis F.val)

@[simp] theorem labelledEmbedding_basis (F : Face K) :
    labelledEmbedding (k:=k) K u (freeBasis K F)=
      monomial (faceLabel u F.val) (1:k) • Simplicial.basis F.val :=
  Module.Basis.constr_basis _ _ _ _

theorem labelledEmbedding_coefficient (F : Face K) (z : FreeModule (k:=k) (X:=X) K) :
    Simplicial.basis.repr (labelledEmbedding K u z) F.val=
      z F * monomial (faceLabel u F.val) 1 := by
  have he : (Simplicial.basis.coord F.val).comp (labelledEmbedding (k:=k) K u)=
      (LinearMap.mulRight _ (monomial (faceLabel u F.val) (1:k))).comp (Finsupp.lapply F) := by
    apply (freeBasis K).ext
    intro G
    simp only [LinearMap.comp_apply,Module.Basis.coord_apply]
    rw [labelledEmbedding_basis]
    simp only [
      map_smul,Finsupp.smul_apply,Module.Basis.repr_self,Finsupp.single_apply,
      freeBasis_apply,Finsupp.lapply_apply,LinearMap.mulRight_apply,smul_eq_mul]
    by_cases h : G=F
    · subst G
      simp
    · have hval : G.val≠F.val := fun hh => h (Subtype.ext hh)
      simp only [if_neg h,if_neg hval,mul_zero,zero_mul]
  exact LinearMap.congr_fun he z

theorem labelledEmbedding_injective : Function.Injective (labelledEmbedding (k:=k) K u) := by
  intro z w h
  apply Finsupp.ext
  intro F
  have hh := congrArg (fun y => Simplicial.basis.repr y F.val) h
  rw [labelledEmbedding_coefficient,labelledEmbedding_coefficient] at hh
  exact MvPolynomial.monomial_one_mul_cancel_right_iff.mp hh

theorem labelledEmbedding_differential (z : FreeModule (k:=k) (X:=X) K) :
    labelledEmbedding K u (differential K hK u z)=
      Simplicial.boundary (labelledEmbedding K u z) := by
  have he : (labelledEmbedding (k:=k) K u).comp (differential K hK u)=
      Simplicial.boundary.comp (labelledEmbedding K u) := by
    apply (freeBasis K).ext
    intro F
    simp only [LinearMap.comp_apply,differential_basis,map_sum,map_zsmul_unit,map_smul,
      labelledEmbedding_basis,Sublattice.face_boundary_basis_sum,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro v _
    rw [smul_smul,monomial_mul_monomial,one_mul]
    dsimp only [eraseFace]
    rw [tsub_add_cancel_of_le (faceLabel_mono u (Finset.erase_subset v.val F.val))]
    exact smul_comm _ _ _
  exact LinearMap.congr_fun he z

theorem differential_square : (differential (k:=k) K hK u).comp (differential K hK u)=0 := by
  apply LinearMap.ext
  intro z
  change differential K hK u (differential K hK u z) = 0
  apply labelledEmbedding_injective K u
  rw [map_zero,labelledEmbedding_differential,labelledEmbedding_differential,
    Simplicial.boundary_boundary]

def chainPiece (i : ℕ) : Submodule (PolynomialRing (k:=k) (X:=X))
    (FreeModule (k:=k) (X:=X) K) := Grading.Piece (freeBasis K) (fun F => F.val.card) i

def chainBasis (i : ℕ) : Module.Basis {F : Face K // F.val.card=i}
    (PolynomialRing (k:=k) (X:=X)) (chainPiece (k:=k) (X:=X) K i) :=
  Grading.restrictedBasis (freeBasis (k:=k) (X:=X) K) (fun F => F.val.card=i)

theorem differential_lowers (i : ℕ) (z : FreeModule (k:=k) (X:=X) K)
    (hz : z∈chainPiece K (i+1)) : differential K hK u z∈chainPiece K i := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨F,hF,rfl⟩ := hz
      change F.val.card = i + 1 at hF
      rw [differential_basis]
      apply Submodule.sum_mem
      intro v _
      apply Submodule.smul_of_tower_mem
      apply Submodule.smul_mem
      exact Submodule.subset_span ⟨eraseFace K hK F v.val,
        (Finset.card_erase_of_mem v.property).trans (by omega),rfl⟩
  | zero => simpa only [map_zero] using (chainPiece (k:=k) (X:=X) K i).zero_mem
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [map_smul] using Submodule.smul_mem _ c ih

def coefficientBasis : Module.Basis (Σ F : Face K,X →₀ ℕ) k
    (FreeModule (k:=k) (X:=X) K) :=
  Finsupp.basis (fun _ : Face K => MvPolynomial.basisMonomials X k)

@[simp] theorem coefficientBasis_apply (F : Face K) (a : X →₀ ℕ) :
    coefficientBasis (k:=k) K ⟨F,a⟩=Finsupp.single F (monomial a 1) := by
  simp only [coefficientBasis,Finsupp.coe_basis,MvPolynomial.coe_basisMonomials]

theorem coefficientBasis_eq_smul (F : Face K) (a : X →₀ ℕ) :
    coefficientBasis (k:=k) K ⟨F,a⟩=monomial a (1:k) • freeBasis K F := by
  rw [coefficientBasis_apply,freeBasis_apply,Finsupp.smul_single,smul_eq_mul,mul_one]

def fineDegree (a : Σ F : Face K,X →₀ ℕ) : X →₀ ℕ := a.2+faceLabel u a.1.val

def finePiece (b : X →₀ ℕ) : Submodule k (FreeModule (k:=k) (X:=X) K) :=
  Grading.Piece (coefficientBasis K) (fineDegree K u) b

def fineProjection (b : X →₀ ℕ) : Module.End k (FreeModule (k:=k) (X:=X) K) :=
  Grading.projection (coefficientBasis K) (fineDegree K u) b

def erasedCoefficientIndex (a : Σ F : Face K,X →₀ ℕ) (v : V) :
    Σ F : Face K,X →₀ ℕ :=
  ⟨eraseFace K hK a.1 v,a.2+(faceLabel u a.1.val-faceLabel u (a.1.val.erase v))⟩

theorem fineDegree_erase (a : Σ F : Face K,X →₀ ℕ) (v : V) :
    fineDegree K u (erasedCoefficientIndex K hK u a v)=fineDegree K u a := by
  dsimp [fineDegree,erasedCoefficientIndex,eraseFace]
  rw [add_assoc,tsub_add_cancel_of_le (faceLabel_mono u (Finset.erase_subset v a.1.val))]

theorem differential_coefficientBasis (a : Σ F : Face K,X →₀ ℕ) :
    differential K hK u (coefficientBasis (k:=k) K a)=
      ∑ v : {v // v∈a.1.val},TauCeti.ExteriorAlgebra.basisEraseSign v.val a.1.val •
        coefficientBasis K (erasedCoefficientIndex K hK u a v.val) := by
  rw [coefficientBasis_eq_smul,map_smul,differential_basis,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [smul_comm,smul_smul,monomial_mul_monomial,one_mul,
    coefficientBasis_eq_smul]
  rfl

theorem differential_fine (b : X →₀ ℕ) (z : FreeModule (k:=k) (X:=X) K)
    (hz : z∈finePiece K u b) : differential K hK u z∈finePiece K u b := by
  apply map_mem_piece_of_basis (coefficientBasis K) (coefficientBasis K)
    (fineDegree K u) (fineDegree K u) ((differential K hK u).restrictScalars k) _ b hz
  intro a
  simp only [LinearMap.restrictScalars_apply]
  rw [differential_coefficientBasis]
  apply Submodule.sum_mem
  intro v _
  exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span
    ⟨erasedCoefficientIndex K hK u a v.val,fineDegree_erase K hK u a v.val,rfl⟩)

theorem differential_fineProjection (b : X →₀ ℕ) (z : FreeModule (k:=k) (X:=X) K) :
    differential K hK u (fineProjection K u b z)=
      fineProjection K u b (differential K hK u z) := by
  have he : ((differential (k:=k) K hK u).restrictScalars k).comp (fineProjection K u b)=
      (fineProjection K u b).comp ((differential K hK u).restrictScalars k) := by
    apply (coefficientBasis K).ext
    intro a
    simp only [LinearMap.comp_apply,LinearMap.restrictScalars_apply,
      fineProjection,Grading.projection_basis,
      differential_coefficientBasis,map_sum,map_zsmul_unit]
    by_cases ha : fineDegree K u a=b
    · simp only [if_pos ha,differential_coefficientBasis,Grading.projection_basis,
        fineDegree_erase,if_pos ha]
    · simp only [if_neg ha,map_zero,Grading.projection_basis,fineDegree_erase,
        if_neg ha,smul_zero,Finset.sum_const_zero]
  exact LinearMap.congr_fun he z

end FourPapers.LabelledSimplicial

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.BasisEquivalenceGrading -/
section

/-! # Actual linear equivalences preserving basis degree labels

All statements retain the LinearEquiv head. Concrete applications therefore
need not convert a large basis equivalence to its underlying LinearMap while
proving the same pointwise basis identities.
-/

section
set_option autoImplicit false
noncomputable section

namespace FourPapers
open CommAlg

variable {R X Y I J Γ : Type*} [CommRing R]
  [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
  (b : Module.Basis I R X) (c : Module.Basis J R Y)
  (degree : I → Γ) (degree' : J → Γ) (e : X ≃ₗ[R] Y)

/-- Pointwise degree preservation on a basis preserves its actual span. -/
theorem linearEquiv_mem_piece_of_basis
    (he : ∀ i, e (b i) ∈ Grading.Piece c degree' (degree i))
    (a : Γ) {x : X} (hx : x ∈ Grading.Piece b degree a) :
    e x ∈ Grading.Piece c degree' a := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      change degree i = a at hi
      rw [← hi]
      exact he i
  | zero =>
      rw [e.map_zero]
      exact (Grading.Piece c degree' a).zero_mem
  | add x y hx hy ihx ihy =>
      rw [e.map_add]
      exact (Grading.Piece c degree' a).add_mem ihx ihy
  | smul r x hx ih =>
      rw [e.map_smul]
      exact (Grading.Piece c degree' a).smul_mem r ih

/-- A specified basis equivalence transports each degree component exactly.
The index equivalence and its pointwise degree equation remain explicit. -/
theorem linearEquiv_mem_piece_iff_of_basis (σ : I ≃ J)
    (he : ∀ i, e (b i) = c (σ i))
    (hdegree : ∀ i, degree' (σ i) = degree i) (a : Γ) (x : X) :
    e x ∈ Grading.Piece c degree' a ↔ x ∈ Grading.Piece b degree a := by
  have hs (j : J) : e.symm (c j) = b (σ.symm j) := by
    apply e.injective
    rw [e.apply_symm_apply, he, σ.apply_symm_apply]
  constructor
  · intro hx
    have hback : ∀ j, e.symm (c j) ∈ Grading.Piece b degree (degree' j) := by
      intro j
      rw [hs]
      have hdeg : degree (σ.symm j) = degree' j := by
        rw [← hdegree (σ.symm j), σ.apply_symm_apply]
      rw [← hdeg]
      exact Grading.basis_mem_piece b degree (σ.symm j)
    have hh := linearEquiv_mem_piece_of_basis (R:=R) (X:=Y) (Y:=X)
      c b degree' degree e.symm hback a hx
    simpa only [e.symm_apply_apply] using hh
  · intro hx
    apply linearEquiv_mem_piece_of_basis (R:=R) (X:=X) (Y:=Y)
      b c degree degree' e _ a hx
    intro i
    rw [he, ← hdegree i]
    exact Grading.basis_mem_piece c degree' (σ i)

end FourPapers

end
end
end


end
