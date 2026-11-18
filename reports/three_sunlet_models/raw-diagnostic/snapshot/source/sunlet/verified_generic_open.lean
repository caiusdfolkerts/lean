module
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Data.Fintype.Perm
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import sunlet.verified_field_core

@[expose] public section
noncomputable section
set_option Elab.async false

#check "SUNLET_GENERIC_OPEN_IMPORTS_READY"



/-! Independent diagonal variables adjoined to the off-diagonal parameter field, with the exact displayed coordinate formula. -/

noncomputable section

namespace Sunlet.RationalBaseChange

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {k E O J : Type*} [Field k] [Field E] [Algebra k E]
  [DecidableEq J] (q : O → E) (target : O → J)

abbrev ExtendedField := FractionRing (MvPolynomial J E)

def diagonal (j : J) : ExtendedField (E := E) (J := J) :=
  algebraMap (MvPolynomial J E) _ (MvPolynomial.X j)

theorem diagonal_ne_zero (j : J) : diagonal (E := E) j ≠ 0 := by
  intro h
  apply MvPolynomial.X_ne_zero (R := E) j
  apply IsFractionRing.injective (MvPolynomial J E) (ExtendedField (E := E) (J := J))
  simpa only [diagonal, map_zero] using h

def coordinates : J ⊕ O → ExtendedField (E := E) (J := J)
  | .inl j => diagonal j
  | .inr i => diagonal (target i) * algebraMap E _ (q i)

abbrev ImageField := IntermediateField.adjoin k (Set.range (coordinates q target))

end Sunlet.RationalBaseChange
end

section GenericSource_ArbitraryAmbientEmbeddings

namespace Sunlet.GeneratedFieldActions

variable {k E A O : Type*} [Field k] [Field E] [Field A]
  [Algebra k E] [Algebra k A]

theorem eq_on_adjoin (q : O → E) (φ ψ : E →ₐ[k] A)
    (h : ∀ i, φ (q i) = ψ (q i))
    (x : IntermediateField.adjoin k (Set.range q)) : φ x.val = ψ x.val := by
  refine IntermediateField.adjoin_induction k (motive := fun x _ => φ x = ψ x)
    ?_ ?_ ?_ ?_ ?_ x.property
  · rintro _ ⟨i, rfl⟩
    exact h i
  · intro a
    rw [φ.commutes, ψ.commutes]
  · intro x y _ _ hx hy
    simp [hx, hy]
  · intro x _ hx
    simp [hx]
  · intro x y _ _ hx hy
    simp [hx, hy]

end Sunlet.GeneratedFieldActions

namespace Sunlet.ToricPairAlgebra

variable {k Ω ι A : Type*} [Field k] [CharZero k]
  [Fintype Ω] [Fintype ι] [DecidableEq Ω] [DecidableEq ι]
  (o : Ω) (π : ι → Equiv.Perm Ω)
  [Field A] [CharZero A] [Algebra k A]
  [Algebra (FunctionField (k := k) (ι := ι) o) A]
  [IsScalarTower k (FunctionField (k := k) (ι := ι) o) A]

theorem unordered_under_embedding_arbitrary_ambient
    (W : SparseWitness (k := k) o π)
    (hmoves : ∀ a, π a o ≠ o)
    (hdim : 2 < Fintype.card (NormalizedVariations.Index ι Ω o))
    (ψ : FunctionField (k := k) (ι := ι) o →ₐ[k] A)
    (hcoord : ∀ ax,
      algebraMap (FunctionField (k := k) (ι := ι) o) A (genericCoordinates o π ax) =
        ψ (genericCoordinates o π ax)) :
    ((fun ax => ψ (genericPoint o π false ax)) =
        (fun ax => algebraMap (FunctionField (k := k) (ι := ι) o) A (genericPoint o π false ax)) ∧
      (fun ax => ψ (genericPoint o π true ax)) =
        (fun ax => algebraMap (FunctionField (k := k) (ι := ι) o) A (genericPoint o π true ax))) ∨
    ((fun ax => ψ (genericPoint o π false ax)) =
        (fun ax => algebraMap (FunctionField (k := k) (ι := ι) o) A (genericPoint o π true ax)) ∧
      (fun ax => ψ (genericPoint o π true ax)) =
        (fun ax => algebraMap (FunctionField (k := k) (ι := ι) o) A (genericPoint o π false ax))) := by
  let E := FunctionField (k := k) (ι := ι) o
  let F := JacobianFinite.generatedField (genericCoordinates (k := k) o π)
  letI : Module.Finite F E :=
    (generic_finite_separable o π (W.A : Set ι) (W.B : Set ι)
      W.disjoint hmoves W.Atwo W.Btwo W.Atrans W.Btrans).1
  let ψF : E →ₐ[F] A :=
    { __ := ψ.toRingHom
      commutes' x := (GeneratedFieldActions.eq_on_adjoin (genericCoordinates o π)
        (canonical (k := k) (F := A) (ι := ι) o) ψ hcoord x).symm }
  have halg : ∀ x ∈ Set.range ψ, IsIntegral E x := by
    rintro _ ⟨x, rfl⟩
    have hx : IsIntegral F (ψF x) := (Algebra.IsIntegral.isIntegral x).map ψF
    exact (hx.isAlgebraic.extendScalars (algebraMap F E).injective).isIntegral
  let B := IntermediateField.adjoin E (Set.range ψ)
  letI : Algebra.IsAlgebraic E B := IntermediateField.isAlgebraic_adjoin halg
  let ψB : E →ₐ[k] B :=
    { toFun x := ⟨ψ x, IntermediateField.subset_adjoin E (Set.range ψ) ⟨x, rfl⟩⟩
      map_zero' := Subtype.ext ψ.map_zero
      map_one' := Subtype.ext ψ.map_one
      map_add' x y := Subtype.ext (ψ.map_add x y)
      map_mul' x y := Subtype.ext (ψ.map_mul x y)
      commutes' a := Subtype.ext (ψ.commutes a) }
  have hb : ∀ ax, algebraMap E B (genericCoordinates o π ax) =
      ψB (genericCoordinates o π ax) := by
    intro ax
    apply Subtype.ext
    exact hcoord ax
  have hu := unordered_under_embedding o π W hmoves hdim ψB hb
  rcases hu with ⟨hf, ht⟩ | ⟨hf, ht⟩
  · left
    constructor
    · funext ax
      exact congrArg Subtype.val (congrFun hf ax)
    · funext ax
      exact congrArg Subtype.val (congrFun ht ax)
  · right
    constructor
    · funext ax
      exact congrArg Subtype.val (congrFun hf ax)
    · funext ax
      exact congrArg Subtype.val (congrFun ht ax)

end Sunlet.ToricPairAlgebra

end GenericSource_ArbitraryAmbientEmbeddings

#check "SUNLET_ArbitraryAmbientEmbeddings_READY"


section GenericSource_EmbeddingFixedField

namespace Sunlet.EmbeddingFixedField

variable {F E : Type*} [Field F] [Field E] [CharZero F] [Algebra F E]
  [Algebra.IsAlgebraic F E]

theorem mem_range_of_embeddings (x : E)
    (hx : ∀ ψ : E →ₐ[F] AlgebraicClosure E,
      ψ x = algebraMap E (AlgebraicClosure E) x) :
    x ∈ Set.range (algebraMap F E) := by
  let A := AlgebraicClosure E
  letI : Algebra.IsAlgebraic F A := Algebra.IsAlgebraic.trans F E A
  letI : IsAlgClosure F A := (isAlgClosure_iff F A).mpr ⟨inferInstance, inferInstance⟩
  letI : IsGalois F A := ⟨⟩
  have hf : algebraMap E A x ∈ Set.range (algebraMap F A) := by
    apply (InfiniteGalois.mem_range_algebraMap_iff_fixed _).mpr
    intro σ
    exact hx (σ.toAlgHom.comp (IsScalarTower.toAlgHom F E A))
  obtain ⟨a, ha⟩ := hf
  refine ⟨a, (algebraMap E A).injective ?_⟩
  rw [← IsScalarTower.algebraMap_apply F E A]
  exact ha

end Sunlet.EmbeddingFixedField

namespace Sunlet.ToricPairAlgebra

variable {k Ω ι : Type*} [Field k] [CharZero k]
  [Fintype Ω] [Fintype ι] [DecidableEq Ω] [DecidableEq ι]
  (o : Ω) (π : ι → Equiv.Perm Ω)

/-- Products of component differences are rational in the literal sum
coordinates over the original ground field, including the rational field. -/
theorem differenceProduct_mem_generatedField
    (W : SparseWitness (k := k) o π)
    (hmoves : ∀ a, π a o ≠ o)
    (hdim : 2 < Fintype.card (NormalizedVariations.Index ι Ω o))
    (i j : ι × Ω) :
    (genericPoint (k := k) o π false i - genericPoint o π true i) *
        (genericPoint o π false j - genericPoint o π true j) ∈
      JacobianFinite.generatedField (genericCoordinates o π) := by
  let E := FunctionField (k := k) (ι := ι) o
  let F := JacobianFinite.generatedField (genericCoordinates (k := k) o π)
  let A := AlgebraicClosure E
  letI : Module.Finite F E :=
    (generic_finite_separable o π (W.A : Set ι) (W.B : Set ι)
      W.disjoint hmoves W.Atwo W.Btwo W.Atrans W.Btrans).1
  have hf : ∀ ψ : E →ₐ[F] A,
      ψ ((genericPoint o π false i - genericPoint o π true i) *
        (genericPoint o π false j - genericPoint o π true j)) =
      algebraMap E A ((genericPoint o π false i - genericPoint o π true i) *
        (genericPoint o π false j - genericPoint o π true j)) := by
    intro ψ
    have hc : ∀ ax, algebraMap E A (genericCoordinates o π ax) =
        (ψ.restrictScalars k) (genericCoordinates o π ax) := by
      intro ax
      let q : F := ⟨genericCoordinates o π ax,
        JacobianFinite.coordinate_mem_generatedField _ ax⟩
      exact (ψ.commutes q).symm
    have hu := unordered_under_embedding o π W hmoves hdim (ψ.restrictScalars k) hc
    simp only [map_mul, map_sub]
    rcases hu with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · simp only [AlgHom.restrictScalars_apply] at h0 h1
      rw [congrFun h0 i, congrFun h1 i, congrFun h0 j, congrFun h1 j]
    · simp only [AlgHom.restrictScalars_apply] at h0 h1
      rw [congrFun h0 i, congrFun h1 i, congrFun h0 j, congrFun h1 j]
      ring
  obtain ⟨a, ha⟩ := EmbeddingFixedField.mem_range_of_embeddings _ hf
  exact ha ▸ a.property

end Sunlet.ToricPairAlgebra

end GenericSource_EmbeddingFixedField

#check "SUNLET_EmbeddingFixedField_READY"


section GenericSource_PolynomialClosureProduct

namespace Sunlet.PolynomialClosureProduct

variable {K O : Type*} [Field K]

def closure (S : Set (O → K)) : Set (O → K) :=
  MvPolynomial.zeroLocus K (MvPolynomial.vanishingIdeal K S)

def pair (x y : O → K) : Bool × O → K := fun bi => if bi.1 then y bi.2 else x bi.2

def fixLeft (x : O → K) : MvPolynomial (Bool × O) K →ₐ[K] MvPolynomial O K :=
  MvPolynomial.aeval (fun bi => if bi.1 then MvPolynomial.X bi.2 else MvPolynomial.C (x bi.2))

def fixRight (y : O → K) : MvPolynomial (Bool × O) K →ₐ[K] MvPolynomial O K :=
  MvPolynomial.aeval (fun bi => if bi.1 then MvPolynomial.C (y bi.2) else MvPolynomial.X bi.2)

theorem aeval_fixLeft (x y : O → K) (P : MvPolynomial (Bool × O) K) :
    MvPolynomial.aeval y (fixLeft x P) = MvPolynomial.aeval (pair x y) P := by
  have hh : (MvPolynomial.aeval y).comp (fixLeft x) = MvPolynomial.aeval (pair x y) := by
    ext bi
    rcases bi with ⟨b, i⟩
    cases b <;> simp [fixLeft, pair]
  exact AlgHom.congr_fun hh P

theorem aeval_fixRight (x y : O → K) (P : MvPolynomial (Bool × O) K) :
    MvPolynomial.aeval x (fixRight y P) = MvPolynomial.aeval (pair x y) P := by
  have hh : (MvPolynomial.aeval x).comp (fixRight y) = MvPolynomial.aeval (pair x y) := by
    ext bi
    rcases bi with ⟨b, i⟩
    cases b <;> simp [fixRight, pair]
  exact AlgHom.congr_fun hh P

/-- This explicitly includes all boundary points of both closures. -/
theorem identity_on_closure_pairs (S : Set (O → K))
    (P : MvPolynomial (Bool × O) K)
    (hP : ∀ x ∈ S, ∀ y ∈ S, MvPolynomial.aeval (pair x y) P = 0) :
    ∀ x ∈ closure S, ∀ y ∈ closure S,
      MvPolynomial.aeval (pair x y) P = 0 := by
  have hfirst : ∀ x ∈ S, ∀ y ∈ closure S,
      MvPolynomial.aeval (pair x y) P = 0 := by
    intro x hx y hy
    have hf : fixLeft x P ∈ MvPolynomial.vanishingIdeal K S := by
      intro y hy
      rw [aeval_fixLeft]
      exact hP x hx y hy
    rw [← aeval_fixLeft]
    exact hy (fixLeft x P) hf
  intro x hx y hy
  have hf : fixRight y P ∈ MvPolynomial.vanishingIdeal K S := by
    intro x hx
    rw [aeval_fixRight]
    exact hfirst x hx y hy
  rw [← aeval_fixRight]
  exact hx (fixRight y P) hf

end Sunlet.PolynomialClosureProduct

end GenericSource_PolynomialClosureProduct

#check "SUNLET_PolynomialClosureProduct_READY"


section GenericSource_ToricClosure
open scoped BigOperators

namespace Sunlet.ToricPairAlgebra

variable {k Ω ι : Type*} [Field k] [CharZero k]
  [Fintype Ω] [Fintype ι] [DecidableEq Ω] [DecidableEq ι]
  (o : Ω)

def parameterImage (π : ι → Equiv.Perm Ω) : Set (ι × Ω → k) :=
  {x | ∃ (U : ι → k) (h : Ω → kˣ), h o = 1 ∧ x = toricPoint π U h}

def toricClosure (π : ι → Equiv.Perm Ω) : Set (ι × Ω → k) :=
  PolynomialClosureProduct.closure (parameterImage (k := k) o π)

def laurentPoint (π : ι → Equiv.Perm Ω) (b : Bool) (ax : ι × Ω) :
    LaurentRing (k := k) (ι := ι) o :=
  coefficient o b ax.1 * (torus o b ax.2).val * ((torus o b (π ax.1 ax.2))⁻¹).val

theorem generic_laurentPoint (π : ι → Equiv.Perm Ω) (b : Bool) (ax : ι × Ω) :
    generic o (laurentPoint (k := k) o π b ax) = genericPoint (k := k) o π b ax := by
  simp [laurentPoint, genericPoint, ToricDifferential.coordinate, ToricDifferential.ratio,
    generic, div_eq_mul_inv, mul_assoc]

theorem evaluate_laurentPoint (π : ι → Equiv.Perm Ω)
    (U : Bool → ι → k) (h : Bool → Ω → kˣ) (hbase : ∀ b, h b o = 1)
    (b : Bool) (ax : ι × Ω) :
    evaluate o U h (laurentPoint (k := k) o π b ax) = toricPoint π (U b) (h b) ax := by
  simp [laurentPoint, evaluate_torus o U h hbase, toricPoint,
    ToricDifferential.coordinate, ToricDifferential.ratio, div_eq_mul_inv, mul_assoc]

theorem denominator_ne_zero : denominator (k := k) (ι := ι) o ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun _ _ => MvPolynomial.X_ne_zero _)

def assignedTorus (x : Index (ι := ι) o → k)
    (hx : MvPolynomial.aeval x (denominator (k := k) (ι := ι) o) ≠ 0)
    (b : Bool) (a : Ω) : kˣ :=
  if ha : a = o then 1 else Units.mk0 (x (b, Sum.inr ⟨a, ha⟩)) (by
    have hp : ∏ j : Bool × {a : Ω // a ≠ o}, x (j.1, Sum.inr j.2) ≠ 0 := by
      simpa [denominator] using hx
    exact (Finset.prod_ne_zero_iff.mp hp) (b, ⟨a, ha⟩) (Finset.mem_univ _))

@[simp] theorem assignedTorus_base (x : Index (ι := ι) o → k)
    (hx : MvPolynomial.aeval x (denominator (k := k) (ι := ι) o) ≠ 0) (b : Bool) :
    assignedTorus o x hx b o = 1 := by simp [assignedTorus]

theorem variableValues_assignment (x : Index (ι := ι) o → k)
    (hx : MvPolynomial.aeval x (denominator (k := k) (ι := ι) o) ≠ 0) :
    variableValues o (fun b a => x (b, Sum.inl a)) (assignedTorus o x hx) = x := by
  funext bj
  rcases bj with ⟨b, a | a⟩
  · rfl
  · simp [variableValues, assignedTorus, a.property]

theorem evaluate_polynomial_assignment (x : Index (ι := ι) o → k)
    (hx : MvPolynomial.aeval x (denominator (k := k) (ι := ι) o) ≠ 0)
    (p : PolynomialRing (k := k) (ι := ι) o) :
    evaluate o (fun b a => x (b, Sum.inl a)) (assignedTorus o x hx)
      (algebraMap (PolynomialRing (k := k) (ι := ι) o) (LaurentRing (k := k) (ι := ι) o) p) =
        MvPolynomial.aeval x p := by
  have hh : (evaluate o (fun b a => x (b, Sum.inl a)) (assignedTorus o x hx)).comp
      (IsScalarTower.toAlgHom k (PolynomialRing (k := k) (ι := ι) o)
        (LaurentRing (k := k) (ι := ι) o)) = MvPolynomial.aeval x := by
    ext j
    change evaluate o (fun b a => x (b, Sum.inl a)) (assignedTorus o x hx)
      (algebraMap (PolynomialRing (k := k) (ι := ι) o) (LaurentRing (k := k) (ι := ι) o)
        (MvPolynomial.X j)) = MvPolynomial.aeval x (MvPolynomial.X j)
    rw [evaluate_polynomial, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    exact congrFun (variableValues_assignment o x hx) j
  exact AlgHom.congr_fun hh p

/-- Every nonzero element of the literal Laurent parameter algebra is
detected by a field-valued parameter point. -/
theorem laurent_separated_by_points (f : LaurentRing (k := k) (ι := ι) o)
    (hf : ∀ (U : Bool → ι → k) (h : Bool → Ω → kˣ),
      (∀ b, h b o = 1) → evaluate o U h f = 0) : f = 0 := by
  letI : Infinite k := Infinite.of_injective Nat.cast (Nat.cast_injective (R := k))
  let p := (IsLocalization.Away.sec (denominator (k := k) (ι := ι) o) f).1
  let n := (IsLocalization.Away.sec (denominator (k := k) (ι := ι) o) f).2
  have hsec : f * algebraMap (PolynomialRing (k := k) (ι := ι) o)
      (LaurentRing (k := k) (ι := ι) o) ((denominator o) ^ n) =
        algebraMap (PolynomialRing (k := k) (ι := ι) o)
          (LaurentRing (k := k) (ι := ι) o) p :=
    IsLocalization.Away.sec_spec (denominator o) f
  have hp : ∀ x : Index (ι := ι) o → k, MvPolynomial.aeval x (denominator (k := k) (ι := ι) o) ≠ 0 →
      MvPolynomial.aeval x p = 0 := by
    intro x hx
    have he := congrArg (evaluate o (fun b a => x (b, Sum.inl a))
      (assignedTorus o x hx)) hsec
    rw [map_mul, hf _ _ (assignedTorus_base o x hx), zero_mul,
      evaluate_polynomial_assignment] at he
    exact he.symm
  have hprod : p * denominator o = 0 := by
    apply MvPolynomial.funext
    intro x
    change MvPolynomial.aeval x (p * denominator o) = MvPolynomial.aeval x 0
    by_cases hx : MvPolynomial.aeval x (denominator (k := k) (ι := ι) o) = 0
    · rw [map_mul, map_zero, hx, mul_zero]
    · rw [map_mul, map_zero, hp x hx, zero_mul]
  have hp0 : p = 0 := (mul_eq_zero.mp hprod).resolve_right (denominator_ne_zero (k := k) (ι := ι) o)
  have hu := IsLocalization.Away.algebraMap_pow_isUnit
    (S := LaurentRing (k := k) (ι := ι) o) (denominator (k := k) (ι := ι) o) n
  rw [map_pow] at hsec
  apply hu.mul_right_cancel
  simpa only [hp0, map_zero, zero_mul] using hsec

theorem generic_pair_identity_on_parameters (π : ι → Equiv.Perm Ω)
    (P : MvPolynomial (Bool × (ι × Ω)) k)
    (hP : MvPolynomial.aeval (fun bi => genericPoint (k := k) o π bi.1 bi.2) P = 0) :
    ∀ x ∈ parameterImage (k := k) o π, ∀ y ∈ parameterImage (k := k) o π,
      MvPolynomial.aeval (PolynomialClosureProduct.pair x y) P = 0 := by
  have hg : MvPolynomial.aeval (fun bi => laurentPoint (k := k) o π bi.1 bi.2) P = 0 := by
    apply (generic_injective (k := k) (ι := ι) o)
    rw [map_zero, MvPolynomial.comp_aeval_apply]
    simpa only [generic_laurentPoint] using hP
  rintro x ⟨U, h, hb, rfl⟩ y ⟨V, g, gb, rfl⟩
  let U' : Bool → ι → k := fun b => if b then V else U
  let h' : Bool → Ω → kˣ := fun b => if b then g else h
  have hbase : ∀ b, h' b o = 1 := by intro b; cases b <;> assumption
  have he := congrArg (evaluate o U' h') hg
  rw [map_zero, MvPolynomial.comp_aeval_apply] at he
  convert he using 1
  congr 1
  apply congrArg MvPolynomial.aeval
  funext bi
  rcases bi with ⟨b, i⟩
  rw [evaluate_laurentPoint o π U' h' hbase]
  cases b <;> rfl

theorem generic_pair_identity_on_closure (π : ι → Equiv.Perm Ω)
    (P : MvPolynomial (Bool × (ι × Ω)) k)
    (hP : MvPolynomial.aeval (fun bi => genericPoint (k := k) o π bi.1 bi.2) P = 0) :
    ∀ x ∈ toricClosure (k := k) o π, ∀ y ∈ toricClosure (k := k) o π,
      MvPolynomial.aeval (PolynomialClosureProduct.pair x y) P = 0 :=
  PolynomialClosureProduct.identity_on_closure_pairs _ P
    (generic_pair_identity_on_parameters o π P hP)

def genericPointIdeal (π : ι → Equiv.Perm Ω) : Ideal (MvPolynomial (ι × Ω) k) :=
  RingHom.ker (MvPolynomial.aeval (genericPoint (k := k) o π false))

theorem generic_point_equation_iff (π : ι → Equiv.Perm Ω) (b : Bool)
    (P : MvPolynomial (ι × Ω) k) :
    MvPolynomial.aeval (genericPoint (k := k) o π b) P = 0 ↔
      P ∈ MvPolynomial.vanishingIdeal k (parameterImage (k := k) o π) := by
  constructor
  · intro hP
    have hg : MvPolynomial.aeval (laurentPoint (k := k) o π b) P = 0 := by
      apply generic_injective (k := k) (ι := ι) o
      rw [map_zero, MvPolynomial.comp_aeval_apply]
      simpa only [generic_laurentPoint] using hP
    rintro x ⟨U, h, hb, rfl⟩
    have he := congrArg (evaluate o (fun _ => U) (fun _ => h)) hg
    rw [map_zero, MvPolynomial.comp_aeval_apply] at he
    simpa only [evaluate_laurentPoint o π (fun _ => U) (fun _ => h) (fun _ => hb)] using he
  · intro hP
    have hg : MvPolynomial.aeval (laurentPoint (k := k) o π b) P = 0 := by
      apply laurent_separated_by_points o
      intro U h hb
      rw [MvPolynomial.comp_aeval_apply]
      simpa only [evaluate_laurentPoint o π U h hb] using
        hP (toricPoint π (U b) (h b)) ⟨U b, h b, hb b, rfl⟩
    have he := congrArg (generic (k := k) (ι := ι) o) hg
    rw [map_zero, MvPolynomial.comp_aeval_apply] at he
    simpa only [generic_laurentPoint] using he

theorem genericPointIdeal_eq_vanishingIdeal (π : ι → Equiv.Perm Ω) :
    genericPointIdeal (k := k) o π =
      MvPolynomial.vanishingIdeal k (parameterImage (k := k) o π) := by
  ext P
  exact generic_point_equation_iff o π false P

theorem toricClosure_eq_generic_zeroLocus (π : ι → Equiv.Perm Ω) :
    toricClosure (k := k) o π = MvPolynomial.zeroLocus k (genericPointIdeal (k := k) o π) := by
  rw [genericPointIdeal_eq_vanishingIdeal]
  rfl

end Sunlet.ToricPairAlgebra

end GenericSource_ToricClosure

#check "SUNLET_ToricClosure_READY"


section GenericSource_RankOneRecovery

namespace Sunlet.RankOneRecovery

variable {K O : Type*} [Field K] [CharZero K]

theorem pair_eq_of_sum_and_difference (x y x' y' : O → K)
    (hs : x + y = x' + y') (hd : x - y = x' - y') : x = x' ∧ y = y' := by
  constructor
  · funext i
    have hsi := congrFun hs i
    have hdi := congrFun hd i
    simp only [Pi.add_apply, Pi.sub_apply] at hsi hdi
    linear_combination (1 / 2 : K) * hsi + (1 / 2 : K) * hdi
  · funext i
    have hsi := congrFun hs i
    have hdi := congrFun hd i
    simp only [Pi.add_apply, Pi.sub_apply] at hsi hdi
    linear_combination (1 / 2 : K) * hsi - (1 / 2 : K) * hdi

/-- This uses the full coordinates of arbitrary points and makes no
assumption that either point has nonzero toric parameters. -/
theorem unordered_of_sum_and_pivot_products (x y x' y' : O → K) (p : O)
    (hs : x + y = x' + y') (hp : x p - y p ≠ 0)
    (hprod : ∀ i, (x p - y p) * (x i - y i) =
      (x' p - y' p) * (x' i - y' i)) :
    (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by
  have hfac : ((x p - y p) - (x' p - y' p)) *
      ((x p - y p) + (x' p - y' p)) = 0 := by
    linear_combination hprod p
  rcases mul_eq_zero.mp hfac with he | he
  · left
    have hb : x p - y p = x' p - y' p := sub_eq_zero.mp he
    have hd : x - y = x' - y' := by
      funext i
      change x i - y i = x' i - y' i
      apply mul_left_cancel₀ hp
      rw [hprod i, ← hb]
    exact pair_eq_of_sum_and_difference x y x' y' hs hd
  · right
    have hb : x' p - y' p = -(x p - y p) := by
      linear_combination he
    have hd : x - y = y' - x' := by
      funext i
      change x i - y i = y' i - x' i
      apply mul_left_cancel₀ hp
      rw [hprod i, hb]
      ring
    exact pair_eq_of_sum_and_difference x y y' x'
      (by simpa only [add_comm y' x'] using hs) hd

end Sunlet.RankOneRecovery

end GenericSource_RankOneRecovery

#check "SUNLET_RankOneRecovery_READY"


section GenericSource_SumOpenUniqueness
open scoped BigOperators

namespace Sunlet.ToricPairAlgebra

variable {k Ω ι : Type*} [Field k] [CharZero k]
  [Fintype Ω] [Fintype ι] [DecidableEq Ω] [DecidableEq ι]
  (o : Ω) (π : ι → Equiv.Perm Ω)

def genericDifference (i : ι × Ω) : FunctionField (k := k) (ι := ι) o :=
  genericPoint (k := k) o π false i - genericPoint (k := k) o π true i

theorem genericPoint_coordinate_ne_zero (b : Bool) (i : ι × Ω) :
    genericPoint (k := k) o π b i ≠ 0 := by
  change genericCoefficient o b i.1 *
    ((genericTorus (k := k) (ι := ι) o b i.2).val /
      (genericTorus (k := k) (ι := ι) o b (π i.1 i.2)).val) ≠ 0
  exact mul_ne_zero (genericVariable_ne_zero o (b, Sum.inl i.1))
    (div_ne_zero (Units.ne_zero _) (Units.ne_zero _))

theorem genericDifference_ne_zero (i : ι × Ω) : genericDifference (k := k) o π i ≠ 0 := by
  intro he
  have hxy := sub_eq_zero.mp he
  have hd := congrArg (euler (k := k) (ι := ι) o) hxy
  have hf := congrFun (euler_genericPoint (k := k) o π false) i
  have ht := congrFun (euler_genericPoint (k := k) o π true) i
  change euler o (genericPoint (k := k) o π false i) = genericPoint (k := k) o π false i at hf
  change euler o (genericPoint (k := k) o π true i) = 0 at ht
  rw [hf, ht] at hd
  exact genericPoint_coordinate_ne_zero o π false i hd

structure PivotRecovery (p : ι × Ω) where
  numerator : ι × Ω → MvPolynomial (ι × Ω) k
  denominator : ι × Ω → MvPolynomial (ι × Ω) k
  denominator_ne : ∀ i,
    MvPolynomial.aeval (genericCoordinates (k := k) o π) (denominator i) ≠ 0
  relation : ∀ i,
    MvPolynomial.aeval (genericCoordinates (k := k) o π) (denominator i) *
      (genericDifference (k := k) o π p * genericDifference (k := k) o π i) =
      MvPolynomial.aeval (genericCoordinates (k := k) o π) (numerator i)

namespace PivotRecovery

variable {o π} {p : ι × Ω} (D : PivotRecovery (k := k) o π p)

def openPolynomial : MvPolynomial (ι × Ω) k :=
  D.numerator p * ∏ i, D.denominator i

theorem numerator_pivot_ne :
    MvPolynomial.aeval (genericCoordinates (k := k) o π) (D.numerator p) ≠ 0 := by
  rw [← D.relation p]
  exact mul_ne_zero (D.denominator_ne p)
    (mul_ne_zero (genericDifference_ne_zero o π p) (genericDifference_ne_zero o π p))

theorem openPolynomial_generic_ne :
    MvPolynomial.aeval (genericCoordinates (k := k) o π) D.openPolynomial ≠ 0 := by
  simp only [openPolynomial, map_mul, map_prod]
  exact mul_ne_zero D.numerator_pivot_ne
    (Finset.prod_ne_zero_iff.mpr (fun i _ => D.denominator_ne i))

theorem open_factors (z : ι × Ω → k)
    (hz : MvPolynomial.aeval z D.openPolynomial ≠ 0) :
    MvPolynomial.aeval z (D.numerator p) ≠ 0 ∧
      ∀ i, MvPolynomial.aeval z (D.denominator i) ≠ 0 := by
  simp only [openPolynomial, map_mul, map_prod, mul_ne_zero_iff] at hz
  exact ⟨hz.1, fun i => (Finset.prod_ne_zero_iff.mp hz.2) i (Finset.mem_univ i)⟩

def sumSubstitution : MvPolynomial (ι × Ω) k →ₐ[k]
    MvPolynomial (Bool × (ι × Ω)) k :=
  MvPolynomial.aeval (fun i => MvPolynomial.X (false, i) + MvPolynomial.X (true, i))

def differencePolynomial (i : ι × Ω) : MvPolynomial (Bool × (ι × Ω)) k :=
  MvPolynomial.X (false, i) - MvPolynomial.X (true, i)

def relationPolynomial (i : ι × Ω) : MvPolynomial (Bool × (ι × Ω)) k :=
  sumSubstitution (D.denominator i) * (differencePolynomial p * differencePolynomial i) -
    sumSubstitution (D.numerator i)

theorem aeval_sumSubstitution {A : Type*} [CommRing A] [Algebra k A]
    (v : Bool × (ι × Ω) → A) (P : MvPolynomial (ι × Ω) k) :
    MvPolynomial.aeval v (sumSubstitution P) =
      MvPolynomial.aeval (fun i => v (false, i) + v (true, i)) P := by
  rw [sumSubstitution, MvPolynomial.comp_aeval_apply]
  simp only [map_add, MvPolynomial.aeval_X]

theorem relationPolynomial_generic (i : ι × Ω) :
    MvPolynomial.aeval (fun bi => genericPoint (k := k) o π bi.1 bi.2) (D.relationPolynomial i) = 0 := by
  simp only [relationPolynomial, map_sub, map_mul, differencePolynomial,
    MvPolynomial.aeval_X, aeval_sumSubstitution]
  change MvPolynomial.aeval (genericCoordinates (k := k) o π) (D.denominator i) *
      (genericDifference (k := k) o π p * genericDifference (k := k) o π i) -
      MvPolynomial.aeval (genericCoordinates (k := k) o π) (D.numerator i) = 0
  exact sub_eq_zero.mpr (D.relation i)

theorem relation_on_closure (x y : ι × Ω → k)
    (hx : x ∈ toricClosure (k := k) o π) (hy : y ∈ toricClosure (k := k) o π) (i : ι × Ω) :
    MvPolynomial.aeval (x + y) (D.denominator i) * ((x p - y p) * (x i - y i)) =
      MvPolynomial.aeval (x + y) (D.numerator i) := by
  have hh := generic_pair_identity_on_closure o π (D.relationPolynomial i)
    (D.relationPolynomial_generic i) x hx y hy
  simp only [relationPolynomial, map_sub, map_mul, differencePolynomial,
    MvPolynomial.aeval_X, aeval_sumSubstitution, PolynomialClosureProduct.pair,
    Bool.false_eq_true, ↓reduceIte] at hh
  exact sub_eq_zero.mp hh

theorem product_at (z x y : ι × Ω → k)
    (hz : MvPolynomial.aeval z D.openPolynomial ≠ 0)
    (hx : x ∈ toricClosure (k := k) o π) (hy : y ∈ toricClosure (k := k) o π)
    (hs : x + y = z) (i : ι × Ω) :
    (x p - y p) * (x i - y i) =
      MvPolynomial.aeval z (D.numerator i) / MvPolynomial.aeval z (D.denominator i) := by
  apply (eq_div_iff ((D.open_factors z hz).2 i)).mpr
  have hh := D.relation_on_closure x y hx hy i
  rw [hs] at hh
  simpa only [mul_comm] using hh

/-- The open set excludes every possible additional boundary
decomposition, rather than only alternative torus parameterizations. -/
theorem unique_unordered_on_open (z x y x' y' : ι × Ω → k)
    (hz : MvPolynomial.aeval z D.openPolynomial ≠ 0)
    (hx : x ∈ toricClosure (k := k) o π) (hy : y ∈ toricClosure (k := k) o π)
    (hx' : x' ∈ toricClosure (k := k) o π) (hy' : y' ∈ toricClosure (k := k) o π)
    (hs : x + y = z) (hs' : x' + y' = z) :
    (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by
  have hp : x p - y p ≠ 0 := by
    intro hzero
    have hh := D.product_at z x y hz hx hy hs p
    rw [hzero, zero_mul] at hh
    exact (div_ne_zero (D.open_factors z hz).1 ((D.open_factors z hz).2 p)) hh.symm
  apply RankOneRecovery.unordered_of_sum_and_pivot_products x y x' y' p
    (hs.trans hs'.symm) hp
  intro i
  exact (D.product_at z x y hz hx hy hs i).trans
    (D.product_at z x' y' hz hx' hy' hs' i).symm

/-- The principal open set actually meets the parameterized secant, so
the uniqueness statement is not vacuous. -/
theorem nonempty_open_parameter_sums :
    ∃ (U : Bool → ι → k) (h : Bool → Ω → kˣ), (∀ b, h b o = 1) ∧
      MvPolynomial.aeval (toricPoint π (U false) (h false) +
        toricPoint π (U true) (h true)) D.openPolynomial ≠ 0 := by
  by_contra hn
  push_neg at hn
  let f : LaurentRing (k := k) (ι := ι) o :=
    MvPolynomial.aeval (fun i => laurentPoint (k := k) o π false i + laurentPoint (k := k) o π true i)
      D.openPolynomial
  have hf : f = 0 := by
    apply laurent_separated_by_points o
    intro U h hb
    dsimp only [f]
    rw [MvPolynomial.comp_aeval_apply]
    simp only [map_add, evaluate_laurentPoint o π U h hb]
    exact hn U h hb
  have hg := congrArg (generic (k := k) (ι := ι) o) hf
  dsimp only [f] at hg
  rw [map_zero, MvPolynomial.comp_aeval_apply] at hg
  simp only [map_add, generic_laurentPoint] at hg
  exact D.openPolynomial_generic_ne hg

end PivotRecovery

/-- The reconstruction coefficients are defined over the original
characteristic-zero field; no algebraic-closure descent is assumed. -/
theorem exists_pivotRecovery_of_witness
    (W : SparseWitness (k := k) o π)
    (hmoves : ∀ a, π a o ≠ o)
    (hdim : 2 < Fintype.card (NormalizedVariations.Index ι Ω o))
    (p : ι × Ω) : Nonempty (PivotRecovery (k := k) o π p) := by
  have hr : ∀ i : ι × Ω, ∃ n d : MvPolynomial (ι × Ω) k,
      MvPolynomial.aeval (genericCoordinates (k := k) o π) d ≠ 0 ∧
      MvPolynomial.aeval (genericCoordinates (k := k) o π) d *
        (genericDifference (k := k) o π p * genericDifference (k := k) o π i) =
        MvPolynomial.aeval (genericCoordinates (k := k) o π) n := by
    intro i
    have hm := differenceProduct_mem_generatedField o π W hmoves hdim p i
    obtain ⟨n, d, he⟩ := (IntermediateField.mem_adjoin_range_iff k
      (genericCoordinates (k := k) o π) _).mp hm
    have hd : MvPolynomial.aeval (genericCoordinates (k := k) o π) d ≠ 0 := by
      intro hd
      rw [hd, div_zero] at he
      exact mul_ne_zero (genericDifference_ne_zero o π p)
        (genericDifference_ne_zero o π i) he
    refine ⟨n, d, hd, ?_⟩
    unfold genericDifference
    rw [he]
    field_simp
  choose n d hd he using hr
  exact ⟨⟨n, d, hd, he⟩⟩

end Sunlet.ToricPairAlgebra

namespace Sunlet.LoopData

open ToricPairAlgebra

variable {k Ω ι : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  [Fintype Ω] [Fintype ι] [DecidableEq Ω] [DecidableEq ι]
  (L : LoopData Ω) (e : ι ≃ {x : Ω // x ≠ L.identity})
  (π : ι → Equiv.Perm Ω) (hπ : ∀ a, π a = L.left (e a))

include hπ in
theorem exists_pivotRecovery
    (W : SparseWitness (k := k) L.identity π)
    (hmoves : ∀ a, π a L.identity ≠ L.identity)
    (hdim : 2 < Fintype.card (NormalizedVariations.Index ι Ω L.identity))
    (p : ι × Ω) : Nonempty (PivotRecovery (k := k) L.identity π p) := by
  have hr : ∀ i : ι × Ω, ∃ n d : MvPolynomial (ι × Ω) k,
      MvPolynomial.aeval (genericCoordinates (k := k) L.identity π) d ≠ 0 ∧
      MvPolynomial.aeval (genericCoordinates (k := k) L.identity π) d *
        (genericDifference (k := k) L.identity π p * genericDifference (k := k) L.identity π i) =
        MvPolynomial.aeval (genericCoordinates (k := k) L.identity π) n := by
    intro i
    have hm := L.differenceProduct_mem_coordinateField e π hπ W hmoves hdim p i
    obtain ⟨n, d, he⟩ := (IntermediateField.mem_adjoin_range_iff k
      (genericCoordinates (k := k) L.identity π) _).mp hm
    have hd : MvPolynomial.aeval (genericCoordinates (k := k) L.identity π) d ≠ 0 := by
      intro hd
      rw [hd, div_zero] at he
      exact mul_ne_zero (genericDifference_ne_zero L.identity π p)
        (genericDifference_ne_zero L.identity π i) he
    refine ⟨n, d, hd, ?_⟩
    unfold genericDifference
    rw [he]
    field_simp
  choose n d hd he using hr
  exact ⟨⟨n, d, hd, he⟩⟩

end Sunlet.LoopData

end GenericSource_SumOpenUniqueness

#check "SUNLET_SumOpenUniqueness_READY"


section GenericSource_SecantClosure

namespace Sunlet.ToricPairAlgebra

variable {k Ω ι : Type*} [Field k] [CharZero k]
  [Fintype Ω] [Fintype ι] [DecidableEq Ω] [DecidableEq ι]
  (o : Ω) (π : ι → Equiv.Perm Ω)

theorem parameterImage_subset_toricClosure :
    parameterImage (k := k) o π ⊆ toricClosure (k := k) o π := by
  intro x hx P hP
  exact hP x hx

def sumImage : Set (ι × Ω → k) :=
  {z | ∃ x ∈ toricClosure (k := k) o π, ∃ y ∈ toricClosure (k := k) o π, x + y = z}

def secantClosure : Set (ι × Ω → k) :=
  PolynomialClosureProduct.closure (sumImage (k := k) o π)

def genericSumIdeal : Ideal (MvPolynomial (ι × Ω) k) :=
  RingHom.ker (MvPolynomial.aeval (genericCoordinates (k := k) o π))

theorem genericSumIdeal_eq_vanishingIdeal :
    genericSumIdeal (k := k) o π = MvPolynomial.vanishingIdeal k (sumImage (k := k) o π) := by
  ext P
  change MvPolynomial.aeval (genericCoordinates (k := k) o π) P = 0 ↔ _
  constructor
  · intro hP
    have hg : MvPolynomial.aeval (fun bi => genericPoint (k := k) o π bi.1 bi.2)
        (PivotRecovery.sumSubstitution P) = 0 := by
      rw [PivotRecovery.aeval_sumSubstitution]
      exact hP
    rintro z ⟨x, hx, y, hy, rfl⟩
    have hh := generic_pair_identity_on_closure o π
      (PivotRecovery.sumSubstitution P) hg x hx y hy
    simp only [PivotRecovery.aeval_sumSubstitution,
      PolynomialClosureProduct.pair, Bool.false_eq_true, ↓reduceIte] at hh
    change MvPolynomial.aeval (fun i => x i + y i) P = 0
    exact hh
  · intro hP
    have hf : MvPolynomial.aeval
        (fun i => laurentPoint (k := k) o π false i + laurentPoint (k := k) o π true i) P = 0 := by
      apply laurent_separated_by_points o
      intro U h hb
      rw [MvPolynomial.comp_aeval_apply]
      simp only [map_add, evaluate_laurentPoint o π U h hb]
      apply hP
      exact ⟨toricPoint π (U false) (h false),
        parameterImage_subset_toricClosure o π ⟨U false, h false, hb false, rfl⟩,
        toricPoint π (U true) (h true),
        parameterImage_subset_toricClosure o π ⟨U true, h true, hb true, rfl⟩, rfl⟩
    have hg := congrArg (generic (k := k) (ι := ι) o) hf
    rw [map_zero, MvPolynomial.comp_aeval_apply] at hg
    simp only [map_add, generic_laurentPoint] at hg
    change MvPolynomial.aeval (fun i => genericPoint (k := k) o π false i +
      genericPoint (k := k) o π true i) P = 0 at hg
    have he : (fun i => genericPoint (k := k) o π false i +
        genericPoint (k := k) o π true i) = genericCoordinates (k := k) o π := by
      funext i
      rfl
    rw [he] at hg
    exact hg

theorem secantClosure_eq_generic_zeroLocus :
    secantClosure (k := k) o π = MvPolynomial.zeroLocus k (genericSumIdeal (k := k) o π) := by
  rw [genericSumIdeal_eq_vanishingIdeal]
  rfl

def principalOpen (P : MvPolynomial (ι × Ω) k) : Set (ι × Ω → k) :=
  {z | z ∈ secantClosure (k := k) o π ∧ MvPolynomial.aeval z P ≠ 0}

theorem vanishingIdeal_principalOpen
    (P : MvPolynomial (ι × Ω) k)
    (hP : MvPolynomial.aeval (genericCoordinates (k := k) o π) P ≠ 0) :
    MvPolynomial.vanishingIdeal k (principalOpen (k := k) o π P) = genericSumIdeal (k := k) o π := by
  ext Q
  constructor
  · intro hQ
    have hf : MvPolynomial.aeval
        (fun i => laurentPoint (k := k) o π false i + laurentPoint (k := k) o π true i) (P * Q) = 0 := by
      apply laurent_separated_by_points o
      intro U h hb
      rw [MvPolynomial.comp_aeval_apply]
      simp only [map_add, evaluate_laurentPoint o π U h hb, map_mul]
      let z := toricPoint π (U false) (h false) + toricPoint π (U true) (h true)
      change MvPolynomial.aeval z P * MvPolynomial.aeval z Q = 0
      by_cases hzP : MvPolynomial.aeval z P = 0
      · rw [hzP, zero_mul]
      · have hz : z ∈ secantClosure (k := k) o π := by
          intro R hR
          apply hR z
          exact ⟨toricPoint π (U false) (h false),
            parameterImage_subset_toricClosure o π ⟨U false, h false, hb false, rfl⟩,
            toricPoint π (U true) (h true),
            parameterImage_subset_toricClosure o π ⟨U true, h true, hb true, rfl⟩, rfl⟩
        rw [hQ z ⟨hz, hzP⟩, mul_zero]
    have hg := congrArg (generic (k := k) (ι := ι) o) hf
    rw [map_zero, MvPolynomial.comp_aeval_apply] at hg
    simp only [map_add, generic_laurentPoint, map_mul] at hg
    exact (mul_eq_zero.mp hg).resolve_left hP
  · intro hQ z hz
    rcases hz with ⟨hz, _⟩
    rw [secantClosure_eq_generic_zeroLocus] at hz
    exact hz Q hQ

/-- The principal open has the full secant as its algebraic closure.
This supplies the density assertion in the word "general". -/
theorem closure_principalOpen
    (P : MvPolynomial (ι × Ω) k)
    (hP : MvPolynomial.aeval (genericCoordinates (k := k) o π) P ≠ 0) :
    PolynomialClosureProduct.closure (principalOpen (k := k) o π P) = secantClosure (k := k) o π := by
  unfold PolynomialClosureProduct.closure
  rw [vanishingIdeal_principalOpen o π P hP, secantClosure_eq_generic_zeroLocus]

end Sunlet.ToricPairAlgebra

end GenericSource_SecantClosure

#check "SUNLET_SecantClosure_READY"


section GenericSource_QuadraticReconstruction

namespace Sunlet.QuadraticReconstruction

open Polynomial

variable {R F E : Type*} [CommRing R] [Field F] [Field E]
  [Algebra R F] [Algebra F E] [Algebra R E] [IsScalarTower R F E]

def polynomial (d : R) : R[X] := X ^ 2 - C d

theorem polynomial_monic (d : R) : (polynomial d).Monic :=
  monic_X_pow_sub_C d (by decide)

theorem polynomial_natDegree [Nontrivial R] (d : R) : (polynomial d).natDegree = 2 := by
  simp [polynomial]

theorem polynomial_aeval (d : R) (t : E) (ht : t ^ 2 = algebraMap R E d) :
    aeval t (polynomial d) = 0 := by simp [polynomial, ht]

def genericLift (d : R) (t : E) (ht : t ^ 2 = algebraMap R E d) :
    AdjoinRoot (polynomial d) →ₐ[R] E :=
  AdjoinRoot.liftAlgHom (polynomial d) (Algebra.ofId R E) t (polynomial_aeval d t ht)

/-- The quadratic algebra injects into the actual parameter field as
soon as its root is not in the intervening sum field. -/
theorem genericLift_injective
    (hinj : Function.Injective (algebraMap R F))
    (d : R) (t : E) (ht : t ^ 2 = algebraMap R E d)
    (hnot : t ∉ Set.range (algebraMap F E)) :
    Function.Injective (genericLift d t ht) := by
  let P : F[X] := (polynomial d).map (algebraMap R F)
  have hpmonic : P.Monic := (polynomial_monic d).map _
  have hpdeg : P.natDegree = 2 := by
    simp [P, polynomial]
  have hproot : aeval t P = 0 := by
    simp [P, polynomial, ht, ← IsScalarTower.algebraMap_apply R F E]
  have hint : IsIntegral F t := ⟨P, hpmonic, hproot⟩
  have hmindeg : 2 ≤ (minpoly F t).natDegree :=
    (minpoly.two_le_natDegree_iff hint).mpr hnot
  have hmin : P = minpoly F t :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hpmonic
      (minpoly.dvd F t hproot) (by simpa [hpdeg] using hmindeg)
  apply (injective_iff_map_eq_zero (genericLift d t ht)).mpr
  intro a ha
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective a
  apply AdjoinRoot.mk_eq_zero.mpr
  apply (Polynomial.map_dvd_map (algebraMap R F) hinj (polynomial_monic d)).mp
  change P ∣ q.map (algebraMap R F)
  rw [hmin]
  apply minpoly.dvd F t
  change (q.map (algebraMap R F)).eval₂ (algebraMap F E) t = 0
  rw [Polynomial.eval₂_map, ← IsScalarTower.algebraMap_eq R F E]
  exact ha

@[simp] theorem genericLift_root (d : R) (t : E) (ht : t ^ 2 = algebraMap R E d) :
    genericLift d t ht (AdjoinRoot.root (polynomial d)) = t := by
  exact AdjoinRoot.liftAlgHom_root (polynomial d) (Algebra.ofId R E) t _

@[simp] theorem genericLift_algebraMap (d : R) (t : E)
    (ht : t ^ 2 = algebraMap R E d) (r : R) :
    genericLift d t ht (algebraMap R (AdjoinRoot (polynomial d)) r) =
      algebraMap R E r := (genericLift d t ht).commutes r

section ClosedPoint

variable {k : Type*} [Field k] [IsAlgClosed k] [Algebra k R]

theorem exists_closedPoint_lift (d : R) (φ : R →ₐ[k] k) :
    ∃ ψ : AdjoinRoot (polynomial d) →ₐ[k] k,
      ∀ r : R, ψ (algebraMap R (AdjoinRoot (polynomial d)) r) = φ r := by
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (φ d) (by decide : 0 < 2)
  let ψ := AdjoinRoot.liftAlgHom (polynomial d) φ t (by simp [polynomial, ht])
  refine ⟨ψ, ?_⟩
  intro r
  exact AdjoinRoot.liftAlgHom_of (polynomial d) φ t _ r

end ClosedPoint

end Sunlet.QuadraticReconstruction

end GenericSource_QuadraticReconstruction

#check "SUNLET_QuadraticReconstruction_READY"


section GenericSource_QuadraticPoints

namespace Sunlet.QuadraticReconstruction

variable {k R F E O : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  [CommRing R] [Field F] [Field E] [CharZero E]
  [Algebra k R] [Algebra k F] [Algebra k E]
  [Algebra R F] [Algebra F E] [Algebra R E]
  [IsScalarTower k R F] [IsScalarTower k F E]
  [IsScalarTower k R E] [IsScalarTower R F E]

def reconstructedPoint (d : Rˣ) (q r : O → R) (b : Bool) (i : O) :
    AdjoinRoot (polynomial d.val) :=
  (2 : k)⁻¹ •
    (algebraMap R _ (q i) + (if b then -1 else 1) *
      algebraMap R _ (r i) * algebraMap R _ (d⁻¹).val *
        AdjoinRoot.root (polynomial d.val))

theorem generic_reconstructedPoint
    (d : Rˣ) (q r : O → R) (x y : O → E) (t : E)
    (ht : t ^ 2 = algebraMap R E d.val)
    (hq : ∀ i, algebraMap R E (q i) = x i + y i)
    (hr : ∀ i, algebraMap R E (r i) = t * (x i - y i))
    (b : Bool) (i : O) :
    genericLift d.val t ht (reconstructedPoint (k := k) d q r b i) =
      if b then y i else x i := by
  have hdinv : algebraMap R E (d⁻¹).val * t ^ 2 = 1 := by
    rw [ht, ← map_mul]
    simp
  have hlinear : algebraMap R E (r i) * algebraMap R E (d⁻¹).val * t =
      x i - y i := by
    rw [hr]
    calc
      (t * (x i - y i)) * algebraMap R E (d⁻¹).val * t =
          (x i - y i) * (algebraMap R E (d⁻¹).val * t ^ 2) := by ring
      _ = x i - y i := by rw [hdinv, mul_one]
  change (genericLift d.val t ht).restrictScalars k
      (reconstructedPoint (k := k) d q r b i) = _
  simp only [reconstructedPoint, map_smul, map_add, map_mul,
    AlgHom.restrictScalars_apply, genericLift_root, genericLift_algebraMap]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, map_one, one_mul, hq, hlinear]
    simp only [Algebra.smul_def, map_inv₀, map_ofNat]
    field_simp
    ring
  · simp only [↓reduceIte, map_neg, map_one, neg_one_mul, neg_mul,
      ← neg_mul, hq, hlinear]
    simp only [Algebra.smul_def, map_inv₀, map_ofNat]
    field_simp
    rw [hlinear]
    ring

theorem specialization_preserves_equation
    (hinj : Function.Injective (algebraMap R F))
    (d : Rˣ) (q r : O → R) (x y : O → E) (t : E)
    (ht : t ^ 2 = algebraMap R E d.val)
    (hnot : t ∉ Set.range (algebraMap F E))
    (hq : ∀ i, algebraMap R E (q i) = x i + y i)
    (hr : ∀ i, algebraMap R E (r i) = t * (x i - y i))
    (ψ : AdjoinRoot (polynomial d.val) →ₐ[k] k)
    (b : Bool) (P : MvPolynomial O k)
    (hP : MvPolynomial.aeval (if b then y else x) P = 0) :
    MvPolynomial.aeval (fun i => ψ (reconstructedPoint (k := k) d q r b i)) P = 0 := by
  have he : MvPolynomial.aeval (reconstructedPoint (k := k) d q r b) P = 0 := by
    apply genericLift_injective hinj d.val t ht hnot
    rw [map_zero]
    change (genericLift d.val t ht).restrictScalars k
      (MvPolynomial.aeval (reconstructedPoint (k := k) d q r b) P) = 0
    rw [MvPolynomial.comp_aeval_apply]
    have hf : (fun i => genericLift d.val t ht
        (reconstructedPoint (k := k) d q r b i)) = if b then y else x := by
      funext i
      rw [generic_reconstructedPoint d q r x y t ht hq hr]
      cases b <;> rfl
    change MvPolynomial.aeval (fun i => genericLift d.val t ht
      (reconstructedPoint (k := k) d q r b i)) P = 0
    rw [hf]
    exact hP
  have hh := congrArg ψ he
  rw [map_zero, MvPolynomial.comp_aeval_apply] at hh
  exact hh

/-- Every specialization of the coefficient algebra lifts to a pair
whose sum is the specialized sum and whose components satisfy all the
generic polynomial equations. -/
theorem exists_specialized_pair
    (hinj : Function.Injective (algebraMap R F))
    (d : Rˣ) (q r : O → R) (x y : O → E) (t : E)
    (ht : t ^ 2 = algebraMap R E d.val)
    (hnot : t ∉ Set.range (algebraMap F E))
    (hq : ∀ i, algebraMap R E (q i) = x i + y i)
    (hr : ∀ i, algebraMap R E (r i) = t * (x i - y i))
    (φ : R →ₐ[k] k) :
    ∃ x' y' : O → k,
      (∀ i, x' i + y' i = φ (q i)) ∧
      (∀ P : MvPolynomial O k, MvPolynomial.aeval x P = 0 →
        MvPolynomial.aeval x' P = 0) ∧
      (∀ P : MvPolynomial O k, MvPolynomial.aeval y P = 0 →
        MvPolynomial.aeval y' P = 0) := by
  obtain ⟨ψ, hψ⟩ := exists_closedPoint_lift (k := k) d.val φ
  let x' : O → k := fun i => ψ (reconstructedPoint (k := k) d q r false i)
  let y' : O → k := fun i => ψ (reconstructedPoint (k := k) d q r true i)
  refine ⟨x', y', ?_, ?_, ?_⟩
  · intro i
    simp only [x', y', reconstructedPoint, Bool.false_eq_true, ↓reduceIte,
      map_smul, map_add, map_mul, map_neg, map_one, one_mul, neg_one_mul,
      hψ, Algebra.smul_def, AlgHom.commutes]
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
    field_simp
    ring
  · intro P hP
    exact specialization_preserves_equation hinj d q r x y t ht hnot hq hr ψ false P hP
  · intro P hP
    exact specialization_preserves_equation hinj d q r x y t ht hnot hq hr ψ true P hP

end Sunlet.QuadraticReconstruction

end GenericSource_QuadraticPoints

#check "SUNLET_QuadraticPoints_READY"


section GenericSource_ImageLocalization

namespace Sunlet.ImageLocalization

variable {k F O : Type*} [Field k] [Field F] [Algebra k F]
  (q : O → F)

abbrev CoordinateAlgebra := (MvPolynomial.aeval q : MvPolynomial O k →ₐ[k] F).range

def polynomial : MvPolynomial O k →ₐ[k] CoordinateAlgebra (k := k) q :=
  (MvPolynomial.aeval q).rangeRestrict

@[simp] theorem polynomial_val (P : MvPolynomial O k) :
    (polynomial q P).val = MvPolynomial.aeval q P := rfl

variable (P : MvPolynomial O k)

abbrev OpenAlgebra := Localization.Away (polynomial q P)

def ofPolynomial : MvPolynomial O k →ₐ[k] OpenAlgebra q P :=
  (IsScalarTower.toAlgHom k (CoordinateAlgebra (k := k) q) (OpenAlgebra q P)).comp (polynomial q)

def generic (hP : MvPolynomial.aeval q P ≠ 0) : OpenAlgebra q P →ₐ[k] F :=
  IsLocalization.Away.liftAlgHom (polynomial q P)
    (IsUnit.mk0 (((MvPolynomial.aeval q).range.val) (polynomial q P)) hP)

@[simp] theorem generic_of (hP : MvPolynomial.aeval q P ≠ 0) (a : CoordinateAlgebra (k := k) q) :
    generic q P hP (algebraMap (CoordinateAlgebra (k := k) q) (OpenAlgebra q P) a) = a.val := by
  simp [generic]

@[simp] theorem generic_ofPolynomial (hP : MvPolynomial.aeval q P ≠ 0)
    (Q : MvPolynomial O k) :
    generic q P hP (ofPolynomial q P Q) = MvPolynomial.aeval q Q := by
  exact generic_of q P hP (polynomial q Q)

theorem generic_injective (hP : MvPolynomial.aeval q P ≠ 0) :
    Function.Injective (generic q P hP) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers (polynomial q P)) (generic q P hP).toRingHom).mpr
  intro a b
  constructor
  · exact congrArg (generic q P hP)
  · intro he
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, generic_of] at he
    exact congrArg (algebraMap (CoordinateAlgebra (k := k) q) (OpenAlgebra q P)) (Subtype.ext he)

def point (z : O → k)
    (hz : ∀ Q : MvPolynomial O k, MvPolynomial.aeval q Q = 0 →
      MvPolynomial.aeval z Q = 0) : CoordinateAlgebra (k := k) q →ₐ[k] k :=
  AlgHom.liftOfSurjective (polynomial q) (MvPolynomial.aeval q).rangeRestrict_surjective
    (MvPolynomial.aeval z) (by
      intro Q hQ
      apply hz Q
      exact congrArg Subtype.val (RingHom.mem_ker.mp hQ))

@[simp] theorem point_polynomial (z : O → k)
    (hz : ∀ Q : MvPolynomial O k, MvPolynomial.aeval q Q = 0 →
      MvPolynomial.aeval z Q = 0) (Q : MvPolynomial O k) :
    point q z hz (polynomial q Q) = MvPolynomial.aeval z Q := by
  exact AlgHom.liftOfSurjective_apply _ _ _ _ Q

def openPoint (z : O → k)
    (hz : ∀ Q : MvPolynomial O k, MvPolynomial.aeval q Q = 0 →
      MvPolynomial.aeval z Q = 0)
    (hPz : MvPolynomial.aeval z P ≠ 0) : OpenAlgebra q P →ₐ[k] k :=
  IsLocalization.Away.liftAlgHom (polynomial q P)
    (show IsUnit (point q z hz (polynomial q P)) by
      rw [point_polynomial]
      exact IsUnit.mk0 _ hPz)

@[simp] theorem openPoint_ofPolynomial (z : O → k)
    (hz : ∀ Q : MvPolynomial O k, MvPolynomial.aeval q Q = 0 →
      MvPolynomial.aeval z Q = 0)
    (hPz : MvPolynomial.aeval z P ≠ 0) (Q : MvPolynomial O k) :
    openPoint q P z hz hPz (ofPolynomial q P Q) = MvPolynomial.aeval z Q := by
  simp [openPoint, ofPolynomial]

theorem isUnit_ofPolynomial (Q : MvPolynomial O k) (hQ : Q ∣ P) :
    IsUnit (ofPolynomial q P Q) :=
  IsLocalization.Away.isUnit_of_dvd (polynomial q P) (map_dvd (polynomial q) hQ)

end Sunlet.ImageLocalization

end GenericSource_ImageLocalization

#check "SUNLET_ImageLocalization_READY"


section GenericSource_QuadraticImageOpen
open scoped BigOperators

namespace Sunlet.ToricPairAlgebra

variable {k Ω ι : Type*} [Field k] [CharZero k]
  [Fintype Ω] [Fintype ι] [DecidableEq Ω] [DecidableEq ι]
  (o : Ω) (π : ι → Equiv.Perm Ω)

def imageFieldCoordinate (i : ι × Ω) :
    JacobianFinite.generatedField (genericCoordinates (k := k) o π) :=
  ⟨genericCoordinates (k := k) o π i, JacobianFinite.coordinate_mem_generatedField _ i⟩

theorem imageFieldCoordinate_aeval (P : MvPolynomial (ι × Ω) k) :
    (JacobianFinite.generatedField (genericCoordinates (k := k) o π)).val
      (MvPolynomial.aeval (imageFieldCoordinate (k := k) o π) P) =
        MvPolynomial.aeval (genericCoordinates (k := k) o π) P := by
  rw [MvPolynomial.comp_aeval_apply]
  rfl

namespace PivotRecovery

variable {o π} {p : ι × Ω} (D : PivotRecovery (k := k) o π p)

abbrev CoefficientRing :=
  ImageLocalization.OpenAlgebra (imageFieldCoordinate (k := k) o π) D.openPolynomial

theorem openPolynomial_imageField_ne :
    MvPolynomial.aeval (imageFieldCoordinate (k := k) o π) D.openPolynomial ≠ 0 := by
  intro he
  have hh := congrArg
    (JacobianFinite.generatedField (genericCoordinates (k := k) o π)).val he
  rw [map_zero, imageFieldCoordinate_aeval] at hh
  exact D.openPolynomial_generic_ne hh

def coefficientGeneric : D.CoefficientRing →ₐ[k]
    JacobianFinite.generatedField (genericCoordinates (k := k) o π) :=
  ImageLocalization.generic _ D.openPolynomial D.openPolynomial_imageField_ne

def ambientGeneric : D.CoefficientRing →ₐ[k] FunctionField (k := k) (ι := ι) o :=
  (JacobianFinite.generatedField (genericCoordinates (k := k) o π)).val.comp D.coefficientGeneric

def polynomialInRing : MvPolynomial (ι × Ω) k →ₐ[k] D.CoefficientRing :=
  ImageLocalization.ofPolynomial _ D.openPolynomial

@[simp] theorem ambientGeneric_polynomial (P : MvPolynomial (ι × Ω) k) :
    D.ambientGeneric (D.polynomialInRing P) =
      MvPolynomial.aeval (genericCoordinates (k := k) o π) P := by
  change (JacobianFinite.generatedField (genericCoordinates (k := k) o π)).val
      (ImageLocalization.generic _ D.openPolynomial D.openPolynomial_imageField_ne
        (ImageLocalization.ofPolynomial _ D.openPolynomial P)) = _
  rw [ImageLocalization.generic_ofPolynomial, imageFieldCoordinate_aeval]

def denominatorUnit (i : ι × Ω) : D.CoefficientRingˣ :=
  (ImageLocalization.isUnit_ofPolynomial (imageFieldCoordinate (k := k) o π) D.openPolynomial
    (D.denominator i) (by
      exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem D.denominator (Finset.mem_univ i)) _)).unit

def numeratorPivotUnit : D.CoefficientRingˣ :=
  (ImageLocalization.isUnit_ofPolynomial (imageFieldCoordinate (k := k) o π) D.openPolynomial
    (D.numerator p) (dvd_mul_right _ _)).unit

@[simp] theorem denominatorUnit_val (i : ι × Ω) :
    (D.denominatorUnit i).val = D.polynomialInRing (D.denominator i) :=
  IsUnit.unit_spec _

@[simp] theorem numeratorPivotUnit_val :
    D.numeratorPivotUnit.val = D.polynomialInRing (D.numerator p) :=
  IsUnit.unit_spec _

def ratioInRing (i : ι × Ω) : D.CoefficientRing :=
  D.polynomialInRing (D.numerator i) * ((D.denominatorUnit i)⁻¹).val

def pivotUnit : D.CoefficientRingˣ := D.numeratorPivotUnit * (D.denominatorUnit p)⁻¹

@[simp] theorem pivotUnit_val : D.pivotUnit.val = D.ratioInRing p := by
  simp [pivotUnit, ratioInRing]

theorem ambientGeneric_ratio (i : ι × Ω) :
    D.ambientGeneric (D.ratioInRing i) = genericDifference (k := k) o π p * genericDifference (k := k) o π i := by
  rw [ratioInRing, map_mul, map_units_inv, denominatorUnit_val,
    ambientGeneric_polynomial, ambientGeneric_polynomial]
  change MvPolynomial.aeval (genericCoordinates (k := k) o π) (D.numerator i) /
      MvPolynomial.aeval (genericCoordinates (k := k) o π) (D.denominator i) = _
  apply (div_eq_iff (D.denominator_ne i)).mpr
  simpa only [mul_comm] using (D.relation i).symm

set_option maxHeartbeats 800000 in
/-- This existence statement is on the whole algebraic image closure,
not merely on the parameterized image or its torus points. -/
theorem exists_pair_on_open [IsAlgClosed k]
    (hnot : genericDifference (k := k) o π p ∉
      JacobianFinite.generatedField (genericCoordinates (k := k) o π))
    (z : ι × Ω → k) (hz : z ∈ secantClosure (k := k) o π)
    (hPz : MvPolynomial.aeval z D.openPolynomial ≠ 0) :
    ∃ x ∈ toricClosure (k := k) o π, ∃ y ∈ toricClosure (k := k) o π, x + y = z := by
  let E := FunctionField (k := k) (ι := ι) o
  let F := JacobianFinite.generatedField (genericCoordinates (k := k) o π)
  let R := D.CoefficientRing
  let g : R →ₐ[k] F := D.coefficientGeneric
  let gE : R →ₐ[k] E := D.ambientGeneric
  letI : Algebra R F := g.toRingHom.toAlgebra
  letI : Algebra R E := gE.toRingHom.toAlgebra
  letI : IsScalarTower k R F := IsScalarTower.of_algHom g
  letI : IsScalarTower k R E := IsScalarTower.of_algHom gE
  letI : IsScalarTower R F E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hginj : Function.Injective (algebraMap R F) :=
    ImageLocalization.generic_injective _ _ D.openPolynomial_imageField_ne
  have hnot' : genericDifference (k := k) o π p ∉ Set.range (algebraMap F E) := by
    rintro ⟨a, ha⟩
    exact hnot (ha ▸ a.property)
  have hz' : ∀ Q : MvPolynomial (ι × Ω) k,
      MvPolynomial.aeval (imageFieldCoordinate (k := k) o π) Q = 0 →
        MvPolynomial.aeval z Q = 0 := by
    intro Q hQ
    rw [secantClosure_eq_generic_zeroLocus] at hz
    apply hz Q
    have hh := congrArg F.val hQ
    rw [map_zero, imageFieldCoordinate_aeval] at hh
    exact hh
  let φ : R →ₐ[k] k := ImageLocalization.openPoint _ D.openPolynomial z hz' hPz
  let qR : ι × Ω → R := fun i => D.polynomialInRing (MvPolynomial.X i)
  have hq : ∀ i, algebraMap R E (qR i) =
      genericPoint (k := k) o π false i + genericPoint (k := k) o π true i := by
    intro i
    change D.ambientGeneric (D.polynomialInRing (MvPolynomial.X i)) = _
    rw [ambientGeneric_polynomial, MvPolynomial.aeval_X]
    rfl
  have hr : ∀ i, algebraMap R E (D.ratioInRing i) =
      genericDifference (k := k) o π p * (genericPoint (k := k) o π false i - genericPoint (k := k) o π true i) :=
    D.ambientGeneric_ratio
  have ht : genericDifference (k := k) o π p ^ 2 = algebraMap R E D.pivotUnit.val := by
    change _ = D.ambientGeneric D.pivotUnit.val
    rw [pivotUnit_val, ambientGeneric_ratio, pow_two]
  obtain ⟨x, y, hs, hx, hy⟩ := QuadraticReconstruction.exists_specialized_pair
    (k := k) (R := R) (F := F) (E := E) hginj D.pivotUnit qR D.ratioInRing
    (genericPoint (k := k) o π false) (genericPoint (k := k) o π true) (genericDifference (k := k) o π p)
    ht hnot' hq hr φ
  refine ⟨x, ?_, y, ?_, ?_⟩
  · rw [toricClosure_eq_generic_zeroLocus]
    intro Q hQ
    exact hx Q hQ
  · rw [toricClosure_eq_generic_zeroLocus]
    intro Q hQ
    apply hy Q
    exact (generic_point_equation_iff o π true Q).mpr
      ((generic_point_equation_iff o π false Q).mp hQ)
  · funext i
    have hh := hs i
    change x i + y i = φ (qR i) at hh
    change x i + y i = z i
    rw [show φ (qR i) = z i from by
      exact (ImageLocalization.openPoint_ofPolynomial _ D.openPolynomial z hz' hPz
        (MvPolynomial.X i)).trans (MvPolynomial.aeval_X z i)] at hh
    exact hh

end PivotRecovery

end Sunlet.ToricPairAlgebra

end GenericSource_QuadraticImageOpen

#check "SUNLET_QuadraticImageOpen_READY"


section GenericSource_RationalBaseChange

namespace Sunlet.RationalBaseChange

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {k E O J : Type*} [Field k] [Field E] [Algebra k E]
  [DecidableEq J] (q : O → E) (target : O → J)

abbrev OriginalField := IntermediateField.adjoin k (Set.range q)
abbrev ExtendedBase := FractionRing (MvPolynomial J (OriginalField (k := k) q))

local instance polynomialBaseToExtendedFaithful :
    FaithfulSMul (MvPolynomial J (OriginalField (k := k) q))
      (ExtendedField (E := E) (J := J)) := by
  apply (faithfulSMul_iff_algebraMap_injective
    (MvPolynomial J (OriginalField (k := k) q))
    (ExtendedField (E := E) (J := J))).mpr
  change Function.Injective ((algebraMap (MvPolynomial J E)
    (ExtendedField (E := E) (J := J))).comp
    (MvPolynomial.map (algebraMap (OriginalField (k := k) q) E)))
  exact (IsFractionRing.injective (MvPolynomial J E)
    (ExtendedField (E := E) (J := J))).comp
    (MvPolynomial.map_injective _ (algebraMap (OriginalField (k := k) q) E).injective)

local instance baseExtendedAlgebra :
    Algebra (ExtendedBase (k := k) (J := J) q) (ExtendedField (E := E) (J := J)) :=
  FractionRing.liftAlgebra (MvPolynomial J (OriginalField (k := k) q))
    (ExtendedField (E := E) (J := J))

local instance polynomialGroundTower :
    IsScalarTower k (MvPolynomial J (OriginalField (k := k) q))
      (ExtendedField (E := E) (J := J)) := by
  apply IsScalarTower.of_algebraMap_eq
  intro c
  change algebraMap k (ExtendedField (E := E) (J := J)) c =
    algebraMap (MvPolynomial J E) (ExtendedField (E := E) (J := J))
      (MvPolynomial.map (algebraMap (OriginalField (k := k) q) E)
        (MvPolynomial.C (algebraMap k (OriginalField (k := k) q) c)))
  rw [MvPolynomial.map_C, ← IsScalarTower.algebraMap_apply k (OriginalField (k := k) q) E]
  rfl

local instance baseGroundTower :
    IsScalarTower k (ExtendedBase (k := k) (J := J) q)
      (ExtendedField (E := E) (J := J)) :=
  IsScalarTower.to₁₃₄ k (MvPolynomial J (OriginalField (k := k) q))
    (ExtendedBase (k := k) (J := J) q) (ExtendedField (E := E) (J := J))

def baseEmbedding : ExtendedBase (k := k) (J := J) q →ₐ[k] ExtendedField (E := E) (J := J) :=
  IsScalarTower.toAlgHom k _ _

theorem baseEmbedding_constant (a : OriginalField (k := k) q) :
    baseEmbedding (k := k) (J := J) q (algebraMap (OriginalField (k := k) q) (ExtendedBase (k := k) (J := J) q) a) =
      algebraMap E (ExtendedField (J := J)) a.val := by
  change baseEmbedding (k := k) (J := J) q
    (algebraMap (MvPolynomial J (OriginalField (k := k) q))
      (ExtendedBase (k := k) (J := J) q) (MvPolynomial.C a)) = _
  change algebraMap (ExtendedBase (k := k) (J := J) q) (ExtendedField (E := E) (J := J))
    (algebraMap (MvPolynomial J (OriginalField (k := k) q))
      (ExtendedBase (k := k) (J := J) q) (MvPolynomial.C a)) = _
  rw [← IsScalarTower.algebraMap_apply
    (MvPolynomial J (OriginalField (k := k) q))
    (ExtendedBase (k := k) (J := J) q) (ExtendedField (E := E) (J := J))]
  change algebraMap (MvPolynomial J E) (ExtendedField (E := E) (J := J))
    (MvPolynomial.map (algebraMap (OriginalField (k := k) q) E) (MvPolynomial.C a)) = _
  rw [MvPolynomial.map_C]
  rfl

theorem baseEmbedding_variable (j : J) :
    baseEmbedding (k := k) (J := J) q
      (algebraMap (MvPolynomial J (OriginalField (k := k) q)) (ExtendedBase (k := k) (J := J) q)
        (MvPolynomial.X j)) = diagonal (E := E) j := by
  change algebraMap (ExtendedBase (k := k) (J := J) q) (ExtendedField (E := E) (J := J))
      (algebraMap (MvPolynomial J (OriginalField (k := k) q)) (ExtendedBase (k := k) (J := J) q)
        (MvPolynomial.X j)) = _
  rw [← IsScalarTower.algebraMap_apply
      (MvPolynomial J (OriginalField (k := k) q))
      (ExtendedBase (k := k) (J := J) q) (ExtendedField (E := E) (J := J)),
    IsScalarTower.algebraMap_apply (MvPolynomial J (OriginalField (k := k) q))
      (MvPolynomial J E) (ExtendedField (E := E) (J := J))]
  change algebraMap (MvPolynomial J E) (ExtendedField (E := E) (J := J))
    (MvPolynomial.map (algebraMap (OriginalField (k := k) q) E) (MvPolynomial.X j)) = _
  rw [MvPolynomial.map_X]
  rfl

theorem diagonal_mem (j : J) : diagonal (E := E) j ∈ ImageField (k := k) q target :=
  IntermediateField.subset_adjoin k _ ⟨Sum.inl j, rfl⟩

theorem original_coordinate_mem (i : O) :
    algebraMap E (ExtendedField (J := J)) (q i) ∈ ImageField (k := k) q target := by
  have hc : coordinates q target (Sum.inr i) ∈ ImageField (k := k) q target :=
    IntermediateField.subset_adjoin k _ ⟨Sum.inr i, rfl⟩
  have hh := (ImageField (k := k) q target).div_mem hc (diagonal_mem q target (target i))
  simpa only [coordinates, mul_div_cancel_left₀ _ (diagonal_ne_zero (E := E) (target i))] using hh

theorem original_field_mem (a : OriginalField (k := k) q) :
    algebraMap E (ExtendedField (J := J)) a.val ∈ ImageField (k := k) q target := by
  refine IntermediateField.adjoin_induction k
    (motive := fun x _ => algebraMap E (ExtendedField (J := J)) x ∈ ImageField (k := k) q target)
    ?_ ?_ ?_ ?_ ?_ a.property
  · rintro _ ⟨i, rfl⟩
    exact original_coordinate_mem q target i
  · intro c
    rw [← IsScalarTower.algebraMap_apply k E (ExtendedField (J := J))]
    exact (ImageField (k := k) q target).algebraMap_mem c
  · intro x y _ _ hx hy
    simpa only [map_add] using (ImageField (k := k) q target).add_mem hx hy
  · intro x _ hx
    simpa only [map_inv₀] using (ImageField (k := k) q target).inv_mem hx
  · intro x y _ _ hx hy
    simpa only [map_mul] using (ImageField (k := k) q target).mul_mem hx hy

/-- Exact equality with the field generated by the literal normalized
coordinate functions, including the scaled off-diagonal entries. -/
theorem imageField_eq_range :
    ImageField (k := k) q target = (baseEmbedding (k := k) (J := J) q).fieldRange := by
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨j | i, rfl⟩
    · exact ⟨_, baseEmbedding_variable q j⟩
    · let a : OriginalField (k := k) q := ⟨q i,
        IntermediateField.subset_adjoin k _ ⟨i, rfl⟩⟩
      have hz : diagonal (E := E) (target i) ∈ (baseEmbedding (k := k) (J := J) q).fieldRange :=
        ⟨_, baseEmbedding_variable q (target i)⟩
      have hq : algebraMap E (ExtendedField (J := J)) (q i) ∈
          (baseEmbedding (k := k) (J := J) q).fieldRange :=
        ⟨_, baseEmbedding_constant q a⟩
      exact (baseEmbedding (k := k) (J := J) q).fieldRange.mul_mem hz hq
  · rintro x ⟨a, rfl⟩
    have hp : ∀ p : MvPolynomial J (OriginalField (k := k) q),
        baseEmbedding (k := k) (J := J) q
          (algebraMap (MvPolynomial J (OriginalField (k := k) q)) (ExtendedBase (k := k) (J := J) q) p) ∈
            ImageField (k := k) q target := by
      intro p
      induction p using MvPolynomial.induction_on with
      | C a =>
          change baseEmbedding (k := k) (J := J) q
            (algebraMap (OriginalField (k := k) q) (ExtendedBase (k := k) (J := J) q) a) ∈ _
          rw [baseEmbedding_constant]
          exact original_field_mem q target a
      | add p r hp hr =>
          simpa only [map_add] using (ImageField (k := k) q target).add_mem hp hr
      | mul_X p j hp =>
          simpa only [map_mul, baseEmbedding_variable] using
            (ImageField (k := k) q target).mul_mem hp (diagonal_mem q target j)
    obtain ⟨p, r, _, rfl⟩ := IsFractionRing.div_surjective
      (MvPolynomial J (OriginalField (k := k) q)) a
    change baseEmbedding (k := k) (J := J) q
      (algebraMap (MvPolynomial J (OriginalField (k := k) q)) _ p /
        algebraMap (MvPolynomial J (OriginalField (k := k) q)) _ r) ∈ _
    rw [map_div₀]
    exact (ImageField (k := k) q target).div_mem (hp p) (hp r)

theorem finrank_eq [Algebra.IsAlgebraic (OriginalField (k := k) q) E] :
    Module.finrank (ImageField (k := k) q target) (ExtendedField (E := E) (J := J)) =
      Module.finrank (OriginalField (k := k) q) E := by
  rw [imageField_eq_range]
  have he := Algebra.finrank_eq_of_equiv_equiv
    (baseEmbedding (k := k) (J := J) q).equivFieldRange.toRingEquiv
    (RingEquiv.refl (ExtendedField (E := E) (J := J))) (by ext a; rfl)
  rw [← he]
  unfold Module.finrank
  rw [Algebra.IsAlgebraic.rank_fractionRing_mvPolynomial]
  simp

def extendAutomorphism (σ : E ≃ₐ[k] E) :
    ExtendedField (E := E) (J := J) ≃ₐ[k] ExtendedField (E := E) (J := J) :=
  IsFractionRing.algEquivOfAlgEquiv (MvPolynomial.mapAlgEquiv J σ)

@[simp] theorem extendAutomorphism_diagonal (σ : E ≃ₐ[k] E) (j : J) :
    extendAutomorphism (J := J) σ (diagonal j) = diagonal j := by
  rw [extendAutomorphism, diagonal, IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  simp [MvPolynomial.mapAlgEquiv_apply]

@[simp] theorem extendAutomorphism_constant (σ : E ≃ₐ[k] E) (x : E) :
    extendAutomorphism (J := J) σ (algebraMap E (ExtendedField (J := J)) x) =
      algebraMap E (ExtendedField (J := J)) (σ x) := by
  change extendAutomorphism (J := J) σ
    (algebraMap (MvPolynomial J E) _ (MvPolynomial.C x)) = _
  rw [extendAutomorphism, IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  simp [MvPolynomial.mapAlgEquiv_apply]
  rfl

theorem extended_algEquiv_ext
    {σ τ : ExtendedField (E := E) (J := J) ≃ₐ[k] ExtendedField (E := E) (J := J)}
    (hc : ∀ x : E, σ (algebraMap E _ x) = τ (algebraMap E _ x))
    (hz : ∀ j : J, σ (diagonal j) = τ (diagonal j)) : σ = τ := by
  have hh : σ.toAlgHom = τ.toAlgHom := by
    apply IsLocalization.algHom_ext (nonZeroDivisors (MvPolynomial J E))
    apply AlgHom.toRingHom_injective
    apply MvPolynomial.ringHom_ext
    · exact hc
    · exact hz
  ext x
  exact congrArg (fun f : ExtendedField (E := E) (J := J) →ₐ[k]
    ExtendedField (E := E) (J := J) => f x) hh

def extendHom : (E ≃ₐ[k] E) →*
    (ExtendedField (E := E) (J := J) ≃ₐ[k] ExtendedField (E := E) (J := J)) where
  toFun := extendAutomorphism
  map_one' := by
    apply extended_algEquiv_ext (k := k) (E := E) (J := J)
    · intro x; simp
    · intro j; simp
  map_mul' σ τ := by
    apply extended_algEquiv_ext (k := k) (E := E) (J := J)
    · intro x; simp
    · intro j; simp

theorem extendAutomorphism_injective :
    Function.Injective (extendAutomorphism (k := k) (E := E) (J := J)) := by
  intro σ τ he
  ext x
  apply (algebraMap E (ExtendedField (E := E) (J := J))).injective
  have hh := congrArg (fun f : ExtendedField (E := E) (J := J) ≃ₐ[k]
    ExtendedField (E := E) (J := J) => f (algebraMap E _ x)) he
  simpa only [extendAutomorphism_constant] using hh

theorem extendAutomorphism_coordinates (σ : E ≃ₐ[k] E) (hσ : ∀ i, σ (q i) = q i)
    (j : J ⊕ O) :
    extendAutomorphism (J := J) σ (coordinates q target j) = coordinates q target j := by
  cases j with
  | inl j => exact extendAutomorphism_diagonal σ j
  | inr i => simp [coordinates, hσ]

end Sunlet.RationalBaseChange

end GenericSource_RationalBaseChange

#check "SUNLET_RationalBaseChange_READY"

#check @Sunlet.ToricPairAlgebra.unordered_under_embedding_arbitrary_ambient
#print axioms Sunlet.ToricPairAlgebra.unordered_under_embedding_arbitrary_ambient
#check @Sunlet.ToricPairAlgebra.differenceProduct_mem_generatedField
#print axioms Sunlet.ToricPairAlgebra.differenceProduct_mem_generatedField
#check @Sunlet.ToricPairAlgebra.exists_pivotRecovery_of_witness
#print axioms Sunlet.ToricPairAlgebra.exists_pivotRecovery_of_witness
#check @Sunlet.ToricPairAlgebra.PivotRecovery.unique_unordered_on_open
#print axioms Sunlet.ToricPairAlgebra.PivotRecovery.unique_unordered_on_open
#check @Sunlet.ToricPairAlgebra.PivotRecovery.exists_pair_on_open
#print axioms Sunlet.ToricPairAlgebra.PivotRecovery.exists_pair_on_open
#check @Sunlet.ToricPairAlgebra.closure_principalOpen
#print axioms Sunlet.ToricPairAlgebra.closure_principalOpen
#check @Sunlet.RationalBaseChange.finrank_eq
#print axioms Sunlet.RationalBaseChange.finrank_eq
