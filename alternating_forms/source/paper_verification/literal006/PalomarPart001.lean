module

public import paper_verification.literal006.PalomarPart000
import all paper_verification.literal006.PalomarPart000
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.RepresentationTheory.Intertwining
public import paper_verification.literal003
public import paper_verification.literal005
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.Basis.Prod
import Lean.Elab.Tactic.Omega
public import paper_verification.literal001
public import paper_verification.literal000
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
public import Mathlib.Analysis.Normed.Module.RCLike.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.JointEigenspace
public import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Analysis.CStarAlgebra.Fuglede
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Tactic.Module
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.LinearAlgebra.Matrix.IsDiag
import paper_verification.literal005
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Dimension.LinearMap
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Set.Card
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import Mathlib.LinearAlgebra.Eigenspace.Matrix
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.LinearAlgebra.Matrix.MvPolynomial
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Separation.Connected
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorPower.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.LinearAlgebra.PiTensorProduct.Finite
public import Mathlib.RepresentationTheory.Character
public import Mathlib.LinearAlgebra.TensorProduct.Matrix
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Algebra.CharP.Two
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Data.Int.GCD
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RepresentationTheory.Semisimple
public import paper_verification.literal002
public import Mathlib.RingTheory.SimpleModule.Rank
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.MvPolynomial
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.Data.Matrix.Basis
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Matrix.Mul
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Basis.SMul
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option Elab.async false

section TAF_LiteralSource_0395
/- Original module: TauCeti.RepresentationTheory.Irreducible -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Criteria for irreducibility

This file collects criteria for recognising irreducible representations without inspecting their
subrepresentations one by one, together with existence, density, and Schur lemmas for
finite-dimensional representations.

A representation on a one-dimensional vector space is irreducible, whatever the group and however
it acts: a subrepresentation is in particular a subspace, and a line has only the two trivial
subspaces.  Nontriviality, the other half of irreducibility, is the same dimension count.  This is
how the smallest representations of a group are recognised as irreducible without knowing anything
about the group -- the trivial representation, a character, a sign.

The second criterion turns a lattice-theoretic statement about a fixed ambient representation into
a statement about a subrepresentation on its own: a subrepresentation that is an **atom** of the
lattice of subrepresentations carries an irreducible representation.  Irreducibility of a
subrepresentation `σ` of `ρ` is a statement about the subrepresentations of `σ.toRepresentation`,
one level down from `ρ`, whereas minimality is a statement inside the lattice attached to `ρ`; the
translation between them is the correspondence sending a subrepresentation of `σ.toRepresentation`
to its image in `ρ` under the inclusion of `σ.toSubmodule`.  In practice the atom form is the one
that gets proved -- one exhibits an invariant subspace of the ambient representation and shows it
has no proper nonzero invariant subspace -- and the irreducibility form is the one that gets used.

At the other extreme, a representation whose algebra map exhausts `End k V` is irreducible, because
a vector space is a simple module over its own endomorphism ring, so a nonzero vector can be carried
to any other.  This is the criterion a matrix block of a semisimple group algebra is recognised as
irreducible by.

## Main results

* `Representation.IsIrreducible.nontrivial`: an irreducible representation has a nonzero
  carrier.
* `Representation.IsIrreducible.finrank_pos`: a finite-dimensional irreducible
  representation has positive dimension.
* `Representation.IsIrreducible.natCast_finrank_ne_zero`: in characteristic zero that
  dimension is nonzero, hence invertible, in the base field.
* `Representation.isIrreducible_of_finrank_eq_one`: a line is irreducible.
* `Representation.isIrreducible_of_linearEquiv`: irreducibility transports along an
  equivariant linear equivalence.
* `Representation.isIrreducible_toRepresentation_of_isAtom`: an atom of the lattice of
  subrepresentations carries an irreducible representation.
* `Representation.isIrreducible_of_asAlgebraHom_surjective`: a representation whose
  algebra map exhausts the endomorphisms is irreducible.
* `Representation.isIrreducible_of_finrank_intertwiningMap_self_eq_one`: a semisimple
  representation whose equivariant endomorphisms are the scalars is irreducible.
* `Representation.IsIrreducible.eq_one_or_eq_neg_one_of_mul_self_eq_one`: Schur's lemma for an
  involutive equivariant endomorphism, over any field.
* `Representation.asAlgebraHom_surjective_of_isIrreducible`: over an algebraically closed
  field, every finite-dimensional irreducible representation exhausts the endomorphisms.
* `Representation.exists_ne_zero_forall_exists_rTensor_asAlgebraHom_eq_tmul`: consequently the
  monoid algebra, acting on the left factor of a nonzero tensor in `V ⊗ M`, reaches every
  `v ⊗ m` for one fixed nonzero `m`.
* `Representation.exists_isAtom_le`: every nonzero finite-dimensional subrepresentation
  contains an atom, so the atom criterion always has something to apply to.
* `Representation.exists_isAtom`: in particular a nonzero finite-dimensional
  representation has an atom.
* `Representation.exists_isIrreducible_subrepresentation`: consequently every nonzero
  finite-dimensional representation contains an irreducible subrepresentation.
* `Representation.IsIrreducible.exists_forall_apply_eq_smul`: Schur's lemma over an
  algebraically closed field, for an unbundled equivariant endomorphism.
* `Representation.IsIrreducible.exists_unit_smul_of_intertwines`: two equivariant isomorphisms
  out of an irreducible representation differ by a unit scalar.
-/

public section

open TauCeti
open scoped TensorProduct

namespace Representation

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]

open scoped MonoidAlgebra in
/-- **An irreducible representation has a nonzero carrier.** This is `IsSimpleModule.nontrivial`
for `ρ.asModule`, read back on `V` along `ρ.asModuleEquiv`; the Mathlib statement is not an
instance, so nothing supplies `Nontrivial V` without naming it. -/
theorem IsIrreducible.nontrivial {ρ : Representation k G V}
    (h : ρ.IsIrreducible) : Nontrivial V :=
  have _ : ρ.IsIrreducible := h
  have _ := IsSimpleModule.nontrivial k[G] ρ.asModule
  ρ.asModuleEquiv.symm.toEquiv.nontrivial

/-- **A finite-dimensional irreducible representation has positive dimension.** This is what makes
the degree of an irreducible character positive, and, cast into the base field by
`Representation.IsIrreducible.natCast_finrank_ne_zero`, what lets the orthogonality relations and
the integrated operator divide by that degree. -/
theorem IsIrreducible.finrank_pos [FiniteDimensional k V]
    {ρ : Representation k G V} (h : ρ.IsIrreducible) : 0 < Module.finrank k V :=
  have := h.nontrivial
  Module.finrank_pos

/-- **The dimension of an irreducible representation is nonzero in the base field.** In
characteristic zero it is therefore invertible there: this is the scalar the orthogonality
relations and the integrated operator of an irreducible representation are normalised by. -/
theorem IsIrreducible.natCast_finrank_ne_zero [CharZero k]
    [FiniteDimensional k V] {ρ : Representation k G V} (h : ρ.IsIrreducible) :
    (Module.finrank k V : k) ≠ 0 :=
  Nat.cast_ne_zero.mpr h.finrank_pos.ne'

/-- A representation on a one-dimensional vector space is irreducible. -/
theorem isIrreducible_of_finrank_eq_one (ρ : Representation k G V)
    (h : Module.finrank k V = 1) : ρ.IsIrreducible := by
  have : IsSimpleModule k V := isSimpleModule_iff_finrank_eq_one.mpr h
  have : Nontrivial V := IsSimpleModule.nontrivial k V
  refine ⟨fun σ => (eq_bot_or_eq_top σ.toSubmodule).imp (fun hσ => ?_) fun hσ => ?_⟩
  · exact Subrepresentation.toSubmodule_injective (hσ.trans Subrepresentation.toSubmodule_bot.symm)
  · exact Subrepresentation.toSubmodule_injective (hσ.trans Subrepresentation.toSubmodule_top.symm)

/-- The trivial representation of a monoid on the base field is irreducible, being a line. -/
instance isIrreducible_trivial_self : (trivial k G k).IsIrreducible :=
  isIrreducible_of_finrank_eq_one _ (Module.finrank_self k)

/-- **Irreducibility transports along an equivariant linear equivalence.** A linear equivalence
intertwining two representations matches their lattices of subrepresentations, by taking preimages
of invariant subspaces, so one is irreducible exactly when the other is.

Only one direction is stated; the reverse is this one applied to `e.symm`. -/
theorem isIrreducible_of_linearEquiv {W : Type*} [AddCommGroup W] [Module k W]
    {ρ : Representation k G V} {σ : Representation k G W} (e : V ≃ₗ[k] W)
    (he : ∀ g v, e (ρ g v) = σ g (e v)) (h : ρ.IsIrreducible) : σ.IsIrreducible := by
  have := h.nontrivial
  have : Nontrivial W := e.symm.toEquiv.nontrivial
  refine ⟨fun τ => ?_⟩
  -- pull `τ` back along `e` to a subrepresentation of `ρ`
  let τ' : Subrepresentation ρ :=
    { toSubmodule := τ.toSubmodule.comap (e : V →ₗ[k] W)
      apply_mem_toSubmodule g v hv := by
        simp only [Submodule.mem_comap, LinearEquiv.coe_coe] at hv ⊢
        rw [he]
        exact τ.apply_mem_toSubmodule g hv }
  have hmap : (τ'.toSubmodule).map (e : V →ₗ[k] W) = τ.toSubmodule :=
    Submodule.map_comap_eq_of_surjective e.surjective _
  refine (eq_bot_or_eq_top τ').imp (fun hτ => ?_) fun hτ => ?_
  · refine Subrepresentation.toSubmodule_injective ?_
    rw [← hmap, hτ, Subrepresentation.toSubmodule_bot, Submodule.map_bot,
      Subrepresentation.toSubmodule_bot]
  · refine Subrepresentation.toSubmodule_injective ?_
    rw [← hmap, hτ, Subrepresentation.toSubmodule_top, Submodule.map_top, LinearEquiv.range,
      Subrepresentation.toSubmodule_top]

/-- A subrepresentation that is an **atom** of the lattice of subrepresentations -- nonzero, with
no subrepresentation strictly between it and zero -- carries an irreducible representation.  The
translation is the correspondence between the subrepresentations of `σ.toRepresentation` and the
subrepresentations of `ρ` contained in `σ`, given by pushing forward along the inclusion. -/
theorem isIrreducible_toRepresentation_of_isAtom {ρ : Representation k G V}
    {σ : Subrepresentation ρ} (h : IsAtom σ) : σ.toRepresentation.IsIrreducible := by
  rw [irreducible_iff_isSimpleModule_asModule,
    σ.asModuleEquivAsSubmodule.isSimpleModule_iff, Subrepresentation.isSimpleModule_asSubmodule_iff]
  exact h

/-- **A representation whose algebra map exhausts the endomorphisms is irreducible.** Every nonzero
vector then generates, because a vector space is a simple module over its endomorphism ring. -/
theorem isIrreducible_of_asAlgebraHom_surjective [Nontrivial V] (ρ : Representation k G V)
    (h : Function.Surjective ρ.asAlgebraHom) : ρ.IsIrreducible := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule,
    isSimpleModule_iff_toSpanSingleton_surjective]
  refine ⟨ρ.asModuleEquiv.toEquiv.nontrivial, fun x hx y => ?_⟩
  obtain ⟨T, hT⟩ := IsSimpleModule.toSpanSingleton_surjective (Module.End k V)
    (m := ρ.asModuleEquiv x) (by
      intro hz
      apply hx
      apply ρ.asModuleEquiv.injective
      simpa only [map_zero] using hz) (ρ.asModuleEquiv y)
  rw [LinearMap.toSpanSingleton_apply, Module.End.smul_def] at hT
  obtain ⟨r, rfl⟩ := h T
  refine ⟨r, ρ.asModuleEquiv.injective ?_⟩
  rw [LinearMap.toSpanSingleton_apply, Representation.asModuleEquiv_map_smul, hT]

/-- **A semisimple representation whose intertwiners are the scalars is irreducible.** If every
subrepresentation has an invariant complement and the equivariant endomorphisms of `ρ` form a line,
then `ρ` is irreducible: an idempotent equivariant endomorphism is a scalar `c` with `c * c = c`,
hence `0` or `1`, so `ρ` is indecomposable (`isIndecomposableModule_of_forall_isIdempotentElem`),
and an indecomposable semisimple module is simple (`IsIndecomposableModule.isSimpleModule`).

Over a field in which the order of a finite group is invertible every representation is semisimple
(Maschke), so there this is the converse of Schur's lemma for an absolutely irreducible
representation. -/
theorem isIrreducible_of_finrank_intertwiningMap_self_eq_one {ρ : Representation k G V}
    [ρ.IsSemisimpleRepresentation] (h : Module.finrank k (IntertwiningMap ρ ρ) = 1) :
    ρ.IsIrreducible := by
  have : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    have : Subsingleton (IntertwiningMap ρ ρ) :=
      ⟨fun f g => IntertwiningMap.ext (Subsingleton.elim _ _)⟩
    rw [Module.finrank_zero_of_subsingleton] at h
    exact zero_ne_one h
  have hid : (1 : IntertwiningMap ρ ρ) ≠ 0 := by
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    exact fun h0 => hv (by simpa using congrArg (fun f : IntertwiningMap ρ ρ => f v) h0)
  have : IsSemisimpleModule (MonoidAlgebra k G) ρ.asModule :=
    (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mp inferInstance
  have : Nontrivial ρ.asModule := ρ.asModuleEquiv.toEquiv.nontrivial
  rw [irreducible_iff_isSimpleModule_asModule]
  -- an idempotent endomorphism is a scalar `c` with `c * c = c`, hence `0` or `1`
  refine (isIndecomposableModule_of_forall_isIdempotentElem fun f hf => ?_).isSimpleModule
  let e := IntertwiningMap.equivAlgEnd (ρ := ρ)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hid).mp h (e.symm f)
  have hf' : f = algebraMap k _ c := by
    rw [← e.apply_symm_apply f, ← hc, ← AlgEquiv.commutes e, IntertwiningMap.algebraMap_apply]
  have hcc : IsIdempotentElem c := by
    refine smul_left_injective k hid ?_
    simpa [hf', IsIdempotentElem, ← map_mul, mul_smul] using congrArg e.symm hf
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp hcc with rfl | rfl
  · exact Or.inl (by simp [hf'])
  · exact Or.inr (by simp [hf'])

/-- **An involutive equivariant endomorphism of an irreducible representation is `±1`.** By Schur's
lemma the equivariant endomorphisms of an irreducible representation form a division ring, in which
`f * f = 1` forces `f = 1` or `f = -1`. No algebraic closure or finite dimension is needed. -/
theorem IsIrreducible.eq_one_or_eq_neg_one_of_mul_self_eq_one {ρ : Representation k G V}
    (hρ : ρ.IsIrreducible) {f : IntertwiningMap ρ ρ} (hf : f * f = 1) : f = 1 ∨ f = -1 := by
  classical
  let := hρ
  let e := IntertwiningMap.equivAlgEnd (ρ := ρ)
  have he : e f * e f = 1 := by rw [← map_mul, hf, map_one]
  exact (mul_self_eq_one_iff.mp he).imp
    (fun h ↦ e.injective (by simpa using h)) fun h ↦ e.injective (by simpa using h)

open scoped MonoidAlgebra in
/-- **Burnside density theorem.** The monoid algebra of a finite-dimensional irreducible
representation over an algebraically closed field exhausts the full endomorphism algebra.

Jacobson density gives all endomorphisms linear over the representation's commuting endomorphism
ring. Schur's lemma identifies that ring with the base field, so these are exactly the
`k`-linear endomorphisms. -/
theorem asAlgebraHom_surjective_of_isIrreducible
    [IsAlgClosed k] [FiniteDimensional k V]
    (ρ : Representation k G V) (hρ : ρ.IsIrreducible) :
    Function.Surjective ρ.asAlgebraHom := by
  have : ρ.IsIrreducible := hρ
  have : IsSimpleModule k[G] ρ.asModule := inferInstance
  have : Nontrivial ρ.asModule := IsSimpleModule.nontrivial k[G] ρ.asModule
  have : Nontrivial V := hρ.nontrivial
  have : Module.Finite (Module.End k[G] ρ.asModule) ρ.asModule :=
    Module.Finite.of_restrictScalars_finite k (Module.End k[G] ρ.asModule) ρ.asModule
  intro T
  let T' : Module.End (Module.End k[G] ρ.asModule) ρ.asModule :=
    { toFun := T
      map_add' := T.map_add
      map_smul' := fun f x ↦ by
        -- `T` acts on `V`, while `f` acts on the definitionally equal type synonym
        -- `ρ.asModule`; exposing function application is required before Schur's scalar
        -- description is type-correct.
        change T (f x) = f (T x)
        rw [← endAlgEquivSelfOfIsSimpleModule_smul (k := k) (A := k[G]) f x,
          ← endAlgEquivSelfOfIsSimpleModule_smul (k := k) (A := k[G]) f (T x)]
        exact T.map_smul _ _ }
  obtain ⟨a, ha⟩ :=
    Module.Finite.toModuleEnd_moduleEnd_surjective (R := k[G]) (M := ρ.asModule) T'
  refine ⟨a, LinearMap.ext fun x ↦ ?_⟩
  have hT' (y : ρ.asModule) : T' y = T y := rfl
  have hx := LinearMap.congr_fun ha (ρ.asModuleEquiv.symm x)
  rw [hT'] at hx
  have hx' := congrArg ρ.asModuleEquiv hx
  have hT_equiv : ρ.asModuleEquiv (T (ρ.asModuleEquiv.symm x)) = T x := rfl
  rw [hT_equiv] at hx'
  simpa only [Module.toModuleEnd_apply, DistribSMul.toLinearMap_apply,
    Representation.asModuleEquiv_map_smul, LinearEquiv.apply_symm_apply] using hx'

open scoped MonoidAlgebra in
/-- **Burnside density on a tensor product.** Let `ρ` be a finite-dimensional irreducible
representation over an algebraically closed field and `M` any vector space. Acting on the left
factor of a nonzero `z ∈ V ⊗ M` by the monoid algebra reaches every pure tensor `v ⊗ m` with one
fixed nonzero `m`: there is `m ≠ 0` such that for each `v` some `r ∈ k[G]` has
`(ρ r ⊗ 1) z = v ⊗ m`. -/
theorem exists_ne_zero_forall_exists_rTensor_asAlgebraHom_eq_tmul
    [IsAlgClosed k] [FiniteDimensional k V] (ρ : Representation k G V) (hρ : ρ.IsIrreducible)
    {M : Type*} [AddCommGroup M] [Module k M] {z : V ⊗[k] M} (hz : z ≠ 0) :
    ∃ m : M, m ≠ 0 ∧ ∀ v : V, ∃ r : k[G], (ρ.asAlgebraHom r).rTensor M z = v ⊗ₜ m := by
  -- Some linear functional on `V` contracts `z` to a nonzero vector of `M`.
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual k V, _root_.TensorProduct.lid k M (f.rTensor M z) ≠ 0 := by
    by_contra! H
    apply hz
    apply tensor_eq_zero_of_forall_rTensor_eq_zero (fun f : Module.Dual k V ↦ f)
      (fun v hv ↦ (Module.forall_dual_apply_eq_zero_iff k v).1 hv) z
    intro f
    apply (_root_.TensorProduct.lid k M).injective
    simpa only [map_zero] using H f
  refine ⟨_, hf, fun v ↦ ?_⟩
  -- By density the rank-one endomorphism `x ↦ f x • v` is the action of some `r`.
  obtain ⟨r, hr⟩ := asAlgebraHom_surjective_of_isIrreducible ρ hρ (f.smulRight v)
  have key (w : V ⊗[k] M) :
      (f.smulRight v).rTensor M w = v ⊗ₜ _root_.TensorProduct.lid k M (f.rTensor M w) := by
    induction w using _root_.TensorProduct.inductionOn with
    | tmul x m => simp [_root_.TensorProduct.smul_tmul]
    | add w w' hw hw' => simp only [map_add, hw, hw', _root_.TensorProduct.tmul_add]
  exact ⟨r, by rw [hr, key]⟩

/-! ### Atoms exist in finite dimensions -/

section DivisionRing

variable {k G V : Type*} [DivisionRing k] [Monoid G] [AddCommGroup V] [Module k V]

/-- **Atoms exist.** Every nonzero finite-dimensional subrepresentation contains an atom of the
lattice of subrepresentations.

Finite-dimensionality is what makes a minimal nonzero subrepresentation exist, and only the
subrepresentation being minimised inside has to be finite-dimensional: the ambient representation
may be infinite-dimensional, the scalars need only be a division ring, and the acting monoid stays
arbitrary.  Over a field it combines with
`Representation.isIrreducible_toRepresentation_of_isAtom` to exhibit an irreducible
subrepresentation inside any nonzero one; that companion needs the field, because
`Representation.IsIrreducible` is defined only there. -/
theorem exists_isAtom_le {ρ : Representation k G V} {σ : Subrepresentation ρ}
    [FiniteDimensional k σ.toSubmodule] (hσ : σ ≠ ⊥) :
    ∃ τ : Subrepresentation ρ, τ ≤ σ ∧ IsAtom τ := by
  -- Among the nonzero subrepresentations contained in `σ`, pick one whose subspace has least
  -- dimension; the dimensions are natural numbers, so such a one exists.
  obtain ⟨τ, hmin⟩ :=
    exists_minimalFor_of_wellFoundedLT (fun τ : Subrepresentation ρ => τ ≠ ⊥ ∧ τ ≤ σ)
      (fun τ => Module.finrank k τ.toSubmodule) ⟨σ, hσ, le_rfl⟩
  obtain ⟨hτ, hτσ⟩ := hmin.1
  have : FiniteDimensional k τ.toSubmodule :=
    Submodule.finiteDimensional_of_le (Subrepresentation.toSubmodule_le_toSubmodule.mpr hτσ)
  -- Anything strictly inside `τ` is again inside `σ` and of strictly smaller dimension, so
  -- minimality forces it to be zero.
  refine ⟨τ, hτσ, hτ, fun υ hυ => ?_⟩
  by_contra hυ0
  exact hmin.not_prop_of_lt
    (Submodule.finrank_lt_finrank_of_lt (Subrepresentation.toSubmodule_lt_toSubmodule.mpr hυ))
    ⟨hυ0, hυ.le.trans hτσ⟩

/-- **A nonzero finite-dimensional representation has a minimal nonzero subrepresentation.**  This
is `Representation.exists_isAtom_le` applied to the whole space, which is nonzero exactly
because `V` is; the scalars need only be a division ring and the acting monoid stays arbitrary. -/
theorem exists_isAtom [FiniteDimensional k V] [Nontrivial V] (ρ : Representation k G V) :
    ∃ σ : Subrepresentation ρ, IsAtom σ :=
  let ⟨σ, _, hσ⟩ := exists_isAtom_le top_ne_bot
  ⟨σ, hσ⟩

end DivisionRing

/-- **Schur's lemma, scalar form.** Over an algebraically closed field, a linear endomorphism of a
finite-dimensional irreducible representation commuting with the action is multiplication by a
scalar.  This is `Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed`
read pointwise on an unbundled endomorphism. -/
theorem IsIrreducible.exists_forall_apply_eq_smul [IsAlgClosed k] [FiniteDimensional k V]
    {ρ : Representation k G V} [ρ.IsIrreducible] (f : V →ₗ[k] V)
    (hf : ∀ g v, f (ρ g v) = ρ g (f v)) : ∃ c : k, ∀ v, f v = c • v := by
  obtain ⟨c, hc⟩ := (IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
    (ρ := ρ)).surjective (f.intertwiningMap_of_isIntertwiningMap ρ ρ hf)
  refine ⟨c, fun v ↦ ?_⟩
  simpa [IntertwiningMap.algebraMap_apply] using (DFunLike.congr_fun hc v).symm

/-- **Two equivariant isomorphisms out of an irreducible representation differ by a unit
scalar.**  If `a b : V ≃ₗ[k] W` both carry the action `ρ` to the same `σ`, then `b⁻¹ ∘ a` is an
equivariant automorphism of `V`, hence a nonzero scalar by Schur's lemma
(`Representation.IsIrreducible.exists_forall_apply_eq_smul`). -/
theorem IsIrreducible.exists_unit_smul_of_intertwines [IsAlgClosed k] [FiniteDimensional k V]
    {W : Type*} [AddCommGroup W] [Module k W] {ρ : Representation k G V} [hρ : ρ.IsIrreducible]
    {σ : Representation k G W} (a b : V ≃ₗ[k] W)
    (ha : ∀ g v, a (ρ g v) = σ g (a v)) (hb : ∀ g v, b (ρ g v) = σ g (b v)) :
    ∃ c : kˣ, ∀ v, a v = (c : k) • b v := by
  have : Nontrivial V := hρ.nontrivial
  obtain ⟨c, hc⟩ := exists_forall_apply_eq_smul (ρ := ρ) (a.trans b.symm).toLinearMap
    fun g v ↦ b.injective (by simp [ha, hb])
  have hne : c ≠ 0 := by
    rintro rfl
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    exact hv ((a.trans b.symm).injective (by simpa using hc v))
  refine ⟨Units.mk0 c hne, fun v ↦ ?_⟩
  simpa using congrArg b (hc v)

/-- **Every nonzero finite-dimensional representation contains an irreducible subrepresentation.**
Finite-dimensionality alone suffices; no semisimplicity is assumed.  This produces a single
irreducible subrepresentation, not a decomposition: a representation that is not semisimple need
not be the sum of its irreducible subrepresentations. -/
theorem exists_isIrreducible_subrepresentation [FiniteDimensional k V] [Nontrivial V]
    (ρ : Representation k G V) :
    ∃ σ : Subrepresentation ρ, σ ≠ ⊥ ∧ σ.toRepresentation.IsIrreducible := by
  obtain ⟨σ, hσ⟩ := exists_isAtom ρ
  exact ⟨σ, hσ.1, isIrreducible_toRepresentation_of_isAtom hσ⟩

end Representation
end
end TAF_LiteralSource_0395

section TAF_LiteralSource_0396
/- Original module: TauCeti.RepresentationTheory.LinearCharacter.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# One-dimensional representations from linear characters

A **linear character** of a monoid `G` over a commutative semiring `k` is a multiplicative
character `χ : G →* kˣ`. It acts on the one-dimensional `k`-module `k` by scalar multiplication.
This file packages that action as `Representation.ofLinearCharacter χ`, bundles it as an object
`FDRep.ofLinearCharacter χ` of `FDRep k G`, and records the facts every consumer of a linear
character needs: over a field its character is `χ` and it is simple; over a commutative ring it
has rank one. Restriction along a homomorphism pulls `χ` back, and two of these representations
are isomorphic exactly when the two characters are equal.

The construction is the common core of the linear characters of the Borel subgroup and of
`GL₂`; keeping it here avoids separate scalar-action implementations for each group. It is also
the smallest nonzero representation over a field, and it is what the induction machinery is fed
in the classical worked examples: `Ind_H^G` of a linear character of a subgroup is a *monomial*
representation, and its irreducibility is what the Mackey criterion decides.

## Main definitions

* `Representation.ofLinearCharacter`: the one-dimensional representation associated to a
  unit-valued multiplicative character.
* `FDRep.ofLinearCharacter`: the same representation as an object of `FDRep k G`.

## Main results

* `Representation.ofLinearCharacter_apply`: the action is multiplication by the character value.
* `Representation.ofLinearCharacter_comp`: restriction of the representation is precomposition of
  the character.
* `Representation.ofLinearCharacter_injective`: the representation remembers its character.
* `Representation.ofLinearCharacter_one`: the trivial character carries the trivial
  representation.
* `Representation.char_ofLinearCharacter` and `FDRep.char_ofLinearCharacter`: the trace character
  is the original character, coerced into the coefficient field.
* `Representation.isIrreducible_ofLinearCharacter`: a line has no room for a proper nonzero
  subrepresentation.
* `Representation.IsIrreducible.nonempty_equiv_ofLinearCharacter_iff`: an irreducible
  representation is the line of `χ` exactly when each `g` acts by the scalar `χ g`.
* `FDRep.ofLinearCharacter_def`: the bundled representation is the unbundled one, bundled.
* `FDRep.finrank_ofLinearCharacter`: it is a line.
* `FDRep.simple_ofLinearCharacter`: it is a simple object of `FDRep k G`, being a line.
* `FDRep.actionRes_obj_ofLinearCharacter`: restricting along `f : S →* G` gives the
  one-dimensional representation of the pulled-back character `χ ∘ f`.
* `FDRep.nonempty_iso_ofLinearCharacter_iff`: two of these are isomorphic exactly when the two
  linear characters are equal.
* `FDRep.exists_character_eq_of_commute`: over an algebraically closed field, an irreducible
  representation whose operators commute pairwise has a linear character as its character.

## Implementation notes

Neither definition is exposed: consumers go through the lemmas rather than the body.
`FDRep.ofLinearCharacter_def` is the defining equation the dependent API is derived from, and with
Mathlib's `FDRep.of_ρ'` it recovers the action. Since both sides use the carrier `k`,
`FDRep.actionRes_obj_ofLinearCharacter` is an equality of objects; conjugation, restriction and
comparison of these objects are computed inside `G →* kˣ` through it and
`FDRep.nonempty_iso_ofLinearCharacter_iff`.
-/

public section

open CategoryTheory

universe u v

namespace Representation

variable {k : Type u} {G : Type v}

/-- **The one-dimensional representation associated to a multiplicative character.** An element
`g : G` acts on the line `k` by multiplication by the unit `χ g`. -/
def ofLinearCharacter [CommSemiring k] [Monoid G] (χ : G →* kˣ) : Representation k G k :=
  (Algebra.lsmul k k k).toMonoidHom.comp ((Units.coeHom k).comp χ)

/-- The representation associated to `χ` acts by multiplication by `χ`. -/
@[simp]
theorem ofLinearCharacter_apply [CommSemiring k] [Monoid G] (χ : G →* kˣ) (g : G) (x : k) :
    ofLinearCharacter χ g x = (χ g : k) * x :=
  (rfl)

/-- **Restricting a one-dimensional representation is precomposition of its character.** -/
@[simp]
theorem ofLinearCharacter_comp [CommSemiring k] [Monoid G] {H : Type*} [Monoid H]
    (χ : G →* kˣ) (f : H →* G) :
    (ofLinearCharacter χ).comp f = ofLinearCharacter (χ.comp f) := by
  apply MonoidHom.ext
  intro h
  apply LinearMap.ext
  intro x
  rfl

/-- **The one-dimensional representation remembers its multiplicative character.** -/
theorem ofLinearCharacter_injective [CommSemiring k] [Monoid G] :
    Function.Injective (ofLinearCharacter : (G →* kˣ) → Representation k G k) := by
  intro χ ψ h
  apply MonoidHom.ext
  intro g
  apply Units.ext
  have := congrArg (fun ρ : Representation k G k => ρ g 1) h
  simpa using this

/-- **The trivial linear character carries the trivial representation.** This is the sanity check
that fixes the convention: `χ = 1` acts by the scalar `1`. -/
@[simp]
theorem ofLinearCharacter_one [CommSemiring k] [Monoid G] :
    ofLinearCharacter (1 : G →* kˣ) = Representation.trivial k G k :=
  MonoidHom.ext fun _ => LinearMap.ext fun x => by simp

/-- **The trace character of a one-dimensional representation is its multiplicative character.** -/
@[simp]
theorem char_ofLinearCharacter [Field k] [Monoid G] (χ : G →* kˣ) (g : G) :
    (ofLinearCharacter χ).character g = (χ g : k) := by
  rw [character]
  have h : ofLinearCharacter χ g = LinearMap.id.smulRight (χ g : k) := by
    apply LinearMap.ext
    intro x
    simp [mul_comm]
  rw [h, LinearMap.trace_smulRight, LinearMap.id_apply]

/-- A one-dimensional representation is irreducible, having no room for a proper nonzero
subrepresentation. -/
instance isIrreducible_ofLinearCharacter [Field k] [Monoid G] (χ : G →* kˣ) :
    (ofLinearCharacter (k := k) χ).IsIrreducible :=
  isIrreducible_of_finrank_eq_one _ (Module.finrank_self k)

/-- **An irreducible representation is the line of a linear character `χ` exactly when every `g`
acts by the scalar `χ g`.** If it does, a nonzero vector spans an equivariant copy of the line `k`,
and irreducibility makes this copy everything. -/
theorem IsIrreducible.nonempty_equiv_ofLinearCharacter_iff [Field k] [Monoid G] {V : Type*}
    [AddCommGroup V] [Module k V] {ρ : Representation k G V} (hρ : ρ.IsIrreducible)
    (χ : G →* kˣ) :
    Nonempty (ρ.Equiv (ofLinearCharacter χ)) ↔ ∀ g, ρ g = (χ g : k) • (1 : Module.End k V) := by
  refine ⟨fun ⟨e⟩ g ↦ LinearMap.ext fun v ↦ e.injective ?_, fun h ↦ ?_⟩
  · simpa using IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g v
  let := hρ
  have := hρ.nontrivial
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  -- A nonzero vector spans an equivariant copy of the line, which Schur makes bijective.
  let f : IntertwiningMap (ofLinearCharacter χ) ρ :=
    (LinearMap.toSpanSingleton k V v).intertwiningMap_of_isIntertwiningMap _ _ fun g c ↦ by
      simpa [h, mul_smul] using smul_comm (χ g : k) c v
  have hf : f ≠ 0 := fun h0 ↦ hv (by simpa [f] using DFunLike.congr_fun h0 1)
  exact ⟨(f.ofBijective ((IsIrreducible.bijective_or_eq_zero f).resolve_right hf)).symm⟩

end Representation

namespace FDRep

variable {k : Type u} {G : Type v}

/-- **The one-dimensional representation carrying a linear character, as an object of
`FDRep k G`.** This is the shape induction consumes. -/
noncomputable def ofLinearCharacter [CommRing k] [Monoid G] (χ : G →* kˣ) : FDRep k G :=
  FDRep.of (Representation.ofLinearCharacter χ)

/-- **The bundled one-dimensional representation is the unbundled one, bundled.** This is the
defining equation of `FDRep.ofLinearCharacter`; with `FDRep.of_ρ'` it recovers the action, so
consumers never need to unfold the definition. -/
theorem ofLinearCharacter_def [CommRing k] [Monoid G] (χ : G →* kˣ) :
    ofLinearCharacter (k := k) χ = FDRep.of (Representation.ofLinearCharacter χ) :=
  (rfl)

/-- **Restricting a linear character along a homomorphism pulls the character back.** Both sides
are the line `k` with `s` acting by the scalar `χ (f s)`, so this is an equality of objects, not
merely an isomorphism; it is what lets conjugation and restriction of a one-dimensional
representation be computed inside `G →* kˣ`. -/
@[simp]
theorem actionRes_obj_ofLinearCharacter [CommRing k] [Monoid G] {S : Type*} [Monoid S]
    (f : S →* G) (χ : G →* kˣ) :
    (Action.res (FGModuleCat k) f).obj (ofLinearCharacter χ) = ofLinearCharacter (χ.comp f) :=
  (rfl)

/-- A linear character is carried by a line. -/
@[simp]
theorem finrank_ofLinearCharacter [CommRing k] [Monoid G] (χ : G →* kˣ) :
    Module.finrank k (ofLinearCharacter (k := k) χ) = 1 :=
  CommSemiring.finrank_self k

/-- **The character of `FDRep.ofLinearCharacter` is the linear character it was built from.** -/
@[simp]
theorem char_ofLinearCharacter [Field k] [Monoid G] (χ : G →* kˣ) (g : G) :
    (ofLinearCharacter (k := k) χ).character g = (χ g : k) :=
  Representation.char_ofLinearCharacter χ g

/-- **The one-dimensional representation of a linear character is a simple object**, being a
line. -/
instance simple_ofLinearCharacter [Field k] [Monoid G] (χ : G →* kˣ) :
    Simple (ofLinearCharacter (k := k) χ) :=
  have : Representation.IsIrreducible (ofLinearCharacter (k := k) χ).ρ :=
    Representation.isIrreducible_ofLinearCharacter χ
  FDRep.simple_of_isIrreducible _

/-- **Two one-dimensional representations are isomorphic exactly when their linear characters
agree.** An isomorphism of lines is multiplication by the unit `f 1`, so equivariance reads
`χ g * f 1 = ψ g * f 1`, which that unit cancels from; conversely equal characters give literally
the same object. -/
@[simp]
theorem nonempty_iso_ofLinearCharacter_iff [CommRing k] [Monoid G] (χ ψ : G →* kˣ) :
    Nonempty (ofLinearCharacter (k := k) χ ≅ ofLinearCharacter ψ) ↔ χ = ψ := by
  refine ⟨fun ⟨e⟩ => MonoidHom.ext fun g => Units.ext ?_, fun h => ⟨h ▸ Iso.refl _⟩⟩
  rw [ofLinearCharacter_def, ofLinearCharacter_def] at e
  let f := isoToLinearEquiv e
  have hlin (c : k) : f c = c * f 1 := by simpa using f.map_smul c (1 : k)
  apply f.injective
  rw [hlin (χ g : k), hlin (ψ g : k)]
  have h := DFunLike.congr_fun (FDRep.Iso.conj_ρ e g) (f 1)
  simpa only [f, LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply,
    of_ρ', Representation.ofLinearCharacter_apply, mul_one, hlin (χ g : k)] using h.symm

/-- **An irreducible representation whose operators commute has a linear character.**  Over an
algebraically closed field, if the operators of an irreducible representation `W` commute
pairwise, Schur's lemma makes each a scalar, so `W` is a line and its character is the linear
character of those scalars. -/
theorem exists_character_eq_of_commute [Field k] [IsAlgClosed k] [Group G] (W : FDRep k G)
    [Simple W] (hcomm : ∀ g h : G, Commute (W.ρ g) (W.ρ h)) :
    ∃ χ : G →* kˣ, W.character = fun g => (χ g : k) := by
  have hW := FDRep.isIrreducible_of_simple W
  have : Nontrivial W := hW.nontrivial
  choose c hc using fun g => hW.exists_forall_apply_eq_smul (W.ρ g) fun h v => by
    rw [← Module.End.mul_apply, (hcomm g h).eq, Module.End.mul_apply]
  obtain ⟨v, hv⟩ := exists_ne (0 : W)
  have hmul (g h : G) : c (g * h) = c g * c h := by
    refine smul_left_injective k hv ?_
    dsimp only
    rw [← hc, map_mul, Module.End.mul_apply, hc h, map_smul, hc g, smul_smul, mul_comm]
  have hone : c 1 = 1 := smul_left_injective k hv (by simp [← hc])
  -- The line through `v` is stable, hence everything: `W` is one-dimensional.
  let line : Subrepresentation W.ρ :=
    ⟨k ∙ v, fun g w hw => by
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
      rw [map_smul, hc, smul_smul]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)⟩
  have hline : line = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top line).resolve_left fun h => hv <| by
    have hmem : v ∈ line.toSubmodule := Submodule.mem_span_singleton_self v
    rw [h] at hmem
    exact hmem
  have hfin : Module.finrank k W = 1 :=
    (finrank_eq_one_iff_of_nonzero v hv).mpr (congrArg Subrepresentation.toSubmodule hline)
  let χ : G →* k := { toFun := c, map_one' := hone, map_mul' := hmul }
  refine ⟨χ.toHomUnits, funext fun g => ?_⟩
  have hρ : W.ρ g = c g • LinearMap.id := LinearMap.ext (hc g)
  simp [χ, character, hρ, hfin]

end FDRep
end
end TAF_LiteralSource_0396

section TAF_LiteralSource_0397
/- Original module: TauCeti.RepresentationTheory.CharacterTwist -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Twisting a representation by a linear character

Tensoring a representation `ρ` with a one-dimensional representation does not change its carrier:
the line can be absorbed by `TensorProduct.lid`, leaving the same module with the action rescaled
by the character.  This file records that rescaled action directly as
`Representation.charTwist χ ρ`, `g ↦ χ g • ρ g` for a linear character `χ : G →* kˣ`, and proves
that it is the tensor product with `Representation.ofLinearCharacter χ`
(`Representation.tprodEquivCharTwist`).

Working with the twist rather than with the tensor product is what makes its basic theory
transparent.  Because every value of `χ` is a *unit*, a submodule is stable under `χ g • ρ g`
exactly when it is stable under `ρ g`, so the twist has literally the same subrepresentations
(`Representation.subrepresentationCharTwistOrderIso`) and is irreducible exactly when `ρ` is
(`Representation.isIrreducible_charTwist_iff`).  Neither statement is visible through the tensor
product without transporting along `TensorProduct.lid` first.

The twists form an action of the character group: twisting by `1` changes nothing and twisting
twice multiplies the characters.  The main consumer is the determinant twist of the general linear
group, where `χ = det ^ m` turns a polynomial representation into a rational one.

This is a module of its own rather than a section of
`TauCeti/RepresentationTheory/LinearCharacter/Basic.lean`, which it extends: the twist needs the
tensor product and the subrepresentation lattice. Consumers of the bare one-dimensional
representation need neither.

## Main definitions

* `Representation.charTwist`: the representation `g ↦ χ g • ρ g`.
* `Representation.subrepresentationCharTwistOrderIso`: the twist has the same lattice of
  subrepresentations as `ρ`, by the identity on carriers.
* `Representation.tprodEquivCharTwist` and
  `Representation.tprodOfLinearCharacterEquivCharTwist`: the tensor product of `ρ` with
  `ofLinearCharacter χ` **is** the twist, on either side, along `TensorProduct.lid` and
  `TensorProduct.rid`.

## Main results

* `Representation.charTwist_one` and `Representation.charTwist_charTwist`: twisting is an action of
  the character group `G →* kˣ`.
* `Representation.charTwist_trivial`: twisting the trivial representation of the line gives the
  one-dimensional representation of the character.
* `Representation.lid_ofLinearCharacter_tprod_apply` and
  `Representation.rid_tprod_ofLinearCharacter_apply`: `TensorProduct.lid` and `TensorProduct.rid`
  carry the action of `(ofLinearCharacter χ) ⊗ ρ` and of `ρ ⊗ (ofLinearCharacter χ)` to the action
  of `ρ` rescaled by `χ`.
* `Representation.isIrreducible_charTwist_iff`: **the twist of an irreducible representation is
  irreducible**, and conversely.
* `Representation.char_charTwist`: the trace character of the twist is `χ` times the character
  of `ρ`.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 15, where the
  rational representations of `GL n` are the determinant twists of the polynomial ones.
-/

public section

open scoped TensorProduct

namespace Representation

universe u v w

variable {k : Type u} {G : Type v} {V : Type w}

section CommSemiring

variable [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]

/-- **The twist of a representation by a linear character**: the same carrier, with `ρ g` rescaled
by the unit `χ g`.  It is the tensor product with the one-dimensional representation of `χ`
(`Representation.tprodEquivCharTwist`), with the line absorbed. -/
def charTwist (χ : G →* kˣ) (ρ : Representation k G V) : Representation k G V where
  toFun g := (χ g : k) • ρ g
  map_one' := by simp
  map_mul' g h := by
    ext v
    simp only [map_mul, Units.val_mul, Module.End.mul_apply, LinearMap.smul_apply, map_smul,
      smul_smul, mul_comm]

@[simp]
theorem charTwist_apply (χ : G →* kˣ) (ρ : Representation k G V) (g : G) :
    charTwist χ ρ g = (χ g : k) • ρ g :=
  (rfl)

theorem charTwist_apply_apply (χ : G →* kˣ) (ρ : Representation k G V) (g : G) (v : V) :
    charTwist χ ρ g v = (χ g : k) • ρ g v :=
  (rfl)

/-- Twisting by the trivial character changes nothing. -/
@[simp]
theorem charTwist_one (ρ : Representation k G V) : charTwist (1 : G →* kˣ) ρ = ρ :=
  MonoidHom.ext fun _ => by simp

/-- Twisting twice multiplies the characters: the twists are an action of `G →* kˣ`. -/
theorem charTwist_charTwist (χ ψ : G →* kˣ) (ρ : Representation k G V) :
    charTwist χ (charTwist ψ ρ) = charTwist (χ * ψ) ρ :=
  MonoidHom.ext fun g => LinearMap.ext fun v => by
    simp [mul_smul]

/-- Twisting the trivial representation of the coefficient line by `χ` gives the one-dimensional
representation of `χ`.  So the one-dimensional representations are the twists of the trivial one,
and `Representation.charTwist` extends `Representation.ofLinearCharacter`. -/
@[simp]
theorem charTwist_trivial (χ : G →* kˣ) :
    charTwist χ (trivial k G k) = ofLinearCharacter χ :=
  MonoidHom.ext fun _ => LinearMap.ext fun x => by
    simp [ofLinearCharacter_apply, smul_eq_mul]

/-- A submodule stable under `ρ` is stable under any twist of `ρ`. -/
theorem charTwist_apply_mem_of_apply_mem {χ : G →* kˣ} {ρ : Representation k G V}
    {p : Submodule k V} (hp : ∀ (g : G) ⦃v : V⦄, v ∈ p → ρ g v ∈ p) (g : G) ⦃v : V⦄ (hv : v ∈ p) :
    charTwist χ ρ g v ∈ p :=
  p.smul_mem _ (hp g hv)

/-- Conversely a submodule stable under a twist of `ρ` is stable under `ρ`, the character values
being units. -/
theorem apply_mem_of_charTwist_apply_mem {χ : G →* kˣ} {ρ : Representation k G V}
    {p : Submodule k V} (hp : ∀ (g : G) ⦃v : V⦄, v ∈ p → charTwist χ ρ g v ∈ p) (g : G) ⦃v : V⦄
    (hv : v ∈ p) : ρ g v ∈ p := by
  have h := p.smul_mem ((χ g)⁻¹ : kˣ) (hp g hv)
  rwa [charTwist_apply_apply, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    one_smul] at h

variable (χ : G →* kˣ) (ρ : Representation k G V)

/-- **A twist has the same subrepresentations as the representation it twists**, by the identity on
carriers: the character values are units, so they scale a stable submodule into itself and back. -/
def subrepresentationCharTwistOrderIso : Subrepresentation (charTwist χ ρ) ≃o Subrepresentation ρ
    where
  toFun p := ⟨p.toSubmodule, apply_mem_of_charTwist_apply_mem p.apply_mem_toSubmodule⟩
  invFun p := ⟨p.toSubmodule, charTwist_apply_mem_of_apply_mem p.apply_mem_toSubmodule⟩
  left_inv _ := Subrepresentation.toSubmodule_injective rfl
  right_inv _ := Subrepresentation.toSubmodule_injective rfl
  map_rel_iff' := Iff.rfl

@[simp]
theorem toSubmodule_subrepresentationCharTwistOrderIso (p : Subrepresentation (charTwist χ ρ)) :
    (subrepresentationCharTwistOrderIso χ ρ p).toSubmodule = p.toSubmodule :=
  (rfl)

@[simp]
theorem toSubmodule_subrepresentationCharTwistOrderIso_symm (p : Subrepresentation ρ) :
    ((subrepresentationCharTwistOrderIso χ ρ).symm p).toSubmodule = p.toSubmodule :=
  (rfl)

/-- **`TensorProduct.lid` carries the action of `(ofLinearCharacter χ) ⊗ ρ` to the action of `ρ`
rescaled by `χ`.**  This is the equivariance datum behind
`Representation.tprodEquivCharTwist`, recorded on elements so that it can be used without
unfolding that equivalence. -/
theorem lid_ofLinearCharacter_tprod_apply (g : G) (x : k ⊗[k] V) :
    _root_.TensorProduct.lid k V (((ofLinearCharacter χ).tprod ρ) g x)
      = (χ g : k) • ρ g (_root_.TensorProduct.lid k V x) := by
  induction x using _root_.TensorProduct.inductionOn with
  | tmul c v =>
    simp only [tprod_apply, _root_.TensorProduct.map_tmul, ofLinearCharacter_apply,
      _root_.TensorProduct.lid_tmul, map_smul, smul_smul]
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

/-- **The tensor product with the one-dimensional representation of a character is the twist by
that character**, along `TensorProduct.lid`.  This is the identification that lets the twist be
read as the usual tensor product `χ ⊗ ρ`, and conversely lets a tensor product with a line be
computed on the original carrier. -/
noncomputable def tprodEquivCharTwist :
    ((ofLinearCharacter χ).tprod ρ).Equiv (charTwist χ ρ) :=
  .mk (_root_.TensorProduct.lid k V) fun g =>
    LinearMap.ext fun x => lid_ofLinearCharacter_tprod_apply χ ρ g x

@[simp]
theorem toLinearMap_tprodEquivCharTwist :
    (tprodEquivCharTwist χ ρ).toLinearMap = (_root_.TensorProduct.lid k V).toLinearMap :=
  (rfl)

@[simp]
theorem tprodEquivCharTwist_tmul (x : k) (v : V) :
    tprodEquivCharTwist χ ρ (x ⊗ₜ[k] v) = x • v :=
  (rfl)

/-- The inverse of `Representation.tprodEquivCharTwist` puts the line `1` in front. -/
@[simp]
theorem tprodEquivCharTwist_symm_apply (v : V) :
    (tprodEquivCharTwist χ ρ).symm v = (1 : k) ⊗ₜ[k] v :=
  (rfl)

/-- **`TensorProduct.rid` carries the action of `ρ ⊗ (ofLinearCharacter χ)` to the action of `ρ`
rescaled by `χ`.**  This is the mirror of `Representation.lid_ofLinearCharacter_tprod_apply` for a
line on the right, and the equivariance datum behind
`Representation.tprodOfLinearCharacterEquivCharTwist`. -/
theorem rid_tprod_ofLinearCharacter_apply (g : G) (x : V ⊗[k] k) :
    _root_.TensorProduct.rid k V ((ρ.tprod (ofLinearCharacter χ)) g x)
      = (χ g : k) • ρ g (_root_.TensorProduct.rid k V x) := by
  induction x using _root_.TensorProduct.inductionOn with
  | tmul v c =>
    simp only [tprod_apply, _root_.TensorProduct.map_tmul, ofLinearCharacter_apply,
      _root_.TensorProduct.rid_tmul, map_smul, smul_smul]
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

/-- **The tensor product with the one-dimensional representation of a character on the right is
also the twist by that character**, along `TensorProduct.rid`: the mirror of
`Representation.tprodEquivCharTwist`, so that a consumer holding `ρ ⊗ χ` reaches the twist theory
without flipping the factors first. -/
noncomputable def tprodOfLinearCharacterEquivCharTwist :
    (ρ.tprod (ofLinearCharacter χ)).Equiv (charTwist χ ρ) :=
  .mk (_root_.TensorProduct.rid k V) fun g =>
    LinearMap.ext fun x => rid_tprod_ofLinearCharacter_apply χ ρ g x

@[simp]
theorem toLinearMap_tprodOfLinearCharacterEquivCharTwist :
    (tprodOfLinearCharacterEquivCharTwist χ ρ).toLinearMap
      = (_root_.TensorProduct.rid k V).toLinearMap :=
  (rfl)

@[simp]
theorem tprodOfLinearCharacterEquivCharTwist_tmul (v : V) (x : k) :
    tprodOfLinearCharacterEquivCharTwist χ ρ (v ⊗ₜ[k] x) = x • v :=
  (rfl)

/-- The inverse of `Representation.tprodOfLinearCharacterEquivCharTwist` tensors with `1` on the
right. -/
@[simp]
theorem tprodOfLinearCharacterEquivCharTwist_symm_apply (v : V) :
    (tprodOfLinearCharacterEquivCharTwist χ ρ).symm v = v ⊗ₜ[k] (1 : k) :=
  (rfl)

end CommSemiring

section Field

variable [Field k] [Monoid G] [AddCommGroup V] [Module k V] (χ : G →* kˣ)
  (ρ : Representation k G V)

/-- **A twist of an irreducible representation is irreducible**, and only a twist of an irreducible
one is: twisting by a character does not change the lattice of subrepresentations. -/
@[simp]
theorem isIrreducible_charTwist_iff : (charTwist χ ρ).IsIrreducible ↔ ρ.IsIrreducible :=
  OrderIso.isSimpleOrder_iff (subrepresentationCharTwistOrderIso χ ρ)

/-- The instance form of `Representation.isIrreducible_charTwist_iff`: a twist of an irreducible
representation is irreducible. -/
instance isIrreducible_charTwist [ρ.IsIrreducible] : (charTwist χ ρ).IsIrreducible :=
  (isIrreducible_charTwist_iff χ ρ).mpr ‹_›

/-- **The character of a twist is the pointwise product** of the twisting character with the
character of the representation. -/
@[simp]
theorem char_charTwist (g : G) :
    (charTwist χ ρ).character g = (χ g : k) * ρ.character g := by
  rw [character, character, charTwist_apply, map_smul, smul_eq_mul]

end Field

end Representation
end
end TAF_LiteralSource_0397

section TAF_LiteralSource_0398
/- Original module: TauCeti.RepresentationTheory.ClassicalGroups.Determinant -/
/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Determinant-power representations of the general linear group

This file packages the determinant and its integral powers as one-dimensional representations of
the general linear group. These are the rational characters used to form determinant twists of
polynomial representations.

## Main definitions

* `TauCeti.detPowerRep` is the representation on the scalar module with action by `det(g)^m`.
* `TauCeti.detRep` is the determinant representation, the case `m = 1`.
* `TauCeti.tprodDetPowerSLEquiv`: the restriction of `det^m ⊗ ρ` to `SL n k` is the restriction of
  `ρ`, along `TensorProduct.lid`.

## Main results

* `TauCeti.detPowerRep_def` is its defining equation, as the one-dimensional representation of the
  linear character `det ^ m`.
* `TauCeti.detPowerRep_comp_toGL`: every determinant power restricts to the trivial
  representation of the special linear subgroup, which is why **the determinant twist is invisible
  to `SL n k`** (`TauCeti.tprodDetPowerSLEquiv`).
-/

public section

open Matrix
open scoped TensorProduct

universe u v

namespace TauCeti

variable (k : Type u) (n : ℕ)

section CommRing

variable [CommRing k]

/-- The one-dimensional representation of `GL n k` on which `g` acts by `det(g)^m`. This is the
representation carrying the linear character `det ^ m`. -/
def detPowerRep (m : ℤ) : Representation k (GL (Fin n) k) k :=
  Representation.ofLinearCharacter ((Matrix.GeneralLinearGroup.det : GL (Fin n) k →* kˣ) ^ m)

/-- The defining equation of `TauCeti.detPowerRep`: it is the one-dimensional representation of
the linear character `det ^ m`.  The body is not exposed, so this is how a downstream module
applies the general theory of `Representation.ofLinearCharacter` and of its twists to it. -/
theorem detPowerRep_def (m : ℤ) :
    detPowerRep k n m =
      Representation.ofLinearCharacter ((Matrix.GeneralLinearGroup.det : GL (Fin n) k →* kˣ) ^ m) :=
  (rfl)

/-- The determinant representation of `GL n k`. -/
abbrev detRep : Representation k (GL (Fin n) k) k := detPowerRep k n 1

/-- The determinant-power action is scalar multiplication by the indicated determinant power. -/
@[simp]
theorem detPowerRep_apply (m : ℤ) (g : GL (Fin n) k) (x : k) :
    detPowerRep k n m g x = (↑((Matrix.GeneralLinearGroup.det g) ^ m) : k) * x :=
  Representation.ofLinearCharacter_apply _ g x

/-- The zero determinant power is the trivial representation. -/
@[simp]
theorem detPowerRep_zero : detPowerRep k n 0 = 1 := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro x
  simp

/-- Adding exponents composes the corresponding determinant actions. -/
theorem detPowerRep_add_apply (m l : ℤ) (g : GL (Fin n) k) (x : k) :
    detPowerRep k n (m + l) g x = detPowerRep k n m g (detPowerRep k n l g x) := by
  simp only [detPowerRep_apply, _root_.zpow_add, Units.val_mul]
  rw [mul_assoc]

/-- Every determinant-power representation restricts to the trivial representation of `SL n k`. -/
@[simp]
theorem detPowerRep_comp_toGL (m : ℤ) : (detPowerRep k n m).comp Matrix.SpecialLinearGroup.toGL =
      Representation.trivial k (Matrix.SpecialLinearGroup (Fin n) k) k := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro x
  -- Unfolding the two composed monoid homomorphisms exposes the scalar-action formula.
  change detPowerRep k n m (Matrix.SpecialLinearGroup.toGL g) x = x
  rw [detPowerRep_apply]
  simp

/-! ## The determinant twist on the special linear group -/

/-- **`TensorProduct.lid` carries the restricted action of `det^m ⊗ ρ` to the restricted action of
`ρ`**: the determinant is `1` on `SL n k`, so the twisting factor is `1`.  This is the
equivariance datum behind `TauCeti.tprodDetPowerSLEquiv`, recorded on elements so that it can be
used without unfolding that equivalence. -/
theorem lid_detPowerRep_tprod_toGL_apply {V : Type v} [AddCommMonoid V] [Module k V] (m : ℤ)
    (ρ : Representation k (GL (Fin n) k) V) (g : Matrix.SpecialLinearGroup (Fin n) k)
    (x : k ⊗[k] V) :
    _root_.TensorProduct.lid k V
        (((detPowerRep k n m).tprod ρ) (Matrix.SpecialLinearGroup.toGL g) x)
      = ρ (Matrix.SpecialLinearGroup.toGL g) (_root_.TensorProduct.lid k V x) := by
  have hdet : (((Matrix.GeneralLinearGroup.det : GL (Fin n) k →* kˣ) ^ m)
      (Matrix.SpecialLinearGroup.toGL g) : kˣ) = 1 := by
    simp
  rw [detPowerRep_def, Representation.lid_ofLinearCharacter_tprod_apply, hdet, Units.val_one,
    one_smul]

/-- **The determinant twist is invisible to the special linear group**: for every representation
`ρ` of `GL n k`, the restriction of `det^m ⊗ ρ` to `SL n k` is the restriction of `ρ`, along
`TensorProduct.lid`.  This is the restricted counterpart of
`Representation.tprodEquivCharTwist`, where the twisting character `det ^ m` has become `1`. -/
noncomputable def tprodDetPowerSLEquiv {V : Type v} [AddCommMonoid V] [Module k V] (m : ℤ)
    (ρ : Representation k (GL (Fin n) k) V) :
    Representation.Equiv
      (((detPowerRep k n m).tprod ρ).comp Matrix.SpecialLinearGroup.toGL)
      (ρ.comp Matrix.SpecialLinearGroup.toGL) :=
  .mk (_root_.TensorProduct.lid k V) fun g =>
    LinearMap.ext fun x => lid_detPowerRep_tprod_toGL_apply k n m ρ g x

@[simp]
theorem toLinearMap_tprodDetPowerSLEquiv {V : Type v} [AddCommMonoid V] [Module k V] (m : ℤ)
    (ρ : Representation k (GL (Fin n) k) V) :
    (tprodDetPowerSLEquiv k n m ρ).toLinearMap =
      (_root_.TensorProduct.lid k V).toLinearMap :=
  (rfl)

@[simp]
theorem tprodDetPowerSLEquiv_tmul {V : Type v} [AddCommMonoid V] [Module k V] (m : ℤ)
    (ρ : Representation k (GL (Fin n) k) V) (x : k) (v : V) :
    tprodDetPowerSLEquiv k n m ρ (x ⊗ₜ[k] v) = x • v :=
  (rfl)

/-- The determinant-power representation as a finite-dimensional representation. -/
noncomputable abbrev detPowerFDRep (m : ℤ) : FDRep k (GL (Fin n) k) :=
  FDRep.ofLinearCharacter (Matrix.GeneralLinearGroup.det ^ m)

/-- The determinant representation as a finite-dimensional representation. -/
noncomputable abbrev detFDRep : FDRep k (GL (Fin n) k) :=
  FDRep.of (detRep k n)

end CommRing

section Field

variable [Field k]

/-- Negating the exponent makes the determinant scalar the inverse of the original power. -/
theorem detPowerRep_neg_apply (m : ℤ) (g : GL (Fin n) k) (x : k) :
    detPowerRep k n (-m) g x = (↑((Matrix.GeneralLinearGroup.det g) ^ m) : k)⁻¹ * x := by
  simp only [detPowerRep_apply, _root_.zpow_neg, Units.val_inv_eq_inv_val]

/-- The character of the determinant-power representation is the corresponding determinant power. -/
@[simp]
theorem char_detPowerRep (m : ℤ) (g : GL (Fin n) k) :
    (detPowerRep k n m).character g = (↑((Matrix.GeneralLinearGroup.det g) ^ m) : k) := by
  exact Representation.char_ofLinearCharacter _ g

/-- The bundled determinant-power character is the corresponding determinant power.

This is deliberately not a `simp` lemma: `TauCeti.detPowerFDRep` is a reducible abbreviation for
`FDRep.ofLinearCharacter (det ^ m)`, so `FDRep.char_ofLinearCharacter` already reduces
its left-hand side. -/
theorem char_detPowerFDRep (m : ℤ) (g : GL (Fin n) k) :
    (detPowerFDRep k n m).character g = (↑((Matrix.GeneralLinearGroup.det g) ^ m) : k) :=
  FDRep.char_ofLinearCharacter _ g

/-- The bundled determinant character is the determinant. -/
theorem char_detFDRep (g : GL (Fin n) k) :
    (detFDRep k n).character g = (Matrix.GeneralLinearGroup.det g : k) := by
  -- The determinant representation is the first determinant power, so its character is that of
  -- `FDRep.ofLinearCharacter (det ^ (1 : ℤ))`.
  have h : detFDRep k n = detPowerFDRep k n 1 := (FDRep.ofLinearCharacter_def _).symm
  rw [h, char_detPowerFDRep, zpow_one]

end Field

end TauCeti
end
end TAF_LiteralSource_0398

section TAF_LiteralSource_0399
/- Original module: TauCeti.RepresentationTheory.ClassicalGroups.ExteriorPower -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Exterior powers of the standard representation

This file specializes exterior powers of representations to the standard representation of the
general linear group. The resulting action applies a matrix to every factor of a pure wedge.

In the top degree `d = n` the action collapses to a scalar: a matrix acts on `⋀[k]^n (Fin n → k)`
by its determinant, so that exterior power is the determinant representation.

## Main definitions

* `TauCeti.extPowerRep` is the exterior-power representation of `GL n k`.
* `TauCeti.extPowerFDRep` is its bundled finite-dimensional form.
* `TauCeti.topExtPowerEquivDet` identifies the top exterior power with the determinant
  representation, and `TauCeti.extPowerFDRepDetIso` is its bundled form.

## Main results

* `TauCeti.char_extPowerRep_diagonal` identifies the character on diagonal matrices with an
  elementary symmetric polynomial.
* `TauCeti.extPowerRep_self_apply` and `TauCeti.char_extPowerRep_self` compute the top-degree
  action and character as the determinant.

Vanishing of `⋀[k]^d (Fin n → k)`, and hence `extPowerRep k n d`, once `n < d` is given by
`exteriorPower.eq_zero_of_finrank_lt` in `TauCeti.LinearAlgebra.ExteriorPower.Basic`. The
degree-zero and degree-one identifications of `extPowerRep k n` are the generic
`(stdRep k n).exteriorPowerZeroEquiv` and `(stdRep k n).exteriorPowerOneEquiv`.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 15.
-/

public section

open CategoryTheory
open Matrix
open scoped TensorProduct

universe u

namespace TauCeti

variable (k : Type u) (n d : ℕ)

section CommRing

variable [CommRing k]

/-- The `d`th exterior power of the standard representation of `GL n k`. -/
noncomputable abbrev extPowerRep :
    Representation k (GL (Fin n) k) (⋀[k]^d (Fin n → k)) :=
  (stdRep k n).exteriorPower d

/-- The exterior power of the standard representation, bundled as an object of `FDRep`. -/
noncomputable abbrev extPowerFDRep : FDRep k (GL (Fin n) k) :=
  FDRep.of (extPowerRep k n d)

/-- In the top degree a matrix acts on the exterior power by multiplication by its determinant.

This is deliberately not a `simp` lemma: `Representation.exteriorPower_apply` and `stdRep_apply`
already rewrite the left-hand side to `exteriorPower.map n (Matrix.mulVecLin ↑g)`, so it is not in
`simp` normal form and the rewrite could never fire. The `simp`-normal statement is
`Module.Basis.map_exteriorPower_top_eq_det_smul`, applied here to `Pi.basisFun k (Fin n)`. -/
theorem extPowerRep_self_apply (g : GL (Fin n) k) :
    extPowerRep k n n g = Matrix.det (g : Matrix (Fin n) (Fin n) k) • LinearMap.id := by
  rw [Representation.exteriorPower_apply, stdRep_apply, ← Matrix.toLin'_apply',
    (Pi.basisFun k (Fin n)).map_exteriorPower_top_eq_det_smul, LinearMap.det_toLin']

/-- **The top exterior power of the standard representation is the determinant representation.**
The identification sends a wedge of `n` vectors to the determinant of the matrix they form. -/
noncomputable def topExtPowerEquivDet : (extPowerRep k n n).Equiv (detRep k n) :=
  .mk ((Pi.basisFun k (Fin n)).exteriorPowerTopEquiv) fun g ↦ by
    refine LinearMap.ext fun x ↦ ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      extPowerRep_self_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq, map_smul,
      smul_eq_mul, detPowerRep_apply, zpow_one, Matrix.GeneralLinearGroup.val_det_apply]

/-- The underlying linear equivalence of `TauCeti.topExtPowerEquivDet` is the top-degree
identification of the exterior power with the scalars. -/
@[simp]
theorem topExtPowerEquivDet_toLinearEquiv :
    (topExtPowerEquivDet k n).toLinearEquiv = (Pi.basisFun k (Fin n)).exteriorPowerTopEquiv :=
  (rfl)

/-- The identification sends a wedge of `n` vectors to the determinant of the matrix they form. -/
@[simp]
theorem topExtPowerEquivDet_apply_ιMulti (v : Fin n → (Fin n → k)) :
    topExtPowerEquivDet k n (exteriorPower.ιMulti k n v) = (Matrix.of v).det := by
  rw [← Representation.Equiv.coe_toIntertwiningMap,
    ← Representation.Equiv.toLinearEquiv_apply, topExtPowerEquivDet_toLinearEquiv,
    Module.Basis.exteriorPowerTopEquiv_apply_ιMulti, Pi.basisFun_det_apply]

/-- The identification of the top exterior power with the determinant representation, bundled as
an isomorphism in `FDRep`. -/
noncomputable def extPowerFDRepDetIso : extPowerFDRep k n n ≅ detFDRep k n :=
  Action.mkIso (topExtPowerEquivDet k n).toLinearEquiv.toFGModuleCatIso fun g ↦ by
    apply FGModuleCat.hom_ext
    exact (topExtPowerEquivDet k n).isIntertwining' g

/-- The forward map of the bundled identification is the underlying representation
equivalence. -/
@[simp]
theorem extPowerFDRepDetIso_hom_hom : (extPowerFDRepDetIso k n).hom.hom =
      ConcreteCategory.ofHom (topExtPowerEquivDet k n).toLinearMap := by
  rw [extPowerFDRepDetIso]
  rfl

/-- The inverse map of the bundled identification is the inverse representation equivalence. -/
@[simp]
theorem extPowerFDRepDetIso_inv_hom : (extPowerFDRepDetIso k n).inv.hom =
      ConcreteCategory.ofHom (topExtPowerEquivDet k n).symm.toLinearMap := by
  rw [extPowerFDRepDetIso]
  rfl

end CommRing

section Field

variable [Field k]

/-- The character of the `d`th exterior power on a diagonal matrix is the `d`th elementary
symmetric polynomial in its diagonal entries. -/
@[simp]
theorem char_extPowerRep_diagonal (t : Fin n → kˣ) : (extPowerRep k n d).character (diagGL t) =
      MvPolynomial.eval (fun i => (t i : k)) (MvPolynomial.esymm (Fin n) k d) := by
  rw [Representation.character, Representation.exteriorPower_apply]
  rw [(Pi.basisFun k (Fin n)).trace_map_exteriorPower_of_apply
    (stdRep k n (diagGL t)) (fun i => (t i : k)) d
    (stdRep_diagGL_apply_basisFun t)]
  simp only [MvPolynomial.esymm, MvPolynomial.eval_sum, MvPolynomial.eval_prod,
    MvPolynomial.eval_X]
  -- Both sides sum the same products over the `d`-element subsets of `Fin n`, indexed by
  -- `Set.powersetCard` on the left and by `Finset.powersetCard` on the right.
  exact (Finset.sum_subtype (Finset.powersetCard d Finset.univ)
    (fun _ => Finset.mem_powersetCard_univ) fun s => ∏ i ∈ s, (t i : k)).symm

/-- The character of the top exterior power of the standard representation is the determinant.

This is deliberately not a `simp` lemma: on a diagonal matrix its left-hand side is also matched by
`TauCeti.char_extPowerRep_diagonal`, whose elementary-symmetric right-hand side is a different
normal form. -/
theorem char_extPowerRep_self (g : GL (Fin n) k) :
    (extPowerRep k n n).character g = Matrix.det (g : Matrix (Fin n) (Fin n) k) := by
  rw [Representation.char_iso (topExtPowerEquivDet k n), char_detPowerRep k n 1 g, zpow_one,
    Matrix.GeneralLinearGroup.val_det_apply]

end Field

end TauCeti
end
end TAF_LiteralSource_0399

section TAF_LiteralSource_0400
/- Original module: TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Multilinear -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

-- `MvPolynomial.eq_of_eval_eq_on_gl`, the Zariski density of the invertible matrices, together with
-- the `GL` notation and the coercion of an element of `GL m k` to a matrix.
-- `Matrix.single`, the matrix units in which the arguments are expanded.

/-!
# A multilinear form on matrices is determined on the diagonal by the invertible matrices

Let `Θ` be a multilinear form in `ι` matrix arguments over a commutative semiring `K`. Its
**diagonal** `Y ↦ Θ (Y, …, Y)` is a polynomial function of the entries of `Y`: expanding each
argument in the matrix units `Matrix.single i j 1` writes it as a sum, over the functions
`a : ι → m × n`, of the constant `Θ (fun i => single (a i).1 (a i).2 1)` times the monomial
`∏ᵢ Y (a i).1 (a i).2`. The matrices need not be square. That is
`MultilinearMap.exists_mvPolynomial_eval_eq_apply_const` below.

Over an *infinite* field the invertible square matrices are Zariski dense, so such a polynomial
function vanishes everywhere as soon as it vanishes on `GL m K`
(`MvPolynomial.eq_of_eval_eq_on_gl`). Hence a multilinear form whose diagonal kills every invertible
matrix has zero diagonal: `MultilinearMap.apply_const_eq_zero_of_eq_zero_on_gl`.

This is the form in which density is used to pass from the invertible diagonal operators `g^{⊗ι}`
on a tensor power to all of them; the argument is stated here on matrices, where the ambient
polynomial ring `MvPolynomial (m × m) K` and the density statement live.

## Main results

* `MultilinearMap.exists_mvPolynomial_eval_eq_apply_const`: the diagonal of a multilinear form on
  (possibly rectangular) matrices is the evaluation of a polynomial in the matrix entries.
* `MultilinearMap.apply_const_eq_zero_of_eq_zero_on_gl`: over an infinite field, a multilinear form
  on matrices whose diagonal vanishes on the invertible matrices has vanishing diagonal.
-/

public section

open Matrix MvPolynomial

namespace MultilinearMap

universe u v v' w

variable {ι : Type u} {m : Type v} {n : Type v'} {K : Type w} [Finite ι]

section CommSemiring

variable [Finite m] [Finite n] [CommSemiring K]

/-- **The diagonal of a multilinear form on matrices is a polynomial in the matrix entries.**
Expanding each of the `ι` arguments in the matrix units, the value `Θ (Y, …, Y)` is a sum of
constants times monomials `∏ᵢ Y (a i).1 (a i).2` indexed by the functions `a : ι → m × n`. -/
theorem exists_mvPolynomial_eval_eq_apply_const
    (Θ : MultilinearMap K (fun _ : ι => Matrix m n K) K) :
    ∃ P : MvPolynomial (m × n) K, ∀ Y : Matrix m n K,
      MvPolynomial.eval (fun p : m × n => Y p.1 p.2) P = Θ fun _ => Y := by
  classical
  cases nonempty_fintype ι
  cases nonempty_fintype m
  cases nonempty_fintype n
  refine ⟨∑ a : ι → m × n, C (Θ fun i => single (a i).1 (a i).2 1) * ∏ i, X (a i), fun Y => ?_⟩
  have hY : ∑ p : m × n, Y p.1 p.2 • single p.1 p.2 (1 : K) = Y := by
    simp only [smul_single, smul_eq_mul, mul_one]
    rw [Fintype.sum_prod_type]
    exact (matrix_eq_sum_single Y).symm
  have hexp : (Θ fun _ => Y) =
      ∑ a : ι → m × n, (∏ i, Y (a i).1 (a i).2) * Θ fun i => single (a i).1 (a i).2 1 := by
    have hstep : (Θ fun _ : ι => ∑ p : m × n, Y p.1 p.2 • single p.1 p.2 (1 : K)) =
        ∑ a : ι → m × n, (∏ i, Y (a i).1 (a i).2) * Θ fun i => single (a i).1 (a i).2 1 := by
      rw [Θ.map_sum]
      exact Finset.sum_congr rfl fun a _ => by
        rw [Θ.map_smul_univ (fun i => Y (a i).1 (a i).2), smul_eq_mul]
    rwa [hY] at hstep
  rw [hexp]
  simp only [_root_.map_sum, _root_.map_mul, eval_C, _root_.map_prod, eval_X]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

end CommSemiring

section Field

variable [Fintype m] [DecidableEq m] [Field K] [Infinite K]

/-- **A multilinear form on matrices whose diagonal vanishes on the invertible matrices has
vanishing diagonal.** The diagonal is a polynomial function of the matrix entries (the square case
of `MultilinearMap.exists_mvPolynomial_eval_eq_apply_const`), and over an infinite field the
invertible matrices are Zariski dense. -/
theorem apply_const_eq_zero_of_eq_zero_on_gl (Θ : MultilinearMap K (fun _ : ι => Matrix m m K) K)
    (h : ∀ g : GL m K, (Θ fun _ => (g : Matrix m m K)) = 0) (Y : Matrix m m K) :
    (Θ fun _ => Y) = 0 := by
  obtain ⟨P, hP⟩ := Θ.exists_mvPolynomial_eval_eq_apply_const
  have hzero : P = 0 := MvPolynomial.eq_of_eval_eq_on_gl fun g => by simp [hP, h g]
  rw [← hP Y, hzero, _root_.map_zero]

end Field

end MultilinearMap
end
end TAF_LiteralSource_0400

section TAF_LiteralSource_0401
/- Original module: TauCeti.LinearAlgebra.PiTensorProduct.GeneralLinear -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

-- `Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff`, the detection of a subspace by the
-- functionals vanishing on it.
-- `Matrix.toLinAlgEquiv`, the algebra isomorphism between matrices and endomorphisms.
-- `PiTensorProduct.map` and `PiTensorProduct.mapMultilinear`, the diagonal operators.

/-!
# The diagonal operators of the invertible endomorphisms span all of them

A `V`-endomorphism `f` acts on the tensor power `⨂[K] (_ : ι), V` diagonally, by
`f^{⊗ι} = PiTensorProduct.map (fun _ ↦ f)`. These diagonal operators are not closed under addition,
so the span of the ones coming from *invertible* `f` is not visibly all of the span of them all.
Over an infinite field and for a finite-dimensional `V` the two spans nonetheless coincide
(`PiTensorProduct.span_range_map_const_units_eq_span_range_map_const`), because the invertible
endomorphisms are Zariski dense. That is what lets the general linear group replace the whole
endomorphism algebra in Schur-Weyl duality, where the commutant of the symmetric-group action is
the span of the diagonal operators and one wants it to be the image of `K[GL(V)]`.

## The argument

A vector of a vector space lies in a subspace as soon as every functional vanishing on the subspace
kills it (`Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff`). So fix a functional `φ` on
`End (⨂[K] (_ : ι), V)` vanishing on the span of the invertible diagonal operators. Composing `φ`
with `PiTensorProduct.mapMultilinear`, which is multilinear in the family of endomorphisms, and with
the matrix-to-endomorphism isomorphism attached to a basis, produces a multilinear form `Θ` in `ι`
matrix arguments whose diagonal is `Θ (Y, …, Y) = φ (Y^{⊗ι})`. That diagonal vanishes on the
invertible matrices, hence identically, by
`MultilinearMap.apply_const_eq_zero_of_eq_zero_on_gl`.

## Main results

* `PiTensorProduct.map_const_mem_span_range_map_const_units`: the diagonal operator of an
  endomorphism is a combination of the diagonal operators of the invertible ones.
* `PiTensorProduct.span_range_map_const_units_eq_span_range_map_const`: consequently the two spans
  agree.
-/

public section

open Matrix

open scoped TensorProduct

namespace PiTensorProduct

universe u v w

variable {K : Type u} {V : Type v} {ι : Type w} [Field K] [Infinite K] [AddCommGroup V]
  [Module K V] [FiniteDimensional K V] [Finite ι]

/-- **The diagonal operator of an endomorphism is a combination of the diagonal operators of the
invertible ones**, over an infinite field and for a finite-dimensional `V`. -/
theorem map_const_mem_span_range_map_const_units (f : V →ₗ[K] V) :
    map (fun _ : ι => f) ∈ Submodule.span K
      (Set.range fun u : (V →ₗ[K] V)ˣ => map fun _ : ι => (u : V →ₗ[K] V)) := by
  classical
  cases nonempty_fintype ι
  set S := Submodule.span K
    (Set.range fun u : (V →ₗ[K] V)ˣ => map fun _ : ι => (u : V →ₗ[K] V)) with _hSdef
  suffices h : ∀ φ : Module.Dual K ((⨂[K] _ : ι, V) →ₗ[K] (⨂[K] _ : ι, V)),
      (∀ y ∈ S, φ y = 0) → φ (map fun _ : ι => f) = 0 by
    exact (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff S _).mp fun φ hφ =>
      h φ ((Submodule.mem_dualAnnihilator _).mp hφ)
  intro φ hφ
  set e := Module.finBasis K V with _
  set Θ : MultilinearMap K
      (fun _ : ι => Matrix (Fin (Module.finrank K V)) (Fin (Module.finrank K V)) K) K :=
    (LinearMap.compMultilinearMap φ
      (mapMultilinear K (fun _ : ι => V) fun _ : ι => V)).compLinearMap
        fun _ => (Matrix.toLinAlgEquiv e).toLinearMap with hΘdef
  have hΘ : ∀ X, (Θ fun _ => X) = φ (map fun _ : ι => Matrix.toLinAlgEquiv e X) := fun _ => by
    simp only [hΘdef, MultilinearMap.compLinearMap_apply, LinearMap.compMultilinearMap_apply,
      mapMultilinear_apply, AlgEquiv.toLinearMap_apply]
  have hgl : ∀ g : GL (Fin (Module.finrank K V)) K,
      (Θ fun _ => (g : Matrix (Fin (Module.finrank K V)) (Fin (Module.finrank K V)) K)) = 0 := by
    intro g
    rw [hΘ]
    obtain ⟨u, hu⟩ := g.isUnit.map (Matrix.toLinAlgEquiv e)
    exact hφ _ (Submodule.subset_span ⟨u, congrArg _ (funext fun _ => hu)⟩)
  have hf := Θ.apply_const_eq_zero_of_eq_zero_on_gl hgl (LinearMap.toMatrixAlgEquiv e f)
  rwa [hΘ, Matrix.toLinAlgEquiv_toMatrixAlgEquiv] at hf

/-- **The diagonal operators of the invertible endomorphisms span the same subspace as all the
diagonal operators**, over an infinite field and for a finite-dimensional `V`. -/
theorem span_range_map_const_units_eq_span_range_map_const :
    Submodule.span K (Set.range fun u : (V →ₗ[K] V)ˣ => map fun _ : ι => (u : V →ₗ[K] V)) =
      Submodule.span K (Set.range fun f : V →ₗ[K] V => map fun _ : ι => f) :=
  le_antisymm (Submodule.span_le.2 (by rintro _ ⟨u, rfl⟩; exact Submodule.subset_span ⟨_, rfl⟩))
    (Submodule.span_le.2 (by
      rintro _ ⟨f, rfl⟩; exact map_const_mem_span_range_map_const_units f))

end PiTensorProduct
end
end TAF_LiteralSource_0401

section TAF_LiteralSource_0402
/- Original module: TauCeti.LinearAlgebra.Matrix.KroneckerPower -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Kronecker powers of matrices

For a matrix `A` with rows indexed by `m`, columns indexed by `n` and a finite type `κ`, the
Kronecker power `Matrix.kroneckerPower κ A` is the matrix with rows indexed by `κ → m` and columns
indexed by `κ → n` whose `(v, u)` entry is `∏ i, A (v i) (u i)`. It is the matrix of `A` acting in
every factor of the `κ`-indexed tensor power, in the monomial bases.

The Kronecker power is multiplicative and commutes with transposition, so if `Aᵀ * A = 1` then
the Kronecker power satisfies the same identity.

## Main definitions

* `Matrix.kroneckerPower`: the `κ`-indexed Kronecker power of a matrix.

## Main results

* `Matrix.kroneckerPower_mul`, `Matrix.kroneckerPower_one`, `Matrix.transpose_kroneckerPower`:
  the Kronecker power is multiplicative, sends `1` to `1` and commutes with transposition.
* `Matrix.transpose_kroneckerPower_mul_self`: the Kronecker power of a matrix with `Aᵀ * A = 1`
  satisfies the same identity.
-/

public section

namespace Matrix

variable {R : Type*} {l m n : Type*} (κ : Type*)

/-- The **Kronecker power** of a matrix `A : Matrix m n R`: the matrix with rows indexed by
`κ → m` and columns indexed by `κ → n` whose `(v, u)` entry is `∏ i, A (v i) (u i)`, the matrix of
`A` acting in every factor of the `κ`-indexed tensor power. -/
def kroneckerPower [CommMonoid R] [Fintype κ] (A : Matrix m n R) : Matrix (κ → m) (κ → n) R :=
  Matrix.of fun v u => ∏ i, A (v i) (u i)

@[simp]
theorem kroneckerPower_apply [CommMonoid R] [Fintype κ] (A : Matrix m n R) (v : κ → m)
    (u : κ → n) :
    A.kroneckerPower κ v u = ∏ i, A (v i) (u i) :=
  (rfl)

variable {κ}

/-- The Kronecker power commutes with transposition. -/
@[simp]
theorem transpose_kroneckerPower [CommMonoid R] [Fintype κ] (A : Matrix m n R) :
    (A.kroneckerPower κ)ᵀ = Aᵀ.kroneckerPower κ :=
  (rfl)

/-- The Kronecker power of the identity matrix is the identity matrix. -/
@[simp]
theorem kroneckerPower_one [CommMonoidWithZero R] [DecidableEq n] [Fintype κ] :
    (1 : Matrix n n R).kroneckerPower κ = 1 := by
  ext v u
  simp only [kroneckerPower_apply, Matrix.one_apply, Fintype.prod_boole, ← funext_iff]

/-- The Kronecker power is multiplicative: the `(v, u)` entry of `A^{⊗κ} * B^{⊗κ}` expands, by
distributing the product over the sums, into the product of the entries of `A * B`. -/
theorem kroneckerPower_mul [CommSemiring R] [Fintype m] [Fintype κ] [DecidableEq κ]
    (A : Matrix l m R) (B : Matrix m n R) :
    (A * B).kroneckerPower κ = A.kroneckerPower κ * B.kroneckerPower κ := by
  ext v u
  simp only [kroneckerPower_apply, Matrix.mul_apply, Fintype.prod_sum, ← Finset.prod_mul_distrib]

/-- The Kronecker power of a matrix `A` with `Aᵀ * A = 1` satisfies the same identity. -/
theorem transpose_kroneckerPower_mul_self [CommSemiring R] [Fintype n] [DecidableEq n]
    [Fintype κ] [DecidableEq κ] {A : Matrix n n R} (hA : Aᵀ * A = 1) :
    (A.kroneckerPower κ)ᵀ * A.kroneckerPower κ = 1 := by
  rw [transpose_kroneckerPower, ← kroneckerPower_mul, hA, kroneckerPower_one]

end Matrix
end
end TAF_LiteralSource_0402

section TAF_LiteralSource_0403
/- Original module: TauCeti.RepresentationTheory.Symmetric.TensorAction.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Permuting tensor factors

This file defines the symmetric-group action on a power of a module by permuting its tensor
factors. Mathlib's `Representation.asAlgebraHom` then extends the action linearly to the group
algebra, which is the action used by Young symmetrizers.

The construction is the first target in Layer 2 of the
[classical-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md)
and the first construction in Layer 8 of the
[Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md).
It reuses `PiTensorProduct.reindex`; the convention is
`σ • (⨂ₜ i, m i) = ⨂ₜ i, m (σ⁻¹ i)`.

## Main definitions

* `PiTensorProduct.reindexRepresentation` is the permutation action for an arbitrary index type
  and module.
* `permTensorAction` specializes it to `(Fin n → R)^{⊗d}`.
* `permTensorActionAlgHom` is its `Representation.asAlgebraHom` extension to `R[S_d]`.
* `TauCeti.tensorPowerBasis` is the monomial basis of `(Rⁿ)^{⊗d}`, on which the action is a
  reindexing.

## Main results

* `TauCeti.finrank_tensorPower` is the dimension count `dim (Rⁿ)^{⊗d} = nᵈ` that the monomial
  basis supplies.
* `Matrix.piTensorProductMap_tensorPowerBasis` and
  `Matrix.toMatrix_piTensorProductMap_tensorPowerBasis`: in the monomial basis, a matrix `A` acting
  in every tensor factor has the Kronecker power `Matrix.kroneckerPower (Fin d) A` as its matrix.
* `PiTensorProduct.map_reindex_range_reindexRepresentation_asAlgebraHom` transports the image of
  a group-algebra element along any equivalence of tensor-factor index types.
-/

public section

open scoped TensorProduct

universe u v w

namespace PiTensorProduct

variable (R : Type u) (M : Type v) (ι : Type w)
variable [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The representation of the permutation group of `ι` on the `ι`-indexed tensor power,
acting by reindexing the tensor factors. -/
noncomputable def reindexRepresentation :
    Representation R (Equiv.Perm ι) (⨂[R] _ : ι, M) where
  toFun σ := (reindex R (fun _ : ι => M) σ).toLinearMap
  map_one' := by
    simpa only [Equiv.Perm.one_def, Module.End.one_eq_id,
      LinearEquiv.refl_toLinearMap] using
      congrArg LinearEquiv.toLinearMap
        (reindex_refl (R := R) (s := fun _ : ι => M))
  map_mul' σ τ := by
    apply LinearMap.ext
    intro x
    simp only [Module.End.mul_apply, LinearEquiv.coe_toLinearMap]
    simpa only [Equiv.Perm.mul_def] using
      (reindex_reindex (R := R) (s := fun _ : ι => M) τ σ x).symm

/-- The permutation representation acts by `PiTensorProduct.reindex`. -/
@[simp]
theorem reindexRepresentation_apply (σ : Equiv.Perm ι) :
    reindexRepresentation R M ι σ = (reindex R (fun _ : ι => M) σ).toLinearMap :=
  (rfl)

/-- Permuting factors commutes with applying the same linear map in every tensor factor. -/
theorem commute_reindexRepresentation_map (σ : Equiv.Perm ι) (f : M →ₗ[R] M) :
    Commute (reindexRepresentation R M ι σ) (map fun _ : ι => f) := by
  apply LinearMap.ext
  intro x
  simpa only [Module.End.mul_apply, reindexRepresentation_apply,
    LinearEquiv.coe_toLinearMap] using
    (map_reindex (f := fun _ : ι => f) σ x).symm

/-- Every element of the group algebra commutes with applying the same linear map in every
tensor factor. -/
theorem commute_reindexRepresentation_asAlgebraHom_map
    (a : MonoidAlgebra R (Equiv.Perm ι)) (f : M →ₗ[R] M) :
    Commute ((reindexRepresentation R M ι).asAlgebraHom a) (map fun _ : ι => f) := by
  induction a using MonoidAlgebra.induction_on with
  | of σ =>
    simpa only [Representation.asAlgebraHom_of] using commute_reindexRepresentation_map R M ι σ f
  | add a b ha hb => simpa only [map_add] using ha.add_left hb
  | smul r a ha => simpa only [map_smul] using ha.smul_left r

/-- The group-algebra action on a pure tensor is the corresponding finite linear combination
of reindexed pure tensors. -/
theorem reindexRepresentation_asAlgebraHom_apply_tprod
    (a : MonoidAlgebra R (Equiv.Perm ι)) (m : ι → M) :
    (reindexRepresentation R M ι).asAlgebraHom a (tprod R m) =
      a.coeff.sum fun σ r => r • tprod R (fun i => m (σ.symm i)) := by
  classical
  simp [Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply, Finsupp.sum,
    LinearMap.sum_apply]

/-- Relabeling tensor factors along an equivalence transports the image of a group-algebra
element onto the image of its transport to the permutation group of the new index type. -/
theorem map_reindex_range_reindexRepresentation_asAlgebraHom {κ : Type*} (e : ι ≃ κ)
    (a : MonoidAlgebra R (Equiv.Perm ι)) :
    (LinearMap.range ((reindexRepresentation R M ι).asAlgebraHom a)).map
        (reindex R (fun _ => M) e : (⨂[R] _ : ι, M) →ₗ[R] (⨂[R] _ : κ, M)) =
      LinearMap.range ((reindexRepresentation R M κ).asAlgebraHom
        (MonoidAlgebra.domCongr R R e.permCongrHom a)) := by
  have h :
      (reindex R (fun _ => M) e).toLinearMap ∘ₗ
          (reindexRepresentation R M ι).asAlgebraHom a =
        (reindexRepresentation R M κ).asAlgebraHom
            (MonoidAlgebra.domCongr R R e.permCongrHom a) ∘ₗ
          (reindex R (fun _ => M) e).toLinearMap := by
    induction a using MonoidAlgebra.induction_on with
    | of σ =>
      ext f
      simp [MonoidAlgebra.of_apply, Equiv.permCongrHom_coe, Equiv.permCongr_def,
        ← Equiv.trans_assoc]
    | add a b ha hb => simp [ha, hb, LinearMap.comp_add, LinearMap.add_comp]
    | smul r a ha => simp [ha, LinearMap.comp_smul, LinearMap.smul_comp]
  rw [← LinearMap.range_comp, h]
  exact LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)

end PiTensorProduct

namespace TauCeti

variable (R : Type u) (n d : ℕ)
variable [CommSemiring R]

/-- The symmetric-group action on `(Fin n → R)^{⊗d}` by permutation of tensor factors. -/
noncomputable def permTensorAction :
    Representation R (Equiv.Perm (Fin d)) (⨂[R] _ : Fin d, Fin n → R) :=
  PiTensorProduct.reindexRepresentation R (Fin n → R) (Fin d)

/-- The symmetric-group action on `(Fin n → R)^{⊗d}` is the reindexing representation for the
index type `Fin d`. -/
theorem permTensorAction_def :
    permTensorAction R n d = PiTensorProduct.reindexRepresentation R (Fin n → R) (Fin d) :=
  (rfl)

/-- A permutation acts on `(Fin n → R)^{⊗d}` by `PiTensorProduct.reindex`. -/
@[simp]
theorem permTensorAction_apply (σ : Equiv.Perm (Fin d)) :
    permTensorAction R n d σ =
      (PiTensorProduct.reindex R (fun _ : Fin d => Fin n → R) σ).toLinearMap :=
  (rfl)

/-- The group-algebra action of `R[S_d]` on `(Fin n → R)^{⊗d}` induced by factor
permutations. -/
noncomputable def permTensorActionAlgHom :
    MonoidAlgebra R (Equiv.Perm (Fin d)) →ₐ[R]
      Module.End R (⨂[R] _ : Fin d, Fin n → R) :=
  (permTensorAction R n d).asAlgebraHom

/-- The group-algebra action of `R[S_d]` is the linear extension of `permTensorAction`. -/
theorem permTensorActionAlgHom_def :
    permTensorActionAlgHom R n d = (permTensorAction R n d).asAlgebraHom :=
  (rfl)

/-- A single permutation, viewed in the group algebra, acts by `permTensorAction`. -/
theorem permTensorActionAlgHom_of (σ : Equiv.Perm (Fin d)) :
    permTensorActionAlgHom R n d (MonoidAlgebra.of R (Equiv.Perm (Fin d)) σ) =
      permTensorAction R n d σ := by
  rw [permTensorActionAlgHom_def, Representation.asAlgebraHom_of]

/-- The group-algebra action of `a ∈ R[S_d]` is the coefficient-weighted sum of the permutation
actions. -/
theorem permTensorActionAlgHom_eq_sum (a : MonoidAlgebra R (Equiv.Perm (Fin d))) :
    permTensorActionAlgHom R n d a = ∑ σ, a.coeff σ • permTensorAction R n d σ := by
  simp [permTensorActionAlgHom_def, Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply,
    Finsupp.sum_fintype]

/-- The group-algebra action on a pure tensor of `(Fin n → R)^{⊗d}` is the corresponding finite
linear combination of reindexed pure tensors. -/
@[simp]
theorem permTensorActionAlgHom_apply_tprod (a : MonoidAlgebra R (Equiv.Perm (Fin d)))
    (m : Fin d → (Fin n → R)) :
    permTensorActionAlgHom R n d a (PiTensorProduct.tprod R m) =
      a.coeff.sum fun σ r => r • PiTensorProduct.tprod R fun i => m (σ.symm i) := by
  rw [permTensorActionAlgHom_def, permTensorAction_def]
  exact PiTensorProduct.reindexRepresentation_asAlgebraHom_apply_tprod R (Fin n → R) (Fin d) a m

/-- Relabeling the tensor factors along `finCongr h`, for `h : m = d`, transports the image of
`a ∈ R[S_m]` onto the image of its transport to `R[S_d]`. -/
theorem map_reindex_range_permTensorAction_asAlgebraHom {m : ℕ} (h : m = d)
    (a : MonoidAlgebra R (Equiv.Perm (Fin m))) :
    (LinearMap.range ((permTensorAction R n m).asAlgebraHom a)).map
        (PiTensorProduct.reindex R (fun _ => Fin n → R) (finCongr h) :
          (⨂[R] _ : Fin m, Fin n → R) →ₗ[R] (⨂[R] _ : Fin d, Fin n → R)) =
      LinearMap.range ((permTensorAction R n d).asAlgebraHom
        (MonoidAlgebra.domCongr R R (finCongr h).permCongrHom a)) := by
  simpa only [permTensorAction_def] using
    PiTensorProduct.map_reindex_range_reindexRepresentation_asAlgebraHom R (Fin n → R) (Fin m)
      (finCongr h) a

/-- The monomial basis of `(Rⁿ)^{⊗d}`: the basis vector at `f : Fin d → Fin n` is the pure tensor
whose `i`-th factor is the `f i`-th standard basis vector of `Rⁿ`. -/
noncomputable def tensorPowerBasis :
    Module.Basis (Fin d → Fin n) R (⨂[R] _ : Fin d, Fin n → R) :=
  Basis.piTensorProduct fun _ => Pi.basisFun R (Fin n)

/-- The monomial basis is the tensor product of the standard bases.  The definition is not
exposed, so this is its defining equation, used to compare it with the `Basis.piTensorProduct`
spelling of the weight theory. -/
theorem tensorPowerBasis_def :
    tensorPowerBasis R n d = Basis.piTensorProduct fun _ : Fin d => Pi.basisFun R (Fin n) :=
  (rfl)

@[simp]
theorem tensorPowerBasis_apply (f : Fin d → Fin n) :
    tensorPowerBasis R n d f = PiTensorProduct.tprod R fun i => Pi.single (f i) (1 : R) := by
  classical
  rw [tensorPowerBasis, Basis.piTensorProduct_apply]
  simp

/-- **The dimension of `(Rⁿ)^{⊗d}` is `nᵈ`**, read off the monomial basis
`TauCeti.tensorPowerBasis`, whose index type is `Fin d → Fin n`. -/
theorem finrank_tensorPower [StrongRankCondition R] :
    Module.finrank R (⨂[R] _ : Fin d, Fin n → R) = n ^ d := by
  rw [Module.finrank_eq_card_basis (tensorPowerBasis R n d), Fintype.card_fun]
  simp

/-- **A matrix acting diagonally on the monomial basis of `(Rⁿ)^{⊗d}`.** Applying `A` in every
tensor factor sends the basis tensor `e_u` to `∑ v, (∏ i, A (v i) (u i)) • e_v`, so its matrix in
the monomial basis is the Kronecker power of `A`. -/
theorem _root_.Matrix.piTensorProductMap_tensorPowerBasis {R : Type u} [CommSemiring R] {n d : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (u : Fin d → Fin n) :
    PiTensorProduct.map (fun _ : Fin d => A.mulVecLin) (tensorPowerBasis R n d u) =
      ∑ v, A.kroneckerPower (Fin d) v u • tensorPowerBasis R n d v := by
  have hcol : ∀ i, A.mulVecLin (Pi.single (u i) (1 : R)) =
      ∑ c, A c (u i) • Pi.single c (1 : R) := fun i => by
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one, ← (Pi.basisFun R (Fin n)).sum_repr
      (A.col (u i))]
    simp [Matrix.col_apply]
  simp only [tensorPowerBasis_apply, PiTensorProduct.map_tprod, hcol,
    MultilinearMap.map_sum_finset, MultilinearMap.map_smul_univ]
  simp

/-- **The matrix of `A^{⊗d}` in the monomial basis is the Kronecker power of `A`.** The matrix of
`A` acting in every tensor factor of `(Rⁿ)^{⊗d}`, in the basis `TauCeti.tensorPowerBasis`, is
`Matrix.kroneckerPower (Fin d) A`. -/
theorem _root_.Matrix.toMatrix_piTensorProductMap_tensorPowerBasis {R : Type u} [CommSemiring R]
    {n d : ℕ} (A : Matrix (Fin n) (Fin n) R) :
    LinearMap.toMatrix (tensorPowerBasis R n d) (tensorPowerBasis R n d)
        (PiTensorProduct.map fun _ : Fin d => A.mulVecLin) =
      A.kroneckerPower (Fin d) := by
  ext v u
  rw [LinearMap.toMatrix_apply, A.piTensorProductMap_tensorPowerBasis u, map_sum]
  simp [Finsupp.single_apply, -tensorPowerBasis_apply]

-- These two derived normal forms remain explicit rewrite lemmas: `simpNF` detects each as already
-- provable from the underlying tensor-action rules, so adding them to the simp set is redundant.
/-- A permutation acts on the monomial basis of `(Rⁿ)^{⊗d}` by precomposing the index function
with its inverse. -/
theorem permTensorAction_tensorPowerBasis (σ : Equiv.Perm (Fin d)) (f : Fin d → Fin n) :
    permTensorAction R n d σ (tensorPowerBasis R n d f) =
      tensorPowerBasis R n d fun i => f (σ.symm i) := by
  simp

/-- A group-algebra basis element acts on a monomial basis vector by precomposition and
scaling. -/
theorem permTensorActionAlgHom_single_tensorPowerBasis (ρ : Equiv.Perm (Fin d)) (r : R)
    (f : Fin d → Fin n) :
    permTensorActionAlgHom R n d (MonoidAlgebra.single ρ r) (tensorPowerBasis R n d f) =
      r • tensorPowerBasis R n d fun i => f (ρ.symm i) := by
  rw [permTensorActionAlgHom_def, Representation.asAlgebraHom_single, LinearMap.smul_apply,
    permTensorAction_tensorPowerBasis]

/-- The group-algebra action on a monomial basis vector is the coefficient-weighted sum of the
precomposed monomial basis vectors. -/
theorem permTensorActionAlgHom_apply_tensorPowerBasis
    (a : MonoidAlgebra R (Equiv.Perm (Fin d))) (f : Fin d → Fin n) :
    permTensorActionAlgHom R n d a (tensorPowerBasis R n d f) =
      ∑ σ ∈ a.coeff.support,
        a.coeff σ • tensorPowerBasis R n d fun i => f (σ.symm i) := by
  rw [tensorPowerBasis_apply, permTensorActionAlgHom_apply_tprod, Finsupp.sum]
  exact Finset.sum_congr rfl fun σ _ => by rw [tensorPowerBasis_apply]

end TauCeti
end
end TAF_LiteralSource_0403

section TAF_LiteralSource_0404
/- Original module: TauCeti.RepresentationTheory.ClassicalGroups.TensorPower -/
/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Tensor powers of the standard representation

This file specializes the diagonal tensor-power construction to the standard representation of
the general linear group. It supplies the tensor powers that underpin the Weyl construction for
polynomial representations, together with the description of their monoid-algebra image over an
infinite field.

## Main results

* `TauCeti.tensorPowerRep` is the `d`-fold tensor power of `stdRep`.
* `TauCeti.tensorPowerFDRep` is its bundled finite-dimensional form.
* `TauCeti.commute_permTensorAction_tensorPowerRep` proves that the general-linear and
  symmetric-group actions commute, and `TauCeti.commute_permTensorActionAlgHom_tensorPowerRep`
  extends that to the whole group algebra `k[S_d]`.
* `TauCeti.permTensorPowerRep` combines the two commuting actions into one representation of
  `S_d × GL n k`, and `TauCeti.range_asAlgebraHom_permTensorAction_le_comap` says that the image of
  any element of `k[S_d]`, such as a Young symmetrizer, is a `GL n k`-subrepresentation.
* `TauCeti.trace_permTensorAction_conj_mul_tensorPowerRep`: for any `g ∈ GL n k`, the trace of a
  permutation of the tensor factors composed with `g^{⊗d}` is a class function of the permutation.
* `TauCeti.tensorPowerPermIntertwiningMap` packages `g^{⊗d}` as an intertwining map of the
  symmetric-group action, and `TauCeti.tensorPowerIntertwiningRep` is the resulting action of
  `GL n k` on the `S_d`-intertwining maps into the tensor power, by composition.
* `TauCeti.toSubmodule_range_tensorPowerRep_asAlgebraHom_eq_span_range_map_const` identifies the
  image of `k[GLₙ]` with the span of all diagonal tensor operators over an infinite field.
-/

public section

open Matrix
open scoped TensorProduct

open PiTensorProduct

universe u

namespace TauCeti

variable (k : Type u) (n d : ℕ)

section CommRing

variable [CommRing k]

/-- The diagonal action of `GL n k` on the `d`-fold tensor power of its standard representation. -/
noncomputable abbrev tensorPowerRep :
    Representation k (GL (Fin n) k) (⨂[k]^d (Fin n → k)) :=
  (stdRep k n).tensorPower d

/-- The tensor power of the standard representation, bundled as an object of `FDRep`. -/
noncomputable abbrev tensorPowerFDRep : FDRep k (GL (Fin n) k) :=
  FDRep.of (tensorPowerRep k n d)

/-- The actions of `GL n k` and the symmetric group on the tensor power commute.

This is the commuting-actions half of Schur--Weyl duality; it makes no double-centralizer claim. -/
theorem commute_permTensorAction_tensorPowerRep (σ : Equiv.Perm (Fin d)) (g : GL (Fin n) k) :
    Commute (permTensorAction k n d σ) (tensorPowerRep k n d g) := by
  rw [tensorPowerRep, Representation.tensorPower_apply, permTensorAction_def]
  exact PiTensorProduct.commute_reindexRepresentation_map k (Fin n → k) (Fin d) σ (stdRep k n g)

variable {k n d} in
/-- **The trace of a permutation of the tensor factors composed with `g^{⊗d}` is a class function
of the permutation**, because the two actions commute. -/
theorem trace_permTensorAction_conj_mul_tensorPowerRep (σ τ : Equiv.Perm (Fin d))
    (g : GL (Fin n) k) :
    LinearMap.trace k _ (permTensorAction k n d (τ * σ * τ⁻¹) * tensorPowerRep k n d g) =
      LinearMap.trace k _ (permTensorAction k n d σ * tensorPowerRep k n d g) := by
  set P := permTensorAction k n d
  set G := tensorPowerRep k n d g
  have hc : P τ⁻¹ * G = G * P τ⁻¹ := (commute_permTensorAction_tensorPowerRep k n d τ⁻¹ g).eq
  have hinv : P τ⁻¹ * P τ = 1 := by rw [← map_mul P, inv_mul_cancel, map_one]
  calc LinearMap.trace k _ (P (τ * σ * τ⁻¹) * G)
      _ = LinearMap.trace k _ (P τ * (P σ * G * P τ⁻¹)) := by
        rw [map_mul P, map_mul P, mul_assoc, hc]
        simp only [mul_assoc]
      _ = LinearMap.trace k _ (P σ * G * (P τ⁻¹ * P τ)) := by
        rw [LinearMap.trace_mul_comm, mul_assoc]
      _ = LinearMap.trace k _ (P σ * G) := by rw [hinv, mul_one]

/-- The whole group algebra `k[S_d]` commutes with the general-linear action on the tensor power,
so a Young symmetrizer cuts out a `GL n k`-subrepresentation. -/
theorem commute_permTensorActionAlgHom_tensorPowerRep
    (a : MonoidAlgebra k (Equiv.Perm (Fin d))) (g : GL (Fin n) k) :
    Commute (permTensorActionAlgHom k n d a) (tensorPowerRep k n d g) := by
  rw [tensorPowerRep, Representation.tensorPower_apply, permTensorActionAlgHom_def,
    permTensorAction_def]
  exact PiTensorProduct.commute_reindexRepresentation_asAlgebraHom_map k (Fin n → k) (Fin d) a
    (stdRep k n g)

/-- **The image of an element of `k[S_d]` in `(kⁿ)^{⊗d}` is stable under `GL n k`**, because the
two actions commute.  In particular a Young symmetrizer cuts out a subrepresentation. -/
theorem range_asAlgebraHom_permTensorAction_le_comap (a : MonoidAlgebra k (Equiv.Perm (Fin d)))
    (g : GL (Fin n) k) :
    LinearMap.range ((permTensorAction k n d).asAlgebraHom a) ≤
      (LinearMap.range ((permTensorAction k n d).asAlgebraHom a)).comap
        (tensorPowerRep k n d g) := by
  rintro _ ⟨x, rfl⟩
  have h := commute_permTensorActionAlgHom_tensorPowerRep k n d a g
  rw [permTensorActionAlgHom_def] at h
  exact ⟨tensorPowerRep k n d g x, LinearMap.congr_fun h.eq x⟩

/-- **The joint action of `S_d × GL n k` on `(kⁿ)^{⊗d}`**: a pair `(σ, g)` acts by permuting the
tensor factors by `σ` after applying `g` in every factor.  It is a representation of the product
group because the two actions commute. -/
noncomputable def permTensorPowerRep :
    Representation k (Equiv.Perm (Fin d) × GL (Fin n) k) (⨂[k]^d (Fin n → k)) :=
  (permTensorAction k n d).noncommCoprod (tensorPowerRep k n d)
    (commute_permTensorAction_tensorPowerRep k n d)

/-- The pair `(σ, g)` acts on `(kⁿ)^{⊗d}` as `σ ∘ g^{⊗d}`. -/
@[simp]
theorem permTensorPowerRep_apply (σ : Equiv.Perm (Fin d)) (g : GL (Fin n) k) :
    permTensorPowerRep k n d (σ, g) = permTensorAction k n d σ * tensorPowerRep k n d g :=
  (rfl)

/-- The operator `g^{⊗d}` on `(kⁿ)^{⊗d}` as an intertwining map of the symmetric-group action:
the diagonal action of `GL n k` commutes with permuting the tensor factors. -/
noncomputable def tensorPowerPermIntertwiningMap (g : GL (Fin n) k) :
    Representation.IntertwiningMap (permTensorAction k n d) (permTensorAction k n d) where
  toLinearMap := tensorPowerRep k n d g
  isIntertwining' σ := (commute_permTensorAction_tensorPowerRep k n d σ g).eq.symm

@[simp]
theorem tensorPowerPermIntertwiningMap_apply (g : GL (Fin n) k) (x : ⨂[k]^d (Fin n → k)) :
    tensorPowerPermIntertwiningMap k n d g x = tensorPowerRep k n d g x :=
  (rfl)

variable {k n d} in
/-- The representation of `GL n k` on the `S_d`-intertwining maps from `ρ` into `(kⁿ)^{⊗d}`, by
composition with `g^{⊗d}`. In a split semisimple setting, when `ρ` is irreducible, this is the
multiplicity space of `ρ` in the tensor power, with its residual action of the general linear
group. -/
noncomputable def tensorPowerIntertwiningRep {W : Type*} [AddCommGroup W] [Module k W]
    (ρ : Representation k (Equiv.Perm (Fin d)) W) :
    Representation k (GL (Fin n) k)
      (Representation.IntertwiningMap ρ (permTensorAction k n d)) where
  toFun g := Representation.IntertwiningMap.llcomp ρ _ _ (tensorPowerPermIntertwiningMap k n d g)
  map_one' := by
    ext f x
    simp only [← Representation.IntertwiningMap.comp_def,
      Representation.IntertwiningMap.toLinearMap_apply, Representation.IntertwiningMap.comp_apply,
      tensorPowerPermIntertwiningMap_apply, map_one, Module.End.one_apply]
  map_mul' g h := by
    ext f x
    simp only [← Representation.IntertwiningMap.comp_def,
      Representation.IntertwiningMap.toLinearMap_apply, Representation.IntertwiningMap.comp_apply,
      tensorPowerPermIntertwiningMap_apply, map_mul, Module.End.mul_apply]

variable {k n d} in
@[simp]
theorem tensorPowerIntertwiningRep_apply_apply {W : Type*} [AddCommGroup W] [Module k W]
    (ρ : Representation k (Equiv.Perm (Fin d)) W) (g : GL (Fin n) k)
    (f : Representation.IntertwiningMap ρ (permTensorAction k n d)) (w : W) :
    tensorPowerIntertwiningRep ρ g f w = tensorPowerRep k n d g (f w) :=
  (rfl)

end CommRing

section InfiniteField

variable [Field k] [Infinite k]

/-- **The general linear group spans the same operators on `(kⁿ)^{⊗d}` as the whole endomorphism
algebra of `kⁿ`**: the span of the diagonal operators `g^{⊗d}` for `g` invertible is the span of all
the diagonal operators `f^{⊗d}`. This is the Zariski density of the invertible endomorphisms of
`kⁿ`, and it needs the field to be infinite. -/
theorem span_range_tensorPowerRep_eq_span_range_map_const :
    Submodule.span k (Set.range (tensorPowerRep k n d)) =
      Submodule.span k (Set.range fun f : (Fin n → k) →ₗ[k] (Fin n → k) =>
        PiTensorProduct.map fun _ : Fin d => f) := by
  have hrange : Set.range (tensorPowerRep k n d) =
      Set.range fun u : ((Fin n → k) →ₗ[k] Fin n → k)ˣ =>
        PiTensorProduct.map fun _ : Fin d => (u : (Fin n → k) →ₗ[k] Fin n → k) := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      refine ⟨Matrix.GeneralLinearGroup.toLin g, ?_⟩
      rw [tensorPowerRep, Representation.tensorPower_apply, stdRep_apply]
      simp [Matrix.GeneralLinearGroup.coe_toLin]
    · rintro ⟨u, rfl⟩
      obtain ⟨g, rfl⟩ := Matrix.GeneralLinearGroup.toLin.surjective u
      refine ⟨g, ?_⟩
      rw [tensorPowerRep, Representation.tensorPower_apply, stdRep_apply]
      simp [Matrix.GeneralLinearGroup.coe_toLin]
  rw [hrange, PiTensorProduct.span_range_map_const_units_eq_span_range_map_const]

/-- **The image of the monoid algebra `k[GLₙ]` in `End ((kⁿ)^{⊗d})` is the span of all the
diagonal operators `f^{⊗d}`**, with `f` ranging over every endomorphism of `kⁿ` and not only the
invertible ones. -/
theorem toSubmodule_range_tensorPowerRep_asAlgebraHom_eq_span_range_map_const :
    Subalgebra.toSubmodule (tensorPowerRep k n d).asAlgebraHom.range =
      Submodule.span k (Set.range fun f : (Fin n → k) →ₗ[k] (Fin n → k) =>
        PiTensorProduct.map fun _ : Fin d => f) := by
  rw [Representation.toSubmodule_range_asAlgebraHom,
    span_range_tensorPowerRep_eq_span_range_map_const]

end InfiniteField

section Field

variable [Field k]

/-- The character of the tensor power is the corresponding power of the standard character.

This is intentionally not a simp lemma: `Representation.char_tensorPower` and `char_stdRep`
already normalize its left-hand side, so registering this specialization would violate `simpNF`. -/
theorem char_tensorPowerRep (g : GL (Fin n) k) : (tensorPowerRep k n d).character g =
      Matrix.trace (g : Matrix (Fin n) (Fin n) k) ^ d := by
  rw [Representation.char_tensorPower, char_stdRep]

/-- The character of the bundled tensor power is the corresponding power of the matrix trace. -/
@[simp]
theorem char_tensorPowerFDRep (g : GL (Fin n) k) : (tensorPowerFDRep k n d).character g =
      Matrix.trace (g : Matrix (Fin n) (Fin n) k) ^ d := by
  simpa only [FDRep.character, FDRep.of_ρ', Representation.character] using
    char_tensorPowerRep k n d g

end Field

end TauCeti
end
end TAF_LiteralSource_0404

section TAF_LiteralSource_0405
/- Original module: TauCeti.RepresentationTheory.ClassicalGroups.Rational -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

-- The two subalgebras of functions on `GL n k` the definitions below are stated against; this
-- module also supplies `MvPolynomial.eval`, in which their coordinate form is written.
-- The subalgebra-generic behaviour of matrix coefficients under change of basis, quotients,
-- tensor products and tensor powers; this module also supplies `Basis.piTensorProduct`, the basis
-- the tensor-power results below are stated against.

/-!
# Rational and polynomial representations of the general linear group

A representation of `GL n ℂ` is **polynomial** when, in some basis of the carrier, every matrix
entry of `ρ g` is a polynomial in the entries `gᵢⱼ`, and **rational** when every entry is such a
polynomial divided by a power of `det g`.  The distinction is the one that separates the
representations arising inside tensor powers of the standard representation from those needing a
determinant twist: `TauCeti.stdRep` and its tensor, symmetric and exterior powers are polynomial, as
is `det ^ m` for `m ≥ 0`, whereas `det ^ (-1)` is rational.

The two definitions quantify existentially over a basis, and the content of this file is that this
costs nothing: the condition holds in *one* basis exactly when it holds in *every* basis
(`TauCeti.isRationalRep_iff_forall_mem_rationalFunctions` and its polynomial companion), because a
change of basis rewrites each entry as a fixed linear combination of the old entries, with
coefficients independent of `g`.  So the existential form is a genuinely basis-independent property
of `ρ`, and the coordinate-entry form is available against whatever basis a computation has in hand.

The bookkeeping is carried by two algebras of functions on the group rather than by the
representations.  `TauCeti.Matrix.GeneralLinearGroup.polynomialFunctions k n` collects the
`f : GL (Fin n) k → k` that evaluate some polynomial in the matrix entries, and
`TauCeti.Matrix.GeneralLinearGroup.rationalFunctions k n` those `f` for which some determinant power
`det ^ m` makes `det ^ m * f` polynomial.  Both are `k`-subalgebras of the functions on the group,
and closure under sums, products and scalars is what reduces every argument below to a single entry
computation: the change-of-basis formula is a sum of scalar multiples, the entries of a tensor
product are products of entries, and a determinant power is one generator.  Those entry computations
are themselves subalgebra-generic, and live in `TauCeti.RepresentationTheory.MatrixCoefficients`.

The two function algebras carry an arbitrary base ring, but the two *representation-level* notions
are stated over `ℂ`. The restriction is not cosmetic: over a finite
field `k` the group `GL n k` is a finite set and every function on it is the evaluation of a
polynomial in the matrix entries, so `TauCeti.Matrix.GeneralLinearGroup.polynomialFunctions k n` is
then the whole function algebra and every finite-dimensional representation would count as
polynomial.  The coordinate-entry condition is faithful to the intended notion only over an infinite
field; here the base field is `ℂ`.

That the negative determinant powers are rational is
`TauCeti.Matrix.GeneralLinearGroup.det_zpow_mem_rationalFunctions`.  Whether a *given*
representation fails to be polynomial is a separate question, not addressed here; so is complete
reducibility of rational representations, which requires the theory of reductive groups.

## Main definitions

* `TauCeti.IsPolynomialRep`, `TauCeti.IsRationalRep`: a representation is polynomial, respectively
  rational, in coordinates.

## Main results

* `TauCeti.isPolynomialRep_iff_forall_mem_polynomialFunctions` and
  `TauCeti.isRationalRep_iff_forall_mem_rationalFunctions`: **basis independence**, the entry
  condition against an arbitrary basis characterises the property.
* `TauCeti.IsRationalRep.dual_apply_mem_rationalFunctions`: the matrix coefficients
  `g ↦ f (ρ g w)` of a rational representation are rational functions, and
  `TauCeti.isRationalRep_iff_forall_dual_apply_mem_rationalFunctions`: this characterises
  rationality of a finite-dimensional representation.
* `TauCeti.IsRationalRep.directSum`: a finite direct sum of rational representations is rational.
* `TauCeti.IsPolynomialRep.isRationalRep`: a polynomial representation is rational.
* `TauCeti.isPolynomialRep_stdRep`: the standard representation is polynomial.
* `TauCeti.isRationalRep_detPowerRep` and `TauCeti.isPolynomialRep_detPowerRep_of_nonneg`:
  `det ^ m` is rational, and polynomial when `0 ≤ m`.
* `TauCeti.IsPolynomialRep.tprod` and `TauCeti.IsRationalRep.tprod`: both properties pass to tensor
  products.
* `TauCeti.IsPolynomialRep.of_surjective` and `TauCeti.IsRationalRep.of_surjective`: both
  properties pass to quotients.
* `TauCeti.IsPolynomialRep.tensorPower`, `TauCeti.IsPolynomialRep.symmetricPower` and
  `TauCeti.IsPolynomialRep.exteriorPower`, together with `TauCeti.IsRationalRep.tensorPower`,
  `TauCeti.IsRationalRep.symmetricPower` and `TauCeti.IsRationalRep.exteriorPower`: both properties
  pass to the functorial powers, whence `TauCeti.isPolynomialRep_tensorPowerRep`,
  `TauCeti.isPolynomialRep_symPowerRep` and `TauCeti.isPolynomialRep_extPowerRep` for the standard
  representation.

-/

public section

open Matrix MvPolynomial TauCeti.Matrix.GeneralLinearGroup

universe u v w x y z

namespace TauCeti

/-! ### Rationality and polynomiality of a representation -/

section Defs

variable {n : ℕ} {W : Type v} [AddCommMonoid W] [Module ℂ W]

/-- **A polynomial representation** of `GL n ℂ`: in some basis of the carrier, every matrix entry of
`ρ g` is a polynomial in the entries of `g`.  The carrier is forced to be finite-dimensional, since
no basis indexed by `Fin (Module.finrank ℂ W)` exists otherwise
(`TauCeti.IsPolynomialRep.finite`).  The condition does not depend on the basis: see
`TauCeti.isPolynomialRep_iff_forall_mem_polynomialFunctions`.

The base field is `ℂ` rather than a general field because the coordinate-entry
condition is faithful only over an infinite field: over a finite `k` the group `GL n k` is finite,
so every function on it — hence every matrix entry of every representation — is polynomial in the
entries of `g`. -/
def IsPolynomialRep (ρ : Representation ℂ (GL (Fin n) ℂ) W) : Prop :=
  ∃ (b : Module.Basis (Fin (Module.finrank ℂ W)) ℂ W)
    (P : Fin (Module.finrank ℂ W) → Fin (Module.finrank ℂ W) → MvPolynomial (Fin n × Fin n) ℂ),
    ∀ (g : GL (Fin n) ℂ) (i j : Fin (Module.finrank ℂ W)),
      LinearMap.toMatrix b b (ρ g) i j
        = MvPolynomial.eval (fun p => (g : Matrix (Fin n) (Fin n) ℂ) p.1 p.2) (P i j)

/-- The coordinate-entry form of `TauCeti.IsPolynomialRep`, as a lemma. -/
theorem isPolynomialRep_iff (ρ : Representation ℂ (GL (Fin n) ℂ) W) :
    IsPolynomialRep ρ ↔ ∃ (b : Module.Basis (Fin (Module.finrank ℂ W)) ℂ W)
      (P : Fin (Module.finrank ℂ W) → Fin (Module.finrank ℂ W) → MvPolynomial (Fin n × Fin n) ℂ),
      ∀ (g : GL (Fin n) ℂ) (i j : Fin (Module.finrank ℂ W)),
        LinearMap.toMatrix b b (ρ g) i j
          = MvPolynomial.eval (fun p => (g : Matrix (Fin n) (Fin n) ℂ) p.1 p.2) (P i j) :=
  (Iff.rfl)

/-- **A rational representation** of `GL n ℂ`: in some basis of the carrier, every matrix entry of
`ρ g` is a polynomial in the entries of `g` divided by a fixed power of `det g`.  The carrier is
forced to be finite-dimensional (`TauCeti.IsRationalRep.finite`), and the condition does not depend
on the basis: see `TauCeti.isRationalRep_iff_forall_mem_rationalFunctions`.  The base field is `ℂ`
for the reason recorded on `TauCeti.IsPolynomialRep`. -/
def IsRationalRep (ρ : Representation ℂ (GL (Fin n) ℂ) W) : Prop :=
  ∃ (b : Module.Basis (Fin (Module.finrank ℂ W)) ℂ W)
    (P : Fin (Module.finrank ℂ W) → Fin (Module.finrank ℂ W) → MvPolynomial (Fin n × Fin n) ℂ)
    (m : ℕ), ∀ (g : GL (Fin n) ℂ) (i j : Fin (Module.finrank ℂ W)),
      LinearMap.toMatrix b b (ρ g) i j
        = ((g : Matrix (Fin n) (Fin n) ℂ).det ^ m)⁻¹ *
          MvPolynomial.eval (fun p => (g : Matrix (Fin n) (Fin n) ℂ) p.1 p.2) (P i j)

/-- The coordinate-entry form of `TauCeti.IsRationalRep`, as a lemma. -/
theorem isRationalRep_iff (ρ : Representation ℂ (GL (Fin n) ℂ) W) :
    IsRationalRep ρ ↔ ∃ (b : Module.Basis (Fin (Module.finrank ℂ W)) ℂ W)
      (P : Fin (Module.finrank ℂ W) → Fin (Module.finrank ℂ W) → MvPolynomial (Fin n × Fin n) ℂ)
      (m : ℕ), ∀ (g : GL (Fin n) ℂ) (i j : Fin (Module.finrank ℂ W)),
        LinearMap.toMatrix b b (ρ g) i j
          = ((g : Matrix (Fin n) (Fin n) ℂ).det ^ m)⁻¹ *
            MvPolynomial.eval (fun p => (g : Matrix (Fin n) (Fin n) ℂ) p.1 p.2) (P i j) :=
  (Iff.rfl)

variable {ρ : Representation ℂ (GL (Fin n) ℂ) W}

/-- The carrier of a polynomial representation is finite-dimensional. -/
theorem IsPolynomialRep.finite (h : IsPolynomialRep ρ) : Module.Finite ℂ W := by
  obtain ⟨b, -⟩ := h
  exact Module.Finite.of_basis b

/-- The carrier of a rational representation is finite-dimensional. -/
theorem IsRationalRep.finite (h : IsRationalRep ρ) : Module.Finite ℂ W := by
  obtain ⟨b, -⟩ := h
  exact Module.Finite.of_basis b

end Defs

section BasisIndependence

variable {n : ℕ} {W : Type v} [AddCommMonoid W] [Module ℂ W]
variable {ρ : Representation ℂ (GL (Fin n) ℂ) W}

/-- **Polynomiality is basis independent.**  A representation is polynomial exactly when, against
*any* chosen basis, each matrix entry is a polynomial function of the entries of `g`. -/
theorem isPolynomialRep_iff_forall_mem_polynomialFunctions {ι : Type w} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ W) :
    IsPolynomialRep ρ ↔
      ∀ i j, (fun g => LinearMap.toMatrix b b (ρ g) i j) ∈ polynomialFunctions ℂ n := by
  have hcard : Module.finrank ℂ W = Fintype.card ι := Module.finrank_eq_card_basis b
  constructor
  · rintro ⟨b₀, P, hP⟩
    exact fun i j => Representation.toMatrix_mem_of_toMatrix_mem (polynomialFunctions ℂ n) b₀ b ρ
      (fun p l => mem_polynomialFunctions.mpr ⟨P p l, fun g => hP g p l⟩) i j
  · intro h
    let e : ι ≃ Fin (Module.finrank ℂ W) := Fintype.equivFinOfCardEq hcard.symm
    have hb : ∀ i j, (fun g => LinearMap.toMatrix (b.reindex e) (b.reindex e) (ρ g) i j)
        ∈ polynomialFunctions ℂ n :=
      fun i j => Representation.toMatrix_mem_of_toMatrix_mem _ b (b.reindex e) ρ h i j
    choose P hP using fun q : Fin (Module.finrank ℂ W) × Fin (Module.finrank ℂ W) =>
      mem_polynomialFunctions.mp (hb q.1 q.2)
    exact ⟨b.reindex e, fun i j => P (i, j), fun g i j => hP (i, j) g⟩

/-- **Rationality is basis independent.**  A representation is rational exactly when, against *any*
chosen basis, each matrix entry is a rational function of the entries of `g`. -/
theorem isRationalRep_iff_forall_mem_rationalFunctions {ι : Type w} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ W) :
    IsRationalRep ρ ↔
      ∀ i j, (fun g => LinearMap.toMatrix b b (ρ g) i j) ∈ rationalFunctions ℂ n := by
  have hcard : Module.finrank ℂ W = Fintype.card ι := Module.finrank_eq_card_basis b
  constructor
  · rintro ⟨b₀, P, m, hP⟩
    refine fun i j => Representation.toMatrix_mem_of_toMatrix_mem _ b₀ b ρ (fun p l => ?_) i j
    exact mem_rationalFunctions_iff_inv.mpr ⟨P p l, m, fun g => hP g p l⟩
  · intro h
    let e : ι ≃ Fin (Module.finrank ℂ W) := Fintype.equivFinOfCardEq hcard.symm
    have hb : ∀ i j, (fun g => LinearMap.toMatrix (b.reindex e) (b.reindex e) (ρ g) i j)
        ∈ rationalFunctions ℂ n :=
      fun i j => Representation.toMatrix_mem_of_toMatrix_mem _ b (b.reindex e) ρ h i j
    obtain ⟨P, m, hPm⟩ := exists_forall_eq_inv_mul_of_forall_mem_rationalFunctions
      (f := fun q : Fin (Module.finrank ℂ W) × Fin (Module.finrank ℂ W) => fun g =>
        LinearMap.toMatrix (b.reindex e) (b.reindex e) (ρ g) q.1 q.2)
      (fun q => hb q.1 q.2)
    exact ⟨b.reindex e, fun i j => P (i, j), m, fun g i j => hPm (i, j) g⟩

/-- A polynomial representation is rational. -/
theorem IsPolynomialRep.isRationalRep (h : IsPolynomialRep ρ) : IsRationalRep ρ := by
  obtain ⟨b, P, hP⟩ := h
  exact (isRationalRep_iff_forall_mem_rationalFunctions b).mpr fun i j =>
    polynomialFunctions_le_rationalFunctions
      (mem_polynomialFunctions.mpr ⟨P i j, fun g => hP g i j⟩)

/-- **A quotient of a polynomial representation is polynomial.**  This is the form in which the
functorial powers below inherit polynomiality from the tensor power. -/
theorem IsPolynomialRep.of_surjective {V : Type y} [AddCommMonoid V] [Module ℂ V]
    {σ : Representation ℂ (GL (Fin n) ℂ) V} (h : IsPolynomialRep ρ)
    (f : Representation.IntertwiningMap ρ σ) (hf : Function.Surjective f) : IsPolynomialRep σ := by
  -- `Module.finBasis` needs an additive group; over the field `ℂ` one is recovered from the module
  -- structure, with negation `(-1) • ·`, extending the given `AddCommMonoid`.
  let _ : AddCommGroup V := Module.addCommMonoidToAddCommGroup ℂ
  obtain ⟨b, P, hP⟩ := h
  have : Module.Finite ℂ W := Module.Finite.of_basis b
  have : Module.Finite ℂ V := Module.Finite.of_surjective f.toLinearMap hf
  exact (isPolynomialRep_iff_forall_mem_polynomialFunctions (Module.finBasis ℂ V)).mpr fun i j =>
    Representation.toMatrix_mem_of_toMatrix_mem_of_surjective (polynomialFunctions ℂ n) b
      (Module.finBasis ℂ V) f hf
      (fun p l => mem_polynomialFunctions.mpr ⟨P p l, fun g => hP g p l⟩) i j

/-- **A quotient of a rational representation is rational.** -/
theorem IsRationalRep.of_surjective {V : Type y} [AddCommMonoid V] [Module ℂ V]
    {σ : Representation ℂ (GL (Fin n) ℂ) V} (h : IsRationalRep ρ)
    (f : Representation.IntertwiningMap ρ σ) (hf : Function.Surjective f) : IsRationalRep σ := by
  -- `Module.finBasis` needs an additive group; over the field `ℂ` one is recovered from the module
  -- structure, with negation `(-1) • ·`, extending the given `AddCommMonoid`.
  let _ : AddCommGroup V := Module.addCommMonoidToAddCommGroup ℂ
  obtain ⟨b, P, m, hP⟩ := h
  have : Module.Finite ℂ W := Module.Finite.of_basis b
  have : Module.Finite ℂ V := Module.Finite.of_surjective f.toLinearMap hf
  exact (isRationalRep_iff_forall_mem_rationalFunctions (Module.finBasis ℂ V)).mpr fun i j =>
    Representation.toMatrix_mem_of_toMatrix_mem_of_surjective (rationalFunctions ℂ n) b
      (Module.finBasis ℂ V) f hf
      (fun p l => mem_rationalFunctions_iff_inv.mpr ⟨P p l, m, fun g => hP g p l⟩) i j

end BasisIndependence

/-! ### Matrix coefficients of a rational representation -/

section MatrixCoefficients

variable {n : ℕ} {W : Type v} [AddCommGroup W] [Module ℂ W]
variable {ρ : Representation ℂ (GL (Fin n) ℂ) W}

/-- **The matrix coefficients of a rational representation are rational functions.** For a linear
functional `f` and a vector `w`, the function `g ↦ f (ρ g w)` is a polynomial in the entries of
`g` divided by a power of `det g`. -/
theorem IsRationalRep.dual_apply_mem_rationalFunctions (h : IsRationalRep ρ)
    (f : Module.Dual ℂ W) (w : W) : (fun g => f (ρ g w)) ∈ rationalFunctions ℂ n := by
  have := h.finite
  let b := Module.finBasis ℂ W
  have hb := (isRationalRep_iff_forall_mem_rationalFunctions b).mp h
  have heq : (fun g => f (ρ g w)) = ∑ i, ∑ j, (b.repr w j * f (b i)) •
      fun g => LinearMap.toMatrix b b (ρ g) i j := by
    funext g
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, LinearMap.toMatrix_apply]
    conv_lhs => rw [← b.sum_repr w]
    simp only [map_sum, map_smul, smul_eq_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    conv_lhs => rw [← b.sum_repr (ρ g (b j))]
    simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [heq]
  exact Subalgebra.sum_mem _ fun i _ => Subalgebra.sum_mem _ fun j _ =>
    Subalgebra.smul_mem _ (hb i j) _

/-- **Rationality from matrix coefficients.** A finite-dimensional representation is rational
exactly when all its matrix coefficients `g ↦ f (ρ g w)` are rational functions. -/
theorem isRationalRep_iff_forall_dual_apply_mem_rationalFunctions [Module.Finite ℂ W] :
    IsRationalRep ρ ↔
      ∀ (f : Module.Dual ℂ W) (w : W), (fun g => f (ρ g w)) ∈ rationalFunctions ℂ n := by
  refine ⟨fun h => h.dual_apply_mem_rationalFunctions, fun h => ?_⟩
  let b := Module.finBasis ℂ W
  refine (isRationalRep_iff_forall_mem_rationalFunctions b).mpr fun i j => ?_
  simpa only [LinearMap.toMatrix_apply, Module.Basis.coord_apply] using h (b.coord i) (b j)

/-- **A finite direct sum of rational representations is rational.** A matrix coefficient of the
direct sum is a sum of matrix coefficients of the summands. -/
theorem IsRationalRep.directSum {ι : Type*} [Finite ι] {V : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    {σ : ∀ i, Representation ℂ (GL (Fin n) ℂ) (V i)} (h : ∀ i, IsRationalRep (σ i)) :
    IsRationalRep (Representation.directSum σ) := by
  classical
  have := Fintype.ofFinite ι
  have (i : ι) : Module.Finite ℂ (V i) := (h i).finite
  refine isRationalRep_iff_forall_dual_apply_mem_rationalFunctions.mpr fun f w => ?_
  have heq : (fun g => f (Representation.directSum σ g w)) =
      ∑ i, fun g => (f ∘ₗ DirectSum.lof ℂ ι V i) (σ i g (w i)) := by
    funext g
    conv_lhs => rw [← DirectSum.sum_univ_of w]
    simp [Representation.directSum_apply, ← DirectSum.lof_eq_of ℂ]
  rw [heq]
  exact Subalgebra.sum_mem _ fun i _ => (h i).dual_apply_mem_rationalFunctions _ _

end MatrixCoefficients

/-! ### The basic examples -/

section Examples

variable (n : ℕ)

/-- **The standard representation is polynomial**: in the standard basis its matrix is `g`
itself. -/
@[simp]
theorem isPolynomialRep_stdRep : IsPolynomialRep (stdRep ℂ n) := by
  refine (isPolynomialRep_iff_forall_mem_polynomialFunctions
    (Pi.basisFun ℂ (Fin n))).mpr fun i j => ?_
  have hentry : (fun g : GL (Fin n) ℂ =>
      LinearMap.toMatrix (Pi.basisFun ℂ (Fin n)) (Pi.basisFun ℂ (Fin n)) (stdRep ℂ n g) i j)
      = fun g : GL (Fin n) ℂ => (g : Matrix (Fin n) (Fin n) ℂ) i j := by
    funext g
    simp [Matrix.mulVec_single]
  rw [hentry]
  exact entry_mem_polynomialFunctions i j

variable {n}

/-- **The determinant powers are rational representations.** -/
@[simp]
theorem isRationalRep_detPowerRep (m : ℤ) : IsRationalRep (detPowerRep ℂ n m) := by
  refine (isRationalRep_iff_forall_mem_rationalFunctions
    (Module.Basis.singleton Unit ℂ)).mpr fun i j => ?_
  have hentry : (fun g : GL (Fin n) ℂ =>
      LinearMap.toMatrix (Module.Basis.singleton Unit ℂ) (Module.Basis.singleton Unit ℂ)
        (detPowerRep ℂ n m g) i j)
      = fun g : GL (Fin n) ℂ => ((Matrix.GeneralLinearGroup.det g ^ m : ℂˣ) : ℂ) := by
    funext g
    rw [LinearMap.toMatrix_singleton]
    simp
  rw [hentry]
  exact det_zpow_mem_rationalFunctions m

/-- **The nonnegative determinant powers are polynomial representations.** -/
@[simp]
theorem isPolynomialRep_detPowerRep_of_nonneg {m : ℤ} (hm : 0 ≤ m) :
    IsPolynomialRep (detPowerRep ℂ n m) := by
  lift m to ℕ using hm
  refine (isPolynomialRep_iff_forall_mem_polynomialFunctions
    (Module.Basis.singleton Unit ℂ)).mpr fun i j => ?_
  have hentry : (fun g : GL (Fin n) ℂ =>
      LinearMap.toMatrix (Module.Basis.singleton Unit ℂ) (Module.Basis.singleton Unit ℂ)
        (detPowerRep ℂ n (m : ℤ) g) i j)
      = fun g : GL (Fin n) ℂ => (g : Matrix (Fin n) (Fin n) ℂ).det ^ m := by
    funext g
    rw [LinearMap.toMatrix_singleton]
    simp [zpow_natCast, Units.val_pow_eq_pow_val]
  rw [hentry]
  exact pow_mem det_mem_polynomialFunctions m

end Examples

section TensorProduct

variable {n : ℕ}
variable {W : Type v} [AddCommMonoid W] [Module ℂ W]
  {W' : Type x} [AddCommMonoid W'] [Module ℂ W']
variable {ρ : Representation ℂ (GL (Fin n) ℂ) W} {σ : Representation ℂ (GL (Fin n) ℂ) W'}

/-- **A tensor product of polynomial representations is polynomial.** -/
theorem IsPolynomialRep.tprod (hρ : IsPolynomialRep ρ) (hσ : IsPolynomialRep σ) :
    IsPolynomialRep (ρ.tprod σ) := by
  -- `Representation.toMatrix_tprod_mem` is stated for additive groups; over the field `ℂ` they are
  -- recovered from the module structures, with negation `(-1) • ·`, extending the given monoids.
  let _ : AddCommGroup W := Module.addCommMonoidToAddCommGroup ℂ
  let _ : AddCommGroup W' := Module.addCommMonoidToAddCommGroup ℂ
  obtain ⟨b, P, hP⟩ := hρ
  obtain ⟨c, Q, hQ⟩ := hσ
  refine (isPolynomialRep_iff_forall_mem_polynomialFunctions (b.tensorProduct c)).mpr fun i j => ?_
  exact Representation.toMatrix_tprod_mem _ b c
    (fun p l => mem_polynomialFunctions.mpr ⟨P p l, fun g => hP g p l⟩)
    (fun p l => mem_polynomialFunctions.mpr ⟨Q p l, fun g => hQ g p l⟩) i j

/-- **A tensor product of rational representations is rational.** -/
theorem IsRationalRep.tprod (hρ : IsRationalRep ρ) (hσ : IsRationalRep σ) :
    IsRationalRep (ρ.tprod σ) := by
  -- `Representation.toMatrix_tprod_mem` is stated for additive groups; over the field `ℂ` they are
  -- recovered from the module structures, with negation `(-1) • ·`, extending the given monoids.
  let _ : AddCommGroup W := Module.addCommMonoidToAddCommGroup ℂ
  let _ : AddCommGroup W' := Module.addCommMonoidToAddCommGroup ℂ
  obtain ⟨b, P, mP, hP⟩ := hρ
  obtain ⟨c, Q, mQ, hQ⟩ := hσ
  refine (isRationalRep_iff_forall_mem_rationalFunctions (b.tensorProduct c)).mpr fun i j => ?_
  exact Representation.toMatrix_tprod_mem _ b c
    (fun p l => mem_rationalFunctions_iff_inv.mpr ⟨P p l, mP, fun g => hP g p l⟩)
    (fun p l => mem_rationalFunctions_iff_inv.mpr ⟨Q p l, mQ, fun g => hQ g p l⟩) i j

end TensorProduct

/-! ### The functorial powers -/

section FunctorialPowers

variable {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
variable {ρ : Representation ℂ (GL (Fin n) ℂ) W}

/-- **A tensor power of a polynomial representation is polynomial.** -/
theorem IsPolynomialRep.tensorPower (h : IsPolynomialRep ρ) (d : ℕ) :
    IsPolynomialRep (ρ.tensorPower d) := by
  obtain ⟨b, P, hP⟩ := h
  refine (isPolynomialRep_iff_forall_mem_polynomialFunctions
    (Basis.piTensorProduct fun _ : Fin d => b)).mpr fun i j => ?_
  exact Representation.toMatrix_tensorPower_mem _ b
    (fun p l => mem_polynomialFunctions.mpr ⟨P p l, fun g => hP g p l⟩) i j

/-- **A tensor power of a rational representation is rational.** -/
theorem IsRationalRep.tensorPower (h : IsRationalRep ρ) (d : ℕ) :
    IsRationalRep (ρ.tensorPower d) := by
  obtain ⟨b, P, m, hP⟩ := h
  refine (isRationalRep_iff_forall_mem_rationalFunctions
    (Basis.piTensorProduct fun _ : Fin d => b)).mpr fun i j => ?_
  exact Representation.toMatrix_tensorPower_mem _ b
    (fun p l => mem_rationalFunctions_iff_inv.mpr ⟨P p l, m, fun g => hP g p l⟩) i j

/-- The canonical map onto the symmetric power, as a surjective intertwining map out of the tensor
power.  It is what makes the symmetric power inherit polynomiality and rationality. -/
private noncomputable def symmetricPowerIntertwiningMap (ρ : Representation ℂ (GL (Fin n) ℂ) W)
    (d : ℕ) : Representation.IntertwiningMap (ρ.tensorPower d) (ρ.symmetricPower d) :=
  LinearMap.intertwiningMap_of_isIntertwiningMap _ _ (SymmetricPower.mk ℂ (Fin d) W) fun g x => by
    simp

private theorem symmetricPowerIntertwiningMap_surjective (ρ : Representation ℂ (GL (Fin n) ℂ) W)
    (d : ℕ) : Function.Surjective (symmetricPowerIntertwiningMap ρ d) :=
  LinearMap.range_eq_top.mp (SymmetricPower.range_mk ℂ (Fin d) W)

/-- The canonical map onto the exterior power, as a surjective intertwining map out of the tensor
power.  It is what makes the exterior power inherit polynomiality and rationality. -/
private noncomputable def exteriorPowerIntertwiningMap (ρ : Representation ℂ (GL (Fin n) ℂ) W)
    (d : ℕ) : Representation.IntertwiningMap (ρ.tensorPower d) (ρ.exteriorPower d) :=
  LinearMap.intertwiningMap_of_isIntertwiningMap _ _ (exteriorPower.fromTensorPower ℂ W d)
    fun g x => by
      simpa using (LinearMap.congr_fun (exteriorPower.map_comp_fromTensorPower d (ρ g)) x).symm

private theorem exteriorPowerIntertwiningMap_surjective (ρ : Representation ℂ (GL (Fin n) ℂ) W)
    (d : ℕ) : Function.Surjective (exteriorPowerIntertwiningMap ρ d) :=
  exteriorPower.fromTensorPower_surjective d

/-- **A symmetric power of a polynomial representation is polynomial.** -/
theorem IsPolynomialRep.symmetricPower (h : IsPolynomialRep ρ) (d : ℕ) :
    IsPolynomialRep (ρ.symmetricPower d) :=
  (h.tensorPower d).of_surjective (symmetricPowerIntertwiningMap ρ d)
    (symmetricPowerIntertwiningMap_surjective ρ d)

/-- **A symmetric power of a rational representation is rational.** -/
theorem IsRationalRep.symmetricPower (h : IsRationalRep ρ) (d : ℕ) :
    IsRationalRep (ρ.symmetricPower d) :=
  (h.tensorPower d).of_surjective (symmetricPowerIntertwiningMap ρ d)
    (symmetricPowerIntertwiningMap_surjective ρ d)

/-- **An exterior power of a polynomial representation is polynomial.** -/
theorem IsPolynomialRep.exteriorPower (h : IsPolynomialRep ρ) (d : ℕ) :
    IsPolynomialRep (ρ.exteriorPower d) :=
  (h.tensorPower d).of_surjective (exteriorPowerIntertwiningMap ρ d)
    (exteriorPowerIntertwiningMap_surjective ρ d)

/-- **An exterior power of a rational representation is rational.** -/
theorem IsRationalRep.exteriorPower (h : IsRationalRep ρ) (d : ℕ) :
    IsRationalRep (ρ.exteriorPower d) :=
  (h.tensorPower d).of_surjective (exteriorPowerIntertwiningMap ρ d)
    (exteriorPowerIntertwiningMap_surjective ρ d)

variable (n d : ℕ)

/-- **The tensor powers of the standard representation are polynomial.** -/
@[simp]
theorem isPolynomialRep_tensorPowerRep : IsPolynomialRep (tensorPowerRep ℂ n d) :=
  (isPolynomialRep_stdRep n).tensorPower d

/-- **The symmetric powers of the standard representation are polynomial.** -/
@[simp]
theorem isPolynomialRep_symPowerRep : IsPolynomialRep (symPowerRep ℂ n d) :=
  (isPolynomialRep_stdRep n).symmetricPower d

/-- **The exterior powers of the standard representation are polynomial.** -/
@[simp]
theorem isPolynomialRep_extPowerRep : IsPolynomialRep (extPowerRep ℂ n d) :=
  (isPolynomialRep_stdRep n).exteriorPower d

end FunctorialPowers

end TauCeti
end
end TAF_LiteralSource_0405

section TAF_LiteralSource_0406
/- Original module: TauCeti.Analysis.InnerProductSpace.Positive.Definite -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# A positive-definite form is the standard one in suitable coordinates

Let `S` be a symmetric operator on a finite-dimensional inner product space `V` whose associated
Hermitian form `⟪S v, w⟫` is positive definite. This file produces a linear automorphism of `V`
along which that form pulls back to the inner product `V` already carries:

`TauCeti.exists_continuousLinearEquiv_inner_map_map` gives `e : V ≃L[𝕜] V` with
`⟪S (e x), e y⟫ = ⟪x, y⟫` for all `x` and `y`.

Equivalently `e` is an isometry from `(V, ⟪·,·⟫)` onto `(V, ⟪S ·, ·⟫)`, so its inverse is the
operator usually written `S ^ (1 / 2)`; the construction here avoids building an operator square
root by scaling an orthonormal eigenbasis of `S` instead. The eigenvalues of `S` are positive
because the form is definite, so dividing the `i`-th eigenvector by `√(λ i)` produces a basis that
is orthonormal *for the form*, and `e` is the map carrying the eigenbasis to it.

## Main statements

* `TauCeti.exists_continuousLinearEquiv_inner_map_map`: a positive-definite symmetric operator's
  form becomes the standard inner product after a change of coordinates.

Only the existence of `e` is exported, since it depends on a choice of eigenbasis. The operator is
taken continuous and the change of coordinates produced is a continuous linear equivalence; on a
finite-dimensional space that is no restriction either way, and it is the form the consumer both
supplies and wants.

The intended consumer is Weyl's unitarian trick: applied to the Gram operator of the Haar-averaged
inner product of a representation of a compact group, this is what turns the invariant form into
an honest unitary structure, in
`TauCeti/RepresentationTheory/Compact/UnitaryModel.lean`.
-/

public section

open RCLike
open scoped InnerProductSpace

namespace TauCeti

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [FiniteDimensional 𝕜 V]

/-- **A positive-definite form is standard in suitable coordinates.** If `S` is a symmetric
operator on a finite-dimensional inner product space whose form `⟪S ·, ·⟫` is positive definite,
then there is a continuous linear automorphism `e` with `⟪S (e x), e y⟫ = ⟪x, y⟫`.

The automorphism is the inverse of the square root of `S`, built without any operator functional
calculus: an orthonormal eigenbasis `b` of `S` has positive eigenvalues `λ i`, so the vectors
`(√(λ i))⁻¹ • b i` are orthonormal for the form `⟪S ·, ·⟫`, and `e` is the automorphism carrying
`b i` to them. -/
theorem exists_continuousLinearEquiv_inner_map_map (S : V →L[𝕜] V)
    (hsymm : (S : V →ₗ[𝕜] V).IsSymmetric) (hpos : ∀ v : V, v ≠ 0 → 0 < re ⟪S v, v⟫_𝕜) :
    ∃ e : V ≃L[𝕜] V, ∀ x y : V, ⟪S (e x), e y⟫_𝕜 = ⟪x, y⟫_𝕜 := by
  classical
  set n := Module.finrank 𝕜 V with hn
  set b := hsymm.eigenvectorBasis hn.symm
  set lam := hsymm.eigenvalues hn.symm
  have hSb : ∀ i, S (b i) = (lam i : 𝕜) • b i := fun i ↦
    hsymm.apply_eigenvectorBasis hn.symm i
  have hbb : ∀ i j, ⟪b i, b j⟫_𝕜 = if i = j then 1 else 0 :=
    orthonormal_iff_ite.mp b.orthonormal
  -- The eigenvalues are positive: `⟪S (b i), b i⟫ = λ i` and the form is definite.
  have hlam : ∀ i, 0 < lam i := fun i ↦ by
    have h := hpos (b i) (b.orthonormal.ne_zero i)
    rw [hSb i, inner_smul_left, hbb i i] at h
    simpa using h
  -- Scaling the `i`-th eigenvector by `(√(λ i))⁻¹` makes the family orthonormal for the form.
  set w : Fin n → 𝕜 := fun i ↦ ((Real.sqrt (lam i))⁻¹ : ℝ) with hwdef
  have hw : ∀ i, IsUnit (w i) := fun i ↦ by
    refine isUnit_iff_ne_zero.mpr ?_
    simp [hwdef, Real.sqrt_eq_zero', (hlam i).not_ge]
  set el : V ≃ₗ[𝕜] V := b.toBasis.equiv (b.toBasis.isUnitSMul hw) (Equiv.refl (Fin n)) with heldef
  set e : V ≃L[𝕜] V := el.toContinuousLinearEquiv with hedef
  have he' : ∀ i, e (b.toBasis i) = w i • b.toBasis i := fun i ↦ by
    simp only [hedef, heldef, LinearEquiv.coe_toContinuousLinearEquiv',
      Module.Basis.equiv_apply, Equiv.refl_apply, Module.Basis.isUnitSMul_apply]
  have he : ∀ i, e (b i) = w i • b i := by simpa only [b.coe_toBasis] using he'
  have hkey : ∀ i j, ⟪S (e (b i)), e (b j)⟫_𝕜 = if i = j then 1 else 0 := fun i j ↦ by
    rw [he i, he j, map_smul, hSb i, smul_smul, inner_smul_left, inner_smul_right, hbb i j]
    rcases eq_or_ne i j with rfl | hij
    · have hr : ((Real.sqrt (lam i))⁻¹ * lam i * (Real.sqrt (lam i))⁻¹ : ℝ) = 1 := by
        have hne : Real.sqrt (lam i) ≠ 0 := (Real.sqrt_pos.mpr (hlam i)).ne'
        field_simp
        exact (Real.sq_sqrt (hlam i).le).symm
      rw [ite_eq_left rfl, mul_one, hwdef, ← RCLike.ofReal_mul, conj_ofReal, ← RCLike.ofReal_mul,
        hr, RCLike.ofReal_one]
    · simp [hij]
  -- Both sides are sesquilinear, so the basis computation determines them.
  refine ⟨e, fun x y ↦ ?_⟩
  rw [← b.sum_inner_mul_inner x y]
  conv_lhs => rw [← b.sum_repr' x, ← b.sum_repr' y]
  simp only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right, hkey]
  simp [inner_conj_symm, mul_comm]

end TauCeti
end
end TAF_LiteralSource_0406

section TAF_LiteralSource_0407
/- Original module: TauCeti.RepresentationTheory.Compact.Haar -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Normalized Haar measure on compact groups

This file normalizes Mathlib's Haar measure on a compact topological group to a probability
measure, and records its left, right, and inversion invariance.

The Layer 0 design follows the [compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/roadmap/representation-theory/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md)
and its accompanying `Suggested.lean`.

Since `haarProb` is a Haar measure and a probability measure, Mathlib's generic API applies to
it directly: `MeasureTheory.Measure.isHaarMeasure_eq_of_isProbabilityMeasure` identifies it with
any other Haar probability measure, and `MeasureTheory.integral_mul_left_eq_self`,
`MeasureTheory.integral_mul_right_eq_self` and `MeasureTheory.integral_inv_eq_self` give the
translation and inversion identities used for averaging representations.
-/

public section

open MeasureTheory Set

namespace TauCeti

section LocallyCompactGroup

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- Haar measure of a nonempty locally compact group has nonzero total mass. -/
theorem haar_univ_ne_zero : (Measure.haar : Measure G) univ ≠ 0 :=
  (Measure.measure_pos_of_nonempty_interior (μ := Measure.haar) (by simp)).ne'

/-- Every probability Haar measure on a locally compact group is right-invariant. -/
theorem isMulRightInvariant_of_isHaarMeasure_of_isProbabilityMeasure (μ : Measure G)
    [μ.IsHaarMeasure] [IsProbabilityMeasure μ] : μ.IsMulRightInvariant where
  map_mul_right_eq_self g := by
    have : (Measure.map (· * g) μ).IsHaarMeasure :=
      Measure.isHaarMeasure_map_mul_right μ g
    have : IsProbabilityMeasure (Measure.map (· * g) μ) :=
      inferInstance
    exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

/-- Every probability Haar measure on a locally compact group is invariant under inversion. -/
theorem isInvInvariant_of_isHaarMeasure_of_isProbabilityMeasure (μ : Measure G)
    [μ.IsHaarMeasure] [IsProbabilityMeasure μ] : μ.IsInvInvariant := by
  have : μ.IsMulRightInvariant :=
    isMulRightInvariant_of_isHaarMeasure_of_isProbabilityMeasure (G := G) μ
  constructor
  let : μ.inv.IsHaarMeasure := {
    toIsFiniteMeasureOnCompacts := inferInstance
    toIsMulLeftInvariant := inferInstance
    toIsOpenPosMeasure := inferInstance }
  let : IsProbabilityMeasure μ.inv := by
    rw [Measure.inv_def]
    infer_instance
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

end LocallyCompactGroup

section CompactGroup

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- Haar measure of a compact group has finite total mass. -/
theorem haar_univ_lt_top : (Measure.haar : Measure G) univ < ⊤ :=
  measure_lt_top _ _

private noncomputable def haarFinite : FiniteMeasure G :=
  ⟨Measure.haar, inferInstance⟩

/-- The finite measure used to normalize Haar measure has underlying measure `Measure.haar`. -/
private theorem haarFinite_toMeasure : (haarFinite G : Measure G) = Measure.haar := by
  ext s _
  rfl

private theorem haarFinite_ne_zero : haarFinite G ≠ 0 := by
  rw [← FiniteMeasure.mass_nonzero_iff]
  apply ENNReal.coe_ne_zero.mp
  rw [FiniteMeasure.ennreal_mass, haarFinite_toMeasure]
  exact haar_univ_ne_zero G

/-- Haar probability measure on a compact topological group. -/
noncomputable def haarProb : Measure G :=
  (haarFinite G).normalize

/-- The definition of normalized Haar measure as a rescaling of Mathlib's Haar measure. -/
theorem haarProb_def :
    haarProb G = ((Measure.haar : Measure G) univ)⁻¹ • Measure.haar :=
  by
    rw [haarProb,
      FiniteMeasure.toMeasure_normalize_eq_of_nonzero (haarFinite G) (haarFinite_ne_zero G)]
    rw [← haarFinite_toMeasure, ← FiniteMeasure.ennreal_mass, ← ENNReal.coe_inv]
    · rfl
    · exact (FiniteMeasure.mass_nonzero_iff (haarFinite G)).mpr (haarFinite_ne_zero G)

instance isProbabilityMeasure_haarProb : IsProbabilityMeasure (haarProb G) := by
  exact (haarFinite G).normalize.property

/-- Normalized Haar measure has total mass one.

Not a `simp` lemma: `simp` already closes this goal from the `IsProbabilityMeasure` instance
via `MeasureTheory.measure_univ`. -/
theorem haarProb_apply_univ : haarProb G univ = 1 :=
  measure_univ

instance isMulLeftInvariant_haarProb : (haarProb G).IsMulLeftInvariant := by
  rw [haarProb_def]
  infer_instance

instance isHaarMeasure_haarProb : (haarProb G).IsHaarMeasure := by
  rw [haarProb_def]
  exact Measure.IsHaarMeasure.smul Measure.haar
    (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))
    (ENNReal.inv_ne_top.mpr (NeZero.ne _))

/-- Normalized Haar measure is invariant under right multiplication. -/
instance isMulRightInvariant_haarProb : (haarProb G).IsMulRightInvariant :=
  isMulRightInvariant_of_isHaarMeasure_of_isProbabilityMeasure (G := G) _

/-- Normalized Haar measure is invariant under inversion. -/
instance isInvInvariant_haarProb : (haarProb G).IsInvInvariant :=
  isInvInvariant_of_isHaarMeasure_of_isProbabilityMeasure (G := G) _

/-- A probability Haar measure on a compact group is the normalized Haar measure. -/
theorem eq_haarProb_of_isHaarMeasure_of_isProbabilityMeasure (μ : Measure G)
    [μ.IsHaarMeasure] [IsProbabilityMeasure μ] : μ = haarProb G :=
  Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

end CompactGroup

end TauCeti
end
end TAF_LiteralSource_0407

section TAF_LiteralSource_0408
/- Original module: TauCeti.RepresentationTheory.Compact.Averaging -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Averaging over compact groups

This file bundles integration against normalized Haar measure as a continuous linear map on
continuous vector-valued functions. It records the norm bound, constants, and invariance under left
and right translation needed for averaging representations.

The implementation reuses Mathlib's Bochner integral, its commutation with continuous linear maps,
and the generic left-, right-, and inversion-invariance lemmas for integrals on groups.

The construction is the averaging operator from Layer 0 of the
[compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/roadmap/representation-theory/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md).
-/

public section

open MeasureTheory

namespace TauCeti

section CompactGroup

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {V : Type*} [NormedAddCommGroup V]

/-- A continuous vector-valued function on a compact group is Bochner integrable against
normalized Haar measure: it is continuous on the compact set `univ`, which carries finite
measure. -/
theorem integrable_continuousMap (f : C(G, V)) :
    Integrable f (haarProb G) := by
  simpa only [integrableOn_univ] using
    f.continuous.continuousOn.integrableOn_compact' (μ := haarProb G) isCompact_univ
      MeasurableSet.univ

section NormedFieldScalars

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace ℝ V] [NormedSpace 𝕜 V]
  [SMulCommClass ℝ 𝕜 V]

/-- Averaging a continuous vector-valued function against normalized Haar measure, as a
continuous linear map.

`V` is not assumed complete, so this is the Bochner integral's junk value `0` unless it is: the
definition and its linear structure need no completeness, and the lemmas below that talk about the
average's actual value (`haarAverage_const`, `norm_haarAverage_eq_one`, and everything reached
through `haarAverage_comp_comm`) ask for `[CompleteSpace V]` precisely because they do. -/
noncomputable def haarAverage : C(G, V) →L[𝕜] V :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ ∫ g, f g ∂haarProb G
      map_add' := fun f h ↦ integral_add
        (integrable_continuousMap G f) (integrable_continuousMap G h)
      map_smul' := fun c f ↦ integral_smul c f }
    1 fun f ↦ by
      rw [one_mul]
      simpa using norm_integral_le_of_norm_le_const
        (μ := haarProb G) (Filter.Eventually.of_forall f.norm_coe_le_norm)

/-- The Haar average is the Bochner integral against normalized Haar measure.

Not a `simp` lemma: `haarAverage` is the normal form here, so that the constant, translation
and inversion lemmas below can be `simp` lemmas. Unfold explicitly with `rw`/`simp` when the
underlying integral is wanted. -/
theorem haarAverage_apply (f : C(G, V)) :
    haarAverage G (𝕜 := 𝕜) f = ∫ g, f g ∂haarProb G :=
  (rfl)

/-- The operator norm of Haar averaging is at most one. -/
theorem norm_haarAverage_le_one :
    ‖haarAverage G (𝕜 := 𝕜) (V := V)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- Haar averaging is norm-nonincreasing for the uniform norm on continuous maps. -/
theorem norm_haarAverage_apply_le (f : C(G, V)) :
    ‖haarAverage G (𝕜 := 𝕜) f‖ ≤ ‖f‖ := by
  simpa using (haarAverage G (𝕜 := 𝕜) (V := V)).le_of_opNorm_le (norm_haarAverage_le_one G) f

/-- The Haar average of a constant function is that constant. -/
@[simp]
theorem haarAverage_const [CompleteSpace V] (v : V) :
    haarAverage G (𝕜 := 𝕜) (ContinuousMap.const G v) = v := by
  simp [haarAverage_apply]

/-- On a nonzero target, Haar averaging has operator norm one. -/
theorem norm_haarAverage_eq_one [Nontrivial V] [CompleteSpace V] :
    ‖haarAverage G (𝕜 := 𝕜) (V := V)‖ = 1 := by
  apply le_antisymm (norm_haarAverage_le_one G) _
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hnorm : ‖ContinuousMap.const G v‖ = ‖v‖ := by
    rw [← (ContinuousMap.linearIsometryBoundedOfCompact G V 𝕜).norm_map]
    exact BoundedContinuousFunction.norm_const_eq v
  have h := (haarAverage G (𝕜 := 𝕜) (V := V)).ratio_le_opNorm
    (ContinuousMap.const G v)
  simpa [haarAverage_const, hnorm, norm_ne_zero_iff.mpr hv] using h

/-- Haar averaging is unchanged by left translation of the argument. -/
@[simp]
theorem haarAverage_comp_mulLeft (f : C(G, V)) (g : G) :
    haarAverage G (𝕜 := 𝕜) (f.comp (ContinuousMap.mulLeft g)) =
      haarAverage G (𝕜 := 𝕜) f := by
  simp only [haarAverage_apply, ContinuousMap.coe_comp, Function.comp_apply,
    ContinuousMap.coe_mulLeft]
  exact integral_mul_left_eq_self f g

/-- Haar averaging is unchanged by right translation of the argument. -/
@[simp]
theorem haarAverage_comp_mulRight (f : C(G, V)) (g : G) :
    haarAverage G (𝕜 := 𝕜) (f.comp (ContinuousMap.mulRight g)) =
      haarAverage G (𝕜 := 𝕜) f := by
  simp only [haarAverage_apply, ContinuousMap.coe_comp, Function.comp_apply,
    ContinuousMap.coe_mulRight]
  exact integral_mul_right_eq_self f g

/-- Haar averaging is unchanged by inversion of the argument. -/
@[simp]
theorem haarAverage_comp_inv (f : C(G, V)) :
    haarAverage G (𝕜 := 𝕜) (f.comp (Homeomorph.inv G : C(G, G))) =
      haarAverage G (𝕜 := 𝕜) f := by
  simp only [haarAverage_apply, ContinuousMap.coe_comp, Function.comp_apply,
    ContinuousMap.coe_ofClass, Homeomorph.coe_inv]
  exact integral_inv_eq_self f (haarProb G)

end NormedFieldScalars

section RCLikeScalars

variable {𝕜 : Type*} [RCLike 𝕜] [NormedSpace ℝ V] [NormedSpace 𝕜 V] [SMulCommClass ℝ 𝕜 V]

/-- Continuous linear maps commute with Haar averaging.

The scalars are assumed to be `RCLike` because Mathlib states
`ContinuousLinearMap.integral_comp_comm` under that hypothesis. -/
@[simp]
theorem _root_.ContinuousLinearMap.haarAverage_comp_comm {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] [NormedSpace 𝕜 W] [SMulCommClass ℝ 𝕜 W] [CompleteSpace V] [CompleteSpace W]
    (L : V →L[𝕜] W) (f : C(G, V)) :
    haarAverage G (𝕜 := 𝕜) ((L : C(V, W)).comp f) = L (haarAverage G (𝕜 := 𝕜) f) := by
  simp only [haarAverage_apply, ContinuousMap.coe_comp, Function.comp_apply,
    ContinuousMap.coe_ofClass]
  exact L.integral_comp_comm (integrable_continuousMap G f)

end RCLikeScalars

end CompactGroup

end TauCeti
end
end TAF_LiteralSource_0408

