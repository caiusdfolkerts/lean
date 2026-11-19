module
public meta import Lean.Util.CollectAxioms
public import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Homology.Augment
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.Preadditive
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.SpanRank
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Algebra.Ring.Subgroup
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Grade
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Finsupp.Order
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.OfFn
public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.SMul
public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Product
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Finsupp.Span
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.Order.Atoms.Finite
public import Mathlib.Order.Basic
public import Mathlib.Order.Fin.Tuple
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Order.PiLex
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SplitIfs
public meta import Lean.Elab.Command
public meta import Lean.Elab.Tactic.Omega

@[expose] public section
namespace PalomarBarycentricTor
/-- Canonical cancellation and scalar-action laws used by the actual complexes. -/
theorem natRightCancelAdd : IsRightCancelAdd ℕ := by infer_instance
def naturalDown : ComplexShape ℕ := @ComplexShape.down ℕ _ natRightCancelAdd _
def naturalUp : ComplexShape ℕ := @ComplexShape.up ℕ _ natRightCancelAdd _
attribute [reducible] naturalDown naturalUp

theorem coefficientSMulComm {K : Type*} [CommRing K] : SMulCommClass K K K := by infer_instance
theorem functionScalarTower {V K : Type*} [CommRing K] : IsScalarTower K K (V → K) := by infer_instance
theorem exteriorScalarComm {V K : Type*} [CommRing K] : SMulCommClass K K (ExteriorAlgebra K (V → K)) := by infer_instance
theorem tensorPreservesZero {R : Type*} [CommRing R] (M : ModuleCat R) : ((CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat R)).flip.obj M).PreservesZeroMorphisms := by infer_instance
attribute [instance 2200] natRightCancelAdd coefficientSMulComm functionScalarTower exteriorScalarComm tensorPreservesZero
end PalomarBarycentricTor
end
@[expose] public section
-- Keep editor information enabled for the stock Lean command processor.
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/- BEGIN FourPapers/Support/Koszul.lean -/
section

section
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
/-! ## Source: CommAlg.ExteriorPower.BaseChange -/
section CheckedSource0
/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/


/-!

# Base change of exterior power

In this PR, we proved that exterior power commutes with arbitrary base change.

# Main Results

* `exteriorPower.baseChangeIso`: for `R`-algebra `S`, the base change isomorphism
  `S ⊗[R] (⋀[R]^i M) ≃ₗ[S] ⋀[S]^i (S ⊗[R] M)`

-/

section

variable (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]

variable (S : Type*) [CommRing S] [Algebra R S]

open TensorProduct

namespace ExteriorAlgebra

/-- Abbreviation of base change of `ExteriorAlgebra.ι`. -/
noncomputable abbrev baseChangeι : S ⊗[R] M →ₗ[S] S ⊗[R] ExteriorAlgebra R M :=
  (ExteriorAlgebra.ι R).baseChange S

lemma baseChangeι_mul_add_swap (x y : S ⊗[R] M) :
    ExteriorAlgebra.baseChangeι R M S x * ExteriorAlgebra.baseChangeι R M S y +
      ExteriorAlgebra.baseChangeι R M S y * ExteriorAlgebra.baseChangeι R M S x = 0 := by
  -- Reduce the anticommutation relation to pure tensors in each variable.
  induction x using TensorProduct.inductionOn with
  | tmul s m =>
    induction y using TensorProduct.inductionOn with
    | tmul t n => simp [Algebra.TensorProduct.tmul_mul_tmul, ExteriorAlgebra.ι_add_mul_swap, mul_comm,
        ← TensorProduct.tmul_add]
    | add y₁ y₂ hy₁ hy₂ =>
      simpa [map_add, add_mul, mul_add, add_assoc, add_left_comm, add_comm] using
        congrArg₂ (· + ·) hy₁ hy₂
  | add x₁ x₂ hx₁ hx₂ =>
    simpa [map_add, add_mul, mul_add, add_assoc, add_left_comm, add_comm] using
      congrArg₂ (· + ·) hx₁ hx₂

lemma baseChangeι_sq_zero (x : S ⊗[R] M) : baseChangeι R M S x * baseChangeι R M S x = 0 := by
  -- Check the square-zero relation by induction on the tensor and use the anticommutation lemma
  -- for the cross term in the add case.
  induction x using TensorProduct.inductionOn with
  | tmul s m => simp [ExteriorAlgebra.baseChangeι, Algebra.TensorProduct.tmul_mul_tmul]
  | add x y hx hy =>
    simp only [map_add, mul_add, add_mul, add_left_comm, add_assoc]
    simp [hx, hy, ExteriorAlgebra.baseChangeι_mul_add_swap R M S x y]

/-- The exterior algebra map from `ExteriorAlgebra S (S ⊗[R] M)` to `S ⊗[R] ExteriorAlgebra R M`,
lift from `ExteriorAlgebra.baseChangeι`. -/
noncomputable def baseChangeExteriorAlgebraToTensor :
    ExteriorAlgebra S (S ⊗[R] M) →ₐ[S] S ⊗[R] ExteriorAlgebra R M :=
  ExteriorAlgebra.lift S
    ⟨ExteriorAlgebra.baseChangeι R M S, ExteriorAlgebra.baseChangeι_sq_zero R M S⟩

end ExteriorAlgebra

namespace exteriorPower

instance : IsScalarTower R S (ExteriorAlgebra S (S ⊗[R] M)) :=
  IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)

lemma baseChangeGenerator_map_update_add (i : ℕ) [DecidableEq (Fin i)] (m : Fin i → M)
    (j : Fin i) (x y : M) :
    (ExteriorAlgebra.ιMulti S i) ((TensorProduct.mk R S M 1) ∘ Function.update m j (x + y)) =
      (ExteriorAlgebra.ιMulti S i) ((TensorProduct.mk R S M 1) ∘ Function.update m j x) +
        (ExteriorAlgebra.ιMulti S i) ((TensorProduct.mk R S M 1) ∘ Function.update m j y) := by
  have hz (z : M) : ((TensorProduct.mk R S M 1) ∘ Function.update m j z) =
    Function.update (((TensorProduct.mk R S M 1) ∘ m)) j ((TensorProduct.mk R S M 1) z) := by
    funext a
    rcases eq_or_ne a j with rfl|ne
    · simp
    · simp [Function.update, ne]
  rw [hz (x + y), hz x, hz y, map_add, (ExteriorAlgebra.ιMulti S i).map_update_add]

lemma baseChangeGenerator_map_update_smul (i : ℕ) [DecidableEq (Fin i)] (m : Fin i → M)
    (j : Fin i) (r : R) (x : M) :
    (ExteriorAlgebra.ιMulti S i) ((TensorProduct.mk R S M 1) ∘ Function.update m j (r • x)) =
      r • (ExteriorAlgebra.ιMulti S i) ((TensorProduct.mk R S M 1) ∘ Function.update m j x) := by
  have hz (z : M) : ((TensorProduct.mk R S M 1) ∘ Function.update m j z) =
    Function.update (((TensorProduct.mk R S M 1) ∘ m)) j ((TensorProduct.mk R S M 1) z) := by
    funext a
    rcases eq_or_ne a j with rfl|ne
    · simp
    · simp [Function.update, ne]
  rw [hz (r • x), hz x]
  simpa using (ExteriorAlgebra.ιMulti S i).map_update_smul
    (((TensorProduct.mk R S M 1) ∘ m)) j (algebraMap R S r) (TensorProduct.mk R S M 1 x)

/-- The alternating map obtained from `ExteriorAlgebra.ιMulti` on compositing with
`TensorProduct.mk R S M 1`. -/
noncomputable def baseChangeGenerator (i : ℕ) : M [⋀^Fin i]→ₗ[R] ExteriorAlgebra S (S ⊗[R] M) where
  toFun m := ExteriorAlgebra.ιMulti S i ((TensorProduct.mk R S M 1) ∘ m)
  map_update_add' := baseChangeGenerator_map_update_add R M S i
  map_update_smul' := baseChangeGenerator_map_update_smul R M S i
  map_eq_zero_of_eq' m j k hjk hjk_ne := by
    have : ((mk R S M 1) ∘ m) j = ((mk R S M 1) ∘ m) k := by
      simpa using congrArg (TensorProduct.mk R S M 1) hjk
    simpa using
      (ExteriorAlgebra.ιMulti S i).map_eq_zero_of_eq (((TensorProduct.mk R S M 1) ∘ m)) this hjk_ne

/-- Auxiliary alternating map for `exteriorPower.baseChangeIsoForward`. -/
noncomputable def baseChangeIsoForwardAux (i : ℕ) : M [⋀^Fin i]→ₗ[R] (⋀[S]^i (S ⊗[R] M)) :=
  (baseChangeGenerator R M S i).codRestrict ((⋀[S]^i (S ⊗[R] M)).restrictScalars R) (fun m =>
    ExteriorAlgebra.ιMulti_range S i (Set.mem_range_self ((TensorProduct.mk R S M 1) ∘ m)))

/-- Forward function of `exteriorPower.baseChangeIso`, lift from the map
`(⋀[R]^i M) →ₗ[R] ⋀[S]^i (S ⊗[R] M)` corresponding to `exteriorPower.baseChangeIsoForwardAux`. -/
noncomputable def baseChangeIsoForward (i : ℕ) : S ⊗[R] (⋀[R]^i M) →ₗ[S] (⋀[S]^i (S ⊗[R] M)) :=
  TensorProduct.AlgebraTensorModule.lift {
    toFun s := s • exteriorPower.alternatingMapLinearEquiv (baseChangeIsoForwardAux R M S i)
    map_add' s t := by simp [add_smul]
    map_smul' s t := by simp [smul_smul] }

lemma baseChangeIsoForward_apply_one_tmul_ιMulti (i : ℕ) (m : Fin i → M) :
    baseChangeIsoForward R M S i (1 ⊗ₜ[R] ιMulti R i m) =
      ιMulti S i ((TensorProduct.mk R S M 1) ∘ m) := by
  rw [exteriorPower.baseChangeIsoForward, TensorProduct.AlgebraTensorModule.lift_tmul]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, one_smul,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

/-- Projection from `ExteriorAlgebra` to exterior power. -/
noncomputable def degreeProjection (i : ℕ) : ExteriorAlgebra R M →ₗ[R] (⋀[R]^i M) :=
  ExteriorAlgebra.liftAlternating (Function.update 0 i (exteriorPower.ιMulti R i))

lemma degreeProjection_apply_ιMulti (i : ℕ) (m : Fin i → M) :
    degreeProjection R M i (ExteriorAlgebra.ιMulti R i m) = ιMulti R i m := by
  rw [exteriorPower.degreeProjection]
  simp

/-- Auxiliary alternating map for `exteriorPower.baseChangeIsoInverse`. -/
noncomputable def baseChangeInverseAlternating (i : ℕ) :
    (S ⊗[R] M) [⋀^Fin i]→ₗ[S] S ⊗[R] (⋀[R]^i M) :=
  (((exteriorPower.degreeProjection R M i).baseChange S).comp
    (ExteriorAlgebra.baseChangeExteriorAlgebraToTensor R M S).toLinearMap).compAlternatingMap
      (ExteriorAlgebra.ιMulti S i)

lemma baseChangeInverseAlternating_apply_tmul (i : ℕ) (s : Fin i → S) (m : Fin i → M) :
    baseChangeInverseAlternating R M S i (fun j ↦ s j ⊗ₜ[R] m j) =
      (Finset.univ.prod fun j ↦ s j) ⊗ₜ[R] exteriorPower.ιMulti R i m := by
  simp only [baseChangeInverseAlternating, LinearMap.comp_apply,
    LinearMap.compAlternatingMap_apply, AlgHom.toLinearMap_apply, ExteriorAlgebra.ιMulti_apply]
  have hprod : (List.ofFn fun j ↦ s j ⊗ₜ[R] ExteriorAlgebra.ι R (m j)).prod =
    (Finset.univ.prod fun j ↦ s j) ⊗ₜ[R] (List.ofFn fun j ↦ ExteriorAlgebra.ι R (m j)).prod := by
    induction i with
    | zero => simp [Algebra.TensorProduct.one_def]
    | succ i ih =>
      rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, ih]
      simp [Algebra.TensorProduct.tmul_mul_tmul, Fin.prod_univ_succ]
  rw [map_list_prod (ExteriorAlgebra.baseChangeExteriorAlgebraToTensor R M S)]
  have himages : List.map (ExteriorAlgebra.baseChangeExteriorAlgebraToTensor R M S)
    (List.ofFn fun j ↦ ExteriorAlgebra.ι S (s j ⊗ₜ[R] m j)) =
      List.ofFn fun j ↦ s j ⊗ₜ[R] ExteriorAlgebra.ι R (m j) := by
    ext j
    simp [ExteriorAlgebra.baseChangeExteriorAlgebraToTensor, ExteriorAlgebra.baseChangeι]
  rw [himages, hprod]
  simpa [ExteriorAlgebra.ιMulti_apply] using
    congrArg ((Finset.univ.prod fun j ↦ s j) ⊗ₜ[R] ·) (degreeProjection_apply_ιMulti R M i m)

/-- Inverse function of `exteriorPower.baseChangeIso`,
obtained from `exteriorPower.baseChangeInverseAlternating`. -/
noncomputable def baseChangeIsoInverse (i : ℕ) : ⋀[S]^i (S ⊗[R] M) →ₗ[S] S ⊗[R] (⋀[R]^i M) :=
  alternatingMapLinearEquiv (baseChangeInverseAlternating R M S i)

lemma baseChangeIsoInverse_apply_tmul (i : ℕ) (s : Fin i → S) (m : Fin i → M) :
    baseChangeIsoInverse R M S i (ιMulti S i (fun j ↦ s j ⊗ₜ[R] m j)) =
      (Finset.univ.prod fun j ↦ s j) ⊗ₜ[R] ιMulti R i m := by
  simp [baseChangeIsoInverse, baseChangeInverseAlternating_apply_tmul]

lemma baseChange_left_inverse (i : ℕ) :
    (baseChangeIsoInverse R M S i).comp (baseChangeIsoForward R M S i) = LinearMap.id := by
  ext m
  have : (TensorProduct.mk R S M 1) ∘ m = fun j ↦ 1 ⊗ₜ[R] m j := rfl
  simp [baseChangeIsoForward_apply_one_tmul_ιMulti, baseChangeIsoInverse, this,
    baseChangeInverseAlternating_apply_tmul R M S i (fun _ ↦ 1) m]

lemma baseChangeIsoForward_surjective (i : ℕ) :
    Function.Surjective (baseChangeIsoForward R M S i) := by
  have eqtop : Submodule.span S (Set.range (TensorProduct.mk R S M 1 : M →ₗ[R] S ⊗[R] M)) = ⊤ := by
    rw [← Set.image_univ, ← Submodule.baseChange_span, Submodule.span_univ,
      Submodule.baseChange_top]
  rw [← LinearMap.range_eq_top, eq_top_iff, ← ιMulti_span_of_span S i _ eqtop,
    Submodule.span_le, Set.image_subset_iff]
  intro a ha
  let m (j : Fin i) : M := Classical.choose (ha (Set.mem_range_self j))
  have aeq : a = (TensorProduct.mk R S M 1) ∘ m := by
    ext j
    exact (Classical.choose_spec (ha (Set.mem_range_self j))).symm
  simp only [Set.mem_preimage, SetLike.mem_coe, LinearMap.mem_range, aeq]
  use 1 ⊗ₜ[R] ιMulti R i m
  rw [baseChangeIsoForward_apply_one_tmul_ιMulti]

lemma baseChange_right_inverse (i : ℕ) :
    (baseChangeIsoForward R M S i).comp (baseChangeIsoInverse R M S i) = LinearMap.id := by
  refine LinearMap.ext (fun x ↦ ?_)
  rcases baseChangeIsoForward_surjective R M S i x with ⟨y, rfl⟩
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]
  rw [← LinearMap.comp_apply _ _ y, exteriorPower.baseChange_left_inverse, LinearMap.id_coe, id_eq]

/-- The commute of exterior power and base change. -/
noncomputable def baseChangeIso (i : ℕ) : S ⊗[R] (⋀[R]^i M) ≃ₗ[S] ⋀[S]^i (S ⊗[R] M) where
  __ := baseChangeIsoForward R M S i
  invFun := baseChangeIsoInverse R M S i
  left_inv x := LinearMap.congr_fun (exteriorPower.baseChange_left_inverse R M S i) x
  right_inv x := LinearMap.congr_fun (exteriorPower.baseChange_right_inverse R M S i) x

lemma baseChangeIso_apply_tmul (i : ℕ) (m : Fin i → M) :
    baseChangeIso R M S i (1 ⊗ₜ[R] (ιMulti R i m)) =
      ιMulti S i ((TensorProduct.mk R S M 1) ∘ m) := by
  simp [exteriorPower.baseChangeIso, baseChangeIsoForward_apply_one_tmul_ιMulti]

lemma baseChangeIso_symm_apply_tmul (i : ℕ) (s : Fin i → S) (m : Fin i → M) :
    (baseChangeIso R M S i).symm (ιMulti S i (fun j ↦ s j ⊗ₜ[R] m j)) =
      (Finset.univ.prod fun j ↦ s j) ⊗ₜ[R] ιMulti R i m := by
  simp [exteriorPower.baseChangeIso, exteriorPower.baseChangeIsoInverse_apply_tmul]

end exteriorPower

end
end CheckedSource0

/-! ## Source: CommAlg.ExteriorPower.Product -/
section CheckedSource1
/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/


/-!

# Exterior power of product module

-/

section

universe u

variable (R : Type u) [CommRing R]

variable (M N : Type*) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

open TensorProduct

namespace ExteriorAlgebra

section RingHelpers

variable {M} in
@[simp]
lemma algebraMapInv_ι (x : M) : algebraMapInv (ι R x) = (0 : R) := by
  simp [algebraMapInv]

variable {M} in
lemma algebraMapInv_algebraMap (r : R) :
    algebraMapInv (algebraMap R (ExteriorAlgebra R M) r) = r :=
  algebraMap_leftInverse M r

variable {M} in
@[simp]
lemma ιInv_ι (x : M) : ιInv (ι R x : ExteriorAlgebra R M) = x :=
  ι_leftInverse x

variable {M} in
@[simp]
lemma ιInv_one : ιInv (1 : ExteriorAlgebra R M) = 0 := by
  let : Module Rᵐᵒᵖ M := Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)
  have : IsCentralScalar R M := ⟨fun r m => rfl⟩
  simp [ιInv]

variable {M} in
@[simp]
lemma ιInv_algebraMap (r : R) : ιInv (algebraMap R (ExteriorAlgebra R M) r) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, ιInv_one, smul_zero]

lemma ι_mul_ι_ring (a b : R) : ι R a * ι R b = 0 := by
  trans a • ι R (1 : R) * b • ι R (1 : R)
  · simp [← map_smul, smul_eq_mul, mul_one]
  · rw [smul_mul_smul_comm, ι_sq_zero, smul_zero]

/-- Every element of the exterior algebra of the base ring decomposes into a scalar part and a
generator part. -/
lemma eq_algebraMap_add_ι (t : ExteriorAlgebra R R) :
    t = algebraMap R _ (algebraMapInv t) + ι R (ιInv t) := by
  induction t using ExteriorAlgebra.induction with
  | algebraMap r => simp
  | ι x => simp
  | add a b ha hb =>
    nth_rw 1 [ha, hb]
    simp [map_add, ← add_assoc, ← add_comm ((ι R) (ιInv a))]
  | mul a b ha hb =>
    obtain ⟨α, x, ha⟩ : ∃ α x, a = algebraMap R _ α + ι R x := ⟨_, _, ha⟩
    obtain ⟨β, y, hb⟩ : ∃ β y, b = algebraMap R _ β + ι R y := ⟨_, _, hb⟩
    subst ha hb
    have e1 : algebraMap R (ExteriorAlgebra R R) α * ι R y = ι R (α • y) := by
      rw [← Algebra.smul_def, ← map_smul]
    have e2 : (ι R x : ExteriorAlgebra R R) * algebraMap R _ β = ι R (β • x) := by
      rw [← Algebra.commutes, ← Algebra.smul_def, ← map_smul]
    rw [add_mul, mul_add, mul_add, ι_mul_ι_ring, e1, e2, ← map_mul, add_zero, add_assoc, ← map_add]
    simp [-map_mul]

variable {R} in
/-- The exterior algebra of the base ring is a free module of rank two, with basis `1, ι 1`. -/
noncomputable def prodRingEquiv : (R × R) ≃ₗ[R] ExteriorAlgebra R R where
  __ := LinearMap.coprod (Algebra.linearMap R (ExteriorAlgebra R R)) (ι R)
  invFun := algebraMapInv.toLinearMap.prod ιInv
  left_inv x := by simp
  right_inv x := by simp [← eq_algebraMap_add_ι R x]

variable {R} in
@[simp]
lemma prodRingEquiv_apply (c : R × R) :
    prodRingEquiv c = algebraMap R (ExteriorAlgebra R R) c.1 + ι R c.2 := rfl

end RingHelpers

variable {N} in
/-- The exterior algebra of `M × R` is, as a module, the product of two copies of the exterior
algebra of `M`; the pair `(x, y)` corresponds to `x + y ∧ ι (0, 1)`. -/
noncomputable def prodEquivProd :
    (ExteriorAlgebra R M × ExteriorAlgebra R M) ≃ₗ[R] ExteriorAlgebra R (M × R) :=
  (LinearEquiv.prodCongr (TensorProduct.rid R (ExteriorAlgebra R M)).symm
      (TensorProduct.rid R (ExteriorAlgebra R M)).symm).trans <|
    ((TensorProduct.prodRight R R (ExteriorAlgebra R M) R R).symm).trans <|
      (TensorProduct.congr (LinearEquiv.refl R _) prodRingEquiv).trans <|
        ((GradedTensorProduct.of R _ _).trans (prodEquivTensor R M R).symm.toLinearEquiv)

lemma prodEquivProd_apply (x y : ExteriorAlgebra R M) :
    prodEquivProd R M (x, y) = ExteriorAlgebra.map (LinearMap.inl R M R) x +
      ExteriorAlgebra.map (LinearMap.inl R M R) y * ι R ((0, 1) : M × R) := by
  have hsplit : (x ⊗ₜ[R] (1 : R), y ⊗ₜ[R] (1 : R)) =
    (x ⊗ₜ[R] 1, x ⊗ₜ[R] 0) + (y ⊗ₜ[R] 0, y ⊗ₜ[R] 1) := by simp
  simp only [prodEquivProd, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
    TensorProduct.rid_symm_apply]
  rw [hsplit, map_add, TensorProduct.prodRight_symm_tmul, TensorProduct.prodRight_symm_tmul,
    map_add, TensorProduct.congr_tmul, TensorProduct.congr_tmul, map_add, map_add]
  simp only [LinearEquiv.refl_apply, prodRingEquiv_apply, map_one, map_zero, add_zero, zero_add,
    AlgEquiv.toLinearEquiv_apply]
  simp [prodEquivTensor_symm_tmul, prodEquivTensor_symm_tmul, map_apply_ι]

lemma prodEquivProd_comp_inl :
    (ExteriorAlgebra.prodEquivProd R M).comp (LinearMap.inl R _ _) =
      ExteriorAlgebra.map (LinearMap.inl R M R) := by
  refine LinearMap.ext fun x => ?_
  simp [prodEquivProd_apply]

lemma prodEquivProd_apply_snd (a : ExteriorAlgebra R M) :
    ExteriorAlgebra.prodEquivProd R M (0, a) =
      (ExteriorAlgebra.map (LinearMap.inl R M R) a) * ExteriorAlgebra.ι R ((0, 1) : M × R) := by
  rw [prodEquivProd_apply, map_zero, zero_add]

section MemDecomp

variable {R M N}

lemma map_mem_exteriorPower (f : M →ₗ[R] N) {k : ℕ} {w : ExteriorAlgebra R M} (hw : w ∈ ⋀[R]^k M) :
    ExteriorAlgebra.map f w ∈ ⋀[R]^k N := by
  simpa [exteriorPower.coe_map] using (exteriorPower.map k f ⟨w, hw⟩).2

lemma ι_mul_mem_exteriorPower_anticomm {k : ℕ} {w : ExteriorAlgebra R M} (hw : w ∈ ⋀[R]^k M)
    (z : M) : ι R z * w = ((-1 : ℤ) ^ k) • (w * ι R z) := by
  rw [← ιMulti_span_fixedDegree] at hw
  induction hw using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨v, rfl⟩ := ha
    exact ι_mul_ιMulti_anticomm _ _ _
  | zero => simp
  | add a b _ _ iha ihb => rw [mul_add, iha, ihb, add_mul, smul_add]
  | smul c a _ ih => simp [ih]

/-- Every element of `⋀[R]^(i+1) (M × R)` decomposes as `map inl x + map inl y * ι (0, 1)` with
`x` and `y` of the appropriate degrees. -/
lemma exists_decomp (i : ℕ) :
    ∀ z ∈ ⋀[R]^(i + 1) (M × R), ∃ x ∈ ⋀[R]^(i + 1) M, ∃ y ∈ ⋀[R]^i M,
      z = ExteriorAlgebra.map (LinearMap.inl R M R) x +
        ExteriorAlgebra.map (LinearMap.inl R M R) y * ι R ((0, 1) : M × R) := by
  induction i with
  | zero =>
    intro z hz
    rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hz
    induction hz using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨v, rfl⟩ := hw
      refine ⟨ι R (v 0).1, by simp, algebraMap R _ (v 0).2, ?_, ?_⟩
      · rw [Algebra.algebraMap_eq_smul_one]
        exact Submodule.smul_mem _ _ (SetLike.one_mem_graded _)
      · simp [map_apply_ι, AlgHom.commutes, ← Algebra.smul_def, ← map_smul, ← map_add]
    | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
    | add a b _ _ iha ihb =>
      obtain ⟨xa, hxa, ya, hya, rfl⟩ := iha
      obtain ⟨xb, hxb, yb, hyb, rfl⟩ := ihb
      refine ⟨xa + xb, add_mem hxa hxb, ya + yb, add_mem hya hyb, ?_⟩
      rw [map_add, map_add, add_mul]
      abel
    | smul c a _ ih =>
      obtain ⟨x, hx, y, hy, rfl⟩ := ih
      refine ⟨c • x, Submodule.smul_mem _ _ hx, c • y, Submodule.smul_mem _ _ hy, ?_⟩
      rw [map_smul, map_smul, smul_add, smul_mul_assoc]
  | succ i IH =>
    intro z hz
    rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hz
    induction hz using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨v, rfl⟩ := hw
      obtain ⟨x, hx, y, hy, heq⟩ := IH _
        (ExteriorAlgebra.ιMulti_range R (i + 1) (Set.mem_range_self (Matrix.vecTail v)))
      have hι1 : ι R ((v 0).1) ∈ ⋀[R]^1 M := by simp
      have hv0 : ι R (v 0) = ExteriorAlgebra.map (LinearMap.inl R M R) (ι R (v 0).1) +
          (v 0).2 • ι R ((0, 1) : M × R) := by
        rw [map_apply_ι, ← map_smul, ← map_add]
        simp
      refine ⟨ι R (v 0).1 * x, ?_, ι R (v 0).1 * y + (((-1 : R) ^ (i + 1)) * (v 0).2) • x, ?_, ?_⟩
      · simpa [Nat.add_comm 1 (i + 1)] using SetLike.mul_mem_graded hι1 hx
      · refine add_mem ?_ (Submodule.smul_mem _ _ hx)
        simpa [Nat.add_comm 1 i] using SetLike.mul_mem_graded hι1 hy
      · have hD : ι R (0, 1) * (ExteriorAlgebra.map (LinearMap.inl R M R) y * ι R (0, 1)) = 0 := by
          rw [← mul_assoc, ι_mul_mem_exteriorPower_anticomm (map_mem_exteriorPower _ hy),
            smul_mul_assoc, mul_assoc, ι_sq_zero, mul_zero, smul_zero]
        rw [ιMulti_succ_apply, heq, hv0, add_mul, mul_add, mul_add, smul_mul_assoc, smul_mul_assoc,
          hD, smul_zero, add_zero, ι_mul_mem_exteriorPower_anticomm (map_mem_exteriorPower _ hx)]
        simp [← algebraMap_smul R (R := ℤ), smul_smul, mul_comm ((v 0).2), add_mul, ← mul_assoc,
          add_assoc]
    | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
    | add a b _ _ iha ihb =>
      obtain ⟨xa, hxa, ya, hya, rfl⟩ := iha
      obtain ⟨xb, hxb, yb, hyb, rfl⟩ := ihb
      refine ⟨xa + xb, add_mem hxa hxb, ya + yb, add_mem hya hyb, ?_⟩
      simp only [← add_assoc, map_add, add_mul]
      abel
    | smul c a _ ih =>
      obtain ⟨x, hx, y, hy, rfl⟩ := ih
      refine ⟨c • x, Submodule.smul_mem _ _ hx, c • y, Submodule.smul_mem _ _ hy, ?_⟩
      rw [map_smul, map_smul, smul_add, smul_mul_assoc]

end MemDecomp

lemma prodEquivProd_mem_exteriorPower (i : ℕ) (x y : ExteriorAlgebra R M) :
    ExteriorAlgebra.prodEquivProd R M (x, y) ∈ ⋀[R]^(i + 1) (M × R) ↔
    (x ∈ ⋀[R]^(i + 1) M ∧ y ∈ ⋀[R]^i M) := by
  refine ⟨fun h ↦ ?_, fun ⟨hx, hy⟩ ↦ ?_⟩
  · rw [prodEquivProd_apply] at h
    obtain ⟨x', hx', y', hy', heq⟩ := exists_decomp i _ h
    have hinj : (x, y) = (x', y') := by
      apply (prodEquivProd R M).injective
      rw [prodEquivProd_apply, prodEquivProd_apply, heq]
    obtain ⟨h1, h2⟩ := Prod.mk.injEq .. ▸ hinj
    exact ⟨h1 ▸ hx', h2 ▸ hy'⟩
  · rw [prodEquivProd_apply]
    refine add_mem (map_mem_exteriorPower _ hx) ?_
    have hι : ι R ((0, 1) : M × R) ∈ ⋀[R]^1 (M × R) := by simp
    exact SetLike.mul_mem_graded (map_mem_exteriorPower _ hy) hι

end ExteriorAlgebra

set_option backward.isDefEq.respectTransparency false in
open ExteriorAlgebra in
/-- The `(i+1)`-st exterior power of `M × R` decomposes as the product of the `(i+1)`-st and the
`i`-th exterior powers of `M`. -/
noncomputable def exteriorPowerProdEquivProd (i : ℕ) :
    (⋀[R]^(i + 1) M × ⋀[R]^i M) ≃ₗ[R] ⋀[R]^(i + 1) (M × R) :=
  LinearEquiv.ofBijective
    (LinearMap.codRestrict _ ((prodEquivProd R M).toLinearMap.comp
      ((⋀[R]^(i + 1) M).subtype.prodMap ((⋀[R]^i M).subtype)))
      fun c => (prodEquivProd_mem_exteriorPower R M i c.1 c.2).mpr ⟨c.1.2, c.2.2⟩)
    ⟨by simp [← LinearMap.ker_eq_bot], fun z => by
      obtain ⟨w, hw⟩ := (prodEquivProd R M).surjective z.1
      have hmem := (prodEquivProd_mem_exteriorPower R M i w.1 w.2).mp (by simp [hw])
      exact ⟨(⟨w.1, hmem.1⟩, ⟨w.2, hmem.2⟩), Subtype.ext hw⟩⟩

lemma exteriorPowerProdEquivProd_apply_coe (i : ℕ) (x : ⋀[R]^(i + 1) M) (y : ⋀[R]^i M) :
    (exteriorPowerProdEquivProd R M i) (x, y) = ExteriorAlgebra.prodEquivProd R M (x, y) :=
  rfl

lemma exteriorPowerProdEquivProd_apply_inl_ιMulti (i : ℕ) (m : Fin (i + 1) → M) :
    (exteriorPowerProdEquivProd R M i) (exteriorPower.ιMulti R (i + 1) m, 0) =
      exteriorPower.ιMulti R (i + 1) ((LinearMap.inl R M R) ∘ m) := by
  apply Subtype.ext
  rw [exteriorPowerProdEquivProd_apply_coe, ZeroMemClass.coe_zero,
    ExteriorAlgebra.prodEquivProd_apply, map_zero, zero_mul, add_zero,
    exteriorPower.ιMulti_apply_coe, exteriorPower.ιMulti_apply_coe,
    ExteriorAlgebra.map_apply_ιMulti]

lemma exteriorPowerProdEquivProd_comp_inl (i : ℕ) :
    (exteriorPowerProdEquivProd R M i).toLinearMap.comp (LinearMap.inl R _ _) =
    exteriorPower.map (i + 1) (LinearMap.inl R _ _) := by
  ext m
  have : Matrix.vecTail ((LinearMap.inl R M R) ∘ m) =
    fun j ↦ Matrix.vecTail (fun i ↦ Prod.mk (m i)) j 0 := rfl
  simp [exteriorPowerProdEquivProd_apply_inl_ιMulti, ← this]

lemma exteriorPowerProdEquivProd_apply_inr_ιMulti (i : ℕ) (m : Fin i → M) :
    (exteriorPowerProdEquivProd R M i) (0, exteriorPower.ιMulti R i m) =
      ExteriorAlgebra.ιMulti R i ((LinearMap.inl R M R) ∘ m) *
        ExteriorAlgebra.ι R ((0, 1) : M × R) := by
  rw [exteriorPowerProdEquivProd_apply_coe, ZeroMemClass.coe_zero,
    ExteriorAlgebra.prodEquivProd_apply, map_zero, zero_add,
    exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.map_apply_ιMulti]

end
end CheckedSource1

/-! ## Source: CommAlg.KoszulComplex.Complex -/
section CheckedSource2
/-
Copyright (c) 2026 Nailin Guan, Jingting Wang, Yi Yuan, Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Jingting Wang, Yi Yuan, Yongle Hu
-/


/-!
# The Koszul complex

Given a commutative ring `R`, an `R`-module `M` and a linear map `φ : M →ₗ[R] R`, the
*Koszul complex* `K(φ)` is the chain complex of `R`-modules whose `n`-th term is the exterior
power `⋀[R]^n M` and whose differential `⋀[R]^(n + 1) M → ⋀[R]^n M` is

`x₀ ∧ ⋯ ∧ xₙ ↦ ∑ i, (-1) ^ i • φ (xᵢ) • x₀ ∧ ⋯ ∧ x̂ᵢ ∧ ⋯ ∧ xₙ`.

The Koszul complex of a sequence `f₁, …, fᵣ` of elements of `R` is the special case
`M = Rʳ`, `φ = (a₁, …, aᵣ) ↦ ∑ aᵢ fᵢ`.

## Main definitions

* `koszulComplex.dAlternating φ n`: the alternating map `M [⋀^Fin (n + 1)]→ₗ[R] ⋀[R]^n M`
  displayed above, defined as the alternatisation of `x ↦ φ x • ιMulti`.
* `koszulComplex.d φ n`: the induced linear map `⋀[R]^(n + 1) M →ₗ[R] ⋀[R]^n M`, the Koszul
  differential.
* `koszulComplex φ`: the Koszul complex of `φ`, as a `HomologicalComplex (ModuleCat R) PalomarBarycentricTor.naturalDown`.
* `koszulComplex.ofList l`: the Koszul complex of a list `l` of elements of `R`.
* `koszulComplex.map`: the chain map `koszulComplex φ ⟶ koszulComplex φ'` induced by a
  linear map `f : M →ₗ[R] N` with `φ' ∘ₗ f = φ`, and `koszulComplex.isoOfEquiv`, the
  isomorphism induced by a linear equivalence.

## Main results

* `koszulComplex.d_comp_eq_zero`: the Koszul differential squares to zero.
* `koszulComplex.map_comp`: `koszulComplex.map` is compatible with composition.
* `koszulComplex.isZero_X_of_card_generators_lt`: if `M` is generated by `k` elements then
  `koszulComplex φ` vanishes in degrees `> k`; in particular
  (`koszulComplex.isZero_X_ofList_of_length_lt`) the Koszul complex of a list of length `r`
  vanishes in degrees `> r`.

## Implementation notes

* The Stacks project defines the Koszul complex as a commutative differential graded algebra,
  the exterior algebra `⋀ M` with `d` the unique derivation extending `φ`; here we only record
  the underlying chain complex.

## References

* [The Stacks project, Section 15.29 *The Koszul complex*](https://stacks.math.columbia.edu/tag/0621)
-/

section

universe u v

open CategoryTheory Category Limits Module ExteriorAlgebra

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] (φ : M →ₗ[R] R)

/-- The alternating map for the Koszul differential. -/
noncomputable def koszulComplex.dAlternating (n : ℕ) :
    M [⋀^Fin (n + 1)]→ₗ[R] ⋀[R]^n M :=
  AlternatingMap.alternatizeUncurryFin (φ.smulRight (exteriorPower.ιMulti R n))
/-- Defining formula for the differential used in the Tor comparison. -/
theorem koszulComplex.dAlternating_palomar_formula (n : ℕ) : koszulComplex.dAlternating φ n = AlternatingMap.alternatizeUncurryFin (φ.smulRight (exteriorPower.ιMulti R n)) := rfl

lemma koszulComplex.dAlternating_apply (n : ℕ) (x : Fin (n + 1) → M) :
    koszulComplex.dAlternating φ n x =
      ∑ i : Fin (n + 1),
        ((-1 : R) ^ (i : ℕ) * φ (x i)) • exteriorPower.ιMulti R n (i.removeNth x) := by
  rw [koszulComplex.dAlternating, AlternatingMap.alternatizeUncurryFin_apply]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp [← Int.cast_smul_eq_zsmul R, smul_smul]

/-- The differential for Koszul complex. -/
noncomputable def koszulComplex.d (n : ℕ) : ⋀[R]^(n + 1) M →ₗ[R] ⋀[R]^n M :=
  exteriorPower.alternatingMapLinearEquiv (koszulComplex.dAlternating φ n)
/-- Defining formula for the differential used in the Tor comparison. -/
theorem koszulComplex.d_palomar_formula (n : ℕ) : koszulComplex.d φ n = exteriorPower.alternatingMapLinearEquiv (koszulComplex.dAlternating φ n) := rfl

lemma koszulComplex.d_comp_eq_zero (n : ℕ) :
    koszulComplex.d φ n ∘ₗ koszulComplex.d φ (n + 1) = 0 := by
  let β : M →ₗ[R] M →ₗ[R] M [⋀^Fin n]→ₗ[R] ⋀[R]^n M :=
    φ.smulRight (φ.smulRight (exteriorPower.ιMulti R n))
  have hβ (x y : M) : β x y = β y x := by
    ext v
    simp [β, smul_smul, mul_comm]
  have : (koszulComplex.d φ n).compAlternatingMap (koszulComplex.dAlternating φ (n + 1)) = 0 := by
    rw [← AlternatingMap.alternatizeUncurryFin_alternatizeUncurryFinLM_comp_of_symmetric hβ]
    ext v
    simp [koszulComplex.d, koszulComplex.dAlternating, β,
      AlternatingMap.alternatizeUncurryFin_apply, Finset.smul_sum]
  simpa [koszulComplex.d, ← exteriorPower.alternatingMapLinearEquiv_comp]

/-- The Koszul complex, with objects exterior powers and differential `koszulComplex.d`. -/
@[stacks 0622 "only recording chain complex"]
noncomputable def koszulComplex : HomologicalComplex (ModuleCat R) PalomarBarycentricTor.naturalDown :=
  ChainComplex.of (fun n ↦ ModuleCat.of R (⋀[R]^n M))
    (fun n ↦ ModuleCat.ofHom (koszulComplex.d φ n))
    (fun n ↦ by rw [← ModuleCat.ofHom_comp, koszulComplex.d_comp_eq_zero, ModuleCat.ofHom_zero])

lemma koszulComplex.X_eq_exteriorPower (i : ℕ) :
    (koszulComplex φ).X i = ModuleCat.of R (⋀[R]^i M) := rfl

lemma koszulComplex.d_eq_d (i : ℕ) :
    (koszulComplex φ).d (i + 1) i = ModuleCat.ofHom (koszulComplex.d φ i) := by
  simp [koszulComplex]

namespace koszulComplex

variable {N : Type v} [AddCommGroup N] [Module R N]

/-- The Koszul complex generated by a list of elements in the ring. -/
@[stacks 0623]
noncomputable def ofList (l : List R) := koszulComplex (Fintype.linearCombination R l.get)

section functoriality

lemma map_dAlternating_apply (f : M →ₗ[R] N) (φ' : N →ₗ[R] R) (h : φ' ∘ₗ f = φ)
    (i : ℕ) (v : Fin (i + 1) → M) :
    ((koszulComplex.dAlternating φ' i) (f ∘ v) : ⋀[R]^i N) =
      exteriorPower.map i f ((koszulComplex.dAlternating φ i) v) := by
  calc
    _ = ∑ x : Fin (i + 1), (-1) ^ (x : ℕ) • φ' (f (v x)) •
          exteriorPower.ιMulti R i (x.removeNth (f ∘ v)) := by
      simp [koszulComplex.dAlternating, AlternatingMap.alternatizeUncurryFin_apply]
    _ = ∑ x : Fin (i + 1), (-1) ^ (x : ℕ) • φ (v x) •
          exteriorPower.ιMulti R i (f ∘ x.removeNth v) := by
      refine Finset.sum_congr rfl (fun x hx ↦ ?_)
      simp only [← h, LinearMap.coe_comp, Function.comp_apply]
      rfl
    _ = exteriorPower.map i f ((koszulComplex.dAlternating φ i) v) := by
      rw [koszulComplex.dAlternating, AlternatingMap.alternatizeUncurryFin_apply]
      simp [map_sum, map_smul, exteriorPower.map_apply_ιMulti]

lemma map_d_comm (f : M →ₗ[R] N) (φ' : N →ₗ[R] R) (h : φ' ∘ₗ f = φ) (i : ℕ) :
    ModuleCat.ofHom (exteriorPower.map (i + 1) f) ≫ ModuleCat.ofHom (koszulComplex.d φ' i) =
      ModuleCat.ofHom (koszulComplex.d φ i) ≫ ModuleCat.ofHom (exteriorPower.map i f) := by
  ext v
  simp [koszulComplex.d, map_dAlternating_apply (φ := φ) (f := f) (φ' := φ') h]

/-- The map between two Koszul complex when give a linear map between module that commute with
two defining linear maps. -/
@[stacks 0624 "only recording chain complex map"]
noncomputable def map (f : M →ₗ[R] N) (φ' : N →ₗ[R] R) (h : φ' ∘ₗ f = φ) :
    koszulComplex φ ⟶ koszulComplex φ' :=
  ChainComplex.ofHom
    (fun i ↦ ModuleCat.ofHom (exteriorPower.map i f))
    (fun i ↦ by simpa [d_eq_d] using! map_d_comm φ f φ' h i)

variable {L : Type v} [AddCommGroup L] [Module R L]

lemma map_comp (f : M →ₗ[R] N) (φ' : N →ₗ[R] R) (g : N →ₗ[R] L) (φ'' : L →ₗ[R] R)
    (h : φ' ∘ₗ f = φ) (h' : φ'' ∘ₗ g = φ') (h'' : φ'' ∘ₗ g ∘ₗ f = φ) :
    koszulComplex.map φ f φ' h ≫ koszulComplex.map φ' g φ'' h' =
      koszulComplex.map φ (g ∘ₗ f) φ'' h'' := by
  ext i x
  simp [map, X_eq_exteriorPower, exteriorPower.map_comp]

/-- The map between two Koszul complex when give an linear equiv between module that commute with
two defining linear maps. -/
@[stacks 0625]
noncomputable def isoOfEquiv (f : M ≃ₗ[R] N) (φ' : N →ₗ[R] R) (h : φ' ∘ₗ f = φ) :
    koszulComplex φ ≅ koszulComplex φ' where
  hom := koszulComplex.map φ f φ' h
  inv := koszulComplex.map φ' f.symm φ ((f.comp_toLinearMap_symm_eq φ' φ).mpr h.symm)
  hom_inv_id := by
    ext i x
    simp [map, X_eq_exteriorPower, ← exteriorPower.map_comp]
  inv_hom_id := by
    ext i x
    simp [map, X_eq_exteriorPower, ← exteriorPower.map_comp]

end functoriality

lemma isZero_X_of_card_generators_lt {ι : Type*} [Finite ι] [LinearOrder ι] (g : ι → M)
    (hg : Submodule.span R (Set.range g) = ⊤) (i : ℕ) (hi : Nat.card ι < i) :
    IsZero ((koszulComplex φ).X i) :=
  ModuleCat.isZero_of_iff_subsingleton.mpr
    (exteriorPower.subsingleton_of_span_eq_top_of_card_lt g hg i hi)

lemma isZero_X_ofList_of_length_lt (l : List R) (i : ℕ) (hi : l.length < i) :
    IsZero ((ofList l).X i) := isZero_X_of_card_generators_lt _
  (Pi.basisFun R (Fin l.length)) (Pi.basisFun R (Fin l.length)).span_eq i
  (by simpa [Nat.card_eq_fintype_card] using hi)

section basechange

open TensorProduct

universe w in
lemma exteriorPower.baseChangeIso_comm_aux (S : Type w) [CommRing S] [Algebra R S] (φ : M →ₗ[R] R)
    (i : ℕ) :
    (exteriorPower.baseChangeIso R M S i).toLinearMap.comp
      ((koszulComplex.d φ i).baseChange S) =
        (koszulComplex.d ((TensorProduct.AlgebraTensorModule.rid R S S).toLinearMap.comp
          (φ.baseChange S)) i).comp (exteriorPower.baseChangeIso R M S (i + 1)).toLinearMap := by
  ext m
  simp only [koszulComplex.d, AlgebraTensorModule.curry_apply, LinearMap.restrictScalars_comp,
    LinearMap.compAlternatingMap_apply, curry_apply, LinearMap.coe_comp,
    LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, Function.comp_apply,
    LinearMap.baseChange_tmul, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    exteriorPower.baseChangeIso_apply_tmul, SetLike.coe_eq_coe]
  trans ∑ j : Fin (i + 1), (((-1 : S) ^ (j : ℕ)) * algebraMap R S (φ (m j))) •
    exteriorPower.ιMulti S i ((TensorProduct.mk R S M 1) ∘ j.removeNth m)
  · rw [koszulComplex.dAlternating_apply, TensorProduct.tmul_sum, map_sum]
    congr
    funext j
    rw [tmul_smul, ← algebraMap_smul S, map_smul, map_mul, map_pow, map_neg, map_one,
      exteriorPower.baseChangeIso_apply_tmul]
  · rw [koszulComplex.dAlternating_apply]
    congr
    funext j
    simp only [Function.comp_apply, mk_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
      LinearMap.baseChange_tmul, AlgebraTensorModule.rid_tmul, Algebra.mul_smul_comm, mul_one]
    rw [mul_smul, ← smul_assoc, smul_eq_mul, mul_comm, ← Algebra.smul_def]
    congr

instance (T : Type v) [CommRing T] (g : R →+* T) :
    (ModuleCat.extendScalars.{u, v, u} g).Additive where
  map_add {X Y a b} := by
    simp only [ModuleCat.extendScalars, ModuleCat.ExtendScalars.map',
      ModuleCat.hom_add, LinearMap.baseChange_add]
    rfl

variable {S : Type (max u v)} [CommRing S] (f : R →+* S)

set_option backward.isDefEq.respectTransparency false in
/-- The base change isomorphism for Koszul complex. -/
noncomputable def baseChangeIso {M : Type u} [AddCommGroup M] [Module R M] (φ : M →ₗ[R] R) :
    letI := f.toAlgebra
    ((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex _).obj (koszulComplex φ) ≅
      koszulComplex ((TensorProduct.AlgebraTensorModule.rid R S S).toLinearMap.comp
        (φ.baseChange S)) :=
  let := f.toAlgebra
  HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ (exteriorPower.baseChangeIso R M S i).toModuleIso) (fun i j hij ↦ by
      simp only [ComplexShape.down_Rel] at hij
      subst hij
      simp only [koszulComplex, LinearEquiv.toModuleIso_hom, ChainComplex.of_d,
        Functor.mapHomologicalComplex_obj_d]
      exact congrArg ModuleCat.ofHom (exteriorPower.baseChangeIso_comm_aux S φ j).symm)

/-- The base change isomorphism for Koszul complex generated by a list of elements. -/
noncomputable def ofListBaseChangeIso (l : List R) (l' : List S) (eqmap : l.map f = l') :
    ((ModuleCat.extendScalars f).mapHomologicalComplex _).obj (ofList l) ≅ ofList l' :=
  let := f.toAlgebra
  let e : Fin l.length ≃ Fin l'.length := finCongr (by simp [← eqmap])
  (baseChangeIso f (Fintype.linearCombination R l.get)).trans
    (koszulComplex.isoOfEquiv _ ((TensorProduct.piScalarRight R S S (Fin l.length)).trans
      (LinearEquiv.funCongrLeft S S e.symm)) _ (by
        ext i
        have : (LinearMap.funLeft S S e.symm) (fun j ↦ f (Pi.single (M := fun _ ↦ R) i 1 j)) =
          Pi.single (e i) 1 := by
          ext j
          rcases eq_or_ne (e i) j with rfl|ne
          · simp
          · simp [e.symm_apply_eq.not.mpr ne.symm, ne]
        have eq : l'.get (e i) = f (l.get i) := by simp [← eqmap, e]
        simpa [-List.get_eq_getElem, ← Algebra.algebraMap_eq_smul_one, RingHom.algebraMap_toAlgebra,
          this] using eq))

end basechange

section induction

variable (φ : M →ₗ[R] R) (a : R)

/-- Abbreviation for `x ↦ φ x.1 + a • x.2`. -/
abbrev appendMap : M × R →ₗ[R] R := φ.comp (LinearMap.fst R M R) + a • (LinearMap.snd R M R)

variable (R M) in
/-- Abbreviation for equivalence between zero term of Koszul complex. -/
noncomputable abbrev XZeroEquiv : ⋀[R]^0 M ≃ₗ[R] ⋀[R]^0 (M × R):=
  (exteriorPower.zeroEquiv R _).trans (exteriorPower.zeroEquiv R _).symm

/-- Charatcerization of differential under `exteriorPowerProdEquivProd` at zero degree. -/
lemma appendMap_d_eq_zero :
    (koszulComplex.d (appendMap φ a) 0).comp (exteriorPowerProdEquivProd R M 0).toLinearMap =
      (XZeroEquiv R M).toLinearMap.comp ((koszulComplex.d φ 0).comp (LinearMap.fst R _ _) +
        a • (LinearMap.snd R _ _)) := by
  ext m
  · simp only [LinearMap.compAlternatingMap_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearEquiv.coe_coe, LinearMap.add_apply, LinearMap.coe_fst,
      LinearMap.smul_apply, LinearMap.coe_snd, smul_zero, add_zero, LinearMap.coe_inl]
    rw [exteriorPowerProdEquivProd_apply_inl_ιMulti]
    simp [koszulComplex.d, koszulComplex.dAlternating_apply, XZeroEquiv, appendMap,
      exteriorPower.zeroEquiv_symm_apply]
  · have hE : (exteriorPowerProdEquivProd R M 0) (0, exteriorPower.ιMulti R 0 m) =
        exteriorPower.ιMulti R 1 (fun _ => ((0, 1) : M × R)) := by
      apply Subtype.ext
      simp [exteriorPowerProdEquivProd_apply_inr_ιMulti]
    simp [hE, koszulComplex.d, koszulComplex.dAlternating_apply, XZeroEquiv, appendMap,
      exteriorPower.zeroEquiv_symm_apply]

variable (n : ℕ)

private lemma removeNth_castSucc_snoc {α : Type*} {k : ℕ} (u : Fin (k + 1) → α) (z : α)
    (j : Fin (k + 1)) :
    (Fin.castSucc j).removeNth (Fin.snoc u z : Fin (k + 2) → α) =
      Fin.snoc (j.removeNth u) z := by
  ext l
  induction l using Fin.lastCases with
  | last =>
    rw [Fin.removeNth_apply, Fin.succAbove_castSucc_of_le j (Fin.last k) j.le_last,
      Fin.succ_last, Fin.snoc_last, Fin.snoc_last]
  | cast l =>
    rw [Fin.removeNth_apply, Fin.castSucc_succAbove_castSucc, Fin.snoc_castSucc,
      Fin.snoc_castSucc, Fin.removeNth_apply]

lemma exteriorPowerProdEquivProd_apply_inr_eq_snoc (k : ℕ) (v : Fin k → M) :
    (exteriorPowerProdEquivProd R M k) (0, exteriorPower.ιMulti R k v) =
      exteriorPower.ιMulti R (k + 1) (Fin.snoc ((LinearMap.inl R M R) ∘ v) (0, 1)) := by
  apply Subtype.ext
  have : ExteriorAlgebra.ι R ((0, 1) : M × R) =
    ExteriorAlgebra.ιMulti R 1 ![((0, 1) : M × R)] := by simp
  rw [exteriorPowerProdEquivProd_apply_inr_ιMulti, exteriorPower.ιMulti_apply_coe, this,
    ExteriorAlgebra.ιMulti_mul_ιMulti, Fin.append_right_eq_snoc]
  simp

/-- Charatcerization of differential under `exteriorPowerProdEquivProd` at positive degree. -/
lemma appendMap_d_eq_pos (n : ℕ) :
    (koszulComplex.d (appendMap φ a) (n + 1)).comp
      (exteriorPowerProdEquivProd R M (n + 1)).toLinearMap =
        (exteriorPowerProdEquivProd R M n).toLinearMap.comp
          ((LinearMap.inl R _ _).comp ((koszulComplex.d φ (n + 1)).comp (LinearMap.fst R _ _)) +
            (LinearMap.inr R _ _).comp ((koszulComplex.d φ n).comp (LinearMap.snd R _ _)) +
              (-1 : ℤ) ^ (n + 1) • a • (LinearMap.inl R _ _).comp (LinearMap.snd R _ _)) := by
  have h : (appendMap φ a) ∘ₗ (LinearMap.inl R M R) = φ := by ext x; simp
  ext m
  · have hrm2 (j : Fin (n + 1 + 1)) : j.removeNth (⇑(LinearMap.inl R M R) ∘ m) =
      (LinearMap.inl R M R) ∘ j.removeNth m := rfl
    have hinl (x : ⋀[R]^(n + 1) M) : (exteriorPowerProdEquivProd R M n) (x, 0) =
      ((exteriorPowerProdEquivProd R M n).toLinearMap ∘ₗ LinearMap.inl R _ _) x := rfl
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearEquiv.coe_coe, LinearMap.add_apply, LinearMap.coe_fst, LinearMap.coe_inl,
      LinearMap.smul_apply, LinearMap.coe_snd, smul_zero, add_zero, map_zero, Prod.mk_zero_zero]
    rw [exteriorPowerProdEquivProd_apply_inl_ιMulti]
    simp only [koszulComplex.d, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
      koszulComplex.dAlternating_apply]
    simp only [hrm2, ← exteriorPowerProdEquivProd_apply_inl_ιMulti, hinl, map_sum, map_smul]
    simp [appendMap]
  · have hrm (j : Fin (n + 1)) : j.removeNth (⇑(LinearMap.inl R M R) ∘ m) =
      (LinearMap.inl R M R) ∘ j.removeNth m := rfl
    have hinr (x : ⋀[R]^n M) : (exteriorPowerProdEquivProd R M n) (0, x) =
      ((exteriorPowerProdEquivProd R M n).toLinearMap ∘ₗ LinearMap.inr R _ _) x := rfl
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearEquiv.coe_coe, LinearMap.add_apply, LinearMap.coe_fst, LinearMap.coe_inr, zero_add,
      LinearMap.smul_apply, LinearMap.coe_snd, map_zero, LinearMap.coe_inl, Prod.mk_zero_zero]
    rw [exteriorPowerProdEquivProd_apply_inr_eq_snoc]
    simp only [koszulComplex.d, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
      koszulComplex.dAlternating_apply, Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc,  Fin.val_castSucc, Fin.snoc_last, Fin.val_last,
      Fin.removeNth_last, Fin.init_snoc, removeNth_castSucc_snoc, hrm]
    rw [← exteriorPowerProdEquivProd_apply_inl_ιMulti]
    simp only [← exteriorPowerProdEquivProd_apply_inr_eq_snoc, hinr, map_sum, map_smul,
      map_add, map_zsmul]
    simp [appendMap, ← Int.cast_smul_eq_zsmul R ((-1) ^ (n + 1)), smul_smul]

/-- The zero hom of `koszulComplex.toAppendMap`. -/
noncomputable abbrev fromOfListHomZero :
    (koszulComplex φ).X 0 ⟶ (koszulComplex (appendMap φ a)).X 0 :=
  ModuleCat.ofHom (XZeroEquiv R M).toLinearMap

/-- The `i + 1`-th hom of `koszulComplex.toAppendMap`. -/
noncomputable abbrev fromOfListHomSucc (i : ℕ) :
    (koszulComplex φ).X (i + 1) ⟶ (koszulComplex (appendMap φ a)).X (i + 1) :=
  ModuleCat.ofHom ((exteriorPowerProdEquivProd R M i).toLinearMap.comp (LinearMap.inl R _ _))

lemma from_ofList_hom_comm_zero :
    fromOfListHomSucc φ a 0 ≫ (koszulComplex (appendMap φ a)).d (0 + 1) 0 =
      (koszulComplex φ).d (0 + 1) 0 ≫ fromOfListHomZero φ a := by
  ext y
  have h := LinearMap.congr_fun (appendMap_d_eq_zero φ a) (y, 0)
  simpa [d_eq_d, fromOfListHomSucc, fromOfListHomZero] using! h

lemma from_ofList_hom_comm_pos (i : ℕ) :
    fromOfListHomSucc φ a (i + 1) ≫ (koszulComplex (appendMap φ a)).d (i + 1 + 1) (i + 1) =
      (koszulComplex φ).d (i + 1 + 1) (i + 1) ≫ fromOfListHomSucc φ a i := by
  ext y
  have h := LinearMap.congr_fun (appendMap_d_eq_pos φ a i) (y, 0)
  simpa [d_eq_d, fromOfListHomSucc] using! h

/-- The homomorphism given by inclusion to the first component
using `exteriorPowerProdEquivProd`. -/
noncomputable def toAppendMap : koszulComplex φ ⟶ koszulComplex (appendMap φ a) :=
  ChainComplex.ofHom
    (fun i ↦
      match i with
      | 0 => fromOfListHomZero φ a
      | i + 1 => fromOfListHomSucc φ a i)
    (fun i ↦
      match i with
      | 0 => from_ofList_hom_comm_zero φ a
      | i + 1 => from_ofList_hom_comm_pos φ a i)

/-- Augumentation of Koszul complex by zero object. -/
noncomputable abbrev upOne : HomologicalComplex (ModuleCat R) PalomarBarycentricTor.naturalDown :=
  ChainComplex.augment (show ChainComplex (ModuleCat R) ℕ from koszulComplex φ) (X := ModuleCat.of R PUnit) 0 (by simp)

/-- The canonical isomorphism of homology for augumenting with zero object. -/
noncomputable def upOneHomologyIso (i : ℕ) :
    (upOne φ).homology (i + 1) ≅ (koszulComplex φ).homology i :=
  match i with
  | 0 =>
    ((upOne φ).isoHomologyι 1 0 (by simp) (ChainComplex.augment_d_one_zero _ _ _)) ≪≫
      ((upOne φ).opcyclesIsoSc' 2 1 0 (by simp) (by simp)) ≪≫
        (ShortComplex.opcyclesIsoCokernel (S := (upOne φ).sc' 2 1 0)) ≪≫
          (ShortComplex.opcyclesIsoCokernel (S := (koszulComplex φ).sc' 1 0 0)).symm ≪≫
            ((koszulComplex φ).opcyclesIsoSc' 1 0 0 (by simp) (by simp)).symm ≪≫
              (ChainComplex.isoHomologyι₀ (show ChainComplex (ModuleCat R) ℕ from koszulComplex φ)).symm
  | n + 1 =>
    ((upOne φ).homologyIsoSc' (n + 3) (n + 2) (n + 1) (by simp) (by simp)) ≪≫
      ((koszulComplex φ).homologyIsoSc' (n + 2) (n + 1) n (by simp) (by simp)).symm

/-- Auxiliary definition for `toUpOne` -/
noncomputable abbrev toUpOneHom (i : ℕ) :
    (koszulComplex (appendMap φ a)).X (i + 1) ⟶ (upOne φ).X (i + 1) :=
  ModuleCat.ofHom ((LinearMap.snd R _ _).comp (exteriorPowerProdEquivProd R M i).symm.toLinearMap)

set_option backward.isDefEq.respectTransparency false in
lemma to_self_hom_comm (i : ℕ) :
    toUpOneHom φ a (i + 1) ≫ (koszulComplex φ).d (i + 1) i =
      (koszulComplex (appendMap φ a)).d (i + 1 + 1) (i + 1) ≫ toUpOneHom φ a i := by
  rw [d_eq_d, d_eq_d]
  ext y
  have h := LinearMap.congr_fun (appendMap_d_eq_pos φ a i)
    ((exteriorPowerProdEquivProd R M (i + 1)).symm y)
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply] at h
  change koszulComplex.d φ i ((LinearMap.snd R _ _)
      ((exteriorPowerProdEquivProd R M (i + 1)).symm y)) =
    (LinearMap.snd R _ _) ((exteriorPowerProdEquivProd R M i).symm
      (koszulComplex.d (appendMap φ a) (i + 1) y))
  rw [h, LinearEquiv.symm_apply_apply]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The homomorphism given by projection to the second component
using `exteriorPowerProdEquivProd`. -/
noncomputable def toUpOne : koszulComplex (appendMap φ a) ⟶ upOne φ :=
  ChainComplex.ofHom
    (fun i ↦
      match i with
      | 0 => 0
      | i + 1 => toUpOneHom φ a i)
    (fun i ↦
      match i with
      | 0 => by simp
      | i + 1 => to_self_hom_comm φ a i)

lemma toAppendMap_comp_toUpOne_eq_zero : toAppendMap φ a ≫ toUpOne φ a = 0 := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  rcases n with _ | n
  · simp only [ChainComplex.augment_X_zero, toAppendMap, toUpOne, HomologicalComplex.comp_f,
      HomologicalComplex.zero_f]
    exact comp_zero
  · ext y
    change (LinearMap.snd R _ _) ((exteriorPowerProdEquivProd R M n).symm
      ((exteriorPowerProdEquivProd R M n) ((LinearMap.inl R _ _) y))) = 0
    simp [LinearEquiv.symm_apply_apply]

/-- The short complex given by `toAppendMap` and `toUpOne` -/
noncomputable def shortComplexProd : ShortComplex (HomologicalComplex (ModuleCat R) PalomarBarycentricTor.naturalDown) where
  f := toAppendMap φ a
  g := toUpOne φ a
  zero := toAppendMap_comp_toUpOne_eq_zero φ a

lemma shortComplexProd_shortExact : (shortComplexProd φ a).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  rcases n with _ | n
  · apply ShortComplex.ShortExact.mk' _
      ((ModuleCat.mono_iff_injective _).mpr (XZeroEquiv R M).injective)
      ((ModuleCat.epi_iff_surjective _).mpr fun x ↦ ⟨0, rfl⟩)
    rw [ShortComplex.moduleCat_exact_iff]
    intro x₂ _
    exact ⟨(XZeroEquiv R M).symm x₂, (XZeroEquiv R M).apply_symm_apply x₂⟩
  · let e := exteriorPowerProdEquivProd R M n
    apply ShortComplex.ShortExact.mk' _
      ((ModuleCat.mono_iff_injective _).mpr (e.injective.comp (Prod.mk_left_injective 0)))
      ((ModuleCat.epi_iff_surjective _).mpr (Prod.snd_surjective.comp e.symm.surjective))
    rw [ShortComplex.moduleCat_exact_iff]
    intro x₂ hx₂
    have : e.symm x₂ = ((e.symm x₂).1, 0) := Prod.ext_iff.mpr ⟨rfl, hx₂⟩
    exact ⟨(e.symm x₂).1, e.eq_symm_apply.mp this.symm⟩

set_option backward.isDefEq.respectTransparency false in
/-- Characterization of connecting `δ` of `koszulComplex.shortComplexProd`. -/
lemma shortComplexProd_δ_eq (i : ℕ) :
    (shortComplexProd_shortExact φ a).δ (i + 1) i rfl =
      ((-1 : R) ^ i * a) • (upOneHomologyIso φ i).hom := by
  have hx₃ := (upOne φ).iCycles_d (i + 1) i
  let compinr := (exteriorPowerProdEquivProd R M i).toLinearMap ∘ₗ LinearMap.inr R _ _
  have hx₂ : ((upOne φ).iCycles (i + 1) ≫ ModuleCat.ofHom compinr) ≫
      (shortComplexProd φ a).g.f (i + 1) = (upOne φ).iCycles (i + 1) := by
    refine ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
    change (LinearMap.snd R _ _) ((exteriorPowerProdEquivProd R M i).symm
      ((exteriorPowerProdEquivProd R M i) (0, ((upOne φ).iCycles (i + 1)).hom z))) =
      ((upOne φ).iCycles (i + 1)).hom z
    simp [LinearEquiv.symm_apply_apply]
  have hk : (ComplexShape.down ℕ).next i = i - 1 := by rcases i with _ | n <;> simp
  have hd : ((upOne φ).iCycles (i + 1)) ≫ (koszulComplex φ).d i (i - 1) = 0 := by
    rcases i with _ | n
    · rw [(koszulComplex φ).shape 0 0 (by simp), comp_zero]
    · exact hx₃
  have hx₁ : (((-1 : R) ^ i * a) • ((upOne φ).iCycles (i + 1))) ≫ (shortComplexProd φ a).f.f i =
    ((upOne φ).iCycles (i + 1) ≫ ModuleCat.ofHom compinr) ≫
      (koszulComplex (appendMap φ a)).d (i + 1) i := by
    rw [d_eq_d]
    rcases i with _ | n
    · ext z
      have h := LinearMap.congr_fun (appendMap_d_eq_zero φ a) (0, ((upOne φ).iCycles 1).hom z)
      simpa using! h.symm
    · ext z
      have hcyc : koszulComplex.d φ n (((upOne φ).iCycles (n + 2)).hom z) = 0 := by
        simpa [d_eq_d] using! congrArg (fun F => ModuleCat.Hom.hom F z) hx₃
      have h := LinearMap.congr_fun (appendMap_d_eq_pos φ a n)
        (0, ((upOne φ).iCycles (n + 2)).hom z)
      have hsc : ((-1 : ℤ) ^ (n + 1)) • a • (((upOne φ).iCycles (n + 2)).hom z, 0) =
          ((((-1 : R) ^ (n + 1) * a) • ((upOne φ).iCycles (n + 2)).hom z), (0 : ⋀[R]^n M)) := by
        simp [← Int.cast_smul_eq_zsmul R, smul_smul]
      simpa only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
        LinearMap.add_apply, LinearMap.coe_fst, LinearMap.coe_snd, LinearMap.smul_apply,
        LinearMap.inl_apply, map_zero, zero_add, hcyc, hsc] using! h.symm
  have hδ := (shortComplexProd_shortExact φ a).δ_eq (i + 1) i rfl
    ((upOne φ).iCycles (i + 1)) hx₃ ((upOne φ).iCycles (i + 1) ≫ ModuleCat.ofHom compinr) hx₂
    (((-1 : R) ^ i * a) • (upOne φ).iCycles (i + 1)) hx₁ (i - 1) hk
  have hδ' : (upOne φ).liftCycles ((upOne φ).iCycles (i + 1)) i (by simp) hx₃ ≫
    (upOne φ).homologyπ (i + 1) ≫ (shortComplexProd_shortExact φ a).δ (i + 1) i rfl =
      (((-1 : R) ^ i * a) • (koszulComplex φ).liftCycles ((upOne φ).iCycles (i + 1)) (i - 1)
        hk hd) ≫ (koszulComplex φ).homologyπ i := by
    apply hδ.trans
    congr 1
    simp [← cancel_mono ((koszulComplex φ).iCycles i), shortComplexProd]
  have hlift : (upOne φ).liftCycles ((upOne φ).iCycles (i + 1)) i (by simp) hx₃ = 𝟙 _ := by
    simp [← cancel_mono ((upOne φ).iCycles (i + 1))]
  rw [hlift, Category.id_comp, Linear.smul_comp] at hδ'
  have hmain : (koszulComplex φ).liftCycles ((upOne φ).iCycles (i + 1)) (i - 1) hk hd ≫
    (koszulComplex φ).homologyπ i = (upOne φ).homologyπ (i + 1) ≫ (upOneHomologyIso φ i).hom := by
    rcases i with _ | n
    · rw [← cancel_mono ((ChainComplex.isoHomologyι₀ (koszulComplex φ)).hom)]
      trans ((upOne φ).iCycles 1) ≫ (koszulComplex φ).pOpcycles 0
      · rw [Category.assoc, HomologicalComplex.isoHomologyι_hom, HomologicalComplex.homology_π_ι,
          ← Category.assoc, HomologicalComplex.liftCycles_i]
      · have : HomologicalComplex.pOpcycles (koszulComplex φ) 0 =
          cokernel.π ((upOne φ).sc' 2 1 0).f ≫ cokernel.desc ((koszulComplex φ).sc' 1 0 0).f
            ((koszulComplex φ).sc' 1 0 0).pOpcycles (ShortComplex.f_pOpcycles _) ≫
              ((koszulComplex φ).opcyclesIsoSc' 1 0 0 (by simp) (by simp)).inv := by
          simp only [ChainComplex.prev, zero_add, ChainComplex.next_nat_zero,
            ← HomologicalComplex.pOpcycles_opcyclesIsoSc'_inv, ← assoc, Iso.cancel_iso_inv_right]
          exact (CategoryTheory.Limits.cokernel.π_desc _ _ _).symm
        simp [upOneHomologyIso, this]
    · have e3 : (koszulComplex φ).liftCycles ((upOne φ).iCycles (n + 2)) (n + 1 - 1) hk hd =
        ((upOne φ).cyclesIsoSc' (n + 3) (n + 2) (n + 1) (by simp) (by simp)).hom ≫
          ((koszulComplex φ).cyclesIsoSc' (n + 2) (n + 1) n (by simp) (by simp)).inv := by
        rw [← cancel_mono ((koszulComplex φ).iCycles (n + 1)),
          HomologicalComplex.liftCycles_i, Category.assoc,
          ← (upOne φ).cyclesIsoSc'_hom_iCycles (n + 3) (n + 2) (n + 1) (by simp) (by simp),
          (koszulComplex φ).cyclesIsoSc'_inv_iCycles (n + 2) (n + 1) n (by simp) (by simp)]
        rfl
      simp only [e3, assoc, upOneHomologyIso, Iso.trans_hom, Iso.symm_hom,
        HomologicalComplex.π_homologyIsoSc'_hom_assoc, Iso.cancel_iso_hom_left]
      exact ((koszulComplex φ).π_homologyIsoSc'_inv (n + 2) (n + 1) n (by simp) (by simp)).symm
  rw [← cancel_epi ((upOne φ).homologyπ (i + 1)), hδ', Linear.comp_smul, ← hmain]

end induction

section H0

variable (φ : M →ₗ[R] R)

/-- The equivalence between zeroth homology and cokernel of the differential. -/
noncomputable def zeroHomologyLinearEquivAux : (koszulComplex φ).homology 0 ≃ₗ[R]
    (⋀[R]^0 M) ⧸ (koszulComplex.d φ 0).range :=
  (((ChainComplex.isoHomologyι₀ (koszulComplex φ)).trans
    ((koszulComplex φ).opcyclesIsoSc' 1 0 0 (by simp) (by simp))).trans
      ((koszulComplex φ).sc' 1 0 0).moduleCatOpcyclesIso).toLinearEquiv

lemma equiv_comp_koszulComplex.d_zero_eq :
    (exteriorPower.zeroEquiv R M).toLinearMap.comp (koszulComplex.d φ 0) =
      φ.comp (exteriorPower.oneEquiv R M).toLinearMap := by
  ext m
  simp [koszulComplex.d, koszulComplex.dAlternating_apply]

lemma d_zero_range_map :
    (koszulComplex.d φ 0).range.map (exteriorPower.zeroEquiv R _).toLinearMap = φ.range := by
  rw [← LinearMap.range_comp, equiv_comp_koszulComplex.d_zero_eq]
  simp

/-- Zeroth homology of Koszul complex generated by a list of elements is isomorphic to
the ring quotient by these elements. -/
noncomputable def zeroHomologyOfListLinearEquiv (l : List R) :
    (ofList l).homology 0 ≃ₗ[R] R ⧸ Ideal.ofList l :=
  (zeroHomologyLinearEquivAux _).trans (Submodule.Quotient.equiv _ _ (exteriorPower.zeroEquiv R _)
    (by simp [koszulComplex.d_zero_range_map]))

end H0

section regular

open RingTheory.Sequence

variable (R) in
/-- Splitting off the last coordinate of a tuple as a linear equivalence. -/
def snocLinearEquiv (n : ℕ) : (Fin (n + 1) → R) ≃ₗ[R] (Fin n → R) × R where
  toFun f := (Fin.init f, f (Fin.last n))
  map_add' f g := rfl
  map_smul' c f := rfl
  invFun p := Fin.snoc p.1 p.2
  left_inv f := Fin.snoc_init_self f
  right_inv p := Prod.ext (by simp) (by simp)

/-- Isomorphism on module level for `ofListIsoOfEq` -/
def ofListIsoOfEqAux {rs' rs : List R} {a : R} (eq : rs = rs' ++ [a]) :
    (Fin rs.length → R) ≃ₗ[R] (Fin rs'.length → R) × R :=
  (LinearEquiv.funCongrLeft R R (finCongr (by simp [eq]))).trans (snocLinearEquiv R rs'.length)

lemma ofListIsoOfEqAux_comp {rs' rs : List R} {a : R} (eq : rs = rs' ++ [a]) :
    (appendMap (Fintype.linearCombination R rs'.get) a).comp (ofListIsoOfEqAux eq).toLinearMap =
      Fintype.linearCombination R rs.get := by
  subst eq
  have h : rs'.length + 1 = (rs' ++ [a]).length := by simp
  apply LinearMap.ext
  intro f
  have : Fintype.linearCombination R rs'.get (Fin.init (f ∘ finCongr h)) +
    a • (f ∘ finCongr h) (Fin.last rs'.length) =
      (Fintype.linearCombination R (rs' ++ [a]).get) f := by
    rw [Fintype.linearCombination_apply, Fintype.linearCombination_apply,
      ← (finCongr h).sum_comp, Fin.sum_univ_castSucc]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      simp [List.getElem_append_left, i.isLt]
    · simp [mul_comm, Fin.last]
  simpa [ofListIsoOfEqAux, appendMap]

/-- Given `rs = rs' ++ [a]`, the Koszul complex generated by `rs` is isomorphic to the one
defined by `appendMap (Fintype.linearCombination R rs'.get) a` via `ofListIsoOfEqAux`. -/
noncomputable def ofListIsoOfEq {rs' rs : List R} {a : R} (eq : rs = rs' ++ [a]) : ofList rs ≅
    koszulComplex (appendMap (Fintype.linearCombination R rs'.get) a) :=
  isoOfEquiv _ (ofListIsoOfEqAux eq) _ (ofListIsoOfEqAux_comp eq)

set_option backward.isDefEq.respectTransparency false in
lemma exactAt_of_isRegular (rs : List R) (reg : IsRegular R rs)
    (i : ℕ) (ne : i ≠ 0) : (ofList rs).ExactAt i := by
  generalize h : rs.length = n
  induction n generalizing rs i with
  | zero =>
    apply ShortComplex.exact_of_isZero_X₂
    exact isZero_X_ofList_of_length_lt rs i (by simpa [h, ← Nat.ne_zero_iff_zero_lt])
  | succ n ih =>
    have nenil : rs ≠ [] := List.ne_nil_of_length_eq_add_one h
    let rs' := rs.dropLast
    let a := rs.getLast nenil
    have eq : rs = rs' ++ [a] := (List.dropLast_concat_getLast nenil).symm
    have hw : IsWeaklyRegular R (rs' ++ [a]) := by simpa [eq] using reg.toIsWeaklyRegular
    have reg' : IsRegular R rs' := by
      refine ⟨((isWeaklyRegular_append_iff R _ _).mp hw).1, Ne.symm ?_⟩
      apply ne_top_of_le_ne_top reg.top_ne_smul.symm
      exact Submodule.smul_mono_left (Ideal.span_mono fun x hx => List.dropLast_subset rs hx)
    have areg : IsSMulRegular (R ⧸ Ideal.ofList rs') a := by
      have := (isWeaklyRegular_singleton_iff _ a).mp ((isWeaklyRegular_append_iff R _ _).mp hw).2
      exact ((Submodule.quotEquivOfEq _ _ (by simp)).isSMulRegular_congr a).mp this
    apply HomologicalComplex.ExactAt.of_iso _ (ofListIsoOfEq eq).symm
    set φ := Fintype.linearCombination R rs'.get
    have ih' (i : ℕ) (ne : i ≠ 0) : IsZero ((koszulComplex φ).homology i) :=
      ((koszulComplex φ).exactAt_iff_isZero_homology i).mp (ih rs' reg' i ne (by simp [rs', h]))
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    apply ((shortComplexProd_shortExact φ a).homology_exact₂ i).isZero_X₂
      ((ih' i ne).eq_zero_of_src _)
    rcases Nat.exists_eq_succ_of_ne_zero ne with ⟨j, rfl⟩
    rcases eq_or_ne j 0 with rfl|ne0
    · simp only [Nat.succ_eq_add_one]
      rw [← ((shortComplexProd_shortExact φ a).homology_exact₃ (0 + 1) 0 rfl).mono_g_iff]
      simp only [ModuleCat.mono_iff_injective, shortComplexProd_δ_eq]
      simp only [Nat.reduceAdd, pow_zero, one_mul, ← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro x hx
      apply (upOneHomologyIso φ 0).toLinearEquiv.map_eq_zero_iff.mp
      exact (((zeroHomologyOfListLinearEquiv rs').isSMulRegular_congr a).mpr
        areg).right_eq_zero_of_smul hx
    · exact ((upOneHomologyIso φ j).isZero_iff.mpr (ih' j ne0)).eq_zero_of_tgt _

end regular

end koszulComplex

end
end CheckedSource2

/-! ## Source: CommAlg.KoszulComplex.Variables -/
section CheckedSource3

/-! # Polynomial variables form a regular sequence

This proof uses actual polynomial coefficients and ideal quotients. Multiplication by a variable
outside a set of variables is injective modulo the ideal generated by that set.
-/

noncomputable section

namespace CommAlg.Koszul

open MvPolynomial RingTheory.Sequence

variable {V k : Type*} [CommRing k]

lemma ofList_map_X (l : List V) :
    Ideal.ofList (l.map (X : V → MvPolynomial V k)) =
      Ideal.span ((X : V → MvPolynomial V k) '' {j | j ∈ l}) := by
  apply congrArg Ideal.span
  ext f
  simp only [Set.mem_ofPred_eq, List.mem_map, Set.mem_image]

lemma variable_regular_mod_variables (s : Set V) (j : V) (hj : j ∉ s) :
    IsSMulRegular (MvPolynomial V k ⧸
      Ideal.span ((X : V → MvPolynomial V k) '' s)) (X j : MvPolynomial V k) := by
  classical
  rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
  intro f hf
  rw [smul_eq_mul, MvPolynomial.mem_ideal_span_X_image] at hf
  rw [MvPolynomial.mem_ideal_span_X_image]
  intro a ha
  have hm : Finsupp.single j 1 + a ∈ (X j * f).support := by
    simpa only [MvPolynomial.mem_support_iff, MvPolynomial.coeff_X_mul] using ha
  obtain ⟨i, hi, hai⟩ := hf _ hm
  refine ⟨i, hi, ?_⟩
  have hij : j ≠ i := by rintro rfl; exact hj hi
  simpa [Finsupp.single_apply, hij] using hai

lemma variable_ideal_ne_top [Nontrivial k] (s : Set V) :
    Ideal.span ((X : V → MvPolynomial V k) '' s) ≠ ⊤ := by
  rw [Ideal.ne_top_iff_one]
  rw [MvPolynomial.mem_ideal_span_X_image]
  push Not
  refine ⟨0, ?_, ?_⟩
  · simp
  · simp

lemma variables_weaklyRegular (l : List V) (hl : l.Nodup) :
    IsWeaklyRegular (MvPolynomial V k) (l.map (X : V → MvPolynomial V k)) := by
  classical
  constructor
  intro i hi
  have hi' : i < l.length := by simpa using hi
  have hnot : l[i] ∉ l.take i := by
    intro hmem
    obtain ⟨j, hj, heq⟩ := List.getElem_of_mem hmem
    have hji : j < i := lt_of_lt_of_le hj (List.length_take_le i l)
    have hjl : j < l.length := lt_trans hji hi'
    have heq' : l[j] = l[i] := by simpa using heq
    have hji' := hl.getElem_inj_iff.mp heq'
    omega
  have heq : (Ideal.ofList (List.take i (l.map (X : V → MvPolynomial V k))) •
      (⊤ : Submodule (MvPolynomial V k) (MvPolynomial V k))) =
      Ideal.span ((X : V → MvPolynomial V k) '' {j | j ∈ l.take i}) := by
    change Ideal.ofList (List.take i (l.map X)) * ⊤ = _
    rw [Ideal.mul_top, ← List.map_take, ofList_map_X]
  apply ((Submodule.quotEquivOfEq _ _ heq).isSMulRegular_congr _).mpr
  simpa using variable_regular_mod_variables (k := k) {j | j ∈ l.take i} l[i] hnot

lemma variables_regular [Nontrivial k] (l : List V) (hl : l.Nodup) :
    IsRegular (MvPolynomial V k) (l.map (X : V → MvPolynomial V k)) := by
  refine ⟨variables_weaklyRegular l hl, ?_⟩
  simpa [ofList_map_X, eq_comm] using
    variable_ideal_ne_top (k := k) {j | j ∈ l}

lemma fin_variables_regular [Nontrivial k] (n : ℕ) :
    IsRegular (MvPolynomial (Fin n) k)
      (List.ofFn (X : Fin n → MvPolynomial (Fin n) k)) := by
  simpa only [List.map_ofFn, Function.comp_def] using
    variables_regular (k := k) (List.ofFn (fun i : Fin n => i)) (List.nodup_ofFn.mpr Function.injective_id)

end CommAlg.Koszul

end
end CheckedSource3

/-! ## Source: CommAlg.KoszulComplex.Resolution -/
section CheckedSource4

/-! # Genuine projective resolutions and derived Tor from Koszul complexes -/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CommAlg.Koszul

universe u
variable {R : Type u} [CommRing R]

/-- An exact positive-degree complex of projectives resolves its zeroth cokernel. -/
def resolutionOpcycles (K : HomologicalComplex (ModuleCat.{u} R) PalomarBarycentricTor.naturalDown)
    (hproj : ∀ n, Projective (K.X n)) (hexact : ∀ n, K.ExactAt (n + 1)) :
    ProjectiveResolution (K.opcycles 0) where
  complex := K
  projective := hproj
  π := (ChainComplex.toSingle₀Equiv K _).symm ⟨K.pOpcycles 0, K.d_pOpcycles 1 0⟩
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · dsimp
        simp only [ChainComplex.toSingle₀Equiv_symm_apply_f_zero]
        refine ⟨?_, inferInstance⟩
        exact ShortComplex.exact_of_g_is_cokernel _ (K.opcyclesIsCokernel 1 0 (by simp))
      · exact K.shape 0 0 (by simp)
      all_goals rfl
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · exact hexact n
      · exact ChainComplex.exactAt_succ_single_obj _ _⟩

/-- Change the resolved object along an actual isomorphism. -/
def transportResolution {X Y : ModuleCat.{u} R} (P : ProjectiveResolution X)
    (e : X ≅ Y) : ProjectiveResolution Y where
  complex := P.complex
  projective := P.projective
  π := P.π ≫ (ChainComplex.single₀ _).map e.hom

/-- The Koszul complex of a regular sequence is a projective resolution of its quotient ring. -/
def regularSequenceResolution (l : List R) (hl : RingTheory.Sequence.IsRegular R l) :
    ProjectiveResolution (ModuleCat.of R (R ⧸ Ideal.ofList l)) :=
  transportResolution
    (resolutionOpcycles (koszulComplex.ofList l)
      (fun n => by
        change Projective (ModuleCat.of R (⋀[R]^n (Fin l.length → R)))
        infer_instance)
      (fun n => koszulComplex.exactAt_of_isRegular l hl (n + 1) (by omega)))
    ((ChainComplex.isoHomologyι₀ (koszulComplex.ofList l)).symm ≪≫
      (koszulComplex.zeroHomologyOfListLinearEquiv l).toModuleIso)

@[simp] theorem regularSequenceResolution_complex (l : List R)
    (hl : RingTheory.Sequence.IsRegular R l) :
    (regularSequenceResolution l hl).complex = koszulComplex.ofList l := rfl

/-- Tensor a Koszul complex with a genuine module. -/
def coefficientComplex (l : List R) (M : ModuleCat.{u} R) :
    HomologicalComplex (ModuleCat.{u} R) PalomarBarycentricTor.naturalDown :=
  (((CategoryTheory.MonoidalCategory.tensoringRight (ModuleCat R)).obj M).mapHomologicalComplex (ComplexShape.down ℕ)).obj (koszulComplex.ofList l)

/-- The first-factor derived tensor functor (Mathlib's `Tor'`) is computed by this Koszul complex.
No balance or symmetry theorem is assumed: the quotient is resolved in the first factor. -/
def torIsoKoszulHomology (l : List R) (hl : RingTheory.Sequence.IsRegular R l)
    (M : ModuleCat.{u} R) (i : ℕ) :
    ((CategoryTheory.Tor' (ModuleCat R) i).obj
      (ModuleCat.of R (R ⧸ Ideal.ofList l))).obj M ≅
      (coefficientComplex l M).homology i :=
  (regularSequenceResolution l hl).isoLeftDerivedObj
    ((CategoryTheory.MonoidalCategory.tensoringRight (ModuleCat R)).obj M) i

end CommAlg.Koszul

end
end CheckedSource4

/-! ## Source: CommAlg.KoszulComplex.Polynomial -/
section CheckedSource5

/-! # The polynomial Koszul resolution and the actual coefficient field -/

noncomputable section

namespace CommAlg.Koszul

open CategoryTheory MvPolynomial

universe u v
variable {V : Type} {k : Type u} [CommRing k]

lemma ker_constantCoeff :
    RingHom.ker (constantCoeff : MvPolynomial V k →+* k) = idealOfVars V k := by
  classical
  ext f
  rw [RingHom.mem_ker, constantCoeff_eq]
  change f.coeff 0 = 0 ↔ f ∈ Ideal.span (Set.range (X : V → MvPolynomial V k))
  rw [← Set.image_univ, mem_ideal_span_X_image]
  constructor
  · intro hf a ha
    have ha0 : a ≠ 0 := by
      intro h
      subst a
      exact (MvPolynomial.mem_support_iff.mp ha) hf
    obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
      by_contra h
      push Not at h
      exact ha0 (Finsupp.ext h)
    exact ⟨i, Set.mem_univ i, hi⟩
  · intro hf
    by_contra h
    obtain ⟨i, _, hi⟩ := hf 0 (MvPolynomial.mem_support_iff.mpr h)
    exact hi rfl

/-- Quotienting the polynomial ring by all variables really recovers its coefficient ring. -/
def residueRingEquiv :
    (MvPolynomial V k ⧸ idealOfVars V k) ≃+* k :=
  (Ideal.quotEquivOfEq ker_constantCoeff.symm).trans
    ((constantCoeff : MvPolynomial V k →+* k).quotientKerEquivOfRightInverse
      (fun a => constantCoeff_C V a))

@[simp] lemma residueRingEquiv_mk (f : MvPolynomial V k) :
    residueRingEquiv (Ideal.Quotient.mk (idealOfVars V k) f) = constantCoeff f := by
  simp [residueRingEquiv]

lemma ofList_fin_variables (n : ℕ) :
    Ideal.ofList (List.ofFn (X : Fin n → MvPolynomial (Fin n) k)) =
      idealOfVars (Fin n) k := by
  apply congrArg Ideal.span
  ext f
  simp

/-- The residue module used in Tor; the preceding ring equivalence identifies it with `k`. -/
abbrev Residue (n : ℕ) (k : Type u) [CommRing k] :=
  MvPolynomial (Fin n) k ⧸ idealOfVars (Fin n) k

/-- An actual finite free Koszul resolution of the polynomial coefficient field. -/
def polynomialResolution [Nontrivial k] (n : ℕ) :
    ProjectiveResolution (ModuleCat.of (MvPolynomial (Fin n) k) (Residue n k)) :=
  transportResolution
    (regularSequenceResolution (List.ofFn (X : Fin n → MvPolynomial (Fin n) k))
      (fin_variables_regular n))
    (Submodule.quotEquivOfEq _ _ (ofList_fin_variables (k := k) n)).toModuleIso

@[simp] lemma polynomialResolution_complex [Nontrivial k] (n : ℕ) :
    (polynomialResolution (k := k) n).complex =
      koszulComplex.ofList (List.ofFn (X : Fin n → MvPolynomial (Fin n) k)) := rfl

/-- Derived Tor against the actual polynomial residue field. -/
def polynomialTor [Nontrivial k] (n i : ℕ)
    (M : ModuleCat.{u} (MvPolynomial (Fin n) k)) :
    ModuleCat.{u} (MvPolynomial (Fin n) k) :=
  ((Tor' (ModuleCat (MvPolynomial (Fin n) k)) i).obj
    (ModuleCat.of (MvPolynomial (Fin n) k) (Residue n k))).obj M

/-- The canonical isomorphism from genuine derived Tor to the variable Koszul homology. -/
def polynomialTorIso [Nontrivial k] (n i : ℕ)
    (M : ModuleCat.{u} (MvPolynomial (Fin n) k)) :
    polynomialTor n i M ≅
      (coefficientComplex (List.ofFn (X : Fin n → MvPolynomial (Fin n) k)) M).homology i :=
  (polynomialResolution (k := k) n).isoLeftDerivedObj
    ((CategoryTheory.MonoidalCategory.tensoringRight _).obj M) i

end CommAlg.Koszul

end
end CheckedSource5

/-! ## Source: TauCeti.Algebra.Homology.HomologicalComplex.Basic -/
section CheckedSource6
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Additional API for homological complexes

This file records additivity of the cycles functor, degreewise recursion for powers of a
complex endomorphism, and the existence of coproducts of complexes, computed degreewise. It also
records the basic properties of the maps
`K.toCycles i j : K.X i ⟶ K.cycles j` induced by the differentials: they kill the cycles in degree
`i`, commute with morphisms of complexes, vanish after a morphism from a complex concentrated in
degree `i`, and are epimorphisms in degrees where the complex is exact. In a degree with no nonzero
differential into it, the identification of the homology with the cycles is natural
(`HomologicalComplex.isoHomologyπ_inv_naturality`). The sequence
`Zᵢ ⟶ Kᵢ ⟶ Zⱼ` of cycles is exact when `j = c.next i`
(`HomologicalComplex.cyclesShortComplex_exact`). For adjacent degrees `i` and `j`, the cycles of a
complex exact in degree `j` fit into a short exact sequence `0 ⟶ Zᵢ ⟶ Kᵢ ⟶ Zⱼ ⟶ 0`
(`HomologicalComplex.cyclesShortComplex_shortExact`), which stays short exact when its outer terms
are replaced by isomorphic objects (`HomologicalComplex.cyclesShortComplex_shortExact_of_iso`);
likewise a monomorphism onto the kernel of the differential `Kᵢ ⟶ Kⱼ` gives a short exact sequence
`0 ⟶ A ⟶ Kᵢ ⟶ Zⱼ ⟶ 0` (`HomologicalComplex.shortExact_toCycles`). Constructing the bundled cycle
sequence requires homology only in the two selected degrees.
The exactness results additionally require homology of the cycle sequence itself.
For chain complexes indexed by the natural numbers, the identification of zero chains with
cycles is natural (`ChainComplex.cycles₀Iso_inv_naturality`), and so is the passage from zero
chains to zeroth homology (`ChainComplex.pOpcycles_comp_isoHomologyι₀_inv_comp_homologyMap`).
The isomorphisms `homologyIsoSc'`
are natural (`HomologicalComplex.homologyMap_comp_homologyIsoSc'_hom`), and exactness in a degree
is the vanishing of the homology of the short complex `sc'` there
(`HomologicalComplex.exactAt_iff_isZero_homology_sc'`).
Homology of complexes commutes with an additive functor preserving homology
(`CategoryTheory.Functor.mapHomologicalComplexCompHomologyFunctorIso`), the complex-level form of
Mathlib's `CategoryTheory.ShortComplex.homologyFunctorIso`.
-/

section

open CategoryTheory Limits

universe w v u

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {ι : Type*}
  {c : ComplexShape ι} {K : HomologicalComplex C c} {s : K ⟶ K}

/-- Degreewise recursion for the powers of a chain endomorphism. -/
lemma pow_f_succ (m : ℕ) (i : ι) :
    (End.of s ^ (m + 1)).asHom.f i = (End.of s ^ m).asHom.f i ≫ s.f i := by
  rw [pow_succ', End.mul_asHom, comp_f]

/-- Homological complexes have the coproducts that the underlying category has. They are
computed degreewise. -/
instance hasCoproducts [HasCoproducts.{w} C] : HasCoproducts.{w} (HomologicalComplex C c) :=
  fun _ ↦ inferInstance

/-! ### The maps onto the cycles -/

section Cycles

variable (K) {L : HomologicalComplex C c}

/-- The map from the cycles in degree `i` to the cycles in degree `j` induced by the differential
vanishes. -/
@[reassoc]
lemma iCycles_toCycles (i j : ι) [K.HasHomology i] [K.HasHomology j] :
    K.iCycles i ≫ K.toCycles i j = 0 := by
  rw [← cancel_mono (K.iCycles j), Category.assoc, toCycles_i, iCycles_d, zero_comp]

/-- The short complex `Zᵢ(K) ⟶ Kᵢ ⟶ Zⱼ(K)` cut out of a homological complex. Its
second map is the differential with codomain restricted to the cycles in degree `j`. -/
noncomputable def cyclesShortComplex (i j : ι) [K.HasHomology i] [K.HasHomology j] :
    ShortComplex C :=
  ShortComplex.mk (K.iCycles i) (K.toCycles i j) (K.iCycles_toCycles i j)

/-- The cycle sequence is formed by the inclusion of cycles and the corestricted differential. -/
lemma cyclesShortComplex_def (i j : ι) [K.HasHomology i] [K.HasHomology j] :
    K.cyclesShortComplex i j =
      ShortComplex.mk (K.iCycles i) (K.toCycles i j) (K.iCycles_toCycles i j) := (rfl)

@[simp]
lemma cyclesShortComplex_X₁ (i j : ι) [K.HasHomology i] [K.HasHomology j] :
    (K.cyclesShortComplex i j).X₁ = K.cycles i := (rfl)

@[simp]
lemma cyclesShortComplex_X₂ (i j : ι) [K.HasHomology i] [K.HasHomology j] :
    (K.cyclesShortComplex i j).X₂ = K.X i := (rfl)

@[simp]
lemma cyclesShortComplex_X₃ (i j : ι) [K.HasHomology i] [K.HasHomology j] :
    (K.cyclesShortComplex i j).X₃ = K.cycles j := (rfl)

/-- The first map of the cycle sequence is the inclusion of cycles, transported along the
object equalities `cyclesShortComplex_X₁` and `cyclesShortComplex_X₂`. -/
@[simp]
lemma cyclesShortComplex_f (i j : ι) [K.HasHomology i] [K.HasHomology j] :
    (K.cyclesShortComplex i j).f = eqToHom (K.cyclesShortComplex_X₁ i j) ≫ K.iCycles i ≫
      eqToHom (K.cyclesShortComplex_X₂ i j).symm :=
  (Category.comp_id _).symm.trans (Category.id_comp _).symm

/-- The second map of the cycle sequence is the corestricted differential, transported along the
object equalities `cyclesShortComplex_X₂` and `cyclesShortComplex_X₃`. -/
@[simp]
lemma cyclesShortComplex_g (i j : ι) [K.HasHomology i] [K.HasHomology j] :
    (K.cyclesShortComplex i j).g = eqToHom (K.cyclesShortComplex_X₂ i j) ≫ K.toCycles i j ≫
      eqToHom (K.cyclesShortComplex_X₃ i j).symm :=
  (Category.comp_id _).symm.trans (Category.id_comp _).symm

variable {K}

/-- The maps onto the cycles induced by the differentials commute with morphisms of complexes. -/
@[reassoc]
lemma toCycles_cyclesMap (φ : K ⟶ L) (i j : ι) [K.HasHomology j] [L.HasHomology j] :
    K.toCycles i j ≫ cyclesMap φ j = φ.f i ≫ L.toCycles i j :=
  (cancel_mono (L.iCycles j)).1 <| by simp

/-- In a degree `j` with no nonzero differential into it, the identifications
`K.isoHomologyπ i j` of the homology with the cycles commute with the maps induced by a morphism of
complexes. -/
@[reassoc]
lemma isoHomologyπ_inv_naturality (φ : K ⟶ L) (i j : ι) (hi : c.prev j = i) (hK : K.d i j = 0)
    (hL : L.d i j = 0) [K.HasHomology j] [L.HasHomology j] :
    homologyMap φ j ≫ (L.isoHomologyπ i j hi hL).inv =
      (K.isoHomologyπ i j hi hK).inv ≫ cyclesMap φ j := by
  rw [← cancel_epi (K.isoHomologyπ i j hi hK).hom]
  simp

variable [HasZeroObject C] [DecidableEq ι] {i : ι} {X : C}

/-- A morphism from a complex concentrated in degree `i` vanishes after the differential out of
degree `i`. -/
@[reassoc]
lemma single_f_d (g : (single C c i).obj X ⟶ L) (j : ι) : g.f i ≫ L.d i j = 0 := by
  rw [g.comm i j, single_obj_d, zero_comp]

/-- A morphism from a complex concentrated in degree `i` vanishes after the map onto the cycles in
degree `j`. -/
@[reassoc]
lemma single_f_toCycles (g : (single C c i).obj X ⟶ L) (j : ι) [L.HasHomology j] :
    g.f i ≫ L.toCycles i j = 0 := by
  rw [← cancel_mono (L.iCycles j), Category.assoc, toCycles_i, single_f_d, zero_comp]

end Cycles

end HomologicalComplex

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {ι : Type*}
  {c : ComplexShape ι} {K : HomologicalComplex C c}

variable (K) in
/-- The sequence `Zᵢ ⟶ Kᵢ ⟶ Zⱼ` of the cycles of a complex `K` is exact when `j` is the degree
following `i`: the cycles in degree `i` are the kernel of the differential. -/
lemma cyclesShortComplex_exact (i j : ι) [K.HasHomology i] [K.HasHomology j]
    [hH : (K.cyclesShortComplex i j).HasHomology] (hij : c.next i = j) :
    (K.cyclesShortComplex i j).Exact := by
  rw [cyclesShortComplex_def] at hH ⊢
  let S := ShortComplex.mk _ _ (K.iCycles_toCycles i j)
  have hS := isKernelOfComp (K.iCycles j) (K.d i j) (K.cyclesIsKernel i j hij)
    (K.iCycles_toCycles i j) (K.toCycles_i i j)
  rw [S.exact_iff_iCycles_pOpcycles_zero]
  have h : hS.lift (KernelFork.ofι S.iCycles S.iCycles_g) ≫ S.f = S.iCycles :=
    Fork.IsLimit.lift_ι _
  rw [← h, Category.assoc, S.f_pOpcycles, comp_zero]

/-- A morphism killed by the differential `Kᵢ ⟶ Kⱼ` is killed by its corestriction to the
cycles in degree `j`. -/
lemma comp_toCycles_eq_zero {A : C} {i : ι} (j : ι) [K.HasHomology j] (a : A ⟶ K.X i)
    (ha : a ≫ K.d i j = 0) : a ≫ K.toCycles i j = 0 := by
  rw [← cancel_mono (K.iCycles j), Category.assoc, K.toCycles_i, ha, zero_comp]

/-- The corestriction `Kᵢ ⟶ Zⱼ` of the differential has the same kernel as the differential
`Kᵢ ⟶ Kⱼ`: if `A ⟶ Kᵢ ⟶ Kⱼ` is exact, then so is `A ⟶ Kᵢ ⟶ Zⱼ`. -/
lemma exact_toCycles {A : C} {i : ι} (j : ι) [K.HasHomology j] (a : A ⟶ K.X i)
    (ha : a ≫ K.d i j = 0) (hex : (ShortComplex.mk a (K.d i j) ha).Exact) :
    (ShortComplex.mk a (K.toCycles i j) (comp_toCycles_eq_zero j a ha)).Exact :=
  (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
    (S₁ := ShortComplex.mk a (K.toCycles i j) (comp_toCycles_eq_zero j a ha))
    (S₂ := ShortComplex.mk a (K.d i j) ha)
    { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := K.iCycles j }).2 hex

end HomologicalComplex

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] {ι : Type*}
  {c : ComplexShape ι} {K : HomologicalComplex C c}

/-- In a complex exact in degree `j`, the map onto the cycles in degree `j` from the preceding
degree is an epimorphism. -/
lemma epi_toCycles_of_exactAt {i j : ι} [K.HasHomology j]
    (h : K.ExactAt j) (hij : c.prev j = i) :
    Epi (K.toCycles i j) := by
  rw [exactAt_iff' _ i j (c.next j) hij rfl] at h
  have := h.hasHomology
  rw [← epi_comp_iff_of_isIso _ (K.cyclesIsoSc' i j (c.next j) hij rfl).hom,
    K.toCycles_cyclesIsoSc'_hom]
  exact h.epi_toCycles

/-- The cycle sequence `Zᵢ(K) ⟶ Kᵢ ⟶ Zⱼ(K)` is short exact when `i` and `j` are adjacent
and `K` is exact in degree `j`. -/
lemma cyclesShortComplex_shortExact (i j : ι) [K.HasHomology i] [K.HasHomology j]
    [(K.cyclesShortComplex i j).HasHomology]
    (hij : c.Rel i j) (hK : K.ExactAt j) : (K.cyclesShortComplex i j).ShortExact := by
  have hE := K.cyclesShortComplex_exact i j (c.next_eq' hij)
  rw [cyclesShortComplex_def] at hE ⊢
  exact ShortComplex.ShortExact.mk' hE
    inferInstance (epi_toCycles_of_exactAt hK (c.prev_eq' hij))

/-- The cycle sequence `Zᵢ(K) ⟶ Kᵢ ⟶ Zⱼ(K)`, with its outer terms replaced along isomorphisms
`X ≅ Zᵢ(K)` and `Zⱼ(K) ≅ Y`, is short exact when `i` and `j` are adjacent and `K` is exact in
degree `j`. -/
lemma cyclesShortComplex_shortExact_of_iso {i j : ι} [K.HasHomology i] [K.HasHomology j]
    [(K.cyclesShortComplex i j).HasHomology] (hij : c.Rel i j) (hK : K.ExactAt j) {X Y : C}
    (e : X ≅ K.cycles i) (e' : K.cycles j ≅ Y) :
    (ShortComplex.mk (e.hom ≫ K.iCycles i) (K.toCycles i j ≫ e'.hom)
      (by simp [iCycles_toCycles_assoc])).ShortExact :=
  ShortComplex.shortExact_of_iso (ShortComplex.isoMk e.symm (Iso.refl (K.X i)) e') <|
    K.cyclesShortComplex_def i j ▸ K.cyclesShortComplex_shortExact i j hij hK

/-- A monomorphism `A ⟶ Kᵢ` onto the kernel of the differential `Kᵢ ⟶ Kⱼ` fits into a short exact
sequence `0 ⟶ A ⟶ Kᵢ ⟶ Zⱼ ⟶ 0` when `i` precedes `j` and `K` is exact in degree `j`. -/
lemma shortExact_toCycles {A : C} {i j : ι} [K.HasHomology j] (a : A ⟶ K.X i) [Mono a]
    (ha : a ≫ K.d i j = 0) (hex : (ShortComplex.mk a (K.d i j) ha).Exact)
    (hij : c.prev j = i) (hK : K.ExactAt j) :
    (ShortComplex.mk a (K.toCycles i j) (comp_toCycles_eq_zero j a ha)).ShortExact :=
  have := epi_toCycles_of_exactAt hK hij
  { exact := exact_toCycles j a ha hex }

end HomologicalComplex

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] {ι : Type*} {c : ComplexShape ι}
  {K L : HomologicalComplex C c}

/-- Taking cycles is additive on morphisms of complexes. -/
@[simp]
lemma cyclesMap_add (f g : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i] :
    cyclesMap (f + g) i = cyclesMap f i + cyclesMap g i := by
  apply (cancel_mono (L.iCycles i)).1
  simp only [Preadditive.add_comp, cyclesMap_i, add_f_apply, Preadditive.comp_add]

instance cyclesFunctor_additive [CategoryWithHomology C] (i : ι) :
    (cyclesFunctor C c i).Additive where
  map_add := by
    intro X Y f g
    -- `cyclesFunctor` is opaque, so expose its defining map before applying the map-level API.
    change cyclesMap (f + g) i = cyclesMap f i + cyclesMap g i
    exact cyclesMap_add f g i

section HomologyIsoSc'

variable {C : Type*} [Category* C] [HasZeroMorphisms C] {ι : Type*}
  {c : ComplexShape ι} {K L : HomologicalComplex C c} (f : K ⟶ L) (i j k : ι)
  (hi : c.prev j = i) (hk : c.next j = k) [K.HasHomology j] [L.HasHomology j]
  [(K.sc' i j k).HasHomology] [(L.sc' i j k).HasHomology]

/-- The isomorphisms `homologyIsoSc'` are natural (this is the naturality of Mathlib's
`homologyFunctorIso'`, for complexes which only individually have homology). -/
@[reassoc]
lemma homologyMap_comp_homologyIsoSc'_hom :
    homologyMap f j ≫ (L.homologyIsoSc' i j k hi hk).hom =
      (K.homologyIsoSc' i j k hi hk).hom ≫
        ShortComplex.homologyMap ((shortComplexFunctor' C c i j k).map f) := by
  rw [homologyIsoSc', homologyIsoSc', ShortComplex.homologyMapIso_hom,
    ShortComplex.homologyMapIso_hom, homologyMap]
  -- the source of `homologyMap f j` is `K.homology j`, which is `(K.sc j).homology` only up to
  -- unfolding `HomologicalComplex.homology`, so the generic `homologyMap_comp` needs `erw`
  erw [← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp]
  congr 1
  exact (natIsoSc' C c i j k hi hk).hom.naturality f

end HomologyIsoSc'

/-- A homological complex is exact at `j` exactly when the homology of its short complex at `j`,
with explicit neighbouring indices, is zero. -/
lemma exactAt_iff_isZero_homology_sc' {C : Type*} [Category* C] [HasZeroMorphisms C] {ι : Type*}
    {c : ComplexShape ι} (L : HomologicalComplex C c) (i j k : ι) (hi : c.prev j = i)
    (hk : c.next j = k) [(L.sc' i j k).HasHomology] :
    L.ExactAt j ↔ IsZero (L.sc' i j k).homology :=
  (exactAt_iff' L i j k hi hk).trans (ShortComplex.exact_iff_isZero_homology _)

end HomologicalComplex

namespace ChainComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {K L : ChainComplex C ℕ} [K.HasHomology 0] [L.HasHomology 0]

/-- The identification of degree-zero chains with degree-zero cycles is natural. -/
@[reassoc]
lemma cycles₀Iso_inv_naturality (φ : K ⟶ L) :
    K.cycles₀Iso.inv ≫ HomologicalComplex.cyclesMap φ 0 =
      φ.f 0 ≫ L.cycles₀Iso.inv := by
  apply (cancel_mono (L.iCycles 0)).1
  simp

/-- The passage from degree-zero chains to degree-zero homology, through the identification of
the homology with the opcycles, is natural. -/
@[reassoc]
lemma pOpcycles_comp_isoHomologyι₀_inv_comp_homologyMap (φ : K ⟶ L) :
    K.pOpcycles 0 ≫ K.isoHomologyι₀.inv ≫ HomologicalComplex.homologyMap φ 0 =
      φ.f 0 ≫ L.pOpcycles 0 ≫ L.isoHomologyι₀.inv := by
  rw [ChainComplex.isoHomologyι₀_inv_naturality, HomologicalComplex.p_opcyclesMap_assoc]

end ChainComplex

namespace HomologicalComplex

section HomologyTransport

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [CategoryWithHomology C]
  {ι : Type*} {c : ComplexShape ι} {L L' M M' : HomologicalComplex C c}

/-- A morphism transported along equalities of complexes induces the corresponding transport
of the homology map. -/
lemma homologyMap_comp_eqToHom (ψ : L ⟶ L') (hM : M = L) (hM' : M' = L')
    (τ : M ⟶ M') (hτ : τ = eqToHom hM ≫ ψ ≫ eqToHom hM'.symm) (q : ι) :
    homologyMap τ q ≫ eqToHom (congrArg (·.homology q) hM') =
      eqToHom (congrArg (·.homology q) hM) ≫ homologyMap ψ q := by
  subst hM hM' hτ
  simp

end HomologyTransport

end HomologicalComplex

namespace CategoryTheory.Functor

variable {C : Type*} [Category* C] {D : Type*} [Category* D]
  [Preadditive C] [Preadditive D] [CategoryWithHomology C] [CategoryWithHomology D]
  (F : C ⥤ D) [F.Additive] [F.PreservesHomology] {ι : Type*} (c : ComplexShape ι) (i : ι)

/-- Homology of homological complexes commutes with a functor preserving homology. -/
noncomputable def mapHomologicalComplexCompHomologyFunctorIso :
    F.mapHomologicalComplex c ⋙ HomologicalComplex.homologyFunctor D c i ≅
      HomologicalComplex.homologyFunctor C c i ⋙ F :=
  -- the short complex of `F` applied to `K` in degree `i` is `F` applied to that of `K`
  isoWhiskerLeft (HomologicalComplex.shortComplexFunctor C c i) (ShortComplex.homologyFunctorIso F)

@[simp]
lemma mapHomologicalComplexCompHomologyFunctorIso_hom_app (K : HomologicalComplex C c) :
    (F.mapHomologicalComplexCompHomologyFunctorIso c i).hom.app K =
      ((K.sc i).mapHomologyIso F).hom :=
  (rfl)

end CategoryTheory.Functor

end
end CheckedSource6

/-! ## Source: TauCeti.Algebra.Homology.Homotopy -/
section CheckedSource7
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Constructions on chain homotopies

Four constructions of chain homotopies: two produce new homotopies from old ones, and the
other two assemble a null-homotopy from components given all at once.

`Homotopy.descCokernel` descends a homotopy along a degreewise cokernel.  Let `p : L ⟶ M` exhibit
`M` in each degree as the cokernel of `u : K ⟶ L`, and let `p' : L' ⟶ M'` be any morphism of
complexes.  A chain homotopy between morphisms `L ⟶ L'` whose components send the image of `u`
into the kernel of `p'` then descends to a chain homotopy between the induced morphisms `M ⟶ M'`.
Only the source side is assumed to be a degreewise cokernel; on the target side the hypothesis is
the bare vanishing `u.f i ≫ HL.hom i j ≫ p'.f j = 0`, which is what the universal property needs.
This is the mechanism behind homotopy invariance of relative homology, where `M` is the relative
chain complex of a pair, that is, the degreewise cokernel of the chains of the subspace, and the
vanishing holds because the homotopy restricts to the subspace.

`Homotopy.idPow` iterates a chain homotopy from the identity of `K` to an endomorphism `s`: it
exhibits every power `sᵐ` as homotopic to the identity, through the explicit operator
`∑_{k < m} sᵏ ≫ h`.  Its components are needed, and not just the existence of some homotopy, when
`m` is allowed to vary from one summand of `K` to another, as in the proof that small singular
chains for an open cover include as a chain homotopy equivalence.

`Homotopy.mkChainComplex` builds a null-homotopy of a chain map between `ℕ`-indexed chain
complexes from its components `h n : P.X n ⟶ Q.X (n + 1)`, given all at once together with the
homotopy identities in degree zero and in positive degrees.  It is the non-inductive counterpart of
Mathlib's `Homotopy.mkInductive`, for the situation where the components are constructed by a
recursion of their own rather than one degree at a time from the previous two.

`Homotopy.mkCochainComplexInt` is its counterpart for `ℤ`-indexed cochain complexes: a
null-homotopy of `e : P ⟶ Q` from components `h n : P.X (n + 1) ⟶ Q.X n` and the homotopy
identities `e.f (n + 1) = d ≫ h (n + 1) + h n ≫ d`, stated in every degree `n + 1` so that no
index is a difference.

`Homotopy.comm_zero_apply` and `Homotopy.comm_succ_apply` are the homotopy identities of a
homotopy between maps of `ℕ`-indexed chain complexes of modules, evaluated on elements.

`CochainComplex.nonempty_homotopy_mkHomToSingle_zero_iff` characterizes null-homotopic chain maps
from a cochain complex `K` to an object `A` placed in degree `i`: the map given by `φ : Kⁱ ⟶ A` is
null-homotopic if and only if `φ` factors through the differential `Kⁱ ⟶ Kⁱ⁺¹`. It is Mathlib's
criterion `CochainComplex.HomComplex.Cocycle.toSingleMk_mem_coboundaries_iff`, translated from
coboundaries to homotopies.

`Homotopy.cyclesMap_sub_eq` expresses the difference of the maps on cycles induced by
homotopic maps as a factorization through a term of the target complex. In particular, these
maps agree after passing to a stable category that kills that term.
-/

section

noncomputable section

open CategoryTheory Limits

universe v u

namespace Homotopy

/-- On cycles, the difference of homotopic maps factors through the preceding target term.
This identity does not require exactness of either complex. -/
theorem cyclesMap_sub_eq {C : Type u} [Category.{v} C] [Preadditive C]
    {ι : Type*} {c : ComplexShape ι} {K L : HomologicalComplex C c} {f g : K ⟶ L}
    (h : Homotopy f g) (i : ι) [K.HasHomology i] [L.HasHomology i] :
    HomologicalComplex.cyclesMap f i - HomologicalComplex.cyclesMap g i =
      K.iCycles i ≫ h.hom i (c.prev i) ≫ L.toCycles (c.prev i) i := by
  apply (cancel_mono (L.iCycles i)).mp
  simp only [Preadditive.sub_comp, HomologicalComplex.cyclesMap_i, Category.assoc,
    HomologicalComplex.toCycles_i]
  rw [h.comm i]
  simp [dNext, prevD, Preadditive.comp_add, ← Category.assoc]

variable {C : Type u} [Category.{v} C] [Preadditive C] {ι : Type*} {c : ComplexShape ι}
  {K L M L' M' : HomologicalComplex C c}
  {fL gL : L ⟶ L'} {fM gM : M ⟶ M'}
  (HL : Homotopy fL gL)
  (u : K ⟶ L) (p : L ⟶ M) (p' : L' ⟶ M')
  (hw : ∀ i, u.f i ≫ p.f i = 0)
  (hp : ∀ i, IsColimit (CokernelCofork.ofπ (p.f i) (hw i)))
  (hcomm : ∀ i j, u.f i ≫ HL.hom i j ≫ p'.f j = 0)

include hw hp hcomm

/-- The components of the chain homotopy that `Homotopy.descCokernel` obtains on the quotient
complex `M`. -/
@[no_expose]
def descCokernelHom (i j : ι) : M.X i ⟶ M'.X j :=
  (CokernelCofork.IsColimit.desc' (hp i) (HL.hom i j ≫ p'.f j) (hcomm i j)).1

@[reassoc (attr := simp)]
lemma π_descCokernelHom (i j : ι) :
    p.f i ≫ descCokernelHom HL u p p' hw hp hcomm i j = HL.hom i j ≫ p'.f j :=
  (CokernelCofork.IsColimit.desc' (hp i) (HL.hom i j ≫ p'.f j) (hcomm i j)).2

private lemma π_comp_dNext (i : ι) :
    p.f i ≫ dNext i (descCokernelHom HL u p p' hw hp hcomm) = dNext i HL.hom ≫ p'.f i := by
  rw [← dNext_comp_left, ← dNext_comp_right]
  exact congrArg (fun F ↦ dNext i F) (by funext a b; exact π_descCokernelHom ..)

private lemma π_comp_prevD (i : ι) :
    p.f i ≫ prevD i (descCokernelHom HL u p p' hw hp hcomm) = prevD i HL.hom ≫ p'.f i := by
  rw [← prevD_comp_left, ← prevD_comp_right]
  exact congrArg (fun F ↦ prevD i F) (by funext a b; exact π_descCokernelHom ..)

/-- A chain homotopy on the total complexes whose components kill the subcomplex after composing
with `p'` descends to a chain homotopy on the quotient complex `M`. -/
@[no_expose]
def descCokernel (hf : p ≫ fM = fL ≫ p') (hg : p ≫ gM = gL ≫ p') : Homotopy fM gM where
  hom := descCokernelHom HL u p p' hw hp hcomm
  zero i j hij := Cofork.IsColimit.hom_ext (hp i) (by simp [HL.zero i j hij])
  comm i := Cofork.IsColimit.hom_ext (hp i) (by
    simp only [Cofork.π_ofπ, Preadditive.comp_add, π_comp_dNext, π_comp_prevD,
      ← HomologicalComplex.comp_f p fM, ← HomologicalComplex.comp_f p gM, hf, hg,
      HomologicalComplex.comp_f]
    rw [← Preadditive.add_comp, ← Preadditive.add_comp, ← HL.comm i])

@[simp]
lemma descCokernel_hom (hf : p ≫ fM = fL ≫ p') (hg : p ≫ gM = gL ≫ p') :
    (descCokernel HL u p p' hw hp hcomm hf hg).hom = descCokernelHom HL u p p' hw hp hcomm := (rfl)

@[reassoc]
lemma π_descCokernel_hom (hf : p ≫ fM = fL ≫ p') (hg : p ≫ gM = gL ≫ p') (i j : ι) :
    p.f i ≫ (descCokernel HL u p p' hw hp hcomm hf hg).hom i j = HL.hom i j ≫ p'.f j :=
  π_descCokernelHom HL u p p' hw hp hcomm i j

end Homotopy

section Pow

variable {C : Type u} [Category.{v} C] {ι : Type*} {c : ComplexShape ι}

namespace Homotopy

variable [Preadditive C] {K : HomologicalComplex C c} {s : K ⟶ K}

/-- Iterating a chain homotopy from the identity.  If `h` is a chain homotopy from the identity of
`K` to a chain endomorphism `s`, then `h.idPow m` is a chain homotopy from the identity to the
`m`-th power of `s`, whose operator in bidegree `(i, j)` is `∑_{k < m} (sᵏ)ᵢ ≫ hᵢⱼ`. -/
@[no_expose]
def idPow (h : Homotopy (𝟙 K) s) (m : ℕ) : Homotopy (𝟙 K) (End.of s ^ m).asHom where
  hom i j := ∑ k ∈ Finset.range m, (End.of s ^ k).asHom.f i ≫ h.hom i j
  zero i j hij := by simp [h.zero i j hij]
  comm i := by
    have hdn : dNext i (fun a b ↦ ∑ k ∈ Finset.range m, (End.of s ^ k).asHom.f a ≫ h.hom a b) =
        ∑ k ∈ Finset.range m, (End.of s ^ k).asHom.f i ≫ dNext i h.hom := by
      simpa only [Finset.sum_fn, dNext_comp_left] using
        map_sum (dNext i) (fun k a b ↦ (End.of s ^ k).asHom.f a ≫ h.hom a b) (Finset.range m)
    have hpv : prevD i (fun a b ↦ ∑ k ∈ Finset.range m, (End.of s ^ k).asHom.f a ≫ h.hom a b) =
        ∑ k ∈ Finset.range m, (End.of s ^ k).asHom.f i ≫ prevD i h.hom := by
      simpa only [Finset.sum_fn, prevD_comp_left] using
        map_sum (prevD i) (fun k a b ↦ (End.of s ^ k).asHom.f a ≫ h.hom a b) (Finset.range m)
    have hstep : ∀ k ∈ Finset.range m, (End.of s ^ k).asHom.f i ≫ dNext i h.hom +
        (End.of s ^ k).asHom.f i ≫ prevD i h.hom =
        (End.of s ^ k).asHom.f i - (End.of s ^ (k + 1)).asHom.f i := fun k _ ↦ by
      have hsum : dNext i h.hom + prevD i h.hom = 𝟙 (K.X i) - s.f i := by
        have hc := h.comm i
        rw [HomologicalComplex.id_f] at hc
        rw [hc]
        abel
      rw [← Preadditive.comp_add, hsum, Preadditive.comp_sub, Category.comp_id,
        HomologicalComplex.pow_f_succ]
    rw [hdn, hpv, ← Finset.sum_add_distrib, Finset.sum_congr rfl hstep,
      Finset.sum_range_sub' (fun k ↦ (End.of s ^ k).asHom.f i) m, pow_zero, End.one_asHom,
      HomologicalComplex.id_f]
    abel

@[simp]
lemma idPow_hom (h : Homotopy (𝟙 K) s) (m : ℕ) (i j : ι) :
    (h.idPow m).hom i j = ∑ k ∈ Finset.range m, (End.of s ^ k).asHom.f i ≫ h.hom i j := (rfl)

end Homotopy

end Pow

section MkChainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] {P Q : ChainComplex C ℕ}

namespace Homotopy

/-- A null-homotopy of a chain map `e : P ⟶ Q` between `ℕ`-indexed chain complexes, from its
components `h n : P.X n ⟶ Q.X (n + 1)` and the homotopy identities `e.f 0 = h 0 ≫ d` and
`e.f (n + 1) = d ≫ h n + h (n + 1) ≫ d`. The components are given all at once; compare
`Homotopy.mkInductive`, which constructs them one degree at a time. -/
@[no_expose]
def mkChainComplex (e : P ⟶ Q) (h : ∀ n, P.X n ⟶ Q.X (n + 1)) (comm_zero : e.f 0 = h 0 ≫ Q.d 1 0)
    (comm_succ : ∀ n, e.f (n + 1) = P.d (n + 1) n ≫ h n + h (n + 1) ≫ Q.d (n + 2) (n + 1)) :
    Homotopy e 0 where
  hom i j := if hij : i + 1 = j then h i ≫ eqToHom (congrArg Q.X hij) else 0
  zero i j hij := dite_eq_right (by simpa [ComplexShape.down_Rel] using hij)
  comm i := by
    cases i with
    | zero =>
        rw [dNext_zero_chainComplex, prevD_chainComplex]
        simpa using comm_zero
    | succ i =>
        rw [dNext_succ_chainComplex, prevD_chainComplex]
        simpa using comm_succ i

@[simp]
lemma mkChainComplex_hom_succ (e : P ⟶ Q) (h : ∀ n, P.X n ⟶ Q.X (n + 1))
    (comm_zero : e.f 0 = h 0 ≫ Q.d 1 0)
    (comm_succ : ∀ n, e.f (n + 1) = P.d (n + 1) n ≫ h n + h (n + 1) ≫ Q.d (n + 2) (n + 1))
    (n : ℕ) : (mkChainComplex e h comm_zero comm_succ).hom n (n + 1) = h n := by
  simp [mkChainComplex]

end Homotopy

end MkChainComplex

section MkCochainComplexInt

variable {C : Type u} [Category.{v} C] [Preadditive C] {P Q : CochainComplex C ℤ}

namespace Homotopy

/-- A null-homotopy of a map `e : P ⟶ Q` between `ℤ`-indexed cochain complexes, from its
components `h n : P.X (n + 1) ⟶ Q.X n` and the homotopy identities
`e.f (n + 1) = d ≫ h (n + 1) + h n ≫ d`. Every degree is written as `n + 1`, so that no index is
ever a difference. The components are given all at once, as in `Homotopy.mkChainComplex`. -/
@[no_expose]
def mkCochainComplexInt (e : P ⟶ Q) (h : ∀ n, P.X (n + 1) ⟶ Q.X n)
    (comm : ∀ n, e.f (n + 1) = P.d (n + 1) (n + 1 + 1) ≫ h (n + 1) + h n ≫ Q.d n (n + 1)) :
    Homotopy e 0 where
  hom i j := if hij : j + 1 = i then eqToHom (congrArg P.X hij.symm) ≫ h j else 0
  zero i j hij := dite_eq_right (by simpa [ComplexShape.up_Rel] using hij)
  comm i := by
    obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
    rw [dNext_eq _ (ComplexShape.up_mk (n + 1) (n + 1 + 1) rfl),
      prevD_eq _ (ComplexShape.up_mk n (n + 1) rfl)]
    simpa using comm n

@[simp]
lemma mkCochainComplexInt_hom (e : P ⟶ Q) (h : ∀ n, P.X (n + 1) ⟶ Q.X n)
    (comm : ∀ n, e.f (n + 1) = P.d (n + 1) (n + 1 + 1) ≫ h (n + 1) + h n ≫ Q.d n (n + 1))
    (n : ℤ) : (mkCochainComplexInt e h comm).hom (n + 1) n = h n := by
  simp [mkCochainComplexInt]

end Homotopy

end MkCochainComplexInt

section ModuleCat

variable {R : Type*} [Ring R] {P Q : HomologicalComplex (ModuleCat R) PalomarBarycentricTor.naturalDown} {e e' : P ⟶ Q}

namespace Homotopy

/-- The homotopy identity in degree zero, on elements: the difference of the two maps is the
boundary of the homotopy. -/
theorem comm_zero_apply (h : Homotopy e e') (x : P.X 0) :
    e.f 0 x = Q.d 1 0 (h.hom 0 1 x) + e'.f 0 x := by
  have hc := h.comm 0
  rw [dNext_zero_chainComplex, prevD_chainComplex, zero_add] at hc
  simpa using congrArg (fun φ : P.X 0 ⟶ Q.X 0 ↦ φ x) hc

/-- The homotopy identity in positive degrees, on elements. -/
theorem comm_succ_apply (h : Homotopy e e') (n : ℕ) (x : P.X (n + 1)) :
    e.f (n + 1) x =
      h.hom n (n + 1) (P.d (n + 1) n x) + Q.d (n + 2) (n + 1) (h.hom (n + 1) (n + 2) x) +
        e'.f (n + 1) x := by
  have hc := h.comm (n + 1)
  rw [dNext_succ_chainComplex, prevD_chainComplex] at hc
  simpa [add_assoc] using congrArg (fun φ : P.X (n + 1) ⟶ Q.X (n + 1) ↦ φ x) hc

end Homotopy

end ModuleCat

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

open HomComplex in
/-- **Null-homotopic chain maps to an object in one degree**: the chain map from `K` to `A`
placed in degree `i` given by `φ : Kⁱ ⟶ A` is null-homotopic if and only if `φ` factors through
the differential `Kⁱ ⟶ Kʲ`, where `j = i + 1`. -/
lemma nonempty_homotopy_mkHomToSingle_zero_iff (K : CochainComplex C ℤ) {i j : ℤ}
    (hij : i + 1 = j) {A : C} (φ : K.X i ⟶ A)
    (hφ : ∀ k, (ComplexShape.up ℤ).Rel k i → K.d k i ≫ φ = 0) :
    Nonempty (Homotopy (HomologicalComplex.mkHomToSingle φ hφ) 0) ↔
      ∃ g : K.X j ⟶ A, K.d i j ≫ g = φ := by
  have hφ' : K.d (i - 1) i ≫ φ = 0 := hφ _ (by simp)
  rw [← Cocycle.toSingleMk_mem_coboundaries_iff φ (add_zero i) (i - 1) (by lia) hφ' j hij,
    mem_coboundaries_iff _ (-1) (by simp)]
  -- The cocycle of `Cocycle.toSingleMk` is the zero-cochain of the chain map.
  have h : (Cocycle.toSingleMk φ (add_zero i) (i - 1) (by lia) hφ' : Cochain _ _ 0) =
      Cochain.ofHom (HomologicalComplex.mkHomToSingle φ hφ) :=
    (Cochain.toSingleEquiv (add_zero i)).injective (by
      simp [Cochain.toSingleEquiv, HomologicalComplex.mkHomToSingle_f])
  rw [h]
  exact ⟨fun ⟨ho⟩ ↦ ⟨Cochain.ofHomotopy ho, by simp [δ_ofHomotopy]⟩,
    fun ⟨z, hz⟩ ↦ ⟨(Cochain.equivHomotopy _ _).symm ⟨z, by simpa using hz.symm⟩⟩⟩

end CochainComplex

end
end
end CheckedSource7

/-! ## Source: TauCeti.Algebra.Homology.Linear -/
section CheckedSource8
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Homology commutes with scalar multiplication of chain maps

For a linear category `C`, the map induced on homology by a chain map is linear in the chain
map: `homologyMap (a • φ) i = a • homologyMap φ i`. This is the homological-complex version of
Mathlib's `ShortComplex.homologyMap_smul`, recorded as a TODO in
`Mathlib/Algebra/Homology/Linear.lean`. It identifies, for instance, the map induced by
multiplication by a scalar on a complex of modules with multiplication by that scalar on
homology, and it makes the homology functor in each degree a linear functor.
-/

section

open CategoryTheory

namespace HomologicalComplex

variable {R : Type*} [Semiring R] {C : Type*} [Category* C] [Preadditive C]
  [CategoryTheory.Linear R C] {ι : Type*} {c : ComplexShape ι}

/-- The short complex attached to a degree sends a scalar multiple of a chain map to the scalar
multiple of the induced morphism of short complexes. -/
@[simp]
lemma shortComplexFunctor_map_smul (i : ι) (a : R) {K L : HomologicalComplex C c} (φ : K ⟶ L) :
    (shortComplexFunctor C c i).map (a • φ) = a • (shortComplexFunctor C c i).map φ := by
  -- Each component is `smul_f_apply`, stated for the `SMul` instance of the complexes.
  ext <;> exact smul_f_apply _ _ _

/-- The map induced on homology by a scalar multiple of a chain map is the scalar multiple of the
induced map. -/
@[simp]
lemma homologyMap_smul (a : R) {K L : HomologicalComplex C c} (φ : K ⟶ L) (i : ι)
    [K.HasHomology i] [L.HasHomology i] :
    homologyMap (a • φ) i = a • homologyMap φ i := by
  rw [homologyMap, shortComplexFunctor_map_smul]
  exact ShortComplex.homologyMap_smul _ _

/-- Taking homology in a fixed degree is a linear functor. -/
instance [CategoryWithHomology C] (i : ι) : (homologyFunctor C c i).Linear R where
  map_smul φ a := homologyMap_smul a φ i

end HomologicalComplex

end
end CheckedSource8

/-! ## Source: TauCeti.LinearAlgebra.CliffordAlgebra.Grading -/
section CheckedSource9
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Reading the `ℤ/2`-grading: base cases, exterior bases, and ordered products

An induction over the `ℤ/2`-grading of a Clifford algebra — Mathlib's
`CliffordAlgebra.evenOdd_induction` — hands its base case back as membership in a power of
`LinearMap.range (ι Q)` whose exponent is a `ZMod.val`. Since `(0 : ZMod 2).val` is `0` and
`(1 : ZMod 2).val` is `1`, that membership says "a scalar" in the even case and "a vector" in the
odd one. Reading it that way is bookkeeping that every such induction repeats, so it is recorded
here once and shared.

In the other direction, the ordered product `(l.map (ι Q)).prod` of a list of vectors — the
spelling `TauCeti/LinearAlgebra/CliffordAlgebra/VolumeElement/Basic.lean` uses for the volume
element — is homogeneous of degree `l.length`, which is Mathlib's
`SetLike.list_prod_map_mem_graded` for the graded monoid `CliffordAlgebra.evenOdd Q` with the
degree of each factor read off `CliffordAlgebra.ι_mem_evenOdd_one`. Reading it off by the parity of
the length is what matters downstream.

The grade involution acts on the graded piece of parity `p` by the sign `(-1) ^ p`, combining
Mathlib's `CliffordAlgebra.involute_eq_of_mem_even` and `CliffordAlgebra.involute_eq_of_mem_odd`
into one statement indexed by the parity. Once `2` is invertible, the two graded pieces are the
eigenspaces of the grade involution: the even part is its fixed space and the odd part its
`-1`-eigenspace. Mathlib proves one implication of each (the two lemmas above) and leaves the
converses as a TODO; they are recorded here. This is the form in which the grading is
transported along maps commuting with the involution, such as extension of scalars.

The coordinate basis of an exterior algebra is homogeneous for this grading: the basis vector
indexed by `s` has degree `s.card`, and — over a nontrivial ring, where a basis vector is nonzero
and the two graded pieces meet only in `0` — that degree is the *only* one it has. This statement
belongs to the grading API independently of any spin representation.

## Main results

* `CliffordAlgebra.exists_algebraMap_of_mem_range_ι_pow_zero`: in the even base case the
  element is a scalar.
* `CliffordAlgebra.exists_ι_of_mem_range_ι_pow_one`: in the odd base case it is a vector.
* `CliffordAlgebra.ι_range_pow_le_evenOdd`: the `n`-th power of the range of `ι` lies in the
  graded piece of degree `n`.
* `CliffordAlgebra.prod_map_ι_mem_evenOdd`: an ordered product of `n` generators is homogeneous
  of degree `n`, and `CliffordAlgebra.prod_map_ι_mem_evenOdd_zero_of_even_length` and
  `CliffordAlgebra.prod_map_ι_mem_evenOdd_one_of_odd_length` read that off in the even and the odd
  case.
* `CliffordAlgebra.involute_eq_uzpow_smul_of_mem_evenOdd`: the grade involution acts on the graded
  piece of parity `p` by `(-1) ^ p`.
* `CliffordAlgebra.involute_eq_self_iff` and `CliffordAlgebra.involute_eq_neg_iff`: with `2`
  invertible, the even and odd parts are the `±1`-eigenspaces of the grade involution.
* `Module.Basis.exteriorAlgebra_mem_evenOdd_card`: an exterior coordinate-basis vector is
  homogeneous of degree given by the cardinality of its index set, and
  `Module.Basis.exteriorAlgebra_mem_evenOdd_iff` says that this is the only degree it has.
* `Module.Basis.mem_evenOdd_iff_exteriorAlgebra_repr_eq_zero`: an exterior element is
  homogeneous of a given parity exactly when its coordinates vanish at every index set of the
  other parity.
-/



universe u v w

namespace CliffordAlgebra

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  {Q : QuadraticForm R M}

/-- An element of the `(0 : ZMod 2).val`-th power of the range of `ι` is a scalar. This is the
`i = 0` half of the `range_ι_pow` hypothesis of `CliffordAlgebra.evenOdd_induction`. -/
theorem exists_algebraMap_of_mem_range_ι_pow_zero {v : CliffordAlgebra Q}
    (hv : v ∈ LinearMap.range (ι Q) ^ (0 : ZMod 2).val) :
    ∃ r : R, algebraMap R (CliffordAlgebra Q) r = v :=
  Submodule.mem_one.mp (by simpa using hv)

/-- An element of the `(1 : ZMod 2).val`-th power of the range of `ι` is a vector. This is the
`i = 1` half of the `range_ι_pow` hypothesis of `CliffordAlgebra.evenOdd_induction`. -/
theorem exists_ι_of_mem_range_ι_pow_one {v : CliffordAlgebra Q}
    (hv : v ∈ LinearMap.range (ι Q) ^ (1 : ZMod 2).val) : ∃ a, ι Q a = v := by
  simpa [ZMod.val_one] using hv

/-- **The `n`-th power of the vectors is homogeneous of degree `n`** for the `ℤ/2` grading: it is
one of the summands defining `CliffordAlgebra.evenOdd Q n`. -/
theorem ι_range_pow_le_evenOdd (n : ℕ) :
    LinearMap.range (ι Q) ^ n ≤ evenOdd Q (n : ZMod 2) := by
  rw [evenOdd]
  exact le_iSup (fun j : {m : ℕ // (m : ZMod 2) = (n : ZMod 2)} => LinearMap.range (ι Q) ^ (j : ℕ))
    ⟨n, rfl⟩

/-- **An ordered product of `n` generators is homogeneous of degree `n`** for the `ℤ/2` grading. -/
theorem prod_map_ι_mem_evenOdd (l : List M) :
    (l.map (ι Q)).prod ∈ evenOdd Q (l.length : ZMod 2) := by
  simpa using SetLike.list_prod_map_mem_graded (A := evenOdd Q) l (fun _ => (1 : ZMod 2)) (ι Q)
    fun j _ => ι_mem_evenOdd_one Q j

/-- **The ordered product of an even number of vectors is even.** -/
theorem prod_map_ι_mem_evenOdd_zero_of_even_length {l : List M} (hlen : Even l.length) :
    (l.map (ι Q)).prod ∈ evenOdd Q 0 := by
  have h : (l.length : ZMod 2) = 0 := by
    rw [← ZMod.natCast_mod l.length 2, Nat.even_iff.mp hlen, Nat.cast_zero]
  exact h ▸ prod_map_ι_mem_evenOdd l

/-- **The ordered product of an odd number of vectors is odd.** -/
theorem prod_map_ι_mem_evenOdd_one_of_odd_length {l : List M} (hlen : Odd l.length) :
    (l.map (ι Q)).prod ∈ evenOdd Q 1 := by
  have h : (l.length : ZMod 2) = 1 := by
    rw [← ZMod.natCast_mod l.length 2, Nat.odd_iff.mp hlen, Nat.cast_one]
  exact h ▸ prod_map_ι_mem_evenOdd l

/-! ### The graded pieces as eigenspaces of the grade involution -/

section Involute

/-- Every Clifford element is the sum of an even and an odd element. -/
private theorem exists_add_eq (x : CliffordAlgebra Q) :
    ∃ e ∈ evenOdd Q 0, ∃ o ∈ evenOdd Q 1, e + o = x :=
  Submodule.mem_sup.mp ((evenOdd_isCompl Q).sup_eq_top ▸ Submodule.mem_top)

/-- **The grade involution acts on the graded piece of parity `p` by the sign `(-1) ^ p`.** -/
theorem involute_eq_uzpow_smul_of_mem_evenOdd {p : ZMod 2} {x : CliffordAlgebra Q}
    (hx : x ∈ evenOdd Q p) : involute x = ((-1 : ℤˣ) ^ p) • x := by
  obtain rfl | rfl : p = 0 ∨ p = 1 := by clear hx; revert p; decide
  · rw [involute_eq_of_mem_even hx, uzpow_zero, one_smul]
  · rw [involute_eq_of_mem_odd hx, uzpow_one, Units.neg_smul, one_smul]

variable [Invertible (2 : R)]

/-- **The even part is the fixed space of the grade involution** once `2` is invertible. Mathlib's
`CliffordAlgebra.involute_eq_of_mem_even` is the reverse implication. -/
theorem involute_eq_self_iff {x : CliffordAlgebra Q} : involute x = x ↔ x ∈ evenOdd Q 0 := by
  refine ⟨fun hx => ?_, involute_eq_of_mem_even⟩
  obtain ⟨e, he, o, ho, rfl⟩ := exists_add_eq x
  rw [map_add, involute_eq_of_mem_even he, involute_eq_of_mem_odd ho] at hx
  have h2 : (2 : R) • o = 0 := by linear_combination (norm := module) -hx
  simpa [(isUnit_of_invertible (2 : R)).smul_eq_zero.mp h2] using he

/-- **The odd part is the `-1`-eigenspace of the grade involution** once `2` is invertible.
Mathlib's `CliffordAlgebra.involute_eq_of_mem_odd` is the reverse implication. -/
theorem involute_eq_neg_iff {x : CliffordAlgebra Q} : involute x = -x ↔ x ∈ evenOdd Q 1 := by
  refine ⟨fun hx => ?_, involute_eq_of_mem_odd⟩
  obtain ⟨e, he, o, ho, rfl⟩ := exists_add_eq x
  rw [map_add, involute_eq_of_mem_even he, involute_eq_of_mem_odd ho] at hx
  have h2 : (2 : R) • e = 0 := by linear_combination (norm := module) hx
  simpa [(isUnit_of_invertible (2 : R)).smul_eq_zero.mp h2] using ho

end Involute

end CliffordAlgebra

namespace Module.Basis

variable {R : Type u} {M : Type v} {I : Type w} [CommRing R] [AddCommGroup M] [Module R M]
  [LinearOrder I]

/-- **An exterior coordinate-basis vector is homogeneous of degree its number of coordinates.** -/
@[simp] theorem exteriorAlgebra_mem_evenOdd_card (b : Module.Basis I R M) (s : Finset I) :
    b.ExteriorAlgebra s ∈
      CliffordAlgebra.evenOdd (0 : QuadraticForm R M) (s.card : ZMod 2) := by
  rw [CliffordAlgebra.evenOdd]
  refine Submodule.mem_iSup_of_mem ⟨s.card, rfl⟩ ?_
  have h := (b.exteriorPower s.card
    (⟨s, rfl⟩ : Set.powersetCard I s.card)).2
  rw [← ExteriorAlgebra.basis_eq_coe_basis] at h
  exact h

/-- **An exterior coordinate-basis vector is homogeneous of exactly one degree**: it lies in the
graded piece `i` precisely when `i` is the parity of its number of coordinates. -/
@[simp]
theorem exteriorAlgebra_mem_evenOdd_iff [Nontrivial R] (b : Module.Basis I R M) (s : Finset I)
    (i : ZMod 2) :
    b.ExteriorAlgebra s ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm R M) i ↔
      (s.card : ZMod 2) = i := by
  refine ⟨fun hmem => ?_, fun h => h ▸ b.exteriorAlgebra_mem_evenOdd_card s⟩
  by_contra hne
  have hcard := b.exteriorAlgebra_mem_evenOdd_card s
  have hpair : ∀ c d : ZMod 2, c ≠ d → (c = 0 ∧ d = 1) ∨ (c = 1 ∧ d = 0) := by decide
  have hsplit := hpair _ _ hne
  have hbot : b.ExteriorAlgebra s ∈
      CliffordAlgebra.evenOdd (0 : QuadraticForm R M) 0 ⊓
        CliffordAlgebra.evenOdd (0 : QuadraticForm R M) 1 := by
    rcases hsplit with ⟨hc, hi⟩ | ⟨hc, hi⟩
    · exact ⟨hc ▸ hcard, hi ▸ hmem⟩
    · exact ⟨hi ▸ hmem, hc ▸ hcard⟩
  rw [(CliffordAlgebra.evenOdd_isCompl (Q := (0 : QuadraticForm R M))).inf_eq_bot,
    Submodule.mem_bot] at hbot
  exact b.ExteriorAlgebra.ne_zero s hbot

/-- **An exterior element is homogeneous of parity `i` exactly when it has no coordinates of the
other parity**: its coordinate in the exterior coordinate basis vanishes at every index set whose
cardinality has the other parity. -/
theorem mem_evenOdd_iff_exteriorAlgebra_repr_eq_zero (b : Module.Basis I R M) {i : ZMod 2}
    {x : _root_.ExteriorAlgebra R M} :
    x ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm R M) i ↔
      ∀ t : Finset I, (t.card : ZMod 2) ≠ i → b.ExteriorAlgebra.repr x t = 0 := by
  classical
  have hsupp : ∀ (j : ZMod 2) (y : _root_.ExteriorAlgebra R M),
      (∀ t : Finset I, (t.card : ZMod 2) ≠ j → b.ExteriorAlgebra.repr y t = 0) →
        y ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm R M) j := by
    intro j y hy
    rw [← b.ExteriorAlgebra.linearCombination_repr y, Finsupp.linearCombination_apply]
    refine Submodule.sum_mem _ fun s hs ↦ Submodule.smul_mem _ _ ?_
    have hs' : (s.card : ZMod 2) = j := by_contra fun h ↦ Finsupp.mem_support_iff.1 hs (hy s h)
    exact hs' ▸ b.exteriorAlgebra_mem_evenOdd_card s
  refine ⟨fun hx t ht ↦ ?_, hsupp i x⟩
  -- `y` is the part of `x` of the parity opposite to `i`; it is homogeneous of both parities.
  let y := b.ExteriorAlgebra.repr.symm
    ((b.ExteriorAlgebra.repr x).filter fun s ↦ (s.card : ZMod 2) ≠ i)
  have hrepr (s : Finset I) : b.ExteriorAlgebra.repr y s =
      if (s.card : ZMod 2) ≠ i then b.ExteriorAlgebra.repr x s else 0 := by
    simp only [y, LinearEquiv.apply_symm_apply, Finsupp.filter_apply]
  have hflip : ∀ c d : ZMod 2, c ≠ d + 1 → c = d := by decide
  have hy₁ : y ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm R M) (i + 1) :=
    hsupp _ y fun s hs ↦ by rw [hrepr, ite_eq_right (not_not.2 (hflip _ _ hs))]
  have hy₀ : y ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm R M) i := by
    have hrest : x - y ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm R M) i :=
      hsupp i _ fun s hs ↦ by rw [map_sub, Finsupp.sub_apply, hrepr, ite_eq_left hs, sub_self]
    simpa using Submodule.sub_mem _ hx hrest
  have hdisj : Disjoint (CliffordAlgebra.evenOdd (0 : QuadraticForm R M) i)
      (CliffordAlgebra.evenOdd (0 : QuadraticForm R M) (i + 1)) := by
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) i with rfl | rfl
    · exact (CliffordAlgebra.evenOdd_isCompl (0 : QuadraticForm R M)).disjoint
    · exact (CliffordAlgebra.evenOdd_isCompl (0 : QuadraticForm R M)).disjoint.symm
  have hy : y = 0 := (Submodule.disjoint_def.1 hdisj) y hy₀ hy₁
  have hcoord := hrepr t
  rw [hy, ite_eq_left ht, map_zero, Finsupp.coe_zero, Pi.zero_apply] at hcoord
  exact hcoord.symm

end Module.Basis

end CheckedSource9

/-! ## Source: TauCeti.LinearAlgebra.CliffordAlgebra.Contraction -/
section CheckedSource10
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

-- Private: `CliffordAlgebra.exists_algebraMap_of_mem_range_ι_pow_zero` and
-- `CliffordAlgebra.exists_ι_of_mem_range_ι_pow_one` are used only inside a proof.

/-!
# Contraction against the `ℤ/2`-grading, and the change of form on right factors

Mathlib's `CliffordAlgebra.contractLeft` lowers the degree of a multivector by one, so it
exchanges the two halves of the `ℤ/2`-grading. Mathlib records neither half of that sentence:
`involute` interacts with products (`involute` is an algebra homomorphism) and with the grading,
but never with a contraction, and `evenOdd` is never related to `contractLeft` at all.

This file proves both. That a contraction carries `evenOdd Q i` into `evenOdd Q (i + 1)` is the
grading statement itself, and it is what makes an annihilation operator odd; anticommutation with
the grade involution is its operator shadow, and is what makes the grade involution usable as an
*even* operator alongside exterior multiplication and contraction — for instance because an
anisotropic vector orthogonal to a polarization acts on a spinor module by its scalar coordinate
times the grade involution. More precisely, contraction is a derivation twisted by the grade
involution, `d ⌋ (x * y) = (d ⌋ x) * y + involute x * (d ⌋ y)`, the graded Leibniz rule of an odd
operator.

The degree bookkeeping is in `ZMod 2`, where lowering and raising the degree by one are the same
map, so `evenOdd Q (i + 1)` and `evenOdd Q (i - 1)` are the same submodule; the statement below
names the first.

The parity statement is proved by induction over the grading; its base case is read off by
`CliffordAlgebra.exists_algebraMap_of_mem_range_ι_pow_zero` and
`CliffordAlgebra.exists_ι_of_mem_range_ι_pow_one`, which are general facts about the
grading and live with it.

Mathlib's `CliffordAlgebra.changeForm` is built by folding from the left, so Mathlib describes
it on left factors only (`CliffordAlgebra.changeForm_ι_mul`). The second half of this file supplies
the right-handed description `CliffordAlgebra.changeForm_mul_ι`, which rests on the graded
Leibniz rules for a contraction meeting a vector factor on the far side and on the commutation of
left with right contraction, left as a `TODO` in Mathlib. From it, `changeForm` commutes with
reversion when the bilinear form is symmetric; and since contraction anticommutes with the grade
involution, `changeForm` commutes with the grade involution for every bilinear form. In particular
`CliffordAlgebra.equivExterior` intertwines both operations with those of the exterior algebra.

## Main results

* `CliffordAlgebra.contractLeft_map`: contraction is natural under quadratic isometries.

* `CliffordAlgebra.contractLeft_mem_evenOdd`: **contraction shifts the parity**.
* `CliffordAlgebra.involute_contractLeft`: `involute (d ⌋ x) = -(d ⌋ involute x)`.
* `CliffordAlgebra.contractLeft_mul`: the graded Leibniz rule
  `d ⌋ (x * y) = (d ⌋ x) * y + involute x * (d ⌋ y)`.
* `CliffordAlgebra.contractLeft_mul_ι` and `CliffordAlgebra.contractRight_ι_mul`: the graded
  Leibniz rules for a vector factor on the far side.
* `CliffordAlgebra.contractRight_contractLeft`: `(d ⌋ x) ⌊ d' = d ⌋ (x ⌊ d')`.
* `CliffordAlgebra.contractLeft_prod_map_ι_eq_zero`: a contraction kills a product of vectors in
  its kernel.
* `CliffordAlgebra.changeForm_mul_ι`: `changeForm` on a right vector factor.
* `CliffordAlgebra.changeForm_involute` and `CliffordAlgebra.changeForm_reverse`: `changeForm`
  commutes with the grade involution, and with reversion for a symmetric form.
* `CliffordAlgebra.equivExterior_involute` and `CliffordAlgebra.equivExterior_reverse`: the same
  for the isomorphism with the exterior algebra.
* `CliffordAlgebra.equivExterior_mem_evenOdd_iff`: that isomorphism preserves the `ℤ/2`-grading.
* `CliffordAlgebra.equivExterior_ι_mul` and `CliffordAlgebra.equivExterior_mul_ι`: that
  isomorphism on left and right vector factors.
* `CliffordAlgebra.equivExterior_prod_map_ι_of_pairwise_isOrtho`: that isomorphism sends a product
  of pairwise orthogonal vectors to their exterior product.

## References

* [D. Grinberg, *The Clifford algebra and the Chevalley map*][grinberg_clifford_2016], for the
  contraction operators themselves.
-/



universe u v w

namespace CliffordAlgebra

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  {Q : QuadraticForm R M}

section Naturality

variable {M₁ : Type v} [AddCommGroup M₁] [Module R M₁]
  {M₂ : Type w} [AddCommGroup M₂] [Module R M₂]
  {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}

/-- Contraction against a linear functional commutes with the algebra map induced by a
quadratic isometry, after pulling back the functional. -/
theorem contractLeft_map (f : Q₁ →qᵢ Q₂) (d : Module.Dual R M₂)
    (x : CliffordAlgebra Q₁) :
    contractLeft d (map f x) = map f (contractLeft (d ∘ₗ f.toLinearMap) x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp only [AlgHom.commutes, contractLeft_algebraMap, map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x m hx =>
    simp only [map_mul, map_apply_ι, contractLeft_ι_mul, hx, map_sub,
      map_smul, LinearMap.comp_apply, QuadraticMap.Isometry.coe_toLinearMap]

end Naturality

/-- **The grade involution anticommutes with contraction.** Contracting against a linear
functional lowers the degree by one, hence swaps the even and odd parts of the Clifford algebra,
so it anticommutes with the operator that is `+1` on the even part and `-1` on the odd part. -/
@[simp, grind =]
theorem involute_contractLeft (d : Module.Dual R M) (x : CliffordAlgebra Q) :
    involute (contractLeft d x) = -contractLeft d (involute x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x y hx hy => simp only [map_add, hx, hy, neg_add]
  | ι_mul x a hx =>
    have hlhs : involute (contractLeft d (ι Q a * x))
        = d a • involute x - ι Q a * contractLeft d (involute x) := by
      rw [contractLeft_ι_mul, map_sub, map_smul, map_mul, involute_ι, hx, neg_mul_neg]
    have hrhs : involute (ι Q a * x) = -(ι Q a * involute x) := by
      rw [map_mul, involute_ι, neg_mul]
    rw [hlhs, hrhs, map_neg, neg_neg, contractLeft_ι_mul]

/-- **Contraction shifts the parity.** Contracting against a linear functional lowers the degree
of a multivector by one, so it carries the `i`-th half of the `ℤ/2`-grading into the other one. -/
theorem contractLeft_mem_evenOdd (d : Module.Dual R M) {i : ZMod 2} {x : CliffordAlgebra Q}
    (hx : x ∈ evenOdd Q i) : contractLeft d x ∈ evenOdd Q (i + 1) := by
  -- Two parity facts, used to keep the indices in `ZMod 2` honest.
  have hone : (1 : ZMod 2) + 1 = 0 := by decide
  have hshift : ∀ c : ZMod 2, (1 : ZMod 2) + (c + 1) = c := by decide
  induction x, hx using CliffordAlgebra.evenOdd_induction with
  | range_ι_pow v hv =>
    -- `i.val` is `0` or `1`, so `v` is a scalar or a vector.
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) i with rfl | rfl
    · obtain ⟨r, rfl⟩ := exists_algebraMap_of_mem_range_ι_pow_zero hv
      simp
    · obtain ⟨a, rfl⟩ := exists_ι_of_mem_range_ι_pow_one hv
      rw [contractLeft_ι, hone]
      exact SetLike.algebraMap_mem_graded _ _
  | add x y hx hy ihx ihy => simpa only [map_add] using add_mem ihx ihy
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
    have h₂ : ι Q m₂ * x ∈ evenOdd Q (i + 1) := by
      rw [add_comm]
      exact SetLike.mul_mem_graded (ι_mem_evenOdd_one Q m₂) hx
    have h₁ : contractLeft d (ι Q m₂ * x) ∈ evenOdd Q i := by
      rw [contractLeft_ι_mul]
      refine sub_mem (Submodule.smul_mem _ _ hx) ?_
      simpa only [hshift] using SetLike.mul_mem_graded (ι_mem_evenOdd_one Q m₂) ih
    rw [mul_assoc, contractLeft_ι_mul]
    refine sub_mem (Submodule.smul_mem _ _ h₂) ?_
    rw [add_comm]
    exact SetLike.mul_mem_graded (ι_mem_evenOdd_one Q m₁) h₁

/-- **The graded Leibniz rule for contraction.** Contraction against `d` is a derivation twisted
by the grade involution: `d ⌋ (x * y) = (d ⌋ x) * y + involute x * (d ⌋ y)`.  On a homogeneous
multivector `x` of degree `n` the involution is the sign `(-1) ^ n`, which gives the familiar
odd-derivation rule. -/
theorem contractLeft_mul (d : Module.Dual R M) (x y : CliffordAlgebra Q) :
    contractLeft d (x * y) = contractLeft d x * y + involute x * contractLeft d y := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [contractLeft_algebraMap_mul, contractLeft_algebraMap, zero_mul, zero_add,
      AlgHom.commutes]
  | add x x' hx hx' => simp only [add_mul, map_add, hx, hx']; abel
  | ι_mul x a hx =>
    rw [mul_assoc, contractLeft_ι_mul, hx, contractLeft_ι_mul, map_mul, involute_ι]
    simp only [mul_add, sub_mul, smul_mul_assoc, neg_mul, mul_assoc]
    abel

/-- **The graded Leibniz rule for a right vector factor.** Contraction against `d` passes through
a right factor `ι Q m`, at the cost of the term `d m • involute x` produced by contracting that
factor itself after it has moved past `x`. -/
theorem contractLeft_mul_ι (d : Module.Dual R M) (x : CliffordAlgebra Q) (m : M) :
    contractLeft d (x * ι Q m) = contractLeft d x * ι Q m + d m • involute x := by
  rw [contractLeft_mul, contractLeft_ι, ← Algebra.commutes, ← Algebra.smul_def]

/-- **The graded Leibniz rule for right contraction and a left vector factor**, the mirror image of
`CliffordAlgebra.contractLeft_mul_ι` under reversion: `(ι Q a * x) ⌊ d` is
`ι Q a * (x ⌊ d) + d a • involute x`. -/
theorem contractRight_ι_mul (d : Module.Dual R M) (a : M) (x : CliffordAlgebra Q) :
    contractRight (ι Q a * x) d = ι Q a * contractRight x d + d a • involute x := by
  simp [contractRight_eq, contractLeft_mul_ι, reverse_involute_commute.eq]

/-- **Left and right contraction commute**: `(d ⌋ x) ⌊ d' = d ⌋ (x ⌊ d')`. This is the statement
left as a `TODO` after `CliffordAlgebra.contractRight_comm` in Mathlib. -/
theorem contractRight_contractLeft (d d' : Module.Dual R M) (x : CliffordAlgebra Q) :
    contractRight (contractLeft d x) d' = contractLeft d (contractRight x d') := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | ι_mul x a hx =>
    simp [contractLeft_ι_mul, contractRight_ι_mul, hx, involute_contractLeft]
    abel

/-- Contraction against a functional `d` kills a product of vectors that `d` annihilates. -/
theorem contractLeft_prod_map_ι_eq_zero (d : Module.Dual R M) {l : List M}
    (h : ∀ m ∈ l, d m = 0) : contractLeft d (l.map (ι Q)).prod = 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, contractLeft_ι_mul, h a List.mem_cons_self, zero_smul,
      ih fun m hm ↦ h m (List.mem_cons_of_mem a hm), mul_zero, sub_zero]

section changeForm

variable {Q' : QuadraticForm R M} {B : LinearMap.BilinForm R M}
  (h : B.toQuadraticMap = Q' - Q)

/-- **`changeForm` and a right vector factor**: the right-handed counterpart of Mathlib's
`CliffordAlgebra.changeForm_ι_mul`, in which the correction term contracts from the right against
the functional `B.flip m = B · m`. No symmetry of `B` is needed. -/
theorem changeForm_mul_ι (x : CliffordAlgebra Q) (m : M) :
    changeForm h (x * ι Q m) =
      changeForm h x * ι Q' m - contractRight (changeForm h x) (B.flip m) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [Algebra.commutes, changeForm_ι_mul, changeForm_algebraMap, contractLeft_algebraMap,
      contractRight_algebraMap, sub_zero, sub_zero, Algebra.commutes]
  | add x y hx hy =>
    simp only [add_mul, map_add, hx, hy, LinearMap.add_apply]
    abel
  | ι_mul x a hx =>
    simp [mul_assoc, changeForm_ι_mul, hx, contractLeft_mul_ι, contractRight_contractLeft,
      contractRight_ι_mul, mul_sub, sub_mul]
    abel

/-- **`changeForm` commutes with the grade involution**, for every bilinear form `B`. -/
@[simp]
theorem changeForm_involute (x : CliffordAlgebra Q) :
    changeForm h (involute x) = involute (changeForm h x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x a hx =>
    simp [changeForm_ι_mul, hx, involute_contractLeft]
    abel

/-- **`changeForm` commutes with reversion** when the bilinear form `B` is symmetric. This covers
`CliffordAlgebra.equivExterior`, whose bilinear form is the symmetric
`QuadraticMap.associated (-Q)`. -/
theorem changeForm_reverse (hB : B.IsSymm) (x : CliffordAlgebra Q) :
    changeForm h (reverse x) = reverse (changeForm h x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x a hx =>
    have hflip : B.flip=B := by
      ext x y
      exact hB.eq y x
    simp [changeForm_mul_ι,hx,changeForm_ι_mul,contractRight_eq,hflip]

end changeForm

section equivExterior

variable [Invertible (2 : R)] (Q)

/-- `CliffordAlgebra.equivExterior` on a left vector factor: the specialization of Mathlib's
`CliffordAlgebra.changeForm_ι_mul` to the bilinear form `QuadraticMap.associated (-Q)`.

Not a `simp` lemma, for the same reason as `CliffordAlgebra.equivExterior_involute`. -/
theorem equivExterior_ι_mul (m : M) (x : CliffordAlgebra Q) :
    equivExterior Q (ι Q m * x) =
      ExteriorAlgebra.ι R m * equivExterior Q x -
        contractLeft (QuadraticMap.associated (-Q) m) (equivExterior Q x) :=
  changeForm_ι_mul changeForm.associated_neg_proof m x

/-- `CliffordAlgebra.equivExterior` on a right vector factor: the specialization of
`CliffordAlgebra.changeForm_mul_ι` to the symmetric bilinear form `QuadraticMap.associated (-Q)`.

Not a `simp` lemma, for the same reason as `CliffordAlgebra.equivExterior_involute`. -/
theorem equivExterior_mul_ι (x : CliffordAlgebra Q) (m : M) :
    equivExterior Q (x * ι Q m) =
      equivExterior Q x * ExteriorAlgebra.ι R m -
        contractRight (equivExterior Q x) (QuadraticMap.associated (-Q) m) := by
  rw [← QuadraticMap.associated_flip]
  exact changeForm_mul_ι changeForm.associated_neg_proof x m

/-- `CliffordAlgebra.equivExterior` intertwines the grade involutions.

Not a `simp` lemma: `simp` unfolds `CliffordAlgebra.equivExterior` to the underlying
`CliffordAlgebra.changeForm`, where `CliffordAlgebra.changeForm_involute` applies. -/
theorem equivExterior_involute (x : CliffordAlgebra Q) :
    equivExterior Q (involute x) = involute (equivExterior Q x) :=
  changeForm_involute changeForm.associated_neg_proof x

/-- **`CliffordAlgebra.equivExterior` preserves the `ℤ/2`-grading**: a Clifford element has
parity `i` exactly when its image in the exterior algebra has parity `i`. -/
theorem equivExterior_mem_evenOdd_iff {i : ZMod 2} {x : CliffordAlgebra Q} :
    equivExterior Q x ∈ evenOdd (0 : QuadraticForm R M) i ↔ x ∈ evenOdd Q i := by
  obtain rfl | rfl : i = 0 ∨ i = 1 := by revert i; decide
  · rw [← involute_eq_self_iff, ← involute_eq_self_iff, ← equivExterior_involute,
      (equivExterior Q).injective.eq_iff]
  · rw [← involute_eq_neg_iff, ← involute_eq_neg_iff, ← equivExterior_involute, ← map_neg,
      (equivExterior Q).injective.eq_iff]

/-- `CliffordAlgebra.equivExterior` intertwines reversion, because the bilinear form
`QuadraticMap.associated (-Q)` it changes the form by is symmetric.

Not a `simp` lemma, for the same reason as `CliffordAlgebra.equivExterior_involute`. -/
theorem equivExterior_reverse (x : CliffordAlgebra Q) :
    equivExterior Q (reverse x) = reverse (equivExterior Q x) :=
  changeForm_reverse changeForm.associated_neg_proof ⟨(QuadraticForm.associated_isSymm R (-Q)).eq⟩ x

/-- **`CliffordAlgebra.equivExterior` sends a product of pairwise orthogonal vectors to their
exterior product.** Each correction term of `CliffordAlgebra.equivExterior_ι_mul` contracts the
later factors against the first, and vanishes by orthogonality. No hypothesis on `Q` is needed;
in particular `Q` may be degenerate. -/
theorem equivExterior_prod_map_ι_of_pairwise_isOrtho {l : List M} (hl : l.Pairwise Q.IsOrtho) :
    equivExterior Q (l.map (ι Q)).prod = (l.map (ExteriorAlgebra.ι R)).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.pairwise_cons] at hl
    rw [List.map_cons, List.prod_cons, equivExterior_ι_mul, ih hl.2,
      contractLeft_prod_map_ι_eq_zero, sub_zero, List.map_cons, List.prod_cons]
    intro m hm
    simp [hl.1 m hm]

end equivExterior

end CliffordAlgebra

end CheckedSource10

/-! ## Source: TauCeti.LinearAlgebra.ExteriorPower.Basic -/
section CheckedSource11
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Further results on exterior powers

This file records that the `d`th exterior power of a finite free module over a commutative ring
vanishes as soon as `d` exceeds the rank of the module, and that exterior powers of projective
modules are projective.

It then builds the surjection `exteriorPower.fromTensorPower : ⨂[R]^n M →ₗ[R] ⋀[R]^n M` that is
left inverse, up to the factor `n!`, to Mathlib's antisymmetrization
`exteriorPower.toTensorPower`: composing the antisymmetrization with it is `n! • id` on the exterior
power, while composing the two the other way round is the antisymmetrization operator
`∑_σ sgn(σ) σ` on the tensor power. Consequently the antisymmetrization is injective once `n!` is a
unit in the base ring, and its image is the image of that operator. That is the statement a Young
symmetrizer of a one-column shape consumes.

Finally, it describes images of exterior powers under induced maps: inside the exterior algebra,
the image of `⋀ⁿ M` under `f` is the `n`th power of the degree-one image of `f`, and over a field an
injective map embeds `⋀ⁿ V` with its binomial dimension.

## Main definitions

* `exteriorPower.fromTensorPower` is the canonical surjection of the tensor power onto the
  exterior power.
## Main results

* `exteriorPower.eq_zero_of_finrank_lt` states that every element of `⋀[R]^d M` is zero when
  `Module.finrank R M < d`.
* `exteriorPower.instProjective`: exterior powers of projective modules are projective.
* `exteriorPower.fromTensorPower_comp_toTensorPower`: antisymmetrizing and projecting back is
  multiplication by `n!`, whence `exteriorPower.toTensorPower_injective`.
* `exteriorPower.ιMulti_ne_zero_iff`: over a field, an exterior product of vectors is nonzero
  exactly when the vectors are linearly independent.
* `exteriorPower.toTensorPower_injective_of_free`: antisymmetrization is injective for free
  modules in every characteristic, without factorial invertibility.
* `exteriorPower.range_toTensorPower`: the image of the antisymmetrization is the image of the
  antisymmetrization operator on the tensor power.
* `exteriorPower.map_bijective`: a bijective linear map induces bijections of exterior powers.
* `exteriorPower.toTensorPower_comp_map` and `exteriorPower.map_comp_fromTensorPower`: the
  antisymmetrization and the canonical surjection are natural in the module.
* `TauCeti.ExteriorAlgebra.exteriorPower_map_map`: the image of `⋀ⁿ M` in the exterior algebra
  under the map induced by `f` is the `n`th power of the degree-one image of `f`.
* `TauCeti.ExteriorAlgebra.ι_mem_exteriorPower_one` and
  `TauCeti.ExteriorAlgebra.ι_ιInv_of_mem_exteriorPower_one`: the first exterior power consists of
  the vectors, and `ExteriorAlgebra.ιInv` recovers the vector from its image.
* `TauCeti.ExteriorAlgebra.ι_mul_mem_exteriorPower` and `TauCeti.ExteriorAlgebra.wedgeLeft`:
  left multiplication by a vector carries `⋀ⁿ M` into `⋀ⁿ⁺¹ M`, packaged as the linear map
  `v ↦ m ∧ v` with values in degree `n + 1`.
* `TauCeti.exteriorPower.finrank_range_map`: over a field, the image of `⋀ⁿ V` under the map
  induced by an injective linear map has dimension `(dim V).choose n`.
* `TauCeti.exteriorPower.mem_span_range_iff_ι_mul_ιMulti_eq_zero`: over a field, a vector lies in
  the span of a linearly independent family exactly when its product with the exterior product of
  the family vanishes.

## References

The results use Mathlib's exterior-power basis and dimension formula from
`Mathlib.LinearAlgebra.ExteriorPower.Basis`, by Sophie Morel and Daniel Morrison.
-/


open scoped BigOperators TensorProduct

universe u w

variable {R : Type u} {M : Type w}

namespace exteriorPower

section Vanishing

variable [CommRing R] [AddCommGroup M] [Module R M]
variable [Module.Free R M] [Module.Finite R M]

/-- An exterior power above the rank of a finite free module is zero. -/
theorem eq_zero_of_finrank_lt (d : ℕ) (h : Module.finrank R M < d) (x : ⋀[R]^d M) :
    x = 0 := by
  have : Subsingleton (⋀[R]^d M) := by
    rcases subsingleton_or_nontrivial R with _ | _
    · exact Module.subsingleton R _
    · rw [← Module.finrank_eq_zero_iff_of_free R, finrank_eq, Nat.choose_eq_zero_iff]
      exact h
  exact Subsingleton.elim x 0

end Vanishing

/-! ### Antisymmetrization of free modules -/

section Free

variable [CommRing R] [AddCommGroup M] [Module R M]

/-- Pairing with a pure exterior product of linear forms factors through the
antisymmetrization into the tensor power. -/
theorem pairingDual_ιMulti_apply {n : ℕ} (g : Fin n → Module.Dual R M) (x : ⋀[R]^n M) :
    pairingDual R M n (ιMulti R n g) x =
      TensorPower.multilinearMapToDual R M n g (toTensorPower R M n x) := by
  simp [pairingDual, alternatingMapToDual]

/-- Antisymmetrization embeds every exterior power of a free module into its tensor power,
over any commutative ring, without requiring the factorial to be invertible. -/
theorem toTensorPower_injective_of_free [Module.Free R M] {n : ℕ} :
    Function.Injective (toTensorPower R M n) := by
  classical
  let : LinearOrder (Module.Free.ChooseBasisIndex R M) := linearOrderOfSTO WellOrderingRel
  let b := Module.Free.chooseBasis R M
  -- Each exterior-basis coordinate factors through antisymmetrization.
  intro x y h
  apply (b.exteriorPower n).repr.injective
  ext s
  rw [basis_repr_apply, basis_repr_apply]
  simp only [ιMultiDual, ιMulti_family, pairingDual_ιMulti_apply, h]

end Free

/-! ### Projectivity -/

section Projective

variable [CommRing R] [AddCommGroup M] [Module R M]

/-- Exterior powers of a projective module are projective: `⋀[R]^n M` is a direct summand of the
exterior power of the free module `M →₀ R`. -/
instance instProjective [Module.Projective R M] (n : ℕ) : Module.Projective R (⋀[R]^n M) := by
  obtain ⟨s, hs⟩ := Module.projective_def'.mp ‹Module.Projective R M›
  refine .of_split (map n s) (map n (Finsupp.linearCombination R id)) ?_
  rw [← map_comp, hs, map_id]

end Projective

/-! ### The exterior power as a quotient of the tensor power -/

section FromTensorPower

variable [CommRing R] [AddCommGroup M] [Module R M] (n : ℕ)

variable (R M) in
/-- **The canonical surjection of the tensor power onto the exterior power**, sending a pure
tensor to the corresponding exterior product.

Mathlib's `exteriorPower.toTensorPower` runs the other way, by antisymmetrization; antisymmetrizing
and then projecting back is `n!` on the exterior power, while projecting and then antisymmetrizing
is the antisymmetrization operator `∑_σ sgn(σ) σ` on the tensor power. -/
noncomputable def fromTensorPower : (⨂[R]^n M) →ₗ[R] ⋀[R]^n M :=
  PiTensorProduct.lift (ιMulti R n).toMultilinearMap

@[simp]
theorem fromTensorPower_tprod (m : Fin n → M) :
    fromTensorPower R M n (PiTensorProduct.tprod R m) = ιMulti R n m :=
  PiTensorProduct.lift.tprod m

theorem fromTensorPower_surjective : Function.Surjective (fromTensorPower R M n) := by
  rw [← LinearMap.range_eq_top, ← top_le_iff, ← ιMulti_span R n M, Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  exact ⟨PiTensorProduct.tprod R v, fromTensorPower_tprod n v⟩

/-- Antisymmetrizing an exterior product and projecting it back multiplies by `n!`: each of the
`n!` signed reorderings returns the same exterior product. -/
@[simp]
theorem fromTensorPower_comp_toTensorPower :
    (fromTensorPower R M n) ∘ₗ (toTensorPower R M n) =
      n.factorial • LinearMap.id (R := R) (M := ⋀[R]^n M) := by
  refine LinearMap.ext_on (ιMulti_span R n M) ?_
  rintro _ ⟨v, rfl⟩
  have hsq : ∀ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign σ : ℤ)) * ((Equiv.Perm.sign σ : ℤ)) = 1 := fun σ => by
    rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
  have h : ∀ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign σ : ℤ)) • ιMulti R n (fun i => v (σ i)) = ιMulti R n v := fun σ => by
    rw [← Function.comp_def v σ, (ιMulti R n).map_perm v σ, Units.smul_def, smul_smul, hsq, one_smul]
  rw [LinearMap.coe_comp, Function.comp_apply, toTensorPower_apply_ιMulti, map_sum]
  simp only [Units.smul_def, map_zsmul, fromTensorPower_tprod, h]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    LinearMap.smul_apply, LinearMap.id_apply]

/-- The antisymmetrization is injective as soon as `n!` is a unit in the base ring, for instance
over a `ℚ`-algebra. -/
theorem toTensorPower_injective (h : IsUnit (n.factorial : R)) :
    Function.Injective (toTensorPower R M n) := by
  obtain ⟨u, hu⟩ := h
  -- Rescaling the canonical surjection by `u⁻¹` makes it a left inverse of the antisymmetrization.
  refine LinearMap.injective_of_comp_eq_id _ (((u⁻¹ : Rˣ) : R) • fromTensorPower R M n) ?_
  rw [LinearMap.smul_comp, fromTensorPower_comp_toTensorPower, ← Nat.cast_smul_eq_nsmul R,
    smul_smul, ← hu, u.inv_mul, one_smul]

/-- Projecting a tensor to the exterior power and antisymmetrizing it back is the
antisymmetrization operator `∑_σ sgn(σ) σ` of the tensor power. -/
theorem toTensorPower_comp_fromTensorPower :
    (toTensorPower R M n) ∘ₗ (fromTensorPower R M n) =
      ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) •
        (PiTensorProduct.reindex R (fun _ : Fin n => M) σ).toLinearMap := by
  refine PiTensorProduct.ext (MultilinearMap.ext fun m => ?_)
  rw [LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply,
    LinearMap.coe_comp, Function.comp_apply, fromTensorPower_tprod,
    toTensorPower_apply_ιMulti, LinearMap.sum_apply]
  refine Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin n))) _ _ fun σ => ?_
  simp [Units.smul_def, Equiv.Perm.inv_def]

/-- The antisymmetrization is natural in the module. -/
theorem toTensorPower_comp_map {N : Type*} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) :
    (toTensorPower R N n) ∘ₗ (map n f) =
      (PiTensorProduct.map fun _ : Fin n => f) ∘ₗ (toTensorPower R M n) := by
  refine LinearMap.ext_on (ιMulti_span R n M) ?_
  rintro _ ⟨v, rfl⟩
  simp [Units.smul_def, Function.comp_def]

/-- The canonical surjection is natural in the module. -/
theorem map_comp_fromTensorPower {N : Type*} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) :
    (map n f) ∘ₗ (fromTensorPower R M n) =
      (fromTensorPower R N n) ∘ₗ (PiTensorProduct.map fun _ : Fin n => f) := by
  refine PiTensorProduct.ext (MultilinearMap.ext fun m => ?_)
  simp [Function.comp_def]

/-- The image of the antisymmetrization is the image of the antisymmetrization operator
`∑_σ sgn(σ) σ` on the tensor power. -/
theorem range_toTensorPower :
    LinearMap.range (toTensorPower R M n) =
      LinearMap.range (∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) •
        (PiTensorProduct.reindex R (fun _ : Fin n => M) σ).toLinearMap) := by
  rw [← toTensorPower_comp_fromTensorPower, LinearMap.range_comp,
    LinearMap.range_eq_top.mpr (fromTensorPower_surjective n), Submodule.map_top]

end FromTensorPower

/-! ### Exterior products over a field -/

section Field

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-- Over a field, the exterior product of `n` vectors is nonzero exactly when they are linearly
independent. -/
theorem ιMulti_ne_zero_iff {n : ℕ} (v : Fin n → V) :
    ιMulti K n v ≠ 0 ↔ LinearIndependent K v := by
  refine ⟨fun h ↦ by_contra fun hv ↦ h ((ιMulti K n).map_linearDependent v hv), fun hv ↦ ?_⟩
  -- The only `n`-element subset of `Fin n` is enumerated by the identity.
  have hs : (Finset.univ : Finset (Fin n)).card = n := by simp
  have he : ⇑(Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard hs)) = id := by
    rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
    exact (Finset.orderEmbOfFin_unique hs (fun _ ↦ Finset.mem_univ _) strictMono_id).symm
  simpa [ιMulti_family, he] using (ιMulti_family_linearIndependent_field (n := n) hv).ne_zero
    (Set.powersetCard.ofCard hs)

end Field

/-! ### Bijectivity of induced maps -/

section Bijective

variable [CommRing R] [AddCommGroup M] [Module R M] {N : Type*} [AddCommGroup N] [Module R N]

/-- A bijective linear map induces a bijective map on every exterior power. -/
theorem map_bijective {n : ℕ} {f : M →ₗ[R] N} (hf : Function.Bijective f) :
    Function.Bijective (map n f) :=
  ⟨map_injective (LinearEquiv.ofBijective f hf).symm.toLinearMap (by ext; simp),
    map_surjective hf.2⟩

end Bijective

end exteriorPower

namespace TauCeti

namespace ExteriorAlgebra

variable [CommRing R] [AddCommGroup M] [Module R M] {N : Type*} [AddCommGroup N] [Module R N]

/-- Inside the exterior algebra, the image of the `n`th exterior power under the map induced by
`f` is the `n`th power of the degree-one image of the range of `f`. -/
theorem exteriorPower_map_map (n : ℕ) (f : M →ₗ[R] N) :
    (⋀[R]^n M).map (_root_.ExteriorAlgebra.map f).toLinearMap =
      ((LinearMap.range f).map (_root_.ExteriorAlgebra.ι R)) ^ n := by
  rw [_root_.ExteriorAlgebra.exteriorPower, Submodule.map_pow,
    _root_.ExteriorAlgebra.ι_range_map_map]

/-- A vector lies in the first exterior power. -/
theorem ι_mem_exteriorPower_one (m : M) : _root_.ExteriorAlgebra.ι R m ∈ ⋀[R]^1 M := by
  rw [_root_.ExteriorAlgebra.exteriorPower, pow_one]
  exact LinearMap.mem_range_self _ m

/-- An element of the first exterior power is the vector `ExteriorAlgebra.ιInv` reads off from
it. -/
theorem ι_ιInv_of_mem_exteriorPower_one {x : _root_.ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^1 M) :
    _root_.ExteriorAlgebra.ι R (_root_.ExteriorAlgebra.ιInv x) = x := by
  rw [_root_.ExteriorAlgebra.exteriorPower, pow_one] at hx
  obtain ⟨m, rfl⟩ := hx
  rw [_root_.ExteriorAlgebra.ι_leftInverse]

/-- Left multiplication by a vector raises the exterior degree by one: it carries the `n`-th
exterior power into the `(n + 1)`-th. -/
theorem ι_mul_mem_exteriorPower (m : M) {n : ℕ} {x : _root_.ExteriorAlgebra R M}
    (hx : x ∈ ⋀[R]^n M) :
    _root_.ExteriorAlgebra.ι R m * x ∈ ⋀[R]^(n + 1) M := by
  rw [_root_.ExteriorAlgebra.exteriorPower, pow_succ']
  exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ m) hx

/-- Exterior multiplication `v ↦ m ∧ v` by a vector `m`, from the `n`-th exterior power to the
`(n + 1)`-th. Mathlib's `exteriorPower.wedge R M 1 n` is the same product with values in degree
`1 + n`, which is not definitionally `n + 1`; this form composes with maps out of `⋀ⁿ⁺¹ M`. -/
def wedgeLeft (m : M) (n : ℕ) : ⋀[R]^n M →ₗ[R] ⋀[R]^(n + 1) M :=
  (LinearMap.mulLeft R (_root_.ExteriorAlgebra.ι R m)).restrict fun _ hx ↦
    ι_mul_mem_exteriorPower m hx

/-- `wedgeLeft m n` is left multiplication by `ι R m` in the exterior algebra. -/
@[simp]
theorem coe_wedgeLeft_apply (m : M) (n : ℕ) (x : ⋀[R]^n M) :
    (wedgeLeft m n x : _root_.ExteriorAlgebra R M) = _root_.ExteriorAlgebra.ι R m * x :=
  (rfl)

/-- `wedgeLeft m n` prepends `m` to a wedge product of vectors: `m ∧ (v₀ ∧ ⋯ ∧ vₙ₋₁)`. -/
@[simp]
theorem wedgeLeft_ιMulti (m : M) (n : ℕ) (v : Fin n → M) :
    wedgeLeft m n (exteriorPower.ιMulti R n v) = exteriorPower.ιMulti R (n + 1) (Fin.cons m v) := by
  ext
  simp [_root_.ExteriorAlgebra.ιMulti_succ_apply, Matrix.vecTail]

end ExteriorAlgebra

namespace exteriorPower

variable {K : Type*} [Field K] {V W : Type*} [AddCommGroup V] [Module K V] [Module.Finite K V]
  [AddCommGroup W] [Module K W]

/-- Over a field, the image of the `n`th exterior power of a finite-dimensional space under the
map induced by an injective linear map has dimension `(dim V).choose n`. -/
theorem finrank_range_map {f : V →ₗ[K] W} (hf : Function.Injective f) (n : ℕ) :
    Module.finrank K (LinearMap.range (_root_.exteriorPower.map n f)) =
      (Module.finrank K V).choose n := by
  rw [LinearMap.finrank_range_of_inj (_root_.exteriorPower.map_injective_field hf),
    _root_.exteriorPower.finrank_eq]

omit [Module.Finite K V] in
/-- Over a field, a vector lies in the span of a linearly independent family of `n` vectors exactly
when its product with the exterior product of the family vanishes in the exterior algebra. -/
theorem mem_span_range_iff_ι_mul_ιMulti_eq_zero {n : ℕ} {v : Fin n → V}
    (hv : LinearIndependent K v) (w : V) :
    w ∈ Submodule.span K (Set.range v) ↔
      _root_.ExteriorAlgebra.ι K w * (_root_.exteriorPower.ιMulti K n v : ExteriorAlgebra K V) =
        0 := by
  have hcons : w ∈ Submodule.span K (Set.range v) ↔
      ¬LinearIndependent K (Fin.cons w v : Fin (n + 1) → V) := by
    rw [linearIndependent_finCons]
    tauto
  rw [hcons, ← _root_.exteriorPower.ιMulti_ne_zero_iff, not_not, ← ZeroMemClass.coe_eq_zero,
    _root_.exteriorPower.ιMulti_apply_coe, _root_.ExteriorAlgebra.ιMulti_succ_apply,
    _root_.exteriorPower.ιMulti_apply_coe]
  simp [Matrix.vecTail, Function.comp_def]

end exteriorPower

end TauCeti

end CheckedSource11

/-! ## Source: TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction -/
section CheckedSource12
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Coordinate projections on an exterior algebra

Left multiplication by a basis vector after contraction by its dual coordinate is the projection
onto the exterior basis vectors containing that coordinate. This is the occupation-number
projection used by both scalar detection in Clifford algebras and the matrix-unit construction
from creation and annihilation operators.

Each of the two halves acts on an exterior basis vector by a single coordinate move, up to the
shuffle sign that carries the moved coordinate to the front: contraction erases the coordinate
from the index set, and left multiplication inserts it, each vanishing when the index set is on
the wrong side of that move. Creation after contraction at distinct coordinates therefore
replaces an occupied coordinate with an unoccupied one, with the product of their shuffle signs.

The grade involution is diagonal for the exterior basis as well: it multiplies an exterior
monomial, and so the basis vector indexed by `s`, by the parity of its degree.

Every basis vector is the product of the exterior-algebra generators of its index set, in
increasing order; for index sets with one or two elements this is also recorded in the explicit
forms `TauCeti.ExteriorAlgebra.basis_singleton` and `TauCeti.ExteriorAlgebra.basis_pair`.

Independently of a basis, `ExteriorAlgebra.contractLeft_map` states naturality under a linear
map: pull back the contracting functional and then map the contracted element. This follows
from the general quadratic-isometry statement `CliffordAlgebra.contractLeft_map`.

Independently of a basis, the grade involution is the sign `(-1) ^ n` on the `n`-th exterior power,
a contraction carries the `(n + 1)`-th exterior power into the `n`-th, and a vector graded-commutes
with every multivector: `ι m * x = involute x * ι m`.  Together with the graded Leibniz rule
`CliffordAlgebra.contractLeft_mul`, these say that a contraction is an odd derivation of degree
`-1` of the graded-commutative exterior algebra. On a wedge product of vectors it is the alternating
sum of deletions (`TauCeti.ExteriorAlgebra.contractLeft_ιMulti`); this is the differential of the
Koszul complex.

In degree at least the rank, contraction loses no information: if `d m = 1` and
`finrank R M ≤ n`, every `x ∈ ⋀ⁿ M` is `m ∧ (d ⌋ x)`. Hence two forms killed by `d` multiply to
zero once their degrees add up to the rank, and in rank at most four a two-form `x` satisfies
`x ∧ x = 2 x ∧ m ∧ (d ⌋ x)`. This is the algebra behind the splitting of a two-form on a product
`ℝ × Y` along the unit normal of the factor `Y`.

On `M × R`, with `e = (0, 1)`, every element `z` of the exterior algebra splits as `a + e ∧ b`,
where `a` and `b` are the images in `⋀ M` of `z` and of its contraction by the second coordinate
(`ExteriorAlgebra.map_inl_map_fst_add_ι_inr_mul_contractLeft_snd`). This is the
decomposition `⋀ᵏ⁺¹ (M × R) ≅ ⋀ᵏ⁺¹ M ⊕ e ∧ ⋀ᵏ M` used to adjoin one element to a Koszul complex.
In this splitting, the contraction by `φ + x · snd` acts as `d(a + e ∧ b) = (d a + x b) - e ∧ d b`
(`ExteriorAlgebra.map_fst_contractLeft_coprod`,
`ExteriorAlgebra.contractLeft_map_fst_contractLeft_snd`).
-/


open CliffordAlgebra

namespace TauCeti.ExteriorAlgebra

universe u v w

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

/-- **An exterior-basis vector is the product of its generators in increasing order**: the basis
vector indexed by `s` is `ι (b i₁) * ⋯ * ι (b iₖ)` for `s.sort = [i₁, …, iₖ]`. -/
theorem _root_.Module.Basis.exteriorAlgebra_eq_prod_map_sort {I : Type w} [LinearOrder I]
    (b : Module.Basis I R M) (s : Finset I) :
    b.ExteriorAlgebra s = ((s.sort.map b).map (ExteriorAlgebra.ι R)).prod := by
  rw [ExteriorAlgebra.basis_apply_ofCard b rfl, ExteriorAlgebra.ιMulti_family,
    ExteriorAlgebra.ιMulti_apply]
  congr 1
  refine List.ext_getElem (by simp) fun n _ _ ↦ ?_
  simp only [List.getElem_ofFn, Function.comp_apply, List.getElem_map,
    Set.powersetCard.ofFinEmbEquiv_symm_apply, Set.powersetCard.ofCard]
  exact congrArg (fun i ↦ ExteriorAlgebra.ι R (b i)) (Finset.orderEmbOfFin_apply _ _ _)

/-- Contracting an exterior-basis vector by a coordinate not in its index set gives zero. -/
@[simp]
private theorem contractLeft_coord_basis_eq_zero_of_not_mem {I : Type w} [LinearOrder I]
    (b : Module.Basis I R M) (i : I) (s : Finset I) (hi : i ∉ s) :
    contractLeft (Q := (0 : QuadraticForm R M)) (b.coord i) (b.ExteriorAlgebra s) = 0 := by
  rw [b.exteriorAlgebra_eq_prod_map_sort]
  refine contractLeft_prod_map_ι_eq_zero _ fun m hm ↦ ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hm
  rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply,
    ite_eq_right_iff]
  rintro rfl
  exact absurd ((Finset.mem_sort _).mp hj) hi

/-- **The grade involution acts on an exterior monomial by the parity of its degree.** The
monomial is the product of its `n` generators, each of which the involution negates. -/
@[simp]
theorem involute_ιMulti {n : ℕ} (v : Fin n → M) :
    CliffordAlgebra.involute (Q := (0 : QuadraticForm R M)) (ExteriorAlgebra.ιMulti R n v) =
      (-1 : R) ^ n • ExteriorAlgebra.ιMulti R n v := by
  -- Every exterior monomial is the product of the list of its generators.
  have h : ExteriorAlgebra.ιMulti R n v =
      ((List.ofFn v).map (CliffordAlgebra.ι (0 : QuadraticForm R M))).prod := by
    rw [ExteriorAlgebra.ιMulti_apply, List.map_ofFn]
    rfl
  rw [h, CliffordAlgebra.involute_prod_map_ι, List.length_ofFn]

/-- **The grade involution acts on an exterior-basis vector by the parity of its index set.** The
basis vector indexed by `s` is the monomial on `s.card` generators. -/
@[simp]
theorem involute_basis {I : Type w} [LinearOrder I]
    (b : Module.Basis I R M) (s : Finset I) :
    CliffordAlgebra.involute (Q := (0 : QuadraticForm R M)) (b.ExteriorAlgebra s) =
      (-1 : R) ^ s.card • b.ExteriorAlgebra s := by
  rw [ExteriorAlgebra.basis_apply]
  exact involute_ιMulti _

def basisEraseSignOfErase {I : Type w} [LinearOrder I]
    (i : I) (t : Finset I) (hi : i ∉ t) : ℤˣ :=
  let u : Set.powersetCard I 1 := ⟨{i}, Finset.card_singleton i⟩
  let t' : Set.powersetCard I t.card := ⟨t, rfl⟩
  (Set.powersetCard.permOfDisjoint (s := u) (t := t') (by simp [u, t', hi])).sign

/-- The shuffle sign for the singleton basis vector indexed by `i` followed by the basis vector
indexed by `s.erase i`. When `i ∈ s`, this is the sign of moving `i` to the front of `s`. -/
def basisEraseSign {I : Type w} [LinearOrder I] (i : I) (s : Finset I) : ℤˣ :=
  basisEraseSignOfErase i (s.erase i) (by simp)

private theorem basisEraseSign_eq_neg_one_pow_card_filter_lt_of_mem
    {I : Type w} [LinearOrder I]
    (i : I) (s : Finset I) (hi : i ∈ s) :
    basisEraseSign i s = (-1 : ℤˣ) ^ (s.filter (fun j ↦ j < i)).card := by
  classical
  let n := (s.erase i).card
  have hsCard : s.card = n + 1 := by
    simpa [n] using (Finset.card_erase_add_one hi).symm
  -- Enumerate `s` in increasing order. The position `k` of `i` counts precisely the entries
  -- which the shuffle crosses when it moves the singleton `{i}` to the front.
  let e : Fin (n + 1) ↪o I := s.orderEmbOfFin hsCard
  let k : Fin (n + 1) := (s.orderIsoOfFin hsCard).symm ⟨i, hi⟩
  have hek : e k = i := by
    exact congrArg Subtype.val ((s.orderIsoOfFin hsCard).apply_symm_apply ⟨i, hi⟩)
  have hremove : k.removeNth (fun j ↦ e j) =
      (s.erase i).orderEmbOfFin (show (s.erase i).card = n from rfl) := by
    apply Finset.orderEmbOfFin_unique
    · intro j
      exact Finset.mem_erase.mpr ⟨fun h ↦ k.succAbove_ne j (e.injective (h.trans hek.symm)),
        Finset.orderEmbOfFin_mem s hsCard _⟩
    · exact e.strictMono.comp (Fin.strictMono_succAbove k)
  let u : Set.powersetCard I 1 := ⟨{i}, Finset.card_singleton i⟩
  let t : Set.powersetCard I n := ⟨s.erase i, rfl⟩
  have hdisj : Disjoint u.val t.val := by simp [u, t]
  have hsCard' : s.card = 1 + n := hsCard.trans (Nat.add_comm n 1)
  have hunion : Set.powersetCard.disjUnion hdisj =
      (Set.powersetCard.ofCard (s := s) hsCard' : Set.powersetCard I (1 + n)) := by
    apply Subtype.ext
    simp [u, t, hi]
  let p : Equiv.Perm (Fin (1 + n)) := Set.powersetCard.permOfDisjoint hdisj
  let c : Fin (1 + n) ≃ Fin (n + 1) := finCongr (Nat.add_comm 1 n)
  let p' : Equiv.Perm (Fin (n + 1)) := c.symm.trans (p.trans c)
  -- After reconciling the two cardinality presentations, this shuffle is the inverse cycle
  -- which moves position `k` to the front and shifts the preceding positions one step right.
  have hec : (fun q ↦ e (c q)) =
      (Set.powersetCard.disjUnion hdisj).val.orderEmbOfFin
        (Set.powersetCard.disjUnion hdisj).prop := by
    apply Finset.orderEmbOfFin_unique
    · intro q
      have hdval : (Set.powersetCard.disjUnion hdisj).val = s :=
        congrArg Subtype.val hunion
      rw [hdval]
      exact Finset.orderEmbOfFin_mem s hsCard (c q)
    · intro a b hab
      apply e.strictMono
      simpa [c, Fin.ext_iff] using hab
  have hp : p' = k.cycleRange.symm := by
    apply Equiv.ext
    intro j
    apply e.injective
    -- Unfold the conjugated shuffle so both sides are compared in the increasing enumeration.
    change e (c (p (c.symm j))) = e (k.cycleRange.symm j)
    have hrhs : e (k.cycleRange.symm j) =
        (Fin.cons (e k) (k.removeNth (fun q ↦ e q)) : Fin (n + 1) → I) j := by
      simpa only [Function.comp_apply] using
        congrFun (Fin.cons_removeNth_eq_comp_cycleRange_symm e k) j |>.symm
    rw [hrhs, hek]
    -- The disjoint-union permutation enumerates the singleton first and the erased set second.
    change e (c (p (c.symm j))) =
      (Fin.cons i (k.removeNth (fun q ↦ e q)) : Fin (n + 1) → I) j
    rw [hremove]
    -- Expose the function represented by the increasing enumeration before applying `hec`.
    change (fun q ↦ e (c q)) (p (c.symm j)) = _
    rw [hec]
    let x : (Set.powersetCard.disjUnion hdisj).val :=
      Equiv.Finset.disjUnionEquiv u.val t.val hdisj
        (((Set.powersetCard.orderIsoOfFin u).sumCongr
          (Set.powersetCard.orderIsoOfFin t)) (finSumFinEquiv.symm (c.symm j)))
    have hx : (Set.powersetCard.disjUnion hdisj).val.orderEmbOfFin
        (Set.powersetCard.disjUnion hdisj).prop (p (c.symm j)) = x := by
      have hpApply : p (c.symm j) =
          (Set.powersetCard.orderIsoOfFin (Set.powersetCard.disjUnion hdisj)).symm x := rfl
      rw [hpApply]
      exact congrArg Subtype.val
        ((Set.powersetCard.orderIsoOfFin (Set.powersetCard.disjUnion hdisj)).apply_symm_apply x)
    rw [hx]
    cases j using Fin.cases with
    | zero =>
        have hzero : finSumFinEquiv.symm (c.symm 0) = Sum.inl (0 : Fin 1) := by
          apply finSumFinEquiv.injective
          apply Fin.ext
          rfl
        simp only [x, hzero, Fin.cons_zero]
        -- Coercing the disjoint-union subtype reveals the singleton entry.
        change ↑(Equiv.Finset.disjUnionEquiv u.val t.val hdisj
          (Sum.inl ((Set.powersetCard.orderIsoOfFin u) 0))) = i
        rw [Equiv.Finset.disjUnionEquiv_inl]
        dsimp only [Set.powersetCard.orderIsoOfFin, u]
        -- The unique increasing enumeration of a singleton is constant at its element.
        change Finset.orderEmbOfFin {i} (Finset.card_singleton i) 0 = i
        exact Finset.orderEmbOfFin_singleton i 0
    | succ q =>
        have hsucc : finSumFinEquiv.symm (c.symm q.succ) = Sum.inr q := by
          apply finSumFinEquiv.injective
          rw [finSumFinEquiv.apply_symm_apply]
          apply Fin.ext
          simp [c]
          omega
        simp only [x, hsucc, Fin.cons_succ]
        -- Coercing the right summand reveals the increasing enumeration of `s.erase i`.
        change ↑(Equiv.Finset.disjUnionEquiv u.val t.val hdisj
          (Sum.inr ((Set.powersetCard.orderIsoOfFin t) q))) =
            (s.erase i).orderEmbOfFin (show (s.erase i).card = n from rfl) q
        rw [Equiv.Finset.disjUnionEquiv_inr]
        dsimp only [Set.powersetCard.orderIsoOfFin, t]
        change (s.erase i).orderEmbOfFin (show (s.erase i).card = n from rfl) q =
          (s.erase i).orderEmbOfFin (show (s.erase i).card = n from rfl) q
        rfl
  have hsign : Equiv.Perm.sign p' = Equiv.Perm.sign p := by
    simp [p']
  rw [basisEraseSign]
  -- Unfolding the local permutation exposes the sign computed above.
  change Equiv.Perm.sign p = _
  rw [← hsign, hp, Equiv.Perm.sign_symm, Fin.sign_cycleRange]
  congr 1
  -- The initial segment below `k` is order-isomorphic to the elements of `s` strictly below `i`,
  -- so its cardinality is the exponent in the claimed sign.
  have himage : Finset.image e (Finset.Iio k) = s.filter (fun j ↦ j < i) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_Iio, Finset.mem_filter]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem s hsCard j, hek ▸ e.strictMono hj⟩
    · rintro ⟨hxs, hxi⟩
      let j : Fin (n + 1) := (s.orderIsoOfFin hsCard).symm ⟨x, hxs⟩
      refine ⟨j, ?_, ?_⟩
      · exact e.lt_iff_lt.mp (by simpa [e, j, k] using hxi)
      · exact congrArg Subtype.val ((s.orderIsoOfFin hsCard).apply_symm_apply ⟨x, hxs⟩)
  rw [← Fin.card_Iio k, ← himage, Finset.card_image_of_injective _ e.injective]

/-- The shuffle sign which moves `i` to the front of an ordered exterior monomial is `-1`
raised to the number of indices before `i`. This formula also applies when `i ∉ s`: inserting
`i` changes neither the erased set defining the shuffle nor the indices strictly below `i`. -/
@[simp]
theorem basisEraseSign_eq_neg_one_pow_card_filter_lt {I : Type w} [LinearOrder I]
    (i : I) (s : Finset I) :
    basisEraseSign i s = (-1 : ℤˣ) ^ (s.filter (fun j ↦ j < i)).card := by
  classical
  by_cases hi : i ∈ s
  · exact basisEraseSign_eq_neg_one_pow_card_filter_lt_of_mem i s hi
  · have hsign : basisEraseSign i (insert i s) = basisEraseSign i s := by
      simp [basisEraseSign, hi]
    have hfilter : (insert i s).filter (fun j ↦ j < i) = s.filter (fun j ↦ j < i) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hji' | hjs, hji⟩
        · exact ((ne_of_lt hji) hji').elim
        · exact ⟨hjs, hji⟩
      · exact fun h ↦ ⟨Or.inr h.1, h.2⟩
    rw [← hsign, ← hfilter]
    exact basisEraseSign_eq_neg_one_pow_card_filter_lt_of_mem i (insert i s)
      (Finset.mem_insert_self i s)

/-- The exterior-basis vector indexed by a singleton is the image of the corresponding basis
vector under the exterior-algebra generator. -/
@[simp]
theorem basis_singleton {I : Type w} [LinearOrder I]
    (b : Module.Basis I R M) (i : I) :
    b.ExteriorAlgebra {i} = ExteriorAlgebra.ι R (b i) := by
  simp [b.exteriorAlgebra_eq_prod_map_sort]

/-- The exterior-basis vector indexed by a pair `{i, j}` with `i < j` is the product of the two
basis vectors in increasing order. -/
theorem basis_pair {I : Type w} [LinearOrder I] (b : Module.Basis I R M) {i j : I} (hij : i < j) :
    b.ExteriorAlgebra {i, j} = ExteriorAlgebra.ι R (b i) * ExteriorAlgebra.ι R (b j) := by
  rw [b.exteriorAlgebra_eq_prod_map_sort,
    Finset.sort_insert _ (by simpa using hij.le) (by simpa using hij.ne)]
  simp

/-- Multiplying the basis vector for `i` by the basis vector for `s.erase i` reconstructs the
basis vector for `s`, with the shuffle sign that moves `i` to the front. -/
theorem basis_singleton_mul_basis_erase {I : Type w} [LinearOrder I]
    (b : Module.Basis I R M) (i : I) (s : Finset I) (hi : i ∈ s) :
    b.ExteriorAlgebra {i} * b.ExteriorAlgebra (s.erase i) =
      basisEraseSign i s • b.ExteriorAlgebra s := by
  let u : Set.powersetCard I 1 := ⟨{i}, Finset.card_singleton i⟩
  let t : Set.powersetCard I (s.erase i).card := ⟨s.erase i, rfl⟩
  have hdisj : Disjoint u.val t.val := by simp [u, t]
  have hunion : Set.powersetCard.disjUnion hdisj =
      (Set.powersetCard.ofCard (s := s) (by
        rw [Finset.card_erase_of_mem hi]
        have : 0 < s.card := Finset.card_pos.mpr ⟨i, hi⟩
        omega) : Set.powersetCard I (1 + (s.erase i).card)) := by
    apply Subtype.ext
    simp [Set.powersetCard.disjUnion, u, t, hi]
  have hprod := ExteriorAlgebra.basis_mul_of_disjoint b u t hdisj
  rw [hunion] at hprod
  simpa [basisEraseSign, basisEraseSignOfErase, u, t] using hprod

/-- **Creating a basis coordinate inserts it into the index set**, with the shuffle sign that
moves it to the front; it is zero when the coordinate is already present, since a repeated
generator squares to zero. -/
@[simp]
theorem ι_mul_basis {I : Type w} [LinearOrder I]
    (b : Module.Basis I R M) (i : I) (s : Finset I) :
    ExteriorAlgebra.ι R (b i) * b.ExteriorAlgebra s =
      if i ∈ s then 0
        else basisEraseSign i (insert i s) • b.ExteriorAlgebra (insert i s) := by
  classical
  rw [← basis_singleton]
  split_ifs with hi
  · exact ExteriorAlgebra.basis_mul_of_not_disjoint b
      (⟨{i}, Finset.card_singleton i⟩ : Set.powersetCard I 1) (⟨s, rfl⟩ : Set.powersetCard I s.card)
      (by simp [hi])
  · have h := basis_singleton_mul_basis_erase b i (insert i s) (Finset.mem_insert_self i s)
    rwa [Finset.erase_insert hi] at h

/-- Contracting an exterior-basis vector erases the contracted coordinate, with the shuffle sign
that moves that coordinate to the front; it is zero when the coordinate is absent. -/
@[simp]
theorem contractLeft_coord_basis {I : Type w} [LinearOrder I]
    (b : Module.Basis I R M) (i : I) (s : Finset I) :
    contractLeft (Q := (0 : QuadraticForm R M)) (b.coord i) (b.ExteriorAlgebra s) =
      if i ∈ s then basisEraseSign i s • b.ExteriorAlgebra (s.erase i) else 0 := by
  classical
  split_ifs with hi
  · have hprod' := basis_singleton_mul_basis_erase b i s hi
    have hcontract : contractLeft (Q := (0 : QuadraticForm R M)) (b.coord i)
        (b.ExteriorAlgebra {i} * b.ExteriorAlgebra (s.erase i)) =
        b.ExteriorAlgebra (s.erase i) := by
      rw [basis_singleton, contractLeft_ι_mul]
      simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
      rw [contractLeft_coord_basis_eq_zero_of_not_mem b i (s.erase i) (by simp),
        mul_zero, sub_zero]
      simp
    rcases Int.units_eq_one_or (basisEraseSign i s) with hsign | hsign
    · rw [hsign, one_smul] at hprod' ⊢
      rw [← hprod']
      exact hcontract
    · have hprodNeg : b.ExteriorAlgebra {i} * b.ExteriorAlgebra (s.erase i) =
          -b.ExteriorAlgebra s := by
        rw [hsign] at hprod'
        simpa using hprod'
      rw [hprodNeg, map_neg] at hcontract
      have h := congrArg Neg.neg hcontract
      rw [hsign]
      simpa using h
  · exact contractLeft_coord_basis_eq_zero_of_not_mem b i s hi

/-- Creating an unoccupied coordinate after contracting an occupied one replaces that
coordinate in an exterior-basis vector, with the product of the two shuffle signs. -/
theorem ι_mul_contractLeft_coord_basis_of_not_mem_of_mem {I : Type w} [LinearOrder I]
    (b : Module.Basis I R M) (i j : I) (s : Finset I) (hi : i ∉ s) (hj : j ∈ s) :
    ExteriorAlgebra.ι R (b i) *
        contractLeft (Q := (0 : QuadraticForm R M)) (b.coord j) (b.ExteriorAlgebra s) =
      (basisEraseSign j s * basisEraseSign i (insert i (s.erase j))) •
        b.ExteriorAlgebra (insert i (s.erase j)) := by
  classical
  simp [contractLeft_coord_basis, ι_mul_basis, hi, hj, mul_smul_comm, smul_smul]

/-- Creation after contraction by a basis coordinate is the projection onto exterior basis
vectors containing that coordinate.

This is not a `simp` lemma because `contractLeft_coord_basis` is the canonical normal form for
the contraction in its left-hand side. -/
theorem ι_mul_contractLeft_coord_basis {I : Type w} [LinearOrder I]
    (b : Module.Basis I R M) (i : I) (s : Finset I) :
    ExteriorAlgebra.ι R (b i) *
        contractLeft (Q := (0 : QuadraticForm R M)) (b.coord i) (b.ExteriorAlgebra s) =
      if i ∈ s then b.ExteriorAlgebra s else 0 := by
  rw [contractLeft_coord_basis]
  split_ifs with hi
  · rw [← basis_singleton]
    rw [mul_smul_comm]
    rw [basis_singleton_mul_basis_erase b i s hi]
    let n := (s.filter fun j ↦ j < i).card
    have hsignSq : ((-1 : ℤˣ) ^ n) * ((-1 : ℤˣ) ^ n) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    rw [basisEraseSign_eq_neg_one_pow_card_filter_lt, smul_smul, hsignSq, one_smul]
  · rw [mul_zero]

/-! ### Exterior powers under the grade involution and contraction -/

/-- **The grade involution acts on the `n`-th exterior power by `(-1) ^ n`.** -/
theorem involute_of_mem_exteriorPower {n : ℕ} {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^n M) :
    involute (Q := (0 : QuadraticForm R M)) x = (-1 : R) ^ n • x := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r => simp
  | add x y i hx hy ihx ihy => rw [map_add, ihx, ihy, smul_add]
  | mem_mul m hm i x hx ih =>
    obtain ⟨v, rfl⟩ := hm
    rw [map_mul, ih, involute_ι, mul_smul_comm, neg_mul, smul_neg, pow_succ', mul_smul,
      neg_one_smul]

/-- Contraction annihilates the zeroth exterior power, the scalars. -/
theorem contractLeft_eq_zero_of_mem_exteriorPower_zero (d : Module.Dual R M)
    {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^0 M) :
    contractLeft (Q := (0 : QuadraticForm R M)) d x = 0 := by
  rw [_root_.ExteriorAlgebra.exteriorPower, pow_zero] at hx
  obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hx
  exact contractLeft_algebraMap (Q := (0 : QuadraticForm R M)) d r

/-- **Contraction lowers the exterior degree by one**: it carries the `(n + 1)`-th exterior power
into the `n`-th. -/
theorem contractLeft_mem_exteriorPower (d : Module.Dual R M) {n : ℕ}
    {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^(n + 1) M) :
    contractLeft (Q := (0 : QuadraticForm R M)) d x ∈ ⋀[R]^n M := by
  suffices h : ∀ i (x : ExteriorAlgebra R M) (_ : x ∈ ⋀[R]^i M),
      contractLeft (Q := (0 : QuadraticForm R M)) d x ∈ ⋀[R]^(i - 1) M from h _ x hx
  intro i x hx
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r => simp
  | add x y i hx hy ihx ihy => rw [map_add]; exact add_mem ihx ihy
  | mem_mul m hm i x hx ih =>
    obtain ⟨v, rfl⟩ := hm
    rw [contractLeft_ι_mul, Nat.succ_sub_one]
    refine sub_mem (Submodule.smul_mem _ _ hx) ?_
    rcases i with _ | i
    · rw [contractLeft_eq_zero_of_mem_exteriorPower_zero d hx, mul_zero]
      exact zero_mem _
    · rw [Nat.add_sub_cancel] at ih
      exact ι_mul_mem_exteriorPower v ih

/-- **Contraction of a wedge product of vectors** is the alternating sum of the contractions of
its factors: `d ⌋ (v₀ ∧ ⋯ ∧ vₙ) = ∑ᵢ (-1) ^ i d(vᵢ) v₀ ∧ ⋯ ∧ v̂ᵢ ∧ ⋯ ∧ vₙ`. -/
theorem contractLeft_ιMulti (d : Module.Dual R M) {n : ℕ} (v : Fin (n + 1) → M) :
    contractLeft (Q := (0 : QuadraticForm R M)) d (ExteriorAlgebra.ιMulti R (n + 1) v) =
      ∑ i : Fin (n + 1), ((-1 : R) ^ (i : ℕ) * d (v i)) •
        ExteriorAlgebra.ιMulti R n (i.removeNth v) := by
  induction n with
  | zero => simp [Algebra.algebraMap_eq_smul_one]
  | succ n ih =>
    have hrem (i : Fin (n + 1)) : ExteriorAlgebra.ιMulti R (n + 1) (i.succ.removeNth v) =
        ExteriorAlgebra.ι R (v 0) *
          ExteriorAlgebra.ιMulti R n (i.removeNth (Matrix.vecTail v)) := by
      rw [ExteriorAlgebra.ιMulti_succ_apply]
      congr 2
      ext j
      simp [Matrix.vecTail, Fin.removeNth_apply, Fin.succ_succAbove_succ]
    rw [ExteriorAlgebra.ιMulti_succ_apply, contractLeft_ι_mul, ih, Fin.sum_univ_succ (n := n + 1),
      Finset.mul_sum]
    simp [hrem, pow_succ, sub_eq_add_neg, Matrix.vecTail, Fin.tail,
      Function.comp_def]

end TauCeti.ExteriorAlgebra

namespace ExteriorAlgebra

variable {R : Type*} {M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Contraction against a functional commutes with an exterior-algebra map after pulling
back the functional. -/
theorem contractLeft_map {N : Type*} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)
    (d : Module.Dual R N) (x : ExteriorAlgebra R M) :
    contractLeft (Q := (0 : QuadraticForm R N)) d (_root_.ExteriorAlgebra.map f x) =
      _root_.ExteriorAlgebra.map f
        (contractLeft (Q := (0 : QuadraticForm R M)) (d ∘ₗ f) x) := by
  -- The exterior-algebra map is the zero-quadratic-form case of the Clifford-algebra map.
  exact CliffordAlgebra.contractLeft_map { f with map_app' := fun _ => rfl } d x

/-- **A vector graded-commutes with every multivector**: moving `ι R m` past `x` applies the grade
involution to `x`. -/
theorem ι_mul_eq_involute_mul (m : M) (x : ExteriorAlgebra R M) :
    ExteriorAlgebra.ι R m * x =
      involute (Q := (0 : QuadraticForm R M)) x * ExteriorAlgebra.ι R m := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes, Algebra.commutes]
  | ι v =>
    rw [involute_ι, neg_mul, eq_neg_iff_add_eq_zero]
    exact ExteriorAlgebra.ι_add_mul_swap m v
  | mul x y hx hy => rw [← mul_assoc, hx, mul_assoc, hy, map_mul, mul_assoc]
  | add x y hx hy => rw [mul_add, hx, hy, map_add, add_mul]

end ExteriorAlgebra

namespace TauCeti.ExteriorAlgebra

open _root_.ExteriorAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-! ### Contraction in degree at least the rank -/

variable [Module.Free R M] [Module.Finite R M]

/-- **A form of degree at least the rank is divisible by any vector `m` with `d m = 1`**: if
`d m = 1` and `finrank R M ≤ n`, then every `x ∈ ⋀ⁿ M` is `m ∧ (d ⌋ x)`. -/
theorem eq_ι_mul_contractLeft_of_finrank_le {d : Module.Dual R M} {m : M} (hdm : d m = 1)
    {n : ℕ} (hn : Module.finrank R M ≤ n) {x : _root_.ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^n M) :
    x = ι R m * contractLeft (Q := (0 : QuadraticForm R M)) d x := by
  -- `m ∧ x` lies above the rank, so it vanishes, and contracting it by `d` gives the claim.
  have h0 : ι R m * x = 0 := ZeroMemClass.coe_eq_zero.mpr <|
    exteriorPower.eq_zero_of_finrank_lt (1 + n) (by omega)
      ⟨_, SetLike.mul_mem_graded (ι_mem_exteriorPower_one m) hx⟩
  have h := congrArg (contractLeft (Q := (0 : QuadraticForm R M)) d) h0
  rwa [contractLeft_ι_mul, hdm, one_smul, map_zero, sub_eq_zero] at h

/-- **Forms killed by a contraction multiply to zero in degree at least the rank**: if `d m = 1`,
the forms `x ∈ ⋀ᵏ M` and `y ∈ ⋀ˡ M` satisfy `d ⌋ x = 0` and `d ⌋ y = 0`, and
`finrank R M ≤ k + l`, then `x ∧ y = 0`. -/
theorem mul_eq_zero_of_contractLeft_eq_zero {d : Module.Dual R M} {m : M} (hdm : d m = 1)
    {k l : ℕ} (hkl : Module.finrank R M ≤ k + l) {x y : _root_.ExteriorAlgebra R M}
    (hx : x ∈ ⋀[R]^k M) (hy : y ∈ ⋀[R]^l M)
    (hdx : contractLeft (Q := (0 : QuadraticForm R M)) d x = 0)
    (hdy : contractLeft (Q := (0 : QuadraticForm R M)) d y = 0) : x * y = 0 := by
  rw [eq_ι_mul_contractLeft_of_finrank_le hdm hkl (SetLike.mul_mem_graded hx hy), contractLeft_mul,
    hdx, hdy, zero_mul, mul_zero, add_zero, mul_zero]

/-- **The square of a two-form in rank at most four.** If `d m = 1` and `finrank R M ≤ 4`, a
two-form `x` satisfies `x ∧ x = 2 x ∧ m ∧ (d ⌋ x)`. -/
theorem mul_self_eq_two_smul_mul_ι_mul_contractLeft {d : Module.Dual R M} {m : M}
    (hdm : d m = 1) (h4 : Module.finrank R M ≤ 4) {x : _root_.ExteriorAlgebra R M}
    (hx : x ∈ ⋀[R]^2 M) :
    x * x = 2 • (x * (ι R m * contractLeft (Q := (0 : QuadraticForm R M)) d x)) := by
  -- Write `x = m ∧ a + b` with `a = d ⌋ x`. Then `d ⌋ b = 0`, so `b ∧ b = 0` in rank at most
  -- four; also `(m ∧ a) ∧ (m ∧ a) = 0`, and the two-forms `m ∧ a` and `b` commute.
  -- The contraction `d ⌋ x` is a vector `a`.
  obtain ⟨a, ha⟩ : ∃ a, ι R a = contractLeft (Q := (0 : QuadraticForm R M)) d x :=
    ⟨_, ι_ιInv_of_mem_exteriorPower_one (contractLeft_mem_exteriorPower d (n := 1) hx)⟩
  rw [← ha]
  set g := ι R m * ι R a with hg
  have hgmem : g ∈ ⋀[R]^2 M :=
    SetLike.mul_mem_graded (ι_mem_exteriorPower_one m) (ι_mem_exteriorPower_one a)
  -- The remainder `b = x - m ∧ a` is a two-form killed by `d`.
  set b := x - g with hb
  have hbmem : b ∈ ⋀[R]^2 M := sub_mem hx hgmem
  have hdb : contractLeft (Q := (0 : QuadraticForm R M)) d b = 0 := by
    have hda : contractLeft (Q := (0 : QuadraticForm R M)) d (ι R a) = 0 := by
      rw [ha, contractLeft_contractLeft]
    rw [hb, map_sub, hg, contractLeft_ι_mul, hdm, one_smul, hda, mul_zero, sub_zero, ha,
      sub_self]
  have hbb : b * b = 0 :=
    mul_eq_zero_of_contractLeft_eq_zero hdm (by omega) hbmem hbmem hdb hdb
  have hgg : g * g = 0 := by
    have h := ι_add_mul_swap (R := R) a m
    rw [add_eq_zero_iff_eq_neg] at h
    calc g * g = ι R m * (ι R a * ι R m) * ι R a := by simp only [hg, mul_assoc]
      _ = 0 := by rw [h, mul_neg, ← mul_assoc, ι_sq_zero, zero_mul, neg_zero, zero_mul]
  -- A two-form is fixed by the grade involution, so it commutes with the two-form `g`.
  have hinv : involute (Q := (0 : QuadraticForm R M)) b = b := by
    rw [involute_of_mem_exteriorPower hbmem]
    simp
  have hcomm : g * b = b * g := by
    rw [hg, mul_assoc, ι_mul_eq_involute_mul a b, hinv, ← mul_assoc, ι_mul_eq_involute_mul m b,
      hinv, mul_assoc]
  have hx' : x = b + g := (sub_add_cancel x g).symm
  rw [hx', add_mul, mul_add, mul_add, hbb, hgg, hcomm, add_mul, hgg, two_smul]
  abel

end TauCeti.ExteriorAlgebra

namespace ExteriorAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-! ### Splitting off a free coordinate -/

/-- **Splitting off a free coordinate.** In the exterior algebra of `M × R`, with `e = (0, 1)`,
every element `z` is `a + e ∧ b`, where `a` is the image of `z` under `⋀ M × R → ⋀ M → ⋀ (M × R)`
and `b` is the image of the contraction of `z` by the second coordinate. -/
theorem map_inl_map_fst_add_ι_inr_mul_contractLeft_snd (z : ExteriorAlgebra R (M × R)) :
    map (LinearMap.inl R M R) (map (LinearMap.fst R M R) z) +
        ι R (LinearMap.inr R M R 1) * map (LinearMap.inl R M R) (map (LinearMap.fst R M R)
          (contractLeft (Q := (0 : QuadraticForm R (M × R))) (LinearMap.snd R M R) z)) =
      z := by
  induction z using CliffordAlgebra.left_induction with
  | algebraMap r => simp [contractLeft_algebraMap]
  | add z₁ z₂ h₁ h₂ =>
    simp only [map_add, mul_add]
    conv_rhs => rw [← h₁, ← h₂]
    abel
  | ι_mul z m ih =>
    -- Write `m = (m₁, 0) + m₂ e`; then `e ∧ e = 0` and `(m₁, 0) ∧ e = -(e ∧ (m₁, 0))`.
    have hm : ι R m = ι R (LinearMap.inl R M R m.1) + m.2 • ι R (LinearMap.inr R M R 1) := by
      rw [← map_smul, ← map_add]; congr 1; ext <;> simp
    have he := ι_sq_zero (R := R) (LinearMap.inr R M R (1 : R))
    have hc := eq_neg_of_add_eq_zero_right <|
      ι_add_mul_swap (R := R) (LinearMap.inr R M R (1 : R)) (LinearMap.inl R M R m.1)
    -- `left_induction` states the step with `CliffordAlgebra.ι 0`, which is `ι R` by definition.
    change _ = ι R m * z
    rw [contractLeft_ι_mul]
    simp only [map_mul, map_sub, map_smul, map_apply_ι]
    conv_rhs => rw [← ih, hm]
    simp only [add_mul, mul_add, mul_sub, smul_mul_assoc, mul_smul_comm, ← mul_assoc, he, hc,
      smul_zero, add_zero, neg_mul, LinearMap.fst_apply, LinearMap.snd_apply]
    abel

/-! ### Contractions on `M × R` in the splitting `a + e ∧ b` -/

/-- The contraction by `φ.coprod ψ` on the image of `⋀ M` in `⋀ (M × N)` is the contraction
by `φ`. -/
theorem contractLeft_coprod_map_inl {N : Type*} [AddCommGroup N] [Module R N]
    (φ : Module.Dual R M) (ψ : Module.Dual R N) (w : ExteriorAlgebra R M) :
    contractLeft (Q := (0 : QuadraticForm R (M × N))) (φ.coprod ψ)
        (map (LinearMap.inl R M N) w) =
      map (LinearMap.inl R M N) (contractLeft (Q := (0 : QuadraticForm R M)) φ w) := by
  rw [contractLeft_map, LinearMap.coprod_inl]

/-- The contraction by `φ + x · snd` on `e ∧ w`, with `e = (0, 1)`: `d(e ∧ w) = x w - e ∧ d w`. -/
theorem contractLeft_coprod_ι_inr_mul (φ : Module.Dual R M) (x : R)
    (w : ExteriorAlgebra R (M × R)) :
    contractLeft (Q := (0 : QuadraticForm R (M × R)))
        (φ.coprod (LinearMap.toSpanSingleton R R x)) (ι R (LinearMap.inr R M R 1) * w) =
        x • w - ι R (LinearMap.inr R M R 1) *
          contractLeft (Q := (0 : QuadraticForm R (M × R)))
            (φ.coprod (LinearMap.toSpanSingleton R R x)) w := by
  rw [contractLeft_ι_mul]
  simp

/-- Projection onto the first factor retracts the induced map of exterior algebras. -/
theorem leftInverse_map_fst_map_inl {N : Type*} [AddCommGroup N] [Module R N] :
    Function.LeftInverse (map (LinearMap.fst R M N)) (map (LinearMap.inl R M N)) :=
  leftInverse_map_iff.2 fun _ ↦ rfl

/-- The `⋀ M`-component of the contraction by `φ + x · snd`: writing `z = a + e ∧ b` as in
`map_inl_map_fst_add_ι_inr_mul_contractLeft_snd`, the `⋀ M`-component of `d z` is `d a + x b`. -/
theorem map_fst_contractLeft_coprod (φ : Module.Dual R M) (x : R)
    (z : ExteriorAlgebra R (M × R)) :
    map (LinearMap.fst R M R)
        (contractLeft (Q := (0 : QuadraticForm R (M × R)))
          (φ.coprod (LinearMap.toSpanSingleton R R x)) z) =
      contractLeft (Q := (0 : QuadraticForm R M)) φ (map (LinearMap.fst R M R) z) +
        x • map (LinearMap.fst R M R)
          (contractLeft (Q := (0 : QuadraticForm R (M × R))) (LinearMap.snd R M R) z) := by
  conv_lhs => rw [← map_inl_map_fst_add_ι_inr_mul_contractLeft_snd z]
  rw [map_add, contractLeft_coprod_map_inl, contractLeft_coprod_ι_inr_mul,
    contractLeft_coprod_map_inl]
  simp only [LinearMap.coe_inr, map_add, map_sub, map_smul, map_mul, map_apply_ι,
    LinearMap.fst_apply, map_zero, zero_mul, sub_zero]
  rw [leftInverse_map_fst_map_inl, leftInverse_map_fst_map_inl]

/-- The `e`-component of the contraction by `φ + x · snd`: writing `z = a + e ∧ b` as in
`map_inl_map_fst_add_ι_inr_mul_contractLeft_snd`, the contraction `d b` is minus the
`e`-component of `d z`. -/
theorem contractLeft_map_fst_contractLeft_snd (φ : Module.Dual R M) (x : R)
    (z : ExteriorAlgebra R (M × R)) :
    contractLeft (Q := (0 : QuadraticForm R M)) φ (map (LinearMap.fst R M R)
        (contractLeft (Q := (0 : QuadraticForm R (M × R))) (LinearMap.snd R M R) z)) =
      -map (LinearMap.fst R M R)
        (contractLeft (Q := (0 : QuadraticForm R (M × R))) (LinearMap.snd R M R)
          (contractLeft (Q := (0 : QuadraticForm R (M × R)))
            (φ.coprod (LinearMap.toSpanSingleton R R x)) z)) := by
  have hD := map_inl_map_fst_add_ι_inr_mul_contractLeft_snd
    (contractLeft (Q := (0 : QuadraticForm R (M × R))) (LinearMap.snd R M R) z)
  rw [contractLeft_contractLeft, map_zero, map_zero, mul_zero, add_zero] at hD
  rw [← leftInverse_map_fst_map_inl (R := R) (M := M) (N := R) (contractLeft _ _),
    ← contractLeft_coprod_map_inl φ (LinearMap.toSpanSingleton R R x),
    hD, contractLeft_comm, map_neg]

end ExteriorAlgebra

end CheckedSource12

/-! ## Source: TauCeti.RingTheory.KoszulComplex.Basic -/
section CheckedSource13
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The Koszul complex of a linear functional

For a linear functional `φ : M → R` on a module over a commutative ring, the Koszul complex
`K(φ)` is the chain complex `⋯ → ⋀³ M → ⋀² M → M → R` with `K(φ)ₙ = ⋀ⁿ M` and differential the
contraction by `φ`,
`d(v₀ ∧ ⋯ ∧ vₙ) = ∑ᵢ (-1) ^ i φ(vᵢ) v₀ ∧ ⋯ ∧ v̂ᵢ ∧ ⋯ ∧ vₙ`.
For a finite sequence `x = (x₁, …, xₙ)` in `R`, the functional `v ↦ ∑ᵢ vᵢ xᵢ` on `Rⁿ` gives the
Koszul complex `K(x)` of the sequence, whose zeroth homology is `R ⧸ (x₁, …, xₙ)`.

## Main declarations

* `TauCeti.koszulComplex φ`: the Koszul complex of `φ`, as an `ℕ`-indexed chain complex of
  `R`-modules.
* `TauCeti.koszulDifferential φ n`: its differential `⋀ⁿ⁺¹ M → ⋀ⁿ M`, the contraction by `φ`, with
  the alternating-deletion formula `TauCeti.koszulDifferential_ιMulti`.
* `TauCeti.zeroEquiv_koszulDifferential_zero`: under `⋀⁰ M ≅ R` and `⋀¹ M ≅ M`, the first
  differential is `φ` itself.
* `TauCeti.exact_koszulDifferential_of_retract`: exactness of a Koszul complex passes to a
  retract along linear maps compatible with the functionals.
* `TauCeti.map_fst_koszulDifferential_coprod`: the coordinate formula for the differential
  after adjoining one scalar to a linear functional.
* `TauCeti.koszulComplex.exactAt_succ_iff`: `Hₖ₊₁(K(φ)) = 0` exactly when the Koszul
  differentials out of and into `⋀ᵏ⁺¹ M` are exact.
* `TauCeti.koszulComplex.map`: the chain map `K(φ) → K(ψ)` induced by a linear map `g` with
  `ψ ∘ g = φ`, functorial in `g`, and `TauCeti.koszulComplex.mapIso`, the isomorphism induced by a
  linear equivalence.
* `TauCeti.koszulComplex.smulHomotopy`: for `m : M`, exterior multiplication by `m` is a
  null-homotopy of multiplication by `φ(m)`, so that `φ(m)` annihilates the Koszul homology
  (`TauCeti.koszulComplex.smul_homology_eq_zero`).
* `TauCeti.koszulComplex.homologyZeroEquiv`: `H₀(K(φ)) ≃ R ⧸ φ(M)`, and its specialization
  `TauCeti.koszulComplex.homologyZeroEquivSpan` to `H₀(K(x)) ≃ R ⧸ (x₁, …, xₙ)` for a finite
  sequence.

## References

* [The Stacks Project, Tags 0622, 0623 and 0624](https://stacks.math.columbia.edu/tag/0621)

The interface (the Koszul complex of a linear functional with exterior-power terms, the
alternating-deletion differential, `koszulComplex.map` along `ψ ∘ g = φ`, and the homotopy
`d(m ∧ v) + m ∧ d(v) = φ(m) v`) follows the design of Nailin Guan in the Mathlib pull requests
[mathlib4#43708](https://github.com/leanprover-community/mathlib4/pull/43708) (definition
of the Koszul complex) and
[mathlib4#43706](https://github.com/leanprover-community/mathlib4/pull/43706) (homotopy of the
Koszul complex). No code from those pull requests is vendored here.
-/

section

noncomputable section

universe u v

open CategoryTheory CliffordAlgebra

namespace TauCeti

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

section Differential

variable (φ : Module.Dual R M)

/-- The Koszul differential `⋀ⁿ⁺¹ M → ⋀ⁿ M` of a linear functional `φ`: the contraction by `φ`,
`v₀ ∧ ⋯ ∧ vₙ ↦ ∑ᵢ (-1) ^ i φ(vᵢ) v₀ ∧ ⋯ ∧ v̂ᵢ ∧ ⋯ ∧ vₙ` (see `koszulDifferential_ιMulti`). -/
def koszulDifferential (n : ℕ) : ⋀[R]^(n + 1) M →ₗ[R] ⋀[R]^n M :=
  (contractLeft (Q := (0 : QuadraticForm R M)) φ).restrict fun _ hx ↦
    ExteriorAlgebra.contractLeft_mem_exteriorPower φ hx

/-- The Koszul differential is the contraction by `φ`. -/
@[simp]
theorem coe_koszulDifferential_apply (n : ℕ) (x : ⋀[R]^(n + 1) M) :
    (koszulDifferential φ n x : ExteriorAlgebra R M) =
      contractLeft (Q := (0 : QuadraticForm R M)) φ x :=
  (rfl)

/-- The Koszul differential on a wedge product of vectors is the alternating sum of deletions:
`d(v₀ ∧ ⋯ ∧ vₙ) = ∑ᵢ (-1) ^ i φ(vᵢ) v₀ ∧ ⋯ ∧ v̂ᵢ ∧ ⋯ ∧ vₙ`. -/
theorem koszulDifferential_ιMulti (n : ℕ) (v : Fin (n + 1) → M) :
    koszulDifferential φ n (exteriorPower.ιMulti R (n + 1) v) =
      ∑ i : Fin (n + 1), ((-1 : R) ^ (i : ℕ) * φ (v i)) •
        exteriorPower.ιMulti R n (i.removeNth v) := by
  ext
  simp only [coe_koszulDifferential_apply, exteriorPower.ιMulti_apply_coe,
    ExteriorAlgebra.contractLeft_ιMulti, Submodule.coe_sum, Submodule.coe_smul]

/-- The Koszul differential squares to zero. -/
@[simp]
theorem koszulDifferential_comp_koszulDifferential (n : ℕ) :
    koszulDifferential φ n ∘ₗ koszulDifferential φ (n + 1) = 0 :=
  LinearMap.ext fun x ↦ Subtype.ext (contractLeft_contractLeft φ x.1)

/-- The Koszul differential squares to zero, elementwise. -/
@[simp]
theorem koszulDifferential_koszulDifferential (n : ℕ) (x : ⋀[R]^(n + 2) M) :
    koszulDifferential φ n (koszulDifferential φ (n + 1) x) = 0 :=
  LinearMap.congr_fun (koszulDifferential_comp_koszulDifferential φ n) x

/-- **The first Koszul differential is `φ`**: under the identifications `⋀⁰ M ≅ R` and
`⋀¹ M ≅ M`, the differential `⋀¹ M → ⋀⁰ M` is `φ`. -/
theorem zeroEquiv_comp_koszulDifferential_zero :
    (exteriorPower.zeroEquiv R M).toLinearMap ∘ₗ koszulDifferential φ 0 =
      φ ∘ₗ (exteriorPower.oneEquiv R M).toLinearMap := by
  refine exteriorPower.linearMap_ext (AlternatingMap.ext fun v ↦ ?_)
  simp [koszulDifferential_ιMulti]

/-- **The first Koszul differential is `φ`**, elementwise. -/
@[simp]
theorem zeroEquiv_koszulDifferential_zero (x : ⋀[R]^1 M) :
    exteriorPower.zeroEquiv R M (koszulDifferential φ 0 x) = φ (exteriorPower.oneEquiv R M x) :=
  LinearMap.congr_fun (zeroEquiv_comp_koszulDifferential_zero φ) x

/-- The image of the first Koszul differential, transported along `⋀⁰ M ≅ R`, is the image
of `φ`. -/
theorem map_zeroEquiv_range_koszulDifferential_zero :
    (LinearMap.range (koszulDifferential φ 0)).map (exteriorPower.zeroEquiv R M).toLinearMap =
      LinearMap.range φ := by
  rw [← LinearMap.range_comp, zeroEquiv_comp_koszulDifferential_zero,
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]

/-- The Koszul differential is natural: if `ψ ∘ g = φ`, then `⋀ g` intertwines the Koszul
differentials of `φ` and `ψ`. -/
theorem koszulDifferential_comp_map {N : Type*} [AddCommGroup N] [Module R N]
    {ψ : Module.Dual R N} {g : M →ₗ[R] N} (h : ψ ∘ₗ g = φ) (n : ℕ) :
    koszulDifferential ψ n ∘ₗ exteriorPower.map (n + 1) g =
      exteriorPower.map n g ∘ₗ koszulDifferential φ n :=
  LinearMap.ext fun x ↦ Subtype.ext <| by simp [ExteriorAlgebra.contractLeft_map, h]

/-- The Koszul differential is natural, elementwise: `⋀ g` carries the Koszul differential of
`ψ ∘ g` to that of `ψ`. -/
@[simp]
theorem koszulDifferential_map {N : Type*} [AddCommGroup N] [Module R N]
    (ψ : Module.Dual R N) (g : M →ₗ[R] N) (n : ℕ) (x : ⋀[R]^(n + 1) M) :
    koszulDifferential ψ n (exteriorPower.map (n + 1) g x) =
      exteriorPower.map n g (koszulDifferential (ψ ∘ₗ g) n x) :=
  LinearMap.congr_fun (koszulDifferential_comp_map _ rfl n) x

/-- The `⋀ M`-component of the Koszul differential of `K(φ, x)`: writing `z = a + e ∧ b`, it is
`d a + x b`. -/
theorem map_fst_koszulDifferential_coprod (x : R) (k : ℕ) (z : ⋀[R]^(k + 1) (M × R)) :
    exteriorPower.map k (LinearMap.fst R M R)
        (koszulDifferential (φ.coprod (LinearMap.toSpanSingleton R R x)) k z) =
      koszulDifferential φ k (exteriorPower.map (k + 1) (LinearMap.fst R M R) z) +
        x • exteriorPower.map k (LinearMap.fst R M R)
          (koszulDifferential (LinearMap.snd R M R) k z) :=
  Subtype.ext <| by
    simp only [exteriorPower.coe_map, coe_koszulDifferential_apply, Submodule.coe_add,
      Submodule.coe_smul, ExteriorAlgebra.map_fst_contractLeft_coprod]

variable {φ} in
/-- **Exactness passes to retracts.** If `g : M → N` has a retraction `h` and `ψ = φ ∘ h` (so
that also `φ = ψ ∘ g`), then the Koszul complex `K(φ)` is a retract of `K(ψ)`, and exactness of
`K(ψ)` at `⋀ⁿ⁺¹ N` implies exactness of `K(φ)` at `⋀ⁿ⁺¹ M`. -/
theorem exact_koszulDifferential_of_retract {N : Type*} [AddCommGroup N] [Module R N]
    {ψ : Module.Dual R N} (g : M →ₗ[R] N) (h : N →ₗ[R] M) (hhg : h ∘ₗ g = LinearMap.id)
    (hψ : φ ∘ₗ h = ψ) (n : ℕ)
    (hex : Function.Exact (koszulDifferential ψ (n + 1)) (koszulDifferential ψ n)) :
    Function.Exact (koszulDifferential φ (n + 1)) (koszulDifferential φ n) := by
  have hφ : ψ ∘ₗ g = φ := by rw [← hψ, LinearMap.comp_assoc, hhg, LinearMap.comp_id]
  refine LinearMap.exact_of_comp_of_mem_range
    (koszulDifferential_comp_koszulDifferential φ n) fun z hz ↦ ?_
  obtain ⟨y, hy⟩ := (hex (exteriorPower.map (n + 1) g z)).1 (by
    rw [koszulDifferential_map, hφ, hz, map_zero])
  refine ⟨exteriorPower.map (n + 2) h y, ?_⟩
  rw [koszulDifferential_map, hψ, hy]
  simp only [← LinearMap.comp_apply, ← exteriorPower.map_comp, hhg,
    exteriorPower.map_id, LinearMap.id_apply]

/-- The Koszul homotopy identity in degree zero: `d(m ∧ r) = φ(m) r` for `r ∈ ⋀⁰ M`. -/
theorem koszulDifferential_comp_wedgeLeft_zero (m : M) :
    koszulDifferential φ 0 ∘ₗ ExteriorAlgebra.wedgeLeft m 0 = φ m • LinearMap.id :=
  LinearMap.ext fun x ↦ Subtype.ext <| by
    simp [contractLeft_ι_mul, ExteriorAlgebra.contractLeft_eq_zero_of_mem_exteriorPower_zero φ x.2]

/-- The Koszul homotopy identity in positive degrees: `m ∧ d(v) + d(m ∧ v) = φ(m) v`. -/
theorem wedgeLeft_comp_koszulDifferential_add (m : M) (n : ℕ) :
    ExteriorAlgebra.wedgeLeft m n ∘ₗ koszulDifferential φ n +
        koszulDifferential φ (n + 1) ∘ₗ ExteriorAlgebra.wedgeLeft m (n + 1) =
      φ m • LinearMap.id :=
  LinearMap.ext fun x ↦ Subtype.ext <| by simp [contractLeft_ι_mul]

end Differential

/-- The **Koszul complex** `K(φ)` of a linear functional `φ : M → R`: the `ℕ`-indexed chain complex
with `K(φ)ₙ = ⋀ⁿ M` and differential `koszulDifferential φ`, the contraction by `φ`.

The body is exposed so that the terms of the complex are definitionally the exterior powers, and
elements of `(koszulComplex φ).X n` can be used as elements of `⋀ⁿ M`. -/
@[expose] def koszulComplex (φ : Module.Dual R M) : HomologicalComplex (ModuleCat.{max u v} R) PalomarBarycentricTor.naturalDown :=
  ChainComplex.of (fun n ↦ ModuleCat.of R (⋀[R]^n M))
    (fun n ↦ ModuleCat.ofHom (koszulDifferential φ n))
    fun n ↦ ModuleCat.hom_ext (koszulDifferential_comp_koszulDifferential φ n)

section

variable (φ : Module.Dual R M)

/-- The terms of the Koszul complex are the exterior powers. -/
@[simp]
theorem koszulComplex_X (n : ℕ) : (koszulComplex φ).X n = ModuleCat.of R (⋀[R]^n M) :=
  (rfl)

/-- The differential of the Koszul complex is the Koszul differential. -/
theorem koszulComplex_d (n : ℕ) :
    (koszulComplex φ).d (n + 1) n = ModuleCat.ofHom (koszulDifferential φ n) := by
  simp [koszulComplex]

/-- The differential of the Koszul complex is the Koszul differential, elementwise. -/
@[simp]
theorem koszulComplex_d_apply (n : ℕ) (x : ⋀[R]^(n + 1) M) :
    ((koszulComplex φ).d (n + 1) n).hom x = koszulDifferential φ n x :=
  congr($(koszulComplex_d φ n).hom x)

end

namespace koszulComplex

variable (φ : Module.Dual R M)

/-- The Koszul complex `K(φ)` is exact at `⋀ᵏ⁺¹ M`, i.e. `Hₖ₊₁(K(φ)) = 0`, exactly when the
Koszul differentials `⋀ᵏ⁺² M → ⋀ᵏ⁺¹ M → ⋀ᵏ M` are exact. -/
theorem exactAt_succ_iff (k : ℕ) :
    (koszulComplex φ).ExactAt (k + 1) ↔
      Function.Exact (koszulDifferential φ (k + 1)) (koszulDifferential φ k) := by
  rw [HomologicalComplex.exactAt_iff' _ (k + 2) (k + 1) k (by simp) (by simp),
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  simp only [HomologicalComplex.shortComplexFunctor'_obj_f,
    HomologicalComplex.shortComplexFunctor'_obj_g, koszulComplex_d]
  -- `ModuleCat.Hom.hom (ModuleCat.ofHom f)` is `f`; `ModuleCat.hom_ofHom` does not rewrite here
  -- because the terms of `koszulComplex φ` are only definitionally the exterior powers.
  rfl

section Map

variable {N P : Type v} [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
  {φ} {ψ : Module.Dual R N} {χ : Module.Dual R P}

/-- The chain map `K(φ) → K(ψ)` induced by a linear map `g : M → N` with `ψ ∘ g = φ`: in degree
`n` it is `⋀ⁿ g`. -/
def map (g : M →ₗ[R] N) (h : ψ ∘ₗ g = φ) : koszulComplex φ ⟶ koszulComplex ψ :=
  ChainComplex.ofHom (fun n ↦ ModuleCat.ofHom (exteriorPower.map n g)) fun n ↦ by
    rw [koszulComplex_d, koszulComplex_d]
    exact ModuleCat.hom_ext (koszulDifferential_comp_map _ h n)

/-- In degree `n`, the chain map induced by `g` is `⋀ⁿ g`. -/
@[simp]
theorem map_f (g : M →ₗ[R] N) (h : ψ ∘ₗ g = φ) (n : ℕ) :
    (map g h).f n = ModuleCat.ofHom (exteriorPower.map n g) := by
  rfl

/-- The identity of `M` induces the identity of `K(φ)`. -/
@[simp]
theorem map_id : map (φ := φ) LinearMap.id (LinearMap.comp_id φ) = 𝟙 (koszulComplex φ) := by
  ext n : 1
  rw [map_f, exteriorPower.map_id, HomologicalComplex.id_f]
  exact ModuleCat.ofHom_id

/-- The chain map induced by a composite is the composite of the induced chain maps. -/
@[reassoc]
theorem map_comp (g : M →ₗ[R] N) (h : ψ ∘ₗ g = φ) (g' : N →ₗ[R] P) (h' : χ ∘ₗ g' = ψ) :
    map (g' ∘ₗ g) (by rw [← LinearMap.comp_assoc, h', h]) = map g h ≫ map g' h' := by
  ext n : 1
  rw [map_f, HomologicalComplex.comp_f, map_f, map_f, exteriorPower.map_comp]
  exact ModuleCat.ofHom_comp _ _

/-- The isomorphism `K(φ) ≅ K(ψ)` induced by a linear equivalence `e : M ≃ N` with `ψ ∘ e = φ`;
in degree `n` it is `⋀ⁿ e`. -/
def mapIso (e : M ≃ₗ[R] N) (h : ψ ∘ₗ e.toLinearMap = φ) :
    koszulComplex φ ≅ koszulComplex ψ where
  hom := map e.toLinearMap h
  inv := map e.symm.toLinearMap (by rw [← h, LinearMap.comp_assoc, e.comp_symm, LinearMap.comp_id])
  hom_inv_id := by
    rw [← map_comp, ← map_id]
    congr 1
    exact e.symm_comp
  inv_hom_id := by
    rw [← map_comp, ← map_id]
    congr 1
    exact e.comp_symm

/-- The isomorphism induced by a linear equivalence `e` is the chain map induced by `e`. -/
@[simp]
theorem mapIso_hom (e : M ≃ₗ[R] N) (h : ψ ∘ₗ e.toLinearMap = φ) :
    (mapIso e h).hom = map e.toLinearMap h :=
  (rfl)

/-- The inverse of the isomorphism induced by `e` is the chain map induced by `e.symm`. -/
@[simp]
theorem mapIso_inv (e : M ≃ₗ[R] N) (h : ψ ∘ₗ e.toLinearMap = φ) :
    (mapIso e h).inv =
      map e.symm.toLinearMap (by rw [← h, LinearMap.comp_assoc, e.comp_symm, LinearMap.comp_id]) :=
  (rfl)

end Map

section Homotopy

/-- **Koszul homotopy**: for `m : M`, exterior multiplication `v ↦ m ∧ v` is a null-homotopy of
multiplication by `φ(m)` on `K(φ)`; see `koszulDifferential_comp_wedgeLeft_zero` and
`wedgeLeft_comp_koszulDifferential_add`. -/
def smulHomotopy (m : M) : Homotopy (φ m • 𝟙 (koszulComplex φ)) 0 :=
  Homotopy.mkChainComplex _ (fun n ↦ ModuleCat.ofHom (ExteriorAlgebra.wedgeLeft m n))
    (ModuleCat.hom_ext (koszulDifferential_comp_wedgeLeft_zero φ m).symm)
    fun n ↦ by
      rw [koszulComplex_d, koszulComplex_d]
      exact ModuleCat.hom_ext (wedgeLeft_comp_koszulDifferential_add φ m n).symm

/-- The components of the Koszul homotopy are exterior multiplication by `m`. -/
@[simp]
theorem smulHomotopy_hom (m : M) (n : ℕ) :
    (smulHomotopy φ m).hom n (n + 1) = ModuleCat.ofHom (ExteriorAlgebra.wedgeLeft m n) :=
  Homotopy.mkChainComplex_hom_succ _ _ _ _ n

/-- **Every value of `φ` annihilates the Koszul homology**: `φ(m) • z = 0` for every class `z` in
every homology module of `K(φ)`. -/
theorem smul_homology_eq_zero (m : M) (n : ℕ) (z : (koszulComplex φ).homology n) :
    φ m • z = 0 := by
  have h := (smulHomotopy φ m).homologyMap_eq n
  rw [HomologicalComplex.homologyMap_smul, HomologicalComplex.homologyMap_id,
    HomologicalComplex.homologyMap_zero] at h
  simpa using congr(($h).hom z)

end Homotopy

section HomologyZero

/-- `H₀(K(φ))` is the cokernel of the first differential `⋀¹ M → ⋀⁰ M`. -/
def homologyZeroIso :
    (koszulComplex φ).homology 0 ≅
      ModuleCat.of R (⋀[R]^0 M ⧸ LinearMap.range (koszulDifferential φ 0)) :=
  (ChainComplex.isoHomologyι₀ (koszulComplex φ)) ≪≫
    (koszulComplex φ).opcyclesIsoSc' 1 0 0 (by simp) (by simp) ≪≫
      ((koszulComplex φ).sc' 1 0 0).moduleCatOpcyclesIso

private theorem pOpcycles_comp_homologyZeroIso_hom :
    (koszulComplex φ).pOpcycles 0 ≫ (ChainComplex.isoHomologyι₀ (koszulComplex φ)).inv ≫
        (homologyZeroIso φ).hom =
      ModuleCat.ofHom (LinearMap.range (koszulDifferential φ 0)).mkQ := by
  have h := ((koszulComplex φ).pOpcycles_opcyclesIsoSc'_hom_assoc 1 0 0 (by simp) (by simp)
    ((koszulComplex φ).sc' 1 0 0).moduleCatOpcyclesIso.hom).trans
      ((koszulComplex φ).sc' 1 0 0).pOpcycles_comp_moduleCatOpcyclesIso_hom
  simp only [homologyZeroIso, Iso.trans_hom, Iso.inv_hom_id_assoc]
  -- The codomain of `homologyZeroIso` is that of `moduleCatOpcyclesIso` with `sc'` unfolded.
  exact h

/-- **Zeroth Koszul homology**: `H₀(K(φ)) ≃ R ⧸ φ(M)`. It is the cokernel of the first
differential, transported along `⋀⁰ M ≅ R`; see `homologyZeroEquiv_apply`. -/
def homologyZeroEquiv : (koszulComplex φ).homology 0 ≃ₗ[R] R ⧸ LinearMap.range φ :=
  (homologyZeroIso φ).toLinearEquiv ≪≫ₗ
    Submodule.Quotient.equiv _ _ (exteriorPower.zeroEquiv R M)
      (map_zeroEquiv_range_koszulDifferential_zero φ)

/-- `homologyZeroEquiv` sends the class of `x ∈ ⋀⁰ M` to the class of the corresponding scalar. -/
@[simp]
theorem homologyZeroEquiv_apply (x : ⋀[R]^0 M) :
    homologyZeroEquiv φ
        ((ChainComplex.isoHomologyι₀ (koszulComplex φ)).inv.hom (((koszulComplex φ).pOpcycles 0).hom x)) =
      Ideal.Quotient.mk _ (exteriorPower.zeroEquiv R M x) := by
  have hx : (homologyZeroIso φ).hom.hom
      ((ChainComplex.isoHomologyι₀ (koszulComplex φ)).inv.hom (((koszulComplex φ).pOpcycles 0).hom x)) =
      (LinearMap.range (koszulDifferential φ 0)).mkQ x :=
    congr(($(pOpcycles_comp_homologyZeroIso_hom φ)).hom x)
  -- `simp` does not rewrite with `Iso.toLinearEquiv_apply` here, so expose `hx` by `rw` first.
  rw [homologyZeroEquiv, LinearEquiv.trans_apply, Iso.toLinearEquiv_apply, hx]
  simp

/-- **Zeroth Koszul homology of a finite sequence**: for `x = (xᵢ)` in `R`, the Koszul complex of
the functional `v ↦ ∑ᵢ vᵢ xᵢ` has `H₀ ≃ R ⧸ (xᵢ)`. -/
def homologyZeroEquivSpan {ι : Type*} [Fintype ι] (x : ι → R) :
    (koszulComplex (Fintype.linearCombination R x)).homology 0 ≃ₗ[R]
      R ⧸ Ideal.span (Set.range x) :=
  homologyZeroEquiv _ ≪≫ₗ Submodule.quotEquivOfEq _ _ (Fintype.range_linearCombination R x)

/-- `homologyZeroEquivSpan` sends the class of `y ∈ ⋀⁰ Rⁿ` to the class of the corresponding
scalar modulo `(xᵢ)`. -/
@[simp]
theorem homologyZeroEquivSpan_apply {ι : Type*} [Fintype ι] (x : ι → R)
    (y : ⋀[R]^0 (ι → R)) :
    homologyZeroEquivSpan x
        ((ChainComplex.isoHomologyι₀ (koszulComplex (Fintype.linearCombination R x))).inv.hom
          (((koszulComplex (Fintype.linearCombination R x)).pOpcycles 0).hom y)) =
      Ideal.Quotient.mk _ (exteriorPower.zeroEquiv R (ι → R) y) := by
  simpa [homologyZeroEquivSpan] using Submodule.quotEquivOfEq_mk _ _
    (Fintype.range_linearCombination R x) (exteriorPower.zeroEquiv R (ι → R) y)

end HomologyZero

end koszulComplex

end TauCeti

end
end
end CheckedSource13

/-! ## Source: TauCeti.Algebra.Ring.Subgroup -/
section CheckedSource14
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Additive closures in rings

This file gives criteria for the additive closure of a set in a ring to be closed under
multiplication, and hence to coincide with the underlying additive subgroup of the subring
generated by that set.

## Main results

* `TauCeti.AddSubgroup.mul_mem_closure_of_mul_mem`: products of elements of an additive closure
  remain in the closure when this holds for its generators.
* `AddSubgroup.closure_mul_closure`: the product of two additive closures is the additive
  closure of the pairwise products.
* `Subring.toAddSubgroup_closure_of_one_mem_of_mul_mem`: under the corresponding
  hypotheses, the subring and additive-subgroup closures have the same underlying additive group.
* `AddSubgroup.multiplierRing`: the subring of elements `x` with `x W ⊆ W`, for an additive
  subgroup `W` of a ring.
-/

section

open scoped Pointwise

namespace TauCeti

variable {R : Type*} [NonUnitalNonAssocRing R]

/-- The product of two additive closures is the additive closure of the pairwise products.

This is the additive-subgroup analogue of `AddSubmonoid.closure_mul_closure` from
`Mathlib.Algebra.Ring.Submonoid.Pointwise`. -/
theorem _root_.AddSubgroup.closure_mul_closure (S T : Set R) :
    AddSubgroup.closure S * AddSubgroup.closure T = AddSubgroup.closure (S * T) := by
  apply AddSubgroup.toAddSubmonoid_injective
  simp only [AddSubgroup.mul_toAddSubmonoid, AddSubgroup.closure_toAddSubmonoid,
    AddSubmonoid.closure_union, AddSubmonoid.closure_neg,
    AddSubmonoid.sup_mul, AddSubmonoid.mul_sup, AddSubmonoid.closure_mul_closure,
    neg_mul, mul_neg, AddSubmonoid.neg_sup, neg_neg, sup_idem, sup_comm]

/-- If products of generators lie in their additive closure, then that additive closure is
closed under multiplication. -/
theorem AddSubgroup.mul_mem_closure_of_mul_mem {R : Type*} [NonUnitalNonAssocRing R] {s : Set R}
    (hs : ∀ x ∈ s, ∀ y ∈ s, x * y ∈ AddSubgroup.closure s) {x y : R}
    (hx : x ∈ AddSubgroup.closure s) (hy : y ∈ AddSubgroup.closure s) :
    x * y ∈ AddSubgroup.closure s := by
  induction hx, hy using AddSubgroup.closure_induction₂ with
  | mem x y hx hy => exact hs x hx y hy
  | zero_left => simp
  | zero_right => simp
  | add_left _ _ _ _ _ _ hx hy => simpa [add_mul] using AddSubgroup.add_mem _ hx hy
  | add_right _ _ _ _ _ _ hx hy => simpa [mul_add] using AddSubgroup.add_mem _ hx hy
  | neg_left _ _ _ _ hx => simpa [neg_mul] using AddSubgroup.neg_mem _ hx
  | neg_right _ _ _ _ hx => simpa [mul_neg] using AddSubgroup.neg_mem _ hx

/-- If the additive closure of a set contains one and products of generators lie in that closure,
then it is the underlying additive subgroup of the subring closure of the set. -/
theorem _root_.Subring.toAddSubgroup_closure_of_one_mem_of_mul_mem {R : Type*} [NonAssocRing R]
    {s : Set R}
    (h1 : (1 : R) ∈ AddSubgroup.closure s)
    (hmul : ∀ x ∈ s, ∀ y ∈ s, x * y ∈ AddSubgroup.closure s) :
    (Subring.closure s).toAddSubgroup = AddSubgroup.closure s := by
  refine le_antisymm (fun x hx => ?_) ((AddSubgroup.closure_le _).2 fun x hx => ?_)
  · rw [Subring.mem_toAddSubgroup] at hx
    induction hx using Subring.closure_induction with
    | mem x hx => exact AddSubgroup.subset_closure hx
    | zero => exact zero_mem _
    | one => exact h1
    | add _ _ _ _ hx hy => exact add_mem hx hy
    | neg _ _ hx => exact neg_mem hx
    | mul _ _ _ _ hx hy => exact AddSubgroup.mul_mem_closure_of_mul_mem hmul hx hy
  · exact Subring.mem_toAddSubgroup.2 (Subring.subset_closure hx)

/-- The *multiplier ring* of an additive subgroup `W` of a ring: the elements `x` with `x W ⊆ W`,
that is, the transporter of `W` into itself under left multiplication. It is a subring even when
`W` is not. -/
def _root_.AddSubgroup.multiplierRing {R : Type*} [Ring R] (W : AddSubgroup R) : Subring R where
  carrier := {x | ∀ z ∈ W, x * z ∈ W}
  one_mem' z hz := by rwa [one_mul]
  mul_mem' hx hy z hz := by
    rw [mul_assoc]
    exact hx _ (hy z hz)
  zero_mem' z _ := by
    rw [zero_mul]
    exact zero_mem W
  add_mem' hx hy z hz := by
    rw [add_mul]
    exact add_mem (hx z hz) (hy z hz)
  neg_mem' hx z hz := by
    rw [neg_mul]
    exact neg_mem (hx z hz)

@[simp]
theorem _root_.AddSubgroup.mem_multiplierRing {R : Type*} [Ring R] {W : AddSubgroup R} {x : R} :
    x ∈ W.multiplierRing ↔ ∀ z ∈ W, x * z ∈ W :=
  Iff.rfl

end TauCeti

end
end CheckedSource14

/-! ## Source: TauCeti.RingTheory.Ideal.Operations -/
section CheckedSource15
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/



/-!
# Complements on ideal multiplication and the ideal action

This file collects general facts about the multiplication of ideals and about the action `I • N`
of an ideal on a module, complementing `Mathlib/RingTheory/Ideal/Operations.lean`.

## Main results

* `Ideal.eq_one_of_mul_eq_one`: a two-sided left factor of the unit ideal is the unit ideal.
  Over a commutative semiring, this implies that the divisor antidiagonal of the unit ideal
  is a singleton.
* `Ideal.toAddSubgroup_mul_eq_closure_mul`: additive generators of a product of ideals.
* `Ideal.smul_top_eq_top_of_pi`: an ideal that expands the whole of a product of modules expands
  the whole of every factor.
* `Ideal.smul_top_eq_comap_mul`: the action on an ideal identifies its product submodule.
* `Ideal.smul_top_eq_top_of_isIdempotentElem`: an idempotent ideal `I` satisfies `I • I = I`.
* `Ideal.span_range_fin_two_eq_top_iff`: a pair generates the unit ideal exactly when its entries
  are coprime.
* `LinearMap.apply_mem_of_mem_smul_top`: a linear functional carries `I • M` into `I`.
* `Module.Basis.mem_smul_top_iff`: for a module with a basis, `I • M` consists of the vectors
  whose coordinates all lie in `I`.
* `Ideal.span_insert_eq_top_of_subset`: a generating set `S` may be replaced by a set `S'`, both
  taken together with a common element `a`, as soon as every element of `S` is `a` itself or
  belongs to `S'`.
* `IsSMulRegular.of_span_singleton_le`: if a regular element belongs to the principal ideal
  generated by another element, then the latter is regular.
* `Ideal.span_pair_sq_eq_span_singleton_of_isCoprime`: if `x ^ 2 = z m` with `z` and `m`
  coprime, then `(z, x) ^ 2 = (z)`.
* `IsSMulRegular.span_singleton_mul_right_mono` and
  `IsSMulRegular.span_singleton_mul_right_inj`: multiplication by the principal ideal of a regular
  element preserves and reflects inclusion and equality of ideals.
* `Ideal.span_singleton_pow_sup_span_singleton_pow`: the left ideals generated by `a ^ j` and
  `a ^ m` have as supremum the left ideal generated by `a ^ min j m`.
* `Ideal.sup_pow_le_sup_pow_right`: modulo a two-sided ideal `I`, powers of
  `I ⊔ J` are controlled by the corresponding power of the left ideal `J`.
* `Ideal.span_pair_pow_eq_span_singleton`: if `z (1 - t) = x ^ n` with `t ∈ (x, z)` and
  the left ideals `(x, z)` and `(z)` are two-sided, then `(x, z) ^ n = (z)`.
* `Ideal.isTwoSided_span_of_subset_center`: a left ideal spanned by central elements is two-sided.
* `Ideal.coe_span_subset_of_forall_mul_mem`: a left ideal lies in an additive submonoid containing
  every left multiple of its generators.
* `Submodule.mem_span_algebraMap_smul_iff`: over an algebra `A`, the action on a submodule `N` of
  the left ideal spanned by a scalar `x` produces exactly the multiples `x • w` with `w ∈ N`.
* `Submodule.mem_span_range_smul_top_iff_exists_fun`: the action on `M` of the ideal generated by
  finitely many elements `fᵢ` produces exactly the sums `∑ fᵢ • mᵢ`.
* `Subalgebra.toSubmodule_sup_pow_restrictScalars_eq_top`: if a subalgebra and a principal left
  ideal additively span the ambient algebra, and the subalgebra contains a generator of the
  ideal, then the same holds with the ideal replaced by any power.
-/

section

open scoped Pointwise

namespace Ideal

variable {R : Type*} [Ring R] {I J : Ideal R} {S T : Set R}

/-- If `S` and `T` additively generate the ideals `I` and `J`, then their pairwise products
additively generate `I * J`. -/
theorem toAddSubgroup_mul_eq_closure_mul
    (hI : I.toAddSubgroup = AddSubgroup.closure S)
    (hJ : J.toAddSubgroup = AddSubgroup.closure T) :
    (I * J).toAddSubgroup = AddSubgroup.closure (S * T) := by
  apply AddSubgroup.toAddSubmonoid_injective
  rw [Submodule.toAddSubgroup_toAddSubmonoid, _root_.Submodule.mul_toAddSubmonoid,
    ← Submodule.toAddSubgroup_toAddSubmonoid I, ← Submodule.toAddSubgroup_toAddSubmonoid J,
    hI, hJ, ← _root_.AddSubgroup.mul_toAddSubmonoid,
    AddSubgroup.closure_mul_closure]

section Mul

variable {R : Type*} [Semiring R] {I J : Ideal R}

/-- If a two-sided ideal times a left ideal is the unit ideal, then the first ideal is the
unit ideal. -/
theorem eq_one_of_mul_eq_one [I.IsTwoSided] (h : I * J = 1) : I = 1 := by
  rw [Ideal.one_eq_top] at h ⊢
  exact eq_top_mono Ideal.mul_le_left h

end Mul

section CommSemiring

variable {R : Type*} [CommSemiring R]

/-- The product `I * J`, viewed as a submodule of `I`, is the action of `J` on `I`. -/
theorem smul_top_eq_comap_mul (I J : Ideal R) :
    J • (⊤ : Submodule R I) = Submodule.comap I.subtype (I * J) := by
  ext x
  simp only [Submodule.mem_smul_top_iff, Submodule.mem_comap, Submodule.coe_subtype,
    Ideal.smul_eq_mul, mul_comm J I]

/-- If `I * I = I`, then `I • I = I`: every element of `I` is a sum of products of two elements
of `I`. -/
theorem smul_top_eq_top_of_isIdempotentElem {I : Ideal R} (hI : IsIdempotentElem I) :
    I • (⊤ : Submodule R I) = ⊤ := by
  apply Submodule.map_injective_of_injective I.injective_subtype
  rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype, Ideal.smul_eq_mul, hI.eq]

/-- The two entries of a pair generate the unit ideal exactly when they are coprime. -/
theorem span_range_fin_two_eq_top_iff (v : Fin 2 → R) :
    span (Set.range v) = ⊤ ↔ IsCoprime (v 0) (v 1) := by
  have hv : Set.range v = {v 0, v 1} := by
    ext x
    simp [Fin.exists_fin_two, eq_comm]
  rw [hv, span_insert, sup_eq_top_iff_isCoprime]

end CommSemiring

section Pi

variable {R : Type*} [Semiring R] {ι : Type*} {M : ι → Type*} [∀ i, AddCommMonoid (M i)]
    [∀ i, Module R (M i)]

/-- **Expanding a product expands every factor**: if `I • ⊤ = ⊤` in `∀ i, M i` then `I • ⊤ = ⊤` in
each `M i`. Thus properness of `I • ⊤` in one factor implies properness in the product. -/
theorem smul_top_eq_top_of_pi (I : Ideal R) (h : I • (⊤ : Submodule R (∀ i, M i)) = ⊤) (i : ι) :
    I • (⊤ : Submodule R (M i)) = ⊤ := by
  have := congrArg (Submodule.map (LinearMap.proj (R := R) (φ := M) i)) h
  rwa [Submodule.map_smul'', Submodule.map_top,
    LinearMap.range_eq_top.mpr (Function.surjective_eval i)] at this

end Pi

end Ideal

namespace Submodule

variable {R A V : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [AddCommMonoid V]
  [Module R V] [Module A V] [IsScalarTower R A V]

/-- For an `R`-algebra `A`, possibly noncommutative, the action on a submodule `N` of the
left ideal spanned by a scalar `x : R` consists of the multiples `x • w` with `w ∈ N`.
This extends the membership criterion from `Submodule.ideal_span_singleton_smul` to
noncommutative algebras. -/
theorem mem_span_algebraMap_smul_iff (N : Submodule A V) (x : R) {v : V} :
    v ∈ Ideal.span {algebraMap R A x} • N ↔ ∃ w ∈ N, x • w = v := by
  constructor
  · intro hv
    refine Submodule.smul_induction_on hv (fun r hr w hw ↦ ?_)
      fun _ _ ⟨w, hw, h⟩ ⟨w', hw', h'⟩ ↦
        ⟨w + w', N.add_mem hw hw', by rw [smul_add, h, h']⟩
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    exact ⟨a • w, N.smul_mem a hw, by rw [mul_smul, algebraMap_smul, smul_comm]⟩
  · rintro ⟨w, hw, rfl⟩
    rw [← algebraMap_smul A]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hw

end Submodule

namespace Submodule

variable {R M ι : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [Fintype ι]

/-- The elements of `(f₁, …, f_r) M` are exactly the sums `∑ fᵢ mᵢ` with `mᵢ ∈ M`. -/
theorem mem_span_range_smul_top_iff_exists_fun {f : ι → R} {x : M} :
    x ∈ Ideal.span (Set.range f) • (⊤ : Submodule R M) ↔ ∃ m : ι → M, ∑ i, f i • m i = x := by
  rw [span_smul_eq, ← LinearMap.range_id, ← range_lsum_smul, LinearMap.mem_range,
    Finsupp.equivFunOnFinite.exists_congr_left]
  simp [Finsupp.sum_fintype]

end Submodule

namespace IsSMulRegular

variable {R : Type*} [Semiring R] {a b : R}

/-- If a regular element `b` belongs to the principal ideal generated by `a`, then `a` is regular.
Equivalently, regularity descends along an inclusion `(b) ⊆ (a)` of principal left ideals. -/
theorem of_span_singleton_le (hb : IsSMulRegular R b) (h : Ideal.span {b} ≤ Ideal.span {a}) :
    IsSMulRegular R a := by
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp (h (Ideal.mem_span_singleton_self b))
  rw [← hr] at hb
  exact hb.of_mul

/-- Multiplication by the principal ideal of a regular element preserves and reflects
inclusion of ideals. This generalizes `Ideal.span_singleton_mul_right_mono`, which assumes
a domain and a nonzero element. -/
theorem span_singleton_mul_right_mono {R : Type*} [CommSemiring R] {a : R}
    (ha : IsSMulRegular R a) {I J : Ideal R} :
    Ideal.span {a} * I ≤ Ideal.span {a} * J ↔ I ≤ J := by
  constructor
  · intro h x hx
    obtain ⟨y, hy, hyx⟩ := (Submodule.mem_span_algebraMap_smul_iff J a).mp (by
      simpa only [Algebra.algebraMap_self_apply, Ideal.smul_eq_mul] using
        h (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self a) hx))
    exact ha hyx ▸ hy
  · exact Ideal.mul_mono_right

/-- Multiplication by the principal ideal of a regular element is injective on ideals. This
generalizes `Ideal.span_singleton_mul_right_inj`, which assumes a domain and a nonzero element. -/
theorem span_singleton_mul_right_inj {R : Type*} [CommSemiring R] {a : R}
    (ha : IsSMulRegular R a) {I J : Ideal R} :
    Ideal.span {a} * I = Ideal.span {a} * J ↔ I = J := by
  simp only [le_antisymm_iff, ha.span_singleton_mul_right_mono]

end IsSMulRegular

namespace Ideal

section Span

variable {R : Type*} [Semiring R] {a : R} {S S' : Set R}

/-- **Replacing one generating set by another**: if every element of `S` is either `a` itself or an
element of `S'`, then `S'` together with `a` generates the unit ideal as soon as `S` together with
`a` does. Note that `S'` need not be contained in `S`, and may be larger: the hypothesis constrains
only where the elements of `S` are found. Both spans contain `a`, so only the rest of `S` has to be
accounted for. -/
theorem span_insert_eq_top_of_subset (hsub : S ⊆ insert a S')
    (hspan : Ideal.span (insert a S) = ⊤) : Ideal.span (insert a S') = ⊤ :=
  eq_top_mono (Ideal.span_mono <| Set.insert_subset (Set.mem_insert _ _) hsub) hspan

/-- The left ideals generated by two powers of the same element have as supremum the left ideal
generated by the smaller power. -/
theorem span_singleton_pow_sup_span_singleton_pow (a : R) (j m : ℕ) :
    span {a ^ j} ⊔ span {a ^ m} = span {a ^ min j m} := by
  rcases le_total j m with h | h
  · rw [min_eq_left h, sup_eq_left, span_singleton_le_iff_mem, mem_span_singleton']
    exact ⟨a ^ (m - j), pow_sub_mul_pow a h⟩
  · rw [min_eq_right h, sup_eq_right, span_singleton_le_iff_mem, mem_span_singleton']
    exact ⟨a ^ (j - m), pow_sub_mul_pow a h⟩

/-- A left ideal lies in an additive submonoid `U` as soon as every left multiple of each of its
generators lies in `U`. -/
theorem coe_span_subset_of_forall_mul_mem {U : AddSubmonoid R} (h : ∀ x ∈ S, ∀ r : R, r * x ∈ U) :
    (span S : Set R) ⊆ U := by
  intro y hy
  have hy' : y ∈ (Submodule.span R S).toAddSubmonoid := hy
  rw [Submodule.span_eq_closure] at hy'
  refine (AddSubmonoid.closure_le (S := U)).mpr ?_ hy'
  rintro _ ⟨r, -, x, hx, rfl⟩
  exact h x hx r

variable {A : Type*} [Semiring A] {s : Set A}

/-- A left ideal spanned by central elements is two-sided. -/
theorem isTwoSided_span_of_subset_center (hs : s ⊆ Set.center A) :
    (Ideal.span s).IsTwoSided where
  mul_mem_of_left b hz := by
    refine Submodule.span_induction (p := fun z _ ↦ z * b ∈ Ideal.span s)
      (fun z hz ↦ ?_) (by simp) (fun x y _ _ hx hy ↦ ?_)
      (fun c x _ hx ↦ ?_) hz
    · rw [← (Semigroup.mem_center_iff.mp (hs hz) b)]
      exact Ideal.mul_mem_left _ b (Ideal.subset_span hz)
    · rw [add_mul]
      exact Ideal.add_mem _ hx hy
    · rw [smul_eq_mul, mul_assoc]
      exact Ideal.mul_mem_left _ c hx

end Span

end Ideal

namespace LinearMap

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- A linear functional `f : M → R` carries `I • M` into the ideal `I`: the ideal action on `R`
itself is multiplication, and `f` is linear over it. -/
theorem apply_mem_of_mem_smul_top (f : M →ₗ[R] R) {I : Ideal R} [I.IsTwoSided] {x : M}
    (hx : x ∈ I • (⊤ : Submodule R M)) : f x ∈ I := by
  have := Submodule.smul_top_le_comap_smul_top I f hx
  rwa [Submodule.mem_comap, smul_eq_mul, Ideal.mul_top] at this

end LinearMap

namespace Module.Basis

variable {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- For a module with a basis `b`, a vector lies in `I • M` exactly when all of its coordinates
lie in the ideal `I`. -/
theorem mem_smul_top_iff (b : Basis ι R M) {I : Ideal R} [I.IsTwoSided] {x : M} :
    x ∈ I • (⊤ : Submodule R M) ↔ ∀ i, b.repr x i ∈ I := by
  refine ⟨fun hx i ↦ LinearMap.apply_mem_of_mem_smul_top (b.coord i) hx, fun hx ↦ ?_⟩
  rw [← b.linearCombination_repr x, Finsupp.linearCombination_apply]
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem_smul (hx i) Submodule.mem_top

end Module.Basis

universe u

/-- A supremum of two two-sided ideals is two-sided. -/
instance (priority := low) Ideal.isTwoSided_sup {R : Type u} [Semiring R] (I J : Ideal R)
    [I.IsTwoSided] [J.IsTwoSided] : (I ⊔ J).IsTwoSided where
  mul_mem_of_left b ha := by
    obtain ⟨i, hi, j, hj, rfl⟩ := Submodule.mem_sup.mp ha
    rw [add_mul]
    exact Submodule.add_mem _ (Ideal.mem_sup_left (I.mul_mem_right b hi))
      (Ideal.mem_sup_right (J.mul_mem_right b hj))

/-- The `n`-th power of the supremum of a two-sided ideal and a left ideal is contained in
the first ideal plus the `n`-th power of the second. -/
theorem Ideal.sup_pow_le_sup_pow_right {R : Type u} [Semiring R] (I J : Ideal R)
    [I.IsTwoSided] (n : ℕ) :
    (I ⊔ J) ^ n ≤ I ⊔ J ^ n := by
  induction n with
  | zero =>
      rw [Submodule.pow_zero, Submodule.pow_zero]
      exact le_sup_right
  | succ n ih =>
      rw [Submodule.pow_succ, Submodule.pow_succ]
      refine (Ideal.mul_mono_left ih).trans ?_
      rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
      exact sup_le
        (sup_le (Ideal.mul_le_left.trans le_sup_left)
          (Ideal.mul_le_left.trans le_sup_left))
        (sup_le (Ideal.mul_le_right.trans le_sup_left) le_sup_right)

/-- **A pair generating a power of one of its members.** If the left ideals `(x, z)` and
`(z)` are two-sided and `z (1 - t) = x ^ n` for some `t` in `(x, z)`, then `(x, z) ^ n = (z)`.
The two-sidedness hypotheses hold automatically in a commutative ring.
Modulo `z`, the ideal `(x, z)` becomes `(x)`, whose `n`-th power vanishes; conversely
`z = x ^ n (1 + t + ⋯ + t ^ (n - 1)) + z t ^ n`. -/
theorem Ideal.span_pair_pow_eq_span_singleton {R : Type u} [Ring R] {x z t : R} {n : ℕ}
    [(Ideal.span {x, z}).IsTwoSided] [(Ideal.span {z}).IsTwoSided]
    (hz : z * (1 - t) = x ^ n) (ht : t ∈ Ideal.span {x, z}) :
    Ideal.span {x, z} ^ n = Ideal.span {z} := by
  refine le_antisymm ?_ ?_
  · have hpow (k : ℕ) : Ideal.span {x, z} ^ k ≤ Ideal.span {x ^ k} ⊔ Ideal.span {z} := by
      induction k with
      | zero => simp [Submodule.pow_zero]
      | succ k ih =>
        calc Ideal.span {x, z} ^ (k + 1) =
            Ideal.span {x, z} ^ k * (Ideal.span {x} ⊔ Ideal.span {z}) := by
              rw [Submodule.pow_succ, ← Ideal.span_insert]
          _ = Ideal.span {x, z} ^ k * Ideal.span {x} ⊔
              Ideal.span {x, z} ^ k * Ideal.span {z} := Ideal.mul_sup _ _ _
          _ ≤ Ideal.span {x ^ (k + 1)} ⊔ Ideal.span {z} := by
            refine sup_le ?_ (Ideal.mul_le_right.trans le_sup_right)
            intro y hy
            obtain ⟨a, ha, rfl⟩ := Ideal.mem_mul_span_singleton.mp hy
            obtain ⟨b, hb, c, hc, rfl⟩ := Submodule.mem_sup.mp (ih ha)
            obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hb
            rw [add_mul, mul_assoc, ← pow_succ]
            exact add_mem
              (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
              (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ hc))
    refine (hpow n).trans (sup_le ?_ le_rfl)
    rw [Ideal.span_singleton_le_iff_mem, ← hz]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self z)
  · have hz' : x ^ n * ∑ i ∈ Finset.range n, t ^ i + z * t ^ n = z := by
      rw [← hz, mul_assoc, mul_neg_geom_sum]
      simp [mul_sub]
    have hxm : x ∈ Ideal.span {x, z} := Ideal.subset_span (Set.mem_insert x _)
    rw [Ideal.span_singleton_le_iff_mem]
    suffices x ^ n * ∑ i ∈ Finset.range n, t ^ i + z * t ^ n ∈ Ideal.span {x, z} ^ n by
      rwa [hz'] at this
    exact add_mem (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hxm n))
      (Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow ht n))

/-- **A pair whose square is principal.** In a commutative semiring, if `x ^ 2 = z m` with `z`
and `m` coprime, then `(z, x) ^ 2 = (z)`. For a squarefree integer `d = p m` with `p` prime,
applied to a square root `x` of `d`, this is the ramified factorization `(p) = (p, √d) ^ 2`. -/
theorem Ideal.span_pair_sq_eq_span_singleton_of_isCoprime {R : Type u} [CommSemiring R]
    {z x m : R} (hx : x ^ 2 = z * m) (hm : IsCoprime z m) :
    Ideal.span {z, x} ^ 2 = Ideal.span {z} := by
  refine le_antisymm ?_ ?_
  · rw [sq, Ideal.span_pair_mul_span_pair, Ideal.span_le]
    rintro y (rfl | rfl | rfl | rfl)
    · exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self z)
    · exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self z)
    · exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self z)
    · rw [← sq, hx]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self z)
  · obtain ⟨u, v, huv⟩ := hm
    have hz : z = u * z ^ 2 + v * x ^ 2 := by
      rw [hx]
      calc z = z * (u * z + v * m) := by rw [huv, mul_one]
        _ = u * z ^ 2 + v * (z * m) := by ring
    have hzI : z ∈ Ideal.span {z, x} := Ideal.subset_span (Set.mem_insert z _)
    have hxI : x ∈ Ideal.span {z, x} := Ideal.subset_span (by simp)
    have h := add_mem (Ideal.mul_mem_left _ u (Ideal.pow_mem_pow hzI 2))
      (Ideal.mul_mem_left _ v (Ideal.pow_mem_pow hxI 2))
    rwa [← hz, ← Ideal.span_singleton_le_iff_mem] at h

namespace Subalgebra

variable {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]

/-- If every element of `S` is a sum of an element of a subalgebra `T` and an element of a
principal left ideal `I`, and `T` contains a generator of `I`, then the same holds with `I`
replaced by any power. -/
theorem toSubmodule_sup_pow_restrictScalars_eq_top {T : Subalgebra R S} {I : Ideal S} {π : S}
    (hπ : Ideal.span {π} = I) (hπT : π ∈ T)
    (h : T.toSubmodule ⊔ I.restrictScalars R = ⊤) (n : ℕ) :
    T.toSubmodule ⊔ (I ^ n).restrictScalars R = ⊤ := by
  subst I
  induction n with
  | zero => simp [Submodule.pow_zero, Ideal.one_eq_top]
  | succ n ih =>
    refine eq_top_iff.mpr fun s _ => ?_
    obtain ⟨t, ht, m, hm, rfl⟩ := Submodule.mem_sup.mp (h.ge Submodule.mem_top : s ∈ _)
    obtain ⟨u, rfl⟩ : ∃ u, u * π = m := by
      rw [Submodule.restrictScalars_mem, Ideal.mem_span_singleton'] at hm
      exact hm
    obtain ⟨t', ht', m', hm', rfl⟩ := Submodule.mem_sup.mp (ih.ge Submodule.mem_top : u ∈ _)
    refine Submodule.mem_sup.mpr ⟨t + t' * π, ?_, m' * π, ?_, by
      simp only [add_mul, add_assoc]⟩
    · rw [Subalgebra.mem_toSubmodule] at ht ht' ⊢
      exact add_mem ht (mul_mem ht' hπT)
    · rw [Submodule.restrictScalars_mem, Submodule.pow_succ]
      exact Ideal.mul_mem_mul hm' (Ideal.mem_span_singleton_self _)

end Subalgebra

end

end CheckedSource15

/-! ## Source: TauCeti.RingTheory.KoszulComplex.Basis -/
section CheckedSource16
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The Koszul differential in a basis

Let `M` be a free module with basis `(bᵢ)` and let `φ : M → R` be a linear functional. In the
exterior-power basis, the contraction by the coordinate `bᵢ*` deletes the index `i`, so the Koszul
differential of `φ` is `d(z) = ∑ᵢ φ(bᵢ) ιᵢ(z)` with `ιᵢ` the contraction by `bᵢ*`. The family of
all contractions `z ↦ (ιᵢ(z))ᵢ` is the linearized Koszul differential `⋀ⁿ⁺¹ M → ⋀ⁿ M ⊗ M`, and it
is split injective coordinatewise: the coordinate of `z` at an index set `s ∋ i` is, up to sign,
the coordinate of `ιᵢ(z)` at `s \ {i}`. Hence for every ideal `I`, an element `z` of positive
degree lies in `I • ⋀ M` exactly when all its contractions `ιᵢ(z)` do.

## Main results

* `Module.Basis.koszulDifferential_eq_sum`: the Koszul differential of `φ` is `∑ᵢ φ(bᵢ) ιᵢ`.
* `Module.Basis.koszulDifferential_coord_exteriorPower_basis_of_mem` and
  `Module.Basis.koszulDifferential_coord_exteriorPower_basis_of_notMem`: contraction by a
  coordinate on the exterior-power basis.
* `Module.Basis.exteriorPower_basis_repr_koszulDifferential_coord`: the coordinates of a
  contraction.
* `Module.Basis.mem_smul_top_iff_forall_koszulDifferential_coord_mem`: an element of positive
  degree lies in `I • ⋀ M` exactly when all its coordinate contractions do.

## References

* [The Stacks Project, Lemma 10.110.3](https://stacks.math.columbia.edu/tag/00OA)
-/

section

noncomputable section

universe u v

open CliffordAlgebra TauCeti

namespace Module.Basis

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {ι : Type*}

/-- The Koszul differential of `φ` is the combination of the contractions by the coordinates of a
finite basis, with coefficients `φ(bᵢ)`: `d(z) = ∑ᵢ φ(bᵢ) ιᵢ(z)`. -/
theorem koszulDifferential_eq_sum [Fintype ι] (b : Module.Basis ι R M) (φ : Module.Dual R M)
    (n : ℕ) (z : ⋀[R]^(n + 1) M) :
    koszulDifferential φ n z = ∑ i, φ (b i) • koszulDifferential (b.coord i) n z := by
  apply Subtype.ext
  rw [coe_koszulDifferential_apply, Submodule.coe_sum]
  conv_lhs => rw [← b.sum_dual_apply_smul_coord φ]
  rw [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_smul, LinearMap.smul_apply, Submodule.coe_smul, coe_koszulDifferential_apply]

section Basis

variable [LinearOrder ι] (b : Module.Basis ι R M) {n : ℕ}

/-- Contraction by the coordinate `bᵢ*` erases `i` from an exterior-basis vector whose index set
contains it, with the shuffle sign that moves `i` to the front. -/
theorem koszulDifferential_coord_exteriorPower_basis_of_mem {i : ι}
    {s : Set.powersetCard ι (n + 1)} (h : i ∈ s.val) :
    koszulDifferential (b.coord i) n (b.exteriorPower (n + 1) s) =
      ExteriorAlgebra.basisEraseSign i s.val •
        b.exteriorPower n (Set.powersetCard.ofCard (s := s.val.erase i)
          (by simp [Finset.card_erase_of_mem h, Set.powersetCard.card_eq])) := by
  apply Subtype.ext
  rw [coe_koszulDifferential_apply, ← _root_.ExteriorAlgebra.basis_eq_coe_basis,
    ExteriorAlgebra.contractLeft_coord_basis]
  simp only [h, ↓reduceIte, Submodule.coe_smul_of_tower]
  rw [← _root_.ExteriorAlgebra.basis_eq_coe_basis, Set.powersetCard.val_ofCard]

/-- Contraction by the coordinate `bᵢ*` kills an exterior-basis vector whose index set does not
contain `i`. -/
theorem koszulDifferential_coord_exteriorPower_basis_of_notMem {i : ι}
    {s : Set.powersetCard ι (n + 1)} (h : i ∉ s.val) :
    koszulDifferential (b.coord i) n (b.exteriorPower (n + 1) s) = 0 := by
  apply Subtype.ext
  rw [coe_koszulDifferential_apply, ← _root_.ExteriorAlgebra.basis_eq_coe_basis,
    ExteriorAlgebra.contractLeft_coord_basis]
  simp [h]

/-- The coordinates of a contraction: for `i ∈ s`, the coordinate of `ιᵢ(z)` at `s \ {i}` is the
coordinate of `z` at `s`, up to the shuffle sign moving `i` to the front of `s`. -/
theorem exteriorPower_basis_repr_koszulDifferential_coord (z : ⋀[R]^(n + 1) M)
    {i : ι} {s : Set.powersetCard ι (n + 1)} (h : i ∈ s.val) :
    (b.exteriorPower n).repr (koszulDifferential (b.coord i) n z)
        (Set.powersetCard.ofCard (s := s.val.erase i)
          (by simp [Finset.card_erase_of_mem h, Set.powersetCard.card_eq])) =
      ExteriorAlgebra.basisEraseSign i s.val • (b.exteriorPower (n + 1)).repr z s := by
  -- Both sides are linear in `z`; compare them on the exterior basis.
  let t' : Set.powersetCard ι n := Set.powersetCard.ofCard (s := s.val.erase i)
    (by simp [Finset.card_erase_of_mem h, Set.powersetCard.card_eq])
  suffices hcoord : (b.exteriorPower n).coord t' ∘ₗ koszulDifferential (b.coord i) n =
      ExteriorAlgebra.basisEraseSign i s.val • (b.exteriorPower (n + 1)).coord s by
    simpa only [LinearMap.comp_apply, LinearMap.smul_apply, Module.Basis.coord_apply] using
      LinearMap.congr_fun hcoord z
  refine (b.exteriorPower (n + 1)).ext fun t ↦ ?_
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_apply]
  by_cases hit : i ∈ t.val
  · rw [koszulDifferential_coord_exteriorPower_basis_of_mem b hit, map_zsmul_unit,
      Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
    -- Erasing `i` is injective on the index sets containing `i`.
    have heq : (Set.powersetCard.ofCard (s := t.val.erase i)
        (by simp [Finset.card_erase_of_mem hit, Set.powersetCard.card_eq]) = t') ↔ t = s := by
      simp only [Subtype.ext_iff, t', Set.powersetCard.val_ofCard]
      exact ⟨fun he ↦ Finset.erase_injOn' i hit h he, fun he ↦ by rw [he]⟩
    by_cases hts : t = s
    · subst hts
      simp [t']
    · simp [heq.not.mpr hts, hts]
  · have hts : t ≠ s := fun hts ↦ hit (hts ▸ h)
    rw [koszulDifferential_coord_exteriorPower_basis_of_notMem b hit]
    simp [hts]

end Basis

/-- **The linearized Koszul differential is injective modulo every ideal.** For a module with a
basis `(bᵢ)`, an element `z` of positive exterior degree lies in `I • ⋀ M` exactly when its
contractions by all coordinates `bᵢ*` do. -/
theorem mem_smul_top_iff_forall_koszulDifferential_coord_mem (b : Module.Basis ι R M)
    (I : Ideal R) {n : ℕ} (z : ⋀[R]^(n + 1) M) :
    z ∈ I • (⊤ : Submodule R (⋀[R]^(n + 1) M)) ↔
      ∀ i, koszulDifferential (b.coord i) n z ∈ I • (⊤ : Submodule R (⋀[R]^n M)) := by
  refine ⟨fun hz i ↦ Submodule.smul_top_le_comap_smul_top I _ hz, fun h ↦ ?_⟩
  -- The exterior-power basis needs an order on the indices; any one will do.
  let : LinearOrder ι := IsWellOrder.linearOrder WellOrderingRel
  rw [(b.exteriorPower (n + 1)).mem_smul_top_iff]
  intro s
  obtain ⟨i, hi⟩ : s.val.Nonempty := Finset.card_pos.mp (by simp [Set.powersetCard.card_eq])
  have hmem := (b.exteriorPower n).mem_smul_top_iff.mp (h i)
    (Set.powersetCard.ofCard (s := s.val.erase i) (by simp [Finset.card_erase_of_mem hi,
      Set.powersetCard.card_eq]))
  rw [b.exteriorPower_basis_repr_koszulDifferential_coord z hi] at hmem
  -- The sign is a unit of `ℤ`, so it can be cancelled.
  have hsign := I.toAddSubgroup.zsmul_mem hmem (ExteriorAlgebra.basisEraseSign i s.val : ℤ)
  rwa [← Units.smul_def, smul_smul, Int.units_mul_self, one_smul] at hsign

end Module.Basis

end
end
end CheckedSource16

/-! ## Source: CommAlg.KoszulComplex.Coordinates -/
section CheckedSource17

/-! # Exterior-basis coordinates of the genuine tensor Koszul differential -/

noncomputable section

set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false

namespace CommAlg.Koszul

open CategoryTheory TensorProduct

universe u v
variable {R : Type u} {V : Type} [CommRing R] [Fintype V] [LinearOrder V]

lemma differential_eq_contraction {S : Type*} [CommRing S]
    {N : Type*} [AddCommGroup N] [Module S N]
    (φ : N →ₗ[S] S) (i : ℕ) :
    koszulComplex.d φ i = TauCeti.koszulDifferential φ i := by
  apply exteriorPower.linearMap_ext
  ext v
  simp [koszulComplex.d, koszulComplex.dAlternating_apply,
    TauCeti.koszulDifferential_ιMulti]

/-- Tensor Koszul complex for an arbitrarily indexed finite sequence. -/
abbrev familyCoefficientComplex (x : V → R) (M : ModuleCat.{u} R) :
    HomologicalComplex (ModuleCat.{u} R) PalomarBarycentricTor.naturalDown :=
  (((CategoryTheory.MonoidalCategory.tensoringRight (ModuleCat R)).obj M).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (koszulComplex (Fintype.linearCombination R x))

/-- Its genuine exterior-basis coordinate equivalence. -/
def coefficientCoordinates (x : V → R) (M : ModuleCat.{u} R) (i : ℕ) :
    (familyCoefficientComplex x M).X i ≃ₗ[R] (Set.powersetCard V i →₀ M) :=
  TensorProduct.equivFinsuppOfBasisLeft ((Pi.basisFun R V).exteriorPower i)

set_option maxHeartbeats 2000000 in
/-- The differential transported through the basis, not stipulated as a different complex. -/
def coordinateDifferential (x : V → R) (M : ModuleCat.{u} R) (i : ℕ) :
    (Set.powersetCard V (i + 1) →₀ M) →ₗ[R] (Set.powersetCard V i →₀ M) :=
  let δ : (familyCoefficientComplex.{u} x M).X (i + 1) →ₗ[R]
      (familyCoefficientComplex.{u} x M).X i :=
    ((familyCoefficientComplex.{u} x M).d (i + 1) i).hom
  (coefficientCoordinates.{u} x M i).toLinearMap.comp
    (δ.comp (coefficientCoordinates.{u} x M (i + 1)).symm.toLinearMap)
/-- Defining formula for the differential used in the Tor comparison. -/
theorem coordinateDifferential_palomar_formula (x : V → R) (M : ModuleCat.{u} R) (i : ℕ) : coordinateDifferential x M i = (coefficientCoordinates.{u} x M i).toLinearMap.comp (((familyCoefficientComplex.{u} x M).d (i + 1) i).hom.comp (coefficientCoordinates.{u} x M (i + 1)).symm.toLinearMap) := rfl

lemma coordinateDifferential_comp (x : V → R) (M : ModuleCat.{u} R) (i : ℕ) :
    coordinateDifferential x M i ∘ₗ coordinateDifferential x M (i + 1) = 0 := by
  apply LinearMap.ext
  intro a
  simp only [coordinateDifferential, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, LinearMap.zero_apply]
  have h := congrArg (fun f => ModuleCat.Hom.hom f
    ((coefficientCoordinates x M (i + 2)).symm a))
    ((familyCoefficientComplex x M).d_comp_d (i + 2) (i + 1) i)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply, map_zero] using congrArg (coefficientCoordinates x M i) h

/-- The coordinate chain complex is explicitly isomorphic to the tensor Koszul complex. -/
def coordinateComplex (x : V → R) (M : ModuleCat.{u} R) :
    HomologicalComplex (ModuleCat.{u} R) PalomarBarycentricTor.naturalDown :=
  ChainComplex.of (fun i => ModuleCat.of R (Set.powersetCard V i →₀ M))
    (fun i => ModuleCat.ofHom (coordinateDifferential x M i))
    (fun i => ModuleCat.hom_ext (coordinateDifferential_comp x M i))

@[simp] lemma coordinates_basis_tensor (x : V → R) (M : ModuleCat.{u} R) (i : ℕ)
    (s : Set.powersetCard V i) (m : M) :
    coefficientCoordinates x M i
      (((Pi.basisFun R V).exteriorPower i s) ⊗ₜ[R] m) = Finsupp.single s m := by
  apply Finsupp.ext
  intro t
  change (TensorProduct.equivFinsuppOfBasisLeft ((Pi.basisFun R V).exteriorPower i))
    (((Pi.basisFun R V).exteriorPower i s) ⊗ₜ[R] m) t = (Finsupp.single s m) t
  rw [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, Module.Basis.repr_self]
  simp [Finsupp.single_apply]

@[simp] lemma coordinates_symm_single (x : V → R) (M : ModuleCat.{u} R) (i : ℕ)
    (s : Set.powersetCard V i) (m : M) :
    (coefficientCoordinates x M i).symm (Finsupp.single s m) =
      ((Pi.basisFun R V).exteriorPower i s) ⊗ₜ[R] m := by
  have h := congrArg (coefficientCoordinates x M i).symm
    (coordinates_basis_tensor x M i s m)
  simpa only [LinearEquiv.symm_apply_apply] using h.symm

/-- The canonical cardinality-correct index after deleting an exterior generator. -/
def eraseIndex {i : ℕ} (s : Set.powersetCard V (i + 1)) (j : {j // j ∈ s.val}) :
    Set.powersetCard V i :=
  ⟨s.val.erase j.val, by simp [Finset.card_erase_of_mem j.property, s.property]⟩

lemma basis_differential (x : V → R) (i : ℕ) (s : Set.powersetCard V (i + 1)) :
    koszulComplex.d (Fintype.linearCombination R x) i
      ((Pi.basisFun R V).exteriorPower (i + 1) s) =
      ∑ j : {j // j ∈ s.val}, x j.val •
        (TauCeti.ExteriorAlgebra.basisEraseSign j.val s.val •
          (Pi.basisFun R V).exteriorPower i (eraseIndex s j)) := by
  rw [differential_eq_contraction, Module.Basis.koszulDifferential_eq_sum (Pi.basisFun R V)]
  classical
  let f : V → ⋀[R]^i (V → R) := fun j =>
    (Fintype.linearCombination R x) ((Pi.basisFun R V) j) •
      TauCeti.koszulDifferential ((Pi.basisFun R V).coord j) i
        ((Pi.basisFun R V).exteriorPower (i + 1) s)
  change ∑ j, f j = _
  calc
    ∑ j, f j = ∑ j ∈ s.val, f j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j hj hjnot
      simp only [f]
      rw [Module.Basis.koszulDifferential_coord_exteriorPower_basis_of_notMem _ hjnot,
        smul_zero]
    _ = ∑ j : {j // j ∈ s.val}, f j.val :=
      Finset.sum_subtype s.val (fun _ => Iff.rfl) f
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [f]
      rw [Module.Basis.koszulDifferential_coord_exteriorPower_basis_of_mem _ j.property]
      simp [eraseIndex, Set.powersetCard.ofCard, Fintype.linearCombination_apply, Pi.basisFun_apply, Pi.single_apply, ite_mul]

lemma family_d_tmul (x : V → R) (M : ModuleCat.{u} R) (i : ℕ)
    (w : ⋀[R]^(i + 1) (V → R)) (m : M) :
    ((familyCoefficientComplex x M).d (i + 1) i).hom (w ⊗ₜ[R] m) =
      koszulComplex.d (Fintype.linearCombination R x) i w ⊗ₜ[R] m := by
  change ((CategoryTheory.MonoidalCategory.tensoringRight (ModuleCat R)).obj M).map
    ((koszulComplex (Fintype.linearCombination R x)).d (i + 1) i) (w ⊗ₜ[R] m) = _
  rw [koszulComplex.d_eq_d]
  rfl

lemma coordinateDifferential_single (x : V → R) (M : ModuleCat.{u} R) (i : ℕ)
    (s : Set.powersetCard V (i + 1)) (m : M) :
    coordinateDifferential x M i (Finsupp.single s m) =
      ∑ j : {j // j ∈ s.val}, Finsupp.single (eraseIndex s j)
        (x j.val • (TauCeti.ExteriorAlgebra.basisEraseSign j.val s.val • m)) := by
  simp only [coordinateDifferential, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [coordinates_symm_single]
  erw [family_d_tmul x M i ((Pi.basisFun R V).exteriorPower (i + 1) s) m]
  rw [basis_differential, TensorProduct.sum_tmul, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  change (TensorProduct.equivFinsuppOfBasisLeft ((Pi.basisFun R V).exteriorPower i))
    ((x j.val • (TauCeti.ExteriorAlgebra.basisEraseSign j.val s.val •
      (Pi.basisFun R V).exteriorPower i (eraseIndex s j))) ⊗ₜ[R] m) = _
  apply Finsupp.ext
  intro t
  rw [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
  simp only [map_smul, map_zsmul_unit, Module.Basis.repr_self,
    Finsupp.smul_apply, Finsupp.single_apply]
  by_cases h : eraseIndex s j = t
  · simp only [h, ↓reduceIte, one_smul]
    simpa [smul_smul] using smul_comm (TauCeti.ExteriorAlgebra.basisEraseSign j.val s.val) (x j.val) m
  · simp [h]

@[simp] lemma coordinateComplex_d (x : V → R) (M : ModuleCat.{u} R) (i : ℕ) :
    (coordinateComplex x M).d (i + 1) i =
      ModuleCat.ofHom (coordinateDifferential x M i) := by
  simp [coordinateComplex]

/-- This isomorphism justifies using the explicit coordinates for genuine derived homology. -/
def coordinateComplexIso (x : V → R) (M : ModuleCat.{u} R) :
    familyCoefficientComplex x M ≅ coordinateComplex x M :=
  HomologicalComplex.Hom.isoOfComponents (fun i => (coefficientCoordinates x M i).toModuleIso)
    (by
      intro i j hij
      obtain rfl : i = j + 1 := hij.symm
      rw [coordinateComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      change coordinateDifferential x M j (coefficientCoordinates x M (j + 1) z) =
        coefficientCoordinates x M j (((familyCoefficientComplex x M).d (j + 1) j).hom z)
      simp only [coordinateDifferential, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply])

end CommAlg.Koszul

end
end CheckedSource17

/-! ## Source: CommAlg.KoszulComplex.FiniteVariables -/
section CheckedSource18

/-!
# The genuine polynomial Tor complex for arbitrary finite variable types

An enumeration is used only to construct a regular-sequence resolution.
An explicit linear equivalence then identifies its Koszul complex with the
family indexed by the original variable type. All homology is transported
through actual chain-complex isomorphisms.
-/

noncomputable section

namespace CommAlg.Koszul

open CategoryTheory MvPolynomial

universe u v
variable {V : Type} {k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

def finiteVariableList : List (MvPolynomial V k) :=
  List.ofFn (fun i : Fin (Fintype.card V) => X ((Fintype.equivFin V).symm i))

def finiteVariableIndex : Fin (finiteVariableList (V := V) (k := k)).length ≃ V :=
  (finCongr (by simp [finiteVariableList])).trans (Fintype.equivFin V).symm

@[simp] theorem finiteVariableList_get
    (i : Fin (finiteVariableList (V := V) (k := k)).length) :
    (finiteVariableList (V := V) (k := k)).get i =
      X (finiteVariableIndex (V := V) (k := k) i) := by
  exact List.get_ofFn (fun j : Fin (Fintype.card V) =>
    X ((Fintype.equivFin V).symm j)) i

theorem finite_variables_regular [Nontrivial k] :
    RingTheory.Sequence.IsRegular (MvPolynomial V k) (finiteVariableList (V := V) (k := k)) := by
  simpa only [finiteVariableList, List.map_ofFn, Function.comp_def] using
    variables_regular (k := k) (List.ofFn (Fintype.equivFin V).symm)
      (List.nodup_ofFn.mpr (Fintype.equivFin V).symm.injective)

theorem ofList_finite_variables :
    Ideal.ofList (finiteVariableList (V := V) (k := k)) = idealOfVars V k := by
  apply congrArg Ideal.span
  ext f
  simp only [finiteVariableList, List.mem_ofFn, Set.mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨(Fintype.equivFin V).symm i, rfl⟩
  · rintro ⟨v, rfl⟩
    exact ⟨Fintype.equivFin V v, by simp⟩

abbrev FiniteResidue (V : Type) (k : Type u) [CommRing k] :=
  MvPolynomial V k ⧸ idealOfVars V k

/-- An actual projective resolution of the coefficient ring, viewed as the
quotient by all polynomial variables. -/
def finitePolynomialResolution [Nontrivial k] :
    ProjectiveResolution (ModuleCat.of (MvPolynomial V k) (FiniteResidue V k)) :=
  transportResolution
    (regularSequenceResolution (finiteVariableList (V := V) (k := k)) finite_variables_regular)
    (Submodule.quotEquivOfEq _ _ (ofList_finite_variables (V := V) (k := k))).toModuleIso

@[simp] theorem finitePolynomialResolution_complex [Nontrivial k] :
    (finitePolynomialResolution (V := V) (k := k)).complex =
      koszulComplex.ofList (finiteVariableList (V := V) (k := k)) := rfl

def finiteVariableLinearEquiv :
    (Fin (finiteVariableList (V := V) (k := k)).length → MvPolynomial V k) ≃ₗ[MvPolynomial V k]
      (V → MvPolynomial V k) :=
  LinearEquiv.funCongrLeft _ _ (finiteVariableIndex (V := V) (k := k)).symm

theorem finiteVariableLinearEquiv_single
    (i : Fin (finiteVariableList (V := V) (k := k)).length) :
    finiteVariableLinearEquiv (Pi.single i (1 : MvPolynomial V k)) =
      Pi.single (finiteVariableIndex (V := V) (k := k) i) (1 : MvPolynomial V k) := by
  funext v
  change (Pi.single (M := fun _ => MvPolynomial V k) i 1)
      ((finiteVariableIndex (V := V) (k := k)).symm v) =
    (Pi.single (M := fun _ => MvPolynomial V k)
      (finiteVariableIndex (V := V) (k := k) i) 1) v
  by_cases h : finiteVariableIndex (V := V) (k := k) i = v
  · subst v
    simp
  · have h' : (finiteVariableIndex (V := V) (k := k)).symm v ≠ i := by
      intro he
      exact h (by rw [← he, Equiv.apply_symm_apply])
    simp [Pi.single_apply, h, h', Ne.symm h']

theorem finiteVariableLinearEquiv_comp :
    (Fintype.linearCombination (MvPolynomial V k) (X : V → MvPolynomial V k)) ∘ₗ
      (finiteVariableLinearEquiv (V := V) (k := k)).toLinearMap =
        Fintype.linearCombination (MvPolynomial V k)
          (finiteVariableList (V := V) (k := k)).get := by
  apply (Pi.basisFun (MvPolynomial V k)
    (Fin (finiteVariableList (V := V) (k := k)).length)).ext
  intro i
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Pi.basisFun_apply]
  rw [finiteVariableLinearEquiv_single]
  simpa [Fintype.linearCombination_apply, Pi.single_apply, ite_mul] using
    (finiteVariableList_get (V := V) (k := k) i).symm

/-- The enumerated regular-sequence complex and the original variable-indexed
Koszul complex are genuinely isomorphic. -/
def finiteVariableKoszulIso :
    koszulComplex.ofList (finiteVariableList (V := V) (k := k)) ≅
      koszulComplex (Fintype.linearCombination (MvPolynomial V k) (X : V → MvPolynomial V k)) :=
  koszulComplex.isoOfEquiv _ finiteVariableLinearEquiv _ finiteVariableLinearEquiv_comp

def finiteCoefficientComplexIso (M : ModuleCat.{u} (MvPolynomial V k)) :
    coefficientComplex (finiteVariableList (V := V) (k := k)) M ≅
      familyCoefficientComplex (X : V → MvPolynomial V k) M :=
  (((CategoryTheory.MonoidalCategory.tensoringRight (ModuleCat (MvPolynomial V k))).obj M).mapHomologicalComplex
    (ComplexShape.down ℕ)).mapIso finiteVariableKoszulIso

/-- Mathlib's genuine first-factor derived tensor functor with the actual
polynomial residue module, for the original finite variable type. -/
def finitePolynomialTor (i : ℕ) (M : ModuleCat.{u} (MvPolynomial V k)) :
    ModuleCat.{u} (MvPolynomial V k) :=
  ((Tor' (ModuleCat (MvPolynomial V k)) i).obj
    (ModuleCat.of (MvPolynomial V k) (FiniteResidue V k))).obj M

/-- Genuine derived Tor is computed by the original variable-indexed
coefficient Koszul complex, in every degree and for every module. -/
def finitePolynomialTorIso [Nontrivial k] (i : ℕ)
    (M : ModuleCat.{u} (MvPolynomial V k)) :
    finitePolynomialTor i M ≅
      (familyCoefficientComplex (X : V → MvPolynomial V k) M).homology i :=
  (finitePolynomialResolution (V := V) (k := k)).isoLeftDerivedObj
    ((CategoryTheory.MonoidalCategory.tensoringRight _).obj M) i ≪≫
      (HomologicalComplex.homologyFunctor (ModuleCat (MvPolynomial V k)) (ComplexShape.down ℕ) i).mapIso
        (finiteCoefficientComplexIso M)

end CommAlg.Koszul

end
end CheckedSource18

/-! ## Source: CommAlg.Polymatroid.Exponents -/
section CheckedSource19
/-! # Finite exponent families and their genuine monomial ideals -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Exponent (V : Type*) := V →₀ ℕ
abbrev Family (V : Type*) := Finset (Exponent V)

def Equigenerated (B : Family V) (d : ℕ) : Prop := ∀ a ∈ B, a.degree = d

def Antichain (B : Family V) : Prop := ∀ a ∈ B, ∀ b ∈ B, a ≤ b → a = b

def Contains (B : Family V) (a : Exponent V) : Prop := ∃ b ∈ B, b ≤ a

def exchange (a : Exponent V) (i j : V) : Exponent V :=
  a - Finsupp.single i 1 + Finsupp.single j 1

def ExchangeAxiom (B : Family V) : Prop :=
  ∀ a ∈ B, ∀ b ∈ B, ∀ i, b i < a i →
    ∃ j, a j < b j ∧ exchange a i j ∈ B

def IsPolymatroidal (B : Family V) : Prop :=
  (∃ d, Equigenerated B d) ∧ ExchangeAxiom B

def monomialIdeal (k : Type*) [CommSemiring k] (B : Family V) :
    Ideal (MvPolynomial V k) :=
  Ideal.span ((fun a : Exponent V => MvPolynomial.monomial a (1 : k)) '' (B : Set (Exponent V)))

theorem mem_monomialIdeal_iff {k : Type*} [CommSemiring k] (B : Family V)
    (f : MvPolynomial V k) :
    f ∈ monomialIdeal k B ↔ ∀ a ∈ f.support, Contains B a := by
  exact MvPolynomial.mem_ideal_span_monomial_image

theorem monomial_mem_iff {k : Type*} [CommSemiring k] [Nontrivial k]
    (B : Family V) (a : Exponent V) :
    MvPolynomial.monomial a (1 : k) ∈ monomialIdeal k B ↔ Contains B a := by
  rw [mem_monomialIdeal_iff]
  simp

theorem degree_mono {a b : Exponent V} (h : a ≤ b) : a.degree ≤ b.degree := by
  rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum]
  exact Finset.sum_le_sum (fun i _ => h i)

theorem eq_of_le_of_degree_eq {a b : Exponent V} (h : a ≤ b)
    (hd : a.degree = b.degree) : a = b := by
  ext i
  have hs : ∑ j, a j = ∑ j, b j := by
    simpa only [Finsupp.degree_eq_sum] using hd
  exact (Finset.sum_eq_sum_iff_of_le (fun j _ => h j)).mp hs i (Finset.mem_univ i)

theorem Equigenerated.antichain {B : Family V} {d : ℕ} (hB : Equigenerated B d) :
    Antichain B := by
  intro a ha b hb hab
  exact eq_of_le_of_degree_eq hab ((hB a ha).trans (hB b hb).symm)

theorem Equigenerated.mem_iff_contains {B : Family V} {d : ℕ}
    (hB : Equigenerated B d) {a : Exponent V} (ha : a.degree = d) :
    a ∈ B ↔ Contains B a := by
  constructor
  · intro h
    exact ⟨a, h, le_rfl⟩
  · rintro ⟨b, hb, hba⟩
    exact eq_of_le_of_degree_eq hba ((hB b hb).trans ha.symm) ▸ hb

@[simp] theorem exchange_apply (a : Exponent V) (i j h : V) :
    exchange a i j h = a h - (if h = i then 1 else 0) + (if h = j then 1 else 0) := by
  simp [exchange, Finsupp.single_apply, eq_comm]

theorem exchange_degree (a : Exponent V) (i j : V) (hi : 0 < a i) :
    (exchange a i j).degree = a.degree := by
  have hle : Finsupp.single i 1 ≤ a := by
    intro h
    by_cases hh : h = i
    · subst h
      simpa using (show 1 ≤ a i by omega)
    · simp [Finsupp.single_apply, hh, Ne.symm hh]
  have he : exchange a i j + Finsupp.single i 1 = a + Finsupp.single j 1 := by
    unfold exchange
    rw [add_right_comm, tsub_add_cancel_of_le hle]
  have hd := congrArg Finsupp.degree he
  simp only [map_add, Finsupp.degree_single] at hd
  omega

theorem exchange_ne {a : Exponent V} {i j : V} (hij : i ≠ j) (hi : 0 < a i) :
    exchange a i j ≠ a := by
  intro h
  have he := congrArg (fun b : Exponent V => b i) h
  simp [hij] at he
  omega

theorem exchange_inverse {a : Exponent V} {i j : V} (hij : i ≠ j) (hi : 0 < a i) :
    exchange (exchange a i j) j i = a := by
  ext h
  simp only [exchange_apply]
  by_cases hhi : h = i <;> by_cases hhj : h = j <;> simp_all <;> omega

theorem exists_surplus {a b : Exponent V} (hdeg : a.degree = b.degree)
    {i : V} (hi : b i < a i) : ∃ j, a j < b j := by
  by_contra h
  push_neg at h
  have hab : b ≤ a := h
  have heq := eq_of_le_of_degree_eq hab hdeg.symm
  rw [heq] at hi
  exact (lt_irrefl _ hi)

def subsetSum (a : Exponent V) (U : Finset V) : ℕ := ∑ i ∈ U, a i

@[simp] theorem subsetSum_empty (a : Exponent V) : subsetSum a ∅ = 0 := by
  simp [subsetSum]

@[simp] theorem subsetSum_univ (a : Exponent V) : subsetSum a Finset.univ = a.degree := by
  simp [subsetSum, Finsupp.degree_eq_sum]

theorem subsetSum_mono (a : Exponent V) {U W : Finset V} (h : U ⊆ W) :
    subsetSum a U ≤ subsetSum a W :=
  Finset.sum_le_sum_of_subset h

theorem subsetSum_union_inter (a : Exponent V) (U W : Finset V) :
    subsetSum a U + subsetSum a W = subsetSum a (U ∪ W) + subsetSum a (U ∩ W) := by
  exact (Finset.sum_union_inter (s₁ := U) (s₂ := W) (f := fun i => a i)).symm

end CommAlg.Polymatroid
end

end CheckedSource19

/-! ## Source: CommAlg.Grading.BasisPieces -/
section CheckedSource21
/-! # Genuine homogeneous components obtained by assigning degrees to basis vectors -/

noncomputable section

namespace CommAlg.Grading

open Classical

variable {R M I A : Type*} [CommRing R] [AddCommMonoid M] [Module R M]

/-- Restrict a basis to the span of an arbitrary set of its indices. -/
def restrictedBasis (b : Module.Basis I R M) (P : I → Prop) :
    Module.Basis {i // P i} R (Submodule.span R (b '' {i | P i})) :=
  (Module.Basis.span (b.linearIndependent.comp Subtype.val Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ (by congr 1; ext x; simp))

@[simp] lemma restrictedBasis_val (b : Module.Basis I R M) (P : I → Prop)
    (i : {i // P i}) :
    (restrictedBasis b P i).val = b i.val := by
  simp [restrictedBasis, Module.Basis.map_apply]

/-- A degree component is a genuine submodule of the original module. -/
def Piece (b : Module.Basis I R M) (deg : I → A) (a : A) : Submodule R M :=
  Submodule.span R (b '' {i | deg i = a})

lemma mem_piece (b : Module.Basis I R M) (deg : I → A) (a : A) (x : M) :
    x ∈ Piece b deg a ↔ ∀ i, b.repr x i ≠ 0 → deg i = a := by
  rw [Piece, b.mem_span_image]
  simp only [Set.subset_def, Finset.mem_coe, Finsupp.mem_support_iff, Set.mem_setOf_eq]

lemma basis_mem_piece (b : Module.Basis I R M) (deg : I → A) (i : I) :
    b i ∈ Piece b deg (deg i) := Submodule.subset_span ⟨i, rfl, rfl⟩

def filterMap (P : I → Prop) : (I →₀ R) →ₗ[R] (I →₀ R) where
  toFun := Finsupp.filter P
  map_add' x y := Finsupp.filter_add
  map_smul' c x := Finsupp.filter_smul

@[simp] lemma filterMap_apply (P : I → Prop) (x : I →₀ R) :
    filterMap P x = x.filter P := rfl

/-- Homogeneous projection defined on the original module by its actual basis coefficients. -/
def projection (b : Module.Basis I R M) (deg : I → A) (a : A) : M →ₗ[R] M :=
  b.repr.symm.toLinearMap ∘ₗ filterMap (fun i => deg i = a) ∘ₗ
    b.repr.toLinearMap

@[simp] lemma projection_basis (b : Module.Basis I R M) (deg : I → A) (a : A) (i : I) :
    projection b deg a (b i) = if deg i = a then b i else 0 := by
  by_cases h : deg i = a
  · simp [projection, h, Finsupp.filter_single_of_pos]
  · simp [projection, h, Finsupp.filter_single_of_neg]

lemma projection_mem (b : Module.Basis I R M) (deg : I → A) (a : A) (x : M) :
    projection b deg a x ∈ Piece b deg a := by
  rw [mem_piece]
  intro i hi
  simp only [projection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, filterMap_apply,
    Finsupp.filter_apply] at hi
  split_ifs at hi with h
  · exact h
  · exact (hi rfl).elim

lemma projection_eq_self {b : Module.Basis I R M} {deg : I → A} {a : A} {x : M}
    (hx : x ∈ Piece b deg a) : projection b deg a x = x := by
  apply b.repr.injective
  simp only [projection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  ext i
  simp only [filterMap_apply, Finsupp.filter_apply]
  by_cases hi : deg i = a
  · simp [hi]
  · have hz : b.repr x i = 0 := by
      by_contra hn
      exact hi ((mem_piece b deg a x).mp hx i hn)
    simp [hi, hz]

lemma projection_eq_zero {b : Module.Basis I R M} {deg : I → A} {a c : A}
    (h : a ≠ c) {x : M} (hx : x ∈ Piece b deg c) : projection b deg a x = 0 := by
  apply b.repr.injective
  simp only [projection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, map_zero]
  ext i
  simp only [filterMap_apply, Finsupp.filter_apply, Finsupp.zero_apply]
  split_ifs with hi
  · by_contra hn
    exact h (hi.symm.trans ((mem_piece b deg c x).mp hx i hn))
  · rfl

/-- Every actual vector is the finite sum of its homogeneous components. -/
lemma sum_projections [DecidableEq A] (b : Module.Basis I R M) (deg : I → A) (x : M) :
    ∑ a ∈ (b.repr x).support.image deg, projection b deg a x = x := by
  apply b.repr.injective
  simp only [map_sum, projection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  ext i
  simp only [Finsupp.finset_sum_apply, filterMap_apply, Finsupp.filter_apply]
  by_cases hi : b.repr x i = 0
  · simp [hi]
  · have hm : deg i ∈ (b.repr x).support.image deg :=
      Finset.mem_image.mpr ⟨i, Finsupp.mem_support_iff.mpr hi, rfl⟩
    rw [Finset.sum_eq_single (deg i)]
    · simp
    · intro a ha hne
      simp [Ne.symm hne]
    · intro hnot
      exact (hnot hm).elim

end CommAlg.Grading
end

end CheckedSource21

/-! ## Source: CommAlg.Simplicial.Chains -/
section CheckedSource22
/-! # Augmented simplicial chains as genuine exterior-algebra chains

The empty face has chain degree zero. Thus chain degree `i` represents reduced simplicial
homology degree `i - 1`, including the empty-face class in degree zero. The differential is the
actual exterior contraction by the sum of the coordinates, with its usual signed face boundary.
-/

noncomputable section

namespace CommAlg.Simplicial

open CliffordAlgebra

variable {V k : Type*} [Fintype V] [LinearOrder V] [CommRing k]

abbrev Ambient (V k : Type*) [Fintype V] [CommRing k] := ExteriorAlgebra k (V → k)

def basis : Module.Basis (Finset V) k (Ambient V k) := (Pi.basisFun k V).ExteriorAlgebra

def Chains (K : Finset V → Prop) (i : ℕ) : Submodule k (Ambient V k) :=
  Submodule.span k (basis '' {s | K s ∧ s.card = i})

def Downward (K : Finset V → Prop) : Prop :=
  ∀ ⦃s t⦄, t ⊆ s → K s → K t

def deletion (K : Finset V → Prop) (e : V) (s : Finset V) : Prop := K s ∧ e ∉ s

def link (K : Finset V → Prop) (e : V) (s : Finset V) : Prop := K (insert e s) ∧ e ∉ s

lemma downward_deletion {K : Finset V → Prop} (hK : Downward K) (e : V) :
    Downward (deletion K e) := by
  intro s t hts hs
  exact ⟨hK hts hs.1, fun h => hs.2 (hts h)⟩

lemma downward_link {K : Finset V → Prop} (hK : Downward K) (e : V) :
    Downward (link K e) := by
  intro s t hts hs
  exact ⟨hK (Finset.insert_subset_insert e hts) hs.1, fun h => hs.2 (hts h)⟩

abbrev boundary : Ambient V k →ₗ[k] Ambient V k :=
  contractLeft (Q := (0 : QuadraticForm k (V → k)))
    (Fintype.linearCombination k (fun _ : V => (1 : k)))
/-- Defining formula for the differential used in the Tor comparison. -/
theorem boundary_palomar_formula  : boundary (V := V) (k := k) = contractLeft (Q := (0 : QuadraticForm k (V → k))) (Fintype.linearCombination k (fun _ : V => (1 : k))) := rfl

abbrev contraction (e : V) : Ambient V k →ₗ[k] Ambient V k :=
  contractLeft (Q := (0 : QuadraticForm k (V → k))) ((Pi.basisFun k V).coord e)

abbrev creation (e : V) : Ambient V k →ₗ[k] Ambient V k :=
  LinearMap.mulLeft k (ExteriorAlgebra.ι k ((Pi.basisFun k V) e))

lemma boundary_boundary (z : Ambient V k) : boundary (boundary z) = 0 :=
  contractLeft_contractLeft _ z

lemma contraction_boundary (e : V) (z : Ambient V k) :
    contraction e (boundary z) = -boundary (contraction e z) :=
  contractLeft_comm _ _ z

lemma boundary_creation (e : V) (z : Ambient V k) :
    boundary (creation e z) = z - creation e (boundary z) := by
  rw [show creation e z = ExteriorAlgebra.ι k ((Pi.basisFun k V) e) * z from rfl,
    contractLeft_ι_mul]
  simp [Fintype.linearCombination_apply, Pi.basisFun_apply, Pi.single_apply, ite_mul]

lemma contraction_creation (e : V) (z : Ambient V k) :
    contraction e (creation e z) = z - creation e (contraction e z) := by
  rw [show creation e z = ExteriorAlgebra.ι k ((Pi.basisFun k V) e) * z from rfl,
    contractLeft_ι_mul]
  simp [Module.Basis.coord_apply]

lemma contraction_basis (e : V) (s : Finset V) :
    contraction (k := k) e (basis s) =
      if e ∈ s then TauCeti.ExteriorAlgebra.basisEraseSign e s • basis (s.erase e) else 0 :=
  TauCeti.ExteriorAlgebra.contractLeft_coord_basis (Pi.basisFun k V) e s

lemma creation_basis (e : V) (s : Finset V) :
    creation (k := k) e (basis s) =
      if e ∈ s then 0 else
        TauCeti.ExteriorAlgebra.basisEraseSign e (insert e s) • basis (insert e s) :=
  TauCeti.ExteriorAlgebra.ι_mul_basis (Pi.basisFun k V) e s

lemma boundary_eq_sum (z : Ambient V k) :
    boundary z = ∑ e : V, contraction e z := by
  let φ := Fintype.linearCombination k (fun _ : V => (1 : k))
  change contractLeft φ z = _
  conv_lhs => rw [← (Pi.basisFun k V).sum_dual_apply_smul_coord φ]
  rw [map_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro e he
  simp [φ, Fintype.linearCombination_apply, Pi.basisFun_apply, Pi.single_apply, ite_mul]

lemma basis_mem {K : Finset V → Prop} {i : ℕ} {s : Finset V}
    (hK : K s) (hi : s.card = i) : basis (k := k) s ∈ Chains K i :=
  Submodule.subset_span ⟨s, ⟨hK, hi⟩, rfl⟩

lemma chains_mono {K L : Finset V → Prop} (h : ∀ s, K s → L s) (i : ℕ) :
    Chains (k := k) K i ≤ Chains L i :=
  Submodule.span_mono (Set.image_mono (fun s hs => ⟨h s hs.1, hs.2⟩))

lemma contraction_mem {K : Finset V → Prop} (e : V) {i : ℕ} {z : Ambient V k}
    (hz : z ∈ Chains K (i + 1)) : contraction e z ∈ Chains (link K e) i := by
  induction hz using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨s, ⟨hs, hcard⟩, rfl⟩ := ha
    rw [contraction_basis]
    split_ifs with he
    · apply Submodule.smul_mem
      apply basis_mem
      · exact ⟨by simpa [Finset.insert_erase he] using hs, Finset.notMem_erase _ _⟩
      · simpa [hcard] using Finset.card_erase_of_mem he
    · exact Submodule.zero_mem _
  | zero => simpa using (Submodule.zero_mem (Chains (k := k) (link K e) i))
  | add a b ha hb iha ihb => simpa [mul_add] using Submodule.add_mem _ iha ihb
  | smul r a ha ih => simpa using Submodule.smul_mem _ r ih

lemma contraction_zero_of_deletion {K : Finset V → Prop} (e : V) {i : ℕ}
    {z : Ambient V k} (hz : z ∈ Chains (deletion K e) i) : contraction e z = 0 := by
  induction hz using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨s, ⟨hs, _⟩, rfl⟩ := ha
    simp [contraction_basis, hs.2]
  | zero => simp
  | add a b ha hb iha ihb => simp [iha, ihb]
  | smul r a ha ih => simp [ih]

lemma link_le_deletion {K : Finset V → Prop} (hK : Downward K) (e : V) (i : ℕ) :
    Chains (k := k) (link K e) i ≤ Chains (deletion K e) i :=
  chains_mono (fun s hs => ⟨hK (Finset.subset_insert e s) hs.1, hs.2⟩) i

lemma boundary_mem {K : Finset V → Prop} (hK : Downward K) {i : ℕ} {z : Ambient V k}
    (hz : z ∈ Chains K (i + 1)) : boundary z ∈ Chains K i := by
  rw [boundary_eq_sum]
  apply Submodule.sum_mem
  intro e he
  exact chains_mono (fun s hs => hs.1) i
    (link_le_deletion hK e i (contraction_mem e hz))

lemma boundary_zero_degree_zero {K : Finset V → Prop} {z : Ambient V k}
    (hz : z ∈ Chains K 0) : boundary z = 0 := by
  induction hz using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨s, ⟨hs, hcard⟩, rfl⟩ := ha
    obtain rfl : s = ∅ := Finset.card_eq_zero.mp hcard
    simp [boundary_eq_sum, contraction_basis]
  | zero => simp
  | add a b ha hb iha ihb => simp [iha, ihb]
  | smul r a ha ih => simp [ih]

lemma creation_mem_link {K : Finset V → Prop} (e : V) {i : ℕ} {z : Ambient V k}
    (hz : z ∈ Chains (link K e) i) : creation e z ∈ Chains K (i + 1) := by
  induction hz using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨s, ⟨hs, hcard⟩, rfl⟩ := ha
    rw [creation_basis, if_neg hs.2]
    apply Submodule.smul_mem
    exact basis_mem hs.1 (by simp [hs.2, hcard])
  | zero => simpa using (Submodule.zero_mem (Chains (k := k) K (i + 1)))
  | add a b ha hb iha ihb => simpa [mul_add] using Submodule.add_mem _ iha ihb
  | smul r a ha ih => simpa using Submodule.smul_mem _ r ih

lemma delete_part_mem {K : Finset V → Prop} (e : V) {i : ℕ} {z : Ambient V k}
    (hz : z ∈ Chains K i) : z - creation e (contraction e z) ∈ Chains (deletion K e) i := by
  induction hz using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨s, ⟨hs, hcard⟩, rfl⟩ := ha
    by_cases he : e ∈ s
    · have hprojection : creation (k := k) e (contraction e (basis s)) = basis s := by
        have h := TauCeti.ExteriorAlgebra.ι_mul_contractLeft_coord_basis (Pi.basisFun k V) e s
        rw [if_pos he] at h
        exact h
      rw [hprojection, sub_self]
      exact Submodule.zero_mem _
    · rw [contraction_basis, if_neg he, map_zero, sub_zero]
      exact basis_mem ⟨hs, he⟩ hcard
  | zero => simpa using (Submodule.zero_mem (Chains (k := k) (deletion K e) i))
  | add a b ha hb iha ihb =>
    simpa [mul_add, add_sub_add_comm] using Submodule.add_mem _ iha ihb
  | smul r a ha ih => simpa [smul_sub] using Submodule.smul_mem _ r ih

lemma mem_deletion_of_contraction_zero {K : Finset V → Prop} (e : V) {i : ℕ}
    {z : Ambient V k} (hz : z ∈ Chains K i) (he : contraction e z = 0) :
    z ∈ Chains (deletion K e) i := by
  simpa [he] using delete_part_mem e hz

end CommAlg.Simplicial
end

end CheckedSource22

/-! ## Source: CommAlg.KoszulComplex.FaceCombinatorics -/
section CheckedSource23
/-! # Upper Koszul faces as actual divisibility conditions -/

noncomputable section
namespace CommAlg.Koszul
open Classical CommAlg.Polymatroid
universe u
variable {V : Type u} [Fintype V] [LinearOrder V]

/-- The squarefree exponent vector associated with an exterior basis wedge. -/
def faceExponent (s : Finset V) : Exponent V := ∑ j ∈ s, Finsupp.single j 1

@[simp] lemma faceExponent_apply (s : Finset V) (j : V) :
    faceExponent s j = if j ∈ s then 1 else 0 := by
  classical
  simp [faceExponent, Finsupp.single_apply]

@[simp] lemma faceExponent_empty : faceExponent (∅ : Finset V) = 0 := by
  simp [faceExponent]

lemma faceExponent_mono {s t : Finset V} (h : s ⊆ t) : faceExponent s ≤ faceExponent t := by
  intro j
  by_cases hs : j ∈ s
  · simp [faceExponent_apply, hs, h hs]
  · simp [faceExponent_apply, hs]

lemma faceExponent_erase_add {s : Finset V} {j : V} (hj : j ∈ s) :
    faceExponent (s.erase j) + Finsupp.single j 1 = faceExponent s := by
  ext a
  by_cases h : a = j
  · subst a; simp [hj]
  · simp [faceExponent_apply, Finsupp.single_apply, h, Ne.symm h]

/-- A face exactly when its exterior monomial divides `a` and the residual monomial lies in the ideal. -/
def koszulFaces (B : Family V) (a : Exponent V) (s : Finset V) : Prop :=
  faceExponent s ≤ a ∧ Contains B (a - faceExponent s)

lemma koszulFaces_downward (B : Family V) (a : Exponent V) :
    Simplicial.Downward (koszulFaces B a) := by
  intro s t hts hs
  refine ⟨(faceExponent_mono hts).trans hs.1, ?_⟩
  obtain ⟨b, hb, hba⟩ := hs.2
  exact ⟨b, hb, hba.trans (tsub_le_tsub_left (faceExponent_mono hts) a)⟩


end CommAlg.Koszul
end

end CheckedSource23

/-! ## Source: CommAlg.KoszulComplex.ResidueCoefficients -/
section CheckedSource113

/-! # The residue quotient is the coefficient field with its intended polynomial action -/

noncomputable section
namespace CommAlg.Koszul
open CategoryTheory MvPolynomial
universe u v
variable {V : Type} {k : Type u} [CommRing k]

/-- The coefficient ring, with polynomial action by evaluation at zero. -/
def residueCoefficientModule : ModuleCat.{u} (MvPolynomial V k) :=
  (ModuleCat.restrictScalars (constantCoeff : MvPolynomial V k →+* k)).obj (ModuleCat.of k k)

/-- The quotient by all variables agrees as a polynomial module with the coefficient ring. -/
def residueCoefficientEquiv :
    FiniteResidue V k ≃ₗ[MvPolynomial V k] residueCoefficientModule (V := V) (k := k) where
  toFun := (residueRingEquiv (V := V) (k := k))
  invFun := (residueRingEquiv (V := V) (k := k)).symm
  left_inv := (residueRingEquiv (V := V) (k := k)).left_inv
  right_inv := (residueRingEquiv (V := V) (k := k)).right_inv
  map_add' := (residueRingEquiv (V := V) (k := k)).map_add
  map_smul' f q := by
    change (residueRingEquiv (V := V) (k := k)) (f • q) = constantCoeff f * (residueRingEquiv (V := V) (k := k)) q
    refine Quotient.inductionOn' q ?_
    intro p
    change (residueRingEquiv (V := V) (k := k))
      (Ideal.Quotient.mk (idealOfVars V k) (f * p)) =
      constantCoeff f * (residueRingEquiv (V := V) (k := k))
        (Ideal.Quotient.mk (idealOfVars V k) p)
    simp only [residueRingEquiv_mk, map_mul]

/-- Canonical polynomial-module isomorphism to the actual coefficient ring. -/
def residueCoefficientIso :
    ModuleCat.of (MvPolynomial V k) (FiniteResidue V k) ≅
      residueCoefficientModule (V := V) (k := k) :=
  residueCoefficientEquiv.toModuleIso

variable [Fintype V] [LinearOrder V]

/-- The derived Tor groups used throughout are isomorphic to derived Tor with the coefficient ring
itself, carrying precisely its standard evaluation-at-zero polynomial action. -/
def finitePolynomialTorCoefficientIso (i : ℕ) (M : ModuleCat.{u} (MvPolynomial V k)) :
    finitePolynomialTor i M ≅
      ((Tor' (ModuleCat (MvPolynomial V k)) i).obj
        (residueCoefficientModule (V := V) (k := k))).obj M :=
  ((Functor.flip (Tor' (ModuleCat (MvPolynomial V k)) i)).obj M).mapIso residueCoefficientIso

end CommAlg.Koszul

end
end CheckedSource113

#print axioms CommAlg.Koszul.finitePolynomialTorIso

#print axioms CommAlg.Koszul.finitePolynomialTorCoefficientIso

#print axioms CommAlg.Grading.projection

#print axioms CommAlg.Simplicial.boundary_mem

end
end

/- BEGIN FourPapers/Universal/CoreComplete.lean -/
section

section
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 10000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

/- BEGIN SimplicialPoset.lean -/
section


/-!
# Finite simplicial posets and their canonical vertex sets

The definition is precisely the Boolean-lower-interval definition in the paper.
No global embedding into a Boolean lattice is assumed: distinct faces may have
the same vertices.  The canonical vertex set of a face consists of the atoms
below it.  It determines a subface only within a fixed Boolean interval.
-/

noncomputable section

set_option autoImplicit false

namespace FourPapers.Universal

open Classical Finset

variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]

/-- The paper's definition of a finite simplicial poset. -/
def IsSimplicialPoset (P : Type*) [PartialOrder P] [OrderBot P] : Prop :=
  ∀ p : P, ∃ n : ℕ, Nonempty (Set.Iic p ≃o Finset (Fin n))

/-- The canonical vertices, as atoms in the original poset. -/
def faceVertices (p : P) : Finset P :=
  univ.filter fun a => IsAtom a ∧ a ≤ p

@[simp] theorem mem_faceVertices {p a : P} :
    a ∈ faceVertices p ↔ IsAtom a ∧ a ≤ p := by
  simp [faceVertices]

@[simp] theorem faceVertices_bot : faceVertices (⊥ : P) = ∅ := by
  ext a
  simp only [mem_faceVertices]
  constructor
  · rintro ⟨ha, hle⟩
    exact (ha.ne_bot (le_bot_iff.mp hle)).elim
  · intro h
    simp at h

theorem faceVertices_mono : Monotone (faceVertices : P → Finset P) := by
  intro p q hpq a ha
  rcases mem_faceVertices.mp ha with ⟨hat, hap⟩
  exact mem_faceVertices.mpr ⟨hat, hap.trans hpq⟩

/-- The atom corresponding to one coordinate in a Boolean chart. -/
def chartAtom {p : P} {n : ℕ} (e : Set.Iic p ≃o Finset (Fin n)) (i : Fin n) : P :=
  (e.symm {i}).val

theorem chartAtom_isAtom {p : P} {n : ℕ}
    (e : Set.Iic p ≃o Finset (Fin n)) (i : Fin n) : IsAtom (chartAtom e i) :=
  IsAtom.of_isAtom_coe_Iic ((e.symm.isAtom_iff {i}).mpr (Finset.isAtom_singleton i))

theorem chartAtom_le {p : P} {n : ℕ}
    (e : Set.Iic p ≃o Finset (Fin n)) (i : Fin n) : chartAtom e i ≤ p :=
  (e.symm {i}).property

theorem chartAtom_le_iff {p : P} {n : ℕ}
    (e : Set.Iic p ≃o Finset (Fin n)) (i : Fin n) (x : Set.Iic p) :
    chartAtom e i ≤ x.val ↔ i ∈ e x := by
  change e.symm {i} ≤ x ↔ i ∈ e x
  rw [← e.le_iff_le]
  simp

theorem atom_eq_chartAtom {p a : P} {n : ℕ}
    (e : Set.Iic p ≃o Finset (Fin n)) (ha : IsAtom a) (hap : a ≤ p) :
    ∃ i : Fin n, a = chartAtom e i := by
  have hea : IsAtom (e ⟨a, hap⟩) := (e.isAtom_iff _).mpr (ha.Iic hap)
  obtain ⟨i, hi⟩ := Finset.isAtom_iff.mp hea
  refine ⟨i, ?_⟩
  have he : e.symm (e ⟨a, hap⟩) = e.symm {i} := congrArg e.symm hi
  exact congrArg Subtype.val (by simpa using he)

/-- Inside one face, inclusion of canonical vertex sets is precisely the order. -/
theorem faceVertices_subset_iff (hs : IsSimplicialPoset P) {p x y : P}
    (hxp : x ≤ p) (hyp : y ≤ p) :
    faceVertices x ⊆ faceVertices y ↔ x ≤ y := by
  constructor
  · intro h
    obtain ⟨n, ⟨e⟩⟩ := hs p
    have he : e ⟨x, hxp⟩ ⊆ e ⟨y, hyp⟩ := by
      intro i hi
      have hix : chartAtom e i ∈ faceVertices x :=
        mem_faceVertices.mpr ⟨chartAtom_isAtom e i, (chartAtom_le_iff e i _).mpr hi⟩
      exact (chartAtom_le_iff e i _).mp (mem_faceVertices.mp (h hix)).2
    exact e.le_iff_le.mp he
  · exact fun h => faceVertices_mono h

theorem faceVertices_injective_below (hs : IsSimplicialPoset P) {p x y : P}
    (hxp : x ≤ p) (hyp : y ≤ p) (h : faceVertices x = faceVertices y) : x = y := by
  exact le_antisymm ((faceVertices_subset_iff hs hxp hyp).mp h.subset)
    ((faceVertices_subset_iff hs hyp hxp).mp h.symm.subset)

/-- Every subset of the vertices of a face occurs as exactly one subface. -/
theorem existsUnique_subface (hs : IsSimplicialPoset P) (p : P) (s : Finset P)
    (hsu : s ⊆ faceVertices p) :
    ∃! x : Set.Iic p, faceVertices x.val = s := by
  obtain ⟨n, ⟨e⟩⟩ := hs p
  let t : Finset (Fin n) := univ.filter fun i => chartAtom e i ∈ s
  let x : Set.Iic p := e.symm t
  have hx : faceVertices x.val = s := by
    ext a
    constructor
    · intro ha
      obtain ⟨hat, hax⟩ := mem_faceVertices.mp ha
      obtain ⟨i, rfl⟩ := atom_eq_chartAtom e hat (hax.trans x.property)
      have hit : i ∈ t := by
        simpa [x] using (chartAtom_le_iff e i x).mp hax
      exact (mem_filter.mp hit).2
    · intro ha
      obtain ⟨hat, hap⟩ := mem_faceVertices.mp (hsu ha)
      obtain ⟨i, rfl⟩ := atom_eq_chartAtom e hat hap
      refine mem_faceVertices.mpr ⟨chartAtom_isAtom e i, ?_⟩
      apply (chartAtom_le_iff e i x).mpr
      simpa [x, t] using ha
  refine ⟨x, hx, ?_⟩
  intro y hy
  apply Subtype.ext
  exact faceVertices_injective_below hs y.property x.property (hy.trans hx.symm)

theorem faceVertices_nonempty (hs : IsSimplicialPoset P) {p : P} (hp : p ≠ ⊥) :
    (faceVertices p).Nonempty := by
  by_contra h
  have he : faceVertices p = faceVertices (⊥ : P) := by
    simpa using Finset.not_nonempty_iff_eq_empty.mp h
  exact hp (faceVertices_injective_below hs le_rfl bot_le he)

theorem faceVertices_eq_empty_iff (hs : IsSimplicialPoset P) (p : P) :
    faceVertices p = ∅ ↔ p = ⊥ := by
  constructor
  · intro h
    exact faceVertices_injective_below hs le_rfl bot_le (by simpa using h)
  · rintro rfl
    exact faceVertices_bot

/-- The rank is the number of vertices in a Boolean face. -/
def faceRank (p : P) : ℕ := (faceVertices p).card

@[simp] theorem faceRank_bot : faceRank (⊥ : P) = 0 := by simp [faceRank]

theorem faceRank_strictMono (hs : IsSimplicialPoset P) :
    StrictMono (faceRank : P → ℕ) := by
  intro p q hpq
  apply Finset.card_lt_card
  refine (ssubset_iff_subset_ne).mpr ⟨faceVertices_mono hpq.le, ?_⟩
  intro h
  exact hpq.ne (faceVertices_injective_below hs hpq.le le_rfl h)

theorem faceRank_eq_of_orderIso {Q : Type*} [PartialOrder Q] [OrderBot Q] [Fintype Q]
    (e : P ≃o Q) (p : P) : faceRank (e p) = faceRank p := by
  have he : faceVertices (e p) = (faceVertices p).image e := by
    ext a
    simp only [mem_faceVertices, mem_image]
    constructor
    · rintro ⟨ha, hap⟩
      refine ⟨e.symm a, ?_, e.apply_symm_apply a⟩
      exact ⟨(e.symm.isAtom_iff a).mpr ha, by simpa using e.symm.monotone hap⟩
    · rintro ⟨b, ⟨hb, hbp⟩, rfl⟩
      exact ⟨(e.isAtom_iff b).mpr hb, e.monotone hbp⟩
  simp only [faceRank, he, Finset.card_image_iff.mpr e.injective.injOn]

end FourPapers.Universal
end
end

/- BEGIN CoherentDiagrams.lean -/
section


/-!
# Coherent comparisons and actual inverse limits

The section module is the submodule of the product consisting of compatible
families.  Coherent stalk equivalences give an actual linear equivalence on this
inverse limit and on every relative restriction kernel.  No flatness condition
appears in this argument.
-/

noncomputable section

set_option autoImplicit false

namespace FourPapers.Universal

universe u v w

variable (K : Type u) [CommRing K] (P : Type v) [Preorder P]

/-- A contravariant diagram of modules on an ordered set. -/
structure ModuleDiagram where
  obj : P → Type w
  [addCommGroup : ∀ p, AddCommGroup (obj p)]
  [module : ∀ p, Module K (obj p)]
  res : ∀ {p q}, q ≤ p → obj p →ₗ[K] obj q
  res_refl : ∀ p x, res (le_refl p) x = x
  res_comp : ∀ {p q r} (hqp : q ≤ p) (hrq : r ≤ q) x,
    res hrq (res hqp x) = res (hrq.trans hqp) x

attribute [instance] ModuleDiagram.addCommGroup ModuleDiagram.module

variable {K P}

namespace ModuleDiagram

variable (D : ModuleDiagram K P)

/-- The inverse limit, realized as compatible families in the product module. -/
def sections : Submodule K (∀ p, D.obj p) where
  carrier := {x | ∀ p q (h : q ≤ p), D.res h (x p) = x q}
  zero_mem' := by intros; simp
  add_mem' := by
    intro x y hx hy p q h
    simpa using congrArg₂ (· + ·) (hx p q h) (hy p q h)
  smul_mem' := by
    intro c x hx p q h
    simpa using congrArg (c • ·) (hx p q h)

@[simp] theorem mem_sections (x : ∀ p, D.obj p) :
    x ∈ D.sections ↔ ∀ p q (h : q ≤ p), D.res h (x p) = x q := Iff.rfl

/-- Restriction to an arbitrary subset of objects with its inherited order. -/
abbrev restrict (Q : Set P) : ModuleDiagram K Q where
  obj p := D.obj p.val
  res h := D.res h
  res_refl p x := D.res_refl p.val x
  res_comp h₁ h₂ x := D.res_comp h₁ h₂ x

/-- Restrict a compatible family. -/
def restriction (Q : Set P) : D.sections →ₗ[K] (D.restrict Q).sections where
  toFun x := ⟨fun p => x.val p.val, by
    intro p q h
    exact x.property p.val q.val h⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual relative module: the kernel of restriction. -/
def relative (Q : Set P) : Submodule K D.sections :=
  LinearMap.ker (D.restriction Q)

theorem mem_relative_iff (Q : Set P) (x : D.sections) :
    x ∈ D.relative Q ↔ ∀ p ∈ Q, x.val p = 0 := by
  change D.restriction Q x = 0 ↔ _
  constructor
  · intro h p hp
    exact congrArg (fun z : (D.restrict Q).sections => z.val ⟨p, hp⟩) h
  · intro h
    apply Subtype.ext
    funext p
    exact h p.val p.property

end ModuleDiagram

/-- A coherent family of linear equivalences. -/
structure CoherentEquiv (D E : ModuleDiagram K P) where
  component : ∀ p, D.obj p ≃ₗ[K] E.obj p
  naturality : ∀ p q (h : q ≤ p) x,
    E.res h (component p x) = component q (D.res h x)

namespace CoherentEquiv

variable {D E F : ModuleDiagram K P}

def refl (D : ModuleDiagram K P) : CoherentEquiv D D where
  component p := LinearEquiv.refl K (D.obj p)
  naturality _ _ _ _ := rfl

def symm (e : CoherentEquiv D E) : CoherentEquiv E D where
  component p := (e.component p).symm
  naturality p q h x := by
    apply (e.component q).injective
    simpa using (e.naturality p q h ((e.component p).symm x)).symm
theorem symm_palomar_formula (e : CoherentEquiv D E) (p : P) :
    e.symm.component p = (e.component p).symm := rfl

def trans (e : CoherentEquiv D E) (f : CoherentEquiv E F) : CoherentEquiv D F where
  component p := (e.component p).trans (f.component p)
  naturality p q h x := by
    change F.res h (f.component p (e.component p x)) =
      f.component q (e.component q (D.res h x))
    rw [f.naturality, e.naturality]

/-- A coherent family gives an isomorphism of its actual inverse-limit modules. -/
def sectionEquiv (e : CoherentEquiv D E) : D.sections ≃ₗ[K] E.sections where
  toFun x := ⟨fun p => e.component p (x.val p), by
    intro p q h
    rw [e.naturality, x.property p q h]⟩
  invFun x := ⟨fun p => (e.component p).symm (x.val p), by
    intro p q h
    change D.res h (e.symm.component p (x.val p)) =
      e.symm.component q (x.val q)
    exact (e.symm.naturality p q h (x.val p)).trans
      (congrArg (e.symm.component q) (x.property p q h))⟩
  left_inv x := by
    apply Subtype.ext
    funext p
    exact (e.component p).symm_apply_apply (x.val p)
  right_inv x := by
    apply Subtype.ext
    funext p
    exact (e.component p).apply_symm_apply (x.val p)
  map_add' x y := by
    apply Subtype.ext
    funext p
    exact map_add (e.component p) (x.val p) (y.val p)
  map_smul' c x := by
    apply Subtype.ext
    funext p
    exact map_smul (e.component p) c (x.val p)
theorem sectionEquiv_palomar_formula (e : CoherentEquiv D E) (x : D.sections) (p : P) :
    (e.sectionEquiv x).val p = e.component p (x.val p) := rfl

@[simp] theorem sectionEquiv_apply (e : CoherentEquiv D E)
    (x : D.sections) (p : P) :
    (e.sectionEquiv x).val p = e.component p (x.val p) := rfl

def restrict (e : CoherentEquiv D E) (Q : Set P) :
    CoherentEquiv (D.restrict Q) (E.restrict Q) where
  component p := e.component p.val
  naturality p q h x := e.naturality p.val q.val h x

/-- The inverse-limit comparison commutes with every restriction. -/
theorem restriction_naturality (e : CoherentEquiv D E) (Q : Set P) (x : D.sections) :
    E.restriction Q (e.sectionEquiv x) =
      (e.restrict Q).sectionEquiv (D.restriction Q x) := rfl

/-- The same coherent family identifies every relative restriction kernel. -/
def relativeEquiv (e : CoherentEquiv D E) (Q : Set P) :
    D.relative Q ≃ₗ[K] E.relative Q where
  toFun x := ⟨e.sectionEquiv x.val, by
    have hx := (D.mem_relative_iff Q x.val).mp x.property
    rw [ModuleDiagram.mem_relative_iff]
    intro p hp
    simp [hx p hp]⟩
  invFun x := ⟨e.sectionEquiv.symm x.val, by
    have hx := (E.mem_relative_iff Q x.val).mp x.property
    rw [ModuleDiagram.mem_relative_iff]
    intro p hp
    change (e.component p).symm (x.val.val p) = 0
    simp [hx p hp]⟩
  left_inv x := by
    apply Subtype.ext
    exact e.sectionEquiv.symm_apply_apply x.val
  right_inv x := by
    apply Subtype.ext
    exact e.sectionEquiv.apply_symm_apply x.val
  map_add' x y := by
    apply Subtype.ext
    exact map_add e.sectionEquiv x.val y.val
  map_smul' c x := by
    apply Subtype.ext
    exact map_smul e.sectionEquiv c x.val

end CoherentEquiv

end FourPapers.Universal
end
end

/- BEGIN PolynomialDiagram.lean -/
section


/-!
# The actual polynomial face diagram

The stalk at a face is the polynomial ring on its atoms. Restriction kills
precisely the variables outside the smaller face. The empty face is retained,
so its stalk is the coefficient ring rather than being omitted from the limit.
-/

noncomputable section

set_option autoImplicit false

namespace FourPapers.Universal

open Classical MvPolynomial

variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K]

/-- The atoms of a specified face, viewed as actual elements of the poset. -/
abbrev FaceVertex (p : P) := {a : P // IsAtom a ∧ a ≤ p}

instance palomarFaceVertexFintype (p : P) : Fintype (FaceVertex p) := Fintype.ofFinite _

def faceVertexInclusion {p q : P} (hqp : q ≤ p) : FaceVertex q ↪ FaceVertex p where
  toFun a := ⟨a.val, a.property.1, a.property.2.trans hqp⟩
  inj' _ _ h := Subtype.ext (congrArg (fun a : FaceVertex p => a.val) h)

abbrev PolynomialStalk (p : P) := MvPolynomial (FaceVertex p) K

/-- Restriction is an algebra homomorphism, not an abstract chosen linear map. -/
def polynomialRestriction {p q : P} (hqp : q ≤ p) :
    PolynomialStalk K p →ₐ[K] PolynomialStalk K q := by
  classical
  exact aeval fun a => if h : a.val ≤ q then X ⟨a.val, a.property.1, h⟩ else 0

@[simp] theorem polynomialRestriction_X {p q : P} (hqp : q ≤ p)
    (a : FaceVertex p) :
    polynomialRestriction K hqp (X a) =
      if h : a.val ≤ q then X ⟨a.val, a.property.1, h⟩ else 0 := by
  classical
  simp [polynomialRestriction]

@[simp] theorem polynomialRestriction_C {p q : P} (hqp : q ≤ p) (c : K) :
    polynomialRestriction K hqp (C c) = C c := by
  simp [polynomialRestriction]

theorem polynomialRestriction_refl (p : P) :
    polynomialRestriction K (le_refl p) = AlgHom.id K (PolynomialStalk K p) := by
  classical
  apply MvPolynomial.algHom_ext
  intro a
  simp [a.property.2]

theorem polynomialRestriction_comp {p q r : P} (hqp : q ≤ p) (hrq : r ≤ q) :
    (polynomialRestriction K hrq).comp (polynomialRestriction K hqp) =
      polynomialRestriction K (hrq.trans hqp) := by
  classical
  apply MvPolynomial.algHom_ext
  intro a
  by_cases hq : a.val ≤ q
  · by_cases hr : a.val ≤ r <;> simp [hq, hr]
  · have hr : ¬ a.val ≤ r := fun h => hq (h.trans hrq)
    simp [hq, hr]

/-- Inclusion of a smaller polynomial ring is a section of face restriction. -/
theorem polynomialRestriction_rename {p q : P} (hqp : q ≤ p) :
    (polynomialRestriction K hqp).comp (rename (faceVertexInclusion hqp)) =
      AlgHom.id K (PolynomialStalk K q) := by
  classical
  apply MvPolynomial.algHom_ext
  intro a
  simp only [AlgHom.comp_apply, MvPolynomial.rename_X, AlgHom.id_apply]
  rw [polynomialRestriction_X]
  change (if h : a.val ≤ q then X ⟨a.val, a.property.1, h⟩ else 0) = X a
  rw [dif_pos a.property.2]

theorem polynomialRestriction_surjective {p q : P} (hqp : q ≤ p) :
    Function.Surjective (polynomialRestriction K hqp) := by
  intro f
  exact ⟨rename (faceVertexInclusion hqp) f,
    DFunLike.congr_fun (polynomialRestriction_rename K hqp) f⟩

/-- The polynomial rings and their actual face restrictions form a diagram. -/
abbrev polynomialDiagram : ModuleDiagram K P where
  obj p := PolynomialStalk K p
  res h := (polynomialRestriction K h).toLinearMap
  res_refl p f := DFunLike.congr_fun (polynomialRestriction_refl K p) f
  res_comp hqp hrq f := DFunLike.congr_fun (polynomialRestriction_comp K hqp hrq) f

/-- On a stalk, the universal rank parameters are elementary symmetric polynomials. -/
def polynomialParameter (p : P) (i : ℕ) : PolynomialStalk K p :=
  MvPolynomial.esymm (FaceVertex p) K i

/-- The top parameter is the product of every atom variable. -/
def polynomialTop (p : P) : PolynomialStalk K p :=
  ∏ a : FaceVertex p, X a

theorem polynomialTop_regular (p : P) : IsRegular (polynomialTop K p) :=
  MvPolynomial.isRegular_prod_X Finset.univ

theorem polynomialTop_mul_injective (p : P) :
    Function.Injective (fun f : PolynomialStalk K p => polynomialTop K p * f) :=
  (polynomialTop_regular K p).left

theorem polynomialTop_eq_parameter (p : P) :
    polynomialTop K p = polynomialParameter K p (Fintype.card (FaceVertex p)) := by
  classical
  unfold polynomialTop polynomialParameter MvPolynomial.esymm
  rw [← Finset.card_univ (α := FaceVertex p), Finset.powersetCard_self]
  simp

/-- Every proper subface omits an atom, even if the poset has repeated vertex sets
on distinct incomparable faces. Only the Boolean interval below the given face is used. -/
theorem exists_atom_not_le (hs : IsSimplicialPoset P) {p q : P} (hqp : q < p) :
    ∃ a : FaceVertex p, ¬ a.val ≤ q := by
  by_contra h
  push Not at h
  have hsub : faceVertices p ⊆ faceVertices q := by
    intro a ha
    obtain ⟨hat, hap⟩ := mem_faceVertices.mp ha
    exact mem_faceVertices.mpr ⟨hat, h ⟨a, hat, hap⟩⟩
  exact hqp.not_ge ((faceVertices_subset_iff hs le_rfl hqp.le).mp hsub)

theorem polynomialRestriction_top (hs : IsSimplicialPoset P) {p q : P}
    (hqp : q < p) : polynomialRestriction K hqp.le (polynomialTop K p) = 0 := by
  classical
  obtain ⟨a, ha⟩ := exists_atom_not_le hs hqp
  simp only [polynomialTop, map_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ a)
  simp [ha]

end FourPapers.Universal
end
end

/- BEGIN FaceRingPresentation.lean -/
section


/-!
# The original face-ring presentations

Both rings below are quotients of polynomial rings by their conventional
relations. In particular, the polynomial face ring is not defined to be the
barycentric module. Its comparison with the inverse-limit polynomial diagram
is a further theorem to establish.
-/

noncomputable section

set_option autoImplicit false

namespace FourPapers.Universal

open Classical MvPolynomial Finset

variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]

abbrev NonzeroFace (P : Type*) [Preorder P] [OrderBot P] := {p : P // p ≠ ⊥}

instance palomarNonzeroFaceFintype : Fintype (NonzeroFace P) := Fintype.ofFinite _

/-- The meet of two faces in a specified common Boolean upper interval. -/
def faceMeetBelow (hs : IsSimplicialPoset P) (p q w : P)
    (hpw : p ≤ w) (hqw : q ≤ w) : P :=
  ((existsUnique_subface hs w (faceVertices p ∩ faceVertices q)
    (Finset.inter_subset_left.trans (faceVertices_mono hpw))).choose).val

theorem faceMeetBelow_le_top (hs : IsSimplicialPoset P) (p q w : P)
    (hpw : p ≤ w) (hqw : q ≤ w) : faceMeetBelow hs p q w hpw hqw ≤ w :=
  ((existsUnique_subface hs w (faceVertices p ∩ faceVertices q)
    (Finset.inter_subset_left.trans (faceVertices_mono hpw))).choose).property

theorem faceMeetBelow_vertices (hs : IsSimplicialPoset P) (p q w : P)
    (hpw : p ≤ w) (hqw : q ≤ w) :
    faceVertices (faceMeetBelow hs p q w hpw hqw) = faceVertices p ∩ faceVertices q :=
  (existsUnique_subface hs w (faceVertices p ∩ faceVertices q)
    (Finset.inter_subset_left.trans (faceVertices_mono hpw))).choose_spec.1

theorem faceMeetBelow_le_left (hs : IsSimplicialPoset P) (p q w : P)
    (hpw : p ≤ w) (hqw : q ≤ w) : faceMeetBelow hs p q w hpw hqw ≤ p := by
  apply (faceVertices_subset_iff hs (faceMeetBelow_le_top hs p q w hpw hqw) hpw).mp
  rw [faceMeetBelow_vertices]
  exact Finset.inter_subset_left

theorem faceMeetBelow_le_right (hs : IsSimplicialPoset P) (p q w : P)
    (hpw : p ≤ w) (hqw : q ≤ w) : faceMeetBelow hs p q w hpw hqw ≤ q := by
  apply (faceVertices_subset_iff hs (faceMeetBelow_le_top hs p q w hpw hqw) hqw).mp
  rw [faceMeetBelow_vertices]
  exact Finset.inter_subset_right

theorem le_faceMeetBelow (hs : IsSimplicialPoset P) (p q w : P)
    (hpw : p ≤ w) (hqw : q ≤ w) {a : P} (hap : a ≤ p) (haq : a ≤ q) :
    a ≤ faceMeetBelow hs p q w hpw hqw := by
  apply (faceVertices_subset_iff hs (hap.trans hpw)
    (faceMeetBelow_le_top hs p q w hpw hqw)).mp
  rw [faceMeetBelow_vertices]
  exact Finset.subset_inter (faceVertices_mono hap) (faceVertices_mono haq)

/-- The chosen common upper face does not affect the meet. -/
theorem faceMeetBelow_independent (hs : IsSimplicialPoset P) (p q w w' : P)
    (hpw : p ≤ w) (hqw : q ≤ w) (hpw' : p ≤ w') (hqw' : q ≤ w') :
    faceMeetBelow hs p q w hpw hqw = faceMeetBelow hs p q w' hpw' hqw' := by
  apply le_antisymm
  · exact le_faceMeetBelow hs p q w' hpw' hqw'
      (faceMeetBelow_le_left hs p q w hpw hqw)
      (faceMeetBelow_le_right hs p q w hpw hqw)
  · exact le_faceMeetBelow hs p q w hpw hqw
      (faceMeetBelow_le_left hs p q w' hpw' hqw')
      (faceMeetBelow_le_right hs p q w' hpw' hqw')

def IsMinimalCommonUpper (p q w : P) : Prop :=
  p ≤ w ∧ q ≤ w ∧ ∀ v, p ≤ v → q ≤ v → v ≤ w → v = w

def minimalCommonUppers (p q : P) : Finset P :=
  univ.filter (IsMinimalCommonUpper p q)

@[simp] theorem mem_minimalCommonUppers (p q w : P) :
    w ∈ minimalCommonUppers p q ↔ IsMinimalCommonUpper p q w := by
  simp [minimalCommonUppers]

variable (K : Type*) [CommRing K]

abbrev FacePolynomial := MvPolynomial (NonzeroFace P) K

/-- The bottom-face symbol is the scalar one, as in the original definition. -/
def faceSymbol (p : P) : FacePolynomial (P := P) K :=
  if hp : p = ⊥ then 1 else X ⟨p, hp⟩

@[simp] theorem faceSymbol_bot : faceSymbol (P := P) K ⊥ = 1 := by
  simp [faceSymbol]

@[simp] theorem faceSymbol_nonzero (p : NonzeroFace P) :
    faceSymbol K p.val = X p := by
  simp [faceSymbol, p.property]

/-- All conventional straightening relations, with no additional relations.
Common-upper witnesses give the same meet, by the independence theorem above. -/
def faceRelations (hs : IsSimplicialPoset P) : Set (FacePolynomial (P := P) K) :=
  {f | (∃ (p q w : P) (hpw : p ≤ w) (hqw : q ≤ w),
      f = faceSymbol K p * faceSymbol K q -
        faceSymbol K (faceMeetBelow hs p q w hpw hqw) *
          ∑ u ∈ minimalCommonUppers p q, faceSymbol K u) ∨
    (∃ p q, (¬ ∃ w, p ≤ w ∧ q ≤ w) ∧
      f = faceSymbol K p * faceSymbol K q)}

def faceIdeal (hs : IsSimplicialPoset P) : Ideal (FacePolynomial (P := P) K) :=
  Ideal.span (faceRelations K hs)

/-- Stanley's face ring of the original simplicial poset. -/
abbrev FaceRing (hs : IsSimplicialPoset P) :=
  FacePolynomial (P := P) K ⧸ faceIdeal K hs
def palomarFaceRingModule (hs : IsSimplicialPoset P) : Module K (FaceRing K hs) := inferInstance
attribute [instance 2400] palomarFaceRingModule


/-- The Stanley--Reisner ideal of the order complex, generated by incomparable pairs. -/
def barycentricIdeal : Ideal (FacePolynomial (P := P) K) :=
  Ideal.span {f | ∃ p q : NonzeroFace P,
    ¬ p.val ≤ q.val ∧ ¬ q.val ≤ p.val ∧ f = X p * X q}

abbrev BarycentricRing := FacePolynomial (P := P) K ⧸ barycentricIdeal (P := P) K

def faceRingGenerator (hs : IsSimplicialPoset P) (p : P) : FaceRing K hs :=
  Ideal.Quotient.mk (faceIdeal K hs) (faceSymbol K p)

def barycentricGenerator (p : P) : BarycentricRing (P := P) K :=
  Ideal.Quotient.mk (barycentricIdeal K) (faceSymbol K p)

/-- The universal parameters are sums of the actual rank-i face generators. -/
def faceRankParameter (hs : IsSimplicialPoset P) (i : ℕ) : FaceRing K hs :=
  ∑ p ∈ univ.filter (fun p : P => faceRank p = i), faceRingGenerator K hs p

def barycentricRankParameter (i : ℕ) : BarycentricRing (P := P) K :=
  ∑ p ∈ univ.filter (fun p : P => faceRank p = i), barycentricGenerator K p

def faceParameterAction (hs : IsSimplicialPoset P) (d : ℕ) :
    MvPolynomial (Fin d) K →ₐ[K] FaceRing K hs :=
  MvPolynomial.aeval fun i => faceRankParameter K hs (i.val + 1)

def barycentricParameterAction (d : ℕ) :
    MvPolynomial (Fin d) K →ₐ[K] BarycentricRing (P := P) K :=
  MvPolynomial.aeval fun i => barycentricRankParameter K (i.val + 1)

end FourPapers.Universal

end
end

/- BEGIN RankWeight.lean -/
section


/-!
# The exact quadratic rank-weight filtration

The paper assigns rank `r` weight `r(2d-r)`. For a vertex exponent vector `a`,
the equivalent expression is `2d |a| - Σᵥ,𝓌 min(aᵥ,a𝓌)`. The overlap cost is
superadditive, so the rank weight is subadditive under polynomial multiplication.
These are the actual quadratic weights, not a replacement degree filtration.
-/

noncomputable section

set_option autoImplicit false

namespace FourPapers.Universal

variable {V : Type*} [Fintype V]

def vertexDegree (a : V → ℕ) : ℕ := ∑ v, a v

def overlapCost (a : V → ℕ) : ℕ := ∑ v, ∑ w, min (a v) (a w)

def rankWeight (d r : ℕ) : ℤ := (r : ℤ) * (2 * (d : ℤ) - r)

def polynomialRankWeight (d : ℕ) (a : V → ℕ) : ℤ :=
  2 * (d : ℤ) * (vertexDegree a : ℤ) - (overlapCost a : ℤ)

@[simp] theorem vertexDegree_add (a b : V → ℕ) :
    vertexDegree (a + b) = vertexDegree a + vertexDegree b := by
  simp [vertexDegree, Finset.sum_add_distrib]

theorem min_add_superadditive (a b c d : ℕ) :
    min a b + min c d ≤ min (a + c) (b + d) :=
  le_min (add_le_add (min_le_left _ _) (min_le_left _ _))
    (add_le_add (min_le_right _ _) (min_le_right _ _))

theorem overlapCost_superadditive (a b : V → ℕ) :
    overlapCost a + overlapCost b ≤ overlapCost (a + b) := by
  calc
    overlapCost a + overlapCost b =
        ∑ v, ∑ w, (min (a v) (a w) + min (b v) (b w)) := by
      simp [overlapCost, Finset.sum_add_distrib]
    _ ≤ overlapCost (a + b) := by
      apply Finset.sum_le_sum
      intro v hv
      apply Finset.sum_le_sum
      intro w hw
      exact min_add_superadditive (a v) (a w) (b v) (b w)

theorem overlapCost_le_card_mul_degree (a : V → ℕ) :
    overlapCost a ≤ Fintype.card V * vertexDegree a := by
  calc
    overlapCost a ≤ ∑ v : V, ∑ _w : V, a v := by
      apply Finset.sum_le_sum
      intro v hv
      exact Finset.sum_le_sum (fun w hw => min_le_left _ _)
    _ = Fintype.card V * vertexDegree a := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← Finset.mul_sum]
      rfl

theorem polynomialRankWeight_subadditive (d : ℕ) (a b : V → ℕ) :
    polynomialRankWeight d (a + b) ≤
      polynomialRankWeight d a + polynomialRankWeight d b := by
  have hc : (overlapCost a : ℤ) + overlapCost b ≤ overlapCost (a + b) := by
    exact_mod_cast overlapCost_superadditive a b
  simp only [polynomialRankWeight, vertexDegree_add, Nat.cast_add]
  nlinarith

theorem polynomialRankWeight_nonnegative (d : ℕ) (hd : Fintype.card V ≤ d)
    (a : V → ℕ) : 0 ≤ polynomialRankWeight d a := by
  have hc : (overlapCost a : ℤ) ≤ (Fintype.card V : ℤ) * vertexDegree a := by
    exact_mod_cast overlapCost_le_card_mul_degree a
  have hd' : (Fintype.card V : ℤ) ≤ d := by exact_mod_cast hd
  have ha : (0 : ℤ) ≤ vertexDegree a := Nat.cast_nonneg _
  have hdn : (0 : ℤ) ≤ d := Nat.cast_nonneg _
  unfold polynomialRankWeight
  nlinarith

def faceIndicator (s : Finset V) (v : V) : ℕ := by
  classical
  exact if v ∈ s then 1 else 0

@[simp] theorem vertexDegree_indicator (s : Finset V) :
    vertexDegree (faceIndicator s) = s.card := by
  classical
  simp [vertexDegree, faceIndicator]

theorem overlapCost_indicator (s : Finset V) :
    overlapCost (faceIndicator s) = s.card * s.card := by
  classical
  have hmin (v w : V) :
      min (faceIndicator s v) (faceIndicator s w) =
        faceIndicator s v * faceIndicator s w := by
    by_cases hv : v ∈ s <;> by_cases hw : w ∈ s <;> simp [faceIndicator, hv, hw]
  calc
    overlapCost (faceIndicator s) =
        ∑ v, ∑ w, faceIndicator s v * faceIndicator s w := by
      simp only [overlapCost, hmin]
    _ = vertexDegree (faceIndicator s) * vertexDegree (faceIndicator s) := by
      unfold vertexDegree
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro v hv
      rw [Finset.mul_sum]
    _ = s.card * s.card := by rw [vertexDegree_indicator]

@[simp] theorem polynomialRankWeight_indicator (d : ℕ) (s : Finset V) :
    polynomialRankWeight d (faceIndicator s) = rankWeight d s.card := by
  rw [polynomialRankWeight, vertexDegree_indicator, overlapCost_indicator]
  simp only [Nat.cast_mul, rankWeight]
  ring

variable [DecidableEq V]

/-- The exact weight drop in the Boolean straightening relation. -/
theorem rankWeight_straightening_difference (d : ℕ) (s t : Finset V) :
    rankWeight d s.card + rankWeight d t.card -
        rankWeight d (s ∩ t).card - rankWeight d (s ∪ t).card =
      2 * ((s.card : ℤ) - (s ∩ t).card) * ((t.card : ℤ) - (s ∩ t).card) := by
  classical
  have hu : ((s ∪ t).card : ℤ) + (s ∩ t).card = (s.card : ℤ) + t.card := by
    exact_mod_cast Finset.card_union_add_card_inter s t
  have hu' : ((s ∪ t).card : ℤ) = (s.card : ℤ) + t.card - (s ∩ t).card := by
    linarith
  unfold rankWeight
  rw [hu']
  ring

theorem rankWeight_straightening_strict (d : ℕ) (s t : Finset V)
    (hst : ¬ s ⊆ t) (hts : ¬ t ⊆ s) :
    rankWeight d (s ∩ t).card + rankWeight d (s ∪ t).card <
      rankWeight d s.card + rankWeight d t.card := by
  classical
  have hs : (s ∩ t).card < s.card := by
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.inter_subset_left, ?_⟩
    intro he
    exact hst (by rw [← he]; exact Finset.inter_subset_right)
  have ht : (s ∩ t).card < t.card := by
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.inter_subset_right, ?_⟩
    intro he
    exact hts (by rw [← he]; exact Finset.inter_subset_left)
  have hs' : ((s ∩ t).card : ℤ) < s.card := by exact_mod_cast hs
  have ht' : ((s ∩ t).card : ℤ) < t.card := by exact_mod_cast ht
  have hpos := mul_pos (sub_pos.mpr hs') (sub_pos.mpr ht')
  have hd := rankWeight_straightening_difference d s t
  nlinarith

end FourPapers.Universal

end
end

/- BEGIN FaceIntervals.lean -/
section


/-! # Joins inside Boolean face intervals and exact straightening weights -/

noncomputable section

set_option autoImplicit false

namespace FourPapers.Universal

open Classical Finset

variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]

/-- The smallest common upper face inside a specified Boolean interval. -/
def faceJoinBelow (hs : IsSimplicialPoset P) (p q w : P)
    (hpw : p ≤ w) (hqw : q ≤ w) : P :=
  ((existsUnique_subface hs w (faceVertices p ∪ faceVertices q)
    (Finset.union_subset (faceVertices_mono hpw) (faceVertices_mono hqw))).choose).val

theorem faceJoinBelow_le_top (hs : IsSimplicialPoset P) (p q w : P)
    (hpw : p ≤ w) (hqw : q ≤ w) : faceJoinBelow hs p q w hpw hqw ≤ w :=
  ((existsUnique_subface hs w (faceVertices p ∪ faceVertices q)
    (Finset.union_subset (faceVertices_mono hpw) (faceVertices_mono hqw))).choose).property

theorem faceJoinBelow_vertices (hs : IsSimplicialPoset P) (p q w : P)
    (hpw : p ≤ w) (hqw : q ≤ w) :
    faceVertices (faceJoinBelow hs p q w hpw hqw) = faceVertices p ∪ faceVertices q :=
  (existsUnique_subface hs w (faceVertices p ∪ faceVertices q)
    (Finset.union_subset (faceVertices_mono hpw) (faceVertices_mono hqw))).choose_spec.1

theorem left_le_faceJoinBelow (hs : IsSimplicialPoset P) (p q w : P)
    (hpw : p ≤ w) (hqw : q ≤ w) : p ≤ faceJoinBelow hs p q w hpw hqw := by
  apply (faceVertices_subset_iff hs hpw (faceJoinBelow_le_top hs p q w hpw hqw)).mp
  rw [faceJoinBelow_vertices]
  exact Finset.subset_union_left

theorem right_le_faceJoinBelow (hs : IsSimplicialPoset P) (p q w : P)
    (hpw : p ≤ w) (hqw : q ≤ w) : q ≤ faceJoinBelow hs p q w hpw hqw := by
  apply (faceVertices_subset_iff hs hqw (faceJoinBelow_le_top hs p q w hpw hqw)).mp
  rw [faceJoinBelow_vertices]
  exact Finset.subset_union_right

theorem faceJoinBelow_le (hs : IsSimplicialPoset P) (p q w : P)
    (hpw : p ≤ w) (hqw : q ≤ w) {u : P} (hpu : p ≤ u) (hqu : q ≤ u)
    (huw : u ≤ w) : faceJoinBelow hs p q w hpw hqw ≤ u := by
  apply (faceVertices_subset_iff hs (faceJoinBelow_le_top hs p q w hpw hqw) huw).mp
  rw [faceJoinBelow_vertices]
  exact Finset.union_subset (faceVertices_mono hpu) (faceVertices_mono hqu)

theorem faceJoinBelow_minimal (hs : IsSimplicialPoset P) (p q w : P)
    (hpw : p ≤ w) (hqw : q ≤ w) :
    IsMinimalCommonUpper p q (faceJoinBelow hs p q w hpw hqw) := by
  refine ⟨left_le_faceJoinBelow hs p q w hpw hqw,
    right_le_faceJoinBelow hs p q w hpw hqw, ?_⟩
  intro v hpv hqv hv
  exact le_antisymm hv (faceJoinBelow_le hs p q w hpw hqw hpv hqv
    (hv.trans (faceJoinBelow_le_top hs p q w hpw hqw)))

theorem minimalCommonUpper_eq_join (hs : IsSimplicialPoset P) {p q u w : P}
    (hu : IsMinimalCommonUpper p q u) (huw : u ≤ w) :
    u = faceJoinBelow hs p q w (hu.1.trans huw) (hu.2.1.trans huw) := by
  symm
  exact hu.2.2 _
    (left_le_faceJoinBelow hs p q w _ _)
    (right_le_faceJoinBelow hs p q w _ _)
    (faceJoinBelow_le hs p q w _ _ hu.1 hu.2.1 huw)

theorem minimalCommonUpper_vertices (hs : IsSimplicialPoset P) {p q u : P}
    (hu : IsMinimalCommonUpper p q u) :
    faceVertices u = faceVertices p ∪ faceVertices q := by
  rw [minimalCommonUpper_eq_join hs hu le_rfl]
  exact faceJoinBelow_vertices hs p q u _ _

/-- Exactly one minimal common upper face survives restriction to a face
containing both inputs. The other minimal uppers may be genuinely different
faces with the same vertex set. -/
theorem minimalCommonUppers_below_eq_singleton (hs : IsSimplicialPoset P)
    (p q w : P) (hpw : p ≤ w) (hqw : q ≤ w) :
    (minimalCommonUppers p q).filter (· ≤ w) =
      {faceJoinBelow hs p q w hpw hqw} := by
  ext u
  simp only [Finset.mem_filter, mem_minimalCommonUppers, Finset.mem_singleton]
  constructor
  · rintro ⟨hu, huw⟩
    exact minimalCommonUpper_eq_join hs hu huw
  · rintro rfl
    exact ⟨faceJoinBelow_minimal hs p q w hpw hqw,
      faceJoinBelow_le_top hs p q w hpw hqw⟩

/-- Rank additivity in each actual straightening relation. -/
theorem faceRank_meet_add_upper (hs : IsSimplicialPoset P) {p q u : P}
    (hu : IsMinimalCommonUpper p q u) :
    faceRank (faceMeetBelow hs p q u hu.1 hu.2.1) + faceRank u =
      faceRank p + faceRank q := by
  unfold faceRank
  rw [faceMeetBelow_vertices, minimalCommonUpper_vertices hs hu, add_comm]
  exact Finset.card_union_add_card_inter _ _

/-- The strict weight decrease uses precisely `r(2d-r)`. -/
theorem face_straightening_weight_strict (hs : IsSimplicialPoset P)
    (d : ℕ) {p q u : P} (hu : IsMinimalCommonUpper p q u)
    (hpq : ¬ p ≤ q) (hqp : ¬ q ≤ p) :
    rankWeight d (faceRank (faceMeetBelow hs p q u hu.1 hu.2.1)) +
        rankWeight d (faceRank u) <
      rankWeight d (faceRank p) + rankWeight d (faceRank q) := by
  unfold faceRank
  rw [faceMeetBelow_vertices, minimalCommonUpper_vertices hs hu]
  apply rankWeight_straightening_strict
  · exact fun h => hpq ((faceVertices_subset_iff hs hu.1 hu.2.1).mp h)
  · exact fun h => hqp ((faceVertices_subset_iff hs hu.2.1 hu.1).mp h)

end FourPapers.Universal
end
end

/- BEGIN FaceEvaluation.lean -/
section


/-!
# Evaluation of the original face ring in its polynomial stalks

Each face generator is sent to the product of its vertex variables when the
face is contained in the stalk, and to zero otherwise. The straightening
relations are proved to vanish, so the map descends from the original quotient.
-/

noncomputable section

set_option autoImplicit false

namespace FourPapers.Universal

open Classical Finset MvPolynomial

variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K]

/-- The vertices of `q` that occur in the ambient face `p`. -/
def stalkVertexSet (p q : P) : Finset (FaceVertex p) :=
  univ.filter fun a => a.val ≤ q

@[simp] theorem mem_stalkVertexSet (p q : P) (a : FaceVertex p) :
    a ∈ stalkVertexSet p q ↔ a.val ≤ q := by simp [stalkVertexSet]

@[simp] theorem stalkVertexSet_bot (p : P) : stalkVertexSet p (⊥ : P) = ∅ := by
  ext a
  simp only [mem_stalkVertexSet]
  exact iff_of_false (fun ha => a.property.1.ne_bot (le_bot_iff.mp ha)) (by simp)

def faceProduct (p q : P) : PolynomialStalk K p :=
  ∏ a ∈ stalkVertexSet p q, X a

@[simp] theorem faceProduct_bot (p : P) : faceProduct K p (⊥ : P) = 1 := by
  simp [faceProduct]

def faceValue (p q : P) : PolynomialStalk K p :=
  if q ≤ p then faceProduct K p q else 0

@[simp] theorem faceValue_bot (p : P) : faceValue K p (⊥ : P) = 1 := by
  simp [faceValue]

theorem stalkVertexSet_meet (hs : IsSimplicialPoset P) (p q w r : P)
    (hpw : p ≤ w) (hqw : q ≤ w) :
    stalkVertexSet r (faceMeetBelow hs p q w hpw hqw) =
      stalkVertexSet r p ∩ stalkVertexSet r q := by
  ext a
  simp only [mem_stalkVertexSet, mem_inter]
  constructor
  · intro h
    exact ⟨h.trans (faceMeetBelow_le_left hs p q w hpw hqw),
      h.trans (faceMeetBelow_le_right hs p q w hpw hqw)⟩
  · rintro ⟨hp, hq⟩
    exact le_faceMeetBelow hs p q w hpw hqw hp hq

theorem stalkVertexSet_join (hs : IsSimplicialPoset P) (p q w r : P)
    (hpw : p ≤ w) (hqw : q ≤ w) :
    stalkVertexSet r (faceJoinBelow hs p q w hpw hqw) =
      stalkVertexSet r p ∪ stalkVertexSet r q := by
  ext a
  have hm (x : P) : a.val ∈ faceVertices x ↔ a.val ≤ x := by
    simp [a.property.1]
  simp only [mem_stalkVertexSet, mem_union]
  rw [← hm, faceJoinBelow_vertices, mem_union, hm, hm]

theorem faceProduct_straightening (hs : IsSimplicialPoset P) (p q w r : P)
    (hpw : p ≤ w) (hqw : q ≤ w) :
    faceProduct K r p * faceProduct K r q =
      faceProduct K r (faceMeetBelow hs p q w hpw hqw) *
        faceProduct K r (faceJoinBelow hs p q w hpw hqw) := by
  unfold faceProduct
  rw [stalkVertexSet_meet, stalkVertexSet_join]
  exact (Finset.prod_union_inter (f := fun a : FaceVertex r => (X a : PolynomialStalk K r))).symm.trans
    (mul_comm _ _)

theorem sum_faceValue_minimalCommonUppers (hs : IsSimplicialPoset P)
    (p q r : P) (hpr : p ≤ r) (hqr : q ≤ r) :
    (∑ u ∈ minimalCommonUppers p q, faceValue K r u) =
      faceProduct K r (faceJoinBelow hs p q r hpr hqr) := by
  unfold faceValue
  rw [← Finset.sum_filter, minimalCommonUppers_below_eq_singleton hs p q r hpr hqr]
  simp

theorem sum_faceValue_minimalCommonUppers_of_not_left (p q r : P) (hpr : ¬ p ≤ r) :
    (∑ u ∈ minimalCommonUppers p q, faceValue K r u) = 0 := by
  apply Finset.sum_eq_zero
  intro u hu
  have hur : ¬ u ≤ r := fun h => hpr (((mem_minimalCommonUppers p q u).mp hu).1.trans h)
  simp [faceValue, hur]

theorem sum_faceValue_minimalCommonUppers_of_not_right (p q r : P) (hqr : ¬ q ≤ r) :
    (∑ u ∈ minimalCommonUppers p q, faceValue K r u) = 0 := by
  apply Finset.sum_eq_zero
  intro u hu
  have hur : ¬ u ≤ r := fun h => hqr (((mem_minimalCommonUppers p q u).mp hu).2.1.trans h)
  simp [faceValue, hur]

theorem faceValue_straightening (hs : IsSimplicialPoset P) (p q w r : P)
    (hpw : p ≤ w) (hqw : q ≤ w) :
    faceValue K r p * faceValue K r q =
      faceValue K r (faceMeetBelow hs p q w hpw hqw) *
        ∑ u ∈ minimalCommonUppers p q, faceValue K r u := by
  by_cases hpr : p ≤ r
  · by_cases hqr : q ≤ r
    · have hmr : faceMeetBelow hs p q w hpw hqw ≤ r :=
        (faceMeetBelow_le_left hs p q w hpw hqw).trans hpr
      rw [sum_faceValue_minimalCommonUppers K hs p q r hpr hqr]
      simp only [faceValue, if_pos hpr, if_pos hqr, if_pos hmr]
      rw [faceMeetBelow_independent hs p q w r hpw hqw hpr hqr]
      exact faceProduct_straightening K hs p q r r hpr hqr
    · rw [sum_faceValue_minimalCommonUppers_of_not_right K p q r hqr]
      simp [faceValue, hqr]
  · rw [sum_faceValue_minimalCommonUppers_of_not_left K p q r hpr]
    simp [faceValue, hpr]

/-- Evaluation before taking the original face-ring quotient. -/
def faceEvaluation (r : P) : FacePolynomial (P := P) K →ₐ[K] PolynomialStalk K r :=
  MvPolynomial.aeval fun p => faceValue K r p.val

@[simp] theorem faceEvaluation_symbol (r p : P) :
    faceEvaluation K r (faceSymbol K p) = faceValue K r p := by
  by_cases hp : p = ⊥
  · subst p
    simp
  · simp [faceSymbol, hp, faceEvaluation]

theorem faceEvaluation_relation (hs : IsSimplicialPoset P) (r : P)
    {f : FacePolynomial (P := P) K} (hf : f ∈ faceRelations K hs) :
    faceEvaluation K r f = 0 := by
  rcases hf with ⟨p, q, w, hpw, hqw, rfl⟩ | ⟨p, q, hnone, rfl⟩
  · simp only [map_sub, map_mul, map_sum, faceEvaluation_symbol]
    exact sub_eq_zero.mpr (faceValue_straightening K hs p q w r hpw hqw)
  · simp only [map_mul, faceEvaluation_symbol]
    by_cases hpr : p ≤ r
    · have hqr : ¬ q ≤ r := fun h => hnone ⟨r, hpr, h⟩
      simp [faceValue, hqr]
    · simp [faceValue, hpr]

/-- The map is defined on the conventional face-ring presentation. -/
def faceRingEvaluation (hs : IsSimplicialPoset P) (r : P) :
    FaceRing K hs →ₐ[K] PolynomialStalk K r :=
  Ideal.Quotient.liftₐ (faceIdeal K hs) (faceEvaluation K r) (by
    change faceIdeal K hs ≤ RingHom.ker (faceEvaluation K r).toRingHom
    apply Ideal.span_le.mpr
    intro f hf
    exact faceEvaluation_relation K hs r hf)

@[simp] theorem faceRingEvaluation_generator (hs : IsSimplicialPoset P) (r p : P) :
    faceRingEvaluation K hs r (faceRingGenerator K hs p) = faceValue K r p :=
  faceEvaluation_symbol K r p

end FourPapers.Universal
end
end

/- BEGIN MonomialQuotient.lean -/
section


/-! # The actual monomial quotient and its standard monomial basis

The quotient in this file is the quotient of the ordinary multivariate polynomial
ring by the ideal generated by its forbidden monomials.  Its basis theorem is
proved from the coefficientwise membership theorem for monomial ideals.
-/

noncomputable section

set_option autoImplicit false

set_option maxHeartbeats 1000000

namespace FourPapers.Universal

open Classical

variable {V K : Type*} [CommRing K]

/-- An allowed collection of exponent vectors is closed under divisibility. -/
def IsDivisorClosed (P : (V →₀ ℕ) → Prop) : Prop :=
  ∀ ⦃a b⦄, a ≤ b → P b → P a

/-- The actual ideal generated by the forbidden monomials. -/
def forbiddenIdeal (P : (V →₀ ℕ) → Prop) : Ideal (MvPolynomial V K) :=
  Ideal.span ((fun a : V →₀ ℕ => MvPolynomial.monomial a (1 : K)) '' {a | ¬ P a})

lemma mem_forbiddenIdeal (P : (V →₀ ℕ) → Prop) (hP : IsDivisorClosed P)
    (f : MvPolynomial V K) :
    f ∈ forbiddenIdeal P ↔ ∀ a, P a → f.coeff a = 0 := by
  rw [forbiddenIdeal, MvPolynomial.mem_ideal_span_monomial_image]
  constructor
  · intro h a ha
    by_contra hc
    obtain ⟨b, hb, hba⟩ := h a (MvPolynomial.mem_support_iff.mpr hc)
    exact hb (hP hba ha)
  · intro h a ha
    refine ⟨a, ?_, le_rfl⟩
    intro hp
    exact (MvPolynomial.mem_support_iff.mp ha) (h a hp)

/-- The usual monomial quotient algebra. -/
abbrev MonomialQuotient (P : (V →₀ ℕ) → Prop) :=
  MvPolynomial V K ⧸ forbiddenIdeal P

/-- Read off precisely the coefficients of the allowed monomials. -/
def standardCoefficients (P : (V →₀ ℕ) → Prop) :
    MvPolynomial V K →ₗ[K] ({a // P a} →₀ K) :=
  (Finsupp.lsubtypeDomain {a | P a}).comp
    (MvPolynomial.basisMonomials V K).repr.toLinearMap

@[simp] lemma standardCoefficients_apply (P : (V →₀ ℕ) → Prop)
    (f : MvPolynomial V K) (a : {a // P a}) :
    standardCoefficients P f a = f.coeff a.val := rfl

lemma standardCoefficients_surjective (P : (V →₀ ℕ) → Prop) :
    Function.Surjective (standardCoefficients (K := K) P) := by
  intro x
  refine ⟨(MvPolynomial.basisMonomials V K).repr.symm
    (Finsupp.mapDomain Subtype.val x), ?_⟩
  change (Finsupp.lsubtypeDomain (R := K) {a | P a})
    ((MvPolynomial.basisMonomials V K).repr
      ((MvPolynomial.basisMonomials V K).repr.symm
        (Finsupp.mapDomain Subtype.val x))) = x
  rw [LinearEquiv.apply_symm_apply]
  ext a
  exact Finsupp.mapDomain_apply_of_injective Subtype.val_injective x a

lemma standardCoefficients_ker (P : (V →₀ ℕ) → Prop)
    (hP : IsDivisorClosed P) :
    LinearMap.ker (standardCoefficients (K := K) P) =
      (forbiddenIdeal P).restrictScalars K := by
  ext f
  rw [LinearMap.mem_ker]
  change standardCoefficients P f = 0 ↔ f ∈ forbiddenIdeal P
  rw [mem_forbiddenIdeal P hP]
  constructor
  · intro h a ha
    exact congrArg (fun c => c ⟨a, ha⟩) h
  · intro h
    ext a
    exact h a.val a.property

/-- A coefficient equivalence on the genuine quotient, not on a surrogate vector
space.  It provides the standard monomial basis over every commutative ring. -/
def standardMonomialEquiv (P : (V →₀ ℕ) → Prop) (hP : IsDivisorClosed P) :
    MonomialQuotient (K := K) P ≃ₗ[K] ({a // P a} →₀ K) :=
  (Submodule.quotEquivOfEq _ _ (standardCoefficients_ker (K := K) P hP).symm).trans
    ((standardCoefficients (K := K) P).quotKerEquivOfSurjective
      (standardCoefficients_surjective (K := K) P))

@[simp] lemma standardMonomialEquiv_mk (P : (V →₀ ℕ) → Prop)
    (hP : IsDivisorClosed P) (f : MvPolynomial V K) :
    standardMonomialEquiv P hP (Ideal.Quotient.mk (forbiddenIdeal P) f) =
      standardCoefficients P f := by
  rfl

/-- The allowed monomials form a basis of the actual quotient. -/
def standardMonomialBasis (P : (V →₀ ℕ) → Prop) (hP : IsDivisorClosed P) :
    Module.Basis {a // P a} K (MonomialQuotient (K := K) P) :=
  (Finsupp.basisSingleOne).map (standardMonomialEquiv P hP).symm

@[simp] lemma standardMonomialBasis_apply (P : (V →₀ ℕ) → Prop)
    (hP : IsDivisorClosed P) (a : {a // P a}) :
    standardMonomialBasis (K := K) P hP a =
      Ideal.Quotient.mk (forbiddenIdeal P) (MvPolynomial.monomial a.val 1) := by
  apply (standardMonomialEquiv (K := K) P hP).injective
  ext b
  simp [standardMonomialBasis, MvPolynomial.coeff_monomial,
    Finsupp.single_apply, Subtype.ext_iff]

end FourPapers.Universal
end
end

/- BEGIN PermutationFlags.lean -/
section


/-! # Full Boolean flags, descents, and their lexicographic order

The combinatorics in this file is independent of the coefficient ring. A vertex
ordering is an actual bijection, its prefixes are actual subsets, and a descent
has its usual adjacent-value meaning.
-/

set_option autoImplicit false

noncomputable section

namespace FourPapers.Universal

open Finset Classical

variable {V : Type*} [LinearOrder V] {n : ℕ}

/-- A full flag, written by the order in which its vertices enter. -/
abbrev VertexOrdering (n : ℕ) (V : Type*) := Fin n ≃ V

/-- The prefix of rank `c+1`. -/
def orderingPrefix (σ : VertexOrdering n V) (c : Fin n) : Finset V :=
  (Finset.Iic c).image σ

@[simp] theorem mem_orderingPrefix (σ : VertexOrdering n V) (c : Fin n) (v : V) :
    v ∈ orderingPrefix σ c ↔ σ.symm v ≤ c := by
  constructor
  · intro hv
    obtain ⟨i, hi, hiv⟩ := Finset.mem_image.mp hv
    have hie : i = σ.symm v := by
      apply σ.injective
      simpa using hiv
    simpa [hie] using hi
  · intro hv
    exact Finset.mem_image.mpr ⟨σ.symm v, Finset.mem_Iic.mpr hv, σ.apply_symm_apply v⟩

@[simp] theorem card_orderingPrefix (σ : VertexOrdering n V) (c : Fin n) :
    (orderingPrefix σ c).card = c.val + 1 := by
  rw [orderingPrefix, Finset.card_image_of_injective _ σ.injective, Fin.card_Iic]

theorem orderingPrefix_nonempty (σ : VertexOrdering n V) (c : Fin n) :
    (orderingPrefix σ c).Nonempty := by
  exact Finset.card_pos.mp (by rw [card_orderingPrefix]; omega)

theorem orderingPrefix_mono (σ : VertexOrdering n V) : Monotone (orderingPrefix σ) := by
  intro i j hij v hv
  exact (mem_orderingPrefix σ j v).mpr ((mem_orderingPrefix σ i v).mp hv |>.trans hij)

/-- A descent after position `c`; the last position is never a descent. -/
def IsOrderingDescent (σ : VertexOrdering n V) (c : Fin n) : Prop :=
  ∃ h : c.val + 1 < n, σ ⟨c.val + 1, h⟩ < σ c

def orderingDescents (σ : VertexOrdering n V) : Finset (Fin n) :=
  Finset.univ.filter (IsOrderingDescent σ)

@[simp] theorem mem_orderingDescents (σ : VertexOrdering n V) (c : Fin n) :
    c ∈ orderingDescents σ ↔ IsOrderingDescent σ c := by
  simp [orderingDescents]

/-- An interval containing no adjacent descent is increasing. -/
theorem ordering_le_of_no_descent {σ : VertexOrdering n V} {i j : Fin n}
    (hij : i ≤ j)
    (h : ∀ c : Fin n, i ≤ c → c < j → ¬ IsOrderingDescent σ c) :
    σ i ≤ σ j := by
  have haux : ∀ (t : ℕ) (ht : t < n), i.val ≤ t → t ≤ j.val →
      σ i ≤ σ ⟨t, ht⟩ := by
    intro t
    induction t with
    | zero =>
      intro ht hi hj
      have he : i = ⟨0, ht⟩ := Fin.ext (Nat.eq_zero_of_le_zero hi)
      simp [he]
    | succ t ih =>
      intro ht hi hj
      by_cases hie : i.val = t + 1
      · have he : i = ⟨t + 1, ht⟩ := Fin.ext hie
        simpa [he]
      · have hit : i.val ≤ t := by omega
        have htn : t < n := by omega
        have htj : t < j.val := by omega
        have hs : σ ⟨t, htn⟩ ≤ σ ⟨t + 1, ht⟩ := by
          apply le_of_not_gt
          intro hn
          exact h ⟨t, htn⟩ hit htj ⟨ht, hn⟩
        exact (ih htn hit (by omega)).trans hs
  exact haux j.val j.isLt hij le_rfl

theorem exists_orderingDescent_between {σ : VertexOrdering n V} {i j : Fin n}
    (hij : i < j) (hval : σ j < σ i) :
    ∃ c : Fin n, i ≤ c ∧ c < j ∧ IsOrderingDescent σ c := by
  by_contra hn
  have h : ∀ c : Fin n, i ≤ c → c < j → ¬ IsOrderingDescent σ c := by
    intro c hic hcj hc
    exact hn ⟨c, hic, hcj, hc⟩
  exact (not_le_of_gt hval) (ordering_le_of_no_descent hij.le h)

/-- Fixing all descent prefixes forces an ordering to be lexicographically no
earlier than the original ordering. This is the triangularity mechanism for
the descent-monomial basis. -/
theorem ordering_lex_le_of_descent_prefix {σ τ : VertexOrdering n V}
    (hprefix : ∀ c, IsOrderingDescent σ c → orderingPrefix τ c = orderingPrefix σ c) :
    toLex (fun i => σ i) ≤ toLex (fun i => τ i) := by
  by_contra hn
  have hlt : toLex (fun i => τ i) < toLex (fun i => σ i) := lt_of_not_ge hn
  obtain ⟨i, hearlier, hval⟩ := hlt
  let j : Fin n := σ.symm (τ i)
  have hjval : σ j = τ i := σ.apply_symm_apply (τ i)
  have hij : i < j := by
    by_contra hnij
    have hji : j ≤ i := le_of_not_gt hnij
    rcases lt_or_eq_of_le hji with hji | hji
    · have he : τ j = τ i := (hearlier j hji).trans hjval
      have hje := τ.injective he
      exact (ne_of_lt hji) hje
    · have he : τ i = σ i := by simpa [hji] using hjval.symm
      exact (ne_of_lt hval) he
  have hval' : σ j < σ i := by simpa [hjval] using hval
  obtain ⟨c, hic, hcj, hc⟩ := exists_orderingDescent_between hij hval'
  have hm : τ i ∈ orderingPrefix τ c := by
    simpa only [mem_orderingPrefix, Equiv.symm_apply_apply] using hic
  rw [hprefix c hc] at hm
  have hjc : j ≤ c := (mem_orderingPrefix σ c (τ i)).mp hm
  exact (not_le_of_gt hcj) hjc

/-- The preceding triangularity yields uniqueness of the increasing-block
refinement of a partially specified flag. -/
theorem ordering_eq_of_descent_prefixes {σ τ : VertexOrdering n V}
    (hστ : ∀ c, IsOrderingDescent σ c → orderingPrefix τ c = orderingPrefix σ c)
    (hτσ : ∀ c, IsOrderingDescent τ c → orderingPrefix σ c = orderingPrefix τ c) :
    σ = τ := by
  have he := le_antisymm (ordering_lex_le_of_descent_prefix hστ)
    (ordering_lex_le_of_descent_prefix hτσ)
  apply Equiv.ext
  exact congrFun (congrArg ofLex he)

section Weights

variable [Fintype V]

/-- Order the vertices by decreasing weight, resolving equal weights by the
original vertex order. This exists for every finite vertex set, including the
empty one. -/
theorem exists_weightOrdering (w : V → ℕ) :
    ∃ σ : VertexOrdering (Fintype.card V) V,
      ∀ i j, i < j → w (σ j) < w (σ i) ∨
        (w (σ i) = w (σ j) ∧ σ i < σ j) := by
  let code : V → (OrderDual ℕ ×ₗ V) := fun v => toLex (OrderDual.toDual (w v), v)
  have hcode : Function.Injective code := by
    intro v u h
    exact congrArg (fun x => (ofLex x).2) h
  obtain ⟨σ, hσ⟩ : ∃ σ : VertexOrdering (Fintype.card V) V,
      ∀ i j, i < j → code (σ i) < code (σ j) := by
    letI : LinearOrder V := LinearOrder.lift' code hcode
    let σ := Fintype.orderIsoFinOfCardEq V rfl
    refine ⟨σ.toEquiv, ?_⟩
    intro i j hij
    exact σ.strictMono hij
  refine ⟨σ, ?_⟩
  intro i j hij
  have hlt : code (σ i) < code (σ j) := hσ i j hij
  exact Prod.Lex.toLex_lt_toLex.mp hlt

def weightOrdering (w : V → ℕ) : VertexOrdering (Fintype.card V) V :=
  Classical.choose (exists_weightOrdering w)

theorem weightOrdering_order (w : V → ℕ) {i j : Fin (Fintype.card V)} (hij : i < j) :
    w (weightOrdering w j) < w (weightOrdering w i) ∨
      (w (weightOrdering w i) = w (weightOrdering w j) ∧
        weightOrdering w i < weightOrdering w j) :=
  Classical.choose_spec (exists_weightOrdering w) i j hij

theorem weightOrdering_antitone (w : V → ℕ) :
    Antitone (fun i => w (weightOrdering w i)) := by
  intro i j hij
  rcases lt_or_eq_of_le hij with hij | rfl
  · rcases weightOrdering_order w hij with hw | ⟨hw, _⟩
    · exact hw.le
    · exact hw.ge
  · exact le_rfl

theorem weightOrdering_descent_lt (w : V → ℕ) {c : Fin (Fintype.card V)}
    (hc : IsOrderingDescent (weightOrdering w) c) :
    ∃ h : c.val + 1 < Fintype.card V,
      w (weightOrdering w ⟨c.val + 1, h⟩) < w (weightOrdering w c) := by
  obtain ⟨h, hc⟩ := hc
  refine ⟨h, ?_⟩
  rcases weightOrdering_order w
    (show c < ⟨c.val + 1, h⟩ from Nat.lt_succ_self c.val) with hw | ⟨hw, ho⟩
  · exact hw
  · exact (not_lt_of_gt hc ho).elim

end Weights

/-- A set whose vertices all have greater weight than its complement is an
initial segment in every decreasing-weight ordering. -/
theorem orderingPrefix_eq_of_weight_separation (w : V → ℕ)
    (σ : VertexOrdering n V) (ha : Antitone (fun i => w (σ i)))
    (F : Finset V) (c : Fin n) (hcard : F.card = c.val + 1)
    (hsep : ∀ x ∈ F, ∀ y ∉ F, w y < w x) : orderingPrefix σ c = F := by
  have hsub : F ⊆ orderingPrefix σ c := by
    intro v hv
    let j := σ.symm v
    have hp : orderingPrefix σ j ⊆ F := by
      intro u hu
      by_contra hun
      have hju : w (σ j) ≤ w (σ (σ.symm u)) :=
        ha ((mem_orderingPrefix σ j u).mp hu)
      have huv : w v ≤ w u := by simpa [j] using hju
      exact (not_le_of_gt (hsep v hv u hun)) huv
    have hcj := Finset.card_le_card hp
    rw [card_orderingPrefix, hcard] at hcj
    apply (mem_orderingPrefix σ c v).mpr
    change j ≤ c
    omega
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [card_orderingPrefix, hcard])).symm

/-- Number of specified faces containing a vertex. -/
def flagScore (C : Finset (Finset V)) (v : V) : ℕ :=
  (C.filter (fun F => v ∈ F)).card

/-- A chain separates its vertices strictly by the number of faces containing
them. This avoids any choice of a maximal refinement. -/
theorem flagScore_lt_of_mem_notMem {C : Finset (Finset V)}
    (hC : ∀ F ∈ C, ∀ G ∈ C, F ⊆ G ∨ G ⊆ F)
    {F : Finset V} (hF : F ∈ C) {x y : V} (hx : x ∈ F) (hy : y ∉ F) :
    flagScore C y < flagScore C x := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro G hG
    obtain ⟨hGC, hyG⟩ := Finset.mem_filter.mp hG
    apply Finset.mem_filter.mpr
    refine ⟨hGC, ?_⟩
    rcases hC F hF G hGC with hFG | hGF
    · exact hFG hx
    · exact (hy (hGF hyG)).elim
  · intro he
    have hxF : F ∈ C.filter (fun G => x ∈ G) := Finset.mem_filter.mpr ⟨hF, hx⟩
    rw [← he] at hxF
    exact hy (Finset.mem_filter.mp hxF).2

theorem exists_mem_notMem_of_flagScore_lt {C : Finset (Finset V)} {x y : V}
    (h : flagScore C y < flagScore C x) :
    ∃ F ∈ C, x ∈ F ∧ y ∉ F := by
  by_contra hn
  have hsub : C.filter (fun F => x ∈ F) ⊆ C.filter (fun F => y ∈ F) := by
    intro F hF
    obtain ⟨hFC, hxF⟩ := Finset.mem_filter.mp hF
    refine Finset.mem_filter.mpr ⟨hFC, ?_⟩
    by_contra hyF
    exact hn ⟨F, hFC, hxF, hyF⟩
  exact (not_le_of_gt h) (Finset.card_le_card hsub)

end FourPapers.Universal
end
end

/- BEGIN BooleanBasis.lean -/
section


/-! # Boolean barycentric rings and their color structure

All rings below are genuine quotients of multivariate polynomial rings.
The coefficient ring is arbitrary and may have positive characteristic or
zero divisors.
-/

set_option autoImplicit false

noncomputable section

namespace FourPapers.Universal

open Classical Finset

variable {V K : Type*} [Fintype V] [DecidableEq V] [CommRing K]

/-- Nonempty faces of the Boolean simplex on `V`. -/
abbrev BooleanFace (V : Type*) [DecidableEq V] := {F : Finset V // F.Nonempty}

/-- Rank minus one, to index the rank parameters by `Fin (card V)`. -/
def BooleanFace.color (F : BooleanFace V) : Fin (Fintype.card V) :=
  ⟨F.val.card - 1, by
    have hp : 0 < F.val.card := card_pos.mpr F.property
    have hb : F.val.card ≤ Fintype.card V := card_le_univ F.val
    omega⟩

@[simp] theorem BooleanFace.color_succ (F : BooleanFace V) :
    (BooleanFace.color F).val + 1 = F.val.card := by
  have hp : 0 < F.val.card := card_pos.mpr F.property
  simp only [BooleanFace.color]
  omega

theorem BooleanFace.card_eq_of_color_eq {F G : BooleanFace V}
    (h : (BooleanFace.color F) = G.color) : F.val.card = G.val.card := by
  have hv := congrArg Fin.val h
  have hF := F.color_succ
  have hG := G.color_succ
  omega

/-- The support of a standard barycentric monomial is a chain of faces. -/
def IsChainExponent (a : BooleanFace V →₀ ℕ) : Prop :=
  ∀ F ∈ a.support, ∀ G ∈ a.support, F.val ⊆ G.val ∨ G.val ⊆ F.val

theorem isChainExponent_divisorClosed : IsDivisorClosed (IsChainExponent (V := V)) := by
  intro a b hab hb F hF G hG
  exact hb F (Finsupp.support_mono hab hF) G (Finsupp.support_mono hab hG)

theorem isChainExponent_zero : IsChainExponent (0 : BooleanFace V →₀ ℕ) := by
  simp [IsChainExponent]

theorem isChainExponent_single (F : BooleanFace V) (m : ℕ) :
    IsChainExponent (Finsupp.single F m) := by
  intro G hG H hH
  have hGF : G = F := ((Finsupp.mem_support_single G F m).mp hG).1
  have hHF : H = F := ((Finsupp.mem_support_single H F m).mp hH).1
  subst G
  subst H
  exact Or.inl Subset.rfl

theorem eq_of_chain_of_color_eq {a : BooleanFace V →₀ ℕ}
    (ha : IsChainExponent a) {F G : BooleanFace V}
    (hF : F ∈ a.support) (hG : G ∈ a.support) (hc : (BooleanFace.color F) = G.color) : F = G := by
  apply Subtype.ext
  have he := BooleanFace.card_eq_of_color_eq hc
  rcases ha F hF G hG with hFG | hGF
  · exact eq_of_subset_of_card_le hFG he.ge
  · exact (eq_of_subset_of_card_le hGF he.le).symm

/-- The usual Stanley--Reisner ring of the Boolean order complex. -/
abbrev BooleanBarycentricRing (V K : Type*) [Fintype V] [DecidableEq V] [CommRing K] :=
  MonomialQuotient (K := K) (IsChainExponent (V := V))

/-- Its genuine chain-monomial coefficient basis. -/
def booleanChainBasis :
    Module.Basis {a : BooleanFace V →₀ ℕ // IsChainExponent a} K
      (BooleanBarycentricRing V K) :=
  standardMonomialBasis IsChainExponent isChainExponent_divisorClosed

def faceVariable (F : BooleanFace V) : BooleanBarycentricRing V K :=
  Ideal.Quotient.mk (forbiddenIdeal (K := K) IsChainExponent) (MvPolynomial.X F)

theorem chainMonomial_eq_zero {a : BooleanFace V →₀ ℕ} (ha : ¬ IsChainExponent a) :
    Ideal.Quotient.mk (forbiddenIdeal (K := K) IsChainExponent)
      (MvPolynomial.monomial a 1) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span ⟨a, ha, rfl⟩

theorem faceVariable_mul_eq_zero {F G : BooleanFace V}
    (h : ¬ (F.val ⊆ G.val ∨ G.val ⊆ F.val)) :
    faceVariable (K := K) F * faceVariable G = 0 := by
  have hne : F ≠ G := by
    intro he
    subst G
    exact h (Or.inl Subset.rfl)
  have hn : ¬ IsChainExponent (Finsupp.single F 1 + Finsupp.single G 1) := by
    intro hc
    apply h
    apply hc F _ G _ <;>
      simp [Finsupp.mem_support_iff, hne, Ne.symm hne]
  simpa only [faceVariable, ← map_mul, MvPolynomial.X,
    MvPolynomial.monomial_mul, one_mul] using (chainMonomial_eq_zero (K := K) hn)

theorem sameColor_faceVariable_mul_eq_zero {F G : BooleanFace V}
    (hcolor : (BooleanFace.color F) = G.color) (hne : F ≠ G) :
    faceVariable (K := K) F * faceVariable G = 0 := by
  apply faceVariable_mul_eq_zero
  intro h
  apply hne
  apply Subtype.ext
  have he := BooleanFace.card_eq_of_color_eq hcolor
  rcases h with hFG | hGF
  · exact eq_of_subset_of_card_le hFG he.ge
  · exact (eq_of_subset_of_card_le hGF he.le).symm

def facesOfColor (c : Fin (Fintype.card V)) : Finset (BooleanFace V) :=
  Finset.univ.filter (fun F => (BooleanFace.color F) = c)

@[simp] theorem mem_facesOfColor (c : Fin (Fintype.card V)) (F : BooleanFace V) :
    F ∈ facesOfColor c ↔ (BooleanFace.color F) = c := by
  simp [facesOfColor]

/-- The paper's rank color sum, with `c` representing rank `c+1`. -/
def colorSum (c : Fin (Fintype.card V)) : BooleanBarycentricRing V K :=
  ∑ F ∈ facesOfColor c, faceVariable F

theorem colorSum_mul_faceVariable (F : BooleanFace V) :
    colorSum (K := K) (BooleanFace.color F) * faceVariable F = faceVariable F ^ 2 := by
  rw [colorSum, sum_mul]
  rw [Finset.sum_eq_single F]
  · exact (pow_two _).symm
  · intro G hG hGF
    apply sameColor_faceVariable_mul_eq_zero
    · exact (mem_facesOfColor _ _).mp hG
    · exact hGF
  · intro hF
    exact (hF ((mem_facesOfColor _ _).mpr rfl)).elim

/-- The unique face of a given color in a chain absorbs every further
factor of that color sum. This is integral and involves no division. -/
theorem colorSum_pow_mul_faceVariable (F : BooleanFace V) (m : ℕ) :
    colorSum (K := K) (BooleanFace.color F) ^ m * faceVariable F = faceVariable F ^ (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc
      colorSum (BooleanFace.color F) ^ (m + 1) * faceVariable F =
          colorSum (BooleanFace.color F) ^ m * (colorSum (BooleanFace.color F) * faceVariable F) := by
            rw [pow_succ, mul_assoc]
      _ = colorSum (BooleanFace.color F) ^ m * (faceVariable F * faceVariable F) := by
            rw [colorSum_mul_faceVariable, pow_two]
      _ = faceVariable F ^ (m + 1) * faceVariable F := by rw [← mul_assoc, ih]
      _ = faceVariable F ^ (m + 1 + 1) := (pow_succ _ _).symm

/-- Powers of one color sum have coefficient one on every allowed pure
power. Mixed same-color products vanish in the actual quotient. -/
theorem colorSum_pow_succ (c : Fin (Fintype.card V)) (m : ℕ) :
    colorSum (K := K) c ^ (m + 1) =
      ∑ F ∈ facesOfColor c, faceVariable F ^ (m + 1) := by
  rw [pow_succ]
  conv_lhs => rhs; unfold colorSum
  rw [mul_sum]
  apply Finset.sum_congr rfl
  intro F hF
  have hc := (mem_facesOfColor _ _).mp hF
  rw [← hc]
  exact colorSum_pow_mul_faceVariable F m

section Flags

variable [LinearOrder V]

def orderingFace (σ : VertexOrdering (Fintype.card V) V)
    (c : Fin (Fintype.card V)) : BooleanFace V :=
  ⟨orderingPrefix σ c, orderingPrefix_nonempty σ c⟩

@[simp] theorem orderingFace_color (σ : VertexOrdering (Fintype.card V) V)
    (c : Fin (Fintype.card V)) : (orderingFace σ c).color = c := by
  apply Fin.ext
  simp [BooleanFace.color, orderingFace]

theorem orderingFace_injective (σ : VertexOrdering (Fintype.card V) V) :
    Function.Injective (orderingFace σ) := by
  intro i j hij
  simpa using congrArg BooleanFace.color hij

def chainFaceSet (a : BooleanFace V →₀ ℕ) : Finset (Finset V) :=
  a.support.image Subtype.val

theorem chainFaceSet_chain {a : BooleanFace V →₀ ℕ} (ha : IsChainExponent a) :
    ∀ F ∈ chainFaceSet a, ∀ G ∈ chainFaceSet a, F ⊆ G ∨ G ⊆ F := by
  intro F hF G hG
  obtain ⟨F', hF', rfl⟩ := Finset.mem_image.mp hF
  obtain ⟨G', hG', rfl⟩ := Finset.mem_image.mp hG
  exact ha F' hF' G' hG'

/-- The increasing-block refinement of a chain. -/
def chainOrdering (a : BooleanFace V →₀ ℕ) : VertexOrdering (Fintype.card V) V :=
  weightOrdering (flagScore (chainFaceSet a))

theorem chainOrdering_prefix {a : BooleanFace V →₀ ℕ} (ha : IsChainExponent a)
    {F : BooleanFace V} (hF : F ∈ a.support) :
    orderingPrefix (chainOrdering a) (BooleanFace.color F) = F.val := by
  apply orderingPrefix_eq_of_weight_separation (flagScore (chainFaceSet a))
    (chainOrdering a) (weightOrdering_antitone _) F.val (BooleanFace.color F)
  · exact F.color_succ.symm
  · intro x hx y hy
    exact flagScore_lt_of_mem_notMem (chainFaceSet_chain ha)
      (Finset.mem_image.mpr ⟨F, hF, rfl⟩) hx hy

theorem chainOrdering_face {a : BooleanFace V →₀ ℕ} (ha : IsChainExponent a)
    {F : BooleanFace V} (hF : F ∈ a.support) :
    orderingFace (chainOrdering a) (BooleanFace.color F) = F :=
  Subtype.ext (chainOrdering_prefix ha hF)

def chainColorDegree (a : BooleanFace V →₀ ℕ) : Fin (Fintype.card V) →₀ ℕ :=
  Finsupp.mapDomain BooleanFace.color a

theorem chainColorDegree_apply {a : BooleanFace V →₀ ℕ} (ha : IsChainExponent a)
    {F : BooleanFace V} (hF : F ∈ a.support) : chainColorDegree a (BooleanFace.color F) = a F := by
  apply Finsupp.mapDomain_apply' (a.support : Set (BooleanFace V)) a (Set.Subset.refl _)
  · intro F hF G hG hc
    exact eq_of_chain_of_color_eq ha hF hG hc
  · exact hF

theorem chainColorDegree_support {a : BooleanFace V →₀ ℕ} (ha : IsChainExponent a) :
    (chainColorDegree a).support = a.support.image BooleanFace.color := by
  apply Finsupp.mapDomain_support_of_injOn
  intro F hF G hG hc
  exact eq_of_chain_of_color_eq ha hF hG hc

theorem chainOrdering_descents {a : BooleanFace V →₀ ℕ} (ha : IsChainExponent a) :
    orderingDescents (chainOrdering a) ⊆ (chainColorDegree a).support := by
  intro c hc
  obtain ⟨hn, hw⟩ := weightOrdering_descent_lt (flagScore (chainFaceSet a))
    ((mem_orderingDescents _ _).mp hc)
  obtain ⟨G, hG, hx, hy⟩ := exists_mem_notMem_of_flagScore_lt hw
  obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hG
  have hpc := chainOrdering_prefix ha hF
  have hleft : c ≤ (BooleanFace.color F) := by
    have hm : chainOrdering a c ∈ orderingPrefix (chainOrdering a) (BooleanFace.color F) := by
      rw [hpc]
      exact hx
    simpa only [mem_orderingPrefix, Equiv.symm_apply_apply] using hm
  have hright : ¬ (⟨c.val + 1, hn⟩ : Fin (Fintype.card V)) ≤ (BooleanFace.color F) := by
    intro h
    apply hy
    rw [← hpc]
    simpa only [mem_orderingPrefix, chainOrdering, Equiv.symm_apply_apply] using h
  have hcol : (BooleanFace.color F) = c := by
    apply Fin.ext
    change (BooleanFace.color F).val = c.val
    change c.val ≤ (BooleanFace.color F).val at hleft
    change ¬ c.val + 1 ≤ (BooleanFace.color F).val at hright
    omega
  rw [chainColorDegree_support ha]
  exact Finset.mem_image.mpr ⟨F, hF, hcol⟩

/-- Put the prescribed multiplicity at each prefix of a full flag. -/
def prefixExponent (σ : VertexOrdering (Fintype.card V) V)
    (m : Fin (Fintype.card V) →₀ ℕ) : BooleanFace V →₀ ℕ :=
  Finsupp.mapDomain (orderingFace σ) m

@[simp] theorem prefixExponent_support (σ : VertexOrdering (Fintype.card V) V)
    (m : Fin (Fintype.card V) →₀ ℕ) :
    (prefixExponent σ m).support = m.support.image (orderingFace σ) :=
  Finsupp.mapDomain_support_of_injective (orderingFace_injective σ) m

theorem prefixExponent_isChain (σ : VertexOrdering (Fintype.card V) V)
    (m : Fin (Fintype.card V) →₀ ℕ) : IsChainExponent (prefixExponent σ m) := by
  intro F hF G hG
  rw [prefixExponent_support] at hF hG
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hF
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hG
  rcases le_total i j with hij | hji
  · exact Or.inl (orderingPrefix_mono σ hij)
  · exact Or.inr (orderingPrefix_mono σ hji)

@[simp] theorem chainColorDegree_prefixExponent
    (σ : VertexOrdering (Fintype.card V) V) (m : Fin (Fintype.card V) →₀ ℕ) :
    chainColorDegree (prefixExponent σ m) = m := by
  rw [chainColorDegree, prefixExponent, ← Finsupp.mapDomain_fun_comp]
  simp only [orderingFace_color, Finsupp.mapDomain_fun_id]

theorem prefixExponent_chainColorDegree {a : BooleanFace V →₀ ℕ}
    (ha : IsChainExponent a) :
    prefixExponent (chainOrdering a) (chainColorDegree a) = a := by
  rw [prefixExponent, chainColorDegree, ← Finsupp.mapDomain_fun_comp]
  calc
    Finsupp.mapDomain (fun F => orderingFace (chainOrdering a) (BooleanFace.color F)) a =
        Finsupp.mapDomain id a := by
          apply Finsupp.mapDomain_congr
          intro F hF
          exact chainOrdering_face ha hF
    _ = a := Finsupp.mapDomain_id

theorem chainOrdering_prefixExponent
    (σ : VertexOrdering (Fintype.card V) V) (m : Fin (Fintype.card V) →₀ ℕ)
    (hdesc : orderingDescents σ ⊆ m.support) :
    chainOrdering (prefixExponent σ m) = σ := by
  let a := prefixExponent σ m
  have ha : IsChainExponent a := prefixExponent_isChain σ m
  have hp : ∀ c ∈ m.support,
      orderingPrefix (chainOrdering a) c = orderingPrefix σ c := by
    intro c hc
    have hF : orderingFace σ c ∈ a.support := by
      rw [prefixExponent_support]
      exact Finset.mem_image.mpr ⟨c, hc, rfl⟩
    have h := chainOrdering_prefix ha hF
    change orderingPrefix (chainOrdering a) (BooleanFace.color (orderingFace σ c)) =
      (orderingFace σ c).val at h
    rw [orderingFace_color] at h
    change orderingPrefix (chainOrdering a) c = orderingPrefix σ c at h
    exact h
  apply ordering_eq_of_descent_prefixes
  · intro c hc
    apply (hp c _).symm
    have hm := chainOrdering_descents ha ((mem_orderingDescents _ _).mpr hc)
    simpa only [a, chainColorDegree_prefixExponent] using hm
  · intro c hc
    exact hp c (hdesc ((mem_orderingDescents _ _).mpr hc))

/-- The full flag decomposition of every standard monomial, including all
multiplicities and the exact descent restriction. -/
def chainFlagEquiv :
    {a : BooleanFace V →₀ ℕ // IsChainExponent a} ≃
      {p : VertexOrdering (Fintype.card V) V × (Fin (Fintype.card V) →₀ ℕ) //
        orderingDescents p.1 ⊆ p.2.support} where
  toFun a := ⟨(chainOrdering a.val, chainColorDegree a.val), chainOrdering_descents a.property⟩
  invFun p := ⟨prefixExponent p.val.1 p.val.2, prefixExponent_isChain _ _⟩
  left_inv a := Subtype.ext (prefixExponent_chainColorDegree a.property)
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact chainOrdering_prefixExponent _ _ p.property
    · exact chainColorDegree_prefixExponent _ _

end Flags

end FourPapers.Universal
end
end

/- BEGIN FaceBooleanInterval.lean -/
section


/-! # The canonical Boolean chart on the actual vertices of a face -/

noncomputable section

set_option autoImplicit false

namespace FourPapers.Universal

open Classical Finset

variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]

/-- Extending the actual local vertex subset recovers precisely the global
canonical vertex set, when the face lies below the ambient face. -/
theorem image_stalkVertexSet {p q : P} (hqp : q ≤ p) :
    (stalkVertexSet p q).image Subtype.val = faceVertices q := by
  ext a
  simp only [Finset.mem_image, mem_stalkVertexSet, mem_faceVertices]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v.property.1, hv⟩
  · rintro ⟨ha, haq⟩
    exact ⟨⟨a, ha, haq.trans hqp⟩, haq, rfl⟩

theorem stalkVertexSet_subset_iff (hs : IsSimplicialPoset P) {p q r : P}
    (hqp : q ≤ p) (hrp : r ≤ p) :
    stalkVertexSet p q ⊆ stalkVertexSet p r ↔ q ≤ r := by
  constructor
  · intro h
    apply (faceVertices_subset_iff hs hqp hrp).mp
    rw [← image_stalkVertexSet hqp, ← image_stalkVertexSet hrp]
    exact Finset.image_subset_image h
  · intro h a ha
    exact (mem_stalkVertexSet p r a).mpr (((mem_stalkVertexSet p q a).mp ha).trans h)

def subfaceOfVertexSet (hs : IsSimplicialPoset P) (p : P)
    (s : Finset (FaceVertex p)) : Set.Iic p :=
  (existsUnique_subface hs p (s.image Subtype.val) (by
    intro a ha
    obtain ⟨v, hv, rfl⟩ := mem_image.mp ha
    exact mem_faceVertices.mpr v.property)).choose

theorem subfaceOfVertexSet_vertices (hs : IsSimplicialPoset P) (p : P)
    (s : Finset (FaceVertex p)) :
    faceVertices (subfaceOfVertexSet hs p s).val = s.image Subtype.val :=
  (existsUnique_subface hs p (s.image Subtype.val) (by
    intro a ha
    obtain ⟨v, hv, rfl⟩ := mem_image.mp ha
    exact mem_faceVertices.mpr v.property)).choose_spec.1

theorem stalkVertexSet_subfaceOfVertexSet (hs : IsSimplicialPoset P) (p : P)
    (s : Finset (FaceVertex p)) :
    stalkVertexSet p (subfaceOfVertexSet hs p s).val = s := by
  have h := (image_stalkVertexSet (subfaceOfVertexSet hs p s).property).trans
    (subfaceOfVertexSet_vertices hs p s)
  exact Finset.image_injective Subtype.val_injective h

def faceBooleanInterval (hs : IsSimplicialPoset P) (p : P) :
    Set.Iic p ≃o Finset (FaceVertex p) where
  toFun q := stalkVertexSet p q.val
  invFun := subfaceOfVertexSet hs p
  left_inv q := by
    apply Subtype.ext
    apply faceVertices_injective_below hs (subfaceOfVertexSet hs p _).property q.property
    rw [subfaceOfVertexSet_vertices, image_stalkVertexSet q.property]
  right_inv := stalkVertexSet_subfaceOfVertexSet hs p
  map_rel_iff' := by
    intro q r
    exact stalkVertexSet_subset_iff hs q.property r.property

/-- Nonempty Boolean faces embed as actual nonzero subfaces of the original
poset. The embedding is confined to this Boolean interval. -/
def booleanFaceInclusion (hs : IsSimplicialPoset P) (p : P) :
    BooleanFace (FaceVertex p) ↪ NonzeroFace P where
  toFun F := ⟨(subfaceOfVertexSet hs p F.val).val, by
    intro hbot
    have he := stalkVertexSet_subfaceOfVertexSet hs p F.val
    rw [hbot, stalkVertexSet_bot] at he
    exact F.property.ne_empty he.symm⟩
  inj' F G h := by
    apply Subtype.ext
    have he : (subfaceOfVertexSet hs p F.val).val =
        (subfaceOfVertexSet hs p G.val).val := congrArg (fun z : NonzeroFace P => z.val) h
    have hv := congrArg (stalkVertexSet p) he
    simpa only [stalkVertexSet_subfaceOfVertexSet] using hv
theorem booleanFaceInclusion_palomar_formula (hs : IsSimplicialPoset P) (p : P) (F : BooleanFace (FaceVertex p)) :
    (booleanFaceInclusion hs p F).val = (subfaceOfVertexSet hs p F.val).val := rfl

theorem booleanFaceInclusion_le (hs : IsSimplicialPoset P) (p : P)
    (F : BooleanFace (FaceVertex p)) : (booleanFaceInclusion hs p F).val ≤ p :=
  (subfaceOfVertexSet hs p F.val).property

@[simp] theorem stalkVertexSet_booleanFaceInclusion (hs : IsSimplicialPoset P)
    (p : P) (F : BooleanFace (FaceVertex p)) :
    stalkVertexSet p (booleanFaceInclusion hs p F).val = F.val :=
  stalkVertexSet_subfaceOfVertexSet hs p F.val

theorem booleanFaceInclusion_le_iff (hs : IsSimplicialPoset P) (p : P)
    (F G : BooleanFace (FaceVertex p)) :
    (booleanFaceInclusion hs p F).val ≤ (booleanFaceInclusion hs p G).val ↔ F.val ⊆ G.val := by
  rw [← stalkVertexSet_subset_iff hs (booleanFaceInclusion_le hs p F)
    (booleanFaceInclusion_le hs p G)]
  simp only [stalkVertexSet_booleanFaceInclusion]

end FourPapers.Universal
end
end

/- BEGIN BarycentricPresentation.lean -/
section


/-! # Chain monomials in the actual barycentric face ring -/

noncomputable section

set_option autoImplicit false

namespace FourPapers.Universal

open Classical MvPolynomial Finset

variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]
variable (K : Type*) [CommRing K]

/-- Exponents whose positive support is a chain of nonzero faces. -/
def BarycentricAllowed (a : NonzeroFace P →₀ ℕ) : Prop :=
  ∀ p ∈ a.support, ∀ q ∈ a.support, p.val ≤ q.val ∨ q.val ≤ p.val

theorem barycentricAllowed_divisorClosed :
    IsDivisorClosed (BarycentricAllowed (P := P)) := by
  intro a b hab hb p hp q hq
  exact hb p (Finsupp.support_mono hab hp) q (Finsupp.support_mono hab hq)

theorem incomparable_pair_forbidden (p q : NonzeroFace P)
    (hpq : ¬ p.val ≤ q.val) (hqp : ¬ q.val ≤ p.val) :
    ¬ BarycentricAllowed (Finsupp.single p 1 + Finsupp.single q 1) := by
  have hne : p ≠ q := by rintro rfl; exact hpq le_rfl
  intro h
  have hp : p ∈ (Finsupp.single p 1 + Finsupp.single q 1).support := by
    simp [Finsupp.mem_support_iff, Finsupp.single_apply, hne, Ne.symm hne]
  have hq : q ∈ (Finsupp.single p 1 + Finsupp.single q 1).support := by
    simp [Finsupp.mem_support_iff, Finsupp.single_apply, hne, Ne.symm hne]
  exact (h p hp q hq).elim hpq hqp

theorem incomparable_pair_le {a : NonzeroFace P →₀ ℕ} (p q : NonzeroFace P)
    (hp : p ∈ a.support) (hq : q ∈ a.support) (hpq : p ≠ q) :
    Finsupp.single p 1 + Finsupp.single q 1 ≤ a := by
  intro v
  by_cases hvp : v = p
  · subst v
    simpa [Finsupp.single_apply, hpq, Ne.symm hpq] using
      Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hp)
  · by_cases hvq : v = q
    · subst v
      simpa [Finsupp.single_apply, hpq, Ne.symm hpq] using
        Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hq)
    · simp [Finsupp.single_apply, hvp, hvq, Ne.symm hvp, Ne.symm hvq]

/-- The ordinary incomparable-pair presentation is exactly the forbidden-
monomial ideal. Thus the quotient basis is a theorem about the original ring. -/
theorem barycentricIdeal_eq_forbiddenIdeal :
    barycentricIdeal (P := P) K =
      forbiddenIdeal (K := K) (BarycentricAllowed (P := P)) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro f ⟨p, q, hpq, hqp, rfl⟩
    apply Ideal.subset_span
    refine ⟨Finsupp.single p 1 + Finsupp.single q 1,
      incomparable_pair_forbidden p q hpq hqp, ?_⟩
    simp [MvPolynomial.X, MvPolynomial.monomial_mul]
  · apply Ideal.span_le.mpr
    rintro f ⟨a, ha, rfl⟩
    unfold BarycentricAllowed at ha
    push Not at ha
    obtain ⟨p, hp, q, hq, hpq, hqp⟩ := ha
    have hne : p ≠ q := by rintro rfl; exact hpq le_rfl
    have hle := incomparable_pair_le p q hp hq hne
    obtain ⟨c, hc⟩ := exists_add_of_le hle
    have hpair : (X p * X q : FacePolynomial (P := P) K) ∈ barycentricIdeal K :=
      Ideal.subset_span ⟨p, q, hpq, hqp, rfl⟩
    have hm : (MvPolynomial.monomial a (1 : K)) =
        (X p * X q) * MvPolynomial.monomial c 1 := by
      rw [hc]
      simp [MvPolynomial.X, MvPolynomial.monomial_mul, add_assoc]
    change MvPolynomial.monomial a (1 : K) ∈ barycentricIdeal K
    rw [hm]
    exact Ideal.mul_mem_right _ _ hpair

end FourPapers.Universal

end
end

/- BEGIN StandardCarriers.lean -/
section


/-! # The smallest supporting face of an actual standard face monomial

The carrier is a face of the original poset, not merely its vertex set. Thus
repeated vertex sets on different faces are distinguished throughout.
-/

noncomputable section

set_option autoImplicit false

namespace FourPapers.Universal

open Classical Finset

variable {P : Type*} [PartialOrder P] [OrderBot P] [Fintype P]

abbrev StandardFaceIndex (P : Type*) [PartialOrder P] [OrderBot P] :=
  {a : NonzeroFace P →₀ ℕ // BarycentricAllowed a}

/-- Choose the largest-rank face in the chain, or the bottom face for the
empty chain. The following theorem characterizes this choice intrinsically. -/
def standardCarrier (a : StandardFaceIndex P) : P :=
  if h : a.val.support.Nonempty then
    (Finset.exists_max_image a.val.support (fun p : NonzeroFace P => faceRank p.val) h).choose.val
  else ⊥

theorem standardCarrier_le_iff (hs : IsSimplicialPoset P)
    (a : StandardFaceIndex P) (p : P) :
    standardCarrier a ≤ p ↔ ∀ q ∈ a.val.support, q.val ≤ p := by
  by_cases h : a.val.support.Nonempty
  · let q := (Finset.exists_max_image a.val.support
      (fun q : NonzeroFace P => faceRank q.val) h).choose
    have hq : q ∈ a.val.support :=
      (Finset.exists_max_image a.val.support
        (fun q : NonzeroFace P => faceRank q.val) h).choose_spec.1
    have hmax : ∀ r ∈ a.val.support, faceRank r.val ≤ faceRank q.val :=
      (Finset.exists_max_image a.val.support
        (fun q : NonzeroFace P => faceRank q.val) h).choose_spec.2
    have hrq : ∀ r ∈ a.val.support, r.val ≤ q.val := by
      intro r hr
      rcases a.property r hr q hq with hle | hge
      · exact hle
      · by_contra hn
        have hlt : q.val < r.val := lt_of_le_of_ne hge (Ne.symm (ne_of_not_le hn))
        exact (not_lt_of_ge (hmax r hr)) (faceRank_strictMono hs hlt)
    simp only [standardCarrier, dif_pos h]
    constructor
    · intro hqp r hr
      exact (hrq r hr).trans hqp
    · intro hall
      exact hall q hq
  · have he : a.val.support = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [standardCarrier, h, he]

theorem standardCarrier_mem_or_bot (a : StandardFaceIndex P) :
    standardCarrier a = ⊥ ∨ ∃ q ∈ a.val.support, standardCarrier a = q.val := by
  by_cases h : a.val.support.Nonempty
  · right
    let q := (Finset.exists_max_image a.val.support
      (fun q : NonzeroFace P => faceRank q.val) h).choose
    exact ⟨q, (Finset.exists_max_image a.val.support
      (fun q : NonzeroFace P => faceRank q.val) h).choose_spec.1,
      by simp [standardCarrier, h, q]⟩
  · exact Or.inl (by simp [standardCarrier, h])

theorem booleanFaceInclusion_range_iff (hs : IsSimplicialPoset P)
    (p : P) (q : NonzeroFace P) :
    q ∈ Set.range (booleanFaceInclusion hs p) ↔ q.val ≤ p := by
  constructor
  · rintro ⟨F, rfl⟩
    exact booleanFaceInclusion_le hs p F
  · intro hqp
    have hn : (stalkVertexSet p q.val).Nonempty := by
      obtain ⟨v, hv⟩ := faceVertices_nonempty hs q.property
      obtain ⟨ha, haq⟩ := mem_faceVertices.mp hv
      exact ⟨⟨v, ha, haq.trans hqp⟩, (mem_stalkVertexSet p q.val ⟨v, ha, haq.trans hqp⟩).mpr haq⟩
    refine ⟨⟨stalkVertexSet p q.val, hn⟩, ?_⟩
    apply Subtype.ext
    apply faceVertices_injective_below hs
      (booleanFaceInclusion_le hs p _) hqp
    rw [← image_stalkVertexSet (booleanFaceInclusion_le hs p _),
      stalkVertexSet_booleanFaceInclusion, image_stalkVertexSet hqp]

theorem standardExponent_map_booleanFaceInclusion (hs : IsSimplicialPoset P)
    (p : P) {a : BooleanFace (FaceVertex p) →₀ ℕ} (ha : IsChainExponent a) :
    BarycentricAllowed (a.mapDomain (booleanFaceInclusion hs p)) := by
  intro q hq r hr
  rw [Finsupp.mapDomain_support_of_injective (booleanFaceInclusion hs p).injective] at hq hr
  obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp hr
  rcases ha F hF G hG with hFG | hGF
  · exact Or.inl ((booleanFaceInclusion_le_iff hs p F G).mpr hFG)
  · exact Or.inr ((booleanFaceInclusion_le_iff hs p G F).mpr hGF)

theorem chainExponent_comap_booleanFaceInclusion (hs : IsSimplicialPoset P)
    (p : P) {a : NonzeroFace P →₀ ℕ} (ha : BarycentricAllowed a) :
    IsChainExponent (a.comapDomain (booleanFaceInclusion hs p)
      (booleanFaceInclusion hs p).injective.injOn) := by
  intro F hF G hG
  have hFa : booleanFaceInclusion hs p F ∈ a.support := by
    simpa only [Finsupp.mem_support_iff, Finsupp.comapDomain_apply] using hF
  have hGa : booleanFaceInclusion hs p G ∈ a.support := by
    simpa only [Finsupp.mem_support_iff, Finsupp.comapDomain_apply] using hG
  rcases ha _ hFa _ hGa with hFG | hGF
  · exact Or.inl ((booleanFaceInclusion_le_iff hs p F G).mp hFG)
  · exact Or.inr ((booleanFaceInclusion_le_iff hs p G F).mp hGF)

abbrev StandardInside (p : P) := {a : StandardFaceIndex P // standardCarrier a ≤ p}

/-- This is an exact equivalence of exponent indices, derived from the
canonical Boolean interval. No global Boolean-lattice embedding is assumed. -/
def standardInsideEquiv (hs : IsSimplicialPoset P) (p : P) :
    {a : BooleanFace (FaceVertex p) →₀ ℕ // IsChainExponent a} ≃ StandardInside p where
  toFun a := ⟨⟨a.val.mapDomain (booleanFaceInclusion hs p),
    standardExponent_map_booleanFaceInclusion hs p a.property⟩, by
      apply (standardCarrier_le_iff hs _ p).mpr
      intro q hq
      rw [Finsupp.mapDomain_support_of_injective (booleanFaceInclusion hs p).injective] at hq
      obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hq
      exact booleanFaceInclusion_le hs p F⟩
  invFun a := ⟨a.val.val.comapDomain (booleanFaceInclusion hs p)
    (booleanFaceInclusion hs p).injective.injOn,
    chainExponent_comap_booleanFaceInclusion hs p a.val.property⟩
  left_inv a := Subtype.ext
    (Finsupp.comapDomain_mapDomain _ (booleanFaceInclusion hs p).injective a.val)
  right_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    apply Finsupp.mapDomain_comapDomain _ (booleanFaceInclusion hs p).injective
    intro q hq
    exact (booleanFaceInclusion_range_iff hs p q).mpr
      ((standardCarrier_le_iff hs a.val p).mp a.property q hq)

end FourPapers.Universal
end
end

/- BEGIN MonomialRestriction.lean -/
section


/-!
# Genuine face restrictions on monomial quotient rings

An embedding of variable sets gives a restriction homomorphism by killing its
complement. The compatibility hypothesis concerns only the two specified sets
of allowed exponents; no quotient is identified with a formal surrogate.
-/

noncomputable section

set_option autoImplicit false

namespace FourPapers.Universal

variable {V W K : Type*} [CommRing K]

theorem killCompl_mem_forbiddenIdeal
    (e : V ↪ W) (P : (W →₀ ℕ) → Prop) (Q : (V →₀ ℕ) → Prop)
    (hP : IsDivisorClosed P) (hQ : IsDivisorClosed Q)
    (allowed : ∀ a, Q a → P (a.mapDomain e))
    {f : MvPolynomial W K} (hf : f ∈ forbiddenIdeal P) :
    MvPolynomial.killCompl e.injective f ∈ forbiddenIdeal Q := by
  rw [mem_forbiddenIdeal Q hQ]
  intro a ha
  rw [MvPolynomial.coeff_killCompl]
  exact (mem_forbiddenIdeal P hP f).mp hf (a.mapDomain e) (allowed a ha)

/-- Restriction between the actual quotient algebras. -/
def monomialRestriction
    (e : V ↪ W) (P : (W →₀ ℕ) → Prop) (Q : (V →₀ ℕ) → Prop)
    (hP : IsDivisorClosed P) (hQ : IsDivisorClosed Q)
    (allowed : ∀ a, Q a → P (a.mapDomain e)) :
    MonomialQuotient (K := K) P →ₐ[K] MonomialQuotient (K := K) Q :=
  Ideal.Quotient.liftₐ (forbiddenIdeal P)
    ((Ideal.Quotient.mkₐ K (forbiddenIdeal Q)).comp
      (MvPolynomial.killCompl e.injective)) (by
        intro f hf
        change Ideal.Quotient.mk (forbiddenIdeal Q)
          (MvPolynomial.killCompl e.injective f) = 0
        exact Ideal.Quotient.eq_zero_iff_mem.mpr
          (killCompl_mem_forbiddenIdeal e P Q hP hQ allowed hf))

@[simp] theorem monomialRestriction_mk
    (e : V ↪ W) (P : (W →₀ ℕ) → Prop) (Q : (V →₀ ℕ) → Prop)
    (hP : IsDivisorClosed P) (hQ : IsDivisorClosed Q)
    (allowed : ∀ a, Q a → P (a.mapDomain e)) (f : MvPolynomial W K) :
    monomialRestriction e P Q hP hQ allowed (Ideal.Quotient.mk (forbiddenIdeal P) f) =
      Ideal.Quotient.mk (forbiddenIdeal Q) (MvPolynomial.killCompl e.injective f) := rfl

/-- Coefficients restrict exactly by extending exponent vectors by zero. -/
theorem monomialRestriction_coefficient
    (e : V ↪ W) (P : (W →₀ ℕ) → Prop) (Q : (V →₀ ℕ) → Prop)
    (hP : IsDivisorClosed P) (hQ : IsDivisorClosed Q)
    (allowed : ∀ a, Q a → P (a.mapDomain e))
    (x : MonomialQuotient (K := K) P) (a : {a // Q a}) :
    standardMonomialEquiv Q hQ (monomialRestriction e P Q hP hQ allowed x) a =
      standardMonomialEquiv P hP x ⟨a.val.mapDomain e, allowed a.val a.property⟩ := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [monomialRestriction_mk, standardMonomialEquiv_mk,
    standardCoefficients_apply, MvPolynomial.coeff_killCompl]

end FourPapers.Universal
end
end

/- BEGIN BooleanRestrictions.lean -/
section


/-! # Actual restrictions between Boolean barycentric face rings

An embedding of vertex sets induces the embedding of their nonempty faces.
Restriction kills every face not contained in the smaller vertex set.
-/

set_option autoImplicit false

noncomputable section

namespace FourPapers.Universal

open Classical Finset

variable {U V W K : Type*}
  [Fintype U] [Fintype V] [Fintype W]
  [DecidableEq U] [DecidableEq V] [DecidableEq W] [CommRing K]

def booleanFaceEmbedding (e : V ↪ W) : BooleanFace V ↪ BooleanFace W where
  toFun F := ⟨F.val.map e, F.property.map (f := e)⟩
  inj' F G h := Subtype.ext (Finset.map_injective e (congrArg Subtype.val h))

@[simp] theorem booleanFaceEmbedding_val (e : V ↪ W) (F : BooleanFace V) :
    (booleanFaceEmbedding e F).val = F.val.map e := rfl

@[simp] theorem booleanFaceEmbedding_card (e : V ↪ W) (F : BooleanFace V) :
    (booleanFaceEmbedding e F).val.card = F.val.card := Finset.card_map _

@[simp] theorem booleanFaceEmbedding_refl (F : BooleanFace V) :
    booleanFaceEmbedding (Function.Embedding.refl V) F = F := by
  apply Subtype.ext
  simp [booleanFaceEmbedding]

@[simp] theorem booleanFaceEmbedding_trans (e : U ↪ V) (f : V ↪ W)
    (F : BooleanFace U) :
    booleanFaceEmbedding f (booleanFaceEmbedding e F) =
      booleanFaceEmbedding (e.trans f) F := by
  apply Subtype.ext
  exact Finset.map_map e f F.val

theorem isChainExponent_map_booleanFaceEmbedding (e : V ↪ W)
    {a : BooleanFace V →₀ ℕ} (ha : IsChainExponent a) :
    IsChainExponent (a.mapDomain (booleanFaceEmbedding e)) := by
  intro F hF G hG
  rw [Finsupp.mapDomain_support_of_injective (booleanFaceEmbedding e).injective] at hF hG
  obtain ⟨F', hF', rfl⟩ := Finset.mem_image.mp hF
  obtain ⟨G', hG', rfl⟩ := Finset.mem_image.mp hG
  rcases ha F' hF' G' hG' with hFG | hGF
  · exact Or.inl (Finset.map_subset_map.mpr hFG)
  · exact Or.inr (Finset.map_subset_map.mpr hGF)

def booleanRestriction (e : V ↪ W) :
    BooleanBarycentricRing W K →ₐ[K] BooleanBarycentricRing V K :=
  monomialRestriction (booleanFaceEmbedding e) IsChainExponent IsChainExponent
    isChainExponent_divisorClosed isChainExponent_divisorClosed
    (fun _ ha => isChainExponent_map_booleanFaceEmbedding e ha)

@[simp] theorem booleanRestriction_mk (e : V ↪ W)
    (f : MvPolynomial (BooleanFace W) K) :
    booleanRestriction e (Ideal.Quotient.mk (forbiddenIdeal IsChainExponent) f) =
      Ideal.Quotient.mk (forbiddenIdeal IsChainExponent)
        (MvPolynomial.killCompl (booleanFaceEmbedding e).injective f) := rfl

theorem booleanRestriction_face_included (e : V ↪ W) (F : BooleanFace V) :
    booleanRestriction e (faceVariable (K := K) (booleanFaceEmbedding e F)) =
      faceVariable F := by
  unfold faceVariable
  rw [booleanRestriction_mk]
  congr 1
  have h := DFunLike.congr_fun
    (MvPolynomial.killCompl_comp_rename (R := K) (booleanFaceEmbedding e).injective)
    (MvPolynomial.X F)
  simpa only [AlgHom.comp_apply, MvPolynomial.rename_X, AlgHom.id_apply] using h

theorem booleanRestriction_face_outside (e : V ↪ W) (F : BooleanFace W)
    (hF : F ∉ Set.range (booleanFaceEmbedding e)) :
    booleanRestriction e (faceVariable (K := K) F) = 0 := by
  unfold faceVariable
  rw [booleanRestriction_mk]
  have h : MvPolynomial.killCompl (R := K) (booleanFaceEmbedding e).injective
      (MvPolynomial.X F) = 0 := by
    simp only [MvPolynomial.killCompl, MvPolynomial.aeval_X, dif_neg hF]
  rw [h, map_zero]

theorem booleanRestriction_coefficient (e : V ↪ W)
    (x : BooleanBarycentricRing W K)
    (a : {a : BooleanFace V →₀ ℕ // IsChainExponent a}) :
    (booleanChainBasis (K := K)).repr (booleanRestriction e x) a =
      (booleanChainBasis (K := K)).repr x
        ⟨a.val.mapDomain (booleanFaceEmbedding e),
          isChainExponent_map_booleanFaceEmbedding e a.property⟩ :=
  monomialRestriction_coefficient _ _ _ _ _ _ _ _

theorem booleanRestriction_refl :
    booleanRestriction (K := K) (Function.Embedding.refl V) =
      AlgHom.id K (BooleanBarycentricRing V K) := by
  apply AlgHom.ext
  intro x
  apply (booleanChainBasis (K := K)).repr.injective
  ext a
  rw [booleanRestriction_coefficient]
  congr 1
  apply Subtype.ext
  change Finsupp.mapDomain (booleanFaceEmbedding (Function.Embedding.refl V)) a.val = a.val
  have he : (booleanFaceEmbedding (Function.Embedding.refl V) : BooleanFace V → BooleanFace V) = id :=
    funext booleanFaceEmbedding_refl
  rw [he]
  exact Finsupp.mapDomain_id

theorem booleanRestriction_comp (e : U ↪ V) (f : V ↪ W) :
    (booleanRestriction (K := K) e).comp (booleanRestriction f) =
      booleanRestriction (e.trans f) := by
  apply AlgHom.ext
  intro x
  apply (booleanChainBasis (K := K)).repr.injective
  ext a
  change (booleanChainBasis (K := K)).repr
    (booleanRestriction e (booleanRestriction f x)) a = _
  rw [booleanRestriction_coefficient, booleanRestriction_coefficient,
    booleanRestriction_coefficient]
  congr 1
  apply Subtype.ext
  change Finsupp.mapDomain (booleanFaceEmbedding f)
    (Finsupp.mapDomain (booleanFaceEmbedding e) a.val) =
      Finsupp.mapDomain (booleanFaceEmbedding (e.trans f)) a.val
  rw [← Finsupp.mapDomain_fun_comp]
  apply Finsupp.mapDomain_congr
  intro F hF
  exact booleanFaceEmbedding_trans e f F

/-- Rank-indexed color sums include every rank, so they restrict without
changing the global parameter index when a face has fewer vertices. -/
def booleanRankParameter (r : ℕ) : BooleanBarycentricRing V K :=
  ∑ F : BooleanFace V, if F.val.card = r then faceVariable F else 0

theorem booleanRankParameter_color (c : Fin (Fintype.card V)) :
    booleanRankParameter (K := K) (c.val + 1) = colorSum c := by
  rw [booleanRankParameter, colorSum, facesOfColor, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro F hF
  have he : F.val.card = c.val + 1 ↔ F.color = c := by
    constructor
    · intro h
      apply Fin.ext
      have hF := F.color_succ
      omega
    · rintro rfl
      exact F.color_succ.symm
  simp only [he]

theorem booleanRankParameter_above (r : ℕ) (hr : Fintype.card V < r) :
    booleanRankParameter (V := V) (K := K) r = 0 := by
  apply Finset.sum_eq_zero
  intro F hF
  have hc : F.val.card ≤ Fintype.card V := Finset.card_le_univ F.val
  have hn : F.val.card ≠ r := by omega
  simp [hn]

theorem booleanRestriction_rankParameter (e : V ↪ W) (r : ℕ) :
    booleanRestriction (K := K) e (booleanRankParameter r) =
      booleanRankParameter r := by
  rw [booleanRankParameter, map_sum]
  calc
    (∑ F : BooleanFace W,
        booleanRestriction e (if F.val.card = r then faceVariable F else 0)) =
        ∑ G : BooleanFace V,
          booleanRestriction e
            (if (booleanFaceEmbedding e G).val.card = r then
              faceVariable (booleanFaceEmbedding e G) else 0) := by
      symm
      apply Finset.sum_bij_ne_zero (fun G _ _ => booleanFaceEmbedding e G)
      · intro G hG hG0
        exact Finset.mem_univ _
      · intro G H hG hH hG0 hH0 he
        exact (booleanFaceEmbedding e).injective he
      · intro F hF hF0
        have hmem : F ∈ Set.range (booleanFaceEmbedding e) := by
          by_contra hn
          apply hF0
          split_ifs <;> simp [booleanRestriction_face_outside e F hn]
        obtain ⟨G, rfl⟩ := hmem
        exact ⟨G, Finset.mem_univ _, hF0, rfl⟩
      · intro G hG hG0
        rfl
    _ = booleanRankParameter r := by
      unfold booleanRankParameter
      apply Finset.sum_congr rfl
      intro G hG
      rw [booleanFaceEmbedding_card]
      split_ifs <;> simp [booleanRestriction_face_included]

end FourPapers.Universal
end
end

/- BEGIN CoefficientDiagram.lean -/
section


/-!
# Coefficientwise gluing on a finite face diagram

Each basis index has a smallest supporting face. Compatible local coefficient
families then glue to one finitely supported global coefficient family. This
proves the inverse-limit step without assuming that inverse limits commute with
tensor products or that the coefficient ring is a field.
-/

noncomputable section

set_option autoImplicit false

namespace FourPapers.Universal

open Classical

variable {P I : Type*} [Preorder P]
variable (K : Type*) [CommRing K] (carrier : I → P)

def coefficientStalk (p : P) : Submodule K (I →₀ K) :=
  Finsupp.supported K K {i | carrier i ≤ p}

def coefficientRestriction {p q : P} (_hqp : q ≤ p) :
    coefficientStalk K carrier p →ₗ[K] coefficientStalk K carrier q :=
  (Finsupp.restrictDom K K {i | carrier i ≤ q}).comp
    (coefficientStalk K carrier p).subtype
theorem coefficientRestriction_palomar_formula {p q : P} (h : q ≤ p) :
    coefficientRestriction K carrier h = (Finsupp.restrictDom K K {i | carrier i ≤ q}).comp (coefficientStalk K carrier p).subtype := rfl

@[simp] theorem coefficientRestriction_apply {p q : P} (hqp : q ≤ p)
    (x : coefficientStalk K carrier p) (i : I) :
    (coefficientRestriction K carrier hqp x).val i =
      if carrier i ≤ q then x.val i else 0 := rfl

abbrev coefficientDiagram : ModuleDiagram K P where
  obj p := coefficientStalk K carrier p
  res h := coefficientRestriction K carrier h
  res_refl p x := by
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    by_cases hi : carrier i ≤ p
    · simp [hi]
    · have hx := (Finsupp.mem_supported' K x.val).mp x.property i hi
      simp [hi, hx]
  res_comp := by
    intro p q r hqp hrq x
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    by_cases hi : carrier i ≤ r
    · have hiq := hi.trans hrq
      simp [hi, hiq]
    · simp [hi]
theorem coefficientDiagram_palomar_formula {p q : P} (h : q ≤ p) :
    (coefficientDiagram K carrier).res h = coefficientRestriction K carrier h := rfl

def coefficientSection : (I →₀ K) →ₗ[K] (coefficientDiagram K carrier).sections where
  toFun x := ⟨fun p => Finsupp.restrictDom K K {i | carrier i ≤ p} x, by
    intro p q hqp
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    change (if carrier i ≤ q then (if carrier i ≤ p then x i else 0) else 0) =
      (if carrier i ≤ q then x i else 0)
    by_cases hi : carrier i ≤ q
    · have hip := hi.trans hqp
      simp [hi, hip]
    · simp [hi]⟩
  map_add' x y := by
    apply Subtype.ext
    funext p
    exact map_add (Finsupp.restrictDom K K {i | carrier i ≤ p}) x y
  map_smul' c x := by
    apply Subtype.ext
    funext p
    exact map_smul (Finsupp.restrictDom K K {i | carrier i ≤ p}) c x

@[simp] theorem coefficientSection_apply (x : I →₀ K) (p : P) (i : I) :
    ((coefficientSection K carrier x).val p).val i =
      if carrier i ≤ p then x i else 0 := rfl

def coefficientAtCarrier (x : (coefficientDiagram K carrier).sections) (i : I) : K :=
  (x.val (carrier i)).val i

theorem coefficientAtCarrier_eq (x : (coefficientDiagram K carrier).sections)
    (i : I) (p : P) (hip : carrier i ≤ p) :
    coefficientAtCarrier K carrier x i = (x.val p).val i := by
  have h := congrArg (fun z : coefficientStalk K carrier (carrier i) => z.val i)
    (x.property p (carrier i) hip)
  change (if carrier i ≤ carrier i then (x.val p).val i else 0) =
    (x.val (carrier i)).val i at h
  simpa only [if_pos le_rfl, coefficientAtCarrier] using h.symm

variable [Fintype P]

/-- Finiteness of the face poset, rather than finiteness of the monomial index
set, makes the assembled coefficient family finitely supported. -/
def coefficientAssembly (x : (coefficientDiagram K carrier).sections) : I →₀ K :=
  Finsupp.onFinset (Finset.univ.biUnion fun p => (x.val p).val.support)
    (coefficientAtCarrier K carrier x) (by
      intro i hi
      apply Finset.mem_biUnion.mpr
      exact ⟨carrier i, Finset.mem_univ _, Finsupp.mem_support_iff.mpr hi⟩)

@[simp] theorem coefficientAssembly_apply (x : (coefficientDiagram K carrier).sections)
    (i : I) : coefficientAssembly K carrier x i = coefficientAtCarrier K carrier x i := rfl

theorem coefficientAssembly_section (x : I →₀ K) :
    coefficientAssembly K carrier (coefficientSection K carrier x) = x := by
  apply Finsupp.ext
  intro i
  simp [coefficientAtCarrier]

theorem coefficientSection_assembly (x : (coefficientDiagram K carrier).sections) :
    coefficientSection K carrier (coefficientAssembly K carrier x) = x := by
  apply Subtype.ext
  funext p
  apply Subtype.ext
  apply Finsupp.ext
  intro i
  by_cases hi : carrier i ≤ p
  · simp [hi, coefficientAtCarrier_eq K carrier x i p hi]
  · have hx := (Finsupp.mem_supported' K (x.val p).val).mp (x.val p).property i hi
    simp [hi, hx]

/-- The exact coefficient gluing equivalence for a finite diagram. -/
def coefficientSectionEquiv : (I →₀ K) ≃ₗ[K] (coefficientDiagram K carrier).sections where
  toFun := coefficientSection K carrier
  invFun := coefficientAssembly K carrier
  left_inv := coefficientAssembly_section K carrier
  right_inv := coefficientSection_assembly K carrier
  map_add' := (coefficientSection K carrier).map_add
  map_smul' := (coefficientSection K carrier).map_smul
theorem coefficientSectionEquiv_palomar_formula (x : I →₀ K) :
    coefficientSectionEquiv K carrier x = coefficientSection K carrier x := rfl

/-- Any actual diagram with these coherent coefficient coordinates has the
same explicit global basis. The required coherent coordinates remain an
explicit input and must be established for the relevant face rings. -/
def sectionsFromCoherentCoefficients (D : ModuleDiagram K P)
    (e : CoherentEquiv D (coefficientDiagram K carrier)) :
    D.sections ≃ₗ[K] (I →₀ K) :=
  e.sectionEquiv.trans (coefficientSectionEquiv K carrier).symm
theorem sectionsFromCoherentCoefficients_palomar_formula (D : ModuleDiagram K P) (e : CoherentEquiv D (coefficientDiagram K carrier)) :
    sectionsFromCoherentCoefficients K carrier D e = e.sectionEquiv.trans (coefficientSectionEquiv K carrier).symm := rfl

end FourPapers.Universal
end
end


-- Close only the anonymous source scopes reopened by the next shard.
end
end
