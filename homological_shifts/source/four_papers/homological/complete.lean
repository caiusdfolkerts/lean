module
public import Aesop
public meta import Lean.Elab.Command
public meta import Lean.Elab.Tactic.Omega
public meta import Lean.Util.CollectAxioms
public meta import Lean.Util.FoldConsts
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.BigOperators.Option
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Group.Submonoid.Basic
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
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.SpanRank
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Order.Floor.Div
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Algebra.Ring.Subgroup
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.CategoryTheory.Abelian.Projective.Ext
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Combinatorics.Matroid.Circuit
public import Mathlib.Combinatorics.Matroid.IndepAxioms
public import Mathlib.Combinatorics.Matroid.Minor.Contract
public import Mathlib.Combinatorics.Matroid.Rank.ENat
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Option
public import Mathlib.Data.Finsupp.Interval
public import Mathlib.Data.Finsupp.Option
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Product
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Finsupp.Span
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.Order.Fin.Tuple
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Order.WithBot
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.ReesAlgebra
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Contrapose
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Tactic.Tauto

-- Generated verification output directories.
run_cmd Lean.Elab.Command.liftIO do
  IO.FS.createDirAll ".lake/reports/audit/homological"


@[expose] public section
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "0: CommAlg.ExteriorPower.BaseChange\n"

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

public section

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

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "1: CommAlg.ExteriorPower.Product\n"

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

@[expose] public section

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

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "2: CommAlg.KoszulComplex.Complex\n"

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
* `koszulComplex φ`: the Koszul complex of `φ`, as a `ChainComplex (ModuleCat R) ℕ`.
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

@[expose] public section

universe u v

open CategoryTheory Category Limits Module ExteriorAlgebra

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] (φ : M →ₗ[R] R)

/-- The alternating map for the Koszul differential. -/
noncomputable def koszulComplex.dAlternating (n : ℕ) :
    M [⋀^Fin (n + 1)]→ₗ[R] ⋀[R]^n M :=
  AlternatingMap.alternatizeUncurryFin (φ.smulRight (exteriorPower.ιMulti R n))

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
noncomputable def koszulComplex : ChainComplex (ModuleCat R) ℕ :=
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
noncomputable abbrev upOne : ChainComplex (ModuleCat R) ℕ :=
  (koszulComplex φ).augment (X := ModuleCat.of R PUnit) 0 (by simp)

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
              (koszulComplex φ).isoHomologyι₀.symm
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
noncomputable def shortComplexProd : ShortComplex (ChainComplex (ModuleCat R) ℕ) where
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
    · rw [← cancel_mono ((koszulComplex φ).isoHomologyι₀.hom)]
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
  (((koszulComplex φ).isoHomologyι₀.trans
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

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "3: CommAlg.KoszulComplex.Variables\n"

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

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "4: CommAlg.KoszulComplex.Resolution\n"

/-! ## Source: CommAlg.KoszulComplex.Resolution -/
section CheckedSource4

/-! # Genuine projective resolutions and derived Tor from Koszul complexes -/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CommAlg.Koszul

universe u
variable {R : Type u} [CommRing R]

/-- An exact positive-degree complex of projectives resolves its zeroth cokernel. -/
def resolutionOpcycles (K : ChainComplex (ModuleCat.{u} R) ℕ)
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
    ((koszulComplex.ofList l).isoHomologyι₀.symm ≪≫
      (koszulComplex.zeroHomologyOfListLinearEquiv l).toModuleIso)

@[simp] theorem regularSequenceResolution_complex (l : List R)
    (hl : RingTheory.Sequence.IsRegular R l) :
    (regularSequenceResolution l hl).complex = koszulComplex.ofList l := rfl

/-- Tensor a Koszul complex with a genuine module. -/
def coefficientComplex (l : List R) (M : ModuleCat.{u} R) :
    ChainComplex (ModuleCat.{u} R) ℕ :=
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

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "5: CommAlg.KoszulComplex.Polynomial\n"

/-! ## Source: CommAlg.KoszulComplex.Polynomial -/
section CheckedSource5

/-! # The polynomial Koszul resolution and the actual coefficient field -/

noncomputable section

namespace CommAlg.Koszul

open CategoryTheory MvPolynomial

universe u
variable {V k : Type u} [CommRing k]

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

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "6: TauCeti.Algebra.Homology.HomologicalComplex.Basic\n"

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

public section

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

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "7: TauCeti.Algebra.Homology.Homotopy\n"

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

@[expose] public section

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

variable {R : Type*} [Ring R] {P Q : ChainComplex (ModuleCat R) ℕ} {e e' : P ⟶ Q}

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

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "8: TauCeti.Algebra.Homology.Linear\n"

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

public section

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

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "9: TauCeti.LinearAlgebra.CliffordAlgebra.Grading\n"

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

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "10: TauCeti.LinearAlgebra.CliffordAlgebra.Contraction\n"

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

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "11: TauCeti.LinearAlgebra.ExteriorPower.Basic\n"

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

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "12: TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction\n"

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

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "13: TauCeti.RingTheory.KoszulComplex.Basic\n"

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

public section

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
@[expose] def koszulComplex (φ : Module.Dual R M) : ChainComplex (ModuleCat.{max u v} R) ℕ :=
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
  (koszulComplex φ).isoHomologyι₀ ≪≫
    (koszulComplex φ).opcyclesIsoSc' 1 0 0 (by simp) (by simp) ≪≫
      ((koszulComplex φ).sc' 1 0 0).moduleCatOpcyclesIso

private theorem pOpcycles_comp_homologyZeroIso_hom :
    (koszulComplex φ).pOpcycles 0 ≫ (koszulComplex φ).isoHomologyι₀.inv ≫
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
        ((koszulComplex φ).isoHomologyι₀.inv.hom (((koszulComplex φ).pOpcycles 0).hom x)) =
      Ideal.Quotient.mk _ (exteriorPower.zeroEquiv R M x) := by
  have hx : (homologyZeroIso φ).hom.hom
      ((koszulComplex φ).isoHomologyι₀.inv.hom (((koszulComplex φ).pOpcycles 0).hom x)) =
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
        ((koszulComplex (Fintype.linearCombination R x)).isoHomologyι₀.inv.hom
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

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "14: TauCeti.Algebra.Ring.Subgroup\n"

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

public section

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

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "15: TauCeti.RingTheory.Ideal.Operations\n"

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

public section

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

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "16: TauCeti.RingTheory.KoszulComplex.Basis\n"

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

public section

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

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "17: CommAlg.KoszulComplex.Coordinates\n"

/-! ## Source: CommAlg.KoszulComplex.Coordinates -/
section CheckedSource17

/-! # Exterior-basis coordinates of the genuine tensor Koszul differential -/

noncomputable section

set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false

namespace CommAlg.Koszul

open CategoryTheory TensorProduct

universe u
variable {R V : Type u} [CommRing R] [Fintype V] [LinearOrder V]

lemma differential_eq_contraction {N : Type*} [AddCommGroup N] [Module R N]
    (φ : N →ₗ[R] R) (i : ℕ) :
    koszulComplex.d φ i = TauCeti.koszulDifferential φ i := by
  apply exteriorPower.linearMap_ext
  ext v
  simp [koszulComplex.d, koszulComplex.dAlternating_apply,
    TauCeti.koszulDifferential_ιMulti]

/-- Tensor Koszul complex for an arbitrarily indexed finite sequence. -/
abbrev familyCoefficientComplex (x : V → R) (M : ModuleCat.{u} R) :
    ChainComplex (ModuleCat.{u} R) ℕ :=
  (((CategoryTheory.MonoidalCategory.tensoringRight (ModuleCat R)).obj M).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (koszulComplex (Fintype.linearCombination R x))

/-- Its genuine exterior-basis coordinate equivalence. -/
def coefficientCoordinates (x : V → R) (M : ModuleCat.{u} R) (i : ℕ) :
    (familyCoefficientComplex x M).X i ≃ₗ[R] (Set.powersetCard V i →₀ M) :=
  TensorProduct.equivFinsuppOfBasisLeft ((Pi.basisFun R V).exteriorPower i)

/-- The differential transported through the basis, not stipulated as a different complex. -/
def coordinateDifferential (x : V → R) (M : ModuleCat.{u} R) (i : ℕ) :
    (Set.powersetCard V (i + 1) →₀ M) →ₗ[R] (Set.powersetCard V i →₀ M) :=
  (coefficientCoordinates x M i).toLinearMap ∘ₗ
    ((familyCoefficientComplex x M).d (i + 1) i).hom ∘ₗ
      (coefficientCoordinates x M (i + 1)).symm.toLinearMap

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
    ChainComplex (ModuleCat.{u} R) ℕ :=
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
  apply (coefficientCoordinates x M i).injective
  rw [LinearEquiv.apply_symm_apply]
  exact (coordinates_basis_tensor x M i s m).symm

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

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "18: CommAlg.KoszulComplex.FiniteVariables\n"

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

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

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

abbrev FiniteResidue (V k : Type u) [CommRing k] :=
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

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "19: CommAlg.Polymatroid.Exponents\n"

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

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "20: CommAlg.KoszulComplex.CoefficientTor\n"

/-! ## Source: CommAlg.KoszulComplex.CoefficientTor -/
section CheckedSource20

/-!
# Genuine Tor over the coefficient ring

The coordinate Koszul complex is transported along exact restriction of
scalars. Its differential remains the actual tensor Koszul differential.
-/

noncomputable section

set_option maxHeartbeats 1000000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false

namespace CommAlg.Koszul

open CategoryTheory MvPolynomial CommAlg.Polymatroid

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

abbrev underlyingDifferential (B : Family V) (i : ℕ) :
    (Set.powersetCard V (i + 1) →₀ (monomialIdeal k B)) →ₗ[k]
      (Set.powersetCard V i →₀ (monomialIdeal k B)) :=
  (coordinateDifferential (X : V → MvPolynomial V k)
    (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B)) i).restrictScalars k

theorem underlyingDifferential_comp (B : Family V) (i : ℕ) :
    underlyingDifferential (k := k) B i ∘ₗ underlyingDifferential B (i + 1) = 0 := by
  apply LinearMap.ext
  intro z
  exact LinearMap.congr_fun
    (coordinateDifferential_comp (X : V → MvPolynomial V k)
      (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B)) i) z

/-- The genuine coordinate Koszul complex, regarded as a complex over the
coefficient ring by its canonical scalar structure. -/
def underlyingComplex (B : Family V) : ChainComplex (ModuleCat.{u} k) ℕ :=
  ChainComplex.of
    (fun i => ModuleCat.of k (Set.powersetCard V i →₀ (monomialIdeal k B)))
    (fun i => ModuleCat.ofHom (underlyingDifferential B i))
    (fun i => ModuleCat.hom_ext (underlyingDifferential_comp B i))

@[simp] theorem underlyingComplex_d (B : Family V) (i : ℕ) :
    (underlyingComplex (k := k) B).d (i + 1) i =
      ModuleCat.ofHom
        ((coordinateDifferential (X : V → MvPolynomial V k)
          (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B)) i).restrictScalars k) := by
  simp [underlyingComplex]

/-- The restriction-of-scalars module structure agrees with the canonical
coefficient-ring module structure. The equivalence is the identity on values. -/
def coefficientRestrictionEquiv (B : Family V) (i : ℕ) :
    ((ModuleCat.restrictScalars (algebraMap k (MvPolynomial V k))).obj
      (ModuleCat.of (MvPolynomial V k)
        (Set.powersetCard V i →₀ (monomialIdeal k B)))) ≃ₗ[k]
      (Set.powersetCard V i →₀ (monomialIdeal k B)) where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' := fun r z => by
    change (algebraMap k (MvPolynomial V k) r) •
      (show Set.powersetCard V i →₀ (monomialIdeal k B) from z) =
        r • (show Set.powersetCard V i →₀ (monomialIdeal k B) from z)
    exact algebraMap_smul (MvPolynomial V k) r
      (show Set.powersetCard V i →₀ (monomialIdeal k B) from z)

/-- Exact scalar restriction of the polynomial coordinate complex is
isomorphic to the same complex in canonical coefficient-ring modules. -/
def restrictionCoordinateComplexIso (B : Family V) :
    ((ModuleCat.restrictScalars (algebraMap k (MvPolynomial V k))).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj
      (coordinateComplex (X : V → MvPolynomial V k)
        (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B))) ≅
      underlyingComplex (k := k) B :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (coefficientRestrictionEquiv B i).toModuleIso)
    (by
      intro i j hij
      obtain rfl : i = j + 1 := hij.symm
      simp only [Functor.mapHomologicalComplex_obj_d, coordinateComplex_d,
        underlyingComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      rfl)

/-- Actual derived Tor, restricted to the coefficient ring, is the homology
of the original standard coordinate Koszul complex. -/
def coefficientTorIso [Nontrivial k] (B : Family V) (i : ℕ) :
    (ModuleCat.restrictScalars (algebraMap k (MvPolynomial V k))).obj
      (finitePolynomialTor i
        (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B))) ≅
      (underlyingComplex (k := k) B).homology i :=
  let F := ModuleCat.restrictScalars (algebraMap k (MvPolynomial V k))
  let M := ModuleCat.of (MvPolynomial V k) (monomialIdeal k B)
  let C := coordinateComplex (X : V → MvPolynomial V k) M
  F.mapIso (finitePolynomialTorIso i M ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat (MvPolynomial V k))
      (ComplexShape.down ℕ) i).mapIso (coordinateComplexIso (X : V → MvPolynomial V k) M)) ≪≫
    ((C.sc i).mapHomologyIso F).symm ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.down ℕ) i).mapIso
      (restrictionCoordinateComplexIso B)

end CommAlg.Koszul

end
end CheckedSource20

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "21: CommAlg.Grading.BasisPieces\n"

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

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "22: CommAlg.Simplicial.Chains\n"

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

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "23: CommAlg.KoszulComplex.FaceCombinatorics\n"

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

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "24: CommAlg.KoszulComplex.MonomialBasis\n"

/-! ## Source: CommAlg.KoszulComplex.MonomialBasis -/
section CheckedSource24

/-! # Actual monomial bases and the multigrading of the tensor Koszul complex -/

noncomputable section

set_option maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency false

namespace CommAlg.Koszul

open Classical MvPolynomial CommAlg.Polymatroid

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

lemma monomialIdeal_restrict_eq_span (B : Family V) :
    (monomialIdeal k B).restrictScalars k =
      Submodule.span k ((MvPolynomial.basisMonomials V k) '' {a | Contains B a}) := by
  ext f
  change f ∈ monomialIdeal k B ↔ _
  rw [mem_monomialIdeal_iff, Module.Basis.mem_span_image]
  rfl

def idealScalarEquiv (B : Family V) :
    (monomialIdeal k B).restrictScalars k ≃ₗ[k] monomialIdeal k B where
  toFun x := ⟨x.val, x.property⟩
  invFun x := ⟨x.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- All the monomials in a monomial ideal form an actual coefficient-ring basis. -/
def monomialBasis (B : Family V) :
    Module.Basis {a : Exponent V // Contains B a} k (monomialIdeal k B) :=
  (Grading.restrictedBasis (MvPolynomial.basisMonomials V k) (Contains B)).map
    ((LinearEquiv.ofEq _ _ (monomialIdeal_restrict_eq_span B).symm).trans (idealScalarEquiv B))

@[simp] lemma monomialBasis_val (B : Family V) (a : {a : Exponent V // Contains B a}) :
    (monomialBasis (k := k) B a).val = MvPolynomial.monomial a.val 1 := by
  unfold monomialBasis
  rw [Module.Basis.map_apply]
  change (Grading.restrictedBasis (MvPolynomial.basisMonomials V k) (Contains B) a).val = _
  exact Grading.restrictedBasis_val (MvPolynomial.basisMonomials V k) (Contains B) a

abbrev MonomialIndex (B : Family V) (i : ℕ) :=
  Σ s : Set.powersetCard V i, {a : Exponent V // Contains B a}

/-- The exterior-monomial basis of the actual coefficient module of the Koszul complex. -/
def monomialCoefficientBasis (B : Family V) (i : ℕ) :
    Module.Basis (MonomialIndex B i) k
      (Set.powersetCard V i →₀ (monomialIdeal k B)) :=
  Finsupp.basis (fun _ : Set.powersetCard V i => monomialBasis B)

@[simp] lemma monomialCoefficientBasis_apply (B : Family V) (i : ℕ)
    (s : Set.powersetCard V i) (a : {a : Exponent V // Contains B a}) :
    monomialCoefficientBasis (k := k) B i ⟨s, a⟩ =
      Finsupp.single s (monomialBasis B a) := by
  simp [monomialCoefficientBasis, Finsupp.coe_basis]

attribute [irreducible] monomialBasis monomialCoefficientBasis

/-- Its multidegree includes the exterior factor, as in the standard graded Koszul resolution. -/
def monomialDegree {B : Family V} {i : ℕ} (t : MonomialIndex B i) : Exponent V :=
  t.2.val + faceExponent t.1.val

/-- The degree-`a` submodule of the actual tensor Koszul coefficient module. -/
def homogeneousPiece (B : Family V) (a : Exponent V) (i : ℕ) :
    Submodule k (Set.powersetCard V i →₀ (monomialIdeal k B)) :=
  Grading.Piece (R := k) (M := Set.powersetCard V i →₀ (monomialIdeal k B)) (monomialCoefficientBasis (k := k) B i) monomialDegree a

instance homogeneousPiece_addCommGroup (B : Family V) (a : Exponent V) (i : ℕ) :
    AddCommGroup (homogeneousPiece (k := k) B a i) :=
  Submodule.addCommGroup (R := k) (M := Set.powersetCard V i →₀ (monomialIdeal k B))
    (homogeneousPiece B a i)

/-- Its canonical homogeneous projection on the actual coefficient module. -/
def homogeneousProjection (B : Family V) (a : Exponent V) (i : ℕ) :
    (Set.powersetCard V i →₀ (monomialIdeal k B)) →ₗ[k]
      (Set.powersetCard V i →₀ (monomialIdeal k B)) :=
  Grading.projection (R := k) (M := Set.powersetCard V i →₀ (monomialIdeal k B)) (monomialCoefficientBasis (k := k) B i) monomialDegree a

lemma homogeneousProjection_mem (B : Family V) (a : Exponent V) (i : ℕ)
    (x : Set.powersetCard V i →₀ (monomialIdeal k B)) :
    homogeneousProjection (k := k) B a i x ∈ homogeneousPiece (k := k) B a i :=
by
  unfold homogeneousProjection homogeneousPiece
  exact Grading.projection_mem (R := k) (M := Set.powersetCard V i →₀ (monomialIdeal k B))
    (monomialCoefficientBasis (k := k) B i) monomialDegree a x

lemma homogeneous_decomposition (B : Family V) (i : ℕ)
    (x : Set.powersetCard V i →₀ (monomialIdeal k B)) :
    ∑ a ∈ ((monomialCoefficientBasis (k := k) B i).repr x).support.image monomialDegree,
      homogeneousProjection (k := k) B a i x = x :=
by
  unfold homogeneousProjection
  exact Grading.sum_projections (R := k) (M := Set.powersetCard V i →₀ (monomialIdeal k B))
    (monomialCoefficientBasis (k := k) B i) monomialDegree x

end CommAlg.Koszul

end
end CheckedSource24

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "25: CommAlg.Simplicial.Filling\n"

/-! ## Source: CommAlg.Simplicial.Filling -/
section CheckedSource25

/-! # Chain-level deletion/contraction and nonzero homology

Every predicate below refers to actual exterior chains, their actual boundary, and the actual
existence of a filling chain. These lemmas supply the full homological induction for matroids.
-/

noncomputable section

namespace CommAlg.Simplicial

variable {V k : Type*} [Fintype V] [LinearOrder V] [CommRing k]

/-- Every closed augmented chain in this degree is the boundary of a chain in the next degree. -/
def ExactIn (K : Finset V → Prop) (i : ℕ) : Prop :=
  ∀ z : Ambient V k, z ∈ Chains K i → boundary z = 0 →
    ∃ y : Ambient V k, y ∈ Chains K (i + 1) ∧ boundary y = z

/-- An actual closed chain whose homology class does not vanish. -/
def NonzeroHomology (K : Finset V → Prop) (i : ℕ) : Prop :=
  ∃ z : Ambient V k, z ∈ Chains K i ∧ boundary z = 0 ∧
    ∀ y : Ambient V k, y ∈ Chains K (i + 1) → boundary y ≠ z

lemma nonzeroHomology_iff_not_exactIn (K : Finset V → Prop) (i : ℕ) :
    NonzeroHomology (k := k) K i ↔ ¬ExactIn (k := k) K i := by
  classical
  simp only [NonzeroHomology, ExactIn, not_forall, not_exists, not_and]
  tauto

lemma chains_eq_bot_of_no_face {K : Finset V → Prop} {i : ℕ}
    (h : ∀ s, K s → s.card ≠ i) : Chains (k := k) K i = ⊥ := by
  apply le_antisymm _ bot_le
  rw [Chains, Submodule.span_le]
  rintro z ⟨s, ⟨hs, hc⟩, rfl⟩
  exact (h s hs hc).elim

lemma exactIn_of_no_face {K : Finset V → Prop} {i : ℕ}
    (h : ∀ s, K s → s.card ≠ i) : ExactIn (k := k) K i := by
  intro z hz hcycle
  rw [chains_eq_bot_of_no_face h, Submodule.mem_bot] at hz
  subst z
  exact ⟨0, Submodule.zero_mem _, map_zero _⟩

lemma creation_mem_of_cone {K : Finset V → Prop} (e : V)
    (hc : ∀ s, K s → K (insert e s)) {i : ℕ} {z : Ambient V k}
    (hz : z ∈ Chains K i) : creation e z ∈ Chains K (i + 1) := by
  induction hz using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨s, ⟨hs, hcard⟩, rfl⟩ := ha
    rw [creation_basis]
    split_ifs with he
    · exact Submodule.zero_mem _
    · apply Submodule.smul_mem
      exact basis_mem (hc s hs) (by simp [he, hcard])
  | zero => simpa using (Submodule.zero_mem (Chains (k := k) K (i + 1)))
  | add a b ha hb iha ihb => simpa [mul_add] using Submodule.add_mem _ iha ihb
  | smul r a ha ih => simpa using Submodule.smul_mem _ r ih

lemma exactIn_of_cone {K : Finset V → Prop} (e : V)
    (hc : ∀ s, K s → K (insert e s)) (i : ℕ) : ExactIn (k := k) K i := by
  intro z hz hcycle
  refine ⟨creation e z, creation_mem_of_cone e hc hz, ?_⟩
  simp only [boundary_creation, hcycle, map_zero, sub_zero]

lemma exactIn_zero_of_vertex {K : Finset V → Prop} (e : V) (he : K {e}) :
    ExactIn (k := k) K 0 := by
  intro z hz hcycle
  have hc : creation e z ∈ Chains K 1 := by
    clear hcycle
    induction hz using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨s, ⟨hs, hcard⟩, rfl⟩ := ha
      obtain rfl : s = ∅ := Finset.card_eq_zero.mp hcard
      rw [creation_basis]
      simp only [Finset.notMem_empty, ↓reduceIte, Finset.insert_empty]
      exact Submodule.smul_mem _ _ (basis_mem he (Finset.card_singleton _))
    | zero => simpa using (Submodule.zero_mem (Chains (k := k) K 1))
    | add a b ha hb iha ihb => simpa [mul_add] using Submodule.add_mem _ iha ihb
    | smul r a ha ih => simpa using Submodule.smul_mem _ r ih
  refine ⟨creation e z, hc, ?_⟩
  simp only [boundary_creation, hcycle, map_zero, sub_zero]

lemma nonzeroHomology_zero_of_only_empty [Nontrivial k] {K : Finset V → Prop}
    (he : K ∅) (hK : ∀ s, K s → s = ∅) : NonzeroHomology (k := k) K 0 := by
  refine ⟨basis ∅, basis_mem he rfl, ?_, ?_⟩
  · exact boundary_zero_degree_zero (basis_mem he rfl)
  · intro y hy hyb
    have hn : ∀ s, K s → s.card ≠ 1 := by
      intro s hs
      rw [hK s hs]
      simp
    rw [chains_eq_bot_of_no_face hn, Submodule.mem_bot] at hy
    subst y
    have hb : basis (k := k) (∅ : Finset V) ≠ 0 := Module.Basis.ne_zero _ _
    exact hb (by simpa using hyb.symm)

/-- The exactness half of deletion/contraction, proved by filling explicit chains. -/
lemma exactIn_of_deletion_link {K : Finset V → Prop} (hK : Downward K) (e : V) (i : ℕ)
    (hdel : ExactIn (k := k) (deletion K e) (i + 1))
    (hlink : ExactIn (k := k) (link K e) i) : ExactIn (k := k) K (i + 1) := by
  intro z hz hcycle
  have hw := contraction_mem e hz
  have hwcycle : boundary (contraction e z) = 0 := by
    have h := contraction_boundary e z
    rw [hcycle, map_zero, eq_neg_iff_add_eq_zero, zero_add] at h
    exact h
  obtain ⟨v, hv, hvb⟩ := hlink _ hw hwcycle
  let z' := z + boundary (creation e v)
  have hz' : z' ∈ Chains K (i + 1) :=
    Submodule.add_mem _ hz (boundary_mem hK (creation_mem_link e hv))
  have hvcon : contraction e v = 0 :=
    contraction_zero_of_deletion e (link_le_deletion hK e _ hv)
  have hz'con : contraction e z' = 0 := by
    dsimp only [z']
    rw [map_add, contraction_boundary, contraction_creation, hvcon, map_zero, sub_zero, hvb]
    exact add_neg_cancel _
  have hz'del := mem_deletion_of_contraction_zero e hz' hz'con
  have hz'cycle : boundary z' = 0 := by
    simp only [z', map_add, hcycle, boundary_boundary, add_zero]
  obtain ⟨y, hy, hyb⟩ := hdel z' hz'del hz'cycle
  refine ⟨y - creation e v,
    Submodule.sub_mem _ (chains_mono (fun s hs => hs.1) _ hy) (creation_mem_link e hv), ?_⟩
  rw [map_sub, hyb]
  exact add_sub_cancel_right z _

/-- Nonzero link homology produces nonzero homology one degree higher, whenever every chain in
that degree of the deletion can be filled. The proof constructs the cycle explicitly. -/
lemma nonzeroHomology_of_link {K : Finset V → Prop} (hK : Downward K) (e : V) (i : ℕ)
    (hdel : ExactIn (k := k) (deletion K e) i)
    (hlink : NonzeroHomology (k := k) (link K e) i) :
    NonzeroHomology (k := k) K (i + 1) := by
  obtain ⟨w, hw, hwcycle, hwnonboundary⟩ := hlink
  obtain ⟨y, hy, hyb⟩ := hdel w (link_le_deletion hK e i hw) hwcycle
  refine ⟨creation e w - y,
    Submodule.sub_mem _ (creation_mem_link e hw) (chains_mono (fun s hs => hs.1) _ hy), ?_, ?_⟩
  · rw [map_sub, boundary_creation, hwcycle, map_zero, sub_zero, hyb, sub_self]
  · intro q hq hqb
    have hwcon := contraction_zero_of_deletion e (link_le_deletion hK e i hw)
    have hycon := contraction_zero_of_deletion e hy
    have h := congrArg (contraction e) hqb
    rw [contraction_boundary, map_sub, contraction_creation, hwcon, map_zero, sub_zero,
      hycon, sub_zero] at h
    exact hwnonboundary (-contraction e q)
      (Submodule.neg_mem _ (contraction_mem e hq)) (by simpa only [map_neg] using h)

end CommAlg.Simplicial

end
end CheckedSource25

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "26: CommAlg.Simplicial.Homology\n"

/-! ## Source: CommAlg.Simplicial.Homology -/
section CheckedSource26

/-! # Actual categorical homology of the augmented exterior chains -/

noncomputable section

namespace CommAlg.Simplicial

open CategoryTheory CategoryTheory.Limits

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

/-- The usual signed boundary, restricted to the actual face-chain submodules. -/
def chainDifferential {K : Finset V → Prop} (hK : Downward K) (i : ℕ) :
    Chains (k := k) K (i + 1) →ₗ[k] Chains (k := k) K i :=
  (boundary.domRestrict (Chains K (i + 1))).codRestrict _
    (fun z => boundary_mem hK z.property)

@[simp] lemma chainDifferential_val {K : Finset V → Prop} (hK : Downward K) (i : ℕ)
    (z : Chains (k := k) K (i + 1)) :
    (chainDifferential hK i z).val = boundary z.val := rfl

lemma chainDifferential_comp {K : Finset V → Prop} (hK : Downward K) (i : ℕ) :
    chainDifferential (k := k) hK i ∘ₗ chainDifferential hK (i + 1) = 0 := by
  ext z
  exact boundary_boundary z.val

/-- This is the genuine augmented simplicial chain complex, with the empty face in degree zero. -/
def chainComplex {K : Finset V → Prop} (hK : Downward K) :
    ChainComplex (ModuleCat.{u} k) ℕ :=
  ChainComplex.of (fun i => ModuleCat.of k (Chains (k := k) K i))
    (fun i => ModuleCat.ofHom (chainDifferential hK i))
    (fun i => ModuleCat.hom_ext (chainDifferential_comp hK i))

@[simp] lemma chainComplex_d {K : Finset V → Prop} (hK : Downward K) (i : ℕ) :
    (chainComplex (k := k) hK).d (i + 1) i = ModuleCat.ofHom (chainDifferential hK i) := by
  simp [chainComplex]

lemma chainComplex_exactAt_succ_iff {K : Finset V → Prop} (hK : Downward K) (i : ℕ) :
    (chainComplex (k := k) hK).ExactAt (i + 1) ↔ ExactIn (k := k) K (i + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (i + 2) (i + 1) i (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  dsimp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor']
  simp only [chainComplex_d]
  change (∀ z : Chains (k := k) K (i + 1), chainDifferential hK i z = 0 →
    ∃ y : Chains (k := k) K (i + 2), chainDifferential hK (i + 1) y = z) ↔ _
  constructor
  · intro h z hz hc
    obtain ⟨y, hy⟩ := h ⟨z, hz⟩ (Subtype.ext hc)
    exact ⟨y.val, y.property, congrArg Subtype.val hy⟩
  · intro h z hz
    obtain ⟨y, hy, heq⟩ := h z.val z.property (congrArg Subtype.val hz)
    exact ⟨⟨y, hy⟩, Subtype.ext heq⟩

lemma chainComplex_exactAt_zero_iff {K : Finset V → Prop} (hK : Downward K) :
    (chainComplex (k := k) hK).ExactAt 0 ↔ ExactIn (k := k) K 0 := by
  rw [HomologicalComplex.exactAt_iff' _ 1 0 0 (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  dsimp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor']
  rw [chainComplex_d, (chainComplex (k := k) hK).shape 0 0 (by simp)]
  change (∀ z : Chains (k := k) K 0, (0 : Chains (k := k) K 0) = 0 →
    ∃ y : Chains (k := k) K 1, chainDifferential hK 0 y = z) ↔ _
  constructor
  · intro h z hz hc
    obtain ⟨y, hy⟩ := h ⟨z, hz⟩ rfl
    exact ⟨y.val, y.property, congrArg Subtype.val hy⟩
  · intro h z hz
    obtain ⟨y, hy, heq⟩ := h z.val z.property (boundary_zero_degree_zero z.property)
    exact ⟨⟨y, hy⟩, Subtype.ext heq⟩

lemma chainComplex_exactAt_iff {K : Finset V → Prop} (hK : Downward K) (i : ℕ) :
    (chainComplex (k := k) hK).ExactAt i ↔ ExactIn (k := k) K i := by
  cases i with
  | zero => exact chainComplex_exactAt_zero_iff hK
  | succ i => exact chainComplex_exactAt_succ_iff hK i

/-- The explicit cycle/nonboundary condition is equivalent to nonvanishing of actual homology. -/
lemma homology_nonzero_iff {K : Finset V → Prop} (hK : Downward K) (i : ℕ) :
    ¬ IsZero ((chainComplex (k := k) hK).homology i) ↔ NonzeroHomology (k := k) K i := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology, chainComplex_exactAt_iff,
    nonzeroHomology_iff_not_exactIn]

end CommAlg.Simplicial

end
end CheckedSource26

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "27: CommAlg.KoszulComplex.Faces\n"

/-! ## Source: CommAlg.KoszulComplex.Faces -/
section CheckedSource27

/-! # The actual upper Koszul faces and their homogeneous chain indices -/

noncomputable section

set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

namespace CommAlg.Koszul

open Classical CommAlg.Polymatroid

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

abbrev FaceIndex (B : Family V) (a : Exponent V) (i : ℕ) :=
  {s : Finset V // koszulFaces B a s ∧ s.card = i}

def faceChainBasis (B : Family V) (a : Exponent V) (i : ℕ) :
    Module.Basis (FaceIndex B a i) k (Simplicial.Chains (k := k) (koszulFaces B a) i) :=
  Grading.restrictedBasis Simplicial.basis (fun s => koszulFaces B a s ∧ s.card = i)

@[simp] lemma faceChainBasis_val (B : Family V) (a : Exponent V) (i : ℕ)
    (s : FaceIndex B a i) : (faceChainBasis (k := k) B a i s).val = Simplicial.basis s.val :=
  Grading.restrictedBasis_val _ _ _

/-- Exact matching of simplicial face bases with actual monomial-exterior bases of degree `a`. -/
def faceMonomialEquiv (B : Family V) (a : Exponent V) (i : ℕ) :
    FaceIndex B a i ≃ {t : MonomialIndex B i // monomialDegree t = a} where
  toFun s := ⟨⟨⟨s.val, s.property.2⟩,
    ⟨a - faceExponent s.val, s.property.1.2⟩⟩,
    tsub_add_cancel_of_le s.property.1.1⟩
  invFun t := ⟨t.val.1.val, ⟨⟨by
    exact (le_add_of_nonneg_left (show (0 : Exponent V) ≤ t.val.2.val from zero_le)).trans_eq t.property, by
    have he : a - faceExponent t.val.1.val = t.val.2.val := by
      exact (congrArg (fun b : Exponent V => b - faceExponent t.val.1.val)
        t.property.symm).trans (add_tsub_cancel_right _ _)
    rw [he]
    exact t.val.2.property⟩, t.val.1.property⟩⟩
  left_inv s := rfl
  right_inv t := by
    rcases t with ⟨⟨s, b⟩, ht⟩
    apply Subtype.ext
    dsimp only
    have hb : a - faceExponent s.val = b.val :=
      (congrArg (fun c : Exponent V => c - faceExponent s.val)
        ht.symm).trans (add_tsub_cancel_right _ _)
    exact congrArg (fun c : {c : Exponent V // Contains B c} => (⟨s, c⟩ : MonomialIndex B i))
      (Subtype.ext hb)

/-- The isomorphism acts on real chains in the actual Koszul homogeneous component. -/
def faceHomogeneousEquiv (B : Family V) (a : Exponent V) (i : ℕ) :
    Simplicial.Chains (k := k) (koszulFaces B a) i ≃ₗ[k] homogeneousPiece (k := k) B a i :=
  (faceChainBasis (k := k) B a i).equiv
    (Grading.restrictedBasis (monomialCoefficientBasis (k := k) B i)
      (fun t => monomialDegree t = a)) (faceMonomialEquiv B a i)

@[simp] lemma faceHomogeneousEquiv_basis (B : Family V) (a : Exponent V) (i : ℕ)
    (s : FaceIndex B a i) :
    (faceHomogeneousEquiv (k := k) B a i (faceChainBasis (k := k) B a i s)).val =
      monomialCoefficientBasis (k := k) B i (faceMonomialEquiv B a i s).val := by
  unfold faceHomogeneousEquiv
  rw [Module.Basis.equiv_apply]
  exact Grading.restrictedBasis_val _ _ _

end CommAlg.Koszul

end
end CheckedSource27

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "28: CommAlg.KoszulComplex.MonomialDifferential\n"

/-! ## Source: CommAlg.KoszulComplex.MonomialDifferential -/
section CheckedSource28

/-! # The actual Koszul differential preserves the standard multigrading -/

noncomputable section

set_option maxHeartbeats 200000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false

namespace CommAlg.Koszul

open Classical MvPolynomial CommAlg.Polymatroid CategoryTheory

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

abbrev monomialDifferential (B : Family V) (i : ℕ) :
    (Set.powersetCard V (i + 1) →₀ (monomialIdeal k B)) →ₗ[k]
      (Set.powersetCard V i →₀ (monomialIdeal k B)) :=
  (coordinateDifferential (X : V → MvPolynomial V k)
    (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B)) i).restrictScalars k

/-- A term obtained by removing one exterior variable and multiplying the coefficient by it. -/
def differentialIndex {B : Family V} {i : ℕ} (t : MonomialIndex B (i + 1))
    (j : {j // j ∈ t.1.val}) : MonomialIndex B i :=
  ⟨eraseIndex t.1 j, ⟨t.2.val + Finsupp.single j.val 1, by
    obtain ⟨b, hb, hba⟩ := t.2.property
    exact ⟨b, hb, hba.trans (le_add_of_nonneg_right (zero_le))⟩⟩⟩

lemma differentialIndex_degree {B : Family V} {i : ℕ} (t : MonomialIndex B (i + 1))
    (j : {j // j ∈ t.1.val}) :
    monomialDegree (differentialIndex t j) = monomialDegree t := by
  change (t.2.val + Finsupp.single j.val 1) + faceExponent (t.1.val.erase j.val) = _
  rw [add_assoc, add_comm (Finsupp.single j.val 1), faceExponent_erase_add j.property]
  rfl

lemma monomialBasis_mul_variable (B : Family V) (a : {a : Exponent V // Contains B a})
    (j : V) (ha : Contains B (a.val + Finsupp.single j 1)) :
    (X j : MvPolynomial V k) • monomialBasis (k := k) B a =
      monomialBasis (k := k) B ⟨a.val + Finsupp.single j 1, ha⟩ := by
  apply Subtype.ext
  change X j * (monomialBasis (k := k) B a).val = _
  rw [monomialBasis_val, monomialBasis_val, X, monomial_mul_monomial]
  simp [add_comm]

lemma monomialDifferential_basis (B : Family V) (i : ℕ) (t : MonomialIndex B (i + 1)) :
    monomialDifferential (k := k) B i (monomialCoefficientBasis (k := k) B (i + 1) t) =
      ∑ j : {j // j ∈ t.1.val}, TauCeti.ExteriorAlgebra.basisEraseSign j.val t.1.val •
        monomialCoefficientBasis (k := k) B i (differentialIndex t j) := by
  rcases t with ⟨s, a⟩
  rw [monomialCoefficientBasis_apply]
  change coordinateDifferential (X : V → MvPolynomial V k)
    (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B)) i
    (Finsupp.single s (monomialBasis (k := k) B a)) = _
  rw [coordinateDifferential_single]
  apply Finset.sum_congr rfl
  intro j hj
  change Finsupp.single (eraseIndex s j)
    (X j.val • (TauCeti.ExteriorAlgebra.basisEraseSign j.val s.val • monomialBasis (k := k) B a)) = _
  rw [smul_comm (X j.val)]
  rw [monomialBasis_mul_variable (k := k) B a j.val (differentialIndex (B := B) ⟨s, a⟩ j).2.property]
  simp [differentialIndex, monomialCoefficientBasis_apply, Finsupp.smul_single]

lemma monomialDifferential_comp (B : Family V) (i : ℕ) :
    monomialDifferential (k := k) B i ∘ₗ monomialDifferential (k := k) B (i + 1) = 0 := by
  apply LinearMap.ext
  intro z
  exact LinearMap.congr_fun (underlyingDifferential_comp (k := k) B i) z

lemma monomialDifferential_homogeneous (B : Family V) (a : Exponent V) (i : ℕ)
    {z : Set.powersetCard V (i + 1) →₀ (monomialIdeal k B)}
    (hz : z ∈ homogeneousPiece (k := k) B a (i + 1)) :
    monomialDifferential (k := k) B i z ∈ homogeneousPiece (k := k) B a i := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨t, ht, rfl⟩ := hz
    rw [monomialDifferential_basis]
    apply Submodule.sum_mem
    intro j hj
    apply (Submodule.smul_mem_iff' _ (TauCeti.ExteriorAlgebra.basisEraseSign j.val t.1.val)).2
    exact Submodule.subset_span
      ⟨differentialIndex t j, (differentialIndex_degree t j).trans ht, rfl⟩
  | zero => simpa only [map_zero] using (Submodule.zero_mem (homogeneousPiece (k := k) B a i))
  | add z w hz hw ihz ihw => simpa using Submodule.add_mem _ ihz ihw
  | smul c z hz ih => simpa using Submodule.smul_mem _ c ih

lemma homogeneousProjection_differential (B : Family V) (a : Exponent V) (i : ℕ) :
    homogeneousProjection (k := k) B a i ∘ₗ monomialDifferential (k := k) B i =
      monomialDifferential (k := k) B i ∘ₗ homogeneousProjection (k := k) B a (i + 1) := by
  apply (monomialCoefficientBasis (k := k) B (i + 1)).ext
  intro t
  change homogeneousProjection (k := k) B a i
    (monomialDifferential B i (monomialCoefficientBasis B (i + 1) t)) =
    monomialDifferential B i (homogeneousProjection B a (i + 1)
      (monomialCoefficientBasis B (i + 1) t))
  have hm : monomialDifferential (k := k) B i (monomialCoefficientBasis B (i + 1) t) ∈
      homogeneousPiece B (monomialDegree t) i :=
    monomialDifferential_homogeneous B _ i (Grading.basis_mem_piece _ _ t)
  change Grading.projection _ _ a _ = monomialDifferential (k := k) B i
    (Grading.projection _ _ a ((monomialCoefficientBasis B (i + 1)) t))
  rw [Grading.projection_basis]
  by_cases ht : monomialDegree t = a
  · rw [if_pos ht]
    exact Grading.projection_eq_self (ht ▸ hm)
  · rw [if_neg ht, map_zero]
    exact Grading.projection_eq_zero (Ne.symm ht) hm

/-- Restricting the actual Koszul differential to its genuine degree component. -/
def homogeneousDifferential (B : Family V) (a : Exponent V) (i : ℕ) :
    homogeneousPiece (k := k) B a (i + 1) →ₗ[k] homogeneousPiece (k := k) B a i :=
  ((monomialDifferential (k := k) B i).domRestrict (homogeneousPiece (k := k) B a (i + 1))).codRestrict _
    (fun z => monomialDifferential_homogeneous B a i z.property)

lemma homogeneousDifferential_comp (B : Family V) (a : Exponent V) (i : ℕ) :
    homogeneousDifferential (k := k) B a i ∘ₗ homogeneousDifferential (k := k) B a (i + 1) = 0 := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  exact LinearMap.congr_fun (monomialDifferential_comp B i) z.val

/-- The actual multidegree subcomplex of the tensor Koszul resolution. -/
def homogeneousComplex (B : Family V) (a : Exponent V) :
    ChainComplex (ModuleCat.{u} k) ℕ :=
  ChainComplex.of (fun i => ModuleCat.of k (homogeneousPiece (k := k) B a i))
    (fun i => ModuleCat.ofHom (homogeneousDifferential (k := k) B a i))
    (fun i => ModuleCat.hom_ext (homogeneousDifferential_comp B a i))

@[simp] lemma homogeneousComplex_d (B : Family V) (a : Exponent V) (i : ℕ) :
    (homogeneousComplex (k := k) B a).d (i + 1) i =
      ModuleCat.ofHom (homogeneousDifferential (k := k) B a i) := by
  simp [homogeneousComplex]

end CommAlg.Koszul

end
end CheckedSource28

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "29: CommAlg.KoszulComplex.HomogeneousFaces\n"

/-! ## Source: CommAlg.KoszulComplex.HomogeneousFaces -/
section CheckedSource29

/-! # Homogeneous Koszul components are genuinely isomorphic to upper-face chains -/

noncomputable section

set_option maxHeartbeats 1000000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false

namespace CommAlg.Koszul

open Classical CommAlg.Polymatroid CategoryTheory

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

lemma boundary_basis_sum (s : Finset V) :
    Simplicial.boundary (Simplicial.basis (k := k) s) =
      ∑ j : {j // j ∈ s}, TauCeti.ExteriorAlgebra.basisEraseSign j.val s •
        Simplicial.basis (s.erase j.val) := by
  rw [Simplicial.boundary_eq_sum]
  calc
    ∑ j : V, Simplicial.contraction j (Simplicial.basis s) =
        ∑ j ∈ s, Simplicial.contraction j (Simplicial.basis s) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j hj hnot
      simp only [Simplicial.contraction_basis, if_neg hnot]
    _ = ∑ j : {j // j ∈ s}, Simplicial.contraction j.val (Simplicial.basis s) :=
      Finset.sum_subtype s (fun _ => Iff.rfl) _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Simplicial.contraction_basis, if_pos j.property]

def eraseFace {B : Family V} {a : Exponent V} {i : ℕ}
    (s : FaceIndex B a (i + 1)) (j : {j // j ∈ s.val}) : FaceIndex B a i :=
  ⟨s.val.erase j.val,
    (koszulFaces_downward B a) (Finset.erase_subset _ _) s.property.1,
    by simp [Finset.card_erase_of_mem j.property, s.property.2]⟩

lemma faceChainDifferential_basis (B : Family V) (a : Exponent V) (i : ℕ)
    (s : FaceIndex B a (i + 1)) :
    Simplicial.chainDifferential (k := k) (koszulFaces_downward B a) i
      (faceChainBasis (k := k) B a (i + 1) s) =
      ∑ j : {j // j ∈ s.val}, TauCeti.ExteriorAlgebra.basisEraseSign j.val s.val •
        faceChainBasis (k := k) B a i (eraseFace s j) := by
  apply Subtype.ext
  simp only [Simplicial.chainDifferential_val, faceChainBasis_val,
    Submodule.coe_sum, Submodule.coe_smul_of_tower, eraseFace]
  exact boundary_basis_sum s.val

lemma faceMonomialEquiv_erase (B : Family V) (a : Exponent V) (i : ℕ)
    (s : FaceIndex B a (i + 1)) (j : {j // j ∈ s.val}) :
    (faceMonomialEquiv B a i (eraseFace s j)).val =
      differentialIndex (faceMonomialEquiv B a (i + 1) s).val j := by
  have hExp : a - faceExponent (s.val.erase j.val) =
      a - faceExponent s.val + Finsupp.single j.val 1 := by
    have he := faceExponent_erase_add j.property
    have hle := s.property.1.1
    ext v
    have hv := hle v
    have hev := congrArg (fun b : Exponent V => b v) he
    simp only [Finsupp.add_apply, Finsupp.tsub_apply] at *
    omega
  exact congrArg (fun b : {b : Exponent V // Contains B b} =>
    (⟨eraseIndex ⟨s.val, s.property.2⟩ j, b⟩ : MonomialIndex B i)) (Subtype.ext hExp)

lemma faceHomogeneousEquiv_comm (B : Family V) (a : Exponent V) (i : ℕ) :
    (faceHomogeneousEquiv (k := k) B a i).toLinearMap ∘ₗ
        Simplicial.chainDifferential (koszulFaces_downward B a) i =
      homogeneousDifferential (k := k) B a i ∘ₗ
        (faceHomogeneousEquiv (k := k) B a (i + 1)).toLinearMap := by
  apply (faceChainBasis (k := k) B a (i + 1)).ext
  intro s
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, faceChainDifferential_basis,
    map_sum, map_zsmul_unit]
  apply Subtype.ext
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, faceHomogeneousEquiv_basis]
  change _ = monomialDifferential (k := k) B i
    ((faceHomogeneousEquiv (k := k) B a (i + 1))
      ((faceChainBasis (k := k) B a (i + 1)) s)).val
  rw [faceHomogeneousEquiv_basis, monomialDifferential_basis]
  apply Finset.sum_congr rfl
  intro j hj
  rw [faceMonomialEquiv_erase]
  rfl

/-- Kernel-checked chain isomorphism, including every homological and multigraded degree. -/
def homogeneousFacesIso (B : Family V) (a : Exponent V) :
    Simplicial.chainComplex (k := k) (koszulFaces_downward B a) ≅
      homogeneousComplex (k := k) B a :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (faceHomogeneousEquiv (k := k) B a i).toModuleIso) (by
      intro i j hij
      obtain rfl : i = j + 1 := hij.symm
      rw [Simplicial.chainComplex_d, homogeneousComplex_d]
      apply ModuleCat.hom_ext
      exact (faceHomogeneousEquiv_comm B a j).symm)

/-- Nonvanishing of an actual homogeneous Koszul homology group is exactly the face-chain condition. -/
lemma homogeneous_homology_nonzero_iff (B : Family V) (a : Exponent V) (i : ℕ) :
    ¬ CategoryTheory.Limits.IsZero ((homogeneousComplex (k := k) B a).homology i) ↔
      Simplicial.NonzeroHomology (k := k) (koszulFaces B a) i := by
  have e := (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.down ℕ) i).mapIso
    (homogeneousFacesIso (k := k) B a)
  have he : CategoryTheory.Limits.IsZero
      ((Simplicial.chainComplex (k := k) (koszulFaces_downward B a)).homology i) ↔
      CategoryTheory.Limits.IsZero ((homogeneousComplex (k := k) B a).homology i) :=
    e.isZero_iff
  exact (not_congr he.symm).trans (Simplicial.homology_nonzero_iff _ i)

end CommAlg.Koszul

end
end CheckedSource29

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "30: CommAlg.KoszulComplex.GradedTor\n"

/-! ## Source: CommAlg.KoszulComplex.GradedTor -/
section CheckedSource30

/-! # Standard multigraded pieces as actual submodules of genuine derived Tor

The degree pieces below are images in Mathlib's derived tensor functor. Their inclusions split
by the homogeneous projections of the actual Koszul resolution. No combinatorial support
condition is used in their definition.
-/

noncomputable section

set_option maxHeartbeats 100000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true

namespace CommAlg.Koszul

open Classical CommAlg.Polymatroid CategoryTheory CategoryTheory.Limits

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

/-- Inclusion of the genuine homogeneous subcomplex. -/
def homogeneousInclusion (B : Family V) (a : Exponent V) :
    homogeneousComplex (k := k) B a ⟶ underlyingComplex (k := k) B where
  f i := ModuleCat.ofHom (homogeneousPiece (k := k) B a i).subtype
  comm' i j hij := by
    obtain rfl : i = j + 1 := hij.symm
    rw [homogeneousComplex_d, underlyingComplex_d]
    rfl

/-- Projection onto the genuine homogeneous subcomplex. -/
def homogeneousRetraction (B : Family V) (a : Exponent V) :
    underlyingComplex (k := k) B ⟶ homogeneousComplex (k := k) B a where
  f i := ModuleCat.ofHom ((homogeneousProjection (k := k) B a i).codRestrict _
    (fun z => homogeneousProjection_mem B a i z))
  comm' i j hij := by
    obtain rfl : i = j + 1 := hij.symm
    rw [homogeneousComplex_d, underlyingComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    exact (LinearMap.congr_fun (homogeneousProjection_differential B a j) z).symm

lemma homogeneousInclusion_retraction (B : Family V) (a : Exponent V) :
    homogeneousInclusion (k := k) B a ≫ homogeneousRetraction (k := k) B a = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  exact Grading.projection_eq_self z.property

lemma homogeneousHomology_injective (B : Family V) (a : Exponent V) (i : ℕ) :
    Function.Injective (HomologicalComplex.homologyMap
      (homogeneousInclusion (k := k) B a) i).hom := by
  have hs : HomologicalComplex.homologyMap (homogeneousInclusion (k := k) B a) i ≫
      HomologicalComplex.homologyMap (homogeneousRetraction (k := k) B a) i = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp, homogeneousInclusion_retraction,
      HomologicalComplex.homologyMap_id]
  intro x y h
  have hh := congrArg (HomologicalComplex.homologyMap (homogeneousRetraction (k := k) B a) i) h
  simpa only [← ModuleCat.comp_apply, hs, ModuleCat.id_apply] using hh

variable [Nontrivial k]

/-- The map from homogeneous Koszul homology into the actual derived Tor module. -/
def toDerivedTor (B : Family V) (a : Exponent V) (i : ℕ) :
    (homogeneousComplex (k := k) B a).homology i ⟶
      (ModuleCat.restrictScalars (algebraMap k (MvPolynomial V k))).obj
        (finitePolynomialTor i (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B))) :=
  HomologicalComplex.homologyMap (homogeneousInclusion (k := k) B a) i ≫ (coefficientTorIso (k := k) B i).inv

lemma toDerivedTor_injective (B : Family V) (a : Exponent V) (i : ℕ) :
    Function.Injective (toDerivedTor (k := k) B a i).hom := by
  intro x y h
  apply homogeneousHomology_injective (k := k) B a i
  apply (coefficientTorIso (k := k) B i).symm.toLinearEquiv.injective
  exact h

/-- The standard degree component, as a genuine submodule of derived Tor. -/
def gradedTor (B : Family V) (a : Exponent V) (i : ℕ) :
    Submodule k ((ModuleCat.restrictScalars (algebraMap k (MvPolynomial V k))).obj
      (finitePolynomialTor i (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B)))) :=
  LinearMap.range (toDerivedTor (k := k) B a i).hom

/-- Every homogeneous Koszul homology group is isomorphic to its actual derived-Tor component. -/
def gradedTorIso (B : Family V) (a : Exponent V) (i : ℕ) :
    (homogeneousComplex (k := k) B a).homology i ≅ ModuleCat.of k (gradedTor (k := k) B a i) :=
  (LinearEquiv.ofInjective (toDerivedTor (k := k) B a i).hom (toDerivedTor_injective (k := k) B a i)).toModuleIso

/-- Nonzero multigraded Betti support defined using genuine derived Tor. -/
def GradedBettiNonzero (B : Family V) (a : Exponent V) (i : ℕ) : Prop :=
  ¬ IsZero (ModuleCat.of k (gradedTor (k := k) B a i))

lemma gradedBettiNonzero_iff_faces (B : Family V) (a : Exponent V) (i : ℕ) :
    GradedBettiNonzero (k := k) B a i ↔
      Simplicial.NonzeroHomology (k := k) (koszulFaces B a) i := by
  unfold GradedBettiNonzero
  rw [← (gradedTorIso (k := k) B a i).isZero_iff, homogeneous_homology_nonzero_iff]

/-- The homological shift ideal, generated by precisely the nonzero genuine Tor multidegrees. -/
def homologicalShift (B : Family V) (i : ℕ) : Ideal (MvPolynomial V k) :=
  Ideal.span ((fun a : Exponent V => MvPolynomial.monomial a (1 : k)) ''
    {a | GradedBettiNonzero (k := k) B a i})

end CommAlg.Koszul

end
end CheckedSource30

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "31: CommAlg.Polymatroid.RankFunction\n"

/-! ## Source: CommAlg.Polymatroid.RankFunction -/
section CheckedSource31

/-! # Integral polymatroid rank functions

The fields are precisely normalization, monotonicity and submodularity of an
ordinary nonnegative integer-valued function on subsets.  No exchange or
homological conclusion is included in the definition.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [DecidableEq V]

structure RankFunction (V : Type*) [DecidableEq V] where
  toFun : Finset V → ℕ
  empty : toFun ∅ = 0
  monotone : Monotone toFun
  submodular : ∀ A B, toFun (A ∪ B) + toFun (A ∩ B) ≤ toFun A + toFun B

instance : CoeFun (RankFunction V) (fun _ => Finset V → ℕ) := ⟨RankFunction.toFun⟩

@[simp] theorem RankFunction.map_empty (g : RankFunction V) : g ∅ = 0 := g.empty

def RankFunction.Active (g : RankFunction V) : Prop :=
  ∀ A, A.Nonempty → 1 ≤ g A

/-- Additive formulation of the inequality between all marginal increments. -/
def RankFunction.Dominates (u g : RankFunction V) : Prop :=
  ∀ A B, A ⊆ B → g B + u A ≤ u B + g A

theorem RankFunction.le_of_dominates {u g : RankFunction V}
    (h : u.Dominates g) (A : Finset V) : g A ≤ u A := by
  simpa using h ∅ A (empty_subset A)

theorem RankFunction.mixed_submodular {u g : RankFunction V}
    (h : u.Dominates g) (A B : Finset V) :
    g (A ∪ B) + u (A ∩ B) ≤ g A + u B := by
  have hg := g.submodular A B
  have hi := h (A ∩ B) B inter_subset_right
  omega

def RankFunction.add (g u : RankFunction V) : RankFunction V where
  toFun A := g A + u A
  empty := by simp
  monotone := fun A B h => Nat.add_le_add (g.monotone h) (u.monotone h)
  submodular A B := by
    have hg := g.submodular A B
    have hu := u.submodular A B
    omega

def RankFunction.scale (s : ℕ) (g : RankFunction V) : RankFunction V where
  toFun A := s * g A
  empty := by simp
  monotone := fun A B h => Nat.mul_le_mul_left s (g.monotone h)
  submodular A B := by
    simpa only [Nat.mul_add] using Nat.mul_le_mul_left s (g.submodular A B)

end CommAlg.Polymatroid

end
end CheckedSource31

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "32: CommAlg.Polymatroid.DilworthBasic\n"

/-! ## Source: CommAlg.Polymatroid.DilworthBasic -/
section CheckedSource32

/-! # The actual partition minimum in the homological rank formula -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def partitionCost (g : Finset V → ℕ) {A : Finset V} (P : Finpartition A) : ℕ :=
  ∑ B ∈ P.parts, (g B - 1)

/-- Minimum over all partitions of `A` into nonempty blocks. -/
def partitionRank (g : Finset V → ℕ) (A : Finset V) : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty (fun P : Finpartition A => partitionCost g P)

theorem partitionRank_le (g : Finset V → ℕ) {A : Finset V} (P : Finpartition A) :
    partitionRank g A ≤ partitionCost g P :=
  Finset.inf'_le _ (Finset.mem_univ P)

theorem le_partitionRank (g : Finset V → ℕ) (A : Finset V) (n : ℕ)
    (h : ∀ P : Finpartition A, n ≤ partitionCost g P) : n ≤ partitionRank g A :=
  Finset.le_inf' _ _ (fun P _ => h P)

theorem partitionRank_attained (g : Finset V → ℕ) (A : Finset V) :
    ∃ P : Finpartition A, partitionCost g P = partitionRank g A := by
  obtain ⟨P, _, hP⟩ := (Finset.inf'_le_iff Finset.univ_nonempty).mp
    (le_rfl : partitionRank g A ≤ partitionRank g A)
  exact ⟨P, le_antisymm hP (partitionRank_le g P)⟩

@[simp] theorem partitionRank_empty (g : Finset V → ℕ) : partitionRank g ∅ = 0 := by
  apply Nat.eq_zero_of_le_zero
  simpa [partitionCost] using partitionRank_le g (Finpartition.empty (Finset V))

theorem partitionRank_le_single (g : Finset V → ℕ) {A : Finset V}
    (hA : A.Nonempty) : partitionRank g A ≤ g A - 1 := by
  simpa [partitionCost] using partitionRank_le g (Finpartition.indiscrete hA.ne_empty)

def augmentedPartitionRank (g : Finset V → ℕ) (A : Finset V) : ℕ :=
  A.card + partitionRank g A

@[simp] theorem augmentedPartitionRank_empty (g : Finset V → ℕ) :
    augmentedPartitionRank g ∅ = 0 := by simp [augmentedPartitionRank]

end CommAlg.Polymatroid

end
end CheckedSource32

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "33: CommAlg.Polymatroid.DilworthMarginal\n"

/-! ## Source: CommAlg.Polymatroid.DilworthMarginal -/
section CheckedSource33

/-!
# Monotonicity and marginal domination of the partition rank

The partition minimum is restricted to a smaller set by intersecting every
block with that set. The augmented block cost absorbs the unit lost when an
intersection is empty. Submodularity then bounds the total marginal increase
by the sum of the block marginal increases.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Restriction of an optimal partition proves monotonicity of the actual
partition minimum. Positivity on nonempty sets is not needed here. -/
theorem partitionRank_mono (g : RankFunction V) : Monotone (partitionRank g) := by
  intro A B hAB
  obtain ⟨P, hP⟩ := partitionRank_attained g B
  calc
    partitionRank g A ≤ partitionCost g (P.restrict hAB) := partitionRank_le g _
    _ = ∑ C ∈ P.parts, (g (C ∩ A) - 1) := by
      exact P.sum_restrict hAB (fun C => g C - 1) (by simp)
    _ ≤ partitionCost g P := by
      apply Finset.sum_le_sum
      intro C hC
      exact Nat.sub_le_sub_right (g.monotone Finset.inter_subset_left) 1
    _ = partitionRank g B := hP

theorem augmentedPartitionRank_mono (g : RankFunction V) :
    Monotone (augmentedPartitionRank g) := by
  intro A B hAB
  exact Nat.add_le_add (Finset.card_le_card hAB) (partitionRank_mono g hAB)

omit [Fintype V] in
/-- Adding a finite family of sets successively bounds the total rank increase
by the sum of their increases over their intersections with the initial set.
No disjointness assumption on the family is necessary. -/
theorem RankFunction.biUnion_marginal (g : RankFunction V) (A : Finset V)
    (S : Finset (Finset V)) :
    g (A ∪ S.biUnion id) + ∑ C ∈ S, g (C ∩ A) ≤ g A + ∑ C ∈ S, g C := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert C S hCS ih =>
    have hs := g.submodular (A ∪ S.biUnion id) C
    have hm : g (C ∩ A) ≤ g ((A ∪ S.biUnion id) ∩ C) := by
      apply g.monotone
      intro x hx
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mp hx).2),
          (Finset.mem_inter.mp hx).1⟩
    have hu : A ∪ (C ∪ S.biUnion id) = (A ∪ S.biUnion id) ∪ C := by
      ext x
      simp only [Finset.mem_union]
      tauto
    simp only [Finset.biUnion_insert, id_eq, Finset.sum_insert hCS]
    rw [hu]
    omega

omit [Fintype V] in
theorem RankFunction.partition_marginal (g : RankFunction V)
    {A B : Finset V} (hAB : A ⊆ B) (P : Finpartition B) :
    g B + ∑ C ∈ P.parts, g (C ∩ A) ≤ g A + ∑ C ∈ P.parts, g C := by
  simpa only [P.biUnion_parts, Finset.union_eq_right.mpr hAB] using
    g.biUnion_marginal A P.parts

omit [Fintype V] in
/-- The cardinality part of an augmented block cost compensates for its
missing unit when restriction removes a whole block. -/
theorem augmentedBlockCost_marginal (g : RankFunction V) (hg : g.Active)
    (A C : Finset V) (hC : C.Nonempty) :
    g C + ((C ∩ A).card + (g (C ∩ A) - 1)) ≤
      (C.card + (g C - 1)) + g (C ∩ A) := by
  have hCard : (C ∩ A).card ≤ C.card := Finset.card_le_card Finset.inter_subset_left
  have hGC := hg C hC
  by_cases hCA : (C ∩ A).Nonempty
  · have hGCA := hg (C ∩ A) hCA
    omega
  · have he : C ∩ A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hCA
    have hc := Finset.card_pos.mpr hC
    simp only [he, Finset.card_empty, RankFunction.map_empty, Nat.zero_sub,
      Nat.add_zero]
    omega

/-- Lemma 3.2's complete marginal inequality in additive form, avoiding any
ambiguity from truncated natural subtraction. -/
theorem augmentedPartitionRank_marginal (g : RankFunction V) (hg : g.Active)
    {A B : Finset V} (hAB : A ⊆ B) :
    g B + augmentedPartitionRank g A ≤ augmentedPartitionRank g B + g A := by
  obtain ⟨P, hP⟩ := partitionRank_attained g B
  have hRestricted : partitionRank g A ≤ ∑ C ∈ P.parts, (g (C ∩ A) - 1) := by
    calc
      partitionRank g A ≤ partitionCost g (P.restrict hAB) := partitionRank_le g _
      _ = _ := P.sum_restrict hAB (fun C => g C - 1) (by simp)
  have hCards : ∑ C ∈ P.parts, (C ∩ A).card = A.card := by
    exact (P.sum_restrict hAB (fun C => C.card) (by simp)).symm.trans
      (P.restrict hAB).sum_card_parts
  have hLower : augmentedPartitionRank g A ≤
      ∑ C ∈ P.parts, ((C ∩ A).card + (g (C ∩ A) - 1)) := by
    rw [Finset.sum_add_distrib, hCards]
    exact Nat.add_le_add_left hRestricted A.card
  have hUpper : (∑ C ∈ P.parts, (C.card + (g C - 1))) =
      augmentedPartitionRank g B := by
    rw [Finset.sum_add_distrib, P.sum_card_parts]
    exact congrArg (fun n => B.card + n) hP
  have hBlocks : (∑ C ∈ P.parts, g C) +
      (∑ C ∈ P.parts, ((C ∩ A).card + (g (C ∩ A) - 1))) ≤
      (∑ C ∈ P.parts, (C.card + (g C - 1))) +
      (∑ C ∈ P.parts, g (C ∩ A)) := by
    simpa only [Finset.sum_add_distrib] using
      (Finset.sum_le_sum (s := P.parts) (fun C hC =>
        augmentedBlockCost_marginal g hg A C (P.nonempty_of_mem_parts hC)))
  have hRank := g.partition_marginal hAB P
  rw [hUpper] at hBlocks
  omega

end CommAlg.Polymatroid

end
end CheckedSource33

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "34: CommAlg.Polymatroid.DilworthSubmodular\n"

/-! ## Source: CommAlg.Polymatroid.DilworthSubmodular -/
section CheckedSource34

/-! # Submodularity of the partition minimum

We give a finite one-block uncrossing argument.  Intersecting a single new
block with the blocks of a partition gives a partition of the intersection;
merging those that meet it gives a partition of the union.  Induction over
the second partition yields the full submodular inequality.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem RankFunction.intersecting_cost_submodular (g : RankFunction V)
    (hg : g.Active) {A B : Finset V} (h : (A ∩ B).Nonempty) :
    (g (A ∪ B) - 1) + (g (A ∩ B) - 1) ≤ (g A - 1) + (g B - 1) := by
  have hI := hg (A ∩ B) h
  have hA := hg A (h.mono inter_subset_left)
  have hB := hg B (h.mono inter_subset_right)
  have hU := hg (A ∪ B) (h.mono (inter_subset_left.trans subset_union_left))
  have hs := g.submodular A B
  omega

theorem partitionRank_le_cover (g : RankFunction V) (S : Finset (Finset V))
    (hd : (S : Set (Finset V)).PairwiseDisjoint id) :
    partitionRank g (S.biUnion id) ≤ ∑ C ∈ S, (g C - 1) := by
  let P : Finpartition (S.biUnion id) :=
    Finpartition.ofErase S hd.supIndep (Finset.sup_eq_biUnion S id)
  have h := partitionRank_le g P
  have hs : partitionCost g P = ∑ C ∈ S, (g C - 1) := by
    change ∑ C ∈ S.erase ∅, (g C - 1) = ∑ C ∈ S, (g C - 1)
    exact Finset.sum_erase S (by simp)
  rwa [hs] at h

theorem partitionRank_disjoint_subadd (g : RankFunction V)
    {A B : Finset V} (hAB : Disjoint A B) :
    partitionRank g (A ∪ B) ≤ partitionRank g A + partitionRank g B := by
  obtain ⟨P, hP⟩ := partitionRank_attained g A
  obtain ⟨Q, hQ⟩ := partitionRank_attained g B
  have hcross : ∀ C ∈ P.parts, ∀ D ∈ Q.parts, Disjoint C D := by
    intro C hC D hD
    exact hAB.mono (P.subset hC) (Q.subset hD)
  have hd : ((P.parts ∪ Q.parts : Finset (Finset V)) : Set (Finset V)).PairwiseDisjoint id := by
    intro C hC D hD hne
    rcases mem_union.mp hC with hC | hC <;> rcases mem_union.mp hD with hD | hD
    · exact P.disjoint hC hD hne
    · exact hcross C hC D hD
    · exact (hcross D hD C hC).symm
    · exact Q.disjoint hC hD hne
  have hpq : Disjoint P.parts Q.parts := by
    apply Finset.disjoint_left.mpr
    intro C hC hD
    exact P.ne_empty hC (disjoint_self.mp (hcross C hC C hD))
  have h := partitionRank_le_cover g (P.parts ∪ Q.parts) hd
  rw [Finset.union_biUnion, P.biUnion_parts, Q.biUnion_parts, Finset.sum_union hpq] at h
  change partitionRank g (A ∪ B) ≤ partitionCost g P + partitionCost g Q at h
  simpa only [hP, hQ] using h

theorem RankFunction.merge_cost (g : RankFunction V) (hg : g.Active)
    (C : Finset V) (R : Finset (Finset V))
    (hd : (R : Set (Finset V)).PairwiseDisjoint id)
    (hm : ∀ S ∈ R, (S ∩ C).Nonempty) :
    (g (C ∪ R.biUnion id) - 1) + ∑ S ∈ R, (g (S ∩ C) - 1) ≤
      (g C - 1) + ∑ S ∈ R, (g S - 1) := by
  induction R using Finset.induction_on with
  | empty => simp
  | @insert S R hSR ih =>
    have hdR : (R : Set (Finset V)).PairwiseDisjoint id := by
      intro X hX Y hY hne
      exact hd (mem_insert_of_mem hX) (mem_insert_of_mem hY) hne
    have hmR : ∀ X ∈ R, (X ∩ C).Nonempty :=
      fun X hX => hm X (mem_insert_of_mem hX)
    have ih' := ih hdR hmR
    have hdis : Disjoint S (R.biUnion id) := by
      rw [Finset.disjoint_biUnion_right]
      intro X hX
      exact hd (mem_insert_self _ _) (mem_insert_of_mem hX) (fun heq => hSR (heq ▸ hX))
    have hi : S ∩ (C ∪ R.biUnion id) = S ∩ C := by
      ext x
      have hx : x ∈ S → x ∉ R.biUnion id := fun hx => Finset.disjoint_left.mp hdis hx
      simp only [mem_inter, mem_union]
      tauto
    have hsub := g.intersecting_cost_submodular hg
      (A := S) (B := C ∪ R.biUnion id) (by rw [hi]; exact hm S (mem_insert_self _ _))
    rw [hi] at hsub
    have hu : C ∪ (insert S R).biUnion id = S ∪ (C ∪ R.biUnion id) := by
      ext x
      simp only [mem_union, mem_biUnion, mem_insert, id_eq]
      aesop
    rw [hu, Finset.sum_insert hSR, Finset.sum_insert hSR]
    omega

theorem partitionRank_single_submodular (g : RankFunction V) (hg : g.Active)
    (A C : Finset V) :
    partitionRank g (A ∪ C) + partitionRank g (A ∩ C) ≤
      partitionRank g A + (g C - 1) := by
  by_cases hC : C = ∅
  · simp [hC]
  have hCne : C.Nonempty := Finset.nonempty_iff_ne_empty.mpr hC
  obtain ⟨P, hP⟩ := partitionRank_attained g A
  let R := P.parts.filter (fun S => (S ∩ C).Nonempty)
  let T := P.parts.filter (fun S => ¬ (S ∩ C).Nonempty)
  let U := C ∪ R.biUnion id
  have hRsub : R ⊆ P.parts := Finset.filter_subset _ _
  have hTsub : T ⊆ P.parts := Finset.filter_subset _ _
  have hdR : (R : Set (Finset V)).PairwiseDisjoint id := by
    intro S hS D hD hne
    exact P.disjoint (hRsub hS) (hRsub hD) hne
  have hmeet : ∀ S ∈ R, (S ∩ C).Nonempty := fun S hS => (mem_filter.mp hS).2
  have hmerge := g.merge_cost hg C R hdR hmeet
  have hTU : ∀ S ∈ T, Disjoint S U := by
    intro S hS
    have hSC : Disjoint S C := by
      exact Finset.disjoint_iff_inter_eq_empty.mpr
        (Finset.not_nonempty_iff_eq_empty.mp (mem_filter.mp hS).2)
    apply Finset.disjoint_union_right.mpr
    refine ⟨hSC, ?_⟩
    rw [Finset.disjoint_biUnion_right]
    intro D hD
    apply P.disjoint (hTsub hS) (hRsub hD)
    intro heq
    exact (mem_filter.mp hS).2 (heq ▸ hmeet D hD)
  have hUne : U.Nonempty := hCne.mono subset_union_left
  have hUT : U ∉ T := by
    intro h
    exact hUne.ne_empty (disjoint_self.mp (hTU U h))
  have hdU : ((insert U T : Finset (Finset V)) : Set (Finset V)).PairwiseDisjoint id := by
    intro S hS D hD hne
    rcases mem_insert.mp hS with rfl | hS <;> rcases mem_insert.mp hD with rfl | hD
    · exact (hne rfl).elim
    · exact (hTU D hD).symm
    · exact hTU S hS
    · exact P.disjoint (hTsub hS) (hTsub hD) hne
  have hcover : (insert U T).biUnion id = A ∪ C := by
    ext x
    constructor
    · intro hx
      obtain ⟨S, hS, hxS⟩ := mem_biUnion.mp hx
      rcases mem_insert.mp hS with rfl | hS
      · rcases mem_union.mp hxS with hxC | hxR
        · exact mem_union_right _ hxC
        · obtain ⟨D, hD, hxD⟩ := mem_biUnion.mp hxR
          exact mem_union_left _ (P.subset (hRsub hD) hxD)
      · exact mem_union_left _ (P.subset (hTsub hS) hxS)
    · intro hx
      rcases mem_union.mp hx with hxA | hxC
      · obtain ⟨S, hS, hxS⟩ := P.exists_mem hxA
        by_cases hm : (S ∩ C).Nonempty
        · exact mem_biUnion.mpr ⟨U, mem_insert_self _ _,
            mem_union_right _ (mem_biUnion.mpr ⟨S, mem_filter.mpr ⟨hS, hm⟩, hxS⟩)⟩
        · exact mem_biUnion.mpr ⟨S, mem_insert_of_mem (mem_filter.mpr ⟨hS, hm⟩), hxS⟩
      · exact mem_biUnion.mpr ⟨U, mem_insert_self _ _, mem_union_left _ hxC⟩
  have hUnion := partitionRank_le_cover g (insert U T) hdU
  rw [hcover, Finset.sum_insert hUT] at hUnion
  have hInter := partitionRank_le g (P.restrict (inter_subset_left : A ∩ C ⊆ A))
  have hrestrict : partitionCost g (P.restrict (inter_subset_left : A ∩ C ⊆ A)) =
      ∑ S ∈ R, (g (S ∩ C) - 1) := by
    unfold partitionCost
    rw [P.sum_restrict _ (fun S => g S - 1) (by simp)]
    calc
      (∑ S ∈ P.parts, (g (S ⊓ (A ∩ C)) - 1)) =
          ∑ S ∈ P.parts, (g (S ∩ C) - 1) := by
        apply Finset.sum_congr rfl
        intro S hS
        change g (S ∩ (A ∩ C)) - 1 = _
        rw [← Finset.inter_assoc, Finset.inter_eq_left.mpr (P.subset hS)]
      _ = ∑ S ∈ R, (g (S ∩ C) - 1) := by
        symm
        apply Finset.sum_subset hRsub
        intro S hS hn
        have hnot : ¬ (S ∩ C).Nonempty := fun hm => hn (mem_filter.mpr ⟨hS, hm⟩)
        rw [Finset.not_nonempty_iff_eq_empty.mp hnot]
        simp
  rw [hrestrict] at hInter
  have hcost : (∑ S ∈ R, (g S - 1)) + (∑ S ∈ T, (g S - 1)) =
      partitionCost g P :=
    Finset.sum_filter_add_sum_filter_not P.parts (fun S => (S ∩ C).Nonempty) _
  change (g U - 1) + _ ≤ _ at hmerge
  omega

theorem partitionRank_partition_submodular (g : RankFunction V) (hg : g.Active)
    (A : Finset V) (R : Finset (Finset V))
    (hd : (R : Set (Finset V)).PairwiseDisjoint id) :
    partitionRank g (A ∪ R.biUnion id) + partitionRank g (A ∩ R.biUnion id) ≤
      partitionRank g A + ∑ C ∈ R, (g C - 1) := by
  induction R using Finset.induction_on with
  | empty => simp
  | @insert C R hCR ih =>
    have hdR : (R : Set (Finset V)).PairwiseDisjoint id := by
      intro S hS T hT hne
      exact hd (mem_insert_of_mem hS) (mem_insert_of_mem hT) hne
    have hdis : Disjoint C (R.biUnion id) := by
      rw [Finset.disjoint_biUnion_right]
      intro S hS
      exact hd (mem_insert_self _ _) (mem_insert_of_mem hS) (fun h => hCR (h ▸ hS))
    have ih' := ih hdR
    have hsingle := partitionRank_single_submodular g hg (A ∪ R.biUnion id) C
    have hsmall : (A ∪ R.biUnion id) ∩ C = A ∩ C := by
      rw [Finset.union_inter_distrib_right,
        Finset.disjoint_iff_inter_eq_empty.mp hdis.symm, Finset.union_empty]
    rw [hsmall] at hsingle
    have hinter := partitionRank_disjoint_subadd g
      (hdis.mono inter_subset_right inter_subset_right :
        Disjoint (A ∩ C) (A ∩ R.biUnion id))
    have hu : A ∪ (insert C R).biUnion id = (A ∪ R.biUnion id) ∪ C := by
      simp only [Finset.biUnion_insert, id_eq]
      ac_rfl
    have hi : A ∩ (insert C R).biUnion id = (A ∩ C) ∪ (A ∩ R.biUnion id) := by
      simp only [Finset.biUnion_insert, id_eq, Finset.inter_union_distrib_left]
    rw [hu, hi, Finset.sum_insert hCR]
    omega

/-- The exact set-partition minimum is submodular in every finite ground set. -/
theorem partitionRank_submodular (g : RankFunction V) (hg : g.Active) (A B : Finset V) :
    partitionRank g (A ∪ B) + partitionRank g (A ∩ B) ≤
      partitionRank g A + partitionRank g B := by
  obtain ⟨P, hP⟩ := partitionRank_attained g B
  have h := partitionRank_partition_submodular g hg A P.parts P.disjoint
  rw [P.biUnion_parts] at h
  change _ ≤ partitionRank g A + partitionCost g P at h
  rwa [hP] at h

end CommAlg.Polymatroid

end
end CheckedSource34

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "35: CommAlg.Polymatroid.RankInterpolation\n"

/-! ## Source: CommAlg.Polymatroid.RankInterpolation -/
section CheckedSource35

/-! # Rank interpolation under domination of marginal increments -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [DecidableEq V]

def shiftRankValue (g u : RankFunction V) (i : ℕ) (A : Finset V) : ℕ :=
  if A = ∅ then 0 else min (g A + i) (u A)

@[simp] theorem shiftRankValue_empty (g u : RankFunction V) (i : ℕ) :
    shiftRankValue g u i ∅ = 0 := by simp [shiftRankValue]

theorem shiftRankValue_le_u (g u : RankFunction V) (i : ℕ) (A : Finset V) :
    shiftRankValue g u i A ≤ u A := by
  unfold shiftRankValue
  split_ifs
  · exact Nat.zero_le _
  · exact min_le_right _ _

theorem shiftRankValue_le_add (g u : RankFunction V) (i : ℕ) (A : Finset V) :
    shiftRankValue g u i A ≤ g A + i := by
  unfold shiftRankValue
  split_ifs
  · exact Nat.zero_le _
  · exact min_le_left _ _

/-- Lemma 3.3, first interpolation, with exactly its marginal hypothesis. -/
def RankFunction.interpolate (g u : RankFunction V) (h : u.Dominates g)
    (i : ℕ) : RankFunction V where
  toFun := shiftRankValue g u i
  empty := shiftRankValue_empty g u i
  monotone := by
    intro A B hAB
    by_cases hA : A = ∅
    · simp [hA]
    have hB : B ≠ ∅ := by
      intro heq
      apply hA
      simpa [heq] using hAB
    simp only [shiftRankValue, if_neg hA, if_neg hB]
    exact min_le_min (Nat.add_le_add_right (g.monotone hAB) i) (u.monotone hAB)
  submodular := by
    intro A B
    by_cases hA : A = ∅
    · simp [hA]
    by_cases hB : B = ∅
    · simp [hB]
    have hUg := shiftRankValue_le_add g u i (A ∪ B)
    have hIg := shiftRankValue_le_add g u i (A ∩ B)
    have hUu := shiftRankValue_le_u g u i (A ∪ B)
    have hIu := shiftRankValue_le_u g u i (A ∩ B)
    have hg := g.submodular A B
    have hu := u.submodular A B
    have hm := RankFunction.mixed_submodular h A B
    have hm' := RankFunction.mixed_submodular h B A
    rw [Finset.union_comm B A, Finset.inter_comm B A] at hm'
    rcases le_total (g A + i) (u A) with ha | ha <;>
      rcases le_total (g B + i) (u B) with hb | hb
    · have hAv : shiftRankValue g u i A = g A + i := by
        simp [shiftRankValue, hA, min_eq_left ha]
      have hBv : shiftRankValue g u i B = g B + i := by
        simp [shiftRankValue, hB, min_eq_left hb]
      rw [hAv, hBv]
      omega
    · have hAv : shiftRankValue g u i A = g A + i := by
        simp [shiftRankValue, hA, min_eq_left ha]
      have hBv : shiftRankValue g u i B = u B := by
        simp [shiftRankValue, hB, min_eq_right hb]
      rw [hAv, hBv]
      omega
    · have hAv : shiftRankValue g u i A = u A := by
        simp [shiftRankValue, hA, min_eq_right ha]
      have hBv : shiftRankValue g u i B = g B + i := by
        simp [shiftRankValue, hB, min_eq_left hb]
      rw [hAv, hBv]
      omega
    · have hAv : shiftRankValue g u i A = u A := by
        simp [shiftRankValue, hA, min_eq_right ha]
      have hBv : shiftRankValue g u i B = u B := by
        simp [shiftRankValue, hB, min_eq_right hb]
      rw [hAv, hBv]
      omega

@[simp] theorem RankFunction.interpolate_apply (g u : RankFunction V)
    (h : u.Dominates g) (i : ℕ) (A : Finset V) :
    g.interpolate u h i A = shiftRankValue g u i A := rfl

end CommAlg.Polymatroid

end
end CheckedSource35

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "36: CommAlg.Polymatroid.Dilworth\n"

/-! ## Source: CommAlg.Polymatroid.Dilworth -/
section CheckedSource36

/-! # The partition rank and homological-rank interpolation

This file completes Lemma 3.2 and the first part of Lemma 3.3 of
`Rank formulas for homological shifts of polymatroidal ideals`.
The homological interpretation itself is established in the Tor comparison
files; this module makes only its stated combinatorial claims.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The exact Dilworth partition minimum, as a proved polymatroid rank. -/
def dilworthRank (g : RankFunction V) (hg : g.Active) : RankFunction V where
  toFun := partitionRank g
  empty := partitionRank_empty g
  monotone := partitionRank_mono g
  submodular := partitionRank_submodular g hg

/-- The augmented partition rank `u_g(A)=|A|+D_g(A)`. -/
def augmentedRank (g : RankFunction V) (hg : g.Active) : RankFunction V where
  toFun := augmentedPartitionRank g
  empty := augmentedPartitionRank_empty g
  monotone := augmentedPartitionRank_mono g
  submodular A B := by
    have h := partitionRank_submodular g hg A B
    have hc := Finset.card_union_add_card_inter A B
    unfold augmentedPartitionRank
    omega

theorem augmentedRank_dominates (g : RankFunction V) (hg : g.Active) :
    (augmentedRank g hg).Dominates g :=
  fun A B hAB => augmentedPartitionRank_marginal g hg hAB

/-- The rank function in Theorem 1.2, before identifying its bases with Tor support. -/
def homologicalRank (g : RankFunction V) (hg : g.Active) (i : ℕ) : RankFunction V :=
  g.interpolate (augmentedRank g hg) (augmentedRank_dominates g hg) i

@[simp] theorem homologicalRank_empty (g : RankFunction V) (hg : g.Active) (i : ℕ) :
    homologicalRank g hg i ∅ = 0 := RankFunction.map_empty _

theorem homologicalRank_apply (g : RankFunction V) (hg : g.Active) (i : ℕ)
    {A : Finset V} (hA : A.Nonempty) :
    homologicalRank g hg i A = min (g A + i) (A.card + partitionRank g A) := by
  simp [homologicalRank, RankFunction.interpolate_apply, shiftRankValue, hA.ne_empty,
    augmentedRank, augmentedPartitionRank]

theorem sum_subsetSum_partition (a : Exponent V) {A : Finset V} (P : Finpartition A) :
    ∑ C ∈ P.parts, subsetSum a C = subsetSum a A := by
  unfold subsetSum
  calc
    (∑ C ∈ P.parts, ∑ i ∈ C, a i) = ∑ i ∈ P.parts.biUnion id, a i :=
      (Finset.sum_biUnion P.disjoint).symm
    _ = ∑ i ∈ A, a i := congrArg (fun S => ∑ i ∈ S, a i) P.biUnion_parts

/-- Additive exponents satisfy the nonempty-set bounds exactly when they
satisfy all bounds from the actual partition minimum. -/
theorem nonempty_bounds_iff_partition_bounds (g : RankFunction V) (a : Exponent V) :
    (∀ A, A.Nonempty → subsetSum a A ≤ g A - 1) ↔
      (∀ A, subsetSum a A ≤ partitionRank g A) := by
  constructor
  · intro h A
    apply le_partitionRank g A
    intro P
    rw [← sum_subsetSum_partition a P]
    exact Finset.sum_le_sum (fun C hC => h C (P.nonempty_of_mem_parts hC))
  · intro h A hA
    exact (h A).trans (partitionRank_le_single g hA)

end CommAlg.Polymatroid

end
end CheckedSource36

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "37: CommAlg.Polymatroid.TrimBounds\n"

/-! ## Source: CommAlg.Polymatroid.TrimBounds -/
section CheckedSource37

/-! # Removing the first copy of each supported variable

These are the exact exponent inequalities (3.3)--(3.6), including arbitrary
zero coordinates.  The support is the actual support of the exponent vector.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def supportPred (a : Exponent V) : Exponent V :=
  a.mapRange (fun n => n - 1) (by simp)

@[simp] theorem supportPred_apply (a : Exponent V) (j : V) :
    supportPred a j = a j - 1 := rfl

theorem supportPred_add_support (a : Exponent V) (j : V) :
    supportPred a j + (if j ∈ a.support then 1 else 0) = a j := by
  simp only [supportPred_apply, Finsupp.mem_support_iff]
  split_ifs <;> omega

theorem subsetSum_supportPred (a : Exponent V) (A : Finset V) :
    subsetSum (supportPred a) A + (A ∩ a.support).card = subsetSum a A := by
  have h := Finset.sum_congr (s₁ := A) (s₂ := A) rfl
    (fun j _ => supportPred_add_support a j)
  simpa only [Finset.sum_add_distrib, Finset.sum_boole, Finset.filter_mem_eq_inter,
    Nat.cast_id, subsetSum] using h

theorem subsetSum_support_inter (a : Exponent V) (A : Finset V) :
    subsetSum a (A ∩ a.support) = subsetSum a A := by
  apply Finset.sum_subset inter_subset_left
  intro j hjA hj
  have hn : j ∉ a.support := fun h => hj (mem_inter.mpr ⟨hjA, h⟩)
  exact Finsupp.notMem_support_iff.mp hn

theorem subsetSum_supportPred_inter (a : Exponent V) (A : Finset V) :
    subsetSum (supportPred a) (A ∩ a.support) = subsetSum (supportPred a) A := by
  apply Finset.sum_subset inter_subset_left
  intro j hjA hj
  have hn : j ∉ a.support := fun h => hj (mem_inter.mpr ⟨hjA, h⟩)
  simp [Finsupp.notMem_support_iff.mp hn]

theorem supportPred_bounds_iff_augmented (g : RankFunction V) (a : Exponent V) :
    (∀ A, subsetSum (supportPred a) A ≤ partitionRank g A) ↔
      (∀ A, subsetSum a A ≤ augmentedPartitionRank g A) := by
  constructor
  · intro h A
    have heq := subsetSum_supportPred a A
    have hc := Finset.card_le_card (inter_subset_left : A ∩ a.support ⊆ A)
    have hb := h A
    unfold augmentedPartitionRank
    omega
  · intro h A
    have hb := h (A ∩ a.support)
    have heq := subsetSum_supportPred a (A ∩ a.support)
    rw [Finset.inter_eq_left.mpr inter_subset_right, subsetSum_supportPred_inter] at heq
    have hm := partitionRank_mono g (inter_subset_left : A ∩ a.support ⊆ A)
    unfold augmentedPartitionRank at hb
    omega

/-- Exact equivalence of (3.3) and (3.6) in the paper. -/
theorem supportPred_nonempty_bounds_iff_augmented (g : RankFunction V) (a : Exponent V) :
    (∀ A, A.Nonempty → subsetSum (supportPred a) A ≤ g A - 1) ↔
      (∀ A, subsetSum a A ≤ augmentedPartitionRank g A) :=
  (nonempty_bounds_iff_partition_bounds g (supportPred a)).trans
    (supportPred_bounds_iff_augmented g a)

end CommAlg.Polymatroid

end
end CheckedSource37

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "38: CommAlg.Polymatroid.Localization\n"

/-! ## Source: CommAlg.Polymatroid.Localization -/
section CheckedSource38

/-! # Minimal projected generators and local subset minima -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def minimalFamily (B : Family V) : Family V :=
  B.filter (fun a => ∀ b ∈ B, b ≤ a → b = a)

@[simp] theorem mem_minimalFamily {B : Family V} {a : Exponent V} :
    a ∈ minimalFamily B ↔ a ∈ B ∧ ∀ b ∈ B, b ≤ a → b = a := by
  simp [minimalFamily]

theorem minimalFamily_subset (B : Family V) : minimalFamily B ⊆ B := by
  intro a ha
  exact (mem_minimalFamily.mp ha).1

theorem minimal_below {B : Family V} {a : Exponent V} (ha : a ∈ B) :
    ∃ b ∈ minimalFamily B, b ≤ a := by
  obtain ⟨b, hba, hb, hmin⟩ := B.exists_le_minimal ha
  exact ⟨b, mem_minimalFamily.mpr ⟨hb, fun c hc hcb => le_antisymm hcb (hmin hc hcb)⟩, hba⟩

theorem minimalFamily_nonempty {B : Family V} (hB : B.Nonempty) :
    (minimalFamily B).Nonempty := by
  obtain ⟨a, ha⟩ := hB
  obtain ⟨b, hb, _⟩ := minimal_below ha
  exact ⟨b, hb⟩

theorem minimalFamily_antichain (B : Family V) : Antichain (minimalFamily B) := by
  intro a ha b hb hab
  exact (mem_minimalFamily.mp hb).2 a ((mem_minimalFamily.mp ha).1) hab

theorem contains_minimalFamily (B : Family V) (a : Exponent V) :
    Contains (minimalFamily B) a ↔ Contains B a := by
  constructor
  · rintro ⟨b, hb, hba⟩
    exact ⟨b, minimalFamily_subset B hb, hba⟩
  · rintro ⟨b, hb, hba⟩
    obtain ⟨c, hc, hcb⟩ := minimal_below hb
    exact ⟨c, hc, hcb.trans hba⟩

theorem minimalFamily_eq {B : Family V} (hB : Antichain B) : minimalFamily B = B := by
  ext a
  simp only [mem_minimalFamily]
  exact ⟨And.left, fun ha => ⟨ha, fun b hb hba => hB b hb a ha hba⟩⟩

theorem monomialIdeal_minimalFamily (k : Type*) [CommSemiring k] (B : Family V) :
    monomialIdeal k (minimalFamily B) = monomialIdeal k B := by
  ext f
  simp only [mem_monomialIdeal_iff, contains_minimalFamily]

def project (U : Finset V) (a : Exponent V) : Exponent V := a.filter (· ∈ U)

@[simp] theorem project_apply (U : Finset V) (a : Exponent V) (i : V) :
    project U a i = if i ∈ U then a i else 0 := rfl

theorem project_le (U : Finset V) (a : Exponent V) : project U a ≤ a := by
  intro i
  simp only [project_apply]
  split <;> omega

theorem project_mono (U : Finset V) {a b : Exponent V} (hab : a ≤ b) :
    project U a ≤ project U b := by
  intro i
  simp only [project_apply]
  split
  · exact hab i
  · exact le_rfl

theorem project_project {U W : Finset V} (hWU : W ⊆ U) (a : Exponent V) :
    project W (project U a) = project W a := by
  ext i
  by_cases hiW : i ∈ W
  · simp [hiW, hWU hiW]
  · simp [hiW]

@[simp] theorem project_univ (a : Exponent V) : project Finset.univ a = a := by
  ext i
  simp

@[simp] theorem project_empty (a : Exponent V) : project ∅ a = 0 := by
  ext i
  simp

theorem subsetSum_project {U W : Finset V} (hWU : W ⊆ U) (a : Exponent V) :
    subsetSum (project U a) W = subsetSum a W := by
  apply Finset.sum_congr rfl
  intro i hi
  simp [hWU hi]

theorem degree_project (U : Finset V) (a : Exponent V) :
    (project U a).degree = subsetSum a U := by
  rw [Finsupp.degree_eq_sum]
  simp only [project_apply, ← Finset.sum_filter]
  simp [subsetSum]

def localize (B : Family V) (U : Finset V) : Family V :=
  minimalFamily (B.image (project U))

theorem localize_nonempty {B : Family V} (hB : B.Nonempty) (U : Finset V) :
    (localize B U).Nonempty := minimalFamily_nonempty (hB.image _)

theorem localize_antichain (B : Family V) (U : Finset V) : Antichain (localize B U) :=
  minimalFamily_antichain _

theorem localize_member {B : Family V} {U : Finset V} {b : Exponent V}
    (hb : b ∈ localize B U) : ∃ a ∈ B, project U a = b :=
  Finset.mem_image.mp (minimalFamily_subset _ hb)

theorem localize_supported {B : Family V} {U : Finset V} {b : Exponent V}
    (hb : b ∈ localize B U) : project U b = b := by
  obtain ⟨a, ha, rfl⟩ := localize_member hb
  exact project_project le_rfl a

theorem localize_below {B : Family V} {U : Finset V} {a : Exponent V}
    (ha : a ∈ B) : ∃ b ∈ localize B U, b ≤ project U a :=
  minimal_below (Finset.mem_image.mpr ⟨a, ha, rfl⟩)

theorem contains_localize (B : Family V) (U : Finset V) (a : Exponent V) :
    Contains (localize B U) a ↔ ∃ b ∈ B, project U b ≤ a := by
  rw [localize, contains_minimalFamily]
  simp [Contains]

def lowerRank (B : Family V) (U : Finset V) : ℕ :=
  if h : B.Nonempty then B.inf' h (fun a => subsetSum a U) else 0

theorem lowerRank_le {B : Family V} {a : Exponent V} (ha : a ∈ B) (U : Finset V) :
    lowerRank B U ≤ subsetSum a U := by
  rw [lowerRank, dif_pos ⟨a, ha⟩]
  exact Finset.inf'_le _ ha

theorem lowerRank_attained {B : Family V} (hB : B.Nonempty) (U : Finset V) :
    ∃ a ∈ B, subsetSum a U = lowerRank B U := by
  obtain ⟨a, ha, hle⟩ := (Finset.inf'_le_iff hB).mp
    (le_rfl : B.inf' hB (fun a => subsetSum a U) ≤ B.inf' hB (fun a => subsetSum a U))
  exact ⟨a, ha, le_antisymm (by simpa [lowerRank, hB] using hle) (lowerRank_le ha U)⟩

theorem le_lowerRank {B : Family V} (hB : B.Nonempty) {U : Finset V} {r : ℕ}
    (h : ∀ a ∈ B, r ≤ subsetSum a U) : r ≤ lowerRank B U := by
  rw [lowerRank, dif_pos hB]
  exact Finset.le_inf' hB _ h

@[simp] theorem lowerRank_empty (B : Family V) : lowerRank B ∅ = 0 := by
  unfold lowerRank
  split_ifs with h
  · obtain ⟨a, ha⟩ := h
    exact Nat.eq_zero_of_le_zero (by simpa using Finset.inf'_le (fun a => subsetSum a ∅) ha)
  · rfl

theorem lowerRank_mono {B : Family V} (hB : B.Nonempty) {U W : Finset V} (hUW : U ⊆ W) :
    lowerRank B U ≤ lowerRank B W := by
  apply le_lowerRank hB
  intro a ha
  exact (lowerRank_le ha U).trans (subsetSum_mono a hUW)

theorem localize_sum_ge {B : Family V} {U W : Finset V} (hWU : W ⊆ U)
    {b : Exponent V} (hb : b ∈ localize B U) : lowerRank B W ≤ subsetSum b W := by
  obtain ⟨a, ha, rfl⟩ := localize_member hb
  rw [subsetSum_project hWU]
  exact lowerRank_le ha W

/-- Projection and removal of redundant monomials preserve every subset minimum. -/
theorem lowerRank_localize {B : Family V} (hB : B.Nonempty)
    {U W : Finset V} (hWU : W ⊆ U) : lowerRank (localize B U) W = lowerRank B W := by
  apply le_antisymm
  · obtain ⟨a, ha, hmin⟩ := lowerRank_attained hB W
    obtain ⟨b, hb, hba⟩ := localize_below (U := U) ha
    calc
      lowerRank (localize B U) W ≤ subsetSum b W := lowerRank_le hb W
      _ ≤ subsetSum (project U a) W := Finset.sum_le_sum (fun i _ => hba i)
      _ = lowerRank B W := (subsetSum_project hWU a).trans hmin
  · exact le_lowerRank (localize_nonempty hB U) (fun b hb => localize_sum_ge hWU hb)

def LocallyEquigenerated (B : Family V) : Prop :=
  ∀ U : Finset V, ∃ d, Equigenerated (localize B U) d

theorem localize_degree {B : Family V} (hB : B.Nonempty) (hl : LocallyEquigenerated B)
    {U : Finset V} {b : Exponent V} (hb : b ∈ localize B U) : b.degree = lowerRank B U := by
  obtain ⟨d, hd⟩ := hl U
  obtain ⟨a, ha, hmin⟩ := lowerRank_attained (localize_nonempty hB U) U
  rw [lowerRank_localize hB le_rfl] at hmin
  have haD : a.degree = subsetSum a U := by
    rw [← degree_project, localize_supported ha]
  exact (hd b hb).trans ((hd a ha).symm.trans (haD.trans hmin))

def Supermodular (r : Finset V → ℕ) : Prop :=
  ∀ A B, r A + r B ≤ r (A ∪ B) + r (A ∩ B)

/-- Lemma 2.4: local equigeneration forces supermodularity. -/
theorem lowerRank_supermodular {B : Family V} (hB : B.Nonempty)
    (hl : LocallyEquigenerated B) : Supermodular (lowerRank B) := by
  intro A C
  obtain ⟨b, hb, hmin⟩ := lowerRank_attained (localize_nonempty hB (A ∪ C)) (A ∩ C)
  rw [lowerRank_localize hB (Finset.inter_subset_left.trans Finset.subset_union_left)] at hmin
  have hdeg := localize_degree hB hl hb
  have hsum : subsetSum b (A ∪ C) = lowerRank B (A ∪ C) := by
    rw [← degree_project, localize_supported hb]
    exact hdeg
  calc
    lowerRank B A + lowerRank B C ≤ subsetSum b A + subsetSum b C :=
      Nat.add_le_add (localize_sum_ge Finset.subset_union_left hb)
        (localize_sum_ge Finset.subset_union_right hb)
    _ = subsetSum b (A ∪ C) + subsetSum b (A ∩ C) := subsetSum_union_inter b A C
    _ = _ := by rw [hsum, hmin]

end CommAlg.Polymatroid

end
end CheckedSource38

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "39: CommAlg.Polymatroid.TightSets\n"

/-! ## Source: CommAlg.Polymatroid.TightSets -/
section CheckedSource39

/-! # Supermodular lower inequalities force the full exchange axiom -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def LowerFeasible (r : Finset V → ℕ) (a : Exponent V) : Prop :=
  ∀ U, r U ≤ subsetSum a U

def Tight (r : Finset V → ℕ) (a : Exponent V) (U : Finset V) : Prop :=
  subsetSum a U = r U

theorem tight_union_inter {r : Finset V → ℕ} (hr : Supermodular r)
    {a : Exponent V} (ha : LowerFeasible r a) {U W : Finset V}
    (hU : Tight r a U) (hW : Tight r a W) :
    Tight r a (U ∪ W) ∧ Tight r a (U ∩ W) := by
  have hsum := subsetSum_union_inter a U W
  have hsuper := hr U W
  have hfeasU := ha (U ∪ W)
  have hfeasW := ha (U ∩ W)
  unfold Tight at *
  omega

theorem subsetSum_exchange (a : Exponent V) (i j : V) (hi : 0 < a i) (U : Finset V) :
    subsetSum (exchange a i j) U + (if i ∈ U then 1 else 0) =
      subsetSum a U + (if j ∈ U then 1 else 0) := by
  have hle : Finsupp.single i 1 ≤ a := by
    intro h
    by_cases hh : h = i
    · subst h
      simpa using (show 1 ≤ a i by omega)
    · simp [Finsupp.single_apply, hh, Ne.symm hh]
  have he : exchange a i j + Finsupp.single i 1 = a + Finsupp.single j 1 := by
    unfold exchange
    rw [add_right_comm, tsub_add_cancel_of_le hle]
  have hs := congrArg (fun b : Exponent V => subsetSum b U) he
  simpa [subsetSum, Finset.sum_add_distrib, Finsupp.single_apply] using hs

theorem failed_exchange_tight {r : Finset V → ℕ} {a : Exponent V}
    (ha : LowerFeasible r a) {i j : V} (hi : 0 < a i)
    (hbad : ¬ LowerFeasible r (exchange a i j)) :
    ∃ U, Tight r a U ∧ i ∈ U ∧ j ∉ U := by
  simp only [LowerFeasible, not_forall, not_le] at hbad
  obtain ⟨U, hU⟩ := hbad
  have hfeas := ha U
  have hs := subsetSum_exchange a i j hi U
  have hiU : i ∈ U := by
    by_contra h
    rw [if_neg h] at hs
    split_ifs at hs <;> omega
  have hjU : j ∉ U := by
    intro h
    rw [if_pos hiU, if_pos h] at hs
    omega
  refine ⟨U, ?_, hiU, hjU⟩
  rw [if_pos hiU, if_neg hjU] at hs
  unfold Tight
  omega

theorem tight_avoiding {r : Finset V → ℕ} (hr : Supermodular r)
    {a : Exponent V} (ha : LowerFeasible r a) (i : V)
    (D : Finset V) (hD : D.Nonempty)
    (h : ∀ j ∈ D, ∃ U, Tight r a U ∧ i ∈ U ∧ j ∉ U) :
    ∃ C, Tight r a C ∧ i ∈ C ∧ ∀ j ∈ D, j ∉ C := by
  induction hD using Finset.Nonempty.cons_induction with
  | singleton j =>
    obtain ⟨U, hU, hi, hj⟩ := h j (Finset.mem_singleton_self _)
    exact ⟨U, hU, hi, by simpa using hj⟩
  | cons j D hj hD ih =>
    obtain ⟨C, hC, hiC, havoid⟩ := ih (fun q hq => h q (Finset.mem_cons.mpr (Or.inr hq)))
    obtain ⟨U, hU, hiU, hjU⟩ := h j (Finset.mem_cons.mpr (Or.inl rfl))
    refine ⟨C ∩ U, (tight_union_inter hr ha hC hU).2, Finset.mem_inter.mpr ⟨hiC, hiU⟩, ?_⟩
    intro q hq hqin
    rcases Finset.mem_cons.mp hq with rfl | hq
    · exact hjU (Finset.mem_inter.mp hqin).2
    · exact havoid q hq (Finset.mem_inter.mp hqin).1

/-- Full prescribed-donor exchange for all integer points of a fixed degree
satisfying supermodular lower inequalities. -/
theorem feasible_exchange {r : Finset V → ℕ} (hr : Supermodular r)
    {a b : Exponent V} (ha : LowerFeasible r a) (hb : LowerFeasible r b)
    (hdeg : a.degree = b.degree) {i : V} (hi : b i < a i) :
    ∃ j, a j < b j ∧ LowerFeasible r (exchange a i j) := by
  by_contra hbad
  push_neg at hbad
  let D : Finset V := Finset.univ.filter (fun j => a j < b j)
  have hD : D.Nonempty := by
    obtain ⟨j, hj⟩ := exists_surplus hdeg hi
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
  obtain ⟨C, hC, hiC, havoid⟩ := tight_avoiding hr ha i D hD (by
    intro j hj
    exact failed_exchange_tight ha (by omega) (hbad j (Finset.mem_filter.mp hj).2))
  have hle : ∀ j ∈ C, b j ≤ a j := by
    intro j hj
    by_contra h
    have hD' : j ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_univ j, by omega⟩
    exact havoid j hD' hj
  have hlt : subsetSum b C < subsetSum a C :=
    Finset.sum_lt_sum hle ⟨i, hiC, hi⟩
  have hfeas := hb C
  unfold Tight at hC
  omega

/-- Lemma 2.6, stated for a genuine monomial exponent ideal. -/
theorem polymatroidal_of_lower_inequalities {B : Family V} {d : ℕ}
    (hB : Equigenerated B d) {r : Finset V → ℕ} (hr : Supermodular r)
    (hrep : ∀ a, Contains B a ↔ LowerFeasible r a) : IsPolymatroidal B := by
  refine ⟨⟨d, hB⟩, ?_⟩
  intro a ha b hb i hi
  obtain ⟨j, hj, hex⟩ := feasible_exchange hr
    ((hrep a).mp ⟨a, ha, le_rfl⟩) ((hrep b).mp ⟨b, hb, le_rfl⟩)
    ((hB a ha).trans (hB b hb).symm) hi
  exact ⟨j, hj, (hB.mem_iff_contains ((exchange_degree a i j (by omega)).trans (hB a ha))).mpr
    ((hrep _).mpr hex)⟩

end CommAlg.Polymatroid

end
end CheckedSource39

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "40: CommAlg.Polymatroid.SocleReconstruction\n"

/-! ## Source: CommAlg.Polymatroid.SocleReconstruction -/
section CheckedSource40

/-! # Actual monomial socles recover the exponent ideal

A monomial socle element is an exponent outside the ideal which enters the
ideal after multiplication by each retained variable. This is the literal
monomial condition, not a surrogate exchange or rigidity property.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem Contains.mono {B : Family V} {a b : Exponent V}
    (ha : Contains B a) (hab : a ≤ b) : Contains B b := by
  obtain ⟨c, hc, hca⟩ := ha
  exact ⟨c, hc, hca.trans hab⟩

theorem project_add (U : Finset V) (a b : Exponent V) :
    project U (a + b) = project U a + project U b := by
  ext i
  by_cases hi : i ∈ U <;> simp [hi]

theorem project_single {U : Finset V} {i : V} (hi : i ∈ U) (k : ℕ) :
    project U (Finsupp.single i k) = Finsupp.single i k := by
  ext j
  by_cases hji : j = i
  · subst j
    simp [hi]
  · simp [Finsupp.single_apply, hji, Ne.symm hji]

/-- A bounded corner outside a monomial ideal lies below an actual socle monomial. -/
theorem exists_socle_above (B : Family V) (U : Finset V) (a : Exponent V)
    (hsupp : project U a = a) (hout : ¬ Contains B a)
    (hkill : ∀ i ∈ U, ∃ k : ℕ, Contains B (a + Finsupp.single i k)) :
    ∃ b, a ≤ b ∧ project U b = b ∧ ¬ Contains B b ∧
      ∀ i ∈ U, Contains B (b + Finsupp.single i 1) := by
  choose k hk using hkill
  let bound : Exponent V := Finsupp.equivFunOnFinite.symm
    (fun i => if hi : i ∈ U then a i + k i hi else 0)
  let T : Set (Exponent V) := {b | a ≤ b ∧ project U b = b ∧ ¬ Contains B b}
  have hbounded : T ⊆ Set.Iic bound := by
    intro b hb i
    change b i ≤ (if hi : i ∈ U then a i + k i hi else 0)
    by_cases hi : i ∈ U
    · rw [dif_pos hi]
      by_contra h
      apply hb.2.2
      apply (hk i hi).mono
      intro j
      by_cases hji : j = i
      · subst j
        simpa using (show a i + k i hi ≤ b i by omega)
      · simpa [Finsupp.single_apply, hji, Ne.symm hji] using hb.1 j
    · rw [dif_neg hi]
      have he := congrArg (fun c : Exponent V => c i) hb.2.1
      simpa [hi] using he.symm.le
  have hfinite : T.Finite := (Set.finite_Iic bound).subset hbounded
  obtain ⟨b, hb, hmax⟩ := hfinite.exists_maximal ⟨a, le_rfl, hsupp, hout⟩
  refine ⟨b, hb.1, hb.2.1, hb.2.2, ?_⟩
  intro i hi
  by_contra hout'
  have hb' : b + Finsupp.single i 1 ∈ T := by
    refine ⟨hb.1.trans (le_add_right le_rfl), ?_, hout'⟩
    rw [project_add, hb.2.1, project_single hi]
  have hle := hmax hb' (le_add_right le_rfl)
  have h := hle i
  simp at h

def LocalSocleDegrees (B : Family V) : Prop :=
  ∀ (U : Finset V) (a : Exponent V), project U a = a →
    ¬ Contains (localize B U) a →
    (∀ i ∈ U, Contains (localize B U) (a + Finsupp.single i 1)) →
    a.degree + 1 = lowerRank B U

theorem contains_project_empty {B : Family V} (hB : B.Nonempty) (a : Exponent V) :
    Contains (localize B ∅) (project ∅ a) := by
  rw [contains_localize]
  obtain ⟨b, hb⟩ := hB
  exact ⟨b, hb, by simp⟩

theorem contains_localize_univ (B : Family V) (a : Exponent V) :
    Contains (localize B Finset.univ) (project Finset.univ a) ↔ Contains B a := by
  rw [contains_localize]
  simp only [project_univ, Contains]

/-- Every missing monomial has a localization where it lies below a socle monomial. -/
theorem missing_local_socle {B : Family V} (hB : B.Nonempty) {a : Exponent V}
    (ha : ¬ Contains B a) :
    ∃ U : Finset V, U.Nonempty ∧ ∃ b : Exponent V,
      project U a ≤ b ∧ project U b = b ∧ ¬ Contains (localize B U) b ∧
        ∀ i ∈ U, Contains (localize B U) (b + Finsupp.single i 1) := by
  let bad : Finset (Finset V) := Finset.univ.filter
    (fun U => ¬ Contains (localize B U) (project U a))
  have hbad : bad.Nonempty := by
    refine ⟨Finset.univ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rwa [contains_localize_univ]
  obtain ⟨U, hU, hmin⟩ := bad.exists_minimal hbad
  have hout : ¬ Contains (localize B U) (project U a) := (Finset.mem_filter.mp hU).2
  have hUne : U.Nonempty := by
    by_contra h
    have he : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    subst U
    exact hout (contains_project_empty hB a)
  have hgood : ∀ i ∈ U, Contains (localize B (U.erase i)) (project (U.erase i) a) := by
    intro i hi
    by_contra h
    have hmem : U.erase i ∈ bad := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    have hsub := hmin hmem (Finset.erase_subset i U)
    exact Finset.notMem_erase i U (hsub hi)
  have hkill : ∀ i ∈ U, ∃ k : ℕ,
      Contains (localize B U) (project U a + Finsupp.single i k) := by
    intro i hi
    obtain ⟨b, hb, hba⟩ := (contains_localize B (U.erase i) _).mp (hgood i hi)
    refine ⟨b i, (contains_localize B U _).mpr ⟨b, hb, ?_⟩⟩
    intro j
    by_cases hji : j = i
    · subst j
      simp [hi]
    · by_cases hjU : j ∈ U
      · have h := hba j
        have hjerase : j ∈ U.erase i := Finset.mem_erase.mpr ⟨hji, hjU⟩
        simpa [hjerase, hjU, Finsupp.single_apply, hji, Ne.symm hji] using h
      · simp [hjU, Finsupp.single_apply, hji, Ne.symm hji]
  obtain ⟨b, hab, hbsupp, hbout, hbsoc⟩ := exists_socle_above (localize B U) U
    (project U a) (project_project le_rfl a) hout hkill
  exact ⟨U, hUne, b, hab, hbsupp, hbout, hbsoc⟩

/-- Lemma 2.5: all local monomial socle degrees recover every monomial of the ideal. -/
theorem contains_iff_lowerFeasible {B : Family V} (hB : B.Nonempty)
    (hsoc : LocalSocleDegrees B) (a : Exponent V) :
    Contains B a ↔ LowerFeasible (lowerRank B) a := by
  constructor
  · rintro ⟨b, hb, hba⟩ U
    exact (lowerRank_le hb U).trans (Finset.sum_le_sum (fun i _ => hba i))
  · intro hfeas
    by_contra hout
    obtain ⟨U, _, b, hab, hbsupp, hbout, hbsoc⟩ := missing_local_socle hB hout
    have hdegree := hsoc U b hbsupp hbout hbsoc
    have hle := degree_mono hab
    rw [degree_project] at hle
    have hr := hfeas U
    omega

/-- The complete converse in the local-socle characterization, before invoking
any homological source for its literal monomial socle hypothesis. -/
theorem polymatroidal_of_local_socles {B : Family V} (hB : B.Nonempty)
    (ha : Antichain B) (hl : LocallyEquigenerated B) (hsoc : LocalSocleDegrees B) :
    IsPolymatroidal B := by
  obtain ⟨d, hd⟩ := hl Finset.univ
  have he : localize B Finset.univ = B := by
    have hp : project (Finset.univ : Finset V) = id := funext project_univ
    simpa [localize, hp] using minimalFamily_eq ha
  rw [he] at hd
  exact polymatroidal_of_lower_inequalities hd (lowerRank_supermodular hB hl)
    (contains_iff_lowerFeasible hB hsoc)

end CommAlg.Polymatroid

end
end CheckedSource40

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "41: CommAlg.Polymatroid.CloneMatroid\n"

/-! ## Source: CommAlg.Polymatroid.CloneMatroid -/
section CheckedSource41

/-! # The genuine clone matroid of an exchange family

Replacing each coordinate by sufficiently many interchangeable elements turns
the integer exchange axiom into the ordinary matroid basis exchange axiom.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Clone (V : Type*) (d : ℕ) := V × Fin (d + 1)

def clonesOfSet {d : ℕ} (S : Set (Clone V d)) : Finset (Clone V d) :=
  Finset.univ.filter (· ∈ S)

@[simp] theorem mem_clonesOfSet {d : ℕ} (S : Set (Clone V d)) (x : Clone V d) :
    x ∈ clonesOfSet S ↔ x ∈ S := by simp [clonesOfSet]

@[simp] theorem clonesOfSet_coe {d : ℕ} (S : Finset (Clone V d)) :
    clonesOfSet (S : Set (Clone V d)) = S := by ext x; simp

def cloneCount {d : ℕ} (S : Finset (Clone V d)) : Exponent V :=
  ∑ x ∈ S, Finsupp.single x.1 1

@[simp] theorem cloneCount_apply {d : ℕ} (S : Finset (Clone V d)) (i : V) :
    cloneCount S i = (S.filter (fun x => x.1 = i)).card := by
  simp only [cloneCount, Finsupp.finsetSum_apply, Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_congr rfl (fun x _ => by simp [Finsupp.single_apply, eq_comm])

@[simp] theorem cloneCount_degree {d : ℕ} (S : Finset (Clone V d)) :
    (cloneCount S).degree = S.card := by
  simp [cloneCount, map_sum]

theorem cloneCount_mono {d : ℕ} {S T : Finset (Clone V d)} (hST : S ⊆ T) :
    cloneCount S ≤ cloneCount T := by
  intro i
  rw [cloneCount_apply, cloneCount_apply]
  exact Finset.card_le_card (Finset.filter_subset_filter _ hST)

theorem cloneCount_exchange {d : ℕ} {S : Finset (Clone V d)} {e f : Clone V d}
    (he : e ∈ S) (hf : f ∉ S) :
    cloneCount (insert f (S.erase e)) = exchange (cloneCount S) e.1 f.1 := by
  have hfe : f ∉ S.erase e := fun h => hf (Finset.mem_of_mem_erase h)
  have hc : cloneCount (S.erase e) + Finsupp.single e.1 1 = cloneCount S :=
    Finset.sum_erase_add _ _ he
  rw [cloneCount, Finset.sum_insert hfe]
  change Finsupp.single f.1 1 + cloneCount (S.erase e) = _
  rw [exchange, ← hc, add_tsub_cancel_right, add_comm]

def canonicalClones (d : ℕ) (a : Exponent V) : Finset (Clone V d) :=
  Finset.univ.filter (fun x => x.2.val < a x.1)

theorem coordinate_le_degree (a : Exponent V) (i : V) : a i ≤ a.degree := by
  rw [Finsupp.degree_eq_sum]
  exact Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)

theorem cloneCount_canonical (d : ℕ) (a : Exponent V) (ha : ∀ i, a i ≤ d + 1) :
    cloneCount (canonicalClones d a) = a := by
  ext i
  rw [cloneCount_apply]
  simp only [canonicalClones, Finset.filter_filter]
  have he : (Finset.univ.filter (fun x : Clone V d => x.2.val < a x.1 ∧ x.1 = i)) =
      (Finset.univ.filter (fun k : Fin (d + 1) => k.val < a i)).map
        ⟨fun k => (i, k), fun k l h => congrArg Prod.snd h⟩ := by
    ext x
    constructor
    · intro hx
      obtain ⟨hx, hi⟩ := (Finset.mem_filter.mp hx).2
      apply Finset.mem_map.mpr
      refine ⟨x.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · simpa [hi] using hx
      · exact Prod.ext hi.symm rfl
    · intro hx
      obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hk).2, rfl⟩
  rw [he, Finset.card_map, Fin.card_filter_val_lt, Nat.min_eq_right (ha i)]

theorem cloneCount_subsetSum {d : ℕ} (S : Finset (Clone V d)) (U : Finset V) :
    subsetSum (cloneCount S) U = (S.filter (fun x => x.1 ∈ U)).card := by
  simp only [subsetSum, cloneCount, Finsupp.finsetSum_apply]
  rw [Finset.sum_comm]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  simp [Finsupp.single_apply]

theorem exists_clone_of_count_lt {d : ℕ} {S T : Finset (Clone V d)} {i : V}
    (h : cloneCount S i < cloneCount T i) :
    ∃ f ∈ T, f ∉ S ∧ f.1 = i := by
  by_contra hn
  push_neg at hn
  have hsub : T.filter (fun x => x.1 = i) ⊆ S.filter (fun x => x.1 = i) := by
    intro f hf
    obtain ⟨hfT, hfi⟩ := Finset.mem_filter.mp hf
    refine Finset.mem_filter.mpr ⟨?_, hfi⟩
    by_contra hfS
    exact hn f hfT hfS hfi
  have hcard := Finset.card_le_card hsub
  rw [← cloneCount_apply, ← cloneCount_apply] at hcard
  omega

theorem exists_clone_same_of_count_le {d : ℕ} {S T : Finset (Clone V d)}
    {e : Clone V d} (heS : e ∈ S) (heT : e ∉ T)
    (h : cloneCount S e.1 ≤ cloneCount T e.1) :
    ∃ f ∈ T, f ∉ S ∧ f.1 = e.1 := by
  by_contra hn
  push_neg at hn
  have hsub : T.filter (fun x => x.1 = e.1) ⊆ S.filter (fun x => x.1 = e.1) := by
    intro f hf
    obtain ⟨hfT, hfi⟩ := Finset.mem_filter.mp hf
    refine Finset.mem_filter.mpr ⟨?_, hfi⟩
    by_contra hfS
    exact hn f hfT hfS hfi
  have hne : T.filter (fun x => x.1 = e.1) ≠ S.filter (fun x => x.1 = e.1) := by
    intro heq
    have hm : e ∈ T.filter (fun x => x.1 = e.1) := by rw [heq]; simp [heS]
    exact heT (Finset.mem_filter.mp hm).1
  have hcard := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
  rw [← cloneCount_apply, ← cloneCount_apply] at hcard
  omega

set_option maxHeartbeats 800000 in
theorem clone_basis_exchange {B : Family V} {d : ℕ} (hB : IsPolymatroidal B) :
    Matroid.ExchangeProperty
      (fun S : Set (Clone V d) => cloneCount (clonesOfSet S) ∈ B) := by
  intro S T hS hT e he
  let SF := (clonesOfSet S)
  let TF := (clonesOfSet T)
  have heS : e ∈ SF := by simpa [SF] using he.1
  have heT : e ∉ TF := by simpa [TF] using he.2
  by_cases hcount : cloneCount TF e.1 < cloneCount SF e.1
  · obtain ⟨j, hj, hex⟩ := hB.2 (cloneCount SF) hS (cloneCount TF) hT e.1 hcount
    obtain ⟨f, hfT, hfS, hfj⟩ := exists_clone_of_count_lt hj
    refine ⟨f, ⟨by simpa [TF] using hfT, by simpa [SF] using hfS⟩, ?_⟩
    have heq : (clonesOfSet (insert f (S \ {e}))) = insert f (SF.erase e) := by
      ext x
      simp [SF, and_comm]
    change cloneCount (clonesOfSet (insert f (S \ {e}))) ∈ B
    rw [heq, cloneCount_exchange heS hfS, hfj]
    exact hex
  · obtain ⟨f, hfT, hfS, hfe⟩ := exists_clone_same_of_count_le heS heT (Nat.le_of_not_gt hcount)
    refine ⟨f, ⟨by simpa [TF] using hfT, by simpa [SF] using hfS⟩, ?_⟩
    have heq : (clonesOfSet (insert f (S \ {e}))) = insert f (SF.erase e) := by
      ext x
      simp [SF, and_comm]
    change cloneCount (clonesOfSet (insert f (S \ {e}))) ∈ B
    rw [heq, cloneCount_exchange heS hfS, hfe]
    have hpos : 0 < cloneCount SF e.1 := by
      rw [cloneCount_apply]
      exact Finset.card_pos.mpr ⟨e, by simp [heS]⟩
    have hsame : exchange (cloneCount SF) e.1 e.1 = cloneCount SF := by
      ext i
      by_cases hi : i = e.1
      · subst i
        simpa only [exchange_apply, ↓reduceIte] using
          Nat.sub_add_cancel (show 1 ≤ cloneCount SF e.1 by omega)
      · simp [hi]
    rwa [hsame]

/-- No rank condition is assumed: this matroid is constructed solely from the
given finite equigenerated exchange family. -/
def cloneMatroid (B : Family V) (hBne : B.Nonempty) (d : ℕ)
    (hdeg : Equigenerated B d) (hB : IsPolymatroidal B) : Matroid (Clone V d) :=
  Matroid.ofIsBaseOfFinite (Set.toFinite Set.univ)
    (fun S => cloneCount (clonesOfSet S) ∈ B)
    (by
      obtain ⟨a, ha⟩ := hBne
      refine ⟨(canonicalClones d a : Set (Clone V d)), ?_⟩
      have he : (clonesOfSet (canonicalClones d a : Set (Clone V d))) = canonicalClones d a := by
        ext x
        simp
      rw [he]
      rw [cloneCount_canonical d a (fun i => (coordinate_le_degree a i).trans (by rw [hdeg a ha]; omega))]
      exact ha)
    (clone_basis_exchange hB) (fun _ _ => Set.subset_univ _)

@[simp] theorem cloneMatroid_ground (B : Family V) (hBne : B.Nonempty) (d : ℕ)
    (hdeg : Equigenerated B d) (hB : IsPolymatroidal B) :
    (cloneMatroid B hBne d hdeg hB).E = Set.univ := rfl

@[simp] theorem cloneMatroid_isBase (B : Family V) (hBne : B.Nonempty) (d : ℕ)
    (hdeg : Equigenerated B d) (hB : IsPolymatroidal B) (S : Set (Clone V d)) :
    (cloneMatroid B hBne d hdeg hB).IsBase S ↔ cloneCount (clonesOfSet S) ∈ B := Iff.rfl

end CommAlg.Polymatroid

end
end CheckedSource41

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "42: CommAlg.Polymatroid.CloneRank\n"

/-! ## Source: CommAlg.Polymatroid.CloneRank -/
section CheckedSource42

/-! # Canonical rank inequalities from the integer exchange axiom

The clone matroid proves both submodularity of the canonical rank and the
integer saturation of its base polytope.  In particular no linear-resolution
theorem or homological characterization is used in this direction.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def upperRank (B : Family V) (U : Finset V) : ℕ :=
  B.sup (fun a => subsetSum a U)

theorem le_upperRank {B : Family V} {a : Exponent V} (ha : a ∈ B) (U : Finset V) :
    subsetSum a U ≤ upperRank B U := by
  exact Finset.le_sup (f := fun b => subsetSum b U) ha

theorem upperRank_attained {B : Family V} (hB : B.Nonempty) (U : Finset V) :
    ∃ a ∈ B, subsetSum a U = upperRank B U := by
  obtain ⟨a, ha, he⟩ := Finset.exists_mem_eq_sup B hB (fun a => subsetSum a U)
  exact ⟨a, ha, he.symm⟩

def cloneGroup {d : ℕ} (U : Finset V) : Set (Clone V d) := {x | x.1 ∈ U}

theorem encard_clonesOfSet {d : ℕ} (S : Set (Clone V d)) :
    S.encard = (clonesOfSet S).card := by
  have h : (clonesOfSet S : Set (Clone V d)) = S := by ext x; simp
  calc
    S.encard = (clonesOfSet S : Set (Clone V d)).encard := congrArg Set.encard h.symm
    _ = _ := Set.encard_coe_eq_coe_finsetCard _

theorem cloneGroup_inter {d : ℕ} (U W : Finset V) :
    (cloneGroup (d := d) (U ∩ W)) = cloneGroup U ∩ cloneGroup W := by
  ext x; simp [cloneGroup]

theorem cloneGroup_union {d : ℕ} (U W : Finset V) :
    (cloneGroup (d := d) (U ∪ W)) = cloneGroup U ∪ cloneGroup W := by
  ext x; simp [cloneGroup]

section Family

variable (B : Family V) (hBne : B.Nonempty) (d : ℕ)
  (hdeg : Equigenerated B d) (hB : IsPolymatroidal B)

local notation "M" => cloneMatroid B hBne d hdeg hB

theorem cloneGroup_rank (U : Finset V) : (M).eRk (cloneGroup U) = upperRank B U := by
  apply le_antisymm
  · apply Matroid.eRk_le_iff.mpr
    intro I hIU hI
    obtain ⟨T, hT, hIT⟩ := hI.exists_isBase_superset
    have hT' : cloneCount (clonesOfSet T) ∈ B := hT
    have hsub : clonesOfSet I ⊆ (clonesOfSet T).filter (fun x => x.1 ∈ U) := by
      intro x hx
      have hxI : x ∈ I := mem_clonesOfSet I x |>.mp hx
      exact Finset.mem_filter.mpr ⟨mem_clonesOfSet T x |>.mpr (hIT hxI), hIU hxI⟩
    have hcard : (clonesOfSet I).card ≤ upperRank B U := calc
      _ ≤ ((clonesOfSet T).filter (fun x => x.1 ∈ U)).card := Finset.card_le_card hsub
      _ = subsetSum (cloneCount (clonesOfSet T)) U := (cloneCount_subsetSum _ _).symm
      _ ≤ upperRank B U := le_upperRank hT' U
    rw [encard_clonesOfSet]
    exact_mod_cast hcard
  · obtain ⟨a, ha, he⟩ := upperRank_attained hBne U
    let S := canonicalClones d a
    have hc : cloneCount S = a := cloneCount_canonical d a
      (fun i => (coordinate_le_degree a i).trans (by rw [hdeg a ha]; omega))
    have hS : (M).IsBase (S : Set (Clone V d)) := by
      change cloneCount (clonesOfSet (S : Set (Clone V d))) ∈ B
      rwa [clonesOfSet_coe, hc]
    let T := S.filter (fun x => x.1 ∈ U)
    have hT : (M).Indep (T : Set (Clone V d)) := hS.indep.subset (by
      intro x hx
      exact (Finset.mem_filter.mp hx).1)
    have hTU : (T : Set (Clone V d)) ⊆ cloneGroup U := by
      intro x hx
      exact (Finset.mem_filter.mp hx).2
    have hcard : T.card = upperRank B U := by
      rw [← cloneCount_subsetSum, hc, he]
    simpa only [Set.encard_coe_eq_coe_finsetCard, hcard] using hT.encard_le_eRk_of_subset hTU

/-- The canonical upper rank of an exchange family is genuinely submodular. -/
def canonicalRank : RankFunction V where
  toFun := upperRank B
  empty := by simp [upperRank]
  monotone := by
    intro U W hUW
    apply Finset.sup_le
    intro a ha
    exact (subsetSum_mono a hUW).trans (le_upperRank ha W)
  submodular := by
    intro U W
    have h := (M).eRk_inter_add_eRk_union_le (cloneGroup U) (cloneGroup W)
    rw [← cloneGroup_inter, ← cloneGroup_union,
      cloneGroup_rank B hBne d hdeg hB, cloneGroup_rank B hBne d hdeg hB,
      cloneGroup_rank B hBne d hdeg hB, cloneGroup_rank B hBne d hdeg hB] at h
    exact_mod_cast (show (upperRank B (U ∪ W) : ℕ∞) + upperRank B (U ∩ W) ≤
      upperRank B U + upperRank B W by simpa only [add_comm] using h)

@[simp] theorem canonicalRank_apply (U : Finset V) :
    canonicalRank B hBne d hdeg hB U = upperRank B U := rfl

theorem cloneCount_map (σ : Clone V d ≃ Clone V d)
    (hσ : ∀ x, (σ x).1 = x.1) (S : Finset (Clone V d)) :
    cloneCount (S.map σ.toEmbedding) = cloneCount S := by
  simp only [cloneCount, Finset.sum_map, Equiv.toEmbedding_apply, hσ]

theorem clonesOfSet_image (σ : Clone V d ≃ Clone V d) (S : Set (Clone V d)) :
    clonesOfSet (σ '' S) = (clonesOfSet S).map σ.toEmbedding := by
  ext x
  simp

theorem clone_indep_image (σ : Clone V d ≃ Clone V d)
    (hσ : ∀ x, (σ x).1 = x.1) {I : Set (Clone V d)} (hI : (M).Indep I) :
    (M).Indep (σ '' I) := by
  obtain ⟨T, hT, hIT⟩ := hI.exists_isBase_superset
  apply Matroid.indep_iff.mpr
  refine ⟨σ '' T, ?_, Set.image_mono hIT⟩
  change cloneCount (clonesOfSet (σ '' T)) ∈ B
  rw [clonesOfSet_image, cloneCount_map d σ hσ]
  exact hT

theorem clone_indep_image_iff (σ : Clone V d ≃ Clone V d)
    (hσ : ∀ x, (σ x).1 = x.1) (I : Set (Clone V d)) :
    (M).Indep (σ '' I) ↔ (M).Indep I := by
  refine ⟨?_, clone_indep_image B hBne d hdeg hB σ hσ⟩
  intro h
  have hσ' : ∀ x, (σ.symm x).1 = x.1 := by
    intro x
    simpa only [Equiv.apply_symm_apply] using (hσ (σ.symm x)).symm
  have hi := clone_indep_image B hBne d hdeg hB σ.symm hσ' h
  simpa using hi

/-- Every clone of an element in a circuit lies in that circuit's closure. -/
theorem circuit_clone_mem_closure {C : Set (Clone V d)} (hC : (M).IsCircuit C)
    {e f : Clone V d} (he : e ∈ C) (hfe : f.1 = e.1) : f ∈ (M).closure C := by
  by_cases hf : f ∈ C
  · exact (M).subset_closure C (by simp) hf
  have hne : e ≠ f := fun h => hf (h ▸ he)
  have hswap : ∀ x : Clone V d, (Equiv.swap e f x).1 = x.1 := by
    intro x
    by_cases hxe : x = e
    · subst x; simpa using hfe
    by_cases hxf : x = f
    · subst x; simpa using hfe.symm
    simp [Equiv.swap_apply_of_ne_of_ne hxe hxf]
  have hn : ¬ (M).Indep ((Equiv.swap e f) '' C) := by
    intro h
    exact hC.not_indep ((clone_indep_image_iff B hBne d hdeg hB _ hswap C).mp h)
  have him : ((Equiv.swap e f) '' C) = insert f (C \ {e}) := by
    rw [Equiv.image_swap_of_mem_of_notMem he hf]
    ext x
    simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff]
    aesop
  rw [him] at hn
  have hdep : (M).Dep (insert f (C \ {e})) := (Matroid.not_indep_iff (by simp)).mp hn
  have hf' : f ∉ C \ {e} := fun h => hf h.1
  have hc := (hC.sdiff_singleton_indep he).mem_closure_iff_of_notMem hf'
  exact (M).closure_subset_closure Set.sdiff_subset (hc.mpr hdep)

include hBne hdeg hB in
/-- Exact integral base-polytope description, proved from exchange alone. -/
theorem mem_iff_canonical_rank (a : Exponent V) :
    a ∈ B ↔ a.degree = d ∧ ∀ U, subsetSum a U ≤ upperRank B U := by
  refine ⟨fun ha => ⟨hdeg a ha, fun U => le_upperRank ha U⟩, ?_⟩
  rintro ⟨hadeg, haU⟩
  let S := canonicalClones d a
  have hc : cloneCount S = a := cloneCount_canonical d a
    (fun i => (coordinate_le_degree a i).trans (by rw [hadeg]; omega))
  have hS : (M).Indep (S : Set (Clone V d)) := by
    by_contra hn
    have hdep : (M).Dep (S : Set (Clone V d)) :=
      (Matroid.not_indep_iff (by simp)).mp hn
    obtain ⟨C, hCS, hC⟩ := hdep.exists_isCircuit_subset
    let U := (clonesOfSet C).image Prod.fst
    have hCG : C ⊆ cloneGroup U := by
      intro x hx
      exact Finset.mem_image.mpr ⟨x, (mem_clonesOfSet C x).mpr hx, rfl⟩
    have hGC : cloneGroup U ⊆ (M).closure C := by
      intro x hx
      obtain ⟨e, he, hex⟩ := Finset.mem_image.mp hx
      exact circuit_clone_mem_closure B hBne d hdeg hB hC
        ((mem_clonesOfSet C e).mp he) hex.symm
    have hr : (M).eRk (cloneGroup U) ≤ (M).eRk C := by
      simpa only [(M).eRk_closure_eq] using (M).eRk_mono hGC
    have hlt := Matroid.eRk_lt_encard_of_dep_of_finite (Set.toFinite C) hC.dep
    have hcount : C.encard ≤ (subsetSum a U : ℕ∞) := by
      have hsub : clonesOfSet C ⊆ S.filter (fun x => x.1 ∈ U) := by
        intro x hx
        have hxC := (mem_clonesOfSet C x).mp hx
        exact Finset.mem_filter.mpr ⟨hCS hxC, hCG hxC⟩
      have hcard := Finset.card_le_card hsub
      rw [← cloneCount_subsetSum, hc] at hcard
      rw [encard_clonesOfSet]
      exact_mod_cast hcard
    have haR : (subsetSum a U : ℕ∞) ≤ (M).eRk (cloneGroup U) := by
      rw [cloneGroup_rank]
      exact_mod_cast haU U
    exact (not_lt_of_ge haR) (hr.trans_lt (hlt.trans_le hcount))
  obtain ⟨T, hT, hST⟩ := hS.exists_isBase_superset
  have hmem : cloneCount (clonesOfSet T) ∈ B := hT
  have hle : a ≤ cloneCount (clonesOfSet T) := by
    rw [← hc]
    apply cloneCount_mono
    intro x hx
    exact (mem_clonesOfSet T x).mpr (hST hx)
  have heq := eq_of_le_of_degree_eq hle (hadeg.trans (hdeg _ hmem).symm)
  rwa [heq]

end Family

end CommAlg.Polymatroid

end
end CheckedSource42

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "43: CommAlg.Polymatroid.RankIdeal\n"

/-! ## Source: CommAlg.Polymatroid.RankIdeal -/
section CheckedSource43

/-! # From rank inequalities to actual monomial ideals -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem subsetSum_add_compl (a : Exponent V) (U : Finset V) :
    subsetSum a U + subsetSum a Uᶜ = a.degree := by
  simpa only [subsetSum, Finsupp.degree_eq_sum] using U.sum_add_sum_compl a

def RankFunction.lower (g : RankFunction V) (U : Finset V) : ℕ :=
  g Finset.univ - g Uᶜ

theorem RankFunction.lower_add_compl (g : RankFunction V) (U : Finset V) :
    g.lower U + g Uᶜ = g Finset.univ :=
  Nat.sub_add_cancel (g.monotone (Finset.subset_univ _))

@[simp] theorem RankFunction.lower_empty (g : RankFunction V) : g.lower ∅ = 0 := by
  simp [RankFunction.lower]

@[simp] theorem RankFunction.lower_univ (g : RankFunction V) :
    g.lower Finset.univ = g Finset.univ := by simp [RankFunction.lower]

theorem RankFunction.lower_le (g : RankFunction V) (U : Finset V) :
    g.lower U ≤ g Finset.univ := Nat.sub_le _ _

theorem RankFunction.lower_supermodular (g : RankFunction V) : Supermodular g.lower := by
  intro U W
  have hs := g.submodular Uᶜ Wᶜ
  have hU := g.lower_add_compl U
  have hW := g.lower_add_compl W
  have hUn := g.lower_add_compl (U ∪ W)
  have hIn := g.lower_add_compl (U ∩ W)
  simp only [compl_union, compl_inter] at hUn hIn
  omega

def UpperFeasible (g : RankFunction V) (a : Exponent V) : Prop :=
  ∀ U, subsetSum a U ≤ g U

theorem upperFeasible_iff_lowerFeasible (g : RankFunction V) {a : Exponent V}
    (ha : a.degree = g Finset.univ) :
    UpperFeasible g a ↔ LowerFeasible g.lower a := by
  constructor
  · intro h U
    have hu := h Uᶜ
    have hs := subsetSum_add_compl a U
    have hg := g.lower_add_compl U
    omega
  · intro h U
    have hu := h Uᶜ
    have hs := subsetSum_add_compl a U
    have hg := g.lower_add_compl Uᶜ
    simp only [compl_compl] at hg
    omega

theorem single_one_le {a : Exponent V} {i : V} (hi : 0 < a i) :
    Finsupp.single i 1 ≤ a := by
  intro j
  by_cases hji : j = i
  · subst j; simpa using (show 1 ≤ a i by omega)
  · simp [Finsupp.single_apply, hji, Ne.symm hji]

theorem subsetSum_sub_single {a : Exponent V} {i : V} (hi : 0 < a i) (U : Finset V) :
    subsetSum (a - Finsupp.single i 1) U + (if i ∈ U then 1 else 0) = subsetSum a U := by
  have he := tsub_add_cancel_of_le (single_one_le hi)
  have hs := congrArg (fun b : Exponent V => subsetSum b U) he
  simpa [subsetSum, Finset.sum_add_distrib, Finsupp.single_apply] using hs

theorem failed_decrement_tight {r : Finset V → ℕ} {a : Exponent V}
    (ha : LowerFeasible r a) {i : V} (hi : 0 < a i)
    (hbad : ¬ LowerFeasible r (a - Finsupp.single i 1)) :
    ∃ U, Tight r a U ∧ i ∈ U := by
  simp only [LowerFeasible, not_forall, not_le] at hbad
  obtain ⟨U, hU⟩ := hbad
  have hs := subsetSum_sub_single hi U
  have hf := ha U
  have hiU : i ∈ U := by
    by_contra h
    rw [if_neg h] at hs
    omega
  refine ⟨U, ?_, hiU⟩
  rw [if_pos hiU] at hs
  unfold Tight
  omega

theorem tight_cover {r : Finset V → ℕ} (hr : Supermodular r) (hr0 : r ∅ = 0)
    {a : Exponent V} (ha : LowerFeasible r a) (D : Finset V)
    (h : ∀ i ∈ D, ∃ U, Tight r a U ∧ i ∈ U) :
    ∃ U, Tight r a U ∧ D ⊆ U := by
  induction D using Finset.induction_on with
  | empty => exact ⟨∅, by simp [Tight, hr0], Finset.empty_subset _⟩
  | @insert i D hi ih =>
    obtain ⟨U, hU, hDU⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    obtain ⟨W, hW, hiW⟩ := h i (Finset.mem_insert_self _ _)
    exact ⟨U ∪ W, (tight_union_inter hr ha hU hW).1,
      Finset.insert_subset_iff.mpr ⟨Finset.mem_union_right _ hiW,
        hDU.trans Finset.subset_union_left⟩⟩

/-- Integral descent to a base: all larger feasible vectors dominate a
feasible vector of the precise total rank. -/
theorem exists_lower_base_below {r : Finset V → ℕ} (hr : Supermodular r)
    (hr0 : r ∅ = 0) {d : ℕ} (hrd : r Finset.univ = d) (hrle : ∀ U, r U ≤ d)
    {a : Exponent V} (ha : LowerFeasible r a) :
    ∃ b, b ≤ a ∧ b.degree = d ∧ LowerFeasible r b := by
  let T : Set (Exponent V) := {b | b ≤ a ∧ LowerFeasible r b}
  have hfin : T.Finite := (Set.finite_Iic a).subset (fun _ h => h.1)
  obtain ⟨b, hb, hmin⟩ := hfin.exists_minimal ⟨a, le_rfl, ha⟩
  have hcover : ∀ i ∈ b.support, ∃ U, Tight r b U ∧ i ∈ U := by
    intro i hi
    have hip : 0 < b i := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)
    apply failed_decrement_tight hb.2 hip
    intro hgood
    have hmem : b - Finsupp.single i 1 ∈ T := ⟨tsub_le_self.trans hb.1, hgood⟩
    have hle := hmin hmem tsub_le_self
    have hc := hle i
    simp only [Finsupp.tsub_apply, Finsupp.single_eq_same] at hc
    omega
  obtain ⟨U, hU, hsupp⟩ := tight_cover hr hr0 hb.2 b.support hcover
  have hp : project U b = b := by
    ext i
    by_cases hi : i ∈ U
    · simp [hi]
    · have hb0 : b i = 0 := Finsupp.notMem_support_iff.mp (fun h => hi (hsupp h))
      simp [hi, hb0]
  have hdegU : b.degree = subsetSum b U := by rw [← degree_project, hp]
  have hlo := hb.2 Finset.univ
  have hhi := hrle U
  simp only [subsetSum_univ, hrd] at hlo
  unfold Tight at hU
  exact ⟨b, hb.1, by omega, hb.2⟩

theorem lowerRank_add_upperRank_compl {B : Family V} (hBne : B.Nonempty) {d : ℕ}
    (hdeg : Equigenerated B d) (U : Finset V) :
    lowerRank B U + upperRank B Uᶜ = d := by
  obtain ⟨a, ha, hamin⟩ := lowerRank_attained hBne U
  obtain ⟨b, hb, hbmax⟩ := upperRank_attained hBne Uᶜ
  have haSum := subsetSum_add_compl a U
  have hbSum := subsetSum_add_compl b U
  have hbMin := lowerRank_le hb U
  have haMax := le_upperRank ha Uᶜ
  have haDeg := hdeg a ha
  have hbDeg := hdeg b hb
  omega

theorem lowerRank_eq_canonical_lower (B : Family V) (hBne : B.Nonempty) (d : ℕ)
    (hdeg : Equigenerated B d) (hB : IsPolymatroidal B) (U : Finset V) :
    lowerRank B U = (canonicalRank B hBne d hdeg hB).lower U := by
  have hsum := lowerRank_add_upperRank_compl hBne hdeg U
  have htop : upperRank B Finset.univ = d := by
    obtain ⟨a, ha, he⟩ := upperRank_attained hBne Finset.univ
    simpa only [subsetSum_univ, hdeg a ha] using he.symm
  change lowerRank B U = upperRank B Finset.univ - upperRank B Uᶜ
  omega

/-- Complete monomial membership for an arbitrary exchange family. -/
theorem contains_iff_canonical_lower (B : Family V) (hBne : B.Nonempty) (d : ℕ)
    (hdeg : Equigenerated B d) (hB : IsPolymatroidal B) (a : Exponent V) :
    Contains B a ↔ LowerFeasible (lowerRank B) a := by
  constructor
  · rintro ⟨b, hb, hba⟩ U
    exact (lowerRank_le hb U).trans (Finset.sum_le_sum (fun i _ => hba i))
  · intro ha
    let g := canonicalRank B hBne d hdeg hB
    have hr : lowerRank B = g.lower := funext (lowerRank_eq_canonical_lower B hBne d hdeg hB)
    have htop : g Finset.univ = d := by
      change upperRank B Finset.univ = d
      obtain ⟨b, hb, he⟩ := upperRank_attained hBne Finset.univ
      simpa only [subsetSum_univ, hdeg b hb] using he.symm
    have ha' : LowerFeasible g.lower a := by rwa [← hr]
    obtain ⟨b, hba, hbdeg, hb⟩ := exists_lower_base_below g.lower_supermodular
      g.lower_empty g.lower_univ (g.lower_le) ha'
    refine ⟨b, (mem_iff_canonical_rank B hBne d hdeg hB b).mpr ⟨hbdeg.trans htop, ?_⟩, hba⟩
    exact (upperFeasible_iff_lowerFeasible g hbdeg).mpr hb

end CommAlg.Polymatroid

end
end CheckedSource43

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "44: CommAlg.Polymatroid.ConstraintMatroid\n"

/-! ## Source: CommAlg.Polymatroid.ConstraintMatroid -/
section CheckedSource44

/-! # Matroids defined by possibly nonmonotone submodular constraints

This is the constraint-matroid lemma used by the homological rank formula.
Monotonicity of the constraint function is deliberately not assumed.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def SubmodularNat (q : Finset V → ℕ) : Prop :=
  ∀ U W, q (U ∪ W) + q (U ∩ W) ≤ q U + q W

def ConstraintFeasible (q : Finset V → ℕ) (I : Finset V) : Prop :=
  ∀ U, (I ∩ U).card ≤ q U

def ConstraintTight (q : Finset V → ℕ) (I U : Finset V) : Prop :=
  (I ∩ U).card = q U

theorem card_inter_modular (I U W : Finset V) :
    (I ∩ (U ∪ W)).card + (I ∩ (U ∩ W)).card = (I ∩ U).card + (I ∩ W).card := by
  have hu : I ∩ (U ∪ W) = (I ∩ U) ∪ (I ∩ W) := by ext x; simp; tauto
  have hi : I ∩ (U ∩ W) = (I ∩ U) ∩ (I ∩ W) := by ext x; simp; tauto
  rw [hu, hi]
  exact Finset.card_union_add_card_inter _ _

theorem constraint_tight_union_inter {q : Finset V → ℕ} (hq : SubmodularNat q)
    {I U W : Finset V} (hI : ConstraintFeasible q I)
    (hU : ConstraintTight q I U) (hW : ConstraintTight q I W) :
    ConstraintTight q I (U ∪ W) ∧ ConstraintTight q I (U ∩ W) := by
  have hm := card_inter_modular I U W
  have hs := hq U W
  have hfU := hI (U ∪ W)
  have hfI := hI (U ∩ W)
  unfold ConstraintTight at *
  omega

theorem constraintFeasible_empty (q : Finset V → ℕ) : ConstraintFeasible q ∅ := by
  intro U; simp

theorem ConstraintFeasible.subset {q : Finset V → ℕ} {I J : Finset V}
    (hJ : ConstraintFeasible q J) (hIJ : I ⊆ J) : ConstraintFeasible q I := by
  intro U
  exact (Finset.card_le_card (fun x hx => Finset.mem_inter.mpr
    ⟨hIJ (Finset.mem_inter.mp hx).1, (Finset.mem_inter.mp hx).2⟩)).trans (hJ U)

theorem constraint_failed_insert {q : Finset V → ℕ} {I : Finset V}
    (hI : ConstraintFeasible q I) {e : V} (he : e ∉ I)
    (hbad : ¬ ConstraintFeasible q (insert e I)) :
    ∃ U, ConstraintTight q I U ∧ e ∈ U := by
  simp only [ConstraintFeasible, not_forall, not_le] at hbad
  obtain ⟨U, hU⟩ := hbad
  have heU : e ∈ U := by
    by_contra hn
    have hi : insert e I ∩ U = I ∩ U := by ext x; simp; aesop
    rw [hi] at hU
    exact (not_lt_of_ge (hI U)) hU
  have hi : insert e I ∩ U = insert e (I ∩ U) := by ext x; simp; aesop
  have he' : e ∉ I ∩ U := fun h => he (Finset.mem_inter.mp h).1
  rw [hi, Finset.card_insert_of_notMem he'] at hU
  exact ⟨U, Nat.le_antisymm (hI U) (by omega), heU⟩

theorem constraint_tight_cover {q : Finset V → ℕ} (hq : SubmodularNat q) (hq0 : q ∅ = 0)
    {I : Finset V} (hI : ConstraintFeasible q I) (D : Finset V)
    (h : ∀ e ∈ D, ∃ U, ConstraintTight q I U ∧ e ∈ U) :
    ∃ U, ConstraintTight q I U ∧ D ⊆ U := by
  induction D using Finset.induction_on with
  | empty => exact ⟨∅, by simp [ConstraintTight, hq0], Finset.empty_subset _⟩
  | @insert e D he ih =>
    obtain ⟨U, hU, hDU⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    obtain ⟨W, hW, heW⟩ := h e (Finset.mem_insert_self _ _)
    exact ⟨U ∪ W, (constraint_tight_union_inter hq hI hU hW).1,
      Finset.insert_subset_iff.mpr ⟨Finset.mem_union_right _ heW,
        hDU.trans Finset.subset_union_left⟩⟩

theorem constraint_augment {q : Finset V → ℕ} (hq : SubmodularNat q) (hq0 : q ∅ = 0)
    {I J : Finset V} (hI : ConstraintFeasible q I) (hJ : ConstraintFeasible q J)
    (hcard : I.card < J.card) :
    ∃ e ∈ J, e ∉ I ∧ ConstraintFeasible q (insert e I) := by
  by_contra hn
  push_neg at hn
  obtain ⟨U, hU, hcover⟩ := constraint_tight_cover hq hq0 hI (J \ I) (by
    intro e he
    obtain ⟨heJ, heI⟩ := Finset.mem_sdiff.mp he
    exact constraint_failed_insert hI heI (hn e heJ heI))
  have hout : J \ U ⊆ I \ U := by
    intro e he
    obtain ⟨heJ, heU⟩ := Finset.mem_sdiff.mp he
    refine Finset.mem_sdiff.mpr ⟨?_, heU⟩
    by_contra heI
    exact heU (hcover (Finset.mem_sdiff.mpr ⟨heJ, heI⟩))
  have hc := Finset.card_le_card hout
  have hj := hJ U
  have hci := Finset.card_inter_add_card_sdiff I U
  have hcj := Finset.card_inter_add_card_sdiff J U
  unfold ConstraintTight at hU
  omega

def constraintMatroid (q : Finset V → ℕ) (hq : SubmodularNat q) (hq0 : q ∅ = 0)
    (T : Finset V) : Matroid V :=
  (IndepMatroid.ofFinset (T : Set V)
    (fun I => I ⊆ T ∧ ConstraintFeasible q I)
    ⟨Finset.empty_subset _, constraintFeasible_empty q⟩
    (fun _ _ hJ hIJ => ⟨hIJ.trans hJ.1, hJ.2.subset hIJ⟩)
    (by
      intro I J hI hJ hcard
      obtain ⟨e, heJ, heI, he⟩ := constraint_augment hq hq0 hI.2 hJ.2 hcard
      exact ⟨e, heJ, heI, Finset.insert_subset_iff.mpr ⟨hJ.1 heJ, hI.1⟩, he⟩)
    (fun _ hI => hI.1)).matroid

@[simp] theorem constraintMatroid_ground (q : Finset V → ℕ) (hq : SubmodularNat q)
    (hq0 : q ∅ = 0) (T : Finset V) :
    (constraintMatroid q hq hq0 T).E = (T : Set V) := rfl

@[simp] theorem constraintMatroid_indep (q : Finset V → ℕ) (hq : SubmodularNat q)
    (hq0 : q ∅ = 0) (T I : Finset V) :
    (constraintMatroid q hq hq0 T).Indep (I : Set V) ↔ I ⊆ T ∧ ConstraintFeasible q I := by
  change (∀ J : Finset V, (J : Set V) ⊆ (I : Set V) → J ⊆ T ∧ ConstraintFeasible q J) ↔ _
  constructor
  · exact fun h => h I Set.Subset.rfl
  · intro h J hJI
    exact ⟨hJI.trans h.1, h.2.subset hJI⟩

theorem constraint_card_le {q : Finset V → ℕ} {I R : Finset V}
    (hI : ConstraintFeasible q I) (hIR : I ⊆ R) (U : Finset V) :
    I.card ≤ q U + (R \ U).card := by
  have hc := Finset.card_le_card (Finset.sdiff_subset_sdiff hIR (le_refl U))
  have hi := hI U
  have he := Finset.card_inter_add_card_sdiff I U
  omega

/-- A maximal feasible subset has a tight-set certificate of its exact size. -/
theorem constraint_maximal_certificate {q : Finset V → ℕ} (hq : SubmodularNat q)
    (hq0 : q ∅ = 0) (R : Finset V) :
    ∃ I U, I ⊆ R ∧ ConstraintFeasible q I ∧
      I.card = q U + (R \ U).card ∧
      ∀ J, J ⊆ R → ConstraintFeasible q J → J.card ≤ I.card := by
  let C := R.powerset.filter (ConstraintFeasible q)
  have hC : C.Nonempty := ⟨∅, Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), constraintFeasible_empty q⟩⟩
  obtain ⟨I, hIC, hmax⟩ := C.exists_maximal hC
  obtain ⟨hIR, hI⟩ : I ⊆ R ∧ ConstraintFeasible q I := by
    simpa only [C, Finset.mem_filter, Finset.mem_powerset] using hIC
  have hblocked : ∀ e ∈ R \ I, ∃ U, ConstraintTight q I U ∧ e ∈ U := by
    intro e he
    obtain ⟨heR, heI⟩ := Finset.mem_sdiff.mp he
    apply constraint_failed_insert hI heI
    intro hgood
    have hiC : insert e I ∈ C := Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.insert_subset_iff.mpr ⟨heR, hIR⟩), hgood⟩
    exact heI (hmax hiC (Finset.subset_insert _ _) (Finset.mem_insert_self _ _))
  obtain ⟨U, hU, hcover⟩ := constraint_tight_cover hq hq0 hI (R \ I) hblocked
  have hout : R \ U = I \ U := by
    apply Finset.Subset.antisymm
    · intro e he
      obtain ⟨heR, heU⟩ := Finset.mem_sdiff.mp he
      refine Finset.mem_sdiff.mpr ⟨?_, heU⟩
      by_contra heI
      exact heU (hcover (Finset.mem_sdiff.mpr ⟨heR, heI⟩))
    · exact Finset.sdiff_subset_sdiff hIR (le_refl U)
  have hcard : I.card = q U + (R \ U).card := by
    rw [hout]
    have hc := Finset.card_inter_add_card_sdiff I U
    unfold ConstraintTight at hU
    omega
  exact ⟨I, U, hIR, hI, hcard, fun J hJR hJ => hcard ▸ constraint_card_le hJ hJR U⟩

def finiteSet (S : Set V) : Finset V := Finset.univ.filter (· ∈ S)

@[simp] theorem mem_finiteSet (S : Set V) (x : V) : x ∈ finiteSet S ↔ x ∈ S := by
  simp [finiteSet]

theorem coe_finiteSet (S : Set V) : (finiteSet S : Set V) = S := by ext x; simp

/-- The minimum formula is witnessed by an actual subset, and is the rank of
the actual Mathlib matroid, not an unproved combinatorial surrogate. -/
theorem constraint_rank_certificate (q : Finset V → ℕ) (hq : SubmodularNat q)
    (hq0 : q ∅ = 0) (T R : Finset V) (hRT : R ⊆ T) :
    ∃ U, (constraintMatroid q hq hq0 T).eRk (R : Set V) =
        ((q U + (R \ U).card : ℕ) : ℕ∞) ∧
      ∀ W, q U + (R \ U).card ≤ q W + (R \ W).card := by
  obtain ⟨I, U, hIR, hI, hcard, hmax⟩ := constraint_maximal_certificate hq hq0 R
  let M := constraintMatroid q hq hq0 T
  have hi : M.Indep (I : Set V) := (constraintMatroid_indep q hq hq0 T I).mpr
    ⟨hIR.trans hRT, hI⟩
  have he : M.eRk (R : Set V) = I.card := by
    apply le_antisymm
    · apply Matroid.eRk_le_iff.mpr
      intro J hJR hJ
      let JF := finiteSet J
      have hJF : M.Indep (JF : Set V) := by rwa [coe_finiteSet]
      have hJF' := (constraintMatroid_indep q hq hq0 T JF).mp hJF
      have hJFR : JF ⊆ R := by intro x hx; exact hJR ((mem_finiteSet J x).mp hx)
      have hc := hmax JF hJFR hJF'.2
      have hjc : J.encard = JF.card := by
        rw [← coe_finiteSet J, Set.encard_coe_eq_coe_finsetCard]
      rw [hjc]
      exact_mod_cast hc
    · simpa only [Set.encard_coe_eq_coe_finsetCard] using hi.encard_le_eRk_of_subset hIR
  refine ⟨U, he.trans (congrArg Nat.cast hcard), ?_⟩
  intro W
  rw [← hcard]
  exact constraint_card_le hI hIR W

end CommAlg.Polymatroid

end
end CheckedSource44

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "45: CommAlg.Polymatroid.ConstraintRank\n"

/-! ## Source: CommAlg.Polymatroid.ConstraintRank -/
section CheckedSource45

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

instance constraintMatroid_finite (q : Finset V → ℕ) (hq : SubmodularNat q)
    (hq0 : q ∅ = 0) (T : Finset V) : (constraintMatroid q hq hq0 T).Finite :=
  ⟨by rw [constraintMatroid_ground]; exact T.finite_toSet⟩

theorem constraint_rank_le (q : Finset V → ℕ) (hq : SubmodularNat q)
    (hq0 : q ∅ = 0) (T R : Finset V) (hRT : R ⊆ T) (U : Finset V) :
    (constraintMatroid q hq hq0 T).eRk (R : Set V) ≤
      ((q U + (R \ U).card : ℕ) : ℕ∞) := by
  obtain ⟨W, hW, hmin⟩ := constraint_rank_certificate q hq hq0 T R hRT
  rw [hW]
  exact_mod_cast hmin U

theorem le_constraint_rank (q : Finset V → ℕ) (hq : SubmodularNat q)
    (hq0 : q ∅ = 0) (T R : Finset V) (hRT : R ⊆ T) (n : ℕ) :
    (n : ℕ∞) ≤ (constraintMatroid q hq hq0 T).eRk (R : Set V) ↔
      ∀ U, n ≤ q U + (R \ U).card := by
  obtain ⟨W, hW, hmin⟩ := constraint_rank_certificate q hq hq0 T R hRT
  rw [hW]
  constructor
  · intro h U
    exact (show n ≤ q W + (R \ W).card by exact_mod_cast h).trans (hmin U)
  · intro h
    exact_mod_cast h W

/-- Every element outside a minimizing set is an actual coloop. -/
theorem constraint_isColoop_of_minimizer (q : Finset V → ℕ) (hq : SubmodularNat q)
    (hq0 : q ∅ = 0) (T U : Finset V)
    (hmin : (constraintMatroid q hq hq0 T).eRk (T : Set V) =
      ((q U + (T \ U).card : ℕ) : ℕ∞)) {e : V} (he : e ∈ T \ U) :
    (constraintMatroid q hq hq0 T).IsColoop e := by
  let M := constraintMatroid q hq hq0 T
  apply Matroid.isColoop_iff_forall_mem_isBase.mpr
  intro J hJ
  by_contra heJ
  let JF := finiteSet J
  have hJF : M.Indep (JF : Set V) := by
    rw [coe_finiteSet]
    exact hJ.indep
  obtain ⟨hJT, hfeas⟩ := (constraintMatroid_indep q hq hq0 T JF).mp hJF
  have hcard : JF.card = q U + (T \ U).card := by
    have hc := hJ.encard_eq_eRank
    have hjc : J.encard = (JF.card : ℕ∞) := by
      rw [← coe_finiteSet J, Set.encard_coe_eq_coe_finsetCard]
    rw [hjc, ← M.eRk_ground] at hc
    change (JF.card : ℕ∞) = M.eRk (T : Set V) at hc
    rw [hmin] at hc
    exact_mod_cast hc
  have hss : JF \ U ⊂ T \ U := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.sdiff_subset_sdiff hJT (le_refl U), ?_⟩
    intro heq
    have hm : e ∈ JF \ U := by rwa [heq]
    exact heJ ((mem_finiteSet J e).mp (Finset.mem_sdiff.mp hm).1)
  have hc := Finset.card_lt_card hss
  have hf := hfeas U
  have heq := Finset.card_inter_add_card_sdiff JF U
  omega

end CommAlg.Polymatroid

end
end CheckedSource45

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "46: CommAlg.Polymatroid.KoszulRankArithmetic\n"

/-! ## Source: CommAlg.Polymatroid.KoszulRankArithmetic -/
section CheckedSource46

/-!
# Exact arithmetic of the Koszul deletion constraints

These identities retain natural-valued exponents throughout. Every subtraction
in the deletion slack is justified by actual lower-inequality membership.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def deletionSlack (g : RankFunction V) (a : Exponent V) (U : Finset V) : ℕ :=
  subsetSum a U - g.lower U

theorem deletionSlack_add_lower (g : RankFunction V) {a : Exponent V}
    (ha : LowerFeasible g.lower a) (U : Finset V) :
    deletionSlack g a U + g.lower U = subsetSum a U :=
  Nat.sub_add_cancel (ha U)

@[simp] theorem deletionSlack_empty (g : RankFunction V) (a : Exponent V) :
    deletionSlack g a ∅ = 0 := by simp [deletionSlack]

theorem deletionSlack_submodular (g : RankFunction V) {a : Exponent V}
    (ha : LowerFeasible g.lower a) : SubmodularNat (deletionSlack g a) := by
  intro U W
  have hMod := subsetSum_union_inter a U W
  have hSuper := g.lower_supermodular U W
  have hU := deletionSlack_add_lower g ha U
  have hW := deletionSlack_add_lower g ha W
  have hUnion := deletionSlack_add_lower g ha (U ∪ W)
  have hInter := deletionSlack_add_lower g ha (U ∩ W)
  omega

theorem deletionSlack_univ (g : RankFunction V) {a : Exponent V} {i : ℕ}
    (hDegree : a.degree = g univ + i) : deletionSlack g a univ = i := by
  simp only [deletionSlack, subsetSum_univ, RankFunction.lower_univ, hDegree,
    Nat.add_sub_cancel_left]

theorem deletionSlack_add_complement (g : RankFunction V) {a : Exponent V} {i : ℕ}
    (ha : LowerFeasible g.lower a) (hDegree : a.degree = g univ + i) (U : Finset V) :
    deletionSlack g a U + subsetSum a Uᶜ = i + g Uᶜ := by
  have hSlack := deletionSlack_add_lower g ha U
  have hLower := g.lower_add_compl U
  have hSum := subsetSum_add_compl a U
  omega

theorem card_erase_sdiff_add_indicator (T U : Finset V) {j : V} (hj : j ∈ T) :
    ((T.erase j) \ U).card + (if j ∈ Uᶜ then 1 else 0) = (T ∩ Uᶜ).card := by
  rw [Finset.erase_sdiff_comm]
  have hSet : T \ U = T ∩ Uᶜ := by ext x; simp
  rw [hSet]
  by_cases hjU : j ∈ Uᶜ
  · rw [if_pos hjU]
    exact Finset.card_erase_add_one (Finset.mem_inter.mpr ⟨hj, hjU⟩)
  · rw [if_neg hjU, Nat.add_zero, Finset.erase_eq_of_notMem (by simp [hjU])]

/-- A rank-formula cost is at least the target degree precisely when the
support-predecessor exponent satisfies the corresponding one-unit inequality. -/
theorem deletion_cost_ge_iff_supportPred (g : RankFunction V) {a : Exponent V} {i : ℕ}
    (ha : LowerFeasible g.lower a) (hDegree : a.degree = g univ + i)
    {j : V} (hj : j ∈ a.support) (U : Finset V) :
    i ≤ deletionSlack g a U + ((a.support.erase j) \ U).card ↔
      subsetSum (supportPred a) Uᶜ + (if j ∈ Uᶜ then 1 else 0) ≤ g Uᶜ := by
  have hSlack := deletionSlack_add_complement g ha hDegree U
  have hCard := card_erase_sdiff_add_indicator a.support U hj
  have hPred := subsetSum_supportPred a Uᶜ
  rw [Finset.inter_comm Uᶜ a.support] at hPred
  omega

theorem all_deletion_costs_ge_iff (g : RankFunction V) {a : Exponent V} {i : ℕ}
    (ha : LowerFeasible g.lower a) (hDegree : a.degree = g univ + i) :
    (∀ j ∈ a.support, ∀ U, i ≤ deletionSlack g a U + ((a.support.erase j) \ U).card) ↔
      (∀ j ∈ a.support, ∀ A,
        subsetSum (supportPred a) A + (if j ∈ A then 1 else 0) ≤ g A) := by
  constructor
  · intro h j hj A
    simpa only [compl_compl] using
      (deletion_cost_ge_iff_supportPred g ha hDegree hj Aᶜ).mp (h j hj Aᶜ)
  · intro h j hj U
    exact (deletion_cost_ge_iff_supportPred g ha hDegree hj U).mpr (h j hj Uᶜ)

theorem supportPred_indicator_bounds_iff (g : RankFunction V) (hg : g.Active)
    (a : Exponent V) :
    (∀ j ∈ a.support, ∀ A,
      subsetSum (supportPred a) A + (if j ∈ A then 1 else 0) ≤ g A) ↔
      (∀ A, A.Nonempty → subsetSum (supportPred a) A ≤ g A - 1) := by
  constructor
  · intro h A hA
    by_cases hSupport : (A ∩ a.support).Nonempty
    · obtain ⟨j, hj⟩ := hSupport
      obtain ⟨hjA, hjSupport⟩ := Finset.mem_inter.mp hj
      have hb := h j hjSupport A
      rw [if_pos hjA] at hb
      omega
    · have hEmpty : A ∩ a.support = ∅ := Finset.not_nonempty_iff_eq_empty.mp hSupport
      have hSum := subsetSum_supportPred_inter a A
      rw [hEmpty, subsetSum_empty] at hSum
      omega
  · intro h j hj A
    by_cases hjA : j ∈ A
    · have hA : A.Nonempty := ⟨j, hjA⟩
      have hb := h A hA
      have hgA := hg A hA
      rw [if_pos hjA]
      omega
    · rw [if_neg hjA, Nat.add_zero]
      by_cases hA : A.Nonempty
      · exact (h A hA).trans (Nat.sub_le _ _)
      · have he := Finset.not_nonempty_iff_eq_empty.mp hA
        simp [he]

end CommAlg.Polymatroid

end
end CheckedSource46

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "47: CommAlg.Matroid.MinorInduction\n"

/-! ## Source: CommAlg.Matroid.MinorInduction -/
section CheckedSource47


/-!
# Finite matroid deletion and contraction for homology induction

All minors are Mathlib's actual matroids. The natural rank is the finite value
of Mathlib's extended-natural rank, and every numerical formula is derived
from base cardinalities.
-/

noncomputable section

@[expose] public section

open scoped Matroid

namespace CommAlg.Matroid

open Classical Set

variable {V : Type*} {M : _root_.Matroid V} {e : V} {I : Set V}

def rank (M : _root_.Matroid V) : ℕ := M.eRank.toNat

def NoColoops (M : _root_.Matroid V) : Prop := ∀ e, ¬ M.IsColoop e

theorem rank_eq_ncard_of_isBase {B : Set V} (hB : M.IsBase B) : rank M = B.ncard := by
  exact (congrArg ENat.toNat hB.encard_eq_eRank).symm

theorem rank_delete_of_not_isColoop (he : ¬ M.IsColoop e) :
    rank (M ＼ ({e} : Set V)) = rank M := by
  have hS : M.Spanning (M.E \ {e}) := by
    by_contra h
    exact he (_root_.Matroid.isColoop_iff_sdiff_not_spanning.mpr h)
  exact congrArg ENat.toNat hS.eRank_restrict

theorem NoColoops.contract {C : Set V} (hM : NoColoops M) : NoColoops (M ／ C) := by
  intro a ha
  exact hM a (_root_.Matroid.contract_isColoop_iff.mp ha).1

theorem noColoops_iff_coloops_eq_empty : NoColoops M ↔ M.coloops = ∅ := by
  simp [NoColoops, Set.eq_empty_iff_forall_notMem,
    ← _root_.Matroid.isColoop_iff_mem_coloops]

theorem coloop_insert_indep (he : M.IsColoop e) (hI : M.Indep I) :
    M.Indep (insert e I) := he.insert_indep_of_indep hI

section Finite

variable [Finite V]

theorem indep_ncard_le_rank (hI : M.Indep I) : I.ncard ≤ rank M := by
  obtain ⟨B, hB, hIB⟩ := hI.exists_isBase_superset
  rw [rank_eq_ncard_of_isBase hB]
  exact Set.ncard_le_ncard hIB

theorem rank_delete_le (M : _root_.Matroid V) (D : Set V) :
    rank (M ＼ D) ≤ rank M := by
  obtain ⟨B, hB⟩ := (M ＼ D).exists_isBase
  rw [rank_eq_ncard_of_isBase hB]
  exact indep_ncard_le_rank hB.indep.of_delete

theorem exists_nonloop_of_rank_pos (hr : 0 < rank M) : ∃ e, M.IsNonloop e := by
  obtain ⟨B, hB⟩ := M.exists_isBase
  rw [rank_eq_ncard_of_isBase hB] at hr
  obtain ⟨e, he⟩ := (Set.ncard_pos (Set.toFinite B)).mp hr
  exact ⟨e, hB.indep.isNonloop_of_mem he⟩

theorem rank_pos_of_nonloop (he : M.IsNonloop e) : 0 < rank M := by
  have h := indep_ncard_le_rank he.indep
  have h' : 1 ≤ rank M := by simpa using h
  omega

theorem rank_pos_iff_exists_nonloop : 0 < rank M ↔ ∃ e, M.IsNonloop e :=
  ⟨exists_nonloop_of_rank_pos, fun ⟨_, he⟩ => rank_pos_of_nonloop he⟩

theorem indep_eq_empty_of_rank_zero (hr : rank M = 0) (hI : M.Indep I) : I = ∅ := by
  have h := indep_ncard_le_rank hI
  rw [hr] at h
  exact (Set.ncard_eq_zero (Set.toFinite I)).mp (Nat.eq_zero_of_le_zero h)

theorem rank_contract_add_one (he : M.IsNonloop e) :
    rank (M ／ ({e} : Set V)) + 1 = rank M := by
  obtain ⟨B, hB⟩ := (M ／ ({e} : Set V)).exists_isBase
  obtain ⟨hBM, hBe⟩ := he.indep.contract_isBase_iff.mp hB
  have heB : e ∉ B := Set.disjoint_singleton_right.mp hBe
  rw [rank_eq_ncard_of_isBase hB, rank_eq_ncard_of_isBase hBM,
    Set.union_singleton, Set.ncard_insert_of_notMem heB]

theorem rank_contract_eq_sub_one (he : M.IsNonloop e) :
    rank (M ／ ({e} : Set V)) = rank M - 1 := by
  have h := rank_contract_add_one he
  omega

theorem rank_delete_add_one_of_isColoop (he : M.IsColoop e) :
    rank (M ＼ ({e} : Set V)) + 1 = rank M := by
  have hC : ({e} : Set V) ⊆ M.coloops := Set.singleton_subset_iff.mpr he
  rw [← _root_.Matroid.contract_eq_delete_of_subset_coloops hC]
  exact rank_contract_add_one he.isNonloop

/-- When the ground set is nonempty and rank is at most `i`, rank `i` with
no coloops is equivalent to preservation of rank `i` after every singleton
deletion. This includes `i = 0`. -/
theorem rank_eq_and_noColoops_iff_delete_rank (M : _root_.Matroid V) (i : ℕ)
    (hE : M.E.Nonempty) (hr : rank M ≤ i) :
    (rank M = i ∧ NoColoops M) ↔
      ∀ e ∈ M.E, rank (M ＼ ({e} : Set V)) = i := by
  constructor
  · rintro ⟨hRank, hM⟩ e he
    exact (rank_delete_of_not_isColoop (hM e)).trans hRank
  · intro h
    obtain ⟨e, he⟩ := hE
    have hLower := rank_delete_le M ({e} : Set V)
    rw [h e he] at hLower
    have hRank : rank M = i := Nat.le_antisymm hr hLower
    refine ⟨hRank, ?_⟩
    intro f hf
    have hDelete := h f hf.mem_ground
    have hDrop := rank_delete_add_one_of_isColoop hf
    omega

theorem delete_ground_ncard_add_one (he : e ∈ M.E) :
    (M ＼ ({e} : Set V)).E.ncard + 1 = M.E.ncard := by
  exact Set.ncard_sdiff_singleton_add_one he

theorem contract_ground_ncard_add_one (he : e ∈ M.E) :
    (M ／ ({e} : Set V)).E.ncard + 1 = M.E.ncard := by
  exact Set.ncard_sdiff_singleton_add_one he

theorem delete_ground_ncard_lt (he : e ∈ M.E) :
    (M ＼ ({e} : Set V)).E.ncard < M.E.ncard := by
  have h := delete_ground_ncard_add_one he
  omega

theorem contract_ground_ncard_lt (he : e ∈ M.E) :
    (M ／ ({e} : Set V)).E.ncard < M.E.ncard := by
  have h := contract_ground_ncard_add_one he
  omega

end Finite

section Finset

variable [DecidableEq V]

/-- Deletion is exactly deletion of a label in the independence complex. -/
theorem delete_indep_finset_iff (s : Finset V) :
    (M ＼ ({e} : Set V)).Indep (s : Set V) ↔ M.Indep (s : Set V) ∧ e ∉ s := by
  simp only [_root_.Matroid.delete_indep_iff, Set.disjoint_singleton_right,
    Finset.mem_coe]

/-- Contraction at a nonloop is exactly the link in the independence complex. -/
theorem contract_indep_finset_iff (he : M.IsNonloop e) (s : Finset V) :
    (M ／ ({e} : Set V)).Indep (s : Set V) ↔
      M.Indep ((insert e s : Finset V) : Set V) ∧ e ∉ s := by
  simpa only [Finset.coe_insert, Finset.mem_coe, and_comm] using
    he.contractElem_indep_iff (I := (s : Set V))

theorem coloop_insert_indep_finset (he : M.IsColoop e) {s : Finset V}
    (hs : M.Indep (s : Set V)) : M.Indep ((insert e s : Finset V) : Set V) := by
  simpa only [Finset.coe_insert] using he.insert_indep_of_indep hs

variable [Finite V]

theorem indep_card_le_rank {s : Finset V} (hs : M.Indep (s : Set V)) :
    s.card ≤ rank M := by
  simpa using indep_ncard_le_rank hs

theorem indep_finset_eq_empty_of_rank_zero (hr : rank M = 0) {s : Finset V}
    (hs : M.Indep (s : Set V)) : s = ∅ := by
  have h := indep_card_le_rank hs
  rw [hr] at h
  exact Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero h)

end Finset

end CommAlg.Matroid

end
end
end CheckedSource47

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "48: CommAlg.Matroid.IndependenceHomology\n"

/-! ## Source: CommAlg.Matroid.IndependenceHomology -/
section CheckedSource48

/-!
# Homology of every finite matroid independence complex

The augmented chain complex is the genuine exterior-basis complex from
`CommAlg.Simplicial.Chains`. Induction removes an actual ground element,
using actual deletion and contraction matroids. No shellability, homology
concentration, or top-homology hypothesis is built into the statement.
-/

noncomputable section

open scoped Matroid

namespace CommAlg.Matroid

open Classical
open CommAlg.Simplicial

variable {V k : Type*} [Fintype V] [LinearOrder V] [CommRing k]

def independenceFaces (M : _root_.Matroid V) (s : Finset V) : Prop :=
  M.Indep (s : Set V)

omit [Fintype V] [LinearOrder V] in
theorem independenceFaces_downward (M : _root_.Matroid V) :
    Downward (independenceFaces M) := by
  intro s t hts hs
  exact hs.subset (by simpa using hts)

omit [Fintype V] [LinearOrder V] in
@[simp] theorem independenceFaces_empty (M : _root_.Matroid V) :
    independenceFaces M ∅ := by
  simpa only [independenceFaces, Finset.coe_empty] using M.empty_indep

omit [Fintype V] in
theorem independenceFaces_delete (M : _root_.Matroid V) (e : V) :
    independenceFaces (M ＼ ({e} : Set V)) = deletion (independenceFaces M) e := by
  funext s
  exact propext (delete_indep_finset_iff s)

omit [Fintype V] in
theorem independenceFaces_contract (M : _root_.Matroid V) {e : V} (he : M.IsNonloop e) :
    independenceFaces (M ／ ({e} : Set V)) = link (independenceFaces M) e := by
  funext s
  exact propext (contract_indep_finset_iff he s)

theorem independence_exactIn_of_coloop (M : _root_.Matroid V) {e : V}
    (he : M.IsColoop e) (i : ℕ) : ExactIn (k := k) (independenceFaces M) i := by
  apply exactIn_of_cone e
  intro s hs
  exact coloop_insert_indep_finset he hs

private theorem independence_exactIn_induction (n : ℕ) :
    ∀ M : _root_.Matroid V, M.E.ncard = n →
      ∀ i : ℕ, i ≠ rank M → ExactIn (k := k) (independenceFaces M) i := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro M hCard i hi
    by_cases hr : rank M = 0
    · apply exactIn_of_no_face
      intro s hs
      have hs0 : s = ∅ := indep_finset_eq_empty_of_rank_zero hr hs
      rw [hs0, Finset.card_empty]
      simpa only [hr, ne_eq, eq_comm] using hi
    by_cases hColoop : ∃ e, M.IsColoop e
    · obtain ⟨e, he⟩ := hColoop
      exact independence_exactIn_of_coloop M he i
    obtain ⟨e, he⟩ := exists_nonloop_of_rank_pos (Nat.pos_of_ne_zero hr)
    have hne : ¬ M.IsColoop e := fun h => hColoop ⟨e, h⟩
    have hDeleteRank := rank_delete_of_not_isColoop hne
    have hContractRank := rank_contract_add_one he
    have hDeleteCard : (M ＼ ({e} : Set V)).E.ncard < n := by
      rw [← hCard]
      exact delete_ground_ncard_lt he.mem_ground
    have hContractCard : (M ／ ({e} : Set V)).E.ncard < n := by
      rw [← hCard]
      exact contract_ground_ncard_lt he.mem_ground
    cases i with
    | zero =>
      apply exactIn_zero_of_vertex e
      simpa only [independenceFaces, Finset.coe_singleton] using he.indep
    | succ j =>
      have hDelete : ExactIn (k := k) (independenceFaces (M ＼ ({e} : Set V))) (j + 1) :=
        ih _ hDeleteCard _ rfl _ (by omega)
      have hContract : ExactIn (k := k) (independenceFaces (M ／ ({e} : Set V))) j :=
        ih _ hContractCard _ rfl _ (by omega)
      apply exactIn_of_deletion_link (independenceFaces_downward M) e j
      · rwa [← independenceFaces_delete M e]
      · rwa [← independenceFaces_contract M he]

/-- Every reduced homology group of a finite matroid independence complex
outside degree `rank M - 1` vanishes, expressed by explicit chain fillings.
The empty face has augmented chain degree zero. -/
theorem independence_exactIn_of_ne_rank (M : _root_.Matroid V) (i : ℕ)
    (hi : i ≠ rank M) : ExactIn (k := k) (independenceFaces M) i :=
  independence_exactIn_induction M.E.ncard M rfl i hi

section Nontrivial

variable [Nontrivial k]

private theorem independence_nonzero_top_induction (n : ℕ) :
    ∀ M : _root_.Matroid V, M.E.ncard = n → NoColoops M →
      NonzeroHomology (k := k) (independenceFaces M) (rank M) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro M hCard hM
    by_cases hr : rank M = 0
    · rw [hr]
      apply nonzeroHomology_zero_of_only_empty (independenceFaces_empty M)
      intro s hs
      exact indep_finset_eq_empty_of_rank_zero hr hs
    obtain ⟨e, he⟩ := exists_nonloop_of_rank_pos (Nat.pos_of_ne_zero hr)
    have hDeleteRank := rank_delete_of_not_isColoop (hM e)
    have hContractRank := rank_contract_add_one he
    have hContractCard : (M ／ ({e} : Set V)).E.ncard < n := by
      rw [← hCard]
      exact contract_ground_ncard_lt he.mem_ground
    have hContract : NonzeroHomology (k := k)
        (independenceFaces (M ／ ({e} : Set V))) (rank (M ／ ({e} : Set V))) :=
      ih _ hContractCard _ rfl hM.contract
    have hDelete : ExactIn (k := k) (independenceFaces (M ＼ ({e} : Set V)))
        (rank (M ／ ({e} : Set V))) :=
      independence_exactIn_of_ne_rank _ _ (by omega)
    have hTop := nonzeroHomology_of_link (independenceFaces_downward M) e
      (rank (M ／ ({e} : Set V)))
      (by rwa [← independenceFaces_delete M e])
      (by rwa [← independenceFaces_contract M he])
    rwa [hContractRank] at hTop

/-- A finite matroid with no coloops has an actual nonboundary cycle in its
top augmented chain degree, over every nontrivial commutative coefficient ring. -/
theorem independence_nonzero_top (M : _root_.Matroid V) (hM : NoColoops M) :
    NonzeroHomology (k := k) (independenceFaces M) (rank M) :=
  independence_nonzero_top_induction M.E.ncard M rfl hM

/-- Full homology detection for every finite matroid, including rank zero,
loops, coloops, and all coefficient characteristics. -/
theorem independence_nonzeroHomology_iff (M : _root_.Matroid V) (i : ℕ) :
    NonzeroHomology (k := k) (independenceFaces M) i ↔ i = rank M ∧ NoColoops M := by
  constructor
  · intro h
    have hNot := (nonzeroHomology_iff_not_exactIn _ _).mp h
    refine ⟨?_, ?_⟩
    · by_contra hi
      exact hNot (independence_exactIn_of_ne_rank M i hi)
    · intro e he
      exact hNot (independence_exactIn_of_coloop M he i)
  · rintro ⟨rfl, hM⟩
    exact independence_nonzero_top M hM

theorem independence_exactIn_iff (M : _root_.Matroid V) (i : ℕ) :
    ExactIn (k := k) (independenceFaces M) i ↔ i ≠ rank M ∨ ¬ NoColoops M := by
  have h := independence_nonzeroHomology_iff (k := k) M i
  rw [nonzeroHomology_iff_not_exactIn] at h
  tauto

end Nontrivial

end CommAlg.Matroid

end
end CheckedSource48

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "49: CommAlg.Polymatroid.KoszulRankCriterion\n"

/-! ## Source: CommAlg.Polymatroid.KoszulRankCriterion -/
section CheckedSource49

/-!
# Exact rank and coloop detection for the Koszul matroid

The matroid is built from the actual nonnegative deletion slacks of a monomial
satisfying the lower rank inequalities. Its rank and coloops are Mathlib's
notions, and its homology is the actual augmented exterior-chain homology.
-/

noncomputable section

open scoped Matroid

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def koszulConstraintMatroid (g : RankFunction V) (a : Exponent V)
    (ha : LowerFeasible g.lower a) : _root_.Matroid V :=
  constraintMatroid (deletionSlack g a) (deletionSlack_submodular g ha)
    (deletionSlack_empty g a) a.support

@[simp] theorem koszulConstraintMatroid_ground (g : RankFunction V) (a : Exponent V)
    (ha : LowerFeasible g.lower a) :
    (koszulConstraintMatroid g a ha).E = (a.support : Set V) := rfl

@[simp] theorem koszulConstraintMatroid_indep (g : RankFunction V) (a : Exponent V)
    (ha : LowerFeasible g.lower a) (s : Finset V) :
    (koszulConstraintMatroid g a ha).Indep (s : Set V) ↔
      s ⊆ a.support ∧ ∀ U, (s ∩ U).card ≤ deletionSlack g a U :=
  constraintMatroid_indep _ _ _ _ _

theorem le_koszulConstraint_rank (g : RankFunction V) (a : Exponent V)
    (ha : LowerFeasible g.lower a) (R : Finset V) (hR : R ⊆ a.support) (i : ℕ) :
    i ≤ ((koszulConstraintMatroid g a ha).eRk (R : Set V)).toNat ↔
      ∀ U, i ≤ deletionSlack g a U + (R \ U).card := by
  obtain ⟨U, hU, hmin⟩ := constraint_rank_certificate (deletionSlack g a)
    (deletionSlack_submodular g ha) (deletionSlack_empty g a) a.support R hR
  change i ≤ ((constraintMatroid _ _ _ _).eRk (R : Set V)).toNat ↔ _
  rw [hU, ENat.toNat_natCast]
  exact ⟨fun h W => h.trans (hmin W), fun h => h U⟩

theorem koszulConstraint_rank_le (g : RankFunction V) {a : Exponent V} {i : ℕ}
    (ha : LowerFeasible g.lower a) (hDegree : a.degree = g univ + i) :
    CommAlg.Matroid.rank (koszulConstraintMatroid g a ha) ≤ i := by
  obtain ⟨U, hU, hmin⟩ := constraint_rank_certificate (deletionSlack g a)
    (deletionSlack_submodular g ha) (deletionSlack_empty g a)
    a.support a.support le_rfl
  have hBound := hmin univ
  have hBound' : deletionSlack g a U + (a.support \ U).card ≤ i := by
    simpa only [deletionSlack_univ g hDegree, Finset.sdiff_eq_empty_iff_subset.mpr
      (Finset.subset_univ a.support), Finset.card_empty, Nat.add_zero] using hBound
  have hRank : CommAlg.Matroid.rank (koszulConstraintMatroid g a ha) =
      deletionSlack g a U + (a.support \ U).card := by
    unfold CommAlg.Matroid.rank
    rw [← _root_.Matroid.eRk_ground]
    change ((constraintMatroid _ _ _ _).eRk (a.support : Set V)).toNat = _
    rw [hU, ENat.toNat_natCast]
  rwa [hRank]

theorem koszulConstraint_delete_rank_eq (g : RankFunction V) (a : Exponent V)
    (ha : LowerFeasible g.lower a) (j : V) :
    CommAlg.Matroid.rank ((koszulConstraintMatroid g a ha) ＼ ({j} : Set V)) =
      ((koszulConstraintMatroid g a ha).eRk ((a.support.erase j : Finset V) : Set V)).toNat := by
  have hGround : (koszulConstraintMatroid g a ha).E \ {j} =
      ((a.support.erase j : Finset V) : Set V) := by
    ext x
    simp only [koszulConstraintMatroid_ground, Set.mem_sdiff, Finset.mem_coe,
      Set.mem_singleton_iff, Finset.mem_erase]
    tauto
  unfold CommAlg.Matroid.rank
  rw [_root_.Matroid.delete_eq_restrict, _root_.Matroid.eRank_restrict, hGround]

theorem le_koszulConstraint_delete_rank (g : RankFunction V) (a : Exponent V)
    (ha : LowerFeasible g.lower a) (j : V) (i : ℕ) :
    i ≤ CommAlg.Matroid.rank ((koszulConstraintMatroid g a ha) ＼ ({j} : Set V)) ↔
      ∀ U, i ≤ deletionSlack g a U + ((a.support.erase j) \ U).card := by
  rw [koszulConstraint_delete_rank_eq]
  exact le_koszulConstraint_rank g a ha (a.support.erase j) (Finset.erase_subset _ _) i

/-- The full equivalence (3.1)--(3.3) for the actual Koszul constraint matroid. -/
theorem koszulConstraint_rank_and_noColoops_iff (g : RankFunction V) (hg : g.Active)
    {a : Exponent V} {i : ℕ} (ha : LowerFeasible g.lower a)
    (hDegree : a.degree = g univ + i) (hSupport : a.support.Nonempty) :
    (CommAlg.Matroid.rank (koszulConstraintMatroid g a ha) = i ∧
      CommAlg.Matroid.NoColoops (koszulConstraintMatroid g a ha)) ↔
      ∀ A, A.Nonempty → subsetSum (supportPred a) A ≤ g A - 1 := by
  let M := koszulConstraintMatroid g a ha
  have hRank := koszulConstraint_rank_le g ha hDegree
  have hGround : M.E.Nonempty := by
    simpa only [M, koszulConstraintMatroid_ground, Finset.coe_nonempty] using hSupport
  have hDelete := CommAlg.Matroid.rank_eq_and_noColoops_iff_delete_rank M i hGround hRank
  have hStep : (CommAlg.Matroid.rank M = i ∧ CommAlg.Matroid.NoColoops M) ↔
      ∀ j ∈ a.support, ∀ U,
        i ≤ deletionSlack g a U + ((a.support.erase j) \ U).card := by
    rw [hDelete]
    constructor
    · intro h j hj
      apply (le_koszulConstraint_delete_rank g a ha j i).mp
      exact le_of_eq (h j hj).symm
    · intro h j hj
      have hLower := (le_koszulConstraint_delete_rank g a ha j i).mpr (h j hj)
      have hUpper := (CommAlg.Matroid.rank_delete_le M ({j} : Set V)).trans hRank
      exact Nat.le_antisymm hUpper hLower
  exact hStep.trans ((all_deletion_costs_ge_iff g ha hDegree).trans
    (supportPred_indicator_bounds_iff g hg a))

omit [Fintype V] [DecidableEq V] in
theorem support_nonempty_of_degree_pos {a : Exponent V} (ha : 0 < a.degree) :
    a.support.Nonempty := by
  by_contra h
  have he : a.support = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
  have hz : a = 0 := Finsupp.support_eq_empty.mp he
  simp [hz] at ha

/-- The positive-rank case used in the paper automatically has nonempty
support; no support condition is imposed on the theorem's input. -/
theorem koszulConstraint_rank_and_noColoops_iff_of_rank_pos
    (g : RankFunction V) (hg : g.Active) (hd : 0 < g univ)
    {a : Exponent V} {i : ℕ} (ha : LowerFeasible g.lower a)
    (hDegree : a.degree = g univ + i) :
    (CommAlg.Matroid.rank (koszulConstraintMatroid g a ha) = i ∧
      CommAlg.Matroid.NoColoops (koszulConstraintMatroid g a ha)) ↔
      ∀ A, A.Nonempty → subsetSum (supportPred a) A ≤ g A - 1 :=
  koszulConstraint_rank_and_noColoops_iff g hg ha hDegree
    (support_nonempty_of_degree_pos (by omega))

/-- No coloops forces a minimizing rank certificate to contain the whole
support. Consequently the actual rank is exactly the excess total degree.
This requires neither active variables nor positive total rank. -/
theorem koszulConstraint_rank_eq_excess_of_noColoops (g : RankFunction V)
    {a : Exponent V} (ha : LowerFeasible g.lower a)
    (hNo : CommAlg.Matroid.NoColoops (koszulConstraintMatroid g a ha)) :
    CommAlg.Matroid.rank (koszulConstraintMatroid g a ha) = a.degree - g univ := by
  obtain ⟨U, hU, hmin⟩ := constraint_rank_certificate (deletionSlack g a)
    (deletionSlack_submodular g ha) (deletionSlack_empty g a)
    a.support a.support le_rfl
  have hSupport : a.support ⊆ U := by
    intro j hj
    by_contra hjU
    exact hNo j (constraint_isColoop_of_minimizer (deletionSlack g a)
      (deletionSlack_submodular g ha) (deletionSlack_empty g a) a.support U hU
      (Finset.mem_sdiff.mpr ⟨hj, hjU⟩))
  have hRank : CommAlg.Matroid.rank (koszulConstraintMatroid g a ha) =
      deletionSlack g a U := by
    unfold CommAlg.Matroid.rank
    rw [← _root_.Matroid.eRk_ground]
    change ((constraintMatroid _ _ _ _).eRk (a.support : Set V)).toNat = _
    rw [hU, Finset.sdiff_eq_empty_iff_subset.mpr hSupport, Finset.card_empty,
      Nat.add_zero, ENat.toNat_natCast]
  have hZero : subsetSum a Uᶜ = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    exact Finsupp.notMem_support_iff.mp (fun h => (Finset.mem_compl.mp hj) (hSupport h))
  have hSum := subsetSum_add_compl a U
  rw [hZero, Nat.add_zero] at hSum
  have hSlack := deletionSlack_add_lower g ha U
  have hLower := g.lower_le U
  have hTotal := ha univ
  simp only [RankFunction.lower_univ, subsetSum_univ] at hTotal
  have hDegree : a.degree = g univ + (a.degree - g univ) := by omega
  have hUpper := koszulConstraint_rank_le g ha hDegree
  omega

section Homology

variable [LinearOrder V] {k : Type*} [CommRing k] [Nontrivial k]

/-- Field-independent nonvanishing of the genuine augmented homology of the
Koszul matroid, expressed by the exact upper subset inequalities (3.6). -/
theorem koszulConstraint_nonzeroHomology_iff_augmented (g : RankFunction V)
    (hg : g.Active) (hd : 0 < g univ) {a : Exponent V} {i : ℕ}
    (ha : LowerFeasible g.lower a) (hDegree : a.degree = g univ + i) :
    CommAlg.Simplicial.NonzeroHomology (k := k)
      (CommAlg.Matroid.independenceFaces (koszulConstraintMatroid g a ha)) i ↔
      ∀ A, subsetSum a A ≤ augmentedPartitionRank g A := by
  rw [CommAlg.Matroid.independence_nonzeroHomology_iff]
  have h := koszulConstraint_rank_and_noColoops_iff_of_rank_pos g hg hd ha hDegree
  rw [eq_comm] at h
  exact h.trans (supportPred_nonempty_bounds_iff_augmented g a)

/-- All-degree concentration follows directly from the actual constraint
matroid, without assuming a linear-resolution theorem. -/
theorem koszulConstraint_nonzeroHomology_degree (g : RankFunction V)
    {a : Exponent V} (ha : LowerFeasible g.lower a) {i : ℕ}
    (h : CommAlg.Simplicial.NonzeroHomology (k := k)
      (CommAlg.Matroid.independenceFaces (koszulConstraintMatroid g a ha)) i) :
    a.degree = g univ + i := by
  obtain ⟨hRank, hNo⟩ := (CommAlg.Matroid.independence_nonzeroHomology_iff _ _).mp h
  have hExcess := koszulConstraint_rank_eq_excess_of_noColoops g ha hNo
  have hTotal := ha univ
  simp only [RankFunction.lower_univ, subsetSum_univ] at hTotal
  omega

end Homology

end CommAlg.Polymatroid

end
end CheckedSource49

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "50: CommAlg.KoszulComplex.FaceMatroid\n"

/-! ## Source: CommAlg.KoszulComplex.FaceMatroid -/
section CheckedSource50

/-! # The actual Koszul faces are the constraint matroid's independent sets

The proof starts from the monomial membership condition in `koszulFaces`.
It proves both the support condition and the exact simultaneous-deletion
inequalities, before identifying any homology groups.
-/

noncomputable section

namespace CommAlg.Koszul

open Classical Finset CommAlg.Polymatroid

variable {V : Type*} [Fintype V] [LinearOrder V]

theorem faceExponent_le_iff_subset_support (s : Finset V) (a : Exponent V) :
    faceExponent s ≤ a ↔ s ⊆ a.support := by
  constructor
  · intro h j hj
    have hb := h j
    simp only [faceExponent_apply, if_pos hj] at hb
    exact Finsupp.mem_support_iff.mpr (by omega)
  · intro h j
    by_cases hj : j ∈ s
    · have hb := Finsupp.mem_support_iff.mp (h hj)
      simp only [faceExponent_apply, if_pos hj]
      omega
    · simp [hj]

theorem subsetSum_faceExponent (s U : Finset V) :
    subsetSum (faceExponent s) U = (s ∩ U).card := by
  simp only [subsetSum, faceExponent_apply, Finset.sum_boole, Finset.filter_mem_eq_inter,
    Nat.cast_id, Finset.inter_comm]

theorem subsetSum_sub_faceExponent {s : Finset V} {a : Exponent V}
    (ha : faceExponent s ≤ a) (U : Finset V) :
    subsetSum (a - faceExponent s) U + (s ∩ U).card = subsetSum a U := by
  have he := tsub_add_cancel_of_le ha
  have hs := congrArg (fun b : Exponent V => subsetSum b U) he
  have hs' : subsetSum (a - faceExponent s) U + subsetSum (faceExponent s) U = subsetSum a U := by
    simpa only [subsetSum, Finsupp.add_apply, Finset.sum_add_distrib] using hs
  rwa [subsetSum_faceExponent] at hs'

theorem lowerFeasible_sub_faceExponent_iff (g : RankFunction V)
    {a : Exponent V} (ha : LowerFeasible g.lower a) {s : Finset V}
    (hs : faceExponent s ≤ a) :
    LowerFeasible g.lower (a - faceExponent s) ↔
      ∀ U, (s ∩ U).card ≤ deletionSlack g a U := by
  constructor
  · intro h U
    have hLower := h U
    have hSub := subsetSum_sub_faceExponent hs U
    have hSlack := deletionSlack_add_lower g ha U
    omega
  · intro h U
    have hBound := h U
    have hSub := subsetSum_sub_faceExponent hs U
    have hSlack := deletionSlack_add_lower g ha U
    omega

/-- Exact equality of the original upper Koszul complex's faces with the
independent sets of the actual finite constraint matroid. -/
theorem koszulFaces_eq_independenceFaces (B : Family V) (g : RankFunction V)
    (hB : ∀ a, Contains B a ↔ LowerFeasible g.lower a)
    (a : Exponent V) (ha : LowerFeasible g.lower a) :
    koszulFaces B a = CommAlg.Matroid.independenceFaces (koszulConstraintMatroid g a ha) := by
  funext s
  apply propext
  change (faceExponent s ≤ a ∧ Contains B (a - faceExponent s)) ↔
    (koszulConstraintMatroid g a ha).Indep (s : Set V)
  rw [koszulConstraintMatroid_indep]
  constructor
  · rintro ⟨hs, hb⟩
    exact ⟨(faceExponent_le_iff_subset_support s a).mp hs,
      (lowerFeasible_sub_faceExponent_iff g ha hs).mp ((hB _).mp hb)⟩
  · rintro ⟨hs, hb⟩
    have hs' := (faceExponent_le_iff_subset_support s a).mpr hs
    exact ⟨hs', (hB _).mpr ((lowerFeasible_sub_faceExponent_iff g ha hs').mpr hb)⟩

theorem koszulFaces_contains {B : Family V} {a : Exponent V} {s : Finset V}
    (hs : koszulFaces B a s) : Contains B a := by
  obtain ⟨b, hb, hba⟩ := hs.2
  exact ⟨b, hb, hba.trans tsub_le_self⟩

theorem koszulFaces_false_of_not_contains (B : Family V) (a : Exponent V)
    (ha : ¬ Contains B a) : koszulFaces B a = fun _ => False := by
  funext s
  exact propext ⟨fun h => ha (koszulFaces_contains h), False.elim⟩

end CommAlg.Koszul

end
end CheckedSource50

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "51: CommAlg.Polymatroid.RankBases\n"

/-! ## Source: CommAlg.Polymatroid.RankBases -/
section CheckedSource51

/-! # Finite integer base families and their actual polynomial ideals -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def IsRankBase (g : RankFunction V) (a : Exponent V) : Prop :=
  a.degree = g Finset.univ ∧ UpperFeasible g a

def constExponent (n : ℕ) : Exponent V := Finsupp.equivFunOnFinite.symm (fun _ => n)

@[simp] theorem constExponent_apply (n : ℕ) (i : V) : constExponent n i = n := rfl

def rankBases (g : RankFunction V) : Family V :=
  (Finset.Iic (constExponent (g Finset.univ))).filter (IsRankBase g)

@[simp] theorem mem_rankBases (g : RankFunction V) (a : Exponent V) :
    a ∈ rankBases g ↔ IsRankBase g a := by
  simp only [rankBases, Finset.mem_filter, Finset.mem_Iic]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  intro i
  exact (coordinate_le_degree a i).trans h.1.le

theorem subsetSum_add (a b : Exponent V) (U : Finset V) :
    subsetSum (a + b) U = subsetSum a U + subsetSum b U := by
  simp [subsetSum, Finset.sum_add_distrib]

theorem rankBases_equigenerated (g : RankFunction V) :
    Equigenerated (rankBases g) (g Finset.univ) := by
  intro a ha
  exact ((mem_rankBases g a).mp ha).1

theorem rankBases_nonempty (g : RankFunction V) : (rankBases g).Nonempty := by
  have hf : LowerFeasible g.lower (constExponent (g Finset.univ)) := by
    intro U
    by_cases hU : U.Nonempty
    · obtain ⟨i, hi⟩ := hU
      exact (g.lower_le U).trans (by
        simpa only [subsetSum, constExponent_apply] using
          Finset.single_le_sum (f := fun _ : V => g Finset.univ)
            (fun j _ => Nat.zero_le _) hi)
    · have he : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
      simp [he]
  obtain ⟨a, _, hadeg, ha⟩ := exists_lower_base_below g.lower_supermodular g.lower_empty
    g.lower_univ g.lower_le hf
  exact ⟨a, (mem_rankBases g a).mpr
    ⟨hadeg, (upperFeasible_iff_lowerFeasible g hadeg).mpr ha⟩⟩

theorem rankBases_polymatroidal (g : RankFunction V) : IsPolymatroidal (rankBases g) := by
  refine ⟨⟨g Finset.univ, rankBases_equigenerated g⟩, ?_⟩
  intro a ha b hb i hi
  have ha := (mem_rankBases g a).mp ha
  have hb := (mem_rankBases g b).mp hb
  have hla := (upperFeasible_iff_lowerFeasible g ha.1).mp ha.2
  have hlb := (upperFeasible_iff_lowerFeasible g hb.1).mp hb.2
  obtain ⟨j, hj, hex⟩ := feasible_exchange g.lower_supermodular hla hlb
    (ha.1.trans hb.1.symm) hi
  have hd := (exchange_degree a i j (by omega)).trans ha.1
  exact ⟨j, hj, (mem_rankBases g _).mpr
    ⟨hd, (upperFeasible_iff_lowerFeasible g hd).mpr hex⟩⟩

theorem contains_rankBases_iff (g : RankFunction V) (a : Exponent V) :
    Contains (rankBases g) a ↔ LowerFeasible g.lower a := by
  constructor
  · rintro ⟨b, hb, hba⟩ U
    have hb := (mem_rankBases g b).mp hb
    exact ((upperFeasible_iff_lowerFeasible g hb.1).mp hb.2 U).trans
      (Finset.sum_le_sum (fun i _ => hba i))
  · intro ha
    obtain ⟨b, hba, hbdeg, hb⟩ := exists_lower_base_below g.lower_supermodular g.lower_empty
      g.lower_univ g.lower_le ha
    exact ⟨b, (mem_rankBases g b).mpr
      ⟨hbdeg, (upperFeasible_iff_lowerFeasible g hbdeg).mpr hb⟩, hba⟩

theorem rankBases_canonical (B : Family V) (hBne : B.Nonempty) (d : ℕ)
    (hdeg : Equigenerated B d) (hB : IsPolymatroidal B) :
    rankBases (canonicalRank B hBne d hdeg hB) = B := by
  have htop : upperRank B Finset.univ = d := by
    obtain ⟨a, ha, he⟩ := upperRank_attained hBne Finset.univ
    simpa only [subsetSum_univ, hdeg a ha] using he.symm
  ext a
  rw [mem_rankBases, mem_iff_canonical_rank B hBne d hdeg hB]
  change (a.degree = upperRank B Finset.univ ∧ _) ↔ _
  rw [htop]
  rfl

def rankIdeal (k : Type*) [CommSemiring k] (g : RankFunction V) : Ideal (MvPolynomial V k) :=
  monomialIdeal k (rankBases g)

theorem monomial_mem_rankIdeal_iff (k : Type*) [CommSemiring k] [Nontrivial k]
    (g : RankFunction V) (a : Exponent V) :
    MvPolynomial.monomial a (1 : k) ∈ rankIdeal k g ↔ LowerFeasible g.lower a := by
  rw [rankIdeal, monomial_mem_iff, contains_rankBases_iff]

end CommAlg.Polymatroid

end
end CheckedSource51

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "52: CommAlg.Polymatroid.FiniteMinimum\n"

/-! ## Source: CommAlg.Polymatroid.FiniteMinimum -/
section CheckedSource52

/-! # Exact minima of nonempty finite families of natural numbers -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def finiteMinimum (f : ι → ℕ) : ℕ :=
  univ.inf' univ_nonempty f

theorem finiteMinimum_le (f : ι → ℕ) (j : ι) : finiteMinimum f ≤ f j :=
  Finset.inf'_le _ (mem_univ j)

theorem le_finiteMinimum {f : ι → ℕ} {n : ℕ} (h : ∀ j, n ≤ f j) :
    n ≤ finiteMinimum f := Finset.le_inf' _ _ (fun j _ => h j)

theorem finiteMinimum_attained (f : ι → ℕ) : ∃ j, f j = finiteMinimum f := by
  obtain ⟨j, _, hj⟩ := (Finset.inf'_le_iff univ_nonempty).mp
    (le_rfl : finiteMinimum f ≤ finiteMinimum f)
  exact ⟨j, le_antisymm hj (finiteMinimum_le f j)⟩

theorem finiteMinimum_mono {f g : ι → ℕ} (h : ∀ j, f j ≤ g j) :
    finiteMinimum f ≤ finiteMinimum g := by
  obtain ⟨j, hj⟩ := finiteMinimum_attained g
  exact ((finiteMinimum_le f j).trans (h j)).trans_eq hj

theorem finiteMinimum_add_const (f : ι → ℕ) (n : ℕ) :
    finiteMinimum (fun j => n + f j) = n + finiteMinimum f := by
  obtain ⟨j, hj⟩ := finiteMinimum_attained f
  apply le_antisymm
  · exact (finiteMinimum_le (fun j => n + f j) j).trans_eq (congrArg (n + ·) hj)
  · exact le_finiteMinimum (fun j => Nat.add_le_add_left (finiteMinimum_le f j) n)

theorem finiteMinimum_min_left (f : ι → ℕ) (n : ℕ) :
    finiteMinimum (fun j => min n (f j)) = min n (finiteMinimum f) := by
  obtain ⟨j, hj⟩ := finiteMinimum_attained f
  apply le_antisymm
  · exact (finiteMinimum_le (fun j => min n (f j)) j).trans_eq (congrArg (min n) hj)
  · exact le_finiteMinimum (fun j => min_le_min_left n (finiteMinimum_le f j))

theorem le_finiteMinimum_iff (f : ι → ℕ) (n : ℕ) :
    n ≤ finiteMinimum f ↔ ∀ j, n ≤ f j :=
  ⟨fun h j => h.trans (finiteMinimum_le f j), le_finiteMinimum⟩

end CommAlg.Polymatroid

end
end CheckedSource52

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "53: CommAlg.Polymatroid.PartitionDefect\n"

/-! ## Source: CommAlg.Polymatroid.PartitionDefect -/
section CheckedSource53

/-! # Exact partition defects and the homological rank of twisted powers -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def partitionDefect (g : RankFunction V) {A : Finset V} (P : Finpartition A) : ℕ :=
  (∑ C ∈ P.parts, g C) - g A

def partitionSlack {A : Finset V} (P : Finpartition A) : ℕ := A.card - P.parts.card

theorem RankFunction.le_sum_partition (g : RankFunction V) {A : Finset V}
    (P : Finpartition A) : g A ≤ ∑ C ∈ P.parts, g C := by
  simpa [P.biUnion_parts] using g.biUnion_marginal ∅ P.parts

theorem partitionDefect_add_rank (g : RankFunction V) {A : Finset V}
    (P : Finpartition A) : partitionDefect g P + g A = ∑ C ∈ P.parts, g C :=
  Nat.sub_add_cancel (g.le_sum_partition P)

theorem partitionSlack_add_parts {A : Finset V} (P : Finpartition A) :
    partitionSlack P + P.parts.card = A.card := Nat.sub_add_cancel P.card_parts_le_card

theorem partitionDefect_add (g f : RankFunction V) {A : Finset V} (P : Finpartition A) :
    partitionDefect (g.add f) P = partitionDefect g P + partitionDefect f P := by
  have hg := partitionDefect_add_rank g P
  have hf := partitionDefect_add_rank f P
  have hgf := partitionDefect_add_rank (g.add f) P
  change partitionDefect (g.add f) P + (g A + f A) =
    ∑ C ∈ P.parts, (g C + f C) at hgf
  rw [Finset.sum_add_distrib] at hgf
  omega

theorem partitionDefect_scale (g : RankFunction V) (s : ℕ)
    {A : Finset V} (P : Finpartition A) :
    partitionDefect (RankFunction.scale s g) P = s * partitionDefect g P := by
  change (∑ C ∈ P.parts, s * g C) - s * g A = s * ((∑ C ∈ P.parts, g C) - g A)
  rw [← Finset.mul_sum, Nat.mul_sub_left_distrib]

theorem partitionCost_add_parts (g : RankFunction V) (hg : g.Active)
    {A : Finset V} (P : Finpartition A) :
    partitionCost g P + P.parts.card = ∑ C ∈ P.parts, g C := by
  have hp : ∀ C ∈ P.parts, (g C - 1) + 1 = g C := by
    intro C hC
    exact Nat.sub_add_cancel (hg C (P.nonempty_of_mem_parts hC))
  have hs := Finset.sum_congr rfl hp
  simpa [partitionCost, Finset.sum_add_distrib] using hs

theorem augmented_partition_cost (g : RankFunction V) (hg : g.Active)
    {A : Finset V} (P : Finpartition A) :
    A.card + partitionCost g P = g A + partitionDefect g P + partitionSlack P := by
  have hc := partitionCost_add_parts g hg P
  have hd := partitionDefect_add_rank g P
  have hs := partitionSlack_add_parts P
  omega

theorem augmentedPartitionRank_defect (g : RankFunction V) (hg : g.Active)
    (A : Finset V) :
    augmentedPartitionRank g A =
      g A + finiteMinimum (fun P : Finpartition A => partitionDefect g P + partitionSlack P) := by
  unfold augmentedPartitionRank
  change A.card + finiteMinimum (fun P : Finpartition A => partitionCost g P) = _
  rw [← finiteMinimum_add_const, ← finiteMinimum_add_const]
  congr 1
  funext P
  simpa only [Nat.add_assoc] using augmented_partition_cost g hg P

theorem homologicalRank_defect (g : RankFunction V) (hg : g.Active) (i : ℕ)
    {A : Finset V} (hA : A.Nonempty) :
    homologicalRank g hg i A = g A +
      min i (finiteMinimum (fun P : Finpartition A => partitionDefect g P + partitionSlack P)) := by
  rw [homologicalRank_apply g hg i hA]
  change min (g A + i) (augmentedPartitionRank g A) = _
  rw [augmentedPartitionRank_defect g hg A, Nat.add_min_add_left]

def twistedPowerRank (η ρ : RankFunction V) (s : ℕ) : RankFunction V :=
  η.add (RankFunction.scale s ρ)

theorem twistedPowerRank_apply (η ρ : RankFunction V) (s : ℕ) (A : Finset V) :
    twistedPowerRank η ρ s A = η A + s * ρ A := rfl

theorem twistedPower_defect (η ρ : RankFunction V) (s : ℕ)
    {A : Finset V} (P : Finpartition A) :
    partitionDefect (twistedPowerRank η ρ s) P =
      s * partitionDefect ρ P + partitionDefect η P := by
  rw [twistedPowerRank, partitionDefect_add, partitionDefect_scale, Nat.add_comm]

/-- Formula (4.1), with arbitrary fixed twist and arbitrary finite ground set. -/
theorem twistedPower_homologicalRank (η ρ : RankFunction V) (s i : ℕ)
    (hg : (twistedPowerRank η ρ s).Active) {A : Finset V} (hA : A.Nonempty) :
    homologicalRank (twistedPowerRank η ρ s) hg i A =
      twistedPowerRank η ρ s A + min i
        (finiteMinimum (fun P : Finpartition A =>
          s * partitionDefect ρ P + partitionDefect η P + partitionSlack P)) := by
  rw [homologicalRank_defect _ hg i hA]
  simp only [twistedPower_defect]

end CommAlg.Polymatroid

end
end CheckedSource53

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "54: CommAlg.Polymatroid.UniformRank\n"

/-! ## Source: CommAlg.Polymatroid.UniformRank -/
section CheckedSource54

/-! # Uniform ranks and the singleton caps of homological ranks -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def RankFunction.truncate (g : RankFunction V) (d : ℕ) : RankFunction V where
  toFun A := min (g A) d
  empty := by simp
  monotone := fun A B h => min_le_min_right d (g.monotone h)
  submodular A B := by
    have hg := g.submodular A B
    have hiA := g.monotone (inter_subset_left : A ∩ B ⊆ A)
    have hiB := g.monotone (inter_subset_right : A ∩ B ⊆ B)
    omega

def cardinalRank (V : Type*) [DecidableEq V] : RankFunction V where
  toFun A := A.card
  empty := card_empty
  monotone := fun _ _ h => card_le_card h
  submodular A B := (card_union_add_card_inter A B).le

def uniformRank (V : Type*) [DecidableEq V] (d : ℕ) : RankFunction V :=
  (cardinalRank V).truncate d

@[simp] theorem uniformRank_apply (d : ℕ) (A : Finset V) :
    uniformRank V d A = min A.card d := rfl

def uniformPowerRank (V : Type*) [DecidableEq V] (d s : ℕ) : RankFunction V :=
  RankFunction.scale s (uniformRank V d)

@[simp] theorem uniformPowerRank_apply (d s : ℕ) (A : Finset V) :
    uniformPowerRank V d s A = s * min A.card d := rfl

theorem uniformPowerRank_active {d s : ℕ} (hd : 1 ≤ d) (hs : 1 ≤ s) :
    (uniformPowerRank V d s).Active := by
  intro A hA
  have hc : 1 ≤ A.card := card_pos.mpr hA
  have hm : 1 ≤ min A.card d := le_min hc hd
  change 1 ≤ s * min A.card d
  nlinarith

theorem RankFunction.le_sum_singletons (g : RankFunction V) (A : Finset V) :
    g A ≤ ∑ j ∈ A, g {j} := by
  simpa [Finpartition.parts_bot] using g.le_sum_partition (⊥ : Finpartition A)

theorem homologicalRank_singleton (g : RankFunction V) (hg : g.Active)
    (i : ℕ) (j : V) : homologicalRank g hg i {j} = g {j} := by
  have hD := partitionRank_le_single g (singleton_nonempty j)
  have hg1 := hg {j} (singleton_nonempty j)
  have hLo : g {j} ≤ augmentedPartitionRank g {j} :=
    RankFunction.le_of_dominates (augmentedRank_dominates g hg) {j}
  have hEq : augmentedPartitionRank g {j} = g {j} := by
    unfold augmentedPartitionRank at hLo ⊢
    simp only [card_singleton] at *
    omega
  rw [homologicalRank_apply g hg i (singleton_nonempty j)]
  change min (g {j} + i) (augmentedPartitionRank g {j}) = _
  rw [hEq, min_eq_right (Nat.le_add_right _ _)]

theorem homologicalRank_le_sum_singletons (g : RankFunction V) (hg : g.Active)
    (i : ℕ) (A : Finset V) : homologicalRank g hg i A ≤ ∑ j ∈ A, g {j} := by
  simpa only [homologicalRank_singleton] using (homologicalRank g hg i).le_sum_singletons A

@[simp] theorem subsetSum_constExponent (n : ℕ) (A : Finset V) :
    subsetSum (constExponent n : Exponent V) A = A.card * n := by
  simp [subsetSum]

@[simp] theorem degree_constExponent (n : ℕ) :
    (constExponent n : Exponent V).degree = Fintype.card V * n := by
  simp [Finsupp.degree_eq_sum]

/-- The bases of a scaled uniform rank are exactly the bounded exponent
vectors of the required total degree. This identifies the squarefree
Veronese family at `s=1` and all its powers at arbitrary `s`. -/
theorem isRankBase_uniformPower_iff (d s : ℕ) (hd : d ≤ Fintype.card V)
    (a : Exponent V) :
    IsRankBase (uniformPowerRank V d s) a ↔ a.degree = s * d ∧ ∀ j, a j ≤ s := by
  have htop : uniformPowerRank V d s univ = s * d := by simp [min_eq_right hd]
  constructor
  · rintro ⟨hdeg, hbound⟩
    refine ⟨hdeg.trans htop, fun j => ?_⟩
    have h := hbound {j}
    simp only [subsetSum, sum_singleton, uniformPowerRank_apply, card_singleton] at h
    have hm : min 1 d ≤ 1 := min_le_left _ _
    nlinarith
  · rintro ⟨hdeg, hcap⟩
    refine ⟨hdeg.trans htop.symm, fun A => ?_⟩
    have hc : subsetSum a A ≤ A.card * s := by
      simpa [subsetSum] using (Finset.sum_le_sum (s := A) (fun j _ => hcap j))
    have ht : subsetSum a A ≤ s * d := by
      have h := subsetSum_mono a (subset_univ A)
      simpa only [subsetSum_univ, hdeg] using h
    change subsetSum a A ≤ s * min A.card d
    rcases le_total A.card d with h | h
    · rw [min_eq_left h, Nat.mul_comm]
      exact hc
    · rwa [min_eq_right h]

end CommAlg.Polymatroid

end
end CheckedSource54

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "55: CommAlg.Polymatroid.UniversalRank\n"

/-! ## Source: CommAlg.Polymatroid.UniversalRank -/
section CheckedSource55

/-! # Homological ranks with all inactive coordinates retained

For every integral polymatroid rank `g`, the rank `g+|·|` is active. Its
Dilworth truncation is exactly

  u_g(A) = min over partitions P of A of Σ(C in P) (g(C)+|C|−1).

This is the same as `|A|+D_g(A)` with integer block costs, including zero
coordinates. On active ground sets it is proved equal to the earlier formula.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def cardinalLift (g : RankFunction V) : RankFunction V := g.add (cardinalRank V)

@[simp] theorem cardinalLift_apply (g : RankFunction V) (A : Finset V) :
    cardinalLift g A = g A + A.card := rfl

theorem cardinalLift_active (g : RankFunction V) : (cardinalLift g).Active := by
  intro A hA
  have hc := card_pos.mpr hA
  change 1 ≤ g A + A.card
  omega

def universalAugmentedRank (g : RankFunction V) : RankFunction V :=
  dilworthRank (cardinalLift g) (cardinalLift_active g)

@[simp] theorem universalAugmentedRank_apply (g : RankFunction V) (A : Finset V) :
    universalAugmentedRank g A = partitionRank (cardinalLift g) A := rfl

theorem universalAugmentedRank_dominates (g : RankFunction V) :
    (universalAugmentedRank g).Dominates g := by
  intro A B hAB
  have h := augmentedPartitionRank_marginal (cardinalLift g) (cardinalLift_active g) hAB
  simp only [cardinalLift_apply, augmentedPartitionRank] at h
  change g B + partitionRank (cardinalLift g) A ≤ partitionRank (cardinalLift g) B + g A
  omega

def universalHomologicalRank (g : RankFunction V) (i : ℕ) : RankFunction V :=
  g.interpolate (universalAugmentedRank g) (universalAugmentedRank_dominates g) i

@[simp] theorem universalHomologicalRank_empty (g : RankFunction V) (i : ℕ) :
    universalHomologicalRank g i ∅ = 0 := RankFunction.map_empty _

theorem universalHomologicalRank_apply (g : RankFunction V) (i : ℕ)
    {A : Finset V} (hA : A.Nonempty) :
    universalHomologicalRank g i A = min (g A + i) (universalAugmentedRank g A) := by
  simp [universalHomologicalRank, RankFunction.interpolate_apply, shiftRankValue, hA.ne_empty]

theorem universalHomologicalRank_le_add (g : RankFunction V) (i : ℕ) (A : Finset V) :
    universalHomologicalRank g i A ≤ g A + i :=
  shiftRankValue_le_add g (universalAugmentedRank g) i A

/-- The cost identity also justifies the integer-partition interpretation
when some original rank values vanish. -/
theorem cardinalLift_cost_add_parts (g : RankFunction V) {A : Finset V}
    (P : Finpartition A) :
    partitionCost (cardinalLift g) P + P.parts.card = A.card + ∑ C ∈ P.parts, g C := by
  have h := partitionCost_add_parts (cardinalLift g) (cardinalLift_active g) P
  simpa only [cardinalLift_apply, Finset.sum_add_distrib, P.sum_card_parts, Nat.add_comm] using h

theorem cardinalLift_cost_of_active (g : RankFunction V) (hg : g.Active)
    {A : Finset V} (P : Finpartition A) :
    partitionCost (cardinalLift g) P = A.card + partitionCost g P := by
  have h1 := cardinalLift_cost_add_parts g P
  have h2 := partitionCost_add_parts g hg P
  omega

/-- The universal rank is exactly the original active-ground-set formula. -/
theorem universalAugmentedRank_eq_active (g : RankFunction V) (hg : g.Active)
    (A : Finset V) : universalAugmentedRank g A = augmentedPartitionRank g A := by
  change finiteMinimum (fun P : Finpartition A => partitionCost (cardinalLift g) P) =
    A.card + finiteMinimum (fun P : Finpartition A => partitionCost g P)
  rw [← finiteMinimum_add_const]
  congr 1
  funext P
  exact cardinalLift_cost_of_active g hg P

theorem universalHomologicalRank_eq_active (g : RankFunction V) (hg : g.Active)
    (i : ℕ) (A : Finset V) : universalHomologicalRank g i A = homologicalRank g hg i A := by
  by_cases hA : A = ∅
  · simp [hA]
  have hne := Finset.nonempty_iff_ne_empty.mpr hA
  rw [universalHomologicalRank_apply g i hne, homologicalRank_apply g hg i hne,
    universalAugmentedRank_eq_active g hg A]
  rfl

/-- Every simultaneous deletion inequality is equivalent to the upper
inequalities of the universal partition rank, with no activity assumption. -/
theorem universal_bounds_iff (g : RankFunction V) (a : Exponent V) :
    (∀ A, A.Nonempty → subsetSum a A ≤ g A + A.card - 1) ↔
      (∀ A, subsetSum a A ≤ universalAugmentedRank g A) := by
  exact nonempty_bounds_iff_partition_bounds (cardinalLift g) a

theorem universalAugmentedRank_le_cost (g : RankFunction V) {A : Finset V}
    (P : Finpartition A) : universalAugmentedRank g A ≤ partitionCost (cardinalLift g) P :=
  partitionRank_le _ P

theorem universalAugmentedRank_attained (g : RankFunction V) (A : Finset V) :
    ∃ P : Finpartition A, partitionCost (cardinalLift g) P = universalAugmentedRank g A :=
  partitionRank_attained _ A

end CommAlg.Polymatroid

end
end CheckedSource55

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "56: CommAlg.Polymatroid.KoszulRankUniversal\n"

/-! ## Source: CommAlg.Polymatroid.KoszulRankUniversal -/
section CheckedSource56

/-!
# The Koszul rank criterion with arbitrary loops and zero rank

The actual rank/coloop criterion is first expressed by support-sensitive
indicator inequalities. These are equivalent to inequalities on the original
exponent using `g(A) + |A| - 1`, without assuming active variables.
-/

noncomputable section

open scoped Matroid

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem supportPred_indicator_bounds_iff_lift (g : RankFunction V) (a : Exponent V) :
    (∀ j ∈ a.support, ∀ A,
      subsetSum (supportPred a) A + (if j ∈ A then 1 else 0) ≤ g A) ↔
      (∀ A, A.Nonempty → subsetSum a A ≤ g A + A.card - 1) := by
  constructor
  · intro h A hA
    by_cases hW : (A ∩ a.support).Nonempty
    · obtain ⟨j, hj⟩ := hW
      obtain ⟨hjA, hjS⟩ := mem_inter.mp hj
      have hb := h j hjS A
      rw [if_pos hjA] at hb
      have he := subsetSum_supportPred a A
      have hc := card_le_card (inter_subset_left : A ∩ a.support ⊆ A)
      omega
    · have he := subsetSum_support_inter a A
      rw [not_nonempty_iff_eq_empty.mp hW, subsetSum_empty] at he
      omega
  · intro h j hj A
    by_cases hW : (A ∩ a.support).Nonempty
    · have hb := h (A ∩ a.support) hW
      have he := subsetSum_supportPred a (A ∩ a.support)
      rw [inter_eq_left.mpr inter_subset_right, subsetSum_supportPred_inter] at he
      have hg := g.monotone (inter_subset_left : A ∩ a.support ⊆ A)
      have hc : 1 ≤ (A ∩ a.support).card := card_pos.mpr hW
      split_ifs <;> omega
    · have hEmpty : A ∩ a.support = ∅ := not_nonempty_iff_eq_empty.mp hW
      have he := subsetSum_supportPred_inter a A
      rw [hEmpty, subsetSum_empty] at he
      have hjA : j ∉ A := by
        intro hjA
        have hjW := mem_inter.mpr ⟨hjA, hj⟩
        rw [hEmpty] at hjW
        exact notMem_empty j hjW
      rw [if_neg hjA]
      omega

/-- The rank and no-coloop criterion remains exact when some variables are
loops, the rank is zero, or the support is empty. -/
theorem koszulConstraint_rank_and_noColoops_iff_indicator (g : RankFunction V)
    {a : Exponent V} {i : ℕ} (ha : LowerFeasible g.lower a)
    (hDegree : a.degree = g univ + i) :
    (CommAlg.Matroid.rank (koszulConstraintMatroid g a ha) = i ∧
      CommAlg.Matroid.NoColoops (koszulConstraintMatroid g a ha)) ↔
      ∀ j ∈ a.support, ∀ A,
        subsetSum (supportPred a) A + (if j ∈ A then 1 else 0) ≤ g A := by
  by_cases hSupport : a.support.Nonempty
  · let M := koszulConstraintMatroid g a ha
    have hRank := koszulConstraint_rank_le g ha hDegree
    have hGround : M.E.Nonempty := by
      simpa only [M, koszulConstraintMatroid_ground, Finset.coe_nonempty] using hSupport
    have hDelete := CommAlg.Matroid.rank_eq_and_noColoops_iff_delete_rank M i hGround hRank
    have hStep : (CommAlg.Matroid.rank M = i ∧ CommAlg.Matroid.NoColoops M) ↔
        ∀ j ∈ a.support, ∀ U,
          i ≤ deletionSlack g a U + ((a.support.erase j) \ U).card := by
      rw [hDelete]
      constructor
      · intro h j hj
        apply (le_koszulConstraint_delete_rank g a ha j i).mp
        exact le_of_eq (h j hj).symm
      · intro h j hj
        have hLower := (le_koszulConstraint_delete_rank g a ha j i).mpr (h j hj)
        have hUpper := (CommAlg.Matroid.rank_delete_le M ({j} : Set V)).trans hRank
        exact Nat.le_antisymm hUpper hLower
    exact hStep.trans (all_deletion_costs_ge_iff g ha hDegree)
  · have hEmpty : a.support = ∅ := not_nonempty_iff_eq_empty.mp hSupport
    have ha0 : a = 0 := Finsupp.support_eq_empty.mp hEmpty
    have hi : i = 0 := by
      have hz : a.degree = 0 := by simp [ha0]
      omega
    have hRank := koszulConstraint_rank_le g ha hDegree
    have hNo : CommAlg.Matroid.NoColoops (koszulConstraintMatroid g a ha) := by
      intro j hj
      have hjg := hj.mem_ground
      simpa only [koszulConstraintMatroid_ground, hEmpty, coe_empty,
        Set.mem_empty_iff_false] using hjg
    constructor
    · intro _ j hj
      simp [hEmpty] at hj
    · intro _
      exact ⟨by omega, hNo⟩

theorem koszulConstraint_rank_and_noColoops_iff_lift (g : RankFunction V)
    {a : Exponent V} {i : ℕ} (ha : LowerFeasible g.lower a)
    (hDegree : a.degree = g univ + i) :
    (CommAlg.Matroid.rank (koszulConstraintMatroid g a ha) = i ∧
      CommAlg.Matroid.NoColoops (koszulConstraintMatroid g a ha)) ↔
      ∀ A, A.Nonempty → subsetSum a A ≤ g A + A.card - 1 :=
  (koszulConstraint_rank_and_noColoops_iff_indicator g ha hDegree).trans
    (supportPred_indicator_bounds_iff_lift g a)

theorem koszulConstraint_rank_and_noColoops_iff_universal (g : RankFunction V)
    {a : Exponent V} {i : ℕ} (ha : LowerFeasible g.lower a)
    (hDegree : a.degree = g univ + i) :
    (CommAlg.Matroid.rank (koszulConstraintMatroid g a ha) = i ∧
      CommAlg.Matroid.NoColoops (koszulConstraintMatroid g a ha)) ↔
      ∀ A, subsetSum a A ≤ universalAugmentedRank g A :=
  (koszulConstraint_rank_and_noColoops_iff_lift g ha hDegree).trans
    (universal_bounds_iff g a)

section Homology

variable [LinearOrder V] {k : Type*} [CommRing k] [Nontrivial k]

/-- The genuine chain-homology criterion, including all loop and zero-rank
cases, without an active-variable hypothesis. -/
theorem koszulConstraint_nonzeroHomology_iff_universal (g : RankFunction V)
    {a : Exponent V} {i : ℕ} (ha : LowerFeasible g.lower a)
    (hDegree : a.degree = g univ + i) :
    CommAlg.Simplicial.NonzeroHomology (k := k)
      (CommAlg.Matroid.independenceFaces (koszulConstraintMatroid g a ha)) i ↔
      ∀ A, subsetSum a A ≤ universalAugmentedRank g A := by
  rw [CommAlg.Matroid.independence_nonzeroHomology_iff]
  have h := koszulConstraint_rank_and_noColoops_iff_universal g ha hDegree
  rw [eq_comm] at h
  exact h

/-- Complete degree and inequality characterization of actual nonvanishing,
valid for an arbitrary normalized monotone submodular rank. -/
theorem koszulConstraint_nonzeroHomology_iff_universal_full (g : RankFunction V)
    {a : Exponent V} (ha : LowerFeasible g.lower a) (i : ℕ) :
    CommAlg.Simplicial.NonzeroHomology (k := k)
      (CommAlg.Matroid.independenceFaces (koszulConstraintMatroid g a ha)) i ↔
      a.degree = g univ + i ∧ ∀ A, subsetSum a A ≤ universalAugmentedRank g A := by
  constructor
  · intro h
    have hDegree := koszulConstraint_nonzeroHomology_degree g ha h
    exact ⟨hDegree, (koszulConstraint_nonzeroHomology_iff_universal g ha hDegree).mp h⟩
  · rintro ⟨hDegree, hBounds⟩
    exact (koszulConstraint_nonzeroHomology_iff_universal g ha hDegree).mpr hBounds

end Homology

end CommAlg.Polymatroid

end
end CheckedSource56

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "57: CommAlg.Polymatroid.RankGreedy\n"

/-! ## Source: CommAlg.Polymatroid.RankGreedy -/
section CheckedSource57

/-! # Base extension and recovery of every canonical rank value -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def UpperTight (g : RankFunction V) (a : Exponent V) (U : Finset V) : Prop :=
  subsetSum a U = g U

theorem upper_tight_union_inter (g : RankFunction V) {a : Exponent V}
    (ha : UpperFeasible g a) {U W : Finset V}
    (hU : UpperTight g a U) (hW : UpperTight g a W) :
    UpperTight g a (U ∪ W) ∧ UpperTight g a (U ∩ W) := by
  have hm := subsetSum_union_inter a U W
  have hs := g.submodular U W
  have h1 := ha (U ∪ W)
  have h2 := ha (U ∩ W)
  unfold UpperTight at *
  omega

theorem upper_failed_increment (g : RankFunction V) {a : Exponent V}
    (ha : UpperFeasible g a) (i : V) (hbad : ¬ UpperFeasible g (a + Finsupp.single i 1)) :
    ∃ U, UpperTight g a U ∧ i ∈ U := by
  simp only [UpperFeasible, not_forall, not_le] at hbad
  obtain ⟨U, hU⟩ := hbad
  have hs : subsetSum (a + Finsupp.single i 1) U =
      subsetSum a U + (if i ∈ U then 1 else 0) := by
    rw [subsetSum_add]
    simp [subsetSum, Finsupp.single_apply]
  have hf := ha U
  have hiU : i ∈ U := by
    by_contra h
    rw [if_neg h] at hs
    omega
  rw [if_pos hiU] at hs
  exact ⟨U, by unfold UpperTight; omega, hiU⟩

theorem upper_tight_cover (g : RankFunction V) {a : Exponent V}
    (ha : UpperFeasible g a) (D : Finset V)
    (h : ∀ i ∈ D, ∃ U, UpperTight g a U ∧ i ∈ U) :
    ∃ U, UpperTight g a U ∧ D ⊆ U := by
  induction D using Finset.induction_on with
  | empty => exact ⟨∅, by simp [UpperTight], Finset.empty_subset _⟩
  | @insert i D hi ih =>
    obtain ⟨U, hU, hDU⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    obtain ⟨W, hW, hiW⟩ := h i (Finset.mem_insert_self _ _)
    exact ⟨U ∪ W, (upper_tight_union_inter g ha hU hW).1,
      Finset.insert_subset_iff.mpr ⟨Finset.mem_union_right _ hiW,
        hDU.trans Finset.subset_union_left⟩⟩

theorem upperFeasible_le_const (g : RankFunction V) {a : Exponent V}
    (ha : UpperFeasible g a) : a ≤ constExponent (g Finset.univ) := by
  intro i
  have hi := ha {i}
  simp only [subsetSum, Finset.sum_singleton] at hi
  exact hi.trans (g.monotone (Finset.subset_univ _))

theorem exists_rankBase_above (g : RankFunction V) {a : Exponent V}
    (ha : UpperFeasible g a) : ∃ b, a ≤ b ∧ IsRankBase g b := by
  let T : Set (Exponent V) := {b | a ≤ b ∧ UpperFeasible g b}
  have hfin : T.Finite := (Set.finite_Iic (constExponent (g Finset.univ))).subset
    (fun _ h => upperFeasible_le_const g h.2)
  obtain ⟨b, hb, hmax⟩ := hfin.exists_maximal ⟨a, le_rfl, ha⟩
  have hcover : ∀ i ∈ (Finset.univ : Finset V), ∃ U, UpperTight g b U ∧ i ∈ U := by
    intro i hi
    apply upper_failed_increment g hb.2 i
    intro hgood
    have hmem : b + Finsupp.single i 1 ∈ T := ⟨hb.1.trans (le_add_right le_rfl), hgood⟩
    have hle := hmax hmem (le_add_right le_rfl)
    have hc := hle i
    simp at hc
  obtain ⟨U, hU, hfull⟩ := upper_tight_cover g hb.2 Finset.univ hcover
  have he : U = Finset.univ := Finset.Subset.antisymm (Finset.subset_univ _) hfull
  have hdeg : b.degree = g Finset.univ := by
    simpa only [UpperTight, he, subsetSum_univ] using hU
  exact ⟨b, hb.1, hdeg, hb.2⟩

def RankFunction.restrict (g : RankFunction V) (A : Finset V) : RankFunction V where
  toFun U := g (U ∩ A)
  empty := by simp
  monotone := by
    intro U W hUW
    apply g.monotone
    exact Finset.inter_subset_inter_right hUW
  submodular := by
    intro U W
    have hu : (U ∪ W) ∩ A = (U ∩ A) ∪ (W ∩ A) := by ext x; simp; tauto
    have hi : (U ∩ W) ∩ A = (U ∩ A) ∩ (W ∩ A) := by ext x; simp <;> tauto
    rw [hu, hi]
    exact g.submodular _ _

/-- Every individual upper bound is attained by an integer base. -/
theorem exists_rankBase_attaining (g : RankFunction V) (U : Finset V) :
    ∃ a, IsRankBase g a ∧ subsetSum a U = g U := by
  obtain ⟨b, hb⟩ := rankBases_nonempty (g.restrict U)
  have hb := (mem_rankBases _ b).mp hb
  have hbU : project U b = b := by
    ext i
    by_cases hi : i ∈ U
    · simp [hi]
    · have hs := hb.2 {i}
      have he : ({i} : Finset V) ∩ U = ∅ := by ext j; simp; aesop
      change subsetSum b {i} ≤ g ({i} ∩ U) at hs
      simp only [subsetSum, Finset.sum_singleton, he, RankFunction.map_empty] at hs
      have hzero : b i = 0 := Nat.eq_zero_of_le_zero hs
      simp [hi, hzero]
  have hbdeg : b.degree = g U := by
    simpa only [RankFunction.restrict, Finset.univ_inter] using hb.1
  have hbupper : UpperFeasible g b := by
    intro W
    exact (hb.2 W).trans (g.monotone Finset.inter_subset_left)
  obtain ⟨a, hba, ha⟩ := exists_rankBase_above g hbupper
  have hsum : subsetSum b U = g U := by rw [← degree_project, hbU, hbdeg]
  have hsumle : subsetSum b U ≤ subsetSum a U := Finset.sum_le_sum (fun i _ => hba i)
  exact ⟨a, ha, Nat.le_antisymm (ha.2 U) (hsum ▸ hsumle)⟩

@[simp] theorem upperRank_rankBases (g : RankFunction V) (U : Finset V) :
    upperRank (rankBases g) U = g U := by
  apply le_antisymm
  · apply Finset.sup_le
    intro a ha
    exact ((mem_rankBases g a).mp ha).2 U
  · obtain ⟨a, ha, hU⟩ := exists_rankBase_attaining g U
    rw [← hU]
    exact le_upperRank ((mem_rankBases g a).mpr ha) U

theorem rankBases_injective : Function.Injective (rankBases (V := V)) := by
  intro g h he
  cases g with | mk g g0 gm gs =>
    cases h with | mk h h0 hm hs =>
      congr 1
      funext U
      have hg := upperRank_rankBases (RankFunction.mk g g0 gm gs) U
      have hh := upperRank_rankBases (RankFunction.mk h h0 hm hs) U
      rw [he] at hg
      exact hg.symm.trans hh

end CommAlg.Polymatroid

end
end CheckedSource57

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "58: CommAlg.Polymatroid.RankShiftFormula\n"

/-! ## Source: CommAlg.Polymatroid.RankShiftFormula -/
section CheckedSource58

/-! # The right-hand side of the homological-shift rank formula

`rankShiftIdeal` is the explicitly described ideal on the right-hand side of
Theorem 1.2. It is not a definition of a homological shift: the separate
graded-Tor theorem proves that the genuine homological shift equals it.
This module proves its exact monomial membership and all partition inequalities,
including inactive variables and the unit rank.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def rankShiftFamily (g : RankFunction V) (i : ℕ) : Family V :=
  if universalHomologicalRank g i univ = g univ + i then
    rankBases (universalHomologicalRank g i) else ∅

def rankShiftIdeal (k : Type*) [CommSemiring k] (g : RankFunction V) (i : ℕ) :
    Ideal (MvPolynomial V k) :=
  if universalHomologicalRank g i univ = g univ + i then
    rankIdeal k (universalHomologicalRank g i) else ⊥

theorem rankShiftIdeal_eq_monomialIdeal (k : Type*) [CommSemiring k]
    (g : RankFunction V) (i : ℕ) :
    rankShiftIdeal k g i = monomialIdeal k (rankShiftFamily g i) := by
  unfold rankShiftIdeal rankShiftFamily
  split_ifs
  · rfl
  · simp [monomialIdeal]

theorem rankShiftFamily_nonempty_iff (g : RankFunction V) (i : ℕ) :
    (rankShiftFamily g i).Nonempty ↔ universalHomologicalRank g i univ = g univ + i := by
  unfold rankShiftFamily
  split_ifs with h
  · simp [h, rankBases_nonempty]
  · simp [h]

theorem rankShiftFamily_equigenerated (g : RankFunction V) (i : ℕ) :
    Equigenerated (rankShiftFamily g i) (g univ + i) := by
  intro a ha
  unfold rankShiftFamily at ha
  split_ifs at ha with h
  · exact ((mem_rankBases _ a).mp ha).1.trans h
  · simp at ha

theorem mem_rankShiftFamily_iff (g : RankFunction V) (i : ℕ) (a : Exponent V) :
    a ∈ rankShiftFamily g i ↔
      a.degree = g univ + i ∧ UpperFeasible (universalHomologicalRank g i) a := by
  by_cases h : universalHomologicalRank g i univ = g univ + i
  · simp [rankShiftFamily, h, mem_rankBases, IsRankBase]
  · have hle := universalHomologicalRank_le_add g i univ
    simp only [rankShiftFamily, if_neg h, notMem_empty, false_iff, not_and]
    intro hdeg hbound
    have hb := hbound univ
    rw [subsetSum_univ, hdeg] at hb
    omega

theorem rankShiftFamily_polymatroidal (g : RankFunction V) (i : ℕ) :
    IsPolymatroidal (rankShiftFamily g i) := by
  unfold rankShiftFamily
  split_ifs
  · exact rankBases_polymatroidal _
  · exact ⟨⟨0, by simp [Equigenerated]⟩, by simp [ExchangeAxiom]⟩

theorem rankShiftFamily_upperRank (g : RankFunction V) (i : ℕ)
    (h : (rankShiftFamily g i).Nonempty) (A : Finset V) :
    upperRank (rankShiftFamily g i) A = universalHomologicalRank g i A := by
  rw [rankShiftFamily, if_pos ((rankShiftFamily_nonempty_iff g i).mp h)]
  exact upperRank_rankBases _ A

section Ideals

variable {k : Type*} [CommSemiring k] [Nontrivial k]

theorem monomial_mem_rankShiftIdeal_iff (g : RankFunction V) (i : ℕ) (a : Exponent V) :
    MvPolynomial.monomial a (1 : k) ∈ rankShiftIdeal k g i ↔
      ∀ A, g univ + i ≤ subsetSum a Aᶜ + universalHomologicalRank g i A := by
  by_cases h : universalHomologicalRank g i univ = g univ + i
  · rw [rankShiftIdeal, if_pos h, monomial_mem_rankIdeal_iff]
    constructor
    · intro hb A
      have hB := hb Aᶜ
      have hL := (universalHomologicalRank g i).lower_add_compl Aᶜ
      simp only [compl_compl, h] at hL
      omega
    · intro hb U
      have hB := hb Uᶜ
      have hL := (universalHomologicalRank g i).lower_add_compl U
      simp only [compl_compl] at hB
      rw [h] at hL
      omega
  · rw [rankShiftIdeal, if_neg h]
    constructor
    · intro hb
      have : False := by simpa using hb
      exact this.elim
    · intro hb
      have hB := hb univ
      simp only [compl_univ, subsetSum_empty, Nat.zero_add] at hB
      have hU := universalHomologicalRank_le_add g i univ
      omega

/-- Exact expanded membership, valid even when the indicated shift is zero.
Every block is nonempty because `P` is an actual `Finpartition A`. -/
theorem monomial_mem_rankShiftIdeal_partition_iff (g : RankFunction V) (i : ℕ)
    (a : Exponent V) :
    MvPolynomial.monomial a (1 : k) ∈ rankShiftIdeal k g i ↔
      g univ + i ≤ a.degree ∧ LowerFeasible g.lower a ∧
        ∀ A, A.Nonempty → ∀ P : Finpartition A,
          g univ + i + P.parts.card ≤ subsetSum a Aᶜ + A.card + ∑ C ∈ P.parts, g C := by
  rw [monomial_mem_rankShiftIdeal_iff]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · simpa using h ∅
    · intro U
      have hb := h Uᶜ
      have hR := universalHomologicalRank_le_add g i Uᶜ
      have hL := g.lower_add_compl U
      simp only [compl_compl] at hb
      omega
    · intro A hA P
      have hb := h A
      have hR : universalHomologicalRank g i A ≤ universalAugmentedRank g A :=
        shiftRankValue_le_u g (universalAugmentedRank g) i A
      have hP := universalAugmentedRank_le_cost g P
      have hCost := cardinalLift_cost_add_parts g P
      omega
  · rintro ⟨hdeg, hLower, hParts⟩ A
    by_cases hA : A = ∅
    · simpa [hA] using hdeg
    have hA' := Finset.nonempty_iff_ne_empty.mpr hA
    have hL := hLower Aᶜ
    have hLC := g.lower_add_compl Aᶜ
    simp only [compl_compl] at hLC
    obtain ⟨P, hP⟩ := universalAugmentedRank_attained g A
    have hPart := hParts A hA' P
    have hCost := cardinalLift_cost_add_parts g P
    rw [hP] at hCost
    rw [universalHomologicalRank_apply g i hA']
    omega

theorem mem_rankShiftIdeal_iff_coeff (g : RankFunction V) (i : ℕ)
    (f : MvPolynomial V k) :
    f ∈ rankShiftIdeal k g i ↔
      ∀ a ∈ f.support, MvPolynomial.monomial a (1 : k) ∈ rankShiftIdeal k g i := by
  simp_rw [rankShiftIdeal_eq_monomialIdeal, monomial_mem_iff]
  exact mem_monomialIdeal_iff _ _

theorem rankShiftIdeal_le_rankIdeal (g : RankFunction V) (i : ℕ) :
    rankShiftIdeal k g i ≤ rankIdeal k g := by
  intro f hf
  apply (mem_monomialIdeal_iff (rankBases g) f).mpr
  intro a ha
  have hmon := (mem_rankShiftIdeal_iff_coeff g i f).mp hf a ha
  exact (contains_rankBases_iff g a).mpr
    ((monomial_mem_rankShiftIdeal_partition_iff g i a).mp hmon).2.1

end Ideals

end CommAlg.Polymatroid

end
end CheckedSource58

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "59: CommAlg.Polymatroid.KoszulRankFormula\n"

/-! ## Source: CommAlg.Polymatroid.KoszulRankFormula -/
section CheckedSource59

/-! # The full rank formula for the actual upper Koszul complex

Every degree and every normalized monotone submodular rank is included.
The subsequent derived-Tor theorem transports this exact statement to
the homological shift ideal.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [LinearOrder V]

theorem mem_rankShiftFamily_iff_lower (g : RankFunction V) (i : ℕ) (a : Exponent V) :
    a ∈ rankShiftFamily g i ↔ a.degree = g univ + i ∧
      LowerFeasible g.lower a ∧ UpperFeasible (universalAugmentedRank g) a := by
  rw [mem_rankShiftFamily_iff]
  constructor
  · rintro ⟨hdeg, hb⟩
    refine ⟨hdeg, ?_, ?_⟩
    · intro U
      have hcomp := hb Uᶜ
      have hR := universalHomologicalRank_le_add g i Uᶜ
      have hL := g.lower_add_compl U
      have hS := subsetSum_add_compl a U
      omega
    · intro A
      exact (hb A).trans (shiftRankValue_le_u g (universalAugmentedRank g) i A)
  · rintro ⟨hdeg, hLower, hUpper⟩
    refine ⟨hdeg, ?_⟩
    intro A
    by_cases hA : A = ∅
    · simp [hA]
    rw [universalHomologicalRank_apply g i (Finset.nonempty_iff_ne_empty.mpr hA)]
    apply le_min
    · have hcomp := hLower Aᶜ
      have hL := g.lower_add_compl Aᶜ
      have hS := subsetSum_add_compl a A
      simp only [compl_compl] at hL
      omega
    · exact hUpper A

section Homology

variable {k : Type*} [CommRing k] [Nontrivial k]

theorem koszulFaces_nonzeroHomology_iff_rankShiftFamily
    (g : RankFunction V) (a : Exponent V) (i : ℕ) :
    Simplicial.NonzeroHomology (k := k) (Koszul.koszulFaces (rankBases g) a) i ↔
      a ∈ rankShiftFamily g i := by
  by_cases ha : Contains (rankBases g) a
  · have hLower := (contains_rankBases_iff g a).mp ha
    rw [Koszul.koszulFaces_eq_independenceFaces (rankBases g) g
      (contains_rankBases_iff g) a hLower,
      koszulConstraint_nonzeroHomology_iff_universal_full g hLower i,
      mem_rankShiftFamily_iff_lower]
    simp only [hLower, true_and]
    rfl
  · have hn : ¬ Simplicial.NonzeroHomology (k := k)
        (Koszul.koszulFaces (rankBases g) a) i := by
      rw [Simplicial.nonzeroHomology_iff_not_exactIn]
      apply not_not.mpr
      apply Simplicial.exactIn_of_no_face
      intro s hs
      exact (ha (Koszul.koszulFaces_contains hs)).elim
    have hm : a ∉ rankShiftFamily g i := by
      intro hm
      exact ha ((contains_rankBases_iff g a).mpr
        ((mem_rankShiftFamily_iff_lower g i a).mp hm).2.1)
    simp only [hn, hm]

end Homology

end CommAlg.Polymatroid

end
end CheckedSource59

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "60: CommAlg.Polymatroid.IntegerSandwich\n"

/-! ## Source: CommAlg.Polymatroid.IntegerSandwich -/
section CheckedSource60

/-! # Integral submodular / supermodular sandwich

An elementary coordinate-elimination proof, including integrality, supplies
the integer decomposition theorem needed for products of polymatroid ideals.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [DecidableEq V]

theorem integer_sandwich_on (E : Finset V) :
    ∀ (p q : Finset V → ℤ), p ∅ = 0 → q ∅ = 0 →
      (∀ A, A ⊆ E → ∀ B, B ⊆ E → p A + p B ≤ p (A ∪ B) + p (A ∩ B)) →
      (∀ A, A ⊆ E → ∀ B, B ⊆ E → q (A ∪ B) + q (A ∩ B) ≤ q A + q B) →
      (∀ A, A ⊆ E → p A ≤ q A) →
      ∃ b : V → ℤ, (∀ i, i ∉ E → b i = 0) ∧
        ∀ A, A ⊆ E → p A ≤ ∑ i ∈ A, b i ∧ (∑ i ∈ A, b i) ≤ q A := by
  induction E using Finset.induction_on with
  | empty =>
    intro p q hp0 hq0 hp hq hpq
    refine ⟨fun _ => 0, by simp, ?_⟩
    intro A hA
    have he : A = ∅ := Finset.subset_empty.mp hA
    simp [he, hp0, hq0]
  | @insert i E hi ih =>
    intro p q hp0 hq0 hp hq hpq
    have hpow : E.powerset.Nonempty := ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset _)⟩
    let t : ℤ := E.powerset.sup' hpow (fun A => p (insert i A) - q A)
    have htL : ∀ A, A ⊆ E → p (insert i A) - q A ≤ t := by
      intro A hA
      exact Finset.le_sup' (fun A => p (insert i A) - q A) (Finset.mem_powerset.mpr hA)
    have htR : ∀ B, B ⊆ E → t ≤ q (insert i B) - p B := by
      intro B hB
      apply Finset.sup'_le hpow _
      intro A hA
      have hA := Finset.mem_powerset.mp hA
      have hiA : i ∉ A := fun h => hi (hA h)
      have hiB : i ∉ B := fun h => hi (hB h)
      have hps := hp (insert i A) (Finset.insert_subset_insert i hA) B
        (hB.trans (Finset.subset_insert _ _))
      have hqs := hq A (hA.trans (Finset.subset_insert _ _)) (insert i B)
        (Finset.insert_subset_insert i hB)
      have hu := hpq (insert i (A ∪ B)) (Finset.insert_subset_insert i (Finset.union_subset hA hB))
      have hin := hpq (A ∩ B) ((Finset.inter_subset_left.trans hA).trans (Finset.subset_insert _ _))
      simp only [Finset.insert_union, Finset.union_insert,
        Finset.insert_inter_of_notMem hiB, Finset.inter_insert_of_notMem hiA] at hps hqs
      omega
    have htiL := htL ∅ (Finset.empty_subset E)
    have htiR := htR ∅ (Finset.empty_subset E)
    simp only [hp0, hq0, sub_zero] at htiL htiR
    let p' : Finset V → ℤ := fun A => max (p A) (p (insert i A) - t)
    let q' : Finset V → ℤ := fun A => min (q A) (q (insert i A) - t)
    have hp0' : p' ∅ = 0 := by
      change max (p ∅) (p (insert i ∅) - t) = 0
      rw [hp0]
      exact max_eq_left (by omega)
    have hq0' : q' ∅ = 0 := by
      change min (q ∅) (q (insert i ∅) - t) = 0
      rw [hq0]
      exact min_eq_left (by omega)
    have hp' : ∀ A, A ⊆ E → ∀ B, B ⊆ E →
        p' A + p' B ≤ p' (A ∪ B) + p' (A ∩ B) := by
      intro A hA B hB
      have hiA : i ∉ A := fun h => hi (hA h)
      have hiB : i ∉ B := fun h => hi (hB h)
      have hAE : A ⊆ insert i E := hA.trans (Finset.subset_insert _ _)
      have hBE : B ⊆ insert i E := hB.trans (Finset.subset_insert _ _)
      have hAiE := Finset.insert_subset_insert (a := i) hA
      have hBiE := Finset.insert_subset_insert (a := i) hB
      have h00 := hp A hAE B hBE
      have h10 := hp (insert i A) hAiE B hBE
      have h01 := hp A hAE (insert i B) hBiE
      have h11 := hp (insert i A) hAiE (insert i B) hBiE
      have hii : insert i A ∩ insert i B = insert i (A ∩ B) := by ext x; simp; tauto
      simp only [Finset.insert_union, Finset.union_insert, Finset.insert_idem, hii,
        Finset.insert_inter_of_notMem hiB, Finset.inter_insert_of_notMem hiA] at h10 h01 h11
      dsimp [p']
      omega
    have hq' : ∀ A, A ⊆ E → ∀ B, B ⊆ E →
        q' (A ∪ B) + q' (A ∩ B) ≤ q' A + q' B := by
      intro A hA B hB
      have hiA : i ∉ A := fun h => hi (hA h)
      have hiB : i ∉ B := fun h => hi (hB h)
      have hAE : A ⊆ insert i E := hA.trans (Finset.subset_insert _ _)
      have hBE : B ⊆ insert i E := hB.trans (Finset.subset_insert _ _)
      have hAiE := Finset.insert_subset_insert (a := i) hA
      have hBiE := Finset.insert_subset_insert (a := i) hB
      have h00 := hq A hAE B hBE
      have h10 := hq (insert i A) hAiE B hBE
      have h01 := hq A hAE (insert i B) hBiE
      have h11 := hq (insert i A) hAiE (insert i B) hBiE
      have hii : insert i A ∩ insert i B = insert i (A ∩ B) := by ext x; simp; tauto
      simp only [Finset.insert_union, Finset.union_insert, Finset.insert_idem, hii,
        Finset.insert_inter_of_notMem hiB, Finset.inter_insert_of_notMem hiA] at h10 h01 h11
      dsimp [q']
      omega
    have hpq' : ∀ A, A ⊆ E → p' A ≤ q' A := by
      intro A hA
      have h0 := hpq A (hA.trans (Finset.subset_insert _ _))
      have h1 := hpq (insert i A) (Finset.insert_subset_insert i hA)
      have hL := htL A hA
      have hR := htR A hA
      dsimp [p', q']
      omega
    obtain ⟨b, hb0, hb⟩ := ih p' q' hp0' hq0' hp' hq' hpq'
    let b' := Function.update b i t
    have hsum : ∀ A, i ∉ A → (∑ j ∈ A, b' j) = ∑ j ∈ A, b j := by
      intro A hiA
      apply Finset.sum_congr rfl
      intro j hj
      have hji : j ≠ i := fun he => hiA (he ▸ hj)
      simp [b', Function.update_of_ne hji]
    refine ⟨b', ?_, ?_⟩
    · intro j hj
      have hji : j ≠ i := fun h => hj (h ▸ Finset.mem_insert_self _ _)
      have hjE : j ∉ E := fun h => hj (Finset.mem_insert_of_mem h)
      simp [b', Function.update_of_ne hji, hb0 j hjE]
    · intro A hA
      by_cases hiA : i ∈ A
      · let A' := A.erase i
        have hA'E : A' ⊆ E := by
          intro j hj
          obtain ⟨hji, hjA⟩ := Finset.mem_erase.mp hj
          exact (Finset.mem_insert.mp (hA hjA)).resolve_left hji
        have hAi : insert i A' = A := Finset.insert_erase hiA
        have hbA := hb A' hA'E
        have hsumA : (∑ j ∈ A, b' j) = t + ∑ j ∈ A', b j := by
          rw [← hAi, Finset.sum_insert (Finset.notMem_erase _ _), hsum A' (Finset.notMem_erase _ _)]
          simp [b']
        have hpl : p (insert i A') - t ≤ p' A' := le_max_right _ _
        have hqu : q' A' ≤ q (insert i A') - t := min_le_right _ _
        rw [hAi] at hpl hqu
        rw [hsumA]
        omega
      · have hAE : A ⊆ E := by
          intro j hj
          exact (Finset.mem_insert.mp (hA hj)).resolve_left (fun h => hiA (h ▸ hj))
        have hbA := hb A hAE
        have hpl : p A ≤ p' A := le_max_left _ _
        have hqu : q' A ≤ q A := min_le_left _ _
        rw [hsum A hiA]
        omega

theorem integer_sandwich [Fintype V] (p q : Finset V → ℤ) (hp0 : p ∅ = 0) (hq0 : q ∅ = 0)
    (hp : ∀ A B, p A + p B ≤ p (A ∪ B) + p (A ∩ B))
    (hq : ∀ A B, q (A ∪ B) + q (A ∩ B) ≤ q A + q B)
    (hpq : ∀ A, p A ≤ q A) :
    ∃ b : V → ℤ, ∀ A, p A ≤ ∑ i ∈ A, b i ∧ (∑ i ∈ A, b i) ≤ q A := by
  obtain ⟨b, _, hb⟩ := integer_sandwich_on Finset.univ p q hp0 hq0
    (fun A _ B _ => hp A B) (fun A _ B _ => hq A B) (fun A _ => hpq A)
  exact ⟨b, fun A => hb A (Finset.subset_univ _)⟩

end CommAlg.Polymatroid

end
end CheckedSource60

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "61: CommAlg.Polymatroid.Minkowski\n"

/-! ## Source: CommAlg.Polymatroid.Minkowski -/
section CheckedSource61

/-! # Integral Minkowski decomposition of polymatroid bases -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem rank_base_decompose (g h : RankFunction V) {a : Exponent V}
    (ha : IsRankBase (g.add h) a) :
    ∃ b c : Exponent V, IsRankBase g b ∧ IsRankBase h c ∧ a = b + c := by
  let p : Finset V → ℤ := fun U => (subsetSum a U : ℤ) - h U
  let q : Finset V → ℤ := fun U => g U
  have hp0 : p ∅ = 0 := by simp [p]
  have hq0 : q ∅ = 0 := by simp [q]
  have hp : ∀ U W, p U + p W ≤ p (U ∪ W) + p (U ∩ W) := by
    intro U W
    have hs : (h (U ∪ W) : ℤ) + h (U ∩ W) ≤ h U + h W := by
      exact_mod_cast h.submodular U W
    have hm : (subsetSum a (U ∪ W) : ℤ) + subsetSum a (U ∩ W) =
        subsetSum a U + subsetSum a W := by
      exact_mod_cast (subsetSum_union_inter a U W).symm
    dsimp [p]
    omega
  have hq : ∀ U W, q (U ∪ W) + q (U ∩ W) ≤ q U + q W := by
    intro U W
    dsimp [q]
    exact_mod_cast g.submodular U W
  have hpq : ∀ U, p U ≤ q U := by
    intro U
    have hU : subsetSum a U ≤ g U + h U := ha.2 U
    have hz : (subsetSum a U : ℤ) ≤ g U + h U := by exact_mod_cast hU
    dsimp [p, q]
    omega
  obtain ⟨bZ, hbZ⟩ := integer_sandwich p q hp0 hq0 hp hq hpq
  have hadeg : a.degree = g Finset.univ + h Finset.univ := ha.1
  have hbtotal : (∑ i, bZ i) = (g Finset.univ : ℤ) := by
    have hb := hbZ Finset.univ
    dsimp [p, q] at hb
    rw [subsetSum_univ, hadeg] at hb
    push_cast at hb
    omega
  have hb0 : ∀ i, 0 ≤ bZ i := by
    intro i
    have hs := Finset.sum_erase_add Finset.univ bZ (Finset.mem_univ i)
    have hb := (hbZ (Finset.univ.erase i)).2
    have hg : (g (Finset.univ.erase i) : ℤ) ≤ g Finset.univ := by
      exact_mod_cast g.monotone (Finset.erase_subset _ _)
    change (∑ j ∈ Finset.univ.erase i, bZ j) ≤ (g (Finset.univ.erase i) : ℤ) at hb
    omega
  have hbaZ : ∀ i, bZ i ≤ (a i : ℤ) := by
    intro i
    have hs := Finset.sum_erase_add Finset.univ bZ (Finset.mem_univ i)
    have hb := (hbZ (Finset.univ.erase i)).1
    have hh : (h (Finset.univ.erase i) : ℤ) ≤ h Finset.univ := by
      exact_mod_cast h.monotone (Finset.erase_subset _ _)
    have haSum : (subsetSum a (Finset.univ.erase i) : ℤ) + a i = a.degree := by
      exact_mod_cast (show subsetSum a (Finset.univ.erase i) + a i = a.degree by
        simpa only [subsetSum, Finsupp.degree_eq_sum] using
          Finset.sum_erase_add Finset.univ a (Finset.mem_univ i))
    have hdegree : (a.degree : ℤ) = g Finset.univ + h Finset.univ := by exact_mod_cast hadeg
    dsimp [p] at hb
    omega
  let b : Exponent V := Finsupp.equivFunOnFinite.symm (fun i => (bZ i).toNat)
  have hbcast : ∀ i, (b i : ℤ) = bZ i := fun i => Int.toNat_of_nonneg (hb0 i)
  have hbsum : ∀ U, (subsetSum b U : ℤ) = ∑ i ∈ U, bZ i := by
    intro U
    simp only [subsetSum, Nat.cast_sum, hbcast]
  have hbdeg : b.degree = g Finset.univ := by
    have ht := hbsum Finset.univ
    rw [subsetSum_univ, hbtotal] at ht
    exact_mod_cast ht
  have hble : b ≤ a := by
    intro i
    have ht := hbaZ i
    rw [← hbcast i] at ht
    exact_mod_cast ht
  have hbupper : UpperFeasible g b := by
    intro U
    have ht := (hbZ U).2
    change (∑ i ∈ U, bZ i) ≤ (g U : ℤ) at ht
    rw [← hbsum U] at ht
    exact_mod_cast ht
  let c := a - b
  have hcb : c + b = a := tsub_add_cancel_of_le hble
  have hcdeg : c.degree = h Finset.univ := by
    have ht := congrArg Finsupp.degree hcb
    rw [map_add, hbdeg, hadeg] at ht
    omega
  have hcupper : UpperFeasible h c := by
    intro U
    have ht := (hbZ U).1
    have hs := congrArg (fun z : Exponent V => subsetSum z U) hcb
    rw [subsetSum_add] at hs
    have hsZ : (subsetSum c U : ℤ) + subsetSum b U = subsetSum a U := by exact_mod_cast hs
    dsimp [p] at ht
    rw [← hbsum U] at ht
    have hcZ : (subsetSum c U : ℤ) ≤ h U := by omega
    exact_mod_cast hcZ
  exact ⟨b, c, ⟨hbdeg, hbupper⟩, ⟨hcdeg, hcupper⟩, by simpa only [add_comm] using hcb.symm⟩

theorem rank_base_add {g h : RankFunction V} {b c : Exponent V}
    (hb : IsRankBase g b) (hc : IsRankBase h c) : IsRankBase (g.add h) (b + c) := by
  constructor
  · change (b + c).degree = g Finset.univ + h Finset.univ
    rw [map_add, hb.1, hc.1]
  · intro U
    change subsetSum (b + c) U ≤ g U + h U
    rw [subsetSum_add]
    exact Nat.add_le_add (hb.2 U) (hc.2 U)

theorem rank_base_minkowski (g h : RankFunction V) (a : Exponent V) :
    IsRankBase (g.add h) a ↔
      ∃ b c : Exponent V, IsRankBase g b ∧ IsRankBase h c ∧ a = b + c := by
  refine ⟨rank_base_decompose g h, ?_⟩
  rintro ⟨b, c, hb, hc, rfl⟩
  exact rank_base_add hb hc

theorem rankBases_add (g h : RankFunction V) :
    rankBases (g.add h) = ((rankBases g).product (rankBases h)).image (fun bc => bc.1 + bc.2) := by
  ext a
  constructor
  · intro ha
    obtain ⟨b, c, hb, hc, he⟩ := rank_base_decompose g h ((mem_rankBases _ _).mp ha)
    exact Finset.mem_image.mpr ⟨(b, c), Finset.mem_product.mpr
      ⟨(mem_rankBases _ _).mpr hb, (mem_rankBases _ _).mpr hc⟩, he.symm⟩
  · intro ha
    obtain ⟨⟨b, c⟩, hbc, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hb, hc⟩ := Finset.mem_product.mp hbc
    exact (mem_rankBases _ _).mpr (rank_base_add ((mem_rankBases _ _).mp hb)
      ((mem_rankBases _ _).mp hc))

end CommAlg.Polymatroid

end
end CheckedSource61

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "62: CommAlg.Polymatroid.IdealProducts\n"

/-! ## Source: CommAlg.Polymatroid.IdealProducts -/
section CheckedSource62

/-! # Products and powers of actual polymatroidal polynomial ideals -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset
open scoped Pointwise

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem monomialIdeal_mul (k : Type*) [CommSemiring k] (B C : Family V) :
    monomialIdeal k B * monomialIdeal k C =
      monomialIdeal k ((B.product C).image (fun bc => bc.1 + bc.2)) := by
  unfold monomialIdeal
  rw [Ideal.span_mul_span]
  apply congrArg Ideal.span
  ext f
  constructor
  · intro hf
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.mp hf
    obtain ⟨b, hb, rfl⟩ := hx
    obtain ⟨c, hc, rfl⟩ := hy
    refine ⟨b + c, Finset.mem_image.mpr ⟨(b, c), Finset.mem_product.mpr ⟨hb, hc⟩, rfl⟩, ?_⟩
    simp [MvPolynomial.monomial_mul]
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨⟨b, c⟩, hbc, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hb, hc⟩ := Finset.mem_product.mp hbc
    refine Set.mem_mul.mpr ⟨MvPolynomial.monomial b 1, ⟨b, hb, rfl⟩,
      MvPolynomial.monomial c 1, ⟨c, hc, rfl⟩, ?_⟩
    simp [MvPolynomial.monomial_mul]

theorem rankIdeal_add (k : Type*) [CommSemiring k] (g h : RankFunction V) :
    rankIdeal k (g.add h) = rankIdeal k g * rankIdeal k h := by
  rw [rankIdeal, rankBases_add, ← monomialIdeal_mul]
  rfl

theorem RankFunction.ext_fun {g h : RankFunction V} (he : ∀ U, g U = h U) : g = h := by
  cases g with | mk g g0 gm gs =>
    cases h with | mk h h0 hm hs =>
      congr 1
      exact funext he

theorem rankIdeal_scale_zero (k : Type*) [CommSemiring k] (g : RankFunction V) :
    rankIdeal k (g.scale 0) = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  have hb : (0 : Exponent V) ∈ rankBases (g.scale 0) := by
    rw [mem_rankBases]
    constructor
    · simp [RankFunction.scale]
    · intro U; simp [subsetSum, RankFunction.scale]
  have hm : MvPolynomial.monomial (0 : Exponent V) (1 : k) ∈ rankIdeal k (g.scale 0) :=
    Ideal.subset_span ⟨0, hb, rfl⟩
  simpa using hm

theorem rankIdeal_scale (k : Type*) [CommSemiring k] (g : RankFunction V) (s : ℕ) :
    rankIdeal k (g.scale s) = (rankIdeal k g) ^ s := by
  induction s with
  | zero => simpa using rankIdeal_scale_zero k g
  | succ s ih =>
    have hs : g.scale (s + 1) = (g.scale s).add g := by
      apply RankFunction.ext_fun
      intro U
      simp [RankFunction.scale, RankFunction.add, Nat.add_mul]
    rw [hs, rankIdeal_add, ih, pow_succ]

theorem family_eq_of_contains_iff {B C : Family V} (hB : Antichain B) (hC : Antichain C)
    (he : ∀ a, Contains B a ↔ Contains C a) : B = C := by
  apply Finset.Subset.antisymm
  · intro a ha
    obtain ⟨b, hb, hba⟩ := (he a).mp ⟨a, ha, le_rfl⟩
    obtain ⟨c, hc, hcb⟩ := (he b).mpr ⟨b, hb, le_rfl⟩
    have hca := hB c hc a ha (hcb.trans hba)
    have hab : a ≤ b := hca ▸ hcb
    have heq := le_antisymm hab hba
    rwa [heq]
  · intro a ha
    obtain ⟨b, hb, hba⟩ := (he a).mpr ⟨a, ha, le_rfl⟩
    obtain ⟨c, hc, hcb⟩ := (he b).mp ⟨b, hb, le_rfl⟩
    have hca := hC c hc a ha (hcb.trans hba)
    have hab : a ≤ b := hca ▸ hcb
    have heq := le_antisymm hab hba
    rwa [heq]

theorem rankIdeal_injective (k : Type*) [CommSemiring k] [Nontrivial k] :
    Function.Injective (rankIdeal (V := V) k) := by
  intro g h he
  apply rankBases_injective
  apply family_eq_of_contains_iff (rankBases_equigenerated g).antichain
    (rankBases_equigenerated h).antichain
  intro a
  rw [← monomial_mem_iff (k := k), ← monomial_mem_iff (k := k)]
  change (MvPolynomial.monomial a (1 : k) ∈ rankIdeal k g) ↔ _
  rw [he]
  rfl

end CommAlg.Polymatroid

end
end CheckedSource62

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "63: CommAlg.Polymatroid.HomologicalMain\n"

/-! ## Source: CommAlg.Polymatroid.HomologicalMain -/
section CheckedSource63

/-! # The main homological-shift rank theorem

The left-hand sides below use the nonzero multigraded components of
Mathlib's actual derived tensor functor. The proof identifies their
homogeneous Koszul complexes with genuine matroid independence chains,
then applies the fully proved rank and coloop criterion.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]

/-- All multigraded Betti support, with no degree, activity, or rank restriction. -/
theorem gradedBettiNonzero_rankBases_iff (g : RankFunction V) (a : Exponent V) (i : ℕ) :
    Koszul.GradedBettiNonzero (k := k) (rankBases g) a i ↔ a ∈ rankShiftFamily g i := by
  rw [Koszul.gradedBettiNonzero_iff_faces]
  exact koszulFaces_nonzeroHomology_iff_rankShiftFamily g a i

/-- Theorem 1.2, including zero layers, zero rank and inactive variables. -/
theorem homologicalShift_rankBases (g : RankFunction V) (i : ℕ) :
    Koszul.homologicalShift (k := k) (rankBases g) i = rankShiftIdeal k g i := by
  simp only [Koszul.homologicalShift, rankShiftIdeal_eq_monomialIdeal, monomialIdeal,
    gradedBettiNonzero_rankBases_iff]
  rfl

/-- The paper's partition-rank presentation on the active ground set. -/
theorem homologicalShift_rankBases_active (g : RankFunction V) (hg : g.Active) (i : ℕ) :
    Koszul.homologicalShift (k := k) (rankBases g) i =
      if homologicalRank g hg i univ = g univ + i then
        rankIdeal k (homologicalRank g hg i) else ⊥ := by
  rw [homologicalShift_rankBases, rankShiftIdeal]
  have he : universalHomologicalRank g i = homologicalRank g hg i := by
    apply RankFunction.ext_fun
    exact universalHomologicalRank_eq_active g hg i
  rw [he]

/-- Every nonempty equigenerated exchange family is covered by the rank theorem. -/
theorem homologicalShift_canonical (B : Family V) (hBne : B.Nonempty) (d : ℕ)
    (hdeg : Equigenerated B d) (hB : IsPolymatroidal B) (i : ℕ) :
    Koszul.homologicalShift (k := k) B i =
      rankShiftIdeal k (canonicalRank B hBne d hdeg hB) i := by
  simpa only [rankBases_canonical B hBne d hdeg hB] using
    (homologicalShift_rankBases (k := k) (canonicalRank B hBne d hdeg hB) i)

theorem gradedBettiNonzero_empty (a : Exponent V) (i : ℕ) :
    ¬ Koszul.GradedBettiNonzero (k := k) (∅ : Family V) a i := by
  rw [Koszul.gradedBettiNonzero_iff_faces, Simplicial.nonzeroHomology_iff_not_exactIn]
  apply not_not.mpr
  apply Simplicial.exactIn_of_no_face
  intro s hs
  obtain ⟨b, hb, _⟩ := Koszul.koszulFaces_contains hs
  exact (notMem_empty b hb).elim

/-- The zero ideal case, including every homological degree. -/
theorem homologicalShift_empty (i : ℕ) :
    Koszul.homologicalShift (k := k) (∅ : Family V) i = ⊥ := by
  simp [Koszul.homologicalShift, gradedBettiNonzero_empty]

/-- Homological shifts are polymatroidal, including the zero ideal. -/
theorem homologicalShift_polymatroidal (B : Family V) (hB : IsPolymatroidal B) (i : ℕ) :
    ∃ C : Family V, IsPolymatroidal C ∧
      Koszul.homologicalShift (k := k) B i = monomialIdeal k C := by
  by_cases hBne : B.Nonempty
  · obtain ⟨d, hdeg⟩ := hB.1
    let g := canonicalRank B hBne d hdeg hB
    refine ⟨rankShiftFamily g i, rankShiftFamily_polymatroidal g i, ?_⟩
    rw [homologicalShift_canonical B hBne d hdeg hB i, rankShiftIdeal_eq_monomialIdeal]
  · have he : B = ∅ := not_nonempty_iff_eq_empty.mp hBne
    subst B
    exact ⟨∅, hB, by simp [homologicalShift_empty, monomialIdeal]⟩

end CommAlg.Polymatroid

end
end CheckedSource63

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "64: CommAlg.Polymatroid.MultiRank\n"

/-! ## Source: CommAlg.Polymatroid.MultiRank -/
section CheckedSource64

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V J : Type*} [Fintype V] [DecidableEq V] [DecidableEq J]

def zeroRank : RankFunction V where
  toFun _ := 0
  empty := rfl
  monotone := fun _ _ _ => le_rfl
  submodular _ _ := le_rfl

def sumRanks (F : Finset J) (ρ : J → RankFunction V) : RankFunction V where
  toFun A := ∑ j ∈ F, ρ j A
  empty := by simp
  monotone := fun _ _ h => Finset.sum_le_sum (fun j _ => (ρ j).monotone h)
  submodular A B := by
    simpa only [← Finset.sum_add_distrib] using Finset.sum_le_sum (s := F)
      (fun j _ => (ρ j).submodular A B)

@[simp] theorem zeroRank_apply (A : Finset V) : zeroRank A = 0 := rfl

@[simp] theorem sumRanks_apply (F : Finset J) (ρ : J → RankFunction V) (A : Finset V) :
    sumRanks F ρ A = ∑ j ∈ F, ρ j A := rfl

@[simp] theorem sumRanks_empty (ρ : J → RankFunction V) : sumRanks ∅ ρ = zeroRank := by
  apply RankFunction.ext_fun
  intro A
  simp

theorem sumRanks_insert (F : Finset J) (ρ : J → RankFunction V) {j : J} (hj : j ∉ F) :
    sumRanks (insert j F) ρ = (ρ j).add (sumRanks F ρ) := by
  apply RankFunction.ext_fun
  intro A
  simp [RankFunction.add, hj]

theorem rankIdeal_zeroRank (k : Type*) [CommSemiring k] : rankIdeal k (zeroRank (V := V)) = ⊤ := by
  have hz : (zeroRank (V := V)).scale 0 = zeroRank := by
    apply RankFunction.ext_fun
    intro A
    rfl
  rw [← hz]
  exact rankIdeal_scale_zero k _

theorem rankIdeal_sumRanks (k : Type*) [CommSemiring k] (F : Finset J)
    (ρ : J → RankFunction V) : rankIdeal k (sumRanks F ρ) = ∏ j ∈ F, rankIdeal k (ρ j) := by
  induction F using Finset.induction_on with
  | empty => simp [rankIdeal_zeroRank]
  | @insert j F hj ih =>
    rw [sumRanks_insert F ρ hj, rankIdeal_add, ih, Finset.prod_insert hj]

def multiRank [Fintype J] (ρ : J → RankFunction V) (s : J →₀ ℕ) : RankFunction V :=
  sumRanks Finset.univ (fun j => (ρ j).scale (s j))

@[simp] theorem multiRank_apply [Fintype J] (ρ : J → RankFunction V) (s : J →₀ ℕ)
    (A : Finset V) : multiRank ρ s A = ∑ j, s j * ρ j A := rfl

@[simp] theorem multiRank_zero [Fintype J] (ρ : J → RankFunction V) : multiRank ρ 0 = zeroRank := by
  apply RankFunction.ext_fun
  intro A
  simp

theorem multiRank_add [Fintype J] (ρ : J → RankFunction V) (s t : J →₀ ℕ) :
    multiRank ρ (s + t) = (multiRank ρ s).add (multiRank ρ t) := by
  apply RankFunction.ext_fun
  intro A
  simp [RankFunction.add, Nat.add_mul, Finset.sum_add_distrib]

@[simp] theorem multiRank_single [Fintype J] (ρ : J → RankFunction V) (j : J) (n : ℕ) :
    multiRank ρ (Finsupp.single j n) = (ρ j).scale n := by
  apply RankFunction.ext_fun
  intro A
  simp [RankFunction.scale, Finsupp.single_apply]

/-- Exact equality of actual products of polynomial ideals, for every multidegree. -/
theorem rankIdeal_multiRank (k : Type*) [CommSemiring k] [Fintype J]
    (ρ : J → RankFunction V) (s : J →₀ ℕ) :
    rankIdeal k (multiRank ρ s) = ∏ j, (rankIdeal k (ρ j)) ^ (s j) := by
  rw [multiRank, rankIdeal_sumRanks]
  apply Finset.prod_congr rfl
  intro j hj
  exact rankIdeal_scale k (ρ j) (s j)

end CommAlg.Polymatroid

end
end CheckedSource64

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "65: CommAlg.Polymatroid.IdealBridge\n"

/-! ## Source: CommAlg.Polymatroid.IdealBridge -/
section CheckedSource65

/-! # Polymatroidal ideals as actual polynomial ideals

The defining exchange family is unique: every equigenerated family is an
antichain, and monomial membership recovers an antichain of generators.
Consequently the homological shift below is independent of a presentation;
it is computed from the genuine derived-Tor components of the actual ideal.
This bridge includes both the zero and the unit ideal.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]

def IsPolymatroidalIdeal (I : Ideal (MvPolynomial V k)) : Prop :=
  ∃ B : Family V, IsPolymatroidal B ∧ I = monomialIdeal k B

theorem monomialIdeal_family_unique {B C : Family V}
    (hB : IsPolymatroidal B) (hC : IsPolymatroidal C)
    (he : monomialIdeal k B = monomialIdeal k C) : B = C := by
  obtain ⟨d, hd⟩ := hB.1
  obtain ⟨e, heq⟩ := hC.1
  apply family_eq_of_contains_iff hd.antichain heq.antichain
  intro a
  rw [← monomial_mem_iff (k := k), ← monomial_mem_iff (k := k), he]

def idealGenerators (I : Ideal (MvPolynomial V k)) (hI : IsPolymatroidalIdeal I) : Family V :=
  hI.choose

theorem idealGenerators_polymatroidal (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) : IsPolymatroidal (idealGenerators I hI) :=
  hI.choose_spec.1

theorem monomialIdeal_idealGenerators (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) : monomialIdeal k (idealGenerators I hI) = I :=
  hI.choose_spec.2.symm

theorem idealGenerators_eq_of_presentation (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (B : Family V) (hB : IsPolymatroidal B)
    (he : I = monomialIdeal k B) : idealGenerators I hI = B :=
  monomialIdeal_family_unique (idealGenerators_polymatroidal I hI) hB
    ((monomialIdeal_idealGenerators I hI).trans he)

theorem isPolymatroidalIdeal_monomialIdeal (B : Family V) (hB : IsPolymatroidal B) :
    IsPolymatroidalIdeal (monomialIdeal k B) := ⟨B, hB, rfl⟩

theorem isPolymatroidalIdeal_rankIdeal (g : RankFunction V) :
    IsPolymatroidalIdeal (rankIdeal k g) :=
  ⟨rankBases g, rankBases_polymatroidal g, rfl⟩

theorem isPolymatroidalIdeal_bot : IsPolymatroidalIdeal (⊥ : Ideal (MvPolynomial V k)) := by
  refine ⟨∅, ⟨⟨0, by simp [Equigenerated]⟩, by simp [ExchangeAxiom]⟩, ?_⟩
  simp [monomialIdeal]

theorem isPolymatroidalIdeal_top : IsPolymatroidalIdeal (⊤ : Ideal (MvPolynomial V k)) := by
  simpa only [rankIdeal_zeroRank] using
    (isPolymatroidalIdeal_rankIdeal (k := k) (zeroRank (V := V)))

theorem IsPolymatroidalIdeal.eq_bot_or_rank {I : Ideal (MvPolynomial V k)}
    (hI : IsPolymatroidalIdeal I) : I = ⊥ ∨ ∃ g : RankFunction V, I = rankIdeal k g := by
  obtain ⟨B, hB, rfl⟩ := hI
  by_cases hne : B.Nonempty
  · obtain ⟨d, hd⟩ := hB.1
    refine Or.inr ⟨canonicalRank B hne d hd hB, ?_⟩
    rw [rankIdeal, rankBases_canonical B hne d hd hB]
  · have he := not_nonempty_iff_eq_empty.mp hne
    exact Or.inl (by simp [he, monomialIdeal])

theorem IsPolymatroidalIdeal.exists_rank {I : Ideal (MvPolynomial V k)}
    (hI : IsPolymatroidalIdeal I) (hne : I ≠ ⊥) : ∃ g : RankFunction V, I = rankIdeal k g :=
  hI.eq_bot_or_rank.resolve_left hne

theorem IsPolymatroidalIdeal.mul {I J : Ideal (MvPolynomial V k)}
    (hI : IsPolymatroidalIdeal I) (hJ : IsPolymatroidalIdeal J) :
    IsPolymatroidalIdeal (I * J) := by
  rcases hI.eq_bot_or_rank with rfl | ⟨g, rfl⟩
  · simpa using (isPolymatroidalIdeal_bot (V := V) (k := k))
  rcases hJ.eq_bot_or_rank with rfl | ⟨h, rfl⟩
  · simpa using (isPolymatroidalIdeal_bot (V := V) (k := k))
  rw [← rankIdeal_add]
  exact isPolymatroidalIdeal_rankIdeal _

theorem IsPolymatroidalIdeal.pow {I : Ideal (MvPolynomial V k)}
    (hI : IsPolymatroidalIdeal I) (s : ℕ) : IsPolymatroidalIdeal (I ^ s) := by
  induction s with
  | zero => simpa using (isPolymatroidalIdeal_top (V := V) (k := k))
  | succ s ih => simpa only [pow_succ] using ih.mul hI

theorem IsPolymatroidalIdeal.prod {J : Type*} (F : Finset J)
    (I : J → Ideal (MvPolynomial V k)) (hI : ∀ j ∈ F, IsPolymatroidalIdeal (I j)) :
    IsPolymatroidalIdeal (∏ j ∈ F, I j) := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using (isPolymatroidalIdeal_top (V := V) (k := k))
  | @insert j F hj ih =>
    rw [Finset.prod_insert hj]
    exact (hI j (mem_insert_self _ _)).mul (ih (fun x hx => hI x (mem_insert_of_mem hx)))

/-- The homological shift of an actual polymatroidal ideal. The uniquely
determined generator family only supplies the finite presentation used to
construct its standard multigrading on genuine derived Tor. -/
def homologicalShiftIdeal (I : Ideal (MvPolynomial V k)) (hI : IsPolymatroidalIdeal I)
    (i : ℕ) : Ideal (MvPolynomial V k) :=
  Koszul.homologicalShift (k := k) (idealGenerators I hI) i

theorem homologicalShiftIdeal_of_presentation (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (B : Family V) (hB : IsPolymatroidal B)
    (he : I = monomialIdeal k B) (i : ℕ) :
    homologicalShiftIdeal I hI i = Koszul.homologicalShift (k := k) B i := by
  unfold homologicalShiftIdeal
  rw [idealGenerators_eq_of_presentation I hI B hB he]

theorem homologicalShiftIdeal_eq_rankShiftIdeal (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (g : RankFunction V) (he : I = rankIdeal k g) (i : ℕ) :
    homologicalShiftIdeal I hI i = rankShiftIdeal k g i := by
  rw [homologicalShiftIdeal_of_presentation I hI (rankBases g) (rankBases_polymatroidal g) he,
    homologicalShift_rankBases]

@[simp] theorem homologicalShiftIdeal_bot (hI : IsPolymatroidalIdeal (⊥ : Ideal (MvPolynomial V k)))
    (i : ℕ) : homologicalShiftIdeal ⊥ hI i = ⊥ := by
  rw [homologicalShiftIdeal_of_presentation _ hI ∅
    ⟨⟨0, by simp [Equigenerated]⟩, by simp [ExchangeAxiom]⟩ (by simp [monomialIdeal]),
    homologicalShift_empty]

theorem homologicalShiftIdeal_congr {I J : Ideal (MvPolynomial V k)}
    (hI : IsPolymatroidalIdeal I) (hJ : IsPolymatroidalIdeal J) (he : I = J) (i : ℕ) :
    homologicalShiftIdeal I hI i = homologicalShiftIdeal J hJ i := by
  subst J
  rfl

theorem homologicalShiftIdeal_polymatroidal (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i : ℕ) : IsPolymatroidalIdeal (homologicalShiftIdeal I hI i) := by
  obtain ⟨B, hB, he⟩ := homologicalShift_polymatroidal (k := k) (idealGenerators I hI)
    (idealGenerators_polymatroidal I hI) i
  exact ⟨B, hB, he⟩

end CommAlg.Polymatroid

end
end CheckedSource65

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "66: CommAlg.Polymatroid.AffineMinimum\n"

/-! ## Source: CommAlg.Polymatroid.AffineMinimum -/
section CheckedSource66

/-! # Exact stabilization of capped minima of integer affine functions -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def cappedAffineMinimum (κ : ℕ) (δ b : ι → ℕ) (s : ℕ) : ℕ :=
  min κ (finiteMinimum (fun j => s * δ j + b j))

/-- Every positive integer slope has passed the cap once `s ≥ κ`. -/
theorem cappedAffineMinimum_stable (κ : ℕ) (δ b : ι → ℕ) {s : ℕ} (hs : κ ≤ s) :
    cappedAffineMinimum κ δ b (s + 1) = cappedAffineMinimum κ δ b s := by
  unfold cappedAffineMinimum
  rw [← finiteMinimum_min_left, ← finiteMinimum_min_left]
  congr 1
  funext j
  by_cases hd : δ j = 0
  · simp [hd]
  · have hp : 1 ≤ δ j := by omega
    have h0 : κ ≤ s * δ j + b j := by nlinarith
    have h1 : κ ≤ (s + 1) * δ j + b j := by nlinarith
    simp [min_eq_left h0, min_eq_left h1]

/-- The maximum of the clamped ceiling thresholds, with a zero entry for
each zero slope. `⌈/⌉` is Mathlib's exact natural ceiling division. -/
def affineThreshold (κ : ℕ) (δ b : ι → ℕ) : ℕ :=
  univ.sup (fun j => if δ j = 0 then 0 else (κ - b j) ⌈/⌉ δ j)

theorem affineThreshold_le_iff (κ : ℕ) (δ b : ι → ℕ)
    (hz : ∀ j, δ j = 0 → κ ≤ b j) (s : ℕ) :
    affineThreshold κ δ b ≤ s ↔ ∀ j, κ ≤ s * δ j + b j := by
  simp only [affineThreshold, Finset.sup_le_iff, Finset.mem_univ, forall_true_left]
  apply forall_congr'
  intro j
  by_cases hd : δ j = 0
  · simp [hd, hz j hd]
  · rw [if_neg hd, ceilDiv_le_iff_le_mul (by omega : 0 < δ j)]
    rw [Nat.mul_comm (δ j) s]
    omega

theorem affineThreshold_le_cap (κ : ℕ) (δ b : ι → ℕ) :
    affineThreshold κ δ b ≤ κ := by
  apply Finset.sup_le
  intro j hj
  by_cases hd : δ j = 0
  · simp [hd]
  · rw [if_neg hd, ceilDiv_le_iff_le_mul (by omega : 0 < δ j)]
    have hp : 1 ≤ δ j := by omega
    nlinarith [Nat.sub_le κ (b j)]

theorem cappedAffineMinimum_le_cap (κ : ℕ) (δ b : ι → ℕ) (s : ℕ) :
    cappedAffineMinimum κ δ b s ≤ κ := min_le_left _ _

theorem cappedAffineMinimum_eq_cap_iff (κ : ℕ) (δ b : ι → ℕ)
    (hz : ∀ j, δ j = 0 → κ ≤ b j) (s : ℕ) :
    cappedAffineMinimum κ δ b s = κ ↔ affineThreshold κ δ b ≤ s := by
  rw [cappedAffineMinimum, min_eq_left_iff, le_finiteMinimum_iff,
    affineThreshold_le_iff κ δ b hz s]

theorem cappedAffineMinimum_lt_cap_iff (κ : ℕ) (δ b : ι → ℕ)
    (hz : ∀ j, δ j = 0 → κ ≤ b j) (s : ℕ) :
    cappedAffineMinimum κ δ b s < κ ↔ s < affineThreshold κ δ b := by
  have he := cappedAffineMinimum_eq_cap_iff κ δ b hz s
  have hl := cappedAffineMinimum_le_cap κ δ b s
  omega

theorem cappedAffineMinimum_mono (κ : ℕ) (δ b : ι → ℕ) :
    Monotone (cappedAffineMinimum κ δ b) := by
  intro s t hst
  exact min_le_min_left κ (finiteMinimum_mono (fun j => by
    exact Nat.add_le_add_right (Nat.mul_le_mul_right (δ j) hst) (b j)))

/-- There are no gaps before stabilization: the value strictly increases
at every integer step below the exact ceiling threshold. -/
theorem cappedAffineMinimum_strict_step (κ : ℕ) (δ b : ι → ℕ)
    (hz : ∀ j, δ j = 0 → κ ≤ b j) {s : ℕ} (hs : s < affineThreshold κ δ b) :
    cappedAffineMinimum κ δ b s < cappedAffineMinimum κ δ b (s + 1) := by
  have hlt := (cappedAffineMinimum_lt_cap_iff κ δ b hz s).mpr hs
  by_cases hn : κ ≤ finiteMinimum (fun j => (s + 1) * δ j + b j)
  · simpa only [cappedAffineMinimum, min_eq_left hn] using hlt
  · obtain ⟨j, hj⟩ := finiteMinimum_attained (fun j => (s + 1) * δ j + b j)
    have hsmall : (s + 1) * δ j + b j < κ := by omega
    have hd : δ j ≠ 0 := by
      intro heq
      have hzj := hz j heq
      simp only [heq, Nat.mul_zero, Nat.zero_add] at hsmall
      omega
    have hprev : cappedAffineMinimum κ δ b s ≤ s * δ j + b j :=
      (min_le_right _ _).trans (finiteMinimum_le _ j)
    have hnext : cappedAffineMinimum κ δ b (s + 1) =
        finiteMinimum (fun j => (s + 1) * δ j + b j) := min_eq_right (by omega)
    rw [hnext, ← hj]
    rw [Nat.add_mul, Nat.one_mul]
    omega

theorem cappedAffineMinimum_step_eq_iff (κ : ℕ) (δ b : ι → ℕ)
    (hz : ∀ j, δ j = 0 → κ ≤ b j) (s : ℕ) :
    cappedAffineMinimum κ δ b (s + 1) = cappedAffineMinimum κ δ b s ↔
      affineThreshold κ δ b ≤ s := by
  constructor
  · intro heq
    by_contra hn
    have hlt := cappedAffineMinimum_strict_step κ δ b hz (by omega : s < affineThreshold κ δ b)
    omega
  · intro hs
    rw [(cappedAffineMinimum_eq_cap_iff κ δ b hz s).mpr hs,
      (cappedAffineMinimum_eq_cap_iff κ δ b hz (s + 1)).mpr (by omega)]

end CommAlg.Polymatroid

end
end CheckedSource66

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "67: CommAlg.Polymatroid.PowerStabilization\n"

/-! ## Source: CommAlg.Polymatroid.PowerStabilization -/
section CheckedSource67

/-! # The exact rank identity behind uniform stabilization of twisted powers -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem twistedPower_active (η ρ : RankFunction V)
    (h : (twistedPowerRank η ρ 1).Active) {s : ℕ} (hs : 1 ≤ s) :
    (twistedPowerRank η ρ s).Active := by
  intro A hA
  have h1 := h A hA
  simp only [twistedPowerRank_apply, Nat.one_mul] at h1 ⊢
  nlinarith

/-- Uniform stabilization retains arbitrary fixed twists and the entire
range `s ≥ i`. Its application to shift ideals uses the separate Tor theorem. -/
theorem twistedPower_homologicalRank_succ (η ρ : RankFunction V) (i s : ℕ)
    (hs : i ≤ s) (h0 : (twistedPowerRank η ρ s).Active)
    (h1 : (twistedPowerRank η ρ (s + 1)).Active) (A : Finset V) :
    homologicalRank (twistedPowerRank η ρ (s + 1)) h1 i A =
      ρ A + homologicalRank (twistedPowerRank η ρ s) h0 i A := by
  by_cases hA : A = ∅
  · simp [hA]
  have hA' := Finset.nonempty_iff_ne_empty.mpr hA
  rw [twistedPower_homologicalRank η ρ (s + 1) i h1 hA',
    twistedPower_homologicalRank η ρ s i h0 hA']
  have hcap := cappedAffineMinimum_stable i
    (fun P : Finpartition A => partitionDefect ρ P)
    (fun P => partitionDefect η P + partitionSlack P) hs
  simp only [cappedAffineMinimum, ← Nat.add_assoc] at hcap
  rw [hcap]
  simp only [twistedPowerRank_apply, Nat.add_mul, Nat.one_mul]
  omega

/-- The total-rank nonvanishing conditions agree for consecutive powers
throughout the uniform stabilization range. -/
theorem twistedPower_total_rank_eq_iff (η ρ : RankFunction V) (i s : ℕ)
    (hs : i ≤ s) (h0 : (twistedPowerRank η ρ s).Active)
    (h1 : (twistedPowerRank η ρ (s + 1)).Active) :
    homologicalRank (twistedPowerRank η ρ (s + 1)) h1 i univ =
        twistedPowerRank η ρ (s + 1) univ + i ↔
      homologicalRank (twistedPowerRank η ρ s) h0 i univ =
        twistedPowerRank η ρ s univ + i := by
  rw [twistedPower_homologicalRank_succ η ρ i s hs h0 h1 univ]
  simp only [twistedPowerRank_apply, Nat.add_mul, Nat.one_mul]
  omega

end CommAlg.Polymatroid

end
end CheckedSource67

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "68: CommAlg.Polymatroid.PartitionThreshold\n"

/-! ## Source: CommAlg.Polymatroid.PartitionThreshold -/
section CheckedSource68

/-! # Exact ceiling thresholds for every subset and every homological degree

The finite maximum over zero-defect partitions is the paper's `c_ρ(A)`;
the ceiling maximum is its `τ_i(A)`.  No degree or ground-set bound is used.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def zeroDefectPartitions (ρ : RankFunction V) (A : Finset V) : Finset (Finpartition A) :=
  univ.filter (fun P => partitionDefect ρ P = 0)

theorem zeroDefectPartitions_nonempty (ρ : RankFunction V) (A : Finset V) :
    (zeroDefectPartitions ρ A).Nonempty := by
  by_cases hA : A = ∅
  · subst A
    refine ⟨Finpartition.empty (Finset V), ?_⟩
    simp [zeroDefectPartitions, partitionDefect]
  · refine ⟨Finpartition.indiscrete hA, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simp [partitionDefect, Finpartition.indiscrete]

def zeroDefectComponents (ρ : RankFunction V) (A : Finset V) : ℕ :=
  (zeroDefectPartitions ρ A).sup (fun P => P.parts.card)

theorem zeroDefectComponents_le_card (ρ : RankFunction V) (A : Finset V) :
    zeroDefectComponents ρ A ≤ A.card :=
  Finset.sup_le (fun P _ => P.card_parts_le_card)

theorem zeroDefectComponents_attained (ρ : RankFunction V) (A : Finset V) :
    ∃ P : Finpartition A, partitionDefect ρ P = 0 ∧
      P.parts.card = zeroDefectComponents ρ A := by
  obtain ⟨P, hP, hmax⟩ := Finset.exists_max_image
    (zeroDefectPartitions ρ A) (fun P => P.parts.card) (zeroDefectPartitions_nonempty ρ A)
  refine ⟨P, (mem_filter.mp hP).2, ?_⟩
  change P.parts.card = (zeroDefectPartitions ρ A).sup (fun Q => Q.parts.card)
  exact le_antisymm (Finset.le_sup (f := fun Q : Finpartition A => Q.parts.card) hP)
    (Finset.sup_le (fun Q hQ => hmax Q hQ))

def eventualOffset (ρ : RankFunction V) (A : Finset V) : ℕ :=
  A.card - zeroDefectComponents ρ A

theorem eventualOffset_le_slack (ρ : RankFunction V) {A : Finset V}
    (P : Finpartition A) (hP : partitionDefect ρ P = 0) :
    eventualOffset ρ A ≤ partitionSlack P := by
  have hc : P.parts.card ≤ zeroDefectComponents ρ A := by
    change P.parts.card ≤ (zeroDefectPartitions ρ A).sup (fun Q => Q.parts.card)
    have hm : P ∈ zeroDefectPartitions ρ A := mem_filter.mpr ⟨mem_univ P, hP⟩
    exact Finset.le_sup (f := fun Q : Finpartition A => Q.parts.card) hm
  exact Nat.sub_le_sub_left hc A.card

theorem eventualOffset_attained (ρ : RankFunction V) (A : Finset V) :
    ∃ P : Finpartition A, partitionDefect ρ P = 0 ∧ partitionSlack P = eventualOffset ρ A := by
  obtain ⟨P, hd, hc⟩ := zeroDefectComponents_attained ρ A
  exact ⟨P, hd, congrArg (A.card - ·) hc⟩

def eventualCorrection (ρ : RankFunction V) (i : ℕ) (A : Finset V) : ℕ :=
  min i (eventualOffset ρ A)

def powerCorrection (ρ : RankFunction V) (i s : ℕ) (A : Finset V) : ℕ :=
  cappedAffineMinimum i (fun P : Finpartition A => partitionDefect ρ P)
    partitionSlack s

def powerThreshold (ρ : RankFunction V) (i : ℕ) (A : Finset V) : ℕ :=
  affineThreshold (eventualCorrection ρ i A)
    (fun P : Finpartition A => partitionDefect ρ P) partitionSlack

theorem eventualCorrection_le_zero_slack (ρ : RankFunction V) (i : ℕ) (A : Finset V) :
    ∀ P : Finpartition A, partitionDefect ρ P = 0 →
      eventualCorrection ρ i A ≤ partitionSlack P := by
  intro P hP
  exact (min_le_right _ _).trans (eventualOffset_le_slack ρ P hP)

theorem powerCorrection_recap (ρ : RankFunction V) (i s : ℕ) (A : Finset V) :
    powerCorrection ρ i s A =
      cappedAffineMinimum (eventualCorrection ρ i A)
        (fun P : Finpartition A => partitionDefect ρ P) partitionSlack s := by
  obtain ⟨P, hd, hb⟩ := eventualOffset_attained ρ A
  have hmin : finiteMinimum (fun P : Finpartition A => s * partitionDefect ρ P + partitionSlack P) ≤
      eventualOffset ρ A := by
    have h := finiteMinimum_le (fun P : Finpartition A =>
      s * partitionDefect ρ P + partitionSlack P) P
    simpa [hd, hb] using h
  unfold powerCorrection cappedAffineMinimum eventualCorrection
  rw [min_assoc, min_eq_right hmin]

theorem powerThreshold_le (ρ : RankFunction V) (i : ℕ) (A : Finset V) :
    powerThreshold ρ i A ≤ i :=
  (affineThreshold_le_cap _ _ _).trans (min_le_left _ _)

theorem powerCorrection_eq_eventual_iff (ρ : RankFunction V) (i s : ℕ) (A : Finset V) :
    powerCorrection ρ i s A = eventualCorrection ρ i A ↔ powerThreshold ρ i A ≤ s := by
  rw [powerCorrection_recap]
  exact cappedAffineMinimum_eq_cap_iff _ _ _ (eventualCorrection_le_zero_slack ρ i A) s

theorem powerCorrection_step_eq_iff (ρ : RankFunction V) (i s : ℕ) (A : Finset V) :
    powerCorrection ρ i (s + 1) A = powerCorrection ρ i s A ↔ powerThreshold ρ i A ≤ s := by
  rw [powerCorrection_recap ρ i (s + 1), powerCorrection_recap ρ i s]
  exact cappedAffineMinimum_step_eq_iff _ _ _ (eventualCorrection_le_zero_slack ρ i A) s

theorem powerCorrection_strict_step (ρ : RankFunction V) (i s : ℕ) (A : Finset V)
    (hs : s < powerThreshold ρ i A) :
    powerCorrection ρ i s A < powerCorrection ρ i (s + 1) A := by
  rw [powerCorrection_recap ρ i s, powerCorrection_recap ρ i (s + 1)]
  exact cappedAffineMinimum_strict_step _ _ _ (eventualCorrection_le_zero_slack ρ i A) hs

@[simp] theorem powerCorrection_zero (ρ : RankFunction V) (i : ℕ) (A : Finset V) :
    powerCorrection ρ i 0 A = 0 := by
  apply Nat.eq_zero_of_le_zero
  have h := finiteMinimum_le
    (fun P : Finpartition A => 0 * partitionDefect ρ P + partitionSlack P) (⊥ : Finpartition A)
  have hb : partitionSlack (⊥ : Finpartition A) = 0 := by simp [partitionSlack, Finpartition.card_bot]
  have hbound : powerCorrection ρ i 0 A ≤
      finiteMinimum (fun P : Finpartition A => 0 * partitionDefect ρ P + partitionSlack P) :=
    min_le_right _ _
  simpa [hb] using hbound.trans h

@[simp] theorem powerThreshold_empty (ρ : RankFunction V) (i : ℕ) :
    powerThreshold ρ i ∅ = 0 := by
  apply Nat.eq_zero_of_le_zero
  have h := affineThreshold_le_cap (eventualCorrection ρ i ∅)
    (fun P : Finpartition (∅ : Finset V) => partitionDefect ρ P) partitionSlack
  simpa [eventualCorrection, eventualOffset, powerThreshold] using h

theorem powerThreshold_pos (ρ : RankFunction V) {i : ℕ} (hi : 0 < i)
    {A : Finset V} (hA : i ≤ eventualOffset ρ A) : 1 ≤ powerThreshold ρ i A := by
  have he := powerCorrection_eq_eventual_iff ρ i 0 A
  have hκ : eventualCorrection ρ i A = i := min_eq_left hA
  rw [powerCorrection_zero, hκ] at he
  omega

theorem powerCorrection_eq_degree_iff (ρ : RankFunction V) (i s : ℕ) (A : Finset V)
    (hA : i ≤ eventualOffset ρ A) :
    powerCorrection ρ i s A = i ↔ powerThreshold ρ i A ≤ s := by
  have he := powerCorrection_eq_eventual_iff ρ i s A
  simpa only [eventualCorrection, min_eq_left hA] using he

theorem powerCorrection_lt_degree (ρ : RankFunction V) (i s : ℕ) (A : Finset V)
    (hA : eventualOffset ρ A < i) : powerCorrection ρ i s A < i := by
  rw [powerCorrection_recap]
  have h := cappedAffineMinimum_le_cap (eventualCorrection ρ i A)
    (fun P : Finpartition A => partitionDefect ρ P) partitionSlack s
  have hκ : eventualCorrection ρ i A = eventualOffset ρ A := min_eq_right hA.le
  omega

/-- The paper's maximum over all nonempty subsets; the empty subset contributes zero. -/
def globalPowerThreshold (ρ : RankFunction V) (i : ℕ) : ℕ :=
  univ.sup (powerThreshold ρ i)

theorem powerThreshold_le_global (ρ : RankFunction V) (i : ℕ) (A : Finset V) :
    powerThreshold ρ i A ≤ globalPowerThreshold ρ i := Finset.le_sup (mem_univ A)

theorem globalPowerThreshold_le (ρ : RankFunction V) (i : ℕ) :
    globalPowerThreshold ρ i ≤ i := Finset.sup_le (fun A _ => powerThreshold_le ρ i A)

theorem all_powerCorrection_step_eq_iff (ρ : RankFunction V) (i s : ℕ) :
    (∀ A, powerCorrection ρ i (s + 1) A = powerCorrection ρ i s A) ↔
      globalPowerThreshold ρ i ≤ s := by
  simp only [powerCorrection_step_eq_iff, globalPowerThreshold, Finset.sup_le_iff,
    Finset.mem_univ, forall_true_left]

theorem exists_strict_powerCorrection (ρ : RankFunction V) (i s : ℕ)
    (hs : s < globalPowerThreshold ρ i) :
    ∃ A : Finset V, A.Nonempty ∧
      powerCorrection ρ i s A < powerCorrection ρ i (s + 1) A := by
  have hex : ∃ A, s < powerThreshold ρ i A := by
    by_contra hn
    push Not at hn
    have hle : globalPowerThreshold ρ i ≤ s := Finset.sup_le (fun A _ => hn A)
    omega
  obtain ⟨A, hA⟩ := hex
  have hne : A ≠ ∅ := by intro heq; simp [heq] at hA
  exact ⟨A, Finset.nonempty_iff_ne_empty.mpr hne, powerCorrection_strict_step ρ i s A hA⟩

end CommAlg.Polymatroid

end
end CheckedSource68

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "69: CommAlg.Polymatroid.ShiftMultiplication\n"

/-! ## Source: CommAlg.Polymatroid.ShiftMultiplication -/
section CheckedSource69

/-! # Multiplication of rank-shift ideals, including all inactive coordinates

These are genuine ideal inclusions. The proof uses the exact partition
membership inequalities and is transported to homological shifts by the
separate graded-Tor rank formula.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem RankFunction.lower_add (f g : RankFunction V) (U : Finset V) :
    (f.add g).lower U = f.lower U + g.lower U := by
  have hf := f.lower_add_compl U
  have hg := g.lower_add_compl U
  have hfg := (f.add g).lower_add_compl U
  change (f.add g).lower U + (f Uᶜ + g Uᶜ) = f univ + g univ at hfg
  omega

section Ideals

variable {k : Type*} [CommSemiring k] [Nontrivial k]

theorem monomial_add_mem_rankShiftIdeal (f g : RankFunction V) (i : ℕ)
    (b a : Exponent V) (hb : LowerFeasible f.lower b)
    (ha : MvPolynomial.monomial a (1 : k) ∈ rankShiftIdeal k g i) :
    MvPolynomial.monomial (b + a) (1 : k) ∈ rankShiftIdeal k (f.add g) i := by
  obtain ⟨haDeg, haLower, haPart⟩ := (monomial_mem_rankShiftIdeal_partition_iff g i a).mp ha
  apply (monomial_mem_rankShiftIdeal_partition_iff (f.add g) i (b + a)).mpr
  refine ⟨?_, ?_, ?_⟩
  · have hbDeg := hb univ
    simp only [RankFunction.lower_univ, subsetSum_univ] at hbDeg
    change (f univ + g univ) + i ≤ (b + a).degree
    rw [map_add]
    omega
  · intro U
    rw [RankFunction.lower_add, subsetSum_add]
    exact Nat.add_le_add (hb U) (haLower U)
  · intro A hA P
    have hpa := haPart A hA P
    have hbf := hb Aᶜ
    have hfcomp := f.lower_add_compl Aᶜ
    simp only [compl_compl] at hfcomp
    have hfpart := f.le_sum_partition P
    change (f univ + g univ) + i + P.parts.card ≤
      subsetSum (b + a) Aᶜ + A.card + ∑ C ∈ P.parts, (f C + g C)
    rw [subsetSum_add, Finset.sum_add_distrib]
    omega

/-- Lemma 3.4 for the exact formula ideals, with no positivity or activity
restriction on either rank. -/
theorem rankIdeal_mul_rankShiftIdeal_le (f g : RankFunction V) (i : ℕ) :
    rankIdeal k f * rankShiftIdeal k g i ≤ rankShiftIdeal k (f.add g) i := by
  rw [rankIdeal, rankShiftIdeal_eq_monomialIdeal, monomialIdeal_mul]
  apply Ideal.span_le.mpr
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨⟨b, c⟩, hbc, rfl⟩ := mem_image.mp ha
  obtain ⟨hb, hc⟩ := mem_product.mp hbc
  have hb' : LowerFeasible f.lower b :=
    (contains_rankBases_iff f b).mp ⟨b, hb, le_rfl⟩
  have hc' : MvPolynomial.monomial c (1 : k) ∈ rankShiftIdeal k g i := by
    rw [rankShiftIdeal_eq_monomialIdeal]
    exact Ideal.subset_span ⟨c, hc, rfl⟩
  exact monomial_add_mem_rankShiftIdeal f g i b c hb' hc'

end Ideals

end CommAlg.Polymatroid

end
end CheckedSource69

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "70: CommAlg.Polymatroid.PowerShiftInterval\n"

/-! ## Source: CommAlg.Polymatroid.PowerShiftInterval -/
section CheckedSource70

/-!
# Exact nonvanishing and consecutive ideal equality for power shifts

The partition thresholds are connected here to the actual polynomial ideals
on the right-hand side of the graded-Tor formula. Canonical ranks, recovered
from their integer bases, detect equality of those ideals.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem RankFunction.Active.scale {ρ : RankFunction V} (hρ : ρ.Active)
    {s : ℕ} (hs : 1 ≤ s) : (RankFunction.scale s ρ).Active := by
  intro A hA
  have h := hρ A hA
  change 1 ≤ s * ρ A
  nlinarith

@[simp] theorem powerCorrection_empty (ρ : RankFunction V) (i s : ℕ) :
    powerCorrection ρ i s ∅ = 0 := by
  have h := (powerCorrection_eq_eventual_iff ρ i s ∅).mpr (by simp)
  simpa [eventualCorrection, eventualOffset] using h

theorem power_homologicalRank (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) {s : ℕ} (hs : 1 ≤ s) (A : Finset V) :
    universalHomologicalRank (RankFunction.scale s ρ) i A =
      s * ρ A + powerCorrection ρ i s A := by
  by_cases hA : A = ∅
  · simp [hA]
  have hne := nonempty_iff_ne_empty.mpr hA
  rw [universalHomologicalRank_eq_active _ (hρ.scale hs),
    homologicalRank_defect _ (hρ.scale hs) i hne]
  simp only [partitionDefect_scale]
  rfl

theorem powerShiftFamily_nonempty_iff (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) {s : ℕ} (hs : 1 ≤ s) :
    (rankShiftFamily (RankFunction.scale s ρ) i).Nonempty ↔
      powerCorrection ρ i s univ = i := by
  rw [rankShiftFamily_nonempty_iff, power_homologicalRank ρ hρ i hs univ]
  change s * ρ univ + powerCorrection ρ i s univ = s * ρ univ + i ↔ _
  exact Nat.add_left_cancel_iff

theorem powerShiftFamily_nonempty_iff_threshold (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) (hi : i ≤ eventualOffset ρ univ) {s : ℕ} (hs : 1 ≤ s) :
    (rankShiftFamily (RankFunction.scale s ρ) i).Nonempty ↔
      powerThreshold ρ i univ ≤ s := by
  rw [powerShiftFamily_nonempty_iff ρ hρ i hs,
    powerCorrection_eq_degree_iff ρ i s univ hi]

theorem powerShiftFamily_empty_of_above (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) (hi : eventualOffset ρ univ < i) {s : ℕ} (hs : 1 ≤ s) :
    rankShiftFamily (RankFunction.scale s ρ) i = ∅ := by
  apply not_nonempty_iff_eq_empty.mp
  rw [powerShiftFamily_nonempty_iff ρ hρ i hs]
  exact ne_of_lt (powerCorrection_lt_degree ρ i s univ hi)

theorem power_homologicalRank_add_eq_iff (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) {s : ℕ} (hs : 1 ≤ s) :
    ρ.add (universalHomologicalRank (RankFunction.scale s ρ) i) =
        universalHomologicalRank (RankFunction.scale (s + 1) ρ) i ↔
      globalPowerThreshold ρ i ≤ s := by
  rw [← all_powerCorrection_step_eq_iff]
  constructor
  · intro h A
    have he := congrArg (fun g : RankFunction V => g A) h
    change ρ A + universalHomologicalRank (RankFunction.scale s ρ) i A =
      universalHomologicalRank (RankFunction.scale (s + 1) ρ) i A at he
    rw [power_homologicalRank ρ hρ i hs,
      power_homologicalRank ρ hρ i (by omega)] at he
    nlinarith
  · intro h
    apply RankFunction.ext_fun
    intro A
    change ρ A + universalHomologicalRank (RankFunction.scale s ρ) i A =
      universalHomologicalRank (RankFunction.scale (s + 1) ρ) i A
    rw [power_homologicalRank ρ hρ i hs,
      power_homologicalRank ρ hρ i (by omega), h A]
    nlinarith

section Ideals

variable {k : Type*} [CommSemiring k] [Nontrivial k]

theorem monomialIdeal_ne_bot_iff (B : Family V) :
    monomialIdeal k B ≠ ⊥ ↔ B.Nonempty := by
  constructor
  · intro h
    by_contra hn
    have he := not_nonempty_iff_eq_empty.mp hn
    exact h (by simp [he, monomialIdeal])
  · rintro ⟨a, ha⟩ hbot
    have hm : MvPolynomial.monomial a (1 : k) ∈ monomialIdeal k B :=
      Ideal.subset_span ⟨a, ha, rfl⟩
    rw [hbot] at hm
    simpa using hm

theorem rankShiftIdeal_ne_bot_iff (g : RankFunction V) (i : ℕ) :
    rankShiftIdeal k g i ≠ ⊥ ↔ (rankShiftFamily g i).Nonempty := by
  rw [rankShiftIdeal_eq_monomialIdeal, monomialIdeal_ne_bot_iff]

theorem powerShiftIdeal_ne_bot_iff_threshold (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) (hi : i ≤ eventualOffset ρ univ) {s : ℕ} (hs : 1 ≤ s) :
    rankShiftIdeal k (RankFunction.scale s ρ) i ≠ ⊥ ↔
      powerThreshold ρ i univ ≤ s := by
  rw [rankShiftIdeal_ne_bot_iff, powerShiftFamily_nonempty_iff_threshold ρ hρ i hi hs]

theorem powerShiftIdeal_eq_bot_of_above (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) (hi : eventualOffset ρ univ < i) {s : ℕ} (hs : 1 ≤ s) :
    rankShiftIdeal k (RankFunction.scale s ρ) i = ⊥ := by
  rw [rankShiftIdeal_eq_monomialIdeal, powerShiftFamily_empty_of_above ρ hρ i hi hs]
  simp [monomialIdeal]

theorem powerShiftIdeal_mul_le (ρ : RankFunction V) (i n s : ℕ) :
    (rankIdeal k ρ) ^ n * rankShiftIdeal k (RankFunction.scale s ρ) i ≤
      rankShiftIdeal k (RankFunction.scale (n + s) ρ) i := by
  have h := rankIdeal_mul_rankShiftIdeal_le (k := k)
    (RankFunction.scale n ρ) (RankFunction.scale s ρ) i
  have he : (RankFunction.scale n ρ).add (RankFunction.scale s ρ) =
      RankFunction.scale (n + s) ρ := by
    apply RankFunction.ext_fun
    intro A
    change n * ρ A + s * ρ A = (n + s) * ρ A
    exact (Nat.add_mul n s (ρ A)).symm
  rwa [rankIdeal_scale, he] at h

/-- After the first nonzero piece, consecutive actual ideals agree under
the Rees action exactly at and beyond the global threshold. -/
theorem powerShiftIdeal_mul_eq_iff (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) (hi : i ≤ eventualOffset ρ univ) {s : ℕ} (hs : 1 ≤ s)
    (hr : powerThreshold ρ i univ ≤ s) :
    rankIdeal k ρ * rankShiftIdeal k (RankFunction.scale s ρ) i =
        rankShiftIdeal k (RankFunction.scale (s + 1) ρ) i ↔
      globalPowerThreshold ρ i ≤ s := by
  have h0 := (rankShiftFamily_nonempty_iff _ i).mp
    ((powerShiftFamily_nonempty_iff_threshold ρ hρ i hi hs).mpr hr)
  have h1 := (rankShiftFamily_nonempty_iff _ i).mp
    ((powerShiftFamily_nonempty_iff_threshold ρ hρ i hi (by omega)).mpr
      (show powerThreshold ρ i univ ≤ s + 1 by omega))
  rw [rankShiftIdeal, if_pos h0, rankShiftIdeal, if_pos h1, ← rankIdeal_add]
  rw [(rankIdeal_injective k).eq_iff]
  exact power_homologicalRank_add_eq_iff ρ hρ i hs

end Ideals

end CommAlg.Polymatroid

end
end CheckedSource70

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "71: CommAlg.KoszulComplex.TorGrading\n"

/-! ## Source: CommAlg.KoszulComplex.TorGrading -/
section CheckedSource71

/-! # Completeness and independence of the genuine Tor multigrading

Every derived Tor class is a finite sum of the degree components defined in `GradedTor`.
The projections onto distinct components annihilate one another, so this is a genuine
internal grading of the actual derived tensor module.
-/

noncomputable section
set_option maxHeartbeats 300000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false

namespace CommAlg.Koszul
open Classical CommAlg.Polymatroid CategoryTheory CategoryTheory.Limits
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

/-- Distinct multidegrees have orthogonal chain projections. -/
lemma homogeneousInclusion_retraction_ne (B : Family V) (a b : Exponent V)
    (hab : a ≠ b) :
    homogeneousInclusion (k := k) B a ≫ homogeneousRetraction (k := k) B b = 0 := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  exact Grading.projection_eq_zero (Ne.symm hab) z.property

/-- The chain endomorphism projecting to one degree and including it again. -/
def homogeneousProjector (B : Family V) (a : Exponent V) :
    underlyingComplex (k := k) B ⟶ underlyingComplex (k := k) B :=
  homogeneousRetraction (k := k) B a ≫ homogeneousInclusion (k := k) B a

@[simp] lemma homogeneousProjector_f (B : Family V) (a : Exponent V) (i : ℕ) :
    (homogeneousProjector (k := k) B a).f i =
      ModuleCat.ofHom (homogeneousProjection (k := k) B a i) := rfl

/-- Every actual Koszul homology class is a finite sum of its homogeneous projections. -/
lemma homogeneous_homology_decomposition (B : Family V) (i : ℕ)
    (x : (underlyingComplex (k := k) B).homology i) :
    ∃ s : Finset (Exponent V),
      ∑ a ∈ s, HomologicalComplex.homologyMap (homogeneousProjector (k := k) B a) i x = x := by
  let K := underlyingComplex (k := k) B
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ i)).mp inferInstance x
  let s := ((monomialCoefficientBasis (k := k) B i).repr (K.iCycles i z)).support.image
    monomialDegree
  have hz : ∑ a ∈ s, HomologicalComplex.cyclesMap
      (homogeneousProjector (k := k) B a) i z = z := by
    apply (ModuleCat.mono_iff_injective (K.iCycles i)).mp inferInstance
    rw [map_sum]
    calc
      ∑ a ∈ s, K.iCycles i
          (HomologicalComplex.cyclesMap (homogeneousProjector (k := k) B a) i z) =
          ∑ a ∈ s, homogeneousProjection (k := k) B a i (K.iCycles i z) := by
        apply Finset.sum_congr rfl
        intro a ha
        have h := congrArg (fun f : K.cycles i ⟶ K.X i => f z)
          (HomologicalComplex.cyclesMap_i (homogeneousProjector (k := k) B a) i)
        exact h
      _ = _ := homogeneous_decomposition B i (K.iCycles i z)
  refine ⟨s, ?_⟩
  calc
    ∑ a ∈ s, HomologicalComplex.homologyMap (homogeneousProjector (k := k) B a) i
        (K.homologyπ i z) =
        ∑ a ∈ s, K.homologyπ i
          (HomologicalComplex.cyclesMap (homogeneousProjector (k := k) B a) i z) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact congrArg (fun f : K.cycles i ⟶ K.homology i => f z)
        (HomologicalComplex.homologyπ_naturality (homogeneousProjector (k := k) B a) i)
    _ = K.homologyπ i
        (∑ a ∈ s, HomologicalComplex.cyclesMap
          (homogeneousProjector (k := k) B a) i z) := (map_sum _ _ _).symm
    _ = _ := congrArg (K.homologyπ i) hz

variable [Nontrivial k]

/-- A nonzero multigraded Betti component forces the genuine derived Tor module to be nonzero. -/
lemma derivedTor_nonzero_of_graded (B : Family V) (a : Exponent V) (i : ℕ)
    (h : GradedBettiNonzero (k := k) B a i) :
    ¬ IsZero (finitePolynomialTor i
      (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B))) := by
  intro hz
  letI : Subsingleton (finitePolynomialTor i
      (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B))) :=
    ModuleCat.isZero_iff_subsingleton.mp hz
  apply h
  apply ModuleCat.isZero_iff_subsingleton.mpr
  constructor
  intro x y
  apply Subtype.ext
  exact Subsingleton.elim (α := finitePolynomialTor i
    (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B))) x.val y.val

end CommAlg.Koszul

end
end CheckedSource71

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "72: CommAlg.KoszulComplex.BettiNumbers\n"

/-! ## Source: CommAlg.KoszulComplex.BettiNumbers -/
section CheckedSource72

/-! # Genuine finite multigraded Betti numbers

Over a field, every homogeneous component of the derived Tor module is finite-dimensional.
Its dimension therefore has positive support exactly at the degree components used to define
homological shift ideals.
-/

noncomputable section
set_option maxHeartbeats 300000
set_option maxRecDepth 2500
namespace CommAlg.Koszul
open Classical CommAlg.Polymatroid CategoryTheory CategoryTheory.Limits
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

instance homogeneousPiece_finite (B : Family V) (a : Exponent V) (i : ℕ) :
    FiniteDimensional k (homogeneousPiece (k := k) B a i) := by
  letI : FiniteDimensional k (Simplicial.Chains (k := k) (koszulFaces B a) i) :=
    (faceChainBasis (k := k) B a i).finiteDimensional_of_finite
  exact FiniteDimensional.of_injective (faceHomogeneousEquiv (k := k) B a i).symm.toLinearMap
    (faceHomogeneousEquiv (k := k) B a i).symm.injective

instance homogeneousHomology_finite (B : Family V) (a : Exponent V) (i : ℕ) :
    FiniteDimensional k ((homogeneousComplex (k := k) B a).homology i) := by
  let K := homogeneousComplex (k := k) B a
  letI : FiniteDimensional k (K.X i) := homogeneousPiece_finite B a i
  letI : FiniteDimensional k (K.cycles i) :=
    FiniteDimensional.of_injective (K.iCycles i).hom
      ((ModuleCat.mono_iff_injective (K.iCycles i)).mp inferInstance)
  exact FiniteDimensional.of_surjective (K.homologyπ i).hom
    ((ModuleCat.epi_iff_surjective (K.homologyπ i)).mp inferInstance)

instance gradedTor_finite (B : Family V) (a : Exponent V) (i : ℕ) :
    FiniteDimensional k (gradedTor (k := k) B a i) := by
  exact FiniteDimensional.of_injective (gradedTorIso (k := k) B a i).inv.hom
    ((ModuleCat.mono_iff_injective (gradedTorIso (k := k) B a i).inv).mp inferInstance)

/-- The actual multigraded Betti number: dimension of the corresponding derived Tor component. -/
def bettiNumber (B : Family V) (a : Exponent V) (i : ℕ) : ℕ :=
  Module.finrank k (gradedTor (k := k) B a i)

lemma bettiNumber_pos_iff (B : Family V) (a : Exponent V) (i : ℕ) :
    0 < bettiNumber (k := k) B a i ↔ GradedBettiNonzero (k := k) B a i := by
  unfold bettiNumber GradedBettiNonzero
  rw [Nat.pos_iff_ne_zero]
  have he : Module.finrank k (gradedTor (k := k) B a i) = 0 ↔
      Subsingleton (gradedTor (k := k) B a i) :=
    Module.finrank_zero_iff (R := k) (M := gradedTor (k := k) B a i)
  exact (not_congr he).trans (not_congr (ModuleCat.isZero_iff_subsingleton
    (M := ModuleCat.of k (gradedTor (k := k) B a i))).symm)

lemma bettiNumber_pos_iff_faces (B : Family V) (a : Exponent V) (i : ℕ) :
    0 < bettiNumber (k := k) B a i ↔
      Simplicial.NonzeroHomology (k := k) (koszulFaces B a) i := by
  rw [bettiNumber_pos_iff, gradedBettiNonzero_iff_faces]

end CommAlg.Koszul

end
end CheckedSource72

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "73: CommAlg.Polymatroid.HomologicalRankTheorem\n"

/-! ## Source: CommAlg.Polymatroid.HomologicalRankTheorem -/
section CheckedSource73

/-! # The ideal-level rank formula and numerical Betti correspondence -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]

/-- Theorem 1.2 as a literal equality of actual homological-shift ideals. -/
theorem homologicalShiftIdeal_partitionFormula (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (g : RankFunction V) (he : I = rankIdeal k g)
    (hg : g.Active) (i : ℕ) :
    homologicalShiftIdeal I hI i =
      if homologicalRank g hg i univ = g univ + i then
        rankIdeal k (homologicalRank g hg i) else ⊥ := by
  rw [homologicalShiftIdeal_of_presentation I hI (rankBases g) (rankBases_polymatroidal g) he]
  exact homologicalShift_rankBases_active g hg i

theorem homologicalShiftIdeal_generators (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (g : RankFunction V) (he : I = rankIdeal k g) (i : ℕ) :
    idealGenerators (homologicalShiftIdeal I hI i) (homologicalShiftIdeal_polymatroidal I hI i) =
      rankShiftFamily g i := by
  apply idealGenerators_eq_of_presentation _ _ _ (rankShiftFamily_polymatroidal g i)
  rw [homologicalShiftIdeal_eq_rankShiftIdeal I hI g he i, rankShiftIdeal_eq_monomialIdeal]

/-- The rank displayed in the main theorem is the canonical rank of the
actual minimal generators whenever the homological shift is nonzero. -/
theorem homologicalShiftIdeal_canonicalRank (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (g : RankFunction V) (he : I = rankIdeal k g) (i : ℕ)
    (hne : homologicalShiftIdeal I hI i ≠ ⊥) (A : Finset V) :
    upperRank (idealGenerators (homologicalShiftIdeal I hI i)
      (homologicalShiftIdeal_polymatroidal I hI i)) A = universalHomologicalRank g i A := by
  rw [homologicalShiftIdeal_generators I hI g he i]
  apply rankShiftFamily_upperRank
  rw [homologicalShiftIdeal_eq_rankShiftIdeal I hI g he i] at hne
  exact (rankShiftIdeal_ne_bot_iff g i).mp hne

section Field

variable {l : Type u} [Field l]

/-- The numerical multigraded Betti numbers have precisely the stated
rank-family support; finite-dimensionality is independently proved. -/
theorem bettiNumber_rankBases_pos_iff (g : RankFunction V) (a : Exponent V) (i : ℕ) :
    0 < Koszul.bettiNumber (k := l) (rankBases g) a i ↔ a ∈ rankShiftFamily g i := by
  rw [Koszul.bettiNumber_pos_iff, gradedBettiNonzero_rankBases_iff]

theorem bettiNumber_ideal_pos_iff (I : Ideal (MvPolynomial V l))
    (hI : IsPolymatroidalIdeal I) (g : RankFunction V) (he : I = rankIdeal l g)
    (a : Exponent V) (i : ℕ) :
    0 < Koszul.bettiNumber (k := l) (idealGenerators I hI) a i ↔
      a ∈ rankShiftFamily g i := by
  rw [idealGenerators_eq_of_presentation I hI (rankBases g) (rankBases_polymatroidal g) he,
    bettiNumber_rankBases_pos_iff]

end Field

end CommAlg.Polymatroid

end
end CheckedSource73

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "74: CommAlg.Polymatroid.UniversalPowerStabilization\n"

/-! ## Source: CommAlg.Polymatroid.UniversalPowerStabilization -/
section CheckedSource74

/-! # Uniform stabilization without an activity restriction

The universal partition rank treats inactive variables with their correct
integer block costs. Its defect formula proves the entire range `s ≥ i` for
arbitrary twists, and the resulting identities are equalities of actual
polynomial ideals, including the vanishing shift cases.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem cardinalLift_partition_cost_defect (g : RankFunction V)
    {A : Finset V} (P : Finpartition A) :
    partitionCost (cardinalLift g) P = g A + partitionDefect g P + partitionSlack P := by
  have hc := cardinalLift_cost_add_parts g P
  have hd := partitionDefect_add_rank g P
  have hs := partitionSlack_add_parts P
  omega

theorem universalAugmentedRank_defect (g : RankFunction V) (A : Finset V) :
    universalAugmentedRank g A =
      g A + finiteMinimum (fun P : Finpartition A => partitionDefect g P + partitionSlack P) := by
  change finiteMinimum (fun P : Finpartition A => partitionCost (cardinalLift g) P) = _
  rw [← finiteMinimum_add_const]
  congr 1
  funext P
  simpa only [Nat.add_assoc] using cardinalLift_partition_cost_defect g P

theorem universalHomologicalRank_defect (g : RankFunction V) (i : ℕ)
    {A : Finset V} (hA : A.Nonempty) :
    universalHomologicalRank g i A = g A +
      min i (finiteMinimum (fun P : Finpartition A => partitionDefect g P + partitionSlack P)) := by
  rw [universalHomologicalRank_apply g i hA, universalAugmentedRank_defect,
    Nat.add_min_add_left]

theorem twistedPower_universalHomologicalRank (η ρ : RankFunction V) (s i : ℕ)
    {A : Finset V} (hA : A.Nonempty) :
    universalHomologicalRank (twistedPowerRank η ρ s) i A =
      twistedPowerRank η ρ s A + min i
        (finiteMinimum (fun P : Finpartition A =>
          s * partitionDefect ρ P + partitionDefect η P + partitionSlack P)) := by
  rw [universalHomologicalRank_defect _ i hA]
  simp only [twistedPower_defect]

/-- The rank identity is valid for all ranks, including loops and the unit
ideal, with no deletion of coordinates. -/
theorem twistedPower_universalHomologicalRank_succ (η ρ : RankFunction V) (i s : ℕ)
    (hs : i ≤ s) (A : Finset V) :
    universalHomologicalRank (twistedPowerRank η ρ (s + 1)) i A =
      ρ A + universalHomologicalRank (twistedPowerRank η ρ s) i A := by
  by_cases hA : A = ∅
  · simp [hA]
  have hA' := Finset.nonempty_iff_ne_empty.mpr hA
  rw [twistedPower_universalHomologicalRank η ρ (s + 1) i hA',
    twistedPower_universalHomologicalRank η ρ s i hA']
  have hcap := cappedAffineMinimum_stable i
    (fun P : Finpartition A => partitionDefect ρ P)
    (fun P => partitionDefect η P + partitionSlack P) hs
  simp only [cappedAffineMinimum, ← Nat.add_assoc] at hcap
  rw [hcap]
  simp only [twistedPowerRank_apply, Nat.add_mul, Nat.one_mul]
  omega

theorem twistedPower_universalRank_succ (η ρ : RankFunction V) (i s : ℕ)
    (hs : i ≤ s) :
    universalHomologicalRank (twistedPowerRank η ρ (s + 1)) i =
      ρ.add (universalHomologicalRank (twistedPowerRank η ρ s) i) := by
  apply RankFunction.ext_fun
  exact twistedPower_universalHomologicalRank_succ η ρ i s hs

theorem twistedPower_universalTotal_rank_eq_iff (η ρ : RankFunction V) (i s : ℕ)
    (hs : i ≤ s) :
    universalHomologicalRank (twistedPowerRank η ρ (s + 1)) i univ =
        twistedPowerRank η ρ (s + 1) univ + i ↔
      universalHomologicalRank (twistedPowerRank η ρ s) i univ =
        twistedPowerRank η ρ s univ + i := by
  rw [twistedPower_universalHomologicalRank_succ η ρ i s hs univ]
  simp only [twistedPowerRank_apply, Nat.add_mul, Nat.one_mul]
  omega

section Ideals

variable (k : Type*) [CommSemiring k]

/-- The complete ideal identity underlying Theorem 1.1, including arbitrary
fixed twists and all zero shift layers. -/
theorem twistedPower_rankShiftIdeal_succ (η ρ : RankFunction V) (i s : ℕ)
    (hs : i ≤ s) :
    rankShiftIdeal k (twistedPowerRank η ρ (s + 1)) i =
      rankIdeal k ρ * rankShiftIdeal k (twistedPowerRank η ρ s) i := by
  by_cases h0 : universalHomologicalRank (twistedPowerRank η ρ s) i univ =
      twistedPowerRank η ρ s univ + i
  · have h1 := (twistedPower_universalTotal_rank_eq_iff η ρ i s hs).mpr h0
    rw [rankShiftIdeal, if_pos h1, rankShiftIdeal, if_pos h0,
      twistedPower_universalRank_succ η ρ i s hs, rankIdeal_add]
  · have h1 : ¬ universalHomologicalRank (twistedPowerRank η ρ (s + 1)) i univ =
        twistedPowerRank η ρ (s + 1) univ + i :=
      fun h => h0 ((twistedPower_universalTotal_rank_eq_iff η ρ i s hs).mp h)
    simp [rankShiftIdeal, h1, h0]

theorem rankIdeal_twistedPower (η ρ : RankFunction V) (s : ℕ) :
    rankIdeal k (twistedPowerRank η ρ s) = rankIdeal k η * rankIdeal k ρ ^ s := by
  rw [twistedPowerRank, rankIdeal_add, rankIdeal_scale]

theorem power_rankShiftIdeal_succ (ρ : RankFunction V) (i s : ℕ) (hs : i ≤ s) :
    rankShiftIdeal k (ρ.scale (s + 1)) i =
      rankIdeal k ρ * rankShiftIdeal k (ρ.scale s) i := by
  have he (n : ℕ) : twistedPowerRank zeroRank ρ n = ρ.scale n := by
    apply RankFunction.ext_fun
    intro A
    simp [twistedPowerRank_apply, RankFunction.scale]
  simpa only [he] using twistedPower_rankShiftIdeal_succ k zeroRank ρ i s hs

end Ideals

section SeveralColors

variable {J : Type*} [Fintype J] [DecidableEq J]

theorem multiRank_erase_decompose (ρ : J → RankFunction V) (s : J →₀ ℕ) (j : J) :
    multiRank ρ s = (multiRank ρ (s.erase j)).add ((ρ j).scale (s j)) := by
  have he : s.erase j + Finsupp.single j (s j) = s := by
    ext x
    by_cases hx : x = j
    · subst x; simp
    · simp [Finsupp.erase_apply, hx, Ne.symm hx]
  conv_lhs => rw [← he]
  rw [multiRank_add, multiRank_single]

theorem twistedMultiRank_erase_decompose (η : RankFunction V)
    (ρ : J → RankFunction V) (s : J →₀ ℕ) (j : J) :
    η.add (multiRank ρ s) =
      twistedPowerRank (η.add (multiRank ρ (s.erase j))) (ρ j) (s j) := by
  rw [multiRank_erase_decompose ρ s j]
  apply RankFunction.ext_fun
  intro A
  change η A + (multiRank ρ (s.erase j) A + s j * ρ j A) =
    (η A + multiRank ρ (s.erase j) A) + s j * ρ j A
  omega

theorem twistedMultiRank_succ_decompose (η : RankFunction V)
    (ρ : J → RankFunction V) (s : J →₀ ℕ) (j : J) :
    η.add (multiRank ρ (s + Finsupp.single j 1)) =
      twistedPowerRank (η.add (multiRank ρ (s.erase j))) (ρ j) (s j + 1) := by
  rw [twistedMultiRank_erase_decompose η ρ (s + Finsupp.single j 1) j]
  have he : (s + Finsupp.single j 1).erase j = s.erase j := by
    ext x
    by_cases hx : x = j
    · subst x; simp
    · simp [Finsupp.erase_apply, hx, Ne.symm hx]
  simp only [he, Finsupp.add_apply, Finsupp.single_eq_same]

/-- Corollary 4.1 at the rank-ideal level: each coordinate stabilizes in the
same complete range, with all other colors absorbed into an arbitrary twist. -/
theorem multi_rankShiftIdeal_succ (k : Type*) [CommSemiring k]
    (η : RankFunction V) (ρ : J → RankFunction V) (s : J →₀ ℕ)
    (i : ℕ) (j : J) (hs : i ≤ s j) :
    rankShiftIdeal k (η.add (multiRank ρ (s + Finsupp.single j 1))) i =
      rankIdeal k (ρ j) * rankShiftIdeal k (η.add (multiRank ρ s)) i := by
  rw [twistedMultiRank_succ_decompose, twistedMultiRank_erase_decompose η ρ s j]
  exact twistedPower_rankShiftIdeal_succ k _ _ i (s j) hs

end SeveralColors

end CommAlg.Polymatroid

end
end CheckedSource74

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "75: CommAlg.IntegralClosure.Weight\n"

/-! ## Source: CommAlg.IntegralClosure.Weight -/
section CheckedSource75

/-! # Linear-weight bounds and initial forms in polynomial domains -/

noncomputable section

namespace CommAlg.Weight

open Classical Finset
open scoped Pointwise

variable {V k : Type*} [DecidableEq V] [CommRing k]

def Bound (w : V → ℤ) (c : ℤ) (p : MvPolynomial V k) : Prop :=
  ∀ a, p.coeff a ≠ 0 → c ≤ Finsupp.weight w a

theorem bound_zero (w : V → ℤ) (c : ℤ) : Bound w c (0 : MvPolynomial V k) := by
  intro a ha
  simp at ha

theorem Bound.mono {w : V → ℤ} {c d : ℤ} {p : MvPolynomial V k}
    (hp : Bound w c p) (hd : d ≤ c) : Bound w d p := fun a ha => hd.trans (hp a ha)

theorem Bound.add {w : V → ℤ} {c : ℤ} {p q : MvPolynomial V k}
    (hp : Bound w c p) (hq : Bound w c q) : Bound w c (p + q) := by
  intro a ha
  by_cases hpa : p.coeff a = 0
  · apply hq a
    simpa only [MvPolynomial.coeff_add, hpa, zero_add] using ha
  · exact hp a hpa

theorem Bound.neg {w : V → ℤ} {c : ℤ} {p : MvPolynomial V k}
    (hp : Bound w c p) : Bound w c (-p) := by
  intro a ha
  exact hp a (by simpa using ha)

theorem Bound.mul {w : V → ℤ} {c d : ℤ} {p q : MvPolynomial V k}
    (hp : Bound w c p) (hq : Bound w d q) : Bound w (c + d) (p * q) := by
  intro a ha
  have hm := MvPolynomial.support_mul p q (MvPolynomial.mem_support_iff.mpr ha)
  obtain ⟨b, hb, e, he, rfl⟩ := Finset.mem_add.mp hm
  rw [map_add]
  exact add_le_add (hp b (MvPolynomial.mem_support_iff.mp hb))
    (hq e (MvPolynomial.mem_support_iff.mp he))

theorem bound_one (w : V → ℤ) : Bound w 0 (1 : MvPolynomial V k) := by
  intro a ha
  by_cases h : a = 0
  · subst a; simp
  · simp [MvPolynomial.coeff_one, h, Ne.symm h] at ha

theorem Bound.pow {w : V → ℤ} {c : ℤ} {p : MvPolynomial V k}
    (hp : Bound w c p) (n : ℕ) : Bound w ((n : ℤ) * c) (p ^ n) := by
  induction n with
  | zero => simpa using bound_one w
  | succ n ih =>
    simpa only [pow_succ, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using ih.mul hp

theorem bound_sum {ι : Type*} (w : V → ℤ) (c : ℤ) (s : Finset ι)
    (f : ι → MvPolynomial V k) (hf : ∀ i ∈ s, Bound w c (f i)) :
    Bound w c (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using bound_zero w c
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem exists_minimum (w : V → ℤ) {p : MvPolynomial V k} (hp : p ≠ 0) :
    ∃ m : ℤ, Bound w m p ∧ ∃ a, p.coeff a ≠ 0 ∧ Finsupp.weight w a = m := by
  have hS := MvPolynomial.support_nonempty.mpr hp
  let m := p.support.inf' hS (Finsupp.weight w)
  obtain ⟨a, ha, he⟩ := Finset.exists_mem_eq_inf' hS (Finsupp.weight w)
  refine ⟨m, ?_, a, MvPolynomial.mem_support_iff.mp ha, he.symm⟩
  intro b hb
  exact Finset.inf'_le _ (MvPolynomial.mem_support_iff.mpr hb)

abbrev initial (w : V → ℤ) (m : ℤ) (p : MvPolynomial V k) : MvPolynomial V k :=
  MvPolynomial.weightedHomogeneousComponent w m p

theorem initial_ne_zero {w : V → ℤ} {m : ℤ} {p : MvPolynomial V k}
    (h : ∃ a, p.coeff a ≠ 0 ∧ Finsupp.weight w a = m) : initial w m p ≠ 0 := by
  obtain ⟨a, ha, haw⟩ := h
  intro he
  have hc := congrArg (fun q : MvPolynomial V k => q.coeff a) he
  apply ha
  simpa only [initial, MvPolynomial.coeff_weightedHomogeneousComponent, haw,
    ↓reduceIte, MvPolynomial.coeff_zero, Finsupp.zero_apply] using hc

/-- The lowest nonzero weighted homogeneous components multiply exactly. -/
theorem initial_mul {w : V → ℤ} {m n : ℤ} {p q : MvPolynomial V k}
    (hp : Bound w m p) (hq : Bound w n q) :
    initial w (m + n) (p * q) = initial w m p * initial w n q := by
  ext a
  rw [MvPolynomial.coeff_weightedHomogeneousComponent, MvPolynomial.coeff_mul,
    MvPolynomial.coeff_mul]
  by_cases haw : Finsupp.weight w a = m + n
  · rw [if_pos haw]
    apply Finset.sum_congr rfl
    rintro ⟨b, c⟩ hbc
    have hsum : b + c = a := Finset.mem_antidiagonal.mp hbc
    by_cases hb : p.coeff b = 0
    · simp [MvPolynomial.coeff_weightedHomogeneousComponent, hb]
    by_cases hc : q.coeff c = 0
    · simp [MvPolynomial.coeff_weightedHomogeneousComponent, hc]
    have hbw := hp b hb
    have hcw := hq c hc
    have hsumw : Finsupp.weight w b + Finsupp.weight w c = m + n := by
      rw [← map_add, hsum, haw]
    have hbm : Finsupp.weight w b = m := by omega
    have hcn : Finsupp.weight w c = n := by omega
    simp [MvPolynomial.coeff_weightedHomogeneousComponent, hbm, hcn]
  · rw [if_neg haw]
    symm
    apply Finset.sum_eq_zero
    rintro ⟨b, c⟩ hbc
    have hsum : b + c = a := Finset.mem_antidiagonal.mp hbc
    by_cases hbm : Finsupp.weight w b = m
    · have hcn : Finsupp.weight w c ≠ n := by
        intro hcn
        apply haw
        rw [← hsum, map_add, hbm, hcn]
      simp [MvPolynomial.coeff_weightedHomogeneousComponent, hcn]
    · simp [MvPolynomial.coeff_weightedHomogeneousComponent, hbm]

theorem minimum_mul [IsDomain k] {w : V → ℤ} {m n : ℤ} {p q : MvPolynomial V k}
    (hp : Bound w m p) (hq : Bound w n q)
    (hpm : ∃ a, p.coeff a ≠ 0 ∧ Finsupp.weight w a = m)
    (hqn : ∃ a, q.coeff a ≠ 0 ∧ Finsupp.weight w a = n) :
    ∃ a, (p * q).coeff a ≠ 0 ∧ Finsupp.weight w a = m + n := by
  have hn : initial w (m + n) (p * q) ≠ 0 := by
    rw [initial_mul hp hq]
    exact mul_ne_zero (initial_ne_zero hpm) (initial_ne_zero hqn)
  obtain ⟨a, ha⟩ := MvPolynomial.support_nonempty.mpr hn
  have hc := MvPolynomial.mem_support_iff.mp ha
  rw [MvPolynomial.coeff_weightedHomogeneousComponent] at hc
  split_ifs at hc with haw
  · exact ⟨a, hc, haw⟩
  · exact (hc rfl).elim

theorem minimum_pow [IsDomain k] {w : V → ℤ} {m : ℤ} {p : MvPolynomial V k}
    (hp : Bound w m p) (hpm : ∃ a, p.coeff a ≠ 0 ∧ Finsupp.weight w a = m) (n : ℕ) :
    ∃ a, (p ^ n).coeff a ≠ 0 ∧ Finsupp.weight w a = (n : ℤ) * m := by
  induction n with
  | zero => exact ⟨0, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨a, ha, haw⟩ := minimum_mul (hp.pow n) hp ih hpm
    exact ⟨a, by simpa only [pow_succ] using ha, by
      simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using haw⟩

end CommAlg.Weight

end
end CheckedSource75

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "76: CommAlg.IntegralClosure.Ideal\n"

/-! ## Source: CommAlg.IntegralClosure.Ideal -/
section CheckedSource76

/-! # Integral closure of ideals cut out by integer linear weights

Mathlib's ring-integrality theory does not yet define integrality over an
ideal.  The definition here is the usual monic equation
`x^n + ∑_{i<n} c_i*x^i = 0`, with `c_i ∈ I^(n-i)`.
-/

noncomputable section

namespace CommAlg

open Classical Finset

variable {R : Type*} [CommRing R]

/-- The standard monic-equation definition of integrality over an ideal. -/
def IntegralOverIdeal (I : Ideal R) (x : R) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∃ c : ℕ → R,
    (∀ i < n, c i ∈ I ^ (n - i)) ∧ x ^ n + ∑ i ∈ Finset.range n, c i * x ^ i = 0

def IsIntegrallyClosedIdeal (I : Ideal R) : Prop :=
  ∀ x : R, IntegralOverIdeal I x → x ∈ I

theorem integralOverIdeal_of_mem {I : Ideal R} {x : R} (hx : x ∈ I) :
    IntegralOverIdeal I x := by
  refine ⟨1, by omega, fun _ => -x, ?_, ?_⟩
  · intro i hi
    have he : i = 0 := by omega
    simpa [he] using I.neg_mem hx
  · simp

namespace Weight

variable {V k : Type*} [DecidableEq V] [CommRing k]

def cutIdeal (f : R →+* MvPolynomial V k) (w : V → ℤ)
    (h0 : ∀ x, Bound w 0 (f x)) (c : ℤ) : Ideal R where
  carrier := {x | Bound w c (f x)}
  zero_mem' := by simpa using bound_zero w c
  add_mem' hx hy := by simpa using hx.add hy
  smul_mem' r x hx := by
    change Bound w c (f (r * x))
    simpa only [smul_eq_mul, map_mul, zero_add] using (h0 r).mul hx

@[simp] theorem mem_cutIdeal (f : R →+* MvPolynomial V k) (w : V → ℤ)
    (h0 : ∀ x, Bound w 0 (f x)) (c : ℤ) (x : R) :
    x ∈ cutIdeal f w h0 c ↔ Bound w c (f x) := Iff.rfl

theorem bound_of_mem_pow (f : R →+* MvPolynomial V k) (w : V → ℤ)
    (h0 : ∀ x, Bound w 0 (f x)) (I : Ideal R) (c : ℤ)
    (hI : ∀ x ∈ I, Bound w c (f x)) (n : ℕ) {x : R} (hx : x ∈ I ^ n) :
    Bound w ((n : ℤ) * c) (f x) := by
  induction n generalizing x with
  | zero => simpa using h0 x
  | succ n ih =>
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on (C := fun y => Bound w ((↑(n + 1) : ℤ) * c) (f y)) hx ?_ ?_
    · intro a ha b hb
      have h := (ih ha).mul (hI b hb)
      simpa only [map_mul, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using h
    · intro a b ha hb
      simpa only [map_add] using ha.add hb

theorem bound_of_integral [IsDomain k] (f : R →+* MvPolynomial V k) (w : V → ℤ)
    (h0 : ∀ x, Bound w 0 (f x)) (I : Ideal R) (c : ℤ)
    (hI : ∀ x ∈ I, Bound w c (f x)) {x : R} (hx : IntegralOverIdeal I x) :
    Bound w c (f x) := by
  by_contra hn
  simp only [Bound, not_forall, not_le] at hn
  obtain ⟨a₀, ha₀, hbad⟩ := hn
  have hfx : f x ≠ 0 := by intro he; simp [he] at ha₀
  obtain ⟨m, hm, hmin⟩ := exists_minimum w hfx
  have hmc : m < c := (hm a₀ ha₀).trans_lt hbad
  obtain ⟨n, hn, b, hb, heq⟩ := hx
  obtain ⟨a, hap, haw⟩ := minimum_pow hm hmin n
  have hsum : Bound w ((n : ℤ) * m + 1)
      (∑ i ∈ Finset.range n, f (b i) * (f x) ^ i) := by
    apply bound_sum
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    have hbnd := (bound_of_mem_pow f w h0 I c hI (n - i) (hb i hin)).mul (hm.pow i)
    apply hbnd.mono
    have hni : ((n - i : ℕ) : ℤ) + i = n := by
      exact_mod_cast Nat.sub_add_cancel (Nat.le_of_lt hin)
    have hpos : (0 : ℤ) < ((n - i : ℕ) : ℤ) := by
      exact_mod_cast Nat.sub_pos_of_lt hin
    have hprod : (0 : ℤ) < ((n - i : ℕ) : ℤ) * (c - m) := mul_pos hpos (by omega)
    have hprod1 : (1 : ℤ) ≤ ((n - i : ℕ) : ℤ) * (c - m) := by omega
    rw [← hni]
    nlinarith
  have hsumcoeff : (∑ i ∈ Finset.range n, f (b i) * (f x) ^ i).coeff a = 0 := by
    by_contra hne
    have h := hsum a hne
    rw [haw] at h
    omega
  have heq' : (f x) ^ n + ∑ i ∈ Finset.range n, f (b i) * (f x) ^ i = 0 := by
    simpa only [map_add, map_pow, map_sum, map_mul, map_zero] using congrArg f heq
  have hc := congrArg (fun p : MvPolynomial V k => p.coeff a) heq'
  apply hap
  simpa only [MvPolynomial.coeff_add, hsumcoeff, add_zero,
    MvPolynomial.coeff_zero, Finsupp.zero_apply] using hc

theorem cutIdeal_integrallyClosed [IsDomain k] (f : R →+* MvPolynomial V k) (w : V → ℤ)
    (h0 : ∀ x, Bound w 0 (f x)) (c : ℤ) : IsIntegrallyClosedIdeal (cutIdeal f w h0 c) := by
  intro x hx
  exact bound_of_integral f w h0 _ c (fun _ h => h) hx

/-- An arbitrary intersection of linear-weight cuts is integrally closed.
The coefficient ring may be any domain, in particular any field. -/
theorem integrallyClosed_of_weight_bounds [IsDomain k] {J : Type*}
    (f : R →+* MvPolynomial V k) (w : J → V → ℤ) (c : J → ℤ)
    (h0 : ∀ j x, Bound (w j) 0 (f x)) (I : Ideal R)
    (hmem : ∀ x, x ∈ I ↔ ∀ j, Bound (w j) (c j) (f x)) : IsIntegrallyClosedIdeal I := by
  intro x hx
  apply (hmem x).mpr
  intro j
  exact bound_of_integral f (w j) (h0 j) I (c j) (fun y hy => (hmem y).mp hy j) hx

end Weight

end CommAlg

end
end CheckedSource76

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "77: CommAlg.IntegralClosure.SemigroupAlgebra\n"

/-! ## Source: CommAlg.IntegralClosure.SemigroupAlgebra -/
section CheckedSource77

/-! # Actual polynomial subalgebras supported on additive exponent semigroups -/

noncomputable section

namespace CommAlg

open Classical Finset
open scoped Pointwise

variable {V k : Type*} [DecidableEq V] [CommRing k]

def supportedSubalgebra (k : Type*) [CommRing k] (S : AddSubmonoid (V →₀ ℕ)) :
    Subalgebra k (MvPolynomial V k) where
  carrier := {p | ∀ a ∈ p.support, a ∈ S}
  zero_mem' := by simp
  one_mem' := by
    intro a ha
    have hm : a ∈ (MvPolynomial.monomial (0 : V →₀ ℕ) (1 : k)).support := by simpa using ha
    have he := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm)
    simpa only [he] using S.zero_mem
  add_mem' hp hq := by
    intro a ha
    rcases Finset.mem_union.mp (MvPolynomial.support_add ha) with ha | ha
    · exact hp a ha
    · exact hq a ha
  mul_mem' hp hq := by
    intro a ha
    obtain ⟨b, hb, c, hc, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ ha)
    exact S.add_mem (hp b hb) (hq c hc)
  algebraMap_mem' r := by
    intro a ha
    have hm : a ∈ (MvPolynomial.monomial (0 : V →₀ ℕ) r).support := ha
    have he := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm)
    simpa only [he] using S.zero_mem

@[simp] theorem mem_supportedSubalgebra (S : AddSubmonoid (V →₀ ℕ)) (p : MvPolynomial V k) :
    p ∈ supportedSubalgebra k S ↔ ∀ a ∈ p.support, a ∈ S := Iff.rfl

theorem monomial_mem_supportedSubalgebra (S : AddSubmonoid (V →₀ ℕ))
    {a : V →₀ ℕ} (ha : a ∈ S) (r : k) :
    MvPolynomial.monomial a r ∈ supportedSubalgebra k S := by
  intro b hb
  simpa only [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hb)] using ha

@[simp] theorem monomial_one_mem_supportedSubalgebra_iff [Nontrivial k]
    (S : AddSubmonoid (V →₀ ℕ)) (a : V →₀ ℕ) :
    MvPolynomial.monomial a (1 : k) ∈ supportedSubalgebra k S ↔ a ∈ S := by
  constructor
  · intro h
    exact h a (by simp [MvPolynomial.support_monomial])
  · exact fun h => monomial_mem_supportedSubalgebra S h 1

theorem supportedSubalgebra_eq_adjoin (S : AddSubmonoid (V →₀ ℕ)) :
    supportedSubalgebra k S = Algebra.adjoin k
      ((fun a => MvPolynomial.monomial a (1 : k)) '' (S : Set (V →₀ ℕ))) := by
  apply le_antisymm
  · intro p hp
    rw [p.as_sum]
    apply Subalgebra.sum_mem
    intro a ha
    have hm : MvPolynomial.monomial a (1 : k) ∈ Algebra.adjoin k
        ((fun a => MvPolynomial.monomial a (1 : k)) '' (S : Set (V →₀ ℕ))) := by
      apply Algebra.subset_adjoin
      exact ⟨a, hp a ha, rfl⟩
    have hc := (Algebra.adjoin k
      ((fun a => MvPolynomial.monomial a (1 : k)) '' (S : Set (V →₀ ℕ)))).algebraMap_mem (p.coeff a)
    have hmul := Subalgebra.mul_mem _ hc hm
    simpa [MvPolynomial.C_mul_monomial] using hmul
  · apply Algebra.adjoin_le
    rintro _ ⟨a, ha, rfl⟩
    exact monomial_mem_supportedSubalgebra S ha 1

/-- The support model agrees with the usual subalgebra generated by monomials. -/
theorem supported_closure_eq_adjoin (G : Set (V →₀ ℕ)) :
    supportedSubalgebra k (AddSubmonoid.closure G) =
      Algebra.adjoin k ((fun a => MvPolynomial.monomial a (1 : k)) '' G) := by
  rw [supportedSubalgebra_eq_adjoin]
  apply le_antisymm
  · apply Algebra.adjoin_le
    rintro _ ⟨a, ha, rfl⟩
    induction ha using AddSubmonoid.closure_induction with
    | mem a ha => exact Algebra.subset_adjoin ⟨a, ha, rfl⟩
    | zero => simpa using (Algebra.adjoin k
        ((fun a => MvPolynomial.monomial a (1 : k)) '' G)).one_mem
    | add a b ha hb iha ihb =>
      have hmul := Subalgebra.mul_mem _ iha ihb
      simpa using hmul
  · apply Algebra.adjoin_mono
    exact Set.image_mono AddSubmonoid.subset_closure

theorem nonnegative_weight_closure (G : Set (V →₀ ℕ)) (w : V → ℤ)
    (hG : ∀ a ∈ G, 0 ≤ Finsupp.weight w a) :
    ∀ a ∈ AddSubmonoid.closure G, 0 ≤ Finsupp.weight w a := by
  intro a ha
  induction ha using AddSubmonoid.closure_induction with
  | mem a ha => exact hG a ha
  | zero => simp
  | add a b ha hb iha ihb => simpa using add_nonneg iha ihb

theorem supported_weight_nonnegative (S : AddSubmonoid (V →₀ ℕ)) (w : V → ℤ)
    (hS : ∀ a ∈ S, 0 ≤ Finsupp.weight w a) (p : supportedSubalgebra k S) :
    Weight.Bound w 0 p.val := by
  intro a ha
  exact hS a (p.property a (MvPolynomial.mem_support_iff.mpr ha))

theorem supported_ideal_integrallyClosed [IsDomain k] {J : Type*}
    (S : AddSubmonoid (V →₀ ℕ)) (w : J → V → ℤ) (c : J → ℤ)
    (hS : ∀ j a, a ∈ S → 0 ≤ Finsupp.weight (w j) a)
    (I : Ideal (supportedSubalgebra k S))
    (hmem : ∀ p, p ∈ I ↔ ∀ j, Weight.Bound (w j) (c j) p.val) :
    IsIntegrallyClosedIdeal I :=
  Weight.integrallyClosed_of_weight_bounds (supportedSubalgebra k S).val.toRingHom w c
    (fun j p => supported_weight_nonnegative S (w j) (hS j) p) I hmem

end CommAlg

end
end CheckedSource77

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "78: CommAlg.IntegralClosure.MultiRees\n"

/-! ## Source: CommAlg.IntegralClosure.MultiRees -/
section CheckedSource78

/-! # The actual multi-Rees subalgebra and its homogeneous ideals

The definition is the ordinary subalgebra of a polynomial ring whose
multidegree-s coefficient lies in the product of ideal powers.
-/

noncomputable section

namespace CommAlg

open Classical Finset

variable {J R : Type*} [Fintype J] [DecidableEq J] [CommRing R]

def powerProduct (I : J → Ideal R) (s : J →₀ ℕ) : Ideal R := ∏ j, (I j) ^ (s j)

@[simp] theorem powerProduct_zero (I : J → Ideal R) : powerProduct I 0 = ⊤ := by
  simp [powerProduct]

theorem powerProduct_add (I : J → Ideal R) (s t : J →₀ ℕ) :
    powerProduct I (s + t) = powerProduct I s * powerProduct I t := by
  simp only [powerProduct, Finsupp.add_apply, pow_add, Finset.prod_mul_distrib]

def multiReesAlgebra (I : J → Ideal R) : Subalgebra R (MvPolynomial J R) where
  carrier := {p | ∀ s, p.coeff s ∈ powerProduct I s}
  zero_mem' := by simp
  one_mem' := by
    intro s
    by_cases hs : s = 0
    · subst s; simp
    · simp [MvPolynomial.coeff_one, hs, Ne.symm hs]
  add_mem' hp hq := fun s => by
    simpa only [MvPolynomial.coeff_add] using Ideal.add_mem _ (hp s) (hq s)
  mul_mem' hp hq := by
    intro s
    rw [MvPolynomial.coeff_mul]
    apply Ideal.sum_mem
    intro uv huv
    have he : uv.1 + uv.2 = s := Finset.mem_antidiagonal.mp huv
    have h := Ideal.mul_mem_mul (hp uv.1) (hq uv.2)
    rwa [← powerProduct_add, he] at h
  algebraMap_mem' r := by
    intro s
    change (MvPolynomial.C r).coeff s ∈ powerProduct I s
    by_cases hs : s = 0
    · subst s; simp
    · simp [MvPolynomial.coeff_C, hs, Ne.symm hs]

@[simp] theorem mem_multiReesAlgebra (I : J → Ideal R) (p : MvPolynomial J R) :
    p ∈ multiReesAlgebra I ↔ ∀ s, p.coeff s ∈ powerProduct I s := Iff.rfl

@[simp] theorem monomial_mem_multiReesAlgebra (I : J → Ideal R) (s : J →₀ ℕ) (r : R) :
    MvPolynomial.monomial s r ∈ multiReesAlgebra I ↔ r ∈ powerProduct I s := by
  constructor
  · intro h
    simpa using h s
  · intro h t
    by_cases ht : t = s
    · subst t; simpa using h
    · simp [MvPolynomial.coeff_monomial, ht, Ne.symm ht]

def multiReesIdeal (I : J → Ideal R) (K : (J →₀ ℕ) → Ideal R)
    (hact : ∀ s t, powerProduct I s * K t ≤ K (s + t)) : Ideal (multiReesAlgebra I) where
  carrier := {p | ∀ s, p.val.coeff s ∈ K s}
  zero_mem' := by simp
  add_mem' hp hq := fun s => by
    simpa only [Subalgebra.coe_add, MvPolynomial.coeff_add] using (K s).add_mem (hp s) (hq s)
  smul_mem' r p hp := by
    intro s
    change (r.val * p.val).coeff s ∈ K s
    rw [MvPolynomial.coeff_mul]
    apply Ideal.sum_mem
    intro uv huv
    have he : uv.1 + uv.2 = s := Finset.mem_antidiagonal.mp huv
    rw [← he]
    exact hact uv.1 uv.2 (Ideal.mul_mem_mul (r.property uv.1) (hp uv.2))

@[simp] theorem mem_multiReesIdeal (I : J → Ideal R) (K : (J →₀ ℕ) → Ideal R)
    (hact : ∀ s t, powerProduct I s * K t ≤ K (s + t)) (p : multiReesAlgebra I) :
    p ∈ multiReesIdeal I K hact ↔ ∀ s, p.val.coeff s ∈ K s := Iff.rfl

section Polynomial

variable {V k : Type*} [Fintype V] [DecidableEq V] [CommRing k]

def reesDegree (e : J ⊕ V →₀ ℕ) : J →₀ ℕ :=
  (Finsupp.sumFinsuppAddEquivProdFinsupp e).1

def ordinaryDegree (e : J ⊕ V →₀ ℕ) : V →₀ ℕ :=
  (Finsupp.sumFinsuppAddEquivProdFinsupp e).2

@[simp] theorem reesDegree_apply (e : J ⊕ V →₀ ℕ) (j : J) : reesDegree e j = e (.inl j) := rfl

@[simp] theorem ordinaryDegree_apply (e : J ⊕ V →₀ ℕ) (v : V) : ordinaryDegree e v = e (.inr v) := rfl

theorem coeff_sumAlgEquiv (p : MvPolynomial (J ⊕ V) k) (s : J →₀ ℕ) (a : V →₀ ℕ) :
    (((MvPolynomial.sumAlgEquiv k J V) p).coeff s).coeff a =
      p.coeff (Finsupp.sumFinsuppAddEquivProdFinsupp.symm (s, a)) := by
  change ((AddMonoidAlgebra.domCongr k k Finsupp.sumFinsuppAddEquivProdFinsupp p).coeff (s,a)) = _
  exact AddMonoidAlgebra.coeff_domCongr _ _ _

theorem coeff_flatten (p : MvPolynomial J (MvPolynomial V k)) (s : J →₀ ℕ) (a : V →₀ ℕ) :
    ((MvPolynomial.sumAlgEquiv k J V).symm p).coeff
      (Finsupp.sumFinsuppAddEquivProdFinsupp.symm (s, a)) = (p.coeff s).coeff a := by
  have h := coeff_sumAlgEquiv ((MvPolynomial.sumAlgEquiv k J V).symm p) s a
  simpa only [AlgEquiv.apply_symm_apply] using h.symm

theorem coeff_flatten_at (p : MvPolynomial J (MvPolynomial V k)) (e : J ⊕ V →₀ ℕ) :
    ((MvPolynomial.sumAlgEquiv k J V).symm p).coeff e =
      (p.coeff (reesDegree e)).coeff (ordinaryDegree e) := by
  have h := coeff_flatten p (reesDegree e) (ordinaryDegree e)
  simpa only [reesDegree, ordinaryDegree, Prod.mk.eta, AddEquiv.symm_apply_apply] using h

def multiReesFlatten (I : J → Ideal (MvPolynomial V k)) :
    multiReesAlgebra I →+* MvPolynomial (J ⊕ V) k :=
  (MvPolynomial.sumAlgEquiv k J V).symm.toRingHom.comp (multiReesAlgebra I).val.toRingHom

theorem multiReesFlatten_injective (I : J → Ideal (MvPolynomial V k)) :
    Function.Injective (multiReesFlatten I) :=
  (MvPolynomial.sumAlgEquiv k J V).symm.injective.comp Subtype.val_injective

theorem multiReesFlatten_coeff (I : J → Ideal (MvPolynomial V k))
    (p : multiReesAlgebra I) (e : J ⊕ V →₀ ℕ) :
    (multiReesFlatten I p).coeff e = (p.val.coeff (reesDegree e)).coeff (ordinaryDegree e) :=
  coeff_flatten_at p.val e

theorem mem_polymatroid_multiRees (ρ : J → Polymatroid.RankFunction V)
    (p : MvPolynomial J (MvPolynomial V k)) :
    p ∈ multiReesAlgebra (fun j => Polymatroid.rankIdeal k (ρ j)) ↔
      ∀ e, ((MvPolynomial.sumAlgEquiv k J V).symm p).coeff e ≠ 0 →
        Polymatroid.LowerFeasible (Polymatroid.multiRank ρ (reesDegree e)).lower (ordinaryDegree e) := by
  simp only [mem_multiReesAlgebra, powerProduct, ← Polymatroid.rankIdeal_multiRank]
  constructor
  · intro hp e he
    have hm := (Polymatroid.mem_monomialIdeal_iff _ _).mp (hp (reesDegree e))
    exact (Polymatroid.contains_rankBases_iff _ _).mp
      (hm _ (MvPolynomial.mem_support_iff.mpr (by rwa [coeff_flatten_at] at he)))
  · intro hp s
    apply (Polymatroid.mem_monomialIdeal_iff _ _).mpr
    intro a ha
    let e := Finsupp.sumFinsuppAddEquivProdFinsupp.symm (s, a)
    have he : ((MvPolynomial.sumAlgEquiv k J V).symm p).coeff e ≠ 0 := by
      rw [coeff_flatten]
      exact MvPolynomial.mem_support_iff.mp ha
    have h := hp e he
    have hs : reesDegree e = s := by simp [e, reesDegree]
    have ha' : ordinaryDegree e = a := by simp [e, ordinaryDegree]
    rw [hs, ha'] at h
    exact (Polymatroid.contains_rankBases_iff _ _).mpr h

end Polynomial

end CommAlg

end
end CheckedSource78

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "79: CommAlg.Rees.BoxGeneration\n"

/-! ## Source: CommAlg.Rees.BoxGeneration -/
section CheckedSource79

/-! # Generating an actual multigraded Rees ideal in a finite box

The conclusion is equality with an ideal span inside the actual multi-Rees
algebra. It follows from coordinatewise stabilization by induction on the
sum of the Rees exponents and the polynomial's homogeneous decomposition.
-/

noncomputable section

namespace CommAlg

open Classical Finset

variable {J R : Type*} [Fintype J] [DecidableEq J] [CommRing R]

@[simp] theorem powerProduct_single (I : J → Ideal R) (j : J) (n : ℕ) :
    powerProduct I (Finsupp.single j n) = (I j) ^ n := by
  unfold powerProduct
  rw [Finset.prod_eq_single j]
  · simp
  · intro x hx hxj
    simp [Finsupp.single_apply, hxj, Ne.symm hxj]
  · simp

/-- The coefficient ideal of homogeneous monomials that already belong to an
ideal of the actual Rees algebra. -/
def homogeneousCoefficientIdeal (I : J → Ideal R) (L : Ideal (multiReesAlgebra I))
    (s : J →₀ ℕ) : Ideal R where
  carrier := {r | ∃ p ∈ L, p.val = MvPolynomial.monomial s r}
  zero_mem' := ⟨0, L.zero_mem, by simp⟩
  add_mem' := by
    rintro r t ⟨p, hp, he⟩ ⟨q, hq, hf⟩
    refine ⟨p + q, L.add_mem hp hq, ?_⟩
    change p.val + q.val = _
    rw [he, hf, map_add]
  smul_mem' := by
    intro a r
    rintro ⟨p, hp, he⟩
    refine ⟨(algebraMap R (multiReesAlgebra I) a) * p,
      L.mul_mem_left _ hp, ?_⟩
    change MvPolynomial.C a * p.val = MvPolynomial.monomial s (a * r)
    rw [he, MvPolynomial.C_mul_monomial]

@[simp] theorem mem_homogeneousCoefficientIdeal (I : J → Ideal R)
    (L : Ideal (multiReesAlgebra I)) (s : J →₀ ℕ) (r : R) :
    r ∈ homogeneousCoefficientIdeal I L s ↔
      ∃ p ∈ L, p.val = MvPolynomial.monomial s r := Iff.rfl

/-- Multiplication here is the actual multiplication of homogeneous
polynomials inside the Rees subalgebra. -/
theorem homogeneousCoefficientIdeal_action (I : J → Ideal R)
    (L : Ideal (multiReesAlgebra I)) (s t : J →₀ ℕ) :
    powerProduct I s * homogeneousCoefficientIdeal I L t ≤
      homogeneousCoefficientIdeal I L (s + t) := by
  apply Ideal.mul_le.mpr
  intro r hr q hq
  obtain ⟨p, hp, he⟩ := hq
  let x : multiReesAlgebra I :=
    ⟨MvPolynomial.monomial s r, (monomial_mem_multiReesAlgebra I s r).mpr hr⟩
  refine ⟨x * p, L.mul_mem_left x hp, ?_⟩
  change MvPolynomial.monomial s r * p.val = _
  rw [he, MvPolynomial.monomial_mul_monomial]

/-- All homogeneous module elements whose Rees multidegree belongs to the
closed coordinate box. Polynomial coefficients are unrestricted elements of
the corresponding actual coefficient ideal. -/
def reesBoxGenerators (I : J → Ideal R) (K : (J →₀ ℕ) → Ideal R) (i : ℕ) :
    Set (multiReesAlgebra I) :=
  {p | ∃ s r, (∀ j, s j ≤ i) ∧ r ∈ K s ∧ p.val = MvPolynomial.monomial s r}

theorem reesBoxGenerators_subset (I : J → Ideal R) (K : (J →₀ ℕ) → Ideal R)
    (hact : ∀ s t, powerProduct I s * K t ≤ K (s + t)) (i : ℕ) :
    reesBoxGenerators I K i ⊆ multiReesIdeal I K hact := by
  rintro p ⟨s, r, hs, hr, he⟩ t
  rw [he]
  by_cases ht : t = s
  · subst t; simpa using hr
  · simp [MvPolynomial.coeff_monomial, ht, Ne.symm ht]

/-- Coordinate stabilization implies equality with the span of the actual
homogeneous elements in the finite Rees-degree box. -/
theorem multiReesIdeal_span_box (I : J → Ideal R) (K : (J →₀ ℕ) → Ideal R)
    (hact : ∀ s t, powerProduct I s * K t ≤ K (s + t))
    (hsub : ∀ s, K s ≤ powerProduct I s) (i : ℕ)
    (hstep : ∀ s j, i ≤ s j → K (s + Finsupp.single j 1) = I j * K s) :
    multiReesIdeal I K hact = Ideal.span (reesBoxGenerators I K i) := by
  let L : Ideal (multiReesAlgebra I) := Ideal.span (reesBoxGenerators I K i)
  have hc : ∀ n : ℕ, ∀ s : J →₀ ℕ, s.degree = n →
      K s ≤ homogeneousCoefficientIdeal I L s := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s hs
      by_cases hbox : ∀ j, s j ≤ i
      · intro r hr
        let p : multiReesAlgebra I :=
          ⟨MvPolynomial.monomial s r, (monomial_mem_multiReesAlgebra I s r).mpr (hsub s hr)⟩
        exact ⟨p, Ideal.subset_span ⟨s, r, hbox, hr, rfl⟩, rfl⟩
      · push_neg at hbox
        obtain ⟨j, hj⟩ := hbox
        let t := s - Finsupp.single j 1
        have he : t + Finsupp.single j 1 = s := by
          apply tsub_add_cancel_of_le
          intro x
          by_cases hx : x = j
          · subst x
            simpa using (show 1 ≤ s j by omega)
          · simp [Finsupp.single_apply, hx, Ne.symm hx]
        have htj : i ≤ t j := by
          change i ≤ s j - (Finsupp.single j 1) j
          simp only [Finsupp.single_eq_same]
          omega
        have htdeg : t.degree < n := by
          have hh := congrArg Finsupp.degree he
          simp only [map_add, Finsupp.degree_single, hs] at hh
          omega
        have hit := ih t.degree htdeg t rfl
        rw [← he, hstep t j htj]
        calc
          I j * K t ≤ I j * homogeneousCoefficientIdeal I L t := Ideal.mul_mono le_rfl hit
          _ ≤ homogeneousCoefficientIdeal I L (t + Finsupp.single j 1) := by
            have hh := homogeneousCoefficientIdeal_action I L (Finsupp.single j 1) t
            simpa only [powerProduct_single, pow_one, add_comm] using hh
  apply le_antisymm
  · intro p hp
    have hh : ∀ s, ∃ q ∈ L, q.val =
        MvPolynomial.monomial s (p.val.coeff s) := fun s => hc s.degree s rfl (hp s)
    choose q hq he using hh
    have hsum : ∑ s ∈ p.val.support, q s ∈ L :=
      L.sum_mem (fun s hs => hq s)
    have heq : (∑ s ∈ p.val.support, q s) = p := by
      apply Subtype.ext
      change (multiReesAlgebra I).val (∑ s ∈ p.val.support, q s) = p.val
      rw [map_sum]
      calc
        (∑ s ∈ p.val.support, (q s).val) =
            ∑ s ∈ p.val.support, MvPolynomial.monomial s (p.val.coeff s) :=
          Finset.sum_congr rfl (fun s hs => he s)
        _ = p.val := (MvPolynomial.as_sum p.val).symm
    rwa [heq] at hsum
  · exact Ideal.span_le.mpr (reesBoxGenerators_subset I K hact i)

end CommAlg

end
end CheckedSource79

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "80: CommAlg.Polymatroid.HomologicalStabilization\n"

/-! ## Source: CommAlg.Polymatroid.HomologicalStabilization -/
section CheckedSource80

/-! # Stabilization for actual polynomial ideals

These statements use the genuine derived-Tor homological shift of the actual
ideal powers and products. The zero ideal is included explicitly, as are
arbitrary inactive variables, the unit ideal, and fixed polymatroidal twists.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]

/-- The complete twisted equality of Theorem 1.1, for actual ideals.
The degree-zero case is also valid. -/
theorem homologicalShift_twistedPowers (I J : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (hJ : IsPolymatroidalIdeal J)
    (i s : ℕ) (hs : i ≤ s) :
    homologicalShiftIdeal (J * I ^ (s + 1)) (hJ.mul (hI.pow (s + 1))) i =
      I * homologicalShiftIdeal (J * I ^ s) (hJ.mul (hI.pow s)) i := by
  rcases hI.eq_bot_or_rank with rfl | ⟨ρ, rfl⟩
  · simp
  rcases hJ.eq_bot_or_rank with rfl | ⟨η, rfl⟩
  · simp
  rw [homologicalShiftIdeal_eq_rankShiftIdeal _ _ (twistedPowerRank η ρ (s + 1))
      (rankIdeal_twistedPower k η ρ (s + 1)).symm,
    homologicalShiftIdeal_eq_rankShiftIdeal _ _ (twistedPowerRank η ρ s)
      (rankIdeal_twistedPower k η ρ s).symm]
  exact twistedPower_rankShiftIdeal_succ k η ρ i s hs

/-- Theorem 1.1: no loss of parameter range and no additional activity
hypothesis on the original ideal. -/
theorem homologicalShift_powers (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i s : ℕ) (hs : i ≤ s) :
    homologicalShiftIdeal (I ^ (s + 1)) (hI.pow (s + 1)) i =
      I * homologicalShiftIdeal (I ^ s) (hI.pow s) i := by
  simpa using homologicalShift_twistedPowers I ⊤ hI isPolymatroidalIdeal_top i s hs

section SeveralColors

variable {C : Type*} [Fintype C] [DecidableEq C]

theorem IsPolymatroidalIdeal.powerProduct (I : C → Ideal (MvPolynomial V k))
    (hI : ∀ c, IsPolymatroidalIdeal (I c)) (s : C →₀ ℕ) :
    IsPolymatroidalIdeal (CommAlg.powerProduct I s) :=
  IsPolymatroidalIdeal.prod univ (fun c => I c ^ (s c)) (fun c hc => (hI c).pow (s c))

theorem powerProduct_erase_decompose (I : C → Ideal (MvPolynomial V k))
    (s : C →₀ ℕ) (c : C) :
    CommAlg.powerProduct I s = CommAlg.powerProduct I (s.erase c) * I c ^ (s c) := by
  have he : s.erase c + Finsupp.single c (s c) = s := by
    ext x
    by_cases hx : x = c
    · subst x; simp
    · simp [Finsupp.erase_apply, hx, Ne.symm hx]
  conv_lhs => rw [← he]
  rw [CommAlg.powerProduct_add, CommAlg.powerProduct_single]

theorem twistedPowerProduct_erase_decompose (I : C → Ideal (MvPolynomial V k))
    (J : Ideal (MvPolynomial V k)) (s : C →₀ ℕ) (c : C) :
    J * CommAlg.powerProduct I s =
      (J * CommAlg.powerProduct I (s.erase c)) * I c ^ (s c) := by
  rw [powerProduct_erase_decompose I s c, mul_assoc]

theorem twistedPowerProduct_succ_decompose (I : C → Ideal (MvPolynomial V k))
    (J : Ideal (MvPolynomial V k)) (s : C →₀ ℕ) (c : C) :
    J * CommAlg.powerProduct I (s + Finsupp.single c 1) =
      (J * CommAlg.powerProduct I (s.erase c)) * I c ^ (s c + 1) := by
  rw [twistedPowerProduct_erase_decompose I J (s + Finsupp.single c 1) c]
  have he : (s + Finsupp.single c 1).erase c = s.erase c := by
    ext x
    by_cases hx : x = c
    · subst x; simp
    · simp [Finsupp.erase_apply, hx, Ne.symm hx]
  simp only [he, Finsupp.add_apply, Finsupp.single_eq_same]

/-- The full several-colors equality of Corollary 4.1 on actual ideals,
including zero factors, arbitrary fixed twists and zero exponents. -/
theorem homologicalShift_severalColors (I : C → Ideal (MvPolynomial V k))
    (J : Ideal (MvPolynomial V k)) (hI : ∀ c, IsPolymatroidalIdeal (I c))
    (hJ : IsPolymatroidalIdeal J) (s : C →₀ ℕ) (i : ℕ) (c : C) (hs : i ≤ s c) :
    homologicalShiftIdeal (J * CommAlg.powerProduct I (s + Finsupp.single c 1))
        (hJ.mul (IsPolymatroidalIdeal.powerProduct I hI _)) i =
      I c * homologicalShiftIdeal (J * CommAlg.powerProduct I s)
        (hJ.mul (IsPolymatroidalIdeal.powerProduct I hI _)) i := by
  let K := J * CommAlg.powerProduct I (s.erase c)
  have hK : IsPolymatroidalIdeal K :=
    hJ.mul (IsPolymatroidalIdeal.powerProduct I hI _)
  calc
    _ = homologicalShiftIdeal (K * I c ^ (s c + 1)) (hK.mul ((hI c).pow _)) i :=
      homologicalShiftIdeal_congr _ _ (twistedPowerProduct_succ_decompose I J s c) i
    _ = I c * homologicalShiftIdeal (K * I c ^ (s c)) (hK.mul ((hI c).pow _)) i :=
      homologicalShift_twistedPowers (I c) K (hI c) hK i (s c) hs
    _ = _ := congrArg (I c * ·)
      (homologicalShiftIdeal_congr _ _ (twistedPowerProduct_erase_decompose I J s c).symm i)

end SeveralColors

end CommAlg.Polymatroid

end
end CheckedSource80

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "81: CommAlg.IntegralClosure.ShiftWeights\n"

/-! ## Source: CommAlg.IntegralClosure.ShiftWeights -/
section CheckedSource81

/-! # The exact linear inequalities of homological-shift Rees ideals

There are two families of integer weights: the ordinary polymatroid lower
bounds, and one weight for every partition. The empty partition supplies
the total-degree inequality. No positivity assumption on ranks is used.
-/

noncomputable section

namespace CommAlg

open Classical Finset Polymatroid

variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

def ShiftCut (V : Type*) [DecidableEq V] :=
  Finset V ⊕ (Σ A : Finset V, Finpartition A)

def cutWeight (c : J → ℤ) (A : Finset V) : J ⊕ V → ℤ :=
  Sum.elim c (fun v => if v ∈ Aᶜ then 1 else 0)

theorem weight_cutWeight (c : J → ℤ) (A : Finset V) (e : J ⊕ V →₀ ℕ) :
    Finsupp.weight (cutWeight c A) e =
      (∑ j, (reesDegree e j : ℤ) * c j) + (subsetSum (ordinaryDegree e) Aᶜ : ℤ) := by
  rw [Finsupp.weight_eq_sum, Fintype.sum_sum_type]
  refine congrArg₂ (· + ·) ?_ ?_
  · apply sum_congr rfl
    intro j hj
    simp [cutWeight, nsmul_eq_mul]
  · simp only [cutWeight, Sum.elim_inr, nsmul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_mem]
    simp [subsetSum]

def shiftWeight (ρ : J → RankFunction V) : ShiftCut V → J ⊕ V → ℤ
  | .inl A => cutWeight (fun j => (ρ j A : ℤ) - ρ j univ) A
  | .inr ⟨A, P⟩ => cutWeight (fun j => (∑ C ∈ P.parts, (ρ j C : ℤ)) - ρ j univ) A

def shiftThreshold (η : RankFunction V) (i : ℕ) : ShiftCut V → ℤ
  | .inl A => (η univ : ℤ) - η A
  | .inr ⟨A, P⟩ => (η univ : ℤ) + i + P.parts.card - A.card - ∑ C ∈ P.parts, (η C : ℤ)

theorem shiftWeight_lower (ρ : J → RankFunction V) (A : Finset V)
    (e : J ⊕ V →₀ ℕ) :
    Finsupp.weight (shiftWeight ρ (.inl A)) e =
      (subsetSum (ordinaryDegree e) Aᶜ : ℤ) +
        multiRank ρ (reesDegree e) A - multiRank ρ (reesDegree e) univ := by
  rw [shiftWeight, weight_cutWeight]
  simp only [mul_sub, sum_sub_distrib, multiRank_apply, Nat.cast_sum, Nat.cast_mul]
  ring

theorem shiftWeight_partition (ρ : J → RankFunction V) (A : Finset V)
    (P : Finpartition A) (e : J ⊕ V →₀ ℕ) :
    Finsupp.weight (shiftWeight ρ (.inr ⟨A, P⟩)) e =
      (subsetSum (ordinaryDegree e) Aᶜ : ℤ) +
        (∑ C ∈ P.parts, (multiRank ρ (reesDegree e) C : ℤ)) -
          multiRank ρ (reesDegree e) univ := by
  rw [shiftWeight, weight_cutWeight]
  simp only [mul_sub, sum_sub_distrib, mul_sum, multiRank_apply, Nat.cast_sum, Nat.cast_mul]
  rw [Finset.sum_comm (s := univ) (t := P.parts)]
  ring

theorem shiftWeight_nonneg (ρ : J → RankFunction V) (e : J ⊕ V →₀ ℕ)
    (he : LowerFeasible (multiRank ρ (reesDegree e)).lower (ordinaryDegree e))
    (t : ShiftCut V) : 0 ≤ Finsupp.weight (shiftWeight ρ t) e := by
  rcases t with A | ⟨A, P⟩
  · rw [shiftWeight_lower]
    have hb := he Aᶜ
    have hL := (multiRank ρ (reesDegree e)).lower_add_compl Aᶜ
    simp only [compl_compl] at hL
    omega
  · rw [shiftWeight_partition]
    have hb := he Aᶜ
    have hL := (multiRank ρ (reesDegree e)).lower_add_compl Aᶜ
    have hP := (multiRank ρ (reesDegree e)).le_sum_partition P
    simp only [compl_compl] at hL
    have hPz : (multiRank ρ (reesDegree e) A : ℤ) ≤
        ∑ C ∈ P.parts, (multiRank ρ (reesDegree e) C : ℤ) := by exact_mod_cast hP
    omega

theorem shiftWeight_bounds_iff {k : Type*} [CommSemiring k] [Nontrivial k]
    (η : RankFunction V) (ρ : J → RankFunction V) (i : ℕ)
    (e : J ⊕ V →₀ ℕ) :
    (∀ t, shiftThreshold η i t ≤ Finsupp.weight (shiftWeight ρ t) e) ↔
      MvPolynomial.monomial (ordinaryDegree e) (1 : k) ∈
        rankShiftIdeal k (η.add (multiRank ρ (reesDegree e))) i := by
  rw [monomial_mem_rankShiftIdeal_partition_iff]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · have hc := h (.inr ⟨∅, Finpartition.empty (Finset V)⟩)
      rw [shiftWeight_partition] at hc
      simp only [shiftThreshold, Finpartition.empty_parts, card_empty, sum_empty,
        compl_empty, subsetSum_univ, Nat.cast_zero, add_zero, sub_zero] at hc
      change η univ + multiRank ρ (reesDegree e) univ + i ≤ (ordinaryDegree e).degree
      omega
    · intro U
      have hc := h (.inl Uᶜ)
      rw [shiftWeight_lower] at hc
      simp only [shiftThreshold, compl_compl] at hc
      have hL := (η.add (multiRank ρ (reesDegree e))).lower_add_compl U
      change (η.add (multiRank ρ (reesDegree e))).lower U +
        (η Uᶜ + multiRank ρ (reesDegree e) Uᶜ) =
          η univ + multiRank ρ (reesDegree e) univ at hL
      omega
    · intro A hA P
      have hc := h (.inr ⟨A, P⟩)
      rw [shiftWeight_partition] at hc
      simp only [shiftThreshold, ← Nat.cast_sum] at hc
      change η univ + multiRank ρ (reesDegree e) univ + i + P.parts.card ≤
        subsetSum (ordinaryDegree e) Aᶜ + A.card +
          ∑ C ∈ P.parts, (η C + multiRank ρ (reesDegree e) C)
      rw [sum_add_distrib]
      omega
  · rintro ⟨hdeg, hLower, hPart⟩ t
    rcases t with A | ⟨A, P⟩
    · rw [shiftWeight_lower]
      simp only [shiftThreshold]
      have hb := hLower Aᶜ
      have hL := (η.add (multiRank ρ (reesDegree e))).lower_add_compl Aᶜ
      simp only [compl_compl] at hL
      change (η.add (multiRank ρ (reesDegree e))).lower Aᶜ +
        (η A + multiRank ρ (reesDegree e) A) =
          η univ + multiRank ρ (reesDegree e) univ at hL
      omega
    · rw [shiftWeight_partition]
      simp only [shiftThreshold, ← Nat.cast_sum]
      by_cases hA : A = ∅
      · subst A
        have hP : P.parts = ∅ := P.parts_eq_empty_iff.mpr rfl
        simp only [hP, card_empty, sum_empty, compl_empty, subsetSum_univ,
          Nat.cast_zero, add_zero, sub_zero]
        change η univ + multiRank ρ (reesDegree e) univ + i ≤
          (ordinaryDegree e).degree at hdeg
        omega
      · have hp := hPart A (Finset.nonempty_iff_ne_empty.mpr hA) P
        change η univ + multiRank ρ (reesDegree e) univ + i + P.parts.card ≤
          subsetSum (ordinaryDegree e) Aᶜ + A.card +
            ∑ C ∈ P.parts, (η C + multiRank ρ (reesDegree e) C) at hp
        rw [sum_add_distrib] at hp
        omega

end CommAlg

end
end CheckedSource81

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "82: CommAlg.IntegralClosure.ShiftRees\n"

/-! ## Source: CommAlg.IntegralClosure.ShiftRees -/
section CheckedSource82

/-! # Integral closure of the actual multi-Rees coefficient ideal

The carrier is the literal coefficientwise direct sum in the multi-Rees
subalgebra. Its equality with the ideal of genuine homological shifts is
obtained from the separately proved graded-Tor rank formula.
-/

noncomputable section

namespace CommAlg

open Classical Finset Polymatroid

variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
variable {k : Type*} [CommRing k] [Nontrivial k]

def rankShiftMultiFamily (η : RankFunction V) (ρ : J → RankFunction V) (i : ℕ)
    (s : J →₀ ℕ) : Ideal (MvPolynomial V k) :=
  rankShiftIdeal k (η.add (multiRank ρ s)) i

theorem rankShiftMulti_action (η : RankFunction V) (ρ : J → RankFunction V) (i : ℕ)
    (s t : J →₀ ℕ) :
    powerProduct (fun j => rankIdeal k (ρ j)) s * rankShiftMultiFamily η ρ i t ≤
      rankShiftMultiFamily η ρ i (s + t) := by
  rw [powerProduct, ← rankIdeal_multiRank]
  have hr : (multiRank ρ s).add (η.add (multiRank ρ t)) =
      η.add (multiRank ρ (s + t)) := by
    apply RankFunction.ext_fun
    intro A
    simp only [multiRank_add, RankFunction.add]
    omega
  unfold rankShiftMultiFamily
  rw [← hr]
  exact rankIdeal_mul_rankShiftIdeal_le _ _ i

def rankShiftMultiIdeal (η : RankFunction V) (ρ : J → RankFunction V) (i : ℕ) :
    Ideal (multiReesAlgebra (fun j => rankIdeal k (ρ j))) :=
  multiReesIdeal (fun j => rankIdeal k (ρ j)) (rankShiftMultiFamily η ρ i)
    (rankShiftMulti_action η ρ i)

@[simp] theorem mem_rankShiftMultiIdeal (η : RankFunction V) (ρ : J → RankFunction V)
    (i : ℕ) (p : multiReesAlgebra (fun j => rankIdeal k (ρ j))) :
    p ∈ rankShiftMultiIdeal η ρ i ↔
      ∀ s, p.val.coeff s ∈ rankShiftIdeal k (η.add (multiRank ρ s)) i := Iff.rfl

theorem rankShiftMulti_mem_iff_weights (η : RankFunction V) (ρ : J → RankFunction V)
    (i : ℕ) (p : multiReesAlgebra (fun j => rankIdeal k (ρ j))) :
    p ∈ rankShiftMultiIdeal η ρ i ↔
      ∀ t, Weight.Bound (shiftWeight ρ t) (shiftThreshold η i t)
        (multiReesFlatten (fun j => rankIdeal k (ρ j)) p) := by
  rw [mem_rankShiftMultiIdeal]
  constructor
  · intro hp t e he
    have ha : ordinaryDegree e ∈ (p.val.coeff (reesDegree e)).support := by
      apply MvPolynomial.mem_support_iff.mpr
      rwa [multiReesFlatten_coeff] at he
    have hm := (mem_rankShiftIdeal_iff_coeff _ i _).mp (hp (reesDegree e))
      (ordinaryDegree e) ha
    exact (shiftWeight_bounds_iff η ρ i e).mpr hm t
  · intro hp s
    apply (mem_rankShiftIdeal_iff_coeff _ i _).mpr
    intro a ha
    let e := Finsupp.sumFinsuppAddEquivProdFinsupp.symm (s, a)
    have hs : reesDegree e = s := by simp [e, reesDegree]
    have ha' : ordinaryDegree e = a := by simp [e, ordinaryDegree]
    have he : (multiReesFlatten (fun j => rankIdeal k (ρ j)) p).coeff e ≠ 0 := by
      rw [multiReesFlatten_coeff, hs, ha']
      exact MvPolynomial.mem_support_iff.mp ha
    have hm := (shiftWeight_bounds_iff (k := k) η ρ i e).mp (fun t => hp t e he)
    simpa only [hs, ha'] using hm

theorem shiftWeight_bound_zero (ρ : J → RankFunction V) (t : ShiftCut V)
    (p : multiReesAlgebra (fun j => rankIdeal k (ρ j))) :
    Weight.Bound (shiftWeight ρ t) 0
      (multiReesFlatten (fun j => rankIdeal k (ρ j)) p) := by
  intro e he
  apply shiftWeight_nonneg ρ e _ t
  exact (mem_polymatroid_multiRees ρ p.val).mp p.property e he

/-- The multi-Rees ideal described by the exact shift-rank formula is
integrally closed over every domain. This includes every field, all
multidegrees, fixed twists, unit ideals, and inactive variables. -/
theorem rankShiftMultiIdeal_integrallyClosed [IsDomain k]
    (η : RankFunction V) (ρ : J → RankFunction V) (i : ℕ) :
    IsIntegrallyClosedIdeal (rankShiftMultiIdeal (k := k) η ρ i) := by
  apply Weight.integrallyClosed_of_weight_bounds
    (multiReesFlatten (fun j => rankIdeal k (ρ j)))
    (shiftWeight ρ) (shiftThreshold η i)
    (shiftWeight_bound_zero ρ)
  exact rankShiftMulti_mem_iff_weights η ρ i

end CommAlg

end
end CheckedSource82

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "83: CommAlg.Polymatroid.PowerShiftRees\n"

/-! ## Source: CommAlg.Polymatroid.PowerShiftRees -/
section CheckedSource83

/-!
# The actual power-shift Rees ideal and its minimal monomials

The degree-zero component is zero, as in the module in Theorem 4.4.
Minimality means divisibility by another module monomial through a monomial
of the genuine Rees algebra. This includes degree-zero polynomial factors.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V k : Type*} [Fintype V] [DecidableEq V] [CommRing k] [Nontrivial k]

def powerShiftPiece (ρ : RankFunction V) (i s : ℕ) : Ideal (MvPolynomial V k) :=
  if s = 0 then ⊥ else rankShiftIdeal k (RankFunction.scale s ρ) i

@[simp] theorem powerShiftPiece_zero (ρ : RankFunction V) (i : ℕ) :
    powerShiftPiece (k := k) ρ i 0 = ⊥ := by simp [powerShiftPiece]

theorem powerShiftPiece_pos (ρ : RankFunction V) (i : ℕ) {s : ℕ} (hs : 0 < s) :
    powerShiftPiece (k := k) ρ i s = rankShiftIdeal k (RankFunction.scale s ρ) i := by
  simp [powerShiftPiece, Nat.ne_of_gt hs]

theorem powerShiftPiece_le_pow (ρ : RankFunction V) (i s : ℕ) :
    powerShiftPiece (k := k) ρ i s ≤ (rankIdeal k ρ) ^ s := by
  by_cases hs : s = 0
  · simp [hs]
  · rw [powerShiftPiece, if_neg hs, ← rankIdeal_scale]
    exact rankShiftIdeal_le_rankIdeal _ _

theorem powerShiftPiece_action (ρ : RankFunction V) (i n s : ℕ) :
    (rankIdeal k ρ) ^ n * powerShiftPiece ρ i s ≤ powerShiftPiece ρ i (n + s) := by
  by_cases hs : s = 0
  · simp [hs]
  · have hns : n + s ≠ 0 := by omega
    simp only [powerShiftPiece, if_neg hs, if_neg hns]
    exact powerShiftIdeal_mul_le ρ i n s

/-- The ordinary coefficientwise ideal inside Mathlib's actual Rees algebra.
Its underlying graded module is precisely the direct sum of the positive
power-shift pieces. -/
def shiftReesIdeal (ρ : RankFunction V) (i : ℕ) : Ideal (reesAlgebra (rankIdeal k ρ)) where
  carrier := {p | ∀ s, p.val.coeff s ∈ powerShiftPiece ρ i s}
  zero_mem' := by simp
  add_mem' hp hq := fun s => by
    simpa only [Subalgebra.coe_add, Polynomial.coeff_add] using
      (powerShiftPiece ρ i s).add_mem (hp s) (hq s)
  smul_mem' r p hp := by
    intro s
    change (r.val * p.val).coeff s ∈ powerShiftPiece ρ i s
    rw [Polynomial.coeff_mul]
    apply Ideal.sum_mem
    rintro ⟨n, t⟩ hnt
    rw [← Finset.mem_antidiagonal.mp hnt]
    exact powerShiftPiece_action ρ i n t
      (Ideal.mul_mem_mul (r.property n) (hp t))

@[simp] theorem mem_shiftReesIdeal (ρ : RankFunction V) (i : ℕ)
    (p : reesAlgebra (rankIdeal k ρ)) :
    p ∈ shiftReesIdeal ρ i ↔ ∀ s, p.val.coeff s ∈ powerShiftPiece ρ i s := Iff.rfl

def shiftReesMonomial (ρ : RankFunction V) (i s : ℕ) (a : Exponent V)
    (ha : MvPolynomial.monomial a (1 : k) ∈ powerShiftPiece ρ i s) :
    reesAlgebra (rankIdeal k ρ) :=
  ⟨Polynomial.monomial s (MvPolynomial.monomial a 1),
    reesAlgebra.monomial_mem.mpr (powerShiftPiece_le_pow ρ i s ha)⟩

theorem shiftReesMonomial_mem (ρ : RankFunction V) (i s : ℕ) (a : Exponent V)
    (ha : MvPolynomial.monomial a (1 : k) ∈ powerShiftPiece ρ i s) :
    shiftReesMonomial ρ i s a ha ∈ shiftReesIdeal ρ i := by
  intro t
  change (Polynomial.monomial s (MvPolynomial.monomial a 1)).coeff t ∈ _
  by_cases ht : t = s
  · subst t
    simpa using ha
  · simp [Polynomial.coeff_monomial, ht, Ne.symm ht]

/-- The exponent factorization is literal multiplication of monomials in
the ambient polynomial ring, not a stipulated combinatorial action. -/
theorem rees_monomial_factorization {s r : ℕ} (hrs : r ≤ s)
    {a b : Exponent V} (hba : b ≤ a) :
    Polynomial.monomial (s - r) (MvPolynomial.monomial (a - b) (1 : k)) *
      Polynomial.monomial r (MvPolynomial.monomial b 1) =
        Polynomial.monomial s (MvPolynomial.monomial a 1) := by
  rw [Polynomial.monomial_mul_monomial, MvPolynomial.monomial_mul]
  simp only [Nat.sub_add_cancel hrs, tsub_add_cancel_of_le hba, one_mul]

/-- A genuine minimal module monomial: every divisor that belongs to the
module and whose quotient belongs to the Rees algebra is the same monomial.
The pair `(s,a)` records its actual Rees and ordinary multidegrees. -/
def IsMinimalShiftReesMonomial (ρ : RankFunction V) (i s : ℕ) (a : Exponent V) : Prop :=
  MvPolynomial.monomial a (1 : k) ∈ powerShiftPiece ρ i s ∧
    ∀ r b, r ≤ s → b ≤ a →
      MvPolynomial.monomial b (1 : k) ∈ powerShiftPiece ρ i r →
      MvPolynomial.monomial (a - b) (1 : k) ∈ (rankIdeal k ρ) ^ (s - r) →
      r = s ∧ b = a

theorem minimalShiftRees_positive {ρ : RankFunction V} {i s : ℕ} {a : Exponent V}
    (h : IsMinimalShiftReesMonomial (k := k) ρ i s a) : 0 < s := by
  by_contra hn
  have hs : s = 0 := by omega
  have hm := h.1
  simp [hs] at hm

theorem earlier_powerShift_product_le (ρ : RankFunction V) (i : ℕ) {r s : ℕ}
    (hrs : r < s) :
    (rankIdeal k ρ) ^ (s - r) * powerShiftPiece ρ i r ≤
      rankIdeal k ρ * powerShiftPiece ρ i (s - 1) := by
  have he : s - r = 1 + (s - 1 - r) := by omega
  have ht : s - 1 - r + r = s - 1 := by omega
  rw [he, pow_add, pow_one, mul_assoc]
  have h := powerShiftPiece_action (k := k) ρ i (s - 1 - r) r
  rw [ht] at h
  exact Ideal.mul_mono le_rfl h

/-- Exact intrinsic criterion for the new minimal monomials in a positive
Rees degree: ordinary minimal bases outside the preceding Rees product. -/
theorem minimalShiftRees_iff (ρ : RankFunction V) (i : ℕ) {s : ℕ} (hs : 0 < s)
    (a : Exponent V) :
    IsMinimalShiftReesMonomial (k := k) ρ i s a ↔
      a ∈ rankShiftFamily (RankFunction.scale s ρ) i ∧
        MvPolynomial.monomial a (1 : k) ∉ rankIdeal k ρ * powerShiftPiece ρ i (s - 1) := by
  have hpiece := powerShiftPiece_pos (k := k) ρ i hs
  constructor
  · intro h
    have ha := h.1
    rw [hpiece, rankShiftIdeal_eq_monomialIdeal, monomial_mem_iff] at ha
    obtain ⟨b, hb, hba⟩ := ha
    have hbPiece : MvPolynomial.monomial b (1 : k) ∈ powerShiftPiece ρ i s := by
      rw [hpiece, rankShiftIdeal_eq_monomialIdeal, monomial_mem_iff]
      exact ⟨b, hb, le_rfl⟩
    have he := (h.2 s b le_rfl hba hbPiece (by simp)).2
    refine ⟨he ▸ hb, ?_⟩
    intro hp
    by_cases hs1 : s = 1
    · simp [hs1] at hp
    have hprev : 0 < s - 1 := by omega
    rw [powerShiftPiece_pos ρ i hprev, rankIdeal, rankShiftIdeal_eq_monomialIdeal,
      monomialIdeal_mul, monomial_mem_iff] at hp
    obtain ⟨c, hc, hca⟩ := hp
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := mem_image.mp hc
    obtain ⟨hx, hy⟩ := mem_product.mp hxy
    have hya : y ≤ a := (le_add_left le_rfl).trans hca
    have hxa : x ≤ a - y := by
      intro j
      have hj := hca j
      simp only [Finsupp.add_apply] at hj
      change x j ≤ a j - y j
      omega
    have hyPiece : MvPolynomial.monomial y (1 : k) ∈ powerShiftPiece ρ i (s - 1) := by
      rw [powerShiftPiece_pos ρ i hprev, rankShiftIdeal_eq_monomialIdeal, monomial_mem_iff]
      exact ⟨y, hy, le_rfl⟩
    have hxPower : MvPolynomial.monomial (a - y) (1 : k) ∈ (rankIdeal k ρ) ^ (s - (s - 1)) := by
      rw [show s - (s - 1) = 1 by omega, pow_one]
      exact (monomial_mem_iff (rankBases ρ) (a - y)).mpr ⟨x, hx, hxa⟩
    have he := (h.2 (s - 1) y (by omega) hya hyPiece hxPower).1
    omega
  · rintro ⟨ha, hnew⟩
    refine ⟨?_, ?_⟩
    · rw [hpiece, rankShiftIdeal_eq_monomialIdeal, monomial_mem_iff]
      exact ⟨a, ha, le_rfl⟩
    · intro r b hrs hba hb hf
      by_cases hrsEq : r = s
      · subst r
        rw [hpiece, rankShiftIdeal_eq_monomialIdeal, monomial_mem_iff] at hb
        obtain ⟨c, hc, hcb⟩ := hb
        have he := (rankShiftFamily_equigenerated (RankFunction.scale s ρ) i).antichain
          c hc a ha (hcb.trans hba)
        exact ⟨rfl, le_antisymm hba (he ▸ hcb)⟩
      · have hrsLt : r < s := by omega
        have hp := Ideal.mul_mem_mul hf hb
        have hp' : MvPolynomial.monomial a (1 : k) ∈
            (rankIdeal k ρ) ^ (s - r) * powerShiftPiece ρ i r := by
          simpa only [MvPolynomial.monomial_mul, one_mul, tsub_add_cancel_of_le hba] using hp
        exact (hnew (earlier_powerShift_product_le ρ i hrsLt hp')).elim

end CommAlg.Polymatroid

end
end CheckedSource83

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "84: CommAlg.IntegralClosure.OrdinaryRees\n"

/-! ## Source: CommAlg.IntegralClosure.OrdinaryRees -/
section CheckedSource84

/-! # The ordinary Rees algebra and the positive-power shift ideal

This module applies the full weight proof inside Mathlib's ordinary
`reesAlgebra`. The comparison with one-variable multigrading is an actual
algebra homomorphism with an exact coefficient formula.
-/

noncomputable section

namespace CommAlg

open Classical Finset Polymatroid

variable {R : Type*} [CommRing R]

def reesToMulti (I : Ideal R) : reesAlgebra I →ₐ[R] multiReesAlgebra (fun _ : Unit => I) :=
  ((MvPolynomial.uniqueAlgEquiv R Unit).symm.toAlgHom.comp (reesAlgebra I).val).codRestrict
    (multiReesAlgebra (fun _ : Unit => I)) (by
      intro p s
      change ((MvPolynomial.uniqueAlgEquiv R Unit).symm p.val).coeff s ∈
        powerProduct (fun _ : Unit => I) s
      rw [MvPolynomial.coeff_uniqueAlgEquiv_symm]
      simpa [powerProduct] using p.property (s ()))

@[simp] theorem reesToMulti_coeff (I : Ideal R) (p : reesAlgebra I) (s : Unit →₀ ℕ) :
    ((reesToMulti I p).val).coeff s = p.val.coeff (s ()) :=
  MvPolynomial.coeff_uniqueAlgEquiv_symm _ p.val s

section Ranks

variable {V k : Type*} [Fintype V] [DecidableEq V] [CommRing k] [Nontrivial k]

theorem universalAugmentedRank_zero (A : Finset V) :
    universalAugmentedRank (zeroRank : RankFunction V) A = 0 := by
  apply Nat.eq_zero_of_le_zero
  have h := universalAugmentedRank_le_cost (zeroRank : RankFunction V) (⊥ : Finpartition A)
  simpa [partitionCost, Finpartition.parts_bot, cardinalLift, RankFunction.add,
    cardinalRank] using h

theorem rankShiftIdeal_zeroRank_pos (i : ℕ) (hi : 0 < i) :
    rankShiftIdeal k (zeroRank : RankFunction V) i = ⊥ := by
  have hu : universalHomologicalRank (zeroRank : RankFunction V) i univ = 0 := by
    apply Nat.eq_zero_of_le_zero
    have h := shiftRankValue_le_u (zeroRank : RankFunction V)
      (universalAugmentedRank zeroRank) i univ
    change universalHomologicalRank (zeroRank : RankFunction V) i univ ≤
      universalAugmentedRank zeroRank univ at h
    simpa only [universalAugmentedRank_zero] using h
  simp [rankShiftIdeal, hu, Nat.ne_of_lt hi]

theorem oneColor_rank (ρ : RankFunction V) (s : Unit →₀ ℕ) :
    (zeroRank : RankFunction V).add (multiRank (fun _ : Unit => ρ) s) = ρ.scale (s ()) := by
  apply RankFunction.ext_fun
  intro A
  simp [RankFunction.add, multiRank_apply, RankFunction.scale]

theorem positivePowerPiece_eq_oneColor (ρ : RankFunction V) (i : ℕ) (hi : 0 < i)
    (s : Unit →₀ ℕ) :
    powerShiftPiece (k := k) ρ i (s ()) =
      rankShiftIdeal k (zeroRank.add (multiRank (fun _ : Unit => ρ) s)) i := by
  rw [oneColor_rank]
  by_cases hs : s () = 0
  · rw [hs, powerShiftPiece_zero]
    have he : ρ.scale 0 = (zeroRank : RankFunction V) := by
      apply RankFunction.ext_fun
      intro A
      simp [RankFunction.scale]
    rw [he, rankShiftIdeal_zeroRank_pos i hi]
  · simp [powerShiftPiece, hs]

theorem mem_shiftReesIdeal_iff_oneColor (ρ : RankFunction V) (i : ℕ) (hi : 0 < i)
    (p : reesAlgebra (rankIdeal k ρ)) :
    p ∈ shiftReesIdeal ρ i ↔
      reesToMulti (rankIdeal k ρ) p ∈ rankShiftMultiIdeal zeroRank (fun _ : Unit => ρ) i := by
  rw [mem_shiftReesIdeal, mem_rankShiftMultiIdeal]
  simp only [reesToMulti_coeff, ← positivePowerPiece_eq_oneColor ρ i hi]
  constructor
  · intro h s
    exact h (s ())
  · intro h n
    simpa using h (Finsupp.single () n)

/-- Theorem 6.1 for the formula ideals, in Mathlib's actual ordinary Rees
algebra and with exactly the positive power layers. -/
theorem shiftReesIdeal_integrallyClosed [IsDomain k] (ρ : RankFunction V)
    (i : ℕ) (hi : 0 < i) : IsIntegrallyClosedIdeal (shiftReesIdeal (k := k) ρ i) := by
  let f := (multiReesFlatten (fun _ : Unit => rankIdeal k ρ)).comp
    (reesToMulti (rankIdeal k ρ)).toRingHom
  apply Weight.integrallyClosed_of_weight_bounds f
    (shiftWeight (fun _ : Unit => ρ)) (shiftThreshold zeroRank i)
    (fun t p => shiftWeight_bound_zero (fun _ : Unit => ρ) t (reesToMulti (rankIdeal k ρ) p))
  intro p
  rw [mem_shiftReesIdeal_iff_oneColor ρ i hi, rankShiftMulti_mem_iff_weights]
  rfl

end Ranks

theorem integrallyClosed_bot [IsDomain R] : IsIntegrallyClosedIdeal (⊥ : Ideal R) := by
  intro x hx
  obtain ⟨n, hn, c, hc, he⟩ := hx
  have hcz : ∀ j ∈ range n, c j = 0 := by
    intro j hj
    have hjn := mem_range.mp hj
    have hp : n - j ≠ 0 := by omega
    simpa only [Ideal.bot_pow hp, Ideal.mem_bot] using hc j hjn
  have hz : x ^ n = 0 := by
    have hs : ∑ j ∈ range n, c j * x ^ j = 0 :=
      sum_eq_zero (fun j hj => by rw [hcz j hj, zero_mul])
    simpa only [hs, add_zero] using he
  exact Ideal.mem_bot.mpr (eq_zero_of_pow_eq_zero hz)

end CommAlg

end
end CheckedSource84

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "85: CommAlg.Polymatroid.HomologicalMultiplication\n"

/-! ## Source: CommAlg.Polymatroid.HomologicalMultiplication -/
section CheckedSource85

/-! # Multiplication and containment for genuine homological shifts of ideals -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]

theorem homologicalShiftIdeal_le (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i : ℕ) : homologicalShiftIdeal I hI i ≤ I := by
  rcases hI.eq_bot_or_rank with h0 | ⟨g, hg⟩
  · subst I
    simp
  · rw [homologicalShiftIdeal_eq_rankShiftIdeal I hI g hg i, hg]
    exact rankShiftIdeal_le_rankIdeal g i

/-- Lemma 3.4 for actual polynomial ideals, including both zero ideals. -/
theorem homologicalShiftIdeal_mul_le (I J : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (hJ : IsPolymatroidalIdeal J) (i : ℕ) :
    I * homologicalShiftIdeal J hJ i ≤ homologicalShiftIdeal (I * J) (hI.mul hJ) i := by
  rcases hI.eq_bot_or_rank with h0 | ⟨g, hg⟩
  · subst I
    simp
  rcases hJ.eq_bot_or_rank with h0 | ⟨f, hf⟩
  · subst J
    simp
  have hp : I * J = rankIdeal k (g.add f) := by rw [hg, hf, rankIdeal_add]
  rw [homologicalShiftIdeal_eq_rankShiftIdeal J hJ f hf i,
    homologicalShiftIdeal_eq_rankShiftIdeal (I * J) (hI.mul hJ) (g.add f) hp i, hg]
  exact rankIdeal_mul_rankShiftIdeal_le g f i

end CommAlg.Polymatroid

end
end CheckedSource85

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "86: CommAlg.IntegralClosure.HomologicalRees\n"

/-! ## Source: CommAlg.IntegralClosure.HomologicalRees -/
section CheckedSource86

/-! # Integral closure of the genuine homological-shift Rees ideals

Every homogeneous coefficient below is the homological shift of an actual
polynomial ideal, defined through its genuine derived-Tor components.
The weight proof is applied only after proving exact equality of carriers.
-/

noncomputable section

namespace CommAlg

open Classical Finset Polymatroid

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]
variable {C : Type*} [Fintype C] [DecidableEq C]

theorem polymatroidal_powerProduct (I : C → Ideal (MvPolynomial V k))
    (hI : ∀ j, IsPolymatroidalIdeal (I j)) (s : C →₀ ℕ) :
    IsPolymatroidalIdeal (powerProduct I s) :=
  IsPolymatroidalIdeal.prod univ (fun j => I j ^ s j) (fun j _ => (hI j).pow (s j))

def homologicalMultiPiece (J : Ideal (MvPolynomial V k))
    (I : C → Ideal (MvPolynomial V k)) (hJ : IsPolymatroidalIdeal J)
    (hI : ∀ j, IsPolymatroidalIdeal (I j)) (i : ℕ) (s : C →₀ ℕ) :
    Ideal (MvPolynomial V k) :=
  homologicalShiftIdeal (J * powerProduct I s) (hJ.mul (polymatroidal_powerProduct I hI s)) i

theorem homologicalMultiPiece_action (J : Ideal (MvPolynomial V k))
    (I : C → Ideal (MvPolynomial V k)) (hJ : IsPolymatroidalIdeal J)
    (hI : ∀ j, IsPolymatroidalIdeal (I j)) (i : ℕ) (s t : C →₀ ℕ) :
    powerProduct I s * homologicalMultiPiece J I hJ hI i t ≤
      homologicalMultiPiece J I hJ hI i (s + t) := by
  have he : powerProduct I s * (J * powerProduct I t) = J * powerProduct I (s + t) := by
    rw [powerProduct_add]
    ac_rfl
  have h := homologicalShiftIdeal_mul_le (powerProduct I s) (J * powerProduct I t)
    (polymatroidal_powerProduct I hI s) (hJ.mul (polymatroidal_powerProduct I hI t)) i
  rw [homologicalShiftIdeal_congr _ (hJ.mul (polymatroidal_powerProduct I hI (s + t))) he i] at h
  exact h

def homologicalMultiIdeal (J : Ideal (MvPolynomial V k))
    (I : C → Ideal (MvPolynomial V k)) (hJ : IsPolymatroidalIdeal J)
    (hI : ∀ j, IsPolymatroidalIdeal (I j)) (i : ℕ) : Ideal (multiReesAlgebra I) :=
  multiReesIdeal I (homologicalMultiPiece J I hJ hI i)
    (homologicalMultiPiece_action J I hJ hI i)

@[simp] theorem mem_homologicalMultiIdeal (J : Ideal (MvPolynomial V k))
    (I : C → Ideal (MvPolynomial V k)) (hJ : IsPolymatroidalIdeal J)
    (hI : ∀ j, IsPolymatroidalIdeal (I j)) (i : ℕ) (p : multiReesAlgebra I) :
    p ∈ homologicalMultiIdeal J I hJ hI i ↔
      ∀ s, p.val.coeff s ∈ homologicalMultiPiece J I hJ hI i s := Iff.rfl

theorem homologicalMultiPiece_rank (η : RankFunction V) (ρ : C → RankFunction V)
    (hJ : IsPolymatroidalIdeal (rankIdeal k η))
    (hI : ∀ j, IsPolymatroidalIdeal (rankIdeal k (ρ j))) (i : ℕ) (s : C →₀ ℕ) :
    homologicalMultiPiece (rankIdeal k η) (fun j => rankIdeal k (ρ j)) hJ hI i s =
      rankShiftMultiFamily η ρ i s := by
  unfold homologicalMultiPiece rankShiftMultiFamily
  apply homologicalShiftIdeal_eq_rankShiftIdeal
  rw [powerProduct, ← rankIdeal_multiRank, rankIdeal_add]

theorem homologicalMultiIdeal_rank (η : RankFunction V) (ρ : C → RankFunction V)
    (hJ : IsPolymatroidalIdeal (rankIdeal k η))
    (hI : ∀ j, IsPolymatroidalIdeal (rankIdeal k (ρ j))) (i : ℕ) :
    homologicalMultiIdeal (rankIdeal k η) (fun j => rankIdeal k (ρ j)) hJ hI i =
      rankShiftMultiIdeal η ρ i := by
  ext p
  simp only [mem_homologicalMultiIdeal, homologicalMultiPiece_rank,
    mem_rankShiftMultiIdeal, rankShiftMultiFamily]

theorem homologicalMultiIdeal_zero_twist (I : C → Ideal (MvPolynomial V k))
    (hJ : IsPolymatroidalIdeal (⊥ : Ideal (MvPolynomial V k)))
    (hI : ∀ j, IsPolymatroidalIdeal (I j)) (i : ℕ) :
    homologicalMultiIdeal ⊥ I hJ hI i = ⊥ := by
  ext p
  simp only [mem_homologicalMultiIdeal, homologicalMultiPiece, Ideal.bot_mul,
    homologicalShiftIdeal_bot, Ideal.mem_bot]
  constructor
  · intro hp
    apply Subtype.ext
    apply MvPolynomial.ext
    simpa using hp
  · rintro rfl
    simp

/-- Corollary 6.2: the entire twisted multi-Rees ideal of genuine
homological shifts is integrally closed. Zero coordinates and the unit
ideal are included; a zero twist gives the zero ideal. -/
theorem homologicalMultiIdeal_integrallyClosed [IsDomain k]
    (J : Ideal (MvPolynomial V k)) (I : C → Ideal (MvPolynomial V k))
    (hJ : IsPolymatroidalIdeal J) (hI : ∀ j, IsPolymatroidalIdeal (I j))
    (hIne : ∀ j, I j ≠ ⊥) (i : ℕ) :
    IsIntegrallyClosedIdeal (homologicalMultiIdeal J I hJ hI i) := by
  rcases hJ.eq_bot_or_rank with h0 | ⟨η, hη⟩
  · subst J
    rw [homologicalMultiIdeal_zero_twist]
    exact integrallyClosed_bot
  · choose ρ hρ using fun j => (hI j).exists_rank (hIne j)
    have he : I = fun j => rankIdeal k (ρ j) := funext hρ
    subst J
    subst I
    rw [homologicalMultiIdeal_rank]
    exact rankShiftMultiIdeal_integrallyClosed η ρ i

def homologicalPowerPiece (I : Ideal (MvPolynomial V k)) (hI : IsPolymatroidalIdeal I)
    (i s : ℕ) : Ideal (MvPolynomial V k) :=
  if s = 0 then ⊥ else homologicalShiftIdeal (I ^ s) (hI.pow s) i

theorem homologicalPowerPiece_action (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i n s : ℕ) :
    I ^ n * homologicalPowerPiece I hI i s ≤ homologicalPowerPiece I hI i (n + s) := by
  by_cases hs : s = 0
  · simp [homologicalPowerPiece, hs]
  · have hns : n + s ≠ 0 := by omega
    simp only [homologicalPowerPiece, if_neg hs, if_neg hns]
    have h := homologicalShiftIdeal_mul_le (I ^ n) (I ^ s) (hI.pow n) (hI.pow s) i
    rw [homologicalShiftIdeal_congr _ (hI.pow (n + s)) (pow_add I n s).symm i] at h
    exact h

def homologicalPowerIdeal (I : Ideal (MvPolynomial V k)) (hI : IsPolymatroidalIdeal I)
    (i : ℕ) : Ideal (reesAlgebra I) where
  carrier := {p | ∀ s, p.val.coeff s ∈ homologicalPowerPiece I hI i s}
  zero_mem' := by simp
  add_mem' hp hq := fun s => by
    simpa only [Subalgebra.coe_add, Polynomial.coeff_add] using
      (homologicalPowerPiece I hI i s).add_mem (hp s) (hq s)
  smul_mem' r p hp := by
    intro s
    change (r.val * p.val).coeff s ∈ homologicalPowerPiece I hI i s
    rw [Polynomial.coeff_mul]
    apply Ideal.sum_mem
    rintro ⟨n, t⟩ hnt
    rw [← Finset.mem_antidiagonal.mp hnt]
    exact homologicalPowerPiece_action I hI i n t
      (Ideal.mul_mem_mul (r.property n) (hp t))

@[simp] theorem mem_homologicalPowerIdeal (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i : ℕ) (p : reesAlgebra I) :
    p ∈ homologicalPowerIdeal I hI i ↔
      ∀ s, p.val.coeff s ∈ homologicalPowerPiece I hI i s := Iff.rfl

theorem homologicalPowerPiece_rank (ρ : RankFunction V)
    (hI : IsPolymatroidalIdeal (rankIdeal k ρ)) (i s : ℕ) :
    homologicalPowerPiece (rankIdeal k ρ) hI i s = powerShiftPiece ρ i s := by
  by_cases hs : s = 0
  · simp [homologicalPowerPiece, powerShiftPiece, hs]
  · simp only [homologicalPowerPiece, powerShiftPiece, if_neg hs]
    exact homologicalShiftIdeal_eq_rankShiftIdeal _ _ (ρ.scale s)
      (rankIdeal_scale k ρ s).symm i

theorem homologicalPowerIdeal_rank (ρ : RankFunction V)
    (hI : IsPolymatroidalIdeal (rankIdeal k ρ)) (i : ℕ) :
    homologicalPowerIdeal (rankIdeal k ρ) hI i = shiftReesIdeal ρ i := by
  ext p
  simp only [mem_homologicalPowerIdeal, homologicalPowerPiece_rank, mem_shiftReesIdeal]

theorem homologicalPowerIdeal_bot
    (hI : IsPolymatroidalIdeal (⊥ : Ideal (MvPolynomial V k))) (i : ℕ) :
    homologicalPowerIdeal ⊥ hI i = ⊥ := by
  have hp (s : ℕ) : homologicalPowerPiece ⊥ hI i s = ⊥ := by
    by_cases hs : s = 0
    · simp [homologicalPowerPiece, hs]
    · simp [homologicalPowerPiece, hs, Ideal.bot_pow hs]
  ext p
  simp only [mem_homologicalPowerIdeal, hp, Ideal.mem_bot]
  constructor
  · intro h
    apply Subtype.ext
    apply Polynomial.ext
    simpa using h
  · rintro rfl
    simp

/-- Theorem 6.1 in its literal ideal form: the positive-power direct sum of
genuine homological shifts is an integrally closed ideal of Mathlib's
ordinary Rees algebra, for every polymatroidal ideal and every `i > 0`. -/
theorem homologicalPowerIdeal_integrallyClosed [IsDomain k]
    (I : Ideal (MvPolynomial V k)) (hI : IsPolymatroidalIdeal I)
    (i : ℕ) (hi : 0 < i) : IsIntegrallyClosedIdeal (homologicalPowerIdeal I hI i) := by
  rcases hI.eq_bot_or_rank with h0 | ⟨ρ, hρ⟩
  · subst I
    rw [homologicalPowerIdeal_bot]
    exact integrallyClosed_bot
  · subst I
    rw [homologicalPowerIdeal_rank]
    exact shiftReesIdeal_integrallyClosed ρ i hi

end CommAlg

end
end CheckedSource86

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "87: CommAlg.Rees.OneColor\n"

/-! ## Source: CommAlg.Rees.OneColor -/
section CheckedSource87

/-! # The actual equivalence between ordinary and one-color Rees algebras -/

noncomputable section

namespace CommAlg

open Classical

variable {R : Type*} [CommRing R]

theorem reesToMulti_injective (I : Ideal R) : Function.Injective (reesToMulti I) := by
  intro p q h
  apply Subtype.ext
  apply (MvPolynomial.uniqueAlgEquiv R Unit).symm.injective
  exact congrArg Subtype.val h

theorem reesToMulti_surjective (I : Ideal R) : Function.Surjective (reesToMulti I) := by
  intro q
  have hp : (MvPolynomial.uniqueAlgEquiv R Unit) q.val ∈ reesAlgebra I := by
    intro n
    rw [MvPolynomial.coeff_uniqueAlgEquiv]
    simpa [powerProduct] using q.property (Finsupp.single () n)
  refine ⟨⟨(MvPolynomial.uniqueAlgEquiv R Unit) q.val, hp⟩, ?_⟩
  apply Subtype.ext
  exact (MvPolynomial.uniqueAlgEquiv R Unit).symm_apply_apply q.val

/-- Ordinary polynomial grading and the one-color multigrading define
isomorphic Rees algebras, with their actual coefficient conditions. -/
def reesMultiEquiv (I : Ideal R) : reesAlgebra I ≃ₐ[R] multiReesAlgebra (fun _ : Unit => I) :=
  AlgEquiv.ofBijective (reesToMulti I) ⟨reesToMulti_injective I, reesToMulti_surjective I⟩

@[simp] theorem reesMultiEquiv_apply (I : Ideal R) (p : reesAlgebra I) :
    reesMultiEquiv I p = reesToMulti I p := rfl

theorem reesMultiEquiv_symm_val (I : Ideal R)
    (q : multiReesAlgebra (fun _ : Unit => I)) :
    ((reesMultiEquiv I).symm q).val = (MvPolynomial.uniqueAlgEquiv R Unit) q.val := by
  have h := congrArg Subtype.val ((reesMultiEquiv I).apply_symm_apply q)
  change (MvPolynomial.uniqueAlgEquiv R Unit).symm ((reesMultiEquiv I).symm q).val = q.val at h
  have hh := congrArg (MvPolynomial.uniqueAlgEquiv R Unit) h
  simpa only [AlgEquiv.apply_symm_apply] using hh

end CommAlg

end
end CheckedSource87

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "88: CommAlg.Rees.HomologicalGeneration\n"

/-! ## Source: CommAlg.Rees.HomologicalGeneration -/
section CheckedSource88

/-! # Full generation bounds for the genuine homological-shift modules

The conclusions are literal ideal-span equalities inside the actual ordinary
and multi-Rees algebras. They include every polynomial element of the modules,
all fixed twists, zero ideals and inactive coordinates.
-/

noncomputable section

set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

namespace CommAlg

open Classical Finset Polymatroid

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]
variable {C : Type*} [Fintype C] [DecidableEq C]

theorem homologicalMultiPiece_le_powerProduct (J : Ideal (MvPolynomial V k))
    (I : C → Ideal (MvPolynomial V k)) (hJ : IsPolymatroidalIdeal J)
    (hI : ∀ c, IsPolymatroidalIdeal (I c)) (i : ℕ) (s : C →₀ ℕ) :
    homologicalMultiPiece J I hJ hI i s ≤ powerProduct I s :=
  (homologicalShiftIdeal_le _ _ i).trans Ideal.mul_le_right

/-- The complete module-generation assertion of Corollary 4.1, for the
actual ideal of genuine homological shifts in the actual multi-Rees ring. -/
theorem homologicalMultiIdeal_generated_in_box (J : Ideal (MvPolynomial V k))
    (I : C → Ideal (MvPolynomial V k)) (hJ : IsPolymatroidalIdeal J)
    (hI : ∀ c, IsPolymatroidalIdeal (I c)) (i : ℕ) :
    homologicalMultiIdeal J I hJ hI i =
      Ideal.span (reesBoxGenerators I (homologicalMultiPiece J I hJ hI i) i) := by
  apply multiReesIdeal_span_box _ _ (homologicalMultiPiece_action J I hJ hI i)
    (homologicalMultiPiece_le_powerProduct J I hJ hI i)
  intro s c hs
  exact homologicalShift_severalColors I J hI hJ s i c hs

theorem homologicalShiftIdeal_top_pos
    (hS : IsPolymatroidalIdeal (⊤ : Ideal (MvPolynomial V k))) (i : ℕ) (hi : 0 < i) :
    homologicalShiftIdeal ⊤ hS i = ⊥ := by
  rw [homologicalShiftIdeal_eq_rankShiftIdeal _ hS zeroRank (rankIdeal_zeroRank k).symm i]
  exact rankShiftIdeal_zeroRank_pos i hi

theorem homologicalMultiPiece_oneColor (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i : ℕ) (s : Unit →₀ ℕ) :
    homologicalMultiPiece ⊤ (fun _ : Unit => I) isPolymatroidalIdeal_top (fun _ => hI) i s =
      homologicalShiftIdeal (I ^ (s ())) (hI.pow _) i := by
  apply homologicalShiftIdeal_congr
  simp [powerProduct]

theorem homologicalPowerPiece_eq_oneColor (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i : ℕ) (hi : 0 < i) (s : Unit →₀ ℕ) :
    homologicalPowerPiece I hI i (s ()) =
      homologicalMultiPiece ⊤ (fun _ : Unit => I) isPolymatroidalIdeal_top (fun _ => hI) i s := by
  rw [homologicalMultiPiece_oneColor]
  by_cases hs : s () = 0
  · simp only [homologicalPowerPiece, hs, ite_true, pow_zero, Ideal.one_eq_top]
    exact (homologicalShiftIdeal_top_pos _ i hi).symm
  · simp [homologicalPowerPiece, hs]

theorem mem_homologicalPowerIdeal_iff_oneColor (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i : ℕ) (hi : 0 < i) (p : reesAlgebra I) :
    p ∈ homologicalPowerIdeal I hI i ↔
      reesMultiEquiv I p ∈ homologicalMultiIdeal ⊤ (fun _ : Unit => I)
        isPolymatroidalIdeal_top (fun _ => hI) i := by
  rw [mem_homologicalPowerIdeal, mem_homologicalMultiIdeal]
  simp only [reesMultiEquiv_apply, reesToMulti_coeff,
    ← homologicalPowerPiece_eq_oneColor I hI i hi]
  constructor
  · intro h s
    exact h (s ())
  · intro h n
    simpa using h (Finsupp.single () n)

theorem homologicalPowerIdeal_eq_map_oneColor (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i : ℕ) (hi : 0 < i) :
    homologicalPowerIdeal I hI i = Ideal.map (reesMultiEquiv I).symm.toRingHom
      (homologicalMultiIdeal ⊤ (fun _ : Unit => I) isPolymatroidalIdeal_top (fun _ => hI) i) := by
  calc
    _ = Ideal.comap (reesMultiEquiv I).toRingHom
        (homologicalMultiIdeal ⊤ (fun _ : Unit => I) isPolymatroidalIdeal_top (fun _ => hI) i) := by
      ext p
      exact mem_homologicalPowerIdeal_iff_oneColor I hI i hi p
    _ = _ := (Ideal.map_comap_of_equiv (reesMultiEquiv I).symm.toRingEquiv).symm

/-- Homogeneous elements of the actual positive-power shift module in Rees
degrees at most `i`. Its degree-zero component is zero by definition. -/
def homologicalPowerBoxGenerators (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i : ℕ) : Set (reesAlgebra I) :=
  {p | ∃ s r, s ≤ i ∧ r ∈ homologicalPowerPiece I hI i s ∧
    p.val = Polynomial.monomial s r}

theorem oneColor_box_image (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i : ℕ) (hi : 0 < i) :
    (reesMultiEquiv I).symm '' reesBoxGenerators (fun _ : Unit => I)
      (homologicalMultiPiece ⊤ (fun _ : Unit => I) isPolymatroidalIdeal_top (fun _ => hI) i) i =
        homologicalPowerBoxGenerators I hI i := by
  ext p
  constructor
  · rintro ⟨q, ⟨s, r, hs, hr, he⟩, rfl⟩
    refine ⟨s (), r, hs (), ?_, ?_⟩
    · rwa [homologicalPowerPiece_eq_oneColor I hI i hi s]
    · rw [reesMultiEquiv_symm_val, he, MvPolynomial.uniqueAlgEquiv_monomial]
  · rintro ⟨n, r, hn, hr, he⟩
    refine ⟨reesMultiEquiv I p, ?_, (reesMultiEquiv I).symm_apply_apply p⟩
    refine ⟨Finsupp.single () n, r, ?_, ?_, ?_⟩
    · intro c
      cases c
      simpa using hn
    · rw [← homologicalPowerPiece_eq_oneColor I hI i hi (Finsupp.single () n)]
      simpa using hr
    · change (MvPolynomial.uniqueAlgEquiv (MvPolynomial V k) Unit).symm p.val = _
      rw [he]
      simpa using (MvPolynomial.uniqueAlgEquiv_symm_monomial
        (R := MvPolynomial V k) (d := Finsupp.single () n) (r := r))

/-- The full module-generation conclusion of Theorem 1.1, as a literal span
inside Mathlib's ordinary Rees algebra. It holds for all polymatroidal ideals,
including zero and unit ideals, over every field. -/
theorem homologicalPowerIdeal_generated_le (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i : ℕ) (hi : 0 < i) :
    homologicalPowerIdeal I hI i = Ideal.span (homologicalPowerBoxGenerators I hI i) := by
  rw [homologicalPowerIdeal_eq_map_oneColor I hI i hi,
    homologicalMultiIdeal_generated_in_box, Ideal.map_span]
  exact congrArg Ideal.span (oneColor_box_image I hI i hi)

end CommAlg

end
end CheckedSource88

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "89: CommAlg.Polymatroid.UniformSharpness\n"

/-! ## Source: CommAlg.Polymatroid.UniformSharpness -/
section CheckedSource89

/-!
# Uniform-matroid sharpness in every positive homological degree

For a ground set of size `i + 1`, the rank-`i` uniform matroid gives the
squarefree Veronese example. Below the `i`th power its homological rank
cannot reach the required degree. At that power the only base exponent is
the constant vector `i`.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem uniform_homologicalRank_cap (i s : ℕ) (hi : 1 ≤ i) (hs : 1 ≤ s)
    (A : Finset V) :
    homologicalRank (uniformPowerRank V i s) (uniformPowerRank_active hi hs) i A ≤
      A.card * s := by
  have h := homologicalRank_le_sum_singletons (uniformPowerRank V i s)
    (uniformPowerRank_active hi hs) i A
  simpa only [uniformPowerRank_apply, card_singleton, min_eq_left hi,
    Nat.mul_one, sum_const_nat] using h

/-- The total rank is too small at every positive power below `i`. -/
theorem uniform_homologicalRank_lt {i s : ℕ} (hi : 1 ≤ i) (hs : 1 ≤ s)
    (hsi : s < i) (hcard : Fintype.card V = i + 1) :
    homologicalRank (uniformPowerRank V i s) (uniformPowerRank_active hi hs) i univ <
      uniformPowerRank V i s univ + i := by
  have h := uniform_homologicalRank_cap (V := V) i s hi hs univ
  simp only [card_univ, hcard, uniformPowerRank_apply,
    min_eq_right (Nat.le_succ i)] at h ⊢
  nlinarith

theorem uniform_threshold_supportPred_bound {i : ℕ} (hi : 1 ≤ i)
    (hcard : Fintype.card V = i + 1) {A : Finset V} (hA : A.Nonempty) :
    subsetSum (supportPred (constExponent i : Exponent V)) A ≤
      uniformPowerRank V i i A - 1 := by
  have hc : 1 ≤ A.card := card_pos.mpr hA
  have hcn : A.card ≤ i + 1 := by
    simpa only [hcard] using card_le_univ A
  have him : i - 1 + 1 = i := Nat.sub_add_cancel hi
  have hsum : subsetSum (supportPred (constExponent i : Exponent V)) A =
      A.card * (i - 1) := by
    simp [subsetSum]
  rw [hsum, uniformPowerRank_apply]
  rcases le_total A.card i with h | h
  · rw [min_eq_left h]
    have hp : 1 ≤ i * A.card := by nlinarith
    have hs := Nat.sub_add_cancel hp
    nlinarith
  · rw [min_eq_right h]
    have hp : 1 ≤ i * i := by nlinarith
    have hs := Nat.sub_add_cancel hp
    nlinarith

/-- The constant exponent satisfies every augmented partition inequality. -/
theorem uniform_threshold_augmented_feasible {i : ℕ} (hi : 1 ≤ i)
    (hcard : Fintype.card V = i + 1) :
    ∀ A, subsetSum (constExponent i : Exponent V) A ≤
      augmentedPartitionRank (uniformPowerRank V i i) A :=
  (supportPred_nonempty_bounds_iff_augmented (uniformPowerRank V i i)
    (constExponent i)).mp (fun _ hA => uniform_threshold_supportPred_bound hi hcard hA)

theorem uniform_threshold_upperFeasible {i : ℕ} (hi : 1 ≤ i)
    (hcard : Fintype.card V = i + 1) :
    UpperFeasible
      (homologicalRank (uniformPowerRank V i i) (uniformPowerRank_active hi hi) i)
      (constExponent i) := by
  intro A
  by_cases hA : A.Nonempty
  · rw [homologicalRank_apply _ _ _ hA]
    change subsetSum (constExponent i) A ≤
      min (uniformPowerRank V i i A + i) (augmentedPartitionRank _ A)
    refine le_min ?_ (uniform_threshold_augmented_feasible hi hcard A)
    rw [subsetSum_constExponent, uniformPowerRank_apply]
    have hc : A.card ≤ i + 1 := by simpa only [hcard] using card_le_univ A
    rcases le_total A.card i with h | h
    · rw [min_eq_left h]
      nlinarith
    · rw [min_eq_right h]
      nlinarith
  · have he := not_nonempty_iff_eq_empty.mp hA
    simp [he, subsetSum]

/-- At the `i`th power the required total degree is attained. -/
theorem uniform_homologicalRank_top {i : ℕ} (hi : 1 ≤ i)
    (hcard : Fintype.card V = i + 1) :
    homologicalRank (uniformPowerRank V i i) (uniformPowerRank_active hi hi) i univ =
      uniformPowerRank V i i univ + i := by
  have hLo := uniform_threshold_upperFeasible hi hcard univ
  have hHi := uniform_homologicalRank_cap (V := V) i i hi hi univ
  simp only [subsetSum_constExponent, card_univ, hcard] at hLo hHi
  simp only [uniformPowerRank_apply, card_univ, hcard,
    min_eq_right (Nat.le_succ i)]
  nlinarith

theorem uniform_threshold_isRankBase {i : ℕ} (hi : 1 ≤ i)
    (hcard : Fintype.card V = i + 1) :
    IsRankBase
      (homologicalRank (uniformPowerRank V i i) (uniformPowerRank_active hi hi) i)
      (constExponent i) := by
  refine ⟨?_, uniform_threshold_upperFeasible hi hcard⟩
  rw [degree_constExponent, uniform_homologicalRank_top hi hcard]
  simp only [hcard, uniformPowerRank_apply, card_univ,
    min_eq_right (Nat.le_succ i)]
  nlinarith

/-- The exact unique base at the sharp threshold, with no restriction on the
positive homological degree. -/
theorem uniform_threshold_isRankBase_iff {i : ℕ} (hi : 1 ≤ i)
    (hcard : Fintype.card V = i + 1) (a : Exponent V) :
    IsRankBase
      (homologicalRank (uniformPowerRank V i i) (uniformPowerRank_active hi hi) i) a ↔
      a = constExponent i := by
  constructor
  · intro ha
    have hcap : a ≤ constExponent i := by
      intro j
      have h := ha.2 {j}
      rw [homologicalRank_singleton] at h
      simpa only [subsetSum, sum_singleton, uniformPowerRank_apply, card_singleton,
        min_eq_left hi, Nat.mul_one, constExponent_apply] using h
    apply eq_of_le_of_degree_eq hcap
    exact ha.1.trans (uniform_threshold_isRankBase hi hcard).1.symm
  · rintro rfl
    exact uniform_threshold_isRankBase hi hcard

theorem uniform_threshold_rankBases {i : ℕ} (hi : 1 ≤ i)
    (hcard : Fintype.card V = i + 1) :
    rankBases
      (homologicalRank (uniformPowerRank V i i) (uniformPowerRank_active hi hi) i) =
      {constExponent i} := by
  ext a
  rw [mem_rankBases, uniform_threshold_isRankBase_iff hi hcard, mem_singleton]

end CommAlg.Polymatroid

end
end CheckedSource89

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "90: CommAlg.Polymatroid.HomologicalSharpness\n"

/-! ## Source: CommAlg.Polymatroid.HomologicalSharpness -/
section CheckedSource90

/-! # The sharp uniform-Veronese example in every positive degree

The ideal is the squarefree Veronese ideal in `i+1` variables. Its exact
generators are identified, and every homological shift assertion uses
the genuine derived-Tor definition on actual powers of that ideal.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]

def squarefreeVeroneseIdeal (k : Type u) [CommRing k] (V : Type u)
    [Fintype V] [LinearOrder V] (d : ℕ) : Ideal (MvPolynomial V k) :=
  rankIdeal k (uniformRank V d)

theorem squarefreeVeronese_polymatroidal (d : ℕ) :
    IsPolymatroidalIdeal (squarefreeVeroneseIdeal k V d) :=
  isPolymatroidalIdeal_rankIdeal _

/-- The generating monomials are exactly the squarefree monomials of
degree `d`, whenever `d` is at most the number of variables. -/
theorem squarefreeVeronese_generators (d : ℕ) (hd : d ≤ Fintype.card V) (a : Exponent V) :
    a ∈ rankBases (uniformRank V d) ↔ a.degree = d ∧ ∀ j, a j ≤ 1 := by
  have he : uniformPowerRank V d 1 = uniformRank V d := by
    apply RankFunction.ext_fun
    intro A
    simp
  rw [← he, mem_rankBases, isRankBase_uniformPower_iff d 1 hd]
  simp

theorem squarefreeVeronese_power_rank (d s : ℕ) :
    squarefreeVeroneseIdeal k V d ^ s = rankIdeal k (uniformPowerRank V d s) :=
  (rankIdeal_scale k (uniformRank V d) s).symm

/-- Proposition 4.2, vanishing at every positive power strictly below `i`. -/
theorem squarefreeVeronese_shift_below {i s : ℕ} (hi : 1 ≤ i) (hs : 1 ≤ s)
    (hsi : s < i) (hcard : Fintype.card V = i + 1) :
    homologicalShiftIdeal (squarefreeVeroneseIdeal k V i ^ s)
      ((squarefreeVeronese_polymatroidal i).pow s) i = ⊥ := by
  rw [homologicalShiftIdeal_eq_rankShiftIdeal _ _ (uniformPowerRank V i s)
    (squarefreeVeronese_power_rank i s) i]
  have he : universalHomologicalRank (uniformPowerRank V i s) i =
      homologicalRank (uniformPowerRank V i s) (uniformPowerRank_active hi hs) i := by
    apply RankFunction.ext_fun
    exact universalHomologicalRank_eq_active _ _ i
  have hlt := uniform_homologicalRank_lt hi hs hsi hcard
  simp only [rankShiftIdeal, he, if_neg (Nat.ne_of_lt hlt)]

theorem monomial_constExponent_eq_prod_pow (i : ℕ) :
    MvPolynomial.monomial (constExponent i : Exponent V) (1 : k) =
      (∏ j : V, MvPolynomial.X j) ^ i := by
  rw [← Finset.prod_pow]
  rw [MvPolynomial.prod_X_pow]
  have he : (constExponent i : Exponent V) = Finsupp.indicator univ (fun _ _ => i) := by
    ext j
    simp
  exact congrArg (fun a : Exponent V => MvPolynomial.monomial a (1 : k)) he

/-- Proposition 4.2, the exact principal ideal at the sharp threshold. -/
theorem squarefreeVeronese_shift_at_threshold {i : ℕ} (hi : 1 ≤ i)
    (hcard : Fintype.card V = i + 1) :
    homologicalShiftIdeal (squarefreeVeroneseIdeal k V i ^ i)
      ((squarefreeVeronese_polymatroidal i).pow i) i =
        Ideal.span {(∏ j : V, (MvPolynomial.X j : MvPolynomial V k)) ^ i} := by
  rw [homologicalShiftIdeal_eq_rankShiftIdeal _ _ (uniformPowerRank V i i)
    (squarefreeVeronese_power_rank i i) i]
  have he : universalHomologicalRank (uniformPowerRank V i i) i =
      homologicalRank (uniformPowerRank V i i) (uniformPowerRank_active hi hi) i := by
    apply RankFunction.ext_fun
    exact universalHomologicalRank_eq_active _ _ i
  rw [rankShiftIdeal, he, if_pos (uniform_homologicalRank_top hi hcard), rankIdeal,
    uniform_threshold_rankBases hi hcard, monomialIdeal]
  simp only [Finset.coe_singleton, Set.image_singleton, monomial_constExponent_eq_prod_pow]

theorem squarefreeVeronese_shift_at_threshold_ne_bot {i : ℕ} (hi : 1 ≤ i)
    (hcard : Fintype.card V = i + 1) :
    homologicalShiftIdeal (squarefreeVeroneseIdeal k V i ^ i)
      ((squarefreeVeronese_polymatroidal i).pow i) i ≠ ⊥ := by
  rw [squarefreeVeronese_shift_at_threshold hi hcard,
    ← monomial_constExponent_eq_prod_pow]
  intro he
  have hm : MvPolynomial.monomial (constExponent i : Exponent V) (1 : k) ∈
      Ideal.span {MvPolynomial.monomial (constExponent i : Exponent V) (1 : k)} :=
    Ideal.subset_span (Set.mem_singleton _)
  rw [he, Ideal.mem_bot] at hm
  simpa using hm

end CommAlg.Polymatroid

end
end CheckedSource90

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "91: CommAlg.Polymatroid.Revlex\n"

/-! ## Source: CommAlg.Polymatroid.Revlex -/
section CheckedSource91

/-! # Reverse lexicographic exchange and the colon variables

The strict comparison records the largest differing variable. This convention
orders equigenerated monomials in decreasing reverse lexicographic order.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [LinearOrder V]

def RevlexBefore (a b : Exponent V) : Prop :=
  ∃ i, a i < b i ∧ ∀ j, i < j → a j = b j

theorem revlexBefore_irrefl (a : Exponent V) : ¬ RevlexBefore a a := by
  rintro ⟨i, hi, _⟩
  exact (lt_irrefl _ hi)

theorem revlexBefore_trans {a b c : Exponent V}
    (hab : RevlexBefore a b) (hbc : RevlexBefore b c) : RevlexBefore a c := by
  obtain ⟨i, hi, he⟩ := hab
  obtain ⟨j, hj, hf⟩ := hbc
  rcases lt_trichotomy i j with hij | rfl | hji
  · refine ⟨j, ?_, fun x hx => (he x (hij.trans hx)).trans (hf x hx)⟩
    rw [he j hij]
    exact hj
  · exact ⟨i, hi.trans hj, fun x hx => (he x hx).trans (hf x hx)⟩
  · refine ⟨i, ?_, fun x hx => (he x hx).trans (hf x (hji.trans hx))⟩
    rw [← hf i hji]
    exact hi

theorem revlexBefore_asymm {a b : Exponent V} (hab : RevlexBefore a b) :
    ¬ RevlexBefore b a := fun hba => revlexBefore_irrefl a (revlexBefore_trans hab hba)

theorem revlexBefore_total {a b : Exponent V} (hab : a ≠ b) :
    RevlexBefore a b ∨ RevlexBefore b a := by
  let D := univ.filter (fun i => a i ≠ b i)
  have hD : D.Nonempty := by
    by_contra h
    apply hab
    ext i
    by_contra hi
    exact h ⟨i, mem_filter.mpr ⟨mem_univ i, hi⟩⟩
  let i := D.max' hD
  have hi : a i ≠ b i := (mem_filter.mp (D.max'_mem hD)).2
  have he : ∀ j, i < j → a j = b j := by
    intro j hij
    by_contra hj
    have hjD : j ∈ D := mem_filter.mpr ⟨mem_univ j, hj⟩
    exact (not_lt_of_ge (D.le_max' j hjD)) hij
  rcases lt_or_gt_of_ne hi with h | h
  · exact Or.inl ⟨i, h, he⟩
  · exact Or.inr ⟨i, h, fun j hj => (he j hj).symm⟩

def revlexBeforeFamily (B : Family V) (b : Exponent V) : Family V :=
  B.filter (fun a => RevlexBefore a b)

@[simp] theorem mem_revlexBeforeFamily (B : Family V) (a b : Exponent V) :
    a ∈ revlexBeforeFamily B b ↔ a ∈ B ∧ RevlexBefore a b := by
  simp [revlexBeforeFamily]

def revlexColonVariables (B : Family V) (b : Exponent V) : Finset V :=
  univ.filter (fun j => ∃ i, j < i ∧ 0 < b i ∧ exchange b i j ∈ B)

@[simp] theorem mem_revlexColonVariables (B : Family V) (b : Exponent V) (j : V) :
    j ∈ revlexColonVariables B b ↔
      ∃ i, j < i ∧ 0 < b i ∧ exchange b i j ∈ B := by
  simp [revlexColonVariables]

theorem exchange_revlexBefore (b : Exponent V) {i j : V}
    (hji : j < i) (hi : 0 < b i) : RevlexBefore (exchange b i j) b := by
  refine ⟨i, ?_, ?_⟩
  · simp only [exchange_apply, ite_true, if_neg (ne_of_gt hji)]
    omega
  · intro x hix
    simp [exchange_apply, ne_of_gt hix, ne_of_gt (hji.trans hix)]

/-- A preceding generator supplies a colon variable which divides its quotient
by the gcd with the current generator. -/
theorem revlex_exchange {B : Family V} (hB : ExchangeAxiom B)
    {a b : Exponent V} (ha : a ∈ B) (hb : b ∈ B) (hab : RevlexBefore a b) :
    ∃ j ∈ revlexColonVariables B b, b j < a j := by
  obtain ⟨i, hi, he⟩ := hab
  obtain ⟨j, hj, hex⟩ := hB b hb a ha i hi
  have hji : j < i := by
    rcases lt_trichotomy j i with h | rfl | h
    · exact h
    · omega
    · have := he j h
      omega
  exact ⟨j, (mem_revlexColonVariables B b j).mpr ⟨i, hji, by omega, hex⟩, hj⟩

/-- Exact divisibility criterion for the preceding generators, before passing
to polynomial ideals. -/
theorem contains_revlexBefore_add_iff {B : Family V} (hB : ExchangeAxiom B)
    {b : Exponent V} (hb : b ∈ B) (a : Exponent V) :
    Contains (revlexBeforeFamily B b) (a + b) ↔
      ∃ j ∈ revlexColonVariables B b, 0 < a j := by
  constructor
  · rintro ⟨c, hc, hca⟩
    obtain ⟨hcB, hcb⟩ := (mem_revlexBeforeFamily B c b).mp hc
    obtain ⟨j, hj, hbj⟩ := revlex_exchange hB hcB hb hcb
    refine ⟨j, hj, ?_⟩
    have hle := hca j
    simp only [Finsupp.add_apply] at hle
    omega
  · rintro ⟨j, hj, haj⟩
    obtain ⟨i, hji, hbi, hex⟩ := (mem_revlexColonVariables B b j).mp hj
    refine ⟨exchange b i j, (mem_revlexBeforeFamily B _ b).mpr
      ⟨hex, exchange_revlexBefore b hji hbi⟩, ?_⟩
    intro x
    simp only [exchange_apply, Finsupp.add_apply]
    by_cases hxj : x = j
    · subst x
      simp only [if_neg (ne_of_lt hji), ite_true]
      omega
    · simp only [if_neg hxj]
      split <;> omega

end CommAlg.Polymatroid

end
end CheckedSource91

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "92: CommAlg.Polymatroid.LinearQuotients\n"

/-! ## Source: CommAlg.Polymatroid.LinearQuotients -/
section CheckedSource92

/-! # Actual linear quotients of polymatroidal monomial ideals

The colon ideal is the ordinary ideal quotient in the polynomial ring, and
its generators are actual variables. The coefficient calculation proves that
no non-monomial elements are lost in the passage to exponent divisibility.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {k : Type*} [CommSemiring k]

theorem mem_monomialIdeal_colon_iff (B : Family V) (b : Exponent V)
    (f : MvPolynomial V k) :
    f ∈ (monomialIdeal k B).colon {MvPolynomial.monomial b 1} ↔
      ∀ a ∈ f.support, Contains B (a + b) := by
  rw [Submodule.mem_colon_singleton, smul_eq_mul, mem_monomialIdeal_iff]
  constructor
  · intro h a ha
    apply h
    simpa only [MvPolynomial.mem_support_iff, MvPolynomial.coeff_mul_monomial,
      mul_one] using (MvPolynomial.mem_support_iff.mp ha)
  · intro h c hc
    have hc' := MvPolynomial.mem_support_iff.mp hc
    have hbc : b ≤ c := by
      by_contra hbc
      rw [MvPolynomial.coeff_mul_monomial', if_neg hbc] at hc'
      exact hc' rfl
    have ha : c - b ∈ f.support := by
      rw [MvPolynomial.mem_support_iff]
      simpa only [MvPolynomial.coeff_mul_monomial', if_pos hbc, mul_one] using hc'
    have hh := h (c - b) ha
    rwa [tsub_add_cancel_of_le hbc] at hh

/-- The ideal generated by the indicated polynomial variables. -/
def variableIdeal (C : Finset V) : Ideal (MvPolynomial V k) :=
  Ideal.span (MvPolynomial.X '' (C : Set V))

theorem variableIdeal_eq_monomialIdeal (C : Finset V) :
    variableIdeal (k := k) C =
      monomialIdeal k (C.image (fun j => Finsupp.single j 1)) := by
  unfold variableIdeal monomialIdeal
  apply congrArg Ideal.span
  ext f
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨Finsupp.single j 1, mem_image.mpr ⟨j, hj, rfl⟩, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨j, hj, rfl⟩ := mem_image.mp ha
    exact ⟨j, hj, rfl⟩

theorem contains_variableFamily_iff (C : Finset V) (a : Exponent V) :
    Contains (C.image (fun j => Finsupp.single j 1)) a ↔
      ∃ j ∈ C, 0 < a j := by
  constructor
  · rintro ⟨b, hb, hba⟩
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hb
    refine ⟨j, hj, ?_⟩
    have := hba j
    simpa only [Finsupp.single_eq_same, Nat.succ_le_iff] using this
  · rintro ⟨j, hj, haj⟩
    refine ⟨Finsupp.single j 1, mem_image.mpr ⟨j, hj, rfl⟩, ?_⟩
    intro x
    by_cases hx : x = j
    · subst x
      simpa using (show 1 ≤ a j by omega)
    · simp [Finsupp.single_apply, hx, Ne.symm hx]

theorem mem_variableIdeal_iff (C : Finset V) (f : MvPolynomial V k) :
    f ∈ variableIdeal (k := k) C ↔
      ∀ a ∈ f.support, ∃ j ∈ C, 0 < a j := by
  rw [variableIdeal_eq_monomialIdeal, mem_monomialIdeal_iff]
  simp_rw [contains_variableFamily_iff]

/-- The exact reverse-lexicographic linear quotient of every polymatroidal
family. This includes the first generator, whose colon has no variables. -/
theorem revlex_colon_eq_variableIdeal {B : Family V} (hB : ExchangeAxiom B)
    {b : Exponent V} (hb : b ∈ B) :
    (monomialIdeal k (revlexBeforeFamily B b)).colon {MvPolynomial.monomial b 1} =
      variableIdeal (k := k) (revlexColonVariables B b) := by
  ext f
  rw [mem_monomialIdeal_colon_iff, mem_variableIdeal_iff]
  simp_rw [contains_revlexBefore_add_iff hB hb]

/-- The form with the principal ideal in the denominator. -/
theorem revlex_colon_span_eq_variableIdeal {B : Family V} (hB : ExchangeAxiom B)
    {b : Exponent V} (hb : b ∈ B) :
    (monomialIdeal k (revlexBeforeFamily B b)).colon
        (Ideal.span {MvPolynomial.monomial b (1 : k)}) =
      variableIdeal (k := k) (revlexColonVariables B b) := by
  rw [Ideal.colon_span, revlex_colon_eq_variableIdeal hB hb]

theorem rankBases_revlex_colon_eq (g : RankFunction V)
    {b : Exponent V} (hb : b ∈ rankBases g) :
    (monomialIdeal k (revlexBeforeFamily (rankBases g) b)).colon
        {MvPolynomial.monomial b 1} =
      variableIdeal (k := k) (revlexColonVariables (rankBases g) b) :=
  revlex_colon_eq_variableIdeal (rankBases_polymatroidal g).2 hb

end CommAlg.Polymatroid

end
end CheckedSource92

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "93: CommAlg.ProjectiveDimension.KoszulBound\n"

/-! ## Source: CommAlg.ProjectiveDimension.KoszulBound -/
section CheckedSource93

/-!
# Actual projective-dimension bounds from the finite Koszul resolution

These are bounds on Mathlib's Ext-defined projective dimension. No residue-Tor
vanishing criterion or local-ring hypothesis is used for the upper bound.
-/

noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

namespace CommAlg.ProjectiveDimension

universe u v w

theorem le_of_resolution {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    {X : C} (P : ProjectiveResolution X) (N : ℕ)
    (h : ∀ n, N < n → IsZero (P.complex.X n)) :
    projectiveDimension X ≤ N := by
  rw [projectiveDimension_le_iff]
  apply HasProjectiveDimensionLT.mk
  intro n hn Y e
  obtain ⟨f, hf, rfl⟩ := P.extMk_surjective e (n + 1) rfl
  have hf0 : f = 0 := (h n (by omega)).eq_of_src _ _
  subst f
  exact P.extMk_zero (n + 1) rfl

variable {R : Type u} [CommRing R]

theorem exteriorPower_fin_isZero (m n : ℕ) (h : m < n) :
    IsZero (ModuleCat.of R (⋀[R]^n (Fin m → R))) := by
  letI : IsEmpty (Set.powersetCard (Fin m) n) := ⟨fun s => by
    have hc := Finset.card_le_univ s.val
    have he : s.val.card = n := s.property
    simp only [Fintype.card_fin] at hc
    omega⟩
  haveI : Subsingleton (⋀[R]^n (Fin m → R)) := ⟨fun x y =>
    ((Pi.basisFun R (Fin m)).exteriorPower n).repr.injective (Subsingleton.elim _ _)⟩
  exact ModuleCat.isZero_iff_subsingleton.mpr inferInstance

theorem regularSequence_quotient_le (l : List R)
    (hl : RingTheory.Sequence.IsRegular R l) :
    projectiveDimension (ModuleCat.of R (R ⧸ Ideal.ofList l)) ≤ l.length := by
  letI := HasExt.standard (ModuleCat.{u} R)
  apply le_of_resolution (CommAlg.Koszul.regularSequenceResolution l hl) l.length
  intro n hn
  change IsZero (ModuleCat.of R (⋀[R]^n (Fin l.length → R)))
  exact exteriorPower_fin_isZero l.length n hn

variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

theorem variableIdeal_quotient_le (A : Finset V) :
    projectiveDimension
      (ModuleCat.of (MvPolynomial V k)
        (MvPolynomial V k ⧸ CommAlg.Polymatroid.variableIdeal (k := k) A)) ≤ A.card := by
  let l : List (MvPolynomial V k) := A.toList.map MvPolynomial.X
  have hreg := CommAlg.Koszul.variables_regular (k := k) A.toList A.nodup_toList
  have he : Ideal.ofList l = CommAlg.Polymatroid.variableIdeal (k := k) A := by
    apply congrArg Ideal.span
    ext f
    simp [l, CommAlg.Polymatroid.variableIdeal]
  have h := regularSequence_quotient_le l hreg
  have hlen : l.length = A.card := by simp [l]
  rw [he, hlen] at h
  exact h

end CommAlg.ProjectiveDimension

end
end CheckedSource93

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "94: CommAlg.ProjectiveDimension.IdealGeneratorExact\n"

/-! ## Source: CommAlg.ProjectiveDimension.IdealGeneratorExact -/
section CheckedSource94

/-! # The exact sequence for adjoining one ideal generator

For every commutative ring, this constructs the literal short exact sequence
`0 → J → J + (m) → R/(J:m) → 0`. No regularity assumption on `m` is needed.
-/

noncomputable section

namespace CommAlg

open Classical CategoryTheory

variable {R : Type*} [CommRing R]

def generatorExtension (J : Ideal R) (m : R) : Ideal R := J ⊔ Ideal.span {m}

def generatorSubmodule (J : Ideal R) (m : R) : Submodule R (generatorExtension J m) :=
  Submodule.comap (generatorExtension J m).subtype (J : Submodule R R)

abbrev generatorQuotient (J : Ideal R) (m : R) :=
  generatorExtension J m ⧸ generatorSubmodule J m

def mulToGeneratorExtension (J : Ideal R) (m : R) : R →ₗ[R] generatorExtension J m where
  toFun r := ⟨r * m, (show Ideal.span {m} ≤ generatorExtension J m from le_sup_right)
    (Ideal.mem_span_singleton'.mpr ⟨r, rfl⟩)⟩
  map_add' r s := Subtype.ext (add_mul r s m)
  map_smul' r s := Subtype.ext (by simp [mul_assoc])

def generatorQuotientMap (J : Ideal R) (m : R) : R →ₗ[R] generatorQuotient J m :=
  (generatorSubmodule J m).mkQ.comp (mulToGeneratorExtension J m)

theorem generatorQuotientMap_ker (J : Ideal R) (m : R) :
    LinearMap.ker (generatorQuotientMap J m) = J.colon {m} := by
  ext r
  simp only [LinearMap.mem_ker, generatorQuotientMap, LinearMap.comp_apply,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_colon_singleton,
    smul_eq_mul]
  rfl

theorem generatorQuotientMap_surjective (J : Ideal R) (m : R) :
    Function.Surjective (generatorQuotientMap J m) := by
  intro q
  obtain ⟨x, rfl⟩ := (generatorSubmodule J m).mkQ_surjective q
  obtain ⟨y, hy, z, hz, he⟩ := Submodule.mem_sup.mp x.property
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hz
  refine ⟨r, ?_⟩
  apply (Submodule.Quotient.eq _).mpr
  change r * m - x.val ∈ J
  rw [← he, ← hr]
  simpa using J.neg_mem hy

/-- The actual quotient by the previously generated ideal is the quotient by
the ordinary colon ideal. -/
def generatorQuotientEquiv (J : Ideal R) (m : R) :
    generatorQuotient J m ≃ₗ[R] R ⧸ J.colon {m} :=
  (LinearMap.quotKerEquivOfSurjective (generatorQuotientMap J m)
    (generatorQuotientMap_surjective J m)).symm.trans
      (Submodule.quotEquivOfEq _ _ (generatorQuotientMap_ker J m))

def generatorInclusion (J : Ideal R) (m : R) : J →ₗ[R] generatorExtension J m :=
  Submodule.inclusion le_sup_left

def generatorProjection (J : Ideal R) (m : R) :
    generatorExtension J m →ₗ[R] R ⧸ J.colon {m} :=
  (generatorQuotientEquiv J m).toLinearMap.comp (generatorSubmodule J m).mkQ

@[simp] theorem generatorProjection_eq_zero_iff (J : Ideal R) (m : R)
    (x : generatorExtension J m) : generatorProjection J m x = 0 ↔ x.val ∈ J := by
  change (generatorQuotientEquiv J m) ((generatorSubmodule J m).mkQ x) = 0 ↔ _
  rw [(generatorQuotientEquiv J m).map_eq_zero_iff]
  exact Submodule.Quotient.mk_eq_zero _

theorem generatorProjection_comp_inclusion (J : Ideal R) (m : R) :
    (generatorProjection J m).comp (generatorInclusion J m) = 0 := by
  ext x
  apply (generatorProjection_eq_zero_iff J m _).mpr
  exact x.property

/-- The genuine categorical exact sequence used for induction along a linear
quotient ordering. -/
def generatorExact (J : Ideal R) (m : R) : ShortComplex (ModuleCat R) :=
  ShortComplex.moduleCatMk (generatorInclusion J m) (generatorProjection J m)
    (generatorProjection_comp_inclusion J m)

theorem generatorExact_shortExact (J : Ideal R) (m : R) :
    (generatorExact J m).ShortExact := by
  unfold generatorExact
  apply ModuleCat.shortComplex_shortExact
  · change Function.Exact (generatorInclusion J m) (generatorProjection J m)
    intro x
    rw [generatorProjection_eq_zero_iff]
    constructor
    · intro hx
      exact ⟨⟨x.val, hx⟩, Subtype.ext rfl⟩
    · rintro ⟨y, rfl⟩
      exact y.property
  · change Function.Injective (generatorInclusion J m)
    intro x y hxy
    exact Subtype.ext (congrArg (fun z : generatorExtension J m => z.val) hxy)
  · exact (generatorQuotientEquiv J m).surjective.comp
      (generatorSubmodule J m).mkQ_surjective

/-- The projective-dimension bound has exactly the two terms needed in the
linear-quotient induction. -/
theorem generatorExtension_projectiveDimension_le (J : Ideal R) (m : R) :
    projectiveDimension (ModuleCat.of R (generatorExtension J m)) ≤
      projectiveDimension (ModuleCat.of R J) ⊔
        projectiveDimension (ModuleCat.of R (R ⧸ J.colon {m})) :=
  (generatorExact_shortExact J m).projectiveDimension_X₂_le_sup

end CommAlg

end
end CheckedSource94

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "95: CommAlg.Polymatroid.HomogenizedRank\n"

/-! ## Source: CommAlg.Polymatroid.HomogenizedRank -/
section CheckedSource95

/-! # Homogenization of ranks with ordered marginal increments

`none` denotes the additional coordinate `z`; `some j` denotes an original
coordinate.  Both branches of the rank formula are proved for every subset.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def rankGap (g u : RankFunction V) : ℕ := u univ - g univ

theorem RankFunction.gap_bound {g u : RankFunction V} (h : u.Dominates g)
    (A : Finset V) : u A ≤ rankGap g u + g A := by
  have hE := RankFunction.le_of_dominates h univ
  have hm := h A univ (subset_univ A)
  unfold rankGap
  omega

def homogenizedRankValue (g u : RankFunction V) (A : Finset (Option V)) : ℕ :=
  if none ∈ A then rankGap g u + g A.eraseNone else u A.eraseNone

/-- The second interpolation in Lemma 3.3, on the ground set extended by one
genuine new coordinate. -/
def RankFunction.homogenize (g u : RankFunction V) (h : u.Dominates g) :
    RankFunction (Option V) where
  toFun := homogenizedRankValue g u
  empty := by simp [homogenizedRankValue]
  monotone := by
    intro A B hAB
    have hm : A.eraseNone ⊆ B.eraseNone := Finset.eraseNone.monotone hAB
    by_cases hA : none ∈ A
    · have hB := hAB hA
      simp only [homogenizedRankValue, if_pos hA, if_pos hB]
      exact Nat.add_le_add_left (g.monotone hm) _
    · by_cases hB : none ∈ B
      · simp only [homogenizedRankValue, if_neg hA, if_pos hB]
        exact (RankFunction.gap_bound h A.eraseNone).trans
          (Nat.add_le_add_left (g.monotone hm) _)
      · simp only [homogenizedRankValue, if_neg hA, if_neg hB]
        exact u.monotone hm
  submodular := by
    intro A B
    have hg := g.submodular A.eraseNone B.eraseNone
    have hu := u.submodular A.eraseNone B.eraseNone
    have hm := RankFunction.mixed_submodular h A.eraseNone B.eraseNone
    have hm' := RankFunction.mixed_submodular h B.eraseNone A.eraseNone
    rw [Finset.union_comm B.eraseNone A.eraseNone,
      Finset.inter_comm B.eraseNone A.eraseNone] at hm'
    by_cases hA : none ∈ A <;> by_cases hB : none ∈ B <;>
      simp [homogenizedRankValue, hA, hB] <;> omega

@[simp] theorem RankFunction.homogenize_apply (g u : RankFunction V)
    (h : u.Dominates g) (A : Finset (Option V)) :
    g.homogenize u h A = homogenizedRankValue g u A := rfl

@[simp] theorem RankFunction.homogenize_some (g u : RankFunction V)
    (h : u.Dominates g) (A : Finset V) :
    g.homogenize u h (A.image some) = u A := by
  simp [homogenizedRankValue]

@[simp] theorem RankFunction.homogenize_insertNone (g u : RankFunction V)
    (h : u.Dominates g) (A : Finset V) :
    g.homogenize u h A.insertNone = rankGap g u + g A := by
  simp [homogenizedRankValue]

@[simp] theorem RankFunction.homogenize_singleton_none (g u : RankFunction V)
    (h : u.Dominates g) :
    g.homogenize u h {none} = rankGap g u := by
  simp [homogenizedRankValue]

@[simp] theorem RankFunction.homogenize_univ (g u : RankFunction V)
    (h : u.Dominates g) :
    g.homogenize u h univ = u univ := by
  have hg := RankFunction.le_of_dominates h univ
  have he : (univ : Finset (Option V)).eraseNone = univ := by ext x; simp
  simp [homogenizedRankValue, he, rankGap, Nat.sub_add_cancel hg]

end CommAlg.Polymatroid

end
end CheckedSource95

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "96: CommAlg.Polymatroid.HomogenizedBases\n"

/-! ## Source: CommAlg.Polymatroid.HomogenizedBases -/
section CheckedSource96

/-! # Homogenizing all homological-shift rank ideals

The extra variable is `none`. The results below identify every base of the
homogenized rank, and then identify the actual polynomial ideal generated by
all the powers of this variable times the renamed shift ideals. No topological
or homological support is built into the definition of these rank ideals.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

@[simp] theorem subsetSum_image_some (e : Exponent (Option V)) (A : Finset V) :
    subsetSum e (A.image some) = subsetSum e.some A := by
  unfold subsetSum
  rw [Finset.sum_image]
  · rfl
  · intro x hx y hy hxy
    exact Option.some.inj hxy

@[simp] theorem subsetSum_insertNone (e : Exponent (Option V)) (A : Finset V) :
    subsetSum e A.insertNone = e none + subsetSum e.some A := by
  exact Finset.sum_insertNone e A

theorem degree_option (e : Exponent (Option V)) :
    e.degree = e none + e.some.degree := by
  rw [← subsetSum_univ, univ_option, subsetSum_insertNone, subsetSum_univ]

@[simp] theorem degree_optionElim (a : Exponent V) (z : ℕ) :
    (a.optionElim z).degree = z + a.degree := by
  rw [degree_option]
  simp

theorem upperFeasible_homogenize_iff (g u : RankFunction V) (h : u.Dominates g)
    (e : Exponent (Option V)) :
    UpperFeasible (g.homogenize u h) e ↔
      UpperFeasible u e.some ∧
        ∀ A, e none + subsetSum e.some A ≤ rankGap g u + g A := by
  constructor
  · intro he
    constructor
    · intro A
      simpa only [subsetSum_image_some, RankFunction.homogenize_some] using he (A.image some)
    · intro A
      simpa only [subsetSum_insertNone, RankFunction.homogenize_insertNone] using he A.insertNone
  · rintro ⟨hu, hg⟩ C
    by_cases hC : none ∈ C
    · have hEq : C.eraseNone.insertNone = C := by
        rw [Finset.insertNone_eraseNone, Finset.insert_eq_of_mem hC]
      rw [← hEq, subsetSum_insertNone, RankFunction.homogenize_insertNone]
      exact hg _
    · have hEq : C.eraseNone.image some = C := by
        rw [Finset.image_some_eraseNone, Finset.erase_eq_of_notMem hC]
      rw [← hEq, subsetSum_image_some, RankFunction.homogenize_some]
      exact hu _

/-- The rank function occurring in Theorem 5.1, including ranks with loops. -/
def homogenizedShiftRank (g : RankFunction V) : RankFunction (Option V) :=
  g.homogenize (universalAugmentedRank g) (universalAugmentedRank_dominates g)

/-- Its degree excess over the original ideal, eventually identified with the
projective dimension by the genuine Tor support theorem. -/
def shiftLength (g : RankFunction V) : ℕ := rankGap g (universalAugmentedRank g)

theorem shiftLength_add_degree (g : RankFunction V) :
    shiftLength g + g univ = universalAugmentedRank g univ := by
  exact Nat.sub_add_cancel
    (RankFunction.le_of_dominates (universalAugmentedRank_dominates g) univ)

theorem isRankBase_homogenizedShift_iff (g : RankFunction V)
    (e : Exponent (Option V)) :
    IsRankBase (homogenizedShiftRank g) e ↔
      ∃ i ≤ shiftLength g, ∃ a ∈ rankShiftFamily g i,
        e = a.optionElim (shiftLength g - i) := by
  constructor
  · rintro ⟨hdeg, he⟩
    have hsplit := (upperFeasible_homogenize_iff g (universalAugmentedRank g)
      (universalAugmentedRank_dominates g) e).mp he
    have hz : e none ≤ shiftLength g := by
      have hz := hsplit.2 ∅
      simpa [shiftLength] using hz
    have htotal : e none + e.some.degree = shiftLength g + g univ := by
      rw [← degree_option, hdeg]
      exact (RankFunction.homogenize_univ g _ _).trans (shiftLength_add_degree g).symm
    refine ⟨shiftLength g - e none, Nat.sub_le _ _, e.some, ?_, ?_⟩
    · rw [mem_rankShiftFamily_iff]
      refine ⟨by omega, ?_⟩
      intro A
      by_cases hA : A = ∅
      · simp [hA]
      · rw [universalHomologicalRank_apply g _ (Finset.nonempty_iff_ne_empty.mpr hA)]
        have hb := hsplit.2 A
        change e none + subsetSum e.some A ≤ shiftLength g + g A at hb
        exact le_min (by omega) (hsplit.1 A)
    · have hez : shiftLength g - (shiftLength g - e none) = e none := by omega
      rw [hez, Finsupp.optionElim_some]
  · rintro ⟨i, hi, a, ha, rfl⟩
    obtain ⟨haDeg, haBound⟩ := (mem_rankShiftFamily_iff g i a).mp ha
    constructor
    · rw [degree_optionElim, haDeg]
      change shiftLength g - i + (g univ + i) =
        g.homogenize (universalAugmentedRank g) (universalAugmentedRank_dominates g) univ
      rw [RankFunction.homogenize_univ, ← shiftLength_add_degree]
      omega
    · change UpperFeasible (g.homogenize (universalAugmentedRank g)
        (universalAugmentedRank_dominates g)) _
      rw [upperFeasible_homogenize_iff]
      simp only [Finsupp.some_optionElim, Finsupp.optionElim_apply_none]
      constructor
      · intro A
        exact (haBound A).trans
          (shiftRankValue_le_u g (universalAugmentedRank g) i A)
      · intro A
        have hb := (haBound A).trans (universalHomologicalRank_le_add g i A)
        change shiftLength g - i + subsetSum a A ≤ shiftLength g + g A
        omega

theorem rankBases_homogenizedShift (g : RankFunction V) :
    rankBases (homogenizedShiftRank g) =
      (Finset.range (shiftLength g + 1)).biUnion (fun i =>
        (rankShiftFamily g i).image (fun a => a.optionElim (shiftLength g - i))) := by
  ext e
  simp only [mem_rankBases, isRankBase_homogenizedShift_iff,
    Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Nat.lt_succ_iff]
  constructor
  · rintro ⟨i, hi, a, ha, he⟩
    exact ⟨i, hi, a, ha, he.symm⟩
  · rintro ⟨i, hi, a, ha, he⟩
    exact ⟨i, hi, a, ha, he.symm⟩

end CommAlg.Polymatroid

end
end CheckedSource96

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "97: CommAlg.Polymatroid.RevlexColonCardinality\n"

/-! ## Source: CommAlg.Polymatroid.RevlexColonCardinality -/
section CheckedSource97

/-! # Bounding every actual linear quotient by the homological rank gap

For a base `b`, add one to each colon variable. The resulting exponent obeys
the full partition inequalities. The key strict inequality on a nonempty set
of colon variables follows by choosing its largest variable: a legal transfer
into that variable must have its donor still larger.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [LinearOrder V]

@[simp] theorem subsetSum_faceExponent (C A : Finset V) :
    subsetSum (Koszul.faceExponent C) A = (A ∩ C).card := by
  simp [subsetSum, Koszul.faceExponent_apply, ← Finset.sum_filter]

@[simp] theorem degree_faceExponent (C : Finset V) :
    (Koszul.faceExponent C).degree = C.card := by
  rw [← subsetSum_univ, subsetSum_faceExponent, univ_inter]

def revlexColonWitness (B : Family V) (b : Exponent V) : Exponent V :=
  b + Koszul.faceExponent (revlexColonVariables B b)

/-- A nonempty set of colon variables cannot be tight at the current base. -/
theorem rankBase_strict_on_colon_subset (g : RankFunction V)
    {b : Exponent V} (hb : b ∈ rankBases g) {A : Finset V} (hA : A.Nonempty)
    (hAC : A ⊆ revlexColonVariables (rankBases g) b) : subsetSum b A < g A := by
  have hbound := ((mem_rankBases g b).mp hb).2 A
  by_contra hbad
  have htight : subsetSum b A = g A := by omega
  let j := A.max' hA
  have hjA : j ∈ A := A.max'_mem hA
  obtain ⟨i, hji, hbi, hex⟩ :=
    (mem_revlexColonVariables (rankBases g) b j).mp (hAC hjA)
  have hiA : i ∈ A := by
    by_contra hiA
    have hs := subsetSum_exchange b i j hbi A
    rw [if_neg hiA, if_pos hjA] at hs
    have hc := ((mem_rankBases g _).mp hex).2 A
    omega
  exact (not_lt_of_ge (A.le_max' i hiA)) hji

theorem revlexColonWitness_subset_bound (g : RankFunction V)
    {b : Exponent V} (hb : b ∈ rankBases g) {A : Finset V} (hA : A.Nonempty) :
    subsetSum (revlexColonWitness (rankBases g) b) A ≤ g A + A.card - 1 := by
  rw [revlexColonWitness, subsetSum_add, subsetSum_faceExponent]
  have hbA := ((mem_rankBases g b).mp hb).2 A
  have hc : (A ∩ revlexColonVariables (rankBases g) b).card ≤ A.card :=
    card_le_card inter_subset_left
  by_cases hAC : A ⊆ revlexColonVariables (rankBases g) b
  · have hlt := rankBase_strict_on_colon_subset g hb hA hAC
    omega
  · have hlt : (A ∩ revlexColonVariables (rankBases g) b).card < A.card := by
      by_contra h
      have he : A ∩ revlexColonVariables (rankBases g) b = A :=
        eq_of_subset_of_card_le inter_subset_left (by omega)
      apply hAC
      rw [← he]
      exact inter_subset_right
    omega

theorem revlexColonWitness_upperFeasible (g : RankFunction V)
    {b : Exponent V} (hb : b ∈ rankBases g) :
    UpperFeasible (universalAugmentedRank g) (revlexColonWitness (rankBases g) b) :=
  (universal_bounds_iff g _).mp (fun _ hA => revlexColonWitness_subset_bound g hb hA)

/-- The size of each genuine colon generating set is bounded by the exact
partition-rank gap. There is no activity hypothesis. -/
theorem revlexColonVariables_card_le_shiftLength (g : RankFunction V)
    {b : Exponent V} (hb : b ∈ rankBases g) :
    (revlexColonVariables (rankBases g) b).card ≤ shiftLength g := by
  have h := revlexColonWitness_upperFeasible g hb univ
  rw [subsetSum_univ, revlexColonWitness, map_add, degree_faceExponent,
    ((mem_rankBases g b).mp hb).1] at h
  have hp := shiftLength_add_degree g
  omega

/-- The same construction is a base in the exact shift layer of the colon
cardinality, which later gives a genuine Tor nonvanishing witness. -/
theorem revlexColonWitness_mem_shiftFamily (g : RankFunction V)
    {b : Exponent V} (hb : b ∈ rankBases g) :
    revlexColonWitness (rankBases g) b ∈
      rankShiftFamily g (revlexColonVariables (rankBases g) b).card := by
  rw [mem_rankShiftFamily_iff]
  constructor
  · rw [revlexColonWitness, map_add, degree_faceExponent, ((mem_rankBases g b).mp hb).1]
  · intro A
    by_cases hA : A = ∅
    · simp [hA]
    rw [universalHomologicalRank_apply g _ (nonempty_iff_ne_empty.mpr hA)]
    refine le_min ?_ (revlexColonWitness_upperFeasible g hb A)
    rw [revlexColonWitness, subsetSum_add, subsetSum_faceExponent]
    exact Nat.add_le_add (((mem_rankBases g b).mp hb).2 A)
      (card_le_card inter_subset_right)

end CommAlg.Polymatroid

end
end CheckedSource97

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "98: CommAlg.ProjectiveDimension.RankIdealUpper\n"

/-! ## Source: CommAlg.ProjectiveDimension.RankIdealUpper -/
section CheckedSource98

/-!
# Actual projective dimension: the upper bound from linear quotients

Finite induction follows initial segments of the genuine reverse lexicographic
order. The quotient at each step is the actual quotient by its colon ideal.
-/

noncomputable section

namespace CommAlg.ProjectiveDimension

open Classical Finset CategoryTheory CategoryTheory.Limits CommAlg.Polymatroid

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

theorem exists_revlex_greatest (C : Family V) (hC : C.Nonempty) :
    ∃ b ∈ C, ∀ a ∈ C, a = b ∨ RevlexBefore a b := by
  induction C using Finset.induction_on with
  | empty => simp at hC
  | @insert b C hb ih =>
    by_cases hne : C.Nonempty
    · obtain ⟨c, hc, hmax⟩ := ih hne
      by_cases hbc : b = c
      · refine ⟨c, mem_insert_of_mem hc, ?_⟩
        intro a ha
        rcases mem_insert.mp ha with rfl | ha
        · exact Or.inl hbc
        · exact hmax a ha
      rcases revlexBefore_total hbc with hbc | hcb
      · refine ⟨c, mem_insert_of_mem hc, ?_⟩
        intro a ha
        rcases mem_insert.mp ha with rfl | ha
        · exact Or.inr hbc
        · exact hmax a ha
      · refine ⟨b, mem_insert_self _ _, ?_⟩
        intro a ha
        rcases mem_insert.mp ha with rfl | ha
        · exact Or.inl rfl
        · rcases hmax a ha with rfl | hac
          · exact Or.inr hcb
          · exact Or.inr (revlexBefore_trans hac hcb)
    · have he := not_nonempty_iff_eq_empty.mp hne
      subst C
      exact ⟨b, by simp, fun a ha => Or.inl (by simpa using ha)⟩

theorem monomialIdeal_insert_generator (C : Family V) (b : Exponent V) :
    monomialIdeal k (insert b C) =
      CommAlg.generatorExtension (monomialIdeal k C) (MvPolynomial.monomial b 1) := by
  simp [monomialIdeal, CommAlg.generatorExtension,
    Ideal.span_insert, sup_comm]

/-- Every initial segment has projective dimension bounded by the final
partition-rank gap. The proof uses actual short exact module sequences. -/
theorem initialSegment_projectiveDimension_le (g : RankFunction V) (C : Family V)
    (hCB : C ⊆ rankBases g)
    (hdown : ∀ a ∈ C, ∀ b ∈ rankBases g, RevlexBefore b a → b ∈ C) :
    projectiveDimension (ModuleCat.of (MvPolynomial V k) (monomialIdeal k C)) ≤
      shiftLength g := by
  induction C using Finset.strongInductionOn with
  | _ C ih =>
    by_cases hne : C.Nonempty
    · obtain ⟨b, hb, hmax⟩ := exists_revlex_greatest C hne
      let D := C.erase b
      have hDC : D ⊂ C := erase_ssubset hb
      have hDB : D ⊆ rankBases g := (erase_subset _ _).trans hCB
      have hDdown : ∀ a ∈ D, ∀ c ∈ rankBases g, RevlexBefore c a → c ∈ D := by
        intro a ha c hc hca
        obtain ⟨hab, haC⟩ := mem_erase.mp ha
        apply mem_erase.mpr
        refine ⟨?_, hdown a haC c hc hca⟩
        intro hcb
        subst c
        rcases hmax a haC with he | habefore
        · exact hab he
        · exact revlexBefore_asymm habefore hca
      have hDpd := ih D hDC hDB hDdown
      have hDeq : D = revlexBeforeFamily (rankBases g) b := by
        ext a
        constructor
        · intro ha
          obtain ⟨hab, haC⟩ := mem_erase.mp ha
          refine (mem_revlexBeforeFamily _ _ _).mpr ⟨hCB haC, ?_⟩
          exact (hmax a haC).resolve_left hab
        · intro ha
          obtain ⟨haB, hab⟩ := (mem_revlexBeforeFamily _ _ _).mp ha
          apply mem_erase.mpr
          refine ⟨?_, hdown b hb a haB hab⟩
          intro he
          subst a
          exact revlexBefore_irrefl b hab
      have hcolon : (monomialIdeal k D).colon {MvPolynomial.monomial b 1} =
          variableIdeal (k := k) (revlexColonVariables (rankBases g) b) := by
        rw [hDeq]
        exact rankBases_revlex_colon_eq g (hCB hb)
      have hquot : projectiveDimension
          (ModuleCat.of (MvPolynomial V k)
            (MvPolynomial V k ⧸ (monomialIdeal k D).colon {MvPolynomial.monomial b 1})) ≤
          shiftLength g := by
        rw [hcolon]
        exact (variableIdeal_quotient_le _).trans
          (by exact_mod_cast revlexColonVariables_card_le_shiftLength g (hCB hb))
      have he : monomialIdeal k C =
          CommAlg.generatorExtension (monomialIdeal k D) (MvPolynomial.monomial b 1) := by
        have hIns : insert b D = C := insert_erase hb
        calc
          monomialIdeal k C = monomialIdeal k (insert b D) :=
            congrArg (monomialIdeal k) hIns.symm
          _ = _ := monomialIdeal_insert_generator D b
      rw [he]
      exact (CommAlg.generatorExtension_projectiveDimension_le _ _).trans (sup_le hDpd hquot)
    · have he : C = ∅ := not_nonempty_iff_eq_empty.mp hne
      subst C
      have he0 : monomialIdeal k (∅ : Family V) = ⊥ := by simp [monomialIdeal]
      haveI : Subsingleton (monomialIdeal k (∅ : Family V)) := by
        rw [he0]
        infer_instance
      have hz : IsZero (ModuleCat.of (MvPolynomial V k) (monomialIdeal k (∅ : Family V))) :=
        ModuleCat.isZero_iff_subsingleton.mpr inferInstance
      rw [(projectiveDimension_eq_bot_iff _).mpr hz]
      exact bot_le

/-- The actual Ext-defined projective dimension of every polymatroid rank
ideal is at most the universal partition-rank gap, including loops and rank zero. -/
theorem rankIdeal_projectiveDimension_le (g : RankFunction V) :
    projectiveDimension (ModuleCat.of (MvPolynomial V k) (rankIdeal k g)) ≤
      shiftLength g :=
  initialSegment_projectiveDimension_le g (rankBases g) le_rfl
    (fun _ _ _ hb _ => hb)

end CommAlg.ProjectiveDimension

end
end CheckedSource98

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "99: CommAlg.KoszulComplex.CoefficientProjectiveDimension\n"

/-! ## Source: CommAlg.KoszulComplex.CoefficientProjectiveDimension -/
section CheckedSource99

/-! # Genuine projective-dimension detection by coefficient Koszul homology

This proves the needed vanishing theorem directly from a projective presentation and
its homology long exact sequence. No balance theorem for `Tor` and `Tor'` is assumed.
-/

noncomputable section
set_option maxHeartbeats 300000
set_option maxRecDepth 2500
namespace CommAlg.Koszul
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
universe u
variable {R : Type u} [CommRing R]

/-- Tensor a fixed chain complex with a variable coefficient module. -/
def tensorCoefficientFunctor (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    ModuleCat.{u} R ⥤ ChainComplex (ModuleCat.{u} R) ℕ where
  obj M := (((tensoringRight (ModuleCat R)).obj M).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj K
  map f := (((tensoringRight (ModuleCat R)).map f).mapHomologicalComplex
    (ComplexShape.down ℕ)).app K
  map_id M := by simp
  map_comp f g := by simp

instance tensorCoefficientFunctor_preservesZero (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    (tensorCoefficientFunctor K).PreservesZeroMorphisms where
  map_zero X Y := by
    apply HomologicalComplex.Hom.ext
    funext i
    change (tensorLeft (K.X i)).map (0 : X ⟶ Y) = 0
    exact Functor.map_zero _ _ _

/-- Flat chain groups preserve short exact coefficient sequences degree by degree. -/
lemma tensorCoefficient_shortExact (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (hflat : ∀ i, Module.Flat R (K.X i)) (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) : (S.map (tensorCoefficientFunctor K)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  letI : Module.Flat R (K.X i) := hflat i
  change (S.map (tensorLeft (K.X i))).ShortExact
  letI : Mono S.f := hS.mono_f
  letI : Epi S.g := hS.epi_g
  refine ShortComplex.ShortExact.mk'
    (Module.Flat.lTensor_shortComplex_exact (K.X i) S hS.exact) ?_ ?_
  · apply (ModuleCat.mono_iff_injective _).mpr
    exact Module.Flat.lTensor_preserves_injective_linearMap (M := K.X i) S.f.hom
      ((ModuleCat.mono_iff_injective S.f).mp hS.mono_f)
  · apply (ModuleCat.epi_iff_surjective _).mpr
    exact LinearMap.lTensor_surjective (K.X i)
      ((ModuleCat.epi_iff_surjective S.g).mp hS.epi_g)

/-- Tensoring an exact positive-degree complex with a projective coefficient module preserves exactness. -/
lemma tensorCoefficient_isZero_of_projective
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (hexact : ∀ i, K.ExactAt (i + 1))
    (M : ModuleCat.{u} R) [Projective M] (i : ℕ) :
    IsZero (((tensorCoefficientFunctor K).obj M).homology (i + 1)) := by
  letI : Module.Flat R M := inferInstance
  apply HomologicalComplex.ExactAt.isZero_homology
  change ((K.sc (i + 1)).map (tensorRight M)).Exact
  exact Module.Flat.rTensor_shortComplex_exact M (K.sc (i + 1)) (hexact i)

/-- If the actual projective dimension is below `n`, coefficient homology vanishes in degree `n`.
The induction uses actual projective presentations and actual homology connecting maps. -/
lemma tensorCoefficient_isZero_of_hasProjectiveDimensionLT
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (hflat : ∀ i, Module.Flat R (K.X i)) (hexact : ∀ i, K.ExactAt (i + 1))
    (n : ℕ) (M : ModuleCat.{u} R) (hM : HasProjectiveDimensionLT M n) :
    IsZero (((tensorCoefficientFunctor K).obj M).homology n) := by
  induction n generalizing M with
  | zero =>
      have hz : IsZero M := (hasProjectiveDimensionLT_zero_iff_isZero M).mp hM
      exact (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) 0).map_isZero
        ((tensorCoefficientFunctor K).map_isZero hz)
  | succ n ih =>
      cases n with
      | zero =>
          letI : Projective M := projective_iff_hasProjectiveDimensionLT_one.mpr hM
          exact tensorCoefficient_isZero_of_projective K hexact M 0
      | succ n =>
          let ⟨p⟩ := EnoughProjectives.presentation M
          let S := ShortComplex.mk (kernel.ι p.f) p.f (kernel.condition p.f)
          have hS : S.ShortExact := { exact := ShortComplex.exact_kernel p.f }
          have hKer : HasProjectiveDimensionLT S.X₁ (n + 1) :=
            (hS.hasProjectiveDimensionLT_X₃_iff n inferInstance).mp hM
          have hleft := tensorCoefficient_isZero_of_projective K hexact S.X₂ (n + 1)
          have hright := ih S.X₁ hKer
          have ht := tensorCoefficient_shortExact K hflat S hS
          have he := ht.homology_exact₃ (n + 2) (n + 1) (by rfl)
          exact he.isZero_X₂ (hleft.eq_of_src _ _) (hright.eq_of_tgt _ _)

/-- Nonzero coefficient homology supplies a lower bound for Mathlib's actual projective dimension. -/
lemma tensorCoefficient_nonzero_le_projectiveDimension
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (hflat : ∀ i, Module.Flat R (K.X i)) (hexact : ∀ i, K.ExactAt (i + 1))
    (M : ModuleCat.{u} R) (n : ℕ)
    (h : ¬ IsZero (((tensorCoefficientFunctor K).obj M).homology n)) :
    (n : WithBot ℕ∞) ≤ projectiveDimension M := by
  rw [projectiveDimension_ge_iff]
  exact fun hM => h (tensorCoefficient_isZero_of_hasProjectiveDimensionLT K hflat hexact n M hM)

variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]

/-- Genuine coefficient Koszul homology cannot occur above the actual projective dimension. -/
lemma familyCoefficient_nonzero_le_projectiveDimension
    (M : ModuleCat.{u} (MvPolynomial V k)) (n : ℕ)
    (h : ¬ IsZero ((familyCoefficientComplex (MvPolynomial.X : V → MvPolynomial V k) M).homology n)) :
    (n : WithBot ℕ∞) ≤ projectiveDimension M := by
  apply tensorCoefficient_nonzero_le_projectiveDimension
    (koszulComplex (Fintype.linearCombination (MvPolynomial V k) MvPolynomial.X))
    (fun i => by
      change Module.Flat (MvPolynomial V k) (⋀[MvPolynomial V k]^i (V → MvPolynomial V k))
      infer_instance) ?_ M n h
  intro i
  exact (koszulComplex.exactAt_of_isRegular
    (finiteVariableList (V := V) (k := k)) finite_variables_regular (i + 1) (by omega)).of_iso
    finiteVariableKoszulIso

/-- The same bound for Mathlib's actual first-factor derived Tor module. -/
lemma finitePolynomialTor_nonzero_le_projectiveDimension
    (M : ModuleCat.{u} (MvPolynomial V k)) (n : ℕ)
    (h : ¬ IsZero (finitePolynomialTor n M)) :
    (n : WithBot ℕ∞) ≤ projectiveDimension M := by
  apply familyCoefficient_nonzero_le_projectiveDimension M n
  exact fun hz => h ((finitePolynomialTorIso n M).isZero_iff.mpr hz)

end CommAlg.Koszul

end
end CheckedSource99

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "100: CommAlg.ProjectiveDimension.RankIdeal\n"

/-! ## Source: CommAlg.ProjectiveDimension.RankIdeal -/
section CheckedSource100

/-!
# The actual projective dimension of a polymatroidal ideal

The upper bound is obtained from actual linear-quotient exact sequences.
The lower bound uses a nonzero multigraded component of Mathlib's derived
tensor functor and the proved coefficient-complex dimension-shift theorem.
Neither projective dimension nor Tor nonvanishing is defined by the rank formula.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem rankShiftFamily_nonempty_iff_le_shiftLength (g : RankFunction V) (i : ℕ) :
    (rankShiftFamily g i).Nonempty ↔ i ≤ shiftLength g := by
  rw [rankShiftFamily_nonempty_iff]
  have hd := shiftLength_add_degree g
  by_cases hE : (univ : Finset V).Nonempty
  · rw [universalHomologicalRank_apply g i hE]
    omega
  · have he : (univ : Finset V) = ∅ := not_nonempty_iff_eq_empty.mp hE
    simp only [he, RankFunction.map_empty] at hd ⊢
    omega

theorem top_rankShiftFamily_nonempty (g : RankFunction V) :
    (rankShiftFamily g (shiftLength g)).Nonempty :=
  (rankShiftFamily_nonempty_iff_le_shiftLength g _).mpr le_rfl

end CommAlg.Polymatroid

namespace CommAlg.ProjectiveDimension

open Classical Finset CategoryTheory CategoryTheory.Limits CommAlg.Polymatroid

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

/-- The exact categorical projective dimension, including the unit ideal and loops. -/
theorem rankIdeal_projectiveDimension (g : RankFunction V) :
    projectiveDimension (ModuleCat.of (MvPolynomial V k) (rankIdeal k g)) =
      (shiftLength g : WithBot ℕ∞) := by
  apply le_antisymm (rankIdeal_projectiveDimension_le g)
  obtain ⟨a, ha⟩ := top_rankShiftFamily_nonempty g
  have hβ := (gradedBettiNonzero_rankBases_iff (k := k) g a (shiftLength g)).mpr ha
  exact Koszul.finitePolynomialTor_nonzero_le_projectiveDimension _ _
    (Koszul.derivedTor_nonzero_of_graded _ _ _ hβ)

/-- The same statement for an actual polynomial ideal with its proved rank presentation. -/
theorem polymatroidalIdeal_projectiveDimension (I : Ideal (MvPolynomial V k))
    (g : RankFunction V) (hI : I = rankIdeal k g) :
    projectiveDimension (ModuleCat.of (MvPolynomial V k) I) =
      (shiftLength g : WithBot ℕ∞) := by
  subst I
  exact rankIdeal_projectiveDimension g

end CommAlg.ProjectiveDimension

end
end CheckedSource100

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "101: CommAlg.ProjectiveDimension.PowerFormula\n"

/-! ## Source: CommAlg.ProjectiveDimension.PowerFormula -/
section CheckedSource101

/-! # Corollary 4.3: exact projective dimensions of powers

The left-hand side is Mathlib's categorical projective dimension of the
actual polynomial ideal. The minimum ranges over every set partition.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem shiftLength_active_defect (g : RankFunction V) (hg : g.Active) :
    shiftLength g =
      finiteMinimum (fun P : Finpartition (univ : Finset V) =>
        partitionDefect g P + partitionSlack P) := by
  have h := shiftLength_add_degree g
  rw [universalAugmentedRank_eq_active g hg,
    augmentedPartitionRank_defect g hg] at h
  omega

theorem shiftLength_scale_partition (ρ : RankFunction V) (hρ : ρ.Active)
    (s : ℕ) (hs : 1 ≤ s) :
    shiftLength (ρ.scale s) =
      finiteMinimum (fun P : Finpartition (univ : Finset V) =>
        s * partitionDefect ρ P + partitionSlack P) := by
  rw [shiftLength_active_defect _ (hρ.scale hs)]
  simp only [partitionDefect_scale]

theorem partitionMinimum_eq_eventual (ρ : RankFunction V) (s : ℕ)
    (hs : eventualOffset ρ (univ : Finset V) ≤ s) :
    finiteMinimum (fun P : Finpartition (univ : Finset V) =>
      s * partitionDefect ρ P + partitionSlack P) = eventualOffset ρ univ := by
  apply le_antisymm
  · obtain ⟨P, hd, hb⟩ := eventualOffset_attained ρ (univ : Finset V)
    simpa only [hd, hb, Nat.mul_zero, Nat.zero_add] using
      finiteMinimum_le (fun P : Finpartition (univ : Finset V) =>
        s * partitionDefect ρ P + partitionSlack P) P
  · apply le_finiteMinimum
    intro P
    by_cases hd : partitionDefect ρ P = 0
    · exact (eventualOffset_le_slack ρ P hd).trans (Nat.le_add_left _ _)
    · have hpos : 1 ≤ partitionDefect ρ P := by omega
      nlinarith

theorem shiftLength_scale_eventual (ρ : RankFunction V) (hρ : ρ.Active)
    (s : ℕ) (hs : max 1 (eventualOffset ρ univ) ≤ s) :
    shiftLength (ρ.scale s) = eventualOffset ρ univ := by
  rw [shiftLength_scale_partition ρ hρ s ((le_max_left _ _).trans hs)]
  exact partitionMinimum_eq_eventual ρ s ((le_max_right _ _).trans hs)

end CommAlg.Polymatroid

namespace CommAlg.ProjectiveDimension

open Classical Finset CategoryTheory CommAlg.Polymatroid

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

/-- Formula (4.3), with no additional restriction on the number of variables or powers. -/
theorem rankIdeal_power_projectiveDimension (ρ : RankFunction V) (hρ : ρ.Active)
    (s : ℕ) (hs : 1 ≤ s) :
    projectiveDimension (ModuleCat.of (MvPolynomial V k) ↥((rankIdeal k ρ) ^ s)) =
      (finiteMinimum (fun P : Finpartition (univ : Finset V) =>
        s * partitionDefect ρ P + partitionSlack P) : WithBot ℕ∞) := by
  rw [← rankIdeal_scale, rankIdeal_projectiveDimension,
    shiftLength_scale_partition ρ hρ s hs]

/-- The eventual projective dimension is attained by the paper's stated uniform bound. -/
theorem rankIdeal_power_projectiveDimension_eventual (ρ : RankFunction V) (hρ : ρ.Active)
    (s : ℕ) (hs : max 1 (eventualOffset ρ univ) ≤ s) :
    projectiveDimension (ModuleCat.of (MvPolynomial V k) ↥((rankIdeal k ρ) ^ s)) =
      (eventualOffset ρ univ : WithBot ℕ∞) := by
  rw [← rankIdeal_scale, rankIdeal_projectiveDimension,
    shiftLength_scale_eventual ρ hρ s hs]

/-- Literal ideal form of Corollary 4.3 for any proved rank presentation. -/
theorem polymatroidal_power_projectiveDimension (I : Ideal (MvPolynomial V k))
    (ρ : RankFunction V) (hI : I = rankIdeal k ρ) (hρ : ρ.Active)
    (s : ℕ) (hs : 1 ≤ s) :
    projectiveDimension (ModuleCat.of (MvPolynomial V k) ↥(I ^ s)) =
      (finiteMinimum (fun P : Finpartition (univ : Finset V) =>
        s * partitionDefect ρ P + partitionSlack P) : WithBot ℕ∞) := by
  subst I
  exact rankIdeal_power_projectiveDimension ρ hρ s hs

theorem polymatroidal_power_projectiveDimension_eventual (I : Ideal (MvPolynomial V k))
    (ρ : RankFunction V) (hI : I = rankIdeal k ρ) (hρ : ρ.Active)
    (s : ℕ) (hs : max 1 (eventualOffset ρ univ) ≤ s) :
    projectiveDimension (ModuleCat.of (MvPolynomial V k) ↥(I ^ s)) =
      (eventualOffset ρ univ : WithBot ℕ∞) := by
  subst I
  exact rankIdeal_power_projectiveDimension_eventual ρ hρ s hs

end CommAlg.ProjectiveDimension

end
end CheckedSource101

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "102: CommAlg.Polymatroid.PowerShiftGenerators\n"

/-! ## Source: CommAlg.Polymatroid.PowerShiftGenerators -/
section CheckedSource102

/-! # Exact degrees of the minimal monomial generators of the actual Rees ideal -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V k : Type*} [Fintype V] [DecidableEq V] [CommRing k] [Nontrivial k]

theorem exists_monomial_generator_notMem_iff (B : Family V)
    (J : Ideal (MvPolynomial V k)) (hJ : J ≤ monomialIdeal k B) :
    (∃ a ∈ B, MvPolynomial.monomial a (1 : k) ∉ J) ↔ J ≠ monomialIdeal k B := by
  constructor
  · rintro ⟨a, ha, hn⟩ he
    apply hn
    rw [he]
    exact Ideal.subset_span ⟨a, ha, rfl⟩
  · intro h
    by_contra hn
    push_neg at hn
    apply h
    apply le_antisymm hJ
    apply Ideal.span_le.mpr
    rintro f ⟨a, ha, rfl⟩
    exact hn a ha

theorem preceding_powerShift_product_le (ρ : RankFunction V) (i : ℕ)
    {s : ℕ} (hs : 0 < s) :
    rankIdeal k ρ * powerShiftPiece ρ i (s - 1) ≤ powerShiftPiece ρ i s := by
  have h := powerShiftPiece_action (k := k) ρ i 1 (s - 1)
  simpa only [pow_one, Nat.add_sub_of_le hs] using h

theorem exists_minimalShiftRees_iff (ρ : RankFunction V) (i : ℕ)
    {s : ℕ} (hs : 0 < s) :
    (∃ a, IsMinimalShiftReesMonomial (k := k) ρ i s a) ↔
      rankIdeal k ρ * powerShiftPiece ρ i (s - 1) ≠ powerShiftPiece ρ i s := by
  simp_rw [minimalShiftRees_iff ρ i hs]
  have he : powerShiftPiece (k := k) ρ i s =
      monomialIdeal k (rankShiftFamily (RankFunction.scale s ρ) i) := by
    rw [powerShiftPiece_pos ρ i hs, rankShiftIdeal_eq_monomialIdeal]
  rw [he]
  exact exists_monomial_generator_notMem_iff _ _
    (he ▸ preceding_powerShift_product_le ρ i hs)

theorem powerShiftPiece_eq_bot_before (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) (hi : i ≤ eventualOffset ρ univ) {s : ℕ}
    (hs : s < powerThreshold ρ i univ) : powerShiftPiece (k := k) ρ i s = ⊥ := by
  by_cases hs0 : s = 0
  · simp [hs0]
  · rw [powerShiftPiece_pos ρ i (by omega)]
    by_contra hn
    have hr := (powerShiftIdeal_ne_bot_iff_threshold ρ hρ i hi (by omega)).mp hn
    omega

theorem powerShiftPiece_ne_bot_at (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) (hi0 : 0 < i) (hi : i ≤ eventualOffset ρ univ) :
    powerShiftPiece (k := k) ρ i (powerThreshold ρ i univ) ≠ ⊥ := by
  have hr := powerThreshold_pos ρ hi0 hi
  rw [powerShiftPiece_pos ρ i hr]
  exact (powerShiftIdeal_ne_bot_iff_threshold ρ hρ i hi hr).mpr le_rfl

/-- Theorem 4.4's exact interval, for semantic minimal monomials of the genuine
Rees ideal. Every degree in the interval occurs and every other degree is absent. -/
theorem minimalShiftRees_degree_iff (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) (hi0 : 0 < i) (hi : i ≤ eventualOffset ρ univ) (s : ℕ) :
    (∃ a, IsMinimalShiftReesMonomial (k := k) ρ i s a) ↔
      powerThreshold ρ i univ ≤ s ∧ s ≤ globalPowerThreshold ρ i := by
  have hr : 1 ≤ powerThreshold ρ i univ := powerThreshold_pos ρ hi0 hi
  have hrS := powerThreshold_le_global ρ i univ
  by_cases hs0 : s = 0
  · subst s
    constructor
    · rintro ⟨a, ha⟩
      have hp := minimalShiftRees_positive ha
      omega
    · omega
  have hs : 0 < s := by omega
  rw [exists_minimalShiftRees_iff ρ i hs]
  by_cases hsr : s < powerThreshold ρ i univ
  · have hz := powerShiftPiece_eq_bot_before (k := k) ρ hρ i hi hsr
    have hp : rankIdeal k ρ * powerShiftPiece ρ i (s - 1) = ⊥ := by
      apply le_antisymm _ bot_le
      exact hz ▸ preceding_powerShift_product_le ρ i hs
    rw [hz, hp]
    constructor
    · intro h
      exact (h rfl).elim
    · intro h
      omega
  by_cases hsrEq : s = powerThreshold ρ i univ
  · have hp : powerShiftPiece (k := k) ρ i (s - 1) = ⊥ :=
      powerShiftPiece_eq_bot_before ρ hρ i hi (by omega)
    have hn : powerShiftPiece (k := k) ρ i s ≠ ⊥ := by
      rw [hsrEq]
      exact powerShiftPiece_ne_bot_at ρ hρ i hi0 hi
    rw [hp, Ideal.mul_bot]
    constructor
    · intro _
      omega
    · intro _ he
      exact hn he.symm
  have hprev : 1 ≤ s - 1 := by omega
  have hprevr : powerThreshold ρ i univ ≤ s - 1 := by omega
  have he := powerShiftIdeal_mul_eq_iff (k := k) ρ hρ i hi hprev hprevr
  rw [powerShiftPiece_pos ρ i hprev, powerShiftPiece_pos ρ i hs]
  have hsucc : s - 1 + 1 = s := by omega
  rw [hsucc] at he
  simp only [ne_eq, he]
  omega

theorem powerShiftPiece_eq_bot_of_above (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) (hi : eventualOffset ρ univ < i) (s : ℕ) :
    powerShiftPiece (k := k) ρ i s = ⊥ := by
  by_cases hs : s = 0
  · simp [hs]
  · rw [powerShiftPiece_pos ρ i (by omega)]
    exact powerShiftIdeal_eq_bot_of_above ρ hρ i hi (by omega)

/-- Above the eventual projective-dimension offset the entire actual Rees
ideal, and therefore its graded module, is zero. -/
theorem shiftReesIdeal_eq_bot_of_above (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) (hi : eventualOffset ρ univ < i) : shiftReesIdeal (k := k) ρ i = ⊥ := by
  apply bot_unique
  intro p hp
  change p = 0
  apply Subtype.ext
  apply Polynomial.ext
  intro s
  have h := hp s
  rw [powerShiftPiece_eq_bot_of_above ρ hρ i hi s] at h
  simpa using h

/-- The endpoints satisfy all of the quantitative bounds in Theorem 4.4. -/
theorem powerShift_generator_endpoints (ρ : RankFunction V) (i : ℕ)
    (hi0 : 0 < i) (hi : i ≤ eventualOffset ρ univ) :
    1 ≤ powerThreshold ρ i univ ∧
      powerThreshold ρ i univ ≤ globalPowerThreshold ρ i ∧
      globalPowerThreshold ρ i ≤ i :=
  ⟨powerThreshold_pos ρ hi0 hi, powerThreshold_le_global ρ i univ,
    globalPowerThreshold_le ρ i⟩

end CommAlg.Polymatroid

end
end CheckedSource102

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "103: CommAlg.Polymatroid.PowerShiftSpanning\n"

/-! ## Source: CommAlg.Polymatroid.PowerShiftSpanning -/
section CheckedSource103

/-! # Minimal Rees monomials really generate the coefficientwise ideal -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V k : Type*} [Fintype V] [DecidableEq V] [CommRing k] [Nontrivial k]

def minimalShiftReesSet (ρ : RankFunction V) (i : ℕ) : Set (reesAlgebra (rankIdeal k ρ)) :=
  {p | ∃ s a, ∃ h : IsMinimalShiftReesMonomial (k := k) ρ i s a,
    p = shiftReesMonomial ρ i s a h.1}

theorem shiftReesMonomial_mem_span_minimal (ρ : RankFunction V) (i s : ℕ)
    (a : Exponent V) (ha : MvPolynomial.monomial a (1 : k) ∈ powerShiftPiece ρ i s) :
    shiftReesMonomial ρ i s a ha ∈ Ideal.span (minimalShiftReesSet ρ i) := by
  generalize hn : s + a.degree = n
  induction n using Nat.strong_induction_on generalizing s a with
  | h n ih =>
    by_cases hmin : IsMinimalShiftReesMonomial (k := k) ρ i s a
    · exact Ideal.subset_span ⟨s, a, hmin, rfl⟩
    · have hnmin : ¬ ∀ r b, r ≤ s → b ≤ a →
          MvPolynomial.monomial b (1 : k) ∈ powerShiftPiece ρ i r →
          MvPolynomial.monomial (a - b) (1 : k) ∈ (rankIdeal k ρ) ^ (s - r) →
          r = s ∧ b = a := fun h => hmin ⟨ha, h⟩
      push_neg at hnmin
      obtain ⟨r, b, hrs, hba, hb, hf, hne⟩ := hnmin
      have hd := degree_mono hba
      have hmeasure : r + b.degree < n := by
        by_contra hbad
        have heR : r = s := by omega
        have heD : b.degree = a.degree := by omega
        exact hne heR (eq_of_le_of_degree_eq hba heD)
      have hbSpan := ih (r + b.degree) hmeasure r b hb rfl
      let q : reesAlgebra (rankIdeal k ρ) :=
        ⟨Polynomial.monomial (s - r) (MvPolynomial.monomial (a - b) 1),
          reesAlgebra.monomial_mem.mpr hf⟩
      have he : q * shiftReesMonomial ρ i r b hb = shiftReesMonomial ρ i s a ha := by
        apply Subtype.ext
        exact rees_monomial_factorization hrs hba
      rw [← he]
      exact Ideal.mul_mem_left _ q hbSpan

def liftReesCoefficient (ρ : RankFunction V) (s : ℕ) (f : MvPolynomial V k)
    (hf : f ∈ (rankIdeal k ρ) ^ s) : reesAlgebra (rankIdeal k ρ) :=
  ⟨Polynomial.monomial s f, reesAlgebra.monomial_mem.mpr hf⟩

theorem liftReesCoefficient_mem_of_bases (ρ : RankFunction V) (i : ℕ)
    {s : ℕ} (hs : 0 < s) (J : Ideal (reesAlgebra (rankIdeal k ρ)))
    (hgen : ∀ a ∈ rankShiftFamily (RankFunction.scale s ρ) i,
      ∀ ha : MvPolynomial.monomial a (1 : k) ∈ (rankIdeal k ρ) ^ s,
        liftReesCoefficient ρ s (MvPolynomial.monomial a 1) ha ∈ J)
    (f : MvPolynomial V k) (hf : f ∈ powerShiftPiece ρ i s)
    (hfPow : f ∈ (rankIdeal k ρ) ^ s) : liftReesCoefficient ρ s f hfPow ∈ J := by
  have hpiece : powerShiftPiece (k := k) ρ i s =
      monomialIdeal k (rankShiftFamily (RankFunction.scale s ρ) i) := by
    rw [powerShiftPiece_pos ρ i hs, rankShiftIdeal_eq_monomialIdeal]
  have hbound : monomialIdeal k (rankShiftFamily (RankFunction.scale s ρ) i) ≤
      (rankIdeal k ρ) ^ s := hpiece ▸ powerShiftPiece_le_pow ρ i s
  rw [hpiece] at hf
  suffices h : ∀ f, f ∈ monomialIdeal k (rankShiftFamily (RankFunction.scale s ρ) i) →
      ∀ hfPow, liftReesCoefficient ρ s f hfPow ∈ J from h f hf hfPow
  intro f hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, ha, rfl⟩ := hf
    exact hgen a ha
  | zero =>
    intro hzero
    have he : liftReesCoefficient ρ s 0 hzero = 0 := by
      apply Subtype.ext
      simp [liftReesCoefficient]
    simpa only [he] using J.zero_mem
  | add x y hx hy ihx ihy =>
    intro hxy
    have he : liftReesCoefficient ρ s (x + y) hxy =
        liftReesCoefficient ρ s x (hbound hx) + liftReesCoefficient ρ s y (hbound hy) := by
      apply Subtype.ext
      simp [liftReesCoefficient]
    rw [he]
    exact J.add_mem (ihx _) (ihy _)
  | smul r x hx ih =>
    intro hrx
    have he : liftReesCoefficient ρ s (r • x) hrx =
        algebraMap (MvPolynomial V k) (reesAlgebra (rankIdeal k ρ)) r *
          liftReesCoefficient ρ s x (hbound hx) := by
      apply Subtype.ext
      change Polynomial.monomial s (r * x) = Polynomial.C r * Polynomial.monomial s x
      rw [Polynomial.C_mul_monomial]
    rw [he]
    exact J.mul_mem_left _ (ih _)

/-- Every polynomial element of the Rees ideal is generated by its genuine
minimal monomials. This proves actual module generation, in addition to the
combinatorial degree characterization. -/
theorem shiftReesIdeal_eq_span_minimal (ρ : RankFunction V) (i : ℕ) :
    shiftReesIdeal (k := k) ρ i = Ideal.span (minimalShiftReesSet ρ i) := by
  apply le_antisymm
  · intro p hp
    rw [reesAlgebra.as_sum_support p]
    apply Ideal.sum_mem
    intro s hs
    change liftReesCoefficient ρ s (p.val.coeff s) (p.property s) ∈ _
    by_cases hs0 : s = 0
    · have hz := hp s
      rw [hs0, powerShiftPiece_zero] at hz
      have hf0 : p.val.coeff 0 = 0 := hz
      have he : liftReesCoefficient ρ s (p.val.coeff s) (p.property s) = 0 := by
        apply Subtype.ext
        simp [liftReesCoefficient, hs0, hf0]
      rw [he]
      exact Ideal.zero_mem _
    · apply liftReesCoefficient_mem_of_bases ρ i (by omega) _ _ _ (hp s)
      intro a ha haPow
      have hmem : MvPolynomial.monomial a (1 : k) ∈ powerShiftPiece ρ i s := by
        rw [powerShiftPiece_pos ρ i (by omega), rankShiftIdeal_eq_monomialIdeal,
          monomial_mem_iff]
        exact ⟨a, ha, le_rfl⟩
      exact shiftReesMonomial_mem_span_minimal ρ i s a hmem
  · apply Ideal.span_le.mpr
    rintro p ⟨s, a, ha, rfl⟩
    exact shiftReesMonomial_mem ρ i s a ha.1

def boundedShiftReesSet (ρ : RankFunction V) (i q : ℕ) : Set (reesAlgebra (rankIdeal k ρ)) :=
  {p | ∃ s a, ∃ ha : MvPolynomial.monomial a (1 : k) ∈ powerShiftPiece ρ i s,
    s ≤ q ∧ p = shiftReesMonomial ρ i s a ha}

/-- The exact endpoint is an actual generation bound in the Rees algebra. -/
theorem shiftReesIdeal_generated_at_threshold (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) (hi0 : 0 < i) (hi : i ≤ eventualOffset ρ univ) :
    shiftReesIdeal (k := k) ρ i =
      Ideal.span (boundedShiftReesSet ρ i (globalPowerThreshold ρ i)) := by
  apply le_antisymm
  · rw [shiftReesIdeal_eq_span_minimal]
    apply Ideal.span_mono
    rintro p ⟨s, a, ha, rfl⟩
    have hs := ((minimalShiftRees_degree_iff ρ hρ i hi0 hi s).mp ⟨a, ha⟩).2
    exact ⟨s, a, ha.1, hs, rfl⟩
  · apply Ideal.span_le.mpr
    rintro p ⟨s, a, ha, _, rfl⟩
    exact shiftReesMonomial_mem ρ i s a ha

end CommAlg.Polymatroid

end
end CheckedSource103

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "104: CommAlg.Polymatroid.PowerShiftLeastGeneration\n"

/-! ## Source: CommAlg.Polymatroid.PowerShiftLeastGeneration -/
section CheckedSource104

/-!
# The exact threshold is the least actual Rees generation bound

A coefficient of a minimal module monomial cannot be created by multiplying
module elements in which that coefficient is zero. This gives an intrinsic
obstruction to generation in any smaller Rees degrees.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V k : Type*} [Fintype V] [DecidableEq V] [CommRing k] [Nontrivial k]

theorem monomial_mem_powerShiftPiece_of_coeff (ρ : RankFunction V) (i s : ℕ)
    {f : MvPolynomial V k} (hf : f ∈ powerShiftPiece ρ i s) {a : Exponent V}
    (ha : f.coeff a ≠ 0) : MvPolynomial.monomial a (1 : k) ∈ powerShiftPiece ρ i s := by
  by_cases hs : s = 0
  · simp only [hs, powerShiftPiece_zero, Submodule.mem_bot] at hf
    simp [hf] at ha
  · rw [powerShiftPiece_pos ρ i (by omega)] at hf ⊢
    exact (mem_rankShiftIdeal_iff_coeff _ _ f).mp hf a (MvPolynomial.mem_support_iff.mpr ha)

theorem monomial_mem_rankIdeal_power_of_coeff (ρ : RankFunction V) (s : ℕ)
    {f : MvPolynomial V k} (hf : f ∈ (rankIdeal k ρ) ^ s) {a : Exponent V}
    (ha : f.coeff a ≠ 0) : MvPolynomial.monomial a (1 : k) ∈ (rankIdeal k ρ) ^ s := by
  rw [← rankIdeal_scale] at hf ⊢
  exact (monomial_mem_iff (rankBases (RankFunction.scale s ρ)) a).mpr
    ((mem_monomialIdeal_iff _ f).mp hf a (MvPolynomial.mem_support_iff.mpr ha))

def reesCoefficient (ρ : RankFunction V) (s : ℕ) (a : Exponent V)
    (p : reesAlgebra (rankIdeal k ρ)) : k := (p.val.coeff s).coeff a

@[simp] theorem reesCoefficient_zero (ρ : RankFunction V) (s : ℕ) (a : Exponent V) :
    reesCoefficient (k := k) ρ s a 0 = 0 := by simp [reesCoefficient]

@[simp] theorem reesCoefficient_add (ρ : RankFunction V) (s : ℕ) (a : Exponent V)
    (p q : reesAlgebra (rankIdeal k ρ)) :
    reesCoefficient ρ s a (p + q) = reesCoefficient ρ s a p + reesCoefficient ρ s a q := by
  simp [reesCoefficient]

theorem minimalShiftRees_coefficient_mul_zero (ρ : RankFunction V) (i s : ℕ)
    (a : Exponent V) (hmin : IsMinimalShiftReesMonomial (k := k) ρ i s a)
    (p : reesAlgebra (rankIdeal k ρ)) (hp : p ∈ shiftReesIdeal ρ i)
    (hz : reesCoefficient ρ s a p = 0) (r : reesAlgebra (rankIdeal k ρ)) :
    reesCoefficient ρ s a (r * p) = 0 := by
  change ((r.val * p.val).coeff s).coeff a = 0
  rw [Polynomial.coeff_mul, MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  rintro ⟨n, t⟩ hnt
  have hntEq : n + t = s := mem_antidiagonal.mp hnt
  rw [MvPolynomial.coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨c, b⟩ hcb
  have hcbEq : c + b = a := mem_antidiagonal.mp hcb
  by_cases hr : (r.val.coeff n).coeff c = 0
  · simp [hr]
  by_cases hpb : (p.val.coeff t).coeff b = 0
  · simp [hpb]
  have hrMon := monomial_mem_rankIdeal_power_of_coeff ρ n (r.property n) hr
  have hpMon := monomial_mem_powerShiftPiece_of_coeff ρ i t (hp t) hpb
  have hba : b ≤ a := hcbEq ▸ le_add_left le_rfl
  have hquot : MvPolynomial.monomial (a - b) (1 : k) ∈ (rankIdeal k ρ) ^ (s - t) := by
    have haSub : a - b = c := by rw [← hcbEq, add_tsub_cancel_right]
    rw [haSub, show s - t = n by omega]
    exact hrMon
  obtain ⟨ht, hb⟩ := hmin.2 t b (by omega) hba hpMon hquot
  subst t
  subst b
  exact (hpb hz).elim

theorem coefficient_zero_on_span_bounded (ρ : RankFunction V) (i s q : ℕ)
    (a : Exponent V) (hmin : IsMinimalShiftReesMonomial (k := k) ρ i s a)
    (hqs : q < s) (p : reesAlgebra (rankIdeal k ρ))
    (hp : p ∈ Ideal.span (boundedShiftReesSet ρ i q)) :
    reesCoefficient ρ s a p = 0 := by
  have h : p ∈ shiftReesIdeal ρ i ∧ reesCoefficient ρ s a p = 0 := by
    induction hp using Submodule.span_induction with
    | mem p hp =>
      obtain ⟨t, b, hb, ht, rfl⟩ := hp
      refine ⟨shiftReesMonomial_mem ρ i t b hb, ?_⟩
      have hst : s ≠ t := by omega
      simp [reesCoefficient, shiftReesMonomial, Polynomial.coeff_monomial, hst, Ne.symm hst]
    | zero => exact ⟨Ideal.zero_mem _, by simp⟩
    | add p r hp hr ihp ihr =>
      exact ⟨Ideal.add_mem _ ihp.1 ihr.1, by simp [ihp.2, ihr.2]⟩
    | smul r p hp ih =>
      exact ⟨Ideal.mul_mem_left _ r ih.1,
        minimalShiftRees_coefficient_mul_zero ρ i s a hmin p ih.1 ih.2 r⟩
  exact h.2

/-- No lower-degree monomial generating set can generate a minimal monomial
in a larger Rees degree. The obstruction is a literal polynomial coefficient. -/
theorem minimalShiftRees_notMem_span_bounded (ρ : RankFunction V) (i s q : ℕ)
    (a : Exponent V) (hmin : IsMinimalShiftReesMonomial (k := k) ρ i s a)
    (hqs : q < s) :
    shiftReesMonomial ρ i s a hmin.1 ∉ Ideal.span (boundedShiftReesSet ρ i q) := by
  intro hp
  have hz := coefficient_zero_on_span_bounded ρ i s q a hmin hqs _ hp
  simpa [reesCoefficient, shiftReesMonomial] using hz

/-- Theorem 4.4's exact least generation bound, stated as equality with an
actual ideal span in the ordinary Rees algebra. -/
theorem shiftReesIdeal_generation_bound_iff (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) (hi0 : 0 < i) (hi : i ≤ eventualOffset ρ univ) (q : ℕ) :
    shiftReesIdeal (k := k) ρ i = Ideal.span (boundedShiftReesSet ρ i q) ↔
      globalPowerThreshold ρ i ≤ q := by
  constructor
  · intro he
    by_contra hq
    have hq' : q < globalPowerThreshold ρ i := by omega
    obtain ⟨a, ha⟩ := (minimalShiftRees_degree_iff (k := k) ρ hρ i hi0 hi
      (globalPowerThreshold ρ i)).mpr ⟨powerThreshold_le_global ρ i univ, le_rfl⟩
    have hp := shiftReesMonomial_mem ρ i (globalPowerThreshold ρ i) a ha.1
    rw [he] at hp
    exact minimalShiftRees_notMem_span_bounded ρ i _ q a ha hq' hp
  · intro hq
    apply le_antisymm
    · rw [shiftReesIdeal_generated_at_threshold ρ hρ i hi0 hi]
      apply Ideal.span_mono
      rintro p ⟨s, a, ha, hs, rfl⟩
      exact ⟨s, a, ha, hs.trans hq, rfl⟩
    · apply Ideal.span_le.mpr
      rintro p ⟨s, a, ha, _, rfl⟩
      exact shiftReesMonomial_mem ρ i s a ha

end CommAlg.Polymatroid

end
end CheckedSource104

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "105: CommAlg.Polymatroid.PowerShiftNewGenerators\n"

/-! ## Source: CommAlg.Polymatroid.PowerShiftNewGenerators -/
section CheckedSource105

/-! # The explicit inequalities selecting new minimal Rees generators -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V k : Type*} [Fintype V] [DecidableEq V] [CommRing k] [Nontrivial k]

/-- The post-Theorem-4.4 criterion identifies each individual new generator,
not only the degrees in which generators exist. -/
theorem minimalShiftRees_iff_rank_violation (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) (hi0 : 0 < i) (hi : i ≤ eventualOffset ρ univ) (s : ℕ)
    (hrs : powerThreshold ρ i univ < s) (a : Exponent V)
    (ha : a ∈ rankShiftFamily (ρ.scale s) i) :
    IsMinimalShiftReesMonomial (k := k) ρ i s a ↔
      ∃ A : Finset V, A.Nonempty ∧
        s * ρ A + powerCorrection ρ i (s - 1) A < subsetSum a A := by
  have hr := powerThreshold_pos ρ hi0 hi
  have hs : 0 < s := by omega
  have hs1 : 1 ≤ s - 1 := by omega
  have hprev : (rankShiftFamily (ρ.scale (s - 1)) i).Nonempty :=
    (powerShiftFamily_nonempty_iff_threshold ρ hρ i hi hs1).mpr (by omega)
  have htotal := (rankShiftFamily_nonempty_iff _ _).mp hprev
  let g := ρ.add (universalHomologicalRank (ρ.scale (s - 1)) i)
  have hdeg : a.degree = g univ := by
    have haD := rankShiftFamily_equigenerated (ρ.scale s) i a ha
    change a.degree = ρ univ + universalHomologicalRank (ρ.scale (s - 1)) i univ
    rw [htotal]
    change a.degree = ρ univ + ((s - 1) * ρ univ + i)
    change a.degree = s * ρ univ + i at haD
    have hss : s - 1 + 1 = s := by omega
    nlinarith
  have hprod : rankIdeal k ρ * powerShiftPiece ρ i (s - 1) = rankIdeal k g := by
    rw [powerShiftPiece_pos ρ i hs1, rankShiftIdeal, if_pos htotal, ← rankIdeal_add]
  have hg (A : Finset V) : g A = s * ρ A + powerCorrection ρ i (s - 1) A := by
    change ρ A + universalHomologicalRank (ρ.scale (s - 1)) i A = _
    rw [power_homologicalRank ρ hρ i hs1]
    have hss : s - 1 + 1 = s := by omega
    nlinarith
  rw [minimalShiftRees_iff ρ i hs a, and_iff_right ha, hprod,
    monomial_mem_rankIdeal_iff, ← upperFeasible_iff_lowerFeasible g hdeg]
  change (¬ ∀ A, subsetSum a A ≤ g A) ↔ _
  constructor
  · intro hn
    obtain ⟨A, hA⟩ := not_forall.mp hn
    have hne : A.Nonempty := by
      by_contra h
      have he := not_nonempty_iff_eq_empty.mp h
      simp [he] at hA
    exact ⟨A, hne, by simpa [hg A] using Nat.lt_of_not_ge hA⟩
  · rintro ⟨A, _, hA⟩ hb
    have h := hb A
    rw [hg] at h
    omega

end CommAlg.Polymatroid

end
end CheckedSource105

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "106: CommAlg.Polymatroid.HomologicalInterval\n"

/-! ## Source: CommAlg.Polymatroid.HomologicalInterval -/
section CheckedSource106

/-!
# Theorem 4.4 for genuine homological shifts in the ordinary Rees algebra

All module pieces below are the homological shifts defined by the nonzero
multigraded components of the actual derived tensor functor. Minimality means
minimality under divisibility by actual Rees monomials, including degree-zero
polynomial factors. Generation is an equality of actual ideal spans.
-/

noncomputable section

namespace CommAlg

open Classical Finset Polymatroid

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]

def IsMinimalHomologicalPowerMonomial (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i s : ℕ) (a : Exponent V) : Prop :=
  MvPolynomial.monomial a (1 : k) ∈ homologicalPowerPiece I hI i s ∧
    ∀ r b, r ≤ s → b ≤ a →
      MvPolynomial.monomial b (1 : k) ∈ homologicalPowerPiece I hI i r →
      MvPolynomial.monomial (a - b) (1 : k) ∈ I ^ (s - r) →
      r = s ∧ b = a

/-- The actual module monomials through a specified Rees degree. -/
def boundedHomologicalPowerMonomials (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i q : ℕ) : Set (reesAlgebra I) :=
  {p | ∃ s a, MvPolynomial.monomial a (1 : k) ∈ homologicalPowerPiece I hI i s ∧
    s ≤ q ∧ p.val = Polynomial.monomial s (MvPolynomial.monomial a 1)}

def minimalHomologicalPowerMonomials (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i : ℕ) : Set (reesAlgebra I) :=
  {p | ∃ s a, IsMinimalHomologicalPowerMonomial I hI i s a ∧
    p.val = Polynomial.monomial s (MvPolynomial.monomial a 1)}

theorem isMinimalHomologicalPowerMonomial_rank (ρ : RankFunction V)
    (hI : IsPolymatroidalIdeal (rankIdeal k ρ)) (i s : ℕ) (a : Exponent V) :
    IsMinimalHomologicalPowerMonomial (rankIdeal k ρ) hI i s a ↔
      IsMinimalShiftReesMonomial (k := k) ρ i s a := by
  simp only [IsMinimalHomologicalPowerMonomial, IsMinimalShiftReesMonomial,
    homologicalPowerPiece_rank]

theorem boundedHomologicalPowerMonomials_rank (ρ : RankFunction V)
    (hI : IsPolymatroidalIdeal (rankIdeal k ρ)) (i q : ℕ) :
    boundedHomologicalPowerMonomials (rankIdeal k ρ) hI i q =
      boundedShiftReesSet (k := k) ρ i q := by
  ext p
  constructor
  · rintro ⟨s, a, ha, hs, he⟩
    rw [homologicalPowerPiece_rank] at ha
    exact ⟨s, a, ha, hs, Subtype.ext he⟩
  · rintro ⟨s, a, ha, hs, rfl⟩
    exact ⟨s, a, by simpa only [homologicalPowerPiece_rank] using ha, hs, rfl⟩

theorem minimalHomologicalPowerMonomials_rank (ρ : RankFunction V)
    (hI : IsPolymatroidalIdeal (rankIdeal k ρ)) (i : ℕ) :
    minimalHomologicalPowerMonomials (rankIdeal k ρ) hI i =
      minimalShiftReesSet (k := k) ρ i := by
  ext p
  constructor
  · rintro ⟨s, a, ha, he⟩
    have ha' := (isMinimalHomologicalPowerMonomial_rank ρ hI i s a).mp ha
    exact ⟨s, a, ha', Subtype.ext he⟩
  · rintro ⟨s, a, ha, rfl⟩
    exact ⟨s, a, (isMinimalHomologicalPowerMonomial_rank ρ hI i s a).mpr ha, rfl⟩

/-- The semantic minimal monomials really generate the whole homological Rees ideal. -/
theorem homologicalPowerIdeal_eq_span_minimal (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (ρ : RankFunction V) (he : I = rankIdeal k ρ)
    (i : ℕ) :
    homologicalPowerIdeal I hI i = Ideal.span (minimalHomologicalPowerMonomials I hI i) := by
  subst I
  rw [homologicalPowerIdeal_rank, minimalHomologicalPowerMonomials_rank]
  exact shiftReesIdeal_eq_span_minimal ρ i

/-- The zero-module branch of Theorem 4.4, for the genuine homological Rees ideal. -/
theorem homologicalPowerIdeal_eq_bot_of_above (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (ρ : RankFunction V) (he : I = rankIdeal k ρ)
    (hρ : ρ.Active) (i : ℕ) (hi : eventualOffset ρ univ < i) :
    homologicalPowerIdeal I hI i = ⊥ := by
  subst I
  rw [homologicalPowerIdeal_rank]
  exact shiftReesIdeal_eq_bot_of_above ρ hρ i hi

/-- Every positive power has a nonzero shift exactly at and after the first threshold. -/
theorem homologicalShift_power_nonzero_iff (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (ρ : RankFunction V) (he : I = rankIdeal k ρ)
    (hρ : ρ.Active) (i : ℕ) (hi : i ≤ eventualOffset ρ univ)
    (s : ℕ) (hs : 1 ≤ s) :
    homologicalShiftIdeal (I ^ s) (hI.pow s) i ≠ ⊥ ↔ powerThreshold ρ i univ ≤ s := by
  subst I
  rw [homologicalShiftIdeal_eq_rankShiftIdeal _ _ (ρ.scale s)
    (rankIdeal_scale k ρ s).symm]
  exact powerShiftIdeal_ne_bot_iff_threshold ρ hρ i hi hs

/-- The exact interval of actual minimal monomial module-generator degrees. -/
theorem homologicalPower_minimal_degree_iff (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (ρ : RankFunction V) (he : I = rankIdeal k ρ)
    (hρ : ρ.Active) (i : ℕ) (hi0 : 0 < i) (hi : i ≤ eventualOffset ρ univ) (s : ℕ) :
    (∃ a, IsMinimalHomologicalPowerMonomial I hI i s a) ↔
      powerThreshold ρ i univ ≤ s ∧ s ≤ globalPowerThreshold ρ i := by
  subst I
  simp only [isMinimalHomologicalPowerMonomial_rank]
  exact minimalShiftRees_degree_iff ρ hρ i hi0 hi s

/-- The exact least bound is an equality of spans in Mathlib's ordinary Rees algebra. -/
theorem homologicalPower_generation_bound_iff (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (ρ : RankFunction V) (he : I = rankIdeal k ρ)
    (hρ : ρ.Active) (i : ℕ) (hi0 : 0 < i) (hi : i ≤ eventualOffset ρ univ) (q : ℕ) :
    homologicalPowerIdeal I hI i = Ideal.span (boundedHomologicalPowerMonomials I hI i q) ↔
      globalPowerThreshold ρ i ≤ q := by
  subst I
  rw [homologicalPowerIdeal_rank, boundedHomologicalPowerMonomials_rank]
  exact shiftReesIdeal_generation_bound_iff ρ hρ i hi0 hi q

/-- The paper's individual new-generator criterion, with genuine Betti support as input. -/
theorem homologicalPower_minimal_iff_rank_violation (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (ρ : RankFunction V) (he : I = rankIdeal k ρ)
    (hρ : ρ.Active) (i : ℕ) (hi0 : 0 < i) (hi : i ≤ eventualOffset ρ univ)
    (s : ℕ) (hrs : powerThreshold ρ i univ < s) (a : Exponent V)
    (ha : Koszul.GradedBettiNonzero (k := k) (rankBases (ρ.scale s)) a i) :
    IsMinimalHomologicalPowerMonomial I hI i s a ↔
      ∃ A : Finset V, A.Nonempty ∧
        s * ρ A + powerCorrection ρ i (s - 1) A < subsetSum a A := by
  subst I
  rw [isMinimalHomologicalPowerMonomial_rank]
  exact minimalShiftRees_iff_rank_violation ρ hρ i hi0 hi s hrs a
    ((gradedBettiNonzero_rankBases_iff _ _ _).mp ha)

end CommAlg

end
end CheckedSource106

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "107: CommAlg.Polymatroid.HomogenizedIdeal\n"

/-! ## Source: CommAlg.Polymatroid.HomogenizedIdeal -/
section CheckedSource107

/-! # The actual homogenized polynomial ideal

This is the algebraic identity in Theorem 5.1. Extension of an ideal to the
polynomial ring with one extra variable is `Ideal.map` under the actual
variable-renaming homomorphism. Multiplication by the specified power of the
new variable is multiplication by its principal ideal.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset
open scoped Pointwise

variable {V : Type*} [Fintype V] [DecidableEq V]

section Semiring

variable (k : Type*) [CommSemiring k]

theorem monomialIdeal_union (B C : Family V) :
    monomialIdeal k (B ∪ C) = monomialIdeal k B + monomialIdeal k C := by
  simp only [monomialIdeal, Finset.coe_union, Set.image_union, Ideal.span_union,
    Ideal.add_eq_sup]

theorem monomialIdeal_biUnion {J : Type*} [DecidableEq J]
    (s : Finset J) (B : J → Family V) :
    monomialIdeal k (s.biUnion B) = ∑ j ∈ s, monomialIdeal k (B j) := by
  induction s using Finset.induction_on with
  | empty => simp [monomialIdeal]
  | @insert j s hj ih =>
    rw [Finset.biUnion_insert, monomialIdeal_union, Finset.sum_insert hj, ih]

theorem monomial_optionElim (a : Exponent V) (z : ℕ) :
    MvPolynomial.X (R := k) none ^ z *
        MvPolynomial.rename some (MvPolynomial.monomial a 1) =
      MvPolynomial.monomial (a.optionElim z) 1 := by
  have he : Finsupp.single none z + a.mapDomain some = a.optionElim z := by
    change Finsupp.single none z + a.mapDomain (Function.Embedding.some : V ↪ Option V) = _
    rw [← Finsupp.embDomain_eq_mapDomain]
    ext x
    cases x <;> simp
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.rename_monomial,
    MvPolynomial.monomial_mul, one_mul, he]

theorem monomialIdeal_optionElim (B : Family V) (z : ℕ) :
    Ideal.span {MvPolynomial.X (R := k) none ^ z} *
      Ideal.map (MvPolynomial.rename some).toRingHom (monomialIdeal k B) =
        monomialIdeal k (B.image (fun a => a.optionElim z)) := by
  unfold monomialIdeal
  rw [Ideal.map_span, Ideal.span_mul_span]
  apply congrArg Ideal.span
  ext f
  constructor
  · intro hf
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.mp hf
    obtain rfl := Set.mem_singleton_iff.mp hx
    obtain ⟨q, hq, rfl⟩ := hy
    obtain ⟨a, ha, rfl⟩ := hq
    refine ⟨a.optionElim z, Finset.mem_image.mpr ⟨a, ha, rfl⟩, ?_⟩
    exact (monomial_optionElim k a z).symm
  · rintro ⟨e, he, rfl⟩
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    exact Set.mem_mul.mpr ⟨_, Set.mem_singleton _, _,
      ⟨MvPolynomial.monomial a 1, ⟨a, ha, rfl⟩, rfl⟩, monomial_optionElim k a z⟩

/-- The displayed sum in Theorem 5.1, at this stage with the explicit rank
formula in place of the separately defined genuine homological-shift ideal. -/
def homogenizedShiftIdeal (g : RankFunction V) : Ideal (MvPolynomial (Option V) k) :=
  ∑ i ∈ Finset.range (shiftLength g + 1),
    Ideal.span {MvPolynomial.X (R := k) none ^ (shiftLength g - i)} *
      Ideal.map (MvPolynomial.rename some).toRingHom (rankShiftIdeal k g i)

/-- Every generator in every shift layer occurs, and there are no additional
minimal generators. This is an equality of actual polynomial ideals. -/
theorem homogenizedShiftIdeal_eq_rankIdeal (g : RankFunction V) :
    homogenizedShiftIdeal k g = rankIdeal k (homogenizedShiftRank g) := by
  rw [rankIdeal, rankBases_homogenizedShift, monomialIdeal_biUnion]
  unfold homogenizedShiftIdeal
  apply Finset.sum_congr rfl
  intro i hi
  rw [rankShiftIdeal_eq_monomialIdeal, monomialIdeal_optionElim]

end Semiring

/-- The canonical upper rank of the precise union of homogenized shift bases. -/
theorem homogenizedShiftFamily_upperRank (g : RankFunction V)
    (A : Finset (Option V)) :
    upperRank ((Finset.range (shiftLength g + 1)).biUnion (fun i =>
      (rankShiftFamily g i).image (fun a => a.optionElim (shiftLength g - i)))) A =
        homogenizedShiftRank g A := by
  rw [← rankBases_homogenizedShift, upperRank_rankBases]

/-- The full union of homogenized shift bases satisfies the ordinary discrete
polymatroid exchange axiom. -/
theorem homogenizedShiftFamily_polymatroidal (g : RankFunction V) :
    IsPolymatroidal ((Finset.range (shiftLength g + 1)).biUnion (fun i =>
      (rankShiftFamily g i).image (fun a => a.optionElim (shiftLength g - i)))) := by
  rw [← rankBases_homogenizedShift]
  exact rankBases_polymatroidal _

end CommAlg.Polymatroid

end
end CheckedSource107

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "108: CommAlg.Polymatroid.HomologicalHomogenization\n"

/-! ## Source: CommAlg.Polymatroid.HomologicalHomogenization -/
section CheckedSource108

/-! # Homogenization of the genuine total Betti support

This module proves the actual polynomial-ideal identity, the exact derived-Tor
base description, its degree, exchange property, and canonical rank. The
projective-dimension identification of the rank gap is supplied separately by
the checked projective-resolution and linear-quotient argument.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]

local instance : LinearOrder (Option V) := (inferInstance : LinearOrder (WithBot V))

/-- The literal sum in Theorem 5.1 in the polynomial ring with the extra
variable `none`. Original variables are included by `some`. -/
def homogenizedHomologicalIdeal (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (p : ℕ) : Ideal (MvPolynomial (Option V) k) :=
  ∑ i ∈ Finset.range (p + 1),
    Ideal.span {MvPolynomial.X (R := k) none ^ (p - i)} *
      Ideal.map (MvPolynomial.rename some).toRingHom (homologicalShiftIdeal I hI i)

/-- The equality is between actual ideals, and the summands are the genuine
homological-shift ideals defined from Mathlib's derived Tor. -/
theorem homogenizedHomologicalIdeal_eq_rankIdeal (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (g : RankFunction V) (he : I = rankIdeal k g) :
    homogenizedHomologicalIdeal I hI (shiftLength g) =
      rankIdeal k (homogenizedShiftRank g) := by
  unfold homogenizedHomologicalIdeal
  simp_rw [homologicalShiftIdeal_eq_rankShiftIdeal I hI g he]
  exact homogenizedShiftIdeal_eq_rankIdeal k g

/-- The precise base description in terms of all nonzero actual Tor
multidegrees, with both implications checked. -/
theorem homogenized_rankBase_iff_actualBetti (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (g : RankFunction V) (he : I = rankIdeal k g)
    (e : Exponent (Option V)) :
    IsRankBase (homogenizedShiftRank g) e ↔
      ∃ i ≤ shiftLength g, ∃ a : Exponent V,
        Koszul.GradedBettiNonzero (k := k) (idealGenerators I hI) a i ∧
          e = a.optionElim (shiftLength g - i) := by
  rw [idealGenerators_eq_of_presentation I hI (rankBases g) (rankBases_polymatroidal g) he]
  simp_rw [gradedBettiNonzero_rankBases_iff]
  exact isRankBase_homogenizedShift_iff g e

theorem homogenizedHomologicalIdeal_polymatroidal (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (g : RankFunction V) (he : I = rankIdeal k g) :
    IsPolymatroidalIdeal (homogenizedHomologicalIdeal I hI (shiftLength g)) := by
  rw [homogenizedHomologicalIdeal_eq_rankIdeal I hI g he]
  exact isPolymatroidalIdeal_rankIdeal _

theorem homogenizedHomologicalIdeal_generators (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (g : RankFunction V) (he : I = rankIdeal k g) :
    idealGenerators (homogenizedHomologicalIdeal I hI (shiftLength g))
      (homogenizedHomologicalIdeal_polymatroidal I hI g he) =
        rankBases (homogenizedShiftRank g) :=
  idealGenerators_eq_of_presentation _ _ _ (rankBases_polymatroidal _)
    (homogenizedHomologicalIdeal_eq_rankIdeal I hI g he)

/-- Every minimal generator has precisely the asserted total degree. -/
theorem homogenizedHomologicalIdeal_degree (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (g : RankFunction V) (he : I = rankIdeal k g) :
    Equigenerated (idealGenerators (homogenizedHomologicalIdeal I hI (shiftLength g))
      (homogenizedHomologicalIdeal_polymatroidal I hI g he)) (g univ + shiftLength g) := by
  rw [homogenizedHomologicalIdeal_generators I hI g he]
  have hd := rankBases_equigenerated (homogenizedShiftRank g)
  have hr : homogenizedShiftRank g univ = g univ + shiftLength g := by
    rw [homogenizedShiftRank, RankFunction.homogenize_univ, ← shiftLength_add_degree]
    omega
  rwa [hr] at hd

/-- The displayed rank is canonical, recovered by maximization over the
actual minimal generator exponents. -/
theorem homogenizedHomologicalIdeal_canonicalRank (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (g : RankFunction V) (he : I = rankIdeal k g)
    (A : Finset (Option V)) :
    upperRank (idealGenerators (homogenizedHomologicalIdeal I hI (shiftLength g))
      (homogenizedHomologicalIdeal_polymatroidal I hI g he)) A = homogenizedShiftRank g A := by
  rw [homogenizedHomologicalIdeal_generators I hI g he, upperRank_rankBases]

@[simp] theorem homogenizedShiftRank_on_original (g : RankFunction V) (A : Finset V) :
    homogenizedShiftRank g (A.image some) = universalAugmentedRank g A := by
  exact RankFunction.homogenize_some g _ _ A

@[simp] theorem homogenizedShiftRank_with_new_variable (g : RankFunction V) (A : Finset V) :
    homogenizedShiftRank g A.insertNone = shiftLength g + g A := by
  exact RankFunction.homogenize_insertNone g _ _ A

theorem homogenizedShiftRank_active_original (g : RankFunction V) (hg : g.Active)
    (A : Finset V) : homogenizedShiftRank g (A.image some) = A.card + partitionRank g A := by
  rw [homogenizedShiftRank_on_original, universalAugmentedRank_eq_active g hg A]
  rfl

/-- The exact Betti support is independent of the coefficient field (in fact,
it is independent of every nontrivial commutative coefficient ring). -/
theorem gradedBettiNonzero_rankBases_field_independent
    {l : Type u} [CommRing l] [Nontrivial l] (g : RankFunction V) (a : Exponent V) (i : ℕ) :
    Koszul.GradedBettiNonzero (k := k) (rankBases g) a i ↔
      Koszul.GradedBettiNonzero (k := l) (rankBases g) a i := by
  rw [gradedBettiNonzero_rankBases_iff, gradedBettiNonzero_rankBases_iff]

end CommAlg.Polymatroid

end
end CheckedSource108

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "109: CommAlg.Polymatroid.HomologicalHomogenizationPD\n"

/-! ## Source: CommAlg.Polymatroid.HomologicalHomogenizationPD -/
section CheckedSource109

/-! # Theorem 5.1 with the actual projective dimension

This final statement combines the genuine Tor support, the actual ideal sum,
and Mathlib's categorical projective dimension.  All conclusions refer to the
unique minimal monomial generators of that sum.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset CategoryTheory

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

local instance : LinearOrder (Option V) := (inferInstance : LinearOrder (WithBot V))

/-- The complete homogenization assertion, including the actual projective
dimension and both directions of the characterization of every minimal
generator by a nonzero actual Tor multidegree.  Loops and the unit ideal are
allowed in addition to the paper's nonzero proper active case. -/
theorem homological_homogenization (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (g : RankFunction V) (he : I = rankIdeal k g) :
    ∃ p : ℕ,
      p = shiftLength g ∧
      projectiveDimension (ModuleCat.of (MvPolynomial V k) I) = (p : WithBot ℕ∞) ∧
      ∃ hH : IsPolymatroidalIdeal (homogenizedHomologicalIdeal I hI p),
        Equigenerated (idealGenerators (homogenizedHomologicalIdeal I hI p) hH)
          (g univ + p) ∧
        (∀ A : Finset (Option V),
          upperRank (idealGenerators (homogenizedHomologicalIdeal I hI p) hH) A =
            homogenizedShiftRank g A) ∧
        (∀ e : Exponent (Option V),
          e ∈ idealGenerators (homogenizedHomologicalIdeal I hI p) hH ↔
            ∃ i ≤ p, ∃ a : Exponent V,
              Koszul.GradedBettiNonzero (k := k) (idealGenerators I hI) a i ∧
                e = a.optionElim (p - i)) := by
  refine ⟨shiftLength g, rfl,
    CommAlg.ProjectiveDimension.polymatroidalIdeal_projectiveDimension I g he,
    homogenizedHomologicalIdeal_polymatroidal I hI g he,
    homogenizedHomologicalIdeal_degree I hI g he,
    homogenizedHomologicalIdeal_canonicalRank I hI g he, ?_⟩
  intro e
  rw [homogenizedHomologicalIdeal_generators I hI g he, mem_rankBases]
  exact homogenized_rankBase_iff_actualBetti I hI g he e

/-- No rank presentation is an additional hypothesis on an actual nonzero
polymatroidal ideal: it is constructed from its exchange generators. -/
theorem homological_homogenization_exists_rank (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (hne : I ≠ ⊥) :
    ∃ g : RankFunction V, I = rankIdeal k g ∧
      projectiveDimension (ModuleCat.of (MvPolynomial V k) I) =
        (shiftLength g : WithBot ℕ∞) ∧
      IsPolymatroidalIdeal (homogenizedHomologicalIdeal I hI (shiftLength g)) := by
  obtain ⟨g, he⟩ := hI.exists_rank hne
  exact ⟨g, he,
    CommAlg.ProjectiveDimension.polymatroidalIdeal_projectiveDimension I g he,
    homogenizedHomologicalIdeal_polymatroidal I hI g he⟩

end CommAlg.Polymatroid

end
end CheckedSource109

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "110: CommAlg.Polymatroid.ThresholdCorrespondence\n"

/-! ## Source: CommAlg.Polymatroid.ThresholdCorrespondence -/
section CheckedSource110

/-! # Exact correspondence with the paper's signed rational ceilings

Natural subtraction in the implementation clamps the numerator at zero.
The first theorem verifies that this is exactly the nonnegative part of the
ordinary rational ceiling, even when the paper's signed numerator is negative.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

theorem signedCeiling_toNat_eq_ceilDiv (κ b δ : ℕ) (hδ : 0 < δ) :
    (Int.ceil (((κ : ℚ) - b) / δ)).toNat = (κ - b) ⌈/⌉ δ := by
  apply eq_of_forall_ge_iff
  intro s
  have hδQ : (0 : ℚ) < δ := by exact_mod_cast hδ
  calc
    (Int.ceil (((κ : ℚ) - b) / δ)).toNat ≤ s ↔
        ((κ : ℚ) - b) / δ ≤ s := by
      rw [Int.toNat_le, Int.ceil_le]
      simp only [Int.cast_natCast]
    _ ↔ (κ : ℚ) ≤ s * δ + b := by rw [div_le_iff₀ hδQ, sub_le_iff_le_add]
    _ ↔ κ ≤ s * δ + b := by norm_cast
    _ ↔ (κ - b) ⌈/⌉ δ ≤ s := by
      rw [ceilDiv_le_iff_le_mul hδ, Nat.mul_comm δ s]
      omega

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The implemented threshold is the paper's maximum over positive-defect
partitions of the nonnegative part of its displayed rational ceiling. -/
theorem powerThreshold_eq_rationalCeiling (ρ : RankFunction V) (i : ℕ) (A : Finset V) :
    powerThreshold ρ i A = Finset.univ.sup (fun P : Finpartition A =>
      if 0 < partitionDefect ρ P then
        (Int.ceil ((((eventualCorrection ρ i A : ℕ) : ℚ) - partitionSlack P) /
          (partitionDefect ρ P : ℚ))).toNat else 0) := by
  unfold powerThreshold affineThreshold
  apply Finset.sup_congr rfl
  intro P hP
  by_cases hd : partitionDefect ρ P = 0
  · simp [hd]
  · have hp : 0 < partitionDefect ρ P := by omega
    simp only [if_neg hd, if_pos hp]
    exact (signedCeiling_toNat_eq_ceilDiv _ _ _ hp).symm

end CommAlg.Polymatroid

end
end CheckedSource110

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "111: CommAlg.KoszulComplex.DerivedDecomposition\n"

/-! ## Source: CommAlg.KoszulComplex.DerivedDecomposition -/
section CheckedSource111

/-! # Every genuine derived Tor class is a finite sum of multigraded classes -/

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2500
namespace CommAlg.Koszul
open Classical CommAlg.Polymatroid CategoryTheory CategoryTheory.Limits
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]

/-- A canonical component of a derived Tor element, regarded as a member of its true degree submodule. -/
def derivedComponent (B : Family V) (i : ℕ)
    (x : (ModuleCat.restrictScalars (algebraMap k (MvPolynomial V k))).obj
      (finitePolynomialTor i (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B))))
    (a : Exponent V) : gradedTor (k := k) B a i :=
  ⟨toDerivedTor (k := k) B a i
    (HomologicalComplex.homologyMap (homogeneousRetraction (k := k) B a) i
      ((coefficientTorIso (k := k) B i).hom x)), ⟨_, rfl⟩⟩

/-- Completeness of the multigrading: every actual derived Tor class is a finite sum of its components. -/
lemma derivedTor_decomposition (B : Family V) (i : ℕ)
    (x : (ModuleCat.restrictScalars (algebraMap k (MvPolynomial V k))).obj
      (finitePolynomialTor i (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B)))) :
    ∃ s : Finset (Exponent V), ∑ a ∈ s, (derivedComponent (k := k) B i x a).val = x := by
  obtain ⟨s, hs⟩ := homogeneous_homology_decomposition (k := k) B i
    ((coefficientTorIso (k := k) B i).hom x)
  refine ⟨s, ?_⟩
  apply (coefficientTorIso (k := k) B i).toLinearEquiv.injective
  change (coefficientTorIso (k := k) B i).hom _ = _
  rw [map_sum]
  calc
    ∑ a ∈ s, (coefficientTorIso (k := k) B i).hom
        (derivedComponent (k := k) B i x a).val =
      ∑ a ∈ s, HomologicalComplex.homologyMap
        (homogeneousProjector (k := k) B a) i ((coefficientTorIso (k := k) B i).hom x) := by
      apply Finset.sum_congr rfl
      intro a ha
      simp only [derivedComponent, toDerivedTor, ModuleCat.comp_apply,
        ← ModuleCat.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply,
        homogeneousProjector, HomologicalComplex.homologyMap_comp, Category.assoc,
        Iso.inv_hom_id_assoc, Category.comp_id]
    _ = _ := hs

/-- The actual degree submodules span all of derived Tor. -/
lemma iSup_gradedTor (B : Family V) (i : ℕ) :
    (⨆ a : Exponent V, gradedTor (k := k) B a i) = ⊤ := by
  apply top_unique
  intro x hx
  obtain ⟨s, hs⟩ := derivedTor_decomposition (k := k) B i x
  rw [← hs]
  apply Submodule.sum_mem
  intro a ha
  exact (le_iSup (fun a : Exponent V => gradedTor (k := k) B a i) a)
    (derivedComponent (k := k) B i x a).property

/-- Nonzero derived Tor has some nonzero multidegree, and conversely. -/
lemma derivedTor_nonzero_iff (B : Family V) (i : ℕ) :
    ¬ IsZero (finitePolynomialTor i
      (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B))) ↔
      ∃ a, GradedBettiNonzero (k := k) B a i := by
  constructor
  · contrapose!
    intro h
    apply ModuleCat.isZero_iff_subsingleton.mpr
    constructor
    intro x y
    have hx : x = 0 := by
      obtain ⟨s, hs⟩ := derivedTor_decomposition (k := k) B i x
      rw [← hs]
      apply Finset.sum_eq_zero
      intro a ha
      have hz := ModuleCat.isZero_iff_subsingleton.mp (not_not.mp (h a))
      exact congrArg Subtype.val (hz.elim (derivedComponent (k := k) B i x a) 0)
    have hy : y = 0 := by
      obtain ⟨s, hs⟩ := derivedTor_decomposition (k := k) B i y
      rw [← hs]
      apply Finset.sum_eq_zero
      intro a ha
      have hz := ModuleCat.isZero_iff_subsingleton.mp (not_not.mp (h a))
      exact congrArg Subtype.val (hz.elim (derivedComponent (k := k) B i y a) 0)
    exact hx.trans hy.symm
  · rintro ⟨a, ha⟩
    exact derivedTor_nonzero_of_graded (k := k) B a i ha

end CommAlg.Koszul

end
end CheckedSource111

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "112: CommAlg.KoszulComplex.InternalGrading\n"

/-! ## Source: CommAlg.KoszulComplex.InternalGrading -/
section CheckedSource112

/-! # The multigraded pieces form an actual internal direct sum of derived Tor -/

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2500
namespace CommAlg.Koszul
open Classical CommAlg.Polymatroid CategoryTheory CategoryTheory.Limits
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]

/-- The canonical projection from derived Tor onto a homogeneous homology group. -/
def fromDerivedTor (B : Family V) (a : Exponent V) (i : ℕ) :
    (ModuleCat.restrictScalars (algebraMap k (MvPolynomial V k))).obj
      (finitePolynomialTor i (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B))) ⟶
      (homogeneousComplex (k := k) B a).homology i :=
  (coefficientTorIso (k := k) B i).hom ≫
    HomologicalComplex.homologyMap (homogeneousRetraction (k := k) B a) i

lemma toDerivedTor_from_same (B : Family V) (a : Exponent V) (i : ℕ) :
    toDerivedTor (k := k) B a i ≫ fromDerivedTor (k := k) B a i = 𝟙 _ := by
  simp only [toDerivedTor, fromDerivedTor, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← HomologicalComplex.homologyMap_comp, homogeneousInclusion_retraction,
    HomologicalComplex.homologyMap_id]

lemma toDerivedTor_from_ne (B : Family V) (a b : Exponent V) (i : ℕ) (hab : a ≠ b) :
    toDerivedTor (k := k) B a i ≫ fromDerivedTor (k := k) B b i = 0 := by
  simp only [toDerivedTor, fromDerivedTor, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← HomologicalComplex.homologyMap_comp,
    homogeneousInclusion_retraction_ne B a b hab, HomologicalComplex.homologyMap_zero]

/-- The genuine degree projection, as an endomorphism of actual derived Tor. -/
def derivedProjection (B : Family V) (a : Exponent V) (i : ℕ) :=
  (fromDerivedTor (k := k) B a i ≫ toDerivedTor (k := k) B a i).hom

lemma derivedProjection_self (B : Family V) (a : Exponent V) (i : ℕ)
    {x} (hx : x ∈ gradedTor (k := k) B a i) : derivedProjection (k := k) B a i x = x := by
  obtain ⟨y, rfl⟩ := hx
  change (fromDerivedTor (k := k) B a i ≫ toDerivedTor (k := k) B a i)
    (toDerivedTor (k := k) B a i y) = toDerivedTor (k := k) B a i y
  rw [← ModuleCat.comp_apply, ← Category.assoc, toDerivedTor_from_same, Category.id_comp]

lemma derivedProjection_other (B : Family V) (a b : Exponent V) (i : ℕ)
    (hab : a ≠ b) {x} (hx : x ∈ gradedTor (k := k) B b i) :
    derivedProjection (k := k) B a i x = 0 := by
  obtain ⟨y, rfl⟩ := hx
  change (fromDerivedTor (k := k) B a i ≫ toDerivedTor (k := k) B a i)
    (toDerivedTor (k := k) B b i y) = 0
  rw [← ModuleCat.comp_apply, ← Category.assoc,
    toDerivedTor_from_ne B b a i (Ne.symm hab), zero_comp]
  rfl

lemma gradedTor_independent (B : Family V) (i : ℕ) :
    iSupIndep (fun a : Exponent V => gradedTor (k := k) B a i) := by
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s v hv hs a ha
  have h := congrArg (derivedProjection (k := k) B a i) hs
  rw [map_sum, map_zero] at h
  rw [Finset.sum_eq_single a] at h
  · rwa [derivedProjection_self B a i (hv a ha)] at h
  · intro b hb hba
    exact derivedProjection_other B a b i (Ne.symm hba) (hv b hb)
  · exact fun hnot => (hnot ha).elim

/-- The degree pieces used to define Betti support are a genuine internal direct sum of derived Tor. -/
theorem gradedTor_isInternal (B : Family V) (i : ℕ) :
    DirectSum.IsInternal (fun a : Exponent V => gradedTor (k := k) B a i) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (gradedTor_independent B i) (iSup_gradedTor B i)

end CommAlg.Koszul

end
end CheckedSource112

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "113: CommAlg.KoszulComplex.ResidueCoefficients\n"

/-! ## Source: CommAlg.KoszulComplex.ResidueCoefficients -/
section CheckedSource113

/-! # The residue quotient is the coefficient field with its intended polynomial action -/

noncomputable section
namespace CommAlg.Koszul
open CategoryTheory MvPolynomial
universe u
variable {V k : Type u} [CommRing k]

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

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "114: CommAlg\n"

/-! ## Source: CommAlg -/
section CheckedSource114

/-! Complete principal theorem library for Rank formulas for homological shifts of polymatroidal ideals. -/

end CheckedSource114

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "115: FourPapers.Homological.Main\n"

/-! ## Source: FourPapers.Homological.Main -/
section CheckedSource115

/-!
# Principal results of the attached homological-shifts manuscript

This public entry point specializes the more general verified library to fields,
as in the manuscript. The underlying homological shifts use genuine multigraded
pieces of Mathlib's derived tensor functor. No expected rank formula occurs in
their definition.

Manuscript: `14_homological_shifts(9).pdf`, SHA-256
`de8e82538734073169d46a02e8a142dc9f898f90863425ecdfc1a82e39f15341`.
-/

set_option autoImplicit false

noncomputable section

namespace FourPapers.Homological

open Classical Finset CommAlg CommAlg.Polymatroid

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

/-- Theorem 1.1: stabilization for every ideal and every `s ≥ i > 0`. -/
theorem theorem_1_1 (I : Ideal (MvPolynomial V k)) (hI : IsPolymatroidalIdeal I)
    (i s : ℕ) (_hi : 0 < i) (hs : i ≤ s) :
    homologicalShiftIdeal (I ^ (s + 1)) (hI.pow (s + 1)) i =
      I * homologicalShiftIdeal (I ^ s) (hI.pow s) i :=
  homologicalShift_powers I hI i s hs

/-- The fixed-polymatroidal-twist clause of Theorem 1.1. -/
theorem theorem_1_1_twisted (I J : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (hJ : IsPolymatroidalIdeal J)
    (i s : ℕ) (_hi : 0 < i) (hs : i ≤ s) :
    homologicalShiftIdeal (J * I ^ (s + 1)) (hJ.mul (hI.pow (s + 1))) i =
      I * homologicalShiftIdeal (J * I ^ s) (hJ.mul (hI.pow s)) i :=
  homologicalShift_twistedPowers I J hI hJ i s hs

/-- The actual ordinary Rees-module generation assertion of Theorem 1.1. -/
theorem theorem_1_1_generation (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i : ℕ) (hi : 0 < i) :
    homologicalPowerIdeal I hI i = Ideal.span (homologicalPowerBoxGenerators I hI i) :=
  homologicalPowerIdeal_generated_le I hI i hi

/-- Theorem 1.2: the exact partition formula on the active ground set.
The right-hand side rank is a proved `RankFunction`, hence includes all
normalization, monotonicity, integrality, and submodularity assertions. -/
theorem theorem_1_2 (g : RankFunction V) (hg : g.Active) (i : ℕ) :
    homologicalShiftIdeal (rankIdeal k g) (isPolymatroidalIdeal_rankIdeal g) i =
      if homologicalRank g hg i univ = g univ + i then
        rankIdeal k (homologicalRank g hg i) else ⊥ :=
  homologicalShiftIdeal_partitionFormula _ _ g rfl hg i

/-- The canonicality clause of Theorem 1.2; the left side takes the maximum
over the actual minimal monomial generator exponents. -/
theorem theorem_1_2_canonical (g : RankFunction V) (hg : g.Active) (i : ℕ)
    (hne : homologicalShiftIdeal (rankIdeal k g)
      (isPolymatroidalIdeal_rankIdeal g) i ≠ ⊥) (A : Finset V) :
    upperRank (idealGenerators
      (homologicalShiftIdeal (rankIdeal k g) (isPolymatroidalIdeal_rankIdeal g) i)
      (homologicalShiftIdeal_polymatroidal _ _ i)) A = homologicalRank g hg i A := by
  rw [homologicalShiftIdeal_canonicalRank _ _ g rfl i hne]
  exact universalHomologicalRank_eq_active g hg i A

/-- Proposition 4.2: the universal sharpness family in all positive degrees. -/
theorem proposition_4_2 (i : ℕ) (hi : 1 ≤ i) (hcard : Fintype.card V = i + 1) :
    (∀ s : ℕ, 1 ≤ s → s < i →
      homologicalShiftIdeal (squarefreeVeroneseIdeal k V i ^ s)
        ((squarefreeVeronese_polymatroidal i).pow s) i = ⊥) ∧
    homologicalShiftIdeal (squarefreeVeroneseIdeal k V i ^ i)
      ((squarefreeVeronese_polymatroidal i).pow i) i =
        Ideal.span {(∏ j : V, (MvPolynomial.X j : MvPolynomial V k)) ^ i} ∧
    homologicalShiftIdeal (squarefreeVeroneseIdeal k V i ^ i)
      ((squarefreeVeronese_polymatroidal i).pow i) i ≠ ⊥ :=
  ⟨fun _ hs hsi => squarefreeVeronese_shift_below hi hs hsi hcard,
    squarefreeVeronese_shift_at_threshold hi hcard,
    squarefreeVeronese_shift_at_threshold_ne_bot hi hcard⟩

/-- Corollary 4.3: actual categorical projective dimension, with the minimum
ranging over every partition of the entire active ground set. -/
theorem corollary_4_3 (ρ : RankFunction V) (hρ : ρ.Active) (s : ℕ) (hs : 1 ≤ s) :
    CategoryTheory.projectiveDimension
        (ModuleCat.of (MvPolynomial V k) ↥((rankIdeal k ρ) ^ s)) =
      (finiteMinimum (fun P : Finpartition (univ : Finset V) =>
        s * partitionDefect ρ P + partitionSlack P) : WithBot ℕ∞) :=
  CommAlg.ProjectiveDimension.rankIdeal_power_projectiveDimension ρ hρ s hs

/-- The eventual projective-dimension assertion in Corollary 4.3. -/
theorem corollary_4_3_eventual (ρ : RankFunction V) (hρ : ρ.Active)
    (s : ℕ) (hs : max 1 (eventualOffset ρ univ) ≤ s) :
    CategoryTheory.projectiveDimension
        (ModuleCat.of (MvPolynomial V k) ↥((rankIdeal k ρ) ^ s)) =
      (eventualOffset ρ univ : WithBot ℕ∞) :=
  CommAlg.ProjectiveDimension.rankIdeal_power_projectiveDimension_eventual ρ hρ s hs

/-- The zero-module case of Theorem 4.4. -/
theorem theorem_4_4_zero (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) (hi : eventualOffset ρ univ < i) :
    homologicalPowerIdeal (rankIdeal k ρ) (isPolymatroidalIdeal_rankIdeal ρ) i = ⊥ :=
  homologicalPowerIdeal_eq_bot_of_above _ _ ρ rfl hρ i hi

/-- Theorem 4.4: the exact interval of actual minimal monomial Rees-module
generators, its endpoints, first nonzero piece, and exact least generation bound. -/
theorem theorem_4_4 (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) (hi0 : 0 < i) (hi : i ≤ eventualOffset ρ univ) :
    (1 ≤ powerThreshold ρ i univ ∧
      powerThreshold ρ i univ ≤ globalPowerThreshold ρ i ∧
      globalPowerThreshold ρ i ≤ i) ∧
    (∀ s : ℕ, 1 ≤ s →
      (homologicalShiftIdeal (rankIdeal k ρ ^ s)
        ((isPolymatroidalIdeal_rankIdeal ρ).pow s) i ≠ ⊥ ↔
          powerThreshold ρ i univ ≤ s)) ∧
    (∀ s : ℕ,
      (∃ a, IsMinimalHomologicalPowerMonomial (rankIdeal k ρ)
        (isPolymatroidalIdeal_rankIdeal ρ) i s a) ↔
          powerThreshold ρ i univ ≤ s ∧ s ≤ globalPowerThreshold ρ i) ∧
    (∀ q : ℕ,
      homologicalPowerIdeal (rankIdeal k ρ) (isPolymatroidalIdeal_rankIdeal ρ) i =
        Ideal.span (boundedHomologicalPowerMonomials (rankIdeal k ρ)
          (isPolymatroidalIdeal_rankIdeal ρ) i q) ↔
            globalPowerThreshold ρ i ≤ q) :=
  ⟨powerShift_generator_endpoints ρ i hi0 hi,
    fun s hs => homologicalShift_power_nonzero_iff (rankIdeal k ρ) (isPolymatroidalIdeal_rankIdeal ρ) ρ rfl hρ i hi s hs,
    fun s => homologicalPower_minimal_degree_iff _ _ ρ rfl hρ i hi0 hi s,
    fun q => homologicalPower_generation_bound_iff _ _ ρ rfl hρ i hi0 hi q⟩

/-- The threshold used in Theorem 4.4 is exactly the paper's signed rational
ceiling formula, including negative numerators and empty index collections. -/
theorem theorem_4_4_threshold_formula (ρ : RankFunction V) (i : ℕ) (A : Finset V) :
    powerThreshold ρ i A = Finset.univ.sup (fun P : Finpartition A =>
      if 0 < partitionDefect ρ P then
        (Int.ceil ((((eventualCorrection ρ i A : ℕ) : ℚ) - partitionSlack P) /
          (partitionDefect ρ P : ℚ))).toNat else 0) :=
  powerThreshold_eq_rationalCeiling ρ i A

local instance : LinearOrder (Option V) := (inferInstance : LinearOrder (WithBot V))

/-- Theorem 5.1: the total-support ideal, its genuine projective dimension,
degree, canonical rank, and exact actual-Tor description of every generator. -/
theorem theorem_5_1 (I : Ideal (MvPolynomial V k)) (hI : IsPolymatroidalIdeal I)
    (g : RankFunction V) (he : I = rankIdeal k g) :
    ∃ p : ℕ,
      p = shiftLength g ∧
      CategoryTheory.projectiveDimension (ModuleCat.of (MvPolynomial V k) I) =
        (p : WithBot ℕ∞) ∧
      ∃ hH : IsPolymatroidalIdeal (homogenizedHomologicalIdeal I hI p),
        Equigenerated (idealGenerators (homogenizedHomologicalIdeal I hI p) hH)
          (g univ + p) ∧
        (∀ A : Finset (Option V),
          upperRank (idealGenerators (homogenizedHomologicalIdeal I hI p) hH) A =
            homogenizedShiftRank g A) ∧
        (∀ e : Exponent (Option V),
          e ∈ idealGenerators (homogenizedHomologicalIdeal I hI p) hH ↔
            ∃ i ≤ p, ∃ a : Exponent V,
              Koszul.GradedBettiNonzero (k := k) (idealGenerators I hI) a i ∧
                e = a.optionElim (p - i)) :=
  homological_homogenization I hI g he

/-- The two displayed formulas for the canonical rank in Theorem 5.1. -/
theorem theorem_5_1_rank (g : RankFunction V) (hg : g.Active) (A : Finset V) :
    homogenizedShiftRank g (A.image some) = A.card + partitionRank g A ∧
      homogenizedShiftRank g A.insertNone = shiftLength g + g A :=
  ⟨homogenizedShiftRank_active_original g hg A,
    homogenizedShiftRank_with_new_variable g A⟩

/-- The final field-independence assertion in Theorem 5.1, on the exact
nonzero multigraded pieces of genuine derived Tor. -/
theorem theorem_5_1_field_independent {l : Type u} [Field l]
    (g : RankFunction V) (a : Exponent V) (i : ℕ) :
    Koszul.GradedBettiNonzero (k := k) (rankBases g) a i ↔
      Koszul.GradedBettiNonzero (k := l) (rankBases g) a i :=
  gradedBettiNonzero_rankBases_field_independent g a i

/-- Theorem 6.1: integral closure inside the actual ordinary Rees algebra. -/
theorem theorem_6_1 (I : Ideal (MvPolynomial V k)) (hI : IsPolymatroidalIdeal I)
    (i : ℕ) (hi : 0 < i) :
    IsIntegrallyClosedIdeal (homologicalPowerIdeal I hI i) :=
  homologicalPowerIdeal_integrallyClosed I hI i hi

section SeveralColors

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- Corollary 4.1: the full coordinatewise stabilization equality. -/
theorem corollary_4_1 (I : C → Ideal (MvPolynomial V k))
    (J : Ideal (MvPolynomial V k)) (hI : ∀ c, IsPolymatroidalIdeal (I c))
    (hJ : IsPolymatroidalIdeal J) (s : C →₀ ℕ) (i : ℕ)
    (c : C) (_hi : 0 < i) (hs : i ≤ s c) :
    homologicalShiftIdeal (J * powerProduct I (s + Finsupp.single c 1))
        (hJ.mul (IsPolymatroidalIdeal.powerProduct I hI _)) i =
      I c * homologicalShiftIdeal (J * powerProduct I s)
        (hJ.mul (IsPolymatroidalIdeal.powerProduct I hI _)) i :=
  homologicalShift_severalColors I J hI hJ s i c hs

/-- The full multigraded module-generation clause of Corollary 4.1. -/
theorem corollary_4_1_generation (I : C → Ideal (MvPolynomial V k))
    (J : Ideal (MvPolynomial V k)) (hI : ∀ c, IsPolymatroidalIdeal (I c))
    (hJ : IsPolymatroidalIdeal J) (i : ℕ) :
    homologicalMultiIdeal J I hJ hI i =
      Ideal.span (reesBoxGenerators I (homologicalMultiPiece J I hJ hI i) i) :=
  homologicalMultiIdeal_generated_in_box J I hJ hI i

/-- Corollary 6.2: arbitrary finite colors, fixed twists, and zero coordinates. -/
theorem corollary_6_2 (I : C → Ideal (MvPolynomial V k))
    (J : Ideal (MvPolynomial V k)) (hI : ∀ c, IsPolymatroidalIdeal (I c))
    (hJ : IsPolymatroidalIdeal J) (hIne : ∀ c, I c ≠ ⊥) (i : ℕ) :
    IsIntegrallyClosedIdeal (homologicalMultiIdeal J I hJ hI i) :=
  homologicalMultiIdeal_integrallyClosed J I hJ hI hIne i

end SeveralColors

end FourPapers.Homological

end
end CheckedSource115

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "116: CommAlg.AuditSupport\n"

/-! ## Source: CommAlg.AuditSupport -/
section CheckedSource116

/-! # Reproducible transitive proof audits

These elaborator commands inspect the checked Lean environment. They do
not introduce mathematical declarations or axioms. The axiom guard fails
if any audited result uses anything beyond Lean's three standard axioms.
-/

open Lean Elab Command

elab "audit_standard_axioms " n:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
  let axs ← Lean.collectAxioms name
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for ax in axs do
    unless allowed.contains ax do
      throwError "Unapproved transitive axiom {ax} in {name}"
  logInfo m!"AXIOM AUDIT PASSED: {name}: {axs}"

meta def dependencyModule (env : Environment) (name : Name) : Name :=
  match env.getModuleIdxFor? name with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => env.mainModule

meta def isProjectModule (name : Name) : Bool :=
  let s := name.toString
  s.startsWith "CommAlg." || s == "CommAlg" || s.startsWith "TauCeti." ||
    s.startsWith "FourPapers." || s == "FourPapers" || s.startsWith "four_papers."

/-- Export the exact transitive declaration graph through every locally
proved module, stopping only at the pinned Lean/Mathlib library boundary. -/
elab "export_proof_dependencies " path:str "[" ns:ident,* "]" : command => do
  let roots ← ns.getElems.mapM fun n => liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
  let env := (← getEnv).setExporting false
  let mut todo := roots
  let mut cursor := 0
  let mut seen : NameSet := {}
  let mut nodes : Array Json := #[]
  let mut rootInfo : Array Json := #[]
  for name in roots do
    let axs ← Lean.collectAxioms name
    let some info := env.checked.get.find? name | throwError "Missing checked root {name}"
    let ty ← liftTermElabM <| Meta.ppExpr info.type
    rootInfo := rootInfo.push <| Json.mkObj
      [("name", toJson name.toString), ("type", toJson ty.pretty),
       ("axioms", toJson (axs.map Name.toString))]
  while cursor < todo.size do
    let name := todo[cursor]!
    cursor := cursor + 1
    if seen.contains name then continue
    seen := seen.insert name
    let modName := dependencyModule env name
    let boundary := !isProjectModule modName
    let some info := env.checked.get.find? name | throwError "Missing checked dependency {name}"
    let deps := if boundary then #[] else info.getUsedConstantsAsSet.toArray.qsort Name.lt
    todo := todo ++ deps
    nodes := nodes.push <| Json.mkObj
      [("name", toJson name.toString), ("module", toJson modName.toString),
       ("library_boundary", toJson boundary), ("dependencies", toJson (deps.map Name.toString))]
  let document := Json.mkObj
    [("format", toJson "Lean checked-environment dependency graph, version 1"),
     ("boundary", toJson "All FourPapers, CommAlg, and vendored TauCeti declarations are expanded; pinned Lean/Mathlib declarations are leaves."),
     ("roots", Json.arr rootInfo), ("nodes", Json.arr nodes)]
  let target : System.FilePath := path.getString
  if let some parent := target.parent then liftIO <| IO.FS.createDirAll parent
  liftIO <| IO.FS.writeFile target (document.pretty ++ "\n")
  logInfo m!"DEPENDENCY GRAPH: {nodes.size} checked declarations written to {path.getString}"

end CheckedSource116

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "117: CommAlg.AuditCore\n"

/-! ## Source: CommAlg.AuditCore -/
section CheckedSource117

/-! Kernel-environment audits of the main rank, stabilization, sharpness, homogenization, and normalization theorems. -/

set_option maxHeartbeats 0
set_option maxRecDepth 10000

audit_standard_axioms CommAlg.Polymatroid.homologicalShiftIdeal_partitionFormula
audit_standard_axioms CommAlg.Polymatroid.homologicalShiftIdeal_canonicalRank
audit_standard_axioms CommAlg.Polymatroid.bettiNumber_ideal_pos_iff
audit_standard_axioms CommAlg.Polymatroid.homologicalShift_powers
audit_standard_axioms CommAlg.Polymatroid.homologicalShift_twistedPowers
audit_standard_axioms CommAlg.Polymatroid.homologicalShift_severalColors
audit_standard_axioms CommAlg.Polymatroid.homologicalShiftIdeal_mul_le
audit_standard_axioms CommAlg.Polymatroid.squarefreeVeronese_shift_below
audit_standard_axioms CommAlg.Polymatroid.squarefreeVeronese_shift_at_threshold
audit_standard_axioms CommAlg.Polymatroid.squarefreeVeronese_shift_at_threshold_ne_bot
audit_standard_axioms CommAlg.Polymatroid.homogenizedHomologicalIdeal_eq_rankIdeal
audit_standard_axioms CommAlg.Polymatroid.homogenized_rankBase_iff_actualBetti
audit_standard_axioms CommAlg.Polymatroid.homogenizedHomologicalIdeal_polymatroidal
audit_standard_axioms CommAlg.Polymatroid.homogenizedHomologicalIdeal_degree
audit_standard_axioms CommAlg.Polymatroid.homogenizedHomologicalIdeal_canonicalRank
audit_standard_axioms CommAlg.Polymatroid.homogenizedShiftRank_on_original
audit_standard_axioms CommAlg.Polymatroid.homogenizedShiftRank_with_new_variable
audit_standard_axioms CommAlg.Polymatroid.gradedBettiNonzero_rankBases_field_independent
audit_standard_axioms CommAlg.homologicalPowerIdeal_integrallyClosed
audit_standard_axioms CommAlg.homologicalMultiIdeal_integrallyClosed

export_proof_dependencies ".lake/reports/audit/core_dependencies.json" [
  CommAlg.Polymatroid.homologicalShiftIdeal_partitionFormula,
  CommAlg.Polymatroid.homologicalShiftIdeal_canonicalRank,
  CommAlg.Polymatroid.bettiNumber_ideal_pos_iff,
  CommAlg.Polymatroid.homologicalShift_powers,
  CommAlg.Polymatroid.homologicalShift_twistedPowers,
  CommAlg.Polymatroid.homologicalShift_severalColors,
  CommAlg.Polymatroid.homologicalShiftIdeal_mul_le,
  CommAlg.Polymatroid.squarefreeVeronese_shift_below,
  CommAlg.Polymatroid.squarefreeVeronese_shift_at_threshold,
  CommAlg.Polymatroid.squarefreeVeronese_shift_at_threshold_ne_bot,
  CommAlg.Polymatroid.homogenizedHomologicalIdeal_eq_rankIdeal,
  CommAlg.Polymatroid.homogenized_rankBase_iff_actualBetti,
  CommAlg.Polymatroid.homogenizedHomologicalIdeal_polymatroidal,
  CommAlg.Polymatroid.homogenizedHomologicalIdeal_degree,
  CommAlg.Polymatroid.homogenizedHomologicalIdeal_canonicalRank,
  CommAlg.Polymatroid.homogenizedShiftRank_on_original,
  CommAlg.Polymatroid.homogenizedShiftRank_with_new_variable,
  CommAlg.Polymatroid.gradedBettiNonzero_rankBases_field_independent,
  CommAlg.homologicalPowerIdeal_integrallyClosed,
  CommAlg.homologicalMultiIdeal_integrallyClosed
]

end CheckedSource117

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "118: CommAlg.AuditConsequences\n"

/-! ## Source: CommAlg.AuditConsequences -/
section CheckedSource118

/-! Complete audits of actual projective dimensions, module generation, exact intervals, total support, and Tor foundations. -/

set_option maxHeartbeats 0
set_option maxRecDepth 10000

audit_standard_axioms CommAlg.ProjectiveDimension.rankIdeal_projectiveDimension
audit_standard_axioms CommAlg.ProjectiveDimension.polymatroidal_power_projectiveDimension
audit_standard_axioms CommAlg.ProjectiveDimension.polymatroidal_power_projectiveDimension_eventual
audit_standard_axioms CommAlg.homologicalPowerIdeal_generated_le
audit_standard_axioms CommAlg.homologicalMultiIdeal_generated_in_box
audit_standard_axioms CommAlg.homologicalPowerIdeal_eq_bot_of_above
audit_standard_axioms CommAlg.homologicalShift_power_nonzero_iff
audit_standard_axioms CommAlg.homologicalPower_minimal_degree_iff
audit_standard_axioms CommAlg.homologicalPower_generation_bound_iff
audit_standard_axioms CommAlg.homologicalPowerIdeal_eq_span_minimal
audit_standard_axioms CommAlg.homologicalPower_minimal_iff_rank_violation
audit_standard_axioms CommAlg.Polymatroid.powerShift_generator_endpoints
audit_standard_axioms CommAlg.Polymatroid.powerThreshold_eq_rationalCeiling
audit_standard_axioms CommAlg.Polymatroid.homological_homogenization
audit_standard_axioms CommAlg.Polymatroid.homological_homogenization_exists_rank
audit_standard_axioms CommAlg.Koszul.gradedTor_isInternal
audit_standard_axioms CommAlg.Koszul.derivedTor_nonzero_iff
audit_standard_axioms CommAlg.Koszul.finitePolynomialTorCoefficientIso
audit_standard_axioms CommAlg.Koszul.bettiNumber_pos_iff
audit_standard_axioms CommAlg.Koszul.finitePolynomialTor_nonzero_le_projectiveDimension

export_proof_dependencies ".lake/reports/audit/consequences_dependencies.json" [
  CommAlg.ProjectiveDimension.rankIdeal_projectiveDimension,
  CommAlg.ProjectiveDimension.polymatroidal_power_projectiveDimension,
  CommAlg.ProjectiveDimension.polymatroidal_power_projectiveDimension_eventual,
  CommAlg.homologicalPowerIdeal_generated_le,
  CommAlg.homologicalMultiIdeal_generated_in_box,
  CommAlg.homologicalPowerIdeal_eq_bot_of_above,
  CommAlg.homologicalShift_power_nonzero_iff,
  CommAlg.homologicalPower_minimal_degree_iff,
  CommAlg.homologicalPower_generation_bound_iff,
  CommAlg.homologicalPowerIdeal_eq_span_minimal,
  CommAlg.homologicalPower_minimal_iff_rank_violation,
  CommAlg.Polymatroid.powerShift_generator_endpoints,
  CommAlg.Polymatroid.powerThreshold_eq_rationalCeiling,
  CommAlg.Polymatroid.homological_homogenization,
  CommAlg.Polymatroid.homological_homogenization_exists_rank,
  CommAlg.Koszul.gradedTor_isInternal,
  CommAlg.Koszul.derivedTor_nonzero_iff,
  CommAlg.Koszul.finitePolynomialTorCoefficientIso,
  CommAlg.Koszul.bettiNumber_pos_iff,
  CommAlg.Koszul.finitePolynomialTor_nonzero_le_projectiveDimension
]

end CheckedSource118

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "119: CommAlg.Audit\n"

/-! ## Source: CommAlg.Audit -/
section CheckedSource119

/-! All principal theorems are guarded against unapproved transitive axioms. -/

end CheckedSource119

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile ".lake/reports/audit/homological/compile_progress.txt" "120: FourPapers.Homological.Audit\n"

/-! ## Source: FourPapers.Homological.Audit -/
section CheckedSource120

set_option autoImplicit false

/-! The public paper-numbered results and their semantic bridges are checked
against precisely Lean's standard logical axioms. -/

set_option maxHeartbeats 0
set_option maxRecDepth 10000

audit_standard_axioms FourPapers.Homological.theorem_1_1
audit_standard_axioms FourPapers.Homological.theorem_1_1_twisted
audit_standard_axioms FourPapers.Homological.theorem_1_1_generation
audit_standard_axioms FourPapers.Homological.theorem_1_2
audit_standard_axioms FourPapers.Homological.theorem_1_2_canonical
audit_standard_axioms FourPapers.Homological.corollary_4_1
audit_standard_axioms FourPapers.Homological.corollary_4_1_generation
audit_standard_axioms FourPapers.Homological.proposition_4_2
audit_standard_axioms FourPapers.Homological.corollary_4_3
audit_standard_axioms FourPapers.Homological.corollary_4_3_eventual
audit_standard_axioms FourPapers.Homological.theorem_4_4_zero
audit_standard_axioms FourPapers.Homological.theorem_4_4
audit_standard_axioms FourPapers.Homological.theorem_4_4_threshold_formula
audit_standard_axioms FourPapers.Homological.theorem_5_1
audit_standard_axioms FourPapers.Homological.theorem_5_1_rank
audit_standard_axioms FourPapers.Homological.theorem_5_1_field_independent
audit_standard_axioms FourPapers.Homological.theorem_6_1
audit_standard_axioms FourPapers.Homological.corollary_6_2

audit_standard_axioms CommAlg.Koszul.finitePolynomialResolution
audit_standard_axioms CommAlg.Koszul.finitePolynomialTorIso
audit_standard_axioms CommAlg.Koszul.finitePolynomialTorCoefficientIso
audit_standard_axioms CommAlg.Koszul.coefficientTorIso
audit_standard_axioms CommAlg.Koszul.homogeneousFacesIso
audit_standard_axioms CommAlg.Koszul.gradedTor_isInternal
audit_standard_axioms CommAlg.Koszul.bettiNumber_pos_iff
audit_standard_axioms CommAlg.Matroid.independence_nonzeroHomology_iff
audit_standard_axioms CommAlg.Polymatroid.rankBases_canonical
audit_standard_axioms CommAlg.Polymatroid.rank_base_minkowski
audit_standard_axioms CommAlg.Polymatroid.powerThreshold_eq_rationalCeiling
audit_standard_axioms CommAlg.Weight.integrallyClosed_of_weight_bounds

export_proof_dependencies ".lake/reports/audit/homological/principal_dependencies.json" [
  FourPapers.Homological.theorem_1_1,
  FourPapers.Homological.theorem_1_1_twisted,
  FourPapers.Homological.theorem_1_1_generation,
  FourPapers.Homological.theorem_1_2,
  FourPapers.Homological.theorem_1_2_canonical,
  FourPapers.Homological.corollary_4_1,
  FourPapers.Homological.corollary_4_1_generation,
  FourPapers.Homological.proposition_4_2,
  FourPapers.Homological.corollary_4_3,
  FourPapers.Homological.corollary_4_3_eventual,
  FourPapers.Homological.theorem_4_4_zero,
  FourPapers.Homological.theorem_4_4,
  FourPapers.Homological.theorem_4_4_threshold_formula,
  FourPapers.Homological.theorem_5_1,
  FourPapers.Homological.theorem_5_1_rank,
  FourPapers.Homological.theorem_5_1_field_independent,
  FourPapers.Homological.theorem_6_1,
  FourPapers.Homological.corollary_6_2,
  CommAlg.Polymatroid.homologicalShiftIdeal_partitionFormula,
  CommAlg.Polymatroid.homologicalShiftIdeal_canonicalRank,
  CommAlg.Polymatroid.gradedBettiNonzero_rankBases_iff,
  CommAlg.Polymatroid.homologicalShift_powers,
  CommAlg.Polymatroid.homologicalShift_twistedPowers,
  CommAlg.homologicalPowerIdeal_generated_le,
  CommAlg.Polymatroid.homologicalShift_severalColors,
  CommAlg.homologicalMultiIdeal_generated_in_box,
  CommAlg.Polymatroid.squarefreeVeronese_shift_below,
  CommAlg.Polymatroid.squarefreeVeronese_shift_at_threshold,
  CommAlg.Polymatroid.squarefreeVeronese_shift_at_threshold_ne_bot,
  CommAlg.ProjectiveDimension.rankIdeal_power_projectiveDimension,
  CommAlg.ProjectiveDimension.rankIdeal_power_projectiveDimension_eventual,
  CommAlg.homologicalPowerIdeal_eq_bot_of_above,
  CommAlg.homologicalShift_power_nonzero_iff,
  CommAlg.homologicalPower_minimal_degree_iff,
  CommAlg.homologicalPower_generation_bound_iff,
  CommAlg.homologicalPowerIdeal_eq_span_minimal,
  CommAlg.homologicalPower_minimal_iff_rank_violation,
  CommAlg.Polymatroid.powerShift_generator_endpoints,
  CommAlg.Polymatroid.powerThreshold_eq_rationalCeiling,
  CommAlg.Polymatroid.homological_homogenization,
  CommAlg.Polymatroid.homogenizedHomologicalIdeal_eq_rankIdeal,
  CommAlg.Polymatroid.homogenizedShiftRank_active_original,
  CommAlg.Polymatroid.homogenizedShiftRank_with_new_variable,
  CommAlg.Polymatroid.gradedBettiNonzero_rankBases_field_independent,
  CommAlg.homologicalPowerIdeal_integrallyClosed,
  CommAlg.homologicalMultiIdeal_integrallyClosed,
  CommAlg.Koszul.finitePolynomialResolution,
  CommAlg.Koszul.finitePolynomialTorIso,
  CommAlg.Koszul.finitePolynomialTorCoefficientIso,
  CommAlg.Koszul.coefficientTorIso,
  CommAlg.Koszul.homogeneousFacesIso,
  CommAlg.Koszul.gradedTor_isInternal,
  CommAlg.Koszul.bettiNumber_pos_iff,
  CommAlg.Matroid.independence_nonzeroHomology_iff,
  CommAlg.Polymatroid.rankBases_canonical,
  CommAlg.Polymatroid.rank_base_minkowski,
  CommAlg.Weight.integrallyClosed_of_weight_bounds
]

end CheckedSource120
