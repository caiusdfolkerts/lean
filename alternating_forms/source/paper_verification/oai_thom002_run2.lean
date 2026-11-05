module

public import paper_verification.oai_thom001_run1
import all paper_verification.oai_thom001_run1
public import Mathlib.GroupTheory.Perm.Fin
import all Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Algebra.Module.Submodule.Equiv
import all Mathlib.Algebra.Module.Submodule.Equiv
public import paper_verification.oai_thom000_run1
import all paper_verification.oai_thom000_run1
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import all Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
import all Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
public import Mathlib.Analysis.Convex.Contractible
import all Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Complex.Basic
import all Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Homology.Functor
import all Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.Homotopy
import all Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
import all Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
import all Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import all Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
public import Mathlib.Topology.Homotopy.Equiv
import all Mathlib.Topology.Homotopy.Equiv
public import Mathlib.Analysis.InnerProductSpace.PiL2
import all Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.Instances.Sphere
import all Mathlib.Geometry.Manifold.Instances.Sphere
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.PrettyPrinter

set_option Elab.async false

@[expose] public section ComponentSource_0
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.SubdivisionBoundary -/

/-! # Subdivision Boundary -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.SubdivisionBoundary

noncomputable section

/-!
# Boundary compatibility of barycentric subdivision

The outer-face geometry identifies the remaining boundary terms after the
proved interior cancellation. All maps are the actual standard-simplex maps.
-/

open _root_.CategoryTheory
open scoped BigOperators Classical Simplicial

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Cycles

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

variable {ι κ η : Type*} [Fintype ι] [Fintype κ] [Fintype η]

private theorem zsmul_finset_sum {A J : Type*} [AddCommGroup A]
    (a : ℤ) (s : Finset J) (f : J → A) :
    a • ∑ j ∈ s, f j = ∑ j ∈ s, a • f j :=
  map_sum (zsmulAddGroupHom a) f s

omit [Fintype ι] in
/-- The ambient vertex interpolation map acts on a coordinate vector as expected. -/
@[simp]
theorem simplexVertexLinearMap_piSingle [DecidableEq κ]
    (v : κ → Convexity.StdSimplex ℝ ι) (k : κ) (a : ℝ) :
    BarycentricSimplex.Cycles.simplexVertexLinearMap v (Pi.single k a) = a • (v k : ι → ℝ) := by
  funext i
  simp [BarycentricSimplex.Cycles.simplexVertexLinearMap_apply, Pi.single_apply]

omit [Fintype ι] in
/-- Vertex interpolation is natural under a map of source vertices. -/
theorem simplexVertexLinearMap_precomp (v : κ → Convexity.StdSimplex ℝ ι) (f : η → κ) :
    (BarycentricSimplex.Cycles.simplexVertexLinearMap v).comp (FunOnFinite.linearMap ℝ ℝ f) =
      BarycentricSimplex.Cycles.simplexVertexLinearMap (fun k => v (f k)) := by
  classical
  apply LinearMap.pi_ext
  intro k a
  simp only [LinearMap.comp_apply, FunOnFinite.linearMap_piSingle,
    simplexVertexLinearMap_piSingle]

/-- Vertex interpolation is natural under a map of target vertices. -/
theorem simplexVertexLinearMap_postcomp (v : κ → Convexity.StdSimplex ℝ ι) (f : ι → η) :
    (FunOnFinite.linearMap ℝ ℝ f).comp (BarycentricSimplex.Cycles.simplexVertexLinearMap v) =
      BarycentricSimplex.Cycles.simplexVertexLinearMap (fun k => Convexity.StdSimplex.map f (v k)) := by
  classical
  apply LinearMap.pi_ext
  intro k a
  simp only [LinearMap.comp_apply, simplexVertexLinearMap_piSingle, map_smul,
    Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex.map_coordinates]

/-- The source naturality identity holds for the genuine continuous simplex maps. -/
theorem simplexVertexMap_precomp_map (v : κ → Convexity.StdSimplex ℝ ι) (f : η → κ)
    (x : Convexity.StdSimplex ℝ η) :
    BarycentricSimplex.Cycles.simplexVertexMap v (Convexity.StdSimplex.map f x) =
      BarycentricSimplex.Cycles.simplexVertexMap (fun k => v (f k)) x := by
  apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ _).injective
  simp only [BarycentricSimplex.Cycles.simplexVertexMap_eq_affine, BarycentricSimplex.Cycles.simplexVertexAffineMap,
    LinearMap.coe_toAffineMap, Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex.map_coordinates]
  exact congrArg (fun L : (η → ℝ) →ₗ[ℝ] (ι → ℝ) => L x)
    (simplexVertexLinearMap_precomp v f)

/-- The target naturality identity holds for the genuine continuous simplex maps. -/
theorem simplexVertexMap_postcomp_map (v : κ → Convexity.StdSimplex ℝ ι) (f : ι → η)
    (x : Convexity.StdSimplex ℝ κ) :
    Convexity.StdSimplex.map f (BarycentricSimplex.Cycles.simplexVertexMap v x) =
      BarycentricSimplex.Cycles.simplexVertexMap (fun k => Convexity.StdSimplex.map f (v k)) x := by
  apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ _).injective
  simp only [BarycentricSimplex.Cycles.simplexVertexMap_eq_affine, BarycentricSimplex.Cycles.simplexVertexAffineMap,
    LinearMap.coe_toAffineMap, Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex.map_coordinates]
  exact congrArg (fun L : (κ → ℝ) →ₗ[ℝ] (η → ℝ) => L x)
    (simplexVertexLinearMap_postcomp v f)

/-- An injective vertex map carries the actual face barycenter to the mapped face barycenter. -/
theorem map_faceBarycenter (f : κ ↪ ι) (s : Finset κ) (hs : s.Nonempty) :
    Convexity.StdSimplex.map f (BarycentricSimplex.Cycles.faceBarycenter s hs) = BarycentricSimplex.Cycles.faceBarycenter (s.map f) hs.map := by
  classical
  apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ _).injective
  change ((Convexity.StdSimplex.map f (BarycentricSimplex.Cycles.faceBarycenter s hs)).weights : ι → ℝ) =
    ((BarycentricSimplex.Cycles.faceBarycenter (s.map f) hs.map).weights : ι → ℝ)
  rw [Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex.map_coordinates]
  change FunOnFinite.linearMap ℝ ℝ f (BarycentricSimplex.Cycles.faceBarycenter s hs : κ → ℝ) =
    (BarycentricSimplex.Cycles.faceBarycenter (s.map f) hs.map : ι → ℝ)
  rw [BarycentricSimplex.Cycles.faceBarycenter_eq_centroid s hs, BarycentricSimplex.Cycles.faceBarycenter_eq_centroid (s.map f) hs.map,
    BarycentricMesh.centroid_eq_inv_card_sum s hs,
    BarycentricMesh.centroid_eq_inv_card_sum (s.map f) hs.map]
  simp only [map_smul, map_sum, Finset.card_map, Finset.sum_map,
    FunOnFinite.linearMap_piSingle]

/-- Initial faces of an inserted permutation are images of the smaller initial faces. -/
theorem outer_initial_face_eq {n : ℕ} (i : Fin (n + 2))
    (σ : Equiv.Perm (Fin (n + 2))) (τ : Equiv.Perm (Fin (n + 1)))
    (hσ : ∀ k, σ k.castSucc = i.succAbove (τ k)) (k : Fin (n + 1)) :
    (Finset.Iic k.castSucc).map σ.toEmbedding =
      ((Finset.Iic k).map τ.toEmbedding).map i.succAboveEmb := by
  rw [← Fin.map_castSuccEmb_Iic k, Finset.map_map, Finset.map_map]
  apply congrArg (fun e : Fin (n + 1) ↪ Fin (n + 2) => (Finset.Iic k).map e)
  apply Function.Embedding.ext
  intro j
  exact hσ j

/-- The last face of an inserted barycentric cell is exactly the corresponding
smaller cell followed by the original face inclusion. -/
theorem barycentricSubdivisionMap_comp_outer_face {n : ℕ}
    (i : Fin (n + 2)) (σ : Equiv.Perm (Fin (n + 2)))
    (τ : Equiv.Perm (Fin (n + 1)))
    (hσ : ∀ k, σ k.castSucc = i.succAbove (τ k)) :
    (BarycentricSimplex.Cycles.barycentricSubdivisionMap σ).comp
        (AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.standardSimplexFace (Fin.last (n + 1))) =
      (AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.standardSimplexFace i).comp
        (BarycentricSimplex.Cycles.barycentricSubdivisionMap τ) := by
  apply ContinuousMap.ext
  intro x
  change BarycentricSimplex.Cycles.simplexVertexMap
      (fun k => BarycentricSimplex.Cycles.faceBarycenter ((BarycentricSimplex.Cycles.permutationBarycentricFlag σ).face k)
        ((BarycentricSimplex.Cycles.permutationBarycentricFlag σ).nonempty k))
      (Convexity.StdSimplex.map (Fin.last (n + 1)).succAbove x) =
    Convexity.StdSimplex.map i.succAbove (BarycentricSimplex.Cycles.simplexVertexMap
      (fun k => BarycentricSimplex.Cycles.faceBarycenter ((BarycentricSimplex.Cycles.permutationBarycentricFlag τ).face k)
        ((BarycentricSimplex.Cycles.permutationBarycentricFlag τ).nonempty k)) x)
  rw [simplexVertexMap_precomp_map, simplexVertexMap_postcomp_map]
  apply congrArg (fun v => BarycentricSimplex.Cycles.simplexVertexMap v x)
  funext k
  simp only [Fin.succAbove_last_apply, BarycentricSimplex.Cycles.permutationBarycentricFlag]
  have h := map_faceBarycenter i.succAboveEmb
    ((Finset.Iic k).map τ.toEmbedding) ((BarycentricSimplex.Cycles.permutationBarycentricFlag τ).nonempty k)
  refine Eq.trans ?_ (by simpa only [Fin.coe_succAboveEmb] using h.symm)
  apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ _).injective
  funext a
  simp only [BarycentricSimplex.Cycles.faceBarycenter_apply]
  rw [outer_initial_face_eq i σ τ hσ k]

/-- The unit simplex generator, with the integral singular-chain model fixed explicitly. -/
def integralSimplexChain (X : TopCat.{0}) {n : ℕ} (s : SubdivisionOperator.Cycles.SingularSimplex X n) :
    (LocalHomology.Cycles.integralSingularChains X).X n :=
  (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) s 1

/-- The subdivision formula on the unit simplex generators used in the chain complex. -/
theorem subdivisionDegree_simplexChain (X : TopCat.{0}) (n : ℕ)
    (s : SubdivisionOperator.Cycles.SingularSimplex X n) :
    SubdivisionOperator.Cycles.subdivisionDegree X n (integralSimplexChain X s) =
      ∑ σ : Equiv.Perm (Fin (n + 1)), (Equiv.Perm.sign σ : ℤ) •
        integralSimplexChain X
          (SubdivisionOperator.Cycles.subdivisionSimplex X n s σ) := by
  rw [integralSimplexChain, SubdivisionOperator.Cycles.subdivisionDegree_simplex]
  apply Finset.sum_congr rfl
  intro σ _
  simpa only [integralSimplexChain, zsmul_eq_mul, mul_one] using!
    map_zsmul ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ)
      (SubdivisionOperator.Cycles.subdivisionSimplex X n s σ)).hom (Equiv.Perm.sign σ : ℤ) (1 : ℤ)

/-- The actual singular face of a subdivided simplex has the expected composite map. -/
theorem subdivisionSimplex_face_continuous (X : TopCat.{0}) (n : ℕ)
    (s : SubdivisionOperator.Cycles.SingularSimplex X (n + 1)) (σ : Equiv.Perm (Fin (n + 2)))
    (i : Fin (n + 2)) :
    AlgebraicTopology.Cohomology.Singular.Coefficients.singularSimplicesEquivContinuousMap X n
      ((TopCat.toSSet.obj X).δ i (SubdivisionOperator.Cycles.subdivisionSimplex X (n + 1) s σ)) =
      (AlgebraicTopology.Cohomology.Singular.Coefficients.singularSimplicesEquivContinuousMap X (n + 1) s).comp
        ((BarycentricSimplex.Cycles.barycentricSubdivisionMap σ).comp (AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.standardSimplexFace i)) := by
  rw [AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.singularSimplicesEquivContinuousMap_face]
  change (X.toSSetObjEquiv (.op ⦋n + 1⦌) (SubdivisionOperator.Cycles.subdivisionSimplex X (n + 1) s σ)).comp _ = _
  rw [SubdivisionOperator.Cycles.subdivisionSimplex_toContinuousMap]
  rfl

/-- The paired interior faces are equal as actual singular simplices. -/
theorem subdivisionSimplex_inner_face_swap (X : TopCat.{0}) (n : ℕ)
    (s : SubdivisionOperator.Cycles.SingularSimplex X (n + 1)) (σ : Equiv.Perm (Fin (n + 2)))
    (j : Fin (n + 1)) :
    (TopCat.toSSet.obj X).δ j.castSucc
      (SubdivisionOperator.Cycles.subdivisionSimplex X (n + 1) s (σ * Equiv.swap j.castSucc j.succ)) =
      (TopCat.toSSet.obj X).δ j.castSucc (SubdivisionOperator.Cycles.subdivisionSimplex X (n + 1) s σ) := by
  apply (AlgebraicTopology.Cohomology.Singular.Coefficients.singularSimplicesEquivContinuousMap X n).injective
  rw [subdivisionSimplex_face_continuous, subdivisionSimplex_face_continuous,
    SubdivisionSigns.Cycles.barycentricSubdivisionMap_comp_inner_face_swap]

/-- Outer-face compatibility holds at the actual singular-simplex level. -/
theorem subdivisionSimplex_outer_face (X : TopCat.{0}) (n : ℕ)
    (s : SubdivisionOperator.Cycles.SingularSimplex X (n + 1)) (i : Fin (n + 2))
    (σ : Equiv.Perm (Fin (n + 2))) (τ : Equiv.Perm (Fin (n + 1)))
    (hσ : ∀ k, σ k.castSucc = i.succAbove (τ k)) :
    (TopCat.toSSet.obj X).δ (Fin.last (n + 1)) (SubdivisionOperator.Cycles.subdivisionSimplex X (n + 1) s σ) =
      SubdivisionOperator.Cycles.subdivisionSimplex X n ((TopCat.toSSet.obj X).δ i s) τ := by
  apply (AlgebraicTopology.Cohomology.Singular.Coefficients.singularSimplicesEquivContinuousMap X n).injective
  rw [subdivisionSimplex_face_continuous]
  change _ = X.toSSetObjEquiv (.op ⦋n⦌) (SubdivisionOperator.Cycles.subdivisionSimplex X n _ τ)
  rw [SubdivisionOperator.Cycles.subdivisionSimplex_toContinuousMap]
  change _ = (AlgebraicTopology.Cohomology.Singular.Coefficients.singularSimplicesEquivContinuousMap X n
    ((TopCat.toSSet.obj X).δ i s)).comp _
  rw [AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.singularSimplicesEquivContinuousMap_face,
    barycentricSubdivisionMap_comp_outer_face i σ τ hσ]
  rfl

/-- Each interior contribution vanishes in the unit-generator chain notation. -/
theorem subdivision_inner_chain_sum_zero (X : TopCat.{0}) (n : ℕ)
    (s : SubdivisionOperator.Cycles.SingularSimplex X (n + 1)) (j : Fin (n + 1)) :
    (∑ σ : Equiv.Perm (Fin (n + 2)),
      ((Equiv.Perm.sign σ : ℤ) * (-1 : ℤ) ^ j.val) •
        integralSimplexChain X
          ((TopCat.toSSet.obj X).δ j.castSucc (SubdivisionOperator.Cycles.subdivisionSimplex X (n + 1) s σ))) = 0 := by
  simp only [mul_smul]
  apply SubdivisionSigns.Cycles.sum_perm_sign_eq_zero_of_swap_invariant j.castSucc j.succ
    (ne_of_lt j.castSucc_lt_succ)
  intro σ
  rw [subdivisionSimplex_inner_face_swap]

/-- The outer faces reindex exactly by an original face and its subdivision cell,
with the correct integral orientation coefficient. -/
theorem subdivision_outer_chain_sum (X : TopCat.{0}) (n : ℕ)
    (s : SubdivisionOperator.Cycles.SingularSimplex X (n + 1)) :
    (∑ σ : Equiv.Perm (Fin (n + 2)),
      ((Equiv.Perm.sign σ : ℤ) * (-1 : ℤ) ^ (n + 1)) •
        integralSimplexChain X
          ((TopCat.toSSet.obj X).δ (Fin.last (n + 1))
            (SubdivisionOperator.Cycles.subdivisionSimplex X (n + 1) s σ))) =
      ∑ i : Fin (n + 2), ∑ τ : Equiv.Perm (Fin (n + 1)),
        ((-1 : ℤ) ^ i.val * (Equiv.Perm.sign τ : ℤ)) •
          integralSimplexChain X
            (SubdivisionOperator.Cycles.subdivisionSimplex X n ((TopCat.toSSet.obj X).δ i s) τ) := by
  rw [← (PermutationLast.Cycles.insertLastPermutationEquiv n).sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro τ _
  simp only [PermutationLast.Cycles.insertLastPermutationEquiv_apply, PermutationLast.Cycles.sign_insertLastPermutation]
  rw [subdivisionSimplex_outer_face X n s i (PermutationLast.Cycles.insertLastPermutation i τ) τ
    (PermutationLast.Cycles.insertLastPermutation_apply_castSucc i τ)]

/-- The unit-generator boundary formula in the integral singular-chain model. -/
theorem integralSimplexChain_boundary (X : TopCat.{0}) (n : ℕ)
    (s : SubdivisionOperator.Cycles.SingularSimplex X (n + 1)) :
    (LocalHomology.Cycles.integralSingularChains X).d (n + 1) n
      (integralSimplexChain X s) =
        ∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.val) •
          integralSimplexChain X
            ((TopCat.toSSet.obj X).δ i s) := by
  simpa only [integralSimplexChain, AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain] using!
    (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain_boundary (R := ℤ) (TopCat.toSSet.obj X) s)

/-- Expanding the actual boundary of a subdivided simplex gives the finite sum
over all its geometric faces and all permutation cells. -/
theorem boundary_subdivision_simplexChain_expansion (X : TopCat.{0}) (n : ℕ)
    (s : SubdivisionOperator.Cycles.SingularSimplex X (n + 1)) :
    (LocalHomology.Cycles.integralSingularChains X).d (n + 1) n
        (SubdivisionOperator.Cycles.subdivisionDegree X (n + 1)
          (integralSimplexChain X s)) =
      ∑ i : Fin (n + 2), ∑ σ : Equiv.Perm (Fin (n + 2)),
        ((Equiv.Perm.sign σ : ℤ) * (-1 : ℤ) ^ i.val) •
          integralSimplexChain X
            ((TopCat.toSSet.obj X).δ i (SubdivisionOperator.Cycles.subdivisionSimplex X (n + 1) s σ)) := by
  rw [subdivisionDegree_simplexChain, map_sum]
  simp only [map_zsmul, integralSimplexChain_boundary,
    zsmul_finset_sum, ← mul_zsmul]
  exact Finset.sum_comm

/-- Barycentric subdivision commutes with the actual singular boundary on each
unit simplex generator. Interior faces cancel and the outer faces are precisely
the subdivisions of the original boundary. -/
theorem boundary_subdivision_simplexChain (X : TopCat.{0}) (n : ℕ)
    (s : SubdivisionOperator.Cycles.SingularSimplex X (n + 1)) :
    (LocalHomology.Cycles.integralSingularChains X).d (n + 1) n
        (SubdivisionOperator.Cycles.subdivisionDegree X (n + 1)
          (integralSimplexChain X s)) =
      SubdivisionOperator.Cycles.subdivisionDegree X n ((LocalHomology.Cycles.integralSingularChains X).d (n + 1) n
        (integralSimplexChain X s)) := by
  rw [boundary_subdivision_simplexChain_expansion, Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, subdivision_inner_chain_sum_zero,
    Finset.sum_const_zero, zero_add, Fin.val_last]
  rw [subdivision_outer_chain_sum, integralSimplexChain_boundary, map_sum]
  simp only [map_zsmul, subdivisionDegree_simplexChain, zsmul_finset_sum, ← mul_zsmul]

/-- The actual degreewise linear maps commute with the actual singular differential. -/
theorem subdivisionDegree_comm (X : TopCat.{0}) (n : ℕ) :
    ((LocalHomology.Cycles.integralSingularChains X).d (n + 1) n).hom.comp (SubdivisionOperator.Cycles.subdivisionDegree X (n + 1)) =
      (SubdivisionOperator.Cycles.subdivisionDegree X n).comp ((LocalHomology.Cycles.integralSingularChains X).d (n + 1) n).hom := by
  apply AlgebraicTopology.Cohomology.Singular.ChainDual.chainFunctional_ext (TopCat.toSSet.obj X)
    ((LocalHomology.Cycles.integralSingularChains X).X n)
  intro s
  simpa only [integralSimplexChain, AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain,
    LinearMap.comp_apply] using! boundary_subdivision_simplexChain X n s

/-- Pointwise boundary compatibility for arbitrary actual integral singular chains. -/
theorem subdivisionDegree_boundary (X : TopCat.{0}) (n : ℕ)
    (c : (LocalHomology.Cycles.integralSingularChains X).X (n + 1)) :
    (LocalHomology.Cycles.integralSingularChains X).d (n + 1) n (SubdivisionOperator.Cycles.subdivisionDegree X (n + 1) c) =
      SubdivisionOperator.Cycles.subdivisionDegree X n ((LocalHomology.Cycles.integralSingularChains X).d (n + 1) n c) :=
  LinearMap.congr_fun (subdivisionDegree_comm X n) c

/-- The genuine integral barycentric subdivision chain map. Its components are
the explicitly constructed signed sums of geometric subdivision cells. -/
def subdivisionChainMap (X : TopCat.{0}) :
    LocalHomology.Cycles.integralSingularChains X ⟶ LocalHomology.Cycles.integralSingularChains X :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (SubdivisionOperator.Cycles.subdivisionDegree X n)) (fun n => by
    apply ModuleCat.hom_ext
    exact subdivisionDegree_comm X n)

/-- The chain-map packaging preserves the previously defined degreewise operator. -/
@[simp]
theorem subdivisionChainMap_f (X : TopCat.{0}) (n : ℕ) :
    ((subdivisionChainMap X).f n).hom = SubdivisionOperator.Cycles.subdivisionDegree X n := rfl

end Cycles

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.SubdivisionBoundary
end ComponentSource_0

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.SubdivisionBoundary"

@[expose] public section ComponentSource_1
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.SmallSubdivision -/

/-! # Small Subdivision -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.SmallSubdivision.Cycles

noncomputable section

/-!
# Actual barycentric subdivision on the small-chain complex

The signed ambient operator preserves the genuine image of small chains because
its cells have smaller geometric ranges. We restrict that actual linear map
through the injective chain inclusion. Boundary compatibility is then proved
from the already established ambient boundary identity, using injectivity.
-/

open _root_.CategoryTheory
open scoped Simplicial

variable (X : TopCat.{0}) {J : Type} (U : J → Set X)

/-- Actual barycentric subdivision preserves the actual image of small chains. -/
theorem subdivisionDegree_preserves_smallChainImage (n : ℕ)
    (c : (LocalHomology.Cycles.integralSingularChains X).X n)
    (hc : c ∈ LinearMap.range ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n).hom) :
    SubdivisionOperator.Cycles.subdivisionDegree X n c ∈
      LinearMap.range ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n).hom := by
  apply (SmallChainImage.Cycles.mem_range_smallIntegralChainInclusion_iff X U n _).2
  intro t ht
  obtain ⟨s, hs, hsub⟩ := SubdivisionOperator.Cycles.support_subdivisionDegree_range X n c t ht
  have hsmall := (SmallChainImage.Cycles.mem_range_smallIntegralChainInclusion_iff X U n c).1 hc s hs
  change ∃ i, Set.range (X.toSSetObjEquiv (.op ⦋n⦌) t) ⊆ U i
  obtain ⟨i, hi⟩ := hsmall
  exact ⟨i, hsub.trans hi⟩

/-- The unique linear restriction of the actual ambient subdivision operator
to genuine small chains. -/
def smallSubdivisionDegree (n : ℕ) :
    (SmallChainImage.Cycles.integralSmallSingularChains X U).X n →ₗ[ℤ]
      (SmallChainImage.Cycles.integralSmallSingularChains X U).X n :=
  LinearMap.codRestrictOfInjective
    ((SubdivisionOperator.Cycles.subdivisionDegree X n).comp ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n).hom)
    ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n).hom
    (SmallChainImage.Cycles.smallIntegralChainInclusion_injective X U n)
    (fun c => subdivisionDegree_preserves_smallChainImage X U n _
      (LinearMap.mem_range_self _ c))

/-- Inclusion carries the restricted operator back to the given signed ambient operator. -/
@[simp]
theorem smallSubdivisionDegree_inclusion (n : ℕ)
    (c : (SmallChainImage.Cycles.integralSmallSingularChains X U).X n) :
    (SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n (smallSubdivisionDegree X U n c) =
      SubdivisionOperator.Cycles.subdivisionDegree X n ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n c) := by
  simp [smallSubdivisionDegree]

/-- The preceding compatibility as an equality of actual linear maps. -/
theorem smallSubdivisionDegree_intertwining (n : ℕ) :
    ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n).hom.comp (smallSubdivisionDegree X U n) =
      (SubdivisionOperator.Cycles.subdivisionDegree X n).comp ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n).hom := by
  ext c
  exact smallSubdivisionDegree_inclusion X U n c

/-- The inclusion commutes with every actual iterate. -/
theorem smallSubdivisionDegree_iterate_inclusion (n N : ℕ)
    (c : (SmallChainImage.Cycles.integralSmallSingularChains X U).X n) :
    (SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n ((smallSubdivisionDegree X U n)^[N] c) =
      (SubdivisionOperator.Cycles.subdivisionDegree X n)^[N] ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n c) := by
  induction N with
  | zero => rfl
  | succ N ih =>
      rw [Function.iterate_succ_apply', smallSubdivisionDegree_inclusion, ih,
        Function.iterate_succ_apply']

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Elementwise differential compatibility of the genuine small-chain inclusion. -/
theorem smallIntegralChainInclusion_d (i j : ℕ)
    (c : (SmallChainImage.Cycles.integralSmallSingularChains X U).X i) :
    (SmallChainImage.Cycles.smallIntegralChainInclusion X U).f j ((SmallChainImage.Cycles.integralSmallSingularChains X U).d i j c) =
      (LocalHomology.Cycles.integralSingularChains X).d i j ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f i c) := by
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using!
    congrArg (fun f : (SmallChainImage.Cycles.integralSmallSingularChains X U).X i ⟶
      (LocalHomology.Cycles.integralSingularChains X).X j => f.hom c)
      ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).comm i j).symm

/-- Actual small subdivision commutes with the actual small-chain boundary. -/
theorem smallSubdivisionDegree_boundary (n : ℕ)
    (c : (SmallChainImage.Cycles.integralSmallSingularChains X U).X (n + 1)) :
    (SmallChainImage.Cycles.integralSmallSingularChains X U).d (n + 1) n
        (smallSubdivisionDegree X U (n + 1) c) =
      smallSubdivisionDegree X U n ((SmallChainImage.Cycles.integralSmallSingularChains X U).d (n + 1) n c) := by
  apply SmallChainImage.Cycles.smallIntegralChainInclusion_injective X U n
  simpa only [smallIntegralChainInclusion_d, smallSubdivisionDegree_inclusion] using
    SubdivisionBoundary.Cycles.subdivisionDegree_boundary X n ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f (n + 1) c)

/-- Boundary compatibility as the linear-map equality used in chain-map construction. -/
theorem smallSubdivisionDegree_comm (n : ℕ) :
    ((SmallChainImage.Cycles.integralSmallSingularChains X U).d (n + 1) n).hom.comp
        (smallSubdivisionDegree X U (n + 1)) =
      (smallSubdivisionDegree X U n).comp
        ((SmallChainImage.Cycles.integralSmallSingularChains X U).d (n + 1) n).hom := by
  ext c
  exact smallSubdivisionDegree_boundary X U n c

/-- The genuine signed barycentric subdivision chain map on small chains. -/
def smallSubdivisionChainMap :
    SmallChainImage.Cycles.integralSmallSingularChains X U ⟶ SmallChainImage.Cycles.integralSmallSingularChains X U :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (smallSubdivisionDegree X U n))
    (fun n => by
      apply ModuleCat.hom_ext
      exact smallSubdivisionDegree_comm X U n)

@[simp]
theorem smallSubdivisionChainMap_f (n : ℕ) :
    ((smallSubdivisionChainMap X U).f n).hom = smallSubdivisionDegree X U n := rfl

/-- Actual chain-map intertwining, in the orientation required by the
small-chain quasi-isomorphism criterion. -/
theorem smallSubdivisionChainMap_intertwining :
    SmallChainImage.Cycles.smallIntegralChainInclusion X U ≫ SubdivisionBoundary.Cycles.subdivisionChainMap X =
      smallSubdivisionChainMap X U ≫ SmallChainImage.Cycles.smallIntegralChainInclusion X U := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  exact (smallSubdivisionDegree_intertwining X U n).symm

/-- Eventual image membership formulated directly using the assembled actual
ambient subdivision chain map. -/
theorem exists_subdivisionChainMap_iterate_small_preimage
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i)
    {n : ℕ} (c : (LocalHomology.Cycles.integralSingularChains X).X n) :
    ∃ N : ℕ, ∃ b : (SmallChainImage.Cycles.integralSmallSingularChains X U).X n,
      (SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n b =
        ((SubdivisionBoundary.Cycles.subdivisionChainMap X).f n)^[N] c :=
  SmallChainImage.Cycles.exists_subdivisionDegree_iterate_smallChain_preimage X U hopen hcover c

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.SmallSubdivision.Cycles
end ComponentSource_1

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.SmallSubdivision"

@[expose] public section ComponentSource_2
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.ContractibleModel -/

/-! # Contractible Model -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.ContractibleModel.Cycles

noncomputable section

/-!
# Singular homology of contractible complex normal models

The chain and homology objects here are mathlib's genuine singular chains.
Continuous homotopy equivalences induce chain homotopy equivalences. Combining
this with the computation for a point proves positive-degree vanishing.

The complex normal model is the actual topological vector space `Fin p → ℂ`.
An explicit straight-line contraction is given. This file does not compute
its punctured-space or local homology and does not postulate an orientation
class or a cycle class map.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology

variable {R : Type} [Ring R]

/-- A genuine homotopy equivalence induces a homotopy equivalence of singular
chain complexes with the indicated coefficient module. -/
def singularChainsHomotopyEquiv (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} (e : ContinuousMap.HomotopyEquiv X Y) :
    _root_.HomotopyEquiv
      (((singularChainComplexFunctor (ModuleCat.{0} R)).obj M).obj X)
      (((singularChainComplexFunctor (ModuleCat.{0} R)).obj M).obj Y) where
  hom := ((singularChainComplexFunctor (ModuleCat.{0} R)).obj M).map
    (TopCat.ofHom e.toFun)
  inv := ((singularChainComplexFunctor (ModuleCat.{0} R)).obj M).map
    (TopCat.ofHom e.invFun)
  homotopyHomInvId := by
    have H : TopCat.Homotopy
        (TopCat.ofHom e.toFun ≫ TopCat.ofHom e.invFun) (𝟙 X) := e.left_inv.some
    simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] using
      H.singularChainComplexFunctorObjMap M
  homotopyInvHomId := by
    have H : TopCat.Homotopy
        (TopCat.ofHom e.invFun ≫ TopCat.ofHom e.toFun) (𝟙 Y) := e.right_inv.some
    simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] using
      H.singularChainComplexFunctorObjMap M

/-- Singular homology is invariant under an actual continuous homotopy
equivalence. -/
def singularHomologyIsoOfHomotopyEquiv (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{0} R) n).obj M).obj X ≅
      ((singularHomologyFunctor (ModuleCat.{0} R) n).obj M).obj Y :=
  (singularChainsHomotopyEquiv M e).toHomologyIso n

/-- Positive-degree singular homology of a contractible space is zero. -/
theorem isZero_singularHomology_of_contractible (M : ModuleCat.{0} R)
    (X : TopCat.{0}) [ContractibleSpace X] (n : ℕ) (hn : n ≠ 0) :
    IsZero (((singularHomologyFunctor (ModuleCat.{0} R) n).obj M).obj X) := by
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit X
  exact (isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    (ModuleCat.{0} R) n M (TopCat.of Unit) hn).of_iso
      (singularHomologyIsoOfHomotopyEquiv M (Y := TopCat.of Unit) e n)

/-- The integral specialization, expressed in the absolute chain objects
used by the relative and local homology construction. -/
theorem isZero_integralSingularHomology_of_contractible
    (X : TopCat.{0}) [ContractibleSpace X] (n : ℕ) (hn : n ≠ 0) :
    IsZero ((LocalHomology.Cycles.integralSingularChains X).homology n) :=
  isZero_singularHomology_of_contractible (ModuleCat.of ℤ ℤ) X n hn

/-- The genuine integral singular chain complex of a contractible space
is exact in every positive degree. -/
theorem integralSingularChains_exactAt_of_contractible
    (X : TopCat.{0}) [ContractibleSpace X] (n : ℕ) (hn : n ≠ 0) :
    (LocalHomology.Cycles.integralSingularChains X).ExactAt n := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact isZero_integralSingularHomology_of_contractible X n hn

/-- The canonical augmentation computes integral H0 of a path-connected
space, with no choice of homology generator. -/
def integralSingularH0Iso (X : TopCat.{0}) [PathConnectedSpace X] :
    (LocalHomology.Cycles.integralSingularChains X).homology 0 ≅ ModuleCat.of ℤ ℤ := by
  let e := asIso (X.singularHomology₀ε (C := ModuleCat.{0} ℤ) (ModuleCat.of ℤ ℤ))
  exact e

/-- Explicit straight-line contraction of the complex normal coordinate
space, starting with the identity and ending at the zero vector. -/
def complexNormalModelContraction (p : ℕ) :
    ContinuousMap.Homotopy (ContinuousMap.id (Fin p → ℂ))
      (ContinuousMap.const (Fin p → ℂ) 0) where
  toFun q := (1 - (q.1 : ℝ)) • q.2
  continuous_toFun := by fun_prop
  map_zero_left x := by simp
  map_one_left x := by simp

theorem complexNormalModelContraction_apply (p : ℕ)
    (t : unitInterval) (x : Fin p → ℂ) :
    complexNormalModelContraction p (t, x) = (1 - (t : ℝ)) • x := rfl

/-- The complex normal coordinate space is contractible through the displayed
straight-line contraction. -/
theorem complexNormalModel_contractible (p : ℕ) : ContractibleSpace (Fin p → ℂ) :=
  (contractible_iff_id_nullhomotopic (Fin p → ℂ)).mpr
    ⟨0, ⟨complexNormalModelContraction p⟩⟩

/-- Positive-degree integral homology vanishes on the complex normal model. -/
theorem isZero_complexNormalModelHomology (p n : ℕ) (hn : n ≠ 0) :
    IsZero ((LocalHomology.Cycles.integralSingularChains (TopCat.of (Fin p → ℂ))).homology n) := by
  let := complexNormalModel_contractible p
  exact isZero_integralSingularHomology_of_contractible _ n hn

/-- The integral singular chain complex of the normal model is exact in
positive degrees. -/
theorem complexNormalModel_exactAt (p n : ℕ) (hn : n ≠ 0) :
    (LocalHomology.Cycles.integralSingularChains (TopCat.of (Fin p → ℂ))).ExactAt n := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact isZero_complexNormalModelHomology p n hn

/-- Degree-zero homology of the normal model is canonically the integers. -/
def complexNormalModelH0Iso (p : ℕ) :
    (LocalHomology.Cycles.integralSingularChains (TopCat.of (Fin p → ℂ))).homology 0 ≅ ModuleCat.of ℤ ℤ :=
  integralSingularH0Iso _

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.ContractibleModel.Cycles
end ComponentSource_2

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.ContractibleModel"

@[expose] public section ComponentSource_3
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.SimplexFillings -/

/-! # Simplex Fillings -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.SimplexFillings.Cycles

noncomputable section

/-!
# Actual singular-chain fillings in a standard topological simplex

Positive cycles are filled using the proved singular homology vanishing of a
contractible space and the proved cycle/boundary quotient description.
Degree-zero fillings use the actual canonical homology augmentation, not an
assumed acyclic-model property.
-/

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology
open scoped Simplicial

/-- Regard any zero-chain as a cycle in the genuine nonnegative chain complex. -/
def zeroChainToCycles (X : TopCat.{0}) :
    (LocalHomology.Cycles.integralSingularChains X).X 0 →+
      AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (LocalHomology.Cycles.integralSingularChains X) 0 where
  toFun c := ⟨c, AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.mem_chainCycles_zero (LocalHomology.Cycles.integralSingularChains X) c⟩
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

/-- The augmentation of genuine singular zero-chains is the canonical
homology augmentation composed with the canonical class projection. -/
def singularZeroChainAugmentation (X : TopCat.{0}) :
    (LocalHomology.Cycles.integralSingularChains X).X 0 →+ ℤ :=
  (X.singularHomology₀ε (C := ModuleCat.{0} ℤ) (ModuleCat.of ℤ ℤ)).hom.toAddMonoidHom.comp
    ((AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (LocalHomology.Cycles.integralSingularChains X) 0).toAddMonoidHom.comp
      (zeroChainToCycles X))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The explicit zero-chain class is the canonical projection through the
degree-zero cycle isomorphism. -/
theorem zeroChain_class_eq (X : TopCat.{0}) (c : (LocalHomology.Cycles.integralSingularChains X).X 0) :
    AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (LocalHomology.Cycles.integralSingularChains X) 0 (zeroChainToCycles X c) =
      ((LocalHomology.Cycles.integralSingularChains X).homologyπ 0)
        ((LocalHomology.Cycles.integralSingularChains X).cycles₀Iso.inv c) := by
  let C := LocalHomology.Cycles.integralSingularChains X
  rw [AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_eq_homologyπ]
  apply congrArg (C.homologyπ 0)
  apply (ModuleCat.mono_iff_injective (C.iCycles 0)).mp inferInstance
  change (((C.sc 0).moduleCatCyclesIso.inv ≫ (C.sc 0).iCycles)
    (zeroChainToCycles X c)) = ((C.cycles₀Iso.inv ≫ C.cycles₀Iso.hom) c)
  rw [(C.sc 0).moduleCatCyclesIso_inv_iCycles, Iso.inv_hom_id]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Every actual singular zero-simplex contributes its coefficient to the
augmentation; hence this is the usual sum-of-coefficients augmentation. -/
@[simp] theorem singularZeroChainAugmentation_simplex (X : TopCat.{0})
    (σ : (TopCat.toSSet.obj X).obj (.op ⦋0⦌)) (a : ℤ) :
    singularZeroChainAugmentation X
      ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ a) = a := by
  let C := LocalHomology.Cycles.integralSingularChains X
  let ι := (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ
  have hlift : ι ≫ C.cycles₀Iso.inv =
      C.liftCycles ι 0 (by simp) (by simp) := by
    apply (cancel_mono (C.iCycles 0)).mp
    rw [HomologicalComplex.liftCycles_i, Category.assoc]
    change ι ≫ (C.cycles₀Iso.inv ≫ C.cycles₀Iso.hom) = ι
    rw [Iso.inv_hom_id, Category.comp_id]
  have h : (ι ≫ C.cycles₀Iso.inv) ≫ C.homologyπ 0 ≫
      X.singularHomology₀ε (C := ModuleCat.{0} ℤ) (ModuleCat.of ℤ ℤ) = 𝟙 _ := by
    rw [hlift]
    exact (TopCat.toSSet.obj X).liftCycles_ιChainComplex_homologyπ_homology₀ε
      (ModuleCat.of ℤ ℤ) σ
  have ha := congrArg (fun f : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ => f.hom a) h
  change (X.singularHomology₀ε (C := ModuleCat.{0} ℤ) (ModuleCat.of ℤ ℤ)).hom
    (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass C 0 (zeroChainToCycles X (ι a))) = a
  rw [zeroChain_class_eq]
  exact ha

/-- Every positive-degree singular cycle on a contractible space is the
boundary of an actual singular chain one degree higher. -/
theorem exists_singularBoundary_of_contractible
    (X : TopCat.{0}) [ContractibleSpace X] (n : ℕ) (hn : n ≠ 0)
    (c : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (LocalHomology.Cycles.integralSingularChains X) n) :
    ∃ b : (LocalHomology.Cycles.integralSingularChains X).X (n + 1),
      (LocalHomology.Cycles.integralSingularChains X).d (n + 1) n b = c.1 := by
  let := ModuleCat.subsingleton_of_isZero
    (ContractibleModel.Cycles.isZero_integralSingularHomology_of_contractible X n hn)
  exact (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_eq_zero_iff_exists _ n c).mp (Subsingleton.elim _ _)

/-- Unbundled positive-cycle filling, directly in the singular chain modules. -/
theorem exists_singularBoundary_succ_of_contractible
    (X : TopCat.{0}) [ContractibleSpace X] (n : ℕ)
    (c : (LocalHomology.Cycles.integralSingularChains X).X (n + 1))
    (hc : (LocalHomology.Cycles.integralSingularChains X).d (n + 1) n c = 0) :
    ∃ b : (LocalHomology.Cycles.integralSingularChains X).X (n + 2),
      (LocalHomology.Cycles.integralSingularChains X).d (n + 2) (n + 1) b = c :=
  exists_singularBoundary_of_contractible X (n + 1) (Nat.succ_ne_zero n)
    ⟨c, (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.mem_chainCycles_iff_succ _ n c).mpr hc⟩

/-- A zero-chain with zero canonical augmentation on a path-connected space
is the boundary of an actual one-chain. -/
theorem exists_singularBoundary_zero_of_pathConnected
    (X : TopCat.{0}) [PathConnectedSpace X]
    (c : (LocalHomology.Cycles.integralSingularChains X).X 0)
    (hc : singularZeroChainAugmentation X c = 0) :
    ∃ b : (LocalHomology.Cycles.integralSingularChains X).X 1,
      (LocalHomology.Cycles.integralSingularChains X).d 1 0 b = c := by
  apply (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_eq_zero_iff_exists _ 0 (zeroChainToCycles X c)).mp
  apply (ContractibleModel.Cycles.integralSingularH0Iso X).toLinearEquiv.injective
  change singularZeroChainAugmentation X c = (ContractibleModel.Cycles.integralSingularH0Iso X).toLinearEquiv 0
  rw [hc, map_zero]

/-- The ordinary geometric standard simplex is contractible by convexity. -/
theorem stdSimplex_contractible (q : ℕ) :
    ContractibleSpace (Convexity.StdSimplex ℝ (Fin (q + 1))) :=
  inferInstance

/-- The actual standard simplex object used by mathlib's singular-set
construction is contractible, including its universe-lift convention. -/
theorem toTopSimplex_contractible (q : ℕ) :
    ContractibleSpace (SimplexCategory.toTop.{0}.obj ⦋q⦌) := by
  let : ContractibleSpace (SimplexCategory.toTop₀.obj ⦋q⦌) := stdSimplex_contractible q
  exact (SimplexCategory.toTop₀.obj ⦋q⦌).uliftFunctorObjHomeo.symm.contractibleSpace

/-- Positive singular cycles in a geometric standard simplex have fillings. -/
theorem exists_stdSimplex_boundary_succ (q n : ℕ)
    (c : (LocalHomology.Cycles.integralSingularChains (TopCat.of (Convexity.StdSimplex ℝ (Fin (q + 1))))).X (n + 1))
    (hc : (LocalHomology.Cycles.integralSingularChains (TopCat.of (Convexity.StdSimplex ℝ (Fin (q + 1))))).d
      (n + 1) n c = 0) :
    ∃ b : (LocalHomology.Cycles.integralSingularChains (TopCat.of (Convexity.StdSimplex ℝ (Fin (q + 1))))).X (n + 2),
      (LocalHomology.Cycles.integralSingularChains (TopCat.of (Convexity.StdSimplex ℝ (Fin (q + 1))))).d
        (n + 2) (n + 1) b = c := by
  let := stdSimplex_contractible q
  exact exists_singularBoundary_succ_of_contractible _ n c hc

/-- Positive singular cycles in the standard simplex object have actual
singular-chain fillings, suitable for acyclic-model recursion. -/
theorem exists_simplex_boundary_succ (q n : ℕ)
    (c : (LocalHomology.Cycles.integralSingularChains (SimplexCategory.toTop.{0}.obj ⦋q⦌)).X (n + 1))
    (hc : (LocalHomology.Cycles.integralSingularChains (SimplexCategory.toTop.{0}.obj ⦋q⦌)).d
      (n + 1) n c = 0) :
    ∃ b : (LocalHomology.Cycles.integralSingularChains (SimplexCategory.toTop.{0}.obj ⦋q⦌)).X (n + 2),
      (LocalHomology.Cycles.integralSingularChains (SimplexCategory.toTop.{0}.obj ⦋q⦌)).d
        (n + 2) (n + 1) b = c := by
  let := toTopSimplex_contractible q
  exact exists_singularBoundary_succ_of_contractible _ n c hc

/-- Augmentation-zero singular zero-chains in the standard simplex have
actual one-chain fillings. -/
theorem exists_simplex_boundary_zero (q : ℕ)
    (c : (LocalHomology.Cycles.integralSingularChains (SimplexCategory.toTop.{0}.obj ⦋q⦌)).X 0)
    (hc : singularZeroChainAugmentation (SimplexCategory.toTop.{0}.obj ⦋q⦌) c = 0) :
    ∃ b : (LocalHomology.Cycles.integralSingularChains (SimplexCategory.toTop.{0}.obj ⦋q⦌)).X 1,
      (LocalHomology.Cycles.integralSingularChains (SimplexCategory.toTop.{0}.obj ⦋q⦌)).d 1 0 b = c :=
  exists_singularBoundary_zero_of_pathConnected _ c hc

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.SimplexFillings.Cycles
end ComponentSource_3

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.SimplexFillings"

@[expose] public section ComponentSource_4
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.SubdivisionNaturality -/

/-! # Subdivision Naturality -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.SubdivisionNaturality

noncomputable section

/-!
# Naturality and normalization of actual subdivision

These are properties of the actual degreewise signed subdivision operator.
No differential commutation or chain homotopy is assumed here.
-/

open _root_.CategoryTheory
open scoped Simplicial BigOperators Classical

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Cycles

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

/-- Any two points of the genuine standard zero-simplex agree. -/
theorem standardZeroSimplex_eq (x y : Convexity.StdSimplex ℝ (Fin 1)) : x = y := by
  apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin 1)).injective
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  have hx := Convexity.StdSimplex.total_of_fintype x
  have hy := Convexity.StdSimplex.total_of_fintype y
  simp only [Fin.sum_univ_one] at hx hy
  exact hx.trans hy.symm

/-- Geometric subdivision fixes every zero-simplex. -/
@[simp]
theorem subdivisionSimplex_zero (X : TopCat.{0}) (s : SubdivisionOperator.Cycles.SingularSimplex X 0)
    (σ : Equiv.Perm (Fin 1)) : SubdivisionOperator.Cycles.subdivisionSimplex X 0 s σ = s := by
  apply (X.toSSetObjEquiv (.op ⦋0⦌)).injective
  rw [SubdivisionOperator.Cycles.subdivisionSimplex_toContinuousMap]
  apply ContinuousMap.ext
  intro x
  simp only [ContinuousMap.comp_apply]
  rw [standardZeroSimplex_eq (BarycentricSimplex.Cycles.barycentricSubdivisionMap σ x) x]

/-- The signed generator formula is the identity in degree zero. -/
@[simp]
theorem subdivisionGenerator_zero (X : TopCat.{0}) (s : SubdivisionOperator.Cycles.SingularSimplex X 0) :
    SubdivisionOperator.Cycles.subdivisionGenerator X 0 s = Finsupp.single s 1 := by
  have hsign (σ : Equiv.Perm (Fin 1)) : (Equiv.Perm.sign σ : ℤ) = 1 := by
    rw [show σ = 1 from Subsingleton.elim _ _]
    simp
  simp [SubdivisionOperator.Cycles.subdivisionGenerator, hsign]

/-- The coefficient subdivision map is the identity in degree zero. -/
theorem subdivisionFinsupp_zero_dimension (X : TopCat.{0}) :
    SubdivisionOperator.Cycles.subdivisionFinsupp X 0 = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro s a
  simp [SubdivisionOperator.Cycles.subdivisionFinsupp, Finsupp.smul_single]

/-- Actual singular zero-chains are fixed by subdivision. -/
theorem subdivisionDegree_zero_dimension (X : TopCat.{0}) :
    SubdivisionOperator.Cycles.subdivisionDegree X 0 = LinearMap.id := by
  apply LinearMap.ext
  intro c
  apply (SingularChainSupport.Cycles.singularChainCoefficients X 0).injective
  rw [SubdivisionOperator.Cycles.subdivisionDegree_coefficients, subdivisionFinsupp_zero_dimension]
  rfl

@[simp]
theorem subdivisionDegree_zero_dimension_apply (X : TopCat.{0})
    (c : (LocalHomology.Cycles.integralSingularChains X).X 0) : SubdivisionOperator.Cycles.subdivisionDegree X 0 c = c := by
  rw [subdivisionDegree_zero_dimension]
  rfl

/-- Compatibility with the actual canonical zero-chain augmentation. -/
@[simp]
theorem singularZeroChainAugmentation_subdivision (X : TopCat.{0})
    (c : (LocalHomology.Cycles.integralSingularChains X).X 0) :
    SimplexFillings.Cycles.singularZeroChainAugmentation X (SubdivisionOperator.Cycles.subdivisionDegree X 0 c) =
      SimplexFillings.Cycles.singularZeroChainAugmentation X c := by
  rw [subdivisionDegree_zero_dimension_apply]

/-- A barycentric cell commutes with continuous postcomposition. -/
theorem subdivisionSimplex_postcompose {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (s : SubdivisionOperator.Cycles.SingularSimplex X n) (σ : Equiv.Perm (Fin (n + 1))) :
    (TopCat.toSSet.map f).app _ (SubdivisionOperator.Cycles.subdivisionSimplex X n s σ) =
      SubdivisionOperator.Cycles.subdivisionSimplex Y n ((TopCat.toSSet.map f).app _ s) σ := by
  have hgeom (t : SubdivisionOperator.Cycles.SingularSimplex X n) :
      Y.toSSetObjEquiv (.op ⦋n⦌) ((TopCat.toSSet.map f).app _ t) =
        f.hom.comp (X.toSSetObjEquiv (.op ⦋n⦌) t) := rfl
  apply (Y.toSSetObjEquiv (.op ⦋n⦌)).injective
  rw [hgeom, SubdivisionOperator.Cycles.subdivisionSimplex_toContinuousMap, SubdivisionOperator.Cycles.subdivisionSimplex_toContinuousMap, hgeom]
  rfl

/-- The actual singular-chain pushforward in an individual degree. -/
abbrev singularChainPostcompose {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    (LocalHomology.Cycles.integralSingularChains X).X n →ₗ[ℤ] (LocalHomology.Cycles.integralSingularChains Y).X n :=
  ((LocalHomology.Cycles.integralSingularChainFunctor.map f).f n).hom

/-- Its action on a genuine simplex summand is literal postcomposition. -/
@[simp]
theorem singularChainPostcompose_simplex {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (s : SubdivisionOperator.Cycles.SingularSimplex X n) (a : ℤ) :
    singularChainPostcompose f n
      ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) s a) =
      (TopCat.toSSet.obj Y).ιChainComplex (R := ModuleCat.of ℤ ℤ)
        ((TopCat.toSSet.map f).app _ s) a := by
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using!
    congrArg (fun g : ModuleCat.of ℤ ℤ ⟶ (LocalHomology.Cycles.integralSingularChains Y).X n => g.hom a)
      (SSet.ι_chainComplexMap_f (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y)
        (TopCat.toSSet.map f) (ModuleCat.of ℤ ℤ) s)

/-- To check a linear map on actual singular chains, check each simplex summand. -/
theorem singularChainLinearMap_ext (X : TopCat.{0}) (n : ℕ) (M : ModuleCat.{0} ℤ)
    (f g : (LocalHomology.Cycles.integralSingularChains X).X n →ₗ[ℤ] M)
    (h : ∀ (s : SubdivisionOperator.Cycles.SingularSimplex X n) (a : ℤ),
      f ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) s a) =
      g ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) s a)) : f = g := by
  have hcat : ModuleCat.ofHom f = ModuleCat.ofHom g := by
    apply (TopCat.toSSet.obj X).chainComplex_hom_ext
    intro s
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply] using! h s a
  exact congrArg (fun k => k.hom) hcat

/-- Actual degreewise subdivision is natural under any continuous map. -/
theorem subdivisionDegree_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    (singularChainPostcompose f n).comp (SubdivisionOperator.Cycles.subdivisionDegree X n) =
      (SubdivisionOperator.Cycles.subdivisionDegree Y n).comp (singularChainPostcompose f n) := by
  have hsd (Z : TopCat.{0}) (t : SubdivisionOperator.Cycles.SingularSimplex Z n) (b : ℤ) :
      SubdivisionOperator.Cycles.subdivisionDegree Z n ((TopCat.toSSet.obj Z).ιChainComplex
        (R := ModuleCat.of ℤ ℤ) t b) =
        ∑ σ : Equiv.Perm (Fin (n + 1)),
          (TopCat.toSSet.obj Z).ιChainComplex (R := ModuleCat.of ℤ ℤ)
            (SubdivisionOperator.Cycles.subdivisionSimplex Z n t σ) ((Equiv.Perm.sign σ : ℤ) * b) := by
    simpa only using! SubdivisionOperator.Cycles.subdivisionDegree_simplex Z n t b
  have hp (t : SubdivisionOperator.Cycles.SingularSimplex X n) (b : ℤ) :
      singularChainPostcompose f n
        ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) t b) =
        (TopCat.toSSet.obj Y).ιChainComplex (R := ModuleCat.of ℤ ℤ)
          ((TopCat.toSSet.map f).app _ t) b := by
    simpa only using! singularChainPostcompose_simplex f n t b
  apply singularChainLinearMap_ext X n ((LocalHomology.Cycles.integralSingularChains Y).X n)
  intro s a
  simp only [LinearMap.comp_apply, hsd, map_sum, hp, subdivisionSimplex_postcompose]

/-- Pointwise naturality, convenient for the actual acyclic-model construction. -/
theorem subdivisionDegree_naturality_apply {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (c : (LocalHomology.Cycles.integralSingularChains X).X n) :
    singularChainPostcompose f n (SubdivisionOperator.Cycles.subdivisionDegree X n c) =
      SubdivisionOperator.Cycles.subdivisionDegree Y n (singularChainPostcompose f n c) :=
  LinearMap.congr_fun (subdivisionDegree_naturality f n) c

/-- Once a chain is subordinate to a cover, subdivision preserves that property.
This uses actual range containment and imposes no openness assumption. -/
theorem subdivisionDegree_preserves_small {X : TopCat.{0}} {J : Type}
    (U : J → Set X) (n : ℕ) (c : (LocalHomology.Cycles.integralSingularChains X).X n)
    (hc : ∀ s ∈ SingularChainSupport.Cycles.singularChainSupport c,
      s ∈ (AlgebraicTopology.DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex X U).obj (.op ⦋n⦌)) :
    ∀ t ∈ SingularChainSupport.Cycles.singularChainSupport (SubdivisionOperator.Cycles.subdivisionDegree X n c),
      t ∈ (AlgebraicTopology.DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex X U).obj (.op ⦋n⦌) := by
  intro t ht
  obtain ⟨s, hs, hsub⟩ := SubdivisionOperator.Cycles.support_subdivisionDegree_range X n c t ht
  obtain ⟨j, hj⟩ := hc s hs
  exact ⟨j, hsub.trans hj⟩

end Cycles

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.SubdivisionNaturality
end ComponentSource_4

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.SubdivisionNaturality"

@[expose] public section ComponentSource_5
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.SubdivisionHomotopy -/

/-! # Subdivision Homotopy -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.SubdivisionHomotopy.Cycles

noncomputable section

/-!
# Natural singular-chain fillings for subdivision homotopies

The ordinary singular chains form a chain complex in the functor category
`TopCat ⥤ ModuleCat ℤ`. Its degree-n functor is represented by the actual
topological n-simplex, in the free-module sense expressed by mathlib's
singular-chain adjunction. Positive cycles on this model have genuine fillings.
These facts permit natural chain-homotopy induction, without postulating
acyclic models or a subdivision homotopy.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology
open scoped Simplicial

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The degree-n ordinary integral singular chain functor. -/
abbrev singularChainDegreeFunctor (n : ℕ) : TopCat.{0} ⥤ ModuleCat.{0} ℤ :=
  LocalHomology.Cycles.integralSingularChainFunctor ⋙
    HomologicalComplex.eval (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n

/-- The actual singular boundary is natural in the topological space. -/
def singularBoundaryNatural (i j : ℕ) :
    singularChainDegreeFunctor i ⟶ singularChainDegreeFunctor j where
  app X := (LocalHomology.Cycles.integralSingularChains X).d i j
  naturality _ _ f := (LocalHomology.Cycles.integralSingularChainFunctor.map f).comm i j

/-- Genuine integral singular chains viewed as a complex of functors. -/
abbrev naturalSingularChains : ChainComplex (TopCat.{0} ⥤ ModuleCat.{0} ℤ) ℕ where
  X := singularChainDegreeFunctor
  d := singularBoundaryNatural
  shape i j h := by
    apply NatTrans.ext
    funext X
    exact (LocalHomology.Cycles.integralSingularChains X).shape i j h
  d_comp_d' i j k _ _ := by
    apply NatTrans.ext
    funext X
    exact (LocalHomology.Cycles.integralSingularChains X).d_comp_d i j k

/-- A natural degree-n chain operation is evaluated on its genuine simplex model. -/
def singularModelEvaluation (n k : ℕ)
    (a : singularChainDegreeFunctor n ⟶ singularChainDegreeFunctor k) :
    ModuleCat.of ℤ ℤ ⟶
      (LocalHomology.Cycles.integralSingularChains (SimplexCategory.toTop.{0}.obj ⦋n⦌)).X k :=
  (singularChainComplexFunctorAdjunction (ModuleCat.{0} ℤ) n).homEquiv
    (ModuleCat.of ℤ ℤ) (singularChainDegreeFunctor k) a

/-- Evaluation on the universal simplex detects equality of natural operations. -/
theorem singularModelEvaluation_injective (n k : ℕ) :
    Function.Injective (singularModelEvaluation n k) :=
  (singularChainComplexFunctorAdjunction (ModuleCat.{0} ℤ) n).homEquiv
    (ModuleCat.of ℤ ℤ) (singularChainDegreeFunctor k) |>.injective

@[simp]
theorem singularModelEvaluation_zero (n k : ℕ) :
    singularModelEvaluation n k 0 = 0 := by
  simp [singularModelEvaluation]; rfl

/-- Model evaluation commutes with a further natural chain operation. -/
theorem singularModelEvaluation_comp (n k l : ℕ)
    (a : singularChainDegreeFunctor n ⟶ singularChainDegreeFunctor k)
    (b : singularChainDegreeFunctor k ⟶ singularChainDegreeFunctor l) :
    singularModelEvaluation n l (a ≫ b) =
      singularModelEvaluation n k a ≫ b.app (SimplexCategory.toTop.{0}.obj ⦋n⦌) :=
  (singularChainComplexFunctorAdjunction (ModuleCat.{0} ℤ) n).homEquiv_naturality_right a b

/-- Every natural positive-cycle operation admits a natural filling operation.
The filling is obtained from the proved contractibility of the actual standard
simplex, then extended by its free singular-chain universal property. -/
theorem exists_naturalSingularFilling (n k : ℕ)
    (a : singularChainDegreeFunctor n ⟶ singularChainDegreeFunctor (k + 1))
    (ha : a ≫ singularBoundaryNatural (k + 1) k = 0) :
    ∃ b : singularChainDegreeFunctor n ⟶ singularChainDegreeFunctor (k + 2),
      b ≫ singularBoundaryNatural (k + 2) (k + 1) = a := by
  let model := SimplexCategory.toTop.{0}.obj ⦋n⦌
  let v := singularModelEvaluation n (k + 1) a
  have hv : v ≫ (LocalHomology.Cycles.integralSingularChains model).d (k + 1) k = 0 := by
    change singularModelEvaluation n (k + 1) a ≫
      (singularBoundaryNatural (k + 1) k).app model = 0
    rw [← singularModelEvaluation_comp, ha, singularModelEvaluation_zero]
  have hcycle : (LocalHomology.Cycles.integralSingularChains model).d (k + 1) k (v 1) = 0 := by
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply,
      ModuleCat.hom_zero, LinearMap.zero_apply] using!
      congrArg (fun f : ModuleCat.of ℤ ℤ ⟶ (LocalHomology.Cycles.integralSingularChains model).X k ↦ f.hom 1) hv
  obtain ⟨c, hc⟩ := SimplexFillings.Cycles.exists_simplex_boundary_succ n k (v 1) hcycle
  let cf : ModuleCat.of ℤ ℤ ⟶ (LocalHomology.Cycles.integralSingularChains model).X (k + 2) :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _ c)
  have hcf : cf.hom 1 = c := LinearMap.toSpanSingleton_apply_one ℤ _ c
  let b := ((singularChainComplexFunctorAdjunction (ModuleCat.{0} ℤ) n).homEquiv
    (ModuleCat.of ℤ ℤ) (singularChainDegreeFunctor (k + 2))).symm cf
  refine ⟨b, ?_⟩
  apply singularModelEvaluation_injective n (k + 1)
  rw [singularModelEvaluation_comp]
  have hb : singularModelEvaluation n (k + 2) b = cf :=
    Equiv.apply_symm_apply _ _
  rw [hb]
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  change (cf ≫ (LocalHomology.Cycles.integralSingularChains model).d (k + 2) (k + 1)).hom 1 = v.hom 1
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, hcf]
  exact hc

/-- A natural singular-chain endomorphism which vanishes in degree zero is
naturally null-homotopic. This is the acyclic-model argument proved from the
actual simplex fillings, rather than an assumed acyclic-model principle. -/
def naturalSingularNullhomotopy (e : naturalSingularChains ⟶ naturalSingularChains)
    (he : e.f 0 = 0) : Homotopy e 0 := by
  classical
  have hclosed : e.f 1 ≫ singularBoundaryNatural 1 0 = 0 := by
    change e.f 1 ≫ naturalSingularChains.d 1 0 = 0
    rw [e.comm 1 0, he, comp_zero]
  let hfirst := exists_naturalSingularFilling 1 0 (e.f 1) hclosed
  let first := Classical.choose hfirst
  have hfirst_eq := Classical.choose_spec hfirst
  refine Homotopy.mkInductive e 0 ?_ first ?_ ?_
  · simpa only [zero_comp] using he
  · simpa only [first, comp_zero, zero_add] using! hfirst_eq.symm
  · intro n p
    rcases p with ⟨u, v, hp⟩
    let a := e.f (n + 2) - naturalSingularChains.d (n + 2) (n + 1) ≫ v
    have ha : a ≫ singularBoundaryNatural (n + 2) (n + 1) = 0 := by
      change a ≫ naturalSingularChains.d (n + 2) (n + 1) = 0
      dsimp only [a]
      rw [Preadditive.sub_comp, e.comm (n + 2) (n + 1), hp,
        Preadditive.comp_add]
      simp only [← Category.assoc, naturalSingularChains.d_comp_d,
        zero_comp, zero_add, sub_self]
    let hnext := exists_naturalSingularFilling (n + 2) (n + 1) a ha
    refine ⟨Classical.choose hnext, ?_⟩
    have hnext_eq := Classical.choose_spec hnext
    change e.f (n + 2) = naturalSingularChains.d (n + 2) (n + 1) ≫ v +
      Classical.choose hnext ≫ singularBoundaryNatural (n + 3) (n + 2)
    rw [hnext_eq]
    dsimp only [a]
    abel

/-- Natural chain endomorphisms agreeing in degree zero are naturally
chain-homotopic, by applying the proved natural filling induction to their difference. -/
def naturalSingularHomotopy (f g : naturalSingularChains ⟶ naturalSingularChains)
    (hzero : f.f 0 = g.f 0) : Homotopy f g :=
  (Homotopy.equivSubZero (f := f) (g := g)).symm (naturalSingularNullhomotopy (f - g) (by
    change f.f 0 - g.f 0 = 0
    rw [hzero, sub_self]))

/-- The signed geometric subdivision chain map, simultaneously on all spaces. -/
def naturalSubdivision : naturalSingularChains ⟶ naturalSingularChains where
  f n :=
    { app X := (SubdivisionBoundary.Cycles.subdivisionChainMap X).f n
      naturality X Y f := by
        apply ModuleCat.hom_ext
        simpa only [ModuleCat.hom_comp, SubdivisionBoundary.Cycles.subdivisionChainMap_f] using!
          (SubdivisionNaturality.Cycles.subdivisionDegree_naturality f n).symm }
  comm' i j _ := by
    apply NatTrans.ext
    funext X
    exact (SubdivisionBoundary.Cycles.subdivisionChainMap X).comm i j

/-- The actual subdivision natural transformation is the identity in degree zero. -/
theorem naturalSubdivision_zero :
    naturalSubdivision.f 0 = 𝟙 (singularChainDegreeFunctor 0) := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  change ((SubdivisionBoundary.Cycles.subdivisionChainMap X).f 0).hom = LinearMap.id
  rw [SubdivisionBoundary.Cycles.subdivisionChainMap_f, SubdivisionNaturality.Cycles.subdivisionDegree_zero_dimension]

/-- The genuine subdivision chain homotopy, constructed by natural simplex fillings. -/
def naturalSubdivisionHomotopy : Homotopy naturalSubdivision (𝟙 naturalSingularChains) :=
  naturalSingularHomotopy naturalSubdivision (𝟙 naturalSingularChains) naturalSubdivision_zero

/-- Evaluation of a natural singular-chain map on an actual topological space. -/
def naturalSingularChainMapAt (e : naturalSingularChains ⟶ naturalSingularChains)
    (X : TopCat.{0}) : LocalHomology.Cycles.integralSingularChains X ⟶ LocalHomology.Cycles.integralSingularChains X where
  f i := (e.f i).app X
  comm' i j _ := NatTrans.congr_app (e.comm i j) X

/-- Evaluation of a natural chain homotopy on an actual space. -/
def naturalSingularHomotopyAt
    {f g : naturalSingularChains ⟶ naturalSingularChains} (h : Homotopy f g)
    (X : TopCat.{0}) :
    Homotopy (naturalSingularChainMapAt f X) (naturalSingularChainMapAt g X) where
  hom i j := (h.hom i j).app X
  zero i j hij := NatTrans.congr_app (h.zero i j hij) X
  comm i := NatTrans.congr_app (h.comm i) X

/-- Actual barycentric subdivision is chain-homotopic to the identity. -/
def subdivisionHomotopy (X : TopCat.{0}) :
    Homotopy (SubdivisionBoundary.Cycles.subdivisionChainMap X) (𝟙 (LocalHomology.Cycles.integralSingularChains X)) :=
  naturalSingularHomotopyAt naturalSubdivisionHomotopy X

/-- The constructed subdivision homotopy is natural under continuous maps. -/
theorem subdivisionHomotopy_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (i j : ℕ) :
    (LocalHomology.Cycles.integralSingularChainFunctor.map f).f i ≫ (subdivisionHomotopy Y).hom i j =
      (subdivisionHomotopy X).hom i j ≫ (LocalHomology.Cycles.integralSingularChainFunctor.map f).f j :=
  (naturalSubdivisionHomotopy.hom i j).naturality f

/-- In particular the actual homotopy preserves chains coming from every subspace. -/
theorem subdivisionHomotopy_subspace (X : TopCat.{0}) (A : Set X) (i j : ℕ) :
    (LocalHomology.Cycles.subspaceChainInclusion X A).f i ≫ (subdivisionHomotopy X).hom i j =
      (subdivisionHomotopy (TopCat.of A)).hom i j ≫ (LocalHomology.Cycles.subspaceChainInclusion X A).f j :=
  subdivisionHomotopy_naturality (LocalHomology.Cycles.subspaceInclusion X A) i j

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.SubdivisionHomotopy.Cycles
end ComponentSource_5

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.SubdivisionHomotopy"

@[expose] public section ComponentSource_6
/- Original module: OAI.AlgebraicTopology.Cohomology.Singular.NaturalSmallChains -/

/-! # Natural Small Chains -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.NaturalSmallChains

noncomputable section

/-!
# Natural chain operations preserve small singular chains

A singular simplex whose image lies in a subset factors continuously through
that subset. Naturality therefore forces every natural operation on singular
chains to carry this simplex into the image of the same subspace. Taking sums
shows that the actual image of the small-chain inclusion is preserved.

The argument works for any family of subsets; openness and the covering
condition are unnecessary for this locality statement.
-/

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

open _root_.CategoryTheory
open scoped Simplicial

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A simplex with image in a subset is an actual simplex of the subspace. -/
theorem singularSimplex_liftsToSubspace (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (s : (TopCat.toSSet.obj X).obj (.op ⦋n⦌))
    (hs : Set.range (X.toSSetObjEquiv (.op ⦋n⦌) s) ⊆ A) :
    ∃ t : (TopCat.toSSet.obj (TopCat.of A)).obj (.op ⦋n⦌),
      (TopCat.toSSet.map (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X A)).app (.op ⦋n⦌) t = s := by
  let g := X.toSSetObjEquiv (.op ⦋n⦌) s
  let h : C(Convexity.StdSimplex ℝ (Fin (n + 1)), A) :=
    ⟨fun x => ⟨g x, hs ⟨x, rfl⟩⟩, g.continuous.subtype_mk _⟩
  refine ⟨((TopCat.of A).toSSetObjEquiv (.op ⦋n⦌)).symm h, ?_⟩
  apply (X.toSSetObjEquiv (.op ⦋n⦌)).injective
  change (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X A).hom.comp
    ((TopCat.of A).toSSetObjEquiv (.op ⦋n⦌)
      (((TopCat.of A).toSSetObjEquiv (.op ⦋n⦌)).symm h)) = g
  rw [Equiv.apply_symm_apply]
  rfl

variable (X : TopCat.{0}) {J : Type} (U : J → Set X)

/-- Singular simplices of a family member give small singular simplices. -/
def coverMemberSingularMap (i : J) :
    TopCat.toSSet.obj (TopCat.of (U i)) ⟶
      (DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex X U : SSet) :=
  SSet.Subcomplex.lift (TopCat.toSSet.map (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X (U i))) (by
    intro n s hs
    obtain ⟨t, rfl⟩ := hs
    refine ⟨i, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact (((TopCat.of (U i)).toSSetObjEquiv n t) x).property)

@[reassoc (attr := simp)]
theorem coverMemberSingularMap_inclusion (i : J) :
    coverMemberSingularMap X U i ≫ DeRham.Comparison.SmallSingularSet.smallSingularInclusion X U =
      TopCat.toSSet.map (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X (U i)) := rfl

/-- The subspace chain map factors through the genuine small-chain complex. -/
def coverMemberChainMap (i : J) :
    AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of (U i)) ⟶ AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.integralSmallSingularChains X U :=
  SSet.chainComplexMap (coverMemberSingularMap X U i) (ModuleCat.of ℤ ℤ)

@[reassoc (attr := simp)]
theorem coverMemberChainMap_inclusion (i : J) :
    coverMemberChainMap X U i ≫ AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.smallIntegralChainInclusion X U =
      AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion X (U i) := by
  change ((SSet.chainComplexFunctor (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)).map
      (coverMemberSingularMap X U i) ≫
    ((SSet.chainComplexFunctor (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)).map
      (DeRham.Comparison.SmallSingularSet.smallSingularInclusion X U) = _
  rw [← Functor.map_comp, coverMemberSingularMap_inclusion]
  rfl

/-- Any natural chain operation sends a small simplex summand into the actual
image of the small-chain inclusion. -/
theorem naturalSingularOperation_smallSimplex {n m : ℕ}
    (a : AlgebraicGeometry.CycleClass.Geometric.SubdivisionHomotopy.Cycles.singularChainDegreeFunctor n ⟶ AlgebraicGeometry.CycleClass.Geometric.SubdivisionHomotopy.Cycles.singularChainDegreeFunctor m)
    (s : (TopCat.toSSet.obj X).obj (.op ⦋n⦌))
    (hs : s ∈ (DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex X U).obj (.op ⦋n⦌))
    (z : ℤ) :
    a.app X ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) s z) ∈
      LinearMap.range ((AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.smallIntegralChainInclusion X U).f m).hom := by
  obtain ⟨i, hi⟩ := hs
  obtain ⟨t, ht⟩ := singularSimplex_liftsToSubspace X (U i) n s hi
  let u := (TopCat.toSSet.obj (TopCat.of (U i))).ιChainComplex
    (R := ModuleCat.of ℤ ℤ) t z
  have hu : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion X (U i)).f n u =
      (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) s z := by
    change AlgebraicGeometry.CycleClass.Geometric.SubdivisionNaturality.Cycles.singularChainPostcompose (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X (U i)) n
      ((TopCat.toSSet.obj (TopCat.of (U i))).ιChainComplex
        (R := ModuleCat.of ℤ ℤ) t z) = _
    rw [AlgebraicGeometry.CycleClass.Geometric.SubdivisionNaturality.Cycles.singularChainPostcompose_simplex, ht]
  have hnat : a.app X ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion X (U i)).f n u) =
      (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion X (U i)).f m (a.app (TopCat.of (U i)) u) := by
    exact ConcreteCategory.congr_hom (a.naturality (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X (U i))) u
  rw [hu] at hnat
  refine ⟨(coverMemberChainMap X U i).f m (a.app (TopCat.of (U i)) u), ?_⟩
  rw [hnat]
  exact ConcreteCategory.congr_hom
    (congrArg (fun f => f.f m) (coverMemberChainMap_inclusion X U i))
    (a.app (TopCat.of (U i)) u)

/-- Every natural operation on ordinary integral singular chains preserves the
actual image of the small-chain inclusion, for an arbitrary family of subsets. -/
theorem naturalSingularOperation_preserves_smallChainImage {n m : ℕ}
    (a : AlgebraicGeometry.CycleClass.Geometric.SubdivisionHomotopy.Cycles.singularChainDegreeFunctor n ⟶ AlgebraicGeometry.CycleClass.Geometric.SubdivisionHomotopy.Cycles.singularChainDegreeFunctor m)
    (X : TopCat.{0}) {J : Type} (U : J → Set X)
    {c : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n}
    (hc : c ∈ LinearMap.range ((AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n).hom) :
    a.app X c ∈ LinearMap.range ((AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.smallIntegralChainInclusion X U).f m).hom := by
  let P := LinearMap.range ((AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.smallIntegralChainInclusion X U).f m).hom
  let : Module ℤ ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X m ⧸ P) := Submodule.Quotient.module P
  have hzero : (AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n ≫ a.app X ≫
      ModuleCat.ofHom P.mkQ = 0 := by
    apply SSet.chainComplex_hom_ext
    intro s
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    have hsmall := naturalSingularOperation_smallSimplex X U a s.val s.property z
    have hgen : (AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n
        ((DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex X U : SSet).ιChainComplex
          (R := ModuleCat.of ℤ ℤ) s z) =
        (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) s.val z :=
      ConcreteCategory.congr_hom
        (SSet.ι_chainComplexMap_f
          (DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex X U : SSet)
          (TopCat.toSSet.obj X) (DeRham.Comparison.SmallSingularSet.smallSingularInclusion X U)
          (ModuleCat.of ℤ ℤ) s) z
    change P.mkQ (a.app X ((AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n
      ((DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex X U : SSet).ιChainComplex
        (R := ModuleCat.of ℤ ℤ) s z))) = 0
    rw [hgen, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hsmall
  obtain ⟨b, rfl⟩ := hc
  have hb := ConcreteCategory.congr_hom hzero b
  change P.mkQ (a.app X ((AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n b)) = 0 at hb
  exact (Submodule.Quotient.mk_eq_zero (p := P)).mp hb

end

end OAI.AlgebraicTopology.Cohomology.Singular.NaturalSmallChains
end ComponentSource_6

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicTopology.Cohomology.Singular.NaturalSmallChains"

@[expose] public section ComponentSource_7
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.SmallSubdivisionHomotopy -/

/-! # Small Subdivision Homotopy -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.SmallSubdivisionHomotopy.Cycles

noncomputable section

/-!
# The actual subdivision homotopy on small singular chains

The ambient subdivision homotopy is natural under every continuous map.
Consequently each component preserves cover-small chains: every such simplex
factors through a single member of the cover. We restrict these actual
components through the injective small-chain inclusion, and prove their
homotopy identity using that inclusion.

No openness or covering assumption is needed for this restriction. Those
hypotheses enter only the separate eventual-smallness theorem.
-/

open _root_.CategoryTheory

variable (X : TopCat.{0}) {J : Type} (U : J → Set X)

/-- Every component of the actual ambient subdivision homotopy preserves
the actual image of the small-chain inclusion. -/
theorem subdivisionHomotopy_preserves_smallChainImage (a b : ℕ)
    {c : (LocalHomology.Cycles.integralSingularChains X).X a}
    (hc : c ∈ LinearMap.range ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f a).hom) :
    (SubdivisionHomotopy.Cycles.subdivisionHomotopy X).hom a b c ∈
      LinearMap.range ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f b).hom :=
  AlgebraicTopology.Cohomology.Singular.NaturalSmallChains.naturalSingularOperation_preserves_smallChainImage
    (SubdivisionHomotopy.Cycles.naturalSubdivisionHomotopy.hom a b) X U hc

/-- The genuine barycentric subdivision chain map on small chains is
homotopic to the identity, by restriction of the constructed ambient homotopy. -/
def smallSubdivisionHomotopy :
    Homotopy (SmallSubdivision.Cycles.smallSubdivisionChainMap X U) (𝟙 (SmallChainImage.Cycles.integralSmallSingularChains X U)) :=
  InjectiveHomotopyRestriction.Cycles.restrictHomotopy (SmallChainImage.Cycles.smallIntegralChainInclusion X U)
    (SmallChainImage.Cycles.smallIntegralChainInclusion_injective X U)
    (SmallSubdivision.Cycles.smallSubdivisionChainMap_intertwining X U) (by simp)
    (SubdivisionHomotopy.Cycles.subdivisionHomotopy X)
    (fun a b c => subdivisionHomotopy_preserves_smallChainImage X U a b
      (LinearMap.mem_range_self _ c))

/-- Inclusion identifies each restricted homotopy component with the actual
ambient component. -/
@[reassoc]
theorem smallSubdivisionHomotopy_inclusion (a b : ℕ) :
    (smallSubdivisionHomotopy X U).hom a b ≫
        (SmallChainImage.Cycles.smallIntegralChainInclusion X U).f b =
      (SmallChainImage.Cycles.smallIntegralChainInclusion X U).f a ≫ (SubdivisionHomotopy.Cycles.subdivisionHomotopy X).hom a b :=
  InjectiveHomotopyRestriction.Cycles.restrictedHomotopyComponent_comp _ _ _ _ a b

/-- The same compatibility evaluated on an actual small chain. -/
@[simp]
theorem smallSubdivisionHomotopy_apply_inclusion (a b : ℕ)
    (c : (SmallChainImage.Cycles.integralSmallSingularChains X U).X a) :
    (SmallChainImage.Cycles.smallIntegralChainInclusion X U).f b ((smallSubdivisionHomotopy X U).hom a b c) =
      (SubdivisionHomotopy.Cycles.subdivisionHomotopy X).hom a b ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f a c) :=
  InjectiveHomotopyRestriction.Cycles.restrictedHomotopyComponent_apply _ _ _ _ a b c

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.SmallSubdivisionHomotopy.Cycles
end ComponentSource_7

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.SmallSubdivisionHomotopy"

@[expose] public section ComponentSource_8
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.SmallSingularQuasiIso -/

/-! # Small Singular Quasi Iso -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.SmallSingularQuasiIso.Cycles

noncomputable section

/-!
# The actual open-cover small-chain inclusion is a quasi-isomorphism

This module applies the eventual-smallness criterion to the constructed signed
barycentric subdivision chain maps and their constructed chain homotopies.
The only hypotheses are that the given family consists of open subsets and
covers the actual topological space.
-/

open _root_.CategoryTheory

variable (X : TopCat.{0}) {J : Type} (U : J → Set X)

/-- For an actual open cover, the canonical inclusion of cover-small integral
singular chains into all integral singular chains is a quasi-isomorphism. -/
theorem smallIntegralChainInclusion_quasiIso
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i) :
    _root_.QuasiIso (SmallChainImage.Cycles.smallIntegralChainInclusion X U) :=
  EventuallySmall.Cycles.quasiIso_of_eventuallySmall
    (SmallChainImage.Cycles.smallIntegralChainInclusion X U)
    (SmallChainImage.Cycles.smallIntegralChainInclusion_injective X U)
    (SmallSubdivision.Cycles.smallSubdivisionChainMap X U)
    (SubdivisionBoundary.Cycles.subdivisionChainMap X)
    (SmallSubdivision.Cycles.smallSubdivisionChainMap_intertwining X U)
    (SmallSubdivisionHomotopy.Cycles.smallSubdivisionHomotopy X U)
    (SubdivisionHomotopy.Cycles.subdivisionHomotopy X)
    (fun _ c => SmallSubdivision.Cycles.exists_subdivisionChainMap_iterate_small_preimage X U hopen hcover c)

/-- The induced homology map is bijective in every degree, including zero. -/
theorem smallIntegralHomologyMap_bijective
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ) :
    Function.Bijective (HomologicalComplex.homologyMap (SmallChainImage.Cycles.smallIntegralChainInclusion X U) n) := by
  let _ := smallIntegralChainInclusion_quasiIso X U hopen hcover
  exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance

/-- The genuine homology isomorphism induced by the canonical inclusion of
open-cover small singular chains. -/
def smallIntegralHomologyIso
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ) :
    (SmallChainImage.Cycles.integralSmallSingularChains X U).homology n ≅ (LocalHomology.Cycles.integralSingularChains X).homology n := by
  letI := smallIntegralChainInclusion_quasiIso X U hopen hcover
  exact isoOfQuasiIsoAt (SmallChainImage.Cycles.smallIntegralChainInclusion X U) n

@[simp]
theorem smallIntegralHomologyIso_hom
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ) :
    (smallIntegralHomologyIso X U hopen hcover n).hom =
      HomologicalComplex.homologyMap (SmallChainImage.Cycles.smallIntegralChainInclusion X U) n := rfl

@[reassoc (attr := simp)]
theorem smallIntegralHomologyMap_iso_inv
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ) :
    HomologicalComplex.homologyMap (SmallChainImage.Cycles.smallIntegralChainInclusion X U) n ≫
      (smallIntegralHomologyIso X U hopen hcover n).inv = 𝟙 _ :=
  (smallIntegralHomologyIso X U hopen hcover n).hom_inv_id

@[reassoc (attr := simp)]
theorem smallIntegralHomologyIso_inv_map
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ) :
    (smallIntegralHomologyIso X U hopen hcover n).inv ≫
      HomologicalComplex.homologyMap (SmallChainImage.Cycles.smallIntegralChainInclusion X U) n = 𝟙 _ :=
  (smallIntegralHomologyIso X U hopen hcover n).inv_hom_id

variable (A B : Set X)

/-- Actual quasi-isomorphism for a binary open cover, in the presentation used
by the small-chain Mayer--Vietoris sequence. -/
theorem binarySmallIntegralChainInclusion_quasiIso
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ) :
    _root_.QuasiIso (BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X A B) := by
  have hopen : ∀ b : Bool, IsOpen (if b then B else A) := by
    intro b
    cases b
    · exact hA
    · exact hB
  have hcov : ∀ x : X, ∃ b : Bool, x ∈ if b then B else A := by
    intro x
    have hx : x ∈ A ∪ B := by rw [hcover]; trivial
    rcases hx with hx | hx
    · exact ⟨false, hx⟩
    · exact ⟨true, hx⟩
  let _ := smallIntegralChainInclusion_quasiIso X
    (fun b : Bool => if b then B else A) hopen hcov
  dsimp only [BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion]
  infer_instance

/-- The binary-cover small homology is canonically the ambient singular
homology for an actual binary open cover. -/
def binarySmallIntegralHomologyIso
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ) (n : ℕ) :
    SmallMayerVietoris.Cycles.binarySmallSingularHomology X A B n ≅ (LocalHomology.Cycles.integralSingularChains X).homology n := by
  letI := binarySmallIntegralChainInclusion_quasiIso X A B hA hB hcover
  exact isoOfQuasiIsoAt (BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X A B) n

@[simp]
theorem binarySmallIntegralHomologyIso_hom
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ) (n : ℕ) :
    (binarySmallIntegralHomologyIso X A B hA hB hcover n).hom =
      HomologicalComplex.homologyMap (BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X A B) n := rfl

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.SmallSingularQuasiIso.Cycles
end ComponentSource_8

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.SmallSingularQuasiIso"

@[expose] public section ComponentSource_9
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.LocalExcision -/

/-! # Local Excision -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.LocalExcision

noncomputable section

/-!
# Local excision for actual integral singular homology

The relative-cover comparison starts from the actual binary small-chain
pushout. Its quotient identifies relative chains in one cover member with
small chains modulo the other cover member.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Cycles

variable (X : TopCat.{0}) (U A : Set X)

/-- The subspace of `U` lying in `A` is the actual intersection subspace of `X`. -/
def relativeIntersectionHomeomorph :
    ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' A) ≃ₜ (U ∩ A : Set X) where
  toFun u := ⟨u.1.1, u.1.2, u.2⟩
  invFun z := ⟨⟨z.1, z.2.1⟩, z.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- The map from the intersection, viewed inside `U`, to the second subspace. -/
def relativeIntersectionToRight :
    TopCat.of ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' A) ⟶ TopCat.of A :=
  LocalHomology.Cycles.subspaceMap (LocalHomology.Cycles.subspaceInclusion X U) (fun _ h => h)

/-- The binary small-chain pushout expressed using the genuine relative-pair
subspace in `U`. -/
theorem relativeCover_isPushout :
    IsPushout
      (LocalHomology.Cycles.subspaceChainInclusion (TopCat.of U) ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' A))
      (LocalHomology.Cycles.integralSingularChainFunctor.map (relativeIntersectionToRight X U A))
      (SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (SmallMayerVietoris.Cycles.binarySmallSingularLeft X U A))
      (SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (SmallMayerVietoris.Cycles.binarySmallSingularRight X U A)) := by
  refine (SmallMayerVietoris.Cycles.binarySmallChain_isPushout X U A).of_iso'
    (LocalHomology.Cycles.integralSingularChainFunctor.mapIso
      (TopCat.isoOfHomeo (relativeIntersectionHomeomorph X U A)))
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · change LocalHomology.Cycles.integralSingularChainFunctor.map _ ≫ LocalHomology.Cycles.integralSingularChainFunctor.map _ =
      LocalHomology.Cycles.integralSingularChainFunctor.map _ ≫ 𝟙 _
    rw [Category.comp_id, ← Functor.map_comp]
    rfl
  · change LocalHomology.Cycles.integralSingularChainFunctor.map _ ≫ LocalHomology.Cycles.integralSingularChainFunctor.map _ =
      LocalHomology.Cycles.integralSingularChainFunctor.map _ ≫ 𝟙 _
    rw [Category.comp_id, ← Functor.map_comp]
    rfl
  · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- The actual binary-cover small chains modulo chains in the second member. -/
abbrev binarySmallRelativeChains : ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  cokernel (SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (SmallMayerVietoris.Cycles.binarySmallSingularRight X U A))

/-- Projection from binary small chains to their quotient by chains in `A`. -/
abbrev binarySmallRelativeProjection :
    SmallMayerVietoris.Cycles.binarySmallSingularChains X U A ⟶ binarySmallRelativeChains X U A :=
  cokernel.π (SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (SmallMayerVietoris.Cycles.binarySmallSingularRight X U A))

/-- The canonical relative-cover quotient map, induced by inclusion of `U`. -/
def relativeCoverCokernelMap :
    LocalHomology.Cycles.relativeSingularChains (TopCat.of U) ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' A) ⟶
      binarySmallRelativeChains X U A :=
  cokernel.map
    (LocalHomology.Cycles.subspaceChainInclusion (TopCat.of U) ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' A))
    (SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (SmallMayerVietoris.Cycles.binarySmallSingularRight X U A))
    (LocalHomology.Cycles.integralSingularChainFunctor.map (relativeIntersectionToRight X U A))
    (SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (SmallMayerVietoris.Cycles.binarySmallSingularLeft X U A))
    (relativeCover_isPushout X U A).w

/-- A pushout preserves the quotient by the opposite cover member. -/
instance relativeCoverCokernelMap_isIso : IsIso (relativeCoverCokernelMap X U A) :=
  isIso_cokernel_map_of_isPushout (relativeCover_isPushout X U A)

/-- Relative chains in `U` are exactly small chains modulo chains in `A`. -/
def relativeCoverCokernelIso :
    LocalHomology.Cycles.relativeSingularChains (TopCat.of U) ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' A) ≅
      binarySmallRelativeChains X U A :=
  asIso (relativeCoverCokernelMap X U A)

/-- The quotient identification is induced by the actual inclusion of `U`. -/
@[reassoc (attr := simp)]
theorem relativeCoverCokernelMap_projection :
    LocalHomology.Cycles.relativeChainProjection (TopCat.of U) ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' A) ≫
        relativeCoverCokernelMap X U A =
      SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (SmallMayerVietoris.Cycles.binarySmallSingularLeft X U A) ≫
        binarySmallRelativeProjection X U A :=
  cokernel.π_desc _ _ _

/-- The actual map of relative chain complexes induced by inclusion of `U`. -/
def relativeCoverInclusion :
    LocalHomology.Cycles.relativeSingularChains (TopCat.of U) ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' A) ⟶
      LocalHomology.Cycles.relativeSingularChains X A :=
  LocalHomology.Cycles.relativeSingularChainsMap (LocalHomology.Cycles.subspaceInclusion X U) (fun _ h => h)

/-- Chains in the second member inject into the actual binary small chains. -/
instance binarySmallSingularRight_chain_mono :
    Mono (SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (SmallMayerVietoris.Cycles.binarySmallSingularRight X U A)) :=
  mono_of_mono_fac (BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion_right X U A)

/-- The quotient sequence for actual small chains relative to `A`. -/
def binarySmallRelativeSequence :
    ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ) :=
  ShortComplex.mk
    (SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (SmallMayerVietoris.Cycles.binarySmallSingularRight X U A))
    (binarySmallRelativeProjection X U A) (cokernel.condition _)

/-- The quotient sequence of small relative chains is short exact. -/
theorem binarySmallRelativeSequence_shortExact :
    (binarySmallRelativeSequence X U A).ShortExact := by
  change (ShortComplex.mk
    (SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (SmallMayerVietoris.Cycles.binarySmallSingularRight X U A))
    (cokernel.π _) _).ShortExact
  exact { exact := ShortComplex.cokernelSequence_exact _ }

/-- Canonical inclusion from small relative chains to all relative chains. -/
def binarySmallRelativeInclusion :
    binarySmallRelativeChains X U A ⟶ LocalHomology.Cycles.relativeSingularChains X A :=
  cokernel.map
    (SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (SmallMayerVietoris.Cycles.binarySmallSingularRight X U A))
    (LocalHomology.Cycles.subspaceChainInclusion X A) (𝟙 _) (BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U A)
    (by
      rw [Category.id_comp]
      exact BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion_right X U A)

/-- The small relative inclusion is induced by the actual absolute inclusion. -/
@[reassoc (attr := simp)]
theorem binarySmallRelativeInclusion_projection :
    binarySmallRelativeProjection X U A ≫ binarySmallRelativeInclusion X U A =
      BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U A ≫ LocalHomology.Cycles.relativeChainProjection X A :=
  cokernel.π_desc _ _ _

/-- Comparison of the two actual short exact sequences, identical on `C(A)`. -/
def binarySmallRelativeSequenceMap :
    binarySmallRelativeSequence X U A ⟶ LocalHomology.Cycles.relativeChainSequence X A where
  τ₁ := 𝟙 _
  τ₂ := BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U A
  τ₃ := binarySmallRelativeInclusion X U A
  comm₁₂ := by
    change 𝟙 _ ≫ LocalHomology.Cycles.subspaceChainInclusion X A =
      SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (SmallMayerVietoris.Cycles.binarySmallSingularRight X U A) ≫
        BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U A
    rw [Category.id_comp]
    exact (BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion_right X U A).symm
  comm₂₃ := (binarySmallRelativeInclusion_projection X U A).symm

/-- The relative comparison inherits a proved absolute small-chain
quasi-isomorphism by the homology sequences of these short exact sequences. -/
theorem binarySmallRelativeInclusion_quasiIso_of_small
    (hsmall : _root_.QuasiIso (BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U A)) :
    _root_.QuasiIso (binarySmallRelativeInclusion X U A) := by
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃
    (binarySmallRelativeSequenceMap X U A)
    (binarySmallRelativeSequence_shortExact X U A)
    (LocalHomology.Cycles.relativeChainSequence_shortExact X A)
    (by change _root_.QuasiIso (𝟙 _); infer_instance) hsmall

/-- The canonical relative inclusion factors through the proved quotient
identification and the canonical small relative inclusion. -/
theorem relativeCoverInclusion_factor :
    relativeCoverCokernelMap X U A ≫ binarySmallRelativeInclusion X U A =
      relativeCoverInclusion X U A := by
  apply (cancel_epi
    (LocalHomology.Cycles.relativeChainProjection (TopCat.of U) ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' A))).mp
  rw [← Category.assoc, relativeCoverCokernelMap_projection, Category.assoc,
    binarySmallRelativeInclusion_projection, ← Category.assoc,
    BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion_left]
  exact (LocalHomology.Cycles.relativeChainProjection_naturality (LocalHomology.Cycles.subspaceInclusion X U) (fun _ h => h)).symm

/-- Relative excision follows from the actual absolute small-chain
quasi-isomorphism; the quotient identification is a chain isomorphism. -/
theorem relativeCoverInclusion_quasiIso_of_small
    (hsmall : _root_.QuasiIso (BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X U A)) :
    _root_.QuasiIso (relativeCoverInclusion X U A) := by
  have := binarySmallRelativeInclusion_quasiIso_of_small X U A hsmall
  rw [← relativeCoverInclusion_factor]
  infer_instance

/-- For an actual binary open cover, the canonical inclusion of small relative
chains is a quasi-isomorphism. -/
theorem binarySmallRelativeInclusion_quasiIso
    (hU : IsOpen U) (hA : IsOpen A) (hcover : U ∪ A = Set.univ) :
    _root_.QuasiIso (binarySmallRelativeInclusion X U A) :=
  binarySmallRelativeInclusion_quasiIso_of_small X U A
    (SmallSingularQuasiIso.Cycles.binarySmallIntegralChainInclusion_quasiIso X U A hU hA hcover)

/-- Relative excision for a binary open cover, proved for the actual inclusion
of pairs `(U, U ∩ A) → (X, A)`. -/
theorem relativeCoverInclusion_quasiIso
    (hU : IsOpen U) (hA : IsOpen A) (hcover : U ∪ A = Set.univ) :
    _root_.QuasiIso (relativeCoverInclusion X U A) :=
  relativeCoverInclusion_quasiIso_of_small X U A
    (SmallSingularQuasiIso.Cycles.binarySmallIntegralChainInclusion_quasiIso X U A hU hA hcover)

/-- The relative homology isomorphism of a binary open cover is induced by
the genuine inclusion of pairs. -/
def relativeCoverHomologyIso
    (hU : IsOpen U) (hA : IsOpen A) (hcover : U ∪ A = Set.univ) (n : ℕ) :
    LocalHomology.Cycles.relativeSingularHomology (TopCat.of U) ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' A) n ≅
      LocalHomology.Cycles.relativeSingularHomology X A n := by
  have := relativeCoverInclusion_quasiIso X U A hU hA hcover
  exact isoOfQuasiIsoAt (relativeCoverInclusion X U A) n

@[simp]
theorem relativeCoverHomologyIso_hom
    (hU : IsOpen U) (hA : IsOpen A) (hcover : U ∪ A = Set.univ) (n : ℕ) :
    (relativeCoverHomologyIso X U A hU hA hcover n).hom =
      HomologicalComplex.homologyMap (relativeCoverInclusion X U A) n := rfl

variable (x : X) (hx : x ∈ U)

/-- The actual map of punctured pairs induced by the inclusion of `U` into `X`. -/
def localExcisionChainMap :
    LocalHomology.Cycles.relativeSingularChains (TopCat.of U) ({(⟨x, hx⟩ : U)}ᶜ : Set U) ⟶
      LocalHomology.Cycles.relativeSingularChains X ({x}ᶜ : Set X) :=
  LocalHomology.Cycles.relativeSingularChainsMap (LocalHomology.Cycles.subspaceInclusion X U) (by
    intro y hy
    change y.1 ≠ x
    change y ≠ (⟨x, hx⟩ : U) at hy
    exact fun h => hy (Subtype.ext h))

/-- The punctured subspace of `U` is the preimage of the ambient punctured space;
the relative-chain isomorphism is induced by the identity homeomorphism. -/
def localRelativePreimageIso :
    LocalHomology.Cycles.relativeSingularChains (TopCat.of U) ({(⟨x, hx⟩ : U)}ᶜ : Set U) ≅
      LocalHomology.Cycles.relativeSingularChains (TopCat.of U) ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' ({x}ᶜ : Set X)) :=
  LocalHomology.Cycles.relativeSingularChainsIso (Homeomorph.refl (TopCat.of U)) (by
    intro y
    change y ≠ (⟨x, hx⟩ : U) ↔ y.1 ≠ x
    exact not_congr Subtype.ext_iff)

/-- The punctured-subspace identification does not change absolute chains. -/
@[reassoc (attr := simp)]
theorem localRelativePreimageIso_projection :
    LocalHomology.Cycles.relativeChainProjection (TopCat.of U) ({(⟨x, hx⟩ : U)}ᶜ : Set U) ≫
        (localRelativePreimageIso X U x hx).hom =
      LocalHomology.Cycles.relativeChainProjection (TopCat.of U)
        ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' ({x}ᶜ : Set X)) := by
  have h : Set.MapsTo (𝟙 (TopCat.of U)) ({(⟨x, hx⟩ : U)}ᶜ : Set U)
      ((LocalHomology.Cycles.subspaceInclusion X U) ⁻¹' ({x}ᶜ : Set X)) := by
    intro y hy
    change y.1 ≠ x
    change y ≠ (⟨x, hx⟩ : U) at hy
    exact fun h => hy (Subtype.ext h)
  change _ ≫ LocalHomology.Cycles.relativeSingularChainsMap (𝟙 (TopCat.of U)) h = _
  rw [LocalHomology.Cycles.relativeChainProjection_naturality, CategoryTheory.Functor.map_id, Category.id_comp]

/-- Local excision is the relative-cover inclusion after the identity
identification of the two punctured-subspace presentations. -/
theorem localExcisionChainMap_factor :
    (localRelativePreimageIso X U x hx).hom ≫ relativeCoverInclusion X U ({x}ᶜ : Set X) =
      localExcisionChainMap X U x hx := by
  apply (cancel_epi
    (LocalHomology.Cycles.relativeChainProjection (TopCat.of U) ({(⟨x, hx⟩ : U)}ᶜ : Set U))).mp
  rw [← Category.assoc, localRelativePreimageIso_projection]
  exact (LocalHomology.Cycles.relativeChainProjection_naturality (LocalHomology.Cycles.subspaceInclusion X U) (fun _ h => h)).trans
    (LocalHomology.Cycles.relativeChainProjection_naturality (LocalHomology.Cycles.subspaceInclusion X U) _).symm

/-- Local excision: an open neighborhood of a point in a T1 space induces a
quasi-isomorphism on the actual punctured relative singular chain complexes. -/
theorem localExcisionChainMap_quasiIso [T1Space X] (hU : IsOpen U) :
    _root_.QuasiIso (localExcisionChainMap X U x hx) := by
  have hcover : U ∪ ({x}ᶜ : Set X) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    by_cases hy : y = x
    · subst y
      exact Or.inl hx
    · exact Or.inr (by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hy)
  have := relativeCoverInclusion_quasiIso X U ({x}ᶜ : Set X)
    hU isOpen_compl_singleton hcover
  rw [← localExcisionChainMap_factor X U x hx]
  infer_instance

/-- The canonical local homology isomorphism induced by an open-neighborhood
inclusion, with no excision or local-orientation assumption. -/
def localExcisionHomologyIso [T1Space X] (hU : IsOpen U) (n : ℕ) :
    LocalHomology.Cycles.localSingularHomology (TopCat.of U) (⟨x, hx⟩ : U) n ≅
      LocalHomology.Cycles.localSingularHomology X x n := by
  have := localExcisionChainMap_quasiIso X U x hx hU
  exact isoOfQuasiIsoAt (localExcisionChainMap X U x hx) n

@[simp]
theorem localExcisionHomologyIso_hom [T1Space X] (hU : IsOpen U) (n : ℕ) :
    (localExcisionHomologyIso X U x hx hU n).hom =
      HomologicalComplex.homologyMap (localExcisionChainMap X U x hx) n := rfl

end Cycles

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.LocalExcision
end ComponentSource_9

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.LocalExcision"

@[expose] public section ComponentSource_10
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.NormalSphere -/

/-! # Normal Sphere -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.NormalSphere.Cycles

noncomputable section

/-!
# The sphere in a punctured normal space

Radial normalization is a strong deformation retraction from a punctured real
normed vector space to its unit sphere. This applies in particular to the real
normed space underlying a complex normal coordinate space. The construction
uses mathlib's actual polar-coordinate homeomorphism; it makes no assertion
about sphere homology or the existence of a Thom class.
-/

open unitInterval

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The complement of the origin in a normal coordinate vector space. -/
abbrev PuncturedNormal := ({0}ᶜ : Set E)

/-- The actual unit sphere of a normal coordinate vector space. -/
abbrev NormalUnitSphere := Metric.sphere (0 : E) 1

def radiusOne : Set.Ioi (0 : ℝ) := ⟨1, by change (0 : ℝ) < 1; exact zero_lt_one⟩

/-- Radial projection to the sphere in polar coordinates. -/
def normalSphereProjection : C(PuncturedNormal E, NormalUnitSphere E) where
  toFun x := (homeomorphUnitSphereProd E x).1
  continuous_toFun := (homeomorphUnitSphereProd E).continuous.fst

/-- Inclusion of the unit sphere into the punctured normal space. -/
def normalSphereInclusion : C(NormalUnitSphere E, PuncturedNormal E) where
  toFun x := (homeomorphUnitSphereProd E).symm (x, radiusOne)
  continuous_toFun := (homeomorphUnitSphereProd E).symm.continuous.comp
    (continuous_id.prodMk continuous_const)

@[simp]
theorem normalSphereProjection_coe (x : PuncturedNormal E) :
    ((normalSphereProjection E x : NormalUnitSphere E) : E) = ‖(x : E)‖⁻¹ • (x : E) := by
  simp [normalSphereProjection, homeomorphUnitSphereProd_apply_fst_coe]

@[simp]
theorem normalSphereInclusion_coe (x : NormalUnitSphere E) :
    ((normalSphereInclusion E x : PuncturedNormal E) : E) = (x : E) := by
  simp [normalSphereInclusion, homeomorphUnitSphereProd_symm_apply_coe, radiusOne]

@[simp]
theorem normalSphereProjection_inclusion (x : NormalUnitSphere E) :
    normalSphereProjection E (normalSphereInclusion E x) = x := by
  change ((homeomorphUnitSphereProd E)
    ((homeomorphUnitSphereProd E).symm (x, radiusOne))).1 = x
  rw [(homeomorphUnitSphereProd E).apply_symm_apply]

def interpolateRadius (t : I) (r : Set.Ioi (0 : ℝ)) : Set.Ioi (0 : ℝ) :=
  ⟨(1 - (t : ℝ)) * (r : ℝ) + (t : ℝ), by
    have ht0 : 0 ≤ (t : ℝ) := t.property.1
    have ht1 : (t : ℝ) ≤ 1 := t.property.2
    have hr : 0 < (r : ℝ) := r.property
    rcases lt_or_eq_of_le ht0 with ht | ht
    · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr ht1) hr.le) ht
    · simp [← ht]⟩

theorem continuous_interpolateRadius :
    Continuous (fun z : I × Set.Ioi (0 : ℝ) => interpolateRadius z.1 z.2) := by
  unfold interpolateRadius
  fun_prop

@[simp]
theorem interpolateRadius_zero (r : Set.Ioi (0 : ℝ)) :
    interpolateRadius 0 r = r := by
  apply Subtype.ext
  simp [interpolateRadius]

@[simp]
theorem interpolateRadius_one (r : Set.Ioi (0 : ℝ)) :
    interpolateRadius 1 r = radiusOne := by
  apply Subtype.ext
  simp [interpolateRadius, radiusOne]

@[simp]
theorem interpolateRadius_radiusOne (t : I) :
    interpolateRadius t radiusOne = radiusOne := by
  apply Subtype.ext
  simp [interpolateRadius, radiusOne]

/-- Radial contraction to the unit sphere, fixed at every point of that sphere
throughout the homotopy. The radius changes from `r` to `(1-t)*r+t`. -/
def normalSphereDeformation :
    ContinuousMap.HomotopyRel (ContinuousMap.id (PuncturedNormal E))
      ((normalSphereInclusion E).comp (normalSphereProjection E))
      (Set.range (normalSphereInclusion E)) where
  toFun z := (homeomorphUnitSphereProd E).symm
    ((homeomorphUnitSphereProd E z.2).1,
      interpolateRadius z.1 (homeomorphUnitSphereProd E z.2).2)
  continuous_toFun := (homeomorphUnitSphereProd E).symm.continuous.comp
    (((homeomorphUnitSphereProd E).continuous.fst.comp continuous_snd).prodMk
      (continuous_interpolateRadius.comp
        (continuous_fst.prodMk ((homeomorphUnitSphereProd E).continuous.snd.comp continuous_snd))))
  map_zero_left x := by
    change (homeomorphUnitSphereProd E).symm
      ((homeomorphUnitSphereProd E x).1,
        interpolateRadius 0 (homeomorphUnitSphereProd E x).2) = x
    rw [interpolateRadius_zero]
    exact (homeomorphUnitSphereProd E).symm_apply_apply x
  map_one_left x := by
    change (homeomorphUnitSphereProd E).symm
      ((homeomorphUnitSphereProd E x).1,
        interpolateRadius 1 (homeomorphUnitSphereProd E x).2) =
      (homeomorphUnitSphereProd E).symm ((homeomorphUnitSphereProd E x).1, radiusOne)
    rw [interpolateRadius_one]
  prop' t x hx := by
    rcases hx with ⟨y, rfl⟩
    change (homeomorphUnitSphereProd E).symm
      (((homeomorphUnitSphereProd E) ((homeomorphUnitSphereProd E).symm (y, radiusOne))).1,
        interpolateRadius t
          (((homeomorphUnitSphereProd E) ((homeomorphUnitSphereProd E).symm (y, radiusOne))).2)) =
      (homeomorphUnitSphereProd E).symm (y, radiusOne)
    rw [(homeomorphUnitSphereProd E).apply_symm_apply]
    simp only [interpolateRadius_radiusOne]

/-- The radial deformation has the usual positive scalar interpolation formula. -/
theorem normalSphereDeformation_coe (t : I) (x : PuncturedNormal E) :
    (((normalSphereDeformation E) (t, x) : PuncturedNormal E) : E) =
      (((1 - (t : ℝ)) * ‖(x : E)‖ + (t : ℝ)) / ‖(x : E)‖) • (x : E) := by
  change (((homeomorphUnitSphereProd E).symm
    ((homeomorphUnitSphereProd E x).1,
      interpolateRadius t (homeomorphUnitSphereProd E x).2) : PuncturedNormal E) : E) = _
  rw [homeomorphUnitSphereProd_symm_apply_coe]
  simp only [interpolateRadius, homeomorphUnitSphereProd_apply_fst_coe,
    homeomorphUnitSphereProd_apply_snd_coe, smul_smul, div_eq_mul_inv]

@[simp]
theorem normalSphereDeformation_fixed (t : I) (x : NormalUnitSphere E) :
    (normalSphereDeformation E) (t, normalSphereInclusion E x) = normalSphereInclusion E x := by
  exact (normalSphereDeformation E).eq_fst t (Set.mem_range_self x)

/-- The punctured normal coordinate space and its unit sphere are homotopy
equivalent, via the explicit radial deformation retraction. -/
def normalSphereHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (PuncturedNormal E) (NormalUnitSphere E) where
  toFun := normalSphereProjection E
  invFun := normalSphereInclusion E
  left_inv := ⟨(normalSphereDeformation E).toHomotopy.symm⟩
  right_inv := by
    have h : (normalSphereProjection E).comp (normalSphereInclusion E) =
        ContinuousMap.id (NormalUnitSphere E) := by
      apply ContinuousMap.ext
      intro x
      exact normalSphereProjection_inclusion E x
    rw [h]

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.NormalSphere.Cycles
end ComponentSource_10

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.NormalSphere"

@[expose] public section ComponentSource_11
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.NormalSphereHomology -/

/-! # Normal Sphere Homology -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.NormalSphereHomology.Cycles

noncomputable section

/-!
# Singular homology of the punctured normal model

The actual radial homotopy equivalence identifies singular homology of the
punctured normal space with singular homology of its sphere. No computation of
sphere homology, orientation generator, or Thom class is assumed here.
-/

open _root_.CategoryTheory _root_.AlgebraicTopology

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {R : Type} [Ring R]

/-- Radial retraction gives a chain homotopy equivalence for genuine singular
chains with any coefficient module. -/
def normalSphereSingularChainsEquiv (M : ModuleCat.{0} R) :
    _root_.HomotopyEquiv
      (((singularChainComplexFunctor (ModuleCat.{0} R)).obj M).obj
        (TopCat.of (NormalSphere.Cycles.PuncturedNormal E)))
      (((singularChainComplexFunctor (ModuleCat.{0} R)).obj M).obj
        (TopCat.of (NormalSphere.Cycles.NormalUnitSphere E))) :=
  ContractibleModel.Cycles.singularChainsHomotopyEquiv M
    (X := TopCat.of (NormalSphere.Cycles.PuncturedNormal E)) (Y := TopCat.of (NormalSphere.Cycles.NormalUnitSphere E))
    (NormalSphere.Cycles.normalSphereHomotopyEquiv E)

/-- The induced genuine singular-homology isomorphism from punctured normal
coordinates to the unit sphere. -/
def normalSphereSingularHomologyIso (M : ModuleCat.{0} R) (n : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{0} R) n).obj M).obj
        (TopCat.of (NormalSphere.Cycles.PuncturedNormal E)) ≅
      ((singularHomologyFunctor (ModuleCat.{0} R) n).obj M).obj
        (TopCat.of (NormalSphere.Cycles.NormalUnitSphere E)) :=
  ContractibleModel.Cycles.singularHomologyIsoOfHomotopyEquiv M
    (X := TopCat.of (NormalSphere.Cycles.PuncturedNormal E)) (Y := TopCat.of (NormalSphere.Cycles.NormalUnitSphere E))
    (NormalSphere.Cycles.normalSphereHomotopyEquiv E) n

@[simp]
theorem normalSphereSingularHomologyIso_hom (M : ModuleCat.{0} R) (n : ℕ) :
    (normalSphereSingularHomologyIso E M n).hom =
      ((singularHomologyFunctor (ModuleCat.{0} R) n).obj M).map
        (TopCat.ofHom (NormalSphere.Cycles.normalSphereProjection E)) := rfl

@[simp]
theorem normalSphereSingularHomologyIso_inv (M : ModuleCat.{0} R) (n : ℕ) :
    (normalSphereSingularHomologyIso E M n).inv =
      ((singularHomologyFunctor (ModuleCat.{0} R) n).obj M).map
        (TopCat.ofHom (NormalSphere.Cycles.normalSphereInclusion E)) := rfl

/-- The integral specialization uses the same singular chains as the local
homology pair construction. -/
def normalSphereIntegralHomologyIso (n : ℕ) :
    (LocalHomology.Cycles.integralSingularChains (TopCat.of (NormalSphere.Cycles.PuncturedNormal E))).homology n ≅
      (LocalHomology.Cycles.integralSingularChains (TopCat.of (NormalSphere.Cycles.NormalUnitSphere E))).homology n :=
  normalSphereSingularHomologyIso E (ModuleCat.of ℤ ℤ) n

@[simp]
theorem normalSphereIntegralHomologyIso_hom (n : ℕ) :
    (normalSphereIntegralHomologyIso E n).hom =
      HomologicalComplex.homologyMap
        (LocalHomology.Cycles.integralSingularChainFunctor.map (TopCat.ofHom (NormalSphere.Cycles.normalSphereProjection E))) n := rfl

@[simp]
theorem normalSphereIntegralHomologyIso_inv (n : ℕ) :
    (normalSphereIntegralHomologyIso E n).inv =
      HomologicalComplex.homologyMap
        (LocalHomology.Cycles.integralSingularChainFunctor.map (TopCat.ofHom (NormalSphere.Cycles.normalSphereInclusion E))) n := rfl

/-- In the complex normal model this is the sphere step needed for the
relative pair `(C^p, C^p \ {0})`. -/
def complexNormalSphereIntegralHomologyIso (p n : ℕ) :
    (LocalHomology.Cycles.integralSingularChains (TopCat.of (NormalSphere.Cycles.PuncturedNormal (Fin p → ℂ)))).homology n ≅
      (LocalHomology.Cycles.integralSingularChains (TopCat.of (NormalSphere.Cycles.NormalUnitSphere (Fin p → ℂ)))).homology n :=
  normalSphereIntegralHomologyIso (Fin p → ℂ) n

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.NormalSphereHomology.Cycles
end ComponentSource_11

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.NormalSphereHomology"

@[expose] public section ComponentSource_12
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.NormalNormChange -/

/-! # Normal Norm Change -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.NormalNormChange.Cycles

noncomputable section

/-!
# Changing the norm in local normal-space models

The ordinary function space `Fin p → ℂ` has the sup norm, whereas the Euclidean
model uses the `L²` norm. Their unit spheres are not definitionally the same.
An actual continuous linear equivalence identifies their punctured spaces;
the proved radial homotopy equivalences then identify their sphere homology.
No sphere-homology computation or orientation generator is assumed here.
-/

open _root_.CategoryTheory _root_.AlgebraicTopology

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A continuous linear coordinate change gives an actual homeomorphism of
the punctured normal spaces. -/
def puncturedNormalHomeomorph (e : E ≃L[ℝ] F) :
    NormalSphere.Cycles.PuncturedNormal E ≃ₜ NormalSphere.Cycles.PuncturedNormal F :=
  e.toHomeomorph.subtype (by
    intro x
    change x ≠ 0 ↔ e x ≠ 0
    constructor
    · intro hx he
      apply hx
      apply e.injective
      simpa only [map_zero] using he
    · intro hx he
      apply hx
      simp only [he, map_zero])

@[simp]
theorem puncturedNormalHomeomorph_apply (e : E ≃L[ℝ] F)
    (x : NormalSphere.Cycles.PuncturedNormal E) :
    ((puncturedNormalHomeomorph e x : NormalSphere.Cycles.PuncturedNormal F) : F) = e x := rfl

/-- Radial projection and inclusion transfer a change of normal coordinates
to a genuine homotopy equivalence of the corresponding unit spheres. -/
def normalSphereChange (e : E ≃L[ℝ] F) :
    ContinuousMap.HomotopyEquiv (NormalSphere.Cycles.NormalUnitSphere E) (NormalSphere.Cycles.NormalUnitSphere F) :=
  (NormalSphere.Cycles.normalSphereHomotopyEquiv E).symm.trans
    ((puncturedNormalHomeomorph e).toHomotopyEquiv.trans
      (NormalSphere.Cycles.normalSphereHomotopyEquiv F))

/-- The forward map is the normalized linear coordinate change. -/
theorem normalSphereChange_apply_coe (e : E ≃L[ℝ] F) (x : NormalSphere.Cycles.NormalUnitSphere E) :
    ((normalSphereChange e x : NormalSphere.Cycles.NormalUnitSphere F) : F) =
      ‖e (x : E)‖⁻¹ • e (x : E) := by
  change ((NormalSphere.Cycles.normalSphereProjection F
    (puncturedNormalHomeomorph e (NormalSphere.Cycles.normalSphereInclusion E x)) : NormalSphere.Cycles.NormalUnitSphere F) : F) = _
  rw [NormalSphere.Cycles.normalSphereProjection_coe, puncturedNormalHomeomorph_apply,
    NormalSphere.Cycles.normalSphereInclusion_coe]

/-- The resulting sphere-homology isomorphism is induced by actual maps. -/
def normalSphereHomologyChange (e : E ≃L[ℝ] F) (n : ℕ) :
    (LocalHomology.Cycles.integralSingularChains (TopCat.of (NormalSphere.Cycles.NormalUnitSphere E))).homology n ≅
      (LocalHomology.Cycles.integralSingularChains (TopCat.of (NormalSphere.Cycles.NormalUnitSphere F))).homology n :=
  ContractibleModel.Cycles.singularHomologyIsoOfHomotopyEquiv (ModuleCat.of ℤ ℤ)
    (X := TopCat.of (NormalSphere.Cycles.NormalUnitSphere E)) (Y := TopCat.of (NormalSphere.Cycles.NormalUnitSphere F))
    (normalSphereChange e) n

/-- The genuine real continuous linear equivalence between sup-norm complex
coordinates and their Euclidean version. -/
def complexPiEuclideanRealEquiv (p : ℕ) :
    (Fin p → ℂ) ≃L[ℝ] EuclideanSpace ℂ (Fin p) where
  toLinearEquiv := (EuclideanSpace.equiv (Fin p) ℂ).symm.toLinearEquiv.restrictScalars ℝ
  continuous_toFun := (EuclideanSpace.equiv (Fin p) ℂ).symm.continuous
  continuous_invFun := (EuclideanSpace.equiv (Fin p) ℂ).continuous

/-- The sup-norm and Euclidean-norm complex coordinate spheres have the same
homotopy type through explicitly constructed radial maps. -/
def complexEuclideanSphereChange (p : ℕ) :
    ContinuousMap.HomotopyEquiv (NormalSphere.Cycles.NormalUnitSphere (Fin p → ℂ))
      (NormalSphere.Cycles.NormalUnitSphere (EuclideanSpace ℂ (Fin p))) :=
  normalSphereChange (complexPiEuclideanRealEquiv p)

/-- In particular their actual integral singular homology groups are isomorphic. -/
def complexEuclideanSphereHomologyChange (p n : ℕ) :
    (LocalHomology.Cycles.integralSingularChains (TopCat.of (NormalSphere.Cycles.NormalUnitSphere (Fin p → ℂ)))).homology n ≅
      (LocalHomology.Cycles.integralSingularChains
        (TopCat.of (NormalSphere.Cycles.NormalUnitSphere (EuclideanSpace ℂ (Fin p))))).homology n :=
  normalSphereHomologyChange (complexPiEuclideanRealEquiv p) n

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.NormalNormChange.Cycles
end ComponentSource_12

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.NormalNormChange"

@[expose] public section ComponentSource_13
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.LocalNormalHomology -/

/-! # Local Normal Homology -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.LocalNormalHomology.Cycles

noncomputable section

/-!
# Local singular homology of complex normal coordinates

The positive-degree connecting isomorphism of the actual pair
`(ℂ^p, ℂ^p \ {0})` combines with the explicit radial homotopy equivalence.
This reduces local homology in degrees at least two to homology of the actual
unit sphere. It does not assume or establish the computation of sphere homology,
a preferred generator, or an orientation-to-fundamental-class theorem.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

/-- For a complex normal model, the actual relative boundary identifies local
homology in degree `n+1` with punctured-space homology in positive degree `n`. -/
def complexNormalLocalBoundaryIso (p n : ℕ) (hn : n ≠ 0) :
    LocalHomology.Cycles.localSingularHomology (TopCat.of (Fin p → ℂ)) 0 (n + 1) ≅
      RelativeHomologyExact.Cycles.integralSingularHomology (TopCat.of (NormalSphere.Cycles.PuncturedNormal (Fin p → ℂ))) n :=
  RelativeHomologyExact.Cycles.relativeHomologyBoundaryIso (TopCat.of (Fin p → ℂ)) ({0}ᶜ : Set (Fin p → ℂ)) n
    (ContractibleModel.Cycles.isZero_complexNormalModelHomology p (n + 1) (Nat.succ_ne_zero n))
    (ContractibleModel.Cycles.isZero_complexNormalModelHomology p n hn)

/-- The preceding isomorphism is the connecting boundary itself. -/
@[simp]
theorem complexNormalLocalBoundaryIso_hom (p n : ℕ) (hn : n ≠ 0) :
    (complexNormalLocalBoundaryIso p n hn).hom =
      RelativeHomologyExact.Cycles.relativeHomologyBoundary (TopCat.of (Fin p → ℂ)) ({0}ᶜ : Set (Fin p → ℂ)) n :=
  rfl

/-- Genuine local singular homology reduces to genuine unit-sphere homology by
the relative boundary followed by the explicitly constructed radial map. -/
def complexNormalLocalSphereIso (p n : ℕ) (hn : n ≠ 0) :
    LocalHomology.Cycles.localSingularHomology (TopCat.of (Fin p → ℂ)) 0 (n + 1) ≅
      RelativeHomologyExact.Cycles.integralSingularHomology (TopCat.of (NormalSphere.Cycles.NormalUnitSphere (Fin p → ℂ))) n :=
  complexNormalLocalBoundaryIso p n hn ≪≫ NormalSphereHomology.Cycles.complexNormalSphereIntegralHomologyIso p n

/-- The local-to-sphere comparison uses the actual boundary and singular-homology
map induced by radial projection, rather than an arbitrarily chosen isomorphism. -/
@[simp]
theorem complexNormalLocalSphereIso_hom (p n : ℕ) (hn : n ≠ 0) :
    (complexNormalLocalSphereIso p n hn).hom =
      RelativeHomologyExact.Cycles.relativeHomologyBoundary (TopCat.of (Fin p → ℂ)) ({0}ᶜ : Set (Fin p → ℂ)) n ≫
        RelativeHomologyExact.Cycles.integralSingularHomologyMap
          (TopCat.ofHom (NormalSphere.Cycles.normalSphereProjection (Fin p → ℂ))) n :=
  rfl

/-- In every positive complex dimension `p+1`, the top local degree `2p+2`
reduces to sphere degree `2p+1`. No value of that sphere homology is assumed. -/
def positiveComplexNormalTopLocalSphereIso (p : ℕ) :
    LocalHomology.Cycles.localSingularHomology (TopCat.of (Fin (p + 1) → ℂ)) 0 (2 * p + 2) ≅
      RelativeHomologyExact.Cycles.integralSingularHomology
        (TopCat.of (NormalSphere.Cycles.NormalUnitSphere (Fin (p + 1) → ℂ))) (2 * p + 1) :=
  complexNormalLocalSphereIso (p + 1) (2 * p + 1) (Nat.succ_ne_zero (2 * p))

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.LocalNormalHomology.Cycles
end ComponentSource_13

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.LocalNormalHomology"

@[expose] public section ComponentSource_14
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.RealComplexNormalModel -/

/-! # Real Complex Normal Model -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.RealComplexNormalModel.Cycles

noncomputable section

/-!
# Explicit real coordinates on a complex normal model

Each complex coordinate is sent to its real and imaginary parts in that order.
The paired coordinates are then flattened to `Fin (2 * p)`. These are actual
continuous linear equivalences, so they give maps of the punctured spaces and
the relative singular-chain models. Radial retraction also gives the induced
comparison of unit-sphere homology, despite the different norms on the models.

This file does not identify a local homology generator with an orientation.
-/

open _root_.CategoryTheory

/-- A complex number in the ordered real coordinates `(Re, Im)`. -/
def complexCoordinatePair : ℂ ≃L[ℝ] (Fin 2 → ℝ) :=
  Complex.equivRealProdCLM.trans (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm

@[simp]
theorem complexCoordinatePair_zero (z : ℂ) : complexCoordinatePair z 0 = z.re := rfl

@[simp]
theorem complexCoordinatePair_one (z : ℂ) : complexCoordinatePair z 1 = z.im := rfl

@[simp]
theorem complexCoordinatePair_symm_apply (x : Fin 2 → ℝ) :
    complexCoordinatePair.symm x = x 0 + x 1 * Complex.I := by
  change Complex.equivRealProdCLM.symm (x 0, x 1) = _
  exact Complex.equivRealProdCLM_symm_apply _

/-- The explicit real coordinate equivalence before flattening the indices. -/
def complexPairedRealEquiv (p : ℕ) :
    (Fin p → ℂ) ≃L[ℝ] (Fin p × Fin 2 → ℝ) where
  toFun z ij := complexCoordinatePair (z ij.1) ij.2
  invFun x i := complexCoordinatePair.symm (fun j ↦ x (i, j))
  left_inv z := by
    funext i
    exact complexCoordinatePair.symm_apply_apply (z i)
  right_inv x := by
    funext ij
    exact congrFun (complexCoordinatePair.apply_symm_apply (fun j ↦ x (ij.1, j))) ij.2
  map_add' z w := by
    funext ij
    exact congrFun (map_add complexCoordinatePair (z ij.1) (w ij.1)) ij.2
  map_smul' r z := by
    funext ij
    exact congrFun (map_smul complexCoordinatePair r (z ij.1)) ij.2
  continuous_toFun := by
    apply continuous_pi
    intro ij
    exact (continuous_apply ij.2).comp
      (complexCoordinatePair.continuous.comp (continuous_apply ij.1))
  continuous_invFun := by
    apply continuous_pi
    intro i
    apply complexCoordinatePair.symm.continuous.comp
    exact continuous_pi fun j ↦ continuous_apply (i, j)

@[simp]
theorem complexPairedRealEquiv_apply (p : ℕ) (z : Fin p → ℂ) (i : Fin p) (j : Fin 2) :
    complexPairedRealEquiv p z (i, j) = complexCoordinatePair (z i) j := rfl

/-- The pair `(i,j)` becomes coordinate `2*i+j`; real and imaginary parts are
adjacent, rather than collected in two separate blocks. -/
def complexInterleavedIndex (p : ℕ) : Fin p × Fin 2 ≃ Fin (2 * p) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm p 2))

@[simp]
theorem complexInterleavedIndex_val (p : ℕ) (i : Fin p) (j : Fin 2) :
    (complexInterleavedIndex p (i, j)).val = 2 * i.val + j.val := by
  change j.val + 2 * i.val = 2 * i.val + j.val
  exact Nat.add_comm _ _

/-- Real and imaginary parts, in interleaved order, identify the complex
normal model with real Euclidean space of twice its dimension. -/
def complexRealEuclideanEquiv (p : ℕ) :
    (Fin p → ℂ) ≃L[ℝ] EuclideanSpace ℝ (Fin (2 * p)) :=
  (complexPairedRealEquiv p).trans
    ((ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin (2 * p) ↦ ℝ)
      (complexInterleavedIndex p)).trans
      (EuclideanSpace.equiv (Fin (2 * p)) ℝ).symm)

@[simp]
theorem complexRealEuclideanEquiv_apply_pair (p : ℕ) (z : Fin p → ℂ)
    (i : Fin p) (j : Fin 2) :
    complexRealEuclideanEquiv p z (complexInterleavedIndex p (i, j)) =
      complexCoordinatePair (z i) j := by
  change Equiv.piCongrLeft (fun _ : Fin (2 * p) ↦ ℝ) (complexInterleavedIndex p)
    (complexPairedRealEquiv p z) (complexInterleavedIndex p (i, j)) = _
  exact Equiv.piCongrLeft_apply_apply _ _ _ _

@[simp]
theorem complexRealEuclideanEquiv_apply_re (p : ℕ) (z : Fin p → ℂ) (i : Fin p) :
    complexRealEuclideanEquiv p z (complexInterleavedIndex p (i, 0)) = (z i).re := by
  rw [complexRealEuclideanEquiv_apply_pair, complexCoordinatePair_zero]

@[simp]
theorem complexRealEuclideanEquiv_apply_im (p : ℕ) (z : Fin p → ℂ) (i : Fin p) :
    complexRealEuclideanEquiv p z (complexInterleavedIndex p (i, 1)) = (z i).im := by
  rw [complexRealEuclideanEquiv_apply_pair, complexCoordinatePair_one]

/-- The inverse recombines each adjacent pair as `x + y I`. -/
theorem complexRealEuclideanEquiv_symm_apply (p : ℕ)
    (x : EuclideanSpace ℝ (Fin (2 * p))) (i : Fin p) :
    (complexRealEuclideanEquiv p).symm x i =
      x (complexInterleavedIndex p (i, 0)) +
        x (complexInterleavedIndex p (i, 1)) * Complex.I := by
  have hre := complexRealEuclideanEquiv_apply_re p ((complexRealEuclideanEquiv p).symm x) i
  have him := complexRealEuclideanEquiv_apply_im p ((complexRealEuclideanEquiv p).symm x) i
  rw [ContinuousLinearEquiv.apply_symm_apply] at hre him
  rw [hre, him]
  exact (Complex.re_add_im _).symm

/-- The explicit coordinate change restricts to the actual punctured spaces. -/
def complexRealPuncturedHomeomorph (p : ℕ) :
    NormalSphere.Cycles.PuncturedNormal (Fin p → ℂ) ≃ₜ
      NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (2 * p))) :=
  NormalNormChange.Cycles.puncturedNormalHomeomorph (complexRealEuclideanEquiv p)

/-- The punctured-space homology comparison comes from the coordinate
homeomorphism itself. -/
def complexRealPuncturedHomologyIso (p n : ℕ) :
    RelativeHomologyExact.Cycles.integralSingularHomology (TopCat.of (NormalSphere.Cycles.PuncturedNormal (Fin p → ℂ))) n ≅
      RelativeHomologyExact.Cycles.integralSingularHomology
        (TopCat.of (NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (2 * p))))) n :=
  ContractibleModel.Cycles.singularHomologyIsoOfHomotopyEquiv (ModuleCat.of ℤ ℤ)
    (X := TopCat.of (NormalSphere.Cycles.PuncturedNormal (Fin p → ℂ)))
    (Y := TopCat.of (NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (2 * p)))))
    (complexRealPuncturedHomeomorph p).toHomotopyEquiv n

/-- Normalizing the interleaved coordinate change gives a homotopy equivalence
of the complex sup-norm sphere with the real Euclidean unit sphere. -/
def complexRealSphereHomotopyEquiv (p : ℕ) :
    ContinuousMap.HomotopyEquiv (NormalSphere.Cycles.NormalUnitSphere (Fin p → ℂ))
      (NormalSphere.Cycles.NormalUnitSphere (EuclideanSpace ℝ (Fin (2 * p)))) :=
  NormalNormChange.Cycles.normalSphereChange (complexRealEuclideanEquiv p)

theorem complexRealSphereHomotopyEquiv_apply_coe (p : ℕ)
    (x : NormalSphere.Cycles.NormalUnitSphere (Fin p → ℂ)) :
    ((complexRealSphereHomotopyEquiv p x :
      NormalSphere.Cycles.NormalUnitSphere (EuclideanSpace ℝ (Fin (2 * p)))) :
      EuclideanSpace ℝ (Fin (2 * p))) =
        ‖complexRealEuclideanEquiv p (x : Fin p → ℂ)‖⁻¹ •
          complexRealEuclideanEquiv p (x : Fin p → ℂ) :=
  NormalNormChange.Cycles.normalSphereChange_apply_coe (complexRealEuclideanEquiv p) x

/-- The homology comparison is induced by these explicit maps of spheres. -/
def complexRealSphereHomologyIso (p n : ℕ) :
    RelativeHomologyExact.Cycles.integralSingularHomology (TopCat.of (NormalSphere.Cycles.NormalUnitSphere (Fin p → ℂ))) n ≅
      RelativeHomologyExact.Cycles.integralSingularHomology
        (TopCat.of (NormalSphere.Cycles.NormalUnitSphere (EuclideanSpace ℝ (Fin (2 * p))))) n :=
  NormalNormChange.Cycles.normalSphereHomologyChange (complexRealEuclideanEquiv p) n

@[simp]
theorem complexRealSphereHomologyIso_hom (p n : ℕ) :
    (complexRealSphereHomologyIso p n).hom =
      RelativeHomologyExact.Cycles.integralSingularHomologyMap
        (TopCat.ofHom (complexRealSphereHomotopyEquiv p).toFun) n := rfl

/-- The same coordinate change identifies the genuine local relative homology
groups, in every degree. -/
def complexRealLocalHomologyIso (p n : ℕ) :
    LocalHomology.Cycles.localSingularHomology (TopCat.of (Fin p → ℂ)) 0 n ≅
      LocalHomology.Cycles.localSingularHomology (TopCat.of (EuclideanSpace ℝ (Fin (2 * p)))) 0 n := by
  have hzero : (complexRealEuclideanEquiv p).toHomeomorph (0 : Fin p → ℂ) = 0 :=
    map_zero (complexRealEuclideanEquiv p)
  simpa only [hzero] using
    (LocalHomology.Cycles.localSingularHomologyIso
      (X := TopCat.of (Fin p → ℂ))
      (Y := TopCat.of (EuclideanSpace ℝ (Fin (2 * p))))
      (complexRealEuclideanEquiv p).toHomeomorph 0 n)

/-- In degrees at least two, the actual relative boundary and the explicit
coordinate/radial maps reduce complex local homology to a real unit sphere. -/
def complexNormalLocalRealSphereIso (p n : ℕ) (hn : n ≠ 0) :
    LocalHomology.Cycles.localSingularHomology (TopCat.of (Fin p → ℂ)) 0 (n + 1) ≅
      RelativeHomologyExact.Cycles.integralSingularHomology
        (TopCat.of (NormalSphere.Cycles.NormalUnitSphere (EuclideanSpace ℝ (Fin (2 * p))))) n :=
  LocalNormalHomology.Cycles.complexNormalLocalSphereIso p n hn ≪≫ complexRealSphereHomologyIso p n

/-- The local-to-real-sphere map is the genuine relative boundary, followed
by the radial projection and the explicit coordinate comparison. -/
@[simp]
theorem complexNormalLocalRealSphereIso_hom (p n : ℕ) (hn : n ≠ 0) :
    (complexNormalLocalRealSphereIso p n hn).hom =
      RelativeHomologyExact.Cycles.relativeHomologyBoundary (TopCat.of (Fin p → ℂ)) ({0}ᶜ : Set (Fin p → ℂ)) n ≫
        RelativeHomologyExact.Cycles.integralSingularHomologyMap
          (TopCat.ofHom (NormalSphere.Cycles.normalSphereProjection (Fin p → ℂ))) n ≫
        RelativeHomologyExact.Cycles.integralSingularHomologyMap
          (TopCat.ofHom (complexRealSphereHomotopyEquiv p).toFun) n := by
  simp only [complexNormalLocalRealSphereIso, Iso.trans_hom,
    LocalNormalHomology.Cycles.complexNormalLocalSphereIso_hom, complexRealSphereHomologyIso_hom, Category.assoc]

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.RealComplexNormalModel.Cycles
end ComponentSource_14

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.RealComplexNormalModel"

@[expose] public section ComponentSource_15
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.SphereCover -/

/-! # Sphere Cover -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.SphereCover.Cycles

noncomputable section

/-!
# Two stereographic open sets on a sphere

The complements of opposite poles form an actual open cover of the unit sphere.
Each complement is homeomorphic to a real vector space and hence contractible.
Their intersection is homeomorphic to a punctured hyperplane and is therefore
homotopy equivalent to a sphere in one lower ambient dimension.

No excision, Mayer--Vietoris theorem, or sphere-homology computation is assumed.
-/

open _root_.Metric _root_.Module _root_.Submodule
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E]

/-- The stereographic domain obtained by deleting a pole from the sphere. -/
def spherePoleOpen (v : NormalSphere.Cycles.NormalUnitSphere E) : Set (NormalSphere.Cycles.NormalUnitSphere E) := {v}ᶜ

@[simp]
theorem mem_spherePoleOpen (v x : NormalSphere.Cycles.NormalUnitSphere E) :
    x ∈ spherePoleOpen v ↔ x ≠ v := Iff.rfl

theorem isOpen_spherePoleOpen (v : NormalSphere.Cycles.NormalUnitSphere E) : IsOpen (spherePoleOpen v) :=
  isOpen_compl_singleton

variable [InnerProductSpace ℝ E]

/-- Opposite poles have disjoint omitted singleton sets. -/
theorem spherePoleOpen_union (v : NormalSphere.Cycles.NormalUnitSphere E) :
    spherePoleOpen v ∪ spherePoleOpen (-v) = Set.univ := by
  ext x
  simp only [Set.mem_union, mem_spherePoleOpen, Set.mem_univ, iff_true]
  by_cases h : x = v
  · exact Or.inr (h ▸ ne_neg_of_mem_unit_sphere ℝ v)
  · exact Or.inl h

/-- The hyperplane perpendicular to the chosen pole. -/
abbrev SphereEquatorSpace (v : NormalSphere.Cycles.NormalUnitSphere E) := (ℝ ∙ (v : E))ᗮ

/-- The actual stereographic homeomorphism on a pole complement. -/
def spherePoleChart (v : NormalSphere.Cycles.NormalUnitSphere E) :
    spherePoleOpen v ≃ₜ SphereEquatorSpace v :=
  (stereographic (norm_eq_of_mem_sphere v)).toHomeomorphSourceTarget.trans
    (Homeomorph.Set.univ _)

@[simp]
theorem spherePoleChart_apply (v : NormalSphere.Cycles.NormalUnitSphere E) (x : spherePoleOpen v) :
    spherePoleChart v x = stereographic (norm_eq_of_mem_sphere v) (x : NormalSphere.Cycles.NormalUnitSphere E) :=
  rfl

/-- Every pole complement is genuinely contractible. -/
theorem spherePoleOpen_contractible (v : NormalSphere.Cycles.NormalUnitSphere E) :
    ContractibleSpace (spherePoleOpen v) :=
  (spherePoleChart v).contractibleSpace

/-- The opposite pole, viewed as a point of the chosen stereographic chart. -/
def sphereOppositePole (v : NormalSphere.Cycles.NormalUnitSphere E) : spherePoleOpen v :=
  ⟨-v, (ne_neg_of_mem_unit_sphere ℝ v).symm⟩

@[simp]
theorem spherePoleChart_opposite (v : NormalSphere.Cycles.NormalUnitSphere E) :
    spherePoleChart v (sphereOppositePole v) = 0 := by
  exact stereographic_apply_neg v

/-- Deleting the opposite pole from this chart is exactly deleting zero from
the hyperplane. -/
theorem spherePoleChart_eq_zero_iff (v : NormalSphere.Cycles.NormalUnitSphere E) (x : spherePoleOpen v) :
    spherePoleChart v x = 0 ↔ (x : NormalSphere.Cycles.NormalUnitSphere E) = -v := by
  constructor
  · intro h
    have he : spherePoleChart v x = spherePoleChart v (sphereOppositePole v) := by
      rw [h, spherePoleChart_opposite]
    exact congrArg Subtype.val ((spherePoleChart v).injective he)
  · intro h
    have he : x = sphereOppositePole v := Subtype.ext h
    rw [he, spherePoleChart_opposite]

/-- Flatten the two membership conditions in the intersection of the charts. -/
def spherePoleIntersectionNested (v : NormalSphere.Cycles.NormalUnitSphere E) :
    ↥(spherePoleOpen v ∩ spherePoleOpen (-v)) ≃ₜ
      {x : spherePoleOpen v // (x : NormalSphere.Cycles.NormalUnitSphere E) ≠ -v} where
  toFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  invFun x := ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The overlap of the two stereographic domains is a punctured real
hyperplane, via the restricted stereographic homeomorphism. -/
def spherePoleIntersectionChart (v : NormalSphere.Cycles.NormalUnitSphere E) :
    ↥(spherePoleOpen v ∩ spherePoleOpen (-v)) ≃ₜ NormalSphere.Cycles.PuncturedNormal (SphereEquatorSpace v) :=
  (spherePoleIntersectionNested v).trans
    ((spherePoleChart v).subtype (fun x => by
      change (x : NormalSphere.Cycles.NormalUnitSphere E) ≠ -v ↔ spherePoleChart v x ≠ 0
      exact (not_congr (spherePoleChart_eq_zero_iff v x)).symm))

@[simp]
theorem spherePoleIntersectionChart_apply (v : NormalSphere.Cycles.NormalUnitSphere E)
    (x : ↥(spherePoleOpen v ∩ spherePoleOpen (-v))) :
    (spherePoleIntersectionChart v x : SphereEquatorSpace v) =
      stereographic (norm_eq_of_mem_sphere v) (x : NormalSphere.Cycles.NormalUnitSphere E) := rfl

/-- Radial normalization in stereographic coordinates identifies the overlap
up to homotopy with the unit sphere of the equatorial hyperplane. -/
def spherePoleIntersectionSphereEquiv (v : NormalSphere.Cycles.NormalUnitSphere E) :
    ContinuousMap.HomotopyEquiv ↥(spherePoleOpen v ∩ spherePoleOpen (-v))
      (NormalSphere.Cycles.NormalUnitSphere (SphereEquatorSpace v)) :=
  (spherePoleIntersectionChart v).toHomotopyEquiv.trans
    (NormalSphere.Cycles.normalSphereHomotopyEquiv (SphereEquatorSpace v))

/-- The equatorial hyperplane has one less real dimension. -/
theorem sphereEquatorSpace_finrank [FiniteDimensional ℝ E] (v : NormalSphere.Cycles.NormalUnitSphere E) :
    Module.finrank ℝ (SphereEquatorSpace v) + 1 = Module.finrank ℝ E := by
  have h := (ℝ ∙ (v : E)).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton (ne_zero_of_mem_unit_sphere v)] at h
  simpa [Nat.add_comm] using h

/-- In an `(n+1)`-dimensional inner product space, the equatorial sphere is
homeomorphic to the usual unit sphere in real Euclidean `n`-space. -/
def sphereEquatorEuclideanHomeomorph (n : ℕ) [Fact (Module.finrank ℝ E = n + 1)]
    (v : NormalSphere.Cycles.NormalUnitSphere E) :
    NormalSphere.Cycles.NormalUnitSphere (SphereEquatorSpace v) ≃ₜ
      NormalSphere.Cycles.NormalUnitSphere (EuclideanSpace ℝ (Fin n)) :=
  (OrthonormalBasis.fromOrthogonalSpanSingleton n (ne_zero_of_mem_unit_sphere v)).repr.toHomeomorph.subtype
    (fun x => by
      simp only [NormalSphere.Cycles.NormalUnitSphere, mem_sphere_zero_iff_norm]
      change ‖x‖ = 1 ↔
        ‖(OrthonormalBasis.fromOrthogonalSpanSingleton n (ne_zero_of_mem_unit_sphere v)).repr x‖ = 1
      rw [LinearIsometryEquiv.norm_map])

/-- The explicit lower-dimensional sphere equivalence used in dimension
induction for the two-chart cover. -/
def spherePoleIntersectionLowerSphereEquiv (n : ℕ) [Fact (Module.finrank ℝ E = n + 1)]
    (v : NormalSphere.Cycles.NormalUnitSphere E) :
    ContinuousMap.HomotopyEquiv ↥(spherePoleOpen v ∩ spherePoleOpen (-v))
      (NormalSphere.Cycles.NormalUnitSphere (EuclideanSpace ℝ (Fin n))) :=
  (spherePoleIntersectionSphereEquiv v).trans
    (sphereEquatorEuclideanHomeomorph n v).toHomotopyEquiv

/-- A concrete north pole for the standard sphere. -/
def standardSphereNorthPole (n : ℕ) : NormalSphere.Cycles.NormalUnitSphere (EuclideanSpace ℝ (Fin (n + 1))) :=
  ⟨EuclideanSpace.single 0 1, by simp [NormalSphere.Cycles.NormalUnitSphere]⟩

section OrderedEquatorCoordinates

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

abbrev StandardEquator (n : ℕ) := SphereEquatorSpace (standardSphereNorthPole n)

theorem standardEquator_first_zero (n : ℕ) (x : StandardEquator n) : x.val 0 = 0 := by
  have h := x.property
  rw [Submodule.mem_orthogonal_singleton_iff_inner_left] at h
  simpa [standardSphereNorthPole, EuclideanSpace.inner_single_right] using h

def orderedEquatorCoordinates (n : ℕ) : StandardEquator n ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun x := WithLp.toLp 2 (fun i => x.val i.succ)
  invFun y := ⟨WithLp.toLp 2 (Fin.cons 0 (fun i => y i)), by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    simp [standardSphereNorthPole, EuclideanSpace.inner_single_right]⟩
  left_inv x := by
    apply Subtype.ext
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (standardEquator_first_zero n x).symm
    · rfl
  right_inv y := by ext i; rfl
  map_add' x y := by ext i; rfl
  map_smul' r x := by ext i; rfl
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖WithLp.toLp 2 (fun i : Fin n => x.val i.succ)‖ ^ 2 = ‖x.val‖ ^ 2
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
    simp only [standardEquator_first_zero, zero_pow (by decide : 2 ≠ 0), zero_add]

def orderedEquatorBasis (n : ℕ) : OrthonormalBasis (Fin n) ℝ (StandardEquator n) :=
  OrthonormalBasis.ofRepr (orderedEquatorCoordinates n)

theorem orderedEquatorCoordinates_apply (n : ℕ) (x : StandardEquator n) (i : Fin n) :
    orderedEquatorCoordinates n x i = x.val i.succ := rfl

def orderedEquatorSphereHomeomorph (n : ℕ) :
    NormalSphere.Cycles.NormalUnitSphere (StandardEquator n) ≃ₜ NormalSphere.Cycles.NormalUnitSphere (EuclideanSpace ℝ (Fin n)) :=
  (orderedEquatorCoordinates n).toHomeomorph.subtype (fun x => by
    simp only [NormalSphere.Cycles.NormalUnitSphere, mem_sphere_zero_iff_norm]
    change ‖x‖ = 1 ↔ ‖orderedEquatorCoordinates n x‖ = 1
    rw [LinearIsometryEquiv.norm_map])

end OrderedEquatorCoordinates

/-- The two-chart intersection for the standard `n`-sphere has the homotopy
type of the unit sphere in real `n`-space. This also handles `n = 0`, when
both the intersection and that lower sphere are empty. -/
def standardSphereOverlapEquiv (n : ℕ) :
    ContinuousMap.HomotopyEquiv
      ↥(spherePoleOpen (standardSphereNorthPole n) ∩
        spherePoleOpen (-standardSphereNorthPole n))
      (NormalSphere.Cycles.NormalUnitSphere (EuclideanSpace ℝ (Fin n))) :=
  (spherePoleIntersectionSphereEquiv (standardSphereNorthPole n)).trans
    (orderedEquatorSphereHomeomorph n).toHomotopyEquiv

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.SphereCover.Cycles
end ComponentSource_15

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.SphereCover"

@[expose] public section ComponentSource_16
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.SmallSphereHomology -/

/-! # Small Sphere Homology -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.SmallSphereHomology.Cycles

noncomputable section

/-!
# Higher homology of the two-chart small chains of a sphere

The actual Mayer–Vietoris connecting map is an isomorphism in degrees at
least two when the two pieces are contractible. For the complements of
opposite sphere poles, the overlap is homotopy equivalent to a sphere in
one lower ambient dimension. The resulting shift is proved here for the
small singular chain complex itself.

The inclusion of small chains into all singular chains is not assumed to
be a quasi-isomorphism. These results alone do not compute the homology of
all singular chains of a sphere or select an orientation generator.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

/-- Vanishing of both summands implies vanishing of the actual middle
homology object in the small-chain Mayer–Vietoris sequence. -/
theorem smallMayerVietorisMiddleHomology_isZero (X : TopCat.{0})
    (U V : Set X) (n : ℕ)
    (hU : IsZero (RelativeHomologyExact.Cycles.integralSingularHomology (TopCat.of U) n))
    (hV : IsZero (RelativeHomologyExact.Cycles.integralSingularHomology (TopCat.of V) n)) :
    IsZero ((SmallMayerVietoris.Cycles.smallMayerVietorisSequence X U V).X₂.homology n) :=
  ((biprod_isZero_iff _ _).mpr ⟨hU, hV⟩).of_iso
    (SmallMayerVietoris.Cycles.smallMayerVietorisMiddleHomologyIso X U V n)

/-- The actual connecting morphism is an isomorphism when the two
neighboring homology groups of both pieces vanish. -/
def smallMayerVietorisBoundaryIso (X : TopCat.{0}) (U V : Set X) (n : ℕ)
    (hUi : IsZero (RelativeHomologyExact.Cycles.integralSingularHomology (TopCat.of U) (n + 1)))
    (hVi : IsZero (RelativeHomologyExact.Cycles.integralSingularHomology (TopCat.of V) (n + 1)))
    (hUj : IsZero (RelativeHomologyExact.Cycles.integralSingularHomology (TopCat.of U) n))
    (hVj : IsZero (RelativeHomologyExact.Cycles.integralSingularHomology (TopCat.of V) n)) :
    SmallMayerVietoris.Cycles.binarySmallSingularHomology X U V (n + 1) ≅
      RelativeHomologyExact.Cycles.integralSingularHomology (TopCat.of (U ∩ V : Set X)) n :=
  (SmallMayerVietoris.Cycles.smallMayerVietorisSequence_shortExact X U V).δIso (n + 1) n rfl
    (smallMayerVietorisMiddleHomology_isZero X U V (n + 1) hUi hVi)
    (smallMayerVietorisMiddleHomology_isZero X U V n hUj hVj)

@[simp]
theorem smallMayerVietorisBoundaryIso_hom (X : TopCat.{0}) (U V : Set X) (n : ℕ)
    (hUi : IsZero (RelativeHomologyExact.Cycles.integralSingularHomology (TopCat.of U) (n + 1)))
    (hVi : IsZero (RelativeHomologyExact.Cycles.integralSingularHomology (TopCat.of V) (n + 1)))
    (hUj : IsZero (RelativeHomologyExact.Cycles.integralSingularHomology (TopCat.of U) n))
    (hVj : IsZero (RelativeHomologyExact.Cycles.integralSingularHomology (TopCat.of V) n)) :
    (smallMayerVietorisBoundaryIso X U V n hUi hVi hUj hVj).hom =
      SmallMayerVietoris.Cycles.smallMayerVietorisBoundary X U V n := rfl

/-- For two contractible pieces, the small-chain connecting map is an
isomorphism from degree `n+2` to intersection homology in degree `n+1`. -/
def contractibleSmallMayerVietorisBoundaryIso (X : TopCat.{0}) (U V : Set X)
    [ContractibleSpace U] [ContractibleSpace V] (n : ℕ) :
    SmallMayerVietoris.Cycles.binarySmallSingularHomology X U V (n + 2) ≅
      RelativeHomologyExact.Cycles.integralSingularHomology (TopCat.of (U ∩ V : Set X)) (n + 1) :=
  smallMayerVietorisBoundaryIso X U V (n + 1)
    (ContractibleModel.Cycles.isZero_integralSingularHomology_of_contractible _ (n + 2) (by omega))
    (ContractibleModel.Cycles.isZero_integralSingularHomology_of_contractible _ (n + 2) (by omega))
    (ContractibleModel.Cycles.isZero_integralSingularHomology_of_contractible _ (n + 1) (Nat.succ_ne_zero n))
    (ContractibleModel.Cycles.isZero_integralSingularHomology_of_contractible _ (n + 1) (Nat.succ_ne_zero n))

@[simp]
theorem contractibleSmallMayerVietorisBoundaryIso_hom (X : TopCat.{0}) (U V : Set X)
    [ContractibleSpace U] [ContractibleSpace V] (n : ℕ) :
    (contractibleSmallMayerVietorisBoundaryIso X U V n).hom =
      SmallMayerVietoris.Cycles.smallMayerVietorisBoundary X U V (n + 1) := rfl

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual singular chains on a sphere that lie in one of the two
complements of the specified opposite poles. -/
abbrev spherePoleSmallChains (v : NormalSphere.Cycles.NormalUnitSphere E) :
    ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  SmallMayerVietoris.Cycles.binarySmallSingularChains (TopCat.of (NormalSphere.Cycles.NormalUnitSphere E))
    (SphereCover.Cycles.spherePoleOpen v) (SphereCover.Cycles.spherePoleOpen (-v))

/-- The homology of the actual two-chart small chain complex. -/
abbrev spherePoleSmallHomology (v : NormalSphere.Cycles.NormalUnitSphere E) (n : ℕ) :
    ModuleCat.{0} ℤ := (spherePoleSmallChains v).homology n

/-- The small-sphere boundary is an isomorphism to the actual homology of
the intersection of the two stereographic domains. -/
def spherePoleSmallBoundaryIso (v : NormalSphere.Cycles.NormalUnitSphere E) (n : ℕ) :
    spherePoleSmallHomology v (n + 2) ≅
      RelativeHomologyExact.Cycles.integralSingularHomology
        (TopCat.of ↥(SphereCover.Cycles.spherePoleOpen v ∩ SphereCover.Cycles.spherePoleOpen (-v))) (n + 1) := by
  letI := SphereCover.Cycles.spherePoleOpen_contractible v
  letI := SphereCover.Cycles.spherePoleOpen_contractible (-v)
  exact contractibleSmallMayerVietorisBoundaryIso _ _ _ n

@[simp]
theorem spherePoleSmallBoundaryIso_hom (v : NormalSphere.Cycles.NormalUnitSphere E) (n : ℕ) :
    (spherePoleSmallBoundaryIso v n).hom =
      SmallMayerVietoris.Cycles.smallMayerVietorisBoundary (TopCat.of (NormalSphere.Cycles.NormalUnitSphere E))
        (SphereCover.Cycles.spherePoleOpen v) (SphereCover.Cycles.spherePoleOpen (-v)) (n + 1) := rfl

/-- The higher small-chain homology of a sphere shifts to the actual
singular homology of its equatorial sphere. -/
def spherePoleSmallHomologyShift (v : NormalSphere.Cycles.NormalUnitSphere E) (n : ℕ) :
    spherePoleSmallHomology v (n + 2) ≅
      RelativeHomologyExact.Cycles.integralSingularHomology
        (TopCat.of (NormalSphere.Cycles.NormalUnitSphere (SphereCover.Cycles.SphereEquatorSpace v))) (n + 1) :=
  spherePoleSmallBoundaryIso v n ≪≫
    ContractibleModel.Cycles.singularHomologyIsoOfHomotopyEquiv (ModuleCat.of ℤ ℤ)
      (X := TopCat.of ↥(SphereCover.Cycles.spherePoleOpen v ∩ SphereCover.Cycles.spherePoleOpen (-v)))
      (Y := TopCat.of (NormalSphere.Cycles.NormalUnitSphere (SphereCover.Cycles.SphereEquatorSpace v)))
      (SphereCover.Cycles.spherePoleIntersectionSphereEquiv v) (n + 1)

/-- The shift is specifically the connecting morphism followed by the
map from the established stereographic and radial homotopy equivalence. -/
theorem spherePoleSmallHomologyShift_hom (v : NormalSphere.Cycles.NormalUnitSphere E) (n : ℕ) :
    (spherePoleSmallHomologyShift v n).hom =
      SmallMayerVietoris.Cycles.smallMayerVietorisBoundary (TopCat.of (NormalSphere.Cycles.NormalUnitSphere E))
        (SphereCover.Cycles.spherePoleOpen v) (SphereCover.Cycles.spherePoleOpen (-v)) (n + 1) ≫
      RelativeHomologyExact.Cycles.integralSingularHomologyMap
        (TopCat.ofHom (SphereCover.Cycles.spherePoleIntersectionSphereEquiv v).toFun) (n + 1) := rfl

/-- For the standard `d`-sphere and the specified opposite-pole cover,
the actual small-chain homology in degree `n+2` is isomorphic to the
homology in degree `n+1` of the unit sphere in `ℝ^d`. -/
def standardSphereSmallHomologyShift (d n : ℕ) :
    spherePoleSmallHomology (SphereCover.Cycles.standardSphereNorthPole d) (n + 2) ≅
      RelativeHomologyExact.Cycles.integralSingularHomology
        (TopCat.of (NormalSphere.Cycles.NormalUnitSphere (EuclideanSpace ℝ (Fin d)))) (n + 1) :=
  spherePoleSmallBoundaryIso (SphereCover.Cycles.standardSphereNorthPole d) n ≪≫
    ContractibleModel.Cycles.singularHomologyIsoOfHomotopyEquiv (ModuleCat.of ℤ ℤ)
      (X := TopCat.of ↥(SphereCover.Cycles.spherePoleOpen (SphereCover.Cycles.standardSphereNorthPole d) ∩
        SphereCover.Cycles.spherePoleOpen (-SphereCover.Cycles.standardSphereNorthPole d)))
      (Y := TopCat.of (NormalSphere.Cycles.NormalUnitSphere (EuclideanSpace ℝ (Fin d))))
      (SphereCover.Cycles.standardSphereOverlapEquiv d) (n + 1)

@[simp]
theorem standardSphereSmallHomologyShift_hom (d n : ℕ) :
    (standardSphereSmallHomologyShift d n).hom =
      SmallMayerVietoris.Cycles.smallMayerVietorisBoundary
        (TopCat.of (NormalSphere.Cycles.NormalUnitSphere (EuclideanSpace ℝ (Fin (d + 1)))))
        (SphereCover.Cycles.spherePoleOpen (SphereCover.Cycles.standardSphereNorthPole d))
        (SphereCover.Cycles.spherePoleOpen (-SphereCover.Cycles.standardSphereNorthPole d)) (n + 1) ≫
      RelativeHomologyExact.Cycles.integralSingularHomologyMap
        (TopCat.ofHom (SphereCover.Cycles.standardSphereOverlapEquiv d).toFun) (n + 1) := rfl

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.SmallSphereHomology.Cycles
end ComponentSource_16

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.SmallSphereHomology"

@[expose] public section ComponentSource_17
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.Point -/

/-! # Point -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.Point.Cycles

noncomputable section

/-!+# The integral local class of a point

This file proves the dimension-zero normalization using actual relative singular
chains. It identifies the relative chain complex of `(X, ∅)` with the absolute
one, then uses the canonical zeroth-homology augmentation. Its distinguished
point class is the inverse image of `1: ℤ`, not an assumed fundamental class.
No positive-dimensional orientation or fundamental-class theorem is asserted.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology

/-- An empty topological space has zero integral singular chain complex. -/
theorem integralSingularChains_isZero_of_isEmpty (X : TopCat.{0}) [IsEmpty X] :
    IsZero (LocalHomology.Cycles.integralSingularChains X) := by
  have hs : IsZero (∐ fun _ : X ↦ ModuleCat.of ℤ ℤ) := by
    rw [IsZero.iff_id_eq_zero]
    apply Sigma.hom_ext
    intro x
    exact isEmptyElim x
  have hc : IsZero (ChainComplex.alternatingConst.obj (∐ fun _ : X ↦ ModuleCat.of ℤ ℤ)) := by
    rw [IsZero.iff_id_eq_zero]
    apply HomologicalComplex.hom_ext
    intro n
    exact hs.eq_zero_of_src _
  exact hc.of_iso
    (singularChainComplexFunctorIsoOfTotallyDisconnectedSpace
      (ModuleCat.{0} ℤ) (ModuleCat.of ℤ ℤ) X)

/-- The singular-chain inclusion from the empty subspace is the zero chain map. -/
theorem subspaceChainInclusion_empty (X : TopCat.{0}) :
    LocalHomology.Cycles.subspaceChainInclusion X ∅ = 0 :=
  (integralSingularChains_isZero_of_isEmpty (TopCat.of (∅ : Set X))).eq_zero_of_src _

/-- Quotienting integral singular chains by the chains of the empty subspace
does not change the chain complex. -/
def relativeEmptyChainsIso (X : TopCat.{0}) :
    LocalHomology.Cycles.relativeSingularChains X ∅ ≅ LocalHomology.Cycles.integralSingularChains X := by
  letI : IsIso (LocalHomology.Cycles.relativeChainProjection X ∅) :=
    cokernel.π_of_zero (subspaceChainInclusion_empty X)
  exact (asIso (LocalHomology.Cycles.relativeChainProjection X ∅)).symm

/-- Relative homology for the empty subspace is ordinary integral singular homology. -/
def relativeEmptyHomologyIso (X : TopCat.{0}) (n : ℕ) :
    LocalHomology.Cycles.relativeSingularHomology X ∅ n ≅ (LocalHomology.Cycles.integralSingularChains X).homology n :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n).mapIso
    (relativeEmptyChainsIso X)

/-- On a path-connected space, the genuine relative group `H₀(X, ∅; ℤ)` is
identified with `ℤ` by the canonical augmentation. -/
def relativeEmptyHomologyZeroIso (X : TopCat.{0}) [PathConnectedSpace X] :
    LocalHomology.Cycles.relativeSingularHomology X ∅ 0 ≅ ModuleCat.of ℤ ℤ :=
  relativeEmptyHomologyIso X 0 ≪≫ ContractibleModel.Cycles.integralSingularH0Iso X

/-- The one-point topological model of a complex manifold of dimension zero. -/
abbrev pointModel : TopCat.{0} := TopCat.of PUnit

instance pointModel_pathConnectedSpace : PathConnectedSpace pointModel where
  nonempty := ⟨PUnit.unit⟩
  joined x y := by
    have h : x = y := Subsingleton.elim _ _
    subst y
    exact ⟨Path.refl x⟩

/-- The complement of the point in the one-point model is empty. -/
theorem pointModel_punctured_eq_empty :
    ({PUnit.unit}ᶜ : Set pointModel) = ∅ := by
  ext x
  simp

/-- The actual degree-zero local singular homology group of a point is `ℤ`. -/
def pointLocalHomologyZeroIso :
    LocalHomology.Cycles.localSingularHomology pointModel PUnit.unit 0 ≅ ModuleCat.of ℤ ℤ := by
  unfold LocalHomology.Cycles.localSingularHomology
  rw [pointModel_punctured_eq_empty]
  exact relativeEmptyHomologyZeroIso pointModel

/-- The positively normalized integral local class of the point. -/
def pointLocalClass : LocalHomology.Cycles.localSingularHomology pointModel PUnit.unit 0 :=
  pointLocalHomologyZeroIso.inv (1 : ℤ)

/-- The point class has augmentation exactly one. -/
@[simp]
theorem pointLocalClass_normalization :
    pointLocalHomologyZeroIso.hom pointLocalClass = 1 := by
  change (pointLocalHomologyZeroIso.inv ≫ pointLocalHomologyZeroIso.hom) (1 : ℤ) = 1
  simp

/-- The local class of the point is nonzero. -/
theorem pointLocalClass_ne_zero : pointLocalClass ≠ 0 := by
  intro h
  have hn := pointLocalClass_normalization
  rw [h, map_zero] at hn
  exact zero_ne_one hn

/-- Every integral local class of a point is a unique integer multiple of its
positively normalized generator. -/
theorem pointLocalClass_generates
    (x : LocalHomology.Cycles.localSingularHomology pointModel PUnit.unit 0) :
    ∃! n : ℤ, n • pointLocalClass = x := by
  have hnorm (n : ℤ) : pointLocalHomologyZeroIso.hom (n • pointLocalClass) = n := by
    calc
      pointLocalHomologyZeroIso.hom (n • pointLocalClass) =
          n • (pointLocalHomologyZeroIso.hom pointLocalClass) :=
        map_zsmul pointLocalHomologyZeroIso.hom.hom _ _
      _ = n := by rw [pointLocalClass_normalization]; simp
  refine ⟨pointLocalHomologyZeroIso.hom x, ?_, ?_⟩
  · apply (ConcreteCategory.bijective_of_isIso pointLocalHomologyZeroIso.hom).1
    exact hnorm _
  · intro n hn
    calc
      n = pointLocalHomologyZeroIso.hom (n • pointLocalClass) := (hnorm n).symm
      _ = pointLocalHomologyZeroIso.hom x := congrArg pointLocalHomologyZeroIso.hom hn

/-- The genuine complex coordinate model in dimension zero is the point model. -/
def complexZeroModelHomeomorphPoint : (Fin 0 → ℂ) ≃ₜ pointModel where
  toFun _ := PUnit.unit
  invFun _ := 0
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
  continuous_toFun := continuous_const
  continuous_invFun := continuous_const

/-- The actual local homology normalization of the zero-dimensional complex
coordinate model, transported by its canonical homeomorphism with a point. -/
def complexZeroLocalHomologyIso :
    LocalHomology.Cycles.localSingularHomology (TopCat.of (Fin 0 → ℂ)) 0 0 ≅ ModuleCat.of ℤ ℤ :=
  LocalHomology.Cycles.localSingularHomologyIso (X := TopCat.of (Fin 0 → ℂ)) (Y := pointModel)
    complexZeroModelHomeomorphPoint 0 0 ≪≫ pointLocalHomologyZeroIso

/-- The positively normalized local class in complex dimension zero. -/
def complexZeroLocalClass : LocalHomology.Cycles.localSingularHomology (TopCat.of (Fin 0 → ℂ)) 0 0 :=
  complexZeroLocalHomologyIso.inv (1 : ℤ)

@[simp]
theorem complexZeroLocalClass_normalization :
    complexZeroLocalHomologyIso.hom complexZeroLocalClass = 1 := by
  change (complexZeroLocalHomologyIso.inv ≫ complexZeroLocalHomologyIso.hom) (1 : ℤ) = 1
  simp

theorem complexZeroLocalClass_ne_zero : complexZeroLocalClass ≠ 0 := by
  intro h
  have hn := complexZeroLocalClass_normalization
  rw [h, map_zero] at hn
  exact zero_ne_one hn

/-- The zero-dimensional complex local homology group is freely generated
by its positively normalized class. -/
theorem complexZeroLocalClass_generates
    (x : LocalHomology.Cycles.localSingularHomology (TopCat.of (Fin 0 → ℂ)) 0 0) :
    ∃! n : ℤ, n • complexZeroLocalClass = x := by
  have hnorm (n : ℤ) : complexZeroLocalHomologyIso.hom (n • complexZeroLocalClass) = n := by
    calc
      complexZeroLocalHomologyIso.hom (n • complexZeroLocalClass) =
          n • (complexZeroLocalHomologyIso.hom complexZeroLocalClass) :=
        map_zsmul complexZeroLocalHomologyIso.hom.hom _ _
      _ = n := by rw [complexZeroLocalClass_normalization]; simp
  refine ⟨complexZeroLocalHomologyIso.hom x, ?_, ?_⟩
  · apply (ConcreteCategory.bijective_of_isIso complexZeroLocalHomologyIso.hom).1
    exact hnorm _
  · intro n hn
    calc
      n = complexZeroLocalHomologyIso.hom (n • complexZeroLocalClass) := (hnorm n).symm
      _ = complexZeroLocalHomologyIso.hom x := congrArg complexZeroLocalHomologyIso.hom hn

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.Point.Cycles
end ComponentSource_17

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.Point"


set_option pp.explicit false
set_option pp.proofs false
set_option pp.deepTerms false
set_option maxHeartbeats 0

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let opts ← getOptions
  if true && env.header.trustLevel != 0 then
    throwError "The final environment has nonzero kernel trust level"
  if Lean.debug.skipKernelTC.get opts then
    throwError "The final environment disabled kernel type checking"
  if Lean.Elab.inServer.get opts then
    throwError "The final environment unexpectedly uses server mode"
  let required : Array (Name × String) := #[
    (`OAI.AlgebraicGeometry.CycleClass.Geometric.Point.Cycles.complexZeroLocalClass_generates, "theorem")
  ]
  let localNames := env.checked.get.constants.foldStage2 (fun acc name _ => acc.push name) (#[] : Array Name)
  if localNames.isEmpty then throwError "Empty authored declaration audit"
  let mut names := localNames
  for (name, _) in required do
    unless names.contains name do names := names.push name
  let mut rows : Array Json := #[]
  for name in names do
    let some info := env.checked.get.find? name | throwError "Missing checked declaration {name}"
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .quotInfo _ => "quotient primitive"
    if kind == "axiom" then throwError "Authored axiom {name}"
    let value := info.value? (allowOpaque := true)
    if kind == "theorem" || kind == "definition" || kind == "opaque" then
      unless value.isSome do throwError "No actual body {name}"
    for (requiredName, expectedKind) in required do
      if name == requiredName && kind != expectedKind then
        throwError "Endpoint kind mismatch {name}: expected {expectedKind}, got {kind}"
    let axioms ← collectAxioms name
    for ax in axioms do
      if ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound then
        throwError "Unapproved transitive axiom {name}: {ax}"
    let mut fields := [("name", toJson name.toString), ("kind", toJson kind),
      ("actual_body_available", toJson value.isSome),
      ("universe_parameters", toJson (info.levelParams.map Name.toString)),
      ("type_dependencies", toJson (info.type.getUsedConstants.map Name.toString)),
      ("body_dependencies", toJson ((value.map Expr.getUsedConstants).getD #[] |>.map Name.toString)),
      ("transitive_axioms", toJson (axioms.map Name.toString))]
    if required.any (fun e => e.1 == name) then
      let typeText ← liftTermElabM <| return (← Meta.ppExpr info.type).pretty
      fields := fields ++ [("readable_type", toJson typeText)]
    rows := rows.push (Json.mkObj fields)
  IO.FS.createDirAll ".lake/reports"
  let path := ".lake/reports/" ++ (← getEnv).mainModule.toString ++ ".json"
  IO.FS.writeFile path (Json.mkObj [("accepted", toJson true),
    ("nonce", toJson "8a9af8a86955627184aa2cc0adcee040"), ("declaration_count", toJson localNames.size),
    ("kernel_trust_level", toJson env.header.trustLevel.toNat),
    ("kernel_type_checking_enabled", toJson (!Lean.debug.skipKernelTC.get opts)),
    ("server_mode", toJson (Lean.Elab.inServer.get opts)),
    ("required_endpoint_count", toJson required.size),
    ("all_new_declarations_read_from_checked_environment", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo "LITERAL_COMPONENT_KERNEL_AUDIT_COMPLETE:8a9af8a86955627184aa2cc0adcee040"
