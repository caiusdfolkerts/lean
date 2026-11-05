module

public import paper_verification.oai_thom000_run1
import all paper_verification.oai_thom000_run1
public import Mathlib.AlgebraicTopology.TopologicalSimplex
import all Mathlib.AlgebraicTopology.TopologicalSimplex
public import Mathlib.AlgebraicTopology.SingularSet
import all Mathlib.AlgebraicTopology.SingularSet
public import Mathlib.Order.Interval.Finset.Fin
import all Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Analysis.SpecificLimits.Basic
import all Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import all Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Tactic.Ring
import all Mathlib.Tactic.Ring
public import Mathlib.GroupTheory.Perm.Sign
import all Mathlib.GroupTheory.Perm.Sign
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import all Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
import all Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.Algebra.Category.ModuleCat.Colimits
import all Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.LinearAlgebra.Span.Basic
import all Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
import all Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.Homotopy
import all Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
import all Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Module.Submodule.Equiv
import all Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import all Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.GroupTheory.Perm.Fin
import all Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Algebra.Ring.Commute
import all Mathlib.Algebra.Ring.Commute
public import Lean.Elab.Tactic.Omega
import all Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.PrettyPrinter

set_option Elab.async false

@[expose] public section ComponentSource_0
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.BarycentricSimplex -/

/-! # Barycentric Simplex -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.BarycentricSimplex.Cycles

noncomputable section

/-!
# Actual barycentric subdivision maps of topological simplices

A nonempty face has its genuine arithmetic-mean barycenter. A nested flag of
faces gives a continuous simplex map by affine interpolation of those
barycenters. Full flags associated with vertex permutations give the usual
geometric cells of barycentric subdivision.

This module constructs the geometric maps only; no boundary identity,
subdivision chain homotopy, or excision theorem is assumed.
-/

open scoped BigOperators Classical OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The arithmetic-mean point of a nonempty face of the standard simplex. -/
def faceBarycenter (s : Finset ι) (hs : s.Nonempty) : Convexity.StdSimplex ℝ ι := by
  classical
  refine Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex.ofCoordinates (fun i => if i ∈ s then (s.card : ℝ)⁻¹ else 0) ?_ ?_
  · intro i
    split_ifs <;> positivity
  · have hcard : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hs.card_pos)
    simp [hcard]

@[simp]
theorem faceBarycenter_apply (s : Finset ι) (hs : s.Nonempty) (i : ι) :
    faceBarycenter s hs i = if i ∈ s then (s.card : ℝ)⁻¹ else 0 := by
  classical
  rfl

/-- The explicit coordinates agree with mathlib's affine centroid. -/
theorem faceBarycenter_eq_centroid [DecidableEq ι] (s : Finset ι) (hs : s.Nonempty) :
    (faceBarycenter s hs : ι → ℝ) = s.centroid ℝ (fun i => Pi.single i (1 : ℝ)) := by
  rw [BarycentricMesh.centroid_eq_inv_card_sum s hs]
  funext i
  rw [faceBarycenter_apply]
  simp [Finset.sum_apply, Pi.single_apply]

/-- Affine interpolation in barycentric coordinates extends to an actual
linear map on the ambient coordinate spaces. -/
def simplexVertexLinearMap (v : κ → Convexity.StdSimplex ℝ ι) : (κ → ℝ) →ₗ[ℝ] (ι → ℝ) :=
  ∑ k, (LinearMap.proj (R := ℝ) k).smulRight (v k : ι → ℝ)

omit [Fintype ι] in
@[simp]
theorem simplexVertexLinearMap_apply (v : κ → Convexity.StdSimplex ℝ ι)
    (x : κ → ℝ) (i : ι) :
    simplexVertexLinearMap v x i = ∑ k, x k * v k i := by
  simp [simplexVertexLinearMap]

omit [Fintype ι] in
/-- The ambient extension is the explicit weighted sum of its vertices. -/
theorem simplexVertexLinearMap_eq_sum (v : κ → Convexity.StdSimplex ℝ ι) (x : κ → ℝ) :
    simplexVertexLinearMap v x = ∑ k, x k • (v k : ι → ℝ) := by
  funext i
  simp [simplexVertexLinearMap_apply, Finset.sum_apply]

/-- The ambient extension is, in particular, an affine map. -/
def simplexVertexAffineMap (v : κ → Convexity.StdSimplex ℝ ι) : (κ → ℝ) →ᵃ[ℝ] (ι → ℝ) :=
  (simplexVertexLinearMap v).toAffineMap

/-- Barycentric interpolation is simplex-valued. -/
theorem simplexVertexLinearMap_mem (v : κ → Convexity.StdSimplex ℝ ι)
    (x : Convexity.StdSimplex ℝ κ) :
    (∀ i, 0 ≤ simplexVertexLinearMap v x i) ∧ ∑ i, simplexVertexLinearMap v x i = 1 := by
  constructor
  · intro i
    rw [simplexVertexLinearMap_apply]
    exact Finset.sum_nonneg fun k _ =>
      mul_nonneg (Convexity.StdSimplex.weights_nonneg (w := x) k) (Convexity.StdSimplex.weights_nonneg (w := v k) i)
  · simp only [simplexVertexLinearMap_apply]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, Convexity.StdSimplex.total_of_fintype, mul_one]

omit [Fintype ι] in
/-- The interpolation map is continuous in the ordinary simplex topology. -/
theorem continuous_simplexVertexLinearMap (v : κ → Convexity.StdSimplex ℝ ι) :
    Continuous (simplexVertexLinearMap v) := by
  apply continuous_pi
  intro i
  simp only [simplexVertexLinearMap_apply]
  fun_prop

/-- The genuine continuous map of simplices specified by its vertex images. -/
def simplexVertexMap (v : κ → Convexity.StdSimplex ℝ ι) : C(Convexity.StdSimplex ℝ κ, Convexity.StdSimplex ℝ ι) where
  toFun x := Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex.ofCoordinates (simplexVertexLinearMap v x)
    (simplexVertexLinearMap_mem v x).1 (simplexVertexLinearMap_mem v x).2
  continuous_toFun := by
    apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ ι).continuous_iff.mpr
    simpa [Function.comp_def, Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex.ofCoordinates] using
      (continuous_simplexVertexLinearMap v).comp
        (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ κ).continuous

@[simp]
theorem simplexVertexMap_apply (v : κ → Convexity.StdSimplex ℝ ι)
    (x : Convexity.StdSimplex ℝ κ) (i : ι) :
    simplexVertexMap v x i = ∑ k, x k * v k i := by
  simp [simplexVertexMap, Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex.ofCoordinates, simplexVertexLinearMap_apply]

/-- The constructed continuous map is the restriction of the displayed
ambient affine map, not an abstract map with assumed affine properties. -/
theorem simplexVertexMap_eq_affine (v : κ → Convexity.StdSimplex ℝ ι)
    (x : Convexity.StdSimplex ℝ κ) :
    (simplexVertexMap v x : ι → ℝ) = simplexVertexAffineMap v x := by
  funext i
  simp [simplexVertexMap, Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex.ofCoordinates,
    simplexVertexAffineMap]

@[simp]
theorem simplexVertexMap_vertex [DecidableEq κ] (v : κ → Convexity.StdSimplex ℝ ι) (k : κ) :
    simplexVertexMap v (Convexity.StdSimplex.single k) = v k := by
  apply Convexity.StdSimplex.ext
  ext i
  simp [simplexVertexMap_apply, Convexity.StdSimplex.single, Finsupp.single_apply]

/-- Every interpolated point lies in the actual convex hull of the vertex images. -/
theorem simplexVertexMap_mem_convexHull (v : κ → Convexity.StdSimplex ℝ ι)
    (x : Convexity.StdSimplex ℝ κ) :
    (simplexVertexMap v x : ι → ℝ) ∈
      convexHull ℝ (Set.range fun k => (v k : ι → ℝ)) := by
  change simplexVertexLinearMap v x ∈ _
  rw [simplexVertexLinearMap_eq_sum]
  exact (convex_convexHull ℝ _).sum_mem
    (fun k _ => Convexity.StdSimplex.weights_nonneg (w := x) k) (Convexity.StdSimplex.total_of_fintype x)
    (fun k _ => subset_convexHull ℝ _ (Set.mem_range_self k))

/-- Ordered nested nonempty faces, allowing repeated faces for degenerate cells. -/
structure BarycentricFlag (ι : Type*) (m : ℕ) where
  face : Fin (m + 1) → Finset ι
  nonempty : ∀ j, (face j).Nonempty
  monotone : Monotone face

namespace BarycentricFlag

variable {m : ℕ}

/-- The actual geometric simplex corresponding to a face flag. -/
def toContinuousMap (F : BarycentricFlag ι m) :
    C(Convexity.StdSimplex ℝ (Fin (m + 1)), Convexity.StdSimplex ℝ ι) :=
  simplexVertexMap (fun j => faceBarycenter (F.face j) (F.nonempty j))

@[simp]
theorem toContinuousMap_vertex (F : BarycentricFlag ι m) (j : Fin (m + 1)) :
    F.toContinuousMap (Convexity.StdSimplex.single j) = faceBarycenter (F.face j) (F.nonempty j) :=
  simplexVertexMap_vertex _ _

@[simp]
theorem toContinuousMap_apply (F : BarycentricFlag ι m)
    (x : Convexity.StdSimplex ℝ (Fin (m + 1))) (i : ι) :
    F.toContinuousMap x i =
      ∑ j, x j * (if i ∈ F.face j then ((F.face j).card : ℝ)⁻¹ else 0) := by
  classical
  simp [BarycentricFlag.toContinuousMap]

/-- The geometric flag simplex lies in the convex hull of its genuine centroids. -/
theorem toContinuousMap_mem_convexHull [DecidableEq ι] (F : BarycentricFlag ι m)
    (x : Convexity.StdSimplex ℝ (Fin (m + 1))) :
    (F.toContinuousMap x : ι → ℝ) ∈ convexHull ℝ
      (Set.range fun j => (F.face j).centroid ℝ (fun i => Pi.single i (1 : ℝ))) := by
  have h := simplexVertexMap_mem_convexHull
    (fun j => faceBarycenter (F.face j) (F.nonempty j)) x
  simpa only [BarycentricFlag.toContinuousMap, faceBarycenter_eq_centroid] using h

/-- A flag cell in the standard `n`-simplex has mesh at most `n/(n+1)`.
The bound follows from the proved face-centroid estimate, not an axiom about subdivision. -/
theorem toContinuousMap_dist_le {n : ℕ} (F : BarycentricFlag (Fin (n + 1)) m)
    (x y : Convexity.StdSimplex ℝ (Fin (m + 1))) :
    dist (F.toContinuousMap x) (F.toContinuousMap y) ≤ (n : ℝ) / (n + 1) := by
  have hchain (j k : Fin (m + 1)) : F.face j ⊆ F.face k ∨ F.face k ⊆ F.face j := by
    rcases le_total j k with h | h
    · exact Or.inl (F.monotone h)
    · exact Or.inr (F.monotone h)
  have hD (i j : Fin (n + 1)) :
      dist (Pi.single i (1 : ℝ) : Fin (n + 1) → ℝ)
        (Pi.single j (1 : ℝ) : Fin (n + 1) → ℝ) ≤ 1 :=
    by
      apply (dist_pi_le_iff (by norm_num : (0 : ℝ) ≤ 1)).2
      intro k
      by_cases hi : i = k <;> by_cases hj : j = k <;>
        simp [hi, hj, Real.dist_eq]
  have h := BarycentricMesh.dist_convexHull_centroids_le_dimension_factor
    (fun i : Fin (n + 1) => Pi.single i (1 : ℝ)) F.face F.nonempty hchain 1 hD
    (F.toContinuousMap_mem_convexHull x) (F.toContinuousMap_mem_convexHull y)
  change dist (F.toContinuousMap x : Fin (n + 1) → ℝ)
    (F.toContinuousMap y : Fin (n + 1) → ℝ) ≤ _
  simpa only [mul_one] using h

end BarycentricFlag

/-- The full nested flag obtained by successively inserting permuted vertices. -/
def permutationBarycentricFlag {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    BarycentricFlag (Fin (n + 1)) n where
  face j := (Finset.Iic j).map σ.toEmbedding
  nonempty j := ⟨σ j, Finset.mem_map.mpr ⟨j, Finset.mem_Iic.mpr le_rfl, rfl⟩⟩
  monotone := by
    intro j k hjk a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp ha
    exact Finset.mem_map.mpr ⟨b, Finset.mem_Iic.mpr ((Finset.mem_Iic.mp hb).trans hjk), rfl⟩

@[simp]
theorem permutationBarycentricFlag_card {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (j : Fin (n + 1)) : ((permutationBarycentricFlag σ).face j).card = j.val + 1 := by
  simp [permutationBarycentricFlag]

/-- A standard barycentric subdivision cell, as an actual continuous self-map
of the topological standard simplex. -/
def barycentricSubdivisionMap {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    C(Convexity.StdSimplex ℝ (Fin (n + 1)), Convexity.StdSimplex ℝ (Fin (n + 1))) :=
  (permutationBarycentricFlag σ).toContinuousMap

/-- The vertices of the cell are the successive genuine face barycenters. -/
@[simp]
theorem barycentricSubdivisionMap_vertex {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (j : Fin (n + 1)) :
    barycentricSubdivisionMap σ (Convexity.StdSimplex.single j) =
      faceBarycenter ((Finset.Iic j).map σ.toEmbedding)
        ⟨σ j, Finset.mem_map.mpr ⟨j, Finset.mem_Iic.mpr le_rfl, rfl⟩⟩ :=
  (permutationBarycentricFlag σ).toContinuousMap_vertex j

/-- The one-step mesh estimate for every actual subdivision cell. -/
theorem barycentricSubdivisionMap_dist_le {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (x y : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    dist (barycentricSubdivisionMap σ x) (barycentricSubdivisionMap σ y) ≤
      (n : ℝ) / (n + 1) :=
  (permutationBarycentricFlag σ).toContinuousMap_dist_le x y

/-- Subdivision of an individual genuine continuous singular simplex. -/
def subdividedSingularSimplex {X : Type*} [TopologicalSpace X] {n : ℕ}
    (f : C(Convexity.StdSimplex ℝ (Fin (n + 1)), X)) (σ : Equiv.Perm (Fin (n + 1))) :
    C(Convexity.StdSimplex ℝ (Fin (n + 1)), X) :=
  f.comp (barycentricSubdivisionMap σ)

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.BarycentricSimplex.Cycles
end ComponentSource_0

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.BarycentricSimplex"

@[expose] public section ComponentSource_1
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.SmallSimplex -/

/-! # Small Simplex -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.SmallSimplex.Cycles

noncomputable section

/-!
# The geometric smallness step for singular excision

Pulling an open cover back along an actual singular simplex gives a Lebesgue
number on its compact standard-simplex domain. Consequently all sufficiently
small continuous subsimplices are subordinate to the cover. A single scale,
and then a single geometric-shrinking exponent, works for any finite family
of singular simplices.

This file does not assume or construct a subdivision chain operator. Its final
theorem supplies the geometric conclusion once a concrete subsimplex map has
the stated diameter bound. Constructing the barycentric chain operator and its
chain homotopy remains a separate obligation.
-/

open _root_.CategoryTheory
open scoped Simplicial

variable {X : TopCat.{0}} {ι : Type} (U : ι → Set X)
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i)

include hopen hcover

/-- Every singular simplex has a positive scale at which balls in its domain
map into single cover members. This is the actual pulled-back-cover Lebesgue
number, not an assumption on a prospective chain map. -/
theorem singularSimplex_lebesgueNumber {n : ℕ}
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), X)) :
    ∃ ε > 0, ∀ x : Convexity.StdSimplex ℝ (Fin (n + 1)),
      ∃ i, Metric.ball x ε ⊆ σ ⁻¹' U i := by
  have hpull : ∀ i, IsOpen (σ ⁻¹' U i) :=
    fun i ↦ (hopen i).preimage σ.continuous
  have hpullcover : (Set.univ : Set (Convexity.StdSimplex ℝ (Fin (n + 1)))) ⊆
      ⋃ i, σ ⁻¹' U i := by
    intro x _
    obtain ⟨i, hi⟩ := hcover (σ x)
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨ε, hε, hsmall⟩ :=
    lebesgue_number_lemma_of_metric isCompact_univ hpull hpullcover
  exact ⟨ε, hε, fun x ↦ hsmall x (Set.mem_univ x)⟩

/-- Small diameter of an actual continuous subsimplex implies that its
composition with the original singular simplex lies in one cover member. -/
theorem singularSimplex_small_subsimplices {n : ℕ}
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), X)) :
    ∃ ε > 0, ∀ (m : ℕ) (τ : C(Convexity.StdSimplex ℝ (Fin (m + 1)),
      Convexity.StdSimplex ℝ (Fin (n + 1)))),
      (∀ a b, dist (τ a) (τ b) < ε) →
      ∃ i, Set.range (σ.comp τ) ⊆ U i := by
  obtain ⟨ε, hε, hball⟩ := singularSimplex_lebesgueNumber U hopen hcover σ
  refine ⟨ε, hε, ?_⟩
  intro m τ hτ
  let a : Convexity.StdSimplex ℝ (Fin (m + 1)) := Convexity.StdSimplex.single 0
  obtain ⟨i, hi⟩ := hball (τ a)
  refine ⟨i, ?_⟩
  rintro _ ⟨b, rfl⟩
  exact hi (hτ b a)

/-- A finite family of genuine singular simplices admits one common
smallness scale. This is the finite-support step needed for singular chains. -/
theorem singularSimplices_uniform_smallness {n : ℕ}
    (s : Finset C(Convexity.StdSimplex ℝ (Fin (n + 1)), X)) :
    ∃ ε > 0, ∀ σ ∈ s, ∀ (m : ℕ)
      (τ : C(Convexity.StdSimplex ℝ (Fin (m + 1)), Convexity.StdSimplex ℝ (Fin (n + 1)))),
      (∀ a b, dist (τ a) (τ b) < ε) →
      ∃ i, Set.range (σ.comp τ) ⊆ U i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨1, zero_lt_one, ?_⟩
      intro σ hσ
      exact (Finset.notMem_empty σ hσ).elim
  | @insert σ s _ ih =>
      obtain ⟨δ, hδ, hσ⟩ := singularSimplex_small_subsimplices U hopen hcover σ
      obtain ⟨ε, hε, hs⟩ := ih
      refine ⟨min δ ε, lt_min hδ hε, ?_⟩
      intro ψ hψ m τ hτ
      rcases Finset.mem_insert.mp hψ with rfl | hψ
      · exact hσ m τ (fun a b ↦ (hτ a b).trans_le (min_le_left δ ε))
      · exact hs ψ hψ m τ (fun a b ↦ (hτ a b).trans_le (min_le_right δ ε))

/-- Geometric mesh contraction eventually makes every subsimplex in a finite
family subordinate to an open cover. The diameter hypothesis is explicit;
no subdivision identity or mesh estimate is smuggled in as structure data. -/
theorem singularSimplices_geometric_smallness {n : ℕ}
    (s : Finset C(Convexity.StdSimplex ℝ (Fin (n + 1)), X))
    {r : ℝ} (hr : r < 1) :
    ∃ N : ℕ, ∀ σ ∈ s, ∀ (m : ℕ)
      (τ : C(Convexity.StdSimplex ℝ (Fin (m + 1)), Convexity.StdSimplex ℝ (Fin (n + 1)))),
      (∀ a b, dist (τ a) (τ b) ≤ r ^ N) →
      ∃ i, Set.range (σ.comp τ) ⊆ U i := by
  obtain ⟨ε, hε, hsmall⟩ := singularSimplices_uniform_smallness U hopen hcover s
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε hr
  refine ⟨N, ?_⟩
  intro σ hσ m τ hτ
  exact hsmall σ hσ m τ (fun a b ↦ (hτ a b).trans_lt hN)

omit hopen hcover in
/-- The geometric containment result packages into the actual small singular
simplex type used by the cover Čech resolution. -/
def smallSingularSimplexOfRange {n : ℕ}
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), X))
    (hσ : ∃ i, Set.range σ ⊆ U i) :
    AlgebraicTopology.DeRham.Comparison.CechCoverRows.SmallSingularSimplex X U n :=
  ⟨(X.toSSetObjEquiv (.op ⦋n⦌)).symm σ, by
    simpa only [Equiv.apply_symm_apply] using hσ⟩

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.SmallSimplex.Cycles
end ComponentSource_1

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.SmallSimplex"

@[expose] public section ComponentSource_2
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.SingularChainSupport -/

/-! # Singular Chain Support -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.SingularChainSupport.Cycles

noncomputable section

/-!
# Finite support of genuine integral singular chains

The degreewise coproduct in mathlib's singular chain complex is canonically
identified with finitely supported integer functions on the actual continuous
singular simplices. The finite-family Lebesgue argument then applies to every
element of the genuine chain complex.
-/

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped Simplicial

/-- The canonical finite-support description of genuine singular chains. -/
def singularChainDegreeFinsuppIso (X : TopCat.{0}) (n : ℕ) :
    (LocalHomology.Cycles.integralSingularChains X).X n ≅
      ModuleCat.of ℤ (((TopCat.toSSet.obj X).obj (.op ⦋n⦌)) →₀ ℤ) :=
  ((TopCat.toSSet.obj X).isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n).coconePointUniqueUpToIso
      (ModuleCat.finsuppCoconeIsColimit ℤ ℤ ((TopCat.toSSet.obj X).obj (.op ⦋n⦌)))

/-- Coefficients of a genuine singular chain in its simplex basis. -/
def singularChainCoefficients (X : TopCat.{0}) (n : ℕ) :
    (LocalHomology.Cycles.integralSingularChains X).X n ≃ₗ[ℤ]
      (((TopCat.toSSet.obj X).obj (.op ⦋n⦌)) →₀ ℤ) :=
  (singularChainDegreeFinsuppIso X n).toLinearEquiv

/-- The coefficient description sends the actual simplex summand to the
corresponding finitely supported singleton. -/
@[reassoc (attr := simp)]
theorem singularChainCoefficients_simplex (X : TopCat.{0}) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (.op ⦋n⦌)) :
    (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ ≫
      (singularChainDegreeFinsuppIso X n).hom =
        ModuleCat.ofHom (Finsupp.lsingle σ (R := ℤ) (M := ModuleCat.of ℤ ℤ)) :=
  ((TopCat.toSSet.obj X).isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n).comp_coconePointUniqueUpToIso_hom
      (ModuleCat.finsuppCoconeIsColimit ℤ ℤ ((TopCat.toSSet.obj X).obj (.op ⦋n⦌)))
      (Discrete.mk σ)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Elementwise form of the canonical simplex coefficient formula. -/
@[simp]
theorem singularChainCoefficients_simplex_apply (X : TopCat.{0}) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (.op ⦋n⦌)) (a : ℤ) :
    singularChainCoefficients X n
      ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ a) =
        Finsupp.single σ a := by
  change (singularChainDegreeFinsuppIso X n).hom.hom
    (((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom a) = _
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_ofHom, Finsupp.lsingle_apply] using!
      congrArg (fun f : ModuleCat.of ℤ ℤ ⟶
        ModuleCat.of ℤ (((TopCat.toSSet.obj X).obj (.op ⦋n⦌)) →₀ ℤ) ↦ f.hom a)
        (singularChainCoefficients_simplex X n σ)

/-- The finite set of simplices occurring with nonzero coefficient. -/
def singularChainSupport {X : TopCat.{0}} {n : ℕ}
    (c : (LocalHomology.Cycles.integralSingularChains X).X n) :
    Finset ((TopCat.toSSet.obj X).obj (.op ⦋n⦌)) :=
  (singularChainCoefficients X n c).support

@[simp]
theorem singularChainCoefficients_eq_zero_iff {X : TopCat.{0}} {n : ℕ}
    (c : (LocalHomology.Cycles.integralSingularChains X).X n) :
    singularChainCoefficients X n c = 0 ↔ c = 0 :=
  (singularChainCoefficients X n).map_eq_zero_iff

/-- One geometric refinement exponent works simultaneously on every simplex
in an actual chain. The input maps are real continuous subsimplices, and their
mesh estimate remains an explicit hypothesis to be proved by subdivision. -/
theorem singularChain_geometric_smallness {X : TopCat.{0}} {ι : Type}
    (U : ι → Set X) (hopen : ∀ i, IsOpen (U i))
    (hcover : ∀ x : X, ∃ i, x ∈ U i) {n : ℕ}
    (c : (LocalHomology.Cycles.integralSingularChains X).X n) {r : ℝ} (hr : r < 1) :
    ∃ N : ℕ, ∀ σ ∈ singularChainSupport c, ∀ (m : ℕ)
      (τ : C(Convexity.StdSimplex ℝ (Fin (m + 1)), Convexity.StdSimplex ℝ (Fin (n + 1)))),
      (∀ a b, dist (τ a) (τ b) ≤ r ^ N) →
      ∃ i, Set.range ((X.toSSetObjEquiv (.op ⦋n⦌) σ).comp τ) ⊆ U i := by
  classical
  let s := (singularChainSupport c).image (X.toSSetObjEquiv (.op ⦋n⦌))
  obtain ⟨N, hN⟩ := SmallSimplex.Cycles.singularSimplices_geometric_smallness U hopen hcover s hr
  refine ⟨N, ?_⟩
  intro σ hσ m τ hτ
  exact hN _ (Finset.mem_image.mpr ⟨σ, hσ, rfl⟩) m τ hτ

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.SingularChainSupport.Cycles
end ComponentSource_2

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.SingularChainSupport"

@[expose] public section ComponentSource_3
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.IteratedSubdivision -/

/-! # Iterated Subdivision -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.IteratedSubdivision.Cycles

noncomputable section

/-!
# Iterated actual barycentric maps and geometric smallness

We iterate the constructed barycentric affine maps themselves. The mesh estimate
comes from the centroids of the current vertices; it does not assume that a
single barycentric map has an unproved Lipschitz constant. Finite support and a
Lebesgue number then make every iterated cell of an actual integral chain small.
-/

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

open _root_.CategoryTheory
open scoped BigOperators Simplicial

variable {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]

/-- Barycentric affine interpolation respects actual composition. -/
theorem simplexVertexMap_comp (v : κ → Convexity.StdSimplex ℝ ι)
    (w : μ → Convexity.StdSimplex ℝ κ) :
    (BarycentricSimplex.Cycles.simplexVertexMap v).comp (BarycentricSimplex.Cycles.simplexVertexMap w) =
      BarycentricSimplex.Cycles.simplexVertexMap (fun j => BarycentricSimplex.Cycles.simplexVertexMap v (w j)) := by
  ext x i
  simp only [ContinuousMap.comp_apply, BarycentricSimplex.Cycles.simplexVertexMap_apply,
    Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/-- Interpolation of the original vertices is the identity simplex map. -/
theorem simplexVertexMap_vertices [DecidableEq ι] :
    BarycentricSimplex.Cycles.simplexVertexMap (fun i : ι => Convexity.StdSimplex.single i) =
      ContinuousMap.id (Convexity.StdSimplex ℝ ι) := by
  ext x i
  simp [BarycentricSimplex.Cycles.simplexVertexMap_apply, Convexity.StdSimplex.single, Finsupp.single_apply]

/-- An affine barycentric map sends the barycenter of a face to the actual
arithmetic centroid of its vertex images. -/
theorem simplexVertexMap_faceBarycenter (v : κ → Convexity.StdSimplex ℝ ι)
    (s : Finset κ) (hs : s.Nonempty) :
    (BarycentricSimplex.Cycles.simplexVertexMap v (BarycentricSimplex.Cycles.faceBarycenter s hs) : ι → ℝ) =
      s.centroid ℝ (fun j => (v j : ι → ℝ)) := by
  classical
  rw [BarycentricMesh.centroid_eq_inv_card_sum s hs]
  funext i
  simp [BarycentricSimplex.Cycles.simplexVertexMap_apply, BarycentricSimplex.Cycles.faceBarycenter_apply,
    Finset.sum_apply, Finset.mul_sum, ite_mul]

/-- The mesh factor for an `n`-dimensional simplex. -/
abbrev barycentricMeshFactor (n : ℕ) : ℝ := (n : ℝ) / (n + 1)

theorem barycentricMeshFactor_nonneg (n : ℕ) : 0 ≤ barycentricMeshFactor n := by
  positivity

theorem barycentricMeshFactor_lt_one (n : ℕ) : barycentricMeshFactor n < 1 := by
  apply (div_lt_one (by positivity : (0 : ℝ) < n + 1)).2
  linarith

/-- The actual new vertices obtained by applying one barycentric cell to a
simplex with the specified old vertices. -/
def subdivideSimplexVertices {n : ℕ} (v : Fin (n + 1) → Convexity.StdSimplex ℝ ι)
    (σ : Equiv.Perm (Fin (n + 1))) : Fin (n + 1) → Convexity.StdSimplex ℝ ι :=
  fun j => BarycentricSimplex.Cycles.simplexVertexMap v
    (BarycentricSimplex.Cycles.faceBarycenter ((BarycentricSimplex.Cycles.permutationBarycentricFlag σ).face j)
      ((BarycentricSimplex.Cycles.permutationBarycentricFlag σ).nonempty j))

/-- This vertex construction is exactly precomposition by the existing
barycentric subdivision map. -/
theorem simplexVertexMap_subdivide {n : ℕ}
    (v : Fin (n + 1) → Convexity.StdSimplex ℝ ι) (σ : Equiv.Perm (Fin (n + 1))) :
    BarycentricSimplex.Cycles.simplexVertexMap (subdivideSimplexVertices v σ) =
      (BarycentricSimplex.Cycles.simplexVertexMap v).comp (BarycentricSimplex.Cycles.barycentricSubdivisionMap σ) := by
  symm
  exact simplexVertexMap_comp v _

/-- One genuine subdivision contracts the current vertex diameter bound. -/
theorem subdivideSimplexVertices_dist_le {n : ℕ}
    (v : Fin (n + 1) → Convexity.StdSimplex ℝ ι) (σ : Equiv.Perm (Fin (n + 1)))
    (D : ℝ) (hD : ∀ i j, dist (v i) (v j) ≤ D) (i j : Fin (n + 1)) :
    dist (subdivideSimplexVertices v σ i) (subdivideSimplexVertices v σ j) ≤
      barycentricMeshFactor n * D := by
  have hchain : (BarycentricSimplex.Cycles.permutationBarycentricFlag σ).face i ⊆
      (BarycentricSimplex.Cycles.permutationBarycentricFlag σ).face j ∨
      (BarycentricSimplex.Cycles.permutationBarycentricFlag σ).face j ⊆ (BarycentricSimplex.Cycles.permutationBarycentricFlag σ).face i := by
    rcases le_total i j with hij | hji
    · exact Or.inl ((BarycentricSimplex.Cycles.permutationBarycentricFlag σ).monotone hij)
    · exact Or.inr ((BarycentricSimplex.Cycles.permutationBarycentricFlag σ).monotone hji)
  have h := BarycentricMesh.dist_centroid_le_dimension_factor
    (fun k => (v k : ι → ℝ)) _ _
    ((BarycentricSimplex.Cycles.permutationBarycentricFlag σ).nonempty i)
    ((BarycentricSimplex.Cycles.permutationBarycentricFlag σ).nonempty j) hchain D hD
  rw [← simplexVertexMap_faceBarycenter v _ ((BarycentricSimplex.Cycles.permutationBarycentricFlag σ).nonempty i),
    ← simplexVertexMap_faceBarycenter v _ ((BarycentricSimplex.Cycles.permutationBarycentricFlag σ).nonempty j)] at h
  simpa only [subdivideSimplexVertices, Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex.dist_eq_weights] using h

/-- Successive actual barycentric vertex constructions; the head permutation
is the newest precomposition. -/
def iteratedSimplexVertices {n : ℕ} (v : Fin (n + 1) → Convexity.StdSimplex ℝ ι)
    (l : List (Equiv.Perm (Fin (n + 1)))) : Fin (n + 1) → Convexity.StdSimplex ℝ ι :=
  l.foldr (fun σ w => subdivideSimplexVertices w σ) v

/-- The actual affine map of an iterated subdivision cell. -/
def iteratedSimplexMap {n : ℕ} (v : Fin (n + 1) → Convexity.StdSimplex ℝ ι)
    (l : List (Equiv.Perm (Fin (n + 1)))) :
    C(Convexity.StdSimplex ℝ (Fin (n + 1)), Convexity.StdSimplex ℝ ι) :=
  BarycentricSimplex.Cycles.simplexVertexMap (iteratedSimplexVertices v l)

@[simp]
theorem iteratedSimplexMap_nil {n : ℕ} (v : Fin (n + 1) → Convexity.StdSimplex ℝ ι) :
    iteratedSimplexMap v [] = BarycentricSimplex.Cycles.simplexVertexMap v := rfl

@[simp]
theorem iteratedSimplexMap_cons {n : ℕ} (v : Fin (n + 1) → Convexity.StdSimplex ℝ ι)
    (σ : Equiv.Perm (Fin (n + 1))) (l : List (Equiv.Perm (Fin (n + 1)))) :
    iteratedSimplexMap v (σ :: l) =
      (iteratedSimplexMap v l).comp (BarycentricSimplex.Cycles.barycentricSubdivisionMap σ) :=
  simplexVertexMap_subdivide _ _

/-- The iterated vertex estimate, with the actual initial diameter bound. -/
theorem iteratedSimplexVertices_dist_le {n : ℕ}
    (v : Fin (n + 1) → Convexity.StdSimplex ℝ ι) (D : ℝ)
    (hD : ∀ i j, dist (v i) (v j) ≤ D)
    (l : List (Equiv.Perm (Fin (n + 1)))) (i j : Fin (n + 1)) :
    dist (iteratedSimplexVertices v l i) (iteratedSimplexVertices v l j) ≤
      barycentricMeshFactor n ^ l.length * D := by
  induction l generalizing i j with
  | nil => simpa [iteratedSimplexVertices] using hD i j
  | cons σ l ih =>
      have hprev (a b : Fin (n + 1)) := ih a b
      calc
        dist (iteratedSimplexVertices v (σ :: l) i)
            (iteratedSimplexVertices v (σ :: l) j) ≤
            barycentricMeshFactor n * (barycentricMeshFactor n ^ l.length * D) :=
          subdivideSimplexVertices_dist_le _ σ _ hprev i j
        _ = barycentricMeshFactor n ^ (σ :: l).length * D := by
          simp only [List.length_cons, pow_succ]
          ring

/-- The mesh estimate holds for all points in the actual iterated cell. -/
theorem iteratedSimplexMap_dist_le {n : ℕ}
    (v : Fin (n + 1) → Convexity.StdSimplex ℝ ι) (D : ℝ)
    (hD : ∀ i j, dist (v i) (v j) ≤ D)
    (l : List (Equiv.Perm (Fin (n + 1))))
    (x y : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    dist (iteratedSimplexMap v l x) (iteratedSimplexMap v l y) ≤
      barycentricMeshFactor n ^ l.length * D := by
  have hx := BarycentricSimplex.Cycles.simplexVertexMap_mem_convexHull (iteratedSimplexVertices v l) x
  have hy := BarycentricSimplex.Cycles.simplexVertexMap_mem_convexHull (iteratedSimplexVertices v l) y
  obtain ⟨x', ⟨i, rfl⟩, y', ⟨j, rfl⟩, hxy⟩ := convexHull_exists_dist_ge2 hx hy
  exact hxy.trans (iteratedSimplexVertices_dist_le v D hD l i j)

/-- Actual diameter contraction of the image, relative to the initial vertices. -/
theorem iteratedSimplexMap_diam_le {n : ℕ}
    (v : Fin (n + 1) → Convexity.StdSimplex ℝ ι)
    (l : List (Equiv.Perm (Fin (n + 1)))) :
    Metric.diam (Set.range (iteratedSimplexMap v l)) ≤
      barycentricMeshFactor n ^ l.length * Metric.diam (Set.range v) := by
  apply Metric.diam_le_of_forall_dist_le (mul_nonneg
    (pow_nonneg (barycentricMeshFactor_nonneg n) _) Metric.diam_nonneg)
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  exact iteratedSimplexMap_dist_le v _
    (fun i j => Metric.dist_le_diam_of_mem (Set.finite_range v).isBounded
      (Set.mem_range_self i) (Set.mem_range_self j)) l x y

/-- The same contraction bound relative to the diameter of the entire initial
affine simplex, rather than only its vertex set. -/
theorem iteratedSimplexMap_diam_le_initial {n : ℕ}
    (v : Fin (n + 1) → Convexity.StdSimplex ℝ ι)
    (l : List (Equiv.Perm (Fin (n + 1)))) :
    Metric.diam (Set.range (iteratedSimplexMap v l)) ≤
      barycentricMeshFactor n ^ l.length * Metric.diam (Set.range (BarycentricSimplex.Cycles.simplexVertexMap v)) := by
  have hsub : Set.range v ⊆ Set.range (BarycentricSimplex.Cycles.simplexVertexMap v) := by
    rintro _ ⟨i, rfl⟩
    exact ⟨Convexity.StdSimplex.single i, BarycentricSimplex.Cycles.simplexVertexMap_vertex v i⟩
  have hbdd := (isCompact_range (BarycentricSimplex.Cycles.simplexVertexMap v).continuous).isBounded
  exact (iteratedSimplexMap_diam_le v l).trans (mul_le_mul_of_nonneg_left
    (Metric.diam_mono hsub hbdd) (pow_nonneg (barycentricMeshFactor_nonneg n) _))

/-- Iteration starting with the standard simplex itself. -/
def iteratedSubdivisionMap {n : ℕ} (l : List (Equiv.Perm (Fin (n + 1)))) :
    C(Convexity.StdSimplex ℝ (Fin (n + 1)), Convexity.StdSimplex ℝ (Fin (n + 1))) :=
  iteratedSimplexMap (fun i => Convexity.StdSimplex.single i) l

@[simp]
theorem iteratedSubdivisionMap_nil {n : ℕ} :
    iteratedSubdivisionMap (n := n) [] = ContinuousMap.id _ :=
  simplexVertexMap_vertices

@[simp]
theorem iteratedSubdivisionMap_cons {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (l : List (Equiv.Perm (Fin (n + 1)))) :
    iteratedSubdivisionMap (σ :: l) =
      (iteratedSubdivisionMap l).comp (BarycentricSimplex.Cycles.barycentricSubdivisionMap σ) :=
  iteratedSimplexMap_cons _ _ _

/-- The uniform mesh bound for every genuine iterated standard cell. -/
theorem iteratedSubdivisionMap_dist_le {n : ℕ}
    (l : List (Equiv.Perm (Fin (n + 1))))
    (x y : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    dist (iteratedSubdivisionMap l x) (iteratedSubdivisionMap l y) ≤
      barycentricMeshFactor n ^ l.length := by
  have hD (i j : Fin (n + 1)) :
      dist (Convexity.StdSimplex.single i : Convexity.StdSimplex ℝ (Fin (n + 1)))
        (Convexity.StdSimplex.single j) ≤ 1 :=
    (Metric.dist_le_diam_of_mem
      (Convexity.StdSimplex.isBounded_range_toFun_comp_weights (Fin (n + 1)))
      ⟨Convexity.StdSimplex.single i, rfl⟩ ⟨Convexity.StdSimplex.single j, rfl⟩).trans
        (Convexity.StdSimplex.diam_range_toFun_comp_weights_subset_closedBall (Fin (n + 1)))
  simpa only [mul_one, iteratedSubdivisionMap] using iteratedSimplexMap_dist_le
    (fun i => Convexity.StdSimplex.single i) 1 hD l x y

/-- A common number of actual barycentric iterations makes every cell of every
simplex in a finite family subordinate to the given open cover. -/
theorem singularSimplices_iteratedSubdivision_small {X : TopCat.{0}} {J : Type}
    (U : J → Set X) (hopen : ∀ i, IsOpen (U i))
    (hcover : ∀ x : X, ∃ i, x ∈ U i) {n : ℕ}
    (s : Finset C(Convexity.StdSimplex ℝ (Fin (n + 1)), X)) :
    ∃ N : ℕ, ∀ σ ∈ s, ∀ l : List (Equiv.Perm (Fin (n + 1))),
      l.length = N → ∃ i, Set.range (σ.comp (iteratedSubdivisionMap l)) ⊆ U i := by
  obtain ⟨N, hN⟩ := SmallSimplex.Cycles.singularSimplices_geometric_smallness U hopen hcover s
    (barycentricMeshFactor_lt_one n)
  refine ⟨N, ?_⟩
  intro σ hσ l hl
  apply hN σ hσ n (iteratedSubdivisionMap l)
  intro x y
  simpa only [hl] using iteratedSubdivisionMap_dist_le l x y

/-- In particular, one common number of iterations works on the actual finite
support of every genuine integral singular chain. No mesh assumption remains. -/
theorem singularChain_iteratedSubdivision_small {X : TopCat.{0}} {J : Type}
    (U : J → Set X) (hopen : ∀ i, IsOpen (U i))
    (hcover : ∀ x : X, ∃ i, x ∈ U i) {n : ℕ}
    (c : (LocalHomology.Cycles.integralSingularChains X).X n) :
    ∃ N : ℕ, ∀ σ ∈ SingularChainSupport.Cycles.singularChainSupport c,
      ∀ l : List (Equiv.Perm (Fin (n + 1))), l.length = N →
      ∃ i, Set.range ((X.toSSetObjEquiv (.op ⦋n⦌) σ).comp
        (iteratedSubdivisionMap l)) ⊆ U i := by
  obtain ⟨N, hN⟩ := SingularChainSupport.Cycles.singularChain_geometric_smallness U hopen hcover c
    (barycentricMeshFactor_lt_one n)
  refine ⟨N, ?_⟩
  intro σ hσ l hl
  apply hN σ hσ n (iteratedSubdivisionMap l)
  intro x y
  simpa only [hl] using iteratedSubdivisionMap_dist_le l x y

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.IteratedSubdivision.Cycles
end ComponentSource_3

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.IteratedSubdivision"

@[expose] public section ComponentSource_4
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.SubdivisionOperator -/

/-! # Subdivision Operator -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.SubdivisionOperator.Cycles

noncomputable section

/-!
# The actual degreewise barycentric subdivision operator

Each genuine continuous singular simplex is replaced by the signed sum of its
permutation-indexed barycentric subsimplices. The finite-support model extends
this assignment linearly and the proved chain-coordinate equivalence transports
it to mathlib's integral singular chains.

This is only a degreewise linear operator. No commutation with the differential
or subdivision chain homotopy is asserted here.
-/

open _root_.CategoryTheory
open scoped Simplicial BigOperators Classical

/-- The actual index set in degree `n` of integral singular chains. -/
abbrev SingularSimplex (X : TopCat.{0}) (n : ℕ) :=
  (TopCat.toSSet.obj X).obj (.op ⦋n⦌)

/-- A genuine singular simplex precomposed with one barycentric cell map. -/
def subdivisionSimplex (X : TopCat.{0}) (n : ℕ) (s : SingularSimplex X n)
    (σ : Equiv.Perm (Fin (n + 1))) : SingularSimplex X n :=
  (X.toSSetObjEquiv (.op ⦋n⦌)).symm
    ((X.toSSetObjEquiv (.op ⦋n⦌) s).comp (BarycentricSimplex.Cycles.barycentricSubdivisionMap σ))

/-- Geometrically the constructed simplex is exactly the indicated precomposition. -/
@[simp]
theorem subdivisionSimplex_toContinuousMap (X : TopCat.{0}) (n : ℕ)
    (s : SingularSimplex X n) (σ : Equiv.Perm (Fin (n + 1))) :
    X.toSSetObjEquiv (.op ⦋n⦌) (subdivisionSimplex X n s σ) =
      (X.toSSetObjEquiv (.op ⦋n⦌) s).comp (BarycentricSimplex.Cycles.barycentricSubdivisionMap σ) :=
  (X.toSSetObjEquiv (.op ⦋n⦌)).apply_symm_apply _

/-- Subdivision never enlarges the geometric range of a simplex. -/
theorem range_subdivisionSimplex_subset (X : TopCat.{0}) (n : ℕ)
    (s : SingularSimplex X n) (σ : Equiv.Perm (Fin (n + 1))) :
    Set.range (X.toSSetObjEquiv (.op ⦋n⦌) (subdivisionSimplex X n s σ)) ⊆
      Set.range (X.toSSetObjEquiv (.op ⦋n⦌) s) := by
  rw [subdivisionSimplex_toContinuousMap]
  rintro x ⟨t, rfl⟩
  exact ⟨BarycentricSimplex.Cycles.barycentricSubdivisionMap σ t, rfl⟩

/-- The signed barycentric chain associated to one actual singular simplex. -/
def subdivisionGenerator (X : TopCat.{0}) (n : ℕ) (s : SingularSimplex X n) :
    SingularSimplex X n →₀ ℤ :=
  ∑ σ : Equiv.Perm (Fin (n + 1)),
    Finsupp.single (subdivisionSimplex X n s σ) (Equiv.Perm.sign σ : ℤ)

/-- The signed finite sum extended linearly on genuine simplex coefficients. -/
def subdivisionFinsupp (X : TopCat.{0}) (n : ℕ) :
    (SingularSimplex X n →₀ ℤ) →ₗ[ℤ] (SingularSimplex X n →₀ ℤ) :=
  Finsupp.linearCombination ℤ (subdivisionGenerator X n)

/-- The operator is the displayed finite linear combination. -/
theorem subdivisionFinsupp_apply (X : TopCat.{0}) (n : ℕ)
    (c : SingularSimplex X n →₀ ℤ) :
    subdivisionFinsupp X n c =
      ∑ s ∈ c.support, c s • subdivisionGenerator X n s := rfl

/-- Formula on a generator with an arbitrary integer coefficient. -/
@[simp]
theorem subdivisionFinsupp_single (X : TopCat.{0}) (n : ℕ)
    (s : SingularSimplex X n) (a : ℤ) :
    subdivisionFinsupp X n (Finsupp.single s a) =
      ∑ σ : Equiv.Perm (Fin (n + 1)),
        Finsupp.single (subdivisionSimplex X n s σ) ((Equiv.Perm.sign σ : ℤ) * a) := by
  simp [subdivisionFinsupp, subdivisionGenerator, Finset.smul_sum, Finsupp.smul_single,
    mul_comm]

/-- Every nonzero generator term comes from an actual barycentric cell. -/
theorem mem_support_subdivisionGenerator (X : TopCat.{0}) (n : ℕ)
    (s t : SingularSimplex X n) (ht : t ∈ (subdivisionGenerator X n s).support) :
    ∃ σ : Equiv.Perm (Fin (n + 1)), subdivisionSimplex X n s σ = t := by
  obtain ⟨σ, _, hσ⟩ := Finsupp.mem_support_finsetSum t ht
  have hsingle : t ∈ ({subdivisionSimplex X n s σ} : Finset (SingularSimplex X n)) :=
    Finsupp.support_single_subset hσ
  exact ⟨σ, (Finset.mem_singleton.mp hsingle).symm⟩

/-- Every simplex with nonzero subdivided coefficient refines a simplex from
exactly the original finite support; cancellation can only remove terms. -/
theorem mem_support_subdivisionFinsupp (X : TopCat.{0}) (n : ℕ)
    (c : SingularSimplex X n →₀ ℤ) (t : SingularSimplex X n)
    (ht : t ∈ (subdivisionFinsupp X n c).support) :
    ∃ s ∈ c.support, ∃ σ : Equiv.Perm (Fin (n + 1)), subdivisionSimplex X n s σ = t := by
  rw [subdivisionFinsupp_apply] at ht
  obtain ⟨s, hs, hts⟩ := Finsupp.mem_support_finsetSum t ht
  have hgen : t ∈ (subdivisionGenerator X n s).support := Finsupp.support_smul hts
  obtain ⟨σ, hσ⟩ := mem_support_subdivisionGenerator X n s t hgen
  exact ⟨s, hs, σ, hσ⟩

/-- A finite geometric bound on the support, independent of cancellations. -/
theorem support_subdivisionFinsupp_subset (X : TopCat.{0}) (n : ℕ)
    (c : SingularSimplex X n →₀ ℤ) :
    (subdivisionFinsupp X n c).support ⊆ c.support.biUnion (fun s =>
      Finset.univ.image (subdivisionSimplex X n s)) := by
  intro t ht
  obtain ⟨s, hs, σ, hσ⟩ := mem_support_subdivisionFinsupp X n c t ht
  exact Finset.mem_biUnion.mpr ⟨s, hs, Finset.mem_image.mpr ⟨σ, Finset.mem_univ _, hσ⟩⟩

/-- Actual degreewise subdivision on mathlib's integral singular chains. -/
def subdivisionDegree (X : TopCat.{0}) (n : ℕ) :
    (LocalHomology.Cycles.integralSingularChains X).X n →ₗ[ℤ] (LocalHomology.Cycles.integralSingularChains X).X n :=
  (SingularChainSupport.Cycles.singularChainCoefficients X n).symm.toLinearMap ∘ₗ subdivisionFinsupp X n ∘ₗ
    (SingularChainSupport.Cycles.singularChainCoefficients X n).toLinearMap

/-- Its coefficients are exactly the signed finite-support operator. -/
@[simp]
theorem subdivisionDegree_coefficients (X : TopCat.{0}) (n : ℕ)
    (c : (LocalHomology.Cycles.integralSingularChains X).X n) :
    SingularChainSupport.Cycles.singularChainCoefficients X n (subdivisionDegree X n c) =
      subdivisionFinsupp X n (SingularChainSupport.Cycles.singularChainCoefficients X n c) := by
  simp [subdivisionDegree]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The concrete simplex-summand formula in the actual chain module. -/
theorem subdivisionDegree_simplex (X : TopCat.{0}) (n : ℕ)
    (s : SingularSimplex X n) (a : ℤ) :
    subdivisionDegree X n ((TopCat.toSSet.obj X).ιChainComplex
      (R := ModuleCat.of ℤ ℤ) s a) =
      ∑ σ : Equiv.Perm (Fin (n + 1)),
        (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ)
          (subdivisionSimplex X n s σ) ((Equiv.Perm.sign σ : ℤ) * a) := by
  have hcoeff (t : SingularSimplex X n) (b : ℤ) :
      SingularChainSupport.Cycles.singularChainCoefficients X n
        ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) t b) =
          Finsupp.single t b := by
    simpa only using! SingularChainSupport.Cycles.singularChainCoefficients_simplex_apply X n t b
  apply (SingularChainSupport.Cycles.singularChainCoefficients X n).injective
  simp only [subdivisionDegree_coefficients, hcoeff,
    subdivisionFinsupp_single, map_sum]

/-- The geometric support formula on the actual singular chain module. -/
theorem mem_support_subdivisionDegree (X : TopCat.{0}) (n : ℕ)
    (c : (LocalHomology.Cycles.integralSingularChains X).X n) (t : SingularSimplex X n)
    (ht : t ∈ SingularChainSupport.Cycles.singularChainSupport (subdivisionDegree X n c)) :
    ∃ s ∈ SingularChainSupport.Cycles.singularChainSupport c, ∃ σ : Equiv.Perm (Fin (n + 1)),
      subdivisionSimplex X n s σ = t := by
  change t ∈ (SingularChainSupport.Cycles.singularChainCoefficients X n (subdivisionDegree X n c)).support at ht
  rw [subdivisionDegree_coefficients] at ht
  exact mem_support_subdivisionFinsupp X n (SingularChainSupport.Cycles.singularChainCoefficients X n c) t ht

/-- Consequently each subdivided support simplex has range contained in the
range of some original support simplex. -/
theorem support_subdivisionDegree_range (X : TopCat.{0}) (n : ℕ)
    (c : (LocalHomology.Cycles.integralSingularChains X).X n) (t : SingularSimplex X n)
    (ht : t ∈ SingularChainSupport.Cycles.singularChainSupport (subdivisionDegree X n c)) :
    ∃ s ∈ SingularChainSupport.Cycles.singularChainSupport c,
      Set.range (X.toSSetObjEquiv (.op ⦋n⦌) t) ⊆
        Set.range (X.toSSetObjEquiv (.op ⦋n⦌) s) := by
  obtain ⟨s, hs, σ, rfl⟩ := mem_support_subdivisionDegree X n c t ht
  exact ⟨s, hs, range_subdivisionSimplex_subset X n s σ⟩

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.SubdivisionOperator.Cycles
end ComponentSource_4

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.SubdivisionOperator"

@[expose] public section ComponentSource_5
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.SubdivisionSmallness -/

/-! # Subdivision Smallness -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.SubdivisionSmallness.Cycles

noncomputable section

/-!
# Actual iterated subdivision makes finite singular chains small

The support formula for the genuine degreewise signed subdivision operator is
iterated and matched with the actual affine cell maps. Thus the geometric mesh
estimate applies to every simplex that survives in the actual subdivided chain,
including any cancellations of coefficients.
-/

open _root_.CategoryTheory
open scoped Simplicial

/-- Every simplex in the support of an actual iterated subdivision comes from
an original support simplex and an equally long list of actual cell maps. -/
theorem mem_support_iterated_subdivisionDegree (X : TopCat.{0}) (n N : ℕ)
    (c : (LocalHomology.Cycles.integralSingularChains X).X n) (t : SubdivisionOperator.Cycles.SingularSimplex X n)
    (ht : t ∈ SingularChainSupport.Cycles.singularChainSupport ((SubdivisionOperator.Cycles.subdivisionDegree X n)^[N] c)) :
    ∃ s ∈ SingularChainSupport.Cycles.singularChainSupport c, ∃ l : List (Equiv.Perm (Fin (n + 1))),
      l.length = N ∧ X.toSSetObjEquiv (.op ⦋n⦌) t =
        (X.toSSetObjEquiv (.op ⦋n⦌) s).comp (IteratedSubdivision.Cycles.iteratedSubdivisionMap l) := by
  induction N generalizing t with
  | zero =>
      refine ⟨t, ?_, [], rfl, ?_⟩
      · simpa only [Function.iterate_zero_apply] using ht
      · simp
  | succ N ih =>
      rw [Function.iterate_succ_apply'] at ht
      obtain ⟨u, hu, σ, rfl⟩ := SubdivisionOperator.Cycles.mem_support_subdivisionDegree X n _ t ht
      obtain ⟨s, hs, l, hl, heq⟩ := ih u hu
      refine ⟨s, hs, σ :: l, by simp [hl], ?_⟩
      simp only [SubdivisionOperator.Cycles.subdivisionSimplex_toContinuousMap, heq,
        IteratedSubdivision.Cycles.iteratedSubdivisionMap_cons, ContinuousMap.comp_assoc]

/-- For every genuine finite integral chain, some actual iterate of its signed
barycentric subdivision consists entirely of simplices in single cover members. -/
theorem exists_subdivisionDegree_iterate_small {X : TopCat.{0}} {J : Type}
    (U : J → Set X) (hopen : ∀ i, IsOpen (U i))
    (hcover : ∀ x : X, ∃ i, x ∈ U i) {n : ℕ}
    (c : (LocalHomology.Cycles.integralSingularChains X).X n) :
    ∃ N : ℕ, ∀ t ∈ SingularChainSupport.Cycles.singularChainSupport ((SubdivisionOperator.Cycles.subdivisionDegree X n)^[N] c),
      t ∈ (AlgebraicTopology.DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex X U).obj (.op ⦋n⦌) := by
  obtain ⟨N, hN⟩ := IteratedSubdivision.Cycles.singularChain_iteratedSubdivision_small U hopen hcover c
  refine ⟨N, ?_⟩
  intro t ht
  obtain ⟨s, hs, l, hl, heq⟩ := mem_support_iterated_subdivisionDegree X n N c t ht
  change ∃ i, Set.range (X.toSSetObjEquiv (.op ⦋n⦌) t) ⊆ U i
  rw [heq]
  exact hN s hs l hl

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.SubdivisionSmallness.Cycles
end ComponentSource_5

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.SubdivisionSmallness"

@[expose] public section ComponentSource_6
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.SmallChainImage -/

/-! # Small Chain Image -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles

noncomputable section

/-!
# The actual image of small singular chains

The inclusion of the small singular simplicial set induces a genuine chain
map. In the canonical finite-support coefficient descriptions, it is precisely
extension along the inclusion of simplex indices. Hence its degreewise image
is exactly the chains whose support consists of small simplices.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped Simplicial

/-- Canonical simplex coefficients for the integral chains of any simplicial set. -/
def simplicialIntegralChainDegreeFinsuppIso (S : SSet.{0}) (n : ℕ) :
    (S.chainComplex (ModuleCat.of ℤ ℤ)).X n ≅
      ModuleCat.of ℤ (S.obj (.op ⦋n⦌) →₀ ℤ) :=
  (S.isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n).coconePointUniqueUpToIso
    (ModuleCat.finsuppCoconeIsColimit ℤ ℤ (S.obj (.op ⦋n⦌)))

def simplicialIntegralChainCoefficients (S : SSet.{0}) (n : ℕ) :
    (S.chainComplex (ModuleCat.of ℤ ℤ)).X n ≃ₗ[ℤ] (S.obj (.op ⦋n⦌) →₀ ℤ) :=
  (simplicialIntegralChainDegreeFinsuppIso S n).toLinearEquiv

@[reassoc (attr := simp)]
theorem simplicialIntegralChainCoefficients_simplex (S : SSet.{0}) (n : ℕ)
    (s : S.obj (.op ⦋n⦌)) :
    S.ιChainComplex (R := ModuleCat.of ℤ ℤ) s ≫
      (simplicialIntegralChainDegreeFinsuppIso S n).hom =
        ModuleCat.ofHom (Finsupp.lsingle s (R := ℤ) (M := ModuleCat.of ℤ ℤ)) :=
  (S.isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n).comp_coconePointUniqueUpToIso_hom
    (ModuleCat.finsuppCoconeIsColimit ℤ ℤ (S.obj (.op ⦋n⦌))) (Discrete.mk s)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A simplicial map carries the coefficient of each source simplex to its
actual image simplex, adding coefficients if several images coincide. -/
theorem simplicialIntegralChainCoefficients_naturality {S T : SSet.{0}}
    (f : S ⟶ T) (n : ℕ) :
    (SSet.chainComplexMap f (ModuleCat.of ℤ ℤ)).f n ≫
        (simplicialIntegralChainDegreeFinsuppIso T n).hom =
      (simplicialIntegralChainDegreeFinsuppIso S n).hom ≫
        ModuleCat.ofHom (Finsupp.lmapDomain ℤ ℤ (f.app (.op ⦋n⦌))) := by
  apply SSet.chainComplex_hom_ext
  intro s
  simp only [SSet.ι_chainComplexMap_f_assoc,
    simplicialIntegralChainCoefficients_simplex,
    simplicialIntegralChainCoefficients_simplex_assoc]
  apply ModuleCat.hom_ext
  ext a
  simp [Finsupp.lmapDomain_apply]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Elementwise form of the genuine coefficient naturality identity. -/
theorem simplicialIntegralChainCoefficients_map {S T : SSet.{0}}
    (f : S ⟶ T) (n : ℕ) (c : (S.chainComplex (ModuleCat.of ℤ ℤ)).X n) :
    simplicialIntegralChainCoefficients T n
        ((SSet.chainComplexMap f (ModuleCat.of ℤ ℤ)).f n c) =
      Finsupp.mapDomain (f.app (.op ⦋n⦌))
        (simplicialIntegralChainCoefficients S n c) := by
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    Finsupp.lmapDomain_apply] using!
    congrArg (fun g : (S.chainComplex (ModuleCat.of ℤ ℤ)).X n ⟶
      ModuleCat.of ℤ (T.obj (.op ⦋n⦌) →₀ ℤ) => g.hom c)
      (simplicialIntegralChainCoefficients_naturality f n)

variable (X : TopCat.{0}) {J : Type} (U : J → Set X)

/-- Genuine integral chains of the small singular simplicial subcomplex. -/
abbrev integralSmallSingularChains : ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  (OAI.AlgebraicTopology.DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex X U : SSet).chainComplex
    (ModuleCat.of ℤ ℤ)

/-- The actual chain map induced by inclusion of small singular simplices. -/
abbrev smallIntegralChainInclusion :
    integralSmallSingularChains X U ⟶ LocalHomology.Cycles.integralSingularChains X :=
  SSet.chainComplexMap (OAI.AlgebraicTopology.DeRham.Comparison.SmallSingularSet.smallSingularInclusion X U)
    (ModuleCat.of ℤ ℤ)

/-- Canonical finite-support coefficients on the genuine small-chain complex. -/
abbrev smallIntegralChainCoefficients (n : ℕ) :
    (integralSmallSingularChains X U).X n ≃ₗ[ℤ]
      ((OAI.AlgebraicTopology.DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex X U : SSet).obj (.op ⦋n⦌) →₀ ℤ) :=
  simplicialIntegralChainCoefficients
    (OAI.AlgebraicTopology.DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex X U : SSet) n

/-- In canonical coefficients the actual inclusion extends along the subtype
inclusion, with no arbitrary choice of a chain-level comparison map. -/
theorem smallIntegralChainInclusion_coefficients (n : ℕ)
    (c : (integralSmallSingularChains X U).X n) :
    SingularChainSupport.Cycles.singularChainCoefficients X n ((smallIntegralChainInclusion X U).f n c) =
      Finsupp.mapDomain Subtype.val (smallIntegralChainCoefficients X U n c) :=
  simplicialIntegralChainCoefficients_map
    (OAI.AlgebraicTopology.DeRham.Comparison.SmallSingularSet.smallSingularInclusion X U) n c

/-- The actual small-chain inclusion is injective in each degree. -/
theorem smallIntegralChainInclusion_injective (n : ℕ) :
    Function.Injective ((smallIntegralChainInclusion X U).f n) := by
  intro a b h
  apply (smallIntegralChainCoefficients X U n).injective
  apply Finsupp.mapDomain_injective Subtype.val_injective
  rw [← smallIntegralChainInclusion_coefficients, ← smallIntegralChainInclusion_coefficients, h]

instance smallIntegralChainInclusion_degree_mono (n : ℕ) :
    Mono ((smallIntegralChainInclusion X U).f n) :=
  (ModuleCat.mono_iff_injective _).mpr (smallIntegralChainInclusion_injective X U n)

instance smallIntegralChainInclusion_mono : Mono (smallIntegralChainInclusion X U) :=
  HomologicalComplex.mono_of_mono_f _ (fun _ => inferInstance)

/-- The image of the genuine inclusion is exactly the chains supported on
small simplices. This identifies the support criterion with actual image membership. -/
theorem mem_range_smallIntegralChainInclusion_iff (n : ℕ)
    (c : (LocalHomology.Cycles.integralSingularChains X).X n) :
    c ∈ LinearMap.range ((smallIntegralChainInclusion X U).f n).hom ↔
      ∀ t ∈ SingularChainSupport.Cycles.singularChainSupport c,
        t ∈ (OAI.AlgebraicTopology.DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex X U).obj (.op ⦋n⦌) := by
  constructor
  · rintro ⟨b, rfl⟩ t ht
    change t ∈ (SingularChainSupport.Cycles.singularChainCoefficients X n
      ((smallIntegralChainInclusion X U).f n b)).support at ht
    rw [smallIntegralChainInclusion_coefficients] at ht
    obtain ⟨s, rfl⟩ := Finsupp.mem_range_of_mapDomain_ne_zero
      (Finsupp.mem_support_iff.mp ht)
    exact s.property
  · intro hc
    have hcoeff : SingularChainSupport.Cycles.singularChainCoefficients X n c ∈ Set.range
        (Finsupp.mapDomain (Subtype.val :
          (OAI.AlgebraicTopology.DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex X U : SSet).obj (.op ⦋n⦌) →
            (TopCat.toSSet.obj X).obj (.op ⦋n⦌))) := by
      apply (Finsupp.mem_range_mapDomain_iff _ Subtype.val_injective _).2
      intro t ht
      by_contra hne
      apply ht
      exact ⟨⟨t, hc t (Finsupp.mem_support_iff.mpr hne)⟩, rfl⟩
    obtain ⟨b, hb⟩ := hcoeff
    refine ⟨(smallIntegralChainCoefficients X U n).symm b, ?_⟩
    apply (SingularChainSupport.Cycles.singularChainCoefficients X n).injective
    rw [smallIntegralChainInclusion_coefficients]
    exact (congrArg (Finsupp.mapDomain Subtype.val)
      ((smallIntegralChainCoefficients X U n).apply_symm_apply b)).trans hb

/-- The actual signed barycentric operator eventually lands in the actual
image of the small-chain inclusion for every finite integral chain. -/
theorem exists_subdivisionDegree_iterate_in_smallChainImage
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i)
    {n : ℕ} (c : (LocalHomology.Cycles.integralSingularChains X).X n) :
    ∃ N : ℕ, (SubdivisionOperator.Cycles.subdivisionDegree X n)^[N] c ∈
      LinearMap.range ((smallIntegralChainInclusion X U).f n).hom := by
  obtain ⟨N, hN⟩ := SubdivisionSmallness.Cycles.exists_subdivisionDegree_iterate_small U hopen hcover c
  exact ⟨N, (mem_range_smallIntegralChainInclusion_iff X U n _).2 hN⟩

/-- Equivalent preimage formulation, with a genuine element of the small-chain complex. -/
theorem exists_subdivisionDegree_iterate_smallChain_preimage
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i)
    {n : ℕ} (c : (LocalHomology.Cycles.integralSingularChains X).X n) :
    ∃ N : ℕ, ∃ b : (integralSmallSingularChains X U).X n,
      (smallIntegralChainInclusion X U).f n b = (SubdivisionOperator.Cycles.subdivisionDegree X n)^[N] c :=
  exists_subdivisionDegree_iterate_in_smallChainImage X U hopen hcover c

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles
end ComponentSource_6

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.SmallChainImage"

@[expose] public section ComponentSource_7
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion -/

/-! # Binary Small Inclusion -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles

noncomputable section

/-!
# The binary small-chain presentation and its canonical inclusion

This identifies the actual binary-cover model used by Mayer--Vietoris with
the actual Bool-indexed small-chain model used by subdivision.
-/

open _root_.CategoryTheory

variable (X : TopCat.{0}) (A B : Set X)

/-- The binary small-chain model used by Mayer--Vietoris is the same actual
small-chain complex as the Bool-indexed cover model. -/
def binarySmallFamilyChainIso :
    SmallMayerVietoris.Cycles.binarySmallSingularChains X A B ≅
      SmallChainImage.Cycles.integralSmallSingularChains X (fun b : Bool => if b then B else A) :=
  eqToIso (congrArg
    (fun S : (TopCat.toSSet.obj X).Subcomplex =>
      (S : SSet).chainComplex (ModuleCat.of ℤ ℤ))
    (SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex_eq X A B))

/-- The actual binary-cover small-chain inclusion, using the proved equality
of its two presentations. -/
def binarySmallIntegralChainInclusion :
    SmallMayerVietoris.Cycles.binarySmallSingularChains X A B ⟶ LocalHomology.Cycles.integralSingularChains X :=
  (binarySmallFamilyChainIso X A B).hom ≫
    SmallChainImage.Cycles.smallIntegralChainInclusion X (fun b : Bool => if b then B else A)

private theorem chainInclusion_eq_transport {S : SSet.{0}} (P Q : S.Subcomplex)
    (h : P = Q) :
    (eqToIso (congrArg (fun T : S.Subcomplex =>
      (T : SSet).chainComplex (ModuleCat.of ℤ ℤ)) h)).hom ≫
      SSet.chainComplexMap Q.ι (ModuleCat.of ℤ ℤ) =
      SSet.chainComplexMap P.ι (ModuleCat.of ℤ ℤ) := by
  subst Q
  simp

/-- The transported binary inclusion is exactly the map induced by the
canonical simplicial-subcomplex inclusion. -/
theorem binarySmallIntegralChainInclusion_eq_canonical :
    binarySmallIntegralChainInclusion X A B =
      SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex X A B).ι := by
  exact chainInclusion_eq_transport _ _ (SmallMayerVietoris.Cycles.binarySmallSingularSubcomplex_eq X A B)

set_option backward.isDefEq.respectTransparency false in
/-- The left small-chain map followed by the ambient inclusion is the actual
singular chain map of the left subspace inclusion. -/
theorem binarySmallIntegralChainInclusion_left :
    SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (SmallMayerVietoris.Cycles.binarySmallSingularLeft X A B) ≫
      binarySmallIntegralChainInclusion X A B =
      LocalHomology.Cycles.integralSingularChainFunctor.map (LocalHomology.Cycles.subspaceInclusion X A) := by
  rw [binarySmallIntegralChainInclusion_eq_canonical, ← CategoryTheory.Functor.map_comp]
  congr 1

set_option backward.isDefEq.respectTransparency false in
/-- The right small-chain map followed by the ambient inclusion is the actual
singular chain map of the right subspace inclusion. -/
theorem binarySmallIntegralChainInclusion_right :
    SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (SmallMayerVietoris.Cycles.binarySmallSingularRight X A B) ≫
      binarySmallIntegralChainInclusion X A B =
      LocalHomology.Cycles.integralSingularChainFunctor.map (LocalHomology.Cycles.subspaceInclusion X B) := by
  rw [binarySmallIntegralChainInclusion_eq_canonical, ← CategoryTheory.Functor.map_comp]
  congr 1

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles
end ComponentSource_7

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion"

@[expose] public section ComponentSource_8
/- Original module: OAI.AlgebraicTopology.Cohomology.Singular.ChainRepresentatives -/

/-! # Chain Representatives -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.ChainRepresentatives

noncomputable section

/-!
# Representatives for the homology paired with singular cohomology

These are the chain-complex counterparts of the cocycle representatives.
They use mathlib's existing explicit kernel/image description of homology.
-/

open _root_.CategoryTheory

variable {R : Type} [Ring R]

abbrev chainCycles (C : ChainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) :
    Submodule R (C.X n) :=
  LinearMap.ker (C.sc n).g.hom

abbrev chainBoundaryMap (C : ChainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) :
    (C.sc n).X₁ →ₗ[R] chainCycles C n :=
  (C.sc n).moduleCatToCycles

abbrev chainBoundaries (C : ChainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) :
    Submodule R (chainCycles C n) :=
  LinearMap.range (chainBoundaryMap C n)

/-- The usual quotient of cycles by boundaries is the categorical homology. -/
def homologyQuotientIso (C : ChainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) :
    C.homology n ≅ ModuleCat.of R (chainCycles C n ⧸ chainBoundaries C n) :=
  (C.sc n).moduleCatHomologyIso

/-- The homology class of a chain cycle. -/
def chainClass (C : ChainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) :
    chainCycles C n →ₗ[R] C.homology n :=
  (homologyQuotientIso C n).toLinearEquiv.symm.toLinearMap.comp
    (chainBoundaries C n).mkQ

@[simp]
theorem mem_chainCycles_iff_succ (C : ChainComplex (ModuleCat.{0} R) ℕ)
    (n : ℕ) (x : C.X (n + 1)) :
    x ∈ chainCycles C (n + 1) ↔ (C.d (n + 1) n) x = 0 := by
  change (C.d (n + 1) ((ComplexShape.down ℕ).next (n + 1))) x = 0 ↔ _
  rw [(ComplexShape.down ℕ).next_eq'
    (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl)]

/-- Every degree-zero chain is a cycle in a nonnegative chain complex. -/
theorem mem_chainCycles_zero (C : ChainComplex (ModuleCat.{0} R) ℕ) (x : C.X 0) :
    x ∈ chainCycles C 0 := by
  change (C.d 0 ((ComplexShape.down ℕ).next 0)) x = 0
  rw [C.shape 0 _ (Nat.succ_ne_zero _)]
  rfl

@[simp]
theorem chainCycles_zero_eq_top (C : ChainComplex (ModuleCat.{0} R) ℕ) :
    chainCycles C 0 = ⊤ := by
  ext x
  simp only [Submodule.mem_top, iff_true]
  exact mem_chainCycles_zero C x

/-- Every differential of a cycle vanishes, including off-shape differentials. -/
theorem chainCycle_d_eq_zero (C : ChainComplex (ModuleCat.{0} R) ℕ)
    (n i : ℕ) (x : chainCycles C n) : (C.d n i) (x : C.X n) = 0 := by
  by_cases h : (ComplexShape.down ℕ).Rel n i
  · have hx : (C.d n ((ComplexShape.down ℕ).next n)) (x : C.X n) = 0 := x.property
    have hi : (ComplexShape.down ℕ).next n = i := (ComplexShape.down ℕ).next_eq' h
    rw [hi] at hx
    exact hx
  · rw [C.shape n i h]
    rfl

/-- Agreement of the explicit class map with the categorical projection. -/
theorem chainClass_eq_homologyπ (C : ChainComplex (ModuleCat.{0} R) ℕ)
    (n : ℕ) (x : chainCycles C n) :
    chainClass C n x = (C.homologyπ n) ((C.sc n).moduleCatCyclesIso.inv x) := by
  change (C.sc n).moduleCatHomologyIso.inv ((C.sc n).moduleCatLeftHomologyData.π x) =
    (C.sc n).homologyπ ((C.sc n).moduleCatCyclesIso.inv x)
  exact (ConcreteCategory.congr_hom ((C.sc n).moduleCatCyclesIso_inv_π) x).symm

theorem chainClass_surjective (C : ChainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) :
    Function.Surjective (chainClass C n) :=
  (homologyQuotientIso C n).toLinearEquiv.symm.surjective.comp
    (chainBoundaries C n).mkQ_surjective

theorem chainClass_eq_iff (C : ChainComplex (ModuleCat.{0} R) ℕ)
    (n : ℕ) (x y : chainCycles C n) :
    chainClass C n x = chainClass C n y ↔ x - y ∈ chainBoundaries C n := by
  change (homologyQuotientIso C n).toLinearEquiv.symm ((chainBoundaries C n).mkQ x) =
      (homologyQuotientIso C n).toLinearEquiv.symm ((chainBoundaries C n).mkQ y) ↔ _
  rw [(homologyQuotientIso C n).toLinearEquiv.symm.injective.eq_iff]
  exact Submodule.Quotient.eq _

@[simp]
theorem chainClass_eq_zero_iff (C : ChainComplex (ModuleCat.{0} R) ℕ)
    (n : ℕ) (x : chainCycles C n) :
    chainClass C n x = 0 ↔ x ∈ chainBoundaries C n := by
  simpa using chainClass_eq_iff C n x 0

@[simp]
theorem chainClass_boundary (C : ChainComplex (ModuleCat.{0} R) ℕ)
    (n : ℕ) (x : (C.sc n).X₁) :
    chainClass C n (chainBoundaryMap C n x) = 0 := by
  apply (chainClass_eq_zero_iff C n _).mpr
  exact ⟨x, rfl⟩

/-- Equality of homology classes is witnessed by an actual chain one degree higher. -/
theorem chainClass_eq_iff_exists (C : ChainComplex (ModuleCat.{0} R) ℕ)
    (n : ℕ) (x y : chainCycles C n) :
    chainClass C n x = chainClass C n y ↔
      ∃ z : C.X (n + 1), (C.d (n + 1) n) z =
        (x : C.X n) - (y : C.X n) := by
  rw [chainClass_eq_iff]
  have h : (x - y ∈ chainBoundaries C n) ↔
      ∃ z : (C.sc n).X₁, (C.sc n).f z = (x : C.X n) - (y : C.X n) := by
    change (∃ z, chainBoundaryMap C n z = x - y) ↔ _
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨z, congrArg Subtype.val hz⟩
    · rintro ⟨z, hz⟩
      exact ⟨z, Subtype.ext hz⟩
  rw [h]
  change (∃ z : C.X ((ComplexShape.down ℕ).prev n),
    (C.d ((ComplexShape.down ℕ).prev n) n) z =
      (x : C.X n) - (y : C.X n)) ↔ _
  rw [(ComplexShape.down ℕ).prev_eq'
    (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl)]

/-- A cycle has zero homology class precisely when it is a boundary. -/
theorem chainClass_eq_zero_iff_exists (C : ChainComplex (ModuleCat.{0} R) ℕ)
    (n : ℕ) (x : chainCycles C n) :
    chainClass C n x = 0 ↔ ∃ z : C.X (n + 1), (C.d (n + 1) n) z = (x : C.X n) := by
  simpa using chainClass_eq_iff_exists C n x 0

end

end OAI.AlgebraicTopology.Cohomology.Singular.ChainRepresentatives
end ComponentSource_8

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicTopology.Cohomology.Singular.ChainRepresentatives"

@[expose] public section ComponentSource_9
/- Original module: OAI.AlgebraicTopology.Cohomology.Singular.Formulas -/

/-! # Formulas -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.Formulas

noncomputable section

/-!
# The ordinary simplicial coboundary and pullback formulas

The degreewise objects of `simplicialCochains` are all functions on simplices.
The lemmas below identify its differential with the alternating face formula
and its contravariant maps with precomposition on simplices. Thus the
opposite-category construction has the standard cochain operations.

The categorical proofs generalize the checked `OppositeCochainAudit.lean`
from the frozen September 2026 audit from rational coefficients to an arbitrary
module over a ring. No Hodge-theoretic comparison is asserted here.
-/

open _root_.CategoryTheory Opposite
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [Ring R]

/-- Evaluating the cochain differential is the alternating sum of face evaluations. -/
theorem evaluation_coboundary (K : SSet.{0}) (M : ModuleCat.{0} R)
    {n : ℕ} (s : K _⦋n + 1⦌) :
    (Basic.simplicialCochains K M).d n (n + 1) ≫ Coefficients.simplicialEvaluation K M s =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.val) • Coefficients.simplicialEvaluation K M (K.δ i s) := by
  simpa only [Coefficients.simplicialEvaluation, Basic.simplicialCochains, Basic.oppositeSimplicialChains,
    HomologicalComplex.unop_d, unop_comp, unop_sum, unop_zsmul] using
    congrArg Quiver.Hom.unop (K.ιChainComplex_d (R := op M) s)

/-- A simplicial pullback evaluates on the image of the simplex. -/
theorem evaluation_pullback (M : ModuleCat.{0} R) {K L : SSet.{0}}
    (f : K ⟶ L) {n : ℕ} (s : K _⦋n⦌) :
    (Functor.simplicialPullback M f).f n ≫ Coefficients.simplicialEvaluation K M s =
      Coefficients.simplicialEvaluation L M (f.app _ s) := by
  change ((SSet.chainComplexMap f (op M)).f n).unop ≫
    Coefficients.simplicialEvaluation K M s = Coefficients.simplicialEvaluation L M (f.app _ s)
  simpa only [Coefficients.simplicialEvaluation, unop_comp] using
    congrArg Quiver.Hom.unop
      (SSet.ι_chainComplexMap_f (X := K) (Y := L) (R := op M) f s)

/-- The alternating face formula for an individual module-valued cochain. -/
theorem evaluation_coboundary_apply (K : SSet.{0}) (M : ModuleCat.{0} R)
    {n : ℕ} (c : (Basic.simplicialCochains K M).X n) (s : K _⦋n + 1⦌) :
    Coefficients.simplicialEvaluation K M s ((Basic.simplicialCochains K M).d n (n + 1) c) =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.val) • Coefficients.simplicialEvaluation K M (K.δ i s) c := by
  simpa [ModuleCat.comp_apply] using
    ConcreteCategory.congr_hom (evaluation_coboundary K M s) c

/-- The precomposition formula for an individual module-valued cochain. -/
theorem evaluation_pullback_apply (M : ModuleCat.{0} R) {K L : SSet.{0}}
    (f : K ⟶ L) {n : ℕ} (c : (Basic.simplicialCochains L M).X n) (s : K _⦋n⦌) :
    Coefficients.simplicialEvaluation K M s ((Functor.simplicialPullback M f).f n c) =
      Coefficients.simplicialEvaluation L M (f.app _ s) c := by
  simpa [ModuleCat.comp_apply] using
    ConcreteCategory.congr_hom (evaluation_pullback M f s) c

/-- In ordinary function coordinates, the differential is the alternating face sum. -/
theorem degreewiseFunctionIso_coboundary (K : SSet.{0}) (M : ModuleCat.{0} R)
    {n : ℕ} (c : (Basic.simplicialCochains K M).X n) (s : K _⦋n + 1⦌) :
    (Coefficients.degreewiseFunctionIso K M (n + 1)).hom
        ((Basic.simplicialCochains K M).d n (n + 1) c) s =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.val) •
        (Coefficients.degreewiseFunctionIso K M n).hom c (K.δ i s) := by
  calc
    _ = Coefficients.simplicialEvaluation K M s ((Basic.simplicialCochains K M).d n (n + 1) c) :=
      Coefficients.degreewiseFunctionIso_hom_apply K M _ s
    _ = ∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.val) •
        Coefficients.simplicialEvaluation K M (K.δ i s) c := evaluation_coboundary_apply K M c s
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun v : M => ((-1 : ℤ) ^ i.val) • v)
        (Coefficients.degreewiseFunctionIso_hom_apply K M c (K.δ i s)).symm

/-- In ordinary function coordinates, a simplicial pullback is precomposition. -/
theorem degreewiseFunctionIso_pullback (M : ModuleCat.{0} R) {K L : SSet.{0}}
    (f : K ⟶ L) {n : ℕ} (c : (Basic.simplicialCochains L M).X n) (s : K _⦋n⦌) :
    (Coefficients.degreewiseFunctionIso K M n).hom ((Functor.simplicialPullback M f).f n c) s =
      (Coefficients.degreewiseFunctionIso L M n).hom c (f.app _ s) := by
  calc
    _ = Coefficients.simplicialEvaluation K M s ((Functor.simplicialPullback M f).f n c) :=
      Coefficients.degreewiseFunctionIso_hom_apply K M _ s
    _ = Coefficients.simplicialEvaluation L M (f.app _ s) c := evaluation_pullback_apply M f c s
    _ = _ := (Coefficients.degreewiseFunctionIso_hom_apply L M c (f.app _ s)).symm

end

end OAI.AlgebraicTopology.Cohomology.Singular.Formulas
end ComponentSource_9

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicTopology.Cohomology.Singular.Formulas"

@[expose] public section ComponentSource_10
/- Original module: OAI.AlgebraicTopology.Cohomology.Singular.ChainDual -/

/-! # Chain Dual -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.ChainDual

noncomputable section

/-!
# Singular cochains as linear maps on singular chains

The genuine coproduct defining simplicial chains is freely generated over the
coefficient ring by the simplices. Its linear maps into a coefficient module are
therefore exactly the ordinary cochains. The equivalence below is compatible
with the actual alternating boundary and coboundary operators.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open scoped Simplicial

variable {R : Type} [CommRing R]

/-- Simplicial chains with coefficients in the scalar ring itself. -/
abbrev simplicialScalarChains (K : SSet.{0}) : ChainComplex (ModuleCat.{0} R) ℕ :=
  K.chainComplex (ModuleCat.of R R)

/-- The chain consisting of one simplex with coefficient one. -/
def simplexChain (K : SSet.{0}) {n : ℕ} (s : K _⦋n⦌) :
    (simplicialScalarChains (R := R) K).X n :=
  K.ιChainComplex (R := ModuleCat.of R R) s 1

/-- Scalar-linear maps on simplicial chains are determined by their values on simplices. -/
theorem chainFunctional_ext (K : SSet.{0}) (M : ModuleCat.{0} R) {n : ℕ}
    {f g : (simplicialScalarChains (R := R) K).X n →ₗ[R] M}
    (h : ∀ s : K _⦋n⦌, f (simplexChain K s) = g (simplexChain K s)) : f = g := by
  have hfg : ModuleCat.ofHom f = ModuleCat.ofHom g := by
    apply SSet.chainComplex_hom_ext (X := K) (R := ModuleCat.of R R)
    intro s
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    exact h s
  exact congrArg ModuleCat.Hom.hom hfg

/-- Extend the values assigned to simplices uniquely and linearly to all chains. -/
def chainFunctionalOfFunction (K : SSet.{0}) (M : ModuleCat.{0} R) (n : ℕ)
    (v : K _⦋n⦌ → M) : (simplicialScalarChains (R := R) K).X n →ₗ[R] M :=
  (Sigma.desc (fun s : K _⦋n⦌ =>
    ModuleCat.ofHom (LinearMap.toSpanSingleton R M (v s)))).hom

@[simp]
theorem chainFunctionalOfFunction_simplex (K : SSet.{0}) (M : ModuleCat.{0} R)
    (n : ℕ) (v : K _⦋n⦌ → M) (s : K _⦋n⦌) :
    chainFunctionalOfFunction K M n v (simplexChain K s) = v s := by
  have h := Sigma.ι_comp_desc (fun t : K _⦋n⦌ =>
    (ModuleCat.ofHom (LinearMap.toSpanSingleton R M (v t)) :
      ModuleCat.of R R ⟶ M)) s
  have he := congrArg (fun f : ModuleCat.of R R ⟶ M => f.hom 1) h
  exact he.trans (LinearMap.toSpanSingleton_apply_one R M (v s))

/-- The universal property of the free scalar chain module, as a linear equivalence. -/
def functionChainFunctionalEquiv (K : SSet.{0}) (M : ModuleCat.{0} R) (n : ℕ) :
    (K _⦋n⦌ → M) ≃ₗ[R] ((simplicialScalarChains (R := R) K).X n →ₗ[R] M) where
  toFun := chainFunctionalOfFunction K M n
  invFun f s := f (simplexChain K s)
  left_inv v := by
    funext s
    exact chainFunctionalOfFunction_simplex K M n v s
  right_inv f := by
    apply chainFunctional_ext K M
    intro s
    exact chainFunctionalOfFunction_simplex K M n _ s
  map_add' v w := by
    apply chainFunctional_ext K M
    intro s
    simp only [chainFunctionalOfFunction_simplex, Pi.add_apply, LinearMap.add_apply]
  map_smul' r v := by
    apply chainFunctional_ext K M
    intro s
    simp only [chainFunctionalOfFunction_simplex, Pi.smul_apply, LinearMap.smul_apply,
      RingHom.id_apply]

/-- Genuine simplicial cochains are exactly coefficient-valued linear maps on
scalar simplicial chains. In particular scalar-valued cochains form their linear dual. -/
def degreewiseChainDualEquiv (K : SSet.{0}) (M : ModuleCat.{0} R) (n : ℕ) :
    (Singular.Basic.simplicialCochains K M).X n ≃ₗ[R]
      ((simplicialScalarChains (R := R) K).X n →ₗ[R] M) :=
  (Coefficients.degreewiseFunctionIso K M n).toLinearEquiv.trans (functionChainFunctionalEquiv K M n)

@[simp]
theorem degreewiseChainDualEquiv_simplex (K : SSet.{0}) (M : ModuleCat.{0} R)
    {n : ℕ} (c : (Singular.Basic.simplicialCochains K M).X n) (s : K _⦋n⦌) :
    degreewiseChainDualEquiv K M n c (simplexChain K s) =
      Coefficients.simplicialEvaluation K M s c := by
  change chainFunctionalOfFunction K M n ((Coefficients.degreewiseFunctionIso K M n).hom c)
    (simplexChain K s) = _
  rw [chainFunctionalOfFunction_simplex, Coefficients.degreewiseFunctionIso_hom_apply]

/-- The actual chain boundary of a simplex is its signed sum of faces. -/
theorem simplexChain_boundary (K : SSet.{0}) {n : ℕ} (s : K _⦋n + 1⦌) :
    (simplicialScalarChains (R := R) K).d (n + 1) n (simplexChain K s) =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.val) • simplexChain (R := R) K (K.δ i s) := by
  have h := congrArg
    (fun f : ModuleCat.of R R ⟶ (simplicialScalarChains (R := R) K).X n => f.hom 1)
    (K.ιChainComplex_d (R := ModuleCat.of R R) s)
  simpa only [simplexChain, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.sum_apply,
    LinearMap.smul_apply] using h

/-- Under chain-cochain duality, the cochain differential is precomposition
with the genuine chain boundary. -/
theorem degreewiseChainDualEquiv_coboundary (K : SSet.{0}) (M : ModuleCat.{0} R)
    {n : ℕ} (c : (Singular.Basic.simplicialCochains K M).X n) :
    degreewiseChainDualEquiv K M (n + 1) ((Singular.Basic.simplicialCochains K M).d n (n + 1) c) =
      (degreewiseChainDualEquiv K M n c).comp
        ((simplicialScalarChains (R := R) K).d (n + 1) n).hom := by
  apply chainFunctional_ext K M
  intro s
  simp only [degreewiseChainDualEquiv_simplex, LinearMap.comp_apply,
    simplexChain_boundary, map_sum, map_zsmul, Formulas.evaluation_coboundary_apply]

/-- Chain-cochain adjointness for arbitrary indices, including the zero maps
outside the shape of the complex. -/
theorem degreewiseChainDualEquiv_d (K : SSet.{0}) (M : ModuleCat.{0} R)
    (i j : ℕ) (c : (Singular.Basic.simplicialCochains K M).X i) :
    degreewiseChainDualEquiv K M j ((Singular.Basic.simplicialCochains K M).d i j c) =
      (degreewiseChainDualEquiv K M i c).comp
        ((simplicialScalarChains (R := R) K).d j i).hom := by
  by_cases hij : (ComplexShape.up ℕ).Rel i j
  · have hj : i + 1 = j := hij
    subst j
    exact degreewiseChainDualEquiv_coboundary K M c
  · have hji : ¬(ComplexShape.down ℕ).Rel j i := hij
    rw [(Singular.Basic.simplicialCochains K M).shape i j hij,
      (simplicialScalarChains (R := R) K).shape j i hji]
    simp

/-- Evaluation pairs the coboundary of a cochain with a chain in the same way as
it pairs the cochain with the boundary of that chain. -/
theorem chainCochainPairing_coboundary (K : SSet.{0}) (M : ModuleCat.{0} R)
    {n : ℕ} (c : (Singular.Basic.simplicialCochains K M).X n)
    (z : (simplicialScalarChains (R := R) K).X (n + 1)) :
    degreewiseChainDualEquiv K M (n + 1) ((Singular.Basic.simplicialCochains K M).d n (n + 1) c) z =
      degreewiseChainDualEquiv K M n c
        ((simplicialScalarChains (R := R) K).d (n + 1) n z) :=
  LinearMap.congr_fun (degreewiseChainDualEquiv_coboundary K M c) z

/-- The same chain-duality equivalence on genuine continuous singular simplices. -/
def singularDegreewiseChainDualEquiv (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ) :
    (Singular.Basic.singularCochains M X).X n ≃ₗ[R]
      (((TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R)).X n →ₗ[R] M) :=
  degreewiseChainDualEquiv (TopCat.toSSet.obj X) M n

end

end OAI.AlgebraicTopology.Cohomology.Singular.ChainDual
end ComponentSource_10

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicTopology.Cohomology.Singular.ChainDual"

@[expose] public section ComponentSource_11
/- Original module: OAI.AlgebraicTopology.Cohomology.Singular.Evaluation -/

/-! # Evaluation -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.Evaluation

noncomputable section

/-!
# Evaluation of singular cohomology on singular homology

The pairing descends the actual linear evaluation of a singular cochain on a
singular chain. The chain/cochain differential identity proves both required
independence statements: cocycles vanish on boundaries and coboundaries vanish
on cycles. No arbitrary pairing is supplied as an assumption.
-/

open _root_.CategoryTheory

variable {R : Type} [CommRing R]

/-- Scalar singular chains on the genuine continuous singular simplicial set. -/
abbrev singularScalarChains (X : TopCat.{0}) : ChainComplex (ModuleCat.{0} R) ℕ :=
  ChainDual.simplicialScalarChains (R := R) (TopCat.toSSet.obj X)

/-- Every outgoing differential vanishes on a cocycle, including off-shape ones. -/
theorem cochainCocycle_d_eq_zero (C : CochainComplex (ModuleCat.{0} R) ℕ)
    (n i : ℕ) (c : Representatives.cochainCocycles C n) : (C.d n i) (c : C.X n) = 0 := by
  by_cases h : (ComplexShape.up ℕ).Rel n i
  · have hc : (C.d n ((ComplexShape.up ℕ).next n)) (c : C.X n) = 0 := c.property
    have hi : (ComplexShape.up ℕ).next n = i := (ComplexShape.up ℕ).next_eq' h
    rw [hi] at hc
    exact hc
  · rw [C.shape n i h]
    rfl

/-- A genuine cocycle evaluates to zero on every genuine boundary. -/
theorem cocycle_evaluation_boundary (K : SSet.{0}) (M : ModuleCat.{0} R)
    (n i : ℕ) (c : Representatives.cochainCocycles (Basic.simplicialCochains K M) n)
    (z : (ChainDual.simplicialScalarChains (R := R) K).X i) :
    ChainDual.degreewiseChainDualEquiv K M n (c : (Basic.simplicialCochains K M).X n)
      ((ChainDual.simplicialScalarChains (R := R) K).d i n z) = 0 := by
  have h := LinearMap.congr_fun
    (ChainDual.degreewiseChainDualEquiv_d K M n i (c : (Basic.simplicialCochains K M).X n)) z
  have hc := cochainCocycle_d_eq_zero (Basic.simplicialCochains K M) n i c
  simpa only [hc, map_zero, LinearMap.zero_apply, LinearMap.comp_apply] using h.symm

/-- A genuine coboundary evaluates to zero on every genuine cycle. -/
theorem coboundary_evaluation_cycle (K : SSet.{0}) (M : ModuleCat.{0} R)
    (i n : ℕ) (c : (Basic.simplicialCochains K M).X i)
    (z : ChainRepresentatives.chainCycles (ChainDual.simplicialScalarChains (R := R) K) n) :
    ChainDual.degreewiseChainDualEquiv K M n ((Basic.simplicialCochains K M).d i n c)
      (z : (ChainDual.simplicialScalarChains (R := R) K).X n) = 0 := by
  have h := LinearMap.congr_fun (ChainDual.degreewiseChainDualEquiv_d K M i n c)
    (z : (ChainDual.simplicialScalarChains (R := R) K).X n)
  simpa only [LinearMap.comp_apply,
    ChainRepresentatives.chainCycle_d_eq_zero (ChainDual.simplicialScalarChains (R := R) K) n i z, map_zero] using h

/-- A cocycle's evaluation, descended to actual categorical homology. -/
def evaluateCocycle (K : SSet.{0}) (M : ModuleCat.{0} R) (n : ℕ)
    (c : Representatives.cochainCocycles (Basic.simplicialCochains K M) n) :
    (ChainDual.simplicialScalarChains (R := R) K).homology n →ₗ[R] M :=
  ((ChainRepresentatives.chainBoundaries (ChainDual.simplicialScalarChains (R := R) K) n).liftQ
    ((ChainDual.degreewiseChainDualEquiv K M n (c : (Basic.simplicialCochains K M).X n)).comp
      (ChainRepresentatives.chainCycles (ChainDual.simplicialScalarChains (R := R) K) n).subtype)
    (by
      intro z hz
      rcases hz with ⟨w, rfl⟩
      change ChainDual.degreewiseChainDualEquiv K M n (c : (Basic.simplicialCochains K M).X n)
        (((ChainDual.simplicialScalarChains (R := R) K).sc n).f w) = 0
      exact cocycle_evaluation_boundary K M n _ c w)).comp
    (ChainRepresentatives.homologyQuotientIso (ChainDual.simplicialScalarChains (R := R) K) n).toLinearEquiv.toLinearMap

@[simp]
theorem evaluateCocycle_chainClass (K : SSet.{0}) (M : ModuleCat.{0} R) (n : ℕ)
    (c : Representatives.cochainCocycles (Basic.simplicialCochains K M) n)
    (z : ChainRepresentatives.chainCycles (ChainDual.simplicialScalarChains (R := R) K) n) :
    evaluateCocycle K M n c (ChainRepresentatives.chainClass (ChainDual.simplicialScalarChains (R := R) K) n z) =
      ChainDual.degreewiseChainDualEquiv K M n (c : (Basic.simplicialCochains K M).X n)
        (z : (ChainDual.simplicialScalarChains (R := R) K).X n) := by
  dsimp only [evaluateCocycle, ChainRepresentatives.chainClass, LinearMap.comp_apply]
  simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rfl

/-- Evaluation on homology is linear in the cocycle. -/
def cocycleHomologyEvaluation (K : SSet.{0}) (M : ModuleCat.{0} R) (n : ℕ) :
    Representatives.cochainCocycles (Basic.simplicialCochains K M) n →ₗ[R]
      ((ChainDual.simplicialScalarChains (R := R) K).homology n →ₗ[R] M) where
  toFun := evaluateCocycle K M n
  map_add' c d := by
    ext h
    obtain ⟨z, rfl⟩ := ChainRepresentatives.chainClass_surjective (ChainDual.simplicialScalarChains (R := R) K) n h
    simp only [evaluateCocycle_chainClass, LinearMap.add_apply, Submodule.coe_add, map_add]
  map_smul' r c := by
    ext h
    obtain ⟨z, rfl⟩ := ChainRepresentatives.chainClass_surjective (ChainDual.simplicialScalarChains (R := R) K) n h
    simp only [evaluateCocycle_chainClass, LinearMap.smul_apply, Submodule.coe_smul,
      map_smul, RingHom.id_apply]

/-- Changing the cocycle by a coboundary does not change evaluation on homology. -/
@[simp]
theorem cocycleHomologyEvaluation_boundary (K : SSet.{0}) (M : ModuleCat.{0} R)
    (n : ℕ) (c : ((Basic.simplicialCochains K M).sc n).X₁) :
    cocycleHomologyEvaluation K M n (Representatives.cochainBoundaryMap (Basic.simplicialCochains K M) n c) = 0 := by
  ext h
  obtain ⟨z, rfl⟩ := ChainRepresentatives.chainClass_surjective (ChainDual.simplicialScalarChains (R := R) K) n h
  change evaluateCocycle K M n (Representatives.cochainBoundaryMap (Basic.simplicialCochains K M) n c)
    (ChainRepresentatives.chainClass (ChainDual.simplicialScalarChains (R := R) K) n z) = 0
  rw [evaluateCocycle_chainClass]
  exact coboundary_evaluation_cycle K M _ n c z

/-- Actual simplicial cohomology evaluates linearly on actual simplicial homology. -/
def simplicialHomologyEvaluation (K : SSet.{0}) (M : ModuleCat.{0} R) (n : ℕ) :
    (Basic.simplicialCochains K M).homology n →ₗ[R]
      ((ChainDual.simplicialScalarChains (R := R) K).homology n →ₗ[R] M) :=
  ((Representatives.cochainBoundaries (Basic.simplicialCochains K M) n).liftQ
    (cocycleHomologyEvaluation K M n)
    (by
      intro c hc
      rcases hc with ⟨w, rfl⟩
      exact cocycleHomologyEvaluation_boundary K M n w)).comp
    (Representatives.cohomologyQuotientIso (Basic.simplicialCochains K M) n).toLinearEquiv.toLinearMap

/-- The descended pairing is the original chain/cochain evaluation on representatives. -/
@[simp]
theorem simplicialHomologyEvaluation_class_class (K : SSet.{0}) (M : ModuleCat.{0} R)
    (n : ℕ) (c : Representatives.cochainCocycles (Basic.simplicialCochains K M) n)
    (z : ChainRepresentatives.chainCycles (ChainDual.simplicialScalarChains (R := R) K) n) :
    simplicialHomologyEvaluation K M n (Representatives.cochainClass (Basic.simplicialCochains K M) n c)
      (ChainRepresentatives.chainClass (ChainDual.simplicialScalarChains (R := R) K) n z) =
      ChainDual.degreewiseChainDualEquiv K M n (c : (Basic.simplicialCochains K M).X n)
        (z : (ChainDual.simplicialScalarChains (R := R) K).X n) := by
  dsimp only [simplicialHomologyEvaluation, Representatives.cochainClass, LinearMap.comp_apply]
  simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  exact evaluateCocycle_chainClass K M n c z

/-- Evaluation of singular cohomology with module coefficients on scalar singular homology. -/
def singularEvaluation (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ) :
    Basic.singularCohomology M X n →ₗ[R]
      ((singularScalarChains (R := R) X).homology n →ₗ[R] M) :=
  simplicialHomologyEvaluation (TopCat.toSSet.obj X) M n

/-- Singular evaluation is ordinary evaluation of an actual cocycle on an actual cycle. -/
@[simp]
theorem singularEvaluation_class_class (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ)
    (c : Representatives.singularCocycles M X n) (z : ChainRepresentatives.chainCycles (singularScalarChains (R := R) X) n) :
    singularEvaluation M X n (Representatives.singularClass M X n c)
      (ChainRepresentatives.chainClass (singularScalarChains (R := R) X) n z) =
      ChainDual.singularDegreewiseChainDualEquiv M X n (c : (Basic.singularCochains M X).X n)
        (z : (singularScalarChains (R := R) X).X n) :=
  simplicialHomologyEvaluation_class_class (TopCat.toSSet.obj X) M n c z

end

end OAI.AlgebraicTopology.Cohomology.Singular.Evaluation
end ComponentSource_11

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicTopology.Cohomology.Singular.Evaluation"

@[expose] public section ComponentSource_12
/- Original module: OAI.AlgebraicTopology.Cohomology.Singular.UniversalCoefficient -/

/-! # Universal Coefficient -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.UniversalCoefficient

noncomputable section

/-!
# Universal coefficient duality over a field

The canonical singular cohomology evaluation map is an isomorphism over a field.
The linear algebra below uses extension of linear functionals, as proved in
mathlib by extending bases, with no finite-dimensionality assumption.
-/

open _root_.CategoryTheory

variable {F : Type} [Field F]

/-- A functional which vanishes on a linear map's kernel factors through that map.
No splitting or extension is an extra assumption: mathlib supplies it over a field. -/
theorem functionalFactors_of_vanishesOnKernel
    {V W : Type} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    (f : V →ₗ[F] W) (φ : V →ₗ[F] F)
    (hφ : ∀ v : V, f v = 0 → φ v = 0) :
    ∃ ψ : W →ₗ[F] F, ψ.comp f = φ := by
  have hmem : φ ∈ (LinearMap.ker f).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    exact hφ
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker f] at hmem
  exact hmem

/-- A scalar cocycle which evaluates to zero on every cycle is a coboundary.
This uses the actual chain and cochain complexes in every degree, including zero. -/
theorem cochainClass_eq_zero_of_vanishesOnCycles (K : SSet.{0}) (n : ℕ)
    (c : Representatives.cochainCocycles (Basic.simplicialCochains K (ModuleCat.of F F)) n)
    (hc : ∀ z : ChainRepresentatives.chainCycles (ChainDual.simplicialScalarChains (R := F) K) n,
      ChainDual.degreewiseChainDualEquiv K (ModuleCat.of F F) n c.val z.val = 0) :
    Representatives.cochainClass (Basic.simplicialCochains K (ModuleCat.of F F)) n c = 0 := by
  let C := ChainDual.simplicialScalarChains (R := F) K
  let D := Basic.simplicialCochains K (ModuleCat.of F F)
  let φ : C.X n →ₗ[F] F := ChainDual.degreewiseChainDualEquiv K (ModuleCat.of F F) n c.val
  obtain ⟨ψ, hψ⟩ := functionalFactors_of_vanishesOnKernel (C.sc n).g.hom φ
    (fun z hz => hc ⟨z, hz⟩)
  let p : (D.sc n).X₁ :=
    (ChainDual.degreewiseChainDualEquiv K (ModuleCat.of F F) ((ComplexShape.up ℕ).prev n)).symm ψ
  have hp : (D.sc n).f p = (c : D.X n) := by
    apply (ChainDual.degreewiseChainDualEquiv K (ModuleCat.of F F) n).injective
    change ChainDual.degreewiseChainDualEquiv K (ModuleCat.of F F) n
      (D.d ((ComplexShape.up ℕ).prev n) n p) = φ
    rw [ChainDual.degreewiseChainDualEquiv_d]
    have he : ChainDual.degreewiseChainDualEquiv K (ModuleCat.of F F)
        ((ComplexShape.up ℕ).prev n) p = ψ :=
      (ChainDual.degreewiseChainDualEquiv K (ModuleCat.of F F)
        ((ComplexShape.up ℕ).prev n)).apply_symm_apply ψ
    rw [he]
    exact hψ
  apply (Representatives.cochainClass_eq_zero_iff D n c).mpr
  exact ⟨p, Subtype.ext hp⟩

/-- Every functional on actual scalar homology is evaluation by a scalar cocycle.
The necessary extension from the cycle subspace is proved by mathlib's basis extension. -/
theorem exists_cocycle_realizing_homologyFunctional (K : SSet.{0}) (n : ℕ)
    (L : (ChainDual.simplicialScalarChains (R := F) K).homology n →ₗ[F] F) :
    ∃ c : Representatives.cochainCocycles (Basic.simplicialCochains K (ModuleCat.of F F)) n,
      ∀ z : ChainRepresentatives.chainCycles (ChainDual.simplicialScalarChains (R := F) K) n,
        ChainDual.degreewiseChainDualEquiv K (ModuleCat.of F F) n c.val z.val =
          L (ChainRepresentatives.chainClass (ChainDual.simplicialScalarChains (R := F) K) n z) := by
  let C := ChainDual.simplicialScalarChains (R := F) K
  let D := Basic.simplicialCochains K (ModuleCat.of F F)
  obtain ⟨φ, hφ⟩ := (L.comp (ChainRepresentatives.chainClass C n)).exists_extend
  let c : D.X n := (ChainDual.degreewiseChainDualEquiv K (ModuleCat.of F F) n).symm φ
  have hbound : φ.comp (C.sc n).f.hom = 0 := by
    ext z
    have hz := LinearMap.congr_fun hφ (ChainRepresentatives.chainBoundaryMap C n z)
    change φ ((C.sc n).f z) = L (ChainRepresentatives.chainClass C n (ChainRepresentatives.chainBoundaryMap C n z)) at hz
    rw [ChainRepresentatives.chainClass_boundary, map_zero] at hz
    change φ ((C.sc n).f z) = 0
    exact hz
  have hc : c ∈ Representatives.cochainCocycles D n := by
    change (D.d n ((ComplexShape.up ℕ).next n)) c = 0
    apply (ChainDual.degreewiseChainDualEquiv K (ModuleCat.of F F) ((ComplexShape.up ℕ).next n)).injective
    rw [ChainDual.degreewiseChainDualEquiv_d, map_zero]
    have he : ChainDual.degreewiseChainDualEquiv K (ModuleCat.of F F) n c = φ :=
      (ChainDual.degreewiseChainDualEquiv K (ModuleCat.of F F) n).apply_symm_apply φ
    rw [he]
    exact hbound
  refine ⟨⟨c, hc⟩, fun z => ?_⟩
  have hz := LinearMap.congr_fun hφ z
  simpa only [c, LinearEquiv.apply_symm_apply, LinearMap.comp_apply,
    Submodule.subtype_apply] using hz

/-- Over a field, two cohomology classes are equal whenever their canonical
evaluations on all homology classes agree. -/
theorem simplicialHomologyEvaluation_injective (K : SSet.{0}) (n : ℕ) :
    Function.Injective (Evaluation.simplicialHomologyEvaluation K (ModuleCat.of F F) n) := by
  intro a b hab
  let C := ChainDual.simplicialScalarChains (R := F) K
  let D := Basic.simplicialCochains K (ModuleCat.of F F)
  have hzero : Evaluation.simplicialHomologyEvaluation K (ModuleCat.of F F) n (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  obtain ⟨c, hc⟩ := Representatives.cochainClass_surjective D n (a - b)
  have hc0 : Representatives.cochainClass D n c = 0 := by
    apply cochainClass_eq_zero_of_vanishesOnCycles K n c
    intro z
    have hz : Evaluation.simplicialHomologyEvaluation K (ModuleCat.of F F) n
        (Representatives.cochainClass D n c) (ChainRepresentatives.chainClass C n z) = 0 := by
      rw [hc, hzero]
      rfl
    exact (Evaluation.simplicialHomologyEvaluation_class_class K (ModuleCat.of F F) n c z).symm.trans hz
  exact sub_eq_zero.mp (hc.symm.trans hc0)

/-- Every scalar-linear functional on homology is canonical evaluation by a
cohomology class when the coefficient ring is a field. -/
theorem simplicialHomologyEvaluation_surjective (K : SSet.{0}) (n : ℕ) :
    Function.Surjective (Evaluation.simplicialHomologyEvaluation K (ModuleCat.of F F) n) := by
  intro L
  obtain ⟨c, hc⟩ := exists_cocycle_realizing_homologyFunctional K n L
  refine ⟨Representatives.cochainClass (Basic.simplicialCochains K (ModuleCat.of F F)) n c, ?_⟩
  ext h
  obtain ⟨z, rfl⟩ := ChainRepresentatives.chainClass_surjective (ChainDual.simplicialScalarChains (R := F) K) n h
  rw [Evaluation.simplicialHomologyEvaluation_class_class]
  exact hc z

/-- The field universal-coefficient isomorphism for the actual simplicial chain
and cochain complexes, with the canonical evaluation map as its forward map. -/
def simplicialUniversalCoefficientEquiv (K : SSet.{0}) (n : ℕ) :
    (Basic.simplicialCochains K (ModuleCat.of F F)).homology n ≃ₗ[F]
      Module.Dual F ((ChainDual.simplicialScalarChains (R := F) K).homology n) :=
  LinearEquiv.ofBijective (Evaluation.simplicialHomologyEvaluation K (ModuleCat.of F F) n)
    ⟨simplicialHomologyEvaluation_injective K n,
      simplicialHomologyEvaluation_surjective K n⟩

@[simp]
theorem simplicialUniversalCoefficientEquiv_apply (K : SSet.{0}) (n : ℕ)
    (c : (Basic.simplicialCochains K (ModuleCat.of F F)).homology n) :
    simplicialUniversalCoefficientEquiv K n c =
      Evaluation.simplicialHomologyEvaluation K (ModuleCat.of F F) n c := rfl

/-- Canonical universal-coefficient duality for genuine singular cohomology and
homology over an arbitrary field, in every nonnegative degree. -/
def singularUniversalCoefficientEquiv (X : TopCat.{0}) (n : ℕ) :
    Basic.singularCohomology (ModuleCat.of F F) X n ≃ₗ[F]
      Module.Dual F ((Evaluation.singularScalarChains (R := F) X).homology n) :=
  simplicialUniversalCoefficientEquiv (TopCat.toSSet.obj X) n

@[simp]
theorem singularUniversalCoefficientEquiv_apply (X : TopCat.{0}) (n : ℕ)
    (c : Basic.singularCohomology (ModuleCat.of F F) X n) :
    singularUniversalCoefficientEquiv X n c =
      Evaluation.singularEvaluation (ModuleCat.of F F) X n c := rfl

end

end OAI.AlgebraicTopology.Cohomology.Singular.UniversalCoefficient
end ComponentSource_12

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicTopology.Cohomology.Singular.UniversalCoefficient"

@[expose] public section ComponentSource_13
/- Original module: OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality -/

/-! # Evaluation Naturality -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality

noncomputable section

/-!
# Naturality of the canonical singular evaluation pairing

The chain maps below are mathlib's actual simplicial and singular chain maps.
Evaluation commutes with pullback in cohomology, pushforward in homology, and
maps of coefficient modules. The field universal-coefficient isomorphism has
the same naturality because its forward map is this canonical evaluation.
-/

open _root_.CategoryTheory
open scoped Simplicial

variable {R : Type} [CommRing R]
variable {C D : ChainComplex (ModuleCat.{0} R) ℕ}

/-- Restriction of an actual chain map to the cycle submodules. -/
def chainCycleMap (f : C ⟶ D) (n : ℕ) : ChainRepresentatives.chainCycles C n →ₗ[R] ChainRepresentatives.chainCycles D n :=
  ((f.f n).hom.comp (ChainRepresentatives.chainCycles C n).subtype).codRestrict _ fun z => by
    change (D.d n ((ComplexShape.down ℕ).next n)) ((f.f n) (z : C.X n)) = 0
    have h := ConcreteCategory.congr_hom (f.comm n ((ComplexShape.down ℕ).next n))
      (z : C.X n)
    simpa only [ConcreteCategory.comp_apply,
      ChainRepresentatives.chainCycle_d_eq_zero C n ((ComplexShape.down ℕ).next n) z, map_zero] using h

@[simp]
theorem chainCycleMap_val (f : C ⟶ D) (n : ℕ) (z : ChainRepresentatives.chainCycles C n) :
    (chainCycleMap f n z : D.X n) = (f.f n) (z : C.X n) := rfl

/-- The concrete cycle map is the categorical cycle map in concrete coordinates. -/
theorem chainCycleMap_eq_cyclesMap (f : C ⟶ D) (n : ℕ) (z : ChainRepresentatives.chainCycles C n) :
    (D.sc n).moduleCatCyclesIso.inv (chainCycleMap f n z) =
      (HomologicalComplex.cyclesMap f n) ((C.sc n).moduleCatCyclesIso.inv z) := by
  apply (ModuleCat.mono_iff_injective (D.iCycles n)).mp inferInstance
  have hD := ConcreteCategory.congr_hom ((D.sc n).moduleCatCyclesIso_inv_iCycles)
    (chainCycleMap f n z)
  have hC := ConcreteCategory.congr_hom ((C.sc n).moduleCatCyclesIso_inv_iCycles) z
  have hf := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i f n)
    ((C.sc n).moduleCatCyclesIso.inv z)
  change (D.iCycles n) ((D.sc n).moduleCatCyclesIso.inv (chainCycleMap f n z)) =
    (f.f n) (z : C.X n) at hD
  change (C.iCycles n) ((C.sc n).moduleCatCyclesIso.inv z) = (z : C.X n) at hC
  change (D.iCycles n) ((HomologicalComplex.cyclesMap f n)
    ((C.sc n).moduleCatCyclesIso.inv z)) =
      (f.f n) ((C.iCycles n) ((C.sc n).moduleCatCyclesIso.inv z)) at hf
  rw [hC] at hf
  exact hD.trans hf.symm

/-- An actual chain map sends a represented homology class to the image cycle's class. -/
theorem chainClass_naturality (f : C ⟶ D) (n : ℕ) (z : ChainRepresentatives.chainCycles C n) :
    (HomologicalComplex.homologyMap f n) (ChainRepresentatives.chainClass C n z) =
      ChainRepresentatives.chainClass D n (chainCycleMap f n z) := by
  rw [ChainRepresentatives.chainClass_eq_homologyπ, ChainRepresentatives.chainClass_eq_homologyπ, chainCycleMap_eq_cyclesMap]
  exact ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality f n)
    ((C.sc n).moduleCatCyclesIso.inv z)

/-- A chain map sends a boundary representative to the boundary of its image. -/
theorem chainCycleMap_boundary (f : C ⟶ D) (n : ℕ) (z : (C.sc n).X₁) :
    chainCycleMap f n (ChainRepresentatives.chainBoundaryMap C n z) =
      ChainRepresentatives.chainBoundaryMap D n ((f.f ((ComplexShape.down ℕ).prev n)) z) := by
  apply Subtype.ext
  exact (ConcreteCategory.congr_hom (f.comm ((ComplexShape.down ℕ).prev n) n) z).symm

/-- The actual scalar chain map of a morphism of simplicial sets. -/
abbrev simplicialScalarChainMap {K L : SSet.{0}} (f : K ⟶ L) :
    ChainDual.simplicialScalarChains (R := R) K ⟶ ChainDual.simplicialScalarChains (R := R) L :=
  SSet.chainComplexMap f (ModuleCat.of R R)

/-- The actual pushforward on scalar simplicial homology. -/
abbrev simplicialHomologyPushforward {K L : SSet.{0}} (f : K ⟶ L) (n : ℕ) :
    (ChainDual.simplicialScalarChains (R := R) K).homology n ⟶
      (ChainDual.simplicialScalarChains (R := R) L).homology n :=
  HomologicalComplex.homologyMap (simplicialScalarChainMap (R := R) f) n

@[simp]
theorem simplicialScalarChainMap_simplex {K L : SSet.{0}} (f : K ⟶ L)
    {n : ℕ} (s : K _⦋n⦌) :
    (simplicialScalarChainMap (R := R) f).f n (ChainDual.simplexChain K s) =
      ChainDual.simplexChain L (f.app _ s) :=
  ConcreteCategory.congr_hom
    (SSet.ι_chainComplexMap_f (X := K) (Y := L) (R := ModuleCat.of R R) f s) 1

/-- Pullback of an actual cochain is precomposition with the actual scalar chain map. -/
theorem degreewiseChainDualEquiv_pullback (M : ModuleCat.{0} R)
    {K L : SSet.{0}} (f : K ⟶ L) (n : ℕ) (c : (Basic.simplicialCochains L M).X n) :
    ChainDual.degreewiseChainDualEquiv K M n ((Functor.simplicialPullback M f).f n c) =
      (ChainDual.degreewiseChainDualEquiv L M n c).comp
        ((simplicialScalarChainMap (R := R) f).f n).hom := by
  apply ChainDual.chainFunctional_ext K M
  intro s
  simp only [ChainDual.degreewiseChainDualEquiv_simplex, LinearMap.comp_apply,
    simplicialScalarChainMap_simplex, Formulas.evaluation_pullback_apply]

/-- The canonical simplicial pairing is natural in the underlying simplicial set. -/
theorem simplicialHomologyEvaluation_naturality (M : ModuleCat.{0} R)
    {K L : SSet.{0}} (f : K ⟶ L) (n : ℕ)
    (c : (Basic.simplicialCochains L M).homology n)
    (z : (ChainDual.simplicialScalarChains (R := R) K).homology n) :
    Evaluation.simplicialHomologyEvaluation K M n
        ((HomologicalComplex.homologyMap (Functor.simplicialPullback M f) n) c) z =
      Evaluation.simplicialHomologyEvaluation L M n c
        (simplicialHomologyPushforward (R := R) f n z) := by
  obtain ⟨c, rfl⟩ := Representatives.cochainClass_surjective (Basic.simplicialCochains L M) n c
  obtain ⟨z, rfl⟩ := ChainRepresentatives.chainClass_surjective (ChainDual.simplicialScalarChains (R := R) K) n z
  rw [RepresentativesNaturality.cochainClass_naturality, chainClass_naturality,
    Evaluation.simplicialHomologyEvaluation_class_class, Evaluation.simplicialHomologyEvaluation_class_class]
  exact LinearMap.congr_fun (degreewiseChainDualEquiv_pullback M f n c.val) z.val

/-- The actual scalar singular chain map of a continuous map. -/
abbrev singularScalarChainMap {X Y : TopCat.{0}} (f : X ⟶ Y) :
    Evaluation.singularScalarChains (R := R) X ⟶ Evaluation.singularScalarChains (R := R) Y :=
  simplicialScalarChainMap (R := R) (TopCat.toSSet.map f)

/-- Pushforward of actual scalar singular homology classes. -/
abbrev singularHomologyPushforward {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    (Evaluation.singularScalarChains (R := R) X).homology n ⟶
      (Evaluation.singularScalarChains (R := R) Y).homology n :=
  simplicialHomologyPushforward (R := R) (TopCat.toSSet.map f) n

/-- The chain representative formula for continuous pushforward in homology. -/
theorem singularHomologyPushforward_class {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (z : ChainRepresentatives.chainCycles (Evaluation.singularScalarChains (R := R) X) n) :
    singularHomologyPushforward (R := R) f n (ChainRepresentatives.chainClass (Evaluation.singularScalarChains X) n z) =
      ChainRepresentatives.chainClass (Evaluation.singularScalarChains Y) n
        (chainCycleMap (singularScalarChainMap (R := R) f) n z) :=
  chainClass_naturality (singularScalarChainMap (R := R) f) n z

/-- Pullback in singular cohomology is adjoint to continuous pushforward in homology. -/
theorem singularEvaluation_naturality (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (c : Basic.singularCohomology M Y n) (z : (Evaluation.singularScalarChains (R := R) X).homology n) :
    Evaluation.singularEvaluation M X n ((Functor.singularCohomologyPullback M f n) c) z =
      Evaluation.singularEvaluation M Y n c (singularHomologyPushforward (R := R) f n z) :=
  simplicialHomologyEvaluation_naturality M (TopCat.toSSet.map f) n c z

/-- On singular cochains, changing coefficients postcomposes the chain functional. -/
theorem singularDegreewiseChainDualEquiv_coefficient {M N : ModuleCat.{0} R}
    (f : M ⟶ N) (X : TopCat.{0}) (n : ℕ) (c : (Basic.singularCochains M X).X n) :
    ChainDual.singularDegreewiseChainDualEquiv N X n ((Coefficients.coefficientCochainMap f X).f n c) =
      f.hom.comp (ChainDual.singularDegreewiseChainDualEquiv M X n c) := by
  apply ChainDual.chainFunctional_ext (TopCat.toSSet.obj X) N
  intro s
  change ChainDual.degreewiseChainDualEquiv (TopCat.toSSet.obj X) N n
      ((Coefficients.coefficientCochainMap f X).f n c) (ChainDual.simplexChain (TopCat.toSSet.obj X) s) =
    f (ChainDual.degreewiseChainDualEquiv (TopCat.toSSet.obj X) M n c
      (ChainDual.simplexChain (TopCat.toSSet.obj X) s))
  rw [ChainDual.degreewiseChainDualEquiv_simplex, ChainDual.degreewiseChainDualEquiv_simplex]
  exact ConcreteCategory.congr_hom (Coefficients.coefficientCochainMap_evaluation f X s) c

/-- The canonical singular pairing is natural in its coefficient module. -/
theorem singularEvaluation_coefficient {M N : ModuleCat.{0} R}
    (f : M ⟶ N) (X : TopCat.{0}) (n : ℕ)
    (c : Basic.singularCohomology M X n) (z : (Evaluation.singularScalarChains (R := R) X).homology n) :
    Evaluation.singularEvaluation N X n ((Coefficients.coefficientMap f X n) c) z =
      f (Evaluation.singularEvaluation M X n c z) := by
  obtain ⟨c, rfl⟩ := Representatives.singularClass_surjective M X n c
  obtain ⟨z, rfl⟩ := ChainRepresentatives.chainClass_surjective (Evaluation.singularScalarChains (R := R) X) n z
  rw [RepresentativesNaturality.coefficientMap_class, Evaluation.singularEvaluation_class_class, Evaluation.singularEvaluation_class_class]
  exact LinearMap.congr_fun (singularDegreewiseChainDualEquiv_coefficient f X n c.val) z.val

variable {F : Type} [Field F]

/-- The field universal-coefficient identification is contravariantly natural. -/
theorem singularUniversalCoefficientEquiv_naturality {X Y : TopCat.{0}}
    (f : X ⟶ Y) (n : ℕ) (c : Basic.singularCohomology (ModuleCat.of F F) Y n) :
    UniversalCoefficient.singularUniversalCoefficientEquiv X n
        ((Functor.singularCohomologyPullback (ModuleCat.of F F) f n) c) =
      (UniversalCoefficient.singularUniversalCoefficientEquiv Y n c).comp
        (singularHomologyPushforward (R := F) f n).hom := by
  ext z
  simp only [UniversalCoefficient.singularUniversalCoefficientEquiv_apply, LinearMap.comp_apply]
  exact singularEvaluation_naturality (ModuleCat.of F F) f n c z

end

end OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality
end ComponentSource_13

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality"

@[expose] public section ComponentSource_14
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.EventuallySmall -/

/-! # Eventually Small -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.EventuallySmall.Cycles

noncomputable section

/-!
# An eventual-subdivision criterion for a genuine chain inclusion

Let an injective chain map identify a chain complex with a subcomplex of
another one. Suppose compatible endomorphisms of both complexes are each
chain homotopic to the identity, and every ambient chain eventually enters
the subcomplex under iteration. Then the inclusion is a quasi-isomorphism.

All maps and homotopies in this theorem are actual mathlib chain maps and
homotopies. The theorem does not assume or assert that any unconstructed
geometric subdivision operator satisfies these hypotheses.
-/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality

variable {R : Type} [CommRing R]
variable {C D : ChainComplex (ModuleCat.{0} R) ℕ}

/-- Iteration of an actual chain endomorphism. -/
def iterateChainMap (s : C ⟶ C) : ℕ → (C ⟶ C)
  | 0 => 𝟙 C
  | N + 1 => iterateChainMap s N ≫ s

@[simp]
theorem iterateChainMap_apply (s : C ⟶ C) (N n : ℕ) (x : C.X n) :
    ((Cycles.iterateChainMap s N).f n) x = ((s.f n)^[N]) x := by
  induction N with
  | zero => rfl
  | succ N ih =>
    change (s.f n) (((Cycles.iterateChainMap s N).f n) x) = ((s.f n)^[N + 1]) x
    rw [ih, Function.iterate_succ_apply']

/-- A compatible chain inclusion commutes with all iterates. -/
theorem iterateChainMap_commute (i : C ⟶ D) (sC : C ⟶ C) (sD : D ⟶ D)
    (h : i ≫ sD = sC ≫ i) (N : ℕ) :
    i ≫ Cycles.iterateChainMap sD N = Cycles.iterateChainMap sC N ≫ i := by
  induction N with
  | zero => simp [Cycles.iterateChainMap]
  | succ N ih =>
    calc
      i ≫ Cycles.iterateChainMap sD (N + 1) = (i ≫ Cycles.iterateChainMap sD N) ≫ sD := by
        simp only [Cycles.iterateChainMap, Category.assoc]
      _ = (Cycles.iterateChainMap sC N ≫ i) ≫ sD := by rw [ih]
      _ = Cycles.iterateChainMap sC N ≫ (i ≫ sD) := Category.assoc _ _ _
      _ = Cycles.iterateChainMap sC N ≫ (sC ≫ i) := by rw [h]
      _ = Cycles.iterateChainMap sC (N + 1) ≫ i := by
        simp only [Cycles.iterateChainMap, Category.assoc]

/-- Iterating an endomorphism homotopic to the identity still acts as the
identity on genuine homology. -/
theorem iterateChainMap_homologyMap (s : C ⟶ C) (h : _root_.Homotopy s (𝟙 C))
    (N n : ℕ) :
    HomologicalComplex.homologyMap (Cycles.iterateChainMap s N) n = 𝟙 (C.homology n) := by
  have hs : HomologicalComplex.homologyMap s n = 𝟙 (C.homology n) := by
    simpa using h.homologyMap_eq n
  induction N with
  | zero => simp [Cycles.iterateChainMap]
  | succ N ih =>
    simp only [Cycles.iterateChainMap, HomologicalComplex.homologyMap_comp, ih, hs,
      Category.id_comp]

/-- A represented cycle retains its class under every iterate. -/
theorem iterateChainMap_class (s : C ⟶ C) (h : _root_.Homotopy s (𝟙 C))
    (N n : ℕ) (z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles C n) :
    AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass C n (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (Cycles.iterateChainMap s N) n z) = AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass C n z := by
  rw [← AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality, iterateChainMap_homologyMap s h N n]
  rfl

/-- Injectivity of a chain inclusion lets one recognize a cycle in the
subcomplex from its image in the ambient complex. -/
theorem chainMap_preimage_isCycle (i : C ⟶ D)
    (hi : ∀ n, Function.Injective (i.f n)) (n : ℕ) (x : C.X n)
    (hx : (i.f n) x ∈ AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles D n) : x ∈ AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles C n := by
  change (D.d n ((ComplexShape.down ℕ).next n)) ((i.f n) x) = 0 at hx
  change (C.d n ((ComplexShape.down ℕ).next n)) x = 0
  apply hi ((ComplexShape.down ℕ).next n)
  simpa only [map_zero, ConcreteCategory.comp_apply] using
    (ConcreteCategory.congr_hom (i.comm n ((ComplexShape.down ℕ).next n)) x).symm.trans hx

/-- Moving a representative cycle into the subcomplex proves surjectivity on
homology. -/
theorem eventuallySmall_homology_surjective (i : C ⟶ D)
    (hi : ∀ n, Function.Injective (i.f n)) (sD : D ⟶ D)
    (hD : _root_.Homotopy sD (𝟙 D))
    (hevent : ∀ (n : ℕ) (x : D.X n),
      ∃ (N : ℕ) (y : C.X n), (i.f n) y = ((sD.f n)^[N]) x)
    (n : ℕ) : Function.Surjective (HomologicalComplex.homologyMap i n) := by
  intro y
  obtain ⟨z, rfl⟩ := AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_surjective D n y
  obtain ⟨N, x, hx⟩ := hevent n (z : D.X n)
  have hx' : (i.f n) x = ((Cycles.iterateChainMap sD N).f n) (z : D.X n) := by
    rw [iterateChainMap_apply]
    exact hx
  have hxc : x ∈ AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles C n := chainMap_preimage_isCycle i hi n x (by
    rw [hx']
    exact (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (Cycles.iterateChainMap sD N) n z).property)
  refine ⟨AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass C n ⟨x, hxc⟩, ?_⟩
  rw [AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality]
  have heq : AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap i n ⟨x, hxc⟩ = AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (Cycles.iterateChainMap sD N) n z :=
    Subtype.ext hx'
  rw [heq]
  exact iterateChainMap_class sD hD N n z

/-- Moving an ambient bounding chain into the subcomplex, and using the
restricted homotopy, proves injectivity on homology. -/
theorem eventuallySmall_homology_injective (i : C ⟶ D)
    (hi : ∀ n, Function.Injective (i.f n)) (sC : C ⟶ C) (sD : D ⟶ D)
    (hcomm : i ≫ sD = sC ≫ i) (hC : _root_.Homotopy sC (𝟙 C))
    (hevent : ∀ (n : ℕ) (x : D.X n),
      ∃ (N : ℕ) (y : C.X n), (i.f n) y = ((sD.f n)^[N]) x)
    (n : ℕ) : Function.Injective (HomologicalComplex.homologyMap i n) := by
  change Function.Injective (HomologicalComplex.homologyMap i n).hom
  apply (injective_iff_map_eq_zero (HomologicalComplex.homologyMap i n).hom).mpr
  intro y hy
  obtain ⟨z, rfl⟩ := AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_surjective C n y
  change (HomologicalComplex.homologyMap i n) (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass C n z) = 0 at hy
  rw [AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality] at hy
  obtain ⟨b, hb⟩ := (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_eq_zero_iff_exists D n (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap i n z)).mp hy
  change (D.d (n + 1) n) b = (i.f n) (z : C.X n) at hb
  obtain ⟨N, w, hw⟩ := hevent (n + 1) b
  have hw' : (i.f (n + 1)) w = ((Cycles.iterateChainMap sD N).f (n + 1)) b := by
    rw [iterateChainMap_apply]
    exact hw
  have hc := congrArg (fun f : C ⟶ D => (f.f n) (z : C.X n))
    (iterateChainMap_commute i sC sD hcomm N)
  change ((Cycles.iterateChainMap sD N).f n) ((i.f n) (z : C.X n)) =
    (i.f n) (((Cycles.iterateChainMap sC N).f n) (z : C.X n)) at hc
  have hbound : (C.d (n + 1) n) w =
      ((Cycles.iterateChainMap sC N).f n) (z : C.X n) := by
    apply hi n
    calc
      (i.f n) ((C.d (n + 1) n) w) = (D.d (n + 1) n) ((i.f (n + 1)) w) :=
        by simpa only [ConcreteCategory.comp_apply] using
          (ConcreteCategory.congr_hom (i.comm (n + 1) n) w).symm
      _ = (D.d (n + 1) n) (((Cycles.iterateChainMap sD N).f (n + 1)) b) := by rw [hw']
      _ = ((Cycles.iterateChainMap sD N).f n) ((D.d (n + 1) n) b) :=
        by simpa only [ConcreteCategory.comp_apply] using
          ConcreteCategory.congr_hom ((Cycles.iterateChainMap sD N).comm (n + 1) n) b
      _ = ((Cycles.iterateChainMap sD N).f n) ((i.f n) (z : C.X n)) := by rw [hb]
      _ = (i.f n) (((Cycles.iterateChainMap sC N).f n) (z : C.X n)) := hc
  have hzN : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass C n (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (Cycles.iterateChainMap sC N) n z) = 0 :=
    (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_eq_zero_iff_exists C n _).mpr ⟨w, hbound⟩
  rw [iterateChainMap_class sC hC N n z] at hzN
  exact hzN

/-- A genuine chain inclusion is a quasi-isomorphism when compatible
endomorphisms, chain homotopic to the identity on both complexes, eventually
move every ambient chain into its image. -/
theorem quasiIso_of_eventuallySmall (i : C ⟶ D)
    (hi : ∀ n, Function.Injective (i.f n)) (sC : C ⟶ C) (sD : D ⟶ D)
    (hcomm : i ≫ sD = sC ≫ i)
    (hC : _root_.Homotopy sC (𝟙 C)) (hD : _root_.Homotopy sD (𝟙 D))
    (hevent : ∀ (n : ℕ) (x : D.X n),
      ∃ (N : ℕ) (y : C.X n), (i.f n) y = ((sD.f n)^[N]) x) :
    _root_.QuasiIso i := by
  apply (quasiIso_iff i).mpr
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap,
    ConcreteCategory.isIso_iff_bijective]
  exact ⟨eventuallySmall_homology_injective i hi sC sD hcomm hC hevent n,
    eventuallySmall_homology_surjective i hi sD hD hevent n⟩

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.EventuallySmall.Cycles
end ComponentSource_14

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.EventuallySmall"

@[expose] public section ComponentSource_15
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.InjectiveHomotopyRestriction -/

/-! # Injective Homotopy Restriction -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.InjectiveHomotopyRestriction.Cycles

noncomputable section

/-!
# Restricting an actual homotopy through an injective chain map

When the components of a given homotopy preserve the image of a degreewise
injective chain map, they have unique restrictions. The homotopy identity for
those restrictions follows by applying the injection. This construction does
not assume a homotopy on the smaller complex.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w

variable {R : Type u} [CommRing R] {ι : Type v} {c : ComplexShape ι}
  {C D : HomologicalComplex (ModuleCat.{w} R) c}
  {fD gD : D ⟶ D}

/-- The unique restriction of one actual homotopy component through an
injective chain map whose image it preserves. -/
def restrictedHomotopyComponent (i : C ⟶ D)
    (hi : ∀ n, Function.Injective (i.f n)) (h : Homotopy fD gD)
    (hmem : ∀ a b (x : C.X a), h.hom a b (i.f a x) ∈ LinearMap.range (i.f b).hom)
    (a b : ι) : C.X a ⟶ C.X b :=
  ModuleCat.ofHom (LinearMap.codRestrictOfInjective
    ((h.hom a b).hom.comp (i.f a).hom) (i.f b).hom (hi b) (hmem a b))

/-- Inclusion recovers the given ambient component exactly. -/
@[simp]
theorem restrictedHomotopyComponent_apply (i : C ⟶ D)
    (hi : ∀ n, Function.Injective (i.f n)) (h : Homotopy fD gD)
    (hmem : ∀ a b (x : C.X a), h.hom a b (i.f a x) ∈ LinearMap.range (i.f b).hom)
    (a b : ι) (x : C.X a) :
    i.f b (restrictedHomotopyComponent i hi h hmem a b x) = h.hom a b (i.f a x) := by
  simp [restrictedHomotopyComponent]

/-- Categorical component compatibility for the restriction. -/
@[reassoc]
theorem restrictedHomotopyComponent_comp (i : C ⟶ D)
    (hi : ∀ n, Function.Injective (i.f n)) (h : Homotopy fD gD)
    (hmem : ∀ a b (x : C.X a), h.hom a b (i.f a x) ∈ LinearMap.range (i.f b).hom)
    (a b : ι) :
    restrictedHomotopyComponent i hi h hmem a b ≫ i.f b = i.f a ≫ h.hom a b := by
  apply ModuleCat.hom_ext
  ext x
  exact restrictedHomotopyComponent_apply i hi h hmem a b x

/-- Restrict an existing chain homotopy to a degreewise injective subcomplex.
The two endpoint chain maps must be intertwined by the same inclusion. -/
def restrictHomotopy {fC gC : C ⟶ C} (i : C ⟶ D)
    (hi : ∀ n, Function.Injective (i.f n))
    (hf : i ≫ fD = fC ≫ i) (hg : i ≫ gD = gC ≫ i)
    (h : Homotopy fD gD)
    (hmem : ∀ a b (x : C.X a), h.hom a b (i.f a x) ∈ LinearMap.range (i.f b).hom) :
    Homotopy fC gC := by
  let K := restrictedHomotopyComponent i hi h hmem
  have hK (a b : ι) : K a b ≫ i.f b = i.f a ≫ h.hom a b :=
    restrictedHomotopyComponent_comp i hi h hmem a b
  refine { hom := K, zero := ?_, comm := ?_ }
  · intro a b hab
    let : Mono (i.f b) := (ModuleCat.mono_iff_injective _).2 (hi b)
    apply (cancel_mono (i.f b)).1
    rw [hK, h.zero a b hab, comp_zero, zero_comp]
  · intro n
    let : Mono (i.f n) := (ModuleCat.mono_iff_injective _).2 (hi n)
    apply (cancel_mono (i.f n)).1
    have hf' : i.f n ≫ fD.f n = fC.f n ≫ i.f n :=
      HomologicalComplex.congr_hom hf n
    have hg' : i.f n ≫ gD.f n = gC.f n ≫ i.f n :=
      HomologicalComplex.congr_hom hg n
    have hd : dNext n K ≫ i.f n = i.f n ≫ dNext n h.hom := by
      calc
        dNext n K ≫ i.f n = dNext n (fun a b => K a b ≫ i.f b) :=
          (dNext_comp_right K i n).symm
        _ = dNext n (fun a b => i.f a ≫ h.hom a b) := by simp only [hK]
        _ = i.f n ≫ dNext n h.hom := dNext_comp_left i h.hom n
    have hp : prevD n K ≫ i.f n = i.f n ≫ prevD n h.hom := by
      calc
        prevD n K ≫ i.f n = prevD n (fun a b => K a b ≫ i.f b) :=
          (prevD_comp_right K i n).symm
        _ = prevD n (fun a b => i.f a ≫ h.hom a b) := by simp only [hK]
        _ = i.f n ≫ prevD n h.hom := prevD_comp_left i h.hom n
    calc
      fC.f n ≫ i.f n = i.f n ≫ fD.f n := hf'.symm
      _ = i.f n ≫ (dNext n h.hom + prevD n h.hom + gD.f n) := by rw [h.comm n]
      _ = (dNext n K + prevD n K + gC.f n) ≫ i.f n := by
        simp only [Preadditive.comp_add, Preadditive.add_comp]
        rw [hd, hp, hg']

/-- The resulting homotopy has exactly the constructed restricted components. -/
theorem restrictHomotopy_hom {fC gC : C ⟶ C} (i : C ⟶ D)
    (hi : ∀ n, Function.Injective (i.f n))
    (hf : i ≫ fD = fC ≫ i) (hg : i ≫ gD = gC ≫ i)
    (h : Homotopy fD gD)
    (hmem : ∀ a b (x : C.X a), h.hom a b (i.f a x) ∈ LinearMap.range (i.f b).hom)
    (a b : ι) :
    (restrictHomotopy i hi hf hg h hmem).hom a b =
      restrictedHomotopyComponent i hi h hmem a b := rfl

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.InjectiveHomotopyRestriction.Cycles
end ComponentSource_15

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.InjectiveHomotopyRestriction"

@[expose] public section ComponentSource_16
/- Original module: OAI.AlgebraicTopology.Cohomology.Singular.ContinuousFormulas -/

/-! # Continuous Formulas -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.ContinuousFormulas

noncomputable section

/-!
# Singular cochain formulas on continuous maps from standard simplices

This file expresses the previously proved simplicial formulas in the actual
function module `C(Convexity.StdSimplex ℝ (Fin (n + 1)), X) → M`. The coefficient-valued
functions are arbitrary; continuity is required of the singular simplices.
The faces are the usual inclusions omitting one barycentric coordinate.
-/

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

open _root_.CategoryTheory Opposite
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The standard simplex face that omits barycentric coordinate `i`. -/
def standardSimplexFace {n : ℕ} (i : Fin (n + 2)) :
    C(Convexity.StdSimplex ℝ (Fin (n + 1)), Convexity.StdSimplex ℝ (Fin (n + 2))) :=
  ⟨Convexity.StdSimplex.map i.succAbove, Convexity.StdSimplex.continuous_map ℝ i.succAbove⟩

/-- The face map is the actual map of topological standard simplices. -/
theorem standardSimplexFace_apply {n : ℕ} (i : Fin (n + 2))
    (z : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    standardSimplexFace i z = Convexity.StdSimplex.map i.succAbove z := rfl

/-- A face in the singular simplicial set is precomposition with its face inclusion. -/
theorem singularSimplicesEquivContinuousMap_face (X : TopCat.{0}) {n : ℕ}
    (s : Basic.singularSimplices X (n + 1)) (i : Fin (n + 2)) :
    Coefficients.singularSimplicesEquivContinuousMap X n ((TopCat.toSSet.obj X).δ i s) =
      (Coefficients.singularSimplicesEquivContinuousMap X (n + 1) s).comp (standardSimplexFace i) := by
  ext z
  exact TopCat.toSSetObjEquiv_δ_apply s i z

/-- The continuous-map-to-simplex identification also respects each face inclusion. -/
theorem singularSimplicesEquivContinuousMap_symm_face (X : TopCat.{0}) {n : ℕ}
    (s : C(Convexity.StdSimplex ℝ (Fin (n + 2)), X)) (i : Fin (n + 2)) :
    (TopCat.toSSet.obj X).δ i ((Coefficients.singularSimplicesEquivContinuousMap X (n + 1)).symm s) =
      (Coefficients.singularSimplicesEquivContinuousMap X n).symm (s.comp (standardSimplexFace i)) := by
  apply (Coefficients.singularSimplicesEquivContinuousMap X n).injective
  rw [singularSimplicesEquivContinuousMap_face, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]

/-- A continuous map of spaces acts on singular simplices by postcomposition. -/
theorem singularSimplicesEquivContinuousMap_map {X Y : TopCat.{0}}
    (f : X ⟶ Y) {n : ℕ} (s : Basic.singularSimplices X n) :
    Coefficients.singularSimplicesEquivContinuousMap Y n ((TopCat.toSSet.map f).app _ s) =
      f.hom.comp (Coefficients.singularSimplicesEquivContinuousMap X n s) := rfl

/-- Postcomposition agrees with the singular simplicial map under the inverse identification. -/
theorem singularSimplicesEquivContinuousMap_symm_map {X Y : TopCat.{0}}
    (f : X ⟶ Y) {n : ℕ} (s : C(Convexity.StdSimplex ℝ (Fin (n + 1)), X)) :
    (TopCat.toSSet.map f).app _ ((Coefficients.singularSimplicesEquivContinuousMap X n).symm s) =
      (Coefficients.singularSimplicesEquivContinuousMap Y n).symm (f.hom.comp s) := by
  apply (Coefficients.singularSimplicesEquivContinuousMap Y n).injective
  rw [singularSimplicesEquivContinuousMap_map, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]

variable {R : Type} [Ring R]

/-- The continuous-simplex function isomorphism evaluates through the inverse simplex equivalence. -/
theorem singularDegreewiseContinuousFunctionIso_hom_apply (M : ModuleCat.{0} R)
    (X : TopCat.{0}) {n : ℕ} (c : (Basic.singularCochains M X).X n)
    (s : C(Convexity.StdSimplex ℝ (Fin (n + 1)), X)) :
    (Coefficients.singularDegreewiseContinuousFunctionIso M X n).hom c s =
      (Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) M n).hom c
        ((Coefficients.singularSimplicesEquivContinuousMap X n).symm s) := rfl

/-- In functions on genuine continuous singular simplices, the differential is the usual
alternating sum of restrictions to the topological simplex faces. -/
theorem singularDegreewiseContinuousFunctionIso_coboundary (M : ModuleCat.{0} R)
    (X : TopCat.{0}) {n : ℕ} (c : (Basic.singularCochains M X).X n)
    (s : C(Convexity.StdSimplex ℝ (Fin (n + 2)), X)) :
    (Coefficients.singularDegreewiseContinuousFunctionIso M X (n + 1)).hom
        ((Basic.singularCochains M X).d n (n + 1) c) s =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.val) •
        (Coefficients.singularDegreewiseContinuousFunctionIso M X n).hom c
          (s.comp (standardSimplexFace i)) := by
  calc
    _ = (Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) M (n + 1)).hom
        ((Basic.singularCochains M X).d n (n + 1) c)
        ((Coefficients.singularSimplicesEquivContinuousMap X (n + 1)).symm s) :=
      singularDegreewiseContinuousFunctionIso_hom_apply M X _ s
    _ = ∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.val) •
        (Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) M n).hom c
          ((TopCat.toSSet.obj X).δ i
            ((Coefficients.singularSimplicesEquivContinuousMap X (n + 1)).symm s)) :=
      Formulas.degreewiseFunctionIso_coboundary (TopCat.toSSet.obj X) M c _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [singularSimplicesEquivContinuousMap_symm_face]
      exact congrArg (fun v : M => ((-1 : ℤ) ^ i.val) • v)
        (singularDegreewiseContinuousFunctionIso_hom_apply M X c
          (s.comp (standardSimplexFace i))).symm

/-- In functions on genuine continuous singular simplices, cochain pullback is
precomposition with postcomposition of simplices by the continuous map of spaces. -/
theorem singularDegreewiseContinuousFunctionIso_pullback (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} (f : X ⟶ Y) {n : ℕ} (c : (Basic.singularCochains M Y).X n)
    (s : C(Convexity.StdSimplex ℝ (Fin (n + 1)), X)) :
    (Coefficients.singularDegreewiseContinuousFunctionIso M X n).hom ((Functor.singularPullback M f).f n c) s =
      (Coefficients.singularDegreewiseContinuousFunctionIso M Y n).hom c (f.hom.comp s) := by
  calc
    _ = (Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj X) M n).hom
        ((Functor.singularPullback M f).f n c) ((Coefficients.singularSimplicesEquivContinuousMap X n).symm s) :=
      singularDegreewiseContinuousFunctionIso_hom_apply M X _ s
    _ = (Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj Y) M n).hom c
        ((TopCat.toSSet.map f).app _ ((Coefficients.singularSimplicesEquivContinuousMap X n).symm s)) :=
      Formulas.degreewiseFunctionIso_pullback M (TopCat.toSSet.map f) c _
    _ = _ := by
      rw [singularSimplicesEquivContinuousMap_symm_map]
      exact (singularDegreewiseContinuousFunctionIso_hom_apply M Y c (f.hom.comp s)).symm

/-- Every function on continuous singular simplices defines a cochain, and its
coboundary is the alternating face sum. No support or regularity restriction is imposed on `φ`. -/
theorem continuousFunction_coboundary (M : ModuleCat.{0} R) (X : TopCat.{0}) {n : ℕ}
    (φ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), X) → M)
    (s : C(Convexity.StdSimplex ℝ (Fin (n + 2)), X)) :
    (Coefficients.singularDegreewiseContinuousFunctionIso M X (n + 1)).hom
        ((Basic.singularCochains M X).d n (n + 1)
          ((Coefficients.singularDegreewiseContinuousFunctionIso M X n).inv φ)) s =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.val) • φ (s.comp (standardSimplexFace i)) := by
  calc
    _ = ∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.val) •
        (Coefficients.singularDegreewiseContinuousFunctionIso M X n).hom
          ((Coefficients.singularDegreewiseContinuousFunctionIso M X n).inv φ)
          (s.comp (standardSimplexFace i)) :=
      singularDegreewiseContinuousFunctionIso_coboundary M X _ s
    _ = _ := congrArg
      (fun ψ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), X) → M =>
        ∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.val) • ψ (s.comp (standardSimplexFace i)))
      (ModuleCat.hom_inv_apply (Coefficients.singularDegreewiseContinuousFunctionIso M X n) φ)

/-- Pullback of the cochain defined by any function on continuous singular simplices
is precomposition by postcomposition of the simplices. -/
theorem continuousFunction_pullback (M : ModuleCat.{0} R) {X Y : TopCat.{0}}
    (f : X ⟶ Y) {n : ℕ} (φ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), Y) → M)
    (s : C(Convexity.StdSimplex ℝ (Fin (n + 1)), X)) :
    (Coefficients.singularDegreewiseContinuousFunctionIso M X n).hom
        ((Functor.singularPullback M f).f n
          ((Coefficients.singularDegreewiseContinuousFunctionIso M Y n).inv φ)) s =
      φ (f.hom.comp s) := by
  calc
    _ = (Coefficients.singularDegreewiseContinuousFunctionIso M Y n).hom
        ((Coefficients.singularDegreewiseContinuousFunctionIso M Y n).inv φ) (f.hom.comp s) :=
      singularDegreewiseContinuousFunctionIso_pullback M f _ s
    _ = _ := congrFun
      (ModuleCat.hom_inv_apply (Coefficients.singularDegreewiseContinuousFunctionIso M Y n) φ) _

end

end OAI.AlgebraicTopology.Cohomology.Singular.ContinuousFormulas
end ComponentSource_16

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicTopology.Cohomology.Singular.ContinuousFormulas"

@[expose] public section ComponentSource_17
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.SubdivisionSigns -/

/-! # Subdivision Signs -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.SubdivisionSigns.Cycles

noncomputable section

/-!
# Interior face cancellation in geometric barycentric subdivision

Adjacent positions in a vertex permutation give the same face after deleting
the intermediate barycenter. Their permutation signs are opposite.
-/

open scoped BigOperators Classical

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

/-- A signed permutation sum cancels when its values are invariant under a fixed
right adjacent swap (or, more generally, any fixed transposition). -/
theorem sum_perm_sign_eq_zero_of_swap_invariant
    {ι M : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup M]
    (a b : ι) (hab : a ≠ b) (f : Equiv.Perm ι → M)
    (hf : ∀ σ, f (σ * Equiv.swap a b) = f σ) :
    ∑ σ : Equiv.Perm ι, (Equiv.Perm.sign σ : ℤ) • f σ = 0 := by
  apply Finset.sum_involution (fun σ _ => σ * Equiv.swap a b)
  · intro σ _
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab, hf σ]
    simp
  · intro σ _ _ h
    have hx := congrArg (fun τ : Equiv.Perm ι => τ a) h
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left] at hx
    exact hab (σ.injective hx).symm
  · intro σ _
    exact Finset.mem_univ _
  · intro σ _
    ext x
    simp

/-- Swapping adjacent positions preserves every initial interval except the
one ending at the first of the two positions. -/
theorem adjacent_swap_le_iff {n : ℕ} (j : Fin (n + 1))
    (k x : Fin (n + 2)) (hk : k ≠ j.castSucc) :
    Equiv.swap j.castSucc j.succ x ≤ k ↔ x ≤ k := by
  have hkval : k.val ≠ j.val := by
    intro h
    exact hk (Fin.ext h)
  by_cases hxa : x = j.castSucc
  · subst x
    rw [Equiv.swap_apply_left]
    change j.val + 1 ≤ k.val ↔ j.val ≤ k.val
    omega
  · by_cases hxb : x = j.succ
    · subst x
      rw [Equiv.swap_apply_right]
      change j.val ≤ k.val ↔ j.val + 1 ≤ k.val
      omega
    · rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]

/-- All unaffected initial vertex sets of the paired permutation flags agree. -/
theorem permutation_initial_face_swap_eq {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 2))) (j : Fin (n + 1))
    (k : Fin (n + 2)) (hk : k ≠ j.castSucc) :
    (Finset.Iic k).map (σ * Equiv.swap j.castSucc j.succ).toEmbedding =
      (Finset.Iic k).map σ.toEmbedding := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, hxy⟩ := Finset.mem_map.mp hx
    exact Finset.mem_map.mpr
      ⟨Equiv.swap j.castSucc j.succ y,
        Finset.mem_Iic.mpr ((adjacent_swap_le_iff j k y hk).2 (Finset.mem_Iic.mp hy)),
        hxy⟩
  · intro hx
    obtain ⟨y, hy, hxy⟩ := Finset.mem_map.mp hx
    refine Finset.mem_map.mpr
      ⟨Equiv.swap j.castSucc j.succ y,
        Finset.mem_Iic.mpr ((adjacent_swap_le_iff j k y hk).2 (Finset.mem_Iic.mp hy)), ?_⟩
    simpa only [Equiv.coe_toEmbedding, Equiv.Perm.mul_apply, Equiv.swap_apply_self] using hxy

/-- The omitted barycentric coordinate of the actual standard face map is zero. -/
theorem standardSimplexFace_omitted_coordinate {n : ℕ} (j : Fin (n + 2))
    (x : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.standardSimplexFace j x j = 0 := by
  exact Finsupp.mapDomain_of_notMem_range x.weights j (by simp)

/-- Paired permutation cells have literally the same deleted interior face map. -/
theorem barycentricSubdivisionMap_comp_inner_face_swap {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 2))) (j : Fin (n + 1)) :
    (BarycentricSimplex.Cycles.barycentricSubdivisionMap (σ * Equiv.swap j.castSucc j.succ)).comp
        (AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.standardSimplexFace j.castSucc) =
      (BarycentricSimplex.Cycles.barycentricSubdivisionMap σ).comp
        (AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.standardSimplexFace j.castSucc) := by
  apply ContinuousMap.ext
  intro x
  apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 2))).injective
  funext i
  simp only [ContinuousMap.comp_apply, BarycentricSimplex.Cycles.barycentricSubdivisionMap,
    BarycentricSimplex.Cycles.BarycentricFlag.toContinuousMap, BarycentricSimplex.Cycles.simplexVertexMap_apply]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k = j.castSucc
  · subst k
    rw [standardSimplexFace_omitted_coordinate]
    simp only [zero_mul]
  · simp only [BarycentricSimplex.Cycles.permutationBarycentricFlag, BarycentricSimplex.Cycles.faceBarycenter_apply]
    rw [permutation_initial_face_swap_eq σ j k hk]

/-- The actual integral singular-chain contribution of any fixed interior face
cancels when summed over all barycentric cells. -/
theorem sum_subdivision_inner_faces_eq_zero {X : Type*} [TopologicalSpace X] {n : ℕ}
    (f : C(Convexity.StdSimplex ℝ (Fin (n + 2)), X)) (j : Fin (n + 1)) :
    (∑ σ : Equiv.Perm (Fin (n + 2)), (Equiv.Perm.sign σ : ℤ) •
      Finsupp.single
        (f.comp ((BarycentricSimplex.Cycles.barycentricSubdivisionMap σ).comp
          (AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.standardSimplexFace j.castSucc))) (1 : ℤ)) = 0 := by
  apply sum_perm_sign_eq_zero_of_swap_invariant j.castSucc j.succ
    (ne_of_lt j.castSucc_lt_succ)
  intro σ
  rw [barycentricSubdivisionMap_comp_inner_face_swap σ j]

/-- The equivalent coefficient-on-generator form matches the usual subdivision
operator on finitely supported integral singular chains. -/
theorem sum_subdivision_inner_face_coefficients_eq_zero
    {X : Type*} [TopologicalSpace X] {n : ℕ}
    (f : C(Convexity.StdSimplex ℝ (Fin (n + 2)), X)) (j : Fin (n + 1)) :
    (∑ σ : Equiv.Perm (Fin (n + 2)),
      Finsupp.single
        (f.comp ((BarycentricSimplex.Cycles.barycentricSubdivisionMap σ).comp
          (AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.standardSimplexFace j.castSucc)))
        (Equiv.Perm.sign σ : ℤ)) = 0 := by
  simpa only [Finsupp.smul_single, smul_eq_mul, mul_one] using
    sum_subdivision_inner_faces_eq_zero f j

/-- Including the alternating boundary coefficient leaves each interior-face
sum zero, in the precise coefficients used by the singular boundary. -/
theorem sum_subdivision_inner_boundary_coefficients_eq_zero
    {X : Type*} [TopologicalSpace X] {n : ℕ}
    (f : C(Convexity.StdSimplex ℝ (Fin (n + 2)), X)) (j : Fin (n + 1)) :
    (∑ σ : Equiv.Perm (Fin (n + 2)),
      Finsupp.single
        (f.comp ((BarycentricSimplex.Cycles.barycentricSubdivisionMap σ).comp
          (AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.standardSimplexFace j.castSucc)))
        ((Equiv.Perm.sign σ : ℤ) * (-1 : ℤ) ^ j.val)) = 0 := by
  have h : (∑ σ : Equiv.Perm (Fin (n + 2)), (Equiv.Perm.sign σ : ℤ) •
      Finsupp.single
        (f.comp ((BarycentricSimplex.Cycles.barycentricSubdivisionMap σ).comp
          (AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.standardSimplexFace j.castSucc)))
        ((-1 : ℤ) ^ j.val)) = 0 := by
    apply sum_perm_sign_eq_zero_of_swap_invariant j.castSucc j.succ
      (ne_of_lt j.castSucc_lt_succ)
    intro σ
    rw [barycentricSubdivisionMap_comp_inner_face_swap σ j]
  simpa only [Finsupp.smul_single, smul_eq_mul] using h

/-- The total interior part of the boundary of a subdivided singular simplex vanishes. -/
theorem sum_subdivision_all_inner_boundary_coefficients_eq_zero
    {X : Type*} [TopologicalSpace X] {n : ℕ}
    (f : C(Convexity.StdSimplex ℝ (Fin (n + 2)), X)) :
    (∑ j : Fin (n + 1), ∑ σ : Equiv.Perm (Fin (n + 2)),
      Finsupp.single
        (f.comp ((BarycentricSimplex.Cycles.barycentricSubdivisionMap σ).comp
          (AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.standardSimplexFace j.castSucc)))
        ((Equiv.Perm.sign σ : ℤ) * (-1 : ℤ) ^ j.val)) = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  exact sum_subdivision_inner_boundary_coefficients_eq_zero f j

/-- The same cancellation holds inside mathlib's actual integral singular chain
complex, including the alternating boundary coefficient. -/
theorem sum_actual_subdivision_inner_faces_eq_zero (X : TopCat.{0}) {n : ℕ}
    (f : C(Convexity.StdSimplex ℝ (Fin (n + 2)), X)) (j : Fin (n + 1)) :
    (∑ σ : Equiv.Perm (Fin (n + 2)), (Equiv.Perm.sign σ : ℤ) •
      (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ)
        ((AlgebraicTopology.Cohomology.Singular.Coefficients.singularSimplicesEquivContinuousMap X n).symm
          (f.comp ((BarycentricSimplex.Cycles.barycentricSubdivisionMap σ).comp
            (AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.standardSimplexFace j.castSucc))))
        ((-1 : ℤ) ^ j.val) : (LocalHomology.Cycles.integralSingularChains X).X n) = 0 := by
  apply sum_perm_sign_eq_zero_of_swap_invariant j.castSucc j.succ
    (ne_of_lt j.castSucc_lt_succ)
  intro σ
  rw [barycentricSubdivisionMap_comp_inner_face_swap σ j]

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.SubdivisionSigns.Cycles
end ComponentSource_17

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.SubdivisionSigns"

@[expose] public section ComponentSource_18
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.PermutationLast -/

/-! # Permutation Last -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.PermutationLast.Cycles

/-!
# Permutations classified by their last value

Inserting a final value into an ordered permutation of the remaining values is
an actual equivalence of finite permutation types. The sign identity gives the
alternating coefficient needed for the outer faces of barycentric subdivision.
-/

open Equiv

/-- Insert the value `i` at the last position, retaining the increasing order
identification of its complement. -/
def insertLastPermutation {n : ℕ} (i : Fin (n + 2))
    (τ : Equiv.Perm (Fin (n + 1))) : Equiv.Perm (Fin (n + 2)) :=
  Fin.cycleIcc i (Fin.last (n + 1)) *
    τ.extendDomain (finSuccAboveEquiv (Fin.last (n + 1)))

/-- The inserted permutation sends its last position to the chosen value. -/
@[simp] theorem insertLastPermutation_apply_last {n : ℕ} (i : Fin (n + 2))
    (τ : Equiv.Perm (Fin (n + 1))) :
    insertLastPermutation i τ (Fin.last (n + 1)) = i := by
  rw [insertLastPermutation, Equiv.Perm.mul_apply,
    Equiv.Perm.extendDomain_apply_not_subtype _ _ (by simp)]
  exact Fin.cycleIcc_of_last (Fin.le_last i)

/-- The other positions follow the canonical order-preserving deletion of `i`. -/
@[simp] theorem insertLastPermutation_apply_castSucc {n : ℕ} (i : Fin (n + 2))
    (τ : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) :
    insertLastPermutation i τ k.castSucc = i.succAbove (τ k) := by
  have hext : τ.extendDomain (finSuccAboveEquiv (Fin.last (n + 1))) k.castSucc =
      (τ k).castSucc := by
    simpa only [finSuccAboveEquiv_apply, Fin.succAbove_last] using
      τ.extendDomain_apply_image (finSuccAboveEquiv (Fin.last (n + 1))) k
  rw [insertLastPermutation, Equiv.Perm.mul_apply, hext]
  simpa only [Function.comp_apply, Fin.succAbove_last] using
    congrFun (Fin.cycleIcc_comp_succAbove i (Fin.last (n + 1)) (Fin.le_last i)) (τ k)

/-- The insertion parameters can be recovered uniquely. -/
theorem insertLastPermutation_injective (n : ℕ) :
    Function.Injective (fun p : Fin (n + 2) × Equiv.Perm (Fin (n + 1)) =>
      insertLastPermutation p.1 p.2) := by
  rintro ⟨i, τ⟩ ⟨j, υ⟩ h
  have hij : i = j := by
    simpa only [insertLastPermutation_apply_last] using
      congrArg (fun σ => σ (Fin.last (n + 1))) h
  subst j
  have hτυ : τ = υ := by
    apply Equiv.ext
    intro k
    apply Fin.succAbove_right_injective (p := i)
    simpa only [insertLastPermutation_apply_castSucc] using
      congrArg (fun σ => σ k.castSucc) h
  exact congrArg (Prod.mk i) hτυ

/-- Every permutation is obtained uniquely by inserting its last value. -/
noncomputable def insertLastPermutationEquiv (n : ℕ) :
    (Fin (n + 2) × Equiv.Perm (Fin (n + 1))) ≃ Equiv.Perm (Fin (n + 2)) :=
  Equiv.ofBijective (fun p => insertLastPermutation p.1 p.2)
    ⟨insertLastPermutation_injective n,
      (Finite.injective_iff_surjective_of_equiv
        (Equiv.Perm.decomposeFin (n := n + 1)).symm).mp
          (insertLastPermutation_injective n)⟩

@[simp] theorem insertLastPermutationEquiv_apply (n : ℕ)
    (p : Fin (n + 2) × Equiv.Perm (Fin (n + 1))) :
    insertLastPermutationEquiv n p = insertLastPermutation p.1 p.2 := rfl

/-- The first coordinate of the inverse equivalence is the last image itself. -/
@[simp] theorem insertLastPermutationEquiv_symm_fst {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 2))) :
    ((insertLastPermutationEquiv n).symm σ).1 = σ (Fin.last (n + 1)) := by
  have h := congrArg (fun τ => τ (Fin.last (n + 1)))
    ((insertLastPermutationEquiv n).apply_symm_apply σ)
  simpa only [insertLastPermutationEquiv_apply, insertLastPermutation_apply_last] using h

/-- Inserting `i` contributes precisely the sign of the cycle from `i` to the last value. -/
theorem sign_insertLastPermutation_factor {n : ℕ} (i : Fin (n + 2))
    (τ : Equiv.Perm (Fin (n + 1))) :
    (Equiv.Perm.sign (insertLastPermutation i τ) : ℤ) =
      (-1 : ℤ) ^ (n + 1 - i.val) * (Equiv.Perm.sign τ : ℤ) := by
  rw [insertLastPermutation, Equiv.Perm.sign_mul, Equiv.Perm.sign_extendDomain,
    Fin.sign_cycleIcc_of_le (Fin.le_last i)]
  simp

/-- The outer-face coefficient agrees with the deleted vertex's alternating sign. -/
theorem sign_insertLastPermutation {n : ℕ} (i : Fin (n + 2))
    (τ : Equiv.Perm (Fin (n + 1))) :
    (Equiv.Perm.sign (insertLastPermutation i τ) : ℤ) * (-1 : ℤ) ^ (n + 1) =
      (-1 : ℤ) ^ i.val * (Equiv.Perm.sign τ : ℤ) := by
  have hp : (-1 : ℤ) ^ (n + 1 - i.val) * (-1 : ℤ) ^ (n + 1) = (-1 : ℤ) ^ i.val := by
    rw [← pow_add, neg_one_pow_eq_pow_mod_two ((n + 1 - i.val) + (n + 1)),
      neg_one_pow_eq_pow_mod_two i.val]
    congr 1
    have hi := i.isLt
    omega
  rw [sign_insertLastPermutation_factor, mul_right_comm, hp]

end OAI.AlgebraicGeometry.CycleClass.Geometric.PermutationLast.Cycles
end ComponentSource_18

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.PermutationLast"


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
    (`OAI.AlgebraicGeometry.CycleClass.Geometric.PermutationLast.Cycles.sign_insertLastPermutation, "theorem")
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
    ("nonce", toJson "4968c807b2eec63a79ad6f51f3d55b02"), ("declaration_count", toJson localNames.size),
    ("kernel_trust_level", toJson env.header.trustLevel.toNat),
    ("kernel_type_checking_enabled", toJson (!Lean.debug.skipKernelTC.get opts)),
    ("server_mode", toJson (Lean.Elab.inServer.get opts)),
    ("required_endpoint_count", toJson required.size),
    ("all_new_declarations_read_from_checked_environment", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo "LITERAL_COMPONENT_KERNEL_AUDIT_COMPLETE:4968c807b2eec63a79ad6f51f3d55b02"
