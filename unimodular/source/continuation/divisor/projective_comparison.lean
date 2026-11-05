module

public import Continuation.Divisor.ProjectiveFoundations
public import Continuation.Divisor.Geometry

/-!
# An actual projective embedding from the vertex charts

The finite weight family consists of every original vertex and one
primitive lattice step in every inward edge direction. Its convex hull
is the original polytope. At each vertex, its difference semigroup is
exactly the dual cone semigroup. The recovered affine-chart comparison
therefore identifies the actual fan scheme with its monomial Proj and
supplies a genuine closed immersion into finite projective space.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

universe u
namespace Unimodular.Projectivity

open Set AlgebraicGeometry CategoryTheory
open PaperVerification.ToricGeometry PaperVerification.ToricCharacters
open scoped Classical BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : ℕ}

/-- Concrete polytope data for the original full fan cones. The fields
state actual vertex, normal-cone and unit-step equalities, not scheme
projectivity or a prescribed projective presentation. -/
structure VertexChartData (F : PaperVerification.ToricGeometry.SmoothCompleteFan n)
    (P : LatticePolytope n) where
  vertex : F.fullCones → Lattice n
  vertex_mem : ∀ s, PaperVerification.ToricGeometry.embed n (vertex s) ∈ P.carrier
  hull : P.carrier = convexHull ℝ
    (Set.range (fun s => PaperVerification.ToricGeometry.embed n (vertex s)))
  normal : ∀ s, P.normalCone (PaperVerification.ToricGeometry.embed n (vertex s)) =
    (latticeRayCone s.val : Set (Ambient n))
  unitStep_mem : ∀ s i, PaperVerification.ToricGeometry.embed n
    (vertex s + integralDualBasis (F.fullConeBasis s) i) ∈ P.carrier

variable {F : PaperVerification.ToricGeometry.SmoothCompleteFan n}
  {P : LatticePolytope n} (D : VertexChartData F P)

/-- Universe lifting lets the projective embedding use any field universe. -/
abbrev WeightIndex := ULift.{u} (F.fullCones × Option (Fin n))

namespace VertexChartData

def weight (j : WeightIndex.{u} (F := F)) : Lattice n :=
  D.vertex j.down.1 + j.down.2.elim 0 (integralDualBasis (F.fullConeBasis j.down.1))

@[simp] theorem weight_vertex (s : F.fullCones) :
    D.weight (ULift.up (s, none) : WeightIndex.{u} (F := F)) = D.vertex s := by
  simp [weight]

@[simp] theorem weight_step (s : F.fullCones) (i : Fin n) :
    D.weight (ULift.up (s, some i) : WeightIndex.{u} (F := F)) =
      D.vertex s + integralDualBasis (F.fullConeBasis s) i := rfl

theorem weight_mem (j : WeightIndex.{u} (F := F)) :
    PaperVerification.ToricGeometry.embed n (D.weight j) ∈ P.carrier := by
  rcases j with ⟨s, i⟩
  cases i with
  | none => simpa using D.vertex_mem s
  | some i => exact D.unitStep_mem s i

theorem hull_weights :
    convexHull ℝ (Set.range (fun j : WeightIndex.{u} (F := F) =>
      PaperVerification.ToricGeometry.embed n (D.weight j))) = P.carrier := by
  apply le_antisymm
  · apply convexHull_min
    · rintro x ⟨j, rfl⟩
      exact D.weight_mem j
    · rw [D.hull]
      exact convex_convexHull ℝ _
  · rw [D.hull]
    apply convexHull_mono
    rintro x ⟨s, rfl⟩
    exact ⟨ULift.up (s, none), by simp⟩

theorem vertex_orthant (s : F.fullCones) (x : Ambient n) (hx : x ∈ P.carrier)
    (i : Fin n) :
    0 ≤ (integralBasisReal (integralDualBasis (F.fullConeBasis s))).repr
      (x - PaperVerification.ToricGeometry.embed n (D.vertex s)) i := by
  have hi : F.fullConeBasis s i ∈ s.val := by
    rw [F.fullConeBasis_ray_set]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hn : PaperVerification.ToricGeometry.embed n (F.fullConeBasis s i) ∈
      P.normalCone (PaperVerification.ToricGeometry.embed n (D.vertex s)) := by
    rw [D.normal]
    exact latticeRayCone_generator s.val hi
  have h := hn x hx
  rw [integralDualBasis_real_repr]
  simpa only [integralBasisReal_apply, Pi.sub_apply, mul_comm] using h

theorem vertex_extreme (s : F.fullCones) :
    PaperVerification.ToricGeometry.embed n (D.vertex s) ∈ P.carrier.extremePoints ℝ :=
  P.extreme_of_supporting_basis _ (D.vertex_mem s)
    (integralBasisReal (integralDualBasis (F.fullConeBasis s))) (D.vertex_orthant s)

theorem vertexIndex_exists (j : vertexWeightIndices D.weight.{u}) :
    ∃ s : F.fullCones, D.weight j.val = D.vertex s := by
  have hj : PaperVerification.ToricGeometry.embed n (D.weight j.val) ∈
      P.carrier.extremePoints ℝ := by
    rw [← D.hull_weights]
    exact (Finset.mem_filter.mp j.property).2
  rw [D.hull] at hj
  obtain ⟨s, hs⟩ := extremePoints_convexHull_subset hj
  exact ⟨s, (embed_injective n hs).symm⟩

/-- Select the original full cone belonging to an actual vertex weight. -/
def vertexCone (j : vertexWeightIndices D.weight.{u}) : F.fullCones :=
  Classical.choose (D.vertexIndex_exists j)

theorem vertexCone_weight (j : vertexWeightIndices D.weight.{u}) :
    D.weight j.val = D.vertex (D.vertexCone j) :=
  Classical.choose_spec (D.vertexIndex_exists j)

theorem cone_eq_of_latticeRayCone_eq {s t : Finset (Lattice n)}
    (hs : s ∈ F.cones) (ht : t ∈ F.cones)
    (he : latticeRayCone s = latticeRayCone t) : s = t := by
  apply Finset.Subset.antisymm
  · intro v hv
    apply (F.ray_mem_cone_iff ht (F.ray_mem_of_mem_cone hs hv)).mp
    rw [← he]
    exact latticeRayCone_generator s hv
  · intro v hv
    apply (F.ray_mem_cone_iff hs (F.ray_mem_of_mem_cone ht hv)).mp
    rw [he]
    exact latticeRayCone_generator t hv

theorem vertexCone_cover (t : Finset (Lattice n)) (ht : t ∈ F.cones) :
    ∃ j : vertexWeightIndices D.weight.{u}, t ⊆ (D.vertexCone j).val := by
  obtain ⟨s, hs, hts, hcard⟩ := F.isPure t ht
  let s' : F.fullCones := ⟨s, Finset.mem_filter.mpr ⟨hs, hcard⟩⟩
  let i : WeightIndex.{u} (F := F) := ULift.up (s', none)
  have hi : i ∈ vertexWeightIndices D.weight := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ i, ?_⟩
    rw [D.hull_weights]
    simpa only [i, D.weight_vertex] using D.vertex_extreme s'
  let j : vertexWeightIndices D.weight := ⟨i, hi⟩
  have hv : D.vertex (D.vertexCone j) = D.vertex s' := by
    rw [← D.vertexCone_weight j]
    exact D.weight_vertex s'
  have he : latticeRayCone (D.vertexCone j).val = latticeRayCone s'.val := by
    apply SetLike.coe_injective
    rw [← D.normal, ← D.normal, hv]
  have he' := cone_eq_of_latticeRayCone_eq (F.fullCones_mem (D.vertexCone j))
    (F.fullCones_mem s') he
  exact ⟨j, he'.symm ▸ hts⟩

/-- Every weight difference is an actual integral dual-cone element. -/
theorem difference_mem_dual (j : vertexWeightIndices D.weight.{u})
    (i : WeightIndex.{u} (F := F)) :
    D.weight i - D.weight j.val ∈ dualConeMonoid (D.vertexCone j).val := by
  intro v hv
  have hn : PaperVerification.ToricGeometry.embed n v ∈
      P.normalCone (PaperVerification.ToricGeometry.embed n (D.vertex (D.vertexCone j))) := by
    rw [D.normal]
    exact latticeRayCone_generator _ hv
  have h := hn _ (D.weight_mem i)
  rw [D.vertexCone_weight j]
  change 0 ≤ ∑ q, v q * (D.weight i q - D.vertex (D.vertexCone j) q)
  change 0 ≤ ∑ q, (v q : ℝ) *
    ((D.weight i q : ℝ) - (D.vertex (D.vertexCone j) q : ℝ)) at h
  exact_mod_cast h

/-- The primitive unit steps generate the entire genuine tangent semigroup. -/
theorem dual_eq_difference (j : vertexWeightIndices D.weight.{u}) :
    dualConeMonoid (D.vertexCone j).val = differenceWeightMonoid D.weight j.val := by
  let s := D.vertexCone j
  let b := integralDualBasis (F.fullConeBasis s)
  apply le_antisymm
  · intro z hz
    have hc : ∀ i : Fin n, 0 ≤ b.repr z i := by
      rw [F.fullConeBasis_ray_set, dualConeMonoid_basis_eq] at hz
      exact fun i => hz i (Finset.mem_univ i)
    have hb (i : Fin n) : b i ∈ differenceWeightMonoid D.weight j.val := by
      apply AddSubmonoid.subset_closure
      refine ⟨ULift.up (s, some i), ?_⟩
      change D.weight (ULift.up (s, some i)) - D.weight j.val = b i
      rw [D.weight_step, D.vertexCone_weight]
      exact add_sub_cancel_left _ _
    rw [← b.sum_repr z]
    apply AddSubmonoid.sum_mem
    intro i _
    have he : ((b.repr z i).toNat : ℤ) = b.repr z i := Int.toNat_of_nonneg (hc i)
    rw [← he, natCast_zsmul]
    exact AddSubmonoid.nsmul_mem _ (hb i) _
  · apply AddSubmonoid.closure_le.mpr
    rintro z ⟨i, rfl⟩
    exact D.difference_mem_dual j i

variable (k : Type u) [Field k]

/-- Isomorphism of the actual fan scheme with the actual monomial Proj.
The source is not replaced by a projective model in a definition. -/
def fanSchemeIsoMonomial : F.fanScheme k ≅ monomialProjectiveScheme D.weight.{u} k :=
  F.monomialNormalFanIso P D.weight k (fun j => (D.vertexCone j).val)
    D.dual_eq_difference (fun j => F.fullCones_mem (D.vertexCone j))
    D.vertexCone_cover (fun j => D.weight_mem j.val)
    (fun j => by rw [D.vertexCone_weight]; exact D.normal (D.vertexCone j))

/-- A genuine closed immersion into finite polynomial projective space. -/
def fanProjectiveEmbedding :
    F.fanScheme k ⟶ Proj (MvPolynomial.homogeneousSubmodule
      (WeightIndex.{u} (F := F)) k) :=
  (D.fanSchemeIsoMonomial k).hom ≫ monomialProjectiveEmbedding D.weight k

instance fanProjectiveEmbedding_isClosedImmersion :
    IsClosedImmersion (D.fanProjectiveEmbedding k) := by
  unfold fanProjectiveEmbedding
  infer_instance

#print axioms dual_eq_difference
#print axioms fanSchemeIsoMonomial
#print axioms fanProjectiveEmbedding_isClosedImmersion

end VertexChartData
end Unimodular.Projectivity
