module

public import Continuation.Fano.All
public import Recovery.Unimodular.RegularMatroid.RepresentationCore
public import Continuation.Runtime.MinorRepresentation
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Combinatorics.Matroid.Map
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.List.FinRange
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Integer
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.StdBasis
public import Recovery.Unimodular.PriorExtensions.SignedSumsRegular
public import Recovery.Unimodular.ProductVectorMatroid

@[expose] public section

/-!
# Rational representation and the arbitrary-matroid Fano construction

The exact bodies below are grouped to avoid repeated large-library import
startup on machines with limited memory. Named source sections and the adjacent
manifest record the original files. No mathematical parameter is removed by
this grouping, and every new proof remains kernel checked.
-/

set_option debug.skipKernelTC false
set_option maxHeartbeats 0

/-! The five shared representation sections are supplied by their unique
`Recovery.Unimodular.RegularMatroid.RepresentationCore` owner. The remaining
geometric construction sections and the complete observation list are unchanged. -/

/-! ## Exact source section: Continuation/Runtime/PrivateCoordinateMinor.lean -/
section



set_option backward.isDefEq.respectTransparency false

/-!
# Private coordinates retain the original ordinary matroid as a minor

Contract the negative private coordinate columns. Projection to the original
space is exactly the quotient by their span. Additional columns are deleted.
The statement is independent of any convex or toric construction.
-/

open Set Submodule
open scoped Matroid

namespace Unimodular.PrivateCoordinateMinor

variable {K E X W : Type*} [Field K] [Fintype E] [DecidableEq E]
  [AddCommGroup W] [Module K W]

def negativePrivateColumn (e : E) : W × (E → K) := (0, -Pi.single e 1)

theorem private_sum (z : E → K) :
    (∑ e, (-z e) • (negativePrivateColumn (W := W) e)) = (0, z) := by
  apply Prod.ext
  · simp [negativePrivateColumn, Prod.fst_sum]
  · ext i
    simp [negativePrivateColumn, Prod.snd_sum, Finset.sum_apply, Pi.smul_apply,
      Pi.single_apply]

theorem private_span :
    span K (Set.range (negativePrivateColumn (K := K) (W := W))) =
      LinearMap.ker (LinearMap.fst K W (E → K)) := by
  apply le_antisymm
  · apply span_le.mpr
    rintro _ ⟨e, rfl⟩
    simp [negativePrivateColumn]
  · intro z hz
    have hz0 : z.1 = 0 := hz
    have heq : z = (0, z.2) := Prod.ext hz0 rfl
    rw [heq, ← private_sum (W := W) z.2]
    apply Submodule.sum_mem
    intro e _
    exact Submodule.smul_mem _ _ (subset_span ⟨e, rfl⟩)

/-- An exact contraction/deletion certificate in any larger labelled family. -/
theorem isMinor_of_private_columns (v : X → W × (E → K)) (u : E → W)
    (keep contract : E ↪ X)
    (hdisjoint : Disjoint (Set.range keep) (Set.range contract))
    (hkeep : ∀ e, (v (keep e)).1 = u e)
    (hcontract : ∀ e, v (contract e) = negativePrivateColumn e) :
    (VectorMatroid.ofFamily (K := K) u).mapEmbedding keep ≤m
      VectorMatroid.ofFamily (K := K) v := by
  have himage : v '' Set.range contract =
      Set.range (negativePrivateColumn (K := K) (W := W)) := by
    ext z
    constructor
    · rintro ⟨x, ⟨e, rfl⟩, rfl⟩
      exact ⟨e, (hcontract e).symm⟩
    · rintro ⟨e, rfl⟩
      exact ⟨contract e, ⟨e, rfl⟩, hcontract e⟩
  have hker : LinearMap.ker (LinearMap.fst K W (E → K)) =
      span K (v '' Set.range contract) := by
    rw [himage, private_span]
  have hR : Set.range keep ⊆ Set.univ \ Set.range contract := by
    intro x hx
    exact ⟨Set.mem_univ _, fun hc ↦ Set.disjoint_left.mp hdisjoint hx hc⟩
  exact VectorMatroid.mapEmbedding_isMinor_of_kernel_image v u (Set.subset_univ _)
    keep hR (LinearMap.fst K W (E → K)) hker hkeep

def pairedFamily (u : E → W) : E ⊕ E → W × (E → K) :=
  Sum.elim (fun e ↦ (u e, Pi.single e 1)) negativePrivateColumn

def keepEmbedding : E ↪ E ⊕ E := ⟨Sum.inl, Sum.inl_injective⟩
def contractEmbedding : E ↪ E ⊕ E := ⟨Sum.inr, Sum.inr_injective⟩

theorem pairedFamily_minor (u : E → W) :
    (VectorMatroid.ofFamily (K := K) u).mapEmbedding keepEmbedding ≤m
      VectorMatroid.ofFamily (K := K) (pairedFamily (K := K) u) := by
  apply isMinor_of_private_columns (pairedFamily (K := K) u) u
    keepEmbedding contractEmbedding
  · exact Set.disjoint_left.mpr (by
      rintro x ⟨e, rfl⟩ ⟨f, h⟩
      change Sum.inr f = Sum.inl e at h
      cases h)
  · intro e
    rfl
  · intro e
    rfl

end Unimodular.PrivateCoordinateMinor

namespace Unimodular.PrivateCoordinateMinor

section PositivePrivate
variable {K E S W : Type*} [Field K] [Fintype S] [DecidableEq S]
  [AddCommGroup W] [Module K W]

def positivePrivateColumn (s : S) : W × (S → K) := (0, Pi.single s 1)

theorem positive_private_sum (z : S → K) :
    (∑ s, z s • (positivePrivateColumn (W := W) s)) = (0, z) := by
  apply Prod.ext
  · simp [positivePrivateColumn, Prod.fst_sum]
  · ext i
    simp [positivePrivateColumn, Prod.snd_sum, Finset.sum_apply, Pi.smul_apply,
      Pi.single_apply]

theorem positive_private_span :
    span K (Set.range (positivePrivateColumn (K := K) (W := W))) =
      LinearMap.ker (LinearMap.fst K W (S → K)) := by
  apply le_antisymm
  · apply span_le.mpr
    rintro _ ⟨s, rfl⟩
    simp [positivePrivateColumn]
  · intro z hz
    have hz0 : z.1 = 0 := hz
    have heq : z = (0, z.2) := Prod.ext hz0 rfl
    rw [heq, ← positive_private_sum (W := W) z.2]
    apply Submodule.sum_mem
    intro s _
    exact Submodule.smul_mem _ _ (subset_span ⟨s, rfl⟩)

/-- The original labels may be any subset of a larger family; all other
nonprivate columns are deleted after the private coordinates are contracted. -/
theorem isMinor_of_positive_private_columns {X : Type*}
    (v : X → W × (S → K)) (u : E → W)
    (keep : E ↪ X) (contract : S ↪ X)
    (hdisjoint : Disjoint (Set.range keep) (Set.range contract))
    (hkeep : ∀ e, (v (keep e)).1 = u e)
    (hcontract : ∀ s, v (contract s) = positivePrivateColumn s) :
    (VectorMatroid.ofFamily (K := K) u).mapEmbedding keep ≤m
      VectorMatroid.ofFamily (K := K) v := by
  have himage : v '' Set.range contract =
      Set.range (positivePrivateColumn (K := K) (W := W)) := by
    ext z
    constructor
    · rintro ⟨x, ⟨s, rfl⟩, rfl⟩
      exact ⟨s, (hcontract s).symm⟩
    · rintro ⟨s, rfl⟩
      exact ⟨contract s, ⟨s, rfl⟩, hcontract s⟩
  have hker : LinearMap.ker (LinearMap.fst K W (S → K)) =
      span K (v '' Set.range contract) := by
    rw [himage, positive_private_span]
  have hR : Set.range keep ⊆ Set.univ \ Set.range contract := by
    intro x hx
    exact ⟨Set.mem_univ _, fun hc ↦ Set.disjoint_left.mp hdisjoint hx hc⟩
  exact VectorMatroid.mapEmbedding_isMinor_of_kernel_image v u (Set.subset_univ _)
    keep hR (LinearMap.fst K W (S → K)) hker hkeep

/-- Coordinate packing and an integral change of basis do not alter the
actual minor statement. This wrapper applies directly to a family indexed by
the actual facet set of a polytope. -/
theorem isMinor_of_positive_private_columns_equiv {X Z : Type*}
    [AddCommGroup Z] [Module K Z]
    (v : X → Z) (u : E → W) (coordinates : Z ≃ₗ[K] W × (S → K))
    (keep : E ↪ X) (contract : S ↪ X)
    (hdisjoint : Disjoint (Set.range keep) (Set.range contract))
    (hkeep : ∀ e, (coordinates (v (keep e))).1 = u e)
    (hcontract : ∀ s, coordinates (v (contract s)) = positivePrivateColumn s) :
    (VectorMatroid.ofFamily (K := K) u).mapEmbedding keep ≤m
      VectorMatroid.ofFamily (K := K) v := by
  have h := isMinor_of_positive_private_columns (coordinates ∘ v) u
    keep contract hdisjoint hkeep hcontract
  have heq : VectorMatroid.ofFamily (K := K) (coordinates ∘ v) =
      VectorMatroid.ofFamily (K := K) v := by
    apply (VectorMatroid.ofFamily_eq_iff _ _).mpr
    intro I
    exact coordinates.toLinearMap.linearIndepOn_iff_of_injOn coordinates.injective.injOn
  rwa [heq] at h

def liftedFamily (u : E → W) (extra : E → S → K) : E ⊕ S → W × (S → K) :=
  Sum.elim (fun e ↦ (u e, extra e)) positivePrivateColumn

def leftEmbedding : E ↪ E ⊕ S := ⟨Sum.inl, Sum.inl_injective⟩

/-- Contracting all positive private coordinates recovers every original
column, including loops and repeated labels, with arbitrary lifted components. -/
theorem liftedFamily_minor (u : E → W) (extra : E → S → K) :
    (VectorMatroid.ofFamily (K := K) u).mapEmbedding leftEmbedding ≤m
      VectorMatroid.ofFamily (K := K) (liftedFamily u extra) := by
  let v := liftedFamily u extra
  have himage : v '' Set.range (Sum.inr : S → E ⊕ S) =
      Set.range (positivePrivateColumn (K := K) (W := W) (S := S)) := by
    ext z
    constructor
    · rintro ⟨x, ⟨s, rfl⟩, rfl⟩
      exact ⟨s, rfl⟩
    · rintro ⟨s, rfl⟩
      exact ⟨Sum.inr s, ⟨s, rfl⟩, rfl⟩
  have hker : LinearMap.ker (LinearMap.fst K W (S → K)) =
      span K (v '' Set.range (Sum.inr : S → E ⊕ S)) := by
    rw [himage, positive_private_span]
  have hR : Set.range (leftEmbedding (E := E) (S := S)) ⊆
      Set.univ \ Set.range (Sum.inr : S → E ⊕ S) := by
    rintro x ⟨e, rfl⟩
    refine ⟨Set.mem_univ _, ?_⟩
    rintro ⟨s, h⟩
    change Sum.inr s = Sum.inl e at h
    cases h
  exact VectorMatroid.mapEmbedding_isMinor_of_kernel_image v u (Set.subset_univ _)
    leftEmbedding hR (LinearMap.fst K W (S → K)) hker (fun _ ↦ rfl)

end PositivePrivate
end Unimodular.PrivateCoordinateMinor
end

/-! ## Exact source section: Continuation/Runtime/MultiwedgeMinor.lean -/
section



set_option backward.isDefEq.respectTransparency false

/-!
# The prescribed matroid is a minor of the actual multiwedge facet matroid

The label embeddings land in the finite set of genuine primitive facet
normals. All pure private coordinates are contracted; any unselected old
labels are deleted. Coordinate packing is transported by its actual linear
equivalence, so this conclusion concerns the standard real ray matroid.
-/

noncomputable section
open Set
open scoped Matroid

namespace Unimodular.MultiwedgeSmooth

variable {n : ℕ} {E F : Type*} [Fintype E] [DecidableEq E]
  (J : E → Type*) [∀ e, Fintype (J e)] [∀ e, DecidableEq (J e)]
  (A : E → Lattice n) (hJ : ∀ e, Nonempty (J e))

def facetMatroid : Matroid {u // u ∈ packedNormals J A} :=
  VectorMatroid.ofFamily (K := ℝ) (fun u ↦ Unimodular.embed u.val)

def selectedFacetEmbedding (f : F ↪ E) : F ↪ {u // u ∈ packedNormals J A} :=
  (f.trans ⟨Sum.inl, Sum.inl_injective⟩).trans (facetEmbedding J A hJ)

def pureFacetEmbedding : Extra J ↪ {u // u ∈ packedNormals J A} :=
  (⟨Sum.inr, Sum.inr_injective⟩ : Extra J ↪ E ⊕ Extra J).trans
    (facetEmbedding J A hJ)

theorem selected_pure_disjoint (f : F ↪ E) :
    Disjoint (Set.range (selectedFacetEmbedding J A hJ f))
      (Set.range (pureFacetEmbedding J A hJ)) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨e, rfl⟩ ⟨s, hs⟩
  have h := (facetEmbedding J A hJ).injective hs
  cases h

/-- This includes arbitrary extra old labels, which disappear by deletion. -/
theorem selected_input_minor (f : F ↪ E) :
    (VectorMatroid.ofFamily (K := ℝ) (fun e ↦ Unimodular.embed (A (f e)))).mapEmbedding
      (selectedFacetEmbedding J A hJ f) ≤m facetMatroid J A := by
  apply PrivateCoordinateMinor.isMinor_of_positive_private_columns_equiv
    (fun u : {u // u ∈ packedNormals J A} ↦ Unimodular.embed u.val)
    (fun e ↦ Unimodular.embed (A (f e)))
    (ProductCoordinates.pack (Extra J) ℝ).symm
    (selectedFacetEmbedding J A hJ f) (pureFacetEmbedding J A hJ)
    (selected_pure_disjoint J A hJ f)
  · intro e
    change ((ProductCoordinates.pack (Extra J) ℝ).symm
      (Unimodular.embed (packedFamily J A (Sum.inl (f e))))).1 = _
    rw [packedFamily, ProductCoordinates.embed_pack, LinearEquiv.symm_apply_apply]
    rfl
  · intro s
    change (ProductCoordinates.pack (Extra J) ℝ).symm
      (Unimodular.embed (packedFamily J A (Sum.inr s))) = _
    rw [packedFamily, ProductCoordinates.embed_pack, LinearEquiv.symm_apply_apply]
    ext i <;> simp [ProductCoordinates.embedProduct, MultiwedgeGeometry.normal,
      MultiwedgeBasis.pure, PrivateCoordinateMinor.positivePrivateColumn,
      Unimodular.embed, Pi.single_apply]

end Unimodular.MultiwedgeSmooth

namespace Unimodular.CubeInput

variable {n : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
  (u : E → Lattice n) (d : ℤ) (hd : 2 ≤ d)

def inputFacetEmbedding : E ↪ {v // v ∈ (presentation u d hd).normals} :=
  MultiwedgeSmooth.selectedFacetEmbedding (Block u d) (normal u)
    (block_nonempty u d hd) ⟨Sum.inl, Sum.inl_injective⟩

/-- Full arbitrary integer-family realization, on the actual facets of the
constructed smooth reflexive polytope. No rank or simplicity hypothesis occurs. -/
theorem input_matroid_minor :
    (VectorMatroid.ofFamily (K := ℝ) (fun e ↦ Unimodular.embed (u e))).mapEmbedding
      (inputFacetEmbedding u d hd) ≤m
      VectorMatroid.ofFamily (K := ℝ)
        (fun v : {v // v ∈ (presentation u d hd).normals} ↦ Unimodular.embed v.val) :=
  MultiwedgeSmooth.selected_input_minor (Block u d) (normal u)
    (block_nonempty u d hd) ⟨Sum.inl, Sum.inl_injective⟩

end Unimodular.CubeInput
end
end

/-! ## Exact source section: Continuation/Fano/RationalRealization.lean -/
section



/-!
# Arbitrary rational matroids in divisible smooth reflexive polytopes

The input is an ordinary finite matroid on its actual ground set. A rational
representation is cleared of denominators and given one unused zero coordinate.
The cube construction then supplies an actual smooth reflexive polytope, all
primitive facet labels, an ordinary contraction/deletion minor, and the integral
character relation witnessing divisibility of its boundary divisor. Congruence
of all vertices excludes unimodular triangles in every geometric face.

The scheme-theoretic passage from the coefficient relation to the intrinsic
anticanonical line bundle is a separate theorem in `AnticanonicalDivisibility`.
-/

namespace Unimodular.RationalRealization

open Set
open scoped Matroid
noncomputable section

variable {E : Type*}

/-- The full polytope and ordinary-matroid part of Corollary 5.3, including
arbitrary finite ground sets, loops, parallel labels, and the empty matroid. -/
theorem exists_smooth_reflexive_realization
    (M : Matroid E) [M.Finite]
    (hM : RepresentationBridge.RepresentableOnGround ℚ M)
    (d : ℤ) (hd : 2 ≤ d) :
    ∃ n : ℕ, 0 < n ∧ ∃ P : SmoothReflexivePresentation n,
      ∃ f : M.E ↪ {v // v ∈ P.normals},
        (M.restrictSubtype M.E).mapEmbedding f ≤m
          VectorMatroid.ofFamily (K := ℝ)
            (fun v : {v // v ∈ P.normals} ↦ embed v.val) ∧
        (∀ F : Set (Ambient n), IsExtreme ℝ P.carrier F →
          ¬ SegmentSimplex.IsUnimodularTriangle F) ∧
        (∃ D : Lattice n → ℤ, ∃ m : Lattice n,
          ∀ u ∈ P.normals, 1 = d * D u + integerPairing m u) ∧
        (∀ a ∈ P.vertices, ∀ b ∈ P.vertices,
          ∃ z : Lattice n, b - a = d • z) := by
  classical
  letI : Fintype M.E := M.ground_finite.fintype
  obtain ⟨r, hr, u, hu⟩ :=
    RepresentationBridge.RepresentableOnGround.integer_real_positive M hM
  let n := MultiwedgeSmooth.dimension (n := r) (CubeInput.Block u d)
  let P := CubeInput.presentation u d hd
  refine ⟨n, ?_, P, CubeInput.inputFacetEmbedding u d hd, ?_, ?_, ?_, ?_⟩
  · exact hr.trans_le (Nat.le_add_right _ _)
  · rw [hu]
    exact CubeInput.input_matroid_minor u d hd
  · exact CubeInput.presentation_UT_free u d hd
  · obtain ⟨D,hD⟩ := MultiwedgeSmooth.boundary_coefficient_relation
      (CubeInput.Block u d) (CubeInput.normal u) (CubeInput.height u d)
      (CubeInput.block_card u d hd) d (CubeInput.height_dvd u d)
    exact ⟨D, MultiwedgeSmooth.indexCharacter (CubeInput.Block u d), hD⟩
  · intro a ha b hb
    exact MultiwedgeSmooth.packed_vertices_difference
      (CubeInput.Block u d) (CubeInput.normal u) (CubeInput.height u d) d
      (CubeInput.vertices d) (CubeInput.vertex_dvd d) (CubeInput.height_dvd u d)
      a b ha hb

/-- Rational representability is also necessary for an ordinary minor of
the genuine facet-normal matroid of any smooth reflexive polytope. -/
theorem rationally_representable_of_facet_minor
    {n : ℕ} (P : SmoothReflexivePresentation n) (M : Matroid E) [M.Finite]
    (f : M.E ↪ {v // v ∈ P.normals})
    (hminor : (M.restrictSubtype M.E).mapEmbedding f ≤m
      VectorMatroid.ofFamily (K := ℝ)
        (fun v : {v // v ∈ P.normals} ↦ embed v.val)) :
    RepresentationBridge.RepresentableOnGround ℚ M :=
  RepresentationBridge.integer_ray_minor_ground_representable
    (fun v : {v // v ∈ P.normals} ↦ v.val) M f hminor

end
end Unimodular.RationalRealization

end

#print axioms Unimodular.RepresentationBridge.ofFamily_dual
#print axioms Unimodular.RepresentationBridge.RepresentableOnGround.integer_real_positive
#print axioms Unimodular.RepresentationBridge.integer_ray_minor_ground_representable
#print axioms Unimodular.CubeInput.input_matroid_minor
#print axioms Unimodular.RationalRealization.exists_smooth_reflexive_realization
#print axioms Unimodular.RationalRealization.rationally_representable_of_facet_minor
