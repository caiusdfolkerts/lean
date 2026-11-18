module

public import PaperVerification.LatticeCosetProjection
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Tactic.Abel

@[expose] public section

/-!
# Projection transfer in an arbitrary finite-dimensional Euclidean space

The finite-coset theorem is transported through orthonormal coordinates.
The ambient lattice, its intersections with the two actual subspaces, and
its orthogonal projection remain independent geometric objects.  The finite
glue decomposition is the displayed data of Proposition 6.1.  Gaussian
convergence and equality of fibre depths are derived in the imported theorems.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators InnerProductSpace

section MetricCoordinates

variable {E : Type*} [NormedAddCommGroup E] {n : ℕ}

def normSetGaussian (S : Set E) (α : ℝ) (x : E) : ℝ :=
  ∑' z : S, Real.exp (-α * ‖z.val - x‖ ^ 2)

def normSquaredDepth (S : Set E) (x : E) : ℝ :=
  sInf ((fun z : E => ‖x - z‖ ^ 2) '' S)

def NormColdSpot (S : Set E) (α : ℝ) (x : E) : Prop :=
  ∀ y : E, normSetGaussian S α x ≤ normSetGaussian S α y

def NormDeepHole (S : Set E) (x : E) : Prop :=
  ∀ y : E, normSquaredDepth S y ≤ normSquaredDepth S x

/-- The geometric definition is the square of the ordinary metric distance,
including sets for which a nearest point is not attained. -/
theorem normSquaredDepth_eq_infDist_sq (S : Set E) (hS : S.Nonempty) (x : E) :
    normSquaredDepth S x = Metric.infDist x S ^ 2 := by
  have hnonneg : 0 ≤ normSquaredDepth S x := by
    apply le_csInf (hS.image _)
    rintro r ⟨z, hz, rfl⟩
    exact sq_nonneg _
  have hbound (z : E) (hz : z ∈ S) : normSquaredDepth S x ≤ ‖x - z‖ ^ 2 :=
    csInf_le ⟨0, by rintro r ⟨v, hv, rfl⟩; exact sq_nonneg _⟩ ⟨z, hz, rfl⟩
  apply le_antisymm
  · have hsqrt : Real.sqrt (normSquaredDepth S x) ≤ Metric.infDist x S := by
      apply (Metric.le_infDist hS).mpr
      intro z hz
      apply (sq_le_sq₀ (Real.sqrt_nonneg _) dist_nonneg).mp
      rw [Real.sq_sqrt hnonneg, dist_eq_norm]
      exact hbound z hz
    have hs := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt 2
    simpa only [Real.sq_sqrt hnonneg] using hs
  · apply le_csInf (hS.image _)
    rintro r ⟨z, hz, rfl⟩
    simpa only [dist_eq_norm] using
      pow_le_pow_left₀ Metric.infDist_nonneg (Metric.infDist_le_dist_of_mem hz) 2

theorem normDeepHole_iff_metric (S : Set E) (hS : S.Nonempty) (x : E) :
    NormDeepHole S x ↔ ∀ y : E, Metric.infDist y S ≤ Metric.infDist x S := by
  constructor
  · intro hx y
    have hy := hx y
    rw [normSquaredDepth_eq_infDist_sq S hS, normSquaredDepth_eq_infDist_sq S hS] at hy
    exact (sq_le_sq₀ Metric.infDist_nonneg Metric.infDist_nonneg).mp hy
  · intro hx y
    rw [normSquaredDepth_eq_infDist_sq S hS, normSquaredDepth_eq_infDist_sq S hS]
    exact pow_le_pow_left₀ Metric.infDist_nonneg (hx y) 2

def coordinateImageEquiv (e : E ≃ (Fin n → ℝ)) (S : Set E) : S ≃ e '' S where
  toFun z := ⟨e z.val, z.val, z.property, rfl⟩
  invFun z := ⟨e.symm z.val, by
    obtain ⟨x, hx, hxe⟩ := z.property
    simpa only [← hxe, e.symm_apply_apply] using hx⟩
  left_inv z := by apply Subtype.ext; exact e.symm_apply_apply z.val
  right_inv z := by apply Subtype.ext; exact e.apply_symm_apply z.val

theorem setGaussian_coordinate_image (e : E ≃ (Fin n → ℝ))
    (he : ∀ x y, sqDist (e x) (e y) = ‖x - y‖ ^ 2)
    (S : Set E) (α : ℝ) (x : E) :
    setGaussian (e '' S) α (e x) = normSetGaussian S α x := by
  unfold setGaussian normSetGaussian
  rw [← (coordinateImageEquiv e S).tsum_eq]
  apply tsum_congr
  intro z
  change Real.exp (-α * sqDist (e z.val) (e x)) = _
  rw [he]

theorem squaredDepth_coordinate_image (e : E ≃ (Fin n → ℝ))
    (he : ∀ x y, sqDist (e x) (e y) = ‖x - y‖ ^ 2)
    (S : Set E) (x : E) :
    squaredDepth (e '' S) (e x) = normSquaredDepth S x := by
  unfold squaredDepth normSquaredDepth
  congr 1
  ext r
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, (he x z).symm⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨e z, ⟨z, hz, rfl⟩, he x z⟩

theorem coldSpot_coordinate_image (e : E ≃ (Fin n → ℝ))
    (he : ∀ x y, sqDist (e x) (e y) = ‖x - y‖ ^ 2)
    (S : Set E) (α : ℝ) (x : E) :
    IsColdSpot (e '' S) α (e x) ↔ NormColdSpot S α x := by
  constructor
  · intro hx y
    simpa only [setGaussian_coordinate_image e he] using hx (e y)
  · intro hx y
    obtain ⟨y, rfl⟩ := e.surjective y
    simpa only [setGaussian_coordinate_image e he] using hx y

theorem deepHole_coordinate_image (e : E ≃ (Fin n → ℝ))
    (he : ∀ x y, sqDist (e x) (e y) = ‖x - y‖ ^ 2)
    (S : Set E) (x : E) :
    IsDeepHole (e '' S) (e x) ↔ NormDeepHole S x := by
  constructor
  · intro hx y
    simpa only [squaredDepth_coordinate_image e he] using hx (e y)
  · intro hx y
    obtain ⟨y, rfl⟩ := e.surjective y
    simpa only [squaredDepth_coordinate_image e he] using hx y

theorem gaussian_range_coordinate_image (e : E ≃ (Fin n → ℝ))
    (he : ∀ x y, sqDist (e x) (e y) = ‖x - y‖ ^ 2)
    (S : Set E) (α : ℝ) :
    Set.range (setGaussian (e '' S) α) = Set.range (normSetGaussian S α) := by
  ext r
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := e.surjective y
    exact ⟨x, (setGaussian_coordinate_image e he S α x).symm.trans hy⟩
  · rintro ⟨x, hx⟩
    exact ⟨e x, (setGaussian_coordinate_image e he S α x).trans hx⟩

end MetricCoordinates

section OrthonormalCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Writing the second summand as `Hᗮ` loses no orthogonal decomposition:
every orthogonal complementary subspace is exactly this subspace. -/
theorem orthogonal_summand_eq (H W : Submodule ℝ E)
    (hspan : H ⊔ W = ⊤) (horth : W ≤ Hᗮ) : W = Hᗮ := by
  apply le_antisymm horth
  intro x hx
  have hxsum : x ∈ H ⊔ W := by rw [hspan]; exact Submodule.mem_top
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hxsum
  have huorth : u ∈ Hᗮ := by
    have hsub := Hᗮ.sub_mem hx (horth hv)
    simpa only [← huv, add_sub_cancel_right] using hsub
  have hu0 : u = 0 := (Submodule.disjoint_def.mp H.orthogonal_disjoint) u hu huorth
  simpa only [← huv, hu0, zero_add] using hv

def isometricCoordinates {n : ℕ} (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    E ≃ (Fin n → ℝ) :=
  e.toEquiv.trans (WithLp.equiv 2 (Fin n → ℝ))

theorem sqDist_isometricCoordinates {n : ℕ}
    (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) (x y : E) :
    sqDist (isometricCoordinates e x) (isometricCoordinates e y) = ‖x - y‖ ^ 2 := by
  rw [sqDist_eq_euclidean_norm_sq]
  change ‖e x - e y‖ ^ 2 = _
  rw [← map_sub, e.norm_map]

def orthogonalCoordinates (H : Submodule ℝ E) {h w : ℕ}
    (eH : H ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin h))
    (eW : Hᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin w)) : E ≃ (Fin (h + w) → ℝ) :=
  ((H.prodEquivOfIsCompl Hᗮ H.isCompl_orthogonal).symm.toEquiv.trans
    ((isometricCoordinates eH).prodCongr (isometricCoordinates eW))).trans
      (Fin.appendEquiv h w)

theorem orthogonalCoordinates_add (H : Submodule ℝ E) {h w : ℕ}
    (eH : H ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin h))
    (eW : Hᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin w)) (x : H) (t : Hᗮ) :
    orthogonalCoordinates H eH eW ((x : E) + (t : E)) =
      Fin.append (isometricCoordinates eH x) (isometricCoordinates eW t) := by
  change (Fin.appendEquiv h w)
    (((isometricCoordinates eH).prodCongr (isometricCoordinates eW))
      ((H.prodEquivOfIsCompl Hᗮ H.isCompl_orthogonal).symm
        ((H.prodEquivOfIsCompl Hᗮ H.isCompl_orthogonal) (x, t)))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

theorem sqDist_orthogonalCoordinates (H : Submodule ℝ E) {h w : ℕ}
    (eH : H ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin h))
    (eW : Hᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin w)) (x y : E) :
    sqDist (orthogonalCoordinates H eH eW x) (orthogonalCoordinates H eH eW y) =
      ‖x - y‖ ^ 2 := by
  obtain ⟨⟨xH, xW⟩, rfl⟩ := (H.prodEquivOfIsCompl Hᗮ H.isCompl_orthogonal).surjective x
  obtain ⟨⟨yH, yW⟩, rfl⟩ := (H.prodEquivOfIsCompl Hᗮ H.isCompl_orthogonal).surjective y
  change sqDist (orthogonalCoordinates H eH eW ((xH : E) + (xW : E)))
    (orthogonalCoordinates H eH eW ((yH : E) + (yW : E))) =
      ‖((xH : E) + (xW : E)) - ((yH : E) + (yW : E))‖ ^ 2
  rw [orthogonalCoordinates_add, orthogonalCoordinates_add, sqDist_append_blocks,
    sqDist_isometricCoordinates, sqDist_isometricCoordinates]
  have hsub : ((xH : E) + (xW : E)) - ((yH : E) + (yW : E)) =
      ((xH - yH : H) : E) + ((xW - yW : Hᗮ) : E) := by
    simp only [Submodule.coe_sub]
    abel
  have horth : ⟪((xH - yH : H) : E), ((xW - yW : Hᗮ) : E)⟫_ℝ = 0 :=
    Submodule.inner_right_of_mem_orthogonal (K := H)
      (xH - yH).property (xW - yW).property
  rw [hsub]
  simpa only [pow_two, Submodule.norm_coe] using
    (norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth).symm

def latticeIntersection (L : Submodule ℤ E) (H : Submodule ℝ E) : Submodule ℤ H :=
  ZLattice.comap ℝ L H.subtype

def latticeOrthogonalProjection (L : Submodule ℤ E) (H : Submodule ℝ E) :
    Submodule ℤ H :=
  L.map (H.orthogonalProjectionOnto.toLinearMap.restrictScalars ℤ)

def latticeCoset {V : Type*} [AddCommGroup V] (N : Submodule ℤ V) (a : V) : Set V :=
  {x | x - a ∈ N}

def coordinateLattice {n : ℕ} (N : Submodule ℤ E)
    (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    Submodule ℤ (EuclideanSpace ℝ (Fin n)) :=
  ZLattice.comap ℝ N e.symm.toLinearMap

theorem coordinateLattice_coset_mem {n : ℕ} (N : Submodule ℤ E)
    (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) (a x : E) :
    isometricCoordinates e x ∈ euclideanLatticeCoset (coordinateLattice N e) (e a) ↔
      x ∈ latticeCoset N a := by
  change e.symm (e x - e a) ∈ N ↔ x - a ∈ N
  rw [map_sub, e.symm_apply_apply, e.symm_apply_apply]

theorem coordinateLattice_coset_image {n : ℕ} (N : Submodule ℤ E)
    (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) (a : E) :
    (isometricCoordinates e) '' latticeCoset N a =
      euclideanLatticeCoset (coordinateLattice N e) (e a) := by
  ext x
  obtain ⟨x, rfl⟩ := (isometricCoordinates e).surjective x
  rw [coordinateLattice_coset_mem]
  constructor
  · rintro ⟨y, hy, heq⟩
    exact (isometricCoordinates e).injective heq ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem orthogonal_projection_add (H : Submodule ℝ E) (x : H) (t : Hᗮ) :
    H.orthogonalProjectionOnto ((x : E) + (t : E)) = x := by
  rw [map_add, H.orthogonalProjectionOnto_mem_subspace_eq_self,
    Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal (K := H) t.property, add_zero]

/-- Literal finite glue data in the orthogonal subspaces.  In particular the
underlying lattice is not defined by the desired Gaussian or deep-hole set. -/
def HasOrthogonalGlue (L : Submodule ℤ E) (H : Submodule ℝ E)
    {G : Type*} (a : G → H) (b : G → Hᗮ) : Prop :=
  ∀ z : E, z ∈ L ↔ ∃ g : G, ∃ x : H, ∃ t : Hᗮ,
    x ∈ latticeCoset (latticeIntersection L H) (a g) ∧
    t ∈ latticeCoset (latticeIntersection L Hᗮ) (b g) ∧ z = (x : E) + (t : E)

theorem orthogonalGlue_coordinate_image (L : Submodule ℤ E) (H : Submodule ℝ E)
    {G : Type*} (a : G → H) (b : G → Hᗮ) (hglue : HasOrthogonalGlue L H a b)
    {h w : ℕ} (eH : H ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin h))
    (eW : Hᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin w)) :
    (orthogonalCoordinates H eH eW) '' (L : Set E) =
      orthogonalGlue
        (fun g => euclideanLatticeCoset (coordinateLattice (latticeIntersection L H) eH) (eH (a g)))
        (fun g => euclideanLatticeCoset (coordinateLattice (latticeIntersection L Hᗮ) eW) (eW (b g))) := by
  ext z
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨g, x, t, hx, ht, rfl⟩ := (hglue z).mp hz
    exact ⟨g, isometricCoordinates eH x,
      (coordinateLattice_coset_mem _ _ _ _).mpr hx,
      isometricCoordinates eW t, (coordinateLattice_coset_mem _ _ _ _).mpr ht,
      orthogonalCoordinates_add H eH eW x t⟩
  · rintro ⟨g, x, hx, t, ht, rfl⟩
    obtain ⟨x, rfl⟩ := (isometricCoordinates eH).surjective x
    obtain ⟨t, rfl⟩ := (isometricCoordinates eW).surjective t
    exact ⟨(x : E) + (t : E), (hglue _).mpr ⟨g, x, t,
      (coordinateLattice_coset_mem _ _ _ _).mp hx,
      (coordinateLattice_coset_mem _ _ _ _).mp ht, rfl⟩,
      orthogonalCoordinates_add H eH eW x t⟩

theorem orthogonalProjection_coordinate_image (L : Submodule ℤ E) (H : Submodule ℝ E)
    {G : Type*} (a : G → H) (b : G → Hᗮ) (hglue : HasOrthogonalGlue L H a b)
    {h : ℕ} (eH : H ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin h)) :
    (isometricCoordinates eH) '' (latticeOrthogonalProjection L H : Set H) =
      ⋃ g, euclideanLatticeCoset (coordinateLattice (latticeIntersection L H) eH) (eH (a g)) := by
  ext x
  constructor
  · rintro ⟨x, ⟨z, hz, hzx⟩, rfl⟩
    obtain ⟨g, y, t, hy, ht, rfl⟩ := (hglue z).mp hz
    have hyx : y = x := (orthogonal_projection_add H y t).symm.trans hzx
    exact Set.mem_iUnion.mpr ⟨g,
      (coordinateLattice_coset_mem (latticeIntersection L H) eH (a g) x).mpr
        (hyx ▸ hy)⟩
  · obtain ⟨x, rfl⟩ := (isometricCoordinates eH).surjective x
    intro hx
    obtain ⟨g, hg⟩ := Set.mem_iUnion.mp hx
    refine ⟨x, ?_, rfl⟩
    refine ⟨(x : E) + (b g : E), (hglue _).mpr ⟨g, x, b g,
      (coordinateLattice_coset_mem _ _ _ _).mp hg, ?_, rfl⟩,
      orthogonal_projection_add H x (b g)⟩
    change b g - b g ∈ latticeIntersection L Hᗮ
    simpa using (latticeIntersection L Hᗮ).zero_mem

/-- Proposition 6.1 in an arbitrary finite-dimensional real inner-product
space, with the paper's explicitly displayed finite glue decomposition.

`latticeIntersection` is the actual intersection, expressed as a submodule
of the subspace; `latticeOrthogonalProjection` is the actual orthogonal image.
There are no convergence, common-depth, or projected-minimum hypotheses.
The dimension of either summand is unrestricted, including zero. -/
theorem orthogonal_lattice_projection_transfer
    (L : Submodule ℤ E) [DiscreteTopology L] (H : Submodule ℝ E)
    {G : Type*} [Fintype G] (a : G → H) (b : G → Hᗮ)
    (hglue : HasOrthogonalGlue L H a b)
    (ha : Pairwise (fun g g' => a g - a g' ∉ latticeIntersection L H))
    (t₀ : Hᗮ) (c : ℝ → ℝ)
    (hfibre : ∀ α : ℝ, 0 < α → ∀ g,
      normSetGaussian (latticeCoset (latticeIntersection L Hᗮ) (b g)) α t₀ = c α)
    (K : Set E)
    (hK : ∀ α : ℝ, 0 < α → ∀ z : E,
      NormColdSpot (L : Set E) α z ↔ z ∈ K)
    (hmeet : ∃ x₀ : H, (x₀ : E) + (t₀ : E) ∈ K) :
    (∀ α : ℝ, 0 < α → ∀ x : H,
      NormColdSpot (latticeOrthogonalProjection L H : Set H) α x ↔
        (x : E) + (t₀ : E) ∈ K) ∧
    (∀ α : ℝ, 0 < α →
      sInf (Set.range (normSetGaussian (latticeOrthogonalProjection L H : Set H) α)) =
        sInf (Set.range (normSetGaussian (L : Set E) α)) / c α) ∧
    ((∀ z : E, z ∈ K ↔ NormDeepHole (L : Set E) z) → ∀ x : H,
      NormDeepHole (latticeOrthogonalProjection L H : Set H) x ↔
        (x : E) + (t₀ : E) ∈ K) := by
  letI : Nonempty G := by
    obtain ⟨g, _, _, _, _, _⟩ := (hglue 0).mp L.zero_mem
    exact ⟨g⟩
  let N := latticeIntersection L H
  let F := latticeIntersection L Hᗮ
  letI : DiscreteTopology N :=
    ZLattice.comap_discreteTopology ℝ L H.subtypeL.continuous H.subtype_injective
  letI : DiscreteTopology F :=
    ZLattice.comap_discreteTopology ℝ L Hᗮ.subtypeL.continuous Hᗮ.subtype_injective
  let eH := (stdOrthonormalBasis ℝ H).repr
  let eW := (stdOrthonormalBasis ℝ Hᗮ).repr
  let NC := coordinateLattice N eH
  let FC := coordinateLattice F eW
  letI : DiscreteTopology NC :=
    ZLattice.comap_discreteTopology ℝ N eH.symm.continuous eH.symm.injective
  letI : DiscreteTopology FC :=
    ZLattice.comap_discreteTopology ℝ F eW.symm.continuous eW.symm.injective
  let hc := isometricCoordinates eH
  let wc := isometricCoordinates eW
  let ec := orthogonalCoordinates H eH eW
  let C := fun g => euclideanLatticeCoset NC (eH (a g))
  let D := fun g => euclideanLatticeCoset FC (eW (b g))
  let Kc : Set (Fin (Module.finrank ℝ H + Module.finrank ℝ Hᗮ) → ℝ) :=
    {z | ec.symm z ∈ K}
  have hhc : ∀ x y, sqDist (hc x) (hc y) = ‖x - y‖ ^ 2 :=
    sqDist_isometricCoordinates eH
  have hec : ∀ x y, sqDist (ec x) (ec y) = ‖x - y‖ ^ 2 :=
    sqDist_orthogonalCoordinates H eH eW
  have hgluec : ec '' (L : Set E) = orthogonalGlue C D :=
    orthogonalGlue_coordinate_image L H a b hglue eH eW
  have hMc : hc '' (latticeOrthogonalProjection L H : Set H) = ⋃ g, C g :=
    orthogonalProjection_coordinate_image L H a b hglue eH
  have hac : Pairwise (fun g g' => eH (a g) - eH (a g') ∉ NC) := by
    intro g g' hne hm
    apply ha hne
    change eH.symm (eH (a g) - eH (a g')) ∈ N at hm
    simpa only [map_sub, eH.symm_apply_apply] using hm
  have hfibc : ∀ α : ℝ, 0 < α → ∀ g,
      setGaussian (D g) α (wc t₀) = c α := by
    intro α hα g
    calc
      setGaussian (D g) α (wc t₀) =
          normSetGaussian (latticeCoset F (b g)) α t₀ := by
        change setGaussian
          (euclideanLatticeCoset (coordinateLattice F eW) (eW (b g))) α
          (isometricCoordinates eW t₀) = _
        rw [← coordinateLattice_coset_image F eW (b g)]
        exact setGaussian_coordinate_image (isometricCoordinates eW)
          (sqDist_isometricCoordinates eW) _ _ _
      _ = c α := hfibre α hα g
  have hKc : ∀ α : ℝ, 0 < α → ∀ z,
      IsColdSpot (orthogonalGlue C D) α z ↔ z ∈ Kc := by
    intro α hα z
    obtain ⟨z, rfl⟩ := ec.surjective z
    rw [← hgluec, coldSpot_coordinate_image ec hec]
    simpa only [Kc, Set.mem_setOf_eq, ec.symm_apply_apply] using hK α hα z
  have hmeetc : ∃ x₀, Fin.append x₀ (wc t₀) ∈ Kc := by
    obtain ⟨x₀, hx₀⟩ := hmeet
    refine ⟨hc x₀, ?_⟩
    change ec.symm (Fin.append (hc x₀) (wc t₀)) ∈ K
    rw [← orthogonalCoordinates_add H eH eW]
    simpa only [ec, Equiv.symm_apply_apply] using hx₀
  have ht := lattice_coset_projection_transfer NC FC
    (fun g => eH (a g)) (fun g => eW (b g)) hac (wc t₀) c hfibc Kc hKc hmeetc
  refine ⟨?_, ?_, ?_⟩
  · intro α hα x
    have hx := ht.1 α hα (hc x)
    rw [← hMc, coldSpot_coordinate_image hc hhc] at hx
    change NormColdSpot (latticeOrthogonalProjection L H : Set H) α x ↔
      ec.symm (Fin.append (hc x) (wc t₀)) ∈ K at hx
    rw [← orthogonalCoordinates_add H eH eW] at hx
    simpa only [ec, Equiv.symm_apply_apply] using hx
  · intro α hα
    have hv := ht.2.1 α hα
    rw [← hMc, ← hgluec, gaussian_range_coordinate_image hc hhc,
      gaussian_range_coordinate_image ec hec] at hv
    exact hv
  · intro hdeep x
    have hdeepc : ∀ z, z ∈ Kc ↔ IsDeepHole (orthogonalGlue C D) z := by
      intro z
      obtain ⟨z, rfl⟩ := ec.surjective z
      rw [← hgluec, deepHole_coordinate_image ec hec]
      simpa only [Kc, Set.mem_setOf_eq, ec.symm_apply_apply] using hdeep z
    have hx := ht.2.2 hdeepc (hc x)
    rw [← hMc, deepHole_coordinate_image hc hhc] at hx
    change NormDeepHole (latticeOrthogonalProjection L H : Set H) x ↔
      ec.symm (Fin.append (hc x) (wc t₀)) ∈ K at hx
    rw [← orthogonalCoordinates_add H eH eW] at hx
    simpa only [ec, Equiv.symm_apply_apply] using hx

end OrthonormalCoordinates

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.orthogonal_lattice_projection_transfer
