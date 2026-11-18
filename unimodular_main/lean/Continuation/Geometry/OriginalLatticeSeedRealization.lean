module

public import Continuation.Divisor.SeedCompletion
public import Continuation.Geometry.OriginalLatticeBase
public import Continuation.Geometry.OriginalLatticeRays
public import Continuation.Geometry.OriginalLatticePolar
public import Continuation.Geometry.OriginalLatticeInterior
public import Continuation.Geometry.OriginalLatticeSeedRays

@[expose] public section

/-!
# Proposition 4.2 in the original integral lattice

An integral basis is used only to invoke the coordinate construction.  The
output retains the original real ray hull, the literal character lattice
Hom(N, Z), every proper face of the canonical seed, the full original fan,
and the actual Spec k[σ∨ ∩ Hom(N, Z)] gluing.  The latter is proved isomorphic
over k to the very same smooth projective scheme on which the ordinary
anticanonical nefness and bigness are established.

No chart compatibility or geometric transport hypothesis is supplied by
the caller: the chart naturality, overlap pullbacks and colimit comparison
are proved in the imported original-lattice modules.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open TauCeti.Toric PaperVerification.ToricGeometry
open AlgebraicGeometry CategoryTheory
open Unimodular.Projectivity Unimodular.NefBig
open scoped Classical

universe u v

namespace PaperVerification.OriginalLatticeCharts

variable {N : Type u} [AddCommGroup N]
    {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {n : ℕ} (b : Module.Basis (Fin n) ℤ N)
    {ι : N →+ V} (hi : IsIntegralLattice ι)

/-- The complete seed and weak-Fano realization in the given integral
lattice.  All ray, polytope, polar and fan assertions refer to that original
lattice.  The final isomorphism is between the actual original semigroup
chart gluing and the actual scheme carrying the geometric conclusions. -/
theorem theorem_4_2_original_lattice
    (k : Type u) [Field k] (hn : 0 < n) (U : Finset N)
    (hU : Unimodular.IntegralRigidity.Uniform b
      (fun u : (U : Set N) => u.val))
    (hpos : PointedCone.hull ℝ (ι '' (U : Set N)) = ⊤)
    (hzero : (0 : N) ∉ U) :
    ∃ F : SmoothCompleteFan n,
      ∃ a : Lattice n → ℤ, ∃ ha : F.IsStrictSupport (fun u => (a u : ℝ)),
      ∃ Ψ : Fan ι,
      (originalFan b hi F).IsComplete ∧
      (originalFan b hi F).IsRegular ∧
      (∀ u : N, Unimodular.ConeBases.IsRay (originalFan b hi F) u ↔ u ∈ U) ∧
      (originalFan b hi F).cones =
        Set.range (fun s : OriginalConeIndex b F => latticeCone (ι := ι) s.val) ∧
      Ψ.IsComplete ∧
      (∀ R : PointedCone ℝ V,
        (R ∈ Ψ.cones ∧ Module.finrank ℝ (Submodule.span ℝ (R : Set V)) = 1) ↔
          ∃ w ∈ U, R = PointedCone.hull ℝ {ι w}) ∧
      (∀ C, C ∈ Ψ.cones ↔ ∃ E : Set V, Convex ℝ E ∧
        IsExtreme ℝ (originalRayHull (ι := ι) U) E ∧
        E ≠ originalRayHull (ι := ι) U ∧ C = PointedCone.hull ℝ E) ∧
      (originalFan b hi F).IsSubdivision Ψ ∧
      (0 : V) ∈ interior (originalRayHull (ι := ι) U) ∧
      (∃ W : Finset (N →+ ℤ), originalDualPolar (originalRayHull (ι := ι) U) =
        convexHull ℝ (hi.realCharacter '' (W : Set (N →+ ℤ)))) ∧
      (originalRayHull (ι := ι) U).extremePoints ℝ = ι '' (U : Set N) ∧
      (∀ x : N, ι x ∈ originalRayHull (ι := ι) U ↔ x = 0 ∨ x ∈ U) ∧
      Nonempty (Over.mk (originalSchemeStructureMap b hi k F) ≅ F.fanSchemeOver k) ∧
      Smooth (F.fanSchemeStructureMap k) ∧
      IsProper (F.fanSchemeStructureMap k) ∧
      IsClosedImmersion (strictSupportProjectiveEmbedding F a ha k) ∧
      strictSupportProjectiveEmbedding F a ha k ≫
        polynomialProjectiveToSpec k (WeightIndex.{u} (F := F)) =
          F.fanSchemeStructureMap k ∧
      topologicalKrullDim (F.fanScheme k) = n ∧
      AlgebraicGeometry.IsNef (baseField := k) (anticanonicalLineBundle F k).obj ∧
      IsBig k (anticanonicalLineBundle F k).obj := by
  let Uc : Finset (Lattice n) := U.image b.equivFun
  have hUc := (uniform_coordinate_image_iff b U).mpr hU
  have hpc := coordinate_image_positiveHull_top b hi U hpos
  have hzc := zero_not_mem_coordinate_image b U hzero
  obtain ⟨F, a, ha, Ψ, hrays, hcomplete, hseedrays, hfaces, hsub,
      hinterior, hpolar, hvertices, hterminal, hsmooth, hproper, hembed,
      hover, hdim, hnef, hbig⟩ :=
    Unimodular.WeightedPolytopes.theorem_4_2_geometric_seed k hn Uc hUc hpc hzc
  have hseedrays' : ∀ R : PointedCone ℝ (Ambient n),
      (R ∈ Ψ.cones ∧ Module.finrank ℝ (Submodule.span ℝ (R : Set (Ambient n))) = 1) ↔
        ∃ w ∈ U.image b.equivFun,
          R = PointedCone.hull ℝ {PaperVerification.ToricGeometry.embed n w} := by
    intro R
    constructor
    · intro hR
      obtain ⟨w, hw⟩ := (hseedrays R).mp hR
      exact ⟨w.val, w.property, hw⟩
    · rintro ⟨w, hw, he⟩
      exact (hseedrays R).mpr ⟨⟨w, hw⟩, he⟩
  have hfaces' : ∀ C, C ∈ Ψ.cones ↔ ∃ E : Set (Ambient n), Convex ℝ E ∧
      IsExtreme ℝ (convexHull ℝ (PaperVerification.ToricGeometry.embed n ''
        (U.image b.equivFun : Set (Lattice n)))) E ∧
      E ≠ convexHull ℝ (PaperVerification.ToricGeometry.embed n ''
        (U.image b.equivFun : Set (Lattice n))) ∧ C = PointedCone.hull ℝ E := hfaces
  have hpolar' : ∃ W : Finset (N →+ ℤ),
      originalDualPolar (originalRayHull (ι := ι) U) =
        convexHull ℝ (hi.realCharacter '' (W : Set (N →+ ℤ))) := by
    obtain ⟨W, hW⟩ := hpolar
    apply originalDualPolar_latticePolytope b hi U W
    exact hW
  refine ⟨F, a, ha, transportFan b hi Ψ,
    originalFan_complete b hi F, originalFan_regular b hi F,
    originalFan_prescribed_rays b hi F U hrays,
    originalFan_cones_eq_range b hi F,
    (transportFan_complete_iff b hi Ψ).mpr hcomplete,
    transported_seed_rays b hi U Ψ hseedrays',
    transported_seed_cones b hi U Ψ hfaces',
    originalFan_subdivision b hi F hsub,
    originalRayHull_zero_interior b hi U hinterior, hpolar',
    originalRayHull_extremePoints b hi U hvertices,
    originalRayHull_lattice_points b hi U hterminal,
    ⟨originalGluingOverIso b hi k F⟩,
    hsmooth, hproper, hembed, hover, hdim, hnef, hbig⟩

end PaperVerification.OriginalLatticeCharts

#print axioms PaperVerification.OriginalLatticeCharts.theorem_4_2_original_lattice
