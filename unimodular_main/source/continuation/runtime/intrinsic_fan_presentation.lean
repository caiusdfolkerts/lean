module

public import Continuation.Runtime.IntrinsicBoundaryRays
public import Continuation.Runtime.BoundaryValuationTransport
public import Continuation.Runtime.AmpleDegreeOneFoundations

/-! Actual fan reconstruction and the exact original boundary-polytope
comparison, independent of graphic section-ring presentations. The
mathematical bodies are the original canonical proofs. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricGeometry PaperVerification.ToricSchemes
open scoped Classical

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

/-- Every primitive fan ray, not just a selected real basis, is included
in the integer spanning family. A full smooth cone supplies an integral basis. -/
theorem integerSpan_all_rays {n : ℕ} (F : SmoothCompleteFan n) :
    Submodule.span ℤ (Set.range (fun v : F.rays => v.val)) = ⊤ := by
  obtain ⟨s, hs⟩ := F.fullCones_nonempty F.isPure
  let s' : F.fullCones := ⟨s, hs⟩
  apply top_unique
  rw [← (F.fullConeBasis s').span_eq]
  apply Submodule.span_mono
  rintro x ⟨i, rfl⟩
  exact ⟨F.activeRay s' i, rfl⟩

end PaperVerification.ToricGeometry.SmoothCompleteFan

namespace PaperVerification.ToricSchemes.SplitToricEmbedding

open Unimodular.NefBig

variable {k : Type u} [Field k] {n : ℕ}
    {X : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n → ℤ)) X]
    [IsIntegral X.left] [Smooth X.hom] [IsProper X.hom]
    (T : SplitToricEmbedding k n X)

local instance fanPresentationLocallyNoetherian : IsLocallyNoetherian X.left :=
  LocallyOfFiniteType.isLocallyNoetherian X.hom

/-- The literal unit-boundary divisor inequalities, with the ordinary
unreflected sign. The anticanonical identification is a theorem below. -/
def unitBoundaryDivisorPolytope : Set (Ambient n) :=
  {x | ∀ q : T.BoundaryPrime, -(1 : ℝ) ≤ T.boundaryForm q x}

/-- The ample line bundle quantified in the paper supplies the actual
reconstruction input internally. No auxiliary ample divisor is assumed. -/
theorem exists_fan_of_ordinaryAmple
    (M : X.left.Modules) (hM : IsInvertibleModule M) (hample : IsAmpleModule M) :
    ∃ (F : SmoothCompleteFan n) (e : F.fanSchemeOver k ≅ X),
      (F.intrinsicToricEmbedding k).torus ≫ e.hom = T.torus := by
  let D := invertibleFractionalPresentation M hM
  have hC : IsAmpleModule D.localCocycle.sheaf :=
    isAmpleModule_of_iso D.presentationIso hample
  have hD : D.IsAmple := isAmple_cocycle_of_isAmpleModule D.localCocycle hC
  obtain ⟨P, F, e, _, _, _, hbase, htorus⟩ := T.exists_smooth_complete_fan D hD
  let eOver : F.fanSchemeOver k ≅ X := Over.isoMk e hbase
  refine ⟨F, eOver, ?_⟩
  apply Over.OverMorphism.ext
  exact htorus

section Presentation

variable (F : SmoothCompleteFan n) (e : F.fanSchemeOver k ≅ X)
    (htorus : (F.intrinsicToricEmbedding k).torus ≫ e.hom = T.torus)

local instance fanPresentationOverIntegral : IsIntegral (F.fanSchemeOver k).left := by
  change IsIntegral (F.fanScheme k)
  infer_instance
local instance fanPresentationOverLocallyNoetherian : IsLocallyNoetherian (F.fanSchemeOver k).left := by
  change IsLocallyNoetherian (F.fanScheme k)
  infer_instance

include e htorus in
/-- Equality with every actual primitive ray is derived from the character
orders on every boundary prime, in both directions. -/
theorem completeBoundaryRaySet_presentation :
    T.completeBoundaryRaySet = (F.rays : Set (Lattice n)) := by
  ext v
  change (∃ q : T.BoundaryPrime, T.boundaryValuation q = v) ↔ v ∈ F.rays
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨p, rfl⟩ :=
      ((F.intrinsicToricEmbedding k).boundaryPrimeEquiv T e htorus).surjective q
    rw [(F.intrinsicToricEmbedding k).boundaryValuation_equiv T e htorus]
    exact F.boundaryValuation_mem_rays k p
  · intro hv
    obtain ⟨p, hp⟩ := F.exists_boundaryPrime_valuation k v hv
    refine ⟨(F.intrinsicToricEmbedding k).boundaryPrimeEquiv T e htorus p, ?_⟩
    rw [(F.intrinsicToricEmbedding k).boundaryValuation_equiv T e htorus]
    exact hp

include e htorus in
/-- The literal unreflected divisor polytope agrees in every real point,
not only at lattice points or in a chosen chamber. -/
theorem unitBoundaryDivisorPolytope_presentation :
    T.unitBoundaryDivisorPolytope = F.fanPolytope (fun _ => (1 : ℝ)) := by
  ext x
  change (∀ q : T.BoundaryPrime, -(1 : ℝ) ≤
    dotProductEquiv ℝ (Fin n) (embed n (T.boundaryValuation q)) x) ↔
    ∀ v ∈ F.rays, -(1 : ℝ) ≤ dotProductEquiv ℝ (Fin n) (embed n v) x
  have hr := T.completeBoundaryRaySet_presentation F e htorus
  constructor
  · intro h v hv
    have hv' : v ∈ T.completeBoundaryRaySet := by rw [hr]; exact hv
    obtain ⟨q, rfl⟩ := hv'
    exact h q
  · intro h q
    apply h
    change T.boundaryValuation q ∈ (F.rays : Set _)
    rw [← hr]
    exact Set.mem_range_self q

end Presentation

end PaperVerification.ToricSchemes.SplitToricEmbedding

#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.exists_fan_of_ordinaryAmple
#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.unitBoundaryDivisorPolytope_presentation
