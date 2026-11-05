module

public import PaperVerification.ToricCartierBoundaryInvariance
public import PaperVerification.ToricActionProductProperties

@[expose] public section

/-!
# The normalized Cartier divisor is invariant under the actual torus action

The only geometric assumptions are an actual dense equivariant open torus
embedding and ordinary smoothness. Normality, product integrality, local
Noetherianity, boundary invariance, and equality of Cartier presentations
are conclusions of the preceding proofs. The comparison is equality of
embedded fractional sheaves, which is stronger than an unspecified
isomorphism of line bundles.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory MonObj

namespace PaperVerification.ToricSchemes.SplitToricEmbedding

variable {k : Type u} [Field k] {n : ℕ}
    {X : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n→ℤ)) X]
    [IsIntegral X.left] [Smooth X.hom]
    (T : SplitToricEmbedding k n X)

theorem action_pullback_equivalent_of_unitFrames
    [IsLocallyNoetherian X.left] (E : CartierData X.left)
    (hE : E.localCocycle.HasUnitFramesOn T.torusOpen) :
    (E.dominantPullback (γ[splitTorusOver k (Fin n→ℤ),X]).left).Equivalent
      (E.dominantPullback (snd (splitTorusOver k (Fin n→ℤ)) X).left) := by
  let G := splitTorusOver k (Fin n→ℤ)
  let Y := G⊗X
  let p := (snd G X).left
  let a := (γ[G,X]).left
  let C := E.localCocycle
  let P := C.dominantPullback p
  letI : IsLocallyNoetherian Y.left := T.product_locallyNoetherian
  letI : Smooth Y.hom := T.product_smooth
  have hunit : P.HasUnitFramesOn (p ⁻¹ᵁ T.torusOpen) :=
    C.hasUnitFramesOn_pullback T.torusOpen
      hE p
  have hzero : ∀ y∉T.productBoundary,P.toCartierData.weilCoefficient y=0 := by
    intro y hy
    apply P.weilCoefficient_zero_of_unitFrames (p ⁻¹ᵁ T.torusOpen) hunit y
    exact Classical.not_not.mp hy
  have hInv : (P.dominantPullback T.graphIso.hom).toCartierData.Equivalent
      P.toCartierData :=
    P.equivalent_pullback_of_boundary_fixed Y.hom T.graphIso T.productBoundary
      T.graph_preimage_productBoundary T.graph_fixes_codimensionOne_boundary hzero
  have hcomp := C.dominantPullback_comp_equivalent p T.graphIso.hom
  have hpa : T.graphIso.hom ≫ p = a := T.graph_hom_snd
  have hcomp' : (P.dominantPullback T.graphIso.hom).toCartierData.Equivalent
      (C.dominantPullback a).toCartierData := by
    simpa only [P, hpa] using hcomp
  exact (C.dominantPullback a).toCartierData.equivalent_trans
    (P.dominantPullback T.graphIso.hom).toCartierData P.toCartierData
    ((P.dominantPullback T.graphIso.hom).toCartierData.equivalent_symm
      (C.dominantPullback a).toCartierData hcomp') hInv

theorem normalized_action_pullback_equivalent_of_locallyNoetherian
    [IsLocallyNoetherian X.left] (D : CartierData X.left) :
    ((torusNormalizedCartier k n X.left T.torus.left D).dominantPullback
      (γ[splitTorusOver k (Fin n→ℤ),X]).left).Equivalent
        ((torusNormalizedCartier k n X.left T.torus.left D).dominantPullback
          (snd (splitTorusOver k (Fin n→ℤ)) X).left) :=
  T.action_pullback_equivalent_of_unitFrames
    (torusNormalizedCartier k n X.left T.torus.left D)
    (torusNormalizedCartier_unitFrames k n X.left T.torus.left D)

/-- The local Noetherian condition in the proof is derived from ordinary
smoothness over the field and is absent from the mathematical inputs. -/
theorem normalized_action_pullback_equivalent (D : CartierData X.left) :
    letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
    ((torusNormalizedCartier k n X.left T.torus.left D).dominantPullback
      (γ[splitTorusOver k (Fin n→ℤ),X]).left).Equivalent
        ((torusNormalizedCartier k n X.left T.torus.left D).dominantPullback
          (snd (splitTorusOver k (Fin n→ℤ)) X).left) := by
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  exact T.normalized_action_pullback_equivalent_of_locallyNoetherian D

/-- The corresponding isomorphism of the actual ordinary sheaf pullbacks.
It is obtained from equality of their proved fractional realizations. -/
def normalizedActionSheafIso (D : CartierData X.left) :
    letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
    (Scheme.Modules.pullback (γ[splitTorusOver k (Fin n→ℤ),X]).left).obj
        (torusNormalizedCartier k n X.left T.torus.left D).sheaf ≅
      (Scheme.Modules.pullback (snd (splitTorusOver k (Fin n→ℤ)) X).left).obj
        (torusNormalizedCartier k n X.left T.torus.left D).sheaf := by
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let E := torusNormalizedCartier k n X.left T.torus.left D
  exact E.dominantPullbackSheafIso (γ[splitTorusOver k (Fin n→ℤ),X]).left ≪≫
    (T.normalized_action_pullback_equivalent D).choose ≪≫
      (E.dominantPullbackSheafIso (snd (splitTorusOver k (Fin n→ℤ)) X).left).symm

end PaperVerification.ToricSchemes.SplitToricEmbedding
