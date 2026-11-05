module

public import PaperVerification.ToricIntrinsicSectionCharacters
public import PaperVerification.ToricCartierRationalSections

@[expose] public section

/-!
# Actual local regularity of the torus action on a normalized section

This is the geometric input to coefficient extraction. It is a statement
about ordinary regular functions on the actual product scheme and follows
from the independently proved equality of its fractional Cartier sheaves.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open PaperVerification.ToricCharacters
open scoped PaperVerification.ToricSchemes.BaseSections

namespace PaperVerification.ToricSchemes.SplitToricEmbedding

variable {k : Type u} [Field k] {n : ℕ}
    {X : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n→ℤ)) X]
    [IsIntegral X.left] [Smooth X.hom] [IsLocallyNoetherian X.left]
    (T : SplitToricEmbedding k n X) (D : CartierData X.left)

theorem action_ratio_regular_of_unitFrames
    (E : CartierData X.left) (hE : E.localCocycle.HasUnitFramesOn T.torusOpen)
    (f : AddMonoidAlgebra k (Fin n→ℤ))
    (hf : f∈torusSectionCharacters k n X.left T.torus.left E)
    (i : E.localCocycle.index)
    (U : X.left.Opens) [Nonempty U]
    (hU : U≤E.localCocycle.openSet i) :
    let p := (snd (splitTorusOver k (Fin n→ℤ)) X).left
    letI : Nonempty (p ⁻¹ᵁ U) := dominant_preimage_nonempty p U
    dominantFunctionFieldMap (γ[splitTorusOver k (Fin n→ℤ),X]).left
        (openTorusRationalAlgHom k n X.left T.torus.left f) /
      dominantFunctionFieldMap p
        (E.localCocycle.generator i :
          X.left.functionField) ∈
      ((splitTorusOver k (Fin n→ℤ)⊗X).left.germToFunctionField (p ⁻¹ᵁ U)).hom.range := by
  let G := splitTorusOver k (Fin n→ℤ)
  let Y := (G⊗X).left
  let p := (snd G X).left
  let a := (γ[G,X]).left
  let q := openTorusRationalAlgHom k n X.left T.torus.left f
  letI : Nonempty (p ⁻¹ᵁ U) := dominant_preimage_nonempty p U
  have hq : q∈E.sectionValueRange ⊤ :=
    hf
  have ha : dominantFunctionFieldMap a q∈(E.dominantPullback a).sectionValueRange ⊤ := by
    letI : Nonempty (a ⁻¹ᵁ (⊤ : X.left.Opens)) := dominant_preimage_nonempty a ⊤
    exact E.dominantPullback_mem_sectionValueRange a ⊤ q hq
  have hp : dominantFunctionFieldMap a q∈(E.dominantPullback p).sectionValueRange ⊤ := by
    rw [← (E.dominantPullback a).equivalent_sectionValueRange
      (E.dominantPullback p)
      (T.action_pullback_equivalent_of_unitFrames E hE) ⊤]
    exact ha
  obtain ⟨s,hs⟩ := hp
  have hlocal : dominantFunctionFieldMap a q∈
      (E.dominantPullback p).sectionValueRange (p ⁻¹ᵁ U) :=
    ⟨(E.dominantPullback p).sheaf.presheaf.map (homOfLE le_top).op s,
      ((E.dominantPullback p).sectionValue_restrict (homOfLE le_top) s).trans hs⟩
  exact ((E.localCocycle.dominantPullback p).mem_sectionValueRange_iff i
    (p ⁻¹ᵁ U) (p.preimage_mono hU) (dominantFunctionFieldMap a q)).mp hlocal

theorem normalized_action_ratio_regular
    (f : AddMonoidAlgebra k (Fin n→ℤ))
    (hf : f∈normalizedGlobalCharacters k n X.left T.torus.left D)
    (i : (torusNormalizedCartier k n X.left T.torus.left D).localCocycle.index)
    (U : X.left.Opens) [Nonempty U]
    (hU : U≤(torusNormalizedCartier k n X.left T.torus.left D).localCocycle.openSet i) :
    let p := (snd (splitTorusOver k (Fin n→ℤ)) X).left
    letI : Nonempty (p ⁻¹ᵁ U) := dominant_preimage_nonempty p U
    dominantFunctionFieldMap (γ[splitTorusOver k (Fin n→ℤ),X]).left
        (openTorusRationalAlgHom k n X.left T.torus.left f) /
      dominantFunctionFieldMap p
        ((torusNormalizedCartier k n X.left T.torus.left D).localCocycle.generator i :
          X.left.functionField) ∈
      ((splitTorusOver k (Fin n→ℤ)⊗X).left.germToFunctionField (p ⁻¹ᵁ U)).hom.range :=
  T.action_ratio_regular_of_unitFrames (torusNormalizedCartier k n X.left T.torus.left D)
    (torusNormalizedCartier_unitFrames k n X.left T.torus.left D) f
    ((mem_normalizedGlobalCharacters_iff k n X.left T.torus.left D f).mp hf) i U hU

end PaperVerification.ToricSchemes.SplitToricEmbedding
