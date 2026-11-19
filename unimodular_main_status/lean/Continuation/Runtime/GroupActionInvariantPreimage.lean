module

public import Continuation.Runtime.GroupActionRestriction

/-!
# Inverse images of invariant opens

Equivariance on the actual scheme product transports invariance through
an arbitrary equivariant morphism. In particular, the invariant opens of
an open subscheme are obtained from invariant opens of the original
scheme without any assertion about rational points.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GroupAction

/-- Invariance is preserved by the inverse image of an actual equivariant
morphism. -/
theorem invariant_preimage {S : Scheme.{u}} (G : Over S) [MonObj G]
    {X Y : Over S} [ModObj G X] [ModObj G Y]
    (i : Y ⟶ X) [IsModHom G i] (U : X.left.Opens)
    (hU : (γ[G,X]).left ⁻¹ᵁ U = (snd G X).left ⁻¹ᵁ U) :
    (γ[G,Y]).left ⁻¹ᵁ (i.left ⁻¹ᵁ U) =
      (snd G Y).left ⁻¹ᵁ (i.left ⁻¹ᵁ U) := by
  have ha : (γ[G,Y]).left ≫ i.left = (G ◁ i).left ≫ (γ[G,X]).left :=
    congrArg (fun f : G ⊗ Y ⟶ X => f.left)
      (IsModHom.smul_hom (A := G) (f := i))
  have hp : (G ◁ i).left ≫ (snd G X).left = (snd G Y).left ≫ i.left :=
    congrArg (fun f : G ⊗ Y ⟶ X => f.left) (whiskerLeft_snd G i)
  rw [← Scheme.Hom.comp_preimage, ha, Scheme.Hom.comp_preimage, hU,
    ← Scheme.Hom.comp_preimage, hp, Scheme.Hom.comp_preimage]

end AlgebraicGeometry.GroupAction

#print axioms AlgebraicGeometry.GroupAction.invariant_preimage
