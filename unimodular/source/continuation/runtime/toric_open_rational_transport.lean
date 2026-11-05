module

public import Continuation.Runtime.ToricOpenRestriction
public import Continuation.Runtime.IntrinsicReconstruction

/-!
# The original Laurent coordinates under toric restriction

The generic-stalk map of a dominant morphism that preserves the specified
torus carries every original Laurent coordinate to that same coordinate
in the target function field. Restriction to an invariant open therefore
retains the character lattice literally.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open PaperVerification.ToricCharacters
open AlgebraicGeometry CategoryTheory
open MonoidalCategory CartesianMonoidalCategory

namespace PaperVerification.ToricSchemes.SplitToricEmbedding

variable {k : Type u} [Field k] {n : ℕ}
    {X Y : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n → ℤ)) X]
    [ModObj (splitTorusOver k (Fin n → ℤ)) Y]
    [IsIntegral X.left] [IsIntegral Y.left]
    (T : SplitToricEmbedding k n X) (S : SplitToricEmbedding k n Y)

/-- Transport follows from the genuine affine coordinate square; no
function-field identification or change of lattice is assumed. -/
theorem laurentValue_pullback (i : Y ⟶ X) [IsDominant i.left]
    (hi : S.torus ≫ i = T.torus) (f : AddMonoidAlgebra k (Fin n → ℤ)) :
    dominantFunctionFieldMap i.left
        (openTorusRationalAlgHom k n X.left T.torus.left f) =
      openTorusRationalAlgHom k n Y.left S.torus.left f := by
  let R := CommRingCat.of (torusCoordinateRing k n)
  letI : IsDomain R := torusCoordinateRing_isDomain k n
  change dominantFunctionFieldMap i.left (affineOpenCoordinateMap R T.torus.left f) =
    affineOpenCoordinateMap R S.torus.left f
  apply dominantFunctionFieldMap_affineCoordinate R R T.torus.left S.torus.left i.left
    (𝟙 R)
  rw [Spec.map_id, Category.id_comp]
  exact congrArg (fun g => g.left) hi

end PaperVerification.ToricSchemes.SplitToricEmbedding

#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.laurentValue_pullback
