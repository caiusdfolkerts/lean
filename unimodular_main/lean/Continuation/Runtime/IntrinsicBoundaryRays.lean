module

public import Continuation.Runtime.IntrinsicReconstruction

/-! The exact original signed ray set, defined from all actual boundary
prime valuations. This definition is independent of graphicity. -/

@[expose] public noncomputable section
universe u
open AlgebraicGeometry CategoryTheory
namespace PaperVerification.ToricSchemes.SplitToricEmbedding
variable {k : Type u} [Field k] {n : ℕ}
    {X : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n → ℤ)) X]
    [IsIntegral X.left] [Smooth X.hom]
    (T : SplitToricEmbedding k n X)
local instance raySetLocallyNoetherian : IsLocallyNoetherian X.left :=
  LocallyOfFiniteType.isLocallyNoetherian X.hom
/-- Every original signed boundary valuation, with no graphic model. -/
def completeBoundaryRaySet : Set (PaperVerification.ToricGeometry.Lattice n) :=
  Set.range T.boundaryValuation
end PaperVerification.ToricSchemes.SplitToricEmbedding
