module

public import Continuation.Runtime.InvariantCoordinateCharts
public import Continuation.Runtime.ActualCoordinateFanIso

/-!
# The fan of an independently specified smooth complete toric variety

Starting with the actual scheme, its structure morphism and its specified
dense equivariant split torus, we construct an isomorphism from a smooth
complete fan scheme.  No projectivity, ample sheaf, invariant affine
cover, fan, or rational polyhedral decomposition is an input.

The construction proceeds through invariant affine neighbourhoods, their
literal character algebras, common-face overlaps and the valuative
criterion using real Hahn-series valuations.  Thus completeness covers
all real directions, including irrational ones.  The isomorphism is over
the original field and fixes the original torus coordinates.

This source endpoint awaits native checking of the complete dependency
chain.  Its presence is not a verification receipt.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricGeometry

namespace PaperVerification.ToricSchemes.SplitToricEmbedding

variable {k : Type u} [Field k] {n : ℕ}
    {X : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n → ℤ)) X]
    [IsIntegral X.left] [Smooth X.hom] [IsProper X.hom]
    (T : SplitToricEmbedding k n X)

/-- Every original smooth complete split toric variety is its actual
smooth complete fan scheme, compatibly with the specified dense torus.
The dimension may be zero and the ground field is arbitrary. -/
theorem exists_fan_of_complete :
    ∃ (F : SmoothCompleteFan n) (e : F.fanSchemeOver k ≅ X),
      (F.intrinsicToricEmbedding k).torus ≫ e.hom = T.torus := by
  letI : IsLocallyNoetherian X.left :=
    LocallyOfFiniteType.isLocallyNoetherian X.hom
  letI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  letI : IsNoetherian X.left := {}
  letI : X.left.IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from X.hom]
    infer_instance⟩
  obtain ⟨C⟩ := T.nonempty_coordinateChartCover
  have hj : T.torus.left ≫ X.hom = Spec.map (CommRingCat.ofHom
      (algebraMap k (AddMonoidAlgebra k (Lattice n)))) := T.torus.w
  obtain ⟨F, e, hbase, htorus⟩ := C.exists_fan_presentation X.hom hj
  let eOver : F.fanSchemeOver k ≅ X := Over.isoMk e hbase
  refine ⟨F, eOver, ?_⟩
  apply Over.OverMorphism.ext
  exact htorus

end PaperVerification.ToricSchemes.SplitToricEmbedding

#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.exists_fan_of_complete
