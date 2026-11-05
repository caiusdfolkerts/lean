module

public import PaperVerification.ToricIntrinsicFanClassification
public import PaperVerification.ToricFanDimension

@[expose] public section

/-!
# Torus rank equals the ordinary dimension of the intrinsic scheme

The reconstructed fan is only an intermediate object. The conclusion
identifies the original scheme's topological Krull dimension with the
rank of its actual dense split torus.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes.SplitToricEmbedding

open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
open PaperVerification.ToricCharacters PaperVerification.ToricGeometry

variable {k : Type u} [Field k] {n : ℕ}
    {X : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n → ℤ)) X]
    [IsIntegral X.left] [Smooth X.hom] [IsProper X.hom]
    (T : SplitToricEmbedding k n X)

include T in
/-- The dimension parameter in the intrinsic principal statements is
the usual dimension of the actual scheme. -/
theorem topologicalKrullDim_eq_rank
    (D : CartierData X.left) (hD : D.IsAmple) :
    topologicalKrullDim X.left = n := by
  obtain ⟨P, «Σ», e, hP, hfan, hpure, hbase, htorus⟩ :=
    T.exists_smooth_complete_fan D hD
  rw [← IsHomeomorph.topologicalKrullDim_eq _ e.hom.homeomorph.isHomeomorph]
  exact «Σ».fanScheme_topologicalKrullDim k hpure

include T in
theorem orderKrullDim_eq_rank
    (D : CartierData X.left) (hD : D.IsAmple) :
    Order.krullDim X.left = n := by
  rw [← scheme_topologicalKrullDim_eq_orderKrullDim]
  exact T.topologicalKrullDim_eq_rank D hD

end PaperVerification.ToricSchemes.SplitToricEmbedding

#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.topologicalKrullDim_eq_rank
