module

public import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Scheme

/-!
# A zero vector space has empty projective spectrum

The argument uses the actual irrelevant homogeneous ideal: every one of its
module generators vanishes, contradicting the defining condition on a Proj point.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.SymmetricProjectiveEmpty

open AlgebraicGeometry
open OAI.AlgebraicGeometry.Divisors.LineBundles
open SymmetricProjective.Scheme.BundleCycles

theorem symmetricProjective_isEmpty_of_subsingleton (R M : Type)
    [CommRing R] [AddCommGroup M] [Module R M] [Subsingleton M] :
    IsEmpty (symmetricProjectiveScheme R M) := by
  refine ⟨fun x => x.not_irrelevant_le ?_⟩
  change (HomogeneousIdeal.irrelevant
    (Symmetric.Grading.BundleCycles.symmetricGrading R M)).toIdeal ≤
      x.asHomogeneousIdeal.toIdeal
  rw [Symmetric.GradingIdeals.BundleCycles.symmetricIrrelevant_eq_generatorIdeal]
  apply Ideal.span_le.mpr
  rintro a ⟨m,rfl⟩
  rw [Subsingleton.elim m 0, map_zero]
  exact Ideal.zero_mem _

end PaperVerification.SymmetricProjectiveEmpty
