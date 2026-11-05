import OAI.AlgebraicTopology.Cohomology.Singular.Coefficients

/-!
# Singular cohomology of the empty space

The argument uses actual singular simplices. A simplex has a vertex, so an
empty space has no singular simplices in any degree. Its whole cochain complex
is therefore zero. The cochain proof is the generic argument in the pinned
OpenAI Math `Duality/Poincare/CompactSupportCohomology.lean`; no compact-support
theory is required here. See the accompanying third-party attribution.
-/

namespace PaperVerification.EmptySingularCohomology

noncomputable section

open CategoryTheory CategoryTheory.Limits
open OAI.AlgebraicTopology.Cohomology.Singular

variable {R : Type} [Ring R] (M : ModuleCat.{0} R) (X : TopCat.{0}) [IsEmpty X]

theorem cochains_isZero : IsZero (Basic.singularCochains M X) := by
  apply (IsZero.iff_id_eq_zero _).2
  apply HomologicalComplex.hom_ext
  intro n
  have : IsEmpty (Basic.singularSimplices X n) := ⟨fun s =>
    isEmptyElim (Coefficients.singularSimplicesEquivContinuousMap X n s
      (Convexity.StdSimplex.single (R := ℝ) (0 : Fin (n + 1))))⟩
  exact ((ModuleCat.isZero_of_subsingleton
    (ModuleCat.of R (Basic.singularSimplices X n → M))).of_iso
      (Coefficients.singularDegreewiseFunctionIso M X n)).eq_of_tgt _ _

/-- The statement includes degree zero. -/
theorem cohomology_isZero (n : ℕ) : IsZero (Basic.singularCohomology M X n) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (ComplexShape.up ℕ) n).map_isZero (cochains_isZero M X)

end
end PaperVerification.EmptySingularCohomology
