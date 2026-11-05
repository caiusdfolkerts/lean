import OAI.AlgebraicTopology.Cohomology.Singular.RelativeSequence

/-!
# The actual relative cohomology of a space relative to itself

Restriction to the whole subspace is an isomorphism of singular cochain
complexes. Its kernel is therefore zero in every degree. This also handles
an empty geometric stratum when its open complement is the entire space.
-/

namespace PaperVerification.RelativeCohomologyWhole

noncomputable section

open CategoryTheory CategoryTheory.Limits
open OAI.AlgebraicTopology.Cohomology.Singular
open OAI.AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles

variable {R : Type} [Ring R] (M : ModuleCat.{0} R) (X : TopCat.{0})

/-- The literal whole-subspace inclusion is the hom of this topological
isomorphism; no replacement of the underlying space is made. -/
def wholeSubspaceIso : TopCat.of (Set.univ : Set X) ≅ X where
  hom := subspaceInclusion X Set.univ
  inv := TopCat.ofHom ⟨fun x => ⟨x, Set.mem_univ x⟩,
    continuous_id.subtype_mk _⟩
  hom_inv_id := by ext x; rfl
  inv_hom_id := by ext x; rfl

instance wholeSubspaceInclusion_isIso :
    IsIso (subspaceInclusion X Set.univ) :=
  inferInstanceAs (IsIso (wholeSubspaceIso X).hom)

instance wholeSubspaceRestriction_isIso :
    IsIso (RelativeSequence.subspaceCochainRestriction M X Set.univ) := by
  change IsIso ((Functor.singularCochainsFunctor M).map
    (subspaceInclusion X Set.univ).op)
  infer_instance

theorem relativeCochains_univ_isZero :
    IsZero (RelativeSequence.relativeSingularCochains M X Set.univ) :=
  isZero_kernel_of_mono (RelativeSequence.subspaceCochainRestriction M X Set.univ)

/-- All genuine relative singular groups of `(X,X)` vanish. -/
theorem relativeCohomology_univ_isZero (n : ℕ) :
    IsZero (RelativeSequence.relativeSingularCohomology M X Set.univ n) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (ComplexShape.up ℕ) n).map_isZero (relativeCochains_univ_isZero M X)

end
end PaperVerification.RelativeCohomologyWhole
