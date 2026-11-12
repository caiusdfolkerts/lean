module

public import ToricPower.ToricSectionExtension
public import ToricPower.CoherentEpimorphismLifting
public import ToricPower.BoundedDerivedExtComparison

/-!
# The actual bounded coherent derived embedding for smooth toric varieties

Finite affine-chart generators lift through every quasi-coherent
epimorphism and extend globally after twisting by explicit Cartier
boundaries. This proves the geometric epimorphism-lifting condition.
The actual all-degree Ext maps are therefore bijective, and the literal
bounded derived category of coherent sheaves embeds fully faithfully into
the unbounded derived category of quasi-coherent sheaves.

The theorem applies to noncomplete smooth toric fans and to torus factors.
There is no supplied coherent-resolution or derived-comparison hypothesis.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TauCeti.Toric

namespace ToricPower

universe u v

local instance coherentEmbeddingDerivedCategory (X : Scheme.{u}) [IsLocallyNoetherian X] :
    HasDerivedCategory.{u+1} (Coh X) := HasDerivedCategory.standard _

local instance quasicoherentEmbeddingDerivedCategory (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} (QCoh X) := HasDerivedCategory.standard _

local instance coherentEmbeddingHasExt (X : Scheme.{u}) [IsLocallyNoetherian X] :
    HasExt.{u+1} (Coh X) := hasExt_of_hasDerivedCategory _

local instance quasicoherentEmbeddingHasExt (X : Scheme.{u}) :
    HasExt.{u+1} (QCoh X) := hasExt_of_hasDerivedCategory _

/-- The literal bounded coherent source, followed by the derived functor
of the actual exact inclusion into quasi-coherent sheaves. -/
def boundedCoherentToQuasicoherent (X : Scheme.{u}) [IsLocallyNoetherian X] :
    DbCoh X ⥤ DerivedQCoh X :=
  DerivedCategory.Bounded.ι ⋙ (coherentToQuasicoherent X).mapDerivedCategory

instance (X : Scheme.{u}) [IsLocallyNoetherian X] :
    (boundedCoherentToQuasicoherent X).CommShift ℤ := by
  unfold boundedCoherentToQuasicoherent
  infer_instance

instance (X : Scheme.{u}) [IsLocallyNoetherian X] :
    (boundedCoherentToQuasicoherent X).IsTriangulated := by
  unfold boundedCoherentToQuasicoherent
  infer_instance

variable {N : Type u} {V : Type v} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

/-- The coherent lifting condition is a theorem of actual smooth toric
geometry, obtained from explicit Cartier-boundary section extension. -/
theorem toricCoherentToQuasicoherent_hasEpimorphismLifts
    (fan : Fan i) (nonempty : Nonempty fan.cones) (regular : fan.IsRegular) :
    letI := toricScheme_isNoetherian fan
    HasEpimorphismLifts (coherentToQuasicoherent fan.algebraicRealization) := by
  letI := toricScheme_isNoetherian fan
  letI := toricSchemeIntegral fan nonempty
  let opens := fun σ : fan.cones => (fan.affineToricChartι σ).opensRange
  have covers : TopologicalSpace.IsOpenCover opens :=
    ((toricChartBoundaryAtlas fan regular (Classical.choice nonempty)).cartierEquationAtlas
      nonempty).covers
  apply coherentToQuasicoherent_hasEpimorphismLifts_of_extensions opens covers
    (fun σ => isAffineOpen_opensRange (fan.affineToricChartι σ))
  intro σ M hM s
  exact toricSection_exists_cartier_extension fan nonempty regular σ M s

/-- The exact coherent inclusion preserves every actual extension class. -/
theorem toricCoherentExt_bijective (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) :
    letI := toricScheme_isNoetherian fan
    ∀ (M P : Coh fan.algebraicRealization) (n : ℕ),
      Function.Bijective
        ((coherentToQuasicoherent fan.algebraicRealization).mapExtAddHom M P n) := by
  letI := toricScheme_isNoetherian fan
  exact mapExt_bijective_of_epimorphism_lifts
    (coherentToQuasicoherent fan.algebraicRealization)
    (toricCoherentToQuasicoherent_hasEpimorphismLifts fan nonempty regular)

/-- Full faithfulness for the literal bounded coherent derived category,
proved from geometric lifting and all-degree Ext comparison. -/
def toricBoundedCoherentToQuasicoherentFullyFaithful
    (fan : Fan i) (nonempty : Nonempty fan.cones) (regular : fan.IsRegular) :
    letI := toricScheme_isNoetherian fan
    (boundedCoherentToQuasicoherent fan.algebraicRealization).FullyFaithful := by
  letI := toricScheme_isNoetherian fan
  exact boundedDerivedFullyFaithfulOfEpimorphismLifts
    (coherentToQuasicoherent fan.algebraicRealization)
    (toricCoherentToQuasicoherent_hasEpimorphismLifts fan nonempty regular)

end ToricPower

end
