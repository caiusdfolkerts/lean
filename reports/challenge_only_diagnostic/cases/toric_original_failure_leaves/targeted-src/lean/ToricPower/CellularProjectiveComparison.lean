module

public import ToricPower.CellularLinearDensityExtension
public import ToricPower.NaturalComplexCoproductComparison

/-!
# Original natural comparisons on all projective diagrams

A quasi-isomorphism on every free representable extends to every
projective diagram, using unrestricted basis coproducts and the actual
vector-cover retraction. An epimorphism on those representables extends
to every diagram by the genuine linear density generators.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace ToricPower.Cellular

universe u v

variable (k : Type u) [Field k] {C : Type u} [Category.{u} C]

/-- The actual vector cover splits for every projective diagram. -/
def projectiveVectorCoverRetract (M : C ⥤ ModuleCat.{u} k) [Projective M] :
    Retract M (diagramVectorCoverObj k M) where
  i := Projective.factorThru (𝟙 M) (diagramVectorCoverMap k M)
  r := diagramVectorCoverMap k M
  retract := Projective.factorThru_comp _ _

section QuasiIsomorphisms

variable {A : Type v} [Category.{u} A] [Abelian A]
  [HasCoproducts.{u} A] [AB4OfSize.{u} A]
  {ι : Type u} {shape : ComplexShape ι}
  {Φ Ψ : (C ⥤ ModuleCat.{u} k) ⥤ HomologicalComplex A shape}
  [PreservesColimitsOfSize.{u,u} Φ] [PreservesColimitsOfSize.{u,u} Ψ]
  (τ : Φ ⟶ Ψ) (represented : ∀ c, QuasiIso (τ.app (representable k c)))

include represented in
/-- Unrestricted coefficient copowers retain the original comparison. -/
theorem naturalComparison_vectorCopower_quasiIso (c : C) (V : ModuleCat.{u} k) :
    QuasiIso (τ.app (vectorCopower k (representable k c) V)) := by
  letI : QuasiIso (τ.app (representable k c)) := represented c
  exact naturalComparison_coproduct_quasiIso τ
    (fun _ : Module.Free.ChooseBasisIndex k V => representable k c)

include represented in
/-- The comparison on the full genuine cover is a quasi-isomorphism. -/
theorem naturalComparison_vectorCover_quasiIso (M : C ⥤ ModuleCat.{u} k) :
    QuasiIso (τ.app (diagramVectorCoverObj k M)) := by
  letI (c : C) : QuasiIso (τ.app (vectorCopower k (representable k c) (M.obj c))) :=
    naturalComparison_vectorCopower_quasiIso k τ represented c (M.obj c)
  exact naturalComparison_coproduct_quasiIso τ
    (fun c : C => vectorCopower k (representable k c) (M.obj c))

include represented in
/-- Every projective diagram is covered, including infinite-dimensional
ones. The conclusion is about the specified natural transformation. -/
theorem naturalComparison_projective_quasiIso
    (M : C ⥤ ModuleCat.{u} k) [Projective M] : QuasiIso (τ.app M) := by
  letI : QuasiIso (τ.app (diagramVectorCoverObj k M)) :=
    naturalComparison_vectorCover_quasiIso k τ represented M
  exact quasiIso_of_retractArrow (τ.retractArrowApp (projectiveVectorCoverRetract k M))

end QuasiIsomorphisms

section Epimorphisms

variable {B : Type v} [Category.{u} B] [Preadditive B] [Linear k B]
  [HasColimitsOfSize.{u,u} B]
  {Φ Ψ : (C ⥤ ModuleCat.{u} k) ⥤ B}
  [Ψ.Additive] [Ψ.Linear k] [PreservesColimitsOfSize.{u,u} Ψ]
  (τ : Φ ⟶ Ψ) (represented : ∀ c, Epi (τ.app (representable k c)))

include represented in
/-- Density detects epimorphisms on all diagrams, with no projectivity
or finite-dimensional hypothesis on the diagram. -/
theorem naturalComparison_epi_of_representables (M : C ⥤ ModuleCat.{u} k) :
    Epi (τ.app M) := by
  constructor
  intro E f g equal
  apply mappedRepresentables_hom_ext k Ψ
  intro c x
  letI : Epi (τ.app (representable k c)) := represented c
  apply (cancel_epi (τ.app (representable k c))).mp
  have left := congrArg (fun h => h ≫ f) (τ.naturality (fromValue k M c x))
  have right := congrArg (fun h => h ≫ g) (τ.naturality (fromValue k M c x))
  simp only [Category.assoc] at left right
  exact left.symm.trans ((congrArg (fun h => Φ.map (fromValue k M c x) ≫ h) equal).trans right)

end Epimorphisms

end ToricPower.Cellular

end
