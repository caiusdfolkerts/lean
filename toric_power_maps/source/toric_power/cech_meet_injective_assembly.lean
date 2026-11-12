module

public import ToricPower.CechMeetCoefficientComparison
public import ToricPower.RelativeHomPrecompQuasiIso
public import ToricPower.QuasicoherentInjectiveFlasque

/-!
# Actual Čech augmentation on bounded-below injective complexes

The ordered-tuple resolution is applied to the actual chart-section
diagram. Quasicoherent injective sheaves are flasque, so its positive
coefficient rows are exact. The relative Hom construction then proves
that the actual augmentation is a quasi-isomorphism on every bounded-
below complex of injective quasicoherent sheaves.

Affineness is used only for exactness of the chart-section functor; the
augmentation calculation itself requires flasqueness and the displayed
literal intersection identities.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CochainComplex

namespace ToricPower.FiniteCech

variable {B : Type} [SemilatticeInf B] [Finite B]
  (k : Type) [Field k] (X : Scheme) [X.Over (Spec (.of k))]
  (opens : B ⥤ X.Opens)

/-- Restriction of an actual module sheaf to all actual chart sections. -/
def meetChartSectionsFunctor : X.Modules ⥤ Bᵒᵖ ⥤ ModuleCat k :=
  FiniteCover.schemeBasePresheaf k X ⋙
    (Functor.whiskeringLeft Bᵒᵖ X.Opensᵒᵖ (ModuleCat k)).obj opens.op

instance meetChartSectionsFunctor_additive :
    (meetChartSectionsFunctor k X opens).Additive := by
  unfold meetChartSectionsFunctor
  infer_instance

/-- The same literal section diagram, restricted to actual QCoh. -/
def quasicoherentMeetSections : QCoh X ⥤ Bᵒᵖ ⥤ ModuleCat k :=
  quasicoherentInclusion X ⋙ meetChartSectionsFunctor k X opens

instance quasicoherentMeetSections_additive :
    (quasicoherentMeetSections k X opens).Additive := by
  unfold quasicoherentMeetSections
  infer_instance

theorem quasicoherentMeetSections_evaluation (b : Bᵒᵖ) :
    quasicoherentMeetSections k X opens ⋙ (evaluation _ _).obj b =
      quasicoherentInclusion X ⋙ FiniteCover.schemeBaseSections k X (opens.obj b.unop) := rfl

/-- Exactness is proved by the actual affine section functors at every chart. -/
theorem quasicoherentMeetSections_exact (affine : ∀ b, IsAffineOpen (opens.obj b)) :
    PreservesFiniteLimits (quasicoherentMeetSections k X opens) ∧
      PreservesFiniteColimits (quasicoherentMeetSections k X opens) := by
  constructor
  · apply preservesFiniteLimits_of_evaluation
    intro b
    rw [quasicoherentMeetSections_evaluation]
    exact (FiniteCover.schemeBaseSections_exact k X (opens.obj b.unop) (affine _)).1
  · apply preservesFiniteColimits_of_evaluation
    intro b
    rw [quasicoherentMeetSections_evaluation]
    exact (FiniteCover.schemeBaseSections_exact k X (opens.obj b.unop) (affine _)).2

variable (meetEq : ∀ (q : ℕ) (t : Fin (q+1) → B),
    BondalThomsen.FiniteAffineCechHigherComparison.cechIntersection opens.obj q t =
      opens.obj (tupleMeet t))

include meetEq in
/-- Actual flasque sheaves give exact augmented tuple Hom rows. -/
theorem meetSections_augmentationHomExact (M : X.Modules) [M.presheaf.IsFlasque] :
    AugmentationHomExact (projectiveCochain (tupleProjectiveResolution k))
      (tupleAugmented k).right ((meetChartSectionsFunctor k X opens).obj M)
      (projectiveCochainAugmentation (tupleProjectiveResolution k)) := by
  apply projectiveCochain_augmentationHomExact k
  exact meetTupleCoefficient_exactAt_positive k X opens meetEq M

variable [IsLocallyNoetherian X] [CompactSpace X] [X.IsSeparated]

include meetEq in
/-- The actual augmentation comparison is a quasi-isomorphism on every
bounded-below complex of quasicoherent injectives, without a boundedness
assumption on its length above. -/
theorem meetSections_injectiveComplex_augmentation_quasiIso
    (I : CochainComplex (QCoh X) ℤ) (d : ℤ) [I.IsStrictlyGE d]
    [∀ q, Injective (I.X q)] :
    QuasiIso (linearHomComplexPrecomp k
      (projectiveCochainAugmentation (tupleProjectiveResolution k))
      (((quasicoherentMeetSections k X opens).mapHomologicalComplex (.up ℤ)).obj I)) := by
  apply augmentation_linearHomPrecomp_quasiIso k _ _ _ _ d
  intro q
  exact meetSections_augmentationHomExact k X opens meetEq (I.X q).obj

end ToricPower.FiniteCech
