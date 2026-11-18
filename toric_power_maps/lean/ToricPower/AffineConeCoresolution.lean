module

public import ToricPower.ComplexCoconeFunctor
public import ToricPower.QuasicoherentOpenBaseChange
public import ToricPower.DerivedOpenCoverDetection

/-!
# A finite functorial coresolution from an affine open cover

For an affine open immersion `j`, the fiber of the unit
`K → j_*j^*K` vanishes after restriction to that open. Base change shows
that it retains every open on which `K` already vanished. Applying these
fibers for a finite cover therefore gives an acyclic complex. The cone of
its natural map to `K` is the resulting functorial coresolution of `K`.

All complexes here may be unbounded. This file establishes the actual
coaugmentation and its quasi-isomorphism; the acyclicity after applying a
particular Hom functor is a separate theorem.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
  CategoryTheory.Pretriangulated CochainComplex TopologicalSpace
open scoped ZeroObject

namespace ToricPower

universe u v

local instance affineConeDerivedCategory (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} (QCoh X) := HasDerivedCategory.standard _

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [IsAffineHom j]

/-- The actual exact open-localization endofunctor. -/
def quasicoherentOpenLocalization : QCoh X ⥤ QCoh X :=
  quasicoherentRestriction j ⋙ quasicoherentAffinePushforward j

instance : (quasicoherentOpenLocalization j).Additive := by
  unfold quasicoherentOpenLocalization
  infer_instance

instance : PreservesFiniteLimits (quasicoherentOpenLocalization j) := by
  unfold quasicoherentOpenLocalization
  infer_instance

instance : PreservesFiniteColimits (quasicoherentOpenLocalization j) := by
  unfold quasicoherentOpenLocalization
  infer_instance

/-- The restriction-adjunction unit, applied termwise to arbitrary complexes. -/
def openLocalizationComplexUnit :
    𝟭 (CochainComplex (QCoh X) ℤ) ⟶
      (quasicoherentOpenLocalization j).mapHomologicalComplex (.up ℤ) where
  app K :=
    { f := fun p => (quasicoherentOpenAdjunction j).unit.app (K.X p)
      comm' := fun p q _ =>
        ((quasicoherentOpenAdjunction j).unit.naturality (K.d p q)).symm }
  naturality {_ _} f := by
    apply HomologicalComplex.Hom.ext
    funext p
    exact (quasicoherentOpenAdjunction j).unit.naturality (f.f p)

/-- The actual mapping fiber of the open-localization unit. -/
def openFiberComplexFunctor :
    CochainComplex (QCoh X) ℤ ⥤ CochainComplex (QCoh X) ℤ :=
  ComplexCone.coconeFunctor (openLocalizationComplexUnit j)

/-- The original mapping-fiber projection, naturally in the input complex. -/
def openFiberComplexProjection : openFiberComplexFunctor j ⟶ 𝟭 _ :=
  ComplexCone.coconeProjection (openLocalizationComplexUnit j)

/-- Restriction of the actual unit is already an isomorphism of complexes,
by the ordinary open-immersion adjunction and its triangle identity. -/
theorem openLocalizationComplexUnit_restrict_isIso
    (K : CochainComplex (QCoh X) ℤ) :
    IsIso (((quasicoherentRestriction j).mapHomologicalComplex (.up ℤ)).map
      ((openLocalizationComplexUnit j).app K)) := by
  letI : ∀ p, IsIso
      ((((quasicoherentRestriction j).mapHomologicalComplex (.up ℤ)).map
        ((openLocalizationComplexUnit j).app K)).f p) := fun p => by
    change IsIso ((quasicoherentRestriction j).map
      ((quasicoherentOpenAdjunction j).unit.app (K.X p)))
    infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

/-- One fiber step removes its own open, in the actual derived category. -/
theorem openFiberComplex_restrict_isZero (K : CochainComplex (QCoh X) ℤ) :
    IsZero ((quasicoherentRestriction j).mapDerivedCategory.obj
      (DerivedCategory.Q.obj ((openFiberComplexFunctor j).obj K))) := by
  letI := openLocalizationComplexUnit_restrict_isIso j K
  have hz := ComplexCone.cocone_image_isZero (quasicoherentRestriction j)
    ((openLocalizationComplexUnit j).app K)
  exact ((quasicoherentRestriction j).mapDerivedCategoryFactors.app
    ((openFiberComplexFunctor j).obj K)).isZero_iff.mpr hz

/-- The literal localized complex agrees with restriction followed by
affine direct image on the actual unbounded derived categories. -/
def openLocalizationComplexDerivedIso (K : CochainComplex (QCoh X) ℤ) :
    DerivedCategory.Q.obj
        (((quasicoherentOpenLocalization j).mapHomologicalComplex (.up ℤ)).obj K) ≅
      (quasicoherentAffinePushforward j).mapDerivedCategory.obj
        ((quasicoherentRestriction j).mapDerivedCategory.obj (DerivedCategory.Q.obj K)) :=
  ((quasicoherentOpenLocalization j).mapDerivedCategoryFactors.app K).symm ≪≫
    ((Functor.mapDerivedCategoryCompIso (quasicoherentRestriction j)
      (quasicoherentAffinePushforward j)).app (DerivedCategory.Q.obj K)).symm

/-- A fiber step preserves vanishing on every previously removed open. -/
theorem openFiberComplex_preserves_open_vanishing (V : X.Opens)
    (K : CochainComplex (QCoh X) ℤ)
    (hK : IsZero ((quasicoherentRestriction V.ι).mapDerivedCategory.obj
      (DerivedCategory.Q.obj K))) :
    IsZero ((quasicoherentRestriction V.ι).mapDerivedCategory.obj
      (DerivedCategory.Q.obj ((openFiberComplexFunctor j).obj K))) := by
  let F := (quasicoherentRestriction V.ι).mapDerivedCategory
  let φ := (openLocalizationComplexUnit j).app K
  let T := DerivedCategory.Q.mapTriangle.obj (mappingCocone.triangle φ)
  have hT : T ∈ distTriang (DerivedQCoh X) :=
    DerivedCategory.mappingCocone_triangle_distinguished φ
  have hL : IsZero (F.obj (DerivedCategory.Q.obj
      (((quasicoherentOpenLocalization j).mapHomologicalComplex (.up ℤ)).obj K))) :=
    (F.mapIso (openLocalizationComplexDerivedIso j K)).isZero_iff.mpr
      (quasicoherentOpenPushRestriction_isZero j V (DerivedCategory.Q.obj K) hK)
  exact Triangle.isZero₁_of_isZero₂₃ (F.mapTriangle.obj T)
    (F.map_distinguished T hT) hK hL

section FiniteCover

variable {I : Type v} (V : I → X.Opens) [∀ i, IsAffineHom (V i).ι]

/-- The finite iterated fiber and its natural comparison with the input.
The list records the actual opens, with repetitions permitted. -/
def openFiberStage : (l : List I) →
    Σ F : CochainComplex (QCoh X) ℤ ⥤ CochainComplex (QCoh X) ℤ, F ⟶ 𝟭 _
  | [] => ⟨𝟭 _, 𝟙 _⟩
  | i :: l =>
      let S := openFiberStage l
      ⟨S.1 ⋙ openFiberComplexFunctor (V i).ι,
        { app K := (openFiberComplexProjection (V i).ι).app (S.1.obj K) ≫ S.2.app K
          naturality {K L} f := by
            dsimp only [Functor.comp_map]
            rw [← Category.assoc, (openFiberComplexProjection (V i).ι).naturality]
            simp only [Functor.id_map, Category.assoc]
            rw [S.2.naturality]
            rfl }⟩

/-- After the listed steps, all their opens have vanished. -/
theorem openFiberStage_restrict_isZero (l : List I)
    (K : CochainComplex (QCoh X) ℤ) (i : I) (hi : i ∈ l) :
    IsZero ((quasicoherentRestriction (V i).ι).mapDerivedCategory.obj
      (DerivedCategory.Q.obj ((openFiberStage V l).1.obj K))) := by
  induction l with
  | nil => simp only [List.not_mem_nil] at hi
  | cons a l ih =>
      rcases List.mem_cons.mp hi with h | h
      · subst i
        exact openFiberComplex_restrict_isZero (V a).ι ((openFiberStage V l).1.obj K)
      · exact openFiberComplex_preserves_open_vanishing (V a).ι (V i)
          ((openFiberStage V l).1.obj K) (ih h)

/-- A finite cover removes all support; the resulting complex is acyclic. -/
theorem openFiberStage_isZero (l : List I) (hl : ∀ i, i ∈ l)
    (hV : IsOpenCover V) (K : CochainComplex (QCoh X) ℤ) :
    IsZero (DerivedCategory.Q.obj ((openFiberStage V l).1.obj K)) :=
  quasicoherentDerived_isZero_of_openCover V hV _
    (fun i => openFiberStage_restrict_isZero V l K i (hl i))

/-- The actual finite cone coresolution. -/
def affineConeCoresolution (l : List I) :
    CochainComplex (QCoh X) ℤ ⥤ CochainComplex (QCoh X) ℤ :=
  ComplexCone.coneFunctor (openFiberStage V l).2

/-- Its natural coaugmentation from the original complex. -/
def affineConeCoaugmentation (l : List I) :
    𝟭 (CochainComplex (QCoh X) ℤ) ⟶ affineConeCoresolution V l :=
  ComplexCone.coneInclusion (openFiberStage V l).2

/-- The finite coaugmentation is a genuine quasi-isomorphism on every
unbounded quasicoherent complex, with the covering hypothesis discharged. -/
theorem affineConeCoaugmentation_quasiIso (l : List I) (hl : ∀ i, i ∈ l)
    (hV : IsOpenCover V) (K : CochainComplex (QCoh X) ℤ) :
    QuasiIso ((affineConeCoaugmentation V l).app K) := by
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  exact (Triangle.isZero₁_iff_isIso₂
    (DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle ((openFiberStage V l).2.app K)))
    (DerivedCategory.mappingCone_triangle_distinguished _)).mp
      (openFiberStage_isZero V l hl hV K)

end FiniteCover

end ToricPower

end
