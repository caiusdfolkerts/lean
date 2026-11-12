module

public import ToricPower.CellularFiniteResolution
public import ToricPower.ProjectiveCechDerivedComparison
public import ToricPower.ComplexCoconeFunctor
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# A literal relative local-section complex for cellular diagrams

For a subcategory of a local face star, restriction is followed by the
actual signed Hom complex from a projective resolution of the constant
rank-one diagram. The natural map from the value at the initial cell
has a genuine mapping fiber. This relative local-section complex is
defined on arbitrary unbounded complexes. If all coefficients on the
chosen subcategory vanish cohomologically, its projection onto the
initial coefficient is a quasi-isomorphism.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open CochainComplex CochainComplex.HomComplex
open scoped ZeroObject

namespace ToricPower

universe u

section Acyclic

variable {A : Type*} [Category.{u} A] [Abelian A] [HasDerivedCategory A]

/-- The ordinary localization sends every genuinely acyclic complex to zero. -/
theorem derivedComplex_isZero_of_acyclic (K : CochainComplex A ℤ) (hK : K.Acyclic) :
    IsZero (DerivedCategory.Q.obj K) := by
  let z : K ⟶ (0 : CochainComplex A ℤ) := 0
  have : QuasiIso z := by
    rw [quasiIso_iff]
    intro q
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact (hK q).isZero_homology.isIso
      ((HomologicalComplex.homologyFunctor A (.up ℤ) q).map_isZero (isZero_zero _)) _
  exact (asIso (DerivedCategory.Q.map z)).isZero_iff.mpr
    (DerivedCategory.Q.map_isZero (isZero_zero _))

/-- K-projectivity gives actual acyclicity of the complete signed
linear Hom complex, with no bound on the target. -/
theorem linearHomComplex_acyclic_of_target_acyclic (k : Type u) [CommRing k] [Linear k A]
    (P K : CochainComplex A ℤ) [P.IsKProjective] (hK : K.Acyclic) :
    (linearHomComplex k P K).Acyclic := by
  have zeroK := derivedComplex_isZero_of_acyclic K hK
  intro q
  have shifted : IsZero (DerivedCategory.Q.obj (K⟦q⟧)) :=
    ((DerivedCategory.Q.commShiftIso q).app K).isZero_iff.mpr
      ((CategoryTheory.shiftFunctor (DerivedCategory A) q).map_isZero zeroK)
  letI : Subsingleton (DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj (K⟦q⟧)) :=
    ⟨fun f g => shifted.eq_of_tgt f g⟩
  letI : Subsingleton (CohomologyClass P K q) :=
    (homClassDerivedEquiv P K q).injective.subsingleton
  letI : Subsingleton ((linearHomComplex k P K).homology q) :=
    (HomComplex.homologyLinearEquiv k P K q).injective.subsingleton
  exact (HomologicalComplex.exactAt_iff_isZero_homology _ q).mpr
    (ModuleCat.isZero_of_subsingleton _)

end Acyclic

section Evaluation

variable {C D : Type*} [Category C] [Category D] [Abelian D]

/-- Acyclicity of full complexes of diagrams is detected at all objects. -/
theorem diagramComplex_acyclic_of_evaluation
    (K : CochainComplex (C ⥤ D) ℤ) (h : ∀ c, (K.asFunctor.obj c).Acyclic) : K.Acyclic := by
  let z : K ⟶ (0 : CochainComplex (C ⥤ D) ℤ) := 0
  have : QuasiIso z := by
    rw [HomologicalComplex.quasiIso_iff_evaluation]
    intro c
    rw [quasiIso_iff]
    intro q
    apply (quasiIsoAt_iff_exactAt' _ q
      (HomologicalComplex.acyclic_of_isZero
        _
        ((((evaluation C D).obj c).mapHomologicalComplex (.up ℤ)).map_isZero
          (isZero_zero _)) q)).mpr
    exact h c q
  intro q
  exact (quasiIsoAt_iff_exactAt' z q
    (HomologicalComplex.acyclic_of_isZero _ (isZero_zero _) q)).mp inferInstance

end Evaluation

namespace Cellular

variable (k : Type u) [Field k]
  {C H : Type u} [Category.{u} C] [Category.{u} H]
  (j : H ⥤ C) (c : C) (arrows : (Functor.const H).obj c ⟶ j)

/-- The actual constant rank-one coefficient diagram. -/
def localConstantDiagram : H ⥤ ModuleCat.{u} k :=
  (Functor.const H).obj (ModuleCat.of k k)

/-- Restriction along the actual face inclusion. -/
def localDiagramRestriction : (C ⥤ ModuleCat.{u} k) ⥤ H ⥤ ModuleCat.{u} k :=
  (Functor.whiskeringLeft H C (ModuleCat.{u} k)).obj j

instance localDiagramRestriction_additive : (localDiagramRestriction k j).Additive := by
  unfold localDiagramRestriction
  infer_instance

instance localDiagramRestriction_limits : PreservesFiniteLimits (localDiagramRestriction k j) := by
  unfold localDiagramRestriction
  infer_instance

instance localDiagramRestriction_colimits : PreservesFiniteColimits (localDiagramRestriction k j) := by
  unfold localDiagramRestriction
  infer_instance

/-- An initial coefficient determines a genuine section of the
restricted diagram by all of its actual incidence maps. -/
def initialCoefficientSection (F : C ⥤ ModuleCat.{u} k) (x : F.obj c) :
    localConstantDiagram k (H := H) ⟶ j ⋙ F where
  app h := ModuleCat.ofHom (LinearMap.toSpanSingleton k (F.obj (j.obj h))
    (F.map (arrows.app h) x))
  naturality {h h'} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change k at r
    have incidence : arrows.app h ≫ j.map f = arrows.app h' := by
      have natural := (arrows.naturality f).symm
      change arrows.app h ≫ j.map f = (𝟙 c) ≫ arrows.app h' at natural
      simpa only [Category.id_comp] using natural
    have value := ConcreteCategory.congr_hom (F.map_comp (arrows.app h) (j.map f)) x
    rw [incidence] at value
    change r • F.map (arrows.app h') x = F.map (j.map f) (r • F.map (arrows.app h) x)
    rw [map_smul (F.map (j.map f)).hom]
    exact congrArg (fun y => r • y) value

/-- The actual scalar-linear section map, natural in every coefficient diagram. -/
def initialCoefficientSectionNatTrans :
    (evaluation C (ModuleCat.{u} k)).obj c ⟶
      ordinaryProjectiveCoefficients k (localDiagramRestriction k j)
        (Z := localConstantDiagram k (H := H)) where
  app F := ModuleCat.ofHom
    { toFun := initialCoefficientSection k j c arrows F
      map_add' x y := by
        apply NatTrans.ext
        funext h
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro r
        change k at r
        change r • F.map (arrows.app h) (x+y) =
          r • F.map (arrows.app h) x + r • F.map (arrows.app h) y
        rw [map_add (F.map (arrows.app h)).hom,smul_add]
      map_smul' a x := by
        apply NatTrans.ext
        funext h
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro r
        change k at r
        change r • F.map (arrows.app h) (a • x) = a • (r • F.map (arrows.app h) x)
        rw [map_smul (F.map (arrows.app h)).hom,smul_comm] }
  naturality {F G} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply NatTrans.ext
    funext h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change k at r
    have value := ConcreteCategory.congr_hom (f.naturality (arrows.app h)) x
    change r • G.map (arrows.app h) (f.app c x) =
      f.app (j.obj h) (r • F.map (arrows.app h) x)
    rw [map_smul (f.app (j.obj h)).hom]
    exact congrArg (fun y => r • y) value.symm

/-- A genuine projective resolution of the full constant diagram. -/
def localSectionResolution : ProjectiveResolution (localConstantDiagram k (H := H)) :=
  diagramProjectiveResolution k (localConstantDiagram k)

/-- The actual signed derived-section complex, before localization. -/
def localSectionComplexFunctor :
    CochainComplex (C ⥤ ModuleCat.{u} k) ℤ ⥤ CochainComplex (ModuleCat.{u} k) ℤ :=
  projectiveCoefficientComplexFunctor k (localDiagramRestriction k j)
    (localSectionResolution k (H := H))

/-- The literal restriction map from the initial coefficient to the
derived section complex of the chosen face region. -/
def localSectionComparison :
    ((evaluation C (ModuleCat.{u} k)).obj c).mapHomologicalComplex (.up ℤ) ⟶
      localSectionComplexFunctor k j :=
  NatTrans.mapHomologicalComplex (initialCoefficientSectionNatTrans k j c arrows) (.up ℤ) ≫
    projectiveCoefficientComplexUnit k (localDiagramRestriction k j)
      (localSectionResolution k (H := H))

/-- The actual relative local-section (Morse) complex. -/
def localMorseComplexFunctor :
    CochainComplex (C ⥤ ModuleCat.{u} k) ℤ ⥤ CochainComplex (ModuleCat.{u} k) ℤ :=
  ComplexCone.coconeFunctor (localSectionComparison k j c arrows)

/-- Its genuine, natural map to the initial coefficient complex. -/
def localMorseProjection :
    localMorseComplexFunctor k j c arrows ⟶
      ((evaluation C (ModuleCat.{u} k)).obj c).mapHomologicalComplex (.up ℤ) :=
  ComplexCone.coconeProjection (localSectionComparison k j c arrows)

local instance : HasDerivedCategory.{u+1} (H ⥤ ModuleCat.{u} k) :=
  HasDerivedCategory.standard _
local instance : HasDerivedCategory.{u+1} (ModuleCat.{u} k) :=
  HasDerivedCategory.standard _

/-- Vanishing of every actual coefficient on the region makes its
complete derived-section complex acyclic. -/
theorem localSectionComplex_acyclic_of_coefficients
    (K : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ)
    (vanishes : ∀ h : H, (K.asFunctor.obj (j.obj h)).Acyclic) :
    ((localSectionComplexFunctor k j).obj K).Acyclic := by
  apply linearHomComplex_acyclic_of_target_acyclic
  apply diagramComplex_acyclic_of_evaluation
  exact vanishes

/-- At a maximal support stratum, the relative local-section complex
is genuinely quasi-isomorphic to the nonzero initial coefficient. -/
theorem localMorseProjection_quasiIso_of_coefficients
    (K : CochainComplex (C ⥤ ModuleCat.{u} k) ℤ)
    (vanishes : ∀ h : H, (K.asFunctor.obj (j.obj h)).Acyclic) :
    QuasiIso ((localMorseProjection k j c arrows).app K) := by
  let φ := (localSectionComparison k j c arrows).app K
  have zero := derivedComplex_isZero_of_acyclic ((localSectionComplexFunctor k j).obj K)
    (localSectionComplex_acyclic_of_coefficients k j K vanishes)
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  exact (Triangle.isZero₃_iff_isIso₁
    (DerivedCategory.Q.mapTriangle.obj (mappingCocone.triangle φ))
    (DerivedCategory.mappingCocone_triangle_distinguished φ)).mp zero

end Cellular

end ToricPower

end
