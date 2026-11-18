module

public import ToricPower.AffineConeCoresolution
public import ToricPower.ComplexConeFiltration
public import ToricPower.ComplexCoconeNaturality

/-!
# The finite affine coresolution on arbitrary morphisms

An additive functor that is exact after each affine-open localization
carries our finite coresolution to a functor preserving all quasi-
isomorphisms. This constructs its actual localization on unbounded
quasicoherent derived categories. The absolute right-derived universal
property is established separately, after the resolved-object comparison.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
  CategoryTheory.Pretriangulated CochainComplex

namespace ToricPower

universe u v w z

local instance affineConeStageDerivedCategory (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} (QCoh X) := HasDerivedCategory.standard _

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [IsAffineHom j]

/-- Every fiber step preserves actual quasi-isomorphisms. -/
theorem openFiberComplex_map_quasiIso
    {K L : CochainComplex (QCoh X) ℤ} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso ((openFiberComplexFunctor j).map f) := by
  let τ := openLocalizationComplexUnit j
  have h := ComplexCone.additive_cone_map_quasiIso (𝟭 (QCoh X))
    (τ.app K) (τ.app L) f
    (((quasicoherentOpenLocalization j).mapHomologicalComplex (.up ℤ)).map f)
    (τ.naturality f).symm
  letI : QuasiIso ((ComplexCone.coneFunctor τ).map f) := h
  change QuasiIso (((ComplexCone.coneFunctor τ).map f)⟦(-1 : ℤ)⟧')
  infer_instance

variable {I : Type v} (V : I → X.Opens) [∀ i, IsAffineHom (V i).ι]

/-- Iterated fibers retain preservation of quasi-isomorphisms. -/
theorem openFiberStage_map_quasiIso (l : List I)
    {K L : CochainComplex (QCoh X) ℤ} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso ((openFiberStage V l).1.map f) := by
  induction l with
  | nil => exact inferInstanceAs (QuasiIso f)
  | cons i l ih =>
      letI := ih
      exact openFiberComplex_map_quasiIso (V i).ι ((openFiberStage V l).1.map f)

@[simp]
theorem openFiberStage_cons_projection (i : I) (l : List I)
    (K : CochainComplex (QCoh X) ℤ) :
    (openFiberStage V (i :: l)).2.app K =
      (openFiberComplexProjection (V i).ι).app ((openFiberStage V l).1.obj K) ≫
        (openFiberStage V l).2.app K := rfl

variable {D : Type w} [Category.{z} D] [Abelian D] [HasDerivedCategory D]
  (H : QCoh X ⥤ D) [H.Additive]
  [∀ i, PreservesFiniteLimits (quasicoherentOpenLocalization (V i).ι ⋙ H)]
  [∀ i, PreservesFiniteColimits (quasicoherentOpenLocalization (V i).ι ⋙ H)]

/-- The finite coresolution becomes homotopical after an additive functor
which is exact on every localized piece. This holds for every stage and
therefore does not use a covering or boundedness hypothesis. -/
theorem affineConeCoresolution_map_quasiIso (l : List I)
    {K L : CochainComplex (QCoh X) ℤ} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso ((H.mapHomologicalComplex (.up ℤ)).map
      ((affineConeCoresolution V l).map f)) := by
  induction l with
  | nil =>
      rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
      exact (ComplexCone.additive_cone_identity_isZero H K).isIso
        (ComplexCone.additive_cone_identity_isZero H L) _
  | cons i l ih =>
      let S := openFiberStage V l
      let τ := openLocalizationComplexUnit (V i).ι
      let p := openFiberComplexProjection (V i).ι
      letI := openFiberStage_map_quasiIso V l f
      letI : QuasiIso ((H.mapHomologicalComplex (.up ℤ)).map
          (((quasicoherentOpenLocalization (V i).ι).mapHomologicalComplex (.up ℤ)).map
            (S.1.map f))) := by
        change QuasiIso (((quasicoherentOpenLocalization (V i).ι ⋙ H).mapHomologicalComplex
          (.up ℤ)).map (S.1.map f))
        infer_instance
      letI : QuasiIso ((H.mapHomologicalComplex (.up ℤ)).map
          (mappingCone.map (p.app (S.1.obj K)) (p.app (S.1.obj L))
            ((openFiberComplexFunctor (V i).ι).map (S.1.map f)) (S.1.map f)
            (p.naturality (S.1.map f)).symm)) :=
        ComplexCone.additive_fiberProjectionCone_map_quasiIso H τ (S.1.map f)
      letI : QuasiIso ((H.mapHomologicalComplex (.up ℤ)).map
        (mappingCone.map (S.2.app K) (S.2.app L) (S.1.map f) f (S.2.naturality f).symm)) := ih
      have h := ComplexCone.additive_map_compositeCone_quasiIso
        (p.app (S.1.obj K)) (S.2.app K) (p.app (S.1.obj L)) (S.2.app L)
        ((openFiberComplexFunctor (V i).ι).map (S.1.map f)) (S.1.map f) f
        (p.naturality (S.1.map f)).symm (S.2.naturality f).symm H
      exact h

/-- The actual localization of the resolved additive functor. -/
def affineConeDerivedStage (l : List I) : DerivedQCoh X ⥤ DerivedCategory D :=
  Localization.lift (W := HomologicalComplex.quasiIso (QCoh X) (.up ℤ))
    (affineConeCoresolution V l ⋙ H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (fun K L f hf => by
      letI : QuasiIso f := hf
      letI := affineConeCoresolution_map_quasiIso V H l f
      exact (inferInstance : IsIso (DerivedCategory.Q.map
        ((H.mapHomologicalComplex (.up ℤ)).map ((affineConeCoresolution V l).map f)))))
    DerivedCategory.Q

/-- Its canonical, universal localization factorization. -/
def affineConeDerivedStageFactors (l : List I) :
    DerivedCategory.Q ⋙ affineConeDerivedStage V H l ≅
      affineConeCoresolution V l ⋙ H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  Localization.fac _ _ _

end ToricPower

end
