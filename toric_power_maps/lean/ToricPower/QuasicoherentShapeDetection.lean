module

public import ToricPower.AffineSectionsDetection
public import ToricPower.JointShapeHomologyDetection

/-!
# Actual affine sections detect maps of quasicoherent complexes

The objects and every differential of a termwise quasicoherent complex
are lifted through the ordinary full inclusion. Exact affine sections
then detect the actual homology maps. No fullness of a derived inclusion
and no boundedness hypothesis enter this argument.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HomologicalComplex TopologicalSpace

namespace ToricPower

universe u v t

variable {X : Scheme.{u}} {J : Type v} {shape : ComplexShape J}

/-- The original complex, lifted degree by degree to the actual full subcategory. -/
def quasicoherentComplexLift (K : HomologicalComplex X.Modules shape)
    (quasicoherent : ∀ q, (K.X q).IsQuasicoherent) : HomologicalComplex (QCoh X) shape where
  X q := ⟨K.X q, quasicoherent q⟩
  d p q := ObjectProperty.homMk (K.d p q)
  shape p q h := by apply ObjectProperty.hom_ext; exact K.shape p q h
  d_comp_d' p q r _ _ := by apply ObjectProperty.hom_ext; exact K.d_comp_d p q r

/-- Its ordinary underlying complex has exactly the original objects and maps. -/
def quasicoherentComplexLiftIso (K : HomologicalComplex X.Modules shape)
    (quasicoherent : ∀ q, (K.X q).IsQuasicoherent) :
    ((quasicoherentInclusion X).mapHomologicalComplex shape).obj
      (quasicoherentComplexLift K quasicoherent) ≅ K :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intros
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl)

variable (k : Type u) [Field k] [X.Over (Spec (.of k))]
  {I : Type t} (U : I → X.Opens) (covering : IsOpenCover U)
  (affine : ∀ i, IsAffineOpen (U i))

include covering affine in
/-- The exact original scalar section maps on an actual affine open
cover detect quasi-isomorphisms in every complex shape. -/
theorem quasicoherent_complex_quasiIso_of_affineSections
    {K L : HomologicalComplex X.Modules shape} (f : K ⟶ L)
    (sourceQCoh : ∀ q, (K.X q).IsQuasicoherent)
    (targetQCoh : ∀ q, (L.X q).IsQuasicoherent)
    (localIso : ∀ i, QuasiIso
      (((FiniteCover.schemeBaseSections k X (U i)).mapHomologicalComplex shape).map f)) :
    QuasiIso f := by
  let Iq := (quasicoherentInclusion X).mapHomologicalComplex shape
  let eK := quasicoherentComplexLiftIso K sourceQCoh
  let eL := quasicoherentComplexLiftIso L targetQCoh
  let fq := Iq.preimage (eK.hom ≫ f ≫ eL.inv)
  let G (i : I) := quasicoherentInclusion X ⋙ FiniteCover.schemeBaseSections k X (U i)
  letI exactLimits (i : I) : PreservesFiniteLimits (G i) :=
    (FiniteCover.schemeBaseSections_exact k X (U i) (affine i)).1
  letI exactColimits (i : I) : PreservesFiniteColimits (G i) :=
    (FiniteCover.schemeBaseSections_exact k X (U i) (affine i)).2
  haveI liftedQuasiIso : QuasiIso fq := by
    apply quasiIso_of_jointly_detect_zero_shape G
      (fun M zero => quasicoherent_isZero_of_affineSections k X U covering affine M zero)
    intro i
    letI := localIso i
    change QuasiIso (((FiniteCover.schemeBaseSections k X (U i)).mapHomologicalComplex
      shape).map (Iq.map fq))
    rw [show Iq.map fq = eK.hom ≫ f ≫ eL.inv from Iq.map_preimage _]
    simp only [Functor.map_comp]
    infer_instance
  haveI compositeQuasiIso : QuasiIso (eK.hom ≫ f ≫ eL.inv) := by
    rw [← Iq.map_preimage (eK.hom ≫ f ≫ eL.inv)]
    exact HomologicalComplex.quasiIso_map_of_preservesHomology fq (quasicoherentInclusion X)
  haveI middleQuasiIso : QuasiIso (f ≫ eL.inv) := quasiIso_of_comp_left eK.hom _
  exact quasiIso_of_comp_right f eL.inv

end ToricPower

end

