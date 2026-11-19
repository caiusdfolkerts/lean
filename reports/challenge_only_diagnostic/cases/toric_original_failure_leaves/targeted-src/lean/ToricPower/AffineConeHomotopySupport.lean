module

public import ToricPower.AffineConeCoresolution

/-!
# Actual finite affine fibers remove support in the homotopy category

The comparison is stronger than acyclicity: after restriction to every
listed affine open, the actual iterated fiber is contractible. One fiber
step is killed by its own actual restriction-adjunction unit, which is an
isomorphism after restriction. Ordinary open base change preserves all
opens on which the input was already contractible. No boundedness,
injective-resolution existence, or derived acyclicity assumption enters.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
  CategoryTheory.Pretriangulated CochainComplex

namespace ToricPower

universe u v

/-- Transport zero after a functor along an actual object isomorphism.
Keeping this generic avoids unfolding large sheaf functors in the local
support argument. -/
private theorem functor_isZero_of_iso {A B : Type*} [Category A] [Category B]
    (F : A ⥤ B) {M N : A} (e : M ≅ N) (zeroN : IsZero (F.obj N)) :
    IsZero (F.obj M) :=
  (F.mapIso e).isZero_iff.mpr zeroN

section GenericShift

variable {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
  (H : A ⥤ B) [H.Additive] {K L : CochainComplex A ℤ} (f : K ⟶ L)

/-- The genuine shift comparison identifies the image of the original
mapping fiber with the shifted image of its original cone. -/
def homotopyImageMappingCoconeShiftIso :
    (H.mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient A (.up ℤ)).obj (mappingCocone f)) ≅
      ((H.mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient A (.up ℤ)).obj (mappingCone f)))⟦(-1 : ℤ)⟧ :=
  (H.mapHomotopyCategory (.up ℤ)).mapIso
      (((HomotopyCategory.quotient A (.up ℤ)).commShiftIso (-1)).app (mappingCone f)) ≪≫
    ((H.mapHomotopyCategory (.up ℤ)).commShiftIso (-1)).app
      ((HomotopyCategory.quotient A (.up ℤ)).obj (mappingCone f))

theorem homotopyImageMappingCocone_isZero_of_cone
    (zeroCone : IsZero ((H.mapHomotopyCategory (.up ℤ)).obj
      ((HomotopyCategory.quotient A (.up ℤ)).obj (mappingCone f)))) :
    IsZero ((H.mapHomotopyCategory (.up ℤ)).obj
      ((HomotopyCategory.quotient A (.up ℤ)).obj (mappingCocone f))) :=
  (homotopyImageMappingCoconeShiftIso H f).isZero_iff.mpr
    ((CategoryTheory.shiftFunctor _ (-1 : ℤ)).map_isZero zeroCone)

/-- An actual isomorphism of complexes has contractible mapping fiber
under every additive functor that sees that isomorphism. -/
theorem homotopyImageMappingCocone_isZero_of_isIso
    [IsIso ((H.mapHomologicalComplex (.up ℤ)).map f)] :
    IsZero ((H.mapHomotopyCategory (.up ℤ)).obj
      ((HomotopyCategory.quotient A (.up ℤ)).obj (mappingCocone f))) := by
  let HH := H.mapHomotopyCategory (.up ℤ)
  let Q := HomotopyCategory.quotient A (.up ℤ)
  have isomorphism : IsIso (HH.map (Q.map f)) := by
    apply (NatIso.isIso_map_iff (H.mapHomotopyCategoryFactors (.up ℤ)) f).mpr
    change IsIso ((HomotopyCategory.quotient B (.up ℤ)).map
      ((H.mapHomologicalComplex (.up ℤ)).map f))
    infer_instance
  exact homotopyImageMappingCocone_isZero_of_cone H f
    (Triangle.isZero₃_of_isIso₁ (HH.mapTriangle.obj (mappingCone.triangleh f))
      (HH.map_distinguished _ (HomotopyCategory.mappingCone_triangleh_distinguished f))
      isomorphism)

/-- A mapping fiber between two contractible images stays contractible,
with no exactness premise on the additive functor. -/
theorem homotopyImageMappingCocone_isZero_of_endpoints
    (zeroK : IsZero ((H.mapHomotopyCategory (.up ℤ)).obj
      ((HomotopyCategory.quotient A (.up ℤ)).obj K)))
    (zeroL : IsZero ((H.mapHomotopyCategory (.up ℤ)).obj
      ((HomotopyCategory.quotient A (.up ℤ)).obj L))) :
    IsZero ((H.mapHomotopyCategory (.up ℤ)).obj
      ((HomotopyCategory.quotient A (.up ℤ)).obj (mappingCocone f))) := by
  let HH := H.mapHomotopyCategory (.up ℤ)
  exact homotopyImageMappingCocone_isZero_of_cone H f
    (Triangle.isZero₃_of_isZero₁₂ (HH.mapTriangle.obj (mappingCone.triangleh f))
      (HH.map_distinguished _ (HomotopyCategory.mappingCone_triangleh_distinguished f))
      zeroK zeroL)

end GenericShift

variable {U X Y : Scheme.{u}}

/-- Actual ordinary open base change, induced on homotopy categories. -/
def quasicoherentHomotopyRestrictPushforwardIso (f : U ⟶ X) [IsAffineHom f]
    (V : X.Opens) :
    (quasicoherentAffinePushforward f).mapHomotopyCategory (.up ℤ) ⋙
        (quasicoherentRestriction V.ι).mapHomotopyCategory (.up ℤ) ≅
      (quasicoherentRestriction (f ⁻¹ᵁ V).ι).mapHomotopyCategory (.up ℤ) ⋙
        (quasicoherentAffinePushforward (f ∣_ V)).mapHomotopyCategory (.up ℤ) :=
  Functor.mapHomotopyCategoryCompIso (Iso.refl _) (.up ℤ) ≪≫
    NatIso.mapHomotopyCategory (quasicoherentRestrictPushforwardIso f V) (.up ℤ) ≪≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl _) (.up ℤ)).symm

/-- Actual composition of restrictions on homotopy categories. -/
def quasicoherentHomotopyRestrictionCompIso (f : U ⟶ X) (g : X ⟶ Y)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    (quasicoherentRestriction (f ≫ g)).mapHomotopyCategory (.up ℤ) ≅
      (quasicoherentRestriction g).mapHomotopyCategory (.up ℤ) ⋙
        (quasicoherentRestriction f).mapHomotopyCategory (.up ℤ) :=
  NatIso.mapHomotopyCategory (quasicoherentRestrictionCompIso f g) (.up ℤ) ≪≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl _) (.up ℤ)).symm

/-- Actual equality-of-map transport on homotopy categories. -/
def quasicoherentHomotopyRestrictionCongrIso {f g : U ⟶ X} (h : f = g)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    (quasicoherentRestriction f).mapHomotopyCategory (.up ℤ) ≅
      (quasicoherentRestriction g).mapHomotopyCategory (.up ℤ) :=
  NatIso.mapHomotopyCategory (quasicoherentRestrictionCongrIso h) (.up ℤ)

/-- Another affine-open localization cannot create noncontractible
restriction on an open where the original complex was contractible. -/
theorem quasicoherentOpenPushRestriction_homotopy_isZero
    (j : U ⟶ X) [IsOpenImmersion j] [IsAffineHom j] (V : X.Opens)
    (K : HomotopyCategory (QCoh X) (.up ℤ))
    (zeroK : IsZero ((quasicoherentRestriction V.ι).mapHomotopyCategory (.up ℤ) |>.obj K)) :
    IsZero ((quasicoherentRestriction V.ι).mapHomotopyCategory (.up ℤ) |>.obj
      ((quasicoherentAffinePushforward j).mapHomotopyCategory (.up ℤ) |>.obj
        ((quasicoherentRestriction j).mapHomotopyCategory (.up ℤ) |>.obj K))) := by
  let comparison :=
    (quasicoherentHomotopyRestrictionCompIso (j ⁻¹ᵁ V).ι j).symm ≪≫
      quasicoherentHomotopyRestrictionCongrIso (morphismRestrict_ι j V).symm ≪≫
      quasicoherentHomotopyRestrictionCompIso (j ∣_ V) V.ι
  have zeroRestricted : IsZero
      ((quasicoherentRestriction (j ⁻¹ᵁ V).ι).mapHomotopyCategory (.up ℤ) |>.obj
        ((quasicoherentRestriction j).mapHomotopyCategory (.up ℤ) |>.obj K)) :=
    (comparison.app K).isZero_iff.mpr
      ((quasicoherentRestriction (j ∣_ V)).mapHomotopyCategory (.up ℤ) |>.map_isZero zeroK)
  exact ((quasicoherentHomotopyRestrictPushforwardIso j V).app
    ((quasicoherentRestriction j).mapHomotopyCategory (.up ℤ) |>.obj K)).isZero_iff.mpr
      ((quasicoherentAffinePushforward (j ∣_ V)).mapHomotopyCategory (.up ℤ)
        |>.map_isZero zeroRestricted)

variable (j : U ⟶ X) [IsOpenImmersion j] [IsAffineHom j]

/-- The original termwise localization agrees with the two actual
homotopy functors, by their canonical quotient factorizations. -/
def openLocalizationComplexHomotopyIso (K : CochainComplex (QCoh X) ℤ) :
    (HomotopyCategory.quotient (QCoh X) (.up ℤ)).obj
        (((quasicoherentOpenLocalization j).mapHomologicalComplex (.up ℤ)).obj K) ≅
      (quasicoherentAffinePushforward j).mapHomotopyCategory (.up ℤ) |>.obj
        ((quasicoherentRestriction j).mapHomotopyCategory (.up ℤ) |>.obj
          ((HomotopyCategory.quotient (QCoh X) (.up ℤ)).obj K)) :=
  (((quasicoherentOpenLocalization j).mapHomotopyCategoryFactors (.up ℤ)).app K).symm ≪≫
    (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (quasicoherentOpenLocalization j)) (.up ℤ)).symm.app
        ((HomotopyCategory.quotient (QCoh X) (.up ℤ)).obj K)

/-- A fiber step is contractible on its own open, using the literal
restriction of the adjunction unit as an isomorphism of complexes. -/
theorem openFiberComplex_restrict_homotopy_isZero (K : CochainComplex (QCoh X) ℤ) :
    IsZero ((quasicoherentRestriction j).mapHomotopyCategory (.up ℤ) |>.obj
      ((HomotopyCategory.quotient (QCoh X) (.up ℤ)).obj
        ((openFiberComplexFunctor j).obj K))) := by
  letI := openLocalizationComplexUnit_restrict_isIso j K
  exact homotopyImageMappingCocone_isZero_of_isIso (quasicoherentRestriction j)
    ((openLocalizationComplexUnit j).app K)

/-- A fiber step preserves contractibility on every already removed open. -/
theorem openFiberComplex_preserves_open_homotopy_vanishing (V : X.Opens)
    (K : CochainComplex (QCoh X) ℤ)
    (zeroK : IsZero ((quasicoherentRestriction V.ι).mapHomotopyCategory (.up ℤ) |>.obj
      ((HomotopyCategory.quotient (QCoh X) (.up ℤ)).obj K))) :
    IsZero ((quasicoherentRestriction V.ι).mapHomotopyCategory (.up ℤ) |>.obj
      ((HomotopyCategory.quotient (QCoh X) (.up ℤ)).obj
        ((openFiberComplexFunctor j).obj K))) := by
  let H := (quasicoherentRestriction V.ι).mapHomotopyCategory (.up ℤ)
  let Q := HomotopyCategory.quotient (QCoh X) (.up ℤ)
  let φ := (openLocalizationComplexUnit j).app K
  have zeroLocalized : IsZero (H.obj (Q.obj
      (((quasicoherentOpenLocalization j).mapHomologicalComplex (.up ℤ)).obj K))) :=
    functor_isZero_of_iso H (openLocalizationComplexHomotopyIso j K)
      (quasicoherentOpenPushRestriction_homotopy_isZero j V (Q.obj K) zeroK)
  exact homotopyImageMappingCocone_isZero_of_endpoints (quasicoherentRestriction V.ι) φ
    zeroK zeroLocalized

/-- The finite iterated fiber is genuinely contractible on each listed
open, for every arbitrary unbounded input complex. -/
theorem openFiberStage_restrict_homotopy_isZero {I : Type v}
    (V : I → X.Opens) [∀ i, IsAffineHom (V i).ι] (l : List I)
    (K : CochainComplex (QCoh X) ℤ) (i : I) (member : i ∈ l) :
    IsZero ((quasicoherentRestriction (V i).ι).mapHomotopyCategory (.up ℤ) |>.obj
      ((HomotopyCategory.quotient (QCoh X) (.up ℤ)).obj
        ((openFiberStage V l).1.obj K))) := by
  induction l with
  | nil => simp only [List.not_mem_nil] at member
  | cons a l ih =>
      rcases List.mem_cons.mp member with same | later
      · subst i
        exact openFiberComplex_restrict_homotopy_isZero (V a).ι
          ((openFiberStage V l).1.obj K)
      · exact openFiberComplex_preserves_open_homotopy_vanishing (V a).ι (V i)
          ((openFiberStage V l).1.obj K) (ih later)

end ToricPower
