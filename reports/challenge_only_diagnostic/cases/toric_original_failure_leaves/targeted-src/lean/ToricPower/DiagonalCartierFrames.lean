module

public import ToricPower.DivisorWeightMonomialFrames
public import ToricPower.DiagonalSheafComposition
public import ToricPower.DiagonalToricFrames
public import ToricPower.SchemeRestrictionTensor

/-!
# Cartier frames on the actual product charts

The two factors of a diagonal line sheaf are pulled back along the actual
projections of the actual toric product. The chart projection identities
identify their pullbacks with the pullbacks of the actual affine Cartier
frames. Their monomial entries then acquire the literal coefficients
`χ^(a+q_left,target-q_left,source, -a+q_right,target-q_right,source)`.

All comparisons below are between specified sheaves and specified maps.
Development source, pending checking by the pinned Lean kernel.
-/

@[expose] public noncomputable section

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open TauCeti.Toric ToricPower.IntegralArrangement
open scoped Classical TensorProduct

namespace ToricPower

section FrameTransport

universe u v w

variable {X Y : Scheme.{u}}

/-- Base change of a specified rank-one frame, using the genuine
structure-sheaf pullback isomorphism. -/
def schemePullbackFrame (f : X ⟶ Y) {M : Y.Modules}
    (frame : SheafOfModules.unit Y.ringCatSheaf ≅ M) :
    SheafOfModules.unit X.ringCatSheaf ≅ (Scheme.Modules.pullback f).obj M :=
  (Scheme.Modules.pullbackObjUnitIso f).symm ≪≫
    (Scheme.Modules.pullback f).mapIso frame

/-- The coefficient of a specified rank-one map pulls back by the
actual homomorphism on global functions. -/
@[reassoc]
theorem schemePullbackFrame_map (f : X ⟶ Y) {M N : Y.Modules}
    (source : SheafOfModules.unit Y.ringCatSheaf ≅ M)
    (target : SheafOfModules.unit Y.ringCatSheaf ≅ N)
    (map : M ⟶ N) (r : Γ(Y, ⊤))
    (h : source.hom ≫ map =
      Scheme.Modules.globalSectionsSmul (SheafOfModules.unit Y.ringCatSheaf) r ≫ target.hom) :
    (schemePullbackFrame f source).hom ≫ (Scheme.Modules.pullback f).map map =
      Scheme.Modules.globalSectionsSmul (SheafOfModules.unit X.ringCatSheaf)
        (f.appTop r) ≫ (schemePullbackFrame f target).hom := by
  dsimp only [schemePullbackFrame, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [Category.assoc, ← Functor.map_comp, h, Functor.map_comp]
  erw [Scheme.Modules.pullback_map_globalSectionsSmul]
  change (Scheme.Modules.pullbackObjUnitIso f).inv ≫
      Scheme.Modules.globalSectionsSmul ((Scheme.Modules.pullback f).obj (𝟙_ Y.Modules))
        (f.appTop r) ≫ (Scheme.Modules.pullback f).map target.hom =
    Scheme.Modules.globalSectionsSmul (𝟙_ X.Modules) (f.appTop r) ≫
      (Scheme.Modules.pullbackObjUnitIso f).inv ≫ (Scheme.Modules.pullback f).map target.hom
  simpa only [Category.assoc] using
    congrArg (fun k => k ≫ (Scheme.Modules.pullback f).map target.hom)
      (Scheme.Modules.globalSectionsSmul_naturality
        (Scheme.Modules.pullbackObjUnitIso f).inv (f.appTop r)).symm

/-- Transport a specified frame across a specified natural isomorphism. -/
def schemeFrameTransport {C : Type v} [Category.{w} C]
    {F G : C ⥤ X.Modules} (comparison : F ≅ G) (M : C)
    (frame : SheafOfModules.unit X.ringCatSheaf ≅ G.obj M) :
    SheafOfModules.unit X.ringCatSheaf ≅ F.obj M :=
  frame ≪≫ comparison.symm.app M

@[reassoc]
theorem schemeFrameTransport_map {C : Type v} [Category.{w} C]
    {F G : C ⥤ X.Modules} (comparison : F ≅ G) {M N : C}
    (source : SheafOfModules.unit X.ringCatSheaf ≅ G.obj M)
    (target : SheafOfModules.unit X.ringCatSheaf ≅ G.obj N)
    (map : M ⟶ N) (r : Γ(X, ⊤))
    (h : source.hom ≫ G.map map =
      Scheme.Modules.globalSectionsSmul (SheafOfModules.unit X.ringCatSheaf) r ≫ target.hom) :
    (schemeFrameTransport comparison M source).hom ≫ F.map map =
      Scheme.Modules.globalSectionsSmul (SheafOfModules.unit X.ringCatSheaf) r ≫
        (schemeFrameTransport comparison N target).hom := by
  dsimp only [schemeFrameTransport, Iso.trans_hom, Iso.symm_hom, Iso.app_hom]
  rw [Category.assoc, ← comparison.inv.naturality, ← Category.assoc, h, Category.assoc]

theorem affineGlobalSectionsEquiv_specMap {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (r : R) :
    (Spec.map (CommRingCat.ofHom f)).appTop (affineGlobalSectionsEquiv R r) =
      affineGlobalSectionsEquiv S (f r) := by
  exact (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f)) r).symm

/-- In the structure-sheaf frame, tensoring scalar endomorphisms
multiplies their actual global functions. -/
@[reassoc]
theorem unitSheafTensorSmul (X : Scheme.{u}) (r s : Γ(X, ⊤)) :
    (λ_ (SheafOfModules.unit X.ringCatSheaf)).inv ≫
        (Scheme.Modules.globalSectionsSmul (SheafOfModules.unit X.ringCatSheaf) r ⊗ₘ
          Scheme.Modules.globalSectionsSmul (SheafOfModules.unit X.ringCatSheaf) s) =
      Scheme.Modules.globalSectionsSmul (SheafOfModules.unit X.ringCatSheaf) (r * s) ≫
        (λ_ (SheafOfModules.unit X.ringCatSheaf)).inv := by
  let I : X.Modules := 𝟙_ X.Modules
  let f := Scheme.Modules.globalSectionsSmul I r
  let g := Scheme.Modules.globalSectionsSmul I s
  have first_natural : (f ▷ I) ≫ (λ_ I).hom = (λ_ I).hom ≫ f := by
    simpa only [I, ← unitors_equal] using (rightUnitor_naturality f)
  have second_natural : (I ◁ g) ≫ (λ_ I).hom = (λ_ I).hom ≫ g :=
    leftUnitor_naturality g
  change (λ_ I).inv ≫ (f ⊗ₘ g) =
    Scheme.Modules.globalSectionsSmul I (r * s) ≫ (λ_ I).inv
  apply (cancel_mono (λ_ I).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change (λ_ I).inv ≫ (f ⊗ₘ g) ≫ (λ_ I).hom =
    Scheme.Modules.globalSectionsSmul I (r * s)
  calc
    _ = (λ_ I).inv ≫ (f ▷ I) ≫ (λ_ I).hom ≫ g := by
      rw [tensorHom_def]
      simp only [Category.assoc]
      rw [second_natural]
    _ = f ≫ g := by
      simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
        congrArg (fun k => (λ_ I).inv ≫ k ≫ g) first_natural
    _ = _ := by rw [← Scheme.Modules.globalSectionsSmul_mul, mul_comm]

/-- The tensor product of two specified pullback frames. Invertibility
of the canonical tensor comparison is proved for the actual open
immersion, without an assumed monoidal structure on arbitrary pullbacks. -/
def schemePullbackTensorFrame (f : X ⟶ Y) [IsOpenImmersion f]
    {M N : Y.Modules}
    (first : SheafOfModules.unit X.ringCatSheaf ≅ (Scheme.Modules.pullback f).obj M)
    (second : SheafOfModules.unit X.ringCatSheaf ≅ (Scheme.Modules.pullback f).obj N) :
    SheafOfModules.unit X.ringCatSheaf ≅ (Scheme.Modules.pullback f).obj (M ⊗ N) :=
  (λ_ (SheafOfModules.unit X.ringCatSheaf)).symm ≪≫ tensorIso first second ≪≫
    (Scheme.Modules.pullbackTensorIsoOfOpenImmersion f M N).symm

/-- The coefficient in the tensor frame is the product of the two
coefficients. This is an equality of the specified pulled-back maps. -/
@[reassoc]
theorem schemePullbackTensorFrame_map (f : X ⟶ Y) [IsOpenImmersion f]
    {M₁ M₂ N₁ N₂ : Y.Modules}
    (firstSource : SheafOfModules.unit X.ringCatSheaf ≅ (Scheme.Modules.pullback f).obj M₁)
    (firstTarget : SheafOfModules.unit X.ringCatSheaf ≅ (Scheme.Modules.pullback f).obj M₂)
    (secondSource : SheafOfModules.unit X.ringCatSheaf ≅ (Scheme.Modules.pullback f).obj N₁)
    (secondTarget : SheafOfModules.unit X.ringCatSheaf ≅ (Scheme.Modules.pullback f).obj N₂)
    (first : M₁ ⟶ M₂) (second : N₁ ⟶ N₂) (r s : Γ(X, ⊤))
    (hfirst : firstSource.hom ≫ (Scheme.Modules.pullback f).map first =
      Scheme.Modules.globalSectionsSmul (SheafOfModules.unit X.ringCatSheaf) r ≫ firstTarget.hom)
    (hsecond : secondSource.hom ≫ (Scheme.Modules.pullback f).map second =
      Scheme.Modules.globalSectionsSmul (SheafOfModules.unit X.ringCatSheaf) s ≫ secondTarget.hom) :
    (schemePullbackTensorFrame f firstSource secondSource).hom ≫
        (Scheme.Modules.pullback f).map (first ⊗ₘ second) =
      Scheme.Modules.globalSectionsSmul (SheafOfModules.unit X.ringCatSheaf) (r * s) ≫
        (schemePullbackTensorFrame f firstTarget secondTarget).hom := by
  let comparisonSource := Scheme.Modules.pullbackTensorIsoOfOpenImmersion f M₁ N₁
  let comparisonTarget := Scheme.Modules.pullbackTensorIsoOfOpenImmersion f M₂ N₂
  apply (cancel_mono comparisonTarget.hom).mp
  dsimp only [schemePullbackTensorFrame, Iso.trans_hom, Iso.symm_hom, tensorIso_hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change (λ_ (SheafOfModules.unit X.ringCatSheaf)).inv ≫
      (firstSource.hom ⊗ₘ secondSource.hom) ≫ comparisonSource.inv ≫
        (Scheme.Modules.pullback f).map (first ⊗ₘ second) ≫
          Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) M₂ N₂ = _
  erw [← Functor.OplaxMonoidal.δ_natural]
  change (λ_ (SheafOfModules.unit X.ringCatSheaf)).inv ≫
      (firstSource.hom ⊗ₘ secondSource.hom) ≫ comparisonSource.inv ≫ comparisonSource.hom ≫
        ((Scheme.Modules.pullback f).map first ⊗ₘ (Scheme.Modules.pullback f).map second) = _
  rw [Iso.inv_hom_id_assoc]
  dsimp only [comparisonTarget]
  simp only [Iso.inv_hom_id, Category.comp_id]
  erw [tensorHom_comp_tensorHom, hfirst, hsecond,
    ← tensorHom_comp_tensorHom]
  rw [← Category.assoc, unitSheafTensorSmul, Category.assoc]

end FrameTransport

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {latticeMap : N →+ V}
  (fan : Fan latticeMap) (nonempty : Nonempty fan.cones)
  (regular : fan.IsRegular) {n s : ℕ}
  (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)
  (σ τ : fan.cones)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "S" => fanConeRaySet fan rays σ
local notation "T" => fanConeRaySet fan rays τ
local notation "R" => DiagonalChartRing ℂ A S T
local notation "U" => Spec (CommRingCat.of R)
local notation "chart" => diagonalProductChartι fan basis rays σ τ
local notation "leftRing" => diagonalProductFirstCoordinate fan basis rays σ τ
local notation "rightRing" => diagonalProductSecondCoordinate fan basis rays σ τ
local notation "leftMap" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (diagonalProductFirstCoordinate fan basis rays σ τ)))
local notation "rightMap" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (diagonalProductSecondCoordinate fan basis rays σ τ)))

/-- The actual first projection square, at the level of module pullbacks. -/
def diagonalFirstPullbackComparison :
    Scheme.Modules.pullback (toricDiagonalFirst fan) ⋙ Scheme.Modules.pullback chart ≅
      Scheme.Modules.pullback (fan.affineToricChartι σ) ⋙ Scheme.Modules.pullback leftMap :=
  Scheme.Modules.pullbackComp _ _ ≪≫
    Scheme.Modules.pullbackCongr (diagonalProductChartι_first fan basis rays σ τ) ≪≫
    (Scheme.Modules.pullbackComp _ _).symm

/-- The actual second projection square, at the level of module pullbacks. -/
def diagonalSecondPullbackComparison :
    Scheme.Modules.pullback (toricDiagonalSecond fan) ⋙ Scheme.Modules.pullback chart ≅
      Scheme.Modules.pullback (fan.affineToricChartι τ) ⋙ Scheme.Modules.pullback rightMap :=
  Scheme.Modules.pullbackComp _ _ ≪≫
    Scheme.Modules.pullbackCongr (diagonalProductChartι_second fan basis rays σ τ) ≪≫
    (Scheme.Modules.pullbackComp _ _).symm

/-- The first factor's actual frame on the product chart. -/
def diagonalFirstCartierFrame {d : ℕ} (j : NormalizedCell A d) :
    letI := toricSchemeIntegral fan nonempty
    SheafOfModules.unit (U).ringCatSheaf ≅
      (Scheme.Modules.pullback chart).obj
        ((Scheme.Modules.pullback (toricDiagonalFirst fan)).obj
          (diagonalLeftSheaf fan nonempty regular basis rays j)) :=
  schemeFrameTransport (diagonalFirstPullbackComparison fan basis rays σ τ) _
    (schemePullbackFrame leftMap
      (toricCartierPullbackFrame fan nonempty regular
        (diagonalLeftCoefficients fan basis rays j) σ))

/-- The second factor's actual frame on the product chart. -/
def diagonalSecondCartierFrame {d : ℕ} (j : NormalizedCell A d) :
    letI := toricSchemeIntegral fan nonempty
    SheafOfModules.unit (U).ringCatSheaf ≅
      (Scheme.Modules.pullback chart).obj
        ((Scheme.Modules.pullback (toricDiagonalSecond fan)).obj
          (diagonalRightSheaf fan nonempty regular basis rays j)) :=
  schemeFrameTransport (diagonalSecondPullbackComparison fan basis rays σ τ) _
    (schemePullbackFrame rightMap
      (toricCartierPullbackFrame fan nonempty regular
        (diagonalRightCoefficients fan basis rays j) τ))

/-- The first normalized chart coefficient in the literal product ring. -/
def diagonalFirstChartCoefficient {e d : ℕ} (j : NormalizedCell A e)
    (i : NormalizedCell A d) (a : Fin n → ℤ)
    (h : DiagonalEntryRegular fan basis rays j i a) : R :=
  leftRing (normalizedToricMonomial fan regular
    (diagonalLeftCoefficients fan basis rays j)
    (diagonalLeftCoefficients fan basis rays i) (basis.equivFun.symm a) h.1 σ)

/-- The second normalized chart coefficient in the literal product ring. -/
def diagonalSecondChartCoefficient {e d : ℕ} (j : NormalizedCell A e)
    (i : NormalizedCell A d) (a : Fin n → ℤ)
    (h : DiagonalEntryRegular fan basis rays j i a) : R :=
  rightRing (normalizedToricMonomial fan regular
    (diagonalRightCoefficients fan basis rays j)
    (diagonalRightCoefficients fan basis rays i) (-(basis.equivFun.symm a))
    (by intro ρ; simpa only [AddMonoidHom.neg_apply, sub_eq_add_neg] using h.2 ρ) τ)

@[reassoc]
theorem diagonalFirstCartierFrame_map {e d : ℕ} (j : NormalizedCell A e)
    (i : NormalizedCell A d) (a : Fin n → ℤ)
    (h : DiagonalEntryRegular fan basis rays j i a) :
    letI := toricSchemeIntegral fan nonempty
    (diagonalFirstCartierFrame fan nonempty regular basis rays σ τ j).hom ≫
      (Scheme.Modules.pullback chart).map
        ((Scheme.Modules.pullback (toricDiagonalFirst fan)).map
          (toricCartierMonomialMap fan nonempty regular
            (diagonalLeftCoefficients fan basis rays j)
            (diagonalLeftCoefficients fan basis rays i) (basis.equivFun.symm a) h.1)) =
      Scheme.Modules.globalSectionsSmul (SheafOfModules.unit (U).ringCatSheaf)
        (affineGlobalSectionsEquiv R
          (diagonalFirstChartCoefficient fan regular basis rays σ τ j i a h)) ≫
        (diagonalFirstCartierFrame fan nonempty regular basis rays σ τ i).hom := by
  letI := toricSchemeIntegral fan nonempty
  apply schemeFrameTransport_map
  have hframe := schemePullbackFrame_map leftMap
    (toricCartierPullbackFrame fan nonempty regular
      (diagonalLeftCoefficients fan basis rays j) σ)
    (toricCartierPullbackFrame fan nonempty regular
      (diagonalLeftCoefficients fan basis rays i) σ)
    ((Scheme.Modules.pullback (fan.affineToricChartι σ)).map
      (toricCartierMonomialMap fan nonempty regular
        (diagonalLeftCoefficients fan basis rays j)
        (diagonalLeftCoefficients fan basis rays i) (basis.equivFun.symm a) h.1))
    (affineGlobalSectionsEquiv (affineCoordinateRing fan.lattice σ.val)
      (normalizedToricMonomial fan regular (diagonalLeftCoefficients fan basis rays j)
        (diagonalLeftCoefficients fan basis rays i) (basis.equivFun.symm a) h.1 σ))
    (toricCartierMonomialMap_pullback_frame fan nonempty regular _ _ _ _ σ)
  simpa only [affineGlobalSectionsEquiv_specMap, diagonalFirstChartCoefficient,
    CategoryTheory.Functor.comp_map, CategoryTheory.Functor.comp_obj,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using hframe

@[reassoc]
theorem diagonalSecondCartierFrame_map {e d : ℕ} (j : NormalizedCell A e)
    (i : NormalizedCell A d) (a : Fin n → ℤ)
    (h : DiagonalEntryRegular fan basis rays j i a) :
    letI := toricSchemeIntegral fan nonempty
    (diagonalSecondCartierFrame fan nonempty regular basis rays σ τ j).hom ≫
      (Scheme.Modules.pullback chart).map
        ((Scheme.Modules.pullback (toricDiagonalSecond fan)).map
          (toricCartierMonomialMap fan nonempty regular
            (diagonalRightCoefficients fan basis rays j)
            (diagonalRightCoefficients fan basis rays i) (-(basis.equivFun.symm a))
            (by intro ρ; simpa only [AddMonoidHom.neg_apply, sub_eq_add_neg] using h.2 ρ))) =
      Scheme.Modules.globalSectionsSmul (SheafOfModules.unit (U).ringCatSheaf)
        (affineGlobalSectionsEquiv R
          (diagonalSecondChartCoefficient fan regular basis rays σ τ j i a h)) ≫
        (diagonalSecondCartierFrame fan nonempty regular basis rays σ τ i).hom := by
  letI := toricSchemeIntegral fan nonempty
  apply schemeFrameTransport_map
  have hframe := schemePullbackFrame_map rightMap
    (toricCartierPullbackFrame fan nonempty regular
      (diagonalRightCoefficients fan basis rays j) τ)
    (toricCartierPullbackFrame fan nonempty regular
      (diagonalRightCoefficients fan basis rays i) τ)
    ((Scheme.Modules.pullback (fan.affineToricChartι τ)).map
      (toricCartierMonomialMap fan nonempty regular
        (diagonalRightCoefficients fan basis rays j)
        (diagonalRightCoefficients fan basis rays i) (-(basis.equivFun.symm a))
        (by intro ρ; simpa only [AddMonoidHom.neg_apply, sub_eq_add_neg] using h.2 ρ)))
    (affineGlobalSectionsEquiv (affineCoordinateRing fan.lattice τ.val)
      (normalizedToricMonomial fan regular (diagonalRightCoefficients fan basis rays j)
        (diagonalRightCoefficients fan basis rays i) (-(basis.equivFun.symm a))
        (by intro ρ; simpa only [AddMonoidHom.neg_apply, sub_eq_add_neg] using h.2 ρ) τ))
    (toricCartierMonomialMap_pullback_frame fan nonempty regular _ _ _ _ τ)
  simpa only [affineGlobalSectionsEquiv_specMap, diagonalSecondChartCoefficient,
    CategoryTheory.Functor.comp_map, CategoryTheory.Functor.comp_obj,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using hframe

/-- The literal regular product-semigroup exponent of a global entry,
computed from the actual two Cartier frames. -/
def diagonalEntryChartCharacter {e d : ℕ} (j : NormalizedCell A e)
    (i : NormalizedCell A d) (a : Fin n → ℤ)
    (h : DiagonalEntryRegular fan basis rays j i a) :
    rayCharacterMonoid A S × rayCharacterMonoid A T :=
  ((fanRayCharacterMonoidEquiv fan basis rays σ).symm
      ⟨normalizedToricMonomialCharacter fan regular
        (diagonalLeftCoefficients fan basis rays j)
        (diagonalLeftCoefficients fan basis rays i) (basis.equivFun.symm a) σ,
        normalizedToricMonomialCharacter_mem fan regular _ _ _ h.1 σ⟩,
    (fanRayCharacterMonoidEquiv fan basis rays τ).symm
      ⟨normalizedToricMonomialCharacter fan regular
        (diagonalRightCoefficients fan basis rays j)
        (diagonalRightCoefficients fan basis rays i) (-(basis.equivFun.symm a)) τ,
        normalizedToricMonomialCharacter_mem fan regular _ _ _
          (by intro ρ; simpa only [AddMonoidHom.neg_apply, sub_eq_add_neg] using h.2 ρ) τ⟩)

theorem diagonalEntryChartCharacter_left {e d : ℕ} (j : NormalizedCell A e)
    (i : NormalizedCell A d) (a : Fin n → ℤ)
    (h : DiagonalEntryRegular fan basis rays j i a) :
    (diagonalEntryChartCharacter fan regular basis rays σ τ j i a h).1.val =
      a + diagonalLeftFrameCharacter fan regular basis rays σ i -
        diagonalLeftFrameCharacter fan regular basis rays σ j := by
  change basis.equivFun
      (coneDivisorCharacter fan regular (diagonalLeftCoefficients fan basis rays i) σ +
        basis.equivFun.symm a -
        coneDivisorCharacter fan regular (diagonalLeftCoefficients fan basis rays j) σ) = _
  simp only [map_sub, map_add, LinearEquiv.apply_symm_apply,
    diagonalLeftFrameCharacter, add_comm]

theorem diagonalEntryChartCharacter_right {e d : ℕ} (j : NormalizedCell A e)
    (i : NormalizedCell A d) (a : Fin n → ℤ)
    (h : DiagonalEntryRegular fan basis rays j i a) :
    (diagonalEntryChartCharacter fan regular basis rays σ τ j i a h).2.val =
      -a + diagonalRightFrameCharacter fan regular basis rays τ i -
        diagonalRightFrameCharacter fan regular basis rays τ j := by
  change basis.equivFun
      (coneDivisorCharacter fan regular (diagonalRightCoefficients fan basis rays i) τ +
        -(basis.equivFun.symm a) -
        coneDivisorCharacter fan regular (diagonalRightCoefficients fan basis rays j) τ) = _
  simp only [map_sub, map_add, map_neg, LinearEquiv.apply_symm_apply,
    diagonalRightFrameCharacter, add_comm]

/-- Multiplication of the two factor coefficients is exactly the
single regular monomial of the explicit product-semigroup exponent. -/
theorem diagonalChartCoefficient_eq_single {e d : ℕ} (j : NormalizedCell A e)
    (i : NormalizedCell A d) (a : Fin n → ℤ)
    (h : DiagonalEntryRegular fan basis rays j i a) :
    diagonalFirstChartCoefficient fan regular basis rays σ τ j i a h *
      diagonalSecondChartCoefficient fan regular basis rays σ τ j i a h =
    AddMonoidAlgebra.single (diagonalEntryChartCharacter fan regular basis rays σ τ j i a h) 1 := by
  apply (diagonalProductCoordinateEquiv fan basis rays σ τ).injective
  simp only [map_mul, diagonalFirstChartCoefficient, diagonalSecondChartCoefficient,
    diagonalProductFirstCoordinate, diagonalProductSecondCoordinate,
    AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply,
    Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
    diagonalProductCoordinateEquiv_single]
  congr 1 <;> simp [diagonalEntryChartCharacter, normalizedToricMonomial]

/-- The actual product line sheaf has the tensor product of the two
specified Cartier frames on the actual affine product chart. -/
def diagonalProductCartierFrame {d : ℕ} (j : NormalizedCell A d) :
    letI := toricSchemeIntegral fan nonempty
    SheafOfModules.unit (U).ringCatSheaf ≅
      (Scheme.Modules.pullback chart).obj
        (diagonalProductSheaf fan nonempty regular basis rays j) := by
  letI := toricSchemeIntegral fan nonempty
  exact schemePullbackTensorFrame chart
    (diagonalFirstCartierFrame fan nonempty regular basis rays σ τ j)
    (diagonalSecondCartierFrame fan nonempty regular basis rays σ τ j)

/-- The actual global product-character map, pulled back to the actual
product chart and read in its actual Cartier frames, is multiplication
by the exact regular monomial used in the finite cellular matrix. -/
@[reassoc]
theorem diagonalProductCartierFrame_map {e d : ℕ} (j : NormalizedCell A e)
    (i : NormalizedCell A d) (a : Fin n → ℤ)
    (h : DiagonalEntryRegular fan basis rays j i a) :
    letI := toricSchemeIntegral fan nonempty
    (diagonalProductCartierFrame fan nonempty regular basis rays σ τ j).hom ≫
      (Scheme.Modules.pullback chart).map
        (diagonalProductCharacterMap fan nonempty regular basis rays j i a h) =
      Scheme.Modules.globalSectionsSmul (SheafOfModules.unit (U).ringCatSheaf)
        (affineGlobalSectionsEquiv R
          (AddMonoidAlgebra.single
            (diagonalEntryChartCharacter fan regular basis rays σ τ j i a h) 1)) ≫
        (diagonalProductCartierFrame fan nonempty regular basis rays σ τ i).hom := by
  letI := toricSchemeIntegral fan nonempty
  have hframe := schemePullbackTensorFrame_map chart
    (diagonalFirstCartierFrame fan nonempty regular basis rays σ τ j)
    (diagonalFirstCartierFrame fan nonempty regular basis rays σ τ i)
    (diagonalSecondCartierFrame fan nonempty regular basis rays σ τ j)
    (diagonalSecondCartierFrame fan nonempty regular basis rays σ τ i)
    ((Scheme.Modules.pullback (toricDiagonalFirst fan)).map
      (toricCartierMonomialMap fan nonempty regular
        (diagonalLeftCoefficients fan basis rays j)
        (diagonalLeftCoefficients fan basis rays i) (basis.equivFun.symm a) h.1))
    ((Scheme.Modules.pullback (toricDiagonalSecond fan)).map
      (toricCartierMonomialMap fan nonempty regular
        (diagonalRightCoefficients fan basis rays j)
        (diagonalRightCoefficients fan basis rays i) (-(basis.equivFun.symm a))
        (by intro ρ; simpa only [AddMonoidHom.neg_apply, sub_eq_add_neg] using h.2 ρ)))
    (affineGlobalSectionsEquiv R
      (diagonalFirstChartCoefficient fan regular basis rays σ τ j i a h))
    (affineGlobalSectionsEquiv R
      (diagonalSecondChartCoefficient fan regular basis rays σ τ j i a h))
    (diagonalFirstCartierFrame_map fan nonempty regular basis rays σ τ j i a h)
    (diagonalSecondCartierFrame_map fan nonempty regular basis rays σ τ j i a h)
  rw [← map_mul, diagonalChartCoefficient_eq_single] at hframe
  exact hframe

end ToricPower
