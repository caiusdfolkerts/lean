module

public import ToricPower.ComplexCoconeNaturality
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-! # Exactness of genuine functorial mapping fibers

The actual mapping-cone term is identified with its two coefficient
modules. Every map acts diagonally in these coordinates. Consequently
short exact coefficient sequences remain short exact after forming the
mapping fiber. No splitting of the original coefficient sequence is
assumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex

namespace ToricPower.ComplexCone

variable {k : Type} [CommRing k]

theorem moduleShortExact_of_productCoordinates
    (S T U : ShortComplex (ModuleCat.{0} k))
    (e₁ : S.X₁ ≃ₗ[k] T.X₁ × U.X₁)
    (e₂ : S.X₂ ≃ₗ[k] T.X₂ × U.X₂)
    (e₃ : S.X₃ ≃ₗ[k] T.X₃ × U.X₃)
    (first : ∀ x, e₂ (S.f x) = (T.f (e₁ x).1,U.f (e₁ x).2))
    (second : ∀ x, e₃ (S.g x) = (T.g (e₂ x).1,U.g (e₂ x).2))
    (hT : T.ShortExact) (hU : U.ShortExact) : S.ShortExact := by
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    have zero : (T.g (e₂ x).1,U.g (e₂ x).2) = 0 := by
      rw [← second,hx,map_zero]
    obtain ⟨a,ha⟩ := (ShortComplex.moduleCat_exact_iff T).mp hT.exact
      (e₂ x).1 (congrArg Prod.fst zero)
    obtain ⟨b,hb⟩ := (ShortComplex.moduleCat_exact_iff U).mp hU.exact
      (e₂ x).2 (congrArg Prod.snd zero)
    refine ⟨e₁.symm (a,b),e₂.injective ?_⟩
    rw [first,LinearEquiv.apply_symm_apply,ha,hb]
  · rw [ModuleCat.mono_iff_injective]
    intro x y equal
    apply e₁.injective
    have mapped := congrArg e₂ equal
    rw [first,first] at mapped
    exact Prod.ext
      (hT.moduleCat_injective_f (congrArg Prod.fst mapped))
      (hU.moduleCat_injective_f (congrArg Prod.snd mapped))
  · rw [ModuleCat.epi_iff_surjective]
    intro z
    obtain ⟨a,ha⟩ := hT.moduleCat_surjective_g (e₃ z).1
    obtain ⟨b,hb⟩ := hU.moduleCat_surjective_g (e₃ z).2
    refine ⟨e₂.symm (a,b),e₃.injective ?_⟩
    rw [second,LinearEquiv.apply_symm_apply,ha,hb]

def mappingConeModuleTermEquiv {K L : CochainComplex (ModuleCat.{0} k) ℤ}
    (φ : K ⟶ L) (q : ℤ) :
    (mappingCone φ).X q ≃ₗ[k] K.X (q+1) × L.X q :=
  (homotopyCofiber.XIsoBiprod φ q (q+1) rfl ≪≫
    ModuleCat.biprodIsoProd _ _).toLinearEquiv

theorem mappingConeModuleTermEquiv_fst
    {K L : CochainComplex (ModuleCat.{0} k) ℤ} (φ : K ⟶ L) (q : ℤ)
    (x : (mappingCone φ).X q) :
    (mappingConeModuleTermEquiv φ q x).1 =
      (mappingCone.fst φ).1.v q (q+1) rfl x := by
  have projection : (ModuleCat.biprodIsoProd (K.X (q+1)) (L.X q)).hom ≫
      ModuleCat.ofHom (LinearMap.fst k (K.X (q+1)) (L.X q)) = biprod.fst := by
    rw [← ModuleCat.biprodIsoProd_inv_comp_fst,Iso.hom_inv_id_assoc]
  have value := ConcreteCategory.congr_hom projection
    ((homotopyCofiber.XIsoBiprod φ q (q+1) rfl).hom x)
  exact value

theorem mappingConeModuleTermEquiv_snd
    {K L : CochainComplex (ModuleCat.{0} k) ℤ} (φ : K ⟶ L) (q : ℤ)
    (x : (mappingCone φ).X q) :
    (mappingConeModuleTermEquiv φ q x).2 =
      (mappingCone.snd φ).v q q (add_zero q) x := by
  have projection : (ModuleCat.biprodIsoProd (K.X (q+1)) (L.X q)).hom ≫
      ModuleCat.ofHom (LinearMap.snd k (K.X (q+1)) (L.X q)) = biprod.snd := by
    rw [← ModuleCat.biprodIsoProd_inv_comp_snd,Iso.hom_inv_id_assoc]
  have value := ConcreteCategory.congr_hom projection
    ((homotopyCofiber.XIsoBiprod φ q (q+1) rfl).hom x)
  have formula : (homotopyCofiber.XIsoBiprod φ q (q+1) rfl).hom ≫
      biprod.snd = (mappingCone.snd φ).v q q (add_zero q) := by
    change _ = homotopyCofiber.sndX φ q
    apply homotopyCofiber.ext_from_X φ (q+1) q rfl <;> simp
  exact value.trans (ConcreteCategory.congr_hom formula x)

theorem mappingConeModuleTermEquiv_map
    {K₁ L₁ K₂ L₂ : CochainComplex (ModuleCat.{0} k) ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (square : φ₁ ≫ b = a ≫ φ₂) (q : ℤ) (x : (mappingCone φ₁).X q) :
    mappingConeModuleTermEquiv φ₂ q ((mappingCone.map φ₁ φ₂ a b square).f q x) =
      (a.f (q+1) (mappingConeModuleTermEquiv φ₁ q x).1,
        b.f q (mappingConeModuleTermEquiv φ₁ q x).2) := by
  apply Prod.ext
  · rw [mappingConeModuleTermEquiv_fst,mappingConeModuleTermEquiv_fst]
    exact ConcreteCategory.congr_hom
      (mappingCone_map_fst_v φ₁ φ₂ a b square q (q+1) rfl) x
  · rw [mappingConeModuleTermEquiv_snd,mappingConeModuleTermEquiv_snd]
    exact ConcreteCategory.congr_hom (mappingCone_map_snd_v φ₁ φ₂ a b square q) x

variable {B : Type*} [Category B] [HasZeroMorphisms B]
  {F G : B ⥤ CochainComplex (ModuleCat.{0} k) ℤ}
  [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] (τ : F ⟶ G)

instance coneFunctor_preservesZeroMorphisms : (coneFunctor τ).PreservesZeroMorphisms where
  map_zero X Y := by
    change mappingCone.map (τ.app X) (τ.app Y) (F.map 0) (G.map 0)
      (τ.naturality (0 : X ⟶ Y)).symm = 0
    apply HomologicalComplex.Hom.ext
    funext q
    apply mappingCone.ext_from (τ.app X) (q+1) q rfl
    · simp [mappingCone.map,F.map_zero,G.map_zero]
    · simp [mappingCone.map,F.map_zero,G.map_zero]

instance coconeFunctor_preservesZeroMorphisms : (coconeFunctor τ).PreservesZeroMorphisms := by
  unfold coconeFunctor
  infer_instance

theorem coneFunctor_map_shortExact (S : ShortComplex B)
    (hF : (S.map F).ShortExact) (hG : (S.map G).ShortExact) :
    (S.map (coneFunctor τ)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro q
  let T := (S.map F).map (HomologicalComplex.eval (ModuleCat k) (.up ℤ) (q+1))
  let U := (S.map G).map (HomologicalComplex.eval (ModuleCat k) (.up ℤ) q)
  exact moduleShortExact_of_productCoordinates
    ((S.map (coneFunctor τ)).map (HomologicalComplex.eval (ModuleCat k) (.up ℤ) q)) T U
    (mappingConeModuleTermEquiv (τ.app S.X₁) q)
    (mappingConeModuleTermEquiv (τ.app S.X₂) q)
    (mappingConeModuleTermEquiv (τ.app S.X₃) q)
    (mappingConeModuleTermEquiv_map (τ.app S.X₁) (τ.app S.X₂)
      (F.map S.f) (G.map S.f) (τ.naturality S.f).symm q)
    (mappingConeModuleTermEquiv_map (τ.app S.X₂) (τ.app S.X₃)
      (F.map S.g) (G.map S.g) (τ.naturality S.g).symm q)
    (hF.map_of_exact _) (hG.map_of_exact _)

/-- Mapping fibers preserve every short exact coefficient sequence
whenever both functors in their defining comparison do so. -/
theorem coconeFunctor_map_shortExact (S : ShortComplex B)
    (hF : (S.map F).ShortExact) (hG : (S.map G).ShortExact) :
    (S.map (coconeFunctor τ)).ShortExact :=
  (coneFunctor_map_shortExact τ S hF hG).map_of_exact
    (CategoryTheory.shiftFunctor _ (-1 : ℤ))

end ToricPower.ComplexCone

end
