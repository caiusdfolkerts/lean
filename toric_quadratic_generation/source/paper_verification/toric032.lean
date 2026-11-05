module

public import Lean.Elab.BuiltinEvalCommand
public meta import Lean.Elab.BuiltinEvalCommand
public import Lean.Util.CollectAxioms
public meta import Lean.Util.CollectAxioms
public import Lean.Util.FoldConsts
public meta import Lean.Util.FoldConsts
public import paper_verification.toric025

@[expose] public section


-- BEGIN ORIGINAL PaperVerification.ToricTorusCoactionRational
section Source_ToricTorusCoactionRational

-- original header: module

-- original header: public import PaperVerification.ToricIntrinsicSectionCharacters
-- original header: public import PaperVerification.ToricDominantAffineCoordinates

-- original header: @[expose] public section

/-! # The actual torus multiplication and its rational character coaction -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open PaperVerification.ToricCharacters
open scoped TensorProduct PaperVerification.ToricSchemes.BaseSections

namespace PaperVerification.ToricSchemes

variable (k : Type u) [Field k] (n : ℕ)

local instance torusCoordinate_domain : IsDomain (torusCoordinateRing k n) :=
  torusCoordinateRing_isDomain k n

theorem openTorusRationalAlgHom_pullback
    (X : Scheme.{u}) [IsIntegral X] [X.Over (Spec (CommRingCat.of k))]
    (j : splitTorus k (Fin n→ℤ) ⟶ X) [hj : IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k))]
    (f : AddMonoidAlgebra k (Fin n→ℤ)) :
    dominantFunctionFieldMap j (openTorusRationalAlgHom k n X j f) =
      openTorusRationalAlgHom k n (splitTorus k (Fin n→ℤ)) (𝟙 _) f := by
  have hd : IsDominant j := inferInstance
  letI : IsOpenImmersion
      (show Spec (CommRingCat.of (torusCoordinateRing k n)) ⟶ X from j) := hj
  letI : IsDominant
      (show Spec (CommRingCat.of (torusCoordinateRing k n)) ⟶ X from j) := hd
  exact dominantFunctionFieldMap_affineCoordinate
    (CommRingCat.of (torusCoordinateRing k n))
    (CommRingCat.of (torusCoordinateRing k n)) j (𝟙 _) j (𝟙 _)
    (by simp) f

theorem torus_mul_spec :
    μ[splitTorusOver k (Fin n→ℤ)].left =
      (pullbackSpecIso (CommRingCat.of k)
        (CommRingCat.of (torusCoordinateRing k n))
        (CommRingCat.of (torusCoordinateRing k n))).hom ≫
        Spec.map (CommRingCat.ofHom
          (Bialgebra.comulAlgHom k (torusCoordinateRing k n)).toRingHom) :=
  mul_spec_asOver_spec_left

instance torus_mul_surjective : Surjective μ[splitTorusOver k (Fin n→ℤ)].left := by
  let G := splitTorusOver k (Fin n→ℤ)
  letI : ModObj G G := ModObj.regular G
  exact torusAction_surjective k n G

namespace SplitToricEmbedding

variable {k n} {X : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n→ℤ)) X]
    [IsIntegral X.left] [Smooth X.hom]
    (T : SplitToricEmbedding k n X)

include T in
theorem torus_locallyNoetherian : IsLocallyNoetherian (splitTorus k (Fin n→ℤ)) := by
  change IsLocallyNoetherian (splitTorusOver k (Fin n→ℤ)).left
  letI : Smooth (splitTorusOver k (Fin n→ℤ)).hom := T.torus_smooth
  exact LocallyOfFiniteType.isLocallyNoetherian (splitTorusOver k (Fin n→ℤ)).hom

include T in
theorem doubleTorus_integral :
    IsIntegral (splitTorusOver k (Fin n→ℤ) ⊗ splitTorusOver k (Fin n→ℤ)).left := by
  letI : IsLocallyNoetherian (splitTorusOver k (Fin n→ℤ)).left :=
    T.torus_locallyNoetherian
  exact torusProduct_integral k n (splitTorusOver k (Fin n→ℤ))

include T in
/-- The proved double-torus integrality at the literal affine pullback type. -/
theorem doubleTorus_affinePullback_integral :
    IsIntegral (pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k (torusCoordinateRing k n))))
      (Spec.map (CommRingCat.ofHom (algebraMap k (torusCoordinateRing k n))))) :=
  T.doubleTorus_integral

include T in
/-- The actual affine tensor-product chart of the double torus is a
domain, derived from geometric integrality rather than postulated. -/
theorem doubleTorusTensor_isDomain :
    IsDomain (torusCoordinateRing k n ⊗[k] torusCoordinateRing k n) := by
  letI := T.doubleTorus_affinePullback_integral
  let e := pullbackSpecIso (CommRingCat.of k)
    (CommRingCat.of (torusCoordinateRing k n))
    (CommRingCat.of (torusCoordinateRing k n))
  exact (affine_isIntegral_iff _).mp (IsIntegral.of_isIso e.hom)

/-- Multiplication pulls a genuine torus rational function back through
the genuine Hopf comultiplication on its affine coordinate algebra. -/
theorem torus_mul_rational (f : AddMonoidAlgebra k (Fin n→ℤ)) :
    letI := T.doubleTorus_integral
    letI := T.doubleTorus_affinePullback_integral
    letI := T.doubleTorusTensor_isDomain
    dominantFunctionFieldMap μ[splitTorusOver k (Fin n→ℤ)].left
      (openTorusRationalAlgHom k n (splitTorus k (Fin n→ℤ)) (𝟙 _) f) =
      affineOpenCoordinateMap
        (CommRingCat.of (torusCoordinateRing k n ⊗[k] torusCoordinateRing k n))
        (pullbackSpecIso (CommRingCat.of k)
          (CommRingCat.of (torusCoordinateRing k n))
          (CommRingCat.of (torusCoordinateRing k n))).inv
        (Coalgebra.comul (R:=k) f) := by
  letI := T.doubleTorus_integral
  letI := T.doubleTorus_affinePullback_integral
  letI := T.doubleTorusTensor_isDomain
  let R := CommRingCat.of (torusCoordinateRing k n)
  let S := CommRingCat.of (torusCoordinateRing k n ⊗[k] torusCoordinateRing k n)
  let e := pullbackSpecIso (CommRingCat.of k) R R
  let mul : pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k (torusCoordinateRing k n))))
      (Spec.map (CommRingCat.ofHom (algebraMap k (torusCoordinateRing k n)))) ⟶ Spec R :=
    μ[splitTorusOver k (Fin n→ℤ)].left
  letI : IsOpenImmersion e.inv := IsOpenImmersion.of_isIso e.inv
  letI : IsDominant mul :=
    inferInstanceAs (IsDominant μ[splitTorusOver k (Fin n→ℤ)].left)
  let φ : R ⟶ S :=
    CommRingCat.ofHom (Bialgebra.comulAlgHom k (torusCoordinateRing k n)).toRingHom
  have hcomm : e.inv ≫ mul = Spec.map φ ≫ 𝟙 (Spec R) := by
    calc
      e.inv ≫ mul = e.inv ≫ (e.hom ≫ Spec.map φ) :=
        congrArg (fun h => e.inv ≫ h) (torus_mul_spec k n)
      _ = Spec.map φ := e.inv_hom_id_assoc _
      _ = Spec.map φ ≫ 𝟙 (Spec R) := (Category.comp_id _).symm
  exact dominantFunctionFieldMap_affineCoordinate R S (𝟙 (Spec R)) e.inv mul φ hcomm f

/-- The open double-torus map used to test actual rational identities. -/
def doubleTorusMap :
    (splitTorusOver k (Fin n→ℤ) ⊗ splitTorusOver k (Fin n→ℤ)).left ⟶
      (splitTorusOver k (Fin n→ℤ) ⊗ X).left :=
  (splitTorusOver k (Fin n→ℤ) ◁ T.torus).left

instance doubleTorusMap_isOpenImmersion : IsOpenImmersion T.doubleTorusMap := by
  rw [doubleTorusMap,Over.whiskerLeft_left]
  infer_instance

theorem doubleTorusMap_comp_action :
    T.doubleTorusMap ≫ (γ[splitTorusOver k (Fin n→ℤ),X]).left =
      μ[splitTorusOver k (Fin n→ℤ)].left ≫ T.torus.left := by
  exact (congrArg (fun f=>f.left) T.equivariant).symm

end SplitToricEmbedding

end PaperVerification.ToricSchemes
end
end Source_ToricTorusCoactionRational
-- END ORIGINAL PaperVerification.ToricTorusCoactionRational


-- BEGIN ORIGINAL PaperVerification.ToricIntrinsicSectionCoaction
section Source_ToricIntrinsicSectionCoaction

-- original header: module

-- original header: public import PaperVerification.ToricTorusCoactionRational
-- original header: public import PaperVerification.ToricProductRationalMap
-- original header: public import PaperVerification.ToricActionSectionRegularity
-- original header: public import PaperVerification.ToricTensorCharacterCoefficients

-- original header: @[expose] public section

/-!
# The genuine character coaction on intrinsic normalized global sections

The action pullback is first computed on the actual dense double torus.
Its local regularity then permits coefficient extraction in the actual
affine product coordinate ring. Thus the global-section Laurent image is
proved to be stable under the Hopf coaction, over every ground field.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open PaperVerification.ToricCharacters
open scoped TensorProduct PaperVerification.ToricSchemes.BaseSections

namespace PaperVerification.ToricSchemes.SplitToricEmbedding

variable {k : Type u} [Field k] {n : ℕ}
    {X : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n→ℤ)) X]
    [IsIntegral X.left] [Smooth X.hom]
    (T : SplitToricEmbedding k n X)

section LocallyNoetherian

variable [IsLocallyNoetherian X.left]

theorem action_pullback_laurent (f : AddMonoidAlgebra k (Fin n→ℤ)) :
    dominantFunctionFieldMap (γ[splitTorusOver k (Fin n→ℤ),X]).left
      (openTorusRationalAlgHom k n X.left T.torus.left f) =
      torusProductRationalMap k n X
        (Algebra.TensorProduct.map (AlgHom.id k _)
          (openTorusRationalAlgHom k n X.left T.torus.left)
          (Coalgebra.comul (R:=k) f)) := by
  let G := splitTorusOver k (Fin n→ℤ)
  let A := AddMonoidAlgebra k (Fin n→ℤ)
  let torusValue := openTorusRationalAlgHom k n X.left T.torus.left
  let ι₀ := torusCoordinateValueAlgHom k n
  letI : IsLocallyNoetherian G.left := T.torus_locallyNoetherian
  letI : IsIntegral (G ⊗ G).left := T.doubleTorus_integral
  letI : IsDominant (G ◁ T.torus).left := by
    change IsDominant T.doubleTorusMap
    infer_instance
  letI : IsDomain A := torusCoordinateRing_isDomain k n
  letI := T.doubleTorusTensor_isDomain
  have hmap (w : A⊗[k]A) :
      Algebra.TensorProduct.map (AlgHom.id k A)
        (BaseSections.dominantFunctionFieldAlgHom k T.torus.left)
        (Algebra.TensorProduct.map (AlgHom.id k A) torusValue w) =
      Algebra.TensorProduct.map (AlgHom.id k A) ι₀ w := by
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
        simp only [Algebra.TensorProduct.map_tmul,AlgHom.id_apply]
        congr 1
        exact openTorusRationalAlgHom_pullback k n X.left T.torus.left b
    | add w v hw hv => simp only [map_add,hw,hv]
  have hcongr (g h : (G⊗G).left ⟶ X.left)
      [IsDominant g] [IsDominant h] (heq : g=h) :
      dominantFunctionFieldMap g=dominantFunctionFieldMap h := by
    subst h
    rfl
  have hact : dominantFunctionFieldMap T.doubleTorusMap
        (dominantFunctionFieldMap (γ[G,X]).left (torusValue f)) =
      dominantFunctionFieldMap μ[G].left
        (dominantFunctionFieldMap T.torus.left (torusValue f)) := by
    calc
      _ = dominantFunctionFieldMap (T.doubleTorusMap ≫ (γ[G,X]).left)
          (torusValue f) :=
        (congrArg (fun φ => φ (torusValue f))
          (dominantFunctionFieldMap_comp T.doubleTorusMap (γ[G,X]).left)).symm
      _ = dominantFunctionFieldMap (μ[G].left ≫ T.torus.left) (torusValue f) :=
        congrArg (fun φ => φ (torusValue f))
          (hcongr _ _ T.doubleTorusMap_comp_action)
      _ = _ := congrArg (fun φ => φ (torusValue f))
        (dominantFunctionFieldMap_comp μ[G].left T.torus.left)
  have hinner : dominantFunctionFieldMap T.torus.left (torusValue f)=ι₀ f :=
    openTorusRationalAlgHom_pullback k n X.left T.torus.left f
  apply dominantFunctionFieldMap_injective T.doubleTorusMap
  change dominantFunctionFieldMap T.doubleTorusMap
    (dominantFunctionFieldMap (γ[G,X]).left (torusValue f)) = _
  rw [hact,hinner]
  change _=dominantFunctionFieldMap (G ◁ T.torus).left
    (torusProductRationalMap k n X
      (Algebra.TensorProduct.map (AlgHom.id k A) torusValue (Coalgebra.comul (R:=k) f)))
  rw [torusProductRationalMap_natural,hmap]
  let jA : Spec (CommRingCat.of A) ⟶ G.left := 𝟙 G.left
  letI : IsOpenImmersion jA := by
    change IsOpenImmersion (𝟙 (Spec (CommRingCat.of A)))
    infer_instance
  letI : jA.IsOver (Spec (CommRingCat.of k)) := by
    constructor
    change (𝟙 G.left) ≫ G.hom = G.hom
    exact Category.id_comp _
  have hι : ι₀=affineCoordinateValueAlgHom k A jA := by
    ext a
    rfl
  rw [hι,torusProductRationalMap_affineCoordinate]
  let jAA : Spec (CommRingCat.of (A⊗[k]A)) ⟶ (G⊗G).left :=
    (pullbackSpecIso k A A).inv
  have hjAA : IsOpenImmersion jAA :=
    IsOpenImmersion.of_isIso (pullbackSpecIso k A A).inv
  have hchart : torusProductAffineChart k n G A jA=
      (pullbackSpecIso (CommRingCat.of k) (CommRingCat.of A) (CommRingCat.of A)).inv := by
    apply pullback.hom_ext
    · exact (torusProductAffineChart_fst k n G A jA).trans
        (pullbackSpecIso_inv_fst k A A).symm
    · exact (torusProductAffineChart_snd k n G A jA).trans
        ((Category.comp_id _).trans (pullbackSpecIso_inv_snd k A A).symm)
  have hcoordinate
      (j l : Spec (CommRingCat.of (A⊗[k]A)) ⟶ (G⊗G).left)
      [IsOpenImmersion j] [IsOpenImmersion l] (heq : j=l) :
      affineOpenCoordinateMap (CommRingCat.of (A⊗[k]A)) j =
        affineOpenCoordinateMap (CommRingCat.of (A⊗[k]A)) l := by
    subst l
    rfl
  exact (T.torus_mul_rational f).trans
    (congrArg (fun φ => φ (Coalgebra.comul (R:=k) f))
      (@hcoordinate (torusProductAffineChart k n G A jA) jAA
        (torusProductAffineChart_isOpenImmersion k n G A jA) hjAA hchart)).symm

/-- Every individual Laurent character component of a true global
section remains a true global section. -/
theorem torusSectionCharacters_component_of_unitFrames (E : CartierData X.left)
    (hE : E.localCocycle.HasUnitFramesOn T.torusOpen)
    (f : AddMonoidAlgebra k (Fin n→ℤ))
    (hf : f∈torusSectionCharacters k n X.left T.torus.left E)
    (m : Fin n→ℤ) :
    AddMonoidAlgebra.single m (f.coeff m)∈
      torusSectionCharacters k n X.left T.torus.left E := by
  let G := splitTorusOver k (Fin n→ℤ)
  let A := AddMonoidAlgebra k (Fin n→ℤ)
  let torusValue := openTorusRationalAlgHom k n X.left T.torus.left
  let p := (snd G X).left
  let δf := Algebra.TensorProduct.map (AlgHom.id k A) torusValue (Coalgebra.comul (R:=k) f)
  change torusValue (AddMonoidAlgebra.single m (f.coeff m))∈E.sectionValueRange ⊤
  apply E.mem_globalSectionValueRange_of_affine_ratios
  intro i U hU hAff hUi
  letI := hU
  letI : Nonempty (p ⁻¹ᵁ U) := dominant_preimage_nonempty p U
  let q := (E.localCocycle.generator i : X.left.functionField)
  let w : A⊗[k]X.left.functionField := δf*(1⊗ₜ[k]q⁻¹)
  have hwregular : torusProductRationalMap k n X w∈
      Set.range ((G⊗X).left.germToFunctionField (p ⁻¹ᵁ U)) := by
    have h := T.action_ratio_regular_of_unitFrames E hE f hf i U hUi
    have hunit : torusProductRationalMap k n X (1⊗ₜ[k]q⁻¹)=
        (dominantFunctionFieldMap p q)⁻¹ := by
      simp only [torusProductRationalMap_tmul,map_one,one_mul,map_inv₀]
      exact one_mul _
    have hwvalue : torusProductRationalMap k n X w=
        dominantFunctionFieldMap (γ[G,X]).left (torusValue f) /
          dominantFunctionFieldMap p q := by
      calc
        _ = torusProductRationalMap k n X δf *
            torusProductRationalMap k n X (1⊗ₜ[k]q⁻¹) :=
          map_mul (torusProductRationalMap k n X) δf (1⊗ₜ[k]q⁻¹)
        _ = dominantFunctionFieldMap (γ[G,X]).left (torusValue f) *
            (dominantFunctionFieldMap p q)⁻¹ :=
          congrArg₂ (fun a b => a*b) (T.action_pullback_laurent f).symm hunit
        _ = _ := (div_eq_mul_inv _ _).symm
    obtain ⟨r,hr⟩ := h
    exact ⟨r,hr.trans hwvalue.symm⟩
  have hw := (torusProductRationalMap_mem_regularAffine_iff k n X U hAff w).mp hwregular
  have hcoeff := characterCoefficient_mem_range k
    (BaseSections.regularValueAlgHom k U).toLinearMap m w hw
  rw [show characterCoefficient k m w=
      torusValue (AddMonoidAlgebra.single m (f.coeff m))*q⁻¹ from
    characterCoefficient_coaction_ratio k torusValue f q⁻¹ m] at hcoeff
  obtain ⟨r,hr⟩ := hcoeff
  refine ⟨r,?_⟩
  change X.left.germToFunctionField U r = _
  change X.left.germToFunctionField U r =
    torusValue (AddMonoidAlgebra.single m (f.coeff m))*q⁻¹ at hr
  simpa only [div_eq_mul_inv,q] using hr

theorem normalizedGlobalCharacters_component (D : CartierData X.left)
    (f : AddMonoidAlgebra k (Fin n→ℤ))
    (hf : f∈normalizedGlobalCharacters k n X.left T.torus.left D)
    (m : Fin n→ℤ) :
    AddMonoidAlgebra.single m (f.coeff m)∈
      normalizedGlobalCharacters k n X.left T.torus.left D := by
  apply (mem_normalizedGlobalCharacters_iff k n X.left T.torus.left D _).mpr
  exact T.torusSectionCharacters_component_of_unitFrames
    (torusNormalizedCartier k n X.left T.torus.left D)
    (torusNormalizedCartier_unitFrames k n X.left T.torus.left D) f
    ((mem_normalizedGlobalCharacters_iff k n X.left T.torus.left D f).mp hf) m

end LocallyNoetherian

/-- Genuine character stability for any actual Cartier presentation
whose local frames have been proved to be units on the dense torus. -/
theorem torusSectionCharacters_isCharacterStable_of_unitFrames
    (E : CartierData X.left) (hE : E.localCocycle.HasUnitFramesOn T.torusOpen) :
    IsCharacterStable k (torusSectionCharacters k n X.left T.torus.left E) := by
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  apply (isCharacterStable_iff_components k _).mpr
  exact T.torusSectionCharacters_component_of_unitFrames E hE

/-- The actual normalized global-section representation of an arbitrary
smooth intrinsic toric embedding is a genuine Hopf subrepresentation.
Local Noetherianity is derived from smoothness, not included as input. -/
theorem normalizedGlobalCharacters_isCharacterStable (D : CartierData X.left) :
    IsCharacterStable k (normalizedGlobalCharacters k n X.left T.torus.left D) := by
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  apply (isCharacterStable_iff_components k _).mpr
  exact T.normalizedGlobalCharacters_component D

/-- The resulting actual global-section space has its honest character
basis. This is a conclusion about the real sheaf sections. -/
def normalizedGlobalSectionCharacterCoordinates (D : CartierData X.left) :
    Γ((torusNormalizedCartier k n X.left T.torus.left D).sheaf,⊤) ≃ₗ[k]
      characterExponents k (normalizedGlobalCharacters k n X.left T.torus.left D) →₀ k :=
  (normalizedGlobalSectionCoordinates k n X.left T.torus.left D).trans
    (stableCharacterCoordinates k _ (T.normalizedGlobalCharacters_isCharacterStable D))

end PaperVerification.ToricSchemes.SplitToricEmbedding
end
end Source_ToricIntrinsicSectionCoaction
-- END ORIGINAL PaperVerification.ToricIntrinsicSectionCoaction


