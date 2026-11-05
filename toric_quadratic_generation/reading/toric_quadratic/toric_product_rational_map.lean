module

public import PaperVerification.ToricAffineProductCharts

@[expose] public section

/-!
# Actual rational functions on a torus product

The tensor map is defined using the genuine two projections on generic
stalks. Its injectivity is proved on an actual nonempty affine chart,
after clearing finitely many coefficient denominators. For every actual
affine open, its regular-function range is exactly the tensor extension
of the original regular-function range.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory
open PaperVerification.ToricCharacters
open scoped TensorProduct BaseSections Classical

variable (k : Type u) [Field k] (n : ℕ)
    (X : Over (Spec (CommRingCat.of k)))
    [IsIntegral X.left] [IsLocallyNoetherian X.left]

local notation "A" => AddMonoidAlgebra k (Fin n→ℤ)
local notation "G" => splitTorusOver k (Fin n→ℤ)
local notation "Y" => Functor.obj (Over.forget (Spec (CommRingCat.of k))) (G ⊗ X)

local instance coefficientTorusDomain : IsDomain A := torusCoordinateRing_isDomain k n

local instance productRationalIntegral : IsIntegral Y := torusProduct_integral k n X

local instance productRationalOver : (Y).Over (Spec (CommRingCat.of k)) :=
  OverClass.fromOver (G ⊗ X)

instance torusProduct_firstProjection_surjective : Surjective (fst G X).left := by
  letI : Surjective X.hom := by
    constructor
    intro z
    exact ⟨Classical.choice (inferInstance : Nonempty X.left),Subsingleton.elim _ _⟩
  change Surjective (pullback.fst (G).hom X.hom)
  infer_instance

/-- Literal regular torus coordinates inside its actual generic stalk. -/
def torusCoordinateValueAlgHom : A →ₐ[k] (G).left.functionField := by
  let j : Spec (CommRingCat.of A) ⟶ (G).left := 𝟙 (G).left
  letI : IsOpenImmersion j := by change IsOpenImmersion (𝟙 (G).left); infer_instance
  letI : j.IsOver (Spec (CommRingCat.of k)) := by
    constructor
    change (𝟙 (G).left) ≫ (G).hom = (G).hom
    exact Category.id_comp _
  exact affineCoordinateValueAlgHom k A j

/-- The actual product rational embedding: character coordinates are
pulled through the first projection, coefficients through the second. -/
def torusProductRationalMap : A ⊗[k] X.left.functionField →ₐ[k] (Y).functionField :=
  Algebra.TensorProduct.lift
    ((BaseSections.dominantFunctionFieldAlgHom k (fst G X).left).comp
      (torusCoordinateValueAlgHom k n))
    (BaseSections.dominantFunctionFieldAlgHom k (snd G X).left)
    (fun _ _=>Commute.all _ _)

@[simp] theorem torusProductRationalMap_tmul (f : A) (z : X.left.functionField) :
    torusProductRationalMap k n X (f ⊗ₜ[k] z)=
      dominantFunctionFieldMap (fst G X).left (torusCoordinateValueAlgHom k n f)*
        dominantFunctionFieldMap (snd G X).left z := rfl

section AffineChart

variable (R : Type u) [CommRing R] [IsDomain R] [Algebra k R]
    (j : Spec (CommRingCat.of R)⟶X.left)
    [IsOpenImmersion j] [j.IsOver (Spec (CommRingCat.of k))]

/-- On an actual affine product chart the abstract tensor formula is
exactly the genuine chart coordinate-to-generic-stalk map. -/
theorem torusProductRationalMap_affineCoordinate (t : A ⊗[k] R) :
    letI := latticeTensor_isDomain k n R
    torusProductRationalMap k n X
        (Algebra.TensorProduct.map (AlgHom.id k A) (affineCoordinateValueAlgHom k R j) t)=
      affineOpenCoordinateMap (CommRingCat.of (A ⊗[k] R))
        (torusProductAffineChart k n X R j) t := by
  letI := latticeTensor_isDomain k n R
  let j₀ : Spec (CommRingCat.of A) ⟶ (G).left := 𝟙 (G).left
  letI : IsOpenImmersion j₀ := by
    change IsOpenImmersion (𝟙 (G).left)
    infer_instance
  induction t using TensorProduct.induction_on with
  | zero =>
      exact (congrArg (torusProductRationalMap k n X)
        (map_zero (Algebra.TensorProduct.map (AlgHom.id k A)
          (affineCoordinateValueAlgHom k R j)))).trans
        ((map_zero (torusProductRationalMap k n X)).trans
          (map_zero (affineOpenCoordinateMap (CommRingCat.of (A ⊗[k] R))
            (torusProductAffineChart k n X R j))).symm)
  | tmul f r =>
      simp only [Algebra.TensorProduct.map_tmul,AlgHom.id_apply,torusProductRationalMap_tmul]
      change dominantFunctionFieldMap (fst G X).left
          (affineOpenCoordinateMap (CommRingCat.of A) j₀ f)*
        dominantFunctionFieldMap (snd G X).left
          (affineOpenCoordinateMap (CommRingCat.of R) j r)=_
      rw [dominantFunctionFieldMap_affineCoordinate (CommRingCat.of A)
        (CommRingCat.of (A ⊗[k] R)) j₀
        (torusProductAffineChart k n X R j) (fst G X).left
        (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] R).toRingHom)
        (by exact (torusProductAffineChart_fst k n X R j).trans (Category.comp_id _).symm),
        dominantFunctionFieldMap_affineCoordinate (CommRingCat.of R)
        (CommRingCat.of (A ⊗[k] R)) j
        (torusProductAffineChart k n X R j) (snd G X).left
        (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : R →ₐ[k] A ⊗[k] R).toRingHom)
        (torusProductAffineChart_snd k n X R j)]
      rw [← map_mul]
      congr 1
      change (f ⊗ₜ[k] (1 : R)) * ((1 : A) ⊗ₜ[k] r) = f ⊗ₜ[k] r
      rw [Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]
  | add t v ht hv => simp only [map_add,ht,hv]

theorem torusProductRationalMap_affineCoordinate_range :
    letI := latticeTensor_isDomain k n R
    let l := torusProductAffineChart k n X R j
    letI : Nonempty (l ''ᵁ (⊤ : (Spec (CommRingCat.of (A ⊗[k] R))).Opens)) :=
      openImmersion_image_nonempty l ⊤
    Set.range (fun t : A ⊗[k] R=>torusProductRationalMap k n X
      (Algebra.TensorProduct.map (AlgHom.id k A) (affineCoordinateValueAlgHom k R j) t))=
      Set.range ((Y).germToFunctionField (l ''ᵁ (⊤ : (Spec (CommRingCat.of (A ⊗[k] R))).Opens))) := by
  letI := latticeTensor_isDomain k n R
  simp_rw [torusProductRationalMap_affineCoordinate]
  exact affineOpenCoordinate_range (CommRingCat.of (A ⊗[k] R))
    (torusProductAffineChart k n X R j)

end AffineChart

theorem torusProductRationalMap_injective : Function.Injective (torusProductRationalMap k n X) := by
  obtain ⟨U,hU,hx,hsub⟩ := exists_isAffineOpen_mem_and_subset
    (show genericPoint X.left∈(⊤ : X.left.Opens) from trivial)
  letI : Nonempty U := ⟨⟨genericPoint X.left,hx⟩⟩
  let R := Γ(X.left,U)
  let j := hU.fromSpec
  letI : j.IsOver (Spec (CommRingCat.of k)) := affineOpen_fromSpec_isOver k X.left U hU
  letI : IsFractionRing R X.left.functionField :=
    functionField_isFractionRing_of_isAffineOpen X.left U hU
  letI : IsScalarTower k R X.left.functionField :=
    IsScalarTower.of_algebraMap_eq (fun c=>(BaseSections.germ_scalarMap k U c).symm)
  letI := latticeTensor_isDomain k n R
  letI := latticeTensor_isDomain k n X.left.functionField
  let F := Algebra.TensorProduct.map (AlgHom.id k A)
    (BaseSections.regularValueAlgHom k U)
  have hF (t : A ⊗[k] R) : torusProductRationalMap k n X (F t)=
      affineOpenCoordinateMap (CommRingCat.of (A ⊗[k] R))
        (torusProductAffineChart k n X R j) t := by
    have he : BaseSections.regularValueAlgHom k U=affineCoordinateValueAlgHom k R j := by
      ext r
      exact (affineOpenCoordinateMap_fromSpec X.left U hU r).symm
    rw [show F=Algebra.TensorProduct.map (AlgHom.id k A)
      (affineCoordinateValueAlgHom k R j) from congrArg (Algebra.TensorProduct.map (AlgHom.id k A)) he]
    exact torusProductRationalMap_affineCoordinate k n X R j t
  apply (injective_iff_map_eq_zero _).mpr
  intro w hw
  obtain ⟨d,hd,t,ht⟩ := tensor_exists_common_denominator k A R X.left.functionField w
  change F t=(1 ⊗ₜ[k] X.left.germToFunctionField U d)*w at ht
  have hct : affineOpenCoordinateMap (CommRingCat.of (A ⊗[k] R))
      (torusProductAffineChart k n X R j) t=0 := by
    rw [← hF,ht,map_mul,hw,mul_zero]
  have ht0 : t=0 := by
    apply (openImmersionGlobalToFunctionField_injective
      (torusProductAffineChart k n X R j)).comp
        (Scheme.ΓSpecIso (CommRingCat.of (A ⊗[k] R))).commRingCatIsoToRingEquiv.symm.injective
    change affineOpenCoordinateMap (CommRingCat.of (A ⊗[k] R))
        (torusProductAffineChart k n X R j) t =
      affineOpenCoordinateMap (CommRingCat.of (A ⊗[k] R))
        (torusProductAffineChart k n X R j) 0
    exact hct.trans (map_zero (affineOpenCoordinateMap (CommRingCat.of (A ⊗[k] R))
      (torusProductAffineChart k n X R j))).symm
  have hden : (1 ⊗ₜ[k] X.left.germToFunctionField U d : A ⊗[k] X.left.functionField)≠0 := by
    intro hz
    have hm := congrArg (torusProductRationalMap k n X) hz
    simp only [torusProductRationalMap_tmul,map_one,one_mul,map_zero] at hm
    have hdz : X.left.germToFunctionField U d=0 :=
      (dominantFunctionFieldMap (snd G X).left).injective (hm.trans (map_zero _).symm)
    exact hd (X.left.germToFunctionField_injective U (hdz.trans (map_zero _).symm))
  rw [ht0,map_zero] at ht
  exact (mul_eq_zero.mp ht.symm).resolve_left hden

theorem torusProductRationalMap_regularAffine_range (U : X.left.Opens)
    (hU : IsAffineOpen U) [Nonempty U] :
    letI : Nonempty ((snd G X).left ⁻¹ᵁ U) := dominant_preimage_nonempty (snd G X).left U
    Set.range (fun t : A ⊗[k] Γ(X.left,U)=>torusProductRationalMap k n X
      (Algebra.TensorProduct.map (AlgHom.id k A) (BaseSections.regularValueAlgHom k U) t))=
      Set.range ((Y).germToFunctionField ((snd G X).left ⁻¹ᵁ U)) := by
  letI : Nonempty ((snd G X).left ⁻¹ᵁ U) := dominant_preimage_nonempty (snd G X).left U
  let R := Γ(X.left,U)
  let j := hU.fromSpec
  letI : j.IsOver (Spec (CommRingCat.of k)) := affineOpen_fromSpec_isOver k X.left U hU
  letI := latticeTensor_isDomain k n R
  let l := torusProductAffineChart k n X R j
  have he : BaseSections.regularValueAlgHom k U=affineCoordinateValueAlgHom k R j := by
    ext r
    exact (affineOpenCoordinateMap_fromSpec X.left U hU r).symm
  have hV : l ''ᵁ (⊤ : (Spec (CommRingCat.of (A ⊗[k] R))).Opens)=(snd G X).left ⁻¹ᵁ U := by
    rw [Scheme.Hom.image_top_eq_opensRange,torusProductAffineChart_opensRange,
      hU.opensRange_fromSpec]
  rw [he]
  letI : Nonempty (l ''ᵁ (⊤ : (Spec (CommRingCat.of (A ⊗[k] R))).Opens)) :=
    openImmersion_image_nonempty l ⊤
  have hRange {V W : (Y).Opens} [Nonempty V] [Nonempty W] (h : V=W) :
      Set.range ((Y).germToFunctionField V)=Set.range ((Y).germToFunctionField W) := by
    subst W
    rfl
  exact (torusProductRationalMap_affineCoordinate_range k n X R j).trans
    (hRange hV)

/-- Exact coefficientwise regularity on every affine open, stated in
the actual function field of the actual product scheme. -/
theorem torusProductRationalMap_mem_regularAffine_iff (U : X.left.Opens)
    (hU : IsAffineOpen U) [Nonempty U] (w : A ⊗[k] X.left.functionField) :
    letI : Nonempty ((snd G X).left ⁻¹ᵁ U) := dominant_preimage_nonempty (snd G X).left U
    torusProductRationalMap k n X w∈
      Set.range ((Y).germToFunctionField ((snd G X).left ⁻¹ᵁ U)) ↔
      w∈LinearMap.range (TensorProduct.map (LinearMap.id : A →ₗ[k] A)
        (BaseSections.regularValueAlgHom k U).toLinearMap) := by
  letI : Nonempty ((snd G X).left ⁻¹ᵁ U) := dominant_preimage_nonempty (snd G X).left U
  rw [← torusProductRationalMap_regularAffine_range k n X U hU]
  constructor
  · rintro ⟨t,ht⟩
    exact ⟨t,torusProductRationalMap_injective k n X ht⟩
  · rintro ⟨t,rfl⟩
    exact ⟨t,rfl⟩

section Naturality

variable {Z : Over (Spec (CommRingCat.of k))}
    [IsIntegral Z.left] [IsLocallyNoetherian Z.left]
    (j : Z⟶X) [IsDominant j.left]
    [IsDominant (splitTorusOver k (Fin n→ℤ) ◁ j).left]

theorem torusProductRationalMap_natural (w : A ⊗[k] X.left.functionField) :
    dominantFunctionFieldMap (G ◁ j).left (torusProductRationalMap k n X w)=
      torusProductRationalMap k n Z
        (Algebra.TensorProduct.map (AlgHom.id k A)
          (BaseSections.dominantFunctionFieldAlgHom k j.left) w) := by
  have hfst : (G ◁ j).left≫(fst G X).left=(fst G Z).left := by
    change ((G ◁ j)≫fst G X).left=(fst G Z).left
    simp
  have hsnd : (G ◁ j).left≫(snd G X).left=(snd G Z).left≫j.left := by
    change ((G ◁ j)≫snd G X).left=((snd G Z)≫j).left
    simp
  have hmap {Y₁ Y₂ : Scheme.{u}} [IsIntegral Y₁] [IsIntegral Y₂]
      (f g : Y₁ ⟶ Y₂) [IsDominant f] [IsDominant g] (h : f=g) :
      dominantFunctionFieldMap f=dominantFunctionFieldMap g := by
    subst g
    rfl
  have hfstField :
      (dominantFunctionFieldMap (G ◁ j).left).comp
        (dominantFunctionFieldMap (fst G X).left) =
      dominantFunctionFieldMap (fst G Z).left :=
    (dominantFunctionFieldMap_comp (G ◁ j).left (fst G X).left).symm.trans
      (hmap _ _ hfst)
  have hsndField :
      (dominantFunctionFieldMap (G ◁ j).left).comp
        (dominantFunctionFieldMap (snd G X).left) =
      (dominantFunctionFieldMap (snd G Z).left).comp
        (dominantFunctionFieldMap j.left) :=
    (dominantFunctionFieldMap_comp (G ◁ j).left (snd G X).left).symm.trans
      ((hmap _ _ hsnd).trans
        (dominantFunctionFieldMap_comp (snd G Z).left j.left))
  induction w using TensorProduct.induction_on with
  | zero =>
      exact ((congrArg (dominantFunctionFieldMap (G ◁ j).left)
        (map_zero (torusProductRationalMap k n X))).trans
        (map_zero (dominantFunctionFieldMap (G ◁ j).left))).trans
        ((congrArg (torusProductRationalMap k n Z)
          (map_zero (Algebra.TensorProduct.map (AlgHom.id k A)
            (BaseSections.dominantFunctionFieldAlgHom k j.left)))).trans
          (map_zero (torusProductRationalMap k n Z))).symm
  | tmul f z =>
      simp only [Algebra.TensorProduct.map_tmul,AlgHom.id_apply,torusProductRationalMap_tmul,map_mul]
      change dominantFunctionFieldMap (G ◁ j).left
          (dominantFunctionFieldMap (fst G X).left (torusCoordinateValueAlgHom k n f))*
        dominantFunctionFieldMap (G ◁ j).left
          (dominantFunctionFieldMap (snd G X).left z)=_
      exact congrArg₂ (· * ·)
        (congrArg (fun φ : (G).left.functionField →+* (G ⊗ Z).left.functionField =>
          φ (torusCoordinateValueAlgHom k n f)) hfstField)
        (congrArg (fun φ : X.left.functionField →+* (G ⊗ Z).left.functionField =>
          φ z) hsndField)
  | add w v hw hv => simp only [map_add,hw,hv]

end Naturality

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.torusProductRationalMap_injective
#print axioms PaperVerification.ToricSchemes.torusProductRationalMap_mem_regularAffine_iff
