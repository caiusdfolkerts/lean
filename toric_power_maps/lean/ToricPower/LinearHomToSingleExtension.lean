module

public import ToricPower.LinearHomToSingleCoefficients

/-!
# The full signed comparison with ordinary coefficient cochains

The explicit sign normalization extends over all integer degrees. Both
complexes vanish in negative degree, and the extension map is a genuine
chain isomorphism, natural in every coefficient morphism.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite
open CochainComplex HomComplex HomologicalComplex

namespace ToricPower

universe u v r
variable (R : Type r) [CommRing R]
  {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  (K : ChainComplex C ℕ) (Y : C)

/-- Hom into a degree-zero target has no negative cochains when its
source is an actual nonpositive extended chain complex. -/
theorem homToSingle_isZero_negative (n : ℤ) (hn : n < 0) :
    IsZero ((linearHomComplex R (K.extend ComplexShape.embeddingDownNat)
      ((CochainComplex.singleFunctor C 0).obj Y)).X n) := by
  let e := Cochain.toSingleLinearEquiv (R := R) (K := K.extend ComplexShape.embeddingDownNat)
    (X := Y) (show -n+n=0 by omega)
  have hz : IsZero ((K.extend ComplexShape.embeddingDownNat).X (-n)) :=
    CochainComplex.isZero_of_isStrictlyLE (K.extend ComplexShape.embeddingDownNat) 0 (-n) (by omega)
  letI : Subsingleton ((K.extend ComplexShape.embeddingDownNat).X (-n) ⟶ Y) :=
    ⟨fun f g => hz.eq_of_src f g⟩
  letI : Subsingleton (Cochain (K.extend ComplexShape.embeddingDownNat)
      ((CochainComplex.singleFunctor C 0).obj Y) n) := e.injective.subsingleton
  change IsZero (ModuleCat.of R (Cochain (K.extend ComplexShape.embeddingDownNat)
    ((CochainComplex.singleFunctor C 0).obj Y) n))
  exact ModuleCat.isZero_of_subsingleton _

/-- The boundary condition for the genuine extension of the signed
comparison follows from its actual zero negative-degree source. -/
theorem homToSingleRestriction_hasLift :
    ComplexShape.embeddingUpNat.HasLift (homToSingleRestrictionIso R K Y).hom := by
  intro j hj n hn
  have hneg : n < 0 := by
    by_contra h
    have hn' : 0 ≤ n := by omega
    exact hj.notMem hn n.toNat (by simp [ComplexShape.embeddingUpNat, Int.toNat_of_nonneg hn'])
  rw [(homToSingle_isZero_negative R K Y n hneg).eq_of_src
    ((linearHomComplex R (K.extend ComplexShape.embeddingDownNat)
      ((CochainComplex.singleFunctor C 0).obj Y)).d n _) 0, zero_comp]

/-- The full integer-indexed chain map, including the zero negative degrees. -/
def homToSingleExtendedMap :
    linearHomComplex R (K.extend ComplexShape.embeddingDownNat)
      ((CochainComplex.singleFunctor C 0).obj Y) ⟶
        (ordinaryChainCoefficients R K Y).extend ComplexShape.embeddingUpNat :=
  ComplexShape.embeddingUpNat.liftExtend (homToSingleRestrictionIso R K Y).hom
    (homToSingleRestriction_hasLift R K Y)

instance homToSingleExtendedMap_isIso : IsIso (homToSingleExtendedMap R K Y) := by
  have components : ∀ n, IsIso ((homToSingleExtendedMap R K Y).f n) := by
    intro n
    by_cases hn : 0 ≤ n
    · let m := n.toNat
      have hm : ComplexShape.embeddingUpNat.f m = n := by
        dsimp [m, ComplexShape.embeddingUpNat]
        exact Int.toNat_of_nonneg hn
      exact (ComplexShape.embeddingUpNat.isIso_liftExtend_f_iff
        (homToSingleRestrictionIso R K Y).hom (homToSingleRestriction_hasLift R K Y) hm).2
          inferInstance
    · exact (homToSingle_isZero_negative R K Y n (by omega)).isIso
        ((ordinaryChainCoefficients R K Y).isZero_extend_X ComplexShape.embeddingUpNat n
          (fun m hm => by change (m : ℤ) = n at hm; omega)) _
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The full complex-linear chain isomorphism, with the actual signed
Hom differential and every original ordinary coefficient differential. -/
def homToSingleExtendedIso :
    linearHomComplex R (K.extend ComplexShape.embeddingDownNat)
      ((CochainComplex.singleFunctor C 0).obj Y) ≅
        (ordinaryChainCoefficients R K Y).extend ComplexShape.embeddingUpNat :=
  asIso (homToSingleExtendedMap R K Y)

/-- The ordinary coefficient map induced by an arbitrary target morphism. -/
def ordinaryChainCoefficientsMap {Y Z : C} (f : Y ⟶ Z) :
    ordinaryChainCoefficients R K Y ⟶ ordinaryChainCoefficients R K Z :=
  (NatTrans.mapHomologicalComplex ((linearYoneda R C).map f) (.up ℕ)).app K.op

/-- Unsigned coordinate evaluation commutes with every target map. -/
theorem homToSingleRawDegreeEquiv_naturality {Y Z : C} (f : Y ⟶ Z) (n : ℕ)
    (z : Cochain (K.extend ComplexShape.embeddingDownNat)
      ((CochainComplex.singleFunctor C 0).obj Y) (n : ℤ)) :
    homToSingleRawDegreeEquiv R K Z n
      (homCochainPostcomp R (K.extend ComplexShape.embeddingDownNat)
        ((CochainComplex.singleFunctor C 0).map f) (n : ℤ) z) =
      homToSingleRawDegreeEquiv R K Y n z ≫ f := by
  obtain ⟨g, rfl⟩ := Cochain.toSingleMk_surjective z (-(n : ℤ)) (by omega)
  change homToSingleRawDegreeEquiv R K Z n
    ((Cochain.toSingleMk g _).comp (.ofHom ((CochainComplex.singleFunctor C 0).map f))
      (add_zero (n : ℤ))) = _
  rw [← Cochain.toSingleMk_postcomp, homToSingleRawDegreeEquiv_toSingleMk,
    homToSingleRawDegreeEquiv_toSingleMk, Category.assoc]

/-- Naturality of every degree sign, before extending the coefficient complex. -/
theorem homToSingleRestrictionIso_naturality {Y Z : C} (f : Y ⟶ Z) :
    HomologicalComplex.restrictionMap
        (linearHomComplexMap R (K.extend ComplexShape.embeddingDownNat)
          ((CochainComplex.singleFunctor C 0).map f)) ComplexShape.embeddingUpNat ≫
        (homToSingleRestrictionIso R K Z).hom =
      (homToSingleRestrictionIso R K Y).hom ≫ ordinaryChainCoefficientsMap R K f := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change homDualSign n • homToSingleRawDegreeEquiv R K Z n
      (homCochainPostcomp R (K.extend ComplexShape.embeddingDownNat)
        ((CochainComplex.singleFunctor C 0).map f) (n : ℤ) z) =
    (homDualSign n • homToSingleRawDegreeEquiv R K Y n z) ≫ f
  rw [homToSingleRawDegreeEquiv_naturality, Linear.units_smul_comp]

/-- The full signed chain isomorphism is natural in every actual
coefficient map, before localization. -/
theorem homToSingleExtendedIso_naturality {Y Z : C} (f : Y ⟶ Z) :
    linearHomComplexMap R (K.extend ComplexShape.embeddingDownNat)
        ((CochainComplex.singleFunctor C 0).map f) ≫
        (homToSingleExtendedIso R K Z).hom =
      (homToSingleExtendedIso R K Y).hom ≫
        HomologicalComplex.extendMap (ordinaryChainCoefficientsMap R K f)
          ComplexShape.embeddingUpNat := by
  apply (ComplexShape.embeddingUpNat.homEquiv _ _).injective
  apply Subtype.ext
  change ComplexShape.embeddingUpNat.homRestrict (_ ≫ _) =
    ComplexShape.embeddingUpNat.homRestrict (_ ≫ _)
  rw [ComplexShape.embeddingUpNat.homRestrict_precomp,
    ComplexShape.embeddingUpNat.homRestrict_comp_extendMap]
  change _ ≫ ComplexShape.embeddingUpNat.homRestrict
      (ComplexShape.embeddingUpNat.liftExtend (homToSingleRestrictionIso R K Z).hom
        (homToSingleRestriction_hasLift R K Z)) =
    ComplexShape.embeddingUpNat.homRestrict
      (ComplexShape.embeddingUpNat.liftExtend (homToSingleRestrictionIso R K Y).hom
        (homToSingleRestriction_hasLift R K Y)) ≫ _
  rw [ComplexShape.embeddingUpNat.homRestrict_liftExtend,
    ComplexShape.embeddingUpNat.homRestrict_liftExtend]
  exact homToSingleRestrictionIso_naturality R K f

end ToricPower
