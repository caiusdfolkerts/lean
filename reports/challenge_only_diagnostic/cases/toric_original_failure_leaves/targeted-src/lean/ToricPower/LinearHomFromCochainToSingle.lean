module

public import ToricPower.LinearHomToSingleExtension

/-! # Signed Hom from nonnegative cochains to a single target

The ordinary contravariant coefficient chains occupy nonpositive Hom
degrees. The explicit cumulative sign intertwines their original
boundary with the genuine signed Hom differential in every degree.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite
open CochainComplex HomComplex HomologicalComplex

namespace ToricPower

def cochainHomDualSign : ℕ → ℤˣ
  | 0 => 1
  | q+1 => (q : ℤ).negOnePow * cochainHomDualSign q

theorem cochainHomDualSign_step (q : ℕ) :
    cochainHomDualSign q * (-(q : ℤ)).negOnePow = cochainHomDualSign (q+1) := by
  rw [cochainHomDualSign,Int.negOnePow_neg,mul_comm]

universe u v r
variable (R : Type r) [CommRing R]
  {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]

def cochainHomDualSignLinearEquiv (M : Type*) [AddCommGroup M] [Module R M] (q : ℕ) :
    M ≃ₗ[R] M where
  toFun x := cochainHomDualSign q • x
  invFun x := cochainHomDualSign q • x
  left_inv x := by
    change cochainHomDualSign q • (cochainHomDualSign q • x) = x
    rw [smul_smul,Int.units_mul_self,one_smul]
  right_inv x := by
    change cochainHomDualSign q • (cochainHomDualSign q • x) = x
    rw [smul_smul,Int.units_mul_self,one_smul]
  map_add' x y := smul_add _ _ _
  map_smul' a x := smul_comm _ _ _

variable (K : CochainComplex C ℕ) (Y : C)

def ordinaryCochainCoefficients : ChainComplex (ModuleCat.{v} R) ℕ :=
  (((linearYoneda R C).obj Y).mapHomologicalComplex (.down ℕ)).obj K.op

def cochainHomToSingleRawDegreeEquiv (q : ℕ) :
    Cochain (K.extend ComplexShape.embeddingUpNat)
      ((CochainComplex.singleFunctor C 0).obj Y) (-(q : ℤ)) ≃ₗ[R] (K.X q ⟶ Y) :=
  (Cochain.toSingleLinearEquiv (R := R)
    (show (q : ℤ)+(-(q : ℤ))=0 by omega)).trans
      (Linear.homCongr R (K.extendXIso ComplexShape.embeddingUpNat
        (show ComplexShape.embeddingUpNat.f q = (q : ℤ) by rfl)) (Iso.refl Y))

theorem cochainHomToSingleRawDegreeEquiv_toSingleMk (q : ℕ)
    (f : (K.extend ComplexShape.embeddingUpNat).X (q : ℤ) ⟶ Y) :
    cochainHomToSingleRawDegreeEquiv R K Y q
      (Cochain.toSingleMk f (show (q : ℤ)+(-(q : ℤ))=0 by omega)) =
      (K.extendXIso ComplexShape.embeddingUpNat
        (show ComplexShape.embeddingUpNat.f q = (q : ℤ) by rfl)).inv ≫ f := by
  simp [cochainHomToSingleRawDegreeEquiv,Linear.homCongr]

theorem cochainHomToSingleRawDegreeEquiv_d (q : ℕ)
    (z : Cochain (K.extend ComplexShape.embeddingUpNat)
      ((CochainComplex.singleFunctor C 0).obj Y) (-((q+1 : ℕ) : ℤ))) :
    cochainHomToSingleRawDegreeEquiv R K Y q
        (δ (-((q+1 : ℕ) : ℤ)) (-(q : ℤ)) z) =
      (-(q : ℤ)).negOnePow •
        (K.d q (q+1) ≫ cochainHomToSingleRawDegreeEquiv R K Y (q+1) z) := by
  obtain ⟨f,rfl⟩ := Cochain.toSingleMk_surjective z ((q+1 : ℕ) : ℤ) (by omega)
  rw [Cochain.δ_toSingleMk _ _ (-(q : ℤ)) (q : ℤ) (by omega)]
  simp only [Units.smul_def,map_zsmul,cochainHomToSingleRawDegreeEquiv_toSingleMk]
  congr 1
  rw [K.extend_d_eq ComplexShape.embeddingUpNat
    (show ComplexShape.embeddingUpNat.f q = (q : ℤ) by rfl)
    (show ComplexShape.embeddingUpNat.f (q+1) = ((q+1 : ℕ) : ℤ) by rfl)]
  simp only [Category.assoc,Iso.inv_hom_id_assoc]

def cochainHomToSingleDegreeEquiv (q : ℕ) :
    Cochain (K.extend ComplexShape.embeddingUpNat)
      ((CochainComplex.singleFunctor C 0).obj Y) (-(q : ℤ)) ≃ₗ[R] (K.X q ⟶ Y) :=
  (cochainHomToSingleRawDegreeEquiv R K Y q).trans
    (cochainHomDualSignLinearEquiv R _ q)

def cochainHomToSingleRestrictionIso :
    (linearHomComplex R (K.extend ComplexShape.embeddingUpNat)
      ((CochainComplex.singleFunctor C 0).obj Y)).restriction ComplexShape.embeddingDownNat ≅
        ordinaryCochainCoefficients R K Y :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q => (cochainHomToSingleDegreeEquiv R K Y q).toModuleIso)
    (fun q p hqp => by
      obtain rfl : p+1=q := hqp
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      change K.d p (p+1) ≫ (cochainHomDualSign (p+1) •
          cochainHomToSingleRawDegreeEquiv R K Y (p+1) z) =
        cochainHomDualSign p • cochainHomToSingleRawDegreeEquiv R K Y p
          (δ (-((p+1 : ℕ) : ℤ)) (-(p : ℤ)) z)
      rw [cochainHomToSingleRawDegreeEquiv_d,smul_smul,cochainHomDualSign_step,
        Linear.comp_units_smul])

theorem cochainHomToSingle_isZero_positive (q : ℤ) (positive : 0 < q) :
    IsZero ((linearHomComplex R (K.extend ComplexShape.embeddingUpNat)
      ((CochainComplex.singleFunctor C 0).obj Y)).X q) := by
  let e := Cochain.toSingleLinearEquiv (R := R) (K := K.extend ComplexShape.embeddingUpNat)
    (X := Y) (show -q+q=0 by omega)
  have zero : IsZero ((K.extend ComplexShape.embeddingUpNat).X (-q)) :=
    CochainComplex.isZero_of_isStrictlyGE (K.extend ComplexShape.embeddingUpNat) 0 (-q) (by omega)
  letI : Subsingleton ((K.extend ComplexShape.embeddingUpNat).X (-q) ⟶ Y) :=
    ⟨fun f g => zero.eq_of_src f g⟩
  letI : Subsingleton (Cochain (K.extend ComplexShape.embeddingUpNat)
      ((CochainComplex.singleFunctor C 0).obj Y) q) := e.injective.subsingleton
  change IsZero (ModuleCat.of R (Cochain (K.extend ComplexShape.embeddingUpNat)
    ((CochainComplex.singleFunctor C 0).obj Y) q))
  exact ModuleCat.isZero_of_subsingleton _

theorem cochainHomToSingleRestriction_hasLift :
    ComplexShape.embeddingDownNat.HasLift (cochainHomToSingleRestrictionIso R K Y).hom := by
  intro j hj q hq
  have positive : 0 < q := by
    by_contra h
    have nonnegative : 0 ≤ -q := by omega
    apply hj.notMem hq (-q).toNat
    change -(((-q).toNat : ℕ) : ℤ) = q
    rw [Int.toNat_of_nonneg nonnegative,neg_neg]
  rw [(cochainHomToSingle_isZero_positive R K Y q positive).eq_of_src
    ((linearHomComplex R (K.extend ComplexShape.embeddingUpNat)
      ((CochainComplex.singleFunctor C 0).obj Y)).d q _) 0,zero_comp]

def cochainHomToSingleExtendedMap :
    linearHomComplex R (K.extend ComplexShape.embeddingUpNat)
      ((CochainComplex.singleFunctor C 0).obj Y) ⟶
        (ordinaryCochainCoefficients R K Y).extend ComplexShape.embeddingDownNat :=
  ComplexShape.embeddingDownNat.liftExtend (cochainHomToSingleRestrictionIso R K Y).hom
    (cochainHomToSingleRestriction_hasLift R K Y)

instance cochainHomToSingleExtendedMap_isIso : IsIso (cochainHomToSingleExtendedMap R K Y) := by
  have components : ∀ q, IsIso ((cochainHomToSingleExtendedMap R K Y).f q) := by
    intro q
    by_cases nonpositive : q ≤ 0
    · have equal : ComplexShape.embeddingDownNat.f (-q).toNat = q := by
        change -(((-q).toNat : ℕ) : ℤ) = q
        rw [Int.toNat_of_nonneg (by omega),neg_neg]
      exact (ComplexShape.embeddingDownNat.isIso_liftExtend_f_iff
        (cochainHomToSingleRestrictionIso R K Y).hom
        (cochainHomToSingleRestriction_hasLift R K Y) equal).2 inferInstance
    · exact (cochainHomToSingle_isZero_positive R K Y q (by omega)).isIso
        ((ordinaryCochainCoefficients R K Y).isZero_extend_X ComplexShape.embeddingDownNat q
          (fun m hm => by change -(m : ℤ) = q at hm; omega)) _
  exact HomologicalComplex.Hom.isIso_of_components _

def cochainHomToSingleExtendedIso :
    linearHomComplex R (K.extend ComplexShape.embeddingUpNat)
      ((CochainComplex.singleFunctor C 0).obj Y) ≅
        (ordinaryCochainCoefficients R K Y).extend ComplexShape.embeddingDownNat :=
  asIso (cochainHomToSingleExtendedMap R K Y)

end ToricPower

end
