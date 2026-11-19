module

public import ToricPower.NegativeFunctorTotalMap
public import ToricPower.NegativeFunctorTotalCoordinates
public import Mathlib.Algebra.Homology.Embedding.HomEquiv
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace ToricPower.NegativeFunctorTotal

universe u v w z

variable {A : Type u} [Category.{v} A] [Preadditive A] [HasZeroObject A]
  {B : Type w} [Category.{z} B] [Preadditive B] [HasZeroObject B] [HasFiniteBiproducts B]
  (Φ : A ⥤ ChainComplex B ℕ) [Φ.Additive]
  (width : ℕ) (M : A)

abbrev singleInput : CochainComplex A ℤ := (CochainComplex.singleFunctor A 0).obj M

def singleInputRowIso (q : Fin width) :
    (row Φ (singleInput M) q).X (-(chainDegree q : ℤ)) ≅ (Φ.obj M).X (chainDegree q) := by
  exact (degree Φ (chainDegree q)).mapIso
    (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0 M
      (-(chainDegree q : ℤ)+(chainDegree q : ℤ)) (neg_add_cancel _))

theorem singleInputRow_isZero (a : ℤ) (q : Fin width)
    (different : a+(chainDegree q : ℤ) ≠ 0) :
    IsZero ((row Φ (singleInput M) q).X a) :=
  (degree Φ (chainDegree q)).map_isZero
    (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M _ different)

theorem singleInput_otherRows_zero (q : Fin width) (r : Fin width) (different : r ≠ q) :
    IsZero ((row Φ (singleInput M) r).X (-(chainDegree q : ℤ))) := by
  apply singleInputRow_isZero
  intro same
  have equal : r.rev=q.rev := Fin.ext (by change chainDegree r = chainDegree q; omega)
  apply different
  simpa only [Fin.rev_rev] using congrArg Fin.rev equal

def singleInputProjectionIso (q : Fin width) :
    (total Φ width (singleInput M)).X (-(chainDegree q : ℤ)) ≅
      (row Φ (singleInput M) q).X (-(chainDegree q : ℤ)) where
  hom := biproduct.π (fun r => (row Φ (singleInput M) r).X (-(chainDegree q : ℤ))) q
  inv := biproduct.ι (fun r => (row Φ (singleInput M) r).X (-(chainDegree q : ℤ))) q
  hom_inv_id := by
    apply biproduct.hom_ext
    intro r
    by_cases same : r=q
    · subst r
      simp only [Category.assoc,biproduct.ι_π_self,Category.comp_id,Category.id_comp]
    · exact (singleInput_otherRows_zero Φ width M q r same).eq_of_tgt _ _
  inv_hom_id := biproduct.ι_π_self _ _

def singleInputFiniteDegreeIso (q : Fin width) :
    (total Φ width (singleInput M)).X (-(chainDegree q : ℤ)) ≅ (Φ.obj M).X (chainDegree q) :=
  singleInputProjectionIso Φ width M q ≪≫ singleInputRowIso Φ width M q

theorem singleInputTotal_isZero_positive (a : ℤ) (positive : 0 < a) :
    IsZero ((total Φ width (singleInput M)).X a) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply biproduct.hom_ext
  intro q
  exact (singleInputRow_isZero Φ width M a q (by omega)).eq_of_tgt _ _

theorem singleInputTotal_isZero_below (q : ℕ) (high : width ≤ q) :
    IsZero ((total Φ width (singleInput M)).X (-(q : ℤ))) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply biproduct.hom_ext
  intro r
  have bound : chainDegree r < width := r.rev.isLt
  exact (singleInputRow_isZero Φ width M _ r (by omega)).eq_of_tgt _ _

variable (outside : ∀ q, width ≤ q → IsZero ((Φ.obj M).X q))

theorem singleInputHorizontal_conjugate (x y : ℤ) (hx : x=0) (hy : y=0) (p q : ℕ) :
    (degree Φ p).map (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0 M x hx).inv ≫
      transportedHorizontal Φ (singleInput M) x y p q (hx.trans hy.symm) ≫
      (degree Φ q).map (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0 M y hy).hom =
        (Φ.obj M).d p q := by
  subst x
  subst y
  let e := HomologicalComplex.singleObjXSelf (.up ℤ) 0 M
  change (Φ.map e.inv).f p ≫ ((Φ.obj ((singleInput M).X 0)).d p q ≫ 𝟙 _) ≫
      (Φ.map e.hom).f q = _
  rw [Category.comp_id,← Category.assoc,(Φ.map e.inv).comm p q,Category.assoc]
  have composition := congrArg (fun f => f.f q)
    (show Φ.map e.inv ≫ Φ.map e.hom = 𝟙 (Φ.obj M) by
      rw [← Φ.map_comp,e.inv_hom_id,Φ.map_id])
  change _ ≫ (Φ.map e.inv ≫ Φ.map e.hom).f q = _
  rw [composition]
  exact Category.comp_id _

theorem singleInputRowIso_horizontal (p q : Fin width) :
    (singleInputRowIso Φ width M p).inv ≫
      transportedHorizontal Φ (singleInput M)
        (-(chainDegree p : ℤ)+(chainDegree p : ℤ)) (-(chainDegree q : ℤ)+(chainDegree q : ℤ))
        (chainDegree p) (chainDegree q) (by omega) ≫ (singleInputRowIso Φ width M q).hom =
      (Φ.obj M).d (chainDegree p) (chainDegree q) :=
  singleInputHorizontal_conjugate Φ M _ _ (neg_add_cancel _) (neg_add_cancel _) _ _

theorem singleInputFiniteDegreeIso_d (p q : Fin width) (step : chainDegree p=chainDegree q+1) :
    (total Φ width (singleInput M)).d (-(chainDegree p : ℤ)) (-(chainDegree q : ℤ)) ≫
        (singleInputFiniteDegreeIso Φ width M q).hom =
      (singleInputFiniteDegreeIso Φ width M p).hom ≫ (Φ.obj M).d (chainDegree p) (chainDegree q) := by
  apply (cancel_epi (singleInputFiniteDegreeIso Φ width M p).inv).mp
  simp only [Iso.inv_hom_id_assoc]
  have entry := congrArg (fun f => (singleInputRowIso Φ width M p).inv ≫ f ≫
      (singleInputRowIso Φ width M q).hom)
    (total_d_entry_next Φ (singleInput M) (-(chainDegree p : ℤ)) (-(chainDegree q : ℤ))
      (by omega) p q step)
  simpa only [singleInputFiniteDegreeIso,Iso.trans_inv,Iso.trans_hom,
    singleInputProjectionIso,Category.assoc] using
    entry.trans (singleInputRowIso_horizontal Φ width M p q)

def singleInputTransportedFiniteDegreeIso (p : Fin width) (a : ℕ)
    (equal : chainDegree p=a) :
    (total Φ width (singleInput M)).X (-(a : ℤ)) ≅ (Φ.obj M).X a :=
  eqToIso (congrArg (fun n : ℕ => (total Φ width (singleInput M)).X (-(n : ℤ))) equal.symm) ≪≫
    singleInputFiniteDegreeIso Φ width M p ≪≫ eqToIso (congrArg (Φ.obj M).X equal)

theorem singleInputTransportedFiniteDegreeIso_d (p q : Fin width) (a b : ℕ)
    (hp : chainDegree p=a) (hq : chainDegree q=b) (step : a=b+1) :
    (singleInputTransportedFiniteDegreeIso Φ width M p a hp).hom ≫ (Φ.obj M).d a b =
      (total Φ width (singleInput M)).d (-(a : ℤ)) (-(b : ℤ)) ≫
        (singleInputTransportedFiniteDegreeIso Φ width M q b hq).hom := by
  subst a
  subst b
  simpa only [singleInputTransportedFiniteDegreeIso,eqToIso_refl,Iso.refl_trans,
    Iso.trans_refl] using (singleInputFiniteDegreeIso_d Φ width M p q step).symm

def singleInputDegreeIso (q : ℕ) :
    (total Φ width (singleInput M)).X (-(q : ℤ)) ≅ (Φ.obj M).X q :=
  if inside : q < width then
    singleInputTransportedFiniteDegreeIso Φ width M (⟨q,inside⟩ : Fin width).rev q
      (by simp only [chainDegree,Fin.rev_rev])
  else (singleInputTotal_isZero_below Φ width M q (by omega)).iso (outside q (by omega))

def singleInputRestrictionIso :
    (total Φ width (singleInput M)).restriction ComplexShape.embeddingDownNat ≅ Φ.obj M :=
  HomologicalComplex.Hom.isoOfComponents (singleInputDegreeIso Φ width M outside)
    (fun p q related => by
      obtain rfl : q+1=p := related
      change (singleInputDegreeIso Φ width M outside (q+1)).hom ≫ (Φ.obj M).d (q+1) q =
        (total Φ width (singleInput M)).d (-((q+1 : ℕ) : ℤ)) (-(q : ℤ)) ≫
          (singleInputDegreeIso Φ width M outside q).hom
      by_cases inside : q+1<width
      · simp only [singleInputDegreeIso,dif_pos inside,dif_pos (show q<width by omega)]
        exact singleInputTransportedFiniteDegreeIso_d Φ width M
          (⟨q+1,inside⟩ : Fin width).rev (⟨q,by omega⟩ : Fin width).rev (q+1) q
          (by simp only [chainDegree,Fin.rev_rev]) (by simp only [chainDegree,Fin.rev_rev]) rfl
      · exact (singleInputTotal_isZero_below Φ width M (q+1) (by omega)).eq_of_src _ _)

theorem singleInputRestriction_hasLift :
    ComplexShape.embeddingDownNat.HasLift (singleInputRestrictionIso Φ width M outside).hom := by
  intro j hj a ha
  have positive : 0<a := by
    by_contra nonpositive
    apply hj.notMem ha (-a).toNat
    change -(((-a).toNat : ℕ) : ℤ)=a
    rw [Int.toNat_of_nonneg (by omega),neg_neg]
  rw [(singleInputTotal_isZero_positive Φ width M a positive).eq_of_src
    ((total Φ width (singleInput M)).d a _) 0,zero_comp]

def singleInputExtendedMap :
    total Φ width (singleInput M) ⟶ (Φ.obj M).extend ComplexShape.embeddingDownNat :=
  ComplexShape.embeddingDownNat.liftExtend (singleInputRestrictionIso Φ width M outside).hom
    (singleInputRestriction_hasLift Φ width M outside)

instance singleInputExtendedMap_isIso : IsIso (singleInputExtendedMap Φ width M outside) := by
  have components : ∀ a, IsIso ((singleInputExtendedMap Φ width M outside).f a) := by
    intro a
    by_cases nonpositive : a≤0
    · have equal : ComplexShape.embeddingDownNat.f (-a).toNat=a := by
        change -(((-a).toNat : ℕ) : ℤ)=a
        rw [Int.toNat_of_nonneg (by omega),neg_neg]
      exact (ComplexShape.embeddingDownNat.isIso_liftExtend_f_iff
        (singleInputRestrictionIso Φ width M outside).hom
        (singleInputRestriction_hasLift Φ width M outside) equal).2 inferInstance
    · exact (singleInputTotal_isZero_positive Φ width M a (by omega)).isIso
        ((Φ.obj M).isZero_extend_X ComplexShape.embeddingDownNat a
          (fun q hq => by change -(q : ℤ)=a at hq; omega)) _
  exact HomologicalComplex.Hom.isIso_of_components _

def singleInputIso :
    total Φ width (singleInput M) ≅ (Φ.obj M).extend ComplexShape.embeddingDownNat :=
  asIso (singleInputExtendedMap Φ width M outside)

end ToricPower.NegativeFunctorTotal

end

