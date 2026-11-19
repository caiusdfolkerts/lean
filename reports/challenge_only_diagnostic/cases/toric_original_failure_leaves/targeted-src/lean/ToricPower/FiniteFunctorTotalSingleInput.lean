module

public import ToricPower.FiniteFunctorTotalMap
public import ToricPower.FiniteFunctorTotalCoordinates
public import Mathlib.Algebra.Homology.Embedding.HomEquiv
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-! # A single input recovers the original finite cochain complex -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace ToricPower.FunctorTotal

universe u v w z
variable {A : Type u} [Category.{v} A] [Preadditive A] [HasZeroObject A]
  {B : Type w} [Category.{z} B] [Preadditive B] [HasZeroObject B] [HasFiniteBiproducts B]
  (Φ : A ⥤ CochainComplex B ℕ) [Φ.Additive] (width : ℕ) (M : A)

abbrev singleInput : CochainComplex A ℤ := (CochainComplex.singleFunctor A 0).obj M

def singleInputRowIso (q : Fin width) :
    (row Φ (singleInput M) q).X (q.val : ℤ) ≅ (Φ.obj M).X q.val :=
  (degree Φ q.val).mapIso
    (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0 M
      ((q.val : ℤ)+ -(q.val : ℤ)) (add_neg_cancel _))

theorem singleInputRow_isZero (a : ℤ) (q : Fin width)
    (different : a+ -(q.val : ℤ) ≠ 0) :
    IsZero ((row Φ (singleInput M) q).X a) :=
  (degree Φ q.val).map_isZero
    (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M _ different)

theorem singleInput_otherRows_zero (q r : Fin width) (different : r ≠ q) :
    IsZero ((row Φ (singleInput M) r).X (q.val : ℤ)) := by
  apply singleInputRow_isZero
  intro equal
  exact different (Fin.ext (by omega))

def singleInputProjectionIso (q : Fin width) :
    (total Φ width (singleInput M)).X (q.val : ℤ) ≅
      (row Φ (singleInput M) q).X (q.val : ℤ) where
  hom := biproduct.π (fun r => (row Φ (singleInput M) r).X (q.val : ℤ)) q
  inv := biproduct.ι (fun r => (row Φ (singleInput M) r).X (q.val : ℤ)) q
  hom_inv_id := by
    apply biproduct.hom_ext
    intro r
    by_cases same : r=q
    · subst r
      simp only [Category.assoc,biproduct.ι_π_self,Category.comp_id,Category.id_comp]
    · exact (singleInput_otherRows_zero Φ width M q r same).eq_of_tgt _ _
  inv_hom_id := biproduct.ι_π_self _ _

def singleInputFiniteDegreeIso (q : Fin width) :
    (total Φ width (singleInput M)).X (q.val : ℤ) ≅ (Φ.obj M).X q.val :=
  singleInputProjectionIso Φ width M q ≪≫ singleInputRowIso Φ width M q

theorem singleInputTotal_isZero_negative (a : ℤ) (negative : a<0) :
    IsZero ((total Φ width (singleInput M)).X a) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply biproduct.hom_ext
  intro q
  exact (singleInputRow_isZero Φ width M a q (by omega)).eq_of_tgt _ _

theorem singleInputTotal_isZero_above (q : ℕ) (high : width ≤ q) :
    IsZero ((total Φ width (singleInput M)).X (q : ℤ)) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply biproduct.hom_ext
  intro r
  have bound := r.isLt
  exact (singleInputRow_isZero Φ width M _ r (by omega)).eq_of_tgt _ _

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
        ((p.val : ℤ)+ -(p.val : ℤ)) ((q.val : ℤ)+ -(q.val : ℤ))
        p.val q.val (by omega) ≫ (singleInputRowIso Φ width M q).hom =
      (Φ.obj M).d p.val q.val :=
  singleInputHorizontal_conjugate Φ M _ _ (add_neg_cancel _) (add_neg_cancel _) _ _

theorem singleInputFiniteDegreeIso_d (p q : Fin width) (step : p.val+1=q.val) :
    (total Φ width (singleInput M)).d (p.val : ℤ) (q.val : ℤ) ≫
        (singleInputFiniteDegreeIso Φ width M q).hom =
      (singleInputFiniteDegreeIso Φ width M p).hom ≫ (Φ.obj M).d p.val q.val := by
  apply (cancel_epi (singleInputFiniteDegreeIso Φ width M p).inv).mp
  simp only [Iso.inv_hom_id_assoc]
  have entry := congrArg (fun f => (singleInputRowIso Φ width M p).inv ≫ f ≫
      (singleInputRowIso Φ width M q).hom)
    (total_d_entry_next Φ (singleInput M) (p.val : ℤ) (q.val : ℤ) (by omega) p q step)
  simpa only [singleInputFiniteDegreeIso,Iso.trans_inv,Iso.trans_hom,
    singleInputProjectionIso,Category.assoc] using
    entry.trans (singleInputRowIso_horizontal Φ width M p q)

variable (outside : ∀ q, width ≤ q → IsZero ((Φ.obj M).X q))

def singleInputDegreeIso (q : ℕ) :
    (total Φ width (singleInput M)).X (q : ℤ) ≅ (Φ.obj M).X q :=
  if inside : q<width then singleInputFiniteDegreeIso Φ width M ⟨q,inside⟩
  else (singleInputTotal_isZero_above Φ width M q (by omega)).iso (outside q (by omega))

def singleInputRestrictionIso :
    (total Φ width (singleInput M)).restriction ComplexShape.embeddingUpNat ≅ Φ.obj M :=
  HomologicalComplex.Hom.isoOfComponents (singleInputDegreeIso Φ width M outside)
    (fun p q related => by
      obtain rfl : p+1=q := related
      change (singleInputDegreeIso Φ width M outside p).hom ≫ (Φ.obj M).d p (p+1) =
        (total Φ width (singleInput M)).d (p : ℤ) ((p+1 : ℕ) : ℤ) ≫
          (singleInputDegreeIso Φ width M outside (p+1)).hom
      by_cases inside : p+1<width
      · simp only [singleInputDegreeIso,dif_pos inside,dif_pos (show p<width by omega)]
        exact (singleInputFiniteDegreeIso_d Φ width M ⟨p,by omega⟩ ⟨p+1,inside⟩ rfl).symm
      · exact (outside (p+1) (by omega)).eq_of_tgt _ _)

theorem singleInputRestriction_hasLift :
    ComplexShape.embeddingUpNat.HasLift (singleInputRestrictionIso Φ width M outside).hom := by
  intro j hj a ha
  have negative : a<0 := by
    by_contra nonnegative
    apply hj.notMem ha a.toNat
    change (a.toNat : ℤ)=a
    exact Int.toNat_of_nonneg (by omega)
  rw [(singleInputTotal_isZero_negative Φ width M a negative).eq_of_src
    ((total Φ width (singleInput M)).d a _) 0,zero_comp]

def singleInputExtendedMap :
    total Φ width (singleInput M) ⟶ (Φ.obj M).extend ComplexShape.embeddingUpNat :=
  ComplexShape.embeddingUpNat.liftExtend (singleInputRestrictionIso Φ width M outside).hom
    (singleInputRestriction_hasLift Φ width M outside)

instance singleInputExtendedMap_isIso : IsIso (singleInputExtendedMap Φ width M outside) := by
  have components : ∀ a, IsIso ((singleInputExtendedMap Φ width M outside).f a) := by
    intro a
    by_cases nonnegative : 0≤a
    · have equal : ComplexShape.embeddingUpNat.f a.toNat=a := by
        change (a.toNat : ℤ)=a
        exact Int.toNat_of_nonneg nonnegative
      exact (ComplexShape.embeddingUpNat.isIso_liftExtend_f_iff
        (singleInputRestrictionIso Φ width M outside).hom
        (singleInputRestriction_hasLift Φ width M outside) equal).2 inferInstance
    · exact (singleInputTotal_isZero_negative Φ width M a (by omega)).isIso
        ((Φ.obj M).isZero_extend_X ComplexShape.embeddingUpNat a
          (fun q hq => by change (q : ℤ)=a at hq; omega)) _
  exact HomologicalComplex.Hom.isIso_of_components _

def singleInputIso :
    total Φ width (singleInput M) ≅ (Φ.obj M).extend ComplexShape.embeddingUpNat :=
  asIso (singleInputExtendedMap Φ width M outside)

end ToricPower.FunctorTotal

end

