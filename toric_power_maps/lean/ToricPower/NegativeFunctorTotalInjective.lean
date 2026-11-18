module

public import ToricPower.NegativeFunctorTotalMap
public import ToricPower.DerivedFunctorOnInjectiveComplex
public import ToricPower.DerivedHomPlusExt

/-!
# Injective models for the finite negative total

A horizontal chain complex of finite width lowers a vertical lower bound
by at most its width. If its coefficient functors preserve injectives,
the total of an injective complex is again termwise injective. The last
isomorphism uses the actual total of the injective-resolution map and
Mathlib's right-derived unit; its quasi-isomorphism hypothesis is explicit.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace ToricPower.NegativeFunctorTotal

universe u v w z u' v'

variable {A : Type u} [Category.{v} A] [Abelian A]
  {B : Type w} [Category.{z} B] [Abelian B] [HasFiniteBiproducts B]
  (Φ : A ⥤ ChainComplex B ℕ) [Φ.Additive] (width : ℕ)

theorem total_isStrictlyGE (K : CochainComplex A ℤ) (lower : ℤ)
    [K.IsStrictlyGE lower] : (total Φ width K).IsStrictlyGE (lower-width) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro a below
  apply (IsZero.iff_id_eq_zero _).mpr
  apply biproduct.hom_ext
  intro q
  have rowZero : IsZero ((row Φ K q).X a) := by
    change IsZero ((degree Φ (chainDegree q)).obj (K.X (a+(chainDegree q : ℤ))))
    apply (degree Φ (chainDegree q)).map_isZero
    have degreeBound : chainDegree q < width := q.rev.isLt
    exact K.isZero_of_isStrictlyGE lower (a+(chainDegree q : ℤ)) (by omega)
  exact rowZero.eq_of_tgt _ _

/-- The genuine finite total, with its proved lower bound. -/
def plus (K : CochainComplex.Plus A) : CochainComplex.Plus B := by
  refine ⟨total Φ width K.obj, ?_⟩
  obtain ⟨lower, bounded⟩ := K.property
  letI := bounded
  exact ⟨lower-width, total_isStrictlyGE Φ width K.obj lower⟩

theorem total_terms_injective
    (preservesInjectives : ∀ (q : ℕ) (M : A), Injective M → Injective ((Φ.obj M).X q))
    (I : CochainComplex A ℤ) [∀ p, Injective (I.X p)] (a : ℤ) :
    Injective ((total Φ width I).X a) := by
  letI : ∀ q : Fin width, Injective ((row Φ I q).X a) := fun q =>
    preservesInjectives (chainDegree q) (I.X (a+(chainDegree q : ℤ))) inferInstance
  change Injective (⨁ fun q : Fin width => (row Φ I q).X a)
  infer_instance

variable [EnoughInjectives A] [EnoughInjectives B] [HasDerivedCategory B]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory D]
  (H : B ⥤ D) [H.Additive]

/-- Compute the actual right-derived functor on the total of a single
object, using the total of its chosen injective resolution. -/
def rightDerivedSingleTotalIso
    (preservesInjectives : ∀ (q : ℕ) (M : A), Injective M → Injective ((Φ.obj M).X q))
    (M : A)
    (replacementQuasiIso : QuasiIso (map Φ width (singleInjectiveCochainι M))) :
    H.rightDerivedFunctorPlus.obj
      (DerivedCategory.Plus.Q.obj (plus Φ width (singlePlusComplex M))) ≅
    DerivedCategory.Plus.Q.obj
      (H.mapCochainComplexPlus.obj
        (plus Φ width ⟨singleInjectiveCochain M, ⟨0, inferInstance⟩⟩)) := by
  let J : CochainComplex.Plus B :=
    plus Φ width ⟨singleInjectiveCochain M, ⟨0, inferInstance⟩⟩
  let f : plus Φ width (singlePlusComplex M) ⟶ J :=
    ObjectProperty.homMk (map Φ width (singleInjectiveCochainι M))
  have quasi : (CochainComplex.Plus.quasiIso B) f := replacementQuasiIso
  letI : IsIso (DerivedCategory.Plus.Q.map f) :=
    Localization.inverts DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso B) f quasi
  letI : ∀ a, Injective (J.obj.X a) := fun a =>
    total_terms_injective Φ width preservesInjectives (singleInjectiveCochain M) a
  exact H.rightDerivedFunctorPlus.mapIso (asIso (DerivedCategory.Plus.Q.map f)) ≪≫
    rightDerivedFunctorPlusOnInjective H J

end ToricPower.NegativeFunctorTotal

end
