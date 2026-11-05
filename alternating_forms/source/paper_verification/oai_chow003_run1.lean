module

public import paper_verification.oai_chow002_run2
import all paper_verification.oai_chow002_run2
public import paper_verification.oai_chow000_run4
import all paper_verification.oai_chow000_run4
public import paper_verification.oai_chow001_run2
import all paper_verification.oai_chow001_run2
public import Mathlib.LinearAlgebra.Quotient.Basic
import all Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.KrullDimension.Polynomial
import all Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.Ideal.GoingDown
import all Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
import all Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
import all Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.FunctionField
import all Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.LinearAlgebra.Finsupp.LSum
import all Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.AlgebraicGeometry.AffineSpace
import all Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import all Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Algebra.MvPolynomial.Equiv
import all Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.AlgebraicGeometry.Noetherian
import all Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import all Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.PullbackCarrier
import all Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.Polynomial.Ideal
import all Mathlib.RingTheory.Polynomial.Ideal
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import all Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.LocalRing.Length
import all Mathlib.RingTheory.LocalRing.Length
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
import all Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.PrincipalIdealDomain
import all Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Algebra.Polynomial.FieldDivision
import all Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.RingTheory.Ideal.Height
import all Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Localization.Algebra
import all Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.RingHom.Flat
import all Mathlib.RingTheory.RingHom.Flat
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.PrettyPrinter

set_option Elab.async false

@[expose] public section ComponentSource_0
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.CycleLocalization -/

/-! # Cycle Localization -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.CycleLocalization.BundleCycles

noncomputable section

/-!
# LineBundleCycles: exact localization of dimension-graded finite cycles

For an actual closed immersion whose range is the complement of an open
immersion, precisely the cycles restricting to zero are pushed from the
closed part. The proof uses all coefficients and the actual point maps.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {U X Z : Scheme} [AlgebraicGeometry.IsNoetherian U]
    (i : U ⟶ X) [IsOpenImmersion i] (j : Z ⟶ X) [IsClosedImmersion j]
    (hcomp : Set.range j = (Set.range i)ᶜ) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)

include hcomp

/-- A cycle pushed from the closed complement restricts to zero on the open. -/
theorem openDimensionCycleRestriction_closed (d : ℕ)
    (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (j ≫ f) d →₀ ℚ) :
    Open.CycleRestriction.BundleCycles.openDimensionCycleRestriction i f d (Closed.CyclePushforward.BundleCycles.closedDimensionCyclePushforward j f d z) = 0 := by
  ext x
  change Finsupp.mapDomain (Closed.CyclePushforward.BundleCycles.closedDimensionPointMap j f d) z (Open.CycleRestriction.BundleCycles.openDimensionPointEmbedding i f d x) = 0
  apply Finsupp.mapDomain_of_notMem_range z _
  rintro ⟨y, hy⟩
  have hp : j y.1 = i x.1 := congrArg Subtype.val hy
  have hn : j y.1 ∉ Set.range i :=
    (congrArg (fun s : Set X => j y.1 ∈ s) hcomp).mp ⟨y.1, rfl⟩
  exact hn ⟨x.1, hp.symm⟩

/-- All coefficients of a cycle vanishing on the open lift to the actual closed complement. -/
theorem exists_closedDimensionCycle_of_zero_restriction (d : ℕ)
    (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) (hz : Open.CycleRestriction.BundleCycles.openDimensionCycleRestriction i f d z = 0) :
    ∃ w : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (j ≫ f) d →₀ ℚ, Closed.CyclePushforward.BundleCycles.closedDimensionCyclePushforward j f d w = z := by
  let e : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (j ≫ f) d ↪ Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d :=
    ⟨Closed.CyclePushforward.BundleCycles.closedDimensionPointMap j f d, Closed.CyclePushforward.BundleCycles.closedDimensionPointMap_injective j f d⟩
  have hs : ((z.support : Finset (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d)) : Set (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d)) ⊆
      Set.range e := by
    intro q hq
    have hqz : z q ≠ 0 := Finsupp.mem_support_iff.mp hq
    have hnot : q.1 ∉ Set.range i := by
      rintro ⟨x, hx⟩
      have hd : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) (i ≫ f) = d :=
        (ImmersionDimension.BundleCycles.pointClosure_dimension_immersion i f x).symm.trans
          ((congrArg (fun y => Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm y) f) hx).trans q.2)
      let p : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (i ≫ f) d := ⟨x, hd⟩
      have he : Open.CycleRestriction.BundleCycles.openDimensionPointEmbedding i f d p = q := Subtype.ext hx
      have hzero := congrArg (fun a => a p) hz
      change z (Open.CycleRestriction.BundleCycles.openDimensionPointEmbedding i f d p) = 0 at hzero
      exact hqz ((congrArg z he.symm).trans hzero)
    have hr : q.1 ∈ Set.range j :=
      (congrArg (fun s : Set X => q.1 ∈ s) hcomp).mpr hnot
    obtain ⟨y, hy⟩ := hr
    have hd : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm y) (j ≫ f) = d :=
      (Point.SupportDimension.BundleCycles.pointClosure_dimension_closedImmersion j f y).symm.trans
        ((congrArg (fun x => Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f) hy).trans q.2)
    exact ⟨⟨y, hd⟩, Subtype.ext hy⟩
  refine ⟨Finsupp.comapDomain e z e.injective.injOn, ?_⟩
  exact (Finsupp.embDomain_eq_mapDomain e (Finsupp.comapDomain e z e.injective.injOn)).symm.trans
    (Finsupp.embDomain_comapDomain hs)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.CycleLocalization.BundleCycles
end ComponentSource_0

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.CycleLocalization"

@[expose] public section ComponentSource_1
/- Original module: OAI.AlgebraicGeometry.Cycles.Functoriality.FunctionFields -/

/-! # Function Fields -/

namespace OAI.AlgebraicGeometry.Cycles.Functoriality.FunctionFields.Construction

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

/-- A finitely generated field tower of equal finite transcendence degrees
has finite degree over the intermediate field. -/
theorem finite_of_equal_trdeg (K E L : Type u) [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
    [FinTrdeg K E] [Algebra.EssFiniteType K L]
    (h : Algebra.trdeg K E = Algebra.trdeg K L) : Module.Finite E L := by
  have hsum : Algebra.trdeg K E + Algebra.trdeg E L = Algebra.trdeg K E :=
    (trdeg_add_eq K E (A := L)).trans h.symm
  have hz : Algebra.trdeg E L = 0 := by
    rcases Cardinal.add_eq_left_iff.mp hsum with hlarge | hzero
    · exact (not_le_of_gt (trdeg_lt_aleph0 K E)
        ((le_max_left _ _).trans hlarge)).elim
    · exact hzero
  let : Algebra.IsAlgebraic E L := trdeg_eq_zero_iff.mp hz
  let : Algebra.EssFiniteType E L := Algebra.EssFiniteType.of_comp K E L
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

variable {S T : Scheme.{u}} [IsIntegral S] [IsIntegral T]

/-- The actual generic-stalk pullback of a dominant morphism. -/
def genericFieldMap (i : S ⟶ T) (hη : i (genericPoint S) = genericPoint T) :
    T.functionField ⟶ S.functionField :=
  (T.presheaf.stalkCongr (Inseparable.of_eq hη.symm)).hom ≫
    i.stalkMap (genericPoint S)

theorem genericFieldMap_germ (i : S ⟶ T)
    (hη : i (genericPoint S) = genericPoint T) :
    T.presheaf.germ ⊤ (genericPoint T) (by trivial) ≫ genericFieldMap i hη =
      i.appTop ≫ S.presheaf.germ ⊤ (genericPoint S) (by trivial) := by
  simp only [genericFieldMap, TopCat.Presheaf.stalkCongr_hom, ← Category.assoc]
  have h := T.presheaf.germ_stalkSpecializes
    (show genericPoint T ∈ (⊤ : T.Opens) from trivial)
    (Inseparable.of_eq hη).specializes
  exact (congrArg
    (fun k : Γ(T, ⊤) ⟶ T.presheaf.stalk (i (genericPoint S)) =>
      k ≫ i.stalkMap (genericPoint S)) h).trans
    (i.germ_stalkMap ⊤ (genericPoint S) (by trivial))

theorem genericFieldMap_base {B : Scheme.{u}} (i : S ⟶ T)
    (hη : i (genericPoint S) = genericPoint T) (g : T ⟶ B) :
    Betti.AffineDimension.Realization.functionFieldBaseMap g ≫ genericFieldMap i hη =
      Betti.AffineDimension.Realization.functionFieldBaseMap (i ≫ g) := by
  simp only [Betti.AffineDimension.Realization.functionFieldBaseMap, Scheme.Hom.comp_appTop, Category.assoc]
  rw [genericFieldMap_germ]

variable {K : Type u} [Field K]

theorem genericFieldMap_scalar (i : S ⟶ T)
    (hη : i (genericPoint S) = genericPoint T) (g : T ⟶ Spec (.of K)) :
    (genericFieldMap i hη).hom.comp (Foundations.Scheme.FunctionFieldScalar.functionFieldScalarMap g) =
      Foundations.Scheme.FunctionFieldScalar.functionFieldScalarMap (i ≫ g) := by
  exact congrArg
    (fun h : Γ(Spec (.of K), ⊤) ⟶ S.functionField =>
      h.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom)
    (genericFieldMap_base i hη g)

/-- The function-field embedding respects the specified ground field. -/
def genericFieldAlgHom (i : S ⟶ T)
    (hη : i (genericPoint S) = genericPoint T) (g : T ⟶ Spec (.of K)) :
    letI := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra g
    letI := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (i ≫ g)
    T.functionField →ₐ[K] S.functionField := by
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra g
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (i ≫ g)
  exact { (genericFieldMap i hη).hom with
    commutes' := fun c => DFunLike.congr_fun (genericFieldMap_scalar i hη g) c }

/-- A dominant map cannot increase the dimension of its image. -/
theorem dimension_le_of_genericPoint (i : S ⟶ T)
    (hη : i (genericPoint S) = genericPoint T) (g : T ⟶ Spec (.of K))
    [LocallyOfFiniteType g] [LocallyOfFiniteType (i ≫ g)] :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension g ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (i ≫ g) := by
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra g
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (i ≫ g)
  apply (Nat.cast_le (α := Cardinal)).mp
  rw [Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_cast, Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_cast]
  exact trdeg_le_of_injective (genericFieldAlgHom i hη g)
    (genericFieldAlgHom i hη g).injective

/-- In the dimension-preserving case the actual generic-field embedding
is finite; this is not a finiteness assumption on the morphism. -/
theorem genericField_extension_finite (i : S ⟶ T)
    (hη : i (genericPoint S) = genericPoint T) (g : T ⟶ Spec (.of K))
    [LocallyOfFiniteType g] [LocallyOfFiniteType (i ≫ g)]
    (hdim : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension g = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (i ≫ g)) :
    letI := (genericFieldMap i hη).hom.toAlgebra
    Module.Finite T.functionField S.functionField := by
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra g
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (i ≫ g)
  let := (genericFieldMap i hη).hom.toAlgebra
  let : IsScalarTower K T.functionField S.functionField :=
    IsScalarTower.of_algHom (genericFieldAlgHom i hη g)
  let := Foundations.Scheme.FunctionFieldFiniteType.functionFieldScalar_finTrdeg g
  let := Foundations.Scheme.FunctionFieldFiniteType.functionFieldScalar_essFiniteType (i ≫ g)
  apply finite_of_equal_trdeg K T.functionField S.functionField
  rw [← Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_cast, ← Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_cast, hdim]

end

end OAI.AlgebraicGeometry.Cycles.Functoriality.FunctionFields.Construction
end ComponentSource_1

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Cycles.Functoriality.FunctionFields"

@[expose] public section ComponentSource_2
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.FunctionField -/

/-! # Function Field -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.FunctionField.BundleCycles

noncomputable section

/-!
# LineBundleCycles: rational functions on the actual support deformation

The constructed projection is surjective, hence dominant. Its generic
stalk map therefore embeds the original support's function field in the
deformation's function field. On every nonempty open, this is exactly
pullback of the regular-function representative by the structural map.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

universe u

/-- A surjective morphism of integral schemes sends the generic point to the generic point. -/
theorem genericPoint_eq_of_surjective {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    (i : A ⟶ B) (hi : Function.Surjective i) : i (genericPoint A) = genericPoint B := by
  apply IsGenericPoint.eq _ (genericPoint_spec B)
  have h := (genericPoint_spec A).image i.continuous
  simp only [Set.image_univ, hi.range_eq, closure_univ] at h
  exact h

/-- Generic-stalk pullback agrees with pullback on every nonempty open. -/
theorem genericFieldMap_germOn {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    (i : A ⟶ B) (hη : i (genericPoint A) = genericPoint B)
    (U : B.Opens) [Nonempty U] [Nonempty (i ⁻¹ᵁ U)] :
    B.germToFunctionField U ≫ Cycles.Functoriality.FunctionFields.Construction.genericFieldMap i hη =
      i.app U ≫ A.germToFunctionField (i ⁻¹ᵁ U) := by
  simp only [Cycles.Functoriality.FunctionFields.Construction.genericFieldMap, TopCat.Presheaf.stalkCongr_hom, ← Category.assoc]
  have hx : genericPoint A ∈ i ⁻¹ᵁ U :=
    (genericPoint_spec A).mem_open_set_iff (i ⁻¹ᵁ U).isOpen |>.mpr
      (by simpa using (show Nonempty (i ⁻¹ᵁ U) from inferInstance))
  have h := B.presheaf.germ_stalkSpecializes
    (show genericPoint B ∈ U from hη ▸ hx) (Inseparable.of_eq hη).specializes
  exact (congrArg
    (fun k : Γ(B, U) ⟶ B.presheaf.stalk (i (genericPoint A)) => k ≫ i.stalkMap (genericPoint A)) h).trans
    (i.germ_stalkMap U (genericPoint A) hx)

variable {X : Scheme.{u}} (I P : X.IdealSheafData) [IsIntegral P.subscheme]

theorem globalSupportDeformationToSupport_genericPoint :
    Support.Projection.BundleCycles.globalSupportDeformationToSupport I P (genericPoint (Global.SupportDeformation.BundleCycles.globalSupportDeformation I P)) =
      genericPoint P.subscheme :=
  genericPoint_eq_of_surjective (Support.Projection.BundleCycles.globalSupportDeformationToSupport I P)
    (Support.Projection.BundleCycles.globalSupportDeformationToSupport_surjective I P)

/-- The actual pullback embedding of support rational functions. -/
def globalSupportFunctionFieldMap :
    P.subscheme.functionField ⟶ (Global.SupportDeformation.BundleCycles.globalSupportDeformation I P).functionField :=
  Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (Support.Projection.BundleCycles.globalSupportDeformationToSupport I P)
    (globalSupportDeformationToSupport_genericPoint I P)

theorem globalSupportFunctionFieldMap_injective : Function.Injective (globalSupportFunctionFieldMap I P) :=
  (globalSupportFunctionFieldMap I P).hom.injective

theorem globalSupportFunctionFieldMap_ne_zero (g : P.subscheme.functionField) (hg : g ≠ 0) :
    globalSupportFunctionFieldMap I P g ≠ 0 := by
  intro h
  exact hg ((globalSupportFunctionFieldMap_injective I P)
    (h.trans (map_zero (globalSupportFunctionFieldMap I P).hom).symm))

/-- The regular representatives pull back by the actual scheme morphism on every open. -/
theorem globalSupportFunctionFieldMap_germOn (U : P.subscheme.Opens)
    [Nonempty U] [Nonempty (Support.Projection.BundleCycles.globalSupportDeformationToSupport I P ⁻¹ᵁ U)] :
    P.subscheme.germToFunctionField U ≫ globalSupportFunctionFieldMap I P =
      (Support.Projection.BundleCycles.globalSupportDeformationToSupport I P).app U ≫
        (Global.SupportDeformation.BundleCycles.globalSupportDeformation I P).germToFunctionField
          (Support.Projection.BundleCycles.globalSupportDeformationToSupport I P ⁻¹ᵁ U) :=
  genericFieldMap_germOn (Support.Projection.BundleCycles.globalSupportDeformationToSupport I P)
    (globalSupportDeformationToSupport_genericPoint I P) U

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.FunctionField.BundleCycles
end ComponentSource_2

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.FunctionField"

@[expose] public section ComponentSource_3
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.RationalDivisorRestriction -/

/-! # Rational Divisor Restriction -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.RationalDivisorRestriction.BundleCycles

noncomputable section

/-!
# LineBundleCycles: local orders of rational functions under open immersion

This extends the checked regular-function length comparison to fractions,
including poles. The ring-order argument follows the fraction transport
calculation in ProjectionFormula, using LineBundleCycles's independently checked length comparison.
The function-field compatibility is proved from actual stalk maps.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.Order

theorem ringOrderMonoid_equiv {R S : Type*} [CommRing R] [CommRing S]
    [IsDomain R] [IsDomain S] [IsNoetherianRing R] [IsNoetherianRing S]
    [Ring.KrullDimLE 1 R] [Ring.KrullDimLE 1 S] (e : R ≃+* S) (a : R) :
    Ring.ordMonoidWithZeroHom S (e a) = Ring.ordMonoidWithZeroHom R a := by
  by_cases ha : a = 0
  · subst a
    simp only [map_zero]
  have ha' : e a ≠ 0 := (map_ne_zero_iff _ e.injective).mpr ha
  have hR : Ring.ord R a = ((Ring.ord R a).toNat : ℕ∞) :=
    (ENat.natCast_toNat (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero ha))).symm
  have hS := (DivisorRestriction.BundleCycles.ringOrder_equiv e a).trans hR
  rw [Ring.ordMonoidWithZeroHom_eq_coe S (mem_nonZeroDivisors_of_ne_zero ha') hS,
    Ring.ordMonoidWithZeroHom_eq_coe R (mem_nonZeroDivisors_of_ne_zero ha) hR]

/-- Actual compatible ring and fraction-field isomorphisms preserve fraction orders. -/
theorem ringOrderFrac_equiv {R S K L : Type*} [CommRing R] [CommRing S]
    [IsDomain R] [IsDomain S] [IsNoetherianRing R] [IsNoetherianRing S]
    [Ring.KrullDimLE 1 R] [Ring.KrullDimLE 1 S]
    [Field K] [Field L] [Algebra R K] [Algebra S L]
    [IsFractionRing R K] [IsFractionRing S L]
    (e : R ≃+* S) (φ : K ≃+* L)
    (hφ : ∀ a : R, φ (algebraMap R K a) = algebraMap S L (e a)) (f : K) :
    Ring.ordFrac S (φ f) = Ring.ordFrac R f := by
  by_cases hf : f = 0
  · subst f
    simp only [map_zero]
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective R f
  have ha : a ≠ 0 := fun ha => hf (by simp [ha])
  have hb' : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  rw [map_div₀, hφ a, hφ b, map_div₀, map_div₀,
    Ring.ordFrac_eq_ord R ha, Ring.ordFrac_eq_ord R hb',
    Ring.ordFrac_eq_ord S ((map_ne_zero_iff _ e.injective).mpr ha),
    Ring.ordFrac_eq_ord S ((map_ne_zero_iff _ e.injective).mpr hb'),
    ringOrderMonoid_equiv e a, ringOrderMonoid_equiv e b]

universe u
variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

/-- Generic-stalk pullback commutes with the actual map from every local ring. -/
theorem genericFieldMap_stalk (i : X ⟶ Y)
    (hη : i (genericPoint X) = genericPoint Y) (x : X)
    (a : Y.presheaf.stalk (i x)) :
    Cycles.Functoriality.FunctionFields.Construction.genericFieldMap i hη (algebraMap (Y.presheaf.stalk (i x)) Y.functionField a) =
      algebraMap (X.presheaf.stalk x) X.functionField (i.stalkMap x a) := by
  have h : CommRingCat.ofHom (algebraMap (Y.presheaf.stalk (i x)) Y.functionField) ≫
      Cycles.Functoriality.FunctionFields.Construction.genericFieldMap i hη = i.stalkMap x ≫
        CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField) := by
    change Y.presheaf.stalkSpecializes ((genericPoint_spec Y).specializes trivial) ≫
      Cycles.Functoriality.FunctionFields.Construction.genericFieldMap i hη = i.stalkMap x ≫
        X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial)
    rw [Cycles.Functoriality.FunctionFields.Construction.genericFieldMap, TopCat.Presheaf.stalkCongr_hom,
      ← Category.assoc]
    exact (congrArg (fun k => k ≫ i.stalkMap (genericPoint X))
      (Y.presheaf.stalkSpecializes_comp (Inseparable.of_eq hη).specializes
        ((genericPoint_spec Y).specializes (Set.mem_univ (i x))))).trans
      (i.stalkSpecializes_stalkMap (genericPoint X) x
        ((genericPoint_spec X).specializes (Set.mem_univ x)))
  exact congrArg (fun k : Y.presheaf.stalk (i x) ⟶ X.functionField => k a) h

variable (i : X ⟶ Y) [IsOpenImmersion i]

def openFunctionFieldMap : Y.functionField ⟶ X.functionField :=
  Cycles.Functoriality.FunctionFields.Construction.genericFieldMap i (genericPoint_eq_of_isOpenImmersion i)

instance openFunctionFieldMap_isIso : IsIso (openFunctionFieldMap i) := by
  unfold openFunctionFieldMap Cycles.Functoriality.FunctionFields.Construction.genericFieldMap
  infer_instance

def openFunctionFieldIso : Y.functionField ≅ X.functionField := asIso (openFunctionFieldMap i)

theorem ord_openImmersion [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : Y.functionField) (x : X) :
    X.ord (openFunctionFieldMap i f) x = Y.ord f (i x) := by
  have hc : coheight (i x) = coheight x := coheight_eq_of_isOpenImmersion i
  by_cases hx : coheight x = 1
  · let : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
    let : Ring.KrullDimLE 1 (Y.presheaf.stalk (i x)) := krullDimLE_of_coheight_le (hc.trans hx).le
    rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hx,
      Scheme.ord_eq_ordHom_of_coheight_eq_one (hc.trans hx)]
    exact congrArg WithZero.log (ringOrderFrac_equiv
      (asIso (i.stalkMap x)).commRingCatIsoToRingEquiv
      (openFunctionFieldIso i).commRingCatIsoToRingEquiv
      (genericFieldMap_stalk i (genericPoint_eq_of_isOpenImmersion i) x) f)
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one hx,
      Scheme.ord_eq_zero_of_coheight_neq_one (fun h => hx (hc.symm.trans h))]

/-- The same finite principal divisor with rational coefficients. -/
def rationalPrincipalPointDivisor (A : Scheme.{u}) [IsIntegral A]
    [AlgebraicGeometry.IsNoetherian A] (f : A.functionField) : A →₀ ℚ :=
  (Ord.BundleCycles.principalDivisor A f).mapRange (fun n : ℤ => (n : ℚ)) Int.cast_zero

@[simp]
theorem rationalPrincipalPointDivisor_apply (A : Scheme.{u}) [IsIntegral A]
    [AlgebraicGeometry.IsNoetherian A] (f : A.functionField) (x : A) :
    rationalPrincipalPointDivisor A f x = (A.ord f x : ℚ) := rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.RationalDivisorRestriction.BundleCycles
end ComponentSource_3

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.RationalDivisorRestriction"

@[expose] public section ComponentSource_4
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.PrincipalPushforward -/

/-! # Principal Pushforward -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.PrincipalPushforward.BundleCycles

noncomputable section

/-!
# LineBundleCycles: closed pushforward of the complete principal divisor

The actual isomorphism between a reduced support and its closed image
identifies their function fields and every local-ring order, including
poles. Pushing the finite divisor therefore gives the genuine principal
divisor of the transported rational function on the image support.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

/-- Principal divisors transport under the actual function-field isomorphism. -/
theorem rationalPrincipalDivisor_iso {A B : Scheme} [IsIntegral A] [IsIntegral B]
    [AlgebraicGeometry.IsNoetherian A] [AlgebraicGeometry.IsNoetherian B]
    (e : A ≅ B) (g : A.functionField) :
    Finsupp.mapDomain e.hom (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor A g) =
      RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor B ((RationalDivisorRestriction.BundleCycles.openFunctionFieldIso e.hom).inv g) := by
  ext y
  obtain ⟨x, rfl⟩ := e.hom.homeomorph.surjective y
  have hi : Function.Injective e.hom := e.hom.homeomorph.injective
  change Finsupp.mapDomain e.hom (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor A g) (e.hom x) =
    RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor B ((RationalDivisorRestriction.BundleCycles.openFunctionFieldIso e.hom).inv g) (e.hom x)
  rw [Finsupp.mapDomain_apply_of_injective hi, RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor_apply,
    RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor_apply]
  have he : RationalDivisorRestriction.BundleCycles.openFunctionFieldMap e.hom ((RationalDivisorRestriction.BundleCycles.openFunctionFieldIso e.hom).inv g) = g :=
    Iso.inv_hom_id_apply (RationalDivisorRestriction.BundleCycles.openFunctionFieldIso e.hom) g
  exact congrArg (fun n : ℤ => (n : ℚ))
    ((congrArg (fun a => A.ord a x) he.symm).trans
      (RationalDivisorRestriction.BundleCycles.ord_openImmersion e.hom ((RationalDivisorRestriction.BundleCycles.openFunctionFieldIso e.hom).inv g) x))

variable {X Y : Scheme} (i : X ⟶ Y) [IsClosedImmersion i]

/-- The same rational function on the actual isomorphic closed-image support. -/
def closedImageRationalFunction (W : TopologicalSpace.IrreducibleCloseds X)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) :
    (CycleClass.Geometric.GenericPoint.reducedSupportScheme (SupportImage.BundleCycles.closedImageSupport i W)).functionField :=
  (RationalDivisorRestriction.BundleCycles.openFunctionFieldIso (SupportImage.BundleCycles.closedSupportImageIso i W).hom).inv g

theorem closedImageRationalFunction_ne_zero (W : TopologicalSpace.IrreducibleCloseds X)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0) :
    closedImageRationalFunction i W g ≠ 0 :=
  (map_ne_zero_iff _ (RationalDivisorRestriction.BundleCycles.openFunctionFieldIso (SupportImage.BundleCycles.closedSupportImageIso i W).hom).inv.hom.injective).mpr hg

variable [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]

/-- Closed pushforward preserves all coefficients of the actual principal divisor. -/
theorem closedPushforward_principalPointDivisor (W : TopologicalSpace.IrreducibleCloseds X)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) :
    Finsupp.mapDomain i (Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g) =
      Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (SupportImage.BundleCycles.closedImageSupport i W) (closedImageRationalFunction i W g) := by
  let e := SupportImage.BundleCycles.closedSupportImageIso i W
  change Finsupp.mapDomain i (Finsupp.embDomain
      ⟨CycleClass.Geometric.GenericPoint.reducedSupportι W, (CycleClass.Geometric.GenericPoint.reducedSupportι W).isClosedEmbedding.injective⟩
      (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) g)) =
    Finsupp.embDomain
      ⟨CycleClass.Geometric.GenericPoint.reducedSupportι (SupportImage.BundleCycles.closedImageSupport i W),
        (CycleClass.Geometric.GenericPoint.reducedSupportι (SupportImage.BundleCycles.closedImageSupport i W)).isClosedEmbedding.injective⟩
      (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (CycleClass.Geometric.GenericPoint.reducedSupportScheme (SupportImage.BundleCycles.closedImageSupport i W))
        ((RationalDivisorRestriction.BundleCycles.openFunctionFieldIso e.hom).inv g))
  rw [Finsupp.embDomain_eq_mapDomain, Finsupp.embDomain_eq_mapDomain, ← Finsupp.mapDomain_comp]
  have hc : i ∘ CycleClass.Geometric.GenericPoint.reducedSupportι W = CycleClass.Geometric.GenericPoint.reducedSupportι (SupportImage.BundleCycles.closedImageSupport i W) ∘ e.hom :=
    funext fun x => (congrArg (fun a => a x) (SupportImage.BundleCycles.closedSupportImageIso_inclusion i W)).symm
  change Finsupp.mapDomain (i ∘ CycleClass.Geometric.GenericPoint.reducedSupportι W) _ = _
  rw [hc, Finsupp.mapDomain_comp, rationalPrincipalDivisor_iso]
  rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.PrincipalPushforward.BundleCycles
end ComponentSource_4

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.PrincipalPushforward"

@[expose] public section ComponentSource_5
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.DimensionChow -/

/-! # Dimension Chow -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.DimensionChow.BundleCycles

noncomputable section

section

/-!
# LineBundleCycles: Chow groups for the nonprojective deformation schemes

These dimension-indexed Chow groups are quotients by the span of genuine
principal divisors on actual integral supports of dimension one larger.
They do not require smoothness, projectivity, or a purity assumption.
Specialization on the quotient requires a separate relation-preservation
proof; it is not included in the definitions.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X : Scheme} [AlgebraicGeometry.IsNoetherian X] (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)

/-- A principal-divisor generator in the actual dimension grading. -/
def IsDimensionPrincipalDivisorQ (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) : Prop :=
  ∃ W : IrreducibleCloseds X, Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f = d + 1 ∧
    ∃ g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField, g ≠ 0 ∧
      z = Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor f d W g

/-- The defining generators have exactly the full principal-divisor coefficients at every point. -/
theorem isDimensionPrincipalDivisorQ_iff [LocallyOfFiniteType f] (d : ℕ)
    (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :
    IsDimensionPrincipalDivisorQ f d z ↔
      ∃ W : IrreducibleCloseds X, Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f = d + 1 ∧
        ∃ g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField, g ≠ 0 ∧
          Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d z = Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g := by
  constructor
  · rintro ⟨W, hW, g, hg, rfl⟩
    exact ⟨W, hW, g, hg, Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor_push f d W hW g⟩
  · rintro ⟨W, hW, g, hg, hz⟩
    refine ⟨W, hW, g, hg, Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion_injective f d ?_⟩
    exact hz.trans (Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor_push f d W hW g).symm

/-- Rational equivalence in dimension d on a general Noetherian scheme. -/
def dimensionRationalEquivalenceQ (d : ℕ) : Submodule ℚ (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :=
  Submodule.span ℚ {z | IsDimensionPrincipalDivisorQ f d z}

/-- The rational Chow group of dimension-d cycles on the actual scheme. -/
def DimensionChowQ (d : ℕ) : ModuleCat ℚ :=
  ModuleCat.of ℚ ((Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) ⧸ dimensionRationalEquivalenceQ f d)

def dimensionCycleToChowQ (d : ℕ) :
    (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) →ₗ[ℚ] DimensionChowQ f d :=
  (dimensionRationalEquivalenceQ f d).mkQ

theorem dimensionCycleToChowQ_surjective (d : ℕ) : Function.Surjective (dimensionCycleToChowQ f d) :=
  (dimensionRationalEquivalenceQ f d).mkQ_surjective

theorem dimensionCycleToChowQ_eq_zero_iff (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :
    dimensionCycleToChowQ f d z = 0 ↔ z ∈ dimensionRationalEquivalenceQ f d :=
  Submodule.Quotient.mk_eq_zero _

/-- Every actual principal divisor of the required dimension vanishes in the quotient. -/
theorem dimensionCycleToChowQ_principal (d : ℕ) (W : IrreducibleCloseds X)
    (hW : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f = d + 1)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0) :
    dimensionCycleToChowQ f d (Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor f d W g) = 0 :=
  (dimensionCycleToChowQ_eq_zero_iff f d _).mpr (Submodule.subset_span ⟨W, hW, g, hg, rfl⟩)

end

/-! # LineBundleCycles: canonical Chow transport along equality of actual structure morphisms -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X : Scheme.{0}} {f g : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}

def dimensionCycleTransport (h : f = g) (d : ℕ) :
    (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) →ₗ[ℚ] (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint g d →₀ ℚ) := by
  subst g
  exact LinearMap.id

theorem dimensionCycleTransport_forget (h : f = g) (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :
    Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion g d (dimensionCycleTransport h d z) = Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d z := by
  subst g
  rfl

variable [AlgebraicGeometry.IsNoetherian X]

def dimensionChowTransport (h : f = g) (d : ℕ) : DimensionChowQ f d →ₗ[ℚ] DimensionChowQ g d := by
  subst g
  exact LinearMap.id

theorem dimensionChowTransport_cycle (h : f = g) (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :
    dimensionChowTransport h d (dimensionCycleToChowQ f d z) =
      dimensionCycleToChowQ g d (dimensionCycleTransport h d z) := by
  subst g
  rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.DimensionChow.BundleCycles
end ComponentSource_5

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.DimensionChow"

@[expose] public section ComponentSource_6
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.ChowPushforward -/

/-! # Chow Pushforward -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.ChowPushforward.BundleCycles

noncomputable section

/-!
# LineBundleCycles: genuine closed-immersion pushforward on rational Chow groups

The actual finite-cycle map sends every principal-divisor generator to
the divisor of the transported function on its actual closed image.
Consequently it preserves the span of rational-equivalence relations
and induces the displayed quotient map.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X Y : Scheme} [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    (i : X ⟶ Y) [IsClosedImmersion i] (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

/-- The full principal divisor is preserved in the correct dimension grade. -/
theorem closedDimensionCyclePushforward_principal (d : ℕ) (W : IrreducibleCloseds X)
    (hW : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W (i ≫ f) = d + 1)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) :
    CyclePushforward.BundleCycles.closedDimensionCyclePushforward i f d (Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor (i ≫ f) d W g) =
      Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor f d (SupportImage.BundleCycles.closedImageSupport i W) (PrincipalPushforward.BundleCycles.closedImageRationalFunction i W g) := by
  apply Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion_injective f d
  rw [CyclePushforward.BundleCycles.closedDimensionCyclePushforward_forget,
    Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor_push (i ≫ f) d W hW,
    PrincipalPushforward.BundleCycles.closedPushforward_principalPointDivisor,
    Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor_push f d (SupportImage.BundleCycles.closedImageSupport i W)
      ((SupportImage.BundleCycles.closedImageSupport_dimension i f W).trans hW)]

/-- A defining rational-equivalence generator maps to a defining generator. -/
theorem closedDimensionCyclePushforward_isPrincipal (d : ℕ)
    (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (i ≫ f) d →₀ ℚ)
    (hz : DimensionChow.BundleCycles.IsDimensionPrincipalDivisorQ (i ≫ f) d z) :
    DimensionChow.BundleCycles.IsDimensionPrincipalDivisorQ f d (CyclePushforward.BundleCycles.closedDimensionCyclePushforward i f d z) := by
  obtain ⟨W, hW, g, hg, rfl⟩ := hz
  exact ⟨SupportImage.BundleCycles.closedImageSupport i W, (SupportImage.BundleCycles.closedImageSupport_dimension i f W).trans hW,
    PrincipalPushforward.BundleCycles.closedImageRationalFunction i W g, PrincipalPushforward.BundleCycles.closedImageRationalFunction_ne_zero i W g hg,
    closedDimensionCyclePushforward_principal i f d W hW g⟩

/-- The complete rational-equivalence submodule is preserved. -/
theorem closedDimensionCyclePushforward_relations (d : ℕ) :
    DimensionChow.BundleCycles.dimensionRationalEquivalenceQ (i ≫ f) d ≤
      (DimensionChow.BundleCycles.dimensionRationalEquivalenceQ f d).comap (CyclePushforward.BundleCycles.closedDimensionCyclePushforward i f d) := by
  apply Submodule.span_le.mpr
  intro z hz
  exact Submodule.subset_span (closedDimensionCyclePushforward_isPrincipal i f d z hz)

/-- Closed pushforward on the genuine dimension-graded Chow quotients. -/
def closedChowPushforward (d : ℕ) : DimensionChow.BundleCycles.DimensionChowQ (i ≫ f) d →ₗ[ℚ] DimensionChow.BundleCycles.DimensionChowQ f d :=
  (DimensionChow.BundleCycles.dimensionRationalEquivalenceQ (i ≫ f) d).mapQ (DimensionChow.BundleCycles.dimensionRationalEquivalenceQ f d)
    (CyclePushforward.BundleCycles.closedDimensionCyclePushforward i f d) (closedDimensionCyclePushforward_relations i f d)

@[simp]
theorem closedChowPushforward_cycle (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (i ≫ f) d →₀ ℚ) :
    closedChowPushforward i f d (DimensionChow.BundleCycles.dimensionCycleToChowQ (i ≫ f) d z) =
      DimensionChow.BundleCycles.dimensionCycleToChowQ f d (CyclePushforward.BundleCycles.closedDimensionCyclePushforward i f d z) := rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.ChowPushforward.BundleCycles
end ComponentSource_6

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.ChowPushforward"

@[expose] public section ComponentSource_7
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Open.SupportRestriction -/

/-! # Support Restriction -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Open.SupportRestriction.BundleCycles

noncomputable section

/-!
# LineBundleCycles: restriction of an actual integral closed support to an open

The scheme-theoretic pullback is an open subscheme of the original
integral support and a closed subscheme of the ambient open. When
nonempty it is integral and isomorphic to the reduced support of the
actual inverse-image closed subset.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable {X Y : Scheme} (i : X ⟶ Y) [IsOpenImmersion i] (W : IrreducibleCloseds Y)

def openSupportPullback : Scheme := pullback i (CycleClass.Geometric.GenericPoint.reducedSupportι W)

def openSupportInclusion : openSupportPullback i W ⟶ X := pullback.fst _ _

def openSupportToOriginal : openSupportPullback i W ⟶ CycleClass.Geometric.GenericPoint.reducedSupportScheme W := pullback.snd _ _

instance openSupportInclusion_isClosedImmersion : IsClosedImmersion (openSupportInclusion i W) :=
  inferInstanceAs (IsClosedImmersion (pullback.fst i (CycleClass.Geometric.GenericPoint.reducedSupportι W)))

instance openSupportToOriginal_isOpenImmersion : IsOpenImmersion (openSupportToOriginal i W) :=
  inferInstanceAs (IsOpenImmersion (pullback.snd i (CycleClass.Geometric.GenericPoint.reducedSupportι W)))

omit [IsOpenImmersion i] in
theorem openSupportInclusion_range : Set.range (openSupportInclusion i W) = i ⁻¹' (W : Set Y) := by
  have h := Scheme.image_preimage_eq_of_isPullback (IsPullback.of_hasPullback i (CycleClass.Geometric.GenericPoint.reducedSupportι W)).flip Set.univ
  simp only [Set.preimage_univ, Set.image_univ, CycleClass.Geometric.GenericPoint.range_reducedSupportι] at h
  exact h

omit [IsOpenImmersion i] in
theorem openSupportPullback_nonempty_iff : Nonempty (openSupportPullback i W) ↔ (i ⁻¹' (W : Set Y)).Nonempty := by
  rw [← openSupportInclusion_range]
  exact Set.range_nonempty_iff_nonempty.symm

variable [Nonempty (openSupportPullback i W)]

instance openSupportPullback_isIntegral : IsIntegral (openSupportPullback i W) :=
  isIntegral_of_isOpenImmersion (openSupportToOriginal i W)

def openRestrictedSupport : IrreducibleCloseds X := CycleClass.Geometric.StratumClosure.integralImageClosure (openSupportInclusion i W)

theorem openRestrictedSupport_coe : (openRestrictedSupport i W : Set X) = i ⁻¹' (W : Set Y) :=
  (openSupportInclusion i W).isClosedEmbedding.isClosed_range.closure_eq.trans (openSupportInclusion_range i W)

def openSupportIso : openSupportPullback i W ≅ CycleClass.Geometric.GenericPoint.reducedSupportScheme (openRestrictedSupport i W) := by
  have he : IsIso (CycleClass.Geometric.StratumClosure.toReducedImageClosure (openSupportInclusion i W)) := by
    change IsIso ((openSupportInclusion i W).toImage ≫ (CycleClass.Geometric.StratumClosure.reducedImageClosureIso (openSupportInclusion i W)).hom)
    infer_instance
  exact @asIso _ _ _ _ (CycleClass.Geometric.StratumClosure.toReducedImageClosure (openSupportInclusion i W)) he

theorem openSupportIso_inclusion :
    (openSupportIso i W).hom ≫ CycleClass.Geometric.GenericPoint.reducedSupportι (openRestrictedSupport i W) = openSupportInclusion i W :=
  CycleClass.Geometric.StratumClosure.toReducedImageClosure_inclusion (openSupportInclusion i W)

def openRestrictedSupportMap : CycleClass.Geometric.GenericPoint.reducedSupportScheme (openRestrictedSupport i W) ⟶ CycleClass.Geometric.GenericPoint.reducedSupportScheme W :=
  (openSupportIso i W).inv ≫ openSupportToOriginal i W

instance openRestrictedSupportMap_isOpenImmersion : IsOpenImmersion (openRestrictedSupportMap i W) := by
  change IsOpenImmersion ((openSupportIso i W).inv ≫ openSupportToOriginal i W)
  infer_instance

theorem openRestrictedSupportMap_inclusion :
    openRestrictedSupportMap i W ≫ CycleClass.Geometric.GenericPoint.reducedSupportι W = CycleClass.Geometric.GenericPoint.reducedSupportι (openRestrictedSupport i W) ≫ i := by
  have hp : openSupportInclusion i W ≫ i = openSupportToOriginal i W ≫ CycleClass.Geometric.GenericPoint.reducedSupportι W := pullback.condition
  have he : (openSupportIso i W).inv ≫ openSupportInclusion i W = CycleClass.Geometric.GenericPoint.reducedSupportι (openRestrictedSupport i W) :=
    (congrArg (fun g => (openSupportIso i W).inv ≫ g) (openSupportIso_inclusion i W).symm).trans
      (Iso.inv_hom_id_assoc _ _)
  change ((openSupportIso i W).inv ≫ openSupportToOriginal i W) ≫ CycleClass.Geometric.GenericPoint.reducedSupportι W = _
  exact (Category.assoc _ _ _).trans ((congrArg (fun g => (openSupportIso i W).inv ≫ g) hp.symm).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (fun g => g ≫ i) he)))

theorem openRestrictedSupport_dimension (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (openRestrictedSupport i W) (i ≫ f) = Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f := by
  have h := Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion (openRestrictedSupportMap i W) (CycleClass.Geometric.SupportFiniteType.supportStructureMap W f)
  have he : openRestrictedSupportMap i W ≫ CycleClass.Geometric.SupportFiniteType.supportStructureMap W f =
      CycleClass.Geometric.SupportFiniteType.supportStructureMap (openRestrictedSupport i W) (i ≫ f) := by
    change openRestrictedSupportMap i W ≫ (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ f) =
      CycleClass.Geometric.GenericPoint.reducedSupportι (openRestrictedSupport i W) ≫ (i ≫ f)
    rw [← Category.assoc, openRestrictedSupportMap_inclusion, Category.assoc]
  exact (congrArg (fun g => Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension g) he.symm).trans h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Open.SupportRestriction.BundleCycles
end ComponentSource_7

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Open.SupportRestriction"

@[expose] public section ComponentSource_8
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Open.PrincipalRestriction -/

/-! # Principal Restriction -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Open.PrincipalRestriction.BundleCycles

noncomputable section

section

/-!
# LineBundleCycles: complete principal-divisor restriction to an open

On a nonempty restricted integral support the actual function-field map
preserves all local orders. When the open misses the support, every
coefficient vanishes. These comparisons include all ambient points.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X Y : Scheme} [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]

theorem schemePrincipalPointDivisor_off_support (W : IrreducibleCloseds X)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (x : X) (hx : x ∉ (W : Set X)) :
    Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g x = 0 := by
  have hr : x ∉ Set.range (CycleClass.Geometric.GenericPoint.reducedSupportι W) := by
    rw [CycleClass.Geometric.GenericPoint.range_reducedSupportι]
    exact hx
  exact Finsupp.embDomain_of_notMem_range _ _ _ hr

variable (i : X ⟶ Y) [IsOpenImmersion i] (W : IrreducibleCloseds Y)

def openRestrictedRationalFunction [Nonempty (SupportRestriction.BundleCycles.openSupportPullback i W)]
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) :
    (CycleClass.Geometric.GenericPoint.reducedSupportScheme (SupportRestriction.BundleCycles.openRestrictedSupport i W)).functionField :=
  RationalDivisorRestriction.BundleCycles.openFunctionFieldMap (SupportRestriction.BundleCycles.openRestrictedSupportMap i W) g

omit [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y] in
theorem openRestrictedRationalFunction_ne_zero [Nonempty (SupportRestriction.BundleCycles.openSupportPullback i W)]
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0) :
    openRestrictedRationalFunction i W g ≠ 0 :=
  (map_ne_zero_iff _ (RationalDivisorRestriction.BundleCycles.openFunctionFieldMap (SupportRestriction.BundleCycles.openRestrictedSupportMap i W)).hom.injective).mpr hg

/-- Restriction to a nonempty support is its genuine complete principal divisor. -/
theorem openRestriction_principalPointDivisor [Nonempty (SupportRestriction.BundleCycles.openSupportPullback i W)]
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) :
    Finsupp.comapDomain i (Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g) i.isOpenEmbedding.injective.injOn =
      Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (SupportRestriction.BundleCycles.openRestrictedSupport i W) (openRestrictedRationalFunction i W g) := by
  ext x
  by_cases hx : x ∈ (SupportRestriction.BundleCycles.openRestrictedSupport i W : Set X)
  · have hr : x ∈ Set.range (CycleClass.Geometric.GenericPoint.reducedSupportι (SupportRestriction.BundleCycles.openRestrictedSupport i W)) := by
      rw [CycleClass.Geometric.GenericPoint.range_reducedSupportι]
      exact hx
    obtain ⟨y, rfl⟩ := hr
    have hp : CycleClass.Geometric.GenericPoint.reducedSupportι W (SupportRestriction.BundleCycles.openRestrictedSupportMap i W y) =
        i (CycleClass.Geometric.GenericPoint.reducedSupportι (SupportRestriction.BundleCycles.openRestrictedSupport i W) y) :=
      congrArg (fun j => j y) (SupportRestriction.BundleCycles.openRestrictedSupportMap_inclusion i W)
    change Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g (i (CycleClass.Geometric.GenericPoint.reducedSupportι (SupportRestriction.BundleCycles.openRestrictedSupport i W) y)) =
      Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (SupportRestriction.BundleCycles.openRestrictedSupport i W)
        (openRestrictedRationalFunction i W g) (CycleClass.Geometric.GenericPoint.reducedSupportι (SupportRestriction.BundleCycles.openRestrictedSupport i W) y)
    rw [← hp, Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor_at_support, Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor_at_support]
    exact congrArg (fun n : ℤ => (n : ℚ))
      (RationalDivisorRestriction.BundleCycles.ord_openImmersion (SupportRestriction.BundleCycles.openRestrictedSupportMap i W) g y).symm
  · have hi : i x ∉ (W : Set Y) := fun h => hx
      ((congrArg (fun s : Set X => x ∈ s) (SupportRestriction.BundleCycles.openRestrictedSupport_coe i W)).mpr h)
    exact (schemePrincipalPointDivisor_off_support W g (i x) hi).trans
      (schemePrincipalPointDivisor_off_support (SupportRestriction.BundleCycles.openRestrictedSupport i W)
        (openRestrictedRationalFunction i W g) x hx).symm

omit [AlgebraicGeometry.IsNoetherian X] in
/-- If the open misses the support, its entire principal divisor restricts to zero. -/
theorem openRestriction_principalPointDivisor_empty [IsEmpty (SupportRestriction.BundleCycles.openSupportPullback i W)]
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) :
    Finsupp.comapDomain i (Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g) i.isOpenEmbedding.injective.injOn = 0 := by
  ext x
  apply schemePrincipalPointDivisor_off_support W g (i x)
  intro hx
  have hn := (SupportRestriction.BundleCycles.openSupportPullback_nonempty_iff i W).mpr ⟨x, hx⟩
  exact isEmptyElim (Classical.choice hn)

end

/-!
# LineBundleCycles: lifting open supports and rational functions to their closures

A reduced integral closed support in an open subscheme is open in its
actual reduced closure in the ambient scheme. Its function field is
therefore canonically unchanged. This supplies concrete ambient
principal divisors lifting the relations on the open.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X Y : Scheme} [AlgebraicGeometry.IsNoetherian X]
    (i : X ⟶ Y) [IsOpenImmersion i] (W : IrreducibleCloseds X)

def openClosureSupport : IrreducibleCloseds Y := CycleClass.Geometric.StratumClosure.integralImageClosure (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ i)

omit [AlgebraicGeometry.IsNoetherian X] [IsOpenImmersion i] in
theorem openClosureSupport_coe : (openClosureSupport i W : Set Y) = closure (i '' (W : Set X)) := by
  change closure (Set.range (i ∘ CycleClass.Geometric.GenericPoint.reducedSupportι W)) = _
  rw [Set.range_comp, CycleClass.Geometric.GenericPoint.range_reducedSupportι]

omit [AlgebraicGeometry.IsNoetherian X] in
theorem openClosureSupport_preimage : i ⁻¹' (openClosureSupport i W : Set Y) = (W : Set X) := by
  rw [openClosureSupport_coe,
    i.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage i.continuous,
    Set.preimage_image_eq _ i.isOpenEmbedding.injective, W.isClosed.closure_eq]

/-- The original support as the actual open subscheme of its reduced closure. -/
def openSupportClosureMap : CycleClass.Geometric.GenericPoint.reducedSupportScheme W ⟶ CycleClass.Geometric.GenericPoint.reducedSupportScheme (openClosureSupport i W) :=
  CycleClass.Geometric.StratumClosure.toReducedImageClosure (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ i)

instance openSupportClosureMap_isOpenImmersion : IsOpenImmersion (openSupportClosureMap i W) :=
  inferInstanceAs (IsOpenImmersion (CycleClass.Geometric.StratumClosure.toReducedImageClosure (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ i)))

omit [IsOpenImmersion i] in
theorem openSupportClosureMap_inclusion :
    openSupportClosureMap i W ≫ CycleClass.Geometric.GenericPoint.reducedSupportι (openClosureSupport i W) = CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ i :=
  CycleClass.Geometric.StratumClosure.toReducedImageClosure_inclusion (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ i)

theorem openClosureSupport_dimension (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (openClosureSupport i W) f = Foundations.Scheme.SupportDimension.supportTranscendenceDimension W (i ≫ f) := by
  have h := CycleClass.Geometric.StratumClosure.schemeTranscendenceDimension_eq_imageClosure (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ i) f
  exact h.symm.trans (congrArg (fun g => Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension g) (Category.assoc _ _ _))

/-- Extend the rational function through the actual generic-stalk isomorphism. -/
def openClosureRationalFunction (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) :
    (CycleClass.Geometric.GenericPoint.reducedSupportScheme (openClosureSupport i W)).functionField :=
  (RationalDivisorRestriction.BundleCycles.openFunctionFieldIso (openSupportClosureMap i W)).inv g

theorem openClosureRationalFunction_ne_zero (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0) :
    openClosureRationalFunction i W g ≠ 0 :=
  (map_ne_zero_iff _ (RationalDivisorRestriction.BundleCycles.openFunctionFieldIso (openSupportClosureMap i W)).inv.hom.injective).mpr hg

variable [AlgebraicGeometry.IsNoetherian Y]

/-- The complete ambient principal divisor restricts to the original one. -/
theorem openClosure_principalPointDivisor (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) :
    Finsupp.comapDomain i
        (Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (openClosureSupport i W) (openClosureRationalFunction i W g))
        i.isOpenEmbedding.injective.injOn = Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g := by
  ext x
  by_cases hx : x ∈ (W : Set X)
  · have hr : x ∈ Set.range (CycleClass.Geometric.GenericPoint.reducedSupportι W) := by
      rw [CycleClass.Geometric.GenericPoint.range_reducedSupportι]
      exact hx
    obtain ⟨y, rfl⟩ := hr
    have hp : CycleClass.Geometric.GenericPoint.reducedSupportι (openClosureSupport i W) (openSupportClosureMap i W y) =
        i (CycleClass.Geometric.GenericPoint.reducedSupportι W y) := congrArg (fun j => j y) (openSupportClosureMap_inclusion i W)
    change Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (openClosureSupport i W) (openClosureRationalFunction i W g)
      (i (CycleClass.Geometric.GenericPoint.reducedSupportι W y)) = Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g (CycleClass.Geometric.GenericPoint.reducedSupportι W y)
    rw [← hp, Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor_at_support, Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor_at_support]
    have he : RationalDivisorRestriction.BundleCycles.openFunctionFieldMap (openSupportClosureMap i W) (openClosureRationalFunction i W g) = g :=
      Iso.inv_hom_id_apply (RationalDivisorRestriction.BundleCycles.openFunctionFieldIso (openSupportClosureMap i W)) g
    exact congrArg (fun n : ℤ => (n : ℚ))
      ((RationalDivisorRestriction.BundleCycles.ord_openImmersion (openSupportClosureMap i W) (openClosureRationalFunction i W g) y).symm.trans
        (congrArg (fun a => (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).ord a y) he))
  · have hi : i x ∉ (openClosureSupport i W : Set Y) :=
      fun h => hx ((congrArg (fun s : Set X => x ∈ s) (openClosureSupport_preimage i W)).mp h)
    exact (schemePrincipalPointDivisor_off_support (openClosureSupport i W)
      (openClosureRationalFunction i W g) (i x) hi).trans (schemePrincipalPointDivisor_off_support W g x hx).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Open.PrincipalRestriction.BundleCycles
end ComponentSource_8

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Open.PrincipalRestriction"

@[expose] public section ComponentSource_9
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ChowRestriction -/

/-! # Chow Restriction -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ChowRestriction.BundleCycles

noncomputable section

/-!
# LineBundleCycles: genuine surjective restriction on rational Chow groups

Restriction sends each principal divisor to the actual principal divisor
on its nonempty restricted support, or to zero when the support is
disjoint from the open. It therefore descends to the actual quotients.
Closing the finitely many generic points of a cycle proves surjectivity.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X Y : Scheme} [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    (i : X ⟶ Y) [IsOpenImmersion i] (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

theorem openDimensionCycleRestriction_principal (d : ℕ) (W : IrreducibleCloseds Y)
    [Nonempty (SupportRestriction.BundleCycles.openSupportPullback i W)] (hW : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f = d + 1)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) :
    CycleRestriction.BundleCycles.openDimensionCycleRestriction i f d (Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor f d W g) =
      Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor (i ≫ f) d (SupportRestriction.BundleCycles.openRestrictedSupport i W)
        (PrincipalRestriction.BundleCycles.openRestrictedRationalFunction i W g) := by
  apply Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion_injective (i ≫ f) d
  rw [CycleRestriction.BundleCycles.openDimensionCycleRestriction_forget, Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor_push f d W hW,
    PrincipalRestriction.BundleCycles.openRestriction_principalPointDivisor,
    Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor_push (i ≫ f) d (SupportRestriction.BundleCycles.openRestrictedSupport i W)
      ((SupportRestriction.BundleCycles.openRestrictedSupport_dimension i W f).trans hW)]

theorem openDimensionCycleRestriction_principal_empty (d : ℕ) (W : IrreducibleCloseds Y)
    [IsEmpty (SupportRestriction.BundleCycles.openSupportPullback i W)] (hW : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f = d + 1)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) :
    CycleRestriction.BundleCycles.openDimensionCycleRestriction i f d (Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor f d W g) = 0 := by
  apply Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion_injective (i ≫ f) d
  rw [CycleRestriction.BundleCycles.openDimensionCycleRestriction_forget, Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor_push f d W hW,
    PrincipalRestriction.BundleCycles.openRestriction_principalPointDivisor_empty, map_zero]

/-- The relation-preservation proof uses the actual nonempty or empty support pullback. -/
theorem openDimensionCycleRestriction_relations (d : ℕ) :
    DimensionChow.BundleCycles.dimensionRationalEquivalenceQ f d ≤
      (DimensionChow.BundleCycles.dimensionRationalEquivalenceQ (i ≫ f) d).comap (CycleRestriction.BundleCycles.openDimensionCycleRestriction i f d) := by
  apply Submodule.span_le.mpr
  rintro z ⟨W, hW, g, hg, rfl⟩
  change CycleRestriction.BundleCycles.openDimensionCycleRestriction i f d (Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor f d W g) ∈
    DimensionChow.BundleCycles.dimensionRationalEquivalenceQ (i ≫ f) d
  cases isEmpty_or_nonempty (SupportRestriction.BundleCycles.openSupportPullback i W) with
  | inl h =>
    let := h
    rw [openDimensionCycleRestriction_principal_empty i f d W hW g]
    exact Submodule.zero_mem _
  | inr h =>
    let := h
    exact Submodule.subset_span ⟨SupportRestriction.BundleCycles.openRestrictedSupport i W,
      (SupportRestriction.BundleCycles.openRestrictedSupport_dimension i W f).trans hW, PrincipalRestriction.BundleCycles.openRestrictedRationalFunction i W g,
      PrincipalRestriction.BundleCycles.openRestrictedRationalFunction_ne_zero i W g hg,
      openDimensionCycleRestriction_principal i f d W hW g⟩

/-- Restriction to an open subscheme on the genuine dimension-graded Chow groups. -/
def openChowRestriction (d : ℕ) : DimensionChow.BundleCycles.DimensionChowQ f d →ₗ[ℚ] DimensionChow.BundleCycles.DimensionChowQ (i ≫ f) d :=
  (DimensionChow.BundleCycles.dimensionRationalEquivalenceQ f d).mapQ (DimensionChow.BundleCycles.dimensionRationalEquivalenceQ (i ≫ f) d)
    (CycleRestriction.BundleCycles.openDimensionCycleRestriction i f d) (openDimensionCycleRestriction_relations i f d)

@[simp]
theorem openChowRestriction_cycle (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :
    openChowRestriction i f d (DimensionChow.BundleCycles.dimensionCycleToChowQ f d z) =
      DimensionChow.BundleCycles.dimensionCycleToChowQ (i ≫ f) d (CycleRestriction.BundleCycles.openDimensionCycleRestriction i f d z) := rfl

/-- Every Chow class on the open comes from closing its finitely many cycle supports. -/
theorem openChowRestriction_surjective (d : ℕ) : Function.Surjective (openChowRestriction i f d) := by
  intro a
  obtain ⟨z, rfl⟩ := DimensionChow.BundleCycles.dimensionCycleToChowQ_surjective (i ≫ f) d a
  refine ⟨DimensionChow.BundleCycles.dimensionCycleToChowQ f d (CycleRestriction.BundleCycles.openDimensionCycleExtension i f d z), ?_⟩
  rw [openChowRestriction_cycle, CycleRestriction.BundleCycles.openDimensionCycleRestriction_extension]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ChowRestriction.BundleCycles
end ComponentSource_9

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ChowRestriction"

@[expose] public section ComponentSource_10
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Open.RelationLifting -/

/-! # Relation Lifting -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Open.RelationLifting.BundleCycles

noncomputable section

/-!
# LineBundleCycles: lifting every rational-equivalence relation from an open

Each principal relation on the open lifts by closing its actual integral
support and extending its function through the generic-stalk isomorphism.
Linear extension lifts the entire relation submodule. A Chow class
vanishing on the open consequently has a cycle representative whose
restriction is exactly zero.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X Y : Scheme} [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    (i : X ⟶ Y) [IsOpenImmersion i] (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

theorem openClosure_gradedPrincipal (d : ℕ) (W : IrreducibleCloseds X)
    (hW : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W (i ≫ f) = d + 1)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) :
    CycleRestriction.BundleCycles.openDimensionCycleRestriction i f d
      (Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor f d (PrincipalRestriction.BundleCycles.openClosureSupport i W) (PrincipalRestriction.BundleCycles.openClosureRationalFunction i W g)) =
      Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor (i ≫ f) d W g := by
  apply Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion_injective (i ≫ f) d
  rw [CycleRestriction.BundleCycles.openDimensionCycleRestriction_forget,
    Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor_push f d (PrincipalRestriction.BundleCycles.openClosureSupport i W)
      ((PrincipalRestriction.BundleCycles.openClosureSupport_dimension i W f).trans hW),
    PrincipalRestriction.BundleCycles.openClosure_principalPointDivisor, Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor_push (i ≫ f) d W hW]

/-- Every relation on the open is the restriction of an actual ambient relation. -/
theorem openDimensionCycleRestriction_relations_lift (d : ℕ) :
    DimensionChow.BundleCycles.dimensionRationalEquivalenceQ (i ≫ f) d ≤
      (DimensionChow.BundleCycles.dimensionRationalEquivalenceQ f d).map (CycleRestriction.BundleCycles.openDimensionCycleRestriction i f d) := by
  apply Submodule.span_le.mpr
  rintro z ⟨W, hW, g, hg, rfl⟩
  refine Submodule.mem_map.mpr ⟨Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor f d (PrincipalRestriction.BundleCycles.openClosureSupport i W)
    (PrincipalRestriction.BundleCycles.openClosureRationalFunction i W g), ?_, openClosure_gradedPrincipal i f d W hW g⟩
  exact Submodule.subset_span ⟨PrincipalRestriction.BundleCycles.openClosureSupport i W, (PrincipalRestriction.BundleCycles.openClosureSupport_dimension i W f).trans hW,
    PrincipalRestriction.BundleCycles.openClosureRationalFunction i W g, PrincipalRestriction.BundleCycles.openClosureRationalFunction_ne_zero i W g hg, rfl⟩

theorem openDimensionCycleRestriction_relations_image (d : ℕ) :
    (DimensionChow.BundleCycles.dimensionRationalEquivalenceQ f d).map (CycleRestriction.BundleCycles.openDimensionCycleRestriction i f d) =
      DimensionChow.BundleCycles.dimensionRationalEquivalenceQ (i ≫ f) d :=
  (Submodule.map_le_iff_le_comap.mpr (ChowRestriction.BundleCycles.openDimensionCycleRestriction_relations i f d)).antisymm
    (openDimensionCycleRestriction_relations_lift i f d)

/-- A class vanishing on the open has a finite cycle representative supported outside it. -/
theorem openChowRestriction_exists_zero_restriction (d : ℕ) (a : DimensionChow.BundleCycles.DimensionChowQ f d)
    (ha : ChowRestriction.BundleCycles.openChowRestriction i f d a = 0) :
    ∃ z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ,
      DimensionChow.BundleCycles.dimensionCycleToChowQ f d z = a ∧ CycleRestriction.BundleCycles.openDimensionCycleRestriction i f d z = 0 := by
  obtain ⟨z, rfl⟩ := DimensionChow.BundleCycles.dimensionCycleToChowQ_surjective f d a
  have hz : CycleRestriction.BundleCycles.openDimensionCycleRestriction i f d z ∈ DimensionChow.BundleCycles.dimensionRationalEquivalenceQ (i ≫ f) d :=
    (DimensionChow.BundleCycles.dimensionCycleToChowQ_eq_zero_iff (i ≫ f) d _).mp ha
  obtain ⟨v, hv, hres⟩ := Submodule.mem_map.mp (openDimensionCycleRestriction_relations_lift i f d hz)
  refine ⟨z - v, ?_, ?_⟩
  · rw [map_sub, (DimensionChow.BundleCycles.dimensionCycleToChowQ_eq_zero_iff f d v).mpr hv, sub_zero]
  · rw [map_sub, hres, sub_self]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Open.RelationLifting.BundleCycles
end ComponentSource_10

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Open.RelationLifting"

@[expose] public section ComponentSource_11
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.ChowLocalization -/

/-! # Chow Localization -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.ChowLocalization.BundleCycles

noncomputable section

/-!
# LineBundleCycles: exact localization for the genuine rational Chow quotients

For a closed complement and its actual open inclusion, closed pushforward
has image precisely the kernel of open restriction. The proof lifts the
open rational-equivalence relation, subtracts that ambient relation, and
then lifts the complete remaining cycle to the closed complement.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {U X Z : Scheme} [AlgebraicGeometry.IsNoetherian U]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Z]
    (i : U ⟶ X) [IsOpenImmersion i] (j : Z ⟶ X) [IsClosedImmersion j]
    (hcomp : Set.range j = (Set.range i)ᶜ) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

include hcomp

theorem openChowRestriction_closed (d : ℕ) (a : DimensionChow.BundleCycles.DimensionChowQ (j ≫ f) d) :
    Open.ChowRestriction.BundleCycles.openChowRestriction i f d (Closed.ChowPushforward.BundleCycles.closedChowPushforward j f d a) = 0 := by
  obtain ⟨z, rfl⟩ := DimensionChow.BundleCycles.dimensionCycleToChowQ_surjective (j ≫ f) d a
  rw [Closed.ChowPushforward.BundleCycles.closedChowPushforward_cycle, Open.ChowRestriction.BundleCycles.openChowRestriction_cycle,
    CycleLocalization.BundleCycles.openDimensionCycleRestriction_closed i j hcomp f d, map_zero]

/-- Exactness at the Chow group of the ambient scheme. -/
theorem openChowRestriction_eq_zero_iff (d : ℕ) (a : DimensionChow.BundleCycles.DimensionChowQ f d) :
    Open.ChowRestriction.BundleCycles.openChowRestriction i f d a = 0 ↔ a ∈ LinearMap.range (Closed.ChowPushforward.BundleCycles.closedChowPushforward j f d) := by
  constructor
  · intro ha
    obtain ⟨z, hza, hz⟩ := Open.RelationLifting.BundleCycles.openChowRestriction_exists_zero_restriction i f d a ha
    obtain ⟨w, hw⟩ := CycleLocalization.BundleCycles.exists_closedDimensionCycle_of_zero_restriction i j hcomp f d z hz
    refine ⟨DimensionChow.BundleCycles.dimensionCycleToChowQ (j ≫ f) d w, ?_⟩
    rw [Closed.ChowPushforward.BundleCycles.closedChowPushforward_cycle, hw, hza]
  · rintro ⟨b, rfl⟩
    exact openChowRestriction_closed i j hcomp f d b

/-- The actual closed/open Chow localization sequence is exact. -/
theorem chowLocalization_exact (d : ℕ) :
    LinearMap.range (Closed.ChowPushforward.BundleCycles.closedChowPushforward j f d) = LinearMap.ker (Open.ChowRestriction.BundleCycles.openChowRestriction i f d) := by
  ext a
  exact (openChowRestriction_eq_zero_iff i j hcomp f d a).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.ChowLocalization.BundleCycles
end ComponentSource_11

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.ChowLocalization"

@[expose] public section ComponentSource_12
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.PrimeExtension -/

/-! # Prime Extension -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.PrimeExtension.BundleCycles

noncomputable section

/-!
# LineBundleCycles: vertical divisor primes in a polynomial extension

Extending a prime to the polynomial ring preserves its height. A
height-one prime meeting the base nontrivially is exactly that extension.
-/

open _root_.Polynomial

variable {R : Type*} [CommRing R]

theorem polynomialPrimeExtension_comap (p : Ideal R) :
    Ideal.comap (C : R →+* R[X]) (p.map C) = p := by
  ext a
  constructor
  · intro ha
    simpa only [coeff_C_zero] using (Ideal.mem_map_C_iff.mp ha) 0
  · intro ha
    exact Ideal.mem_map_of_mem C ha

theorem polynomialPrimeExtension_height [IsNoetherianRing R] (p : Ideal R) [p.IsPrime] :
    (p.map (C : R →+* R[X])).height = p.height := by
  let : (p.map (C : R →+* R[X])).LiesOver p := ⟨(polynomialPrimeExtension_comap p).symm⟩
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p (p.map (C : R →+* R[X]))
  change (p.map C).height = p.height + ((p.map C).map (Ideal.Quotient.mk (p.map C))).height at h
  simpa only [Ideal.map_quotient_self, Ideal.height_bot, add_zero] using h

theorem polynomialHeightOne_isExtended [IsNoetherianRing R] [IsDomain R]
    (P : Ideal R[X]) [P.IsPrime] (hP : P.height = 1)
    (hp : Ideal.comap (C : R →+* R[X]) P ≠ ⊥) :
    (Ideal.comap (C : R →+* R[X]) P).map C = P := by
  let p := Ideal.comap (C : R →+* R[X]) P
  have hle : p.map C ≤ P := Ideal.map_comap_le
  have hpheight : 1 ≤ p.height :=
    Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hp)
  apply Ideal.eq_of_le_of_height_le (p.map C) hle
  rw [polynomialPrimeExtension_height, hP]
  exact hpheight

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.PrimeExtension.BundleCycles
end ComponentSource_12

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.PrimeExtension"

@[expose] public section ComponentSource_13
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.GenericFieldComposition -/

/-! # Generic Field Composition -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.GenericFieldComposition.BundleCycles

noncomputable section

/-!
# LineBundleCycles: functoriality of actual generic-stalk maps

These identities follow from stalk specialization and actual germ maps.
They compare the geometric normalization maps with their local algebra.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u
variable {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]

omit [IsIntegral Z] in
theorem genericFieldMap_congr {i j : X ⟶ Y} (hij : i = j)
    (hi : i (genericPoint X) = genericPoint Y) (hj : j (genericPoint X) = genericPoint Y) :
    Cycles.Functoriality.FunctionFields.Construction.genericFieldMap i hi = Cycles.Functoriality.FunctionFields.Construction.genericFieldMap j hj := by
  subst j
  rfl

theorem genericFieldMap_comp (i : X ⟶ Y) (j : Y ⟶ Z)
    (hi : i (genericPoint X) = genericPoint Y) (hj : j (genericPoint Y) = genericPoint Z) :
    Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (i ≫ j) ((congrArg j hi).trans hj) =
      Cycles.Functoriality.FunctionFields.Construction.genericFieldMap j hj ≫ Cycles.Functoriality.FunctionFields.Construction.genericFieldMap i hi := by
  simp only [Cycles.Functoriality.FunctionFields.Construction.genericFieldMap, TopCat.Presheaf.stalkCongr_hom,
    Scheme.Hom.stalkMap_comp, Category.assoc]
  rw [← j.stalkSpecializes_stalkMap_assoc (i (genericPoint X)) (genericPoint Y)
    (Inseparable.of_eq hi).specializes]
  have hc := Z.presheaf.stalkSpecializes_comp
    ((Inseparable.of_eq hi).specializes.map j.continuous) (Inseparable.of_eq hj).specializes
  exact congrArg (fun k : Z.presheaf.stalk (genericPoint Z) ⟶
    Z.presheaf.stalk (j (i (genericPoint X))) =>
      k ≫ j.stalkMap (i (genericPoint X)) ≫ i.stalkMap (genericPoint X)) hc.symm

omit [IsIntegral Z] in
theorem genericFieldMap_germ_appLE (i : X ⟶ Y)
    (hi : i (genericPoint X) = genericPoint Y)
    (U : Y.Opens) (V : X.Opens) [Nonempty U] [Nonempty V] (hV : V ≤ i ⁻¹ᵁ U) :
    Y.germToFunctionField U ≫ Cycles.Functoriality.FunctionFields.Construction.genericFieldMap i hi =
      i.appLE U V hV ≫ X.germToFunctionField V := by
  let : Nonempty (i ⁻¹ᵁ U) := by
    obtain ⟨v⟩ := ‹Nonempty V›
    exact ⟨⟨v.val, hV v.property⟩⟩
  rw [Deformation.FunctionField.BundleCycles.genericFieldMap_germOn, Scheme.Hom.appLE, Category.assoc]
  congr 1
  exact (X.presheaf.germ_res (homOfLE hV) (genericPoint X)
    (((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr
      (by simpa using (show Nonempty V from inferInstance)))).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.GenericFieldComposition.BundleCycles
end ComponentSource_13

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.GenericFieldComposition"

@[expose] public section ComponentSource_14
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.Projection -/

/-! # Projection -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.Projection.BundleCycles

noncomputable section

/-! # LineBundleCycles: the actual affine-line projection and its extended prime points -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.Polynomial

variable (R : Type) [CommRing R]

def polynomialProjection : Spec (.of R[X]) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R R[X]))

instance polynomialProjection_flat : Flat (polynomialProjection R) :=
  Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr Module.Flat.of_free)

def polynomialPrimePoint (p : Spec (.of R)) : Spec (.of R[X]) :=
  ⟨p.asIdeal.map C, by
    let : p.asIdeal.IsPrime := (show PrimeSpectrum R from p).isPrime
    infer_instance⟩

theorem polynomialPrimePoint_projection (p : Spec (.of R)) :
    polynomialProjection R (polynomialPrimePoint R p) = p :=
  PrimeSpectrum.ext (PrimeExtension.BundleCycles.polynomialPrimeExtension_comap p.asIdeal)

theorem polynomialPrimePoint_injective : Function.Injective (polynomialPrimePoint R) :=
  Function.LeftInverse.injective (polynomialPrimePoint_projection R)

theorem polynomialPrimePoint_coheight [IsNoetherianRing R] (p : Spec (.of R)) :
    Order.coheight (polynomialPrimePoint R p) = Order.coheight p := by
  let : p.asIdeal.IsPrime := (show PrimeSpectrum R from p).isPrime
  rw [← idealHeight_eq_coheight, ← idealHeight_eq_coheight]
  exact PrimeExtension.BundleCycles.polynomialPrimeExtension_height p.asIdeal

theorem polynomialPrimePoint_specializes (P : Spec (.of R[X])) :
    polynomialPrimePoint R (polynomialProjection R P) ⤳ P := by
  apply (PrimeSpectrum.le_iff_specializes _ _).mp
  exact Ideal.map_comap_le

variable [IsDomain R]

theorem polynomialProjection_genericPoint :
    polynomialProjection R (genericPoint (Spec (.of R[X]))) = genericPoint (Spec (.of R)) := by
  rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
  apply PrimeSpectrum.ext
  exact (RingHom.injective_iff_ker_eq_bot (algebraMap R R[X])).mp C_injective

def polynomialFunctionFieldMap : (Spec (.of R)).functionField ⟶ (Spec (.of R[X])).functionField :=
  Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (polynomialProjection R) (polynomialProjection_genericPoint R)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.Projection.BundleCycles
end ComponentSource_14

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.Projection"

@[expose] public section ComponentSource_15
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberGenericPoint -/

/-! # Fiber Generic Point -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberGenericPoint.BundleCycles

noncomputable section

/-! # LineBundleCycles: actual fiber generic points for morphisms with geometrically integral fibers -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X Y : Scheme.{0}} (f : X ⟶ Y) [GeometricallyIntegral f]

def integralFiberGenericPoint (y : Y) : X :=
  f.fiberι y (genericPoint (f.fiber y))

theorem integralFiberGenericPoint_projection (y : Y) : f (integralFiberGenericPoint f y) = y :=
  (f.range_fiberι y).le ⟨genericPoint (f.fiber y), rfl⟩

theorem integralFiberGenericPoint_specializes (y : Y) (x : X) (hx : f x = y) :
    integralFiberGenericPoint f y ⤳ x := by
  obtain ⟨z, rfl⟩ := (f.range_fiberι y).ge hx
  exact (genericPoint_specializes z).map (f.fiberι y).continuous

theorem integralFiberGenericPoint_injective : Function.Injective (integralFiberGenericPoint f) :=
  Function.LeftInverse.injective (integralFiberGenericPoint_projection f)

theorem integralFiberGenericPoint_unique (y : Y) (x : X) (hx : f x = y)
    (hgeneric : ∀ z, f z = y → x ⤳ z) : x = integralFiberGenericPoint f y :=
  ((hgeneric _ (integralFiberGenericPoint_projection f y)).antisymm
    (integralFiberGenericPoint_specializes f y x hx)).eq

def integralFiberCycleExtension : (Y →₀ ℚ) →ₗ[ℚ] (X →₀ ℚ) :=
  Finsupp.lmapDomain ℚ ℚ (integralFiberGenericPoint f)

theorem integralFiberCycleExtension_injective : Function.Injective (integralFiberCycleExtension f) := by
  exact Finsupp.mapDomain_injective (integralFiberGenericPoint_injective f)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberGenericPoint.BundleCycles
end ComponentSource_15

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberGenericPoint"

@[expose] public section ComponentSource_16
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.AffineSpace -/

/-! # Affine Space -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.AffineSpace.BundleCycles

noncomputable section

/-! # LineBundleCycles: the ordinary polynomial spectrum is the actual relative affine line -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (R : Type) [CommRing R]

def polynomialAffineSpaceEquiv : Spec (.of (Polynomial R)) ≅ AffineSpace PUnit (Spec (.of R)) :=
  Scheme.Spec.mapIso (MvPolynomial.uniqueAlgEquiv R PUnit).toRingEquiv.toCommRingCatIso.op ≪≫
    (AffineSpace.SpecIso PUnit (.of R)).symm

theorem polynomialAffineSpaceEquiv_over :
    (polynomialAffineSpaceEquiv R).hom ≫ (AffineSpace PUnit (Spec (.of R)) ↘ Spec (.of R)) =
      Projection.BundleCycles.polynomialProjection R := by
  have h : CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial PUnit R) ≫
      (MvPolynomial.uniqueAlgEquiv R PUnit).toRingEquiv.toCommRingCatIso.hom =
        CommRingCat.ofHom (algebraMap R (Polynomial R)) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact (MvPolynomial.uniqueAlgEquiv R PUnit).commutes a
  change (Spec.map (MvPolynomial.uniqueAlgEquiv R PUnit).toRingEquiv.toCommRingCatIso.hom ≫
    (AffineSpace.SpecIso PUnit (.of R)).inv) ≫ _ = _
  rw [Category.assoc, AffineSpace.SpecIso_inv_over, ← Spec.map_comp, h]
  rfl

instance polynomialProjection_smooth : Smooth (Projection.BundleCycles.polynomialProjection R) :=
  HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr
    (Algebra.Smooth.mk inferInstance inferInstance))

instance polynomialProjection_geometricallyIntegral : GeometricallyIntegral (Projection.BundleCycles.polynomialProjection R) := by
  constructor
  intro K hK y Z a b h
  let e := polynomialAffineSpaceEquiv R
  apply (show GeometricallyIntegral (AffineSpace PUnit (Spec (.of R)) ↘ Spec (.of R)) from
    inferInstance).geometrically_isIntegral y (a ≫ e.hom) b
  apply h.of_iso (.refl _) e (.refl _) (.refl _)
  · simp only [Iso.refl_hom, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · exact (Category.comp_id _).trans (polynomialAffineSpaceEquiv_over R).symm
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

theorem polynomialPrimePoint_eq_fiberGeneric (p : Spec (.of R)) :
    Projection.BundleCycles.polynomialPrimePoint R p = Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Projection.BundleCycles.polynomialProjection R) p := by
  apply Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint_unique _ _ _ (Projection.BundleCycles.polynomialPrimePoint_projection R p)
  intro P hP
  exact (congrArg (Projection.BundleCycles.polynomialPrimePoint R) hP) ▸ Projection.BundleCycles.polynomialPrimePoint_specializes R P

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.AffineSpace.BundleCycles
end ComponentSource_16

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.AffineSpace"

@[expose] public section ComponentSource_17
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.ChartProperties -/

/-! # Chart Properties -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.ChartProperties.BundleCycles

noncomputable section

/-! # LineBundleCycles: geometric properties proved from actual affine-space pullback charts -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem affineSpaceSpecProjection_smooth (B : CommRingCat.{0}) (ι : Type) [Finite ι] :
    Smooth (AffineSpace ι (Spec B) ↘ Spec B) := by
  let e := AffineSpace.SpecIso ι B
  let q := Spec.map (CommRingCat.ofHom (MvPolynomial.C : B →+* MvPolynomial ι B))
  have hq : Smooth q := HasRingHomProperty.Spec_iff.mpr
    (RingHom.smooth_algebraMap.mpr (Algebra.Smooth.mk inferInstance inferInstance))
  have he : AffineSpace ι (Spec B) ↘ Spec B = e.hom ≫ q := by
    apply (cancel_epi e.inv).mp
    rw [← Category.assoc, e.inv_hom_id, Category.id_comp]
    exact AffineSpace.SpecIso_inv_over (n := ι) B
  have h : Smooth (e.hom ≫ q) := @smooth_comp _ _ e.hom _ q inferInstance hq
  exact he.symm ▸ h

theorem morphismProperty_of_affineSpaceCharts (P : MorphismProperty Scheme.{0})
    [IsZariskiLocalAtTarget P] {X Y : Scheme.{0}} (f : X ⟶ Y)
    (hcharts : ∀ y : Y, ∃ (B : CommRingCat.{0}) (i : Spec B ⟶ Y) (ι : Type) (_ : Finite ι)
      (j : AffineSpace ι (Spec B) ⟶ X),
      IsOpenImmersion i ∧ IsOpenImmersion j ∧ y ∈ Set.range i ∧
      IsPullback (AffineSpace ι (Spec B) ↘ Spec B) j i f)
    (hP : ∀ (B : CommRingCat.{0}) (ι : Type) [Finite ι], P (AffineSpace ι (Spec B) ↘ Spec B)) : P f := by
  choose B i ι hι j hi hj hy hsq using hcharts
  let C : Y.OpenCover := Scheme.Cover.mkOfCovers Y (fun y => Spec (B y)) i
    (fun y => ⟨y, hy y⟩) hi
  exact Global.DeformationProperties.BundleCycles.morphismProperty_of_cover_pullbacks P f C
    (fun y => AffineSpace (ι y) (Spec (B y))) j
    (fun y => AffineSpace (ι y) (Spec (B y)) ↘ Spec (B y)) hsq
    (fun y => @hP (B y) (ι y) (hι y))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.ChartProperties.BundleCycles
end ComponentSource_17

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.ChartProperties"

@[expose] public section ComponentSource_18
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.Charts -/

/-! # Charts -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.Charts.BundleCycles

noncomputable section

/-! # LineBundleCycles: actual polynomial charts for the relative affine line over any scheme -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

variable (X : Scheme.{0})

instance affineLineBaseChart_isOpenImmersion (U : X.affineOpens) : IsOpenImmersion U.2.fromSpec :=
  IsAffineOpen.isOpenImmersion_fromSpec U.2

abbrev affineLine : Scheme := AffineSpace PUnit X

def affineLineProjection : affineLine X ⟶ X := AffineSpace PUnit X ↘ X

def affineLinePolynomialChart (U : X.affineOpens) :
    Spec (.of (Polynomial Γ(X, U.1))) ⟶ affineLine X :=
  (LineBundles.Polynomial.AffineSpace.BundleCycles.polynomialAffineSpaceEquiv Γ(X, U.1)).hom ≫ AffineSpace.map PUnit U.2.fromSpec

theorem affineLinePolynomialChart_toBase (U : X.affineOpens) :
    affineLinePolynomialChart X U ≫ affineLineProjection X = LineBundles.Polynomial.Projection.BundleCycles.polynomialProjection Γ(X, U.1) ≫ U.2.fromSpec := by
  change ((LineBundles.Polynomial.AffineSpace.BundleCycles.polynomialAffineSpaceEquiv Γ(X, U.1)).hom ≫ AffineSpace.map PUnit U.2.fromSpec) ≫ (AffineSpace PUnit X ↘ X) = _
  rw [Category.assoc, AffineSpace.map_over, ← Category.assoc, LineBundles.Polynomial.AffineSpace.BundleCycles.polynomialAffineSpaceEquiv_over]

theorem affineLinePolynomialChart_isPullback (U : X.affineOpens) :
    IsPullback (LineBundles.Polynomial.Projection.BundleCycles.polynomialProjection Γ(X, U.1)) (affineLinePolynomialChart X U)
      U.2.fromSpec (affineLineProjection X) := by
  let e := LineBundles.Polynomial.AffineSpace.BundleCycles.polynomialAffineSpaceEquiv Γ(X, U.1)
  apply (AffineSpace.isPullback_map (n := PUnit) U.2.fromSpec).flip.of_iso e.symm (.refl _) (.refl _) (.refl _)
  · change _ ≫ 𝟙 _ = e.inv ≫ _
    apply (cancel_epi e.hom).mp
    rw [Category.comp_id, ← Category.assoc, e.hom_inv_id, Category.id_comp]
    exact LineBundles.Polynomial.AffineSpace.BundleCycles.polynomialAffineSpaceEquiv_over Γ(X, U.1)
  · change _ ≫ 𝟙 _ = e.inv ≫ (e.hom ≫ _)
    rw [Category.comp_id, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl

instance affineLinePolynomialChart_isOpenImmersion (U : X.affineOpens) :
    IsOpenImmersion (affineLinePolynomialChart X U) := by
  have h : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
  exact MorphismProperty.of_isPullback (affineLinePolynomialChart_isPullback X U) h

theorem affineLinePolynomialChart_range (U : X.affineOpens) :
    Set.range (affineLinePolynomialChart X U) = affineLineProjection X ⁻¹' (U.1 : Set X) := by
  have h := Scheme.image_preimage_eq_of_isPullback (affineLinePolynomialChart_isPullback X U) Set.univ
  simp only [Set.preimage_univ, Set.image_univ] at h
  exact h.trans (congrArg (fun A : Set X => affineLineProjection X ⁻¹' A) U.2.range_fromSpec)

theorem affineLinePolynomialChart_covers (x : affineLine X) :
    ∃ (U : X.affineOpens) (y : Spec (.of (Polynomial Γ(X, U.1)))),
      affineLinePolynomialChart X U y = x := by
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top (affineLineProjection X x))
  have h : x ∈ Set.range (affineLinePolynomialChart X ⟨U, hU⟩) :=
    (congrArg (fun A : Set (affineLine X) => x ∈ A) (affineLinePolynomialChart_range X ⟨U, hU⟩)).mpr hx
  obtain ⟨y, hy⟩ := h
  exact ⟨⟨U, hU⟩, y, hy⟩

def affineLinePolynomialCover : (affineLine X).OpenCover :=
  Scheme.Cover.mkOfCovers X.affineOpens (fun U => Spec (.of (Polynomial Γ(X, U.1))))
    (affineLinePolynomialChart X) (affineLinePolynomialChart_covers X)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.Charts.BundleCycles
end ComponentSource_18

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.Charts"

@[expose] public section ComponentSource_19
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.Space -/

/-! # Space -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.Space.BundleCycles

noncomputable section

section

/-! # LineBundleCycles: smoothness and Noetherianity of the actual relative affine line -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (X : Scheme.{0})

instance affineLineChartRing_noetherian [IsLocallyNoetherian X] (U : X.affineOpens) :
    IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U

instance affineLineProjection_smooth : Smooth (Charts.BundleCycles.affineLineProjection X) := by
  have : IsZariskiLocalAtSource (@Smooth.{0}) := HasRingHomProperty.instIsZariskiLocalAtSource
  apply IsZariskiLocalAtSource.of_openCover (P := @Smooth) (Charts.BundleCycles.affineLinePolynomialCover X)
  intro U
  have h : Smooth (LineBundles.Polynomial.Projection.BundleCycles.polynomialProjection Γ(X, U.1) ≫ U.2.fromSpec) := by
    have h₁ := LineBundles.Polynomial.AffineSpace.BundleCycles.polynomialProjection_smooth Γ(X, U.1)
    have : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
    have h₂ : Smooth U.2.fromSpec := inferInstance
    exact @smooth_comp _ _ (LineBundles.Polynomial.Projection.BundleCycles.polynomialProjection Γ(X, U.1)) _ U.2.fromSpec h₁ h₂
  exact (congrArg (fun k => Smooth k) (Charts.BundleCycles.affineLinePolynomialChart_toBase X U)).mpr h

instance affineLineProjection_geometricallyIntegral : GeometricallyIntegral (Charts.BundleCycles.affineLineProjection X) :=
  inferInstanceAs (GeometricallyIntegral (AffineSpace PUnit X ↘ X))

instance affineLineProjection_isAffineHom : IsAffineHom (Charts.BundleCycles.affineLineProjection X) :=
  inferInstanceAs (IsAffineHom (AffineSpace PUnit X ↘ X))

instance affineLine_isLocallyNoetherian [IsLocallyNoetherian X] : IsLocallyNoetherian (Charts.BundleCycles.affineLine X) :=
  LocallyOfFiniteType.isLocallyNoetherian (Charts.BundleCycles.affineLineProjection X)

instance affineLine_isNoetherian [AlgebraicGeometry.IsNoetherian X] :
    AlgebraicGeometry.IsNoetherian (Charts.BundleCycles.affineLine X) := by
  have : CompactSpace (Charts.BundleCycles.affineLine X) := QuasiCompact.compactSpace_of_compactSpace (Charts.BundleCycles.affineLineProjection X)
  exact ⟨⟩

end

section

/-! # LineBundleCycles: the actual closed zero section of the relative affine line -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (X : Scheme.{0})

def affineLineZeroSection : X ⟶ Charts.BundleCycles.affineLine X := AffineSpace.homOfVector (𝟙 X) (fun _ : PUnit => 0)

def affineLineCoordinate : Γ(Charts.BundleCycles.affineLine X, ⊤) := AffineSpace.coord X PUnit.unit

theorem affineLineZeroSection_projection : affineLineZeroSection X ≫ Charts.BundleCycles.affineLineProjection X = 𝟙 X :=
  AffineSpace.homOfVector_over _ _

theorem affineLineZeroSection_coordinate : (affineLineZeroSection X).appTop (affineLineCoordinate X) = 0 :=
  AffineSpace.homOfVector_appTop_coord _ _ _

instance affineLineZeroSection_isClosedImmersion : IsClosedImmersion (affineLineZeroSection X) := by
  have : IsClosedImmersion (affineLineZeroSection X ≫ Charts.BundleCycles.affineLineProjection X) :=
    (affineLineZeroSection_projection X).symm ▸ (inferInstance : IsClosedImmersion (𝟙 X))
  exact IsClosedImmersion.of_comp (affineLineZeroSection X) (Charts.BundleCycles.affineLineProjection X)

end

/-! # LineBundleCycles: the global affine-line coordinate is the actual polynomial variable on every chart -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (R : Type) [CommRing R]

def polynomialCoordinateSection : Γ(Spec (.of (Polynomial R)), ⊤) :=
  (Scheme.ΓSpecIso (.of (Polynomial R))).inv Polynomial.X

theorem polynomialAffineSpaceEquiv_coordinate :
    (LineBundles.Polynomial.AffineSpace.BundleCycles.polynomialAffineSpaceEquiv R).hom.appTop (affineLineCoordinate (Spec (.of R))) =
      polynomialCoordinateSection R := by
  let a : CommRingCat.of (MvPolynomial PUnit R) ⟶ CommRingCat.of (Polynomial R) :=
    (MvPolynomial.uniqueAlgEquiv R PUnit).toRingEquiv.toCommRingCatIso.hom
  have hn := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality a) (MvPolynomial.X PUnit.unit)
  have hX : a (MvPolynomial.X PUnit.unit) = Polynomial.X := MvPolynomial.eval₂_X _ _ _
  change (Scheme.ΓSpecIso (.of (Polynomial R))).inv (a (MvPolynomial.X PUnit.unit)) =
    (Spec.map a).appTop ((Scheme.ΓSpecIso (.of (MvPolynomial PUnit R))).inv (MvPolynomial.X PUnit.unit)) at hn
  rw [hX] at hn
  change (Spec.map a ≫ (AffineSpace.SpecIso PUnit (.of R)).inv).appTop
    (AffineSpace.coord (Spec (.of R)) PUnit.unit) = _
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.SpecIso_inv_appTop_coord]
  exact hn.symm

variable (X : Scheme.{0})

theorem affineLineCoordinate_on_chart (U : X.affineOpens) :
    (Charts.BundleCycles.affineLinePolynomialChart X U).appTop (affineLineCoordinate X) =
      polynomialCoordinateSection Γ(X, U.1) := by
  change ((LineBundles.Polynomial.AffineSpace.BundleCycles.polynomialAffineSpaceEquiv Γ(X, U.1)).hom ≫ AffineSpace.map PUnit U.2.fromSpec).appTop
    (AffineSpace.coord X PUnit.unit) = _
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.map_appTop_coord]
  exact polynomialAffineSpaceEquiv_coordinate Γ(X, U.1)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.Space.BundleCycles
end ComponentSource_19

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.Space"

@[expose] public section ComponentSource_20
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberOpen -/

/-! # Fiber Open -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberOpen.BundleCycles

noncomputable section

section

/-! # LineBundleCycles: actual fiber generic points commute with every scheme pullback square -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

theorem integralFiberGenericPoint_naturality {X Y X' Y' : Scheme.{0}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (i : Y' ⟶ Y) (j : X' ⟶ X)
    [GeometricallyIntegral f] [GeometricallyIntegral f'] (h : IsPullback f' j i f) (y : Y') :
    j (FiberGenericPoint.BundleCycles.integralFiberGenericPoint f' y) = FiberGenericPoint.BundleCycles.integralFiberGenericPoint f (i y) := by
  apply FiberGenericPoint.BundleCycles.integralFiberGenericPoint_unique
  · exact (congrArg (fun k => k (FiberGenericPoint.BundleCycles.integralFiberGenericPoint f' y)) h.w).symm.trans
      (congrArg i (FiberGenericPoint.BundleCycles.integralFiberGenericPoint_projection f' y))
  · intro z hz
    obtain ⟨w, hw₁, hw₂⟩ := Scheme.exists_preimage_of_isPullback h y z hz.symm
    exact hw₂ ▸ (FiberGenericPoint.BundleCycles.integralFiberGenericPoint_specializes f' y w hw₁).map j.continuous

theorem integralFiberCycleExtension_naturality {X Y X' Y' : Scheme.{0}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (i : Y' ⟶ Y) (j : X' ⟶ X)
    [GeometricallyIntegral f] [GeometricallyIntegral f'] (h : IsPullback f' j i f) (z : Y' →₀ ℚ) :
    Finsupp.mapDomain j (FiberGenericPoint.BundleCycles.integralFiberCycleExtension f' z) =
      FiberGenericPoint.BundleCycles.integralFiberCycleExtension f (Finsupp.mapDomain i z) := by
  change Finsupp.mapDomain j (Finsupp.mapDomain (FiberGenericPoint.BundleCycles.integralFiberGenericPoint f') z) =
    Finsupp.mapDomain (FiberGenericPoint.BundleCycles.integralFiberGenericPoint f) (Finsupp.mapDomain i z)
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  exact congrArg (fun k => Finsupp.mapDomain k z)
    (funext (integralFiberGenericPoint_naturality f f' i j h))

end

section

/-! # LineBundleCycles: actual fiber-generic cycle extension commutes with open restriction -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem integralFiberCycleExtension_openRestriction {E X E' U : Scheme.{0}}
    (p : E ⟶ X) (q : E' ⟶ U) [GeometricallyIntegral p] [GeometricallyIntegral q]
    (i : U ⟶ X) (j : E' ⟶ E) [IsOpenImmersion i] [IsOpenImmersion j]
    (h : IsPullback q j i p) (z : X →₀ ℚ) :
    Finsupp.comapDomain j (FiberGenericPoint.BundleCycles.integralFiberCycleExtension p z) j.isOpenEmbedding.injective.injOn =
      FiberGenericPoint.BundleCycles.integralFiberCycleExtension q (Finsupp.comapDomain i z i.isOpenEmbedding.injective.injOn) := by
  ext a
  change Finsupp.mapDomain (FiberGenericPoint.BundleCycles.integralFiberGenericPoint p) z (j a) =
    Finsupp.mapDomain (FiberGenericPoint.BundleCycles.integralFiberGenericPoint q)
      (Finsupp.comapDomain i z i.isOpenEmbedding.injective.injOn) a
  by_cases ha : a ∈ Set.range (FiberGenericPoint.BundleCycles.integralFiberGenericPoint q)
  · obtain ⟨u, rfl⟩ := ha
    rw [integralFiberGenericPoint_naturality p q i j h,
      Finsupp.mapDomain_apply_of_injective (FiberGenericPoint.BundleCycles.integralFiberGenericPoint_injective p),
      Finsupp.mapDomain_apply_of_injective (FiberGenericPoint.BundleCycles.integralFiberGenericPoint_injective q)]
    rfl
  · have hj : j a ∉ Set.range (FiberGenericPoint.BundleCycles.integralFiberGenericPoint p) := by
      rintro ⟨x, hx⟩
      have hb : i (q a) = x :=
        (congrArg (fun k : E' ⟶ X => k a) h.w).trans
          ((congrArg p hx.symm).trans (FiberGenericPoint.BundleCycles.integralFiberGenericPoint_projection p x))
      have he := integralFiberGenericPoint_naturality p q i j h (q a)
      rw [hb] at he
      exact ha ⟨q a, j.isOpenEmbedding.injective (he.trans hx)⟩
    rw [Finsupp.mapDomain_of_notMem_range _ _ hj, Finsupp.mapDomain_of_notMem_range _ _ ha]

end

/-! Fiber generic points and cycle extension commute with a square
of open immersions, even when the source open is only part of the inverse image. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {E X E' U : Scheme.{0}}
    (p : E ⟶ X) (q : E' ⟶ U) [GeometricallyIntegral p] [GeometricallyIntegral q]
    (i : U ⟶ X) (j : E' ⟶ E) [IsOpenImmersion i] [IsOpenImmersion j]
    (h : q ≫ i = j ≫ p)

include h in
theorem integralFiberGenericPoint_openSquare (u : U) :
    j (FiberGenericPoint.BundleCycles.integralFiberGenericPoint q u) = FiberGenericPoint.BundleCycles.integralFiberGenericPoint p (i u) := by
  have hp : p (j (FiberGenericPoint.BundleCycles.integralFiberGenericPoint q u)) = i u :=
    (congrArg (fun f : E' ⟶ X => f (FiberGenericPoint.BundleCycles.integralFiberGenericPoint q u)) h).symm.trans
      (congrArg i (FiberGenericPoint.BundleCycles.integralFiberGenericPoint_projection q u))
  have hs := FiberGenericPoint.BundleCycles.integralFiberGenericPoint_specializes p (i u) (j (FiberGenericPoint.BundleCycles.integralFiberGenericPoint q u)) hp
  have hm : FiberGenericPoint.BundleCycles.integralFiberGenericPoint p (i u) ∈ j.opensRange :=
    hs.mem_open j.opensRange.isOpen ⟨FiberGenericPoint.BundleCycles.integralFiberGenericPoint q u, rfl⟩
  obtain ⟨a, ha⟩ := hm
  have hqa : q a = u := by
    apply i.isOpenEmbedding.injective
    exact (congrArg (fun f : E' ⟶ X => f a) h).trans
      ((congrArg p ha).trans (FiberGenericPoint.BundleCycles.integralFiberGenericPoint_projection p (i u)))
  have ht : j (FiberGenericPoint.BundleCycles.integralFiberGenericPoint q u) ⤳ FiberGenericPoint.BundleCycles.integralFiberGenericPoint p (i u) :=
    ha ▸ (FiberGenericPoint.BundleCycles.integralFiberGenericPoint_specializes q u a hqa).map j.continuous
  exact (ht.antisymm hs).eq

include h in
theorem integralFiberCycleExtension_openSquare (z : X →₀ ℚ) :
    Finsupp.comapDomain j (FiberGenericPoint.BundleCycles.integralFiberCycleExtension p z) j.isOpenEmbedding.injective.injOn =
      FiberGenericPoint.BundleCycles.integralFiberCycleExtension q (Finsupp.comapDomain i z i.isOpenEmbedding.injective.injOn) := by
  ext a
  change Finsupp.mapDomain (FiberGenericPoint.BundleCycles.integralFiberGenericPoint p) z (j a) =
    Finsupp.mapDomain (FiberGenericPoint.BundleCycles.integralFiberGenericPoint q)
      (Finsupp.comapDomain i z i.isOpenEmbedding.injective.injOn) a
  by_cases ha : a ∈ Set.range (FiberGenericPoint.BundleCycles.integralFiberGenericPoint q)
  · obtain ⟨u, rfl⟩ := ha
    rw [integralFiberGenericPoint_openSquare p q i j h,
      Finsupp.mapDomain_apply_of_injective (FiberGenericPoint.BundleCycles.integralFiberGenericPoint_injective p),
      Finsupp.mapDomain_apply_of_injective (FiberGenericPoint.BundleCycles.integralFiberGenericPoint_injective q)]
    rfl
  · have hj : j a ∉ Set.range (FiberGenericPoint.BundleCycles.integralFiberGenericPoint p) := by
      rintro ⟨x, hx⟩
      have hb : i (q a) = x :=
        (congrArg (fun k : E' ⟶ X => k a) h).trans
          ((congrArg p hx.symm).trans (FiberGenericPoint.BundleCycles.integralFiberGenericPoint_projection p x))
      have he := integralFiberGenericPoint_openSquare p q i j h (q a)
      rw [hb] at he
      exact ha ⟨q a, j.isOpenEmbedding.injective (he.trans hx)⟩
    rw [Finsupp.mapDomain_of_notMem_range _ _ hj, Finsupp.mapDomain_of_notMem_range _ _ ha]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberOpen.BundleCycles
end ComponentSource_20

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberOpen"

@[expose] public section ComponentSource_21
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberFieldNaturality -/

/-! # Fiber Field Naturality -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberFieldNaturality.BundleCycles

noncomputable section

section

/-! # LineBundleCycles: actual function-field pullback and fiber generic points on integral schemes -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X Y : Scheme.{0}} (f : X ⟶ Y) [GeometricallyIntegral f]
    [IsIntegral X] [IsIntegral Y]

theorem integralFiberProjection_genericPoint : f (genericPoint X) = genericPoint Y := by
  apply Specializes.antisymm _ (genericPoint_specializes _ ) |>.eq
  obtain ⟨x, hx⟩ := (inferInstance : Surjective f).surj (genericPoint Y)
  exact hx ▸ (genericPoint_specializes x).map f.continuous

theorem integralFiberGenericPoint_generic :
    FiberGenericPoint.BundleCycles.integralFiberGenericPoint f (genericPoint Y) = genericPoint X := by
  apply Eq.symm
  apply FiberGenericPoint.BundleCycles.integralFiberGenericPoint_unique f _ _ (integralFiberProjection_genericPoint f)
  intro z _
  exact genericPoint_specializes z

def integralFiberFunctionFieldMap : Y.functionField ⟶ X.functionField :=
  Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f (integralFiberProjection_genericPoint f)

theorem integralFiberFunctionFieldMap_ne_zero (g : Y.functionField) (hg : g ≠ 0) :
    integralFiberFunctionFieldMap f g ≠ 0 :=
  (map_ne_zero_iff _ (integralFiberFunctionFieldMap f).hom.injective).mpr hg

end

/-! # LineBundleCycles: actual generic-stalk maps on open squares and isomorphic factorizations -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem integralFiberFunctionFieldMap_iso {X Y S : Scheme.{0}}
    [IsIntegral X] [IsIntegral Y] [IsIntegral S]
    (e : X ≅ Y) (p : X ⟶ S) (q : Y ⟶ S)
    [GeometricallyIntegral p] [GeometricallyIntegral q] (h : e.hom ≫ q = p) :
    integralFiberFunctionFieldMap p = integralFiberFunctionFieldMap q ≫ RationalDivisorRestriction.BundleCycles.openFunctionFieldMap e.hom :=
  (GenericFieldComposition.BundleCycles.genericFieldMap_congr h.symm _ _).trans
    (GenericFieldComposition.BundleCycles.genericFieldMap_comp e.hom q (genericPoint_eq_of_isOpenImmersion e.hom)
      (integralFiberProjection_genericPoint q))

theorem integralFiberFunctionFieldMap_openSquare {X Y X' Y' : Scheme.{0}}
    [IsIntegral X] [IsIntegral Y] [IsIntegral X'] [IsIntegral Y']
    (p : X ⟶ Y) (q : X' ⟶ Y') [GeometricallyIntegral p] [GeometricallyIntegral q]
    (i : Y' ⟶ Y) (j : X' ⟶ X) [IsOpenImmersion i] [IsOpenImmersion j]
    (h : j ≫ p = q ≫ i) :
    integralFiberFunctionFieldMap p ≫ RationalDivisorRestriction.BundleCycles.openFunctionFieldMap j =
      RationalDivisorRestriction.BundleCycles.openFunctionFieldMap i ≫ integralFiberFunctionFieldMap q :=
  (GenericFieldComposition.BundleCycles.genericFieldMap_comp j p (genericPoint_eq_of_isOpenImmersion j)
    (integralFiberProjection_genericPoint p)).symm.trans
      ((GenericFieldComposition.BundleCycles.genericFieldMap_congr h _ _).trans
        (GenericFieldComposition.BundleCycles.genericFieldMap_comp q i (integralFiberProjection_genericPoint q)
          (genericPoint_eq_of_isOpenImmersion i)))

theorem integralFiberFunctionFieldMap_factorization {X W Y S : Scheme.{0}}
    [IsIntegral X] [IsIntegral W] [IsIntegral Y] [IsIntegral S]
    (e : X ≅ W) (p : X ⟶ S) (f : W ⟶ Y) (g : Y ⟶ S)
    [GeometricallyIntegral p] [GeometricallyIntegral f] [GeometricallyIntegral g]
    (h : e.hom ≫ f ≫ g = p) :
    integralFiberFunctionFieldMap p ≫ RationalDivisorRestriction.BundleCycles.openFunctionFieldMap e.inv =
      integralFiberFunctionFieldMap g ≫ integralFiberFunctionFieldMap f := by
  have hi : e.inv ≫ p = f ≫ g := by
    rw [← h, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  exact (GenericFieldComposition.BundleCycles.genericFieldMap_comp e.inv p (genericPoint_eq_of_isOpenImmersion e.inv)
    (integralFiberProjection_genericPoint p)).symm.trans
      ((GenericFieldComposition.BundleCycles.genericFieldMap_congr hi _ _).trans
        (GenericFieldComposition.BundleCycles.genericFieldMap_comp f g (integralFiberProjection_genericPoint f)
          (integralFiberProjection_genericPoint g)))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberFieldNaturality.BundleCycles
end ComponentSource_21

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberFieldNaturality"

@[expose] public section ComponentSource_22
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.GenericPoint -/

/-! # Generic Point -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.GenericPoint.BundleCycles

noncomputable section

/-! # LineBundleCycles: affine-line fiber generic points and rational functions on actual polynomial charts -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (X : Scheme.{0})

theorem affineLineFiberGenericPoint_on_chart (U : X.affineOpens) (p : Spec Γ(X, U.1)) :
    Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X) (U.2.fromSpec p) =
      Charts.BundleCycles.affineLinePolynomialChart X U (Polynomial.Projection.BundleCycles.polynomialPrimePoint Γ(X, U.1) p) := by
  exact ((congrArg (Charts.BundleCycles.affineLinePolynomialChart X U) (Polynomial.AffineSpace.BundleCycles.polynomialPrimePoint_eq_fiberGeneric Γ(X, U.1) p)).trans
    (Integral.FiberOpen.BundleCycles.integralFiberGenericPoint_naturality (Charts.BundleCycles.affineLineProjection X) (Polynomial.Projection.BundleCycles.polynomialProjection Γ(X, U.1))
      U.2.fromSpec (Charts.BundleCycles.affineLinePolynomialChart X U) (Charts.BundleCycles.affineLinePolynomialChart_isPullback X U) p)).symm

variable [IsIntegral X]

theorem affineLineFunctionField_on_chart (U : X.affineOpens) [Nonempty U.1] :
    Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap (Charts.BundleCycles.affineLineProjection X) ≫ RationalDivisorRestriction.BundleCycles.openFunctionFieldMap (Charts.BundleCycles.affineLinePolynomialChart X U) =
      RationalDivisorRestriction.BundleCycles.openFunctionFieldMap U.2.fromSpec ≫ Polynomial.Projection.BundleCycles.polynomialFunctionFieldMap Γ(X, U.1) := by
  have : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
  exact (GenericFieldComposition.BundleCycles.genericFieldMap_comp (Charts.BundleCycles.affineLinePolynomialChart X U) (Charts.BundleCycles.affineLineProjection X)
    (genericPoint_eq_of_isOpenImmersion _) (Integral.FiberFieldNaturality.BundleCycles.integralFiberProjection_genericPoint (Charts.BundleCycles.affineLineProjection X))).symm.trans
      ((GenericFieldComposition.BundleCycles.genericFieldMap_congr (Charts.BundleCycles.affineLinePolynomialChart_toBase X U) _ _).trans
        (GenericFieldComposition.BundleCycles.genericFieldMap_comp (Polynomial.Projection.BundleCycles.polynomialProjection Γ(X, U.1)) U.2.fromSpec
          (Polynomial.Projection.BundleCycles.polynomialProjection_genericPoint Γ(X, U.1)) (genericPoint_eq_of_isOpenImmersion _)))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.GenericPoint.BundleCycles
end ComponentSource_22

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.GenericPoint"

@[expose] public section ComponentSource_23
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.ClosedImage -/

/-! # Closed Image -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.ClosedImage.BundleCycles

noncomputable section

/-!
# LineBundleCycles: a closed integral scheme and its actual reduced image support

The canonical map from an integral closed subscheme to its reduced image
is an isomorphism. Its transported principal divisor is exactly the
closed pushforward of the original divisor, coefficient by coefficient.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {A X : Scheme} [IsIntegral A] (i : A ⟶ X) [IsClosedImmersion i]

def integralClosedImageIso : A ≅ CycleClass.Geometric.GenericPoint.reducedSupportScheme (CycleClass.Geometric.StratumClosure.integralImageClosure i) := by
  have he : IsIso (CycleClass.Geometric.StratumClosure.toReducedImageClosure i) := by
    change IsIso (i.toImage ≫ (CycleClass.Geometric.StratumClosure.reducedImageClosureIso i).hom)
    infer_instance
  exact @asIso _ _ _ _ (CycleClass.Geometric.StratumClosure.toReducedImageClosure i) he

theorem integralClosedImageIso_inclusion :
    (integralClosedImageIso i).hom ≫ CycleClass.Geometric.GenericPoint.reducedSupportι (CycleClass.Geometric.StratumClosure.integralImageClosure i) = i :=
  CycleClass.Geometric.StratumClosure.toReducedImageClosure_inclusion i

theorem integralClosedImage_genericPoint :
    irreducibleSetEquivPoints (CycleClass.Geometric.StratumClosure.integralImageClosure i) = i (genericPoint A) := by
  have hc := congrArg (fun j : A ⟶ X => j (genericPoint A)) (integralClosedImageIso_inclusion i)
  have hg := genericPoint_eq_of_isOpenImmersion (integralClosedImageIso i).hom
  exact (CycleClass.Geometric.GenericPoint.reducedSupport_genericPoint_eq (CycleClass.Geometric.StratumClosure.integralImageClosure i)).symm.trans
    ((congrArg (CycleClass.Geometric.GenericPoint.reducedSupportι (CycleClass.Geometric.StratumClosure.integralImageClosure i)) hg).symm.trans hc)

def integralClosedImageFunction (g : A.functionField) :
    (CycleClass.Geometric.GenericPoint.reducedSupportScheme (CycleClass.Geometric.StratumClosure.integralImageClosure i)).functionField :=
  (RationalDivisorRestriction.BundleCycles.openFunctionFieldIso (integralClosedImageIso i).hom).inv g

theorem integralClosedImageFunction_ne_zero (g : A.functionField) (hg : g ≠ 0) :
    integralClosedImageFunction i g ≠ 0 :=
  (map_ne_zero_iff _ (RationalDivisorRestriction.BundleCycles.openFunctionFieldIso (integralClosedImageIso i).hom).inv.hom.injective).mpr hg

variable [AlgebraicGeometry.IsNoetherian A] [AlgebraicGeometry.IsNoetherian X]

theorem integralClosedImage_principalDivisor (g : A.functionField) :
    Finsupp.mapDomain i (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor A g) =
      Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (CycleClass.Geometric.StratumClosure.integralImageClosure i) (integralClosedImageFunction i g) := by
  let e := integralClosedImageIso i
  have hc : CycleClass.Geometric.GenericPoint.reducedSupportι (CycleClass.Geometric.StratumClosure.integralImageClosure i) ∘ e.hom = i :=
    funext (fun a => congrArg (fun j : A ⟶ X => j a) (integralClosedImageIso_inclusion i))
  unfold Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor
  change Finsupp.mapDomain i (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor A g) =
    Finsupp.embDomain ⟨CycleClass.Geometric.GenericPoint.reducedSupportι (CycleClass.Geometric.StratumClosure.integralImageClosure i),
      (CycleClass.Geometric.GenericPoint.reducedSupportι (CycleClass.Geometric.StratumClosure.integralImageClosure i)).isClosedEmbedding.injective⟩
      (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (CycleClass.Geometric.GenericPoint.reducedSupportScheme (CycleClass.Geometric.StratumClosure.integralImageClosure i))
        ((RationalDivisorRestriction.BundleCycles.openFunctionFieldIso e.hom).inv g))
  rw [Finsupp.embDomain_eq_mapDomain, ← Closed.PrincipalPushforward.BundleCycles.rationalPrincipalDivisor_iso e g,
    ← Finsupp.mapDomain_comp]
  exact congrArg (fun j : A → X => Finsupp.mapDomain j (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor A g)) hc.symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.ClosedImage.BundleCycles
end ComponentSource_23

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.ClosedImage"

@[expose] public section ComponentSource_24
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.Support -/

/-! # Support -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.Support.BundleCycles

noncomputable section

/-! # LineBundleCycles: actual inverse images of closed integral supports in the relative affine line -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable (X : Scheme.{0}) (W : IrreducibleCloseds X)

def affineLineSupportMap : Charts.BundleCycles.affineLine (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) ⟶ Charts.BundleCycles.affineLine X :=
  AffineSpace.map PUnit (CycleClass.Geometric.GenericPoint.reducedSupportι W)

theorem affineLineSupport_isPullback :
    IsPullback (Charts.BundleCycles.affineLineProjection (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)) (affineLineSupportMap X W)
      (CycleClass.Geometric.GenericPoint.reducedSupportι W) (Charts.BundleCycles.affineLineProjection X) :=
  (AffineSpace.isPullback_map (n := PUnit) (CycleClass.Geometric.GenericPoint.reducedSupportι W)).flip

instance affineLineSupportMap_isClosedImmersion : IsClosedImmersion (affineLineSupportMap X W) :=
  MorphismProperty.of_isPullback (affineLineSupport_isPullback X W) inferInstance

def affineLineExtendedSupport : IrreducibleCloseds (Charts.BundleCycles.affineLine X) :=
  CycleClass.Geometric.StratumClosure.integralImageClosure (affineLineSupportMap X W)

theorem affineLineExtendedSupport_genericPoint :
    irreducibleSetEquivPoints (affineLineExtendedSupport X W) =
      Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X) (irreducibleSetEquivPoints W) := by
  exact (Integral.ClosedImage.BundleCycles.integralClosedImage_genericPoint (affineLineSupportMap X W)).trans
    ((congrArg (affineLineSupportMap X W)
      (Integral.FiberFieldNaturality.BundleCycles.integralFiberGenericPoint_generic (Charts.BundleCycles.affineLineProjection (CycleClass.Geometric.GenericPoint.reducedSupportScheme W))).symm).trans
        ((Integral.FiberOpen.BundleCycles.integralFiberGenericPoint_naturality (Charts.BundleCycles.affineLineProjection X)
          (Charts.BundleCycles.affineLineProjection (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)) (CycleClass.Geometric.GenericPoint.reducedSupportι W) (affineLineSupportMap X W)
          (affineLineSupport_isPullback X W) _).trans
            (congrArg (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X)) (CycleClass.Geometric.GenericPoint.reducedSupport_genericPoint_eq W))))

theorem affineLineExtendedSupport_coe : (affineLineExtendedSupport X W : Set (Charts.BundleCycles.affineLine X)) =
    Charts.BundleCycles.affineLineProjection X ⁻¹' (W : Set X) := by
  change closure (Set.range (affineLineSupportMap X W)) = _
  rw [(affineLineSupportMap X W).isClosedEmbedding.isClosed_range.closure_eq]
  have h := Scheme.image_preimage_eq_of_isPullback (affineLineSupport_isPullback X W) Set.univ
  simp only [Set.preimage_univ, Set.image_univ] at h
  exact h.trans (congrArg (fun A : Set X => Charts.BundleCycles.affineLineProjection X ⁻¹' A) (CycleClass.Geometric.GenericPoint.range_reducedSupportι W))

theorem affineLineExtendedSupport_eq_pointClosure : affineLineExtendedSupport X W =
    irreducibleSetEquivPoints.symm
      (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X) (irreducibleSetEquivPoints W)) :=
  irreducibleSetEquivPoints.injective ((affineLineExtendedSupport_genericPoint X W).trans
    (irreducibleSetEquivPoints.apply_symm_apply _).symm)

def affineLineExtendedFunction (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) :
    (CycleClass.Geometric.GenericPoint.reducedSupportScheme (affineLineExtendedSupport X W)).functionField :=
  Integral.ClosedImage.BundleCycles.integralClosedImageFunction (affineLineSupportMap X W)
    (Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap (Charts.BundleCycles.affineLineProjection (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)) g)

theorem affineLineExtendedFunction_ne_zero (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0) :
    affineLineExtendedFunction X W g ≠ 0 :=
  Integral.ClosedImage.BundleCycles.integralClosedImageFunction_ne_zero (affineLineSupportMap X W) _
    (Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap_ne_zero (Charts.BundleCycles.affineLineProjection (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)) g hg)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.Support.BundleCycles
end ComponentSource_24

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.Support"

@[expose] public section ComponentSource_25
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.PointSupport -/

/-! # Point Support -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.PointSupport.BundleCycles

noncomputable section

/-! # LineBundleCycles: every affine-line point lifts to the line over the actual closure of its base point -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable (X : Scheme.{0})

theorem affineLinePoint_liftSupport (W : IrreducibleCloseds X) (y : Charts.BundleCycles.affineLine X)
    (hy : Charts.BundleCycles.affineLineProjection X y = irreducibleSetEquivPoints W) :
    ∃ q : Charts.BundleCycles.affineLine (CycleClass.Geometric.GenericPoint.reducedSupportScheme W), Support.BundleCycles.affineLineSupportMap X W q = y ∧
      Charts.BundleCycles.affineLineProjection (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) q = genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) := by
  have h : CycleClass.Geometric.GenericPoint.reducedSupportι W (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)) = Charts.BundleCycles.affineLineProjection X y :=
    (CycleClass.Geometric.GenericPoint.reducedSupport_genericPoint_eq W).trans hy.symm
  obtain ⟨q, hq, hj⟩ := Scheme.exists_preimage_of_isPullback (Support.BundleCycles.affineLineSupport_isPullback X W)
    (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)) y h
  exact ⟨q, hj, hq⟩

theorem affineLineSupportMap_genericPoint (W : IrreducibleCloseds X) :
    Support.BundleCycles.affineLineSupportMap X W (genericPoint (Charts.BundleCycles.affineLine (CycleClass.Geometric.GenericPoint.reducedSupportScheme W))) =
      Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X) (irreducibleSetEquivPoints W) :=
  (Integral.ClosedImage.BundleCycles.integralClosedImage_genericPoint (Support.BundleCycles.affineLineSupportMap X W)).symm.trans
    (Support.BundleCycles.affineLineExtendedSupport_genericPoint X W)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.PointSupport.BundleCycles
end ComponentSource_25

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.PointSupport"

@[expose] public section ComponentSource_26
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.ZeroSection -/

/-! # Zero Section -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.ZeroSection.BundleCycles

noncomputable section

/-! # LineBundleCycles: the polynomial zero section and its actual coordinate vanishing locus -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (R : Type) [CommRing R]

def polynomialZeroSection : Spec (.of R) ⟶ Spec (.of (Polynomial R)) :=
  Spec.map (CommRingCat.ofHom Polynomial.constantCoeff)

theorem polynomialZeroSection_projection : polynomialZeroSection R ≫ Projection.BundleCycles.polynomialProjection R = 𝟙 _ := by
  have h : CommRingCat.ofHom (algebraMap R (Polynomial R)) ≫
      CommRingCat.ofHom (Polynomial.constantCoeff : Polynomial R →+* R) = 𝟙 (CommRingCat.of R) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact Polynomial.coeff_C_zero
  exact (Spec.map_comp _ _).symm.trans ((congrArg Spec.map h).trans (Spec.map_id _))

theorem polynomialZeroSection_coordinate :
    (polynomialZeroSection R).appTop (AffineLine.Space.BundleCycles.polynomialCoordinateSection R) = 0 := by
  have h := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (Polynomial.constantCoeff : Polynomial R →+* R))) Polynomial.X
  change (Scheme.ΓSpecIso (.of R)).inv (Polynomial.constantCoeff Polynomial.X) =
    (polynomialZeroSection R).appTop (AffineLine.Space.BundleCycles.polynomialCoordinateSection R) at h
  have hX : Polynomial.constantCoeff (Polynomial.X : Polynomial R) = 0 := Polynomial.coeff_X_zero
  simpa only [hX, map_zero] using h.symm

theorem polynomialZeroSection_affineSpace :
    polynomialZeroSection R ≫ (LineBundles.Polynomial.AffineSpace.BundleCycles.polynomialAffineSpaceEquiv R).hom = AffineLine.Space.BundleCycles.affineLineZeroSection (Spec (.of R)) := by
  apply AffineSpace.hom_ext
  · change (_ ≫ _) ≫ _ = AffineLine.Space.BundleCycles.affineLineZeroSection (Spec (.of R)) ≫ AffineLine.Charts.BundleCycles.affineLineProjection (Spec (.of R))
    rw [Category.assoc, LineBundles.Polynomial.AffineSpace.BundleCycles.polynomialAffineSpaceEquiv_over, polynomialZeroSection_projection,
      AffineLine.Space.BundleCycles.affineLineZeroSection_projection]
  · intro i
    cases i
    change (polynomialZeroSection R ≫ (LineBundles.Polynomial.AffineSpace.BundleCycles.polynomialAffineSpaceEquiv R).hom).appTop
      (AffineLine.Space.BundleCycles.affineLineCoordinate (Spec (.of R))) = _
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineLine.Space.BundleCycles.polynomialAffineSpaceEquiv_coordinate,
      polynomialZeroSection_coordinate]
    exact (AffineLine.Space.BundleCycles.affineLineZeroSection_coordinate (Spec (.of R))).symm

theorem polynomialZeroSection_range :
    Set.range (polynomialZeroSection R) =
      ((Spec (.of (Polynomial R))).basicOpen (AffineLine.Space.BundleCycles.polynomialCoordinateSection R) : Set (Spec (.of (Polynomial R))))ᶜ := by
  have h : Function.Surjective (Polynomial.constantCoeff : Polynomial R →+* R) :=
    fun a => ⟨Polynomial.C a, Polynomial.coeff_C_zero⟩
  change Set.range (PrimeSpectrum.comap (Polynomial.constantCoeff : Polynomial R →+* R)) = _
  rw [range_comap_of_surjective _ _ h, Polynomial.ker_constantCoeff]
  change PrimeSpectrum.zeroLocus (Ideal.span {(Polynomial.X : Polynomial R)} : Set (Polynomial R)) =
    ((Spec (.of (Polynomial R))).basicOpen
      ((Scheme.ΓSpecIso (.of (Polynomial R))).inv Polynomial.X) : Set (Spec (.of (Polynomial R))))ᶜ
  rw [basicOpen_eq_of_affine]
  ext p
  simp only [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
  change Ideal.span {Polynomial.X} ≤ p.asIdeal ↔ ¬Polynomial.X ∉ p.asIdeal
  exact (Ideal.span_singleton_le_iff_mem (I := p.asIdeal)).trans not_not.symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.ZeroSection.BundleCycles
end ComponentSource_26

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.ZeroSection"

@[expose] public section ComponentSource_27
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.ZeroPrime -/

/-! # Zero Prime -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.ZeroPrime.BundleCycles

noncomputable section

/-! # LineBundleCycles: the actual generic point of the polynomial zero divisor has height one -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (R : Type) [CommRing R] [IsDomain R]

def polynomialZeroPrime : Spec (.of (Polynomial R)) := ZeroSection.BundleCycles.polynomialZeroSection R (genericPoint (Spec (.of R)))

theorem polynomialZeroPrime_asIdeal : (polynomialZeroPrime R).asIdeal = Ideal.span {Polynomial.X} := by
  change (PrimeSpectrum.comap (Polynomial.constantCoeff : Polynomial R →+* R)
    (genericPoint (Spec (.of R)))).asIdeal = _
  rw [genericPoint_eq_bot_of_affine]
  exact Polynomial.ker_constantCoeff

theorem polynomialZeroPrime_coheight [IsNoetherianRing R] : Order.coheight (polynomialZeroPrime R) = 1 := by
  rw [← idealHeight_eq_coheight, polynomialZeroPrime_asIdeal]
  exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_iff_ne_zero.mpr Polynomial.X_ne_zero) Polynomial.not_isUnit_X

theorem polynomialZeroPrime_unique_height_one [IsNoetherianRing R] (p : Spec (.of (Polynomial R)))
    (hp : Order.coheight p = 1) (hX : Polynomial.X ∈ p.asIdeal) : p = polynomialZeroPrime R := by
  let : p.asIdeal.IsPrime := (show PrimeSpectrum (Polynomial R) from p).isPrime
  let : (polynomialZeroPrime R).asIdeal.IsPrime := (show PrimeSpectrum (Polynomial R) from polynomialZeroPrime R).isPrime
  have hle : (polynomialZeroPrime R).asIdeal ≤ p.asIdeal := by
    rw [polynomialZeroPrime_asIdeal]
    exact (Ideal.span_singleton_le_iff_mem (I := p.asIdeal)).mpr hX
  apply PrimeSpectrum.ext
  apply Eq.symm
  apply Ideal.eq_of_le_of_height_le (polynomialZeroPrime R).asIdeal hle
  rw [idealHeight_eq_coheight, idealHeight_eq_coheight, hp, polynomialZeroPrime_coheight]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.ZeroPrime.BundleCycles
end ComponentSource_27

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.ZeroPrime"

@[expose] public section ComponentSource_28
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.PrincipalPrimeStalk -/

/-! # Principal Prime Stalk -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.PrincipalPrimeStalk.BundleCycles

noncomputable section

/-! # LineBundleCycles: a principal prime generator generates the actual affine stalk maximal ideal -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem affinePrincipalPrime_stalk_maximalIdeal {R : Type} [CommRing R]
    (p : Spec (.of R)) (a : R) (hp : p.asIdeal = Ideal.span {a}) :
    Ideal.span {(Spec (.of R)).presheaf.germ ⊤ p (by trivial) ((Scheme.ΓSpecIso (.of R)).inv a)} =
      IsLocalRing.maximalIdeal ((Spec (.of R)).presheaf.stalk p) := by
  let : p.asIdeal.IsPrime := (show PrimeSpectrum R from p).isPrime
  let e := Spec.stalkIso (.of R) p
  have hg := ConcreteCategory.congr_hom (Spec.germ_stalkMapIso_hom (R := .of R) p)
    ((Scheme.ΓSpecIso (.of R)).inv a)
  change e.hom ((Spec (.of R)).presheaf.germ ⊤ p (by trivial) ((Scheme.ΓSpecIso (.of R)).inv a)) =
    algebraMap R (Localization.AtPrime p.asIdeal) ((Scheme.ΓSpecIso (.of R)).hom ((Scheme.ΓSpecIso (.of R)).inv a)) at hg
  rw [Iso.inv_hom_id_apply] at hg
  have hL : (Ideal.span {(Spec (.of R)).presheaf.germ ⊤ p (by trivial) ((Scheme.ΓSpecIso (.of R)).inv a)}).map e.hom.hom =
      IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal) := by
    rw [Ideal.map_span, Set.image_singleton, hg, ← Set.image_singleton, ← Ideal.map_span, ← hp]
    exact Localization.AtPrime.map_eq_maximalIdeal
  have hM : (IsLocalRing.maximalIdeal ((Spec (.of R)).presheaf.stalk p)).map e.hom.hom =
      IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal) :=
    IsLocalRing.map_ringEquiv_maximalIdeal e.commRingCatIsoToRingEquiv
  have h := congrArg (Ideal.comap e.hom.hom) (hL.trans hM.symm)
  have he : Function.Bijective e.hom.hom := e.commRingCatIsoToRingEquiv.bijective
  rw [Ideal.comap_map_of_bijective e.hom.hom he,
    Ideal.comap_map_of_bijective e.hom.hom he] at h
  exact h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.PrincipalPrimeStalk.BundleCycles
end ComponentSource_28

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.PrincipalPrimeStalk"

@[expose] public section ComponentSource_29
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.FlatOrderEq -/

/-! # Flat Order Eq -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.FlatOrderEq.BundleCycles.FlatOrder

noncomputable section

/-! Native orders of vanishing under flat local base change. If the
maximal ideal extends to the maximal ideal, all rational-function orders
are preserved under the compatible fraction-field embedding. -/

universe u

theorem residue_quotient_length (R : Type u) [CommRing R] [IsLocalRing R] :
    Module.length R (R ⧸ IsLocalRing.maximalIdeal R) = 1 := by
  let : Field (R ⧸ IsLocalRing.maximalIdeal R) := Ideal.Quotient.field (IsLocalRing.maximalIdeal R)
  rw [Module.length_eq_of_surjective (M := R ⧸ IsLocalRing.maximalIdeal R)
    (show Function.Surjective (algebraMap R (R ⧸ IsLocalRing.maximalIdeal R)) from Ideal.Quotient.mk_surjective)]
  exact Module.length_eq_one (R ⧸ IsLocalRing.maximalIdeal R) (R ⧸ IsLocalRing.maximalIdeal R)

variable (R S : Type u) [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
  [Algebra R S] [IsLocalHom (algebraMap R S)] [Module.Flat R S]

theorem ord_baseChange (a : R) :
    Ring.ord S (algebraMap R S a) = Ring.ord R a *
      Module.length S (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) := by
  have hi : Ideal.span {algebraMap R S a} = (Ideal.span {a}).map (algebraMap R S) := by
    rw [Ideal.map_span, Set.image_singleton]
  rw [Ring.ord, hi, (Ideal.qoutMapEquivTensorQout (R := R) (I := Ideal.span {a}) S).length_eq]
  exact IsLocalRing.length_baseChange R S _

theorem ord_eq (hmax : (IsLocalRing.maximalIdeal R).map (algebraMap R S) = IsLocalRing.maximalIdeal S)
    (a : R) : Ring.ord S (algebraMap R S a) = Ring.ord R a := by
  rw [ord_baseChange, hmax, residue_quotient_length, mul_one]

variable [IsDomain R] [IsDomain S] [IsNoetherianRing R] [IsNoetherianRing S]
  [Ring.KrullDimLE 1 R] [Ring.KrullDimLE 1 S]

omit [IsNoetherianRing S] [Ring.KrullDimLE 1 S] in
theorem ordMonoid_eq
    (hmax : (IsLocalRing.maximalIdeal R).map (algebraMap R S) = IsLocalRing.maximalIdeal S)
    (hinj : Function.Injective (algebraMap R S)) (a : R) :
    Ring.ordMonoidWithZeroHom S (algebraMap R S a) = Ring.ordMonoidWithZeroHom R a := by
  by_cases ha : a = 0
  · subst a
    simp only [map_zero]
  have ha' : algebraMap R S a ≠ 0 := (map_ne_zero_iff _ hinj).mpr ha
  have hR : Ring.ord R a = ((Ring.ord R a).toNat : ℕ∞) :=
    (ENat.natCast_toNat (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero ha))).symm
  have hS := (ord_eq R S hmax a).trans hR
  rw [Ring.ordMonoidWithZeroHom_eq_coe S (mem_nonZeroDivisors_of_ne_zero ha') hS,
    Ring.ordMonoidWithZeroHom_eq_coe R (mem_nonZeroDivisors_of_ne_zero ha) hR]

theorem ordFrac_eq {K L : Type u} [Field K] [Field L] [Algebra R K] [Algebra S L]
    [IsFractionRing R K] [IsFractionRing S L]
    (hmax : (IsLocalRing.maximalIdeal R).map (algebraMap R S) = IsLocalRing.maximalIdeal S)
    (hinj : Function.Injective (algebraMap R S)) (φ : K →+* L)
    (hφ : ∀ a : R, φ (algebraMap R K a) = algebraMap S L (algebraMap R S a)) (f : K) :
    Ring.ordFrac S (φ f) = Ring.ordFrac R f := by
  by_cases hf : f = 0
  · subst f
    simp only [map_zero]
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective R f
  have ha : a ≠ 0 := fun ha => hf (by simp [ha])
  have hb' : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  rw [map_div₀, hφ a, hφ b, map_div₀, map_div₀,
    Ring.ordFrac_eq_ord R ha, Ring.ordFrac_eq_ord R hb',
    Ring.ordFrac_eq_ord S ((map_ne_zero_iff _ hinj).mpr ha),
    Ring.ordFrac_eq_ord S ((map_ne_zero_iff _ hinj).mpr hb'),
    ordMonoid_eq R S hmax hinj a, ordMonoid_eq R S hmax hinj b]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.FlatOrderEq.BundleCycles.FlatOrder
end ComponentSource_29

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.FlatOrderEq"

@[expose] public section ComponentSource_30
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.PrincipalPrimeDivisor -/

/-! # Principal Prime Divisor -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.PrincipalPrimeDivisor.BundleCycles

noncomputable section

/-! # LineBundleCycles: an actual nonzero principal prime has exactly its reduced single-point divisor -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (p : Spec (.of R)) (a : R) (hp : p.asIdeal = Ideal.span {a}) (ha : a ≠ 0)

include hp ha

theorem affinePrincipalPrime_coheight : Order.coheight p = 1 := by
  let : p.asIdeal.IsPrime := (show PrimeSpectrum R from p).isPrime
  have hunit : ¬IsUnit a := by
    intro h
    apply (show p.asIdeal ≠ ⊤ from Ideal.IsPrime.ne_top')
    apply p.asIdeal.eq_top_of_isUnit_mem _ h
    rw [hp]
    exact Ideal.subset_span (Set.mem_singleton a)
  rw [← idealHeight_eq_coheight, hp]
  exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_iff_ne_zero.mpr ha) hunit

theorem affinePrincipalPrime_multiplicity :
    RegularDivisor.BundleCycles.regularFunctionDivisor (Spec (.of R)) ((Scheme.ΓSpecIso (.of R)).inv a) p = 1 := by
  have hs : (Scheme.ΓSpecIso (.of R)).inv a ≠ 0 :=
    (map_ne_zero_iff _ (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv.injective).mpr ha
  rw [RegularDivisor.BundleCycles.regularFunctionDivisor_coeff_length _ _ hs _ (affinePrincipalPrime_coheight p a hp ha),
    PrincipalPrimeStalk.BundleCycles.affinePrincipalPrime_stalk_maximalIdeal p a hp, FlatOrderEq.BundleCycles.FlatOrder.residue_quotient_length]
  rfl

theorem affinePrincipalPrime_divisor :
    RegularDivisor.BundleCycles.regularFunctionDivisor (Spec (.of R)) ((Scheme.ΓSpecIso (.of R)).inv a) = Finsupp.single p 1 := by
  ext q
  by_cases hq : q = p
  · subst q
    rw [Finsupp.single_eq_same, affinePrincipalPrime_multiplicity p a hp ha]
  · rw [Finsupp.single_eq_of_ne hq]
    by_contra hn
    have hs := RegularDivisor.BundleCycles.regularFunctionDivisor_support_subset (Spec (.of R)) ((Scheme.ΓSpecIso (.of R)).inv a)
      (Finsupp.mem_support_iff.mpr hn)
    have hh : Order.coheight q = 1 := by
      by_contra h
      exact hn (Scheme.ord_eq_zero_of_coheight_neq_one h _)
    have hmem : a ∈ q.asIdeal := by
      change ¬q ∈ (Spec (.of R)).basicOpen ((Scheme.ΓSpecIso (.of R)).inv a) at hs
      rw [basicOpen_eq_of_affine] at hs
      exact not_not.mp hs
    have hle : p.asIdeal ≤ q.asIdeal := by
      rw [hp]
      exact (Ideal.span_singleton_le_iff_mem (I := q.asIdeal)).mpr hmem
    let : p.asIdeal.IsPrime := (show PrimeSpectrum R from p).isPrime
    let : q.asIdeal.IsPrime := (show PrimeSpectrum R from q).isPrime
    apply hq
    apply PrimeSpectrum.ext
    apply Eq.symm
    apply Ideal.eq_of_le_of_height_le p.asIdeal hle
    rw [idealHeight_eq_coheight, idealHeight_eq_coheight, hh, affinePrincipalPrime_coheight p a hp ha]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.PrincipalPrimeDivisor.BundleCycles
end ComponentSource_30

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.PrincipalPrimeDivisor"

@[expose] public section ComponentSource_31
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.FieldPointDivisor -/

/-! # Field Point Divisor -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.FieldPointDivisor.BundleCycles

noncomputable section

/-! # LineBundleCycles: every nongeneric point of the affine line over a field is an actual principal divisor -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem polynomialFieldPoint_exists_principal (K : Type) [Field K]
    (p : Spec (.of (Polynomial K))) (hp : p.asIdeal ≠ ⊥) :
    ∃ a : Polynomial K, a ≠ 0 ∧
      RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Spec (.of (Polynomial K)))
        (RegularDivisor.BundleCycles.globalFunctionFieldElement (Spec (.of (Polynomial K))) ((Scheme.ΓSpecIso (.of (Polynomial K))).inv a)) =
          Finsupp.single p 1 := by
  let : p.asIdeal.IsPrime := (show PrimeSpectrum (Polynomial K) from p).isPrime
  let a := Submodule.IsPrincipal.generator p.asIdeal
  have ha : a ≠ 0 := (Submodule.IsPrincipal.prime_generator_of_isPrime p.asIdeal hp).ne_zero
  have hspan : p.asIdeal = Ideal.span {a} := (Ideal.span_singleton_generator p.asIdeal).symm
  refine ⟨a, ha, ?_⟩
  change (RegularDivisor.BundleCycles.regularFunctionDivisor (Spec (.of (Polynomial K))) ((Scheme.ΓSpecIso (.of (Polynomial K))).inv a)).mapRange
    (fun n : ℤ => (n : ℚ)) Int.cast_zero = _
  rw [Affine.PrincipalPrimeDivisor.BundleCycles.affinePrincipalPrime_divisor p a hspan ha, Finsupp.mapRange_single, Int.cast_one]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.FieldPointDivisor.BundleCycles
end ComponentSource_31

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.FieldPointDivisor"

@[expose] public section ComponentSource_32
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizationStalks -/

/-! # Localization Stalks -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizationStalks.BundleCycles

noncomputable section

/-!
# LineBundleCycles: actual stalks and codimensions under arbitrary localization

Localizing a ring and then localizing at a source prime gives the same
local ring as localizing the original ring at its contracted prime.
The comparison is the actual scheme stalk map, and prime heights are
preserved. These comparisons use the same localization construction as
ProjectionFormula's stalk calculation, with the default elaborator settings.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable (M : Submonoid R) [IsLocalization M S]

include M

theorem localizationLocalRingHom_bijective (q : PrimeSpectrum S) :
    Function.Bijective (Localization.localRingHom (q.asIdeal.under R) q.asIdeal
      (algebraMap R S) rfl) := by
  let A := Localization.AtPrime (q.asIdeal.under R)
  let B := Localization.AtPrime q.asIdeal
  let : IsLocalization.AtPrime B (q.asIdeal.under R) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M B q.asIdeal
  let e : A ≃ₐ[R] B := IsLocalization.algEquiv (q.asIdeal.under R).primeCompl A B
  have he : Localization.localRingHom (q.asIdeal.under R) q.asIdeal
      (algebraMap R S) rfl = e.toRingHom := by
    apply IsLocalization.ringHom_ext (q.asIdeal.under R).primeCompl
    ext r
    change Localization.localRingHom _ _ _ rfl (algebraMap R A r) = e (algebraMap R A r)
    rw [Localization.localRingHom_to_map, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
  rw [he]
  exact e.bijective

theorem localizationStalkMap_isIso (q : Spec (CommRingCat.of S)) :
    IsIso ((Spec.map (CommRingCat.ofHom (algebraMap R S))).stalkMap q) := by
  let f : CommRingCat.of R ⟶ CommRingCat.of S := CommRingCat.ofHom (algebraMap R S)
  let q' : PrimeSpectrum (CommRingCat.of S) := q
  let p := q'.comap f.hom
  let j := CommRingCat.ofHom (Localization.localRingHom p.asIdeal q'.asIdeal f.hom rfl)
  have hj : IsIso j :=
    (ConcreteCategory.isIso_iff_bijective j).mpr (localizationLocalRingHom_bijective R S M q)
  let e := (Spec.stalkIso (CommRingCat.of R) p) ≪≫ (@asIso _ _ _ _ j hj) ≪≫
    (Spec.stalkIso (CommRingCat.of S) q').symm
  have he : e.hom = (Spec.map f).stalkMap q := Scheme.localRingHom_comp_stalkIso f q'
  exact (congrArg (fun k => IsIso k) he).mp e.isIso_hom

theorem localization_coheight (q : Spec (CommRingCat.of S)) :
    Order.coheight ((Spec.map (CommRingCat.ofHom (algebraMap R S))) q) = Order.coheight q := by
  rw [← idealHeight_eq_coheight, ← idealHeight_eq_coheight]
  exact IsLocalization.height_under M q.asIdeal

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizationStalks.BundleCycles
end ComponentSource_32

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizationStalks"

@[expose] public section ComponentSource_33
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizationRationalOrder -/

/-! # Localization Rational Order -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizationRationalOrder.BundleCycles

noncomputable section

/-!
# LineBundleCycles: actual rational orders under arbitrary ring localization

The localization morphism identifies the generic fields and the local
rings at corresponding points. Consequently it preserves the existing
integer rational order, including poles. The complete finite principal
divisor restricts by the actual injective map on spectrum points.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.Order

universe u
variable (R S : Type u) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
variable [Algebra R S] (M : Submonoid R) [IsLocalization M S]

include M

theorem localizationAlgebraMap_injective : Function.Injective (algebraMap R S) := by
  apply IsLocalization.injective S (M := M)
  intro m hm
  apply mem_nonZeroDivisors_of_ne_zero
  intro hz
  have hu := IsLocalization.map_units S (⟨m, hm⟩ : M)
  change IsUnit (algebraMap R S m) at hu
  rw [hz, map_zero] at hu
  exact not_isUnit_zero hu

theorem localization_genericPoint :
    (Spec.map (CommRingCat.ofHom (algebraMap R S))) (genericPoint (Spec (.of S))) =
      genericPoint (Spec (.of R)) := by
  rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
  apply PrimeSpectrum.ext
  exact (RingHom.injective_iff_ker_eq_bot (algebraMap R S)).mp (localizationAlgebraMap_injective R S M)

def localizationFunctionFieldMap : (Spec (.of R)).functionField ⟶ (Spec (.of S)).functionField :=
  Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (Spec.map (CommRingCat.ofHom (algebraMap R S))) (localization_genericPoint R S M)

instance localizationFunctionFieldMap_isIso : IsIso (localizationFunctionFieldMap R S M) := by
  let := LocalizationStalks.BundleCycles.localizationStalkMap_isIso R S M (genericPoint (Spec (.of S)))
  unfold localizationFunctionFieldMap Cycles.Functoriality.FunctionFields.Construction.genericFieldMap
  infer_instance

def localizationFunctionFieldIso : (Spec (.of R)).functionField ≅ (Spec (.of S)).functionField :=
  asIso (localizationFunctionFieldMap R S M)

variable [IsNoetherianRing R] [IsNoetherianRing S]

theorem ord_localization (g : (Spec (.of R)).functionField) (x : Spec (.of S)) :
    (Spec (.of S)).ord (localizationFunctionFieldMap R S M g) x =
      (Spec (.of R)).ord g ((Spec.map (CommRingCat.ofHom (algebraMap R S))) x) := by
  let i := Spec.map (CommRingCat.ofHom (algebraMap R S))
  have hc : coheight (i x) = coheight x := LocalizationStalks.BundleCycles.localization_coheight R S M x
  by_cases hx : coheight x = 1
  · let : Ring.KrullDimLE 1 ((Spec (.of S)).presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
    let : Ring.KrullDimLE 1 ((Spec (.of R)).presheaf.stalk (i x)) := krullDimLE_of_coheight_le (hc.trans hx).le
    let : IsIso (i.stalkMap x) := LocalizationStalks.BundleCycles.localizationStalkMap_isIso R S M x
    rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hx, Scheme.ord_eq_ordHom_of_coheight_eq_one (hc.trans hx)]
    exact congrArg (fun z : WithZero (Multiplicative ℤ) => Multiplicative.toAdd (z.unzeroD 1))
      (RationalDivisorRestriction.BundleCycles.ringOrderFrac_equiv (asIso (i.stalkMap x)).commRingCatIsoToRingEquiv
        (localizationFunctionFieldIso R S M).commRingCatIsoToRingEquiv
        (RationalDivisorRestriction.BundleCycles.genericFieldMap_stalk i (localization_genericPoint R S M) x) g)
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one hx,
      Scheme.ord_eq_zero_of_coheight_neq_one (fun h => hx (hc.symm.trans h))]

theorem principalDivisor_localization (g : (Spec (.of R)).functionField) :
    Finsupp.comapDomain (Spec.map (CommRingCat.ofHom (algebraMap R S))) (Ord.BundleCycles.principalDivisor (Spec (.of R)) g)
      (PrimeSpectrum.localization_comap_injective S M).injOn =
      Ord.BundleCycles.principalDivisor (Spec (.of S)) (localizationFunctionFieldMap R S M g) := by
  ext x
  exact (ord_localization R S M g x).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizationRationalOrder.BundleCycles
end ComponentSource_33

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizationRationalOrder"

@[expose] public section ComponentSource_34
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizationPointDivisor -/

/-! # Localization Point Divisor -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizationPointDivisor.BundleCycles

noncomputable section

/-! # LineBundleCycles: actual point-divisor equations on a localization lift to rational functions before localization -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (R S : Type) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [Algebra R S] (M : Submonoid R) [IsLocalization M S]
    [IsNoetherianRing R] [IsNoetherianRing S]

include M

theorem localizationPointDivisor_lift (p : Spec (.of S)) (a : (Spec (.of S)).functionField)
    (ha : a ≠ 0) (hdiv : RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Spec (.of S)) a = Finsupp.single p 1) :
    ∃ g : (Spec (.of R)).functionField, g ≠ 0 ∧ ∀ q : Spec (.of S),
      ((Spec (.of R)).ord g ((Spec.map (CommRingCat.ofHom (algebraMap R S))) q) : ℚ) =
        Finsupp.single p 1 q := by
  let e := LocalizationRationalOrder.BundleCycles.localizationFunctionFieldIso R S M
  let g := e.inv a
  have hg : g ≠ 0 := (map_ne_zero_iff _ e.symm.commRingCatIsoToRingEquiv.injective).mpr ha
  refine ⟨g, hg, ?_⟩
  intro q
  have h : LocalizationRationalOrder.BundleCycles.localizationFunctionFieldMap R S M g = a := Iso.inv_hom_id_apply e a
  have hord := LocalizationRationalOrder.BundleCycles.ord_localization R S M g q
  rw [h] at hord
  exact (congrArg (fun n : ℤ => (n : ℚ)) hord).symm.trans (congrArg (fun z => z q) hdiv)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizationPointDivisor.BundleCycles
end ComponentSource_34

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizationPointDivisor"

@[expose] public section ComponentSource_35
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.GenericFiber -/

/-! # Generic Fiber -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.GenericFiber.BundleCycles

noncomputable section

section

/-! # LineBundleCycles: a generic-fiber point has a genuine rational equation with all generic-fiber coefficients prescribed -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

attribute [local instance] Polynomial.algebra

def polynomialGenericFiberMap : Spec (.of (Polynomial K)) ⟶ Spec (.of (Polynomial R)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (Polynomial R) (Polynomial K)))

variable [IsNoetherianRing R]

theorem polynomialGenericFiberDivisor_exists (p : Spec (.of (Polynomial K))) (hp : p.asIdeal ≠ ⊥) :
    ∃ g : (Spec (.of (Polynomial R))).functionField, g ≠ 0 ∧ ∀ q : Spec (.of (Polynomial K)),
      ((Spec (.of (Polynomial R))).ord g (polynomialGenericFiberMap R K q) : ℚ) =
        Finsupp.single p 1 q := by
  have : IsLocalization ((nonZeroDivisors R).map Polynomial.C) (Polynomial K) :=
    Polynomial.isLocalization (nonZeroDivisors R) K
  obtain ⟨a, ha, hdiv⟩ := FieldPointDivisor.BundleCycles.polynomialFieldPoint_exists_principal K p hp
  have hs : (Scheme.ΓSpecIso (.of (Polynomial K))).inv a ≠ 0 :=
    (map_ne_zero_iff _ (Scheme.ΓSpecIso (.of (Polynomial K))).symm.commRingCatIsoToRingEquiv.injective).mpr ha
  exact LocalizationPointDivisor.BundleCycles.localizationPointDivisor_lift (Polynomial R) (Polynomial K)
    ((nonZeroDivisors R).map Polynomial.C) p _
    (RegularDivisor.BundleCycles.globalFunctionFieldElement_ne_zero _ _ hs) hdiv

end

section

/-! # LineBundleCycles: the actual generic polynomial fiber consists exactly of primes contracting to zero -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

attribute [local instance] Polynomial.algebra

omit [IsDomain R] in
theorem polynomialGenericFiberMap_injective : Function.Injective (polynomialGenericFiberMap R K) := by
  have : IsLocalization ((nonZeroDivisors R).map Polynomial.C) (Polynomial K) :=
    Polynomial.isLocalization (nonZeroDivisors R) K
  exact PrimeSpectrum.localization_comap_injective (Polynomial K) ((nonZeroDivisors R).map Polynomial.C)

theorem polynomialGenericFiberMap_range_iff (p : Spec (.of (Polynomial R))) :
    p ∈ Set.range (polynomialGenericFiberMap R K) ↔ p.asIdeal.comap Polynomial.C = ⊥ := by
  have : IsLocalization ((nonZeroDivisors R).map Polynomial.C) (Polynomial K) :=
    Polynomial.isLocalization (nonZeroDivisors R) K
  change p ∈ Set.range (PrimeSpectrum.comap (algebraMap (Polynomial R) (Polynomial K))) ↔ _
  rw [PrimeSpectrum.localization_comap_range (Polynomial K) ((nonZeroDivisors R).map Polynomial.C)]
  change Disjoint (((nonZeroDivisors R).map Polynomial.C) : Set (Polynomial R)) p.asIdeal ↔ _
  constructor
  · intro h
    apply bot_unique
    intro a ha
    apply Ideal.mem_bot.mpr
    by_contra hn
    exact Set.disjoint_left.mp h
      (Submonoid.mem_map_of_mem Polynomial.C (mem_nonZeroDivisors_iff_ne_zero.mpr hn)) ha
  · intro h
    apply Set.disjoint_left.mpr
    intro a ha hp
    obtain ⟨r, hr, rfl⟩ := ha
    have hz : r = 0 := Ideal.mem_bot.mp (h.le hp)
    exact (mem_nonZeroDivisors_iff_ne_zero.mp hr) hz

omit [IsDomain R] in
theorem polynomialGenericFiberMap_nonzero (p : Spec (.of (Polynomial R)))
    (hp : p.asIdeal ≠ ⊥) (q : Spec (.of (Polynomial K))) (hq : polynomialGenericFiberMap R K q = p) :
    q.asIdeal ≠ ⊥ := by
  intro hqzero
  apply hp
  have h := congrArg (fun x : Spec (.of (Polynomial R)) => x.asIdeal) hq
  change Ideal.comap (algebraMap (Polynomial R) (Polynomial K)) q.asIdeal = p.asIdeal at h
  rw [hqzero] at h
  exact h.symm.trans (Ideal.comap_bot_of_injective _
    (Polynomial.map_injective (algebraMap R K) (IsFractionRing.injective R K)))

end

/-! # LineBundleCycles: a horizontal affine-line divisor differs from an actual principal divisor only over proper base supports -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]

theorem polynomialHorizontalPoint_relation (p : Spec (.of (Polynomial R)))
    (hp : p.asIdeal ≠ ⊥) (hbase : p.asIdeal.comap Polynomial.C = ⊥) :
    ∃ g : (Spec (.of (Polynomial R))).functionField, g ≠ 0 ∧
      RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Spec (.of (Polynomial R))) g p = 1 ∧
      ∀ q ∈ (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Spec (.of (Polynomial R))) g - Finsupp.single p 1).support,
        q.asIdeal.comap Polynomial.C ≠ ⊥ := by
  let K := FractionRing R
  obtain ⟨P, hP⟩ := (polynomialGenericFiberMap_range_iff R K p).mpr hbase
  obtain ⟨g, hg, hdiv⟩ := polynomialGenericFiberDivisor_exists R K P
    (polynomialGenericFiberMap_nonzero R K p hp P hP)
  have hpoint : RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Spec (.of (Polynomial R))) g p = 1 := by
    have h := hdiv P
    rw [hP, Finsupp.single_eq_same] at h
    exact h
  refine ⟨g, hg, hpoint, ?_⟩
  intro q hq hzero
  obtain ⟨Q, hQ⟩ := (polynomialGenericFiberMap_range_iff R K q).mpr hzero
  have hsingle : Finsupp.single p (1 : ℚ) q = Finsupp.single P 1 Q := by
    rw [← hP, ← hQ]
    exact Finsupp.single_apply_left (polynomialGenericFiberMap_injective R K) P Q 1
  have he : RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Spec (.of (Polynomial R))) g q = Finsupp.single p 1 q := by
    exact (congrArg (fun x => ((Spec (.of (Polynomial R))).ord g x : ℚ)) hQ).symm.trans
      ((hdiv Q).trans hsingle.symm)
  exact Finsupp.mem_support_iff.mp hq (by rw [Finsupp.sub_apply, he, sub_self])

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.GenericFiber.BundleCycles
end ComponentSource_35

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.GenericFiber"

@[expose] public section ComponentSource_36
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.HorizontalCharts -/

/-! # Horizontal Charts -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.HorizontalCharts.BundleCycles

noncomputable section

section

/-! # LineBundleCycles: actual polynomial charts for points over the generic point of an integral base -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable (X : Scheme.{0}) [IsIntegral X]

theorem affineLinePolynomialChart_base_generic_iff (U : X.affineOpens) [Nonempty U.1]
    (P : Spec (.of (Polynomial Γ(X, U.1)))) :
    Charts.BundleCycles.affineLineProjection X (Charts.BundleCycles.affineLinePolynomialChart X U P) = genericPoint X ↔
      LineBundles.Polynomial.Projection.BundleCycles.polynomialProjection Γ(X, U.1) P = genericPoint (Spec Γ(X, U.1)) := by
  have hbase := congrArg (fun k => k P) (Charts.BundleCycles.affineLinePolynomialChart_toBase X U)
  have hg := genericPoint_eq_of_isOpenImmersion U.2.fromSpec
  constructor
  · intro h
    apply U.2.fromSpec.isOpenEmbedding.injective
    exact hbase.symm.trans (h.trans hg.symm)
  · intro h
    exact hbase.trans ((congrArg U.2.fromSpec h).trans hg)

theorem affineLineHorizontalPoint_exists_chart (y : Charts.BundleCycles.affineLine X)
    (hy : Charts.BundleCycles.affineLineProjection X y = genericPoint X) (hne : y ≠ genericPoint (Charts.BundleCycles.affineLine X)) :
    ∃ (U : X.affineOpens) (_ : Nonempty U.1) (P : Spec (.of (Polynomial Γ(X, U.1)))),
      Charts.BundleCycles.affineLinePolynomialChart X U P = y ∧ P.asIdeal ≠ ⊥ ∧ P.asIdeal.comap Polynomial.C = ⊥ := by
  obtain ⟨U, P, rfl⟩ := Charts.BundleCycles.affineLinePolynomialChart_covers X y
  have hu : U.2.fromSpec (LineBundles.Polynomial.Projection.BundleCycles.polynomialProjection Γ(X, U.1) P) ∈ (U.1 : Set X) :=
    U.2.range_fromSpec ▸ Set.mem_range_self (LineBundles.Polynomial.Projection.BundleCycles.polynomialProjection Γ(X, U.1) P)
  have : Nonempty U.1 := ⟨⟨_, hu⟩⟩
  refine ⟨U, inferInstance, P, rfl, ?_, ?_⟩
  · intro hp
    apply hne
    have hP : P = genericPoint (Spec (.of (Polynomial Γ(X, U.1)))) := by
      rw [genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext hp
    exact (congrArg (Charts.BundleCycles.affineLinePolynomialChart X U) hP).trans (genericPoint_eq_of_isOpenImmersion _)
  · have hp := (affineLinePolynomialChart_base_generic_iff X U P).mp hy
    rw [genericPoint_eq_bot_of_affine] at hp
    exact congrArg (fun p : Spec Γ(X, U.1) => p.asIdeal) hp

end

/-! # LineBundleCycles: actual horizontal point-divisor relations on the relative affine line over an integral scheme -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable (X : Scheme.{0}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]

theorem affineLineHorizontalPoint_relation (y : Charts.BundleCycles.affineLine X)
    (hy : Charts.BundleCycles.affineLineProjection X y = genericPoint X) (hne : y ≠ genericPoint (Charts.BundleCycles.affineLine X)) :
    ∃ g : (Charts.BundleCycles.affineLine X).functionField, g ≠ 0 ∧
      ∀ q ∈ (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Charts.BundleCycles.affineLine X) g - Finsupp.single y 1).support,
        Charts.BundleCycles.affineLineProjection X q ≠ genericPoint X := by
  obtain ⟨U, hU, P, rfl, hP, hbase⟩ := affineLineHorizontalPoint_exists_chart X y hy hne
  let := hU
  obtain ⟨a, ha, _, hvertical⟩ := LineBundles.Polynomial.GenericFiber.BundleCycles.polynomialHorizontalPoint_relation Γ(X, U.1) P hP hbase
  let j := Charts.BundleCycles.affineLinePolynomialChart X U
  let e := RationalDivisorRestriction.BundleCycles.openFunctionFieldIso j
  let g := e.inv a
  have hg : g ≠ 0 := (map_ne_zero_iff _ e.symm.commRingCatIsoToRingEquiv.injective).mpr ha
  have hfield : RationalDivisorRestriction.BundleCycles.openFunctionFieldMap j g = a := Iso.inv_hom_id_apply e a
  refine ⟨g, hg, ?_⟩
  intro q hq hgen
  have hmem : q ∈ Set.range j := by
    rw [Charts.BundleCycles.affineLinePolynomialChart_range]
    change Charts.BundleCycles.affineLineProjection X q ∈ (U.1 : Set X)
    rw [hgen]
    exact ((genericPoint_spec X).mem_open_set_iff U.1.isOpen).mpr (by simpa using hU)
  obtain ⟨Q, rfl⟩ := hmem
  have hbQ := (affineLinePolynomialChart_base_generic_iff X U Q).mp hgen
  rw [genericPoint_eq_bot_of_affine] at hbQ
  have hbaseQ : Q.asIdeal.comap Polynomial.C = ⊥ := congrArg (fun p : Spec Γ(X, U.1) => p.asIdeal) hbQ
  apply hvertical Q _ hbaseQ
  apply Finsupp.mem_support_iff.mpr
  intro hz
  apply Finsupp.mem_support_iff.mp hq
  have hord := RationalDivisorRestriction.BundleCycles.ord_openImmersion j g Q
  rw [hfield] at hord
  have hs : Finsupp.single (j P) (1 : ℚ) (j Q) = Finsupp.single P 1 Q :=
    Finsupp.single_apply_left j.isOpenEmbedding.injective P Q 1
  change (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Charts.BundleCycles.affineLine X) g - Finsupp.single (j P) 1 : Charts.BundleCycles.affineLine X →₀ ℚ) (j Q) = 0
  rw [Finsupp.sub_apply, RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor_apply, ← hord, hs]
  exact hz

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.HorizontalCharts.BundleCycles
end ComponentSource_36

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.HorizontalCharts"

@[expose] public section ComponentSource_37
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.LineVerticalDivisors -/

/-! # Line Vertical Divisors -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.LineVerticalDivisors.BundleCycles

noncomputable section

/-! # LineBundleCycles: every vertical codimension-one affine-line point is the actual generic point of its fiber -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable (X : Scheme.{0}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]

theorem affineLineVerticalHeightOne_generic (y : Charts.BundleCycles.affineLine X) (hy : Order.coheight y = 1)
    (hbase : Charts.BundleCycles.affineLineProjection X y ≠ genericPoint X) :
    Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X) (Charts.BundleCycles.affineLineProjection X y) = y := by
  obtain ⟨U, P, rfl⟩ := Charts.BundleCycles.affineLinePolynomialChart_covers X y
  have hu : U.2.fromSpec (LineBundles.Polynomial.Projection.BundleCycles.polynomialProjection Γ(X, U.1) P) ∈ (U.1 : Set X) :=
    U.2.range_fromSpec ▸ Set.mem_range_self (LineBundles.Polynomial.Projection.BundleCycles.polynomialProjection Γ(X, U.1) P)
  have : Nonempty U.1 := ⟨⟨_, hu⟩⟩
  have hPheight : P.asIdeal.height = 1 := by
    rw [idealHeight_eq_coheight]
    exact (coheight_eq_of_isOpenImmersion (Charts.BundleCycles.affineLinePolynomialChart X U)).symm.trans hy
  have hPbase : P.asIdeal.comap Polynomial.C ≠ ⊥ := by
    intro h
    apply hbase
    apply (HorizontalCharts.BundleCycles.affineLinePolynomialChart_base_generic_iff X U P).mpr
    rw [genericPoint_eq_bot_of_affine]
    exact PrimeSpectrum.ext h
  let : P.asIdeal.IsPrime := (show PrimeSpectrum (Polynomial Γ(X, U.1)) from P).isPrime
  have hP : LineBundles.Polynomial.Projection.BundleCycles.polynomialPrimePoint Γ(X, U.1) (LineBundles.Polynomial.Projection.BundleCycles.polynomialProjection Γ(X, U.1) P) = P :=
    PrimeSpectrum.ext (LineBundles.Polynomial.PrimeExtension.BundleCycles.polynomialHeightOne_isExtended P.asIdeal hPheight hPbase)
  have hb := congrArg (fun k => k P) (Charts.BundleCycles.affineLinePolynomialChart_toBase X U)
  exact (congrArg (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X)) hb).trans
    ((GenericPoint.BundleCycles.affineLineFiberGenericPoint_on_chart X U (LineBundles.Polynomial.Projection.BundleCycles.polynomialProjection Γ(X, U.1) P)).trans
      (congrArg (Charts.BundleCycles.affineLinePolynomialChart X U) hP))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.LineVerticalDivisors.BundleCycles
end ComponentSource_37

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.LineVerticalDivisors"

@[expose] public section ComponentSource_38
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.HorizontalCycle -/

/-! # Horizontal Cycle -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.HorizontalCycle.BundleCycles

noncomputable section

/-! # LineBundleCycles: actual horizontal affine-line points differ from extended finite cycles by genuine principal divisors -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (X : Scheme.{0}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]

theorem affineLineHorizontalPoint_residual_extended (y : Charts.BundleCycles.affineLine X)
    (hy : Charts.BundleCycles.affineLineProjection X y = genericPoint X) (hne : y ≠ genericPoint (Charts.BundleCycles.affineLine X)) :
    ∃ g : (Charts.BundleCycles.affineLine X).functionField, g ≠ 0 ∧
      ((RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Charts.BundleCycles.affineLine X) g - Finsupp.single y 1).support : Set (Charts.BundleCycles.affineLine X)) ⊆
        Set.range (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X)) := by
  obtain ⟨g, hg, hvertical⟩ := HorizontalCharts.BundleCycles.affineLineHorizontalPoint_relation X y hy hne
  refine ⟨g, hg, ?_⟩
  intro q hq
  have hbaseq := hvertical q hq
  have hqy : q ≠ y := fun h => hbaseq (h ▸ hy)
  have hnonzero : RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Charts.BundleCycles.affineLine X) g q ≠ 0 := by
    intro hz
    exact Finsupp.mem_support_iff.mp hq (by rw [Finsupp.sub_apply, hz, Finsupp.single_eq_of_ne hqy, sub_self])
  have hh : Order.coheight q = 1 := by
    by_contra h
    apply hnonzero
    rw [RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor_apply, Scheme.ord_eq_zero_of_coheight_neq_one h, Int.cast_zero]
  exact ⟨Charts.BundleCycles.affineLineProjection X q, LineVerticalDivisors.BundleCycles.affineLineVerticalHeightOne_generic X q hh hbaseq⟩

theorem affineLineHorizontalPoint_cycle_relation (y : Charts.BundleCycles.affineLine X)
    (hy : Charts.BundleCycles.affineLineProjection X y = genericPoint X) (hne : y ≠ genericPoint (Charts.BundleCycles.affineLine X)) :
    ∃ g : (Charts.BundleCycles.affineLine X).functionField, g ≠ 0 ∧ ∃ z : X →₀ ℚ,
      Finsupp.single y 1 + Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension (Charts.BundleCycles.affineLineProjection X) z =
        RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Charts.BundleCycles.affineLine X) g := by
  obtain ⟨g, hg, hs⟩ := affineLineHorizontalPoint_residual_extended X y hy hne
  let d := RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Charts.BundleCycles.affineLine X) g - Finsupp.single y 1
  let z := Finsupp.comapDomain (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X)) d
    (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint_injective (Charts.BundleCycles.affineLineProjection X)).injOn
  have he : Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension (Charts.BundleCycles.affineLineProjection X) z = d :=
    Finsupp.mapDomain_comapDomain _ (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint_injective (Charts.BundleCycles.affineLineProjection X)) d hs
  refine ⟨g, hg, z, ?_⟩
  rw [he]
  change Finsupp.single y 1 + (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Charts.BundleCycles.affineLine X) g - Finsupp.single y 1) = _
  rw [add_comm, sub_add_cancel]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.HorizontalCycle.BundleCycles
end ComponentSource_38

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.HorizontalCycle"

@[expose] public section ComponentSource_39
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.PointRelation -/

/-! # Point Relation -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.PointRelation.BundleCycles

noncomputable section

/-! # LineBundleCycles: every nonextended affine-line point has an actual principal-divisor relation with an extended base cycle -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable (X : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X]

theorem affineLineNonextendedPoint_cycle_relation (y : Charts.BundleCycles.affineLine X)
    (hy : y ∉ Set.range (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X))) :
    ∃ W : IrreducibleCloseds (Charts.BundleCycles.affineLine X), ∃ g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField,
      g ≠ 0 ∧ ∃ z : X →₀ ℚ,
      Finsupp.single y 1 + Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension (Charts.BundleCycles.affineLineProjection X) z = Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g := by
  let V := irreducibleSetEquivPoints.symm (Charts.BundleCycles.affineLineProjection X y)
  have hV : irreducibleSetEquivPoints V = Charts.BundleCycles.affineLineProjection X y := irreducibleSetEquivPoints.apply_symm_apply _
  obtain ⟨q, hjq, hqbase⟩ := PointSupport.BundleCycles.affineLinePoint_liftSupport X V y hV.symm
  let A := CycleClass.Geometric.GenericPoint.reducedSupportScheme V
  let j := Support.BundleCycles.affineLineSupportMap X V
  have hq : q ≠ genericPoint (Charts.BundleCycles.affineLine A) := by
    intro h
    apply hy
    refine ⟨Charts.BundleCycles.affineLineProjection X y, ?_⟩
    exact (congrArg (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X)) hV).symm.trans
      ((PointSupport.BundleCycles.affineLineSupportMap_genericPoint X V).symm.trans ((congrArg j h).symm.trans hjq))
  obtain ⟨a, ha, z, hz⟩ := HorizontalCycle.BundleCycles.affineLineHorizontalPoint_cycle_relation A q hqbase hq
  let W := Support.BundleCycles.affineLineExtendedSupport X V
  let g := Integral.ClosedImage.BundleCycles.integralClosedImageFunction j a
  have hg : g ≠ 0 := Integral.ClosedImage.BundleCycles.integralClosedImageFunction_ne_zero j a ha
  refine ⟨W, g, hg, Finsupp.mapDomain (CycleClass.Geometric.GenericPoint.reducedSupportι V) z, ?_⟩
  have h := congrArg (Finsupp.mapDomain j) hz
  rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single, hjq,
    Integral.ClosedImage.BundleCycles.integralClosedImage_principalDivisor] at h
  have hn := Integral.FiberOpen.BundleCycles.integralFiberCycleExtension_naturality (Charts.BundleCycles.affineLineProjection X) (Charts.BundleCycles.affineLineProjection A)
    (CycleClass.Geometric.GenericPoint.reducedSupportι V) j (Support.BundleCycles.affineLineSupport_isPullback X V) z
  exact (congrArg (fun b => Finsupp.single y 1 + b) hn).symm.trans h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.PointRelation.BundleCycles
end ComponentSource_39

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.PointRelation"

@[expose] public section ComponentSource_40
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.Dimension -/

/-! # Dimension -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.Dimension.BundleCycles

noncomputable section

/-! # LineBundleCycles: actual polynomial charts raise the support transcendence dimension by one -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

universe u

theorem polynomial_trdeg_toNat (k R : Type u) [Field k] [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.FiniteType k R] :
    (Algebra.trdeg k (Polynomial R)).toNat = (Algebra.trdeg k R).toNat + 1 := by
  have ht := trdeg_add_eq k R (A := Polynomial R)
  have hfin : Algebra.trdeg k R < Cardinal.aleph0 := trdeg_lt_aleph0_of_finiteType
  rw [Polynomial.trdeg_of_isDomain] at ht
  rw [← ht, Cardinal.toNat_add hfin (by simp)]
  simp

/-- An actual polynomial chart determines the global dimension increase. -/
theorem polynomial_dimension_of_chart (k : Type u) [Field k]
    {R : Type u} [CommRing R] [IsDomain R]
    {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    (a : Spec (CommRingCat.of R) ⟶ A) [IsOpenImmersion a]
    (b : Spec (CommRingCat.of (Polynomial R)) ⟶ B) [IsOpenImmersion b]
    (g : B ⟶ A)
    (h : b ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R (Polynomial R))) ≫ a)
    (f : A ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (g ≫ f) = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f + 1 := by
  let α : CommRingCat.of k ⟶ CommRingCat.of R := Spec.preimage (a ≫ f)
  let : Algebra k R := α.hom.toAlgebra
  have hα : Spec.map α = a ≫ f := Spec.map_preimage _
  have hfα : LocallyOfFiniteType (Spec.map α) :=
    (congrArg (fun q => LocallyOfFiniteType q) hα).mpr inferInstance
  have : Algebra.FiniteType k R :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hfα
  let c : CommRingCat.of R ⟶ CommRingCat.of (Polynomial R) :=
    CommRingCat.ofHom (algebraMap R (Polynomial R))
  have hαc : α ≫ c = CommRingCat.ofHom (algebraMap k (Polynomial R)) := rfl
  have hspec : Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial R))) =
      Spec.map c ≫ (a ≫ f) :=
    (congrArg Spec.map hαc.symm).trans
      ((Spec.map_comp α c).trans (congrArg (fun q => Spec.map c ≫ q) hα))
  have hb : b ≫ (g ≫ f) = Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial R))) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q ≫ f) h).trans ((Category.assoc _ _ _).trans hspec.symm))
  have haDim : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f = (Algebra.trdeg k R).toNat :=
    (Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion a f).symm.trans
      ((congrArg (fun q => Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension q) hα.symm).trans
        (Affine.DimensionBridge.BundleCycles.schemeTranscendenceDimension_spec_algebra k R))
  exact (Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion b (g ≫ f)).symm.trans
    ((congrArg (fun q => Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension q) hb).trans
    ((Affine.DimensionBridge.BundleCycles.schemeTranscendenceDimension_spec_algebra k (Polynomial R)).trans
    ((polynomial_trdeg_toNat k R).trans (congrArg (fun n => n + 1) haDim.symm))))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.Dimension.BundleCycles
end ComponentSource_40

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.Dimension"

@[expose] public section ComponentSource_41
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.CycleGrading -/

/-! # Cycle Grading -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.CycleGrading.BundleCycles

noncomputable section

section

/-! # LineBundleCycles: the actual relative affine line increases every integral support dimension by one -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {k : Type} [Field k] (X : Scheme.{0})

theorem affineLine_dimension [IsIntegral X] (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (Charts.BundleCycles.affineLineProjection X ≫ f) = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f + 1 := by
  let x : X := Classical.choice inferInstance
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top x)
  let V : X.affineOpens := ⟨U, hU⟩
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  have : IsDomain Γ(X, U) := inferInstance
  have hbase : Charts.BundleCycles.affineLinePolynomialChart X V ≫ Charts.BundleCycles.affineLineProjection X =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Polynomial Γ(X, U)))) ≫ hU.fromSpec :=
    Charts.BundleCycles.affineLinePolynomialChart_toBase X V
  exact @LineBundles.Polynomial.Dimension.BundleCycles.polynomial_dimension_of_chart k _ Γ(X, U) _ _ X (Charts.BundleCycles.affineLine X) _ _
    hU.fromSpec (IsAffineOpen.isOpenImmersion_fromSpec hU)
    (Charts.BundleCycles.affineLinePolynomialChart X V) (Charts.BundleCycles.affineLinePolynomialChart_isOpenImmersion X V)
    (Charts.BundleCycles.affineLineProjection X) hbase f inferInstance

theorem affineLineExtendedSupport_dimension (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (W : IrreducibleCloseds X) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Support.BundleCycles.affineLineExtendedSupport X W) (Charts.BundleCycles.affineLineProjection X ≫ f) =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f + 1 := by
  have hc : Support.BundleCycles.affineLineSupportMap X W ≫ (Charts.BundleCycles.affineLineProjection X ≫ f) =
      Charts.BundleCycles.affineLineProjection (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) ≫ (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ f) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q ≫ f) (Support.BundleCycles.affineLineSupport_isPullback X W).w.symm).trans (Category.assoc _ _ _))
  exact (CycleClass.Geometric.StratumClosure.schemeTranscendenceDimension_eq_imageClosure (Support.BundleCycles.affineLineSupportMap X W)
    (Charts.BundleCycles.affineLineProjection X ≫ f)).symm.trans
      ((congrArg (fun q => Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension q) hc).trans
        (affineLine_dimension (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ f)))

end

/-! # LineBundleCycles: actual dimension-graded cycle pullback to the relative affine line -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable (X : Scheme.{0}) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

theorem affineLineFiberGenericPoint_dimension (x : X) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X) x))
        (Charts.BundleCycles.affineLineProjection X ≫ f) =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f + 1 := by
  have he := Support.BundleCycles.affineLineExtendedSupport_eq_pointClosure X (irreducibleSetEquivPoints.symm x)
  rw [irreducibleSetEquivPoints.apply_symm_apply] at he
  exact (congrArg (fun W => Foundations.Scheme.SupportDimension.supportTranscendenceDimension W (Charts.BundleCycles.affineLineProjection X ≫ f)) he).symm.trans
    (affineLineExtendedSupport_dimension X f _)

def affineLineDimensionPointMap (d : ℕ) :
    Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d → Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1) :=
  fun x => ⟨Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X) x.1,
    (affineLineFiberGenericPoint_dimension X f x.1).trans (congrArg (fun n => n + 1) x.2)⟩

def affineLineGradedCycleExtension (d : ℕ) :
    (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) →ₗ[ℚ]
      (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1) →₀ ℚ) :=
  Finsupp.lmapDomain ℚ ℚ (affineLineDimensionPointMap X f d)

theorem affineLineGradedCycleExtension_forget (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :
    Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1)
        (affineLineGradedCycleExtension X f d z) =
      Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension (Charts.BundleCycles.affineLineProjection X) (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d z) := by
  change Finsupp.mapDomain (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1))
      (Finsupp.mapDomain (affineLineDimensionPointMap X f d) z) =
    Finsupp.mapDomain (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X)) (Finsupp.mapDomain (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding f d) z)
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.CycleGrading.BundleCycles
end ComponentSource_41

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.CycleGrading"

@[expose] public section ComponentSource_42
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.RelationGrading -/

/-! # Relation Grading -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.RelationGrading.BundleCycles

noncomputable section

/-! # LineBundleCycles: actual horizontal point relations preserve the exact Chow dimension grade -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable (X : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

theorem affineLineNonextendedPoint_graded_relation (d : ℕ)
    (y : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1))
    (hy : y.val ∉ Set.range (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X))) :
    ∃ (W : IrreducibleCloseds (Charts.BundleCycles.affineLine X)) (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField),
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension W (Charts.BundleCycles.affineLineProjection X ≫ f) = (d + 1) + 1 ∧ g ≠ 0 ∧
      ∃ z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ,
        Finsupp.single y 1 + CycleGrading.BundleCycles.affineLineGradedCycleExtension X f d z =
          Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1) W g := by
  obtain ⟨W, g, hg, w, hrel⟩ := PointRelation.BundleCycles.affineLineNonextendedPoint_cycle_relation X y.val hy
  have hcoeff : Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g y.val = 1 := by
    have h := congrArg (fun z : Charts.BundleCycles.affineLine X →₀ ℚ => z y.val) hrel
    change Finsupp.single y.val (1 : ℚ) y.val +
      Finsupp.mapDomain (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X)) w y.val = _ at h
    rw [Finsupp.single_eq_same, Finsupp.mapDomain_of_notMem_range _ _ hy, add_zero] at h
    exact h.symm
  have hW : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W (Charts.BundleCycles.affineLineProjection X ≫ f) = (d + 1) + 1 := by
    have h := Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor_dimension (Charts.BundleCycles.affineLineProjection X ≫ f) W g y.val
      (hcoeff ▸ one_ne_zero)
    exact h.symm.trans (congrArg (fun n => n + 1) y.property)
  have hs : (w.support : Set X) ⊆ Set.range (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding f d) := by
    intro x hx
    have hxzero : w x ≠ 0 := Finsupp.mem_support_iff.mp hx
    have hneq : Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X) x ≠ y.val := fun h => hy ⟨x, h⟩
    have h := congrArg (fun z : Charts.BundleCycles.affineLine X →₀ ℚ => z (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X) x)) hrel
    change Finsupp.single y.val (1 : ℚ) (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X) x) +
      Finsupp.mapDomain (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X)) w
        (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X) x) = _ at h
    rw [Finsupp.single_eq_of_ne hneq, Finsupp.mapDomain_apply_of_injective (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint_injective (Charts.BundleCycles.affineLineProjection X)), zero_add] at h
    have hn : Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X) x) ≠ 0 :=
      fun hz => hxzero (h.trans hz)
    have hd := Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor_dimension (Charts.BundleCycles.affineLineProjection X ≫ f) W g _ hn
    rw [CycleGrading.BundleCycles.affineLineFiberGenericPoint_dimension, hW] at hd
    refine ⟨⟨x, ?_⟩, rfl⟩
    omega
  let z := Finsupp.comapDomain (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding f d) w (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding f d).injective.injOn
  have hz : Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d z = w :=
    Finsupp.mapDomain_comapDomain _ (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding f d).injective w hs
  refine ⟨W, g, hW, hg, z, ?_⟩
  apply Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion_injective (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1)
  rw [map_add, CycleGrading.BundleCycles.affineLineGradedCycleExtension_forget, hz,
    Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor_push (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1) W hW]
  have hi : Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1) (Finsupp.single y 1) =
      Finsupp.single y.val 1 := Finsupp.mapDomain_single
  rw [hi]
  exact hrel

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.RelationGrading.BundleCycles
end ComponentSource_42

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.RelationGrading"

@[expose] public section ComponentSource_43
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.FlatExtendedPrimeOrder -/

/-! # Flat Extended Prime Order -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.FlatExtendedPrimeOrder.BundleCycles

noncomputable section

/-!
# LineBundleCycles: local orders at extended primes of a flat algebra
-/

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime]
    (hp : p = Ideal.comap (algebraMap R S) P)

theorem extendedPrimeLocalMap_maximalIdeal (hP : p.map (algebraMap R S) = P) :
    (IsLocalRing.maximalIdeal (Localization.AtPrime p)).map
      (Localization.localRingHom p P (algebraMap R S) hp) =
        IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
  have hc : (Localization.localRingHom p P (algebraMap R S) hp).comp
      (algebraMap R (Localization.AtPrime p)) =
        (algebraMap S (Localization.AtPrime P)).comp (algebraMap R S) := by
    ext a
    exact Localization.localRingHom_to_map p P (algebraMap R S) hp a
  rw [← Localization.AtPrime.map_eq_maximalIdeal (I := p), Ideal.map_map, hc,
    ← Ideal.map_map, hP, Localization.AtPrime.map_eq_maximalIdeal]

theorem extendedPrimeLocalMap_flat [Module.Flat R S] :
    (Localization.localRingHom p P (algebraMap R S) hp).Flat :=
  (RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat R S)).localRingHom P p hp

theorem extendedPrimeLocalMap_ord [Module.Flat R S]
    (hP : p.map (algebraMap R S) = P) (a : Localization.AtPrime p) :
    Ring.ord (Localization.AtPrime P)
      (Localization.localRingHom p P (algebraMap R S) hp a) =
        Ring.ord (Localization.AtPrime p) a := by
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime P) :=
    (Localization.localRingHom p P (algebraMap R S) hp).toAlgebra
  let : Module.Flat (Localization.AtPrime p) (Localization.AtPrime P) :=
    extendedPrimeLocalMap_flat p P hp
  let : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime P)) :=
    inferInstanceAs (IsLocalHom (Localization.localRingHom p P (algebraMap R S) hp))
  exact FlatOrderEq.BundleCycles.FlatOrder.ord_eq (Localization.AtPrime p) (Localization.AtPrime P)
    (extendedPrimeLocalMap_maximalIdeal p P hp hP) a

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.FlatExtendedPrimeOrder.BundleCycles
end ComponentSource_43

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.FlatExtendedPrimeOrder"

@[expose] public section ComponentSource_44
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.FlatMorphismOrder -/

/-! # Flat Morphism Order -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.FlatMorphismOrder.BundleCycles

noncomputable section

/-!
# LineBundleCycles: native scheme orders at a reduced generic point of a flat fiber
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.Order

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]

omit [IsLocallyNoetherian X] [IsLocallyNoetherian Y] in
theorem genericMorphism_stalkMap_injective (f : X ⟶ Y)
    (hη : f (genericPoint X) = genericPoint Y) (x : X) : Function.Injective (f.stalkMap x) := by
  intro a b hab
  apply IsFractionRing.injective (Y.presheaf.stalk (f x)) Y.functionField
  apply (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.injective
  rw [RationalDivisorRestriction.BundleCycles.genericFieldMap_stalk f hη x a, RationalDivisorRestriction.BundleCycles.genericFieldMap_stalk f hη x b]
  exact congrArg (algebraMap (X.presheaf.stalk x) X.functionField) hab

theorem ord_flat_stalk_eq (f : X ⟶ Y) [Flat f]
    (hη : f (genericPoint X) = genericPoint Y) (x : X)
    (hx : coheight x = 1) (hy : coheight (f x) = 1)
    (hmax : (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (g : Y.functionField) :
    X.ord (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη g) x = Y.ord g (f x) := by
  let R := Y.presheaf.stalk (f x)
  let S := X.presheaf.stalk x
  let : Algebra R S := (f.stalkMap x).hom.toAlgebra
  let : IsLocalHom (algebraMap R S) := inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  let : Module.Flat R S := Flat.stalkMap f x
  let : Ring.KrullDimLE 1 R := krullDimLE_of_coheight_le hy.le
  let : Ring.KrullDimLE 1 S := krullDimLE_of_coheight_le hx.le
  rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hx, Scheme.ord_eq_ordHom_of_coheight_eq_one hy]
  exact congrArg WithZero.log (FlatOrderEq.BundleCycles.FlatOrder.ordFrac_eq R S hmax (genericMorphism_stalkMap_injective f hη x)
    (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom (RationalDivisorRestriction.BundleCycles.genericFieldMap_stalk f hη x) g)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.FlatMorphismOrder.BundleCycles
end ComponentSource_44

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.FlatMorphismOrder"

@[expose] public section ComponentSource_45
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.ExtendedPrimeStalk -/

/-! # Extended Prime Stalk -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.ExtendedPrimeStalk.BundleCycles

noncomputable section

/-! # LineBundleCycles: the actual affine stalk map at an extended prime -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

theorem affineExtendedPrime_stalk_maximalIdeal (P : Spec (CommRingCat.of S))
    (hP : (P.asIdeal.under R).map (algebraMap R S) = P.asIdeal) :
    (IsLocalRing.maximalIdeal ((Spec (CommRingCat.of R)).presheaf.stalk
      ((Spec.map (CommRingCat.ofHom (algebraMap R S))) P))).map
        ((Spec.map (CommRingCat.ofHom (algebraMap R S))).stalkMap P).hom =
          IsLocalRing.maximalIdeal ((Spec (CommRingCat.of S)).presheaf.stalk P) := by
  let : P.asIdeal.IsPrime := (show PrimeSpectrum S from P).isPrime
  let f : CommRingCat.of R ⟶ CommRingCat.of S := CommRingCat.ofHom (algebraMap R S)
  let p : Spec (CommRingCat.of R) := (Spec.map f) P
  let : p.asIdeal.IsPrime := (show PrimeSpectrum R from p).isPrime
  let eR := Spec.stalkIso (CommRingCat.of R) p
  let eS := Spec.stalkIso (CommRingCat.of S) P
  let l := Localization.localRingHom p.asIdeal P.asIdeal f.hom rfl
  have hlocal : (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)).map l =
      IsLocalRing.maximalIdeal (Localization.AtPrime P.asIdeal) :=
    FlatExtendedPrimeOrder.BundleCycles.extendedPrimeLocalMap_maximalIdeal p.asIdeal P.asIdeal rfl hP
  have he := congrArg CommRingCat.Hom.hom (Scheme.localRingHom_comp_stalkIso f P)
  apply (congrArg (fun t : ((Spec (CommRingCat.of R)).presheaf.stalk p) →+*
    ((Spec (CommRingCat.of S)).presheaf.stalk P) =>
      (IsLocalRing.maximalIdeal ((Spec (CommRingCat.of R)).presheaf.stalk p)).map t) he).symm.trans
  change (IsLocalRing.maximalIdeal ((Spec (CommRingCat.of R)).presheaf.stalk p)).map
    (eS.inv.hom.comp (l.comp eR.hom.hom)) = _
  rw [← Ideal.map_map, ← Ideal.map_map]
  have hR : (IsLocalRing.maximalIdeal ((Spec (CommRingCat.of R)).presheaf.stalk
      ((Spec.map f) P))).map eR.hom.hom = IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal) :=
    IsLocalRing.map_ringEquiv_maximalIdeal eR.commRingCatIsoToRingEquiv
  rw [hR, hlocal]
  exact IsLocalRing.map_ringEquiv_maximalIdeal eS.symm.commRingCatIsoToRingEquiv

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.ExtendedPrimeStalk.BundleCycles
end ComponentSource_45

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.ExtendedPrimeStalk"


set_option pp.explicit false
set_option pp.proofs false
set_option pp.deepTerms false
set_option maxHeartbeats 0

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let opts ← getOptions
  if true && env.header.trustLevel != 0 then
    throwError "The final environment has nonzero kernel trust level"
  if Lean.debug.skipKernelTC.get opts then
    throwError "The final environment disabled kernel type checking"
  if Lean.Elab.inServer.get opts then
    throwError "The final environment unexpectedly uses server mode"
  let required : Array (Name × String) := #[
    (`OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.ExtendedPrimeStalk.BundleCycles.affineExtendedPrime_stalk_maximalIdeal, "theorem")
  ]
  let localNames := env.checked.get.constants.foldStage2 (fun acc name _ => acc.push name) (#[] : Array Name)
  if localNames.isEmpty then throwError "Empty authored declaration audit"
  let mut names := localNames
  for (name, _) in required do
    unless names.contains name do names := names.push name
  let mut rows : Array Json := #[]
  for name in names do
    let some info := env.checked.get.find? name | throwError "Missing checked declaration {name}"
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .quotInfo _ => "quotient primitive"
    if kind == "axiom" then throwError "Authored axiom {name}"
    let value := info.value? (allowOpaque := true)
    if kind == "theorem" || kind == "definition" || kind == "opaque" then
      unless value.isSome do throwError "No actual body {name}"
    for (requiredName, expectedKind) in required do
      if name == requiredName && kind != expectedKind then
        throwError "Endpoint kind mismatch {name}: expected {expectedKind}, got {kind}"
    let axioms ← collectAxioms name
    for ax in axioms do
      if ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound then
        throwError "Unapproved transitive axiom {name}: {ax}"
    let mut fields := [("name", toJson name.toString), ("kind", toJson kind),
      ("actual_body_available", toJson value.isSome),
      ("universe_parameters", toJson (info.levelParams.map Name.toString)),
      ("type_dependencies", toJson (info.type.getUsedConstants.map Name.toString)),
      ("body_dependencies", toJson ((value.map Expr.getUsedConstants).getD #[] |>.map Name.toString)),
      ("transitive_axioms", toJson (axioms.map Name.toString))]
    if required.any (fun e => e.1 == name) then
      let typeText ← liftTermElabM <| return (← Meta.ppExpr info.type).pretty
      fields := fields ++ [("readable_type", toJson typeText)]
    rows := rows.push (Json.mkObj fields)
  IO.FS.createDirAll ".lake/reports"
  let path := ".lake/reports/" ++ (← getEnv).mainModule.toString ++ ".json"
  IO.FS.writeFile path (Json.mkObj [("accepted", toJson true),
    ("nonce", toJson "c7a7816dd006b5c2ed2786dffe2befda"), ("declaration_count", toJson localNames.size),
    ("kernel_trust_level", toJson env.header.trustLevel.toNat),
    ("kernel_type_checking_enabled", toJson (!Lean.debug.skipKernelTC.get opts)),
    ("server_mode", toJson (Lean.Elab.inServer.get opts)),
    ("required_endpoint_count", toJson required.size),
    ("all_new_declarations_read_from_checked_environment", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo "LITERAL_COMPONENT_KERNEL_AUDIT_COMPLETE:c7a7816dd006b5c2ed2786dffe2befda"
