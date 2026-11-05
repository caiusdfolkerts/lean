module

public import paper_verification.oai_chow001_run2
import all paper_verification.oai_chow001_run2
public import paper_verification.oai_chow003_run1
import all paper_verification.oai_chow003_run1
public import Mathlib.AlgebraicGeometry.AffineSpace
import all Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.Logic.Equiv.Fin.Basic
import all Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Tactic.IrreducibleDef
import all Mathlib.Tactic.IrreducibleDef
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.PrettyPrinter

set_option Elab.async false

@[expose] public section ComponentSource_0
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.RationalUnitRepresentative -/

/-!
Extracted from openai/math commit 4eaee87548250b2682affda7d05d947c05554bae,
Divisors/LineBundles/RationalBoundary.lean, under Apache 2.0.
Modification: separate the unchanged algebraic rational-unit representative
and germ lemmas from the later analytic boundary construction.
-/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.RationalBoundary.BundleCycles
noncomputable section
open _root_.AlgebraicGeometry _root_.CategoryTheory

/-- Actual unit data representing a rational function on a nonempty open. -/
structure RationalUnitRepresentative (X : Scheme) [IsIntegral X]
    (f : X.functionField) where
  domain : X.Opens
  nonempty_domain : Nonempty domain
  unit : Γ(X, domain)ˣ
  represents : letI := nonempty_domain
    X.germToFunctionField domain (unit : Γ(X, domain)) = f

/-- Existence is supplied by the function-field construction, with no
cohomological hypotheses. -/
def rationalUnitRepresentative (X : Scheme) [IsIntegral X]
    (f : X.functionField) (hf : f ≠ 0) : RationalUnitRepresentative X f := by
  apply Classical.choice
  obtain ⟨U, _, a, hU, hfa, ha⟩ := exists_isUnit_germ_eq X f hf
  refine ⟨⟨U, hU, ha.unit, ?_⟩⟩
  simpa only [ha.unit_spec] using hfa

namespace RationalUnitRepresentative

variable {X : Scheme} [IsIntegral X] {f : X.functionField}

instance (D : RationalUnitRepresentative X f) : Nonempty D.domain := D.nonempty_domain

/-- The divisor coefficients vanish on every such unit-representing open. -/
theorem ord_eq_zero (D : RationalUnitRepresentative X f)
    [IsLocallyNoetherian X] (x : X) (hx : x ∈ D.domain) : X.ord f x = 0 := by
  rw [← D.represents]
  exact Scheme.ord_of_isUnit D.unit.isUnit hx

/-- The finite algebraic divisor is supported outside the unit domain used
to construct the topological boundary. -/
theorem principalDivisor_support_subset (D : RationalUnitRepresentative X f)
    [AlgebraicGeometry.IsNoetherian X] :
    (↑(Ord.BundleCycles.principalDivisor X f).support : Set X) ⊆ (D.domain : Set X)ᶜ := by
  intro x hx hxU
  have hxne := Finsupp.mem_support_iff.mp hx
  exact hxne (D.ord_eq_zero x hxU)

/-- The entire closed support of each divisor term misses the unit domain. -/
theorem principalDivisor_closure_subset (D : RationalUnitRepresentative X f)
    [AlgebraicGeometry.IsNoetherian X] (x : X) (hx : Ord.BundleCycles.principalDivisor X f x ≠ 0) :
    closure ({x} : Set X) ⊆ (D.domain : Set X)ᶜ := by
  apply D.domain.isOpen.isClosed_compl.closure_subset_iff.mpr
  exact Set.singleton_subset_iff.mpr
    (D.principalDivisor_support_subset (Finsupp.mem_support_iff.mpr hx))

/-- Restriction of a regular section leaves its function-field germ unchanged. -/
theorem germ_restrict {U V : X.Opens} [Nonempty U] [Nonempty V]
    (h : V ≤ U) (a : Γ(X, U)) :
    X.germToFunctionField V (X.presheaf.map (homOfLE h).op a) =
      X.germToFunctionField U a :=
  X.presheaf.germ_res_apply (homOfLE h) (genericPoint X) _ a

/-- Any two representatives of the same rational function agree on every
common nonempty subopen, by injectivity into the actual function field. -/
theorem agree_on_common_open (D E : RationalUnitRepresentative X f)
    (V : X.Opens) [Nonempty V] (hD : V ≤ D.domain) (hE : V ≤ E.domain) :
    X.presheaf.map (homOfLE hD).op (D.unit : Γ(X, D.domain)) =
      X.presheaf.map (homOfLE hE).op (E.unit : Γ(X, E.domain)) := by
  apply X.germToFunctionField_injective V
  rw [germ_restrict, germ_restrict, D.represents, E.represents]

end RationalUnitRepresentative
end
end OAI.AlgebraicGeometry.Divisors.LineBundles.RationalBoundary.BundleCycles
end ComponentSource_0

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.RationalUnitRepresentative"

@[expose] public section ComponentSource_1
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.RationalPullback -/
/- Modified from pinned openai/math: import the extracted algebraic rational-unit representative module. All declarations below are unchanged. Apache 2.0. -/

/-! # Rational Pullback -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles

noncomputable section

/-!
# LineBundleCycles: actual unit representatives on support deformations

Pullback along the constructed dominant projection takes an actual
nonempty unit open to its actual nonempty inverse image. The resulting
principal divisor is supported over the complement of that original
unit open, by its local orders of vanishing.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

section

variable {A B : Scheme} [IsIntegral A] [IsIntegral B] {g : B.functionField}

/-- Pull back a genuine unit representative along a surjective morphism. -/
def RationalBoundary.BundleCycles.RationalUnitRepresentative.pullback (D : RationalBoundary.BundleCycles.RationalUnitRepresentative B g) (i : A ⟶ B) (hi : Function.Surjective i) :
    RationalBoundary.BundleCycles.RationalUnitRepresentative A
      (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap i (Deformation.FunctionField.BundleCycles.genericPoint_eq_of_surjective i hi) g) := by
  have hn : Nonempty (i ⁻¹ᵁ D.domain) := by
    obtain ⟨x⟩ := D.nonempty_domain
    obtain ⟨y, hy⟩ := hi x.1
    exact ⟨⟨y, (congrArg (fun z => z ∈ D.domain) hy).mpr x.2⟩⟩
  refine { domain := i ⁻¹ᵁ D.domain
           nonempty_domain := hn
           unit := Units.map (i.app D.domain).hom.toMonoidHom D.unit
           represents := ?_ }
  have h := ConcreteCategory.congr_hom
    (Deformation.FunctionField.BundleCycles.genericFieldMap_germOn i (Deformation.FunctionField.BundleCycles.genericPoint_eq_of_surjective i hi) D.domain)
    (D.unit : Γ(B, D.domain))
  exact h.symm.trans
    (congrArg (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap i (Deformation.FunctionField.BundleCycles.genericPoint_eq_of_surjective i hi)) D.represents)

@[simp]
theorem RationalBoundary.BundleCycles.RationalUnitRepresentative.pullback_domain (D : RationalBoundary.BundleCycles.RationalUnitRepresentative B g) (i : A ⟶ B)
    (hi : Function.Surjective i) : (D.pullback i hi).domain = i ⁻¹ᵁ D.domain := rfl

end

variable {X : Scheme} (I P : X.IdealSheafData) [IsIntegral P.subscheme]
    {g : P.subscheme.functionField}

/-- The original rational function's unit representative on the actual support deformation. -/
def RationalPullback.BundleCycles.globalSupportRationalRepresentative (D : RationalBoundary.BundleCycles.RationalUnitRepresentative P.subscheme g) :
    RationalBoundary.BundleCycles.RationalUnitRepresentative (Global.SupportDeformation.BundleCycles.globalSupportDeformation I P) (Deformation.FunctionField.BundleCycles.globalSupportFunctionFieldMap I P g) :=
  D.pullback (Support.Projection.BundleCycles.globalSupportDeformationToSupport I P) (Support.Projection.BundleCycles.globalSupportDeformationToSupport_surjective I P)

/-- No divisor coefficient occurs over the original unit domain. -/
theorem RationalPullback.BundleCycles.globalSupportPulledDivisor_vanishes [AlgebraicGeometry.IsNoetherian X]
    (D : RationalBoundary.BundleCycles.RationalUnitRepresentative P.subscheme g) (x : Global.SupportDeformation.BundleCycles.globalSupportDeformation I P)
    (hx : Support.Projection.BundleCycles.globalSupportDeformationToSupport I P x ∈ D.domain) :
    (Global.SupportDeformation.BundleCycles.globalSupportDeformation I P).ord (Deformation.FunctionField.BundleCycles.globalSupportFunctionFieldMap I P g) x = 0 :=
  (RationalPullback.BundleCycles.globalSupportRationalRepresentative I P D).ord_eq_zero x hx

/-- The complete finite divisor is supported over the complement of the original unit open. -/
theorem RationalPullback.BundleCycles.globalSupportPulledDivisor_support [AlgebraicGeometry.IsNoetherian X]
    (D : RationalBoundary.BundleCycles.RationalUnitRepresentative P.subscheme g) :
    ((Ord.BundleCycles.principalDivisor (Global.SupportDeformation.BundleCycles.globalSupportDeformation I P) (Deformation.FunctionField.BundleCycles.globalSupportFunctionFieldMap I P g)).support :
      Set (Global.SupportDeformation.BundleCycles.globalSupportDeformation I P)) ⊆
      (Support.Projection.BundleCycles.globalSupportDeformationToSupport I P) ⁻¹' (D.domain : Set P.subscheme)ᶜ :=
  (RationalPullback.BundleCycles.globalSupportRationalRepresentative I P D).principalDivisor_support_subset

end

end OAI.AlgebraicGeometry.Divisors.LineBundles
end ComponentSource_1

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.RationalPullback"

@[expose] public section ComponentSource_2
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.GenericFiberDivisorZero -/

/-! # Generic Fiber Divisor Zero -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles

noncomputable section

/-!
# LineBundleCycles: a pulled-back rational divisor vanishes over the generic point
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]

def RationalBoundary.BundleCycles.RationalUnitRepresentative.pullbackGeneric {g : Y.functionField}
    (D : RationalBoundary.BundleCycles.RationalUnitRepresentative Y g) (f : X ⟶ Y)
    (hη : f (genericPoint X) = genericPoint Y) :
    RationalBoundary.BundleCycles.RationalUnitRepresentative X (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη g) := by
  have hmem : genericPoint Y ∈ D.domain :=
    ((genericPoint_spec Y).mem_open_set_iff D.domain.isOpen).mpr
      (by simpa using D.nonempty_domain)
  have hn : Nonempty (f ⁻¹ᵁ D.domain) := ⟨⟨genericPoint X, by
    change f (genericPoint X) ∈ D.domain
    rw [hη]
    exact hmem⟩⟩
  refine { domain := f ⁻¹ᵁ D.domain
           nonempty_domain := hn
           unit := Units.map (f.app D.domain).hom.toMonoidHom D.unit
           represents := ?_ }
  have h := ConcreteCategory.congr_hom (Deformation.FunctionField.BundleCycles.genericFieldMap_germOn f hη D.domain)
    (D.unit : Γ(Y, D.domain))
  exact h.symm.trans (congrArg (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη) D.represents)

theorem GenericFiberDivisorZero.BundleCycles.ord_pullback_zero_over_generic [IsLocallyNoetherian X]
    (f : X ⟶ Y) (hη : f (genericPoint X) = genericPoint Y)
    (g : Y.functionField) (hg : g ≠ 0) (x : X) (hx : f x = genericPoint Y) :
    X.ord (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη g) x = 0 := by
  let D := RationalBoundary.BundleCycles.rationalUnitRepresentative Y g hg
  apply (D.pullbackGeneric f hη).ord_eq_zero x
  change f x ∈ D.domain
  rw [hx]
  exact ((genericPoint_spec Y).mem_open_set_iff D.domain.isOpen).mpr
    (by simpa using D.nonempty_domain)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles
end ComponentSource_2

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.GenericFiberDivisorZero"

@[expose] public section ComponentSource_3
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.DivisorPullback -/

/-! # Divisor Pullback -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.DivisorPullback.BundleCycles

noncomputable section

/-!
# LineBundleCycles: complete rational-divisor pullback to the affine line
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.Order

variable (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]

theorem polynomialProjection_order (p : Spec (CommRingCat.of R))
    (g : (Spec (CommRingCat.of R)).functionField) :
    (Spec (CommRingCat.of (Polynomial R))).ord (Projection.BundleCycles.polynomialFunctionFieldMap R g) (Projection.BundleCycles.polynomialPrimePoint R p) =
      (Spec (CommRingCat.of R)).ord g p := by
  let : p.asIdeal.IsPrime := (show PrimeSpectrum R from p).isPrime
  by_cases hp : coheight p = 1
  · have hP : ((Projection.BundleCycles.polynomialPrimePoint R p).asIdeal.under R).map
        (algebraMap R (Polynomial R)) = (Projection.BundleCycles.polynomialPrimePoint R p).asIdeal := by
      change (Ideal.comap (Polynomial.C : R →+* Polynomial R) (p.asIdeal.map Polynomial.C)).map Polynomial.C =
        p.asIdeal.map Polynomial.C
      rw [PrimeExtension.BundleCycles.polynomialPrimeExtension_comap]
    have hmax := Affine.ExtendedPrimeStalk.BundleCycles.affineExtendedPrime_stalk_maximalIdeal (Projection.BundleCycles.polynomialPrimePoint R p) hP
    have h := FlatMorphismOrder.BundleCycles.ord_flat_stalk_eq (Projection.BundleCycles.polynomialProjection R) (Projection.BundleCycles.polynomialProjection_genericPoint R)
      (Projection.BundleCycles.polynomialPrimePoint R p) ((Projection.BundleCycles.polynomialPrimePoint_coheight R p).trans hp)
      (by rw [Projection.BundleCycles.polynomialPrimePoint_projection]; exact hp) hmax g
    exact h.trans (congrArg ((Spec (CommRingCat.of R)).ord g) (Projection.BundleCycles.polynomialPrimePoint_projection R p))
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one hp,
      Scheme.ord_eq_zero_of_coheight_neq_one (fun h => hp ((Projection.BundleCycles.polynomialPrimePoint_coheight R p).symm.trans h))]

theorem polynomialPulledDivisor_support (g : (Spec (CommRingCat.of R)).functionField) (hg : g ≠ 0)
    (P : Spec (CommRingCat.of (Polynomial R)))
    (hP : (Spec (CommRingCat.of (Polynomial R))).ord (Projection.BundleCycles.polynomialFunctionFieldMap R g) P ≠ 0) :
    P ∈ Set.range (Projection.BundleCycles.polynomialPrimePoint R) := by
  let : P.asIdeal.IsPrime := (show PrimeSpectrum (Polynomial R) from P).isPrime
  have hheight : P.asIdeal.height = 1 := by
    rw [idealHeight_eq_coheight]
    by_contra hn
    exact hP (Scheme.ord_eq_zero_of_coheight_neq_one hn _)
  have hp : P.asIdeal.under R ≠ ⊥ := by
    intro hp
    apply hP
    apply GenericFiberDivisorZero.BundleCycles.ord_pullback_zero_over_generic (Projection.BundleCycles.polynomialProjection R) (Projection.BundleCycles.polynomialProjection_genericPoint R) g hg P
    rw [genericPoint_eq_bot_of_affine]
    exact PrimeSpectrum.ext hp
  refine ⟨Projection.BundleCycles.polynomialProjection R P, ?_⟩
  exact PrimeSpectrum.ext (PrimeExtension.BundleCycles.polynomialHeightOne_isExtended P.asIdeal hheight hp)

def polynomialCycleExtension : (Spec (CommRingCat.of R) →₀ ℚ) →ₗ[ℚ]
    (Spec (CommRingCat.of (Polynomial R)) →₀ ℚ) :=
  Finsupp.lmapDomain ℚ ℚ (Projection.BundleCycles.polynomialPrimePoint R)

theorem polynomialPrincipalDivisor_pullback (g : (Spec (CommRingCat.of R)).functionField) (hg : g ≠ 0) :
    RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Spec (CommRingCat.of (Polynomial R))) (Projection.BundleCycles.polynomialFunctionFieldMap R g) =
      polynomialCycleExtension R (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Spec (CommRingCat.of R)) g) := by
  ext P
  by_cases hP : P ∈ Set.range (Projection.BundleCycles.polynomialPrimePoint R)
  · obtain ⟨p, rfl⟩ := hP
    change _ = Finsupp.mapDomain (Projection.BundleCycles.polynomialPrimePoint R) _ (Projection.BundleCycles.polynomialPrimePoint R p)
    rw [Finsupp.mapDomain_apply_of_injective (Projection.BundleCycles.polynomialPrimePoint_injective R),
      RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor_apply, RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor_apply, polynomialProjection_order]
  · have hz : (Spec (CommRingCat.of (Polynomial R))).ord (Projection.BundleCycles.polynomialFunctionFieldMap R g) P = 0 := by
      by_contra hn
      exact hP (polynomialPulledDivisor_support R g hg P hn)
    change _ = Finsupp.mapDomain (Projection.BundleCycles.polynomialPrimePoint R) _ P
    rw [Finsupp.mapDomain_of_notMem_range _ _ hP, RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor_apply, hz, Int.cast_zero]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.DivisorPullback.BundleCycles
end ComponentSource_3

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.DivisorPullback"

@[expose] public section ComponentSource_4
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.DivisorPullback -/

/-! # Divisor Pullback -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.DivisorPullback.BundleCycles

noncomputable section

/-! # LineBundleCycles: complete rational-divisor pullback to the relative affine line -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

variable (X : Scheme.{0})

variable [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]

theorem affineLineOrder_on_chart (U : X.affineOpens) [Nonempty U.1]
    (g : X.functionField) (P : Spec (CommRingCat.of (Polynomial Γ(X, U.1)))) :
    (Charts.BundleCycles.affineLine X).ord (Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap (Charts.BundleCycles.affineLineProjection X) g) (Charts.BundleCycles.affineLinePolynomialChart X U P) =
      (Spec (CommRingCat.of (Polynomial Γ(X, U.1)))).ord
        (LineBundles.Polynomial.Projection.BundleCycles.polynomialFunctionFieldMap Γ(X, U.1) (RationalDivisorRestriction.BundleCycles.openFunctionFieldMap U.2.fromSpec g)) P := by
  have h := congrArg (fun k => k g) (GenericPoint.BundleCycles.affineLineFunctionField_on_chart X U)
  exact (RationalDivisorRestriction.BundleCycles.ord_openImmersion (Charts.BundleCycles.affineLinePolynomialChart X U) (Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap (Charts.BundleCycles.affineLineProjection X) g) P).symm.trans
    (congrArg (fun a => (Spec (CommRingCat.of (Polynomial Γ(X, U.1)))).ord a P) h)

theorem affineLineProjection_order (x : X) (g : X.functionField) :
    (Charts.BundleCycles.affineLine X).ord (Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap (Charts.BundleCycles.affineLineProjection X) g) (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X) x) =
      X.ord g x := by
  obtain ⟨V, hV, hx, _⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top x)
  let U : X.affineOpens := ⟨V, hV⟩
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
  have : Nonempty U.1 := ⟨⟨x, hx⟩⟩
  obtain ⟨p, hp⟩ := (congrArg (fun s : Set X => x ∈ s) U.2.range_fromSpec).mpr hx
  have he := GenericPoint.BundleCycles.affineLineFiberGenericPoint_on_chart X U p
  rw [hp] at he
  rw [he]
  exact (affineLineOrder_on_chart X U g (LineBundles.Polynomial.Projection.BundleCycles.polynomialPrimePoint Γ(X, U.1) p)).trans
    ((LineBundles.Polynomial.DivisorPullback.BundleCycles.polynomialProjection_order Γ(X, U.1) p (RationalDivisorRestriction.BundleCycles.openFunctionFieldMap U.2.fromSpec g)).trans
      ((RationalDivisorRestriction.BundleCycles.ord_openImmersion U.2.fromSpec g p).trans (congrArg (X.ord g) hp)))

theorem affineLinePulledDivisor_support (g : X.functionField) (hg : g ≠ 0)
    (y : Charts.BundleCycles.affineLine X)
    (hy : (Charts.BundleCycles.affineLine X).ord (Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap (Charts.BundleCycles.affineLineProjection X) g) y ≠ 0) :
    y ∈ Set.range (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X)) := by
  obtain ⟨U, P, rfl⟩ := Charts.BundleCycles.affineLinePolynomialChart_covers X y
  have hp : U.2.fromSpec (LineBundles.Polynomial.Projection.BundleCycles.polynomialProjection Γ(X, U.1) P) ∈ (U.1 : Set X) := by
    rw [← U.2.range_fromSpec]
    exact ⟨_, rfl⟩
  have : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
  have : Nonempty U.1 := ⟨⟨_, hp⟩⟩
  have hg' : RationalDivisorRestriction.BundleCycles.openFunctionFieldMap U.2.fromSpec g ≠ 0 :=
    (map_ne_zero_iff _ (RationalDivisorRestriction.BundleCycles.openFunctionFieldMap U.2.fromSpec).hom.injective).mpr hg
  have hP : (Spec (CommRingCat.of (Polynomial Γ(X, U.1)))).ord
      (LineBundles.Polynomial.Projection.BundleCycles.polynomialFunctionFieldMap Γ(X, U.1) (RationalDivisorRestriction.BundleCycles.openFunctionFieldMap U.2.fromSpec g)) P ≠ 0 :=
    fun hz => hy ((affineLineOrder_on_chart X U g P).trans hz)
  obtain ⟨p, rfl⟩ := LineBundles.Polynomial.DivisorPullback.BundleCycles.polynomialPulledDivisor_support Γ(X, U.1) _ hg' P hP
  exact ⟨U.2.fromSpec p, GenericPoint.BundleCycles.affineLineFiberGenericPoint_on_chart X U p⟩

theorem affineLinePrincipalDivisor_pullback (g : X.functionField) (hg : g ≠ 0) :
    RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Charts.BundleCycles.affineLine X) (Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap (Charts.BundleCycles.affineLineProjection X) g) =
      Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension (Charts.BundleCycles.affineLineProjection X) (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g) := by
  ext y
  by_cases hy : y ∈ Set.range (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X))
  · obtain ⟨x, rfl⟩ := hy
    change _ = Finsupp.mapDomain (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X)) _ (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X) x)
    rw [Finsupp.mapDomain_apply_of_injective (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint_injective (Charts.BundleCycles.affineLineProjection X)),
      RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor_apply, RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor_apply, affineLineProjection_order]
  · have hz : (Charts.BundleCycles.affineLine X).ord (Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap (Charts.BundleCycles.affineLineProjection X) g) y = 0 := by
      by_contra hn
      exact hy (affineLinePulledDivisor_support X g hg y hn)
    change _ = Finsupp.mapDomain (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X)) _ y
    rw [Finsupp.mapDomain_of_notMem_range _ _ hy, RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor_apply, hz, Int.cast_zero]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.DivisorPullback.BundleCycles
end ComponentSource_4

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.DivisorPullback"

@[expose] public section ComponentSource_5
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.PrincipalRelations -/

/-! # Principal Relations -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.PrincipalRelations.BundleCycles

noncomputable section

/-! # LineBundleCycles: all actual principal-divisor relations pull back to the relative affine line -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable (X : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X]

theorem affineLineCycleExtension_principal (W : IrreducibleCloseds X)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0) :
    Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension (Charts.BundleCycles.affineLineProjection X) (Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g) =
      Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (Support.BundleCycles.affineLineExtendedSupport X W) (Support.BundleCycles.affineLineExtendedFunction X W g) := by
  let A := CycleClass.Geometric.GenericPoint.reducedSupportScheme W
  let j := Support.BundleCycles.affineLineSupportMap X W
  have he : Finsupp.mapDomain (CycleClass.Geometric.GenericPoint.reducedSupportι W) (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor A g) =
      Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g :=
    (Finsupp.embDomain_eq_mapDomain
      ⟨CycleClass.Geometric.GenericPoint.reducedSupportι W, (CycleClass.Geometric.GenericPoint.reducedSupportι W).isClosedEmbedding.injective⟩
      (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor A g)).symm
  have hnat := Integral.FiberOpen.BundleCycles.integralFiberCycleExtension_naturality (Charts.BundleCycles.affineLineProjection X) (Charts.BundleCycles.affineLineProjection A)
    (CycleClass.Geometric.GenericPoint.reducedSupportι W) j (Support.BundleCycles.affineLineSupport_isPullback X W) (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor A g)
  exact (congrArg (Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension (Charts.BundleCycles.affineLineProjection X)) he.symm).trans
    (hnat.symm.trans
      ((congrArg (Finsupp.mapDomain j) (DivisorPullback.BundleCycles.affineLinePrincipalDivisor_pullback A g hg).symm).trans
        (Integral.ClosedImage.BundleCycles.integralClosedImage_principalDivisor j _)))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.PrincipalRelations.BundleCycles
end ComponentSource_5

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.PrincipalRelations"

@[expose] public section ComponentSource_6
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.ChowExtension -/

/-! # Chow Extension -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.ChowExtension.BundleCycles

noncomputable section

/-! # LineBundleCycles: genuine Chow pullback from the original scheme to its relative affine line -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable (X : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

theorem affineLineGradedCycleExtension_principal (d : ℕ) (W : IrreducibleCloseds X)
    (hW : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f = d + 1)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0) :
    CycleGrading.BundleCycles.affineLineGradedCycleExtension X f d (Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor f d W g) =
      Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1)
        (Support.BundleCycles.affineLineExtendedSupport X W) (Support.BundleCycles.affineLineExtendedFunction X W g) := by
  apply Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion_injective (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1)
  rw [CycleGrading.BundleCycles.affineLineGradedCycleExtension_forget, Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor_push f d W hW,
    PrincipalRelations.BundleCycles.affineLineCycleExtension_principal X W g hg,
    Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor_push (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1)
      (Support.BundleCycles.affineLineExtendedSupport X W) ((CycleGrading.BundleCycles.affineLineExtendedSupport_dimension X f W).trans
        (congrArg (fun n => n + 1) hW))]

theorem affineLineGradedCycleExtension_isPrincipal (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ)
    (hz : DimensionChow.BundleCycles.IsDimensionPrincipalDivisorQ f d z) :
    DimensionChow.BundleCycles.IsDimensionPrincipalDivisorQ (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1)
      (CycleGrading.BundleCycles.affineLineGradedCycleExtension X f d z) := by
  obtain ⟨W, hW, g, hg, rfl⟩ := hz
  exact ⟨Support.BundleCycles.affineLineExtendedSupport X W,
    (CycleGrading.BundleCycles.affineLineExtendedSupport_dimension X f W).trans (congrArg (fun n => n + 1) hW),
    Support.BundleCycles.affineLineExtendedFunction X W g, Support.BundleCycles.affineLineExtendedFunction_ne_zero X W g hg,
    affineLineGradedCycleExtension_principal X f d W hW g hg⟩

theorem affineLineGradedCycleExtension_relations (d : ℕ) :
    DimensionChow.BundleCycles.dimensionRationalEquivalenceQ f d ≤
      (DimensionChow.BundleCycles.dimensionRationalEquivalenceQ (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1)).comap
        (CycleGrading.BundleCycles.affineLineGradedCycleExtension X f d) := by
  apply Submodule.span_le.mpr
  intro z hz
  exact Submodule.subset_span (affineLineGradedCycleExtension_isPrincipal X f d z hz)

def affineLineChowExtension (d : ℕ) :
    DimensionChow.BundleCycles.DimensionChowQ f d →ₗ[ℚ] DimensionChow.BundleCycles.DimensionChowQ (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1) :=
  (DimensionChow.BundleCycles.dimensionRationalEquivalenceQ f d).mapQ
    (DimensionChow.BundleCycles.dimensionRationalEquivalenceQ (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1))
    (CycleGrading.BundleCycles.affineLineGradedCycleExtension X f d) (affineLineGradedCycleExtension_relations X f d)

@[simp]
theorem affineLineChowExtension_cycle (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :
    affineLineChowExtension X f d (DimensionChow.BundleCycles.dimensionCycleToChowQ f d z) =
      DimensionChow.BundleCycles.dimensionCycleToChowQ (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1)
        (CycleGrading.BundleCycles.affineLineGradedCycleExtension X f d z) := rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.ChowExtension.BundleCycles
end ComponentSource_6

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.ChowExtension"

@[expose] public section ComponentSource_7
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.ChowSurjective -/

/-! # Chow Surjective -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.ChowSurjective.BundleCycles

noncomputable section

/-! # LineBundleCycles: surjectivity of the actual dimension-graded affine-line Chow pullback -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable (X : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

theorem affineLineChowExtension_single_mem_range (d : ℕ)
    (y : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1)) :
    DimensionChow.BundleCycles.dimensionCycleToChowQ (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1) (Finsupp.single y 1) ∈
      LinearMap.range (ChowExtension.BundleCycles.affineLineChowExtension X f d) := by
  by_cases hy : y.val ∈ Set.range (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X))
  · obtain ⟨x, hx⟩ := hy
    have hd : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f = d := by
      have h := CycleGrading.BundleCycles.affineLineFiberGenericPoint_dimension X f x
      rw [hx, y.property] at h
      omega
    let x' : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d := ⟨x, hd⟩
    refine ⟨DimensionChow.BundleCycles.dimensionCycleToChowQ f d (Finsupp.single x' 1), ?_⟩
    rw [ChowExtension.BundleCycles.affineLineChowExtension_cycle]
    apply congrArg (DimensionChow.BundleCycles.dimensionCycleToChowQ (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1))
    change Finsupp.mapDomain (CycleGrading.BundleCycles.affineLineDimensionPointMap X f d) (Finsupp.single x' 1) = _
    rw [Finsupp.mapDomain_single]
    exact congrArg (fun q => Finsupp.single q (1 : ℚ)) (Subtype.ext hx)
  · obtain ⟨W, g, hW, hg, z, hz⟩ := RelationGrading.BundleCycles.affineLineNonextendedPoint_graded_relation X f d y hy
    have h := congrArg (DimensionChow.BundleCycles.dimensionCycleToChowQ (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1)) hz
    rw [map_add, ← ChowExtension.BundleCycles.affineLineChowExtension_cycle,
      DimensionChow.BundleCycles.dimensionCycleToChowQ_principal (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1) W hW g hg] at h
    refine ⟨-DimensionChow.BundleCycles.dimensionCycleToChowQ f d z, ?_⟩
    rw [map_neg]
    exact (eq_neg_of_add_eq_zero_left h).symm

theorem affineLineChowExtension_surjective (d : ℕ) : Function.Surjective (ChowExtension.BundleCycles.affineLineChowExtension X f d) := by
  intro a
  obtain ⟨z, rfl⟩ := DimensionChow.BundleCycles.dimensionCycleToChowQ_surjective (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1) a
  change DimensionChow.BundleCycles.dimensionCycleToChowQ (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1) z ∈
    LinearMap.range (ChowExtension.BundleCycles.affineLineChowExtension X f d)
  induction z using Finsupp.induction_linear with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add z w hz hw => rw [map_add]; exact Submodule.add_mem _ hz hw
  | single y q =>
    have h := Submodule.smul_mem (LinearMap.range (ChowExtension.BundleCycles.affineLineChowExtension X f d)) q
      (affineLineChowExtension_single_mem_range X f d y)
    rw [← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one] at h
    exact h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.ChowSurjective.BundleCycles
end ComponentSource_7

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.ChowSurjective"

@[expose] public section ComponentSource_8
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.SpaceProperties -/

/-! # Space Properties -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.SpaceProperties.BundleCycles

noncomputable section

section

/-! # LineBundleCycles: Noetherianity of finite relative affine spaces -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (ι : Type) [Finite ι] (X : Scheme.{0})

instance finiteAffineSpace_isLocallyNoetherian [IsLocallyNoetherian X] :
    IsLocallyNoetherian (AffineSpace ι X) :=
  LocallyOfFiniteType.isLocallyNoetherian (AffineSpace ι X ↘ X)

instance finiteAffineSpace_isNoetherian [AlgebraicGeometry.IsNoetherian X] :
    AlgebraicGeometry.IsNoetherian (AffineSpace ι X) := by
  have : CompactSpace (AffineSpace ι X) :=
    QuasiCompact.compactSpace_of_compactSpace (AffineSpace ι X ↘ X)
  exact ⟨⟩

end

/-! # LineBundleCycles: smoothness and integrality of actual finite relative affine spaces -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (ι : Type) [Finite ι] (X : Scheme.{0})

instance finiteAffineSpaceProjection_smooth : Smooth (AffineSpace ι X ↘ X) := by
  have : IsZariskiLocalAtTarget (@Smooth.{0}) := HasRingHomProperty.instIsZariskiLocalAtTarget _
  apply Global.DeformationProperties.BundleCycles.morphismProperty_of_cover_pullbacks (@Smooth) (AffineSpace ι X ↘ X) X.affineCover
    (fun i => AffineSpace ι (X.affineCover.X i))
    (fun i => AffineSpace.map ι (X.affineCover.f i))
    (fun i => AffineSpace ι (X.affineCover.X i) ↘ X.affineCover.X i)
    (fun i => (AffineSpace.isPullback_map (n := ι) (X.affineCover.f i)).flip)
  intro i
  exact LineBundles.AffineSpace.ChartProperties.BundleCycles.affineSpaceSpecProjection_smooth _ ι

instance finiteAffineSpace_isIntegral [IsIntegral X] [IsLocallyNoetherian X] :
    IsIntegral (AffineSpace ι X) :=
  GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (AffineSpace ι X ↘ X)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.SpaceProperties.BundleCycles
end ComponentSource_8

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.SpaceProperties"

@[expose] public section ComponentSource_9
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.Sum -/

/-! # Sum -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.Sum.BundleCycles

noncomputable section

/-! # LineBundleCycles: actual relative affine spaces split as iterated affine spaces -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (ι κ : Type) (X : Scheme.{0})

def affineSpaceSumToIterated : AffineSpace (ι ⊕ κ) X ⟶ AffineSpace ι (AffineSpace κ X) :=
  AffineSpace.homOfVector (AffineSpace.reindex Sum.inr X)
    (fun i : ι => AffineSpace.coord X (Sum.inl i : ι ⊕ κ))

def affineSpaceIteratedToSum : AffineSpace ι (AffineSpace κ X) ⟶ AffineSpace (ι ⊕ κ) X :=
  AffineSpace.homOfVector
    ((AffineSpace ι (AffineSpace κ X) ↘ AffineSpace κ X) ≫ (AffineSpace κ X ↘ X))
    (Sum.elim (AffineSpace.coord (AffineSpace κ X))
      (fun k : κ => (AffineSpace ι (AffineSpace κ X) ↘ AffineSpace κ X).appTop
        (AffineSpace.coord X k)))

theorem affineSpaceSumToIterated_projection :
    affineSpaceSumToIterated ι κ X ≫ (AffineSpace ι (AffineSpace κ X) ↘ AffineSpace κ X) =
      AffineSpace.reindex Sum.inr X := AffineSpace.homOfVector_over _ _

theorem affineSpaceIteratedToSum_projection :
    affineSpaceIteratedToSum ι κ X ≫ (AffineSpace (ι ⊕ κ) X ↘ X) =
      (AffineSpace ι (AffineSpace κ X) ↘ AffineSpace κ X) ≫ (AffineSpace κ X ↘ X) :=
  AffineSpace.homOfVector_over _ _

theorem affineSpaceIteratedToSum_second :
    affineSpaceIteratedToSum ι κ X ≫ AffineSpace.reindex Sum.inr X =
      (AffineSpace ι (AffineSpace κ X) ↘ AffineSpace κ X) := by
  apply AffineSpace.hom_ext
  · simp [affineSpaceIteratedToSum]
  · intro k
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.reindex_appTop_coord]
    exact AffineSpace.homOfVector_appTop_coord _ _ _

def affineSpaceSumEquiv : AffineSpace (ι ⊕ κ) X ≅ AffineSpace ι (AffineSpace κ X) where
  hom := affineSpaceSumToIterated ι κ X
  inv := affineSpaceIteratedToSum ι κ X
  hom_inv_id := by
    apply AffineSpace.hom_ext
    · change affineSpaceSumToIterated ι κ X ≫
        (affineSpaceIteratedToSum ι κ X ≫ (AffineSpace (ι ⊕ κ) X ↘ X)) = _
      rw [affineSpaceIteratedToSum_projection, ← Category.assoc,
        affineSpaceSumToIterated_projection, AffineSpace.reindex_over, Category.id_comp]
    · intro i
      cases i with
      | inl i =>
        rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
        simp [affineSpaceSumToIterated, affineSpaceIteratedToSum]
      | inr k =>
        rw [Scheme.Hom.comp_appTop]
        change (affineSpaceSumToIterated ι κ X).appTop
          ((affineSpaceIteratedToSum ι κ X).appTop (AffineSpace.coord X (Sum.inr k))) = _
        simp only [affineSpaceIteratedToSum, AffineSpace.homOfVector_appTop_coord, Sum.elim_inr]
        rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
          affineSpaceSumToIterated_projection, AffineSpace.reindex_appTop_coord]
        simp
  inv_hom_id := by
    apply AffineSpace.hom_ext
    · rw [Category.assoc, affineSpaceSumToIterated_projection,
        affineSpaceIteratedToSum_second, Category.id_comp]
    · intro i
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      simp [affineSpaceSumToIterated, affineSpaceIteratedToSum]

theorem affineSpaceSumEquiv_over :
    (affineSpaceSumEquiv ι κ X).hom ≫
      ((AffineSpace ι (AffineSpace κ X) ↘ AffineSpace κ X) ≫ (AffineSpace κ X ↘ X)) =
        (AffineSpace (ι ⊕ κ) X ↘ X) := by
  change affineSpaceSumToIterated ι κ X ≫ _ = _
  rw [← Category.assoc, affineSpaceSumToIterated_projection, AffineSpace.reindex_over]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.Sum.BundleCycles
end ComponentSource_9

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.Sum"

@[expose] public section ComponentSource_10
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.CoordinateEquiv -/

/-! # Coordinate Equiv -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.CoordinateEquiv.BundleCycles

noncomputable section

/-! # LineBundleCycles: empty, reindexed, and successor relative affine spaces -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {ι κ : Type} (X : Scheme.{0})

def affineSpaceReindexEquiv (e : ι ≃ κ) : AffineSpace ι X ≅ AffineSpace κ X where
  hom := AffineSpace.reindex e.symm X
  inv := AffineSpace.reindex e X
  hom_inv_id := by
    apply AffineSpace.hom_ext
    · simp
    · intro i
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      simp
  inv_hom_id := by
    apply AffineSpace.hom_ext
    · simp
    · intro i
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      simp

theorem affineSpaceReindexEquiv_over (e : ι ≃ κ) :
    (affineSpaceReindexEquiv X e).hom ≫ (AffineSpace κ X ↘ X) = (AffineSpace ι X ↘ X) :=
  AffineSpace.reindex_over _ _

def affineSpaceEmptyEquiv (ι : Type) [IsEmpty ι] : AffineSpace ι X ≅ X where
  hom := AffineSpace ι X ↘ X
  inv := AffineSpace.homOfVector (𝟙 X) (fun i : ι => isEmptyElim i)
  hom_inv_id := by
    apply AffineSpace.hom_ext
    · simp
    · exact isEmptyElim
  inv_hom_id := AffineSpace.homOfVector_over _ _

irreducible_def affineSpaceSuccEquiv (n : ℕ) :
    AffineSpace (Fin (n + 1)) X ≅ AffineSpace PUnit (AffineSpace (Fin n) X) :=
  affineSpaceReindexEquiv X
    (((finSuccEquiv n).trans (Equiv.optionEquivSumPUnit (Fin n))).trans (Equiv.sumComm _ _)) ≪≫
      Sum.BundleCycles.affineSpaceSumEquiv PUnit (Fin n) X

theorem affineSpaceSuccEquiv_over (n : ℕ) :
    (affineSpaceSuccEquiv X n).hom ≫
      ((AffineSpace PUnit (AffineSpace (Fin n) X) ↘ AffineSpace (Fin n) X) ≫
        (AffineSpace (Fin n) X ↘ X)) = (AffineSpace (Fin (n + 1)) X ↘ X) := by
  rw [affineSpaceSuccEquiv_def]
  change (_ ≫ (Sum.BundleCycles.affineSpaceSumEquiv PUnit (Fin n) X).hom) ≫ _ = _
  rw [Category.assoc, Sum.BundleCycles.affineSpaceSumEquiv_over, affineSpaceReindexEquiv_over]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.CoordinateEquiv.BundleCycles
end ComponentSource_10

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.CoordinateEquiv"

@[expose] public section ComponentSource_11
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.ChowOver -/

/-! # Chow Over -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.ChowOver.BundleCycles

noncomputable section

section

/-! # LineBundleCycles: closed pushforward with explicit compatibility of structure morphisms -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Scheme.{0}} (i : X ⟶ Y) [IsClosedImmersion i]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (h : i ≫ g = f)

def closedDimensionCyclePushforwardOver (d : ℕ) :
    (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) →ₗ[ℚ] (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint g d →₀ ℚ) :=
  (CyclePushforward.BundleCycles.closedDimensionCyclePushforward i g d).comp (DimensionChow.BundleCycles.dimensionCycleTransport h.symm d)

theorem closedDimensionCyclePushforwardOver_forget (d : ℕ)
    (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :
    Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion g d (closedDimensionCyclePushforwardOver i f g h d z) =
      Finsupp.mapDomain i (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d z) := by
  change Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion g d
    (CyclePushforward.BundleCycles.closedDimensionCyclePushforward i g d (DimensionChow.BundleCycles.dimensionCycleTransport h.symm d z)) = _
  rw [CyclePushforward.BundleCycles.closedDimensionCyclePushforward_forget, DimensionChow.BundleCycles.dimensionCycleTransport_forget]

variable [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    [LocallyOfFiniteType g]

def closedChowPushforwardOver (d : ℕ) : DimensionChow.BundleCycles.DimensionChowQ f d →ₗ[ℚ] DimensionChow.BundleCycles.DimensionChowQ g d :=
  (ChowPushforward.BundleCycles.closedChowPushforward i g d).comp (DimensionChow.BundleCycles.dimensionChowTransport h.symm d)

theorem closedChowPushforwardOver_cycle (d : ℕ)
    (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :
    closedChowPushforwardOver i f g h d (DimensionChow.BundleCycles.dimensionCycleToChowQ f d z) =
      DimensionChow.BundleCycles.dimensionCycleToChowQ g d (closedDimensionCyclePushforwardOver i f g h d z) := by
  change ChowPushforward.BundleCycles.closedChowPushforward i g d
    (DimensionChow.BundleCycles.dimensionChowTransport h.symm d (DimensionChow.BundleCycles.dimensionCycleToChowQ f d z)) = _
  rw [DimensionChow.BundleCycles.dimensionChowTransport_cycle, ChowPushforward.BundleCycles.closedChowPushforward_cycle]
  rfl

end

/-! # LineBundleCycles: genuine Chow transport under isomorphisms of schemes over the complex base -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Scheme.{0}} (e : X ≅ Y)
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (h : e.hom ≫ g = f)

include h in
theorem schemeIso_inverse_over : e.inv ≫ f = g := by
  rw [← h, ← Category.assoc, e.inv_hom_id, Category.id_comp]

theorem schemeIsoCycle_roundtrip (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :
    closedDimensionCyclePushforwardOver e.inv g f (schemeIso_inverse_over e f g h) d
      (closedDimensionCyclePushforwardOver e.hom f g h d z) = z := by
  apply Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion_injective f d
  rw [closedDimensionCyclePushforwardOver_forget, closedDimensionCyclePushforwardOver_forget,
    ← Finsupp.mapDomain_comp]
  have he : (e.inv : Y → X) ∘ (e.hom : X → Y) = id := by
    funext x
    exact congrArg (fun k : X ⟶ X => k x) e.hom_inv_id
  rw [he, Finsupp.mapDomain_id]

variable [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    [LocallyOfFiniteType f] [LocallyOfFiniteType g]

theorem schemeIsoChow_roundtrip (d : ℕ) (a : DimensionChow.BundleCycles.DimensionChowQ f d) :
    closedChowPushforwardOver e.inv g f (schemeIso_inverse_over e f g h) d
      (closedChowPushforwardOver e.hom f g h d a) = a := by
  obtain ⟨z, rfl⟩ := DimensionChow.BundleCycles.dimensionCycleToChowQ_surjective f d a
  rw [closedChowPushforwardOver_cycle, closedChowPushforwardOver_cycle,
    schemeIsoCycle_roundtrip]

/-- The actual closed pushforwards along an isomorphism and its inverse
give inverse maps on the principal-divisor quotients. -/
def schemeIsoChowEquiv (d : ℕ) : DimensionChow.BundleCycles.DimensionChowQ f d ≃ₗ[ℚ] DimensionChow.BundleCycles.DimensionChowQ g d :=
  LinearEquiv.ofLinearMap
    (closedChowPushforwardOver e.hom f g h d)
    (closedChowPushforwardOver e.inv g f (schemeIso_inverse_over e f g h) d)
    (by
      ext a
      exact schemeIsoChow_roundtrip e.symm g f (schemeIso_inverse_over e f g h) d a)
    (by
      ext a
      exact schemeIsoChow_roundtrip e f g h d a)

theorem schemeIsoChowEquiv_cycle (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :
    schemeIsoChowEquiv e f g h d (DimensionChow.BundleCycles.dimensionCycleToChowQ f d z) =
      DimensionChow.BundleCycles.dimensionCycleToChowQ g d (closedDimensionCyclePushforwardOver e.hom f g h d z) :=
  closedChowPushforwardOver_cycle e.hom f g h d z

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.ChowOver.BundleCycles
end ComponentSource_11

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.ChowOver"

@[expose] public section ComponentSource_12
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.ChowZero -/

/-! # Chow Zero -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.ChowZero.BundleCycles

noncomputable section

/-! # LineBundleCycles: zero-dimensional Chow classes on the relative affine line vanish -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable (X : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

theorem affineLineZeroDimension_point_class (y : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (Charts.BundleCycles.affineLineProjection X ≫ f) 0) :
    DimensionChow.BundleCycles.dimensionCycleToChowQ (Charts.BundleCycles.affineLineProjection X ≫ f) 0 (Finsupp.single y 1) = 0 := by
  have hy : y.val ∉ Set.range (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X)) := by
    rintro ⟨x, hx⟩
    have h := CycleGrading.BundleCycles.affineLineFiberGenericPoint_dimension X f x
    rw [hx, y.property] at h
    omega
  obtain ⟨W, g, hg, w, hrel⟩ := PointRelation.BundleCycles.affineLineNonextendedPoint_cycle_relation X y.val hy
  have hcoeff : Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g y.val = 1 := by
    have h := congrArg (fun z : Charts.BundleCycles.affineLine X →₀ ℚ => z y.val) hrel
    change Finsupp.single y.val (1 : ℚ) y.val +
      Finsupp.mapDomain (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X)) w y.val = _ at h
    rw [Finsupp.single_eq_same, Finsupp.mapDomain_of_notMem_range _ _ hy, add_zero] at h
    exact h.symm
  have hW : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W (Charts.BundleCycles.affineLineProjection X ≫ f) = 1 := by
    have h := Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor_dimension (Charts.BundleCycles.affineLineProjection X ≫ f) W g y.val (hcoeff ▸ one_ne_zero)
    exact h.symm.trans (congrArg (fun n => n + 1) y.property)
  have hw : w = 0 := by
    ext x
    by_contra hx
    have hneq : Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X) x ≠ y.val := fun h => hy ⟨x, h⟩
    have h := congrArg (fun z : Charts.BundleCycles.affineLine X →₀ ℚ => z (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X) x)) hrel
    change Finsupp.single y.val (1 : ℚ) (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X) x) +
      Finsupp.mapDomain (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X)) w
        (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X) x) = _ at h
    rw [Finsupp.single_eq_of_ne hneq, Finsupp.mapDomain_apply_of_injective (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint_injective (Charts.BundleCycles.affineLineProjection X)), zero_add] at h
    have hn : Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X) x) ≠ 0 :=
      fun hz => hx (h.trans hz)
    have hd := Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor_dimension (Charts.BundleCycles.affineLineProjection X ≫ f) W g _ hn
    rw [CycleGrading.BundleCycles.affineLineFiberGenericPoint_dimension, hW] at hd
    omega
  rw [hw, map_zero, add_zero] at hrel
  have hgrade : Finsupp.single y 1 = Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor (Charts.BundleCycles.affineLineProjection X ≫ f) 0 W g := by
    apply Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion_injective (Charts.BundleCycles.affineLineProjection X ≫ f) 0
    rw [Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor_push (Charts.BundleCycles.affineLineProjection X ≫ f) 0 W hW]
    exact (show Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion (Charts.BundleCycles.affineLineProjection X ≫ f) 0 (Finsupp.single y 1) =
      Finsupp.single y.val 1 from Finsupp.mapDomain_single).trans hrel
  rw [hgrade, DimensionChow.BundleCycles.dimensionCycleToChowQ_principal (Charts.BundleCycles.affineLineProjection X ≫ f) 0 W hW g hg]

theorem affineLineZeroDimension_chow_eq_zero (a : DimensionChow.BundleCycles.DimensionChowQ (Charts.BundleCycles.affineLineProjection X ≫ f) 0) : a = 0 := by
  obtain ⟨z, rfl⟩ := DimensionChow.BundleCycles.dimensionCycleToChowQ_surjective (Charts.BundleCycles.affineLineProjection X ≫ f) 0 a
  induction z using Finsupp.induction_linear with
  | zero => exact map_zero _
  | add z w hz hw => rw [map_add, hz, hw, add_zero]
  | single y q =>
    have h := congrArg (fun a => q • a) (affineLineZeroDimension_point_class X f y)
    rw [← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one, smul_zero] at h
    exact h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.ChowZero.BundleCycles
end ComponentSource_12

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.ChowZero"


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
    (`OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.ChowZero.BundleCycles.affineLineZeroDimension_chow_eq_zero, "theorem")
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
    ("nonce", toJson "cbed2a20169aceb0f9653d11e8b64ddf"), ("declaration_count", toJson localNames.size),
    ("kernel_trust_level", toJson env.header.trustLevel.toNat),
    ("kernel_type_checking_enabled", toJson (!Lean.debug.skipKernelTC.get opts)),
    ("server_mode", toJson (Lean.Elab.inServer.get opts)),
    ("required_endpoint_count", toJson required.size),
    ("all_new_declarations_read_from_checked_environment", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo "LITERAL_COMPONENT_KERNEL_AUDIT_COMPLETE:cbed2a20169aceb0f9653d11e8b64ddf"
