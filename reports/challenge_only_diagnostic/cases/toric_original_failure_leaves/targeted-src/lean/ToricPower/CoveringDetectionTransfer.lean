module

public import ToricPower.ElementSumProductDerived
public import ToricPower.ElementPullbackBaseChange

/-!
# Returning a detection map through the two genuine covering adjunctions

The universal covering is pulled back along the finite power covering.
The original target has finite cohomological support in each universal
fiber, so the canonical sum-to-product comparison is invertible. A
nonzero map upstairs then returns to a nonzero map between the original
whole direct images. Every step uses the specified covering functors.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace ToricPower

variable {C : Type} [SmallCategory C] (B P : C ⥤ Type)
  (bijective : ∀ {c d : C} (f : c ⟶ d), Function.Bijective (B.map f))
  (R : Type) [CommRing R]

set_option quotPrecheck false in
local notation "ModR" => ModuleCat.{0} R
local notation "πP" => Elements.π P
local notation "L" => πP ⋙ B
local notation "pull" => ElementPushdown.pullbackCoefficient πP B (D := ModR)

local instance coveringTransfer_derivedBase : HasDerivedCategory.{1} (C ⥤ ModR) := HasDerivedCategory.standard _
local instance coveringTransfer_derivedPower : HasDerivedCategory.{1} (P.Elements ⥤ ModR) := HasDerivedCategory.standard _
local instance coveringTransfer_derivedUniversal : HasDerivedCategory.{1} (B.Elements ⥤ ModR) := HasDerivedCategory.standard _
local instance coveringTransfer_derivedPulled : HasDerivedCategory.{1} ((L).Elements ⥤ ModR) := HasDerivedCategory.standard _

def pulledCoveringComplex (K : CochainComplex (B.Elements ⥤ ModR) ℤ) :
    CochainComplex ((L).Elements ⥤ ModR) ℤ :=
  ((pull).mapHomologicalComplex (.up ℤ)).obj K

/-- Pullback retains each entire fiber and its actual homology. -/
theorem pulledCoveringComplex_finite_support
    (K : CochainComplex (B.Elements ⥤ ModR) ℤ)
    (finite : ∀ (q : ℤ) (c : C),
      {r : B.obj c | ¬ IsZero ((K.homology q).obj (B.elementsMk c r))}.Finite)
    (q : ℤ) (c : P.Elements) :
    {r : (L).obj c | ¬ IsZero
      (((pulledCoveringComplex B P R K).homology q).obj ((L).elementsMk c r))}.Finite := by
  apply (finite q c.obj).subset
  intro r nonzero
  let e := ((evaluation (L).Elements ModR).obj ((L).elementsMk c r)).mapIso
    ((K.sc q).mapHomologyIso pull)
  exact fun zero => nonzero (e.isZero_iff.mpr zero)

/-- The comparison retains the actual complex representative and the
actual base-change map, after localization. -/
def pulledCoveringSumIso (K : CochainComplex (B.Elements ⥤ ModR) ℤ) :
    (ElementPushdown.functor L (D := ModR)).mapDerivedCategory.obj
        (DerivedCategory.Q.obj (pulledCoveringComplex B P R K)) ≅
      (ElementPushdown.restriction P (D := ModR)).mapDerivedCategory.obj
        ((ElementPushdown.functor B (D := ModR)).mapDerivedCategory.obj
          (DerivedCategory.Q.obj K)) :=
  (ElementPushdown.functor L (D := ModR)).mapDerivedCategory.mapIso
      ((pull).mapDerivedCategoryFactors.app K).symm ≪≫
    (ElementPushdown.derivedPullbackIso πP B (D := ModR)).app (DerivedCategory.Q.obj K)

include bijective in
/-- A nonzero map on the complete pulled-back covering detects the
original pair of direct images. The source is wholly unbounded. -/
theorem coveringDetectionTransfer
    (K : CochainComplex (B.Elements ⥤ ModR) ℤ)
    (finite : ∀ (q : ℤ) (c : C),
      {r : B.obj c | ¬ IsZero ((K.homology q).obj (B.elementsMk c r))}.Finite)
    (E : DerivedCategory (P.Elements ⥤ ModR))
    (f : (ElementPushdown.restriction L (D := ModR)).mapDerivedCategory.obj E ⟶
      DerivedCategory.Q.obj (pulledCoveringComplex B P R K)) (nonzero : f ≠ 0) :
    ∃ g : (ElementPushdown.functor P (D := ModR)).mapDerivedCategory.obj E ⟶
      (ElementPushdown.functor B (D := ModR)).mapDerivedCategory.obj
        (DerivedCategory.Q.obj K), g ≠ 0 := by
  obtain ⟨a,ha⟩ := ElementComparison.exists_nonzero_into_sum L
    (fun f => bijective f.hom) R (pulledCoveringComplex B P R K)
    (pulledCoveringComplex_finite_support B P R K finite) E f nonzero
  let e := pulledCoveringSumIso B P R K
  have nonzeroBase : a ≫ e.hom ≠ 0 := by
    intro zero
    apply ha
    rw [← cancel_mono e.hom,zero_comp]
    exact zero
  let adj := ElementPushdown.derivedAdjunction P (D := ModR)
  let target := (ElementPushdown.functor B (D := ModR)).mapDerivedCategory.obj
    (DerivedCategory.Q.obj K)
  refine ⟨(adj.homEquiv E target).symm (a ≫ e.hom),?_⟩
  intro zero
  apply nonzeroBase
  have mapped := congrArg (adj.homEquiv E target) zero
  rw [Equiv.apply_symm_apply,adj.homAddEquiv_zero] at mapped
  exact mapped

end ToricPower

end
