module

public import ToricPower.ToricClosedSubtorusSupport
public import ToricPower.LinearSliceLatticeComponents
public import ToricPower.LatticeTraceSplitting

/-! # All parallel slice components are the full restricted character lattice

The component value is the image of the integral row map. Its negative
restricted character is independent of the chosen representative. The
result is an actual additive equivalence with the full character group
of the saturated trace lattice, without a finite-index substitution.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TauCeti.Toric ToricPower.IntegralArrangement
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (selected : Set (Fin s ⊕ Fin n))

/-- The actual component of an integral translate. -/
def integralSliceValueOfLattice : (Fin n → ℤ) →+ IntegralSliceValue A selected :=
  (integralSliceRowMap A selected).rangeRestrict

theorem integralSliceValueOfLattice_representative (value : IntegralSliceValue A selected) :
    integralSliceValueOfLattice A selected (sliceValueRepresentative A selected value) = value := by
  apply Subtype.ext
  funext j
  exact sliceValueRepresentative_values A selected value j

theorem integralSliceValueOfLattice_surjective :
    Function.Surjective (integralSliceValueOfLattice A selected) :=
  fun value => ⟨sliceValueRepresentative A selected value,
    integralSliceValueOfLattice_representative A selected value⟩

end ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)
  (σ : fan.cones) (W : Submodule ℝ V)
  (spans : Submodule.span ℝ (σ.val : Set V) = W)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "selected" => fanConeSliceRows fan rays σ

include spans in
/-- Equality of component rows is exactly equality on the saturated
trace. The full real span, not merely the listed primitive values,
justifies the forward implication. -/
theorem fanConeSliceRowMap_eq_iff (a b : Fin n → ℤ) :
    integralSliceRowMap A selected a = integralSliceRowMap A selected b ↔
      (basis.equivFun.symm a).comp (latticeTrace i W).subtype.toAddMonoidHom =
        (basis.equivFun.symm b).comp (latticeTrace i W).subtype.toAddMonoidHom := by
  constructor
  · intro same
    have zero : latticeLift a-latticeLift b ∈
        arrangementZeroSlice (augmentedForms A) selected := by
      rw [mem_arrangementZeroSlice]
      intro row member
      rw [map_sub,augmentedForms_latticeLift,augmentedForms_latticeLift]
      exact sub_eq_zero.mpr (congrArg (fun z : ℤ => (z : ℝ))
        (congrFun same ⟨row,member⟩))
    rw [← fanCharacterAnnihilator_eq_zeroSlice fan basis rays σ W spans] at zero
    change characterCoordinateEquiv fan.lattice basis (latticeLift a-latticeLift b) ∈
      W.dualAnnihilator at zero
    ext x
    have value := (Submodule.mem_dualAnnihilator _).mp zero (i x.val) x.property
    rw [map_sub,characterCoordinateEquiv_latticeLift fan basis,
      characterCoordinateEquiv_latticeLift fan basis,LinearMap.sub_apply,
      fan.lattice.realCharacter_apply,fan.lattice.realCharacter_apply] at value
    exact_mod_cast (sub_eq_zero.mp value)
  · intro same
    funext row
    rcases row with ⟨row,member⟩
    obtain ⟨ρ,rfl⟩ := member
    let v := primitiveGenerator fan.lattice (fan.isToricCone σ.property) ρ
    have inW : i v ∈ W := by
      rw [← spans]
      exact Submodule.subset_span
        (ρ.val.isFaceOf.le (primitiveGenerator_mem fan.lattice (fan.isToricCone σ.property) ρ))
    have value := DFunLike.congr_fun same (⟨v,inW⟩ : latticeTrace i W)
    change rayPairing A a (rays.symm (Fan.Ray.ofToricRay fan σ ρ)) =
      rayPairing A b (rays.symm (Fan.Ray.ofToricRay fan σ ρ))
    rw [fanArrangementMatrix_character,fanArrangementMatrix_character,
      fanRayPrimitiveGenerator_ofToricRay]
    exact value

/-- The sign is the actual Laurent convention: a cell translated by
`a` contributes the restricted character `-a`. -/
def toricSliceComponentCharacter (value : IntegralSliceValue A selected) :
    latticeTrace i W →+ ℤ :=
  -((basis.equivFun.symm (sliceValueRepresentative A selected value)).comp
    (latticeTrace i W).subtype.toAddMonoidHom)

include spans in
theorem toricSliceComponentCharacter_of_lattice (a : Fin n → ℤ) :
    toricSliceComponentCharacter fan basis rays σ W (integralSliceValueOfLattice A selected a) =
      -((basis.equivFun.symm a).comp (latticeTrace i W).subtype.toAddMonoidHom) := by
  apply congrArg Neg.neg
  apply (fanConeSliceRowMap_eq_iff fan basis rays σ W spans _ _).mp
  funext row
  exact sliceValueRepresentative_values A selected (integralSliceValueOfLattice A selected a) row

include spans in
theorem toricSliceComponentCharacter_injective :
    Function.Injective (toricSliceComponentCharacter fan basis rays σ W) := by
  intro a b same
  have rows := (fanConeSliceRowMap_eq_iff fan basis rays σ W spans _ _).mpr
    (neg_injective same)
  apply Subtype.ext
  funext row
  exact (sliceValueRepresentative_values A selected a row).symm.trans
    ((congrFun rows row).trans (sliceValueRepresentative_values A selected b row))

include spans in
theorem toricSliceComponentCharacter_surjective :
    Function.Surjective (toricSliceComponentCharacter fan basis rays σ W) := by
  intro m
  let extended := latticeTraceCharacterExtension fan.lattice W (-m)
  refine ⟨integralSliceValueOfLattice A selected (basis.equivFun extended),?_⟩
  rw [toricSliceComponentCharacter_of_lattice fan basis rays σ W spans,
    LinearEquiv.symm_apply_apply]
  ext x
  change -(latticeTraceCharacterExtension fan.lattice W (-m) x.val) = m x
  rw [latticeTraceCharacterExtension_apply_trace,AddMonoidHom.neg_apply,neg_neg]

/-- Full additive identification of every actual parallel component
with the integral character lattice of the linear toric subvariety. -/
def toricSliceComponentCharacterEquiv :
    IntegralSliceValue A selected ≃+ (latticeTrace i W →+ ℤ) :=
  AddEquiv.ofBijective
    ({
      toFun := toricSliceComponentCharacter fan basis rays σ W
      map_zero' := by
        have same := toricSliceComponentCharacter_of_lattice fan basis rays σ W spans 0
        simpa only [map_zero,AddMonoidHom.zero_comp,neg_zero] using same
      map_add' := by
        intro a b
        obtain ⟨a,rfl⟩ := integralSliceValueOfLattice_surjective A selected a
        obtain ⟨b,rfl⟩ := integralSliceValueOfLattice_surjective A selected b
        rw [← map_add,toricSliceComponentCharacter_of_lattice fan basis rays σ W spans,
          toricSliceComponentCharacter_of_lattice fan basis rays σ W spans,
          toricSliceComponentCharacter_of_lattice fan basis rays σ W spans]
        ext x
        simp only [map_add,AddMonoidHom.comp_apply,AddMonoidHom.neg_apply,
          AddMonoidHom.add_apply,neg_add] } :
      IntegralSliceValue A selected →+ (latticeTrace i W →+ ℤ))
    ⟨toricSliceComponentCharacter_injective fan basis rays σ W spans,
      toricSliceComponentCharacter_surjective fan basis rays σ W spans⟩

end ToricPower

end
