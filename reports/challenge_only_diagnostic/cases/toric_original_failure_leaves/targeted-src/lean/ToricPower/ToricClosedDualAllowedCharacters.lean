module

public import ToricPower.ToricSliceComponentCharacters
public import ToricPower.ClosedDualSliceComponents
public import ToricPower.LinearSubspaceSupportCharacter
public import ToricPower.RestrictedCartierAtlas
public import ToricPower.DiagonalToricWeights

/-! # The full restricted characters of the dual closed-slice augmentation

The contravariant Cartier differential translates a cell by its positive
Laurent character. Consequently the component character here is the
positive restriction of the integral component representative. The
nonempty weak-inequality components are precisely the regular sections
of the restricted line bundle, expressed in an actual local Cartier
frame. Integral semigroup surjectivity retains every character.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TauCeti.Toric ToricPower.IntegralArrangement
open scoped Classical

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)
  (σ : fan.cones) (W : Submodule ℝ V)
  (spans : Submodule.span ℝ (σ.val : Set V) = W)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "selected" => fanConeSliceRows fan rays σ

def toricClosedDualComponentCharacter (value : IntegralSliceValue A selected) :
    latticeTrace i W →+ ℤ :=
  (basis.equivFun.symm (sliceValueRepresentative A selected value)).comp
    (latticeTrace i W).subtype.toAddMonoidHom

def toricClosedDualComponentCharacterEquiv :
    IntegralSliceValue A selected ≃+ (latticeTrace i W →+ ℤ) :=
  (toricSliceComponentCharacterEquiv fan basis rays σ W spans).trans (AddEquiv.neg _)

@[simp]
theorem toricClosedDualComponentCharacterEquiv_apply (value : IntegralSliceValue A selected) :
    toricClosedDualComponentCharacterEquiv fan basis rays σ W spans value =
      toricClosedDualComponentCharacter fan basis rays σ W value := by
  change -(-((basis.equivFun.symm (sliceValueRepresentative A selected value)).comp
    (latticeTrace i W).subtype.toAddMonoidHom)) = _
  exact neg_neg _

include spans in
theorem toricClosedDualComponentCharacter_of_lattice (a : Fin n → ℤ) :
    toricClosedDualComponentCharacter fan basis rays σ W
      (integralSliceValueOfLattice A selected a) =
      (basis.equivFun.symm a).comp (latticeTrace i W).subtype.toAddMonoidHom := by
  apply (fanConeSliceRowMap_eq_iff fan basis rays σ W spans _ _).mp
  funext row
  exact sliceValueRepresentative_values A selected
    (integralSliceValueOfLattice A selected a) row

include spans in
theorem closedIntegralLevelSlice_annihilator
    (value : IntegralSliceValue A selected) {x : Fin n → ℝ}
    (level : x ∈ closedIntegralLevelSlice A selected value.val) :
    characterCoordinateEquiv fan.lattice basis
      (x-latticeLift (sliceValueRepresentative A selected value)) ∈ W.dualAnnihilator := by
  change x-latticeLift (sliceValueRepresentative A selected value) ∈
    fanCharacterAnnihilator fan basis W
  rw [fanCharacterAnnihilator_eq_zeroSlice fan basis rays σ W spans,
    mem_arrangementZeroSlice]
  intro row member
  rw [map_sub,level ⟨row,member⟩,augmentedForms_latticeLift,
    sliceValueRepresentative_values A selected value ⟨row,member⟩,sub_self]

end ToricPower

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)
  (σ : fan.cones) (W : LinearSubspace fan)
  (spans : Submodule.span ℝ (σ.val : Set V) = W.space)
  (b : fan.Ray → ℤ) (τ : fan.cones)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "selected" => fanConeSliceRows fan rays σ

include spans in
/-- The exact allowed-character criterion in the original local frame.
The target semigroup is that of the saturated restricted cone. -/
theorem toricClosedDualComponentAllowed_iff
    (value : IntegralSliceValue A selected) :
    (closedDualComponentRegion A selected (fanConeRaySet fan rays τ)
      (fun r => b (rays r)) value).Nonempty ↔
      toricClosedDualComponentCharacter fan basis rays σ W.space value +
        (coneDivisorCharacter fan regular b τ).comp
          (latticeTrace i W.space).subtype.toAddMonoidHom ∈
        dualSemigroup (restrictedFan fan W.space W.rational).lattice
          (τ.val.comap W.space.subtype) := by
  let a := sliceValueRepresentative A selected value
  let m := basis.equivFun.symm a
  let q := coneDivisorCharacter fan regular b τ
  let hiW := (restrictedFan fan W.space W.rational).lattice
  constructor
  · rintro ⟨x,level,lower⟩
    have ann := closedIntegralLevelSlice_annihilator fan basis rays σ W.space spans value level
    have nonnegative : ∀ v ∈ τ.val,
        0 ≤ (characterCoordinateEquiv fan.lattice basis x + fan.lattice.realCharacter q) v := by
      apply linear_nonnegative_on_toric_cone fan τ
      intro ρ
      let ray := Fan.Ray.ofToricRay fan τ ρ
      have contained : rays.symm ray ∈ fanConeRaySet fan rays τ := by
        change (rays (rays.symm ray)).toCone ≤ τ
        rw [Equiv.apply_symm_apply]
        exact Fan.Ray.toCone_ofToricRay_le fan τ ρ
      have inequality := lower (rays.symm ray) contained
      change ((-(b (rays (rays.symm ray))) : ℤ) : ℝ) ≤
        augmentedForms A (.inl (rays.symm ray)) x at inequality
      rw [Int.cast_neg,Equiv.apply_symm_apply,← characterCoordinateEquiv_primitive fan basis rays,
        fanRayPrimitiveGenerator_ofToricRay] at inequality
      simp only [LinearMap.add_apply,fan.lattice.realCharacter_apply]
      rw [show q (primitiveGenerator fan.lattice (fan.isToricCone τ.property) ρ) = b ray from
        coneDivisorCharacter_ray fan regular b τ ρ]
      linarith
    apply (mem_dualSemigroup hiW _).mpr
    intro v member
    have zero := (Submodule.mem_dualAnnihilator _).mp ann v.val v.property
    rw [map_sub,LinearMap.sub_apply,characterCoordinateEquiv_latticeLift fan basis] at zero
    have same : characterCoordinateEquiv fan.lattice basis x v.val =
        fan.lattice.realCharacter m v.val := sub_eq_zero.mp zero
    have restriction := hiW.realCharacter_comp fan.lattice
      (latticeTrace i W.space).subtype.toAddMonoidHom W.space.subtype (fun _ => rfl) (m+q)
    have character : toricClosedDualComponentCharacter fan basis rays σ W.space value +
        q.comp (latticeTrace i W.space).subtype.toAddMonoidHom =
        (m+q).comp (latticeTrace i W.space).subtype.toAddMonoidHom := by
      ext z
      rfl
    rw [character,restriction]
    change 0 ≤ fan.lattice.realCharacter (m+q) v.val
    rw [map_add,LinearMap.add_apply,← same]
    exact nonnegative v.val member
  · intro positive
    obtain ⟨lifted,restrict⟩ := linearSubspace_dualSemigroupRestriction_surjective fan W τ
      ⟨toricClosedDualComponentCharacter fan basis rays σ W.space value +
        q.comp (latticeTrace i W.space).subtype.toAddMonoidHom,positive⟩
    have restriction : (lifted.val-q).comp (latticeTrace i W.space).subtype.toAddMonoidHom =
        m.comp (latticeTrace i W.space).subtype.toAddMonoidHom := by
      ext z
      have equality := DFunLike.congr_fun (congrArg Subtype.val restrict) z
      erw [dualSemigroupMap_apply] at equality
      change lifted.val z.val = m z.val+q z.val at equality
      change lifted.val z.val-q z.val=m z.val
      omega
    let liftedCoordinates := basis.equivFun (lifted.val-q)
    have rows : integralSliceRowMap A selected liftedCoordinates =
        integralSliceRowMap A selected a := by
      apply (fanConeSliceRowMap_eq_iff fan basis rays σ W.space spans _ _).mpr
      simpa only [liftedCoordinates,LinearEquiv.symm_apply_apply] using restriction
    refine ⟨latticeLift liftedCoordinates,?_,?_⟩
    · intro row
      rw [augmentedForms_latticeLift]
      exact congrArg (fun z : ℤ => (z : ℝ))
        ((congrFun rows row).trans (sliceValueRepresentative_values A selected value row))
    · intro r member
      have nonnegative := (mem_dualSemigroup fan.lattice lifted.val).mp lifted.property
        (fanRayPrimitiveGenerator_mem_cone fan τ (rays r) member)
      rw [fan.lattice.realCharacter_apply] at nonnegative
      change ((-(b (rays r)) : ℤ) : ℝ) ≤ integralRowForm A r (latticeLift liftedCoordinates)
      rw [Int.cast_neg,integralRowForm_latticeLift,fanArrangementMatrix_basis_character,
        AddMonoidHom.sub_apply,coneDivisorCharacter_fanRay fan regular b τ (rays r) member]
      push_cast
      linarith

end ToricPower

end
