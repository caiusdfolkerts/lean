module

public import ToricPower.DivisorWeightRationalPushforward

/-!
# Actual monomial morphisms between invariant Cartier sheaves

For coefficient vectors b,c and an integral character m, multiplication by
χ^m gives O(b) → O(c) whenever cρ−bρ+⟨m,vρ⟩≥0 on every ray. The construction
uses the actual Cartier sheaves and their rational-function inclusions.
Every local regularity requirement is proved from this inequality.

Development source; no verification claim is made before the current
source has passed the pinned Lean checker.
-/

@[expose] public noncomputable section

set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory TauCeti.Toric MonoidAlgebra TopologicalSpace

namespace ToricPower

universe u v

@[simp] theorem rationalPullback_id {X : Scheme.{u}} [IsIntegral X]
    (x : X.functionField) : rationalPullback (𝟙 X) (by rfl) x = x := by
  simp [rationalPullback, Scheme.Hom.stalkMap_id]

variable {N : Type u} {V : Type v} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

/-- The normalized local exponent of multiplication by a character. -/
def normalizedToricMonomialCharacter (fan : Fan i) (regular : fan.IsRegular)
    (b c : fan.Ray → ℤ) (character : N →+ ℤ) (cone : fan.cones) : N →+ ℤ :=
  coneDivisorCharacter fan regular c cone + character -
    coneDivisorCharacter fan regular b cone

theorem normalizedToricMonomialCharacter_mem (fan : Fan i) (regular : fan.IsRegular)
    (b c : fan.Ray → ℤ) (character : N →+ ℤ)
    (nonnegative : ∀ ρ : fan.Ray,
      0 ≤ c ρ - b ρ + character (fanRayPrimitiveGenerator fan ρ))
    (cone : fan.cones) :
    normalizedToricMonomialCharacter fan regular b c character cone ∈
      dualSemigroup fan.lattice cone.val := by
  rw [mem_dualSemigroup_iff_primitiveGenerator fan.lattice
    (fan.isToricCone cone.property)]
  intro ρ
  have h := nonnegative (Fan.Ray.ofToricRay fan cone ρ)
  rw [fanRayPrimitiveGenerator_ofToricRay] at h
  simpa only [normalizedToricMonomialCharacter, AddMonoidHom.sub_apply,
    AddMonoidHom.add_apply, AddMonoidHom.neg_apply, coneDivisorCharacter_ray, coneDivisorCoefficients,
    sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h

/-- The generic Cartier image criterion is satisfied on every toric chart. -/
def toricMonomialCompatibility (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (b c : fan.Ray → ℤ) (character : N →+ ℤ)
    (nonnegative : ∀ ρ : fan.Ray,
      0 ≤ c ρ - b ρ + character (fanRayPrimitiveGenerator fan ρ)) :
    letI := toricSchemeIntegral fan nonempty
    CartierResidueCompatibility (𝟙 fan.algebraicRealization) (by rfl)
      (invariantCartierDivisor fan nonempty regular b)
      (invariantCartierDivisor fan nonempty regular c)
      (rationalCharacterUnit fan nonempty character : fan.algebraicRealization.functionField) := by
  letI := toricSchemeIntegral fan nonempty
  let sourceAtlas := invariantDivisorCharacterAtlas fan regular b
  let targetAtlas := invariantDivisorCharacterAtlas fan regular c
  refine {
    Index := fan.cones
    chart := fun cone => (fan.affineToricChartι cone).opensRange
    covers := (targetAtlas.cartierEquationAtlas nonempty).covers
    sourceEquation := fun cone => rationalCharacterUnit fan nonempty
      (coneDivisorCharacter fan regular b cone)
    targetEquation := fun cone => rationalCharacterUnit fan nonempty
      (coneDivisorCharacter fan regular c cone)
    source_local := fun cone point member =>
      (sourceAtlas.cartierEquationAtlas nonempty).equation_isLocalEquationAt cone point member
    target_local := fun cone point member =>
      (targetAtlas.cartierEquationAtlas nonempty).equation_isLocalEquationAt cone point member
    preserved := fun _ => rfl
    regular_ratio := ?_ }
  intro cone point member
  rw [rationalPullback_id]
  have unit_equality :
      rationalCharacterUnit fan nonempty (coneDivisorCharacter fan regular c cone) *
        rationalCharacterUnit fan nonempty character *
        (rationalCharacterUnit fan nonempty (coneDivisorCharacter fan regular b cone))⁻¹ =
      rationalCharacterUnit fan nonempty
        (normalizedToricMonomialCharacter fan regular b c character cone) := by
    rw [← rationalCharacterUnit_neg, ← rationalCharacterUnit_add,
      ← rationalCharacterUnit_add]
    congr 1
  have value_equality := congrArg Units.val unit_equality
  simp only [Units.val_mul] at value_equality
  change (rationalCharacterUnit fan nonempty (coneDivisorCharacter fan regular c cone) :
      fan.algebraicRealization.functionField) *
    (rationalCharacterUnit fan nonempty character : fan.algebraicRealization.functionField) *
    (((rationalCharacterUnit fan nonempty (coneDivisorCharacter fan regular b cone))⁻¹ :
      fan.algebraicRealization.functionFieldˣ) : fan.algebraicRealization.functionField) ∈ _
  rw [value_equality]
  let m : dualSemigroup fan.lattice cone.val :=
    ⟨normalizedToricMonomialCharacter fan regular b c character cone,
      normalizedToricMonomialCharacter_mem fan regular b c character nonnegative cone⟩
  have h := chartCoordinateGerm_mem_stalkRange fan nonempty cone
    (single (Multiplicative.ofAdd m) 1) point member
  rw [chartCoordinateGerm_monomial] at h
  exact h

/-- The actual global sheaf morphism given by multiplication by χ^m. -/
def toricCartierMonomialMap (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (b c : fan.Ray → ℤ) (character : N →+ ℤ)
    (nonnegative : ∀ ρ : fan.Ray,
      0 ≤ c ρ - b ρ + character (fanRayPrimitiveGenerator fan ρ)) :
    letI := toricSchemeIntegral fan nonempty
    (invariantCartierDivisor fan nonempty regular b).sheaf ⟶
      (invariantCartierDivisor fan nonempty regular c).sheaf := by
  letI := toricSchemeIntegral fan nonempty
  exact (toricMonomialCompatibility fan nonempty regular b c character nonnegative).sheafMap ≫
    (Scheme.Modules.pushforwardId fan.algebraicRealization).hom.app
      (invariantCartierDivisor fan nonempty regular c).sheaf

/-- The defining map is literally multiplication by the rational character,
under the genuine Cartier-sheaf inclusions. -/
theorem toricCartierMonomialMap_value (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (b c : fan.Ray → ℤ) (character : N →+ ℤ)
    (nonnegative : ∀ ρ : fan.Ray,
      0 ≤ c ρ - b ρ + character (fanRayPrimitiveGenerator fan ρ))
    (domain : fan.algebraicRealization.Opens) [Nonempty domain]
    (s : letI := toricSchemeIntegral fan nonempty;
      Γ((invariantCartierDivisor fan nonempty regular b).sheaf, domain)) :
    letI := toricSchemeIntegral fan nonempty
    TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv domain
      (Scheme.Modules.Hom.app (invariantCartierDivisor fan nonempty regular c).sheafι domain
        (Scheme.Modules.Hom.app
          (toricCartierMonomialMap fan nonempty regular b c character nonnegative) domain s)) =
    (rationalCharacterUnit fan nonempty character : fan.algebraicRealization.functionField) *
      TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv domain
        (Scheme.Modules.Hom.app (invariantCartierDivisor fan nonempty regular b).sheafι domain s) := by
  letI := toricSchemeIntegral fan nonempty
  have factor := (toricMonomialCompatibility fan nonempty regular b c character nonnegative).sheafMap_ι
  have pointwise := ConcreteCategory.congr_hom
    (congrArg (fun map => Scheme.Modules.Hom.app map domain) factor) s
  change Scheme.Modules.Hom.app (invariantCartierDivisor fan nonempty regular c).sheafι domain
      (Scheme.Modules.Hom.app
        (toricCartierMonomialMap fan nonempty regular b c character nonnegative) domain s) =
    Scheme.Modules.Hom.app (cartierRationalMap (𝟙 fan.algebraicRealization) (by rfl)
      (invariantCartierDivisor fan nonempty regular b)
      (rationalCharacterUnit fan nonempty character : fan.algebraicRealization.functionField))
        domain s at pointwise
  rw [pointwise]
  letI : Nonempty ((𝟙 fan.algebraicRealization) ⁻¹ᵁ domain) := by
    change Nonempty domain
    infer_instance
  simpa only [rationalPullback_id, Scheme.Hom.id_preimage] using
    cartierRationalMap_value (𝟙 fan.algebraicRealization) (by rfl)
      (invariantCartierDivisor fan nonempty regular b)
      (rationalCharacterUnit fan nonempty character : fan.algebraicRealization.functionField)
      domain s

/-- Equality of maps into a Cartier sheaf can be checked in the actual
function field on all nonempty opens. The empty open is handled by the
sheaf's zero section object. -/
theorem cartierSheafHom_ext_nonempty {X : Scheme.{u}} [IsIntegral X]
    (D : TauCeti.AlgebraicGeometry.Scheme.CartierDivisor X) {M : X.Modules}
    {f g : M ⟶ D.sheaf}
    (same : ∀ (U : X.Opens) [Nonempty U] (s : Γ(M, U)),
      TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv U
        (Scheme.Modules.Hom.app D.sheafι U (Scheme.Modules.Hom.app f U s)) =
      TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv U
        (Scheme.Modules.Hom.app D.sheafι U (Scheme.Modules.Hom.app g U s))) : f = g := by
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  apply D.sheafι_app_injective U
  rcases isEmpty_or_nonempty U with hU | hU
  · have empty : U = ⊥ := Opens.coe_eq_empty.mp (Set.isEmpty_coe_sort.mp hU)
    letI := TauCeti.AlgebraicGeometry.Scheme.subsingleton_rationalFunctions U empty
    exact Subsingleton.elim _ _
  · letI := hU
    exact (TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv U).injective (same U s)

/-- The regularity inequality for the composite follows by adding the two
actual ray inequalities. -/
theorem toricMonomialNonnegative_add (fan : Fan i) (b c d : fan.Ray → ℤ)
    (m n : N →+ ℤ)
    (first : ∀ ρ : fan.Ray, 0 ≤ c ρ - b ρ + m (fanRayPrimitiveGenerator fan ρ))
    (second : ∀ ρ : fan.Ray, 0 ≤ d ρ - c ρ + n (fanRayPrimitiveGenerator fan ρ)) :
    ∀ ρ : fan.Ray, 0 ≤ d ρ - b ρ + (m + n) (fanRayPrimitiveGenerator fan ρ) := by
  intro ρ
  have hfirst := first ρ
  have hsecond := second ρ
  simp only [AddMonoidHom.add_apply]
  omega

/-- Composition of the actual global sheaf maps is multiplication of the
actual characters. No matrix representation or composition law is assumed. -/
@[reassoc]
theorem toricCartierMonomialMap_comp (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (b c d : fan.Ray → ℤ) (m n : N →+ ℤ)
    (first : ∀ ρ : fan.Ray, 0 ≤ c ρ - b ρ + m (fanRayPrimitiveGenerator fan ρ))
    (second : ∀ ρ : fan.Ray, 0 ≤ d ρ - c ρ + n (fanRayPrimitiveGenerator fan ρ)) :
    letI := toricSchemeIntegral fan nonempty
    toricCartierMonomialMap fan nonempty regular b c m first ≫
      toricCartierMonomialMap fan nonempty regular c d n second =
    toricCartierMonomialMap fan nonempty regular b d (m + n)
      (toricMonomialNonnegative_add fan b c d m n first second) := by
  letI := toricSchemeIntegral fan nonempty
  apply cartierSheafHom_ext_nonempty (invariantCartierDivisor fan nonempty regular d)
  intro U hU s
  change TauCeti.AlgebraicGeometry.Scheme.rationalFunctionsEquiv U
    (Scheme.Modules.Hom.app (invariantCartierDivisor fan nonempty regular d).sheafι U
      (Scheme.Modules.Hom.app (toricCartierMonomialMap fan nonempty regular c d n second) U
        (Scheme.Modules.Hom.app (toricCartierMonomialMap fan nonempty regular b c m first) U s))) = _
  rw [toricCartierMonomialMap_value, toricCartierMonomialMap_value,
    toricCartierMonomialMap_value, rationalCharacterUnit_add, Units.val_mul]
  ring

/-- Multiplication by the zero character on a Cartier sheaf is its identity. -/
theorem toricCartierMonomialMap_id (fan : Fan i) (nonempty : Nonempty fan.cones)
    (regular : fan.IsRegular) (b : fan.Ray → ℤ) :
    letI := toricSchemeIntegral fan nonempty
    toricCartierMonomialMap fan nonempty regular b b 0 (by intro ρ; simp) =
      𝟙 (invariantCartierDivisor fan nonempty regular b).sheaf := by
  letI := toricSchemeIntegral fan nonempty
  apply cartierSheafHom_ext_nonempty (invariantCartierDivisor fan nonempty regular b)
  intro U hU s
  rw [toricCartierMonomialMap_value, rationalCharacterUnit_zero, Units.val_one, one_mul]
  rfl

end ToricPower
