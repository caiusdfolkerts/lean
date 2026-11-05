module

public import PaperVerification.ToricNormalOrders
public import PaperVerification.ToricSmoothNormal
public import PaperVerification.ToricCartierOrders
public import PaperVerification.ToricCartierRangeEquality

@[expose] public section

/-!
# Cartier divisors are detected by their genuine Weil orders on smooth schemes

Normality is derived from ordinary smoothness over the ground field. The
height-one intersection theorem is applied to actual affine coordinate
rings and their actual stalk localizations. Thus the resulting injectivity
statement concerns actual invertible fractional sheaves on the scheme.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace PaperVerification.ToricSchemes

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- On a normal affine open, regularity is detected at the actual points
of codimension one in that open. -/
theorem normalAffine_regular_iff_codimensionOne (U : X.Opens)
    (hU : IsAffineOpen U) [Nonempty U] [IsIntegrallyClosed Γ(X,U)]
    (z : X.functionField) :
    z ∈ (X.germToFunctionField U).hom.range ↔
      ∀ x∈U, Order.coheight x = 1 → z∈regularAtSubring X x := by
  let R := Γ(X,U)
  letI : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨U,hU⟩
  letI : IsFractionRing R X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  constructor
  · rintro ⟨s,rfl⟩ x hx _
    exact regular_germ_mem_regularAt X U s x hx
  · intro h
    change z ∈ fractionRingImage R X.functionField
    apply (mem_fractionRingImage_iff_heightOne R X.functionField z).mpr
    intro P hP hheight
    letI : P.IsPrime := hP
    let p : Spec (.of R) := ⟨P,hP⟩
    let x : X := hU.fromSpec p
    have hxU : x∈U := by
      change x ∈ (U : Set X)
      rw [← hU.range_fromSpec]
      exact ⟨p,rfl⟩
    have hxheight : Order.coheight x = 1 := by
      calc
        Order.coheight x = Order.coheight p :=
          coheight_eq_of_isOpenImmersion hU.fromSpec
        _ = P.height := (idealHeight_eq_coheight (.of R) p).symm
        _ = 1 := hheight
    letI : Algebra R (X.presheaf.stalk x) :=
      TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x,hxU⟩
    letI : IsLocalization.AtPrime (X.presheaf.stalk x) P :=
      hU.isLocalization_stalk' p hxU
    letI : IsScalarTower R (X.presheaf.stalk x) X.functionField :=
      functionField_isScalarTower X U ⟨x,hxU⟩
    exact (mem_heightOneLocalRing_iff_localization_range R X.functionField
      P (X.presheaf.stalk x) z).mpr (h x hxU hxheight)

variable {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) [Smooth f]

include f

/-- A nonzero rational function on a smooth integral scheme is regular on
an arbitrary open exactly when its orders are nonnegative there. -/
theorem smooth_regular_range_iff_orders (U : X.Opens) [Nonempty U]
    (z : X.functionField) (hz : z ≠ 0) :
    z ∈ (X.germToFunctionField U).hom.range ↔
      ∀ x∈U, 0 ≤ X.ord z x := by
  constructor
  · rintro ⟨s,rfl⟩ x hx
    by_cases hcodim : Order.coheight x=1
    · letI : IsIntegrallyClosed (X.presheaf.stalk x) :=
        smooth_stalk_isIntegrallyClosed f x
      exact (rationalOrder_nonnegative_iff_regularAt x hcodim _ hz).mpr
        (regular_germ_mem_regularAt X U s x hx)
    · simp [Scheme.ord_eq_zero_of_coheight_neq_one hcodim]
  · intro h
    apply (mem_regular_range_iff_stalkwise X U z).mpr
    intro x hx
    obtain ⟨V,hV,hxV,hVU⟩ := exists_isAffineOpen_mem_and_subset (x := x) hx
    letI : Nonempty V := ⟨⟨x,hxV⟩⟩
    letI : IsIntegrallyClosed Γ(X,V) :=
      smooth_affineOpen_isIntegrallyClosed f V hV
    have hzV : z∈(X.germToFunctionField V).hom.range := by
      apply (normalAffine_regular_iff_codimensionOne V hV z).mpr
      intro y hy hcodim
      letI : IsIntegrallyClosed (X.presheaf.stalk y) :=
        smooth_stalk_isIntegrallyClosed f y
      exact (rationalOrder_nonnegative_iff_regularAt y hcodim z hz).mp
        (h y (hVU hy))
    obtain ⟨s,hs⟩ := hzV
    rw [← hs]
    exact regular_germ_mem_regularAt X V s x hxV

/-- Vanishing of every genuine Weil order is equivalent to a genuine
regular unit on the open, including nonaffine opens. -/
theorem smooth_regular_unit_iff_orders_zero (U : X.Opens) [Nonempty U]
    (z : X.functionField) (hz : z ≠ 0) :
    (∃ a : Γ(X,U)ˣ,X.germToFunctionField U (a : Γ(X,U))=z) ↔
      ∀ x∈U,X.ord z x=0 := by
  constructor
  · rintro ⟨a,rfl⟩ x hx
    exact X.ord_of_isUnit a.isUnit hx
  · intro h
    have hpos : z∈(X.germToFunctionField U).hom.range :=
      (smooth_regular_range_iff_orders f U z hz).mpr
        (fun x hx => (h x hx).ge)
    have hneg : z⁻¹∈(X.germToFunctionField U).hom.range := by
      apply (smooth_regular_range_iff_orders f U z⁻¹ (inv_ne_zero hz)).mpr
      intro x hx
      rw [rationalOrder_inv hz,h x hx,neg_zero]
    obtain ⟨a,ha⟩ := hpos
    obtain ⟨b,hb⟩ := hneg
    have hab : a*b=1 := by
      apply X.germToFunctionField_injective U
      rw [map_mul,map_one,ha,hb,mul_inv_cancel₀ hz]
    exact ⟨⟨a,b,hab,by simpa only [mul_comm] using hab⟩,ha⟩

namespace CartierData

/-- Equality of the actual Weil coefficients forces equality of Cartier
divisors as embedded fractional sheaves. Normality is a theorem here,
derived from smoothness, not an additional input about the scheme. -/
theorem equivalent_of_weilCoefficient_eq (D E : CartierData X)
    (hcoeff : D.weilCoefficient = E.weilCoefficient) : D.Equivalent E := by
  let C := D.localCocycle
  let B := E.localCocycle
  have hratios : C.GeneratorRatioRegular B ∧ B.GeneratorRatioRegular C := by
    have hunit : ∀ (i : C.index) (j : B.index)
        (V : X.Opens) [Nonempty V], V≤C.openSet i⊓B.openSet j →
        ∃ a : Γ(X,V)ˣ, X.germToFunctionField V (a : Γ(X,V)) =
          (C.generator i : X.functionField)/(B.generator j : X.functionField) := by
      intro i j V hV hsub
      letI := hV
      letI : Nonempty (invertibleOpen D.locallyFree i) :=
        ⟨⟨i,mem_invertibleOpen D.locallyFree i⟩⟩
      letI : Nonempty (invertibleOpen E.locallyFree j) :=
        ⟨⟨j,mem_invertibleOpen E.locallyFree j⟩⟩
      apply (smooth_regular_unit_iff_orders_zero f V _
        (div_ne_zero (C.generator i).ne_zero (B.generator j).ne_zero)).mpr
      intro x hx
      rw [rationalOrder_div (C.generator i).ne_zero (B.generator j).ne_zero]
      have heq := congrFun hcoeff x
      rw [D.weilCoefficient_eq_neg_frameOrder
          (invertibleFrame D.locallyFree i) (hsub hx).1,
        E.weilCoefficient_eq_neg_frameOrder
          (invertibleFrame E.locallyFree j) (hsub hx).2] at heq
      change -X.ord (C.generator i : X.functionField) x =
        -X.ord (B.generator j : X.functionField) x at heq
      omega
    constructor
    · intro i j x hxi hxj
      let V := C.openSet i⊓B.openSet j
      letI : Nonempty V := ⟨⟨x,hxi,hxj⟩⟩
      obtain ⟨a,ha⟩ := hunit i j V le_rfl
      rw [← ha]
      exact regular_germ_mem_regularAt X V a x ⟨hxi,hxj⟩
    · intro j i x hxj hxi
      let V := C.openSet i⊓B.openSet j
      letI : Nonempty V := ⟨⟨x,hxi,hxj⟩⟩
      obtain ⟨a,ha⟩ := hunit i j V le_rfl
      have hinv : X.germToFunctionField V ((a⁻¹ : Γ(X,V)ˣ) : Γ(X,V)) =
          (B.generator j : X.functionField)/(C.generator i : X.functionField) := by
        have hmul := congrArg (X.germToFunctionField V) a.val_inv
        rw [map_mul,map_one,ha] at hmul
        change (C.generator i : X.functionField) / (B.generator j : X.functionField) *
          X.germToFunctionField V ((a⁻¹ : Γ(X,V)ˣ) : Γ(X,V)) = 1 at hmul
        apply mul_left_cancel₀
          (div_ne_zero (C.generator i).ne_zero (B.generator j).ne_zero)
        rw [hmul]
        field_simp
      rw [← hinv]
      exact regular_germ_mem_regularAt X V (a⁻¹ : Γ(X,V)ˣ) x ⟨hxi,hxj⟩
  exact D.equivalent_trans B.toCartierData E
    (D.equivalent_trans C.toCartierData B.toCartierData
      D.equivalent_localCocycle
      (C.equivalent_of_generatorRatios B hratios.1 hratios.2))
    (E.equivalent_symm B.toCartierData E.equivalent_localCocycle)

end CartierData

end PaperVerification.ToricSchemes
