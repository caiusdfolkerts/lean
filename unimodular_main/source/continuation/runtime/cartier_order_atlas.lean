module

public import Continuation.Runtime.IntrinsicReconstruction

/-!
# Cartier sheaves from local order equations

On a smooth integral scheme, equality of all codimension-one orders makes
the ratio of two nonzero local equations a regular unit. Consequently a
cover by such equations constructs an actual invertible fractional sheaf.
The sign below is the usual one: a generator of `𝒪(D)` has order `-D`.
-/

@[expose] public noncomputable section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace PaperVerification.ToricSchemes

variable {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f]

include f in
/-- On a smooth integral scheme, the ordinary section condition for a
Cartier sheaf is exactly the usual nonnegative-order condition. The proof
uses regularity on entire frame opens, including points of higher
codimension. -/
theorem RationalCartierCocycle.mem_sectionValueRange_iff_orders
    (C : RationalCartierCocycle X) (V : X.Opens) [Nonempty V]
    (r : X.functionField) (hr : r ≠ 0) :
    r ∈ C.toCartierData.sectionValueRange V ↔
      ∀ x ∈ V, 0 ≤ X.ord r x + C.toCartierData.weilCoefficient x := by
  rw [C.mem_sectionValueRange_iff_stalkwise]
  constructor
  · intro h x hx
    obtain ⟨i, hi⟩ := C.covers x
    rw [C.weilCoefficient_eq_neg_generator i x hi]
    by_cases hcodim : Order.coheight x = 1
    · letI : IsIntegrallyClosed (X.presheaf.stalk x) :=
        smooth_stalk_isIntegrallyClosed f x
      have hord := (rationalOrder_nonnegative_iff_regularAt x hcodim
        (r / (C.generator i : X.functionField))
        (div_ne_zero hr (C.generator i).ne_zero)).mpr (h i x hx hi)
      simpa only [rationalOrder_div hr (C.generator i).ne_zero,
        sub_eq_add_neg] using hord
    · simp only [Scheme.ord_eq_zero_of_coheight_neq_one hcodim,
        neg_zero, add_zero, le_refl]
  · intro h i x hx hi
    let W := V ⊓ C.openSet i
    letI : Nonempty W := ⟨⟨x, hx, hi⟩⟩
    have hreg : r / (C.generator i : X.functionField) ∈
        (X.germToFunctionField W).hom.range := by
      apply (smooth_regular_range_iff_orders f W _
        (div_ne_zero hr (C.generator i).ne_zero)).mpr
      intro y hy
      have hyorder := h y hy.1
      rw [C.weilCoefficient_eq_neg_generator i y hy.2] at hyorder
      simpa only [rationalOrder_div hr (C.generator i).ne_zero,
        sub_eq_add_neg] using hyorder
    obtain ⟨a, ha⟩ := hreg
    rw [← ha]
    exact regular_germ_mem_regularAt X W a x ⟨hx, hi⟩

/-- At a nonvanishing point, the order of the section cancels the actual
Cartier coefficient. The statement includes every codimension. -/
theorem RationalCartierCocycle.order_add_weilCoefficient_eq_zero_of_nonvanishing
    (C : RationalCartierCocycle X) (s : Γ(C.sheaf, ⊤)) (x : X)
    (hx : x ∈ C.nonvanishingOpen s) :
    X.ord (C.toCartierData.sectionValue ⊤ s) x +
      C.toCartierData.weilCoefficient x = 0 := by
  obtain ⟨i, hi⟩ := C.covers x
  obtain ⟨hr, hinv⟩ := (C.nonvanishing_iff_value i s x hi).mp hx
  have hreg : C.toCartierData.sectionValue ⊤ s /
      (C.generator i : X.functionField) ∈ regularAtSubring X x := by
    change rationalValue X ⊤ s.val / (C.generator i : X.functionField) ∈ regularAtSubring X x
    exact s.property i ⟨x, trivial⟩ hi
  have hunit : IsRegularUnitAt X x
      (C.toCartierData.sectionValue ⊤ s / (C.generator i : X.functionField)) :=
    ⟨hreg, by simpa only [inv_div] using hinv⟩
  have hord := rationalOrder_zero_of_isRegularUnitAt x _
    (div_ne_zero hr (C.generator i).ne_zero) hunit
  rw [rationalOrder_div hr (C.generator i).ne_zero] at hord
  rw [C.weilCoefficient_eq_neg_generator i x hi]
  simpa only [sub_eq_add_neg] using hord

/-- Construct ordinary Cartier transition data from actual local equations
for a specified coefficient function. -/
def cartierCocycleOfOrderAtlas (d : X → ℤ) {ι : Type u}
    (U : ι → X.Opens) (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (g : ι → X.functionFieldˣ)
    (horder : ∀ i x, x ∈ U i → X.ord (g i : X.functionField) x = -d x) :
    RationalCartierCocycle X where
  index := ι
  openSet := U
  covers := hcover
  generator := g
  transition i j x hxi hxj := by
    let V := U i ⊓ U j
    letI : Nonempty V := ⟨⟨x, hxi, hxj⟩⟩
    obtain ⟨unit, hunit⟩ :=
      (smooth_regular_unit_iff_orders_zero f V
        ((g i : X.functionField) / (g j : X.functionField))
        (div_ne_zero (g i).ne_zero (g j).ne_zero)).mpr (by
          intro y hy
          rw [rationalOrder_div (g i).ne_zero (g j).ne_zero,
            horder i y hy.1, horder j y hy.2, sub_self])
    rw [← hunit]
    exact regular_germ_mem_regularAt X V unit x ⟨hxi, hxj⟩

/-- The constructed Cartier sheaf has exactly the prescribed ordinary
Weil coefficients, with no change of sign or omitted codimension. -/
theorem cartierCocycleOfOrderAtlas_weilCoefficient (d : X → ℤ) {ι : Type u}
    (U : ι → X.Opens) (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (g : ι → X.functionFieldˣ)
    (horder : ∀ i x, x ∈ U i → X.ord (g i : X.functionField) x = -d x) :
    (cartierCocycleOfOrderAtlas f d U hcover g horder).toCartierData.weilCoefficient = d := by
  funext x
  obtain ⟨i, hi⟩ := hcover x
  rw [(cartierCocycleOfOrderAtlas f d U hcover g horder).weilCoefficient_eq_neg_generator
    i x hi]
  change -X.ord (g i : X.functionField) x = d x
  rw [horder i x hi, neg_neg]

include f in
/-- Actual local principality supplies an actual Cartier sheaf. This is
the existence counterpart of the previously proved injectivity of Cartier
divisors into their order functions. -/
theorem exists_cartierData_of_local_orders (d : X → ℤ)
    (hlocal : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ g : X.functionFieldˣ,
      ∀ y ∈ U, X.ord (g : X.functionField) y = -d y) :
    ∃ D : CartierData X, D.weilCoefficient = d := by
  choose U hxU g horder using hlocal
  let C := cartierCocycleOfOrderAtlas f d U (fun x => ⟨x, hxU x⟩) g horder
  exact ⟨C.toCartierData,
    cartierCocycleOfOrderAtlas_weilCoefficient f d U (fun x => ⟨x, hxU x⟩) g horder⟩

end PaperVerification.ToricSchemes
