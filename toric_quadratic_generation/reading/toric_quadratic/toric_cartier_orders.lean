module

public import PaperVerification.ToricCartierPresentation
public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic

@[expose] public section

/-!
# Orders and degrees of actual Cartier divisors

The coefficient is computed using Mathlib's order in the actual local ring.
Since our local generators generate `O(D)`, their orders have the opposite
sign from the coefficients of `D`. Independence of the chosen frame follows
from its regular-unit transition function. The construction descends through
the equivalence of embedded fractional sheaves.

The cycle constructor below requires a proof of local finiteness. Thus the
definition of degree cannot silently replace an infinite divisor by a finite
sum or treat a nonproper curve as a proper curve. In the applications the
support and the actual residue degrees are computed on the invariant curve.
-/

noncomputable section

universe u

open CategoryTheory TopologicalSpace AlgebraicGeometry

namespace PaperVerification.ToricSchemes

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

theorem rationalOrder_one (x : X) : X.ord (1 : X.functionField) x = 0 := by
  letI : Nonempty (⊤ : X.Opens) := ⟨⟨x,trivial⟩⟩
  simpa only [map_one] using
    X.ord_of_isUnit (U := ⊤) (f := (1 : Γ(X,⊤))) isUnit_one
      (x := x) (show x ∈ (⊤ : X.Opens) from trivial)

theorem rationalOrder_inv {r : X.functionField} (hr : r ≠ 0) (x : X) :
    X.ord r⁻¹ x = - X.ord r x := by
  have h := X.ord_mul (x := x) hr (inv_ne_zero hr)
  rw [mul_inv_cancel₀ hr,rationalOrder_one] at h
  omega

theorem rationalOrder_div {r s : X.functionField}
    (hr : r ≠ 0) (hs : s ≠ 0) (x : X) :
    X.ord (r/s) x = X.ord r x - X.ord s x := by
  rw [div_eq_mul_inv,X.ord_mul hr (inv_ne_zero hs),rationalOrder_inv hs]
  rfl

theorem rationalOrder_pow {r : X.functionField} (hr : r ≠ 0)
    (n : ℕ) (x : X) : X.ord (r^n) x = (n : ℤ) * X.ord r x := by
  induction n with
  | zero => simp [rationalOrder_one]
  | succ n ih =>
      rw [pow_succ,X.ord_mul (pow_ne_zero n hr) hr,ih]
      push_cast
      ring

theorem rationalOrder_zpow {r : X.functionField} (hr : r ≠ 0)
    (n : ℤ) (x : X) : X.ord (r^n) x = n * X.ord r x := by
  cases n with
  | ofNat n => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using rationalOrder_pow hr n x
  | negSucc n =>
      rw [zpow_negSucc,rationalOrder_inv (pow_ne_zero _ hr),rationalOrder_pow hr,
        Int.negSucc_eq]
      push_cast
      ring

namespace CartierData

variable (D E : CartierData X)

/-- The order of an actual rational frame is independent of the frame at
every point in the overlap. -/
theorem frameOrder_eq {U W : X.Opens} [Nonempty U] [Nonempty W]
    (e : D.Frame U) (f : D.Frame W) {x : X} (hxU : x∈U) (hxW : x∈W) :
    X.ord (D.frameRationalGenerator e) x =
      X.ord (D.frameRationalGenerator f) x := by
  let V : X.Opens := U⊓W
  letI : Nonempty V := ⟨⟨x,hxU,hxW⟩⟩
  obtain ⟨a,ha⟩ := D.exists_frameTransitionUnit e f
    (V := V) inf_le_left inf_le_right
  have h := X.ord_of_isUnit (U := V) a.isUnit (x := x) ⟨hxU,hxW⟩
  rw [ha,rationalOrder_div (D.frameRationalGenerator_ne_zero e)
    (D.frameRationalGenerator_ne_zero f)] at h
  omega

/-- The actual Weil coefficient of a Cartier divisor. At noncodimension-one
points the value is zero, as in Mathlib's order function. -/
def weilCoefficient (x : X) : ℤ :=
  - X.ord (D.localCocycle.generator x : X.functionField) x

/-- Any actual local frame computes the coefficient, not only the selected
frame used in the definition. -/
theorem weilCoefficient_eq_neg_frameOrder {U : X.Opens} [Nonempty U]
    (e : D.Frame U) {x : X} (hxU : x∈U) :
    D.weilCoefficient x = -X.ord (D.frameRationalGenerator e) x := by
  let W := invertibleOpen D.locallyFree x
  letI : Nonempty W := ⟨⟨x,mem_invertibleOpen D.locallyFree x⟩⟩
  change -X.ord (D.frameRationalGenerator (invertibleFrame D.locallyFree x)) x = _
  rw [D.frameOrder_eq (invertibleFrame D.locallyFree x) e
    (mem_invertibleOpen D.locallyFree x) hxU]

@[simp] theorem weilCoefficient_eq_zero_of_coheight_ne_one {x : X}
    (hx : Order.coheight x ≠ 1) : D.weilCoefficient x = 0 := by
  simp [weilCoefficient,Scheme.ord_eq_zero_of_coheight_neq_one hx]

/-- Frames of equivalent embedded fractional sheaves differ by an actual
regular unit. This conclusion uses the embedding-preserving equivalence,
not merely an isomorphism of the underlying line bundles. -/
theorem exists_equivalentFrameTransitionUnit (hDE : D.Equivalent E)
    {U W V : X.Opens} [Nonempty U] [Nonempty W] [Nonempty V]
    (e : D.Frame U) (f : E.Frame W) (hVU : V≤U) (hVW : V≤W) :
    ∃ a : Γ(X,V)ˣ, X.germToFunctionField V (a : Γ(X,V)) =
      D.frameRationalGenerator e / E.frameRationalGenerator f := by
  have hD : D.frameRationalGenerator e ∈ E.sectionValueRange V := by
    rw [← D.equivalent_sectionValueRange E hDE V]
    exact ⟨D.frameGenerator e V hVU,D.sectionValue_frameGenerator e hVU⟩
  have hE : E.frameRationalGenerator f ∈ D.sectionValueRange V := by
    rw [D.equivalent_sectionValueRange E hDE V]
    exact ⟨E.frameGenerator f V hVW,E.sectionValue_frameGenerator f hVW⟩
  obtain ⟨a,ha⟩ := (E.mem_sectionValueRange_iff f hVW _).mp hD
  obtain ⟨b,hb⟩ := (D.mem_sectionValueRange_iff e hVU _).mp hE
  have hab : a*b=1 := by
    apply X.germToFunctionField_injective V
    rw [map_mul,map_one]
    apply mul_right_cancel₀ (D.frameRationalGenerator_ne_zero e)
    rw [mul_assoc,hb,ha,one_mul]
  let aUnit : Γ(X,V)ˣ := ⟨a,b,hab,by simpa only [mul_comm] using hab⟩
  exact ⟨aUnit,(eq_div_iff (E.frameRationalGenerator_ne_zero f)).mpr ha⟩

theorem equivalent_weilCoefficient (hDE : D.Equivalent E) :
    D.weilCoefficient = E.weilCoefficient := by
  funext x
  let U := invertibleOpen D.locallyFree x
  let W := invertibleOpen E.locallyFree x
  let V : X.Opens := U⊓W
  have hxU : x∈U := mem_invertibleOpen D.locallyFree x
  have hxW : x∈W := mem_invertibleOpen E.locallyFree x
  letI : Nonempty U := ⟨⟨x,hxU⟩⟩
  letI : Nonempty W := ⟨⟨x,hxW⟩⟩
  letI : Nonempty V := ⟨⟨x,hxU,hxW⟩⟩
  let e := invertibleFrame D.locallyFree x
  let f := invertibleFrame E.locallyFree x
  obtain ⟨a,ha⟩ := D.exists_equivalentFrameTransitionUnit E hDE e f
    (V := V) inf_le_left inf_le_right
  have h := X.ord_of_isUnit (U := V) a.isUnit (x := x) ⟨hxU,hxW⟩
  rw [ha,rationalOrder_div (D.frameRationalGenerator_ne_zero e)
    (E.frameRationalGenerator_ne_zero f)] at h
  rw [D.weilCoefficient_eq_neg_frameOrder e hxU,
    E.weilCoefficient_eq_neg_frameOrder f hxW]
  omega

/-- The actual Weil cycle, provided its coefficients have locally finite
support. The coefficients are already fixed by the actual local orders. -/
def weilCycle (h : LocallyFiniteSupport D.weilCoefficient) :
    AlgebraicCycle X ℤ where
  toFun := D.weilCoefficient
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' x _ := h x

@[simp] theorem weilCycle_apply
    (h : LocallyFiniteSupport D.weilCoefficient) (x : X) :
    D.weilCycle h x = D.weilCoefficient x := rfl

theorem weilCycle_isWeilDivisor
    (h : LocallyFiniteSupport D.weilCoefficient) :
    AlgebraicCycle.IsWeilDivisor (D.weilCycle h) := by
  intro x hx
  by_contra hcodim
  exact hx (D.weilCoefficient_eq_zero_of_coheight_ne_one hcodim)

/-- Finite support is sufficient, without a separatedness or a T1-space
assumption. This is useful for an explicitly computed invariant curve. -/
theorem locallyFiniteSupport_weilCoefficient_of_finite
    (h : (Function.support D.weilCoefficient).Finite) :
    LocallyFiniteSupport D.weilCoefficient := by
  intro x
  exact ⟨Set.univ,Filter.univ_mem,by simpa only [Set.univ_inter] using h⟩

/-- Degree uses the actual residue degrees of the structure morphism. -/
def degree {Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace X]
    (h : LocallyFiniteSupport D.weilCoefficient) : ℤ :=
  AlgebraicCycle.degree f (D.weilCycle h)

theorem degree_eq_finsum {Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace X]
    (h : LocallyFiniteSupport D.weilCoefficient) :
    D.degree f h = ∑ᶠ x, f.residueDegree x • D.weilCoefficient x := rfl

theorem degree_eq_sum_of_support_subset {Y : Scheme.{u}} (f : X ⟶ Y)
    [CompactSpace X] (h : LocallyFiniteSupport D.weilCoefficient)
    (s : Finset X) (hs : Function.support D.weilCoefficient ⊆ s) :
    D.degree f h = ∑ x ∈ s, f.residueDegree x • D.weilCoefficient x := by
  rw [degree_eq_finsum]
  apply finsum_eq_finsetSum_of_support_subset
  intro x hx
  apply hs
  intro hz
  exact hx (by simp [hz])

theorem equivalent_degree (hDE : D.Equivalent E) {Y : Scheme.{u}}
    (f : X ⟶ Y) [CompactSpace X]
    (hD : LocallyFiniteSupport D.weilCoefficient)
    (hE : LocallyFiniteSupport E.weilCoefficient) :
    D.degree f hD = E.degree f hE := by
  rw [degree_eq_finsum,degree_eq_finsum,D.equivalent_weilCoefficient E hDE]

end CartierData

namespace CartierDivisor

/-- Weil coefficients are independent of the presentation of a Cartier
divisor as an invertible embedded fractional sheaf. -/
def weilCoefficient : CartierDivisor X → X → ℤ :=
  Quotient.lift CartierData.weilCoefficient
    (fun _ _ h => CartierData.equivalent_weilCoefficient _ _ h)

@[simp] theorem weilCoefficient_ofData (D : CartierData X) :
    weilCoefficient (ofData D) = D.weilCoefficient := rfl

end CartierDivisor

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.CartierData.equivalent_weilCoefficient
#print axioms PaperVerification.ToricSchemes.CartierData.equivalent_degree
