module

public import ToricPower.ArrangementShrunkSlice
public import ToricPower.PointClosedPullback

/-!
# The actual point model becomes the prescribed closed affine slice

On the whole chosen support, a sufficiently small inverse branch lands
in the actual upper face star. Its incoming incidence to the base cell
is equivalent to the affine-slice equation. The coefficient comparison
below is an isomorphism of whole functors, retaining all face maps.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Set

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)
  (c : UniversalIncidenceObject A) (P : UniversalIncidenceObject A → Prop)
  (selected : Set (Fin s ⊕ Fin n))
  (direction : cellDirection (augmentedForms A) c.2.val.2 =
    arrangementZeroSlice (augmentedForms A) selected)
  (ell : ℕ) (positive : 0 < ell) (u m v₀ : Fin n → ℤ)
  (center : cellCenter (augmentedForms A) c.2 - latticeLift v₀ ∈
    arrangementZeroSlice (augmentedForms A) selected)
  (compatible : latticeLift u + latticeLift m - (ell : ℝ) • latticeLift v₀ ∈
    arrangementZeroSlice (augmentedForms A) selected)
  (inside : ∀ d : UniversalIncidenceObject A, P d →
    powerInverseBranchPoint ell u (cellCenter (augmentedForms A) d.2) ∈
      localStar (augmentedForms A) (cellCenter (augmentedForms A) c.2))

include direction center compatible in
/-- The original incidence-to-point condition equals the complete
closed affine-slice support on every retained cell. -/
theorem shrunkSupport_pointBelow_iff (d : {d : UniversalIncidenceObject A // P d}) :
    (shrunkSupportFaceStar A c P ell positive u inside).obj d ≤ universalFaceStarPoint A c ↔
      universalAffineSliceSupport A selected m d.val := by
  have star := ((shrunkSupportFaceStar A c P ell positive u inside).obj d).property
  have equation := inverseBranch_eq_cell_iff_affineSlice A c d.val selected direction
    ell positive u m v₀ center compatible (inside d.val d.property)
  change powerInverseBranchCell A ell u d.val ≤ c ↔ _
  constructor
  · intro below
    exact equation.mp (universalIncidence_antisymm A below star)
  · intro supported
    rw [equation.mpr supported]

/-- This is the full coefficient-functor isomorphism used by the
unbounded scalar-retract detection argument. -/
def shrunkSupportPointClosedIso (k : Type) [Field k] :
    Cellular.pointCoinducedFunctor k (universalFaceStarPoint A c) ⋙
        ElementPushdown.baseRestriction
          (shrunkSupportFaceStar A c P ell positive u inside) (D := ModuleCat.{0} k) ≅
      Cellular.closedConstantFunctor k
        (fun d : {d : UniversalIncidenceObject A // P d} =>
          universalAffineSliceSupport A selected m d.val)
        (fun _ _ h => universalAffineSliceSupport_downward A selected m h) :=
  Cellular.pointPullbackClosedIso k _ _
    (shrunkSupportFaceStar A c P ell positive u inside) (universalFaceStarPoint A c)
    (shrunkSupport_pointBelow_iff A c P selected direction ell positive u m v₀ center compatible inside)

end ToricPower.IntegralArrangement

end
