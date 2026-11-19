module

public import ToricPower.ArrangementShrunkSupportDetection

/-!
# A shifted scalar test detects the actual shrunk inverse branch

The maximal cohomological support cell supplies the genuine local point
model. On the complete closed carrier, the specified inverse branch
pulls it back to the actual affine slice. The scalar test then detects
the original unbounded source and returns through the actual closed
restriction/extension adjunction.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (k : Type) [Field k]
  (c : UniversalIncidenceObject A) (P : UniversalIncidenceObject A → Prop)
  (downP : Antitone P)
  (ell : ℕ) (positive : 0 < ell) (u : Fin n → ℤ)
  (inside : ∀ d : UniversalIncidenceObject A, P d →
    powerInverseBranchPoint ell u (cellCenter (augmentedForms A) d.2) ∈
      localStar (augmentedForms A) (cellCenter (augmentedForms A) c.2))

local instance shrunkShiftedDerivedScalar : HasDerivedCategory.{1} (ModuleCat.{0} k) :=
  HasDerivedCategory.standard _
local instance shrunkShiftedDerivedFull :
    HasDerivedCategory.{1} (UniversalIncidenceObject A ⥤ ModuleCat.{0} k) :=
  HasDerivedCategory.standard _
local instance shrunkShiftedDerivedClosed :
    HasDerivedCategory.{1} ({d : UniversalIncidenceObject A // P d} ⥤ ModuleCat.{0} k) :=
  HasDerivedCategory.standard _
local instance shrunkShiftedDerivedStar :
    HasDerivedCategory.{1} (UniversalFaceStar A c ⥤ ModuleCat.{0} k) :=
  HasDerivedCategory.standard _

variable (selected : Set (Fin s ⊕ Fin n))
  (direction : cellDirection (augmentedForms A) c.2.val.2 =
    arrangementZeroSlice (augmentedForms A) selected)
  (m v₀ : Fin n → ℤ)
  (center : cellCenter (augmentedForms A) c.2 - latticeLift v₀ ∈
    arrangementZeroSlice (augmentedForms A) selected)
  (compatible : latticeLift u + latticeLift m - (ell : ℝ) • latticeLift v₀ ∈
    arrangementZeroSlice (augmentedForms A) selected)

include direction center compatible inside downP in
/-- The conclusion is a morphism from the full actual inverse-branch
pullback, with no degree or dimension restriction on its coefficients. -/
theorem exists_nonzero_from_shrunk_branch_shifted_test
    (E K : CochainComplex (UniversalIncidenceObject A ⥤ ModuleCat.{0} k) ℤ)
    (nonzero : ¬ (E.asFunctor.obj c).Acyclic)
    (maximal : ∀ d : UniversalIncidenceObject A,
      ¬ (E.asFunctor.obj d).Acyclic → d.1 ≤ c.1)
    (targetSupport : ∀ d : UniversalIncidenceObject A, ¬ P d →
      ((((evaluation (UniversalIncidenceObject A) (ModuleCat.{0} k)).obj d).mapHomologicalComplex (.up ℤ)).obj K).Acyclic)
    (r : ℤ)
    (test : (Cellular.closedConstantFunctor k
      (fun d : {d : UniversalIncidenceObject A // P d} => universalAffineSliceSupport A selected m d.val)
      (fun _ _ h => universalAffineSliceSupport_downward A selected m h)).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{0} k) 0).obj (ModuleCat.of k k)) ⟶
      ((Cellular.closedFaceRestriction k P).mapDerivedCategory.obj (DerivedCategory.Q.obj K))⟦r⟧)
    (testNonzero : test ≠ 0) :
    ∃ q : ℤ, ∃ f :
      (ElementPushdown.baseRestriction (powerInverseBranchFunctor A ell positive u)
        (D := ModuleCat.{0} k)).mapDerivedCategory.obj (DerivedCategory.Q.obj E) ⟶
          (DerivedCategory.Q.obj K)⟦q⟧, f ≠ 0 := by
  let star := ((universalFaceStarRestriction A k c).mapHomologicalComplex (.up ℤ)).obj E
  have vanishes : ∀ d : UniversalFaceStar A c, d ≠ universalFaceStarPoint A c →
      ((((evaluation (UniversalFaceStar A c) (ModuleCat.{0} k)).obj d).mapHomologicalComplex (.up ℤ)).obj star).Acyclic := by
    intro d hd
    change (E.asFunctor.obj d.val).Acyclic
    by_contra nonzeroD
    have different : c ≠ d.val := fun same => hd (Subtype.ext same.symm)
    exact (not_lt_of_ge (maximal d.val nonzeroD))
      (universalIncidence_dimension_lt A d.property different)
  obtain ⟨q,f,hf⟩ := Cellular.exists_nonzero_from_point_pullback k
    (fun d : {d : UniversalIncidenceObject A // P d} => universalAffineSliceSupport A selected m d.val)
    (fun _ _ h => universalAffineSliceSupport_downward A selected m h)
    (shrunkSupportFaceStar A c P ell positive u inside) (universalFaceStarPoint A c)
    (shrunkSupport_pointBelow_iff A c P selected direction ell positive u m v₀ center compatible inside)
    (universalFaceStar_incoming A c) star vanishes nonzero
    (((Cellular.closedFaceRestriction k P).mapDerivedCategory.obj (DerivedCategory.Q.obj K))⟦r⟧)
    test testNonzero
  let factor := shrunkBranchSupportDerivedIso A k c P ell positive u inside E
  let T := (Cellular.closedFaceRestriction k P).mapDerivedCategory.obj (DerivedCategory.Q.obj K)
  let shifts := ((shiftFunctorAdd _ r q).app T).symm
  have nonzeroRestricted : factor.hom ≫ f ≫ shifts.hom ≠ 0 := by
    intro zero
    apply hf
    rw [← cancel_epi factor.hom,← cancel_mono shifts.hom,Category.assoc,comp_zero,zero_comp]
    exact zero
  obtain ⟨g,hg⟩ := Cellular.extend_shifted_nonzero_from_closed_support k P downP K
    targetSupport _ (r+q) (factor.hom ≫ f ≫ shifts.hom) nonzeroRestricted
  exact ⟨r+q,g,hg⟩


end ToricPower.IntegralArrangement

end
