module

public import ToricPower.CechMeetInjectiveAssembly

/-!
# Exact Čech rows for an actual open direct image

For a sheaf pushed forward from a member of the cover, restriction to
that member is invertible on every open. The usual anchor contraction
therefore solves every positive Čech cocycle. This applies to arbitrary
coefficients on the open; no flasqueness or finiteness of those
coefficients is assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open TopologicalSpace Opposite
open BondalThomsen.FiniteAffineCechHigherComparison
open BondalThomsen.FiniteAffineCechFlasqueAcyclicity
open BondalThomsen.FiniteAffineCechHigherFlasqueAcyclicity

namespace ToricPower

universe u

section Anchor

variable {X : Scheme.{u}} {I : Type u}

/-- Invertible restrictions to one cover member give the actual
positive-degree Čech factorization, by anchor insertion. -/
theorem cech_exactAt_of_anchor_restrictions (U : I → X.Opens) (a : I)
    (M : X.Modules)
    (localM : ∀ V : X.Opens, Function.Bijective
      (sectionRestriction M (show U a ⊓ V ≤ V from inf_le_right)))
    (n : ℕ) : (schemeCechComplex U M).ExactAt (n+1) := by
  classical
  apply (HomologicalComplex.exactAt_iff' _ n (n+1) (n+2) (by simp) (by simp)).mpr
  apply (ShortComplex.ab_exact_iff _).mpr
  intro z hz
  let values := fun t : Fin (n+1) → I =>
    (localM (cechIntersection U n t)).surjective
      (cechLocalAnchorValue U a M n z t)
  let y := cechOfSections U M n (fun t => (values t).choose)
  have hy (t : Fin (n+1) → I) :
      cechRestrictedCoordinate U M n y (U a) t = cechLocalAnchorValue U a M n z t := by
    dsimp only [cechRestrictedCoordinate, y]
    rw [cechOfSections_coordinate]
    exact (values t).choose_spec
  refine ⟨y, ?_⟩
  apply cechCoordinate_ext
  intro t
  apply (localM (cechIntersection U (n+1) t)).injective
  exact cechLocalAnchor_cycle_coboundary U a M n z hz y hy t

/-- Direct image from an open has literally identical sections before
and after intersecting with that open. -/
theorem openPushforward_sectionRestriction_bijective
    (U : X.Opens) (M : U.toScheme.Modules) (V : X.Opens) :
    Function.Bijective (sectionRestriction ((Scheme.Modules.pushforward U.ι).obj M)
      (show U ⊓ V ≤ V from inf_le_right)) := by
  have eq : (Opens.map U.ι.base).obj (U ⊓ V) = (Opens.map U.ι.base).obj V := by
    change U.ι ⁻¹ᵁ (U ⊓ V) = U.ι ⁻¹ᵁ V
    simp only [Scheme.Hom.preimage_inf, U.ι_preimage_self, top_inf_eq]
  have arrow : (Opens.map U.ι.base).map (homOfLE (show U ⊓ V ≤ V from inf_le_right)) =
      eqToHom eq := Subsingleton.elim _ _
  change Function.Bijective
    (M.presheaf.map ((Opens.map U.ι.base).map
      (homOfLE (show U ⊓ V ≤ V from inf_le_right))).op)
  rw [arrow]
  exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance

/-- The complete ordered Čech complex of an actual open direct image
has no positive cohomology. -/
theorem cech_openPushforward_exactAt_positive (U : I → X.Opens) (a : I)
    (M : (U a).toScheme.Modules) (n : ℕ) :
    (schemeCechComplex U ((Scheme.Modules.pushforward (U a).ι).obj M)).ExactAt (n+1) :=
  cech_exactAt_of_anchor_restrictions U a _
    (openPushforward_sectionRestriction_bijective (U a) M) n

end Anchor

namespace FiniteCech

variable {B : Type} [SemilatticeInf B]
  (k : Type) [Field k] (X : Scheme) [X.Over (Spec (.of k))]
  (opens : B ⥤ X.Opens)
  (meetEq : ∀ (q : ℕ) (t : Fin (q+1) → B),
    cechIntersection opens.obj q t = opens.obj (tupleMeet t))

include meetEq in
/-- The actual section comparison transfers the anchor contraction to
the scalar-linear tuple-projective coefficient complex. -/
theorem meetTuple_openPushforward_exactAt_positive (a : B)
    (M : (opens.obj a).toScheme.Modules) (n : ℕ) :
    (tupleCoefficientComplex k
      (meetChartSections k X opens ((Scheme.Modules.pushforward (opens.obj a).ι).obj M))).ExactAt
        (n+1) := by
  have h := (cech_openPushforward_exactAt_positive opens.obj a M n).of_iso
    (meetCechComplexForgetIso k X opens meetEq
      ((Scheme.Modules.pushforward (opens.obj a).ι).obj M))
  rw [HomologicalComplex.exactAt_iff' _ n (n+1) (n+2) (by simp) (by simp)] at h ⊢
  exact (ShortComplex.exact_map_iff_of_faithful _
    (forget₂ (ModuleCat k) AddCommGrpCat)).mp h

/-- The genuine homotopy equivalence transfers exactness to the finite
resolution, retaining all degrees of the ordinary Čech source. -/
theorem finiteCoefficient_exactAt_of_tuple
    (F : Bᵒᵖ ⥤ ModuleCat k) (n : ℕ)
    (h : (tupleCoefficientComplex k F).ExactAt n) :
    (projectiveCoefficientComplex k (finiteTupleResolution k) F).ExactAt n := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact ((finiteCoefficientComparison k F).toHomologyIso n).isZero_iff.mp h.isZero_homology

include meetEq in
/-- Every local coefficient row needed by finite unbounded Čech
assembly is proved for an actual affine-open direct image. -/
theorem meetFinite_openPushforward_exactAt_positive (a : B)
    (M : (opens.obj a).toScheme.Modules) (n : ℕ) :
    (projectiveCoefficientComplex k (finiteTupleResolution k)
      (meetChartSections k X opens ((Scheme.Modules.pushforward (opens.obj a).ι).obj M))).ExactAt
        (n+1) :=
  finiteCoefficient_exactAt_of_tuple k _ (n+1)
    (meetTuple_openPushforward_exactAt_positive k X opens meetEq a M n)

end FiniteCech

end ToricPower

end
