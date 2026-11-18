module

public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.AlgebraicGeometry.Cover.Open

/-!
# Valuative centers in an actual open cover

Universal closedness extends a genuine valued-field point to its
valuation ring. An open chart containing the closed-point image contains
the whole image of that local spectrum. The factorization below keeps
the original generic point and the original base morphism unchanged.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open AlgebraicGeometry CategoryTheory

namespace PaperVerification.ToricSchemes

/-- A valuative point of a universally closed scheme extends through one
of the actual charts of any given open cover. -/
theorem exists_valuativeLift_into_openCover
    {X Y : Scheme.{u}} (f : X ⟶ Y) [UniversallyClosed f]
    (S : ValuativeCommSq f) (U : X.OpenCover.{v}) :
    ∃ (i : U.I₀) (l : Spec (CommRingCat.of S.R) ⟶ U.X i),
      Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ l ≫ U.f i = S.i₁ ∧
      l ≫ U.f i ≫ f = S.i₂ := by
  have hVal : ValuativeCriterion.Existence f := by
    have h : UniversallyClosed f := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  obtain ⟨l, hl₁, hl₂⟩ := (hVal S).exists_lift
  let i := U.idx (l (IsLocalRing.closedPoint S.R))
  have hi : l (IsLocalRing.closedPoint S.R) ∈ Set.range (U.f i) := U.covers _
  have hsub : Set.range l ⊆ Set.range (U.f i) := by
    rintro _ ⟨x, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint x).map l.continuous).mem_open
      (IsOpenImmersion.isOpen_range (U.f i)) hi
  let lU := IsOpenImmersion.lift (U.f i) l hsub
  have hfac : lU ≫ U.f i = l := IsOpenImmersion.lift_fac (U.f i) l hsub
  refine ⟨i, lU, ?_, ?_⟩
  · rw [hfac]
    exact hl₁
  · rw [← Category.assoc, hfac]
    exact hl₂

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.exists_valuativeLift_into_openCover
