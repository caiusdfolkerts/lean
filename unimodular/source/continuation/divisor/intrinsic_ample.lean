module

public import Continuation.Divisor.AnticanonicalBundle
public import Continuation.Divisor.StrictSupportAmple
public import Continuation.Divisor.TrivializationCoordinate

/-!
# Intrinsic ampleness of the anticanonical line bundle

Ampleness below uses the standard affine nonvanishing-open criterion on
ordinary tensor powers. Nonvanishing is the actual stalk-span predicate.
The Cartier calculation is compared with that predicate explicitly.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace Unimodular.NefBig

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open PaperVerification.ToricSchemes PaperVerification.ToricGeometry
open TauCeti.AlgebraicGeometry

section Intrinsic
variable {X : Scheme.{u}}

/-- The ordinary affine nonvanishing-open definition of ampleness.
The invertibility proofs concern the actual tensor powers; they are
witnesses in the conclusion, not additional positivity hypotheses. -/
def IsAmpleModule (M : X.Modules) : Prop :=
  ∃ hInv : ∀ m : ℕ, SheafOfModules.isInvertible X (tensorSheafPower M m),
    CompactSpace X ∧ ∀ x : X, ∃ m : ℕ, 0 < m ∧
      ∃ s : Γ(tensorSheafPower M m, ⊤),
        letI := hInv m
        x ∈ (tensorSheafPower M m).nonvanishingLocus s ∧
          IsAffineOpen ((tensorSheafPower M m).nonvanishingLocus s)

theorem isAmpleModule_of_iso {M N : X.Modules} (e : M ≅ N)
    (hM : IsAmpleModule M) : IsAmpleModule N := by
  obtain ⟨hInv, hcompact, hcover⟩ := hM
  let hN (m : ℕ) : SheafOfModules.isInvertible X (tensorSheafPower N m) :=
    (SheafOfModules.isInvertible X).prop_of_iso (tensorSheafPowerIso e m) (hInv m)
  refine ⟨hN, hcompact, ?_⟩
  intro x
  obtain ⟨m, hm, s, hx, hs⟩ := hcover x
  letI := hInv m
  letI := hN m
  refine ⟨m, hm, (tensorSheafPowerIso e m).hom.app ⊤ s, ?_, ?_⟩
  · simpa only [Scheme.Modules.nonvanishingLocus_hom_app] using hx
  · simpa only [Scheme.Modules.nonvanishingLocus_hom_app] using hs

theorem isAmpleModule_iff_of_iso {M N : X.Modules} (e : M ≅ N) :
    IsAmpleModule M ↔ IsAmpleModule N :=
  ⟨isAmpleModule_of_iso e, isAmpleModule_of_iso e.symm⟩
end Intrinsic

section CartierComparison
variable {X : Scheme.{u}} [IsIntegral X] (C : RationalCartierCocycle X)

/-- The rational local-frame nonvanishing calculation equals the
ordinary stalkwise nonvanishing open of the actual sheaf. -/
theorem cocycle_nonvanishingOpen_eq (s : Γ(C.sheaf, ⊤)) :
    C.nonvanishingOpen s = C.sheaf.nonvanishingLocus s := by
  ext x
  obtain ⟨i, hxi⟩ := C.covers x
  let e := TauCeti.SheafOfModules.freePUnitIsoUnit
    (X.ringCatSheaf.over (C.openSet i)) ≪≫ (C.localFrame i).symm
  have he : Scheme.Modules.trivializationCoordinateIso C.sheaf e = C.localFrame i := by
    exact Scheme.Modules.trivializationCoordinateIso_of_unitIso C.sheaf (C.localFrame i)
  have hc {V : X.Opens} (j : V ⟶ C.openSet i) (q : Γ(C.sheaf, V)) :
      Scheme.Modules.trivializationCoordinate C.sheaf e j q =
        C.localCoordinates i V j.le q := by
    rw [Scheme.Modules.trivializationCoordinate_apply, he]
    rfl
  change x ∈ C.nonvanishingOpen s ↔ x ∈ C.sheaf.nonvanishingLocus s
  rw [C.mem_nonvanishingOpen_iff i s x hxi,
    Scheme.Modules.mem_nonvanishingLocus_iff_of_mem (show x ∈ (⊤ : X.Opens) from trivial)]
  have h := Scheme.Modules.span_germ_eq_top_iff_isUnit C.sheaf e (𝟙 (C.openSet i))
    (C.sheaf.presheaf.map (C.openSet i).leTop.op s) hxi
  have htop : (C.openSet i).leTop =
      homOfLE (show C.openSet i ≤ ⊤ from le_top) := Subsingleton.elim _ _
  rw [htop] at h
  simpa only [hc, TopCat.Presheaf.germ_res_apply,
    RationalCartierCocycle.localCoefficient] using h.symm

/-- The ordinary tensor-power/stalk definition follows from the actual
Cartier section calculation, with every power identified by an isomorphism. -/
theorem isAmpleModule_of_cocycle (hC : C.IsAmple) : IsAmpleModule C.sheaf := by
  let hInv (m : ℕ) : SheafOfModules.isInvertible X (tensorSheafPower C.sheaf m) :=
    (SheafOfModules.isInvertible X).prop_of_iso (C.tensorSheafPowerIso m).symm inferInstance
  refine ⟨hInv, hC.1, ?_⟩
  intro x
  obtain ⟨m, hm, s, hx, hs⟩ := hC.2 x
  letI := hInv m
  let e := (C.tensorSheafPowerIso m).symm
  have he : (tensorSheafPower C.sheaf m).nonvanishingLocus (e.hom.app ⊤ s) =
      (C.pow m).nonvanishingOpen s := by
    rw [Scheme.Modules.nonvanishingLocus_hom_app, cocycle_nonvanishingOpen_eq]
  exact ⟨m, hm, e.hom.app ⊤ s, by simpa only [he] using hx, by simpa only [he] using hs⟩
end CartierComparison

variable {n : ℕ} (F : PaperVerification.ToricGeometry.SmoothCompleteFan n)
  (k : Type u) [Field k]

/-- The intrinsically defined dual of the top Kähler exterior bundle is
ample whenever the actual unit-boundary support is strict. -/
theorem anticanonical_isAmple_of_strictSupport
    (h : F.IsStrictSupport (fun _ => 1)) :
    IsAmpleModule (anticanonicalLineBundle F k).obj := by
  apply isAmpleModule_of_iso (anticanonical_unitBoundaryIso F k).symm
  exact isAmpleModule_of_cocycle _
    (fanCartier_isAmple_of_strictSupport F k (fun _ => 1) (by simpa using h))

#print axioms cocycle_nonvanishingOpen_eq
#print axioms isAmpleModule_of_cocycle
#print axioms anticanonical_isAmple_of_strictSupport
end Unimodular.NefBig
