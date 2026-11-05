import Mathlib.Topology.Sheaves.Flasque
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import OAI.AlgebraicGeometry.SheafCohomology.API
import OAI.AlgebraicGeometry.SheafCohomology.ZeroOutside

/-! # Flasque Vanishing -/

namespace OAI.AlgebraicGeometry.SheafCohomology.FlasqueVanishing

open _root_.CategoryTheory _root_.TopologicalSpace _root_.Order
open _root_.CategoryTheory.Limits _root_.Opposite

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Projective

open OAI.AlgebraicGeometry.SheafCohomology.Vanishing.Projective.TopCat

/-!
# Flasque sheaf theory and cohomological vanishing

A sheaf of abelian groups is **flasque** when every restriction map is epi. Such sheaves
have vanishing higher cohomology, which is one of the key inputs to Grothendieck vanishing.

## Main definitions

* `IsFlasqueSheaf` — the flasque predicate.

## Main results

* `epi_app_of_shortExact_flasque`, `isFlasque_X₃_of_shortExact` — flasqueness propagates
 through short exact sequences.
* `isFlasque_of_injective` — every injective sheaf is flasque.
* `sheafH_subsingleton_H1_of_flasque`, `sheafH_subsingleton_of_flasque` — flasque sheaves
 have vanishing `Hⁿ` for `n ≥ 1`.

Generic `Sheaf.H` and `Ext` API lives in `CohomologyAPI.lean`.
-/

universe u

open Abelian Limits

/-! ## Flasque sheaf sub-lemmas

Together they imply `FlasqueVanishing`. Each is a self-contained
statement that can be attacked independently.
-/

/-- A sheaf of abelian groups is **flasque** if all restriction maps are epi.
 This is equivalent to surjectivity of restriction on sections. -/
abbrev IsFlasqueSheaf {X : TopCat.{u}} (F : Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X) : Prop :=
  ∀ {U V : Opens X} (i : U ⟶ V), Epi (F.obj.map i.op)

/-- If `0 → X₁ → X₂ → X₃ → 0` is short exact and every restriction map of the
underlying presheaf `S.X₁.obj` is epi, then `g(U): X₂(U) → X₃(U)` is epi. -/
theorem epi_app_of_shortExact_of_epi_restrictions {X : TopCat.{u}}
    {S : ShortComplex (Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact)
    (hX₁_epi : ∀ {U V : Opens X} (i : U ⟶ V), Epi (S.X₁.obj.map i.op))
    (U : Opens X) :
    Epi (S.g.hom.app (op U)) := by
  let S' : ShortComplex (_root_.TopCat.Sheaf AddCommGrpCat.{u} X) := S
  letI : _root_.TopCat.Sheaf.IsFlasque S'.X₁ := ⟨fun i => hX₁_epi i.unop⟩
  exact _root_.TopCat.Sheaf.IsFlasque.epi_of_shortExact (S := S') (U := U) hS

/-- If `0 → X₁ → X₂ → X₃ → 0` is short exact and `X₁` is flasque, then
`g(U): X₂(U) → X₃(U)` is epi. -/
theorem epi_app_of_shortExact_flasque {X : TopCat.{u}}
    {S : ShortComplex (Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact)
    (hX₁ : IsFlasqueSheaf S.X₁)
    (U : Opens X) :
    Epi (S.g.hom.app (op U)) := by
  exact epi_app_of_shortExact_of_epi_restrictions hS
    (fun {_ _} i ↦ hX₁ i) U

/-- Quotients of flasque sheaves are flasque along a short exact sequence. -/
theorem isFlasque_X₃_of_shortExact {X : TopCat.{u}}
    {S : ShortComplex (Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact)
    (hX₁ : IsFlasqueSheaf S.X₁)
    (hX₂ : IsFlasqueSheaf S.X₂) :
    IsFlasqueSheaf S.X₃ := by
  intro U V j
  have hg_U : Epi (S.g.hom.app (op U)) :=
    epi_app_of_shortExact_of_epi_restrictions hS
      (fun {_ _} i ↦ hX₁ i) U
  have hres₂ : Epi (S.X₂.obj.map j.op) := hX₂ j
  rw [AddCommGrpCat.epi_iff_surjective] at hg_U hres₂ ⊢
  intro z
  obtain ⟨w, hw⟩ := hg_U z
  obtain ⟨x, hx⟩ := hres₂ w
  exact ⟨ConcreteCategory.hom (S.g.hom.app (op V)) x, by
    have := congrArg (· x) (S.g.hom.naturality j.op)
    simp only [AddCommGrpCat.hom_comp] at this
    exact this.symm.trans (by simp [hx, hw])⟩

/-- Injective sheaves are flasque. -/
theorem isFlasque_of_injective {X : TopCat.{u}}
    (I : Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X) [Injective I] : IsFlasqueSheaf I := by
  intro U V i
  rw [AddCommGrpCat.epi_iff_surjective]
  intro s
  obtain ⟨g, hg⟩ := Injective.factors
    (Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt.sHom s) (Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt.openHom (leOfHom i))
  refine ⟨g.hom.app (op V) (Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt.generator V), ?_⟩
  have hi_eq : I.obj.map i.op = I.obj.map (homOfLE (leOfHom i)).op :=
    congr_arg I.obj.map (congr_arg Quiver.Hom.op (Subsingleton.elim _ _))
  rw [hi_eq, ← g.hom.naturality_apply (homOfLE (leOfHom i)).op,
    ← Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt.openHom_val_app_generator]
  change ((Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt.openHom (leOfHom i) ≫ g).hom.app (op U))
    (Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt.generator U) = s
  rw [hg]
  exact Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt.sHom_app_generator s

/-! ## Cohomological vanishing for flasque sheaves -/

/-- `H¹` vanishes for flasque sheaves. -/
theorem sheafH_subsingleton_H1_of_flasque {X : TopCat.{u}}
    (F : Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X) (hF : IsFlasqueSheaf F) :
    Subsingleton (Sheaf.H F 1) := by
  obtain ⟨ip⟩ := EnoughInjectives.presentation F
  let S : ShortComplex (Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X) := ip.shortComplex
  let : Injective S.X₂ := by
    simpa [S] using (inferInstance : Injective S.X₂)
  have hg : Epi (S.g.hom.app (op ⊤)) := by
    simpa [S] using epi_app_of_shortExact_flasque
      (by simpa [S] using ip.shortExact_shortComplex)
      (fun i ↦ by simpa [S] using hF i) ⊤
  simpa [S] using
    API.ProjectiveVanishing.sheafH_subsingleton_H1_of_injective_of_epi_app_top
      (by simpa [S] using ip.shortExact_shortComplex) hg

/-- Flasque sheaves have vanishing higher cohomology. -/
theorem sheafH_subsingleton_of_flasque
    (X : TopCat.{u}) (F : Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X)
    (hF : IsFlasqueSheaf F)
    (n : ℕ) :
    Subsingleton (Sheaf.H F (n + 1)) := by
  induction n generalizing F with
  | zero =>
      exact sheafH_subsingleton_H1_of_flasque F hF
  | succ n ih =>
      obtain ⟨ip⟩ := EnoughInjectives.presentation F
      let S : ShortComplex (Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X) := ip.shortComplex
      let : Injective S.X₂ := by
        simpa [S] using (inferInstance : Injective S.X₂)
      have hX₁ : IsFlasqueSheaf S.X₁ := fun i ↦ by simpa [S] using hF i
      have hX₂ : IsFlasqueSheaf S.X₂ := isFlasque_of_injective S.X₂
      have hX₃ : IsFlasqueSheaf S.X₃ := fun i ↦ by
        simpa [S] using
          (isFlasque_X₃_of_shortExact
            (by simpa [S] using ip.shortExact_shortComplex) hX₁ hX₂) i
      have h₃H : Subsingleton (Sheaf.H S.X₃ (n + 1)) := by
        simpa using (ih S.X₃ hX₃)
      simpa [S] using
        (API.ProjectiveVanishing.sheafH_dimension_shift_of_injective
          (S := S)
          (by simpa [S] using ip.shortExact_shortComplex)
          (n + 1) h₃H)
end Projective

end OAI.AlgebraicGeometry.SheafCohomology.FlasqueVanishing
