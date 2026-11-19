/-
Adapted from Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective.
Copyright (c) 2025 Nailin Guan. Released under Apache 2.0 license.
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.FiveLemma
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Exact inclusions preserve Ext from a fixed acyclic source

For a fully faithful exact functor, full preservation of injective objects
is stronger than needed to compare Ext out of one fixed source. It suffices
that the images of actual injectives have vanishing positive Ext from that
source. The proof uses the actual map on Ext and the actual long exact
sequences, applying the additive right-exact five lemma in each degree.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace ToricPower

universe u v u' v' w w'

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.Full] [F.Faithful] [HasExt.{w} C] [HasExt.{w'} D] [EnoughInjectives C]

attribute [local simp] Ext.mapExactFunctor_comp Ext.mapExactFunctor_mk₀
  Ext.mapExactFunctor_extClass
attribute [local instance] Ext.subsingleton_of_injective

/-- A fixed-source comparison theorem whose acyclicity premise refers only
to images of actual injective objects, not to an assumed derived equivalence. -/
theorem mapExt_bijective_of_injective_images_acyclic (P : C)
    (hacyclic : ∀ (J : C), Injective J → ∀ n : ℕ,
      Subsingleton (Ext.{w'} (F.obj P) (F.obj J) (n+1)))
    (M : C) (n : ℕ) : Function.Bijective (F.mapExtAddHom P M n) := by
  induction n generalizing M with
  | zero =>
    simpa [Ext.mapExactFunctor₀] using
      ⟨Functor.Faithful.map_injective, Functor.Full.map_surjective⟩
  | succ n ih =>
    let I : InjectivePresentation M := Classical.arbitrary _
    let S := ShortComplex.mk _ _ (cokernel.condition I.f)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    letI : Subsingleton (Ext.{w'} (F.obj P) (S.map F).X₂ (n+1)) :=
      hacyclic I.J I.injective n
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact _ _ _ _
      (F.mapExtAddHom P S.X₂ n) (F.mapExtAddHom P S.X₃ n)
      (F.mapExtAddHom P S.X₁ (n+1))
      (by cat_disch) (by cat_disch)
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' P hS n (n+1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' (F.obj P) (hS.map F) n (n+1) rfl))
      (ih _).surjective (ih _)
      (fun x => Ext.covariant_sequence_exact₁ _ hS x (by subsingleton) rfl)
      (fun y => Ext.covariant_sequence_exact₁ _ (hS.map F) y (by subsingleton) rfl)

end ToricPower

end
