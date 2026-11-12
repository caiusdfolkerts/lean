module

public import ToricPower.ExtEffacement
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective

/-!
# Extension classes under a coherent lifting condition

An exact fully faithful functor induces bijections on every Ext group if
epimorphisms onto its image can be dominated by epimorphisms from its image.
No projectivity, injectivity, or derived full faithfulness is assumed.
-/

@[expose] public noncomputable section

set_option maxHeartbeats 1000000

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace ToricPower

universe u v u' v' w w'

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]

/-- Every epimorphism onto an image object has a further epimorphic
composite whose source is again an image object. -/
def HasEpimorphismLifts (F : C ⥤ D) : Prop :=
  ∀ (X : C) (P : D) (p : P ⟶ F.obj X), Epi p →
    ∃ (Y : C) (q : F.obj Y ⟶ P), Epi (q ≫ p)

variable (F : C ⥤ D) [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.Full] [F.Faithful] [HasExt.{w} C] [HasExt.{w'} D]

attribute [local simp] Ext.mapExactFunctor_comp Ext.mapExactFunctor_mk₀
  Ext.mapExactFunctor_extClass

/-- The epimorphism-lifting criterion for preservation of all Ext groups.
The proof effaces an individual class and then uses the actual long exact
sequence of Ext. -/
theorem mapExt_bijective_of_epimorphism_lifts
    (lifting : HasEpimorphismLifts F) (X Y : C) (n : ℕ) :
    Function.Bijective (F.mapExtAddHom X Y n) := by
  induction n generalizing X Y with
  | zero =>
      simpa [Ext.mapExactFunctor₀] using
        ⟨Functor.Faithful.map_injective, Functor.Full.map_surjective⟩
  | succ n ih =>
      constructor
      · apply (injective_iff_map_eq_zero (F.mapExtAddHom X Y (n + 1))).mpr
        intro x hx
        obtain ⟨P, p, hp, hefface⟩ := exists_epi_effacing_ext x
        letI := hp
        let S := ShortComplex.mk _ _ (kernel.condition p)
        have exactSequence : S.ShortExact :=
          { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel p) }
        obtain ⟨y, hy⟩ := Ext.contravariant_sequence_exact₃ exactSequence Y x hefface
          (n₀ := n) (Nat.add_comm 1 n)
        have hFy : (exactSequence.map F).extClass.comp
            (F.mapExtAddHom S.X₁ Y n y) (Nat.add_comm 1 n) = 0 := by
          simpa only [Functor.mapExtAddHom_apply, Ext.mapExactFunctor_comp,
            Ext.mapExactFunctor_extClass] using
              (congrArg (F.mapExtAddHom X Y (n + 1)) hy).trans hx
        obtain ⟨z, hz⟩ := Ext.contravariant_sequence_exact₁ (exactSequence.map F)
          (F.obj Y) (F.mapExtAddHom S.X₁ Y n y) (n₁ := n + 1) (Nat.add_comm 1 n) hFy
        change (Ext.mk₀ (F.map S.f)).comp z (zero_add n) =
          F.mapExtAddHom S.X₁ Y n y at hz
        obtain ⟨z', hz'⟩ := (ih P Y).surjective z
        have hsource : (Ext.mk₀ S.f).comp z' (zero_add n) = y := by
          apply (ih S.X₁ Y).injective
          simpa only [Functor.mapExtAddHom_apply, Ext.mapExactFunctor_comp,
            Ext.mapExactFunctor_mk₀, ← hz'] using hz
        rw [← hy, ← hsource]
        exact exactSequence.extClass_comp_assoc z'
      · intro x
        obtain ⟨P, p, hp, hefface⟩ := exists_epi_effacing_ext x
        obtain ⟨Q, q, hqp⟩ := lifting X P p hp
        let f : Q ⟶ X := F.preimage (q ≫ p)
        have hf : F.map f = q ≫ p := F.map_preimage _
        haveI : Epi (F.map f) := by rw [hf]; exact hqp
        haveI : Epi f := F.epi_of_epi_map inferInstance
        let S := ShortComplex.mk _ _ (kernel.condition f)
        have exactSequence : S.ShortExact :=
          { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel f) }
        have hefface' : (Ext.mk₀ (S.map F).g).comp x (zero_add (n + 1)) = 0 := by
          change (Ext.mk₀ (F.map f)).comp x (zero_add (n + 1)) = 0
          rw [hf, ← Ext.mk₀_comp_mk₀_assoc, hefface, Ext.comp_zero]
        obtain ⟨y, hy⟩ := Ext.contravariant_sequence_exact₃ (exactSequence.map F)
          (F.obj Y) x hefface' (n₀ := n) (Nat.add_comm 1 n)
        obtain ⟨y', hy'⟩ := (ih S.X₁ Y).surjective y
        refine ⟨exactSequence.extClass.comp y' (Nat.add_comm 1 n), ?_⟩
        simpa only [Functor.mapExtAddHom_apply, Ext.mapExactFunctor_comp,
          Ext.mapExactFunctor_extClass, ← hy'] using hy

end ToricPower

end
