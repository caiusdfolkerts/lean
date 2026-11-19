module

public import ToricPower.TelescopeCompactFactorization
public import Mathlib.CategoryTheory.Idempotents.Basic

/-!
# Splitting idempotents by an actual countable telescope

The telescope of an idempotent has a split-monomorphic first arrow.
Its splitting uses only finite sums in each column, so no convergence
or compactness assumption enters this argument. The telescope then
provides the image object of the original idempotent.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace ToricPower.CompactExtraction

universe u v
variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasCoproducts.{0} C]

def idempotentSequence (X : C) (e : X ⟶ X) : ℕ ⥤ C :=
  Functor.ofSequence (X := fun _ => X) (fun _ => e)

@[simp]
theorem idempotentSequence_transition (X : C) (e : X ⟶ X) (n : ℕ) :
    (idempotentSequence X e).map (homOfLE (Nat.le_succ n)) = e :=
  Functor.ofSequence_map_homOfLE_succ _ n

/-- Each column is a finite sum, even though the coproduct is countable. -/
def idempotentTelescopeRetraction (X : C) (e : X ⟶ X) :
    (∐ (idempotentSequence X e).obj) ⟶ ∐ (idempotentSequence X e).obj :=
  Sigma.desc (fun i =>
    (𝟙 X - e) ≫ Sigma.ι (idempotentSequence X e).obj i -
      ∑ j ∈ Finset.range i, e ≫ Sigma.ι (idempotentSequence X e).obj j)

theorem idempotentTelescope_retract (X : C) (e : X ⟶ X) (he : e ≫ e = e) :
    telescopeMap (idempotentSequence X e) ≫ idempotentTelescopeRetraction X e = 𝟙 _ := by
  apply Sigma.hom_ext
  intro i
  rw [ι_telescopeMap_assoc,Preadditive.sub_comp,idempotentSequence_transition,
    Category.assoc]
  simp only [idempotentTelescopeRetraction,Sigma.ι_comp_desc]
  rw [Finset.sum_range_succ]
  simp only [Preadditive.comp_sub,Preadditive.sub_comp,Preadditive.comp_add,
    Preadditive.comp_sum,
    ← Category.assoc,he,Category.comp_id,Category.id_comp]
  dsimp only [idempotentSequence,Functor.ofSequence]
  abel

/-- An idempotent is fixed on every telescope stage and all stage maps
coincide. These are identities of actual morphisms. -/
theorem idempotentTelescope_stage (X : C) (e : X ⟶ X) (he : e ≫ e = e)
    (T : Telescope (idempotentSequence X e)) (n : ℕ) :
    e ≫ T.ι n = T.ι n ∧ T.ι n = T.ι 0 := by
  have transition (i : ℕ) : e ≫ T.ι (i + 1) = T.ι i := by
    simpa only [idempotentSequence_transition] using T.transition_ι i
  have fixed (i : ℕ) : e ≫ T.ι i = T.ι i := by
    calc
      e ≫ T.ι i = e ≫ e ≫ T.ι (i + 1) := by rw [transition]
      _ = e ≫ T.ι (i + 1) := by rw [← Category.assoc,he]
      _ = T.ι i := transition i
  refine ⟨fixed n, ?_⟩
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [← fixed (n + 1),transition,ih]

/-- Countable coproducts suffice to split every idempotent in a
pretriangulated category. -/
theorem idempotentComplete_of_countableCoproducts : IsIdempotentComplete C := by
  constructor
  intro X e he
  let F := idempotentSequence X e
  let T := Classical.choice (telescope_nonempty F)
  haveI : Mono (telescopeMap F) :=
    mono_of_mono_fac (idempotentTelescope_retract X e he)
  have boundary : T.boundary = 0 :=
    T.triangle.mor₃_eq_zero_of_mono₁ T.distinguished
      (show Mono (telescopeMap F) from inferInstance)
  haveI : Epi T.inclusion := T.triangle.epi₂ T.distinguished boundary
  obtain ⟨p, hp⟩ := T.exists_desc (fun _ => e) (by
    intro n
    change (idempotentSequence X e).map (homOfLE (Nat.le_succ n)) ≫ e = e
    rw [idempotentSequence_transition,he])
  refine ⟨T.obj,p,T.ι 0,?_,hp 0⟩
  apply (cancel_epi T.inclusion).mp
  apply Sigma.hom_ext
  intro n
  have h : T.ι n ≫ (p ≫ T.ι 0) = T.ι n ≫ 𝟙 T.obj := by
    rw [← Category.assoc,hp,Category.comp_id,
      (idempotentTelescope_stage X e he T 0).1,
      (idempotentTelescope_stage X e he T n).2]
  simpa only [Telescope.ι,Category.assoc] using h

end ToricPower.CompactExtraction

end
