module

public import ToricPower.CoproductFiniteFactorization

/-!
# Canonical finite-coproduct retractions

Every finite subcoproduct is split inside the full coproduct by sending
all remaining summands to zero. The resulting idempotent makes support
conditions compatible with enlarging the chosen finite set.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.CompactExtraction

universe u v w
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]

def finiteCoproductRetraction {I : Type w} (family : I → C) (s : Finset I) :
    (∐ family) ⟶ ∐ fun i : s => family i := by
  classical
  exact Sigma.desc (fun i => if h : i ∈ s then
    Sigma.ι (fun i : s => family i) ⟨i, h⟩ else 0)

@[reassoc (attr := simp)]
theorem ι_finiteCoproductRetraction {I : Type w} (family : I → C)
    (s : Finset I) (i : s) :
    Sigma.ι family i ≫ finiteCoproductRetraction family s =
      Sigma.ι (fun i : s => family i) i := by
  simp [finiteCoproductRetraction, Sigma.ι_comp_desc, i.property]

@[reassoc (attr := simp)]
theorem finiteCoproductInclusion_retraction {I : Type w} (family : I → C) (s : Finset I) :
    finiteCoproductInclusion family s ≫ finiteCoproductRetraction family s = 𝟙 _ := by
  apply Sigma.hom_ext
  intro i
  simp [finiteCoproductInclusion, Sigma.ι_comp_desc_assoc]

def finiteCoproductProjector {I : Type w} (family : I → C) (s : Finset I) :
    (∐ family) ⟶ ∐ family :=
  finiteCoproductRetraction family s ≫ finiteCoproductInclusion family s

@[reassoc (attr := simp)]
theorem ι_finiteCoproductProjector {I : Type w} (family : I → C) (s : Finset I)
    {i : I} (member : i ∈ s) :
    Sigma.ι family i ≫ finiteCoproductProjector family s = Sigma.ι family i := by
  change Sigma.ι family (⟨i, member⟩ : s) ≫ finiteCoproductRetraction family s ≫
    finiteCoproductInclusion family s = _
  rw [ι_finiteCoproductRetraction_assoc]
  exact Sigma.ι_comp_desc _ _

@[reassoc (attr := simp)]
theorem finiteCoproductInclusion_projector {I : Type w} (family : I → C)
    {s t : Finset I} (subset : s ⊆ t) :
    finiteCoproductInclusion family s ≫ finiteCoproductProjector family t =
      finiteCoproductInclusion family s := by
  apply Sigma.hom_ext
  intro i
  simp only [finiteCoproductInclusion, Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
  exact ι_finiteCoproductProjector family t (subset i.property)

@[reassoc]
theorem finiteCoproductProjector_mono {I : Type w} (family : I → C)
    {s t : Finset I} (subset : s ⊆ t) :
    finiteCoproductProjector family s ≫ finiteCoproductProjector family t =
      finiteCoproductProjector family s := by
  change (finiteCoproductRetraction family s ≫ finiteCoproductInclusion family s) ≫
    finiteCoproductProjector family t = _
  rw [Category.assoc, finiteCoproductInclusion_projector family subset]
  rfl

theorem finiteSupport_mono {I : Type w} (family : I → C)
    {X : C} (f : X ⟶ ∐ family) {s t : Finset I} (subset : s ⊆ t)
    (support : f ≫ finiteCoproductProjector family s = f) :
    f ≫ finiteCoproductProjector family t = f := by
  rw [← support, Category.assoc, finiteCoproductProjector_mono family subset]

theorem coproductCompact_iff_projector {X : C} :
    CoproductCompact.{u, v, w} X ↔
      ∀ (I : Type w) (family : I → C) (f : X ⟶ ∐ family),
        ∃ s : Finset I, f ≫ finiteCoproductProjector family s = f := by
  constructor
  · intro compact I family f
    obtain ⟨s, lift, factor⟩ := compact I family f
    refine ⟨s, ?_⟩
    rw [← factor, Category.assoc, finiteCoproductInclusion_projector family (Finset.Subset.refl s)]
  · intro support I family f
    obtain ⟨s, equation⟩ := support I family f
    exact ⟨s, f ≫ finiteCoproductRetraction family s,
      by simpa only [finiteCoproductProjector, Category.assoc] using equation⟩

end ToricPower.CompactExtraction

end

