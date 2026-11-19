module

public import ToricPower.CellularFiniteResolution
public import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma

/-!
# Exactness of the actual cellular syzygy functor

The vector cover is exact and its counit is an actual epimorphism.
The snake lemma applied to a short exact sequence and its vector cover
therefore proves that taking the kernel of the counit is exact too.
This supplies the exact coefficient functors needed for a finite derived
realization; exactness is not included as a hypothesis in the definition.

-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

open scoped ZeroObject

namespace ToricPower.Cellular

universe u

variable (k : Type u) [Field k] {C : Type u} [Category.{u} C]

instance diagramSyzygy_additive : (diagramSyzygy k (C := C)).Additive where
  map_add {F G} η θ := by
    apply (cancel_mono (kernel.ι (diagramVectorCoverMap k G))).mp
    simp only [diagramSyzygy, kernel.map, kernel.lift_ι, Preadditive.add_comp,
      Functor.map_add, Preadditive.comp_add]

/-- The vector-cover map on an entire short complex. -/
def diagramCoverShortMap (S : ShortComplex (C ⥤ ModuleCat.{u} k)) :
    S.map (diagramVectorCover k) ⟶ S :=
  S.mapNatTrans (diagramVectorCoverCounit k)

/-- The actual syzygy inclusion on an entire short complex. -/
def diagramSyzygyShortMap (S : ShortComplex (C ⥤ ModuleCat.{u} k)) :
    S.map (diagramSyzygy k) ⟶ S.map (diagramVectorCover k) :=
  S.mapNatTrans (diagramSyzygyInclusion k)

@[reassoc (attr := simp)]
theorem diagramSyzygyShortMap_cover (S : ShortComplex (C ⥤ ModuleCat.{u} k)) :
    diagramSyzygyShortMap k S ≫ diagramCoverShortMap k S = 0 := by
  apply ShortComplex.Hom.ext <;> exact kernel.condition _

instance diagramCoverShortMap_epi (S : ShortComplex (C ⥤ ModuleCat.{u} k)) :
    Epi (diagramCoverShortMap k S) where
  left_cancellation {Z} f g h := by
    apply ShortComplex.Hom.ext
    · exact (cancel_epi (diagramVectorCoverMap k S.X₁)).mp
        (congrArg ShortComplex.Hom.τ₁ h)
    · exact (cancel_epi (diagramVectorCoverMap k S.X₂)).mp
        (congrArg ShortComplex.Hom.τ₂ h)
    · exact (cancel_epi (diagramVectorCoverMap k S.X₃)).mp
        (congrArg ShortComplex.Hom.τ₃ h)

instance diagramSyzygyShortMap_mono (S : ShortComplex (C ⥤ ModuleCat.{u} k)) :
    Mono (diagramSyzygyShortMap k S) where
  right_cancellation {Z} f g h := by
    apply ShortComplex.Hom.ext
    · exact (cancel_mono (kernel.ι (diagramVectorCoverMap k S.X₁))).mp
        (congrArg ShortComplex.Hom.τ₁ h)
    · exact (cancel_mono (kernel.ι (diagramVectorCoverMap k S.X₂))).mp
        (congrArg ShortComplex.Hom.τ₂ h)
    · exact (cancel_mono (kernel.ι (diagramVectorCoverMap k S.X₃))).mp
        (congrArg ShortComplex.Hom.τ₃ h)

/-- The short complex formed from actual syzygies is the actual kernel
of the morphism of short complexes. Each component lift is the universal
kernel lift, and its two squares follow by cancelling kernel inclusions. -/
def diagramSyzygyShortMap_isKernel (S : ShortComplex (C ⥤ ModuleCat.{u} k)) :
    IsLimit (KernelFork.ofι (diagramSyzygyShortMap k S)
      (diagramSyzygyShortMap_cover k S)) := by
  apply KernelFork.IsLimit.ofι'
  intro Z a ha
  have h₁ : a.τ₁ ≫ diagramVectorCoverMap k S.X₁ = 0 :=
    congrArg ShortComplex.Hom.τ₁ ha
  have h₂ : a.τ₂ ≫ diagramVectorCoverMap k S.X₂ = 0 :=
    congrArg ShortComplex.Hom.τ₂ ha
  have h₃ : a.τ₃ ≫ diagramVectorCoverMap k S.X₃ = 0 :=
    congrArg ShortComplex.Hom.τ₃ ha
  refine ⟨
    { τ₁ := kernel.lift _ a.τ₁ h₁
      τ₂ := kernel.lift _ a.τ₂ h₂
      τ₃ := kernel.lift _ a.τ₃ h₃
      comm₁₂ := ?_
      comm₂₃ := ?_ }, ?_⟩
  · apply (cancel_mono (kernel.ι (diagramVectorCoverMap k S.X₂))).mp
    simpa only [diagramSyzygy, ShortComplex.map_f, kernel.map,
      Category.assoc, kernel.lift_ι, kernel.lift_ι_assoc] using a.comm₁₂
  · apply (cancel_mono (kernel.ι (diagramVectorCoverMap k S.X₃))).mp
    simpa only [diagramSyzygy, ShortComplex.map_g, kernel.map,
      Category.assoc, kernel.lift_ι, kernel.lift_ι_assoc] using a.comm₂₃
  · apply ShortComplex.Hom.ext <;> exact kernel.lift_ι _ _ _

/-- The complete actual snake diagram. Its bottom row is zero because
the vector-cover morphism is an epimorphism, not because a cokernel is
discarded by definition. -/
def diagramSyzygySnakeInput
    (S : ShortComplex (C ⥤ ModuleCat.{u} k)) (hS : S.ShortExact) :
    ShortComplex.SnakeInput (C ⥤ ModuleCat.{u} k) where
  L₀ := S.map (diagramSyzygy k)
  L₁ := S.map (diagramVectorCover k)
  L₂ := S
  L₃ := 0
  v₀₁ := diagramSyzygyShortMap k S
  v₁₂ := diagramCoverShortMap k S
  v₂₃ := 0
  w₀₂ := diagramSyzygyShortMap_cover k S
  w₁₃ := by simp
  h₀ := diagramSyzygyShortMap_isKernel k S
  h₃ := CokernelCofork.IsColimit.ofEpiOfIsZero _
    (by infer_instance) (isZero_zero _)
  L₁_exact := (hS.map_of_exact (diagramVectorCover k)).exact
  epi_L₁_g := (hS.map_of_exact (diagramVectorCover k)).epi_g
  L₂_exact := hS.exact
  mono_L₂_f := hS.mono_f

/-- The actual syzygy functor preserves short exact sequences. The
surjectivity on the right is the snake-lemma conclusion with zero
connecting-map target. -/
theorem diagramSyzygy_shortExact
    (S : ShortComplex (C ⥤ ModuleCat.{u} k)) (hS : S.ShortExact) :
    (S.map (diagramSyzygy k)).ShortExact := by
  let T := diagramSyzygySnakeInput k S hS
  letI : Mono T.L₁.f := (hS.map_of_exact (diagramVectorCover k)).mono_f
  have hδ : T.δ = 0 := by
    exact ((ShortComplex.π₁ : ShortComplex (C ⥤ ModuleCat.{u} k) ⥤ _).map_isZero
      (isZero_zero _)).eq_of_tgt _ _
  exact
    { exact := T.L₀_exact
      mono_f := T.mono_L₀_f
      epi_g := T.L₁'_exact.epi_f hδ }

/-- Both sides of exactness follow from the displayed snake diagram. -/
theorem diagramSyzygy_exact :
    PreservesFiniteLimits (diagramSyzygy k (C := C)) ∧
      PreservesFiniteColimits (diagramSyzygy k (C := C)) :=
  ((Functor.exact_tfae (diagramSyzygy k (C := C))).out 1 4).mp
    (diagramSyzygy_shortExact k)

instance diagramSyzygy_preservesFiniteLimits :
    PreservesFiniteLimits (diagramSyzygy k (C := C)) :=
  (diagramSyzygy_exact k).1

instance diagramSyzygy_preservesFiniteColimits :
    PreservesFiniteColimits (diagramSyzygy k (C := C)) :=
  (diagramSyzygy_exact k).2

instance diagramSyzygyIterate_additive (m : ℕ) :
    (diagramSyzygyIterate k m (C := C)).Additive := by
  induction m with
  | zero => dsimp [diagramSyzygyIterate]; infer_instance
  | succ m ih =>
    letI := ih
    dsimp only [diagramSyzygyIterate]
    infer_instance

instance diagramSyzygyIterate_preservesFiniteLimits (m : ℕ) :
    PreservesFiniteLimits (diagramSyzygyIterate k m (C := C)) := by
  induction m with
  | zero => dsimp [diagramSyzygyIterate]; infer_instance
  | succ m ih =>
    letI := ih
    dsimp only [diagramSyzygyIterate]
    infer_instance

instance diagramSyzygyIterate_preservesFiniteColimits (m : ℕ) :
    PreservesFiniteColimits (diagramSyzygyIterate k m (C := C)) := by
  induction m with
  | zero => dsimp [diagramSyzygyIterate]; infer_instance
  | succ m ih =>
    letI := ih
    dsimp only [diagramSyzygyIterate]
    infer_instance

section Target

universe v

variable {A : Type v} [Category.{u} A] [Abelian A]
  (H : (C ⥤ ModuleCat.{u} k) ⥤ A) [H.Additive]

/-- Applying any actual additive realization to the vector cover is
exact. The reason is stronger than exactness of the cover: each covered
short exact sequence has the displayed actual splitting. -/
theorem diagramVectorCover_comp_exact :
    PreservesFiniteLimits (diagramVectorCover k ⋙ H) ∧
      PreservesFiniteColimits (diagramVectorCover k ⋙ H) :=
  ((Functor.exact_tfae (diagramVectorCover k ⋙ H)).out 1 4).mp
    (fun S hS => ((diagramVectorCoverSplitting k S hS).map H).shortExact)

instance diagramVectorCover_comp_preservesFiniteLimits :
    PreservesFiniteLimits (diagramVectorCover k ⋙ H) :=
  (diagramVectorCover_comp_exact k H).1

instance diagramVectorCover_comp_preservesFiniteColimits :
    PreservesFiniteColimits (diagramVectorCover k ⋙ H) :=
  (diagramVectorCover_comp_exact k H).2

/-- Every term of the finite resolution remains an exact coefficient
functor after applying the actual additive realization. This is the
input needed to descend finite totalization on unbounded complexes. -/
def realizedProjectiveTerm (m : ℕ) : (C ⥤ ModuleCat.{u} k) ⥤ A :=
  diagramSyzygyIterate k m ⋙ diagramVectorCover k ⋙ H

instance realizedProjectiveTerm_additive (m : ℕ) :
    (realizedProjectiveTerm k H m).Additive := by
  unfold realizedProjectiveTerm
  infer_instance

instance realizedProjectiveTerm_preservesFiniteLimits (m : ℕ) :
    PreservesFiniteLimits (realizedProjectiveTerm k H m) := by
  unfold realizedProjectiveTerm
  infer_instance

instance realizedProjectiveTerm_preservesFiniteColimits (m : ℕ) :
    PreservesFiniteColimits (realizedProjectiveTerm k H m) := by
  unfold realizedProjectiveTerm
  infer_instance

end Target

end ToricPower.Cellular

end
