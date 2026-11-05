module

public import PaperVerification.ToricModuleFrameGluing
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

@[expose] public section

/-!
# Identification of the actual sheaf pullback by local frames

The target is identified with Mathlib's ordinary module-sheaf pullback by
its adjunction universal property. Compatible transition maps are used to
construct a genuine sheaf morphism; no pullback or section-space dictionary
is a field of a structure or an additional axiom. The statement applies to
closed immersions as well as dominant morphisms.
-/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace PaperVerification.ToricSchemes

open Scheme.Modules

variable {X Y : Scheme.{u}} (f : Y ⟶ X)
    {M : X.Modules} {N : Y.Modules} {ι : Type v}
    (U : ι→X.Opens) (hcover : ∀ x : X,∃ i,x∈U i)
    (e : ∀ i,ModuleFrame M (U i))
    (q : ∀ i,ModuleFrame N (f ⁻¹ᵁ U i))

include hcover in
theorem pullback_frameCover : ∀ y : Y,∃ i,y∈f ⁻¹ᵁ U i := fun y=>hcover (f y)

theorem pushforward_frameGenerator_res {F : Y.Modules}
    (β : M ⟶ (pushforward f).obj F) (i : ι)
    (V : X.Opens) (hV : V≤U i) :
    moduleRes F (f.preimage_mono hV)
        (β.app (U i) ((e i).generator (U i) le_rfl)) =
      β.app V ((e i).generator V hV) := by
  have h := PresheafOfModules.naturality_apply β.val (homOfLE hV).op
    ((e i).generator (U i) le_rfl)
  change β.app V (moduleRes M hV ((e i).generator (U i) le_rfl)) =
    moduleRes F (f.preimage_mono hV)
      (β.app (U i) ((e i).generator (U i) le_rfl)) at h
  exact h.symm.trans (congrArg (β.app V)
    ((e i).generator_res (V := U i) le_rfl hV))

variable (β₀ : M ⟶ (pushforward f).obj N)
    (hβ₀ : ∀ i,β₀.app (U i) ((e i).generator (U i) le_rfl) =
      (q i).generator (f ⁻¹ᵁ U i) le_rfl)

include β₀ hβ₀ in
/-- Any genuine morphism from the original sheaf supplies compatible
images of the comparison target's local generators. -/
theorem comparison_frameImages_compatible {F : Y.Modules}
    (β : M ⟶ (pushforward f).obj F) :
    ModuleFrameGluing.Compatible (fun i=>f ⁻¹ᵁ U i) q
      (fun i=>β.app (U i) ((e i).generator (U i) le_rfl)) := by
  intro i j W hWi hWj
  let V := U i⊓U j
  let c : Γ(X,V) := (e j).coordinates V inf_le_right ((e i).generator V inf_le_left)
  have hW : W≤f ⁻¹ᵁ V := by
    intro y hy
    exact ⟨hWi hy,hWj hy⟩
  have hgen : (e i).generator V inf_le_left =
      c • (e j).generator V inf_le_right :=
    (e j).section_eq V inf_le_right ((e i).generator V inf_le_left)
  have hβ (F : Y.Modules) (β : M ⟶ (pushforward f).obj F) :
      moduleRes F (f.preimage_mono (show V≤U i from inf_le_left))
          (β.app (U i) ((e i).generator (U i) le_rfl)) =
        f.app V c • moduleRes F (f.preimage_mono (show V≤U j from inf_le_right))
          (β.app (U j) ((e j).generator (U j) le_rfl)) := by
    rw [pushforward_frameGenerator_res f U e β i V inf_le_left,
      pushforward_frameGenerator_res f U e β j V inf_le_right,hgen,
      Scheme.Modules.Hom.app_smul]
    rfl
  have hN := hβ N β₀
  rw [hβ₀ i,hβ₀ j,ModuleFrame.generator_res,ModuleFrame.generator_res] at hN
  have hN' := congrArg (moduleRes N hW) hN
  rw [moduleRes_smul,ModuleFrame.generator_res,ModuleFrame.generator_res] at hN'
  have hc : (q j).coordinates W hWj ((q i).generator W hWi) =
      regularRes hW (f.app V c) := by
    rw [hN',_root_.map_smul,ModuleFrame.coordinates_generator,smul_eq_mul,mul_one]
  rw [hc]
  let hi : f ⁻¹ᵁ V≤f ⁻¹ᵁ U i := f.preimage_mono (show V≤U i from inf_le_left)
  let hj : f ⁻¹ᵁ V≤f ⁻¹ᵁ U j := f.preimage_mono (show V≤U j from inf_le_right)
  calc
    _ = moduleRes F hW (moduleRes F hi
        (β.app (U i) ((e i).generator (U i) le_rfl))) :=
      (moduleRes_trans F hi hW _).symm
    _ = moduleRes F hW (f.app V c • moduleRes F hj
        (β.app (U j) ((e j).generator (U j) le_rfl))) :=
      congrArg (moduleRes F hW) (hβ F β)
    _ = regularRes hW (f.app V c) • moduleRes F hW (moduleRes F hj
        (β.app (U j) ((e j).generator (U j) le_rfl))) :=
      moduleRes_smul F hW _ _
    _ = _ := congrArg (fun z=>regularRes hW (f.app V c) • z)
      (moduleRes_trans F hj hW _)

/-- The unique candidate supplied by the actual gluing of local frame
images. Its codomain is an arbitrary genuine module sheaf. -/
def comparisonLift {F : Y.Modules} (β : M ⟶ (pushforward f).obj F) : N ⟶ F :=
  ModuleFrameGluing.hom (fun i=>f ⁻¹ᵁ U i) (pullback_frameCover f U hcover) q
    (fun i=>β.app (U i) ((e i).generator (U i) le_rfl))
    (comparison_frameImages_compatible f U e q β₀ hβ₀ β)

theorem comparisonLift_generator {F : Y.Modules}
    (β : M ⟶ (pushforward f).obj F) (i : ι) :
    (comparisonLift f U hcover e q β₀ hβ₀ β).app (f ⁻¹ᵁ U i)
        ((q i).generator (f ⁻¹ᵁ U i) le_rfl) =
      β.app (U i) ((e i).generator (U i) le_rfl) :=
  ModuleFrameGluing.hom_generator _ _ _ _ _ i

theorem comparison_comp_lift {F : Y.Modules}
    (β : M ⟶ (pushforward f).obj F) :
    β₀ ≫ (pushforward f).map (comparisonLift f U hcover e q β₀ hβ₀ β) = β := by
  apply ModuleFrameGluing.hom_ext U hcover e
  intro i
  change (comparisonLift f U hcover e q β₀ hβ₀ β).app (f ⁻¹ᵁ U i)
    (β₀.app (U i) ((e i).generator (U i) le_rfl)) = _
  rw [hβ₀ i,comparisonLift_generator]

include hcover e q hβ₀ in
theorem comparison_postcompose_bijective (F : Y.Modules) :
    Function.Bijective (fun h : N ⟶ F=>β₀ ≫ (pushforward f).map h) := by
  constructor
  · intro h l heq
    apply ModuleFrameGluing.hom_ext (fun i=>f ⁻¹ᵁ U i)
      (pullback_frameCover f U hcover) q
    intro i
    have hEval := congrArg (fun a : M ⟶ (pushforward f).obj F =>
      a.app (U i) ((e i).generator (U i) le_rfl)) heq
    change h.app (f ⁻¹ᵁ U i) (β₀.app (U i) ((e i).generator (U i) le_rfl)) =
      l.app (f ⁻¹ᵁ U i) (β₀.app (U i) ((e i).generator (U i) le_rfl)) at hEval
    simpa only [hβ₀ i] using hEval
  · intro β
    exact ⟨comparisonLift f U hcover e q β₀ hβ₀ β,
      comparison_comp_lift f U hcover e q β₀ hβ₀ β⟩

include hcover e q hβ₀ in
/-- The actual adjoint morphism is an isomorphism because it has the
genuine universal property of the module-sheaf pullback. -/
theorem pullback_comparison_isIso :
    IsIso (((pullbackPushforwardAdjunction f).homEquiv M N).symm β₀) := by
  let α := ((pullbackPushforwardAdjunction f).homEquiv M N).symm β₀
  rw [isIso_iff_coyoneda_map_bijective]
  intro F
  change Function.Bijective (fun h : N ⟶ F=>α ≫ h)
  let E := (pullbackPushforwardAdjunction f).homEquiv M F
  have hcomp (h : N ⟶ F) : E (α ≫ h)=β₀ ≫ (pushforward f).map h := by
    rw [Adjunction.homEquiv_naturality_right,Equiv.apply_symm_apply]
  have hb := comparison_postcompose_bijective f U hcover e q β₀ hβ₀ F
  constructor
  · intro h l heq
    apply hb.injective
    exact (hcomp h).symm.trans ((congrArg E heq).trans (hcomp l))
  · intro γ
    obtain ⟨h,hh⟩ := hb.surjective (E γ)
    refine ⟨h,E.injective ?_⟩
    exact (hcomp h).trans hh

/-- A shared criterion for arbitrary scheme morphisms: an actual map
sending one local basis to the other identifies the actual pullback. -/
def pullbackIso_of_frameComparison : (pullback f).obj M ≅ N := by
  letI := pullback_comparison_isIso f U hcover e q β₀ hβ₀
  exact asIso (((pullbackPushforwardAdjunction f).homEquiv M N).symm β₀)

section CompatibleTransitions

variable
    (htrans : ModuleFrameGluing.Compatible (N := (pushforward f).obj N) U e
      (fun i=>(q i).generator (f ⁻¹ᵁ U i) le_rfl))

/-- Mapped regular transition functions construct the comparison itself;
the existence of this sheaf map is not assumed. -/
def framePullbackComparison : M ⟶ (pushforward f).obj N :=
  ModuleFrameGluing.hom U hcover e
    (fun i=>(q i).generator (f ⁻¹ᵁ U i) le_rfl) htrans

/-- Local frames with genuinely mapped transition functions identify the
ordinary sheaf pullback, also along a closed boundary immersion. -/
def pullbackIso_of_compatible_frames : (pullback f).obj M ≅ N :=
  pullbackIso_of_frameComparison f U hcover e q
    (framePullbackComparison f U hcover e q htrans)
    (ModuleFrameGluing.hom_generator U hcover e _ htrans)

end CompatibleTransitions

end PaperVerification.ToricSchemes
