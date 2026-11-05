module

public import PaperVerification.ToricModuleFrameGluing
public import PaperVerification.ToricCartierRangeEquality

@[expose] public section

/-!
# Comparing an actual locally free sheaf with prescribed rational Cartier frames

The input is a genuine map of module sheaves into rational functions and
actual local frames on the given Cartier cover. Its value on each frame is
the specified nonzero rational generator. These equalities prove that the
map is injective, identify all local fractional modules, and hence give an
actual isomorphism with the Cartier sheaf, preserving rational values.

In particular, neither injectivity nor the desired Cartier identification
is assumed as part of the comparison data.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes.RationalCartierCocycle

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped Classical

variable {X : Scheme.{u}} [IsIntegral X]
    (C : RationalCartierCocycle X) (M : X.Modules)
    (v : M ⟶ rationalFunctions X)
    (e : ∀ i, ModuleFrame M (C.openSet i))

/-- Equality of the genuine rational values of the actual local frames.
Empty members of the cover impose no condition. -/
def FrameValues : Prop :=
  ∀ (i : C.index) [Nonempty (C.openSet i)],
    rationalValue X (C.openSet i)
      (v.app (C.openSet i) ((e i).generator (C.openSet i) le_rfl)) =
        (C.generator i : X.functionField)

theorem frameValues_restrict (hv : C.FrameValues M v e)
    (i : C.index) (V : X.Opens) [Nonempty V] (hi : V≤C.openSet i) :
    rationalValue X V (v.app V ((e i).generator V hi)) =
      (C.generator i : X.functionField) := by
  letI : Nonempty (C.openSet i) :=
    ⟨⟨(Classical.arbitrary V).val,hi (Classical.arbitrary V).property⟩⟩
  have hn := PresheafOfModules.naturality_apply v.val (homOfLE hi).op
    ((e i).generator (C.openSet i) le_rfl)
  have hgen : moduleRes M hi ((e i).generator (C.openSet i) le_rfl) =
      (e i).generator V hi := (e i).generator_res le_rfl hi
  change v.app V (moduleRes M hi ((e i).generator (C.openSet i) le_rfl)) =
    moduleRes (rationalFunctions X) hi
      (v.app (C.openSet i) ((e i).generator (C.openSet i) le_rfl)) at hn
  have hn' : v.app V ((e i).generator V hi) =
      moduleRes (rationalFunctions X) hi
        (v.app (C.openSet i) ((e i).generator (C.openSet i) le_rfl)) :=
    (congrArg (v.app V) hgen.symm).trans hn
  rw [hn',rationalValue_restrict]
  exact hv i

theorem frameValues_section (hv : C.FrameValues M v e)
    (i : C.index) (V : X.Opens) [Nonempty V]
    (hi : V≤C.openSet i) (s : Γ(M,V)) :
    rationalValue X V (v.app V s) =
      X.germToFunctionField V ((e i).coordinates V hi s) *
        (C.generator i : X.functionField) := by
  conv_lhs => rw [(e i).section_eq V hi s]
  rw [Scheme.Modules.Hom.app_smul,rationalValue_smul,
    C.frameValues_restrict M v e hv i V hi]

/-- Nonzero rational frame values imply local injectivity; it is not an
extra assumption on the sheaf map. -/
theorem frameValues_injective_on (hv : C.FrameValues M v e)
    (i : C.index) (V : X.Opens) [Nonempty V]
    (hi : V≤C.openSet i) : Function.Injective (v.app V) := by
  intro s t h
  apply ((e i).coordinates V hi).injective
  apply X.germToFunctionField_injective V
  apply mul_right_cancel₀ (Units.ne_zero (C.generator i))
  rw [← C.frameValues_section M v e hv i V hi s,
    ← C.frameValues_section M v e hv i V hi t,h]

/-- Local injectivity on the actual cover gives injectivity on every
open, including the empty open. -/
theorem frameValues_injective (hv : C.FrameValues M v e)
    (W : X.Opens) : Function.Injective (v.app W) := by
  intro s t h
  apply module_sections_ext_cover M C.openSet C.covers W s t
  intro i
  by_cases hV : Nonempty (W⊓C.openSet i : X.Opens)
  · letI := hV
    apply C.frameValues_injective_on M v e hv i (W⊓C.openSet i) inf_le_right
    have hs := PresheafOfModules.naturality_apply v.val
      (homOfLE (show W⊓C.openSet i≤W from inf_le_left)).op s
    have ht := PresheafOfModules.naturality_apply v.val
      (homOfLE (show W⊓C.openSet i≤W from inf_le_left)).op t
    calc
      v.app (W⊓C.openSet i) (moduleRes M inf_le_left s) =
          moduleRes (rationalFunctions X) inf_le_left (v.app W s) := hs
      _ = moduleRes (rationalFunctions X) inf_le_left (v.app W t) := by rw [h]
      _ = v.app (W⊓C.openSet i) (moduleRes M inf_le_left t) := ht.symm
  · have hbot : W⊓C.openSet i=⊥ := by
      apply le_antisymm
      · intro x hx
        exact False.elim (hV ⟨⟨x,hx⟩⟩)
      · exact bot_le
    letI := moduleSections_subsingleton_of_empty M (W⊓C.openSet i) hbot
    exact Subsingleton.elim _ _

/-- The actual sheaf with its proved rational embedding, retaining its
underlying module sheaf literally. -/
def cartierDataOfFrames (hv : C.FrameValues M v e) : CartierData X where
  sheaf := M
  inclusion := v
  inclusion_injective := C.frameValues_injective M v e hv
  locallyFree := by
    intro x
    obtain ⟨i,hi⟩ := C.covers x
    exact ⟨C.openSet i,hi,⟨e i⟩⟩

@[simp] theorem cartierDataOfFrames_sheaf (hv : C.FrameValues M v e) :
    (C.cartierDataOfFrames M v e hv).sheaf=M := rfl

/-- The comparison preserves the actual fractional embedding. The
local ranges are both exactly the regular multiples of the same generator. -/
theorem cartierDataOfFrames_equivalent (hv : C.FrameValues M v e) :
    (C.cartierDataOfFrames M v e hv).Equivalent C.toCartierData := by
  let D := C.cartierDataOfFrames M v e hv
  apply D.equivalent_of_local_ranges C.toCartierData C.openSet C.covers
  intro i V hV hi
  letI : Nonempty (C.openSet i) :=
    ⟨⟨(Classical.arbitrary V).val,hi (Classical.arbitrary V).property⟩⟩
  have hg : D.frameRationalGenerator (e i) =
      (C.generator i : X.functionField) := hv i
  ext r
  change r ∈ D.sectionValueRange V ↔ r ∈ C.toCartierData.sectionValueRange V
  rw [D.mem_sectionValueRange_iff (e i) hi r,
    C.mem_sectionValueRange_iff i V hi r,hg]
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨a,(eq_div_iff (Units.ne_zero (C.generator i))).mpr ha⟩
  · rintro ⟨a,ha⟩
    exact ⟨a,(eq_div_iff (Units.ne_zero (C.generator i))).mp ha⟩

/-- A genuine isomorphism with the Cartier sheaf associated to the
specified rational cocycle. -/
def sheafIsoOfFrames (hv : C.FrameValues M v e) : M ≅ C.sheaf :=
  (C.cartierDataOfFrames_equivalent M v e hv).choose

theorem sheafIsoOfFrames_inclusion (hv : C.FrameValues M v e) :
    (C.sheafIsoOfFrames M v e hv).hom≫C.inclusion=v :=
  (C.cartierDataOfFrames_equivalent M v e hv).choose_spec

end PaperVerification.ToricSchemes.RationalCartierCocycle

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.frameValues_injective
#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.sheafIsoOfFrames
