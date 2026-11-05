module

public import Lean.Elab.BuiltinEvalCommand
public meta import Lean.Elab.BuiltinEvalCommand
public import Lean.Util.CollectAxioms
public meta import Lean.Util.CollectAxioms
public import Lean.Util.FoldConsts
public meta import Lean.Util.FoldConsts
public import paper_verification.toric010

@[expose] public section


-- BEGIN ORIGINAL PaperVerification.ToricDominantCartierPullback
section Source_ToricDominantCartierPullback

-- original header: module

-- original header: public import PaperVerification.ToricCartierPullbackFrames
-- original header: public import PaperVerification.ToricDominantFunctionField
-- original header: public import PaperVerification.ToricCartierRangeEquality

-- original header: @[expose] public section

/-!
# Actual Cartier pullback along a dominant morphism

The rational equations are pulled through the genuine map of generic
stalks. Their regularity comes from the actual maps on local rings. The
resulting invertible fractional sheaf is identified with the ordinary
module-sheaf pullback by the independent local-frame theorem.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace PaperVerification.ToricSchemes

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) [IsDominant f]

namespace RationalCartierCocycle

variable (C : RationalCartierCocycle X)

def dominantPullback : RationalCartierCocycle Y where
  index := C.index
  openSet i := f ⁻¹ᵁ C.openSet i
  covers y := C.covers (f y)
  generator i := Units.map (dominantFunctionFieldMap f).toMonoidHom (C.generator i)
  transition i j y hi hj := by
    have h := dominantFunctionFieldMap_mem_regularAt f y
      ((C.generator i : X.functionField)/(C.generator j : X.functionField))
      (C.transition i j (f y) hi hj)
    change dominantFunctionFieldMap f (C.generator i : X.functionField) /
      dominantFunctionFieldMap f (C.generator j : X.functionField) ∈ regularAtSubring Y y
    simpa only [map_div₀] using h

@[simp] theorem dominantPullback_generator (i : C.index) :
    ((C.dominantPullback f).generator i : Y.functionField) =
      dominantFunctionFieldMap f (C.generator i : X.functionField) := rfl

@[simp] theorem localFrame_coordinates (i : C.index)
    (V : X.Opens) (hV : V≤C.openSet i) :
    ModuleFrame.coordinates (C.localFrame i) V hV = C.localCoordinates i V hV := rfl

theorem localFrame_generator_value (i : C.index) (V : X.Opens) [Nonempty V]
    (hV : V≤C.openSet i) :
    C.toCartierData.sectionValue V (ModuleFrame.generator (C.localFrame i) V hV) =
      (C.generator i : X.functionField) := by
  have h := C.localCoordinates_value i V hV (ModuleFrame.generator (C.localFrame i) V hV)
  rw [← localFrame_coordinates,ModuleFrame.coordinates_generator,map_one] at h
  change 1 = C.toCartierData.sectionValue V
    (ModuleFrame.generator (C.localFrame i) V hV)/(C.generator i : X.functionField) at h
  field_simp [Units.ne_zero] at h
  exact h.symm

/-- The pullback local frames have exactly the mapped regular transition
functions of the original frames. This is proved inside actual local
section rings and actual function fields. -/
theorem dominantPullback_frames_compatible :
    ModuleFrameGluing.Compatible
      (N := (Scheme.Modules.pushforward f).obj (C.dominantPullback f).sheaf)
      C.openSet C.localFrame
      (fun i=>ModuleFrame.generator ((C.dominantPullback f).localFrame i)
        (f ⁻¹ᵁ C.openSet i) le_rfl) := by
  intro i j V hi hj
  let B := C.dominantPullback f
  let W := f ⁻¹ᵁ V
  by_cases hW : Nonempty W
  · letI := hW
    let bi : B.index := i
    let bj : B.index := j
    have hWi : W≤B.openSet bi := f.preimage_mono hi
    have hWj : W≤B.openSet bj := f.preimage_mono hj
    letI : Nonempty V := ⟨⟨f (Classical.choice hW).val,(Classical.choice hW).property⟩⟩
    letI : Nonempty (f ⁻¹ᵁ C.openSet i) :=
      ⟨⟨(Classical.choice hW).val,hi (Classical.choice hW).property⟩⟩
    letI : Nonempty (f ⁻¹ᵁ C.openSet j) :=
      ⟨⟨(Classical.choice hW).val,hj (Classical.choice hW).property⟩⟩
    let a : Γ(X,V) := ModuleFrame.coordinates (C.localFrame j) V hj
      (ModuleFrame.generator (C.localFrame i) V hi)
    let b : Γ(Y,W) := f.app V a
    have ha : X.germToFunctionField V a =
        (C.generator i : X.functionField) / (C.generator j : X.functionField) := by
      calc
        _ = rationalValue X V (ModuleFrame.generator (C.localFrame i) V hi).val /
            (C.generator j : X.functionField) :=
          C.localCoordinates_value j V hj (ModuleFrame.generator (C.localFrame i) V hi)
        _ = C.toCartierData.sectionValue V (ModuleFrame.generator (C.localFrame i) V hi) /
            (C.generator j : X.functionField) :=
          congrArg (fun z : X.functionField => z / (C.generator j : X.functionField))
            (C.toCartierData_sectionValue V (ModuleFrame.generator (C.localFrame i) V hi)).symm
        _ = _ := congrArg (fun z : X.functionField => z / (C.generator j : X.functionField))
          (C.localFrame_generator_value i V hi)
    have hb : Y.germToFunctionField W b =
        (B.generator bi : Y.functionField) / (B.generator bj : Y.functionField) := by
      calc
        _ = dominantFunctionFieldMap f (X.germToFunctionField V a) :=
          (dominantFunctionFieldMap_germ f V a).symm
        _ = dominantFunctionFieldMap f
            ((C.generator i : X.functionField) / (C.generator j : X.functionField)) :=
          congrArg (dominantFunctionFieldMap f) ha
        _ = dominantFunctionFieldMap f (C.generator i : X.functionField) /
            dominantFunctionFieldMap f (C.generator j : X.functionField) :=
          map_div₀ (dominantFunctionFieldMap f) _ _
        _ = _ := rfl
    apply B.toCartierData.sectionValue_injective W
    change B.toCartierData.sectionValue W
        (moduleRes B.sheaf hWi
          (ModuleFrame.generator (B.localFrame bi) (B.openSet bi) le_rfl)) =
      B.toCartierData.sectionValue W
        (b • moduleRes B.sheaf hWj
          (ModuleFrame.generator (B.localFrame bj) (B.openSet bj) le_rfl))
    calc
      _ = B.toCartierData.sectionValue W (ModuleFrame.generator (B.localFrame bi) W hWi) :=
        congrArg (fun s : Γ(B.sheaf,W) => B.toCartierData.sectionValue W s)
          (ModuleFrame.generator_res (B.localFrame bi) le_rfl hWi)
      _ = (B.generator bi : Y.functionField) := B.localFrame_generator_value bi W hWi
      _ = ((B.generator bi : Y.functionField) / (B.generator bj : Y.functionField)) *
          (B.generator bj : Y.functionField) :=
        (div_mul_cancel₀ (B.generator bi : Y.functionField) (B.generator bj).ne_zero).symm
      _ = Y.germToFunctionField W b * (B.generator bj : Y.functionField) :=
        congrArg (fun z : Y.functionField => z * (B.generator bj : Y.functionField)) hb.symm
      _ = Y.germToFunctionField W b *
          B.toCartierData.sectionValue W (ModuleFrame.generator (B.localFrame bj) W hWj) :=
        congrArg (fun z : Y.functionField => Y.germToFunctionField W b * z)
          (B.localFrame_generator_value bj W hWj).symm
      _ = B.toCartierData.sectionValue W
          (b • ModuleFrame.generator (B.localFrame bj) W hWj) :=
        (B.toCartierData.sectionValue_smul W b
          (ModuleFrame.generator (B.localFrame bj) W hWj)).symm
      _ = _ :=
        congrArg (fun s : Γ(B.sheaf,W) => B.toCartierData.sectionValue W (b • s))
          (ModuleFrame.generator_res (B.localFrame bj) le_rfl hWj).symm
  · have hbot : W=⊥ := by
      apply le_antisymm ?_ bot_le
      intro y hy
      exact (hW ⟨⟨y,hy⟩⟩).elim
    letI := moduleSections_subsingleton_of_empty B.sheaf W hbot
    change (_ : Γ(B.sheaf,W)) = _
    exact Subsingleton.elim _ _

/-- The independent sheaf-pullback theorem identifies the fractional
construction with Mathlib's genuine module-sheaf pullback. -/
def dominantPullbackSheafIso :
    (Scheme.Modules.pullback f).obj C.sheaf ≅ (C.dominantPullback f).sheaf :=
  pullbackIso_of_compatible_frames f C.openSet C.covers C.localFrame
    (C.dominantPullback f).localFrame (C.dominantPullback_frames_compatible f)

theorem GeneratorRatioRegular.dominantPullback
    (D : RationalCartierCocycle X) (h : C.GeneratorRatioRegular D) :
    (C.dominantPullback f).GeneratorRatioRegular (D.dominantPullback f) := by
  intro i j y hi hj
  have hv := dominantFunctionFieldMap_mem_regularAt f y
    ((C.generator i : X.functionField)/(D.generator j : X.functionField))
    (h i j (f y) hi hj)
  change dominantFunctionFieldMap f (C.generator i : X.functionField) /
    dominantFunctionFieldMap f (D.generator j : X.functionField) ∈ regularAtSubring Y y
  simpa only [map_div₀] using hv

theorem dominantPullback_equivalent_of_equivalent
    (D : RationalCartierCocycle X) (h : C.toCartierData.Equivalent D.toCartierData) :
    (C.dominantPullback f).toCartierData.Equivalent
      (D.dominantPullback f).toCartierData :=
  (C.dominantPullback f).equivalent_of_generatorRatios (D.dominantPullback f)
    (GeneratorRatioRegular.dominantPullback f C D
      (C.generatorRatios_of_equivalent D h))
    (GeneratorRatioRegular.dominantPullback f D C
      (D.generatorRatios_of_equivalent C
        (C.toCartierData.equivalent_symm D.toCartierData h)))

/-- Composition is equality of actual Cartier divisors, proved using
generic-stalk functoriality and the original regular transition ratios. -/
theorem dominantPullback_comp_equivalent {Z : Scheme.{u}} [IsIntegral Z]
    (g : Z ⟶ Y) [IsDominant g] :
    ((C.dominantPullback f).dominantPullback g).toCartierData.Equivalent
      (C.dominantPullback (g≫f)).toCartierData := by
  apply RationalCartierCocycle.equivalent_of_generatorRatios
  · intro i j z hi hj
    have h := dominantFunctionFieldMap_mem_regularAt (g≫f) z
      ((C.generator i : X.functionField)/(C.generator j : X.functionField))
      (C.transition i j ((g≫f) z) hi hj)
    change dominantFunctionFieldMap g (dominantFunctionFieldMap f
        (C.generator i : X.functionField)) /
      dominantFunctionFieldMap (g≫f) (C.generator j : X.functionField) ∈ regularAtSubring Z z
    simpa only [dominantFunctionFieldMap_comp,RingHom.comp_apply,map_div₀] using h
  · intro i j z hi hj
    have h := dominantFunctionFieldMap_mem_regularAt (g≫f) z
      ((C.generator i : X.functionField)/(C.generator j : X.functionField))
      (C.transition i j ((g≫f) z) hi hj)
    change dominantFunctionFieldMap (g≫f) (C.generator i : X.functionField) /
      dominantFunctionFieldMap g (dominantFunctionFieldMap f
        (C.generator j : X.functionField)) ∈ regularAtSubring Z z
    simpa only [dominantFunctionFieldMap_comp,RingHom.comp_apply,map_div₀] using h

end RationalCartierCocycle

namespace CartierData

variable (D E : CartierData X)

/-- Pullback of an arbitrary actual Cartier divisor through a dominant
morphism, defined from its proved local rational presentation. -/
def dominantPullback : CartierData Y :=
  (D.localCocycle.dominantPullback f).toCartierData

def dominantPullbackSheafIso :
    (Scheme.Modules.pullback f).obj D.sheaf ≅ (D.dominantPullback f).sheaf :=
  (Scheme.Modules.pullback f).mapIso D.equivalent_localCocycle.choose ≪≫
    D.localCocycle.dominantPullbackSheafIso f

theorem dominantPullback_equivalent (h : D.Equivalent E) :
    (D.dominantPullback f).Equivalent (E.dominantPullback f) := by
  have hC : D.localCocycle.toCartierData.Equivalent E.localCocycle.toCartierData :=
    D.localCocycle.toCartierData.equivalent_trans D E.localCocycle.toCartierData
      (D.equivalent_symm D.localCocycle.toCartierData D.equivalent_localCocycle)
      (D.equivalent_trans E E.localCocycle.toCartierData h E.equivalent_localCocycle)
  exact D.localCocycle.dominantPullback_equivalent_of_equivalent f E.localCocycle hC

end CartierData

end PaperVerification.ToricSchemes
end
end Source_ToricDominantCartierPullback
-- END ORIGINAL PaperVerification.ToricDominantCartierPullback


