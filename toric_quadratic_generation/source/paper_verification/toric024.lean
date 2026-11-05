module

public import Lean.Elab.BuiltinEvalCommand
public meta import Lean.Elab.BuiltinEvalCommand
public import Lean.Util.CollectAxioms
public meta import Lean.Util.CollectAxioms
public import Lean.Util.FoldConsts
public meta import Lean.Util.FoldConsts
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.Preserves.Lattice
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.LocalAtTarget
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Topology.Sheaves.Module
public import paper_verification.toric010
public import paper_verification.toric022

@[expose] public section


-- BEGIN ORIGINAL PaperVerification.ToricInvertibleFractionalPresentation
section Source_ToricInvertibleFractionalPresentation

-- original header: module

-- original header: public import PaperVerification.ToricInvertibleAffine
-- original header: public import PaperVerification.ToricModuleFrameGluing

-- original header: @[expose] public section

/-!
# Every actual invertible sheaf has a fractional Cartier presentation

A frame near the generic point identifies sections on a nonempty open
with rational functions by restriction to the overlap. Local freeness
and injectivity of regular functions into the function field make this
map injective. The construction keeps the original module sheaf itself;
only an embedding into the genuine rational-function sheaf is chosen.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped Classical

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

variable {X : Scheme.{u}} [IsIntegral X] {M : X.Modules}

/-- Restriction of a locally rank-one sheaf to any nonempty smaller
open is injective on actual sections of an integral scheme. -/
theorem invertibleModule_restriction_injective (hM : IsInvertibleModule M)
    {U V : X.Opens} [Nonempty V] (hVU : V≤U) :
    Function.Injective (moduleRes M hVU) := by
  intro s t hst
  let A := invertibleOpen hM
  have hcover : ∀ x : X,∃ i,x∈A i :=
    fun x=>⟨x,mem_invertibleOpen hM x⟩
  apply module_sections_ext_cover M A hcover U
  intro i
  let W := U⊓A i
  by_cases hW : Nonempty W
  · letI := hW
    let Z := V⊓W
    letI : Nonempty Z := ⟨⟨genericPoint X,
      genericPoint_mem_open X V,genericPoint_mem_open X W⟩⟩
    let e : ModuleFrame M (A i) := invertibleFrame hM i
    apply (e.coordinates W inf_le_right).injective
    apply X.germToFunctionField_injective W
    have hZ := congrArg (moduleRes M (show Z≤V from inf_le_left)) hst
    have hZ' : moduleRes M (show Z≤W from inf_le_right)
        (moduleRes M (show W≤U from inf_le_left) s) =
      moduleRes M (show Z≤W from inf_le_right)
        (moduleRes M (show W≤U from inf_le_left) t) := by
      simpa only [moduleRes_trans] using hZ
    have hc := congrArg (e.coordinates Z (inf_le_right.trans inf_le_right)) hZ'
    have hr : regularRes (show Z≤W from inf_le_right)
        (e.coordinates W inf_le_right (moduleRes M (show W≤U from inf_le_left) s)) =
      regularRes (show Z≤W from inf_le_right)
        (e.coordinates W inf_le_right (moduleRes M (show W≤U from inf_le_left) t)) :=
      (e.coordinates_res (V := W) inf_le_right (show Z≤W from inf_le_right)
        (moduleRes M (show W≤U from inf_le_left) s)).symm.trans
          (hc.trans (e.coordinates_res (V := W) inf_le_right (show Z≤W from inf_le_right)
            (moduleRes M (show W≤U from inf_le_left) t)))
    have hg := congrArg (X.germToFunctionField Z) hr
    exact (germToFunctionField_restrict X (homOfLE (show Z≤W from inf_le_right)) _).symm.trans
      (hg.trans (germToFunctionField_restrict X (homOfLE (show Z≤W from inf_le_right)) _))
  · have hbot : W=⊥ := by
      apply le_antisymm
      · intro x hx
        exact False.elim (hW ⟨⟨x,hx⟩⟩)
      · exact bot_le
    letI := moduleSections_subsingleton_of_empty M W hbot
    exact Subsingleton.elim _ _

section GenericFrame

variable {U₀ : X.Opens} [Nonempty U₀] (e : ModuleFrame M U₀)

/-- The rational coordinate obtained by restricting to a fixed frame
near the generic point. Every nonempty overlap contains that point. -/
def genericFrameValue (V : X.Opens) [Nonempty V] (s : Γ(M,V)) :
    X.functionField :=
  letI : Nonempty (V⊓U₀ : X.Opens) := ⟨⟨genericPoint X,
    genericPoint_mem_open X V,genericPoint_mem_open X U₀⟩⟩
  X.germToFunctionField (V⊓U₀)
    (e.coordinates (V⊓U₀) inf_le_right (moduleRes M inf_le_left s))

@[simp] theorem genericFrameValue_add (V : X.Opens) [Nonempty V]
    (s t : Γ(M,V)) :
    genericFrameValue e V (s+t)=genericFrameValue e V s+genericFrameValue e V t := by
  simp only [genericFrameValue,moduleRes,map_add]

theorem genericFrameValue_smul (V : X.Opens) [Nonempty V]
    (a : Γ(X,V)) (s : Γ(M,V)) :
    genericFrameValue e V (a • s) =
      X.germToFunctionField V a * genericFrameValue e V s := by
  dsimp only [genericFrameValue]
  rw [moduleRes_smul,map_smul,smul_eq_mul,map_mul]
  rw [regularRes,germToFunctionField_restrict]

theorem genericFrameValue_restrict {U V : X.Opens} [Nonempty U] [Nonempty V]
    (hVU : V≤U) (s : Γ(M,U)) :
    genericFrameValue e V (moduleRes M hVU s)=genericFrameValue e U s := by
  letI : Nonempty (U⊓U₀ : X.Opens) := ⟨⟨genericPoint X,
    genericPoint_mem_open X U,genericPoint_mem_open X U₀⟩⟩
  letI : Nonempty (V⊓U₀ : X.Opens) := ⟨⟨genericPoint X,
    genericPoint_mem_open X V,genericPoint_mem_open X U₀⟩⟩
  have hW : V⊓U₀≤U⊓U₀ := inf_le_inf hVU le_rfl
  have hc := e.coordinates_res (V := U⊓U₀) inf_le_right hW
    (moduleRes M inf_le_left s)
  have hc' : e.coordinates (V⊓U₀) inf_le_right
      (moduleRes M inf_le_left (moduleRes M hVU s)) =
    regularRes hW (e.coordinates (U⊓U₀) inf_le_right
      (moduleRes M inf_le_left s)) := by
    simpa only [moduleRes_trans] using hc
  dsimp only [genericFrameValue]
  rw [hc',regularRes,germToFunctionField_restrict]

theorem genericFrameValue_injective (hM : IsInvertibleModule M)
    (V : X.Opens) [Nonempty V] : Function.Injective (genericFrameValue e V) := by
  letI : Nonempty (V⊓U₀ : X.Opens) := ⟨⟨genericPoint X,
    genericPoint_mem_open X V,genericPoint_mem_open X U₀⟩⟩
  intro s t hst
  apply invertibleModule_restriction_injective hM
    (show V⊓U₀≤V from inf_le_left)
  apply (e.coordinates (V⊓U₀) inf_le_right).injective
  exact X.germToFunctionField_injective (V⊓U₀) hst

/-- The actual rational-function section; the empty open is handled by
the zero section, as required by the sheaf axioms. -/
def genericFrameSection (V : X.Opens) (s : Γ(M,V)) : Γ(rationalFunctions X,V) :=
  if hV : Nonempty V then
    letI := hV
    (rationalValue X V).symm (genericFrameValue e V s)
  else 0

@[simp] theorem genericFrameSection_value (V : X.Opens) [Nonempty V]
    (s : Γ(M,V)) :
    rationalValue X V (genericFrameSection e V s)=genericFrameValue e V s := by
  simp only [genericFrameSection,dif_pos (show Nonempty V from inferInstance),
    AddEquiv.apply_symm_apply]

theorem genericFrameSection_add (V : X.Opens) (s t : Γ(M,V)) :
    genericFrameSection e V (s+t)=genericFrameSection e V s+genericFrameSection e V t := by
  by_cases hV : Nonempty V
  · letI := hV
    apply (rationalValue X V).injective
    rw [rationalValue_add,genericFrameSection_value,genericFrameSection_value,
      genericFrameSection_value,genericFrameValue_add]
  · simp only [genericFrameSection,dif_neg hV,zero_add]

theorem genericFrameSection_smul (V : X.Opens) (a : Γ(X,V)) (s : Γ(M,V)) :
    genericFrameSection e V (a • s)=a • genericFrameSection e V s := by
  by_cases hV : Nonempty V
  · letI := hV
    apply (rationalValue X V).injective
    rw [rationalValue_smul,genericFrameSection_value,genericFrameSection_value,
      genericFrameValue_smul]
  · simp only [genericFrameSection,dif_neg hV,smul_zero]

theorem genericFrameSection_restrict {U V : X.Opens} (hVU : V≤U) (s : Γ(M,U)) :
    moduleRes (rationalFunctions X) hVU (genericFrameSection e U s)=
      genericFrameSection e V (moduleRes M hVU s) := by
  by_cases hV : Nonempty V
  · letI := hV
    letI : Nonempty U := ⟨⟨(Classical.choice hV).val,
      hVU (Classical.choice hV).property⟩⟩
    apply (rationalValue X V).injective
    rw [moduleRes,rationalValue_restrict,genericFrameSection_value,
      genericFrameSection_value,genericFrameValue_restrict]
  · have hbot : V=⊥ := by
      apply le_antisymm
      · intro x hx
        exact False.elim (hV ⟨⟨x,hx⟩⟩)
      · exact bot_le
    letI := moduleSections_subsingleton_of_empty (rationalFunctions X) V hbot
    exact Subsingleton.elim _ _

/-- An actual module-sheaf morphism into the actual rational sheaf. -/
def genericFrameInclusion : M ⟶ rationalFunctions X where
  val.app V := ModuleCat.ofHom (X := M.val.obj V)
    (Y := (rationalFunctions X).val.obj V)
    { toFun := genericFrameSection e V.unop
      map_add' := genericFrameSection_add e V.unop
      map_smul' := genericFrameSection_smul e V.unop }
  val.naturality i := by
    ext s
    exact (genericFrameSection_restrict e i.unop.le s).symm

theorem genericFrameInclusion_injective (hM : IsInvertibleModule M) (V : X.Opens) :
    Function.Injective ((genericFrameInclusion e).app V) := by
  by_cases hV : Nonempty V
  · letI := hV
    intro s t hst
    apply genericFrameValue_injective e hM V
    change genericFrameSection e V s = genericFrameSection e V t at hst
    exact (genericFrameSection_value e V s).symm.trans
      ((congrArg (rationalValue X V) hst).trans (genericFrameSection_value e V t))
  · have hbot : V=⊥ := by
      apply le_antisymm
      · intro x hx
        exact False.elim (hV ⟨⟨x,hx⟩⟩)
      · exact bot_le
    letI := moduleSections_subsingleton_of_empty M V hbot
    exact fun _ _ _=>Subsingleton.elim _ _

end GenericFrame

/-- A fractional Cartier presentation of the original invertible sheaf.
The underlying sheaf is unchanged; its rational embedding is constructed. -/
def invertibleFractionalPresentation (M : X.Modules) (hM : IsInvertibleModule M) :
    CartierData X := by
  let U := invertibleOpen hM (genericPoint X)
  letI : Nonempty U := ⟨⟨genericPoint X,mem_invertibleOpen hM (genericPoint X)⟩⟩
  let e : ModuleFrame M U := invertibleFrame hM (genericPoint X)
  exact
    { sheaf := M
      inclusion := genericFrameInclusion e
      inclusion_injective := genericFrameInclusion_injective e hM
      locallyFree := hM }

@[simp] theorem invertibleFractionalPresentation_sheaf
    (M : X.Modules) (hM : IsInvertibleModule M) :
    (invertibleFractionalPresentation M hM).sheaf=M := rfl

/-- Every ordinary actual invertible sheaf is represented by genuine
fractional Cartier data on an integral scheme. -/
theorem exists_cartierData_of_isInvertibleModule
    (M : X.Modules) (hM : IsInvertibleModule M) :
    ∃ D : CartierData X,Nonempty (M≅D.sheaf) :=
  ⟨invertibleFractionalPresentation M hM,⟨Iso.refl M⟩⟩

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.exists_cartierData_of_isInvertibleModule
end
end Source_ToricInvertibleFractionalPresentation
-- END ORIGINAL PaperVerification.ToricInvertibleFractionalPresentation


-- BEGIN ORIGINAL PaperVerification.ToricInvertiblePullback
section Source_ToricInvertiblePullback

-- original header: module

-- original header: public import PaperVerification.ToricInvertibleFractionalPresentation
-- original header: public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
-- original header: public import Mathlib.Topology.Sheaves.Module
-- original header: public import Mathlib.CategoryTheory.Limits.Final
-- original header: public import Mathlib.CategoryTheory.Limits.Preserves.Lattice

-- original header: @[expose] public section

/-!
# Ordinary pullback preserves actual invertible module sheaves

The proof uses the genuine pullback pseudofunctor, the established
equivalence between an open subsite and its open subscheme, and the
ordinary pullback of the structure module. It applies to arbitrary
scheme morphisms, including nondominant closed immersions.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Scheme.Modules

namespace ModuleFrame

variable {X : Scheme.{u}} {M : X.Modules} {U : X.Opens}

/-- The actual open-subscheme version of a frame on the open subsite. -/
def toRestrictIso (e : ModuleFrame M U) :
    M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf :=
  ((overFunctorEquiv U).app M).symm ≪≫
    (overEquiv U).functor.mapIso e ≪≫
      U.sheafOfModulesEquivOverUnit X.ringCatSheaf

/-- Transport a genuine open-subscheme frame back to the open subsite. -/
def ofRestrictIso
    (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    ModuleFrame M U :=
  (overEquiv U).unitIso.app (M.over U) ≪≫
    (overEquiv U).inverse.mapIso ((overFunctorEquiv U).app M ≪≫ e) ≪≫
      U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf

end ModuleFrame

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
/-- The pullback of the actual structure module is the actual structure
module; finality here follows from preservation of the terminal open. -/
def pullbackUnitIso :
    (pullback f).obj (SheafOfModules.unit X.ringCatSheaf) ≅
      SheafOfModules.unit Y.ringCatSheaf := by
  letI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  letI : Limits.PreservesFiniteLimits (Opens.map f.base) := by
    change Limits.PreservesFiniteLimits (OrderHom.ofClass f.base.frameHom).toFunctor
    infer_instance
  letI : (Opens.map f.base).Final := inferInstance
  letI : IsIso (SheafOfModules.pullbackObjUnitToUnit
      (F := Opens.map f.base) (J := Opens.grothendieckTopology X)
      (K := Opens.grothendieckTopology Y) (S := X.ringCatSheaf)
      (R := Y.ringCatSheaf) f.toRingCatSheafHom) := inferInstance
  exact asIso (SheafOfModules.pullbackObjUnitToUnit
    (F := Opens.map f.base) (J := Opens.grothendieckTopology X)
    (K := Opens.grothendieckTopology Y) (S := X.ringCatSheaf)
    (R := Y.ringCatSheaf) f.toRingCatSheafHom)

namespace ModuleFrame

variable {M : X.Modules} {U : X.Opens} (e : ModuleFrame M U)

/-- The actual pullback frame, with its actual preimage open. -/
def pullbackRestrictIso :
    ((pullback f).obj M).restrict (f ⁻¹ᵁ U).ι ≅
      SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf := by
  let g : (f ⁻¹ᵁ U).toScheme ⟶ U.toScheme := f ∣_ U
  have hg : (f ⁻¹ᵁ U).ι ≫ f = g ≫ U.ι := by
    exact (morphismRestrict_ι f U).symm
  exact
    (restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).app ((pullback f).obj M) ≪≫
    (pullbackComp (f ⁻¹ᵁ U).ι f).app M ≪≫
    (pullbackCongr hg).app M ≪≫
    ((pullbackComp g U.ι).app M).symm ≪≫
    (pullback g).mapIso ((restrictFunctorIsoPullback U.ι).app M).symm ≪≫
    (pullback g).mapIso e.toRestrictIso ≪≫
    pullbackUnitIso g

def pullbackFrame : ModuleFrame ((pullback f).obj M) (f ⁻¹ᵁ U) :=
  ofRestrictIso (pullbackRestrictIso f e)

end ModuleFrame

/-- Pullback preserves genuine local rank one without a dominance,
flatness, smoothness, or integrality assumption on the morphism. -/
theorem isInvertibleModule_pullback {M : X.Modules} (hM : IsInvertibleModule M) :
    IsInvertibleModule ((pullback f).obj M) := by
  intro y
  obtain ⟨U,hy,⟨e⟩⟩ := hM (f y)
  exact ⟨f ⁻¹ᵁ U,hy,⟨ModuleFrame.pullbackFrame f e⟩⟩

/-- On an integral target of pullback, the pulled-back invertible sheaf
therefore has an actual fractional Cartier presentation as well. -/
theorem exists_cartierData_pullback [IsIntegral Y]
    {M : X.Modules} (hM : IsInvertibleModule M) :
    ∃ D : CartierData Y,Nonempty ((pullback f).obj M≅D.sheaf) :=
  exists_cartierData_of_isInvertibleModule _ (isInvertibleModule_pullback f hM)

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.isInvertibleModule_pullback
#print axioms PaperVerification.ToricSchemes.exists_cartierData_pullback
end
end Source_ToricInvertiblePullback
-- END ORIGINAL PaperVerification.ToricInvertiblePullback


-- BEGIN ORIGINAL PaperVerification.ToricRationalFrameComparison
section Source_ToricRationalFrameComparison

-- original header: module

-- original header: public import PaperVerification.ToricModuleFrameGluing
-- original header: public import PaperVerification.ToricCartierRangeEquality

-- original header: @[expose] public section

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
end
end Source_ToricRationalFrameComparison
-- END ORIGINAL PaperVerification.ToricRationalFrameComparison


-- BEGIN ORIGINAL PaperVerification.ToricProjectiveRatios
section Source_ToricProjectiveRatios

-- original header: module

-- original header: public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
-- original header: public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
-- original header: public import Mathlib.RingTheory.MvPolynomial.Homogeneous

-- original header: @[expose] public section

/-!
# Actual projective chart maps from homogeneous ratios

These maps use Mathlib's degree-zero homogeneous localization and its
actual affine open immersion into Proj. Homogeneous scaling cancels in
every fraction, so changing a local frame does not change the induced
projective morphism.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped Classical

section UnitEvaluation

variable {σ A B D : Type u} [CommRing A] [CommRing B] [CommRing D]
    [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ→σ) [GradedRing 𝒜]

/-- Homogeneous ratios may be evaluated in any ring when the selected
denominator is a unit. This is the actual affine-chart coordinate map. -/
def unitHomogeneousAwayEvaluation (F : A→+*B) (t : A) (ht : IsUnit (F t)) :
    Away 𝒜 t→+*B :=
  (Localization.awayLift F t ht).comp
    (algebraMap (Away 𝒜 t) (Localization.Away t))

theorem unitHomogeneousAwayEvaluation_mk_of_eq_one (F : A→+*B)
    {t : A} (ht : F t=1) {d : ℕ} (htd : t∈𝒜 d)
    (m : ℕ) (p : A) (hp : p∈𝒜 (m • d)) :
    unitHomogeneousAwayEvaluation 𝒜 F t (ht ▸ isUnit_one)
        (Away.mk 𝒜 htd m p hp)=F p := by
  change Localization.awayLift F t (ht ▸ isUnit_one)
    (Localization.mk p ⟨t^m,m,rfl⟩)=_
  rw [Localization.awayLift_mk F t p 1 (by simpa only [mul_one] using ht)]
  simp

theorem unitHomogeneousAwayEvaluation_map (F : A→+*B) (G : B→+*D)
    (t : A) (ht : IsUnit (F t)) :
    G.comp (unitHomogeneousAwayEvaluation 𝒜 F t ht)=
      unitHomogeneousAwayEvaluation 𝒜 (G.comp F) t (ht.map G) := by
  have h : G.comp (Localization.awayLift F t ht)=
      Localization.awayLift (G.comp F) t (ht.map G) := by
    apply IsLocalization.ringHom_ext (M := Submonoid.powers t)
    ext a
    simp only [RingHom.comp_apply,Localization.awayLift,IsLocalization.Away.lift_eq]
  exact congrArg (fun f=>f.comp (algebraMap (Away 𝒜 t) (Localization.Away t))) h

end UnitEvaluation

section HomogeneousEvaluation

variable {σ A K : Type u} [CommRing A] [Field K] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ→σ) [GradedRing 𝒜]

def homogeneousAwayEvaluation (F : A→+*K) (t : A) (ht : F t≠0) :
    Away 𝒜 t→+*K :=
  (Localization.awayLift F t (isUnit_iff_ne_zero.mpr ht)).comp
    (algebraMap (Away 𝒜 t) (Localization.Away t))

theorem homogeneousAwayEvaluation_mk (F : A→+*K) {t : A} (ht : F t≠0)
    {d : ℕ} (htd : t∈𝒜 d) (m : ℕ) (p : A) (hp : p∈𝒜 (m • d)) :
    homogeneousAwayEvaluation 𝒜 F t ht (Away.mk 𝒜 htd m p hp)=
      F p/(F t)^m := by
  change Localization.awayLift F t (isUnit_iff_ne_zero.mpr ht)
    (Localization.mk p ⟨t^m,m,rfl⟩)=_
  rw [Localization.awayLift_mk F t p (F t)⁻¹ (mul_inv_cancel₀ ht)]
  simp only [div_eq_mul_inv,inv_pow]

theorem homogeneousAwayEvaluation_awayMap (F : A→+*K)
    {t q x : A} {d : ℕ} (hq : q∈𝒜 d) (hx : x=t*q)
    (ht : F t≠0) (hxx : F x≠0) :
    (homogeneousAwayEvaluation 𝒜 F x hxx).comp (awayMap 𝒜 hq hx)=
      homogeneousAwayEvaluation 𝒜 F t ht := by
  let G : Localization.Away t→+*Localization.Away x :=
    Localization.awayLift (algebraMap A (Localization.Away x)) t
      (isUnit_of_dvd_unit (map_dvd _ ⟨q,hx⟩)
        (IsLocalization.Away.algebraMap_isUnit x))
  have hG : (Localization.awayLift F x (isUnit_iff_ne_zero.mpr hxx)).comp G =
      Localization.awayLift F t (isUnit_iff_ne_zero.mpr ht) := by
    apply IsLocalization.ringHom_ext (M := Submonoid.powers t)
    ext a
    simp only [RingHom.comp_apply,G,Localization.awayLift,IsLocalization.Away.lift_eq]
  ext a
  change Localization.awayLift F x (isUnit_iff_ne_zero.mpr hxx)
      ((awayMap 𝒜 hq hx a).val) =
    Localization.awayLift F t (isUnit_iff_ne_zero.mpr ht) a.val
  rw [val_awayMap]
  exact congrArg (fun g=>g a.val) hG

/-- An actual morphism into a genuine affine chart of Proj. -/
def projectiveFieldChart (F : A→+*K) (t : A) {d : ℕ}
    (htd : t∈𝒜 d) (hd : 0<d) (ht : F t≠0) :
    Spec (CommRingCat.of K)⟶Proj 𝒜 :=
  Spec.map (CommRingCat.ofHom (homogeneousAwayEvaluation 𝒜 F t ht)) ≫
    Proj.awayι 𝒜 t htd hd

theorem projectiveFieldChart_mul (F : A→+*K) (t q x : A)
    {d e : ℕ} (htd : t∈𝒜 d) (hqe : q∈𝒜 e) (hd : 0<d)
    (hx : x=t*q) (ht : F t≠0) (hxx : F x≠0) :
    projectiveFieldChart 𝒜 F t htd hd ht =
      projectiveFieldChart 𝒜 F x (hx ▸ SetLike.mul_mem_graded htd hqe)
        (hd.trans_le (Nat.le_add_right d e)) hxx := by
  unfold projectiveFieldChart
  rw [← homogeneousAwayEvaluation_awayMap 𝒜 F hqe hx ht hxx,
    CommRingCat.ofHom_comp,Spec.map_comp,Category.assoc,
    Proj.SpecMap_awayMap_awayι]

/-- A nonzero homogeneous coordinate may be chosen arbitrarily. -/
theorem projectiveFieldChart_independent (F : A→+*K) (t q : A)
    {d e : ℕ} (htd : t∈𝒜 d) (hqe : q∈𝒜 e) (hd : 0<d) (he : 0<e)
    (ht : F t≠0) (hq : F q≠0) :
    projectiveFieldChart 𝒜 F t htd hd ht =
      projectiveFieldChart 𝒜 F q hqe he hq := by
  have hp : F (t*q)≠0 := by rw [map_mul]; exact mul_ne_zero ht hq
  rw [projectiveFieldChart_mul 𝒜 F t q (t*q) htd hqe hd rfl ht hp,
    projectiveFieldChart_mul 𝒜 F q t (t*q) hqe htd he (mul_comm t q) hq hp]
  rfl

end HomogeneousEvaluation

section PolynomialScaling

attribute [local instance] MvPolynomial.gradedAlgebra

variable {ι R K : Type u} [CommRing R] [Field K]

/-- Scaling all variables multiplies a homogeneous polynomial by the
corresponding scalar power, over any field and in every degree. -/
theorem homogeneous_eval_scaled (F : R→+*K) (v : ι→K) (c : K)
    (p : MvPolynomial ι R) (d : ℕ) (hp : p.IsHomogeneous d) :
    p.eval₂ F (fun i=>c*v i)=c^d*p.eval₂ F v := by
  rw [MvPolynomial.eval₂_eq,MvPolynomial.eval₂_eq,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  simp_rw [mul_pow,Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum,← hp.degree_eq_sum_deg_support hm]
  ring

theorem homogeneousAwayEvaluation_scaled (F : R→+*K) (v : ι→K) (c : K)
    (hc : c≠0) (t : MvPolynomial ι R) {d : ℕ} (htd : t.IsHomogeneous d)
    (ht : t.eval₂ F v≠0) :
    homogeneousAwayEvaluation (MvPolynomial.homogeneousSubmodule ι R)
      (MvPolynomial.eval₂Hom F (fun i=>c*v i)) t
        (by rw [MvPolynomial.coe_eval₂Hom,homogeneous_eval_scaled F v c t d htd]
            exact mul_ne_zero (pow_ne_zero _ hc) ht) =
    homogeneousAwayEvaluation (MvPolynomial.homogeneousSubmodule ι R)
      (MvPolynomial.eval₂Hom F v) t ht := by
  ext z
  have htd' : t ∈ MvPolynomial.homogeneousSubmodule ι R d := htd
  obtain ⟨m,p,hp,rfl⟩ :=
    Away.mk_surjective (MvPolynomial.homogeneousSubmodule ι R) htd' z
  have hscaled : (MvPolynomial.eval₂Hom F (fun i=>c*v i)) t ≠ 0 := by
    change t.eval₂ F (fun i=>c*v i) ≠ 0
    rw [homogeneous_eval_scaled F v c t d htd]
    exact mul_ne_zero (pow_ne_zero _ hc) ht
  have hleft := homogeneousAwayEvaluation_mk (MvPolynomial.homogeneousSubmodule ι R)
    (MvPolynomial.eval₂Hom F (fun i=>c*v i)) hscaled htd' m p hp
  have hright := homogeneousAwayEvaluation_mk (MvPolynomial.homogeneousSubmodule ι R)
    (MvPolynomial.eval₂Hom F v) ht htd' m p hp
  refine hleft.trans (Eq.trans ?_ hright.symm)
  change p.eval₂ F (fun i=>c*v i) / (t.eval₂ F (fun i=>c*v i))^m =
    p.eval₂ F v / (t.eval₂ F v)^m
  rw [homogeneous_eval_scaled F v c p (m • d) hp,
    homogeneous_eval_scaled F v c t d htd,mul_pow]
  simp only [smul_eq_mul,Nat.mul_comm m d,pow_mul]
  field_simp [hc,ht]

/-- Frame rescaling leaves the actual morphism to projective space
unchanged, because its actual homogeneous-localization map is unchanged. -/
theorem projectiveFieldChart_scaled (F : R→+*K) (v : ι→K) (c : K)
    (hc : c≠0) (t : MvPolynomial ι R) {d : ℕ} (htd : t.IsHomogeneous d)
    (hd : 0<d) (ht : t.eval₂ F v≠0) :
    projectiveFieldChart (MvPolynomial.homogeneousSubmodule ι R)
      (MvPolynomial.eval₂Hom F (fun i=>c*v i)) t htd hd
        (by rw [MvPolynomial.coe_eval₂Hom,homogeneous_eval_scaled F v c t d htd]
            exact mul_ne_zero (pow_ne_zero _ hc) ht) =
    projectiveFieldChart (MvPolynomial.homogeneousSubmodule ι R)
      (MvPolynomial.eval₂Hom F v) t htd hd ht := by
  unfold projectiveFieldChart
  rw [homogeneousAwayEvaluation_scaled F v c hc t htd ht]

end PolynomialScaling
end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.projectiveFieldChart_independent
#print axioms PaperVerification.ToricSchemes.projectiveFieldChart_scaled
end
end Source_ToricProjectiveRatios
-- END ORIGINAL PaperVerification.ToricProjectiveRatios


-- BEGIN ORIGINAL PaperVerification.ToricAmpleDenominators
section Source_ToricAmpleDenominators

-- original header: module

-- original header: public import PaperVerification.ToricCartierAmple
-- original header: public import Mathlib.AlgebraicGeometry.AffineScheme
-- original header: public import Mathlib.RingTheory.Localization.Away.Basic

-- original header: @[expose] public section

/-!
# Clearing denominators by powers of an actual Cartier section

The local calculation is the universal property of localization on an
affine principal open. Quasi-compactness supplies one exponent for the
whole scheme. This is the section-extension step needed to construct an
embedding from an ample sheaf; it does not assume a fan or an embedding.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open scoped Classical

variable {X : Scheme.{u}} [IsIntegral X]

/-- A rational function regular on an affine principal open has a
denominator which is a power of its defining regular function. -/
theorem affine_regular_after_power
    (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U) (a : Γ(X,U))
    (r : X.functionField)
    (hr : ∀ x∈X.basicOpen a,r∈regularAtSubring X x) :
    ∃ N : ℕ,∀ x∈U,
      r*(X.germToFunctionField U a)^N∈regularAtSubring X x := by
  by_cases ha : X.germToFunctionField U a=0
  · exact ⟨1,by intro x hx; simp only [ha,pow_one,mul_zero]; exact Subring.zero_mem _⟩
  have hη : genericPoint X∈U := genericPoint_mem_open X U
  have hηa : genericPoint X∈X.basicOpen a := by
    rw [X.mem_basicOpen a (genericPoint X) hη]
    change IsUnit (X.germToFunctionField U a)
    exact isUnit_iff_ne_zero.mpr ha
  letI : Nonempty (X.basicOpen a) := ⟨⟨genericPoint X,hηa⟩⟩
  obtain ⟨s,hs⟩ := exists_regularSection_of_stalkwise X (X.basicOpen a) r hr
  letI : IsLocalization.Away a Γ(X,X.basicOpen a) := hU.isLocalization_basicOpen a
  obtain ⟨N,t,ht⟩ := IsLocalization.Away.surj a s
  have halg (v : Γ(X,U)) :
      X.germToFunctionField (X.basicOpen a)
        (algebraMap Γ(X,U) Γ(X,X.basicOpen a) v) = X.germToFunctionField U v :=
    germToFunctionField_restrict X (homOfLE (X.basicOpen_le a)) v
  have hrt : r*(X.germToFunctionField U a)^N=X.germToFunctionField U t := by
    have he := congrArg (X.germToFunctionField (X.basicOpen a)) ht
    simpa only [map_mul,map_pow,halg,hs] using he
  refine ⟨N,?_⟩
  intro x hx
  rw [hrt]
  exact regular_germ_mem_regularAt X U t x hx

namespace RationalCartierCocycle

variable (C : RationalCartierCocycle X)

def localCoefficientOn (i : C.index) (U : X.Opens) (hUi : U≤C.openSet i)
    (s : Γ(C.sheaf,⊤)) : Γ(X,U) :=
  X.presheaf.map (homOfLE hUi).op (C.localCoefficient i s)

theorem localCoefficientOn_value (i : C.index) (U : X.Opens) [Nonempty U]
    (hUi : U≤C.openSet i) (s : Γ(C.sheaf,⊤)) :
    X.germToFunctionField U (C.localCoefficientOn i U hUi s) =
      C.toCartierData.sectionValue ⊤ s/(C.generator i : X.functionField) := by
  letI : Nonempty (C.openSet i) :=
    ⟨⟨(Classical.choice (inferInstance : Nonempty U)).val,
      hUi (Classical.choice (inferInstance : Nonempty U)).property⟩⟩
  rw [localCoefficientOn,germToFunctionField_restrict,C.localCoefficient_value]

theorem localCoefficientOn_basicOpen (i : C.index) (U : X.Opens)
    (hUi : U≤C.openSet i) (s : Γ(C.sheaf,⊤)) :
    X.basicOpen (C.localCoefficientOn i U hUi s)=U⊓C.nonvanishingOpen s := by
  rw [localCoefficientOn,X.basicOpen_res]
  ext x
  constructor
  · rintro ⟨hx,hsa⟩
    exact ⟨hx,Opens.mem_iSup.mpr ⟨i,hsa⟩⟩
  · rintro ⟨hx,hs⟩
    refine ⟨hx,?_⟩
    exact (X.mem_basicOpen (C.localCoefficient i s) x (hUi hx)).mpr
      ((C.mem_nonvanishingOpen_iff i s x (hUi hx)).mp hs)

/-- Quasi-compactness gives finitely many actual affine opens carrying
chosen frames of this Cartier sheaf. -/
theorem exists_finite_affine_frame_cover [CompactSpace X] :
    ∃ (ι : Type u) (_ : Fintype ι) (U : ι→X.Opens) (i : ι→C.index),
      (∀ j,Nonempty (U j)) ∧ (∀ j,IsAffineOpen (U j)) ∧
      (∀ j,U j≤C.openSet (i j)) ∧ (⨆ j,U j)=⊤ := by
  classical
  have hlocal : ∀ x : X,∃ (i : C.index) (U : X.Opens),
      IsAffineOpen U ∧ x∈U ∧ U≤C.openSet i := by
    intro x
    obtain ⟨i,hi⟩ := C.covers x
    obtain ⟨U,hU,hx,hUi⟩ := exists_isAffineOpen_mem_and_subset hi
    exact ⟨i,U,hU,hx,hUi⟩
  choose i U hU hx hUi using hlocal
  have hcover : IsOpenCover U := by
    apply le_antisymm le_top
    intro x hxTop
    exact Opens.mem_iSup.mpr ⟨x,hx x⟩
  obtain ⟨t,ht⟩ := hcover.exists_finite_of_compactSpace
  exact ⟨t,inferInstance,fun j=>U j.val,fun j=>i j.val,
    fun j=>⟨⟨j.val,hx j.val⟩⟩,fun j=>hU j.val,fun j=>hUi j.val,ht⟩

/-- Every rational function regular where `s` is nonvanishing extends
after multiplication by every sufficiently large power of `s`. The
conclusion is an actual global section of the actual Cartier power. -/
theorem eventually_section_extension [CompactSpace X]
    (s : Γ(C.sheaf,⊤)) (r : X.functionField)
    (hr : ∀ x∈C.nonvanishingOpen s,r∈regularAtSubring X x) :
    ∃ N₀ : ℕ,0<N₀ ∧ ∀ N : ℕ,N₀≤N→
      ∃ t : Γ((C.pow N).sheaf,⊤),
        (C.pow N).toCartierData.sectionValue ⊤ t =
          r*(C.toCartierData.sectionValue ⊤ s)^N := by
  classical
  obtain ⟨ι,hι,U,i,hne,hU,hUi,hcover⟩ := C.exists_finite_affine_frame_cover
  letI : Fintype ι := hι
  letI (j : ι) : Nonempty (U j) := hne j
  let a (j : ι) := C.localCoefficientOn (i j) (U j) (hUi j) s
  have hloc (j : ι) : ∃ N : ℕ,∀ x∈U j,
      r*(X.germToFunctionField (U j) (a j))^N∈regularAtSubring X x := by
    apply affine_regular_after_power (U j) (hU j) (a j) r
    intro x hx
    have hsub : X.basicOpen (a j)≤C.nonvanishingOpen s := by
      rw [show a j=C.localCoefficientOn (i j) (U j) (hUi j) s from rfl,
        C.localCoefficientOn_basicOpen]
      exact inf_le_right
    exact hr x (hsub hx)
  choose N hN using hloc
  refine ⟨(∑ j,N j)+1,Nat.succ_pos _,?_⟩
  intro m hm
  let v := C.toCartierData.sectionValue ⊤ s
  have hNm (j : ι) : N j≤m :=
    (Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ j)).trans
      ((Nat.le_succ _).trans hm)
  have hregular (j : ι) (x : X) (hx : x∈U j) :
      r*(v/(C.generator (i j) : X.functionField))^m∈regularAtSubring X x := by
    have hold := hN j x hx
    rw [show a j=C.localCoefficientOn (i j) (U j) (hUi j) s from rfl,
      C.localCoefficientOn_value] at hold
    have hbase : v/(C.generator (i j) : X.functionField)∈regularAtSubring X x := by
      change rationalValue X ⊤ s.val / (C.generator (i j) : X.functionField) ∈
        regularAtSubring X x
      exact s.property (i j) ⟨x,trivial⟩ (hUi j hx)
    have hpow := (regularAtSubring X x).pow_mem hbase (m-N j)
    have he : r*(v/(C.generator (i j) : X.functionField))^m =
        (r*(v/(C.generator (i j) : X.functionField))^(N j))*
          (v/(C.generator (i j) : X.functionField))^(m-N j) := by
      rw [mul_assoc,← pow_add,Nat.add_sub_of_le (hNm j)]
    rw [he]
    exact (regularAtSubring X x).mul_mem hold hpow
  let raw : Γ(rationalFunctions X,⊤) := (rationalValue X ⊤).symm (r*v^m)
  have hrawvalue : rationalValue X ⊤ raw=r*v^m :=
    (rationalValue X ⊤).apply_symm_apply _
  have hraw : raw∈(C.pow m).presheafSubmodule.obj (op ⊤) := by
    intro l x hxl
    have hxcover : x.val∈⨆ j,U j := by rw [hcover]; trivial
    obtain ⟨j,hxj⟩ := Opens.mem_iSup.mp hxcover
    have hreg := hregular j x.val hxj
    have htrans := (regularAtSubring X x.val).pow_mem
      (C.transition (i j) l x.val (hUi j hxj) hxl) m
    have he : (r*(v/(C.generator (i j) : X.functionField))^m)*
        ((C.generator (i j) : X.functionField)/(C.generator l : X.functionField))^m =
          (r*v^m)/(C.generator l : X.functionField)^m := by
      rw [mul_assoc,← mul_pow,
        div_mul_div_cancel₀ (Units.ne_zero (C.generator (i j))),div_pow,mul_div_assoc]
    change rationalValue X ⊤ raw / (C.generator l : X.functionField)^m ∈
      regularAtSubring X x.val
    rw [hrawvalue]
    exact (congrArg (fun z : X.functionField => z∈regularAtSubring X x.val) he).mp
      ((regularAtSubring X x.val).mul_mem hreg htrans)
  refine ⟨⟨raw,hraw⟩,?_⟩
  change rationalValue X ⊤ raw=r*v^m
  exact (rationalValue X ⊤).apply_symm_apply _

theorem exists_section_extension [CompactSpace X]
    (s : Γ(C.sheaf,⊤)) (r : X.functionField)
    (hr : ∀ x∈C.nonvanishingOpen s,r∈regularAtSubring X x) :
    ∃ N : ℕ,0<N ∧ ∃ t : Γ((C.pow N).sheaf,⊤),
      (C.pow N).toCartierData.sectionValue ⊤ t =
        r*(C.toCartierData.sectionValue ⊤ s)^N := by
  obtain ⟨N,hN,h⟩ := C.eventually_section_extension s r hr
  obtain ⟨t,ht⟩ := h N le_rfl
  exact ⟨N,hN,t,ht⟩

end RationalCartierCocycle
end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.eventually_section_extension
end
end Source_ToricAmpleDenominators
-- END ORIGINAL PaperVerification.ToricAmpleDenominators


-- BEGIN ORIGINAL PaperVerification.ToricAmpleCommonPower
section Source_ToricAmpleCommonPower

-- original header: module

-- original header: public import PaperVerification.ToricAmpleDenominators

-- original header: @[expose] public section

/-! # A common positive power for a finite affine section cover -/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes.RationalCartierCocycle

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Classical

variable {X : Scheme.{u}} [IsIntegral X] (C : RationalCartierCocycle X)

/-- Flatten an arbitrary section of an iterated tensor power using the
literal equality of its local rational generators. -/
def flattenPowSection (a b : ℕ) (t : Γ(((C.pow a).pow b).sheaf,⊤)) :
    Γ((C.pow (a*b)).sheaf,⊤) := by
  refine ⟨t.val,?_⟩
  intro i x hx
  have ht : rationalValue X ⊤ t.val /
      ((C.generator i : X.functionField)^a)^b ∈ regularAtSubring X x.val :=
    t.property i x hx
  change rationalValue X ⊤ t.val / (C.generator i : X.functionField)^(a*b) ∈
    regularAtSubring X x.val
  simpa only [pow_mul] using ht

@[simp] theorem flattenPowSection_value (a b : ℕ)
    (t : Γ(((C.pow a).pow b).sheaf,⊤)) :
    (C.pow (a*b)).toCartierData.sectionValue ⊤ (C.flattenPowSection a b t)=
      ((C.pow a).pow b).toCartierData.sectionValue ⊤ t := rfl

theorem flattenPowSection_localCoefficient (a b : ℕ)
    (t : Γ(((C.pow a).pow b).sheaf,⊤)) (i : C.index) :
    (C.pow (a*b)).localCoefficient i (C.flattenPowSection a b t)=
      ((C.pow a).pow b).localCoefficient i t := by
  by_cases hU : Nonempty (C.openSet i)
  · letI := hU
    letI : Nonempty ((C.pow (a*b)).openSet i) := by
      change Nonempty (C.openSet i)
      exact hU
    letI : Nonempty (((C.pow a).pow b).openSet i) := by
      change Nonempty (C.openSet i)
      exact hU
    apply X.germToFunctionField_injective (C.openSet i)
    calc
      _ = (C.pow (a*b)).toCartierData.sectionValue ⊤ (C.flattenPowSection a b t) /
          (C.generator i : X.functionField)^(a*b) :=
        (C.pow (a*b)).localCoefficient_value i (C.flattenPowSection a b t)
      _ = ((C.pow a).pow b).toCartierData.sectionValue ⊤ t /
          ((C.generator i : X.functionField)^a)^b := by
        rw [C.flattenPowSection_value,pow_mul]
      _ = _ := (((C.pow a).pow b).localCoefficient_value i t).symm
  · have hbot : C.openSet i=⊥ := by
      apply le_antisymm ?_ bot_le
      intro x hx
      exact (hU ⟨⟨x,hx⟩⟩).elim
    letI := regularSections_subsingleton_of_empty X (C.openSet i) hbot
    change (_ : Γ(X,C.openSet i)) = _
    exact Subsingleton.elim _ _

theorem nonvanishingOpen_flattenPowSection (a b : ℕ)
    (t : Γ(((C.pow a).pow b).sheaf,⊤)) :
    (C.pow (a*b)).nonvanishingOpen (C.flattenPowSection a b t)=
      ((C.pow a).pow b).nonvanishingOpen t := by
  change (⨆ i : C.index,X.basicOpen ((C.pow (a*b)).localCoefficient i
      (C.flattenPowSection a b t))) =
    ⨆ i : C.index,X.basicOpen (((C.pow a).pow b).localCoefficient i t)
  apply iSup_congr
  intro i
  exact congrArg (fun r : Γ(X,C.openSet i) => X.basicOpen r)
    (C.flattenPowSection_localCoefficient a b t i)

/-- The actual power of a section, with nested Cartier powers identified
by their equal local rational generators. -/
def powerSection (a b : ℕ) (s : Γ((C.pow a).sheaf,⊤)) :
    Γ((C.pow (a*b)).sheaf,⊤) :=
  C.flattenPowSection a b ((C.pow a).sectionPow b s)

@[simp] theorem powerSection_value (a b : ℕ) (s : Γ((C.pow a).sheaf,⊤)) :
    (C.pow (a*b)).toCartierData.sectionValue ⊤ (C.powerSection a b s) =
      ((C.pow a).toCartierData.sectionValue ⊤ s)^b :=
  (C.flattenPowSection_value a b ((C.pow a).sectionPow b s)).trans
    ((C.pow a).sectionPow_value b s)

theorem powerSection_localCoefficient (a b : ℕ) (s : Γ((C.pow a).sheaf,⊤))
    (i : C.index) :
    (C.pow (a*b)).localCoefficient i (C.powerSection a b s) =
      ((C.pow a).localCoefficient i s)^b :=
  (C.flattenPowSection_localCoefficient a b ((C.pow a).sectionPow b s) i).trans
    ((C.pow a).localCoefficient_sectionPow b i s)

theorem nonvanishingOpen_powerSection (a b : ℕ) (hb : 0<b)
    (s : Γ((C.pow a).sheaf,⊤)) :
    (C.pow (a*b)).nonvanishingOpen (C.powerSection a b s)=
      (C.pow a).nonvanishingOpen s := by
  calc
    _ = ((C.pow a).pow b).nonvanishingOpen ((C.pow a).sectionPow b s) :=
      C.nonvanishingOpen_flattenPowSection a b ((C.pow a).sectionPow b s)
    _ = _ := (C.pow a).nonvanishingOpen_sectionPow b hb s

def powerSectionTo (a b N : ℕ) (h : a*b=N)
    (s : Γ((C.pow a).sheaf,⊤)) : Γ((C.pow N).sheaf,⊤) :=
  h ▸ C.powerSection a b s

theorem nonvanishingOpen_powerSectionTo (a b N : ℕ) (h : a*b=N) (hb : 0<b)
    (s : Γ((C.pow a).sheaf,⊤)) :
    (C.pow N).nonvanishingOpen (C.powerSectionTo a b N h s)=
      (C.pow a).nonvanishingOpen s := by
  subst N
  exact C.nonvanishingOpen_powerSection a b hb s

/-- One positive tensor power has finitely many actual sections whose
nonvanishing opens retain the affine cover supplied by ampleness. -/
theorem IsAmple.exists_common_power_affine_cover (hC : C.IsAmple) :
    ∃ (N : ℕ),0<N ∧ ∃ (ι : Type u) (_ : Fintype ι)
      (s : ι→Γ((C.pow N).sheaf,⊤)),
      (∀ i,IsAffineOpen ((C.pow N).nonvanishingOpen (s i))) ∧
      (⨆ i,(C.pow N).nonvanishingOpen (s i))=⊤ := by
  obtain ⟨ι,hι,n,s,hn,ha,hcover⟩ := hC.exists_finite_cover
  letI : Fintype ι := hι
  let N := ∏ i,n i
  have hN : 0<N := Finset.prod_pos (fun i _=>hn i)
  have hmultiple (i : ι) : ∃ b : ℕ,0<b ∧ n i*b=N := by
    have hdvd : n i∣N := Finset.dvd_prod_of_mem n (Finset.mem_univ i)
    obtain ⟨b,hb⟩ := hdvd
    refine ⟨b,?_,hb.symm⟩
    rw [hb] at hN
    exact (mul_pos_iff_of_pos_left (hn i)).mp hN
  choose b hb hmul using hmultiple
  let t (i : ι) := C.powerSectionTo (n i) (b i) N (hmul i) (s i)
  have hopen (i : ι) : (C.pow N).nonvanishingOpen (t i)=
      (C.pow (n i)).nonvanishingOpen (s i) :=
    C.nonvanishingOpen_powerSectionTo (n i) (b i) N (hmul i) (hb i) (s i)
  exact ⟨N,hN,ι,hι,t,(fun i=>by rw [hopen]; exact ha i),
    by simpa only [hopen] using hcover⟩

theorem IsAmple.exists_common_power_nonempty_affine_cover (hC : C.IsAmple) :
    ∃ (N : ℕ),0<N ∧ ∃ (ι : Type u) (_ : Fintype ι)
      (s : ι→Γ((C.pow N).sheaf,⊤)),
      (∀ i,Nonempty ((C.pow N).nonvanishingOpen (s i))) ∧
      (∀ i,IsAffineOpen ((C.pow N).nonvanishingOpen (s i))) ∧
      (⨆ i,(C.pow N).nonvanishingOpen (s i))=⊤ := by
  obtain ⟨N,hN,ι,hι,s,ha,hcover⟩ := hC.exists_common_power_affine_cover
  letI : Fintype ι := hι
  let J := {i : ι // Nonempty ((C.pow N).nonvanishingOpen (s i))}
  refine ⟨N,hN,J,inferInstance,(fun i=>s i),
    (fun i=>i.property),(fun i=>ha i),?_⟩
  apply top_unique
  intro x _
  have hx : x∈⨆ i,(C.pow N).nonvanishingOpen (s i) := by rw [hcover]; trivial
  obtain ⟨i,hxi⟩ := Opens.mem_iSup.mp hx
  exact Opens.mem_iSup.mpr ⟨⟨i,⟨⟨x,hxi⟩⟩⟩,hxi⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
set_option maxHeartbeats 2000000 in
/-- The actual rational product satisfies the precise successor-power
section predicate on the original Cartier cover. The two input predicates
are the literal membership conditions of their Cartier section modules. -/
theorem sectionSuccProduct_isSection (N : ℕ)
    (t s : Γ(rationalFunctions X,⊤))
    (ht : (C.pow N).IsSection ⊤ t) (hs : C.IsSection ⊤ s) :
    (C.pow (N+1)).IsSection ⊤ (rationalMul (X := X) (⊤ : X.Opens) t s) := by
  intro i x hx
  have ht' : rationalValue X ⊤ t / (C.generator i : X.functionField)^N ∈
      regularAtSubring X x.val := ht i x hx
  have hs' : rationalValue X ⊤ s / (C.generator i : X.functionField) ∈
      regularAtSubring X x.val := hs i x hx
  have h := (regularAtSubring X x.val).mul_mem ht' hs'
  have hvalue : rationalValue X ⊤ (rationalMul (X := X) (⊤ : X.Opens) t s) =
      rationalValue X ⊤ t * rationalValue X ⊤ s :=
    rationalValue_mul (X := X) (⊤ : X.Opens) t s
  change rationalValue X ⊤ (rationalMul (X := X) (⊤ : X.Opens) t s) /
    (C.generator i : X.functionField)^(N+1) ∈ regularAtSubring X x.val
  rw [hvalue]
  simpa only [pow_succ,div_mul_div_comm] using h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
/-- Multiply an actual section of the `N`th power by an actual section
of the original Cartier sheaf, retaining the literal local generators. -/
def sectionSuccProduct (N : ℕ) (t : Γ((C.pow N).sheaf,⊤))
    (s : Γ(C.sheaf,⊤)) : Γ((C.pow (N+1)).sheaf,⊤) :=
  ⟨rationalMul (X := X) (⊤ : X.Opens) t.val s.val,
    C.sectionSuccProduct_isSection N t.val s.val t.property s.property⟩

@[simp] theorem sectionSuccProduct_value (N : ℕ)
    (t : Γ((C.pow N).sheaf,⊤)) (s : Γ(C.sheaf,⊤)) :
    (C.pow (N+1)).toCartierData.sectionValue ⊤ (C.sectionSuccProduct N t s) =
      (C.pow N).toCartierData.sectionValue ⊤ t *
        C.toCartierData.sectionValue ⊤ s :=
  map_mul (rationalSectionValueIso X (⊤ : X.Opens)).hom.hom
    (show Γ(Spec X.functionField,genericPointMap X ⁻¹ᵁ (⊤ : X.Opens)) from t.val)
    (show Γ(Spec X.functionField,genericPointMap X ⁻¹ᵁ (⊤ : X.Opens)) from s.val)

theorem localCoefficient_sectionSuccProduct (N : ℕ)
    (t : Γ((C.pow N).sheaf,⊤)) (s : Γ(C.sheaf,⊤)) (i : C.index) :
    (C.pow (N+1)).localCoefficient i (C.sectionSuccProduct N t s) =
      (show Γ(X,C.openSet i) from (C.pow N).localCoefficient i t) *
        C.localCoefficient i s := by
  by_cases hU : Nonempty (C.openSet i)
  · letI := hU
    letI : Nonempty ((C.pow N).openSet i) := by
      change Nonempty (C.openSet i)
      exact hU
    letI : Nonempty ((C.pow (N+1)).openSet i) := by
      change Nonempty (C.openSet i)
      exact hU
    apply X.germToFunctionField_injective (C.openSet i)
    calc
      _ = (C.pow (N+1)).toCartierData.sectionValue ⊤ (C.sectionSuccProduct N t s) /
          (C.generator i : X.functionField)^(N+1) :=
        (C.pow (N+1)).localCoefficient_value i (C.sectionSuccProduct N t s)
      _ = ((C.pow N).toCartierData.sectionValue ⊤ t /
          (C.generator i : X.functionField)^N) *
          (C.toCartierData.sectionValue ⊤ s / (C.generator i : X.functionField)) := by
        rw [C.sectionSuccProduct_value,pow_succ,div_mul_div_comm]
      _ = X.germToFunctionField (C.openSet i) ((C.pow N).localCoefficient i t) *
          X.germToFunctionField (C.openSet i) (C.localCoefficient i s) :=
        congrArg₂ (fun a b : X.functionField => a*b)
          ((C.pow N).localCoefficient_value i t).symm (C.localCoefficient_value i s).symm
      _ = _ := (map_mul (X.germToFunctionField (C.openSet i)).hom _ _).symm
  · have hbot : C.openSet i=⊥ := by
      apply le_antisymm ?_ bot_le
      intro x hx
      exact (hU ⟨⟨x,hx⟩⟩).elim
    letI := regularSections_subsingleton_of_empty X (C.openSet i) hbot
    change (_ : Γ(X,C.openSet i)) = _
    exact Subsingleton.elim _ _

/-- Products vanish wherever either factor vanishes. This is a statement
about units in the genuine local rings, including boundary points. -/
theorem nonvanishingOpen_sectionSuccProduct (N : ℕ)
    (t : Γ((C.pow N).sheaf,⊤)) (s : Γ(C.sheaf,⊤)) :
    (C.pow (N+1)).nonvanishingOpen (C.sectionSuccProduct N t s) =
      (C.pow N).nonvanishingOpen t ⊓ C.nonvanishingOpen s := by
  ext x
  obtain ⟨i,hi⟩ := C.covers x
  change x∈(C.pow (N+1)).nonvanishingOpen (C.sectionSuccProduct N t s) ↔
    x∈(C.pow N).nonvanishingOpen t ∧ x∈C.nonvanishingOpen s
  rw [(C.pow (N+1)).mem_nonvanishingOpen_iff i _ x hi,
    (C.pow N).mem_nonvanishingOpen_iff i t x hi,
    C.mem_nonvanishingOpen_iff i s x hi]
  have hcoeff := C.localCoefficient_sectionSuccProduct N t s i
  have hg := congrArg
    (fun z : Γ(X,C.openSet i) => X.presheaf.germ (C.openSet i) x hi z) hcoeff
  have hm := map_mul (X.presheaf.germ (C.openSet i) x hi).hom
    (show Γ(X,C.openSet i) from (C.pow N).localCoefficient i t)
    (C.localCoefficient i s)
  exact (Iff.of_eq (congrArg IsUnit (hg.trans hm))).trans IsUnit.mul_iff

/-- Every principal open inside the nonvanishing locus of a Cartier
section is exactly the nonvanishing locus of a section of a positive
power. The extra multiplication by `s` excludes all boundary points. -/
theorem exists_power_section_basicOpen [CompactSpace X]
    (s : Γ(C.sheaf,⊤)) [Nonempty (C.nonvanishingOpen s)]
    (a : Γ(X,C.nonvanishingOpen s)) :
    ∃ N : ℕ,0<N ∧ ∃ t : Γ((C.pow N).sheaf,⊤),
      (C.pow N).nonvanishingOpen t=X.basicOpen a := by
  let r := X.germToFunctionField (C.nonvanishingOpen s) a
  obtain ⟨N,hN,t,ht⟩ := C.exists_section_extension s r
    (regular_germ_mem_regularAt X (C.nonvanishingOpen s) a)
  let w := C.sectionSuccProduct N t s
  refine ⟨N+1,Nat.succ_pos _,w,?_⟩
  have hsub : (C.pow (N+1)).nonvanishingOpen w≤C.nonvanishingOpen s := by
    rw [show w=C.sectionSuccProduct N t s from rfl,
      C.nonvanishingOpen_sectionSuccProduct]
    exact inf_le_right
  have hlocal (x : X) (hx : x∈C.nonvanishingOpen s) :
      x∈(C.pow (N+1)).nonvanishingOpen w ↔ x∈X.basicOpen a := by
    obtain ⟨i,hi⟩ := C.covers x
    letI : Nonempty (C.openSet i) := ⟨⟨x,hi⟩⟩
    letI : Nonempty ((C.pow N).openSet i) := by
      change Nonempty (C.openSet i)
      exact ⟨⟨x,hi⟩⟩
    have hsunit : IsUnit (X.presheaf.germ (C.openSet i) x hi
        (C.localCoefficient i s)) :=
      (C.mem_nonvanishingOpen_iff i s x hi).mp hx
    have hcoeff : X.presheaf.germ (C.openSet i) x hi
        ((C.pow N).localCoefficient i t) =
      X.presheaf.germ (C.nonvanishingOpen s) x hx a *
        (X.presheaf.germ (C.openSet i) x hi (C.localCoefficient i s))^N := by
      apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
      have hleft := X.algebraMap_germ_eq_germToFunctionField hi
        (show Γ(X,C.openSet i) from (C.pow N).localCoefficient i t)
      have htvalue : X.germToFunctionField (C.openSet i)
          (show Γ(X,C.openSet i) from (C.pow N).localCoefficient i t) =
          (C.pow N).toCartierData.sectionValue ⊤ t /
            (C.generator i : X.functionField)^N :=
        (C.pow N).localCoefficient_value i t
      have he : (C.pow N).toCartierData.sectionValue ⊤ t /
          (C.generator i : X.functionField)^N =
          r*(X.germToFunctionField (C.openSet i) (C.localCoefficient i s))^N := by
        calc
          _ = (r*(C.toCartierData.sectionValue ⊤ s)^N) /
              (C.generator i : X.functionField)^N :=
            congrArg (fun z : X.functionField => z/(C.generator i : X.functionField)^N) ht
          _ = r*(C.toCartierData.sectionValue ⊤ s/(C.generator i : X.functionField))^N := by
            rw [div_pow,mul_div_assoc]
          _ = _ := congrArg (fun z : X.functionField => r*z^N)
            (C.localCoefficient_value i s).symm
      let stalkMap := algebraMap (X.presheaf.stalk x) X.functionField
      have hright : stalkMap (X.presheaf.germ (C.nonvanishingOpen s) x hx a *
          (X.presheaf.germ (C.openSet i) x hi (C.localCoefficient i s))^N) =
          r*(X.germToFunctionField (C.openSet i) (C.localCoefficient i s))^N :=
        (map_mul stalkMap _ _).trans (congrArg₂ (· * ·)
          (X.algebraMap_germ_eq_germToFunctionField hx a)
          ((map_pow stalkMap _ N).trans (congrArg (fun z : X.functionField => z^N)
            (X.algebraMap_germ_eq_germToFunctionField hi (C.localCoefficient i s)))))
      exact (hleft.trans (htvalue.trans he)).trans hright.symm
    have hwp : (C.pow (N+1)).nonvanishingOpen w =
        (C.pow N).nonvanishingOpen t ⊓ C.nonvanishingOpen s :=
      C.nonvanishingOpen_sectionSuccProduct N t s
    have hw : x∈(C.pow (N+1)).nonvanishingOpen w ↔
        x∈(C.pow N).nonvanishingOpen t :=
      (Iff.of_eq (congrArg (fun V : X.Opens => x∈V) hwp)).trans (and_iff_left hx)
    have hunit : IsUnit (X.presheaf.germ (C.openSet i) x hi
        ((C.pow N).localCoefficient i t)) ↔
        IsUnit (X.presheaf.germ (C.nonvanishingOpen s) x hx a) :=
      (Iff.of_eq (congrArg IsUnit hcoeff)).trans
        (IsUnit.mul_iff.trans (and_iff_left (hsunit.pow N)))
    exact hw.trans (((C.pow N).mem_nonvanishingOpen_iff i t x hi).trans
      (hunit.trans (X.mem_basicOpen a x hx).symm))
  ext x
  constructor
  · intro hx
    exact (hlocal x (hsub hx)).mp hx
  · intro hx
    exact (hlocal x (X.basicOpen_le a hx)).mpr hx

/-- The affine-cover criterion for ampleness supplies affine
nonvanishing neighborhoods inside every prescribed open neighborhood. -/
theorem IsAmple.exists_affine_nonvanishing_subset (hC : C.IsAmple)
    {V : X.Opens} (x : X) (hx : x∈V) :
    ∃ N : ℕ,0<N ∧ ∃ t : Γ((C.pow N).sheaf,⊤),
      x∈(C.pow N).nonvanishingOpen t ∧
      (C.pow N).nonvanishingOpen t≤V ∧
      IsAffineOpen ((C.pow N).nonvanishingOpen t) := by
  letI : CompactSpace X := hC.1
  obtain ⟨a,ha,s,hxs,hUs⟩ := hC.2 x
  letI : Nonempty ((C.pow a).nonvanishingOpen s) := ⟨⟨x,hxs⟩⟩
  obtain ⟨f,hfV,hxf⟩ := hUs.exists_basicOpen_le ⟨x,hx⟩ hxs
  obtain ⟨b,hb,t,ht⟩ := (C.pow a).exists_power_section_basicOpen s f
  refine ⟨a*b,Nat.mul_pos ha hb,C.flattenPowSection a b t,?_⟩
  rw [C.nonvanishingOpen_flattenPowSection,ht]
  exact ⟨hxf,hfV,hUs.basicOpen f⟩

/-- The usual collection of affine nonvanishing opens of sections of
positive powers, without a fan or a projective embedding in its definition. -/
def affinePowerNonvanishingOpens : Set X.Opens :=
  {U | ∃ N : ℕ,0<N ∧ ∃ s : Γ((C.pow N).sheaf,⊤),
    U=(C.pow N).nonvanishingOpen s ∧ IsAffineOpen U}

/-- Equivalence with the ordinary topological-basis criterion for an
ample invertible sheaf on a quasi-compact integral scheme. -/
theorem isAmple_iff_isBasis_affinePowerNonvanishingOpens :
    C.IsAmple ↔ CompactSpace X ∧ Opens.IsBasis C.affinePowerNonvanishingOpens := by
  constructor
  · intro hC
    refine ⟨hC.1,Opens.isBasis_iff_nbhd.mpr ?_⟩
    intro V x hx
    obtain ⟨N,hN,s,hxs,hsub,haff⟩ :=
      IsAmple.exists_affine_nonvanishing_subset (C := C) hC x hx
    exact ⟨(C.pow N).nonvanishingOpen s,⟨N,hN,s,rfl,haff⟩,hxs,hsub⟩
  · rintro ⟨hcompact,hbasis⟩
    refine ⟨hcompact,?_⟩
    intro x
    obtain ⟨U,⟨N,hN,s,rfl,haff⟩,hx,-⟩ :=
      Opens.isBasis_iff_nbhd.mp hbasis (show x∈(⊤ : X.Opens) from trivial)
    exact ⟨N,hN,s,hx,haff⟩

end PaperVerification.ToricSchemes.RationalCartierCocycle

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.IsAmple.exists_common_power_affine_cover
#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.isAmple_iff_isBasis_affinePowerNonvanishingOpens

namespace PaperVerification.ToricSchemes.CartierData

open AlgebraicGeometry TopologicalSpace

variable {X : Scheme.{u}} [IsIntegral X] (D : CartierData X)

/-- The principal theorems' ampleness hypothesis is equivalent to the
standard affine nonvanishing-basis criterion for its actual Cartier sheaf. -/
theorem isAmple_iff_isBasis_affinePowerNonvanishingOpens :
    D.IsAmple ↔ CompactSpace X ∧
      Opens.IsBasis D.localCocycle.affinePowerNonvanishingOpens :=
  D.localCocycle.isAmple_iff_isBasis_affinePowerNonvanishingOpens

end PaperVerification.ToricSchemes.CartierData

#print axioms PaperVerification.ToricSchemes.CartierData.isAmple_iff_isBasis_affinePowerNonvanishingOpens
end
end Source_ToricAmpleCommonPower
-- END ORIGINAL PaperVerification.ToricAmpleCommonPower


-- BEGIN ORIGINAL PaperVerification.ToricSectionRatios
section Source_ToricSectionRatios

-- original header: module

-- original header: public import PaperVerification.ToricAmpleCommonPower
-- original header: public import PaperVerification.ToricCartierBaseSections

-- original header: @[expose] public section

/-! # Actual regular ratios of sections on nonvanishing opens -/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes.RationalCartierCocycle

open AlgebraicGeometry CategoryTheory TopologicalSpace

variable {X : Scheme.{u}} [IsIntegral X] (C : RationalCartierCocycle X)

theorem nonvanishing_iff_value (i : C.index) (s : Γ(C.sheaf,⊤))
    (x : X) (hxi : x∈C.openSet i) :
    x∈C.nonvanishingOpen s ↔
      C.toCartierData.sectionValue ⊤ s≠0 ∧
        (C.generator i : X.functionField)/C.toCartierData.sectionValue ⊤ s∈
          regularAtSubring X x := by
  rw [C.mem_nonvanishingOpen_iff i s x hxi,
    ← X.mem_basicOpen (C.localCoefficient i s) x hxi,
    C.mem_localNonvanishing_iff i s x hxi]

theorem sectionValue_ne_zero_of_nonvanishing (s : Γ(C.sheaf,⊤))
    [hU : Nonempty (C.nonvanishingOpen s)] : C.toCartierData.sectionValue ⊤ s≠0 := by
  let x := Classical.choice hU
  obtain ⟨i,hxi⟩ := C.covers x.val
  exact ((C.nonvanishing_iff_value i s x.val hxi).mp x.property).1

theorem section_ratio_regular (t s : Γ(C.sheaf,⊤))
    (x : X) (hx : x∈C.nonvanishingOpen s) :
    C.toCartierData.sectionValue ⊤ t/C.toCartierData.sectionValue ⊤ s∈
      regularAtSubring X x := by
  obtain ⟨i,hxi⟩ := C.covers x
  have hs := ((C.nonvanishing_iff_value i s x hxi).mp hx).2
  have ht : C.toCartierData.sectionValue ⊤ t/(C.generator i : X.functionField)∈
      regularAtSubring X x := by
    change rationalValue X ⊤ t.val / (C.generator i : X.functionField) ∈
      regularAtSubring X x
    exact t.property i ⟨x,trivial⟩ hxi
  have he : (C.toCartierData.sectionValue ⊤ t/(C.generator i : X.functionField))*
      ((C.generator i : X.functionField)/C.toCartierData.sectionValue ⊤ s) =
        C.toCartierData.sectionValue ⊤ t/C.toCartierData.sectionValue ⊤ s := by
    field_simp [Units.ne_zero]
  simpa only [he] using (regularAtSubring X x).mul_mem ht hs

/-- The quotient is an actual section of the structure sheaf on the
actual nonvanishing open, including its unique value on the empty open. -/
def ratioSection (t s : Γ(C.sheaf,⊤)) : Γ(X,C.nonvanishingOpen s) := by
  classical
  by_cases hU : Nonempty (C.nonvanishingOpen s)
  · letI := hU
    exact Classical.choose (exists_regularSection_of_stalkwise X
      (C.nonvanishingOpen s)
      (C.toCartierData.sectionValue ⊤ t/C.toCartierData.sectionValue ⊤ s)
      (C.section_ratio_regular t s))
  · exact 0

theorem ratioSection_value (t s : Γ(C.sheaf,⊤))
    [Nonempty (C.nonvanishingOpen s)] :
    X.germToFunctionField (C.nonvanishingOpen s) (C.ratioSection t s)=
      C.toCartierData.sectionValue ⊤ t/C.toCartierData.sectionValue ⊤ s := by
  unfold ratioSection
  rw [dif_pos (show Nonempty (C.nonvanishingOpen s) from inferInstance)]
  exact Classical.choose_spec (exists_regularSection_of_stalkwise X
    (C.nonvanishingOpen s)
    (C.toCartierData.sectionValue ⊤ t/C.toCartierData.sectionValue ⊤ s)
    (C.section_ratio_regular t s))

@[simp] theorem ratioSection_self (s : Γ(C.sheaf,⊤)) : C.ratioSection s s=1 := by
  classical
  by_cases hU : Nonempty (C.nonvanishingOpen s)
  · letI := hU
    apply X.germToFunctionField_injective (C.nonvanishingOpen s)
    rw [C.ratioSection_value,map_one,div_self (C.sectionValue_ne_zero_of_nonvanishing s)]
  · have hbot : C.nonvanishingOpen s=⊥ := by
      apply le_antisymm
      · intro x hx
        exact False.elim (hU ⟨⟨x,hx⟩⟩)
      · exact bot_le
    letI := regularSections_subsingleton_of_empty X (C.nonvanishingOpen s) hbot
    exact Subsingleton.elim _ _

/-- The coordinate ratio cuts out exactly the intersection of the two
actual nonvanishing opens. -/
theorem ratioSection_basicOpen (t s : Γ(C.sheaf,⊤)) :
    X.basicOpen (C.ratioSection t s)=C.nonvanishingOpen s⊓C.nonvanishingOpen t := by
  ext x
  by_cases hx : x∈C.nonvanishingOpen s
  · letI : Nonempty (C.nonvanishingOpen s) := ⟨⟨x,hx⟩⟩
    obtain ⟨i,hxi⟩ := C.covers x
    have hs0 := C.sectionValue_ne_zero_of_nonvanishing s
    have hsInv := ((C.nonvanishing_iff_value i s x hxi).mp hx).2
    have hs : C.toCartierData.sectionValue ⊤ s/(C.generator i : X.functionField)∈
        regularAtSubring X x := by
      change rationalValue X ⊤ s.val / (C.generator i : X.functionField) ∈
        regularAtSubring X x
      exact s.property i ⟨x,trivial⟩ hxi
    refine (X.mem_basicOpen (C.ratioSection t s) x hx).trans ?_
    change IsUnit (X.presheaf.germ (C.nonvanishingOpen s) x hx (C.ratioSection t s)) ↔
      x∈C.nonvanishingOpen s ∧ x∈C.nonvanishingOpen t
    rw [isUnit_stalk_iff,
      X.algebraMap_germ_eq_germToFunctionField hx,C.ratioSection_value]
    simp only [Opens.mem_inf,hx,true_and,inv_div]
    rw [C.nonvanishing_iff_value i t x hxi]
    constructor
    · rintro ⟨hfrac0,ht⟩
      refine ⟨(div_ne_zero_iff.mp hfrac0).1,?_⟩
      have he : ((C.generator i : X.functionField)/C.toCartierData.sectionValue ⊤ s)*
          (C.toCartierData.sectionValue ⊤ s/C.toCartierData.sectionValue ⊤ t)=
            (C.generator i : X.functionField)/C.toCartierData.sectionValue ⊤ t := by
        field_simp [hs0]
      simpa only [he] using (regularAtSubring X x).mul_mem hsInv ht
    · rintro ⟨ht0,ht⟩
      refine ⟨div_ne_zero ht0 hs0,?_⟩
      have he : (C.toCartierData.sectionValue ⊤ s/(C.generator i : X.functionField))*
          ((C.generator i : X.functionField)/C.toCartierData.sectionValue ⊤ t)=
            C.toCartierData.sectionValue ⊤ s/C.toCartierData.sectionValue ⊤ t := by
        field_simp [Units.ne_zero]
      simpa only [he] using (regularAtSubring X x).mul_mem hs ht
  · constructor
    · intro h
      exact (hx (X.basicOpen_le _ h)).elim
    · exact fun h=>(hx h.1).elim

end PaperVerification.ToricSchemes.RationalCartierCocycle

namespace PaperVerification.ToricSchemes.BaseSections

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

variable (k : Type u) [CommRing k] (X : Scheme.{u}) [IsIntegral X]
    [X.Over (Spec (CommRingCat.of k))]

theorem germ_scalarMap_top (U : X.Opens) [Nonempty U] (a : k) :
    X.germToFunctionField U (scalarMap k X U a)=
      X.germToFunctionField ⊤ (scalarMap k X ⊤ a) := by
  simp only [scalarMap,RingHom.comp_apply]
  rw [germToFunctionField_restrict,germToFunctionField_restrict]

end PaperVerification.ToricSchemes.BaseSections

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.ratioSection_basicOpen
end
end Source_ToricSectionRatios
-- END ORIGINAL PaperVerification.ToricSectionRatios


-- BEGIN ORIGINAL PaperVerification.ToricSectionProjectiveMap
section Source_ToricSectionProjectiveMap

-- original header: module

-- original header: public import PaperVerification.ToricSectionRatios
-- original header: public import PaperVerification.ToricProjectiveRatios
-- original header: public import PaperVerification.ToricDominantFunctionField
-- original header: public import Mathlib.AlgebraicGeometry.Gluing
-- original header: public import Mathlib.AlgebraicGeometry.Morphisms.Separated

-- original header: @[expose] public section

/-!
# The actual projective morphism defined by generating Cartier sections

The construction uses the genuine ratios in the structure sheaf on the
nonvanishing opens. Compatibility is proved on the generic stalk and then
on each integral overlap by separatedness of Proj. It does not assume a
sections-to-projective-space dictionary.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Classical

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{u}} [IsIntegral X]

theorem genericStalkMap_isDominant :
    IsDominant (X.fromSpecStalk (genericPoint X)) := by
  constructor
  rw [denseRange_iff_closure_range]
  apply Set.eq_univ_of_univ_subset
  rw [← (genericPoint_spec X).def]
  apply closure_mono
  exact Set.singleton_subset_iff.mpr
    ⟨IsLocalRing.closedPoint X.functionField,X.fromSpecStalk_closedPoint⟩

theorem genericStalkMapToOpen_isDominant (U : X.Opens)
    (hU : genericPoint X∈U) :
    IsDominant (U.fromSpecStalkOfMem (genericPoint X) hU) := by
  letI : IsDominant
      (U.fromSpecStalkOfMem (genericPoint X) hU ≫ U.ι) := by
    rw [U.fromSpecStalkOfMem_ι]
    exact genericStalkMap_isDominant
  exact IsDominant.of_comp_of_isOpenImmersion _ U.ι

theorem genericStalkMapToOpen_homOfLE {U V : X.Opens}
    (hUV : U≤V) (hU : genericPoint X∈U) (hV : genericPoint X∈V) :
    U.fromSpecStalkOfMem (genericPoint X) hU ≫ X.homOfLE hUV =
      V.fromSpecStalkOfMem (genericPoint X) hV := by
  rw [← cancel_mono V.ι]
  simp only [Category.assoc,Scheme.homOfLE_ι,
    Scheme.Opens.fromSpecStalkOfMem_ι]

/-- A variable lies in the degree-one piece of the actual polynomial grading. -/
theorem polynomialVariable_mem_degreeOne (k : Type u) [CommRing k]
    {ι : Type u} (i : ι) :
    (MvPolynomial.X i : MvPolynomial ι k) ∈ MvPolynomial.homogeneousSubmodule ι k 1 :=
  (MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X k i)

namespace RationalCartierCocycle

variable (k : Type u) [CommRing k] [X.Over (Spec (CommRingCat.of k))]
    (C : RationalCartierCocycle X) {ι : Type u}
    (s : ι→Γ(C.sheaf,⊤))

/-- The coordinate map of the chart where the i-th actual section does
not vanish. Its selected coordinate is literally one. -/
def sectionProjectiveChartRingMap (i : ι) :
    MvPolynomial ι k→+*Γ(X,C.nonvanishingOpen (s i)) :=
  MvPolynomial.eval₂Hom
    (BaseSections.scalarMap k X (C.nonvanishingOpen (s i)))
    (fun j=>C.ratioSection (s j) (s i))

@[simp] theorem sectionProjectiveChartRingMap_X (i j : ι) :
    C.sectionProjectiveChartRingMap k s i (MvPolynomial.X j)=
      C.ratioSection (s j) (s i) := by
  simp [sectionProjectiveChartRingMap]

@[simp] theorem sectionProjectiveChartRingMap_self (i : ι) :
    C.sectionProjectiveChartRingMap k s i (MvPolynomial.X i)=1 := by
  simp

/-- The chart map is a morphism of actual schemes through the actual
homogeneous degree-zero localization of the polynomial ring. -/
def sectionProjectiveChart (i : ι) :
    (C.nonvanishingOpen (s i)).toScheme⟶
      Proj (MvPolynomial.homogeneousSubmodule ι k) :=
  (C.nonvanishingOpen (s i)).toSpecΓ ≫
    Spec.map (CommRingCat.ofHom
      (unitHomogeneousAwayEvaluation (MvPolynomial.homogeneousSubmodule ι k)
        (C.sectionProjectiveChartRingMap k s i) (MvPolynomial.X i)
          (by rw [C.sectionProjectiveChartRingMap_self k s i]; exact isUnit_one))) ≫
    Proj.awayι (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X i)
      (polynomialVariable_mem_degreeOne k i) (by decide)

def sectionProjectiveFieldMap : MvPolynomial ι k→+*X.functionField :=
  MvPolynomial.eval₂Hom
    ((X.germToFunctionField ⊤).hom.comp (BaseSections.scalarMap k X ⊤))
    (fun j=>C.toCartierData.sectionValue ⊤ (s j))

theorem sectionProjectiveChartRingMap_germ (i : ι)
    [Nonempty (C.nonvanishingOpen (s i))] :
    (X.germToFunctionField (C.nonvanishingOpen (s i))).hom.comp
        (C.sectionProjectiveChartRingMap k s i) =
      MvPolynomial.eval₂Hom
        ((X.germToFunctionField ⊤).hom.comp (BaseSections.scalarMap k X ⊤))
        (fun j=>(C.toCartierData.sectionValue ⊤ (s i))⁻¹*
          C.toCartierData.sectionValue ⊤ (s j)) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply,sectionProjectiveChartRingMap,
      MvPolynomial.eval₂Hom_C]
    exact BaseSections.germ_scalarMap_top k X _ a
  · intro j
    rw [RingHom.comp_apply, C.sectionProjectiveChartRingMap_X k s i j,
      MvPolynomial.eval₂Hom_X', C.ratioSection_value]
    simp only [div_eq_mul_inv, mul_comm]

/-- Every local projective chart restricts to the projective point given
by the genuine rational values of the sections. -/
theorem sectionProjectiveChart_generic (i : ι)
    [Nonempty (C.nonvanishingOpen (s i))]
    (hη : genericPoint X∈C.nonvanishingOpen (s i)) :
    (C.nonvanishingOpen (s i)).fromSpecStalkOfMem (genericPoint X) hη ≫
        C.sectionProjectiveChart k s i =
      projectiveFieldChart (MvPolynomial.homogeneousSubmodule ι k)
        (C.sectionProjectiveFieldMap k s) (MvPolynomial.X i)
        (polynomialVariable_mem_degreeOne k i) (by decide)
        (by simpa [sectionProjectiveFieldMap] using
          C.sectionValue_ne_zero_of_nonvanishing (s i)) := by
  have hs := C.sectionValue_ne_zero_of_nonvanishing (s i)
  let F := (X.germToFunctionField ⊤).hom.comp (BaseSections.scalarMap k X ⊤)
  let v (j : ι) := C.toCartierData.sectionValue ⊤ (s j)
  have hcomp := unitHomogeneousAwayEvaluation_map
    (MvPolynomial.homogeneousSubmodule ι k)
    (C.sectionProjectiveChartRingMap k s i)
    (X.germToFunctionField (C.nonvanishingOpen (s i))).hom
    (MvPolynomial.X i)
    (by rw [C.sectionProjectiveChartRingMap_self k s i]; exact isUnit_one)
  let E := MvPolynomial.eval₂Hom F (fun j => (v i)⁻¹ * v j)
  have hEi : IsUnit (E (MvPolynomial.X i)) := by
    have hv : v i ≠ 0 := hs
    simp only [E, MvPolynomial.eval₂Hom_X', inv_mul_cancel₀ hv]
    exact isUnit_one
  have heval (F₁ F₂ : MvPolynomial ι k →+* X.functionField)
      (hF : F₁ = F₂) (h₁ : IsUnit (F₁ (MvPolynomial.X i)))
      (h₂ : IsUnit (F₂ (MvPolynomial.X i))) :
      unitHomogeneousAwayEvaluation (MvPolynomial.homogeneousSubmodule ι k)
          F₁ (MvPolynomial.X i) h₁ =
        unitHomogeneousAwayEvaluation (MvPolynomial.homogeneousSubmodule ι k)
          F₂ (MvPolynomial.X i) h₂ := by
    subst F₂
    rfl
  have hcomp' := hcomp.trans
    (heval _ E (C.sectionProjectiveChartRingMap_germ k s i) _ hEi)
  unfold sectionProjectiveChart
  rw [← Category.assoc,Scheme.Opens.fromSpecStalkOfMem_toSpecΓ,
    ← Category.assoc,← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
      ((X.germToFunctionField (C.nonvanishingOpen (s i))).hom.comp
        (unitHomogeneousAwayEvaluation _ _ _ _))) ≫ _ = _
  rw [hcomp']
  change projectiveFieldChart (MvPolynomial.homogeneousSubmodule ι k)
    (MvPolynomial.eval₂Hom F (fun j=>(v i)⁻¹*v j)) (MvPolynomial.X i)
      (polynomialVariable_mem_degreeOne k i) (by decide) (by exact hEi.ne_zero) = _
  exact projectiveFieldChart_scaled F v (v i)⁻¹ (inv_ne_zero hs)
    (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X k i) (by decide)
    (by simpa [v] using hs)

theorem sectionProjectiveChart_overlap (i j : ι) :
    X.homOfLE (U := C.nonvanishingOpen (s i)⊓C.nonvanishingOpen (s j))
        inf_le_left ≫ C.sectionProjectiveChart k s i =
      X.homOfLE inf_le_right ≫ C.sectionProjectiveChart k s j := by
  classical
  let U := C.nonvanishingOpen (s i)⊓C.nonvanishingOpen (s j)
  by_cases hU : Nonempty U
  · letI := hU
    letI : Nonempty (C.nonvanishingOpen (s i)) :=
      ⟨⟨(Classical.choice hU).val,(Classical.choice hU).property.1⟩⟩
    letI : Nonempty (C.nonvanishingOpen (s j)) :=
      ⟨⟨(Classical.choice hU).val,(Classical.choice hU).property.2⟩⟩
    have hηU : genericPoint X∈U := genericPoint_mem_open X U
    let η := U.fromSpecStalkOfMem (genericPoint X) hηU
    letI : IsDominant η := genericStalkMapToOpen_isDominant U hηU
    apply ext_of_isDominant η
    rw [← Category.assoc,← Category.assoc,
      genericStalkMapToOpen_homOfLE inf_le_left hηU hηU.1,
      genericStalkMapToOpen_homOfLE inf_le_right hηU hηU.2,
      C.sectionProjectiveChart_generic k s i hηU.1,
      C.sectionProjectiveChart_generic k s j hηU.2]
    exact projectiveFieldChart_independent
      (MvPolynomial.homogeneousSubmodule ι k) (C.sectionProjectiveFieldMap k s)
      (MvPolynomial.X i) (MvPolynomial.X j)
      (polynomialVariable_mem_degreeOne k i) (polynomialVariable_mem_degreeOne k j)
      (by decide) (by decide) _ _
  · letI : IsEmpty U := not_nonempty_iff.mp hU
    exact isInitialOfIsEmpty.hom_ext _ _

/-- Generating sections define an actual global morphism to Proj. -/
def sectionProjectiveMap
    (hcover : (⨆ i,C.nonvanishingOpen (s i))=⊤) :
    X⟶Proj (MvPolynomial.homogeneousSubmodule ι k) :=
  (X.openCoverOfIsOpenCover (fun i=>C.nonvanishingOpen (s i)) hcover).glueMorphisms
    (C.sectionProjectiveChart k s) (by
      intro i j
      change Limits.pullback.fst (C.nonvanishingOpen (s i)).ι
          (C.nonvanishingOpen (s j)).ι ≫ C.sectionProjectiveChart k s i =
        Limits.pullback.snd (C.nonvanishingOpen (s i)).ι
          (C.nonvanishingOpen (s j)).ι ≫ C.sectionProjectiveChart k s j
      apply (cancel_epi (isPullback_opens_inf
        (C.nonvanishingOpen (s i)) (C.nonvanishingOpen (s j))).isoPullback.hom).mp
      simpa only [Category.assoc,IsPullback.isoPullback_hom_fst_assoc,
        IsPullback.isoPullback_hom_snd_assoc] using
        C.sectionProjectiveChart_overlap k s i j)

@[reassoc (attr := simp)] theorem sectionProjectiveMap_chart
    (hcover : (⨆ i,C.nonvanishingOpen (s i))=⊤) (i : ι) :
    (C.nonvanishingOpen (s i)).ι ≫ C.sectionProjectiveMap k s hcover =
      C.sectionProjectiveChart k s i := by
  exact (X.openCoverOfIsOpenCover (fun i=>C.nonvanishingOpen (s i)) hcover).ι_glueMorphisms _ _ i

theorem sectionProjectiveChartRingMap_away_variable (i j : ι) :
    unitHomogeneousAwayEvaluation (MvPolynomial.homogeneousSubmodule ι k)
      (C.sectionProjectiveChartRingMap k s i) (MvPolynomial.X i)
      (by rw [C.sectionProjectiveChartRingMap_self k s i]; exact isUnit_one)
      (HomogeneousLocalization.Away.isLocalizationElem
        (polynomialVariable_mem_degreeOne k i) (polynomialVariable_mem_degreeOne k j)) =
        C.ratioSection (s j) (s i) := by
  have he := unitHomogeneousAwayEvaluation_mk_of_eq_one
    (MvPolynomial.homogeneousSubmodule ι k) (C.sectionProjectiveChartRingMap k s i)
    (C.sectionProjectiveChartRingMap_self k s i)
    (show (MvPolynomial.X i : MvPolynomial ι k) ∈
      MvPolynomial.homogeneousSubmodule ι k 1 from polynomialVariable_mem_degreeOne k i)
    1 ((MvPolynomial.X j : MvPolynomial ι k) ^ 1)
    (by simpa only [one_smul, pow_one] using polynomialVariable_mem_degreeOne k j)
  simpa only [HomogeneousLocalization.Away.isLocalizationElem, pow_one,
    C.sectionProjectiveChartRingMap_X k s i j] using he

theorem sectionProjectiveChart_preimage (i j : ι) :
    C.sectionProjectiveChart k s i ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X j)=
      (C.nonvanishingOpen (s i)).ι ⁻¹ᵁ C.nonvanishingOpen (s j) := by
  have he := C.sectionProjectiveChartRingMap_away_variable k s i j
  rw [sectionProjectiveChart,Scheme.Hom.comp_preimage,
    Scheme.Hom.comp_preimage,
    Proj.awayι_preimage_basicOpen (MvPolynomial.homogeneousSubmodule ι k)
      (polynomialVariable_mem_degreeOne k i) (by decide)
      (polynomialVariable_mem_degreeOne k j) (by decide),
    SpecMap_preimage_basicOpen,CommRingCat.ofHom_apply,he,
    Scheme.Opens.toSpecΓ_preimage_basicOpen,C.ratioSection_basicOpen]
  simp only [Scheme.Hom.preimage_inf,Scheme.Opens.ι_preimage_self,top_inf_eq]

/-- The projective basic opens have exactly the expected inverse images;
this is a statement about scheme morphisms and actual open subsets. -/
theorem sectionProjectiveMap_preimage
    (hcover : (⨆ i,C.nonvanishingOpen (s i))=⊤) (j : ι) :
    C.sectionProjectiveMap k s hcover ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X j)=
      C.nonvanishingOpen (s j) := by
  ext x
  have hx : x∈⨆ i,C.nonvanishingOpen (s i) := by rw [hcover]; trivial
  obtain ⟨i,hxi⟩ := Opens.mem_iSup.mp hx
  have hpre := congrArg (fun U=>((⟨x,hxi⟩ : C.nonvanishingOpen (s i))∈U))
    (C.sectionProjectiveChart_preimage k s i j)
  have hpre' : C.sectionProjectiveChart k s i ⟨x, hxi⟩ ∈
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X j) ↔
      x ∈ C.nonvanishingOpen (s j) := Iff.of_eq hpre
  have hchart : C.sectionProjectiveMap k s hcover x =
      C.sectionProjectiveChart k s i ⟨x, hxi⟩ :=
    congrArg (fun f : (C.nonvanishingOpen (s i)).toScheme ⟶
      Proj (MvPolynomial.homogeneousSubmodule ι k) => f ⟨x, hxi⟩)
      (C.sectionProjectiveMap_chart k s hcover i)
  change C.sectionProjectiveMap k s hcover x ∈
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X j) ↔
      x ∈ C.nonvanishingOpen (s j)
  rw [hchart]
  exact hpre'

end RationalCartierCocycle
end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.sectionProjectiveMap_chart
end
end Source_ToricSectionProjectiveMap
-- END ORIGINAL PaperVerification.ToricSectionProjectiveMap


-- BEGIN ORIGINAL PaperVerification.ToricSectionProjectiveBase
section Source_ToricSectionProjectiveBase

-- original header: module

-- original header: public import PaperVerification.ToricSectionProjectiveMap
-- original header: public import Mathlib.AlgebraicGeometry.Morphisms.Proper

-- original header: @[expose] public section

/-! # The section morphism preserves the actual base structure map -/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [CommRing k] (ι : Type u)

def polynomialGradeZeroScalarMap :
    k→+*MvPolynomial.homogeneousSubmodule ι k 0 where
  toFun a := ⟨MvPolynomial.C a,MvPolynomial.isHomogeneous_C ι a⟩
  map_one' := Subtype.ext (MvPolynomial.C.map_one)
  map_mul' a b := Subtype.ext (MvPolynomial.C.map_mul a b)
  map_zero' := Subtype.ext (MvPolynomial.C.map_zero)
  map_add' a b := Subtype.ext (MvPolynomial.C.map_add a b)

/-- The literal structural morphism of polynomial projective space. -/
def polynomialProjectiveToSpec :
    Proj (MvPolynomial.homogeneousSubmodule ι k)⟶Spec (CommRingCat.of k) :=
  Proj.toSpecZero (MvPolynomial.homogeneousSubmodule ι k) ≫
    Spec.map (CommRingCat.ofHom (polynomialGradeZeroScalarMap k ι))

instance polynomialProjectiveToSpec_isSeparated :
    IsSeparated (polynomialProjectiveToSpec k ι) := by
  unfold polynomialProjectiveToSpec
  infer_instance

namespace BaseSections

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]

theorem toSpec_scalarMap (U : X.Opens) :
    U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (scalarMap k X U)) =
      U.ι ≫ (X ↘ Spec (CommRingCat.of k)) := by
  unfold scalarMap
  rw [CommRingCat.ofHom_comp,CommRingCat.ofHom_comp,Spec.map_comp,
    Spec.map_comp,CommRingCat.ofHom_hom,CommRingCat.ofHom_hom,
    CommRingCat.ofHom_hom,← Category.assoc,
    Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top,Category.assoc,
    ← Scheme.toSpecΓ_naturality_assoc,toSpecΓ_SpecMap_ΓSpecIso_inv,
    Category.comp_id]

end BaseSections

namespace RationalCartierCocycle

variable {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of k))]
    (C : RationalCartierCocycle X) {ι : Type u} (s : ι→Γ(C.sheaf,⊤))

theorem sectionProjectiveChart_toSpec (i : ι) :
    C.sectionProjectiveChart k s i ≫ polynomialProjectiveToSpec k ι =
      (C.nonvanishingOpen (s i)).ι ≫ (X ↘ Spec (CommRingCat.of k)) := by
  let F := C.sectionProjectiveChartRingMap k s i
  have hunit : IsUnit (F (MvPolynomial.X i)) := by
    change IsUnit (C.sectionProjectiveChartRingMap k s i (MvPolynomial.X i))
    rw [C.sectionProjectiveChartRingMap_self k s i]
    exact isUnit_one
  let E := unitHomogeneousAwayEvaluation (MvPolynomial.homogeneousSubmodule ι k)
    F (MvPolynomial.X i) hunit
  have hscalar : E.comp
      ((HomogeneousLocalization.fromZeroRingHom
        (MvPolynomial.homogeneousSubmodule ι k) (Submonoid.powers (MvPolynomial.X i))).comp
          (polynomialGradeZeroScalarMap k ι))=
        BaseSections.scalarMap k X (C.nonvanishingOpen (s i)) := by
    ext a
    change Localization.awayLift F (MvPolynomial.X i) hunit
      (algebraMap (MvPolynomial ι k) (Localization.Away (MvPolynomial.X i))
        (MvPolynomial.C a))=_
    simp only [Localization.awayLift,IsLocalization.Away.lift_eq,
      F,sectionProjectiveChartRingMap,MvPolynomial.eval₂Hom_C]
  unfold sectionProjectiveChart polynomialProjectiveToSpec
  rw [Category.assoc,Category.assoc,Proj.awayι_toSpecZero_assoc,
    ← Spec.map_comp,← Spec.map_comp]
  change (C.nonvanishingOpen (s i)).toSpecΓ ≫
    Spec.map (CommRingCat.ofHom (E.comp
      ((HomogeneousLocalization.fromZeroRingHom
        (MvPolynomial.homogeneousSubmodule ι k) (Submonoid.powers (MvPolynomial.X i))).comp
          (polynomialGradeZeroScalarMap k ι))))=_
  rw [hscalar,BaseSections.toSpec_scalarMap]

theorem sectionProjectiveMap_toSpec
    (hcover : (⨆ i,C.nonvanishingOpen (s i))=⊤) :
    C.sectionProjectiveMap k s hcover ≫ polynomialProjectiveToSpec k ι =
      (X ↘ Spec (CommRingCat.of k)) := by
  apply (X.openCoverOfIsOpenCover (fun i=>C.nonvanishingOpen (s i)) hcover).hom_ext
  intro i
  change (C.nonvanishingOpen (s i)).ι ≫
      (C.sectionProjectiveMap k s hcover ≫ polynomialProjectiveToSpec k ι) =
    (C.nonvanishingOpen (s i)).ι ≫ (X ↘ Spec (CommRingCat.of k))
  rw [← Category.assoc,C.sectionProjectiveMap_chart k s hcover i,
    C.sectionProjectiveChart_toSpec k s i]

/-- Properness follows from the genuine base-compatible map to the
separated projective target. -/
theorem sectionProjectiveMap_isProper
    [IsProper (X ↘ Spec (CommRingCat.of k))]
    (hcover : (⨆ i,C.nonvanishingOpen (s i))=⊤) :
    IsProper (C.sectionProjectiveMap k s hcover) := by
  letI : IsProper
      (C.sectionProjectiveMap k s hcover ≫ polynomialProjectiveToSpec k ι) := by
    rw [C.sectionProjectiveMap_toSpec k s hcover]
    infer_instance
  exact IsProper.of_comp _ (polynomialProjectiveToSpec k ι)

end RationalCartierCocycle
end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.sectionProjectiveMap_isProper
end
end Source_ToricSectionProjectiveBase
-- END ORIGINAL PaperVerification.ToricSectionProjectiveBase


-- BEGIN ORIGINAL PaperVerification.ToricSectionProjectiveEmbedding
section Source_ToricSectionProjectiveEmbedding

-- original header: module

-- original header: public import PaperVerification.ToricSectionProjectiveBase
-- original header: public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
-- original header: public import Mathlib.Topology.LocalAtTarget

-- original header: @[expose] public section

/-! # A genuine closed immersion from actual affine coordinate generators -/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes.RationalCartierCocycle

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [CommRing k] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of k))]
    (C : RationalCartierCocycle X) {ι : Type u} (s : ι→Γ(C.sheaf,⊤))

def sectionProjectiveChartCoordinates (i : ι) :
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule ι k)
        (MvPolynomial.X i)→+*Γ(X,C.nonvanishingOpen (s i)) :=
  unitHomogeneousAwayEvaluation (MvPolynomial.homogeneousSubmodule ι k)
    (C.sectionProjectiveChartRingMap k s i) (MvPolynomial.X i)
    (by rw [C.sectionProjectiveChartRingMap_self k s i]; exact isUnit_one)

theorem sectionProjectiveChart_isPreimmersion (i : ι)
    (hU : IsAffineOpen (C.nonvanishingOpen (s i)))
    (hgen : Function.Surjective (C.sectionProjectiveChartCoordinates k s i)) :
    IsPreimmersion (C.sectionProjectiveChart k s i) := by
  letI : IsAffine (C.nonvanishingOpen (s i)) := hU
  letI : IsIso (C.nonvanishingOpen (s i)).toSpecΓ := by
    rw [← hU.isoSpec_hom]
    infer_instance
  letI : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (C.sectionProjectiveChartCoordinates k s i))) :=
    IsClosedImmersion.spec_of_surjective _ hgen
  let q := Spec.map (CommRingCat.ofHom (C.sectionProjectiveChartCoordinates k s i))
  let z := Proj.awayι (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X i)
    (polynomialVariable_mem_degreeOne k i) (by decide)
  letI : IsPreimmersion (C.nonvanishingOpen (s i)).toSpecΓ := by infer_instance
  letI : IsPreimmersion q := by dsimp only [q]; infer_instance
  letI : IsOpenImmersion z := by dsimp only [z]; infer_instance
  change IsPreimmersion ((C.nonvanishingOpen (s i)).toSpecΓ ≫ q ≫ z)
  exact IsPreimmersion.comp _ _

/-- If some of the nonvanishing affine charts cover X and their actual
ratio maps generate their coordinate rings, the section map is a
preimmersion. No global immersion statement is built into the premise. -/
theorem sectionProjectiveMap_isPreimmersion_of_chartGenerators
    (hcover : (⨆ i,C.nonvanishingOpen (s i))=⊤)
    {κ : Type u} (chooseChart : κ→ι)
    (hchosen : (⨆ i,C.nonvanishingOpen (s (chooseChart i)))=⊤)
    (ha : ∀ i,IsAffineOpen (C.nonvanishingOpen (s (chooseChart i))))
    (hgen : ∀ i,Function.Surjective
      (C.sectionProjectiveChartCoordinates k s (chooseChart i))) :
    IsPreimmersion (C.sectionProjectiveMap k s hcover) := by
  let f := C.sectionProjectiveMap k s hcover
  let U (i : κ) := C.nonvanishingOpen (s (chooseChart i))
  let V (i : κ) := Proj.basicOpen (MvPolynomial.homogeneousSubmodule ι k)
    (MvPolynomial.X (chooseChart i))
  have hlocal (i : κ) : IsPreimmersion ((U i).ι ≫ f) := by
    change IsPreimmersion ((C.nonvanishingOpen (s (chooseChart i))).ι ≫
      C.sectionProjectiveMap k s hcover)
    rw [C.sectionProjectiveMap_chart k s hcover (chooseChart i)]
    exact C.sectionProjectiveChart_isPreimmersion k s _ (ha i) (hgen i)
  letI : SurjectiveOnStalks f :=
    IsZariskiLocalAtSource.of_iSup_eq_top U hchosen (fun i=>by
      letI := hlocal i
      infer_instance)
  refine { isEmbedding := ?_ }
  apply isEmbedding_of_iSup_eq_top_of_preimage_subset_range f f.continuous V
    (V := fun i=>(U i).toScheme) (iV := fun i=>(U i).ι)
  · rintro y ⟨x,rfl⟩
    have hx : x∈⨆ i,U i := by rw [hchosen]; trivial
    obtain ⟨i,hxi⟩ := Opens.mem_iSup.mp hx
    apply Opens.mem_iSup.mpr
    refine ⟨i,?_⟩
    have hp := C.sectionProjectiveMap_preimage k s hcover (chooseChart i)
    change x ∈ C.sectionProjectiveMap k s hcover ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule ι k)
        (MvPolynomial.X (chooseChart i))
    rw [hp]
    exact hxi
  · intro i
    exact (U i).ι.continuous
  · intro i x hx
    have hp := C.sectionProjectiveMap_preimage k s hcover (chooseChart i)
    have hxi : x∈U i := by
      change x∈C.nonvanishingOpen (s (chooseChart i))
      rw [← hp]
      exact hx
    exact ⟨⟨x,hxi⟩,rfl⟩
  · intro i
    letI := hlocal i
    exact ((U i).ι ≫ f).isEmbedding

/-- Properness supplies the closed image. Together with the explicit
local coordinate-ring quotients this gives a genuine closed immersion. -/
theorem sectionProjectiveMap_isClosedImmersion_of_chartGenerators
    [IsProper (X ↘ Spec (CommRingCat.of k))]
    (hcover : (⨆ i,C.nonvanishingOpen (s i))=⊤)
    {κ : Type u} (chooseChart : κ→ι)
    (hchosen : (⨆ i,C.nonvanishingOpen (s (chooseChart i)))=⊤)
    (ha : ∀ i,IsAffineOpen (C.nonvanishingOpen (s (chooseChart i))))
    (hgen : ∀ i,Function.Surjective
      (C.sectionProjectiveChartCoordinates k s (chooseChart i))) :
    IsClosedImmersion (C.sectionProjectiveMap k s hcover) := by
  letI := C.sectionProjectiveMap_isPreimmersion_of_chartGenerators k s
    hcover chooseChart hchosen ha hgen
  letI := C.sectionProjectiveMap_isProper k s hcover
  exact IsClosedImmersion.of_isPreimmersion _
    (C.sectionProjectiveMap k s hcover).isClosedMap.isClosed_range

end PaperVerification.ToricSchemes.RationalCartierCocycle

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.sectionProjectiveMap_isClosedImmersion_of_chartGenerators
end
end Source_ToricSectionProjectiveEmbedding
-- END ORIGINAL PaperVerification.ToricSectionProjectiveEmbedding


-- BEGIN ORIGINAL PaperVerification.ToricSectionChartGenerators
section Source_ToricSectionChartGenerators

-- original header: module

-- original header: public import PaperVerification.ToricSectionProjectiveEmbedding
-- original header: public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
-- original header: public import Mathlib.RingTheory.FiniteType

-- original header: @[expose] public section

/-! # Actual affine coordinate generators as ratios of global sections -/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped Classical BaseSections

attribute [local instance] MvPolynomial.gradedAlgebra

namespace BaseSections

variable (k : Type u) [CommRing k] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))]

theorem scalarMap_finiteType [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    (U : X.Opens) (hU : IsAffineOpen U) :
    (scalarMap k X U).FiniteType := by
  let f := X ↘ Spec (CommRingCat.of k)
  have htop := f.finiteType_appLE (isAffineOpen_top _) hU
    (show U≤f ⁻¹ᵁ ⊤ by simp)
  have hc := RingHom.FiniteType.of_surjective
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
    (ConcreteCategory.bijective_of_isIso _).2
  convert htop.comp hc using 1
  ext a
  simp only [scalarMap,RingHom.comp_apply,Scheme.Hom.appLE,
    CommRingCat.hom_comp,ConcreteCategory.comp_apply]
  rfl

theorem exists_finite_polynomial_generators
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    (U : X.Opens) (hU : IsAffineOpen U) :
    ∃ (ι : Type u) (_ : Fintype ι) (g : ι→Γ(X,U)),
      Function.Surjective (MvPolynomial.eval₂Hom (scalarMap k X U) g) := by
  letI : Algebra.FiniteType k Γ(X,U) := scalarMap_finiteType k U hU
  obtain ⟨g,F,hF⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial.mp
    (show Algebra.FiniteType k Γ(X,U) from inferInstance))
  refine ⟨g,inferInstance,(fun j=>F (MvPolynomial.X j)),?_⟩
  have he : MvPolynomial.eval₂Hom (scalarMap k X U)
      (fun j=>F (MvPolynomial.X j))=F.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      rw [MvPolynomial.eval₂Hom_C]
      change algebraMap k Γ(X,U) a = F (algebraMap k (MvPolynomial g k) a)
      exact (F.commutes a).symm
    · intro j
      simp
  rw [he]
  change Function.Surjective F
  exact hF

end BaseSections

namespace RationalCartierCocycle

variable (k : Type u) [CommRing k] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of k))]
    (C : RationalCartierCocycle X) {ι : Type u} (s : ι→Γ(C.sheaf,⊤))

def sectionProjectiveChartConstant (s : ι→Γ(C.sheaf,⊤)) (i : ι) :
    k→+*HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule ι k)
      (MvPolynomial.X i) :=
  (HomogeneousLocalization.fromZeroRingHom (MvPolynomial.homogeneousSubmodule ι k)
    (Submonoid.powers (MvPolynomial.X i))).comp (polynomialGradeZeroScalarMap k ι)

@[simp] theorem sectionProjectiveChartCoordinates_constant (i : ι) (a : k) :
    C.sectionProjectiveChartCoordinates k s i
        (C.sectionProjectiveChartConstant k s i a)=
      BaseSections.scalarMap k X (C.nonvanishingOpen (s i)) a := by
  change Localization.awayLift (C.sectionProjectiveChartRingMap k s i)
    (MvPolynomial.X i)
      (by rw [C.sectionProjectiveChartRingMap_self k s i]; exact isUnit_one)
      (algebraMap (MvPolynomial ι k) (Localization.Away (MvPolynomial.X i))
        (MvPolynomial.C a))=_
  simp only [Localization.awayLift,IsLocalization.Away.lift_eq,
    sectionProjectiveChartRingMap,MvPolynomial.eval₂Hom_C]

@[simp] theorem sectionProjectiveChartCoordinates_variable (i j : ι) :
    C.sectionProjectiveChartCoordinates k s i
      (HomogeneousLocalization.Away.isLocalizationElem
        (MvPolynomial.isHomogeneous_X k i) (MvPolynomial.isHomogeneous_X k j))=
      C.ratioSection (s j) (s i) := by
  exact C.sectionProjectiveChartRingMap_away_variable k s i j

/-- Every polynomial in actual generating ratios lifts to an actual
element of the homogeneous affine chart ring. -/
theorem sectionProjectiveChartCoordinates_surjective_of_polynomial_generators
    (i : ι) {κ : Type u} (j : κ→ι)
    (g : κ→Γ(X,C.nonvanishingOpen (s i)))
    (hpoly : Function.Surjective (MvPolynomial.eval₂Hom
      (BaseSections.scalarMap k X (C.nonvanishingOpen (s i))) g))
    (hgen : ∀ t,C.ratioSection (s (j t)) (s i)=g t) :
    Function.Surjective (C.sectionProjectiveChartCoordinates k s i) := by
  let F := MvPolynomial.eval₂Hom (C.sectionProjectiveChartConstant k s i)
    (fun t=>HomogeneousLocalization.Away.isLocalizationElem
      (MvPolynomial.isHomogeneous_X k i) (MvPolynomial.isHomogeneous_X k (j t)))
  have hcomp : (C.sectionProjectiveChartCoordinates k s i).comp F=
      MvPolynomial.eval₂Hom
        (BaseSections.scalarMap k X (C.nonvanishingOpen (s i))) g := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply,F,MvPolynomial.eval₂Hom_C,
        C.sectionProjectiveChartCoordinates_constant k s i a]
    · intro t
      simp only [RingHom.comp_apply,F,MvPolynomial.eval₂Hom_X',
        C.sectionProjectiveChartCoordinates_variable k s i (j t),hgen t]
  have hs : Function.Surjective ((C.sectionProjectiveChartCoordinates k s i).comp F) := by
    rw [hcomp]
    exact hpoly
  exact Function.Surjective.of_comp hs

end RationalCartierCocycle
end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.sectionProjectiveChartCoordinates_surjective_of_polynomial_generators
end
end Source_ToricSectionChartGenerators
-- END ORIGINAL PaperVerification.ToricSectionChartGenerators


-- BEGIN ORIGINAL PaperVerification.ToricAmpleProjectiveEmbedding
section Source_ToricAmpleProjectiveEmbedding

-- original header: module

-- original header: public import PaperVerification.ToricSectionChartGenerators
-- original header: public import PaperVerification.ToricBaseSectionNaturality

-- original header: @[expose] public section

/-!
# A finite projective embedding obtained from intrinsic ampleness

Choose finite generators in each genuine affine nonvanishing chart.
The denominator lemma extends every generator after multiplication by a
common positive power of the chart section. Those finitely many actual
global sections give all coordinate-ring quotients needed by the closed
immersion theorem.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped Classical BaseSections

attribute [local instance] MvPolynomial.gradedAlgebra

namespace BaseSections

theorem polynomial_generators_transport (k : Type u) [CommRing k]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    {U V : X.Opens} (h : U=V) {ι : Type u} (g : ι→Γ(X,V))
    (hg : Function.Surjective (MvPolynomial.eval₂Hom (scalarMap k X V) g)) :
    Function.Surjective (MvPolynomial.eval₂Hom (scalarMap k X U)
      (fun j=>X.presheaf.map (eqToHom h).op (g j))) := by
  subst V
  have hid : (fun j => X.presheaf.map (eqToHom (rfl : U = U)).op (g j)) = g := by
    funext j
    change X.presheaf.map (𝟙 (op U)) (g j) = g j
    exact congrArg (fun f : Γ(X,U) ⟶ Γ(X,U) => f (g j))
      (X.presheaf.map_id (op U))
  rw [hid]
  exact hg

end BaseSections

namespace RationalCartierCocycle

variable (k : Type u) [CommRing k] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    (C : RationalCartierCocycle X)

/-- The finite ratio-generation construction, before using properness.
The output sections belong to an actual positive tensor power. -/
theorem exists_power_chart_generators [CompactSpace X]
    {ι : Type u} [Fintype ι] (s : ι→Γ(C.sheaf,⊤))
    (hnonempty : ∀ i,Nonempty (C.nonvanishingOpen (s i)))
    (ha : ∀ i,IsAffineOpen (C.nonvanishingOpen (s i)))
    (hcover : (⨆ i,C.nonvanishingOpen (s i))=⊤) :
    ∃ N : ℕ,0<N ∧ ∃ (J : Type u) (_ : Fintype J)
      (t : J→Γ((C.pow N).sheaf,⊤)) (chooseChart : ι→J),
      (∀ i,t (chooseChart i)=C.sectionPow N (s i)) ∧
      (⨆ j,(C.pow N).nonvanishingOpen (t j))=⊤ ∧
      (⨆ i,(C.pow N).nonvanishingOpen (t (chooseChart i)))=⊤ ∧
      (∀ i,IsAffineOpen ((C.pow N).nonvanishingOpen (t (chooseChart i)))) ∧
      (∀ i,Function.Surjective
        ((C.pow N).sectionProjectiveChartCoordinates k t (chooseChart i))) := by
  choose G hG g hg using fun i=>BaseSections.exists_finite_polynomial_generators
    k (C.nonvanishingOpen (s i)) (ha i)
  letI (i : ι) : Fintype (G i) := hG i
  letI (i : ι) : Nonempty (C.nonvanishingOpen (s i)) := hnonempty i
  let P := (i : ι) × G i
  let r (p : P) : X.functionField :=
    X.germToFunctionField (C.nonvanishingOpen (s p.1)) (g p.1 p.2)
  have hext (p : P) : ∃ B : ℕ,0<B ∧ ∀ N : ℕ,B≤N→
      ∃ u : Γ((C.pow N).sheaf,⊤),
        (C.pow N).toCartierData.sectionValue ⊤ u=
          r p*(C.toCartierData.sectionValue ⊤ (s p.1))^N :=
    C.eventually_section_extension (s p.1) (r p)
      (regular_germ_mem_regularAt X _ (g p.1 p.2))
  choose B hB hext using hext
  let N := (∑ p : P,B p)+1
  have hN : 0<N := Nat.succ_pos _
  have hBN (p : P) : B p≤N :=
    (Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ p)).trans
      (Nat.le_add_right _ 1)
  choose u hu using fun p : P=>hext p N (hBN p)
  let J := ι⊕P
  let t : J→Γ((C.pow N).sheaf,⊤) :=
    Sum.elim (fun i=>C.sectionPow N (s i)) u
  have hopen (i : ι) : (C.pow N).nonvanishingOpen (t (Sum.inl i))=
      C.nonvanishingOpen (s i) := C.nonvanishingOpen_sectionPow N hN (s i)
  have hc : (⨆ i,(C.pow N).nonvanishingOpen (t (Sum.inl i)))=⊤ := by
    simpa only [hopen] using hcover
  refine ⟨N,hN,J,inferInstance,t,Sum.inl,(fun _=>rfl),?_,hc,?_,?_⟩
  · apply top_unique
    rw [← hc]
    exact iSup_le fun i=>le_iSup_of_le (Sum.inl i) le_rfl
  · intro i
    rw [hopen]
    exact ha i
  · intro i
    let U := (C.pow N).nonvanishingOpen (t (Sum.inl i))
    letI : Nonempty U := by
      obtain ⟨x⟩ := hnonempty i
      refine ⟨⟨x.val, ?_⟩⟩
      change x.val ∈ (C.pow N).nonvanishingOpen (t (Sum.inl i))
      rw [hopen i]
      exact x.property
    let g' (j : G i) : Γ(X,U) :=
      X.presheaf.map (eqToHom (hopen i)).op (g i j)
    have hpoly : Function.Surjective
        (MvPolynomial.eval₂Hom (BaseSections.scalarMap k X U) g') :=
      BaseSections.polynomial_generators_transport k (hopen i) (g i) (hg i)
    apply (C.pow N).sectionProjectiveChartCoordinates_surjective_of_polynomial_generators
      k t (Sum.inl i) (fun j=>Sum.inr ⟨i,j⟩) g' hpoly
    intro j
    apply X.germToFunctionField_injective U
    rw [(C.pow N).ratioSection_value]
    change (C.pow N).toCartierData.sectionValue ⊤ (u ⟨i,j⟩)/
      (C.pow N).toCartierData.sectionValue ⊤ (C.sectionPow N (s i)) = _
    rw [hu,C.sectionPow_value]
    have hs : C.toCartierData.sectionValue ⊤ (s i)≠0 :=
      C.sectionValue_ne_zero_of_nonvanishing (s i)
    rw [mul_div_cancel_right₀ _ (pow_ne_zero N hs)]
    change X.germToFunctionField _ (g i j)=
      X.germToFunctionField U (X.presheaf.map (eqToHom (hopen i)).op (g i j))
    exact (germToFunctionField_restrict X (eqToHom (hopen i)) (g i j)).symm

/-- Intrinsic ampleness on a proper finite-type integral scheme yields
a genuine finite projective closed immersion. The sections are actual
sections of two positive, explicitly nested tensor powers of C. -/
theorem IsAmple.exists_finite_projective_embedding
    [IsProper (X ↘ Spec (CommRingCat.of k))] (hC : C.IsAmple) :
    ∃ a : ℕ,0<a ∧ ∃ b : ℕ,0<b ∧
      ∃ (J : Type u) (_ : Fintype J)
        (t : J→Γ(((C.pow a).pow b).sheaf,⊤)),
        ∃ hcover : (⨆ j,((C.pow a).pow b).nonvanishingOpen (t j))=⊤,
          IsClosedImmersion (((C.pow a).pow b).sectionProjectiveMap k t hcover) := by
  letI : CompactSpace X := hC.1
  obtain ⟨a,ha,ι,hι,s,hnonempty,haff,hcover⟩ :=
    hC.exists_common_power_nonempty_affine_cover
  letI : Fintype ι := hι
  obtain ⟨b,hb,J,hJ,t,chooseChart,ht,hall,hchosen,haff',hgen⟩ :=
    (C.pow a).exists_power_chart_generators k s hnonempty haff hcover
  letI : Fintype J := hJ
  exact ⟨a,ha,b,hb,J,hJ,t,hall,
    ((C.pow a).pow b).sectionProjectiveMap_isClosedImmersion_of_chartGenerators
      k t hall chooseChart hchosen haff' hgen⟩

end RationalCartierCocycle
end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.IsAmple.exists_finite_projective_embedding
end
end Source_ToricAmpleProjectiveEmbedding
-- END ORIGINAL PaperVerification.ToricAmpleProjectiveEmbedding


-- BEGIN ORIGINAL PaperVerification.ToricCartierTensor
section Source_ToricCartierTensor

-- original header: module

-- original header: public import PaperVerification.ToricCartierProducts
-- original header: public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
-- original header: public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
-- original header: public import Mathlib.Topology.Sheaves.LocallySurjective

-- original header: @[expose] public section

/-!
# The genuine tensor sheaf of two fractional Cartier sheaves

The tensor sheaf is the sheafification of the ordinary sectionwise
module tensor product. Multiplication of rational functions defines a
natural map to the fractional sheaf with multiplied local generators.
On a common trivializing open, this map is the usual rank-one tensor
isomorphism. Consequently the presheaf map is locally bijective, so its
sheafification is an actual sheaf isomorphism. No tensor-product or
section-space identification is inserted into the Cartier definitions.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open MonoidalCategory
open scoped TensorProduct

variable {X : Scheme.{u}}

/-- The ordinary sectionwise tensor presheaf over the structure sheaf. -/
def tensorPresheaf (F G : X.Modules) : PresheafOfModules X.ringCatSheaf.obj :=
  PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) F.val G.val

/-- The usual tensor product of sheaves of modules, defined by the
standard sheafification construction. -/
def tensorSheaf (F G : X.Modules) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (tensorPresheaf F G)

/-- The canonical map of the sectionwise tensor presheaf into its sheaf. -/
def tensorSheafUnit (F G : X.Modules) :
    tensorPresheaf F G ⟶ (tensorSheaf F G).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app _

/-- Actual sheaf isomorphisms induce the usual tensor-sheaf isomorphism. -/
def tensorSheafIso {F F' G G' : X.Modules} (e : F ≅ F') (f : G ≅ G') :
    tensorSheaf F G ≅ tensorSheaf F' G' := by
  letI : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    inferInstanceAs (MonoidalCategory (PresheafOfModulesOfCommRing X.presheaf))
  exact (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
    (MonoidalCategory.tensorIso ((SheafOfModules.forget _).mapIso e)
      ((SheafOfModules.forget _).mapIso f))

variable [IsIntegral X]

namespace RationalCartierCocycle

variable (C D : RationalCartierCocycle X)

/-- In genuine local frames, rational multiplication is ordinary
multiplication of the two regular coefficients. -/
theorem localCoordinates_sectionProduct (i : C.index) (j : D.index)
    (U : X.Opens) (hU : U≤C.openSet i⊓D.openSet j)
    (s : Γ(C.sheaf,U)) (t : Γ(D.sheaf,U)) :
    (C.mul D).localCoordinates (i,j) U hU (C.sectionProduct D U s t) =
      C.localCoordinates i U (hU.trans inf_le_left) s *
        D.localCoordinates j U (hU.trans inf_le_right) t := by
  classical
  by_cases hnonempty : Nonempty U
  · letI := hnonempty
    apply X.germToFunctionField_injective U
    calc
      X.germToFunctionField U
          ((C.mul D).localCoordinates (i,j) U hU (C.sectionProduct D U s t)) =
          rationalValue X U (C.sectionProduct D U s t).val /
            ((C.mul D).generator (i,j) : X.functionField) :=
        (C.mul D).localCoordinates_value (i,j) U hU (C.sectionProduct D U s t)
      _ = (rationalValue X U s.val / (C.generator i : X.functionField)) *
          (rationalValue X U t.val / (D.generator j : X.functionField)) := by
        change rationalValue X U (rationalMul U s.val t.val) /
          ((C.generator i : X.functionField)*(D.generator j : X.functionField)) = _
        rw [rationalValue_mul, div_mul_div_comm]
      _ = X.germToFunctionField U
          (C.localCoordinates i U (hU.trans inf_le_left) s) *
          X.germToFunctionField U
            (D.localCoordinates j U (hU.trans inf_le_right) t) :=
        congrArg₂ (· * ·)
          (C.localCoordinates_value i U (hU.trans inf_le_left) s).symm
          (D.localCoordinates_value j U (hU.trans inf_le_right) t).symm
      _ = X.germToFunctionField U
          (C.localCoordinates i U (hU.trans inf_le_left) s *
            D.localCoordinates j U (hU.trans inf_le_right) t) :=
        (map_mul (X.germToFunctionField U).hom _ _).symm
  · have hbot : U=⊥ := by
      apply le_antisymm
      · intro x hx
        exact False.elim (hnonempty ⟨⟨x,hx⟩⟩)
      · exact bot_le
    letI := regularSections_subsingleton_of_empty X U hbot
    exact Subsingleton.elim _ _

/-- The explicit rank-one tensor isomorphism on a common trivializing
open, obtained from the independently constructed local frames. -/
def localTensorEquiv (i : C.index) (j : D.index)
    (U : X.Opens) (hU : U≤C.openSet i⊓D.openSet j) :
    Γ(C.sheaf,U) ⊗[Γ(X,U)] Γ(D.sheaf,U) ≃ₗ[Γ(X,U)] Γ((C.mul D).sheaf,U) :=
  ((TensorProduct.congr
    (C.localCoordinates i U (hU.trans inf_le_left))
    (D.localCoordinates j U (hU.trans inf_le_right))).trans
      (TensorProduct.lid Γ(X,U) Γ(X,U))).trans
        ((C.mul D).localCoordinates (i,j) U hU).symm

theorem sectionMultiplication_eq_localTensorEquiv (i : C.index) (j : D.index)
    (U : X.Opens) (hU : U≤C.openSet i⊓D.openSet j) :
    C.sectionMultiplication D U = (C.localTensorEquiv D i j U hU).toLinearMap := by
  apply TensorProduct.ext'
  intro s t
  apply ((C.mul D).localCoordinates (i,j) U hU).injective
  simp only [sectionMultiplication_tmul, localCoordinates_sectionProduct,
    localTensorEquiv, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
    TensorProduct.congr_tmul, TensorProduct.lid_tmul,
    LinearEquiv.apply_symm_apply, smul_eq_mul]

theorem sectionMultiplication_bijective_on (i : C.index) (j : D.index)
    (U : X.Opens) (hU : U≤C.openSet i⊓D.openSet j) :
    Function.Bijective (C.sectionMultiplication D U) := by
  rw [C.sectionMultiplication_eq_localTensorEquiv D i j U hU]
  exact (C.localTensorEquiv D i j U hU).bijective

/-- Rational multiplication is a morphism of the actual sectionwise
tensor presheaf, since it commutes with actual restrictions. -/
def tensorPresheafMultiplication :
    tensorPresheaf C.sheaf D.sheaf ⟶ (C.mul D).sheaf.val :=
  PresheafOfModulesOfCommRing.homMk (R := X.presheaf)
    (M₁ := tensorPresheaf C.sheaf D.sheaf) (M₂ := (C.mul D).sheaf.val)
    (fun U => ModuleCat.ofHom
      (X := (tensorPresheaf C.sheaf D.sheaf).obj U)
      (Y := ((C.mul D).sheaf.val).obj U)
      (C.sectionMultiplication D U.unop))
    (by
      intro U V f
      apply ModuleCat.MonoidalCategory.tensor_ext
      intro s t
      change C.sectionMultiplication D V.unop
          ((tensorPresheaf C.sheaf D.sheaf).map f (s ⊗ₜ[Γ(X,U.unop)] t)) =
        (C.mul D).sheaf.presheaf.map f (C.sectionMultiplication D U.unop
          (s ⊗ₜ[Γ(X,U.unop)] t))
      have hm : (tensorPresheaf C.sheaf D.sheaf).map f
          (s ⊗ₜ[Γ(X,U.unop)] t) =
          C.sheaf.val.map f s ⊗ₜ[Γ(X,V.unop)] D.sheaf.val.map f t :=
        PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul
          (R := X.presheaf) (M₁ := C.sheaf.val) (M₂ := D.sheaf.val) f s t
      exact (congrArg (C.sectionMultiplication D V.unop) hm).trans
        (C.sectionProduct_restrict D f.unop s t).symm)

@[simp] theorem tensorPresheafMultiplication_app (U : X.Opens)
    (z : Γ(C.sheaf,U) ⊗[Γ(X,U)] Γ(D.sheaf,U)) :
    (C.tensorPresheafMultiplication D).app (op U) z =
      C.sectionMultiplication D U z := rfl

/-- Local frames prove local injectivity of the presheaf multiplication. -/
instance tensorPresheafMultiplication_locallyInjective :
    CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
        (C.tensorPresheafMultiplication D)) where
  equalizerSieve_mem {U} s t h := by
    intro x hx
    obtain ⟨i,hi⟩ := C.covers x
    obtain ⟨j,hj⟩ := D.covers x
    let V : X.Opens := U.unop ⊓ (C.openSet i ⊓ D.openSet j)
    let f : V ⟶ U.unop := homOfLE inf_le_left
    refine ⟨V,f,?_,⟨hx,hi,hj⟩⟩
    change (tensorPresheaf C.sheaf D.sheaf).presheaf.map f.op s =
      (tensorPresheaf C.sheaf D.sheaf).presheaf.map f.op t
    apply (C.sectionMultiplication_bijective_on D i j V inf_le_right).injective
    change (C.tensorPresheafMultiplication D).app (op V)
        ((tensorPresheaf C.sheaf D.sheaf).map f.op s) =
      (C.tensorPresheafMultiplication D).app (op V)
        ((tensorPresheaf C.sheaf D.sheaf).map f.op t)
    rw [PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply]
    exact congrArg ((C.mul D).sheaf.presheaf.map f.op) h

/-- Local frames prove local surjectivity of the presheaf multiplication. -/
instance tensorPresheafMultiplication_locallySurjective :
    CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
        (C.tensorPresheafMultiplication D)) where
  imageSieve_mem {U} s := by
    intro x hx
    obtain ⟨i,hi⟩ := C.covers x
    obtain ⟨j,hj⟩ := D.covers x
    let V : X.Opens := U ⊓ (C.openSet i ⊓ D.openSet j)
    let f : V ⟶ U := homOfLE inf_le_left
    obtain ⟨t,ht⟩ := (C.sectionMultiplication_bijective_on D i j V inf_le_right).surjective
      ((C.mul D).sheaf.presheaf.map f.op s)
    exact ⟨V,f,⟨t,ht⟩,⟨hx,hi,hj⟩⟩

instance tensorPresheafMultiplication_sheafification_isIso :
    IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (C.tensorPresheafMultiplication D)) := by
  have hW := (Opens.grothendieckTopology X).W_of_isLocallyBijective
    ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
      (C.tensorPresheafMultiplication D))
  change ((Opens.grothendieckTopology X).W.inverseImage
    (PresheafOfModules.toPresheaf X.ringCatSheaf.obj))
      (C.tensorPresheafMultiplication D) at hW
  rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
    (𝟙 X.ringCatSheaf.obj)] at hW
  exact hW

/-- The genuine sheaf tensor product is canonically isomorphic to the
fractional sheaf obtained by multiplying the actual local equations. -/
def tensorSheafMulIso : tensorSheaf C.sheaf D.sheaf ≅ (C.mul D).sheaf := by
  letI := C.tensorPresheafMultiplication_sheafification_isIso D
  exact asIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (C.tensorPresheafMultiplication D)) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).counit).app (C.mul D).sheaf

/-- The tensor isomorphism is the sheafification of the original
multiplication map, so its map on pure section tensors is the prescribed
actual rational multiplication. -/
theorem tensorSheafMulIso_unit :
    tensorSheafUnit C.sheaf D.sheaf ≫ (C.tensorSheafMulIso D).hom.val =
      C.tensorPresheafMultiplication D := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  have h : (adj.homEquiv (tensorPresheaf C.sheaf D.sheaf) (C.mul D).sheaf).symm
      (C.tensorPresheafMultiplication D) = (C.tensorSheafMulIso D).hom := by
    rw [Adjunction.homEquiv_counit]
    rfl
  have he := congrArg
    (adj.homEquiv (tensorPresheaf C.sheaf D.sheaf) (C.mul D).sheaf) h
  ext U s
  have he' := congrArg (fun φ => φ.app U s) he
  simp only [Equiv.apply_symm_apply,Adjunction.homEquiv_unit,
    PresheafOfModules.comp_app,ConcreteCategory.comp_apply] at he'
  dsimp only [Functor.comp_obj,Functor.comp_map,SheafOfModules.forget,
    PresheafOfModules.restrictScalars,PresheafOfModules.restrictScalarsObj,
    ModuleCat.restrictScalars,ModuleCat.RestrictScalars.obj',
    ModuleCat.RestrictScalars.map'] at he'
  exact he'.symm

@[simp] theorem tensorSheafMulIso_pure_sections (U : X.Opens)
    (s : Γ(C.sheaf,U)) (t : Γ(D.sheaf,U)) :
    (C.tensorSheafMulIso D).hom.app U
      ((tensorSheafUnit C.sheaf D.sheaf).app (op U) (s ⊗ₜ[Γ(X,U)] t)) =
        C.sectionProduct D U s t := by
  have h := congrArg (fun f => f.app (op U) (s ⊗ₜ[Γ(X,U)] t))
    (C.tensorSheafMulIso_unit D)
  simp only [PresheafOfModules.comp_app,ConcreteCategory.comp_apply,
    tensorPresheafMultiplication_app] at h
  change (C.tensorSheafMulIso D).hom.app U
    ((tensorSheafUnit C.sheaf D.sheaf).app (op U) (s ⊗ₜ[Γ(X,U)] t)) =
      C.sectionMultiplication D U (s ⊗ₜ[Γ(X,U)] t) at h
  exact h.trans (C.sectionMultiplication_tmul D U s t)

end RationalCartierCocycle

namespace CartierData

variable (D E : CartierData X)

/-- The addition of arbitrary actual fractional Cartier presentations
agrees with the ordinary tensor product of their actual sheaves. -/
def tensorSheafAddIso : tensorSheaf D.sheaf E.sheaf ≅ (D.add E).sheaf :=
  tensorSheafIso D.presentationIso E.presentationIso ≪≫
    D.localCocycle.tensorSheafMulIso E.localCocycle

end CartierData

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.tensorSheafMulIso
#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.tensorSheafMulIso_pure_sections
#print axioms PaperVerification.ToricSchemes.CartierData.tensorSheafAddIso
end
end Source_ToricCartierTensor
-- END ORIGINAL PaperVerification.ToricCartierTensor


-- BEGIN ORIGINAL PaperVerification.ToricCartierTensorPowers
section Source_ToricCartierTensorPowers

-- original header: module

-- original header: public import PaperVerification.ToricCartierTensor
-- original header: public import PaperVerification.ToricCartierAmple
-- original header: public import Mathlib.Tactic.FieldSimp
-- original header: public import Mathlib.Tactic.Ring

-- original header: @[expose] public section

/-!
# Cartier powers are actual tensor powers

The power of the rational local equations is identified with the
recursively formed genuine tensor power of the sheaf. The transition
between the common cover for a tensor product and the original cover
is justified by the regular-unit transition equations.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

variable {X : Scheme.{u}}

/-- Actual iterated tensor powers, with the structure sheaf in degree zero. -/
def tensorSheafPower (F : X.Modules) : ℕ → X.Modules
  | 0 => SheafOfModules.unit X.ringCatSheaf
  | n+1 => tensorSheaf (tensorSheafPower F n) F

def tensorSheafPowerIso {F G : X.Modules} (e : F ≅ G) :
    ∀ n, tensorSheafPower F n ≅ tensorSheafPower G n
  | 0 => Iso.refl _
  | n+1 => tensorSheafIso (tensorSheafPowerIso e n) e

variable [IsIntegral X]

namespace RationalCartierCocycle

variable (C D : RationalCartierCocycle X)

/-- Equal actual fractional-section predicates give the identity
isomorphism on their rational values. -/
def sectionEquivOfIff (h : ∀ U s, C.IsSection U s ↔ D.IsSection U s)
    (U : X.Opens) : Γ(C.sheaf,U) ≃ₗ[Γ(X,U)] Γ(D.sheaf,U) where
  toFun s := ⟨s.val,(h U s.val).mp s.property⟩
  invFun s := ⟨s.val,(h U s.val).mpr s.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def sheafIsoOfIsSectionIff (h : ∀ U s, C.IsSection U s ↔ D.IsSection U s) :
    C.sheaf ≅ D.sheaf :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    PresheafOfModules.isoMk
      (fun U => (C.sectionEquivOfIff D h U.unop).toModuleIso)
      (by intro U V f; ext s; rfl)

@[simp] theorem sheafIsoOfIsSectionIff_value
    (h : ∀ U s, C.IsSection U s ↔ D.IsSection U s)
    (U : X.Opens) (s : Γ(C.sheaf,U)) :
    ((C.sheafIsoOfIsSectionIff D h).hom.app U s).val = s.val := rfl

/-- A globally principal fractional sheaf is the actual rank-one
structure module. The frame coordinates supply the natural isomorphism. -/
def principalSheafIsoUnit (q : X.functionFieldˣ) :
    (principal (X := X) q).sheaf ≅ SheafOfModules.unit X.ringCatSheaf :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    PresheafOfModules.isoMk
      (fun U => ((principal (X := X) q).localCoordinates PUnit.unit U.unop le_top).toModuleIso)
      (by
        intro U V f
        ext s
        exact (principal (X := X) q).localCoordinates_restrict PUnit.unit
          f.unop le_top le_top s)

theorem pow_zero_isSection_iff (U : X.Opens) (s : Γ(rationalFunctions X,U)) :
    (C.pow 0).IsSection U s ↔ (principal (X := X) 1).IsSection U s := by
  constructor
  · intro hs i x hx
    obtain ⟨j,hj⟩ := C.covers x.val
    simpa only [pow, principal, Units.val_pow_eq_pow_val, pow_zero, Units.val_one] using hs j x hj
  · intro hs i x hx
    simpa only [pow, principal, Units.val_pow_eq_pow_val, pow_zero, Units.val_one] using
      hs PUnit.unit x trivial

/-- Passing to the common product cover preserves the power sheaf. -/
theorem pow_succ_isSection_iff (n : ℕ) (U : X.Opens)
    (s : Γ(rationalFunctions X,U)) :
    (C.pow (n+1)).IsSection U s ↔ ((C.pow n).mul C).IsSection U s := by
  constructor
  · intro hs ij x hx
    have hpow := hs ij.1 x hx.1
    have htransition := C.transition ij.1 ij.2 x.val hx.1 hx.2
    have h := (regularAtSubring X x.val).mul_mem hpow htransition
    change rationalValueAt X U x s /
      ((C.generator ij.1 : X.functionField)^n*(C.generator ij.2 : X.functionField)) ∈ _
    have he : (rationalValueAt X U x s /
        (C.generator ij.1 : X.functionField)^(n+1)) *
        ((C.generator ij.1 : X.functionField)/(C.generator ij.2 : X.functionField)) =
      rationalValueAt X U x s /
        ((C.generator ij.1 : X.functionField)^n*(C.generator ij.2 : X.functionField)) := by
      rw [pow_succ]
      field_simp [Units.ne_zero]
      <;> ring
    simpa only [pow, Units.val_pow_eq_pow_val, he] using h
  · intro hs i x hx
    have h := hs (i,i) x ⟨hx,hx⟩
    simpa only [pow, mul, Units.val_mul, Units.val_pow_eq_pow_val, pow_succ] using h

def powZeroSheafIso : (C.pow 0).sheaf ≅ SheafOfModules.unit X.ringCatSheaf :=
  (C.pow 0).sheafIsoOfIsSectionIff (principal (X := X) 1) C.pow_zero_isSection_iff ≪≫
    principalSheafIsoUnit (X := X) 1

def powSuccSheafIso (n : ℕ) :
    (C.pow (n+1)).sheaf ≅ ((C.pow n).mul C).sheaf :=
  (C.pow (n+1)).sheafIsoOfIsSectionIff ((C.pow n).mul C) (C.pow_succ_isSection_iff n)

/-- Every natural Cartier power is the full ordinary tensor power of
the actual sheaf, including degree zero. -/
def tensorSheafPowerIso : ∀ n, tensorSheafPower C.sheaf n ≅ (C.pow n).sheaf := by
  intro n
  induction n with
  | zero => exact C.powZeroSheafIso.symm
  | succ n ih =>
    exact tensorSheafIso ih (Iso.refl C.sheaf) ≪≫
      (C.pow n).tensorSheafMulIso C ≪≫ (C.powSuccSheafIso n).symm

end RationalCartierCocycle

namespace CartierData

variable (D : CartierData X)

/-- The n-fold Cartier sum represents the genuine n-fold tensor power,
even when the initial fractional presentation uses arbitrary local frames. -/
def tensorSheafNsmulIso (n : ℕ) :
    tensorSheafPower D.sheaf n ≅ (D.nsmul n).sheaf :=
  tensorSheafPowerIso D.presentationIso n ≪≫
    D.localCocycle.tensorSheafPowerIso n

end CartierData

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.tensorSheafPowerIso
#print axioms PaperVerification.ToricSchemes.CartierData.tensorSheafNsmulIso
end
end Source_ToricCartierTensorPowers
-- END ORIGINAL PaperVerification.ToricCartierTensorPowers


-- BEGIN ORIGINAL PaperVerification.ToricFiniteCharacterSubspaces
section Source_ToricFiniteCharacterSubspaces

-- original header: module

-- original header: public import PaperVerification.ToricCharacterSubrepresentations

-- original header: @[expose] public section

/-!
# Finite algebraic subrepresentations generated by finitely many sections

A finite collection in a coaction-stable Laurent subspace is contained
in the span of finitely many characters from that same subspace. This
does not require a prior finite-dimensionality theorem for all global
sections. It is the finite representation used in the projective
linearization construction.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open AddMonoidAlgebra
open scoped TensorProduct Classical

variable (k : Type*) [Field k] {M : Type*} [AddCommGroup M]

theorem characterModule_isCharacterStable (S : Set M) :
    IsCharacterStable k (characterModule k S) := by
  let V := characterModule k S
  let Q : Submodule k (AddMonoidAlgebra k M ⊗[k] AddMonoidAlgebra k M) :=
    LinearMap.range (TensorProduct.map
      (LinearMap.id : AddMonoidAlgebra k M →ₗ[k] _) V.subtype)
  have hle : V ≤ Q.comap (Coalgebra.comul (R := k)) := by
    rw [show V = characterModule k S from rfl, characterModule_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨m,hm,rfl⟩
    have hmem : single m (1:k) ∈ V := by
      rw [show V = characterModule k S from rfl, characterModule_eq_span]
      exact Submodule.subset_span ⟨m,hm,rfl⟩
    refine ⟨single m (1:k) ⊗ₜ[k] (⟨single m (1:k),hmem⟩ : V), ?_⟩
    simp [AddMonoidAlgebra.comul_single]
  exact fun f hf => hle hf

theorem exists_finite_character_subspace
    (V : Submodule k (AddMonoidAlgebra k M)) (hV : IsCharacterStable k V)
    (F : Finset (AddMonoidAlgebra k M)) (hF : ∀ f∈F,f∈V) :
    ∃ S : Finset M,
      (∀ f∈F,f∈characterModule k (S : Set M)) ∧
      characterModule k (S : Set M) ≤ V ∧
      IsCharacterStable k (characterModule k (S : Set M)) := by
  let S : Finset M := F.biUnion (fun f => f.coeff.support)
  refine ⟨S, ?_, ?_, characterModule_isCharacterStable k _⟩
  · intro f hf
    rw [mem_characterModule_iff]
    intro m hm
    exact Finset.mem_biUnion.mpr ⟨f,hf,hm⟩
  · rw [characterModule_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨m,hm,rfl⟩
    obtain ⟨f,hf,hmf⟩ := Finset.mem_biUnion.mp hm
    exact single_mem_of_stable k V hV f (hF f hf) m
      (Finsupp.mem_support_iff.mp hmf)

theorem finiteDimensional_characterModule (S : Finset M) :
    FiniteDimensional k (characterModule k (S : Set M)) := by
  let e : characterModule k (S : Set M) ≃ₗ[k] (S : Set M) →₀ k :=
    AddMonoidAlgebra.supportedEquivFinsupp (R := k) (S := k) (S : Set M)
  exact FiniteDimensional.of_injective e.toLinearMap e.injective

end PaperVerification.ToricCharacters

#print axioms PaperVerification.ToricCharacters.exists_finite_character_subspace
end
end Source_ToricFiniteCharacterSubspaces
-- END ORIGINAL PaperVerification.ToricFiniteCharacterSubspaces


