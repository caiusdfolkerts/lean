module

public import PaperVerification.ToricInvertibleAffine
public import PaperVerification.ToricModuleFrameGluing

@[expose] public section

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
