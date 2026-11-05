module

public import PaperVerification.ToricCartierCocycle
public import PaperVerification.ToricInvertibleAffine

@[expose] public section

/-!
# Equivalence of actual fractional sheaves and Cartier equations

An invertible fractional sheaf supplies rational local generators. Conversely,
the sheaf constructed from these generators recovers the original sheaf and
its actual embedding into rational functions. The proof uses the sheaf gluing
axiom, rather than assuming a section-space correspondence.
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace PaperVerification.ToricSchemes

variable {X : Scheme.{u}} [IsIntegral X]

namespace CartierData

variable (D : CartierData X)

set_option backward.isDefEq.respectTransparency false in
/-- Local membership in the actual image of a fractional sheaf is sufficient
for membership on the whole open set. -/
theorem exists_section_of_locally_in_range (U : X.Opens) [Nonempty U]
    (r : X.functionField)
    (hlocal : ∀ x : U, ∃ V : X.Opens, V≤U ∧ x.val∈V ∧
      ∃ s : Γ(D.sheaf,V), ∀ hV : Nonempty V,
        @sectionValue X inferInstance D V hV s = r) :
    ∃ s : Γ(D.sheaf,U), D.sectionValue U s = r := by
  classical
  have hUne : Nonempty U := inferInstance
  choose V hVU hxV s hs using hlocal
  letI (x : U) : Nonempty (V x) := ⟨⟨x.val,hxV x⟩⟩
  have hcover : U≤⨆ x : U,V x := by
    intro x hx
    exact Opens.mem_iSup.mpr ⟨⟨x,hx⟩,hxV ⟨x,hx⟩⟩
  have hcompatible : D.sheaf.presheaf.IsCompatible V s := by
    intro x y
    letI : Nonempty (V x⊓V y : X.Opens) :=
      ⟨⟨genericPoint X,genericPoint_mem_open X (V x),
        genericPoint_mem_open X (V y)⟩⟩
    apply D.sectionValue_injective (V x⊓V y)
    rw [D.sectionValue_restrict,D.sectionValue_restrict]
    exact (hs x inferInstance).trans (hs y inferInstance).symm
  let F : TopCat.Sheaf AddCommGrpCat X := ⟨D.sheaf.presheaf,D.sheaf.isSheaf⟩
  obtain ⟨g,hg,-⟩ := F.existsUnique_gluing' V U
    (fun x=>homOfLE (hVU x)) hcover s hcompatible
  refine ⟨g,?_⟩
  let x : U := Classical.choice hUne
  calc
    D.sectionValue U g =
      D.sectionValue (V x) (D.sheaf.presheaf.map (homOfLE (hVU x)).op g) :=
        (D.sectionValue_restrict _ g).symm
    _ = D.sectionValue (V x) (s x) := congrArg _ (hg x)
    _ = r := hs x inferInstance

/-- The genuine Cartier equations derived from the chosen local frames. -/
def localCocycle : RationalCartierCocycle X where
  index := X
  openSet := invertibleOpen D.locallyFree
  covers x := ⟨x,mem_invertibleOpen D.locallyFree x⟩
  generator x := by
    letI : Nonempty (invertibleOpen D.locallyFree x) :=
      ⟨⟨x,mem_invertibleOpen D.locallyFree x⟩⟩
    exact Units.mk0
      (D.frameRationalGenerator (invertibleFrame D.locallyFree x))
      (D.frameRationalGenerator_ne_zero (invertibleFrame D.locallyFree x))
  transition i j x hxi hxj := by
    let U := invertibleOpen D.locallyFree i
    let W := invertibleOpen D.locallyFree j
    let V : X.Opens := U⊓W
    letI : Nonempty U := ⟨⟨i,mem_invertibleOpen D.locallyFree i⟩⟩
    letI : Nonempty W := ⟨⟨j,mem_invertibleOpen D.locallyFree j⟩⟩
    letI : Nonempty V := ⟨⟨x,hxi,hxj⟩⟩
    change D.frameRationalGenerator (invertibleFrame D.locallyFree i) /
      D.frameRationalGenerator (invertibleFrame D.locallyFree j) ∈
        regularAtSubring X x
    obtain ⟨a,ha⟩ := D.exists_frameTransitionUnit
      (invertibleFrame D.locallyFree i) (invertibleFrame D.locallyFree j)
      (V := V) inf_le_left inf_le_right
    rw [← ha]
    exact regular_germ_mem_regularAt X V (a : Γ(X,V)) x ⟨hxi,hxj⟩

@[simp] theorem localCocycle_openSet (x : X) :
    D.localCocycle.openSet x = invertibleOpen D.locallyFree x := rfl

@[simp] theorem localCocycle_generator (x : X)
    [Nonempty (invertibleOpen D.locallyFree x)] :
    (D.localCocycle.generator x : X.functionField) =
      D.frameRationalGenerator (invertibleFrame D.locallyFree x) := rfl

/-- Actual sections satisfy the local Cartier regularity condition. -/
theorem inclusion_isSection (U : X.Opens) (s : Γ(D.sheaf,U)) :
    D.localCocycle.IsSection U (D.inclusion.app U s) := by
  intro i x hxi
  let W := invertibleOpen D.locallyFree i
  let V : X.Opens := W⊓U
  letI : Nonempty U := ⟨x⟩
  letI : Nonempty W := ⟨⟨i,mem_invertibleOpen D.locallyFree i⟩⟩
  letI : Nonempty V := ⟨⟨x.val,hxi,x.property⟩⟩
  have hr : D.sectionValue U s ∈ D.sectionValueRange V :=
    ⟨D.sheaf.presheaf.map (homOfLE inf_le_right).op s,D.sectionValue_restrict _ s⟩
  obtain ⟨a,ha⟩ :=
    (D.mem_sectionValueRange_iff (invertibleFrame D.locallyFree i)
      (V := V) inf_le_left _).mp hr
  have ha' : X.germToFunctionField V a =
      D.sectionValue U s / D.frameRationalGenerator (invertibleFrame D.locallyFree i) :=
    (eq_div_iff (D.frameRationalGenerator_ne_zero _)).mpr ha
  simp only [rationalValueAt_eq,localCocycle_generator]
  change D.sectionValue U s / D.frameRationalGenerator (invertibleFrame D.locallyFree i) ∈
    regularAtSubring X x.val
  rw [← ha']
  exact regular_germ_mem_regularAt X V a x.val ⟨hxi,x.property⟩

/-- Every section obtained from the derived Cartier equations is an actual
section of the original fractional sheaf. -/
theorem exists_section_of_localCocycle (U : X.Opens) [Nonempty U]
    (s : Γ(rationalFunctions X,U)) (hs : D.localCocycle.IsSection U s) :
    ∃ t : Γ(D.sheaf,U), D.inclusion.app U t = s := by
  have hloc : ∀ x : U, ∃ V : X.Opens, V≤U ∧ x.val∈V ∧
      ∃ t : Γ(D.sheaf,V), ∀ hV : Nonempty V,
        @sectionValue X inferInstance D V hV t = rationalValue X U s := by
    intro x
    let W := invertibleOpen D.locallyFree x.val
    let V : X.Opens := W⊓U
    letI : Nonempty W := ⟨⟨x.val,mem_invertibleOpen D.locallyFree x.val⟩⟩
    have hxV : x.val∈V := ⟨mem_invertibleOpen D.locallyFree x.val,x.property⟩
    letI : Nonempty V := ⟨⟨x.val,hxV⟩⟩
    let q := D.frameRationalGenerator (invertibleFrame D.locallyFree x.val)
    have hregular : ∀ y∈V,
        rationalValue X U s/q ∈ regularAtSubring X y := by
      intro y hy
      simpa only [rationalValueAt_eq,localCocycle_generator] using
        hs x.val ⟨y,hy.2⟩ hy.1
    obtain ⟨a,ha⟩ := exists_regularSection_of_stalkwise X V
      (rationalValue X U s/q) hregular
    let t := a • D.frameGenerator (invertibleFrame D.locallyFree x.val) V inf_le_left
    refine ⟨V,inf_le_right,hxV,t,?_⟩
    intro hV
    change D.sectionValue V
      (a • D.frameGenerator (invertibleFrame D.locallyFree x.val) V inf_le_left) =
        rationalValue X U s
    rw [D.sectionValue_smul,D.sectionValue_frameGenerator,ha]
    exact div_mul_cancel₀ _ (D.frameRationalGenerator_ne_zero _)
  obtain ⟨t,ht⟩ := D.exists_section_of_locally_in_range U (rationalValue X U s) hloc
  refine ⟨t,(rationalValue X U).injective ?_⟩
  simpa only [sectionValue_apply] using ht

/-- Exact actual-image characterization on every nonempty open. -/
theorem localCocycle_isSection_iff (U : X.Opens) [Nonempty U]
    (s : Γ(rationalFunctions X,U)) :
    D.localCocycle.IsSection U s ↔
      ∃ t : Γ(D.sheaf,U),D.inclusion.app U t=s :=
  ⟨D.exists_section_of_localCocycle U s,
    by rintro ⟨t,rfl⟩; exact D.inclusion_isSection U t⟩

/-- The canonical map into the sheaf reconstructed from local generators. -/
def presentationMap (U : X.Opens) :
    Γ(D.sheaf,U) →ₗ[Γ(X,U)] Γ(D.localCocycle.sheaf,U) where
  toFun s := ⟨D.inclusion.app U s,D.inclusion_isSection U s⟩
  map_add' s t := Subtype.ext (map_add _ _ _)
  map_smul' a s := Subtype.ext (D.inclusion.app_smul a s)

theorem presentationMap_bijective (U : X.Opens) :
    Function.Bijective (D.presentationMap U) := by
  classical
  refine ⟨fun s t h=>D.inclusion_injective U (congrArg Subtype.val h),?_⟩
  intro s
  by_cases hU : Nonempty U
  · letI := hU
    obtain ⟨t,ht⟩ := D.exists_section_of_localCocycle U s.val s.property
    exact ⟨t,Subtype.ext ht⟩
  · have hbot : U=⊥ := by
      apply le_antisymm
      · intro x hx
        exact False.elim (hU ⟨⟨x,hx⟩⟩)
      · exact bot_le
    letI := regularSections_subsingleton_of_empty X U hbot
    letI := Module.subsingleton Γ(X,U) Γ(D.localCocycle.sheaf,U)
    exact ⟨0,Subsingleton.elim _ _⟩

def presentationLinearEquiv (U : X.Opens) :
    Γ(D.sheaf,U) ≃ₗ[Γ(X,U)] Γ(D.localCocycle.sheaf,U) :=
  LinearEquiv.ofBijective (D.presentationMap U) (D.presentationMap_bijective U)

/-- Recovery is an actual natural sheaf isomorphism. -/
def presentationIso : D.sheaf ≅ D.localCocycle.sheaf :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    PresheafOfModules.isoMk
      (fun U=>(D.presentationLinearEquiv U.unop).toModuleIso)
      (by
        intro U V f
        ext s
        apply Subtype.ext
        exact PresheafOfModules.naturality_apply D.inclusion.val f s)

/-- The recovered isomorphism respects the actual rational embedding. -/
theorem equivalent_localCocycle : D.Equivalent D.localCocycle.toCartierData := by
  refine ⟨D.presentationIso,?_⟩
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  rfl

end CartierData

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.CartierData.localCocycle_isSection_iff
#print axioms PaperVerification.ToricSchemes.CartierData.presentationIso
#print axioms PaperVerification.ToricSchemes.CartierData.equivalent_localCocycle
