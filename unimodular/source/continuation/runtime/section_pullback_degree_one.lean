module

public import Continuation.Runtime.SectionPowerEmbedding
public import Continuation.Runtime.PolynomialDegreeOneSheaf

/-!
# Pulling back the ordinary polynomial O(1) along the section morphism

The polynomial degree-one sheaf is independently constructed from local
homogeneous fractions. Its pulled-back coordinate frames are compared with
the actual input sections on their nonvanishing opens. Equality of the
transition ratios glues the comparison to an isomorphism of actual sheaves.

The conclusion identifies the actual pullback of the independently
constructed polynomial degree-one sheaf.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace TopCat
open scoped Classical

namespace BondalThomsen

/-- The map on sections respects equality of scheme morphisms, with the
open-containment witnesses transported by proof irrelevance. -/
theorem schemeAppLE_congr_morphism {X Y : Scheme} (f g : X ⟶ Y)
    (h : f = g) (U : Y.Opens) (V : X.Opens)
    (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) :
    f.appLE U V hf = g.appLE U V hg := by
  subst g
  rfl

/-- An actual section is a frame over its ordinary nonvanishing open. -/
theorem moduleGlobalSectionHom_over_isIso_of_nonvanishing
    {X : Scheme} (M : X.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X M]
    (s : Γ(M, ⊤)) (U : X.Opens) (hU : U ≤ M.nonvanishingLocus s) :
    IsIso ((moduleGlobalSectionHom M s).over U) := by
  apply (isIso_iff_of_reflects_iso _ (SheafOfModules.forget _)).mp
  apply (isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)).mp
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro V
  rw [ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective (fun r : Γ(X, V.unop.left) =>
    r • (M.presheaf.map (homOfLE (show V.unop.left ≤ ⊤ from le_top)).op s :
      Γ(M, V.unop.left)))
  have h := (Scheme.Modules.le_nonvanishingLocus_iff s
    (homOfLE (show U ≤ ⊤ from le_top))).mp hU
      V.unop.left V.unop.hom
  have hcomp : V.unop.hom ≫ (homOfLE (show U ≤ ⊤ from le_top)) =
      homOfLE (show V.unop.left ≤ ⊤ from le_top) := Subsingleton.elim _ _
  rw [hcomp] at h
  exact h

section Comparison

variable {X : Scheme} {P Q : X.Modules} {ι : Type}
  (U : ι → X.Opens) (cover : IsOpenCover U)
  (p : ι → (SheafOfModules.unit X.ringCatSheaf ⟶ P))
  (q : ι → (SheafOfModules.unit X.ringCatSheaf ⟶ Q))
  (hp : ∀ i, IsIso ((p i).over (U i)))
  (hq : ∀ i, IsIso ((q i).over (U i)))
  (ratios : ∀ i j, ∃ c : Γ(X, U i),
    Scheme.Modules.Hom.app (p j) (U i) (1 : Γ(X, U i)) =
      c • Scheme.Modules.Hom.app (p i) (U i) (1 : Γ(X, U i)) ∧
    Scheme.Modules.Hom.app (q j) (U i) (1 : Γ(X, U i)) =
      c • Scheme.Modules.Hom.app (q i) (U i) (1 : Γ(X, U i)))

def sectionComparisonChartIso (i : ι) : P.over (U i) ≅ Q.over (U i) := by
  letI := hp i
  letI := hq i
  exact (asIso ((p i).over (U i))).symm ≪≫ asIso ((q i).over (U i))

theorem sectionComparisonChartIso_diagonal (i : ι) :
    (p i).over (U i) ≫ (sectionComparisonChartIso U p q hp hq i).hom =
      (q i).over (U i) := by
  letI := hp i
  letI := hq i
  simp only [sectionComparisonChartIso, Iso.trans_hom, Iso.symm_hom,
    asIso_hom, asIso_inv, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]

include ratios in
theorem sectionComparisonChartIso_all (i j : ι) :
    (p j).over (U i) ≫ (sectionComparisonChartIso U p q hp hq i).hom =
      (q j).over (U i) := by
  obtain ⟨c, hcP, hcQ⟩ := ratios i j
  apply SheafOfModules.hom_ext
  ext V : 2
  apply (LinearMap.ringLmapEquivSelf _ ℤ _).injective
  let W := V.unop.left
  let hW := V.unop.hom.le
  let cW := X.presheaf.map (homOfLE hW).op c
  have hP := moduleSectionHom_coefficient_restrict (p i) (p j)
    (U i) W hW c hcP
  have hQ := moduleSectionHom_coefficient_restrict (q i) (q j)
    (U i) W hW c hcQ
  have hdiag := congrArg (fun g => g.val.app V (1 : Γ(X, W)))
    (sectionComparisonChartIso_diagonal U p q hp hq i)
  change (sectionComparisonChartIso U p q hp hq i).hom.val.app V
      (Scheme.Modules.Hom.app (p j) W (1 : Γ(X, W))) =
    Scheme.Modules.Hom.app (q j) W (1 : Γ(X, W))
  rw [hP, hQ,
    ((sectionComparisonChartIso U p q hp hq i).hom.val.app V).hom.map_smul]
  exact congrArg (fun s => cW • s) hdiag

include ratios in
theorem sectionComparisonChartIso_overlap (i j : ι) :
    restrictLocalModuleHom (inf_le_left : U i ⊓ U j ≤ U i)
        (sectionComparisonChartIso U p q hp hq i).hom =
      restrictLocalModuleHom inf_le_right
        (sectionComparisonChartIso U p q hp hq j).hom := by
  let W := U i ⊓ U j
  letI := hp i
  have hframe : IsIso ((p i).over W) := by
    rw [← restrictLocalModuleHom_global (inf_le_left : W ≤ U i) (p i)]
    exact restrictLocalModuleHom_isIso _ _
  letI := hframe
  apply (cancel_epi ((p i).over W)).mp
  have hi := congrArg (restrictLocalModuleHom (inf_le_left : W ≤ U i))
    (sectionComparisonChartIso_all U p q hp hq ratios i i)
  have hj := congrArg (restrictLocalModuleHom (inf_le_right : W ≤ U j))
    (sectionComparisonChartIso_all U p q hp hq ratios j i)
  simp only [restrictLocalModuleHom_map_comp, restrictLocalModuleHom_global] at hi hj
  exact hi.trans hj.symm

include ratios in
theorem sectionComparisonChartIso_inverse_overlap (i j : ι) :
    restrictLocalModuleHom (inf_le_left : U i ⊓ U j ≤ U i)
        (sectionComparisonChartIso U p q hp hq i).inv =
      restrictLocalModuleHom inf_le_right
        (sectionComparisonChartIso U p q hp hq j).inv := by
  letI := restrictLocalModuleHom_isIso (inf_le_left : U i ⊓ U j ≤ U i)
    (sectionComparisonChartIso U p q hp hq i).hom
  letI := restrictLocalModuleHom_isIso (inf_le_right : U i ⊓ U j ≤ U j)
    (sectionComparisonChartIso U p q hp hq j).hom
  rw [restrictLocalModuleHom_inverse, restrictLocalModuleHom_inverse]
  exact IsIso.inv_eq_inv.mpr (sectionComparisonChartIso_overlap U p q hp hq ratios i j)

/-- The two sheaves are compared by the same actual global sections and
their checked common transition ratios. -/
def sectionFamilyComparisonIso : P ≅ Q where
  hom := LocalModuleGluing.glue U cover
    (fun i => (sectionComparisonChartIso U p q hp hq i).hom)
    (sectionComparisonChartIso_overlap U p q hp hq ratios)
  inv := LocalModuleGluing.glue U cover
    (fun i => (sectionComparisonChartIso U p q hp hq i).inv)
    (sectionComparisonChartIso_inverse_overlap U p q hp hq ratios)
  hom_inv_id := by
    apply LocalModuleGluing.hom_ext U cover
    intro i
    change (LocalModuleGluing.glue U cover _ _).over (U i) ≫
      (LocalModuleGluing.glue U cover _ _).over (U i) = 𝟙 _
    rw [LocalModuleGluing.glue_over, LocalModuleGluing.glue_over, Iso.hom_inv_id]
  inv_hom_id := by
    apply LocalModuleGluing.hom_ext U cover
    intro i
    change (LocalModuleGluing.glue U cover _ _).over (U i) ≫
      (LocalModuleGluing.glue U cover _ _).over (U i) = 𝟙 _
    rw [LocalModuleGluing.glue_over, LocalModuleGluing.glue_over, Iso.inv_hom_id]

/-- The global comparison preserves every original coordinate section. -/
theorem sectionFamilyComparisonIso_coordinate (i : ι) :
    p i ≫ (sectionFamilyComparisonIso U cover p q hp hq ratios).hom = q i := by
  apply LocalModuleGluing.hom_ext U cover
  intro j
  change (p i).over (U j) ≫
    (LocalModuleGluing.glue U cover _ _).over (U j) = (q i).over (U j)
  rw [LocalModuleGluing.glue_over]
  exact sectionComparisonChartIso_all U p q hp hq ratios j i

end Comparison
end BondalThomsen

namespace PaperVerification.ToricSchemes.RationalCartierCocycle

open BondalThomsen
attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type) [Field k] {X : Scheme} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of k))] (C : RationalCartierCocycle X)
  {ι : Type} (s : ι → Γ(C.sheaf, ⊤))
  (hcover : (⨆ i, C.nonvanishingOpen (s i)) = ⊤)

theorem sourceSection_over_nonvanishing_isIso (i : ι) :
    IsIso ((moduleGlobalSectionHom C.sheaf (s i)).over
      (C.nonvanishingOpen (s i))) := by
  apply moduleGlobalSectionHom_over_isIso_of_nonvanishing
  rw [Unimodular.NefBig.cocycle_nonvanishingOpen_eq]

theorem pulledBackCoordinate_over_nonvanishing_isIso (i : ι) :
    IsIso ((polynomialProjDegreeOnePullbackCoordinateHom k ι
      (C.sectionProjectiveMap k s hcover) i).over (C.nonvanishingOpen (s i))) := by
  let U := C.nonvanishingOpen (s i)
  let f := C.sectionProjectiveMap k s hcover
  let c := polynomialProjDegreeOneCoordinateHom k ι i
  have hc : IsIso (modulePullbackSectionHom (U.ι ≫ f) c) := by
    rw [C.sectionProjectiveMap_chart k s hcover i,
      C.sectionProjectiveChart_eq_affine k s i]
    exact modulePullbackSectionHom_comp_isIso _ _ c
      (polynomialProjDegreeOneCoordinateHom_pullbackChart_isIso k ι i)
  have he := modulePullbackSectionHom_comp U.ι f c
  rw [← he] at hc
  have hr : IsIso (modulePullbackSectionHom U.ι (modulePullbackSectionHom f c)) :=
    (isIso_comp_right_iff _ ((Scheme.Modules.pullbackComp U.ι f).hom.app
      (polynomialProjDegreeOneSheaf k ι))).mp hc
  have h := modulePullbackSectionHom_over_isIso U.ι (modulePullbackSectionHom f c) hr
  erw [Scheme.Opens.opensRange_ι] at h
  exact h

/-- The affine chart-ring evaluation is the actual morphism's map on
regular functions on D(X_i), including nonaffine source opens. -/
theorem sectionProjectiveMap_chart_actualApp (i : ι) :
    Proj.awayToSection (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X i) ≫
      (C.sectionProjectiveMap k s hcover).appLE
        (polynomialDegreeOneCoordinateOpen k ι i) (C.nonvanishingOpen (s i))
        (by rw [C.sectionProjectiveMap_preimage k s hcover i]) =
      CommRingCat.ofHom (C.sectionProjectiveChartCoordinates k s i) := by
  let U := C.nonvanishingOpen (s i)
  let f := C.sectionProjectiveMap k s hcover
  let V := polynomialDegreeOneCoordinateOpen k ι i
  let A := HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule ι k)
    (MvPolynomial.X i)
  let a := CommRingCat.ofHom (C.sectionProjectiveChartCoordinates k s i)
  let z := Proj.awayι (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X i)
    (polynomialVariable_mem_degreeOne k i) (by decide)
  have hz : ⊤ ≤ z ⁻¹ᵁ V := by
    intro x _
    change z x ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X i)
    rw [← Proj.opensRange_awayι _ _ (polynomialVariable_mem_degreeOne k i) (by decide)]
    exact ⟨x, rfl⟩
  apply (cancel_mono U.topIso.inv).mp
  rw [Category.assoc]
  have hopen : U.ι.appLE U ⊤ (by simp) = U.topIso.inv := by
    simp only [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    congr 1
  conv_lhs => rw [← hopen]
  change _ ≫ f.appLE V U _ ≫ U.ι.appLE U ⊤ (by simp) = a ≫ U.topIso.inv
  rw [Scheme.Hom.appLE_comp_appLE U.ι f V U ⊤]
  have hchart : U.ι ≫ f = (U.toSpecΓ ≫ Spec.map a) ≫ z :=
    (C.sectionProjectiveMap_chart k s hcover i).trans
      (C.sectionProjectiveChart_eq_affine k s i)
  have hchartOpen : ⊤ ≤ ((U.toSpecΓ ≫ Spec.map a) ≫ z) ⁻¹ᵁ V := by
    intro x _
    change z ((U.toSpecΓ ≫ Spec.map a) x) ∈ V
    exact hz trivial
  rw [schemeAppLE_congr_morphism (U.ι ≫ f)
    ((U.toSpecΓ ≫ Spec.map a) ≫ z) hchart V ⊤ _ hchartOpen]
  rw [← Scheme.Hom.appLE_comp_appLE (U.toSpecΓ ≫ Spec.map a) z V ⊤ ⊤ hz (by simp)]
  have htop : (U.toSpecΓ ≫ Spec.map a).appLE ⊤ ⊤ (by simp) =
      (U.toSpecΓ ≫ Spec.map a).appTop := (U.toSpecΓ ≫ Spec.map a).appLE_eq_app
  rw [htop, ← Category.assoc, polynomialProjAwayToSection_comp_chartApp,
    Scheme.Hom.comp_appTop, Scheme.Opens.toSpecΓ_appTop]
  rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

theorem sectionProjectiveMap_ratio_actualApp (i j : ι) :
    (C.sectionProjectiveMap k s hcover).appLE
        (polynomialDegreeOneCoordinateOpen k ι i) (C.nonvanishingOpen (s i))
        (by rw [C.sectionProjectiveMap_preimage k s hcover i])
        (polynomialDegreeOneChartRatio k ι i j le_rfl) =
      C.ratioSection (s j) (s i) := by
  rw [polynomialDegreeOneChartRatio_eq_awayToSection]
  calc
    _ = C.sectionProjectiveChartCoordinates k s i
        (HomogeneousLocalization.Away.isLocalizationElem
          (polynomialVariable_mem_degreeOne k i)
          (polynomialVariable_mem_degreeOne k j)) :=
      by
        simpa only [ConcreteCategory.comp_apply, ConcreteCategory.hom_ofHom,
          CommRingCat.hom_ofHom, HomogeneousLocalization.Away.isLocalizationElem,
          pow_one] using
          (ConcreteCategory.congr_hom
            (C.sectionProjectiveMap_chart_actualApp k s hcover i)
            (HomogeneousLocalization.Away.isLocalizationElem
              (polynomialVariable_mem_degreeOne k i)
              (polynomialVariable_mem_degreeOne k j)))
    _ = _ := C.sectionProjectiveChartCoordinates_variable k s i j


theorem sourceSection_ratio (i j : ι) :
    Scheme.Modules.Hom.app (moduleGlobalSectionHom C.sheaf (s j))
        (C.nonvanishingOpen (s i)) (1 : Γ(X, C.nonvanishingOpen (s i))) =
      C.ratioSection (s j) (s i) •
        Scheme.Modules.Hom.app (moduleGlobalSectionHom C.sheaf (s i))
          (C.nonvanishingOpen (s i)) (1 : Γ(X, C.nonvanishingOpen (s i))) := by
  simp only [moduleGlobalSectionHom_app, one_smul]
  let U := C.nonvanishingOpen (s i)
  by_cases hU : Nonempty U
  · letI := hU
    apply C.toCartierData.sectionValue_injective U
    rw [C.toCartierData.sectionValue_smul, C.ratioSection_value]
    calc
      _ = C.toCartierData.sectionValue ⊤ (s j) :=
        C.toCartierData.sectionValue_restrict (homOfLE (show U ≤ ⊤ from le_top)) (s j)
      _ = (C.toCartierData.sectionValue ⊤ (s j) /
          C.toCartierData.sectionValue ⊤ (s i)) *
          C.toCartierData.sectionValue ⊤ (s i) :=
        (div_mul_cancel₀ _ (C.sectionValue_ne_zero_of_nonvanishing (s i))).symm
      _ = _ := congrArg (fun v =>
          (C.toCartierData.sectionValue ⊤ (s j) /
            C.toCartierData.sectionValue ⊤ (s i)) * v)
        (C.toCartierData.sectionValue_restrict
          (homOfLE (show U ≤ ⊤ from le_top)) (s i)).symm
  · have hbot : U = ⊥ := by
      apply le_antisymm ?_ bot_le
      intro x hx
      exact (hU ⟨⟨x, hx⟩⟩).elim
    letI := regularSections_subsingleton_of_empty X U hbot
    letI := Module.subsingleton Γ(X, U) Γ(C.sheaf, U)
    exact Subsingleton.elim _ _

/-- The actual polynomial O(1) pulls back to the original Cartier sheaf.
No map-to-projective-space or line-bundle correspondence is assumed. -/
def sectionProjectiveMap_pullback_degreeOneIso :
    (Scheme.Modules.pullback (C.sectionProjectiveMap k s hcover)).obj
      (polynomialProjDegreeOneSheaf k ι) ≅ C.sheaf := by
  let U := fun i => C.nonvanishingOpen (s i)
  let f := C.sectionProjectiveMap k s hcover
  let p := polynomialProjDegreeOnePullbackCoordinateHom k ι f
  let q := fun i => moduleGlobalSectionHom C.sheaf (s i)
  apply sectionFamilyComparisonIso U (IsOpenCover.mk hcover) p q
    (C.pulledBackCoordinate_over_nonvanishing_isIso k s hcover)
    (C.sourceSection_over_nonvanishing_isIso s)
  intro i j
  refine ⟨C.ratioSection (s j) (s i), ?_, C.sourceSection_ratio s i j⟩
  have h := modulePullbackSectionHom_coefficient f
    (polynomialProjDegreeOneCoordinateHom k ι i)
    (polynomialProjDegreeOneCoordinateHom k ι j)
    (polynomialDegreeOneCoordinateOpen k ι i) (U i)
    (by rw [C.sectionProjectiveMap_preimage k s hcover i])
    (polynomialDegreeOneChartRatio k ι i j le_rfl)
    (polynomialProjDegreeOneCoordinateHom_coefficient k ι i j)
  rw [C.sectionProjectiveMap_ratio_actualApp k s hcover i j] at h
  exact h

/-- The comparison identifies the pullback of each homogeneous coordinate
with the specified actual source section, not merely an isomorphic line bundle. -/
theorem sectionProjectiveMap_pullback_degreeOneIso_coordinate (i : ι) :
    polynomialProjDegreeOnePullbackCoordinateHom k ι
        (C.sectionProjectiveMap k s hcover) i ≫
      (C.sectionProjectiveMap_pullback_degreeOneIso k s hcover).hom =
      moduleGlobalSectionHom C.sheaf (s i) := by
  unfold sectionProjectiveMap_pullback_degreeOneIso
  exact sectionFamilyComparisonIso_coordinate _ _ _ _ _ _ _ i

end PaperVerification.ToricSchemes.RationalCartierCocycle

#print axioms BondalThomsen.sectionFamilyComparisonIso
#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.sectionProjectiveMap_chart_actualApp
#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.sectionProjectiveMap_pullback_degreeOneIso

end
