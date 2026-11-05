module

public import PaperVerification.ToricTorusCartierRepresentative
public import PaperVerification.ToricCartierDescent

@[expose] public section

/-!
# Fractional values on genuine open charts

A global frame on an open chart gives a principal fractional module on
every smaller ambient open. This statement is derived from restriction of
the actual sheaf. It also proves the regularity of the ratio of two chart
generators on the actual scheme overlap.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace PaperVerification.ToricSchemes.CartierData

variable {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (D : CartierData X) (j : Y ⟶ X) [IsOpenImmersion j]

theorem alongSectionValue_range (V : Y.Opens) [Nonempty V] :
    Set.range (D.alongSectionValue j V) =
      Set.range (@sectionValue X inferInstance D (j ''ᵁ V)
        (openImmersion_image_nonempty j V)) := by
  letI : Nonempty (j ''ᵁ V) := openImmersion_image_nonempty j V
  ext r
  constructor
  · rintro ⟨s,rfl⟩
    exact ⟨(D.sheaf.restrictAppIso j V).hom s,rfl⟩
  · rintro ⟨s,rfl⟩
    refine ⟨(D.sheaf.restrictAppIso j V).inv s,?_⟩
    change D.sectionValue (j ''ᵁ V)
      ((D.sheaf.restrictAppIso j V).hom ((D.sheaf.restrictAppIso j V).inv s)) = _
    simp

/-- The exact fractional-principal description on the image of a chart
open, with the ordinary ambient regular-function embedding. -/
theorem mem_sectionValueRange_image_iff
    (e : D.sheaf.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf)
    (V : Y.Opens) [Nonempty V] [Nonempty (j ''ᵁ V)] (r : X.functionField) :
    r ∈ D.sectionValueRange (j ''ᵁ V) ↔
      ∃ a : Γ(X,j ''ᵁ V), X.germToFunctionField (j ''ᵁ V) a *
        D.chartFrameRationalGenerator j e = r := by
  change r ∈ Set.range (D.sectionValue (j ''ᵁ V)) ↔ _
  rw [← D.alongSectionValue_range j V]
  constructor
  · rintro ⟨s,rfl⟩
    let a : Γ(Y,V) := e.hom.app V s
    refine ⟨(j.appIso V).inv a,?_⟩
    calc
      _ = openImmersionRegularToFunctionField j V a * D.chartFrameRationalGenerator j e :=
        congrArg (fun z : X.functionField => z * D.chartFrameRationalGenerator j e)
          (openImmersionRegularToFunctionField_eq_germ_image j V a).symm
      _ = _ := (D.alongSectionValue_frame j e V s).symm
  · rintro ⟨a,ha⟩
    let t : Γ(D.sheaf.restrict j,V) := e.inv.app V ((j.appIso V).hom a)
    refine ⟨t,?_⟩
    have he : (show Γ(Y,V) from e.hom.app V t) = (j.appIso V).hom a :=
      (D.chartFrameCoordinates j e V).apply_symm_apply ((j.appIso V).hom a)
    calc
      _ = openImmersionRegularToFunctionField j V (e.hom.app V t) *
          D.chartFrameRationalGenerator j e := D.alongSectionValue_frame j e V t
      _ = openImmersionRegularToFunctionField j V ((j.appIso V).hom a) *
          D.chartFrameRationalGenerator j e :=
        congrArg (fun r : Γ(Y,V) => openImmersionRegularToFunctionField j V r *
          D.chartFrameRationalGenerator j e) he
      _ = X.germToFunctionField (j ''ᵁ V) ((j.appIso V).inv ((j.appIso V).hom a)) *
          D.chartFrameRationalGenerator j e :=
        congrArg (fun z : X.functionField => z * D.chartFrameRationalGenerator j e)
          (openImmersionRegularToFunctionField_eq_germ_image j V ((j.appIso V).hom a))
      _ = X.germToFunctionField (j ''ᵁ V) a * D.chartFrameRationalGenerator j e :=
        congrArg (fun r : Γ(X,j ''ᵁ V) => X.germToFunctionField (j ''ᵁ V) r *
          D.chartFrameRationalGenerator j e) (CommRingCat.inv_hom_apply (j.appIso V) a)
      _ = r := ha

/-- The chart-frame formula holds on every smaller ambient open, not only
on opens presented as images in the statement. -/
theorem mem_sectionValueRange_iff_chartFrame
    (e : D.sheaf.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf)
    (W : X.Opens) [Nonempty W] (hW : W≤j.opensRange) (r : X.functionField) :
    r ∈ D.sectionValueRange W ↔
      ∃ a : Γ(X,W), X.germToFunctionField W a *
        D.chartFrameRationalGenerator j e = r := by
  let V := j ⁻¹ᵁ W
  letI : Nonempty V := openImmersion_preimage_nonempty j W
  letI : Nonempty (j ''ᵁ V) := openImmersion_image_nonempty j V
  have himage : j ''ᵁ V=W := by
    rw [show V=j ⁻¹ᵁ W from rfl,j.image_preimage_eq_opensRange_inf,inf_eq_right.mpr hW]
  let P (U : X.Opens) : Prop := ∀ (hU : Nonempty U),
    letI : Nonempty U := hU
    r ∈ D.sectionValueRange U ↔
      ∃ a : Γ(X,U), X.germToFunctionField U a *
        D.chartFrameRationalGenerator j e = r
  have hP : P (j ''ᵁ V) := by
    intro hU
    letI := hU
    exact D.mem_sectionValueRange_image_iff j e V r
  have hQ : P W := Eq.mp (congrArg P himage) hP
  exact hQ inferInstance

theorem chartFrameRationalGenerator_mem_sectionValueRange
    (e : D.sheaf.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf)
    (W : X.Opens) [Nonempty W] (hW : W≤j.opensRange) :
    D.chartFrameRationalGenerator j e ∈ D.sectionValueRange W := by
  apply (D.mem_sectionValueRange_iff_chartFrame j e W hW _).mpr
  exact ⟨1,by simp⟩

/-- A chart generator divided by another is an actual regular unit on
every nonempty open in their overlap. -/
theorem exists_chartFrameTransitionUnit (g : Z ⟶ X) [IsOpenImmersion g]
    (e : D.sheaf.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf)
    (f : D.sheaf.restrict g ≅ SheafOfModules.unit Z.ringCatSheaf)
    (W : X.Opens) [Nonempty W] (hWj : W≤j.opensRange) (hWg : W≤g.opensRange) :
    ∃ a : Γ(X,W)ˣ, X.germToFunctionField W (a : Γ(X,W)) =
      D.chartFrameRationalGenerator j e / D.chartFrameRationalGenerator g f := by
  obtain ⟨a,ha⟩ := (D.mem_sectionValueRange_iff_chartFrame g f W hWg _).mp
    (D.chartFrameRationalGenerator_mem_sectionValueRange j e W hWj)
  obtain ⟨b,hb⟩ := (D.mem_sectionValueRange_iff_chartFrame j e W hWj _).mp
    (D.chartFrameRationalGenerator_mem_sectionValueRange g f W hWg)
  have hab : a*b=1 := by
    apply X.germToFunctionField_injective W
    rw [map_mul,map_one]
    apply mul_right_cancel₀ (D.chartFrameRationalGenerator_ne_zero j e)
    rw [mul_assoc,hb,ha,one_mul]
  exact ⟨⟨a,b,hab,by simpa only [mul_comm] using hab⟩,
    (eq_div_iff (D.chartFrameRationalGenerator_ne_zero g f)).mpr ha⟩

theorem chartFrameRatio_regularAt (g : Z ⟶ X) [IsOpenImmersion g]
    (e : D.sheaf.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf)
    (f : D.sheaf.restrict g ≅ SheafOfModules.unit Z.ringCatSheaf)
    (x : X) (hxj : x∈j.opensRange) (hxg : x∈g.opensRange) :
    D.chartFrameRationalGenerator j e / D.chartFrameRationalGenerator g f ∈
      regularAtSubring X x := by
  let W := j.opensRange⊓g.opensRange
  letI : Nonempty W := ⟨⟨x,hxj,hxg⟩⟩
  obtain ⟨a,ha⟩ := D.exists_chartFrameTransitionUnit j g e f W inf_le_left inf_le_right
  rw [← ha]
  exact regular_germ_mem_regularAt X W a x ⟨hxj,hxg⟩

/-- A chosen generator of a chart frame is a unit on an open where the
actual fractional module equals the regular-function module. -/
theorem chartFrameGenerator_isUnit_of_range
    (e : D.sheaf.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf)
    (W : X.Opens) [Nonempty W] (hW : W≤j.opensRange)
    (hregular : (D.sectionValueRange W : Set X.functionField)=
      Set.range (X.germToFunctionField W)) :
    ∃ a : Γ(X,W)ˣ, X.germToFunctionField W (a : Γ(X,W)) =
      D.chartFrameRationalGenerator j e := by
  have hq := D.chartFrameRationalGenerator_mem_sectionValueRange j e W hW
  change D.chartFrameRationalGenerator j e ∈ (D.sectionValueRange W : Set X.functionField) at hq
  rw [hregular] at hq
  obtain ⟨a,ha⟩ := hq
  have h1 : (1 : X.functionField)∈D.sectionValueRange W := by
    change (1 : X.functionField)∈(D.sectionValueRange W : Set X.functionField)
    rw [hregular]
    exact ⟨1,map_one _⟩
  obtain ⟨b,hb⟩ := (D.mem_sectionValueRange_iff_chartFrame j e W hW 1).mp h1
  have hab : a*b=1 := by
    apply X.germToFunctionField_injective W
    rw [map_mul,map_one,ha,mul_comm]
    exact hb
  exact ⟨⟨a,b,hab,by simpa only [mul_comm] using hab⟩,ha⟩

end PaperVerification.ToricSchemes.CartierData

#print axioms PaperVerification.ToricSchemes.CartierData.mem_sectionValueRange_iff_chartFrame
#print axioms PaperVerification.ToricSchemes.CartierData.exists_chartFrameTransitionUnit
#print axioms PaperVerification.ToricSchemes.CartierData.chartFrameGenerator_isUnit_of_range
