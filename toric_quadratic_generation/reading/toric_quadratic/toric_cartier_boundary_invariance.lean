module

public import PaperVerification.ToricDominantCartierPullback
public import PaperVerification.ToricNormalCartier
public import PaperVerification.ToricOrderTransport
public import PaperVerification.ToricBoundaryFixedPoints
public import PaperVerification.ToricCartierChartValues

@[expose] public section

/-!
# Genuine Cartier invariance from fixed boundary components

This file retains the actual rational embedding of each invertible sheaf.
The normalized representative is proved to have unit local frames on the
dense torus. Actual generic-stalk pullback preserves this property. On a
smooth scheme, an automorphism fixing the codimension-one boundary points
therefore preserves the Cartier divisor, by the proved Cartier-to-Weil
injectivity theorem.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

universe u

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory MonObj

namespace PaperVerification.ToricSchemes

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

/-- Both a rational function and its inverse lie in the actual local ring. -/
def IsRegularUnitAt (X : Scheme.{u}) [IsIntegral X] (x : X) (z : X.functionField) : Prop :=
  z∈regularAtSubring X x ∧ z⁻¹∈regularAtSubring X x

theorem isRegularUnitAt_pullback (f : Y ⟶ X) [IsDominant f]
    (y : Y) (z : X.functionField) (h : IsRegularUnitAt X (f y) z) :
    IsRegularUnitAt Y y (dominantFunctionFieldMap f z) := by
  refine ⟨dominantFunctionFieldMap_mem_regularAt f y z h.1,?_⟩
  simpa only [map_inv₀] using dominantFunctionFieldMap_mem_regularAt f y z⁻¹ h.2

theorem rationalOrder_zero_of_isRegularUnitAt [IsLocallyNoetherian X]
    (x : X) (z : X.functionField) (hz : z≠0) (h : IsRegularUnitAt X x z) :
    X.ord z x=0 := by
  obtain ⟨a,ha⟩ := h.1
  obtain ⟨b,hb⟩ := h.2
  have hab : a*b=1 := by
    apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
    rw [map_mul,map_one,ha,hb,mul_inv_cancel₀ hz]
  let aU : (X.presheaf.stalk x)ˣ := ⟨a,b,hab,by simpa only [mul_comm] using hab⟩
  by_cases hx : Order.coheight x=1
  · letI : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
    apply (X.ord_eq_iff hx hz).mpr
    change Ring.ordFrac (X.presheaf.stalk x) z=1
    rw [← ha]
    exact Ring.ordFrac_of_isUnit aU.isUnit
  · exact Scheme.ord_eq_zero_of_coheight_neq_one hx z

namespace RationalCartierCocycle

variable (C : RationalCartierCocycle X)

def HasUnitFramesOn (U : X.Opens) : Prop :=
  ∀ i (x : X),x∈U→x∈C.openSet i→IsRegularUnitAt X x (C.generator i : X.functionField)

theorem HasUnitFramesOn.pow {C : RationalCartierCocycle X}
    {U : X.Opens} (h : C.HasUnitFramesOn U) (n : ℕ) :
    (C.pow n).HasUnitFramesOn U := by
  intro i x hx hi
  change IsRegularUnitAt X x ((C.generator i : X.functionField)^n)
  obtain ⟨hpos,hneg⟩ := h i x hx hi
  refine ⟨?_,?_⟩
  · exact (regularAtSubring X x).pow_mem hpos n
  · simpa only [inv_pow] using (regularAtSubring X x).pow_mem hneg n

/-- Unit frames are independent of the actual Cartier presentation. -/
theorem HasUnitFramesOn.of_equivalent {C : RationalCartierCocycle X} {U : X.Opens}
    (h : C.HasUnitFramesOn U) (D : RationalCartierCocycle X)
    (he : C.toCartierData.Equivalent D.toCartierData) : D.HasUnitFramesOn U := by
  intro j x hx hj
  obtain ⟨i,hi⟩ := C.covers x
  have hC := h i x hx hi
  have hDC := D.generatorRatios_of_equivalent C
    (C.toCartierData.equivalent_symm D.toCartierData he) j i x hj hi
  have hCD := C.generatorRatios_of_equivalent D he i j x hi hj
  refine ⟨?_,?_⟩
  · have hh := (regularAtSubring X x).mul_mem hDC hC.1
    simpa only [div_mul_cancel₀ _ (C.generator i).ne_zero] using hh
  · have hh := (regularAtSubring X x).mul_mem hC.2 hCD
    have heq : (C.generator i : X.functionField)⁻¹ *
        ((C.generator i : X.functionField)/(D.generator j : X.functionField)) =
        (D.generator j : X.functionField)⁻¹ := by
      field_simp [Units.ne_zero]
    simpa only [heq] using hh

theorem hasUnitFramesOn_pullback (U : X.Opens) (h : C.HasUnitFramesOn U)
    (f : Y ⟶ X) [IsDominant f] :
    (C.dominantPullback f).HasUnitFramesOn (f ⁻¹ᵁ U) := by
  intro i y hyU hyi
  exact isRegularUnitAt_pullback f y _ (h i (f y) hyU hyi)

theorem weilCoefficient_eq_neg_generator [IsLocallyNoetherian X]
    (i : C.index) (x : X) (hx : x∈C.openSet i) :
    C.toCartierData.weilCoefficient x = -X.ord (C.generator i : X.functionField) x := by
  letI : Nonempty (C.openSet i) := ⟨⟨x,hx⟩⟩
  rw [C.toCartierData.weilCoefficient_eq_neg_frameOrder (C.localFrame i) hx]
  change -X.ord (C.toCartierData.sectionValue (C.openSet i)
    (ModuleFrame.generator (C.localFrame i) (C.openSet i) le_rfl)) x = _
  rw [localFrame_generator_value]

theorem weilCoefficient_zero_of_unitFrames [IsLocallyNoetherian X]
    (U : X.Opens) (h : C.HasUnitFramesOn U) (x : X) (hx : x∈U) :
    C.toCartierData.weilCoefficient x=0 := by
  obtain ⟨i,hi⟩ := C.covers x
  rw [C.weilCoefficient_eq_neg_generator i x hi,
    rationalOrder_zero_of_isRegularUnitAt x _ (C.generator i).ne_zero (h i x hx hi),neg_zero]

theorem weilCoefficient_pullback_iso [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (e : Y≅X) (y : Y) :
    (C.dominantPullback e.hom).toCartierData.weilCoefficient y =
      C.toCartierData.weilCoefficient (e.hom y) := by
  obtain ⟨i,hi⟩ := C.covers (e.hom y)
  rw [(C.dominantPullback e.hom).weilCoefficient_eq_neg_generator i y hi,
    C.weilCoefficient_eq_neg_generator i (e.hom y) hi,
    dominantPullback_generator,schemeOrder_iso]

end RationalCartierCocycle

namespace CartierData

variable (D : CartierData X)

theorem hasUnitFramesOn_nsmul {U : X.Opens}
    (h : D.localCocycle.HasUnitFramesOn U) (n : ℕ) :
    (D.nsmul n).localCocycle.HasUnitFramesOn U :=
  (h.pow n).of_equivalent (D.nsmul n).localCocycle
    (D.nsmul n).equivalent_localCocycle

theorem weilCoefficient_dominantPullback_iso
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (e : Y≅X) (y : Y) :
    (D.dominantPullback e.hom).weilCoefficient y = D.weilCoefficient (e.hom y) := by
  rw [dominantPullback,D.localCocycle.weilCoefficient_pullback_iso]
  exact (congrFun (D.equivalent_weilCoefficient D.localCocycle.toCartierData
    D.equivalent_localCocycle) (e.hom y)).symm

/-- An actual automorphism fixing the codimension-one support fixes the
Cartier divisor itself. No linear-equivalence relaxation occurs here. -/
theorem equivalent_pullback_of_boundary_fixed
    [IsLocallyNoetherian X] {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [Smooth f] (e : X≅X)
    (B : Set X) (hB : e.hom ⁻¹' B=B)
    (hfixed : ∀ x∈B,Order.coheight x=1→e.hom x=x)
    (hzero : ∀ x∉B,D.weilCoefficient x=0) :
    (D.dominantPullback e.hom).Equivalent D := by
  apply equivalent_of_weilCoefficient_eq f
  funext x
  by_cases hcodim : Order.coheight x=1
  · rw [D.weilCoefficient_dominantPullback_iso e]
    by_cases hx : x∈B
    · rw [hfixed x hx hcodim]
    · have hex : e.hom x∉B := by
        intro h
        apply hx
        change x∈e.hom ⁻¹' B at h
        rwa [hB] at h
      rw [hzero _ hex,hzero _ hx]
  · rw [weilCoefficient_eq_zero_of_coheight_ne_one _ hcodim,
      weilCoefficient_eq_zero_of_coheight_ne_one _ hcodim]

end CartierData

namespace RationalCartierCocycle

theorem equivalent_pullback_of_boundary_fixed
    [IsLocallyNoetherian X] {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [Smooth f] (C : RationalCartierCocycle X)
    (e : X≅X) (B : Set X) (hB : e.hom ⁻¹' B=B)
    (hfixed : ∀ x∈B,Order.coheight x=1→e.hom x=x)
    (hzero : ∀ x∉B,C.toCartierData.weilCoefficient x=0) :
    (C.dominantPullback e.hom).toCartierData.Equivalent C.toCartierData := by
  apply CartierData.equivalent_of_weilCoefficient_eq f
  funext x
  by_cases hcodim : Order.coheight x=1
  · rw [C.weilCoefficient_pullback_iso e]
    by_cases hx : x∈B
    · rw [hfixed x hx hcodim]
    · have hex : e.hom x∉B := by
        intro h
        apply hx
        change x∈e.hom ⁻¹' B at h
        rwa [hB] at h
      rw [hzero _ hex,hzero _ hx]
  · rw [CartierData.weilCoefficient_eq_zero_of_coheight_ne_one _ hcodim,
      CartierData.weilCoefficient_eq_zero_of_coheight_ne_one _ hcodim]

end RationalCartierCocycle

section NormalizedTorus

variable (k : Type u) [Field k] (n : ℕ) (X : Scheme.{u}) [IsIntegral X]
    (j : splitTorus k (Fin n→ℤ) ⟶ X) [IsOpenImmersion j]
    (D : CartierData X)

theorem torusNormalizedCartier_chartGenerator :
    (torusNormalizedCartier k n X j D).chartFrameRationalGenerator j
      (torusNormalizedCartierSheafIso k n X j D)=1 := by
  rw [CartierData.chartFrameRationalGenerator,torusNormalizedCartier_value]
  have h : (torusNormalizedCartierSheafIso k n X j D).hom.app ⊤
      ((torusNormalizedCartierSheafIso k n X j D).inv.app ⊤
        (1 : Γ(splitTorus k (Fin n→ℤ),⊤))) =
      (1 : Γ(splitTorus k (Fin n→ℤ),⊤)) := by
    simpa only [Scheme.Modules.Hom.comp_app,Scheme.Modules.Hom.id_app,
      ConcreteCategory.comp_apply,ConcreteCategory.id_apply] using
      congrArg (fun φ=>φ.app ⊤ (1 : Γ(splitTorus k (Fin n→ℤ),⊤)))
        (torusNormalizedCartierSheafIso k n X j D).inv_hom_id
  exact (congrArg (openImmersionRegularToFunctionField j ⊤) h).trans (map_one _)

theorem torusNormalizedCartier_range_on_open (V : X.Opens) [Nonempty V]
    (hV : V≤j.opensRange) :
    ((torusNormalizedCartier k n X j D).sectionValueRange V : Set X.functionField)=
      Set.range (X.germToFunctionField V) := by
  ext z
  change z ∈ (torusNormalizedCartier k n X j D).sectionValueRange V ↔
    z ∈ Set.range (X.germToFunctionField V)
  rw [(torusNormalizedCartier k n X j D).mem_sectionValueRange_iff_chartFrame
    j (torusNormalizedCartierSheafIso k n X j D) V hV z,
    torusNormalizedCartier_chartGenerator]
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨a,(mul_one (X.germToFunctionField V a)).symm.trans ha⟩
  · rintro ⟨a,ha⟩
    exact ⟨a,(mul_one (X.germToFunctionField V a)).trans ha⟩

/-- Every actual local rational frame of the normalized divisor is a
regular unit at every point of the torus open. -/
theorem torusNormalizedCartier_unitFrames :
    (torusNormalizedCartier k n X j D).localCocycle.HasUnitFramesOn j.opensRange := by
  let E := torusNormalizedCartier k n X j D
  intro i x hx hxi
  let V : X.Opens := E.localCocycle.openSet i⊓j.opensRange
  letI : Nonempty V := ⟨⟨x,hxi,hx⟩⟩
  letI : Nonempty (invertibleOpen E.locallyFree i ⊓ j.opensRange : X.Opens) :=
    ⟨⟨x,hxi,hx⟩⟩
  letI : Nonempty (invertibleOpen E.locallyFree i) :=
    ⟨⟨i,mem_invertibleOpen E.locallyFree i⟩⟩
  let e := invertibleFrame E.locallyFree i
  have hrange := torusNormalizedCartier_range_on_open k n X j D V inf_le_right
  have hq : (E.localCocycle.generator i : X.functionField)∈E.sectionValueRange V := by
    refine ⟨E.frameGenerator e V inf_le_left,?_⟩
    exact E.sectionValue_frameGenerator e inf_le_left
  change (E.localCocycle.generator i : X.functionField) ∈
    ((torusNormalizedCartier k n X j D).sectionValueRange V : Set X.functionField) at hq
  rw [hrange] at hq
  obtain ⟨a,ha⟩ := hq
  have hone : (1 : X.functionField)∈E.sectionValueRange V := by
    change (1 : X.functionField) ∈
      ((torusNormalizedCartier k n X j D).sectionValueRange V : Set X.functionField)
    rw [hrange]
    exact ⟨1,map_one _⟩
  obtain ⟨b,hb⟩ := (E.mem_sectionValueRange_iff e inf_le_left 1).mp hone
  have hb' : X.germToFunctionField V b=(E.localCocycle.generator i : X.functionField)⁻¹ := by
    apply mul_right_cancel₀ (E.localCocycle.generator i).ne_zero
    rw [inv_mul_cancel₀ (E.localCocycle.generator i).ne_zero]
    exact hb
  constructor
  · rw [← ha]
    exact regular_germ_mem_regularAt X V a x ⟨hxi,hx⟩
  · rw [← hb']
    exact regular_germ_mem_regularAt X V b x ⟨hxi,hx⟩

end NormalizedTorus

end PaperVerification.ToricSchemes
