module

public import PaperVerification.ToricAffinePicard
public import PaperVerification.ToricCartierTranslate
public import PaperVerification.ToricCartierScaleCocycle
public import PaperVerification.ToricInvertibleRestriction
public import PaperVerification.ToricDenseTorusFunctionField

@[expose] public section

/-!
# A linearly equivalent Cartier representative trivial on the dense torus

The actual torus Picard trivialization supplies a nonzero rational generator.
Multiplying the fractional embedding by its inverse gives a linearly
equivalent Cartier divisor. On every open of the torus, the new actual
fractional module is precisely the actual regular-function module. The
explicit rational factor is retained; equality of divisors is not confused
with linear equivalence.
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace PaperVerification.ToricSchemes

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (j : Y ⟶ X) [IsOpenImmersion j]

namespace CartierData

variable (D : CartierData X)

/-- The actual rational value of a section on a nonempty open chart. -/
def alongSectionValue (V : Y.Opens) [Nonempty V] :
    Γ(D.sheaf.restrict j,V) →+ X.functionField := by
  letI : Nonempty (j ''ᵁ V) := openImmersion_image_nonempty j V
  exact (D.sectionValue (j ''ᵁ V)).toAddMonoidHom.comp
    (D.sheaf.restrictAppIso j V).addCommGroupIsoToAddEquiv.toAddMonoidHom

theorem alongSectionValue_injective (V : Y.Opens) [Nonempty V] :
    Function.Injective (D.alongSectionValue j V) := by
  letI : Nonempty (j ''ᵁ V) := openImmersion_image_nonempty j V
  exact (D.sectionValue_injective (j ''ᵁ V)).comp
    (D.sheaf.restrictAppIso j V).addCommGroupIsoToAddEquiv.injective

theorem alongSectionValue_smul (V : Y.Opens) [Nonempty V]
    (a : Γ(Y,V)) (s : Γ(D.sheaf.restrict j,V)) :
    D.alongSectionValue j V (a • s) =
      openImmersionRegularToFunctionField j V a * D.alongSectionValue j V s := by
  letI : Nonempty (j ''ᵁ V) := openImmersion_image_nonempty j V
  change D.sectionValue (j ''ᵁ V)
      ((j.appIso V).inv a • (D.sheaf.restrictAppIso j V).hom s) = _
  rw [D.sectionValue_smul,openImmersionRegularToFunctionField_eq_germ_image]
  rfl

theorem alongSectionValue_restrict {U V : Y.Opens} [Nonempty U] [Nonempty V]
    (i : V ⟶ U) (s : Γ(D.sheaf.restrict j,U)) :
    D.alongSectionValue j V ((D.sheaf.restrict j).presheaf.map i.op s) =
      D.alongSectionValue j U s := by
  letI : Nonempty (j ''ᵁ U) := openImmersion_image_nonempty j U
  letI : Nonempty (j ''ᵁ V) := openImmersion_image_nonempty j V
  exact D.sectionValue_restrict (homOfLE (j.image_mono i.le)) s

/-- Evaluation of an actual global trivialization on any open of the chart. -/
def chartFrameCoordinates
    (e : D.sheaf.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf) (V : Y.Opens) :
    Γ(D.sheaf.restrict j,V) ≃ₗ[Γ(Y,V)] Γ(Y,V) :=
  ((PresheafOfModules.evaluation Y.ringCatSheaf.obj (op V)).mapIso
    ((SheafOfModules.forget _).mapIso e)).toLinearEquiv

/-- The nonzero rational generator supplied by an actual chart trivialization. -/
def chartFrameRationalGenerator
    (e : D.sheaf.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf) : X.functionField :=
  D.alongSectionValue j ⊤ (e.inv.app ⊤ (1 : Γ(Y,⊤)))

theorem chartFrameRationalGenerator_ne_zero
    (e : D.sheaf.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf) :
    D.chartFrameRationalGenerator j e ≠ 0 := by
  intro hzero
  have hz : e.inv.app ⊤ (1 : Γ(Y,⊤))=0 :=
    D.alongSectionValue_injective j ⊤ (hzero.trans (map_zero _).symm)
  have h1 : (1 : Γ(Y,⊤))=0 := by
    let L := D.chartFrameCoordinates j e ⊤
    calc
      (1 : Γ(Y,⊤)) = L (e.inv.app ⊤ (1 : Γ(Y,⊤))) :=
        (L.apply_symm_apply (1 : Γ(Y,⊤))).symm
      _ = L 0 := congrArg L hz
      _ = 0 := map_zero L
  apply (one_ne_zero : (1 : Y.functionField) ≠ 0)
  calc
    (1 : Y.functionField) = Y.germToFunctionField ⊤ (1 : Γ(Y,⊤)) :=
      (map_one (Y.germToFunctionField ⊤).hom).symm
    _ = Y.germToFunctionField ⊤ (0 : Γ(Y,⊤)) := congrArg (Y.germToFunctionField ⊤) h1
    _ = 0 := map_zero (Y.germToFunctionField ⊤).hom

theorem alongSectionValue_frameGenerator
    (e : D.sheaf.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf)
    (V : Y.Opens) [Nonempty V] :
    D.alongSectionValue j V (e.inv.app V (1 : Γ(Y,V)))=D.chartFrameRationalGenerator j e := by
  have hg : e.inv.app V (1 : Γ(Y,V)) =
      (D.sheaf.restrict j).presheaf.map (homOfLE le_top).op (e.inv.app ⊤ (1 : Γ(Y,⊤))) := by
    have hn := PresheafOfModules.naturality_apply e.inv.val
      (homOfLE (show V≤(⊤ : Y.Opens) from le_top)).op
      (1 : Γ(Y,⊤))
    change e.inv.app V
        ((Y.presheaf.map (homOfLE (show V≤(⊤ : Y.Opens) from le_top)).op).hom
          (1 : Γ(Y,⊤))) =
      (D.sheaf.restrict j).presheaf.map (homOfLE le_top).op
        (e.inv.app ⊤ (1 : Γ(Y,⊤))) at hn
    simpa only [map_one] using hn
  calc
    _ = D.alongSectionValue j V
        ((D.sheaf.restrict j).presheaf.map (homOfLE le_top).op
          (e.inv.app ⊤ (1 : Γ(Y,⊤)))) := congrArg (D.alongSectionValue j V) hg
    _ = D.alongSectionValue j ⊤ (e.inv.app ⊤ (1 : Γ(Y,⊤))) :=
      D.alongSectionValue_restrict j (homOfLE (show V≤(⊤ : Y.Opens) from le_top)) _
    _ = _ := rfl

/-- The actual chart coordinate describes the rational value of every
section, not only the distinguished generator. -/
theorem alongSectionValue_frame
    (e : D.sheaf.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf)
    (V : Y.Opens) [Nonempty V] (s : Γ(D.sheaf.restrict j,V)) :
    D.alongSectionValue j V s =
      openImmersionRegularToFunctionField j V (e.hom.app V s) *
        D.chartFrameRationalGenerator j e := by
  let a : Γ(Y,V) := e.hom.app V s
  let t : Γ(D.sheaf.restrict j,V) := e.inv.app V (1 : Γ(Y,V))
  have hs : s=a • t := by
    apply (D.chartFrameCoordinates j e V).injective
    change D.chartFrameCoordinates j e V s =
      D.chartFrameCoordinates j e V
        (D.chartFrameCoordinates j e V s • (D.chartFrameCoordinates j e V).symm 1)
    simp
  calc
    _ = D.alongSectionValue j V (a • t) := congrArg (D.alongSectionValue j V) hs
    _ = openImmersionRegularToFunctionField j V a * D.alongSectionValue j V t :=
      D.alongSectionValue_smul j V a t
    _ = _ := congrArg (fun z : X.functionField => openImmersionRegularToFunctionField j V a * z)
      (D.alongSectionValue_frameGenerator j e V)

theorem scale_alongSectionValue (q : X.functionFieldˣ)
    (V : Y.Opens) [Nonempty V] (s : Γ(D.sheaf.restrict j,V)) :
    (D.scale q).alongSectionValue j V s =
      (q : X.functionField)*D.alongSectionValue j V s := by
  letI : Nonempty (j ''ᵁ V) := openImmersion_image_nonempty j V
  exact D.scale_sectionValue q (j ''ᵁ V) s

end CartierData

section Torus

open PaperVerification.ToricCharacters

variable (k : Type u) [Field k] (n : ℕ) (X : Scheme.{u}) [IsIntegral X]
    (j : splitTorus k (Fin n→ℤ) ⟶ X) [hj : IsOpenImmersion j]
    (D : CartierData X)

local instance torusScheme_integral : IsIntegral (splitTorus k (Fin n→ℤ)) := by
  letI := torusCoordinateRing_isDomain k n
  change IsIntegral (Spec (CommRingCat.of (torusCoordinateRing k n)))
  infer_instance

/-- The actual Picard trivialization of the restriction to the split torus. -/
def torusCartierFrame :
    D.sheaf.restrict j ≅ SheafOfModules.unit (splitTorus k (Fin n→ℤ)).ringCatSheaf := by
  letI : IsOpenImmersion
      (show Spec (CommRingCat.of (torusCoordinateRing k n)) ⟶ X from j) := hj
  exact torusInvertibleSheafIso k n (D.sheaf.restrict j)
    (isInvertibleModule_restrict j D.locallyFree)

/-- The explicit ambient rational generator supplied by this trivialization. -/
def torusCartierGenerator : X.functionFieldˣ := by
  letI := torusCoordinateRing_isDomain k n
  exact Units.mk0 (D.chartFrameRationalGenerator j (torusCartierFrame k n X j D))
    (D.chartFrameRationalGenerator_ne_zero j (torusCartierFrame k n X j D))

/-- A linearly equivalent representative, normalized to O_T on the actual
dense open torus. The rational translation factor remains explicit. -/
def torusNormalizedCartier : CartierData X :=
  D.scale (torusCartierGenerator k n X j D)⁻¹

theorem torusNormalizedCartier_linearlyEquivalent :
    (torusNormalizedCartier k n X j D).LinearlyEquivalent D :=
  D.scale_linearlyEquivalent _

theorem torusNormalizedCartier_isAmple_iff :
    (torusNormalizedCartier k n X j D).IsAmple ↔ D.IsAmple :=
  D.isAmple_scale_iff _

def torusNormalizedCartierSheafIso :
    (torusNormalizedCartier k n X j D).sheaf.restrict j ≅
      SheafOfModules.unit (splitTorus k (Fin n→ℤ)).ringCatSheaf :=
  torusCartierFrame k n X j D

/-- On every nonempty torus open, the normalized actual fractional embedding
agrees with the ordinary embedding of regular functions into K(X). -/
theorem torusNormalizedCartier_value
    (V : (splitTorus k (Fin n→ℤ)).Opens) [Nonempty V]
    (s : Γ((torusNormalizedCartier k n X j D).sheaf.restrict j,V)) :
    (torusNormalizedCartier k n X j D).alongSectionValue j V s =
      openImmersionRegularToFunctionField j V
        ((torusNormalizedCartierSheafIso k n X j D).hom.app V s) := by
  letI := torusCoordinateRing_isDomain k n
  calc
    _ = (↑((torusCartierGenerator k n X j D)⁻¹) : X.functionField) *
        D.alongSectionValue j V s := D.scale_alongSectionValue j _ V s
    _ = (↑((torusCartierGenerator k n X j D)⁻¹) : X.functionField) *
        (openImmersionRegularToFunctionField j V
          ((torusCartierFrame k n X j D).hom.app V s) *
            D.chartFrameRationalGenerator j (torusCartierFrame k n X j D)) :=
      congrArg (fun z : X.functionField =>
        (↑((torusCartierGenerator k n X j D)⁻¹) : X.functionField) * z)
        (D.alongSectionValue_frame j (torusCartierFrame k n X j D) V s)
    _ = _ := by
      change (D.chartFrameRationalGenerator j (torusCartierFrame k n X j D))⁻¹ *
          (openImmersionRegularToFunctionField j V
            ((torusCartierFrame k n X j D).hom.app V s) *
              D.chartFrameRationalGenerator j (torusCartierFrame k n X j D)) = _
      field_simp [D.chartFrameRationalGenerator_ne_zero j (torusCartierFrame k n X j D)]
      rfl

/-- Equality of the actual fractional module with the regular-function
module on each torus open. No boundary or invariant-divisor dictionary is
included as an assumption. -/
theorem torusNormalizedCartier_range
    (V : (splitTorus k (Fin n→ℤ)).Opens) [Nonempty V] :
    Set.range ((torusNormalizedCartier k n X j D).alongSectionValue j V) =
      Set.range (openImmersionRegularToFunctionField j V) := by
  letI := torusCoordinateRing_isDomain k n
  ext r
  constructor
  · rintro ⟨s,rfl⟩
    exact ⟨(torusNormalizedCartierSheafIso k n X j D).hom.app V s,
      (torusNormalizedCartier_value k n X j D V s).symm⟩
  · rintro ⟨a,rfl⟩
    let E := torusNormalizedCartierSheafIso k n X j D
    let C := torusNormalizedCartier k n X j D
    let s := E.inv.app V a
    refine ⟨s,?_⟩
    calc
      _ = openImmersionRegularToFunctionField j V (E.hom.app V s) :=
        torusNormalizedCartier_value k n X j D V s
      _ = _ := congrArg (openImmersionRegularToFunctionField j V)
        ((C.chartFrameCoordinates j E V).apply_symm_apply a)

end Torus

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.torusNormalizedCartier_linearlyEquivalent
#print axioms PaperVerification.ToricSchemes.torusNormalizedCartier_value
#print axioms PaperVerification.ToricSchemes.torusNormalizedCartier_range
