module

public import PaperVerification.ToricCartierRationalSections
public import PaperVerification.ToricBaseSectionNaturality
public import PaperVerification.ToricSectionMultiplicationTransport

@[expose] public section

/-!
# Actual Cartier sections under a scheme isomorphism

The maps below use the genuine generic-stalk homomorphism. The section
condition is transported in both directions through the genuine maps of
local rings. This gives base-linear equivalences of actual global-section
spaces. Compatibility with addition and multiplication is proved from the
actual rational values, so no section-space identification is assumed.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

namespace PaperVerification.ToricSchemes

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

@[simp] theorem dominantFunctionFieldMap_id :
    dominantFunctionFieldMap (𝟙 X)=RingHom.id X.functionField := by
  ext r
  have h := congrArg (fun φ : X.functionField →+* X.functionField => φ r)
    (dominantFunctionFieldMap_comp (𝟙 X) (𝟙 X))
  simp only [Category.id_comp,RingHom.comp_apply] at h
  exact (dominantFunctionFieldMap_injective (𝟙 X)) h.symm

@[simp] theorem dominantFunctionFieldMap_iso_hom_inv (e : Y ≅ X)
    (r : X.functionField) :
    dominantFunctionFieldMap e.inv (dominantFunctionFieldMap e.hom r)=r := by
  have h := congrArg (fun φ : X.functionField →+* X.functionField => φ r)
    (dominantFunctionFieldMap_comp e.inv e.hom)
  simpa only [e.inv_hom_id,dominantFunctionFieldMap_id,RingHom.id_apply,
    RingHom.comp_apply] using h.symm

@[simp] theorem dominantFunctionFieldMap_iso_inv_hom (e : Y ≅ X)
    (r : Y.functionField) :
    dominantFunctionFieldMap e.hom (dominantFunctionFieldMap e.inv r)=r :=
  dominantFunctionFieldMap_iso_hom_inv e.symm r

/-- Regularity is transported by the actual local-ring isomorphism. -/
theorem regularAt_schemeIso_iff (e : Y ≅ X) (y : Y) (r : X.functionField) :
    dominantFunctionFieldMap e.hom r ∈ regularAtSubring Y y ↔
      r ∈ regularAtSubring X (e.hom y) := by
  constructor
  · intro h
    have he : e.inv (e.hom y)=y := by
      change (e.hom≫e.inv) y=y
      rw [e.hom_inv_id]
      rfl
    have h' := dominantFunctionFieldMap_mem_regularAt e.inv (e.hom y)
      (dominantFunctionFieldMap e.hom r) (by simpa only [he] using h)
    simpa only [dominantFunctionFieldMap_iso_hom_inv] using h'
  · exact dominantFunctionFieldMap_mem_regularAt e.hom y r

namespace RationalCartierCocycle

variable (C D : RationalCartierCocycle X) (f : Y ⟶ X) [IsDominant f]

theorem toCartierData_dominantPullback_equivalent :
    (C.toCartierData.dominantPullback f).Equivalent
      (C.dominantPullback f).toCartierData :=
  C.toCartierData.localCocycle.dominantPullback_equivalent_of_equivalent f C
    (C.toCartierData.equivalent_symm C.toCartierData.localCocycle.toCartierData
      C.toCartierData.equivalent_localCocycle)

theorem dominantPullback_mul_equivalent :
    ((C.mul D).dominantPullback f).toCartierData.Equivalent
      ((C.dominantPullback f).mul (D.dominantPullback f)).toCartierData := by
  apply RationalCartierCocycle.equivalent_of_generatorRatios
  · intro i j y hi hj
    have h := ((C.dominantPullback f).mul (D.dominantPullback f)).transition
      i j y hi hj
    change ((dominantFunctionFieldMap f) (C.generator i.1 : X.functionField) *
      (dominantFunctionFieldMap f) (D.generator i.2 : X.functionField)) /
      ((dominantFunctionFieldMap f) (C.generator j.1 : X.functionField) *
      (dominantFunctionFieldMap f) (D.generator j.2 : X.functionField)) ∈
        regularAtSubring Y y at h
    change (dominantFunctionFieldMap f)
      ((C.generator i.1 : X.functionField) * (D.generator i.2 : X.functionField)) /
      ((dominantFunctionFieldMap f) (C.generator j.1 : X.functionField) *
      (dominantFunctionFieldMap f) (D.generator j.2 : X.functionField)) ∈
        regularAtSubring Y y
    simpa only [map_mul] using h
  · intro i j y hi hj
    have h := ((C.dominantPullback f).mul (D.dominantPullback f)).transition
      i j y hi hj
    change ((dominantFunctionFieldMap f) (C.generator i.1 : X.functionField) *
      (dominantFunctionFieldMap f) (D.generator i.2 : X.functionField)) /
      ((dominantFunctionFieldMap f) (C.generator j.1 : X.functionField) *
      (dominantFunctionFieldMap f) (D.generator j.2 : X.functionField)) ∈
        regularAtSubring Y y at h
    change ((dominantFunctionFieldMap f) (C.generator i.1 : X.functionField) *
      (dominantFunctionFieldMap f) (D.generator i.2 : X.functionField)) /
      (dominantFunctionFieldMap f)
      ((C.generator j.1 : X.functionField) * (D.generator j.2 : X.functionField)) ∈
        regularAtSubring Y y
    simpa only [map_mul] using h

end RationalCartierCocycle

namespace CartierData

variable (D E : CartierData X)

theorem dominantPullback_add_equivalent (f : Y ⟶ X) [IsDominant f] :
    ((D.add E).dominantPullback f).Equivalent
      ((D.dominantPullback f).add (E.dominantPullback f)) := by
  let C := D.localCocycle
  let F := E.localCocycle
  have h₁ := (C.mul F).toCartierData_dominantPullback_equivalent f
  have h₂ := C.dominantPullback_mul_equivalent F f
  have h₃ := (C.dominantPullback f).toCartierData_add_equivalent
    (F.dominantPullback f)
  exact ((D.add E).dominantPullback f).equivalent_trans
    ((C.mul F).dominantPullback f).toCartierData _ h₁
    (((C.mul F).dominantPullback f).toCartierData.equivalent_trans
      ((C.dominantPullback f).mul (F.dominantPullback f)).toCartierData _ h₂
      (((D.dominantPullback f).add (E.dominantPullback f)).equivalent_symm _ h₃))

/-- Every global section is detected in both directions, not merely
injected into the pullback section space. -/
theorem globalSectionRange_schemeIso_iff (e : Y ≅ X) (r : X.functionField) :
    dominantFunctionFieldMap e.hom r ∈ (D.dominantPullback e.hom).sectionValueRange ⊤ ↔
      r ∈ D.sectionValueRange ⊤ := by
  constructor
  · intro h
    apply (D.mem_sectionValueRange_iff_localStalks ⊤ r).mpr
    intro i x hx hi
    have hex : e.hom (e.inv x)=x := by
      change (e.inv≫e.hom) x=x
      rw [e.inv_hom_id]
      rfl
    have h' := ((D.localCocycle.dominantPullback e.hom).mem_sectionValueRange_iff_stalkwise
      ⊤ _).mp h i (e.inv x) trivial
        (by
          change e.hom (e.inv x) ∈ D.localCocycle.openSet i
          rw [hex]
          exact hi)
    change dominantFunctionFieldMap e.hom r /
      dominantFunctionFieldMap e.hom (D.localCocycle.generator i : X.functionField) ∈
        regularAtSubring Y (e.inv x) at h'
    rw [← map_div₀,regularAt_schemeIso_iff,hex] at h'
    exact h'
  · intro h
    apply ((D.localCocycle.dominantPullback e.hom).mem_sectionValueRange_iff_stalkwise
      ⊤ _).mpr
    intro i y _ hi
    change e.hom y ∈ D.localCocycle.openSet i at hi
    have h' := (D.mem_sectionValueRange_iff_localStalks ⊤ r).mp h
      i (e.hom y) trivial hi
    change dominantFunctionFieldMap e.hom r /
      dominantFunctionFieldMap e.hom (D.localCocycle.generator i : X.functionField) ∈
        regularAtSubring Y y
    rw [← map_div₀,regularAt_schemeIso_iff]
    exact h'

end CartierData

open scoped BaseSections

variable (k : Type u) [CommRing k]
    [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
    (e : Y ≅ X) [e.hom.IsOver (Spec (CommRingCat.of k))]

def schemeIsoFunctionFieldAlgEquiv : X.functionField ≃ₐ[k] Y.functionField where
  __ := openImmersionFunctionFieldEquiv e.hom
  commutes' := (BaseSections.dominantFunctionFieldAlgHom k e.hom).commutes

@[simp] theorem schemeIsoFunctionFieldAlgEquiv_apply (r : X.functionField) :
    schemeIsoFunctionFieldAlgEquiv k e r=dominantFunctionFieldMap e.hom r := rfl

namespace CartierData

variable (D E : CartierData X)

theorem globalSectionValue_map_schemeIso :
    ((D.globalSectionValue k).range).map
      (schemeIsoFunctionFieldAlgEquiv k e).toLinearEquiv.toLinearMap =
        ((D.dominantPullback e.hom).globalSectionValue k).range := by
  ext r
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact (D.globalSectionRange_schemeIso_iff e z).mpr hz
  · intro hr
    obtain ⟨z,rfl⟩ := (schemeIsoFunctionFieldAlgEquiv k e).surjective r
    exact ⟨z,(D.globalSectionRange_schemeIso_iff e z).mp hr,rfl⟩

/-- The actual global-section equivalence over the original base field. -/
def schemeIsoGlobalSections :
    Γ(D.sheaf,⊤) ≃ₗ[k] Γ((D.dominantPullback e.hom).sheaf,⊤) :=
  (LinearEquiv.ofInjective (D.globalSectionValue k) (D.globalSectionValue_injective k)).trans
    (((schemeIsoFunctionFieldAlgEquiv k e).toLinearEquiv.ofSubmodules
      (D.globalSectionValue k).range ((D.dominantPullback e.hom).globalSectionValue k).range
      (D.globalSectionValue_map_schemeIso k e)).trans
        (LinearEquiv.ofInjective ((D.dominantPullback e.hom).globalSectionValue k)
          ((D.dominantPullback e.hom).globalSectionValue_injective k)).symm)

theorem schemeIsoGlobalSections_value (s : Γ(D.sheaf,⊤)) :
    (D.dominantPullback e.hom).globalSectionValue k (D.schemeIsoGlobalSections k e s) =
      dominantFunctionFieldMap e.hom (D.globalSectionValue k s) := by
  change (D.dominantPullback e.hom).globalSectionValue k
    ((LinearEquiv.ofInjective ((D.dominantPullback e.hom).globalSectionValue k)
      ((D.dominantPullback e.hom).globalSectionValue_injective k)).symm _) = _
  exact congrArg Subtype.val
    ((LinearEquiv.ofInjective ((D.dominantPullback e.hom).globalSectionValue k)
      ((D.dominantPullback e.hom).globalSectionValue_injective k)).apply_symm_apply _)

def schemeIsoSumGlobalSections :
    Γ((D.add E).sheaf,⊤) ≃ₗ[k]
      Γ(((D.dominantPullback e.hom).add (E.dominantPullback e.hom)).sheaf,⊤) :=
  ((D.add E).schemeIsoGlobalSections k e).trans
    (((D.add E).dominantPullback e.hom).equivalentGlobalSections k _
      (D.dominantPullback_add_equivalent E e.hom))

theorem schemeIsoSumGlobalSections_value (s : Γ((D.add E).sheaf,⊤)) :
    ((D.dominantPullback e.hom).add (E.dominantPullback e.hom)).globalSectionValue k
        (D.schemeIsoSumGlobalSections k e E s) =
      dominantFunctionFieldMap e.hom ((D.add E).globalSectionValue k s) := by
  rw [schemeIsoSumGlobalSections,LinearEquiv.trans_apply,
    equivalentGlobalSections_value,schemeIsoGlobalSections_value]

theorem sectionMultiplicationOver_schemeIso :
    (D.schemeIsoSumGlobalSections k e E).toLinearMap.comp
      (D.sectionMultiplicationOver k E) =
    ((D.dominantPullback e.hom).sectionMultiplicationOver k (E.dominantPullback e.hom)).comp
      (TensorProduct.map (D.schemeIsoGlobalSections k e).toLinearMap
        (E.schemeIsoGlobalSections k e).toLinearMap) := by
  apply TensorProduct.ext'
  intro s t
  apply ((D.dominantPullback e.hom).add (E.dominantPullback e.hom)).globalSectionValue_injective k
  change ((D.dominantPullback e.hom).add (E.dominantPullback e.hom)).globalSectionValue k
    (D.schemeIsoSumGlobalSections k e E (D.sectionMultiplicationOver k E (s⊗ₜ[k]t))) =
    ((D.dominantPullback e.hom).add (E.dominantPullback e.hom)).globalSectionValue k
      ((D.dominantPullback e.hom).sectionMultiplicationOver k (E.dominantPullback e.hom)
        (D.schemeIsoGlobalSections k e s⊗ₜ[k]E.schemeIsoGlobalSections k e t))
  rw [schemeIsoSumGlobalSections_value,sectionMultiplicationOver_value_tmul,
    sectionMultiplicationOver_value_tmul,map_mul,schemeIsoGlobalSections_value,
    schemeIsoGlobalSections_value]

/-- Actual section multiplication is surjective before transport exactly
when it is surjective after transport through a genuine k-scheme isomorphism. -/
theorem sectionMultiplicationOver_surjective_iff_schemeIso :
    Function.Surjective (D.sectionMultiplicationOver k E) ↔
      Function.Surjective ((D.dominantPullback e.hom).sectionMultiplicationOver k
        (E.dominantPullback e.hom)) := by
  let es := TensorProduct.congr (D.schemeIsoGlobalSections k e) (E.schemeIsoGlobalSections k e)
  let et := D.schemeIsoSumGlobalSections k e E
  have he (z) : et (D.sectionMultiplicationOver k E z)=
      (D.dominantPullback e.hom).sectionMultiplicationOver k (E.dominantPullback e.hom) (es z) :=
    congrArg (fun φ=>φ z) (D.sectionMultiplicationOver_schemeIso k e E)
  constructor
  · intro h y
    obtain ⟨t,ht⟩ := et.surjective y
    obtain ⟨z,hz⟩ := h t
    exact ⟨es z,(he z).symm.trans (by rw [hz,ht])⟩
  · intro h t
    obtain ⟨y,hy⟩ := h (et t)
    obtain ⟨z,hz⟩ := es.surjective y
    exact ⟨z,et.injective (by rw [he,hz,hy])⟩

end CartierData

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.CartierData.schemeIsoGlobalSections
#print axioms PaperVerification.ToricSchemes.CartierData.sectionMultiplicationOver_surjective_iff_schemeIso
