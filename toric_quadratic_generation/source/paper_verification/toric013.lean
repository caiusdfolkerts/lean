module

public import Lean.Elab.BuiltinEvalCommand
public meta import Lean.Elab.BuiltinEvalCommand
public import Lean.Util.CollectAxioms
public meta import Lean.Util.CollectAxioms
public import Lean.Util.FoldConsts
public meta import Lean.Util.FoldConsts
public import Mathlib.LinearAlgebra.Basis.SMul
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.Localization.Module
public import paper_verification.toric010
public import paper_verification.toric022
public import paper_verification.toric023

@[expose] public section


-- BEGIN ORIGINAL PaperVerification.ToricSectionMultiplicationTransport
section Source_ToricSectionMultiplicationTransport

-- original header: module

-- original header: public import PaperVerification.ToricFanSectionMultiplication

-- original header: @[expose] public section

/-!
# Actual section multiplication under Cartier equivalence

Presentation equality and an explicit principal translation induce
isomorphisms of genuine section spaces. Their compatibility with the
actual multiplication map is proved through the injective rational
values, so surjectivity transports without a chosen character basis.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct

namespace PaperVerification.ToricSchemes.CartierData

open scoped BaseSections

variable (k : Type u) [CommRing k] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of k))] (D D' E E' : CartierData X)

def equivalentGlobalSections (h : D.Equivalent D') :
    Γ(D.sheaf,⊤) ≃ₗ[k] Γ(D'.sheaf,⊤) := by
  let e : Γ(D.sheaf,⊤) ≃ₗ[Γ(X,⊤)] Γ(D'.sheaf,⊤) :=
    (((PresheafOfModules.evaluation X.ringCatSheaf.obj (op ⊤)).mapIso
      ((SheafOfModules.forget _).mapIso h.choose)).toLinearEquiv)
  exact e.restrictScalars k

theorem equivalentGlobalSections_value (h : D.Equivalent D') (s : Γ(D.sheaf,⊤)) :
    D'.globalSectionValue k (D.equivalentGlobalSections k D' h s)=D.globalSectionValue k s := by
  have he := congrArg (fun f=>f.app ⊤ s) h.choose_spec
  change rationalValue X ⊤ (D'.inclusion.app ⊤ (h.choose.hom.app ⊤ s)) =
    rationalValue X ⊤ (D.inclusion.app ⊤ s)
  exact congrArg (rationalValue X ⊤) he

theorem sectionMultiplicationOver_equivalent (hD : D.Equivalent D')
    (hE : E.Equivalent E') :
    ((D.add E).equivalentGlobalSections k (D'.add E')
      (D.add_equivalent_add D' E E' hD hE)).toLinearMap.comp
        (D.sectionMultiplicationOver k E) =
      (D'.sectionMultiplicationOver k E').comp
        (TensorProduct.map (D.equivalentGlobalSections k D' hD).toLinearMap
          (E.equivalentGlobalSections k E' hE).toLinearMap) := by
  apply TensorProduct.ext'
  intro s t
  apply (D'.add E').globalSectionValue_injective k
  change (D'.add E').globalSectionValue k
      ((D.add E).equivalentGlobalSections k (D'.add E') _
        (D.sectionMultiplicationOver k E (s⊗ₜ[k]t))) =
    (D'.add E').globalSectionValue k
      (D'.sectionMultiplicationOver k E'
        (D.equivalentGlobalSections k D' hD s ⊗ₜ[k]
          E.equivalentGlobalSections k E' hE t))
  rw [equivalentGlobalSections_value,sectionMultiplicationOver_value_tmul,
    sectionMultiplicationOver_value_tmul,equivalentGlobalSections_value,
    equivalentGlobalSections_value]

theorem sectionMultiplicationOver_surjective_iff_equivalent
    (hD : D.Equivalent D') (hE : E.Equivalent E') :
    Function.Surjective (D.sectionMultiplicationOver k E) ↔
      Function.Surjective (D'.sectionMultiplicationOver k E') := by
  let es := TensorProduct.congr (D.equivalentGlobalSections k D' hD)
    (E.equivalentGlobalSections k E' hE)
  let et := (D.add E).equivalentGlobalSections k (D'.add E')
    (D.add_equivalent_add D' E E' hD hE)
  have he (z) : et (D.sectionMultiplicationOver k E z)=
      D'.sectionMultiplicationOver k E' (es z) :=
    congrArg (fun f=>f z) (D.sectionMultiplicationOver_equivalent k D' E E' hD hE)
  constructor
  · intro h y
    obtain ⟨t,ht⟩ := et.surjective y
    obtain ⟨z,hz⟩ := h t
    exact ⟨es z,(he z).symm.trans (by rw [hz,ht])⟩
  · intro h t
    obtain ⟨y,hy⟩ := h (et t)
    obtain ⟨z,hz⟩ := es.surjective y
    refine ⟨z,et.injective ?_⟩
    rw [he,hz,hy]

theorem scale_globalSectionValue (q : X.functionFieldˣ) (s : Γ(D.sheaf,⊤)) :
    (D.scale q).globalSectionValue k s = (q : X.functionField) * D.globalSectionValue k s :=
  D.scale_sectionValue q ⊤ s

theorem sectionMultiplicationOver_scale (q r : X.functionFieldˣ) :
    (((D.scale q).add (E.scale r)).equivalentGlobalSections k ((D.add E).scale (q*r))
      (D.scale_add_equivalent q E r)).toLinearMap.comp
        ((D.scale q).sectionMultiplicationOver k (E.scale r)) =
      D.sectionMultiplicationOver k E := by
  apply TensorProduct.ext'
  intro s t
  apply (D.add E).globalSectionValue_injective k
  apply mul_left_cancel₀ (Units.ne_zero (q*r))
  have hv := ((D.scale q).add (E.scale r)).equivalentGlobalSections_value k
    ((D.add E).scale (q*r)) (D.scale_add_equivalent q E r)
    ((D.scale q).sectionMultiplicationOver k (E.scale r) (s⊗ₜ[k]t))
  change ((q*r : X.functionFieldˣ):X.functionField) *
      (D.add E).globalSectionValue k
        (((D.scale q).add (E.scale r)).equivalentGlobalSections k
          ((D.add E).scale (q*r)) _
          ((D.scale q).sectionMultiplicationOver k (E.scale r) (s⊗ₜ[k]t))) = _
  calc
    _ = ((D.add E).scale (q*r)).globalSectionValue k
        (((D.scale q).add (E.scale r)).equivalentGlobalSections k
          ((D.add E).scale (q*r)) _
          ((D.scale q).sectionMultiplicationOver k (E.scale r) (s⊗ₜ[k]t))) :=
      ((D.add E).scale_globalSectionValue k (q*r) _).symm
    _ = ((D.scale q).add (E.scale r)).globalSectionValue k
        ((D.scale q).sectionMultiplicationOver k (E.scale r) (s⊗ₜ[k]t)) := hv
    _ = (D.scale q).globalSectionValue k s * (E.scale r).globalSectionValue k t :=
      (D.scale q).sectionMultiplicationOver_value_tmul k (E.scale r) s t
    _ = ((q : X.functionField) * D.globalSectionValue k s) *
        ((r : X.functionField) * E.globalSectionValue k t) :=
      congrArg₂ (fun a b : X.functionField => a*b)
        (D.scale_globalSectionValue k q s) (E.scale_globalSectionValue k r t)
    _ = ((q*r : X.functionFieldˣ) : X.functionField) *
        (D.globalSectionValue k s * E.globalSectionValue k t) := by
      simp only [Units.val_mul]
      ring
    _ = _ := congrArg (fun a : X.functionField =>
      ((q*r : X.functionFieldˣ) : X.functionField) * a)
        (D.sectionMultiplicationOver_value_tmul k E s t).symm

/-- An explicit rational principal translation does not affect
surjectivity of the genuine section multiplication map. -/
theorem sectionMultiplicationOver_surjective_iff_scale (q r : X.functionFieldˣ) :
    Function.Surjective ((D.scale q).sectionMultiplicationOver k (E.scale r)) ↔
      Function.Surjective (D.sectionMultiplicationOver k E) := by
  let e := ((D.scale q).add (E.scale r)).equivalentGlobalSections k
    ((D.add E).scale (q*r)) (D.scale_add_equivalent q E r)
  have he (z) : e ((D.scale q).sectionMultiplicationOver k (E.scale r) z)=
      D.sectionMultiplicationOver k E z :=
    congrArg (fun f=>f z) (D.sectionMultiplicationOver_scale k E q r)
  constructor
  · intro h t
    obtain ⟨s,hs⟩ := e.surjective t
    obtain ⟨z,hz⟩ := h s
    exact ⟨z,(he z).symm.trans (by rw [hz,hs])⟩
  · intro h s
    obtain ⟨z,hz⟩ := h (e s)
    exact ⟨z,e.injective ((he z).trans hz)⟩

end PaperVerification.ToricSchemes.CartierData

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open PaperVerification.ToricSchemes
open scoped Pointwise BaseSections

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

/-- The full section-multiplication dictionary for arbitrary Cartier
divisors on the actual fan scheme, with no invariant presentation premise. -/
theorem arbitraryCartier_sectionMultiplication_surjective_iff (hpure : «Σ».IsPure)
    (D E : CartierData («Σ».fanScheme k)) :
    Function.Surjective (D.sectionMultiplicationOver k E) ↔
      «Σ».fanIntegralExponents («Σ».cartierCoefficients k hpure D + «Σ».cartierCoefficients k hpure E) =
        «Σ».fanIntegralExponents («Σ».cartierCoefficients k hpure D) +
          «Σ».fanIntegralExponents («Σ».cartierCoefficients k hpure E) := by
  letI : IsOpenImmersion («Σ».splitTorusOpenMap k) :=
    ToricGeometry.SmoothCompleteFan.splitTorusOpenMap_isOpenImmersion k «Σ»
  letI : IsOpenImmersion
      (show ToricSchemes.splitTorus k (Fin n → ℤ) ⟶ «Σ».fanScheme k from
        «Σ».splitTorusOpenMap k) := «Σ».splitTorusOpenMap_isOpenImmersion k
  have hscale : Function.Surjective
      ((«Σ».normalizedCartier k D).sectionMultiplicationOver k («Σ».normalizedCartier k E)) ↔
        Function.Surjective (D.sectionMultiplicationOver k E) :=
    D.sectionMultiplicationOver_surjective_iff_scale k E
      (torusCartierGenerator k n («Σ».fanScheme k) («Σ».splitTorusOpenMap k) D)⁻¹
      (torusCartierGenerator k n («Σ».fanScheme k) («Σ».splitTorusOpenMap k) E)⁻¹
  rw [← hscale]
  rw [(«Σ».normalizedCartier k D).sectionMultiplicationOver_surjective_iff_equivalent k
    («Σ».fanCartierData k hpure («Σ».cartierCoefficients k hpure D))
    («Σ».normalizedCartier k E)
    («Σ».fanCartierData k hpure («Σ».cartierCoefficients k hpure E))
    («Σ».normalizedCartier_equivalent_fanCartier k hpure D)
    («Σ».normalizedCartier_equivalent_fanCartier k hpure E)]
  exact «Σ».fanSectionMultiplication_surjective_iff k hpure _ _

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricSchemes.CartierData.sectionMultiplicationOver_surjective_iff_scale
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.arbitraryCartier_sectionMultiplication_surjective_iff
end
end Source_ToricSectionMultiplicationTransport
-- END ORIGINAL PaperVerification.ToricSectionMultiplicationTransport


-- BEGIN ORIGINAL PaperVerification.ToricCartierSchemeIso
section Source_ToricCartierSchemeIso

-- original header: module

-- original header: public import PaperVerification.ToricCartierRationalSections
-- original header: public import PaperVerification.ToricBaseSectionNaturality
-- original header: public import PaperVerification.ToricSectionMultiplicationTransport

-- original header: @[expose] public section

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
end
end Source_ToricCartierSchemeIso
-- END ORIGINAL PaperVerification.ToricCartierSchemeIso


-- BEGIN ORIGINAL PaperVerification.ToricCoordinateDifferentials
section Source_ToricCoordinateDifferentials

-- original header: module

-- original header: public import PaperVerification.ToricChartFaceLocalization
-- original header: public import Mathlib.RingTheory.Kaehler.Polynomial
-- original header: public import Mathlib.RingTheory.Etale.Kaehler
-- original header: public import Mathlib.RingTheory.Localization.Module
-- original header: public import Mathlib.LinearAlgebra.TensorProduct.Basis
-- original header: public import Mathlib.LinearAlgebra.Basis.SMul

-- original header: @[expose] public section

/-!
# Actual Kähler differentials in integral toric coordinates

A full smooth coordinate chart is identified with the actual polynomial
algebra by its character coordinates. Its differential basis is obtained
from the universal Kähler module, and localization proves the corresponding
basis in the actual Laurent character ring. Multiplying by inverse
characters gives the logarithmic differential basis.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open AddMonoidAlgebra KaehlerDifferential
open scoped BigOperators Classical TensorProduct

variable (k : Type*) [CommRing k]

section PolynomialPresentation

variable {ι A : Type*} [CommRing A] [Algebra k A]

/-- The differential basis transported through an actual polynomial
algebra equivalence. Both the universal module and its scalar action are
the ordinary Mathlib Kähler constructions. -/
def polynomialDifferentialBasis (e : MvPolynomial ι k ≃ₐ[k] A) :
    Module.Basis ι A Ω[A⁄k] := by
  letI : Algebra (MvPolynomial ι k) A := e.toRingHom.toAlgebra
  letI : IsScalarTower k (MvPolynomial ι k) A := IsScalarTower.of_algHom e.toAlgHom
  let eA : MvPolynomial ι k ≃ₐ[MvPolynomial ι k] A :=
    { e.toRingEquiv with commutes' := fun _ => rfl }
  letI : Algebra.FormallyEtale (MvPolynomial ι k) A :=
    Algebra.FormallyEtale.of_equiv eA
  exact ((KaehlerDifferential.mvPolynomialBasis k ι).baseChange A).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k (MvPolynomial ι k) A)

@[simp] theorem polynomialDifferentialBasis_apply
    (e : MvPolynomial ι k ≃ₐ[k] A) (i : ι) :
    polynomialDifferentialBasis k e i = D k A (e (MvPolynomial.X i)) := by
  letI : Algebra (MvPolynomial ι k) A := e.toRingHom.toAlgebra
  letI : IsScalarTower k (MvPolynomial ι k) A := IsScalarTower.of_algHom e.toAlgHom
  let eA : MvPolynomial ι k ≃ₐ[MvPolynomial ι k] A :=
    { e.toRingEquiv with commutes' := fun _ => rfl }
  letI : Algebra.FormallyEtale (MvPolynomial ι k) A := Algebra.FormallyEtale.of_equiv eA
  simp only [polynomialDifferentialBasis, Module.Basis.map_apply,
    Module.Basis.baseChange_apply, KaehlerDifferential.mvPolynomialBasis_apply,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]
  change KaehlerDifferential.mapBaseChange k (MvPolynomial ι k) A
    (1 ⊗ₜ[MvPolynomial ι k] D k (MvPolynomial ι k) (MvPolynomial.X i)) = _
  rw [KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]
  rfl

end PolynomialPresentation

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup E] [Module ℤ E]

def fullCoordinateFunctionsEquiv (b : Module.Basis ι ℤ E) :
    coordinateConeMonoid b Finset.univ ≃+ (ι → ℕ) where
  toFun x i := (b.repr (x : E) i).toNat
  invFun x := ⟨b.equivFun.symm (fun i => (x i : ℤ)), by
    intro i hi
    change 0 ≤ b.equivFun (b.equivFun.symm _) i
    rw [b.equivFun.apply_symm_apply]
    exact Int.natCast_nonneg _⟩
  left_inv x := by
    apply Subtype.ext
    apply b.equivFun.injective
    funext i
    rw [b.equivFun.apply_symm_apply]
    exact Int.toNat_of_nonneg (x.property i (Finset.mem_univ i))
  right_inv x := by
    funext i
    change (b.equivFun (b.equivFun.symm _) i).toNat = x i
    rw [b.equivFun.apply_symm_apply, Int.toNat_natCast]
  map_add' x y := by
    funext i
    change (b.repr ((x : E) + (y : E)) i).toNat =
      (b.repr (x : E) i).toNat + (b.repr (y : E) i).toNat
    rw [map_add, Finsupp.add_apply, Int.toNat_add
      (x.property i (Finset.mem_univ i)) (y.property i (Finset.mem_univ i))]

def fullCoordinateFinsuppEquiv (b : Module.Basis ι ℤ E) :
    coordinateConeMonoid b Finset.univ ≃+ (ι →₀ ℕ) :=
  (fullCoordinateFunctionsEquiv b).trans (naturalFunctionFinsuppEquiv ι)

theorem basis_mem_fullCoordinateCone (b : Module.Basis ι ℤ E) (i : ι) :
    b i ∈ coordinateConeMonoid b Finset.univ := by
  intro j hj
  simp only [Module.Basis.repr_self, Finsupp.single_apply]
  split_ifs <;> omega

@[simp] theorem fullCoordinateFinsuppEquiv_basis (b : Module.Basis ι ℤ E) (i : ι) :
    fullCoordinateFinsuppEquiv b ⟨b i, basis_mem_fullCoordinateCone b i⟩ =
      Finsupp.single i 1 := by
  ext j
  simp [fullCoordinateFinsuppEquiv, fullCoordinateFunctionsEquiv,
    naturalFunctionFinsuppEquiv, Module.Basis.repr_self_apply]
  by_cases hij : i = j <;> simp [Finsupp.single_apply, hij]

def fullChartPolynomialEquiv (b : Module.Basis ι ℤ E) :
    monoidChartAlgebra k (coordinateConeMonoid b Finset.univ) ≃ₐ[k] MvPolynomial ι k :=
  (monoidChartAlgebraEquiv k (coordinateConeMonoid b Finset.univ)).symm.trans
    (AddMonoidAlgebra.domCongr k k (fullCoordinateFinsuppEquiv b))

@[simp] theorem fullChartPolynomialEquiv_character (b : Module.Basis ι ℤ E) (i : ι) :
    fullChartPolynomialEquiv k b
      (chartCharacter k (coordinateConeMonoid b Finset.univ) (b i)
        (basis_mem_fullCoordinateCone b i)) = MvPolynomial.X i := by
  have hchar : monoidChartAlgebraEquiv k (coordinateConeMonoid b Finset.univ)
      (single ⟨b i, basis_mem_fullCoordinateCone b i⟩ 1) =
      chartCharacter k (coordinateConeMonoid b Finset.univ) (b i)
        (basis_mem_fullCoordinateCone b i) := by
    apply Subtype.ext
    exact monoidChartMap_single k _ _ _
  rw [fullChartPolynomialEquiv, AlgEquiv.trans_apply, ← hchar,
    AlgEquiv.symm_apply_apply, AddMonoidAlgebra.domCongr_single,
    fullCoordinateFinsuppEquiv_basis]
  rfl

@[simp] theorem fullChartPolynomialEquiv_symm_X (b : Module.Basis ι ℤ E) (i : ι) :
    (fullChartPolynomialEquiv k b).symm (MvPolynomial.X i) =
      chartCharacter k (coordinateConeMonoid b Finset.univ) (b i)
        (basis_mem_fullCoordinateCone b i) :=
  (fullChartPolynomialEquiv k b).symm_apply_eq.mpr
    (fullChartPolynomialEquiv_character k b i).symm

def fullChartDifferentialBasis (b : Module.Basis ι ℤ E) :
    Module.Basis ι (monoidChartAlgebra k (coordinateConeMonoid b Finset.univ))
      Ω[monoidChartAlgebra k (coordinateConeMonoid b Finset.univ)⁄k] :=
  polynomialDifferentialBasis k (fullChartPolynomialEquiv k b).symm

@[simp] theorem fullChartDifferentialBasis_apply (b : Module.Basis ι ℤ E) (i : ι) :
    fullChartDifferentialBasis k b i = D k _
      (chartCharacter k (coordinateConeMonoid b Finset.univ) (b i)
        (basis_mem_fullCoordinateCone b i)) := by
  rw [fullChartDifferentialBasis, polynomialDifferentialBasis_apply,
    fullChartPolynomialEquiv_symm_X]

def unconstrainedChartEquiv (b : Module.Basis ι ℤ E) :
    monoidChartAlgebra k (coordinateConeMonoid b ∅) ≃ₐ[k] AddMonoidAlgebra k E :=
  AlgEquiv.ofBijective (Subalgebra.val _) ⟨Subtype.val_injective, by
    intro f
    refine ⟨⟨f, (mem_monoidChartAlgebra k _ f).mpr ?_⟩, rfl⟩
    intro m hm i hi
    exact (Finset.notMem_empty i hi).elim⟩

def fullChartDenominator (b : Module.Basis ι ℤ E) :
    monoidChartAlgebra k (coordinateConeMonoid b Finset.univ) :=
  chartCharacter k _ (faceDenominatorExponent b ∅ Finset.univ)
    (faceDenominatorExponent_mem b ∅ Finset.univ)

theorem laurent_isLocalization_fullChart (b : Module.Basis ι ℤ E) :
    IsLocalization.Away (fullChartDenominator k b) (AddMonoidAlgebra k E) := by
  apply (isLocalization_iff_isLocalizationMap _ _).mpr
  have hloc := coordinateChartInclusion_isLocalizationMap k b
    (Finset.empty_subset (Finset.univ : Finset ι))
  exact hloc.mulEquiv_comp (unconstrainedChartEquiv k b).toMulEquiv

/-- Localizing the actual universal differential module gives a basis of
the Laurent differential module consisting of the character differentials. -/
def laurentDifferentialBasis (b : Module.Basis ι ℤ E) :
    Module.Basis ι (AddMonoidAlgebra k E) Ω[AddMonoidAlgebra k E⁄k] := by
  let S := monoidChartAlgebra k (coordinateConeMonoid b Finset.univ)
  letI := laurent_isLocalization_fullChart k b
  exact (fullChartDifferentialBasis k b).ofIsLocalizedModule (AddMonoidAlgebra k E)
    (Submonoid.powers (fullChartDenominator k b))
    (KaehlerDifferential.map k k S (AddMonoidAlgebra k E))

@[simp] theorem laurentDifferentialBasis_apply (b : Module.Basis ι ℤ E) (i : ι) :
    laurentDifferentialBasis k b i = D k (AddMonoidAlgebra k E) (single (b i) 1) := by
  simp only [laurentDifferentialBasis, Module.Basis.ofIsLocalizedModule_apply,
    fullChartDifferentialBasis_apply, KaehlerDifferential.map_D]
  rfl

def groupCharacterUnit (m : E) : (AddMonoidAlgebra k E)ˣ where
  val := single m 1
  inv := single (-m) 1
  val_inv := by simp [AddMonoidAlgebra.one_def]
  inv_val := by simp [AddMonoidAlgebra.one_def]

@[simp] theorem groupCharacterUnit_val (m : E) :
    (groupCharacterUnit k m : AddMonoidAlgebra k E) = single m 1 := rfl

def logDifferentialBasis (b : Module.Basis ι ℤ E) :
    Module.Basis ι (AddMonoidAlgebra k E) Ω[AddMonoidAlgebra k E⁄k] :=
  (laurentDifferentialBasis k b).unitsSMul (fun i => groupCharacterUnit k (-b i))

@[simp] theorem logDifferentialBasis_apply (b : Module.Basis ι ℤ E) (i : ι) :
    logDifferentialBasis k b i = single (-b i) (1 : k) • D k (AddMonoidAlgebra k E) (single (b i) 1) := by
  simp only [logDifferentialBasis, Module.Basis.unitsSMul_apply, Units.smul_def,
    groupCharacterUnit_val, laurentDifferentialBasis_apply]

end PaperVerification.ToricCharacters
end
end Source_ToricCoordinateDifferentials
-- END ORIGINAL PaperVerification.ToricCoordinateDifferentials


-- BEGIN ORIGINAL PaperVerification.ToricLogarithmicVolume
section Source_ToricLogarithmicVolume

-- original header: module

-- original header: public import PaperVerification.ToricCoordinateDifferentials
-- original header: public import Mathlib.LinearAlgebra.Determinant
-- original header: public import Mathlib.LinearAlgebra.ExteriorPower.Basic
-- original header: public import Mathlib.LinearAlgebra.ExteriorPower.Basis

-- original header: @[expose] public section

/-!
# The logarithmic character volume form

Logarithmic differentials are defined using the universal Kähler
derivation, and additivity is proved by the Leibniz rule. An integral basis
gives their genuine Laurent-module basis. The actual top exterior power
then changes by the determinant of an integral basis change. In a smooth
polynomial chart its regular volume is the product of the coordinates
times this logarithmic volume.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open AddMonoidAlgebra KaehlerDifferential
open scoped BigOperators Classical

section Exterior

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {n : ℕ}

theorem alternating_eq_basis_determinant (b : Module.Basis (Fin n) R M)
    (f : M [⋀^Fin n]→ₗ[R] N) : f = b.det.smulRight (f b) := by
  apply b.ext_alternating
  intro v hv
  let σ : Equiv.Perm (Fin n) := Equiv.ofBijective v (Finite.injective_iff_bijective.mp hv)
  change f (b ∘ σ) = b.det (b ∘ σ) • f b
  simp only [AlternatingMap.map_perm, Module.Basis.det_self, Units.smul_def,
    Int.smul_one_eq_cast, Int.cast_smul_eq_zsmul]

/-- The actual top exterior power of a finite free module is a rank-one
module, with coefficient given by the determinant in the chosen basis. -/
def basisTopExteriorEquiv (b : Module.Basis (Fin n) R M) : (⋀[R]^n M) ≃ₗ[R] R := by
  let f : (⋀[R]^n M) →ₗ[R] R := exteriorPower.alternatingMapLinearEquiv b.det
  let w := exteriorPower.ιMulti R n b
  refine { f with invFun := fun r => r • w, left_inv := ?_, right_inv := ?_ }
  · intro x
    have hx : x ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R n (M := M))) := by
      rw [exteriorPower.ιMulti_span]
      trivial
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨v, rfl⟩
      change f (exteriorPower.ιMulti R n v) • w = exteriorPower.ιMulti R n v
      rw [show f (exteriorPower.ιMulti R n v) = b.det v from
        exteriorPower.alternatingMapLinearEquiv_apply_ιMulti b.det v]
      exact (congrArg (fun F => F v)
        (alternating_eq_basis_determinant b (exteriorPower.ιMulti R n))).symm
    · change f 0 • w = 0
      rw [map_zero, zero_smul]
    · intro x y hx hy ihx ihy
      change f (x + y) • w = x + y
      change f x • w = x at ihx
      change f y • w = y at ihy
      rw [map_add, add_smul, ihx, ihy]
    · intro r x hx ihx
      change f (r • x) • w = r • x
      change f x • w = x at ihx
      rw [map_smul, smul_eq_mul, mul_smul, ihx]
  · intro r
    change f (r • exteriorPower.ιMulti R n b) = r
    rw [map_smul, show f (exteriorPower.ιMulti R n b) = b.det b from
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti b.det b,
      Module.Basis.det_self, smul_eq_mul, mul_one]

@[simp] theorem basisTopExteriorEquiv_wedge (b : Module.Basis (Fin n) R M) (v : Fin n → M) :
    basisTopExteriorEquiv b (exteriorPower.ιMulti R n v) = b.det v :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti b.det v

@[simp] theorem basisTopExteriorEquiv_basis (b : Module.Basis (Fin n) R M) :
    basisTopExteriorEquiv b (exteriorPower.ιMulti R n b) = 1 := by
  rw [basisTopExteriorEquiv_wedge, Module.Basis.det_self]

end Exterior

variable (k : Type*) [CommRing k] {E : Type*} [AddCommGroup E] [Module ℤ E]

def logDifferential (m : E) : Ω[AddMonoidAlgebra k E⁄k] :=
  single (-m) (1 : k) • D k (AddMonoidAlgebra k E) (single m 1)

@[simp] theorem logDifferential_zero : logDifferential k (0 : E) = 0 := by
  simp [logDifferential, ← AddMonoidAlgebra.one_def]

theorem logDifferential_add (m p : E) :
    logDifferential k (m + p) = logDifferential k m + logDifferential k p := by
  have hprod : (single (m + p) (1 : k)) = single m 1 * single p 1 := by simp
  have hm : -(m + p) + m = -p := by abel
  have hp : -(m + p) + p = -m := by abel
  unfold logDifferential
  rw [hprod, Derivation.leibniz, smul_add, smul_smul, smul_smul]
  simp only [single_mul_single, one_mul, hm, hp]
  exact add_comm _ _

def logDifferentialAddHom : E →+ Ω[AddMonoidAlgebra k E⁄k] where
  toFun := logDifferential k
  map_zero' := logDifferential_zero k
  map_add' := logDifferential_add k

@[simp] theorem logDifferential_zsmul (m : E) (z : ℤ) :
    logDifferential k (z • m) = z • logDifferential k m :=
  (logDifferentialAddHom k).map_zsmul z m

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[simp] theorem logDifferentialBasis_eq (b : Module.Basis ι ℤ E) (i : ι) :
    logDifferentialBasis k b i = logDifferential k (b i) :=
  logDifferentialBasis_apply k b i

theorem logDifferential_expansion (b : Module.Basis ι ℤ E) (m : E) :
    logDifferential k m =
      ∑ i, (b.repr m i : AddMonoidAlgebra k E) • logDifferential k (b i) := by
  calc
    logDifferential k m = logDifferential k (∑ i, b.repr m i • b i) := by
      apply congrArg (logDifferential k)
      calc
        m = ∑ i, (inferInstance : Module ℤ E).smul (b.repr m i) (b i) :=
          (b.sum_repr m).symm
        _ = _ := Finset.sum_congr rfl (fun i _ =>
          int_smul_eq_zsmul (inferInstance : Module ℤ E) (b.repr m i) (b i))
    _ = ∑ i, (b.repr m i : ℤ) • logDifferential k (b i) := by
      exact (map_sum (logDifferentialAddHom k (E := E)) _ _).trans (by
        congr 1
        funext i
        exact logDifferential_zsmul k (b i) (b.repr m i))
    _ = _ := by simp only [Int.cast_smul_eq_zsmul]

theorem logDifferentialBasis_repr (b : Module.Basis ι ℤ E) (m : E) (i : ι) :
    (logDifferentialBasis k b).repr (logDifferential k m) i = (b.repr m i : AddMonoidAlgebra k E) := by
  have hrepr (j : ι) : (logDifferentialBasis k b).repr (logDifferential k (b j)) =
      Finsupp.single j 1 := by
    rw [← logDifferentialBasis_eq, Module.Basis.repr_self]
  rw [logDifferential_expansion k b m]
  simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, hrepr]
  simp [Finsupp.single_apply]

theorem character_differential_eq_smul_log (m : E) :
    D k (AddMonoidAlgebra k E) (single m 1) = single m (1 : k) • logDifferential k m := by
  rw [logDifferential, smul_smul]
  simp [← AddMonoidAlgebra.one_def]

section TopVolume

variable {n : ℕ}

def logVolume (b : Module.Basis (Fin n) ℤ E) :
    ⋀[AddMonoidAlgebra k E]^n Ω[AddMonoidAlgebra k E⁄k] :=
  exteriorPower.ιMulti (AddMonoidAlgebra k E) n (logDifferentialBasis k b)

def regularCoordinateVolume (b : Module.Basis (Fin n) ℤ E) :
    ⋀[AddMonoidAlgebra k E]^n Ω[AddMonoidAlgebra k E⁄k] :=
  exteriorPower.ιMulti (AddMonoidAlgebra k E) n
    (fun i => D k (AddMonoidAlgebra k E) (single (b i) 1))

theorem logDifferentialBasis_det (b c : Module.Basis (Fin n) ℤ E) :
    (logDifferentialBasis k b).det (logDifferentialBasis k c) =
      (b.det c : AddMonoidAlgebra k E) := by
  rw [Module.Basis.det_apply, Module.Basis.det_apply]
  have hmatrix : (logDifferentialBasis k b).toMatrix (logDifferentialBasis k c) =
      (Int.castRingHom (AddMonoidAlgebra k E)).mapMatrix (b.toMatrix c) := by
    funext i j
    change (logDifferentialBasis k b).repr (logDifferentialBasis k c j) i =
      (b.repr (c j) i : AddMonoidAlgebra k E)
    rw [logDifferentialBasis_eq, logDifferentialBasis_repr]
  rw [hmatrix, ← RingHom.map_det]
  rfl

/-- The transition factor is the genuine determinant of the unimodular
integral character change of basis. -/
theorem logVolume_change_basis (b c : Module.Basis (Fin n) ℤ E) :
    logVolume k c = (b.det c : AddMonoidAlgebra k E) • logVolume k b := by
  have h := congrArg (fun f => f (logDifferentialBasis k c))
    (alternating_eq_basis_determinant (logDifferentialBasis k b)
      (exteriorPower.ιMulti (AddMonoidAlgebra k E) n))
  change logVolume k c = (logDifferentialBasis k b).det (logDifferentialBasis k c) •
    logVolume k b at h
  rw [logDifferentialBasis_det] at h
  exact h

theorem logVolume_transition_isUnit (b c : Module.Basis (Fin n) ℤ E) :
    IsUnit (b.det c : AddMonoidAlgebra k E) :=
  (b.isUnit_det c).map (Int.castRingHom (AddMonoidAlgebra k E))

/-- In a smooth full chart the regular differential volume has precisely
one copy of every coordinate character relative to the logarithmic volume. -/
theorem regularCoordinateVolume_eq_character_logVolume (b : Module.Basis (Fin n) ℤ E) :
    regularCoordinateVolume k b = single (∑ i, b i) (1 : k) • logVolume k b := by
  unfold regularCoordinateVolume
  simp_rw [character_differential_eq_smul_log]
  rw [AlternatingMap.map_smul_univ]
  simp only [AddMonoidAlgebra.prod_single, Finset.prod_const_one]
  congr 1
  exact congrArg (exteriorPower.ιMulti (AddMonoidAlgebra k E) n)
    (funext (fun i => (logDifferentialBasis_eq k b i).symm))

end TopVolume

end PaperVerification.ToricCharacters
end
end Source_ToricLogarithmicVolume
-- END ORIGINAL PaperVerification.ToricLogarithmicVolume


