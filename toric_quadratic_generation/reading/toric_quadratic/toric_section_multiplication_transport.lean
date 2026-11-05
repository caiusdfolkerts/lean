module

public import PaperVerification.ToricFanSectionMultiplication

@[expose] public section

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
