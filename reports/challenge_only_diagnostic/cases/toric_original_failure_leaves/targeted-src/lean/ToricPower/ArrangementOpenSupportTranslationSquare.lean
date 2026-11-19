module

public import ToricPower.ArrangementOpenSupportTranslationCoordinates

/-!
# Naturality of translated extension on finite cell supports

The square uses the original relative cellular maps. Its equality is
verified in the original characteristic-cell bases, including the zero
coefficients outside the translated support.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Topology Set
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (k : Type) [Field k]
  {U₀ U₁ V₀ V₁ : OpenCellSupport A} (z : Fin n → ℤ)
  (hU : U₀ ≤ U₁) (hV : V₀ ≤ V₁)
  (h₀ : translatedRegion (U₀.val : Set (Fin n → ℝ)) (latticeLift z) ⊆ V₀.val)
  (h₁ : translatedRegion (U₁.val : Set (Fin n → ℝ)) (latticeLift z) ⊆ V₁.val)
  [finiteU₀ : ∀ q, Finite (OpenSupportCell A U₀ q)]
  [finiteU₁ : ∀ q, Finite (OpenSupportCell A U₁ q)]
  [finiteV₀ : ∀ q, Finite (OpenSupportCell A V₀ q)]
  [finiteV₁ : ∀ q, Finite (OpenSupportCell A V₁ q)]

/-- The actual translated-extension maps commute with support inclusions. -/
theorem openSupportCochainTranslation_square :
    openSupportCochainExtension A k hU ≫ openSupportCochainTranslation A z h₁ k =
      openSupportCochainTranslation A z h₀ k ≫ openSupportCochainExtension A k hV := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply (openSupportCochainCoordinates A k V₁ q).injective
  change openSupportCochainCoordinates A k V₁ q
      ((openSupportCochainTranslation A z h₁ k).f q
        ((openSupportCochainExtension A k hU).f q φ)) =
    openSupportCochainCoordinates A k V₁ q
      ((openSupportCochainExtension A k hV).f q
        ((openSupportCochainTranslation A z h₀ k).f q φ))
  rw [openSupportCochainTranslation_coordinates A z h₁ k q,
    openSupportCochainExtension_coordinates A k hU q,
    openSupportCochainExtension_coordinates A k hV q,
    openSupportCochainTranslation_coordinates A z h₀ k q,
    ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  congr 1

end ToricPower.IntegralArrangement
