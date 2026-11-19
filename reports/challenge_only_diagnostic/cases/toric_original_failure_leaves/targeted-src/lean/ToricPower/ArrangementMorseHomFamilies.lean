module

public import ToricPower.ArrangementMorseHomPresentation

/-! # Morse presentation transport before evaluating a family of complexes -/

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance 2000] Abelian.toPreadditive
attribute [local instance 2000] Preadditive.preadditiveHasZeroMorphisms

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)
  (c : UniversalIncidenceObject A) (region : Set (Fin n → ℝ))
  {C : Type*} [Category.{0} C] [Preadditive C] [Linear ℂ C]

theorem universalLocalMorse_complexHom_all_acyclic_iff
    (P : (UniversalIncidenceObject A)ᵒᵖ ⥤ C)
    [canonicalAdditive : (Cellular.complexHomDiagram P).Additive]
    {T : Type*} (family : T → CochainComplex C ℤ) :
    (∀ t : T, ((universalLocalMorse A ℂ c region).obj
      (((Cellular.complexHomDiagram P).mapHomologicalComplex (.up ℤ)).obj (family t))).Acyclic) ↔
    ∀ t : T, ((universalLocalMorse A ℂ c region).obj
      (((Cellular.homDiagram ℂ P).mapHomologicalComplex (.up ℤ)).obj (family t))).Acyclic :=
  forall_congr' (fun t => universalLocalMorse_complexHom_acyclic_iff A c region P
    (canonicalAdditive := canonicalAdditive) (family t))

end ToricPower.IntegralArrangement
end
