module

public import Recovery.Unimodular.GraphicSectionRing.CanonicalCartierValues

/-!
# Coherence with canonical ordinary tensor-power multiplication

Both maps agree on the actual powers of every local frame. The source is
itself a genuine fractional line bundle, so the local-frame extensionality
theorem upgrades this to equality of the entire sheaf morphisms. The
canonical multiplication was defined independently from the ordinary
monoidal associator and unitor.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

universe u
namespace Unimodular.GraphicSectionRing.CanonicalPowers

open AlgebraicGeometry CategoryTheory Opposite
open PaperVerification.ToricSchemes

variable {X : Scheme.{u}} [IsIntegral X]

/-- The independently defined canonical tensor-power multiplication is
intertwined by the actual Cartier power comparisons in every pair of degrees. -/
theorem multiplyIso_comp_cartierPowerIso (D : CartierData X) (i j : ℕ) :
    (multiplyIso D.sheaf i j).hom ≫ (D.tensorSheafNsmulIso (i + j)).hom =
      (sourceCartierIso D i j).hom := by
  let C := D.localCocycle
  let b (a : (C.pow (i + j)).index) (V : X.Opens)
      (hVa : V ≤ (C.pow (i + j)).openSet a) :
      Γ(tensorSheaf (tensorSheafPower D.sheaf i) (tensorSheafPower D.sheaf j), V) :=
    pure _ _ V
      (purePower D.sheaf V (presentationFrame D a V hVa) i)
      (purePower D.sheaf V (presentationFrame D a V hVa) j)
  apply hom_ext_of_frame (C.pow (i + j)) (C.pow (i + j)).toCartierData
    (sourceCartierIso D i j) b
  · intro a V hVa hV
    letI := hV
    change (C.pow (i + j)).toCartierData.sectionValue V
      ((sourceCartierIso D i j).hom.app V
        (pure _ _ V
          (purePower D.sheaf V (presentationFrame D a V hVa) i)
          (purePower D.sheaf V (presentationFrame D a V hVa) j))) =
      (C.generator a : X.functionField) ^ (i + j)
    rw [sourceCartierIso_purePower_value, presentationFrame_value]
  · intro a V hVa
    classical
    by_cases hV : Nonempty V
    · letI := hV
      apply (C.pow (i + j)).toCartierData.sectionValue_injective V
      change (C.pow (i + j)).toCartierData.sectionValue V
        ((D.tensorSheafNsmulIso (i + j)).hom.app V
          ((multiplyIso D.sheaf i j).hom.app V
            (pure _ _ V
              (purePower D.sheaf V (presentationFrame D a V hVa) i)
              (purePower D.sheaf V (presentationFrame D a V hVa) j)))) =
        (C.pow (i + j)).toCartierData.sectionValue V
          ((sourceCartierIso D i j).hom.app V
            (pure _ _ V
              (purePower D.sheaf V (presentationFrame D a V hVa) i)
              (purePower D.sheaf V (presentationFrame D a V hVa) j)))
      rw [multiplyIso_purePower, cartierPowerIso_purePower_value,
        sourceCartierIso_purePower_value]
    · have hbot : V = ⊥ := by
        apply le_antisymm
        · intro x hx
          exact False.elim (hV ⟨⟨x, hx⟩⟩)
        · exact bot_le
      letI := regularSections_subsingleton_of_empty X V hbot
      letI := Module.subsingleton Γ(X, V) Γ((C.pow (i + j)).toCartierData.sheaf, V)
      exact Subsingleton.elim _ _

/-- Equality of the actual sheaf isomorphisms, not just their abstract
isomorphism classes or dimensions of section spaces. -/
theorem multiplyIso_eq_cartierTransport (D : CartierData X) (i j : ℕ) :
    multiplyIso D.sheaf i j =
      sourceCartierIso D i j ≪≫ (D.tensorSheafNsmulIso (i + j)).symm := by
  apply Iso.ext
  apply (cancel_mono (D.tensorSheafNsmulIso (i + j)).hom).mp
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id] using multiplyIso_comp_cartierPowerIso D i j

#print axioms multiplyIso_comp_cartierPowerIso
#print axioms multiplyIso_eq_cartierTransport

end Unimodular.GraphicSectionRing.CanonicalPowers

#check Unimodular.GraphicSectionRing.CanonicalPowers.multiplyIso_eq_cartierTransport
