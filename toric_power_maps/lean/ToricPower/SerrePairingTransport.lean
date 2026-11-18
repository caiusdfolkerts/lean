module

public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Transporting an actual Serre pairing along object isomorphisms

These elementary formulas keep the maps in both variables explicit.
In particular, they preserve the direction of scalar duality for an
arbitrary, potentially infinite-dimensional, source object.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace ToricPower.SerrePairing

universe u v r
variable (k : Type r) [Field k]
variable {D : Type u} [Category.{v} D] [Preadditive D] [Linear k D]

def transport {E₀ G₀ P₀ E G P : D}
    (pairing : (E₀ ⟶ G₀) ≃ₗ[k] Module.Dual k (P₀ ⟶ E₀))
    (sourceIso : E₀ ≅ E) (targetIso : G₀ ≅ G) (representingIso : P ≅ P₀) :
    (E ⟶ G) ≃ₗ[k] Module.Dual k (P ⟶ E) :=
  (Linear.homCongr k sourceIso.symm targetIso.symm).trans
    (pairing.trans (Linear.homCongr k representingIso sourceIso.symm).dualMap)

theorem transport_apply {E₀ G₀ P₀ E G P : D}
    (pairing : (E₀ ⟶ G₀) ≃ₗ[k] Module.Dual k (P₀ ⟶ E₀))
    (sourceIso : E₀ ≅ E) (targetIso : G₀ ≅ G) (representingIso : P ≅ P₀)
    (f : E ⟶ G) (g : P ⟶ E) :
    transport k pairing sourceIso targetIso representingIso f g =
      pairing ((sourceIso.hom ≫ f) ≫ targetIso.inv)
        ((representingIso.inv ≫ g) ≫ sourceIso.inv) := rfl

theorem transport_source_naturality
    {E₀ F₀ G₀ P₀ E F G P : D}
    (pairingE : (E₀ ⟶ G₀) ≃ₗ[k] Module.Dual k (P₀ ⟶ E₀))
    (pairingF : (F₀ ⟶ G₀) ≃ₗ[k] Module.Dual k (P₀ ⟶ F₀))
    (sourceE : E₀ ≅ E) (sourceF : F₀ ≅ F)
    (targetIso : G₀ ≅ G) (representingIso : P ≅ P₀)
    (natural : ∀ (a : E₀ ⟶ F₀) (f : F₀ ⟶ G₀) (g : P₀ ⟶ E₀),
      pairingE (a ≫ f) g = pairingF f (g ≫ a))
    (a : E ⟶ F) (f : F ⟶ G) (g : P ⟶ E) :
    transport k pairingE sourceE targetIso representingIso (a ≫ f) g =
      transport k pairingF sourceF targetIso representingIso f (g ≫ a) := by
  simpa only [transport_apply, Category.assoc, Iso.inv_hom_id_assoc] using
    natural ((sourceE.hom ≫ a) ≫ sourceF.inv)
      ((sourceF.hom ≫ f) ≫ targetIso.inv)
      ((representingIso.inv ≫ g) ≫ sourceE.inv)

theorem transport_target_naturality
    {E₀ J₀ K₀ PJ₀ PK₀ E J K PJ PK : D}
    (pairingJ : (E₀ ⟶ J₀) ≃ₗ[k] Module.Dual k (PJ₀ ⟶ E₀))
    (pairingK : (E₀ ⟶ K₀) ≃ₗ[k] Module.Dual k (PK₀ ⟶ E₀))
    (sourceIso : E₀ ≅ E) (targetJ : J₀ ≅ J) (targetK : K₀ ≅ K)
    (representingJ : PJ ≅ PJ₀) (representingK : PK ≅ PK₀)
    (a : J ⟶ K) (b : PJ ⟶ PK) (modelMap : PJ₀ ⟶ PK₀)
    (comparison : representingJ.inv ≫ b = modelMap ≫ representingK.inv)
    (natural : ∀ (f : E₀ ⟶ J₀) (g : PK₀ ⟶ E₀),
      pairingK (f ≫ (targetJ.hom ≫ a) ≫ targetK.inv) g =
        pairingJ f (modelMap ≫ g))
    (f : E ⟶ J) (g : PK ⟶ E) :
    transport k pairingK sourceIso targetK representingK (f ≫ a) g =
      transport k pairingJ sourceIso targetJ representingJ f (b ≫ g) := by
  have h := natural ((sourceIso.hom ≫ f) ≫ targetJ.inv)
    ((representingK.inv ≫ g) ≫ sourceIso.inv)
  simp only [Category.assoc, Iso.inv_hom_id_assoc] at h
  simp only [transport_apply, Category.assoc]
  rw [← Category.assoc representingJ.inv b, comparison]
  simpa only [Category.assoc] using h

end ToricPower.SerrePairing

end
