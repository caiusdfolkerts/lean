module

public import ToricPower.CellularHomotopyInverseComparison
public import ToricPower.CellularFiniteDerivedSerre
public import ToricPower.SerrePairingDerivedNaturality
public import ToricPower.SerrePairingDerivedTargetNaturality
public import ToricPower.SerrePairingTransport

/-!
# A signed inverse-Serre pairing on the actual finite incidence-derived category

The representing functor is constructed through the fully faithful
K-injective homotopy localization. Its value is compared with the actual
finite inverse-Nakayama complex. The other object is completely
unrestricted in the unbounded derived category. Both morphism
naturalities retain the genuine functor map, so no reflexivity
assumption is placed on the unrestricted Hom spaces.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CochainComplex

namespace ToricPower.Cellular

universe u w
variable (k : Type u) [Field k] {C : Type u} [Category.{u} C]
  [Finite C] [∀ c d : C, Finite (c ⟶ d)]
  [HasDerivedCategory.{w} (C ⥤ ModuleCat.{u} k)]

attribute [local instance 2000] Abelian.toPreadditive
attribute [local instance 2000] Preadditive.preadditiveHasZeroMorphisms

/-- The dual is on maps out of the representing object, not on maps
from an arbitrary object into the finite coefficient. -/
def homotopyInverseSerreEquiv
    (G : FiniteDerivedDiagrams k (C := C))
    (E : DerivedCategory (C ⥤ ModuleCat.{u} k)) :
    (E ⟶ G.obj) ≃ₗ[k]
      Module.Dual k ((finiteInverseNakayama k).obj G ⟶ E) :=
  SerrePairing.transport k
    (sealedModelDerivedSerreEquiv k (finiteChosenModel k G)
      (DerivedCategory.Q.objPreimage E))
    (DerivedCategory.Q.objObjPreimageIso E) (finiteChosenModel k G).iso
      (finiteInversePairingModelIso k G)

theorem homotopyInverseSerreEquiv_source_naturality
    (G : FiniteDerivedDiagrams k (C := C))
    {E F : DerivedCategory (C ⥤ ModuleCat.{u} k)}
    (a : E ⟶ F) (f : F ⟶ G.obj)
    (g : (finiteInverseNakayama k).obj G ⟶ E) :
    homotopyInverseSerreEquiv k G E (a ≫ f) g =
      homotopyInverseSerreEquiv k G F f (g ≫ a) := by
  apply SerrePairing.transport_source_naturality
  intro a' f' g'
  let M := finiteChosenModel k G
  exact SerrePairing.finiteDerivedSerreEquiv_source_naturality k (sealedInverseNakayama k)
    M.complex (fun q => sealedFiniteInjectivePairing k (M.complex.X q))
    (fun p q => sealedFiniteInjectivePairing_compatible k (M.complex.X p) (M.complex.X q)
      (M.complex.d p q))
    (Finset.Icc M.lower M.upper)
    (boundedComplex_isZero_outside_interval k M.complex M.lower M.upper) a' f' g'

/-- Every finite-side derived map is lifted to an actual chain map into
the K-injective target, and the lift is proved to induce the functor map. -/
theorem homotopyInverseSerreEquiv_target_naturality
    {X Y : FiniteDerivedDiagrams k (C := C)}
    (a : X ⟶ Y) (E : DerivedCategory (C ⥤ ModuleCat.{u} k))
    (f : E ⟶ X.obj) (g : (finiteInverseNakayama k).obj Y ⟶ E) :
    homotopyInverseSerreEquiv k Y E (f ≫ a.hom) g =
      homotopyInverseSerreEquiv k X E f ((finiteInverseNakayama k).map a ≫ g) := by
  let M := finiteChosenModel k X
  let N := finiteChosenModel k Y
  obtain ⟨h, lifts⟩ := derived_Q_map_surjective_of_kInjective k M.complex N.complex
    ((M.iso.hom ≫ a.hom) ≫ N.iso.inv)
  unfold homotopyInverseSerreEquiv
  apply SerrePairing.transport_target_naturality k _ _ _ _ _ _ _
    a.hom ((finiteInverseNakayama k).map a)
    (DerivedCategory.Q.map (((sealedInverseNakayama k).mapHomologicalComplex (.up ℤ)).map h))
    (finiteInversePairingModelIso_inv_naturality k a h lifts)
  intro f' g'
  have equation := SerrePairing.finiteDerivedSerreEquiv_target_chain_naturality k
    (sealedInverseNakayama k) M.complex N.complex
    (fun q => sealedFiniteInjectivePairing k (M.complex.X q))
    (fun q => sealedFiniteInjectivePairing k (N.complex.X q))
    (fun p q => sealedFiniteInjectivePairing_compatible k (M.complex.X p) (M.complex.X q)
      (M.complex.d p q))
    (fun p q => sealedFiniteInjectivePairing_compatible k (N.complex.X p) (N.complex.X q)
      (N.complex.d p q)) h
    (fun q => sealedFiniteInjectivePairing_compatible k (M.complex.X q) (N.complex.X q) (h.f q))
    (Finset.Icc M.lower M.upper)
    (boundedComplex_isZero_outside_interval k M.complex M.lower M.upper)
    (Finset.Icc N.lower N.upper)
    (boundedComplex_isZero_outside_interval k N.complex N.lower N.upper)
    (DerivedCategory.Q.objPreimage E) f' g'
  simpa only [sealedModelDerivedSerreEquiv, lifts, Category.assoc] using equation

end ToricPower.Cellular
end
