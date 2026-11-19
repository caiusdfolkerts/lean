module

public import ToricPower.LinearDualHomology

/-!
# Scalar duality of a natural one-dimensional homology coefficient

A chosen homology isomorphism to the coefficient field determines the
dual cohomology isomorphism by evaluation at one. A chain map respecting
the chosen homology coefficients respects these actual dual maps as well.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace ToricPower

universe u

variable (k : Type u) [Field k]

/-- Scalar duality of a specified coefficient isomorphism, with its
ordinary evaluation-at-one normalization. -/
def scalarDualHomologyClassIso (K : ChainComplex (ModuleCat.{u} k) ℕ)
    (q : ℕ) (e : K.homology q ≅ ModuleCat.of k k) :
    (scalarDualComplex k K).homology q ≅ ModuleCat.of k k :=
  scalarDualHomologyIso k K q ≪≫ (scalarDual k).mapIso e.symm.op ≪≫ scalarDualUnitIso k

/-- The dual coefficient maps are natural for every genuine chain map
preserving the specified homology coefficient. -/
theorem scalarDualHomologyClassIso_natural
    {K L : ChainComplex (ModuleCat.{u} k) ℕ} (f : K ⟶ L) (q : ℕ)
    (eK : K.homology q ≅ ModuleCat.of k k) (eL : L.homology q ≅ ModuleCat.of k k)
    (compatible : HomologicalComplex.homologyMap f q ≫ eL.hom = eK.hom) :
    HomologicalComplex.homologyMap (scalarDualMap k f) q ≫
        (scalarDualHomologyClassIso k K q eK).hom =
      (scalarDualHomologyClassIso k L q eL).hom := by
  have inverseSquare : eK.inv ≫ HomologicalComplex.homologyMap f q = eL.inv := by
    apply (cancel_mono eL.hom).mp
    rw [Category.assoc, compatible, Iso.inv_hom_id, Iso.inv_hom_id]
  simp only [scalarDualHomologyClassIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.op_hom, Iso.symm_hom]
  rw [← Category.assoc, scalarDualHomologyIso_natural, Category.assoc,
    ← Functor.map_comp_assoc, ← op_comp, inverseSquare]

end ToricPower
