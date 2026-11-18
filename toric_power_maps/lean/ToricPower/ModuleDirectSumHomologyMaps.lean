module

public import ToricPower.ModuleDirectSumColimit
public import TauCeti.Algebra.Homology.ShortComplex.Colimit

/-!
# Homology of an unrestricted sum, with its actual inclusions

The comparison comes from the preserved coproduct cocone. This records
exactly how the homology of every coefficient complex enters the full
homology, avoiding any choice of an unrelated direct-sum isomorphism.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped Classical

namespace ToricPower.ModuleDirectSum

variable (R : Type) [CommRing R] {U : Type}
  (K : U → CochainComplex (ModuleCat.{0} R) ℕ) (q : ℕ)

/-- The homology comparison determined by the actual coproduct legs. -/
def homologySumIso :
    (complex R K).homology q ≅ ModuleCat.of R (Π₀ u : U, (K u).homology q) :=
  (isColimitOfPreserves (HomologicalComplex.homologyFunctor (ModuleCat R) (.up ℕ) q)
      (complexCoconeIsColimit R K)).coconePointUniqueUpToIso
    (sumCoconeIsColimit R
      ((Discrete.functor K) ⋙ HomologicalComplex.homologyFunctor (ModuleCat R) (.up ℕ) q))

@[reassoc]
theorem homologySumIso_inclusion (u : U) :
    HomologicalComplex.homologyMap (complexInclusion R K u) q ≫
        (homologySumIso R K q).hom =
      ModuleCat.ofHom (DFinsupp.lsingle (R := R)
        (M := fun v : U => ↑((K v).homology q)) u) :=
  (isColimitOfPreserves (HomologicalComplex.homologyFunctor (ModuleCat R) (.up ℕ) q)
    (complexCoconeIsColimit R K)).fac
      (sumCocone R ((Discrete.functor K) ⋙
        HomologicalComplex.homologyFunctor (ModuleCat R) (.up ℕ) q)) ⟨u⟩

end ToricPower.ModuleDirectSum
