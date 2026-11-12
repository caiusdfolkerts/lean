module

public import ToricPower.ModuleDirectSumComplex

/-!
# The actual coproduct cocone of a family of complexes

The literal dependent finitely supported sum has its canonical chain
inclusions and satisfies the coproduct universal property degreewise.
This connects categorical colimit comparisons to the scalar-linear
homology comparison of `ModuleDirectSumComplex`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped Classical

namespace ToricPower.ModuleDirectSum

variable (R : Type) [CommRing R] {I : Type}
  (K : I → CochainComplex (ModuleCat.{0} R) ℕ)

/-- Inclusion of every full coefficient complex into the unrestricted sum. -/
def complexInclusion (i : I) : K i ⟶ complex R K where
  f q := ModuleCat.ofHom
    (DFinsupp.lsingle (R := R) (M := fun j : I => ↑((K j).X q)) i)
  comm' q r _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change DFinsupp.mapRange.linearMap (fun j : I => ((K j).d q r).hom)
        (DFinsupp.single i x) = DFinsupp.single i ((K i).d q r x)
    simp only [DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange_single]

def complexCocone : Cocone (Discrete.functor K) where
  pt := complex R K
  ι := Discrete.natTrans (fun i => complexInclusion R K i.as)

/-- The genuine chain inclusions exhibit the literal sum complex as
the categorical coproduct, with no bound on its indexing family. -/
def complexCoconeIsColimit : IsColimit (complexCocone R K) := by
  apply HomologicalComplex.isColimitOfEval
  intro q
  exact IsColimit.ofIsoColimit
    (sumCoconeIsColimit R
      ((Discrete.functor K) ⋙ HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℕ) q))
    (Cocone.ext (Iso.refl _) (fun _ => by exact Category.comp_id _))

def complexColimitIso : complex R K ≅ colimit (Discrete.functor K) :=
  (complexCoconeIsColimit R K).coconePointUniqueUpToIso
    (colimit.isColimit (Discrete.functor K))

@[reassoc]
theorem complexColimitIso_inclusion (i : I) :
    complexInclusion R K i ≫ (complexColimitIso R K).hom =
      colimit.ι (Discrete.functor K) ⟨i⟩ :=
  (complexCoconeIsColimit R K).fac (colimit.cocone _) ⟨i⟩

end ToricPower.ModuleDirectSum
