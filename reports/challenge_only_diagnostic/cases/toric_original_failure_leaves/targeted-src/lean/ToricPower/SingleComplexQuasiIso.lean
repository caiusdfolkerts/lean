module

public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Homology of an actual quasi-isomorphism to a single complex

These small generic consequences keep large geometric complexes opaque
while using their already established quasi-isomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]
  {K : CochainComplex C ℕ} {M : C} {n : ℕ}
  (f : K ⟶ (HomologicalComplex.single C (.up ℕ) n).obj M) [QuasiIso f]

/-- The actual induced top-homology isomorphism. -/
def homologyIsoOfQuasiIsoToSingle : K.homology n ≅ M :=
  asIso (HomologicalComplex.homologyMap f n) ≪≫
    HomologicalComplex.singleObjHomologySelfIso (.up ℕ) n M

include f in
/-- All other actual homology groups vanish. -/
theorem isZeroHomologyOfQuasiIsoToSingle (q : ℕ) (different : q ≠ n) :
    IsZero (K.homology q) :=
  (HomologicalComplex.isZero_single_obj_homology (.up ℕ) n M q different).of_iso
    (asIso (HomologicalComplex.homologyMap f q))

end ToricPower
