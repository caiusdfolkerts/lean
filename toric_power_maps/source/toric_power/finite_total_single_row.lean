module

public import ToricPower.FiniteTwistedTotal

/-! # The canonical projection onto the unique nonzero total row -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace ToricPower.FiniteTotal

universe u v

variable {B : Type u} [Category.{v} B] [Preadditive B] [HasFiniteBiproducts B]
  {width : ℕ} (rows : Fin width → CochainComplex B ℤ)
  (off : ∀ a : ℤ, term rows a ⟶ term rows (a+1))
  (coherent : Coherent rows off) (zeroOff : ∀ a, off a = 0)
  (q : Fin width)

/-- The original biproduct projection is a chain map when the
horizontal part vanishes. -/
def rowProjection : complex rows off coherent ⟶ rows q where
  f a := biproduct.π (fun r => (rows r).X a) q
  comm' a b related := by
    have step : a+1=b := related
    subst b
    change biproduct.π (fun r => (rows r).X a) q ≫ (rows q).d a (a+1) =
      CochainComplex.of.d (term rows) (differential rows off) a (a+1) ≫
        biproduct.π (fun r => (rows r).X (a+1)) q
    rw [CochainComplex.of_d,differential,zeroOff,add_zero]
    exact (biproduct.map_π (fun r => (rows r).d a (a+1)) q).symm

/-- Its original biproduct inclusion is a chain map as well. -/
def rowInclusion : rows q ⟶ complex rows off coherent where
  f a := biproduct.ι (fun r => (rows r).X a) q
  comm' a b related := by
    have step : a+1=b := related
    subst b
    change biproduct.ι (fun r => (rows r).X a) q ≫
        CochainComplex.of.d (term rows) (differential rows off) a (a+1) =
      (rows q).d a (a+1) ≫ biproduct.ι (fun r => (rows r).X (a+1)) q
    rw [CochainComplex.of_d,differential,zeroOff,add_zero]
    exact biproduct.ι_map (fun r => (rows r).d a (a+1)) q

/-- Removing actual zero summands identifies the entire finite total
with its unique surviving row. Both maps are the original projections
and inclusions, so their naturality can be checked on the same maps. -/
def singleRowIso
    (otherZero : ∀ r : Fin width, r ≠ q → ∀ a : ℤ, IsZero ((rows r).X a)) :
    complex rows off coherent ≅ rows q where
  hom := rowProjection rows off coherent zeroOff q
  inv := rowInclusion rows off coherent zeroOff q
  hom_inv_id := by
    apply HomologicalComplex.Hom.ext
    funext a
    change biproduct.π (fun r => (rows r).X a) q ≫
      biproduct.ι (fun r => (rows r).X a) q = 𝟙 _
    apply biproduct.hom_ext
    intro r
    by_cases same : r = q
    · subst r
      simp only [Category.assoc,biproduct.ι_π_self,Category.comp_id,Category.id_comp]
    · exact (otherZero r same a).eq_of_tgt _ _
  inv_hom_id := by
    apply HomologicalComplex.Hom.ext
    funext a
    exact biproduct.ι_π_self (fun r => (rows r).X a) q

end ToricPower.FiniteTotal

end
