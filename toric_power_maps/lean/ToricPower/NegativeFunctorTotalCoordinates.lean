module

public import ToricPower.NegativeFunctorTotal

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive HomologicalComplex

namespace ToricPower.NegativeFunctorTotal

universe u v w z
variable {A : Type u} [Category.{v} A] [Preadditive A]
  {B : Type w} [Category.{z} B] [Preadditive B] [HasFiniteBiproducts B]
  (Φ : A ⥤ ChainComplex B ℕ) [Φ.Additive]
  {width : ℕ} (K : CochainComplex A ℤ)

theorem total_d_entry_ne (a : ℤ) (p q : Fin width) (different : p ≠ q) :
    biproduct.ι (fun p : Fin width => (row Φ K p).X a) p ≫
      (total Φ width K).d a (a+1) ≫
      biproduct.π (fun q : Fin width => (row Φ K q).X (a+1)) q =
    offEntry Φ K a p q := by
  change biproduct.ι (fun p : Fin width => (row Φ K p).X a) p ≫
      CochainComplex.of.d (FiniteTotal.term (row Φ K (width := width)))
      (FiniteTotal.differential (row Φ K) (off Φ K)) a (a+1) ≫
      biproduct.π (fun q : Fin width => (row Φ K q).X (a+1)) q = _
  rw [CochainComplex.of_d]
  simp only [FiniteTotal.differential,FiniteTotal.diagonal,off,comp_add,add_comp,
    Category.assoc,biproduct.map_π,biproduct.ι_map_assoc,
    biproduct.ι_matrix_assoc,biproduct.lift_π]
  rw [← Category.assoc,biproduct.ι_π_ne _ different]
  simp

theorem total_d_entry_next (a b : ℤ) (step : a+1=b)
    (p q : Fin width) (next : chainDegree p=chainDegree q+1) :
    biproduct.ι (fun p : Fin width => (row Φ K p).X a) p ≫
      (total Φ width K).d a b ≫
      biproduct.π (fun q : Fin width => (row Φ K q).X b) q =
    transportedHorizontal Φ K (a + (chainDegree p : ℤ)) (b + (chainDegree q : ℤ))
      (chainDegree p) (chainDegree q) (by omega) := by
  subst b
  have different : p ≠ q := by
    intro h
    subst q
    omega
  have entry := total_d_entry_ne Φ K a p q different
  simp only [offEntry,dif_pos next] at entry
  exact entry

end ToricPower.NegativeFunctorTotal

end

