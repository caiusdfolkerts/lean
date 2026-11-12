module

public import ToricPower.FiniteFunctorTotal

/-!
# The actual coordinates of the finite functor total

These formulas retain the original horizontal arrows of the
complex-valued functor and the signed vertical differential. They are
used for the second, horizontal exactness argument.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open HomologicalComplex

namespace ToricPower.FunctorTotal

universe u v w z

variable {A : Type u} [Category.{v} A] [Preadditive A]
  {B : Type w} [Category.{z} B] [Preadditive B] [HasFiniteBiproducts B]
  (Φ : A ⥤ CochainComplex B ℕ) [Φ.Additive]
  {width : ℕ} (K : CochainComplex A ℤ)
  {k : Type} [CommRing k] (F : B ⥤ ModuleCat.{0} k) [F.Additive]

theorem mapped_transportedHorizontal_zero_iff
    (x y : ℤ) (p q : ℕ) (equality : x = y)
    (z : F.obj ((Φ.obj (K.X x)).X p)) :
    F.map (transportedHorizontal Φ K x y p q equality) z = 0 ↔
      F.map ((Φ.obj (K.X x)).d p q) z = 0 := by
  subst equality
  simp [transportedHorizontal]

/-- There is exactly one incoming horizontal matrix entry at a positive
horizontal degree; every other summand is literally zero. -/
theorem mapped_off_project (a : ℤ) (p q : Fin width) (next : p.val+1=q.val)
    (z : F.obj (FiniteTotal.term (row Φ K (width := width)) a)) :
    F.map (biproduct.π (fun q : Fin width => (row Φ K q).X (a+1)) q)
      (F.map (off Φ K a) z) =
    F.map (offEntry Φ K a p q)
      (F.map (biproduct.π (fun p : Fin width => (row Φ K p).X a) p) z) := by
  classical
  have h := congrArg (fun f : FiniteTotal.term (row Φ K (width := width)) a ⟶
      (row Φ K q).X (a+1) => F.map f z)
    (biproduct.matrix_π (offEntry Φ K a) q)
  simp only [off,F.map_comp,ModuleCat.comp_apply] at h ⊢
  rw [h]
  rw [biproduct.desc_eq]
  simp only [F.map_sum,F.map_comp,ModuleCat.hom_sum,LinearMap.sum_apply,
    ModuleCat.comp_apply]
  apply Finset.sum_eq_single p
  · intro r _ different
    have notNext : ¬r.val+1=q.val := by
      intro hr
      apply different
      exact Fin.ext (by omega)
    simp only [offEntry,dif_neg notNext,F.map_zero,ModuleCat.hom_zero,LinearMap.zero_apply]
  · simp

/-- The differential of the actual total is the signed vertical term
plus the one original horizontal predecessor term. -/
theorem mapped_total_d_project (a : ℤ) (p q : Fin width) (next : p.val+1=q.val)
    (z : F.obj ((total Φ width K).X a)) :
    F.map (biproduct.π (fun q : Fin width => (row Φ K q).X (a+1)) q)
      (F.map ((total Φ width K).d a (a+1)) z) =
    F.map ((row Φ K q).d a (a+1))
      (F.map (biproduct.π (fun q : Fin width => (row Φ K q).X a) q) z) +
    F.map (offEntry Φ K a p q)
      (F.map (biproduct.π (fun p : Fin width => (row Φ K p).X a) p) z) := by
  change F.map (biproduct.π (fun q : Fin width => (row Φ K q).X (a+1)) q)
    (F.map (CochainComplex.of.d (FiniteTotal.term (row Φ K (width := width)))
      (FiniteTotal.differential (row Φ K) (off Φ K)) a (a+1)) z) = _
  rw [CochainComplex.of_d]
  have h := congrArg (fun f : FiniteTotal.term (row Φ K (width := width)) a ⟶
      (row Φ K q).X (a+1) => F.map f z)
    (biproduct.map_π (fun q : Fin width => (row Φ K q).d a (a+1)) q)
  simp only [F.map_comp,ModuleCat.comp_apply] at h
  simp only [FiniteTotal.differential,F.map_add,ModuleCat.hom_add,LinearMap.add_apply,map_add]
  rw [mapped_off_project Φ K F a p q next z]
  exact congrArg (fun x => x + F.map (offEntry Φ K a p q)
    (F.map (biproduct.π (fun p : Fin width => (row Φ K p).X a) p) z)) h

/-- An off-diagonal matrix entry of the full differential is exactly the
original horizontal entry. -/
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

/-- The consecutive entry with an explicitly named target degree.
This formulation keeps all arithmetic transports at their actual
source and target objects. -/
theorem total_d_entry_next (a b : ℤ) (step : a+1=b)
    (p q : Fin width) (next : p.val+1=q.val) :
    biproduct.ι (fun p : Fin width => (row Φ K p).X a) p ≫
      (total Φ width K).d a b ≫
      biproduct.π (fun q : Fin width => (row Φ K q).X b) q =
    transportedHorizontal Φ K (a + -(p.val : ℤ)) (b + -(q.val : ℤ))
      p.val q.val (by omega) := by
  subst b
  have different : p ≠ q := by
    intro h
    have same := congrArg Fin.val h
    omega
  have entry := total_d_entry_ne Φ K a p q different
  simp only [offEntry,dif_pos next] at entry
  exact entry

end ToricPower.FunctorTotal

end
