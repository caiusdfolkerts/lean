module

public import ToricPower.FiniteTwistedTotal
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open HomologicalComplex

namespace ToricPower.NegativeFunctorTotal

universe u v w z

variable {A : Type u} [Category.{v} A] [Preadditive A]
  {B : Type w} [Category.{z} B] [Preadditive B] [HasFiniteBiproducts B]
  (Φ : A ⥤ ChainComplex B ℕ) [Φ.Additive]

abbrev degree (q : ℕ) : A ⥤ B := Φ ⋙ HomologicalComplex.eval B (.down ℕ) q

abbrev chainDegree {width : ℕ} (q : Fin width) : ℕ := q.rev.val

abbrev row {width : ℕ} (K : CochainComplex A ℤ) (q : Fin width) :
    CochainComplex B ℤ :=
  (CategoryTheory.shiftFunctor (CochainComplex B ℤ) (chainDegree q : ℤ)).obj
    (((degree Φ (chainDegree q)).mapHomologicalComplex (.up ℤ)).obj K)

def transportedHorizontal (K : CochainComplex A ℤ)
    (x y : ℤ) (p q : ℕ) (equality : x = y) :
    (Φ.obj (K.X x)).X p ⟶ (Φ.obj (K.X y)).X q :=
  (Φ.obj (K.X x)).d p q ≫
    eqToHom (congrArg (fun a : ℤ => (Φ.obj (K.X a)).X q) equality)

theorem transportedHorizontal_comp (K : CochainComplex A ℤ)
    (x y z : ℤ) (p q r : ℕ) (first : x = y) (second : y = z) :
    transportedHorizontal Φ K x y p q first ≫
      transportedHorizontal Φ K y z q r second = 0 := by
  subst first
  subst second
  simp [transportedHorizontal]

theorem transportedHorizontal_vertical (K : CochainComplex A ℤ)
    (x x' y y' : ℤ) (p q : ℕ) (first : x = y) (second : x' = y') :
    (Φ.map (K.d x x')).f p ≫ transportedHorizontal Φ K x' y' p q second =
      transportedHorizontal Φ K x y p q first ≫ (Φ.map (K.d y y')).f q := by
  subst first
  subst second
  simpa only [transportedHorizontal,eqToHom_refl,Category.comp_id] using
    (Φ.map (K.d x x')).comm p q

def offEntry {width : ℕ} (K : CochainComplex A ℤ) (a : ℤ) (p q : Fin width) :
    (row Φ K p).X a ⟶ (row Φ K q).X (a+1) :=
  if next : chainDegree p = chainDegree q+1 then
    transportedHorizontal Φ K (a + (chainDegree p : ℤ))
      (a+1 + (chainDegree q : ℤ)) (chainDegree p) (chainDegree q) (by omega)
  else 0

def off {width : ℕ} (K : CochainComplex A ℤ) (a : ℤ) :
    FiniteTotal.term (row Φ K (width := width)) a ⟶
      FiniteTotal.term (row Φ K (width := width)) (a+1) :=
  biproduct.matrix (offEntry Φ K a)

theorem offEntry_comp {width : ℕ} (K : CochainComplex A ℤ) (a : ℤ)
    (p q r : Fin width) : offEntry Φ K a p q ≫ offEntry Φ K (a+1) q r = 0 := by
  classical
  unfold offEntry
  split_ifs <;> try simp only [zero_comp,comp_zero]
  exact transportedHorizontal_comp Φ K _ _ _ _ _ _ _ _

theorem offEntry_anticommute {width : ℕ} (K : CochainComplex A ℤ) (a : ℤ)
    (p q : Fin width) :
    (row Φ K p).d a (a+1) ≫ offEntry Φ K (a+1) p q +
      offEntry Φ K a p q ≫ (row Φ K q).d (a+1) (a+1+1) = 0 := by
  classical
  by_cases next : chainDegree p = chainDegree q+1
  · simp only [offEntry,dif_pos next]
    change ((chainDegree p : ℤ).negOnePow • (Φ.map (K.d _ _)).f (chainDegree p)) ≫
        transportedHorizontal Φ K _ _ (chainDegree p) (chainDegree q) _ +
      transportedHorizontal Φ K _ _ (chainDegree p) (chainDegree q) _ ≫
        ((chainDegree q : ℤ).negOnePow • (Φ.map (K.d _ _)).f (chainDegree q)) = 0
    rw [Linear.units_smul_comp,Linear.comp_units_smul,
      transportedHorizontal_vertical Φ K
        (a + (chainDegree p : ℤ)) (a+1 + (chainDegree p : ℤ))
        (a+1 + (chainDegree q : ℤ)) (a+1+1 + (chainDegree q : ℤ))
        (chainDegree p) (chainDegree q) (by omega) (by omega)]
    have signs : (chainDegree p : ℤ).negOnePow = -(chainDegree q : ℤ).negOnePow := by
      have equality : (chainDegree p : ℤ) = (chainDegree q : ℤ)+1 := by omega
      rw [equality,Int.negOnePow_succ]
    rw [signs,Units.neg_smul,neg_add_cancel]
  · simp only [offEntry,dif_neg next,zero_comp,comp_zero,add_zero]

theorem off_coherent {width : ℕ} (K : CochainComplex A ℤ) :
    FiniteTotal.Coherent (row Φ K (width := width)) (off Φ K) := by
  constructor
  · intro a
    apply biproduct.hom_ext'
    intro p
    apply biproduct.hom_ext
    intro q
    simpa only [FiniteTotal.diagonal,off,comp_add,add_comp,Category.assoc,
      biproduct.ι_map_assoc,biproduct.map_π,biproduct.ι_matrix_assoc,
      biproduct.lift_π,biproduct.lift_π_assoc,zero_comp,comp_zero] using
      offEntry_anticommute Φ K a p q
  · intro a
    apply biproduct.hom_ext'
    intro p
    apply biproduct.hom_ext
    intro q
    simp only [off,Category.assoc,biproduct.matrix_π,biproduct.ι_matrix_assoc,
      biproduct.lift_desc,zero_comp,comp_zero]
    apply Finset.sum_eq_zero
    intro r _
    exact offEntry_comp Φ K a p r q

theorem off_strictlyRaises {width : ℕ} (K : CochainComplex A ℤ) :
    FiniteTotal.StrictlyRaises (row Φ K (width := width)) (off Φ K) := by
  intro a p q nonraising
  simp only [off,biproduct.ι_matrix_assoc,biproduct.lift_π]
  have notNext : ¬ chainDegree p = chainDegree q+1 := by
    simp only [chainDegree,Fin.val_rev]
    omega
  simp only [offEntry,dif_neg notNext]

def total (width : ℕ) (K : CochainComplex A ℤ) : CochainComplex B ℤ :=
  FiniteTotal.complex (row Φ K (width := width)) (off Φ K) (off_coherent Φ K)

end ToricPower.NegativeFunctorTotal

end

