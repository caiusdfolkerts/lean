module

public import ToricPower.FiniteTwistedTotal
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-!
# Totalizing a finite complex-valued additive functor

For `Φ : A ⥤ CochainComplex B ℕ` and an arbitrary integer complex `K`,
the term of total degree `a` is the actual finite biproduct of
`(Φ.obj (K.X (a-q))).X q`. The vertical sign is `(-1)^q`; the
horizontal differential is the original differential of `Φ`, transported
only across the equality `(a+1)-(q+1)=a-q`.
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

abbrev degree (q : ℕ) : A ⥤ B := Φ ⋙ HomologicalComplex.eval B (.up ℕ) q

/-- The complete vertical row, with its genuine cochain shift. -/
abbrev row {width : ℕ} (K : CochainComplex A ℤ) (q : Fin width) :
    CochainComplex B ℤ :=
  (CategoryTheory.shiftFunctor (CochainComplex B ℤ) (-(q.val : ℤ))).obj
    (((degree Φ q.val).mapHomologicalComplex (.up ℤ)).obj K)

/-- Horizontal transport uses only an equality of the input degrees. -/
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

/-- One original horizontal differential, with no contribution between
nonconsecutive horizontal degrees. -/
def offEntry {width : ℕ} (K : CochainComplex A ℤ) (a : ℤ) (p q : Fin width) :
    (row Φ K p).X a ⟶ (row Φ K q).X (a+1) :=
  if next : p.val+1=q.val then
    transportedHorizontal Φ K (a + -(p.val : ℤ)) (a+1 + -(q.val : ℤ))
      p.val q.val (by omega)
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
  by_cases next : p.val+1=q.val
  · simp only [offEntry,dif_pos next]
    change ((-(p.val : ℤ)).negOnePow • (Φ.map (K.d _ _)).f p.val) ≫
        transportedHorizontal Φ K _ _ p.val q.val _ +
      transportedHorizontal Φ K _ _ p.val q.val _ ≫
        ((-(q.val : ℤ)).negOnePow • (Φ.map (K.d _ _)).f q.val) = 0
    rw [Linear.units_smul_comp,Linear.comp_units_smul,
      transportedHorizontal_vertical Φ K
        (a + -(p.val : ℤ)) (a+1 + -(p.val : ℤ))
        (a+1 + -(q.val : ℤ)) (a+1+1 + -(q.val : ℤ))
        p.val q.val (by omega) (by omega)]
    have signs : (-(q.val : ℤ)).negOnePow = -( -(p.val : ℤ)).negOnePow := by
      rw [Int.negOnePow_neg,Int.negOnePow_neg]
      have equality : (q.val : ℤ) = (p.val : ℤ)+1 := by omega
      rw [equality,Int.negOnePow_succ]
    rw [signs,Units.neg_smul,add_neg_cancel]
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
  have notNext : ¬p.val+1=q.val := by omega
  simp only [offEntry,dif_neg notNext]

/-- The actual finite signed total, on a wholly unbounded input. The
number `width` includes exactly the horizontal degrees `0,…,width−1`.
When `Φ` is zero above them, this is its entire total complex. -/
def total (width : ℕ) (K : CochainComplex A ℤ) : CochainComplex B ℤ :=
  FiniteTotal.complex (row Φ K (width := width)) (off Φ K) (off_coherent Φ K)

end ToricPower.FunctorTotal

end
