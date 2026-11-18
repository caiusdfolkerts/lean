module

public import ToricPower.CechPosetContraction
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.CategoryTheory.Linear.Yoneda

/-!
# Scalar-linear Čech coefficients and their finite comparison

Evaluation on tuple generators identifies maps out of the projective
tuple term with the literal product of sections over intersections.
The identification is linear over the coefficient field and intertwines
every tuple selection. In particular its differential is the ordinary
alternating restriction differential.

Dualizing the proved projective-resolution comparison gives actual
chain maps and homotopies on coefficients. Its finite target has zero
terms above the number of charts, without changing the full source.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace ToricPower.FiniteCech

universe u

variable {B : Type u} [SemilatticeInf B] (k : Type u) [Field k]

/-- Evaluation at the intersection generator is a scalar-linear
equivalence with the actual Čech coefficient product. -/
def tupleEvaluation (n : ℕ) (F : Bᵒᵖ ⥤ ModuleCat.{u} k) :
    (tupleModule k n ⟶ F) ≃ₗ[k] (∀ t : Fin (n+1) → B, F.obj (op (tupleMeet t))) where
  toFun φ t := φ.app (op (tupleMeet t)) (ModuleCat.freeMk (tupleAtMeet t))
  invFun v := tupleDesc k n F v
  left_inv φ := by
    apply NatTrans.ext
    funext b
    apply ModuleCat.free_hom_ext
    intro t
    exact (tupleDesc_freeMk k n F _ b t).trans
      (tupleMap_generator k n F φ b t).symm
  right_inv v := by
    funext t
    have hid : tupleSourceMap (tupleAtMeet t) = 𝟙 (op (tupleMeet t)) := Subsingleton.elim _ _
    have h := tupleDesc_freeMk k n F v (op (tupleMeet t)) (tupleAtMeet t)
    have hmap : F.map (tupleSourceMap (tupleAtMeet t)) = 𝟙 (F.obj (op (tupleMeet t))) :=
      (congrArg F.map hid).trans (F.map_id _)
    exact h.trans (ConcreteCategory.congr_hom hmap (v t))
  map_add' φ ψ := rfl
  map_smul' r φ := rfl

/-- Selection maps act on the free tuple generators by the literal
coordinate selection. -/
def tupleSelection {m n : ℕ} (s : Fin (m+1) → Fin (n+1)) :
    tupleModule k (B := B) n ⟶ tupleModule k m :=
  (freeTupleDiagrams k).map
    { app b := ↾upperTupleSelect s
      naturality {_ _} f := rfl }

/-- The full intersection is contained in an intersection obtained by
selecting entries, with repetitions allowed. -/
theorem tupleMeet_le_selection {m n : ℕ} (s : Fin (m+1) → Fin (n+1))
    (t : Fin (n+1) → B) : tupleMeet t ≤ tupleMeet (t ∘ s) :=
  (le_tupleMeet_iff _ _).mpr (fun j => tupleMeet_le t (s j))

/-- Every coefficient restriction agrees with precomposition by the
actual tuple map, before taking any homology. -/
theorem tupleEvaluation_selection {m n : ℕ} (s : Fin (m+1) → Fin (n+1))
    (F : Bᵒᵖ ⥤ ModuleCat.{u} k) (φ : tupleModule k m ⟶ F) (t : Fin (n+1) → B) :
    tupleEvaluation k n F (tupleSelection k s ≫ φ) t =
      F.map (homOfLE (tupleMeet_le_selection s t)).op
        (tupleEvaluation k m F φ (t ∘ s)) := by
  change φ.app (op (tupleMeet t))
    ((ModuleCat.free k).map (↾upperTupleSelect s) (ModuleCat.freeMk (tupleAtMeet t))) = _
  rw [ModuleCat.free_map_apply]
  exact tupleMap_generator k m F φ (op (tupleMeet t))
    (upperTupleSelect s (tupleAtMeet t))

/-- The scalar-linear dual of an actual chain complex of diagrams. -/
def coefficientComplex (F : Bᵒᵖ ⥤ ModuleCat.{u} k)
    (P : ChainComplex (Bᵒᵖ ⥤ ModuleCat.{u} k) ℕ) : CochainComplex (ModuleCat.{u} k) ℕ :=
  (((linearYoneda k (Bᵒᵖ ⥤ ModuleCat.{u} k)).obj F).mapHomologicalComplex _).obj P.op

/-- The actual contravariant chain map on coefficient complexes. -/
def coefficientMap (F : Bᵒᵖ ⥤ ModuleCat.{u} k)
    {P Q : ChainComplex (Bᵒᵖ ⥤ ModuleCat.{u} k) ℕ} (f : P ⟶ Q) :
    coefficientComplex k F Q ⟶ coefficientComplex k F P :=
  (((linearYoneda k (Bᵒᵖ ⥤ ModuleCat.{u} k)).obj F).mapHomologicalComplex _).map
    ((HomologicalComplex.opFunctor _ _).map f.op)

@[simp]
theorem coefficientMap_id (F : Bᵒᵖ ⥤ ModuleCat.{u} k)
    (P : ChainComplex (Bᵒᵖ ⥤ ModuleCat.{u} k) ℕ) :
    coefficientMap k F (𝟙 P) = 𝟙 (coefficientComplex k F P) := by
  simp [coefficientMap, coefficientComplex]

@[simp]
theorem coefficientMap_comp (F : Bᵒᵖ ⥤ ModuleCat.{u} k)
    {P Q S : ChainComplex (Bᵒᵖ ⥤ ModuleCat.{u} k) ℕ} (f : P ⟶ Q) (g : Q ⟶ S) :
    coefficientMap k F (f ≫ g) = coefficientMap k F g ≫ coefficientMap k F f := by
  simp [coefficientMap]

/-- An actual chain homotopy remains a chain homotopy under scalar Hom. -/
def coefficientHomotopy (F : Bᵒᵖ ⥤ ModuleCat.{u} k)
    {P Q : ChainComplex (Bᵒᵖ ⥤ ModuleCat.{u} k) ℕ} {f g : P ⟶ Q}
    (h : Homotopy f g) : Homotopy (coefficientMap k F f) (coefficientMap k F g) :=
  ((linearYoneda k (Bᵒᵖ ⥤ ModuleCat.{u} k)).obj F).mapHomotopy h.op

/-- The full homotopy-equivalence structure is transported, rather than
merely an equality of cohomology dimensions. -/
def coefficientHomotopyEquiv (F : Bᵒᵖ ⥤ ModuleCat.{u} k)
    {P Q : ChainComplex (Bᵒᵖ ⥤ ModuleCat.{u} k) ℕ} (e : HomotopyEquiv P Q) :
    HomotopyEquiv (coefficientComplex k F P) (coefficientComplex k F Q) where
  hom := coefficientMap k F e.inv
  inv := coefficientMap k F e.hom
  homotopyHomInvId := by
    have h := coefficientHomotopy k F e.homotopyHomInvId
    simpa only [coefficientMap_comp, coefficientMap_id] using h
  homotopyInvHomId := by
    have h := coefficientHomotopy k F e.homotopyInvHomId
    simpa only [coefficientMap_comp, coefficientMap_id] using h

/-- Čech cochains obtained from the actual ordered tuple resolution. -/
abbrev tupleCoefficientComplex (F : Bᵒᵖ ⥤ ModuleCat.{u} k) :
    CochainComplex (ModuleCat.{u} k) ℕ :=
  coefficientComplex k F (tupleComplex k)

/-- In coefficient coordinates, the differential is precisely the
alternating sum of the usual restrictions to the full intersection. -/
theorem tupleCoefficient_d_apply (F : Bᵒᵖ ⥤ ModuleCat.{u} k) (n : ℕ)
    (φ : (tupleCoefficientComplex k F).X n) (t : Fin (n+2) → B) :
    tupleEvaluation k (n+1) F ((tupleCoefficientComplex k F).d n (n+1) φ) t =
      ∑ i : Fin (n+2), ((-1 : ℤ) ^ i.val) •
        F.map (homOfLE (tupleMeet_le_selection i.succAbove t)).op
          (tupleEvaluation k n F φ (t ∘ i.succAbove)) := by
  change tupleEvaluation k (n+1) F ((tupleComplex k).d (n+1) n ≫ φ) t = _
  have hd : (tupleComplex k (B := B)).d (n+1) n =
      ∑ i : Fin (n+2), (-1 : ℤ)^i.val • (tupleAugmented k).left.δ i :=
    AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq _ _
  rw [hd, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp, map_sum, map_zsmul, Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact tupleEvaluation_selection k i.succAbove F φ t

/-- A finite comparison of the literal Čech cochain complex, linear over
the actual coefficient field. -/
def finiteCoefficientComparison (F : Bᵒᵖ ⥤ ModuleCat.{u} k) :
    HomotopyEquiv (tupleCoefficientComplex k F)
      (coefficientComplex k F (finiteTupleResolution k).complex) :=
  coefficientHomotopyEquiv k F (tupleFiniteHomotopyEquiv k)

/-- The finite coefficient comparison has genuinely zero terms above
the number of charts, for every coefficient diagram. -/
theorem finiteCoefficient_isZero_of_card_lt [Fintype B]
    (F : Bᵒᵖ ⥤ ModuleCat.{u} k) (m : ℕ) (hm : Fintype.card B < m) :
    IsZero ((coefficientComplex k F (finiteTupleResolution k).complex).X m) :=
  ((linearYoneda k (Bᵒᵖ ⥤ ModuleCat.{u} k)).obj F).map_isZero
    (finiteTupleResolution_isZero_of_card_lt k m hm).op

end ToricPower.FiniteCech

end
