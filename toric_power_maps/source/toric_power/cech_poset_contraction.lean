module

public import ToricPower.CechPosetResolution

/-!
# Contraction and finite replacement of the ordered Čech resolution

Inserting the chart at which we evaluate is an actual extra degeneracy.
Its contracting homotopy proves that the ordered tuple augmentation is
a quasi-isomorphism of diagrams. Projectivity then supplies a genuine
homotopy equivalence with the finite grade resolution, including the
augmentation comparison. No Čech degree is discarded by definition.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace ToricPower.FiniteCech

universe u

variable {B : Type u} [SemilatticeInf B]

/-- Evaluating the augmented tuple presheaf at an actual chart. -/
def evaluatedTupleSet (b : Bᵒᵖ) : SimplicialObject.Augmented (Type u) :=
  ((SimplicialObject.Augmented.whiskering _ _).obj
    ((evaluation Bᵒᵖ (Type u)).obj b)).obj upperTupleAugmented

/-- The anchor insertion keeps the tuple inside the charts containing
the evaluation chart. -/
def tupleAnchor (b : Bᵒᵖ) (n : ℕ) (t : UpperTuple b.unop n) :
    UpperTuple b.unop (n+1) :=
  ⟨Fin.cons b.unop t.val, fun i => Fin.cases le_rfl t.property i⟩

/-- Every evaluation has an explicit extra degeneracy. It is deliberately
not asserted to be natural in the evaluation chart. -/
def tupleExtraDegeneracy (b : Bᵒᵖ) :
    SimplicialObject.Augmented.ExtraDegeneracy (evaluatedTupleSet b) where
  s' := ↾fun _ => ⟨fun _ => b.unop, fun _ => le_rfl⟩
  s n := ↾tupleAnchor b n
  s'_comp_ε := by
    apply ConcreteCategory.hom_ext
    intro p
    cases p
    rfl
  s₀_comp_δ₁ := by
    apply ConcreteCategory.hom_ext
    intro t
    apply Subtype.ext
    funext i
    fin_cases i
    rfl
  s_comp_δ₀ n := by
    apply ConcreteCategory.hom_ext
    intro t
    apply Subtype.ext
    funext i
    simp [evaluatedTupleSet, upperTupleAugmented, upperTupleSimplicial,
      upperTupleSelect, tupleAnchor, SimplicialObject.δ, SimplexCategory.δ]
  s_comp_δ n i := by
    apply ConcreteCategory.hom_ext
    intro t
    apply Subtype.ext
    funext j
    dsimp [evaluatedTupleSet, upperTupleAugmented, upperTupleSimplicial,
      upperTupleSelect, tupleAnchor, SimplicialObject.δ, SimplexCategory.δ]
    cases j using Fin.cases <;> simp
  s_comp_σ n i := by
    apply ConcreteCategory.hom_ext
    intro t
    apply Subtype.ext
    funext j
    dsimp [evaluatedTupleSet, upperTupleAugmented, upperTupleSimplicial,
      upperTupleSelect, tupleAnchor, SimplicialObject.σ, SimplexCategory.σ]
    cases j using Fin.cases <;> simp

variable (k : Type u) [Field k]

/-- Linearization preserves the actual anchor contraction. -/
def evaluatedTupleModules (b : Bᵒᵖ) : SimplicialObject.Augmented (ModuleCat.{u} k) :=
  ((SimplicialObject.Augmented.whiskering _ _).obj (ModuleCat.free k)).obj
    (evaluatedTupleSet b)

/-- The actual linear chain homotopy equivalence at a chart. -/
def tupleLocalContraction (b : Bᵒᵖ) :
    HomotopyEquiv
      (AlgebraicTopology.AlternatingFaceMapComplex.obj (evaluatedTupleModules k b).left)
      ((ChainComplex.single₀ (ModuleCat.{u} k)).obj (evaluatedTupleModules k b).right) :=
  ((tupleExtraDegeneracy b).map (ModuleCat.free k)).homotopyEquiv

/-- Evaluation commutes with the alternating differential, with literal
identity maps on all the tuple terms. -/
def tupleComplexEvaluationIso (b : Bᵒᵖ) :
    (((evaluation Bᵒᵖ (ModuleCat.{u} k)).obj b).mapHomologicalComplex (.down ℕ)).obj
      (tupleComplex k) ≅
    AlgebraicTopology.AlternatingFaceMapComplex.obj (evaluatedTupleModules k b).left :=
  (AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso
    ((evaluation Bᵒᵖ (ModuleCat.{u} k)).obj b)).app (tupleAugmented k).left

/-- The corresponding comparison for the genuine augmentation target. -/
def tupleSingleEvaluationIso (b : Bᵒᵖ) :
    (((evaluation Bᵒᵖ (ModuleCat.{u} k)).obj b).mapHomologicalComplex (.down ℕ)).obj
      ((ChainComplex.single₀ (Bᵒᵖ ⥤ ModuleCat.{u} k)).obj (tupleAugmented k).right) ≅
    (ChainComplex.single₀ (ModuleCat.{u} k)).obj (evaluatedTupleModules k b).right :=
  (HomologicalComplex.singleMapHomologicalComplex
    ((evaluation Bᵒᵖ (ModuleCat.{u} k)).obj b) (.down ℕ) 0).app (tupleAugmented k).right

/-- The augmentation in the local contraction is the actual evaluated
global augmentation, not a separately chosen map to the same target. -/
theorem tupleAugmentation_evaluation (b : Bᵒᵖ) :
    (tupleComplexEvaluationIso k b).inv ≫
      (((evaluation Bᵒᵖ (ModuleCat.{u} k)).obj b).mapHomologicalComplex (.down ℕ)).map
        (tupleAugmentation k) ≫ (tupleSingleEvaluationIso k b).hom =
      (tupleLocalContraction k b).hom := by
  apply HomologicalComplex.to_single_hom_ext
  simp only [HomologicalComplex.comp_f, tupleSingleEvaluationIso,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    ChainComplex.single₀ObjXSelf, Iso.refl_hom, Iso.refl_inv,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  rfl

/-- The tuple augmentation is locally a genuine quasi-isomorphism. -/
theorem tupleAugmentation_local_quasiIso (b : Bᵒᵖ) :
    QuasiIso
      ((((evaluation Bᵒᵖ (ModuleCat.{u} k)).obj b).mapHomologicalComplex (.down ℕ)).map
        (tupleAugmentation k)) := by
  let f := (((evaluation Bᵒᵖ (ModuleCat.{u} k)).obj b).mapHomologicalComplex (.down ℕ)).map
    (tupleAugmentation k)
  have h : QuasiIso ((tupleComplexEvaluationIso k b).inv ≫ f ≫
      (tupleSingleEvaluationIso k b).hom) := by
    rw [tupleAugmentation_evaluation]
    exact (tupleLocalContraction k b).quasiIso_hom
  letI := h
  letI : QuasiIso (f ≫ (tupleSingleEvaluationIso k b).hom) :=
    quasiIso_of_comp_left (tupleComplexEvaluationIso k b).inv _
  exact quasiIso_of_comp_right f (tupleSingleEvaluationIso k b).hom

/-- Evaluation detects quasi-isomorphisms of actual complexes of
diagrams, so the global tuple augmentation is a quasi-isomorphism. -/
instance tupleAugmentation_quasiIso : QuasiIso (tupleAugmentation k (B := B)) := by
  rw [HomologicalComplex.quasiIso_iff_evaluation]
  exact tupleAugmentation_local_quasiIso k

/-- The ordinary, untruncated ordered tuple complex is a genuine
projective resolution of the constant free rank-one diagram. -/
def tupleProjectiveResolution : ProjectiveResolution (tupleAugmented k (B := B)).right where
  complex := tupleComplex k
  π := tupleAugmentation k
  projective n := tupleComplex_projective k n

/-- The finite-grade projective resolution of the very same constant
diagram; no replacement of the augmented object is involved. -/
def finiteTupleResolution : ProjectiveResolution (tupleAugmented k (B := B)).right :=
  Cellular.diagramProjectiveResolution k (tupleAugmented k).right

/-- Actual chain maps in both directions and both homotopies compare
ordinary ordered tuples with the finite-grade construction. -/
def tupleFiniteHomotopyEquiv :
    HomotopyEquiv (tupleComplex k (B := B)) (finiteTupleResolution k).complex :=
  (tupleProjectiveResolution k).homotopyEquiv (finiteTupleResolution k)

@[reassoc (attr := simp)]
theorem tupleFiniteHomotopyEquiv_hom_augmentation :
    (tupleFiniteHomotopyEquiv k (B := B)).hom ≫ (finiteTupleResolution k).π =
      tupleAugmentation k :=
  ProjectiveResolution.homotopyEquiv_hom_π _ _

@[reassoc (attr := simp)]
theorem tupleFiniteHomotopyEquiv_inv_augmentation :
    (tupleFiniteHomotopyEquiv k (B := B)).inv ≫ tupleAugmentation k =
      (finiteTupleResolution k).π :=
  ProjectiveResolution.homotopyEquiv_inv_π _ _

/-- The comparison target vanishes above the actual grade bound of the
intersection category. This is proved for the constructed resolution. -/
theorem finiteTupleResolution_isZero_above
    (grade : Bᵒᵖ → ℕ)
    (grade_le : ∀ {b c : Bᵒᵖ} (_ : b ⟶ c), grade b ≤ grade c)
    (eq_of_grade_eq : ∀ {b c : Bᵒᵖ} (_ : b ⟶ c), grade b = grade c → b = c)
    (N m : ℕ) (hbound : ∀ b, grade b ≤ N) (hm : N < m) :
    IsZero ((finiteTupleResolution k (B := B)).complex.X m) :=
  Cellular.diagramProjectiveComplex_isZero_above k grade grade_le eq_of_grade_eq
    (tupleAugmented k).right N m hbound hm

section Finite

variable [Fintype B]

/-- All charts above a chart, as a literal finite set. -/
def upperCharts (b : Bᵒᵖ) : Finset B := by
  classical
  exact Finset.univ.filter (fun c => b.unop ≤ c)

@[simp]
theorem mem_upperCharts (b : Bᵒᵖ) (c : B) : c ∈ upperCharts b ↔ b.unop ≤ c := by
  classical
  simp only [upperCharts, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Counting upper charts supplies an honest finite grade on the
opposite intersection poset, with no extra geometric hypothesis. -/
def chartGrade (b : Bᵒᵖ) : ℕ := (upperCharts b).card

theorem upperCharts_subset {b c : Bᵒᵖ} (f : b ⟶ c) :
    upperCharts b ⊆ upperCharts c := by
  intro x hx
  exact (mem_upperCharts c x).mpr ((leOfHom f.unop).trans ((mem_upperCharts b x).mp hx))

theorem chartGrade_le {b c : Bᵒᵖ} (f : b ⟶ c) : chartGrade b ≤ chartGrade c :=
  Finset.card_le_card (upperCharts_subset f)

theorem eq_of_chartGrade_eq {b c : Bᵒᵖ} (f : b ⟶ c)
    (h : chartGrade b = chartGrade c) : b = c := by
  have heq : upperCharts b = upperCharts c :=
    Finset.eq_of_subset_of_card_le (upperCharts_subset f) (Nat.le_of_eq h.symm)
  have hc : c.unop ∈ upperCharts b := by
    rw [heq, mem_upperCharts]
  apply unop_injective
  exact le_antisymm ((mem_upperCharts b c.unop).mp hc) (leOfHom f.unop)

theorem chartGrade_bound (b : Bᵒᵖ) : chartGrade b ≤ Fintype.card B := by
  classical
  exact (Finset.card_le_card (Finset.subset_univ (upperCharts b))).trans_eq (Finset.card_univ)

/-- For every finite intersection poset, the constructed resolution
vanishes above the number of charts. The source remains the complete
ordered Čech complex, to which it is homotopy equivalent. -/
theorem finiteTupleResolution_isZero_of_card_lt (m : ℕ) (hm : Fintype.card B < m) :
    IsZero ((finiteTupleResolution k (B := B)).complex.X m) :=
  finiteTupleResolution_isZero_above k chartGrade chartGrade_le
    eq_of_chartGrade_eq (Fintype.card B) m chartGrade_bound hm

end Finite

end ToricPower.FiniteCech

end
