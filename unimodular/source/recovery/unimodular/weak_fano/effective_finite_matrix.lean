module

public import Recovery.Unimodular.WeakFano.EffectiveMatrixCorrectness
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

namespace Unimodular.EffectiveMatrix

variable {n : ℕ} {E : Type*} [Fintype E] [DecidableEq E] [Encodable E]

instance (u : E → Lattice n) : Encodable (Column u) :=
  inferInstanceAs (Encodable {s : Finset E // fullTest u s})

/-- Both finite index maps are computed from encodings of the original
finite label data. No classical finite equivalence is used by the program. -/
def columnIndex (u : E → Lattice n) : Fin (Fintype.card (Column u)) ≃ Column u :=
  EffectiveIndexing.finiteIndex (Column u)

def rowIndex : Fin (Fintype.card (Option (Row n E))) ≃ Option (Row n E) :=
  EffectiveIndexing.finiteIndex (Option (Row n E))

/-- A concrete Fin-indexed integer matrix computed from the raw ray matrix. -/
def finiteMatrix (u : E → Lattice n) :
    Matrix (Fin (Fintype.card (Option (Row n E)))) (Fin (Fintype.card (Column u))) ℤ :=
  fun i j => matrix u (rowIndex i) (columnIndex u j)

def finiteEquation (u : E → Lattice n) :
    (Fin (Fintype.card (Column u)) → ℤ) →+
      (Fin (Fintype.card (Option (Row n E))) → ℤ) :=
  (Matrix.mulVecLin (finiteMatrix u)).toAddMonoidHom

def finiteTarget : Fin (Fintype.card (Option (Row n E))) → ℤ := fun i => target (rowIndex i)

def encodeCoefficients (u : E → Lattice n) :
    (Column u → ℤ) ≃+ (Fin (Fintype.card (Column u)) → ℤ) :=
  EffectiveIndexing.reindex (columnIndex u).symm

@[simp] theorem encodeCoefficients_apply (u : E → Lattice n) (c : Column u → ℤ)
    (j : Fin (Fintype.card (Column u))) :
    encodeCoefficients u c j = c (columnIndex u j) := rfl

@[simp] theorem finiteEquation_apply (u : E → Lattice n)
    (g : Fin (Fintype.card (Column u)) → ℤ) :
    finiteEquation u g = Matrix.mulVec (finiteMatrix u) g := rfl

/-- Exact equality of every matrix product under the explicit index maps. -/
theorem finiteEquation_encode (u : E → Lattice n) (c : Column u → ℤ)
    (i : Fin (Fintype.card (Option (Row n E)))) :
    finiteEquation u (encodeCoefficients u c) i = equation u c (rowIndex i) := by
  change (∑ j, matrix u (rowIndex i) (columnIndex u j) * c (columnIndex u j)) =
    ∑ s, matrix u (rowIndex i) s * c s
  exact (columnIndex u).sum_comp (fun s => matrix u (rowIndex i) s * c s)

/-- Every integer fiber is carried exactly, not only the kernel. -/
theorem finiteEquation_fiber_iff (u : E → Lattice n) (c : Column u → ℤ)
    (b : Option (Row n E) → ℤ) :
    finiteEquation u (encodeCoefficients u c) = (fun i => b (rowIndex i)) ↔ equation u c = b := by
  constructor
  · intro h
    ext r
    obtain ⟨i, rfl⟩ := rowIndex.surjective r
    exact (finiteEquation_encode u c i).symm.trans (congrFun h i)
  · intro h
    ext i
    rw [finiteEquation_encode, h]

/-- The finite coding introduces no new zero columns or primitive moves. -/
theorem finite_kernel_iff (u : E → Lattice n) (c : Column u → ℤ) :
    encodeCoefficients u c ∈ (finiteEquation u).ker ↔ c ∈ (equation u).ker := by
  exact finiteEquation_fiber_iff u c 0

theorem finite_primitive_iff (u : E → Lattice n) (c : Column u → ℤ) :
    Graver.Primitive (finiteEquation u).ker (encodeCoefficients u c) ↔
      Graver.Primitive (equation u).ker c :=
  EffectiveIndexing.primitive_reindex_iff (columnIndex u).symm (equation u).ker
    (finiteEquation u).ker (finite_kernel_iff u) c

noncomputable section
attribute [local instance] Classical.propDecidable

local notation "ι₀" => EffectiveAllowed.embedding n

/-- Exact interpretation of the computed integer-vector code in the paper's
original column coordinates. This occurs only in the correctness statement. -/
def originalCoefficients (u : E → Lattice n) (hnz : ∀ e, embed (u e) ≠ 0)
    (g : Fin (Fintype.card (Column u)) → ℤ) : AllowedBlocks.FullBlock ι₀ u → ℤ :=
  coefficientEquiv u hnz ((encodeCoefficients u).symm g)

/-- The complete finite integer matrix computed from U has exactly the
paper's primitive replacements, after the literal coordinate permutation. -/
theorem finite_primitive_original_iff (u : E → Lattice n) (hnz : ∀ e, embed (u e) ≠ 0)
    (hspan : Submodule.span ℝ (Set.range (fun e => embed (u e))) = ⊤)
    (g : Fin (Fintype.card (Column u)) → ℤ) :
    Graver.Primitive (finiteEquation u).ker g ↔
      Graver.Primitive (AllowedBlocks.equationMap ι₀ u
        (embed (EffectiveDirection.direction u))).ker (originalCoefficients u hnz g) := by
  have h₁ := finite_primitive_iff u ((encodeCoefficients u).symm g)
  rw [AddEquiv.apply_symm_apply] at h₁
  exact h₁.trans (primitive_iff u hnz hspan ((encodeCoefficients u).symm g))

/-- Exact normalized nonnegative-fiber correspondence for the delivered
Fin-indexed matrix. -/
theorem finite_solution_original_iff (u : E → Lattice n) (hnz : ∀ e, embed (u e) ≠ 0)
    (hspan : Submodule.span ℝ (Set.range (fun e => embed (u e))) = ⊤)
    (g : Fin (Fintype.card (Column u)) → ℤ) :
    ((∀ j, 0 ≤ g j) ∧ finiteEquation u g = finiteTarget) ↔
      AllowedBlocks.IsSolution ι₀ u (embed (EffectiveDirection.direction u))
        (originalCoefficients u hnz g) := by
  let c := (encodeCoefficients u).symm g
  have he : encodeCoefficients u c = g := (encodeCoefficients u).apply_symm_apply g
  have hf := finiteEquation_fiber_iff u c target
  rw [he] at hf
  have hn := EffectiveIndexing.nonnegative_reindex_iff (columnIndex u).symm c
  change (∀ j, 0 ≤ encodeCoefficients u c j) ↔ ∀ s, 0 ≤ c s at hn
  rw [he] at hn
  exact (and_congr hn hf).trans (nonnegative_solution_iff u hnz hspan c)

end
end Unimodular.EffectiveMatrix

#print axioms Unimodular.EffectiveMatrix.finiteMatrix
#print axioms Unimodular.EffectiveMatrix.finiteEquation_fiber_iff
#print axioms Unimodular.EffectiveMatrix.finite_primitive_original_iff
#print axioms Unimodular.EffectiveMatrix.finite_solution_original_iff
#check Unimodular.EffectiveMatrix.finite_primitive_original_iff
