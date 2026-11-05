module

public import PaperVerification.FermionNaturalColorEmbedding
public import PaperVerification.FermionColorBlockExterior
public import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.Finset.Insert
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
# A unit comparison for the actual natural color assembly

Each tensor factor contributes its original
local exterior word.  Their concatenation contains each original odd
coordinate exactly once.  Successive exterior-basis insertions therefore
supply an actual shuffle-sign unit.  No explicit crossing-count formula is
assumed, and the final word uses the paper's theta-then-xi order.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical TensorProduct BigOperators

namespace PaperVerification.Fermion.NaturalColor

section OrderedWords

variable {R V I : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [LinearOrder I] (b : Module.Basis I R V)

private theorem exteriorBasis_empty : b.ExteriorAlgebra (∅ : Finset I)=1 := by
  rw [Module.Basis.exteriorAlgebra_eq_prod_map_sort]
  simp

/-- Any duplicate-free ordering of a fixed basis subset differs from its
sorted exterior basis word by an actual unit of the coefficient ring. -/
theorem orderedWord_basis_unit (l : List I) (hl : l.Nodup) :
    ∃ ε : Rˣ,(l.map (fun i ↦ ExteriorAlgebra.ι R (b i))).prod=
      (ε : R) • b.ExteriorAlgebra l.toFinset := by
  induction l with
  | nil =>
      refine ⟨1,?_⟩
      simp only [List.map_nil,List.prod_nil,List.toFinset_nil,Units.val_one,
        one_smul,exteriorBasis_empty]
  | cons i l ih =>
      have hi : i∉l := (List.nodup_cons.mp hl).1
      have hli : l.Nodup := (List.nodup_cons.mp hl).2
      have hiset : i∉l.toFinset := by simpa only [List.mem_toFinset] using hi
      obtain ⟨ε,hε⟩ := ih hli
      let sign := TauCeti.ExteriorAlgebra.basisEraseSign i (insert i l.toFinset)
      let η : Rˣ := Units.map (Int.castRingHom R).toMonoidHom sign
      have hp : ExteriorAlgebra.ι R (b i)*b.ExteriorAlgebra l.toFinset=
          (η : R) • b.ExteriorAlgebra (insert i l.toFinset) := by
        have h := TauCeti.ExteriorAlgebra.basis_singleton_mul_basis_erase b i
          (insert i l.toFinset) (Finset.mem_insert_self _ _)
        rw [TauCeti.ExteriorAlgebra.basis_singleton,Finset.erase_insert hiset] at h
        change ExteriorAlgebra.ι R (b i)*b.ExteriorAlgebra l.toFinset=
          ((sign : ℤ) : R) • b.ExteriorAlgebra (insert i l.toFinset)
        simpa only [sign,Units.smul_def,Int.cast_smul_eq_zsmul] using h
      refine ⟨ε*η,?_⟩
      simp only [List.map_cons,List.prod_cons,List.toFinset_cons,hε,Units.val_mul]
      rw [Algebra.mul_smul_comm,hp,smul_smul]

end OrderedWords

section Lists

variable {n : ℕ}
open Endpoint Paths ColorPaths

def localWord (i : Fin n) : Mark → List (OddIndex n)
  | .unmarked => []
  | .theta => [.inl i]
  | .xi => [.inr i]
  | .double => [.inl i,.inr i]

@[simp] theorem localWord_nodup (i : Fin n) (a : Mark) :
    (localWord i a).Nodup := by
  cases a <;> simp [localWord]

@[simp] theorem localWord_mem_inl (i j : Fin n) (a : Mark) :
    Sum.inl j∈localWord i a ↔ j=i ∧ (a=.theta ∨ a=.double) := by
  cases a <;> simp [localWord]

@[simp] theorem localWord_mem_inr (i j : Fin n) (a : Mark) :
    Sum.inr j∈localWord i a ↔ j=i ∧ (a=.xi ∨ a=.double) := by
  cases a <;> simp [localWord]

theorem localWord_index {i : Fin n} {a : Mark} {j : OddIndex n}
    (hj : j∈localWord i a) : Sum.elim id id j=i := by
  cases j with
  | inl j => exact (localWord_mem_inl i j a).mp hj |>.1
  | inr j => exact (localWord_mem_inr i j a).mp hj |>.1

/-- Increasing index order, and theta before xi within one index. -/
def orderedColorWord (marks : Fin n → Mark) : List (OddIndex n) :=
  (List.finRange n).flatMap (fun i ↦ localWord i (marks i))

theorem orderedColorWord_nodup (marks : Fin n → Mark) :
    (orderedColorWord marks).Nodup := by
  rw [orderedColorWord,List.nodup_flatMap]
  refine ⟨fun i hi ↦ localWord_nodup i (marks i),?_⟩
  apply (List.nodup_finRange n).imp
  intro i j hij
  intro x hxi hxj
  exact hij ((localWord_index hxi).symm.trans (localWord_index hxj))

theorem orderedColorWord_toFinset (marks : Fin n → Mark) :
    (orderedColorWord marks).toFinset=wordOfMarks marks := by
  ext a
  cases a with
  | inl i =>
      simp only [List.mem_toFinset,orderedColorWord,List.mem_flatMap,
        List.mem_finRange,localWord_mem_inl,wordOfMarks_inl,true_and]
      simp
  | inr i =>
      simp only [List.mem_toFinset,orderedColorWord,List.mem_flatMap,
        List.mem_finRange,localWord_mem_inr,wordOfMarks_inr,true_and]
      simp

private theorem prod_map_flatMap {A B C : Type*} [Monoid C]
    (l : List A) (w : A → List B) (f : B → C) :
    ((l.flatMap w).map f).prod=(l.map (fun i ↦ ((w i).map f).prod)).prod := by
  induction l with
  | nil => simp
  | cons i l ih =>
      simp only [List.flatMap_cons,List.map_append,List.prod_append,
        List.map_cons,List.prod_cons,ih]

end Lists

section ColorBasis

open Endpoint Paths ColorPaths
variable {R : Type*} [CommRing R] {n : ℕ}

local instance paperOddOrder : LinearOrder (OddIndex n) :=
  LinearOrder.lift' Exterior.modeRank Exterior.modeRank_injective

private theorem embedding_basis_theta (i : Fin n) :
    embedding (R := R) i ((Pi.basisFun R (Fin 2)) 0)=
      (Pi.basisFun R (OddIndex n)) (.inl i) := by
  funext j
  cases j <;> simp [embedding,Pi.basisFun_apply,Pi.single_apply,eq_comm]

private theorem embedding_basis_xi (i : Fin n) :
    embedding (R := R) i ((Pi.basisFun R (Fin 2)) 1)=
      (Pi.basisFun R (OddIndex n)) (.inr i) := by
  funext j
  cases j <;> simp [embedding,Pi.basisFun_apply,Pi.single_apply,eq_comm]

private theorem localExteriorBasis_image (m : MultiplicityVector n)
    (T : MultiplicityColoring m) (i : Fin n) :
    ExteriorAlgebra.map (embedding (R := R) i)
      ((Pi.basisFun R (Fin 2)).exteriorPower (m i).val
        ((coloringExteriorIndexEquiv m T) i))=
      ((localWord i (wordMark T.val i)).map
        (fun j ↦ ExteriorAlgebra.ι R ((Pi.basisFun R (OddIndex n)) j))).prod := by
  rw [←ExteriorAlgebra.basis_eq_coe_basis]
  change ExteriorAlgebra.map (embedding (R := R) i)
      ((Pi.basisFun R (Fin 2)).ExteriorAlgebra (markSubset (wordMark T.val i)))=_
  generalize ha : wordMark T.val i=a
  cases a with
  | unmarked =>
      simp only [markSubset,localWord,exteriorBasis_empty,map_one,
        List.map_nil,List.prod_nil]
  | theta =>
      simp only [markSubset,localWord,TauCeti.ExteriorAlgebra.basis_singleton,
        ExteriorAlgebra.map_apply_ι,embedding_basis_theta,List.map_cons,
        List.map_nil,List.prod_cons,List.prod_nil,mul_one]
  | xi =>
      simp only [markSubset,localWord,TauCeti.ExteriorAlgebra.basis_singleton,
        ExteriorAlgebra.map_apply_ι,embedding_basis_xi,List.map_cons,
        List.map_nil,List.prod_cons,List.prod_nil,mul_one]
  | double =>
      rw [show markSubset Mark.double=({0,1} : Finset (Fin 2)) from rfl,
        TauCeti.ExteriorAlgebra.basis_pair (Pi.basisFun R (Fin 2)) (by decide : (0 : Fin 2)<1),
        map_mul,ExteriorAlgebra.map_apply_ι,ExteriorAlgebra.map_apply_ι,
        embedding_basis_theta,embedding_basis_xi]
      simp only [localWord,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]

/-- The actual tensor basis assembles to the ordered list of its original
odd generators. This is a calculation in the original exterior algebra. -/
theorem assemble_basis_word (m : MultiplicityVector n) (T : MultiplicityColoring m) :
    assemble (fun i ↦ (m i).val) (exteriorColorTensorBasis R m T)=
      ((orderedColorWord (wordMark T.val)).map
        (fun j ↦ ExteriorAlgebra.ι R ((Pi.basisFun R (OddIndex n)) j))).prod := by
  rw [exteriorColorTensorBasis_apply,assemble_tprod]
  simp_rw [localExteriorBasis_image]
  rw [List.ofFn_eq_map]
  exact (prod_map_flatMap (List.finRange n)
    (fun i ↦ localWord i (wordMark T.val i))
    (fun j ↦ ExteriorAlgebra.ι R ((Pi.basisFun R (OddIndex n)) j))).symm

/-- Assembly has an invertible diagonal coefficient relative to the paper's
actual theta-then-xi exterior basis; no explicit sign formula is required. -/
theorem assemble_basis_units (m : MultiplicityVector n) (T : MultiplicityColoring m) :
    ∃ ε : Rˣ,assemble (fun i ↦ (m i).val) (exteriorColorTensorBasis R m T)=
      (ε : R) • (Pi.basisFun R (OddIndex n)).ExteriorAlgebra T.val := by
  obtain ⟨ε,hε⟩ := orderedWord_basis_unit (Pi.basisFun R (OddIndex n))
    (orderedColorWord (wordMark T.val)) (orderedColorWord_nodup _)
  refine ⟨ε,?_⟩
  rw [assemble_basis_word,hε]
  apply congrArg (fun W : Finset (OddIndex n) ↦
    (ε : R) • (Pi.basisFun R (OddIndex n)).ExteriorAlgebra W)
  ext a
  have hset := (orderedColorWord_toFinset (wordMark T.val)).trans
    ((marksWordEquiv n).right_inv T.val)
  simpa only [List.mem_toFinset] using Finset.ext_iff.mp hset a

end ColorBasis

section Field

open ColorPaths
variable {F : Type*} [Field F] {n : ℕ}

local instance fieldPaperOddOrder : LinearOrder (OddIndex n) :=
  LinearOrder.lift' Exterior.modeRank Exterior.modeRank_injective

/-- The nonzero coefficient required by the actual quotient-block comparison. -/
theorem assemble_basis_unit (m : MultiplicityVector n) (T : MultiplicityColoring m) :
    ∃ ε : F,ε≠0 ∧
      assemble (fun i ↦ (m i).val) (exteriorColorTensorBasis F m T)=
        ε • (Pi.basisFun F (OddIndex n)).ExteriorAlgebra T.val := by
  obtain ⟨ε,hε⟩ := assemble_basis_units (R := F) m T
  exact ⟨ε,ε.ne_zero,hε⟩

end Field
end PaperVerification.Fermion.NaturalColor
