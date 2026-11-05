import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.Tactic.Ext
import Mathlib.Tactic.SplitIfs
/-! # Genuine homogeneous components obtained by assigning degrees to basis vectors -/

noncomputable section

namespace CommAlg.Grading

open Classical

variable {R M I A : Type*} [CommRing R] [AddCommMonoid M] [Module R M]

/-- Restrict a basis to the span of an arbitrary set of its indices. -/
def restrictedBasis (b : Module.Basis I R M) (P : I → Prop) :
    Module.Basis {i // P i} R (Submodule.span R (b '' {i | P i})) :=
  (Module.Basis.span (b.linearIndependent.comp Subtype.val Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ (by congr 1; ext x; simp))

@[simp] lemma restrictedBasis_val (b : Module.Basis I R M) (P : I → Prop)
    (i : {i // P i}) :
    (restrictedBasis b P i).val = b i.val := by
  simp [restrictedBasis, Module.Basis.map_apply]

/-- A degree component is a genuine submodule of the original module. -/
def Piece (b : Module.Basis I R M) (deg : I → A) (a : A) : Submodule R M :=
  Submodule.span R (b '' {i | deg i = a})

lemma mem_piece (b : Module.Basis I R M) (deg : I → A) (a : A) (x : M) :
    x ∈ Piece b deg a ↔ ∀ i, b.repr x i ≠ 0 → deg i = a := by
  rw [Piece, b.mem_span_image]
  simp only [Set.subset_def, Finset.mem_coe, Finsupp.mem_support_iff, Set.mem_setOf_eq]

lemma basis_mem_piece (b : Module.Basis I R M) (deg : I → A) (i : I) :
    b i ∈ Piece b deg (deg i) := Submodule.subset_span ⟨i, rfl, rfl⟩

def filterMap (P : I → Prop) : (I →₀ R) →ₗ[R] (I →₀ R) where
  toFun := Finsupp.filter P
  map_add' x y := Finsupp.filter_add
  map_smul' c x := Finsupp.filter_smul

@[simp] lemma filterMap_apply (P : I → Prop) (x : I →₀ R) :
    filterMap P x = x.filter P := rfl

/-- Homogeneous projection defined on the original module by its actual basis coefficients. -/
def projection (b : Module.Basis I R M) (deg : I → A) (a : A) : M →ₗ[R] M :=
  b.repr.symm.toLinearMap ∘ₗ filterMap (fun i => deg i = a) ∘ₗ
    b.repr.toLinearMap

@[simp] lemma projection_basis (b : Module.Basis I R M) (deg : I → A) (a : A) (i : I) :
    projection b deg a (b i) = if deg i = a then b i else 0 := by
  by_cases h : deg i = a
  · simp [projection, h, Finsupp.filter_single_of_pos]
  · simp [projection, h, Finsupp.filter_single_of_neg]

lemma projection_mem (b : Module.Basis I R M) (deg : I → A) (a : A) (x : M) :
    projection b deg a x ∈ Piece b deg a := by
  rw [mem_piece]
  intro i hi
  simp only [projection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, filterMap_apply,
    Finsupp.filter_apply] at hi
  split_ifs at hi with h
  · exact h
  · exact (hi rfl).elim

lemma projection_eq_self {b : Module.Basis I R M} {deg : I → A} {a : A} {x : M}
    (hx : x ∈ Piece b deg a) : projection b deg a x = x := by
  apply b.repr.injective
  simp only [projection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  ext i
  simp only [filterMap_apply, Finsupp.filter_apply]
  by_cases hi : deg i = a
  · simp [hi]
  · have hz : b.repr x i = 0 := by
      by_contra hn
      exact hi ((mem_piece b deg a x).mp hx i hn)
    simp [hi, hz]

lemma projection_eq_zero {b : Module.Basis I R M} {deg : I → A} {a c : A}
    (h : a ≠ c) {x : M} (hx : x ∈ Piece b deg c) : projection b deg a x = 0 := by
  apply b.repr.injective
  simp only [projection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, map_zero]
  ext i
  simp only [filterMap_apply, Finsupp.filter_apply, Finsupp.zero_apply]
  split_ifs with hi
  · by_contra hn
    exact h (hi.symm.trans ((mem_piece b deg c x).mp hx i hn))
  · rfl

/-- Every actual vector is the finite sum of its homogeneous components. -/
lemma sum_projections [DecidableEq A] (b : Module.Basis I R M) (deg : I → A) (x : M) :
    ∑ a ∈ (b.repr x).support.image deg, projection b deg a x = x := by
  apply b.repr.injective
  simp only [map_sum, projection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  ext i
  simp only [Finsupp.finset_sum_apply, filterMap_apply, Finsupp.filter_apply]
  by_cases hi : b.repr x i = 0
  · simp [hi]
  · have hm : deg i ∈ (b.repr x).support.image deg :=
      Finset.mem_image.mpr ⟨i, Finsupp.mem_support_iff.mpr hi, rfl⟩
    rw [Finset.sum_eq_single (deg i)]
    · simp
    · intro a ha hne
      simp [Ne.symm hne]
    · intro hnot
      exact (hnot hm).elim

end CommAlg.Grading
end
