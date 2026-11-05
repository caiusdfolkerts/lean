module

public import PaperVerification.FermionAssociatedGraded
public import PaperVerification.FermionFilteredInitial
public import PaperVerification.FermionQuotientDegreeBasis

/-!
# Actual multiplication and leading terms in a homogeneous algebra basis

The basis product hypothesis is used to prove bounded multiplication and the
formula for the leading component of a product.  The quotient filtration is
then the image of the actual bounded ambient submodules.

-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.Fermion.BasisFiltered

open scoped BigOperators

variable {R A Q I : Type*} [CommRing R] [Ring A] [Algebra R A]
  [Ring Q] [Algebra R Q] (b : Module.Basis I R A) (w : I → ℕ)

theorem sum_support_repr (x : A) :
    (∑ i ∈ (b.repr x).support,b.repr x i • b i)=x := by
  simpa only [Finsupp.linearCombination_apply,Finsupp.sum] using b.linearCombination_repr x

theorem bound_sum {J : Type*} (S : Finset J) (x : J → A) (d : ℕ)
    (hx : ∀ j ∈ S,Bound b w d (x j)) : Bound b w d (∑ j ∈ S,x j) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using bound_zero b w d
  | @insert j S hj ih =>
      rw [Finset.sum_insert hj]
      exact bound_add b w (hx j (Finset.mem_insert_self _ _))
        (ih (fun k hk ↦ hx k (Finset.mem_insert_of_mem hk)))

theorem bound_mul
    (hmul : ∀ i j,Homogeneous b w (w i+w j) (b i*b j))
    {d e : ℕ} {x y : A} (hx : Bound b w d x) (hy : Bound b w e y) :
    Bound b w (d+e) (x*y) := by
  classical
  rw [← sum_support_repr b x,← sum_support_repr b y,Finset.sum_mul]
  apply bound_sum b w _ _ _
  intro i hi
  rw [Finset.mul_sum]
  apply bound_sum b w _ _ _
  intro j hj
  rw [smul_mul_smul_comm]
  apply bound_smul b w
  apply bound_mono b w
    (Nat.add_le_add (hx i (Finsupp.mem_support_iff.mp hi)) (hy j (Finsupp.mem_support_iff.mp hj)))
  exact homogeneous_bound b w (hmul i j)

theorem component_mul_top
    (hmul : ∀ i j,Homogeneous b w (w i+w j) (b i*b j))
    {d e : ℕ} {x y : A} (hx : Bound b w d x) (hy : Bound b w e y) :
    component b w (d+e) (x*y)=component b w d x*component b w e y := by
  classical
  conv_lhs => rw [← sum_support_repr b x,← sum_support_repr b y]
  conv_rhs => rw [← sum_support_repr b x,← sum_support_repr b y]
  simp only [Finset.sum_mul,Finset.mul_sum,map_sum,map_smul,smul_mul_smul_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  have hid := hx i (Finsupp.mem_support_iff.mp hi)
  have hje := hy j (Finsupp.mem_support_iff.mp hj)
  rw [component_of_homogeneous b w (hmul i j),
    component_of_homogeneous b w (homogeneous_basis b w i),
    component_of_homogeneous b w (homogeneous_basis b w j)]
  by_cases hd : d=w i <;> by_cases he : e=w j
  · simp only [hd,he,if_true]
  · have hn : d+e ≠ w i+w j := by omega
    simp only [hd,if_true,Nat.add_left_cancel_iff,if_neg he,mul_zero,smul_zero]
  · have hn : d+e ≠ w i+w j := by omega
    simp only [he,if_true,Nat.add_right_cancel_iff,if_neg hd,zero_mul,smul_zero]
  · have hn : d+e ≠ w i+w j := by omega
    simp only [if_neg hd,if_neg he,if_neg hn,zero_mul,smul_zero]

def boundPiece (d : ℕ) : Submodule R A where
  carrier := {x | Bound b w d x}
  zero_mem' := bound_zero b w d
  add_mem' := bound_add b w
  smul_mem' := fun c x hx ↦ bound_smul b w hx c

theorem boundPiece_mono : Monotone (boundPiece b w) :=
  fun _ _ h _ hx ↦ bound_mono b w h hx

/-- The actual quotient filtration is obtained from the ambient weighted
monomial bounds by the original quotient algebra homomorphism. -/
def quotientFiltration (q : A →ₐ[R] Q)
    (hone : Homogeneous b w 0 (1 : A))
    (hmul : ∀ i j,Homogeneous b w (w i+w j) (b i*b j)) :
    FilteredAlgebra.Filtration R Q where
  piece d := (boundPiece b w d).map q.toLinearMap
  mono := fun _ _ h ↦ Submodule.map_mono (boundPiece_mono b w h)
  one_mem := ⟨1,homogeneous_bound b w hone,map_one q⟩
  mul_mem := by
    rintro i j x y ⟨a,ha,rfl⟩ ⟨c,hc,rfl⟩
    exact ⟨a*c,bound_mul b w hmul ha hc,map_mul q a c⟩

end PaperVerification.Fermion.BasisFiltered
