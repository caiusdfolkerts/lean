module

public import PaperVerification.FermionTensorSupercommutative

/-!
# Finite signed tensor products and their universal property

The construction recursively uses Mathlib's genuine graded tensor ring.
The maps preserve its proved natural grading. The finite universal property
is proved by induction from the binary signed universal property.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped TensorProduct

namespace PaperVerification.Fermion

universe u
variable {F : Type u} [Field F]

structure NGradedHom (A B : NGradedAlgebra F) where
  toAlgHom : A.Carrier →ₐ[F] B.Carrier
  degree : ∀ i a,a∈A.part i → toAlgHom a∈B.part i

namespace NGradedHom

def id (A : NGradedAlgebra F) : NGradedHom A A :=
  ⟨AlgHom.id F A.Carrier,fun _ _ ha ↦ ha⟩

def comp {A B C : NGradedAlgebra F} (f : NGradedHom B C) (g : NGradedHom A B) :
    NGradedHom A C :=
  ⟨f.toAlgHom.comp g.toAlgHom,fun i a ha ↦ f.degree i _ (g.degree i a ha)⟩

def includeLeft (A B : NGradedAlgebra F) :
    NGradedHom A (NGradedAlgebra.tensor F A B) :=
  ⟨GradedTensorProduct.includeLeft A.part B.part,
    fun _ _ ha ↦ gradedTensor_includeLeft_degree A.part B.part ha⟩

def includeRight (A B : NGradedAlgebra F) :
    NGradedHom B (NGradedAlgebra.tensor F A B) :=
  ⟨GradedTensorProduct.includeRight A.part B.part,
    fun _ _ hb ↦ gradedTensor_includeRight_degree A.part B.part hb⟩

def tensorLift (A B C : NGradedAlgebra F) (hC : IsSupercommutative C.part)
    (f : NGradedHom A C) (g : NGradedHom B C) :
    NGradedHom (NGradedAlgebra.tensor F A B) C := by
  have hc : ∀ ⦃i j⦄ (a : A.part i) (b : B.part j),
      f.toAlgHom a*g.toAlgHom b=(-1 : ℤˣ)^(j*i) • (g.toAlgHom b*f.toAlgHom a) :=
    fun i j a b ↦ hC i j ⟨f.toAlgHom a,f.degree i a a.property⟩
      ⟨g.toAlgHom b,g.degree j b b.property⟩
  exact ⟨GradedTensorProduct.lift A.part B.part f.toAlgHom g.toAlgHom hc,
    fun _ _ hx ↦ gradedTensor_lift_degree A.part B.part C.part
      f.toAlgHom g.toAlgHom f.degree g.degree hc hx⟩

@[simp] theorem tensorLift_left (A B C : NGradedAlgebra F)
    (hC : IsSupercommutative C.part) (f : NGradedHom A C) (g : NGradedHom B C)
    (a : A.Carrier) :
    (tensorLift A B C hC f g).toAlgHom ((includeLeft A B).toAlgHom a)=f.toAlgHom a := by
  change f.toAlgHom a*g.toAlgHom 1=f.toAlgHom a
  rw [map_one,mul_one]

@[simp] theorem tensorLift_right (A B C : NGradedAlgebra F)
    (hC : IsSupercommutative C.part) (f : NGradedHom A C) (g : NGradedHom B C)
    (b : B.Carrier) :
    (tensorLift A B C hC f g).toAlgHom ((includeRight A B).toAlgHom b)=g.toAlgHom b := by
  change f.toAlgHom 1*g.toAlgHom b=g.toAlgHom b
  rw [map_one,one_mul]

end NGradedHom

namespace NGradedAlgebra

theorem scalar_part_eq_bot {n : ℕ} (hn : n≠0) :
    (scalar F).part n=⊥ := by
  apply Submodule.span_eq_bot.mpr
  rintro x ⟨i,hi,hix⟩
  exact False.elim (hn hi.symm)

theorem scalar_supercommutative : IsSupercommutative (scalar F).part := by
  intro i j a b
  change (a.val : F)*(b.val : F)=(-1 : ℤˣ)^(j*i) • ((b.val : F)*(a.val : F))
  by_cases hi : i=0
  · subst i
    simpa only [Nat.mul_zero,pow_zero,one_smul] using @mul_comm F _ (a.val : F) (b.val : F)
  · have ha : (a.val : F)=0 := (scalar_part_eq_bot hi).le a.property
    simp [ha]

def scalarHom (C : NGradedAlgebra F) : NGradedHom (scalar F) C where
  toAlgHom := by
    change F →ₐ[F] C.Carrier
    exact Algebra.ofId F C.Carrier
  degree := by
    intro i a ha
    let a' : F := a
    change algebraMap F C.Carrier a'∈C.part i
    by_cases hi : i=0
    · subst i
      rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ a' (SetLike.one_mem_graded C.part)
    · have hz : a'=0 := (scalar_part_eq_bot hi).le ha
      rw [hz,map_zero]
      exact Submodule.zero_mem _

def tensorFin : {n : ℕ} → (Fin n → NGradedAlgebra F) → NGradedAlgebra F
  | 0,_ => scalar F
  | n+1,A => tensor F (A 0) (tensorFin (fun i : Fin n ↦ A i.succ))

def tensorFinInclude : {n : ℕ} → (A : Fin n → NGradedAlgebra F) →
    (i : Fin n) → NGradedHom (A i) (tensorFin A)
  | 0,_,i => Fin.elim0 i
  | n+1,A,i => Fin.cases
      (NGradedHom.includeLeft (A 0) (tensorFin (fun j : Fin n ↦ A j.succ)))
      (fun j ↦ (NGradedHom.includeRight (A 0) (tensorFin (fun k : Fin n ↦ A k.succ))).comp
        (tensorFinInclude (fun k : Fin n ↦ A k.succ) j)) i

@[simp] theorem tensorFinInclude_zero {n : ℕ} (A : Fin (n+1) → NGradedAlgebra F) :
    (tensorFinInclude A 0).toAlgHom=
      (NGradedHom.includeLeft (A 0) (tensorFin (fun j : Fin n ↦ A j.succ))).toAlgHom := rfl

@[simp] theorem tensorFinInclude_succ {n : ℕ} (A : Fin (n+1) → NGradedAlgebra F)
    (i : Fin n) :
    (tensorFinInclude A i.succ).toAlgHom=
      (NGradedHom.includeRight (A 0) (tensorFin (fun j : Fin n ↦ A j.succ))).toAlgHom.comp
        (tensorFinInclude (fun j : Fin n ↦ A j.succ) i).toAlgHom := rfl

def tensorFinLift : {n : ℕ} → (A : Fin n → NGradedAlgebra F) →
    (C : NGradedAlgebra F) → IsSupercommutative C.part →
    (∀ i,NGradedHom (A i) C) → NGradedHom (tensorFin A) C
  | 0,_,C,_,_ => scalarHom C
  | n+1,A,C,hC,f =>
      NGradedHom.tensorLift (A 0) (tensorFin (fun i : Fin n ↦ A i.succ)) C hC (f 0)
        (tensorFinLift (fun i : Fin n ↦ A i.succ) C hC (fun i ↦ f i.succ))

@[simp] theorem tensorFinLift_include {n : ℕ} (A : Fin n → NGradedAlgebra F)
    (C : NGradedAlgebra F) (hC : IsSupercommutative C.part)
    (f : ∀ i,NGradedHom (A i) C) (i : Fin n) (a : (A i).Carrier) :
    (tensorFinLift A C hC f).toAlgHom ((tensorFinInclude A i).toAlgHom a)=
      (f i).toAlgHom a := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      rcases Fin.eq_zero_or_eq_succ i with rfl|⟨j,rfl⟩
      · exact NGradedHom.tensorLift_left _ _ _ _ _ _ a
      · exact (NGradedHom.tensorLift_right (A 0)
          (tensorFin (fun k : Fin n ↦ A k.succ)) C hC (f 0)
          (tensorFinLift (fun k : Fin n ↦ A k.succ) C hC (fun k ↦ f k.succ))
          ((tensorFinInclude (fun k : Fin n ↦ A k.succ) j).toAlgHom a)).trans
            (ih (fun k : Fin n ↦ A k.succ) (fun k ↦ f k.succ) j a)

theorem tensorFin_hom_ext {n : ℕ} (A : Fin n → NGradedAlgebra F)
    {C : Type*} [Ring C] [Algebra F C]
    {f g : (tensorFin A).Carrier →ₐ[F] C}
    (h : ∀ i,f.comp (tensorFinInclude A i).toAlgHom=
      g.comp (tensorFinInclude A i).toAlgHom) : f=g := by
  induction n with
  | zero =>
      apply AlgHom.ext
      intro a
      exact (f.commutes a).trans (g.commutes a).symm
  | succ n ih =>
      apply GradedTensorProduct.algHom_ext
      · exact h 0
      · apply ih (fun i : Fin n ↦ A i.succ)
        intro i
        exact h i.succ

theorem tensorFin_supercommutative {n : ℕ} (A : Fin n → NGradedAlgebra F)
    (hA : ∀ i,IsSupercommutative (A i).part) :
    IsSupercommutative (tensorFin A).part := by
  induction n with
  | zero => exact scalar_supercommutative
  | succ n ih =>
      exact gradedTensor_supercommutative (A 0).part
        (tensorFin (fun i : Fin n ↦ A i.succ)).part (hA 0)
        (ih (fun i : Fin n ↦ A i.succ) (fun i ↦ hA i.succ))

end NGradedAlgebra
end PaperVerification.Fermion

