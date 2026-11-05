module

public import PaperVerification.FermionMultigradedTensor
public import PaperVerification.FermionFiniteTensorUniversal

/-!
# Natural bigradings of finite genuine signed tensor products

-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical TensorProduct

namespace PaperVerification.Fermion

def totalBidegree : (ℕ×ℕ) →+ ℕ where
  toFun g := g.1+g.2
  map_zero' := rfl
  map_add' g h := by change (g.1+h.1)+(g.2+h.2)=(g.1+g.2)+(h.1+h.2); omega

universe u
variable {F : Type u} [Field F]

namespace NGradedAlgebra

structure Bigrading (A : NGradedAlgebra F) where
  part : (ℕ×ℕ) → Submodule F A.Carrier
  [graded : GradedAlgebra part]
  total : ∀ g,part g≤A.part (totalBidegree g)

attribute [instance] Bigrading.graded

namespace Bigrading

def scalar : Bigrading (NGradedAlgebra.scalar F) where
  part := basisDegreePart (Module.Basis.singleton Unit F) (fun _ ↦ (0,0))
  graded := basisDegreeGradedAlgebra (Module.Basis.singleton Unit F) (fun _ ↦ (0,0))
    (by
      apply Submodule.subset_span
      refine ⟨(),rfl,?_⟩
      simp)
    (by
      intro i j
      apply Submodule.subset_span
      refine ⟨(),rfl,?_⟩
      simp)
  total g := by
    apply Submodule.span_le.mpr
    rintro x ⟨i,hi,rfl⟩
    change (0,0)=g at hi
    subst g
    apply Submodule.subset_span
    exact ⟨i,rfl,rfl⟩

theorem scalar_part_eq_bot {g : ℕ×ℕ} (hg : g≠0) :
    (scalar (F := F)).part g=⊥ := by
  apply Submodule.span_eq_bot.mpr
  rintro x ⟨i,hi,hix⟩
  exact False.elim (hg hi.symm)

def tensor {A B : NGradedAlgebra F} (qA : Bigrading A) (qB : Bigrading B) :
    Bigrading (NGradedAlgebra.tensor F A B) where
  part := naturalMultigradedTensorPart A.part B.part qA.part qB.part
  graded := naturalMultigradedTensorAlgebra A.part B.part qA.part qB.part
    totalBidegree qA.total qB.total
  total := naturalMultigradedTensorPart_total A.part B.part qA.part qB.part
    totalBidegree qA.total qB.total

def tensorFin : {n : ℕ} → (A : Fin n → NGradedAlgebra F) →
    (∀ i,Bigrading (A i)) → Bigrading (NGradedAlgebra.tensorFin A)
  | 0,_,_ => scalar
  | n+1,A,q => tensor (q 0)
      (tensorFin (fun i : Fin n ↦ A i.succ) (fun i ↦ q i.succ))

theorem tensorFinInclude_bidegree {n : ℕ} (A : Fin n → NGradedAlgebra F)
    (q : ∀ i,Bigrading (A i)) (i : Fin n) {g : ℕ×ℕ} {a : (A i).Carrier}
    (ha : a∈(q i).part g) :
    (NGradedAlgebra.tensorFinInclude A i).toAlgHom a∈(tensorFin A q).part g := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      rcases Fin.eq_zero_or_eq_succ i with h|⟨j,h⟩
      · subst i
        exact multigradedTensor_includeLeft _ _ _ _ ha
      · subst i
        change GradedTensorProduct.includeRight (A 0).part
          (NGradedAlgebra.tensorFin (fun k : Fin n ↦ A k.succ)).part
          ((NGradedAlgebra.tensorFinInclude (fun k : Fin n ↦ A k.succ) j).toAlgHom a)∈_
        exact multigradedTensor_includeRight _ _ _ _
          (ih (fun k : Fin n ↦ A k.succ) (fun k ↦ q k.succ) j ha)

theorem scalarHom_bidegree (C : NGradedAlgebra F) (qC : Bigrading C)
    {g : ℕ×ℕ} {a : F} (ha : a∈(scalar (F := F)).part g) :
    (NGradedAlgebra.scalarHom C).toAlgHom a∈qC.part g := by
  by_cases hg : g=0
  · subst g
    change algebraMap F C.Carrier a∈qC.part 0
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ a (SetLike.one_mem_graded qC.part)
  · rw [scalar_part_eq_bot hg] at ha
    change a=0 at ha
    rw [ha,map_zero]
    exact Submodule.zero_mem _

theorem tensorLift_bidegree {A B C : NGradedAlgebra F}
    (qA : Bigrading A) (qB : Bigrading B) (qC : Bigrading C)
    (hC : IsSupercommutative C.part) (f : NGradedHom A C) (g : NGradedHom B C)
    (hf : ∀ d a,a∈qA.part d → f.toAlgHom a∈qC.part d)
    (hg : ∀ d b,b∈qB.part d → g.toAlgHom b∈qC.part d)
    {d : ℕ×ℕ} {x : (NGradedAlgebra.tensor F A B).Carrier}
    (hx : x∈(tensor qA qB).part d) :
    (NGradedHom.tensorLift A B C hC f g).toAlgHom x∈qC.part d :=
  multigradedTensor_lift A.part B.part qA.part qB.part qC.part
    f.toAlgHom g.toAlgHom hf hg
    (fun i j a b ↦ hC i j ⟨f.toAlgHom a,f.degree i a a.property⟩
      ⟨g.toAlgHom b,g.degree j b b.property⟩) hx

theorem tensorFinLift_bidegree {n : ℕ} (A : Fin n → NGradedAlgebra F)
    (q : ∀ i,Bigrading (A i)) (C : NGradedAlgebra F) (qC : Bigrading C)
    (hC : IsSupercommutative C.part) (f : ∀ i,NGradedHom (A i) C)
    (hf : ∀ i d a,a∈(q i).part d → (f i).toAlgHom a∈qC.part d)
    {d : ℕ×ℕ} {x : (NGradedAlgebra.tensorFin A).Carrier}
    (hx : x∈(tensorFin A q).part d) :
    (NGradedAlgebra.tensorFinLift A C hC f).toAlgHom x∈qC.part d := by
  induction n generalizing d with
  | zero => exact scalarHom_bidegree C qC hx
  | succ n ih =>
      exact tensorLift_bidegree (q 0)
        (tensorFin (fun i : Fin n ↦ A i.succ) (fun i ↦ q i.succ))
        qC hC (f 0)
        (NGradedAlgebra.tensorFinLift (fun i : Fin n ↦ A i.succ) C hC (fun i ↦ f i.succ))
        (hf 0)
        (fun d y hy ↦ ih (fun i : Fin n ↦ A i.succ) (fun i ↦ q i.succ)
          (fun i ↦ f i.succ) (fun i ↦ hf i.succ) hy) hx

end Bigrading
end NGradedAlgebra
end PaperVerification.Fermion

