module

public import PaperVerification.GradedComponentBasis

/-!
# Coefficients of an actual homogeneous basis

Projection to a graded piece keeps exactly the basis coordinates with
that degree. The grading is the supplied genuine direct-sum decomposition;
the result does not assign a grading retrospectively to a desired basis.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.GradedComponentBasis

variable {K V I : Type*} {D : Type} [Field K] [AddCommGroup V] [Module K V]
  [DecidableEq D]
  (G : TauCeti.InternalGrading K V D) (B : Module.Basis I K V)
  (degree : I → D) (hhom : ∀ i,B i∈G.piece (degree i))

include hhom in
theorem repr_projection (p : D) (x : V) (i : I) :
    B.repr (projection G p x) i=if degree i=p then B.repr x i else 0 := by
  classical
  have hx := B.mem_span x
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨j,rfl⟩ := hx
      by_cases hji : j=i
      · subst j
        by_cases hi : degree i=p
        · rw [projection_of_mem G p _ (hi ▸ hhom i),if_pos hi]
        · rw [projection_of_mem_ne G p (degree i) _ (hhom i) hi,if_neg hi]
          simp only [map_zero,Finsupp.zero_apply]
      · by_cases hj : degree j=p
        · rw [projection_of_mem G p _ (hj ▸ hhom j),B.repr_self,
            Finsupp.single_eq_of_ne (Ne.symm hji)]
          split_ifs <;> rfl
        · rw [projection_of_mem_ne G p (degree j) _ (hhom j) hj,
            map_zero,Finsupp.zero_apply,B.repr_self,Finsupp.single_eq_of_ne (Ne.symm hji)]
          split_ifs <;> rfl
  | zero => simp only [map_zero,Finsupp.zero_apply,ite_self]
  | add x y hx hy ihx ihy =>
      rw [map_add,map_add,Finsupp.add_apply,ihx,ihy,map_add,Finsupp.add_apply]
      split_ifs <;> simp only [add_zero]
  | smul c x hx ih =>
      rw [map_smul,map_smul,Finsupp.smul_apply,ih,map_smul,Finsupp.smul_apply]
      split_ifs <;> simp only [smul_zero]

include hhom in
theorem repr_eq_zero_of_degree_ne (p : D) (x : V) (hx : x∈G.piece p)
    (i : I) (hi : degree i≠p) : B.repr x i=0 := by
  have h := repr_projection G B degree hhom p x i
  rwa [projection_of_mem G p x hx,if_neg hi] at h

end PaperVerification.GradedComponentBasis
