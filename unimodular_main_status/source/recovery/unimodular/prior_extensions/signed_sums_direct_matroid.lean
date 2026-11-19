/- The one-sum realizes Mathlib's ordinary direct sum of matroids. -/
module
public import Recovery.Unimodular.PriorExtensions.SignedSumsDirect
public import Recovery.Unimodular.PriorExtensions.SignedSumsMatroid
public import Mathlib.Combinatorics.Matroid.Sum
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Unimodular.SignedSums

def directVectors {K L R M N : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (U : L → M) (V : R → N) : L ⊕ R → M × N :=
  Sum.elim (fun l => (U l, 0)) (fun r => (0, V r))

theorem directVectors_independent {K L R M N : Type*} [Field K]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (U : L → M) (V : R → N) :
    LinearIndependent K (directVectors (K := K) U V) ↔
      LinearIndependent K U ∧ LinearIndependent K V := by
  have hl : LinearIndependent K (fun l => (U l, (0 : N))) ↔ LinearIndependent K U :=
    (LinearMap.inl K M N).linearIndependent_iff_of_injOn
      (fun x _ y _ h => congrArg Prod.fst h)
  have hr : LinearIndependent K (fun r => ((0 : M), V r)) ↔ LinearIndependent K V :=
    (LinearMap.inr K M N).linearIndependent_iff_of_injOn
      (fun x _ y _ h => congrArg Prod.snd h)
  have hleft : Submodule.span K (Set.range (fun l => (U l, (0 : N)))) ≤
      LinearMap.ker (LinearMap.snd K M N) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨l, rfl⟩
    rfl
  have hright : Submodule.span K (Set.range (fun r => ((0 : M), V r))) ≤
      LinearMap.ker (LinearMap.fst K M N) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨r, rfl⟩
    rfl
  have hd : Disjoint (Submodule.span K (Set.range (fun l => (U l, (0 : N)))))
      (Submodule.span K (Set.range (fun r => ((0 : M), V r)))) := by
    apply Submodule.disjoint_def.mpr
    intro x hx hy
    exact Prod.ext (hright hy) (hleft hx)
  change LinearIndependent K (Sum.elim (fun l => (U l, (0 : N)))
    (fun r => ((0 : M), V r))) ↔ _
  rw [linearIndependent_sum]
  change (LinearIndependent K (fun l => (U l, (0 : N))) ∧
    LinearIndependent K (fun r => ((0 : M), V r)) ∧
      Disjoint (Submodule.span K (Set.range (fun l => (U l, (0 : N)))))
        (Submodule.span K (Set.range (fun r => ((0 : M), V r))))) ↔ _
  rw [hl, hr]
  simp [hd]

/-- Literal ordinary matroid one-sum for all independent subsets. -/
theorem directVectors_matroid {K L R M N : Type*} [Field K]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (U : L → M) (V : R → N) :
    VectorMatroid.ofFamily (K := K) (directVectors (K := K) U V) =
      (VectorMatroid.ofFamily (K := K) U).sum (VectorMatroid.ofFamily (K := K) V) := by
  apply Matroid.ext_indep (by ext j; cases j <;> simp)
  intro S hS
  rw [VectorMatroid.ofFamily_indep, Matroid.sum_indep_iff,
    VectorMatroid.ofFamily_indep, VectorMatroid.ofFamily_indep]
  let e : S ≃ {l : L // Sum.inl l ∈ S} ⊕ {r : R // Sum.inr r ∈ S} := Equiv.subtypeSum
  change LinearIndependent K (fun j : S => directVectors (K := K) U V j.val) ↔ _
  rw [← linearIndependent_equiv e.symm]
  have he : (fun j : S => directVectors (K := K) U V j.val) ∘ e.symm =
      directVectors (K := K) (fun l : {l : L // Sum.inl l ∈ S} => U l.val)
        (fun r : {r : R // Sum.inr r ∈ S} => V r.val) := by
    funext j
    cases j <;> rfl
  rw [he, directVectors_independent]
  rfl

/-- All literal one-sum conclusions together, including the ordinary
matroid direct sum of the actual real embeddings of the input columns. -/
theorem proposition_2_2_one_sum_complete {n₁ n₂ : ℕ} {L R : Type*}
    (U : L → Lattice n₁) (V : R → Lattice n₂)
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n₁)) U)
    (hV : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n₂)) V)
    (hspanU : Submodule.span ℝ (Set.range (fun l => embed (U l))) = ⊤)
    (hspanV : Submodule.span ℝ (Set.range (fun l => embed (V l))) = ⊤) :
    (∃ b : Module.Basis (Fin (n₁+n₂)) ℤ (Lattice n₁ × Lattice n₂),
      IntegralRigidity.Uniform b (directFamily U V) ∧
      Submodule.span ℤ (Set.range (directFamily U V)) = ⊤ ∧
      Matrix.IsTotallyUnimodular (fun i j => b.repr (directFamily U V j) i)) ∧
    VectorMatroid.ofFamily (K := ℝ)
      (directVectors (K := ℝ) (fun l => embed (U l)) (fun r => embed (V r))) =
      (VectorMatroid.ofFamily (K := ℝ) (fun l => embed (U l))).sum
        (VectorMatroid.ofFamily (K := ℝ) (fun r => embed (V r))) :=
  ⟨proposition_2_2_one_sum U V hU hV hspanU hspanV, directVectors_matroid _ _⟩

end Unimodular.SignedSums
#print axioms Unimodular.SignedSums.directVectors_matroid
#print axioms Unimodular.SignedSums.proposition_2_2_one_sum_complete
