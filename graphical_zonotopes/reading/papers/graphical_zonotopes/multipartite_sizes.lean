module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic.NormNum
public import Lean.Elab.Tactic.Omega

@[expose] public section
namespace GraphicalZonotopes
namespace BooleanModule
namespace SmallCount

def crossCount (sizes : List ℕ) : ℕ :=
  sizes.sum.choose 2-(sizes.map (fun a => a.choose 2)).sum

/-- Every pair count up to `s.choose 2` is realized by positive multipartite
block sizes using at most `s` vertices. The unused vertices are isolated in
the response pattern, but will remain essential in its Boolean module. -/
theorem exists_multipartite_sizes (s m : ℕ) (hm : m≤s.choose 2) :
    ∃ sizes : List ℕ,(∀ a∈sizes,0<a) ∧ sizes.sum≤s ∧ crossCount sizes=m := by
  induction s with
  | zero =>
    have hm0 : m=0:=by simpa using hm
    subst m
    exact ⟨[],by simp,by simp,by simp [crossCount]⟩
  | succ s ih =>
    by_cases hsmall : m≤s.choose 2
    · obtain ⟨sizes,hpos,hsize,hcount⟩:=ih hsmall
      exact ⟨sizes,hpos,hsize.trans (Nat.le_succ s),hcount⟩
    · have hchoose : (s+1).choose 2=s.choose 2+s := by
        calc
          (s+1).choose 2=s.choose 1+s.choose 2 := Nat.choose_succ_succ' s 1
          _=s.choose 2+s := by rw [Nat.choose_one_right,Nat.add_comm]
      let j:=(s+1).choose 2-m
      let q:=j/3
      let r:=j%3
      have hdecomp : j=3*q+r:=by
        dsimp only [q,r]
        exact (Nat.div_add_mod j 3).symm
      have hr : r<3:=Nat.mod_lt _ (by decide)
      have hj : j<s := by
        dsimp only [j]
        rw [hchoose]
        omega
      have hused : 3*q+2*r≤s+1 := by omega
      let a:=s+1-(3*q+2*r)
      let sizes : List ℕ:=List.replicate q 3++List.replicate r 2++List.replicate a 1
      have hsum : sizes.sum=s+1 := by
        simp only [sizes,List.sum_append,List.sum_replicate,nsmul_eq_mul,Nat.cast_id,Nat.mul_one]
        dsimp only [a]
        omega
      have hinside : (sizes.map (fun n => n.choose 2)).sum=j := by
        simpa only [sizes,List.map_append,List.map_replicate,List.sum_append,
          List.sum_replicate,nsmul_eq_mul,
          show (3 : ℕ).choose 2=3 from by decide,
          show (2 : ℕ).choose 2=1 from by decide,
          show (1 : ℕ).choose 2=0 from by decide,
          Nat.cast_id,Nat.mul_one,Nat.mul_zero,Nat.one_mul,Nat.zero_mul,Nat.add_zero,Nat.mul_comm] using hdecomp.symm
      refine ⟨sizes,?_,by omega,?_⟩
      · intro b hb
        simp only [sizes,List.mem_append,List.mem_replicate] at hb
        rcases hb with (⟨_,rfl⟩ | ⟨_,rfl⟩) | ⟨_,rfl⟩ <;> omega
      · rw [crossCount,hsum,hinside]
        dsimp only [j]
        omega

end SmallCount
end BooleanModule
end GraphicalZonotopes
