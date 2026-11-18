module

public import Papers.GraphicalZonotopes.PathJoinTightEquations

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.PathJoin
open Finset
open scoped BigOperators

theorem tight_n_constant {n : ℕ} {f : SetFunction (Vertex n)} (h : TightOn f)
    (j : Fin (n+1)) : nCoeff f j=nCoeff f 0 := by
  refine Fin.induction rfl (fun k ih => ?_) j
  have hr := tight_near_right h k.castSucc
  have hl := tight_near_left h k.succ
  have hk : k.succ.castSucc≠0 := by simp [Fin.ext_iff]
  rw [nearSpoke_eq_a h _ _ (Fin.succ_ne_zero _)] at hr
  rw [nearSpoke_eq_a h _ _ hk,←consecutive_middle] at hl
  linarith

theorem tight_z_zero {n : ℕ} {f : SetFunction (Vertex n)}
    (hn : TranslationNormalized f) (h : TightOn f) (j : Fin (n+1)) : zCoeff f j=0 := by
  refine Fin.cases (tight_first_z h) (fun k => ?_) j
  have htwo := tight_two_neighbors hn h k
  have hone := tight_near_right h k.castSucc
  linarith

theorem tight_nonhub_coordinates {n : ℕ} {f : SetFunction (Vertex n)}
    (hn : TranslationNormalized f) (h : TightOn f) :
    ∃ t : ℝ,
      (∀ i : Fin (n+2),aCoeff f i=t ∧
        bCoeff f i=(if i=0 then 0 else t) ∧ eCoeff f i=(if i=0 then 0 else -t)) ∧
      (∀ j : Fin (n+1),dCoeff f j=t ∧
        taCoeff f j=(if j.val%2=0 then -t else 0) ∧
        tbCoeff f j=(if j.val%2=0 then 0 else -t) ∧ hCoeff f j=t) := by
  let t := -nCoeff f (0 : Fin (n+1))
  have hnval (j : Fin (n+1)) : nCoeff f j= -t := by
    rw [tight_n_constant h]
    dsimp [t]
    ring
  have hpos (i : Fin (n+2)) (hi : i≠0) :
      aCoeff f i=t ∧ bCoeff f i=t ∧ eCoeff f i= -t := by
    obtain ⟨j,rfl⟩ := Fin.exists_succ_eq.mpr hi
    have hr := tight_near_right h j
    rw [nearSpoke_eq_a h _ _ (Fin.succ_ne_zero _),hnval] at hr
    have hae := tight_a_e h j.succ (Fin.succ_ne_zero _)
    have hbe := tight_b_e h j.succ (Fin.succ_ne_zero _)
    constructor
    · linarith
    constructor <;> linarith
  have ha0 : aCoeff f (0 : Fin (n+2))=t := by
    have hl := tight_near_left h (0 : Fin (n+1))
    rw [hnval] at hl
    simp only [nearSpoke,Fin.val_zero,Nat.zero_mod,ite_true,Fin.castSucc_zero] at hl
    linarith
  refine ⟨t,?_,?_⟩
  · intro i
    by_cases hi : i=0
    · subst i
      simp only [ite_true]
      exact ⟨ha0,tight_first_b h,tight_first_e h⟩
    · simpa only [hi,ite_false] using hpos i hi
  · intro j
    have hd := tight_path_near h j
    rw [hnval] at hd
    have hr := tight_near_right_hub h j
    rw [nearSpoke_eq_a h _ _ (Fin.succ_ne_zero _),
      (hpos j.succ (Fin.succ_ne_zero _)).1,
      (hpos j.succ (Fin.succ_ne_zero _)).2.2,hnval] at hr
    have hz := tight_z_zero hn h j
    have hv := hnval j
    refine ⟨by linarith,?_,?_,by linarith⟩
    all_goals by_cases he : j.val%2=0 <;>
      simp only [nCoeff,zCoeff,he,ite_true,ite_false] at hv hz ⊢ <;> assumption

theorem polynomial_add {n : ℕ} (x y : Slot n → ℝ) :
    FiniteMonomial.polynomial clique (x+y)=
      FiniteMonomial.polynomial clique x+FiniteMonomial.polynomial clique y := by
  simp only [FiniteMonomial.polynomial,Pi.add_apply,add_smul,Finset.sum_add_distrib]

theorem polynomial_single {n : ℕ} (s : Slot n) (a : ℝ) :
    FiniteMonomial.polynomial clique (Pi.single s a)=a • setMonomial (clique s) := by
  classical
  unfold FiniteMonomial.polynomial
  rw [Finset.sum_eq_single s]
  · simp
  · intro j hj hjs
    simp [Pi.single_apply,hjs,Ne.symm hjs]
  · simp

/-- Every solution of all tight equations is a scalar multiple of the
displayed polynomial. The quantified test function is arbitrary; its
graphical support is derived from the nonedge tight equations.
-/
theorem complete_tight_kernel {n : ℕ} (f : SetFunction (Vertex n))
    (hn : TranslationNormalized f) (h : TightOn f) :
    ∃ t : ℝ,f=t • setFunction n := by
  obtain ⟨t,hv,he⟩ := tight_nonhub_coordinates hn h
  let x : Slot n → ℝ := coordinate f
  let a : ℝ := x (.inl ())-t*coefficient n (.inl ())
  have hx : x=t • coefficient n+Pi.single (.inl ()) a := by
    funext s
    rcases s with u | ⟨r,i⟩ | ⟨r,j⟩
    · cases u
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Pi.single_eq_same]
      dsimp [a]
      ring
    · fin_cases r
      · change aCoeff f i=_
        rw [(hv i).1]
        simp [coefficient]
      · change bCoeff f i=_
        rw [(hv i).2.1]
        by_cases hi : i=0 <;> simp [coefficient,hi]
      · change eCoeff f i=_
        rw [(hv i).2.2]
        by_cases hi : i=0 <;> simp [coefficient,hi]
    · fin_cases r
      · change dCoeff f j=_
        rw [(he j).1]
        simp [coefficient]
      · change taCoeff f j=_
        rw [(he j).2.1]
        by_cases hj : j.val%2=0 <;> simp [coefficient,hj]
      · change tbCoeff f j=_
        rw [(he j).2.2.1]
        by_cases hj : j.val%2=0 <;> simp [coefficient,hj]
      · change hCoeff f j=_
        rw [(he j).2.2.2]
        simp [coefficient]
  have hf : f=FiniteMonomial.polynomial clique x := graphical_coordinates hn (tight_graphical h)
  have hsplit : f=t • setFunction n+a • setMonomial (clique (.inl () : Slot n)) := by
    rw [hf,hx,polynomial_add,FiniteMonomial.polynomial_smul,polynomial_single]
    rfl
  have hzero := h (hubA n) (hubB n) (hubA_ne_hubB n) (alternatingSet n)
    (hubA_notMem_alternatingSet n) (hubB_notMem_alternatingSet n) (delta_hub_alternating n)
  rw [hsplit,delta_add,delta_smul,delta_smul,delta_hub_alternating,
    delta_clique_hub _ _ (hubA_notMem_alternatingSet n) (hubB_notMem_alternatingSet n)] at hzero
  have ha : a=0 := by simpa using hzero
  refine ⟨t,?_⟩
  simpa only [ha,zero_smul,add_zero] using hsplit

theorem extreme (n : ℕ) : ExtremeSupermodular (setFunction n) :=
  extremeSupermodular_of_tightEquations (normalized n) (supermodular n) (function_ne_zero n)
    (fun f hn h => complete_tight_kernel f hn h)

end GraphicalZonotopes.PathJoin
