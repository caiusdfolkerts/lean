module

public import PaperVerification.ToricRationalFeasibility
public import PaperVerification.ToricStatements
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
# Integral homogeneous relations from rational convex geometry

An integral point of the real convex hull of finitely many integral
points admits an integer homogeneous relation with those points and a
strictly positive total degree. This is derived from rational feasibility
and explicit denominator clearing. It applies on all faces, including
zero-dimensional hulls.
-/

noncomputable section

namespace PaperVerification.ToricRationalGeometry

open PaperVerification.ToricGeometry
open scoped BigOperators Classical

theorem rational_weights_of_real_weights {κ : Type*} [Fintype κ] {n : ℕ}
    (v : κ → Fin n → ℚ) (m : Fin n → ℚ)
    (w : κ → ℝ) (hw0 : ∀ i,0≤w i) (hw1 : ∑ i,w i=1)
    (hwm : ∀ j,∑ i,w i*(v i j : ℝ)=(m j : ℝ)) :
    ∃ q : κ → ℚ,(∀ i,0≤q i) ∧ ∑ i,q i=1 ∧ ∀ j,∑ i,q i*v i j=m j := by
  let I := κ ⊕ ((Unit ⊕ Fin n) × Bool)
  let A : I → κ → ℚ := fun row i => match row with
    | Sum.inl j => if i=j then 1 else 0
    | Sum.inr (Sum.inl _,false) => 1
    | Sum.inr (Sum.inl _,true) => -1
    | Sum.inr (Sum.inr j,false) => v i j
    | Sum.inr (Sum.inr j,true) => -v i j
  let b : I → ℚ := fun row => match row with
    | Sum.inl _ => 0
    | Sum.inr (Sum.inl _,false) => -1
    | Sum.inr (Sum.inl _,true) => 1
    | Sum.inr (Sum.inr j,false) => -m j
    | Sum.inr (Sum.inr j,true) => m j
  have hfeasible : ∃ x : κ → ℝ,∀ row,0≤(b row : ℝ)+∑ i,(A row i : ℝ)*x i := by
    refine ⟨w,?_⟩
    intro row
    rcases row with i|⟨tag,sign⟩
    · simpa [A,b,apply_ite,ite_mul] using hw0 i
    · rcases tag with u|j <;> cases sign
      · simp [A,b,hw1]
      · simp [A,b,hw1,Finset.sum_neg_distrib]
      · simp [A,b,mul_comm,hwm j]
      · simp [A,b,mul_comm,hwm j,Finset.sum_neg_distrib]
  obtain ⟨q,hq⟩ := rational_matrix_feasible_of_real_feasible A b hfeasible
  refine ⟨q,?_,?_,?_⟩
  · intro i
    simpa [A,b] using hq (Sum.inl i)
  · have hlo := hq (Sum.inr (Sum.inl (),false))
    have hup := hq (Sum.inr (Sum.inl (),true))
    simp only [A,b,one_mul,neg_one_mul,Finset.sum_neg_distrib] at hlo hup
    linarith
  · intro j
    have hlo := hq (Sum.inr (Sum.inr j,false))
    have hup := hq (Sum.inr (Sum.inr j,true))
    simp only [A,b,neg_mul,Finset.sum_neg_distrib] at hlo hup
    simpa [mul_comm] using le_antisymm (by linarith : ∑ i,v i j*q i≤m j)
      (by linarith : m j≤∑ i,v i j*q i)

/-- A common positive denominator gives nonnegative integer weights. -/
theorem clear_nonnegative_rational_denominators {κ : Type*} [Fintype κ]
    (q : κ → ℚ) (hq : ∀ i,0≤q i) :
    ∃ N : ℕ,0<N ∧ ∃ c : κ → ℕ,∀ i,(c i : ℚ)=(N : ℚ)*q i := by
  let N : ℕ := ∏ i,(q i).den
  have hN : 0<N := Finset.prod_pos (fun i hi => (q i).den_pos)
  let c : κ → ℕ := fun i => (q i).num.toNat*(N/(q i).den)
  refine ⟨N,hN,c,?_⟩
  intro i
  have hdiv : (q i).den∣N := Finset.dvd_prod_of_mem (fun i=>(q i).den)
    (Finset.mem_univ i)
  have hmul : (q i).den*(N/(q i).den)=N := Nat.mul_div_cancel' hdiv
  have hnum : 0≤(q i).num := Rat.num_nonneg.mpr (hq i)
  have hnumcast : ((q i).num.toNat : ℚ)=((q i).num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg hnum
  have hNcast : (N : ℚ)=((q i).den : ℚ)*((N/(q i).den : ℕ) : ℚ) := by
    exact_mod_cast hmul.symm
  change (((q i).num.toNat*(N/(q i).den) : ℕ) : ℚ)=(N : ℚ)*q i
  rw [Nat.cast_mul,hnumcast]
  have hd : ((q i).den : ℚ)≠0 := by exact_mod_cast (q i).den_ne_zero
  calc
    ((q i).num : ℚ) * ((N/(q i).den : ℕ) : ℚ) =
        (N : ℚ) * (((q i).num : ℚ) / ((q i).den : ℚ)) := by
      rw [hNcast]
      field_simp
    _ = (N : ℚ) * q i := congrArg ((N : ℚ) * ·) (q i).num_div_den

theorem integral_relation_of_real_weights {κ : Type*} [Fintype κ] {n : ℕ}
    (v : κ → Lattice n) (m : Lattice n)
    (w : κ → ℝ) (hw0 : ∀ i,0≤w i) (hw1 : ∑ i,w i=1)
    (hwm : ∑ i,w i • embed n (v i)=embed n m) :
    ∃ N : ℕ,0<N ∧ ∃ c : κ → ℕ,(∑ i,c i=N) ∧ ∑ i,c i • v i=N • m := by
  let vQ : κ → Fin n → ℚ := fun i j=>(v i j : ℚ)
  let mQ : Fin n → ℚ := fun j=>(m j : ℚ)
  have hcoord (j : Fin n) : ∑ i,w i*(vQ i j : ℝ)=(mQ j : ℝ) := by
    have := congrFun hwm j
    simpa [vQ,mQ,embed,Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using this
  obtain ⟨q,hq0,hq1,hqm⟩ := rational_weights_of_real_weights vQ mQ w hw0 hw1 hcoord
  obtain ⟨N,hN,c,hc⟩ := clear_nonnegative_rational_denominators q hq0
  refine ⟨N,hN,c,?_,?_⟩
  · have hsum : (∑ i,(c i : ℚ))=(N : ℚ) := by
      simp only [hc,← Finset.mul_sum,hq1,mul_one]
    exact_mod_cast hsum
  · ext j
    have hsum : ∑ i,(c i : ℚ)*(v i j : ℚ)=(N : ℚ)*(m j : ℚ) := by
      simp only [hc,mul_assoc,← Finset.mul_sum]
      exact congrArg ((N : ℚ)*·) (hqm j)
    simpa [Finset.sum_apply,Pi.smul_apply,nsmul_eq_mul] using
      (show ∑ i,(c i : ℤ)*v i j=(N : ℤ)*m j by exact_mod_cast hsum)

theorem integral_relation_of_mem_convexHull {n : ℕ} (V : Finset (Lattice n))
    (m : Lattice n) (hm : embed n m∈convexHull ℝ (embed n '' (V : Set (Lattice n)))) :
    ∃ N : ℕ,0<N ∧ ∃ c : V → ℕ,(∑ i,c i=N) ∧ ∑ i,c i • i.val=N • m := by
  have hm' : embed n m∈convexHull ℝ (V.image (embed n) : Set (Ambient n)) := by
    simpa using hm
  obtain ⟨w,hw0,hw1,hwm⟩ := Finset.mem_convexHull'.mp hm'
  have hsum : ∑ i : V,w (embed n i.val)=1 := by
    calc
      ∑ i : V,w (embed n i.val)=∑ i∈V,w (embed n i) := by
        simpa only [Finset.univ_eq_attach] using
          Finset.sum_attach V (fun i => w (embed n i))
      _ = 1 := by
        simpa only [Finset.sum_image (fun x hx y hy hxy => embed_injective n hxy)] using hw1
  have hvec : ∑ i : V,w (embed n i.val) • embed n i.val=embed n m := by
    calc
      ∑ i : V,w (embed n i.val) • embed n i.val=
          ∑ i∈V,w (embed n i) • embed n i := by
        simpa only [Finset.univ_eq_attach] using
          Finset.sum_attach V (fun i => w (embed n i) • embed n i)
      _ = embed n m := by
        simpa only [Finset.sum_image (fun x hx y hy hxy => embed_injective n hxy)] using hwm
  exact integral_relation_of_real_weights (fun i : V=>i.val) m
    (fun i=>w (embed n i.val))
    (fun i=>hw0 _ (Finset.mem_image.mpr ⟨i.val,i.property,rfl⟩)) hsum hvec

theorem integral_relation_of_mem_convexHull_range {κ : Type*} [Fintype κ]
    {n : ℕ} (v : κ → Lattice n) (m : Lattice n)
    (hm : embed n m∈convexHull ℝ (Set.range (fun i=>embed n (v i)))) :
    ∃ N : ℕ,0<N ∧ ∃ c : κ → ℕ,(∑ i,c i=N) ∧ ∑ i,c i • v i=N • m := by
  rw [convexHull_range_eq_exists_affineCombination] at hm
  obtain ⟨s,w,hw0,hw1,hwm⟩ := hm
  let w' : κ → ℝ := fun i=>if i∈s then w i else 0
  have hw'0 (i : κ) : 0≤w' i := by
    by_cases hi : i∈s
    · simpa [w',hi] using hw0 i hi
    · simp [w',hi]
  have hw'1 : ∑ i,w' i=1 := by simpa [w'] using hw1
  have hvec : ∑ i,w' i • embed n (v i)=embed n m := by
    rw [Finset.affineCombination_eq_linear_combination s _ _ hw1] at hwm
    simpa [w',ite_smul] using hwm
  exact integral_relation_of_real_weights v m w' hw'0 hw'1 hvec

end PaperVerification.ToricRationalGeometry

#print axioms PaperVerification.ToricRationalGeometry.integral_relation_of_mem_convexHull
