module

public import Papers.GraphicalZonotopes.BooleanResponseQuotient
public import Papers.GraphicalZonotopes.ConnectedDimension
public import Papers.GraphicalZonotopes.SummandEdges
public import Papers.GraphicalZonotopes.GraphDefinitions

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators Pointwise
variable {H J : Type*} [Fintype H] [DecidableEq H] [Fintype J] [DecidableEq J]

/-- An essential Boolean variable is witnessed by an actual cover with
increment one. For a monotone zero-one function this is ordinary dependence
on that variable. -/
def Essential (F : SetFunction H) (a : H) : Prop :=
  ∃ X : Finset H,a∉X ∧ F (insert a X)-F X=1

def essentialSpokeGraph (F : J → SetFunction H) : SimpleGraph (H⊕J) where
  Adj
    | Sum.inl a,Sum.inr j => Essential (F j) a
    | Sum.inr j,Sum.inl a => Essential (F j) a
    | _,_ => False
  symm := ⟨by intro a b; cases a <;> cases b <;> exact id⟩
  loopless := ⟨by intro a; cases a <;> exact not_false⟩

theorem essentialSpokeGraph_connected [Nonempty H] [Nonempty J]
    (F : J → SetFunction H) (hF : ∀ j a,Essential (F j) a) :
    (essentialSpokeGraph F).Connected := by
  obtain ⟨a₀⟩:=‹Nonempty H›
  obtain ⟨j₀⟩:=‹Nonempty J›
  have hcross : ∀ a j,(essentialSpokeGraph F).Adj (Sum.inl a) (Sum.inr j):=
    fun a j => hF j a
  refine ⟨?_⟩
  intro x y
  cases x with
  | inl a =>
    cases y with
    | inl b =>
      exact (hcross a j₀).reachable.trans (hcross b j₀).reachable.symm
    | inr j => exact (hcross a j).reachable
  | inr i =>
    cases y with
    | inl a => exact (hcross a i).reachable.symm
    | inr j =>
      exact (hcross a₀ i).reachable.symm.trans (hcross a₀ j).reachable

theorem essential_spoke_slack {z : SetFunction H} {F : J → SetFunction H}
    {w : J → ℝ} (hw : ∀ j,0<w j) {a b : H⊕J}
    (hab : (essentialSpokeGraph F).Adj a b) :
    ∃ A : Finset (H⊕J),a∉A ∧ b∉A ∧ delta (assembled z F w) a b A≠0 := by
  cases a with
  | inl u =>
    cases b with
    | inl v => exact False.elim hab
    | inr j =>
      obtain ⟨X,hu,hX⟩:=hab
      refine ⟨hubSet X,by simpa using hu,by simp,?_⟩
      rw [delta_assembled_spoke _ _ _ _ _ _ (by simp),hubs_hubSet,hX,mul_one]
      exact ne_of_gt (hw j)
  | inr i =>
    cases b with
    | inl v =>
      obtain ⟨X,hv,hX⟩:=hab
      refine ⟨hubSet X,by simp,by simpa using hv,?_⟩
      rw [delta_swap,delta_assembled_spoke _ _ _ _ _ _ (by simp),hubs_hubSet,hX,mul_one]
      exact ne_of_gt (hw i)
    | inr j => exact False.elim hab

/-- The dimension clause of Lemma7.3 uses the genuine connected spanning
essential-spoke graph, so ignored variables remain present in the ambient
coordinate space and cannot disappear silently. -/
theorem assembled_fullDimension {z : SetFunction H} (hz : TranslationNormalized z)
    {F : J → SetFunction H} (hF : ∀ j,IsMonotoneBoolean (F j))
    {w : J → ℝ} (hw : ∀ j,0<w j) (hc : Compatible z F w)
    (hconn : (essentialSpokeGraph F).Connected) :
    FullDimension (basePolytope (assembled z F w)) := by
  apply finrank_vectorSpan_eq_of_connected_slacks (assembled_normalized hz F hF w).1
    (assembled_supermodular z F hF w (fun j => (hw j).le) hc) hconn
  intro a b hab
  exact essential_spoke_slack hw hab

theorem assembled_delta_le_weight_sum {z : SetFunction H}
    {F : J → SetFunction H} (hF : ∀ j,IsMonotoneBoolean (F j))
    {w : J → ℝ} (hw : ∀ j,0≤w j) (hc : Compatible z F w)
    (a b : H⊕J) (hab : a≠b) (A : Finset (H⊕J)) (ha : a∉A) (hb : b∉A) :
    delta (assembled z F w) a b A≤∑ j : J,w j := by
  have hsum : 0≤∑ j : J,w j:=sum_nonneg (fun j _ => hw j)
  have hspoke : ∀ u j,Sum.inr j∉A →
      delta (assembled z F w) (Sum.inl u) (Sum.inr j) A≤∑ i : J,w i := by
    intro u j hj
    rw [delta_assembled_spoke _ _ _ _ _ _ hj]
    have hcover : F j (insert u (hubs A))-F j (hubs A)≤1 := by
      rcases cover_values (hF j) u (hubs A) with h | h <;> simp [h]
    exact (mul_le_mul_of_nonneg_left hcover (hw j)).trans
      (by simpa using single_le_sum (fun i _ => hw i) (mem_univ j))
  cases a with
  | inl u =>
    cases b with
    | inl v =>
      rw [assembled_factorization z F w hc u v (fun he => hab (congrArg Sum.inl he)) A ha hb]
      apply sum_le_sum
      intro j hj
      have hx : (if Sum.inr j∈A then (1 : ℝ) else 0)=0 ∨
          (if Sum.inr j∈A then (1 : ℝ) else 0)=1 := by split_ifs <;> simp
      have hle : negativeResponse (F j) u v (hubs A)+
          (if Sum.inr j∈A then 1 else 0)*delta (F j) u v (hubs A)≤1 := by
        rcases response_factor_values (hF j) u v (hubs A) _ hx with h | h <;> rw [h] <;> norm_num
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hle (hw j)
    | inr j => exact hspoke u j hb
  | inr i =>
    cases b with
    | inl v => rw [delta_swap]; exact hspoke v i ha
    | inr j =>
      rw [delta_assembled_outer _ _ _ _ _ (fun he => hab (congrArg Sum.inr he)) _ ha hb]
      exact hsum

theorem IsMonotoneBoolean.integerValued {F : SetFunction H} (hF : IsMonotoneBoolean F) :
    IntegerValued F := by
  intro X
  rcases hF.values X with h | h
  · exact ⟨0,by simpa using h⟩
  · exact ⟨1,by simpa using h⟩

theorem boundaryLift_integerValued {z : SetFunction H} (hz : IntegerValued z) :
    IntegerValued (boundaryLift (J:=J) z) := fun A => hz (hubs A)

theorem branchLift_integerValued (j : J) {F : SetFunction H} (hF : IntegerValued F) :
    IntegerValued (branchLift j F) := by
  intro A
  by_cases hj : Sum.inr j∈A
  · simpa only [branchLift,if_pos hj] using hF (hubs A)
  · exact ⟨0,by simp only [branchLift,if_neg hj,Int.cast_zero]⟩

theorem assembled_integerValued {z : SetFunction H} (hz : IntegerValued z)
    (F : J → SetFunction H) (hF : ∀ j,IsMonotoneBoolean (F j)) (w : J → ℤ) :
    IntegerValued (assembled z F (fun j => (w j : ℝ))) := by
  apply (boundaryLift_integerValued hz).add
  exact IntegerValued.finset_sum univ _ (fun j _ =>
    (branchLift_integerValued j (hF j).integerValued).int_smul (w j))

/-- The exact slack bound gives an actual Minkowski complement in the sum of
the branch weights times the graphical zonotope. -/
theorem assembled_actual_summand {s k : ℕ} {z : SetFunction (Fin s)}
    (hz : TranslationNormalized z) {F : Fin k → SetFunction (Fin s)}
    (hF : ∀ j,IsMonotoneBoolean (F j)) {w : Fin k → ℝ}
    (hw : ∀ j,0≤w j) (hc : Compatible z F w) :
    IsMinkowskiSummand (basePolytope (assembled z F w))
      ((∑ j : Fin k,w j) • graphicalZonotope (cliqueBook s k)) := by
  apply (isMinkowskiSummand_graphical_iff (assembled_normalized hz F hF w).1
    (assembled_supermodular z F hF w hw hc) (sum_nonneg (fun j _ => hw j))).mpr
  refine ⟨assembled_graphical z F w,?_⟩
  intro a b hab hedge A ha hb
  exact assembled_delta_le_weight_sum hF hw hc a b hab A ha hb

theorem assembled_lattice_complement {s k : ℕ} {z : SetFunction (Fin s)}
    (hz : TranslationNormalized z) (hzi : IntegerValued z)
    {F : Fin k → SetFunction (Fin s)} (hF : ∀ j,IsMonotoneBoolean (F j))
    (w : Fin k → ℤ) (hw : ∀ j,0≤w j)
    (hc : Compatible z F (fun j => (w j : ℝ))) :
    LatticePolytope (basePolytope (assembled z F (fun j => (w j : ℝ)))) ∧
    ∃ R : Set ((Fin s⊕Fin k) → ℝ),LatticePolytope R ∧ R.Nonempty ∧
      basePolytope (assembled z F (fun j => (w j : ℝ)))+R=
        ((∑ j : Fin k,(w j : ℝ)) • graphicalZonotope (cliqueBook s k)) := by
  let f:=assembled z F (fun j => (w j : ℝ))
  let a : ℝ:=∑ j : Fin k,(w j : ℝ)
  have hw' : ∀ j,0≤(w j : ℝ):=fun j => by exact_mod_cast hw j
  have hn:=assembled_normalized hz F hF (fun j => (w j : ℝ))
  have hs:=assembled_supermodular z F hF (fun j => (w j : ℝ)) hw' hc
  have hi:=assembled_integerValued hzi F hF w
  have hG:=assembled_graphical z F (fun j => (w j : ℝ))
  have ha : 0≤a:=sum_nonneg (fun j _ => hw' j)
  have hbound : ∀ u v,u≠v → (cliqueBook s k).Adj u v → ∀ A,u∉A → v∉A →
      delta f u v A≤a := by
    intro u v huv hedge A hu hv
    exact assembled_delta_le_weight_sum hF hw' hc u v huv A hu hv
  let g : SetFunction (Fin s⊕Fin k):=a • graphFunction (cliqueBook s k)-f
  have hgn : Normalized g := by
    change a*graphFunction (cliqueBook s k) ∅-f ∅=0
    have hf0 : f ∅=0 := hn.1
    rw [graphFunction_normalized,hf0,mul_zero,sub_self]
  have hgs : Supermodular g:=graphical_complement_supermodular hG ha hbound
  have hgi : IntegerValued g := by
    have hg0:=(graphFunction_integerValued (cliqueBook s k)).int_smul (∑ j : Fin k,w j)
    have he : ((∑ j : Fin k,w j : ℤ) : ℝ)=a := by simp only [Int.cast_sum,a]
    rw [he] at hg0
    exact hg0.sub hi
  exact ⟨hi.basePolytope hn.1 hs,basePolytope g,hgi.basePolytope hgn hgs,
    basePolytope_nonempty hgn hgs,basePolytope_add_graphical_complement hn.1 hs hG ha hbound⟩

end BooleanModule
end GraphicalZonotopes
