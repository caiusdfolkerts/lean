module

public import Papers.GraphicalZonotopes.PathJoinTightKernel
public import Papers.GraphicalZonotopes.ConnectedDimension
public import Papers.GraphicalZonotopes.SummandEdges
public import Papers.GraphicalZonotopes.GraphDefinitions

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.PathJoin
open Finset
open scoped BigOperators Pointwise

def polytope (n : ℕ) : Set (Vertex n → ℝ) := basePolytope (setFunction n)
def complement (n : ℕ) : Set (Vertex n → ℝ) :=
  basePolytope ((((n+2)/2 : ℕ) : ℝ) • graphFunction (graph n)-setFunction n)

theorem graph_connected (n : ℕ) : (graph n).Connected := by
  apply (graph n).connected_iff_exists_forall_reachable.mpr
  refine ⟨hubA n,fun v => ?_⟩
  by_cases hv : v=hubA n
  · subst v; exact SimpleGraph.Reachable.refl _
  · exact ((graph_hubA).mpr (Ne.symm hv)).reachable

theorem neighborBit_first {n : ℕ} (j : Fin (n+1)) (S : Finset (Vertex n)) :
    neighborBit (0 : Fin (n+2)) j S =
      if j=0 then bit (vertex (0 : Fin (n+1)).succ) S else 0 := by
  by_cases hj : j=0
  · subst j
    simp [neighborBit]
  · have hl : (0 : Fin (n+2))≠j.castSucc := by
      intro h
      apply hj
      apply Fin.ext
      have he := congrArg Fin.val h
      simpa only [Fin.val_castSucc,Fin.val_zero] using he.symm
    have hr : (0 : Fin (n+2))≠j.succ := Ne.symm (Fin.succ_ne_zero _)
    simp [neighborBit,hj,hl,hr]

theorem delta_b_first_positive (n : ℕ) :
    delta (setFunction n) (hubB n) (vertex (0 : Fin (n+2)))
      {hubA n,vertex (0 : Fin (n+1)).succ}=1 := by
  rw [setFunction,delta_polynomial_b _ _ _ (by simp) (by simp)]
  simp [coefficient,neighborBit_first,bit]

theorem positive_slack {n : ℕ} (u v : Vertex n) (huv : (graph n).Adj u v) :
    ∃ S : Finset (Vertex n),u∉S ∧ v∉S ∧ 0<delta (setFunction n) u v S := by
  have hab : 0<delta (setFunction n) (hubA n) (hubB n) ∅ := by
    rw [delta_hub _ (by simp) (by simp)]
    simp only [bit,notMem_empty,ite_false,sub_zero,mul_zero,sum_const_zero]
    exact lt_of_lt_of_le zero_lt_one (dilation_ge_one n)
  have ha (i : Fin (n+2)) : 0<delta (setFunction n) (hubA n) (vertex i) ∅ := by
    rw [delta_a_empty]; norm_num
  have hb (i : Fin (n+2)) : ∃ S : Finset (Vertex n),hubB n∉S ∧ vertex i∉S ∧
      0<delta (setFunction n) (hubB n) (vertex i) S := by
    by_cases hi : i=0
    · subst i
      exact ⟨{hubA n,vertex (0 : Fin (n+1)).succ},by simp,by simp,
        by rw [delta_b_first_positive]; norm_num⟩
    · refine ⟨∅,by simp,by simp,?_⟩
      rw [delta_b_colored _ _ (by simp) (by simp)]
      simp [bit,hi]
  have hpath (i j : Fin (n+2)) (hij : (graph n).Adj (vertex i) (vertex j)) :
      0<delta (setFunction n) (vertex i) (vertex j) ∅ := by
    rcases (graph_vertices i j).mp hij with h | h
    · let k : Fin (n+1) := ⟨i.val,by omega⟩
      have hk0 : k.castSucc=i := Fin.ext rfl
      have hk1 : k.succ=j := Fin.ext h
      rw [←hk0,←hk1,delta_path _ _ (by simp) (by simp)]
      simp [bit]
    · let k : Fin (n+1) := ⟨j.val,by omega⟩
      have hk0 : k.castSucc=j := Fin.ext rfl
      have hk1 : k.succ=i := Fin.ext h
      rw [delta_swap,←hk0,←hk1,delta_path _ _ (by simp) (by simp)]
      simp [bit]
  rcases vertex_cases u with rfl | rfl | ⟨i,rfl⟩
  · rcases vertex_cases v with rfl | rfl | ⟨j,rfl⟩
    · exact ((graph n).irrefl huv).elim
    · exact ⟨∅,by simp,by simp,hab⟩
    · exact ⟨∅,by simp,by simp,ha j⟩
  · rcases vertex_cases v with rfl | rfl | ⟨j,rfl⟩
    · exact ⟨∅,by simp,by simp,by rw [delta_swap]; exact hab⟩
    · exact ((graph n).irrefl huv).elim
    · exact hb j
  · rcases vertex_cases v with rfl | rfl | ⟨j,rfl⟩
    · exact ⟨∅,by simp,by simp,by rw [delta_swap]; exact ha i⟩
    · obtain ⟨S,hs,hi,hd⟩ := hb i
      exact ⟨S,hi,hs,by rw [delta_swap]; exact hd⟩
    · exact ⟨∅,by simp,by simp,hpath i j huv⟩

theorem full_dimension (n : ℕ) : FullDimension (polytope n) :=
  finrank_vectorSpan_eq_of_connected_slacks (normalized n).1 (supermodular n)
    (graph_connected n) (fun u v huv => by
      obtain ⟨S,hu,hv,hd⟩ := positive_slack u v huv
      exact ⟨S,hu,hv,ne_of_gt hd⟩)

theorem indecomposable (n : ℕ) : MinkowskiIndecomposable (polytope n) :=
  (extreme n).minkowskiIndecomposable

def integerCoefficient (n : ℕ) : Slot n → ℤ
  | .inl _ => (((n+2)/2 : ℕ) : ℤ)
  | .inr (.inl (r,i)) =>
    if r=0 then 1 else if r=1 then (if i=0 then 0 else 1) else if i=0 then 0 else -1
  | .inr (.inr (r,i)) =>
    if r=0 then 1 else if r=1 then (if i.val%2=0 then -1 else 0)
    else if r=2 then (if i.val%2=0 then 0 else -1) else 1

theorem coefficient_integral (n : ℕ) (s : Slot n) : ∃ a : ℤ,coefficient n s=(a : ℝ) := by
  refine ⟨integerCoefficient n s,?_⟩
  rcases s with u | ⟨r,i⟩ | ⟨r,j⟩
  · change (((n+2)/2 : ℕ) : ℝ)=((((n+2)/2 : ℕ) : ℤ) : ℝ)
    rw [Int.cast_natCast]
  · dsimp only [coefficient,integerCoefficient]
    split_ifs <;> norm_num
  · dsimp only [coefficient,integerCoefficient]
    split_ifs <;> norm_num

theorem integerValued (n : ℕ) : IntegerValued (setFunction n) := by
  unfold setFunction FiniteMonomial.polynomial
  apply IntegerValued.finset_sum
  intro s hs
  obtain ⟨a,ha⟩ := coefficient_integral n s
  rw [ha]
  exact (setMonomial_integerValued (clique s)).int_smul a

theorem lattice (n : ℕ) : LatticePolytope (polytope n) :=
  (integerValued n).basePolytope (normalized n).1 (supermodular n)

theorem complement_normalized (n : ℕ) :
    Normalized ((((n+2)/2 : ℕ) : ℝ) • graphFunction (graph n)-setFunction n) := by
  change _*graphFunction (graph n) ∅-setFunction n ∅=0
  rw [graphFunction_normalized,(normalized n).1]
  ring

theorem complement_supermodular (n : ℕ) :
    Supermodular ((((n+2)/2 : ℕ) : ℝ) • graphFunction (graph n)-setFunction n) :=
  graphical_complement_supermodular (graphical n) (Nat.cast_nonneg _)
    (fun u v huv hadj S hu hv => (slack_bounds u v huv S hu hv).2)

theorem complement_lattice (n : ℕ) : LatticePolytope (complement n) := by
  have hz := (graphFunction_integerValued (graph n)).int_smul (((n+2)/2 : ℕ) : ℤ)
  have hi : IntegerValued ((((n+2)/2 : ℕ) : ℝ) • graphFunction (graph n)-setFunction n) := by
    simpa only [Int.cast_natCast] using hz.sub (integerValued n)
  exact hi.basePolytope (complement_normalized n) (complement_supermodular n)

theorem add_complement (n : ℕ) :
    polytope n+complement n=(((n+2)/2 : ℕ) : ℝ) • graphicalZonotope (graph n) :=
  basePolytope_add_graphical_complement (normalized n).1 (supermodular n) (graphical n)
    (Nat.cast_nonneg _) (fun u v huv hadj S hu hv => (slack_bounds u v huv S hu hv).2)

theorem actual_direction_graph (n : ℕ) : actualDirectionGraph (polytope n)=graph n := by
  ext u v
  constructor
  · exact basePolytope_summand_actualRootEdge (normalized n).1 (supermodular n)
      (graph n) (Nat.cast_nonneg _) (complement n) (add_complement n)
  · intro huv
    obtain ⟨S,hu,hv,hd⟩ := positive_slack u v huv
    exact exposedSegment_of_positive_delta (normalized n).1 (supermodular n)
      ((graph n).ne_of_adj huv) hu hv hd

/-- The actual full-dimensional lattice summand and actual lattice
complement asserted in Appendix B, for every path length at least two.
-/
theorem appendix_B_one (n : ℕ) :
    LatticePolytope (polytope n) ∧ MinkowskiIndecomposable (polytope n) ∧
      FullDimension (polytope n) ∧ LatticePolytope (complement n) ∧
      polytope n+complement n=(((n+2)/2 : ℕ) : ℝ) • graphicalZonotope (graph n) ∧
      actualDirectionGraph (polytope n)=graph n :=
  ⟨lattice n,indecomposable n,full_dimension n,complement_lattice n,add_complement n,
    actual_direction_graph n⟩

end GraphicalZonotopes.PathJoin
