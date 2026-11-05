module
public import consolidated.actual_rigid_seeds

set_option Elab.async false

section BundlePart0
/- Source: Papers/SmallOrderRigidity.lean -/



@[expose] public section
noncomputable section
namespace Papers.PolytopeFourRegularTail
open Set Finset Papers.Polytopes
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical BigOperators
variable {n : ℕ}

theorem actual_cut_count_symmetry (P : ConvexPolytope n) (A B : Finset (E n))
    (hA : A⊆P.vertices) (hB : B⊆P.vertices) :
    (∑x∈A,(B.filter (GeneralVertexStep P x)).card)=
      ∑y∈B,(A.filter (GeneralVertexStep P y)).card := by
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro x hx
  have he : GeneralVertexStep P x y ↔ GeneralVertexStep P y x :=
    ⟨actualStep_symm (hA hx),actualStep_symm (hB hy)⟩
  simp only [he]

theorem actual_degree_lt_card (P : ConvexPolytope n) (T : Finset (E n))
    {x : E n} (hx : x∈T) : (T.filter (GeneralVertexStep P x)).card<T.card := by
  have hsub : T.filter (GeneralVertexStep P x)⊆T.erase x := by
    intro y hy
    obtain ⟨hyT,hxy⟩ := Finset.mem_filter.mp hy
    exact Finset.mem_erase.mpr ⟨hxy.2.1.symm,hyT⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hx] at hc
  have hp := Finset.card_pos.mpr ⟨x,hx⟩
  omega

/-- The full minimum-degree rigidity bound, with no restriction on ambient
or intrinsic dimension: at most `2k-1` vertices of minimum degree `k`. -/
theorem rigid_of_min_degree_small_order
    (P : ConvexPolytope n) (T : Finset (E n)) (hTV : T⊆P.vertices)
    (k : ℕ) (hmin : ∀x∈T,k≤(T.filter (GeneralVertexStep P x)).card)
    (hcard : T.card≤2*k-1) : RigidInTail P T T := by
  by_cases hne : T.Nonempty
  · obtain ⟨x,hx⟩ := hne
    have hm := hmin x hx
    have hlt := actual_degree_lt_card P T hx
    have hk : 2≤k := by omega
    obtain ⟨y,hy⟩ := Finset.card_pos.mp (by omega :
      0<(T.filter (GeneralVertexStep P x)).card)
    obtain ⟨hyT,hxy⟩ := Finset.mem_filter.mp hy
    have hpair := rigid_pair hx hyT hxy
    have hpairT : ({x,y}:Finset (E n))⊆T := by
      intro z hz
      simp only [Finset.mem_insert,Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    have hpairC : ({x,y}:Finset (E n)).card=2 := by simp [hxy.2.1]
    obtain ⟨A,hA⟩ := exists_largest_rigid P T
    have hAc : 2≤A.card := by simpa only [hpairC] using hA.largest _ hpairT hpair
    by_cases hAT : A=T
    · exact hAT ▸ hA.rigid
    have hnot : ¬T⊆A := fun h => hAT (Finset.Subset.antisymm hA.subset h)
    obtain ⟨b,hbT,hbA⟩ := Finset.not_subset.mp hnot
    let B := T\A
    have hbB : b∈B := Finset.mem_sdiff.mpr ⟨hbT,hbA⟩
    have hBT : B⊆T := Finset.sdiff_subset
    have hres := hA.residual_min_degree hTV (k-1) (by
      have he : k-1+1=k := Nat.sub_add_cancel (by omega)
      simpa only [he] using hmin)
    have hmB := hres b hbB
    change k-1≤(B.filter (GeneralVertexStep P b)).card at hmB
    have hltB := actual_degree_lt_card P B hbB
    have hBc : k≤B.card := by omega
    have hcards : B.card+A.card=T.card := Finset.card_sdiff_add_card_eq_card hA.subset
    have hAk : A.card≤k := by omega
    have point (a : E n) (ha : a∈A) :
        k≤(A.card-1)+(B.filter (GeneralVertexStep P a)).card := by
      have hsmall := actual_degree_lt_card P A ha
      have hlarge := hmin a (hA.subset ha)
      have hsub : A.filter (GeneralVertexStep P a)⊆T.filter (GeneralVertexStep P a) :=
        Finset.filter_subset_filter _ hA.subset
      have hfilter : B.filter (GeneralVertexStep P a)=
          T.filter (GeneralVertexStep P a)\A.filter (GeneralVertexStep P a) := by
        ext z
        simp only [B,Finset.mem_filter,Finset.mem_sdiff]
        tauto
      have hc := Finset.card_sdiff_add_card_eq_card hsub
      rw [←hfilter] at hc
      omega
    have hsum := Finset.sum_le_sum (s:=A) (fun a ha=>point a ha)
    simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul] at hsum
    have hcut : (∑a∈A,(B.filter (GeneralVertexStep P a)).card)≤B.card := by
      rw [actual_cut_count_symmetry P A B (hA.subset.trans hTV) (hBT.trans hTV)]
      calc
        _≤∑b∈B,(1:ℕ) := Finset.sum_le_sum (by
          intro b hb
          obtain ⟨hbT,hbA⟩ := Finset.mem_sdiff.mp hb
          exact hA.outside_degree_le_one hTV hbT hbA)
        _=B.card := by simp
    have ha1 : A.card-1+1=A.card := Nat.sub_add_cancel (by omega)
    have ha2 : A.card-2+2=A.card := Nat.sub_add_cancel hAc
    have hka : k-A.card+A.card=k := Nat.sub_add_cancel hAk
    have hnonneg : 0≤(A.card-2)*(k-A.card) := Nat.zero_le _
    have hN : T.card+1≤2*k := by omega
    exfalso
    nlinarith
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    exact rigid_empty P ∅

end Papers.PolytopeFourRegularTail

namespace Papers.Polytopes
open Set Papers.PolytopeFourRegularTail
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical
variable {d : ℕ}

theorem homotheticOn_of_vertexSubset_degree
    (P : ConvexPolytope d) (f : E d→E d) (hf : IsParallelMap P f)
    (S : Finset (E d)) (hS : S⊆P.vertices) {k : ℕ}
    (hdegree : ∀x∈S,k≤(S.filter (GeneralVertexStep P x)).card)
    (hcard : S.card≤2*k-1) : HomotheticOn f (S:Set (E d)) :=
  rigid_of_min_degree_small_order P S hS k hdegree hcard f
    (fun x hx y hy hxy=>hf x (hS hx) y (hS hy) hxy)

end Papers.Polytopes

end
end
end BundlePart0

