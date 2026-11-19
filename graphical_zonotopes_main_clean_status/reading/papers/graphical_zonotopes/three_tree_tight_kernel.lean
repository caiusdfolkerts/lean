module

public import Papers.GraphicalZonotopes.ThreeTreeKernelRigidity
public import Papers.GraphicalZonotopes.ThreeTreeConstructionBounds
public import Papers.GraphicalZonotopes.PositiveDecomposition

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace ThreeTreeStates
open Finset
open RootedResponse
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem zeta_pairSupported_delta_unordered (y : SetFunction V)
    (hy : ∀ C, C.card ≠ 2 → y C = 0) {u v : V} (huv : u ≠ v)
    {S : Finset V} (hu : u ∉ S) (hv : v ∉ S) :
    delta (zeta y) u v S = y {u,v} := by
  rw [delta_zeta huv hu hv]
  refine Finset.sum_eq_single (s := (insert u (insert v S)).powerset.filter
    (fun C => u ∈ C ∧ v ∈ C)) (f := y) ({u,v} : Finset V) ?_ ?_
  · intro C hC hne
    apply hy C
    intro hcard
    have hmem := (mem_filter.mp hC).2
    have hsub : ({u,v} : Finset V) ⊆ C :=
      insert_subset hmem.1 (singleton_subset_iff.mpr hmem.2)
    have he : ({u,v} : Finset V) = C := eq_of_subset_of_card_le hsub (by
      simpa [huv] using le_of_eq hcard)
    exact hne he.symm
  · intro hnot
    exact False.elim (hnot (by simp))

theorem pairFactor_has_zero (G : SimpleGraph V) (s : CompatibleRows G)
    (E : Finset V) (hE : E.card=2) (C : IncidentPairClique G E) :
    ∃ x : V → Bool,pairFactor G s E hE C (fun w => realBit (x w))=0 := by
  let p:=complementPair G C.1 E hE C.2
  let a:=(s.clique C.1).row p.first p.second
  let b:=(s.clique C.1).row p.second p.first
  let x : V → Bool:=Function.update (fun _ => a) p.first.1 b
  refine ⟨x,?_⟩
  have hx1 : x p.first.1=b:=by simp [x]
  have hx2 : x p.second.1=a:=Function.update_of_ne p.ne_val.symm _ _
  change ((max (RootedResponse.integerBit a) (RootedResponse.integerBit b) : ℤ) : ℝ)-
    realBit a*realBit (x p.second.1)-realBit b*realBit (x p.first.1)+
    realBit (x p.first.1)*realBit (x p.second.1)=0
  rw [hx1,hx2]
  cases a <;> cases b <;> norm_num [realBit,RootedResponse.integerBit]

theorem edge_has_zero_slack {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {u v : V} (huv : G.Adj u v) :
    ∃ A : Finset V,u∉A ∧ v∉A ∧ delta (setFunction h s) u v A=0 := by
  classical
  by_cases hg : GoodPair G {u,v}
  · obtain ⟨x,hx⟩:=ForestZeros.totalFactor_has_zero (edgeLink G u v)
      (h.edgeLink_acyclic huv) (linkBit G s huv)
    refine ⟨((booleanSupport (fun w => realBit (x w))).erase u).erase v,
      by simp,by simp,?_⟩
    rw [elemental_good_factorization h s huv hg x]
    exact hx
  · obtain ⟨D,hD,hED⟩:=h.clique_extends (C:=({u,v} : Finset V))
      (by simpa only [insert_subset_iff,singleton_subset_iff] using h.edges_supported huv)
      (((mem_edgeFamily G {u,v}).mp ((pair_mem_edgeFamily G huv.ne).mpr huv)).2)
    let C : IncidentPairClique G {u,v}:=⟨⟨D,hD⟩,hED⟩
    have hpos : 0<Fintype.card (IncidentPairClique G {u,v}):=
      Fintype.card_pos_iff.mpr ⟨C⟩
    have hone : Fintype.card (IncidentPairClique G {u,v})=1 := by
      unfold GoodPair at hg
      omega
    have hsub : Subsingleton (IncidentPairClique G {u,v}):=
      Fintype.card_le_one_iff_subsingleton.mp hone.le
    obtain ⟨x,hx⟩:=pairFactor_has_zero G s {u,v} (by simp [huv.ne]) C
    refine ⟨((booleanSupport (fun w => realBit (x w))).erase u).erase v,
      by simp,by simp,?_⟩
    rw [elemental_factorization h s huv x]
    rw [sum_eq_single C]
    · exact hx
    · intro D hD hDC
      exact False.elim (hDC (hsub.elim _ _))
    · intro hn
      exact False.elim (hn (mem_univ C))

theorem cliqueSupported_zero_of_not_clique {G : SimpleGraph V} {y : SetFunction V}
    (hy : CliqueSupported G y) {C : Finset V} (hc : ¬G.IsClique C) : y C=0 := by
  by_contra hn
  exact hc (hy.clique_of_nonzero hn)

/-- After recovering every actual tetrahedron and triangle coefficient,
the full Möbius residual is supported on pairs. No clique or higher-degree
coordinates are omitted from this assertion. -/
theorem residual_pair_supported {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) (hm : 2≤(tetrahedra G).card)
    {f : SetFunction V} (hn : TranslationNormalized f)
    (hf : TightVariation (setFunction h s) f)
    (a : ℝ) (ha : ∀ C∈tetrahedra G,mobius f C=a) :
    ∀ C,C.card≠2 → (mobius f-a • coefficients h s) C=0 := by
  have hy:=tightVariation_cliqueSupported h s hn hf
  have hz:=coefficients_cliqueSupported h s
  have htri:=all_triangle_coefficients_scaled h s hm hn hf a ha
  intro C hc2
  change mobius f C-a*coefficients h s C=0
  by_cases hcl : G.IsClique C
  · have hcard:=h.clique_card_le_four hcl
    have hc : C.card=0 ∨ C.card=1 ∨ C.card=3 ∨ C.card=4 := by omega
    rcases hc with hc | hc | hc | hc
    · have he : C=∅:=card_eq_zero.mp hc
      rw [he,hy.1,hz.1,mul_zero,sub_zero]
    · obtain ⟨v,rfl⟩:=card_eq_one.mp hc
      rw [hy.2.1 v,hz.2.1 v,mul_zero,sub_zero]
    · rw [htri C (mem_triangles.mpr ⟨hc,hcl⟩),sub_self]
    · have hC : C∈tetrahedra G:=mem_filter.mpr ⟨mem_univ _,hc,hcl⟩
      rw [ha C hC,coefficients_tetrahedron h s hC,mul_one,sub_self]
  · rw [cliqueSupported_zero_of_not_clique hy hcl,
      cliqueSupported_zero_of_not_clique hz hcl,mul_zero,sub_zero]

/-- The complete normalized tight kernel for the constructed ray on any
3-tree with at least two tetrahedra. All real set functions are quantified,
and support is deduced from the original nonedge zero rows. -/
theorem complete_tight_kernel {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) (hm : 2≤(tetrahedra G).card)
    (f : SetFunction V) (hn : TranslationNormalized f)
    (hf : TightVariation (setFunction h s) f) :
    ∃ a : ℝ,f=a • setFunction h s := by
  classical
  obtain ⟨a,ha⟩:=all_clique_scales_equal h s hn hf
  let y:=mobius f-a • coefficients h s
  have hyp : ∀ C,C.card≠2 → y C=0:=residual_pair_supported h s hm hn hf a ha
  have hyf:=tightVariation_cliqueSupported h s hn hf
  have hyz:=coefficients_cliqueSupported h s
  have hzeta : zeta y=f-a • setFunction h s := by
    change zetaLinear (mobius f-a • coefficients h s)=_
    rw [map_sub,map_smul]
    change zeta (mobius f)-a • zeta (coefficients h s)=_
    rw [zeta_mobius]
    rfl
  have hy0 : y=0 := by
    funext C
    by_cases hc2 : C.card=2
    · obtain ⟨u,v,huv,rfl⟩:=card_eq_two.mp hc2
      by_cases hedge : G.Adj u v
      · obtain ⟨A,hu,hv,hA⟩:=edge_has_zero_slack h s hedge
        have hvar:=hf u v huv A hu hv hA
        have hrow:=zeta_pairSupported_delta_unordered y hyp huv hu hv
        rw [hzeta,delta_sub,delta_smul,hvar,hA,mul_zero,sub_zero] at hrow
        exact hrow.symm
      · change mobius f {u,v}-a*coefficients h s {u,v}=0
        rw [hyf.2.2 {u,v} u v (by simp) (by simp) huv hedge,
          hyz.2.2 {u,v} u v (by simp) (by simp) huv hedge,mul_zero,sub_zero]
    · exact hyp C hc2
  refine ⟨a,sub_eq_zero.mp ?_⟩
  rw [← hzeta,hy0]
  exact (zeta_eq_zero_iff _).mpr rfl

theorem setFunction_extreme {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) (hm : 2≤(tetrahedra G).card) :
    ExtremeSupermodular (setFunction h s) :=
  extremeSupermodular_of_tightEquations (setFunction_normalized_graphical h s).1
    (setFunction_supermodular h s) (setFunction_ne_zero h s)
    (complete_tight_kernel h s hm)

end ThreeTreeStates
end GraphicalZonotopes
