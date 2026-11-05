module

public import Papers.GraphicalZonotopes.AffineDimension
public import Papers.GraphicalZonotopes.PositiveDecomposition

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
section Unordered
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Dependence on a displayed set of coordinates is an equality of the
original set function, not an informal support convention. -/
def DependsOn (z : SetFunction V) (S : Finset V) : Prop :=
  ∀ T, z T = z (T ∩ S)

theorem DependsOn.add {f g : SetFunction V} {S : Finset V}
    (hf : DependsOn f S) (hg : DependsOn g S) : DependsOn (f+g) S := by
  intro T
  change f T+g T=f (T∩S)+g (T∩S)
  rw [hf T,hg T]

theorem DependsOn.of_smul {z : SetFunction V} {S : Finset V} {a : ℝ}
    (ha : a ≠ 0) (h : DependsOn (a • z) S) : DependsOn z S := by
  intro T
  exact mul_left_cancel₀ ha (h T)

theorem setMonomial_dependsOn (C : Finset V) : DependsOn (setMonomial C) C := by
  intro T
  simp [setMonomial,subset_inter_iff]

theorem DependsOn.smul {z : SetFunction V} {S : Finset V}
    (h : DependsOn z S) (a : ℝ) : DependsOn (a • z) S := by
  intro T
  change a*z T=a*z (T∩S)
  rw [h T]

theorem zeta_dependsOn {y : SetFunction V} {S : Finset V}
    (hy : ∀ C, ¬ C ⊆ S → y C = 0) : DependsOn (zeta y) S := by
  intro T
  rw [zeta_eq_sum_monomials]
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply sum_congr rfl
  intro C hC
  by_cases hCS : C ⊆ S
  · simp [setMonomial,subset_inter_iff,hCS]
  · simp [hy C hCS]

theorem DependsOn.delta_eq_zero {z : SetFunction V} {S : Finset V}
    (h : DependsOn z S) {u v : V} (hu : u ∉ S) (T : Finset V) :
    delta z u v T = 0 := by
  have hi : ∀ A : Finset V, insert u A ∩ S = A ∩ S := by
    intro A
    ext x
    simp only [mem_inter,mem_insert]
    constructor
    · rintro ⟨hx,hxS⟩
      rcases hx with rfl | hx
      · exact False.elim (hu hxS)
      · exact ⟨hx,hxS⟩
    · rintro ⟨hx,hxS⟩
      exact ⟨Or.inr hx,hxS⟩
  unfold delta
  rw [h (insert u (insert v T)),h (insert u T),h (insert v T),h T,hi,hi]
  ring

theorem basePolytope_coordinate_zero_of_dependsOn {z : SetFunction V} {S : Finset V}
    (hn : TranslationNormalized z) (hd : DependsOn z S) {u : V} (hu : u ∉ S)
    {x : V → ℝ} (hx : x ∈ basePolytope z) : x u = 0 := by
  have hl : 0 ≤ x u := by simpa [hn.2 u,subsetSum] using hx.2 {u}
  have he : univ.erase u ∩ S = S := by
    ext v
    simp only [mem_inter,mem_erase,mem_univ,true_and,and_true]
    constructor
    · exact fun h => h.2
    · intro hv
      exact ⟨fun hvu => hu (hvu ▸ hv),hv⟩
  have hz : z (univ.erase u) = z univ := by
    rw [hd (univ.erase u),hd univ,he,univ_inter]
  have hh := hx.2 (univ.erase u)
  rw [hz] at hh
  have hsum : subsetSum x (univ.erase u)+x u=z univ := by
    rw [subsetSum,sum_erase_add _ _ (mem_univ u)]
    exact hx.1
  linarith

def evaluationLinear (u : V) : (V → ℝ) →ₗ[ℝ] ℝ where
  toFun x := x u
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem vectorSpan_le_evaluation_ker_of_dependsOn {z : SetFunction V} {S : Finset V}
    (hn : TranslationNormalized z) (hs : Supermodular z) (hd : DependsOn z S)
    {u : V} (hu : u ∉ S) : vectorSpan ℝ (basePolytope z) ≤ (evaluationLinear u).ker := by
  obtain ⟨p,hp⟩ := basePolytope_nonempty hn.1 hs
  rw [vectorSpan_eq_span_vsub_set_right ℝ hp]
  apply Submodule.span_le.mpr
  rintro x ⟨q,hq,rfl⟩
  change q u-p u=0
  rw [basePolytope_coordinate_zero_of_dependsOn hn hd hu hq,
    basePolytope_coordinate_zero_of_dependsOn hn hd hu hp,sub_self]

/-- Full affine dimension forces every coordinate to be present in any set
on which the normalized function depends. -/
theorem fullDimension_dependsOn_eq_univ {n : ℕ} (hn : 2 ≤ n)
    {z : SetFunction (Fin n)} (hzn : TranslationNormalized z) (hzs : Supermodular z)
    (hfull : Module.finrank ℝ (vectorSpan ℝ (basePolytope z)) = n-1)
    {S : Finset (Fin n)} (hdep : DependsOn z S) : S = univ := by
  have hne := basePolytope_nonempty hzn.1 hzs
  have hW : vectorSpan ℝ (basePolytope z) = (totalLinear (V := Fin n)).ker :=
    Submodule.eq_of_le_of_finrank_eq (vectorSpan_basePolytope_le_total_ker hne)
      (hfull.trans (finrank_total_ker (by omega)).symm)
  apply eq_univ_of_forall
  intro u
  by_contra hu
  have hex : ∃ v : Fin n, v ≠ u := by
    by_cases hu0 : u = ⟨0,by omega⟩
    · refine ⟨⟨1,by omega⟩,?_⟩
      rw [hu0]
      intro h
      have hv := congrArg Fin.val h
      change (1 : ℕ)=0 at hv
      omega
    · exact ⟨⟨0,by omega⟩,Ne.symm hu0⟩
  obtain ⟨v,hvu⟩ := hex
  have hroot : basisVector u-basisVector v ∈ (totalLinear (V := Fin n)).ker := by
    change subsetSum (basisVector u-basisVector v) univ=0
    simp
  rw [← hW] at hroot
  have hzero := vectorSpan_le_evaluation_ker_of_dependsOn hzn hzs hdep hu hroot
  change (basisVector u-basisVector v) u=0 at hzero
  simp [basisVector,Pi.single_apply,hvu,Ne.symm hvu] at hzero

theorem TranslationNormalized.finset_sum {I : Type*} (s : Finset I)
    (f : I → SetFunction V) (hf : ∀ i ∈ s, TranslationNormalized (f i)) :
    TranslationNormalized (∑ i ∈ s, f i) := by
  constructor
  · change (∑ i ∈ s, f i) ∅=0
    rw [Finset.sum_apply]
    exact sum_eq_zero fun i hi => (hf i hi).1
  · intro v
    change (∑ i ∈ s, f i) {v}=0
    rw [Finset.sum_apply]
    exact sum_eq_zero fun i hi => (hf i hi).2 v

theorem TranslationNormalized.add {f g : SetFunction V}
    (hf : TranslationNormalized f) (hg : TranslationNormalized g) :
    TranslationNormalized (f+g) := by
  exact ⟨by change f ∅+g ∅=0; rw [hf.1,hg.1,add_zero],
    fun v => by change f {v}+g {v}=0; rw [hf.2 v,hg.2 v,add_zero]⟩

/-- Every nonzero member of an arbitrary finite positive decomposition of an
extreme normalized function is a strictly positive multiple of it. -/
theorem ExtremeSupermodular.finite_summand {I : Type*} [Fintype I]
    {z : SetFunction V} (hz : ExtremeSupermodular z) (f : I → SetFunction V)
    (hn : ∀ i, TranslationNormalized (f i)) (hs : ∀ i, Supermodular (f i))
    (he : ∑ i, f i=z) {i : I} (hi : f i ≠ 0) :
    ∃ a : ℝ, 0 < a ∧ f i=a • z := by
  classical
  let g := ∑ j ∈ univ.erase i, f j
  have hgn : TranslationNormalized g := TranslationNormalized.finset_sum _ _ (fun j hj => hn j)
  have hgs : Supermodular g := Supermodular.finset_sum _ _ (fun j hj => hs j)
  have hsum : f i+g=z := by
    rw [add_comm,show g=∑ j ∈ univ.erase i,f j from rfl,
      sum_erase_add _ _ (mem_univ i),he]
  obtain ⟨a,ha,hf⟩ := hz.2.2.2 (f i) g (hn i) hgn (hs i) hgs hsum
  refine ⟨a,lt_of_le_of_ne ha ?_,hf⟩
  intro hzero
  exact hi (by simpa [← hzero] using hf)

end Unordered

namespace PositiveDecomposition
variable {V : Type*} [Fintype V] [LinearOrder V]

theorem DependsOn.adjusted {z : SetFunction V} {S : Finset V}
    (h : GraphicalZonotopes.DependsOn z S) : GraphicalZonotopes.DependsOn (adjusted z) S := by
  apply h.add
  apply zeta_dependsOn
  intro C hC
  by_cases hcard : C.card = 2
  · obtain ⟨u,v,huv,rfl⟩ := card_eq_two.mp hcard
    rw [allocation_pair z huv]
    have hzero : minimumSlack z u v=0 := by
      by_cases hu : u ∈ S
      · have hv : v ∉ S := fun hv => hC (insert_subset hu (singleton_subset_iff.mpr hv))
        have hz : ∀ T, u ∉ T → v ∉ T → delta z u v T=0 := by
          intro T _ _
          have hcomm : delta z u v T=delta z v u T := by
            unfold delta
            rw [insert_comm]
            ring
          rw [hcomm]
          exact h.delta_eq_zero hv T
        obtain ⟨T,hTu,hTv,hmin⟩ := exists_minimumSlack z u v
        exact hmin.symm.trans (hz T hTu hTv)
      · obtain ⟨T,hTu,hTv,hmin⟩ := exists_minimumSlack z u v
        exact hmin.symm.trans (h.delta_eq_zero hu T)
    simp [hzero]
  · exact allocation_zero z hcard

end PositiveDecomposition
end GraphicalZonotopes
