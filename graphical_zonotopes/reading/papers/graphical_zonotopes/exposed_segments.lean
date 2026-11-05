module

public import Papers.GraphicalZonotopes.Directions

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A nondegenerate exposed one-dimensional face, defined by an actual
supporting linear functional and equality with a genuine closed segment. -/
def IsExposedSegment (Q : Set (V → ℝ)) (p q : V → ℝ) : Prop :=
  p ≠ q ∧ ∃ ℓ : (V → ℝ) →ₗ[ℝ] ℝ, ∃ a : ℝ,
    (∀ x ∈ Q, a ≤ ℓ x) ∧ {x ∈ Q | ℓ x = a} = segment ℝ p q

/-- The paper's actual direction graph: its edges are precisely standard-root
parallel directions realized by nondegenerate exposed edges. -/
def ActualRootEdge (Q : Set (V → ℝ)) (u v : V) : Prop :=
  u ≠ v ∧ ∃ p q, IsExposedSegment Q p q ∧
    ∃ a : ℝ, a ≠ 0 ∧ q-p = a • (basisVector u-basisVector v)

def subsetSumLinear (S : Finset V) : (V → ℝ) →ₗ[ℝ] ℝ where
  toFun x := subsetSum x S
  map_add' x y := subsetSum_add x y S
  map_smul' a x := subsetSum_smul a x S

def prefixFaceFunctional {n : ℕ} (e : Fin n ≃ V) (m : ℕ) :
    (V → ℝ) →ₗ[ℝ] ℝ :=
  ∑ j ∈ (univ : Finset (Fin (n+1))).filter (fun j => j.val ≠ m),
    subsetSumLinear (orderPrefix e j.val)

def prefixFaceLevel {n : ℕ} (z : SetFunction V) (e : Fin n ≃ V) (m : ℕ) : ℝ :=
  ∑ j ∈ (univ : Finset (Fin (n+1))).filter (fun j => j.val ≠ m), z (orderPrefix e j.val)

theorem prefixFace_lower_bound {n : ℕ} (z : SetFunction V) (e : Fin n ≃ V)
    (m : ℕ) {x : V → ℝ} (hx : x ∈ basePolytope z) :
    prefixFaceLevel z e m ≤ prefixFaceFunctional e m x := by
  unfold prefixFaceLevel prefixFaceFunctional
  simp only [LinearMap.sum_apply, subsetSumLinear, LinearMap.coe_mk, AddHom.coe_mk]
  exact sum_le_sum (fun j hj => hx.2 _)

theorem prefixFace_eq_iff {n : ℕ} (z : SetFunction V) (e : Fin n ≃ V)
    (m : ℕ) {x : V → ℝ} (hx : x ∈ basePolytope z) :
    prefixFaceFunctional e m x = prefixFaceLevel z e m ↔
      ∀ j : Fin (n+1), j.val ≠ m → subsetSum x (orderPrefix e j.val) = z (orderPrefix e j.val) := by
  unfold prefixFaceFunctional prefixFaceLevel
  simp only [LinearMap.sum_apply, subsetSumLinear, LinearMap.coe_mk, AddHom.coe_mk]
  have hnn : ∀ j ∈ (univ : Finset (Fin (n+1))).filter (fun j => j.val ≠ m),
      0 ≤ subsetSum x (orderPrefix e j.val) - z (orderPrefix e j.val) :=
    fun j _ => sub_nonneg.mpr (hx.2 _)
  rw [← sub_eq_zero, ← sum_sub_distrib, sum_eq_zero_iff_of_nonneg hnn]
  simp only [mem_filter, mem_univ, true_and, sub_eq_zero]

theorem coordinate_of_prefix_equalities {n : ℕ} (z : SetFunction V) (e : Fin n ≃ V)
    (x : V → ℝ) (j : Fin n)
    (h0 : subsetSum x (orderPrefix e j.val) = z (orderPrefix e j.val))
    (h1 : subsetSum x (orderPrefix e (j.val+1)) = z (orderPrefix e (j.val+1))) :
    x (e j) = greedyPoint z e (e j) := by
  rw [orderPrefix_succ, subsetSum_insert (not_mem_orderPrefix e j), h0] at h1
  rw [greedyPoint_apply]
  linarith

/-- The neighboring greedy segment is an exposed edge whenever its elemental
slack is positive. The proof fixes every other prefix, reconstructs every
coordinate, and identifies the remaining interval exactly. -/
theorem exposedSegment_of_positive_delta {z : SetFunction V}
    (hn : Normalized z) (hs : Supermodular z)
    {u v : V} (huv : u ≠ v) {S : Finset V} (hu : u ∉ S) (hv : v ∉ S)
    (hδ : 0 < delta z u v S) : ActualRootEdge (basePolytope z) u v := by
  obtain ⟨e,h0,h1⟩ := exists_pair_enumeration S huv hu hv
  let p := greedyPoint z e
  let q := greedyPoint z (e.trans (Equiv.swap u v))
  let d := delta z u v S
  let m := (e.symm v).val
  have hd0 : d ≠ 0 := ne_of_gt hδ
  have hadj := pair_enumeration_adjacent e S hu h0 h1
  have hp : p ∈ basePolytope z := greedyPoint_mem_basePolytope hn hs e
  have hq : q ∈ basePolytope z := greedyPoint_mem_basePolytope hn hs _
  have hdiff : q-p = d • (basisVector u-basisVector v) :=
    greedyPoint_swap_difference z e S huv hu hv h0 h1
  have hqu : q u-p u = d := by
    have h := congrFun hdiff u
    simpa [basisVector, Pi.single_apply, huv, Ne.symm huv] using h
  have hqv : q v-p v = -d := by
    have h := congrFun hdiff v
    simpa [basisVector, Pi.single_apply, huv, Ne.symm huv] using h
  have hpq : p ≠ q := by
    intro he
    rw [he,sub_self] at hqu
    exact (ne_of_gt hδ) hqu.symm
  refine ⟨huv,p,q,⟨hpq,?_,?_,?_,?_⟩,d,ne_of_gt hδ,hdiff⟩
  · exact prefixFaceFunctional e m
  · exact prefixFaceLevel z e m
  · intro x hx
    exact prefixFace_lower_bound z e m hx
  · apply Set.Subset.antisymm
    · rintro x ⟨hx,hlevel⟩
      have hprefix := (prefixFace_eq_iff z e m hx).mp hlevel
      have hpref (j : Fin ((Fintype.card V)+1)) :=
        greedyPoint_prefix z hn e j.val (by omega)
      have hxS : subsetSum x S = z S := by
        have h := hprefix ⟨(e.symm u).val,by omega⟩ (by dsimp [m]; omega)
        simpa [h0] using h
      have hpS : subsetSum p S = z S := by
        simpa [p,h0] using hpref ⟨(e.symm u).val,by omega⟩
      have hafter : orderPrefix e ((e.symm v).val+1) = insert v (insert u S) := by
        rw [orderPrefix_succ, e.apply_symm_apply,h1]
      have hxTot : x u+x v = p u+p v := by
        have hx' := hprefix ⟨(e.symm v).val+1,by omega⟩ (by dsimp [m]; omega)
        have hp' := hpref ⟨(e.symm v).val+1,by omega⟩
        rw [hafter,subsetSum_insert (by simp [huv,Ne.symm huv,hv]),subsetSum_insert hu,hxS] at hx'
        rw [hafter,subsetSum_insert (by simp [huv,Ne.symm huv,hv]),subsetSum_insert hu,hpS] at hp'
        linarith
      have hpu : p u = z (insert u S)-z S := by
        have h := greedyPoint_apply z e (e.symm u)
        simpa [p,h0] using h
      have hlow : p u ≤ x u := by
        have h := hx.2 (insert u S)
        rw [subsetSum_insert hu,hxS] at h
        linarith
      have hupp : x u ≤ p u+d := by
        have h := hx.2 (insert v S)
        rw [subsetSum_insert hv,hxS] at h
        have hpuv : p u+p v = z (insert v (insert u S))-z S := by
          have hp' := hpref ⟨(e.symm v).val+1,by omega⟩
          rw [hafter,subsetSum_insert (by simp [huv,Ne.symm huv,hv]),subsetSum_insert hu,hpS] at hp'
          linarith
        dsimp [d,delta]
        rw [insert_comm u v]
        linarith
      have houtside : ∀ w, w ≠ u → w ≠ v → x w = p w := by
        intro w hwu hwv
        have hwu' : (e.symm w).val ≠ (e.symm u).val := by
          intro h
          exact hwu (e.symm.injective (Fin.ext h))
        have hwv' : (e.symm w).val ≠ (e.symm v).val := by
          intro h
          exact hwv (e.symm.injective (Fin.ext h))
        have hbefore := hprefix ⟨(e.symm w).val,by omega⟩ (by exact hwv')
        have hafter := hprefix ⟨(e.symm w).val+1,by omega⟩ (by dsimp [m]; omega)
        simpa [p] using coordinate_of_prefix_equalities z e x (e.symm w) hbefore hafter
      let a : ℝ := (p u+d-x u)/d
      let b : ℝ := (x u-p u)/d
      have ha : 0 ≤ a := div_nonneg (by linarith) hδ.le
      have hb : 0 ≤ b := div_nonneg (sub_nonneg.mpr hlow) hδ.le
      have hab : a+b = 1 := by dsimp [a,b]; field_simp [hd0]; ring
      refine ⟨a,b,ha,hb,hab,?_⟩
      have hbδ : b*d = x u-p u := by
        dsimp [b]
        field_simp [hd0]
      funext w
      change a * p w + b * q w = x w
      by_cases hwu : w = u
      · subst w
        have hqe : q u = p u+d := by linarith
        calc
          a * p u + b * q u = (a+b) * p u + b*d := by rw [hqe]; ring
          _ = x u := by rw [hab,one_mul,hbδ]; ring
      · by_cases hwv : w = v
        · subst w
          have hqe : q v = p v-d := by linarith
          calc
            a * p v + b * q v = (a+b) * p v - b*d := by rw [hqe]; ring
            _ = x v := by rw [hab,one_mul,hbδ]; linarith [hxTot]
        · have hqeq : q w = p w := by
            have h := congrFun hdiff w
            simp [basisVector,Pi.single_apply,hwu,hwv,Ne.symm hwu,Ne.symm hwv] at h
            exact sub_eq_zero.mp h
          rw [hqeq,houtside w hwu hwv,← add_mul,hab,one_mul]
    · have hpref : prefixFaceFunctional e m p = prefixFaceLevel z e m := by
        apply (prefixFace_eq_iff z e m hp).mpr
        intro j hj
        exact greedyPoint_prefix z hn e j.val (by omega)
      have hqref : prefixFaceFunctional e m q = prefixFaceLevel z e m := by
        apply (prefixFace_eq_iff z e m hq).mpr
        intro j hj
        have heq := orderPrefix_swap_of_ne e huv hadj hj
        rw [← heq]
        exact greedyPoint_prefix z hn (e.trans (Equiv.swap u v)) j.val (by omega)
      have hconv : Convex ℝ {x ∈ basePolytope z |
          prefixFaceFunctional e m x = prefixFaceLevel z e m} := by
        intro x hx y hy a b ha hb hab
        refine ⟨basePolytope_convex z hx.1 hy.1 ha hb hab, ?_⟩
        rw [map_add,map_smul,map_smul,hx.2,hy.2]
        change a * prefixFaceLevel z e m + b * prefixFaceLevel z e m = prefixFaceLevel z e m
        rw [← add_mul,hab,one_mul]
      exact hconv.segment_subset ⟨hp,hpref⟩ ⟨hq,hqref⟩

end GraphicalZonotopes
