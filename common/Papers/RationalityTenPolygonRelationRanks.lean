module
public import Papers.RationalityTenRelationSpaces
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Lean.Elab.Tactic.Omega

@[expose] public section
noncomputable section
open Matrix Module Set
open scoped BigOperators

namespace Papers.RationalityTen.ChirotopeDensity

/-- Actual homogeneous dependencies, extended by zero outside their support. -/
def globalRelationMap {n r : ℕ} (p : Fin n → Fin r → ℝ)
    (S : Finset (Fin n)) : facetRelationSpace p S →ₗ[ℝ] (Fin n → ℝ) :=
  (insideInjection (K := ℝ) S).comp (facetRelationSpace p S).subtype

def globalRelationSpace {n r : ℕ} (p : Fin n → Fin r → ℝ)
    (S : Finset (Fin n)) : Submodule ℝ (Fin n → ℝ) :=
  (globalRelationMap p S).range

theorem globalRelationMap_injective {n r : ℕ} (p : Fin n → Fin r → ℝ)
    (S : Finset (Fin n)) : Function.Injective (globalRelationMap p S) := by
  intro x y h
  apply Subtype.ext
  ext i
  have hi := congrFun h i.val
  simpa only [globalRelationMap,LinearMap.comp_apply,Submodule.subtype_apply,
    insideInjection,LinearMap.coe_mk,AddHom.coe_mk,dif_pos i.property] using hi

theorem globalRelationSpace_finrank {n r : ℕ} (p : Fin n → Fin r → ℝ)
    (S : Finset (Fin n)) :
    finrank ℝ (globalRelationSpace p S) + subsetRank p S = S.card := by
  rw [globalRelationSpace,LinearMap.finrank_range_of_inj (globalRelationMap_injective p S)]
  exact facetRelationSpace_finrank p S

theorem mem_globalRelationSpace_iff {n r : ℕ} (p : Fin n → Fin r → ℝ)
    (S : Finset (Fin n)) (v : Fin n → ℝ) :
    v ∈ globalRelationSpace p S ↔
      (∀ i, i∉S → v i=0) ∧ (Matrix.of p).transpose.mulVec v=0 := by
  classical
  constructor
  · rintro ⟨w,rfl⟩
    constructor
    · intro i hi
      simp [globalRelationMap,insideInjection,hi]
    · exact w.property
  · rintro ⟨hs,hp⟩
    let w : S→ℝ := fun i => v i.val
    have heq : insideInjection (K:=ℝ) S w = v := by
      ext i
      by_cases hi : i∈S
      · simp [insideInjection,w,hi]
      · simp [insideInjection,hi,hs i hi]
    have hw : w ∈ facetRelationSpace p S := by
      change (Matrix.of p).transpose.mulVec (insideInjection (K:=ℝ) S w)=0
      rw [heq]
      exact hp
    exact ⟨⟨w,hw⟩,heq⟩

theorem globalRelationSpace_mono {n r : ℕ} (p : Fin n → Fin r → ℝ)
    {S T : Finset (Fin n)} (hST : S⊆T) :
    globalRelationSpace p S ≤ globalRelationSpace p T := by
  intro v hv
  obtain ⟨hs,hp⟩ := (mem_globalRelationSpace_iff p S v).mp hv
  exact (mem_globalRelationSpace_iff p T v).mpr
    ⟨fun i hi => hs i (fun h => hi (hST h)),hp⟩

/-- The span of all polygon dependencies contained in a given facet. -/
def polygonRelationSpan {n r : ℕ} (p : Fin n → Fin r → ℝ)
    (L : Finset (Finset (Fin n))) : Submodule ℝ (Fin n → ℝ) :=
  L.sup (globalRelationSpace p)

theorem globalRelationSpace_le_polygonRelationSpan {n r : ℕ}
    (p : Fin n → Fin r → ℝ) {L : Finset (Finset (Fin n))}
    {S : Finset (Fin n)} (hS : S∈L) :
    globalRelationSpace p S ≤ polygonRelationSpan p L :=
  Finset.le_sup hS

theorem polygonRelationSpan_finrank_le {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (L : Finset (Finset (Fin n))) :
    finrank ℝ (polygonRelationSpan p L) ≤
      ∑ S∈L, finrank ℝ (globalRelationSpace p S) := by
  classical
  induction L using Finset.induction_on with
  | empty =>
    have hbot : polygonRelationSpan p ∅=⊥ := by
      apply le_bot_iff.mp
      exact Finset.sup_le (fun S hS => (Finset.notMem_empty S hS).elim)
    rw [hbot,finrank_bot,Finset.sum_empty]
  | @insert S L hS ih =>
    rw [polygonRelationSpan,Finset.sup_insert,Finset.sum_insert hS]
    exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans
      (Nat.add_le_add_left ih _)

theorem polygonRelationSpan_zero_shapes {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (L : Finset (Finset (Fin n)))
    (hrank : ∀ S∈L, subsetRank p S=3)
    (hzero : finrank ℝ (polygonRelationSpan p L)=0) :
    ∀ S∈L, S.card=3 := by
  intro S hS
  have hle := Submodule.finrank_mono (globalRelationSpace_le_polygonRelationSpan p hS)
  have hd := globalRelationSpace_finrank p S
  rw [hzero] at hle
  rw [hrank S hS] at hd
  omega

theorem subsetRank_of_independent {n r : ℕ} (p : Fin n → Fin r → ℝ)
    (S : Finset (Fin n))
    (hS : LinearIndependent ℝ (fun i : S => p i.val)) :
    subsetRank p S=S.card := by
  have hh := linearIndependent_iff_card_eq_finrank_span.mp hS
  change Fintype.card S=finrank ℝ (Submodule.span ℝ (Set.range (fun i:S => p i.val))) at hh
  rw [range_finset_family p S] at hh
  simpa only [Fintype.card_coe,subsetRank] using hh.symm

/-- A relation on four extreme-point labels has no zero coefficient:
otherwise it would be a dependence on at most three labels. -/
theorem four_relation_full_support {n r : ℕ}
    (p : Fin n → Fin r → ℝ)
    (hsmall : ∀ S : Finset (Fin n), S.card≤3 →
      LinearIndependent ℝ (fun i : S => p i.val))
    {S : Finset (Fin n)} (hS : S.card=4)
    {v : Fin n → ℝ} (hv : v∈globalRelationSpace p S) (hv0 : v≠0) :
    ∀ i∈S,v i≠0 := by
  classical
  intro i hi hvi
  have hcard : (S.erase i).card=3 := by rw [Finset.card_erase_of_mem hi,hS]
  have hrank : subsetRank p (S.erase i)=3 := by
    rw [subsetRank_of_independent p _ (hsmall _ (by omega)),hcard]
  have hdim := globalRelationSpace_finrank p (S.erase i)
  have hbot : globalRelationSpace p (S.erase i)=⊥ :=
    Submodule.finrank_eq_zero.mp (by omega)
  obtain ⟨hs,hpv⟩ := (mem_globalRelationSpace_iff p S v).mp hv
  have hmem : v∈globalRelationSpace p (S.erase i) := by
    apply (mem_globalRelationSpace_iff p _ v).mpr
    refine ⟨?_,hpv⟩
    intro j hj
    by_cases hji : j=i
    · simpa only [hji] using hvi
    · exact hs j (fun hjS => hj (Finset.mem_erase.mpr ⟨hji,hjS⟩))
  rw [hbot] at hmem
  exact hv0 hmem

theorem polygonRelationSpan_one_shapes {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (L : Finset (Finset (Fin n)))
    (hrank : ∀ S∈L, subsetRank p S=3)
    (hsmall : ∀ S : Finset (Fin n), S.card≤3 →
      LinearIndependent ℝ (fun i : S => p i.val))
    (hone : finrank ℝ (polygonRelationSpan p L)=1) :
    ∃ S∈L, S.card=4 ∧ ∀ T∈L,T≠S → T.card=3 := by
  classical
  have hcard : ∀ S∈L,S.card=3 ∨ S.card=4 := by
    intro S hS
    have hle := Submodule.finrank_mono (globalRelationSpace_le_polygonRelationSpan p hS)
    have hd := globalRelationSpace_finrank p S
    rw [hone] at hle
    rw [hrank S hS] at hd
    omega
  have hex : ∃ S∈L,S.card=4 := by
    by_contra h
    have hzero : ∀ S∈L,globalRelationSpace p S=⊥ := by
      intro S hS
      have hc : S.card=3 := (hcard S hS).resolve_right (fun hh => h ⟨S,hS,hh⟩)
      have hd := globalRelationSpace_finrank p S
      apply Submodule.finrank_eq_zero.mp
      rw [hrank S hS,hc] at hd
      omega
    have hbot : polygonRelationSpan p L=⊥ :=
      le_bot_iff.mp (Finset.sup_le fun S hS => (hzero S hS).le)
    rw [hbot,finrank_bot] at hone
    exact Nat.zero_ne_one hone
  obtain ⟨S,hSL,hS4⟩ := hex
  have hdimS : finrank ℝ (globalRelationSpace p S)=1 := by
    have hd := globalRelationSpace_finrank p S
    rw [hrank S hSL,hS4] at hd
    omega
  obtain ⟨w,hw⟩ := (Module.finrank_pos_iff_exists_ne_zero).mp
    (show 0<finrank ℝ (globalRelationSpace p S) by omega)
  have hw0 : w.val≠0 := fun hh => hw (Subtype.ext hh)
  have hspanS : globalRelationSpace p S=polygonRelationSpan p L :=
    Submodule.eq_of_le_of_finrank_eq
      (globalRelationSpace_le_polygonRelationSpan p hSL) (hdimS.trans hone.symm)
  refine ⟨S,hSL,hS4,?_⟩
  intro T hTL hTS
  rcases hcard T hTL with hT3 | hT4
  · exact hT3
  · exfalso
    have hdimT : finrank ℝ (globalRelationSpace p T)=1 := by
      have hd := globalRelationSpace_finrank p T
      rw [hrank T hTL,hT4] at hd
      omega
    have hspanT : globalRelationSpace p T=polygonRelationSpan p L :=
      Submodule.eq_of_le_of_finrank_eq
        (globalRelationSpace_le_polygonRelationSpan p hTL) (hdimT.trans hone.symm)
    have hwT : w.val∈globalRelationSpace p T := by
      rw [hspanT,←hspanS]
      exact w.property
    have hsupp := (mem_globalRelationSpace_iff p T w.val).mp hwT
    have hST : S⊆T := by
      intro i hi
      by_contra hin
      exact four_relation_full_support p hsmall hS4 w.property hw0 i hi (hsupp.1 i hin)
    exact hTS (Finset.eq_of_subset_of_card_le hST (by omega)).symm

end Papers.RationalityTen.ChirotopeDensity
