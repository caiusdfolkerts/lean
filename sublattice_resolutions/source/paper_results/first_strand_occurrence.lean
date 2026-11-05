module
public import paper_results.part009

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.FirstStrandOccurrence -/
section

/-! # First occurrence of a normalized strand

This proof removes precisely the factors of homological degree zero from an
actual nonzero product. The retained factors stay in their original order.
Their number is at most the homological degree; the removed factors each have
internal degree `d`, so the normalized internal degree is unchanged in ℤ.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 900000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {k : Type u} [Field k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

lemma list_ofFn_get_map {A B : Type*} (xs : List A) (f : A → B) :
    List.ofFn (fun i : Fin xs.length => f (xs.get i)) = xs.map f := by
  change List.ofFn (f ∘ xs.get) = _
  rw [← List.map_ofFn, List.ofFn_get]

theorem fine_first_strand_occurrence (hE : finiteLatticeClosed n E)
    (m : ℕ) (hm : 0 < m) (α : Exponent (FiniteVariable.{u} n)) (p : ℕ)
    (hp : 0 < p)
    (hβ : bettiNumber (k := k) (exponentPowerFamily (finiteRowFamily n E) m) α p ≠ 0) :
    ∃ r : ℕ, 0 < r ∧ r ≤ p ∧ ∃ γ : Exponent (FiniteVariable.{u} n),
      (γ.degree : ℤ) - (r : ℤ) * d = (α.degree : ℤ) - (m : ℤ) * d ∧
        bettiNumber (k := k) (exponentPowerFamily (finiteRowFamily n E) r) γ p ≠ 0 := by
  obtain ⟨z, hzprod, hzp, hzboundary⟩ :=
    powerBetti_nonzero_homogeneous_product hE m hm α p hβ
  have hcycle : powerFaceDifferential m α z = 0 :=
    homogeneousProductCycleBoundarySpan_le_cycles m α
      (Submodule.mem_sup_left (Submodule.subset_span hzprod))
  let Z : LinearMap.ker (powerFaceDifferential (E := E) (k := k) m α) := ⟨z, hcycle⟩
  have hclass : reesHomologyPieceMap (k := k) hE (m, α) Z ≠ 0 :=
    fun h => hzboundary ((reesHomologyPieceMap_eq_zero_iff hE (m, α) Z).mp h)
  obtain ⟨β, x, hβα, hx, hzx⟩ := hzprod
  choose j hj using fun i => (hx i).2
  let cyc (i : Fin m) :
      LinearMap.ker (powerFaceDifferential (E := E) (k := k) 1 (β i)) :=
    ⟨x i, (hx i).1⟩
  let c (i : Fin m) := reesHomologyPieceMap (k := k) hE (1, β i) (cyc i)
  have hprod : (List.ofFn c).prod ≠ 0 := by
    rw [← reesHomologyPieceMap_product hE m α Z β cyc hβα hzx]
    exact hclass
  have hc (i : Fin m) : c i ≠ 0 := by
    intro hi
    exact hprod (List.prod_eq_zero (List.mem_ofFn.mpr ⟨i, hi⟩))
  have hsumDegree : p = ∑ i, j i := by
    let b := totalFaceBasis (k := k)
      (koszulFaces (exponentPowerFamily (finiteRowFamily n E) m) α)
    have hzj : z ∈ Grading.Piece b (fun F => F.val.card) (∑ i, j i) := by
      change z ∈ Submodule.span k (b '' {F | F.val.card = ∑ i, j i})
      dsimp only [b]
      rw [← totalFacePiece_eq_basis_span]
      apply faceDegree_of_support _ _ z.property
      rw [hzx]
      exact faceDegree_ordered_product m j (fun i => (x i).val)
        (fun i => faceDegree_forget _ _ (hj i))
    have hzp' : z ∈ Grading.Piece b (fun F => F.val.card) p := by
      change z ∈ Submodule.span k (b '' {F | F.val.card = p})
      dsimp only [b]
      rw [← totalFacePiece_eq_basis_span]
      exact hzp
    by_contra h
    have hz0 : z = 0 := (Grading.projection_eq_self hzp').symm.trans
      (Grading.projection_eq_zero h hzj)
    apply hzboundary
    rw [hz0]
    exact Submodule.zero_mem _
  let all := List.ofFn (fun i : Fin m => i)
  let selected := all.filter (fun i => decide (j i ≠ 0))
  let removed := all.filter (fun i => decide (¬j i ≠ 0))
  let r := selected.length
  have hallj : (all.map j).sum = p := by
    simpa only [all, List.map_ofFn, Function.comp_def, List.sum_ofFn] using hsumDegree.symm
  have hr : 0 < r := positive_filter_length_pos all j (by rw [hallj]; exact hp)
  have hrp : r ≤ p := by
    simpa only [hallj] using positive_filter_length_le_sum all j
  have hcentral : ∀ i ∈ all, ¬j i ≠ 0 → ∀ w, Commute (c i) w := by
    intro i _ hi w
    apply reesHomologyPieceMap_zero_degree_central hE (1, β i) (cyc i)
    simpa only [Classical.not_not.mp hi] using hj i
  have hselected : (selected.map c).prod ≠ 0 := by
    have hfilt : all.filter (fun i => @decide (j i ≠ 0) (Classical.propDecidable _)) = selected := by
      apply congrArg (fun f : Fin m → Bool => all.filter f)
      funext i
      by_cases hji : j i = 0 <;> simp [hji]
    have hh := prod_filter_ne_zero all c (fun i => j i ≠ 0) hcentral
      (by simpa only [all, List.map_ofFn, Function.comp_def] using hprod)
    rw [hfilt] at hh
    exact hh
  let β' (i : Fin r) := β (selected.get i)
  let cyc' (i : Fin r) := cyc (selected.get i)
  let γ : Exponent (FiniteVariable.{u} n) := ∑ i, β' i
  let Z' := firstPowerCycleProduct hE r β' cyc'
  have hclass' : reesHomologyPieceMap (k := k) hE (r, γ) Z' ≠ 0 := by
    rw [reesHomologyPieceMap_product hE r γ Z' β' cyc' rfl rfl]
    change (List.ofFn (fun i : Fin r => c (selected.get i))).prod ≠ 0
    rw [list_ofFn_get_map selected c]
    exact hselected
  have hretj : (∑ i : Fin r, j (selected.get i)) = p := by
    rw [← List.sum_ofFn, list_ofFn_get_map selected j]
    exact (positive_filter_sum all j).trans hallj
  have hZ'p : Z'.val ∈ totalFacePiece
      (koszulFaces (exponentPowerFamily (finiteRowFamily n E) r) γ) p := by
    have he := firstPowerCycleProduct_degree hE r β' cyc'
      (fun i => j (selected.get i)) (fun i => hj (selected.get i))
    simpa only [hretj] using he
  have hnew := powerBetti_nonzero_of_class hE r γ p Z' hZ'p hclass'
  have hremoved : (removed.map (fun i => (β i).degree)).sum = removed.length * d := by
    apply sum_map_eq_length_mul
    intro i hi
    have hji : j i = 0 := by
      simpa only [decide_eq_true_eq, not_not] using (List.mem_filter.mp hi).2
    exact firstPowerClass_zero_degree_internal hE (β i) (cyc i)
      (by simpa only [hji] using hj i) (hc i)
  have hγ : (selected.map (fun i => (β i).degree)).sum = γ.degree := by
    rw [← list_ofFn_get_map selected (fun i => (β i).degree), List.sum_ofFn]
    simp only [γ, β', map_sum]
    congr 1
  have hα : (all.map (fun i => (β i).degree)).sum = α.degree := by
    simp only [all, List.map_ofFn, Function.comp_def, List.sum_ofFn]
    rw [← map_sum, hβα]
  have hdegree := List.sum_map_filter_add_sum_map_filter_not
    (fun i => j i ≠ 0) (fun i => (β i).degree) all
  change (selected.map (fun i => (β i).degree)).sum +
    (removed.map (fun i => (β i).degree)).sum =
      (all.map (fun i => (β i).degree)).sum at hdegree
  rw [hγ, hremoved, hα] at hdegree
  have hlength : m = r + removed.length := by
    have he := List.length_eq_length_filter_add (l := all) (fun i => decide (j i ≠ 0))
    simpa only [r, selected, removed, all, List.length_ofFn, decide_not] using he
  refine ⟨r, hr, hrp, γ, ?_, hnew⟩
  have hdegreeZ := congrArg (fun a : ℕ => (a : ℤ)) hdegree
  have hlengthZ := congrArg (fun a : ℕ => (a : ℤ)) hlength
  push_cast at hdegreeZ hlengthZ
  nlinarith

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.fine_first_strand_occurrence

end
end
end


end
