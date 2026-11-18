module

public import Recovery.Unimodular.WeakFano.EffectiveMatrixRows
public import Recovery.Unimodular.WeakFano.EffectiveIndexing
public import Unimodular.FanConnectivity

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open Set TauCeti.Toric

namespace Unimodular.EffectiveMatrix

noncomputable section
attribute [local instance] Classical.propDecidable

variable {n : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
local notation "ι₀" => EffectiveAllowed.embedding n

/-- The computed generic-direction entry agrees with the original actual
interior-membership degree row for every full block. -/
theorem degreeEntry_eq (u : E → Lattice n) (hnz : ∀ e, embed (u e) ≠ 0)
    (hspan : Submodule.span ℝ (Set.range (fun e => embed (u e))) = ⊤)
    (s : Column u) : degreeEntry u s = AllowedBlocks.degreeRow ι₀ u
      (embed (EffectiveDirection.direction u)) (columnEquiv u hnz s) := by
  have hgen := RayHyperplanes.generic_for_allowed ι₀ u hnz hspan
    (EffectiveDirection.direction_generic u hspan)
  have hm : EffectiveConeDecision.contains (fun e : {e // e ∈ s.val} => u e.val)
        (EffectiveDirection.direction u) = true ↔
      embed (EffectiveDirection.direction u) ∈ AllowedBlocks.blockCone ι₀ u s.val := by
    rw [EffectiveConeDecision.contains_iff]
    change embed (EffectiveDirection.direction u) ∈
      EffectiveFaces.cone (fun e : {e // e ∈ s.val} => u e.val) ↔ _
    rw [EffectiveAllowed.cone_subtype]
  have hi : embed (EffectiveDirection.direction u) ∈ AllowedBlocks.blockCone ι₀ u s.val ↔
      embed (EffectiveDirection.direction u) ∈
        interior (AllowedBlocks.blockCone ι₀ u s.val : Set (Ambient n)) :=
    ⟨fun hx => (AllowedBlocks.family ι₀ u).generic_interior hgen
      (columnEquiv u hnz s) hx, fun hx => interior_subset hx⟩
  unfold degreeEntry AllowedBlocks.degreeRow
  simp only [columnEquiv_val]
  by_cases h : embed (EffectiveDirection.direction u) ∈
      interior (AllowedBlocks.blockCone ι₀ u s.val : Set (Ambient n))
  · rw [if_pos ((hm.trans hi).2 h), if_pos h]
  · rw [if_neg (mt (hm.trans hi).1 h), if_neg h]

theorem degree_sum_eq (u : E → Lattice n) (hnz : ∀ e, embed (u e) ≠ 0)
    (hspan : Submodule.span ℝ (Set.range (fun e => embed (u e))) = ⊤)
    (c : Column u → ℤ) :
    (∑ s, degreeEntry u s * c s) = ∑ s, AllowedBlocks.degreeRow ι₀ u
      (embed (EffectiveDirection.direction u)) s * coefficientEquiv u hnz c s := by
  apply Fintype.sum_equiv (columnEquiv u hnz)
  intro s
  rw [degreeEntry_eq u hnz hspan, coefficientEquiv_apply_column]

/-- Exact equality of every normalized signed integer fiber. The parameter
`d` is arbitrary; in particular the full kernel and degree-one fiber agree. -/
theorem equation_eq_level_iff (u : E → Lattice n) (hnz : ∀ e, embed (u e) ≠ 0)
    (hspan : Submodule.span ℝ (Set.range (fun e => embed (u e))) = ⊤)
    (c : Column u → ℤ) (d : ℤ) :
    equation u c = (fun r => r.elim d (fun _ => 0)) ↔
      AllowedBlocks.equationMap ι₀ u (embed (EffectiveDirection.direction u))
        (coefficientEquiv u hnz c) = (0, d) := by
  have hc : equation u c = (fun r => r.elim d (fun _ => 0)) ↔
      (∀ r : Row n E, ∑ s, boundaryEntry u r s * c s = 0) ∧
      (∑ s, degreeEntry u s * c s) = d := by
    constructor
    · intro h
      exact ⟨fun r => congrFun h (some r), congrFun h none⟩
    · rintro ⟨hb, hd⟩
      ext r
      cases r with
      | none => exact hd
      | some r => exact hb r
  have hg : AllowedBlocks.equationMap ι₀ u (embed (EffectiveDirection.direction u))
        (coefficientEquiv u hnz c) = (0, d) ↔
      AllowedBlocks.BoundaryCycle ι₀ u (coefficientEquiv u hnz c) ∧
      (∑ s, AllowedBlocks.degreeRow ι₀ u (embed (EffectiveDirection.direction u)) s *
        coefficientEquiv u hnz c s) = d := by
    constructor
    · intro h
      exact ⟨fun b => congrFun (congrArg Prod.fst h) b, congrArg Prod.snd h⟩
    · rintro ⟨hb, hd⟩
      exact Prod.ext (funext hb) hd
  rw [hc, hg, boundary_sums_iff u hnz hspan, degree_sum_eq u hnz hspan]

/-- Full integer-kernel correspondence, not merely agreement on binary or
nonnegative configurations. -/
theorem mem_kernel_iff (u : E → Lattice n) (hnz : ∀ e, embed (u e) ≠ 0)
    (hspan : Submodule.span ℝ (Set.range (fun e => embed (u e))) = ⊤)
    (c : Column u → ℤ) :
    c ∈ (equation u).ker ↔ coefficientEquiv u hnz c ∈
      (AllowedBlocks.equationMap ι₀ u (embed (EffectiveDirection.direction u))).ker := by
  have hz : (fun r : Option (Row n E) => r.elim (0 : ℤ) (fun _ => 0)) = 0 := by
    ext r
    cases r <;> rfl
  change equation u c = 0 ↔
    AllowedBlocks.equationMap ι₀ u (embed (EffectiveDirection.direction u))
      (coefficientEquiv u hnz c) = (0, 0)
  simpa only [hz] using equation_eq_level_iff u hnz hspan c 0

/-- Therefore the exact Graver-primitive replacements themselves agree,
including all elements never usable between zero-one fan indicators. -/
theorem primitive_iff (u : E → Lattice n) (hnz : ∀ e, embed (u e) ≠ 0)
    (hspan : Submodule.span ℝ (Set.range (fun e => embed (u e))) = ⊤)
    (g : Column u → ℤ) :
    Graver.Primitive (equation u).ker g ↔
      Graver.Primitive (AllowedBlocks.equationMap ι₀ u
        (embed (EffectiveDirection.direction u))).ker (coefficientEquiv u hnz g) := by
  exact (EffectiveIndexing.primitive_reindex_iff (columnEquiv u hnz) (equation u).ker
    (AllowedBlocks.equationMap ι₀ u (embed (EffectiveDirection.direction u))).ker
    (fun c => (mem_kernel_iff u hnz hspan c).symm) g).symm

/-- Exact normalized nonnegative fibers retain the intended geometric
meaning and all coefficients. -/
theorem nonnegative_solution_iff (u : E → Lattice n) (hnz : ∀ e, embed (u e) ≠ 0)
    (hspan : Submodule.span ℝ (Set.range (fun e => embed (u e))) = ⊤)
    (c : Column u → ℤ) :
    ((∀ s, 0 ≤ c s) ∧ equation u c = target) ↔
      AllowedBlocks.IsSolution ι₀ u (embed (EffectiveDirection.direction u))
        (coefficientEquiv u hnz c) := by
  rw [AllowedBlocks.isSolution_iff]
  have he := equation_eq_level_iff u hnz hspan c 1
  have hn := EffectiveIndexing.nonnegative_reindex_iff (columnEquiv u hnz) c
  exact and_congr hn.symm he

/-- The standard integral lattice is proved directly from its actual basis. -/
theorem embedding_integral : IsIntegralLattice (EffectiveAllowed.embedding n) := by
  apply isIntegralLattice_of_basis (Pi.basisFun ℤ (Fin n)) (Pi.basisFun ℝ (Fin n))
  intro i
  ext j
  simp [EffectiveAllowed.embedding, embed, Pi.basisFun_apply, Pi.single_apply]

/-- The computably constructed matrix has exactly the original complete
fans as its nonnegative normalized solutions, with the genuine fan object
and the identical original prescribed rays in the conclusion. -/
theorem computed_matrix_gluing (u : E → Lattice n) (hnz : ∀ e, embed (u e) ≠ 0)
    (hpos : PointedCone.hull ℝ (Set.range (fun e => embed (u e))) = ⊤)
    (c : Column u → ℤ) :
    ((∀ s, 0 ≤ c s) ∧ equation u c = target) ↔
      ∃ Φ : Fan ι₀, Φ.IsComplete ∧ AllowedBlocks.HasRays ι₀ u Φ ∧
        (∀ s : AllowedBlocks.FullBlock ι₀ u, coefficientEquiv u hnz c s =
          if AllowedBlocks.blockCone ι₀ u s.val ∈ Φ.cones then 1 else 0) := by
  have hspan := RayHyperplanes.span_range_eq_top_of_positive _ hpos
  exact (nonnegative_solution_iff u hnz hspan c).trans
    (AllowedBlocks.theorem_3_1 ι₀ u embedding_integral hnz hpos
      (coefficientEquiv u hnz c) (EffectiveDirection.direction_generic u hspan))

/-- No extra nonnegative solutions appear: every computed solution is the
literal zero-one indicator of a genuine complete fan. -/
theorem solution_zero_one (u : E → Lattice n) (hnz : ∀ e, embed (u e) ≠ 0)
    (hpos : PointedCone.hull ℝ (Set.range (fun e => embed (u e))) = ⊤)
    (c : Column u → ℤ) (hc : (∀ s, 0 ≤ c s) ∧ equation u c = target) :
    ∀ s, c s = 0 ∨ c s = 1 := by
  obtain ⟨Φ, hΦ, hr, hi⟩ := (computed_matrix_gluing u hnz hpos c).1 hc
  intro s
  have hh := hi (columnEquiv u hnz s)
  rw [coefficientEquiv_apply_column] at hh
  by_cases hm : AllowedBlocks.blockCone ι₀ u s.val ∈ Φ.cones
  · exact Or.inr (by simpa only [columnEquiv_val, if_pos hm] using hh)
  · exact Or.inl (by simpa only [columnEquiv_val, if_neg hm] using hh)

end
end Unimodular.EffectiveMatrix

#print axioms Unimodular.EffectiveMatrix.degreeEntry_eq
#print axioms Unimodular.EffectiveMatrix.mem_kernel_iff
#print axioms Unimodular.EffectiveMatrix.primitive_iff
#print axioms Unimodular.EffectiveMatrix.computed_matrix_gluing
#check Unimodular.EffectiveMatrix.computed_matrix_gluing
