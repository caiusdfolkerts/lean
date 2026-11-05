module

public import Recovery.Unimodular.WeakFano.EffectiveFiniteMatrix
public import Recovery.Unimodular.WeakFano.EffectiveBinaryMoves
public import Recovery.Unimodular.Graver.AllPrimitiveMoves
public import Unimodular.FanPatches

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open Set TauCeti.Toric

namespace Unimodular.EffectiveMatrix

variable {n : ℕ} {E : Type*} [Fintype E] [DecidableEq E] [Encodable E]

/-- The entire primitive-replacement set, computed directly from the raw
integer ray family. The proven all-Graver bound includes unusable moves. -/
def moves (u : E → Lattice n) : Finset (Column u → ℤ) :=
  (EffectiveGraver.allPrimitiveMoves (finiteMatrix u)).image (encodeCoefficients u).symm

/-- A complete finite list of fan codes. Binary enumeration is justified
below by the original integral gluing theorem, rather than assumed. -/
def fanSolutions (u : E → Lattice n) : Finset (Column u → ℤ) :=
  EffectiveBinaryMoves.solutions (equation u) target

/-- Exact enumeration of every primitive integer kernel vector. -/
theorem mem_moves_iff (u : E → Lattice n) (g : Column u → ℤ) :
    g ∈ moves u ↔ Graver.Primitive (equation u).ker g := by
  rw [moves, Finset.mem_image]
  constructor
  · rintro ⟨h, hh, he⟩
    have hp := (EffectiveGraver.mem_allPrimitiveMoves (finiteMatrix u) h).1 hh
    change Graver.Primitive (finiteEquation u).ker h at hp
    have he' : encodeCoefficients u g = h := by
      rw [← he, AddEquiv.apply_symm_apply]
    rw [← he'] at hp
    exact (finite_primitive_iff u g).1 hp
  · intro hg
    refine ⟨encodeCoefficients u g, ?_, (encodeCoefficients u).symm_apply_apply g⟩
    exact (EffectiveGraver.mem_allPrimitiveMoves (finiteMatrix u) _).2
      ((finite_primitive_iff u g).2 hg)

noncomputable section
attribute [local instance] Classical.propDecidable
local notation "ι₀" => EffectiveAllowed.embedding n

/-- Semantic interpretation of a genuine fan in the executable column code. -/
def fanCode (u : E → Lattice n) (hnz : ∀ e, embed (u e) ≠ 0)
    (Φ : AllowedBlocks.FanOnRays ι₀ u) : Column u → ℤ :=
  (coefficientEquiv u hnz).symm (AllowedBlocks.indicator ι₀ u Φ)

@[simp] theorem coefficient_fanCode (u : E → Lattice n) (hnz : ∀ e, embed (u e) ≠ 0)
    (Φ : AllowedBlocks.FanOnRays ι₀ u) :
    coefficientEquiv u hnz (fanCode u hnz Φ) = AllowedBlocks.indicator ι₀ u Φ :=
  (coefficientEquiv u hnz).apply_symm_apply _

theorem fanCode_injective (u : E → Lattice n) (hnz : ∀ e, embed (u e) ≠ 0) :
    Function.Injective (fanCode u hnz) := by
  intro Φ Ψ h
  apply AllowedBlocks.indicator_injective ι₀ u hnz
  have he := congrArg (coefficientEquiv u hnz) h
  simpa only [coefficient_fanCode] using he

theorem fanCode_solution (u : E → Lattice n) (hnz : ∀ e, embed (u e) ≠ 0)
    (hpos : PointedCone.hull ℝ (Set.range (fun e => embed (u e))) = ⊤)
    (Φ : AllowedBlocks.FanOnRays ι₀ u) :
    (∀ s, 0 ≤ fanCode u hnz Φ s) ∧ equation u (fanCode u hnz Φ) = target := by
  have hspan := RayHyperplanes.span_range_eq_top_of_positive _ hpos
  apply (nonnegative_solution_iff u hnz hspan _).2
  rw [coefficient_fanCode]
  exact AllowedBlocks.indicator_isSolution ι₀ u embedding_integral hnz hpos
    (EffectiveDirection.direction_generic u hspan) Φ

theorem fanCode_mem_solutions (u : E → Lattice n) (hnz : ∀ e, embed (u e) ≠ 0)
    (hpos : PointedCone.hull ℝ (Set.range (fun e => embed (u e))) = ⊤)
    (Φ : AllowedBlocks.FanOnRays ι₀ u) : fanCode u hnz Φ ∈ fanSolutions u := by
  have hc := fanCode_solution u hnz hpos Φ
  exact (EffectiveBinaryMoves.mem_solutions (equation u) target _).2
    ⟨fun s => by have hs := solution_zero_one u hnz hpos _ hc s; omega, hc.2⟩

/-- Every actual complete fan occurs exactly once in the computed finite
solution list. No projectivity, simpliciality, or smoothness is imposed. -/
theorem solutions_iff_unique_fan (u : E → Lattice n) (hnz : ∀ e, embed (u e) ≠ 0)
    (hpos : PointedCone.hull ℝ (Set.range (fun e => embed (u e))) = ⊤)
    (c : Column u → ℤ) :
    c ∈ fanSolutions u ↔ ∃! Φ : AllowedBlocks.FanOnRays ι₀ u, fanCode u hnz Φ = c := by
  constructor
  · intro hc
    obtain ⟨hbin, heq⟩ := (EffectiveBinaryMoves.mem_solutions (equation u) target c).1 hc
    have hnonneg : ∀ s, 0 ≤ c s := fun s => (hbin s).1
    obtain ⟨Φ, hΦ, hr, hi⟩ := (computed_matrix_gluing u hnz hpos c).1 ⟨hnonneg, heq⟩
    let Ψ : AllowedBlocks.FanOnRays ι₀ u := ⟨Φ, hΦ, hr⟩
    have hcode : fanCode u hnz Ψ = c := by
      apply (coefficientEquiv u hnz).injective
      rw [coefficient_fanCode]
      exact (funext hi).symm
    refine ⟨Ψ, hcode, ?_⟩
    intro Ω hΩ
    exact fanCode_injective u hnz (hΩ.trans hcode.symm)
  · rintro ⟨Φ, hΦ, _⟩
    rw [← hΦ]
    exact fanCode_mem_solutions u hnz hpos Φ

/-- The exact admissibility clause: adding an enumerated primitive move
produces another genuine fan precisely when every new coefficient is
nonnegative. All other equations are preserved by the proved kernel. -/
theorem computed_replacement_allowed_iff (u : E → Lattice n)
    (hnz : ∀ e, embed (u e) ≠ 0)
    (hpos : PointedCone.hull ℝ (Set.range (fun e => embed (u e))) = ⊤)
    (c g : Column u → ℤ) (hc : c ∈ fanSolutions u) (hg : g ∈ moves u) :
    c + g ∈ fanSolutions u ↔ ∀ s, 0 ≤ (c + g) s := by
  have hcA := ((EffectiveBinaryMoves.mem_solutions (equation u) target c).1 hc).2
  have hgA := ((mem_moves_iff u g).1 hg).1
  have hcgA : equation u (c + g) = target := by
    rw [map_add, hcA, show equation u g = 0 from hgA, add_zero]
  constructor
  · intro h
    have hb := ((EffectiveBinaryMoves.mem_solutions (equation u) target _).1 h).1
    intro s
    exact (hb s).1
  · intro h
    exact (EffectiveBinaryMoves.mem_solutions (equation u) target _).2
      ⟨fun s => by have hs := solution_zero_one u hnz hpos _ ⟨h, hcgA⟩ s; omega, hcgA⟩

/-- Every pair of genuine complete fans is connected by the explicitly
computed entire Graver basis, and every intermediate maximal cone belongs
to one of the two endpoints. -/
theorem computed_fan_connectivity (u : E → Lattice n) (hnz : ∀ e, embed (u e) ≠ 0)
    (hpos : PointedCone.hull ℝ (Set.range (fun e => embed (u e))) = ⊤)
    (Φ Ψ : AllowedBlocks.FanOnRays ι₀ u) :
    Relation.ReflTransGen
      (fun A B : AllowedBlocks.FanOnRays ι₀ u =>
        fanCode u hnz B - fanCode u hnz A ∈ moves u ∧
        AllowedBlocks.UsesEndpointCones ι₀ u Φ Ψ A ∧
        AllowedBlocks.UsesEndpointCones ι₀ u Φ Ψ B) Φ Ψ := by
  have hspan := RayHyperplanes.span_range_eq_top_of_positive _ hpos
  obtain ⟨G, hG, hpath⟩ := AllowedBlocks.theorem_1_1_connectivity ι₀ u
    embedding_integral hnz hpos (EffectiveDirection.direction_generic u hspan) Φ Ψ
  apply Relation.ReflTransGen.mono (fun A B hAB => ?_) _ _ hpath
  refine ⟨?_, hAB.2.1, hAB.2.2⟩
  apply (mem_moves_iff u _).2
  apply (primitive_iff u hnz hspan _).2
  rw [map_sub, coefficient_fanCode, coefficient_fanCode]
  exact (hG _).1 hAB.1

/-- Complete coordinate-input form of Lemma 3.3: one executable program
returns every primitive replacement, and these moves give the paper's full
fan connectivity and exact nonnegativity admissibility. -/
theorem lemma_3_3_effective_coordinate (u : E → Lattice n)
    (hnz : ∀ e, embed (u e) ≠ 0)
    (hpos : PointedCone.hull ℝ (Set.range (fun e => embed (u e))) = ⊤) :
    (∀ g : Column u → ℤ, g ∈ moves u ↔
      Graver.Primitive (AllowedBlocks.equationMap ι₀ u
        (embed (EffectiveDirection.direction u))).ker (coefficientEquiv u hnz g)) ∧
    (∀ c : Column u → ℤ, c ∈ fanSolutions u ↔
      ∃! Φ : AllowedBlocks.FanOnRays ι₀ u, fanCode u hnz Φ = c) ∧
    (∀ c ∈ fanSolutions u, ∀ g ∈ moves u,
      c + g ∈ fanSolutions u ↔ ∀ s, 0 ≤ (c + g) s) ∧
    ∀ Φ Ψ : AllowedBlocks.FanOnRays ι₀ u,
      Relation.ReflTransGen (fun A B : AllowedBlocks.FanOnRays ι₀ u =>
        fanCode u hnz B - fanCode u hnz A ∈ moves u ∧
        AllowedBlocks.UsesEndpointCones ι₀ u Φ Ψ A ∧
        AllowedBlocks.UsesEndpointCones ι₀ u Φ Ψ B) Φ Ψ := by
  have hspan := RayHyperplanes.span_range_eq_top_of_positive _ hpos
  exact ⟨fun g => (mem_moves_iff u g).trans (primitive_iff u hnz hspan g),
    solutions_iff_unique_fan u hnz hpos,
    fun c hc g hg => computed_replacement_allowed_iff u hnz hpos c g hc hg,
    computed_fan_connectivity u hnz hpos⟩

end
end Unimodular.EffectiveMatrix

#print axioms Unimodular.EffectiveMatrix.moves
#print axioms Unimodular.EffectiveMatrix.fanSolutions
#print axioms Unimodular.EffectiveMatrix.mem_moves_iff
#print axioms Unimodular.EffectiveMatrix.lemma_3_3_effective_coordinate
#check Unimodular.EffectiveMatrix.lemma_3_3_effective_coordinate
