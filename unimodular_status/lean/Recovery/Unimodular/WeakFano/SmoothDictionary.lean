module

public import Recovery.Unimodular.WeakFano.OriginalIndependentBlocks
public import Recovery.Unimodular.WeakFano.ColumnRestriction
public import Unimodular.FanFaithfulness

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TauCeti.Toric Unimodular.AllowedBlocks
attribute [local instance] Classical.propDecidable

namespace Unimodular.SmoothClassification

section Definitions
variable {E N V : Type*} [Fintype E] [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (ι : N →+ V) (u : E → N)

/-- Genuine smooth complete fans with precisely the original ray system. -/
abbrev SmoothFans := {Φ : FanOnRays ι u // Φ.val.IsRegular}

/-- Exactly the independent full-rank columns retained in the paper. -/
abbrev IndependentColumn := {s : FullBlock ι u // Independent ι u s}

/-- The paper's actual facet/degree matrix after all dependent columns are deleted. -/
def restrictedEquation (w : V) :
    (IndependentColumn ι u → ℤ) →+ ((FacetBlock ι u → ℤ) × ℤ) :=
  ColumnRestriction.equation (Independent ι u) (equationMap ι u w)

def restrictedIndicator (Φ : SmoothFans ι u) : IndependentColumn ι u → ℤ :=
  ColumnRestriction.restrict (Independent ι u) (indicator ι u Φ.val)

end Definitions

section OriginalLattice
variable {n : ℕ} {N V : Type*} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ι : N →+ V} (hι : IsIntegralLattice ι) (b : Module.Basis (Fin n) ℤ N)
  (U : Finset N) (hU : IntegralRigidity.Uniform b (fun u : (U : Set N) => u.val))
  (hpos : PointedCone.hull ℝ (ι '' (U : Set N)) = ⊤) (hzero : (0 : N) ∉ U)

local notation "u₀" => (Subtype.val : {u // u ∈ U} → N)

include hι hzero in
lemma original_nonzero : ∀ e : {u // u ∈ U}, ι (u₀ e) ≠ 0 := by
  intro e he
  have hz : e.val = 0 := hι.injective (he.trans (map_zero ι).symm)
  exact hzero (hz ▸ e.property)

include hpos in
lemma original_positive : PointedCone.hull ℝ (Set.range (fun e => ι (u₀ e))) = ⊤ := by
  rw [Set.image_eq_range] at hpos
  exact hpos

include hι b hU hpos hzero

/-- Extending the restricted indicator by zero recovers every full-block
coordinate of the original actual smooth fan. -/
theorem indicator_extension (Φ : SmoothFans ι u₀) :
    ColumnRestriction.extend (Independent ι u₀) (restrictedIndicator ι u₀ Φ) =
      indicator ι u₀ Φ.val := by
  exact ColumnRestriction.extend_restrict (Independent ι u₀) _
    ((regular_iff_indicator_supported_original hι b U hU hpos hzero Φ.val).1 Φ.property)

theorem restrictedIndicator_injective : Function.Injective (restrictedIndicator ι u₀) := by
  intro Φ Ψ he
  apply Subtype.ext
  apply indicator_injective ι u₀ (original_nonzero hι U hzero)
  rw [← indicator_extension hι b U hU hpos hzero Φ,
    ← indicator_extension hι b U hU hpos hzero Ψ, he]

theorem indicator_mem_solutions {w : V}
    (hw : RayHyperplanes.GenericDirection (fun e => ι (u₀ e)) w)
    (Φ : SmoothFans ι u₀) :
    restrictedIndicator ι u₀ Φ ∈ EffectiveBinaryMoves.solutions (restrictedEquation ι u₀ w) (0, 1) := by
  apply (EffectiveBinaryMoves.mem_solutions _ _ _).2
  constructor
  · intro s
    change 0 ≤ indicator ι u₀ Φ.val s.val ∧ indicator ι u₀ Φ.val s.val ≤ 1
    unfold AllowedBlocks.indicator
    split_ifs <;> norm_num
  · change equationMap ι u₀ w
      (ColumnRestriction.extend (Independent ι u₀) (restrictedIndicator ι u₀ Φ)) = (0, 1)
    rw [indicator_extension hι b U hU hpos hzero Φ]
    exact ((isSolution_iff ι u₀ w _).1
      (indicator_isSolution ι u₀ hι (original_nonzero hι U hzero)
        (original_positive U hpos) hw Φ.val)).2

/-- The restricted finite binary fiber consists of exactly the actual smooth
complete fans, in the original lattice. Every solution is realized, and no
geometric completeness, smoothness, or fan structure is assumed of a solution. -/
theorem solutions_iff_smoothFan {w : V}
    (hw : RayHyperplanes.GenericDirection (fun e => ι (u₀ e)) w)
    (c : IndependentColumn ι u₀ → ℤ) :
    c ∈ EffectiveBinaryMoves.solutions (restrictedEquation ι u₀ w) (0, 1) ↔
      ∃ Φ : SmoothFans ι u₀, restrictedIndicator ι u₀ Φ = c := by
  constructor
  · intro hc
    let e := ColumnRestriction.extend (Independent ι u₀) c
    have he : e ∈ EffectiveBinaryMoves.solutions (equationMap ι u₀ w) (0, 1) :=
      (ColumnRestriction.extend_mem_solutions_iff (Independent ι u₀) _ _ c).2 hc
    have he' := (EffectiveBinaryMoves.mem_solutions _ _ _).1 he
    have hes : IsSolution ι u₀ w e := (isSolution_iff ι u₀ w e).2
      ⟨fun s => (he'.1 s).1, he'.2⟩
    let Ψ := realization ι u₀ hι (original_nonzero hι U hzero)
      (original_positive U hpos) hw e hes
    have hΨ : indicator ι u₀ Ψ = e := indicator_realization ι u₀ hι
      (original_nonzero hι U hzero) (original_positive U hpos) hw e hes
    have hreg : Ψ.val.IsRegular := by
      apply (regular_iff_indicator_supported_original hι b U hU hpos hzero Ψ).2
      intro s hs
      rw [hΨ]
      simp [e, hs]
    refine ⟨⟨Ψ, hreg⟩, ?_⟩
    change ColumnRestriction.restrict (Independent ι u₀) (indicator ι u₀ Ψ) = c
    rw [hΨ]
    exact ColumnRestriction.restrict_extend (Independent ι u₀) c
  · rintro ⟨Φ, rfl⟩
    exact indicator_mem_solutions hι b U hU hpos hzero hw Φ

/-- The exact bijection needed for the smooth classification, with literal
column deletion and a complete finite solution set. -/
theorem restricted_bijection {w : V}
    (hw : RayHyperplanes.GenericDirection (fun e => ι (u₀ e)) w) :
    Function.Bijective (fun Φ : SmoothFans ι u₀ =>
      (⟨restrictedIndicator ι u₀ Φ, indicator_mem_solutions hι b U hU hpos hzero hw Φ⟩ :
        {c // c ∈ EffectiveBinaryMoves.solutions (restrictedEquation ι u₀ w) (0, 1)})) := by
  constructor
  · intro Φ Ψ he
    apply restrictedIndicator_injective hι b U hU hpos hzero
    exact congrArg Subtype.val he
  · rintro ⟨c, hc⟩
    obtain ⟨Φ, hΦ⟩ := (solutions_iff_smoothFan hι b U hU hpos hzero hw c).1 hc
    exact ⟨Φ, Subtype.ext hΦ⟩

end OriginalLattice
end Unimodular.SmoothClassification

#print axioms Unimodular.SmoothClassification.indicator_extension
#print axioms Unimodular.SmoothClassification.restrictedIndicator_injective
#print axioms Unimodular.SmoothClassification.solutions_iff_smoothFan
#print axioms Unimodular.SmoothClassification.restricted_bijection
#check Unimodular.SmoothClassification.restricted_bijection
