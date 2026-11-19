module

public import Recovery.Unimodular.WeakFano.SmoothDictionary

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TauCeti.Toric Unimodular.AllowedBlocks
attribute [local instance] Classical.propDecidable

namespace Unimodular.SmoothClassification

variable {n : ℕ} {N V : Type*} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ι : N →+ V} (hι : IsIntegralLattice ι) (b : Module.Basis (Fin n) ℤ N)
  (U : Finset N) (hU : IntegralRigidity.Uniform b (fun u : (U : Set N) => u.val))
  (hpos : PointedCone.hull ℝ (ι '' (U : Set N)) = ⊤) (hzero : (0 : N) ∉ U)

local notation "u₀" => (Subtype.val : {u // u ∈ U} → N)
include hι b hU hpos hzero

/-- Every pair of actual smooth complete fans is connected after literal
column deletion by the computed finite primitive moves. Every maximal cone
throughout the path belongs to an endpoint, and every move is also primitive
for the full original matrix. -/
theorem restricted_connectivity {w : V}
    (hw : RayHyperplanes.GenericDirection (fun e => ι (u₀ e)) w)
    (Φ Ψ : SmoothFans ι u₀) :
    Relation.ReflTransGen
      (fun A B : SmoothFans ι u₀ =>
        restrictedIndicator ι u₀ B - restrictedIndicator ι u₀ A ∈
          EffectiveBinaryMoves.moves (restrictedEquation ι u₀ w) ∧
        Graver.Primitive (equationMap ι u₀ w).ker
          (indicator ι u₀ B.val - indicator ι u₀ A.val) ∧
        UsesEndpointCones ι u₀ Φ.val Ψ.val A.val ∧
        UsesEndpointCones ι u₀ Φ.val Ψ.val B.val) Φ Ψ := by
  let c := restrictedIndicator ι u₀ Φ
  let d := restrictedIndicator ι u₀ Ψ
  have hc := indicator_mem_solutions hι b U hU hpos hzero hw Φ
  have hd := indicator_mem_solutions hι b U hU hpos hzero hw Ψ
  have hpath := ColumnRestriction.restricted_connectivity (Independent ι u₀)
    (equationMap ι u₀ w) (0, 1) c d hc hd
  let realize : (IndependentColumn ι u₀ → ℤ) → SmoothFans ι u₀ := fun a =>
    if ha : a ∈ EffectiveBinaryMoves.solutions (restrictedEquation ι u₀ w) (0, 1) then
      ((solutions_iff_smoothFan hι b U hU hpos hzero hw a).1 ha).choose else Φ
  have hrealize : ∀ a, a ∈ EffectiveBinaryMoves.solutions (restrictedEquation ι u₀ w) (0, 1) →
      restrictedIndicator ι u₀ (realize a) = a := by
    intro a ha
    simp only [realize, dif_pos ha]
    exact ((solutions_iff_smoothFan hι b U hU hpos hzero hw a).1 ha).choose_spec
  have hfull : ∀ a, a ∈ EffectiveBinaryMoves.solutions (restrictedEquation ι u₀ w) (0, 1) →
      indicator ι u₀ (realize a).val = ColumnRestriction.extend (Independent ι u₀) a := by
    intro a ha
    rw [← indicator_extension hι b U hU hpos hzero (realize a), hrealize a ha]
  have hstart : realize c = Φ :=
    restrictedIndicator_injective hι b U hU hpos hzero (hrealize c hc)
  have hend : realize d = Ψ :=
    restrictedIndicator_injective hι b U hU hpos hzero (hrealize d hd)
  have hlift : Relation.ReflTransGen
      (fun A B : SmoothFans ι u₀ =>
        restrictedIndicator ι u₀ B - restrictedIndicator ι u₀ A ∈
          EffectiveBinaryMoves.moves (restrictedEquation ι u₀ w) ∧
        Graver.Primitive (equationMap ι u₀ w).ker
          (indicator ι u₀ B.val - indicator ι u₀ A.val) ∧
        UsesEndpointCones ι u₀ Φ.val Ψ.val A.val ∧
        UsesEndpointCones ι u₀ Φ.val Ψ.val B.val) (realize c) (realize d) := by
    apply Relation.ReflTransGen.lift realize (fun a a' haa' => ?_) _ _ hpath
    obtain ⟨hm, hp, ha, ha', hbox, hbox'⟩ := haa'
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [restrictedEquation, hrealize a ha, hrealize a' ha'] using hm
    · rw [hfull a ha, hfull a' ha', ← map_sub]
      exact hp
    · apply usesEndpointCones_of_between ι u₀ (original_nonzero hι U hzero)
      rw [← indicator_extension hι b U hU hpos hzero Φ,
        ← indicator_extension hι b U hU hpos hzero Ψ, hfull a ha]
      exact ColumnRestriction.extend_between (Independent ι u₀) hbox
    · apply usesEndpointCones_of_between ι u₀ (original_nonzero hι U hzero)
      rw [← indicator_extension hι b U hU hpos hzero Φ,
        ← indicator_extension hι b U hU hpos hzero Ψ, hfull a' ha']
      exact ColumnRestriction.extend_between (Independent ι u₀) hbox'
  simpa only [hstart, hend] using hlift

/-- The smooth projective starting fan, exact restricted solution dictionary,
and complete primitive reachability are all supplied in the conclusion.
This closes the geometric and matrix-level classification clauses of
Corollary 4.3. Computing the geometric facet matrix itself from raw U remains
a distinct effectivity obligation and is not claimed by this theorem. -/
theorem smooth_seed_classification :
    ∃ (w : V) (seed : SmoothFans ι u₀),
      RayHyperplanes.GenericDirection (fun e => ι (u₀ e)) w ∧
      LiteralA3Projectivity.HasIntegralNormalFan seed.val.val ∧
      (∀ c : IndependentColumn ι u₀ → ℤ,
        c ∈ EffectiveBinaryMoves.solutions (restrictedEquation ι u₀ w) (0, 1) ↔
          ∃! Φ : SmoothFans ι u₀, restrictedIndicator ι u₀ Φ = c) ∧
      ∀ Ψ : SmoothFans ι u₀,
        Relation.ReflTransGen
          (fun A B : SmoothFans ι u₀ =>
            restrictedIndicator ι u₀ B - restrictedIndicator ι u₀ A ∈
              EffectiveBinaryMoves.moves (restrictedEquation ι u₀ w) ∧
            Graver.Primitive (equationMap ι u₀ w).ker
              (indicator ι u₀ B.val - indicator ι u₀ A.val) ∧
            UsesEndpointCones ι u₀ seed.val Ψ.val A.val ∧
            UsesEndpointCones ι u₀ seed.val Ψ.val B.val) seed Ψ := by
  obtain ⟨Φ, hΦc, hΦr, hΦu, hΦp⟩ :=
    WeightedPolytopes.smooth_projective_realization_original hι b U hU hpos hzero
  let seed : SmoothFans ι u₀ := ⟨⟨Φ, hΦc, hΦu⟩, hΦr⟩
  obtain ⟨w, hw⟩ := (RayHyperplanes.genericDirection_dense (fun e => ι (u₀ e))).nonempty
  refine ⟨w, seed, hw, hΦp, ?_, ?_⟩
  · intro c
    constructor
    · intro hc
      obtain ⟨Ψ, hΨ⟩ := (solutions_iff_smoothFan hι b U hU hpos hzero hw c).1 hc
      refine ⟨Ψ, hΨ, ?_⟩
      intro Ω hΩ
      exact restrictedIndicator_injective hι b U hU hpos hzero (hΩ.trans hΨ.symm)
    · rintro ⟨Ψ, hΨ, _⟩
      exact (solutions_iff_smoothFan hι b U hU hpos hzero hw c).2 ⟨Ψ, hΨ⟩
  · intro Ψ
    exact restricted_connectivity hι b U hU hpos hzero hw seed Ψ

end Unimodular.SmoothClassification

#print axioms Unimodular.SmoothClassification.restricted_connectivity
#print axioms Unimodular.SmoothClassification.smooth_seed_classification
#check Unimodular.SmoothClassification.smooth_seed_classification
