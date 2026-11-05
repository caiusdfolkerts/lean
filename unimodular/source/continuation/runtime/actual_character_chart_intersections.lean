module

public import Continuation.Runtime.RealValuativeSchemeCharts

/-!
# Separatedness identifies the cones of actual chart overlaps

Suppose a literal character localization has the actual overlap as its
open image. Its nonnegative real weights are exactly the weights that
are nonnegative on both original charts. The proof constructs genuine
Hahn-valuative maps. Separatedness identifies their extensions from the
generic point, and the actual open-immersion factorization puts their
common center in the overlap.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricCharacters

namespace PaperVerification.ToricSchemes

variable (k : Type u) [Field k] {M : Type} [AddCommGroup M]
    (w : M →+ ℝ) {S T U : AddSubmonoid M} (hSU : S ≤ U)
    {X : Scheme.{u}} [X.IsSeparated]
    (a : monoidChartScheme k S ⟶ X) (b : monoidChartScheme k T ⟶ X)
    [IsOpenImmersion a] [IsOpenImmersion b]
    [IsOpenImmersion (monoidChartSpecMap k hSU)]
    (hT : characterChartTorusMap k S ≫ a = characterChartTorusMap k T ≫ b)
    (hrange : (monoidChartSpecMap k hSU).opensRange = a ⁻¹ᵁ b.opensRange)

include k hSU a b hT hrange

/-- A genuine character-chart overlap detects precisely the intersection
of the two complete families of real character inequalities. -/
theorem nonnegative_on_actual_chart_intersection_iff :
    (∀ m ∈ U, 0 ≤ w m) ↔
      (∀ m ∈ S, 0 ≤ w m) ∧ (∀ m ∈ T, 0 ≤ w m) := by
  let c := monoidChartSpecMap k hSU
  let g := realValuationGeneric k
  let p := realWeightTorusPoint k w
  constructor
  · intro hU
    refine ⟨fun m hm => hU m (hSU hm), ?_⟩
    let lU := realCharacterChartLift k w U hU
    let lX := lU ≫ c ≫ a
    have hsub : Set.range lX ⊆ Set.range b := by
      rintro _ ⟨z, rfl⟩
      have hz : c (lU z) ∈ c.opensRange := ⟨lU z, rfl⟩
      rw [hrange] at hz
      exact hz
    let lT := IsOpenImmersion.lift b lX hsub
    have hfac : lT ≫ b = lX := IsOpenImmersion.lift_fac b lX hsub
    have hgeneric : g ≫ lX = p ≫ characterChartTorusMap k T ≫ b := by
      calc
        g ≫ lX = (g ≫ lU) ≫ c ≫ a := by simp only [lX, Category.assoc]
        _ = (p ≫ characterChartTorusMap k U) ≫ c ≫ a := by
          rw [realCharacterChartLift_generic]
        _ = p ≫ characterChartTorusMap k S ≫ a := by
          simp only [Category.assoc, c, characterChartTorusMap_comp_face_assoc]
        _ = p ≫ characterChartTorusMap k T ≫ b := by rw [hT]
    apply nonnegative_of_realCharacterChartLift k w T lT
    apply (cancel_mono b).mp
    simpa only [Category.assoc, hfac] using hgeneric
  · rintro ⟨hS, hTnonneg⟩
    let lS := realCharacterChartLift k w S hS
    let lT := realCharacterChartLift k w T hTnonneg
    have hcommon : lS ≫ a = lT ≫ b := by
      apply ext_of_isDominant g
      calc
        g ≫ lS ≫ a = p ≫ characterChartTorusMap k S ≫ a := by
          rw [← Category.assoc, realCharacterChartLift_generic, Category.assoc]
        _ = p ≫ characterChartTorusMap k T ≫ b := by rw [hT]
        _ = g ≫ lT ≫ b := by
          symm
          rw [← Category.assoc, realCharacterChartLift_generic, Category.assoc]
    have hsub : Set.range lS ⊆ Set.range c := by
      rintro _ ⟨z, rfl⟩
      change lS z ∈ c.opensRange
      rw [hrange]
      refine ⟨lT z, ?_⟩
      exact congrArg (fun f => f z) hcommon.symm
    let lU := IsOpenImmersion.lift c lS hsub
    have hfac : lU ≫ c = lS := IsOpenImmersion.lift_fac c lS hsub
    apply nonnegative_of_realCharacterChartLift k w U lU
    apply (cancel_mono c).mp
    calc
      (g ≫ lU) ≫ c = g ≫ lS := by rw [Category.assoc, hfac]
      _ = p ≫ characterChartTorusMap k S := realCharacterChartLift_generic k w S hS
      _ = (p ≫ characterChartTorusMap k U) ≫ c := by
        rw [Category.assoc, characterChartTorusMap_comp_face]

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.nonnegative_on_actual_chart_intersection_iff
