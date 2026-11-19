module

public import ToricPower.FanLiftedConeProfiles
public import ToricPower.SubfanRayRetraction

/-!
# Positive lifts across a literal subfan inclusion

Prescribed old ray lifts keep every old lifted cone unchanged. When the
subfan is full on its rays, each lifted cone decomposes as the lifted
old-ray face plus exactly its new ray lifts. These are equalities of
actual pointed cones, proved by identifying their generating sets.
-/

@[expose] public noncomputable section
open TauCeti.Toric Set
namespace ToricPower.FanSubdivision

variable {P V W : Type*} [AddCommGroup P]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  {j : P →+ W} (fan extension : Fan j) (included : fan.cones ⊆ extension.cones)
  (a : V) (oldLifts : fan.Ray → V) (lifts : extension.Ray → V)
  (agree : ∀ ρ, lifts (subfanRayEmbedding fan extension included ρ) = oldLifts ρ)

include agree in
theorem liftedCone_subfan_old (σ : fan.cones) :
    liftedCone extension a lifts (subfanConeEmbedding fan extension included σ) =
      liftedCone fan a oldLifts σ := by
  have generators : lifts '' {ρ : extension.Ray |
        ρ.toCone ≤ subfanConeEmbedding fan extension included σ} =
      oldLifts '' {ρ : fan.Ray | ρ.toCone ≤ σ} := by
    ext x
    constructor
    · rintro ⟨ρ,below,value⟩
      have old : ρ.toCone.val ∈ fan.cones := fan.mem_of_isFaceOf σ.property
        (extension.isFaceOf_of_le (included σ.property) ρ.toCone.property below)
      let source : fan.Ray := ⟨⟨ρ.toCone.val,old⟩,ρ.property⟩
      have same : subfanRayEmbedding fan extension included source = ρ := rfl
      refine ⟨source,below,?_⟩
      rw [← agree source,same]
      exact value
    · rintro ⟨ρ,below,value⟩
      refine ⟨subfanRayEmbedding fan extension included ρ,below,?_⟩
      rw [agree]
      exact value
  unfold liftedCone
  rw [generators]

/-- The actual vectors attached to rays absent from the original fan. -/
def newConeRayLifts (σ : extension.cones) : Set V :=
  lifts '' {ρ : extension.Ray | ρ.toCone ≤ σ ∧ ρ.toCone.val ∉ fan.cones}

include agree in
theorem liftedCone_subfan_split (regular : extension.IsRegular)
    (full : IsFullOnRays fan extension) (σ : extension.cones) :
    liftedCone extension a lifts σ =
      liftedCone fan a oldLifts (subfanOldRayFace fan extension regular full σ) ⊔
        PointedCone.hull ℝ (newConeRayLifts fan extension lifts σ) := by
  have generators : lifts '' {ρ : extension.Ray | ρ.toCone ≤ σ} =
      (oldLifts '' {ρ : fan.Ray |
        ρ.toCone ≤ subfanOldRayFace fan extension regular full σ}) ∪
      newConeRayLifts fan extension lifts σ := by
    ext x
    constructor
    · rintro ⟨ρ,below,value⟩
      by_cases old : ρ.toCone.val ∈ fan.cones
      · left
        let source : fan.Ray := ⟨⟨ρ.toCone.val,old⟩,ρ.property⟩
        have same : subfanRayEmbedding fan extension included source = ρ := rfl
        refine ⟨source,?_,?_⟩
        · exact (subfanOldRayFace_rays fan extension regular full σ ρ).mpr ⟨old,below⟩
        · rw [← agree source,same]
          exact value
      · exact Or.inr ⟨ρ,⟨below,old⟩,value⟩
    · rintro (⟨ρ,below,value⟩ | ⟨ρ,⟨below,_⟩,value⟩)
      · refine ⟨subfanRayEmbedding fan extension included ρ,?_,?_⟩
        · exact (subfanOldRayFace_oldRay fan extension included regular full σ ρ).mp below
        · rw [agree]
          exact value
      · exact ⟨ρ,below,value⟩
  unfold liftedCone
  rw [generators]
  simp only [PointedCone.hull,Submodule.span_union,sup_assoc]

end ToricPower.FanSubdivision
end
