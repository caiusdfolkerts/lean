module

public import ToricPower.SubfanRayRetraction

/-! # Transitivity of literal fullness on original rays -/

@[expose] public noncomputable section
open TauCeti.Toric
namespace ToricPower

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

theorem isFullOnRays_self (fan : Fan i) : IsFullOnRays fan fan :=
  fun _ member _ => member

theorem IsFullOnRays.trans {first middle last : Fan i}
    (firstIncluded : first.cones ⊆ middle.cones)
    (middleIncluded : middle.cones ⊆ last.cones)
    (firstFull : IsFullOnRays first middle) (middleFull : IsFullOnRays middle last) :
    IsFullOnRays first last := by
  intro σ member allOld
  have inMiddle : σ ∈ middle.cones :=
    middleFull σ member (fun ρ below => firstIncluded (allOld ρ below))
  apply firstFull σ inMiddle
  intro ρ below
  exact allOld (subfanRayEmbedding middle last middleIncluded ρ) below

end ToricPower
end

