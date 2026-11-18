module

public import ToricPower.FanAdaptedHyperplanes

/-!
# Refining a fan by an integral piecewise linear map

The maps on different cones need only agree on their actual intersections.
Taking inverse images of the sign regions of an integral hyperplane
arrangement gives a genuine finite rational fan with exactly the same
support. A cone on which the map vanishes is retained literally.
-/

@[expose] public noncomputable section
open TauCeti.Toric Set

namespace ToricPower.FanSubdivision

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

theorem realCharacter_comp_extension (lattice : IsIntegralLattice i)
    (mapping : N →+ N) (character : N →+ ℤ) :
    (lattice.realCharacter character).comp (lattice.extend i mapping) =
      lattice.realCharacter (character.comp mapping) := by
  apply lattice.eq_realCharacter
  intro n
  simp only [LinearMap.comp_apply,lattice.extend_apply,lattice.realCharacter_apply,
    AddMonoidHom.comp_apply]

theorem exists_hyperplaneSignCone {κ : Type*} (forms : κ → V →ₗ[ℝ] ℝ) (x : V) :
    ∃ sign : κ → Ordering, x ∈ hyperplaneSignCone forms sign := by
  classical
  let sign : κ → Ordering := fun k =>
    if forms k x < 0 then .lt else if forms k x = 0 then .eq else .gt
  refine ⟨sign,(mem_hyperplaneSignCone forms sign x).mpr ?_⟩
  intro k
  dsimp [sign]
  split_ifs <;> simp only [signConstraint] <;> linarith

variable (fan : Fan i) (regular : fan.IsRegular)
  {κ : Type*} [Fintype κ] [DecidableEq κ]
  (characters : κ → N →+ ℤ) (mapping : fan.cones → N →+ N)

def piecewiseSignCone (σ : fan.cones) (sign : κ → Ordering) : PointedCone ℝ V :=
  σ.val ⊓ PointedCone.comap (fan.lattice.extend i (mapping σ))
    (hyperplaneSignCone (fun k => fan.lattice.realCharacter (characters k)) sign)

include regular in
theorem piecewiseSignCone_rational (σ : fan.cones) (sign : κ → Ordering) :
    IsLatticeRational i (piecewiseSignCone fan characters mapping σ sign) := by
  let forms : (Fin (Module.finrank ℤ N) × Bool) ⊕ (κ × Bool) → N →+ ℤ :=
    Sum.elim (regularFanConeCharacters fan regular σ)
      (fun p => (signInequalityCharacters characters sign p).comp (mapping σ))
  apply integral_inequalityCone_isLatticeRational fan.lattice _ forms
  intro x
  change (x ∈ σ.val ∧ fan.lattice.extend i (mapping σ) x ∈
    hyperplaneSignCone (fun k => fan.lattice.realCharacter (characters k)) sign) ↔ _
  rw [regularFanConeCharacters_membership fan regular σ,
    hyperplaneSignCone_integral_inequalities]
  simp only [forms,Sum.forall,Sum.elim_inl,Sum.elim_inr,
    ← realCharacter_comp_extension,LinearMap.comp_apply]

include regular in
theorem piecewiseSignCone_toric (σ : fan.cones) (sign : κ → Ordering) :
    IsToricCone i (piecewiseSignCone fan characters mapping σ sign) := by
  refine ⟨piecewiseSignCone_rational fan regular characters mapping σ sign,?_⟩
  intro x member nonzero negativeMember
  exact (fan.isToricCone σ.property).salient x member.1 nonzero negativeMember.1

variable (compatible : ∀ (σ τ : fan.cones) (x : V), x ∈ σ.val ⊓ τ.val →
  fan.lattice.extend i (mapping σ) x = fan.lattice.extend i (mapping τ) x)

include compatible in
theorem piecewiseSignCone_inf_isFaceOf (σ τ : fan.cones) (first second : κ → Ordering) :
    (piecewiseSignCone fan characters mapping σ first ⊓
      piecewiseSignCone fan characters mapping τ second).IsFaceOf
      (piecewiseSignCone fan characters mapping σ first) := by
  refine ⟨inf_le_left,?_⟩
  intro x y r hx hy positive combined
  simp only [piecewiseSignCone,Submodule.mem_inf,PointedCone.mem_comap] at hx hy combined ⊢
  have sumSigma : r • x + y ∈ σ.val := σ.val.add_mem (σ.val.smul_mem positive.le hx.1) hy.1
  have xTau : x ∈ τ.val :=
    ((fan.inf_isFaceOf_left σ.property τ.property).mem_of_smul_add_mem
      hx.1 hy.1 positive ⟨sumSigma,combined.2.1⟩).2
  have sumSecond : fan.lattice.extend i (mapping σ) (r • x + y) ∈
      hyperplaneSignCone (fun k => fan.lattice.realCharacter (characters k)) second := by
    rw [compatible σ τ _ ⟨sumSigma,combined.2.1⟩]
    exact combined.2.2
  have imageSecond : fan.lattice.extend i (mapping σ) x ∈
      hyperplaneSignCone (fun k => fan.lattice.realCharacter (characters k)) second := by
    apply (mem_hyperplaneSignCone _ second _).mpr
    intro k
    have firstX := (mem_hyperplaneSignCone _ first _).mp hx.2 k
    have firstY := (mem_hyperplaneSignCone _ first _).mp hy.2 k
    have secondSum := (mem_hyperplaneSignCone _ second _).mp sumSecond k
    rw [map_add,map_smul,map_add,map_smul,smul_eq_mul] at secondSum
    cases hfirst : first k <;> cases hsecond : second k <;>
      simp only [hfirst,hsecond,signConstraint] at firstX firstY secondSum ⊢ <;> nlinarith
  refine ⟨hx,xTau,?_⟩
  rw [← compatible σ τ x ⟨hx.1,xTau⟩]
  exact imageSecond

/-- The actual rational refinement produced by the compatible integral maps. -/
def piecewiseRefinedFan : Fan i :=
  Fan.ofCones fan.lattice
    (Set.range (fun p : fan.cones × (κ → Ordering) =>
      piecewiseSignCone fan characters mapping p.1 p.2))
    (Set.finite_range _) (by
      rintro _ ⟨⟨σ,sign⟩,rfl⟩
      exact piecewiseSignCone_toric fan regular characters mapping σ sign)
    (by
      rintro _ _ ⟨⟨σ,first⟩,rfl⟩ ⟨⟨τ,second⟩,rfl⟩
      exact piecewiseSignCone_inf_isFaceOf fan characters mapping compatible σ τ first second)

theorem piecewiseSignCone_mem_refined (σ : fan.cones) (sign : κ → Ordering) :
    piecewiseSignCone fan characters mapping σ sign ∈
      (piecewiseRefinedFan fan regular characters mapping compatible).cones :=
  Fan.subset_ofCones_cones _ _ _ _ _ ⟨⟨σ,sign⟩,rfl⟩

theorem piecewiseRefinedFan_support :
    (piecewiseRefinedFan fan regular characters mapping compatible).support = fan.support := by
  ext x
  constructor
  · intro member
    obtain ⟨F,cone,belongs⟩ := (Fan.mem_support _).mp member
    unfold piecewiseRefinedFan at cone
    rw [Fan.mem_ofCones_cones] at cone
    obtain ⟨_,⟨⟨σ,sign⟩,rfl⟩,face⟩ := cone
    exact (Fan.mem_support fan).mpr ⟨σ.val,σ.property,(face.le belongs).1⟩
  · intro member
    obtain ⟨σ,cone,belongs⟩ := (Fan.mem_support fan).mp member
    obtain ⟨sign,image⟩ := exists_hyperplaneSignCone
      (fun k => fan.lattice.realCharacter (characters k))
      (fan.lattice.extend i (mapping ⟨σ,cone⟩) x)
    exact (Fan.mem_support _).mpr ⟨_,
      piecewiseSignCone_mem_refined fan regular characters mapping compatible ⟨σ,cone⟩ sign,
      ⟨belongs,image⟩⟩

theorem piecewiseRefinedFan_retains_zero (σ : fan.cones)
    (zero : ∀ x ∈ σ.val, fan.lattice.extend i (mapping σ) x = 0) :
    σ.val ∈ (piecewiseRefinedFan fan regular characters mapping compatible).cones := by
  have equality : piecewiseSignCone fan characters mapping σ (fun _ => .eq) = σ.val := by
    apply le_antisymm inf_le_left
    intro x member
    refine ⟨member,?_⟩
    apply PointedCone.mem_comap.mpr
    rw [zero x member]
    exact Submodule.zero_mem _
  rw [← equality]
  exact piecewiseSignCone_mem_refined fan regular characters mapping compatible σ _

end ToricPower.FanSubdivision
end
