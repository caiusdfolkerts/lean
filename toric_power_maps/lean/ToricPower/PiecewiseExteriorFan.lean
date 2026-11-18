module

public import ToricPower.IntegralPiecewiseFanRefinement

/-!
# Gluing an adjusted fan to the exterior hyperplane cones

This is the actual finite fan construction used for relative completion.
It takes compatible integral maps whose fixed points form faces, and whose
values are the identity where exterior sign cones meet the packing. Every
fan axiom and completeness is then proved. The geometric hypotheses are
discharged separately for the selected-ray projection of a packed fan.
-/

@[expose] public noncomputable section
open TauCeti.Toric Set
open scoped Classical

namespace ToricPower.FanSubdivision

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem signCone_mem_of_combination {κ : Type*} (forms : κ → V →ₗ[ℝ] ℝ)
    (first second : κ → Ordering) {x y : V} {r : ℝ}
    (hx : x ∈ hyperplaneSignCone forms first) (hy : y ∈ hyperplaneSignCone forms first)
    (positive : 0 < r) (combined : r • x + y ∈ hyperplaneSignCone forms second) :
    x ∈ hyperplaneSignCone forms second := by
  apply (mem_hyperplaneSignCone forms second x).mpr
  intro k
  have firstX := (mem_hyperplaneSignCone forms first x).mp hx k
  have firstY := (mem_hyperplaneSignCone forms first y).mp hy k
  have secondSum := (mem_hyperplaneSignCone forms second _).mp combined k
  rw [map_add,map_smul,smul_eq_mul] at secondSum
  cases hfirst : first k <;> cases hsecond : second k <;>
    simp only [hfirst,hsecond,signConstraint] at firstX firstY secondSum ⊢ <;> nlinarith

variable {N : Type*} [AddCommGroup N] {i : N →+ V}
  (fan : Fan i) (regular : fan.IsRegular)
  {κ : Type*} [Fintype κ] [DecidableEq κ]
  (characters : κ → N →+ ℤ)

def IsExteriorSign (sign : κ → Ordering) : Prop :=
  ¬ ∃ σ : fan.cones,
    hyperplaneSignCone (fun k => fan.lattice.realCharacter (characters k)) sign ≤ σ.val

variable (mapping : fan.cones → N →+ N)
  (compatible : ∀ (σ τ : fan.cones) (x : V), x ∈ σ.val ⊓ τ.val →
    fan.lattice.extend i (mapping σ) x = fan.lattice.extend i (mapping τ) x)
  (adapted : ∀ (sign : κ → Ordering) (σ : fan.cones),
    (hyperplaneSignCone (fun k => fan.lattice.realCharacter (characters k)) sign ⊓ σ.val).IsFaceOf
      (hyperplaneSignCone (fun k => fan.lattice.realCharacter (characters k)) sign))
  (fixedFace : ∀ σ : fan.cones,
    (σ.val ⊓ PointedCone.ofSubmodule (LinearMap.id-fan.lattice.extend i (mapping σ)).ker).IsFaceOf σ.val)
  (fixedExterior : ∀ (σ : fan.cones) (sign : κ → Ordering), IsExteriorSign fan characters sign →
    ∀ x, x ∈ σ.val ⊓ hyperplaneSignCone (fun k => fan.lattice.realCharacter (characters k)) sign →
      fan.lattice.extend i (mapping σ) x = x)

include fixedFace fixedExterior in
theorem piecewise_exterior_inf_isFaceOf (σ : fan.cones) (first second : κ → Ordering)
    (outside : IsExteriorSign fan characters second) :
    (piecewiseSignCone fan characters mapping σ first ⊓
      hyperplaneSignCone (fun k => fan.lattice.realCharacter (characters k)) second).IsFaceOf
      (piecewiseSignCone fan characters mapping σ first) := by
  refine ⟨inf_le_left,?_⟩
  intro x y r hx hy positive combined
  simp only [piecewiseSignCone,Submodule.mem_inf,PointedCone.mem_comap] at hx hy combined ⊢
  have sumFixed := fixedExterior σ second outside _ ⟨combined.1.1,combined.2⟩
  have sumFace : r • x + y ∈ σ.val ⊓ PointedCone.ofSubmodule
      (LinearMap.id-fan.lattice.extend i (mapping σ)).ker :=
    ⟨combined.1.1,sub_eq_zero.mpr sumFixed.symm⟩
  have xFace := (fixedFace σ).mem_of_smul_add_mem hx.1 hy.1 positive sumFace
  have xFixed : fan.lattice.extend i (mapping σ) x = x :=
    (sub_eq_zero.mp xFace.2).symm
  have sumSecond : fan.lattice.extend i (mapping σ) (r • x+y) ∈
      hyperplaneSignCone (fun k => fan.lattice.realCharacter (characters k)) second := by
    rw [sumFixed]
    exact combined.2
  rw [map_add,map_smul] at sumSecond
  have imageMember := signCone_mem_of_combination
    (fun k => fan.lattice.realCharacter (characters k)) first second hx.2 hy.2 positive sumSecond
  rw [xFixed] at imageMember
  exact ⟨hx,imageMember⟩

include adapted fixedExterior in
theorem exterior_piecewise_inf_isFaceOf (σ : fan.cones) (first second : κ → Ordering)
    (outside : IsExteriorSign fan characters first) :
    (hyperplaneSignCone (fun k => fan.lattice.realCharacter (characters k)) first ⊓
      piecewiseSignCone fan characters mapping σ second).IsFaceOf
      (hyperplaneSignCone (fun k => fan.lattice.realCharacter (characters k)) first) := by
  refine ⟨inf_le_left,?_⟩
  intro x y r hx hy positive combined
  simp only [piecewiseSignCone,Submodule.mem_inf,PointedCone.mem_comap] at combined ⊢
  have xSigma := ((adapted first σ).mem_of_smul_add_mem hx hy positive
    ⟨combined.1,combined.2.1⟩).2
  have sumFixed := fixedExterior σ first outside _ ⟨combined.2.1,combined.1⟩
  have sumSecond := combined.2.2
  rw [sumFixed] at sumSecond
  have xSecond := signCone_mem_of_combination
    (fun k => fan.lattice.realCharacter (characters k)) first second hx hy positive sumSecond
  refine ⟨hx,xSigma,?_⟩
  rw [fixedExterior σ first outside x ⟨xSigma,hx⟩]
  exact xSecond

abbrev ExteriorAssemblyIndex :=
  (fan.cones × (κ → Ordering)) ⊕ {sign : κ → Ordering // IsExteriorSign fan characters sign}

def exteriorAssemblyCone : ExteriorAssemblyIndex fan characters → PointedCone ℝ V :=
  Sum.elim (fun p => piecewiseSignCone fan characters mapping p.1 p.2)
    (fun p => hyperplaneSignCone (fun k => fan.lattice.realCharacter (characters k)) p.val)

variable (separates : ∀ x : V, (∀ k, fan.lattice.realCharacter (characters k) x = 0) → x = 0)

/-- The finite rational fan obtained by the actual interior/exterior gluing. -/
def exteriorCompletedFan : Fan i :=
  Fan.ofCones fan.lattice (Set.range (exteriorAssemblyCone fan characters mapping))
    (Set.finite_range _) (by
      rintro _ ⟨(⟨σ,sign⟩ | ⟨sign,outside⟩),rfl⟩
      · exact piecewiseSignCone_toric fan regular characters mapping σ sign
      · exact hyperplaneSignCone_toric fan.lattice characters separates sign)
    (by
      rintro _ _ ⟨(⟨σ,first⟩ | ⟨first,outsideFirst⟩),rfl⟩
        ⟨(⟨τ,second⟩ | ⟨second,outsideSecond⟩),rfl⟩
      · exact piecewiseSignCone_inf_isFaceOf fan characters mapping compatible σ τ first second
      · exact piecewise_exterior_inf_isFaceOf fan characters mapping fixedFace fixedExterior
          σ first second outsideSecond
      · exact exterior_piecewise_inf_isFaceOf fan characters mapping adapted fixedExterior
          τ first second outsideFirst
      · exact hyperplaneSignCone_inf_isFaceOf _ first second)

theorem exteriorAssemblyCone_mem (p : ExteriorAssemblyIndex fan characters) :
    exteriorAssemblyCone fan characters mapping p ∈
      (exteriorCompletedFan fan regular characters mapping compatible adapted fixedFace fixedExterior separates).cones :=
  Fan.subset_ofCones_cones _ _ _ _ _ ⟨p,rfl⟩

theorem exteriorCompletedFan_complete :
    (exteriorCompletedFan fan regular characters mapping compatible adapted fixedFace fixedExterior separates).IsComplete := by
  rw [Fan.isComplete_iff]
  intro x
  by_cases belongs : x ∈ fan.support
  · obtain ⟨σ,member,hx⟩ := (Fan.mem_support fan).mp belongs
    obtain ⟨sign,image⟩ := exists_hyperplaneSignCone
      (fun k => fan.lattice.realCharacter (characters k))
      (fan.lattice.extend i (mapping ⟨σ,member⟩) x)
    exact ⟨_,exteriorAssemblyCone_mem fan regular characters mapping compatible adapted fixedFace
      fixedExterior separates (.inl (⟨σ,member⟩,sign)),⟨hx,image⟩⟩
  · obtain ⟨sign,hx⟩ := exists_hyperplaneSignCone
      (fun k => fan.lattice.realCharacter (characters k)) x
    have outside : IsExteriorSign fan characters sign := by
      rintro ⟨σ,contained⟩
      exact belongs ((Fan.mem_support fan).mpr ⟨σ.val,σ.property,contained hx⟩)
    exact ⟨_,exteriorAssemblyCone_mem fan regular characters mapping compatible adapted fixedFace
      fixedExterior separates (.inr ⟨sign,outside⟩),hx⟩

theorem exteriorCompletedFan_retains_zero (σ : fan.cones)
    (zero : ∀ x ∈ σ.val, fan.lattice.extend i (mapping σ) x = 0) :
    σ.val ∈ (exteriorCompletedFan fan regular characters mapping compatible adapted fixedFace
      fixedExterior separates).cones := by
  have equality : exteriorAssemblyCone fan characters mapping (.inl (σ,fun _ => .eq)) = σ.val := by
    apply le_antisymm inf_le_left
    intro x member
    refine ⟨member,?_⟩
    apply PointedCone.mem_comap.mpr
    rw [zero x member]
    exact Submodule.zero_mem _
  rw [← equality]
  exact exteriorAssemblyCone_mem fan regular characters mapping compatible adapted fixedFace fixedExterior separates _

end ToricPower.FanSubdivision
end
