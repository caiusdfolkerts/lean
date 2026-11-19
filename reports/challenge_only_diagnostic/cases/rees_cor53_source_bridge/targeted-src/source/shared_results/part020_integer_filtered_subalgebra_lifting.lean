module
public import graph_foundation.part014
public import shared_results.part020_integer_filtered_bounds

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.IntegerFilteredSubalgebraLifting -/
section

/-! # Lifting special classes with coefficients in a prescribed cycle algebra

This construction remembers where the lifted coefficients lie. It is needed
for the generation conclusion of the degeneration principle, beyond equality
of dimensions.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.IntegerFiltered.MultiplicativeFiltration

variable {K A : Type*} [CommRing K] [Ring A] [Algebra K A]
  (F : MultiplicativeFiltration K A) (D : ParityDifferential K A)
  (hd : ∀ n x, x ∈ F.level n → D.d x ∈ F.level n)
  (hp : ∀ n x, x ∈ F.level n → D.parity x ∈ F.level n)

def reesIn (T : Subalgebra K A) : Subalgebra K F.rees :=
  (gradedCoefficientAlgebra (fun _ : ℤ => T.toSubmodule) T.one_mem
    (fun _ _ _ hx _ hy => T.mul_mem hx hy)).comap F.rees.val

@[simp] theorem mem_reesIn (T : Subalgebra K A) (p : F.rees) :
    p ∈ F.reesIn T ↔ ∀ n, p.val.coeff n ∈ T := Iff.rfl

theorem reesIn_cycle (T : Subalgebra K A) (hT : T ≤ D.cycles) (p : F.reesIn T) :
    (F.reesDGA D hd hp).d p.val = 0 := by
  apply Subtype.ext
  ext n
  exact hT (p.property n)

def goodCyclesMap (T : Subalgebra K A) (hT : T ≤ D.cycles) :
    F.reesIn T →ₐ[K] (F.reesDGA D hd hp).cycles :=
  (F.reesIn T).val.codRestrict (F.reesDGA D hd hp).cycles
    (F.reesIn_cycle D hd hp T hT)

/-- Keep the homology quotient as the head of the generic construction.
This avoids repeatedly normalizing the nested Rees quotient dictionaries. -/
def cycleHomologyComposite
    {R X Y Z : Type*} [CommRing R] [Ring X] [Ring Y] [Ring Z]
    [Algebra R X] [Algebra R Y] [Algebra R Z]
    (D₀ : ParityDifferential R Y) (E₀ : ParityDifferential R Z)
    (f : X →ₐ[R] D₀.cycles) (h : D₀.Homology →ₐ[R] E₀.Homology) :
    X →ₐ[R] E₀.Homology := h.comp (D₀.classMap.comp f)

set_option backward.isDefEq.respectTransparency true in
def goodSpecialMap (T : Subalgebra K A) (hT : T ≤ D.cycles) :
    F.reesIn T →ₐ[K] (F.associatedDGA D hd hp).Homology :=
  cycleHomologyComposite (R:=K) (X:=F.reesIn T) (Y:=F.rees) (Z:=F.AssociatedGraded)
    (F.reesDGA D hd hp) (F.associatedDGA D hd hp)
    (F.goodCyclesMap D hd hp T hT) (F.homologySpecialization D hd hp)

theorem specialClasses_lift_to_reesIn (W : Submodule K A)
    (hlift : F.RelativeLiftsCycles D W)
    (T : Subalgebra K A) (hT : T ≤ D.cycles)
    (hselected : ∀ x ∈ W, D.d x = 0 → x ∈ T) :
    F.specialClasses D hd hp W ⊆ Set.range (F.goodSpecialMap D hd hp T hT) := by
  rintro u ⟨p, hcycle, hW, rfl⟩
  obtain ⟨q, hqd, hqmap, hqW⟩ :=
    F.exists_relative_rees_cycle_lift D hd hp W hlift p hcycle hW
  have hqT : q ∈ F.reesIn T := by
    intro n
    apply hselected _ (hqW n)
    exact congrArg (fun p : F.rees => p.val.coeff n) hqd
  refine ⟨⟨q, hqT⟩, ?_⟩
  change (F.associatedDGA D hd hp).classMap _ = (F.associatedDGA D hd hp).classMap _
  apply congrArg (F.associatedDGA D hd hp).classMap
  exact Subtype.ext hqmap

theorem goodSpecialMap_surjective_of_generators (W : Submodule K A)
    (hlift : F.RelativeLiftsCycles D W)
    (hgen : Algebra.adjoin K (F.specialClasses D hd hp W) = ⊤)
    (T : Subalgebra K A) (hT : T ≤ D.cycles)
    (hselected : ∀ x ∈ W, D.d x = 0 → x ∈ T) :
    Function.Surjective (F.goodSpecialMap D hd hp T hT) := by
  have hr : (⊤ : Subalgebra K (F.associatedDGA D hd hp).Homology) ≤
      (F.goodSpecialMap D hd hp T hT).range := by
    rw [← hgen]
    exact Algebra.adjoin_le (F.specialClasses_lift_to_reesIn D hd hp W hlift T hT hselected)
  intro u
  exact hr (show u ∈ (⊤ : Subalgebra K (F.associatedDGA D hd hp).Homology) from trivial)

/-- A surjective special homology map from coefficientwise `T`-valued Rees
cycles approximates every original cycle by a cycle in `T` of the same leading
weight. Boundary correction stays in `T` because every boundary lies in `T`. -/
theorem cycle_approximation_in_subalgebra
    (T : Subalgebra K A) (hT : T ≤ D.cycles)
    (hbound : ∀ a : A, D.d a ∈ T)
    (hsurj : Function.Surjective (F.goodSpecialMap D hd hp T hT))
    (n : ℤ) (x : A) (hx : x ∈ F.level n) (hdx : D.d x = 0) :
    ∃ z, z ∈ T ∧ z ∈ F.level n ∧ D.d z = 0 ∧ x - z ∈ F.level (n - 1) := by
  let r : F.rees := F.monomial n ⟨x, hx⟩
  have hr : (F.associatedDGA D hd hp).d (F.leadingMap r) = 0 := by
    rw [F.leadingMap_intertwines, F.leadingMap_eq_zero]
    intro i
    change D.d (r.val.coeff i) ∈ F.level (i - 1)
    dsimp only [r]
    rw [F.monomial_coeff]
    split_ifs
    · rw [hdx]
      exact (F.level (i - 1)).zero_mem
    · rw [map_zero]
      exact (F.level (i - 1)).zero_mem
  obtain ⟨q, hq⟩ := hsurj ((F.associatedDGA D hd hp).classMap ⟨F.leadingMap r, hr⟩)
  change (F.associatedDGA D hd hp).classMap _ =
    (F.associatedDGA D hd hp).classMap ⟨F.leadingMap r, hr⟩ at hq
  obtain ⟨v, hv⟩ := ((F.associatedDGA D hd hp).classMap_eq_iff _ _).mp hq
  obtain ⟨v, rfl⟩ := F.leadingMap_surjective v
  change (F.associatedDGA D hd hp).d (F.leadingMap v) =
    F.leadingMap q.val - F.leadingMap r at hv
  let q' : F.rees := q.val - (F.reesDGA D hd hp).d v
  have hq'd : (F.reesDGA D hd hp).d q' = 0 := by
    dsimp only [q']
    rw [map_sub, F.reesIn_cycle D hd hp T hT q,
      (F.reesDGA D hd hp).square_zero, sub_self]
  have hq'map : F.leadingMap q' = F.leadingMap r := by
    dsimp only [q']
    rw [map_sub, ← F.leadingMap_intertwines, hv]
    abel
  refine ⟨q'.val.coeff n, ?_, q'.property n, ?_, ?_⟩
  · change q.val.val.coeff n - D.d (v.val.coeff n) ∈ T
    exact T.sub_mem (q.property n) (hbound (v.val.coeff n))
  · exact congrArg (fun p : F.rees => p.val.coeff n) hq'd
  · have hz : F.leadingMap (r - q') = 0 := by rw [map_sub, hq'map, sub_self]
    have hh := (F.leadingMap_eq_zero (r - q')).mp hz n
    change r.val.coeff n - q'.val.coeff n ∈ F.level (n - 1) at hh
    simpa [r, F.monomial_coeff] using hh

end FourPapers.IntegerFiltered.MultiplicativeFiltration

end
end
end


end
