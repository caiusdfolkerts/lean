module
public import graph_foundation.part014
public import shared_results.part020_filtered_tensor_differential

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.IntegerFilteredDimension -/
section

/-! # Finite homogeneous components of an integer-filtered differential algebra

A finite filtration interval is shifted to the nonnegative indexing used by the
linear-algebra comparison. This is a change of indices only: the differential,
cycles, boundaries, and filtration quotients remain the actual ones.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section

namespace FourPapers.IntegerFiltered.MultiplicativeFiltration

open Classical
open scoped BigOperators

variable {K A : Type*} [Field K] [Ring A] [Algebra K A]
  (F : MultiplicativeFiltration K A) (D : ParityDifferential K A)
  (hd : ∀ n x, x ∈ F.level n → D.d x ∈ F.level n)
  (W : Submodule K A) [FiniteDimensional K W]
  (hW : ∀ x ∈ W, D.d x ∈ W)

def componentDifferential : W →ₗ[K] W :=
  (D.d.domRestrict W).codRestrict W (fun x => hW x.val x.property)

theorem componentDifferential_square :
    (componentDifferential D W hW).comp (componentDifferential D W hW) = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact D.square_zero x.val

def componentFiltration (L : ℤ)
    (hL : (F.level (L - 1)).comap W.subtype = ⊥) :
    FilteredHomology.Filtration (K := K) W where
  level n := (F.level (L + (n : ℤ) - 1)).comap W.subtype
  zero := by simpa using hL
  mono := by
    intro m n hmn
    exact Submodule.comap_mono (F.mono (by omega))
  exhaustive x := by
    obtain ⟨i, hi⟩ := F.exhaustive x.val
    obtain ⟨n, hn⟩ := exists_nat_ge (i - L + 1)
    refine ⟨n, ?_⟩
    exact F.mono (by omega) hi

include hd in
theorem componentDifferential_preserves (L : ℤ)
    (hL : (F.level (L - 1)).comap W.subtype = ⊥) :
    FilteredHomology.Preserves (F.componentFiltration W L hL)
      (F.componentFiltration W L hL) (componentDifferential D W hW) := by
  intro n x hx
  exact hd (L + (n : ℤ) - 1) x.val hx

/-- Equality of homology dimensions in a finite homogeneous component forces
all its leading cycles, with their original integer weights, to lift. -/
theorem relativeLiftsCycles_of_homology_dimension_eq (L : ℤ)
    (hL : (F.level (L - 1)).comap W.subtype = ⊥)
    (N : ℕ) (hN : (F.componentFiltration W L hL).level N = ⊤)
    (hdim :
      Module.finrank K (FilteredHomology.Homology
        (componentDifferential D W hW) (componentDifferential D W hW)
        (componentDifferential_square D W hW)) =
      ∑ n ∈ Finset.range N,
        Module.finrank K (FilteredHomology.GradedHomology
          (F.componentFiltration W L hL) (F.componentFiltration W L hL)
          (F.componentFiltration W L hL)
          (componentDifferential D W hW) (componentDifferential D W hW)
          (F.componentDifferential_preserves D hd W hW L hL)
          (F.componentDifferential_preserves D hd W hW L hL)
          (componentDifferential_square D W hW) n)) :
    F.RelativeLiftsCycles D W := by
  have hlift := FilteredHomology.liftsCycles_of_homology_dimension_eq
    (F.componentFiltration W L hL) (componentDifferential D W hW)
    (F.componentDifferential_preserves D hd W hW L hL)
    (componentDifferential_square D W hW) N hN hdim
  intro n x hxW hxF hdx
  by_cases hn : L ≤ n
  · let j : ℕ := (n - L).toNat
    have hj : L + (j : ℤ) = n := by omega
    let xW : W := ⟨x, hxW⟩
    have hx : xW ∈ (F.componentFiltration W L hL).level (j + 1) := by
      change x ∈ F.level (L + ((j + 1 : ℕ) : ℤ) - 1)
      have he : L + ((j + 1 : ℕ) : ℤ) - 1 = n := by omega
      simpa only [he] using hxF
    have hdx' : componentDifferential D W hW xW ∈
        (F.componentFiltration W L hL).level j := by
      change D.d x ∈ F.level (L + (j : ℤ) - 1)
      simpa only [hj] using hdx
    obtain ⟨z, hz, hzd, hxz⟩ := hlift j xW hx hdx'
    refine ⟨z.val, z.property, ?_, ?_, ?_⟩
    · change z.val ∈ F.level (L + ((j + 1 : ℕ) : ℤ) - 1) at hz
      have he : L + ((j + 1 : ℕ) : ℤ) - 1 = n := by omega
      simpa only [he] using hz
    · exact congrArg Subtype.val hzd
    · change x - z.val ∈ F.level (L + (j : ℤ) - 1) at hxz
      simpa only [hj] using hxz
  · have hx0 : x = 0 := by
      have hxlow : (⟨x, hxW⟩ : W) ∈ (F.level (L - 1)).comap W.subtype :=
        F.mono (by omega) hxF
      rw [hL, Submodule.mem_bot] at hxlow
      exact congrArg Subtype.val hxlow
    refine ⟨0, W.zero_mem, (F.level n).zero_mem, map_zero D.d, ?_⟩
    rw [hx0, sub_self]
    exact (F.level (n - 1)).zero_mem

include hd in
theorem component_liftsCycles_of_relative (L : ℤ)
    (hL : (F.level (L - 1)).comap W.subtype = ⊥)
    (hlift : F.RelativeLiftsCycles D W) :
    FilteredHomology.LiftsCycles (F.componentFiltration W L hL)
      (F.componentFiltration W L hL) (componentDifferential D W hW) := by
  intro n x hx hdx
  have hx' : x.val ∈ F.level (L + (n : ℤ)) := by
    change x.val ∈ F.level (L + ((n + 1 : ℕ) : ℤ) - 1) at hx
    have he : L + ((n + 1 : ℕ) : ℤ) - 1 = L + (n : ℤ) := by omega
    simpa only [he] using hx
  have hdx' : D.d x.val ∈ F.level (L + (n : ℤ) - 1) := hdx
  obtain ⟨z, hzW, hzF, hzd, hxz⟩ := hlift (L + (n : ℤ)) x.val x.property hx' hdx'
  refine ⟨⟨z, hzW⟩, ?_, Subtype.ext hzd, ?_⟩
  · change z ∈ F.level (L + ((n + 1 : ℕ) : ℤ) - 1)
    have he : L + ((n + 1 : ℕ) : ℤ) - 1 = L + (n : ℤ) := by omega
    simpa only [he] using hzF
  · exact hxz

/-- Cycle lifting recovers equality of the actual homology dimensions. -/
theorem component_homology_dimension_eq_of_relative (L : ℤ)
    (hL : (F.level (L - 1)).comap W.subtype = ⊥)
    (N : ℕ) (hN : (F.componentFiltration W L hL).level N = ⊤)
    (hlift : F.RelativeLiftsCycles D W) :
    Module.finrank K (FilteredHomology.Homology
      (componentDifferential D W hW) (componentDifferential D W hW)
      (componentDifferential_square D W hW)) =
      ∑ n ∈ Finset.range N,
        Module.finrank K (FilteredHomology.GradedHomology
          (F.componentFiltration W L hL) (F.componentFiltration W L hL)
          (F.componentFiltration W L hL)
          (componentDifferential D W hW) (componentDifferential D W hW)
          (F.componentDifferential_preserves D hd W hW L hL)
          (F.componentDifferential_preserves D hd W hW L hL)
          (componentDifferential_square D W hW) n) :=
  FilteredHomology.homology_dimension_eq_of_liftsCycles
    (F.componentFiltration W L hL) (componentDifferential D W hW)
    (F.componentDifferential_preserves D hd W hW L hL)
    (componentDifferential_square D W hW) N hN
    (F.component_liftsCycles_of_relative D hd W hW L hL hlift)

end FourPapers.IntegerFiltered.MultiplicativeFiltration

end
end
end


end
