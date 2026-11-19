module
public import graph_foundation.part013
public import shared_results.part018_parity_homology_retract

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.ParityHomologySelectedProjection -/
section

/-! # Homogeneous classes under a quasi-isomorphism

A projection onto a selected coefficient degree commutes with the
homology comparison. Surjectivity on total homology therefore restricts
to surjectivity on the selected classes. No choice of homotopy needs to
respect the coefficient grading.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace FourPapers.ParityDifferential
open Classical
variable {K A B : Type*} [CommRing K] [Ring A] [Ring B]
  [Algebra K A] [Algebra K B]
variable (D : ParityDifferential K A) (E : ParityDifferential K B)

def classesFrom (W : Submodule K A) : Set D.Homology :=
  {z | ∃ x : D.cycles, x.val∈W ∧ D.classMap x=z}

variable (f : A →ₐ[K] B) (hcomm : ∀ x, E.d (f x)=f (D.d x))

include hcomm in
theorem homologyMap_classesFrom_subset (W : Submodule K A) (Z : Submodule K B)
    (hf : ∀ x∈W, f x∈Z) :
    homologyMap D E f hcomm '' D.classesFrom W ⊆ E.classesFrom Z := by
  rintro z ⟨x,⟨a,ha,rfl⟩,rfl⟩
  exact ⟨cyclesMap D E f hcomm a,hf a.val ha,rfl⟩

/-- Project an arbitrary class lift to the required coefficient degree.
The projected boundary supplies the equality of its image with the given
homogeneous class. -/
theorem homologyMap_classesFrom_surjective
    (W : Submodule K A) (Z : Submodule K B)
    (P : A →ₗ[K] A) (Q : B →ₗ[K] B)
    (hPd : ∀ x, D.d (P x)=P (D.d x))
    (hQd : ∀ y, E.d (Q y)=Q (E.d y))
    (hPQ : ∀ x, f (P x)=Q (f x))
    (hP : ∀ x, P x∈W) (hQ : ∀ y∈Z, Q y=y)
    (hH : Function.Surjective (homologyMap D E f hcomm)) :
    E.classesFrom Z ⊆ homologyMap D E f hcomm '' D.classesFrom W := by
  rintro z ⟨y,hy,rfl⟩
  obtain ⟨a,ha⟩ := hH (E.classMap y)
  obtain ⟨x,rfl⟩ := D.classMap_surjective a
  rw [homologyMap_classMap] at ha
  obtain ⟨b,hb⟩ := (E.classMap_eq_iff _ _).mp ha
  change E.d b = f x.val - y.val at hb
  let xp : D.cycles := ⟨P x.val,by rw [D.mem_cycles,hPd,x.property,map_zero]⟩
  refine ⟨D.classMap xp,⟨xp,hP x.val,rfl⟩,?_⟩
  rw [homologyMap_classMap,E.classMap_eq_iff]
  refine ⟨Q b,?_⟩
  change E.d (Q b)=f (P x.val)-y.val
  rw [hQd,hb,map_sub,← hPQ,hQ y.val hy]

theorem homologyMap_classesFrom_eq
    (W : Submodule K A) (Z : Submodule K B)
    (P : A →ₗ[K] A) (Q : B →ₗ[K] B)
    (hPd : ∀ x, D.d (P x)=P (D.d x))
    (hQd : ∀ y, E.d (Q y)=Q (E.d y))
    (hPQ : ∀ x, f (P x)=Q (f x))
    (hP : ∀ x, P x∈W) (hQ : ∀ y∈Z, Q y=y)
    (hf : ∀ x∈W, f x∈Z)
    (hH : Function.Surjective (homologyMap D E f hcomm)) :
    homologyMap D E f hcomm '' D.classesFrom W=E.classesFrom Z :=
  Set.Subset.antisymm (homologyMap_classesFrom_subset D E f hcomm W Z hf)
    (homologyMap_classesFrom_surjective D E f hcomm W Z P Q hPd hQd hPQ hP hQ hH)

/-- The preceding restriction applies to the actual algebra equivalence
constructed from a deformation retract. -/
theorem homologyEquivOfRetract_classesFrom
    (C : HomologicalPerturbation.LinearDeformationRetract
      (R := K) (M := A) (H := B))
    (hD : C.sourceD=D.d) (hE : C.targetD=E.d) (hf : C.projection=f.toLinearMap)
    (W : Submodule K A) (Z : Submodule K B)
    (P : A →ₗ[K] A) (Q : B →ₗ[K] B)
    (hPd : ∀ x, D.d (P x)=P (D.d x))
    (hQd : ∀ y, E.d (Q y)=Q (E.d y))
    (hPQ : ∀ x, f (P x)=Q (f x))
    (hP : ∀ x, P x∈W) (hQ : ∀ y∈Z, Q y=y)
    (hfW : ∀ x∈W, f x∈Z) :
    homologyEquivOfRetract D E f C hD hE hf '' D.classesFrom W=E.classesFrom Z :=
  homologyMap_classesFrom_eq D E f (retract_projection_chain D E f C hD hE hf)
    W Z P Q hPd hQd hPQ hP hQ hfW
    (homologyMap_bijective_of_retract D E f C hD hE hf).surjective

/-- A literal differential-algebra equivalence carries the selected
classes to exactly the selected classes whenever it carries their
coefficient submodules to each other. -/
theorem homologyEquiv_classesFrom (e : A ≃ₐ[K] B)
    (hd : ∀ x, e (D.d x)=E.d (e x))
    (W : Submodule K A) (Z : Submodule K B)
    (hW : ∀ x, e x∈Z ↔ x∈W) :
    homologyEquiv D E e hd '' D.classesFrom W=E.classesFrom Z := by
  apply Set.Subset.antisymm
  · rintro z ⟨x,⟨a,ha,rfl⟩,rfl⟩
    exact ⟨cyclesEquiv D E e hd a,(hW a.val).mpr ha,rfl⟩
  · rintro z ⟨b,hb,rfl⟩
    let a := (cyclesEquiv D E e hd).symm b
    have ha : a.val∈W := (hW a.val).mp (by
      change e (e.symm b.val)∈Z
      rwa [e.apply_symm_apply])
    refine ⟨D.classMap a,⟨a,ha,rfl⟩,?_⟩
    rw [homologyEquiv_classMap]
    exact congrArg E.classMap ((cyclesEquiv D E e hd).apply_symm_apply b)

end FourPapers.ParityDifferential

namespace FourPapers
variable {K A B : Type*} [CommRing K] [Ring A] [Ring B]
  [Algebra K A] [Algebra K B]

/-- Algebraic generation transports along the literal comparison map. -/
theorem adjoin_eq_top_of_algEquiv (e : A ≃ₐ[K] B) (G : Set A) (H : Set B)
    (he : e '' G ⊆ H) (hG : Algebra.adjoin K G=⊤) : Algebra.adjoin K H=⊤ := by
  let T := Algebra.adjoin K H
  have h : Algebra.adjoin K G ≤ T.comap e.toAlgHom := by
    apply Algebra.adjoin_le
    intro x hx
    exact Algebra.subset_adjoin (he ⟨x,hx,rfl⟩)
  rw [hG] at h
  apply top_unique
  intro y _
  obtain ⟨x,rfl⟩ := e.surjective y
  exact h (show x∈(⊤ : Subalgebra K A) from trivial)

theorem adjoin_eq_top_iff_of_algEquiv (e : A ≃ₐ[K] B) (G : Set A) (H : Set B)
    (he : e '' G=H) : Algebra.adjoin K G=⊤ ↔ Algebra.adjoin K H=⊤ := by
  constructor
  · exact adjoin_eq_top_of_algEquiv e G H he.le
  · intro hH
    apply adjoin_eq_top_of_algEquiv e.symm H G ?_ hH
    rintro x ⟨y,hy,rfl⟩
    rw [← he] at hy
    obtain ⟨z,hz,rfl⟩ := hy
    simpa only [e.symm_apply_apply] using hz

end FourPapers

end
end
end


end
