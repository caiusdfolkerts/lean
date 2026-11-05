module
public import paper_results.torsion_foundations
public import paper_results.part009

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.ProjectivePlaneRealization -/
section

/-!
# The explicit 1087-element example, in genuine fine Tor

The universe-lifted endpoint maps define the same literal sublattice of
Fin 30 → Fin 3 as the manuscript's printed incidence list. The integral
normal form is composed with the all-power incidence realization.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace FourPapers.Sublattice.RP2
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid

universe u

-- Use the equality decision carried by the ordered face complex throughout.
-- The generic incidence comparison takes this same ordered vertex type.
local instance : DecidableEq (Vertex.{u}) := LinearOrder.toDecidableEq

def left30 (e : Fin 30) : LeftVertex.{u} := left (ULift.up e : Incidence.{u})

def right30 (e : Fin 30) : Vertex.{u} := right (ULift.up e : Incidence.{u})

theorem left30_surjective : Function.Surjective (left30.{u}) := by
  intro a
  obtain ⟨e,he⟩ := projectivePlaneIncidenceLeft_surjective a.down
  exact ⟨e,congrArg ULift.up he⟩

theorem right30_surjective : Function.Surjective (right30.{u}) := by
  intro a
  obtain ⟨e,he⟩ := projectivePlaneIncidenceRight_surjective a.down
  exact ⟨e,congrArg ULift.up he⟩

theorem nerve30_eq_face : incidenceNerveFaces (left30.{u}) (right30.{u}) = Face.{u} := by
  funext Q
  apply propext
  simpa only [incidenceNerveFaces,left30,right30,left,right,ULift.exists] using nerve_iff_face.{u} Q

set_option backward.isDefEq.respectTransparency false in
theorem lowerStage_lift : incidenceLowerStage (left30.{u})=
    incidenceLowerStage projectivePlaneIncidenceLeft := by
  ext x
  constructor
  · intro hx
    obtain ⟨D,_,hD⟩ := Finset.mem_image.mp hx
    refine Finset.mem_image.mpr ⟨D.map Equiv.ulift.toEmbedding,Finset.mem_univ _,?_⟩
    rw [←hD]
    funext e
    simp [incidenceLower,left30,left]
  · intro hx
    obtain ⟨D,_,hD⟩ := Finset.mem_image.mp hx
    refine Finset.mem_image.mpr ⟨D.map Equiv.ulift.symm.toEmbedding,Finset.mem_univ _,?_⟩
    rw [←hD]
    funext e
    simp [incidenceLower,left30,left]

set_option backward.isDefEq.respectTransparency false in
theorem upperStage_lift : incidenceUpperStage (right30.{u})=
    incidenceUpperStage projectivePlaneIncidenceRight := by
  ext x
  constructor
  · intro hx
    obtain ⟨D,_,hD⟩ := Finset.mem_image.mp hx
    refine Finset.mem_image.mpr ⟨D.map Equiv.ulift.toEmbedding,Finset.mem_univ _,?_⟩
    rw [←hD]
    funext e
    simp [incidenceUpper,right30,right]
  · intro hx
    obtain ⟨D,_,hD⟩ := Finset.mem_image.mp hx
    refine Finset.mem_image.mpr ⟨D.map Equiv.ulift.symm.toEmbedding,Finset.mem_univ _,?_⟩
    rw [←hD]
    funext e
    simp [incidenceUpper,right30,right]

theorem lattice_lift : incidenceSublattice (left30.{u}) (right30.{u}) = projectivePlaneSublattice := by
  rw [incidenceSublattice,lowerStage_lift,upperStage_lift]
  rfl

variable {k : Type u} [CommRing k] [Nontrivial k]

attribute [local irreducible] projectivePlaneSublattice incidenceSublattice

/-- Equality transport preserves the actual scalar action on the Tor submodule. -/
def gradedTorReindex {W : Type u} [Fintype W] [LinearOrder W]
    (B C : Family W) (a b : Exponent W) (p q : ℕ)
    (hB : B = C) (ha : a = b) (hp : p = q) :
    gradedTor (k := k) B a p ≃ₗ[k] gradedTor (k := k) C b q := by
  cases hB
  cases ha
  cases hp
  exact LinearEquiv.refl k _

/-- The exact paper lattice, independent of any coefficient-field choice. -/
def realization (m : ℕ) (hm : 0< m) (q : ℕ) :
    gradedTor (k:=k)
      (exponentPowerFamily (finiteRowFamily (IncidenceRows 30) projectivePlaneSublattice) m)
      (incidenceRealizationDegree (M:=30) m) (q+11) ≃ₗ[k]
      AugmentedFaceHomology (k:=k) Face downward q := by
  let e := gradedTorReindex (k := k)
    (exponentPowerFamily (finiteRowFamily (IncidenceRows 30) projectivePlaneSublattice) m)
    (exponentPowerFamily (finiteRowFamily (IncidenceRows 30)
      (incidenceSublattice (left30.{u}) (right30.{u}))) m)
    (incidenceRealizationDegree (M := 30) m) (incidenceRealizationDegree (M := 30) m)
    (q + 11) (q + Fintype.card (LeftVertex.{u}) + 1)
    (by rw [lattice_lift]) rfl
    (by simpa only [Fintype.card_ulift, Fintype.card_fin] using
      (show q + 11 = q + 10 + 1 by omega))
  let f := incidencePowerRealizationEquiv (k := k) (left30.{u}) (right30.{u}) (by decide)
    left30_surjective right30_surjective m hm q
  let g := augmentedFaceHomologyEquivOfFaces (V := Vertex.{u}) (k := k)
    (incidenceNerveFaces (left30.{u}) (right30.{u})) (Face.{u})
    (incidenceRowNerve_downward left30 right30) downward.{u} nerve30_eq_face.{u} q
  exact e.trans (f.trans g)

theorem realization_zero_below (m : ℕ) (hm : 0< m) (p : ℕ) (hp : p<11) :
    Subsingleton (gradedTor (k:=k)
      (exponentPowerFamily (finiteRowFamily (IncidenceRows 30) projectivePlaneSublattice) m)
      (incidenceRealizationDegree (M:=30) m) p) := by
  letI : Subsingleton (gradedTor (k := k)
      (exponentPowerFamily (finiteRowFamily (IncidenceRows 30)
        (incidenceSublattice (left30.{u}) (right30.{u}))) m)
      (incidenceRealizationDegree (M := 30) m) p) :=
    incidencePowerRealization_zero_below (k := k) (left30.{u}) (right30.{u}) (by decide)
    left30_surjective.{u} right30_surjective.{u} m hm p
    (by simpa only [Fintype.card_ulift, Fintype.card_fin] using hp)
  let e := gradedTorReindex (k := k)
    (exponentPowerFamily (finiteRowFamily (IncidenceRows 30) projectivePlaneSublattice) m)
    (exponentPowerFamily (finiteRowFamily (IncidenceRows 30)
      (incidenceSublattice (left30.{u}) (right30.{u}))) m)
    (incidenceRealizationDegree (M := 30) m) (incidenceRealizationDegree (M := 30) m)
    p p (by rw [lattice_lift]) rfl rfl
  exact e.injective.subsingleton

/-- The exact integral fine group is Z/2 in homological degree 13,
in every positive power. -/
def integral_degree13 (m : ℕ) (hm : 0< m) :
    gradedTor (k:=ℤ)
      (exponentPowerFamily (finiteRowFamily (IncidenceRows 30) projectivePlaneSublattice) m)
      (incidenceRealizationDegree (M:=30) m) 13 ≃ₗ[ℤ] ZMod 2 := by
  let e := (realization (k := ℤ) m hm 2).trans integralH1Equiv
  -- Retain the source submodule's scalar action when forgetting linearity;
  -- the additive equivalence then respects the unique integer-module action.
  let a := @LinearEquiv.toAddEquiv _ _ _ _ _ _ _ _ _ _ _ _
    (gradedTor (k := ℤ)
      (exponentPowerFamily (finiteRowFamily (IncidenceRows 30) projectivePlaneSublattice) m)
      (incidenceRealizationDegree (M := 30) m) 13).module _ e
  exact a.toIntLinearEquiv

theorem integral_other_degrees (m : ℕ) (hm : 0< m) (p : ℕ) (hp : p≠13) :
    Subsingleton (gradedTor (k:=ℤ)
      (exponentPowerFamily (finiteRowFamily (IncidenceRows 30) projectivePlaneSublattice) m)
      (incidenceRealizationDegree (M:=30) m) p) := by
  by_cases hlo : p<11
  · exact realization_zero_below m hm p hlo
  · let q := p-11
    have hpq : p=q+11 := by dsimp [q]; omega
    have hq : q≠2 := by intro h; apply hp; omega
    letI := integral_other_homology_zero q hq
    rw [hpq]
    exact ⟨fun x y=>(realization m hm q).injective (Subsingleton.elim _ _)⟩

section Field
variable {K : Type u} [Field K]

/-- The complete fine Betti function of the isolated torsion degree,
not just the two nonzero cases. -/
theorem fine_betti (m : ℕ) (hm : 0< m) (p : ℕ) :
    bettiNumber (k:=K)
      (exponentPowerFamily (finiteRowFamily (IncidenceRows 30) projectivePlaneSublattice) m)
      (incidenceRealizationDegree (M:=30) m) p=
      if (2:K)=0 ∧ (p=13 ∨ p=14) then 1 else 0 := by
  unfold bettiNumber
  by_cases hlo : p<11
  · letI := realization_zero_below (k:=K) m hm p hlo
    simp only [Module.finrank_zero_of_subsingleton]
    split_ifs with h
    · omega
    · rfl
  · let q := p-11
    have hpq : p=q+11 := by dsimp [q]; omega
    rw [hpq, (realization (k := K) m hm q).finrank_eq, field_homology_finrank]
    have he : (q = 2 ∨ q = 3) ↔ (q + 11 = 13 ∨ q + 11 = 14) := by omega
    by_cases h2 : (2 : K) = 0
    · simp only [h2, true_and, ← he]
    · simp only [h2, false_and, if_false]

end Field
end FourPapers.Sublattice.RP2

end
end
end


end
