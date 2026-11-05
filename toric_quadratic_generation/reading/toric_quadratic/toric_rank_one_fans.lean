module

public import PaperVerification.ToricProjectiveLineDegree
public import Mathlib.Algebra.Group.Int.Units

@[expose] public section

/-!
# Every smooth complete rank-one fan is the two-ray fan

A basis of the rank-one integral lattice has generator `1` or `-1`.
Smoothness restricts each cone to one of these rays or the zero cone,
and completeness forces both rays. The result is an equality of the
actual fans and hence an isomorphism of their actual glued schemes.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry

open AlgebraicGeometry CategoryTheory
open scoped Classical BigOperators

theorem rankOneBasis_generator (b : Module.Basis (Fin 1) ℤ (Lattice 1)) :
    b 0=projectiveLineRay false ∨ b 0=projectiveLineRay true := by
  have hsum := b.sum_repr (projectiveLineRay false)
  have hmul : b 0 0 * b.repr (projectiveLineRay false) 0=1 := by
    have h := congrFun hsum (0 : Fin 1)
    simpa [Fin.sum_univ_one,projectiveLineRay,mul_comm] using h
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hmul with h|h
  · left
    ext i
    have hi : i=(0 : Fin 1) := Subsingleton.elim _ _
    simpa [projectiveLineRay,hi] using h
  · right
    ext i
    have hi : i=(0 : Fin 1) := Subsingleton.elim _ _
    simpa [projectiveLineRay,hi] using h

namespace SmoothCompleteFan

theorem eq_of_cones_eq {d : ℕ} {«Σ» Γ : SmoothCompleteFan d}
    (h : «Σ».cones=Γ.cones) : «Σ»=Γ := by
  cases «Σ»
  cases Γ
  cases h
  rfl

variable («Σ» : SmoothCompleteFan 1)

theorem rankOne_cone_cases {s : Finset (Lattice 1)} (hs : s∈«Σ».cones) :
    s=∅ ∨ s={projectiveLineRay false} ∨ s={projectiveLineRay true} := by
  obtain ⟨b,I,rfl⟩ := «Σ».smooth s hs
  have hI : I⊆{(0 : Fin 1)} := by
    intro i hi
    exact Finset.mem_singleton.mpr (Subsingleton.elim _ _)
  rcases Finset.subset_singleton_iff.mp hI with h|h
  · exact Or.inl (by rw [h,Finset.image_empty])
  · rw [h,Finset.image_singleton]
    rcases rankOneBasis_generator b with hb|hb
    · exact Or.inr (Or.inl (congrArg singleton hb))
    · exact Or.inr (Or.inr (congrArg singleton hb))

theorem rankOne_ray_mem (negative : Bool) :
    {projectiveLineRay negative}∈«Σ».cones := by
  obtain ⟨s,hs,hx⟩ := «Σ».complete (embed 1 (projectiveLineRay negative))
  rcases «Σ».rankOne_cone_cases hs with h|h|h
  · rw [h,latticeRayCone_empty] at hx
    have hz : embed 1 (projectiveLineRay negative)=0 := hx
    have h0 := congrFun hz (0 : Fin 1)
    cases negative <;> norm_num [embed,projectiveLineRay] at h0
  · rw [h,mem_projectiveLineCone] at hx
    cases negative
    · simpa only [h] using hs
    · norm_num [embed,projectiveLineRay] at hx
  · rw [h,mem_projectiveLineCone] at hx
    cases negative
    · norm_num [embed,projectiveLineRay] at hx
    · simpa only [h] using hs

/-- There is no extra classification hypothesis in dimension one. -/
theorem rankOne_eq_projectiveLine : «Σ»=projectiveLineFan := by
  apply eq_of_cones_eq
  ext s
  rw [mem_projectiveLineFan_cones]
  constructor
  · exact «Σ».rankOne_cone_cases
  · rintro (rfl|rfl|rfl)
    · exact «Σ».empty_mem
    · exact «Σ».rankOne_ray_mem false
    · exact «Σ».rankOne_ray_mem true

variable (k : Type u) [Field k]

def rankOneSchemeIso : «Σ».fanScheme k ≅ projectiveLineScheme k :=
  eqToIso (congrArg (fun Γ : SmoothCompleteFan 1 => Γ.fanScheme k)
    «Σ».rankOne_eq_projectiveLine)

end SmoothCompleteFan

/-- The rank condition is an equality of ordinary lattice dimensions,
not a replacement definition of a curve. -/
def oneDimensionalFanSchemeIso {d : ℕ} («Σ» : SmoothCompleteFan d)
    (hd : d=1) (k : Type u) [Field k] :
    «Σ».fanScheme k ≅ projectiveLineScheme k := by
  subst d
  exact «Σ».rankOneSchemeIso k

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.rankOne_eq_projectiveLine
