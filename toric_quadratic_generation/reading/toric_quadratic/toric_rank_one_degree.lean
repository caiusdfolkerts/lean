module

public import PaperVerification.ToricRankOneFans
public import PaperVerification.ToricProjectiveLinePicardDegree

@[expose] public section

/-! # Actual line-bundle degrees on arbitrary rank-one complete fans -/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricSchemes
open scoped Classical

theorem projectiveLineFan_rays :
    projectiveLineFan.rays={projectiveLineRay false,projectiveLineRay true} := by
  ext u
  rw [projectiveLineFan.mem_rays_iff]
  constructor
  · rintro ⟨s,hs,hu⟩
    rcases (mem_projectiveLineFan_cones s).mp hs with h|h|h
    · rw [h] at hu
      exact (Finset.notMem_empty u hu).elim
    · simp only [h,Finset.mem_singleton] at hu
      simp [hu]
    · simp only [h,Finset.mem_singleton] at hu
      simp [hu]
  · intro hu
    rcases Finset.mem_insert.mp hu with h|h
    · subst u
      exact ⟨{projectiveLineRay false},projectiveLineRayCone_mem false,
        Finset.mem_singleton_self _⟩
    · have h' := Finset.mem_singleton.mp h
      subst u
      exact ⟨{projectiveLineRay true},projectiveLineRayCone_mem true,
        Finset.mem_singleton_self _⟩

namespace SmoothCompleteFan

variable {d : ℕ} (Γ : SmoothCompleteFan d) (hd : d=1)

include hd in
theorem oneDimensional_rays :
    Γ.rays={(fun _=>1 : Lattice d),(fun _=>-1 : Lattice d)} := by
  subst d
  rw [Γ.rankOne_eq_projectiveLine,projectiveLineFan_rays]
  rfl

variable (k : Type u) [Field k]

/-- Transport through the constructed actual scheme isomorphism to the
two-chart line, using the actual module-sheaf pullback functor. -/
def OneDimensionalHasDegree (M : (Γ.fanScheme k).Modules) (degree : ℤ) : Prop :=
  ProjectiveLineHasDegree k
    ((Scheme.Modules.pullback (oneDimensionalFanSchemeIso Γ hd k).inv).obj M) degree

theorem oneDimensionalHasDegree_unique {M : (Γ.fanScheme k).Modules}
    {r s : ℤ} (hr : Γ.OneDimensionalHasDegree hd k M r)
    (hs : Γ.OneDimensionalHasDegree hd k M s) : r=s :=
  projectiveLineHasDegree_unique k hr hs

theorem oneDimensionalHasDegree_iso {M N : (Γ.fanScheme k).Modules}
    (F : M ≅ N) (r : ℤ) :
    Γ.OneDimensionalHasDegree hd k M r ↔ Γ.OneDimensionalHasDegree hd k N r :=
  projectiveLineHasDegree_iso k
    ((Scheme.Modules.pullback (oneDimensionalFanSchemeIso Γ hd k).inv).mapIso F) r

/-- The degree of the actual fan Cartier sheaf is the sum over its actual
two primitive rays. This is derived from local orders and residue degrees. -/
theorem oneDimensionalFanCartier_hasDegree (hpure : Γ.IsPure) (a : Lattice d→ℤ) :
    Γ.OneDimensionalHasDegree hd k (Γ.fanCartierData k hpure a).sheaf
      (∑ v∈Γ.rays,a v) := by
  subst d
  have hΓ := Γ.rankOne_eq_projectiveLine
  subst Γ
  have hiso : oneDimensionalFanSchemeIso projectiveLineFan rfl k=
      Iso.refl (projectiveLineScheme k) := by
    rfl
  unfold OneDimensionalHasDegree
  rw [hiso]
  apply (projectiveLineHasDegree_iso k
    ((Scheme.Modules.pullbackId (projectiveLineScheme k)).app
      (projectiveLineCartierData k a).sheaf) _).mpr
  change ProjectiveLineHasDegree k (projectiveLineCartierData k a).sheaf
    (∑ v∈projectiveLineFan.rays,a v)
  have h := projectiveLineCartier_hasDegree k a
  simpa only [projectiveLineFan_rays,Finset.sum_pair projectiveLineRay_ne] using h

end SmoothCompleteFan

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.oneDimensionalFanCartier_hasDegree
