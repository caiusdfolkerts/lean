module

public import PaperVerification.FermionFiniteTensorBigrading

/-!
# Coarsening an independent bigrading to the actual total grading

The proof uses directness of the pre-existing
total grading and exhaustiveness of the separate-degree decomposition.
Thus equality with the total pieces is proved, rather than built into a
transported grading definition.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace PaperVerification.Fermion

universe u v w z
variable {R : Type u} {M : Type v} {I : Type w} {Γ Δ : Type z}
  [CommRing R] [AddCommGroup M] [Module R M]
  [DecidableEq Γ] [DecidableEq Δ]

theorem basisDegreePart_comp (b : Module.Basis I R M) (degree : I → Γ)
    (f : Γ → Δ) (k : Δ) :
    basisDegreePart b (fun i ↦ f (degree i)) k=
      ⨆ g : {g // f g=k},basisDegreePart b degree g.val := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨i,hi,rfl⟩
    apply (le_iSup (fun g : {g // f g=k} ↦ basisDegreePart b degree g.val)
      ⟨degree i,hi⟩)
    exact Submodule.subset_span ⟨i,rfl,rfl⟩
  · refine iSup_le fun g ↦ Submodule.span_le.mpr ?_
    rintro x ⟨i,hi,rfl⟩
    apply Submodule.subset_span
    exact ⟨i,(congrArg f hi).trans g.property,rfl⟩

namespace NGradedAlgebra.Bigrading

variable {F : Type u} [Field F] {A : NGradedAlgebra F}

/-- Coarsening is formed from the independently specified theta/xi pieces. -/
def totalPart (q : NGradedAlgebra.Bigrading A) (k : ℕ) :
    Submodule F A.Carrier :=
  ⨆ g : {g : ℕ×ℕ // totalBidegree g=k},q.part g.val

theorem totalPart_iSup_eq_top (q : NGradedAlgebra.Bigrading A) :
    (⨆ k,q.totalPart k)=⊤ := by
  apply top_unique
  rw [←(DirectSum.Decomposition.isInternal q.part).submodule_iSup_eq_top]
  refine iSup_le fun g ↦ ?_
  exact (le_iSup_of_le (totalBidegree g)
    (le_iSup (fun h : {h : ℕ×ℕ // totalBidegree h=totalBidegree g} ↦ q.part h.val)
      ⟨g,rfl⟩))

/-- The given bigrading recovers the actual total homogeneous submodules. -/
theorem totalPart_eq (q : NGradedAlgebra.Bigrading A) :
    q.totalPart=A.part := by
  apply (iSupIndep.le_iff_eq_of_iSup_eq_top
    (DirectSum.Decomposition.isInternal A.part).submodule_iSupIndep
    q.totalPart_iSup_eq_top).mp
  intro k
  refine iSup_le fun g ↦ ?_
  simpa only [g.property] using q.total g.val

end NGradedAlgebra.Bigrading
end PaperVerification.Fermion
