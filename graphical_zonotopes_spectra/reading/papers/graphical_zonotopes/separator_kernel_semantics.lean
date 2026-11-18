module

public import Papers.GraphicalZonotopes.Gluing

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace Gluing

variable {B J D : Type*} {K I X : J → Type*}

/-- The paper's private common kernel, as an actual linear subspace. It
retains every internal zero equation and every minimizer-difference equation. -/
def Data.privateKernelSpace (M : Data B J K D I X)
    (f : ∀ j, K j → ℝ) (m : J → B → ℝ) (j : J) :
    Submodule ℝ (K j → ℝ) where
  carrier := {g | M.PrivateKernel f m j g}
  zero_mem' := by
    constructor
    · intro i hi
      simp
    · intro b x y hx hy
      simp
  add_mem' := by
    intro g h hg hh
    constructor
    · intro i hi
      rw [map_add,hg.1 i hi,hh.1 i hi,add_zero]
    · intro b x y hx hy
      rw [map_add,map_add,hg.2 b x y hx hy,hh.2 b x y hx hy]
  smul_mem' := by
    intro a g hg
    constructor
    · intro i hi
      rw [map_smul,hg.1 i hi,smul_zero]
    · intro b x y hx hy
      rw [map_smul,map_smul,hg.2 b x y hx hy]

@[simp] theorem mem_privateKernelSpace (M : Data B J K D I X)
    (f : ∀ j, K j → ℝ) (m : J → B → ℝ) (j : J) (g : K j → ℝ) :
    g ∈ M.privateKernelSpace f m j ↔ M.PrivateKernel f m j g := Iff.rfl

theorem self_mem_privateKernelSpace (M : Data B J K D I X)
    (f : ∀ j, K j → ℝ) (m : J → B → ℝ) (j : J) :
    f j ∈ M.privateKernelSpace f m j :=
  ⟨fun _ h => h, fun _ _ _ hx hy => hx.trans hy.symm⟩

/-- The containment hypothesis used by the gluing proof is exactly the
paper's assertion that the private kernel is the span of the chosen vector.
The reverse containment follows from the actual equations at that vector. -/
theorem privateKernelSpace_eq_span_iff (M : Data B J K D I X)
    (f : ∀ j, K j → ℝ) (m : J → B → ℝ) (j : J) :
    M.privateKernelSpace f m j=Submodule.span ℝ {f j} ↔
      ∀ g, M.PrivateKernel f m j g → ∃ c : ℝ, g=c • f j := by
  constructor
  · intro he g hg
    have hmem : g ∈ M.privateKernelSpace f m j := hg
    rw [he,Submodule.mem_span_singleton] at hmem
    obtain ⟨c,hc⟩ := hmem
    exact ⟨c,hc.symm⟩
  · intro hline
    apply le_antisymm
    · intro g hg
      obtain ⟨c,hc⟩ := hline g hg
      exact Submodule.mem_span_singleton.mpr ⟨c,hc.symm⟩
    · apply Submodule.span_le.mpr
      intro g hg
      have he : g=f j := Set.mem_singleton_iff.mp hg
      subst g
      exact self_mem_privateKernelSpace M f m j

end Gluing
end GraphicalZonotopes
