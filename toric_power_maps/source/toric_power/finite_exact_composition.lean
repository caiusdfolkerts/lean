module

public import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-! # Exactness through a right-associated composite -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]

/-- A compact opaque interface avoids expanding geometric functors
when reassociating the already proved exactness of a composite. -/
theorem finiteExact_rightComposite (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D)
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (h : PreservesFiniteLimits (G ⋙ H) ∧ PreservesFiniteColimits (G ⋙ H)) :
    PreservesFiniteLimits ((F ⋙ G) ⋙ H) ∧ PreservesFiniteColimits ((F ⋙ G) ⋙ H) := by
  letI := h.1
  letI := h.2
  exact ⟨inferInstanceAs (PreservesFiniteLimits (F ⋙ (G ⋙ H))),
    inferInstanceAs (PreservesFiniteColimits (F ⋙ (G ⋙ H)))⟩

end ToricPower

end
