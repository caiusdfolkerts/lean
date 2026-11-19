/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import TauCeti.Algebra.Homology.HomologicalComplex.Basic
/-! Compatibility import plus the original historical exactness lemma, whose
name is absent from the pinned canonical API. Every other declaration is owned
by the canonical module. Original complete sources remain unchanged in source/. -/
public section
open CategoryTheory Limits
universe w v u
namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [CategoryWithHomology C] {ι : Type*}
  {c : ComplexShape ι} {K : HomologicalComplex C c}

variable (K) in
/-- The sequence `Zᵢ ⟶ Kᵢ ⟶ Zⱼ` of the cycles of a complex `K` is exact when `j` is the degree
following `i`: the cycles in degree `i` are the kernel of the differential. -/
lemma exact_iCycles_toCycles (i j : ι) (hij : c.next i = j) :
    (ShortComplex.mk _ _ (K.iCycles_toCycles i j)).Exact := by
  refine (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
    (S₁ := ShortComplex.mk _ _ (K.iCycles_toCycles i j))
    (S₂ := ShortComplex.mk _ _ (K.iCycles_d i j))
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := K.iCycles j
      comm₁₂ := by simp
      comm₂₃ := (Category.id_comp _).trans (toCycles_i _ _ _).symm }).2 ?_
  exact ShortComplex.exact_of_f_is_kernel _ (K.cyclesIsKernel i j hij)

end HomologicalComplex
