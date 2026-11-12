module

public import ToricPower.FiniteHomTotalDifferential

/-! # The actual finite dual total is the full Hom complex -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open CochainComplex HomComplex

namespace ToricPower

universe u v r
variable (R : Type r) [CommRing R]
  {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  (K I : CochainComplex C ℤ) (width : ℕ)

open NegativeFunctorTotal

theorem finiteHomTotal_d_self (a : ℤ) (p : Fin width) :
    biproduct.ι (fun p : Fin width => (row (finiteSourceHomCoefficients R K) I p).X a) p ≫
      (total (finiteSourceHomCoefficients R K) width I).d a (a+1) ≫
      biproduct.π (fun q : Fin width => (row (finiteSourceHomCoefficients R K) I q).X (a+1)) p =
    (row (finiteSourceHomCoefficients R K) I p).d a (a+1) := by
  change biproduct.ι (fun p : Fin width => (row (finiteSourceHomCoefficients R K) I p).X a) p ≫
      CochainComplex.of.d (FiniteTotal.term (row (finiteSourceHomCoefficients R K) I (width := width)))
      (FiniteTotal.differential (row (finiteSourceHomCoefficients R K) I)
        (off (finiteSourceHomCoefficients R K) I)) a (a+1) ≫
      biproduct.π (fun q : Fin width => (row (finiteSourceHomCoefficients R K) I q).X (a+1)) p = _
  rw [CochainComplex.of_d]
  simp only [FiniteTotal.differential,FiniteTotal.diagonal,off,comp_add,add_comp,
    Category.assoc,biproduct.map_π,biproduct.ι_map_assoc,
    biproduct.ι_matrix_assoc,biproduct.lift_π]
  rw [← Category.assoc,biproduct.ι_π_self]
  simp only [Category.id_comp,offEntry,dif_neg (show ¬ chainDegree p=chainDegree p+1 by omega),add_zero]

theorem finiteHomTotal_d_entry (a : ℤ) (p q : Fin width) :
    biproduct.ι (fun p : Fin width => (row (finiteSourceHomCoefficients R K) I p).X a) p ≫
      (total (finiteSourceHomCoefficients R K) width I).d a (a+1) ≫
      biproduct.π (fun q : Fin width => (row (finiteSourceHomCoefficients R K) I q).X (a+1)) q =
    ModuleCat.ofHom (finiteHomTotalInclusion R K I width a p) ≫
      (linearHomComplex R K I).d a (a+1) ≫
        ModuleCat.ofHom (finiteHomTotalProjection R K I width (a+1) q) := by
  by_cases same : p=q
  · subst q
    rw [finiteHomTotal_d_self]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    change (chainDegree p : ℤ).negOnePow •
      (f ≫ I.d (a+(chainDegree p : ℤ)) (a+1+(chainDegree p : ℤ))) =
        finiteHomTotalProjection R K I width (a+1) p
          (δ a (a+1) (finiteHomTotalInclusion R K I width a p f))
    exact (finiteHomTotalDifferential_self R K I width a p f).symm
  · rw [total_d_entry_ne (finiteSourceHomCoefficients R K) I a p q same]
    by_cases next : chainDegree p=chainDegree q+1
    · apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      change offEntry (finiteSourceHomCoefficients R K) I a p q f =
        finiteHomTotalProjection R K I width (a+1) q
          (δ a (a+1) (finiteHomTotalInclusion R K I width a p f))
      rw [finiteSourceHomCoefficients_offEntry R K I width a p q next]
      exact (finiteHomTotalDifferential_next R K I width a p q next f).symm
    · rw [offEntry,dif_neg next]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      change 0 = finiteHomTotalProjection R K I width (a+1) q
        (δ a (a+1) (finiteHomTotalInclusion R K I width a p f))
      exact (finiteHomTotalDifferential_other R K I width a p q same next f).symm

theorem finiteHomTotal_d_factor (a : ℤ) :
    (total (finiteSourceHomCoefficients R K) width I).d a (a+1) =
      finiteHomTotalDegreeMap R K I width a ≫ (linearHomComplex R K I).d a (a+1) ≫
        finiteHomTotalDegreeInverse R K I width (a+1) := by
  apply biproduct.hom_ext'
  intro p
  apply biproduct.hom_ext
  intro q
  simp only [finiteHomTotalDegreeMap,finiteHomTotalDegreeInverse,Category.assoc,
    biproduct.ι_desc_assoc,biproduct.lift_π]
  exact finiteHomTotal_d_entry R K I width a p q

variable (outside : ∀ p : ℤ, ¬ (0 ≤ p ∧ p < (width : ℤ)) → IsZero (K.X p))

def finiteHomTotalIso :
    total (finiteSourceHomCoefficients R K) width I ≅ linearHomComplex R K I :=
  HomologicalComplex.Hom.isoOfComponents (finiteHomTotalDegreeIso R K I width outside)
    (fun a b related => by
      obtain rfl : a+1=b := related
      change finiteHomTotalDegreeMap R K I width a ≫ (linearHomComplex R K I).d a (a+1) =
        (total (finiteSourceHomCoefficients R K) width I).d a (a+1) ≫
          finiteHomTotalDegreeMap R K I width (a+1)
      rw [finiteHomTotal_d_factor]
      have inverse : finiteHomTotalDegreeInverse R K I width (a+1) ≫
          finiteHomTotalDegreeMap R K I width (a+1) = 𝟙 _ :=
        (finiteHomTotalDegreeIso R K I width outside (a+1)).inv_hom_id
      rw [Category.assoc,Category.assoc,inverse]
      erw [Category.comp_id])

end ToricPower

end

