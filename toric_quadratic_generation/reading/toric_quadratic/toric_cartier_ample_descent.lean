module

public import PaperVerification.ToricArbitraryCartierFan

@[expose] public section

/-!
# Intrinsic ampleness is independent of Cartier presentation

The proof transports the actual positive-power sections and proves equality
of their genuine nonvanishing open subsets. Thus the intrinsic affine-open
criterion is preserved by the established equality of fractional sheaves.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace PaperVerification.ToricSchemes.RationalCartierCocycle

variable {X : Scheme.{u}} [IsIntegral X] (C D : RationalCartierCocycle X)

theorem mem_nonvanishingOpen_iff_rational (i : C.index) (s : Γ(C.sheaf,⊤))
    (x : X) (hxi : x∈C.openSet i) :
    x∈C.nonvanishingOpen s ↔
      C.toCartierData.sectionValue ⊤ s≠0 ∧
        (C.generator i : X.functionField)/C.toCartierData.sectionValue ⊤ s ∈
          regularAtSubring X x := by
  rw [C.mem_nonvanishingOpen_iff i s x hxi,
    ← X.mem_basicOpen (C.localCoefficient i s) x hxi,
    C.mem_localNonvanishing_iff i s x hxi]

/-- The actual section iso preserving fractional values preserves the
ordinary nonvanishing open, including at zeros of the section. -/
theorem nonvanishingOpen_sameGenerator
    (hCD : C.GeneratorRatioRegular D) (hDC : D.GeneratorRatioRegular C)
    (s : Γ(C.sheaf,⊤)) :
    D.nonvanishingOpen (C.sameGeneratorSheafLinearEquiv D hCD hDC ⊤ s) =
      C.nonvanishingOpen s := by
  ext x
  change x∈D.nonvanishingOpen (C.sameGeneratorSheafLinearEquiv D hCD hDC ⊤ s) ↔
    x∈C.nonvanishingOpen s
  obtain ⟨i,hxi⟩ := C.covers x
  obtain ⟨j,hxj⟩ := D.covers x
  rw [D.mem_nonvanishingOpen_iff_rational j _ x hxj,
    C.mem_nonvanishingOpen_iff_rational i s x hxi]
  have hv : D.toCartierData.sectionValue ⊤
      (C.sameGeneratorSheafLinearEquiv D hCD hDC ⊤ s) =
        C.toCartierData.sectionValue ⊤ s := rfl
  rw [hv]
  constructor
  · rintro ⟨hr,h⟩
    refine ⟨hr,?_⟩
    have hh := (regularAtSubring X x).mul_mem (hCD i j x hxi hxj) h
    have he : ((C.generator i : X.functionField)/(D.generator j : X.functionField)) *
        ((D.generator j : X.functionField)/C.toCartierData.sectionValue ⊤ s) =
        (C.generator i : X.functionField)/C.toCartierData.sectionValue ⊤ s := by
      field_simp [Units.ne_zero,hr]
    simpa only [he] using hh
  · rintro ⟨hr,h⟩
    refine ⟨hr,?_⟩
    have hh := (regularAtSubring X x).mul_mem (hDC j i x hxj hxi) h
    have he : ((D.generator j : X.functionField)/(C.generator i : X.functionField)) *
        ((C.generator i : X.functionField)/C.toCartierData.sectionValue ⊤ s) =
        (D.generator j : X.functionField)/C.toCartierData.sectionValue ⊤ s := by
      field_simp [Units.ne_zero,hr]
    simpa only [he] using hh

theorem isAmple_of_generatorRatios
    (hCD : C.GeneratorRatioRegular D) (hDC : D.GeneratorRatioRegular C)
    (hC : C.IsAmple) : D.IsAmple := by
  refine ⟨hC.1,?_⟩
  intro x
  obtain ⟨n,hn,s,hx,ha⟩ := hC.2 x
  let hpowCD := GeneratorRatioRegular.pow C D hCD n
  let hpowDC := GeneratorRatioRegular.pow D C hDC n
  let t := (C.pow n).sameGeneratorSheafLinearEquiv (D.pow n) hpowCD hpowDC ⊤ s
  have hopen : (D.pow n).nonvanishingOpen t=(C.pow n).nonvanishingOpen s :=
    (C.pow n).nonvanishingOpen_sameGenerator (D.pow n) hpowCD hpowDC s
  exact ⟨n,hn,t,by simpa only [hopen] using hx,by simpa only [hopen] using ha⟩

theorem isAmple_iff_of_generatorRatios
    (hCD : C.GeneratorRatioRegular D) (hDC : D.GeneratorRatioRegular C) :
    C.IsAmple ↔ D.IsAmple :=
  ⟨C.isAmple_of_generatorRatios D hCD hDC,D.isAmple_of_generatorRatios C hDC hCD⟩

end PaperVerification.ToricSchemes.RationalCartierCocycle

namespace PaperVerification.ToricSchemes.CartierData

variable {X : Scheme.{u}} [IsIntegral X] (D E : CartierData X)

theorem isAmple_iff_of_equivalent (h : D.Equivalent E) : D.IsAmple ↔ E.IsAmple :=
  D.localCocycle.isAmple_iff_of_generatorRatios E.localCocycle
    (D.localCocycle_generatorRatios E h)
    (E.localCocycle_generatorRatios D (D.equivalent_symm E h))

end PaperVerification.ToricSchemes.CartierData

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open PaperVerification.ToricSchemes

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

/-- The recovered integral invariant divisor preserves the original
intrinsic ampleness condition on the actual scheme. -/
theorem fanCartier_isAmple_iff (hpure : «Σ».IsPure)
    (D : CartierData («Σ».fanScheme k)) :
    («Σ».fanCartierData k hpure («Σ».cartierCoefficients k hpure D)).IsAmple ↔ D.IsAmple := by
  rw [← («Σ».normalizedCartier k D).isAmple_iff_of_equivalent _
    («Σ».normalizedCartier_equivalent_fanCartier k hpure D)]
  exact «Σ».normalizedCartier_isAmple_iff k D

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricSchemes.CartierData.isAmple_iff_of_equivalent
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.fanCartier_isAmple_iff
