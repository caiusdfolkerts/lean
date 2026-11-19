module
public import incidence_bundle.PalomarPart002
import all incidence_bundle.PalomarPart002
public import foundation_bundle
public import Lean.Elab.Tactic.Omega
@[expose] public section

noncomputable section

/-!
# Consolidated verification sources

Generated only to avoid repeatedly loading the same pinned Mathlib files.
Public theorem statements and proofs preserve their original content.
See IncidenceBundle.sources.json for exact source ranges, hashes, and private
helper alpha-renamings, topological source order, and scope adjustments.
-/

/- Original source: CubicalIndecomposability/FaceDataChecks/Anchors.lean -/
section VerificationSource001



/-!
# Every face inside a listed facet has a cube code

An arbitrary catalogue face is nonempty. Choose one of its vertices, and
test containment only in the facets incident to that vertex. The exact
vertex/facet transpose and the anchor membership are proved below. Thus
the sparse search still covers every face and every facet.

The final numerical certificate traverses only the 3510 actual incidences.
Its explicit `Finset.decidableDforallFinset` instance recurses over the
members of the small finite set, and an explicit cube-code witness avoids
searching over the 27 possible codes. All numerical checks use Lean's
ordinary kernel reduction; the proposed data have no trusted status.

Regenerate with `python3 scripts/sparse_cube_complete.py`.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace CubicalIndecomposability

theorem bundle_64ff450e75_cofacet0758 : bundle_64ff450e75_cubeCofacetCertificate (⟨758, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0759 : bundle_64ff450e75_cubeCofacetCertificate (⟨759, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0760 : bundle_64ff450e75_cubeCofacetCertificate (⟨760, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0761 : bundle_64ff450e75_cubeCofacetCertificate (⟨761, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0762 : bundle_64ff450e75_cubeCofacetCertificate (⟨762, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0763 : bundle_64ff450e75_cubeCofacetCertificate (⟨763, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0764 : bundle_64ff450e75_cubeCofacetCertificate (⟨764, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0765 : bundle_64ff450e75_cubeCofacetCertificate (⟨765, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0766 : bundle_64ff450e75_cubeCofacetCertificate (⟨766, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0767 : bundle_64ff450e75_cubeCofacetCertificate (⟨767, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0768 : bundle_64ff450e75_cubeCofacetCertificate (⟨768, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0769 : bundle_64ff450e75_cubeCofacetCertificate (⟨769, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0770 : bundle_64ff450e75_cubeCofacetCertificate (⟨770, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0771 : bundle_64ff450e75_cubeCofacetCertificate (⟨771, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0772 : bundle_64ff450e75_cubeCofacetCertificate (⟨772, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0773 : bundle_64ff450e75_cubeCofacetCertificate (⟨773, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0774 : bundle_64ff450e75_cubeCofacetCertificate (⟨774, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0775 : bundle_64ff450e75_cubeCofacetCertificate (⟨775, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0776 : bundle_64ff450e75_cubeCofacetCertificate (⟨776, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0777 : bundle_64ff450e75_cubeCofacetCertificate (⟨777, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0778 : bundle_64ff450e75_cubeCofacetCertificate (⟨778, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0779 : bundle_64ff450e75_cubeCofacetCertificate (⟨779, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0780 : bundle_64ff450e75_cubeCofacetCertificate (⟨780, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0781 : bundle_64ff450e75_cubeCofacetCertificate (⟨781, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0782 : bundle_64ff450e75_cubeCofacetCertificate (⟨782, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0783 : bundle_64ff450e75_cubeCofacetCertificate (⟨783, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0784 : bundle_64ff450e75_cubeCofacetCertificate (⟨784, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0785 : bundle_64ff450e75_cubeCofacetCertificate (⟨785, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0786 : bundle_64ff450e75_cubeCofacetCertificate (⟨786, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0787 : bundle_64ff450e75_cubeCofacetCertificate (⟨787, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0788 : bundle_64ff450e75_cubeCofacetCertificate (⟨788, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0789 : bundle_64ff450e75_cubeCofacetCertificate (⟨789, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0790 : bundle_64ff450e75_cubeCofacetCertificate (⟨790, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0791 : bundle_64ff450e75_cubeCofacetCertificate (⟨791, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0792 : bundle_64ff450e75_cubeCofacetCertificate (⟨792, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0793 : bundle_64ff450e75_cubeCofacetCertificate (⟨793, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0794 : bundle_64ff450e75_cubeCofacetCertificate (⟨794, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0795 : bundle_64ff450e75_cubeCofacetCertificate (⟨795, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0796 : bundle_64ff450e75_cubeCofacetCertificate (⟨796, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0797 : bundle_64ff450e75_cubeCofacetCertificate (⟨797, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0798 : bundle_64ff450e75_cubeCofacetCertificate (⟨798, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0799 : bundle_64ff450e75_cubeCofacetCertificate (⟨799, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0800 : bundle_64ff450e75_cubeCofacetCertificate (⟨800, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0801 : bundle_64ff450e75_cubeCofacetCertificate (⟨801, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0802 : bundle_64ff450e75_cubeCofacetCertificate (⟨802, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0803 : bundle_64ff450e75_cubeCofacetCertificate (⟨803, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0804 : bundle_64ff450e75_cubeCofacetCertificate (⟨804, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0805 : bundle_64ff450e75_cubeCofacetCertificate (⟨805, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0806 : bundle_64ff450e75_cubeCofacetCertificate (⟨806, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0807 : bundle_64ff450e75_cubeCofacetCertificate (⟨807, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0808 : bundle_64ff450e75_cubeCofacetCertificate (⟨808, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0809 : bundle_64ff450e75_cubeCofacetCertificate (⟨809, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0810 : bundle_64ff450e75_cubeCofacetCertificate (⟨810, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0811 : bundle_64ff450e75_cubeCofacetCertificate (⟨811, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0812 : bundle_64ff450e75_cubeCofacetCertificate (⟨812, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0813 : bundle_64ff450e75_cubeCofacetCertificate (⟨813, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0814 : bundle_64ff450e75_cubeCofacetCertificate (⟨814, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0815 : bundle_64ff450e75_cubeCofacetCertificate (⟨815, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0816 : bundle_64ff450e75_cubeCofacetCertificate (⟨816, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0817 : bundle_64ff450e75_cubeCofacetCertificate (⟨817, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0818 : bundle_64ff450e75_cubeCofacetCertificate (⟨818, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0819 : bundle_64ff450e75_cubeCofacetCertificate (⟨819, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0820 : bundle_64ff450e75_cubeCofacetCertificate (⟨820, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0821 : bundle_64ff450e75_cubeCofacetCertificate (⟨821, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0822 : bundle_64ff450e75_cubeCofacetCertificate (⟨822, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0823 : bundle_64ff450e75_cubeCofacetCertificate (⟨823, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0824 : bundle_64ff450e75_cubeCofacetCertificate (⟨824, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0825 : bundle_64ff450e75_cubeCofacetCertificate (⟨825, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0826 : bundle_64ff450e75_cubeCofacetCertificate (⟨826, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0827 : bundle_64ff450e75_cubeCofacetCertificate (⟨827, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0828 : bundle_64ff450e75_cubeCofacetCertificate (⟨828, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0829 : bundle_64ff450e75_cubeCofacetCertificate (⟨829, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0830 : bundle_64ff450e75_cubeCofacetCertificate (⟨830, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0831 : bundle_64ff450e75_cubeCofacetCertificate (⟨831, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0832 : bundle_64ff450e75_cubeCofacetCertificate (⟨832, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0833 : bundle_64ff450e75_cubeCofacetCertificate (⟨833, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0834 : bundle_64ff450e75_cubeCofacetCertificate (⟨834, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0835 : bundle_64ff450e75_cubeCofacetCertificate (⟨835, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0836 : bundle_64ff450e75_cubeCofacetCertificate (⟨836, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0837 : bundle_64ff450e75_cubeCofacetCertificate (⟨837, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0838 : bundle_64ff450e75_cubeCofacetCertificate (⟨838, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0839 : bundle_64ff450e75_cubeCofacetCertificate (⟨839, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0840 : bundle_64ff450e75_cubeCofacetCertificate (⟨840, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0841 : bundle_64ff450e75_cubeCofacetCertificate (⟨841, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0842 : bundle_64ff450e75_cubeCofacetCertificate (⟨842, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0843 : bundle_64ff450e75_cubeCofacetCertificate (⟨843, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0844 : bundle_64ff450e75_cubeCofacetCertificate (⟨844, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0845 : bundle_64ff450e75_cubeCofacetCertificate (⟨845, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0846 : bundle_64ff450e75_cubeCofacetCertificate (⟨846, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0847 : bundle_64ff450e75_cubeCofacetCertificate (⟨847, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0848 : bundle_64ff450e75_cubeCofacetCertificate (⟨848, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0849 : bundle_64ff450e75_cubeCofacetCertificate (⟨849, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0850 : bundle_64ff450e75_cubeCofacetCertificate (⟨850, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0851 : bundle_64ff450e75_cubeCofacetCertificate (⟨851, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0852 : bundle_64ff450e75_cubeCofacetCertificate (⟨852, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0853 : bundle_64ff450e75_cubeCofacetCertificate (⟨853, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0854 : bundle_64ff450e75_cubeCofacetCertificate (⟨854, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0855 : bundle_64ff450e75_cubeCofacetCertificate (⟨855, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0856 : bundle_64ff450e75_cubeCofacetCertificate (⟨856, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0857 : bundle_64ff450e75_cubeCofacetCertificate (⟨857, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0858 : bundle_64ff450e75_cubeCofacetCertificate (⟨858, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0859 : bundle_64ff450e75_cubeCofacetCertificate (⟨859, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0860 : bundle_64ff450e75_cubeCofacetCertificate (⟨860, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0861 : bundle_64ff450e75_cubeCofacetCertificate (⟨861, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0862 : bundle_64ff450e75_cubeCofacetCertificate (⟨862, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0863 : bundle_64ff450e75_cubeCofacetCertificate (⟨863, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0864 : bundle_64ff450e75_cubeCofacetCertificate (⟨864, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0865 : bundle_64ff450e75_cubeCofacetCertificate (⟨865, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0866 : bundle_64ff450e75_cubeCofacetCertificate (⟨866, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0867 : bundle_64ff450e75_cubeCofacetCertificate (⟨867, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0868 : bundle_64ff450e75_cubeCofacetCertificate (⟨868, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0869 : bundle_64ff450e75_cubeCofacetCertificate (⟨869, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0870 : bundle_64ff450e75_cubeCofacetCertificate (⟨870, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0871 : bundle_64ff450e75_cubeCofacetCertificate (⟨871, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0872 : bundle_64ff450e75_cubeCofacetCertificate (⟨872, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0873 : bundle_64ff450e75_cubeCofacetCertificate (⟨873, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0874 : bundle_64ff450e75_cubeCofacetCertificate (⟨874, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0875 : bundle_64ff450e75_cubeCofacetCertificate (⟨875, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0876 : bundle_64ff450e75_cubeCofacetCertificate (⟨876, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0877 : bundle_64ff450e75_cubeCofacetCertificate (⟨877, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0878 : bundle_64ff450e75_cubeCofacetCertificate (⟨878, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0879 : bundle_64ff450e75_cubeCofacetCertificate (⟨879, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0880 : bundle_64ff450e75_cubeCofacetCertificate (⟨880, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0881 : bundle_64ff450e75_cubeCofacetCertificate (⟨881, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0882 : bundle_64ff450e75_cubeCofacetCertificate (⟨882, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0883 : bundle_64ff450e75_cubeCofacetCertificate (⟨883, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0884 : bundle_64ff450e75_cubeCofacetCertificate (⟨884, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0885 : bundle_64ff450e75_cubeCofacetCertificate (⟨885, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0886 : bundle_64ff450e75_cubeCofacetCertificate (⟨886, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0887 : bundle_64ff450e75_cubeCofacetCertificate (⟨887, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0888 : bundle_64ff450e75_cubeCofacetCertificate (⟨888, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0889 : bundle_64ff450e75_cubeCofacetCertificate (⟨889, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0890 : bundle_64ff450e75_cubeCofacetCertificate (⟨890, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0891 : bundle_64ff450e75_cubeCofacetCertificate (⟨891, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0892 : bundle_64ff450e75_cubeCofacetCertificate (⟨892, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0893 : bundle_64ff450e75_cubeCofacetCertificate (⟨893, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0894 : bundle_64ff450e75_cubeCofacetCertificate (⟨894, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0895 : bundle_64ff450e75_cubeCofacetCertificate (⟨895, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0896 : bundle_64ff450e75_cubeCofacetCertificate (⟨896, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0897 : bundle_64ff450e75_cubeCofacetCertificate (⟨897, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0898 : bundle_64ff450e75_cubeCofacetCertificate (⟨898, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0899 : bundle_64ff450e75_cubeCofacetCertificate (⟨899, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0900 : bundle_64ff450e75_cubeCofacetCertificate (⟨900, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0901 : bundle_64ff450e75_cubeCofacetCertificate (⟨901, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0902 : bundle_64ff450e75_cubeCofacetCertificate (⟨902, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0903 : bundle_64ff450e75_cubeCofacetCertificate (⟨903, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0904 : bundle_64ff450e75_cubeCofacetCertificate (⟨904, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0905 : bundle_64ff450e75_cubeCofacetCertificate (⟨905, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0906 : bundle_64ff450e75_cubeCofacetCertificate (⟨906, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0907 : bundle_64ff450e75_cubeCofacetCertificate (⟨907, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0908 : bundle_64ff450e75_cubeCofacetCertificate (⟨908, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0909 : bundle_64ff450e75_cubeCofacetCertificate (⟨909, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0910 : bundle_64ff450e75_cubeCofacetCertificate (⟨910, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0911 : bundle_64ff450e75_cubeCofacetCertificate (⟨911, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0912 : bundle_64ff450e75_cubeCofacetCertificate (⟨912, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0913 : bundle_64ff450e75_cubeCofacetCertificate (⟨913, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0914 : bundle_64ff450e75_cubeCofacetCertificate (⟨914, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0915 : bundle_64ff450e75_cubeCofacetCertificate (⟨915, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0916 : bundle_64ff450e75_cubeCofacetCertificate (⟨916, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0917 : bundle_64ff450e75_cubeCofacetCertificate (⟨917, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0918 : bundle_64ff450e75_cubeCofacetCertificate (⟨918, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0919 : bundle_64ff450e75_cubeCofacetCertificate (⟨919, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0920 : bundle_64ff450e75_cubeCofacetCertificate (⟨920, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0921 : bundle_64ff450e75_cubeCofacetCertificate (⟨921, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0922 : bundle_64ff450e75_cubeCofacetCertificate (⟨922, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0923 : bundle_64ff450e75_cubeCofacetCertificate (⟨923, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0924 : bundle_64ff450e75_cubeCofacetCertificate (⟨924, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0925 : bundle_64ff450e75_cubeCofacetCertificate (⟨925, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0926 : bundle_64ff450e75_cubeCofacetCertificate (⟨926, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0927 : bundle_64ff450e75_cubeCofacetCertificate (⟨927, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0928 : bundle_64ff450e75_cubeCofacetCertificate (⟨928, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0929 : bundle_64ff450e75_cubeCofacetCertificate (⟨929, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0930 : bundle_64ff450e75_cubeCofacetCertificate (⟨930, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0931 : bundle_64ff450e75_cubeCofacetCertificate (⟨931, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0932 : bundle_64ff450e75_cubeCofacetCertificate (⟨932, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0933 : bundle_64ff450e75_cubeCofacetCertificate (⟨933, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0934 : bundle_64ff450e75_cubeCofacetCertificate (⟨934, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0935 : bundle_64ff450e75_cubeCofacetCertificate (⟨935, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0936 : bundle_64ff450e75_cubeCofacetCertificate (⟨936, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0937 : bundle_64ff450e75_cubeCofacetCertificate (⟨937, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0938 : bundle_64ff450e75_cubeCofacetCertificate (⟨938, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0939 : bundle_64ff450e75_cubeCofacetCertificate (⟨939, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0940 : bundle_64ff450e75_cubeCofacetCertificate (⟨940, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0941 : bundle_64ff450e75_cubeCofacetCertificate (⟨941, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0942 : bundle_64ff450e75_cubeCofacetCertificate (⟨942, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0943 : bundle_64ff450e75_cubeCofacetCertificate (⟨943, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0944 : bundle_64ff450e75_cubeCofacetCertificate (⟨944, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0945 : bundle_64ff450e75_cubeCofacetCertificate (⟨945, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0946 : bundle_64ff450e75_cubeCofacetCertificate (⟨946, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0947 : bundle_64ff450e75_cubeCofacetCertificate (⟨947, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0948 : bundle_64ff450e75_cubeCofacetCertificate (⟨948, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0949 : bundle_64ff450e75_cubeCofacetCertificate (⟨949, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0950 : bundle_64ff450e75_cubeCofacetCertificate (⟨950, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0951 : bundle_64ff450e75_cubeCofacetCertificate (⟨951, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0952 : bundle_64ff450e75_cubeCofacetCertificate (⟨952, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0953 : bundle_64ff450e75_cubeCofacetCertificate (⟨953, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0954 : bundle_64ff450e75_cubeCofacetCertificate (⟨954, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0955 : bundle_64ff450e75_cubeCofacetCertificate (⟨955, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0956 : bundle_64ff450e75_cubeCofacetCertificate (⟨956, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0957 : bundle_64ff450e75_cubeCofacetCertificate (⟨957, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0958 : bundle_64ff450e75_cubeCofacetCertificate (⟨958, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0959 : bundle_64ff450e75_cubeCofacetCertificate (⟨959, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0960 : bundle_64ff450e75_cubeCofacetCertificate (⟨960, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0961 : bundle_64ff450e75_cubeCofacetCertificate (⟨961, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0962 : bundle_64ff450e75_cubeCofacetCertificate (⟨962, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0963 : bundle_64ff450e75_cubeCofacetCertificate (⟨963, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0964 : bundle_64ff450e75_cubeCofacetCertificate (⟨964, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0965 : bundle_64ff450e75_cubeCofacetCertificate (⟨965, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0966 : bundle_64ff450e75_cubeCofacetCertificate (⟨966, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0967 : bundle_64ff450e75_cubeCofacetCertificate (⟨967, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0968 : bundle_64ff450e75_cubeCofacetCertificate (⟨968, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0969 : bundle_64ff450e75_cubeCofacetCertificate (⟨969, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0970 : bundle_64ff450e75_cubeCofacetCertificate (⟨970, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0971 : bundle_64ff450e75_cubeCofacetCertificate (⟨971, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0972 : bundle_64ff450e75_cubeCofacetCertificate (⟨972, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0973 : bundle_64ff450e75_cubeCofacetCertificate (⟨973, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0974 : bundle_64ff450e75_cubeCofacetCertificate (⟨974, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0975 : bundle_64ff450e75_cubeCofacetCertificate (⟨975, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0976 : bundle_64ff450e75_cubeCofacetCertificate (⟨976, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0977 : bundle_64ff450e75_cubeCofacetCertificate (⟨977, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0978 : bundle_64ff450e75_cubeCofacetCertificate (⟨978, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0979 : bundle_64ff450e75_cubeCofacetCertificate (⟨979, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0980 : bundle_64ff450e75_cubeCofacetCertificate (⟨980, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0981 : bundle_64ff450e75_cubeCofacetCertificate (⟨981, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0982 : bundle_64ff450e75_cubeCofacetCertificate (⟨982, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0983 : bundle_64ff450e75_cubeCofacetCertificate (⟨983, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0984 : bundle_64ff450e75_cubeCofacetCertificate (⟨984, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0985 : bundle_64ff450e75_cubeCofacetCertificate (⟨985, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0986 : bundle_64ff450e75_cubeCofacetCertificate (⟨986, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0987 : bundle_64ff450e75_cubeCofacetCertificate (⟨987, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0988 : bundle_64ff450e75_cubeCofacetCertificate (⟨988, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0989 : bundle_64ff450e75_cubeCofacetCertificate (⟨989, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0990 : bundle_64ff450e75_cubeCofacetCertificate (⟨990, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0991 : bundle_64ff450e75_cubeCofacetCertificate (⟨991, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0992 : bundle_64ff450e75_cubeCofacetCertificate (⟨992, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0993 : bundle_64ff450e75_cubeCofacetCertificate (⟨993, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0994 : bundle_64ff450e75_cubeCofacetCertificate (⟨994, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0995 : bundle_64ff450e75_cubeCofacetCertificate (⟨995, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0996 : bundle_64ff450e75_cubeCofacetCertificate (⟨996, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0997 : bundle_64ff450e75_cubeCofacetCertificate (⟨997, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0998 : bundle_64ff450e75_cubeCofacetCertificate (⟨998, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet0999 : bundle_64ff450e75_cubeCofacetCertificate (⟨999, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1000 : bundle_64ff450e75_cubeCofacetCertificate (⟨1000, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1001 : bundle_64ff450e75_cubeCofacetCertificate (⟨1001, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1002 : bundle_64ff450e75_cubeCofacetCertificate (⟨1002, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1003 : bundle_64ff450e75_cubeCofacetCertificate (⟨1003, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1004 : bundle_64ff450e75_cubeCofacetCertificate (⟨1004, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1005 : bundle_64ff450e75_cubeCofacetCertificate (⟨1005, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1006 : bundle_64ff450e75_cubeCofacetCertificate (⟨1006, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1007 : bundle_64ff450e75_cubeCofacetCertificate (⟨1007, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1008 : bundle_64ff450e75_cubeCofacetCertificate (⟨1008, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1009 : bundle_64ff450e75_cubeCofacetCertificate (⟨1009, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1010 : bundle_64ff450e75_cubeCofacetCertificate (⟨1010, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1011 : bundle_64ff450e75_cubeCofacetCertificate (⟨1011, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1012 : bundle_64ff450e75_cubeCofacetCertificate (⟨1012, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1013 : bundle_64ff450e75_cubeCofacetCertificate (⟨1013, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1014 : bundle_64ff450e75_cubeCofacetCertificate (⟨1014, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1015 : bundle_64ff450e75_cubeCofacetCertificate (⟨1015, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1016 : bundle_64ff450e75_cubeCofacetCertificate (⟨1016, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1017 : bundle_64ff450e75_cubeCofacetCertificate (⟨1017, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1018 : bundle_64ff450e75_cubeCofacetCertificate (⟨1018, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1019 : bundle_64ff450e75_cubeCofacetCertificate (⟨1019, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1020 : bundle_64ff450e75_cubeCofacetCertificate (⟨1020, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1021 : bundle_64ff450e75_cubeCofacetCertificate (⟨1021, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1022 : bundle_64ff450e75_cubeCofacetCertificate (⟨1022, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1023 : bundle_64ff450e75_cubeCofacetCertificate (⟨1023, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1024 : bundle_64ff450e75_cubeCofacetCertificate (⟨1024, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1025 : bundle_64ff450e75_cubeCofacetCertificate (⟨1025, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1026 : bundle_64ff450e75_cubeCofacetCertificate (⟨1026, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1027 : bundle_64ff450e75_cubeCofacetCertificate (⟨1027, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1028 : bundle_64ff450e75_cubeCofacetCertificate (⟨1028, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1029 : bundle_64ff450e75_cubeCofacetCertificate (⟨1029, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1030 : bundle_64ff450e75_cubeCofacetCertificate (⟨1030, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1031 : bundle_64ff450e75_cubeCofacetCertificate (⟨1031, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1032 : bundle_64ff450e75_cubeCofacetCertificate (⟨1032, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1033 : bundle_64ff450e75_cubeCofacetCertificate (⟨1033, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1034 : bundle_64ff450e75_cubeCofacetCertificate (⟨1034, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1035 : bundle_64ff450e75_cubeCofacetCertificate (⟨1035, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1036 : bundle_64ff450e75_cubeCofacetCertificate (⟨1036, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1037 : bundle_64ff450e75_cubeCofacetCertificate (⟨1037, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1038 : bundle_64ff450e75_cubeCofacetCertificate (⟨1038, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1039 : bundle_64ff450e75_cubeCofacetCertificate (⟨1039, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1040 : bundle_64ff450e75_cubeCofacetCertificate (⟨1040, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1041 : bundle_64ff450e75_cubeCofacetCertificate (⟨1041, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1042 : bundle_64ff450e75_cubeCofacetCertificate (⟨1042, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1043 : bundle_64ff450e75_cubeCofacetCertificate (⟨1043, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1044 : bundle_64ff450e75_cubeCofacetCertificate (⟨1044, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1045 : bundle_64ff450e75_cubeCofacetCertificate (⟨1045, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1046 : bundle_64ff450e75_cubeCofacetCertificate (⟨1046, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1047 : bundle_64ff450e75_cubeCofacetCertificate (⟨1047, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1048 : bundle_64ff450e75_cubeCofacetCertificate (⟨1048, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1049 : bundle_64ff450e75_cubeCofacetCertificate (⟨1049, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1050 : bundle_64ff450e75_cubeCofacetCertificate (⟨1050, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1051 : bundle_64ff450e75_cubeCofacetCertificate (⟨1051, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1052 : bundle_64ff450e75_cubeCofacetCertificate (⟨1052, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1053 : bundle_64ff450e75_cubeCofacetCertificate (⟨1053, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1054 : bundle_64ff450e75_cubeCofacetCertificate (⟨1054, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1055 : bundle_64ff450e75_cubeCofacetCertificate (⟨1055, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1056 : bundle_64ff450e75_cubeCofacetCertificate (⟨1056, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1057 : bundle_64ff450e75_cubeCofacetCertificate (⟨1057, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1058 : bundle_64ff450e75_cubeCofacetCertificate (⟨1058, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1059 : bundle_64ff450e75_cubeCofacetCertificate (⟨1059, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1060 : bundle_64ff450e75_cubeCofacetCertificate (⟨1060, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1061 : bundle_64ff450e75_cubeCofacetCertificate (⟨1061, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1062 : bundle_64ff450e75_cubeCofacetCertificate (⟨1062, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1063 : bundle_64ff450e75_cubeCofacetCertificate (⟨1063, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1064 : bundle_64ff450e75_cubeCofacetCertificate (⟨1064, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1065 : bundle_64ff450e75_cubeCofacetCertificate (⟨1065, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1066 : bundle_64ff450e75_cubeCofacetCertificate (⟨1066, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1067 : bundle_64ff450e75_cubeCofacetCertificate (⟨1067, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacet1068 : bundle_64ff450e75_cubeCofacetCertificate (⟨1068, by decide⟩ : Fin 1069) := by
  apply bundle_64ff450e75_cubeCofacetCertificate_of_check
  decide +kernel

theorem bundle_64ff450e75_cofacetGroup0000 (i : Fin 1069)
    (hlo : 0 ≤ i.val) (hhi : i.val < 32) :
    bundle_64ff450e75_cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h16 : i.val < 16
  ·
    by_cases h8 : i.val < 8
    ·
      by_cases h4 : i.val < 4
      ·
        by_cases h2 : i.val < 2
        ·
          by_cases h1 : i.val < 1
          ·
            have he : (⟨0, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 0 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0000
          ·
            have he : (⟨1, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 1 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0001
        ·
          by_cases h3 : i.val < 3
          ·
            have he : (⟨2, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 2 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0002
          ·
            have he : (⟨3, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 3 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0003
      ·
        by_cases h6 : i.val < 6
        ·
          by_cases h5 : i.val < 5
          ·
            have he : (⟨4, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 4 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0004
          ·
            have he : (⟨5, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 5 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0005
        ·
          by_cases h7 : i.val < 7
          ·
            have he : (⟨6, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 6 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0006
          ·
            have he : (⟨7, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 7 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0007
    ·
      by_cases h12 : i.val < 12
      ·
        by_cases h10 : i.val < 10
        ·
          by_cases h9 : i.val < 9
          ·
            have he : (⟨8, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 8 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0008
          ·
            have he : (⟨9, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 9 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0009
        ·
          by_cases h11 : i.val < 11
          ·
            have he : (⟨10, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 10 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0010
          ·
            have he : (⟨11, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 11 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0011
      ·
        by_cases h14 : i.val < 14
        ·
          by_cases h13 : i.val < 13
          ·
            have he : (⟨12, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 12 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0012
          ·
            have he : (⟨13, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 13 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0013
        ·
          by_cases h15 : i.val < 15
          ·
            have he : (⟨14, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 14 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0014
          ·
            have he : (⟨15, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 15 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0015
  ·
    by_cases h24 : i.val < 24
    ·
      by_cases h20 : i.val < 20
      ·
        by_cases h18 : i.val < 18
        ·
          by_cases h17 : i.val < 17
          ·
            have he : (⟨16, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 16 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0016
          ·
            have he : (⟨17, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 17 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0017
        ·
          by_cases h19 : i.val < 19
          ·
            have he : (⟨18, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 18 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0018
          ·
            have he : (⟨19, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 19 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0019
      ·
        by_cases h22 : i.val < 22
        ·
          by_cases h21 : i.val < 21
          ·
            have he : (⟨20, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 20 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0020
          ·
            have he : (⟨21, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 21 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0021
        ·
          by_cases h23 : i.val < 23
          ·
            have he : (⟨22, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 22 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0022
          ·
            have he : (⟨23, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 23 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0023
    ·
      by_cases h28 : i.val < 28
      ·
        by_cases h26 : i.val < 26
        ·
          by_cases h25 : i.val < 25
          ·
            have he : (⟨24, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 24 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0024
          ·
            have he : (⟨25, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 25 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0025
        ·
          by_cases h27 : i.val < 27
          ·
            have he : (⟨26, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 26 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0026
          ·
            have he : (⟨27, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 27 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0027
      ·
        by_cases h30 : i.val < 30
        ·
          by_cases h29 : i.val < 29
          ·
            have he : (⟨28, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 28 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0028
          ·
            have he : (⟨29, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 29 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0029
        ·
          by_cases h31 : i.val < 31
          ·
            have he : (⟨30, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 30 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0030
          ·
            have he : (⟨31, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 31 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0031

theorem bundle_64ff450e75_cofacetGroup0001 (i : Fin 1069)
    (hlo : 32 ≤ i.val) (hhi : i.val < 64) :
    bundle_64ff450e75_cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h48 : i.val < 48
  ·
    by_cases h40 : i.val < 40
    ·
      by_cases h36 : i.val < 36
      ·
        by_cases h34 : i.val < 34
        ·
          by_cases h33 : i.val < 33
          ·
            have he : (⟨32, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 32 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0032
          ·
            have he : (⟨33, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 33 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0033
        ·
          by_cases h35 : i.val < 35
          ·
            have he : (⟨34, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 34 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0034
          ·
            have he : (⟨35, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 35 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0035
      ·
        by_cases h38 : i.val < 38
        ·
          by_cases h37 : i.val < 37
          ·
            have he : (⟨36, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 36 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0036
          ·
            have he : (⟨37, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 37 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0037
        ·
          by_cases h39 : i.val < 39
          ·
            have he : (⟨38, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 38 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0038
          ·
            have he : (⟨39, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 39 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0039
    ·
      by_cases h44 : i.val < 44
      ·
        by_cases h42 : i.val < 42
        ·
          by_cases h41 : i.val < 41
          ·
            have he : (⟨40, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 40 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0040
          ·
            have he : (⟨41, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 41 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0041
        ·
          by_cases h43 : i.val < 43
          ·
            have he : (⟨42, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 42 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0042
          ·
            have he : (⟨43, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 43 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0043
      ·
        by_cases h46 : i.val < 46
        ·
          by_cases h45 : i.val < 45
          ·
            have he : (⟨44, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 44 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0044
          ·
            have he : (⟨45, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 45 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0045
        ·
          by_cases h47 : i.val < 47
          ·
            have he : (⟨46, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 46 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0046
          ·
            have he : (⟨47, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 47 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0047
  ·
    by_cases h56 : i.val < 56
    ·
      by_cases h52 : i.val < 52
      ·
        by_cases h50 : i.val < 50
        ·
          by_cases h49 : i.val < 49
          ·
            have he : (⟨48, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 48 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0048
          ·
            have he : (⟨49, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 49 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0049
        ·
          by_cases h51 : i.val < 51
          ·
            have he : (⟨50, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 50 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0050
          ·
            have he : (⟨51, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 51 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0051
      ·
        by_cases h54 : i.val < 54
        ·
          by_cases h53 : i.val < 53
          ·
            have he : (⟨52, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 52 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0052
          ·
            have he : (⟨53, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 53 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0053
        ·
          by_cases h55 : i.val < 55
          ·
            have he : (⟨54, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 54 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0054
          ·
            have he : (⟨55, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 55 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0055
    ·
      by_cases h60 : i.val < 60
      ·
        by_cases h58 : i.val < 58
        ·
          by_cases h57 : i.val < 57
          ·
            have he : (⟨56, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 56 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0056
          ·
            have he : (⟨57, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 57 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0057
        ·
          by_cases h59 : i.val < 59
          ·
            have he : (⟨58, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 58 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0058
          ·
            have he : (⟨59, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 59 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0059
      ·
        by_cases h62 : i.val < 62
        ·
          by_cases h61 : i.val < 61
          ·
            have he : (⟨60, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 60 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0060
          ·
            have he : (⟨61, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 61 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0061
        ·
          by_cases h63 : i.val < 63
          ·
            have he : (⟨62, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 62 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0062
          ·
            have he : (⟨63, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 63 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0063

theorem bundle_64ff450e75_cofacetGroup0002 (i : Fin 1069)
    (hlo : 64 ≤ i.val) (hhi : i.val < 96) :
    bundle_64ff450e75_cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h80 : i.val < 80
  ·
    by_cases h72 : i.val < 72
    ·
      by_cases h68 : i.val < 68
      ·
        by_cases h66 : i.val < 66
        ·
          by_cases h65 : i.val < 65
          ·
            have he : (⟨64, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 64 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0064
          ·
            have he : (⟨65, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 65 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0065
        ·
          by_cases h67 : i.val < 67
          ·
            have he : (⟨66, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 66 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0066
          ·
            have he : (⟨67, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 67 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0067
      ·
        by_cases h70 : i.val < 70
        ·
          by_cases h69 : i.val < 69
          ·
            have he : (⟨68, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 68 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0068
          ·
            have he : (⟨69, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 69 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0069
        ·
          by_cases h71 : i.val < 71
          ·
            have he : (⟨70, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 70 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0070
          ·
            have he : (⟨71, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 71 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0071
    ·
      by_cases h76 : i.val < 76
      ·
        by_cases h74 : i.val < 74
        ·
          by_cases h73 : i.val < 73
          ·
            have he : (⟨72, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 72 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0072
          ·
            have he : (⟨73, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 73 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0073
        ·
          by_cases h75 : i.val < 75
          ·
            have he : (⟨74, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 74 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0074
          ·
            have he : (⟨75, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 75 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0075
      ·
        by_cases h78 : i.val < 78
        ·
          by_cases h77 : i.val < 77
          ·
            have he : (⟨76, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 76 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0076
          ·
            have he : (⟨77, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 77 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0077
        ·
          by_cases h79 : i.val < 79
          ·
            have he : (⟨78, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 78 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0078
          ·
            have he : (⟨79, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 79 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0079
  ·
    by_cases h88 : i.val < 88
    ·
      by_cases h84 : i.val < 84
      ·
        by_cases h82 : i.val < 82
        ·
          by_cases h81 : i.val < 81
          ·
            have he : (⟨80, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 80 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0080
          ·
            have he : (⟨81, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 81 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0081
        ·
          by_cases h83 : i.val < 83
          ·
            have he : (⟨82, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 82 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0082
          ·
            have he : (⟨83, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 83 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0083
      ·
        by_cases h86 : i.val < 86
        ·
          by_cases h85 : i.val < 85
          ·
            have he : (⟨84, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 84 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0084
          ·
            have he : (⟨85, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 85 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0085
        ·
          by_cases h87 : i.val < 87
          ·
            have he : (⟨86, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 86 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0086
          ·
            have he : (⟨87, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 87 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0087
    ·
      by_cases h92 : i.val < 92
      ·
        by_cases h90 : i.val < 90
        ·
          by_cases h89 : i.val < 89
          ·
            have he : (⟨88, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 88 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0088
          ·
            have he : (⟨89, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 89 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0089
        ·
          by_cases h91 : i.val < 91
          ·
            have he : (⟨90, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 90 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0090
          ·
            have he : (⟨91, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 91 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0091
      ·
        by_cases h94 : i.val < 94
        ·
          by_cases h93 : i.val < 93
          ·
            have he : (⟨92, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 92 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0092
          ·
            have he : (⟨93, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 93 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0093
        ·
          by_cases h95 : i.val < 95
          ·
            have he : (⟨94, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 94 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0094
          ·
            have he : (⟨95, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 95 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0095

theorem bundle_64ff450e75_cofacetGroup0003 (i : Fin 1069)
    (hlo : 96 ≤ i.val) (hhi : i.val < 128) :
    bundle_64ff450e75_cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h112 : i.val < 112
  ·
    by_cases h104 : i.val < 104
    ·
      by_cases h100 : i.val < 100
      ·
        by_cases h98 : i.val < 98
        ·
          by_cases h97 : i.val < 97
          ·
            have he : (⟨96, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 96 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0096
          ·
            have he : (⟨97, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 97 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0097
        ·
          by_cases h99 : i.val < 99
          ·
            have he : (⟨98, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 98 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0098
          ·
            have he : (⟨99, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 99 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0099
      ·
        by_cases h102 : i.val < 102
        ·
          by_cases h101 : i.val < 101
          ·
            have he : (⟨100, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 100 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0100
          ·
            have he : (⟨101, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 101 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0101
        ·
          by_cases h103 : i.val < 103
          ·
            have he : (⟨102, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 102 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0102
          ·
            have he : (⟨103, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 103 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0103
    ·
      by_cases h108 : i.val < 108
      ·
        by_cases h106 : i.val < 106
        ·
          by_cases h105 : i.val < 105
          ·
            have he : (⟨104, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 104 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0104
          ·
            have he : (⟨105, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 105 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0105
        ·
          by_cases h107 : i.val < 107
          ·
            have he : (⟨106, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 106 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0106
          ·
            have he : (⟨107, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 107 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0107
      ·
        by_cases h110 : i.val < 110
        ·
          by_cases h109 : i.val < 109
          ·
            have he : (⟨108, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 108 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0108
          ·
            have he : (⟨109, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 109 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0109
        ·
          by_cases h111 : i.val < 111
          ·
            have he : (⟨110, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 110 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0110
          ·
            have he : (⟨111, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 111 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0111
  ·
    by_cases h120 : i.val < 120
    ·
      by_cases h116 : i.val < 116
      ·
        by_cases h114 : i.val < 114
        ·
          by_cases h113 : i.val < 113
          ·
            have he : (⟨112, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 112 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0112
          ·
            have he : (⟨113, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 113 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0113
        ·
          by_cases h115 : i.val < 115
          ·
            have he : (⟨114, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 114 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0114
          ·
            have he : (⟨115, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 115 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0115
      ·
        by_cases h118 : i.val < 118
        ·
          by_cases h117 : i.val < 117
          ·
            have he : (⟨116, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 116 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0116
          ·
            have he : (⟨117, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 117 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0117
        ·
          by_cases h119 : i.val < 119
          ·
            have he : (⟨118, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 118 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0118
          ·
            have he : (⟨119, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 119 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0119
    ·
      by_cases h124 : i.val < 124
      ·
        by_cases h122 : i.val < 122
        ·
          by_cases h121 : i.val < 121
          ·
            have he : (⟨120, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 120 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0120
          ·
            have he : (⟨121, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 121 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0121
        ·
          by_cases h123 : i.val < 123
          ·
            have he : (⟨122, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 122 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0122
          ·
            have he : (⟨123, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 123 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0123
      ·
        by_cases h126 : i.val < 126
        ·
          by_cases h125 : i.val < 125
          ·
            have he : (⟨124, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 124 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0124
          ·
            have he : (⟨125, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 125 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0125
        ·
          by_cases h127 : i.val < 127
          ·
            have he : (⟨126, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 126 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0126
          ·
            have he : (⟨127, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 127 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0127

theorem bundle_64ff450e75_cofacetGroup0004 (i : Fin 1069)
    (hlo : 128 ≤ i.val) (hhi : i.val < 160) :
    bundle_64ff450e75_cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h144 : i.val < 144
  ·
    by_cases h136 : i.val < 136
    ·
      by_cases h132 : i.val < 132
      ·
        by_cases h130 : i.val < 130
        ·
          by_cases h129 : i.val < 129
          ·
            have he : (⟨128, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 128 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0128
          ·
            have he : (⟨129, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 129 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0129
        ·
          by_cases h131 : i.val < 131
          ·
            have he : (⟨130, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 130 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0130
          ·
            have he : (⟨131, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 131 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0131
      ·
        by_cases h134 : i.val < 134
        ·
          by_cases h133 : i.val < 133
          ·
            have he : (⟨132, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 132 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0132
          ·
            have he : (⟨133, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 133 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0133
        ·
          by_cases h135 : i.val < 135
          ·
            have he : (⟨134, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 134 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0134
          ·
            have he : (⟨135, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 135 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0135
    ·
      by_cases h140 : i.val < 140
      ·
        by_cases h138 : i.val < 138
        ·
          by_cases h137 : i.val < 137
          ·
            have he : (⟨136, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 136 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0136
          ·
            have he : (⟨137, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 137 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0137
        ·
          by_cases h139 : i.val < 139
          ·
            have he : (⟨138, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 138 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0138
          ·
            have he : (⟨139, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 139 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0139
      ·
        by_cases h142 : i.val < 142
        ·
          by_cases h141 : i.val < 141
          ·
            have he : (⟨140, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 140 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0140
          ·
            have he : (⟨141, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 141 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0141
        ·
          by_cases h143 : i.val < 143
          ·
            have he : (⟨142, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 142 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0142
          ·
            have he : (⟨143, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 143 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0143
  ·
    by_cases h152 : i.val < 152
    ·
      by_cases h148 : i.val < 148
      ·
        by_cases h146 : i.val < 146
        ·
          by_cases h145 : i.val < 145
          ·
            have he : (⟨144, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 144 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0144
          ·
            have he : (⟨145, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 145 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0145
        ·
          by_cases h147 : i.val < 147
          ·
            have he : (⟨146, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 146 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0146
          ·
            have he : (⟨147, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 147 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0147
      ·
        by_cases h150 : i.val < 150
        ·
          by_cases h149 : i.val < 149
          ·
            have he : (⟨148, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 148 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0148
          ·
            have he : (⟨149, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 149 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0149
        ·
          by_cases h151 : i.val < 151
          ·
            have he : (⟨150, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 150 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0150
          ·
            have he : (⟨151, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 151 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0151
    ·
      by_cases h156 : i.val < 156
      ·
        by_cases h154 : i.val < 154
        ·
          by_cases h153 : i.val < 153
          ·
            have he : (⟨152, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 152 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0152
          ·
            have he : (⟨153, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 153 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0153
        ·
          by_cases h155 : i.val < 155
          ·
            have he : (⟨154, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 154 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0154
          ·
            have he : (⟨155, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 155 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0155
      ·
        by_cases h158 : i.val < 158
        ·
          by_cases h157 : i.val < 157
          ·
            have he : (⟨156, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 156 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0156
          ·
            have he : (⟨157, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 157 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0157
        ·
          by_cases h159 : i.val < 159
          ·
            have he : (⟨158, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 158 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0158
          ·
            have he : (⟨159, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 159 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0159

theorem bundle_64ff450e75_cofacetGroup0005 (i : Fin 1069)
    (hlo : 160 ≤ i.val) (hhi : i.val < 192) :
    bundle_64ff450e75_cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h176 : i.val < 176
  ·
    by_cases h168 : i.val < 168
    ·
      by_cases h164 : i.val < 164
      ·
        by_cases h162 : i.val < 162
        ·
          by_cases h161 : i.val < 161
          ·
            have he : (⟨160, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 160 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0160
          ·
            have he : (⟨161, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 161 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0161
        ·
          by_cases h163 : i.val < 163
          ·
            have he : (⟨162, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 162 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0162
          ·
            have he : (⟨163, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 163 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0163
      ·
        by_cases h166 : i.val < 166
        ·
          by_cases h165 : i.val < 165
          ·
            have he : (⟨164, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 164 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0164
          ·
            have he : (⟨165, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 165 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0165
        ·
          by_cases h167 : i.val < 167
          ·
            have he : (⟨166, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 166 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0166
          ·
            have he : (⟨167, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 167 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0167
    ·
      by_cases h172 : i.val < 172
      ·
        by_cases h170 : i.val < 170
        ·
          by_cases h169 : i.val < 169
          ·
            have he : (⟨168, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 168 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0168
          ·
            have he : (⟨169, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 169 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0169
        ·
          by_cases h171 : i.val < 171
          ·
            have he : (⟨170, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 170 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0170
          ·
            have he : (⟨171, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 171 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0171
      ·
        by_cases h174 : i.val < 174
        ·
          by_cases h173 : i.val < 173
          ·
            have he : (⟨172, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 172 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0172
          ·
            have he : (⟨173, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 173 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0173
        ·
          by_cases h175 : i.val < 175
          ·
            have he : (⟨174, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 174 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0174
          ·
            have he : (⟨175, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 175 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0175
  ·
    by_cases h184 : i.val < 184
    ·
      by_cases h180 : i.val < 180
      ·
        by_cases h178 : i.val < 178
        ·
          by_cases h177 : i.val < 177
          ·
            have he : (⟨176, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 176 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0176
          ·
            have he : (⟨177, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 177 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0177
        ·
          by_cases h179 : i.val < 179
          ·
            have he : (⟨178, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 178 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0178
          ·
            have he : (⟨179, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 179 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0179
      ·
        by_cases h182 : i.val < 182
        ·
          by_cases h181 : i.val < 181
          ·
            have he : (⟨180, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 180 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0180
          ·
            have he : (⟨181, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 181 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0181
        ·
          by_cases h183 : i.val < 183
          ·
            have he : (⟨182, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 182 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0182
          ·
            have he : (⟨183, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 183 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0183
    ·
      by_cases h188 : i.val < 188
      ·
        by_cases h186 : i.val < 186
        ·
          by_cases h185 : i.val < 185
          ·
            have he : (⟨184, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 184 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0184
          ·
            have he : (⟨185, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 185 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0185
        ·
          by_cases h187 : i.val < 187
          ·
            have he : (⟨186, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 186 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0186
          ·
            have he : (⟨187, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 187 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0187
      ·
        by_cases h190 : i.val < 190
        ·
          by_cases h189 : i.val < 189
          ·
            have he : (⟨188, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 188 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0188
          ·
            have he : (⟨189, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 189 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0189
        ·
          by_cases h191 : i.val < 191
          ·
            have he : (⟨190, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 190 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0190
          ·
            have he : (⟨191, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 191 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0191

theorem bundle_64ff450e75_cofacetGroup0006 (i : Fin 1069)
    (hlo : 192 ≤ i.val) (hhi : i.val < 224) :
    bundle_64ff450e75_cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h208 : i.val < 208
  ·
    by_cases h200 : i.val < 200
    ·
      by_cases h196 : i.val < 196
      ·
        by_cases h194 : i.val < 194
        ·
          by_cases h193 : i.val < 193
          ·
            have he : (⟨192, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 192 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0192
          ·
            have he : (⟨193, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 193 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0193
        ·
          by_cases h195 : i.val < 195
          ·
            have he : (⟨194, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 194 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0194
          ·
            have he : (⟨195, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 195 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0195
      ·
        by_cases h198 : i.val < 198
        ·
          by_cases h197 : i.val < 197
          ·
            have he : (⟨196, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 196 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0196
          ·
            have he : (⟨197, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 197 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0197
        ·
          by_cases h199 : i.val < 199
          ·
            have he : (⟨198, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 198 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0198
          ·
            have he : (⟨199, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 199 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0199
    ·
      by_cases h204 : i.val < 204
      ·
        by_cases h202 : i.val < 202
        ·
          by_cases h201 : i.val < 201
          ·
            have he : (⟨200, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 200 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0200
          ·
            have he : (⟨201, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 201 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0201
        ·
          by_cases h203 : i.val < 203
          ·
            have he : (⟨202, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 202 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0202
          ·
            have he : (⟨203, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 203 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0203
      ·
        by_cases h206 : i.val < 206
        ·
          by_cases h205 : i.val < 205
          ·
            have he : (⟨204, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 204 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0204
          ·
            have he : (⟨205, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 205 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0205
        ·
          by_cases h207 : i.val < 207
          ·
            have he : (⟨206, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 206 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0206
          ·
            have he : (⟨207, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 207 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0207
  ·
    by_cases h216 : i.val < 216
    ·
      by_cases h212 : i.val < 212
      ·
        by_cases h210 : i.val < 210
        ·
          by_cases h209 : i.val < 209
          ·
            have he : (⟨208, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 208 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0208
          ·
            have he : (⟨209, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 209 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0209
        ·
          by_cases h211 : i.val < 211
          ·
            have he : (⟨210, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 210 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0210
          ·
            have he : (⟨211, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 211 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0211
      ·
        by_cases h214 : i.val < 214
        ·
          by_cases h213 : i.val < 213
          ·
            have he : (⟨212, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 212 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0212
          ·
            have he : (⟨213, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 213 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0213
        ·
          by_cases h215 : i.val < 215
          ·
            have he : (⟨214, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 214 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0214
          ·
            have he : (⟨215, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 215 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0215
    ·
      by_cases h220 : i.val < 220
      ·
        by_cases h218 : i.val < 218
        ·
          by_cases h217 : i.val < 217
          ·
            have he : (⟨216, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 216 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0216
          ·
            have he : (⟨217, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 217 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0217
        ·
          by_cases h219 : i.val < 219
          ·
            have he : (⟨218, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 218 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0218
          ·
            have he : (⟨219, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 219 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0219
      ·
        by_cases h222 : i.val < 222
        ·
          by_cases h221 : i.val < 221
          ·
            have he : (⟨220, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 220 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0220
          ·
            have he : (⟨221, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 221 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0221
        ·
          by_cases h223 : i.val < 223
          ·
            have he : (⟨222, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 222 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0222
          ·
            have he : (⟨223, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 223 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0223

theorem bundle_64ff450e75_cofacetGroup0007 (i : Fin 1069)
    (hlo : 224 ≤ i.val) (hhi : i.val < 256) :
    bundle_64ff450e75_cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h240 : i.val < 240
  ·
    by_cases h232 : i.val < 232
    ·
      by_cases h228 : i.val < 228
      ·
        by_cases h226 : i.val < 226
        ·
          by_cases h225 : i.val < 225
          ·
            have he : (⟨224, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 224 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0224
          ·
            have he : (⟨225, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 225 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0225
        ·
          by_cases h227 : i.val < 227
          ·
            have he : (⟨226, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 226 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0226
          ·
            have he : (⟨227, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 227 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0227
      ·
        by_cases h230 : i.val < 230
        ·
          by_cases h229 : i.val < 229
          ·
            have he : (⟨228, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 228 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0228
          ·
            have he : (⟨229, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 229 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0229
        ·
          by_cases h231 : i.val < 231
          ·
            have he : (⟨230, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 230 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0230
          ·
            have he : (⟨231, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 231 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0231
    ·
      by_cases h236 : i.val < 236
      ·
        by_cases h234 : i.val < 234
        ·
          by_cases h233 : i.val < 233
          ·
            have he : (⟨232, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 232 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0232
          ·
            have he : (⟨233, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 233 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0233
        ·
          by_cases h235 : i.val < 235
          ·
            have he : (⟨234, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 234 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0234
          ·
            have he : (⟨235, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 235 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0235
      ·
        by_cases h238 : i.val < 238
        ·
          by_cases h237 : i.val < 237
          ·
            have he : (⟨236, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 236 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0236
          ·
            have he : (⟨237, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 237 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0237
        ·
          by_cases h239 : i.val < 239
          ·
            have he : (⟨238, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 238 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0238
          ·
            have he : (⟨239, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 239 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0239
  ·
    by_cases h248 : i.val < 248
    ·
      by_cases h244 : i.val < 244
      ·
        by_cases h242 : i.val < 242
        ·
          by_cases h241 : i.val < 241
          ·
            have he : (⟨240, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 240 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0240
          ·
            have he : (⟨241, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 241 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0241
        ·
          by_cases h243 : i.val < 243
          ·
            have he : (⟨242, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 242 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0242
          ·
            have he : (⟨243, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 243 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0243
      ·
        by_cases h246 : i.val < 246
        ·
          by_cases h245 : i.val < 245
          ·
            have he : (⟨244, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 244 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0244
          ·
            have he : (⟨245, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 245 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0245
        ·
          by_cases h247 : i.val < 247
          ·
            have he : (⟨246, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 246 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0246
          ·
            have he : (⟨247, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 247 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0247
    ·
      by_cases h252 : i.val < 252
      ·
        by_cases h250 : i.val < 250
        ·
          by_cases h249 : i.val < 249
          ·
            have he : (⟨248, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 248 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0248
          ·
            have he : (⟨249, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 249 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0249
        ·
          by_cases h251 : i.val < 251
          ·
            have he : (⟨250, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 250 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0250
          ·
            have he : (⟨251, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 251 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0251
      ·
        by_cases h254 : i.val < 254
        ·
          by_cases h253 : i.val < 253
          ·
            have he : (⟨252, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 252 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0252
          ·
            have he : (⟨253, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 253 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0253
        ·
          by_cases h255 : i.val < 255
          ·
            have he : (⟨254, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 254 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0254
          ·
            have he : (⟨255, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 255 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0255

theorem bundle_64ff450e75_cofacetGroup0008 (i : Fin 1069)
    (hlo : 256 ≤ i.val) (hhi : i.val < 288) :
    bundle_64ff450e75_cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h272 : i.val < 272
  ·
    by_cases h264 : i.val < 264
    ·
      by_cases h260 : i.val < 260
      ·
        by_cases h258 : i.val < 258
        ·
          by_cases h257 : i.val < 257
          ·
            have he : (⟨256, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 256 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0256
          ·
            have he : (⟨257, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 257 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0257
        ·
          by_cases h259 : i.val < 259
          ·
            have he : (⟨258, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 258 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0258
          ·
            have he : (⟨259, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 259 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0259
      ·
        by_cases h262 : i.val < 262
        ·
          by_cases h261 : i.val < 261
          ·
            have he : (⟨260, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 260 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0260
          ·
            have he : (⟨261, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 261 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0261
        ·
          by_cases h263 : i.val < 263
          ·
            have he : (⟨262, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 262 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0262
          ·
            have he : (⟨263, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 263 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0263
    ·
      by_cases h268 : i.val < 268
      ·
        by_cases h266 : i.val < 266
        ·
          by_cases h265 : i.val < 265
          ·
            have he : (⟨264, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 264 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0264
          ·
            have he : (⟨265, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 265 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0265
        ·
          by_cases h267 : i.val < 267
          ·
            have he : (⟨266, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 266 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0266
          ·
            have he : (⟨267, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 267 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0267
      ·
        by_cases h270 : i.val < 270
        ·
          by_cases h269 : i.val < 269
          ·
            have he : (⟨268, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 268 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0268
          ·
            have he : (⟨269, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 269 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0269
        ·
          by_cases h271 : i.val < 271
          ·
            have he : (⟨270, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 270 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0270
          ·
            have he : (⟨271, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 271 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0271
  ·
    by_cases h280 : i.val < 280
    ·
      by_cases h276 : i.val < 276
      ·
        by_cases h274 : i.val < 274
        ·
          by_cases h273 : i.val < 273
          ·
            have he : (⟨272, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 272 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0272
          ·
            have he : (⟨273, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 273 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0273
        ·
          by_cases h275 : i.val < 275
          ·
            have he : (⟨274, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 274 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0274
          ·
            have he : (⟨275, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 275 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0275
      ·
        by_cases h278 : i.val < 278
        ·
          by_cases h277 : i.val < 277
          ·
            have he : (⟨276, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 276 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0276
          ·
            have he : (⟨277, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 277 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0277
        ·
          by_cases h279 : i.val < 279
          ·
            have he : (⟨278, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 278 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0278
          ·
            have he : (⟨279, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 279 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0279
    ·
      by_cases h284 : i.val < 284
      ·
        by_cases h282 : i.val < 282
        ·
          by_cases h281 : i.val < 281
          ·
            have he : (⟨280, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 280 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0280
          ·
            have he : (⟨281, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 281 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0281
        ·
          by_cases h283 : i.val < 283
          ·
            have he : (⟨282, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 282 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0282
          ·
            have he : (⟨283, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 283 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0283
      ·
        by_cases h286 : i.val < 286
        ·
          by_cases h285 : i.val < 285
          ·
            have he : (⟨284, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 284 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0284
          ·
            have he : (⟨285, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 285 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0285
        ·
          by_cases h287 : i.val < 287
          ·
            have he : (⟨286, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 286 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0286
          ·
            have he : (⟨287, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 287 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0287

theorem bundle_64ff450e75_cofacetGroup0009 (i : Fin 1069)
    (hlo : 288 ≤ i.val) (hhi : i.val < 320) :
    bundle_64ff450e75_cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h304 : i.val < 304
  ·
    by_cases h296 : i.val < 296
    ·
      by_cases h292 : i.val < 292
      ·
        by_cases h290 : i.val < 290
        ·
          by_cases h289 : i.val < 289
          ·
            have he : (⟨288, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 288 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0288
          ·
            have he : (⟨289, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 289 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0289
        ·
          by_cases h291 : i.val < 291
          ·
            have he : (⟨290, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 290 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0290
          ·
            have he : (⟨291, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 291 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0291
      ·
        by_cases h294 : i.val < 294
        ·
          by_cases h293 : i.val < 293
          ·
            have he : (⟨292, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 292 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0292
          ·
            have he : (⟨293, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 293 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0293
        ·
          by_cases h295 : i.val < 295
          ·
            have he : (⟨294, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 294 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0294
          ·
            have he : (⟨295, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 295 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0295
    ·
      by_cases h300 : i.val < 300
      ·
        by_cases h298 : i.val < 298
        ·
          by_cases h297 : i.val < 297
          ·
            have he : (⟨296, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 296 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0296
          ·
            have he : (⟨297, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 297 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0297
        ·
          by_cases h299 : i.val < 299
          ·
            have he : (⟨298, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 298 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0298
          ·
            have he : (⟨299, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 299 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0299
      ·
        by_cases h302 : i.val < 302
        ·
          by_cases h301 : i.val < 301
          ·
            have he : (⟨300, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 300 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0300
          ·
            have he : (⟨301, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 301 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0301
        ·
          by_cases h303 : i.val < 303
          ·
            have he : (⟨302, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 302 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0302
          ·
            have he : (⟨303, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 303 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0303
  ·
    by_cases h312 : i.val < 312
    ·
      by_cases h308 : i.val < 308
      ·
        by_cases h306 : i.val < 306
        ·
          by_cases h305 : i.val < 305
          ·
            have he : (⟨304, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 304 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0304
          ·
            have he : (⟨305, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 305 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0305
        ·
          by_cases h307 : i.val < 307
          ·
            have he : (⟨306, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 306 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0306
          ·
            have he : (⟨307, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 307 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0307
      ·
        by_cases h310 : i.val < 310
        ·
          by_cases h309 : i.val < 309
          ·
            have he : (⟨308, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 308 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0308
          ·
            have he : (⟨309, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 309 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0309
        ·
          by_cases h311 : i.val < 311
          ·
            have he : (⟨310, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 310 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0310
          ·
            have he : (⟨311, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 311 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0311
    ·
      by_cases h316 : i.val < 316
      ·
        by_cases h314 : i.val < 314
        ·
          by_cases h313 : i.val < 313
          ·
            have he : (⟨312, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 312 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0312
          ·
            have he : (⟨313, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 313 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0313
        ·
          by_cases h315 : i.val < 315
          ·
            have he : (⟨314, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 314 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0314
          ·
            have he : (⟨315, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 315 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0315
      ·
        by_cases h318 : i.val < 318
        ·
          by_cases h317 : i.val < 317
          ·
            have he : (⟨316, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 316 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0316
          ·
            have he : (⟨317, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 317 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0317
        ·
          by_cases h319 : i.val < 319
          ·
            have he : (⟨318, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 318 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0318
          ·
            have he : (⟨319, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 319 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0319

theorem bundle_64ff450e75_cofacetGroup0010 (i : Fin 1069)
    (hlo : 320 ≤ i.val) (hhi : i.val < 352) :
    bundle_64ff450e75_cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h336 : i.val < 336
  ·
    by_cases h328 : i.val < 328
    ·
      by_cases h324 : i.val < 324
      ·
        by_cases h322 : i.val < 322
        ·
          by_cases h321 : i.val < 321
          ·
            have he : (⟨320, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 320 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0320
          ·
            have he : (⟨321, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 321 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0321
        ·
          by_cases h323 : i.val < 323
          ·
            have he : (⟨322, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 322 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0322
          ·
            have he : (⟨323, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 323 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0323
      ·
        by_cases h326 : i.val < 326
        ·
          by_cases h325 : i.val < 325
          ·
            have he : (⟨324, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 324 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0324
          ·
            have he : (⟨325, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 325 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0325
        ·
          by_cases h327 : i.val < 327
          ·
            have he : (⟨326, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 326 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0326
          ·
            have he : (⟨327, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 327 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0327
    ·
      by_cases h332 : i.val < 332
      ·
        by_cases h330 : i.val < 330
        ·
          by_cases h329 : i.val < 329
          ·
            have he : (⟨328, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 328 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0328
          ·
            have he : (⟨329, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 329 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0329
        ·
          by_cases h331 : i.val < 331
          ·
            have he : (⟨330, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 330 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0330
          ·
            have he : (⟨331, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 331 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0331
      ·
        by_cases h334 : i.val < 334
        ·
          by_cases h333 : i.val < 333
          ·
            have he : (⟨332, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 332 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0332
          ·
            have he : (⟨333, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 333 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0333
        ·
          by_cases h335 : i.val < 335
          ·
            have he : (⟨334, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 334 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0334
          ·
            have he : (⟨335, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 335 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0335
  ·
    by_cases h344 : i.val < 344
    ·
      by_cases h340 : i.val < 340
      ·
        by_cases h338 : i.val < 338
        ·
          by_cases h337 : i.val < 337
          ·
            have he : (⟨336, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 336 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0336
          ·
            have he : (⟨337, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 337 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0337
        ·
          by_cases h339 : i.val < 339
          ·
            have he : (⟨338, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 338 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0338
          ·
            have he : (⟨339, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 339 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0339
      ·
        by_cases h342 : i.val < 342
        ·
          by_cases h341 : i.val < 341
          ·
            have he : (⟨340, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 340 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0340
          ·
            have he : (⟨341, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 341 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0341
        ·
          by_cases h343 : i.val < 343
          ·
            have he : (⟨342, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 342 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0342
          ·
            have he : (⟨343, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 343 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0343
    ·
      by_cases h348 : i.val < 348
      ·
        by_cases h346 : i.val < 346
        ·
          by_cases h345 : i.val < 345
          ·
            have he : (⟨344, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 344 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0344
          ·
            have he : (⟨345, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 345 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0345
        ·
          by_cases h347 : i.val < 347
          ·
            have he : (⟨346, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 346 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0346
          ·
            have he : (⟨347, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 347 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0347
      ·
        by_cases h350 : i.val < 350
        ·
          by_cases h349 : i.val < 349
          ·
            have he : (⟨348, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 348 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0348
          ·
            have he : (⟨349, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 349 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0349
        ·
          by_cases h351 : i.val < 351
          ·
            have he : (⟨350, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 350 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0350
          ·
            have he : (⟨351, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 351 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0351

theorem bundle_64ff450e75_cofacetGroup0011 (i : Fin 1069)
    (hlo : 352 ≤ i.val) (hhi : i.val < 384) :
    bundle_64ff450e75_cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h368 : i.val < 368
  ·
    by_cases h360 : i.val < 360
    ·
      by_cases h356 : i.val < 356
      ·
        by_cases h354 : i.val < 354
        ·
          by_cases h353 : i.val < 353
          ·
            have he : (⟨352, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 352 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0352
          ·
            have he : (⟨353, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 353 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0353
        ·
          by_cases h355 : i.val < 355
          ·
            have he : (⟨354, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 354 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0354
          ·
            have he : (⟨355, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 355 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0355
      ·
        by_cases h358 : i.val < 358
        ·
          by_cases h357 : i.val < 357
          ·
            have he : (⟨356, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 356 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0356
          ·
            have he : (⟨357, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 357 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0357
        ·
          by_cases h359 : i.val < 359
          ·
            have he : (⟨358, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 358 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0358
          ·
            have he : (⟨359, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 359 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0359
    ·
      by_cases h364 : i.val < 364
      ·
        by_cases h362 : i.val < 362
        ·
          by_cases h361 : i.val < 361
          ·
            have he : (⟨360, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 360 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0360
          ·
            have he : (⟨361, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 361 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0361
        ·
          by_cases h363 : i.val < 363
          ·
            have he : (⟨362, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 362 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0362
          ·
            have he : (⟨363, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 363 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0363
      ·
        by_cases h366 : i.val < 366
        ·
          by_cases h365 : i.val < 365
          ·
            have he : (⟨364, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 364 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0364
          ·
            have he : (⟨365, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 365 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0365
        ·
          by_cases h367 : i.val < 367
          ·
            have he : (⟨366, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 366 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0366
          ·
            have he : (⟨367, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 367 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0367
  ·
    by_cases h376 : i.val < 376
    ·
      by_cases h372 : i.val < 372
      ·
        by_cases h370 : i.val < 370
        ·
          by_cases h369 : i.val < 369
          ·
            have he : (⟨368, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 368 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0368
          ·
            have he : (⟨369, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 369 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0369
        ·
          by_cases h371 : i.val < 371
          ·
            have he : (⟨370, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 370 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0370
          ·
            have he : (⟨371, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 371 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0371
      ·
        by_cases h374 : i.val < 374
        ·
          by_cases h373 : i.val < 373
          ·
            have he : (⟨372, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 372 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0372
          ·
            have he : (⟨373, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 373 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0373
        ·
          by_cases h375 : i.val < 375
          ·
            have he : (⟨374, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 374 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0374
          ·
            have he : (⟨375, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 375 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0375
    ·
      by_cases h380 : i.val < 380
      ·
        by_cases h378 : i.val < 378
        ·
          by_cases h377 : i.val < 377
          ·
            have he : (⟨376, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 376 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0376
          ·
            have he : (⟨377, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 377 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0377
        ·
          by_cases h379 : i.val < 379
          ·
            have he : (⟨378, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 378 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0378
          ·
            have he : (⟨379, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 379 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0379
      ·
        by_cases h382 : i.val < 382
        ·
          by_cases h381 : i.val < 381
          ·
            have he : (⟨380, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 380 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0380
          ·
            have he : (⟨381, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 381 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0381
        ·
          by_cases h383 : i.val < 383
          ·
            have he : (⟨382, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 382 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0382
          ·
            have he : (⟨383, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 383 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0383

theorem bundle_64ff450e75_cofacetGroup0012 (i : Fin 1069)
    (hlo : 384 ≤ i.val) (hhi : i.val < 416) :
    bundle_64ff450e75_cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h400 : i.val < 400
  ·
    by_cases h392 : i.val < 392
    ·
      by_cases h388 : i.val < 388
      ·
        by_cases h386 : i.val < 386
        ·
          by_cases h385 : i.val < 385
          ·
            have he : (⟨384, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 384 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0384
          ·
            have he : (⟨385, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 385 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0385
        ·
          by_cases h387 : i.val < 387
          ·
            have he : (⟨386, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 386 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0386
          ·
            have he : (⟨387, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 387 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0387
      ·
        by_cases h390 : i.val < 390
        ·
          by_cases h389 : i.val < 389
          ·
            have he : (⟨388, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 388 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0388
          ·
            have he : (⟨389, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 389 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0389
        ·
          by_cases h391 : i.val < 391
          ·
            have he : (⟨390, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 390 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0390
          ·
            have he : (⟨391, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 391 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0391
    ·
      by_cases h396 : i.val < 396
      ·
        by_cases h394 : i.val < 394
        ·
          by_cases h393 : i.val < 393
          ·
            have he : (⟨392, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 392 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0392
          ·
            have he : (⟨393, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 393 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0393
        ·
          by_cases h395 : i.val < 395
          ·
            have he : (⟨394, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 394 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0394
          ·
            have he : (⟨395, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 395 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0395
      ·
        by_cases h398 : i.val < 398
        ·
          by_cases h397 : i.val < 397
          ·
            have he : (⟨396, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 396 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0396
          ·
            have he : (⟨397, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 397 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0397
        ·
          by_cases h399 : i.val < 399
          ·
            have he : (⟨398, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 398 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0398
          ·
            have he : (⟨399, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 399 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0399
  ·
    by_cases h408 : i.val < 408
    ·
      by_cases h404 : i.val < 404
      ·
        by_cases h402 : i.val < 402
        ·
          by_cases h401 : i.val < 401
          ·
            have he : (⟨400, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 400 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0400
          ·
            have he : (⟨401, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 401 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0401
        ·
          by_cases h403 : i.val < 403
          ·
            have he : (⟨402, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 402 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0402
          ·
            have he : (⟨403, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 403 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0403
      ·
        by_cases h406 : i.val < 406
        ·
          by_cases h405 : i.val < 405
          ·
            have he : (⟨404, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 404 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0404
          ·
            have he : (⟨405, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 405 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0405
        ·
          by_cases h407 : i.val < 407
          ·
            have he : (⟨406, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 406 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0406
          ·
            have he : (⟨407, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 407 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0407
    ·
      by_cases h412 : i.val < 412
      ·
        by_cases h410 : i.val < 410
        ·
          by_cases h409 : i.val < 409
          ·
            have he : (⟨408, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 408 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0408
          ·
            have he : (⟨409, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 409 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0409
        ·
          by_cases h411 : i.val < 411
          ·
            have he : (⟨410, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 410 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0410
          ·
            have he : (⟨411, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 411 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0411
      ·
        by_cases h414 : i.val < 414
        ·
          by_cases h413 : i.val < 413
          ·
            have he : (⟨412, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 412 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0412
          ·
            have he : (⟨413, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 413 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0413
        ·
          by_cases h415 : i.val < 415
          ·
            have he : (⟨414, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 414 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0414
          ·
            have he : (⟨415, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 415 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0415

theorem bundle_64ff450e75_cofacetGroup0013 (i : Fin 1069)
    (hlo : 416 ≤ i.val) (hhi : i.val < 448) :
    bundle_64ff450e75_cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h432 : i.val < 432
  ·
    by_cases h424 : i.val < 424
    ·
      by_cases h420 : i.val < 420
      ·
        by_cases h418 : i.val < 418
        ·
          by_cases h417 : i.val < 417
          ·
            have he : (⟨416, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 416 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0416
          ·
            have he : (⟨417, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 417 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0417
        ·
          by_cases h419 : i.val < 419
          ·
            have he : (⟨418, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 418 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0418
          ·
            have he : (⟨419, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 419 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0419
      ·
        by_cases h422 : i.val < 422
        ·
          by_cases h421 : i.val < 421
          ·
            have he : (⟨420, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 420 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0420
          ·
            have he : (⟨421, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 421 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0421
        ·
          by_cases h423 : i.val < 423
          ·
            have he : (⟨422, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 422 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0422
          ·
            have he : (⟨423, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 423 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0423
    ·
      by_cases h428 : i.val < 428
      ·
        by_cases h426 : i.val < 426
        ·
          by_cases h425 : i.val < 425
          ·
            have he : (⟨424, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 424 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0424
          ·
            have he : (⟨425, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 425 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0425
        ·
          by_cases h427 : i.val < 427
          ·
            have he : (⟨426, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 426 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0426
          ·
            have he : (⟨427, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 427 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0427
      ·
        by_cases h430 : i.val < 430
        ·
          by_cases h429 : i.val < 429
          ·
            have he : (⟨428, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 428 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0428
          ·
            have he : (⟨429, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 429 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0429
        ·
          by_cases h431 : i.val < 431
          ·
            have he : (⟨430, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 430 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0430
          ·
            have he : (⟨431, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 431 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0431
  ·
    by_cases h440 : i.val < 440
    ·
      by_cases h436 : i.val < 436
      ·
        by_cases h434 : i.val < 434
        ·
          by_cases h433 : i.val < 433
          ·
            have he : (⟨432, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 432 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0432
          ·
            have he : (⟨433, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 433 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0433
        ·
          by_cases h435 : i.val < 435
          ·
            have he : (⟨434, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 434 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0434
          ·
            have he : (⟨435, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 435 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0435
      ·
        by_cases h438 : i.val < 438
        ·
          by_cases h437 : i.val < 437
          ·
            have he : (⟨436, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 436 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0436
          ·
            have he : (⟨437, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 437 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0437
        ·
          by_cases h439 : i.val < 439
          ·
            have he : (⟨438, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 438 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0438
          ·
            have he : (⟨439, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 439 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0439
    ·
      by_cases h444 : i.val < 444
      ·
        by_cases h442 : i.val < 442
        ·
          by_cases h441 : i.val < 441
          ·
            have he : (⟨440, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 440 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0440
          ·
            have he : (⟨441, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 441 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0441
        ·
          by_cases h443 : i.val < 443
          ·
            have he : (⟨442, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 442 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0442
          ·
            have he : (⟨443, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 443 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0443
      ·
        by_cases h446 : i.val < 446
        ·
          by_cases h445 : i.val < 445
          ·
            have he : (⟨444, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 444 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0444
          ·
            have he : (⟨445, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 445 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0445
        ·
          by_cases h447 : i.val < 447
          ·
            have he : (⟨446, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 446 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0446
          ·
            have he : (⟨447, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 447 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0447

theorem bundle_64ff450e75_cofacetGroup0014 (i : Fin 1069)
    (hlo : 448 ≤ i.val) (hhi : i.val < 480) :
    bundle_64ff450e75_cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h464 : i.val < 464
  ·
    by_cases h456 : i.val < 456
    ·
      by_cases h452 : i.val < 452
      ·
        by_cases h450 : i.val < 450
        ·
          by_cases h449 : i.val < 449
          ·
            have he : (⟨448, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 448 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0448
          ·
            have he : (⟨449, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 449 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0449
        ·
          by_cases h451 : i.val < 451
          ·
            have he : (⟨450, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 450 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0450
          ·
            have he : (⟨451, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 451 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0451
      ·
        by_cases h454 : i.val < 454
        ·
          by_cases h453 : i.val < 453
          ·
            have he : (⟨452, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 452 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0452
          ·
            have he : (⟨453, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 453 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0453
        ·
          by_cases h455 : i.val < 455
          ·
            have he : (⟨454, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 454 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0454
          ·
            have he : (⟨455, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 455 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0455
    ·
      by_cases h460 : i.val < 460
      ·
        by_cases h458 : i.val < 458
        ·
          by_cases h457 : i.val < 457
          ·
            have he : (⟨456, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 456 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0456
          ·
            have he : (⟨457, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 457 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0457
        ·
          by_cases h459 : i.val < 459
          ·
            have he : (⟨458, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 458 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0458
          ·
            have he : (⟨459, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 459 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0459
      ·
        by_cases h462 : i.val < 462
        ·
          by_cases h461 : i.val < 461
          ·
            have he : (⟨460, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 460 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0460
          ·
            have he : (⟨461, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 461 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0461
        ·
          by_cases h463 : i.val < 463
          ·
            have he : (⟨462, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 462 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0462
          ·
            have he : (⟨463, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 463 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0463
  ·
    by_cases h472 : i.val < 472
    ·
      by_cases h468 : i.val < 468
      ·
        by_cases h466 : i.val < 466
        ·
          by_cases h465 : i.val < 465
          ·
            have he : (⟨464, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 464 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0464
          ·
            have he : (⟨465, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 465 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0465
        ·
          by_cases h467 : i.val < 467
          ·
            have he : (⟨466, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 466 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0466
          ·
            have he : (⟨467, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 467 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0467
      ·
        by_cases h470 : i.val < 470
        ·
          by_cases h469 : i.val < 469
          ·
            have he : (⟨468, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 468 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0468
          ·
            have he : (⟨469, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 469 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0469
        ·
          by_cases h471 : i.val < 471
          ·
            have he : (⟨470, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 470 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0470
          ·
            have he : (⟨471, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 471 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0471
    ·
      by_cases h476 : i.val < 476
      ·
        by_cases h474 : i.val < 474
        ·
          by_cases h473 : i.val < 473
          ·
            have he : (⟨472, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 472 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0472
          ·
            have he : (⟨473, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 473 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0473
        ·
          by_cases h475 : i.val < 475
          ·
            have he : (⟨474, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 474 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0474
          ·
            have he : (⟨475, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 475 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0475
      ·
        by_cases h478 : i.val < 478
        ·
          by_cases h477 : i.val < 477
          ·
            have he : (⟨476, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 476 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0476
          ·
            have he : (⟨477, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 477 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0477
        ·
          by_cases h479 : i.val < 479
          ·
            have he : (⟨478, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 478 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0478
          ·
            have he : (⟨479, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 479 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0479

theorem bundle_64ff450e75_cofacetGroup0015 (i : Fin 1069)
    (hlo : 480 ≤ i.val) (hhi : i.val < 512) :
    bundle_64ff450e75_cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h496 : i.val < 496
  ·
    by_cases h488 : i.val < 488
    ·
      by_cases h484 : i.val < 484
      ·
        by_cases h482 : i.val < 482
        ·
          by_cases h481 : i.val < 481
          ·
            have he : (⟨480, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 480 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0480
          ·
            have he : (⟨481, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 481 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0481
        ·
          by_cases h483 : i.val < 483
          ·
            have he : (⟨482, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 482 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0482
          ·
            have he : (⟨483, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 483 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0483
      ·
        by_cases h486 : i.val < 486
        ·
          by_cases h485 : i.val < 485
          ·
            have he : (⟨484, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 484 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0484
          ·
            have he : (⟨485, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 485 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0485
        ·
          by_cases h487 : i.val < 487
          ·
            have he : (⟨486, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 486 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0486
          ·
            have he : (⟨487, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 487 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0487
    ·
      by_cases h492 : i.val < 492
      ·
        by_cases h490 : i.val < 490
        ·
          by_cases h489 : i.val < 489
          ·
            have he : (⟨488, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 488 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0488
          ·
            have he : (⟨489, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 489 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0489
        ·
          by_cases h491 : i.val < 491
          ·
            have he : (⟨490, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 490 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0490
          ·
            have he : (⟨491, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 491 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0491
      ·
        by_cases h494 : i.val < 494
        ·
          by_cases h493 : i.val < 493
          ·
            have he : (⟨492, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 492 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0492
          ·
            have he : (⟨493, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 493 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0493
        ·
          by_cases h495 : i.val < 495
          ·
            have he : (⟨494, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 494 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0494
          ·
            have he : (⟨495, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 495 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0495
  ·
    by_cases h504 : i.val < 504
    ·
      by_cases h500 : i.val < 500
      ·
        by_cases h498 : i.val < 498
        ·
          by_cases h497 : i.val < 497
          ·
            have he : (⟨496, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 496 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0496
          ·
            have he : (⟨497, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 497 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0497
        ·
          by_cases h499 : i.val < 499
          ·
            have he : (⟨498, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 498 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0498
          ·
            have he : (⟨499, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 499 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0499
      ·
        by_cases h502 : i.val < 502
        ·
          by_cases h501 : i.val < 501
          ·
            have he : (⟨500, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 500 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0500
          ·
            have he : (⟨501, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 501 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0501
        ·
          by_cases h503 : i.val < 503
          ·
            have he : (⟨502, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 502 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0502
          ·
            have he : (⟨503, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 503 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0503
    ·
      by_cases h508 : i.val < 508
      ·
        by_cases h506 : i.val < 506
        ·
          by_cases h505 : i.val < 505
          ·
            have he : (⟨504, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 504 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0504
          ·
            have he : (⟨505, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 505 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0505
        ·
          by_cases h507 : i.val < 507
          ·
            have he : (⟨506, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 506 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0506
          ·
            have he : (⟨507, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 507 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0507
      ·
        by_cases h510 : i.val < 510
        ·
          by_cases h509 : i.val < 509
          ·
            have he : (⟨508, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 508 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0508
          ·
            have he : (⟨509, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 509 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0509
        ·
          by_cases h511 : i.val < 511
          ·
            have he : (⟨510, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 510 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0510
          ·
            have he : (⟨511, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 511 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0511

theorem bundle_64ff450e75_cofacetGroup0016 (i : Fin 1069)
    (hlo : 512 ≤ i.val) (hhi : i.val < 544) :
    bundle_64ff450e75_cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h528 : i.val < 528
  ·
    by_cases h520 : i.val < 520
    ·
      by_cases h516 : i.val < 516
      ·
        by_cases h514 : i.val < 514
        ·
          by_cases h513 : i.val < 513
          ·
            have he : (⟨512, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 512 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0512
          ·
            have he : (⟨513, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 513 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0513
        ·
          by_cases h515 : i.val < 515
          ·
            have he : (⟨514, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 514 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0514
          ·
            have he : (⟨515, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 515 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0515
      ·
        by_cases h518 : i.val < 518
        ·
          by_cases h517 : i.val < 517
          ·
            have he : (⟨516, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 516 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0516
          ·
            have he : (⟨517, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 517 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0517
        ·
          by_cases h519 : i.val < 519
          ·
            have he : (⟨518, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 518 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0518
          ·
            have he : (⟨519, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 519 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0519
    ·
      by_cases h524 : i.val < 524
      ·
        by_cases h522 : i.val < 522
        ·
          by_cases h521 : i.val < 521
          ·
            have he : (⟨520, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 520 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0520
          ·
            have he : (⟨521, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 521 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0521
        ·
          by_cases h523 : i.val < 523
          ·
            have he : (⟨522, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 522 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0522
          ·
            have he : (⟨523, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 523 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0523
      ·
        by_cases h526 : i.val < 526
        ·
          by_cases h525 : i.val < 525
          ·
            have he : (⟨524, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 524 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0524
          ·
            have he : (⟨525, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 525 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0525
        ·
          by_cases h527 : i.val < 527
          ·
            have he : (⟨526, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 526 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0526
          ·
            have he : (⟨527, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 527 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0527
  ·
    by_cases h536 : i.val < 536
    ·
      by_cases h532 : i.val < 532
      ·
        by_cases h530 : i.val < 530
        ·
          by_cases h529 : i.val < 529
          ·
            have he : (⟨528, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 528 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0528
          ·
            have he : (⟨529, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 529 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0529
        ·
          by_cases h531 : i.val < 531
          ·
            have he : (⟨530, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 530 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0530
          ·
            have he : (⟨531, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 531 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0531
      ·
        by_cases h534 : i.val < 534
        ·
          by_cases h533 : i.val < 533
          ·
            have he : (⟨532, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 532 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0532
          ·
            have he : (⟨533, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 533 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0533
        ·
          by_cases h535 : i.val < 535
          ·
            have he : (⟨534, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 534 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0534
          ·
            have he : (⟨535, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 535 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0535
    ·
      by_cases h540 : i.val < 540
      ·
        by_cases h538 : i.val < 538
        ·
          by_cases h537 : i.val < 537
          ·
            have he : (⟨536, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 536 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0536
          ·
            have he : (⟨537, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 537 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0537
        ·
          by_cases h539 : i.val < 539
          ·
            have he : (⟨538, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 538 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0538
          ·
            have he : (⟨539, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 539 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0539
      ·
        by_cases h542 : i.val < 542
        ·
          by_cases h541 : i.val < 541
          ·
            have he : (⟨540, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 540 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0540
          ·
            have he : (⟨541, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 541 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0541
        ·
          by_cases h543 : i.val < 543
          ·
            have he : (⟨542, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 542 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0542
          ·
            have he : (⟨543, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 543 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0543

theorem bundle_64ff450e75_cofacetGroup0017 (i : Fin 1069)
    (hlo : 544 ≤ i.val) (hhi : i.val < 576) :
    bundle_64ff450e75_cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h560 : i.val < 560
  ·
    by_cases h552 : i.val < 552
    ·
      by_cases h548 : i.val < 548
      ·
        by_cases h546 : i.val < 546
        ·
          by_cases h545 : i.val < 545
          ·
            have he : (⟨544, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 544 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0544
          ·
            have he : (⟨545, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 545 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0545
        ·
          by_cases h547 : i.val < 547
          ·
            have he : (⟨546, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 546 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0546
          ·
            have he : (⟨547, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 547 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0547
      ·
        by_cases h550 : i.val < 550
        ·
          by_cases h549 : i.val < 549
          ·
            have he : (⟨548, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 548 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0548
          ·
            have he : (⟨549, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 549 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0549
        ·
          by_cases h551 : i.val < 551
          ·
            have he : (⟨550, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 550 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0550
          ·
            have he : (⟨551, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 551 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0551
    ·
      by_cases h556 : i.val < 556
      ·
        by_cases h554 : i.val < 554
        ·
          by_cases h553 : i.val < 553
          ·
            have he : (⟨552, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 552 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0552
          ·
            have he : (⟨553, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 553 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0553
        ·
          by_cases h555 : i.val < 555
          ·
            have he : (⟨554, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 554 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0554
          ·
            have he : (⟨555, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 555 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0555
      ·
        by_cases h558 : i.val < 558
        ·
          by_cases h557 : i.val < 557
          ·
            have he : (⟨556, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 556 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0556
          ·
            have he : (⟨557, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 557 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0557
        ·
          by_cases h559 : i.val < 559
          ·
            have he : (⟨558, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 558 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0558
          ·
            have he : (⟨559, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 559 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0559
  ·
    by_cases h568 : i.val < 568
    ·
      by_cases h564 : i.val < 564
      ·
        by_cases h562 : i.val < 562
        ·
          by_cases h561 : i.val < 561
          ·
            have he : (⟨560, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 560 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0560
          ·
            have he : (⟨561, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 561 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0561
        ·
          by_cases h563 : i.val < 563
          ·
            have he : (⟨562, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 562 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0562
          ·
            have he : (⟨563, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 563 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0563
      ·
        by_cases h566 : i.val < 566
        ·
          by_cases h565 : i.val < 565
          ·
            have he : (⟨564, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 564 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0564
          ·
            have he : (⟨565, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 565 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0565
        ·
          by_cases h567 : i.val < 567
          ·
            have he : (⟨566, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 566 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0566
          ·
            have he : (⟨567, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 567 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0567
    ·
      by_cases h572 : i.val < 572
      ·
        by_cases h570 : i.val < 570
        ·
          by_cases h569 : i.val < 569
          ·
            have he : (⟨568, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 568 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0568
          ·
            have he : (⟨569, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 569 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0569
        ·
          by_cases h571 : i.val < 571
          ·
            have he : (⟨570, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 570 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0570
          ·
            have he : (⟨571, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 571 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0571
      ·
        by_cases h574 : i.val < 574
        ·
          by_cases h573 : i.val < 573
          ·
            have he : (⟨572, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 572 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0572
          ·
            have he : (⟨573, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 573 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0573
        ·
          by_cases h575 : i.val < 575
          ·
            have he : (⟨574, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 574 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0574
          ·
            have he : (⟨575, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 575 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0575

theorem bundle_64ff450e75_cofacetGroup0018 (i : Fin 1069)
    (hlo : 576 ≤ i.val) (hhi : i.val < 608) :
    bundle_64ff450e75_cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h592 : i.val < 592
  ·
    by_cases h584 : i.val < 584
    ·
      by_cases h580 : i.val < 580
      ·
        by_cases h578 : i.val < 578
        ·
          by_cases h577 : i.val < 577
          ·
            have he : (⟨576, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 576 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0576
          ·
            have he : (⟨577, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 577 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0577
        ·
          by_cases h579 : i.val < 579
          ·
            have he : (⟨578, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 578 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0578
          ·
            have he : (⟨579, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 579 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0579
      ·
        by_cases h582 : i.val < 582
        ·
          by_cases h581 : i.val < 581
          ·
            have he : (⟨580, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 580 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0580
          ·
            have he : (⟨581, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 581 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0581
        ·
          by_cases h583 : i.val < 583
          ·
            have he : (⟨582, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 582 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0582
          ·
            have he : (⟨583, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 583 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0583
    ·
      by_cases h588 : i.val < 588
      ·
        by_cases h586 : i.val < 586
        ·
          by_cases h585 : i.val < 585
          ·
            have he : (⟨584, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 584 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0584
          ·
            have he : (⟨585, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 585 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0585
        ·
          by_cases h587 : i.val < 587
          ·
            have he : (⟨586, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 586 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0586
          ·
            have he : (⟨587, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 587 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0587
      ·
        by_cases h590 : i.val < 590
        ·
          by_cases h589 : i.val < 589
          ·
            have he : (⟨588, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 588 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0588
          ·
            have he : (⟨589, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 589 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0589
        ·
          by_cases h591 : i.val < 591
          ·
            have he : (⟨590, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 590 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0590
          ·
            have he : (⟨591, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 591 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0591
  ·
    by_cases h600 : i.val < 600
    ·
      by_cases h596 : i.val < 596
      ·
        by_cases h594 : i.val < 594
        ·
          by_cases h593 : i.val < 593
          ·
            have he : (⟨592, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 592 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0592
          ·
            have he : (⟨593, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 593 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0593
        ·
          by_cases h595 : i.val < 595
          ·
            have he : (⟨594, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 594 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0594
          ·
            have he : (⟨595, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 595 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0595
      ·
        by_cases h598 : i.val < 598
        ·
          by_cases h597 : i.val < 597
          ·
            have he : (⟨596, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 596 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0596
          ·
            have he : (⟨597, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 597 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0597
        ·
          by_cases h599 : i.val < 599
          ·
            have he : (⟨598, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 598 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0598
          ·
            have he : (⟨599, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 599 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0599
    ·
      by_cases h604 : i.val < 604
      ·
        by_cases h602 : i.val < 602
        ·
          by_cases h601 : i.val < 601
          ·
            have he : (⟨600, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 600 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0600
          ·
            have he : (⟨601, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 601 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0601
        ·
          by_cases h603 : i.val < 603
          ·
            have he : (⟨602, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 602 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0602
          ·
            have he : (⟨603, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 603 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0603
      ·
        by_cases h606 : i.val < 606
        ·
          by_cases h605 : i.val < 605
          ·
            have he : (⟨604, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 604 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0604
          ·
            have he : (⟨605, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 605 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0605
        ·
          by_cases h607 : i.val < 607
          ·
            have he : (⟨606, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 606 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0606
          ·
            have he : (⟨607, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 607 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0607

theorem bundle_64ff450e75_cofacetGroup0019 (i : Fin 1069)
    (hlo : 608 ≤ i.val) (hhi : i.val < 640) :
    bundle_64ff450e75_cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h624 : i.val < 624
  ·
    by_cases h616 : i.val < 616
    ·
      by_cases h612 : i.val < 612
      ·
        by_cases h610 : i.val < 610
        ·
          by_cases h609 : i.val < 609
          ·
            have he : (⟨608, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 608 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0608
          ·
            have he : (⟨609, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 609 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0609
        ·
          by_cases h611 : i.val < 611
          ·
            have he : (⟨610, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 610 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0610
          ·
            have he : (⟨611, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 611 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0611
      ·
        by_cases h614 : i.val < 614
        ·
          by_cases h613 : i.val < 613
          ·
            have he : (⟨612, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 612 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0612
          ·
            have he : (⟨613, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 613 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0613
        ·
          by_cases h615 : i.val < 615
          ·
            have he : (⟨614, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 614 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0614
          ·
            have he : (⟨615, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 615 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0615
    ·
      by_cases h620 : i.val < 620
      ·
        by_cases h618 : i.val < 618
        ·
          by_cases h617 : i.val < 617
          ·
            have he : (⟨616, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 616 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0616
          ·
            have he : (⟨617, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 617 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0617
        ·
          by_cases h619 : i.val < 619
          ·
            have he : (⟨618, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 618 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0618
          ·
            have he : (⟨619, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 619 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0619
      ·
        by_cases h622 : i.val < 622
        ·
          by_cases h621 : i.val < 621
          ·
            have he : (⟨620, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 620 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0620
          ·
            have he : (⟨621, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 621 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0621
        ·
          by_cases h623 : i.val < 623
          ·
            have he : (⟨622, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 622 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0622
          ·
            have he : (⟨623, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 623 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0623
  ·
    by_cases h632 : i.val < 632
    ·
      by_cases h628 : i.val < 628
      ·
        by_cases h626 : i.val < 626
        ·
          by_cases h625 : i.val < 625
          ·
            have he : (⟨624, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 624 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0624
          ·
            have he : (⟨625, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 625 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0625
        ·
          by_cases h627 : i.val < 627
          ·
            have he : (⟨626, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 626 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0626
          ·
            have he : (⟨627, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 627 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0627
      ·
        by_cases h630 : i.val < 630
        ·
          by_cases h629 : i.val < 629
          ·
            have he : (⟨628, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 628 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0628
          ·
            have he : (⟨629, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 629 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0629
        ·
          by_cases h631 : i.val < 631
          ·
            have he : (⟨630, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 630 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0630
          ·
            have he : (⟨631, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 631 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0631
    ·
      by_cases h636 : i.val < 636
      ·
        by_cases h634 : i.val < 634
        ·
          by_cases h633 : i.val < 633
          ·
            have he : (⟨632, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 632 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0632
          ·
            have he : (⟨633, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 633 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0633
        ·
          by_cases h635 : i.val < 635
          ·
            have he : (⟨634, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 634 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0634
          ·
            have he : (⟨635, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 635 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0635
      ·
        by_cases h638 : i.val < 638
        ·
          by_cases h637 : i.val < 637
          ·
            have he : (⟨636, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 636 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0636
          ·
            have he : (⟨637, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 637 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0637
        ·
          by_cases h639 : i.val < 639
          ·
            have he : (⟨638, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 638 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0638
          ·
            have he : (⟨639, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 639 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0639

theorem bundle_64ff450e75_cofacetGroup0020 (i : Fin 1069)
    (hlo : 640 ≤ i.val) (hhi : i.val < 672) :
    bundle_64ff450e75_cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h656 : i.val < 656
  ·
    by_cases h648 : i.val < 648
    ·
      by_cases h644 : i.val < 644
      ·
        by_cases h642 : i.val < 642
        ·
          by_cases h641 : i.val < 641
          ·
            have he : (⟨640, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 640 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0640
          ·
            have he : (⟨641, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 641 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0641
        ·
          by_cases h643 : i.val < 643
          ·
            have he : (⟨642, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 642 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0642
          ·
            have he : (⟨643, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 643 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0643
      ·
        by_cases h646 : i.val < 646
        ·
          by_cases h645 : i.val < 645
          ·
            have he : (⟨644, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 644 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0644
          ·
            have he : (⟨645, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 645 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0645
        ·
          by_cases h647 : i.val < 647
          ·
            have he : (⟨646, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 646 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0646
          ·
            have he : (⟨647, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 647 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0647
    ·
      by_cases h652 : i.val < 652
      ·
        by_cases h650 : i.val < 650
        ·
          by_cases h649 : i.val < 649
          ·
            have he : (⟨648, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 648 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0648
          ·
            have he : (⟨649, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 649 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0649
        ·
          by_cases h651 : i.val < 651
          ·
            have he : (⟨650, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 650 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0650
          ·
            have he : (⟨651, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 651 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0651
      ·
        by_cases h654 : i.val < 654
        ·
          by_cases h653 : i.val < 653
          ·
            have he : (⟨652, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 652 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0652
          ·
            have he : (⟨653, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 653 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0653
        ·
          by_cases h655 : i.val < 655
          ·
            have he : (⟨654, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 654 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0654
          ·
            have he : (⟨655, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 655 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0655
  ·
    by_cases h664 : i.val < 664
    ·
      by_cases h660 : i.val < 660
      ·
        by_cases h658 : i.val < 658
        ·
          by_cases h657 : i.val < 657
          ·
            have he : (⟨656, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 656 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0656
          ·
            have he : (⟨657, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 657 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0657
        ·
          by_cases h659 : i.val < 659
          ·
            have he : (⟨658, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 658 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0658
          ·
            have he : (⟨659, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 659 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0659
      ·
        by_cases h662 : i.val < 662
        ·
          by_cases h661 : i.val < 661
          ·
            have he : (⟨660, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 660 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0660
          ·
            have he : (⟨661, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 661 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0661
        ·
          by_cases h663 : i.val < 663
          ·
            have he : (⟨662, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 662 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0662
          ·
            have he : (⟨663, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 663 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0663
    ·
      by_cases h668 : i.val < 668
      ·
        by_cases h666 : i.val < 666
        ·
          by_cases h665 : i.val < 665
          ·
            have he : (⟨664, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 664 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0664
          ·
            have he : (⟨665, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 665 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0665
        ·
          by_cases h667 : i.val < 667
          ·
            have he : (⟨666, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 666 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0666
          ·
            have he : (⟨667, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 667 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0667
      ·
        by_cases h670 : i.val < 670
        ·
          by_cases h669 : i.val < 669
          ·
            have he : (⟨668, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 668 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0668
          ·
            have he : (⟨669, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 669 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0669
        ·
          by_cases h671 : i.val < 671
          ·
            have he : (⟨670, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 670 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0670
          ·
            have he : (⟨671, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 671 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0671

theorem bundle_64ff450e75_cofacetGroup0021 (i : Fin 1069)
    (hlo : 672 ≤ i.val) (hhi : i.val < 704) :
    bundle_64ff450e75_cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h688 : i.val < 688
  ·
    by_cases h680 : i.val < 680
    ·
      by_cases h676 : i.val < 676
      ·
        by_cases h674 : i.val < 674
        ·
          by_cases h673 : i.val < 673
          ·
            have he : (⟨672, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 672 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0672
          ·
            have he : (⟨673, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 673 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0673
        ·
          by_cases h675 : i.val < 675
          ·
            have he : (⟨674, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 674 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0674
          ·
            have he : (⟨675, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 675 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0675
      ·
        by_cases h678 : i.val < 678
        ·
          by_cases h677 : i.val < 677
          ·
            have he : (⟨676, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 676 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0676
          ·
            have he : (⟨677, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 677 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0677
        ·
          by_cases h679 : i.val < 679
          ·
            have he : (⟨678, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 678 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0678
          ·
            have he : (⟨679, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 679 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0679
    ·
      by_cases h684 : i.val < 684
      ·
        by_cases h682 : i.val < 682
        ·
          by_cases h681 : i.val < 681
          ·
            have he : (⟨680, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 680 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0680
          ·
            have he : (⟨681, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 681 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0681
        ·
          by_cases h683 : i.val < 683
          ·
            have he : (⟨682, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 682 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0682
          ·
            have he : (⟨683, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 683 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0683
      ·
        by_cases h686 : i.val < 686
        ·
          by_cases h685 : i.val < 685
          ·
            have he : (⟨684, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 684 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0684
          ·
            have he : (⟨685, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 685 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0685
        ·
          by_cases h687 : i.val < 687
          ·
            have he : (⟨686, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 686 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0686
          ·
            have he : (⟨687, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 687 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0687
  ·
    by_cases h696 : i.val < 696
    ·
      by_cases h692 : i.val < 692
      ·
        by_cases h690 : i.val < 690
        ·
          by_cases h689 : i.val < 689
          ·
            have he : (⟨688, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 688 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0688
          ·
            have he : (⟨689, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 689 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0689
        ·
          by_cases h691 : i.val < 691
          ·
            have he : (⟨690, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 690 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0690
          ·
            have he : (⟨691, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 691 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0691
      ·
        by_cases h694 : i.val < 694
        ·
          by_cases h693 : i.val < 693
          ·
            have he : (⟨692, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 692 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0692
          ·
            have he : (⟨693, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 693 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0693
        ·
          by_cases h695 : i.val < 695
          ·
            have he : (⟨694, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 694 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0694
          ·
            have he : (⟨695, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 695 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0695
    ·
      by_cases h700 : i.val < 700
      ·
        by_cases h698 : i.val < 698
        ·
          by_cases h697 : i.val < 697
          ·
            have he : (⟨696, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 696 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0696
          ·
            have he : (⟨697, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 697 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0697
        ·
          by_cases h699 : i.val < 699
          ·
            have he : (⟨698, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 698 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0698
          ·
            have he : (⟨699, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 699 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0699
      ·
        by_cases h702 : i.val < 702
        ·
          by_cases h701 : i.val < 701
          ·
            have he : (⟨700, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 700 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0700
          ·
            have he : (⟨701, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 701 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0701
        ·
          by_cases h703 : i.val < 703
          ·
            have he : (⟨702, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 702 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0702
          ·
            have he : (⟨703, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 703 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0703

theorem bundle_64ff450e75_cofacetGroup0022 (i : Fin 1069)
    (hlo : 704 ≤ i.val) (hhi : i.val < 736) :
    bundle_64ff450e75_cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h720 : i.val < 720
  ·
    by_cases h712 : i.val < 712
    ·
      by_cases h708 : i.val < 708
      ·
        by_cases h706 : i.val < 706
        ·
          by_cases h705 : i.val < 705
          ·
            have he : (⟨704, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 704 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0704
          ·
            have he : (⟨705, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 705 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0705
        ·
          by_cases h707 : i.val < 707
          ·
            have he : (⟨706, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 706 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0706
          ·
            have he : (⟨707, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 707 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0707
      ·
        by_cases h710 : i.val < 710
        ·
          by_cases h709 : i.val < 709
          ·
            have he : (⟨708, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 708 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0708
          ·
            have he : (⟨709, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 709 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0709
        ·
          by_cases h711 : i.val < 711
          ·
            have he : (⟨710, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 710 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0710
          ·
            have he : (⟨711, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 711 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0711
    ·
      by_cases h716 : i.val < 716
      ·
        by_cases h714 : i.val < 714
        ·
          by_cases h713 : i.val < 713
          ·
            have he : (⟨712, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 712 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0712
          ·
            have he : (⟨713, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 713 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0713
        ·
          by_cases h715 : i.val < 715
          ·
            have he : (⟨714, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 714 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0714
          ·
            have he : (⟨715, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 715 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0715
      ·
        by_cases h718 : i.val < 718
        ·
          by_cases h717 : i.val < 717
          ·
            have he : (⟨716, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 716 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0716
          ·
            have he : (⟨717, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 717 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0717
        ·
          by_cases h719 : i.val < 719
          ·
            have he : (⟨718, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 718 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0718
          ·
            have he : (⟨719, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 719 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0719
  ·
    by_cases h728 : i.val < 728
    ·
      by_cases h724 : i.val < 724
      ·
        by_cases h722 : i.val < 722
        ·
          by_cases h721 : i.val < 721
          ·
            have he : (⟨720, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 720 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0720
          ·
            have he : (⟨721, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 721 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0721
        ·
          by_cases h723 : i.val < 723
          ·
            have he : (⟨722, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 722 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0722
          ·
            have he : (⟨723, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 723 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0723
      ·
        by_cases h726 : i.val < 726
        ·
          by_cases h725 : i.val < 725
          ·
            have he : (⟨724, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 724 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0724
          ·
            have he : (⟨725, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 725 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0725
        ·
          by_cases h727 : i.val < 727
          ·
            have he : (⟨726, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 726 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0726
          ·
            have he : (⟨727, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 727 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0727
    ·
      by_cases h732 : i.val < 732
      ·
        by_cases h730 : i.val < 730
        ·
          by_cases h729 : i.val < 729
          ·
            have he : (⟨728, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 728 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0728
          ·
            have he : (⟨729, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 729 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0729
        ·
          by_cases h731 : i.val < 731
          ·
            have he : (⟨730, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 730 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0730
          ·
            have he : (⟨731, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 731 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0731
      ·
        by_cases h734 : i.val < 734
        ·
          by_cases h733 : i.val < 733
          ·
            have he : (⟨732, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 732 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0732
          ·
            have he : (⟨733, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 733 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0733
        ·
          by_cases h735 : i.val < 735
          ·
            have he : (⟨734, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 734 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0734
          ·
            have he : (⟨735, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 735 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0735

theorem bundle_64ff450e75_cofacetGroup0023 (i : Fin 1069)
    (hlo : 736 ≤ i.val) (hhi : i.val < 768) :
    bundle_64ff450e75_cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h752 : i.val < 752
  ·
    by_cases h744 : i.val < 744
    ·
      by_cases h740 : i.val < 740
      ·
        by_cases h738 : i.val < 738
        ·
          by_cases h737 : i.val < 737
          ·
            have he : (⟨736, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 736 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0736
          ·
            have he : (⟨737, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 737 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0737
        ·
          by_cases h739 : i.val < 739
          ·
            have he : (⟨738, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 738 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0738
          ·
            have he : (⟨739, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 739 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0739
      ·
        by_cases h742 : i.val < 742
        ·
          by_cases h741 : i.val < 741
          ·
            have he : (⟨740, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 740 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0740
          ·
            have he : (⟨741, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 741 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0741
        ·
          by_cases h743 : i.val < 743
          ·
            have he : (⟨742, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 742 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0742
          ·
            have he : (⟨743, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 743 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0743
    ·
      by_cases h748 : i.val < 748
      ·
        by_cases h746 : i.val < 746
        ·
          by_cases h745 : i.val < 745
          ·
            have he : (⟨744, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 744 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0744
          ·
            have he : (⟨745, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 745 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0745
        ·
          by_cases h747 : i.val < 747
          ·
            have he : (⟨746, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 746 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0746
          ·
            have he : (⟨747, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 747 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0747
      ·
        by_cases h750 : i.val < 750
        ·
          by_cases h749 : i.val < 749
          ·
            have he : (⟨748, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 748 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0748
          ·
            have he : (⟨749, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 749 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0749
        ·
          by_cases h751 : i.val < 751
          ·
            have he : (⟨750, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 750 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0750
          ·
            have he : (⟨751, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 751 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0751
  ·
    by_cases h760 : i.val < 760
    ·
      by_cases h756 : i.val < 756
      ·
        by_cases h754 : i.val < 754
        ·
          by_cases h753 : i.val < 753
          ·
            have he : (⟨752, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 752 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0752
          ·
            have he : (⟨753, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 753 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0753
        ·
          by_cases h755 : i.val < 755
          ·
            have he : (⟨754, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 754 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0754
          ·
            have he : (⟨755, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 755 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0755
      ·
        by_cases h758 : i.val < 758
        ·
          by_cases h757 : i.val < 757
          ·
            have he : (⟨756, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 756 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0756
          ·
            have he : (⟨757, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 757 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0757
        ·
          by_cases h759 : i.val < 759
          ·
            have he : (⟨758, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 758 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0758
          ·
            have he : (⟨759, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 759 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0759
    ·
      by_cases h764 : i.val < 764
      ·
        by_cases h762 : i.val < 762
        ·
          by_cases h761 : i.val < 761
          ·
            have he : (⟨760, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 760 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0760
          ·
            have he : (⟨761, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 761 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0761
        ·
          by_cases h763 : i.val < 763
          ·
            have he : (⟨762, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 762 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0762
          ·
            have he : (⟨763, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 763 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0763
      ·
        by_cases h766 : i.val < 766
        ·
          by_cases h765 : i.val < 765
          ·
            have he : (⟨764, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 764 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0764
          ·
            have he : (⟨765, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 765 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0765
        ·
          by_cases h767 : i.val < 767
          ·
            have he : (⟨766, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 766 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0766
          ·
            have he : (⟨767, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 767 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0767

theorem bundle_64ff450e75_cofacetGroup0024 (i : Fin 1069)
    (hlo : 768 ≤ i.val) (hhi : i.val < 800) :
    bundle_64ff450e75_cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h784 : i.val < 784
  ·
    by_cases h776 : i.val < 776
    ·
      by_cases h772 : i.val < 772
      ·
        by_cases h770 : i.val < 770
        ·
          by_cases h769 : i.val < 769
          ·
            have he : (⟨768, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 768 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0768
          ·
            have he : (⟨769, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 769 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0769
        ·
          by_cases h771 : i.val < 771
          ·
            have he : (⟨770, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 770 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0770
          ·
            have he : (⟨771, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 771 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0771
      ·
        by_cases h774 : i.val < 774
        ·
          by_cases h773 : i.val < 773
          ·
            have he : (⟨772, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 772 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0772
          ·
            have he : (⟨773, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 773 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0773
        ·
          by_cases h775 : i.val < 775
          ·
            have he : (⟨774, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 774 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0774
          ·
            have he : (⟨775, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 775 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0775
    ·
      by_cases h780 : i.val < 780
      ·
        by_cases h778 : i.val < 778
        ·
          by_cases h777 : i.val < 777
          ·
            have he : (⟨776, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 776 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0776
          ·
            have he : (⟨777, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 777 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0777
        ·
          by_cases h779 : i.val < 779
          ·
            have he : (⟨778, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 778 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0778
          ·
            have he : (⟨779, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 779 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0779
      ·
        by_cases h782 : i.val < 782
        ·
          by_cases h781 : i.val < 781
          ·
            have he : (⟨780, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 780 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0780
          ·
            have he : (⟨781, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 781 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0781
        ·
          by_cases h783 : i.val < 783
          ·
            have he : (⟨782, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 782 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0782
          ·
            have he : (⟨783, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 783 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0783
  ·
    by_cases h792 : i.val < 792
    ·
      by_cases h788 : i.val < 788
      ·
        by_cases h786 : i.val < 786
        ·
          by_cases h785 : i.val < 785
          ·
            have he : (⟨784, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 784 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0784
          ·
            have he : (⟨785, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 785 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0785
        ·
          by_cases h787 : i.val < 787
          ·
            have he : (⟨786, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 786 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0786
          ·
            have he : (⟨787, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 787 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0787
      ·
        by_cases h790 : i.val < 790
        ·
          by_cases h789 : i.val < 789
          ·
            have he : (⟨788, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 788 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0788
          ·
            have he : (⟨789, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 789 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0789
        ·
          by_cases h791 : i.val < 791
          ·
            have he : (⟨790, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 790 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0790
          ·
            have he : (⟨791, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 791 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0791
    ·
      by_cases h796 : i.val < 796
      ·
        by_cases h794 : i.val < 794
        ·
          by_cases h793 : i.val < 793
          ·
            have he : (⟨792, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 792 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0792
          ·
            have he : (⟨793, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 793 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0793
        ·
          by_cases h795 : i.val < 795
          ·
            have he : (⟨794, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 794 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0794
          ·
            have he : (⟨795, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 795 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0795
      ·
        by_cases h798 : i.val < 798
        ·
          by_cases h797 : i.val < 797
          ·
            have he : (⟨796, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 796 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0796
          ·
            have he : (⟨797, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 797 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0797
        ·
          by_cases h799 : i.val < 799
          ·
            have he : (⟨798, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 798 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0798
          ·
            have he : (⟨799, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 799 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0799

theorem bundle_64ff450e75_cofacetGroup0025 (i : Fin 1069)
    (hlo : 800 ≤ i.val) (hhi : i.val < 832) :
    bundle_64ff450e75_cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h816 : i.val < 816
  ·
    by_cases h808 : i.val < 808
    ·
      by_cases h804 : i.val < 804
      ·
        by_cases h802 : i.val < 802
        ·
          by_cases h801 : i.val < 801
          ·
            have he : (⟨800, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 800 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0800
          ·
            have he : (⟨801, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 801 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0801
        ·
          by_cases h803 : i.val < 803
          ·
            have he : (⟨802, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 802 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0802
          ·
            have he : (⟨803, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 803 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0803
      ·
        by_cases h806 : i.val < 806
        ·
          by_cases h805 : i.val < 805
          ·
            have he : (⟨804, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 804 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0804
          ·
            have he : (⟨805, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 805 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0805
        ·
          by_cases h807 : i.val < 807
          ·
            have he : (⟨806, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 806 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0806
          ·
            have he : (⟨807, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 807 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0807
    ·
      by_cases h812 : i.val < 812
      ·
        by_cases h810 : i.val < 810
        ·
          by_cases h809 : i.val < 809
          ·
            have he : (⟨808, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 808 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0808
          ·
            have he : (⟨809, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 809 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0809
        ·
          by_cases h811 : i.val < 811
          ·
            have he : (⟨810, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 810 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0810
          ·
            have he : (⟨811, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 811 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0811
      ·
        by_cases h814 : i.val < 814
        ·
          by_cases h813 : i.val < 813
          ·
            have he : (⟨812, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 812 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0812
          ·
            have he : (⟨813, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 813 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0813
        ·
          by_cases h815 : i.val < 815
          ·
            have he : (⟨814, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 814 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0814
          ·
            have he : (⟨815, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 815 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0815
  ·
    by_cases h824 : i.val < 824
    ·
      by_cases h820 : i.val < 820
      ·
        by_cases h818 : i.val < 818
        ·
          by_cases h817 : i.val < 817
          ·
            have he : (⟨816, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 816 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0816
          ·
            have he : (⟨817, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 817 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0817
        ·
          by_cases h819 : i.val < 819
          ·
            have he : (⟨818, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 818 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0818
          ·
            have he : (⟨819, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 819 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0819
      ·
        by_cases h822 : i.val < 822
        ·
          by_cases h821 : i.val < 821
          ·
            have he : (⟨820, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 820 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0820
          ·
            have he : (⟨821, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 821 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0821
        ·
          by_cases h823 : i.val < 823
          ·
            have he : (⟨822, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 822 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0822
          ·
            have he : (⟨823, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 823 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0823
    ·
      by_cases h828 : i.val < 828
      ·
        by_cases h826 : i.val < 826
        ·
          by_cases h825 : i.val < 825
          ·
            have he : (⟨824, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 824 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0824
          ·
            have he : (⟨825, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 825 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0825
        ·
          by_cases h827 : i.val < 827
          ·
            have he : (⟨826, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 826 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0826
          ·
            have he : (⟨827, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 827 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0827
      ·
        by_cases h830 : i.val < 830
        ·
          by_cases h829 : i.val < 829
          ·
            have he : (⟨828, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 828 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0828
          ·
            have he : (⟨829, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 829 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0829
        ·
          by_cases h831 : i.val < 831
          ·
            have he : (⟨830, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 830 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0830
          ·
            have he : (⟨831, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 831 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0831

theorem bundle_64ff450e75_cofacetGroup0026 (i : Fin 1069)
    (hlo : 832 ≤ i.val) (hhi : i.val < 864) :
    bundle_64ff450e75_cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h848 : i.val < 848
  ·
    by_cases h840 : i.val < 840
    ·
      by_cases h836 : i.val < 836
      ·
        by_cases h834 : i.val < 834
        ·
          by_cases h833 : i.val < 833
          ·
            have he : (⟨832, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 832 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0832
          ·
            have he : (⟨833, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 833 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0833
        ·
          by_cases h835 : i.val < 835
          ·
            have he : (⟨834, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 834 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0834
          ·
            have he : (⟨835, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 835 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0835
      ·
        by_cases h838 : i.val < 838
        ·
          by_cases h837 : i.val < 837
          ·
            have he : (⟨836, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 836 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0836
          ·
            have he : (⟨837, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 837 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0837
        ·
          by_cases h839 : i.val < 839
          ·
            have he : (⟨838, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 838 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0838
          ·
            have he : (⟨839, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 839 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0839
    ·
      by_cases h844 : i.val < 844
      ·
        by_cases h842 : i.val < 842
        ·
          by_cases h841 : i.val < 841
          ·
            have he : (⟨840, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 840 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0840
          ·
            have he : (⟨841, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 841 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0841
        ·
          by_cases h843 : i.val < 843
          ·
            have he : (⟨842, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 842 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0842
          ·
            have he : (⟨843, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 843 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0843
      ·
        by_cases h846 : i.val < 846
        ·
          by_cases h845 : i.val < 845
          ·
            have he : (⟨844, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 844 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0844
          ·
            have he : (⟨845, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 845 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0845
        ·
          by_cases h847 : i.val < 847
          ·
            have he : (⟨846, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 846 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0846
          ·
            have he : (⟨847, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 847 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0847
  ·
    by_cases h856 : i.val < 856
    ·
      by_cases h852 : i.val < 852
      ·
        by_cases h850 : i.val < 850
        ·
          by_cases h849 : i.val < 849
          ·
            have he : (⟨848, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 848 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0848
          ·
            have he : (⟨849, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 849 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0849
        ·
          by_cases h851 : i.val < 851
          ·
            have he : (⟨850, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 850 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0850
          ·
            have he : (⟨851, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 851 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0851
      ·
        by_cases h854 : i.val < 854
        ·
          by_cases h853 : i.val < 853
          ·
            have he : (⟨852, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 852 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0852
          ·
            have he : (⟨853, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 853 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0853
        ·
          by_cases h855 : i.val < 855
          ·
            have he : (⟨854, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 854 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0854
          ·
            have he : (⟨855, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 855 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0855
    ·
      by_cases h860 : i.val < 860
      ·
        by_cases h858 : i.val < 858
        ·
          by_cases h857 : i.val < 857
          ·
            have he : (⟨856, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 856 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0856
          ·
            have he : (⟨857, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 857 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0857
        ·
          by_cases h859 : i.val < 859
          ·
            have he : (⟨858, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 858 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0858
          ·
            have he : (⟨859, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 859 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0859
      ·
        by_cases h862 : i.val < 862
        ·
          by_cases h861 : i.val < 861
          ·
            have he : (⟨860, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 860 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0860
          ·
            have he : (⟨861, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 861 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0861
        ·
          by_cases h863 : i.val < 863
          ·
            have he : (⟨862, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 862 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0862
          ·
            have he : (⟨863, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 863 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0863

theorem bundle_64ff450e75_cofacetGroup0027 (i : Fin 1069)
    (hlo : 864 ≤ i.val) (hhi : i.val < 896) :
    bundle_64ff450e75_cubeCofacetCertificate i := by
  have hi_bound := i.isLt
  by_cases h880 : i.val < 880
  ·
    by_cases h872 : i.val < 872
    ·
      by_cases h868 : i.val < 868
      ·
        by_cases h866 : i.val < 866
        ·
          by_cases h865 : i.val < 865
          ·
            have he : (⟨864, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 864 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0864
          ·
            have he : (⟨865, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 865 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0865
        ·
          by_cases h867 : i.val < 867
          ·
            have he : (⟨866, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 866 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0866
          ·
            have he : (⟨867, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 867 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0867
      ·
        by_cases h870 : i.val < 870
        ·
          by_cases h869 : i.val < 869
          ·
            have he : (⟨868, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 868 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0868
          ·
            have he : (⟨869, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 869 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0869
        ·
          by_cases h871 : i.val < 871
          ·
            have he : (⟨870, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 870 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0870
          ·
            have he : (⟨871, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 871 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0871
    ·
      by_cases h876 : i.val < 876
      ·
        by_cases h874 : i.val < 874
        ·
          by_cases h873 : i.val < 873
          ·
            have he : (⟨872, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 872 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0872
          ·
            have he : (⟨873, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 873 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0873
        ·
          by_cases h875 : i.val < 875
          ·
            have he : (⟨874, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 874 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0874
          ·
            have he : (⟨875, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 875 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0875
      ·
        by_cases h878 : i.val < 878
        ·
          by_cases h877 : i.val < 877
          ·
            have he : (⟨876, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 876 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0876
          ·
            have he : (⟨877, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 877 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0877
        ·
          by_cases h879 : i.val < 879
          ·
            have he : (⟨878, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 878 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0878
          ·
            have he : (⟨879, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 879 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0879
  ·
    by_cases h888 : i.val < 888
    ·
      by_cases h884 : i.val < 884
      ·
        by_cases h882 : i.val < 882
        ·
          by_cases h881 : i.val < 881
          ·
            have he : (⟨880, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 880 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0880
          ·
            have he : (⟨881, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 881 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0881
        ·
          by_cases h883 : i.val < 883
          ·
            have he : (⟨882, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 882 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0882
          ·
            have he : (⟨883, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 883 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0883
      ·
        by_cases h886 : i.val < 886
        ·
          by_cases h885 : i.val < 885
          ·
            have he : (⟨884, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 884 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0884
          ·
            have he : (⟨885, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 885 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0885
        ·
          by_cases h887 : i.val < 887
          ·
            have he : (⟨886, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 886 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0886
          ·
            have he : (⟨887, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 887 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0887
    ·
      by_cases h892 : i.val < 892
      ·
        by_cases h890 : i.val < 890
        ·
          by_cases h889 : i.val < 889
          ·
            have he : (⟨888, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 888 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0888
          ·
            have he : (⟨889, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 889 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0889
        ·
          by_cases h891 : i.val < 891
          ·
            have he : (⟨890, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 890 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0890
          ·
            have he : (⟨891, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 891 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0891
      ·
        by_cases h894 : i.val < 894
        ·
          by_cases h893 : i.val < 893
          ·
            have he : (⟨892, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 892 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0892
          ·
            have he : (⟨893, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 893 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0893
        ·
          by_cases h895 : i.val < 895
          ·
            have he : (⟨894, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 894 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0894
          ·
            have he : (⟨895, by decide⟩ : Fin 1069) = i := by
              apply Fin.ext
              change 895 = i.val
              omega
            simpa only [he] using bundle_64ff450e75_cofacet0895

end CubicalIndecomposability
end VerificationSource001



end -- global noncomputable section
end -- global public section
