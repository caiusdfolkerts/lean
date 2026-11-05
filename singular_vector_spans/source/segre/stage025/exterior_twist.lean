module
import all Mathlib.AlgebraicGeometry.Modules.Sheaf
import all Mathlib.RingTheory.OreLocalization.Basic
import all Mathlib.Algebra.MonoidAlgebra.Defs
public import SegreVerified.Stage001
public import SegreVerified.Stage002
public import SegreVerified.Stage003
public import SegreVerified.Stage004
public import SegreVerified.Stage005
public import SegreVerified.Stage006
public import SegreVerified.Stage007
public import SegreVerified.Stage008
public import SegreVerified.Stage009
public import SegreVerified.Stage010
public import SegreVerified.Stage011
public import SegreVerified.Stage012
public import SegreVerified.Stage013
public import SegreVerified.Stage014
public import SegreVerified.Stage015
public import SegreVerified.Stage016
public import SegreVerified.Stage017
public import SegreVerified.Stage018
public import SegreVerified.Stage019
public import SegreVerified.Stage020
public import SegreVerified.Stage021
public import SegreVerified.Stage022
public import SegreVerified.Stage023
public import SegreVerified.Stage024

public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Tactic.Push
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fin.Basic
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.RingTheory.Polynomial.ContentIdeal
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Sym.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Finset.NatAntidiagonal
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.List.FinRange
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.LinearAlgebra.PiTensorProduct.Finite
public import Mathlib.LinearAlgebra.TensorPower.Symmetric
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Data.Sym.Card
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.FilteredAlgebra.Basic
public import Mathlib.Algebra.DirectSum.Internal
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.Data.Sym.NatCard
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.LinearCombination
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.AffineSpace.Combination
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.Algebra.Ring.Invertible
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Algebra.BigOperators.Option
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Finset.Option
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Fin.Basic
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Tactic.Linarith
public import Mathlib.Order.Sym2
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Data.Fintype.Fin
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.Algebra.MonoidAlgebra.Grading
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps
public import Mathlib.RingTheory.GradedAlgebra.TensorProduct
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.RingTheory.GradedAlgebra.Radical
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Data.Nat.Find
public import Mathlib.Topology.QuasiSeparated
public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Order.SuccPred.Fin
public import Mathlib.Order.SuccPred.IntervalSucc
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.AlgebraicTopology.SimplicialObject.Homotopy
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.ExtraDegeneracy
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Sites.IsSheafFor
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Homology.ShortComplex.Preadditive
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Kernels
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.Algebra.Category.Grp.Biproducts
public import Mathlib.CategoryTheory.Limits.Lattice
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.CategoryTheory.Localization.Monoidal.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import Mathlib.CategoryTheory.Localization.Monoidal.Braided
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.OfCommRing
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Abelian.Subobject
public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import Mathlib.Basic.Finite.Sum
public import Mathlib.CategoryTheory.Monoidal.Limits.Cokernels
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
public import Mathlib.CategoryTheory.Localization.Monoidal.Functor
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.CategoryTheory.Sites.LocalProperties
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Functor.TwoSquare
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.Algebra.Homology.CommSq
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.Sites.CoversTop.Over
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.FiveLemma
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
public import Mathlib.Algebra.Homology.ComplexShapeSigns
public import Mathlib.Algebra.Homology.Embedding.Basic
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.Embedding.HomEquiv
public import Mathlib.Algebra.Homology.TotalComplexSymmetry
public import Mathlib.CategoryTheory.GradedObject.Monoidal
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Topology.Sheaves.Skyscraper
public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.RingTheory.LocalProperties.FinitePresentation
public import Mathlib.RingTheory.Finiteness.Finsupp
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Topology.Sheaves.Over
public import Mathlib.Topology.Category.TopCat.Opens
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.BifunctorHomotopy
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Opposite
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.Order.Fin.Tuple
public import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.QuotSMulTop
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.KrullDimension
public import Mathlib.Order.KrullDimension
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.Topology.LocallyClosed
public import Mathlib.Algebra.Ring.Subgroup
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.LinearAlgebra.Finsupp.Span
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.Data.ENat.Monoid
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Depth.Basic
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.Regular.Category
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Regular.LinearMap
public import Mathlib.RingTheory.IntegralClosure.GoingDown
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.Artinian.Algebra
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Square
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.Algebra.Module.SpanRank
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Finiteness.Nakayama
public import Mathlib.Algebra.Ring.Int.Field
public import Mathlib.RingTheory.Ideal.NatInt
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Support
public import Mathlib.RingTheory.Regular.Flat
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.HasGoingUp
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.Localization.InvSubmonoid
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.Polynomial.RationalRoot
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.Ideal.UFD
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.LinearAlgebra.TensorProduct.Decomposition
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import Mathlib.RingTheory.RootsOfUnity.Minpoly
public import Mathlib.Algebra.Order.Antidiag.Finsupp
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.Logic.Function.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.ExteriorPower.WedgePairing
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Logic.Equiv.Set
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.MvPolynomial.Localization
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.Logic.Equiv.Option
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import Mathlib.RingTheory.LocalProperties.Exactness
public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Product
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Tactic.Abel
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.RingTheory.Ideal.Lattice
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.Multilinear.Curry
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.Data.Finset.Interval
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Dual
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.LinearAlgebra.Projectivization.Subspace
public import Lean.Util.CollectAxioms
import all Lean.Util.CollectAxioms
public import Lean.Util.FoldConsts
public import Lean.Util.Sorry
public import Lean.Elab.Command
public import Lean.PrettyPrinter

public import SegreVerified.Stage025.ProjectiveCech
public import SegreVerified.Stage025.ProjectiveSections
public import SegreVerified.Stage025.Euler
public import SegreVerified.Stage025.ExteriorKernel

set_option Elab.async false
set_option linter.all false

#eval do
  let toolchain ← IO.FS.readFile "lean-toolchain"
  let manifest ← IO.FS.readFile "lake-manifest.json"
  IO.println ("SEGRE_PUBLIC_ENVIRONMENT_BEGIN\n" ++ Lean.versionString ++ "\n" ++
    Lean.githash ++ "\n" ++ toolchain.trimAscii.toString ++ "\n" ++ manifest ++
    "\nSEGRE_PUBLIC_ENVIRONMENT_END")

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  unless env.header.trustLevel == 0 do
    throwError "The retained source check requires kernel trust level zero"
  let imported := exportedAxiomsExt.getState (asyncMode := .mainOnly) env
  let rows := CollectAxioms.runM (env.setExporting false) do
    #[``Nat.add_comm, ``Nat.zero_add].mapM fun name =>
      return (name, ← CollectAxioms.collectAndGet imported.find? name)
  for (name, axioms) in rows do
    unless (env.checked.get.find? name).isSome do throwError "Unchecked smoke target: {name}"
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unapproved shared-collector smoke axiom: {ax}"
  logInfo "SEGRE_SHARED_COLLECTOR_READY"


set_option Elab.async false
set_option maxErrors 0
set_option maxRecDepth 2048
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section ProbeLayer391



/-!
# Singular-vector geometry and all-format spanning theorems

The named sections preserve the original proof stages and local scopes.
-/

@[expose] public section

-- Emit compilation progress immediately while checking this large unit.
set_option stderrAsMessages false
-- Style linting is separate from elaboration, kernel checking, and the axiom audit.
set_option linter.all false
noncomputable section
set_option autoImplicit false


section SegreProjectiveCohomology

run_cmd do
  let out ← IO.getStderr
  out.putStrLn "SEGRE_STAGE SegreProjectiveCohomology"
  out.flush

/-!
# Projective exterior cohomology and the full Koszul gap

The named sections preserve the original proof stages and local scopes.
-/


section SegreExteriorTwist

run_cmd do
  let out ← IO.getStderr
  out.putStrLn "SEGRE_STAGE SegreExteriorTwist"
  out.flush

/-!
# Exterior powers of the full negative-twist coordinate sheaf

The comparison with copies of O(-p) is given by the actual coordinate minors.
Each minor is an alternating multilinear map on sections; the determinant's
Leibniz formula shows that it has the correct homogeneous twist. Local
trivializations identify these minors with the full exterior basis coordinates.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 600000



attribute [local instance] MvPolynomial.gradedAlgebra

namespace PaperVerification.Segre.ExteriorTwist

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open EulerSheaf EulerSections
open ProjectiveSpectrum.TwistingSheaf
open scoped BigOperators

universe u
variable {I K : Type u} [Fintype I] [DecidableEq I] [LinearOrder I] [Field K]

local notation "𝒜" => MvPolynomial.homogeneousSubmodule I K
local notation "X" => Proj 𝒜

/-- All localization-valued functions on an open, without a homogeneous restriction. -/
abbrev AmbientSections (U : (X).Opens) := ∀ x : U, Localizations 𝒜 x.val

/-- Structure-sheaf functions act by their literal values in the localizations. -/
def structureValueHom (U : (X).Opens) : Γ(X,U) →+* AmbientSections (I := I) (K := K) U where
  toFun a x := (a.val x).val
  map_one' := by funext x; exact HomogeneousLocalization.val_one
  map_mul' a b := by funext x; exact HomogeneousLocalization.val_mul _ _
  map_zero' := by funext x; exact HomogeneousLocalization.val_zero
  map_add' a b := by funext x; exact HomogeneousLocalization.val_add _ _

instance ambientSectionsAlgebra (U : (X).Opens) :
    Algebra Γ(X,U) (AmbientSections (I := I) (K := K) U) :=
  (structureValueHom U).toAlgebra

/-- The actual value map is linear over the full ring of functions on the open. -/
def sectionValueLinear (t : ℤ) (U : (X).Opens) :
    Γ(Proj.twistingSheaf 𝒜 t,U) →ₗ[Γ(X,U)] AmbientSections (I := I) (K := K) U where
  toFun s := s.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A product of p genuine sections of O(-1) has the actual twist -p. -/
theorem product_negative_twist {J : Type*} (s : Finset J) (U : (X).Opens)
    (f : J → AmbientSections (I := I) (K := K) U)
    (hf : ∀ j∈s, (isLocallyFraction 𝒜 (-1)).pred (f j)) :
    (isLocallyFraction 𝒜 (-(s.card : ℤ))).pred (∏ j∈s, f j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      change (isLocallyFraction 𝒜 0).pred (1 : AmbientSections (I := I) (K := K) U)
      have h : (fun x : U => (1 : Γ(X,U)).val x |>.val) =
          (1 : AmbientSections (I := I) (K := K) U) := by
        funext x
        exact HomogeneousLocalization.val_one
      exact h ▸ isLocallyFraction_val (1 : Γ(X,U))
  | @insert j s hj ih =>
      rw [Finset.card_insert_of_notMem hj,Finset.prod_insert hj]
      have hp := isLocallyFraction_mul (hf j (Finset.mem_insert_self _ _))
        (ih (fun a ha => hf a (Finset.mem_insert_of_mem ha)))
      have hdeg : (-1 : ℤ) + -(s.card : ℤ) = -((s.card + 1 : ℕ) : ℤ) := by omega
      simpa only [hdeg] using hp

/-- The row of a selected p×p coordinate minor, as a linear map of full section modules. -/
def minorRows (p : ℕ) (s : Set.powersetCard I p) (U : (X).Opens) :
    Γ(eulerSource (I := I) (K := K),U) →ₗ[Γ(X,U)] (Fin p → AmbientSections (I := I) (K := K) U) :=
  LinearMap.pi (fun j => (sectionValueLinear (-1) U).comp
    ((LinearMap.proj (Set.powersetCard.ofFinEmbEquiv.symm s j)).comp
      (productSectionsEquiv (fun _ : I => Proj.twistingSheaf 𝒜 (-1)) U).toLinearMap))

/-- The literal coordinate determinant, as an alternating map into all localization functions. -/
def rawMinor (p : ℕ) (s : Set.powersetCard I p) (U : (X).Opens) :
    Γ(eulerSource (I := I) (K := K),U) [⋀^Fin p]→ₗ[Γ(X,U)]
      AmbientSections (I := I) (K := K) U :=
  ({ toMultilinearMap := (Matrix.detRowAlternating (n := Fin p)
        (R := AmbientSections (I := I) (K := K) U)).toMultilinearMap.restrictScalars Γ(X,U)
     map_eq_zero_of_eq' := fun v i j h hij =>
       (Matrix.detRowAlternating (n := Fin p)
         (R := AmbientSections (I := I) (K := K) U)).map_eq_zero_of_eq v h hij } :
      (Fin p → AmbientSections (I := I) (K := K) U) [⋀^Fin p]→ₗ[Γ(X,U)]
        AmbientSections (I := I) (K := K) U).compLinearMap (minorRows p s U)

@[simp] theorem rawMinor_apply (p : ℕ) (s : Set.powersetCard I p) (U : (X).Opens)
    (v : Fin p → Γ(eulerSource (I := I) (K := K),U)) :
    rawMinor p s U v=Matrix.det (fun i j =>
      (productSectionsEquiv (fun _ : I => Proj.twistingSheaf 𝒜 (-1)) U (v i)
        (Set.powersetCard.ofFinEmbEquiv.symm s j)).val) := rfl

/-- Every coordinate minor has exactly the required twist, including p=0. -/
theorem rawMinor_homogeneous (p : ℕ) (s : Set.powersetCard I p) (U : (X).Opens)
    (v : Fin p → Γ(eulerSource (I := I) (K := K),U)) :
    (isLocallyFraction 𝒜 (-(p : ℤ))).pred (rawMinor p s U v) := by
  erw [rawMinor_apply,Matrix.det_apply]
  apply (sectionsAddSubgroup 𝒜 (-(p : ℤ)) U).sum_mem
  intro σ _
  change (Equiv.Perm.sign σ) •
      (∏ j, (productSectionsEquiv (fun _ : I => Proj.twistingSheaf 𝒜 (-1)) U (v (σ j))
        (Set.powersetCard.ofFinEmbEquiv.symm s j)).val) ∈ sectionsAddSubgroup 𝒜 (-(p : ℤ)) U
  rw [Units.smul_def]
  apply AddSubgroup.zsmul_mem
  apply (mem_sectionsAddSubgroup_iff _).mpr
  simpa only [Finset.card_univ,Fintype.card_fin] using
    product_negative_twist (Finset.univ : Finset (Fin p)) U _ (fun j _ =>
      (productSectionsEquiv (fun _ : I => Proj.twistingSheaf 𝒜 (-1)) U (v (σ j))
        (Set.powersetCard.ofFinEmbEquiv.symm s j)).property)

/-- The actual minor section as an alternating map into O(-p). -/
def minorAlternating (p : ℕ) (s : Set.powersetCard I p) (U : (X).Opens) :
    Γ(eulerSource (I := I) (K := K),U) [⋀^Fin p]→ₗ[Γ(X,U)]
      Γ(Proj.twistingSheaf 𝒜 (-(p : ℤ)),U) where
  toFun v := ⟨rawMinor p s U v,rawMinor_homogeneous p s U v⟩
  map_update_add' v i a b := Subtype.ext ((rawMinor p s U).map_update_add v i a b)
  map_update_smul' v i r a := Subtype.ext ((rawMinor p s U).map_update_smul v i r a)
  map_eq_zero_of_eq' v i j h hij := Subtype.ext ((rawMinor p s U).map_eq_zero_of_eq v h hij)

/-- All actual minor sections together, on the entire exterior power of the section module. -/
def minorLinear (p : ℕ) (U : (X).Opens) :
    (⋀[Γ(X,U)]^p Γ(eulerSource (I := I) (K := K),U)) →ₗ[Γ(X,U)]
      Γ((∏ᶜ fun _ : Set.powersetCard I p => Proj.twistingSheaf 𝒜 (-(p : ℤ))),U) :=
  (productSectionsEquiv (fun _ : Set.powersetCard I p => Proj.twistingSheaf 𝒜 (-(p : ℤ))) U).symm.toLinearMap.comp
      (LinearMap.pi (fun s => exteriorPower.alternatingMapLinearEquiv (minorAlternating p s U)))

@[simp] theorem minorLinear_ιMulti (p : ℕ) (U : (X).Opens)
    (v : Fin p → Γ(eulerSource (I := I) (K := K),U)) (s : Set.powersetCard I p) :
    productSectionsEquiv (fun _ : Set.powersetCard I p => Proj.twistingSheaf 𝒜 (-(p : ℤ))) U
      (minorLinear p U (exteriorPower.ιMulti Γ(X,U) p v)) s=minorAlternating p s U v := by
  simp only [minorLinear,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,
    LinearMap.pi_apply,exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]

/-- The complete coordinate-chart trivialization of the actual Euler source sections. -/
def chartSourceEquiv (j : I) (U : (X).Opens) (hU : U≤ProjectiveCech.coordinateOpen (K := K) j) :
    (I → Γ(X,U)) ≃ₗ[Γ(X,U)] Γ(eulerSource (I := I) (K := K),U) :=
  (LinearEquiv.piCongrRight (fun _ : I => Proj.twistingSheaf.chartSectionsLinearEquiv (-1)
    (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X (R := K) j) U hU)).trans
      (productSectionsEquiv (fun _ : I => Proj.twistingSheaf 𝒜 (-1)) U).symm

@[simp] theorem chartSourceEquiv_component (j : I) (U : (X).Opens)
    (hU : U≤ProjectiveCech.coordinateOpen (K := K) j) (v : I → Γ(X,U)) (i : I) :
    productSectionsEquiv (fun _ : I => Proj.twistingSheaf 𝒜 (-1)) U
      (chartSourceEquiv j U hU v) i=
      Proj.twistingSheaf.chartSectionsLinearEquiv (-1) (MvPolynomial.X j)
        (MvPolynomial.isHomogeneous_X (R := K) j) U hU (v i) := by
  exact congrFun
    ((productSectionsEquiv (fun _ : I => Proj.twistingSheaf 𝒜 (-1)) U).apply_symm_apply
      (fun i => Proj.twistingSheaf.chartSectionsLinearEquiv (-1) (MvPolynomial.X j)
        (MvPolynomial.isHomogeneous_X (R := K) j) U hU (v i))) i

/-- The pth tensor power of the reciprocal generator is exactly the standard generator of O(-p). -/
theorem chartGenerator_negative_power (j : I) (U : (X).Opens)
    (hU : U≤ProjectiveCech.coordinateOpen (K := K) j) (p : ℕ) (x : U) :
    (Proj.twistingSheaf.chartGenerator (-(p : ℤ)) (MvPolynomial.X j)
      (MvPolynomial.isHomogeneous_X (R := K) j) U hU).val x=
      ((Proj.twistingSheaf.chartGenerator (-1) (MvPolynomial.X j)
        (MvPolynomial.isHomogeneous_X (R := K) j) U hU).val x)^p := by
  induction p with
  | zero =>
      simp only [Nat.cast_zero, neg_zero, Proj.twistingSheaf.chartGenerator_apply,
        Int.toNat_zero, pow_zero]
      change (Localization.mk (1 : MvPolynomial I K) 1 : Localizations 𝒜 x.val) = 1
      rw [Localization.mk_one_eq_algebraMap,map_one]
  | succ p ih =>
      have h := Proj.twistingSheaf.mul_chartGenerator_apply (-(p : ℤ)) (MvPolynomial.X j)
        (MvPolynomial.isHomogeneous_X (R := K) j) U hU (-1) x
      change (Proj.twistingSheaf.chartGenerator (-1) (MvPolynomial.X j)
          (MvPolynomial.isHomogeneous_X (R := K) j) U hU).val x *
        (Proj.twistingSheaf.chartGenerator (-(p : ℤ)) (MvPolynomial.X j)
          (MvPolynomial.isHomogeneous_X (R := K) j) U hU).val x=
        (Proj.twistingSheaf.chartGenerator (-1+ -(p : ℤ)) (MvPolynomial.X j)
          (MvPolynomial.isHomogeneous_X (R := K) j) U hU).val x at h
      rw [ih] at h
      have hn : -((p + 1 : ℕ) : ℤ) = -1 + -(p : ℤ) := by omega
      erw [hn]
      simpa only [pow_succ'] using h.symm

/-- In chart coordinates, the actual minor section is the determinant times the genuine
standard generator of O(-p). -/
theorem minorAlternating_on_chart (p : ℕ) (s : Set.powersetCard I p) (j : I) (U : (X).Opens)
    (hU : U≤ProjectiveCech.coordinateOpen (K := K) j) (v : Fin p → I → Γ(X,U)) :
    minorAlternating p s U (fun a => chartSourceEquiv j U hU (v a))=
      Proj.twistingSheaf.chartSectionsLinearEquiv (-(p : ℤ)) (MvPolynomial.X j)
        (MvPolynomial.isHomogeneous_X (R := K) j) U hU
          (Matrix.det (fun a b => v a (Set.powersetCard.ofFinEmbEquiv.symm s b))) := by
  apply Proj.twistingSheaf.ext
  intro x
  let σ : Γ(X,U) →+* Localizations 𝒜 x.val := (Pi.evalRingHom _ x).comp (structureValueHom U)
  let g := (Proj.twistingSheaf.chartGenerator (-1) (MvPolynomial.X j)
    (MvPolynomial.isHomogeneous_X (R := K) j) U hU).val x
  change (Pi.evalRingHom _ x) (Matrix.det (fun a b =>
      (productSectionsEquiv (fun _ : I => Proj.twistingSheaf 𝒜 (-1)) U
        (chartSourceEquiv j U hU (v a)) (Set.powersetCard.ofFinEmbEquiv.symm s b)).val))=_
  erw [RingHom.map_det]
  simp only [RingHom.mapMatrix_apply, Matrix.map, Pi.evalRingHom_apply,
    chartSourceEquiv_component, Proj.twistingSheaf.chartSectionsLinearEquiv_apply_apply]
  change Matrix.det (fun a b => σ (v a (Set.powersetCard.ofFinEmbEquiv.symm s b))*g)=
    σ (Matrix.det (fun a b => v a (Set.powersetCard.ofFinEmbEquiv.symm s b))) *
      (Proj.twistingSheaf.chartGenerator (-(p : ℤ)) (MvPolynomial.X j)
        (MvPolynomial.isHomogeneous_X (R := K) j) U hU).val x
  have hm : (fun a b => σ (v a (Set.powersetCard.ofFinEmbEquiv.symm s b))*g)=
      g • (fun a b => σ (v a (Set.powersetCard.ofFinEmbEquiv.symm s b))) := by
    ext a b
    exact mul_comm _ _
  have hd : Matrix.det (fun a b => σ (v a (Set.powersetCard.ofFinEmbEquiv.symm s b))) =
      σ (Matrix.det (fun a b => v a (Set.powersetCard.ofFinEmbEquiv.symm s b))) := by
    calc
      Matrix.det (fun a b => σ (v a (Set.powersetCard.ofFinEmbEquiv.symm s b))) =
          (σ.mapMatrix (fun a b => v a (Set.powersetCard.ofFinEmbEquiv.symm s b))).det := by
        apply congrArg Matrix.det
        ext a b
        rfl
      _ = σ (Matrix.det (fun a b => v a (Set.powersetCard.ofFinEmbEquiv.symm s b))) :=
        (σ.map_det _).symm
  erw [hm, Matrix.det_smul, Fintype.card_fin, hd, chartGenerator_negative_power]
  exact mul_comm _ _

/-- The full standard trivialization of the target copies of O(-p). -/
def chartTargetEquiv (p : ℕ) (j : I) (U : (X).Opens)
    (hU : U≤ProjectiveCech.coordinateOpen (K := K) j) :
    (Set.powersetCard I p → Γ(X,U)) ≃ₗ[Γ(X,U)]
      Γ((∏ᶜ fun _ : Set.powersetCard I p => Proj.twistingSheaf 𝒜 (-(p : ℤ))),U) :=
  (LinearEquiv.piCongrRight (fun _ : Set.powersetCard I p =>
    Proj.twistingSheaf.chartSectionsLinearEquiv (-(p : ℤ)) (MvPolynomial.X j)
      (MvPolynomial.isHomogeneous_X (R := K) j) U hU)).trans
        (productSectionsEquiv (fun _ : Set.powersetCard I p => Proj.twistingSheaf 𝒜 (-(p : ℤ))) U).symm

/-- The target chart trivialization has the expected component in every minor coordinate. -/
@[simp] theorem chartTargetEquiv_component (p : ℕ) (j : I) (U : (X).Opens)
    (hU : U ≤ ProjectiveCech.coordinateOpen (K := K) j)
    (v : Set.powersetCard I p → Γ(X,U)) (s : Set.powersetCard I p) :
    productSectionsEquiv (fun _ : Set.powersetCard I p => Proj.twistingSheaf 𝒜 (-(p : ℤ))) U
      (chartTargetEquiv p j U hU v) s =
      Proj.twistingSheaf.chartSectionsLinearEquiv (-(p : ℤ)) (MvPolynomial.X j)
        (MvPolynomial.isHomogeneous_X (R := K) j) U hU (v s) := by
  exact congrFun
    ((productSectionsEquiv
      (fun _ : Set.powersetCard I p => Proj.twistingSheaf 𝒜 (-(p : ℤ))) U).apply_symm_apply
      (fun s => Proj.twistingSheaf.chartSectionsLinearEquiv (-(p : ℤ)) (MvPolynomial.X j)
        (MvPolynomial.isHomogeneous_X (R := K) j) U hU (v s))) s

/-- The induced exterior-power chart equivalence. -/
def chartExteriorEquiv (p : ℕ) (j : I) (U : (X).Opens)
    (hU : U≤ProjectiveCech.coordinateOpen (K := K) j) :
    (⋀[Γ(X,U)]^p (I → Γ(X,U))) ≃ₗ[Γ(X,U)]
      ⋀[Γ(X,U)]^p Γ(eulerSource (I := I) (K := K),U) :=
  LinearEquiv.ofBijective (exteriorPower.map p (chartSourceEquiv j U hU).toLinearMap)
    (exteriorPower.map_bijective (chartSourceEquiv j U hU).bijective)

/-- On the whole exterior module, coordinate minors are precisely the standard exterior-basis
coordinates followed by the target chart trivialization. -/
theorem minorLinear_on_chart (p : ℕ) (j : I) (U : (X).Opens)
    (hU : U≤ProjectiveCech.coordinateOpen (K := K) j) :
    (minorLinear p U).comp (chartExteriorEquiv p j U hU).toLinearMap=
      (chartTargetEquiv p j U hU).toLinearMap.comp ((Pi.basisFun Γ(X,U) I).exteriorPower p).equivFun.toLinearMap := by
  apply exteriorPower.linearMap_ext
  ext v
  apply (productSectionsEquiv (fun _ : Set.powersetCard I p => Proj.twistingSheaf 𝒜 (-(p : ℤ))) U).injective
  funext s
  change productSectionsEquiv (fun _ : Set.powersetCard I p => Proj.twistingSheaf 𝒜 (-(p : ℤ))) U
      (minorLinear p U (exteriorPower.map p (chartSourceEquiv j U hU).toLinearMap
        (exteriorPower.ιMulti Γ(X,U) p v))) s=_
  erw [exteriorPower.map_apply_ιMulti,minorLinear_ιMulti]
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, chartTargetEquiv_component]
  change minorAlternating p s U (fun a => chartSourceEquiv j U hU (v a))=
    Proj.twistingSheaf.chartSectionsLinearEquiv (-(p : ℤ)) (MvPolynomial.X j)
      (MvPolynomial.isHomogeneous_X (R := K) j) U hU
        (((Pi.basisFun Γ(X,U) I).exteriorPower p).equivFun (exteriorPower.ιMulti Γ(X,U) p v) s)
  erw [Module.Basis.equivFun_apply,exteriorPower.basis_repr_apply,
    exteriorPower.ιMultiDual_apply_ιMulti]
  simp only [Module.Basis.coord_apply,Pi.basisFun_repr,Matrix.of_apply]
  exact minorAlternating_on_chart p s j U hU v

/-- All coordinate minors give a bijection on every chart subopen, in all exterior degrees. -/
theorem minorLinear_bijective_on_chart (p : ℕ) (j : I) (U : (X).Opens)
    (hU : U≤ProjectiveCech.coordinateOpen (K := K) j) :
    Function.Bijective (minorLinear (I := I) (K := K) p U) := by
  let e := chartExteriorEquiv p j U hU
  have hb : Function.Bijective ((minorLinear p U).comp e.toLinearMap) := by
    rw [minorLinear_on_chart]
    exact (chartTargetEquiv p j U hU).bijective.comp
      ((Pi.basisFun Γ(X,U) I).exteriorPower p).equivFun.bijective
  constructor
  · intro x y h
    obtain ⟨x,rfl⟩ := e.surjective x
    obtain ⟨y,rfl⟩ := e.surjective y
    exact congrArg e (hb.1 h)
  · intro y
    obtain ⟨x,hx⟩ := hb.2 y
    exact ⟨e x,hx⟩

/-- The actual value of a minor section is the determinant of the actual local values. -/
theorem minorAlternating_apply_point (p : ℕ) (s : Set.powersetCard I p) (U : (X).Opens)
    (v : Fin p → Γ(eulerSource (I := I) (K := K),U)) (x : U) :
    (minorAlternating p s U v).val x=Matrix.det (fun a b =>
      (productSectionsEquiv (fun _ : I => Proj.twistingSheaf 𝒜 (-1)) U (v a)
        (Set.powersetCard.ofFinEmbEquiv.symm s b)).val x) := by
  change (Pi.evalRingHom (fun x : U => Localizations 𝒜 x.val) x)
    (Matrix.det (fun a b =>
      (productSectionsEquiv (fun _ : I => Proj.twistingSheaf 𝒜 (-1)) U (v a)
        (Set.powersetCard.ofFinEmbEquiv.symm s b)).val)) = _
  exact (Pi.evalRingHom (fun x : U => Localizations 𝒜 x.val) x).map_det _

/-- The actual minor sections commute with restrictions to all smaller opens. -/
theorem minorAlternating_res (p : ℕ) (s : Set.powersetCard I p) {U V : (X).Opens}
    (i : V ⟶ U) (v : Fin p → Γ(eulerSource (I := I) (K := K),U)) :
    (Proj.twistingSheaf 𝒜 (-(p : ℤ))).presheaf.map i.op (minorAlternating p s U v)=
      minorAlternating p s V (fun a => (eulerSource (I := I) (K := K)).presheaf.map i.op (v a)) := by
  apply Proj.twistingSheaf.ext
  intro x
  change (minorAlternating p s U v).val ⟨x.val,i.le x.property⟩=_
  erw [minorAlternating_apply_point,minorAlternating_apply_point]
  apply congrArg Matrix.det
  funext a b
  erw [productSectionsEquiv_res]
  rfl

/-- The complete minor map commutes with restriction on every pure exterior generator. -/
theorem minorLinear_res_ιMulti (p : ℕ) {U V : (X).Opens} (i : V ⟶ U)
    (v : Fin p → Γ(eulerSource (I := I) (K := K),U)) :
    (∏ᶜ fun _ : Set.powersetCard I p => Proj.twistingSheaf 𝒜 (-(p : ℤ))).presheaf.map i.op
        (minorLinear p U (exteriorPower.ιMulti Γ(X,U) p v)) =
      minorLinear p V (exteriorPower.ιMulti Γ(X,V) p
        (fun a => (eulerSource (I := I) (K := K)).presheaf.map i.op (v a))) := by
  apply (productSectionsEquiv
    (fun _ : Set.powersetCard I p => Proj.twistingSheaf 𝒜 (-(p : ℤ))) V).injective
  funext s
  erw [productSectionsEquiv_res, minorLinear_ιMulti, minorLinear_ιMulti]
  exact minorAlternating_res p s i v

/-- Naturality of maps from a sectionwise exterior power can be checked on its
pure exterior generators. Keeping the presheaves abstract avoids unfolding any
chosen limit presentation of their section modules. -/
theorem exteriorHom_naturality {C : Type u} [SmallCategory C]
    {R : Cᵒᵖ ⥤ CommRingCat.{u}} {M N : PresheafOfModulesOfCommRing.{u} R}
    (p : ℕ) (a : ∀ U, (M.obj U).exteriorPower p ⟶ N.obj U)
    {U V : Cᵒᵖ} (f : U ⟶ V)
    (h : ∀ v : Fin p → M.obj U,
      a V (exteriorPower.ιMulti (R.obj V) p (fun i => M.map f (v i))) =
        N.map f (a U (exteriorPower.ιMulti (R.obj U) p v))) :
    ((PresheafOfModulesOfCommRing.exteriorPower (R := R) p).obj M).map f ≫
        (ModuleCat.restrictScalars (R.map f).hom).map (a V) =
      a U ≫ N.map f := by
  apply ModuleCat.exteriorPower.hom_ext (R := R.obj U) (M := M.obj U) (n := p)
  apply ModuleCat.AlternatingMap.ext
  intro v
  change a V
      (((PresheafOfModulesOfCommRing.exteriorPower (R := R) p).obj M).map f
        (exteriorPower.ιMulti (R.obj U) p v)) =
    N.map f (a U (exteriorPower.ιMulti (R.obj U) p v))
  erw [PresheafOfModulesOfCommRing.exteriorPower_obj_map_mk p M f v]
  exact h v

/-- Construct a morphism from the sectionwise exterior power from linear maps
whose restriction identities hold on pure exterior generators. -/
def exteriorHomOfGenerators {C : Type u} [SmallCategory C]
    {R : Cᵒᵖ ⥤ CommRingCat.{u}} {M N : PresheafOfModulesOfCommRing.{u} R}
    (p : ℕ) (a : ∀ U, (⋀[R.obj U]^p (M.obj U)) →ₗ[R.obj U] N.obj U)
    (h : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (v : Fin p → M.obj U),
      a V (exteriorPower.ιMulti (R.obj V) p (fun i => M.map f (v i))) =
        N.map f (a U (exteriorPower.ιMulti (R.obj U) p v))) :
    ((PresheafOfModulesOfCommRing.exteriorPower (R := R) p).obj M) ⟶ N :=
  PresheafOfModulesOfCommRing.homMk
    (fun U => ModuleCat.ofHom (a U))
    (fun f => exteriorHom_naturality p (fun U => ModuleCat.ofHom (a U)) f (h f))

/-- A sectionwise exterior morphism may equivalently be specified using the
underlying abelian sheaves and their ordinary restriction maps. -/
def exteriorSheafHomOfGenerators {Y : Scheme.{u}} {M N : Y.Modules}
    (p : ℕ)
    (a : ∀ U : Y.Opens, (⋀[Γ(Y,U)]^p Γ(M,U)) →ₗ[Γ(Y,U)] Γ(N,U))
    (h : ∀ {U V : Y.Opens} (i : V ⟶ U) (v : Fin p → Γ(M,U)),
      N.presheaf.map i.op (a U (exteriorPower.ιMulti Γ(Y,U) p v)) =
        a V (exteriorPower.ιMulti Γ(Y,V) p
          (fun j => M.presheaf.map i.op (v j)))) :
    ((PresheafOfModulesOfCommRing.exteriorPower (R := Y.presheaf) p).obj M.val) ⟶ N.val :=
  exteriorHomOfGenerators (R := Y.presheaf) (M := M.val) (N := N.val)
    p (fun U => a U.unop) (fun f v => (h f.unop v).symm)

run_cmd do
  let out ← IO.getStderr
  out.putStrLn "SEGRE_STAGE ExteriorMinorGenerators"
  out.flush

/-- The full coordinate-minor comparison as a morphism from the sectionwise exterior presheaf. -/
def presheafMinorMap (p : ℕ) :
    ((PresheafOfModulesOfCommRing.exteriorPower (R := (X).presheaf) p).obj
      (eulerSource (I := I) (K := K)).val) ⟶
        (∏ᶜ fun _ : Set.powersetCard I p => Proj.twistingSheaf 𝒜 (-(p : ℤ))).val :=
  exteriorSheafHomOfGenerators (Y := X)
    (M := eulerSource (I := I) (K := K))
    (N := ∏ᶜ fun _ : Set.powersetCard I p => Proj.twistingSheaf 𝒜 (-(p : ℤ)))
    p (minorLinear (I := I) (K := K) p)
    (minorLinear_res_ιMulti (I := I) (K := K) p)

run_cmd do
  let out ← IO.getStderr
  out.putStrLn "SEGRE_STAGE ExteriorMinorPresheafMap"
  out.flush

instance presheafMinorMap_locallyInjective (p : ℕ) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf (X).ringCatSheaf.obj).map
        (presheafMinorMap (I := I) (K := K) p)) :=
  SheafExteriorKernel.locallyInjective_of_injective_on_cover_subopens
    ((PresheafOfModules.toPresheaf (X).ringCatSheaf.obj).map
      (presheafMinorMap (I := I) (K := K) p))
    (ProjectiveCech.coordinateOpen (I := I) (K := K))
    (ProjectiveCech.coordinate_cover (I := I) (K := K))
    (fun j U hU => (minorLinear_bijective_on_chart p j U hU).1)

instance presheafMinorMap_locallySurjective (p : ℕ) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf (X).ringCatSheaf.obj).map
        (presheafMinorMap (I := I) (K := K) p)) :=
  SheafExteriorKernel.locallySurjective_of_surjective_on_cover_subopens
    ((PresheafOfModules.toPresheaf (X).ringCatSheaf.obj).map
      (presheafMinorMap (I := I) (K := K) p))
    (ProjectiveCech.coordinateOpen (I := I) (K := K))
    (ProjectiveCech.coordinate_cover (I := I) (K := K))
    (fun j U hU => (minorLinear_bijective_on_chart p j U hU).2)

instance presheafMinorMap_sheafification_isIso (p : ℕ) :
    IsIso ((PresheafOfModules.sheafification (𝟙 (X).ringCatSheaf.obj)).map
      (presheafMinorMap (I := I) (K := K) p)) := by
  have h : (Opens.grothendieckTopology X).W.inverseImage
      (PresheafOfModules.toPresheaf (X).ringCatSheaf.obj)
      (presheafMinorMap (I := I) (K := K) p) :=
    (Opens.grothendieckTopology X).W_of_isLocallyBijective
      ((PresheafOfModules.toPresheaf (X).ringCatSheaf.obj).map
        (presheafMinorMap (I := I) (K := K) p))
  rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
    (𝟙 (X).ringCatSheaf.obj)] at h
  exact h

omit [LinearOrder I] in
/-- The full actual exterior source sheaf is the expected finite product of O(-p), with the
isomorphism defined by genuine coordinate minors in every characteristic. -/
def exteriorSourceTwistIso (p : ℕ) :
    (SheafOfModules.exteriorPower (X).sheaf p).obj (eulerSource (I := I) (K := K)) ≅
      ∏ᶜ fun _ : Set.powersetCard I p => Proj.twistingSheaf 𝒜 (-(p : ℤ)) := by
  classical
  letI : LinearOrder I := LinearOrder.lift' (Fintype.equivFin I) (Fintype.equivFin I).injective
  exact SheafOfModules.exteriorPowerIso (R := (X).sheaf) p
      (eulerSource (I := I) (K := K)) ≪≫
    asIso ((PresheafOfModules.sheafification (𝟙 (X).ringCatSheaf.obj)).map (presheafMinorMap p)) ≪≫
    TauCeti.SheafOfModules.sheafificationIso (X).ringCatSheaf
      (∏ᶜ fun _ : Set.powersetCard I p => Proj.twistingSheaf 𝒜 (-(p : ℤ)))

end PaperVerification.Segre.ExteriorTwist

end SegreExteriorTwist

section SegreTwistedExteriorEuler

/-!
# Actual twists of the exterior Euler short exact sequences

Tensoring by `O(t)` is an equivalence, with inverse tensoring by `O(-t)`.
Consequently the actual exterior Euler sequences remain short exact at every
integer twist. Their middle terms are identified with the full finite products
of the actual twisting sheaves `O(t-p)` through the coordinate-minor comparison.
No flatness or cohomology hypothesis is substituted for this exactness proof.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 600000



attribute [local instance] MvPolynomial.gradedAlgebra

namespace PaperVerification.Segre.TwistedExteriorEuler

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory
open EulerSheaf EulerSections ExteriorEuler ExteriorTwist ProjectiveCech

universe u

section TensorInverse

variable {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]

/-- An actual two-sided tensor inverse makes tensoring an equivalence. The second
inverse isomorphism follows from the braiding, and `Equivalence.mk` supplies the
triangle identity by its verified adjointification construction. -/
def tensorRightEquivalence {L M : C} (e : L ⊗ M ≅ 𝟙_ C) : C ≌ C :=
  CategoryTheory.Equivalence.mk (tensorRight L) (tensorRight M)
    ((rightUnitorNatIso C).symm ≪≫ (tensoringRight C).mapIso e.symm ≪≫
      tensorRightTensor L M)
    ((tensorRightTensor M L).symm ≪≫
      (tensoringRight C).mapIso ((β_ M L) ≪≫ e) ≪≫ rightUnitorNatIso C)

end TensorInverse

variable {I K : Type u} [Fintype I] [DecidableEq I] [Field K]

local notation "𝒜" => MvPolynomial.homogeneousSubmodule I K
local notation "X" => Proj 𝒜

/-- The monoidal tensor product of the two actual twisting sheaves is identified
with their sum twist by multiplication, through the canonical sheafification
comparison, rather than by treating the tensor object as definitionally equal. -/
def twistingTensorIso (m n : ℤ) :
    Proj.twistingSheaf 𝒜 m ⊗ Proj.twistingSheaf 𝒜 n ≅ Proj.twistingSheaf 𝒜 (m+n) :=
  SheafOfModules.tensorUnderlyingIso (R := (X).sheaf)
    (Proj.twistingSheaf 𝒜 m) (Proj.twistingSheaf 𝒜 n) ≪≫
    (TauCeti.SheafOfModules.tensorProductIso (X).sheaf
      (Proj.twistingSheaf 𝒜 m) (Proj.twistingSheaf 𝒜 n)).symm ≪≫
    Proj.twistingSheaf.tensorProductIso (MvPolynomial.X : I → MvPolynomial I K)
      (fun i => MvPolynomial.isHomogeneous_X (R := K) i) coordinate_cover m n

/-- The inverse twist is a literal tensor inverse of `O(t)`. -/
def twistingInverseIso (t : ℤ) :
    Proj.twistingSheaf 𝒜 t ⊗ Proj.twistingSheaf 𝒜 (-t) ≅ 𝟙_ (X).Modules :=
  twistingTensorIso t (-t) ≪≫ eqToIso (by rw [add_neg_cancel]) ≪≫
    (Proj.unitIsoTwistingSheafZero 𝒜).symm

/-- Tensoring by the actual line bundle `O(t)`. -/
abbrev twistFunctor (t : ℤ) : (X).Modules ⥤ (X).Modules :=
  tensorRight (Proj.twistingSheaf 𝒜 t)

/-- The inverse-twist equivalence; both functors are actual sheaf tensor products. -/
def twistEquivalence (t : ℤ) : (X).Modules ≌ (X).Modules :=
  tensorRightEquivalence (twistingInverseIso (I := I) (K := K) t)

instance twistFunctor_isEquivalence (t : ℤ) :
    (twistFunctor (I := I) (K := K) t).IsEquivalence :=
  (twistEquivalence t).isEquivalence_functor

/-- Actual exterior powers of the coordinate Euler kernel, tensored with the
actual twisting sheaf. This is not defined in terms of desired cohomology. -/
def exteriorKernelTwist (p : ℕ) (t : ℤ) : (X).Modules :=
  (twistFunctor t).obj
    ((SheafOfModules.exteriorPower (X).sheaf p).obj (eulerKernel (I := I) (K := K) 0))

/-- The corresponding actual exterior source. -/
def exteriorSourceTwist (p : ℕ) (t : ℤ) : (X).Modules :=
  (twistFunctor t).obj
    ((SheafOfModules.exteriorPower (X).sheaf p).obj (eulerSource (I := I) (K := K)))

/-- All middle terms, including exterior degrees zero and beyond the dimension,
are the full products of `O(t-p)` indexed by exterior-coordinate subsets. -/
def twistedExteriorSourceIso (p : ℕ) (t : ℤ) :
    exteriorSourceTwist (I := I) (K := K) p t ≅
      ∏ᶜ fun _ : Set.powersetCard I p => Proj.twistingSheaf 𝒜 (t-(p : ℤ)) :=
  (twistFunctor t).mapIso (exteriorSourceTwistIso p) ≪≫
    PreservesProduct.iso (twistFunctor t)
      (fun _ : Set.powersetCard I p => Proj.twistingSheaf 𝒜 (-(p : ℤ))) ≪≫
    Pi.mapIso (fun _ => twistingTensorIso (-(p : ℤ)) t ≪≫
      eqToIso (by congr 1; omega))

/-- The actual twisted exterior Euler sequence. -/
def twistedExteriorEulerSequence (p : ℕ) (t : ℤ) : ShortComplex (X).Modules :=
  (exteriorEulerSequence (I := I) (K := K) p).map (twistFunctor t)

/-- Every integer twist preserves the entire exterior Euler short exact sequence. -/
theorem twistedExteriorEuler_shortExact (p : ℕ) (t : ℤ) :
    (twistedExteriorEulerSequence (I := I) (K := K) p t).ShortExact :=
  (exteriorEuler_shortExact p).map_of_exact (twistFunctor t)

/-- The three terms retain their intended actual sheaves. -/
theorem twistedExteriorEuler_terms (p : ℕ) (t : ℤ) :
    (twistedExteriorEulerSequence (I := I) (K := K) p t).X₁=exteriorKernelTwist (p+2) t ∧
    (twistedExteriorEulerSequence (I := I) (K := K) p t).X₂=exteriorSourceTwist (p+2) t ∧
    (twistedExteriorEulerSequence (I := I) (K := K) p t).X₃=exteriorKernelTwist (p+1) t :=
  ⟨rfl,rfl,rfl⟩

/-- Exterior degree zero gives the original twisting sheaf. -/
def exteriorKernelTwistZeroIso (t : ℤ) :
    exteriorKernelTwist (I := I) (K := K) 0 t ≅ Proj.twistingSheaf 𝒜 t :=
  (twistFunctor t).mapIso
    ((SheafOfModules.exteriorPowerZeroIso (X).sheaf).app (eulerKernel 0)) ≪≫
    (λ_ (Proj.twistingSheaf 𝒜 t))

/-- Exterior degree one is the actual Euler kernel tensored by `O(t)`. -/
def exteriorKernelTwistOneIso (t : ℤ) :
    exteriorKernelTwist (I := I) (K := K) 1 t ≅
      eulerKernel 0 ⊗ Proj.twistingSheaf 𝒜 t :=
  (twistFunctor t).mapIso
    ((SheafOfModules.exteriorPowerOneIso (X).sheaf).app (eulerKernel 0))

end PaperVerification.Segre.TwistedExteriorEuler

end SegreTwistedExteriorEuler

section SegreEulerQuasicoherent

/-!
# Quasicoherence of the actual exterior Euler sheaves

The actual exterior source is a finite product of twisting sheaves by the
proved coordinate-minor isomorphism. The actual positive exterior power of
the Euler kernel is the kernel of its genuine contraction differential.
These descriptions prove quasicoherence in every exterior degree, including
zero and degrees above the projective dimension. No quasicoherence hypothesis
is added to the product-cohomology application.

-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 600000

attribute [local instance] MvPolynomial.gradedAlgebra

namespace PaperVerification.Segre.EulerQuasicoherent

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open TauCeti TauCeti.AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open EulerSheaf EulerSections ExteriorEuler ExteriorTwist TwistedExteriorEuler SheafKoszul

universe u

/-- Finite products are actual biproducts, so quasicoherence follows from
its proven preservation under coproducts. -/
theorem finiteProduct_quasicoherent {X : Scheme.{u}} {ι : Type u} [Finite ι]
    (M : ι → X.Modules) [∀ i, (M i).IsQuasicoherent] :
    (∏ᶜ M).IsQuasicoherent := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  letI : HasBiproduct M := HasBiproduct.of_hasProduct M
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((biproduct.isoCoproduct M).symm ≪≫ biproduct.isoProduct M)
    (inferInstanceAs (∐ M).IsQuasicoherent)

variable {I K : Type u} [Fintype I] [DecidableEq I] [Field K]
local notation "𝒜" => MvPolynomial.homogeneousSubmodule I K
local notation "X" => Proj 𝒜

/-- The actual exterior source is quasicoherent through its full coordinate-minor comparison. -/
theorem exteriorSource_quasicoherent (p : ℕ) :
    ((SheafOfModules.exteriorPower (X).sheaf p).obj
      (eulerSource (I := I) (K := K))).IsQuasicoherent := by
  haveI : (∏ᶜ fun _ : Set.powersetCard I p =>
      Proj.twistingSheaf 𝒜 (-(p : ℤ))).IsQuasicoherent :=
    finiteProduct_quasicoherent _
  exact (SheafOfModules.isQuasicoherent (X).ringCatSheaf).prop_of_iso
    (exteriorSourceTwistIso (I := I) (K := K) p).symm inferInstance

/-- Actual exterior powers of the Euler kernel are quasicoherent in every degree. -/
theorem exteriorKernel_quasicoherent (p : ℕ) :
    ((SheafOfModules.exteriorPower (X).sheaf p).obj
      (eulerKernel (I := I) (K := K) 0)).IsQuasicoherent := by
  cases p with
  | zero =>
      have hunit : (SheafOfModules.unit (X).ringCatSheaf).IsQuasicoherent := inferInstance
      exact (SheafOfModules.isQuasicoherent (X).ringCatSheaf).prop_of_iso
        ((SheafOfModules.exteriorPowerZeroIso (X).sheaf).app
          (eulerKernel (I := I) (K := K) 0)).symm hunit
  | succ p =>
      haveI := exteriorSource_quasicoherent (I := I) (K := K) p
      haveI := exteriorSource_quasicoherent (I := I) (K := K) (p + 1)
      haveI : (kernel (differential (R := (X).sheaf)
          (unitEulerMap (I := I) (K := K)) p)).IsQuasicoherent :=
        @Scheme.Modules.isQuasicoherent_kernel
          (Proj (MvPolynomial.homogeneousSubmodule I K)) _ _
          (differential (R := (X).sheaf) (M := eulerSource (I := I) (K := K))
            (unitEulerMap (I := I) (K := K)) p)
          inferInstance inferInstance
      exact (SheafOfModules.isQuasicoherent (X).ringCatSheaf).prop_of_iso
        (exteriorEulerKernelIso (I := I) (K := K) p).symm inferInstance

/-- The actual sheaf Ω^p(t) is quasicoherent for every integer twist. -/
instance exteriorKernelTwist_quasicoherent (p : ℕ) (t : ℤ) :
    (exteriorKernelTwist (I := I) (K := K) p t).IsQuasicoherent := by
  haveI := exteriorKernel_quasicoherent (I := I) (K := K) p
  change (((SheafOfModules.exteriorPower (X).sheaf p).obj
    (eulerKernel (I := I) (K := K) 0)) ⊗ Proj.twistingSheaf 𝒜 t).IsQuasicoherent
  infer_instance

end PaperVerification.Segre.EulerQuasicoherent

end SegreEulerQuasicoherent

end SegreProjectiveCohomology

end
end
end ProbeLayer391

/-! Future-only kernel audit for one exported mathematical stage.

Append to the stage being checked, with Lean.Util.CollectAxioms available through
both `public import Lean.Util.CollectAxioms` and `import all Lean.Util.CollectAxioms`
in that stage's header, as required by the reviewed FullFlattenedAudit.

Every new declaration in the checked kernel environment is included: public,
private, generated and vendored declarations receive the same direct-sorry and
transitive-axiom checks. This is evidence for this stage only. Later principal
theorems need not exist yet, and the final full principal audit remains required.

This preparation does not execute the audit, export a module or alter a proof.
-/

open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  unless env.header.trustLevel == 0 do
    throwError "The stage kernel audit requires kernel trust level zero"
  let names := (env.checked.get.constants.foldStage2
    (fun (names : Array Name) name _ => names.push name) #[]).qsort Name.quickLt
  unless names.size > 0 do throwError "The stage mathematical module is empty"
  -- Reject direct proof holes before computing transitive axiom closures.
  -- The complete successful audit below remains unchanged.
  for name in names do
    let some info := env.checked.get.find? name
      | throwError "Authored declaration is not kernel checked: {name}"
    if let .axiomInfo _ := info then throwError "Authored axiom: {name}"
    if info.type.hasSorry || ((info.value? (allowOpaque := true)).any (·.hasSorry)) then
      throwError "Authored declaration contains a sorry expression: {name}"
  let privateEnv := env.setExporting false
  let importedAxioms := exportedAxiomsExt.getState (asyncMode := .mainOnly) env
  -- Match Lean's ordinary export audit, sharing its traversal cache across names.
  let axiomRows := CollectAxioms.runM privateEnv do
    names.mapM fun name =>
      return (name, ← CollectAxioms.collectAndGet importedAxioms.find? name)
  let mut theoremCount : Nat := 0
  for (name, axioms) in axiomRows do
    let some info := env.checked.get.find? name
      | throwError "Authored declaration is not kernel checked: {name}"
    if let .axiomInfo _ := info then throwError "Authored axiom: {name}"
    if info.type.hasSorry || ((info.value? (allowOpaque := true)).any (·.hasSorry)) then
      throwError "Authored declaration contains a sorry expression: {name}"
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unapproved transitive axiom in {name}: {ax}"
    if let .thmInfo _ := info then
      theoremCount := theoremCount + 1
  let report := Json.mkObj [
    ("main_module", toJson env.header.mainModule.toString),
    ("declaration_count", toJson names.size),
    ("theorem_count", toJson theoremCount),
    ("trust_level", toJson env.header.trustLevel.toNat),
    ("allowed_axioms", toJson #["propext", "Classical.choice", "Quot.sound"]),
    ("audit_scope", toJson "current_stage_new_declarations")]
  logInfo m!"SEGRE_STAGE_KERNEL_AUDIT_PASS {report.compress}"
