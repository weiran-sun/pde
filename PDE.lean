-- Background: calculus, measure theory, functional analysis
import PDE.Background.CalculusMeasureTheory.DivergenceTheorem.GeneralizedDivergence
import PDE.Background.CalculusMeasureTheory.DivergenceTheorem.R3Divergence
import PDE.Background.CalculusMeasureTheory.GraphHausdorffMeasure.R3GraphMeasure
import PDE.Background.CalculusMeasureTheory.GraphHausdorffMeasure.RnGraphHausdorffMeasure
import PDE.Background.CalculusMeasureTheory.GraphHausdorffMeasure.SurfaceIntegration
import PDE.Background.CalculusMeasureTheory.HausdorffUnitCircleSphere
import PDE.Background.CalculusMeasureTheory.PDEDomains
import PDE.Background.CalculusMeasureTheory.DomainGeometry
import PDE.Background.CalculusMeasureTheory.SphereSurfaceMeasure
import PDE.Background.FunctionalAnalysis.OrthonormalBasis
import PDE.Background.FunctionalAnalysis.HilbertWeakCompactness

-- Sobolev spaces
import PDE.FunctionSpaces.SobolevSpace.LpFunctionSpaces
import PDE.FunctionSpaces.SobolevSpace.WeakDerivative
import PDE.FunctionSpaces.SobolevSpace.SobolevSpaces
import PDE.FunctionSpaces.SobolevSpace.HkSpaces
import PDE.FunctionSpaces.SobolevSpace.Mollification

-- Basics: the heat equation
import PDE.Basics.Heat.HeatKernel
import PDE.Basics.Heat.HeatConvolutionAbstract
import PDE.Basics.Heat.HeatSolution
import PDE.Basics.Heat.HeatSolutionProperty
import PDE.Basics.Heat.HeatDecay
import PDE.Basics.Heat.HeatMaximumPrinciple
import PDE.Basics.Heat.HeatKernelND
import PDE.Basics.Heat.HeatSolutionND
import PDE.Basics.Heat.HeatSolutionPropertyND
import PDE.Basics.Heat.HeatMaximumPrincipleND

-- Basics: the Laplace equation
import PDE.Basics.Laplace.CalculusBasic
import PDE.Basics.Laplace.GreensIdentities
import PDE.Basics.Laplace.SphericalMeans
import PDE.Basics.Laplace.LaplaceMeanValue
import PDE.Basics.Laplace.LaplaceMaximumPrinciple
import PDE.Basics.Laplace.LaplaceDirichletPrinciple
import PDE.Basics.Laplace.FundamentalSolution
import PDE.Basics.Laplace.PoissonEquation
import PDE.Basics.Laplace.RepresentationFormula
import PDE.Basics.Laplace.GreensFunction
import PDE.Basics.Laplace.GreensFunctionSymmetry

-- Methods: ODE theory and the Galerkin method
import PDE.Methods.ODEMethods.CaratheodoryExistence
import PDE.Methods.Galerkin.Parabolic.ParabolicOperator
import PDE.Methods.Galerkin.Parabolic.ParabolicExistence
import PDE.Methods.Galerkin.Parabolic.ParabolicExistenceCaratheodory
