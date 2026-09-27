import HeunProblem
import PolynomialGrammar
import JetPropagation
import AnalyticBridge
import FiniteRoot
import Integration
import BaseEigenfunction
import OperatorBridge
import BaseAnalytic
import PerturbationJets
import FiniteRootUniqueness
import FiniteRootStabilization
import AnalyticTaylorBridge
import FrobeniusBounds
import FrobeniusAnalytic
import FrobeniusODE
import FrobeniusTransform
import FrobeniusOne
import FrobeniusGauge
import SingularSolution
import BaseConnection
import SingularGerm
import CauchyBounds
import JointAnalytic
import ODEUniqueness
import RegularSingularUniqueness
import EndpointIndependence
import ConnectionUniqueness
import ActualConnection
import ConnectionAnalytic
import BanachTail
import HeunCompletion

-- Exact literature target and the theorem proving it.
#check Heun.LiteratureConjecture
#check Heun.literatureConjecture
#print axioms Heun.coefficient_at_s_zero
#print axioms Heun.D_injective
#print axioms GcoyHeun.L0_differential
#print axioms GcoyHeun.VHeun_differential
#print axioms GcoyHeun.coeff_VHeun_succ
#print axioms GcoyHeun.bounded_VHeun
#print axioms GcoyHeun.bounded_VConfluent
#print axioms GcoyHeun.bounded_VReduced
#print axioms GcoyHeun.bounded_iterate
#print axioms MoriTakemura.heun_tail_vanishing
#print axioms MoriTakemura.tail_root_jet_stabilization
#print axioms MoriTakemura.complex_scaled_product_hasDerivAt
#print axioms MoriTakemura.scaled_rootProduct_derivative_ne_zero
#print axioms Gcoy.AnalyticBridge.analytic_connection_germ_jets_vanish
#print axioms Gcoy.AnalyticBridge.exists_analytic_implicit_branch
#print axioms Heun.finite_root_germ_exists
#print axioms Heun.exists_formal_polynomial_perturbation
#print axioms Heun.base_regular_endpoint_pair
#print axioms Heun.polynomial_coefficients_eq_recurrence
#print axioms Heun.finiteRootTaylor_stabilizes
#print axioms Heun.coefficient_geometric_bound
#print axioms Heun.frobeniusSum_regular_zero_solution_nonresonant
#print axioms Heun.regularOne_solution
#print axioms Heun.singularFactor_solution_slit
#print axioms Heun.base_IsConnectionCoefficient
#print axioms Gcoy.SingularGerm.singular_not_regularGerms
#print axioms Heun.frobeniusSum_contDiffAt
#print axioms Heun.frobeniusDeriv_contDiffAt
#print axioms Heun.analytic_second_order_span
#print axioms Heun.source_regular_zero_unique_on
#print axioms Heun.actual_endpoint_wronskian_ne_zero
#print axioms Heun.actual_connection_exists
#print axioms Heun.isConnectionCoefficient_unique
#print axioms Heun.actualConnection_spec
#print axioms Heun.actualConnection_base
#print axioms Heun.actualConnection_contDiffAt
#print axioms Heun.borderT_isInvertible
#print axioms Heun.exists_analytic_encoded_branch
#print axioms Heun.analytic_encoded_branch_jet_support
#print axioms Heun.final_hasSum_of_encoded_branch
#print axioms Heun.literatureConjecture
