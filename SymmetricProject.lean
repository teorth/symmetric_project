-- introduces the set_binom function: set_binom n k is the set of k-element subsets of {0,...,n-1}.
import SymmetricProject.binomial

-- introduces the elementary symmetric polynomials: esymm n k x is the k^th symmetric polynomial of the first n variables of an infinite sequence x_0, x_1, ... of reals.
import SymmetricProject.esymm_basic

-- Establishes the generating function identity $\prod_{i=1}^n (z - x_i) = \sum_{k=0}^n (-1)^k S_{n,k}(x) z^{n-k}$.
import SymmetricProject.esymm_generating

