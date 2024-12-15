# This program is a part of the project
# "Complete homogeneous symmetric polynomials with repeating variables"
# by Luis Angel Gonzalez Serrano and Egor A. Maximenko (2024).

# In this program, we test the main theorems about the expansion of h_m(y^{[\kappa]})
# into linear combinations
# \sum_{s=1}^n \sum_{r=1}^{\kappa_s} \binom{r+m-1}{r-1} A_{y,\kappa,s,r} y_s^m
# and
# \sum_{s=1}^n \sum_{r=1}^{\kappa_s} \binom{N+m-1}{r-1} B_{y,\kappa,s,r} y_s^{m+N-r},
# where N=|\kappa|.


import time


def lists_with_bounded_sum(n, s):
    # lists [k_0, k_1, ..., k_{n-1}] with k_0 + k_1 + ... + k_{n-1} \le s
    r = [[]]
    for j in range(n):
        rprev = r
        r = []
        for x in rprev:
            sprev = sum(x)
            for y in range(s - sprev + 1):
                z = x + [y]
                r += [z]
    return r


def lists_with_given_sum(n, s):
    # lists [k_0, k_1, ..., k_{n-1}] with k_0 + k_1 + ... + k_{n-1} = s
    r = [[]] if (n == 0 and s == 0) else []
    if n > 0:
        rprev = lists_with_bounded_sum(n - 1, s)
        for x in rprev:
            y = s - sum(x)
            z = x + [y]
            r += [z]
    return r


def lists_with_bounded_components(n, mmin, mmax):
    # lists [k_0, k_1, ..., k_{n-1}] with mmin \le k_j \le mmax
    r = [[]]
    for j in range(n):
        rprev = r
        r = []
        for x in rprev:
            for y in range(mmin, mmax + 1):
                z = x + [y]
                r += [z]
    return r


def pol_ring(letter, n):
    varnames = [letter + str(k) for k in range(n)]
    PR = PolynomialRing(QQ, varnames)
    return PR


def pol_vars(letter, n):
    PR = pol_ring(letter, n)
    return vector(PR, n, PR.gens())


# The Sage function 'det' crashes for some symbolic matrices.
# The following simple recursive version is more stable.
# To speed up the function and save memory, we do not create the submatrices explicitly.
# The sum over all permutations is slower because our matrices usually have many zeros.


def det_recur(A, rfirst, cols):
    if rfirst == A.nrows():
        return A.base_ring().one()
    result = A.base_ring().zero()
    s = 1
    for k in cols:
        if A[rfirst][k] != 0:
            newcols = [c for c in cols if c != k]
            result += A[rfirst][k] * det_recur(A, rfirst + 1, newcols) * s
        s = -s
    return result


def my_det(A):
    return det_recur(A, 0, list(range(A.nrows())))


def hom_polynomials(xs, degstop):
    n = len(xs)
    R = xs.base_ring()
    hs = vector(R, degstop)
    if degstop > 0:
        for k in range(degstop):
            hs[k] = xs[0] ** k
        for j in range(1, n):
            hs_prev = hs
            hs[0] = R.one()
            for k in range(1, degstop):
                hs[k] = hs_prev[k] + xs[j] * hs[k - 1]
    return hs


def hom_polynomial_via_recur(xs, m):
    hs = hom_polynomials(xs, m + 1)
    return hs[m]


# Construct matrix G_{\la,\ka}(ys) from the paper.

def generalized_confluent_vandermonde_matrix(la, ka, ys):
    n = len(ka)
    N = sum(ka)
    la_ext = la + [0] * (N - len(la))
    R = ys.base_ring()
    A = matrix(R, N, N)
    k = 0
    for p in range(n):
        for r in range(ka[p]):
            for j in range(N):
                mypower = la_ext[N - 1 - j] + j - r
                coef = binomial(la_ext[N - 1 - j] + j, r)
                A[j, k] = coef * (ys[p] ** mypower) if mypower >= 0 else R.zero()
            k += 1
    return A


def confluent_vandermonde_det_formula(ys, ka):
    n = len(ka)
    N = sum(ka)
    R = ys.base_ring()
    result = R.one()
    for j in range(n):
        for k in range(j + 1, n):
            result *= (ys[k] - ys[j]) ** (ka[j] * ka[k])
    return result


def list_with_reps(ys, ka):
    n = len(ys)
    N = sum(ka)
    R = ys.base_ring()
    result = vector(R, N) 
    k = 0
    for q in range(n):
        for r in range(ka[q]):
            result[k] = ys[q]
            k += 1
    return result


# Here is a slightly more efficient algorithm to construct G_{\la,\ka}(ys).


def binomial_coefs(t, m):
    # compute [C[0], ..., C[m - 1]] where C[k] = binomial(t, k)
    C = vector(ZZ, m)
    C[0] = 1  
    for k in range(1, m):
        C[k] = C[k - 1] * (t - k + 1) / k
    return C


def integer_log2(x):
    # compute floor(log2(x)), i.e.,
    # the maximum of k such that 2 ** k <= x
    y = 1
    k = 0
    while y <= x:
        y = 2 * y
        k += 1
    return k - 1


def binary_powers(a, L):
    # compute [a, a ** 2, a ** 4, a ** 8, ..., a ** (2 ** L)]
    R = a.parent()
    b = vector(R, L + 1)
    c = a
    for j in range(L + 1):
        b[j] = c
        c = c * c
    return b


def binary_expon(B, p):
    # compute a ** p using
    # B = [a, a ** 2, a ** 4, a ** 8, ..., a ** (2 ** L)];
    # we suppose that p < 2 ** (L + 1)
    R = B.base_ring()
    c = R.one()
    q = p
    j = 0
    while q > 0:
        if mod(q, 2) != 0:
            c = c * B[j]
        q = q // 2
        j = j + 1
    return c


def generalized_confluent_vandermonde_matrix_efficient(la, ka, y):
    n = len(ka)
    N = sum(ka)
    K = max(ka)
    la_ext = la + [0] * (N - len(la))
    la_ext_rev = list(reversed(la_ext))
    L = integer_log2(la_ext[0] + N)
    R = y.base_ring()
    C = matrix(ZZ, N, K)
    for j in range(N):
        C[j, :] = binomial_coefs(la_ext_rev[j] + j, K)
    G = matrix(R, N, N)
    k = 0
    for q in range(n):
        B = binary_powers(y[q], L)
        for r in range(ka[q]):
            u = [la_ext_rev[j] + j - r for j in range(N)]
            jlist = [j for j in range(N) if u[j] >= 0]
            jmin = min(jlist, default = N)
            for j in range(jmin, N):
                G[j, k] = C[j, r] * binary_expon(B, u[j])
            k += 1
    return G


def schur_rep_via_generalized_confluent_vandermonde_efficient(la, ka, ys):
    numer = my_det(generalized_confluent_vandermonde_matrix_efficient(la, ka, ys))
    denom = confluent_vandermonde_det_formula(ys, ka)
    return numer / denom


def hom_rep_via_generalized_confluent_vandermonde_efficient(m, ka, ys):
    la = [m]
    return schur_rep_via_generalized_confluent_vandermonde_efficient(la, ka, ys)



def multi_power(a, k):
    n = len(a)
    return prod([a[j] ** k[j] for j in range(n)])


def hom_with_repetitions_combinatorial_coef(kappa, k):
    n = len(kappa)
    result = 1
    for j in range(n):
        result *= binomial(kappa[j] + k[j] - 1, k[j])
    return result


def hom_with_repetitions_combinatorial(y, kappa, m):
    n = len(y)
    R = y.base_ring()
    ks = lists_with_given_sum(n, m)
    result = R.zero()
    for k in ks:
        coef = hom_with_repetitions_combinatorial_coef(kappa, k)
        result += coef * multi_power(y, k)
    return result


def A_coef(y, kappa, s, r):
    n = len(y)
    F = FractionField(y.base_ring())
    ind_reduced = list(range(s)) + list(range(s + 1, n))
    kappa_reduced = [kappa[d] for d in ind_reduced]
    wlist = [y[d] / (y[d] - y[s]) for d in ind_reduced]
    w = vector(F, n - 1, wlist)
    factor1 = (- y[s]) ** (sum(kappa) - kappa[s])
    factor2 = F.one()
    for d in ind_reduced:
        factor2 *= (y[d] - y[s]) ** kappa[d]
    factor3 = hom_with_repetitions_combinatorial(w, kappa_reduced, kappa[s] - r)
    result = factor1 * factor3 / factor2
    return result


def B_coef(y, kappa, s, r):
    n = len(y)
    F = FractionField(y.base_ring())
    ind_reduced = list(range(s)) + list(range(s + 1, n))
    kappa_reduced = [kappa[d] for d in ind_reduced]
    zlist = [1 / (y[d] - y[s]) for d in ind_reduced]
    z = vector(F, n - 1, zlist)
    factor1 = (- 1) ** (sum(kappa) - kappa[s])
    factor2 = prod([z[j] ** kappa_reduced[j] for j in range(n - 1)])
    factor3 = hom_with_repetitions_combinatorial(z, kappa_reduced, kappa[s] - r)
    result = factor1 * factor2 * factor3
    return result


def hom_rep_via_A(m, kappa, y):
    n = len(y)
    F = FractionField(y.base_ring())
    result = F.zero()
    for s in range(n):
        for r in range(1, kappa[s] + 1):
            factor0 = binomial(m + r - 1, r - 1)
            factor1 = A_coef(y, kappa, s, r)
            factor2 = y[s] ** m
            term = factor0 * factor1 * factor2
            result += term
    return result


def hom_rep_via_B(m, kappa, y):
    n = len(y)
    N = sum(kappa)
    F = FractionField(y.base_ring())
    result = F.zero()
    for s in range(n):
        for r in range(1, kappa[s] + 1):
            factor0 = binomial(m + N - 1, r - 1)
            factor1 = B_coef(y, kappa, s, r)
            factor2 = y[s] ** (m + N - r)
            term = factor0 * factor1 * factor2
            result += term
    return result


# tests


def test_hom_rep_expansions(m, kappa, verbose):
    n = len(kappa)
    ys = pol_vars('y', n)
    la = [m]
    xs = list_with_reps(ys, kappa)
    r0 = hom_polynomial_via_recur(xs, m)
    r1 = hom_rep_via_generalized_confluent_vandermonde_efficient(m, kappa, ys)
    r2 = hom_rep_via_A(m, kappa, ys)
    r3 = hom_rep_via_B(m, kappa, ys)
    polynomials_are_equal = (r0 == r1) and (r0 == r2) and (r0 == r3)
    if verbose:
        print('test_hom_rep_expansions,')
        print('m = ' + str(m) + ', kappa = ' + str(kappa))
        print('r0 = ', r0)
        print('r1 = ', r1)
        print('r2 = ', r2)
        print('r3 = ', r3)
        print('are equal the polynomials? ', polynomials_are_equal)
    return polynomials_are_equal


def big_test_hom_rep_expansions(mmax, kappa_sum_max):
    print('big_test_hom_rep_expansiones,')
    print('mmax = %d, kappa_sum_max = %d.' % (mmax, kappa_sum_max))
    t0 = time.time()
    nmax = kappa_sum_max
    tests = []
    for n in range(1, nmax):
        kappa_list = partitions_with_given_length_and_bounded_sum(n, kappa_sum_max)
        for ka in kappa_list:
            tests += [(m, ka) for m in range(mmax + 1)]
    print('number of tests: ' + str(len(tests)))
    big_result = True
    for m, ka in tests:
        result = test_hom_rep_expansions(m, ka, False)
        big_result = big_result and result
        print('m = ' + str(m) + ', ka = ' + str(ka) + ', ' + str(result))
    print('number of tests: ' + str(len(tests)))
    print('big_result = ' + str(big_result))
    t1 = time.time()
    print('time = %.3g seconds' % (t1 - t0))
    return big_result


#print(test_hom_rep_expansions(4, [2, 1], True))

print(big_test_hom_rep_expansions(10, 8))


