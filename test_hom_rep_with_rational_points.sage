import time
import random


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


def lists_with_bounded_components_and_given_sum(n, mmin, mmax, s):
    # lists [k_0, k_1, ..., k_{n-1}] with mmin \le k_j \le mmax and k_0+...+k_{n-1}=s
    result0 = lists_with_bounded_components(n, mmin, mmax)
    result1 = list([ka for ka in result0 if sum(ka) == s])
    return result1


def hom_polynomials(xs, degstop):
    # xs is an array of rational numbers
    n = len(xs)
    hs = vector(QQ, degstop)
    if degstop > 0:
        for k in range(degstop):
            hs[k] = xs[0] ** k
        for j in range(1, n):
            hs_prev = hs
            hs[0] = QQ.one()
            for k in range(1, degstop):
                hs[k] = hs_prev[k] + xs[j] * hs[k - 1]
    return hs


def hom_polynomial_via_recur(xs, m):
    hs = hom_polynomials(xs, m + 1)
    return hs[m]


# Construct matrix G_{\la,\ka}(ys) from the paper.

def generalized_confluent_vandermonde_matrix(la, ka, ys):
    # ys is an array of rational numbers
    n = len(ka)
    N = sum(ka)
    la_ext = la + [0] * (N - len(la))
    A = matrix(QQ, N, N)
    k = 0
    for p in range(n):
        for r in range(ka[p]):
            for j in range(N):
                mypower = la_ext[N - 1 - j] + j - r
                coef = binomial(la_ext[N - 1 - j] + j, r)
                A[j, k] = coef * (ys[p] ** mypower) if mypower >= 0 else QQ.zero()
            k += 1
    return A


def confluent_vandermonde_det_formula(ys, ka):
    n = len(ka)
    N = sum(ka)
    result = QQ.one()
    for j in range(n):
        for k in range(j + 1, n):
            result *= (ys[k] - ys[j]) ** (ka[j] * ka[k])
    return result


def list_with_reps(ys, ka):
    # ys is an array of rational numbers
    n = len(ys)
    N = sum(ka)
    result = vector(QQ, N) 
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
    # a is an array of rational numbers
    # compute [a, a ** 2, a ** 4, a ** 8, ..., a ** (2 ** L)]
    b = vector(QQ, L + 1)
    c = a
    for j in range(L + 1):
        b[j] = c
        c = c * c
    return b


def binary_expon(B, p):
    # compute a ** p using
    # B = [a, a ** 2, a ** 4, a ** 8, ..., a ** (2 ** L)];
    # we suppose that p < 2 ** (L + 1)
    c = QQ.one()
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
    C = matrix(ZZ, N, K)
    for j in range(N):
        C[j, :] = binomial_coefs(la_ext_rev[j] + j, K)
    G = matrix(QQ, N, N)
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


def schur_rep_via_G_efficient(la, ka, ys):
    G = generalized_confluent_vandermonde_matrix_efficient(la, ka, ys)
    numer = det(G)
    denom = confluent_vandermonde_det_formula(ys, ka)
    return numer / denom


def hom_rep_via_G_efficient(m, ka, ys):
    la = [m]
    return schur_rep_via_G_efficient(la, ka, ys)


def multi_power(a, k):
    n = len(a)
    return prod([a[j] ** k[j] for j in range(n)])


def hom_with_repetitions_combinatorial_coef(kappa, k):
    n = len(kappa)
    result = 1
    for j in range(n):
        result *= binomial(kappa[j] + k[j] - 1, k[j])
    return result


def hom_rep_combinatorial(m, kappa, y):
    # y is an array of rational numbers
    n = len(y)
    ks = lists_with_given_sum(n, m)
    result = QQ.zero()
    for k in ks:
        coef = hom_with_repetitions_combinatorial_coef(kappa, k)
        result += coef * multi_power(y, k)
    return result


def hom_rep_via_recur(m, kappa, y):
    x = list_with_reps(y, kappa)
    return hom_polynomial_via_recur(x, m)


def A_coef(y, kappa, s, r):
    # y is an array of rational numbers
    n = len(y)
    ind_reduced = list(range(s)) + list(range(s + 1, n))
    kappa_reduced = [kappa[d] for d in ind_reduced]
    wlist = [y[d] / (y[d] - y[s]) for d in ind_reduced]
    w = vector(QQ, n - 1, wlist)
    factor1 = (- y[s]) ** (sum(kappa) - kappa[s])
    factor2 = QQ.one()
    for d in ind_reduced:
        factor2 *= (y[d] - y[s]) ** kappa[d]
    factor3 = hom_rep_via_recur(kappa[s] - r, kappa_reduced, w)
    result = factor1 * factor3 / factor2
    return result


def B_coef(y, kappa, s, r):
    # y is an array of rational numbers
    n = len(y)
    ind_reduced = list(range(s)) + list(range(s + 1, n))
    kappa_reduced = [kappa[d] for d in ind_reduced]
    zlist = [1 / (y[d] - y[s]) for d in ind_reduced]
    z = vector(QQ, n - 1, zlist)
    factor1 = (- 1) ** (sum(kappa) - kappa[s])
    factor2 = prod([z[j] ** kappa_reduced[j] for j in range(n - 1)])
    factor3 = hom_rep_via_recur(kappa[s] - r, kappa_reduced, z)
    result = factor1 * factor2 * factor3
    return result


def binary_exponentiation(a, p):
    # compute a ** p by the binary exponentiation algorithm
    T = parent(a)
    if p < 0:
        return T.zero()
    result = T.one()
    binary_power = a
    q = p
    while q > 0:
        if mod(q, 2) != 0:
            result = result * binary_power
        binary_power = binary_power * binary_power
        q = q // 2
    return result


def hom_rep_via_A(m, kappa, y):
    n = len(y)
    result = QQ.zero()
    for s in range(n):
        for r in range(1, kappa[s] + 1):
            factor0 = binomial(m + r - 1, r - 1)
            factor1 = A_coef(y, kappa, s, r)
            factor2 = binary_exponentiation(y[s], m)
            term = factor0 * factor1 * factor2
            result += term
    return result


def hom_rep_via_B(m, kappa, y):
    n = len(y)
    N = sum(kappa)
    result = QQ.zero()
    for s in range(n):
        for r in range(1, kappa[s] + 1):
            factor0 = binomial(m + N - 1, r - 1)
            factor1 = B_coef(y, kappa, s, r)
            factor2 = binary_exponentiation(y[s], m + N - r)
            term = factor0 * factor1 * factor2
            result += term
    return result


# tests


def all_admissible_rational_numbers(max_numer_and_denom):
    result_set = set()
    for numer in range(1, max_numer_and_denom + 1):
        for denom in range(1, max_numer_and_denom + 1):
            for s in [1, -1]:
                x = QQ(numer * s / denom)
                result_set.add(x)
    return list(result_set) 


def random_partition_of_range(n, N):
    separators = random.sample(list(range(1, N)), n - 1)
    separators = list(sorted(separators))
    separators = [0] + separators + [N]
    kappa = [0] * n
    for j in range(n):
        kappa[j] = separators[j + 1] - separators[j]
    return kappa


def test_hom_rep_rational5(y, ka, m):
    x = list_with_reps(y, ka)
    result_A = hom_rep_via_A(m, ka, y)
    result_B = hom_rep_via_B(m, ka, y)
    result_det = hom_rep_via_G_efficient(m, ka, y)
    result_recur = hom_rep_recur(m, ka, y)
    result_comb = hom_rep_combinatorial(m, ka, y)
    print('results:')
    print(result_A, result_B, result_det, result_recur, result_comb)
    eqAB = result_A == result_B
    eqAdet = result_A == result_det
    eqArecur = result_A == result_recur
    eqAcomb = result_A == result_comb
    logical_result = eqAB and eqAdet and eqArecur and eqAcomb
    return logical_result


def test_hom_rep_rational4(y, ka, m):
    x = list_with_reps(y, ka)
    result_A = hom_rep_via_A(m, ka, y)
    result_B = hom_rep_via_B(m, ka, y)
    result_det = hom_rep_via_G_efficient(m, ka, y)
    result_recur = hom_polynomial_via_recur(x, m)
    eqAB = result_A == result_B
    eqAdet = result_A == result_det
    eqArecur = result_A == result_recur
    logical_result = eqAB and eqAdet and eqArecur
    return logical_result


def random_test_hom_rep_rational5(n, N, m):
    admissible_points = all_admissible_rational_numbers(16)
    admissible_kappas = lists_with_bounded_components_and_given_sum(n, 1, N, N)
    y_list = random.sample(admissible_points, n)
    y = vector(QQ, y_list)
    ka = random.choice(admissible_kappas)
    logical_result = test_hom_rep_rational5(y, ka, m)
    print(y)
    print(ka)
    return logical_result


def big_time_hom_rep_rational(method, n, N, m, nsamples):
    admissible_points = all_admissible_rational_numbers(16)
    start_time = time.time()
    for s in range(nsamples):
        y_list = random.sample(admissible_points, n)
        y = vector(QQ, y_list)
        ka = random_partition_of_range(n, N)
        r0 = method(m, ka, y)
    end_time = time.time()
    result = RDF((end_time - start_time) / nsamples)
    return result


def show_big_time_hom_rep_rational_all_methods(n, N, m, nsamples):
    print('show_big_time_hom_rep_rational_all_methods')
    print('n = %d, N = %d, m = %d, nsamples = %d' % (n, N, m, nsamples))
    tA = big_time_hom_rep_rational(hom_rep_via_A, n, N, m, nsamples)
    print('time with A: ' + str(tA))
    tB = big_time_hom_rep_rational(hom_rep_via_B, n, N, m, nsamples)
    print('time with B: ' + str(tB))
    tG = big_time_hom_rep_rational(hom_rep_via_G_efficient, n, N, m, nsamples)
    print('time with G: ' + str(tG))
    tR = big_time_hom_rep_rational(hom_rep_via_recur, n, N, m, nsamples)
    print('time with recur: ' + str(tR))


#print(random_test_hom_rep_rational5(3, 6, 10))

#tC = big_time_hom_rep_rational(hom_rep_combinatorial, 6, 12, 16, 128)
#print('time with combin: ' + str(tC))
#2.61

#tC = big_time_hom_rep_rational(hom_rep_combinatorial, 6, 12, 32, 128)
#print('time with combin: ' + str(tC))

#show_big_time_hom_rep_rational_all_methods(6, 12, 16, 128)

#show_big_time_hom_rep_rational_all_methods(6, 12, 32, 128)

#show_big_time_hom_rep_rational_all_methods(16, 48, 128, 128)

#show_big_time_hom_rep_rational_all_methods(16, 96, 256, 128)

show_big_time_hom_rep_rational_all_methods(32, 96, 256, 128)

#show_big_time_hom_rep_rational_all_methods(32, 96, 512, 128)

#show_big_time_hom_rep_rational_all_methods(48, 144, 256, 128)

#show_big_time_hom_rep_rational_all_methods(48, 144, 512, 128)

#show_big_time_hom_rep_rational_all_methods(64, 192, 512, 128)

#show_big_time_hom_rep_rational_all_methods(64, 192, 1024, 128)

