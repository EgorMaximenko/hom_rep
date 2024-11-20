# This program is a part of the project
# "Complete homogeneous symmetric polynomials with repeating variables"
# by Luis Angel Gonzalez Serrano and Egor A. Maximenko (2024).

# In this program, we test the decomposition of 1 / \prod_{j=1}^n (1 - y_j t)^{\kappa_j}
# into a linear combination of elementary fractions of the form 1 / (1 - y_j t)^r.


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


def multi_power(a, k):
    n = len(a)
    return prod([a[j] ** k[j] for j in range(n)])


def myvars_yt(n):
    varnames = ['y' + str(k) for k in range(n)]
    varnames += ['t']
    PR = PolynomialRing(QQ, varnames)
    y = vector(PR, n, PR.gens()[: n])
    t = PR.gens()[n]
    return y, t


# kappa = multiplicities


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


def fraction1(y, kappa, t):
    n = len(y)
    R = t.parent()
    numer = R.one()
    denom = R.one()
    for k in range(n):
        denom = denom * ((1 - y[k] * t) ** kappa[k])
    return numer / denom


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


def fraction1_decomposition(y, kappa, t):
    n = len(y)
    F = FractionField(t.parent())
    result = F.zero()
    for s in range(n):
        for r in range(1, kappa[s] + 1):
            coef = A_coef(y, kappa, s, r)
            denom = (1 - y[s] * t) ** r
            term = coef / denom
            result += term
    return result


def test_fraction1_decomposition(kappa, verb):
    n = len(kappa)
    y, t = myvars_yt(n)
    result0 = fraction1(y, kappa, t)
    result1 = fraction1_decomposition(y, kappa, t)
    dif01 = result0 - result1
    result_eq01 = dif01.is_zero()
    if verb:
        print('result0 = ', result0)
        print('result1 = ', result1)
        print('are equal?', result_eq01)
    return result_eq01


def random_test_fraction1_decomposition():
    n = ZZ.random_element(1, 5)
    kappa = [0] * n
    for j in range(n):
        kappa[j] = ZZ.random_element(1, 5)
    print('random_test_fraction1_decomposition, kappa = ', kappa)
    return test_fraction1_decomposition(kappa, True)


def big_test_fraction1_decomposition(nmax, mmax):
    result = True
    for n in range(1, nmax + 1):
        kappas = lists_with_bounded_components(n, 1, mmax)
        for kappa in kappas:
            r0 = test_fraction1_decomposition(kappa, False)
            print(kappa, r0)
            result = result and r0
    return result


#print(test_fraction1_decomposition([3], True))
#print(test_fraction1_decomposition([4, 3], True))
#print(random_test_fraction1_decomposition())
print(big_test_fraction1_decomposition(4, 5))
