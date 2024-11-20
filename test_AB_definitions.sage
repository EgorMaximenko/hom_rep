
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


def myvars(letter, n):
    varnames = [letter + str(k) for k in range(n)]
    PR = PolynomialRing(QQ, varnames)
    y = vector(PR, n, PR.gens())
    return y


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


def A_coef_explicit(y, kappa, s, r):
    n = len(y)
    F = FractionField(y.base_ring())
    ind_reduced = list(range(s)) + list(range(s + 1, n))
    y_reduced = list([y[d] for d in ind_reduced])
    kappa_reduced = list([kappa[d] for d in ind_reduced])   
    ks = lists_with_given_sum(n - 1, kappa[s] - r)
    sum1 = F.zero()
    for k in ks:
        prod1 = F.one()
        for d in range(n - 1):
            coef1 = binomial(kappa_reduced[d] + k[d] - 1, k[d])
            numer1 = (y[s] ** kappa_reduced[d]) * (y_reduced[d] ** k[d])
            denom1 = (y_reduced[d] - y[s]) ** (kappa_reduced[d] + k[d])
            prod1 *= coef1 * numer1 / denom1
        sum1 += prod1
    sign1 = (-1) ** (sum(kappa) - kappa[s])
    return sign1 * sum1


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


def B_coef_explicit(y, kappa, s, r):
    n = len(y)
    F = FractionField(y.base_ring())
    ind_reduced = list(range(s)) + list(range(s + 1, n))
    y_reduced = list([y[d] for d in ind_reduced])
    kappa_reduced = list([kappa[d] for d in ind_reduced])
    ks = lists_with_given_sum(n - 1, kappa[s] - r)
    sum1 = F.zero()
    for k in ks:
        prod1 = F.one()
        for d in range(n - 1):
            coef1 = binomial(kappa_reduced[d] + k[d] - 1, k[d])
            denom1 = (y_reduced[d] - y[s]) ** (kappa_reduced[d] + k[d])
            prod1 *= coef1 / denom1
        sum1 += prod1
    sign1 = (-1) ** (sum(kappa) - kappa[s])
    return sign1 * sum1


def A_via_B(y, kappa, s, r):
    n = len(y)
    F = FractionField(y.base_ring())
    ind_reduced = list(range(s)) + list(range(s + 1, n))
    y_reciprocal = vector(F, n, [1 / y[j] for j in range(n)])
    factor0 = (-1) ** (sum(kappa) + r)
    factor1 = y[s] ** (r - kappa[s])
    factor2 = F.one()
    for j in ind_reduced:
        factor2 *= y[j] ** (- kappa[j])
    factor3 = B_coef(y_reciprocal, kappa, s, r)
    return F(factor0 * factor1 * factor2 * factor3)


def test_AB_definition_particular(kappa, s, r, verb):
    n = len(kappa)
    y = myvars('y', n)
    result_A0 = A_coef(y, kappa, s, r)
    result_A1 = A_coef_explicit(y, kappa, s, r)
    result_A2 = A_via_B(y, kappa, s, r)
    result_B0 = B_coef(y, kappa, s, r)
    result_B1 = B_coef_explicit(y, kappa, s, r)
    dif_A01 = result_A0 - result_A1
    dif_A02 = result_A0 - result_A2
    result_A = dif_A01.is_zero() and dif_A02.is_zero()
    dif_B01 = result_B0 - result_B1
    result_B = dif_B01.is_zero()
    result_AB = result_A and result_B
    if verb:
        print('test_AB_definition_particular, kappa=%s, s=%d, r=%d' % (str(kappa), s, r))
        print('result_A0 = ', result_A0)
        print('result_A1 = ', result_A1)
        print('result_A2 = ', result_A2)
        print('result_B0 = ', result_B0)
        print('result_B1 = ', result_B1)
        print('are equal?', result_AB)
    return result_AB


def test_AB_definition(kappa, verb):
    n = len(kappa)
    y = myvars('y', n)
    total_result = True
    for s in range(n):
        for r in range(kappa[s]):
            result_A0 = A_coef(y, kappa, s, r)
            result_A1 = A_coef_explicit(y, kappa, s, r)
            result_A2 = A_via_B(y, kappa, s, r)
            result_B0 = B_coef(y, kappa, s, r)
            result_B1 = B_coef_explicit(y, kappa, s, r)
            dif_A01 = result_A0 - result_A1
            dif_A02 = result_A0 - result_A2
            result_A = dif_A01.is_zero() and dif_A02.is_zero()
            dif_B01 = result_B0 - result_B1
            result_B = dif_B01.is_zero()
            result_AB = result_A and result_B
            total_result = total_result and result_AB
            if verb:
                print('test_AB_definition_particular, kappa=%s, s=%d, r=%d' % (str(kappa), s, r))
                print('result_A0 = ', result_A0)
                print('result_A1 = ', result_A1)
                print('result_A2 = ', result_A2)
                print('result_B0 = ', result_B0)
                print('result_B1 = ', result_B1)
                print('are equal?', result_AB)
    return total_result


def random_test_AB_definition():
    n = ZZ.random_element(1, 5)
    kappa = [0] * n
    for j in range(n):
        kappa[j] = ZZ.random_element(1, 5)
    return test_AB_definition(kappa, True)


def big_test_AB_definition(nmax, mmax):
    result = True
    for n in range(1, nmax + 1):
        kappas = lists_with_bounded_components(n, 1, mmax)
        for kappa in kappas:
            r0 = test_AB_definition(kappa, False)
            print(kappa, r0)
            result = result and r0
    return result


#print(test_AB_definition_particular([3, 2], 1, 1, True))
#print(test_AB_definition([3, 2], True))
#print(random_test_AB_definition())
print(big_test_AB_definition(4, 5))

