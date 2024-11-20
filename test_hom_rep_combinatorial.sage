
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


def hom_combinatorial(x, m):
    n = len(x)
    ks = lists_with_given_sum(n, m)
    R = x.base_ring()
    result = R(0)
    for k in ks:
        result += multi_power(x, k)
    return result


# kappa = multiplicities


def myvars(letter, n):
    varnames = ['y' + str(k) for k in range(n)]
    PR = PolynomialRing(QQ, varnames)
    return vector(PR, n, PR.gens())


def hom_with_repetitions_combinatorial_coef(kappa, k):
    n = len(kappa)
    result = 1
    for j in range(n):
        result *= binomial(kappa[j] + k[j] - 1, k[j])
    return result


def hom_with_repetitions_combinatorial(y, kappa, m):
    n = len(y)
    ks = lists_with_given_sum(n, m)
    R = y.base_ring()
    result = R(0)
    for k in ks:
        coef = hom_with_repetitions_combinatorial_coef(kappa, k)
        result += coef * multi_power(y, k)
    return result


def hom_with_repetitions_via_x_combinatorial(y, kappa, m):
    n = len(y)
    R = y.base_ring()
    N = sum(kappa)
    x_list = []
    for j in range(n):
        x_list += [y[j]] * kappa[j]
    x = vector(R, N, x_list)
    return hom_combinatorial(x, m)


def symbolic_test_hom_with_repetitions_combinatorial(kappa, m, verb):
    n = len(kappa)
    y = myvars('y', n)
    result0 = hom_with_repetitions_via_x_combinatorial(y, kappa, m)
    result1 = hom_with_repetitions_combinatorial(y, kappa, m)
    if verb:
        print('result0 = ', result0)
        print('result1 = ', result1)
    return result0 == result1


def random_symbolic_test_hom_with_repetitions():
    n = ZZ.random_element(1, 6)
    kappa = [0] * n
    for j in range(n):
        kappa[j] = ZZ.random_element(1, 6)
    m = ZZ.random_element(0, 6)
    print('kappa = ', kappa)
    print('m = ', m)
    return symbolic_test_hom_with_repetitions_combinatorial(kappa, m, True)


def big_symbolic_test_hom_with_repetitions(nmax, kappamax, mmax):
    tasks = []
    for n in range(1, nmax + 1):
        kappas = lists_with_bounded_components(n, 1, kappamax)
        for kappa in kappas:
            for m in range(mmax):
                tasks.append((kappa, m))
    print('len(tasks) = ', len(tasks))
    result = True
    for (kappa, m) in tasks:
        r0 = symbolic_test_hom_with_repetitions_combinatorial(kappa, m, False)
        print(kappa, m, r0)
        result = result and r0  
    return result


#print(symbolic_test_hom_with_repetitions_combinatorial([1, 2], 6, True))
#print(random_symbolic_test_hom_with_repetitions())

print(big_symbolic_test_hom_with_repetitions(4, 4, 8))

