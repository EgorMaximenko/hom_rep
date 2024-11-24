

# Given a list of integers kappa,
# the following function returns the list of partial sums of kappa.
# For kappa = [5, 4, 2, 6], it returns [5, 9, 11, 17].

def sigma(kappa):
    n = len(kappa)
    s = [0] * n
    a = 0
    for j in range(n):
        a += kappa[j]
        s[j] = a
    return s


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


def list_with_repetitions_into_keys_with_counts(a):
    b = list(sorted(a))
    result = []
    n = len(b)
    c = 0
    for j in range(n):
        c += 1
        if (j + 1 >= n) or (b[j + 1] != b[j]):
            result.append((b[j], c))
            c = 0
    return result


def phi(kappa, beta):
    n = len(kappa)
    scur = 0
    scurrent = 0
    result = [0] * n
    for j in range(n):
        sprev = scur
        scur = sprev + kappa[j]
        result[j] = sum(beta[sprev : scur])
    return result


# tests


def test_number_of_multisets(n, m, verbose):
    M = list(lists_with_given_sum(n, m))
    result0 = len(M)
    result1 = binomial(n + m - 1, n - 1)
    logical_result = (result0 == result1)
    if verbose:
        print('test_number_of_multisets, n = %d, m = %d' % (n, m))
        print('M = ' + str(M))
        print('result0 = %d, result1 = %d' % (result0, result1))
        print('are equal? ' + str(logical_result))
    return logical_result


def big_test_number_of_multisets(nmax, mmax):
    result = True
    samples = [(n, m) for n in range(1, nmax + 1) for m in range(mmax + 1)]
    for n, m in samples:
        r0 = test_number_of_multisets(n, m, False)
        result = result and r0
        print('n = %d, m = %d, result = %s' % (n, m, str(r0)))
    return result


def test_phi_values(kappa, m):
    n = len(kappa)
    N = sum(kappa)
    domain = list(lists_with_given_sum(N, m))
    values = [phi(kappa, beta) for beta in domain]
    values_with_counts = list_with_repetitions_into_keys_with_counts(values)
    big_result = True
    for alpha, c in values_with_counts:
        c1 = prod(binomial(kappa[j] + alpha[j] - 1, alpha[j]) for j in range(n))
        result = (c == c1)
        big_result = big_result and result
    return big_result


def big_test_phi_values(nmax, kappa_max, mmax):
    result = True
    samples = []
    for n in range(1, nmax + 1):
        kappas = lists_with_bounded_components(n, 1, kappa_max)
        samples += [(kappa, m) for kappa in kappas for m in range(mmax + 1)]
    for kappa, m in samples:
        r0 = test_phi_values(kappa, m)
        print('kappa = %s, m = %d, r0 = %s' % (str(kappa), m, str(r0)))
        result = result and r0
    return result


#print(test_number_of_multisets(3, 2, True))

#print(big_test_number_of_multisets(8, 16))

#print(test_phi_values([3, 5, 4], 8))

print(big_test_phi_values(3, 6, 8))


#print(test_numeration_for_joined_lists([3, 5, 1]))
#print(big_test_numeration_for_joined_lists(5, 10))


