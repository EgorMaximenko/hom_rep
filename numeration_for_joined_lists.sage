


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


# For kappa = [5, 2, 4], the following function returns
# [[0, 0], [0, 1], [0, 2], [0, 3], [0, 4], [1, 0], [1, 1], [2, 0], [2, 1], [2, 2], [2, 3]].

def list_of_pairs(kappa):
    n = len(kappa)
    result = [(q, r) for q in range(n) for r in range(kappa[q])]
    return list(result)


# For kappa = [3, 7, 6, 3], q = 2, r = 4, the following function returns 14.

def rho(kappa, q, r):
    s = sigma(kappa)
    base = 0 if q == 0 else s[q - 1]
    return base + r


# For kappa = [3, 7, 6, 3], k = 14, the following function returns (2, 4)

def gamma(kappa, k):
    n = len(kappa)
    s = sigma(kappa)
    qs = [-1] + [q for q in range(n) if s[q] <= k]
    q = max(qs) + 1
    base = 0 if q == 0 else s[q - 1]
    r = k - base
    return (q, r)


# Tests

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



def test_numeration_for_joined_lists(kappa):
    N = sum(kappa)
    Q = list_of_pairs(kappa)
    result = True
    for k in range(N):
        (q0, r0) = Q[k]
        (q1, r1) = gamma(kappa, k)
        k1 = rho(kappa, q1, r1)
        #print('k = %d, q0 = %d, r0 = %d, q1 = %d, r1 = %d, k1 = %d' % (k, q0, r0, q1, r1, k1))
        r0 = (q0 == q1) and (r0 == r1)
        r1 = (k == k1)
        local_result = r0 and r1
        result = result and local_result
    return result


def big_test_numeration_for_joined_lists(nmax, kappa_max):
    result = True
    for n in range(1, nmax + 1):
        kappas = lists_with_bounded_components(n, 1, kappa_max)
        for kappa in kappas:
            r0 = test_numeration_for_joined_lists(kappa)
            print(kappa, r0)
            result = result and r0
    return result


#print(test_numeration_for_joined_lists([3, 5, 1]))

print(big_test_numeration_for_joined_lists(5, 10))


