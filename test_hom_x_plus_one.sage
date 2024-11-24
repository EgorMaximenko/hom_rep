# This program is a part of the project
# "Complete homogeneous symmetric polynomials with repeating variables"
# by Luis Angel Gonzalez Serrano and Egor A. Maximenko (2024).

# In this program, we test the following polynomial identity:
# h_m(x_1+1,\ldots,x_n+1) = \sum_{k=0}^m \binom{n + m - 1}{m - k} h_k(x_1,\ldots,x_n).

# This formula was found by Gomezllata Marmolejo, 2022 (see Lemma 3.5).
# https://ora.ox.ac.uk/objects/uuid:322f5a34-f68b-4766-b0c8-774f26027b36
# It is also a particular case of well-known formulas for Schur polynomials.


def prod_diff_this_minus_others(x, j):
    n = len(x)
    ind_others = list(range(j)) + list(range(j + 1, n))
    return prod(x[j] - x[k] for k in ind_others)


def hom_via_geom_progr(x, m):
    n = len(x)
    result = x[0].parent().zero()
    for j in range(n):
        numer = x[j] ** (m + n - 1)
        denom = prod_diff_this_minus_others(x, j)
        result += numer / denom
    return result


def hom_x_plus_one_lhs(x, m):
    n = len(x)
    F = x[0].parent()
    myone = x[0] ** 0
    y = vector(F, n)
    for j in range(n):
        y[j] = x[j] + myone
    return hom_via_geom_progr(y, m)


def hom_x_plus_one_rhs(x, m):
    n = len(x)
    F = x[0].parent()
    result = F(0)
    for k in range(m + 1):
        coef = binomial(n + m - 1, m - k)
        result += coef * hom_via_geom_progr(x, k)
    return result


def test_hom_x_plus_one(n, m, verbose):
    varnames = ['x' + str(k) for k in range(n)]
    PR = PolynomialRing(QQ, varnames)
    x = PR.gens()
    result0 = hom_x_plus_one_lhs(x, m)
    result1 = hom_x_plus_one_rhs(x, m)
    if verbose:
        print('result0 = ', result0)
        print('result1 = ', result1)
    return result0 == result1


def big_test_hom_x_plus_one(nmax, mmax):
    examples = [(n, m) for n in range(1, nmax + 1) for m in range(mmax + 1)]
    big_result = True
    for n, m in examples:
        r = test_hom_x_plus_one(n, m, False)
        big_result = big_result and r
        print('n = ' + str(n) + ', m = ' + str(m) + ', r = ' + str(r))
    return big_result


#print(test_hom_x_plus_one(3, 4, True))

print(big_test_hom_x_plus_one(7, 20))

