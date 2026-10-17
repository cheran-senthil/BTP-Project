"""Exact checks for the elementary completion of the chapter 4 inequality.

Run with Python 3; no dependencies. Finite checks corroborate the proof in
chapter4.tex and mao-rank-inequality.typ; they do not replace the proof.
"""

from math import isqrt


def rank_counts(limit):
    """Count directly by largest part and number of parts modulo 6."""
    by_length = [[0] * (limit + 1) for _ in range(6)]
    by_length[0][0] = 1
    by_rank = [[0] * (limit + 1) for _ in range(6)]
    by_rank[0][0] = 1
    for largest in range(1, limit + 1):
        previous = [row.copy() for row in by_length]
        for n in range(largest, limit + 1):
            for length in range(6):
                source = previous if largest % 2 else by_length
                by_length[length][n] += source[(length - 1) % 6][n - largest]
        for length in range(6):
            rank = ((largest + 1) // 2 - length) % 6
            for n in range(largest, limit + 1):
                by_rank[rank][n] += by_length[length][n] - previous[length][n]
    return by_rank


def root_of_unity_series(limit):
    """R_2(exp(pi*i/3);q) = sum q^(r*r) (-q;q)_(2r)/(-q^6;q^6)_r."""
    term = [1] + [0] * limit
    result = [1] + [0] * limit
    for r in range(1, isqrt(limit) + 1):
        degree = limit - r * r
        term = term[:degree + 1]
        for shift in (2 * r - 1, 2 * r):
            for n in range(degree, shift - 1, -1):
                term[n] += term[n - shift]
        for n in range(6 * r, degree + 1):
            term[n] -= term[n - 6 * r]
        for n, coefficient in enumerate(term):
            result[n + r * r] += coefficient
    return result


def allowed_partitions(limit):
    result = [1] + [0] * limit
    for part in range(1, limit + 1):
        if part % 4 != 2:
            for n in range(part, limit + 1):
                result[n] += result[n - part]
    return result


def multiply(a, b, limit):
    result = [0] * (limit + 1)
    for i, x in enumerate(a):
        if x:
            for j in range(min(len(b), limit + 1 - i)):
                result[i + j] += x * b[j]
    return result


def lambert_series(limit):
    result = [0] * (limit + 1)
    for r in range(1, isqrt(limit) + 1):
        for j, n in enumerate(range(r * (2 * r + 1), limit + 1, 2 * r)):
            result[n] += (-1) ** (r + j + 1)
    return result


def theta_numerator(limit):
    """(phi(q)^2 + phi(q^3)^2 - 2)/4, computed as lattice counts."""
    r2 = [0] * (limit + 1)
    for a in range(-isqrt(limit), isqrt(limit) + 1):
        bound = isqrt(limit - a * a)
        for b in range(-bound, bound + 1):
            r2[a * a + b * b] += 1
    result = [0] * (limit + 1)
    for n in range(1, limit + 1):
        numerator = r2[n] + (r2[n // 3] if n % 3 == 0 else 0)
        assert numerator % 4 == 0
        result[n] = numerator // 4
    return result


def main():
    limit = 3822
    direct_limit = 300
    ranks = rank_counts(direct_limit)
    d = root_of_unity_series(limit)
    for n in range(direct_limit + 1):
        assert ranks[1][n] == ranks[5][n]
        assert ranks[2][n] == ranks[4][n]
        assert d[n] == ranks[0][n] + ranks[1][n] - ranks[2][n] - ranks[3][n]
    assert min(d) > 0

    degree = (limit - 2) // 3 + 1
    p = allowed_partitions(degree)
    lambert = lambert_series(degree)
    correction = multiply(p, lambert, degree)
    assert min(correction) >= 0

    # Verify each paired summand's explicit product formula.
    for r in range(1, isqrt(degree) + 1, 2):
        pair = [0] * (degree + 1)
        for sign, index in ((1, r), (-1, r + 1)):
            start = index * (2 * index + 1)
            for j, n in enumerate(range(start, degree + 1, 2 * index)):
                pair[n] += sign * (-1) ** j
        lhs = multiply(p, pair, degree)
        rhs = [0] * (degree + 1)
        for shift, removed in ((0, 4 * r + 3), (2 * r + 2, 4 * r + 1)):
            product = p.copy()
            for part in (r, 2 * r + 2, removed):
                for n in range(degree, part - 1, -1):
                    product[n] -= product[n - part]
            assert min(product) >= 0
            for part in (4 * r, 4 * r + 4):
                for n in range(part, degree + 1):
                    product[n] += product[n - part]
            for n in range(degree, r - 1, -1):
                product[n] += product[n - r]
            offset = r * (2 * r + 1) + shift
            for n in range(degree + 1 - offset):
                rhs[n + offset] += product[n]
        assert lhs == rhs
        assert min(lhs) >= 0

    bracket = theta_numerator(degree)
    for n in range(degree // 3 + 1):
        bracket[3 * n] += 2 * lambert[n]
    pq3 = [p[n // 3] if n % 3 == 0 else 0 for n in range(degree + 1)]
    formula = multiply(pq3, bracket, degree)
    for n in range(degree):
        assert formula[n + 1] == d[3 * n + 2]
        assert d[3 * n + 2] >= p[n // 3] >= 1

    print(f"Direct rank counts agree through n={direct_limit}.")
    print(f"d(n)>0 for all 0<=n<={limit}; minimum={min(d)}.")
    print(f"Chapter 4 generating function agrees through q^{degree - 1}.")
    print(f"Paired-product identities and positivity agree through q^{degree}.")
    print("Lower bound holds throughout the checked range.")
    print("First ten missing-case values d(9m+8):", [d[9*m + 8] for m in range(10)])
    print("Corresponding lower bounds:", p[:10])


if __name__ == "__main__":
    main()
