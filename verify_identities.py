"""Exact finite coefficient checks for identities in the revised report.

Run with Python 3; no third-party dependencies. These are regression checks
for transcriptions and coefficient extractions, not proofs of infinite identities.
"""

from functools import lru_cache
from math import isqrt

from verify_completion import multiply, rank_counts


LIMIT = 120


def product(exponents, limit=LIMIT):
    coefficients = [1] + [0] * limit
    for part, exponent in sorted(exponents.items()):
        for _ in range(abs(exponent)):
            if exponent > 0:
                for n in range(limit, part - 1, -1):
                    coefficients[n] -= coefficients[n - part]
            else:
                for n in range(part, limit + 1):
                    coefficients[n] += coefficients[n - part]
    return coefficients


@lru_cache(None)
def eta_cached(items, limit):
    exponents = {}
    for step, power in items:
        for part in range(step, limit + 1, step):
            exponents[part] = exponents.get(part, 0) + power
    return product(exponents, limit)


def eta(powers, limit=LIMIT):
    return eta_cached(tuple(sorted(powers.items())), limit).copy()


def j_product(factors, euler_powers=None, limit=LIMIT):
    """Product of J_(a,b)^power factors, with optional J_b powers."""
    exponents = {}
    for a, step, power in factors:
        for start in (a, step-a, step):
            for part in range(start, limit+1, step):
                exponents[part] = exponents.get(part, 0) + power
    for step, power in (euler_powers or {}).items():
        for part in range(step, limit+1, step):
            exponents[part] = exponents.get(part, 0) + power
    return product(exponents, limit)


def combination(*terms, limit=LIMIT):
    result = [0] * (limit + 1)
    for coefficient, shift, series in terms:
        for n in range(min(len(series), limit + 1 - shift)):
            result[n + shift] += coefficient * series[n]
    return result


def check(name, left, right, modulus=None):
    assert len(left) == len(right), name
    for n, (a, b) in enumerate(zip(left, right)):
        assert (a == b if modulus is None else (a - b) % modulus == 0), (
            name, n, a, b, modulus
        )
    print(f"{name}: checked through q^{len(left)-1}" +
          (f" modulo {modulus}" if modulus else ""))


def cubic_theta(step=1, limit=LIMIT):
    result = [0] * (limit + 1)
    bound = isqrt(2 * limit // step) + 1
    for m in range(-bound, bound + 1):
        for n in range(-bound, bound + 1):
            exponent = step * (m*m + m*n + n*n)
            if exponent <= limit:
                result[exponent] += 1
    return result


def main():
    p = eta({1: -1}, 7 * LIMIT + 5)
    check("Ramanujan 5-dissection", p[4:5*LIMIT+5:5],
          combination((5, 0, eta({5: 5, 1: -6}))))
    check("Ramanujan 7-dissection", p[5::7], combination(
        (7, 0, eta({7: 3, 1: -4})), (49, 1, eta({7: 7, 1: -8}))))

    for t in (1, 2, 3):
        check(f"f_{t}^3", eta({t: 3}), eta({3*t: 1}), 3)
        check(f"f_{t}^9", eta({t: 9}), eta({3*t: 3}), 9)

    check("Cubic reciprocal dissection", eta({1: -1, 2: -1}), combination(
        (1, 0, multiply(cubic_theta(6), eta({9: 3, 3: -4, 6: -3}), LIMIT)),
        (1, 1, multiply(cubic_theta(3), eta({18: 3, 3: -3, 6: -4}), LIMIT)),
        (3, 2, eta({9: 3, 18: 3, 3: -4, 6: -4}))))
    check("Cubic product dissection", eta({1: 1, 2: 1}), combination(
        (1, 0, eta({6: 1, 9: 4, 3: -1, 18: -2})),
        (-1, 1, eta({9: 1, 18: 1})),
        (-2, 2, eta({3: 1, 18: 4, 6: -1, 9: -2}))))

    check("Psi dissection", eta({2: 2, 1: -1}), combination(
        (1, 0, eta({6: 1, 9: 2, 3: -1, 18: -1})),
        (1, 1, eta({18: 2, 9: -1}))))
    check("Hirschhorn dissection", eta({2: 1, 1: -2}), combination(
        (1, 0, eta({6: 4, 9: 6, 3: -8, 18: -3})),
        (2, 1, eta({6: 3, 9: 3, 3: -7})),
        (4, 2, eta({6: 2, 18: 3, 3: -6}))))
    check("f_2^5/f_1^4 dissection", eta({2: 5, 1: -4}), combination(
        (1, 0, eta({6: 6, 9: 10, 3: -10, 18: -5})),
        (4, 1, eta({6: 5, 9: 7, 3: -9, 18: -2})),
        (9, 2, eta({6: 4, 9: 4, 18: 1, 3: -8})),
        (10, 3, eta({6: 3, 9: 1, 18: 4, 3: -7})),
        (4, 4, eta({6: 2, 18: 7, 3: -6, 9: -2}))))
    check("U(q)", combination(
        (1, 0, eta({2: 4, 3: 8, 1: -8, 6: -4})),
        (1, 1, eta({2: 1, 6: 5, 1: -5, 3: -1}))), [1]+[0]*LIMIT, 9)

    # Enough exact b(n) values for the coefficient extractions below.
    samples = 24
    b = eta({1: -2, 2: -2}, 81 * samples + 61)
    check("Lin b(9n+7)", [b[9*n+7] for n in range(LIMIT+1)], combination(
        (18, 0, eta({1: 1, 2: 1, 3: 7, 6: -1})),
        (18, 1, eta({1: 1, 2: 1, 6: 7, 3: -1})),
        (-9, 0, eta({3: 2, 6: 2}))), 27)
    check("Extracted b(27n+7), modulo 27",
          [b[27*n+7] for n in range(samples+1)], combination(
              (18, 0, eta({3: 6, 6: -2}, samples)),
              (-36, 1, eta({6: 6, 3: -2}, samples)),
              (-9, 0, eta({3: 1, 6: 1, 1: -1, 2: -1}, samples)),
              limit=samples), 27)
    b27 = [b[27*n+7] for n in range(samples+1)]
    for expression in ({3: 2, 6: 2, 1: -4, 2: -4},
                       {3: 2, 2: 5, 1: -4, 6: -1}):
        check("b(27n+7), modulo 81", b27,
              [9*x for x in eta(expression, samples)], 81)
    check("Lin b(81n+7)", [b[81*n+7] for n in range(samples+1)],
          [9*x for x in eta({2: 1, 3: 2, 6: -1}, samples)], 81)
    check("Lin b(81n+34)", [b[81*n+34] for n in range(samples+1)],
          [36*x for x in eta({1: 1, 6: 2, 3: -1}, samples)], 81)
    check("Lin b(81n+61)", [b[81*n+61] for n in range(samples+1)],
          [0]*(samples+1), 243)
    check("Chern b(81n+61)", [b[81*n+61] for n in range(samples+1)],
          [0]*(samples+1), 729)

    # Check the product-to-theta simplification used in Chapter 4.
    quotient = j_product(
        ((2, 12, 1), (6, 12, 2), (1, 12, -2), (5, 12, -2)), {12: 3})
    phi = [0]*(LIMIT+1)
    phi[0] = 1
    for k in range(1, isqrt(LIMIT)+1):
        phi[k*k] = 2
    squared = multiply(phi, phi, LIMIT)
    twice_theta = [squared[n] + (squared[n//3] if n%3 == 0 else 0)
                   for n in range(LIMIT+1)]
    check("Barman-Sachdeva theta-product identity",
          [2*x for x in quotient], twice_theta)

    # Check the full Mao identity, including the two other residue classes.
    # Multiply by 2q to keep every intermediate series integral and nonnegative
    # in degree; the individual Laurent terms at q^(-1) must cancel.
    first_sum = [0]*(LIMIT+1)
    for j in range(-isqrt(LIMIT), isqrt(LIMIT)+1):
        start, step, sign = 18*j*j + 9*j, 18*j + 3, (-1 if j % 2 else 1)
        if step < 0:
            start, step, sign = start-step, -step, -sign
        for n in range(start, LIMIT+1, step):
            first_sum[n] += sign
    twice_last_sum = [1]+[0]*LIMIT
    for j in range(1, isqrt(LIMIT)+1):
        for k, n in enumerate(range(18*j*j + 9*j, LIMIT+1, 18*j)):
            twice_last_sum[n] += 4*(-1)**(j+k)
    reciprocal = j_product(((9, 36, -1),))
    denominator = ((3, 36, -2), (9, 36, -1), (15, 36, -2))
    first_product = j_product(((6, 36, 2), (18, 36, 1)) + denominator, {36: 3})
    second_product = j_product(((6, 36, 1), (18, 36, 2)) + denominator, {36: 3})
    mao = combination(
        (2, 1, multiply(reciprocal, first_sum, LIMIT)),
        (2, 2, first_product), (1, 0, second_product),
        (-1, 0, multiply(reciprocal, twice_last_sum, LIMIT)))
    ranks = rank_counts(LIMIT-1)
    direct = [0] + [2*(a+b-c-d) for a, b, c, d in zip(*ranks[:4])]
    check("Full Mao identity, multiplied by 2q", mao, direct)


if __name__ == "__main__":
    main()
