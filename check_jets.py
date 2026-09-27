"""Exact rational checks of the polynomial-jet argument (Python standard library).

This is a finite sanity check, not a substitute for the all-orders analytic proof.
Builds perturbative eigenpairs by independent linear algebra, then compares
them with the paper's coefficient recurrence. No floating-point arithmetic.
"""
from fractions import Fraction as Q
import json


def solve(a, b):
    n = len(b)
    a = [[Q(v) for v in row] + [Q(v)] for row, v in zip(a, b)]
    for col in range(n):
        pivot = next(row for row in range(col, n) if a[row][col])
        a[col], a[pivot] = a[pivot], a[col]
        v = a[col][col]
        a[col] = [x / v for x in a[col]]
        for row in range(n):
            if row != col:
                v = a[row][col]
                a[row] = [x - v*y for x, y in zip(a[row], a[col])]
    return [row[-1] for row in a]


def model(family, gamma, delta, alpha, beta):
    epsilon = alpha + beta + 1 - gamma - delta
    d = lambda m: m * (m - 1 + gamma + delta)
    if family == "heun":
        e = lambda m: m * (m - 1 + gamma + epsilon)
        f = lambda m: (m - 1 + alpha) * (m - 1 + beta)
    elif family == "confluent":
        e = lambda m: Q(m)
        f = lambda m: m - 1 + alpha
    else:
        e = lambda m: Q(0)
        f = lambda m: Q(1)
    return d, e, f


def jets(family, gamma, delta, alpha, beta, k, order):
    d, e, f = model(family, gamma, delta, alpha, beta)
    base = [Q(1)]
    for m in range(k):
        base.append((d(m)-d(k))*base[-1]/((m+1)*(m+gamma)))
    polynomials = [base]
    eigenvalue = [-d(k)]
    for j in range(1, order+1):
        degree = k+j
        rhs = [Q(0)]*(degree+1)
        for m, v in enumerate(polynomials[-1]):
            rhs[m] -= e(m)*v
            rhs[m+1] += f(m+1)*v
        for i in range(1, j):
            for m, v in enumerate(polynomials[j-i]):
                rhs[m] -= eigenvalue[i]*v
        # (L0-Dk) p_j + b_j p_0 = rhs, with p_j(0)=0.
        a = [[Q(0)]*(degree+2) for _ in range(degree+2)]
        for m in range(degree+1):
            a[m][m] = d(m)-d(k)
            if m:
                a[m-1][m] = -m*(m-1+gamma)
        for m, v in enumerate(base):
            a[m][-1] = v
        a[-1][0] = 1
        result = solve(a, rhs+[Q(0)])
        polynomials.append(result[:-1])
        eigenvalue.append(result[-1])

    # Direct residual verification, including one degree beyond the jet bound.
    for j in range(order+1):
        residual = [Q(0)]*(k+order+2)
        for m, v in enumerate(polynomials[j]):
            residual[m] += (d(m)-d(k))*v
            if m:
                residual[m-1] -= m*(m-1+gamma)*v
        if j:
            for m, v in enumerate(polynomials[j-1]):
                residual[m] += e(m)*v
                residual[m+1] -= f(m+1)*v
        for i in range(1, j+1):
            for m, v in enumerate(polynomials[j-i]):
                residual[m] += eigenvalue[i]*v
        assert not any(residual), (family, k, j, residual)

    # Independently generate c_m(B(s),s) in Q[s]/(s^(order+1)).
    coefficients = [[Q(1)]+[Q(0)]*order]
    previous = [Q(0)]*(order+1)
    for m in range(k+order+5):
        current = coefficients[-1]
        nxt = [sum(eigenvalue[i]*current[r-i] for i in range(r+1))
               + d(m)*current[r] for r in range(order+1)]
        for r in range(1, order+1):
            nxt[r] += e(m)*current[r-1]-f(m)*previous[r-1]
        nxt = [x/((m+1)*(m+gamma)) for x in nxt]
        coefficients.append(nxt)
        previous = current
    for m, coefficient in enumerate(coefficients):
        for j in range(order+1):
            expected = polynomials[j][m] if m < len(polynomials[j]) else Q(0)
            assert coefficient[j] == expected, (family, k, m, j)
    for j in range(1, order+1):
        assert not any(coefficients[k+j+1][:j+1])

    # The explicit first-order formula in the source, with B=-D-corrections.
    first = e(k) + (k+1)*(k+gamma)*f(k+1)/(d(k)-d(k+1))
    if k:
        first += k*(k-1+gamma)*f(k)/(d(k)-d(k-1))
    assert eigenvalue[1] == -first
    return eigenvalue


if __name__ == "__main__":
    parameter_sets = [
        (Q(1, 2), Q(2, 3), Q(3, 4), Q(5, 6)),
        # Allowed exceptional case gamma+delta=1, including k=0.
        (Q(1, 3), Q(2, 3), Q(2, 5), Q(4, 7)),
        # Vanishing F_1 in Heun and confluent cases is allowed.
        (Q(1, 2), Q(3, 2), Q(0), Q(2, 3)),
        # Non-real-positivity assumptions are not needed; signs can vary.
        (Q(-1, 2), Q(7, 3), Q(-3, 2), Q(5, 4)),
    ]
    count = 0
    examples = {}
    for family in ("heun", "confluent", "reduced"):
        for parameters in parameter_sets:
            for k in range(4):
                result = jets(family, *parameters, k, 6)
                count += 1
                if parameters == parameter_sets[0] and k == 0:
                    examples[family] = [str(x) for x in result[:4]]
    print(json.dumps({"status": "PASS", "cases": count,
                      "order": 6, "arithmetic": "exact rational",
                      "checks": ["polynomial eigenpair residuals",
                                 "degree bound k+j", "coefficient recurrence",
                                 "finite-root jet vanishing",
                                 "source first-order formula"],
                      "example_B_coefficients_orders_0_to_3": examples}, indent=2))
