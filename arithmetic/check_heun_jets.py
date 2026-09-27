"""Exact rational checks of the finite-jet mechanism; no numerical spectral claims."""
from fractions import Fraction as Q


def coefficients(family, gamma, delta, alpha, beta, k, b, length):
    order = len(b) - 1
    eps = alpha + beta + 1 - gamma - delta
    c = [[Q(1)] + [Q(0)] * order]
    previous = [Q(0)] * (order + 1)
    for m in range(length):
        d = m * (m - 1 + gamma + delta)
        e, f = {
            'heun': (m * (m - 1 + gamma + eps), (m - 1 + alpha) * (m - 1 + beta)),
            'confluent': (Q(m), m - 1 + alpha),
            'reduced': (Q(0), Q(1)),
        }[family]
        now = c[-1]
        out = []
        for j in range(order + 1):
            value = sum(b[r] * now[j-r] for r in range(j+1)) + d * now[j]
            if j:
                value += e * now[j-1] - f * previous[j-1]
            out.append(value / ((m+1) * (m+gamma)))
        c.append(out)
        previous = now
    return c


def check(family, gamma, delta, k, order=5):
    alpha, beta = Q(5, 7), Q(11, 13)
    b = [-k * (k - 1 + gamma + delta)]
    for j in range(1, order+1):
        trial = b + [Q(0)]
        zero = coefficients(family, gamma, delta, alpha, beta, k, trial, k+j+1)[-1][j]
        trial[-1] = Q(1)
        one = coefficients(family, gamma, delta, alpha, beta, k, trial, k+j+1)[-1][j]
        assert one != zero
        b.append(-zero / (one-zero))
    c = coefficients(family, gamma, delta, alpha, beta, k, b, k+order+5)
    for j in range(order+1):
        assert all(c[l][j] == 0 for l in range(k+j+1, len(c)))
    return b


if __name__ == '__main__':
    total = 0
    for family in ('heun', 'confluent', 'reduced'):
        for gamma, delta in ((Q(2,3), Q(4,5)), (Q(1,3), Q(2,3))):
            for k in range(4):
                check(family, gamma, delta, k)
                total += 1
    print(f'PASS: {total} exact rational cases, three families, k=0..3, orders 0..5.')
    print('Includes gamma+delta=1 and its k=0 double hypergeometric-parameter case.')
