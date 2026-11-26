#!/usr/bin/env python3
"""
verify.py -- exact-arithmetic verification of every lemma, formula and table
value in main.tex ("A floor-ceiling Wallis-type product for pi and a mod 4
dichotomy").

Usage:
    python3 verify.py            # all checks used by the paper (prints PASS/FAIL)
    python3 verify.py --audit    # additionally audit claims of the ORIGINAL
                                 # manuscript (reported as INFO, not PASS/FAIL)
    python3 verify.py --tables   # print the computed table rows (LaTeX)

Conventions (as in the paper):
    L(n) = floor(n^2/mu),  U(n) = ceil(n^2/mu),
    dL(n) = L(n+1) - L(n), dU(n) = U(n+1) - U(n),
    P_N(mu) = prod_{n=mu}^{N} dL(n)/dU(n).

Identities are checked with Python integers and fractions.Fraction only.
Limits (values near pi/4 or 1) are evaluated with decimal.Decimal at 60
significant digits; each table value is a product of at most N factors, so the
accumulated relative rounding error is below 2*N*10^-59, far below the 6 decimal
places reported in the tables.
"""

import sys
import time
from fractions import Fraction
from decimal import Decimal, getcontext

getcontext().prec = 60
PI = Decimal("3.14159265358979323846264338327950288419716939937510582097494")

MU_MAX = 300      # lemmas checked for 1 <= mu <= MU_MAX
GAMMA_MAX = 10    # ... and 0 <= gamma <= GAMMA_MAX

RESULTS = []


def check(name, ok, detail=""):
    RESULTS.append(ok)
    print(f"[{'PASS' if ok else 'FAIL'}] {name}" + (f"  ({detail})" if detail else ""))
    sys.stdout.flush()


def info(name, detail):
    print(f"[INFO] {name}: {detail}")


# ---------------------------------------------------------------- basics
def L(n, mu):
    return (n * n) // mu


def U(n, mu):
    return -((-n * n) // mu)


def dL(n, mu):
    return L(n + 1, mu) - L(n, mu)


def dU(n, mu):
    return U(n + 1, mu) - U(n, mu)


def factorize(m):
    f, p = {}, 2
    while p * p <= m:
        while m % p == 0:
            f[p] = f.get(p, 0) + 1
            m //= p
        p += 1
    if m > 1:
        f[m] = f.get(m, 0) + 1
    return f


def M_of(mu):
    """M = prod p^ceil(e/2): the least positive integer whose square mu divides."""
    M = 1
    for p, e in factorize(mu).items():
        M *= p ** ((e + 1) // 2)
    return M


def block(mu, g):
    """B_g(mu) = prod_{n = mu*g}^{mu*g + mu - 1} dL(n)/dU(n), exactly."""
    B = Fraction(1)
    for n in range(mu * g, mu * g + mu):
        B *= Fraction(dL(n, mu), dU(n, mu))
    return B


def wallis_factor(g):
    return Fraction(4 * g * (g + 1), (2 * g + 1) ** 2)


def P_decimal(mu, Ns, start=None):
    """Direct evaluation of P_N(mu) for every N in Ns (Decimal, 60 digits).
    Only factors with dL != dU are multiplied (the others equal 1 exactly)."""
    start = mu if start is None else start
    Ns = sorted(Ns)
    out, p, idx = {}, Decimal(1), 0
    l0, u0 = L(start, mu), U(start, mu)
    for n in range(start, Ns[-1] + 1):
        l1 = ((n + 1) * (n + 1)) // mu
        u1 = -((-(n + 1) * (n + 1)) // mu)
        a, b = l1 - l0, u1 - u0
        if a != b:
            p = p * Decimal(a) / Decimal(b)
        l0, u0 = l1, u1
        if n == Ns[idx]:
            out[n] = p
            idx += 1
    return out


def fmt(x, d=6):
    return f"{x:.{d}f}"


# ===================================================================
# 1. Lemma A: dL(n) = 2g + dL(d), dU(n) = 2g + dU(d) for n = mu g + d
# ===================================================================
def check_lemma_A():
    ok, cnt = True, 0
    for mu in range(1, MU_MAX + 1):
        for g in range(0, GAMMA_MAX + 1):
            for d in range(mu):
                n = mu * g + d
                # also the intermediate identities used in the proof
                if L(n, mu) != mu * g * g + 2 * g * d + L(d, mu):
                    ok = False
                if U(n, mu) != mu * g * g + 2 * g * d + U(d, mu):
                    ok = False
                if dL(n, mu) != 2 * g + dL(d, mu) or dU(n, mu) != 2 * g + dU(d, mu):
                    ok = False
                cnt += 1
    check("Lemma A (L,U shift and dL,dU = 2*gamma + local value)", ok,
          f"mu<={MU_MAX}, gamma<={GAMMA_MAX}, {cnt} pairs")


# ===================================================================
# 2. Lemma B: local values dL(d), dU(d) for 0 <= d < mu
# ===================================================================
def check_lemma_B():
    ok_cases, ok_ratio, ok_excl, ok_odd = True, True, True, True
    for mu in range(2, MU_MAX + 1):
        for d in range(mu):
            z0 = (d * d) % mu == 0
            z1 = ((d + 1) ** 2) % mu == 0
            f = (2 * d + 1) // mu
            a, b = dL(d, mu), dU(d, mu)
            if z0 and z1:
                ok_excl = False          # impossible for mu >= 2
            if (z0 or z1) and 2 * d + 1 == mu:
                ok_odd = False           # 2d+1 = mu cannot occur in cases (ii),(iii)
            if not z0 and not z1:
                if a != b:
                    ok_cases = False
            elif z0:
                if not (a == f and b == f + 1 and f in (0, 1)):
                    ok_cases = False
            else:
                if not (b == f and a == f + 1 and f in (0, 1)):
                    ok_cases = False
            # ratio formula for gamma >= 1
            for g in range(1, GAMMA_MAX + 1):
                r = Fraction(dL(mu * g + d, mu), dU(mu * g + d, mu))
                x = Fraction(2 * g, 2 * g + 1)
                y = Fraction(2 * g + 1, 2 * g + 2)
                if not z0 and not z1:
                    exp = Fraction(1)
                elif z0:
                    exp = x if 2 * d + 1 < mu else y
                else:
                    exp = 1 / x if 2 * d + 1 < mu else 1 / y
                if r != exp:
                    ok_ratio = False
    check("Lemma B: mu | d^2 and mu | (d+1)^2 never both hold (mu >= 2)", ok_excl)
    check("Lemma B: 2d+1 != mu whenever mu | d^2 or mu | (d+1)^2", ok_odd)
    check("Lemma B: local values dL(d), dU(d) in the three cases", ok_cases,
          f"2<=mu<={MU_MAX}")
    check("Lemma B: factor = 1, x, y, 1/x or 1/y as stated", ok_ratio,
          f"2<=mu<={MU_MAX}, 1<=gamma<={GAMMA_MAX}")


# ===================================================================
# 3. Proposition C: block product and the counts a, b
# ===================================================================
def check_prop_C():
    ok_M, ok_T, ok_ab, ok_B, ok_orig = True, True, True, True, True
    for mu in range(2, MU_MAX + 1):
        M = M_of(mu)
        T = mu // M
        # mu | d^2  <=>  M | d
        for d in range(mu):
            if ((d * d) % mu == 0) != (d % M == 0):
                ok_M = False
        if mu % M != 0 or M < 2:
            ok_M = False
        # T even <=> 4 | mu
        if (T % 2 == 0) != (mu % 4 == 0):
            ok_T = False
        a = sum(1 for j in range(T) if 2 * j * M + 1 < mu)
        b = sum(1 for j in range(1, T + 1) if 2 * j * M - 1 < mu)
        if a != (T + 1) // 2 or b != T // 2:
            ok_ab = False
        if a != (mu - 1) // (2 * M) + 1 or b != mu // (2 * M):
            ok_orig = False
        for g in range(1, GAMMA_MAX + 1):
            B = block(mu, g)
            exp = Fraction(1) if mu % 4 == 0 else wallis_factor(g)
            if B != exp or B != wallis_factor(g) ** (a - b):
                ok_B = False
    check("Prop C: mu | d^2 <=> M | d (M = prod p^ceil(e/2)), M >= 2", ok_M,
          f"2<=mu<={MU_MAX}")
    check("Prop C: T = mu/M is even <=> 4 | mu", ok_T)
    check("Prop C: a = ceil(T/2), b = floor(T/2)", ok_ab)
    check("Prop C: a = floor((mu-1)/(2M)) + 1, b = floor(mu/(2M)) (original form)", ok_orig)
    check("Prop C: B_gamma(mu) = 1 if 4|mu, 4g(g+1)/(2g+1)^2 otherwise", ok_B,
          f"2<=mu<={MU_MAX}, 1<=gamma<={GAMMA_MAX}")
    # mu = 1
    ok1 = all(dL(n, 1) == dU(n, 1) == 2 * n + 1 for n in range(0, 10000))
    check("mu = 1: dL(n) = dU(n) = 2n+1, every factor equals 1", ok1)


# ===================================================================
# 4. Lemma D: Wallis
# ===================================================================
def check_lemma_D():
    ok = True
    # exact identity R_G = W_{G+1} (2G+3)/(4G+4), W_n = prod 4k^2/(4k^2-1)
    W = Fraction(1)
    Ws = [Fraction(1)]
    for k in range(1, 502):
        W *= Fraction(4 * k * k, 4 * k * k - 1)
        Ws.append(W)
    R = Fraction(1)
    for G in range(1, 501):
        R *= wallis_factor(G)
        if R != Ws[G] * Fraction(G + 1, 2 * G + 1):
            ok = False
    check("Lemma D: R_G = W_G (G+1)/(2G+1) exactly", ok, "1<=G<=500")
    # the termwise identity in the original Lemma 5.8 is false:
    bad = all(wallis_factor(g) != Fraction(2 * g, 2 * g - 1) * Fraction(2 * g, 2 * g + 1)
              for g in range(1, 50))
    check("Lemma D: original termwise rewriting 2g(2g+2)/(2g+1)^2 = (2g/(2g-1))(2g/(2g+1)) "
          "is false (so it is not used)", bad)
    # numeric: R_G -> pi/4 (Decimal, 60 digits)
    r = Decimal(1)
    errs = {}
    for G in range(1, 10 ** 6 + 1):
        r = r * Decimal(4 * G * (G + 1)) / Decimal((2 * G + 1) ** 2)
        if G in (10 ** 3, 10 ** 4, 10 ** 5, 10 ** 6):
            errs[G] = r - PI / 4
    ok2 = all(errs[G] > 0 for G in errs) and abs(errs[10 ** 6]) < Decimal("1e-6")
    check("Lemma D: R_G -> pi/4 (numerically, G up to 10^6)", ok2,
          "R_G - pi/4 at G=10^6: %.3e" % errs[10 ** 6])


# ===================================================================
# 5. Theorem: positivity of factors from n0 = mu, partial blocks
# ===================================================================
def check_theorem_parts():
    ok_pos = all(dL(n, mu) >= 2 * (n // mu) and dU(n, mu) >= 2 * (n // mu) >= 2
                 for mu in range(1, MU_MAX + 1)
                 for n in range(mu, mu * (GAMMA_MAX + 1)))
    check("Lemma A: dL(n), dU(n) >= 2*gamma >= 2 for all n >= mu", ok_pos,
          f"mu<={MU_MAX}, n<{GAMMA_MAX + 1}*mu")
    ok_part = True
    for mu in range(2, MU_MAX + 1):
        T = mu // M_of(mu)
        for G in range(1, GAMMA_MAX + 1):
            lo = Fraction(2 * G, 2 * G + 1) ** (2 * T)
            hi = 1 / lo
            Q = Fraction(1)
            nonunit = 0
            for d in range(mu):
                n = mu * G + d
                f = Fraction(dL(n, mu), dU(n, mu))
                if f != 1:
                    nonunit += 1
                    if not (Fraction(2 * G, 2 * G + 1) <= f <= Fraction(2 * G + 1, 2 * G)):
                        ok_part = False
                Q *= f
                if not (lo <= Q <= hi):
                    ok_part = False
            if nonunit != 2 * T:
                ok_part = False
    check("Theorem: block has exactly 2T non-unit factors; partial products "
          "Q satisfy (2G/(2G+1))^(2T) <= Q <= ((2G+1)/(2G))^(2T)", ok_part,
          f"2<=mu<={MU_MAX}, 1<=G<={GAMMA_MAX}")
    # complete blocks: P_{mu G - 1} = R_{G-1} (4 not | mu) and = 1 (4 | mu)
    ok_cb = True
    for mu in range(2, MU_MAX + 1):
        P = Fraction(1)
        R = Fraction(1)
        for G in range(1, GAMMA_MAX + 1):
            P *= block(mu, G)
            R *= wallis_factor(G)
            if P != (Fraction(1) if mu % 4 == 0 else R):
                ok_cb = False
    check("Remark: P_{mu G-1}(mu) = prod_{g<G} 4g(g+1)/(2g+1)^2 if 4 not| mu, "
          "= 1 if 4 | mu", ok_cb, f"2<=mu<={MU_MAX}, G<={GAMMA_MAX}")


# ===================================================================
# 5b. Proposition E (multiset form of the cancellation)
# ===================================================================
def check_prop_E():
    from collections import Counter
    ok = True
    for mu in range(2, MU_MAX + 1):
        cu, cl = Counter(), Counter()
        for G in range(1, GAMMA_MAX + 1):
            for n in range(mu * G, mu * G + mu):
                cu[dU(n, mu)] += 1
                cl[dL(n, mu)] += 1
            Up, Lp = cu - cl, cl - cu      # multiset differences (remove common part)
            if mu % 4 == 0:
                expU, expL = Counter(), Counter()
            else:
                expU = Counter({2 * g + 1: 2 for g in range(1, G + 1)})
                expL = Counter({2 * g: 2 for g in range(2, G + 1)})
                expL[2] += 1
                expL[2 * G + 2] += 1
            if Up != expU or Lp != expL:
                ok = False
    check("Prop E: cleaned multisets over n = mu..mu(G+1)-1 are {3,3,...,2G+1,2G+1} and "
          "{2,4,4,...,2G,2G,2G+2} (4 not| mu), both empty (4 | mu)", ok,
          f"2<=mu<={MU_MAX}, 1<=G<={GAMMA_MAX}")


# ===================================================================
# 6. Start index
# ===================================================================
def first_bad(mu):
    """Largest n < mu with dL(n) * dU(n) == 0, or None."""
    bad = [n for n in range(0, mu) if dL(n, mu) == 0 or dU(n, mu) == 0]
    return max(bad) if bad else None


def check_start_index():
    ok0 = all(dL(0, mu) == 0 for mu in range(2, MU_MAX + 1))
    check("Start index: dL(0) = 0 for every mu >= 2 (factor n=0 vanishes)", ok0)
    ok_n1 = [mu for mu in range(1, MU_MAX + 1)
             if all(dL(n, mu) > 0 and dU(n, mu) > 0 for n in range(1, mu))]
    check("Start index: factors n=1..mu-1 all nonzero and defined only for mu in {1,2,3}",
          ok_n1 == [1, 2, 3], f"found {ok_n1}")
    check("Start index: dU(1) = 0 for all mu >= 4",
          all(dU(1, mu) == 0 for mu in range(4, MU_MAX + 1)))
    # mu >= 5 always has dL(1) = 0
    check("Start index: dL(1) = 0 for all mu >= 5",
          all(dL(1, mu) == 0 for mu in range(5, MU_MAX + 1)))
    # c(mu, n0) = prod_{n=n0}^{mu-1}
    def c(mu, n0):
        r = Fraction(1)
        for n in range(n0, mu):
            r *= Fraction(dL(n, mu), dU(n, mu))
        return r
    check("Start index: n0 = 1 for mu = 2, 3 multiplies the limit by 2 (limit pi/2)",
          c(2, 1) == 2 and c(3, 1) == 2)
    ok_a, ok_b, ok_pos = True, True, True
    for mu in range(4, MU_MAX + 1, 4):
        if not all(dL(n, mu) > 0 and dU(n, mu) > 0 for n in range(mu // 2, mu)):
            ok_pos = False
        if c(mu, (mu + 2) // 2) != 2:
            ok_a = False
        if c(mu, mu // 2) != 1:
            ok_b = False
    check("Start index (4|mu): factors with mu/2 <= n < mu are nonzero", ok_pos)
    check("Start index (4|mu): prod_{n=(mu+2)/2}^{mu-1} = 2, so limit from (mu+2)/2 is 2",
          ok_a, f"mu<={MU_MAX}")
    check("Start index (4|mu): prod_{n=mu/2}^{mu-1} = 1, so limit from mu/2 is 1",
          ok_b, f"mu<={MU_MAX}")


# ===================================================================
# 7. Closed forms for mu = 2, 3 (Remark in Section 2) and OEIS
# ===================================================================
def check_closed_forms():
    ok2 = all(Fraction(dL(n, 2), dU(n, 2)) == Fraction(2 * ((n + 1) // 2), 2 * (n // 2) + 1)
              for n in range(1, 20001))
    check("mu=2: dL(n)/dU(n) = 2 floor((n+1)/2) / (2 floor(n/2)+1), n >= 1", ok2)
    ok2b = all(dL(n, 2) == 2 * ((n + 1) // 2) and dU(n, 2) == 2 * (n // 2) + 1
               for n in range(0, 20001))
    check("mu=2: dL(n) = 2 ceil(n/2), dU(n) = 2 floor(n/2)+1, n >= 0", ok2b)
    ok3 = all(Fraction(dL(n, 3), dU(n, 3)) == Fraction((2 * n + 2) // 3, 2 * (n // 3) + 1)
              for n in range(1, 20001))
    check("mu=3: dL(n)/dU(n) = floor(2(n+1)/3) / (2 floor(n/3)+1), n >= 1", ok3)
    ok3b = all(dL(n, 3) == (2 * n + 2) // 3 and dU(n, 3) == 2 * (n // 3) + 1
               for n in range(0, 20001))
    check("mu=3: dL(n) = floor(2(n+1)/3), dU(n) = 2 floor(n/3)+1, n >= 0", ok3b)
    # Wallis factors for mu = 2 starting at n = 1
    ok_w = True
    for k in range(1, 5001):
        if Fraction(dL(2 * k - 1, 2), dU(2 * k - 1, 2)) != Fraction(2 * k, 2 * k - 1):
            ok_w = False
        if Fraction(dL(2 * k, 2), dU(2 * k, 2)) != Fraction(2 * k, 2 * k + 1):
            ok_w = False
    check("mu=2: factors n=2k-1, 2k are 2k/(2k-1), 2k/(2k+1) (Wallis)", ok_w)
    # OEIS data (first 20 terms as listed on oeis.org)
    A052928 = [0, 0, 2, 2, 4, 4, 6, 6, 8, 8, 10, 10, 12, 12, 14, 14, 16, 16, 18, 18]  # offset 0
    A063196 = [0, 1, 3, 3, 5, 5, 7, 7, 9, 9, 11, 11, 13, 13, 15, 15, 17, 17, 19, 19]  # offset 1
    A007590 = [0, 0, 2, 4, 8, 12, 18, 24, 32, 40, 50, 60, 72, 84, 98, 112, 128, 144, 162, 180]
    A000982 = [0, 1, 2, 5, 8, 13, 18, 25, 32, 41, 50, 61, 72, 85, 98, 113, 128, 145, 162, 181]
    ok_o = (all(dL(n, 2) == A052928[n + 1] for n in range(0, 19))
            and all(dU(n, 2) == A063196[n] for n in range(1, 20))   # A063196(n+1), list index n
            and all(L(n, 2) == A007590[n] for n in range(20))
            and all(U(n, 2) == A000982[n] for n in range(20)))
    check("OEIS (mu=2): dL(n)=A052928(n+1) n>=0; dU(n)=A063196(n+1) n>=1; "
          "L=A007590; U=A000982 (first 20 terms)", ok_o)


# ===================================================================
# 7b. Observation (error constant), checked numerically
# ===================================================================
def check_observation(G=10 ** 4, mus=range(2, 31), tol=Decimal("0.005")):
    ok, worst = True, Decimal(0)
    for mu in mus:
        M = M_of(mu)
        Ns = [mu * G + r for r in range(mu)]
        vals = P_decimal(mu, Ns)
        for N in Ns:
            if mu % 4:
                obs = N * (4 * vals[N] - PI) / mu
                target = PI / 4 if (N + 1) % M == 0 else -PI / 4
            else:
                obs = N * (vals[N] - 1) / mu
                target = Decimal(0) if (N + 1) % M == 0 else Decimal("-0.5")
            worst = max(worst, abs(obs - target))
            if abs(obs - target) > tol:
                ok = False
    check("Observation: N(4P_N - pi)/mu ~ -pi/4 (N != -1 mod M), +pi/4 (N = -1 mod M); "
          "4|mu: N(P_N - 1)/mu ~ -1/2 resp. 0", ok,
          f"2<=mu<=30, N = {G}mu + r for all 0<=r<mu, max deviation {float(worst):.4f}")


# ===================================================================
# 8. Tables
# ===================================================================
SMALL_MU = [2, 3, 5, 6]
SMALL_N = [10 ** 2, 10 ** 3, 10 ** 4, 10 ** 5, 10 ** 6]
LARGE = [(999, 10 ** 7), (1000, 10 ** 7), (1009, 10 ** 7), (1147, 10 ** 7),
         (8888, 10 ** 7), (9999, 10 ** 7), (10000, 10 ** 7), (65537, 10 ** 7)]

# Values as printed in main.tex (4 P_N, and N (4 P_N - pi) to 3 decimals).
EXPECTED_SMALL = {
    (2, 100): ('3.1260789', '-1.551'),
    (2, 1000): ('3.1400238', '-1.569'),
    (2, 10000): ('3.1414356', '-1.571'),
    (2, 100000): ('3.1415769', '-1.571'),
    (2, 1000000): ('3.1415911', '-1.571'),
    (3, 100): ('3.1182361', '-2.336'),
    (3, 1000): ('3.1392385', '-2.354'),
    (3, 10000): ('3.1413571', '-2.356'),
    (3, 100000): ('3.1415691', '-2.356'),
    (3, 1000000): ('3.1415903', '-2.356'),
    (5, 100): ('3.1035170', '-3.808'),
    (5, 1000): ('3.1376779', '-3.915'),
    (5, 10000): ('3.1412001', '-3.926'),
    (5, 100000): ('3.1415534', '-3.927'),
    (5, 1000000): ('3.1415887', '-3.927'),
    (6, 100): ('3.0943587', '-4.723'),
    (6, 1000): ('3.1368791', '-4.714'),
    (6, 10000): ('3.1411214', '-4.713'),
    (6, 100000): ('3.1415455', '-4.712'),
    (6, 1000000): ('3.1415879', '-4.712'),
}
EXPECTED_LARGE = {
    999: (10000000, '0.7853785', '-0.2500'),
    1000: (10000000, '0.9999500', '-0.5000'),
    1009: (10000000, '0.7853784', '-0.2500'),
    1147: (10000000, '0.7853756', '-0.2500'),
    8888: (10000000, '0.9995558', '-0.4998'),
    9999: (10000000, '0.7852019', '-0.2499'),
    10000: (10000000, '0.9995002', '-0.4998'),
    65537: (10000000, '0.7841117', '-0.2499'),
}


def small_table():
    rows = {}
    for mu in SMALL_MU:
        vals = P_decimal(mu, SMALL_N)
        for N in SMALL_N:
            v = 4 * vals[N]
            rows[(mu, N)] = (fmt(v, 7), fmt(N * (v - PI), 3))
    return rows


def large_table():
    rows = {}
    for mu, N in LARGE:
        v = P_decimal(mu, [N])[N]
        lim = PI / 4 if mu % 4 else Decimal(1)
        rows[mu] = (N, fmt(v, 7), fmt(N * (v / lim - 1) / mu, 4))
    return rows


def check_tables(print_rows=False):
    try:
        tex = open("main.tex", encoding="utf-8").read()
    except OSError:
        tex = ""
    t0 = time.time()
    rows = small_table()
    if print_rows:
        for N in SMALL_N:
            print(f"N={N}: " + " | ".join(f"mu={mu}: {rows[(mu, N)]}" for mu in SMALL_MU))
    ok = bool(EXPECTED_SMALL) and all(rows[k] == EXPECTED_SMALL[k] for k in EXPECTED_SMALL)
    ok = ok and set(EXPECTED_SMALL) == set(rows)
    intex = all(s in tex for v in EXPECTED_SMALL.values() for s in v)
    check("Table 1 values (4 P_N(mu), N(4P_N - pi)) recomputed", ok,
          f"{time.time() - t0:.1f}s")
    check("Table 1 values appear verbatim in main.tex", intex)
    # 1/N rate: N(4P_N - pi) stable to within 1% between N=10^5 and 10^6
    stab = all(abs(Decimal(rows[(mu, 10 ** 6)][1]) - Decimal(rows[(mu, 10 ** 5)][1]))
               <= Decimal("0.01") * abs(Decimal(rows[(mu, 10 ** 6)][1])) for mu in SMALL_MU)
    check("Rate: N(4P_N - pi) changes by < 1% from N=10^5 to 10^6 (error ~ c/N)", stab)

    t0 = time.time()
    rows = large_table()
    if print_rows:
        for mu in rows:
            print(f"mu={mu}: {rows[mu]}")
    ok = bool(EXPECTED_LARGE) and rows == EXPECTED_LARGE
    intex = all(s in tex for v in EXPECTED_LARGE.values() for s in v[1:])
    # large-mu rows: sign and size agree with the Observation (-1/4 resp. -1/2)
    agree = all(abs(Decimal(v[2]) - (Decimal("-0.25") if mu % 4 else Decimal("-0.5")))
                < Decimal("0.001") for mu, v in rows.items())
    check("Table 2 last column agrees with the Observation to within 0.001", agree)
    check("Table 2 values (large mu, N = 10^7) recomputed", ok, f"{time.time() - t0:.1f}s")
    check("Table 2 values appear verbatim in main.tex", intex)


# ===================================================================
# 9. Audit of the ORIGINAL manuscript's claims (informational)
# ===================================================================
def audit():
    print("\n===== AUDIT OF ORIGINAL MANUSCRIPT (informational) =====")
    vals = {mu: P_decimal(mu, [10 ** 6])[10 ** 6] for mu in (2, 3, 5, 6, 7)}
    info("P_{10^6}(mu) from n0=mu", ", ".join(f"mu={m}: {fmt(v, 7)}" for m, v in vals.items()))
    info("2*P vs 4*P at 10^6 (mu=2)", f"2P={fmt(2 * vals[2], 6)}, 4P={fmt(4 * vals[2], 6)}")
    v = P_decimal(5, [10 ** 6])[10 ** 6]
    info("Lemma 5.8 number for mu=5, N=10^6", fmt(v, 16) + " (paper: 0.7853971816527053)")
    # residuals
    neg = any(mu * U(n, mu) - n * n < 0 for mu in range(2, 50) for n in range(200))
    info("alpha = mu U(n) - n^2 ever negative?", str(neg))
    for mu in (2, 3, 4, 5, 6):
        al = [mu * U(n, mu) - n * n for n in range(1, mu) if (n * n) % mu]
        be = [n * n - mu * L(n, mu) for n in range(1, mu) if (n * n) % mu]
        info(f"mu={mu} residuals over n=1..mu-1 (mu not| n^2)", f"alpha={al}, beta={be}")
    # original section 4.1 formulas
    import math

    def f5(n):
        c = lambda k: -((-k) // 5)
        return Fraction(c(n - 1) + c(n), c(n) + c(n - 1) - c(n - 2) + 2 * c(n - 3) - c(n - 4))

    mism = [n for n in range(1, 200) if dU(n, 5) == 0 or f5(n) != Fraction(dL(n, 5), dU(n, 5))]
    info("mu=5 formula (eq. pi-mu5): n in 1..199 where factor != dL/dU", str(mism[:15]))
    p = Decimal(1)
    for n in range(1, 10 ** 5 + 1):
        fr = f5(n)
        p = p * Decimal(fr.numerator) / Decimal(fr.denominator)
    info("mu=5 formula: 2*prod_{n=1}^{10^5}", fmt(2 * p, 7))

    def f4(n):
        return Fraction(-(-(n + 1) // 2), 2 * (-(-n // 2)) - n // 2)

    ok4 = all(f4(n) == Fraction(dL(n + 1, 4), dU(n + 1, 4)) for n in range(1, 10000))
    info("mu=4 formula (eq. 10): factor(n) == dL(n+1)/dU(n+1) for mu=4", str(ok4))
    # P_N(4) table entries in original (0.98000 at N=100 etc.)
    for N in (100, 1000):
        info(f"P_N(4), N={N}, from n0=2 / n0=3 / n0=4",
             f"{fmt(P_decimal(4, [N], 2)[N], 5)} / {fmt(P_decimal(4, [N], 3)[N], 5)} / "
             f"{fmt(P_decimal(4, [N], 4)[N], 5)}")
    # gap parameter, minimal-offset definition
    def gap(mu, blocks=12):
        n0 = mu // 2
        kmax = 0
        for n in range(n0, n0 + blocks * mu):
            t = dU(n, mu)
            k = 1
            if n % 2 == 0:
                while dL(n + k, mu) != t:
                    k += 1
                    if k > 10 * mu:
                        return None
            else:
                while n - k >= 0 and dL(n - k, mu) != t:
                    k += 1
                if n - k < 0:
                    return None
            kmax = max(kmax, k)
        return kmax

    claimed = {4: 1, 8: 3, 12: 5, 16: 3, 20: 9, 24: 13, 28: 13, 32: 17, 64: 7}
    for mu in claimed:
        g6, g12 = gap(mu, 6), gap(mu, 12)
        info(f"gap g({mu}) minimal offset, 6 / 12 blocks", f"{g6} / {g12} (paper: {claimed[mu]})")
    rows = [(n, dU(n, 8), dL(n, 8)) for n in range(4, 16)]
    info("mu=8 example table (n, dU, dL)", str(rows))


def main():
    t = time.time()
    print("== Lemmas and proof steps ==")
    check_lemma_A()
    check_lemma_B()
    check_prop_C()
    check_lemma_D()
    check_theorem_parts()
    check_prop_E()
    print("== Start index ==")
    check_start_index()
    print("== Closed forms and OEIS ==")
    check_closed_forms()
    print("== Observation on the rate ==")
    check_observation()
    print("== Tables ==")
    check_tables(print_rows="--tables" in sys.argv)
    if "--audit" in sys.argv:
        audit()
    n_fail = RESULTS.count(False)
    print(f"\n{len(RESULTS) - n_fail}/{len(RESULTS)} checks passed "
          f"in {time.time() - t:.0f}s." + ("" if n_fail else " ALL PASS."))
    sys.exit(1 if n_fail else 0)


if __name__ == "__main__":
    main()
