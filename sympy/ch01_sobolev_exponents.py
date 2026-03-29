"""
Chapter 1 — SymPy verification of Sobolev exponent identities.

Verifies:
  1. Sobolev conjugate p* = np/(n-p) satisfies 1/p* = 1/p - 1/n
  2. For n=3, p=2: p* = 6
  3. Morrey exponent alpha = 1 - n/p is in (0,1) for p > n
  4. Scaling consistency of the Poincare inequality
"""
import sympy as sp

def main():
    n, p = sp.symbols("n p", positive=True)

    # 1. Sobolev conjugate
    p_star = n * p / (n - p)
    lhs = sp.Rational(1, 1) / p_star
    rhs = 1 / p - 1 / n
    diff = sp.simplify(lhs - rhs)
    assert diff == 0, f"Sobolev conjugate identity failed: {diff}"
    print("[PASS] 1/p* = 1/p - 1/n")

    # 2. n=3, p=2 gives p*=6
    p_star_32 = p_star.subs([(n, 3), (p, 2)])
    assert p_star_32 == 6, f"Expected p*=6, got {p_star_32}"
    print("[PASS] p*(n=3, p=2) = 6")

    # 3. n=3, p=1 gives p*=3/2
    p_star_31 = p_star.subs([(n, 3), (p, 1)])
    assert p_star_31 == sp.Rational(3, 2), f"Expected p*=3/2, got {p_star_31}"
    print("[PASS] p*(n=3, p=1) = 3/2")

    # 4. Morrey exponent alpha = 1 - n/p
    alpha = 1 - n / p
    # For n=3, p=4: alpha = 1/4
    alpha_34 = alpha.subs([(n, 3), (p, 4)])
    assert alpha_34 == sp.Rational(1, 4), f"Expected alpha=1/4, got {alpha_34}"
    print("[PASS] alpha(n=3, p=4) = 1/4")

    # 5. For n=3, p=6: alpha = 1/2
    alpha_36 = alpha.subs([(n, 3), (p, 6)])
    assert alpha_36 == sp.Rational(1, 2), f"Expected alpha=1/2, got {alpha_36}"
    print("[PASS] alpha(n=3, p=6) = 1/2")

    # 6. Scaling check: if u_lambda(x) = u(lambda*x) on Omega_lambda = Omega/lambda,
    #    then ||u_lambda||_Lp(Omega_lambda) = lambda^{-n/p} ||u||_Lp(Omega)
    #    and ||nabla u_lambda||_Lp = lambda^{1-n/p} ||nabla u||_Lp.
    #    Poincare: ||u||_L2 <= C_P ||nabla u||_L2, so C_P scales as lambda^{-1}
    #    (i.e., proportional to diameter).
    lam = sp.Symbol("lambda", positive=True)
    scaling_u = lam ** (-n / p)
    scaling_grad = lam ** (1 - n / p)
    # C_P ratio: ||u_lam||/||grad u_lam|| = (lam^{-n/p} / lam^{1-n/p}) = lam^{-1}
    ratio = sp.simplify(scaling_u / scaling_grad)
    assert ratio == 1 / lam, f"Poincare scaling failed: {ratio}"
    print("[PASS] Poincare constant scales as 1/lambda (proportional to diameter)")

    print("\nAll Chapter 1 SymPy verifications passed.")


if __name__ == "__main__":
    main()
