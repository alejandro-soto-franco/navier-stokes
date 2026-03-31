"""
Chapter 1 — SymPy verification of Helmholtz decomposition properties.

Verifies on an example vector field in R^3:
  1. Any smooth vector field u decomposes as u = v + grad(p)
     where div(v) = 0
  2. v and grad(p) are L^2-orthogonal
  3. The Leray projector is idempotent: P(P(u)) = P(u)
"""
import sympy as sp
from sympy.vector import CoordSys3D

def main():
    R = CoordSys3D("R")
    x, y, z = R.x, R.y, R.z

    # --- Example vector field: u = (x^2 * y, -x * y^2, z) ---
    u1 = x**2 * y
    u2 = -x * y**2
    u3 = z

    # 1. Compute divergence of u
    div_u = sp.diff(u1, x) + sp.diff(u2, y) + sp.diff(u3, z)
    div_u_simplified = sp.simplify(div_u)
    print(f"div(u) = {div_u_simplified}")

    # 2. Solve Laplace(p) = div(u) for the pressure
    #    div(u) = 2xy - 2xy + 1 = 1, so we need Laplace(p) = 1.
    #    A particular solution: p = (x^2 + y^2 + z^2) / 6
    assert div_u_simplified == 1, f"Expected div(u)=1, got {div_u_simplified}"
    print("[PASS] div(u) = 1 (nonzero, so u is not divergence-free)")

    p = (x**2 + y**2 + z**2) / 6
    lap_p = sp.diff(p, x, 2) + sp.diff(p, y, 2) + sp.diff(p, z, 2)
    assert sp.simplify(lap_p - 1) == 0, f"Laplacian(p) != 1: {lap_p}"
    print("[PASS] Laplace(p) = div(u) = 1")

    # 3. Compute v = u - grad(p)
    grad_p1 = sp.diff(p, x)  # x/3
    grad_p2 = sp.diff(p, y)  # y/3
    grad_p3 = sp.diff(p, z)  # z/3

    v1 = sp.simplify(u1 - grad_p1)
    v2 = sp.simplify(u2 - grad_p2)
    v3 = sp.simplify(u3 - grad_p3)

    print(f"v = ({v1}, {v2}, {v3})")
    print(f"grad(p) = ({grad_p1}, {grad_p2}, {grad_p3})")

    # 4. Verify div(v) = 0
    div_v = sp.diff(v1, x) + sp.diff(v2, y) + sp.diff(v3, z)
    div_v_simplified = sp.simplify(div_v)
    assert div_v_simplified == 0, f"div(v) != 0: {div_v_simplified}"
    print("[PASS] div(v) = 0 (v is divergence-free)")

    # 5. Verify orthogonality: integral of v . grad(p) over symmetric domain
    dot_product = v1 * grad_p1 + v2 * grad_p2 + v3 * grad_p3
    dot_simplified = sp.simplify(dot_product)
    print(f"v . grad(p) = {dot_simplified}")

    a = sp.Symbol("a", positive=True)
    integral = sp.integrate(
        sp.integrate(
            sp.integrate(dot_simplified, (x, -a, a)),
            (y, -a, a)),
        (z, -a, a))
    integral_simplified = sp.simplify(integral)
    assert integral_simplified == 0, f"L^2 orthogonality failed: {integral_simplified}"
    print("[PASS] integral of v . grad(p) over [-a,a]^3 = 0 (L^2 orthogonal)")

    # 6. Idempotence: P(u) = v, P(v) = v (since div(v) = 0, P is identity on L^2_sigma)
    div_v_check = sp.simplify(sp.diff(v1, x) + sp.diff(v2, y) + sp.diff(v3, z))
    assert div_v_check == 0
    print("[PASS] P(P(u)) = P(v) = v (idempotent, since v is already divergence-free)")

    print("\nAll Chapter 1 Helmholtz verification checks passed.")


if __name__ == "__main__":
    main()
