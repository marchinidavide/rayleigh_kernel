# /// script
# requires-python = ">=3.10,<3.15"
# dependencies = [
#   "python-flint==0.9.0",
# ]
# ///

r"""Rigorous interval certificate for the constants printed in main.tex.

Every decimal printed in the manuscript is re-derived here in 100-digit
interval arithmetic (``python-flint``) and is required to lie strictly
inside the rounding bin of its printed value. The same enclosures certify
the sign claims that the paper's uniqueness argument rests on.

The auxiliary function ``p``, the polynomial ``Q``, the coefficients
``A_*`` and ``C_*``, the integrals ``I_0`` and ``I_1``, and the reported
values of ``F_*'(0)`` and ``F_*''(1)`` follow the definitions in
``manuscript/main.tex``.

Run from the repository root with::

    uv run --script manuscript/certify_rayleigh_constants.py

Failures raise :class:`CertificateError`. The checks are deliberately not
written with ``assert``: assertions are removed by ``python -O``, which
would let the certificate report success without having checked anything.
"""

from flint import arb, ctx

# Bracketing interval for the unique root t_* of Q, as printed in main.tex.
# These are kept as decimal strings so that importing this module has no
# arithmetic side effects: the working precision is configured by main().
T_MINUS = "3.5701290278126360584735350083717233860170522483300"
T_PLUS = "3.5701290278126360584735350083717233860170522483302"

# Working precision for the ball context, in decimal digits.
WORKING_PRECISION = 100


class CertificateError(RuntimeError):
    """Raised when an enclosure fails to certify a printed constant."""


def require(*, condition: bool, detail: str) -> None:
    """Raise :class:`CertificateError` with ``detail`` unless ``condition`` holds."""
    if not condition:
        message = f"certificate failed: {detail}"
        raise CertificateError(message)


def p(t: arb) -> arb:
    r"""Return the auxiliary function :math:`p(t) = 2 - t\cot(t/2)`.

    This is the ``p`` of ``main.tex``, which also identifies it with the
    derivative :math:`F_t'(0)` of the scaled profile. The cotangent is
    evaluated over the whole ball ``t``, so the result encloses ``p``
    everywhere on the bracketing interval of :math:`t_*`.
    """
    return 2 - t * (t / 2).cot()


def q_polynomial(t: arb) -> arb:
    r"""Return the consistency polynomial :math:`Q(t)`.

    That is :math:`t^4 - 6t^2p(t) + 3p(t)^3\bigl(p(t) - 2\bigr)`, whose unique
    root in :math:`(0, 2\pi)` is :math:`t_*`. The paper proves that this
    ``Q`` is strictly increasing, so ``Q(t_-) < 0 < Q(t_+)`` is a genuine
    sign change and not an artefact of the enclosures.
    """
    pt = p(t)
    return t**4 - 6 * t**2 * pt + 3 * pt**3 * (pt - 2)


def coefficient_a(t: arb) -> arb:
    r"""Return :math:`A_*`, the trigonometric coefficient of the profile.

    That is :math:`(t\sin t + \cos t - 1) / (t(\cos t - 1))`.
    """
    return (t * t.sin() + t.cos() - 1) / (t * (t.cos() - 1))


def coefficient_c(t: arb) -> arb:
    r"""Return :math:`C_* = \bigl(t\cos t - \sin t\bigr) / \bigl(t(\cos t - 1)\bigr)`.

    The support ratio follows as :math:`\kappa_* = K_L/L = 1/C_*`.
    """
    return (t * t.cos() - t.sin()) / (t * (t.cos() - 1))


def integral_i0(t: arb) -> arb:
    r"""Return :math:`I_0(t) = \int_0^1 F_t(y)\,dy` in closed form."""
    return (t**2 * (1 + t.cos()) - 4 * t * t.sin() + 4 * (1 - t.cos())) / (
        2 * t**2 * (1 - t.cos())
    )


def integral_i1(t: arb) -> arb:
    r"""Return :math:`I_1(t) = \int_0^1 y F_t(y)\,dy` in closed form."""
    return (t * (t.cos() + 2) - 3 * t.sin()) / (6 * t * (1 - t.cos()))


def rounding_bin(decimal: str) -> tuple[arb, arb]:
    """Return the open rounding bin of a printed ``decimal``.

    The bin is the set of values that round to ``decimal`` at its own number
    of fractional digits, that is the printed value plus or minus half a unit
    in the last place.
    """
    digits = len(decimal.partition(".")[2])
    center = arb(decimal)
    half_unit = arb(1) / (2 * arb(10) ** digits)
    return center - half_unit, center + half_unit


def require_rounds_to(value: arb, decimal: str) -> None:
    """Require that the enclosure ``value`` lies strictly inside the bin of ``decimal``.

    The comparison is between balls, so containment means the whole
    enclosure is above the lower and below the upper endpoint. Touching an
    endpoint counts as a failure: the printed decimal would then not be
    justified to the stated number of digits.
    """
    lower, upper = rounding_bin(decimal)
    if not (value > lower and value < upper):
        message = f"{value} is not contained in the rounding bin for {decimal}"
        raise CertificateError(message)


def main() -> None:
    """Certify every constant printed in ``main.tex`` and report the enclosures."""
    ctx.dps = WORKING_PRECISION

    t_minus = arb(T_MINUS)
    t_plus = arb(T_PLUS)
    q_minus = q_polynomial(t_minus)
    q_plus = q_polynomial(t_plus)
    require(condition=q_minus < 0, detail=f"expected Q(t_-) < 0, got {q_minus}")
    require(condition=q_plus > 0, detail=f"expected Q(t_+) > 0, got {q_plus}")

    # Interval hull of the root, used for every downstream evaluation.
    t = t_minus.union(t_plus)
    a = coefficient_a(t)
    c = coefficient_c(t)
    i0 = integral_i0(t)
    i1 = integral_i1(t)
    kappa = 1 / c
    rayleigh = t**2 * c**2
    f_prime_zero = 1 + t * a
    f_second_one = -(t**2) * (a * t.sin() + c * t.cos())

    require_rounds_to(t, "3.570129027812636")
    require_rounds_to(a, "0.497710545413385")
    require_rounds_to(c, "0.415370649651761")
    require_rounds_to(i0, "0.302496116691908")
    require_rounds_to(i1, "0.125648008507453")
    require_rounds_to(kappa, "2.407488350075723")
    require_rounds_to(rayleigh, "2.199071934562496")
    require_rounds_to(f_prime_zero, "2.7768908656")
    require_rounds_to(f_second_one, "7.4515812118")

    # Endpoint derivative signs at the free boundary (main.tex, Section 4):
    # F_*'(0) > 0 and F_*''(1) > 0. The second one is what makes the profile
    # turn back to zero at x = 1, since F_*(1) = F_*'(1) = 0 there.
    require(
        condition=f_prime_zero > 0,
        detail=f"expected F_*'(0) > 0, got {f_prime_zero}",
    )
    require(
        condition=f_second_one > 0,
        detail=f"expected F_*''(1) > 0, got {f_second_one}",
    )

    print(f"Q(t_-) = {q_minus.str(20)}")
    print(f"Q(t_+) = {q_plus.str(20)}")
    print(f"t_*      in {t.str(25)}")
    print(f"A_*      in {a.str(25)}")
    print(f"C_*      in {c.str(25)}")
    print(f"I_0      in {i0.str(25)}")
    print(f"I_1      in {i1.str(25)}")
    print(f"kappa_*  in {kappa.str(25)}")
    print(f"lambda_* in {rayleigh.str(25)}")
    print(f"F_*'(0)  in {f_prime_zero.str(25)}")
    print(f"F_*''(1) in {f_second_one.str(25)}")
    print("All sign and decimal-rounding assertions passed.")


if __name__ == "__main__":
    main()
