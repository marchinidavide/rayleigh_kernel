#!/usr/bin/env python3
# /// script
# requires-python = ">=3.10,<3.15"
# dependencies = []
# ///

r"""Generate the scale-free optimizer figure included by main.tex.

The figure plots the normalized optimizer profile
:math:`\\Phi(z) = L f_L(Lz)` on its support, marks the free boundary
:math:`\\kappa_* = K_L/L`, and is written to
``manuscript/rayleigh_kernel_profile.pdf``, which both manuscript variants
include.

The plot is emitted by a self-contained PGFPlots document that is compiled
with ``tectonic`` inside a temporary directory, so no LaTeX intermediates
are left behind. ``SOURCE_DATE_EPOCH`` is pinned to make the output
reproducible.

Run from the repository root with::

    uv run --script manuscript/generate_profile_figure.py
"""

import math
import os
import shutil
import subprocess
import tempfile
from dataclasses import dataclass
from pathlib import Path

# Root of the unique scalar tStar, as certified in
# manuscript/certify_rayleigh_constants.py.
T_STAR = 3.57012902781263605847


@dataclass(frozen=True)
class Profile:
    """Closed-form profile constants at ``tStar``, as printed in ``main.tex``.

    The fields are the trigonometric coefficient ``a``, the decaying
    coefficient ``c``, the normalization ``i0``, and the root ``tStar``
    itself. The support ratio is derived rather than stored, because
    ``main.tex`` gives ``kappa_* = K_L/L = 1/c_*``.
    """

    t: float
    a: float
    c: float
    i0: float

    @property
    def kappa(self) -> float:
        """Return the support ratio ``kappa_* = 1/c_*``."""
        return 1 / self.c


def certified_profile() -> Profile:
    """Return the profile constants evaluated at the certified root."""
    t = T_STAR
    a = (t * math.sin(t) + math.cos(t) - 1) / (t * (math.cos(t) - 1))
    c = (t * math.cos(t) - math.sin(t)) / (t * (math.cos(t) - 1))
    i0 = (t**2 * (1 + math.cos(t)) - 4 * t * math.sin(t) + 4 * (1 - math.cos(t))) / (
        2 * t**2 * (1 - math.cos(t))
    )
    return Profile(t=t, a=a, c=c, i0=i0)


def profile_value(profile: Profile, z: float) -> float:
    """Return ``Phi(z) = L f_L(L z)``, which vanishes beyond ``kappa_*``."""
    y = z / profile.kappa
    if z > profile.kappa:
        return 0.0
    return (
        profile.a * math.sin(profile.t * y)
        + profile.c * (math.cos(profile.t * y) - 1)
        + y
    ) / (profile.kappa * profile.i0)


def main() -> None:
    """Render the figure and install it as ``rayleigh_kernel_profile.pdf``."""
    tectonic = shutil.which("tectonic")
    if tectonic is None:
        message = (
            "tectonic is required on PATH; install it and rerun the documented command"
        )
        raise SystemExit(message)

    profile = certified_profile()
    kappa = profile.kappa
    xmax = 1.08 * kappa
    ymax = 0.8
    points = [
        f"({xmax * index / 999:.12f},{profile_value(profile, xmax * index / 999):.12f})"
        for index in range(1000)
    ]
    source = r"""\documentclass{article}
\usepackage[paperwidth=7.2in,paperheight=4.2in,margin=0pt]{geometry}
\usepackage{pgfplots}
\pgfplotsset{compat=1.18}
\pagestyle{empty}
\begin{document}
\noindent\begin{tikzpicture}
\begin{axis}[
  width=7.2in, height=4.2in, xmin=0, xmax=@@XMAX@@, ymin=0, ymax=@@YMAX@@,
  xlabel={scaled lag $z=x/L$}, ylabel={$\Phi(z)=L f_L(Lz)$},
  grid=major, grid style={draw=black!20}, axis line style={black!70},
  tick style={black!70}, label style={font=\small}, tick label style={font=\small},
  clip=false,
]
\addplot[very thick, color={rgb,255:red,31;green,90;blue,153}, mark=none] coordinates {
@@POINTS@@
};
\addplot[dashed, color=black!65, thin] coordinates {(@@KAPPA@@,0) (@@KAPPA@@,@@YMAX@@)};
\node[anchor=south east, font=\small] at (axis description cs:0.755,0.16)
  {$\kappa_* = @@KAPPA_LABEL@@$};
\end{axis}\end{tikzpicture}
\end{document}
"""
    destination = Path(__file__).with_name("rayleigh_kernel_profile.pdf")
    source = (
        source.replace("@@XMAX@@", f"{xmax:.12f}")
        .replace("@@KAPPA@@", f"{kappa:.12f}")
        .replace("@@KAPPA_LABEL@@", f"{kappa:.6f}")
        .replace("@@YMAX@@", f"{ymax:.12f}")
        .replace("@@POINTS@@", "\n".join(points))
    )
    with tempfile.TemporaryDirectory(
        dir=destination.parent, prefix=".rayleigh-profile-"
    ) as directory:
        work = Path(directory)
        (work / "profile.tex").write_text(source, encoding="utf-8")
        environment = os.environ.copy()
        environment["SOURCE_DATE_EPOCH"] = "0"
        subprocess.run(  # noqa: S603 - fixed argv, no shell, no untrusted input
            [tectonic, "--keep-logs", "--outdir", str(work), "profile.tex"],
            cwd=work,
            env=environment,
            check=True,
        )
        os.replace(work / "profile.pdf", destination)


if __name__ == "__main__":
    main()
