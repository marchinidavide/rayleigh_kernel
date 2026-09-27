# A First-Moment-Constrained Rayleigh Problem on the Half-Line

This repository contains a Lean 4 formalization of the variational problem in
[`manuscript/main.tex`](manuscript/main.tex).  For a prescribed mean lookback
`L > 0`, it studies nonnegative probability densities on the half-line with
zero trace at the origin and minimizes

```text
        ∫₀∞ |f'(x)|² dx
R(f) =  ------------------ .
        ∫₀∞ f(x)² dx
```

The main result is that the minimum is attained by a unique admissible
profile (up to almost-everywhere equality), compactly supported on `[0,K]`,
and linear plus trigonometric on its support.  Its scale-free parameter is the
unique scalar root `tStar`; the formalization also proves the sharp inequality,
the equality case, and the scaling laws.  Certified Lean bounds record the
printed constants and the exact EMA2 comparisons.

## What is formalized

The paper-facing index is [`RayleighKernel/Claims.lean`](RayleighKernel/Claims.lean).
The aggregate certificate for the main theorem is
`RayleighKernel.Claims.MainOptimizerData` (an abbreviation of
`RayleighKernel.Analysis.HalfLineH1.MainOptimizerData`), provided by
`RayleighKernel.Claims.mainOptimizer`.  This is the aggregate main-theorem
certificate; the numerical bounds are separate certified corollaries in
[`RayleighKernel/Numerics`](RayleighKernel/Numerics) and are not fields of that
certificate.

The principal modules are:

* [`RayleighKernel/MainTheorem.lean`](RayleighKernel/MainTheorem.lean) and
  [`RayleighKernel/Claims.lean`](RayleighKernel/Claims.lean) for the optimizer
  and manuscript-facing surface;
* [`RayleighKernel/Optimizer`](RayleighKernel/Optimizer) and
  [`RayleighKernel/Profile`](RayleighKernel/Profile) for support geometry,
  the explicit profile, and the unique scalar root;
* [`RayleighKernel/Discrete`](RayleighKernel/Discrete) for piecewise-linear
  interpolation, recovery, and discrete-to-continuum convergence;
* [`RayleighKernel/Probability`](RayleighKernel/Probability) for finite-cutoff
  projection, covariance, cost, short-memory, kurtosis, and finite-row CLT
  results; and
* [`RayleighKernel/Numerics`](RayleighKernel/Numerics) for Lean-certified
  rational enclosures; and
* [`RayleighKernel/Obstacle/HomogeneousKKT.lean`](RayleighKernel/Obstacle/HomogeneousKKT.lean)
  for the additive homogeneous centered-cone and one-bump first-variation/KKT
  frontend, including two-sided interior stationarity, centered witness independence,
  coefficient and functional bridges to the existing two-bump KKT frontend, and a smooth
  reaction-measure forcing bridge. This module is quotient-equivalent to normalized
  admissibility, but does not replace the existing two-bump Riesz/reaction-measure/regularity
  chain, which remains authoritative downstream.

The probability and covariance statements are deliberately qualified: several
are finite-cutoff or finite-support results, rather than claims about an
infinite random series or process.  The short-memory theorem is profilewise
for each fixed smooth compactly supported profile.  Discrete CLT statements
use finite triangular rows.  Difference-projection density/continuity characterization is formalized in
`RayleighKernel.Probability.DifferenceProjectionIsotropicWhite` and its
associated density and transfer declarations. Full Γ-convergence is outside
this release's scope. The manuscript's tilted-Gaussian example is not claimed
formalized.

## Public API quick start

Focused imports are preferred for downstream code; the aggregate import is convenient for exploration:

```lean
import RayleighKernel
```

For the optimizer and paper-facing claims, use the narrower index module:

```lean
import RayleighKernel.Claims

RayleighKernel.Claims.mainOptimizer
RayleighKernel.Analysis.HalfLineH1.mainOptimizerTheorem
```

For discrete convergence, import only:

```lean
import RayleighKernel.Discrete.Convergence

RayleighKernel.Discrete.tendsto_scaledDiscreteMinimum
RayleighKernel.Discrete.tendsto_scaled_rayleighQuotient_of_nearMinimizer
```

For the P1.9 difference-projection results, use:

```lean
import RayleighKernel.Probability.DifferenceProjection

RayleighKernel.Probability.IsFiniteZeroSum
RayleighKernel.Probability.dense_finiteZeroSum
RayleighKernel.Probability.DifferenceProjectionIsotropicWhite
RayleighKernel.Probability.DifferenceProjectionIsotropicWhite.projection_integral_abs_of_difference
RayleighKernel.Probability.turnoverIsotropicWhite_of_difference_projection
```

Certified numerical results are likewise available through focused imports:
`RayleighKernel.Numerics.RootBracket` for `tStar_mem_rootBracket`,
`RayleighKernel.Numerics.Constants` for the certified `AStar`, `CStar`,
`kappaStar`, and `lambdaStar` rounding-bin declarations, and
`RayleighKernel.Numerics.EMA2` for the certified EMA2 objective and turnover
comparisons. These numerical certificates are separate from
`RayleighKernel.Claims.MainOptimizerData`.

## Prerequisites and local build

Use the pinned Lean toolchain and mathlib revision recorded in
[`lakefile.toml`](lakefile.toml).  The release check additionally requires
[`ripgrep`](https://github.com/BurntSushi/ripgrep) (`rg`) on `PATH`; install it
with your package manager, for example `brew install ripgrep`.  From the project
root, fetch the cached dependencies and build the library:

```bash
lake exe cache get
lake build
```

## Local verification and reproducibility

After the pinned dependencies are already available locally, the portable,
offline release check is:

```bash
scripts/release-check.sh
```

It runs the aggregate root compile, `lake build`, the production forbidden-token
and settings scan, both Git whitespace checks, a version-consistency check
across the release metadata, and a compiled public declaration axiom audit.  The
audit checks the actual names and signatures of the release
surface and prints their axioms; the expected output contains only
`propext`, `Classical.choice`, and `Quot.sound` (definitions may report no
axioms).  The script performs no network operation; dependency acquisition is a
separate prerequisite (`lake exe cache get` when needed).

Two limits are worth knowing.  The whitespace checks use `git diff --check`, so
they only inspect changes against `HEAD`; on the very first commit of a fresh
repository there is no `HEAD` yet and both checks pass vacuously.  The gate
also covers only the Lean development: the Python numerical certificate under
[`manuscript/`](manuscript) is verified separately by the command below.

For a focused module, use `lake env lean path/to/ChangedModule.lean` before the
aggregate check.  The manuscript sources are
[`manuscript/main.tex`](manuscript/main.tex) and its AMS-style variant
[`manuscript/main_ams.tex`](manuscript/main_ams.tex); both include the shared
profile figure, and they are the local reference for the mathematical
statement.

### Manuscript artifacts

Install or use [`uv`](https://docs.astral.sh/uv/) for the isolated numerical
certificate environment. The certificate command is:

```bash
uv run --script manuscript/certify_rayleigh_constants.py
```

Its PEP 723 metadata embeds `python-flint==0.9.0`. Generate the vector figure
with:

```bash
uv run --script manuscript/generate_profile_figure.py
```

The figure script has no Python package dependencies, but requires `tectonic`
on `PATH` and uses PGFPlots 1.18 from the TeX bundle; `uv` manages only the
Python environment, while Tectonic is the required external TeX executable. It rewrites
`manuscript/rayleigh_kernel_profile.pdf`, which both manuscripts include. Lean
`v4.34.0` is pinned by `lean-toolchain`, direct mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435` is pinned in `lakefile.toml`, and
transitive revisions are pinned in `lake-manifest.json`.

Detailed formalization information is in
[`FORMALIZATION.md`](FORMALIZATION.md), and paper-facing declarations are
indexed by [`RayleighKernel/Claims.lean`](RayleighKernel/Claims.lean).

## Citation

If you use this formalization or its accompanying manuscript, please cite it.
Machine-readable metadata is in [`CITATION.cff`](CITATION.cff).

## Statement on the use of generative AI

The Lean 4 formalization in this repository, and the proofs in the accompanying
paper, were produced with help from `gpt-5.6-sol` on high reasoning effort. The
author verified all the results reported here and takes full responsibility for
the content.

## License

Released under the MIT License; see [`LICENSE`](LICENSE).  Proof developments
that import this library should also record the pinned mathlib revision, since
the results are only guaranteed against the toolchain and dependencies
recorded in [`lakefile.toml`](lakefile.toml), [`lean-toolchain`](lean-toolchain),
and [`lake-manifest.json`](lake-manifest.json).
