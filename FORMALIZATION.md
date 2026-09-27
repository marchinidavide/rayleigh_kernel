# Lean formalization overview

This repository formalizes the first-moment-constrained Rayleigh problem on the
half-line in Lean 4 and mathlib. The formal development uses a representative-
free Sobolev model and exposes representative-level bridges where the
manuscript needs pointwise or integral statements.

## Analytic foundations

`HalfLineH1` is the zero-trace half-line Sobolev/Hilbert space, built from the
graph-norm closure of smooth functions supported in the positive half-line.
The foundations provide value and weak-derivative projections, uniqueness and
integration-by-parts interfaces, zero extension and exact norm identities,
completeness, and smooth graph-norm approximation. The public
`HalfLineRepresentativeData` / `HalfLineH1.ofRepresentative` API gives the
converse construction from value and weak-derivative data, with exact
compatibility and almost-everywhere extensionality results.

Canonical representatives are continuous and locally absolutely continuous,
have zero trace and vanish on the nonpositive half-line, satisfy the
fundamental-theorem identity and the half-line Hölder bound, and decay at
infinity. The development includes the supremum estimate, the
one-dimensional Gagliardo--Nirenberg inequality, representative/intrinsic
energy bridges, compactness, local uniform convergence, strong `L²`
convergence, tail estimates, and weak lower semicontinuity needed below.

## Variational theorem and optimizer

The intrinsic mass, first moment, square energy, Dirichlet energy, Rayleigh
quotient, admissibility, and minimizer APIs support a direct-method existence
proof for every `L > 0`. The proof includes scaling, nondegeneracy and moment
passage, the obstacle/KKT first-variation and reaction-measure interfaces,
regularity of the reduced profile, and the homogeneous centered-cone frontend.
It establishes contact and positivity geometry, compression of positivity
components, support structure, and the affine-forcing regularity needed for the
free-boundary analysis.

The explicit profile and scalar root theory identify the optimizer, its compact
support, boundary identities, and exact energies. The main theorem packages
existence, almost-everywhere uniqueness, the explicit representative, the
minimum, the sharp inequality, equality cases, and scale-free rescaling. The
symbolic EMA2 comparison and certified numerical enclosures are included as
separate results.

## Discrete, probability, and covariance extensions

The discrete development defines piecewise-linear interpolation and exact cell
identities, constructs recovery families, and proves convergence of scaled
discrete minima and admissible near-minimizer quotients and interpolants to the
continuum optimizer in the stated weak, strong-`L²`, and compact-local senses.

The probability layer provides finite-cutoff and finite-row projection,
turnover, power-cost, Gaussian, mixture, Rademacher, kurtosis, and CLT
results. The covariance layer includes finite covariance-form and spectral
interfaces, short-memory Toeplitz/Riemann-sum limits, and profilewise
fixed-profile convergence. These statements retain their hypotheses: they do
not silently assert an infinite random series, a general stationary process,
or an unqualified covariance-operator theorem. The manuscript's
tilted-Gaussian example remains outside the formalized surface.

## Public surface and release audit

Paper-facing declarations are indexed by
[`RayleighKernel/Claims.lean`](RayleighKernel/Claims.lean); the aggregate import
is [`RayleighKernel.lean`](RayleighKernel.lean). Focused module imports are
preferred when using a particular result. Certified numerical declarations
are under `RayleighKernel/Numerics` and are separate from the aggregate
optimizer certificate.

The canonical offline release gate is
[`scripts/release-check.sh`](scripts/release-check.sh). It checks compilation,
forbidden production tokens and settings, whitespace, and the compiled public
axiom audit. The expected audited axioms are exactly
`propext`, `Classical.choice`, and `Quot.sound` (definitions may report no
axioms). The source of the mathematical statement is
[`manuscript/main.tex`](manuscript/main.tex).

## Statement on the use of generative AI

The Lean 4 formalization described here, and the proofs in the accompanying
paper, were produced with help from `gpt-5.6-sol` on high reasoning effort. The
author verified all the results reported here and takes full responsibility for
the content.

## Scope

Full Γ-convergence is not included in this release. Discrete results cover the
explicitly stated interpolation, recovery, minimum, and near-minimizer
convergence theorems, without adding a stronger Γ-convergence package.
Finite-cutoff and profilewise qualifications in the probability and covariance
extensions remain part of the claims, and the tilted-Gaussian example is not
formalized.
