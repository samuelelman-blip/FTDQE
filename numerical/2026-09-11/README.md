# FTDQE numerical release — 2026-09-11

The [versioned numerical release](https://github.com/samuelelman-blip/FTDQE/releases/tag/numerical-2026-09-11) contains the corrected manuscript, its LaTeX source and the numerical archive for every table and figure.

Download **FTDQE_numerical_2026-09-11.zip** from that release and extract it. The archive contains 868 manifest-listed files plus the manifest, including canonical coefficients, Hamiltonians, codeword maps, radii, solver settings, stochastic sequences and outputs. Paths in EXHIBIT_INDEX.md refer to the extracted archive root. The SHA256SUMS.txt file here identifies the three release downloads.

The manuscript changes address only three requests:

1. Record and replay the actual stochastic sequence. A PCG64 stream initialized by default_rng(3) consumes the 60 independent-site choices before generating the permutations. Ten recorded sweeps reproduce 1−F = 0.016791641292898, retaining 0.016792. NumPy 2.3.5 is the replay environment; the historical scalar file did not record its version.
2. Publish and cite this numerical release. Feasibility, optimality/support-minimality, declared-score evaluation and dynamical validation have distinct entries. Hashes identify files, while the associated numerical residuals and comparisons assess their content.
3. Record the fourteen literal-cutoff grids and realised times. Four-site K values are (8,12,16,21,25,33,42); six-site values are (16,24,32,40,49,65,81). The six-site longest contrast uses 163 nodes; the full nearest-integer reference used in the scan uses 165.

The outer-loop table is numbered V in this PDF; the review referred to its scan panel as VI(b). Stable TeX labels identify exhibits. See the archive README and exhibit index for the preserved historical figure inputs and family-count record limitations.

The original formal-verification development elsewhere in this repository is unchanged by this numerical release.
