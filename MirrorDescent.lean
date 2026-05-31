/-
Copyright (c) 2025 Mirror Descent Library. All rights reserved.
Released under the MIT license.

# Mirror Descent Lean Library

Root module. Imports the full library:
- `MirrorDescent.Defs`              — Bregman divergence, subgradients, mirror maps
- `MirrorDescent.BregmanDivergence` — non-negativity and the three-point identity
- `MirrorDescent.MirrorStep`        — the per-step descent bound
- `MirrorDescent.Convergence`       — O(1/√K) averaged convergence
-/
import MirrorDescent.Defs
import MirrorDescent.BregmanDivergence
import MirrorDescent.MirrorStep
import MirrorDescent.Convergence
