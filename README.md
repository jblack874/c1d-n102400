# C_1d upper bound: 1.4513063746953752 (102,400-cell step function) — ARCHIVE, superseded by PR #345

> **Superseded by [teorth/optimizationproblems PR #345](https://github.com/teorth/optimizationproblems/pull/345)**
> (A. Canli, updated 21 Nov 2026): C_1d <= 5136552493465657446805004533831259136/3539261750767002528079406787843004249
> = 1.4513061918498968, which is 1.828e-7 below this certificate. Both checkers in this repo accept that certificate
> (`archive_check/`). This repository is kept as a valid, exactly certified bound and as the search log of the NP-β
> method; it is not a record and is not being submitted.

An exact certificate that the signed autocorrelation constant C_1d (constant 1d in
[teorth/optimizationproblems](https://github.com/teorth/optimizationproblems)) satisfies

    C_1d <= 2054622084077908729297673521179121664000/1415705270714577825348504941537856324889 = 1.4513063746953752...

which is **2.599e-8 below the registry's PR #374 (1.4513064006879361)**. The certificate is a local polish of
PR #374's construction, so this is an improved construction, not a new one.

| Field | Result |
|---|---|
| Mathematical objective | Minimize max_t \|(f*f)(t)\| / (∫f)^2 over real step functions f on [-1/4, 1/4] with 102,400 equal cells; any f certifies an upper bound on C_1d. |
| Baseline | Registry PR #374 ([cweill/c1d-upper-bound](https://github.com/cweill/c1d-upper-bound), 2026-11-17): 1.4513064006879361. |
| Candidate result | Exact 2054622084077908729297673521179121664000/1415705270714577825348504941537856324889 = 1.4513063746953752, 2.599e-8 below #374. This is an improvement in the upper bound, not in how precisely the constant is known. |
| Verification | Exact rational arithmetic on the integer heights, two independent checkers: `code/exact_check.py` and PR #374's own `verify_standalone.py` (stdlib Kronecker substitution, run with --exact and --bound). Both pass for every certificate in `records/`. |
| Record eligibility | Not a record: superseded on 21 Nov 2026 by PR #345 (1.4513061918498968, 1.828e-7 lower). Was below every published value at 10:09 CT on 20 Nov. |
| Novelty | Improved construction: local polish of PR #374's construction (relative L2 distance about 1.4e-7); the maximum of |(v*v)_k| is at the single knot k = 165136. No new technique. |
| Search economics | 13 search steps over about 95 minutes of 2-core compute on 2026-11-19/20 (shotgun, NP-beta1 runs 1-4, NP-beta2 runs 5-12); 59 exact-checked certificates beat #374 (1 shotgun, 1 each in runs 1-2, 5 per run in runs 3-10, 6 in run 11, 10 in run 12); hit rate 20-60% per chain. |
| Decision | Archived 23 Nov 2026 (superseded by #345). Earlier notes: continuing (gate still loose). Run 11, a controlled test (same budget, 3 random seeds per arm), found that starting from a sample 5.8e-8 from the chain end beat starting from the chain end in 3 of 3 pairs (mean gain 1.76e-9 vs 5.1e-10); see runs/run11. Run 12 tested five seed distances (0 to 5.9e-8) with two random seeds each; see runs/run12. |

## Lean 4 proof (added 23 Nov 2026)

`lean/` adds a Lean 4 proof that this certificate's exact value is 2054622084077908729297673521179121664000/1415705270714577825348504941537856324889,
with the maximum at knot 165136. It uses no Mathlib and only the standard axioms; Lean's default and paranoid kernels,
lean4lean, nanoda and con-leche accept it (con-ron ran out of memory on the 8 GB build machine). The knot formula from
step function to coefficients is the one step left unformalized. See `lean/README.md`. The Python checkers above are unchanged.

## Record chain (each step's best; every row exact-checked by both checkers)

| Step | Time | Exact value | Below #374 (x1e-9) | exact_check / verify_standalone |
|---|---|---|---|---|
| 00_shotgun | 11-19 12:15 CT | 1.4513063999152274 | 0.77 | True / ACCEPTED |
| 01_run1 | 11-19 14:02 CT | 1.4513063934337895 | 7.25 | True / ACCEPTED |
| 02_run2_c1 | 11-19 14:22 CT | 1.4513063921690856 | 8.52 | True / ACCEPTED |
| 03_run3_t4 | 11-19 14:55 CT | 1.4513063899323682 | 10.76 | True / ACCEPTED |
| 04_run4_u5 | 11-19 15:11 CT | 1.4513063896445777 | 11.04 | True / ACCEPTED |
| 05_run5_v1 | 11-19 17:14 CT | 1.4513063886307913 | 12.06 | True / ACCEPTED |
| 06_run6_w4 | 11-19 17:32 CT | 1.4513063858140385 | 14.87 | True / ACCEPTED |
| 07_run7_x1 | 11-19 17:46 CT | 1.4513063825127677 | 18.18 | True / ACCEPTED |
| 08_run8_y1 | 11-19 18:12 CT | 1.4513063796015264 | 21.09 | True / ACCEPTED |
| 09_run9_z1 | 11-19 23:01 CT | 1.4513063788537772 | 21.83 | True / ACCEPTED |
| 10_run10_a5 | 11-19 23:25 CT | 1.4513063776308637 | 23.06 | True / ACCEPTED |
| 11_run11_D3 | 11-20 08:46 CT | 1.4513063755092774 | 25.18 | True / ACCEPTED |
| 12_run12_L2S1 | 11-20 10:09 CT | 1.4513063746953752 | 25.99 | True / ACCEPTED |

## Method
- **NP-beta1 (Nudge-Polish):** multiply one random block of 16-4,096 cells by (1 + sigma*N(0,1)), sigma log-uniform in
  [1e-8, 1e-6]; polish with p-norm annealed L-BFGS (`code/aaron/s5_search.py`) from p0 = 4096 for 25 s; keep the result
  only if the true max-norm score drops; chain from a shared best (`code/c1d_np.py`).
- **NP-beta2:** NP-beta1 behind two gates. Tightness gate: run only if the number of lags within 1e-8 of the max is at
  most 1% of the number within 1e-7 (C_1d: about 0.15-0.21%; the converged records we tested elsewhere: 92-100%).
  Bar-distance gate: the start must be within about 1e-8 of the live bar. Runs use 5 seed chains in parallel.
- Integer heights come from 56-bit rounding of the floats (`code/aaron/c1d_mkcert.py`); scores are exact on the integers.

## Folders
- `certificate/`: the record certificate (`.json`, and `_values.json` in PR #374's verifier format) and both checker outputs.
- `records/`: the best certificate of every search step, with both checker outputs.
- `runs/`: per-run logs (every sample: sigma, block, p0, input and output score), checker outputs for every chain, result cards, seed lists.
- `code/`: the search and grading code; `code/aaron/`: Aaron Porter's p-norm polish, certificate builder and checkers.
- `figures/`: the certificate and its autoconvolution, the tightness gate across six records, the record chain (PNG and PDF).

## Verify
    python3 -I code/exact_check.py certificate/c1d_n102400_1.4513063746953752.json
    python3 -I verify_standalone.py certificate/c1d_n102400_1.4513063746953752_values.json --exact 2054622084077908729297673521179121664000/1415705270714577825348504941537856324889
(`verify_standalone.py` is in PR #374's repository, linked below.)

## Sources and credit
- Starting construction and second checker: PR #374, [cweill/c1d-upper-bound](https://github.com/cweill/c1d-upper-bound).
- Registry: [teorth/optimizationproblems](https://github.com/teorth/optimizationproblems), constant 1d.
- p-norm polish and certificate tooling: Aaron Porter (`code/aaron/`).
