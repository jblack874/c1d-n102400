# Lean 4 proof of the certificate (added 23 Nov 2026; the Python checkers are unchanged)

This repository is an archive (superseded by PR #345); the Lean proof certifies this certificate's own value.

Follows the checking conventions used for the Lean proof of the Riemann Hypothesis released 20 Nov 2026: the statement
in a separate challenge file, the proof in a solution file, `lake comparator` to confirm both state the same theorem
with no axioms beyond the standard three, and the exported proof replayed by external kernels (`--paranoid`).

**Theorem `C1d.certificate`** (`C1d/Challenge.lean`), for the heights `v` of `certificate/c1d_n102400_1.4513063746953752_values.json`:
`v.length = n`, `v.sum = S`, every coefficient of `c_k = Σ_{i+j=k} v_i v_j` satisfies max_k |c_k| ≤ M, the maximum is attained,
and `2·n·M / S² = num/den`, giving C_1d ≤ 1.4513063746953753 (exact 2054622084077908729297673521179121664000/1415705270714577825348504941537856324889).

| Check | Result |
|---|---|
| `lake comparator --paranoid` (`comparator_C1d_output.txt`) | Lean default kernel, Lean paranoid kernel, lean4lean, nanoda and con-leche accept. con-ron was killed for lack of memory on the 8 GB build machine (exit 137, kernel OOM log), so it gave no verdict. |
| `#print axioms` (`axioms_output.txt`) | `propext`, `Classical.choice`, `Quot.sound` only; no `sorry`, no `native_decide` |
| `tools/check_data.py` (`check_data_output.txt`) | Every height in `C1d/Data.lean` equals the certificate JSON |

**How the proof works** (`Autoconv/`, about 690 lines including comments, no Mathlib):
- `Kronecker.lean`: `conv a b k` is the `k`-th coefficient of the schoolbook product, and evaluating at `B` turns that
  product into one integer multiplication.
- `Bits.lean`: if `X = Σ x_i·2^(K·i)` with `x_i < 2^K`, then `X AND (mask of bits w…K-1 in every digit) = 0` proves
  every `x_i < 2^w`.
- `Final.lean`: with heights stored as base-`2^K` digits of one number `P`, the kernel checks the bound with a few
  big-integer operations (one squaring, two ANDs, closed-form geometric sums), never one coefficient at a time.

**Trusted definitions** (what the statement means): `gd`, `conv` (`Autoconv/Basic.lean`), `combine`, `unpackK`
(`Autoconv/Pack.lean`) and the data in `C1d/Data.lean`.
**Not formalized:** the knot formula that turns `2·n·M/S²` into `max_t |(f*f)(t)| / (∫f)²` for the step function with `n` equal
cells on `[-1/4, 1/4]` (the registry's standard reduction).

Reproduce (Lean v4.36.0-rc1, no dependencies; `bwrap` needed for the comparator sandbox; about 8 GB RAM):
```
lake build
lake comparator --config=comparator_C1d.json --paranoid
lake env lean Axioms.lean
python3 -I tools/check_data.py C1d/Data.lean ../certificate/c1d_n102400_1.4513063746953752_values.json
```
