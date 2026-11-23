"""Independent round trip: read <NS>/Data.lean, rebuild every height, compare with the certificate JSON.
Usage: python3 -I check_data.py DATA_LEAN VALUES_JSON"""
import json, re, sys
src = open(sys.argv[1]).read()
d = json.load(open(sys.argv[2]))
v = [int(x) for x in (d.get('values') or d.get('v_int'))]
n = int(re.search(r'def n : Nat := (\d+)', src).group(1))
K = int(re.search(r'def K : Nat := (\d+)', src).group(1))
w = int(re.search(r'def w : Nat := (\d+)', src).group(1))
cz = int(re.search(r'combine K (\d+) ', src).group(1))
parts = [int(h, 16) for h in re.findall(r'0x[0-9a-f]+', src)]
o = 1 << (w - 1); mask = (1 << K) - 1
out = []
for p in parts:                      # each chunk holds cz digits of K bits
    for i in range(cz):
        out.append(((p >> (K * i)) & mask) - o)
    assert p >> (K * cz) == 0
ok = (n == len(v) == len(out) and out == v)
print(f"n={n} K={K} w={w} chunks={len(parts)} round_trip={'OK' if ok else 'MISMATCH'}")
sys.exit(0 if ok else 1)
