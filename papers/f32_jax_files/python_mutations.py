"""F32-JAX prototype: Python mutation cycles on a COPY of the runtime: each mutant must make the binary32
smoke fail; the unmutated copy must pass. Prints the observed failure line per mutant.
Run from repo root after applying both patches and ./run-evalplan-affine32.sh (generates the module)."""
import shutil, subprocess, sys, os
import tempfile
J = os.path.join(os.path.dirname(os.path.abspath(__file__)), '../../leanncd/experiments/jax_bridge')
PY = J + '/.cache/python/bin/python'
GEN = sys.argv[1] if len(sys.argv) > 1 else J + '/.cache/generated_evalplan_affine_smoke32.py'
D = tempfile.mkdtemp()
os.makedirs(D, exist_ok=True)
shutil.copy(J + '/evalplan_affine_smoke32.py', D)
src = open(J + '/evalplan_affine_runtime.py').read()
muts = [
    ("P1 tree reduction (jnp.sum) instead of ordered fold", "    reduced = jax.vmap(reduce_row)(mat)", "    reduced = jnp.sum(mat, axis=1)"),
    ("P2 term sum grouped by jnp.sum", "    return jax.lax.fori_loop(0, len(terms), term_body, zero)", "    return jnp.sum(stacked, axis=0)"),
    ("P3 factor product reversed", "            return acc * stacked[k]", "            return acc * stacked[len(factor_tensors) - 1 - k]"),
    ("P4 dtype guard skipped", "        if t is not None and t.dtype != dtype:", "        if False:"),
    ("P5 zero-pad mask ignored", "        padded = jnp.where(mask, gathered, dtype(0.0))", "        padded = gathered"),
    ("P6 positional nodes run in reverse order", """    for node in plan["nodes"]:
        store[node["dest"]] = _run_node(node, store, dtype)
    return store""", """    for node in reversed(plan["nodes"]):
        store[node["dest"]] = _run_node(node, store, dtype)
    return store"""),
]
def run():
    r = subprocess.run([PY, D + '/evalplan_affine_smoke32.py', GEN], capture_output=True, text=True)
    lines = (r.stdout + r.stderr).strip().splitlines()
    return r.returncode, lines[-1] if lines else ''
open(D + '/evalplan_affine_runtime.py', 'w').write(src)
print('unmutated:', run())
for label, old, new in muts:
    assert src.count(old) == 1, label
    open(D + '/evalplan_affine_runtime.py', 'w').write(src.replace(old, new))
    print(label, '->', run())
open(D + '/evalplan_affine_runtime.py', 'w').write(src)
print('restored:', run())
