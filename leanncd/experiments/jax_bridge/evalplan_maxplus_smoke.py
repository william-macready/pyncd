"""Checked max-plus parity, metadata refusals and independent source/gradient pins."""
import argparse
import copy
import importlib.util
import json
from pathlib import Path

import jax
import numpy as np


def load(path):
    spec = importlib.util.spec_from_file_location(Path(path).stem, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def verify(precision, checked_path, logic_path=None):
    jax.config.update("jax_enable_x64", precision == 64)
    import jax.numpy as jnp
    import evalplan_affine_runtime as rt
    dt = jnp.float64 if precision == 64 else jnp.float32
    nd = np.float64 if precision == 64 else np.float32
    ud = np.uint64 if precision == 64 else np.uint32
    suffix = str(precision)
    report = {"precision": precision, "x64": bool(jax.config.x64_enabled),
              "checked": [], "refusals": []}

    def array(t):
        return jnp.asarray(np.asarray(t["bits"], dtype=ud).view(nd).reshape(t["shape"]))

    def entry(a):
        a = np.asarray(a)
        return {"shape": a.shape, "bits": a.reshape(-1).view(ud).tolist()}

    def check(a, expected, label):
        a, b = np.asarray(a), np.asarray(array(expected))
        assert a.dtype == b.dtype and a.shape == b.shape, label
        mask = np.isnan(b)
        assert np.array_equal(np.isnan(a), mask), (label, a, b)
        assert np.array_equal(a.view(ud)[~mask], b.view(ud)[~mask]), (label, a, b)

    def run(f, jit=False, runtime=rt):
        inputs = [array(t) for t in f["store" + suffix]]
        if "scan" + suffix in f:
            fn = lambda xs: runtime._run_scan_node(f["scan" + suffix], xs, dt)
        else:
            fn = lambda xs: runtime.run_assign(f["assign" + suffix], xs, dtype=dt)
        return (jax.jit(fn) if jit else fn)(inputs)

    fixtures = load(checked_path).ADVERSARIAL
    assert len(fixtures) == 13
    for f in fixtures:
        for jit in (False, True):
            output = run(f, jit)
            if "scan" + suffix in f:
                for a, slot in zip(output, f["scan" + suffix]["dests"]):
                    check(a, f["expected" + suffix][slot], (f["name"], jit, slot))
            else:
                check(output, f["expected" + suffix], (f["name"], jit))
            report["checked"].append({"name": f["name"], "jit": jit,
                                      "observed": [entry(a) for a in output] if isinstance(output, list)
                                      else entry(output)})

    by = {f["name"]: f for f in fixtures}
    holes = np.asarray(run(by["scan_context_holes"])[0])
    assert np.isneginf(holes[1, 0]) and np.array_equal(
        holes[:, 1:], np.asarray([[7, 13, 19], [11, 17, 23]], dtype=nd)), holes
    assert np.isnan(np.asarray(run(by["false_source_opposing_infinity"]))[0])

    # Validate metadata even for empty domains: no silently ignored invalid tags.
    template = by["bool_to_tropical_true"]
    cases = []
    for name, changes in [
        ("unknown_algebra", {"algebra": "min_plus"}),
        ("unknown_semantics", {"semantics": "future"}),
        ("missing_semantics", {"semantics": None}),
        ("boolean_output", {"algebra": "boolean"}),
    ]:
        f = copy.deepcopy(template)
        f["assign" + suffix].update(changes)
        cases.append((name, f))
    for name, changes in [
        ("iverson", {"tag": "iverson"}),
        ("missing_cast", {"bool_to_tropical": None}),
        ("non_bool_cast", {"bool_to_tropical": 1}),
        ("real_to_bool", {"real_to_bool": True}),
    ]:
        f = copy.deepcopy(template)
        f["assign" + suffix]["terms"][0]["factors"][0].update(changes)
        cases.append((name, f))
    for name, changes in [
        ("unknown_init", {"state_init": ["pos_inf"]}),
        ("init_count", {"state_init": []}),
        ("unknown_scan_semantics", {"semantics": "future"}),
    ]:
        f = copy.deepcopy(by["scan_context_holes"])
        f["scan" + suffix].update(changes)
        cases.append((name, f))
    for name, f in cases:
        for jit in (False, True):
            try:
                run(f, jit)
            except ValueError as error:
                report["refusals"].append({"name": name, "jit": jit, "error": str(error)})
            else:
                raise AssertionError(("metadata silently admitted", name, jit))

    for jit in (False, True):
        assert float(run(by["max_factor_order_cancellation"], jit)) == 1, \
            "max_factor_order_cancellation: ordered [+2^54,-2^54,1] must retain one"
        reciprocal = np.asarray(run(by["max_reciprocal_partial_oob"], jit))
        assert reciprocal[0] == nd(.5) and np.all(np.isneginf(reciprocal[1:])), \
            ("max_reciprocal_partial_oob", jit, reciprocal)
        mixed = by["scan_mixed_init_holes"]
        node = mixed["scan" + suffix]
        assert len(node["dests"]) == 2 and sorted(node["state_init"]) == ["neg_inf", "zero"]
        for history, init in zip(run(mixed, jit), node["state_init"]):
            history = np.asarray(history)
            assert history[0, 0] == nd(3) and np.array_equal(
                history[:, 1:], np.asarray([[7, 13, 19], [11, 17, 23]], dtype=nd)), \
                ("scan_mixed_init_holes_history", jit, init, history)
            assert (np.isneginf(history[1, 0]) if init == "neg_inf" else
                    history[1, 0].view(ud) == ud(0)), \
                ("scan_mixed_init_holes_base", jit, init, history)

    # Ordered scalar contracts, including the zero-seed JVP regression.
    a = jnp.asarray([0., -0., np.nan, 2., np.nan], dtype=dt)
    b = jnp.asarray([-0., 0., 3., np.nan, np.nan], dtype=dt)
    for jit in (False, True):
        maximum = (jax.jit(rt._ordered_max) if jit else rt._ordered_max)(a, b)
        assert np.signbit(np.asarray(maximum)[0]) and not np.signbit(np.asarray(maximum)[1]), \
            "native_max_zero_tie: ordered max must choose the right signed zero"
        assert np.all(np.isnan(np.asarray(maximum)[2:]))
        for x, y, negative in [(0., -0., False), (-0., 0., False), (-0., -0., True)]:
            fn = jax.jit(rt._ordered_add) if jit else rt._ordered_add
            assert bool(np.signbit(np.asarray(fn(dt(x), dt(y))))) == negative
        grad = jax.grad(lambda x: rt._ordered_add(dt(0), x))
        assert float((jax.jit(grad) if jit else grad)(dt(0))) == 1, \
            "ordered_add_jvp_init: a winning zero Init must retain derivative one"

    return report


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("precision_name", nargs="?", choices=("float64", "float32"))
    parser.add_argument("bundle", nargs="?")
    parser.add_argument("--precision", type=int, choices=(32, 64))
    parser.add_argument("--checked")
    parser.add_argument("--logic")
    parser.add_argument("--out")
    args = parser.parse_args()
    if args.precision_name:
        if not args.bundle or args.precision or args.checked or args.logic:
            parser.error("use precision bundle OR --precision --checked [--logic]")
        bundle = load(args.bundle)
        args.precision = int(args.precision_name[-2:])
        args.checked = bundle.CHECKED_PATH
        args.logic = bundle.LOGIC_PATH
    elif args.bundle or not args.precision or not args.checked:
        parser.error("use precision bundle OR --precision --checked [--logic]")
    result = verify(args.precision, args.checked, args.logic)
    if args.out:
        Path(args.out).write_text(json.dumps(result, indent=2) + "\n")
    print(f"PASS max-plus{args.precision}: {len(result['checked'])} checked views, "
          f"{len(result['refusals'])} refusals, {len(result.get('logic', []))} source views, "
          f"{len(result.get('gradients', []))} gradient views")
