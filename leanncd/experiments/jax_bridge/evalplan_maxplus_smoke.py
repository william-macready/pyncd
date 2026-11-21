"""Checked max-plus parity, metadata refusals and independent source/gradient pins."""
import argparse
import copy
import importlib.util
import itertools
import json
from pathlib import Path

import jax
import numpy as np


def load(path):
    spec = importlib.util.spec_from_file_location(Path(path).stem, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def native_path_oracle(inputs, nd):
    """Enumerate paths in the native carrier, independently of the plan/runtime."""
    init, trans, emit, allow = (np.asarray(inputs[n], dtype=nd)
                                for n in ("Init", "Trans", "Emit", "Allow"))
    states, = init.shape
    history, width = emit.shape
    assert width == states and trans.shape == allow.shape == (states, states)
    assert np.all(np.isfinite(allow)) and np.all((allow == 0) | (allow == 1)), \
        "finite binary masks are a companion-model precondition"
    assert np.all(np.isfinite(init) | np.isneginf(init))
    assert np.all(np.isfinite(trans)) and np.all(np.isfinite(emit[:-1])), \
        "active transition/emission factors must be finite"
    assert np.all(np.isnan(emit[-1])), "the unused emission row must remain NaN"
    best = np.full((states, history), -np.inf, dtype=nd)
    scored = []
    for t in range(history):
        for path in itertools.product(range(states), repeat=t + 1):
            if any(allow[a, b] == 0 for a, b in zip(path, path[1:])):
                continue
            value = nd(nd(0) + init[path[0]])
            for step, (a, b) in enumerate(zip(path, path[1:])):
                # Each source product starts at zero; the true predicate casts to zero.
                factor = nd(nd(0) + value)
                factor = nd(factor + trans[a, b])
                factor = nd(factor + emit[step, b])
                value = nd(factor + nd(0))
            if value > best[path[-1], t]:
                best[path[-1], t] = value
            if t == history - 1 and np.isfinite(value):
                scored.append((nd(nd(0) + value), path))
    scored.sort(reverse=True)
    score, winner = scored[0]
    margin = nd(score - scored[1][0])
    assert np.isfinite(score) and margin > 0, "AD requires a unique finite active winner"
    assert sum(value == score for value, _ in scored) == 1
    gradients = {n: np.zeros_like(inputs[n], dtype=nd) for n in ("Init", "Trans", "Emit")}
    gradients["Init"][winner[0]] = 1
    for t, (a, b) in enumerate(zip(winner, winner[1:])):
        gradients["Trans"][a, b] += 1
        gradients["Emit"][t, b] += 1
    return {"D": best, "Score": np.asarray(score)}, gradients, {
        "path": winner, "score": float(score), "runner_up_score": float(scored[1][0]),
        "gap": float(margin), "gap_in_output_ulps": float(margin / abs(np.spacing(score))),
        "finite_allowed_paths": len(scored), "unique_finite_active_winner": True}


def verify_gradient_points(precision, logic, runtime, *, modes=(False, True), cases=None):
    import jax.numpy as jnp
    dt = jnp.float64 if precision == 64 else jnp.float32
    nd = np.float64 if precision == 64 else np.float32
    ud = np.uint64 if precision == 64 else np.uint32
    suffix = str(precision)
    base = next(f for f in logic if f["name"] == "viterbi")

    def decode(f):
        return {n: np.asarray(t["bits"], dtype=ud).view(nd).reshape(t["shape"]).copy()
                for n, t in f["inputs" + suffix].items()}

    baseline = decode(base)
    points = {"baseline": baseline, "changed_winner": copy.deepcopy(baseline),
              "state_permuted": decode(next(f for f in logic if f["name"] == "viterbi_permuted")),
              "near_tie_below": copy.deepcopy(baseline),
              "near_tie_above": copy.deepcopy(baseline)}
    points["changed_winner"]["Init"][2] += nd(4)
    delta = nd(2) ** nd(-47 if precision == 64 else -18)
    points["near_tie_below"]["Init"][2] = nd(1) - delta
    points["near_tie_above"]["Init"][2] = nd(1) + delta
    expected = {name: native_path_oracle(xs, nd) for name, xs in points.items()}
    perm = np.asarray([2, 0, 3, 1])

    def transport(xs):
        return {"Init": xs["Init"][perm], "Trans": xs["Trans"][np.ix_(perm, perm)],
                "Emit": xs["Emit"][:, perm]}

    for n, wanted in dict(transport(baseline),
                          Allow=baseline["Allow"][np.ix_(perm, perm)]).items():
        np.testing.assert_array_equal(points["state_permuted"][n], wanted)
    base_grad = expected["baseline"][1]
    transported = transport(base_grad)
    for n, wanted in transported.items():
        assert np.array_equal(expected["state_permuted"][1][n], wanted), \
            f"gradient_transport state_permuted float{precision} oracle {n}"
    assert expected["state_permuted"][2]["path"] == tuple(
        int(np.flatnonzero(perm == s)[0]) for s in expected["baseline"][2]["path"])
    assert expected["state_permuted"][2]["score"] == expected["baseline"][2]["score"]
    assert expected["state_permuted"][2]["gap"] == expected["baseline"][2]["gap"]
    for name in ("changed_winner", "state_permuted", "near_tie_above"):
        assert expected[name][2]["path"] != expected["baseline"][2]["path"]
        assert not np.array_equal(expected[name][1]["Init"], base_grad["Init"])
        assert not np.array_equal(expected[name][1]["Trans"], base_grad["Trans"])
    assert expected["near_tie_below"][2]["path"] == expected["baseline"][2]["path"]
    assert expected["near_tie_above"][2]["path"] == expected["changed_winner"][2]["path"]
    for name in ("near_tie_below", "near_tie_above"):
        assert expected[name][2]["gap_in_output_ulps"] == 8
    report = {"gradient_points": [], "point_forwards": [], "gradients": []}
    for name, xs in points.items():
        report["gradient_points"].append({
            "name": name, "delta": float(delta) if name.startswith("near_tie") else None,
            **expected[name][2], "expected_gradients": {
                n: a.tolist() for n, a in expected[name][1].items()},
            "expected_forward_bits": {n: a.view(ud).tolist() for n, a in expected[name][0].items()},
            "mask_binary_finite": True, "unused_emit_row_nan": True})

    named = base["jax" + suffix]
    for positional in (False, True):
        def forward(params, allow):
            xs = dict(params, Allow=allow)  # Allow is explicit but never differentiated.
            if positional:
                store = runtime.run_plan_positional(
                    base["jaxpos" + suffix],
                    [xs[n] for n, _ in named["required_inputs"]], dtype=dt)
                return {n: store[s] for n, s in named["materialized"]}
            return runtime.run_named(named, xs, dtype=dt)

        grad = jax.grad(lambda params, allow: forward(params, allow)["Score"], argnums=0)
        functions = [(jit, jax.jit(forward) if jit else forward,
                      jax.jit(grad) if jit else grad) for jit in modes]
        for name, xs in points.items():
            if cases is not None and name not in cases:
                continue
            parameters = {n: jnp.asarray(xs[n]) for n in ("Init", "Trans", "Emit")}
            allow = jnp.asarray(xs["Allow"])
            wanted_forward, wanted_grad, _ = expected[name]
            for jit, forward_fn, grad_fn in functions:
                view = f"{'positional' if positional else 'named'} {'jit' if jit else 'eager'}"
                label = f"{name} float{precision} {view}"
                got_forward = forward_fn(parameters, allow)
                for n, wanted in wanted_forward.items():
                    got = np.asarray(got_forward[n])
                    assert got.dtype == wanted.dtype and got.shape == wanted.shape
                    assert np.array_equal(got.view(ud), wanted.view(ud)), \
                        f"point_forward {label} {n}: {got!r} != {wanted!r}"
                got_grad = grad_fn(parameters, allow)
                for n, wanted in wanted_grad.items():
                    got = np.asarray(got_grad[n])
                    assert got.dtype == wanted.dtype and got.shape == wanted.shape
                    assert np.array_equal(got, wanted), \
                        f"point_gradient {label} {n}: {got!r} != {wanted!r}"
                    if name == "state_permuted":
                        assert np.array_equal(got, transported[n]), \
                            f"gradient_transport {label} {n}: {got!r} != {transported[n]!r}"
                assert np.all(np.asarray(got_grad["Emit"])[-1] == 0), label
                report["point_forwards"].append({
                    "name": name, "jit": jit, "positional": positional,
                    "all_exports_exact": True})
                report["gradients"].append({
                    "name": name, "jit": jit, "positional": positional,
                    "all_parameter_counts_exact": True, "never_read_emit_row_zero": True,
                    "mask_not_differentiated": True,
                    "observed": {n: np.asarray(a).tolist() for n, a in got_grad.items()}})
    return report


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

    checked_module = load(checked_path)
    fixtures = checked_module.ADVERSARIAL
    assert len(fixtures) == 14
    bool_fixtures = checked_module.BOOLEAN
    assert len(bool_fixtures) == 17
    for f in fixtures + bool_fixtures:
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

    # Every max-plus term must reach the fold: B wins at 0, A at 2 and 4, C at 3, NaN in a non-last term at 5.
    multi = by["max_multi_term_winners"]
    assert len(multi["assign" + suffix]["terms"]) == 3, "max_multi_term_winners must render three terms"
    for jit in (False, True):
        got = np.asarray(run(multi, jit))
        wanted = np.asarray([2, -np.inf, 5, 7, 9, np.nan], dtype=nd)
        assert np.array_equal(got, wanted, equal_nan=True), ("max_multi_term_winners", jit, got)

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
    # Hole in the scan-level checks: an empty step range must still validate the step block.
    f = copy.deepcopy(by["scan_context_holes"])
    f["scan" + suffix].update(step_count=0)
    f["scan" + suffix]["step"]["nodes"][0]["algebra"] = "min_plus"
    cases.append(("empty_step_unknown_algebra", f))
    f = copy.deepcopy(by["scan_context_holes"])
    f["scan" + suffix].update(step_count=0)
    f["scan" + suffix]["step"]["nodes"][0]["terms"][0]["factors"][0]["bool_to_tropical"] = None
    cases.append(("empty_step_bad_factor_metadata", f))
    # Accept-neighbour: the same empty-range record with an unmodified step block is admitted.
    f = copy.deepcopy(by["scan_context_holes"])
    f["scan" + suffix].update(step_count=0)
    for jit in (False, True):
        assert len(run(f, jit)) == 1, ("empty step range with a valid step block must run", jit)
    # A max-plus scan whose states all start at 0 is legal (the Lean emitter writes `state_init` only
    # when some state is `.negInf`): omitting it must equal declaring every state "zero", never refuse.
    explicit = copy.deepcopy(by["scan_context_holes"])
    explicit["scan" + suffix]["state_init"] = ["zero"] * len(explicit["scan" + suffix]["state_shapes"])
    omitted = copy.deepcopy(explicit)
    del omitted["scan" + suffix]["state_init"], omitted["scan" + suffix]["semantics"]
    for jit in (False, True):
        a, b = run(explicit, jit), run(omitted, jit)
        assert len(a) == len(b) and all(np.array_equal(np.asarray(x), np.asarray(y), equal_nan=True)
                                        for x, y in zip(a, b)), ("omitted state_init must mean zero", jit)
    for name, f in cases:
        for jit in (False, True):
            try:
                run(f, jit)
            except ValueError as error:
                report["refusals"].append({"name": name, "jit": jit, "error": str(error)})
            else:
                raise AssertionError(("metadata silently admitted", name, jit))

    # --- Boolean (`ordered_boolean_v1`) raw fixtures: Lean-pinned above; each independent pin below
    # names the wrong implementation it kills. Values are NOT normalised to {0, 1} (mirrors Lean).
    bby = {f["name"]: f for f in bool_fixtures}
    z = nd(0)

    def values(name, jit):
        return np.asarray(run(bby[name], jit))

    def negative_zero(x):
        return bool(np.signbit(x)) and x == 0

    for jit in (False, True):
        # min keeps the FIRST operand on a tie; max keeps the SECOND (jnp.minimum/maximum differ).
        tie = values("bool_min_tie_order", jit)
        assert not negative_zero(tie[0]) and negative_zero(tie[1]), ("bool_min_tie_order", jit, tie)
        for name in ("bool_max_tie_reduction", "bool_max_tie_terms"):
            tie = values(name, jit)
            assert negative_zero(tie[0]) and tie[1] == 0 and not np.signbit(tie[1]), (name, jit, tie)
        # min is not `*`: 0.5,0.5 -> 0.5 (product .25); 2,2 -> 1 (product 4); 2,.5 -> .5.
        assert np.array_equal(values("bool_min_not_product", jit), np.asarray([.5, 1, 0, .5], dtype=nd))
        # max is not `+` at the reduction or the term fold (sums would be 2/.75).
        assert np.array_equal(values("bool_max_not_sum", jit), np.asarray([1, .5], dtype=nd))
        # NaN spreads through either operand of min and through max (NaN beats 2.0 and 0.5).
        assert np.all(np.isnan(values("bool_nan_factor_fold", jit)))
        got = values("bool_nan_reduction", jit)
        assert np.isnan(got[0]) and np.isnan(got[1]) and got[2] == 1, ("bool_nan_reduction", jit, got)
        # Iverson factor: included cells take min(x, 1), excluded cells min(x, 0).
        assert np.array_equal(values("bool_iverson_base", jit),
                              np.asarray([[.5, 1, 0], [0, .25, 1], [0, 0, .5]], dtype=nd))
        assert np.array_equal(values("bool_iverson_reduction", jit), np.asarray([.2, .3, .7], dtype=nd))
        # Step-dependent include tables: `[j <= l]` grows (monotone toy), `[l <= j]` shrinks.
        grows = np.asarray(run(bby["bool_scan_step_iverson"], jit)[0])
        assert np.array_equal(grows, np.asarray([[1, 1, 1, 1], [.5, 0, 0, 0], [1, 0, 0, 0]], dtype=nd)), grows
        shrinks = np.asarray(run(bby["bool_scan_step_iverson_ge"], jit)[0])
        assert np.array_equal(shrinks, np.asarray([[1, 1, 0, 0], [.5, .5, .5, 0], [1, 1, 1, 1]], dtype=nd)), shrinks
        # A unary read pads with real 0 THEN applies the function (sqrt(0) = 0 but exp(0) = 1), and
        # sqrt(-0) = -0 survives the folds.
        root = values("bool_unary_sqrt_oob", jit)
        assert root[0] == nd(.5) and negative_zero(root[1]) and np.all(root[2:] == 0), ("sqrt", jit, root)
        assert np.array_equal(values("bool_unary_exp_oob", jit), np.asarray([1, 0, 1, 1], dtype=nd))
        # A real destination reading a Boolean source copies it: no hidden cast (0.5, -3, 2 stay).
        assert np.array_equal(values("real_dest_reads_bool_source", jit), np.asarray([.5, -3, 2, .25], dtype=nd))
        assert "algebra" not in bby["real_dest_reads_bool_source"]["assign" + suffix]
        # Pads and seeds: bare out-of-bounds pad 0 (not -inf), empty factor product 1, empty reduction 0.
        assert np.array_equal(values("bool_bare_oob", jit), np.asarray([1, 0, 0], dtype=nd))
        assert float(values("bool_empty_factors", jit)) == 1
        assert float(values("bool_zero_reduction", jit)) == 0
        # `_ordered_min` scalar contract (Lean `minNaN`): first operand on a signed-zero tie, NaN spreads.
        a = jnp.asarray([0., -0., np.nan, 2., np.nan], dtype=dt)
        b = jnp.asarray([-0., 0., 3., np.nan, np.nan], dtype=dt)
        minimum = np.asarray((jax.jit(rt._ordered_min) if jit else rt._ordered_min)(a, b))
        assert not np.signbit(minimum[0]) and np.signbit(minimum[1]) and np.all(np.isnan(minimum[2:]))

    def bool_node(name):
        return bby[name]["assign" + suffix]

    def iverson_factor(node):
        return next(f for t in node["terms"] for f in t["factors"] if f.get("tag") == "iverson")

    def read_factor(node):
        return next(f for t in node["terms"] for f in t["factors"] if f.get("tag") == "read")

    bool_cases = []

    def refusal(name, template, mutate, scan=False):
        f = copy.deepcopy(bby[template] if template in bby else by[template])
        mutate(f["scan" + suffix] if scan else f["assign" + suffix])
        bool_cases.append((name, f))

    t = "bool_iverson_base"  # a valid Boolean record: one tagged read plus one Iverson factor
    refusal("bool_unknown_semantics", t, lambda n: n.update(semantics="future"))
    refusal("bool_missing_semantics", t, lambda n: n.pop("semantics"))
    refusal("bool_max_plus_semantics", t, lambda n: n.update(semantics="ordered_max_plus_v1"))
    refusal("semantics_without_algebra", t, lambda n: n.pop("algebra"))
    refusal("bool_real_to_bool_true", t, lambda n: read_factor(n).update(real_to_bool=True))
    refusal("bool_real_to_bool_missing", t, lambda n: read_factor(n).pop("real_to_bool"))
    refusal("bool_bool_to_tropical_key", t, lambda n: read_factor(n).update(bool_to_tropical=False))
    refusal("bool_missing_tag", t, lambda n: read_factor(n).pop("tag"))
    refusal("bool_unknown_tag", t, lambda n: read_factor(n).update(tag="future"))
    refusal("bool_include_short", t, lambda n: iverson_factor(n)["include"].pop())
    refusal("bool_include_long", t, lambda n: iverson_factor(n)["include"].append(1))
    refusal("bool_include_entry_2", t, lambda n: iverson_factor(n)["include"].__setitem__(0, 2))
    refusal("bool_include_entry_true", t, lambda n: iverson_factor(n)["include"].__setitem__(0, True))
    refusal("bool_read_with_include", t, lambda n: read_factor(n).update(include=[1]))
    refusal("iverson_in_real_node", "real_dest_reads_bool_source",
            lambda n: n["terms"][0]["factors"].__setitem__(0, {"tag": "iverson", "include": [1] * 4}))
    refusal("iverson_in_max_plus_node", "bool_to_tropical_true",
            lambda n: n["terms"][0]["factors"].__setitem__(0, {"tag": "iverson", "include": [1] * 7}))
    # Scan-level: an empty step range must still validate the Boolean step block's include table.
    s = "bool_scan_step_iverson"
    refusal("bool_scan_empty_step_bad_include", s, lambda n: (n.update(step_count=0), next(
        f for nd_ in n["step"]["nodes"] for tm in nd_["terms"] for f in tm["factors"]
        if f.get("tag") == "iverson")["include"].pop()), scan=True)
    refusal("bool_scan_empty_step_include_entry_2", s, lambda n: (n.update(step_count=0), next(
        f for nd_ in n["step"]["nodes"] for tm in nd_["terms"] for f in tm["factors"]
        if f.get("tag") == "iverson")["include"].__setitem__(0, 2)), scan=True)
    # Accept-neighbour: the same empty-range record with an unmodified step block is admitted.
    f = copy.deepcopy(bby[s])
    f["scan" + suffix].update(step_count=0)
    for jit in (False, True):
        assert len(run(f, jit)) == 1, ("empty step range with a valid Boolean step block must run", jit)
    bool_reason = {name: "ordered_boolean_v1 semantics" for name in (
        "bool_unknown_semantics", "bool_missing_semantics", "bool_max_plus_semantics")}
    bool_reason.update({name: "boolean read requires" for name in (
        "bool_real_to_bool_true", "bool_real_to_bool_missing", "bool_bool_to_tropical_key", "bool_missing_tag")})
    bool_reason.update({name: "include must be one 0/1 entry" for name in (
        "bool_include_short", "bool_include_long", "bool_include_entry_2", "bool_include_entry_true",
        "bool_scan_empty_step_bad_include", "bool_scan_empty_step_include_entry_2")})
    bool_reason.update({"semantics_without_algebra": "legacy metadata-free", "bool_unknown_tag": "unknown factor tag",
                        "bool_read_with_include": "only valid on an iverson factor",
                        "iverson_in_real_node": "require boolean algebra", "iverson_in_max_plus_node": "require boolean algebra"})
    assert set(bool_reason) == {name for name, _ in bool_cases}
    # A Boolean scan record carries no `state_init`/`semantics`: zero init, never refused.
    assert "state_init" not in bby[s]["scan" + suffix] and "semantics" not in bby[s]["scan" + suffix]
    for name, f in bool_cases:
        for jit in (False, True):
            try:
                run(f, jit)
            except ValueError as error:
                # The refusal must be for the changed field, not an accident of another check.
                assert bool_reason[name] in str(error), (name, jit, str(error))
                report["refusals"].append({"name": name, "jit": jit, "error": str(error)})
            else:
                raise AssertionError(("Boolean metadata silently admitted", name, jit))

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

    if logic_path:
        import evalplan_logic_smoke as oracle
        logic = load(logic_path).FIXTURES
        assert len(logic) == 13
        assert sum("jax" + suffix in f for f in logic) == 7
        assert all(not any(k.startswith("jax") for k in f)
                   for f in logic if f["name"].startswith("reachability"))
        report["logic"] = []

        def result(f, jit, positional):
            named = f["jax" + suffix]
            inputs = {n: array(t) for n, t in f["inputs" + suffix].items()}
            if positional:
                p = f["jaxpos" + suffix]
                args = [inputs[n] for n, _ in named["required_inputs"]]
                fn = lambda xs: rt.run_plan_positional(p, xs, dtype=dt)
                store = (jax.jit(fn) if jit else fn)(args)
                return {n: store[s] for n, s in named["materialized"]}
            fn = lambda xs: rt.run_named(named, xs, dtype=dt)
            return (jax.jit(fn) if jit else fn)(inputs)

        for positional in (False, True):
            for jit in (False, True):
                replaced = copy.deepcopy(logic)
                for f in replaced:
                    if not f["name"].startswith("viterbi"):
                        continue
                    got = result(f, jit, positional)
                    for n, a in got.items():
                        check(a, f["plan" + suffix][n], (f["name"], n, jit, positional))
                    f["plan" + suffix] = {n: entry(a) for n, a in got.items()}
                    report["logic"].append({"name": f["name"], "jit": jit,
                                             "positional": positional, "all_exports_exact": True})
                # The unmodified independent exhaustive-path and metamorphic oracle sees JAX values.
                oracle.verify(replaced)

        report.update(verify_gradient_points(precision, logic, rt))
        report["reachability"] = "6 fixtures checked/reference-only; no JAX plan emitted"

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
          f"{len(result.get('gradient_points', []))} gradient input points, "
          f"{len(result.get('point_forwards', []))} point-forward views, "
          f"{len(result.get('gradients', []))} gradient views")
