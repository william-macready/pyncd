#!/usr/bin/env python3
"""Generate proof-free, mechanically copied transport and fixture consumers."""
import hashlib
import json
import pathlib
import re
import sys

root = pathlib.Path(sys.argv[1]).resolve()
out = pathlib.Path(sys.argv[2]).resolve()
expr = root / "leanncd/experiments/indexed_execution/IndexedComponentTransportExpr.lean"
tests = root / "leanncd/experiments/indexed_execution/IndexedComponentTransportTest.lean"
core = root / "leanncd/experiments/indexed_execution/IndexedComponentTransport.lean"
text = expr.read_text()
transport = text[text.index("def transport "):text.index("theorem footprint_transport")]
fixtures = tests.read_text()
start = fixtures.index("namespace IndexedComponentTransportTest")
fixtures = fixtures[start:]
fixtures = fixtures[:fixtures.index("\n#audit_axioms")]
fixtures = fixtures.replace("IndexedComponentTransportTest", "IndexedComponentTransportProbe")
fixtures = re.sub(r"\btransport\b", "probeTransport", fixtures)
# String fixture labels retain their original spelling for comparable failures.
fixtures = fixtures.replace('"probeTransport.', '"transport.')
fixtures = fixtures.replace(
    "open LeanNCD.Semantics IndexedComponentTransport",
    "open LeanNCD.Semantics IndexedComponentTransport\n\n" +
    transport.replace("transport", "probeTransport"))
body = "import IndexedComponentTransportEval\nimport Semantics.AxiomAudit\n\n" + fixtures
# The policy resolver is copied mechanically as a computational consumer, with
# its proof fields deliberately excluded, so mutations reach fixture assertions.
policy = core.read_text()
resolver = re.search(r"resolve := fun q => (.*)\n  inBounds", policy).group(1)
outcome = policy[policy.index("def mapOutcome "):policy.index("def mapResolved ")]
probe_policy = "\n" + outcome.replace("mapOutcome", "probeOutcome") + \
    "\ndef probeResolve (d : Domain srcShape dstShape) (p : ReadPolicy ℚ srcShape) " \
    "(q : RawCoord dstShape) := " + resolver.replace("mapOutcome", "probeOutcome") + "\n"
insertion = body.index("\n#eval check \"transport.axis-raw\"")
body = body[:insertion] + probe_policy + body[insertion:]
body = body.replace("(swapDomain.policy pointPolicy).resolve", "probeResolve swapDomain pointPolicy")
parity = """
#eval check "transport.probe-parity" <| [repeated, selected 0, selected 4, binder,
    zeroReduction, constantRead].all fun e => decide
  (addresses (footprint (probeTransport embed id e) ()) =
    addresses (footprint (IndexedComponentTransport.transport embed id e) ()) ∧
   evalReady RationalReference.ops available (probeTransport embed id e) () =
    evalReady RationalReference.ops available (IndexedComponentTransport.transport embed id e) () ∧
   evalReady RationalReference.ops missing (probeTransport embed id e) () =
    evalReady RationalReference.ops missing (IndexedComponentTransport.transport embed id e) ())
"""
body = body.replace("\nend IndexedComponentTransportProbe", parity + "\nend IndexedComponentTransportProbe")
body += "\n#audit_axioms IndexedComponentTransportProbe\n"
destination = root / "leanncd/experiments/indexed_execution/IndexedComponentTransportProbe.lean"
destination.parent.mkdir(exist_ok=True)
destination.write_text(body)
out.mkdir(parents=True, exist_ok=True)
hashes = {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
          for p in (expr, tests, core, destination)}
(out / "probe-source-hashes.json").write_text(json.dumps(hashes, indent=2) + "\n")
print("Generated", destination)
print("Exact transport recursion and policy resolve RHS extracted; no transport proofs copied.")
