# Advanced component-composition fixture prototype

Prototype authoring only: **exactly two component pairs**, not an acceptance matrix.
Both pairs supply genuine local `SourceContractMatch` values and `MatchedComponent`
packages, explicit `Boundary` values, real assembled graphs, and proofs of
`close_ok`. The observations below are graph-only, copied from actual
`lean-file.sh` runs. No composite match or execution correspondence is claimed.

## Collision, multiplicity, and two simultaneous order changes

Module: `IndexedComponentCompositionCollisionFixtures`.
Exports: `collisionProducer`, `collisionConsumer`, `collisionBoundary`,
`collisionGraph`, `collision_close_ok`, `collisionWriterProvenance`,
`collisionEvents`, `collisionValues`, `collisionPreMetadata`,
`collisionAssembledPreMetadata`, `collisionAdmittedSourceOrder`,
`collisionAssembledAdmittedSourceOrder`.

Donor: `IndexedComponentCompositionLocalFixtures.producerMatch`; the refined
collision pair replaces its two Pre statements with **one statement and three
valuations**, admitting v=0 and v=2 with equal +1 values and rejecting v=1.
Extend its declarations with one private scalar Audit carrying literal 7
and one valuation, and give that tensor old UID 2. The local
tensor type is `Fin 2` with UIDs 0/2, hence injective. Reuse the unchanged
`IndexedComponentCompositionPortFixtures.consumerComponent 4`, whose private
Audit also has old UID 2, tag 30, and capability 301. Only Pre is wired, using
`Domain.id []`.

Producer tensor validation enumeration is `[Pre, privateAudit]`; collector order
is `[privateAudit, Pre]`. Pre collector capabilities are `[102,101]`; fragment
positions are `[Pre10/101, Pre11/102, private30/301]`. The local schedule follows
both collector and capability order changes, with its `priority` proof, rather
than sorting IDs or concatenating writer positions. Pre writer 10/101 is
statement 0, valuation 0; writer 11/102 is statement 0, valuation 2.
Capability order `[102,101]` therefore executes v2 before v0.
The main scalar donor remains unchanged and continues to distinguish its two
statement identities; no extra component pair was added.

Discriminated interpretations:

- Private same-ID tensors/tags/capabilities must remain distinct across sides;
  only the explicit boundary identifies Pre.
- Two separately identified equal +1 occurrences must both contribute.
- Valuation count 3 and guards `[true,false,true]` must survive source context
  transport: dropping the third valuation or admitting the rejected middle
  valuation is not equivalent. Admitted identity/order must remain v2 then v0,
  not renumbered or sorted.
- Tensor enumeration must not replace collector order; writer position must not
  replace capability order. Both disagreements are present in this one pair.

Observed outcome: `"complete"`.
Observed local **and assembled** Pre metadata `(statements, valuations, guards)`:

```text
(1,3,[true,false,true])
```

Observed local admitted source order
`(tensor index, statement index, valuation index, tag, capability)`:

```text
[(1,0,0,30,301), (0,0,2,11,102), (0,0,0,10,101)]
```

Observed assembled upstream admitted source order
`(local tensor index, statement index, valuation index)`:

```text
[(1,0,0), (0,0,2), (0,0,0)]
```

The first row is private Audit; both Pre rows retain statement 0 and their
actual admitted valuation identities. The rejected v1 has no source occurrence
or writer. These constructed metadata and ordered identities are checked by
the same failing-on-difference observation check as the existing events.

Writer provenance `(new tag, new capability, destination UID)`:

```text
[(20,202,0), (22,204,0), (60,602,4), (41,403,3), (61,603,5)]
```

Observed full events `(kind, tag-or-destination-UID, capability-or-0, value)`:

```text
[("write",60,602,7), ("publish",4,0,7),
 ("write",22,204,1), ("write",20,202,1), ("publish",0,0,2),
 ("write",41,403,4), ("publish",3,0,4),
 ("write",61,603,5/2), ("publish",5,0,5/2)]
```

Final availability in order Pre, Out, upstream private, downstream private:
`some [some 2, some 4, some 7, some (5/2)]`.
Both old private UID 2 tensors become distinct UIDs 4 and 5; old private writer
30/301 becomes 60/602 upstream and 61/603 downstream.

## Unequal-axis whole-port adapter and non-palindromic repeated reads

Module: `IndexedComponentCompositionAxisFixtures`.
Exports: `axisProducer`, `axisConsumer`, `axisBoundary`, `axisGraph`,
`axis_close_ok`, `axisMappedReads`, `axisMappedFootprint`,
`axisWriterProvenance`, `axisEvents`, `axisValues`.

Donors: certified `IndexedComponentTransportTest.swapDomain`, `srcShape`,
`dstShape`, `pointPolicy`, `p`, and `q`, plus the existing local-match packaging
pattern. Producer owns only array Pre with `dstShape=[(91,3),(92,2)]`.
Six scalar statements each have one valuation; destinations use the actual
`canonicalLayout dstShape` enumeration, literal values are 1 through 6, local
writer tags are 110 through 115 and capabilities 510 through 515.
Consumer owns input Pre with `srcShape=[(11,2),(12,3)]` and scalar Out.
Boundary explicitly uses `swapDomain` consumer-src to producer-dst, not a
coordinate matcher.

The donor's palindromic p/q/p body was tightened, as requested, to **p/q/p/q**
by adding a final q read. Both source body and fragment reads retain the full
non-palindromic ordered list; local `writer_reads` and `eval_agrees` are proved.

Discriminated interpretations:

- Unequal ordered axis IDs/extents require the certified swap adapter.
- Distinct per-coordinate literals distinguish the transported coordinates.
- The full exact non-palindromic list rejects reversal and set/dedup readings.
  Addition alone does not detect reversal; the footprint assertion does.

Observed outcome: `"complete"`.
Both mapped writer reads and actual transported-body footprint:

```text
[(0,2,0), (0,0,1), (0,2,0), (0,0,1)]
```

The first entry in each triple identifies producer Pre (UID 0).
Observed writer provenance `(new tag, new capability, destination UID, coordinates)`:

```text
[(220,1020,0,[0,0]), (222,1022,0,[0,1]),
 (224,1024,0,[1,0]), (226,1026,0,[1,1]),
 (228,1028,0,[2,0]), (230,1030,0,[2,1]), (421,1403,3,[])]
```

Observed full events:

```text
[("write",220,1020,1), ("publish",0,0,1),
 ("write",222,1022,2), ("publish",0,0,2),
 ("write",224,1024,3), ("publish",0,0,3),
 ("write",226,1026,4), ("publish",0,0,4),
 ("write",228,1028,5), ("publish",0,0,5),
 ("write",230,1030,6), ("publish",0,0,6),
 ("write",421,1403,14), ("publish",3,0,14)]
```

Final producer cells in canonical layout order and consumer Out:
`some ([some 1,some 2,some 3,some 4,some 5,some 6], some 14)`.

## Verification and exact next state

Both real modules were checked with the checkout's `leanncd/scripts/lean-file.sh`,
passing the absolute checkout `leanncd/` directory and each experiment path.
After the guard/valuation refinement, both exact source byte sequences passed
`check-snippet.sh`; the first collision snippet attempt lacked the
`IndexedComponentCompositionPortFixtures` dependency during a concurrent
targeted rebuild, and passed when retried after that successful build.
The modules contain failing-on-difference `#eval` checks for the observed full
events, provenance, terminal values, and mapped repeated read list; they are
not merely printed examples. Local matches and assembled closure are checked
by Lean. No `sorry`, new axioms, `native_decide`, or unsafe execution was added.

Parent registered both new modules in the experiment target; the targeted
wrapper build of `+IndexedComponentCompositionCollisionFixtures` and
`+IndexedComponentCompositionAxisFixtures` completed with exit status 0.
This dispatch does not edit existing modules or `lakefile.toml`. Parent owns records/audit,
the full build, and subsequent general correspondence wiring once
`compose_match` actually exists. No copied-computation or mutation tooling was
created; mutation testing and correspondence remain explicitly deferred.

The accompanying `advanced_fixtures_prototype.patch` is mechanically regenerated
from the committed, checked source modules against the pre-fixture source base
`d9eedd5d^`, excluding this receipt. Axis source bytes are unchanged by this
refinement.

Budget: receipt drafted at action turn 33; close-out uses 41 action turns,
one above the 40-turn target but below the 60-turn hard cap.
The bounded guard/valuation refinement uses **15 new action turns**, for
**56 lifetime action turns**, within its 30-new-turn target and lifetime
60-turn checkpoint.
The supplied `token-report.py` returned
`no transcript for session 166c28b7-d291-45be-9935-ac49e19535cb`, so cumulative
and retained token counts are unavailable rather than fabricated. No known
60-turn/250k-context cap breach.
