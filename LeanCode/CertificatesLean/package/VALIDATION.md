# Current verification scope

This is the current source-bound numerical package for the eight-point proof.
The full CAP has not yet been formalized or verified in Lean.

- `INDEX.json`: active finite cover, boundary and analytic premise references.
- `AnalyticFinite/INDEX.json`: immutable30-cell inputs and allowed validation orders.
- `ANALYTIC_PREMISES.json`: current analytic implications and numerical obligations.
- `verification/analytic_finite/`: accepted full finite receipts.
- `verification/tail/`: exact boundary receipts.
- `verification/fixed_tables/`: four independently checked optional Lean table witnesses.
- `source_bindings.json` and `MANIFEST.json`: complete source and input integrity.

Run `python3 -B check.py --integrity-only` for the stored-evidence audit.
Without that option, `check.py` also freshly runs the exact boundary; it does
not silently rerun the30 finite cells. The sibling `Verification/run_checks.py`
runs all30 cells, audits the fresh reports, replays the boundary, and checks
all four stored tables independently. Use the pinned requirements and run
on Xeonhetzner as described in the root `README.txt`. Never use Python `-O`.

The manuscript supplies the universal analytic implications. Every final
strict inequality, complete remainder, physical-domain condition and checked
table identity remains an explicit obligation. A source hash or PASS string
replaces neither those implications nor their arithmetic checks.
