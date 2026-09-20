# Reproduce the verification

Follow the setup instructions in [CAP.md](../CAP.md). From
`Certificates_All_s/`, run:

```sh
.venv/bin/python -B cap.py replay --jobs 1 --output /path/to/new-results
```

Choose an output directory that does not exist. Inspect the result with:

```sh
.venv/bin/python -m json.tool /path/to/new-results/SUMMARY.json
```

The status must be `PASS_COMPLETE_GLOBAL_REPLAY`.

To display the supplied summary, run:

```sh
.venv/bin/python -B cap.py status
```

The `status` command reads the supplied results; it does not repeat the
computations.
