# Reproduce the certificate checks

Use Python 3.13 and run the following commands from `Certificates_All_s/`
in a fresh checkout:

```sh
python3 -m venv .venv
.venv/bin/python -m pip install -r requirements.txt
.venv/bin/python -B cap.py integrity
.venv/bin/python -B cap.py replay --jobs 1 --output /path/to/new-results
```

Replace `/path/to/new-results` with an output directory that does not exist.
Increase `--jobs` to run more intervals concurrently if sufficient memory is
available; individual intervals can require several gigabytes.

Use `-B` to prevent bytecode caches and run without `-O`.
The integrity check must print `PASS_FILE_INTEGRITY`. A successful complete
replay writes `SUMMARY.json` with status `PASS_COMPLETE_GLOBAL_REPLAY` in the
output directory.

To check a single interval, choose its identifier from `finite/cells.json`:

```sh
.venv/bin/python -B finite/replay.py --cell base_A_00 --jobs 1 --output /path/to/new-cell-results
```

This command checks only the selected interval. Use the complete replay
command above to reproduce all certificate checks.

For additional checks, see the [certificate reader tests](docs/FORMAT.md)
and [arithmetic tests](docs/EXACT_ARITHMETIC.md).
