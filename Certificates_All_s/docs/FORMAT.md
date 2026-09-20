# Check the certificate files

Install the dependencies as described in [CAP.md](../CAP.md), then run
these commands from `Certificates_All_s/`:

```sh
.venv/bin/python -B cap.py integrity
.venv/bin/python -B tools/test_codec.py
```

The first command checks the supplied files against the package manifest.
The second runs the certificate reader tests. Both commands must finish
with exit code zero.

To verify the certificates on all exponent intervals, run the complete
replay command in [CAP.md](../CAP.md).
