# Reproduce the arithmetic tests

Install the dependencies as described in [CAP.md](../CAP.md), then run
these commands from `Certificates_All_s/` without `-O`:

```sh
.venv/bin/python -B tools/test_scalar.py
.venv/bin/python -B tools/test_vector.py
.venv/bin/python -B tools/test_products.py
.venv/bin/python -B tools/test_transcendentals.py
.venv/bin/python -B tools/test_polynomials.py
```

Each command must finish with exit code zero. These tests supplement the
complete certificate replay described in [CAP.md](../CAP.md).
