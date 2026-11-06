# Certificates carried by the Lean proof

This directory contains the certificates from which the Lean proof of global optimality for every
$s\ge0$ in [LeanCode/AllS](../AllS) was generated. The Lean proof does not read these files: the data
generated from them are part of the Lean sources, as packed hexadecimal numerals, and the Lean kernel
checks them. The files document where the Lean data come from and can be checked independently in Python.

[package](package) is a byte-identical copy of the certificate package. It covers $[0,97]$ by 30 cells
and treats $s\ge97$ analytically, with an exact boundary certificate. This package differs from the
one in [Certificates_All_s](../../Certificates_All_s), which uses 111 intervals covering $[0,124]$.

| Path | Contents | Lean |
| --- | --- | --- |
| [package/AnalyticFinite](package/AnalyticFinite) | The 30 finite cells: cell parameters, root data and Bernstein square-factor witnesses. | [ThomsonCompact/Cells](../AllS/ThomsonCompact/Cells) |
| [package/Tail](package/Tail) | The exact boundary certificate `witness.json` for $s\ge97$. | [ThomsonCompact/TailC](../AllS/ThomsonCompact/TailC) |
| [package/verification/fixed_tables](package/verification/fixed_tables) | The right-inverse tables of degrees 12, 14, 16 and 18. | [ThomsonCompact/Fixed](../AllS/ThomsonCompact/Fixed) |
| [package/verification](package/verification) | Acceptance receipts of the numerical replay. | |
| [package/INDEX.json](package/INDEX.json), [package/MANIFEST.json](package/MANIFEST.json) | Cover, analytic premises and SHA-256 of every file. | |

The cells in the order of `Blueprint.CellSpec`:

| Cell | $s$-interval | Degree | Certificate | Lean |
| --- | --- | --- | --- | --- |
| 0 | $[0,2/5]$ | 12 | [`base_A_01`](package/AnalyticFinite/cells/base_A_01.json), [witness](package/AnalyticFinite/witnesses/base_A_01.capd.xz) | [`Cells/base_A_01`](../AllS/ThomsonCompact/Cells/base_A_01) |
| 1 | $[2/5,8/5]$ | 12 | [`base_A_05`](package/AnalyticFinite/cells/base_A_05.json), [witness](package/AnalyticFinite/witnesses/base_A_05.capd.xz) | [`Cells/base_A_05`](../AllS/ThomsonCompact/Cells/base_A_05) |
| 2 | $[13/10,19/10]$ | 12 | [`base_A_08`](package/AnalyticFinite/cells/base_A_08.json), [witness](package/AnalyticFinite/witnesses/base_A_08.capd.xz) | [`Cells/base_A_08`](../AllS/ThomsonCompact/Cells/base_A_08) |
| 3 | $[19/10,5/2]$ | 12 | [`base_B_00`](package/AnalyticFinite/cells/base_B_00.json), [witness](package/AnalyticFinite/witnesses/base_B_00.capd.xz) | [`Cells/base_B_00`](../AllS/ThomsonCompact/Cells/base_B_00) |
| 4 | $[12/5,14/5]$ | 12 | [`base_B_02`](package/AnalyticFinite/cells/base_B_02.json), [witness](package/AnalyticFinite/witnesses/base_B_02.capd.xz) | [`Cells/base_B_02`](../AllS/ThomsonCompact/Cells/base_B_02) |
| 5 | $[14/5,19/5]$ | 12 | [`base_B_04`](package/AnalyticFinite/cells/base_B_04.json), [witness](package/AnalyticFinite/witnesses/base_B_04.capd.xz) | [`Cells/base_B_04`](../AllS/ThomsonCompact/Cells/base_B_04) |
| 6 | $[19/5,21/5]$ | 12 | [`base_B_09`](package/AnalyticFinite/cells/base_B_09.json), [witness](package/AnalyticFinite/witnesses/base_B_09.capd.xz) | [`Cells/base_B_09`](../AllS/ThomsonCompact/Cells/base_B_09) |
| 7 | $[39/10,49/10]$ | 12 | [`base_B_11`](package/AnalyticFinite/cells/base_B_11.json), [witness](package/AnalyticFinite/witnesses/base_B_11.capd.xz) | [`Cells/base_B_11`](../AllS/ThomsonCompact/Cells/base_B_11) |
| 8 | $[49/10,11/2]$ | 12 | [`base_B_15`](package/AnalyticFinite/cells/base_B_15.json), [witness](package/AnalyticFinite/witnesses/base_B_15.capd.xz) | [`Cells/base_B_15`](../AllS/ThomsonCompact/Cells/base_B_15) |
| 9 | $[11/2,61/10]$ | 12 | [`base_B_18`](package/AnalyticFinite/cells/base_B_18.json), [witness](package/AnalyticFinite/witnesses/base_B_18.capd.xz) | [`Cells/base_B_18`](../AllS/ThomsonCompact/Cells/base_B_18) |
| 10 | $[61/10,67/10]$ | 12 | [`base_B_21`](package/AnalyticFinite/cells/base_B_21.json), [witness](package/AnalyticFinite/witnesses/base_B_21.capd.xz) | [`Cells/base_B_21`](../AllS/ThomsonCompact/Cells/base_B_21) |
| 11 | $[67/10,73/10]$ | 12 | [`base_B_24`](package/AnalyticFinite/cells/base_B_24.json), [witness](package/AnalyticFinite/witnesses/base_B_24.capd.xz) | [`Cells/base_B_24`](../AllS/ThomsonCompact/Cells/base_B_24) |
| 12 | $[36/5,8]$ | 12 | [`base_B_26`](package/AnalyticFinite/cells/base_B_26.json), [witness](package/AnalyticFinite/witnesses/base_B_26.capd.xz) | [`Cells/base_B_26`](../AllS/ThomsonCompact/Cells/base_B_26) |
| 13 | $[8,89/10]$ | 12 | [`base_B_30`](package/AnalyticFinite/cells/base_B_30.json), [witness](package/AnalyticFinite/witnesses/base_B_30.capd.xz) | [`Cells/base_B_30`](../AllS/ThomsonCompact/Cells/base_B_30) |
| 14 | $[177/20,191/20]$ | 12 | [`base_B_35`](package/AnalyticFinite/cells/base_B_35.json), [witness](package/AnalyticFinite/witnesses/base_B_35.capd.xz) | [`Cells/base_B_35`](../AllS/ThomsonCompact/Cells/base_B_35) |
| 15 | $[19/2,101/10]$ | 12 | [`base_B_38`](package/AnalyticFinite/cells/base_B_38.json), [witness](package/AnalyticFinite/witnesses/base_B_38.capd.xz) | [`Cells/base_B_38`](../AllS/ThomsonCompact/Cells/base_B_38) |
| 16 | $[101/10,11]$ | 12 | [`base_B_41`](package/AnalyticFinite/cells/base_B_41.json), [witness](package/AnalyticFinite/witnesses/base_B_41.capd.xz) | [`Cells/base_B_41`](../AllS/ThomsonCompact/Cells/base_B_41) |
| 17 | $[87/8,15]$ | 12 | [`base_C_00`](package/AnalyticFinite/cells/base_C_00.json), [witness](package/AnalyticFinite/witnesses/base_C_00.capd.xz) | [`Cells/base_C_00`](../AllS/ThomsonCompact/Cells/base_C_00) |
| 18 | $[15,16]$ | 12 | [`base_C_07`](package/AnalyticFinite/cells/base_C_07.json), [witness](package/AnalyticFinite/witnesses/base_C_07.capd.xz) | [`Cells/base_C_07`](../AllS/ThomsonCompact/Cells/base_C_07) |
| 19 | $[16,43/2]$ | 14 | [`finite_d14_c18`](package/AnalyticFinite/cells/finite_d14_c18.json), [witness](package/AnalyticFinite/witnesses/finite_d14_c18.capd.xz) | [`Cells/finite_d14_c18`](../AllS/ThomsonCompact/Cells/finite_d14_c18) |
| 20 | $[43/2,55/2]$ | 14 | [`finite_d14_c23`](package/AnalyticFinite/cells/finite_d14_c23.json), [witness](package/AnalyticFinite/witnesses/finite_d14_c23.capd.xz) | [`Cells/finite_d14_c23`](../AllS/ThomsonCompact/Cells/finite_d14_c23) |
| 21 | $[55/2,67/2]$ | 14 | [`finite_d14_c29`](package/AnalyticFinite/cells/finite_d14_c29.json), [witness](package/AnalyticFinite/witnesses/finite_d14_c29.capd.xz) | [`Cells/finite_d14_c29`](../AllS/ThomsonCompact/Cells/finite_d14_c29) |
| 22 | $[67/2,79/2]$ | 14 | [`finite_d14_c35`](package/AnalyticFinite/cells/finite_d14_c35.json), [witness](package/AnalyticFinite/witnesses/finite_d14_c35.capd.xz) | [`Cells/finite_d14_c35`](../AllS/ThomsonCompact/Cells/finite_d14_c35) |
| 23 | $[79/2,85/2]$ | 14 | [`finite_d14_c41`](package/AnalyticFinite/cells/finite_d14_c41.json), [witness](package/AnalyticFinite/witnesses/finite_d14_c41.capd.xz) | [`Cells/finite_d14_c41`](../AllS/ThomsonCompact/Cells/finite_d14_c41) |
| 24 | $[167/4,197/4]$ | 14 | [`finite_d14_c44`](package/AnalyticFinite/cells/finite_d14_c44.json), [witness](package/AnalyticFinite/witnesses/finite_d14_c44.capd.xz) | [`Cells/finite_d14_c44`](../AllS/ThomsonCompact/Cells/finite_d14_c44) |
| 25 | $[97/2,103/2]$ | 14 | [`finite_d14_c50`](package/AnalyticFinite/cells/finite_d14_c50.json), [witness](package/AnalyticFinite/witnesses/finite_d14_c50.capd.xz) | [`Cells/finite_d14_c50`](../AllS/ThomsonCompact/Cells/finite_d14_c50) |
| 26 | $[50,62]$ | 16 | [`finite_d16_c56`](package/AnalyticFinite/cells/finite_d16_c56.json), [witness](package/AnalyticFinite/witnesses/finite_d16_c56.capd.xz) | [`Cells/finite_d16_c56`](../AllS/ThomsonCompact/Cells/finite_d16_c56) |
| 27 | $[62,82]$ | 16 | [`finite_d16_c68`](package/AnalyticFinite/cells/finite_d16_c68.json), [witness](package/AnalyticFinite/witnesses/finite_d16_c68.capd.xz) | [`Cells/finite_d16_c68`](../AllS/ThomsonCompact/Cells/finite_d16_c68) |
| 28 | $[81,87]$ | 16 | [`extension_d16_c84_h2`](package/AnalyticFinite/cells/extension_d16_c84_h2.json), [witness](package/AnalyticFinite/witnesses/extension_d16_c84_h2.capd.xz) | [`Cells/extension_d16_c84_h2`](../AllS/ThomsonCompact/Cells/extension_d16_c84_h2) |
| 29 | $[87,97]$ | 18 | [`extension_d18_c92_h2`](package/AnalyticFinite/cells/extension_d18_c92_h2.json), [witness](package/AnalyticFinite/witnesses/extension_d18_c92_h2.capd.xz) | [`Cells/extension_d18_c92_h2`](../AllS/ThomsonCompact/Cells/extension_d18_c92_h2) |

## Checking the package

With the pinned versions in [package/requirements.txt](package/requirements.txt), run

```sh
cd package
python3 -B check.py --integrity-only
```

This audits the stored evidence and reports `PASS_REDUCED_PACKAGE_INTEGRITY`. Without
`--integrity-only`, `check.py` also replays the exact boundary certificate.
