# Global optimality for every exponent `s ≥ 0`

This directory contains the Lean proof of global optimality of the square antiprism for every real
$s\ge0$, with logarithmic energy at $s=0$. The final theorem is
`ThomsonCompact.Statement.all_s_global_optimality` in
[ThomsonCompact/Main/Final.lean](ThomsonCompact/Main/Final.lean). It is stated with verbatim copies of the
definitions of [Showcase.lean](../../Showcase.lean), and
[Showcase_WithProofs.lean](../../Showcase_WithProofs.lean) restates it in the paper's notation.

The proof covers $s\in[0,97]$ by 30 finite cells and $s\ge97$ by an analytic tail argument. Each cell
carries a certificate (Bernstein square factors with an exact correction). Its computer-assisted part is
checked by a Boolean checker with a proof of soundness, evaluated in the Lean kernel by `decide +kernel`
on packed natural-number data. No `native_decide` is used. The certificate data are generated from
[LeanCode/CertificatesLean](../CertificatesLean).

| Path | Contents |
| --- | --- |
| [ThomsonCompact/Main](ThomsonCompact/Main) | The all-exponent statement from the 30 cells, the root, the cover and the tail. |
| [ThomsonCompact/Cells](ThomsonCompact/Cells) | The 30 cells: certificate data, kernel checks and the theorem `ThomsonCompact.Cells.cell<i>`. |
| [ThomsonCompact/Packed](ThomsonCompact/Packed) | Packed natural-number Taylor models, interval arithmetic and their soundness. |
| [ThomsonCompact/Target](ThomsonCompact/Target) | Hermite target models on the height of each cell. |
| [ThomsonCompact/CoeffMap](ThomsonCompact/CoeffMap) | The coefficient map and the Gram block contributions. |
| [ThomsonCompact/Floor](ThomsonCompact/Floor) | Residual, correction and floor bounds. |
| [ThomsonCompact/Fixed](ThomsonCompact/Fixed) | The right inverses of degrees 12, 14, 16 and 18. |
| [ThomsonCompact/Interface](ThomsonCompact/Interface) | Per-degree assembly of a cell from its checked parts. |
| [ThomsonCompact/TailC](ThomsonCompact/TailC) | The algebraic certificates of the tail $s\ge97$. |
| [AllS](AllS), [Blueprint](Blueprint), [Pilot](Pilot) | Analytic finite theory, certificate soundness, equality recovery, cover, tail argument, and the catalogues and tables they use. |

The tail also uses [LeanCode/LargeS](../LargeS). The final theorem depends only on `propext`,
`Classical.choice` and `Quot.sound`.
