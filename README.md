# Reciprocal Neighbor Charges in First-Fit Coloring of Interval Graphs

An elementary, self-contained proof improving the upper bound on the competitive ratio of online First-Fit coloring of interval graphs from **$8$** (Narayanaswamy & Subhash Babu, 2008) to **$4 + 2\sqrt{2} \approx 6.82843$**, accompanied by a complete, end-to-end **Lean 4** formal proof (zero `sorry`, zero custom axioms) and independent Python audit scripts.

---

## Main Theorem

For every nonempty finite interval graph $G$ of clique number $\omega(G)$ and every arrival ordering, the number of colors $\chi_{\mathrm{FF}}(G)$ used by First-Fit satisfies:

$$\chi_{\mathrm{FF}}(G) \le (4 + 2\sqrt{2})\,\omega(G) + \sqrt{2} - 2 \approx 6.82843\,\omega(G) - 0.58579.$$

At the rational parameter $a = 17/5$, this yields the exact integer inequality:

$$35\,\chi_{\mathrm{FF}}(G) + 20 \le 239\,\omega(G) \qquad \left(\frac{239}{35} \approx 6.82857\right).$$

### Key Idea (1-Page Proof)
Building on the ordered column method of Pemmaraju–Raman–Varadarajan (2004), Narayanaswamy–Subhash Babu (2008), and Joret–Milans (2011), we assign a **borrowed** round one unit of income (net balance change $0$, rather than $0$ income). Tracking each side of a terminal column $x$ over maximal neighbor tenures ending in deletion yields the reciprocal charging inequality:

$$a b + 2 r \le 2 N,$$

combined with the terminal column's own balance $N - 1 \le a r + b$, survival $N \ge m + 3$ (for $3 < a \le 4$), and $r \le \omega(G)$. Eliminating $b$ and optimizing $a = 2 + \sqrt{2}$ immediately gives the bound $4 + 2\sqrt{2}$.

---

## Formal Verification (Lean 4)

The end-to-end rational theorem `first_fit_interval_rational_bound` ($35m + 20 \le 239d$ for every nonempty valid closed-interval First-Fit coloring, where $m$ is the largest color and $d \le \omega(G)$ is the maximum stabbing depth at left endpoints) is machine-checked in [`ReciprocalColumns.lean`](ReciprocalColumns.lean) using only Lean 4 `Std` (no Mathlib dependency):

- **Lean version**: Lean 4.15.0 (compiled with warnings as errors)
- **`sorry` count**: `0`
- **Axioms**: `#print axioms first_fit_interval_rational_bound` depends only on standard Lean axioms:
  ```text
  'first_fit_interval_rational_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
  ```

### Reproduce Verification

```bash
# 1. Verify the end-to-end Lean 4 proof (requires Lean 4.15+)
lean ReciprocalColumns.lean

# 2. Run independent exact-rational Python audits (Python 3.10+, stdlib only)
python3 audit_column_epochs.py
python3 column_bounds.py
```

---

## Repository Contents

| File | Description |
| :--- | :--- |
| [`first_fit_reciprocal_charges.pdf`](first_fit_reciprocal_charges.pdf) | Compiled research note containing the complete 1-page proof, endpoint conventions, and comparison with the classical $8\omega$ count. |
| [`first_fit_reciprocal_charges.tex`](first_fit_reciprocal_charges.tex) | LaTeX source of the research note. |
| [`ReciprocalColumns.lean`](ReciprocalColumns.lean) | Complete end-to-end Lean 4 formalization (795 lines, zero `sorry`, standard axioms only). |
| [`audit_column_epochs.py`](audit_column_epochs.py) | Independent exact-`Fraction` audit of completed neighbor epochs, 1,274 abstract histories, 80 mixed-endpoint graphs, and KST wall $T_4$. |
| [`column_bounds.py`](column_bounds.py) | Stress tests across 220 random graphs, recursive anchored walls (up to 3,212 intervals), and 710 geometric cuts. |
| [`anchored_walls.py`](anchored_walls.py) | Depth-$d$ anchored-wall sweep-line search certifying $A(1)=3, A(2)=7, A(3)=11$ and finite-width bounds. |

---

## 日本語概要（Japanese Summary）

区間グラフのオンライン彩色における First-Fit（最小の空き色を選ぶ貪欲法）の競合比について、2008年の Narayanaswamy–Subhash Babu による上界 **$8$**（$8\omega - 3$）を18年ぶりに更新し、**$4 + 2\sqrt{2} \approx 6.82843$**（厳密には $\chi_{\mathrm{FF}}(G) \le (4 + 2\sqrt{2})\omega(G) + \sqrt{2} - 2$、有理数版 $35\chi_{\mathrm{FF}}(G) + 20 \le 239\omega(G)$）を証明しました。

- 証明本体は1ページ未満の初等的な議論で完結しています（[`first_fit_reciprocal_charges.pdf`](first_fit_reciprocal_charges.pdf)）。
- 有理数版定理 $35m + 20 \le 239d$ は [`ReciprocalColumns.lean`](ReciprocalColumns.lean) にて Lean 4.15.0 で**完全エンドツーエンド形式検証済み**です（`sorry` ゼロ、標準公理のみ）。

---

## Transparency & Acknowledgments

The proof discovery, Lean 4 formalization, and verification workflow were conducted in collaboration with frontier AI reasoning models (OpenAI GPT-6 Astra / Codex and Gemini) under human problem selection, auditing, and verification. Every claim in the rational theorem is independently machine-checked by the Lean 4 kernel.

## References

1. S. V. Pemmaraju, R. Raman, and K. R. Varadarajan, *Buffer minimization using max-coloring*, SODA 2004, 562–571.
2. N. S. Narayanaswamy and R. Subhash Babu, *A note on First-Fit coloring of interval graphs*, Order 25 (2008), 49–53.
3. G. Joret and K. G. Milans, *First-Fit is linear on posets excluding two long incomparable chains*, Order 28 (2011), 455–464.
4. H. A. Kierstead, D. A. Smith, and W. T. Trotter, *First-fit coloring on interval graphs has performance ratio at least 5*, European Journal of Combinatorics 51 (2016), 236–254.
