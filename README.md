# Congruences of Partitions

Rank Differences and Cubic Partition Pairs — an undergraduate project with
Abhishek Tyagi, supervised by Dr. Rupam Barman at IIT Guwahati.

- [Revised report (PDF)](report.pdf) — the complete report, proofread and updated
  on 17 October 2026; [LaTeX source](report.tex).
- [Elementary proof (PDF)](mao-rank-inequality.pdf) — a four-page standalone note;
  [Typst source](mao-rank-inequality.typ).
- [Original April 2018 report (PDF)](report-2018.pdf) — preserved unchanged;
  [original sources](https://github.com/cheran-senthil/BTP-Project/tree/93092556037234df1e2590f47c718a317cd40b96).

## The completed argument

Chapter 4 now proves, for every nonnegative integer `n`,

```text
d(3n+2) >= p_S(floor(n/3)) >= 1,
d(n) = N_2(0,6,n) + N_2(1,6,n) - N_2(2,6,n) - N_2(3,6,n).
```

Here `N_2(a,6,n)` counts partitions of `n` without repeated odd parts whose
M₂-rank is `a` modulo 6, and `p_S(m)` counts partitions into odd parts and
multiples of four. This includes the missing progression `d(9m+8)`.
Pairing consecutive Lambert-series terms and cancelling factors from the
partition-generating product gives an elementary coefficientwise proof.

All six chapters have been proofread, including corrections to signs,
exponents, congruence arguments, and references. The cubic partition-pair
chapters present known results with their attribution.

## Build and verify

Build the main report with Tectonic and the standalone note with Typst
(verified with Tectonic 0.17.0 and Typst 0.15.1):

```sh
tectonic report.tex
typst compile mao-rank-inequality.typ mao-rank-inequality.pdf
```

Run the exact coefficient checks with Python 3 (no third-party dependencies):

```sh
python3 verify_completion.py
python3 verify_identities.py
```

The first script compares direct rank counts through `n=300`, checks the
chapter 4 generating function through degree 1273 and the paired products
through degree 1274, and verifies the lower bound over that range. The
second checks Mao's full generating function against direct rank counts,
the other product identities, and the cubic partition congruences.
Finite checks supplement the formal proofs.
