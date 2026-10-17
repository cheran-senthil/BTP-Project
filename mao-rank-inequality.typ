#set document(title: "An elementary proof of a partition rank inequality of Mao",
  description: "A coefficientwise positivity argument and an explicit lower bound for M2-rank differences.")
#set page(paper: "a4", margin: (x: 24mm, y: 22mm), numbering: "1")
#set text(font: "New Computer Modern", size: 11pt, lang: "en")
#set par(justify: true, leading: 0.65em)
#set heading(numbering: "1.")
#show heading: set text(size: 12pt)
#set math.equation(numbering: "(1)", supplement: [Equation])
#show math.equation: set block(above: 0.85em, below: 0.85em)
#show link: set text(fill: rgb("234e70"))
#let qed = h(1fr) + $□$

#align(center)[
  #text(size: 18pt, weight: "bold")[An elementary proof of a partition\ rank inequality of Mao]
  #v(0.6em)
  #text(size: 10pt)[17 October 2026]
]
#v(0.6em)
#block(inset: (x: 9mm))[
  #set text(size: 10pt)
  *Abstract.* We give an elementary coefficientwise proof of Mao’s inequality
  for the $M_2$-rank of partitions without repeated odd parts in the progression
  $3n+2$. Starting from a generating-function identity of Barman and Sachdeva,
  we pair consecutive terms of an alternating Lambert series. After multiplication
  by a partition-generating product, each pair has nonnegative coefficients.
  This yields an explicit lower bound by a restricted partition function and
  includes the progression $9n+8$, which was not covered by their partial result.
]

= Introduction and statement of the result

Let $lambda$ be a nonempty partition without repeated odd parts. If $ell(lambda)$
is its largest part and $nu(lambda)$ its number of parts, its $M_2$-rank is
$
  r_2 (lambda) = ceil(ell(lambda)/2)-nu(lambda).
$
Assign the empty partition rank zero.
Write $N_2 (a,6,n)$ for the number of such partitions of $n$ with
$M_2$-rank congruent to $a$ modulo 6, and set
$
  d(n)=N_2 (0,6,n)+N_2 (1,6,n)-N_2 (2,6,n)-N_2 (3,6,n).
$ <difference>
The inequality considered here is $d(3n+2)>0$ for every $n>=0$.
Barman and Sachdeva [1] established it when $n ≢ 2 space (mod 3)$,
leaving the values $d(9m+8)$ outside the scope of their proof. This remaining
progression is also the unfinished problem discussed in Chapter 4 of the
April 2018 undergraduate report [3].

Define
$
  S={k in ZZ_(>0):k ≢ 2 space (mod 4)}, quad
  P(q)=product_(k in S) 1/(1-q^k)=sum_(m>=0)p_S (m)q^m.
$ <partition-product>
Thus $p_S (m)$ counts partitions of $m$ into odd parts and multiples of four;
as usual, $p_S (0)=1$.

*Theorem 1.* _For every integer $n>=0$,_
$
  d(3n+2)>=p_S (floor(n/3))>=1.
$ <main-bound>
_Equivalently, for every $m>=0$ and $a in {2,5,8}$,_
$
  d(9m+a)>=p_S (m)>=1.
$

Jennings-Shaffer and Reihill [2, Section 7] proved the stronger result
$d(n)>0$ for every $n>=0$ using asymptotic formulas. Here we give an
elementary proof in the progression $3n+2$, with the bound in @main-bound.

#pagebreak()
= Reduction to coefficientwise positivity

All calculations take place in the ring $QQ[[q]]$ of formal power series.
For $A,B in QQ[[q]]$, write $A ≽ B$ if every coefficient of $A-B$ is
nonnegative. Multiplication by a series with nonnegative coefficients
preserves this order.

We use the standard notation
$
  (a_1,dots,a_t;q)_infinity
  =product_(i=1)^t product_(j>=0)(1-a_i q^j), quad
  phi(q)=sum_(j in ZZ)q^(j^2).
$
In particular, $J_(3,12)=(q^3,q^9,q^12;q^12)_infinity$ satisfies
$1/J_(3,12)=P(q^3)$.

*Proposition 2 (Barman–Sachdeva).* _The generating function of the rank
differences in @difference satisfies_
$
  D(q) &:=sum_(n>=0)d(3n+2)q^n \
       &=P(q^3)/q [ (phi(q)^2+phi(q^3)^2)/4
         -sum_(j in ZZ) ((-1)^j q^(6j^2+3j))/(1+q^(6j)) ].
$ <starting-identity>

This is the combination of Proposition 3.1 and Lemma 3.3 of [1]. It is the
only previously established rank-difference identity used in the proof.
The bilateral series is interpreted formally by rewriting negative-index
summands with nonnegative powers of $q$.

For $j>=1$, the negative-index term has the form
$
  ((-1)^(-j)q^(6j^2-3j))/(1+q^(-6j))
  =(((-1)^j q^(6j^2-3j))q^(6j))/(1+q^(6j))
  =((-1)^j q^(6j^2+3j))/(1+q^(6j)).
$
Consequently, isolating the term with index zero and pairing the remaining
indices gives
$
  sum_(j in ZZ) ((-1)^j q^(6j^2+3j))/(1+q^(6j))
  =1/2+2sum_(j>=1)((-1)^j q^(6j^2+3j))/(1+q^(6j)).
$
Define
$
  T(q)=(phi(q)^2+phi(q^3)^2-2)/4, quad
  L(q)=sum_(j>=1)((-1)^(j+1)q^(2j^2+j))/(1+q^(2j)).
$ <auxiliary-series>
@starting-identity therefore becomes
$
  D(q)=1/q [P(q^3)T(q)+2P(q^3)L(q^3)].
$ <reduced-identity>
The bracketed expression has zero constant term, so division by $q$
produces a formal power series. Each sum is locally finite: only finitely
many indices can contribute to a fixed coefficient, since the minimum
exponents grow quadratically.

The series $T(q)$ is manifestly nonnegative. The remaining task is to show
that $P(q)L(q)$ is also nonnegative, even though the summands defining
$L(q)$ alternate in sign.

#pagebreak()
= A positivity lemma

*Lemma 3.* _With $P(q)$ and $L(q)$ as above, $P(q)L(q) ≽ 0$._

*Proof.* For each positive odd integer $r$, pair the term of index $r$
with the term of index $r+1$, and write
$
  B_r (q)=P(q)[q^(2r^2+r)/(1+q^(2r))
               -q^(2(r+1)^2+r+1)/(1+q^(2r+2))].
$ <paired-term>
The difference between the two numerator exponents is
$2(r+1)^2+r+1-(2r^2+r)=4r+3$. Taking a common denominator gives
$
  B_r (q)=q^(2r^2+r)P(q)
    ((1-q^(4r+3))+q^(2r+2)(1-q^(4r+1))) /
    ((1+q^(2r))(1+q^(2r+2))).
$ <paired-fraction>
Now factor
$
  1/((1+q^(2r))(1+q^(2r+2)))
  =((1-q^r)(1+q^r)(1-q^(2r+2))) /
    ((1-q^(4r))(1-q^(4r+4))).
$ <factorization>

For $s in {4r+1,4r+3}$, put
$
  Q_(r,s) (q)&:=P(q)(1-q^r)(1-q^(2r+2))(1-q^s)\
    &=product_(k in S ∖ {r,2r+2,s})1/(1-q^k).
$ <removed-parts>
To justify the second equality, observe that $r$ and $s$ are odd, whereas
$2r+2$ is divisible by four. All three numbers belong to $S$ and are
distinct: $r<2r+2<4r+1<=s$. Thus the three numerator factors cancel
three different denominator factors in $P(q)$. The remaining product
has nonnegative coefficients, so $Q_(r,s) (q) ≽ 0$.

Substituting @factorization and @removed-parts into @paired-fraction yields
the explicit nonnegative expression
$
  B_r (q)=
  (q^(2r^2+r)(1+q^r))/((1-q^(4r))(1-q^(4r+4)))
  [Q_(r,4r+3) (q)+q^(2r+2)Q_(r,4r+1) (q)].
$ <positive-expression>
Every factor on the right has nonnegative coefficients. Hence $B_r (q) ≽ 0$
for every positive odd $r$. Summing these pairs gives
$
  P(q)L(q)=sum_(r>=1, r " odd")B_r (q) ≽ 0.
$
This regrouping is valid in $QQ[[q]]$, because the minimum exponent in
$B_r (q)$ is $2r^2+r$, which tends to infinity with $r$. #qed

*Remark.* The cancellation in @removed-parts is the role of the product
$P(q)$. Positivity is proved for each paired term after multiplication by
this product. No coefficientwise positivity of the alternating series
$L(q)$ alone is required.

#pagebreak()
= Proof of the main theorem

*Proof of Theorem 1.* Since $phi(q)$ has nonnegative coefficients, the
definition of $T(q)$ gives
$
  T(q)=q+q^2+q^3+q^4+2q^5+dots ≽ q+q^2+q^3.
$
Here $q$ and $q^2$ arise from $phi(q)^2/4$, and $q^3$ arises from
$phi(q^3)^2/4$. Subtracting the two constant terms in @auxiliary-series
does not affect any positive-degree coefficient.

By Lemma 3, $P(q^3)L(q^3) ≽ 0$. It follows from @reduced-identity that
$
  D(q) ≽ P(q^3)/q (q+q^2+q^3)
       =P(q^3)(1+q+q^2).
$ <coefficient-bound>
Expanding the right-hand side using @partition-product gives
$
  P(q^3)(1+q+q^2)
  =sum_(m>=0)p_S (m)(q^(3m)+q^(3m+1)+q^(3m+2)).
$
Thus the coefficient of $q^n$ on the right-hand side of @coefficient-bound is
$p_S (floor(n/3))$, proving the first inequality in @main-bound.
Finally, $p_S (m)>=1$ for every $m>=0$: the partition into ones is
allowed for $m>0$, and the empty partition supplies $p_S (0)=1$.
This proves the theorem. #qed

*Verification.* The accompanying script, #raw("verify_completion.py"),
checks the generating-function identity against direct rank counts through
$n=300$ and checks its series expansion through $q^1273$. The paired
product identities are checked through $q^1274$. These finite computations
are independent checks of the formulas and indexing; the proof above holds
for all indices without them. In the previously missing progression,
$
  (d(9m+8))_(m=0)^9=(1,2,5,7,9,15,23,31,40,56).
$

#heading(numbering: none)[References]
#set text(size: 10pt)

#block(breakable: false)[
  [1] R. Barman and A. P. S. Sachdeva, _Proof of a limited version of Mao’s
  partition rank inequality using a theta function identity_, Research in
  Number Theory *2* (2016), article 22.
  #link("https://doi.org/10.1007/s40993-016-0055-5")[doi:10.1007/s40993-016-0055-5].
  #link("https://arxiv.org/pdf/1605.06037")[Full text (PDF)].
]

#block(breakable: false)[
  [2] C. Jennings-Shaffer and D. Reihill, _Asymptotic formulas related to the
  $M_2$-rank of partitions without repeated odd parts_, arXiv:1805.11319.
  First submitted *29 May 2018*; revised 22 February 2019.
  #link("https://arxiv.org/pdf/1805.11319v1")[May 2018 version (PDF)] ·
  #link("https://arxiv.org/pdf/1805.11319v3")[revised version (PDF)] ·
  #link("https://arxiv.org/abs/1805.11319")[abstract and version history].
  The prior proof of $d(n)>0$ is in Section 7, inequality (7.2).
]

#block(breakable: false)[
  [3] _Congruences of Partitions: Rank Differences and Cubic Partition Pairs_,
  B.Tech. project report, Indian Institute of Technology Guwahati, April 2018,
  Chapter 4.
  #link("https://github.com/cheran-senthil/BTP-Project/blob/93092556037234df1e2590f47c718a317cd40b96/report.pdf")[Original report (PDF)] ·
  #link("https://github.com/cheran-senthil/BTP-Project")[source repository].
]
