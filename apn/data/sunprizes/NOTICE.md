# The Sun prizes dataset

The Zhi-Wei Sun conjectures that carry cash prizes on his homepage
([maths.nju.edu.cn/~zwsun](http://maths.nju.edu.cn/~zwsun/), transcribed
2026-08-24) *and* are formalized in Formal Conjectures at the pinned FC commit
(`fc_commit`): 8 of the page's 11 prized conjectures, one manifest row each,
vendored verbatim from upstream's `FormalConjectures/OEIS/<n>.lean`. The three
prized conjectures with no FC formalization at the pin (alternating sums of
consecutive primes, $1000; the representation n = x^4 + y^3 + z^2 + 2^k, $234;
the conjecture related to Bertrand's postulate, $100) are not members.

Each row records the prize as stated on the page (`prize_name`,
`prize_amount`, `prize_currency`) and the conjecture's OEIS sequence
(`oeis_id`). Membership is the committed manifest;
`scripts/generate_sunprizes_isolated.py` produces `Isolated/` from it.
