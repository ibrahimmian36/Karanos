#!/usr/bin/env python3
"""Independent re-check of the generated certificates.

Reads Karanos/Generated/{Witness,Equalities}.lean directly and verifies, with
no dependence on Lean or on the search engine:

  * the 896 partner certificates cover the full grid A x B, and no pair is
    its own partner;
  * every certificate identity holds under free reduction;
  * the homomorphisms to Z/42 and to Sym(4) kill both relators and between
    them separate every pair of distinct witness words.

Standard library only. Exit status 0 means every check passed.
"""
import re
import sys
from collections import Counter
from pathlib import Path

GEN = Path(__file__).resolve().parent.parent / "Karanos" / "Generated"
INV = {"a": "A", "A": "a", "b": "B", "B": "b"}
RELATORS = ["abaaBaaBB", "abbbabbbbAb"]
WORD = r"\[((?:Letter\.[aAbB](?:,\s*)?)*)\]"


def letters(s):
    return "".join(re.findall(r"Letter\.([aAbB])", s))


def reduce(w):
    out = []
    for c in w:
        if out and out[-1] == INV[c]:
            out.pop()
        else:
            out.append(c)
    return "".join(out)


def inverse(w):
    return "".join(INV[c] for c in reversed(w))


def word_list(text, name):
    body = text[text.index(f"def {name}"):].split(":=", 1)[1]
    body = body[: body.index("\n]") + 2]
    return [letters(m.group(1)) for m in re.finditer(WORD, body)]


def split_top(s):
    parts, cur, depth = [], "", 0
    for ch in s:
        depth += ch in "[(⟨"
        depth -= ch in "])⟩"
        if ch == "," and depth == 0:
            parts.append(cur)
            cur = ""
        else:
            cur += ch
    return parts + [cur]


def certificates(text):
    pat = re.compile(r"def pc\d+ : PartnerCert :=\s*⟨(.*)⟩[ \t]*$", re.M)
    piece = re.compile(r"⟨" + WORD + r",\s*(\d+),\s*(true|false)⟩")
    for m in pat.finditer(text):
        f = split_top(m.group(1))
        pieces = [(letters(p.group(1)), int(p.group(2)), p.group(3) == "true")
                  for p in piece.finditer(f[4])]
        yield letters(f[0]), letters(f[1]), letters(f[2]), letters(f[3]), pieces


def perm_mul(p, q):
    return tuple(p[q[i]] for i in range(4))


def perm_inv(p):
    r = [0] * 4
    for i, x in enumerate(p):
        r[x] = i
    return tuple(r)


AB = {"a": -8, "A": 8, "b": 1, "B": -1}
PERM = {"a": (1, 2, 0, 3), "b": (0, 3, 1, 2)}
PERM["A"], PERM["B"] = perm_inv(PERM["a"]), perm_inv(PERM["b"])


def ab_image(w):
    return sum(AB[c] for c in w) % 42


def perm_image(w):
    r = (0, 1, 2, 3)
    for c in w:
        r = perm_mul(r, PERM[c])
    return r


def main():
    witness = (GEN / "Witness.lean").read_text()
    A, B = word_list(witness, "witnessA"), word_list(witness, "witnessB")
    certs = list(certificates((GEN / "Equalities.lean").read_text()))
    ok = True

    def check(cond, msg):
        nonlocal ok
        print(("ok    " if cond else "FAIL  ") + msg)
        ok = ok and cond

    check((len(A), len(B)) == (32, 28), f"witness sizes {len(A)}, {len(B)}")
    check(all(reduce(w) == w for w in A + B), "witness words are freely reduced")
    check(max(map(len, A + B)) == 6, "maximum word length 6")

    grid = {(u, v) for u, v, _, _, _ in certs}
    check(grid == {(u, v) for u in A for v in B} and len(certs) == len(A) * len(B),
          f"{len(certs)} certificates cover the grid A x B exactly once")
    check(all((u, v) != (pu, pv) for u, v, pu, pv, _ in certs),
          "no pair is its own partner")
    check(all(pu in A and pv in B for _, _, pu, pv, _ in certs),
          "every partner lies in A x B")

    bad = 0
    for u, v, pu, pv, pieces in certs:
        rhs = "".join(c + (RELATORS[i] if s else inverse(RELATORS[i])) + inverse(c)
                      for c, i, s in pieces)
        bad += reduce(rhs) != reduce(u + v + inverse(pu + pv))
    check(bad == 0, "every certificate identity holds under free reduction")

    sizes = Counter(len(p) for *_, p in certs)
    total = sum(k * n for k, n in sizes.items())
    print(f"      free-group coincidences: {sizes[0]}; needing relators: "
          f"{len(certs) - sizes[0]}; conjugates: {total}; largest: {max(sizes)}")

    check(all(ab_image(r) == 0 for r in RELATORS), "Z/42 map kills both relators")
    check(all(perm_image(r) == (0, 1, 2, 3) for r in RELATORS),
          "Sym(4) map kills both relators")
    by_ab = by_perm = unseparated = 0
    for side in (A, B):
        for i, x in enumerate(side):
            for y in side[i + 1:]:
                if ab_image(x) != ab_image(y):
                    by_ab += 1
                elif perm_image(x) != perm_image(y):
                    by_perm += 1
                else:
                    unseparated += 1
    check(unseparated == 0,
          f"{by_ab + by_perm} pairs separated ({by_ab} by Z/42, {by_perm} more by Sym(4))")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
