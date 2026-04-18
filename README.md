# Leaf-Binding in a 2-Leaf Merkle Tree: A Lean 4 Proof

---

## Overview

This project formally proves that in a 2-leaf Merkle tree, any valid signature commits to exactly one leaf public key, determined by its index bit. It also shows that a signature cannot simultaneously satisfy both leaf positions, and that mismatched (forged) signatures are rejected.

---

## Design Choices

### `BitVec 256` instead of `Nat`

The proof was previously attempted using Cantor pairing over `Nat`. But it was rejected due to its bijectivity and fully invertible nature. Instead, `BitVec 256` was used to model fixed-size hash outputs. So `H` remains uninterpreted (and thus `noncomputable`).

### `HashModel` typeclass instead of loose axioms

`H` and its injectivity assumption `H_inj` are bundled in a single typeclass:

```lean
class HashModel where
  H     : HashVal → HashVal → HashVal
  H_inj : ∀ a b c d : HashVal, H a b = H c d → a = c ∧ b = d
```

This ensures any concrete instantiation must provide both together. It also makes the assumption explicit and named; `H_inj` is clearly stated as
an idealisation, since real hash functions are not injective (collisions exist by pigeonhole).

### `leaf_ver` as a black-box predicate

The leaf verification predicate is defined as `msg = leaf_pk`. This is intentional (the binding theorem holds for **any** leaf predicate). Making it a parameter keeps the theorem broadly general.

### Concrete signatures set `leaf_sig = 0`

`leaf_sig` is carried in the signature structure but is never inspected by any proof (it is bound to `_` in the `cases` destruct). Setting it to `0` in
concrete examples makes clear that it plays no role in the structural binding argument.

---

## Main Theorems

### `leaf_binding`

```lean

theorem leaf_binding
    (leaf_verify : HashVal → HashVal → HashVal → Prop)
    (pk0 pk1 msg : HashVal)
    (sig : Sig)
    (hv : verify leaf_verify (tree_root pk0 pk1) msg sig) :
    (sig.idx = false ∧ sig.leaf_pk = pk0) ∨
    (sig.idx = true  ∧ sig.leaf_pk = pk1) := by
  cases sig with
  | mk idx lpk _ sib =>
    obtain ⟨_, h_tree⟩ := hv
    simp only [tree_root] at h_tree -- tr: H pk0 pk1, h_tree : (if idx then H sib lpk else H lpk sib) = H pk0 pk1
    cases idx with
    | false => exact Or.inl ⟨rfl, (H_inj lpk sib pk0 pk1 h_tree).left⟩
    | true  => exact Or.inr ⟨rfl, (H_inj sib lpk pk0 pk1 h_tree).right⟩
```

A valid signature commits to exactly one leaf, determined by the index bit. The verifier learns unambiguously which leaf was used.

**Importance**: Core security property of the Merkle tree layer. Without it, an adversary could present a signature that passes verification while claiming either leaf, breaking authentication.

---

### `compositional`

```lean

theorem compositional
    (pk0 pk1 msg : HashVal)
    (sig : Sig)
    (hv : verify leaf_ver (tree_root pk0 pk1) msg sig) :
    ((sig.idx = false ∧ sig.leaf_pk = pk0) ∨
     (sig.idx = true  ∧ sig.leaf_pk = pk1)) ∧
    msg = sig.leaf_pk := by
  obtain ⟨h_leaf, h_tree⟩ := hv
  exact ⟨leaf_binding leaf_ver pk0 pk1 msg sig ⟨h_leaf, h_tree⟩, h_leaf⟩
```

Combines tree binding with the leaf predicate in one result. The message used to verify equals the committed leaf key.

**Importance**: Shows the two layers (Merkle tree and leaf) compose correctly; the message is not only structurally bound to a leaf but also satisfies the leaf predicate.

---

References

- Buchmann, Dahmen, Hülsing. *XMSS – A Practical Forward Secure Signature Scheme Based on Minimal Security Assumptions*. PQCrypto 2011. https://eprint.iacr.org/2011/484.pdf  

- Hülsing et al. *XMSS: eXtended Merkle Signature Scheme*. RFC 8391, May 2018. https://www.rfc-editor.org/rfc/rfc8391

---

## Proof Strategies: Techniques & Tactics

| Category | Technique / Tactic | Where Used | Purpose |
| --- | --- | --- | --- |
| **Tactics** | `cases` | `leaf_binding` | Case split on `Sig` and `Bool idx` to handle both leaf paths |
|  | `simp` | `sig0_ok`, `sig1_ok`, `sig_bad_rejected` | Unfold definitions like `tree_root`, `sig0` and reduce equalities |
|  | `rfl` | `sig0_ok`, `sig1_ok` | Close `leaf_ver` goals via definitional equality `msg = lpk` |
|  | `exact` | `leaf_binding` | Supply proof terms `Or.inl` / `Or.inr` directly |
|  | `obtain` / `have` | `leaf_binding`, `compositional`, `sig_bad_rejected` | Destructure hypotheses and name intermediate results |
|  | `intro` | `sig_bad_rejected` | Introduce assumption to prove negation |
| **Logic** | Case analysis | `leaf_binding` | Split `if idx` into `true` / `false` branches |
|  | Injectivity | `leaf_binding`, `sig_bad_rejected` | Use `H_inj` to deduce `a = c ∧ b = d` from `H a b = H c d` |
|  | Proof by contradiction | `sig_bad_rejected` | Derive `0xFF = pk0` then reduce to `False` |
|  | Conjunction / Disjunction intro | `leaf_binding`, `compositional` | Build `∧` and `∨` conclusions |
| **Structure** | Typeclass abstraction | `HashModel` | Bundle `H` with `H_inj` axiom for parametric theorems |
|  | Modular composition | `compositional` | Combine structural binding + leaf verification |
|  | Instantiation | `sig0_full`, `sig1_full` | Apply general theorems to specific signatures |

---

## Challenges

Firstly, the hash function was kept abstract, and injectivity was assumed.

The root computation was defined noncomputably as:

```lean
noncomputable def tree_root (pk0 pk1 : HashVal) : HashVal :=
  H pk0 pk1
```
Secondly, the public keys were hardcoded as fixed 256-bit values:

```lean
def pk0 : HashVal := 0x0000000000000000000000000000000000000000000000000000000000000042
def pk1 : HashVal := 0x0000000000000000000000000000000000000000000000000000000000000063

-- #eval the keys to confirm they are well-formed 256-bit values
#eval pk0.toHex
#eval pk1.toHex
#eval (pk0 == pk1)
```

Thirdly, signature construction was simplified by encoding validity directly into the structure:

```lean
def sig0 : Sig := ⟨false, pk0, 0, pk1⟩
def sig1 : Sig := ⟨true,  pk1, 0, pk0⟩
```

It was observed that even though `tree_root pk0 pk1` unfolds to `H pk0 pk1`, it doesn't simplify any further. Since `H` is uninterpreted, tree equalities don’t close with `rfl` because they’re not definitionally equal without extra unfolding.

Previously, this limitation led to introducing additional axioms to explicitly assert tree equalities.

This was resolved as follows: the signatures were made so as to align with their expected tree structure. This allowed `simp [tree_root, sig0]` to unfold structure fields. Thus both sides of the goal became the same expression (`H pk0 pk1`). At that point, the goal closes by definitional equality.
