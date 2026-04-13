# Proof101-Mini-Project
Final Mini Project for Introduction to Formal Verification &amp; Proof Assistants (Spring 2026) - Leaf-Binding in a 2-Leaf Merkle Tree

## Proof Techniques Used

This formalization uses a small set of Lean tactics and logical principles to prove binding for a 2-leaf Merkle tree.

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

