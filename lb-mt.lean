-- Leaf-binding for a 2-leaf Merkle tree in Lean 4
-- Hash values are typed as BitVec 256 (fixed 256-bit output).
-- H is bundled with its injectivity assumption in a typeclass.

-- ============================================================
-- 1.  MODEL
-- ============================================================

-- Fixed 256-bit output type - correct type for a hash value.
abbrev HashVal := BitVec 256

/--
  HashModel bundles the hash function H with its injectivity assumption.
  Any instantiation must provide both.
  Injectivity is an idealisation: Real hash functions are not injective.
-/
class HashModel where
  H     : HashVal → HashVal → HashVal
  H_inj : ∀ a b c d : HashVal, H a b = H c d → a = c ∧ b = d

variable [HashModel]
open HashModel

-- ============================================================
-- 2.  DEFINITIONS
-- ============================================================

structure Sig where
  idx      : Bool
  leaf_pk  : HashVal
  leaf_sig : HashVal
  sibling  : HashVal

noncomputable def tree_root (pk0 pk1 : HashVal) : HashVal :=
  H pk0 pk1

def verify
    (leaf_verify : HashVal → HashVal → HashVal → Prop)
    (root msg : HashVal)
    (sig : Sig) : Prop :=
  leaf_verify msg sig.leaf_sig sig.leaf_pk ∧
  (if sig.idx then H sig.sibling sig.leaf_pk
              else H sig.leaf_pk sig.sibling) = root

-- ============================================================
-- 3.  MAIN THEOREM
-- ============================================================

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

-- ============================================================
-- 4.  LEAF VERIFICATION + "COMPOSITIONAL" APPROACH
-- ============================================================

/--
  Abstract leaf predicate: the message matches the leaf key.
  Kept as a black-box Prop - the binding theorem makes no assumption
  about its internals beyond that it holds for valid signatures.
-/
def leaf_ver (msg _ lpk : HashVal) : Prop := msg = lpk

/--
  "Compositional" approach: tree binding + leaf verification together.
  Structural guarantee: the signature commits to exactly one leaf.
  Leaf guarantee: the message equals the committed leaf key.
 
-/
theorem compositional
    (pk0 pk1 msg : HashVal)
    (sig : Sig)
    (hv : verify leaf_ver (tree_root pk0 pk1) msg sig) :
    ((sig.idx = false ∧ sig.leaf_pk = pk0) ∨
     (sig.idx = true  ∧ sig.leaf_pk = pk1)) ∧
    msg = sig.leaf_pk := by
  obtain ⟨h_leaf, h_tree⟩ := hv
  exact ⟨leaf_binding leaf_ver pk0 pk1 msg sig ⟨h_leaf, h_tree⟩, h_leaf⟩

-- ============================================================
-- 5.  INSTANTIATION OVER BitVec 256
-- ============================================================

-- leaf keys as 256-bit vectors
def pk0 : HashVal := 0x0000000000000000000000000000000000000000000000000000000000000042
def pk1 : HashVal := 0x0000000000000000000000000000000000000000000000000000000000000063

-- #eval the keys to confirm they are well-formed 256-bit values
#eval pk0.toHex   -- "0000000000000000000000000000000000000000000000000000000000000042"
#eval pk1.toHex   -- "0000000000000000000000000000000000000000000000000000000000000063"
#eval (pk0 == pk1)  -- false (keys are distinct)

-- Valid signatures: leaf_sig = leaf_pk so leaf_ver holds definitionally
def sig0 : Sig := ⟨false, pk0, 0, pk1⟩
def sig1 : Sig := ⟨true,  pk1, 0, pk0⟩

-- Forged signature: wrong leaf_pk
def sig_bad : Sig := ⟨false, 0xFF, 0xFF, pk1⟩

-- Inspect signature fields
#eval sig0.idx             -- false
#eval sig1.idx             -- true
#eval sig0.leaf_pk.toHex   -- ...0042  (= pk0)
#eval sig1.leaf_pk.toHex   -- ...0063  (= pk1)
#eval sig0.sibling.toHex   -- ...0063  (= pk1, the sibling)
#eval sig1.sibling.toHex   -- ...0042  (= pk0, the sibling)
#eval (0xFF : HashVal).toHex  -- ...00ff  ≠ pk0 or pk1

-- ============================================================
-- 6.  PROOF CHAIN
-- ============================================================

-- leaf_ver holds definitionally for sig0 and sig1
-- because leaf_sig = leaf_pk = the key itself
-- The tree equation holds by simp unfolding the struct fields


theorem sig0_ok : verify leaf_ver (tree_root pk0 pk1) pk0 sig0 :=
  ⟨rfl, by simp [tree_root, sig0]⟩

theorem sig1_ok : verify leaf_ver (tree_root pk0 pk1) pk1 sig1 :=
  ⟨rfl, by simp [tree_root, sig1]⟩

-- Forged signature is rejected by H_inj: accepting it would require
-- H_inj to conclude 0xFF = pk0, which simp refutes on BitVec 256.
theorem sig_bad_rejected : ¬ verify leaf_ver (tree_root pk0 pk1) pk0 sig_bad := by
  intro ⟨_, h_tree⟩
  simp only [sig_bad] at h_tree
  have heq := (H_inj sig_bad.leaf_pk sig_bad.sibling pk0 pk1 h_tree).left
  simp [sig_bad, pk0] at heq

-- Binding theorem applied to proved hypotheses
theorem sig0_binds :
    (sig0.idx = false ∧ sig0.leaf_pk = pk0) ∨
    (sig0.idx = true  ∧ sig0.leaf_pk = pk1) :=
  leaf_binding leaf_ver pk0 pk1 pk0 sig0 sig0_ok

theorem sig1_binds :
    (sig1.idx = false ∧ sig1.leaf_pk = pk0) ∨
    (sig1.idx = true  ∧ sig1.leaf_pk = pk1) :=
  leaf_binding leaf_ver pk0 pk1 pk1 sig1 sig1_ok
  
theorem sig0_full :
  ((sig0.idx = false ∧ sig0.leaf_pk = pk0) ∨
   (sig0.idx = true ∧ sig0.leaf_pk = pk1)) ∧
  pk0 = sig0.leaf_pk :=
  compositional pk0 pk1 pk0 sig0 sig0_ok
  
theorem sig1_full :
  ((sig1.idx = false ∧ sig1.leaf_pk = pk0) ∨
   (sig1.idx = true  ∧ sig1.leaf_pk = pk1)) ∧
  pk1 = sig1.leaf_pk :=
  compositional pk0 pk1 pk1 sig1 sig1_ok
