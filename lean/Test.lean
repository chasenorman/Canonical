import Qq
import Canonical
import Lean

open Qq Lean Meta

#check Canonical.toRule

def test : MetaM Unit := do
  let goal : Expr := q(Nat → Nat → Nat)
  let typ ← Canonical.withArityUnfold true do
    Canonical.toCanonical goal #[] #[] {}

  dbg_trace typ

  let zero := { head := "Nat.zero" }
  let one := { head := "Nat.succ", args := #[ { spine := zero } ] }
  let two := { head := "Nat.succ", args := #[ { spine := one } ] }

  let name := "f"
  let decl := { type := typ, name, equations := #[{
    lhs := { head := "f", args := #[{ spine := zero }, { spine := one }] },
    rhs := one
  }, {
    lhs := { head := "f", args := #[{ spine := one }, { spine := zero }] },
    rhs := one
  }, {
    lhs := { head := "f", args := #[{ spine := zero }, { spine := zero }] },
    rhs := zero
  }, {
    lhs := { head := "f", args := #[{ spine := one }, { spine := one }] },
    rhs := two
  }] }

  let _ ← Canonical.save_problem decl "debug.json"

  let result ← Canonical.runCanonical decl 3 {}

  dbg_trace result.terms


#eval do test
