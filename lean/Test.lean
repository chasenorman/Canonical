import Qq
import Canonical
import Lean

open Qq Lean Meta

def test : MetaM Unit := do
  let goal : Expr := q(Nat → Nat → Nat)
  let typ ← Canonical.withArityUnfold true do
    Canonical.toCanonical goal #[] #[] {}

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

  let result ← Canonical.runCanonical decl 3 {}

  match result.terms[0]? with
  | some t => dbg_trace t.spine
  | none => dbg_trace "no term found"


#eval do test
