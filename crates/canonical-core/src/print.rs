use crate::core::*;
use std::fmt;
use crate::memory::S;

impl WHNF {
    /// A weak head normal form term needs parentheses if there are arguments.
    fn needs_parens(&self) -> bool {
        match &self.0.base.borrow().assignment {
            Some(assignment) => assignment.args.len() > 0,
            None => false,
        }
    }
}

impl<T> Indexed<T> {
    /// A lambda requires parentheses if there are parameters or lets.
    fn needs_parens(&self) -> bool {
        self.params.len() > 0 || self.lets.len() > 0
    }
}


impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut owned_linked = Vec::new();
        // prints the reduced form. 
        let whnf = self.whnf::<true, ()>(&mut owned_linked, &mut ());
        let needs_parens = self.base.borrow().bindings.borrow().needs_parens() || whnf.needs_parens();
        if needs_parens { write!(f, "(")? }
        self.base.borrow().bindings.borrow().fmt(f)?;
        whnf.fmt(f)?;
        if needs_parens { write!(f, ")")? }
        Ok(())
    }
}

impl fmt::Display for WHNF {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.0.base.borrow().assignment {
            Some(assignment) => {
                if let Head::Var(var) = &self.1 {
                    write!(f, "{}", var.bind.borrow().name)?;
                } else {
                    write!(f, "...")?;
                }
                for arg in assignment.args.iter() {
                    let bindings = arg.borrow().bindings.clone();
                    write!(f, " {}", Term { base: arg.downgrade(), es: 
                        self.0.es.append(Node { entry: Entry::vars(next_u64()), bindings }, &mut Vec::new()) })?;
                }
                Ok(())
            }
            None => { 
                if let Some(typ) = &self.0.base.borrow().typ {
                    write!(f, "?{}", typ.2.borrow().name.clone())
                } else {
                    write!(f, "?")
                }
            }
        }   
    }
}

impl fmt::Display for Indexed<S<Bind>> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.needs_parens() { write!(f, "λ")? }
        for param in &self.params {
            write!(f, " {}", param.borrow().name)?;
        }
        for let_ in &self.lets {
            write!(f, ", {} := _", let_.borrow().name)?;
        }
        if self.needs_parens() { write!(f, " ↦ ")? }
        Ok(())
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let codomain = self.codomain();
        let mut owned_linked = Vec::new();
        let whnf = codomain.whnf::<true, ()>(&mut owned_linked, &mut ());
        let needs_parens = codomain.base.borrow().bindings.borrow().needs_parens() || whnf.needs_parens();
        if needs_parens { write!(f, "(")? }
        codomain.base.borrow().bindings.borrow().fmt(f)?;
        whnf.fmt(f)?;
        if needs_parens { write!(f, ")")? }
        Ok(())
    }
}

impl fmt::Debug for Rule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for symbol in self.pattern.iter() {
            if let Some(symbol) = symbol {
                write!(f, "{} ", symbol.bind.borrow().name)?;
            } else {
                write!(f, "* ")?;
            }
        }
        Ok(())
    }
}