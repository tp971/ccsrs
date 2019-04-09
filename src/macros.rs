#[macro_export]
macro_rules! ccs_act {
    ($($ts:tt)*) => {{
        use $crate::*;
        use $crate::ccs::*;
        ccs_parse_act!($($ts)*)
    }};
}

#[doc(hidden)]
#[macro_export]
macro_rules! ccs_parse_act {
    (i) => {
        Action::Tau
    };
    (e) => {
        Action::Delta
    };
    ($name:ident) => {{
        let name = stringify!($name);
        Action::Act(name.to_string())
    }};
    ($name:ident !) => {{
        let name = stringify!($name);
        Action::Snd(name.to_string(), None, None)
    }};
    ($name:ident ! ($($exp:tt)*)) => {{
        let name = stringify!($name);
        let exp = ccs_exp!($($exp)*);
        Action::Snd(name.to_string(), None, Some(exp))
    }};
    ($name:ident ($($param:tt)*) !) => {{
        let name = stringify!($name);
        let param = ccs_exp!($($param)*);
        Action::Snd(name.to_string(), Some(param), None)
    }};
    ($name:ident ($($param:tt)*) ! ($($exp:tt)*)) => {{
        let name = stringify!($name);
        let param = ccs_exp!($($param)*);
        let exp = ccs_exp!($($exp)*);
        Action::Snd(name.to_string(), Some(param), Some(exp))
    }};
    ($name:ident ?) => {{
        let name = stringify!($name);
        Action::Recv(name.to_string(), None, None)
    }};
    ($name:ident ? ($($exp:tt)*)) => {{
        let name = stringify!($name);
        let exp = ccs_exp!($($exp)*);
        Action::Recv(name.to_string(), None, Some(exp))
    }};
    ($name:ident ($($param:tt)*) ?) => {{
        let name = stringify!($name);
        let param = ccs_exp!($($param)*);
        Action::Recv(name.to_string(), Some(param), None)
    }};
    ($name:ident ($($param:tt)*) ? ($($exp:tt)*)) => {{
        let name = stringify!($name);
        let param = ccs_exp!($($param)*);
        let exp = ccs_exp!($($exp)*);
        Action::Recv(name.to_string(), Some(param), Some(exp))
    }};
    ($name:ident ? $id:ident) => {{
        let name = stringify!($name);
        let id = stringify!($id);
        Action::RecvInto(name.to_string(), None, id.to_string())
    }};
    ($name:ident ($($param:tt)*) ? $id:ident) => {{
        let name = stringify!($name);
        let param = ccs_exp!($($param)*);
        let id = stringify!($id);
        Action::RecvInto(name.to_string(), Some(param), id.to_string())
    }};
}



#[macro_export]
macro_rules! ccs {
    ($($ts:tt)*) => {{
        use $crate::*;
        #[allow(unused_imports)]
        use std::collections::BTreeSet;
        #[allow(unused_imports)]
        use std::sync::Arc;
        ccs_parse_operand!([$($ts)*] [] [])
    }};
}

#[doc(hidden)]
#[macro_export]
macro_rules! ccs_parse_operand {
    ([when $cond:tt $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*]) => {{
        let cond = ccs_exp!{ $cond };
        ccs_parse_operand!([$($ts)*] [(cond) $($output)*] [when $($ops)*])
    }};
    ([i . $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*]) => {{
        ccs_parse_operand!([$($ts)*] [(Action::Tau) $($output)*] [. $($ops)*])
    }};
    ([e . $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*]) => {{
        ccs_parse_operand!([$($ts)*] [(Action::Delta) $($output)*] [. $($ops)*])
    }};
    ([$name:ident . $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*]) => {{
        let name = stringify!($name);
        ccs_parse_operand!([$($ts)*] [(Action::Act(name.to_string())) $($output)*] [. $($ops)*])
    }};
    ([$name:ident ! . $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*]) => {{
        let name = stringify!($name);
        ccs_parse_operand!([$($ts)*] [(Action::Snd(name.to_string(), None, None)) $($output)*] [. $($ops)*])
    }};
    ([$name:ident ! ($($exp:tt)*) . $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*]) => {{
        let name = stringify!($name);
        let exp = ccs_exp!($($exp)*);
        ccs_parse_operand!([$($ts)*] [(Action::Snd(name.to_string(), None, Some(exp))) $($output)*] [. $($ops)*])
    }};
    ([$name:ident ($($param:tt)*) ! . $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*]) => {{
        let name = stringify!($name);
        let param = ccs_exp!($($param)*);
        ccs_parse_operand!([$($ts)*] [(Action::Snd(name.to_string(), Some(param), None)) $($output)*] [. $($ops)*])
    }};
    ([$name:ident ($($param:tt)*) ! ($($exp:tt)*) . $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*]) => {{
        let name = stringify!($name);
        let param = ccs_exp!($($param)*);
        let exp = ccs_exp!($($exp)*);
        ccs_parse_operand!([$($ts)*] [(Action::Snd(name.to_string(), Some(param), Some(exp))) $($output)*] [. $($ops)*])
    }};
    ([$name:ident ? . $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*]) => {{
        let name = stringify!($name);
        ccs_parse_operand!([$($ts)*] [(Action::Recv(name.to_string(), None, None)) $($output)*] [. $($ops)*])
    }};
    ([$name:ident ? ($($exp:tt)*) . $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*]) => {{
        let name = stringify!($name);
        let exp = ccs_exp!($($exp)*);
        ccs_parse_operand!([$($ts)*] [(Action::Recv(name.to_string(), None, Some(exp))) $($output)*] [. $($ops)*])
    }};
    ([$name:ident ($($param:tt)*) ? . $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*]) => {{
        let name = stringify!($name);
        let param = ccs_exp!($($param)*);
        ccs_parse_operand!([$($ts)*] [(Action::Recv(name.to_string(), Some(param), None)) $($output)*] [. $($ops)*])
    }};
    ([$name:ident ($($param:tt)*) ? ($($exp:tt)*) . $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*]) => {{
        let name = stringify!($name);
        let param = ccs_exp!($($param)*);
        let exp = ccs_exp!($($exp)*);
        ccs_parse_operand!([$($ts)*] [(Action::Recv(name.to_string(), Some(param), Some(exp))) $($output)*] [. $($ops)*])
    }};
    ([$name:ident ? $id:ident . $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*]) => {{
        let name = stringify!($name);
        let id = stringify!($id);
        ccs_parse_operand!([$($ts)*] [(Action::RecvInto(name.to_string(), None, id.to_string())) $($output)*] [. $($ops)*])
    }};
    ([$name:ident ($($param:tt)*) ? $id:ident . $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*]) => {{
        let name = stringify!($name);
        let param = ccs_exp!($($param)*);
        let id = stringify!($id);
        ccs_parse_operand!([$($ts)*] [(Action::RecvInto(name.to_string(), Some(param), id.to_string())) $($output)*] [. $($ops)*])
    }};
    ([@$var:tt . $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*]) => {
        ccs_parse_operand!([$($ts)*] [($var) $($output)*] [. $($ops)*])
    };
    ([0 $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*]) => {{
        ccs_apply_unary!([$($ts)*] [(Process::Null) $($output)*] [$($ops)*])
    }};
    ([1 $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*]) => {{
        ccs_apply_unary!([$($ts)*] [(Process::Term) $($output)*] [$($ops)*])
    }};
    ([$name:ident [$($args:tt),*] $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*]) => {{
        let name = stringify!($name);
        let mut args = Vec::new();
        $( args.push(ccs_exp!{ $args }); )*
        ccs_apply_unary!([$($ts)*] [(Process::Name(name.to_string(), args)) $($output)*] [$($ops)*])
    }};
    ([$name:ident $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*]) => {{
        let name = stringify!($name);
        ccs_apply_unary!([$($ts)*] [(Process::Name(name.to_string(), vec![])) $($output)*] [$($ops)*])
    }};
    ([@$var:tt $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*]) => {
        ccs_apply_unary!([$($ts)*] [($var) $($output)*] [$($ops)*])
    };
    ([($($t:tt)*) $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*]) => {{
        let exp = ccs!($($t)*);
        ccs_apply_unary!([$($ts)*] [(exp) $($output)*] [$($ops)*])
    }};
}

#[doc(hidden)]
#[macro_export]
macro_rules! ccs_apply_unary {
    ([$($ts:tt)*] [($process:expr) ($cond:expr) $($output:tt)*] [when $($ops:tt)*]) => {{
        ccs_apply_unary!([$($ts)*] [(Process::When($cond, Arc::new($process))) $($output)*] [$($ops)*])
    }};
    ([$($ts:tt)*] [($process:expr) ($action:expr) $($output:tt)*] [. $($ops:tt)*]) => {{
        ccs_apply_unary!([$($ts)*] [(Process::Prefix($action, Arc::new($process))) $($output)*] [$($ops)*])
    }};
    ([/ { * } $($ts:tt)*] [($process:expr) $($output:tt)*] [$($ops:tt)*]) => {{
        ccs_apply_unary!([$($ts)*] [(Process::Restrict(Arc::new($process), true, BTreeSet::new())) $($output)*] [$($ops)*])
    }};
    ([/ { *, $($acts:ident),* } $($ts:tt)*] [($process:expr) $($output:tt)*] [$($ops:tt)*]) => {{
        let mut set = BTreeSet::new();
        $( set.insert(stringify!($acts).to_string()); )*
        ccs_apply_unary!([$($ts)*] [(Process::Restrict(Arc::new($process), true, set)) $($output)*] [$($ops)*])
    }};
    ([/ { $($acts:ident),* } $($ts:tt)*] [($process:expr) $($output:tt)*] [$($ops:tt)*]) => {{
        let mut set = BTreeSet::new();
        $( set.insert(stringify!($acts).to_string()); )*
        ccs_apply_unary!([$($ts)*] [(Process::Restrict(Arc::new($process), false, set)) $($output)*] [$($ops)*])
    }};
    ([$($ts:tt)*] [$($output:tt)*] [$($ops:tt)*]) => {
        ccs_parse_operator!([$($ts)*] [$($output)*] [$($ops)*])
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! ccs_parse_operator {
    ([+ $($ts:tt)*] [$($output:tt)*] [+ $($ops:tt)*]) => { ccs_apply_binary! ([+ $($ts)*] [$($output)*] [+ $($ops)*]) };
    ([+ $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*])   => { ccs_parse_operand!([$($ts)*] [$($output)*] [+ $($ops)*]) };

    ([| $($ts:tt)*] [$($output:tt)*] [+ $($ops:tt)*]) => { ccs_apply_binary! ([| $($ts)*] [$($output)*] [+ $($ops)*]) };
    ([| $($ts:tt)*] [$($output:tt)*] [| $($ops:tt)*]) => { ccs_apply_binary! ([| $($ts)*] [$($output)*] [| $($ops)*]) };
    ([| $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*])   => { ccs_parse_operand!([$($ts)*] [$($output)*] [| $($ops)*]) };

    ([; $($ts:tt)*] [$($output:tt)*] [+ $($ops:tt)*]) => { ccs_apply_binary! ([; $($ts)*] [$($output)*] [+ $($ops)*]) };
    ([; $($ts:tt)*] [$($output:tt)*] [| $($ops:tt)*]) => { ccs_apply_binary! ([; $($ts)*] [$($output)*] [| $($ops)*]) };
    ([; $($ts:tt)*] [$($output:tt)*] [; $($ops:tt)*]) => { ccs_apply_binary! ([; $($ts)*] [$($output)*] [; $($ops)*]) };
    ([; $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*])   => { ccs_parse_operand!([$($ts)*] [$($output)*] [; $($ops)*]) };

    ([]             [($output:expr)] [])              => { $output };
    ([]             [$($output:tt)*] [$($ops:tt)*])   => { ccs_apply_binary! ([]        [$($output)*] [$($ops)*]) };
}

#[doc(hidden)]
#[macro_export]
macro_rules! ccs_apply_binary {
    ([$($ts:tt)*] [($b:expr) ($a:expr) $($output:tt)*] [+ $($ops:tt)*]) => {{
        ccs_parse_operator!([$($ts)*] [(Process::Choice(Arc::new($a), Arc::new($b))) $($output)*] [$($ops)*])
    }};
    ([$($ts:tt)*] [($b:expr) ($a:expr) $($output:tt)*] [| $($ops:tt)*]) => {{
        ccs_parse_operator!([$($ts)*] [(Process::Parallel(Arc::new($a), Arc::new($b))) $($output)*] [$($ops)*])
    }};
    ([$($ts:tt)*] [($b:expr) ($a:expr) $($output:tt)*] [; $($ops:tt)*]) => {{
        ccs_parse_operator!([$($ts)*] [(Process::Sequential(Arc::new($a), Arc::new($b))) $($output)*] [$($ops)*])
    }};
}



#[macro_export]
macro_rules! ccs_exp {
    ($($ts:tt)*) => {{
        use $crate::*;
        #[allow(unused_imports)]
        use std::collections::BTreeSet;
        #[allow(unused_imports)]
        use std::sync::Arc;
        ccs_exp_parse_operand!([$($ts)*] [] [])
    }};
}

#[doc(hidden)]
#[macro_export]
macro_rules! ccs_exp_parse_operand {
    ([+ $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*]) => {{
        ccs_exp_parse_operand!([$($ts)*] [$($output)*] [.+ $($ops)*])
    }};
    ([- $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*]) => {{
        ccs_exp_parse_operand!([$($ts)*] [$($output)*] [.- $($ops)*])
    }};
    ([! $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*]) => {{
        ccs_exp_parse_operand!([$($ts)*] [$($output)*] [.! $($ops)*])
    }};
    ([:$const:tt $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*]) => {{
        ccs_exp_apply_unary!([$($ts)*] [(Exp::from($const)) $($output)*] [$($ops)*])
    }};
    ([$name:ident $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*]) => {{
        let name = stringify!($name);
        ccs_exp_apply_unary!([$($ts)*] [(Exp::IdExp(name.to_string())) $($output)*] [$($ops)*])
    }};
    ([@$var:tt $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*]) => {
        ccs_exp_apply_unary!([$($ts)*] [($var) $($output)*] [$($ops)*])
    };
    ([($($t:tt)*) $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*]) => {{
        let exp = ccs_exp!($($t)*);
        ccs_exp_apply_unary!([$($ts)*] [(exp) $($output)*] [$($ops)*])
    }};
}

#[doc(hidden)]
#[macro_export]
macro_rules! ccs_exp_apply_unary {
    ([$($ts:tt)*] [($exp:expr) $($output:tt)*] [.+ $($ops:tt)*]) => {{
        ccs_exp_apply_unary!([$($ts)*] [(Exp::Unary(UnaryOp::Plus, Arc::new($exp))) $($output)*] [$($ops)*])
    }};
    ([$($ts:tt)*] [($exp:expr) $($output:tt)*] [.- $($ops:tt)*]) => {{
        ccs_exp_apply_unary!([$($ts)*] [(Exp::Unary(UnaryOp::Minus, Arc::new($exp))) $($output)*] [$($ops)*])
    }};
    ([$($ts:tt)*] [($exp:expr) $($output:tt)*] [.! $($ops:tt)*]) => {{
        ccs_exp_apply_unary!([$($ts)*] [(Exp::Unary(UnaryOp::Not, Arc::new($exp))) $($output)*] [$($ops)*])
    }};
    ([$($ts:tt)*] [$($output:tt)*] [$($ops:tt)*]) => {
        ccs_exp_parse_operator!([$($ts)*] [$($output)*] [$($ops)*])
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! ccs_exp_parse_operator {
    ([* $($ts:tt)*] [$($output:tt)*] [* $($ops:tt)*]) => { ccs_exp_apply_binary! ([* $($ts)*] [$($output)*] [* $($ops)*]) };
    ([* $($ts:tt)*] [$($output:tt)*] [/ $($ops:tt)*]) => { ccs_exp_apply_binary! ([* $($ts)*] [$($output)*] [/ $($ops)*]) };
    ([* $($ts:tt)*] [$($output:tt)*] [% $($ops:tt)*]) => { ccs_exp_apply_binary! ([* $($ts)*] [$($output)*] [% $($ops)*]) };
    ([* $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*])   => { ccs_exp_parse_operand!([$($ts)*] [$($output)*] [* $($ops)*]) };

    ([/ $($ts:tt)*] [$($output:tt)*] [* $($ops:tt)*]) => { ccs_exp_apply_binary! ([/ $($ts)*] [$($output)*] [* $($ops)*]) };
    ([/ $($ts:tt)*] [$($output:tt)*] [/ $($ops:tt)*]) => { ccs_exp_apply_binary! ([/ $($ts)*] [$($output)*] [/ $($ops)*]) };
    ([/ $($ts:tt)*] [$($output:tt)*] [% $($ops:tt)*]) => { ccs_exp_apply_binary! ([/ $($ts)*] [$($output)*] [% $($ops)*]) };
    ([/ $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*])   => { ccs_exp_parse_operand!([$($ts)*] [$($output)*] [/ $($ops)*]) };

    ([% $($ts:tt)*] [$($output:tt)*] [* $($ops:tt)*]) => { ccs_exp_apply_binary! ([% $($ts)*] [$($output)*] [* $($ops)*]) };
    ([% $($ts:tt)*] [$($output:tt)*] [/ $($ops:tt)*]) => { ccs_exp_apply_binary! ([% $($ts)*] [$($output)*] [/ $($ops)*]) };
    ([% $($ts:tt)*] [$($output:tt)*] [% $($ops:tt)*]) => { ccs_exp_apply_binary! ([% $($ts)*] [$($output)*] [% $($ops)*]) };
    ([% $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*])   => { ccs_exp_parse_operand!([$($ts)*] [$($output)*] [% $($ops)*]) };

    ([+ $($ts:tt)*] [$($output:tt)*] [* $($ops:tt)*]) => { ccs_exp_apply_binary! ([+ $($ts)*] [$($output)*] [* $($ops)*]) };
    ([+ $($ts:tt)*] [$($output:tt)*] [/ $($ops:tt)*]) => { ccs_exp_apply_binary! ([+ $($ts)*] [$($output)*] [/ $($ops)*]) };
    ([+ $($ts:tt)*] [$($output:tt)*] [% $($ops:tt)*]) => { ccs_exp_apply_binary! ([+ $($ts)*] [$($output)*] [% $($ops)*]) };
    ([+ $($ts:tt)*] [$($output:tt)*] [+ $($ops:tt)*]) => { ccs_exp_apply_binary! ([+ $($ts)*] [$($output)*] [+ $($ops)*]) };
    ([+ $($ts:tt)*] [$($output:tt)*] [- $($ops:tt)*]) => { ccs_exp_apply_binary! ([+ $($ts)*] [$($output)*] [- $($ops)*]) };
    ([+ $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*])   => { ccs_exp_parse_operand!([$($ts)*] [$($output)*] [+ $($ops)*]) };

    ([- $($ts:tt)*] [$($output:tt)*] [* $($ops:tt)*]) => { ccs_exp_apply_binary! ([- $($ts)*] [$($output)*] [* $($ops)*]) };
    ([- $($ts:tt)*] [$($output:tt)*] [/ $($ops:tt)*]) => { ccs_exp_apply_binary! ([- $($ts)*] [$($output)*] [/ $($ops)*]) };
    ([- $($ts:tt)*] [$($output:tt)*] [% $($ops:tt)*]) => { ccs_exp_apply_binary! ([- $($ts)*] [$($output)*] [% $($ops)*]) };
    ([- $($ts:tt)*] [$($output:tt)*] [+ $($ops:tt)*]) => { ccs_exp_apply_binary! ([- $($ts)*] [$($output)*] [+ $($ops)*]) };
    ([- $($ts:tt)*] [$($output:tt)*] [- $($ops:tt)*]) => { ccs_exp_apply_binary! ([- $($ts)*] [$($output)*] [- $($ops)*]) };
    ([- $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*])   => { ccs_exp_parse_operand!([$($ts)*] [$($output)*] [- $($ops)*]) };

    ([^ $($ts:tt)*] [$($output:tt)*] [* $($ops:tt)*]) => { ccs_exp_apply_binary! ([^ $($ts)*] [$($output)*] [* $($ops)*]) };
    ([^ $($ts:tt)*] [$($output:tt)*] [/ $($ops:tt)*]) => { ccs_exp_apply_binary! ([^ $($ts)*] [$($output)*] [/ $($ops)*]) };
    ([^ $($ts:tt)*] [$($output:tt)*] [% $($ops:tt)*]) => { ccs_exp_apply_binary! ([^ $($ts)*] [$($output)*] [% $($ops)*]) };
    ([^ $($ts:tt)*] [$($output:tt)*] [+ $($ops:tt)*]) => { ccs_exp_apply_binary! ([^ $($ts)*] [$($output)*] [+ $($ops)*]) };
    ([^ $($ts:tt)*] [$($output:tt)*] [- $($ops:tt)*]) => { ccs_exp_apply_binary! ([^ $($ts)*] [$($output)*] [- $($ops)*]) };
    ([^ $($ts:tt)*] [$($output:tt)*] [^ $($ops:tt)*]) => { ccs_exp_apply_binary! ([^ $($ts)*] [$($output)*] [^ $($ops)*]) };
    ([^ $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*])   => { ccs_exp_parse_operand!([$($ts)*] [$($output)*] [^ $($ops)*]) };

    ([< $($ts:tt)*] [$($output:tt)*] [* $($ops:tt)*]) => { ccs_exp_apply_binary! ([< $($ts)*] [$($output)*] [* $($ops)*]) };
    ([< $($ts:tt)*] [$($output:tt)*] [/ $($ops:tt)*]) => { ccs_exp_apply_binary! ([< $($ts)*] [$($output)*] [/ $($ops)*]) };
    ([< $($ts:tt)*] [$($output:tt)*] [% $($ops:tt)*]) => { ccs_exp_apply_binary! ([< $($ts)*] [$($output)*] [% $($ops)*]) };
    ([< $($ts:tt)*] [$($output:tt)*] [+ $($ops:tt)*]) => { ccs_exp_apply_binary! ([< $($ts)*] [$($output)*] [+ $($ops)*]) };
    ([< $($ts:tt)*] [$($output:tt)*] [- $($ops:tt)*]) => { ccs_exp_apply_binary! ([< $($ts)*] [$($output)*] [- $($ops)*]) };
    ([< $($ts:tt)*] [$($output:tt)*] [^ $($ops:tt)*]) => { ccs_exp_apply_binary! ([< $($ts)*] [$($output)*] [^ $($ops)*]) };
    ([< $($ts:tt)*] [$($output:tt)*] [< $($ops:tt)*]) => { ccs_exp_apply_binary! ([< $($ts)*] [$($output)*] [< $($ops)*]) };
    ([< $($ts:tt)*] [$($output:tt)*] [<= $($ops:tt)*]) => { ccs_exp_apply_binary! ([< $($ts)*] [$($output)*] [<= $($ops)*]) };
    ([< $($ts:tt)*] [$($output:tt)*] [> $($ops:tt)*]) => { ccs_exp_apply_binary! ([< $($ts)*] [$($output)*] [> $($ops)*]) };
    ([< $($ts:tt)*] [$($output:tt)*] [>= $($ops:tt)*]) => { ccs_exp_apply_binary! ([< $($ts)*] [$($output)*] [>= $($ops)*]) };
    ([< $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*])   => { ccs_exp_parse_operand!([$($ts)*] [$($output)*] [< $($ops)*]) };

    ([<= $($ts:tt)*] [$($output:tt)*] [* $($ops:tt)*]) => { ccs_exp_apply_binary! ([<= $($ts)*] [$($output)*] [* $($ops)*]) };
    ([<= $($ts:tt)*] [$($output:tt)*] [/ $($ops:tt)*]) => { ccs_exp_apply_binary! ([<= $($ts)*] [$($output)*] [/ $($ops)*]) };
    ([<= $($ts:tt)*] [$($output:tt)*] [% $($ops:tt)*]) => { ccs_exp_apply_binary! ([<= $($ts)*] [$($output)*] [% $($ops)*]) };
    ([<= $($ts:tt)*] [$($output:tt)*] [+ $($ops:tt)*]) => { ccs_exp_apply_binary! ([<= $($ts)*] [$($output)*] [+ $($ops)*]) };
    ([<= $($ts:tt)*] [$($output:tt)*] [- $($ops:tt)*]) => { ccs_exp_apply_binary! ([<= $($ts)*] [$($output)*] [- $($ops)*]) };
    ([<= $($ts:tt)*] [$($output:tt)*] [^ $($ops:tt)*]) => { ccs_exp_apply_binary! ([<= $($ts)*] [$($output)*] [^ $($ops)*]) };
    ([<= $($ts:tt)*] [$($output:tt)*] [< $($ops:tt)*]) => { ccs_exp_apply_binary! ([<= $($ts)*] [$($output)*] [< $($ops)*]) };
    ([<= $($ts:tt)*] [$($output:tt)*] [<= $($ops:tt)*]) => { ccs_exp_apply_binary! ([<= $($ts)*] [$($output)*] [<= $($ops)*]) };
    ([<= $($ts:tt)*] [$($output:tt)*] [> $($ops:tt)*]) => { ccs_exp_apply_binary! ([<= $($ts)*] [$($output)*] [> $($ops)*]) };
    ([<= $($ts:tt)*] [$($output:tt)*] [>= $($ops:tt)*]) => { ccs_exp_apply_binary! ([<= $($ts)*] [$($output)*] [>= $($ops)*]) };
    ([<= $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*])   => { ccs_exp_parse_operand!([$($ts)*] [$($output)*] [<= $($ops)*]) };

    ([> $($ts:tt)*] [$($output:tt)*] [* $($ops:tt)*]) => { ccs_exp_apply_binary! ([> $($ts)*] [$($output)*] [* $($ops)*]) };
    ([> $($ts:tt)*] [$($output:tt)*] [/ $($ops:tt)*]) => { ccs_exp_apply_binary! ([> $($ts)*] [$($output)*] [/ $($ops)*]) };
    ([> $($ts:tt)*] [$($output:tt)*] [% $($ops:tt)*]) => { ccs_exp_apply_binary! ([> $($ts)*] [$($output)*] [% $($ops)*]) };
    ([> $($ts:tt)*] [$($output:tt)*] [+ $($ops:tt)*]) => { ccs_exp_apply_binary! ([> $($ts)*] [$($output)*] [+ $($ops)*]) };
    ([> $($ts:tt)*] [$($output:tt)*] [- $($ops:tt)*]) => { ccs_exp_apply_binary! ([> $($ts)*] [$($output)*] [- $($ops)*]) };
    ([> $($ts:tt)*] [$($output:tt)*] [^ $($ops:tt)*]) => { ccs_exp_apply_binary! ([> $($ts)*] [$($output)*] [^ $($ops)*]) };
    ([> $($ts:tt)*] [$($output:tt)*] [< $($ops:tt)*]) => { ccs_exp_apply_binary! ([> $($ts)*] [$($output)*] [< $($ops)*]) };
    ([> $($ts:tt)*] [$($output:tt)*] [<= $($ops:tt)*]) => { ccs_exp_apply_binary! ([> $($ts)*] [$($output)*] [<= $($ops)*]) };
    ([> $($ts:tt)*] [$($output:tt)*] [> $($ops:tt)*]) => { ccs_exp_apply_binary! ([> $($ts)*] [$($output)*] [> $($ops)*]) };
    ([> $($ts:tt)*] [$($output:tt)*] [>= $($ops:tt)*]) => { ccs_exp_apply_binary! ([> $($ts)*] [$($output)*] [>= $($ops)*]) };
    ([> $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*])   => { ccs_exp_parse_operand!([$($ts)*] [$($output)*] [> $($ops)*]) };

    ([>= $($ts:tt)*] [$($output:tt)*] [* $($ops:tt)*]) => { ccs_exp_apply_binary! ([>= $($ts)*] [$($output)*] [* $($ops)*]) };
    ([>= $($ts:tt)*] [$($output:tt)*] [/ $($ops:tt)*]) => { ccs_exp_apply_binary! ([>= $($ts)*] [$($output)*] [/ $($ops)*]) };
    ([>= $($ts:tt)*] [$($output:tt)*] [% $($ops:tt)*]) => { ccs_exp_apply_binary! ([>= $($ts)*] [$($output)*] [% $($ops)*]) };
    ([>= $($ts:tt)*] [$($output:tt)*] [+ $($ops:tt)*]) => { ccs_exp_apply_binary! ([>= $($ts)*] [$($output)*] [+ $($ops)*]) };
    ([>= $($ts:tt)*] [$($output:tt)*] [- $($ops:tt)*]) => { ccs_exp_apply_binary! ([>= $($ts)*] [$($output)*] [- $($ops)*]) };
    ([>= $($ts:tt)*] [$($output:tt)*] [^ $($ops:tt)*]) => { ccs_exp_apply_binary! ([>= $($ts)*] [$($output)*] [^ $($ops)*]) };
    ([>= $($ts:tt)*] [$($output:tt)*] [< $($ops:tt)*]) => { ccs_exp_apply_binary! ([>= $($ts)*] [$($output)*] [< $($ops)*]) };
    ([>= $($ts:tt)*] [$($output:tt)*] [<= $($ops:tt)*]) => { ccs_exp_apply_binary! ([>= $($ts)*] [$($output)*] [<= $($ops)*]) };
    ([>= $($ts:tt)*] [$($output:tt)*] [> $($ops:tt)*]) => { ccs_exp_apply_binary! ([>= $($ts)*] [$($output)*] [> $($ops)*]) };
    ([>= $($ts:tt)*] [$($output:tt)*] [>= $($ops:tt)*]) => { ccs_exp_apply_binary! ([>= $($ts)*] [$($output)*] [>= $($ops)*]) };
    ([>= $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*])   => { ccs_exp_parse_operand!([$($ts)*] [$($output)*] [>= $($ops)*]) };

    ([== $($ts:tt)*] [$($output:tt)*] [* $($ops:tt)*]) => { ccs_exp_apply_binary! ([== $($ts)*] [$($output)*] [* $($ops)*]) };
    ([== $($ts:tt)*] [$($output:tt)*] [/ $($ops:tt)*]) => { ccs_exp_apply_binary! ([== $($ts)*] [$($output)*] [/ $($ops)*]) };
    ([== $($ts:tt)*] [$($output:tt)*] [% $($ops:tt)*]) => { ccs_exp_apply_binary! ([== $($ts)*] [$($output)*] [% $($ops)*]) };
    ([== $($ts:tt)*] [$($output:tt)*] [+ $($ops:tt)*]) => { ccs_exp_apply_binary! ([== $($ts)*] [$($output)*] [+ $($ops)*]) };
    ([== $($ts:tt)*] [$($output:tt)*] [- $($ops:tt)*]) => { ccs_exp_apply_binary! ([== $($ts)*] [$($output)*] [- $($ops)*]) };
    ([== $($ts:tt)*] [$($output:tt)*] [^ $($ops:tt)*]) => { ccs_exp_apply_binary! ([== $($ts)*] [$($output)*] [^ $($ops)*]) };
    ([== $($ts:tt)*] [$($output:tt)*] [< $($ops:tt)*]) => { ccs_exp_apply_binary! ([== $($ts)*] [$($output)*] [< $($ops)*]) };
    ([== $($ts:tt)*] [$($output:tt)*] [<= $($ops:tt)*]) => { ccs_exp_apply_binary! ([== $($ts)*] [$($output)*] [<= $($ops)*]) };
    ([== $($ts:tt)*] [$($output:tt)*] [> $($ops:tt)*]) => { ccs_exp_apply_binary! ([== $($ts)*] [$($output)*] [> $($ops)*]) };
    ([== $($ts:tt)*] [$($output:tt)*] [>= $($ops:tt)*]) => { ccs_exp_apply_binary! ([== $($ts)*] [$($output)*] [>= $($ops)*]) };
    ([== $($ts:tt)*] [$($output:tt)*] [== $($ops:tt)*]) => { ccs_exp_apply_binary! ([== $($ts)*] [$($output)*] [== $($ops)*]) };
    ([== $($ts:tt)*] [$($output:tt)*] [!= $($ops:tt)*]) => { ccs_exp_apply_binary! ([== $($ts)*] [$($output)*] [!= $($ops)*]) };
    ([== $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*])   => { ccs_exp_parse_operand!([$($ts)*] [$($output)*] [== $($ops)*]) };

    ([!= $($ts:tt)*] [$($output:tt)*] [* $($ops:tt)*]) => { ccs_exp_apply_binary! ([!= $($ts)*] [$($output)*] [* $($ops)*]) };
    ([!= $($ts:tt)*] [$($output:tt)*] [/ $($ops:tt)*]) => { ccs_exp_apply_binary! ([!= $($ts)*] [$($output)*] [/ $($ops)*]) };
    ([!= $($ts:tt)*] [$($output:tt)*] [% $($ops:tt)*]) => { ccs_exp_apply_binary! ([!= $($ts)*] [$($output)*] [% $($ops)*]) };
    ([!= $($ts:tt)*] [$($output:tt)*] [+ $($ops:tt)*]) => { ccs_exp_apply_binary! ([!= $($ts)*] [$($output)*] [+ $($ops)*]) };
    ([!= $($ts:tt)*] [$($output:tt)*] [- $($ops:tt)*]) => { ccs_exp_apply_binary! ([!= $($ts)*] [$($output)*] [- $($ops)*]) };
    ([!= $($ts:tt)*] [$($output:tt)*] [^ $($ops:tt)*]) => { ccs_exp_apply_binary! ([!= $($ts)*] [$($output)*] [^ $($ops)*]) };
    ([!= $($ts:tt)*] [$($output:tt)*] [< $($ops:tt)*]) => { ccs_exp_apply_binary! ([!= $($ts)*] [$($output)*] [< $($ops)*]) };
    ([!= $($ts:tt)*] [$($output:tt)*] [<= $($ops:tt)*]) => { ccs_exp_apply_binary! ([!= $($ts)*] [$($output)*] [<= $($ops)*]) };
    ([!= $($ts:tt)*] [$($output:tt)*] [> $($ops:tt)*]) => { ccs_exp_apply_binary! ([!= $($ts)*] [$($output)*] [> $($ops)*]) };
    ([!= $($ts:tt)*] [$($output:tt)*] [>= $($ops:tt)*]) => { ccs_exp_apply_binary! ([!= $($ts)*] [$($output)*] [>= $($ops)*]) };
    ([!= $($ts:tt)*] [$($output:tt)*] [== $($ops:tt)*]) => { ccs_exp_apply_binary! ([!= $($ts)*] [$($output)*] [== $($ops)*]) };
    ([!= $($ts:tt)*] [$($output:tt)*] [!= $($ops:tt)*]) => { ccs_exp_apply_binary! ([!= $($ts)*] [$($output)*] [!= $($ops)*]) };
    ([!= $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*])   => { ccs_exp_parse_operand!([$($ts)*] [$($output)*] [!= $($ops)*]) };

    ([&& $($ts:tt)*] [$($output:tt)*] [* $($ops:tt)*]) => { ccs_exp_apply_binary! ([&& $($ts)*] [$($output)*] [* $($ops)*]) };
    ([&& $($ts:tt)*] [$($output:tt)*] [/ $($ops:tt)*]) => { ccs_exp_apply_binary! ([&& $($ts)*] [$($output)*] [/ $($ops)*]) };
    ([&& $($ts:tt)*] [$($output:tt)*] [% $($ops:tt)*]) => { ccs_exp_apply_binary! ([&& $($ts)*] [$($output)*] [% $($ops)*]) };
    ([&& $($ts:tt)*] [$($output:tt)*] [+ $($ops:tt)*]) => { ccs_exp_apply_binary! ([&& $($ts)*] [$($output)*] [+ $($ops)*]) };
    ([&& $($ts:tt)*] [$($output:tt)*] [- $($ops:tt)*]) => { ccs_exp_apply_binary! ([&& $($ts)*] [$($output)*] [- $($ops)*]) };
    ([&& $($ts:tt)*] [$($output:tt)*] [^ $($ops:tt)*]) => { ccs_exp_apply_binary! ([&& $($ts)*] [$($output)*] [^ $($ops)*]) };
    ([&& $($ts:tt)*] [$($output:tt)*] [< $($ops:tt)*]) => { ccs_exp_apply_binary! ([&& $($ts)*] [$($output)*] [< $($ops)*]) };
    ([&& $($ts:tt)*] [$($output:tt)*] [<= $($ops:tt)*]) => { ccs_exp_apply_binary! ([&& $($ts)*] [$($output)*] [<= $($ops)*]) };
    ([&& $($ts:tt)*] [$($output:tt)*] [> $($ops:tt)*]) => { ccs_exp_apply_binary! ([&& $($ts)*] [$($output)*] [> $($ops)*]) };
    ([&& $($ts:tt)*] [$($output:tt)*] [>= $($ops:tt)*]) => { ccs_exp_apply_binary! ([&& $($ts)*] [$($output)*] [>= $($ops)*]) };
    ([&& $($ts:tt)*] [$($output:tt)*] [== $($ops:tt)*]) => { ccs_exp_apply_binary! ([&& $($ts)*] [$($output)*] [== $($ops)*]) };
    ([&& $($ts:tt)*] [$($output:tt)*] [!= $($ops:tt)*]) => { ccs_exp_apply_binary! ([&& $($ts)*] [$($output)*] [!= $($ops)*]) };
    ([&& $($ts:tt)*] [$($output:tt)*] [&& $($ops:tt)*]) => { ccs_exp_apply_binary! ([&& $($ts)*] [$($output)*] [&& $($ops)*]) };
    ([&& $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*])   => { ccs_exp_parse_operand!([$($ts)*] [$($output)*] [&& $($ops)*]) };

    ([|| $($ts:tt)*] [$($output:tt)*] [* $($ops:tt)*]) => { ccs_exp_apply_binary! ([|| $($ts)*] [$($output)*] [* $($ops)*]) };
    ([|| $($ts:tt)*] [$($output:tt)*] [/ $($ops:tt)*]) => { ccs_exp_apply_binary! ([|| $($ts)*] [$($output)*] [/ $($ops)*]) };
    ([|| $($ts:tt)*] [$($output:tt)*] [% $($ops:tt)*]) => { ccs_exp_apply_binary! ([|| $($ts)*] [$($output)*] [% $($ops)*]) };
    ([|| $($ts:tt)*] [$($output:tt)*] [+ $($ops:tt)*]) => { ccs_exp_apply_binary! ([|| $($ts)*] [$($output)*] [+ $($ops)*]) };
    ([|| $($ts:tt)*] [$($output:tt)*] [- $($ops:tt)*]) => { ccs_exp_apply_binary! ([|| $($ts)*] [$($output)*] [- $($ops)*]) };
    ([|| $($ts:tt)*] [$($output:tt)*] [^ $($ops:tt)*]) => { ccs_exp_apply_binary! ([|| $($ts)*] [$($output)*] [^ $($ops)*]) };
    ([|| $($ts:tt)*] [$($output:tt)*] [< $($ops:tt)*]) => { ccs_exp_apply_binary! ([|| $($ts)*] [$($output)*] [< $($ops)*]) };
    ([|| $($ts:tt)*] [$($output:tt)*] [<= $($ops:tt)*]) => { ccs_exp_apply_binary! ([|| $($ts)*] [$($output)*] [<= $($ops)*]) };
    ([|| $($ts:tt)*] [$($output:tt)*] [> $($ops:tt)*]) => { ccs_exp_apply_binary! ([|| $($ts)*] [$($output)*] [> $($ops)*]) };
    ([|| $($ts:tt)*] [$($output:tt)*] [>= $($ops:tt)*]) => { ccs_exp_apply_binary! ([|| $($ts)*] [$($output)*] [>= $($ops)*]) };
    ([|| $($ts:tt)*] [$($output:tt)*] [== $($ops:tt)*]) => { ccs_exp_apply_binary! ([|| $($ts)*] [$($output)*] [== $($ops)*]) };
    ([|| $($ts:tt)*] [$($output:tt)*] [!= $($ops:tt)*]) => { ccs_exp_apply_binary! ([|| $($ts)*] [$($output)*] [!= $($ops)*]) };
    ([|| $($ts:tt)*] [$($output:tt)*] [&& $($ops:tt)*]) => { ccs_exp_apply_binary! ([|| $($ts)*] [$($output)*] [&& $($ops)*]) };
    ([|| $($ts:tt)*] [$($output:tt)*] [|| $($ops:tt)*]) => { ccs_exp_apply_binary! ([|| $($ts)*] [$($output)*] [|| $($ops)*]) };
    ([|| $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*])   => { ccs_exp_parse_operand!([$($ts)*] [$($output)*] [|| $($ops)*]) };

    ([]             [($output:expr)] [])              => { $output };
    ([]             [$($output:tt)*] [$($ops:tt)*])   => { ccs_exp_apply_binary! ([]        [$($output)*] [$($ops)*]) };
}

#[doc(hidden)]
#[macro_export]
macro_rules! ccs_exp_apply_binary {
    ([$($ts:tt)*] [($b:expr) ($a:expr) $($output:tt)*] [+ $($ops:tt)*]) => {{
        ccs_exp_parse_operator!([$($ts)*] [(Exp::Binary(BinaryOp::Plus, Arc::new($a), Arc::new($b))) $($output)*] [$($ops)*])
    }};
    ([$($ts:tt)*] [($b:expr) ($a:expr) $($output:tt)*] [- $($ops:tt)*]) => {{
        ccs_exp_parse_operator!([$($ts)*] [(Exp::Binary(BinaryOp::Minus, Arc::new($a), Arc::new($b))) $($output)*] [$($ops)*])
    }};
    ([$($ts:tt)*] [($b:expr) ($a:expr) $($output:tt)*] [* $($ops:tt)*]) => {{
        ccs_exp_parse_operator!([$($ts)*] [(Exp::Binary(BinaryOp::Star, Arc::new($a), Arc::new($b))) $($output)*] [$($ops)*])
    }};
    ([$($ts:tt)*] [($b:expr) ($a:expr) $($output:tt)*] [/ $($ops:tt)*]) => {{
        ccs_exp_parse_operator!([$($ts)*] [(Exp::Binary(BinaryOp::Slash, Arc::new($a), Arc::new($b))) $($output)*] [$($ops)*])
    }};
    ([$($ts:tt)*] [($b:expr) ($a:expr) $($output:tt)*] [% $($ops:tt)*]) => {{
        ccs_exp_parse_operator!([$($ts)*] [(Exp::Binary(BinaryOp::Percent, Arc::new($a), Arc::new($b))) $($output)*] [$($ops)*])
    }};
    ([$($ts:tt)*] [($b:expr) ($a:expr) $($output:tt)*] [^ $($ops:tt)*]) => {{
        ccs_exp_parse_operator!([$($ts)*] [(Exp::Binary(BinaryOp::Hat, Arc::new($a), Arc::new($b))) $($output)*] [$($ops)*])
    }};
    ([$($ts:tt)*] [($b:expr) ($a:expr) $($output:tt)*] [< $($ops:tt)*]) => {{
        ccs_exp_parse_operator!([$($ts)*] [(Exp::Binary(BinaryOp::LT, Arc::new($a), Arc::new($b))) $($output)*] [$($ops)*])
    }};
    ([$($ts:tt)*] [($b:expr) ($a:expr) $($output:tt)*] [<= $($ops:tt)*]) => {{
        ccs_exp_parse_operator!([$($ts)*] [(Exp::Binary(BinaryOp::LEq, Arc::new($a), Arc::new($b))) $($output)*] [$($ops)*])
    }};
    ([$($ts:tt)*] [($b:expr) ($a:expr) $($output:tt)*] [> $($ops:tt)*]) => {{
        ccs_exp_parse_operator!([$($ts)*] [(Exp::Binary(BinaryOp::GT, Arc::new($a), Arc::new($b))) $($output)*] [$($ops)*])
    }};
    ([$($ts:tt)*] [($b:expr) ($a:expr) $($output:tt)*] [>= $($ops:tt)*]) => {{
        ccs_exp_parse_operator!([$($ts)*] [(Exp::Binary(BinaryOp::GEq, Arc::new($a), Arc::new($b))) $($output)*] [$($ops)*])
    }};
    ([$($ts:tt)*] [($b:expr) ($a:expr) $($output:tt)*] [== $($ops:tt)*]) => {{
        ccs_exp_parse_operator!([$($ts)*] [(Exp::Binary(BinaryOp::EqEq, Arc::new($a), Arc::new($b))) $($output)*] [$($ops)*])
    }};
    ([$($ts:tt)*] [($b:expr) ($a:expr) $($output:tt)*] [!= $($ops:tt)*]) => {{
        ccs_exp_parse_operator!([$($ts)*] [(Exp::Binary(BinaryOp::NEq, Arc::new($a), Arc::new($b))) $($output)*] [$($ops)*])
    }};
    ([$($ts:tt)*] [($b:expr) ($a:expr) $($output:tt)*] [&& $($ops:tt)*]) => {{
        ccs_exp_parse_operator!([$($ts)*] [(Exp::Binary(BinaryOp::AndAnd, Arc::new($a), Arc::new($b))) $($output)*] [$($ops)*])
    }};
    ([$($ts:tt)*] [($b:expr) ($a:expr) $($output:tt)*] [|| $($ops:tt)*]) => {{
        ccs_exp_parse_operator!([$($ts)*] [(Exp::Binary(BinaryOp::PipePipe, Arc::new($a), Arc::new($b))) $($output)*] [$($ops)*])
    }};
}



#[macro_export]
macro_rules! ccs_bind {
    (@$var:tt) => {
        $var
    };
    ($name:ident := $($ts:tt)*) => {{
        use $crate::*;
        #[allow(unused_imports)]
        use std::sync::Arc;
        Binding::new(stringify!($name).to_string(), vec![], ccs!($($ts)*))
    }};
    ($name:ident[$($args:ident),*] := $($ts:tt)*) => {{
        use $crate::*;
        #[allow(unused_imports)]
        use std::sync::Arc;
        Binding::new(stringify!($name).to_string(), vec![$(stringify!($args).to_string()),*], ccs!($($ts)*))
    }};
}



#[macro_export]
macro_rules! ccs_prog {
    ($({$($binds:tt)*})*) => {{
        use $crate::*;
        #[allow(unused_imports)]
        use std::sync::Arc;
        let mut prog = Program::new();
        $( prog.add_binding(ccs_bind!($($binds)*)); )*
        prog
    }};
    ($({$($binds:tt)*})* ($($proc:tt)+)) => {{
        use $crate::*;
        #[allow(unused_imports)]
        use std::sync::Arc;
        let mut prog = Program::new();
        $( prog.add_binding(ccs_bind!($($binds)*)); )*
        prog.set_process(ccs!{$($proc)*});
        prog
    }};
}
