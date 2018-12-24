pub use crate::{ccs_act, ccs, ccs_bind, ccs_prog};

#[macro_export]
macro_rules! ccs_act {
    ($($ts:tt)*) => {{
        use $crate::*;
        ccs_parse_act!($($ts)*)
    }};
}

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
        use std::rc::Rc;
        ccs_parse_operand!([$($ts)*] [] [])
    }};
}

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
        ccs_apply_unary!([$($ts)*] [(Rc::new(Process::Null)) $($output)*] [$($ops)*])
    }};
    ([1 $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*]) => {{
        ccs_apply_unary!([$($ts)*] [(Rc::new(Process::Term)) $($output)*] [$($ops)*])
    }};
    ([$name:ident [$($args:tt),*] $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*]) => {{
        let name = stringify!($name);
        let mut args = Vec::new();
        $( args.push(ccs_exp!{ $args }); )*
        ccs_apply_unary!([$($ts)*] [(Rc::new(Process::Name(name.to_string(), args))) $($output)*] [$($ops)*])
    }};
    ([$name:ident $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*]) => {{
        let name = stringify!($name);
        ccs_apply_unary!([$($ts)*] [(Rc::new(Process::Name(name.to_string(), vec![]))) $($output)*] [$($ops)*])
    }};
    ([@$var:tt $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*]) => {
        ccs_apply_unary!([$($ts)*] [($var) $($output)*] [$($ops)*])
    };
    ([($($t:tt)*) $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*]) => {{
        let exp = ccs!($($t)*);
        ccs_apply_unary!([$($ts)*] [(exp) $($output)*] [$($ops)*])
    }};
}

#[macro_export]
macro_rules! ccs_apply_unary {
    ([$($ts:tt)*] [($process:expr) ($cond:expr) $($output:tt)*] [when $($ops:tt)*]) => {{
        ccs_apply_unary!([$($ts)*] [(Rc::new(Process::When($cond, $process))) $($output)*] [$($ops)*])
    }};
    ([$($ts:tt)*] [($process:expr) ($action:expr) $($output:tt)*] [. $($ops:tt)*]) => {{
        ccs_apply_unary!([$($ts)*] [(Rc::new(Process::Prefix($action, $process))) $($output)*] [$($ops)*])
    }};
    ([/ { * } $($ts:tt)*] [($process:expr) $($output:tt)*] [$($ops:tt)*]) => {{
        ccs_apply_unary!([$($ts)*] [(Rc::new(Process::Restrict($process, true, BTreeSet::new()))) $($output)*] [$($ops)*])
    }};
    ([/ { *, $($acts:ident),* } $($ts:tt)*] [($process:expr) $($output:tt)*] [$($ops:tt)*]) => {{
        let mut set = BTreeSet::new();
        $( set.insert(stringify!($acts).to_string()); )*
        ccs_apply_unary!([$($ts)*] [(Rc::new(Process::Restrict($process, true, set))) $($output)*] [$($ops)*])
    }};
    ([/ { $($acts:ident),* } $($ts:tt)*] [($process:expr) $($output:tt)*] [$($ops:tt)*]) => {{
        let mut set = BTreeSet::new();
        $( set.insert(stringify!($acts).to_string()); )*
        ccs_apply_unary!([$($ts)*] [(Rc::new(Process::Restrict($process, false, set))) $($output)*] [$($ops)*])
    }};
    ([$($ts:tt)*] [$($output:tt)*] [$($ops:tt)*]) => {
        ccs_parse_operator!([$($ts)*] [$($output)*] [$($ops)*])
    };
}

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

#[macro_export]
macro_rules! ccs_apply_binary {
    ([$($ts:tt)*] [($b:expr) ($a:expr) $($output:tt)*] [+ $($ops:tt)*]) => {{
        ccs_parse_operator!([$($ts)*] [(Rc::new(Process::Choice($a, $b))) $($output)*] [$($ops)*])
    }};
    ([$($ts:tt)*] [($b:expr) ($a:expr) $($output:tt)*] [| $($ops:tt)*]) => {{
        ccs_parse_operator!([$($ts)*] [(Rc::new(Process::Parallel($a, $b))) $($output)*] [$($ops)*])
    }};
    ([$($ts:tt)*] [($b:expr) ($a:expr) $($output:tt)*] [; $($ops:tt)*]) => {{
        ccs_parse_operator!([$($ts)*] [(Rc::new(Process::Sequential($a, $b))) $($output)*] [$($ops)*])
    }};
}



#[macro_export]
macro_rules! ccs_exp {
    ($($ts:tt)*) => {{
        use $crate::*;
        #[allow(unused_imports)]
        use std::collections::BTreeSet;
        #[allow(unused_imports)]
        use std::rc::Rc;
        ccs_exp_parse_operand!([$($ts)*] [] [])
    }};
}

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
        ccs_exp_apply_unary!([$($ts)*] [(Rc::new(Exp::from($const))) $($output)*] [$($ops)*])
    }};
    ([$name:ident $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*]) => {{
        let name = stringify!($name);
        ccs_exp_apply_unary!([$($ts)*] [(Rc::new(Exp::IdExp(name.to_string()))) $($output)*] [$($ops)*])
    }};
    ([@$var:tt $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*]) => {
        ccs_exp_apply_unary!([$($ts)*] [($var) $($output)*] [$($ops)*])
    };
    ([($($t:tt)*) $($ts:tt)*] [$($output:tt)*] [$($ops:tt)*]) => {{
        let exp = ccs_exp!($($t)*);
        ccs_exp_apply_unary!([$($ts)*] [(exp) $($output)*] [$($ops)*])
    }};
}

#[macro_export]
macro_rules! ccs_exp_apply_unary {
    ([$($ts:tt)*] [($exp:expr) $($output:tt)*] [.+ $($ops:tt)*]) => {{
        ccs_exp_apply_unary!([$($ts)*] [(Rc::new(Exp::Unary(UnaryOp::Plus, $exp))) $($output)*] [$($ops)*])
    }};
    ([$($ts:tt)*] [($exp:expr) $($output:tt)*] [.- $($ops:tt)*]) => {{
        ccs_exp_apply_unary!([$($ts)*] [(Rc::new(Exp::Unary(UnaryOp::Minus, $exp))) $($output)*] [$($ops)*])
    }};
    ([$($ts:tt)*] [($exp:expr) $($output:tt)*] [.! $($ops:tt)*]) => {{
        ccs_exp_apply_unary!([$($ts)*] [(Rc::new(Exp::Unary(UnaryOp::Not, $exp))) $($output)*] [$($ops)*])
    }};
    ([$($ts:tt)*] [$($output:tt)*] [$($ops:tt)*]) => {
        ccs_exp_parse_operator!([$($ts)*] [$($output)*] [$($ops)*])
    };
}

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

#[macro_export]
macro_rules! ccs_exp_apply_binary {
    ([$($ts:tt)*] [($b:expr) ($a:expr) $($output:tt)*] [+ $($ops:tt)*]) => {{
        ccs_exp_parse_operator!([$($ts)*] [(Rc::new(Exp::Binary(BinaryOp::Plus, $a, $b))) $($output)*] [$($ops)*])
    }};
    ([$($ts:tt)*] [($b:expr) ($a:expr) $($output:tt)*] [- $($ops:tt)*]) => {{
        ccs_exp_parse_operator!([$($ts)*] [(Rc::new(Exp::Binary(BinaryOp::Minus, $a, $b))) $($output)*] [$($ops)*])
    }};
    ([$($ts:tt)*] [($b:expr) ($a:expr) $($output:tt)*] [* $($ops:tt)*]) => {{
        ccs_exp_parse_operator!([$($ts)*] [(Rc::new(Exp::Binary(BinaryOp::Star, $a, $b))) $($output)*] [$($ops)*])
    }};
    ([$($ts:tt)*] [($b:expr) ($a:expr) $($output:tt)*] [/ $($ops:tt)*]) => {{
        ccs_exp_parse_operator!([$($ts)*] [(Rc::new(Exp::Binary(BinaryOp::Slash, $a, $b))) $($output)*] [$($ops)*])
    }};
    ([$($ts:tt)*] [($b:expr) ($a:expr) $($output:tt)*] [% $($ops:tt)*]) => {{
        ccs_exp_parse_operator!([$($ts)*] [(Rc::new(Exp::Binary(BinaryOp::Percent, $a, $b))) $($output)*] [$($ops)*])
    }};
    ([$($ts:tt)*] [($b:expr) ($a:expr) $($output:tt)*] [^ $($ops:tt)*]) => {{
        ccs_exp_parse_operator!([$($ts)*] [(Rc::new(Exp::Binary(BinaryOp::Hat, $a, $b))) $($output)*] [$($ops)*])
    }};
    ([$($ts:tt)*] [($b:expr) ($a:expr) $($output:tt)*] [< $($ops:tt)*]) => {{
        ccs_exp_parse_operator!([$($ts)*] [(Rc::new(Exp::Binary(BinaryOp::LT, $a, $b))) $($output)*] [$($ops)*])
    }};
    ([$($ts:tt)*] [($b:expr) ($a:expr) $($output:tt)*] [<= $($ops:tt)*]) => {{
        ccs_exp_parse_operator!([$($ts)*] [(Rc::new(Exp::Binary(BinaryOp::LEq, $a, $b))) $($output)*] [$($ops)*])
    }};
    ([$($ts:tt)*] [($b:expr) ($a:expr) $($output:tt)*] [> $($ops:tt)*]) => {{
        ccs_exp_parse_operator!([$($ts)*] [(Rc::new(Exp::Binary(BinaryOp::GT, $a, $b))) $($output)*] [$($ops)*])
    }};
    ([$($ts:tt)*] [($b:expr) ($a:expr) $($output:tt)*] [>= $($ops:tt)*]) => {{
        ccs_exp_parse_operator!([$($ts)*] [(Rc::new(Exp::Binary(BinaryOp::GEq, $a, $b))) $($output)*] [$($ops)*])
    }};
    ([$($ts:tt)*] [($b:expr) ($a:expr) $($output:tt)*] [== $($ops:tt)*]) => {{
        ccs_exp_parse_operator!([$($ts)*] [(Rc::new(Exp::Binary(BinaryOp::EqEq, $a, $b))) $($output)*] [$($ops)*])
    }};
    ([$($ts:tt)*] [($b:expr) ($a:expr) $($output:tt)*] [!= $($ops:tt)*]) => {{
        ccs_exp_parse_operator!([$($ts)*] [(Rc::new(Exp::Binary(BinaryOp::NEq, $a, $b))) $($output)*] [$($ops)*])
    }};
    ([$($ts:tt)*] [($b:expr) ($a:expr) $($output:tt)*] [&& $($ops:tt)*]) => {{
        ccs_exp_parse_operator!([$($ts)*] [(Rc::new(Exp::Binary(BinaryOp::AndAnd, $a, $b))) $($output)*] [$($ops)*])
    }};
    ([$($ts:tt)*] [($b:expr) ($a:expr) $($output:tt)*] [|| $($ops:tt)*]) => {{
        ccs_exp_parse_operator!([$($ts)*] [(Rc::new(Exp::Binary(BinaryOp::PipePipe, $a, $b))) $($output)*] [$($ops)*])
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
        use std::rc::Rc;
        Binding::new(stringify!($name).to_string(), vec![], ccs!($($ts)*))
    }};
    ($name:ident[$($args:ident),*] := $($ts:tt)*) => {{
        use $crate::*;
        #[allow(unused_imports)]
        use std::rc::Rc;
        Binding::new(stringify!($name).to_string(), vec![$(stringify!($args).to_string()),*], ccs!($($ts)*))
    }};
}



#[macro_export]
macro_rules! ccs_prog {
    ($({$($binds:tt)*})*) => {{
        use $crate::*;
        #[allow(unused_imports)]
        use std::rc::Rc;
        let mut prog = Program::new();
        $( prog.add_binding(ccs_bind!($($binds)*)); )*
        prog
    }};
    ($({$($binds:tt)*})* ($($proc:tt)+)) => {{
        use $crate::*;
        #[allow(unused_imports)]
        use std::rc::Rc;
        let mut prog = Program::new();
        $( prog.add_binding(ccs_bind!($($binds)*)); )*
        prog.set_process(ccs!{$($proc)*});
        prog
    }};
}
