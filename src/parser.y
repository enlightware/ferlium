%start Module

// we do not need this atm as we are not using the parser's built in error recovery
%avoid_insert 'UNMATCHED' 'INT' 'IDENT' 'true' 'false'

// least precedence to highest precedence
// inspired by Rust: https://doc.rust-lang.org/reference/expressions.html#expression-precedence
%left ';'
%nonassoc NO_ELSE
%nonassoc 'return' 'if' 'then' 'else' 'match' 'with' 'let' 'var' '=>'
%nonassoc '='
%nonassoc '|'
%left 'or'
%left 'and'
%nonassoc '==' '!=' '<' '<=' '>' '>='
%nonassoc '[' ']'
%left '+' '-'
%left '*' '/' '%'
%right 'U_MINUS' 'not'
%right '.'
%nonassoc '(' ')'

%expect-unused 'U_MINUS' 'NO_ELSE'
%expect-unused Unmatched 'UNMATCHED'

%%

Module -> (Module, Option<Expr>)
    : FunctionsOrTypes Expr
        { ( $1, Some($2) ) }
    | FunctionsOrTypes
        { ( $1, None ) }
    | Expr
        { ( Module::default(), Some($1) ) }
    ;

FunctionsOrTypes -> Module
    : FunctionsOrTypes FunctionOrType
        { let mut module = $1; module.extend($2); module }
    | FunctionOrType
        { $1 }
    ;

FunctionOrType -> Module
    : Function
        { $1 }
    ;

Function -> Module
    : 'fn' 'IDENT' '(' StringArgsOptComma ')' '{' Expr '}'
        {
            let args_span = Span::new(lex_span($3).start(), lex_span($5).end());
            Module::new_with_function((s($2, $lexer), lex_span($2)), $4, args_span, $7, $span)
        }
    ;

//Type -> Module
//    ;

// Operators, see https://doc.rust-lang.org/reference/expressions/operator-expr.html

Expr -> Expr
    : Expr '+' Expr
        { Expr::new(StaticApply(ustr("std::@b+"), vec![$1, $3]), $span) }
    | Expr '-' Expr
        { Expr::new(StaticApply(ustr("std::@b-"), vec![$1, $3]), $span) }
    | Expr '*' Expr
        { Expr::new(StaticApply(ustr("std::@b*"), vec![$1, $3]), $span) }
    | Expr '/' Expr
        { Expr::new(StaticApply(ustr("std::@b/"), vec![$1, $3]), $span) }
    | Expr '%' Expr
        { Expr::new(StaticApply(ustr("std::@b%"), vec![$1, $3]), $span) }
    | Expr 'or' Expr
        { Expr::new(StaticApply(ustr("std::@or"), vec![$1, $3]), $span) }
    | Expr 'and' Expr
        { Expr::new(StaticApply(ustr("std::@and"), vec![$1, $3]), $span) }
    | '-' Expr %prec U_MINUS
        { Expr::new(StaticApply(ustr("std::@u-"), vec![$2]), $span) }
    | 'not' Expr
        { Expr::new(StaticApply(ustr("std::@not"), vec![$2]), $span) }
    | Expr '==' Expr
        { Expr::new(StaticApply(ustr("std::@=="), vec![$1, $3]), $span) }
    | Expr '!=' Expr
        { Expr::new(StaticApply(ustr("std::@!="), vec![$1, $3]), $span) }
    | Expr '<' Expr
        { Expr::new(StaticApply(ustr("std::@<"), vec![$1, $3]), $span) }
    | Expr '<=' Expr
        { Expr::new(StaticApply(ustr("std::@<="), vec![$1, $3]), $span) }
    | Expr '>' Expr
        { Expr::new(StaticApply(ustr("std::@>"), vec![$1, $3]), $span) }
    | Expr '>=' Expr
        { Expr::new(StaticApply(ustr("std::@>="), vec![$1, $3]), $span) }
    | Expr '=' Expr
        { Expr::new(Assign(B::new($1), lex_span($2), B::new($3)), $span) }
    | 'if' Expr '{' Expr '}' 'else' '{' Expr '}'
        { make_if_else($2, $4, $8, $span) }
    | 'if' Expr '{' Expr '}' %prec NO_ELSE
        { make_if_without_else($2, $4, $span) }
    | 'match' Expr '{' MatchArgsOptComma '}'
        { Expr::new(Match(B::new($2), $4, None), $span) }
    | 'match' Expr '{' MatchArgs ',' '_' '=>' ExprOptComma '}'
        { Expr::new(Match(B::new($2), $4, Some(B::new($8))), $span) }
    | 'for' 'IDENT' 'in' Expr '..' Expr '{' Expr '}'
        { make_iteration($2, $4, $6, $8, $lexer, $span) }
    | 'return' Expr
        { error("Return statements are not yet supported", $span) }
    | '(' Expr ')'
        { $2 }
    | Path
        { Expr::new(Variable(ustr($lexer.span_str($span))), $span) }
    | Literal
        { $1 }
    | 'let' 'IDENT' '=' Expr
        { Expr::new(LetVar((s($2, $lexer), lex_span($2)), MutVal::constant(), B::new($4)), $span) }
    | 'var' 'IDENT' '=' Expr
        { Expr::new(LetVar((s($2, $lexer), lex_span($2)), MutVal::mutable(), B::new($4)), $span) }
    | '|' StringArgsOptComma '|' Expr
        { Expr::new(Abstract($2, B::new($4)), $span) }
    | '(' ')'
        { Expr::new(Literal(Value::unit(), Type::unit()), $span) }
    | '(' TupleArgs ')'
        { make_tuple($2, $span) }
    | Expr '.' 'INT'
        { make_proj_or_float($1, $3, $lexer, $span) }
    | Expr '.' 'IDENT'
        { error("Named field projection and record are not yet supported", $span) }
    | '[' ']'
        { Expr::new(Array(vec![]), $span) }
    | '[' ExprArgsOptComma ']'
        { Expr::new(Array($2), $span) }
    | Expr '(' ')'
        { Expr::new(Apply(B::new($1), vec![]), $span) }
    | Expr '(' ExprArgsOptComma ')'
        { Expr::new(Apply(B::new($1), $3), $span) }
    | Expr '[' Expr ']'
        { Expr::new(Index(B::new($1), B::new($3)), $span) }
    | '{' RecordFieldsOptComma '}'
        { error("Record is not yet supported", $span) }
    | Expr ';' Expr
        { make_block($1, $3, $span) }
    ;

// TODO: add enum, add more notations for float

Path -> ()
    : 'IDENT'
        { () }
    | 'IDENT' '::' Path
        { () }
    ;

ExprOptComma -> Expr
    : Expr ','
        { $1 }
    | Expr
        { $1 }
    ;

StringArgsOptComma -> Vec<(Ustr, Span)>
    : StringArgs ','
        { $1 }
    | StringArgs
        { $1 }
    ;

StringArgs -> Vec<(Ustr, Span)>
    : StringArgs ',' 'IDENT'
        { let mut args = $1; args.push((s($3, $lexer), lex_span($3))); args }
    | 'IDENT'
        { vec![(s($1, $lexer), lex_span($1))] }
    | %empty
        { vec![] }
    ;

ExprArgsOptComma -> Vec<Expr>
    : ExprArgs ','
        { $1 }
    | ExprArgs
        { $1 }
    ;

ExprArgs -> Vec<Expr>
    : ExprArgs ',' Expr
        { let mut args = $1; args.push($3); args }
    | Expr
        { vec![$1] }
    ;

TupleArgs -> Vec<Expr>
    : Expr ',' ExprArgs
        { let mut args = vec![$1]; args.append(&mut $3); args }
    | Expr ',' ExprArgs ','
        { let mut args = vec![$1]; args.append(&mut $3); args }
    | Expr ','
        { vec![$1] }
    ;

RecordFieldsOptComma -> ()
    : RecordFields ','
        {}
    | RecordFields
        {}
    ;

RecordFields -> ()
    : RecordFields ',' 'IDENT' ':' Expr
        {}
    | 'IDENT' ':' Expr
        {}
    ;

MatchArgsOptComma -> Vec<(Expr, Expr)>
    : MatchArgs ','
        { $1 }
    | MatchArgs
        { $1 }
    ;

MatchArgs -> Vec<(Expr, Expr)>
    : MatchArgs ',' MatchArg
        { let mut args = $1; args.push($3); args }
    | MatchArg
        { vec![$1] }
    ;

MatchArg -> (Expr, Expr)
    : Pattern '=>' Expr
        { ($1, $3) }
    ;

Pattern -> Expr
    : Expr
        { $1 }
    ;

Literal -> Expr
    : INT
        { parse_num::<isize>(&s($1, $lexer), lex_span($1)) }
    | BoolLiteral
        { Expr::new(Literal($1, Type::primitive::<bool>()), $span) }
    ;

BoolLiteral -> Value
    : 'true'
        { Value::native(true) }
    | 'false'
        { Value::native(false) }
    ;

Unmatched -> ()
    : 'UNMATCHED' { }
    ;

%%

use crate::ast::{Expr, Module};
use crate::ast::ExprKind::*;
use crate::value::Value;
use crate::r#type::Type;
use crate::containers::B;
use crate::mutability::MutVal;
use ustr::{Ustr, ustr};
use lrpar::Span;

// Parser support code is in this module
use crate::parser_helpers::*;
