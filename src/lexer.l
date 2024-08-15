%%
[1-9][0-9]*|0           "INT"

true                    "true"
false                   "false"

if                      "if"
else                    "else"
match                   "match"

for                     "for"
in                      "in"

return                  "return"

let                     "let"
var						"var"

fn                      "fn"

and						"and"
or						"or"
not						"not"

==                      "=="
!=                      "!="
>=                      ">="
\<=                     "<="
>                       ">"
\<                      "<"
=                       "="

\+                      "+"
-                       "-"
\*                      "*"
/                       "/"
%                       "%"

\(                      "("
\)                      ")"
\[                      "["
\]                      "]"
\{                      "{"
\}                      "}"
\|                      "|"
=>                      "=>"
::                      "::"
:                       ":"
;                       ";"
,                       ","
\.\.                    ".."
\.                      "."
_                       "_"

[\p{L}_][\p{L}\p{N}_]*  "IDENT"
\"([^\\\"]|\\.)*\"      "STRING"
f\"([^\\\"]|\\.)*\"     "F_STRING"

[ \t\r\n]+              ;
//[^\n]*                ;
/\*[^*]*\*+([^/*][^*]*\*+)*/ ;

.                       "UNMATCHED"

-                       "U_MINUS"
else                    "NO_ELSE"