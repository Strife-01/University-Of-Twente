package nl.utwente.jmlplugin.parser;

import com.intellij.lexer.FlexLexer;
import com.intellij.psi.tree.IElementType;

import static com.intellij.psi.TokenType.BAD_CHARACTER;
import static com.intellij.psi.TokenType.WHITE_SPACE;
import static nl.utwente.jmlplugin.psi.JMLTypes.*;

%%

%{
  public _JMLLexer() {
    this((java.io.Reader)null);
  }
%}

%public
%class _JMLLexer
%implements FlexLexer
%function advance
%type IElementType
%unicode

EOL=\R
WHITE_SPACE=\s+

IDENT=[_$a-zA-Z][_$a-zA-Z0-9]*
WHITE_SPACE=[ \t\n\x0B\f\r]+
INFORMAL_DESCRIPTION=\([ \t\n\x0B\f\r]*\*([^*]|\*+[^*)])+\*[ \t\n\x0B\f\r]*\)
REST=[^@;().,:*\[\]\s]

%%
<YYINITIAL> {
  {WHITE_SPACE}               { return WHITE_SPACE; }

  "signals_only"              { return SIGNALS_ONLY; }
  "\\not_specified"           { return NOT_SPECIFIED; }
  "\\nothing"                 { return NOTHING; }
  "\\everything"              { return EVERYTHING; }
  "\\into"                    { return INTO; }
  "spec_public"               { return SPEC_PUBLIC; }
  "spec_protected"            { return SPEC_PROTECTED; }
  "loop_invariant"            { return LOOPINVARIANT; }
  "@"                         { return AT_SIGN; }
  ";"                         { return SEMICOLON; }
  "("                         { return L_PAREN; }
  ")"                         { return R_PAREN; }
  "."                         { return DOT; }
  ","                         { return COMMA; }
  ":"                         { return COLON; }
  "*"                         { return STAR; }
  "["                         { return L_SQ_BRAC; }
  "]"                         { return R_SQ_BRAC; }
  "also"                      { return ALSO; }
  "requires"                  { return REQUIRES; }
  "pre"                       { return PRE; }
  "ensures"                   { return ENSURES; }
  "post"                      { return POST; }
  "signals"                   { return SIGNALS; }
  "assignable"                { return ASSIGNABLE; }
  "modifiable"                { return MODIFIABLE; }
  "modifies"                  { return MODIFIES; }
  "invariant"                 { return INVARIANT; }
  "pure"                      { return PURE; }
  "instance"                  { return INSTANCE; }
  "helper"                    { return HELPER; }
  "nullable"                  { return NULLABLE; }
  "public"                    { return PUBLIC; }
  "private"                   { return PRIVATE; }
  "protected"                 { return PROTECTED; }
  "static"                    { return STATIC; }
  "maintaining"               { return MAINTAINING; }
  "assert"                    { return ASSERT; }
  "assume"                    { return ASSUME; }
  "this"                      { return THIS; }
  "super"                     { return SUPER; }

  {IDENT}                     { return IDENT; }
  {WHITE_SPACE}               { return WHITE_SPACE; }
  {INFORMAL_DESCRIPTION}      { return INFORMAL_DESCRIPTION; }
  {REST}                      { return REST; }

}

[^] { return BAD_CHARACTER; }
