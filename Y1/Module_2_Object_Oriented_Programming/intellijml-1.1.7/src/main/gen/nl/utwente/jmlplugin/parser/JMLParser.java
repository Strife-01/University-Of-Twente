// This is a generated file. Not intended for manual editing.
package nl.utwente.jmlplugin.parser;

import com.intellij.lang.PsiBuilder;
import com.intellij.lang.PsiBuilder.Marker;
import static nl.utwente.jmlplugin.psi.JMLTypes.*;
import static nl.utwente.jmlplugin.parser.JMLJavaParser.*;
import com.intellij.psi.tree.IElementType;
import com.intellij.lang.ASTNode;
import com.intellij.psi.tree.TokenSet;
import com.intellij.lang.PsiParser;
import com.intellij.lang.LightPsiParser;

@SuppressWarnings({"SimplifiableIfStatement", "UnusedAssignment"})
public class JMLParser implements PsiParser, LightPsiParser {

  public ASTNode parse(IElementType t, PsiBuilder b) {
    parseLight(t, b);
    return b.getTreeBuilt();
  }

  public void parseLight(IElementType t, PsiBuilder b) {
    boolean r;
    b = adapt_builder_(t, b, this, null);
    Marker m = enter_section_(b, 0, _COLLAPSE_, null);
    r = parse_root_(t, b);
    exit_section_(b, 0, m, t, r, true, TRUE_CONDITION);
  }

  protected boolean parse_root_(IElementType t, PsiBuilder b) {
    return parse_root_(t, b, 0);
  }

  static boolean parse_root_(IElementType t, PsiBuilder b, int l) {
    return jml_root(b, l + 1);
  }

  /* ********************************************************** */
  // assert java_expr SEMICOLON+
  public static boolean assert_statement(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "assert_statement")) return false;
    if (!nextTokenIs(b, ASSERT)) return false;
    boolean r, p;
    Marker m = enter_section_(b, l, _NONE_, ASSERT_STATEMENT, null);
    r = consumeToken(b, ASSERT);
    r = r && java_expr(b, l + 1);
    p = r; // pin = java_expr
    r = r && assert_statement_2(b, l + 1);
    exit_section_(b, l, m, r, p, null);
    return r || p;
  }

  // SEMICOLON+
  private static boolean assert_statement_2(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "assert_statement_2")) return false;
    boolean r;
    Marker m = enter_section_(b);
    r = consumeToken(b, SEMICOLON);
    while (r) {
      int c = current_position_(b);
      if (!consumeToken(b, SEMICOLON)) break;
      if (!empty_element_parsed_guard_(b, "assert_statement_2", c)) break;
    }
    exit_section_(b, m, null, r);
    return r;
  }

  /* ********************************************************** */
  // (assignable|modifiable|modifies) store_ref_list SEMICOLON+
  public static boolean assignable_clause(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "assignable_clause")) return false;
    boolean r;
    Marker m = enter_section_(b, l, _NONE_, ASSIGNABLE_CLAUSE, "<assignable clause>");
    r = assignable_clause_0(b, l + 1);
    r = r && store_ref_list(b, l + 1);
    r = r && assignable_clause_2(b, l + 1);
    exit_section_(b, l, m, r, false, null);
    return r;
  }

  // assignable|modifiable|modifies
  private static boolean assignable_clause_0(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "assignable_clause_0")) return false;
    boolean r;
    r = consumeToken(b, ASSIGNABLE);
    if (!r) r = consumeToken(b, MODIFIABLE);
    if (!r) r = consumeToken(b, MODIFIES);
    return r;
  }

  // SEMICOLON+
  private static boolean assignable_clause_2(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "assignable_clause_2")) return false;
    boolean r;
    Marker m = enter_section_(b);
    r = consumeToken(b, SEMICOLON);
    while (r) {
      int c = current_position_(b);
      if (!consumeToken(b, SEMICOLON)) break;
      if (!empty_element_parsed_guard_(b, "assignable_clause_2", c)) break;
    }
    exit_section_(b, m, null, r);
    return r;
  }

  /* ********************************************************** */
  // assume java_expr SEMICOLON+
  public static boolean assume_statement(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "assume_statement")) return false;
    if (!nextTokenIs(b, ASSUME)) return false;
    boolean r, p;
    Marker m = enter_section_(b, l, _NONE_, ASSUME_STATEMENT, null);
    r = consumeToken(b, ASSUME);
    r = r && java_expr(b, l + 1);
    p = r; // pin = java_expr
    r = r && assume_statement_2(b, l + 1);
    exit_section_(b, l, m, r, p, null);
    return r || p;
  }

  // SEMICOLON+
  private static boolean assume_statement_2(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "assume_statement_2")) return false;
    boolean r;
    Marker m = enter_section_(b);
    r = consumeToken(b, SEMICOLON);
    while (r) {
      int c = current_position_(b);
      if (!consumeToken(b, SEMICOLON)) break;
      if (!empty_element_parsed_guard_(b, "assume_statement_2", c)) break;
    }
    exit_section_(b, m, null, r);
    return r;
  }

  /* ********************************************************** */
  // modifiers? invariant java_expr SEMICOLON+
  public static boolean class_invariant(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "class_invariant")) return false;
    boolean r, p;
    Marker m = enter_section_(b, l, _NONE_, CLASS_INVARIANT, "<class invariant>");
    r = class_invariant_0(b, l + 1);
    r = r && consumeToken(b, INVARIANT);
    r = r && java_expr(b, l + 1);
    p = r; // pin = java_expr
    r = r && class_invariant_3(b, l + 1);
    exit_section_(b, l, m, r, p, null);
    return r || p;
  }

  // modifiers?
  private static boolean class_invariant_0(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "class_invariant_0")) return false;
    modifiers(b, l + 1);
    return true;
  }

  // SEMICOLON+
  private static boolean class_invariant_3(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "class_invariant_3")) return false;
    boolean r;
    Marker m = enter_section_(b);
    r = consumeToken(b, SEMICOLON);
    while (r) {
      int c = current_position_(b);
      if (!consumeToken(b, SEMICOLON)) break;
      if (!empty_element_parsed_guard_(b, "class_invariant_3", c)) break;
    }
    exit_section_(b, m, null, r);
    return r;
  }

  /* ********************************************************** */
  // (class_invariant AT_SIGN*)+
  static boolean class_invariants(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "class_invariants")) return false;
    boolean r;
    Marker m = enter_section_(b);
    r = class_invariants_0(b, l + 1);
    while (r) {
      int c = current_position_(b);
      if (!class_invariants_0(b, l + 1)) break;
      if (!empty_element_parsed_guard_(b, "class_invariants", c)) break;
    }
    exit_section_(b, m, null, r);
    return r;
  }

  // class_invariant AT_SIGN*
  private static boolean class_invariants_0(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "class_invariants_0")) return false;
    boolean r;
    Marker m = enter_section_(b);
    r = class_invariant(b, l + 1);
    r = r && class_invariants_0_1(b, l + 1);
    exit_section_(b, m, null, r);
    return r;
  }

  // AT_SIGN*
  private static boolean class_invariants_0_1(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "class_invariants_0_1")) return false;
    while (true) {
      int c = current_position_(b);
      if (!consumeToken(b, AT_SIGN)) break;
      if (!empty_element_parsed_guard_(b, "class_invariants_0_1", c)) break;
    }
    return true;
  }

  /* ********************************************************** */
  // (ensures|post) pred_or_not SEMICOLON+
  public static boolean ensures_clause(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "ensures_clause")) return false;
    if (!nextTokenIs(b, "<ensures clause>", ENSURES, POST)) return false;
    boolean r, p;
    Marker m = enter_section_(b, l, _NONE_, ENSURES_CLAUSE, "<ensures clause>");
    r = ensures_clause_0(b, l + 1);
    r = r && pred_or_not(b, l + 1);
    p = r; // pin = pred_or_not
    r = r && ensures_clause_2(b, l + 1);
    exit_section_(b, l, m, r, p, null);
    return r || p;
  }

  // ensures|post
  private static boolean ensures_clause_0(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "ensures_clause_0")) return false;
    boolean r;
    r = consumeToken(b, ENSURES);
    if (!r) r = consumeToken(b, POST);
    return r;
  }

  // SEMICOLON+
  private static boolean ensures_clause_2(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "ensures_clause_2")) return false;
    boolean r;
    Marker m = enter_section_(b);
    r = consumeToken(b, SEMICOLON);
    while (r) {
      int c = current_position_(b);
      if (!consumeToken(b, SEMICOLON)) break;
      if (!empty_element_parsed_guard_(b, "ensures_clause_2", c)) break;
    }
    exit_section_(b, m, null, r);
    return r;
  }

  /* ********************************************************** */
  // (AT_SIGN* (loop_invariant | assert_statement | assume_statement))+
  public static boolean in_method_spec(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "in_method_spec")) return false;
    boolean r;
    Marker m = enter_section_(b, l, _NONE_, IN_METHOD_SPEC, "<in-method specification>");
    r = in_method_spec_0(b, l + 1);
    while (r) {
      int c = current_position_(b);
      if (!in_method_spec_0(b, l + 1)) break;
      if (!empty_element_parsed_guard_(b, "in_method_spec", c)) break;
    }
    exit_section_(b, l, m, r, false, null);
    return r;
  }

  // AT_SIGN* (loop_invariant | assert_statement | assume_statement)
  private static boolean in_method_spec_0(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "in_method_spec_0")) return false;
    boolean r;
    Marker m = enter_section_(b);
    r = in_method_spec_0_0(b, l + 1);
    r = r && in_method_spec_0_1(b, l + 1);
    exit_section_(b, m, null, r);
    return r;
  }

  // AT_SIGN*
  private static boolean in_method_spec_0_0(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "in_method_spec_0_0")) return false;
    while (true) {
      int c = current_position_(b);
      if (!consumeToken(b, AT_SIGN)) break;
      if (!empty_element_parsed_guard_(b, "in_method_spec_0_0", c)) break;
    }
    return true;
  }

  // loop_invariant | assert_statement | assume_statement
  private static boolean in_method_spec_0_1(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "in_method_spec_0_1")) return false;
    boolean r;
    r = loop_invariant(b, l + 1);
    if (!r) r = assert_statement(b, l + 1);
    if (!r) r = assume_statement(b, l + 1);
    return r;
  }

  /* ********************************************************** */
  // <<parseJavaExpression>>
  public static boolean java_expr(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "java_expr")) return false;
    boolean r;
    Marker m = enter_section_(b, l, _NONE_, JAVA_EXPR, "<java expr>");
    r = parseJavaExpression(b, l + 1);
    exit_section_(b, l, m, r, false, null);
    return r;
  }

  /* ********************************************************** */
  // public | private | protected | static
  static boolean java_modifier(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "java_modifier")) return false;
    boolean r;
    r = consumeToken(b, PUBLIC);
    if (!r) r = consumeToken(b, PRIVATE);
    if (!r) r = consumeToken(b, PROTECTED);
    if (!r) r = consumeToken(b, STATIC);
    return r;
  }

  /* ********************************************************** */
  // jml_specification
  static boolean jml_root(PsiBuilder b, int l) {
    return jml_specification(b, l + 1);
  }

  /* ********************************************************** */
  // AT_SIGN+ ((method_jml | class_invariants | modifiers | in_method_spec) AT_SIGN*)?
  public static boolean jml_specification(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "jml_specification")) return false;
    if (!nextTokenIs(b, AT_SIGN)) return false;
    boolean r;
    Marker m = enter_section_(b);
    r = jml_specification_0(b, l + 1);
    r = r && jml_specification_1(b, l + 1);
    exit_section_(b, m, JML_SPECIFICATION, r);
    return r;
  }

  // AT_SIGN+
  private static boolean jml_specification_0(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "jml_specification_0")) return false;
    boolean r;
    Marker m = enter_section_(b);
    r = consumeToken(b, AT_SIGN);
    while (r) {
      int c = current_position_(b);
      if (!consumeToken(b, AT_SIGN)) break;
      if (!empty_element_parsed_guard_(b, "jml_specification_0", c)) break;
    }
    exit_section_(b, m, null, r);
    return r;
  }

  // ((method_jml | class_invariants | modifiers | in_method_spec) AT_SIGN*)?
  private static boolean jml_specification_1(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "jml_specification_1")) return false;
    jml_specification_1_0(b, l + 1);
    return true;
  }

  // (method_jml | class_invariants | modifiers | in_method_spec) AT_SIGN*
  private static boolean jml_specification_1_0(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "jml_specification_1_0")) return false;
    boolean r;
    Marker m = enter_section_(b);
    r = jml_specification_1_0_0(b, l + 1);
    r = r && jml_specification_1_0_1(b, l + 1);
    exit_section_(b, m, null, r);
    return r;
  }

  // method_jml | class_invariants | modifiers | in_method_spec
  private static boolean jml_specification_1_0_0(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "jml_specification_1_0_0")) return false;
    boolean r;
    r = method_jml(b, l + 1);
    if (!r) r = class_invariants(b, l + 1);
    if (!r) r = modifiers(b, l + 1);
    if (!r) r = in_method_spec(b, l + 1);
    return r;
  }

  // AT_SIGN*
  private static boolean jml_specification_1_0_1(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "jml_specification_1_0_1")) return false;
    while (true) {
      int c = current_position_(b);
      if (!consumeToken(b, AT_SIGN)) break;
      if (!empty_element_parsed_guard_(b, "jml_specification_1_0_1", c)) break;
    }
    return true;
  }

  /* ********************************************************** */
  // (maintaining | LOOPINVARIANT) java_expr SEMICOLON+
  public static boolean loop_invariant(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "loop_invariant")) return false;
    if (!nextTokenIs(b, "<loop invariant>", LOOPINVARIANT, MAINTAINING)) return false;
    boolean r, p;
    Marker m = enter_section_(b, l, _NONE_, LOOP_INVARIANT, "<loop invariant>");
    r = loop_invariant_0(b, l + 1);
    r = r && java_expr(b, l + 1);
    p = r; // pin = java_expr
    r = r && loop_invariant_2(b, l + 1);
    exit_section_(b, l, m, r, p, null);
    return r || p;
  }

  // maintaining | LOOPINVARIANT
  private static boolean loop_invariant_0(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "loop_invariant_0")) return false;
    boolean r;
    r = consumeToken(b, MAINTAINING);
    if (!r) r = consumeToken(b, LOOPINVARIANT);
    return r;
  }

  // SEMICOLON+
  private static boolean loop_invariant_2(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "loop_invariant_2")) return false;
    boolean r;
    Marker m = enter_section_(b);
    r = consumeToken(b, SEMICOLON);
    while (r) {
      int c = current_position_(b);
      if (!consumeToken(b, SEMICOLON)) break;
      if (!empty_element_parsed_guard_(b, "loop_invariant_2", c)) break;
    }
    exit_section_(b, m, null, r);
    return r;
  }

  /* ********************************************************** */
  // also? method_spec AT_SIGN* modifiers*
  public static boolean method_jml(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "method_jml")) return false;
    boolean r;
    Marker m = enter_section_(b, l, _NONE_, METHOD_JML, "<method specification>");
    r = method_jml_0(b, l + 1);
    r = r && method_spec(b, l + 1);
    r = r && method_jml_2(b, l + 1);
    r = r && method_jml_3(b, l + 1);
    exit_section_(b, l, m, r, false, null);
    return r;
  }

  // also?
  private static boolean method_jml_0(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "method_jml_0")) return false;
    consumeToken(b, ALSO);
    return true;
  }

  // AT_SIGN*
  private static boolean method_jml_2(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "method_jml_2")) return false;
    while (true) {
      int c = current_position_(b);
      if (!consumeToken(b, AT_SIGN)) break;
      if (!empty_element_parsed_guard_(b, "method_jml_2", c)) break;
    }
    return true;
  }

  // modifiers*
  private static boolean method_jml_3(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "method_jml_3")) return false;
    while (true) {
      int c = current_position_(b);
      if (!modifiers(b, l + 1)) break;
      if (!empty_element_parsed_guard_(b, "method_jml_3", c)) break;
    }
    return true;
  }

  /* ********************************************************** */
  // spec_case (AT_SIGN* also spec_case)*
  public static boolean method_spec(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "method_spec")) return false;
    boolean r;
    Marker m = enter_section_(b, l, _NONE_, METHOD_SPEC, "<method specification>");
    r = spec_case(b, l + 1);
    r = r && method_spec_1(b, l + 1);
    exit_section_(b, l, m, r, false, null);
    return r;
  }

  // (AT_SIGN* also spec_case)*
  private static boolean method_spec_1(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "method_spec_1")) return false;
    while (true) {
      int c = current_position_(b);
      if (!method_spec_1_0(b, l + 1)) break;
      if (!empty_element_parsed_guard_(b, "method_spec_1", c)) break;
    }
    return true;
  }

  // AT_SIGN* also spec_case
  private static boolean method_spec_1_0(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "method_spec_1_0")) return false;
    boolean r;
    Marker m = enter_section_(b);
    r = method_spec_1_0_0(b, l + 1);
    r = r && consumeToken(b, ALSO);
    r = r && spec_case(b, l + 1);
    exit_section_(b, m, null, r);
    return r;
  }

  // AT_SIGN*
  private static boolean method_spec_1_0_0(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "method_spec_1_0_0")) return false;
    while (true) {
      int c = current_position_(b);
      if (!consumeToken(b, AT_SIGN)) break;
      if (!empty_element_parsed_guard_(b, "method_spec_1_0_0", c)) break;
    }
    return true;
  }

  /* ********************************************************** */
  // ((SPEC_PUBLIC | SPEC_PROTECTED | pure | instance | helper | nullable | java_modifier) SEMICOLON* AT_SIGN*)+
  public static boolean modifiers(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "modifiers")) return false;
    boolean r;
    Marker m = enter_section_(b, l, _NONE_, MODIFIERS, "<modifiers>");
    r = modifiers_0(b, l + 1);
    while (r) {
      int c = current_position_(b);
      if (!modifiers_0(b, l + 1)) break;
      if (!empty_element_parsed_guard_(b, "modifiers", c)) break;
    }
    exit_section_(b, l, m, r, false, null);
    return r;
  }

  // (SPEC_PUBLIC | SPEC_PROTECTED | pure | instance | helper | nullable | java_modifier) SEMICOLON* AT_SIGN*
  private static boolean modifiers_0(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "modifiers_0")) return false;
    boolean r;
    Marker m = enter_section_(b);
    r = modifiers_0_0(b, l + 1);
    r = r && modifiers_0_1(b, l + 1);
    r = r && modifiers_0_2(b, l + 1);
    exit_section_(b, m, null, r);
    return r;
  }

  // SPEC_PUBLIC | SPEC_PROTECTED | pure | instance | helper | nullable | java_modifier
  private static boolean modifiers_0_0(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "modifiers_0_0")) return false;
    boolean r;
    r = consumeToken(b, SPEC_PUBLIC);
    if (!r) r = consumeToken(b, SPEC_PROTECTED);
    if (!r) r = consumeToken(b, PURE);
    if (!r) r = consumeToken(b, INSTANCE);
    if (!r) r = consumeToken(b, HELPER);
    if (!r) r = consumeToken(b, NULLABLE);
    if (!r) r = java_modifier(b, l + 1);
    return r;
  }

  // SEMICOLON*
  private static boolean modifiers_0_1(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "modifiers_0_1")) return false;
    while (true) {
      int c = current_position_(b);
      if (!consumeToken(b, SEMICOLON)) break;
      if (!empty_element_parsed_guard_(b, "modifiers_0_1", c)) break;
    }
    return true;
  }

  // AT_SIGN*
  private static boolean modifiers_0_2(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "modifiers_0_2")) return false;
    while (true) {
      int c = current_position_(b);
      if (!consumeToken(b, AT_SIGN)) break;
      if (!empty_element_parsed_guard_(b, "modifiers_0_2", c)) break;
    }
    return true;
  }

  /* ********************************************************** */
  // NOT_SPECIFIED | java_expr
  static boolean pred_or_not(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "pred_or_not")) return false;
    boolean r;
    r = consumeToken(b, NOT_SPECIFIED);
    if (!r) r = java_expr(b, l + 1);
    return r;
  }

  /* ********************************************************** */
  // IDENT (DOT IDENT)*
  public static boolean reference_type(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "reference_type")) return false;
    if (!nextTokenIs(b, IDENT)) return false;
    boolean r;
    Marker m = enter_section_(b);
    r = consumeToken(b, IDENT);
    r = r && reference_type_1(b, l + 1);
    exit_section_(b, m, REFERENCE_TYPE, r);
    return r;
  }

  // (DOT IDENT)*
  private static boolean reference_type_1(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "reference_type_1")) return false;
    while (true) {
      int c = current_position_(b);
      if (!reference_type_1_0(b, l + 1)) break;
      if (!empty_element_parsed_guard_(b, "reference_type_1", c)) break;
    }
    return true;
  }

  // DOT IDENT
  private static boolean reference_type_1_0(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "reference_type_1_0")) return false;
    boolean r;
    Marker m = enter_section_(b);
    r = consumeTokens(b, 0, DOT, IDENT);
    exit_section_(b, m, null, r);
    return r;
  }

  /* ********************************************************** */
  // AT_SIGN* (requires|pre) pred_or_not SEMICOLON+
  public static boolean requires_clause(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "requires_clause")) return false;
    boolean r, p;
    Marker m = enter_section_(b, l, _NONE_, REQUIRES_CLAUSE, "<requires clause>");
    r = requires_clause_0(b, l + 1);
    r = r && requires_clause_1(b, l + 1);
    r = r && pred_or_not(b, l + 1);
    p = r; // pin = pred_or_not
    r = r && requires_clause_3(b, l + 1);
    exit_section_(b, l, m, r, p, null);
    return r || p;
  }

  // AT_SIGN*
  private static boolean requires_clause_0(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "requires_clause_0")) return false;
    while (true) {
      int c = current_position_(b);
      if (!consumeToken(b, AT_SIGN)) break;
      if (!empty_element_parsed_guard_(b, "requires_clause_0", c)) break;
    }
    return true;
  }

  // requires|pre
  private static boolean requires_clause_1(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "requires_clause_1")) return false;
    boolean r;
    r = consumeToken(b, REQUIRES);
    if (!r) r = consumeToken(b, PRE);
    return r;
  }

  // SEMICOLON+
  private static boolean requires_clause_3(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "requires_clause_3")) return false;
    boolean r;
    Marker m = enter_section_(b);
    r = consumeToken(b, SEMICOLON);
    while (r) {
      int c = current_position_(b);
      if (!consumeToken(b, SEMICOLON)) break;
      if (!empty_element_parsed_guard_(b, "requires_clause_3", c)) break;
    }
    exit_section_(b, m, null, r);
    return r;
  }

  /* ********************************************************** */
  // signals L_PAREN reference_type IDENT? R_PAREN pred_or_not? SEMICOLON+
  public static boolean signals_clause(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "signals_clause")) return false;
    if (!nextTokenIs(b, SIGNALS)) return false;
    boolean r;
    Marker m = enter_section_(b);
    r = consumeTokens(b, 0, SIGNALS, L_PAREN);
    r = r && reference_type(b, l + 1);
    r = r && signals_clause_3(b, l + 1);
    r = r && consumeToken(b, R_PAREN);
    r = r && signals_clause_5(b, l + 1);
    r = r && signals_clause_6(b, l + 1);
    exit_section_(b, m, SIGNALS_CLAUSE, r);
    return r;
  }

  // IDENT?
  private static boolean signals_clause_3(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "signals_clause_3")) return false;
    consumeToken(b, IDENT);
    return true;
  }

  // pred_or_not?
  private static boolean signals_clause_5(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "signals_clause_5")) return false;
    pred_or_not(b, l + 1);
    return true;
  }

  // SEMICOLON+
  private static boolean signals_clause_6(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "signals_clause_6")) return false;
    boolean r;
    Marker m = enter_section_(b);
    r = consumeToken(b, SEMICOLON);
    while (r) {
      int c = current_position_(b);
      if (!consumeToken(b, SEMICOLON)) break;
      if (!empty_element_parsed_guard_(b, "signals_clause_6", c)) break;
    }
    exit_section_(b, m, null, r);
    return r;
  }

  /* ********************************************************** */
  // SIGNALS_ONLY reference_type (COMMA reference_type)* SEMICOLON+
  public static boolean signals_only_clause(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "signals_only_clause")) return false;
    if (!nextTokenIs(b, SIGNALS_ONLY)) return false;
    boolean r;
    Marker m = enter_section_(b);
    r = consumeToken(b, SIGNALS_ONLY);
    r = r && reference_type(b, l + 1);
    r = r && signals_only_clause_2(b, l + 1);
    r = r && signals_only_clause_3(b, l + 1);
    exit_section_(b, m, SIGNALS_ONLY_CLAUSE, r);
    return r;
  }

  // (COMMA reference_type)*
  private static boolean signals_only_clause_2(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "signals_only_clause_2")) return false;
    while (true) {
      int c = current_position_(b);
      if (!signals_only_clause_2_0(b, l + 1)) break;
      if (!empty_element_parsed_guard_(b, "signals_only_clause_2", c)) break;
    }
    return true;
  }

  // COMMA reference_type
  private static boolean signals_only_clause_2_0(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "signals_only_clause_2_0")) return false;
    boolean r;
    Marker m = enter_section_(b);
    r = consumeToken(b, COMMA);
    r = r && reference_type(b, l + 1);
    exit_section_(b, m, null, r);
    return r;
  }

  // SEMICOLON+
  private static boolean signals_only_clause_3(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "signals_only_clause_3")) return false;
    boolean r;
    Marker m = enter_section_(b);
    r = consumeToken(b, SEMICOLON);
    while (r) {
      int c = current_position_(b);
      if (!consumeToken(b, SEMICOLON)) break;
      if (!empty_element_parsed_guard_(b, "signals_only_clause_3", c)) break;
    }
    exit_section_(b, m, null, r);
    return r;
  }

  /* ********************************************************** */
  // (AT_SIGN* (ensures_clause | signals_clause | signals_only_clause | assignable_clause))+
  public static boolean spec_body(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "spec_body")) return false;
    boolean r;
    Marker m = enter_section_(b, l, _NONE_, SPEC_BODY, "<spec body>");
    r = spec_body_0(b, l + 1);
    while (r) {
      int c = current_position_(b);
      if (!spec_body_0(b, l + 1)) break;
      if (!empty_element_parsed_guard_(b, "spec_body", c)) break;
    }
    exit_section_(b, l, m, r, false, null);
    return r;
  }

  // AT_SIGN* (ensures_clause | signals_clause | signals_only_clause | assignable_clause)
  private static boolean spec_body_0(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "spec_body_0")) return false;
    boolean r;
    Marker m = enter_section_(b);
    r = spec_body_0_0(b, l + 1);
    r = r && spec_body_0_1(b, l + 1);
    exit_section_(b, m, null, r);
    return r;
  }

  // AT_SIGN*
  private static boolean spec_body_0_0(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "spec_body_0_0")) return false;
    while (true) {
      int c = current_position_(b);
      if (!consumeToken(b, AT_SIGN)) break;
      if (!empty_element_parsed_guard_(b, "spec_body_0_0", c)) break;
    }
    return true;
  }

  // ensures_clause | signals_clause | signals_only_clause | assignable_clause
  private static boolean spec_body_0_1(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "spec_body_0_1")) return false;
    boolean r;
    r = ensures_clause(b, l + 1);
    if (!r) r = signals_clause(b, l + 1);
    if (!r) r = signals_only_clause(b, l + 1);
    if (!r) r = assignable_clause(b, l + 1);
    return r;
  }

  /* ********************************************************** */
  // requires_clause+ spec_body? | spec_body
  static boolean spec_case(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "spec_case")) return false;
    boolean r;
    Marker m = enter_section_(b);
    r = spec_case_0(b, l + 1);
    if (!r) r = spec_body(b, l + 1);
    exit_section_(b, m, null, r);
    return r;
  }

  // requires_clause+ spec_body?
  private static boolean spec_case_0(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "spec_case_0")) return false;
    boolean r;
    Marker m = enter_section_(b);
    r = spec_case_0_0(b, l + 1);
    r = r && spec_case_0_1(b, l + 1);
    exit_section_(b, m, null, r);
    return r;
  }

  // requires_clause+
  private static boolean spec_case_0_0(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "spec_case_0_0")) return false;
    boolean r;
    Marker m = enter_section_(b);
    r = requires_clause(b, l + 1);
    while (r) {
      int c = current_position_(b);
      if (!requires_clause(b, l + 1)) break;
      if (!empty_element_parsed_guard_(b, "spec_case_0_0", c)) break;
    }
    exit_section_(b, m, null, r);
    return r;
  }

  // spec_body?
  private static boolean spec_case_0_1(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "spec_case_0_1")) return false;
    spec_body(b, l + 1);
    return true;
  }

  /* ********************************************************** */
  // store_ref_name store_ref_name_suffix*
  public static boolean store_ref(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "store_ref")) return false;
    boolean r;
    Marker m = enter_section_(b, l, _NONE_, STORE_REF, "<name>");
    r = store_ref_name(b, l + 1);
    r = r && store_ref_1(b, l + 1);
    exit_section_(b, l, m, r, false, null);
    return r;
  }

  // store_ref_name_suffix*
  private static boolean store_ref_1(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "store_ref_1")) return false;
    while (true) {
      int c = current_position_(b);
      if (!store_ref_name_suffix(b, l + 1)) break;
      if (!empty_element_parsed_guard_(b, "store_ref_1", c)) break;
    }
    return true;
  }

  /* ********************************************************** */
  // NOTHING | EVERYTHING | NOT_SPECIFIED
  public static boolean store_ref_keyword(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "store_ref_keyword")) return false;
    boolean r;
    Marker m = enter_section_(b, l, _NONE_, STORE_REF_KEYWORD, "<\\nothing, \\everything, \\not_specified>");
    r = consumeToken(b, NOTHING);
    if (!r) r = consumeToken(b, EVERYTHING);
    if (!r) r = consumeToken(b, NOT_SPECIFIED);
    exit_section_(b, l, m, r, false, null);
    return r;
  }

  /* ********************************************************** */
  // store_ref_keyword | store_ref (COMMA store_ref)*
  static boolean store_ref_list(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "store_ref_list")) return false;
    boolean r;
    Marker m = enter_section_(b, l, _NONE_, null, "<list of references>");
    r = store_ref_keyword(b, l + 1);
    if (!r) r = store_ref_list_1(b, l + 1);
    exit_section_(b, l, m, r, false, null);
    return r;
  }

  // store_ref (COMMA store_ref)*
  private static boolean store_ref_list_1(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "store_ref_list_1")) return false;
    boolean r;
    Marker m = enter_section_(b);
    r = store_ref(b, l + 1);
    r = r && store_ref_list_1_1(b, l + 1);
    exit_section_(b, m, null, r);
    return r;
  }

  // (COMMA store_ref)*
  private static boolean store_ref_list_1_1(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "store_ref_list_1_1")) return false;
    while (true) {
      int c = current_position_(b);
      if (!store_ref_list_1_1_0(b, l + 1)) break;
      if (!empty_element_parsed_guard_(b, "store_ref_list_1_1", c)) break;
    }
    return true;
  }

  // COMMA store_ref
  private static boolean store_ref_list_1_1_0(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "store_ref_list_1_1_0")) return false;
    boolean r;
    Marker m = enter_section_(b);
    r = consumeToken(b, COMMA);
    r = r && store_ref(b, l + 1);
    exit_section_(b, m, null, r);
    return r;
  }

  /* ********************************************************** */
  // this | super | IDENT
  static boolean store_ref_name(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "store_ref_name")) return false;
    boolean r;
    r = consumeToken(b, THIS);
    if (!r) r = consumeToken(b, SUPER);
    if (!r) r = consumeToken(b, IDENT);
    return r;
  }

  /* ********************************************************** */
  // (DOT this) | (DOT IDENT) | (DOT STAR) | (L_SQ_BRAC STAR R_SQ_BRAC)
  static boolean store_ref_name_suffix(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "store_ref_name_suffix")) return false;
    if (!nextTokenIs(b, "", DOT, L_SQ_BRAC)) return false;
    boolean r;
    Marker m = enter_section_(b);
    r = store_ref_name_suffix_0(b, l + 1);
    if (!r) r = store_ref_name_suffix_1(b, l + 1);
    if (!r) r = store_ref_name_suffix_2(b, l + 1);
    if (!r) r = store_ref_name_suffix_3(b, l + 1);
    exit_section_(b, m, null, r);
    return r;
  }

  // DOT this
  private static boolean store_ref_name_suffix_0(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "store_ref_name_suffix_0")) return false;
    boolean r;
    Marker m = enter_section_(b);
    r = consumeTokens(b, 0, DOT, THIS);
    exit_section_(b, m, null, r);
    return r;
  }

  // DOT IDENT
  private static boolean store_ref_name_suffix_1(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "store_ref_name_suffix_1")) return false;
    boolean r;
    Marker m = enter_section_(b);
    r = consumeTokens(b, 0, DOT, IDENT);
    exit_section_(b, m, null, r);
    return r;
  }

  // DOT STAR
  private static boolean store_ref_name_suffix_2(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "store_ref_name_suffix_2")) return false;
    boolean r;
    Marker m = enter_section_(b);
    r = consumeTokens(b, 0, DOT, STAR);
    exit_section_(b, m, null, r);
    return r;
  }

  // L_SQ_BRAC STAR R_SQ_BRAC
  private static boolean store_ref_name_suffix_3(PsiBuilder b, int l) {
    if (!recursion_guard_(b, l, "store_ref_name_suffix_3")) return false;
    boolean r;
    Marker m = enter_section_(b);
    r = consumeTokens(b, 0, L_SQ_BRAC, STAR, R_SQ_BRAC);
    exit_section_(b, m, null, r);
    return r;
  }

}
