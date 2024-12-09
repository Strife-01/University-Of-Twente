package nl.utwente.jmlplugin.parser;


import com.intellij.lang.PsiBuilder;
import com.intellij.lang.java.JavaLanguage;
import com.intellij.lang.parser.GeneratedParserUtilBase;
import com.intellij.psi.JavaTokenType;
import com.intellij.psi.tree.IElementType;
import nl.utwente.jmlplugin.JMLLanguage;
import nl.utwente.jmlplugin.psi.JMLTokenSet;
import nl.utwente.jmlplugin.psi.JMLTokenType;
import nl.utwente.jmlplugin.psi.JMLTypes;

import java.util.HashMap;
import java.util.Map;

/**
 * Custom parser section for allowing the embedding of Java expressions in JML parse trees.
 */
public class JMLJavaParser extends GeneratedParserUtilBase {

    /**
     * used to convert tokens to their corresponding rules
     */
    private static final Map<IElementType, IElementType> tokenTypeToRule = new HashMap<>();
    /**
     * used to check for rules in the form of \tokentype( java_expr )
     */
    private static final IElementType parenthesesAroundJava = new IElementType("parentheses around java", JMLLanguage.INSTANCE);

    static {
        tokenTypeToRule.put(JMLTypes.OLD, JMLTypes.OLD_EXPR);
        tokenTypeToRule.put(JMLTypes.TYPE_OF, JMLTypes.TYPE_OF_EXPR);
        tokenTypeToRule.put(JMLTypes.ELEM_TYPE, JMLTypes.ELEM_TYPE_EXPR);
        tokenTypeToRule.put(JMLTypes.NON_NULL_ELEMENTS, JMLTypes.NON_NULL_ELEMENTS_EXPR);
    }

    /**
     * The root for parsing java expressions in JML
     *
     * @param builder the PSI tree builder
     * @param level   the level in the tree
     * @return true if it could be parsed
     */
    public static boolean parseJavaExpression(PsiBuilder builder, int level) {
        PsiBuilder.Marker javaMarker = enter_section_(builder, level + 1, _NONE_, JMLTypes.INNER_JAVA_EXPR, JMLTypes.INNER_JAVA_EXPR.toString());
        boolean correct = parseJavaExprRecursively(builder, level + 2, null, true);
        exit_section_(builder, level + 1, javaMarker, correct, false, null);
        return correct;
    }

    /**
     * Checks that the tokens got consumed by the parser
     *
     * @param builder the PSI tree builder
     * @param pos     the position of the builder
     * @return true if at least 1 token got consumed by the parser
     */
    private static boolean checkNotEmpty(PsiBuilder builder, int pos) {
        if (current_position_(builder) == pos) {
            // check for next token to give the error message maker the illusion that an error must be thrown
            nextTokenIs(builder, JMLTypes.JAVA_EXPR);
            return false;
        }
        return true;
    }

    /**
     * Recursively parses java expressions in JML
     *
     * @param builder         the PSI tree builder
     * @param level           the level in the tree
     * @param parent          the parent element
     * @param contentRequired whether it is required to parse at least 1 token
     * @return true if it could be parsed
     */
    private static boolean parseJavaExprRecursively(PsiBuilder builder, int level, IElementType parent, boolean contentRequired) {
        if (!recursion_guard_(builder, level, "recursive java expression")) return false;
        boolean correct = true;
        int openedParensCount = 0;
        int openedBracesCount = 0;
        int pos = current_position_(builder);
        IElementType type = builder.getTokenType();
        while (correct && !builder.eof() && type != null && (type.getLanguage() == JavaLanguage.INSTANCE
                || JMLTokenSet.backslashKeywordsInJavaExpr.contains(type) || JMLTokenSet.logicalOperators.contains(type))) {
            // check if there is a JML expression

            if (type == JMLTypes.TYPE) {
                correct = parseBackslashType(builder, level);
                // continue otherwise the parenthesis will be counted below
                type = builder.getTokenType();
                continue;
            } else if (JMLTokenSet.parenthesesAroundJavaTokenSet.contains(type)) {
                correct = parseBackslashKeywordParenthesesAroundJava(builder, level, tokenTypeToRule.get(type));
                // continue otherwise the parenthesis will be counted below
                type = builder.getTokenType();
                continue;
            } else if (JMLTokenSet.quantifiers.contains(builder.lookAhead(1))) {
                correct = parseQuantifiedExpr(builder, level);
                // continue otherwise the parenthesis will be counted below
                type = builder.getTokenType();
                continue;
            } else if (JMLTokenSet.quantifiers.contains(builder.getTokenType())) {
                // it does not start with a parenthesis, so pretend to parse a token with the name
                // LPAREN_BEFORE_QUANTIFIER, so we can catch the error message containing it in the syntaxAnnotator
                nextTokenIs(builder, new IElementType("NO_LPAREN_BEFORE_QUANTIFIER", JMLLanguage.INSTANCE));
                correct = false;
            }

            // checks to see if we need to stop parsing for now
            if (openedParensCount == 0 && openedBracesCount == 0) {
                if (parent == parenthesesAroundJava && type == JavaTokenType.RPARENTH) {
                    if (contentRequired) correct = checkNotEmpty(builder, pos);
                    return correct;
                } else if (parent == JMLTypes.Q_PREDICATE && (builder.eof() || type == JavaTokenType.SEMICOLON || type == JavaTokenType.RPARENTH)) {
                    return true;
                } else if (parent == JMLTypes.Q_SPEC_EXPR && (builder.eof() || type == JavaTokenType.RPARENTH)) {
                    if (contentRequired) correct = checkNotEmpty(builder, pos);
                    return correct;
                }
            }

            // count parenthesis and braces
            // we count these in case the expression contains a lambda or function call
            if (type == JavaTokenType.RPARENTH) {
                openedParensCount--;
            } else if (type == JavaTokenType.LPARENTH) {
                openedParensCount++;
            } else if (type == JavaTokenType.LBRACE) {
                openedBracesCount++;
            } else if (type == JavaTokenType.RBRACE) {
                openedBracesCount--;
            }
            // update the variables for the next iteration of the loop
            builder.advanceLexer();
            type = builder.getTokenType();
        }
        if (correct && contentRequired) correct = checkNotEmpty(builder, pos);
        return correct;
    }

    /**
     * Parses JML expressions of the form: \type(typename)
     *
     * @param builder the PSI tree builder
     * @param level   the level in the tree
     * @return true if it could be parsed
     */
    private static boolean parseBackslashType(PsiBuilder builder, int level) {
        PsiBuilder.Marker marker = enter_section_(builder, level, _NONE_, JMLTypes.TYPE_EXPR, JMLTypes.TYPE_EXPR.toString());
        // advance past the keyword
        builder.advanceLexer();
        boolean correct = consumeToken(builder, JavaTokenType.LPARENTH);
        correct = correct && parseTypeName(builder, level);
        correct = correct && consumeToken(builder, JavaTokenType.RPARENTH);
        exit_section_(builder, level, marker, correct, false, null);
        return correct;
    }

    /**
     * Parses JML expressions of the form: \keyword(java_expr)
     *
     * @param builder the PSI tree builder
     * @param level   the level in the tree
     * @param rule    the rule the parsed content should be wrapped in
     * @return true if it could be parsed
     */
    private static boolean parseBackslashKeywordParenthesesAroundJava(PsiBuilder builder, int level, IElementType rule) {
        PsiBuilder.Marker marker = enter_section_(builder, level, _NONE_, rule, rule.toString());
        // advance past the keyword
        builder.advanceLexer();
        boolean correct = consumeToken(builder, JavaTokenType.LPARENTH);
        // parse a java expression
        if (correct) {
            PsiBuilder.Marker javaMarker = enter_section_(builder, level, _NONE_, JMLTypes.INNER_JAVA_EXPR, JMLTypes.INNER_JAVA_EXPR.toString());
            while (true) {
                correct = parseJavaExprRecursively(builder, level + 1, parenthesesAroundJava, true);
                if (correct && !builder.eof() && builder.getTokenType() != JavaTokenType.RPARENTH
                        && !(builder.getTokenType() == JMLTypes.SEMICOLON && (builder.lookAhead(1) == null || builder.lookAhead(1) instanceof JMLTokenType))) {
                    builder.advanceLexer();
                } else {
                    break;
                }
            }
            nextTokenIs(builder, JavaTokenType.RPARENTH);
            exit_section_(builder, level, javaMarker, correct, false, null);
        }
        correct = correct && consumeToken(builder, JavaTokenType.RPARENTH);
        exit_section_(builder, level, marker, correct, false, null);
        return correct;
    }


    /**
     * Parses quantifiers, which are of the form: (\keyword var_decl ';' (predicate? ';')? spec_expr)
     *
     * @param builder the PSI tree builder
     * @param level   the level in the tree
     * @return true if it could be parsed
     */
    private static boolean parseQuantifiedExpr(PsiBuilder builder, int level) {
        PsiBuilder.Marker marker = enter_section_(builder, level, _NONE_, JMLTypes.QUANTIFIED_EXPR, JMLTypes.QUANTIFIED_EXPR.toString());
        boolean correct = false;
        // if it does not start with a parenthesis, then pretend to parse a token with the name
        // LPAREN_BEFORE_QUANTIFIER, so we can catch the error message containing it in the syntaxAnnotator
        if (builder.getTokenType() != JavaTokenType.LPARENTH) {
            // advance past the keyword
            builder.advanceLexer();
            nextTokenIs(builder, new IElementType("NO_LPAREN_BEFORE_QUANTIFIER", JMLLanguage.INSTANCE));
        } else {
            // advance past the L_PARENTH
            builder.advanceLexer();
            // advance past the keyword
            builder.advanceLexer();
            correct = true;
        }
        correct = correct && parseQVarDecl(builder, level + 1);
        // consume the in-between semicolon, only use 1 consumeToken(), otherwise it lists semicolon
        // twice in the error message, once for JML ; and once for Java ;
        if (correct) {
            if (builder.getTokenType() == JMLTypes.SEMICOLON) {
                consumeToken(builder, JMLTypes.SEMICOLON);
            } else {
                correct = consumeToken(builder, JavaTokenType.SEMICOLON);
            }
        }
        // could be the predicate or spec expression
        correct = correct && parseQPredicateOrSpecExpr(builder, level + 1);
        // if there is another semicolon then we have a predicate and a spec_expression
        if (correct && (builder.getTokenType() == JMLTypes.SEMICOLON || builder.getTokenType() == JavaTokenType.SEMICOLON)) {
            builder.advanceLexer();
            correct = parseQSpecExpr(builder, level + 1);
        }
        correct = correct && consumeToken(builder, JavaTokenType.RPARENTH);
        exit_section_(builder, level, marker, correct, false, null);
        return correct;
    }


    /**
     * Parses variable declarations in quantifiers of the form: typename identifier+
     *
     * @param builder the PSI tree builder
     * @param level   the level in the tree
     * @return true if it could be parsed
     */
    private static boolean parseQVarDecl(PsiBuilder builder, int level) {
        PsiBuilder.Marker marker = enter_section_(builder, level, _NONE_, JMLTypes.Q_VAR_DECL, JMLTypes.Q_VAR_DECL.toString());
        // optional nullable
        consumeToken(builder, JMLTypes.NULLABLE);
        // parse the type of the variable declaration
        boolean correct = parseTypeName(builder, level + 1);
        // parse the identifiers
        correct = correct && parseQVarDeclIdentifiers(builder, level + 1);
        exit_section_(builder, level, marker, correct, false, null);
        return correct;
    }


    /**
     * Parses the type in the variable declarations in quantifiers of the form: (int | boolean | char | float | double | IDENTIFIER | byte | short | long | \TYPE) ([])*
     *
     * @param builder the PSI tree builder
     * @param level   the level in the tree
     * @return true if it could be parsed
     */
    private static boolean parseTypeName(PsiBuilder builder, int level) {
        PsiBuilder.Marker typeMarker = enter_section_(builder, level, _NONE_, JMLTypes.TYPE_NAME, "type name");
        boolean correct = consumeToken(builder, JavaTokenType.INT_KEYWORD);
        if (!correct) correct = consumeToken(builder, JavaTokenType.BOOLEAN_KEYWORD);
        if (!correct) correct = consumeToken(builder, JavaTokenType.CHAR_KEYWORD);
        if (!correct) correct = consumeToken(builder, JavaTokenType.FLOAT_KEYWORD);
        if (!correct) correct = consumeToken(builder, JavaTokenType.DOUBLE_KEYWORD);
        if (!correct) correct = consumeToken(builder, JavaTokenType.IDENTIFIER);
        if (!correct) correct = consumeToken(builder, JavaTokenType.BYTE_KEYWORD);
        if (!correct) correct = consumeToken(builder, JavaTokenType.SHORT_KEYWORD);
        if (!correct) correct = consumeToken(builder, JavaTokenType.LONG_KEYWORD);
        if (!correct) correct = consumeToken(builder, JMLTypes.TYPE_CAPS);
        correct = correct && optionalDims(builder);
        exit_section_(builder, level, typeMarker, correct, false, null);
        return correct;
    }


    /**
     * Parses opening and closing square braces of the form: ('[' ']')*
     *
     * @param builder the PSI tree builder
     * @return true if it could be parsed
     */
    private static boolean optionalDims(PsiBuilder builder) {
        while (true) {
            if (!consumeToken(builder, JavaTokenType.LBRACKET)) return true;
            if (!consumeToken(builder, JavaTokenType.RBRACKET)) {
                return false;
            }
        }
    }


    /**
     * Parses the variable names in the variable declarations in quantifiers of the form: identifier dims? (',' identifier dims?)*
     *
     * @param builder the PSI tree builder
     * @param level   the level in the tree
     * @return true if it could be parsed
     */
    @SuppressWarnings("LoopConditionNotUpdatedInsideLoop")
    private static boolean parseQVarDeclIdentifiers(PsiBuilder builder, int level) {
        PsiBuilder.Marker marker = enter_section_(builder, level, _NONE_, JMLTypes.Q_VAR_DECL_IDENTIFIER, "variable name");
        boolean correct = consumeToken(builder, JavaTokenType.IDENTIFIER);
        correct = correct && optionalDims(builder);
        exit_section_(builder, level, marker, correct, correct, null);
        while (correct) {
            // works because when no comma is consumed, the frame will have length 0
            // and when that is the case, no error will be thrown
            boolean correct2 = nextTokenIs(builder,JavaTokenType.COMMA);
            if (correct2) builder.advanceLexer();
            PsiBuilder.Marker marker2 = enter_section_(builder, level, _NONE_, JMLTypes.Q_VAR_DECL_IDENTIFIER, "variable name");
            correct2 = correct2 && consumeToken(builder, JavaTokenType.IDENTIFIER);
            correct2 = correct2 && optionalDims(builder);
            exit_section_(builder, level, marker2, correct2, false, null);
            if (!correct2) break;
        }
        return correct;
    }


    /**
     * Parses the predicate or spec expression in quantifiers of the form: java_expr [;)].
     * If it ends in ';', it is a predicate and if it ends in ')' it is a spec expression
     *
     * @param builder the PSI tree builder
     * @param level   the level in the tree
     * @return true if it could be parsed
     */
    private static boolean parseQPredicateOrSpecExpr(PsiBuilder builder, int level) {
        PsiBuilder.Marker marker = enter_section_(builder, level, _NONE_, "range condition or expression");
        boolean correct;
        int pos = current_position_(builder);
        // parse a java expression
        PsiBuilder.Marker innerJavaMarker = enter_section_(builder, level + 1, _NONE_, JMLTypes.INNER_JAVA_EXPR, JMLTypes.INNER_JAVA_EXPR.toString());
        correct = parseJavaExprRecursively(builder, level + 2, JMLTypes.Q_PREDICATE, false);
        exit_section_(builder, level + 1, innerJavaMarker, null, correct, correct, null);
        // found spec_expression
        if (nextTokenIs(builder, JavaTokenType.RPARENTH)) {
            // throw an error when nothing was parsed, we do it here instead of telling the java recursive parser,
            // because you can have an empty predicate
            if (current_position_(builder) <= pos) {
                // check for next token to give the error message maker the illusion that an error must be thrown
                nextTokenIs(builder, JMLTypes.Q_SPEC_EXPR);
                exit_section_(builder, level, marker, false, false, null);
                return false;
            }
            exit_section_(builder, level, marker, JMLTypes.Q_SPEC_EXPR, correct, correct, null);
            return correct;
            // don't use nextTokenIs() twice here, otherwise it will mention semicolon twice in the error message
            // once for JML ; and once for JAVA ;
        } else if (builder.getTokenType() == JMLTypes.SEMICOLON || nextTokenIs(builder, JavaTokenType.SEMICOLON)) {
            exit_section_(builder, level, marker, JMLTypes.Q_PREDICATE, correct, correct, null);
            return correct;
        }
        exit_section_(builder, level, marker, null, false, false, null);
        return false;
    }

    /**
     * Parses the spec expression in quantifiers of the form: java_expr [)]
     *
     * @param builder the PSI tree builder
     * @param level   the level in the tree
     * @return true if it could be parsed
     */
    private static boolean parseQSpecExpr(PsiBuilder builder, int level) {
        PsiBuilder.Marker marker = enter_section_(builder, level, _NONE_, JMLTypes.Q_SPEC_EXPR, "expression");
        boolean correct;
        // parse a java expression
        PsiBuilder.Marker innerJavaMarker = enter_section_(builder, level + 1, _NONE_, JMLTypes.INNER_JAVA_EXPR, JMLTypes.INNER_JAVA_EXPR.toString());
        correct = parseJavaExprRecursively(builder, level + 2, JMLTypes.Q_SPEC_EXPR, true);
        exit_section_(builder, level + 1, innerJavaMarker, JMLTypes.Q_SPEC_EXPR, correct, false, null);
        // next token should be ) to end the spec expression
        correct = correct && nextTokenIs(builder, JavaTokenType.RPARENTH);
        exit_section_(builder, level, marker, correct, false, null);
        return correct;
    }


}
