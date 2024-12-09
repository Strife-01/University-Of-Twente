package nl.utwente.jmlplugin.psi;

import com.intellij.psi.JavaTokenType;
import com.intellij.psi.TokenType;
import com.intellij.psi.tree.TokenSet;

import static nl.utwente.jmlplugin.psi.JMLTypes.*;

/**
 * Various token sets that might prove useful, kept here for reuse purposes.
 */
public class JMLTokenSet {
    // used for both annotators and syntax highlighting

    public static final TokenSet methodSpecCaseKeywords = TokenSet.create(
            REQUIRES, PRE, ENSURES, POST, SIGNALS, SIGNALS_ONLY, ASSIGNABLE, MODIFIABLE, MODIFIES
    );

    public static final TokenSet allModifiers = TokenSet.create(
            SPEC_PUBLIC, SPEC_PROTECTED, PURE, INSTANCE, HELPER, NULLABLE,
            PUBLIC, PRIVATE, PROTECTED, STATIC
    );

    public static final TokenSet visibilityModifiers = TokenSet.create(PUBLIC, PROTECTED, PRIVATE);

    public static final TokenSet specVisibilityModifiers = TokenSet.create(SPEC_PUBLIC, SPEC_PROTECTED);

    // used for annotators
    public static final TokenSet classModifiers = TokenSet.orSet(specVisibilityModifiers, TokenSet.create(PURE));

    public static final TokenSet invariantModifiers = TokenSet.orSet(visibilityModifiers, TokenSet.create(INSTANCE, STATIC));

    public static final TokenSet fieldModifiers = TokenSet.orSet(
            specVisibilityModifiers, TokenSet.create(NULLABLE, INSTANCE));

    public static final TokenSet methodDeclModifiers = TokenSet.orSet(
            specVisibilityModifiers, TokenSet.create(PURE, NULLABLE, HELPER));

    public static final TokenSet nullable = TokenSet.create(NULLABLE);

    public static final TokenSet also = TokenSet.create(ALSO);

    public static final TokenSet javaKeywords = TokenSet.create(THIS, SUPER);

    public static final TokenSet generalJMLKeywordsInJava = TokenSet.create(NOT_SPECIFIED, OLD, TYPE_OF, TYPE_CAPS, ELEM_TYPE, TYPE, NON_NULL_ELEMENTS);

    // used for lexers / parsers
    public static final TokenSet keywordsBeforeJavaExpr = TokenSet.create(
            REQUIRES, PRE, ENSURES, POST, MAINTAINING, LOOPINVARIANT, ASSUME, ASSERT, INVARIANT
    );

    public static final TokenSet codeBlockKeywords = TokenSet.create(ASSERT, ASSUME, MAINTAINING, LOOPINVARIANT);

    public static final TokenSet commentsAndWhitespace = TokenSet.create(INFORMAL_DESCRIPTION, TokenType.WHITE_SPACE);

    public static final TokenSet skipAfterJavaExpr = TokenSet.orSet(TokenSet.create(AT_SIGN), commentsAndWhitespace);

    public static final TokenSet quantifiers = TokenSet.create(FORALL, EXISTS, NUM_OF, MAX, MIN, SUM, PRODUCT);

    public static final TokenSet result = TokenSet.create(RESULT);

    public static final TokenSet old = TokenSet.create(OLD);

    public static final TokenSet assignableJavaKeywords = TokenSet.create(NOTHING, EVERYTHING);

    public static final TokenSet backslashKeywordsInJavaExpr = TokenSet.orSet(quantifiers,
            TokenSet.create(RESULT, OLD, TYPE_OF, ELEM_TYPE, TYPE, TYPE_CAPS, NON_NULL_ELEMENTS));

    public static final TokenSet allOuterKeywords = TokenSet.orSet(methodSpecCaseKeywords, allModifiers,
            TokenSet.create(INVARIANT, MAINTAINING, LOOPINVARIANT, ASSUME, ASSERT, ALSO));

    // used to check for keywords that have rules in the form of \tokentype(java_expr),
    // does not contain \type() because that one does not take an expression
    public static final TokenSet parenthesesAroundJavaTokenSet =
            TokenSet.create(JMLTypes.OLD, JMLTypes.TYPE_OF, JMLTypes.ELEM_TYPE,
                    JMLTypes.NON_NULL_ELEMENTS);

    public static final TokenSet javaPrimitives = TokenSet.create(
            JavaTokenType.INT_KEYWORD, JavaTokenType.BOOLEAN_KEYWORD, JavaTokenType.CHAR_KEYWORD,
            JavaTokenType.FLOAT_KEYWORD, JavaTokenType.DOUBLE_KEYWORD, JavaTokenType.BYTE_KEYWORD,
            JavaTokenType.SHORT_KEYWORD, JavaTokenType.LONG_KEYWORD, JavaTokenType.VOID_KEYWORD);

    public static final TokenSet logicalOperators = TokenSet.create(LOGICAL_IMPL, LOGICAL_EQ, LOGICAL_IMPL_REV, LOGICAL_NOT_EQ);

    // used for syntax highlighting
    public static final TokenSet backslashKeywords = TokenSet.orSet(TokenSet.create(NOT_SPECIFIED, NOTHING, EVERYTHING, INTO), backslashKeywordsInJavaExpr);

    public static final TokenSet punctuation = TokenSet.create(JavaTokenType.SEMICOLON, SEMICOLON, COMMA, DOT, COLON);

    public static final TokenSet grouping = TokenSet.create(L_PAREN, R_PAREN, L_SQ_BRAC, R_SQ_BRAC);
}
