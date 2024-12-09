package nl.utwente.jmlplugin.lexer;

import com.intellij.lexer.*;
import com.intellij.psi.tree.IElementType;
import com.intellij.psi.tree.TokenSet;
import nl.utwente.jmlplugin.parser._JMLLexer;
import nl.utwente.jmlplugin.psi.JMLTokenSet;
import nl.utwente.jmlplugin.psi.JMLTypes;

import static nl.utwente.jmlplugin.psi.JMLTokenSet.commentsAndWhitespace;
import static nl.utwente.jmlplugin.psi.JMLTokenSet.skipAfterJavaExpr;

/**
 * Merges mixed JML-Java expressions under one token to simplify the Java parsing process.
 */

public class JMLMergingLexer extends MergingLexerAdapter {

    private final MergeFunction mergeFunction = new JMLMergeFunction();

    public JMLMergingLexer() {
        super(new FlexAdapter(new _JMLLexer(null)), TokenSet.EMPTY);
    }

    @Override
    public MergeFunction getMergeFunction() {
        return mergeFunction;
    }

    /**
     * Contains the merge function to be used in JMLMergingLexer
     */
    private static class JMLMergeFunction implements MergeFunction {

        private boolean merging = false;
        private boolean javaExprExpected = false;


        /**
         * Merges certain tokens together and returns the new element type for those merged tokens
         *
         * @param type          the type of the first token
         * @param originalLexer the lexer holding all tokens. Is one token ahead of {@code type}
         * @return the new element type for the merged tokens or a singular token
         */
        @Override
        public IElementType merge(IElementType type, Lexer originalLexer) {
            // merge until you see that the expression ended, assuming greedy matching
            LexerPosition startPos;

            while (merging) {
                // EOF and no end-marker found for the expression
                // (possible that ';' has not been typed by the user yet)
                if (type == null || originalLexer.getTokenType() == null) {
                    merging = false;
                    return JMLTypes.JAVA_EXPR_TOKEN;
                }
                // semicolon greedy matching
                if (originalLexer.getTokenType() == JMLTypes.SEMICOLON) {
                    // store the position of the semicolon
                    startPos = originalLexer.getCurrentPosition();
                    // get the next token after the semicolon
                    originalLexer.advance();
                    // skip whitespace, comments and at-signs
                    while (skipAfterJavaExpr.contains(originalLexer.getTokenType())) {
                        originalLexer.advance();
                    }
                    //end of expression so return java expression
                    if (originalLexer.getTokenType() == null || JMLTokenSet.allOuterKeywords.contains(originalLexer.getTokenType())) {
                        merging = false;
                        // restore to the position of the semicolon, because we do not want the
                        // semicolon and what comes after it in the resulting java expression token
                        originalLexer.restore(startPos);
                        return JMLTypes.JAVA_EXPR_TOKEN;
                    }
                } else if (JMLTokenSet.allOuterKeywords.contains(originalLexer.getTokenType())) {
                    // found a JML keyword such as ensures, so Java expression is over, but user forgot semicolon
                    merging = false;
                    return JMLTypes.JAVA_EXPR_TOKEN;
                } else {
                    originalLexer.advance();
                }
            }

            // found the token before the potential java expression
            if (javaExprExpected && type == JMLTypes.R_PAREN) {
                startPos = originalLexer.getCurrentPosition();
                // skip comments and whitespace
                while (commentsAndWhitespace.contains(originalLexer.getTokenType())) {
                    originalLexer.advance();
                }
                // check if there is a Java expression here
                if (originalLexer.getTokenType() != JMLTypes.SEMICOLON && originalLexer.getTokenType() != JMLTypes.NOT_SPECIFIED) {
                    merging = true;
                }
                javaExprExpected = false;
                originalLexer.restore(startPos);
            } else if (type == JMLTypes.SIGNALS) {
                // for signals clauses, the java expression is not immediately after it,
                // so have a separate marker "javaExprExpected" for that
                javaExprExpected = true;
                return type;
            } else if (JMLTokenSet.keywordsBeforeJavaExpr.contains(type)) {
                startPos = originalLexer.getCurrentPosition();
                // skip comments and whitespace
                while (commentsAndWhitespace.contains(originalLexer.getTokenType())) {
                    originalLexer.advance();
                }

                // check there is a java expression now and not \not_specified
                if (originalLexer.getTokenType() != JMLTypes.NOT_SPECIFIED && originalLexer.getTokenType() != JMLTypes.SEMICOLON) {
                    merging = true;
                }
                // restore to undo our lookahead
                originalLexer.restore(startPos);
            }
            return type;

        }
    }


}
