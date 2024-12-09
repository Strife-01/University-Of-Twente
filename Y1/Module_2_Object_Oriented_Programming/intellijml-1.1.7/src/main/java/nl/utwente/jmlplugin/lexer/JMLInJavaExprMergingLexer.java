package nl.utwente.jmlplugin.lexer;

import com.intellij.lexer.Lexer;
import com.intellij.lexer.MergeFunction;
import com.intellij.lexer.MergingLexerAdapter;
import com.intellij.psi.JavaTokenType;
import com.intellij.psi.TokenType;
import com.intellij.psi.tree.IElementType;
import com.intellij.psi.tree.TokenSet;
import nl.utwente.jmlplugin.psi.JMLTypes;

import java.util.HashMap;
import java.util.Map;

/**
 * Top level parser for JML. Merges JML inside Java expressions. Merges the \keywords from JML into a single token, because otherwise
 * JML views it as \ + keyword instead of \keyword. Also merges JML operators such as ==> and <==>
 */

public class JMLInJavaExprMergingLexer extends MergingLexerAdapter {
    private final MergeFunction mergeFunction = new JavaExprJMLKeywordMergeFunction();

    public JMLInJavaExprMergingLexer() {
        super(new JMLMultiLayerLexer(), TokenSet.EMPTY);
    }

    @Override
    public MergeFunction getMergeFunction() {
        return mergeFunction;
    }

    /**
     * Contains the merge function to be used in JMLInJavaExprMergingLexer
     */
    private static class JavaExprJMLKeywordMergeFunction implements MergeFunction {
        private static final Map<CharSequence, IElementType> textToToken = new HashMap<>();

        static {
            textToToken.put("result", JMLTypes.RESULT);
            textToToken.put("old", JMLTypes.OLD);
            textToToken.put("forall", JMLTypes.FORALL);
            textToToken.put("exists", JMLTypes.EXISTS);
            textToToken.put("max", JMLTypes.MAX);
            textToToken.put("min", JMLTypes.MIN);
            textToToken.put("num_of", JMLTypes.NUM_OF);
            textToToken.put("product", JMLTypes.PRODUCT);
            textToToken.put("sum", JMLTypes.SUM);
            textToToken.put("typeof", JMLTypes.TYPE_OF);
            textToToken.put("elemtype", JMLTypes.ELEM_TYPE);
            textToToken.put("type", JMLTypes.TYPE);
            textToToken.put("TYPE", JMLTypes.TYPE_CAPS);
            textToToken.put("nonnullelements", JMLTypes.NON_NULL_ELEMENTS);
        }

        private boolean checkBackslashKeyword = false;

        /**
         * Merges certain tokens together and returns the new element type for those merged tokens
         *
         * @param type          the type of the first token
         * @param originalLexer the lexer holding all tokens. Is one token ahead of {@code type}
         * @return the new element type for the merged tokens or a singular token
         */
        @Override
        public IElementType merge(IElementType type, Lexer originalLexer) {
            if (checkBackslashKeyword) {
                // we found a backslash, so check if JML keyword is after it
                IElementType result = type;
                if (originalLexer.getTokenType() == JavaTokenType.IDENTIFIER && textToToken.containsKey(originalLexer.getTokenText())) {
                    // found a JML keyword
                    result = textToToken.get(originalLexer.getTokenText());
                    originalLexer.advance();
                }
                checkBackslashKeyword = false;
                return result;
            } else {
                // check for a backslash
                if (originalLexer.getTokenType() == TokenType.BAD_CHARACTER && originalLexer.getTokenText().equals("\\")) {
                    checkBackslashKeyword = true;
                }
                // check for JML logical operators
                else if (type == JavaTokenType.LE /* <= */) {
                    if (originalLexer.getTokenType() == JavaTokenType.EQ /* = */) {
                        originalLexer.advance();
                        if (originalLexer.getTokenType() == JavaTokenType.GT /* > */) {
                            // <==>
                            originalLexer.advance();
                            return JMLTypes.LOGICAL_EQ;
                        } else {
                            // <==
                            return JMLTypes.LOGICAL_IMPL_REV;
                        }
                    } else if (originalLexer.getTokenType() == JavaTokenType.NE /* != */) {
                        originalLexer.advance();
                        if (originalLexer.getTokenType() == JavaTokenType.GT /* > */) {
                            // <=!=>
                            originalLexer.advance();
                            return JMLTypes.LOGICAL_NOT_EQ;
                        }
                        return TokenType.BAD_CHARACTER;
                    }
                } else if (type == JavaTokenType.EQEQ /* == */ && originalLexer.getTokenType() == JavaTokenType.GT /* > */) {
                    // ==>
                    originalLexer.advance();
                    return JMLTypes.LOGICAL_IMPL;
                }
            }
            return type;
        }


    }


}
