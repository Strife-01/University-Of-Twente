package nl.utwente.jmlplugin.completion;

import com.intellij.codeInsight.completion.*;
import com.intellij.codeInsight.lookup.LookupElementBuilder;
import com.intellij.lang.parser.GeneratedParserUtilBase;
import com.intellij.patterns.PsiElementPattern;
import com.intellij.psi.JavaTokenType;
import com.intellij.psi.PsiElement;
import com.intellij.psi.PsiFile;
import com.intellij.psi.PsiIdentifier;
import com.intellij.psi.tree.TokenSet;
import com.intellij.util.ProcessingContext;
import nl.utwente.jmlplugin.psi.JMLFile;
import nl.utwente.jmlplugin.psi.JMLTokenSet;
import nl.utwente.jmlplugin.psi.JMLTypes;
import nl.utwente.jmlplugin.psi.impl.JMLQPredicate;
import nl.utwente.jmlplugin.psi.impl.JMLQSpecExpr;
import org.jetbrains.annotations.NotNull;

import static com.intellij.patterns.PlatformPatterns.psiElement;

/**
 * Class that provides non-referential completion support. Essentially provides support for
 * autocompleting keywords in appropriate places based on IDE context.
 */

public class JMLCompletionContributor extends CompletionContributor {

    /**
     * Implements the completion functionality by extending the base class functionality
     * using the extend method.
     * <p>
     * Context is set by the method calls that are specified in this class as private methods,
     * in these methods Psi Tree patterns are constructed to be matched against for automatic completion
     * pop-up.
     * <p>
     * JMLCompletionProviders are the classes that are actually responsible for generating the suggested words
     * to the user.
     */

    public JMLCompletionContributor() {
        extend(CompletionType.BASIC, jmlStart(), JMLKeywordCompletionProvider.INSTANCE);
        extend(CompletionType.BASIC, jmlAtSignPostJavaExpr(), JMLKeywordCompletionProvider.INSTANCE);
        extend(CompletionType.BASIC, jmlPostJavaExpression(), JMLKeywordCompletionProvider.INSTANCE);
        extend(CompletionType.BASIC, backslashStart(), JMLJavaBackslashCompletionProvider.INSTANCE);
        extend(CompletionType.BASIC, backslashNoLaterExpression(), JMLJavaBackslashCompletionProvider.INSTANCE);
        extend(CompletionType.BASIC, javaJMLStoreRef(), JMLAssignableClauseCompletionProvider.INSTANCE);
        extend(CompletionType.BASIC, javaJMLStoreRefNoSemicolon(), JMLAssignableClauseCompletionProvider.INSTANCE);
        extend(CompletionType.BASIC, javaJMLReferenceType(), JMLJavaExceptionClassProvider.INSTANCE);
        extend(CompletionType.BASIC, javaJMLReferenceTypeNoSemicolon(), JMLJavaExceptionClassProvider.INSTANCE);
        extend(CompletionType.BASIC, javaJMLReferenceTypeNoSemicolonOnly(), JMLJavaExceptionClassProvider.INSTANCE);
        extend(CompletionType.BASIC, javaExpressionStart(), JMLJavaIdentifierCompletionProvider.INSTANCE);
        extend(CompletionType.BASIC, javaDotExpression(), JMLJavaDotCompletionProvider.INSTANCE);
        extend(CompletionType.BASIC, jmlQuantifiedSpecExpression(), JMLJavaIdentifierCompletionProvider.INSTANCE);
        extend(CompletionType.BASIC, jmlQuantifiedSpecDotExpression(), JMLJavaDotCompletionProvider.INSTANCE);
        extend(CompletionType.BASIC, quantifiedExpressionStart(), JMLJavaPrimitiveClassCompletion.INSTANCE);
        extend(CompletionType.BASIC, jmlQuantifiedConditionExpression(), JMLJavaIdentifierCompletionProvider.INSTANCE);
        extend(CompletionType.BASIC, jmlQuantifiedConditionDotExpression(), JMLJavaDotCompletionProvider.INSTANCE);
        //debug code, remove when done or uncomment if needed
        //extend(CompletionType.BASIC, psiElement(), debugPrint());
    }

    /**
     * @return PsiTree pattern for when \jmlkeyword is written inside of a Java+JML expression
     */

    private static PsiElementPattern.Capture<PsiIdentifier> backslashStart() {
        return psiElement(PsiIdentifier.class).withParent(GeneratedParserUtilBase.DummyBlock.class).afterLeaf("\\");
    }

    /**
     * @return PsiTree pattern for when \jmlkeyword is being written in a JML+Java expression and it is the last
     * expression in a multiline comment.
     */

    private static PsiElementPattern.Capture<PsiIdentifier> backslashNoLaterExpression() {
        return psiElement(PsiIdentifier.class).withParent(JMLFile.class).afterLeaf("\\");
    }

    /**
     * @return Psi Tree patterns for empty JML expression
     */

    private static PsiElementPattern.Capture<PsiElement> jmlStart() {
        return psiElement(JMLTypes.IDENT).withSuperParent(2, PsiFile.class);
    }

    /**
     * @return Psi tree pattern for completions after java expressions,
     * usually you would not need this, but our Java embedding into JML is a bit of
     * a hack, so this has to exist.
     */

    private static PsiElementPattern.Capture<PsiIdentifier> jmlPostJavaExpression() {
        return psiElement(PsiIdentifier.class)
                .withParent(psiElement(JMLTypes.INNER_JAVA_EXPR))
                .afterLeaf(";")
                .andNot(jmlQuantifiedSpecExpression())
                .andNot(jmlQuantifiedPredicate());
    }

    /**
     * Quantified expression predicate section so, e.g. in a sum we would be:
     * (\sum int i; HERE; i + 1);
     *
     * @return Quantified expression predicate section
     */

    private static PsiElementPattern.Capture<PsiIdentifier> jmlQuantifiedPredicate() {
        return psiElement(PsiIdentifier.class).withSuperParent(2, JMLQPredicate.class);
    }


    /**
     * @return Psi Tree pattern for java completions that come after a dot
     */

    private static PsiElementPattern.Capture<PsiIdentifier> javaDotExpression() {
        return psiElement(PsiIdentifier.class)
                .withParent(psiElement(JMLTypes.INNER_JAVA_EXPR))
                .afterLeaf(".");
    }

    /**
     * @return pattern for telling when you are in a java expression
     */

    private static PsiElementPattern.Capture<PsiIdentifier> javaExpressionStart() {
        return psiElement(PsiIdentifier.class).withParent(psiElement(JMLTypes.INNER_JAVA_EXPR))
                .andNot(jmlPostJavaExpression())
                .andNot(javaDotExpression())
                .andNot(jmlAtSignPostJavaExpr());
    }

    /**
     * @return pattern for jml keyword completion after a java expr with an @.
     */

    private static PsiElementPattern.Capture<PsiIdentifier> jmlAtSignPostJavaExpr() {
        return psiElement(PsiIdentifier.class)
                .withParent(psiElement(JMLTypes.INNER_JAVA_EXPR))
                .afterLeaf("@");
    }

    /**
     * @return pattern for completion of java variable/field completion in storeRef jml expression,
     * usually found in assignable.
     */

    private static PsiElementPattern.Capture<PsiElement> javaJMLStoreRef() {
        return psiElement(JMLTypes.IDENT)
                .withParent(psiElement(JMLTypes.STORE_REF));
    }

    /**
     * @return PsiTree pattern for when an assignable clause does not have a semicolon.
     */

    private static PsiElementPattern.Capture<PsiElement> javaJMLStoreRefNoSemicolon() {
        return psiElement(JMLTypes.IDENT).afterLeaf("assignable", "modifiable", "modifies");
    }

    /**
     * @return PsiTree pattern for JMLReferenceType completion, usually used to find where to complete
     * signals exception classes.
     */

    private static PsiElementPattern.Capture<PsiElement> javaJMLReferenceType() {
        return psiElement(JMLTypes.IDENT)
                .withParent(psiElement(JMLTypes.REFERENCE_TYPE));
    }

    /**
     * @return PsiTree pattern for Exception class name completions inside the parentheses of the signals clause.
     */

    private static PsiElementPattern.Capture<PsiElement> javaJMLReferenceTypeNoSemicolon() {
        return psiElement(JMLTypes.IDENT).afterSibling(psiElement(JMLTypes.L_PAREN).afterLeaf("signals"));
    }

    /**
     * @return PsiTree pattern for completion of Exception class at the start of the signals_only java expression part.
     */

    private static PsiElementPattern.Capture<PsiElement> javaJMLReferenceTypeNoSemicolonOnly() {
        return psiElement(JMLTypes.IDENT).afterLeaf("signals_only");
    }

    /**
     * @return PsiTreePattern for the first section of a quantified expression.
     */

    private static PsiElementPattern.Capture<PsiIdentifier> quantifiedExpressionStart() {
        return psiElement(PsiIdentifier.class)
                .withParent(JMLFile.class)
                .afterLeaf(getTokenSetOredTogether(JMLTokenSet.quantifiers));
    }

    /**
     * @return PsiTree for java identifier expressions in the last section of a quantified expression (after the loop variable declaration and loop condition)
     */

    private static PsiElementPattern.Capture<PsiIdentifier> jmlQuantifiedSpecExpression() {
        return psiElement(PsiIdentifier.class).withSuperParent(2, JMLQSpecExpr.class).andNot(jmlQuantifiedSpecDotExpression());
    }

    /**
     * @return PsiTree for java dot expressions in the last section of a quantified expression (after the loop variable declaration and loop condition)
     */

    private static PsiElementPattern.Capture<PsiIdentifier> jmlQuantifiedSpecDotExpression() {
        return psiElement(PsiIdentifier.class).withSuperParent(2, JMLQSpecExpr.class).afterLeaf(".");
    }

    /**
     * @return PsiTree for java identifier expressions in the condition section of a quantified expression (middle section)
     */

    private static PsiElementPattern.Capture<PsiIdentifier> jmlQuantifiedConditionExpression() {
        return psiElement(PsiIdentifier.class)
                .withParent(JMLFile.class)
                .andNot(jmlQuantifiedConditionDotExpression())
                .andNot(backslashNoLaterExpression())
                .andNot(quantifiedExpressionStart());
    }

    /**
     * @return PsiTree for java dot expressions in the condition section of a quantified expression (middle section)
     */

    private static PsiElementPattern.Capture<PsiIdentifier> jmlQuantifiedConditionDotExpression() {
        return psiElement(PsiIdentifier.class).withParent(JMLFile.class).afterLeaf(".");
    }

    /**
     * @param set - set of tokens that a psiElement could be (it can be any of them)
     * @return String[] that has the token strings extracted from the token set
     */

    @NotNull
    public static String[] getTokenSetOredTogether(@NotNull TokenSet set) {
        String[] names = new String[set.getTypes().length];
        for (int i = 0; i < set.getTypes().length; i++) {
            names[i] = set.getTypes()[i].toString();
        }
        return names;
    }
    /**
     * @return prints some information about the autocomplete to the console,
     * should not be called up above unless needed for debugging as it it prone to
     * null pointer exceptions.
     *
     * YOU SHOULD EITHER USE A DEBUGGER OR THIS DEBUG PRINT WHEN PROBING FOR COMPLETION PATTERNS BECAUSE PSI VIEWER
     * LIES ABOUT THE STRUCTURE OF THE PARSE TREE WHEN THE EXPRESSION IS INCOMPLETE.
     *
     * DEBUGGER APPROACH IS USUALLY BETTER BECAUSE YOU CAN STOP AND INSPECT THE TREE STRUCTURE BY CALLING METHODS ON
     * parameters.getPosition(). BUT THIS CAN BE VERY ANNOYING AT TIMES IF YOU NEED TO TEST MULTIPLE PLACES AND THE DEBUG
     * PRINT IS PREFERABLE IN THOSE CASES.
     */

    private CompletionProvider<CompletionParameters> debugPrint() {
        return new CompletionProvider<CompletionParameters>() {
            @Override
            protected void addCompletions(@NotNull CompletionParameters parameters,
                                          @NotNull ProcessingContext context,
                                          @NotNull CompletionResultSet result) {
                result.addElement(LookupElementBuilder.create("test"));
                System.out.println(
                        parameters.getPosition().getText() + " " +
                        parameters.getPosition().toString() + " " +
                        parameters.getPosition().getLanguage().toString() + " " +
                        parameters.getPosition().getParent().toString() + " " +
                        //parameters.getPosition().getPrevSibling().getPrevSibling().toString() + " " +
                        (parameters.getPosition().getPrevSibling() == null ? "no sibling" : parameters.getPosition().getPrevSibling().toString())
                );

            }
        };
    }
}
