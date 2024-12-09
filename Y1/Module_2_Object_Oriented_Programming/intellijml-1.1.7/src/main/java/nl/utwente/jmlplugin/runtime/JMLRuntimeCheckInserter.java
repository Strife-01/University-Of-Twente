package nl.utwente.jmlplugin.runtime;

import com.intellij.lang.injection.InjectedLanguageManager;
import com.intellij.lang.java.JavaLanguage;
import com.intellij.openapi.util.Pair;
import com.intellij.openapi.util.TextRange;
import com.intellij.openapi.util.Trinity;
import com.intellij.psi.*;
import com.intellij.psi.util.PsiTreeUtil;
import nl.utwente.jmlplugin.JMLLanguage;
import nl.utwente.jmlplugin.annotator.CommentPosition;
import nl.utwente.jmlplugin.psi.*;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class JMLRuntimeCheckInserter {

    private JMLRuntimeCheckInserter() {
    }

    /**
     * Analyzes the given file and inserts runtime checks
     * into its contents where appropriate.
     *
     * @param psiFile The file that should be analyzed
     */
    public static void insertRuntimeChecks(PsiFile psiFile) {
        if (psiFile.getLanguage() != JavaLanguage.INSTANCE) {
            return; // Nothing to do
        }
        InjectedLanguageManager injectedLanguageManager = InjectedLanguageManager.getInstance(psiFile.getProject());

        // Collect all JML clauses
        // <Java comment, <specification type, specification Java expression, full specification as String>>
        Map<PsiComment, List<Trinity<JMLSpecificationType, JMLJavaExpr, String>>> insertMap = new HashMap<>();
        for (PsiComment comment : PsiTreeUtil.findChildrenOfType(psiFile, PsiComment.class)) {
            List<Pair<PsiElement, TextRange>> injectedPsiFiles = injectedLanguageManager.getInjectedPsiFiles(comment);
            if (injectedPsiFiles == null) {
                continue;
            }
            for (Pair<PsiElement, TextRange> injectedPsiFile : injectedPsiFiles) {
                PsiElement injectedElement = injectedPsiFile.getFirst();
                if (injectedElement.getLanguage() != JMLLanguage.INSTANCE) {
                    continue;
                }
                List<Trinity<JMLSpecificationType, JMLJavaExpr, String>> inserts = insertMap.computeIfAbsent(comment, k -> new ArrayList<>());
                for (PsiElement specification : PsiTreeUtil.findChildrenOfAnyType(injectedElement, JMLSpecificationType.getCheckableClasses())) {
                    JMLJavaExpr javaExpr = PsiTreeUtil.findChildOfType(specification, JMLJavaExpr.class);
                    if (javaExpr == null) {
                        continue;
                    }
                    inserts.add(Trinity.create(JMLSpecificationType.getSpecificationType(specification), javaExpr, specification.getText()));
                }
            }
        }

        // Insert runtime checks according to the found JML
        for (Map.Entry<PsiComment, List<Trinity<JMLSpecificationType, JMLJavaExpr, String>>> entry : insertMap.entrySet()) {
            switch (CommentPosition.getCommentPosition(entry.getKey())) {
                // Positions that have no associated code block
                case ABOVE_CLASS:
                case CLASS_INVARIANT:
                case FIELD:
                case INSIDE_CLASS:
                case PARAMETER:
                case UNKNOWN:
                    continue;
            }
            PsiCodeBlock codeBlock = getOrCreateCodeBlock(entry.getKey());
        }
    }

    /**
     * Gets or creates a code block for elements
     * that have a code block associated with them,
     * such as methods and for loops.
     * Creating a new code block is necessary
     * when the original code uses the "braceless" syntax.
     *
     * @param element The element to get the code block of
     * @return A code block for the given element
     */
    private static PsiCodeBlock getOrCreateCodeBlock(PsiElement element) {
        if (element instanceof PsiCodeBlock) {
            return (PsiCodeBlock) element;
        }
        if (element instanceof PsiMethod) {
            return ((PsiMethod) element).getBody();
        }
        if (element instanceof PsiLoopStatement) {
            PsiStatement statement = ((PsiLoopStatement) element).getBody();
            if (statement instanceof PsiBlockStatement) {
                return ((PsiBlockStatement) statement).getCodeBlock();
            }
            PsiElementFactory factory = JavaPsiFacade.getElementFactory(element.getProject());
            PsiBlockStatement newStatement = (PsiBlockStatement) factory.createStatementFromText("{}", element);
            PsiCodeBlock newCodeBlock = newStatement.getCodeBlock();
            if (statement == null) {
                element.addAfter(newStatement, element.getLastChild());
            } else {
                newCodeBlock.add(statement);
                statement.replace(newStatement);
            }
            return newCodeBlock;
        }
        return null;
    }

    /**
     * An enum containing different types of JML specifications
     * and their associated subclasses of PsiElement
     * that runtime checking can be applied to.
     */
    private enum JMLSpecificationType {
        ASSERT(JMLAssertStatement.class),
        ENSURES(JMLEnsuresClause.class),
        INVARIANT(JMLClassInvariant.class),
        LOOP_INVARIANT(JMLLoopInvariant.class),
        REQUIRES(JMLRequiresClause.class),
        SIGNALS(JMLSignalsClause.class);

        private final Class<? extends PsiElement> clazz;
        @SuppressWarnings("unchecked")
        private static final Class<? extends PsiElement>[] CHECKABLE_CLASSES =
                new Class[JMLSpecificationType.values().length];

        JMLSpecificationType(Class<? extends PsiElement> clazz) {
            this.clazz = clazz;
        }

        public static Class<? extends PsiElement>[] getCheckableClasses() {
            return CHECKABLE_CLASSES;
        }

        public static JMLSpecificationType getSpecificationType(PsiElement specification) {
            if (specification instanceof JMLAssertStatement) {
                return ASSERT;
            } else if (specification instanceof JMLEnsuresClause) {
                return ENSURES;
            } else if (specification instanceof JMLClassInvariant) {
                return INVARIANT;
            } else if (specification instanceof JMLLoopInvariant) {
                return LOOP_INVARIANT;
            } else if (specification instanceof JMLRequiresClause) {
                return REQUIRES;
            } else if (specification instanceof JMLSignalsClause) {
                return SIGNALS;
            } else {
                return null;
            }
        }

        static {
            JMLSpecificationType[] values = JMLSpecificationType.values();
            for (int i = 0; i < values.length; i++) {
                CHECKABLE_CLASSES[i] = values[i].clazz;
            }
        }
    }

}
