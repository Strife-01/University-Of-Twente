package nl.utwente.jmlplugin.completion;

import com.intellij.codeInsight.completion.*;
import com.intellij.psi.JavaPsiFacade;
import com.intellij.psi.PsiClass;
import com.intellij.psi.PsiMember;
import com.intellij.psi.search.GlobalSearchScope;
import com.intellij.psi.search.searches.ClassInheritorsSearch;
import com.intellij.util.ProcessingContext;
import com.intellij.util.Query;
import org.jetbrains.annotations.NotNull;

import static nl.utwente.jmlplugin.completion.JMLCompletionUtils.*;

/**
 * Provides completions for all visible exception classes in the project (all exceptions that subclass Throwable)
 */

public class JMLJavaExceptionClassProvider extends CompletionProvider<CompletionParameters> {

    public static final JMLJavaExceptionClassProvider INSTANCE = new JMLJavaExceptionClassProvider();
    private static final String throwableQualifiedName = "java.lang.Throwable";

    @Override
    protected void addCompletions(@NotNull CompletionParameters parameters, @NotNull ProcessingContext context, @NotNull CompletionResultSet result) {
        if (parameters.getEditor().getProject() == null) return;

        final GlobalSearchScope scope = GlobalSearchScope.everythingScope(parameters.getEditor().getProject());
        final PsiClass superClass = JavaPsiFacade.getInstance(parameters.getEditor().getProject())
                .findClass(throwableQualifiedName, scope);

        if (superClass == null) return;

        final Query<PsiClass> query = ClassInheritorsSearch
                .search(superClass, scope, true, true, false);
        for (PsiClass psiClass: query) {
            if (isAccessibleHere(psiClass, parameters.getPosition())) {
                result.addElement(getClassLookup(psiClass));
            }
        }

        sortResults(parameters, result);
    }
}
