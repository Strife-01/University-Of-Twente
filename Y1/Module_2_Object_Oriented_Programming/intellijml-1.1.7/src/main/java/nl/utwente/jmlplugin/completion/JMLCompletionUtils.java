package nl.utwente.jmlplugin.completion;

import com.intellij.codeInsight.completion.*;
import com.intellij.codeInsight.lookup.LookupElement;
import com.intellij.codeInsight.lookup.LookupElementBuilder;
import com.intellij.lang.injection.InjectedLanguageManager;
import com.intellij.openapi.editor.Editor;
import com.intellij.psi.*;
import com.intellij.psi.impl.PsiImplUtil;
import com.intellij.psi.tree.TokenSet;
import com.intellij.psi.util.PsiTreeUtil;
import com.intellij.psi.util.PsiUtil;
import com.intellij.util.IncorrectOperationException;
import nl.utwente.jmlplugin.annotator.CommentPosition;
import nl.utwente.jmlplugin.annotator.JMLAnnotatorUtil;
import nl.utwente.jmlplugin.psi.impl.*;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

import static nl.utwente.jmlplugin.completion.JMLCompletionWeights.*;
import static nl.utwente.jmlplugin.psi.JMLTokenSet.*;

/**
 * Various utility methods that are needed by the various completion providers.
 *
 * Most completion providers have their logic decoupled into this utility class as a lot of code needs to be shared
 * across many providers.
 */

public class JMLCompletionUtils {

    public static final String[] PRIMITIVE_TYPES = {"byte", "char", "short", "int", "long", "float", "double", "boolean"};

    /**
     * Adds completions for all Java classes that are visible in the project, including imported libraries and
     * the standard library
     *
     * @param params  - completion context
     * @param results - completion results holder
     */

    public static void addJavaClassNameCompletions(CompletionParameters params, CompletionResultSet results) {
        // can throw some really stupid reflection errors can be thrown here, so we need a try-catch here
        try {
            JavaClassNameCompletionContributor.addAllClasses(params, true, results.getPrefixMatcher(), results);
        } catch (Throwable e) {
            //noinspection ConstantConditions
            if (!e.getClass().equals(Throwable.class)) {
                throw e;
            }
        }
    }

    /**
     * Adds all the field and method completions from the Java class file where the autocomplete was called in. This
     * also account for class nesting visibility behaviour.
     *
     * @param params  - completion context
     * @param results - completion results holder
     */

    public static void addFieldAndMethodCompletions(CompletionParameters params, CompletionResultSet results) {
        PsiClass currentClass = getEnclosingClass(params.getPosition());

        //check for null to protect against some weird edge cases
        if (currentClass == null) {
            return;
        }

        //Nested class visibility
        do {
            fillClassCompletions(currentClass, results, params);

            //check to see if we are an inner class
            final PsiClass superClass = getEnclosingClass(currentClass);
            if (superClass == null) {
                break;
            }
            currentClass = superClass;

        } while (true);

        //static imports
        for (PsiImportStaticStatement statement : getStaticImports(params)) {
            final String memberName = statement.getReferenceName();

            final PsiClass importedClass = statement.resolveTargetClass();

            if (memberName == null) {
                // * static import, we are importing everything
                if (importedClass != null) {
                    fillStaticCompletion(importedClass, results, params);
                }
            } else {
                // specific member import
                if (importedClass == null) continue;

                final PsiField field = importedClass.findFieldByName(memberName, true);
                if (field != null) {
                    if (isAccessibleHere((PsiMember) field, params.getPosition())) {
                        results.addElement(getFieldLookup(field));
                    }
                }

                final PsiMethod[] methods = importedClass.findMethodsByName(memberName, true);
                for (PsiMethod method : methods) {
                    if (isAccessibleHere((PsiMember) method, params.getPosition())) {
                        results.addElement(getMethodLookup(method));
                    }
                }

                final PsiClass innerClass = importedClass.findInnerClassByName(memberName, true);
                if (innerClass != null) {
                    if (isAccessibleHere((PsiMember) innerClass, params.getPosition())) {
                        fillClassCompletions(importedClass, results, params);
                    }
                }
            }

        }
    }

    /**
     * @param params - completion context.
     * @return the PsiFile for the underlying Java code.
     */

    @NotNull
    public static PsiFile getJavaFile(@NotNull CompletionParameters params) {
        return InjectedLanguageManager.getInstance(params.getEditor().getProject()).getTopLevelFile(params.getOriginalFile());
    }

    /**
     * @param field - PsiField reference
     * @return LookupElementBuilder reference that has the correct format for the completion of a field
     */

    @NotNull
    public static LookupElementBuilder getFieldLookup(@NotNull PsiField field) {
        return LookupElementBuilder.create(field)
                .withIcon(field.getIcon(0))
                .withTypeText(field.getType().getPresentableText());
    }

    /**
     * @param psiClass - PsiClass reference for which a lookup element needs to be built
     * @return LookupElementBuilder that has the properly formatted LookupElement for completions
     */

    @NotNull
    public static LookupElementBuilder getClassLookup(@NotNull PsiClass psiClass) {
        return LookupElementBuilder.create(psiClass).withIcon(psiClass.getIcon(0));
    }

    /**
     * @param method - method for which a LookupElement should be constructed.
     * @return LookupElementBuilder that contains the proper format for completion of the provided method.
     */

    @NotNull
    public static LookupElementBuilder getMethodLookup(@NotNull PsiMethod method) {
        final String returnType = method.getReturnType() == null ? "" : method.getReturnType().getPresentableText();

        return LookupElementBuilder.create(method)
                .withTypeText(returnType)
                .withIcon(method.getIcon(0))
                .withTailText(method.getParameterList().getText())
                .withStrikeoutness(PsiImplUtil.isDeprecated(method))
                .withInsertHandler((context, item) -> {
                    final Editor editor = context.getEditor();
                    context.setAddCompletionChar(false);
                    context.commitDocument();
                    context.getDocument().insertString(context.getStartOffset() + item.getLookupString().length(), "()");
                    editor.getCaretModel().moveToOffset(context.getStartOffset() + item.getLookupString().length() + 2 );
                });
    }

    /**
     * @param elem - just some PsiElement
     * @return returns the Java class that surrounds the provided PsiElement, null if such and element does not exist
     */

    @Nullable
    public static PsiClass getEnclosingClass(@NotNull PsiElement elem) {
        return PsiTreeUtil.getContextOfType(elem, PsiClass.class);
    }

    /**
     * Fill the completion results from the provided class both field and method
     *
     * @param psiClass - Java class for which completion needs to be filled in for
     * @param results  - completion results holder
     */

    public static void fillClassCompletions(@NotNull PsiClass psiClass, @NotNull CompletionResultSet results, CompletionParameters params) {

        PsiElement[] fields = psiClass.getFields();
        for (PsiElement elem : fields) {
            if (isAccessibleHere((PsiField) elem, params.getPosition())) {
                results.addElement(PrioritizedLookupElement.withPriority(getFieldLookup((PsiField) elem), LOCAL_FIELD.getWeight()));
            }
        }

        //fill method references
        PsiElement[] methods = psiClass.getMethods();
        for (PsiElement elem : methods) {
            if (isAccessibleHere((PsiMethod) elem, params.getPosition())) {
                results.addElement(PrioritizedLookupElement.withPriority(getMethodLookup((PsiMethod) elem), LOCAL_METHOD.getWeight()));
            }
        }
    }

    /**
     * This method fills in the completions for the provided classes super class (i.e. it fills in the super classes
     * methods and fields for completion, if they are accessible).
     *
     * @param results - completion result set
     * @param params - completion context
     */

    public static void fillSuperClassCompletions(@NotNull CompletionResultSet results, CompletionParameters params) {
        PsiClass psiClass = getClass(params.getPosition());
        if(psiClass == null) return;

        // get all super classes
        PsiClass[] subClasses = psiClass.getSupers();

        for(PsiClass subClass: subClasses) {
            //fill field references
            PsiElement[] fields = subClass.getAllFields();
            for (PsiElement elem : fields) {
                if (isAccessibleHere((PsiField) elem, params.getPosition())) {
                    results.addElement(PrioritizedLookupElement.withPriority(getFieldLookup((PsiField) elem), LOCAL_FIELD.getWeight()));
                }
            }

            //fill method references
            PsiElement[] methods = subClass.getAllMethods();
            for (PsiElement elem : methods) {
                if (isAccessibleHere((PsiMethod) elem, params.getPosition())) {
                    results.addElement(PrioritizedLookupElement.withPriority(getMethodLookup((PsiMethod) elem), LOCAL_METHOD.getWeight()));
                }
            }
        }

    }

    /**
     * Fill static method and field references, is used for resolving static class imports, difference with the class
     * completion fill method is that this method only fills in static fields and classes.
     *
     * @param psiClass - reference to the staticly imported Java class
     * @param results  - completion results holder
     */

    public static void fillStaticCompletion(@NotNull PsiClass psiClass, @NotNull CompletionResultSet results, @NotNull CompletionParameters params) {

        //fill field references
        for (PsiElement elem : psiClass.getFields()) {
            final PsiField field = (PsiField) elem;

            if (field.getModifierList() == null) {
                continue;
            }

            if (field.getModifierList().hasModifierProperty(PsiModifier.STATIC)) {
                //check visibility
                if (isAccessibleHere(field, params.getPosition())) {
                    results.addElement(PrioritizedLookupElement
                            .withPriority(getFieldLookup(field), STATIC_IMPORT_FIELD.getWeight()));
                }
            }
        }

        //fill method references
        for (PsiElement elem : psiClass.getMethods()) {
            final PsiMethod method = (PsiMethod) elem;

            if (method.getModifierList().hasModifierProperty(PsiModifier.STATIC)) {
                if (isAccessibleHere(method, params.getPosition())) {
                    results.addElement(PrioritizedLookupElement
                            .withPriority(getMethodLookup(method), STATIC_IMPORT_METHOD.getWeight()));
                }
            }
        }
    }

    /**
     * Fill in the field completions for a given class.
     *
     * @param psiClass - psiClass whose fields need to be included in the code completion.
     * @param results - completion results holder.
     * @param params - completion context.
     */

    public static void fillFieldCompletions(@NotNull PsiClass psiClass, @NotNull CompletionResultSet results, @NotNull CompletionParameters params) {
        for (PsiElement elem : psiClass.getFields()) {
            if (isAccessibleHere((PsiMember) elem, params.getPosition())) {
                results.addElement(getFieldLookup((PsiField) elem));
            }
        }
    }

    /**
     * @param params - context of the autocomplete
     * @return list of static import statements, can be used later to resolve static import references
     */

    @NotNull
    public static List<PsiImportStaticStatement> getStaticImports(@NotNull CompletionParameters params) {
        final LinkedList<PsiImportStaticStatement> result = new LinkedList<>();

        for (PsiElement elem : getJavaFile(params).getChildren()) {
            if (elem instanceof PsiImportList) {
                result.addAll(Arrays.asList(((PsiImportList) elem).getImportStaticStatements()));
                break;
            }
        }

        return result;
    }

    /**
     * @param params - completion context.
     * @return PsiImportList for the Java file in which this completion was called in.
     */

    @Nullable
    public static PsiImportList getImportList(@NotNull CompletionParameters params) {
        for (PsiElement elem : getJavaFile(params).getChildren()) {
            if (elem instanceof PsiImportList) {
                return (PsiImportList) elem;
            }
        }
        return null;
    }

    /**
     * @param elem - PsiElement whose enclosing class needs to be resolved (not the class type, simply where this particurlar thing is written).
     * @return - the enclosing class of the given element.
     */

    @Nullable
    public static PsiClass getClass(@NotNull PsiElement elem) {
        return PsiTreeUtil.getContextOfType(elem, PsiClass.class);
    }

    /**
     * Checks whether a given PsiMember is accessible in the provided location according to Java's visibility rules.
     *
     * @param member - member whose visibility needs to be checked.
     * @param location - the location where we want to reference the member.
     * @return true if the the member is accessible at the given location, false otherwise.
     */

    public static boolean isAccessibleHere(@NotNull PsiMember member,@NotNull PsiElement location) {
        return PsiUtil.isMemberAccessibleAt(member, location);
    }

    /**
     * @param params - completion context.
     * @return returns a PsiMethod reference for the method above which the completion was called on.
     */

    @Nullable
    public static PsiMethod getMethodContext(@NotNull CompletionParameters params) {
        final PsiElement elem = JMLAnnotatorUtil.getJavaContext(params.getPosition());
        return elem instanceof PsiMethod ? (PsiMethod) elem : null;
    }

    /**
     * Fills in the method parameters to the completion, this is used for providing references to the method parameters
     * if the completion is called in the method spec, because these variables could feasible show up quite often.
     *
     * @param params - completion context.
     * @param results - completion results holder.
     */

    public static void fillMethodParameterCompletions(@NotNull CompletionParameters params,@NotNull CompletionResultSet results) {
        final PsiMethod method = getMethodContext(params);
        if (method == null) return;

        for (PsiParameter methodParameter: method.getParameterList().getParameters()) {
            results.addElement(getMethodParameterCompletion(methodParameter));
        }
    }

    /**
     * @param parameter - method parameter for a LookupElement needs to created and correctly formatted.
     * @return LookupElementBuilder with the correct formatting for LookupElement that is made from a PsiParamter.
     */

    @NotNull
    public static LookupElementBuilder getMethodParameterCompletion(@NotNull PsiParameter parameter) {
        return LookupElementBuilder.create(parameter)
                .withIcon(parameter.getIcon(0))
                .withTypeText(parameter.getType().getPresentableText());
    }

    /**
     * Reuse of IntelliJ's completion results sorting algorithm, doesn't work as well as normal as much of the
     * completion that is made by IntelliJ is heavily dependent on context and a proper Java parse tree.
     *
     * But this works better than anything I can come up with, so we use this.
     *
     * @param params - completion context.
     * @param results - completion results holder.
     */

    public static void sortResults(@NotNull CompletionParameters params, @NotNull CompletionResultSet results) {
        JavaCompletionSorting.addJavaSorting(params, results);
    }

    /**
     * Fill in completions for . expressions when they are called on a method parameter, only single dot expressions are
     * supported as we do not have our own recursive type resolver.
     *
     * @param params - completion context.
     * @param results - completion results holder.
     * @return true if the type of the method parameter could be resolved and completions filled in, false otherwise.
     */

    public static boolean fillMethodParameterDotCompletions(@NotNull CompletionParameters params, @NotNull CompletionResultSet results) {
        final PsiMethod method = getMethodContext(params);
        if (method == null) return false;

        final String prevElementText = params.getPosition().getPrevSibling().getPrevSibling().getText();
        for (PsiParameter psiParameter: method.getParameterList().getParameters()) {
            if (psiParameter.getName().equals(prevElementText)) {
                final PsiClass psiClass = getClass(psiParameter.getType());
                if (psiClass == null) return false;

                fillClassCompletions(psiClass, results, params);
                sortResults(params, results);
                return true;
            }
        }
        return false;
    }

    /**
     * @param type - PsiType for which a reference to the class declaration needs to be resolved.
     * @return PsiClass reference for class that defines the PsiType, null if the class reference could not be found.
     */

    @Nullable
    public static PsiClass getClass(@NotNull PsiType type) {
        return PsiUtil.resolveClassInClassTypeOnly(type);
    }

    /**
     * Hack method for providing singly chained . completions for JMLKeywords. To do this properly a recursive type resolver
     * that accounts for JMLKeywords is necessary, so until one is made, this is the stopgap.
     *
     * @param params - completion context.
     * @param results - completion result holder.
     * @return true if the type of the keyword could be resolved and the completions filled in, false otherwise.
     */

    public static boolean fillJMLKeywordCompletions(@NotNull CompletionParameters params, @NotNull CompletionResultSet results) {
        final String prevText = params.getPosition().getPrevSibling().getPrevSibling().getText();

        //check for \result first
        if (prevText.equals("\\result")) {
            final PsiMethod method = getMethodContext(params);
            if (method == null) return true;

            if (method.getReturnType() == null) return true;
            final PsiClass psiClass = getClass(method.getReturnType());

            if (psiClass == null) return true;
            fillClassCompletions(psiClass, results, params);
            sortResults(params, results);
            return true;
        }


        if (params.getPosition().getPrevSibling().getPrevSibling() instanceof JMLOldExpr) {
            final PsiElement old = params.getPosition().getPrevSibling().getPrevSibling();

            for (PsiElement child: old.getChildren()) {
                if (child instanceof JMLInnerJavaExpr) {
                    final String text = child.getText();
                    if (text == null) return true;

                    final PsiExpression parsedExpression = getPsiExpression(text, params);
                    if (parsedExpression == null) return true;

                    final PsiType type = parsedExpression.getType();
                    if (type == null) return true;

                    final PsiClass psiClass = getClass(type);
                    if (psiClass == null) return true;

                    fillClassCompletions(psiClass, results, params);
                    sortResults(params, results);
                    return true;
                }
            }
        }

        return false;
    }

    /**
     * @param text - raw text of the java expression
     *
     * @param params - completion context
     *
     * @return constructs a java psi expression that can be used to resolve java typing and java references,
     * returns null if the project reference could not be retrieved or failed to construct an expression from the text
     */

    @Nullable
    public static PsiExpression getPsiExpression(@NotNull String text, @NotNull CompletionParameters params) {
        if (params.getEditor().getProject() != null) {
            try {
                return JavaPsiFacade.getInstance(params.getEditor().getProject()).getParserFacade().createExpressionFromText(text.trim(), params.getPosition());
            } catch (IncorrectOperationException e) {
                return null;
            }
        }
        return null;
    }

    /**
     * Fill in completions for primitive types.
     * @param results - completion result holder.
     */

    public static void fillPrimitiveClassCompletions(CompletionResultSet results) {
        for (String type: PRIMITIVE_TYPES) {
            results.addElement(LookupElementBuilder.create(type));
        }
    }

    /**
     * @param params - completion context.
     * @return In what kind of JML comment was the completion called in (e.g. method spec or invariant)
     */

    @NotNull
    public static CommentPosition getCommentPosition(@NotNull CompletionParameters params) {
        return CommentPosition.getCommentPosition(JMLAnnotatorUtil.getCommentContext(params.getPosition()));
    }

    /**
     * Add completions for the provided set of Tokens
     * @param set - set of tokens which should be included in the completion results.
     * @param results - completion result holder.
     */

    public static void addTokens(@NotNull TokenSet set, @NotNull CompletionResultSet results) {
        for (int i = 0; i < set.getTypes().length; i++) {
            String tokenText = set.getTypes()[i].toString();

            //account for parentheses
            if (tokenNeedsParentheses(tokenText)) tokenText = tokenText + "()";

            results.addElement(PrioritizedLookupElement.withPriority(LookupElementBuilder.create(tokenText), JMLCompletionWeights.KEYWORD.getWeight()));
        }
    }

    /**
     * Extracts the token text from a set of tokens.
     *
     * @param set - set of tokens whose text needs to be extracted.
     * @return - String[] object that contains the text that the the tokens contained in the set represent.
     */

    @NotNull
    public static String[] getText(@NotNull TokenSet set) {
        final String[] result = new String[set.getTypes().length];

        for (int i = 0; i < set.getTypes().length; i++) {
            if (tokenNeedsParentheses(set.getTypes()[i].toString())) {
                result[i] = set.getTypes()[i].toString() + "()";
            } else {
                result[i] = set.getTypes()[i].toString();
            }
        }

        return result;
    }

    /**
     * Checks whether a given token needs parentheses after it, this is because token text does not include parentheses
     * because they are seperate tokens.
     * @param tokenText - text of a token.
     * @return true if the token should have perentheses, false otherwise.
     */

    public static boolean tokenNeedsParentheses(String tokenText) {
        switch (tokenText) {
            case "\\signals":
            case "signals":
            case "\\old":
            case "\\typeof":
            case "\\elemtype":
            case "\\type":
            case "\\nonnullelements":
                return true;
            default:
                return false;
        }
    }

    /**
     * Fill in JML keyword completions for the JML keywords that can be mixed with Java.
     * This method is context aware and will try to only fill in valid keywords in a
     * given context.
     *
     * @param params - completion context.
     * @param results - completion result holder.
     */
	
	public static void fillJMLCompletions(@NotNull CompletionParameters params, @NotNull CompletionResultSet results) {
        //check additional conditions
        final expressionLocation location;
        try {
           location = expressionLocation.resolveLocation(params);
        } catch (IllegalStateException e) {
            return;
        }

        switch (location) {
            case ASSIGNABLE:
                addTokens(assignableJavaKeywords, results);
                break;
            case ENSURES:
                //fallthrough is intentional
                addTokens(result, results);
            case OTHER:
                addTokens(generalJMLKeywordsInJava, results);
                addTokens(quantifiers, results);
                break;
        }

        addTokens(javaKeywords, results);
    }

    /**
     * Enum for JML expression location, this is needed for context aware completion of JML keywords that can be mixed
     * with Java.
     */

    public enum expressionLocation {
        ENSURES,
        ASSIGNABLE,
        OTHER;

        /**
         * Resolves the JML expression type in which code completion was called in, used to provide context aware
         * JML keyword completions for JML keywords that can be mixed with Java.
         *
         * @param params - completion context.
         * @return the JML expression type where the code completion was called.
         * @throws IllegalStateException - is thrown if the location can not be resolved (should not happen,
         * which is why this is an exception, but who knows)
         */

        @NotNull
        public static expressionLocation resolveLocation(@NotNull CompletionParameters params) throws IllegalStateException {
            //break out of the Java expression
             PsiElement elem = params.getPosition();
             while (true) {
                 if (elem.getParent() != null) {
                     elem = elem.getParent();
                 } else {
                     throw new IllegalStateException("null parent, something is malformed");
                 }

                 if (elem instanceof JMLJavaExprImpl) {
                     break;
                 }
             }

             // broke out out of the java expression now check in what JML expression we are in
             final PsiElement javaParent = elem.getParent();
             if (javaParent == null) throw new IllegalStateException("Incomplete java expression");

             if (javaParent instanceof JMLEnsuresClauseImpl) {
                 return ENSURES;
             } else if (javaParent instanceof JMLAssignableClauseImpl) {
                 return ASSIGNABLE;
             }

            return OTHER;
        }
    }


    /**
     * Fills in local variable completions for when JML completions are called inside a method, this accounts for
     * scope visibility of parameters.
     *
     * @param params - completion context.
     *
     * @param results - completion results holder.
     */
    public static void fillMethodLocalVariables(@NotNull CompletionParameters params, @NotNull CompletionResultSet results) {
        final CommentPosition pos = getCommentPosition(params);

        if (pos == CommentPosition.CODE_BLOCK) {
            // get enclosing method
            final PsiMethod method = getEnclosingMethod(params);
            if (method == null) return;

            // extract all declaration statements from the method
            final LinkedList<PsiDeclarationStatement> declarations = new LinkedList<>();
            if (method.getBody() == null) return;

            // recursively collect all statements in the method
            final LinkedList<PsiStatement> statements = new LinkedList<>();
            for (PsiStatement psiStatement:method.getBody().getStatements()) {
                statements.add(psiStatement);
                getStatements(psiStatement, statements);
            }

            for (PsiStatement statement : statements) {
                if (statement instanceof PsiDeclarationStatement) {
                    declarations.add((PsiDeclarationStatement) statement);
                }
            }

            // extract the list of all locally declared variables
            LinkedList<PsiLocalVariable> localVariables = new LinkedList<>();
            for (PsiDeclarationStatement dec : declarations) {
                for (PsiElement elem : dec.getDeclaredElements()) {
                    if (elem instanceof PsiLocalVariable) {
                        localVariables.add((PsiLocalVariable) elem);
                    }
                }
            }

            //fill in the completions
            for (PsiLocalVariable var : localVariables) {
                // filter by accessibility
                if (localVariableInScope(var, params)) {
                    results.addElement(getLocalVariableLookup(var));
                }
            }
        }
    }

    /**
     * Recursively visits all the children of the given
     * element and collects all PsiStatement elements into the provided list
     *
     * @param statement - PsiStatement whose children need to be recursively visited.
     *
     * @param statementList - PsiStatement list where the collected statements need to be stored.
     */

    public static void getStatements(@NotNull PsiElement statement,
                                     @NotNull LinkedList<PsiStatement> statementList) {
        for (PsiElement elem: statement.getChildren()) {
            if (elem instanceof PsiStatement) {
                statementList.add((PsiStatement) elem);
            }
            getStatements(elem, statementList);
        }
    }


    /**
     * @param params - completion context.
     *
     * @return - returns a reference to the method that encloses the completion,
     * or null if no such enclosing method is found.
     */
    @Nullable
    public static PsiMethod getEnclosingMethod(@NotNull CompletionParameters params) {
        return PsiTreeUtil.getParentOfType(JMLAnnotatorUtil.getJavaContext(params.getPosition()), PsiMethod.class);
    }

    /**
     * @param var - local variable (i.e. variables declared within methods).
     *
     * @param params - completion context.
     *
     * @return - returns true if the provided var is in scope at the completion location, false otherwise.
     */
    public static boolean localVariableInScope(@NotNull PsiLocalVariable var, @NotNull CompletionParameters params) {
        final PsiJavaCodeReferenceElement reference;
        if (params.getEditor().getProject() == null) return false;

        try {
            reference = (PsiJavaCodeReferenceElement) JavaPsiFacade.getInstance(params.getEditor().getProject())
                    .getParserFacade()
                    .createExpressionFromText(var.getName(), params.getPosition());
        } catch (IncorrectOperationException e) {
            return false;
        }

        final JavaResolveResult resolve = reference.advancedResolve(false);
        return resolve.isValidResult();
    }

    /**
     * @param var - local variable reference.
     *
     * @return - returns a LookupElementBuilder that contains a correctly formatted
     * completion suggestion for a method local variable.
     */
    @NotNull
    public static LookupElementBuilder getLocalVariableLookup(@NotNull PsiLocalVariable var) {
        return LookupElementBuilder.create(var)
                .withIcon(var.getIcon(0))
                .withTypeText(var.getType().getPresentableText());
    }

}
