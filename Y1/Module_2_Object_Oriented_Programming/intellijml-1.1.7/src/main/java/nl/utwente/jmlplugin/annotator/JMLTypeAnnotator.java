package nl.utwente.jmlplugin.annotator;

import com.intellij.lang.annotation.AnnotationHolder;
import com.intellij.lang.annotation.HighlightSeverity;
import com.intellij.psi.*;
import com.intellij.psi.tree.IElementType;
import com.intellij.psi.tree.TokenSet;
import com.intellij.psi.util.PsiTreeUtil;
import com.intellij.psi.util.PsiTypesUtil;
import com.intellij.psi.util.TypeConversionUtil;
import com.intellij.util.IncorrectOperationException;
import nl.utwente.jmlplugin.psi.*;
import nl.utwente.jmlplugin.psi.impl.*;
import org.jetbrains.annotations.NotNull;

import java.util.Map;

import static com.intellij.psi.util.PsiTreeUtil.getChildOfType;
import static com.intellij.psi.util.PsiTreeUtil.getParentOfType;
import static nl.utwente.jmlplugin.annotator.JMLAnnotatorUtil.*;
import static nl.utwente.jmlplugin.annotator.JMLTypeAnnotatorUtil.*;

/**
 * Checks the tree for type errors
 */
public class JMLTypeAnnotator {

    /**
     * Annotates the elements on type errors
     *
     * @param element the element we are checking
     * @param holder  the Annotation holder
     */
    public static void annotateTypes(@NotNull PsiElement element, @NotNull AnnotationHolder holder) {
        if (element instanceof JMLStoreRef && element.getParent() instanceof JMLAssignableClause) {
            checkAssignableVarScope(element, holder);
        } else if (element instanceof JMLReferenceType && (element.getParent() instanceof JMLSignalsClause || element.getParent() instanceof JMLSignalsOnlyClause)) {
            checkSignalsType((JMLReferenceType) element, holder);
        } else if (element instanceof JMLJavaExpr) {
            annotateJavaExpr((JMLJavaExpr) element, holder);
        }
    }

    /**
     * Checks whether a reference in an assignable clause can be resolved and whether they are allowed
     *
     * @param element the reference to check for
     * @param holder  the Annotation holder
     */
    public static void checkAssignableVarScope(PsiElement element, AnnotationHolder holder) {
        // get the class the JML comment is in
        PsiClass classContext = getParentOfType(getJavaContext(element), PsiClass.class);
        // replace [*] or .* so we only have the name of the reference
        String referenceName = element.getText().replaceAll("\\[\\*]|\\.\\*", "");

        PsiJavaCodeReferenceElement classReference = null;
        PsiExpression fieldReference = null;
        boolean incorrectRef = false;
        // make a java reference expression out of the name
        // need to try classReference for classes and fieldReference for fields
        try {
            fieldReference = JavaPsiFacade.getElementFactory(element.getProject()).createExpressionFromText(referenceName, classContext);
        } catch (IncorrectOperationException e) {
            incorrectRef = true;
        }
        try {
            classReference = JavaPsiFacade.getElementFactory(element.getProject()).createReferenceFromText(referenceName, classContext);
        } catch (IncorrectOperationException e) {
            // only show this error if both fieldReference and classReference are incorrect
            if (incorrectRef) {
                holder.newAnnotation(HighlightSeverity.ERROR, ErrorMessages.INCORRECT_REFERENCE).range(element.getTextRange()).create();
                return;
            }
        }
        // try to resolve the reference to a field
        JavaResolveResult fieldResolved = null;
        if (fieldReference instanceof PsiJavaCodeReferenceElement) {
            fieldResolved = ((PsiJavaCodeReferenceElement) fieldReference).advancedResolve(false);
        }
        boolean fieldValid = fieldResolved != null && fieldResolved.isValidResult();
        // try to resolve the reference to a class
        JavaResolveResult classResolved = classReference == null ? null : classReference.advancedResolve(false);
        boolean classValid = classResolved != null && classResolved.isValidResult();

        // check that either a field or a class could be resolved
        if (!fieldValid && !classValid && !referenceName.equals("this") && !referenceName.equals("super")) {
            // reference does not point to a field or a class
            holder.newAnnotation(HighlightSeverity.ERROR, ErrorMessages.REFERENCE_UNRESOLVED).create();
            return;
        }
        // divide checking based of whether it ends with [*], .* or nothing
        // [*] is only allowed on arrays
        if (element.getText().contains("[*]")) {
            if (!(fieldValid && fieldResolved.getElement() instanceof PsiField
                    && ((PsiField) fieldResolved.getElement()).getType().getArrayDimensions() > 0)) {
                // reference points to a field, but field is not an array
                holder.newAnnotation(HighlightSeverity.ERROR, ErrorMessages.ASSIGNABLE_ARRAY_ONLY).create();
            }
            // .* is only allowed on class names
        } else if (element.getText().contains(".*")) {
            if (!((classValid && classResolved.getElement() instanceof PsiClass)
                    || (fieldValid && fieldResolved.getElement() instanceof PsiField && ((PsiField) fieldResolved.getElement()).getType() instanceof PsiClassType)
                    || referenceName.equals("this") || referenceName.equals("super"))) {
                // is a static class reference or a reference to a field which holds a class instance
                holder.newAnnotation(HighlightSeverity.ERROR, ErrorMessages.ASSIGNABLE_CLASS_ONLY).create();
            }
        } else {
            if (!fieldValid) {
                // class names are only allowed with .* (you cannot assign a static class reference)
                holder.newAnnotation(HighlightSeverity.ERROR, ErrorMessages.UNASSIGNABLE).create();
            }
            // reference points to a field, check that it is not final
            else if (fieldResolved.getElement() instanceof PsiField && ((PsiField) fieldResolved.getElement()).hasModifierProperty(PsiModifier.FINAL)) {
                holder.newAnnotation(HighlightSeverity.ERROR, ErrorMessages.ASSIGNABLE_VAR_IS_FINAL).create();
            }
        }
    }

    /**
     * Checks whether a reference to an exception in an signals or signals-only clause can be resolved and whether they are allowed
     *
     * @param element the reference to check for
     * @param holder  the Annotation holder
     */
    public static void checkSignalsType(JMLReferenceType element, AnnotationHolder holder) {
        PsiElement context = (getJavaContext(element));
        // make a java reference expression out of the name
        PsiJavaCodeReferenceElement exceptionReference;
        try {
            exceptionReference = JavaPsiFacade.getElementFactory(element.getProject()).createReferenceFromText(element.getText(), context);
        } catch (IncorrectOperationException e) {
            holder.newAnnotation(HighlightSeverity.ERROR, ErrorMessages.NOT_A_CLASS_NAME).create();
            return;
        }

        JavaResolveResult resolveResult = exceptionReference.advancedResolve(false);
        if (resolveResult.isValidResult()) {
            PsiElement resolvedException = resolveResult.getElement();
            if (resolvedException instanceof PsiClass) {
                // get instance of PsiClassType for a runtime exception
                PsiClassType runtimeExceptionType = PsiType.getJavaLangRuntimeException(element.getManager(), element.getResolveScope());
                // find the PsiType of the class java.lang.Exception (PsiType does not have an explicit function for this :( )
                // we know RuntimeException has Exception as super, so we find it by looping through the super types
                PsiType exceptionType = PsiType.NULL;
                for (PsiType superType : runtimeExceptionType.getSuperTypes()) {
                    if (superType.getCanonicalText().equals("java.lang.Exception")) {
                        exceptionType = superType;
                        break;
                    }
                }

                PsiClassType elemType = PsiTypesUtil.getClassType((PsiClass) resolvedException);
                boolean inheritsRuntimeException = TypeConversionUtil.areTypesConvertible(elemType, runtimeExceptionType);
                boolean inheritsException = TypeConversionUtil.areTypesConvertible(elemType, exceptionType);
                // check that our referenced class inherits from Exception and optionally RuntimeException
                if (!inheritsException) {
                    holder.newAnnotation(HighlightSeverity.ERROR, ErrorMessages.NOT_AN_EXCEPTION_CLASS).create();
                }

                // if it is not a runtime exception, it should be mentioned in the throws clause of the context
                else if (!inheritsRuntimeException && context instanceof PsiMethod) {
                    PsiMethod psiMethod = (PsiMethod) context;
                    PsiClassType[] throwsList = psiMethod.getThrowsList().getReferencedTypes();
                    // go through all exceptions in the throws clause till you find a matching exception
                    boolean found = false;
                    for (PsiClassType thrown : throwsList) {
                        if (TypeConversionUtil.areTypesConvertible(elemType, thrown)) {
                            found = true;
                            break;
                        }
                    }
                    if (!found) {
                        // no matching exception found in the throws-clause
                        holder.newAnnotation(HighlightSeverity.ERROR, ErrorMessages.PUT_IN_THROWS_CLAUSE).create();
                    }
                }
            } else {
                // reference got resolved, but not to a class
                holder.newAnnotation(HighlightSeverity.ERROR, ErrorMessages.NOT_A_CLASS_NAME).create();
            }

        } else {
            // reference could not be resolved
            holder.newAnnotation(HighlightSeverity.ERROR, ErrorMessages.CLASS_REFERENCE_NOT_FOUND).create();
        }
    }

    /**
     * Checks the whether the java expression in the JML comment has proper types and does a few other checks as well
     *
     * @param element the java expression element in the JML tree
     * @param holder  the Annotation holder
     */
    private static void annotateJavaExpr(JMLJavaExpr element, @NotNull AnnotationHolder holder) {
        // get the inner java expression
        if (element.getFirstChild() != null) {
            // add a few extra variables that will not be able to be resolved by the Java resolver
            ExtraVariables extraVars = new ExtraVariables();
            PsiElement context = getJavaContext(element);
            if (context instanceof PsiMethod) {
                // parameters are not included by the Java resolver, so we store them ourselves
                addParameterVariables((PsiMethod) context, extraVars);
            }
            if (element.getParent() instanceof JMLSignalsClause) {
                // add the exception reference in the signals clause to the variables
                JMLSignalsClause parent = ((JMLSignalsClause) element.getParent());
                if (parent.getIdent() != null) {
                    addSignalsVariable(parent.getIdent(), parent.getReferenceType(), extraVars, holder);
                }
            } else if (element.getParent() instanceof JMLLoopInvariant) {
                // for loop_invariants add the initializer of the loop
                addLoopInitializers((JMLLoopInvariant) element.getParent(), extraVars);
            }
            // do the actual checking of the java expression
            InnerJavaExprResult res = annotateInnerJavaExpr((JMLInnerJavaExpr) element.getFirstChild(), holder, extraVars, true, true);

        }
    }

    /**
     * Recursively checks that the java expression is valid, and internally replaces JML expressions
     * with corresponding Java expressions such that the Java resolver does not error and checks with the correct types
     *
     * @param element           the inner java expression
     * @param holder            the Annotation holder
     * @param extraVars         an Object that holds extra variables that the Java resolver would not be able to resolve
     * @param mustReturnBoolean if true, it is checked that the expression returns a boolean value
     * @param doTypeChecking    whether type checking needs to happen, as not all expressions need that
     * @return whether the expression is valid, the text and the type of the expression and the range changes
     */
    @NotNull
    private static InnerJavaExprResult annotateInnerJavaExpr(JMLInnerJavaExpr element, AnnotationHolder holder,
                                                             ExtraVariables extraVars, boolean mustReturnBoolean, boolean doTypeChecking) {
        InnerJavaExprResult result = new InnerJavaExprResult(element);
        if (element == null) return result;
        PsiElement currentChild = element.getFirstChild();
        while (currentChild != null) {
            IElementType elemType = currentChild.getNode().getElementType();
            if (elemType == JMLTypes.RESULT) {
                checkBackslashResult(element, holder, result, currentChild);
            } else if (JMLTokenSet.logicalOperators.contains(elemType)) {
                // replace JML operators such as ==> and <==> with &&
                // this is a valid replacement as the JML operators want booleans on both sides of
                // the operator, and so does &&
                result.addText("&&", currentChild);
            } else if (elemType == JMLTypes.TYPE_CAPS) {
                // replace \TYPE
                result.add("java.lang.Class", PsiType.getJavaLangClass(currentChild.getManager(), currentChild.getResolveScope()), currentChild);
            } else if (currentChild instanceof JMLTypeOfExpr) {
                // \typeof(expr), checks the expression and then replaces the entire statement with typeName.class
                JMLInnerJavaExpr javaChild = getChildOfType(currentChild, JMLInnerJavaExpr.class);
                if (javaChild == null) {
                    // should not happen, but just in case.
                    // do not add an error to the holder, as the semantics annotator already did that
                    result.add("null", PsiType.NULL, false, currentChild);
                    currentChild = currentChild.getNextSibling();
                    continue;
                }
                InnerJavaExprResult exprRes = annotateInnerJavaExpr(javaChild, holder, extraVars, false, true);
                result.add(exprRes.getType().getCanonicalText() + ".class",
                        PsiType.getJavaLangClass(currentChild.getManager(), currentChild.getResolveScope()), exprRes.isCorrect(), currentChild);
            } else if (currentChild instanceof JMLElemTypeExpr) {
                checkElemTypeExpr(holder, extraVars, result, currentChild);
            } else if (currentChild instanceof JMLNonNullElementsExpr) {
                checkNonNullElementsExpr(holder, extraVars, result, currentChild);
            } else if (currentChild instanceof JMLOldExpr) {
                // \old(expr), checks the expression, but does not type check it, as the expression is not replaced,
                // so it will be type checked when result is evaluated.
                // replaces \old(expr) with expr
                JMLInnerJavaExpr javaChild = getChildOfType(currentChild, JMLInnerJavaExpr.class);
                if (javaChild == null) {
                    // should not happen, but just in case.
                    // do not add an error to the holder, as the semantics annotator already did that
                    result.add("null", PsiType.NULL, false, currentChild);
                    currentChild = currentChild.getNextSibling();
                    continue;
                }
                result.add(annotateInnerJavaExpr(javaChild, holder, extraVars, false, false), currentChild);
            } else if (currentChild instanceof JMLTypeExpr) {
                checkTypeExpr(holder, result, currentChild);
            } else if (currentChild instanceof JMLQuantifiedExpr) {
                evaluateQuantifiedExpr((JMLQuantifiedExpr) currentChild, extraVars, result, holder);
            } else if (currentChild instanceof PsiIdentifier) {
                // replaces the reference if it is in extraVars
                String newText = getReplacementIfNeeded((PsiIdentifier) currentChild, extraVars);
                result.addText(newText, currentChild);
            } else if (currentChild instanceof PsiComment) {
                // just remove comments
                result.addText("", currentChild);
            } else {
                // do no replacements, just add the token to the result
                result.addText(currentChild.getText(), currentChild);
            }
            // go to the next token
            currentChild = currentChild.getNextSibling();
        }

        // collected the entire java expression string with its replacements,
        // now perform type checking and some other checks on it
        if (result.isCorrect()) {
            // get the actual java expression
            PsiExpression expression = getJavaExprFromText(element, result, holder);
            if (expression != null) {
                result.setExpr(expression);
                // do java expression checking if needed
                if (doTypeChecking) {
                    JMLJavaExprVisitor visitor = new JMLJavaExprVisitor(holder, result.getRangeManager(), element.getProject(), element);
                    result.setCorrect(visitor.doChecking(expression, false));
                    // for invariants, also check the visibility of the resolved references
                    // we do it here, as here we have the resolved variables
                    JMLClassInvariant invariant = getParentOfType(element, JMLClassInvariant.class);
                    if (result.isCorrect() && invariant != null) {
                        checkInvariantVisibility(invariant, visitor);
                        result.setCorrect(visitor.isCorrect());
                    }
                }

                if (mustReturnBoolean && result.isCorrect()) {
                    // check is the expression is a valid boolean expression
                    result.setCorrect(checkExprIsBoolean(expression, holder, result.getRangeManager()));
                }
            } else {
                // when an expression could not be created, it is not a good expression
                result.setCorrect(false);
            }

            // set the type if not set
            if ((result.getType() == PsiType.NULL) && expression != null) {
                result.setType(expression.getType());
            }
        }
        return result;
    }

    /**
     * Checks that the return type of the method is not void and
     * replaces \result with the default value for the return type of the method
     *
     * @param element the inner Java expression containing \result
     * @param holder  the Annotation holder
     * @param result  the result up until now
     * @param current the element we are checking for
     */
    private static void checkBackslashResult(JMLInnerJavaExpr element, AnnotationHolder holder, InnerJavaExprResult result, PsiElement current) {
        if (getJavaContext(element) instanceof PsiMethod) {
            PsiMethod method = (PsiMethod) getJavaContext(element);
            //noinspection ConstantConditions
            PsiType returnType = method.getReturnType();
            if (returnType == null || returnType.equals(PsiType.VOID)) {
                // cannot use \result if the method returns nothing
                result.setCorrect(false);
                holder.newAnnotation(HighlightSeverity.ERROR, ErrorMessages.NO_METHOD_RESULT).range(current).create();
                returnType = PsiType.NULL;
            }
            result.add(getDefaultValueOfType(returnType), returnType, current);
        } else {
            // do not add an error to the holder, as the semantics annotator already did that
            result.add("null", PsiType.NULL, false, current);
        }
    }

    /**
     * \type(typeName)
     * Checks the name can be resolved and replaces the expression with the typeName.class
     *
     * @param holder  the Annotation holder
     * @param result  the result up until now
     * @param current the element we are checking for
     */
    private static void checkTypeExpr(AnnotationHolder holder, InnerJavaExprResult result, PsiElement current) {
        String newText;
        boolean correct = true;
        JMLTypeName typeName = ((JMLTypeExpr) current).getTypeName();
        if (typeName == null) {
            // should not happen, but just in case
            holder.newAnnotation(HighlightSeverity.ERROR, ErrorMessages.NOT_A_TYPE_NAME).range(current).create();
            correct = false;
            newText = "null";
        }
        // special case for \TYPE
        else if (typeName.getFirstChild() != null && typeName.getFirstChild().getNode().getElementType() == JMLTypes.TYPE_CAPS) {
            newText = "java.lang.Class.class";
        } else {
            newText = getTypeString(typeName, result, holder);
        }
        result.add(newText,
                PsiType.getJavaLangClass(current.getManager(), current.getResolveScope()), correct, current);
    }

    /**
     * \nonnullelements(expr)
     * Checks the expression, and checks it returns an array, replaces the entire statement with "false"
     *
     * @param holder    the Annotation holder
     * @param extraVars an Object that holds extra variables that the Java resolver would not be able to resolve
     * @param result    the result up until now
     * @param current   the element we are checking for
     */
    private static void checkNonNullElementsExpr(AnnotationHolder holder, ExtraVariables extraVars, InnerJavaExprResult result, PsiElement current) {
        JMLInnerJavaExpr innerJavaExpr = PsiTreeUtil.getChildOfType(current, JMLInnerJavaExpr.class);
        if (innerJavaExpr == null) {
            // don't add error as parser already did so
            result.add("false", PsiType.BOOLEAN, false, current);
            return;
        }
        InnerJavaExprResult exprRes = annotateInnerJavaExpr(innerJavaExpr, holder, extraVars, false, true);
        if (exprRes.isCorrect() && (exprRes.getType().getArrayDimensions() < 1)) {
            holder.newAnnotation(HighlightSeverity.ERROR, ErrorMessages.NO_ARRAY).range(innerJavaExpr).create();
            exprRes.setCorrect(false);
        }
        result.add("false", PsiType.BOOLEAN, exprRes.isCorrect(), current);
    }

    /**
     * \elemtype(expr)
     * Checks the expression which should be an expression of type java.lang.class,
     * and checks it returns an array and then replaces the entire statement with
     * ClassName.class, removing one set of [] from ClassName
     *
     * @param holder    the Annotation holder
     * @param extraVars an Object that holds extra variables that the Java resolver would not be able to resolve
     * @param result    the result up until now
     * @param current   the element we are checking for
     */
    private static void checkElemTypeExpr(AnnotationHolder holder, ExtraVariables extraVars, InnerJavaExprResult result, PsiElement current) {
        JMLInnerJavaExpr innerJavaExpr = PsiTreeUtil.getChildOfType(current, JMLInnerJavaExpr.class);
        if (innerJavaExpr == null) {
            // parser already gave an error on this
            result.add("null", PsiType.getJavaLangClass(current.getManager(), current.getResolveScope()), false, current);
            return;
        }
        InnerJavaExprResult exprRes = annotateInnerJavaExpr(innerJavaExpr, holder, extraVars, false, true);

        String newText;
        boolean correct = true;
        if (!exprRes.isCorrect()) {
            // don't do checking
            newText = "null";
            correct = false;
        }
        // must be type of java.lang.Class
        else if (exprRes.getExpr().getType() == null || !exprRes.getExpr().getType().getCanonicalText().matches("^java\\.lang\\.Class(?:<.*>)?$")) {
            holder.newAnnotation(HighlightSeverity.ERROR, ErrorMessages.NO_CLASS_INSTANCE).range(innerJavaExpr).create();
            newText = "null";
            correct = false;
        }
        // the generic part should be an array
        else if (exprRes.getExpr().getType().getCanonicalText().endsWith("[]>")) {
            // remove one set of [] and returns the generic type + .class, unfortunately there was no robust
            // way to get the generic type, so that is why we are doing a text replacement instead
            newText = exprRes.getExpr().getType().getCanonicalText().replaceAll("^java\\.lang\\.Class<(.*)\\[]>$", "$1")
                    .replace("? extends ", "") + ".class";
        } else {
            // the generic part is not an array
            holder.newAnnotation(HighlightSeverity.ERROR, ErrorMessages.NO_ARRAY).range(innerJavaExpr).create();
            newText = "null";
            correct = false;
        }
        result.add(newText,
                PsiType.getJavaLangClass(current.getManager(), current.getResolveScope()), correct, current);
    }


    /**
     * Evaluates a quantified expression
     *
     * @param element       the inner java expression
     * @param extraVars     an Object that holds extra variables that the Java resolver would not be able to resolve
     * @param currentResult the incomplete result of the part of the java expression before the quantifier
     * @param holder        the Annotation holder
     */
    private static void evaluateQuantifiedExpr(JMLQuantifiedExpr element, ExtraVariables extraVars, InnerJavaExprResult currentResult, AnnotationHolder holder) {
        JMLQVarDecl varDecls = element.getVarDecls();
        // add the declared variables in the quantified expression to a new list
        ExtraVariables fields = getExtraVarsWithQuantifierVariables(varDecls, extraVars, holder);

        // check the predicate if it is used (as the predicate is optional)
        JMLQPredicate predicate = element.getRangePredicate();
        boolean predicateCorrect = true;
        if (predicate != null && !predicate.getText().equals("")) {
            predicateCorrect = annotateInnerJavaExpr((JMLInnerJavaExpr) predicate.getFirstChild(), holder, fields, true, true).isCorrect();
        }
        // check the spec expression (right-most expression in the quantified expression)
        JMLQSpecExpr expr = element.getSpecExpr();
        // check that it is not null
        if (expr == null) {
            // do not add a message to the Annotator, the syntax annotator already did that
            currentResult.addText("null", element);
            currentResult.setType(PsiType.NULL);
            return;
        }
        IElementType keyword = element.getKeyword();
        // check that the keyword is not null
        if (keyword == null) {
            // do not add a message to the Annotator, the syntax annotator already did that
            currentResult.addText("null", element);
            currentResult.setType(PsiType.NULL);
            return;
        }
        InnerJavaExprResult specResult;
        if (keyword == JMLTypes.FORALL || keyword == JMLTypes.EXISTS) {
            specResult = annotateInnerJavaExpr((JMLInnerJavaExpr) expr.getFirstChild(), holder, fields, true, true);
            currentResult.setType(PsiType.BOOLEAN);
        } else if (keyword == JMLTypes.NUM_OF) {
            specResult = annotateInnerJavaExpr((JMLInnerJavaExpr) expr.getFirstChild(), holder, fields, true, true);
            currentResult.setType(PsiType.LONG);
        } else {
            // is \min, \max, \sum or \product
            specResult = annotateInnerJavaExpr((JMLInnerJavaExpr) expr.getFirstChild(), holder, fields, false, true);
            if (specResult.isCorrect() && !TypeConversionUtil.isNumericType(specResult.getType())) {
                // only throw error if inner expression does not have error
                holder.newAnnotation(HighlightSeverity.ERROR, ErrorMessages.wrongType("numeric", specResult.getType())).range(expr).create();
                currentResult.setCorrect(false);
                currentResult.setType(PsiType.INT);
            } else if (specResult.isCorrect()) {
                currentResult.setType(specResult.getType());
            } else {
                currentResult.setType(PsiType.INT);
            }
        }
        // we don't want to add the text of the predicate and the spec expression, only the default value for the resulting type
        currentResult.addText(getDefaultValueOfType(currentResult.getType()), element);
        currentResult.setCorrect(currentResult.isCorrect() && predicateCorrect && specResult.isCorrect());
    }

    /**
     * Check that the references have the same visibility as the invariant
     *
     * @param classInvariant the invariant expression
     * @param visitor        the visitor after it did all its visiting (so with resolved references)
     */
    public static void checkInvariantVisibility(JMLClassInvariant classInvariant, JMLJavaExprVisitor visitor) {
        // class invariant is not in the class body, so do not do checking (semantics annotator already gave an error message on this)
        if (!CommentPosition.isInvariantOnCorrectPosition(classInvariant)) return;
        // get the class that the invariant is in
        PsiClass ourClass = (PsiClass) getJavaContext(classInvariant);
        // set booleans on whether the class is an interface, an on whether the invariant is explicitly static or instance
        boolean isInterface = ourClass != null && ourClass.isInterface();
        boolean isStatic = findFirstModifierInInvariant(classInvariant.getModifiers(), TokenSet.create(JMLTypes.STATIC)) != null;
        boolean isInstance = findFirstModifierInInvariant(classInvariant.getModifiers(), TokenSet.create(JMLTypes.INSTANCE)) != null;
        // get the visibility of the invariant
        PsiElement visibilityModifier = findFirstModifierInInvariant(classInvariant.getModifiers(), TokenSet.create(JMLTypes.PRIVATE, JMLTypes.PUBLIC, JMLTypes.PROTECTED));
        String visibility;
        if (visibilityModifier == null) {
            visibility = isInterface ? PsiModifier.PUBLIC : PsiModifier.PACKAGE_LOCAL;
        } else {
            visibility = visibilityModifier.getText();
        }
        // for every reference check that it has the same specification visibility,
        // these references have already been resolved by the visitor
        Map<PsiElement, JavaResolveResult> references = visitor.getResolvedReferences();
        for (Map.Entry<PsiElement, JavaResolveResult> ref : references.entrySet()) {
            PsiElement referredElement = ref.getValue().getElement();
            // only check if it references a field or method
            if (referredElement instanceof PsiField || referredElement instanceof PsiMethod) {
                PsiClass containingClass = PsiTreeUtil.getParentOfType(referredElement, PsiClass.class);
                // skip methods and fields that are not in our class
                if (ourClass == null || !ourClass.equals(containingClass)) {
                    continue;
                }
                // check if the field has a specification visibility
                boolean isSpecPublic = doLinkedCommentsContain(referredElement, "spec_public", false);
                boolean isSpecProtected = !isSpecPublic && doLinkedCommentsContain(referredElement, "spec_protected", false);
                PsiModifierList refModifiers = ((PsiModifierListOwner) referredElement).getModifierList();
                if (refModifiers == null) {
                    // should not happen, but just in case
                    visitor.annotateError(ref.getKey(), ErrorMessages.FIELD_NO_MODIFIERS);
                    continue;
                }
                // check that the visibility is correct, also checks implicit visibility
                //noinspection MagicConstant
                if (isSpecPublic ? !visibility.equals(PsiModifier.PUBLIC) :
                        (isSpecProtected ? !visibility.equals(PsiModifier.PROTECTED) :
                                !refModifiers.hasModifierProperty(visibility))) {
                    visitor.annotateError(ref.getKey(), ErrorMessages.INVARIANT_WRONG_VISIBILITY);
                }
                // also check static versus instance, as static invariants cannot mention instance variables
                // invariants are static by default in interfaces and instance in a class
                else if ((isStatic || (isInterface && !isInstance)) && !refModifiers.hasModifierProperty(PsiModifier.STATIC)) {
                    visitor.annotateError(ref.getKey(), ErrorMessages.INVARIANT_SHOULD_BE_STATIC);
                }
            }
        }
    }


}
