package nl.utwente.jmlplugin.annotator;

import com.intellij.codeInsight.AnnotationUtil;
import com.intellij.lang.annotation.AnnotationHolder;
import com.intellij.lang.annotation.HighlightSeverity;
import com.intellij.openapi.project.Project;
import com.intellij.pom.java.LanguageLevel;
import com.intellij.psi.*;
import com.intellij.psi.tree.IElementType;
import com.intellij.psi.util.PsiTreeUtil;
import com.intellij.psi.util.PsiTypesUtil;
import com.intellij.psi.util.TypeConversionUtil;
import nl.utwente.jmlplugin.psi.impl.JMLInnerJavaExpr;
import org.jetbrains.annotations.Nullable;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;

import static nl.utwente.jmlplugin.annotator.JMLAnnotatorUtil.doLinkedCommentsContain;
import static nl.utwente.jmlplugin.annotator.JMLAnnotatorUtil.getJavaContext;

/**
 * Visits Java PsiExpressions and checks for type errors
 */
public class JMLJavaExprVisitor extends JavaRecursiveElementVisitor {
    private final AnnotationHolder holder;
    private final RangeManager rangeManager;
    private final Project project;
    private final JMLInnerJavaExpr originalElement;
    private final Map<PsiElement, JavaResolveResult> resolvedReferences = new HashMap<>();
    private boolean noErrors = true;


    public JMLJavaExprVisitor(AnnotationHolder holder, RangeManager rangeManager, Project project, JMLInnerJavaExpr element) {
        this.holder = holder;
        this.rangeManager = rangeManager;
        this.project = project;
        this.originalElement = element;
    }

    public Map<PsiElement, JavaResolveResult> getResolvedReferences() {
        return resolvedReferences;
    }

    /**
     * Adds an error message the annotation holder
     *
     * @param element the element to use the text range of
     * @param message the error message
     */
    public void annotateError(@Nullable PsiElement element, String message) {
        if (element == null) {
            holder.newAnnotation(HighlightSeverity.ERROR, message).create();
        } else {
            holder.newAnnotation(HighlightSeverity.ERROR, message).range(rangeManager.getOriginalRange(element)).create();
        }
        noErrors = false;
    }

    /**
     * Adds an error message the annotation holder
     *
     * @param startOffset the offset where the error message should start
     * @param endOffset   the offset where the error message should stop
     * @param message     the error message
     */
    public void annotateError(int startOffset, int endOffset, String message) {
        holder.newAnnotation(HighlightSeverity.ERROR, message).range(rangeManager.getOriginalRange(startOffset, endOffset - startOffset)).create();
        noErrors = false;
    }

    public boolean isCorrect() {
        return noErrors;
    }

    /**
     * Calls this visitor on the expression
     *
     * @param expression the expression to type-check
     * @return true if no errors have been found
     */
    public boolean doChecking(@Nullable PsiElement expression, boolean ignorePrevErrors) {
        if (expression != null && (ignorePrevErrors || noErrors)) {
            expression.accept(this);
            return noErrors;
        } else if (expression == null) {
            annotateError(null, ErrorMessages.INVALID_EXPR);
        }
        return false;
    }

    /**
     * Does type checking on the given expressions
     *
     * @param multipleErrorsAllowed if false, it will stop as soon as one error is found
     * @param expressions           the expressions to type-check
     * @return true if no errors have been found
     */
    private boolean typeErrorGuard(boolean multipleErrorsAllowed, PsiElement... expressions) {
        if (!noErrors) return false;
        if (expressions != null) {
            for (PsiElement expression : expressions) {
                if (multipleErrorsAllowed || noErrors)
                    doChecking(expression, multipleErrorsAllowed);
            }
        }
        return noErrors;
    }


    /**
     * Does type checking on the (potential) children of the given expression
     *
     * @param multipleErrorsAllowed if false, it will stop as soon as one error is found
     * @param expression            the expression of which to type check the children
     * @return true if no errors have been found
     */
    @SuppressWarnings("BooleanMethodIsAlwaysInverted")
    private boolean typeErrorGuardForChildren(boolean multipleErrorsAllowed, PsiElement expression) {
        if (!noErrors) return false;
        PsiExpression[] children = PsiTreeUtil.getChildrenOfType(expression, PsiExpression.class);
        if (children != null) {
            for (PsiExpression expr : children) {
                if (multipleErrorsAllowed || noErrors) doChecking(expr, multipleErrorsAllowed);
            }
        }
        return noErrors;
    }

    /**
     * Gives error when "arrRef" is not an array, or when the index is not an int
     *
     * @param expr an expression of the form "arrRef[index]"
     */
    public void visitArrayAccessExpression(PsiArrayAccessExpression expr) {
        PsiExpression arrExpr = expr.getArrayExpression();
        PsiExpression indexExpr = expr.getIndexExpression();
        if (!typeErrorGuard(true, arrExpr, indexExpr)) return;
        // check left side is of type array
        if (arrExpr.getType() == null || arrExpr.getType().getArrayDimensions() < 1) {
            annotateError(arrExpr, ErrorMessages.NO_ARRAY_SO_NO_ACCESS);
        }
        // check right hand side can be converted to int
        if (indexExpr.getType() == null || (!indexExpr.getType().getCanonicalText().equals("java.lang.Integer")
                && !TypeConversionUtil.isIntegerNumber(indexExpr.getType().getPresentableText()))) {
            annotateError(indexExpr, ErrorMessages.wrongType("int or something that can be converted to int", indexExpr.getType()));
        }
    }

    /**
     * Always gives error that assignments are not pure
     *
     * @param expr an expression of the form "x = y"
     */
    public void visitAssignmentExpression(PsiAssignmentExpression expr) {
        annotateError(expr, ErrorMessages.ASSIGNMENT_NOT_PURE);
    }

    /**
     * Gives error when condition is not boolean
     *
     * @param expr an expression of the form "x ? y : z"
     */
    public void visitConditionalExpression(PsiConditionalExpression expr) {
        PsiExpression cond = expr.getCondition();
        if (!typeErrorGuard(true, cond,
                expr.getThenExpression(), expr.getElseExpression())) return;
        // check that condition is boolean
        if (!TypeConversionUtil.isBooleanType(cond.getType())) {
            annotateError(cond, ErrorMessages.wrongType("boolean", cond.getType()));
        }
    }

    /**
     * Gives error when right side type is null or left side does not have a type
     * or when the left and ride side are not compatible
     *
     * @param expr an expression of the form "x instanceof y"
     */
    public void visitInstanceOfExpression(PsiInstanceOfExpression expr) {
        if (!typeErrorGuard(false, expr.getOperand())) return;
        // right hand side if null or left side does not have a type
        if (expr.getCheckType() == null || expr.getOperand().getType() == null) {
            annotateError(expr, ErrorMessages.INVALID_EXPR);
        }
        // left cannot be casted to right
        else if (!TypeConversionUtil.areTypesConvertible(expr.getOperand().getType(), expr.getCheckType().getType())) {
            annotateError(expr, ErrorMessages.wrongInstanceOf(expr.getOperand().getType(), expr.getCheckType().getType()));
        }
    }

    /**
     * Give error when literal expression has the wrong syntax
     *
     * @param expr an expression of the from "'a'", ""text"", "0" or any other literal
     */
    public void visitLiteralExpression(PsiLiteralExpression expr) {
        // check that the String ends properly
        if (expr.getText().startsWith("\"") && !expr.getText().endsWith("\"")) {
            annotateError(expr, ErrorMessages.STRING_NO_END);
        }
        // check that a char ends properly
        else if (expr.getText().startsWith("'") && !expr.getText().endsWith("'")) {
            annotateError(expr, ErrorMessages.CHAR_NO_END);
        }
        // check for any other values, "null" is a valid literal though
        else if (!expr.getText().equals("null") && expr.getValue() == null) {
            annotateError(expr, ErrorMessages.INCORRECT_SYNTAX);
        }
    }

    /**
     * Calls visitor on expression between parentheses
     *
     * @param expr an expression of the form "(expression)"
     */
    public void visitParenthesizedExpression(PsiParenthesizedExpression expr) {
        typeErrorGuard(false, expr.getExpression());
    }

    /**
     * Gives error when left and right are not valid types for the operator
     *
     * @param expr an expression of the form "x && y && z", all have the same operator
     */
    public void visitPolyadicExpression(PsiPolyadicExpression expr) {
        IElementType tokenType = expr.getOperationTokenType();
        PsiExpression[] operands = expr.getOperands();
        if (operands.length > 0) {
            PsiExpression lOp = operands[0];
            if (!typeErrorGuard(false, lOp)) return;
            // for each pair of operands that are next to each other, check whether the types are allowed
            for (int i = 1; i < operands.length; i++) {
                PsiExpression rOp = operands[i];
                if (!typeErrorGuard(false, rOp)) return;
                if (!TypeConversionUtil.isBinaryOperatorApplicable(tokenType, lOp, rOp, false)) {
                    annotateError(lOp.getTextRange().getEndOffset(), rOp.getTextRange().getStartOffset(), ErrorMessages.wrongPolyadic(lOp, rOp));
                    return;
                }
                lOp = rOp;
            }
        } else {
            annotateError(expr, ErrorMessages.INVALID_EXPR);
        }

    }

    /**
     * Gives error when the reference cannot be resolved or is not visible from the caller
     *
     * @param reference a reference, usually created from a PsiIdentifier element
     */
    public void visitReferenceElement(PsiJavaCodeReferenceElement reference) {
        if (!typeErrorGuardForChildren(true, reference)) return;
        JavaResolveResult resolved = reference.advancedResolve(false);
        if (!resolved.isValidResult() && !isSpecVisibilityValid(resolved)) {
            annotateError(reference, ErrorMessages.REFERENCE_UNRESOLVED);
        } else {
            resolvedReferences.put(reference, resolved);
        }
    }

    /**
     * Gives error when the reference cannot be resolved
     *
     * @param expr a reference expression, usually created from a PsiIdentifier element
     */
    public void visitReferenceExpression(PsiReferenceExpression expr) {
        visitReferenceElement(expr);
    }

    /**
     * Gives an error when an array is created, but has dimensions that are not int,
     * or when initializers are of the wrong type. Or when a class is initialized,
     * when the constructor cannot be found
     *
     * @param expr an expression of the form "new int[0]" or "new Object()"
     */
    public void visitNewExpression(PsiNewExpression expr) {
        if (expr.isArrayCreation()) {
            // only gets filled dimensions, so for "new int[0][]", it only return 0 here
            PsiExpression[] arrayDimensions = expr.getArrayDimensions();
            // check all dimensions or of type int
            for (PsiExpression dimExpr : arrayDimensions) {
                if (typeErrorGuard(false, dimExpr)) {
                    if (dimExpr.getType() == null) {
                        // should not happen, but just in case
                        annotateError(dimExpr, ErrorMessages.TYPE_UNKNOWN);
                    }
                    if (!dimExpr.getType().getCanonicalText().equals("java.lang.Integer") && !TypeConversionUtil.isIntegerNumber(dimExpr.getType().getPresentableText())) {
//                    if (!TypeConversionUtil.areTypesConvertible(dimExpr.getType(), PsiType.INT)) {
                        annotateError(dimExpr, ErrorMessages.ARRAY_DIM_NO_INT);
                    }
                }
            }
            PsiArrayInitializerExpression arrayInitializers = expr.getArrayInitializer();
            PsiType type = expr.getType();
            if (!(expr.getType() instanceof PsiArrayType)) {
                // should not happen, but just in case
                annotateError(expr, ErrorMessages.TYPE_UNKNOWN);
                return;
            }
            PsiType arrType = ((PsiArrayType) type).getComponentType();
            if (arrayInitializers != null) {
                PsiExpression[] arrayInitializerExpressions = arrayInitializers.getInitializers();
                for (PsiExpression initializer : arrayInitializerExpressions) {
                    if (!typeErrorGuard(false, initializer)) return;
                    if (initializer.getType() == null) {
                        // should not happen, but just in case
                        annotateError(expr, ErrorMessages.TYPE_UNKNOWN);
                    }
                    // initializer not of same type as array
                    else if (!initializer.getType().isConvertibleFrom(arrType)) {
                        annotateError(initializer, ErrorMessages.ARRAY_INITIALIZER_WRONG_TYPE);
                    }
                }
            }
        } else {
            // is class creation
            PsiJavaCodeReferenceElement ref = expr.getClassReference();
            if (!typeErrorGuard(false, ref)) return;
            // check if reference to the class has been resolved
            if (resolvedReferences.containsKey(ref)) {
                PsiElement found = resolvedReferences.get(ref).getElement();
                // Not a class
                if (!(found instanceof PsiClass)) {
                    annotateError(ref, ErrorMessages.NOT_A_CLASS);
                    return;
                }

                // check that the argument list is not null, should not happen
                if (expr.getArgumentList() == null) {
                    annotateError(expr, ErrorMessages.INVALID_EXPR);
                    return;
                }
                // find the constructor if it exists
                // call to default constructor
                if (((PsiClass) found).getConstructors().length == 0 && expr.getArgumentList().getExpressionCount() == 0) {
                    return;
                }
                // call to a user defined constructor
                JavaResolveResult result = JavaPsiFacade.getInstance(project).getResolveHelper().
                        resolveConstructor(PsiTypesUtil.getClassType((PsiClass) found), expr.getArgumentList(), expr);
                if (!result.isValidResult() && !isSpecVisibilityValid(result)) {
                    // user defined constructor does not exist
                    annotateError(expr, ErrorMessages.CONSTRUCTOR_UNRESOLVED);
                }


            }

        }
    }

    /**
     * Gives an error if the method could not be resolved and a warning when it is not pure
     *
     * @param expr an expression of the form "method(param1, param2)"
     */
    public void visitCallExpression(PsiCallExpression expr) {
        // check the expression before the method call if applicable
        // for example ((OtherClass) variable).callMethod(), then it should check ((OtherClass) variable) first.
        if (expr.getFirstChild() != null && expr.getFirstChild().getFirstChild() instanceof PsiExpression) {
            if (!typeErrorGuardForChildren(false, expr.getFirstChild())) return;
        }
        // check the parameters
        PsiExpressionList parameters = PsiTreeUtil.getChildOfType(expr, PsiExpressionList.class);
        if (parameters != null && parameters.getExpressionCount() > 0) {
            if (!typeErrorGuard(false, parameters.getExpressions())) return;
        }
        // find the reference
        JavaResolveResult result = expr.resolveMethodGenerics();
        if (result.isValidResult() && result.getElement() instanceof PsiMethod) {
            resolvedReferences.put(expr, result);
            checkPurenessOfMethod(expr, result);
            return;
        } else if (result.getElement() instanceof PsiMethod && isSpecVisibilityValid(result)) {
            resolvedReferences.put(expr, result);
            checkPurenessOfMethod(expr, result);
            return;
        }
        annotateError(expr, ErrorMessages.METHOD_UNRESOLVED);
    }

    // return true when valid

    /**
     * Checks that a reference can be found because according to spec visibility rules
     *
     * @param result the resolved field, method or class
     * @return true if it can be found according to spec visibility rules
     */
    private boolean isSpecVisibilityValid(JavaResolveResult result) {
        // can still be valid through spec_public or spec_protected
        PsiElement elem = result.getElement();
        if (elem != null && JMLAnnotatorUtil.doLinkedCommentsContain(elem, "spec_public", false)) {
            return true;
        }
        // for spec_protected, it is allowed if it is in the same package or the caller is a subclass
        else if (elem != null && JMLAnnotatorUtil.doLinkedCommentsContain(elem, "spec_protected", false)) {
            // get the classes containing the resolved reference and the JML comment that is referencing
            PsiClass elemClass = elem instanceof PsiClass ? (PsiClass) elem : PsiTreeUtil.getParentOfType(elem, PsiClass.class);
            PsiElement javaElem = getJavaContext(originalElement);
            PsiClass originalClass = javaElem instanceof PsiClass ? (PsiClass) javaElem : PsiTreeUtil.getParentOfType(javaElem, PsiClass.class);
            // true if they has the same package name or if the class containing the JML comment is a subclass of class containing the resolved element
            return elemClass != null && elemClass.getQualifiedName() != null && originalClass != null && originalClass.getQualifiedName() != null
                    && (elemClass.getQualifiedName().replaceAll("\\..+$", "").equals(originalClass.getQualifiedName().replaceAll("\\..+$", ""))
                    || Arrays.asList(originalClass.getSupers()).contains(elemClass));
        }
        return false;
    }

    /**
     * Checks whether the called method is pure and gives a warning when not pure
     *
     * @param expr   the call expression
     * @param result the found method
     */
    private void checkPurenessOfMethod(PsiCallExpression expr, JavaResolveResult result) {
        // check that the user put JML pure above method
        //noinspection ConstantConditions
        if (!doLinkedCommentsContain(result.getElement(), "pure", false)) {
            // if use did not use @pure, so look for IntelliJ contracts (also inferred ones)
            PsiAnnotation[] annotations = AnnotationUtil.getAllAnnotations((PsiMethod) result.getElement(), true, null, true);
            boolean pureFound = false;
            for (PsiAnnotation annotation : annotations) {
                // found a contract
                if ("org.jetbrains.annotations.Contract".equals(annotation.getQualifiedName())) {
                    PsiAnnotationMemberValue pureVal = annotation.findAttributeValue("pure");
                    // check whether there is a value for pure and whether that value equals true
                    if (pureVal != null && JavaPsiFacade.getInstance(project).getConstantEvaluationHelper().computeConstantExpression(pureVal, false).equals(true)) {
                        pureFound = true;
                        break;
                    }
                }
            }
            if (!pureFound) {
                this.holder.newAnnotation(HighlightSeverity.WARNING, ErrorMessages.METHOD_NOT_PURE).range(rangeManager.getOriginalRange(expr)).create();
            }
        }
    }


    /**
     * Gives an error is the cast is not allowed or a warning when the trying to cast to a sub-class
     *
     * @param expr expression of the form "(Class) expression"
     */
    public void visitTypeCastExpression(PsiTypeCastExpression expr) {
        PsiExpression operand = expr.getOperand();
        PsiTypeElement castType = expr.getCastType();
        if (!typeErrorGuard(true, castType, operand)) return;
        //noinspection ConstantConditions
        if (operand.getType() == null) {
            annotateError(expr, ErrorMessages.INCOMPATIBLE_CAST);
        } else //noinspection ConstantConditions
            if (!TypeConversionUtil.areTypesConvertible(operand.getType(), castType.getType(), LanguageLevel.HIGHEST)) {
                annotateError(expr, ErrorMessages.wrongCast(operand.getType(), castType.getType()));
            }
            // give a warning when trying to cast to a sub-class
            else if (Arrays.asList(castType.getType().getSuperTypes()).contains(operand.getType())) {
                this.holder.newAnnotation(HighlightSeverity.WARNING, ErrorMessages.castToSubType(
                        operand.getType(), castType.getType())).range(rangeManager.getOriginalRange(expr)).create();
            }
    }

    /**
     * Gives error when the operators is not allowed on the type of the operand
     *
     * @param expr an expression of the form "i++"
     */
    public void visitUnaryExpression(PsiUnaryExpression expr) {
        PsiExpression operand = expr.getOperand();
        if (!typeErrorGuard(false, operand)) return;
        PsiJavaToken sign = expr.getOperationSign();
        // check that it is a reference for ++ and --
        if ((sign.getTokenType() == JavaTokenType.PLUSPLUS || sign.getTokenType() == JavaTokenType.MINUSMINUS)
                && !(operand instanceof PsiReferenceExpression)) {
            annotateError(expr, ErrorMessages.VARIABLE_EXPECTED);
        }
        // check that operator is allowed
        else if (!TypeConversionUtil.isUnaryOperatorApplicable(sign, operand)) {
            //noinspection ConstantConditions
            if (operand.getType() == null) {
                annotateError(expr, ErrorMessages.INVALID_EXPR);
            } else {
                annotateError(expr, ErrorMessages.wrongUnary(sign.getText(), operand.getType()));
            }
        }
    }
}
