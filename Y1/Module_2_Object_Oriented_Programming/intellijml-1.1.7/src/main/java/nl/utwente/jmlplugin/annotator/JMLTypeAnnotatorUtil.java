package nl.utwente.jmlplugin.annotator;

import com.intellij.lang.annotation.AnnotationHolder;
import com.intellij.lang.annotation.HighlightSeverity;
import com.intellij.psi.*;
import com.intellij.psi.tree.IElementType;
import com.intellij.psi.util.PsiTreeUtil;
import com.intellij.psi.util.PsiTypesUtil;
import com.intellij.psi.util.TypeConversionUtil;
import com.intellij.util.IncorrectOperationException;
import nl.utwente.jmlplugin.psi.JMLLoopInvariant;
import nl.utwente.jmlplugin.psi.JMLReferenceType;
import nl.utwente.jmlplugin.psi.JMLTokenSet;
import nl.utwente.jmlplugin.psi.impl.JMLInnerJavaExpr;
import nl.utwente.jmlplugin.psi.impl.JMLQVarDecl;
import nl.utwente.jmlplugin.psi.impl.JMLQVarDeclIdentifier;
import org.jetbrains.annotations.NotNull;

import java.util.List;

import static nl.utwente.jmlplugin.annotator.JMLAnnotatorUtil.getCommentContext;
import static nl.utwente.jmlplugin.annotator.JMLAnnotatorUtil.getJavaContext;

/**
 * Util class for JMLTypeAnnotator, deals with java expressions in text from and extra variables
 */
class JMLTypeAnnotatorUtil {
    /**
     * Generates a PSI tree representation of a Java expression from the given text
     *
     * @param element the Java expression element from the JML tree
     * @param result  the result of type checking and replacing certain expressions
     * @param holder  the holder for error messages
     * @return a PSI tree representation of a Java expression
     */
    protected static PsiExpression getJavaExprFromText(@NotNull JMLInnerJavaExpr element, InnerJavaExprResult result, AnnotationHolder holder) {
        PsiExpression expr;
        try {
            // try to parse the text as java
            expr = JavaPsiFacade.getInstance(element.getProject()).getElementFactory().createExpressionFromText(result.getText().replaceAll("[\\s;]+$", ""), getJavaContext(element));
        } catch (IncorrectOperationException e) {
            // A more specific error message is not available when this happens
            holder.newAnnotation(HighlightSeverity.ERROR, ErrorMessages.INVALID_EXPR).range(element).create();
            return null;
        }
        // if there are errors in the tree, display them to the user
        boolean errorFound = false;
        for (PsiErrorElement error : PsiTreeUtil.findChildrenOfType(expr, PsiErrorElement.class)) {
            holder.newAnnotation(HighlightSeverity.ERROR, error.getErrorDescription()).range(result.getRangeManager().getOriginalRange(error)).create();
            errorFound = true;
        }
        return errorFound ? null : expr;
    }

    /**
     * Returns a text replacement for the variable if there is one in ExtraVariables
     *
     * @param ident     the identifier holding the variable name
     * @param extraVars the holder of extra variables
     * @return a string containing the replacements
     */
    protected static String getReplacementIfNeeded(PsiIdentifier ident, ExtraVariables extraVars) {
        PsiElement next = PsiTreeUtil.skipWhitespacesAndCommentsForward(ident);
        PsiElement prev = PsiTreeUtil.skipWhitespacesAndCommentsBackward(ident);
        // if it is a method or constructor call (next element is '(')
        // or has a parent (previous element is '.'), then do not replace
        if ((next != null && next.getNode().getElementType() == JavaTokenType.LPARENTH)
                || (prev != null && prev.getNode().getElementType() == JavaTokenType.DOT)) {
            return ident.getText();
        }
        //see if we can get a replacement
        PsiType type;
        if ((type = extraVars.findVarAndGetType(ident.getText())) != null) {
            // the parentheses are needed, so for example a variable 'x' of type 'int[]' becomes "(new int[0])",
            // so when we have indexing such as 'x[5]', it becomes "(new int[0])[5]", if you didn't have the parentheses
            // it would create a 2 dimensional array instead
            return "(" + getDefaultValueOfType(type) + ")";
        }
        return ident.getText();

    }

    /**
     * Get the representation text of the type in a String (a classname + .class)
     *
     * @param element the element holding the reference
     * @param result  the result of type checking and replacing certain expressions
     * @param holder  the holder for error messages
     * @return a string containing the type representation
     */
    public static String getTypeString(@NotNull PsiElement element, InnerJavaExprResult result, AnnotationHolder holder) {
        PsiElement ident = element.getFirstChild();
        if (ident != null) {
            IElementType elemType = ident.getNode().getElementType();
            // is primitive name such as int, boolean, etc
            if (JMLTokenSet.javaPrimitives.contains(elemType))
                return element.getText() + ".class";
            // not a primitive, so need to see whether it is a reference to a classname
            PsiJavaCodeReferenceElement classReference;
            try {
                // find the class
                classReference = JavaPsiFacade.getElementFactory(element.getProject()).createReferenceFromText(ident.getText(), element.getContext());
            } catch (IncorrectOperationException e) {
                holder.newAnnotation(HighlightSeverity.ERROR, ErrorMessages.INCORRECT_REFERENCE).create();
                result.setCorrect(false);
                return PsiKeyword.NULL;
            }
            JavaResolveResult resolveResult = classReference.advancedResolve(false);
            if (resolveResult.isValidResult() && resolveResult.getElement() instanceof PsiClass) {
                // class exists, so return replacement
                return ((PsiClass) resolveResult.getElement()).getQualifiedName() + ".class";
            }
        }
        holder.newAnnotation(HighlightSeverity.ERROR, ErrorMessages.NOT_A_TYPE_NAME).range(ident != null ? ident : element).create();
        result.setCorrect(false);
        return "java.lang.Class.class";
    }

    /**
     * Gets the default value of the type
     *
     * @param type the type to get the default value for
     * @return a String containing the default value
     */
    protected static String getDefaultValueOfType(PsiType type) {
        if (type instanceof PsiClassType) {
            return "((" + type.getCanonicalText() + ") null)";
        } else if (type instanceof PsiPrimitiveType) {
            // there was no internal function for this, so we do it ourselves
            switch (type.getCanonicalText()) {
                case "boolean":
                    return "false";
                case "byte":
                    return "(byte)0";
                case "char":
                    return "'\0'";
                case "short":
                    return "(short)0";
                case "int":
                    return "0";
                case "long":
                    return "0L";
                case "float":
                    return "0F";
                case "double":
                    return "0D";
                default:
                    return "null";
            }
        } else if(type instanceof PsiArrayType array) {
            PsiType arrayType = array.getComponentType();
            return String.format("(new %s[]{})", arrayType.getCanonicalText());
        }
        // just in case
        return "(" + PsiTypesUtil.getDefaultValueOfType(type) + ")";
    }

    /**
     * Checks whether the expression is boolean
     *
     * @param expr         the expression to check for
     * @param holder       the holder for error messages
     * @param rangeManager the current range manager
     * @return true if the expression is boolean
     */
    protected static boolean checkExprIsBoolean(PsiExpression expr, AnnotationHolder holder, RangeManager rangeManager) {
        PsiType type = expr.getType();
        // check if expression returns a boolean
        if (!TypeConversionUtil.isBooleanType(type)) {
            holder.newAnnotation(HighlightSeverity.ERROR, ErrorMessages.wrongType("boolean", type)).range(rangeManager.getOriginalRange(expr)).create();
            return false;
        }
        return true;
    }

    /**
     * Returns a new instance of ExtraVariables instance holding variables declared in a quantified expressions plus the old variables
     * and checks that they have not been defined already
     *
     * @param varDecl   the variable declaration tree element in the JML tree
     * @param extraVars the original ExtraVariables instance
     * @param holder    the holder for error messages
     * @return a new instance of ExtraVariables holding variables declared in a quantified expressions plus the old variables
     */
    protected static ExtraVariables getExtraVarsWithQuantifierVariables(JMLQVarDecl varDecl, ExtraVariables extraVars, AnnotationHolder holder) {
        ExtraVariables myExtraVars = new ExtraVariables(extraVars);
        if (varDecl == null || varDecl.getTypeName() == null) return myExtraVars;
        String typeStr = varDecl.getTypeName().getText();
        try {
            // try to get the type of the new variables
            PsiType type = JavaPsiFacade.getInstance(varDecl.getProject()).getElementFactory().createTypeFromText(typeStr, getJavaContext(varDecl));
            List<JMLQVarDeclIdentifier> vars = varDecl.getIdentifiers();
            for (JMLQVarDeclIdentifier var : vars) {
                // only add it to the map if it is valid, the check throws the error too
                if (checkIfExtraVariableAllowed(var, extraVars, holder)) {
                    myExtraVars.add(var.getText(), type);
                }
            }
        } catch (IncorrectOperationException e) {
            holder.newAnnotation(HighlightSeverity.ERROR, ErrorMessages.INVALID_EXPR).create();
        }
        return myExtraVars;
    }

    /**
     * Adds the variable declared in a signals clauses to ExtraVariables
     *
     * @param name      the name of the variable
     * @param typeName  the name of the type
     * @param extraVars the original ExtraVariables instance
     * @param holder    the holder for error messages
     */
    protected static void addSignalsVariable(PsiElement name, JMLReferenceType typeName, ExtraVariables extraVars, AnnotationHolder holder) {
        try {
            PsiType type = JavaPsiFacade.getInstance(name.getProject()).getElementFactory().createTypeFromText(typeName.getText(), getJavaContext(name));
            // only add it to the map if it is valid, the check throws the error too
            if (checkIfExtraVariableAllowed(name, extraVars, holder)) {
                extraVars.add(name.getText(), type);
            }
        } catch (IncorrectOperationException e) {
            holder.newAnnotation(HighlightSeverity.ERROR, ErrorMessages.INVALID_EXPR).create();
        }
    }

    /**
     * Adds the parameters of the method to ExtraVariables
     *
     * @param method    the method to add the parameters of
     * @param extraVars the original ExtraVariables instance
     */
    protected static void addParameterVariables(PsiMethod method, ExtraVariables extraVars) {
        PsiParameter[] params = method.getParameterList().getParameters();
        for (PsiParameter param : params) {
            extraVars.add(param.getName(), param.getType());
        }
    }

    /**
     * Adds the initializers of the loop that the loop invariant belongs to to ExtraVariables
     *
     * @param elem      the loop invariant
     * @param extraVars the original ExtraVariables instance
     */
    protected static void addLoopInitializers(JMLLoopInvariant elem, ExtraVariables extraVars) {
        PsiElement javaContext = getCommentContext(elem);
        PsiElement loop = PsiTreeUtil.skipWhitespacesAndCommentsForward(javaContext);
        if (loop instanceof PsiForStatement) {
            PsiStatement initializer = ((PsiForStatement) loop).getInitialization();
            for (PsiLocalVariable localVar : PsiTreeUtil.getChildrenOfTypeAsList(initializer, PsiLocalVariable.class)) {
                extraVars.add(localVar.getName(), localVar.getType());
            }
        } else if (loop instanceof PsiForeachStatement) {
            PsiParameter initializer = ((PsiForeachStatement) loop).getIterationParameter();
            extraVars.add(initializer.getName(), initializer.getType());
        }
    }

    /**
     * Checks whether a new variable is allowed to be added to the current instance of ExtraVariables
     *
     * @param element   the element holding a reference to a variable
     * @param extraVars the original ExtraVariables instance
     * @param holder    the holder for error messages
     * @return false if it is not allowed
     */
    protected static boolean checkIfExtraVariableAllowed(PsiElement element, ExtraVariables extraVars, AnnotationHolder holder) {
        if (extraVars.contains(element.getText())) {
            // variable already exists in extra variable list
            holder.newAnnotation(HighlightSeverity.ERROR, ErrorMessages.OVERRIDING_LOCAL_VAR).range(element).create();
            return false;
        }
        PsiExpression ref;
        PsiElement javaContext = getJavaContext(element);
        try {
            // make an expression out of the variable name
            ref = JavaPsiFacade.getElementFactory(element.getProject()).createExpressionFromText(element.getText(), javaContext);
        } catch (IncorrectOperationException e) {
            return true;
        }
        // not a reference
        if (!(ref instanceof PsiJavaCodeReferenceElement)) {
            return true;
        }
        PsiElement resolved = ((PsiJavaCodeReferenceElement) ref).resolve();
        if (resolved != null && !(resolved instanceof PsiField)) {
            // variable already exists in the code block
            holder.newAnnotation(HighlightSeverity.ERROR, ErrorMessages.OVERRIDING_LOCAL_VAR).range(element).create();
            return false;
        }
        // if it is above a method, also check that it is not in the parameter list, it cannot resolve that automatically
        else if (resolved == null && javaContext instanceof PsiMethod) {
            for (PsiParameter p : ((PsiMethod) javaContext).getParameterList().getParameters()) {
                if (p.getName().equals(element.getText())) {
                    holder.newAnnotation(HighlightSeverity.ERROR, ErrorMessages.OVERRIDING_LOCAL_VAR).range(element).create();
                    return false;
                }
            }

        }
        return true;
    }
}
