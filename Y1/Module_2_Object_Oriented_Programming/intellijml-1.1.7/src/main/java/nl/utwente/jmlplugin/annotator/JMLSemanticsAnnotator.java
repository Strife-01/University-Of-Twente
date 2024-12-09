package nl.utwente.jmlplugin.annotator;

import com.intellij.lang.annotation.AnnotationHolder;
import com.intellij.lang.annotation.HighlightSeverity;
import com.intellij.psi.*;
import com.intellij.psi.tree.IElementType;
import com.intellij.psi.tree.TokenSet;
import nl.utwente.jmlplugin.psi.*;
import nl.utwente.jmlplugin.psi.impl.JMLInnerJavaExpr;
import nl.utwente.jmlplugin.psi.impl.JMLOldExpr;
import org.jetbrains.annotations.NotNull;

import static com.intellij.psi.util.PsiTreeUtil.*;
import static nl.utwente.jmlplugin.annotator.JMLAnnotatorUtil.*;

/**
 * Checks the tree for semantic errors
 */
public class JMLSemanticsAnnotator extends InnerJavaExprResult {

    JMLSemanticsAnnotator(JMLInnerJavaExpr expr) {
        super(expr);
    }

    /**
     * Annotates the elements on semantic errors
     *
     * @param element the element we are checking
     * @param jmlRoot the root of the JML tree
     * @param holder  the Annotation holder
     * @return false if the element has an error
     */
    public static boolean annotateSemantics(@NotNull PsiElement element, JMLJmlSpecification jmlRoot, @NotNull AnnotationHolder holder) {
        if (!checkSpecAllowedHere(element, jmlRoot, holder)) return false;
        // specification is allowed at its position in the Java file, so check for errors now
        // return true on warnings
        if (element instanceof JMLMethodJml && checkModifierBeforeSpecClauses((JMLMethodJml) element)) {
            holder.newAnnotation(HighlightSeverity.ERROR, ErrorMessages.NO_MODIFIER_BEFORE_SPEC).create();
        } else if (element instanceof JMLLoopInvariant && checkLoopInvariantAboveLoop((JMLLoopInvariant) element)) {
            holder.newAnnotation(HighlightSeverity.ERROR, ErrorMessages.LOOP_INVARIANT_NOT_ABOVE_LOOP).create();
        } else if (element instanceof JMLSignalsOnlyClause && checkMultipleSignalsOnly((JMLSignalsOnlyClause) element)) {
            holder.newAnnotation(HighlightSeverity.WARNING, ErrorMessages.MULTIPLE_SIGNALS_ONLY).create();
            return true;
        } else if ((element instanceof JMLRequiresClause || element.getParent() instanceof JMLSpecBody) && checkRedundantNotSpecified(element)) {
            holder.newAnnotation(HighlightSeverity.WARNING, ErrorMessages.NOT_SPECIFIED_REDUNDANT).create();
            return true;
        } else if (element.getNode().getElementType() == JMLTypes.RESULT && checkBackslashResultAllowed(element)) {
            holder.newAnnotation(HighlightSeverity.ERROR, ErrorMessages.BACKSLASH_RESULT_NOT_ALLOWED).create();
        } else if (element instanceof JMLOldExpr && checkOldExprAllowed((JMLOldExpr) element)) {
            holder.newAnnotation(HighlightSeverity.ERROR, ErrorMessages.OLD_EXPR_NOT_ALLOWED).create();
        } else if (JMLTokenSet.allModifiers.contains(element.getNode().getElementType())) {
            CommentPosition modifierPosition = CommentPosition.getModifierPosition(element);
            if (checkModifierAllowedHere(element.getNode().getElementType(), modifierPosition)) {
                holder.newAnnotation(HighlightSeverity.ERROR, ErrorMessages.modifierNotAllowedHere(element.getText(), modifierPosition)).create();
            } else if (element.getNode().getElementType() == JMLTypes.HELPER && checkHelperNotAllowed(element)) {
                holder.newAnnotation(HighlightSeverity.ERROR, ErrorMessages.HELPER_NOT_ALLOWED).create();
            } else if (checkMultipleVisibilityModifiers(element)) {
                holder.newAnnotation(HighlightSeverity.ERROR, ErrorMessages.MULTIPLE_VISIBILITY_MODIFIERS).create();
            } else if (checkMultipleSpecVisibilityModifiers(element, modifierPosition)) {
                holder.newAnnotation(HighlightSeverity.ERROR, ErrorMessages.MULTIPLE_SPEC_VISIBILITY_MODIFIERS).create();
            } else if (checkStaticAndInstance(element)) {
                holder.newAnnotation(HighlightSeverity.ERROR, ErrorMessages.STATIC_AND_INSTANCE).create();
            } else if (checkDuplicateModifiers(element, modifierPosition)) {
                holder.newAnnotation(HighlightSeverity.WARNING, ErrorMessages.DUPLICATE_MODIFIER).create();
                return true;
            } else {
                return true;
            }
        } else {
            return true;
        }
        return false;
    }


    /**
     * Checks whether a specification is allowed at its position in the Java file
     *
     * @param element an element in the JML PSI Tree
     * @param jmlRoot the root element in the JML PSI Tree
     * @param holder  the Annotation holder
     * @return false if the specification is not allowed at its position in the Java file
     */
    private static boolean checkSpecAllowedHere(PsiElement element, JMLJmlSpecification jmlRoot, AnnotationHolder holder) {
        CommentPosition position = CommentPosition.getCommentPosition(jmlRoot);
        // see whether it is a method spec, class invariant, modifiers or in-method specification
        PsiElement jmlSpecKind = getChildOfAnyType(jmlRoot, JMLMethodJml.class,
                JMLClassInvariant.class, JMLModifiers.class, JMLInMethodSpec.class);
        boolean allowed = false;
        if (jmlSpecKind != null) {
            switch (position) {
                case FIELD:
                case ABOVE_CLASS:
                case PARAMETER:
                case VAR_DECLARATION:
                    allowed = jmlSpecKind instanceof JMLModifiers;
                    break;
                case INSIDE_CLASS:
                    allowed = jmlSpecKind instanceof JMLClassInvariant;
                    break;
                case ABOVE_METHOD:
                    allowed = jmlSpecKind instanceof JMLModifiers || jmlSpecKind instanceof JMLMethodJml;
                    break;
                case BEFORE_METHOD_BODY:
                    allowed = jmlSpecKind instanceof JMLMethodJml;
                    break;
                case CODE_BLOCK:
                    allowed = jmlSpecKind instanceof JMLInMethodSpec;
                    break;
                default:
                    break;
            }
            if (!allowed && element instanceof JMLFile) {
                // only show the error on the file PSI element
                holder.newAnnotation(HighlightSeverity.ERROR,
                        ErrorMessages.specKindNotAllowedHere(jmlSpecKind, position)).range(jmlRoot.getTextRange()).create();
            }
        }
        return allowed;
    }

    /**
     * Checks whether modifiers have been placed after specification cases
     *
     * @param element the PsiErrorElement for which we are checking
     * @return true if this error has occurred.
     */
    private static boolean checkModifierBeforeSpecClauses(JMLMethodJml element) {
        // we skip the current comment because that already throws an error in the parser,
        // and is caught by the SyntaxAnnotator
        return doPrevCommentsContain(element, ALL_MODIFIERS_REGEX, false, false);
    }

    /**
     * Checks whether the are multiple signals_only clauses
     *
     * @param element The element which contains the clauses
     * @return true if there are multiple signals_only clauses
     */
    private static boolean checkMultipleSignalsOnly(JMLSignalsOnlyClause element) {
        return doPrevCommentsContain(element, "signals_only", true, true);
    }

    /**
     * Checks whether a modifier is allowed on a certain spot in the Java file
     *
     * @param modifier the modifier we are checking for
     * @param position the position of the modifier in the Java file
     * @return true if this error has occurred
     */
    private static boolean checkModifierAllowedHere(IElementType modifier, CommentPosition position) {
        switch (position) {
            case FIELD:
                return !JMLTokenSet.fieldModifiers.contains(modifier);
            case ABOVE_METHOD:
                return !JMLTokenSet.methodDeclModifiers.contains(modifier);
            case ABOVE_CONSTRUCTOR:
                return !TokenSet.andNot(JMLTokenSet.methodDeclModifiers, TokenSet.create(JMLTypes.NULLABLE)).contains(modifier);
            case CLASS_INVARIANT:
                return !JMLTokenSet.invariantModifiers.contains(modifier);
            case ABOVE_CLASS:
                return !JMLTokenSet.classModifiers.contains(modifier);
            case PARAMETER:
            case VAR_DECLARATION:
                return modifier != JMLTypes.NULLABLE;
            default:
                return true;
        }
    }

    /**
     * Checks whether both static and instance are used
     *
     * @param element A modifier
     * @return true if the modifier appeared already
     */
    private static boolean checkStaticAndInstance(PsiElement element) {
        // do not have to check across comments because this is per invariant
        if (element.getNode().getElementType() == JMLTypes.STATIC) {
            return doPrevInvariantModifiersContain(element, TokenSet.create(JMLTypes.INSTANCE));
        }
        if (element.getNode().getElementType() == JMLTypes.INSTANCE) {
            return doPrevInvariantModifiersContain(element, TokenSet.create(JMLTypes.STATIC));
        }
        return false;

    }

    /**
     * Checks that the helper modifier is allowed (method needs a pure modifier, or needs to be private)
     *
     * @param element the helper modifier element
     * @return true if this error has occurred
     */
    private static boolean checkHelperNotAllowed(PsiElement element) {
        // check if the method is annotated with pure
        if (doLinkedCommentsContain(element, "pure", false))
            return false;
        // not annotated with pure, so check if the method is private
        PsiElement method = getJavaContext(element);
        if (method == null) return false;
        PsiModifierList modifierList = getChildOfType(method, PsiModifierList.class);
        if (modifierList == null) return false;
        return !modifierList.hasModifierProperty(PsiModifier.PRIVATE);
    }


    /**
     * Checks whether another visibility modifier already appeared
     *
     * @param element A modifier
     * @return true if the modifier appeared already
     */
    private static boolean checkMultipleVisibilityModifiers(PsiElement element) {
        if (!JMLTokenSet.visibilityModifiers.contains(element.getNode().getElementType()))
            return false; // element is not a modifier we are checking for
        return doPrevInvariantModifiersContain(element, TokenSet.andNot(JMLTokenSet.visibilityModifiers, TokenSet.create(element.getNode().getElementType())));
    }

    /**
     * Checks whether another specification visibility modifier already appeared
     *
     * @param element A modifier
     * @return true if the modifier appeared already
     */
    private static boolean checkMultipleSpecVisibilityModifiers(PsiElement element, CommentPosition position) {
        if (!JMLTokenSet.specVisibilityModifiers.contains(element.getNode().getElementType()))
            return false; // element is not a modifier we are checking for
        return doPrevCommentsContain(element, "spec_protectedspec_public".replace(element.getText().trim(), ""), false, true);
    }

    /**
     * Checks whether the modifier already appeared
     *
     * @param element A modifier
     * @return true if the modifier appeared already
     */
    private static boolean checkDuplicateModifiers(PsiElement element, CommentPosition position) {
        // class invariants should not go across multiple comments
        if (getParentOfType(element, JMLClassInvariant.class) != null)
            return doPrevInvariantModifiersContain(element, TokenSet.create(element.getNode().getElementType()));
        return doPrevCommentsContain(element, element.getText().trim(), true, true);
    }

    /**
     * Checks whether a loop-invariant is placed above a loop (it should be above a loop)
     *
     * @param element the loop-invariant to check for
     * @return true if the loop-invariant is not above a loop
     */
    private static boolean checkLoopInvariantAboveLoop(JMLLoopInvariant element) {
        PsiComment commentContext = getCommentContext(element);
        // skip all comments and whitespaces that have 1 newline max, otherwise it is not right above it
        PsiElement nextJavaStatement = commentContext.getNextSibling();
        while (nextJavaStatement instanceof PsiComment || (nextJavaStatement instanceof PsiWhiteSpace
                && nextJavaStatement.getText().matches("^[ \t\u00A0]*(\n|\r\n)?[ \t\u00A0]*$"))) {
            nextJavaStatement = nextJavaStatement.getNextSibling();
        }
        // check that it is not above a loop
        return !(nextJavaStatement instanceof PsiWhileStatement || nextJavaStatement instanceof PsiDoWhileStatement
                || nextJavaStatement instanceof PsiForStatement || nextJavaStatement instanceof PsiForeachStatement);
    }


    /**
     * Checks that a clause with \not_specified is not redundant
     *
     * @param element the clause containing \not_specified
     * @return true if it is redundant
     */
    private static boolean checkRedundantNotSpecified(PsiElement element) {
        if (element instanceof JMLRequiresClause || element instanceof JMLEnsuresClause || element instanceof JMLSignalsClause) {
            // first element is the keyword, the next element the expression or \not_specified
            PsiElement child = element.getFirstChild();
            PsiElement nextElem = skipWhitespacesAndCommentsForward(child);
            // check if the clause contains \not_specified
            if (nextElem == null || nextElem.getNode().getElementType() != JMLTypes.NOT_SPECIFIED) {
                return false;
            }
            return doLinkedCommentsContain(element, child.getText().trim(), true);
        }
        // different check for assignable clauses, as there \not_specified is not 2nd child in the tree now
        else if (element instanceof JMLAssignableClause) {
            PsiElement child = getChildOfType(element, JMLStoreRefKeyword.class);
            // check if the clause contains \not_specified
            if (child == null || child.getFirstChild() == null || child.getFirstChild().getNode().getElementType() != JMLTypes.NOT_SPECIFIED) {
                return false;
            }
            return doLinkedCommentsContain(element, "(assignable|modifiable|modifies)", true);
        } else {
            // element is of type signals_only_clause, which cannot contain \not_specified
            return false;
        }
    }

    /**
     * Checks that \result is allowed, it is only allowed in an ensures clause
     *
     * @param element the clause containing \result
     * @return true if it is not allowed
     */
    private static boolean checkBackslashResultAllowed(PsiElement element) {
        return getParentOfType(element, JMLEnsuresClause.class) == null;
    }

    /**
     * Checks that \old() is allowed, it is allowed in in-method specs and in signals and ensures clauses
     *
     * @param element the \old() expression
     * @return true if it is not allowed
     */
    private static boolean checkOldExprAllowed(JMLOldExpr element) {
        return getParentOfType(element, JMLEnsuresClause.class, JMLSignalsClause.class, JMLAssumeStatement.class, JMLAssertStatement.class, JMLLoopInvariant.class) == null;
    }
}
