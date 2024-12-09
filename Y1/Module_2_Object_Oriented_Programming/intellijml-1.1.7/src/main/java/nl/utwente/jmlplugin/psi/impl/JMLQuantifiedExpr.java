package nl.utwente.jmlplugin.psi.impl;

import com.intellij.extapi.psi.ASTWrapperPsiElement;
import com.intellij.lang.ASTNode;
import com.intellij.psi.PsiElement;
import com.intellij.psi.PsiElementVisitor;
import com.intellij.psi.tree.IElementType;
import com.intellij.psi.util.PsiTreeUtil;
import nl.utwente.jmlplugin.psi.JMLVisitor;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

public class JMLQuantifiedExpr extends ASTWrapperPsiElement {

    public JMLQuantifiedExpr(@NotNull ASTNode node) {
        super(node);
    }

    public void accept(@NotNull JMLVisitor visitor) {
        visitor.visitQuantifiedExpr(this);
    }

    @Override
    public void accept(@NotNull PsiElementVisitor visitor) {
        if (visitor instanceof JMLVisitor) accept((JMLVisitor) visitor);
        else super.accept(visitor);
    }

    /**
     * Gets the range predicate of the quantified expression
     *
     * @return the range predicate of the quantified expression or null if it could not be found
     */
    public JMLQPredicate getRangePredicate() {
        return PsiTreeUtil.getChildOfType(this, JMLQPredicate.class);
    }

    /**
     * Gets the body of the quantified expression
     *
     * @return the body of the quantified expression or null if it could not be found
     */
    @Nullable
    public JMLQSpecExpr getSpecExpr() {
        return PsiTreeUtil.getChildOfType(this, JMLQSpecExpr.class);
    }

    /**
     * Gets the keyword of the quantified expression, such as \forall
     *
     * @return the keyword of the quantified expression or null if it could not be found
     */
    @Nullable
    public IElementType getKeyword() {
        PsiElement firstChild = this.getFirstChild();
        if (firstChild == null) return null;
        PsiElement nextSibling = PsiTreeUtil.skipWhitespacesAndCommentsForward(firstChild);
        if (nextSibling == null) return null;
        return nextSibling.getNode().getElementType();
    }

    /**
     * Gets the variable declaration part of the quantified expression
     *
     * @return the range variable declaration part of the quantified expression or null if it could not be found
     */
    @Nullable
    public JMLQVarDecl getVarDecls() {
        return PsiTreeUtil.getChildOfType(this, JMLQVarDecl.class);
    }

}
