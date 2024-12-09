package nl.utwente.jmlplugin.psi.impl;

import com.intellij.extapi.psi.ASTWrapperPsiElement;
import com.intellij.lang.ASTNode;
import com.intellij.psi.PsiElementVisitor;
import nl.utwente.jmlplugin.psi.JMLVisitor;
import org.jetbrains.annotations.NotNull;

public class JMLOldExpr extends ASTWrapperPsiElement {

    public JMLOldExpr(@NotNull ASTNode node) {
        super(node);
    }

    public void accept(@NotNull JMLVisitor visitor) {
        visitor.visitOldExpr(this);
    }

    @Override
    public void accept(@NotNull PsiElementVisitor visitor) {
        if (visitor instanceof JMLVisitor) accept((JMLVisitor) visitor);
        else super.accept(visitor);
    }

}
