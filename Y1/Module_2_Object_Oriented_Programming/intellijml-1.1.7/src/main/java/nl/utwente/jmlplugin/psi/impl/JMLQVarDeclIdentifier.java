package nl.utwente.jmlplugin.psi.impl;

import com.intellij.extapi.psi.ASTWrapperPsiElement;
import com.intellij.lang.ASTNode;
import com.intellij.psi.PsiElementVisitor;
import nl.utwente.jmlplugin.psi.JMLVisitor;
import org.jetbrains.annotations.NotNull;

public class JMLQVarDeclIdentifier extends ASTWrapperPsiElement {

    public JMLQVarDeclIdentifier(@NotNull ASTNode node) {
        super(node);
    }

    public void accept(@NotNull JMLVisitor visitor) {
        visitor.visitQVarDeclIdentifier(this);
    }

    @Override
    public void accept(@NotNull PsiElementVisitor visitor) {
        if (visitor instanceof JMLVisitor) accept((JMLVisitor) visitor);
        else super.accept(visitor);
    }

}
