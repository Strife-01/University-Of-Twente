package nl.utwente.jmlplugin.psi.impl;

import com.intellij.extapi.psi.ASTWrapperPsiElement;
import com.intellij.lang.ASTNode;
import com.intellij.psi.PsiElementVisitor;
import com.intellij.psi.util.PsiTreeUtil;
import nl.utwente.jmlplugin.psi.JMLVisitor;
import org.jetbrains.annotations.NotNull;

import java.util.List;

public class JMLQVarDecl extends ASTWrapperPsiElement {

    public JMLQVarDecl(@NotNull ASTNode node) {
        super(node);
    }

    public void accept(@NotNull JMLVisitor visitor) {
        visitor.visitQVarDecl(this);
    }

    @Override
    public void accept(@NotNull PsiElementVisitor visitor) {
        if (visitor instanceof JMLVisitor) accept((JMLVisitor) visitor);
        else super.accept(visitor);
    }

    /**
     * Gets the name of the type that all the variables have
     *
     * @return the name of the type that all the variables have
     */
    public JMLTypeName getTypeName() {
        if (this.getFirstChild() instanceof JMLTypeName) return (JMLTypeName) this.getFirstChild();
        return null;
    }

    /**
     * Gets a list of all the variables names that are declared in this expression
     *
     * @return a list of all the variables names that are declared in this expression
     */
    public @NotNull
    List<JMLQVarDeclIdentifier> getIdentifiers() {
        return PsiTreeUtil.getChildrenOfTypeAsList(this, JMLQVarDeclIdentifier.class);
    }

}
