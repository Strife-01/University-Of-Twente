// This is a generated file. Not intended for manual editing.
package nl.utwente.jmlplugin.psi.impl;

import java.util.List;
import org.jetbrains.annotations.*;
import com.intellij.lang.ASTNode;
import com.intellij.psi.PsiElement;
import com.intellij.psi.PsiElementVisitor;
import com.intellij.psi.util.PsiTreeUtil;
import static nl.utwente.jmlplugin.psi.JMLTypes.*;
import com.intellij.extapi.psi.ASTWrapperPsiElement;
import nl.utwente.jmlplugin.psi.*;

public class JMLMethodSpecImpl extends ASTWrapperPsiElement implements JMLMethodSpec {

  public JMLMethodSpecImpl(@NotNull ASTNode node) {
    super(node);
  }

  public void accept(@NotNull JMLVisitor visitor) {
    visitor.visitMethodSpec(this);
  }

  @Override
  public void accept(@NotNull PsiElementVisitor visitor) {
    if (visitor instanceof JMLVisitor) accept((JMLVisitor)visitor);
    else super.accept(visitor);
  }

  @Override
  @NotNull
  public List<JMLRequiresClause> getRequiresClauseList() {
    return PsiTreeUtil.getChildrenOfTypeAsList(this, JMLRequiresClause.class);
  }

  @Override
  @NotNull
  public List<JMLSpecBody> getSpecBodyList() {
    return PsiTreeUtil.getChildrenOfTypeAsList(this, JMLSpecBody.class);
  }

}
