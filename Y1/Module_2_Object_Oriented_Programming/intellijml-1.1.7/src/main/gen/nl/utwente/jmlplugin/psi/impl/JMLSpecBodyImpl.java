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

public class JMLSpecBodyImpl extends ASTWrapperPsiElement implements JMLSpecBody {

  public JMLSpecBodyImpl(@NotNull ASTNode node) {
    super(node);
  }

  public void accept(@NotNull JMLVisitor visitor) {
    visitor.visitSpecBody(this);
  }

  @Override
  public void accept(@NotNull PsiElementVisitor visitor) {
    if (visitor instanceof JMLVisitor) accept((JMLVisitor)visitor);
    else super.accept(visitor);
  }

  @Override
  @NotNull
  public List<JMLAssignableClause> getAssignableClauseList() {
    return PsiTreeUtil.getChildrenOfTypeAsList(this, JMLAssignableClause.class);
  }

  @Override
  @NotNull
  public List<JMLEnsuresClause> getEnsuresClauseList() {
    return PsiTreeUtil.getChildrenOfTypeAsList(this, JMLEnsuresClause.class);
  }

  @Override
  @NotNull
  public List<JMLSignalsClause> getSignalsClauseList() {
    return PsiTreeUtil.getChildrenOfTypeAsList(this, JMLSignalsClause.class);
  }

  @Override
  @NotNull
  public List<JMLSignalsOnlyClause> getSignalsOnlyClauseList() {
    return PsiTreeUtil.getChildrenOfTypeAsList(this, JMLSignalsOnlyClause.class);
  }

}
