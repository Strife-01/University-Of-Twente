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

public class JMLSignalsOnlyClauseImpl extends ASTWrapperPsiElement implements JMLSignalsOnlyClause {

  public JMLSignalsOnlyClauseImpl(@NotNull ASTNode node) {
    super(node);
  }

  public void accept(@NotNull JMLVisitor visitor) {
    visitor.visitSignalsOnlyClause(this);
  }

  @Override
  public void accept(@NotNull PsiElementVisitor visitor) {
    if (visitor instanceof JMLVisitor) accept((JMLVisitor)visitor);
    else super.accept(visitor);
  }

  @Override
  @NotNull
  public List<JMLReferenceType> getReferenceTypeList() {
    return PsiTreeUtil.getChildrenOfTypeAsList(this, JMLReferenceType.class);
  }

}
