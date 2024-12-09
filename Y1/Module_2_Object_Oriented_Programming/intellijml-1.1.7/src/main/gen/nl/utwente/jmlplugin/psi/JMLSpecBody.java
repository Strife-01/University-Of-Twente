// This is a generated file. Not intended for manual editing.
package nl.utwente.jmlplugin.psi;

import java.util.List;
import org.jetbrains.annotations.*;
import com.intellij.psi.PsiElement;

public interface JMLSpecBody extends PsiElement {

  @NotNull
  List<JMLAssignableClause> getAssignableClauseList();

  @NotNull
  List<JMLEnsuresClause> getEnsuresClauseList();

  @NotNull
  List<JMLSignalsClause> getSignalsClauseList();

  @NotNull
  List<JMLSignalsOnlyClause> getSignalsOnlyClauseList();

}
