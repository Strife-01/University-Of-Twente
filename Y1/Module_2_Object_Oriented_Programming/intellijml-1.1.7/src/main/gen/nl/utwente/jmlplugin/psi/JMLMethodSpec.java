// This is a generated file. Not intended for manual editing.
package nl.utwente.jmlplugin.psi;

import java.util.List;
import org.jetbrains.annotations.*;
import com.intellij.psi.PsiElement;

public interface JMLMethodSpec extends PsiElement {

  @NotNull
  List<JMLRequiresClause> getRequiresClauseList();

  @NotNull
  List<JMLSpecBody> getSpecBodyList();

}
