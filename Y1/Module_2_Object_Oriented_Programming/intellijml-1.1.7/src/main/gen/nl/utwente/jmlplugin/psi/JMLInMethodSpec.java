// This is a generated file. Not intended for manual editing.
package nl.utwente.jmlplugin.psi;

import java.util.List;
import org.jetbrains.annotations.*;
import com.intellij.psi.PsiElement;

public interface JMLInMethodSpec extends PsiElement {

  @NotNull
  List<JMLAssertStatement> getAssertStatementList();

  @NotNull
  List<JMLAssumeStatement> getAssumeStatementList();

  @NotNull
  List<JMLLoopInvariant> getLoopInvariantList();

}
