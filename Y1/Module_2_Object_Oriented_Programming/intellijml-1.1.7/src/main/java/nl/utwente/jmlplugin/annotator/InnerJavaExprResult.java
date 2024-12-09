package nl.utwente.jmlplugin.annotator;

import com.intellij.psi.PsiElement;
import com.intellij.psi.PsiExpression;
import com.intellij.psi.PsiType;
import nl.utwente.jmlplugin.psi.impl.JMLInnerJavaExpr;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

/**
 * Holds the results of type checking an InnerJavaExpr
 */
class InnerJavaExprResult extends JMLTypeAnnotator {
    private final StringBuilder text;
    private final RangeManager rangeManager;
    private boolean correct;
    private PsiType type;
    private PsiExpression expr = null;

    InnerJavaExprResult(JMLInnerJavaExpr expr) {
        if (expr == null) {
            this.rangeManager = new RangeManager();
            this.correct = false;
        } else {
            this.rangeManager = new RangeManager(expr);
            this.correct = true;
        }
        this.text = new StringBuilder();
        this.type = PsiType.NULL;
    }

    /**
     * Adds an InnerJavaExprResult to the current result
     *
     * @param other        the other InnerJavaExprResult
     * @param originalElem the element of which results are added
     */
    void add(@NotNull InnerJavaExprResult other, @NotNull PsiElement originalElem) {
        add(other.getText(), other.getType(), other.isCorrect(), originalElem);
    }

    /**
     * Adds results to the current result
     *
     * @param str          the text to add to the result
     * @param type         the type the result should be
     * @param correct      if false, this.correct will be false, if true, this.correct will stay the same
     * @param originalElem the element of which results are added
     */
    void add(@NotNull String str, @Nullable PsiType type, boolean correct, PsiElement originalElem) {
        addText(str, originalElem);
        setType(type);
        setCorrect(correct);
    }

    /**
     * Adds results to the current result
     *
     * @param str          the text to add to the result
     * @param type         the type the result should be
     * @param originalElem the element of which results are added
     */
    void add(@NotNull String str, @Nullable PsiType type, @NotNull PsiElement originalElem) {
        setType(type);
        addText(str, originalElem);
    }

    /**
     * Adds text to the current result
     *
     * @param str          the text to add to the result
     * @param originalElem the element of which the text is added
     */
    void addText(@NotNull String str, @NotNull PsiElement originalElem) {
        this.text.append(str);
        if (str.length() != originalElem.getTextLength()) {
            rangeManager.addRangeChange(originalElem, str.length());
        }
    }

    boolean isCorrect() {
        return this.correct;
    }

    /**
     * Sets this.correct of this result
     *
     * @param correct if false, this.correct will be false, if true, this.correct will stay the same
     */
    void setCorrect(boolean correct) {
        this.correct = this.correct && correct;
    }

    @NotNull String getText() {
        return this.text.toString();
    }

    @NotNull PsiType getType() {
        return this.type;
    }

    /**
     * Sets this.type of this result
     *
     * @param newType the new type
     */
    void setType(PsiType newType) {
        this.type = newType != null ? newType : PsiType.NULL;
    }

    @NotNull RangeManager getRangeManager() {
        return rangeManager;
    }

    PsiExpression getExpr() {
        return expr;
    }

    /**
     * Set the expression that was generated from this result
     *
     * @param expr the expression generated from this result
     */
    void setExpr(PsiExpression expr) {
        this.expr = expr;
    }
}
