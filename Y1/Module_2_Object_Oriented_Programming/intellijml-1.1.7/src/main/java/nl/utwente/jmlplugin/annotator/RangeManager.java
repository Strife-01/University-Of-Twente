package nl.utwente.jmlplugin.annotator;

import com.intellij.openapi.util.TextRange;
import com.intellij.psi.PsiElement;
import nl.utwente.jmlplugin.psi.impl.JMLInnerJavaExpr;
import org.jetbrains.annotations.NotNull;

import java.util.ArrayList;

/**
 * Keeps track of changes in text ranges for all elements in an expression
 */
public class RangeManager {
    // holds all the range changes
    private final ArrayList<RangeChange> rangeChanges = new ArrayList<>();

    protected RangeManager(@NotNull JMLInnerJavaExpr expr) {
        // add the offset from the Java file to the changes as we need it later
        rangeChanges.add(new RangeChange(-1, -1, expr.getTextRange().getStartOffset()));
    }

    protected RangeManager() {

    }

    /**
     * @param elem       the element containing the original text before the replacement
     * @param textLength the length of the replacement text
     */
    protected void addRangeChange(PsiElement elem, int textLength) {
        int currentStartOffset = getCurrentOffset(elem.getTextRange().getStartOffset());
        rangeChanges.add(new RangeChange(currentStartOffset, currentStartOffset + textLength, elem.getTextLength() - textLength));
    }

    /**
     * Gets the changed offset from the original offset
     *
     * @param myOffset the original offset
     * @return the changed offset
     */
    protected int getCurrentOffset(int myOffset) {
        int newOffset = myOffset;
        for (RangeChange change : rangeChanges) {
            if (change.startOffset < myOffset) {
                newOffset -= change.deltaLengthChange;
            }
        }
        return newOffset;
    }

    /**
     * Gets the original range before all the replacements
     *
     * @param elem the element containing replaced text
     * @return the original range before all the replacements
     */
    protected TextRange getOriginalRange(PsiElement elem) {
        return getOriginalRange(elem.getTextRange().getStartOffset(), elem.getTextLength());
    }

    /**
     * Gets the original range before all the replacements
     *
     * @param myStartOffset the start offset of the replaced text
     * @param length        the length of the replace text
     * @return the original range before all the replacements
     */
    protected TextRange getOriginalRange(int myStartOffset, int length) {
        // rollback all changes that influenced the range of the element
        for (int i = rangeChanges.size() - 1; i >= 0; i--) {
            RangeChange change = rangeChanges.get(i);
            // change was entirely before the element
            if (change.startOffset < myStartOffset && change.newEndOffset <= myStartOffset) {
                myStartOffset += change.deltaLengthChange;
            }
            // the change was before the end of the element
            else if (change.startOffset < myStartOffset + length) {
                // is subrange of an element, which we do not want, so change it to the range of the element
                if (change.newEndOffset > myStartOffset + length && change.startOffset < myStartOffset) {
                    myStartOffset = change.startOffset;
                }
                // make length at least 1, just in case
                length = Math.max(length + change.deltaLengthChange, 1);
            }
        }
        return new TextRange(Math.max(myStartOffset, rangeChanges.get(0).deltaLengthChange), myStartOffset + length);
    }

    /**
     * Holds a single range change
     */
    private static class RangeChange {
        public final int startOffset;
        public final int newEndOffset;
        // is positive if the new text is shorter
        public final int deltaLengthChange;


        public RangeChange(int startOffset, int newEndOffset, int deltaLengthChange) {
            this.startOffset = startOffset;
            this.newEndOffset = newEndOffset;
            this.deltaLengthChange = deltaLengthChange;
        }
    }
}
