package nl.utwente.jmlplugin.easteregg;

import com.intellij.lang.annotation.AnnotationHolder;
import com.intellij.lang.annotation.Annotator;
import com.intellij.lang.annotation.HighlightSeverity;
import com.intellij.openapi.application.ApplicationManager;
import com.intellij.openapi.editor.markup.TextAttributes;
import com.intellij.openapi.util.TextRange;
import com.intellij.psi.PsiElement;
import nl.utwente.jmlplugin.psi.JMLFile;
import nl.utwente.jmlplugin.settings.JMLApplicationSettings;
import org.jetbrains.annotations.NotNull;

import java.awt.*;
import java.util.ArrayList;
import java.util.List;

@SuppressWarnings("UseJBColor")
public class Rainbow implements Annotator {
    private static final List<Color> colors;

    static {
        colors = new ArrayList<>();
        for (int r = 0; r < 10; r++) colors.add(new Color(r * 255 / 10, 255, 0));
        for (int g = 10; g > 0; g--) colors.add(new Color(255, g * 255 / 10, 0));
        for (int b = 0; b < 10; b++) colors.add(new Color(255, 0, b * 255 / 10));
        for (int r = 10; r > 0; r--) colors.add(new Color(r * 255 / 10, 0, 255));
        for (int g = 0; g < 10; g++) colors.add(new Color(0, g * 255 / 10, 255));
        for (int b = 10; b > 0; b--) colors.add(new Color(0, 255, b * 255 / 10));
        colors.add(new Color(0, 255, 0));
    }


    @Override
    public void annotate(@NotNull PsiElement element, @NotNull AnnotationHolder holder) {
        // make the text rainbow coloured if hidden checkbox is checked
        if (!ApplicationManager.getApplication().isUnitTestMode() && element instanceof JMLFile) {
            JMLApplicationSettings settings = JMLApplicationSettings.getInstance();
            if (settings.RAINBOW_MODE) {
                List<Color> myColors = getColors(element.getTextLength());
                int count = 0;
                for (int i = element.getTextRange().getStartOffset(); i < element.getTextRange().getEndOffset() - 1; i++) {
                    TextAttributes textAttributes = new TextAttributes();
                    textAttributes.setForegroundColor(myColors.get(count % myColors.size()));
                    holder.newSilentAnnotation(new HighlightSeverity("", 1)).enforcedTextAttributes(textAttributes).range(new TextRange(i, i + 1)).create();
                    count++;
                }
            }
        }
    }


    List<Color> getColors(int count) {
        // get a subset of the colors
        List<Color> colorsSubset = new ArrayList<>();
        int increments = colors.size() / Math.min(count, colors.size() - 1);
        for (int i = 0; i < colors.size(); i += increments) {
            colorsSubset.add(colors.get(i));
        }
        return colorsSubset;
    }
}
