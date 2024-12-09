package nl.utwente.jmlplugin.syntax_highlighting;

import com.intellij.openapi.editor.colors.TextAttributesKey;
import com.intellij.openapi.fileTypes.SyntaxHighlighter;
import com.intellij.openapi.options.colors.AttributesDescriptor;
import com.intellij.openapi.options.colors.ColorDescriptor;
import com.intellij.openapi.options.colors.ColorSettingsPage;
import nl.utwente.jmlplugin.JMLIcons;
import org.jetbrains.annotations.NonNls;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import javax.swing.*;
import java.util.Map;

/**
 * JML color settings page class. This implements the custom color settings page.
 */

public class JMLColorSettingsPage implements ColorSettingsPage {

    //color highlighting group declarations
    private static final AttributesDescriptor[] DESCRIPTORS = new AttributesDescriptor[]{
            new AttributesDescriptor("Keywords", JMLSyntaxHighlighter.KEY),
            new AttributesDescriptor("Keywords in expressions", JMLSyntaxHighlighter.BACKSLASH_KEY),
            new AttributesDescriptor("Comments", JMLSyntaxHighlighter.COMMENT),
            new AttributesDescriptor("Text", JMLSyntaxHighlighter.TEXT),
            new AttributesDescriptor("Identifiers", JMLSyntaxHighlighter.IDENTIFIER),
            new AttributesDescriptor("Visibility keywords", JMLSyntaxHighlighter.VISIBILITY_KEY),
            new AttributesDescriptor("Parentheses and brackets", JMLSyntaxHighlighter.GROUPING),
            new AttributesDescriptor("Punctuation marks", JMLSyntaxHighlighter.PUNCTUATION),
            new AttributesDescriptor("At-signs", JMLSyntaxHighlighter.AT_SIGN)
    };

    // set the icon of JML files
    @Override
    public @Nullable Icon getIcon() {
        return JMLIcons.FILE;
    }

    // get the syntax highlighter implementation
    @Override
    public @NotNull SyntaxHighlighter getHighlighter() {
        return new JMLSyntaxHighlighter();
    }

    // gets the demo text that is displayed in the color settings page
    @Override
    public @NonNls
    @NotNull String getDemoText() {
        return "/*@\n" +
                "requires \\not_specified;\n" +
                "requires x > 5;\n" +
                "ensures x > 10;\n" +
                "ensures (\\forall int i; 0 <= i && i < array.length; i > 0);\n" +
                "ensures \\typeof(x) == \\type(int);\n" +
                "ensures \\result > 20;\n" +
                "assignable x, y, z;\n" +
                "signals(IOException exc) exc.getMessage() == \"error!\";\n" +
                "signals_only IO_Exception, NullPointerException;\n" +
                "(* this is a comment *)\n" +
                "assignable x[*], this.y.*;";
    }

    // used for more advanced highlighting, we don't do that
    @Override
    public @Nullable Map<String, TextAttributesKey> getAdditionalHighlightingTagToDescriptorMap() {
        return null;
    }

    @Override
    public AttributesDescriptor @NotNull [] getAttributeDescriptors() {
        return DESCRIPTORS;
    }

    @Override
    public ColorDescriptor @NotNull [] getColorDescriptors() {
        return ColorDescriptor.EMPTY_ARRAY;
    }

    @Override
    public @NotNull String getDisplayName() {
        return "JML";
    }
}
