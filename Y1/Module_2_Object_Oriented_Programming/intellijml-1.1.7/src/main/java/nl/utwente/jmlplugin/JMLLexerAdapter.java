package nl.utwente.jmlplugin;

import com.intellij.lexer.FlexAdapter;
import nl.utwente.jmlplugin.parser._JMLLexer;

/**
 * Class that links the JFlex lexer to the java classes.
 */
public class JMLLexerAdapter extends FlexAdapter {

    public JMLLexerAdapter() {
        super(new _JMLLexer(null));
    }
}
