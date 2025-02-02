/* The following code was generated by JFlex 1.7.0 tweaked for IntelliJ platform */

package nl.utwente.jmlplugin.parser;

import com.intellij.lexer.FlexLexer;
import com.intellij.psi.tree.IElementType;

import static com.intellij.psi.TokenType.BAD_CHARACTER;
import static com.intellij.psi.TokenType.WHITE_SPACE;
import static nl.utwente.jmlplugin.psi.JMLTypes.*;


/**
 * This class is a scanner generated by 
 * <a href="http://www.jflex.de/">JFlex</a> 1.7.0
 * from the specification file <tt>_JMLLexer.flex</tt>
 */
public class _JMLLexer implements FlexLexer {

  /** This character denotes the end of file */
  public static final int YYEOF = -1;

  /** initial size of the lookahead buffer */
  private static final int ZZ_BUFFERSIZE = 16384;

  /** lexical states */
  public static final int YYINITIAL = 0;

  /**
   * ZZ_LEXSTATE[l] is the state in the DFA for the lexical state l
   * ZZ_LEXSTATE[l+1] is the state in the DFA for the lexical state l
   *                  at the beginning of a line
   * l is of the form l = 2*k, k a non negative integer
   */
  private static final int ZZ_LEXSTATE[] = { 
     0, 0
  };

  /** 
   * Translates characters to character classes
   * Chosen bits are [7, 7, 7]
   * Total runtime size is 1928 bytes
   */
  public static int ZZ_CMAP(int ch) {
    return ZZ_CMAP_A[(ZZ_CMAP_Y[ZZ_CMAP_Z[ch>>14]|((ch>>7)&0x7f)]<<7)|(ch&0x7f)];
  }

  /* The ZZ_CMAP_Z table has 68 entries */
  static final char ZZ_CMAP_Z[] = zzUnpackCMap(
    "\1\0\103\200");

  /* The ZZ_CMAP_Y table has 256 entries */
  static final char ZZ_CMAP_Y[] = zzUnpackCMap(
    "\1\0\1\1\53\2\1\3\22\2\1\4\37\2\1\3\237\2");

  /* The ZZ_CMAP_A table has 640 entries */
  static final char ZZ_CMAP_A[] = zzUnpackCMap(
    "\11\0\5\2\22\0\1\2\3\0\1\3\3\0\1\5\1\7\1\6\1\0\1\41\1\0\1\40\1\0\12\4\1\42"+
    "\1\37\4\0\1\36\32\3\1\43\1\22\1\10\1\0\1\17\1\0\1\15\1\35\1\26\1\30\1\25\1"+
    "\27\1\13\1\31\1\12\2\3\1\16\1\45\1\14\1\20\1\24\1\44\1\33\1\11\1\23\1\34\1"+
    "\32\2\3\1\21\1\3\12\0\1\1\32\0\1\1\337\0\1\1\177\0\13\1\35\0\2\1\5\0\1\1\57"+
    "\0\1\1\40\0");

  /** 
   * Translates DFA states to action switch labels.
   */
  private static final int [] ZZ_ACTION = zzUnpackAction();

  private static final String ZZ_ACTION_PACKED_0 =
    "\1\0\1\1\1\2\1\3\1\4\1\5\1\6\1\7"+
    "\1\10\5\4\1\1\5\4\1\11\1\12\1\13\1\14"+
    "\1\15\1\16\1\4\2\0\11\4\3\0\11\4\2\0"+
    "\12\4\3\0\4\4\1\17\7\4\1\0\12\4\1\20"+
    "\1\4\3\0\1\21\1\22\2\4\1\23\6\4\1\0"+
    "\1\24\3\4\1\25\7\4\1\26\3\0\10\4\1\24"+
    "\1\4\1\27\5\4\1\30\1\31\1\4\3\0\2\4"+
    "\1\32\1\4\1\33\3\4\1\34\7\4\3\0\1\35"+
    "\1\4\1\36\7\4\1\37\1\4\1\40\2\4\1\0"+
    "\1\41\1\0\1\4\1\42\2\4\1\43\3\4\1\44"+
    "\2\4\2\0\1\45\5\4\1\46\1\4\2\0\1\4"+
    "\1\47\2\4\1\50\1\4\1\0\1\51\1\52\1\53"+
    "\2\4\1\0\2\4\1\0\1\54\1\55\1\56";

  private static int [] zzUnpackAction() {
    int [] result = new int[222];
    int offset = 0;
    offset = zzUnpackAction(ZZ_ACTION_PACKED_0, offset, result);
    return result;
  }

  private static int zzUnpackAction(String packed, int offset, int [] result) {
    int i = 0;       /* index in packed string  */
    int j = offset;  /* index in unpacked array */
    int l = packed.length();
    while (i < l) {
      int count = packed.charAt(i++);
      int value = packed.charAt(i++);
      do result[j++] = value; while (--count > 0);
    }
    return j;
  }


  /** 
   * Translates a state to a row index in the transition table
   */
  private static final int [] ZZ_ROWMAP = zzUnpackRowMap();

  private static final String ZZ_ROWMAP_PACKED_0 =
    "\0\0\0\46\0\46\0\114\0\162\0\230\0\46\0\46"+
    "\0\46\0\276\0\344\0\u010a\0\u0130\0\u0156\0\u017c\0\u01a2"+
    "\0\u01c8\0\u01ee\0\u0214\0\u023a\0\46\0\46\0\46\0\46"+
    "\0\46\0\46\0\u0260\0\230\0\u0286\0\u02ac\0\u02d2\0\u02f8"+
    "\0\u031e\0\u0344\0\u036a\0\u0390\0\u03b6\0\u03dc\0\u0402\0\u0428"+
    "\0\u044e\0\u0474\0\u049a\0\u04c0\0\u04e6\0\u050c\0\u0532\0\u0558"+
    "\0\u057e\0\u05a4\0\u05ca\0\u05f0\0\u0616\0\u063c\0\u0662\0\u0688"+
    "\0\u06ae\0\u06d4\0\u06fa\0\u0720\0\u0746\0\u076c\0\u0792\0\u07b8"+
    "\0\u07de\0\u0804\0\u082a\0\u0850\0\u0876\0\162\0\u089c\0\u08c2"+
    "\0\u08e8\0\u090e\0\u0934\0\u095a\0\u0980\0\u09a6\0\u09cc\0\u09f2"+
    "\0\u0a18\0\u0a3e\0\u0a64\0\u0a8a\0\u0ab0\0\u0ad6\0\u0afc\0\u0b22"+
    "\0\162\0\u0b48\0\u0b6e\0\u0b94\0\u0bba\0\162\0\162\0\u0be0"+
    "\0\u0c06\0\162\0\u0c2c\0\u0c52\0\u0c78\0\u0c9e\0\u0cc4\0\u0cea"+
    "\0\u0d10\0\46\0\u0d36\0\u0d5c\0\u0d82\0\162\0\u0da8\0\u0dce"+
    "\0\u0df4\0\u0e1a\0\u0e40\0\u0e66\0\u0e8c\0\46\0\u0eb2\0\u0ed8"+
    "\0\u0efe\0\u0f24\0\u0f4a\0\u0f70\0\u0f96\0\u0fbc\0\u0fe2\0\u1008"+
    "\0\u102e\0\u05ca\0\u1054\0\162\0\u107a\0\u10a0\0\u10c6\0\u10ec"+
    "\0\u1112\0\162\0\162\0\u1138\0\u115e\0\u1184\0\u11aa\0\u11d0"+
    "\0\u11f6\0\162\0\u121c\0\162\0\u1242\0\u1268\0\u128e\0\u12b4"+
    "\0\u12da\0\u1300\0\u1326\0\u134c\0\u1372\0\u1398\0\u13be\0\u13e4"+
    "\0\u140a\0\u1430\0\162\0\u1456\0\162\0\u147c\0\u14a2\0\u14c8"+
    "\0\u14ee\0\u1514\0\u153a\0\u1560\0\162\0\u1586\0\162\0\u15ac"+
    "\0\u15d2\0\u15f8\0\46\0\u161e\0\u1644\0\162\0\u166a\0\u1690"+
    "\0\162\0\u16b6\0\u16dc\0\u1702\0\162\0\u1728\0\u174e\0\u1774"+
    "\0\u179a\0\162\0\u17c0\0\u17e6\0\u180c\0\u1832\0\u1858\0\162"+
    "\0\u187e\0\u18a4\0\u18ca\0\u18f0\0\162\0\u1916\0\u193c\0\162"+
    "\0\u1962\0\u1988\0\46\0\162\0\162\0\u19ae\0\u19d4\0\u19fa"+
    "\0\u1a20\0\u1a46\0\u1a6c\0\162\0\162\0\46";

  private static int [] zzUnpackRowMap() {
    int [] result = new int[222];
    int offset = 0;
    offset = zzUnpackRowMap(ZZ_ROWMAP_PACKED_0, offset, result);
    return result;
  }

  private static int zzUnpackRowMap(String packed, int offset, int [] result) {
    int i = 0;  /* index in packed string  */
    int j = offset;  /* index in unpacked array */
    int l = packed.length();
    while (i < l) {
      int high = packed.charAt(i++) << 16;
      result[j++] = high | packed.charAt(i++);
    }
    return j;
  }

  /** 
   * The transition table of the DFA
   */
  private static final int [] ZZ_TRANS = zzUnpackTrans();

  private static final String ZZ_TRANS_PACKED_0 =
    "\1\2\1\3\1\4\1\5\1\2\1\6\1\7\1\10"+
    "\1\11\1\12\1\13\1\5\1\14\1\15\1\16\3\5"+
    "\1\17\1\20\1\21\1\22\3\5\1\23\1\5\1\24"+
    "\2\5\1\25\1\26\1\27\1\30\1\31\1\32\1\5"+
    "\1\33\50\0\1\4\46\0\2\5\4\0\11\5\1\0"+
    "\13\5\6\0\2\5\2\0\1\34\3\0\1\35\42\0"+
    "\2\5\4\0\1\5\1\36\7\5\1\0\1\37\1\40"+
    "\7\5\1\41\1\5\6\0\2\5\3\0\2\5\4\0"+
    "\3\5\1\42\5\5\1\0\13\5\6\0\2\5\3\0"+
    "\2\5\4\0\11\5\1\0\11\5\1\43\1\5\6\0"+
    "\2\5\3\0\2\5\4\0\1\44\4\5\1\45\3\5"+
    "\1\0\13\5\6\0\2\5\3\0\2\5\4\0\7\5"+
    "\1\46\1\5\1\0\13\5\6\0\2\5\12\0\1\47"+
    "\1\0\1\50\10\0\1\51\23\0\2\5\4\0\11\5"+
    "\1\0\6\5\1\52\4\5\6\0\2\5\3\0\2\5"+
    "\4\0\7\5\1\53\1\5\1\0\10\5\1\54\1\55"+
    "\1\5\6\0\2\5\3\0\2\5\4\0\3\5\1\56"+
    "\5\5\1\0\13\5\6\0\2\5\3\0\2\5\4\0"+
    "\11\5\1\0\2\5\1\57\10\5\6\0\2\5\3\0"+
    "\2\5\4\0\11\5\1\0\2\5\1\60\10\5\6\0"+
    "\2\5\3\0\2\5\4\0\4\5\1\61\2\5\1\62"+
    "\1\5\1\0\13\5\6\0\2\5\6\63\1\64\37\63"+
    "\3\0\2\5\4\0\2\5\1\65\6\5\1\0\13\5"+
    "\6\0\2\5\3\0\2\5\4\0\4\5\1\66\4\5"+
    "\1\0\13\5\6\0\2\5\3\0\2\5\4\0\11\5"+
    "\1\0\2\5\1\67\10\5\6\0\2\5\3\0\2\5"+
    "\4\0\11\5\1\0\1\5\1\70\11\5\6\0\2\5"+
    "\3\0\2\5\4\0\1\71\10\5\1\0\7\5\1\72"+
    "\3\5\6\0\2\5\3\0\2\5\4\0\5\5\1\73"+
    "\3\5\1\0\13\5\6\0\2\5\3\0\2\5\4\0"+
    "\1\74\10\5\1\0\13\5\6\0\2\5\3\0\2\5"+
    "\4\0\1\75\10\5\1\0\13\5\6\0\2\5\3\0"+
    "\2\5\4\0\7\5\1\76\1\5\1\0\13\5\6\0"+
    "\2\5\14\0\1\77\51\0\1\100\57\0\1\101\16\0"+
    "\2\5\4\0\1\5\1\102\7\5\1\0\13\5\6\0"+
    "\2\5\3\0\2\5\4\0\1\103\10\5\1\0\13\5"+
    "\6\0\2\5\3\0\2\5\4\0\1\5\1\104\5\5"+
    "\1\105\1\5\1\0\2\5\1\106\10\5\6\0\2\5"+
    "\3\0\2\5\4\0\11\5\1\0\10\5\1\107\1\5"+
    "\1\110\6\0\2\5\3\0\2\5\4\0\1\111\10\5"+
    "\1\0\13\5\6\0\2\5\3\0\2\5\4\0\5\5"+
    "\1\112\3\5\1\0\13\5\6\0\2\5\3\0\2\5"+
    "\4\0\11\5\1\0\13\5\6\0\1\113\1\5\3\0"+
    "\2\5\4\0\1\5\1\114\7\5\1\0\13\5\6\0"+
    "\2\5\3\0\2\5\4\0\11\5\1\0\5\5\1\115"+
    "\5\5\6\0\2\5\6\63\1\116\45\63\1\64\1\0"+
    "\36\63\3\0\2\5\4\0\3\5\1\117\5\5\1\0"+
    "\13\5\6\0\2\5\3\0\2\5\4\0\11\5\1\0"+
    "\1\120\12\5\6\0\2\5\3\0\2\5\4\0\11\5"+
    "\1\0\3\5\1\121\7\5\6\0\2\5\3\0\2\5"+
    "\4\0\11\5\1\0\2\5\1\122\10\5\6\0\2\5"+
    "\3\0\2\5\4\0\11\5\1\0\1\123\12\5\6\0"+
    "\2\5\3\0\2\5\4\0\4\5\1\124\4\5\1\0"+
    "\13\5\6\0\2\5\3\0\2\5\4\0\5\5\1\125"+
    "\3\5\1\0\13\5\6\0\2\5\3\0\2\5\4\0"+
    "\1\5\1\126\7\5\1\0\2\5\1\127\6\5\1\130"+
    "\1\5\6\0\2\5\3\0\2\5\4\0\7\5\1\131"+
    "\1\5\1\0\13\5\6\0\2\5\3\0\2\5\4\0"+
    "\11\5\1\0\1\5\1\132\11\5\6\0\2\5\23\0"+
    "\1\133\45\0\1\134\47\0\1\135\23\0\2\5\4\0"+
    "\1\136\10\5\1\0\13\5\6\0\2\5\3\0\2\5"+
    "\4\0\11\5\1\0\1\137\12\5\6\0\2\5\3\0"+
    "\2\5\4\0\11\5\1\0\7\5\1\140\3\5\6\0"+
    "\2\5\3\0\2\5\4\0\11\5\1\0\1\141\12\5"+
    "\6\0\2\5\3\0\2\5\4\0\11\5\1\0\2\5"+
    "\1\142\10\5\6\0\2\5\3\0\2\5\4\0\5\5"+
    "\1\143\3\5\1\0\13\5\6\0\2\5\3\0\2\5"+
    "\4\0\11\5\1\0\11\5\1\144\1\5\6\0\2\5"+
    "\3\0\2\5\4\0\11\5\1\0\1\5\1\145\11\5"+
    "\6\0\2\5\3\0\2\5\4\0\11\5\1\0\11\5"+
    "\1\146\1\5\6\0\2\5\3\0\2\5\4\0\3\5"+
    "\1\147\5\5\1\0\13\5\6\0\2\5\3\0\2\5"+
    "\4\0\1\5\1\150\7\5\1\0\13\5\6\0\2\5"+
    "\2\63\1\151\3\63\1\64\1\152\36\63\3\0\2\5"+
    "\4\0\4\5\1\153\4\5\1\0\13\5\6\0\2\5"+
    "\3\0\2\5\4\0\1\5\1\154\7\5\1\0\13\5"+
    "\6\0\2\5\3\0\2\5\4\0\6\5\1\155\2\5"+
    "\1\0\13\5\6\0\2\5\3\0\2\5\4\0\11\5"+
    "\1\0\10\5\1\156\2\5\6\0\2\5\3\0\2\5"+
    "\4\0\4\5\1\157\4\5\1\0\13\5\6\0\2\5"+
    "\3\0\2\5\4\0\11\5\1\0\10\5\1\160\2\5"+
    "\6\0\2\5\3\0\2\5\4\0\4\5\1\161\4\5"+
    "\1\0\13\5\6\0\2\5\3\0\2\5\4\0\2\5"+
    "\1\162\6\5\1\0\13\5\6\0\2\5\3\0\2\5"+
    "\4\0\11\5\1\0\10\5\1\163\2\5\6\0\2\5"+
    "\3\0\2\5\4\0\11\5\1\0\13\5\6\0\1\5"+
    "\1\164\3\0\2\5\4\0\6\5\1\165\2\5\1\0"+
    "\13\5\6\0\2\5\20\0\1\166\44\0\1\167\11\0"+
    "\1\170\47\0\1\171\15\0\2\5\4\0\4\5\1\172"+
    "\4\5\1\0\13\5\6\0\2\5\3\0\2\5\4\0"+
    "\11\5\1\0\2\5\1\173\10\5\6\0\2\5\3\0"+
    "\2\5\4\0\1\5\1\174\7\5\1\0\13\5\6\0"+
    "\2\5\3\0\2\5\4\0\11\5\1\0\10\5\1\175"+
    "\2\5\6\0\2\5\3\0\2\5\4\0\11\5\1\0"+
    "\2\5\1\176\10\5\6\0\2\5\3\0\2\5\4\0"+
    "\1\5\1\177\7\5\1\0\13\5\6\0\2\5\3\0"+
    "\2\5\4\0\11\5\1\0\1\200\12\5\6\0\2\5"+
    "\3\0\2\5\4\0\11\5\1\0\4\5\1\201\6\5"+
    "\6\0\2\5\2\63\1\151\3\63\1\116\1\202\36\63"+
    "\3\0\2\5\4\0\5\5\1\203\3\5\1\0\13\5"+
    "\6\0\2\5\3\0\2\5\4\0\11\5\1\0\3\5"+
    "\1\204\7\5\6\0\2\5\3\0\2\5\4\0\11\5"+
    "\1\0\1\5\1\205\11\5\6\0\2\5\3\0\2\5"+
    "\4\0\3\5\1\206\5\5\1\0\13\5\6\0\2\5"+
    "\3\0\2\5\4\0\1\5\1\207\7\5\1\0\13\5"+
    "\6\0\2\5\3\0\2\5\4\0\11\5\1\0\12\5"+
    "\1\210\6\0\2\5\3\0\2\5\4\0\3\5\1\211"+
    "\5\5\1\0\13\5\6\0\2\5\3\0\2\5\4\0"+
    "\11\5\1\0\1\212\12\5\6\0\2\5\3\0\2\5"+
    "\4\0\11\5\1\0\2\5\1\213\10\5\6\0\2\5"+
    "\3\0\2\5\4\0\1\5\1\214\7\5\1\0\13\5"+
    "\6\0\2\5\11\0\1\215\46\0\1\216\54\0\1\217"+
    "\27\0\2\5\4\0\11\5\1\0\1\220\12\5\6\0"+
    "\2\5\3\0\2\5\4\0\11\5\1\0\3\5\1\221"+
    "\7\5\6\0\2\5\3\0\2\5\4\0\11\5\1\0"+
    "\3\5\1\222\7\5\6\0\2\5\3\0\2\5\4\0"+
    "\11\5\1\0\2\5\1\223\10\5\6\0\2\5\3\0"+
    "\2\5\4\0\11\5\1\0\10\5\1\224\2\5\6\0"+
    "\2\5\3\0\2\5\4\0\11\5\1\0\10\5\1\225"+
    "\2\5\6\0\2\5\3\0\2\5\4\0\4\5\1\226"+
    "\4\5\1\0\13\5\6\0\2\5\3\0\2\5\4\0"+
    "\1\5\1\227\7\5\1\0\13\5\6\0\2\5\3\0"+
    "\2\5\4\0\1\230\10\5\1\0\13\5\6\0\2\5"+
    "\3\0\2\5\4\0\11\5\1\0\10\5\1\231\1\232"+
    "\1\5\6\0\2\5\3\0\2\5\4\0\11\5\1\0"+
    "\3\5\1\233\7\5\6\0\2\5\3\0\2\5\4\0"+
    "\4\5\1\234\4\5\1\0\13\5\6\0\2\5\3\0"+
    "\2\5\4\0\5\5\1\235\3\5\1\0\13\5\6\0"+
    "\2\5\3\0\2\5\4\0\4\5\1\236\4\5\1\0"+
    "\13\5\6\0\2\5\3\0\2\5\4\0\3\5\1\237"+
    "\5\5\1\0\13\5\6\0\2\5\24\0\1\240\35\0"+
    "\1\241\54\0\1\242\25\0\2\5\4\0\11\5\1\0"+
    "\2\5\1\243\10\5\6\0\2\5\3\0\2\5\4\0"+
    "\11\5\1\0\1\244\12\5\6\0\2\5\3\0\2\5"+
    "\4\0\1\245\10\5\1\0\13\5\6\0\2\5\3\0"+
    "\2\5\4\0\11\5\1\0\2\5\1\246\10\5\6\0"+
    "\2\5\3\0\2\5\4\0\1\5\1\247\7\5\1\0"+
    "\13\5\6\0\2\5\3\0\2\5\4\0\4\5\1\250"+
    "\4\5\1\0\2\5\1\251\10\5\6\0\2\5\3\0"+
    "\2\5\4\0\6\5\1\252\2\5\1\0\13\5\6\0"+
    "\2\5\3\0\2\5\4\0\7\5\1\253\1\5\1\0"+
    "\13\5\6\0\2\5\3\0\2\5\4\0\11\5\1\0"+
    "\12\5\1\254\6\0\2\5\3\0\2\5\4\0\11\5"+
    "\1\0\2\5\1\255\10\5\6\0\2\5\3\0\2\5"+
    "\4\0\3\5\1\256\5\5\1\0\13\5\6\0\2\5"+
    "\3\0\2\5\4\0\11\5\1\0\2\5\1\257\10\5"+
    "\6\0\2\5\3\0\2\5\4\0\11\5\1\0\12\5"+
    "\1\260\6\0\2\5\3\0\2\5\4\0\11\5\1\0"+
    "\7\5\1\261\3\5\6\0\2\5\25\0\1\262\33\0"+
    "\1\263\63\0\1\264\17\0\2\5\4\0\11\5\1\0"+
    "\2\5\1\265\10\5\6\0\2\5\3\0\2\5\4\0"+
    "\1\266\10\5\1\0\13\5\6\0\2\5\3\0\2\5"+
    "\4\0\3\5\1\267\5\5\1\0\13\5\6\0\2\5"+
    "\3\0\2\5\4\0\11\5\1\0\12\5\1\270\6\0"+
    "\2\5\3\0\2\5\4\0\1\271\10\5\1\0\13\5"+
    "\6\0\2\5\3\0\2\5\4\0\7\5\1\272\1\5"+
    "\1\0\13\5\6\0\2\5\3\0\2\5\4\0\11\5"+
    "\1\0\1\273\12\5\6\0\2\5\3\0\2\5\4\0"+
    "\5\5\1\274\3\5\1\0\13\5\6\0\2\5\3\0"+
    "\2\5\4\0\11\5\1\0\1\275\12\5\6\0\2\5"+
    "\3\0\2\5\4\0\5\5\1\276\3\5\1\0\13\5"+
    "\6\0\2\5\3\0\2\5\4\0\4\5\1\277\4\5"+
    "\1\0\13\5\6\0\2\5\26\0\1\300\31\0\1\301"+
    "\36\0\2\5\4\0\11\5\1\0\5\5\1\302\5\5"+
    "\6\0\2\5\3\0\2\5\4\0\1\5\1\303\7\5"+
    "\1\0\13\5\6\0\2\5\3\0\2\5\4\0\5\5"+
    "\1\304\3\5\1\0\13\5\6\0\2\5\3\0\2\5"+
    "\4\0\3\5\1\305\5\5\1\0\13\5\6\0\2\5"+
    "\3\0\2\5\4\0\11\5\1\0\2\5\1\306\10\5"+
    "\6\0\2\5\3\0\2\5\4\0\1\5\1\307\7\5"+
    "\1\0\13\5\6\0\2\5\3\0\2\5\4\0\11\5"+
    "\1\0\2\5\1\310\10\5\6\0\2\5\3\0\2\5"+
    "\4\0\11\5\1\0\10\5\1\311\2\5\6\0\2\5"+
    "\12\0\1\312\47\0\1\313\34\0\2\5\4\0\3\5"+
    "\1\314\5\5\1\0\13\5\6\0\2\5\3\0\2\5"+
    "\4\0\11\5\1\0\2\5\1\315\10\5\6\0\2\5"+
    "\3\0\2\5\4\0\5\5\1\316\3\5\1\0\13\5"+
    "\6\0\2\5\3\0\2\5\4\0\11\5\1\0\3\5"+
    "\1\317\7\5\6\0\2\5\3\0\2\5\4\0\11\5"+
    "\1\0\3\5\1\320\7\5\6\0\2\5\3\0\2\5"+
    "\4\0\1\5\1\321\7\5\1\0\13\5\6\0\2\5"+
    "\27\0\1\322\31\0\1\323\35\0\2\5\4\0\2\5"+
    "\1\324\6\5\1\0\13\5\6\0\2\5\3\0\2\5"+
    "\4\0\10\5\1\325\1\0\13\5\6\0\2\5\3\0"+
    "\2\5\4\0\11\5\1\0\1\326\12\5\6\0\2\5"+
    "\3\0\2\5\4\0\4\5\1\327\4\5\1\0\13\5"+
    "\6\0\2\5\12\0\1\330\36\0\2\5\4\0\11\5"+
    "\1\0\2\5\1\331\10\5\6\0\2\5\3\0\2\5"+
    "\4\0\3\5\1\332\5\5\1\0\13\5\6\0\2\5"+
    "\25\0\1\333\23\0\2\5\4\0\11\5\1\0\5\5"+
    "\1\334\5\5\6\0\2\5\3\0\2\5\4\0\11\5"+
    "\1\0\1\335\12\5\6\0\2\5\30\0\1\336\15\0";

  private static int [] zzUnpackTrans() {
    int [] result = new int[6802];
    int offset = 0;
    offset = zzUnpackTrans(ZZ_TRANS_PACKED_0, offset, result);
    return result;
  }

  private static int zzUnpackTrans(String packed, int offset, int [] result) {
    int i = 0;       /* index in packed string  */
    int j = offset;  /* index in unpacked array */
    int l = packed.length();
    while (i < l) {
      int count = packed.charAt(i++);
      int value = packed.charAt(i++);
      value--;
      do result[j++] = value; while (--count > 0);
    }
    return j;
  }


  /* error codes */
  private static final int ZZ_UNKNOWN_ERROR = 0;
  private static final int ZZ_NO_MATCH = 1;
  private static final int ZZ_PUSHBACK_2BIG = 2;

  /* error messages for the codes above */
  private static final String[] ZZ_ERROR_MSG = {
    "Unknown internal scanner error",
    "Error: could not match input",
    "Error: pushback value was too large"
  };

  /**
   * ZZ_ATTRIBUTE[aState] contains the attributes of state <code>aState</code>
   */
  private static final int [] ZZ_ATTRIBUTE = zzUnpackAttribute();

  private static final String ZZ_ATTRIBUTE_PACKED_0 =
    "\1\0\2\11\3\1\3\11\13\1\6\11\1\1\2\0"+
    "\11\1\3\0\11\1\2\0\12\1\3\0\14\1\1\0"+
    "\14\1\3\0\13\1\1\0\1\11\13\1\1\11\3\0"+
    "\23\1\3\0\20\1\3\0\17\1\1\0\1\11\1\0"+
    "\13\1\2\0\10\1\2\0\6\1\1\0\1\11\4\1"+
    "\1\0\2\1\1\0\2\1\1\11";

  private static int [] zzUnpackAttribute() {
    int [] result = new int[222];
    int offset = 0;
    offset = zzUnpackAttribute(ZZ_ATTRIBUTE_PACKED_0, offset, result);
    return result;
  }

  private static int zzUnpackAttribute(String packed, int offset, int [] result) {
    int i = 0;       /* index in packed string  */
    int j = offset;  /* index in unpacked array */
    int l = packed.length();
    while (i < l) {
      int count = packed.charAt(i++);
      int value = packed.charAt(i++);
      do result[j++] = value; while (--count > 0);
    }
    return j;
  }

  /** the input device */
  private java.io.Reader zzReader;

  /** the current state of the DFA */
  private int zzState;

  /** the current lexical state */
  private int zzLexicalState = YYINITIAL;

  /** this buffer contains the current text to be matched and is
      the source of the yytext() string */
  private CharSequence zzBuffer = "";

  /** the textposition at the last accepting state */
  private int zzMarkedPos;

  /** the current text position in the buffer */
  private int zzCurrentPos;

  /** startRead marks the beginning of the yytext() string in the buffer */
  private int zzStartRead;

  /** endRead marks the last character in the buffer, that has been read
      from input */
  private int zzEndRead;

  /**
   * zzAtBOL == true <=> the scanner is currently at the beginning of a line
   */
  private boolean zzAtBOL = true;

  /** zzAtEOF == true <=> the scanner is at the EOF */
  private boolean zzAtEOF;

  /** denotes if the user-EOF-code has already been executed */
  private boolean zzEOFDone;

  /* user code: */
  public _JMLLexer() {
    this((java.io.Reader)null);
  }


  /**
   * Creates a new scanner
   *
   * @param   in  the java.io.Reader to read input from.
   */
  public _JMLLexer(java.io.Reader in) {
    this.zzReader = in;
  }


  /** 
   * Unpacks the compressed character translation table.
   *
   * @param packed   the packed character translation table
   * @return         the unpacked character translation table
   */
  private static char [] zzUnpackCMap(String packed) {
    int size = 0;
    for (int i = 0, length = packed.length(); i < length; i += 2) {
      size += packed.charAt(i);
    }
    char[] map = new char[size];
    int i = 0;  /* index in packed string  */
    int j = 0;  /* index in unpacked array */
    while (i < packed.length()) {
      int  count = packed.charAt(i++);
      char value = packed.charAt(i++);
      do map[j++] = value; while (--count > 0);
    }
    return map;
  }

  public final int getTokenStart() {
    return zzStartRead;
  }

  public final int getTokenEnd() {
    return getTokenStart() + yylength();
  }

  public void reset(CharSequence buffer, int start, int end, int initialState) {
    zzBuffer = buffer;
    zzCurrentPos = zzMarkedPos = zzStartRead = start;
    zzAtEOF  = false;
    zzAtBOL = true;
    zzEndRead = end;
    yybegin(initialState);
  }

  /**
   * Refills the input buffer.
   *
   * @return      {@code false}, iff there was new input.
   *
   * @exception   java.io.IOException  if any I/O-Error occurs
   */
  private boolean zzRefill() throws java.io.IOException {
    return true;
  }


  /**
   * Returns the current lexical state.
   */
  public final int yystate() {
    return zzLexicalState;
  }


  /**
   * Enters a new lexical state
   *
   * @param newState the new lexical state
   */
  public final void yybegin(int newState) {
    zzLexicalState = newState;
  }


  /**
   * Returns the text matched by the current regular expression.
   */
  public final CharSequence yytext() {
    return zzBuffer.subSequence(zzStartRead, zzMarkedPos);
  }


  /**
   * Returns the character at position {@code pos} from the
   * matched text.
   *
   * It is equivalent to yytext().charAt(pos), but faster
   *
   * @param pos the position of the character to fetch.
   *            A value from 0 to yylength()-1.
   *
   * @return the character at position pos
   */
  public final char yycharat(int pos) {
    return zzBuffer.charAt(zzStartRead+pos);
  }


  /**
   * Returns the length of the matched text region.
   */
  public final int yylength() {
    return zzMarkedPos-zzStartRead;
  }


  /**
   * Reports an error that occurred while scanning.
   *
   * In a wellformed scanner (no or only correct usage of
   * yypushback(int) and a match-all fallback rule) this method
   * will only be called with things that "Can't Possibly Happen".
   * If this method is called, something is seriously wrong
   * (e.g. a JFlex bug producing a faulty scanner etc.).
   *
   * Usual syntax/scanner level error handling should be done
   * in error fallback rules.
   *
   * @param   errorCode  the code of the errormessage to display
   */
  private void zzScanError(int errorCode) {
    String message;
    try {
      message = ZZ_ERROR_MSG[errorCode];
    }
    catch (ArrayIndexOutOfBoundsException e) {
      message = ZZ_ERROR_MSG[ZZ_UNKNOWN_ERROR];
    }

    throw new Error(message);
  }


  /**
   * Pushes the specified amount of characters back into the input stream.
   *
   * They will be read again by then next call of the scanning method
   *
   * @param number  the number of characters to be read again.
   *                This number must not be greater than yylength()!
   */
  public void yypushback(int number)  {
    if ( number > yylength() )
      zzScanError(ZZ_PUSHBACK_2BIG);

    zzMarkedPos -= number;
  }


  /**
   * Resumes scanning until the next regular expression is matched,
   * the end of input is encountered or an I/O-Error occurs.
   *
   * @return      the next token
   * @exception   java.io.IOException  if any I/O-Error occurs
   */
  public IElementType advance() throws java.io.IOException {
    int zzInput;
    int zzAction;

    // cached fields:
    int zzCurrentPosL;
    int zzMarkedPosL;
    int zzEndReadL = zzEndRead;
    CharSequence zzBufferL = zzBuffer;

    int [] zzTransL = ZZ_TRANS;
    int [] zzRowMapL = ZZ_ROWMAP;
    int [] zzAttrL = ZZ_ATTRIBUTE;

    while (true) {
      zzMarkedPosL = zzMarkedPos;

      zzAction = -1;

      zzCurrentPosL = zzCurrentPos = zzStartRead = zzMarkedPosL;

      zzState = ZZ_LEXSTATE[zzLexicalState];

      // set up zzAction for empty match case:
      int zzAttributes = zzAttrL[zzState];
      if ( (zzAttributes & 1) == 1 ) {
        zzAction = zzState;
      }


      zzForAction: {
        while (true) {

          if (zzCurrentPosL < zzEndReadL) {
            zzInput = Character.codePointAt(zzBufferL, zzCurrentPosL/*, zzEndReadL*/);
            zzCurrentPosL += Character.charCount(zzInput);
          }
          else if (zzAtEOF) {
            zzInput = YYEOF;
            break zzForAction;
          }
          else {
            // store back cached positions
            zzCurrentPos  = zzCurrentPosL;
            zzMarkedPos   = zzMarkedPosL;
            boolean eof = zzRefill();
            // get translated positions and possibly new buffer
            zzCurrentPosL  = zzCurrentPos;
            zzMarkedPosL   = zzMarkedPos;
            zzBufferL      = zzBuffer;
            zzEndReadL     = zzEndRead;
            if (eof) {
              zzInput = YYEOF;
              break zzForAction;
            }
            else {
              zzInput = Character.codePointAt(zzBufferL, zzCurrentPosL/*, zzEndReadL*/);
              zzCurrentPosL += Character.charCount(zzInput);
            }
          }
          int zzNext = zzTransL[ zzRowMapL[zzState] + ZZ_CMAP(zzInput) ];
          if (zzNext == -1) break zzForAction;
          zzState = zzNext;

          zzAttributes = zzAttrL[zzState];
          if ( (zzAttributes & 1) == 1 ) {
            zzAction = zzState;
            zzMarkedPosL = zzCurrentPosL;
            if ( (zzAttributes & 8) == 8 ) break zzForAction;
          }

        }
      }

      // store back cached position
      zzMarkedPos = zzMarkedPosL;

      if (zzInput == YYEOF && zzStartRead == zzCurrentPos) {
        zzAtEOF = true;
        return null;
      }
      else {
        switch (zzAction < 0 ? zzAction : ZZ_ACTION[zzAction]) {
          case 1: 
            { return REST;
            } 
            // fall through
          case 47: break;
          case 2: 
            { return BAD_CHARACTER;
            } 
            // fall through
          case 48: break;
          case 3: 
            { return WHITE_SPACE;
            } 
            // fall through
          case 49: break;
          case 4: 
            { return IDENT;
            } 
            // fall through
          case 50: break;
          case 5: 
            { return L_PAREN;
            } 
            // fall through
          case 51: break;
          case 6: 
            { return STAR;
            } 
            // fall through
          case 52: break;
          case 7: 
            { return R_PAREN;
            } 
            // fall through
          case 53: break;
          case 8: 
            { return R_SQ_BRAC;
            } 
            // fall through
          case 54: break;
          case 9: 
            { return AT_SIGN;
            } 
            // fall through
          case 55: break;
          case 10: 
            { return SEMICOLON;
            } 
            // fall through
          case 56: break;
          case 11: 
            { return DOT;
            } 
            // fall through
          case 57: break;
          case 12: 
            { return COMMA;
            } 
            // fall through
          case 58: break;
          case 13: 
            { return COLON;
            } 
            // fall through
          case 59: break;
          case 14: 
            { return L_SQ_BRAC;
            } 
            // fall through
          case 60: break;
          case 15: 
            { return PRE;
            } 
            // fall through
          case 61: break;
          case 16: 
            { return ALSO;
            } 
            // fall through
          case 62: break;
          case 17: 
            { return THIS;
            } 
            // fall through
          case 63: break;
          case 18: 
            { return POST;
            } 
            // fall through
          case 64: break;
          case 19: 
            { return PURE;
            } 
            // fall through
          case 65: break;
          case 20: 
            { return INFORMAL_DESCRIPTION;
            } 
            // fall through
          case 66: break;
          case 21: 
            { return SUPER;
            } 
            // fall through
          case 67: break;
          case 22: 
            { return INTO;
            } 
            // fall through
          case 68: break;
          case 23: 
            { return STATIC;
            } 
            // fall through
          case 69: break;
          case 24: 
            { return ASSERT;
            } 
            // fall through
          case 70: break;
          case 25: 
            { return ASSUME;
            } 
            // fall through
          case 71: break;
          case 26: 
            { return PUBLIC;
            } 
            // fall through
          case 72: break;
          case 27: 
            { return HELPER;
            } 
            // fall through
          case 73: break;
          case 28: 
            { return SIGNALS;
            } 
            // fall through
          case 74: break;
          case 29: 
            { return PRIVATE;
            } 
            // fall through
          case 75: break;
          case 30: 
            { return ENSURES;
            } 
            // fall through
          case 76: break;
          case 31: 
            { return INSTANCE;
            } 
            // fall through
          case 77: break;
          case 32: 
            { return NULLABLE;
            } 
            // fall through
          case 78: break;
          case 33: 
            { return NOTHING;
            } 
            // fall through
          case 79: break;
          case 34: 
            { return REQUIRES;
            } 
            // fall through
          case 80: break;
          case 35: 
            { return MODIFIES;
            } 
            // fall through
          case 81: break;
          case 36: 
            { return INVARIANT;
            } 
            // fall through
          case 82: break;
          case 37: 
            { return PROTECTED;
            } 
            // fall through
          case 83: break;
          case 38: 
            { return ASSIGNABLE;
            } 
            // fall through
          case 84: break;
          case 39: 
            { return MODIFIABLE;
            } 
            // fall through
          case 85: break;
          case 40: 
            { return SPEC_PUBLIC;
            } 
            // fall through
          case 86: break;
          case 41: 
            { return EVERYTHING;
            } 
            // fall through
          case 87: break;
          case 42: 
            { return MAINTAINING;
            } 
            // fall through
          case 88: break;
          case 43: 
            { return SIGNALS_ONLY;
            } 
            // fall through
          case 89: break;
          case 44: 
            { return SPEC_PROTECTED;
            } 
            // fall through
          case 90: break;
          case 45: 
            { return LOOPINVARIANT;
            } 
            // fall through
          case 91: break;
          case 46: 
            { return NOT_SPECIFIED;
            } 
            // fall through
          case 92: break;
          default:
            zzScanError(ZZ_NO_MATCH);
          }
      }
    }
  }


}
